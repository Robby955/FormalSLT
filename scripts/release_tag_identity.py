#!/usr/bin/env python3
"""Resolve or verify one exact remote release-tag identity."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Sequence


TAG_RE = re.compile(
    r"^v[0-9]+\.[0-9]+\.[0-9]+(?:[.-][0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?$"
)
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
DEFAULT_REPOSITORY_URL = "https://github.com/Robby955/FormalSLT.git"


class ReceiptError(RuntimeError):
    """A condition that prevents release identity from being certified."""


@dataclass(frozen=True)
class TagIdentity:
    tag: str
    repository_url: str
    tag_object: str
    resolved_commit: str
    resolved_at_utc: str


def utc_timestamp() -> str:
    return (
        datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z")
    )


def run(command: Sequence[str], *, cwd: Path | None = None) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        check=False,
        capture_output=True,
        text=True,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        suffix = f": {detail}" if detail else ""
        raise ReceiptError(f"command failed ({' '.join(command)}){suffix}")
    return completed.stdout.strip()


def validate_tag(tag: str) -> str:
    if not TAG_RE.fullmatch(tag):
        raise ReceiptError(f"release tag is not exact semver-style syntax: {tag!r}")
    return tag


def validate_sha(value: str, description: str) -> str:
    if not SHA_RE.fullmatch(value):
        raise ReceiptError(
            f"{description} is not one full SHA-1 commit/object id: {value!r}"
        )
    return value


def resolve_remote_tag(repository_url: str, tag: str) -> TagIdentity:
    validate_tag(tag)
    if not repository_url:
        raise ReceiptError("repository URL must not be empty")

    tag_ref = f"refs/tags/{tag}"
    peeled_ref = f"{tag_ref}^{{}}"
    output = run(["git", "ls-remote", repository_url, tag_ref, peeled_ref])

    rows: dict[str, list[str]] = {}
    for line in output.splitlines():
        fields = line.split()
        if len(fields) != 2:
            raise ReceiptError(f"malformed remote-tag row: {line!r}")
        sha, ref = fields
        if ref not in {tag_ref, peeled_ref}:
            raise ReceiptError(f"unexpected remote-tag ref: {ref}")
        rows.setdefault(ref, []).append(validate_sha(sha, f"object for {ref}"))

    tag_objects = rows.get(tag_ref, [])
    if not tag_objects:
        raise ReceiptError(f"remote tag {tag} does not exist at {repository_url}")
    if len(tag_objects) != 1:
        raise ReceiptError(f"remote tag query for {tag} was ambiguous")

    peeled_objects = rows.get(peeled_ref, [])
    if len(peeled_objects) > 1:
        raise ReceiptError(f"peeled remote tag query for {tag} was ambiguous")

    return TagIdentity(
        tag=tag,
        repository_url=repository_url,
        tag_object=tag_objects[0],
        resolved_commit=peeled_objects[0] if peeled_objects else tag_objects[0],
        resolved_at_utc=utc_timestamp(),
    )


def verify_expected_remote(
    repository_url: str,
    tag: str,
    expected_tag_object: str,
    expected_commit: str,
) -> TagIdentity:
    validate_sha(expected_tag_object, "expected tag object")
    validate_sha(expected_commit, "expected peeled commit")
    current = resolve_remote_tag(repository_url, tag)
    if current.tag_object != expected_tag_object:
        raise ReceiptError(
            f"remote tag object changed: expected {expected_tag_object}, "
            f"found {current.tag_object}"
        )
    if current.resolved_commit != expected_commit:
        raise ReceiptError(
            f"remote peeled commit changed: expected {expected_commit}, "
            f"found {current.resolved_commit}"
        )
    return current


def write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, prefix=f".{path.name}.", delete=False
    ) as temporary:
        temporary.write(encoded)
        temporary_path = Path(temporary.name)
    temporary_path.replace(path)


def append_github_outputs(path: Path, identity: TagIdentity) -> None:
    with path.open("a", encoding="utf-8") as output:
        output.write(f"release_tag={identity.tag}\n")
        output.write(f"tag_object={identity.tag_object}\n")
        output.write(f"resolved_commit={identity.resolved_commit}\n")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    resolve = subparsers.add_parser("resolve", help="establish tag identity once")
    resolve.add_argument("--tag", required=True)
    resolve.add_argument(
        "--repository-url",
        default=os.environ.get("FORMALSLT_REPOSITORY_URL", DEFAULT_REPOSITORY_URL),
    )
    resolve.add_argument("--output", type=Path)
    resolve.add_argument("--github-output", type=Path)
    resolve.add_argument(
        "--expected-commit",
        help="optional event commit that the initial resolution must match",
    )

    verify = subparsers.add_parser("verify", help="compare current remote to expectations")
    verify.add_argument("--tag", required=True)
    verify.add_argument(
        "--repository-url",
        default=os.environ.get("FORMALSLT_REPOSITORY_URL", DEFAULT_REPOSITORY_URL),
    )
    verify.add_argument("--expected-tag-object", required=True)
    verify.add_argument("--expected-commit", required=True)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.command == "resolve":
            identity = resolve_remote_tag(args.repository_url, args.tag)
            if args.expected_commit:
                event_commit = validate_sha(args.expected_commit, "expected event commit")
                if identity.resolved_commit != event_commit:
                    raise ReceiptError(
                        f"push event commit mismatch: event fixed {event_commit}, "
                        f"remote tag resolves to {identity.resolved_commit}"
                    )
            if args.output:
                write_json(args.output, asdict(identity))
            if args.github_output:
                append_github_outputs(args.github_output, identity)
            print(json.dumps(asdict(identity), sort_keys=True))
        else:
            identity = verify_expected_remote(
                args.repository_url,
                args.tag,
                args.expected_tag_object,
                args.expected_commit,
            )
            print(
                f"remote tag identity unchanged: {identity.tag_object} -> "
                f"{identity.resolved_commit}"
            )
    except ReceiptError as exc:
        print(f"ERROR: release-tag identity refused: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
