# Repo hooks

This directory holds shared git hooks for FormalSLT.

## Activation

Hooks under `.git/hooks/` are local to each clone and not tracked. Point your
clone at this directory once after `git clone`:

```
git config core.hooksPath .githooks
```

## Hooks

### `pre-push`

Runs on every `git push`. Refuses the push if either of these is found in the
range `origin/main..HEAD`:

1. **AI attribution in commit messages.** `Co-Authored-By:` trailers naming
   Claude, Anthropic, GPT, OpenAI, or Copilot, plus the "Generated with
   Claude Code" marker and robot emoji.
2. **Workflow vocabulary, vendor names as tooling, or internal paths.**
   Patterns include AI vendor names used as workflow tools (Claude / Codex /
   etc. as agent names rather than subject matter), internal workflow vocab
   (orchestrator, subagent, voice-gate, Tier-1 panel, ...), and absolute
   internal paths (`/Users/...`, `HQ/...`, `agent/memory/`, ...).

The check applies only to commits being pushed; pre-existing strings on
`origin/main` are not re-scanned.

An allowlist carves out legitimate Lean library content: the keyword `sorry`,
`sorryCount`, axiom names (`propext`, `Classical.choice`, `Quot.sound`), and
the author byline.

### Bypass

For a true emergency:

```
git push --no-verify
```

Use sparingly. The hook exists because two AI-attribution trailers landed on
origin/main on 2026-06-09 before the hook was in place and could not be
rewritten without breaking the (then) public fork.
