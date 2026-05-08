## Build the FormalSLT paper PDFs.
##
## Targets:
##   make             # build both main.pdf (full draft) and workshop.pdf
##   make main        # full CPP-style draft (main.tex)
##   make workshop    # 4-page AI4Research @ ICML 2026 submission (workshop.tex)
##   make clean       # remove LaTeX intermediates
##   make distclean   # also remove built PDFs

LATEX  = pdflatex
BIBTEX = bibtex
LATEX_FLAGS = -interaction=nonstopmode -halt-on-error -file-line-error

PAPERS = main workshop

.PHONY: all main workshop clean distclean watch

all: main workshop

main: main.pdf
workshop: workshop.pdf

%.pdf: %.tex references.bib
	$(LATEX) $(LATEX_FLAGS) $*.tex
	$(BIBTEX) $*
	$(LATEX) $(LATEX_FLAGS) $*.tex
	$(LATEX) $(LATEX_FLAGS) $*.tex

clean:
	@for p in $(PAPERS); do \
	  rm -f $$p.aux $$p.bbl $$p.blg $$p.log $$p.out $$p.toc \
	        $$p.fls $$p.fdb_latexmk $$p.synctex.gz ; \
	done

distclean: clean
	@for p in $(PAPERS); do rm -f $$p.pdf ; done

## Optional: latexmk-based incremental build for authors who prefer it.
watch:
	latexmk -pdf -pvc -interaction=nonstopmode workshop.tex
