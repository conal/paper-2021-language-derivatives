PAPER=paper
TALK=talk

all: latex/$(PAPER).pdf latex/$(TALK).pdf

MODULES:=\
  Language

LAGDAS:=$(patsubst %,%.lagda,$(MODULES))

AGDA_DEPENDENCIES:=$(patsubst %,latex/%.tex,$(MODULES))
.SECONDARY: $(AGDA_DEPENDENCIES)

LATEX_DEPENDENCIES:= \
  latex/bib.bib \
  latex/macros.tex \
  latex/unicode.tex \
  latex/commands.tex \
  $(AGDA_DEPENDENCIES)

AGDA=agda

# AGDA-EXTRAS=--only-scope-checking

latex/%.tex: %.lagda
	@mkdir -p $(dir $@)
	${AGDA} -i . --latex $(AGDA-EXTRAS) $< --latex-dir=latex > $(basename $@).log

latex/%: %
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.pdf: latex/%.tex $(LATEX_DEPENDENCIES)
	cd latex && latexmk -xelatex -bibtex $*.tex

# latex/$(PAPER).pdf: $(PAPER_DEPENDENCIES)
# 	cd latex && latexmk -xelatex -bibtex ${PAPER}.tex

# latex/Test.pdf: latex/Test.tex $(PAPER_DEPENDENCIES)
# 	cd latex && latexmk -xelatex -bibtex Test.tex

SHOWPDF=skim

see: $(PAPER).see

%.see: latex/%.pdf
	${SHOWPDF} $<

clean:
	rm -r latex

tags: $(LAGDAS)
	etags $^

web: web-token

web-token: latex/$(PAPER).pdf
	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/new-language-derivatives/$(PAPER)
	touch web-token
