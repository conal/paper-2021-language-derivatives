PAPER=paper
TALK=talk

all: latex/$(TALK).pdf latex/$(PAPER).pdf

MODULES:= \
  Language \
  Inverses \
  Calculus \
  Decidability \
  Reflections \
  Symbolic \
  Automatic \
  SizedAutomatic \
  Predicate \
  Existential

LAGDAS:=$(patsubst %,%.lagda,$(MODULES))

AGDA_DEPENDENCIES:=$(patsubst %,latex/%.tex,$(MODULES))
.SECONDARY: $(AGDA_DEPENDENCIES)

LATEX_DEPENDENCIES:= \
  latex/bib.bib \
  latex/macros.tex \
  latex/unicode.tex \
  latex/commands.tex \
  $(AGDA_DEPENDENCIES)

test :
	echo $(LATEX_DEPENDENCIES)

AGDA=agda

# AGDA-EXTRAS=--only-scope-checking

PRECIOUS: $(LATEX_DEPENDENCIES) latex/$(PAPER).tex latex/$(TALK).tex

latex/%.tex: %.lagda
	@mkdir -p $(dir $@)
	${AGDA} -i . --latex --latex-dir=latex $(AGDA-EXTRAS) $<

#  > $(basename $@).log

latex/%: %
	@mkdir -p $(dir $@)
	cp $< $@

latex/%.pdf: latex/%.tex $(LATEX_DEPENDENCIES)
	cd latex && latexmk -xelatex -bibtex $*.tex
	@touch $@

# The touch is in case latexmk decides not to update the pdf.

SHOWPDF=skim

see: $(PAPER).see

%.see: latex/%.pdf
	${SHOWPDF} $<

clean:
	rm -r latex

tags: $(LAGDAS)
	etags $^

# web: web-token

# web-token: latex/$(PAPER).pdf
# 	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/new-language-derivatives/$(PAPER)
# 	touch web-token
