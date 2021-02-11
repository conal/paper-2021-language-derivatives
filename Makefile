PAPER=language-derivatives

# all: latex/$(PAPER).pdf
all: talk

talk:
	make -C Talk

.PHONY: talk

MODULES:=\
  Introduction \
  Generation \
  Predicate \
  Closed/Structures \
  Predicate/Properties \
  Predicate/Algebra \
  Nullability \
  Inverses \
  Decidability \
  Calculus \
  Regex \
  Trie \
  ProvingProperties \

#   NonTrie \

#   BeyondPredicates \
#   Predicate/Examples \
#   Predicate/Examples/Bit \
#   Relation \
#   Relation/Properties

#   AltDec \
#   AltCalc \
#   NewIntroduction \

LAGDAS:=$(patsubst %,%.lagda,$(MODULES))

AGDA_DEPENDENCIES:=$(patsubst %,latex/%.tex,$(MODULES))
.SECONDARY: $(AGDA_DEPENDENCIES)

PAPER_DEPENDENCIES:= \
  latex/$(PAPER).tex \
  latex/bib.bib \
  latex/macros.tex \
  latex/unicode.tex \
  latex/commands.tex \
  $(AGDA_DEPENDENCIES)

AGDA=agda

# AGDA-EXTRAS=--only-scope-checking

# AGDA-EXTRAS+=--termination-depth=2


# latex/%.tex: %.lagda
# 	@mkdir -p $(dir $@)
# 	${AGDA} -i . --latex $(AGDA-EXTRAS) $< --latex-dir=latex > $(basename $@).log

# POSTPROCESS=postprocess-latex.pl

latex/%.tex: %.lagda
	@mkdir -p $(dir $@)
	${AGDA} -i . --latex $(AGDA-EXTRAS) $< --latex-dir=latex > $(basename $@).log

# references option. Doesn't seem to work.

# latex/%.tex: %.lagda Makefile
# 	mkdir -p $(dir $@)
# 	${AGDA} -i . --latex $(AGDA-EXTRAS) $< --latex-dir=latex > $(basename $@).log
# 	perl $(POSTPROCESS) < $(basename $@).tex > $(basename $@).processed
# 	mv $(basename $@).processed $(basename $@).tex

latex/%: %
	@mkdir -p $(dir $@)
	cp $< $@

latex/$(PAPER).pdf: $(PAPER_DEPENDENCIES)
	cd latex && latexmk -xelatex -bibtex ${PAPER}.tex

latex/Test.pdf: latex/Test.tex $(PAPER_DEPENDENCIES)
	cd latex && latexmk -xelatex -bibtex Test.tex

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
	scp $< conal@conal.net:/home/conal/domains/conal/htdocs/papers/$(PAPER)
	touch web-token
