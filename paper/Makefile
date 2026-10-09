# Build the DIG-KN TACAS tool paper. Requires pdflatex + bibtex.
# llncs.cls and splncs04.bst are vendored here (Springer LNCS).
paper.pdf: paper.tex refs.bib llncs.cls splncs04.bst web_ui.png
	pdflatex -interaction=nonstopmode paper.tex
	bibtex paper
	pdflatex -interaction=nonstopmode paper.tex
	pdflatex -interaction=nonstopmode paper.tex

clean:
	rm -f paper.aux paper.bbl paper.blg paper.log paper.out

cleanall: clean
	rm -f paper.pdf

.PHONY: clean cleanall
