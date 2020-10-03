all: paper.pdf

paper.pdf: paper.tex paper.bib
	pdflatex paper.tex
	bibtex paper.aux
	pdflatex paper.tex
	pdflatex paper.tex

clean:
	rm -f paper.aux
	rm -f paper.bbl
	rm -f paper.blg
	rm -f paper.out
	rm -f paper.log
	rm -f paper.pdf

