all: paper.pdf

paper.pdf: paper.tex paper.aux
	pdflatex paper.tex
	bibtex paper.aux
	pdflatex paper.tex
	pdflatex paper.tex
