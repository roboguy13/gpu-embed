all:
	rm -rf dist-newstyle
	cabal configure --disable-profiling --disable-documentation && cabal build -j1

paper: paper/paper.pdf

paper/paper.pdf: paper/paper.tex
	(cd paper && make)
