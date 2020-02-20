all:
	rm -rf dist-newstyle
	cabal configure --disable-profiling --disable-documentation && cabal build -j1
