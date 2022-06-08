.PHONY: all build install clean install-hasktags TAGS test gif

build:
	cabal build

all: install test

install:
	cabal install

clean:
	rm -rf dist dist-newstyle TAGS

install-hasktags:
	cabal update
	cabal install hasktags

TAGS:
	hasktags --etags .

test:
	TERM=dumb cabal run typos-tests -- -i

build/%.gif: examples/%.act
	typos examples/$(*F).act --latex build/$(*F).tex
	sed -i "s|%\\\\input|\\\\input|" build/$(*F).tex
	cd build && \
	latexmk -pdf $(*F).tex && \
	convert -verbose -delay 25 -density 300 -loop 0 $(*F).pdf $(*F)-tmp.gif && \
	convert -dispose previous -background "rgb(100%,100%,100%)" \
	$(*F)-tmp.gif -trim -layers TrimBounds -coalesce -layers optimize $(*F).gif && \
	rm $(*F)-tmp.gif
