.PHONY: all build install clean install-hasktags TAGS test

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
