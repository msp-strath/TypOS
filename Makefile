.PHONY: install clean install-hasktags TAGS test

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
	cabal run typos-tests -- -i