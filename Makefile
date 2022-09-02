.PHONY: all build install clean install-hasktags TAGS test gif bash-completion

CABAL_OPTIONS= #--ghc-options=-O0
CABAL=cabal $(CABAL_OPTIONS)

build:
	$(CABAL) build

all: install test

install:
	$(CABAL) install --overwrite-policy=always

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
	typos examples/$(*F).act --latex-animated build/$(*F).tex
	sed -i "s|%\\\\input|\\\\input|" build/$(*F).tex
	cd build && \
	latexmk -pdf $(*F).tex && \
	convert -verbose -density 300 -coalesce $(*F).pdf $(*F)-%03d.gif && \
	fdupes -dN . && \
	convert -verbose -delay 25 -loop 0 $(*F)-*.gif $(*F)-tmp.gif && \
	convert -verbose -dispose previous -background "rgb(100%,100%,100%)" \
	$(*F)-tmp.gif -trim -layers TrimBounds -coalesce \
	-bordercolor "rgb(100%,100%,100%)" -border 40 -layers optimize $(*F).gif && \
	rm $(*F)-*

gif: build/stlc.gif

bash-completion:
# Use as follows: source <(make bash-completion)
	typos --bash-completion-script `which typos`

trace: build/stlc.gif
	cp build/stlc.gif build/trace.gif
	rm build/stlc.tex
	typos examples/stlc.act --latex build/stlc.tex
	sed -i "s|%\\\\input|\\\\input|" build/stlc.tex
	cd build && \
	latexmk -pdf stlc.tex && \
	pdf2svg stlc.pdf trace.svg
