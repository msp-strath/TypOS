TARGET:=types
BIB:=typos.bib
TEX:=$(TARGET).tex
PDF:=$(TARGET).pdf
DEPS:=easychair.cls

all: $(TEX) $(DEPS)
	mkdir -p _build
	cp $(BIB) $(DEPS) $(TEX) _build
	cd _build && latexmk -bibtex -pdf $(TEX)
	ln -sf _build/$(PDF) $(PDF)

clean:
	rm -rf _build $(PDF)
