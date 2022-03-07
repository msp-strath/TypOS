TARGET:=types
TEX:=$(TARGET).tex
PDF:=$(TARGET).pdf
DEPS:=easychair.cls

all: $(TEX) $(DEPS)
	mkdir -p _build
	cp $(DEPS) $(TEX) _build
	cd _build && latexmk -pdflatex $(TEX)
	ln -sf _build/$(PDF) $(PDF)

clean:
	rm -rf _build $(PDF)
