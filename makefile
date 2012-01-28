CABAL-CONFIGURE-FLAGS := --user
CABAL-BUILD-FLAGS     :=
VERSION					      := 0.0.3

all : haskell doc

src/IPython/AST.hs : src/IPython/AST.ag
	uuagc -Hd --self src/IPython/AST.ag -P src/IPython/

src/Analysis/Python.hs : src/Analysis/Python.ag src/IPython/AST.ag
	uuagc -Hcfws --self src/Analysis/Python.ag -P src/Analysis/

ag : src/IPython/AST.hs src/Analysis/Python.hs

haskell : ag src/Main.hs
	runhaskell Setup.lhs configure $(CABAL-CONFIGURE-FLAGS)
	runhaskell Setup.lhs build $(CABAL-BUILD-FLAGS)

doc: README
	asciidoc -a toc -a numbered README

dist: all
	cabal sdist
	cp dist/softtyping-$(VERSION).tar.gz dist/submit.tgz


testdist: dist
	cp dist/softtyping-$(VERSION).tar.gz /tmp
	cd /tmp && tar xvzf softtyping-$(VERSION).tar.gz && cd /tmp/softtyping-$(VERSION) && cabal configure && cabal build

clean:
	rm src/Analysis/Python.hs src/IPython/AST.hs
