CABAL-CONFIGURE-FLAGS := --user
CABAL-BUILD-FLAGS     :=
TESTFILE=SimpleExample.hs

default : test

all : haskell

src/AG.hs : src/AG.ag src/AG/Types.ag src/AG/Syntax.ag src/AG/Convert.ag
	uuagc -Hcfws --self --optimize -P src src/AG.ag

haskell : src/AG.hs
	runhaskell Setup.hs configure $(CABAL-CONFIGURE-FLAGS)
	runhaskell Setup.hs build $(CABAL-BUILD-FLAGS)

test : all
	./dist/build/HsToGallina/HsToGallina -w $(TESTFILE)

clean:
	rm src/AG.hs 
	runhaskell Setup.hs clean
