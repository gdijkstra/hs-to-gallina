CABAL-CONFIGURE-FLAGS := --user
CABAL-BUILD-FLAGS     :=
TESTFILE=SimpleExample.hs
TESTFILEBN=`basename $(TESTFILE) ".hs"`

default : test

all : haskell

src/AG.hs : src/AG.ag src/AG/Types.ag src/AG/Syntax.ag src/AG/Convert.ag
	@echo "Make: running uuagc..."
	uuagc -Hcfws --self --optimize -P src src/AG.ag

haskell : src/AG.hs
	@echo "Make: running cabal"
	runhaskell Setup.hs configure $(CABAL-CONFIGURE-FLAGS)
	runhaskell Setup.hs build $(CABAL-BUILD-FLAGS)

test : all clean-coq-tmp
	@echo "Make: running program..."
	./dist/build/HsToGallina/HsToGallina -w $(TESTFILE)
	@echo "Make: running coqc..."
	coqc $(TESTFILEBN).v
	@if [ $$? -eq 0 ] ; then echo "Make: coqc run succesfully" ; else echo "Error: coqc run unsuccesfully"; fi

clean-coq-tmp:
	rm -f $(TESTFILEBN).glob $(TESTFILEBN).v $(TESTFILEBN).vo

clean: clean-coq-tmp
	rm src/AG.hs 
	runhaskell Setup.hs clean

