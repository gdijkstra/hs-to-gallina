CABAL-CONFIGURE-FLAGS := --user
CABAL-BUILD-FLAGS     :=
TESTFILE=examples/ListTest.hs
TESTFILEBN=$(basename $(TESTFILE))

default : test

all : haskell

src/AG.hs : src/AG.ag src/AG/*.ag
	@echo "Make: running uuagc..."
	uuagc -Hcfws --self --optimize -P src src/AG.ag

haskell : src/AG.hs
	@echo "Make: running cabal"
	runhaskell Setup.hs configure $(CABAL-CONFIGURE-FLAGS)
	runhaskell Setup.hs build $(CABAL-BUILD-FLAGS)

test : all clean-coq-tmp prelude
	@echo "Make: running program..."
	./dist/build/HsToGallina/HsToGallina -w $(TESTFILE)
	@echo "Make: running coqc..."
	coqc -I examples $(TESTFILEBN).v
	@if [ $$? -eq 0 ] ; then echo "Make: coqc run succesfully" ; else echo "Error: coqc run unsuccesfully"; fi

prelude: examples/Prelude.v
	coqc examples/Prelude.v

clean-coq-tmp:
	rm examples/Prelude.glob examples/Prelude.vo
	rm -f $(TESTFILEBN).glob $(TESTFILEBN).v $(TESTFILEBN).vo

clean: clean-coq-tmp
	rm src/AG.hs 
	runhaskell Setup.hs clean

