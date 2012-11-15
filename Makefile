CABAL-CONFIGURE-FLAGS := --user
CABAL-BUILD-FLAGS     :=

default : test

all : haskell

src/AG.hs : src/AG.ag src/AG/*.ag
	@echo "Make: running uuagc..."
	uuagc -Hcfws --self --optimize -P src src/AG.ag

haskell : src/AG.hs
	@echo "Make: running cabal"
	runhaskell Setup.hs configure $(CABAL-CONFIGURE-FLAGS)
	runhaskell Setup.hs build $(CABAL-BUILD-FLAGS)

test : all prelude
	@echo "Make: running RunTests..."
	./RunTests
	@if [ $$? -eq 0 ] ; then echo "Make: RunTests run succesfully" ; else echo "Error: RunTests run unsuccesfully"; fi

prelude: lib/Prelude.v
	coqc lib/Prelude.v

clean-prelude:
	rm -f lib/Prelude.glob lib/Prelude.vo

clean: clean-prelude
	rm src/AG.hs 
	runhaskell Setup.hs clean

