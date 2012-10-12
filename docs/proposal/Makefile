default : proposal.pdf

preview : proposal.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app proposal.pdf; fi

proposal.pdf : proposal.tex
	pdflatex proposal.tex && pdflatex proposal.tex && pdflatex -synctex=1 proposal.tex

proposal.tex : proposal.lhs
	lhs2TeX -o proposal.tex proposal.lhs

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm proposal.pdf proposal.tex *.synctex.gz *.bbl *.blg

