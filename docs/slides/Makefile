default : slides.pdf

preview : slides.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app slides.pdf; fi

slides.pdf : slides.tex
	pdflatex -halt-on-error slides.tex && pdflatex slides.tex && pdflatex -synctex=1 slides.tex

slides.tex : slides.lhs
	lhs2TeX -o slides.tex slides.lhs

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm slides.pdf slides.tex *.synctex.gz *.bbl *.blg
