default : slides-slides.pdf slides-notes.pdf

preview : slides-slides.pdf slides-notes.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app slides-slides.pdf; fi

slides-notes.pdf : slides.tex slides-notes.tex
	pdflatex -halt-on-error slides-notes.tex && pdflatex slides-notes.tex && pdflatex -synctex=1 slides-notes.tex

slides-slides.pdf : slides.tex slides-slides.tex
	pdflatex -halt-on-error slides-slides.tex && pdflatex slides-slides.tex && pdflatex -synctex=1 slides-slides.tex

slides.tex : slides.lhs
	lhs2TeX -o slides.tex slides.lhs

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm slides.pdf slides.tex *.synctex.gz *.bbl *.blg
