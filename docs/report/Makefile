default : report.pdf

preview : report.pdf
	if [ `uname` = 'Darwin' ]; then open -a /Applications/Skim.app report.pdf; fi

report.pdf : report.tex report.bib
	pdflatex -halt-on-error report.tex && pdflatex report.tex && pdflatex -synctex=1 report.tex
	bibtex report
	pdflatex -halt-on-error report.tex && pdflatex report.tex && pdflatex -synctex=1 report.tex

report.tex : report.lhs report.fmt report.bib
	lhs2TeX -o report.tex report.lhs

clean :
	rm -f *.aux *.log *.nav *.out *.ptb *.toc *.snm report.pdf report.tex *.synctex.gz *.bbl *.blg

