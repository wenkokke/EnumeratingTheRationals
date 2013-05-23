
html	: doc/EnumeratingTheRationals.html
latex	: doc/EnumeratingTheRationals.tex
pdf		: doc/EnumeratingTheRationals.pdf

doc:
	mkdir -p doc
	
doc/EnumeratingTheRationals.html: doc EnumeratingTheRationals.v
	coqdoc --html --no-index -s -d doc EnumeratingTheRationals.v
	
doc/EnumeratingTheRationals.tex	: doc EnumeratingTheRationals.v
	coqdoc --latex --no-index -s -d doc EnumeratingTheRationals.v
	
doc/EnumeratingTheRationals.pdf	: doc/EnumeratingTheRationals.tex
	pdflatex doc/EnumeratingTheRationals.tex