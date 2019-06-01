sep.pdf : sep.lhs sep.bib
	CURDIR=`pwd` ;\
	OUTPUT=`mktemp -d "/tmp/paperXXXXX"`;\
	cp * $$OUTPUT/ ;\
	cd $$OUTPUT ;\
	lhs2tex sep.lhs > sep.tex ;\
	latexmk -pdf sep.tex ;\
	cp sep.pdf $$CURDIR/
