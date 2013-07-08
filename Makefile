
all : CoList.vo CoTree.vo Naive.vo SternBrocot.vo CalkinWilf.vo

doc : CoList.html CoTree.html Naive.html SternBrocot.html CalkinWilf.html

clean :
	@rm -f *.vo *.glob *.html coqdoc.css
	

CoList.vo :
	coqc CoList.v
	
CoTree.vo : CoList.vo
	coqc -I . CoTree.v
	
Naive.vo : CoTree.vo
	coqc -I . Naive.v
	
SternBrocot.vo : CoTree.vo
	coqc -I . SternBrocot.v
	
CalkinWilf.vo : CoTree.vo
	coqc -I . CalkinWilf.v
	
CoList.html :
	coqdoc -s CoList.v
	
CoTree.html :
	coqdoc -s CoTree.v
	
Naive.html :
	coqdoc -s Naive.v
	
SternBrocot.html :
	coqdoc -s SternBrocot.v
	
CalkinWilf.html :
	coqdoc -s CalkinWilf.v
	