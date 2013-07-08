
all: CoList.vo CoTree.vo Naive.vo SternBrocot.vo CalkinWilf.vo

doc:
	coqdoc -s CoList.v CoTree.v Naive.v SternBrocot.v CalkinWilf.v

clean:
	@rm -f *.vo *.glob *.html coqdoc.css

CoList.vo:
	coqc -I . CoList.v

CoTree.vo: CoList.vo
	coqc -I . CoTree.v
	
Naive.vo: CoList.vo CoTree.vo
	coqc -I . Naive.v
	
SternBrocot.vo: CoList.vo CoTree.vo
	coqc -I . SternBrocot.v
	
CalkinWilf.vo: CoList.vo CoTree.vo
	coqc -I . CalkinWilf.v
