
all : Naive.vo SternBrocot.vo CalkinWilf.vo

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

.PHONY : build
	