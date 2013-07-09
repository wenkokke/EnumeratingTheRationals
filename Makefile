
all: Data/List.vo CoData/CoList.vo CoData/CoTree.vo Enums/NaiveEnum.vo Enums/NaiveTree.vo Enums/SternBrocot.vo Enums/CalkinWilf.vo

doc: all
	pandoc -c doc/coqdoc.css -o index.html README.md
	coqdoc -d doc --no-index -s Data/List.v CoData/CoList.v CoData/CoTree.v Enums/NaiveEnum.v Enums/NaiveTree.v Enums/SternBrocot.v Enums/CalkinWilf.v

clean:
	@rm -f doc/*.html doc/coqdoc.css
	@rm -f Data/*.vo Data/*.glob
	@rm -f CoData/*.vo CoData/*.glob
	@rm -f Enums/*.vo Enums/*.glob

Data/List.vo:
	coqc Data/List.v
	
CoData/CoList.vo:
	coqc -I Data -I CoData CoData/CoList.v

CoData/CoTree.vo: Data/List.vo CoData/CoList.vo
	coqc -I Data -I CoData CoData/CoTree.v
	
Enums/NaiveEnum.vo: CoData/CoList.vo
	coqc -I Data -I CoData Enums/NaiveEnum.v
	
Enums/NaiveTree.vo: CoData/CoList.vo CoData/CoTree.vo
	coqc -I Data -I CoData Enums/NaiveTree.v
	
Enums/SternBrocot.vo: CoData/CoList.vo CoData/CoTree.vo
	coqc -I Data -I CoData Enums/SternBrocot.v
	
Enums/CalkinWilf.vo: CoData/CoList.vo CoData/CoTree.vo
	coqc -I Data -I CoData Enums/CalkinWilf.v
