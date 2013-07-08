
all: Data/List.vo Data/CoList.vo Data/CoTree.vo Enums/NaiveEnum.vo Enums/NaiveTree.vo Enums/SternBrocot.vo Enums/CalkinWilf.vo

doc: all
	coqdoc --no-index -s Data/List.v Data/CoList.v Data/CoTree.v Enums/NaiveEnum.v Enums/NaiveTree.v Enums/SternBrocot.v Enums/CalkinWilf.v

clean:
	@rm -f *.html coqdoc.css
	@rm -f Data/*.vo Data/*.glob
	@rm -f Enums/*.vo Enums/*.glob

Data/List.vo:
	coqc Data/List.v
	
Data/CoList.vo:
	coqc -I Data Data/CoList.v

Data/CoTree.vo: Data/CoList.vo
	coqc -I Data Data/CoTree.v
	
Enums/NaiveEnum.vo: Data/CoList.vo
	coqc -I Data Enums/NaiveEnum.v
	
Enums/NaiveTree.vo: Data/CoList.vo Data/CoTree.vo
	coqc -I Data Enums/NaiveTree.v
	
Enums/SternBrocot.vo: Data/CoList.vo Data/CoTree.vo
	coqc -I Data Enums/SternBrocot.v
	
Enums/CalkinWilf.vo: Data/CoList.vo Data/CoTree.vo
	coqc -I Data Enums/CalkinWilf.v
