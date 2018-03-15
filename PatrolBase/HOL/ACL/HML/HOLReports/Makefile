
PDFLATEX=pdflatex
DVILATEX=latex
MAKEINDEX=makeindex
BIBTEX=bibtex

default: report

clean:
	(rm -f *Report.* HOL*.*)

report:
	hol<documentation.sml
	${PDFLATEX} mmFoundationReport
	${MAKEINDEX} mmFoundationReport
	${PDFLATEX} mmFoundationReport
