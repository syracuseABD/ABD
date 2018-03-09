# ===================================================
# Makefile for ACL HOL manual
# ===================================================

PDFLATEX=pdflatex
DVILATEX=latex
MAKEINDEX=makeindex
BIBTEX=bibtex

default: report

clean:
	(rm -f aclHOLManual.pdf)

report:
	${PDFLATEX} aclHOLManual
	${BIBTEX} aclHOLManual
	${MAKEINDEX} aclHOLManual
	${PDFLATEX} aclHOLManual

