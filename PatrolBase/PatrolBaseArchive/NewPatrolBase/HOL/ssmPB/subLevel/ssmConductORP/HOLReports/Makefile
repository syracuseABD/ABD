# ===================================================
# Makefile for OMNIPatrolBase Theory 
# ===================================================

PDFLATEX=pdflatex
DVILATEX=latex
MAKEINDEX=makeindex
BIBTEX=bibtex

default: report

clean:
	(rm -f *Report.* HOL*.*)

report:
	hol<documentation.sml
	${PDFLATEX} conductORPReport
	${MAKEINDEX} conductORPReport
	${PDFLATEX} conductORPReport

