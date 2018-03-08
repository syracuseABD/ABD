# ===================================================
# Makefile for pretty-printing reports 
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

# ===================================================
# Change example1Report to the appropriate report name
# ===================================================
	${PDFLATEX} example1Report
	${MAKEINDEX} example1Report
	${PDFLATEX} example1Report

