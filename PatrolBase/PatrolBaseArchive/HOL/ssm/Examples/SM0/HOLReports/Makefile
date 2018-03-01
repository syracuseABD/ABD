# ===================================================
# Makefile for example1 Theory 
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
	${PDFLATEX} SM0Report
	${MAKEINDEX} SM0Report
	${PDFLATEX} SM0Report

