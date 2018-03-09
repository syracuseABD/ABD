# ===================================================
# Makefile for ABD/HOL/ACL
# ===================================================

default: theory

clean:
	Holmake cleanAll
	cd HOLReports; make clean

theory:
	Holmake cleanAll; Holmake; cd HOLReports; make clean; make

update:
	Holmake; cd HOLReports; make clean; make
