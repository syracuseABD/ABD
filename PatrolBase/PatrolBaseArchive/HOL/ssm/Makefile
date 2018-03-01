# ===================================================
# Makefile for ssm Theory 
# ===================================================

default: theory

clean:
	Holmake cleanAll
	cd HOLReports;make clean
	cd Examples;make clean

theory:
	Holmake cleanAll;Holmake;cd HOLReports;make clean;make
	cd Examples;make
