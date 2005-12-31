TEXFILES = DeBruijn.tex HOAS.tex IdInt.tex Lambda.tex Main.tex Simple.tex Unique.tex

.SUFFIXES : .lhs .tex

.lhs.tex :
	awk -f bird2code.awk $< > $*.tex


LC:	*.lhs
	ghc -O2 -Wall --make Main.lhs -o LC

lambda.dvi:	lambda.tex $(TEXFILES)
	latex lambda.tex; latex lambda.tex

lambda.ps:	lambda.dvi
	dvips -t A4 lambda.dvi -o lambda.ps

lambda.pdf:	lambda.tex $(TEXFILES)
	pdflatex lambda.tex; pdflatex lambda.tex

.PHONY: timing
timing:	LC
	time ./LC S < timing.lam
	time ./LC U < timing.lam
	time ./LC H < timing.lam
	time ./LC D < timing.lam

.PHONY:	clean
clean:
	rm -f *.hi *.o LC lambda.pdf lambda.ps lambda.dvi lambda.log lambda.aux $(TEXFILES)
