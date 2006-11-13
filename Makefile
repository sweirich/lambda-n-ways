GHC = ghc
#GHC = /usr/local/bin/ghc

TEXFILES = DeBruijn.tex HOAS.tex IdInt.tex Lambda.tex Main.tex Simple.tex Unique.tex

.SUFFIXES : .lhs .tex

.lhs.tex :
	awk -f bird2code.awk $< > $*.tex


LC:	*.lhs
	$(GHC) -O2 -Wall --make Main.lhs -o LC

CMain:	*.lhs *.hs
	$(GHC) -Wall --make CMain.hs -o CMain

top.dvi:	top.tex $(TEXFILES)
	latex top.tex; latex top.tex

top.ps:	top.dvi
	dvips -t A4 top.dvi -o top.ps

top.pdf:	top.tex $(TEXFILES)
	pdflatex top.tex; pdflatex top.tex

.PHONY: timing
timing:	LC
	time ./LC S < timing.lam
	time ./LC U < timing.lam
	time ./LC H < timing.lam
	time ./LC D < timing.lam
	time ./LC C < timing.lam

.PHONY:	clean
clean:
	rm -f *.hi *.o LC top.pdf top.ps top.dvi top.log top.aux $(TEXFILES)
