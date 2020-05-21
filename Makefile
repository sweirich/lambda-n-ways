GHC = ghc

TEXFILES = DeBruijn.tex HOAS.tex IdInt.tex Lambda.tex Main.tex Simple.tex Unique.tex

.SUFFIXES: .lhs .tex

.lhs.tex:
	awk -f bird2code.awk $< > $*.tex

LC:	*.lhs
#	$(GHC) -package mtl -O2 -Wall --make Main.lhs -o LC
	stack build --copy-bins --local-bin-path .

top.dvi: top.tex $(TEXFILES)
	latex top.tex && latex top.tex

top.ps:	top.dvi
	dvips -t A4 top.dvi -o top.ps

top.pdf: top.tex $(TEXFILES)
	pdflatex top.tex && pdflatex top.tex

.PHONY: timing
timing:	LC
	stack exec -- --output bench.html


#	time ./LC Simple < timing.lam
#	time ./LC Unique < timing.lam
#	time ./LC HOAS < timing.lam
#	time ./LC DB < timing.lam
#	time ./LC DB_C < timing.lam
#	time ./LC DB_P < timing.lam
#	time ./LC DB_B < timing.lam
#	time ./LC Bound < timing.lam
#	time ./LC Unbound < timing.lam
#	time ./LC Scoped < timing.lam

.PHONY:	clean
clean:
	rm -f *.hi *.o LC top.pdf top.ps top.dvi top.log top.aux $(TEXFILES)
