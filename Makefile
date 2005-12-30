LC:	*.lhs
	ghc -Wall --make Main.lhs -o LC

.PHONY: timing
timing:	LC
	time ./LC S < timing.lam
	time ./LC U < timing.lam
	time ./LC H < timing.lam

.PHONY:	clean
clean:
	rm -f *.hi *.o LC
