LC:	*.lhs
	ghc -Wall --make Main.lhs -o LC

.PHONY:	clean
clean:
	rm -f *.hi *.o LC
