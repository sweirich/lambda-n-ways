GHC = ghc
OUT = results/

LC:	lib/*.lhs lib/*/*.lhs bench/*.lhs 
#	$(GHC) -package mtl -O2 -Wall --make Main.lhs -o LC
	stack build --copy-bins --local-bin-path .

.PHONY: timing
timing:	LC
	stack run -- --output $(OUT)rand_bench.html --match prefix "rand/"  > $(OUT)output.txt
	stack run -- --output $(OUT)conv_bench.html --match prefix "conv/"  >> $(OUT)output.txt
	stack run -- --output $(OUT)nf_bench.html --match prefix "nf/"  >> $(OUT)output.txt
	stack run -- --output $(OUT)aeq_bench.html --match prefix "aeq/" >> $(OUT)output.txt
#	stack run -- --output $(OUT)con_bench.html --match prefix "con/" >> $(OUT)output.txt
#	stack run -- --output $(OUT)capt_bench.html --match prefix "capt/" >> $(OUT)output.txt

timing_% : LC lib/$(@D)/$(@F).hs
	stack run -- --output $(OUT)con_bench.html --match prefix "con/$(@D).$(@F)" >> $(OUT)output.txt


.PHONY:	clean
clean:
	rm -f *.hi *.o LC 
