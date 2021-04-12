GHC = ghc
OUT = results/

LC:	lib/*.lhs lib/*/*.lhs bench/*.lhs 
#	$(GHC) -package mtl -O2 -Wall --make Main.lhs -o LC
	stack build --copy-bins --local-bin-path .

.PHONY: timing
timing:	LC
#	stack run -- --output $(OUT)rand_bench.html --match prefix "rand/"  > $(OUT)output.txt
#	stack run -- --output $(OUT)conv_bench.html --match prefix "conv/"  >> $(OUT)output.txt
#	stack run -- --output $(OUT)nf_bench.html --match prefix "nf/"  >> $(OUT)output.txt
#	stack run -- --output $(OUT)aeq_bench.html --match prefix "aeq/" >> $(OUT)output.txt
#	stack run -- --output $(OUT)con_bench.html --match prefix "con/" >> $(OUT)output.txt
	stack run -- --output $(OUT)capt_bench.html --match prefix "capt/" >> $(OUT)output.txt

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
	rm -f *.hi *.o LC 
