# Find the name of the suite of files we are benchmarking
SUITE_NAME =$(shell grep "impls = [^ ]*" lib/Suite.hs | cut -d" " -f 3)
MACHINE = $(shell uname -n)

OUT = results/$(MACHINE)/$(SUITE_NAME)/

LC:	lib/*.hs lib/*/*.lhs bench/*.lhs 
	stack build 

.PHONY: timing

################ Everything in a single chart

charts: timing random

eval: LC 
	mkdir -p $(OUT)
	uname -a > $(OUT)output.txt
	stack run -- --output $(OUT)eval_bench.html --match prefix "eval/" --csv $(OUT)eval_bench.csv  >> $(OUT)output.txt
#	stack run -- --output $(OUT)eval5_bench.html --match prefix "eval5/" --csv $(OUT)eval5_bench.csv  >> $(OUT)output.txt
#	stack run -- --output $(OUT)eval4_bench.html --match prefix "eval4/" --csv $(OUT)eval4_bench.csv  >> $(OUT)output.txt
#	stack run -- --output $(OUT)evalC_bench.html --match prefix "evalC/" --csv $(OUT)evalC_bench.csv  >> $(OUT)output.txt

timing:	LC
	mkdir -p $(OUT)
	uname -a > $(OUT)output.txt
	stack run -- --output $(OUT)conv_bench.html --match prefix "conv/"  >> $(OUT)output.txt
	stack run -- --output $(OUT)aeq_bench.html --match prefix "aeq/" >> $(OUT)output.txt
	stack run -- --output $(OUT)aeqs_bench.html --match prefix "aeqs/" >> $(OUT)output.txt

normalize: LC 
	rm -rf $(OUT)
	mkdir -p $(OUT)
	uname -a > $(OUT)output.txt
	stack run -- --output $(OUT)eval_bench.html --match prefix "eval/" --csv $(OUT)eval_bench.csv  >> $(OUT)output.txt
	stack run -- --output $(OUT)nf_bench.html --match prefix "nf/" --csv $(OUT)nf_bench.csv  >> $(OUT)output.txt
	stack run -- --output $(OUT)random15_bench.html --match prefix "random15/"  >> $(OUT)output.txt
	stack run -- --output $(OUT)random20_bench.html --match prefix "random20/"  >> $(OUT)output.txt
	stack run -- --output $(OUT)random25_bench.html --match prefix "random25/"  >> $(OUT)output.txt
	stack run -- --output $(OUT)random35_bench.html --match prefix "random35/"  >> $(OUT)output.txt

################ Separate CSV files for each benchmark, plus individual charts for the constructed ones

DB_SUITE = $(wildcard lib/DeBruijn/*.lhs lib/DeBruijn/*.hs lib/DeBruijn/*/*.lhs lib/DeBruijn/*/*.hs lib/DeBruijn/Lazy/*.hs lib/DeBruijn/Lazy/*.lhs lib/DeBruijn/Lazy/*/*.hs)
LN_SUITE = $(wildcard lib/LocallyNameless/*.hs lib/LocallyNameless/*.lhs lib/LocallyNameless/Lazy/*.hs lib/LocallyNameless/Lazy/*.lhs)
NM_SUITE = $(wildcard lib/Named/*.hs lib/Named/*.lhs)
SUITE =  $(DB_SUITE) $(LN_SUITE) $(NM_SUITE)

RESULTS_CONSTRUCTED = $(subst lib,results/constructed,$(subst .hs,.csv,$(subst .lhs,.csv,$(SUITE))))
RESULTS_NF = $(subst lib,results/nf,$(subst .hs,.csv,$(subst .lhs,.csv,$(SUITE))))
RESULTS_RANDOM = $(subst lib,results/random,$(subst .hs,.csv,$(subst .lhs,.csv,$(SUITE))))
RESULTS = $(RESULTS_CONSTRUCTED)

# Suite.hs must list *all* known benchmarks or this part will fail.
#
# It is a good idea to modify bench/Main.lhs to only contain the benchmarks you want. Otherwise, finding the benchmark
# can be pretty slow

csv: $(RESULTS)

results/nf/%.csv : Makefile $(SUITE)
	mkdir -p $(@D)
	uname -a > $(@D)/uname.txt
	stack run -- --csv results/nf/$*.csv --match prefix "nf/$(subst /,.,$*)"

results/random/%.csv : Makefile $(SUITE)
	mkdir -p $(@D)
	uname -a > $(@D)/uname.txt
	stack run -- --csv results/random/$*-15.csv --match prefix "random15/$(subst /,.,$*)"
	stack run -- --csv results/random/$*-20.csv --match prefix "random20/$(subst /,.,$*)"

results/constructed/%.csv : Makefile $(SUITE)
	@echo $(RESULTS)
	mkdir -p $(@D)
	uname -a > $(@D)/uname.txt
	stack run -- -l 
	stack run -- --csv results/constructed/$*-adjust.csv --output results/constructed/$*-adjust.html --match prefix "adjust/$(subst /,.,$*)"
	stack run -- --csv results/constructed/$*-adjustb.csv --output results/constructed/$*-adjustb.html --match prefix "adjustb/$(subst /,.,$*)"
	stack run -- --csv results/constructed/$*-ids.csv --output results/constructed/$*-ids.html --match prefix "ids/$(subst /,.,$*)"
#	stack run -- --csv results/constructed/$*-con.csv --output results/constructed/$*-con.html --match prefix "con/$(subst /,.,$*)"
#	stack run -- --csv results/constructed/$*-capt.csv --output results/constructed/$*-capt.html --match prefix "capt/$(subst /,.,$*)"



