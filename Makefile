OUT = results/
DB_SUITE = $(wildcard lib/DeBruijn/*.lhs lib/DeBruijn/*.hs lib/DeBruijn/*/*.lhs lib/DeBruijn/*/*.hs lib/DeBruijn/Lazy/*.hs lib/DeBruijn/Lazy/*.lhs lib/DeBruijn/Lazy/*/*.hs)
LN_SUITE = $(wildcard lib/LocallyNameless/*.hs lib/DeBruijn/*/*.hs)
NM_SUITE = $(wildcard lib/Named/*.hs lib/Named/*.lhs)
SUITE = $(DB_SUITE) $(LN_SUITE) $(NM_SUITE)
RESULTS_CONSTRUCTED = $(subst lib,results/constructed,$(subst .hs,.csv,$(subst .lhs,.csv,$(SUITE))))
RESULTS_NF = $(subst lib,results/nf,$(subst .hs,.csv,$(subst .lhs,.csv,$(SUITE))))
RESULTS_RANDOM = $(subst lib,results/random,$(subst .hs,.csv,$(subst .lhs,.csv,$(SUITE))))

LC:	lib/*.hs lib/*/*.lhs bench/*.lhs 
	stack build 

.PHONY: timing

################ Everything in a single chart

timing:	LC
	uname -a > $(OUT)output.txt
	stack run -- --output $(OUT)conv_bench.html --match prefix "conv/"  >> $(OUT)output.txt
	stack run -- --output $(OUT)nf_bench.html --match prefix "nf/"  >> $(OUT)output.txt
	stack run -- --output $(OUT)aeq_bench.html --match prefix "aeq/" >> $(OUT)output.txt

constructed: LC 
	mkdir -p $(OUT)constructed/
	uname -a > $(OUT)constructed/output.txt
	stack run -- --output $(OUT)constructed/ids_bench.html --match prefix "ids/"  >> $(OUT)constructed/output.txt
	stack run -- --output $(OUT)constructed/adjust_bench.html --match prefix "adjust/"  >> $(OUT)constructed/output.txt
	stack run -- --output $(OUT)constructed/con_bench.html --match prefix "con/"  >> $(OUT)constructed/output.txt
	stack run -- --output $(OUT)constructed/capt_bench.html --match prefix "capt/" >> $(OUT)constructed/output.txt

random: LC 
	mkdir -p $(OUT)random/
	uname -a > $(OUT)random/output.txt
	stack run -- --output $(OUT)random/random15_bench.html --match prefix "random15/"  >> $(OUT)random/output.txt
	stack run -- --output $(OUT)random/random20_bench.html --match prefix "random20/"  >> $(OUT)random/output.txt

################ Separate CSV files for each benchmark, plus individual charts for the constructed ones

# Suite.hs must list *all* known benchmarks or this part will fail.
#
# It is a good idea to modify bench/Main.lhs to only contain the benchmarks you want. Otherwise, finding the benchmark
# can be pretty slow

csv: $(RESULTS_NF)

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
	mkdir -p $(@D)
	uname -a > $(@D)/uname.txt
	stack run -- --csv results/constructed/$*-adjust.csv --output results/constructed/$*-adjust.html --match prefix "adjust/$(subst /,.,$*)"
	stack run -- --csv results/constructed/$*-ids.csv --output results/constructed/$*-ids.html --match prefix "ids/$(subst /,.,$*)"


