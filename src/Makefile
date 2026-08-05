# NATIVE by default (~2x faster than bytecode; decisive with the Map-backed store
# for self-applying the specialiser).  Needs `eval $(opam env)` so ocamlfind finds
# the native extlib/alcotest.  Swap the two lines for a bytecode build.
OCAMLC=ocamlfind ocamlopt -g -package extlib -linkpkg
#OCAMLC=ocamlfind ocamlc -g -package extlib -linkpkg

all: ri

ri: BNFC_Util.ml AbsRwhile.ml PrintRwhile.ml ParRwhile.mli ParRwhile.ml LexRwhile.ml Desugar.ml InvRwhile.ml Subst.ml MacroRwhile.ml EvalRwhile.ml Optimize.ml Program2DataRwhile.ml Core.ml Simp.ml Main.ml
	$(OCAMLC) -o $@ $^

LexRwhile.ml: LexRwhile.mll
	ocamllex LexRwhile.mll

ParRwhile.mli: ParRwhile.mly
	ocamlyacc ParRwhile.mly

BNFC_Util.ml: Rwhile.cf
	bnfc -ocaml Rwhile.cf
	touch BNFC_Util.ml

test-suite: BNFC_Util.ml AbsRwhile.ml PrintRwhile.ml ParRwhile.mli ParRwhile.ml LexRwhile.ml Desugar.ml InvRwhile.ml Subst.ml MacroRwhile.ml EvalRwhile.ml Optimize.ml Program2DataRwhile.ml Core.ml TestSuite.ml
	$(OCAMLC) -package alcotest -linkpkg -o $@ BNFC_Util.ml AbsRwhile.ml PrintRwhile.ml ParRwhile.mli ParRwhile.ml LexRwhile.ml Desugar.ml InvRwhile.ml Subst.ml MacroRwhile.ml EvalRwhile.ml Optimize.ml Program2DataRwhile.ml Core.ml TestSuite.ml

run-tests: test-suite
	./test-suite

# d2p: decode/evaluate a program-as-data value (residual inspector).
d2p: BNFC_Util.ml AbsRwhile.ml PrintRwhile.ml ParRwhile.mli ParRwhile.ml LexRwhile.ml Desugar.ml InvRwhile.ml Subst.ml MacroRwhile.ml EvalRwhile.ml Optimize.ml Program2DataRwhile.ml Core.ml d2p.ml
	$(OCAMLC) -o $@ $^

# measure_proj: baseline the Futamura-projection residual sizes (idea 1).
measure_proj: BNFC_Util.ml AbsRwhile.ml PrintRwhile.ml ParRwhile.mli ParRwhile.ml LexRwhile.ml Desugar.ml InvRwhile.ml Subst.ml MacroRwhile.ml EvalRwhile.ml Optimize.ml Program2DataRwhile.ml Core.ml Simp.ml measure_proj.ml
	$(OCAMLC) -o $@ $^

# specsize: size spec_av's AV store (FpN) to a subject program's variable count.
specsize: BNFC_Util.ml AbsRwhile.ml PrintRwhile.ml ParRwhile.mli ParRwhile.ml LexRwhile.ml Desugar.ml InvRwhile.ml Subst.ml MacroRwhile.ml EvalRwhile.ml Optimize.ml Program2DataRwhile.ml Core.ml specsize.ml
	$(OCAMLC) -o $@ $^

clean:
	-rm -f *.cmi *.cmo *.o *.mli *.cmx ri test-suite

distclean: clean
	-rm -f LexRwhile.* ParRwhile.* LayoutRwhile.* SkelRwhile.* PrintRwhile.* ShowRwhile.* TestRwhile.* AbsRwhile.* TestRwhile BNFC_Util.ml\
	 	ri

install: ri
	cp -f ./ri ../web/

test: ri
	./ri ../examples/rep.rwhile ../examples/list123.val
	./ri -inverse ../examples/ri.rwhile
	./ri -exp ../examples/ri.rwhile
	./ri -p2d ../examples/reverse.rwhile
	./ri ../examples/ri.rwhile ../examples/id_and_nil.p_val
	./ri ../examples/ri.rwhile ../examples/reverse_and_list123.p_val
	./ri ../examples/ri.rwhile ../examples/piorder.p_val
	# ./ri ../examples/ri.rwhile ../examples/ri_reverse_list123.p_val    # 6.6s かかった
	# ./ri ../examples/ri.rwhile ../examples/ri_piorder_atree.p_val      # 1分以上かかるかも
	# ./ri ../examples/ri.rwhile ../examples/ri_ri_reverse_list123.p_val # 1:31:39.23もかかった
	./ri ../examples/enumeration.rwhile ../examples/nil.val
	./ri ../examples/length.rwhile ../examples/list123.val
	# ./ri ../examples/perm_to_code.rwhile ../examples/perm_to_code.val  # failed?
	./ri ../examples/compare.rwhile ../examples/compare0.val
	./ri ../examples/minus.rwhile ../examples/minus.val
	./ri ../examples/rle.rwhile ../examples/rle0.val
	./ri ../examples/rle.rwhile ../examples/rle1.val
	./ri ../examples/rle.rwhile ../examples/rle2.val
	./ri ../examples/rle.rwhile ../examples/rle3.val
	./ri ../examples/rle.rwhile ../examples/rle4.val
	#./ri ../examples/infinite.rwhile ../examples/nil.val   #停止しない例
	./ri ../examples/lookup_ppl2015.rwhile ../examples/nil.val
	./ri ../examples/lookup.rwhile ../examples/nil.val
