(* Shared text for the segment walks E01, M01, L01, L03 and X01 of reac-pw/fuzz_segconf
   LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c): CPseg, the cut record of U/Prog/SlotInv.v filled with the
   cut predicates of U/Prog/seg_cuts.v, field for field. The walks prove their SegEnd.seg_<SEG>_stmt at
   CPseg. A record built elsewhere from the same seven predicates is the same term up to unfolding.
   Segment lemma: the cut record the walks share. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotInv seg_cuts.

Definition CPseg : cut_preds :=
  CutPreds P_K13984 P_K139e4 P_K13aac P_K13c34 P_K13c3c P_K13e90 P_K141ec.
