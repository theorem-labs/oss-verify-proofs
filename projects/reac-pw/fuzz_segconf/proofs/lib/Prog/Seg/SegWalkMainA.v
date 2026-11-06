(* Shared text for the segment walks E01, M01, L01, L03 and X01 of reac-pw/fuzz_segconf
   LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): CPseg, the cut record of Prog/SlotInv.v filled with the
   cut predicates of Prog/seg_cuts.v, field for field. The walks prove their SegEnd.seg_<SEG>_stmt at
   CPseg. A record built elsewhere from the same seven predicates is the same term up to unfolding.
   Segment lemma: the cut record the walks share. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotInv seg_cuts.

Definition CPseg : cut_preds :=
  CutPreds P_K138a4 P_K138e8 P_K13984 P_K13ad8 P_K13ae0 P_K13cac P_K13f40.
