(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain): the inner walk 0x13984 .. 0x13ad8,
   L02D.L02_inner, from the seven callee contracts K_L02. The walk is cut at the join 0x139f0 (after the text copy,
   its NUL and the label): Prog/Seg/L02W_front.v walks 0x13984 .. 0x139f0 (memcpy, the NUL store, memset or
   snprintf), Prog/Seg/L02W_back.v walks 0x139f0 .. 0x13ad8 (the drop-in turn or the last turn with m_cross);
   the join's statement and the memory facts both carry are Prog/Seg/L02W_inv.v's.
   Segment lemma of LLVMFuzzerTestOneInput's walk: the inner walk of L02, plain. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02D L02W_inv L02W_front L02W_back.

Theorem L02_inner_holds : K_L02 -> L02_inner.
Proof. intros HK. exact (l02_front HK (l02_back HK)). Qed.
