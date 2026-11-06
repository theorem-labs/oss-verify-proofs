(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain): its segment statement
   SegEnd.seg_L02_stmt CPseg K_L02, from the slot side (L02.evt_L02_of_inner) and the inner walk
   (L02W.L02_inner_holds), through SegEvt.seg_L02_of_evt.
   Segment lemma of LLVMFuzzerTestOneInput's walk. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SegEnd SegEvt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import SegWalkMainA L02D L02 L02W.

Theorem seg_L02_of_inner : (K_L02 -> L02_inner) -> seg_L02_stmt CPseg K_L02.
Proof.
  intros IH. apply seg_L02_of_evt. intros fx rc B APIf LS SH SK ra empty FF K.
  exact (evt_L02_of_inner (fx:=fx) (rc:=rc) B APIf ra empty FF (IH K)).
Qed.

(** The segment statement SegEnd.plain_halts_of_callees takes for L02. *)
Theorem seg_L02 : seg_L02_stmt CPseg K_L02.
Proof. exact (seg_L02_of_inner L02_inner_holds). Qed.
