(* Reader-walk helpers shared by FSW_pj_set_holds.v and FSW_grow_holds.v (lemma file, rule 24: no function proved):
   a pobj's header kept across a callee journal whose footprint misses the object, and below alloc_ceiling. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSW_pj FSW_K3 FSW_rd FSW_rres FSPstat FSH_Fn_reader FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* a pobj's header kept across a callee journal whose footprint misses the object (FSW_rd.fsw_journal_kept_byte on each of
   its 56 bytes, PjStruct.pj_hdr_eq) *)
Lemma pS_hdr_kept_call : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc
  v ty num str kids keys n cap,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) -> pobj tfibsegs B lyc Sc W memc v ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) memc) v ty num str kids keys n cap ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v ty num str kids keys n cap.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc v ty num str kids keys n cap HJ HU HO HP HF HPo HH.
apply (PjStruct.pj_hdr_eq tfibsegs _ _ v ty num str kids keys n cap HH).
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x).
refine (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc (bv_unsigned x)
  HJ HU HO HP _ (HF _ Hx))).
destruct HPo as [[((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
- right. exists cid, pos. split; [exact Hin | lia].
- left. exists b, m. split; [exact Hb | unfold HEAD in H1; lia].
Qed.
(* ... and below alloc_ceiling under same_below *)
Lemma pS_hdr_below : forall (W : world tfibsegs) m m' v ty num str kids keys n cap,
  same_below m m' alloc_ceiling -> 0 <= v -> v + 56 <= alloc_ceiling ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) m) v ty num str kids keys n cap ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) m') v ty num str kids keys n cap.
Proof.
intros W m m' v ty num str kids keys n cap SB H0 H1 HH.
apply (PjStruct.pj_hdr_eq tfibsegs _ _ v ty num str kids keys n cap HH).
intros x Hx. apply (fsw_mrestrict_below (w_H W) m m' x SB). lia.
Qed.

End R.
