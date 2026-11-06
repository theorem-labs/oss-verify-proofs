(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgParseJoin.v (the image-A composition of this
   walk's segment statements), the image-B twin over lib/AU/HPgParseCut.v; itself the composition of
   proofs/reac-pw/fuzz_role/lib/A/RPgParse.v at afaa3cb55c1 (the segment statements joined by induction on the
   loops). *)
(* reac_headamp_prop_parse_result 0x849ac of reac-pw/fuzz_headamp's ASan + UBSan image B (fuzz_headamp.asan-ubsan,
   pinned sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): hd_parse_result_specX from the
   eight segment statements of lib/AU/HPgParseCut.v. The pair loop is joined by induction on its fuel (WALK at fuel 0
   asks a bound no fuel 0 meets), the find loop the same way; lib/AU/HPgParse.v applies hp_join_B to the segment
   theorems. Proves no function by itself (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Local Notation pctx := (@hp_ctx rsegs).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis SE : segE_stmt B MT.
Hypothesis SEPI : segEPI_stmt B MT.
Hypothesis SEXIT : segEXIT_stmt B MT.
Hypothesis SFIND : segFIND_stmt B MT.
Hypothesis SWALK : segWALK_stmt B MT.
Hypothesis SADV : segADV_stmt B MT.
Hypothesis SKEY : segKEY_stmt B MT.
Hypothesis SVAL : segVAL_stmt B MT.

(* the pair loop of the Struct at r, every child, fuel, key slot and state *)
Lemma hpb_walk_all : forall x r n, call_ok B x -> EXIT_ok B MT x ->
forall cc ko cl keys rf, WALK_ok B MT x r cc n ko cl keys rf.
Proof.
intros x r n Hc HX. induction n as [|n IH]; intros cc ko cl keys rf.
- intros F fc regs mem md (_ & _ & (_ & _ & _ & _ & Hb & _) & _). lia.
- assert (HA : forall cc' ko' cl' keys' rf', ADV_ok B MT x r cc' n ko' cl' keys' rf').
  { intros cc' ko' cl' keys' rf'. apply (SADV x r cc' n ko' cl' keys' rf' Hc); [|exact HX].
    intros cc''. apply IH. }
  apply (SWALK x r cc n ko cl keys rf Hc); [intros ko'; apply HA | | exact HX].
  intros ck _. apply (SKEY x r cc n ck cl keys rf Hc); [intros rf'; apply HA|].
  intros ch p. apply (SVAL x r cc n ch p cl keys rf Hc); [intros cl' rf'; apply HA | exact HX].
Qed.

(* the find loop, every property offset and fuel *)
Lemma hpb_find_all : forall x n, call_ok B x -> EPI_ok B MT x -> EXIT_ok B MT x -> forall r, FIND_ok B MT x r n.
Proof.
intros x n Hc HE HX. induction n as [|n IH]; intros r.
- intros F fc regs mem md (_ & _ & (_ & _ & _ & _ & _ & Hb & _) & _). lia.
- apply (SFIND x r n Hc IH HE HX). intros r' cc n' ko cl keys rf. apply (hpb_walk_all x r' n' Hc HX).
Qed.

(* hd_parse_result_specX at image B's entry and literals, for every read-only window *)
Theorem hp_join_B : forall RLO RHI : Z,
hd_parse_result_specX rsegs B MT B_PARSE_RESULT RLO RHI (hi_akey headamp_himg_B) (hi_aph headamp_himg_B)
  (hi_apad headamp_himg_B) (hi_asens headamp_himg_B) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B)
  (hi_dcs headamp_himg_B).
Proof.
intros RLO RHI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs null P O R cap ev bs
  HP Hn H10 H11 H12 H13 HA.
set (x := {| hx_STK := STK; hx_sp0 := sp0; hx_FP := FP; hx_ly := ly; hx_S := S; hx_W0 := W0; hx_mem0 := mem0;
  hx_md0 := md0; hx_own := own; hx_lyc := lyc; hx_Sc := Sc; hx_W := W; hx_memc := memc; hx_mdc := mdc; hx_k := k;
  hx_regs := regs; hx_null := null; hx_P := P; hx_O := O; hx_R := R; hx_cap := cap; hx_ev := ev; hx_bs := bs;
  hx_RLO := RLO; hx_RHI := RHI |} : pctx).
assert (Hc : call_ok B x) by exact (conj HP (conj Hn (conj H10 (conj H11 (conj H12 (conj H13 HA)))))).
pose proof (SEPI x Hc) as HE. pose proof (SEXIT x Hc HE) as HX.
exact (SE x Hc HE (fun r n => hpb_find_all x n Hc HE HX r)).
Qed.

End b.

Print Assumptions hp_join_B.
