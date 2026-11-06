(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARtSoqz ARtSf1m ARtSnjd ARtSrgm AMTac ARt2_lib ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73.

Module ARt4ak4.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtSoqz ARtSnjd ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_fts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem recycle_post_ok : recycle_post_stmt.
Proof.
  unfold recycle_post_stmt. intros until ra0. intros MI ST LOLE CEIL USP UAL FR RA.
  pose proof alloc_ceiling_val as CV. unfold recycle_ret in *.
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold recycle_frame in FR.
  do 7 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  release_frame FR ST usp.
  finish.
Qed.

(* [comment removed for export] *)

Theorem dorec_entryS_ok : dorec_entryS_stmt.
Proof.
  unfold dorec_entryS_stmt. intros until Q. intros MI ST LOLE CEIL A1 TLO THI TAL TDJ TN TNR TC K.
  pose proof alloc_ceiling_val as CV. unfold dorec_entry, dorec_head in *. subst a1.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 112%nat ST.
  do 12 amz.
  amz. (* [comment removed for export] *)
  amz. amz.
  amz. br_not_taken. (* [comment removed for export] *)
  do 7 amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  eapply K; [exact FR | exact TC | exact MU | exact WM | assumption | exact ST].
Qed.

Theorem dorec_call_ok : dorec_call_stmt.
Proof.
  unfold dorec_call_stmt. intros until Q. intros MI BLO BHI BAL I0 SP8 PC K.
  pose proof alloc_ceiling_val as CV. unfold dorec_callblk, dorec_retpc, cbrec_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  remember (b + 24 + 8 * i) as e eqn:HE.
  replace (b + 152 + 8 * i) with (e + 128) in * by lia.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  exact K.
Qed.

Theorem dorec_ret_ok : dorec_ret_stmt.
Proof.
  unfold dorec_ret_stmt. intros until Q. intros IR CR BLO BHI KM KD.
  pose proof alloc_ceiling_val as CV. unfold dorec_callblk, dorec_retpc, dorec_batchblk, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  amz. amz. (* [comment removed for export] *)
  replace (16 + i + 1) with (16 + (i + 1)) by lia. replace (b + 152 + 8 * i + 8) with (b + 152 + 8 * (i + 1)) by lia.
  amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
  - apply KM. lia.
  - apply KD. lia.
Qed.

Lemma class24_of : forall sb kb, 0 <= sb -> 0 <= kb < 2^28 ->
  Z.shiftr (Z.shiftl (sb + 24 * 2^32 + 16 * kb - sb) 27 mod 2^64) 59 = 24.
Proof.
  intros sb kb Hs Hk. replace (sb + 24 * 2^32 + 16 * kb - sb) with (24 * 2^32 + 16 * kb) by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace ((24 * 2^32 + 16 * kb) * 2^27) with (16 * kb * 2^27 + 24 * 2^59) by lia.
  rewrite <- (Z.mod_unique_pos _ (2^64) 0 (16 * kb * 2^27 + 24 * 2^59)); [|lia|lia].
  symmetry. apply Z.div_unique_pos with (r := 16 * kb * 2^27); lia.
Qed.

Theorem dorec_batch_ok : dorec_batch_stmt.
Proof.
  unfold dorec_batch_stmt. intros until Q. intros MI SLO SHI SAL SB0 SBH KB RSB CBC K.
  pose proof alloc_ceiling_val as CV. unfold dorec_batchblk, dorec_nextpc, lcdealloc_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  rewrite class24_of by lia.
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  exact K.
Qed.

Theorem dorec_next_ok : dorec_next_stmt.
Proof.
  unfold dorec_next_stmt. intros until Q. intros MI ST LOLE CEIL USP UAL TLO THI TAL TDJ TNR TC FR RA KM K0.
  pose proof alloc_ceiling_val as CV. unfold dorec_nextpc, dorec_head in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold dorec_frame in FR.
  amz. (* [comment removed for export] *)
  amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
  - apply KM. lia.
  - (* [comment removed for export] *)
    do 12 amz. amz. (* [comment removed for export] *)
    release_frame FR ST usp.
    rewrite KB. apply K0; [lia | exact ST].
Qed.

Theorem dorec_pop_ok : dorec_pop_stmt.
Proof.
  unfold dorec_pop_stmt. intros until Q. intros MI TLO THI TAL BLO BHI BAL TNR NXR TLR BS0 BSR CNR TC BC KZ KS HK0 HK1.
  pose proof alloc_ceiling_val as CV. unfold dorec_head, dorec_batchblk, dorec_callblk, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof (munch_refl [(T, T + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
  - (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    replace (tn + -1) with (tn - 1) in * by lia.
    replace (if nx =? 0 then 0 else tl) with tl in * by (rewrite (proj2 (Z.eqb_neq nx 0)) by lia; reflexivity).
    amz. if_cases KC; zify_cond KC; rewrite ?Z.mod_small in KC by lia.
    + rewrite KC. eapply KZ; [lia | eassumption | eassumption | exact MU | exact WM | assumption | apply HK0; exact MU].
    + amz. amz. amz. (* [comment removed for export] *)
      eapply KS; [lia | eassumption | eassumption | exact MU | exact WM | assumption | apply HK1; exact MU].
  - (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. amz.
    amz. amz. amz. amz.
    amz.
    replace (tn + -1) with (tn - 1) in * by lia.
    replace (if nx =? 0 then 0 else tl) with 0 in * by (rewrite (proj2 (Z.eqb_eq nx 0)) by lia; reflexivity).
    amz. if_cases KC; zify_cond KC; rewrite ?Z.mod_small in KC by lia.
    + rewrite KC. eapply KZ; [lia | eassumption | eassumption | exact MU | exact WM | assumption | apply HK0; exact MU].
    + amz. amz. amz.
      eapply KS; [lia | eassumption | eassumption | exact MU | exact WM | assumption | apply HK1; exact MU].
Qed.

End CEIL.
End ARt4ak4.


Module ARt4bhx.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSoqz ARtSnjd ARtSrgm ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_png ARt25ye.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt25ye.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).

(* [comment removed for export] *)
Lemma shr32_of_decomp : forall c r, 0 <= c -> 0 <= r < 4294967296 -> Z.shiftr (c * 4294967296 + r) 32 = c.
Proof.
  intros c r Hc Hr. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296.
  symmetry. apply Z.div_unique with (r := r); lia.
Qed.

Lemma div_of_decomp : forall idx s d, 0 < s -> 0 <= d < s -> (idx * s + d) / s = idx.
Proof. intros idx s d Hs Hd. symmetry. apply Z.div_unique with (r := d); lia. Qed.

Lemma divuw_idx : forall X s idx d, 0 <= X < 2^64 -> 0 < s < 2^32 -> 0 <= d < s -> 0 <= idx < 2^31 ->
  X mod 4294967296 = idx * s + d ->
  v_divuw (Z_to_bv 64 X) (Z_to_bv 64 s) = Z_to_bv 64 idx.
Proof.
  intros X s idx d HX Hs Hd Hi HM. unfold v_divuw. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
  change (2 ^ 64) with 18446744073709551616 in HX. change (2^32) with 4294967296 in Hs. change (2^31) with 2147483648 in Hi.
  rewrite (Z.mod_small X 18446744073709551616) by lia. rewrite (Z.mod_small s 18446744073709551616) by lia.
  rewrite (Z.mod_small s 4294967296) by lia.
  replace (s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite HM. rewrite (div_of_decomp idx s d) by lia.
  f_equal. rewrite Z.mod_small by lia. lia.
Qed.

Lemma cas_clear_low : forall st w, 0 <= st < 256 -> 0 <= w -> Z.lxor (st + 256 * w) (Z.land (st + 256 * w) 255) = 256 * w.
Proof.
  intros st w Hs Hw. pose proof (cas_set_low st 0 w ltac:(lia) ltac:(lia) Hw) as E. rewrite Z.lxor_0_r in E. rewrite E. lia.
Qed.

Lemma round_up8_facts : forall n, 0 <= n -> n <= round_up n 8 < n + 8 /\ round_up n 8 mod 8 = 0 /\ round_up n 8 = 8 * ((n + 7) / 8).
Proof.
  intros n Hn. unfold round_up. replace (n + 8 - 1) with (n + 7) by lia.
  pose proof (Z_div_mod_eq_full (n + 7) 8). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. replace (8 * ((n + 7) / 8)) with (((n + 7) / 8) * 8) by lia. apply Z_mod_mult.
Qed.

Set Printing Width 200.

Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- _ /\ _ => split
  end).

Definition cbrec_beq : Z := 0x395c8.     (* [comment removed for export] *)
Definition cbrec_cas : Z := 0x395e4.     (* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma cbrec_prefix :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (cb mh sb ri c idx d mu lo : Z) (Q : machine_state -> Prop),
    let sz := class_size c in
    let p := sb + c * 2^32 + idx * sz in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
    mh = p + d -> 0 <= d < sz -> 1 <= c <= 30 -> 0 <= idx -> (idx + 1) * sz <= mu -> 0 <= mu < 2^32 ->
    kHighMemBeg <= sb -> sb + 2^37 <= 2^47 -> sb + 2^37 <= ri -> ri + 4096 <= alloc_ceiling ->
    ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)] -> ro_cells rsegs m RI_PTR [C8 (Z_to_bv 64 ri)] -> ro_cells rsegs m (ri + 128 * c + 48) [C8 (Z_to_bv 64 mu)] ->
    (forall (a2x a4x a5x a6x a7x : word) (m2 : word -> option byte),
        rw_cells rsegs m2 (bv_unsigned sp + -48) (cbrec_frame s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp + -48) ->
        evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 cb) (Z_to_bv 64 mh)
                            (Z_to_bv 64 sb) (Z_to_bv 64 (sb + 137438953472)) a2x (Z_to_bv 64 p) a4x a5x a6x a7x
                            (Z_to_bv 64 p) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 cbrec_beq) fc None m2 (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cb) (Z_to_bv 64 mh) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 cbrec_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until Q. cbv zeta.
  intros MI ST LOLE CEIL MHD DR CR IDX0 FIT MUR SBLO SBHI RI0 RIHI CSB CRI CMU K.
  pose proof alloc_ceiling_val as CV. unfold cbrec_entry, cbrec_beq, RI_PTR, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof (class_size_range c ltac:(lia)) as CSR. unfold kMaxSize in CSR.
  pose proof (class_size_mod32 c ltac:(lia)) as CSM.
  remember (class_size c) as sz eqn:Hsz.
  remember (sb + c * 2 ^ 32 + idx * sz) as p eqn:Hp.
  remember (ri + 128 * c) as R eqn:HR.
  lit_addrs.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (IDXS : 0 <= idx * sz) by nia.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. if_cases KB; zify_cond KB. { exfalso. rewrite ?Z.mod_small in KB by lia. lia. } (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. if_cases KB2; zify_cond KB2. { exfalso. rewrite ?Z.mod_small in KB2 by lia. nia. } (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  replace (mh - sb) with (c * 4294967296 + (idx * sz + d)) by (rewrite MHD, Hp; change (2^32) with 4294967296; lia).
  assert (LOW32 : 0 <= idx * sz + d < 4294967296) by (change (2^32) with 4294967296 in MUR; nia).
  rewrite (shr32_of_decomp c (idx * sz + d)) by lia.
  replace (Z.land c 31) with c by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  remember (c * 4294967296 + (idx * sz + d)) as X eqn:HX.
  amz. amz. if_cases KB3; zify_cond KB3. { exfalso. rewrite ?Z.mod_small in KB3 by lia. lia. } (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (J : forall (a5x a6x a7x : word), a5x = Z_to_bv 64 sz ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 cb) (Z_to_bv 64 mh)
                        (Z_to_bv 64 sb) (Z_to_bv 64 (sb + 137438953472)) (Z_to_bv 64 c) (Z_to_bv 64 c) (Z_to_bv 64 X) a5x a6x a7x
                        s2 (Z_to_bv 64 728408) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x39584) fc None mm (seg_rom rsegs))) end.
  2:{ amz. if_cases KC; zify_cond KC.
      - (* [comment removed for export] *)
        amz. replace (c + -16) with (c - 16) by lia. amz. amz. amz. try rewrite (Z.mod_small (c - 16) 18446744073709551616) by lia. amz. amz. amz. amz. amz.
        lazymatch goal with |- context [Z_to_bv 64 (Z.land ?x ?y + ?z)] => change (Z_to_bv 64 (Z.land x y + z)) with (Z_to_bv 64 (icT c)) end.
        rewrite (icT_ok c) by lia. rewrite <- Hsz. apply J. reflexivity.
      - amz. if_cases KD; zify_cond KD. { exfalso. rewrite ?Z.mod_small in KD by lia. lia. } (* [comment removed for export] *)
        amz. (* [comment removed for export] *) replace (Z.shiftl c 5) with sz by (rewrite Hsz, class_size_lin, Z.shiftl_mul_pow2 by lia; lia).
        amz. (* [comment removed for export] *) apply J. reflexivity. }
  intros a5x a6x a7x ->.
  assert (XM : X mod 4294967296 = idx * sz + d). { subst X. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia. }
  assert (IDX31 : 0 <= idx < 2^31). { assert (32 * idx <= sz * idx) by (apply Z.mul_le_mono_nonneg_r; lia). change (2^32) with 4294967296 in MUR. lia. }
  assert (XR : 0 <= X < 2^64) by (subst X; lia).
  amz. (* [comment removed for export] *)
  rewrite (divuw_idx X sz idx d XR ltac:(lia) DR IDX31 XM).
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  replace (ri + Z.shiftl c 7) with R by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia).
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite (Z.mod_small idx 4294967296) by lia.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  try rewrite (Z.mod_small (sz * idx + sz) 18446744073709551616) by nia.
  replace (mu <? sz * idx + sz) with false by (symmetry; apply Z.ltb_ge; nia).
  amz. (* [comment removed for export] *)
  replace (Z.shiftl c 32 + sb + sz * idx) with p by (rewrite Z.shiftl_mul_pow2 by lia; rewrite Hp; lia).
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  change ((Z.b2z false + -1) mod 18446744073709551616) with (Z.ones 64).
  try rewrite (Z.mod_small p 18446744073709551616) by lia. rewrite Z.land_comm, Z.land_ones by lia. change (2^64) with 18446744073709551616.
  rewrite (Z.mod_small p 18446744073709551616) by lia.
  amz. if_cases KE; zify_cond KE. { exfalso. rewrite ?Z.mod_small in KE by lia. lia. } (* [comment removed for export] *)
  amz. if_cases KF; zify_cond KF. { exfalso. rewrite ?Z.mod_small in KF by lia. nia. } (* [comment removed for export] *)
  eapply K; [exact FR | exact MU | exact WM | exact MI | exact ST].
Qed.

Lemma rw_cells_nil : forall m A, 0 <= A -> A <= 2^64 -> rw_cells rsegs m A [].
Proof.
  intros m A H0 H1. split; [split; [exact I|]|]; cbn.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
  - split; [lia|]. split; [lia|]. intros i Hi; lia.
Qed.

Lemma div8_of_bounds : forall n g, n <= 8 * g < n + 8 -> (n + 7) / 8 = g.
Proof. intros n g H. symmetry. apply Z.div_unique with (r := n + 7 - 8 * g); lia. Qed.

(* [comment removed for export] *)
Lemma cbrec_ptail :
  forall (ra sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fr4 fr3 fr2 fr1 fr0 frra : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (cb mh p d sb mq g n b1 lo : Z) (old : list byte) (pcell : list cell) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
    mh = p + d -> mh = 16 * mq -> kHighMemBeg <= p -> 0 <= d -> 1 <= n < 2^32 -> n <= 8 * g < n + 8 -> mh + 16 + 8 * g <= alloc_ceiling -> 0 <= b1 < 256 ->
    ((d = 0 /\ pcell = []) \/ (16 <= d /\ pcell = [C8 (Z_to_bv 64 0)])) ->
    rw_cells rsegs m p pcell ->
    rw_cells rsegs m mh [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] ->
    rw_cells rsegs m (2 * mq + 2147450882) [CB (Z.to_nat g) old] ->
    rw_cells rsegs m (bv_unsigned sp + -48) (cbrec_frame fr4 fr3 fr2 fr1 fr0 frra) ->
    poison_consts m ->
    munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (2 * mq + 2147450882, 2 * mq + 2147450882 + g)] m0 m ->
    wmono rsegs m0 m ->
    (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -48) (cbrec_frame fr4 fr3 fr2 fr1 fr0 frra) ->
        rw_cells rsegs m' p pcell ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n)] ->
        bytes_at rsegs m' (2 * mq + 2147450882) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat g)) ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (2 * mq + 2147450882, 2 * mq + 2147450882 + g)] m0 m' ->
        wmono rsegs m0 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + -48) ->
        evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 cb) (Z_to_bv 64 mh) a0' a1' a2' a3' a4' a5' a6' a7'
                            (Z_to_bv 64 p) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (Z_to_bv 64 cbrec_tail) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 cb) (Z_to_bv 64 mh)
                        a0 (Z_to_bv 64 (sb + 137438953472)) a2 a3 a4 a5 a6 a7
                        (Z_to_bv 64 p) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 cbrec_cas) fc None m (seg_rom rsegs)).
Proof.
  intros until Q.
  intros MI ST LOLE CEIL MHD MHQ PLO D0 N1 GR MHR B1R DP PCL HDR SHC FR PC MU WM K.
  pose proof alloc_ceiling_val as CV. unfold cbrec_cas, cbrec_tail, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, CHUNK_QUARANTINE, CHUNK_INVALID, cbrec_frame in *. aobj_lin_all.
  lit_addrs.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (first [ dand13 PC as Pcan Pcf Pthr Pg0 Psh Pg1 Pg2 Pg3 Phme Pgms Prms Pgpg Ppg | destruct PC as (Pcan & Pcf & Pthr & Pg0 & Psh & Pg1 & Pg2 & Pg3 & Phme & Pgms & Prms & Pgpg & Ppg) ]). aobj_lin_all.
  assert (MH4 : mh mod 4 = 0) by (rewrite MHQ; replace (16 * mq) with ((4 * mq) * 4) by lia; apply Z_mod_mult).
  assert (PCS : Z.of_nat (cells_size pcell) <= d) by (destruct DP as [[? ->]|[? ->]]; cbn; lia).
  assert (MQ0 : 0 <= mq) by lia.
  assert (SHB : 2 * mq + 2147450882 + g <= bv_unsigned sp - 112) by lia.
  assert (PB : mh + 16 <= bv_unsigned sp - 112) by lia.
  assert (G8 : (n + 7) / 8 = g) by (apply div8_of_bounds; lia).
  apply (hdr4_join _ _ 3 b1 0) in HDR; [| lia | lia | lia | cbn; tauto]. replace (3 + 256 * b1 + 65536 * 0) with (3 + 256 * b1) in HDR by lia.
  amz. rewrite (land_m4 mh) by first [exact MH4 | plia]. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. rewrite (shl3_mod32 mh) by exact MH4. rewrite !Z.shiftl_0_r. (* [comment removed for export] *)
  change (bv_swrap 32 3) with 3. change (bv_swrap 32 255) with 255.
  amz. (* [comment removed for export] *)
  rewrite sx32_small by lia.
  amz. rewrite (land255_low 3 b1) by lia. (* [comment removed for export] *)
  amz. first [br_not_taken | if_false]. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  rewrite ?Z.lxor_0_r. rewrite (land255_low 3 b1) by lia.
  replace (Z.lxor (3 + 256 * b1) 3) with (256 * b1) by (pose proof (cas_clear_low 3 b1 ltac:(lia) ltac:(lia)) as E; rewrite land255_low in E by lia; lia).
  scstep; zsimp. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  replace (256 * b1) with (0 + 256 * b1 + 65536 * 0) in HDR by lia.
  apply (hdr4_split _ _ 0 b1 0) in HDR; [| lia | lia | lia | cbn; tauto].
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  rewrite (zx32_small n) by lia.
  amz. amz. (* [comment removed for export] *)
  rewrite ?(unsigned_lit n), ?Z.shiftl_0_l, ?Z.lor_0_l by lia.
  amz. amz. (* [comment removed for export] *)
  rewrite ?(Z.mod_small (n + 7) 18446744073709551616) by lia.
  rewrite (land_m8 (n + 7)) by lia. rewrite G8.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
  eapply evt_cut; [eapply poison_ok|].
  1:{ exact MI. }
  1:{ rewrite unsigned_lit by lia. exact ST. }
  1:{ rewrite unsigned_lit by lia. lia. }
  1:{ lia. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ reflexivity. }
  1:{ rewrite MHQ. replace (16 * mq + 16) with ((2 * mq + 2) * 8) by lia. apply Z_mod_mult. }
  1:{ replace (8 * g) with (g * 8) by lia. apply Z_mod_mult. }
  1:{ lia. }
  1:{ unfold kHighMemBeg; plia. }
  1:{ lia. }
  1:{ lia. }
  1:{ intros X; discriminate X. }
  1:{ unfold poison_consts; rebundle. }
  1:{ unfold sh, kShadowOffset. rewrite MHQ. replace (16 * mq + 16) with ((2 * mq + 2) * 8) by lia. rewrite Z_div_mult_full by lia.
      replace (8 * g / 8) with g by (symmetry; replace (8 * g) with (g * 8) by lia; apply Z_div_mult_full; lia).
      replace (2 * mq + 2 + 2147450880) with (2 * mq + 2147450882) by lia. exact SHC. }
  1:{ reflexivity. }
  clear SHC.
  intros ms' PO. destruct_exs PO. (first [ dand6 PO as E MUc WMc MIc STc SHZ | destruct PO as (E & MUc & WMc & MIc & STc & SHZ) ]). aobj_lin_all. subst ms'.
  rewrite ?unsigned_lit in MUc, STc by lia.
  unfold sh, kShadowOffset in MUc, SHZ. rewrite MHQ in MUc, SHZ.
  replace ((16 * mq + 16) / 8 + 2147450880) with (2 * mq + 2147450882) in MUc, SHZ
    by (replace (16 * mq + 16) with ((2 * mq + 2) * 8) by lia; rewrite Z_div_mult_full by lia; lia).
  replace (8 * g / 8) with g in MUc, SHZ by (symmetry; replace (8 * g) with (g * 8) by lia; apply Z_div_mult_full; lia).
  lazymatch type of MUc with munch _ _ ?m' => transport_after_call rsegs mA m' MUc WMc end.
  clear MI. rename STc into ST. rename MIc into MI.
  replace (ret_pc (Z_to_bv 64 235072)) with (Z_to_bv 64 235072) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  eapply K; try eassumption.
Qed.

Theorem cbrec_prim_ok : cbrec_prim_stmt.
Proof.
  unfold cbrec_prim_stmt. intros until Q. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 MHD DR DAL CR IDX0 FIT MUR SBLO SBHI SBAL RI0 RIHI NR MHR B1R PC CSB CRI CMU MAG HDR SHC K.
  pose proof alloc_ceiling_val as CV. subst a0 a1.
  pose proof (class_size_range c ltac:(lia)) as CSR. unfold kMaxSize in CSR.
  pose proof (class_size_mod32 c ltac:(lia)) as CSM.
  change (size_hi n) with (Z.shiftr n 32) in *. rewrite (Z.shiftr_div_pow2 n 32), (Z.div_small n (2^32)) in * by lia.
  remember (class_size c) as sz eqn:Hsz.
  remember (sb + c * 2 ^ 32 + idx * sz) as p eqn:Hp.
  remember (round_up n 8) as r8 eqn:Hr8.
  (first [ pose proof ((round_up8_facts n ltac:(lia))) as dR_3; dand3 dR_3 as R8a R8b R8c | pose proof (round_up8_facts n ltac:(lia)) as (R8a & R8b & R8c) ]). rewrite <- Hr8 in R8a, R8b, R8c.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (IDXS : 0 <= idx * sz) by nia.
  assert (PAL16 : p mod 16 = 0).
  { subst p. set (q := sb / 4096). assert (SBQ : sb = 4096 * q) by (subst q; rewrite (Z_div_mod_eq_full sb 4096) at 1; lia).
    set (u := sz / 32). assert (SZU : sz = 32 * u) by (subst u; rewrite (Z_div_mod_eq_full sz 32) at 1; lia).
    rewrite SBQ, SZU. change (2^32) with 4294967296.
    replace (4096 * q + c * 4294967296 + idx * (32 * u)) with ((256 * q + c * 268435456 + idx * u * 2) * 16) by lia. apply Z_mod_mult. }
  assert (PAL8 : p mod 8 = 0).
  { set (q := p / 16). assert (PQ : p = 16 * q) by (subst q; rewrite (Z_div_mod_eq_full p 16) at 1; lia).
    rewrite PQ. replace (16 * q) with ((2 * q) * 8) by lia. apply Z_mod_mult. }
  assert (MH16 : mh mod 16 = 0).
  { rewrite MHD. set (q := p / 16). assert (PQ : p = 16 * q) by (subst q; rewrite (Z_div_mod_eq_full p 16) at 1; lia).
    set (u := d / 16). assert (DU : d = 16 * u) by (subst u; rewrite (Z_div_mod_eq_full d 16) at 1; lia).
    rewrite PQ, DU. replace (16 * q + 16 * u) with ((q + u) * 16) by lia. apply Z_mod_mult. }
  set (mq := mh / 16) in *. assert (MHQ : mh = 16 * mq) by (subst mq; rewrite (Z_div_mod_eq_full mh 16) at 1; lia). clearbody mq.
  assert (SHF : sh (mh + 16) = 2 * mq + 2147450882).
  { unfold sh, kShadowOffset. rewrite MHQ. replace (16 * mq + 16) with ((2 * mq + 2) * 8) by lia. rewrite Z_div_mult_full by lia. lia. }
  remember ((n + 7) / 8) as g eqn:Hg.
  assert (R8d : r8 / 8 = g) by (rewrite R8c, Z.mul_comm; apply Z_div_mult_full; lia).
  rewrite SHF, R8d in SHC, K.
  unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  assert (MHC : mh + 16 + 8 * g <= alloc_ceiling).
  { assert (IS : idx * sz <= mu - sz) by nia. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    clear - IS Hp MHD DR MUR RI0 RIHI R8c R8a NR CR CSR; lia. }
  (* [comment removed for export] *)
  assert (PCX : exists pcell, ((d = 0 /\ pcell = []) \/ (16 <= d /\ pcell = [C8 (Z_to_bv 64 0)])) /\
                              ((d = 0 /\ pcell = []) \/ (16 <= d /\ rw_cells rsegs m p [C8 (Z_to_bv 64 kAllocBegMagic)]))).
  { destruct (Z.eq_dec d 0) as [Dz|Dnz].
    - exists []. split; left; auto.
    - destruct MAG as [Dz|C]; [lia|]. exists [C8 (Z_to_bv 64 0)].
      assert (16 <= d) by (pose proof (Z_div_mod_eq_full d 16); pose proof (Z.mod_pos_bound d 16 ltac:(lia)); lia).
      split; right; auto. }
  (first [ dex1 PCX as pcell; destruct PCX as [PCE PCM] | dand3 PCX as pcell PCE PCM | destruct PCX as (pcell & PCE & PCM) ]). aobj_lin_all. clear MAG.
  (first [ dand13 PC as Pcan Pcf Pthr Pg0 Psh Pg1 Pg2 Pg3 Phme Pgms Prms Pgpg Ppg | destruct PC as (Pcan & Pcf & Pthr & Pg0 & Psh & Pg1 & Pg2 & Pg3 & Phme & Pgms & Prms & Pgpg & Ppg) ]). aobj_lin_all.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (2 * mq + 2147450882, 2 * mq + 2147450882 + g)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct PCM as [[Dz Ep] | [D16 MAGC]].
  - (* [comment removed for export] *)
    subst pcell.
    eapply cbrec_prefix with (c := c) (idx := idx) (d := d) (mu := mu) (ri := ri) (lo := lo); rewrite <- ?Hsz, <- ?Hp;
      try first [exact MI | exact ST | exact CSB | exact CRI | exact CMU | unfold kHighMemBeg; plia | plia].
    intros a2x a4x a5x a6x a7x m2 FR MUc WMc MIc STc.
    transport_after_call rsegs m m2 MUc WMc.
    clear MUc WMc MI. rename STc into ST. rename MIc into MI.
    unfold cbrec_beq.
    amz. if_cases KG; zify_cond KG. 2:{ exfalso. apply KG. rewrite MHD, Dz. lia. }
    eapply cbrec_ptail with (m0 := m) (cb := cb) (mh := mh) (p := p) (d := d) (sb := sb) (mq := mq) (g := g) (n := n) (b1 := b1) (lo := lo) (old := old) (pcell := []).
    all: lazymatch goal with
         | |- _ \/ _ => left; split; [exact Dz | reflexivity]
         | |- rw_cells _ _ _ [] => apply rw_cells_nil; lia
         | |- poison_consts _ => unfold poison_consts; rebundle
         | |- forall _, _ => intros; eapply K; try eassumption; left; exact Dz
         | |- _ => first [exact MI | exact ST | exact HDR | exact SHC | exact FR | exact MU | exact WM | lia | unfold kHighMemBeg; plia]
         end.
  - (* [comment removed for export] *)
    assert (Ep : pcell = [C8 (Z_to_bv 64 0)]) by (destruct PCE as [[? ?]|[? ->]]; [lia|reflexivity]). subst pcell.
    eapply cbrec_prefix with (c := c) (idx := idx) (d := d) (mu := mu) (ri := ri) (lo := lo); rewrite <- ?Hsz, <- ?Hp;
      try first [exact MI | exact ST | exact CSB | exact CRI | exact CMU | unfold kHighMemBeg; plia | plia].
    intros a2x a4x a5x a6x a7x m2 FR MUc WMc MIc STc.
    transport_after_call rsegs m m2 MUc WMc.
    clear MUc WMc MI. rename STc into ST. rename MIc into MI.
    unfold cbrec_beq.
    amz. if_cases KG; zify_cond KG. { exfalso. rewrite ?Z.mod_small in KG by lia. lia. }
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. first [br_not_taken | if_false]. (* [comment removed for export] *)
    scstep; zsimp. (* [comment removed for export] *)
    amz. if_false. (* [comment removed for export] *)
    eapply cbrec_ptail with (m0 := m) (cb := cb) (mh := mh) (p := p) (d := d) (sb := sb) (mq := mq) (g := g) (n := n) (b1 := b1) (lo := lo) (old := old) (pcell := [C8 (Z_to_bv 64 0)]).
    all: lazymatch goal with
         | |- _ \/ _ => right; split; [exact D16 | reflexivity]
         | |- poison_consts _ => unfold poison_consts; rebundle
         | |- forall _, _ => intros; eapply K; try eassumption; right; assumption
         | |- _ => first [exact MI | exact ST | exact HDR | exact SHC | exact FR | exact MAGC | exact MU | exact WM | lia | unfold kHighMemBeg; plia]
         end.
Qed.

End CEIL.
End ARt4bhx.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ANodijx ANod9v0 APgGeo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeH AFreeH0 AFreeC.

Module AFreeC2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARtSoqz AMTac ARt2_lib ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73 ARt_png ARt_fpo ANodeA7 ANodeA6 ANodl61 AFreeH AFreeH0 AFreeC.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@CR; @CEIL; @LOLE; @HR8; @RIHI; @MXR; @LCLO; @NM3; @NM1; @MFA0; @LKS; @LJ; @SPR; @SBLO; @RILO; @SBHI; @SHE; @HNB; @SZ8; @NOFIT; @HMA; @CV; @HSQ; @MH; @SEP_cr; @NF0; @LWZ; @SPH; @SEP_tr; @Bthr'; @X; @Btp; @SEP_cs; @SEP_rs; @NFH; @A0R; @Btsd'; @SEP_ts; @LO0; @CTHR; @LBthr; @LWS])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; tf_transport segs m m' MU WM.
(* [comment removed for export] *)

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@CEIL; @LOLE; @CHI; @SBLO; @CR; @SBHI; @CTHR; @LCLO; @RILO; @MFA0; @HMA; @HSQ; @Bctx'; @SPH; @NFH; @NM1; @HNB; @NF0])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
Section CachePushPost.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  Variables (lo C c sb ri k maxc nf mfa : Z) (ks junk : list word) (statv nfs v88 : word).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (C + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb c).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (Z.shiftr maxc 1).
  #[warnings="-notation-for-abbreviation"] Local Notation nm := (round_up (4 * (nf + h)) kFaMap).
  #[warnings="-notation-for-abbreviation"] Local Notation fe := (sb + c * 4294967296 + kFreeArrayOffset + mfa).

  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis CLO : aobj C 3888.   (* [comment removed for export] *)
  Hypothesis CHI : C + 3888 <= alloc_ceiling.
  Hypothesis CAL : C mod 16 = 0.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis KR : 0 <= k < 2^28.
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_cs : apart C 3888 sb (2^37).
  Hypothesis SEP_cr : apart C 3888 ri 4096.
  Hypothesis MXR : 2 <= maxc <= 16.
  Hypothesis MXE : maxc mod 2 = 0.
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis LJ : length junk = Z.to_nat h.
  Hypothesis NF0 : 0 <= nf.
  Hypothesis NFH : nf + h < 2^27.
  Hypothesis MFA0 : 0 <= mfa.
  Hypothesis MFAM : mfa mod kFaMap = 0.

  (* [comment removed for export] *)
  Variables (tsd ctx thr : Z).
  Hypothesis CTHR : C = thr + 208.
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_ts : apart thr 4096 sb (2^37).
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis TPLO : bv_unsigned tp <= kShadowOffset.
  Hypothesis TSDLO : tsd + 8 <= kShadowOffset.

  Definition cpush_drain_map_W (sp : word) (C c ri sb nf n mfa nm thr : Z) : list (Z * Z) :=
    let E := C + 80 * c in let R := ri + 128 * c in let fa := free_array_of sb c in let fe := sb + c * 4294967296 + kFreeArrayOffset + mfa in
    [(bv_unsigned sp - 688, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 24, R + 32);
     (R + 80, R + 88); (fa + 4 * nf, fa + 4 * nf + 4 * n); (sh fe, sh fe + (nm - mfa) / 8); (thr + 2872, thr + 2888)].

  Definition cpush_drain_map_post (mm72 mm80 : word) (m7 : word -> option byte) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (cpush_drain_map_W sp C c ri sb nf h mfa nm thr) m7 m'
    /\ wmono rsegs m7 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
    /\ rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz k)))]
    /\ rw_cells rsegs m' (C + 2576) [C8 statv']
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))]
    /\ rw_cells rsegs m' (R + 24) [C8 (wz nm)]
    /\ rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88]
    /\ u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks))
    /\ bytes_at rsegs m' (sh fe) (repeat (Z_to_bv 8 250) (Z.to_nat ((nm - mfa) / 8)))
    /\ rw_cells rsegs m' (thr + 2872) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + (nm - mfa)))].

  #[using="TSDLO TPLO SEP_ts SEP_tr CTHR MFAM MFA0 NFH NF0 LJ LKS MXE MXR SEP_cr SEP_cs SEP_rs RIAL RIHI RILO SBAL SBHI SBLO KR CR CAL CHI CLO RA2 SPA SPH CEIL"] Lemma cpush_drain_map_post_ok : forall (m7 : word -> option byte) (t0' t1' t2' a0r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
      (scr scr2 scr3 scr4 old : list byte) (mm72 mm80 : word),
    lo <= usp - 688 -> mfa < 4 * (nf + h) ->   (* [comment removed for export] *)
    bv_unsigned a0r = fe ->
    mem_inv rsegs m7 -> stk rsegs m7 lo (usp + -48 + -64 + -128 + -48 + -128) ->
    thread_cells m7 tp tsd ctx thr -> poison_consts m7 ->
    ro_cells rsegs m7 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m7 0xb1d88 [C8 (wz ri)] -> ro_cells rsegs m7 0xb1d80 [C4 (wz 4294967295)] ->
    ro_cells rsegs m7 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m7 (CF + 144) [C8 (wz 0)] ->
    rw_cells rsegs m7 (usp + -48) (lcd_frame s4 s3 s2 s1 s0 ra) ->
    rw_cells rsegs m7 (usp + -48 + -64) (lcdrain_frame scr (wz lcdealloc_after)) ->
    rw_cells rsegs m7 (usp + -48 + -64 + -128)
             (rta_frame scr2 (R + 8) s11 s10 s9 s8 s7 s6 s5 (wz (sb + c * 4294967296 + 16 * k)) (wz c) (wz 0xb1d58) (wz C) (wz E) (wz lcdrain_ret)) ->
    rw_cells rsegs m7 (usp + -48 + -64 + -128 + -48) (efas_frame scr3 (wz (usp + -48 + -56)) (wz c) (wz nf) (wz R) (wz rta_efasret)) ->
    rw_cells rsegs m7 (usp + -48 + -64 + -128 + -48 + -128)
             (mapcb_frame scr4 (wz 0xb1d58) (wz R) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)) ->   (* [comment removed for export] *)
    rw_cells rsegs m7 E [C4 (wz (maxc - h)); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)] ->
    rw_cells rsegs m7 (C + 2576) [C8 statv] ->
    rw_cells rsegs m7 R [C8 (wz kMutexWriter)] ->
    rw_cells rsegs m7 (R + 16) [C8 (wz nf)] ->
    rw_cells rsegs m7 (R + 24) [C8 (wz mfa)] ->
    rw_cells rsegs m7 (R + 80) [C8 nfs; C8 v88] ->
    u32arr rsegs m7 (fa + 4 * nf) junk ->
    rw_cells rsegs m7 (sh fe) [CB (Z.to_nat ((nm - mfa) / 8)) old] ->
    rw_cells rsegs m7 (thr + 2872) [C8 mm72; C8 mm80] ->
    evt rsegs (cpush_drain_map_post mm72 mm80 m7)
        (MS (mkR (wz mapfixed_resume) (wz (usp + -48 + -64 + -128 + -48 + -128)) gp tp t0' t1' t2' (wz (nm - mfa)) (wz 1)
                 a0r a1' a2' a3' a4' a5' a6' a7'
                 (wz fe) (wz efas_name) (wz PSC) (wz h) (wz (E + 16 + 4 * (maxc - h))) (wz (nf + h)) (wz 2305843009213693952)
                 (wz fa) (wz 1152921504607895551) (wz kMutexWriter) t3' t4' t5' t6')
            F (wz mmap_after_pc) fc None m7 (seg_rom rsegs)).
  Proof.
    intros until mm80. intros LOLE NOFIT A0R MI7 ST7 TC7 PC7 CSB7 CRI7 CITV7 CGCF7 CMLM7 LF DF RF EF MF PCL STA7 MX7 NFC7 MFC7 NFS7 DST7 SHC THS.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST7 as [? _]; assumption).
    pose proof (maxc_half maxc MXR MXE) as [MH HR8]. pose proof (class_size_range c CR) as CSR. unfold kMaxSize in CSR.
    pose proof (roundup_famap_range (4 * (nf + h)) ltac:(lia)) as [NM1 NM2]. pose proof (roundup_famap_cap (4 * (nf + h)) ltac:(lia)) as NM3.
    unfold lcdrain_ret, lcdealloc_after, rta_efasret, efas_mapret in *.
    pose proof TC7 as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    pose proof PC7 as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    unfold kHighMemBeg, free_array_of, kFaMap, kFreeArrayOffset, CF, kShadowOffset in *.
    (* [comment removed for export] *)
    remember (round_up (4 * (nf + h)) 262144) as nmv eqn:HNM.
    assert (HMA : mfa = 8 * (mfa / 8)).
    { pose proof (Z_div_mod_eq_full mfa 8) as X. rewrite (mod0_down mfa 262144 8 ltac:(exists 32768; reflexivity) MFAM) in X. lia. }
    assert (HNB : nmv = 8 * (nmv / 8)).
    { pose proof (Z_div_mod_eq_full nmv 8) as X. rewrite (mod0_down nmv 262144 8 ltac:(exists 32768; reflexivity) NM2) in X. lia. }
    assert (HSQ : sb = 4096 * (sb / 4096)).
    { pose proof (Z_div_mod_eq_full sb 4096) as X. rewrite SBAL in X. lia. }
    set (ma := mfa / 8) in *. set (nb8 := nmv / 8) in *. set (sq := sb / 4096) in *. clearbody ma nb8 sq.
    assert (SHE : sh fe = 512 * sq + c * 536870912 + 469762048 + 2147450880 + ma).
    { unfold sh, kFreeArrayOffset, kShadowOffset. rewrite HMA, HSQ.
      replace (4096 * sq + c * 4294967296 + 3758096384 + 8 * ma) with ((512 * sq + c * 536870912 + 469762048 + ma) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
    assert (SZ8 : (nmv - mfa) / 8 = nb8 - ma) by (rewrite HMA, HNB; replace (8 * nb8 - 8 * ma) with ((nb8 - ma) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    unfold kFreeArrayOffset in SHE. rewrite SHE, SZ8 in *.
    pose proof (munch_refl (cpush_drain_map_W sp C c ri sb nf h mfa nmv thr) m7) as MU.
    unfold cpush_drain_map_W, free_array_of, kFreeArrayOffset in MU. cbv zeta in MU. rewrite ?SHE, ?SZ8 in MU.
    pose proof (wmono_refl rsegs m7) as WM.
    (* [comment removed for export] *)
    eapply evt_cut; [| intros ms' HQ; exact HQ].
    eapply (map_post_ok gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m7
              (usp + -48 + -64 + -128 + -48) lo (nmv - mfa) (sb + c * 4294967296 + 3758096384 + mfa) (sb + c * 4294967296 + 3758096384 + mfa) scr4); [> try (fside CV) .. | idtac].
    all: try (unfold CF; first [kcell | lia]).
    intros t0g t1g t2g a1g a2g a3g a4g a5g a6g a7g t3g t4g t5g t6g m8 MU8 WM8 MI8 ST8.
    rewrite ?unsigned_lit in MU8, ST8 by lia. clear MF. kpost MU8 WM8.
    replace (ret_pc (Z_to_bv 64 0x3a1d8)) with (Z_to_bv 64 0x3a1d8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    assert (TC8 : thread_cells m8 tp tsd ctx thr) by (unfold thread_cells; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [assumption | lia]).
    assert (PC8 : poison_consts m8) by (unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption).
    eapply evt_cut; [eapply (efas_mapped_ok poison_ok thread_stats_ok gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m8
                               (usp + -48 + -64 + -128) lo R nmv mfa (sb + c * 4294967296 + 3758096384 + mfa) tsd ctx thr old scr3 mm72 mm80)|];
      [> try (fside CV) .. | idtac].
    all: try (unfold off_th_stats, kShadowOffset; first [kcell | slia | zmod | rewrite ?SHE, ?SZ8; kcell
                                                        | replace (thr + 2800 + 72) with (thr + 2872) by lia; kcell]).
    intros ms' PO. destruct_exs PO. (first [ dand8 PO as E9 MUc WMc MI9 ST9 MFC9 SHP THS9 | destruct PO as (E9 & MUc & WMc & MI9 & ST9 & MFC9 & SHP & THS9) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST9 by lia. unfold off_th_stats in MUc, THS9. rewrite ?SHE, ?SZ8 in MUc, SHP.
    replace (thr + 2800 + 72) with (thr + 2872) in MUc, THS9 by lia. replace (thr + 2800 + 88) with (thr + 2888) in MUc by lia.
    (* [comment removed for export] *)
    kp SHP.
    clear EF SHC THS Cini Ckey Ctsd Cctx Cthr2 TC7 TC8 PC7 PC8. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x39f74)) with (Z_to_bv 64 0x39f74) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
    pose proof (munch_refl [(usp - 688, usp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88);
                            (sb + c * 4294967296 + 3758096384 + 4 * nf, sb + c * 4294967296 + 3758096384 + 4 * nf + 4 * h)] m9) as MUB.
    pose proof (wmono_refl rsegs m9) as WMB.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells rsegs m9 E _ |- _ =>
      pose proof (line_chunks m9 E _ _ _ ks (Z.to_nat (maxc - h)) (Z.to_nat h) H LKS ltac:(lia)) as SRC end.
    rewrite !Z2Nat.id in SRC by lia.
    remember (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) as ws eqn:HWS.
    assert (LWS : length ws = Z.to_nat h) by (subst ws; rewrite firstn_length_le by (rewrite skipn_length; lia); reflexivity).
    assert (LWZ : Z.of_nat (length ws) = h) by (rewrite LWS, Z2Nat.id by lia; reflexivity).
    assert (LJZ : Z.of_nat (length junk) = h) by (rewrite LJ, Z2Nat.id by lia; reflexivity).
    eapply evt_cut; [eapply (rta_post_ok mrtos_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m9 (usp + -48 + -64) lo ri sb c
                               (usp + -48 + -56) (E + 16 + 4 * (maxc - h)) h nf 1 nfs v88 ws junk scr2)|];
      [> try (fside CV) .. | idtac].
    all: try (fside CV).
    all: try zmod.
    intros ms' PO. destruct_exs PO. (first [ dand10 PO as E5 MUc WMc MI5 ST5 MX5 NFC5 NFS5 SRC5 DST5 | destruct PO as (E5 & MUc & WMc & MI5 & ST5 & MX5 & NFC5 & NFS5 & SRC5 & DST5) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST5 by lia. unfold free_array_of in MUc, DST5.
    clear SRC DST7 NFS7. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RF); kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x39cd0)) with (Z_to_bv 64 0x39cd0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
    (* [comment removed for export] *)
    eapply (lcdrain_post_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 (usp + -48) lo scr);
      [> try (fside CV) .. | idtac].
    all: try zmod.
    intros t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f m6 MU6 WM6 MI6 ST6.
    rewrite ?unsigned_lit in MU6, ST6 by lia. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DF); kpost MU6 WM6.
    replace (ret_pc (Z_to_bv 64 0x39a88)) with (Z_to_bv 64 0x39a88) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (lcdealloc_after_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m6
                               usp lo C c sb k (maxc - h) maxc ks)|];
      [> try (fside CV) .. | idtac].
    all: try (fside CV). all: try zmod.
    intros ms' PO. destruct_exs PO. (first [ dand7 PO as E7 MUc WMc MI7 ST7' PC7' STA7' | destruct PO as (E7 & MUc & WMc & MI7 & ST7' & PC7' & STA7') ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST7' by lia.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_LF); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_SRC5); kpost MUc WMc. rewrite Z_to_bv_bv_unsigned. subst ws.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mz end.
    unfold keep in SHP. eapply bytes_at_transport in SHP; [| exact MUB | rewrite repeat_length; cbn [disjoint_from]; lia].
    apply evt_done. unfold cpush_drain_map_post, cpush_drain_map_W, free_array_of, kFreeArrayOffset, kFaMap. cbv zeta. subst nmv. rewrite ?SHE, ?SZ8.
    hot_eexists_all. split; [reflexivity|].
    split. { exact MU. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [kcell | eassumption].
  Qed.
End CachePushPost.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
End AFreeC2.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeS.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSf1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR.ARt4ak4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR.ARt4bhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeS.ARt4tam OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANod9v0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeS.ARtSxaw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR.AFreeC2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; tf_transport segs m m' MU WM.
(* [comment removed for export] *)

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@CR; @LOLE; @CSR; @LBthr; @HP; @BLO; @DR; @IDX0; @MHD; @Bthr'; @SZ16; @SB16; @D16; @IR; @MHR; @R8E; @FIT; @MUR; @Bctx'; @NF0; @LBctx2; @NFH; @Btp])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= first [ solve [ hot_tf_cut; hot_tf_lia0 ] | hot_tf_lia0 ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TfIncl.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_with_region B S a n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TfIncl.tf_with_region_fast B S a n.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LKS; @LJ; @DR; @BLO; @RILO; @SPR; @CSR; @LBthr; @SBLO; @MXR; @HH8; @PIN; @HP; @SEP_sr; @LOLE; @FIT; @CEIL; @RIHI; @MUFA; @ISZ; @DSZ; @MHD; @SZ16; @IR; @NR; @R8E; @D16; @CNTB; @SB16; @CR; @BFORM; @CV; @KBR; @R81; @RQ; @R82; @X; @SPH; @NF0; @NFH; @SEP_ts; @SEP_tp; @SEP_tr; @MUR; @SEP_tm; @IDX0; @SEP_cs; @K16; @MHR; @BHI; @SEP_bp; @Bthr'; @SEP_bt; @TU; @SEP_Cr; @SEP_bm; @SEP_bfa; @SEP_rs; @SBHI])).
Ltac hot_lia_full := Zify.zify; xlia zchecker.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition cbrec_prim2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (cb mh sb ri c idx d mu n b1 lo : Z) (old : list byte) (Q : machine_state -> Prop),
    let size := class_size c in
    let p := sb + c * 2^32 + idx * size in
    let r8 := round_up n 8 in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
    a0 = wz cb -> a1 = wz mh ->
    mh = p + d -> 0 <= d < size -> d mod 16 = 0 -> 1 <= c <= 30 -> 0 <= idx -> (idx + 1) * size <= mu -> 0 <= mu < 2^32 ->
    kHighMemBeg <= sb -> sb + 2^37 <= 2^47 -> sb mod 4096 = 0 -> sb + 2^37 <= ri -> ri + 4096 <= alloc_ceiling ->
    1 <= n < 2^32 -> mh + 16 + r8 <= 2^47 -> 0 <= b1 < 256 ->
    poison_consts m ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m RI_PTR [C8 (wz ri)] -> ro_cells rsegs m (ri + 128 * c + 48) [C8 (wz mu)] ->
    (d = 0 \/ rw_cells rsegs m p [C8 (wz kAllocBegMagic)]) ->
    rw_cells rsegs m mh [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m (sh (mh + 16)) [CB (Z.to_nat (r8 / 8)) old] ->
    (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -48) (cbrec_frame s4 s3 s2 s1 s0 ra) ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + r8 / 8)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp - 48) ->
        evt rsegs Q (MS (mkR ra' (wz (bv_unsigned sp + -48)) gp tp t0' t1' t2' (wz cb) (wz mh) a0' a1' a2' a3' a4' a5' a6' a7'
                            (wz p) (wz 0xb1d58) (wz 137438953472) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz cbrec_tail) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz cbrec_entry) fc None m (seg_rom rsegs)).

End CEIL.


(* [comment removed for export] *)
Definition it_regs (sp gp tp : word) (T b cnt : Z) (s10 s11 : word)
    (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (j : Z) : bvmap 5 word :=
  mkR ra' sp gp tp t0' t1' t2' (wz T) (wz 0xb1d58) a0' a1' a2' a3' a4' a5' a6' a7'
      (wz LMA_L) (wz LMA_STAT) (wz b) (wz (2^37)) (wz cnt) (wz (b + 152 + 8 * j)) (wz (cnt + 16)) (wz (16 + j)) s10 s11 t3' t4' t5' t6'.
(* [comment removed for export] *)
Definition head_regs (sp gp tp : word) (T : Z) (s10 s11 : word)
    (ra' : word) (tn : Z) (a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' : word) : bvmap 5 word :=
  mkR ra' sp gp tp t0' t1' t2' (wz T) (wz 0xb1d58) (wz tn) a1' a2' a3' a4' a5' a6' a7'
      (wz LMA_L) (wz LMA_STAT) s4' (wz (2^37)) s6' s7' s8' s9' s10 s11 t3' t4' t5' t6'.

Section DoRec.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (rax sp : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  (* [comment removed for export] *)
  Variables (lo T b cnt i : Z) (scr : list byte) (cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word).
  (* [comment removed for export] *)
  Variables (tsd ctx thr sb ri : Z).

  Let CBPRIM : cbrec_prim2_stmt. Proof. exact cbrec_prim_ok. Qed.   (* [comment removed for export] *)

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp + 112).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPE : tp = wz TP.
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis PCo : poison_consts m.
  Hypothesis THRA : thr mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis BLO : kHighMemBeg <= b.
  Hypothesis BHI : b + 8192 <= alloc_ceiling.
  Hypothesis BAL : b mod 8 = 0.
  Hypothesis CNTB : 0 <= cnt <= 1021.
  (* [comment removed for export] *)
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_sr : sb + 2^37 <= ri.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_ts : apart thr 4096 sb (2^37).
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis SEP_cs : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_bt : apart b 8192 thr 4096.
  Hypothesis SEP_bc : apart b 8192 ctx 0x10000.
  Hypothesis SEP_br : apart b 8192 ri 4096.
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1d78 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m RI_PTR [C8 (wz ri)].
  (* [comment removed for export] *)
  Hypothesis DF : rw_cells rsegs m (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0).
  Hypothesis TR : alloc_ceiling <= T.   (* [comment removed for export] *)
  Hypothesis TU : bv_unsigned sp + 112 <= T.
  (* [comment removed for export] *)
  Variable kb : Z.
  Hypothesis BFORM : b = sb + 24 * 2^32 + 16 * kb.
  Hypothesis KBR : 0 <= kb /\ 16 * kb + 8192 <= 3758096384.

  (* [comment removed for export] *)
  Lemma cbc_rw : forall (mm : word -> option byte),
    rw_cells rsegs mm (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs mm (bv_unsigned sp + 8) [C8 (wz C)].
  Proof.
    intros mm H. unfold dorec_frame in H.
    apply (rw_cells_app_split mm (bv_unsigned sp) [CB 8 scr] _) in H as [_ H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
    apply (rw_cells_app_split mm _ [C8 (wz C)] _) in H as [H _]. exact H.
  Qed.
  Lemma cbc_ro : forall (mm : word -> option byte),
    rw_cells rsegs mm (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    ro_cells rsegs mm (bv_unsigned sp + 8) [C8 (wz C)].
  Proof.
    intros mm H. unfold dorec_frame in H.
    apply (rw_cells_app_split mm (bv_unsigned sp) [CB 8 scr] _) in H as [_ H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
    exact (rw_ro_prefix1 mm _ _ _ H).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="KBR BFORM kb DF CRI CSB SEP_bt SEP_cs SEP_tc SEP_tr SEP_ts SEP_sr RIHI RILO SBAL SBHI SBLO CNTB BAL BHI BLO THRA PCo TSDL TC TPE SPA SPH CEIL ST MI CBPRIM ctx tsd Clg"] Lemma iter_prim_push : forall (Q : machine_state -> Prop)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' pw statv : word)
      (mh c idx d mu n b1 rf rfd cntc maxc k : Z) (old : list byte) (ks : list word),
    let size := class_size c in let p := sb + c * 2^32 + idx * size in let r8 := round_up n 8 in let E := C + 80 * c in
    lo <= bv_unsigned sp - 112 ->
    0 <= i < cnt -> bv_unsigned pw = mh -> mh = p + d -> 0 <= d < size -> d mod 16 = 0 -> 1 <= c <= 30 -> 0 <= idx -> (idx + 1) * size <= mu -> 0 <= mu < 2^32 ->
    16 * k = idx * size -> 1 <= n < 2^32 -> mh + 16 + r8 <= 2^47 -> 0 <= b1 < 256 -> 0 <= rf < 2^64 -> 0 <= rfd < 2^64 ->
    0 <= cntc < maxc -> maxc <= 16 -> length ks = 16%nat -> apart b 8192 p size ->
    rw_cells rsegs m (b + 24 + 8 * i) [C8 pw] ->
    ro_cells rsegs m (ri + 128 * c + 48) [C8 (wz mu)] ->
    (d = 0 \/ rw_cells rsegs m p [C8 (wz kAllocBegMagic)]) ->
    rw_cells rsegs m mh [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m (sh (mh + 16)) [CB (Z.to_nat (r8 / 8)) old] ->
    rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)] ->
    rw_cells rsegs m E [C4 (wz cntc); C4 (wz maxc); C8 (wz size); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    (i + 1 < cnt -> forall (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        ro_cells rsegs m' (ri + 128 * c + 48) [C8 (wz mu)] ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        rw_cells rsegs m' E [C4 (wz (cntc + 1)); C4 (wz maxc); C8 (wz size); CB 64 (u32s (upd ks (Z.to_nat cntc) (wz k)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + r8 / 8);
               (thr + 2840, thr + 2856); (E, E + 80); (C + 2576, C + 2584)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (i + 1))
                        F (wz dorec_callblk) fc None m' (seg_rom rsegs))) ->
    (i + 1 = cnt -> forall (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        ro_cells rsegs m' (ri + 128 * c + 48) [C8 (wz mu)] ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        rw_cells rsegs m' E [C4 (wz (cntc + 1)); C4 (wz maxc); C8 (wz size); CB 64 (u32s (upd ks (Z.to_nat cntc) (wz k)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + r8 / 8);
               (thr + 2840, thr + 2856); (E, E + 80); (C + 2576, C + 2584)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (i + 1))
                        F (wz dorec_batchblk) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' i) F (wz dorec_callblk) fc None m (seg_rom rsegs)).
  Proof.
    intros until ks. cbv zeta. intros LOLE IR PW MHD DR DAL CR IDX0 FIT MUR K16 NR MHR B1R RFR RFDR CNTC MXC LKS SEP_bp
           ENT CMU MAG HDR SHC TRF LINE STA KM KD.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (class_size_range c CR) as CSR. unfold kMaxSize in CSR. pose proof (class_size_mod32 c CR) as CSM.
    pose proof (round_up_ge n 8 ltac:(lia)) as R81. pose proof (round_up_lt n 8 ltac:(lia)) as R82. pose proof (round_up_mod n 8 ltac:(lia)) as R83.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold it_regs, kHighMemBeg, RI_PTR, LMA_L, LMA_STAT in *. rewrite TPL in *. change (6194136 - 88) with 6194048 in Ctsd.
    pose proof (cbc_ro m DF) as CBC.
    remember (round_up n 8) as r8 eqn:HR8. remember (class_size c) as size eqn:HSZ.
    remember (sb + c * 2^32 + idx * size) as p eqn:HP.
    (* [comment removed for export] *)
    assert (SZ16 : size = 16 * (size / 16)).
    { pose proof (Z_div_mod_eq_full size 16) as X. rewrite (mod0_down size 32 16 ltac:(exists 2; reflexivity) CSM) in X. lia. }
    assert (SB16 : sb = 16 * (sb / 16)).
    { pose proof (Z_div_mod_eq_full sb 16) as X. rewrite (mod0_down sb 4096 16 ltac:(exists 256; reflexivity) SBAL) in X. lia. }
    assert (D16 : d = 16 * (d / 16)) by (pose proof (Z_div_mod_eq_full d 16) as X; rewrite DAL in X; lia).
    assert (R8E : r8 = 8 * (r8 / 8)) by (pose proof (Z_div_mod_eq_full r8 8) as X; rewrite R83 in X; lia).
    set (sq := size / 16) in *. set (bq := sb / 16) in *. set (dq := d / 16) in *. set (rq := r8 / 8) in *.
    assert (RQ : r8 / 8 = rq) by reflexivity. clearbody sq bq dq rq.
    assert (SHE : sh (mh + 16) = 2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880).
    { unfold sh, kShadowOffset. rewrite MHD, HP, SB16, SZ16, D16.
      replace (16 * bq + c * 2 ^ 32 + idx * (16 * sq) + 16 * dq + 16) with ((2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    rewrite SHE in *.
    (* [comment removed for export] *)
    assert (ISZ : 0 <= idx * size) by (apply Z.mul_nonneg_nonneg; lia).
    assert (PIN : sb <= p /\ p + size <= sb + 2^37) by (rewrite HP; lia).
    assert (DSZ : d + 16 <= size) by lia.
    assert (SEP_tp : apart thr 4096 p size) by (revert SEP_ts; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_tm : apart thr 4096 mh 16) by (revert SEP_ts; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_cp : apart ctx 65536 p size) by (revert SEP_cs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_cm : apart ctx 65536 mh 16) by (revert SEP_cs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_bm : apart b 8192 mh 16) by (revert SEP_bp; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880, 2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880 + rq);
               (thr + 2840, thr + 2856); (C + 80 * c, C + 80 * c + 80); (C + 2576, C + 2584)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    unfold dorec_callblk.
    eapply (dorec_call_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m b i pw); [> try (fside CV) .. | idtac].
    rewrite <- (Z_to_bv_bv_unsigned pw), PW. unfold cbrec_entry.
    (* [comment removed for export] *)
    eapply (CBPRIM _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m
              (bv_unsigned sp + 8) mh sb ri c idx d mu n b1 lo old); rewrite <- ?HSZ, <- ?HP, <- ?HR8; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?HSZ, <- ?HP, <- ?HR8, ?SHE, ?RQ; first [kcell | fside CV | exact MAG]).
    intros ra1 t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m1 CF1 MAG1 HDR1 SHP1 MU1 WM1 MI1 ST1.
    unfold cbrec_frame in CF1. rewrite ?unsigned_lit in CF1, MU1, ST1 by lia. rewrite ?SHE, ?RQ in SHP1, MU1.
    kp MAG1. kp SHP1. clear MAG HDR SHC. kpost MU1 WM1.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (thr + 2840, thr + 2856); (C + 80 * c, C + 80 * c + 80); (C + 2576, C + 2584)] m1) as MUB.
    pose proof (wmono_refl rsegs m1) as WMB.
    unfold cbrec_tail.
    (* [comment removed for export] *)
    assert (TC1 : thread_cells m1 tp tsd ctx thr) by tcells TPL.
    eapply (cbrec_tailp_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1
              (bv_unsigned sp) lo (bv_unsigned sp + 8) C mh p sb c (idx * size) n CHUNK_INVALID b1 tsd ctx thr rf rfd);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | right; lia | unfold CHUNK_INVALID; lia | zmod | exact (proj1 HDR1) | unfold apart in SEP_tm; lia]).
    intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m2 TRF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in MU2, ST2 by lia.
    clear TRF CF1 TC1. kpost MU2 WM2.
    unfold lcdealloc_entry. rewrite (Z_to_bv_bv_unsigned sp).
    replace p with (sb + c * 4294967296 + 16 * k) at 1 by lia.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (lcdealloc_push_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2
                               lo C c sb k cntc maxc ks statv)|]; rewrite <- ?HSZ; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?HSZ; first [kcell | fside CV | zmod]).
    intros ms' PO. destruct_exs PO. (first [ dand7 PO as E3 MUc WMc MI3 ST3 LINE3 STA3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & LINE3 & STA3) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST3 by lia. rewrite <- ?HSZ in MUc, LINE3.
    clear LINE STA. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 dorec_retpc)) with (Z_to_bv 64 dorec_retpc) by (symmetry; apply ret_pc_even; [unfold dorec_retpc; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    unfold keep in MAG1, SHP1.
    eapply bytes_at_transport in SHP1; [| exact MUB | rewrite repeat_length; cbn [disjoint_from]; lia].
    assert (MAG3 : d = 0 \/ rw_cells rsegs m3 p [C8 (wz 0)]).
    { destruct MAG1 as [EE|CC]; [left; exact EE| right]. xfer CC MUB WMB. exact CC. }
    clear MAG1 MUB WMB.
    (* [comment removed for export] *)
    unfold dorec_retpc.
    eapply (dorec_ret_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 b i cnt); [kung; lia | kung; lia | kung; lia | kung; lia | |].
    - intros LT. eapply (KM LT); first [kcell | exact MAG3 | rewrite ?SHE, ?RQ; first [kcell | exact MU | eassumption] | eassumption].
    - intros EQ. eapply (KD EQ); first [kcell | exact MAG3 | rewrite ?SHE, ?RQ; first [kcell | exact MU | eassumption] | eassumption].
  Qed.

  #[using="KBR BFORM kb DF CRI CSB SEP_bt SEP_cs SEP_tc SEP_tr SEP_ts SEP_rs SEP_sr RIAL RIHI RILO SBAL SBHI SBLO CNTB BAL BHI BLO THRA PCo TSDL TC TPE SPA SPH CEIL ST MI CBPRIM ctx tsd Clg"] Lemma iter_prim_drainfast : forall (Q : machine_state -> Prop)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' pw statv : word)
      (mh c idx d mu n b1 rf rfd maxc k nf mfa : Z) (old : list byte) (ks junk : list word) (nfs v88 : word),
    let size := class_size c in let p := sb + c * 2^32 + idx * size in let r8 := round_up n 8 in let E := C + 80 * c in
    let R := ri + 128 * c in let fa := free_array_of sb c in let h := Z.shiftr maxc 1 in
    lo <= bv_unsigned sp - 320 ->
    0 <= i < cnt -> bv_unsigned pw = mh -> mh = p + d -> 0 <= d < size -> d mod 16 = 0 -> 1 <= c <= 30 -> 0 <= idx -> (idx + 1) * size <= mu -> 0 <= mu < 2^32 ->
    16 * k = idx * size -> 1 <= n < 2^32 -> mh + 16 + r8 <= 2^47 -> 0 <= b1 < 256 -> 0 <= rf < 2^64 -> 0 <= rfd < 2^64 ->
    2 <= maxc <= 16 -> maxc mod 2 = 0 -> length ks = 16%nat -> length junk = Z.to_nat h -> 0 <= nf -> nf + h < 2^27 ->
    4 * (nf + h) <= mfa -> mfa < 2^64 -> mu <= 3758096384 -> apart b 8192 p size ->
    ro_cells rsegs m 0xb1d80 [C4 (wz 4294967295)] ->
    rw_cells rsegs m (b + 24 + 8 * i) [C8 pw] ->
    ro_cells rsegs m (ri + 128 * c + 48) [C8 (wz mu)] ->
    (d = 0 \/ rw_cells rsegs m p [C8 (wz kAllocBegMagic)]) ->
    rw_cells rsegs m mh [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m (sh (mh + 16)) [CB (Z.to_nat (r8 / 8)) old] ->
    rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)] ->
    rw_cells rsegs m E [C4 (wz maxc); C4 (wz maxc); C8 (wz size); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] -> rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 24) [C8 (wz mfa)] ->
    rw_cells rsegs m (R + 80) [C8 nfs; C8 v88] -> u32arr rsegs m (fa + 4 * nf) junk ->
    (i + 1 < cnt -> forall (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        ro_cells rsegs m' (ri + 128 * c + 48) [C8 (wz mu)] ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz size); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz k)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))] -> rw_cells rsegs m' (R + 24) [C8 (wz mfa)] ->
        rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] ->
        u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) ->
        munch [(bv_unsigned sp - 320, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + r8 / 8);
               (thr + 2840, thr + 2856); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88);
               (fa + 4 * nf, fa + 4 * nf + 4 * h)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (i + 1))
                        F (wz dorec_callblk) fc None m' (seg_rom rsegs))) ->
    (i + 1 = cnt -> forall (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        ro_cells rsegs m' (ri + 128 * c + 48) [C8 (wz mu)] ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz size); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz k)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))] -> rw_cells rsegs m' (R + 24) [C8 (wz mfa)] ->
        rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] ->
        u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) ->
        munch [(bv_unsigned sp - 320, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + r8 / 8);
               (thr + 2840, thr + 2856); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88);
               (fa + 4 * nf, fa + 4 * nf + 4 * h)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (i + 1))
                        F (wz dorec_batchblk) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' i) F (wz dorec_callblk) fc None m (seg_rom rsegs)).
  Proof.
    intros until v88. cbv zeta. intros LOLE IR PW MHD DR DAL CR IDX0 FIT MUR K16 NR MHR B1R RFR RFDR MXR MXE LKS LJ NF0 NFH FITF MFH MUFA SEP_bp CITV
           ENT CMU MAG HDR SHC TRF LINE STA MX NFC MFA NFS DST KM KD.
    pose proof (maxc_half maxc MXR MXE) as [MH HH8].
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (class_size_range c CR) as CSR. unfold kMaxSize in CSR. pose proof (class_size_mod32 c CR) as CSM.
    pose proof (round_up_ge n 8 ltac:(lia)) as R81. pose proof (round_up_lt n 8 ltac:(lia)) as R82. pose proof (round_up_mod n 8 ltac:(lia)) as R83.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold it_regs, kHighMemBeg, RI_PTR, LMA_L, LMA_STAT in *. rewrite TPL in *. change (6194136 - 88) with 6194048 in Ctsd.
    pose proof (cbc_ro m DF) as CBC.
    remember (round_up n 8) as r8 eqn:HR8. remember (class_size c) as size eqn:HSZ.
    remember (sb + c * 2^32 + idx * size) as p eqn:HP.
    (* [comment removed for export] *)
    assert (SZ16 : size = 16 * (size / 16)).
    { pose proof (Z_div_mod_eq_full size 16) as X. rewrite (mod0_down size 32 16 ltac:(exists 2; reflexivity) CSM) in X. lia. }
    assert (SB16 : sb = 16 * (sb / 16)).
    { pose proof (Z_div_mod_eq_full sb 16) as X. rewrite (mod0_down sb 4096 16 ltac:(exists 256; reflexivity) SBAL) in X. lia. }
    assert (D16 : d = 16 * (d / 16)) by (pose proof (Z_div_mod_eq_full d 16) as X; rewrite DAL in X; lia).
    assert (R8E : r8 = 8 * (r8 / 8)) by (pose proof (Z_div_mod_eq_full r8 8) as X; rewrite R83 in X; lia).
    set (sq := size / 16) in *. set (bq := sb / 16) in *. set (dq := d / 16) in *. set (rq := r8 / 8) in *.
    assert (RQ : r8 / 8 = rq) by reflexivity. clearbody sq bq dq rq.
    assert (SHE : sh (mh + 16) = 2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880).
    { unfold sh, kShadowOffset. rewrite MHD, HP, SB16, SZ16, D16.
      replace (16 * bq + c * 2 ^ 32 + idx * (16 * sq) + 16 * dq + 16) with ((2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    rewrite SHE in *.
    (* [comment removed for export] *)
    assert (ISZ : 0 <= idx * size) by (apply Z.mul_nonneg_nonneg; lia).
    assert (PIN : sb <= p /\ p + size <= sb + 2^37) by (rewrite HP; lia).
    assert (DSZ : d + 16 <= size) by lia.
    assert (SEP_tp : apart thr 4096 p size) by (revert SEP_ts; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_tm : apart thr 4096 mh 16) by (revert SEP_ts; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_cp : apart ctx 65536 p size) by (revert SEP_cs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_cm : apart ctx 65536 mh 16) by (revert SEP_cs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_bm : apart b 8192 mh 16) by (revert SEP_bp; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_bfa : apart b 8192 (sb + c * 4294967296 + 3758096384 + 4 * nf) (4 * Z.shiftr maxc 1)).
    { unfold apart. try (generalize alloc_ceiling_val); clear - BFORM KBR CR NF0 NFH HH8; try pose proof alloc_ceiling_val. lia. }
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880, 2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880 + rq);
               (thr + 2840, thr + 2856); (C + 80 * c, C + 80 * c + 80); (C + 2576, C + 2584); (ri + 128 * c, ri + 128 * c + 8); (ri + 128 * c + 16, ri + 128 * c + 24);
               (ri + 128 * c + 80, ri + 128 * c + 88); (sb + c * 4294967296 + 3758096384 + 4 * nf, sb + c * 4294967296 + 3758096384 + 4 * nf + 4 * Z.shiftr maxc 1)] m) as MU.
    unfold free_array_of in DST, KM, KD.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    unfold dorec_callblk.
    eapply (dorec_call_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m b i pw); [> try (fside CV) .. | idtac].
    rewrite <- (Z_to_bv_bv_unsigned pw), PW. unfold cbrec_entry.
    (* [comment removed for export] *)
    eapply (CBPRIM _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m
              (bv_unsigned sp + 8) mh sb ri c idx d mu n b1 lo old); rewrite <- ?HSZ, <- ?HP, <- ?HR8; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?HSZ, <- ?HP, <- ?HR8, ?SHE, ?RQ; first [kcell | fside CV | exact MAG]).
    intros ra1 t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m1 CF1 MAG1 HDR1 SHP1 MU1 WM1 MI1 ST1.
    unfold cbrec_frame in CF1. rewrite ?unsigned_lit in CF1, MU1, ST1 by lia. rewrite ?SHE, ?RQ in SHP1, MU1.
    kp MAG1. kp SHP1. clear MAG HDR SHC. kpost MU1 WM1.
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (thr + 2840, thr + 2856); (C + 80 * c, C + 80 * c + 80); (C + 2576, C + 2584); (ri + 128 * c, ri + 128 * c + 8); (ri + 128 * c + 16, ri + 128 * c + 24);
               (ri + 128 * c + 80, ri + 128 * c + 88); (sb + c * 4294967296 + 3758096384 + 4 * nf, sb + c * 4294967296 + 3758096384 + 4 * nf + 4 * Z.shiftr maxc 1)] m1) as MUB.
    pose proof (wmono_refl rsegs m1) as WMB.
    unfold cbrec_tail.
    (* [comment removed for export] *)
    assert (TC1 : thread_cells m1 tp tsd ctx thr) by tcells TPL.
    eapply (cbrec_tailp_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1
              (bv_unsigned sp) lo (bv_unsigned sp + 8) C mh p sb c (idx * size) n CHUNK_INVALID b1 tsd ctx thr rf rfd);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | right; lia | unfold CHUNK_INVALID; lia | zmod | exact (proj1 HDR1) | unfold apart in SEP_tm; lia]).
    intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m2 TRF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in MU2, ST2 by lia.
    clear TRF CF1 TC1. kpost MU2 WM2.
    unfold lcdealloc_entry. rewrite (Z_to_bv_bv_unsigned sp).
    replace p with (sb + c * 4294967296 + 16 * k) at 1 by lia.
    (* [comment removed for export] *)
    assert (SEP_Cs : apart C 3888 sb (2^37)) by (revert SEP_ts; unfold apart; clear; intros; lia).
    assert (SEP_Cr : apart C 3888 ri 4096) by (revert SEP_tr; unfold apart; clear; intros; lia).
    eapply evt_cut; [eapply (cpush_drain_fast _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2
                               lo C c sb ri k maxc nf mfa ks junk statv nfs v88)|]; rewrite <- ?HSZ; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?HSZ; unfold free_array_of; first [kcell | fside CV | zmod | assumption]).
    intros ms' PO. unfold cpush_drain_fast_post, cpush_drain_W, free_array_of in PO. cbv zeta in PO. destruct_exs PO.
    (first [ dand12 PO as E3 MUc WMc MI3 ST3 LINE3 STA3 MX3 NFC3 MFA3 NFS3 DST3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & LINE3 & STA3 & MX3 & NFC3 & MFA3 & NFS3 & DST3) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST3 by lia. rewrite <- ?HSZ in MUc, LINE3.
    clear LINE STA MX NFC MFA NFS DST. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Cthr2); kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 dorec_retpc)) with (Z_to_bv 64 dorec_retpc) by (symmetry; apply ret_pc_even; [unfold dorec_retpc; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    unfold keep in MAG1, SHP1.
    eapply bytes_at_transport in SHP1; [| exact MUB | rewrite repeat_length; cbn [disjoint_from]; lia].
    assert (MAG3 : d = 0 \/ rw_cells rsegs m3 p [C8 (wz 0)]).
    { destruct MAG1 as [EE|CC]; [left; exact EE| right]. xfer CC MUB WMB. exact CC. }
    clear MAG1 MUB WMB.
    (* [comment removed for export] *)
    unfold dorec_retpc.
    eapply (dorec_ret_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 b i cnt); [kung; lia | kung; lia | kung; lia | kung; lia | |].
    - intros LT. eapply (KM LT); first [kcell | exact MAG3 | rewrite ?SHE, ?RQ; first [kcell | exact MU | eassumption] | rewrite ?HSZ; kcell | eassumption].
    - intros EQ. eapply (KD EQ); first [kcell | exact MAG3 | rewrite ?SHE, ?RQ; first [kcell | exact MU | eassumption] | rewrite ?HSZ; kcell | eassumption].
  Qed.
  (* [comment removed for export] *)
  #[using="TR CNTB BAL BHI BLO MI ri sb thr Clg"] Lemma batch_pop : forall (Q : machine_state -> Prop)
      (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9' : word) (tn tl ts nx bsize : Z),
    1 <= tn < 2^64 -> 0 <= nx < 2^64 -> 0 <= tl < 2^64 -> 0 <= bsize -> bsize <= ts < 2^64 -> T + 32 <= 2^47 -> T mod 8 = 0 ->
    rw_cells rsegs m T [C8 (wz tn); C8 (wz b); C8 (wz tl); C8 (wz ts)] ->
    rw_cells rsegs m b [C8 (wz nx); C8 (wz bsize); C8 (wz cnt)] ->
    (cnt <> 0 -> forall (m' : word -> option byte),
        rw_cells rsegs m' T [C8 (wz (tn - 1)); C8 (wz nx); C8 (wz (if nx =? 0 then 0 else tl)); C8 (wz (ts - bsize))] ->
        rw_cells rsegs m' b [C8 (wz nx); C8 (wz bsize); C8 (wz cnt)] ->
        munch [(T, T + 32)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 ra' (wz bsize) (wz (ts - bsize)) a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' 0)
                        F (wz dorec_callblk) fc None m' (seg_rom rsegs))) ->
    (cnt = 0 -> forall (m' : word -> option byte),
        rw_cells rsegs m' T [C8 (wz (tn - 1)); C8 (wz nx); C8 (wz (if nx =? 0 then 0 else tl)); C8 (wz (ts - bsize))] ->
        rw_cells rsegs m' b [C8 (wz nx); C8 (wz bsize); C8 (wz cnt)] ->
        munch [(T, T + 32)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' (wz T) (wz 0xb1d58) (wz bsize) (wz (ts - bsize)) a2' a3' a4' a5' a6' a7'
                            (wz LMA_L) (wz LMA_STAT) (wz b) (wz (2^37)) (wz 0) s7' s8' s9' s10 s11 t3' t4' t5' t6')
                        F (wz dorec_batchblk) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (head_regs sp gp tp T s10 s11 ra' tn a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s6' s7' s8' s9') F (wz dorec_head) fc None m (seg_rom rsegs)).
  Proof.
    intros until bsize. intros TNR NXR TLR BS0 BSR THI TAL TCL BCL K1 K0.
    pose proof alloc_ceiling_val as CV. free_lin.
    unfold head_regs, it_regs, kHighMemBeg in *.
    eapply (dorec_pop_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m T tn b tl ts nx bsize cnt
              (fun _ => True) (fun _ => True)); [> try first [eassumption | kung; lia] .. | | | intros; exact I | intros; exact I].
    - intros m' CZ TC' BC' MU' WM' MI' _. apply (K0 CZ m' TC' BC' MU' WM' MI').
    - intros m' CZ TC' BC' MU' WM' MI' _. replace (b + 152) with (b + 152 + 8 * 0) by lia. change (Z_to_bv 64 16) with (Z_to_bv 64 (16 + 0)).
      apply (K1 CZ m' TC' BC' MU' WM' MI').
  Qed.
  (* [comment removed for export] *)
  #[using="BFORM TU TR DF CSB SEP_tc RILO SBAL SBHI SBLO BLO THRA TSDL TC SPA SPH CEIL ST MI ri sb ctx tsd Clg"] Lemma batch_free_push : forall (Q : machine_state -> Prop)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' statv : word)
      (tn tf tl ts cntc maxc : Z) (ks : list word),
    let E := C + 80 * 24 in
    lo <= bv_unsigned sp - 48 -> 0 <= tn < 2^64 -> T + 32 <= 2^47 -> T mod 8 = 0 -> 0 <= kb < 2^28 ->
    0 <= cntc < maxc -> maxc <= 16 -> length ks = 16%nat -> bv_unsigned ra0 mod 2 = 0 ->
    rw_cells rsegs m T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
    rw_cells rsegs m E [C4 (wz cntc); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    (tn <> 0 -> forall (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
        rw_cells rsegs m' E [C4 (wz (cntc + 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat cntc) (wz kb)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        munch [(bv_unsigned sp - 48, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (head_regs sp gp tp T s10 s11 (wz dorec_nextpc) tn a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (wz b) s6' s7' s8' s9')
                        F (wz dorec_head) fc None m' (seg_rom rsegs))) ->
    (tn = 0 -> forall (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
        rw_cells rsegs m' E [C4 (wz (cntc + 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat cntc) (wz kb)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        munch [(bv_unsigned sp - 48, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + 112) ->
        evt rsegs Q (MS (mkR ra0 (wz (bv_unsigned sp + 112)) gp tp t0'' t1'' t2'' s0v s1v (wz 0) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' (wz T) (wz 0xb1d58) a0' a1' a2' a3' a4' a5' a6' a7'
                        (wz LMA_L) (wz LMA_STAT) (wz b) (wz (2^37)) s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                    F (wz dorec_batchblk) fc None m (seg_rom rsegs)).
  Proof.
    intros until ks. cbv zeta. intros LOLE TNR THI TAL KB CNTC MXC LKS RA0 TCL LINE STA KM K0.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold head_regs, kHighMemBeg, LMA_L, LMA_STAT in *.
    pose proof (cbc_rw m DF) as CBC.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (C + 80 * 24, C + 80 * 24 + 80); (C + 2576, C + 2584)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 b) with (Z_to_bv 64 (sb + 24 * 2^32 + 16 * kb)) by (rewrite BFORM; reflexivity).
    eapply (dorec_batch_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m sb kb (wz C));
      [> try (fside CV) .. | idtac].
    all: try (first [kcell | zmod | unfold apart in SEP_ts; lia]).
    unfold lcdealloc_entry.
    eapply evt_cut; [eapply (lcdealloc_push_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
                               lo C 24 sb kb cntc maxc ks statv)|]; rewrite <- ?BFORM; change (class_size 24) with 8192; [> try (fside CV) .. | idtac].
    all: try (first [kcell | zmod | rewrite BFORM; f_equal; lia | unfold apart in SEP_ts; lia]).
    intros ms' PO. destruct_exs PO. (first [ dand7 PO as E3 MUc WMc MI3 ST3 LINE3 STA3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & LINE3 & STA3) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST3 by lia.
    clear LINE STA. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CRI); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Ctsd); kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 dorec_nextpc)) with (Z_to_bv 64 dorec_nextpc) by (symmetry; apply ret_pc_even; [unfold dorec_nextpc; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    assert (SPE : wz (bv_unsigned sp + 112 + -112) = sp) by (replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia; apply Z_to_bv_bv_unsigned).
    rewrite <- SPE at 1.
    eapply (dorec_next_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 (bv_unsigned sp + 112) lo T tn tf tl ts scr
              (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0); [> try (fside CV) .. | idtac].
    all: try (first [replace (bv_unsigned sp + 112 - 112) with (bv_unsigned sp) by lia; first [kcell | eassumption]
                    | replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia; first [kcell | eassumption] | right; lia | zmod]).
    - intros TNZ. replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      eapply (KM TNZ); first [kcell | exact MU | eassumption].
    - intros TZ ST4. eapply (K0 TZ); first [kcell | exact MU | eassumption].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="KBR BFORM kb SEP_sr RIHI RILO SBLO CNTB BHI BLO SPH CEIL ST ri sb m Clg"] Lemma iter_sec_post : forall (Q : machine_state -> Prop) (m8 : word -> option byte)
      (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pw : word) (uscr : list byte) (h msz : Z),
    lo <= bv_unsigned sp - 48 -> 0 <= i < cnt ->
    mem_inv rsegs m8 -> stk rsegs m8 lo (bv_unsigned sp + -48) ->
    ro_cells rsegs m8 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m8 (CF + 144) [C8 (wz 0)] ->
    rw_cells rsegs m8 (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m8 (b + 24 + 8 * i) [C8 pw] ->
    rw_cells rsegs m8 (bv_unsigned sp + -48) (unmap_frame uscr (wz LMA_L) (wz 0xb1d58) (wz T) (wz dorec_retpc)) ->
    (i + 1 < cnt -> forall (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        munch [(bv_unsigned sp - 48, bv_unsigned sp)] m8 m' -> wmono rsegs m8 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (i + 1))
                        F (wz dorec_callblk) fc None m' (seg_rom rsegs))) ->
    (i + 1 = cnt -> forall (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        munch [(bv_unsigned sp - 48, bv_unsigned sp)] m8 m' -> wmono rsegs m8 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (i + 1))
                        F (wz dorec_batchblk) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz unmap_resume) (wz (bv_unsigned sp + -48)) gp tp t0' t1' t2' (wz msz) (wz 0)
                        (wz 0) a1' a2' a3' a4' a5' a6' a7'
                        (wz h) (wz LMA_STAT) (wz b) (wz (2^37)) (wz cnt) (wz (b + 152 + 8 * i)) (wz (cnt + 16)) (wz (16 + i)) s10 s11 t3' t4' t5' t6')
                    F (wz munmap_after_pc) fc None m8 (seg_rom rsegs)).
  Proof.
    intros until msz. intros LOLE IR MI8 ST8 CGCF8 CMLM8 DF8 ENT8 UF KM KD.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    clear MI ST TC PCo CSB CRI DF.
    unfold it_regs, kHighMemBeg, CF in *.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m8) as MU. pose proof (wmono_refl rsegs m8) as WM.
    (* [comment removed for export] *)
    eapply evt_cut; [| intros ms' HQ'; exact HQ'].
    eapply (unmap_post_ok gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m8 (bv_unsigned sp) lo uscr);
      [> try (fside CV) .. | idtac].
    all: try (first [kcell | unfold CF; kcell | unfold dorec_retpc; lia]).
    intros t0g t1g t2g a0g a1g a2g a3g a4g a5g a6g a7g t3g t4g t5g t6g m9 MU9 WM9 MI9 ST9.
    rewrite ?unsigned_lit in MU9, ST9 by lia. clear UF. kpost MU9 WM9.
    replace (ret_pc (Z_to_bv 64 dorec_retpc)) with (Z_to_bv 64 dorec_retpc) by (symmetry; apply ret_pc_even; [unfold dorec_retpc; lia|reflexivity]).
    rewrite (Z_to_bv_bv_unsigned sp). unfold dorec_retpc, LMA_L, LMA_STAT in *.
    (* [comment removed for export] *)
    eapply (dorec_ret_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m9 b i cnt); [kung; lia | kung; lia | kung; lia | kung; lia | |].
    - intros LT. eapply (KM LT); first [kcell | exact MU | eassumption].
    - intros EQ. eapply (KD EQ); first [kcell | exact MU | eassumption].
  Qed.
End DoRec.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
