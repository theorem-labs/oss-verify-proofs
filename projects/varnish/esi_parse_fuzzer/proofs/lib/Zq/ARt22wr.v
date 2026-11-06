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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARt_fpo ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.

Module ARt2mo1.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).
(* [comment removed for export] *)
Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- mapped _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- tls_consts _ => unfold tls_consts
  | |- tls_dyn _ _ _ => unfold tls_dyn
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Ltac qdrain_lock LCK q hi rl :=
  (* [comment removed for export] *)
  apply (hdr4_join _ _ 0 rl hi) in LCK; [| lia | lia | lia | cbn; tauto]; replace (0 + 256 * rl + 65536 * hi) with (256 * rl + 65536 * hi) in LCK by lia.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem qdrain0_ok : qdrain0_stmt.
Proof.
  unfold qdrain0_stmt. intros until lo.
  intros MI ST LOLE CEIL A0 A1 A2 A3 Q0 Q1 QAL CLO CHI RLR HIR GQ0 QB0 NR QMR NB NBR FBR LBR LCK QMX GL CC RA.
  pose proof alloc_ceiling_val as CV.
  unfold qdrain_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1 a2 a3.
  set (qq := q / 8) in *. assert (QQ : q = 8 * qq) by (subst qq; rewrite (Z_div_mod_eq_full q 8) at 1; rewrite QAL; lia). clearbody qq.
  assert (QM4 : (q + 152) mod 4 = 0) by (rewrite QQ; replace (8 * qq + 152) with ((2 * qq + 38) * 4) by lia; apply Z_mod_mult).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192); (c, c + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. carve_frame 48%nat ST.
  do 6 amz. (* [comment removed for export] *)
  amz. amz. amz. rewrite (land_m4 (q + 152)) by first [exact QM4 | plia]. amz. (* [comment removed for export] *)
  qdrain_lock LCK q hi rl.
  amz. (* [comment removed for export] *) rewrite sx32_small by lia.
  amz. amz. amz. amz. replace (256 * rl + 65536 * hi) with (256 * (rl + 256 * hi)) by lia. rewrite (cas_set_low0 1 (rl + 256 * hi)) by lia.
  replace (256 * (rl + 256 * hi)) with (256 * rl + 65536 * hi) by lia. replace (1 + 256 * (rl + 256 * hi)) with (1 + 256 * rl + 65536 * hi) by lia.
  scstep; zsimp. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  amz. replace (Z.land (256 * rl + 65536 * hi) 255) with 0 by (replace (256 * rl + 65536 * hi) with (256 * (rl + 256 * hi)) by lia; rewrite land255_low0 by lia; reflexivity).
  amz. if_false. (* [comment removed for export] *)
  replace (1 + (256 * rl + 65536 * hi)) with (1 + 256 * rl + 65536 * hi) in LCK by lia.
  apply (hdr4_split _ _ 1 rl hi) in LCK; [| lia | lia | lia | cbn; tauto].
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. amz. br_taken. (* [comment removed for export] *)
  do 7 amz.
  release_frame FR ST (bv_unsigned sp).
  (subst hotQ; finish).
Qed.

Theorem qdrainA_ok : qdrainA_stmt.
Proof.
  unfold qdrainA_stmt. intros until glnx.
  intros MI ST LOLE CEIL A0 A1 A2 A3 Q0 Q1 QAL CLO CHI GLO GHI DJ RLR HIR GQ0 QB0 NR QMR NB NBR GN GNR FBR LBR LCK QMX GL CC GLN RA.
  pose proof alloc_ceiling_val as CV.
  unfold qdrain_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1 a2 a3.
  set (qq := q / 8) in *. assert (QQ : q = 8 * qq) by (subst qq; rewrite (Z_div_mod_eq_full q 8) at 1; rewrite QAL; lia). clearbody qq.
  assert (QM4 : (q + 152) mod 4 = 0) by (rewrite QQ; replace (8 * qq + 152) with ((2 * qq + 38) * 4) by lia; apply Z_mod_mult).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192); (c, c + 32); (gl, gl + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. carve_frame 48%nat ST.
  do 6 amz. (* [comment removed for export] *)
  amz. amz. amz. rewrite (land_m4 (q + 152)) by first [exact QM4 | plia]. amz.
  qdrain_lock LCK q hi rl.
  amz. rewrite sx32_small by lia.
  amz. amz. amz. amz. replace (256 * rl + 65536 * hi) with (256 * (rl + 256 * hi)) by lia. rewrite (cas_set_low0 1 (rl + 256 * hi)) by lia.
  replace (256 * (rl + 256 * hi)) with (256 * rl + 65536 * hi) by lia. replace (1 + 256 * (rl + 256 * hi)) with (1 + 256 * rl + 65536 * hi) by lia.
  scstep; zsimp.
  amz. if_false.
  amz. replace (Z.land (256 * rl + 65536 * hi) 255) with 0 by (replace (256 * rl + 65536 * hi) with (256 * (rl + 256 * hi)) by lia; rewrite land255_low0 by lia; reflexivity).
  amz. if_false.
  replace (1 + (256 * rl + 65536 * hi)) with (1 + 256 * rl + 65536 * hi) in LCK by lia.
  apply (hdr4_split _ _ 1 rl hi) in LCK; [| lia | lia | lia | cbn; tauto].
  amz. amz. br_not_taken.
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz.
  amz. amz.
  amz. amz. amz. br_taken.
  do 7 amz.
  release_frame FR ST (bv_unsigned sp).
  (subst hotQ; finish).
Qed.

End CEIL.
End ARt2mo1.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).
(* [comment removed for export] *)
Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- mapped _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- tls_consts _ => unfold tls_consts
  | |- tls_dyn _ _ _ => unfold tls_dyn
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem enqueue_newfull_ok : enqueue_newfull_stmt.
Proof.
  unfold enqueue_newfull_stmt. intros until bj3. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 A2 A3 A4 CLO CHI PLO PHI PAL LLO LHI DJ0 DJ4 DJ5 SB0 SB1 BLO BHI DJ1 DJ2 DJ3 NB NBR CNT LKS KW KWR SZ MCH SBC CC LB PC STA BC RA.
  pose proof alloc_ceiling_val as CV.
  unfold enqueue_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1 a2 a3 a4.
  remember (sb + 24 * 2 ^ 32 + 16 * bv_unsigned kw) as b eqn:BE.
  pose proof (zr_word kw) as KW0; unfold inr64 in KW0.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (c, c + 32); (lb, lb + 8); (C + 1920, C + 1924); (C + 2576, C + 2584); (b, b + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. carve_frame 64%nat ST.
  do 8 amz. (* [comment removed for export] *)
  amz. amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. if_false. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite sx32_small by lia.
  amz. br_not_taken. (* [comment removed for export] *)
  do 7 amz.
  rewrite slli32_srli30 by lia.
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read rsegs mm (C + 1920 + 16) ks (cnt - 1) kw (wa (C + 1920 + 16 + 4 * (cnt - 1))) (pc_chunks_u32arr mm (C + 1920) _ _ _ ks PC LKS) KW ltac:(lia) eq_refl) as HR end.
  amz. (* [comment removed for export] *) rewrite (zx32_word kw KWR). clear HR.
  set (cq := C / 16) in *. assert (CQ : C = 16 * cq) by (subst cq; rewrite (Z_div_mod_eq_full C 16) at 1; rewrite PAL; lia). clearbody cq.
  assert (AL8 : (C + 2576) mod 8 = 0) by (rewrite CQ; replace (16 * cq + 2576) with ((2 * cq + 322) * 8) by lia; apply Z_mod_mult).
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  do 5 amz.
  replace (Z.shiftl (bv_unsigned kw) 4 + (sb + 103079215104)) with b by (rewrite !Z.shiftl_mul_pow2 by lia; lia).
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  do 9 amz.
  release_frame FR ST (bv_unsigned sp).
  replace (cnt + -1) with (cnt - 1) in PC by lia.
  (subst hotQ; finish).
  all: lazymatch goal with |- rw_cells _ ?mm ?a [C8 _] => lazymatch goal with H : rw_cells _ mm a _ |- _ => exact H end | _ => idtac end.
Qed.

End CEIL.
