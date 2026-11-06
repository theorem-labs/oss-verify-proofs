(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r.

Module V_vetlt.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_error_ok : vep_error_stmt.
Proof.
  unfold vep_error_stmt.
  intros VEP v tag q H lo. intros until m.
  intros A0 VEPC TAG PADS EVC HENV HG IMG VLO V8 VHI ST LO CEIL SPH MI.
  rewrite A0. unfold vep_error_entry. unfold VEPERR_STACK in *.
  pose proof alloc_ceiling_val as ACV.
  (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
  (* [comment removed for export] *)
  assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
  assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
  assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
  assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
  (* [comment removed for export] *)
  destruct HENV as [GLOB HOBJ].
  (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as EBSS BSS CP [cnt CNT] | pose proof GLOB as (EBSS & BSS & CP & [cnt CNT]) ]). rewrite EBSS in BSS. cbn [vi_bss VI0 al_segs LayoutP0] in BSS.
  cbn [al_segs LayoutP0] in CP, CNT.
  (first [ pose proof (HOBJ) as dR_3; dand3 dR_3 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
  cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
  (first [ dand4 IMG as _ _ GVSC _ | destruct IMG as (_ & _ & GVSC & _) ]). unfold GOT_vsc in GVSC.
  pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size v tag q TAG PADS) in VEPB.
  (first [ pose proof (PADS) as dR_7; dand7 dR_7 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
  unfold vep_cells in VEPC. rewrite EVC in VEPC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  destruct (rw_cells_forget _ _ _ _ CNT) as [cnt' CNT']. cbn [cells_size csize Nat.add] in CNT'. clear CNT.
  apply evt_done. unfold vep_error_post.
  do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|exact ST].
  split.
  - eapply (glob_ok_intro LayoutP0); [exact EBSS| rewrite EBSS; cbn [vi_bss VI0 al_segs LayoutP0]; exact BSS | exact CP | exact CNT'].
  - eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM|].
    intros a Ha. unfold h_req, h_resp, h_hd in Ha. cbn [outside]. lia.
Qed.

End CEIL.
End V_vetlt.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strchr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr.R_memcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.

Module V_VS46q.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck R_vsqhq.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_vsn6b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pc429 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb Img0 V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac akit_plia := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac akit_avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; akit_avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; akit_plia ] end | akit_plia ]
  end.
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; first [ solve [ akit_avoids_false X ] | lia ] ].
(* [comment removed for export] *)

Definition VSB_vprintf_entry := 0x19880.
Definition VSB_printf_entry := 0x199fc.
(* [comment removed for export] *)
Definition VPRINTF_STACK := 64 + EXT_STACK.
Definition PRINTF_STACK := 64 + VPRINTF_STACK.

(* [comment removed for export] *)
Lemma freespace_wrap : forall s l, 0 <= l < s -> s < 2^64 ->
  (s + (18446744073709551615 - l)) mod 18446744073709551616 = s - l - 1.
Proof.
  intros s l H1 H2. replace (s + (18446744073709551615 - l)) with ((s - l - 1) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof. intros. apply zb_lxor_ones. lia. Qed.

(* [comment removed for export] *)
Lemma fr_recast8 : forall segs m a j (w : word) rest,
  rw_cells segs m a (CB 8 j :: C8 w :: rest) -> rw_cells segs m a (CB 8 j :: CB 8 (le8 w) :: rest).
Proof.
  intros. eapply CellsX.rw_cells_recast; [exact H| |reflexivity].
  destruct H as [[W _] _]. cbn in W |- *. tauto.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  Definition str_home (A : AS) (S : Z) (v : vsb_rec) (HS : Z) (hs : list byte) : Prop :=
    (IMG_LO <= HS /\ HS + Z.of_nat (length hs) <= RO_TOP)
    \/ exists q k, a_live A q = Some k /\ q <= HS /\ HS + Z.of_nat (length hs) <= q + k /\ q <> S /\ q <> vb_buf v /\ hs <> [].

  (* [comment removed for export] *)
  Lemma blk_avoids_crange : forall (A A' : AS) (m0 m' : mem) (xsp win : Z) (V : Z -> Prop) (nb nsz a n : Z),
    cframe LayoutP0 (owned A) (owned A') xsp win V (blk nb nsz) m0 m' ->
    crange A m0 a n -> 0 < n -> a + n <= xsp - win -> nb <> 0 -> 0 < nsz ->
    (forall x, a <= x < a + n -> ~ V x) ->
    ~ (nb < a + n /\ a < nb + nsz).
  Proof.
    (intros A A' m0 m' xsp win V nb nsz a n; (first [ intro dR_20; dand3 dR_20 as C1 C2 C3 | intros (C1 & C2 & C3) ]); (first [ intro dR_21; dand3 dR_21 as Ha Hn CR | intros (Ha & Hn & CR) ]); intros N0 BW NB NS NV [X Y]).
    set (x := Z.max a nb).
    (first [ pose proof ((CR (x - a) ltac:(lia))) as dR_1; dand3 dR_1 as NO NE VIS | destruct (CR (x - a) ltac:(lia)) as (NO & NE & VIS) ]). replace (a + (x - a)) with x in NO, NE, VIS by lia.
    destruct (C3 x ltac:(lia) ltac:(lia) NE ltac:(unfold blk; lia)) as [O | [HV | [MN NI]]].
    - exact (NO O).
    - exact (NV x ltac:(lia) HV).
    - destruct VIS as [VIS|VIS]; [exact (VIS MN)| exact (NI VIS)].
  Qed.

  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.

  (* [comment removed for export] *)
  Definition vp_iter_post (sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (S Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word) (lo : Z)
      (v1 : vsb_rec) (W : list ivl) (mb : mem) (fr_s3 fr_s2 fr_s1 fr_s0 fr_ra : word) : machine_state -> Prop :=
    fun ms => exists (rax t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j8 : list byte) (bs1 : list byte) (m1 : mem),
      ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1
                   (Z_to_bv 64 (vb_size v1)) (Z_to_bv 64 (vb_len v1)) (Z_to_bv 64 (vb_size v1 - vb_len v1 - 1)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 (Z.of_nat (length (OUT slots hs)))) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (Z_to_bv 64 0x19908) (Z_to_bv 32 0) None m1 (seg_rom rsegs)
      /\ munch W mb m1 /\ wmono rsegs mb m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -64) [CB 8 j8; C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 fr_s3; C8 fr_s2; C8 fr_s1; C8 fr_s0; C8 fr_ra]
      /\ rw_cells rsegs m1 S (vsb_cells v1)
      /\ u8arr rsegs m1 (vb_buf v1) bs1 /\ Z.of_nat (length bs1) = vb_size v1
      /\ ro_cells rsegs m1 Afmt FMT /\ ssp_cells m1 canary /\ va_area m1 VA slots /\ bytes_at rsegs m1 HS hs
      /\ (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.

  #[using="P2 P1 HOUT HLA nargs"] Lemma vp_iter : forall (rax gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (sp : word)
      (S Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word) (lo : Z)
      (v1 : vsb_rec) (W : list ivl) (mb m0 : mem) (fr_s3 fr_s2 fr_s1 fr_s0 fr_ra : word) (j8 j8' bs0 : list byte),
    s0 = Z_to_bv 64 S -> s1 = Z_to_bv 64 Afmt ->
    munch W mb m0 -> wmono rsegs mb m0 -> mem_inv rsegs m0 ->
    W = [(bv_unsigned sp - VPRINTF_STACK, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] ->
    stk rsegs m0 lo (bv_unsigned sp + -64) ->
    rw_cells rsegs m0 (bv_unsigned sp + -64) [CB 8 j8; CB 8 j8'; C8 (Z_to_bv 64 VA); C8 fr_s3; C8 fr_s2; C8 fr_s1; C8 fr_s0; C8 fr_ra] ->
    rw_cells rsegs m0 S (vsb_cells v1) -> vsb_inv v1 false ->
    u8arr rsegs m0 (vb_buf v1) bs0 -> Z.of_nat (length bs0) = vb_size v1 ->
    ro_cells rsegs m0 Afmt FMT -> IMG_LO <= Afmt -> Afmt + la <= RO_TOP ->
    ssp_cells m0 canary -> va_area m0 VA slots -> bv_unsigned sp <= VA -> VA + 8 * Z.of_nat (length slots) <= 2^47 ->
    PRE slots HS hs -> bytes_at rsegs m0 HS hs ->
    ~ (vb_buf v1 + vb_len v1 < HS + Z.of_nat (length hs) /\ HS < vb_buf v1 + vb_size v1) -> HS + Z.of_nat (length hs) <= lo ->
    off_image LayoutP0 (vb_buf v1) (vb_size v1) -> vb_buf v1 + vb_size v1 <= alloc_ceiling ->
    (S + 40 <= vb_buf v1 \/ vb_buf v1 + vb_size v1 <= S) -> 4096 <= S -> S + 40 <= alloc_ceiling ->
    alloc_ceiling <= lo -> lo + VPRINTF_STACK <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^47 ->
    evt rsegs (vp_iter_post sp gp tp s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 S Afmt VA slots HS hs canary lo v1 W mb fr_s3 fr_s2 fr_s1 fr_s0 fr_ra)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 0x198cc) (Z_to_bv 32 0) None m0 (seg_rom rsegs)).
  Proof.
    intros until bs0. intros -> -> MU WM MI EW ST FR VSBC VINV U8 LBS HF ARL ART SSP VAA VLO VHI HPRE HSB HSD HSL Bimg Bhi DSB Slo Shi CEIL LO SPHI.
    destruct SSP as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2. unfold va_area in VAA.
    pose proof alloc_ceiling_val as CV.
    unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK, RO_TOP, IMG_LO in *. subst W.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    unfold vsb_cells in VSBC.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (bytes_at_bound _ _ _ _ VAA) as VAB. rewrite u64s_length in VAB.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. rewrite <- HLA in ART.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr _ _ _ _ U8) as BUFC.
    apply (rw_cells_split_CB rsegs _ _ [] _ _ [] [Z.to_nat (vb_len v1); Z.to_nat (vb_size v1 - vb_len v1)]%nat) in BUFC; [|cbn; lia].
    cbn [mk_CB_cells app] in BUFC.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in BUFC. destruct BUFC as [PREF DST].
    cbn [cells_size csize] in DST.
    replace (vb_buf v1 + Z.of_nat (Z.to_nat (vb_len v1) + 0)) with (vb_buf v1 + vb_len v1) in DST by lia. clear U8.
    pose proof Bimg as BimgN. unfold off_image in BimgN. cbn [al_image_lo al_image_hi LayoutP0] in BimgN.
    replace (Z_to_bv 64 (vb_size v1 - vb_len v1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (vb_size v1 - vb_len v1)))) by (f_equal; lia).
    call_lit (vsnprintf_gen_spec FMT la nargs PRE OUT HLA HOUT P1 P2) by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- ro_cells _ _ _ _ => exact HF
      | |- ssp_cells _ _ => split; eassumption
      | |- rw_cells _ _ _ [CB _ _] => exact DST
      | |- va_area _ _ _ => exact VAA
      | |- bytes_at _ _ _ _ => exact HSB
      | |- PRE _ _ _ => exact HPRE
      | |- mem_inv _ _ => assumption
      | |- dst_ok _ _ => unfold dst_ok, IMG_LO, IMG_HI; lia
      | |- @eq _ _ _ => first [ reflexivity | f_equal; lia ]
      | |- (_ <= _)%nat => lia
      | |- _ => rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, RO_TOP, IMG_LO in *; lia
      end || match goal with |- ?G => idtac "VSNSIDE-FAIL:" G end).
    clear PC1 PC2 PC3. rename PC into ST. rename PC0 into DST. clear BimgN.
    (* [comment removed for export] *)
    pose proof (rw_CB_length _ _ _ _ _ DST) as LD.
    lazymatch type of PREF with rw_cells _ ?mq _ [CB ?n1 ?l1] => lazymatch type of DST with rw_cells _ _ _ [CB ?n2 ?l2] =>
      assert (BUFC : rw_cells rsegs mq (vb_buf v1) [CB n1 l1; CB n2 l2])
        by (apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact PREF|]; cbn [cells_size csize];
            eapply rwc_eq; [exact DST|lia]);
      pose proof (CellsX.rw_cells_recast rsegs _ _ _ [CB (n1 + n2)%nat (l1 ++ l2)] BUFC
                    ltac:(cbn; rewrite length_app, (rw_CB_length _ _ _ _ _ PREF), LD; split; [reflexivity|exact I])
                    ltac:(cbn [cells_bytes cbytes]; rewrite <- app_assoc, app_nil_r; reflexivity)) as BUF1;
      clear BUFC PREF DST; apply u8arr_of_rw_cells in BUF1 end end.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K. { exfalso. unsign K. klia K. } clear K.
    zstep. zstep. zstep. zstep. zstep.
    rewrite (lxor_ones64 (vb_len v1)) by lia.
    rewrite <- (Z_to_bv_mod64 (vb_size v1 + (18446744073709551615 - vb_len v1))). rewrite freespace_wrap by lia.
    apply evt_done. unfold vp_iter_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact FR|]. split; [exact VSBC|]. split; [exact BUF1|].
    split. { rewrite length_app, firstn_length, LD. lia. }
    split; [exact HF|]. split; [split; assumption|]. split; [exact VAA|]. split; [exact HSB|]. exact POST.
  Qed.

  (* [comment removed for export] *)
  Section VP.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (S : Z) (v : vsb_rec)
            (Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (canary : word) (lo : Z) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 S.
  Hypothesis A1 : a1 = Z_to_bv 64 Afmt.
  Hypothesis A2 : a2 = Z_to_bv 64 VA.
  Hypothesis VOBJ : vsb_obj LayoutP0 A m S v false.
  (* [comment removed for export] *)
  Hypothesis HF : ro_cells rsegs m Afmt FMT.
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  (* [comment removed for export] *)
  Hypothesis VAA : va_area m VA slots.
  Hypothesis VLO : bv_unsigned sp <= VA.
  Hypothesis VHI : VA + 8 * Z.of_nat (length slots) <= 2^47.
  (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSB : bytes_at rsegs m HS hs.
  Hypothesis HSH : str_home A S v HS hs.
  (* [comment removed for export] *)
  Hypothesis SSP : ssp_cells m canary.
  Hypothesis EM : vb_size v + Z.of_nat (length (OUT slots hs)) <= EXT_MAX.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vsb_extendsize (vb_size v + Z.of_nat (length (OUT slots hs))) <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VPRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (v' : vsb_rec),
      ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
      vsb_obj LayoutP0 A' m' S v' false ->
      (vb_error v <> 0 -> r = -1 /\ v' = v) ->
      (vb_error v = 0 -> r = 0 /\ vb_error v' = 0 /\
         (  vb_len v' = vb_len v + Z.of_nat (length (OUT slots hs))
         \/ (vb_len v' = vb_size v - 1 /\ vb_size v' = vb_size v /\ vb_buf v' = vb_buf v))) ->
      vb_len v <= vb_len v' <= vb_len v + Z.of_nat (length (OUT slots hs)) ->
      vb_size v <= vb_size v' <= Z.max (vb_size v) (vb_len v' + 4096) ->   (* [comment removed for export] *)
      (forall q, q <> vb_buf v -> q <> vb_buf v' -> a_live A' q = a_live A q) ->
      (vb_buf v' = vb_buf v \/ (a_live A (vb_buf v') = None /\ a_live A' (vb_buf v) = None)) ->
      a_livebytes A' = a_livebytes A + vb_size v' - vb_size v -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
      stk rsegs m' lo (bv_unsigned sp) ->
      ssp_cells m' canary -> va_area m' VA slots -> bytes_at rsegs m' HS hs ->
      cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) VPRINTF_STACK
               (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40))
               (blk (vb_buf v') (vb_size v')) m m' ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  #[using="K LO CEIL VLO FMT"] Lemma vp_tail8 : forall (xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 : word)
      (A' : AS) (md' : Model) (mb mt : mem) (v1 : vsb_rec) (bs1 j8 : list byte) (mn Lz : Z),
    m_halted md' = None -> m_vm_lazy md' = [] ->
    ainv A' mb md' ->
    munch [(bv_unsigned sp - VPRINTF_STACK, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] mb mt ->
    wmono rsegs mb mt ->
    client_fp LayoutP0 A' [(bv_unsigned sp - VPRINTF_STACK, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] ->
    mem_inv rsegs mt -> md_frame md md' ->
    stk rsegs mt lo (bv_unsigned sp + -64) ->
    rw_cells rsegs mt (bv_unsigned sp + -64) [CB 8 j8; C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mt S (vsb_cells v1) -> vsb_inv v1 false -> vb_error v1 = 0 -> vb_len v1 = vb_len v ->
    a_live A' S = Some 40 -> a_live A' (vb_buf v1) = Some (vb_size v1) -> S <> vb_buf v1 ->
    u8arr rsegs mt (vb_buf v1) bs1 -> Z.of_nat (length bs1) = vb_size v1 ->
    ssp_cells mt canary -> va_area mt VA slots -> bytes_at rsegs mt HS hs ->
    Lz = Z.of_nat (length (OUT slots hs)) ->
    0 <= mn -> mn <= Lz -> mn <= vb_size v1 - vb_len v1 - 1 ->
    (mn = Lz \/ (mn = vb_size v1 - vb_len v1 - 1 /\ vb_size v1 = vb_size v /\ vb_buf v1 = vb_buf v)) ->
    vb_size v <= vb_size v1 -> (vb_size v1 = vb_size v \/ vb_size v1 <= vb_len v + Lz + 4096) ->
    (forall q, q <> vb_buf v -> q <> vb_buf v1 -> a_live A' q = a_live A q) ->
    (vb_buf v1 = vb_buf v \/ (a_live A (vb_buf v1) = None /\ a_live A' (vb_buf v) = None)) ->
    a_livebytes A' = a_livebytes A + vb_size v1 - vb_size v -> a_nlive A' = a_nlive A ->
    vb_error v = 0 ->
    4096 <= S -> S + 40 <= alloc_ceiling -> (S + 40 <= 0x10000 \/ 0x63000 <= S) ->
    (S + 40 <= vb_buf v1 \/ vb_buf v1 + vb_size v1 <= S) -> ~ (S < HS + Z.of_nat (length hs) /\ HS < S + 40) ->
    (forall m'', munch [(bv_unsigned sp - VPRINTF_STACK, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] mb m'' ->
                 mapped m'' (bv_unsigned sp - VPRINTF_STACK) VPRINTF_STACK ->
                 cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) VPRINTF_STACK
                        (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40)) (blk (vb_buf v1) (vb_size v1)) m m'') ->
    evt rsegs (rz_at rsegs md' T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 Afmt)
                 (Z_to_bv 64 (vb_size v1)) (Z_to_bv 64 (vb_len v1)) (Z_to_bv 64 mn) xa3 xa4 xa5 xa6 xa7
                 xs2 (Z_to_bv 64 Lz) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            bvmap_empty (Z_to_bv 64 0x19934) (Z_to_bv 32 0) None mt (seg_rom rsegs)).
  Proof.
    intros until Lz. intros MDH' MDL' AINVb MU WM CFP MIt MDF STt FR VSBC VINV1 E1 EL VLS1 VLB1 VNE1 U81 LBS1 [SSP1 SSP2] VAA1 HSB1
           ELz MN0 MN1 MN2 MNC SZ1 SZ2 LIVEq REL LBp NLp E0 Slo Shi SimgN DSB1 HSDS CFK.
    pose proof alloc_ceiling_val as CV.
    unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK in *.
    unfold GOT_SSP, SSP_GUARD in SSP1, SSP2. unfold va_area in VAA1.
    pose proof VINV1 as VINV0. (first [ dand8 VINV1 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV1 as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    unfold vsb_cells in VSBC. rewrite E1 in VSBC.
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add length] in FB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rename STt into STq.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    2: pose proof (rw_cells_read_sub rsegs _ _ _ 32 1 VSBC ltac:(lia) ltac:(cbn; lia)) as RDF.
    2: rewrite Vfl in RDF. 2: unfold VSB_FLAGS_LIVE in RDF.
    2: match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end.
    2: zstep. 2: zstep. 2: zstep. 2: if_cases KX. 3: zify_cond KX. 3: dead KX.
    2: clear KX RDF.
    all: clear KR.
    (* [comment removed for export] *)
    all: zstep; if_cases KA; zify_cond KA; [ exfalso; unsign KA; klia KA | clear KA ].
    all: zstep; zstep; zstep; zstep; zstep; do 5 zstep; zstep; zstep.
    all: try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp).
    all: rewrite CellsX.sx32_zero, (unsigned_lit 0) by lia; change (Z.b2z (0 <? 1) + -1)%Z with 0%Z.
    all: release_frame FR STq (bv_unsigned sp).
    all: cps_done.
    all: lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
           pose proof (ainv_munch LayoutP0 A' mb mx md' _ AINVb MU WM CFP) as AINV9;
           pose proof (CFK mx MU ltac:(eapply (stk_mapped (L:=LayoutP0)); [exact STq | exact CEIL | lia | lia])) as CF9 end.
    all: eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 A' _ md' (vsb_set_len v1 (mn + vb_len v1)));
      [ exact AINV9 | assumption | exact MDF
      | (* [comment removed for export] *)
        split; [ unfold vsb_cells; cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent vsb_set_len]; rewrite E1; exact VSBC |];
        split; [ unfold vsb_inv in *; cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent vsb_set_len]; lia |];
        split; [ exact VLS1 |]; split; [ exact VLB1 |]; split; [ exact VNE1 |];
        eexists; split; [ eassumption |]; split; [ cbn [vsb_set_len vb_size]; assumption | intros X; discriminate X ]
      | intros X; exfalso; exact (X E0)
      | intros _; split; [reflexivity|]; split; [cbn [vsb_set_len vb_error]; exact E1|];
        cbn [vsb_set_len vb_len vb_size vb_buf]; lia
      | cbn [vsb_set_len vb_len]; lia
      | cbn [vsb_set_len vb_size vb_len]; lia
      | cbn [vsb_set_len vb_buf]; exact LIVEq
      | cbn [vsb_set_len vb_buf]; exact REL
      | cbn [vsb_set_len vb_size]; exact LBp
      | exact NLp
      | assumption
      | split; assumption
      | assumption
      | assumption
      | cbn [vsb_set_len vb_buf vb_size]; exact CF9 ].
  Qed.

  (* [comment removed for export] *)
  #[using="K LO CEIL HPRE VLO HOUT PRE FMT"] Lemma vp_tail0 : forall (xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 : word)
      (A' : AS) (md' : Model) (mb mt : mem) (v1 : vsb_rec) (bs1 j8 : list byte) (Lz : Z),
    m_halted md' = None -> m_vm_lazy md' = [] ->
    ainv A' mb md' ->
    munch [(bv_unsigned sp - VPRINTF_STACK, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] mb mt ->
    wmono rsegs mb mt ->
    client_fp LayoutP0 A' [(bv_unsigned sp - VPRINTF_STACK, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] ->
    mem_inv rsegs mt -> md_frame md md' ->
    stk rsegs mt lo (bv_unsigned sp + -64) ->
    rw_cells rsegs mt (bv_unsigned sp + -64) [CB 8 j8; C8 (Z_to_bv 64 VA); C8 (Z_to_bv 64 VA); C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs mt S (vsb_cells v1) -> vsb_inv v1 false -> vb_error v1 = 0 -> vb_len v1 = vb_len v ->
    a_live A' S = Some 40 -> a_live A' (vb_buf v1) = Some (vb_size v1) -> S <> vb_buf v1 ->
    u8arr rsegs mt (vb_buf v1) bs1 -> Z.of_nat (length bs1) = vb_size v1 ->
    ssp_cells mt canary -> va_area mt VA slots -> bytes_at rsegs mt HS hs ->
    Lz = Z.of_nat (length (OUT slots hs)) ->
    (vb_size v1 - vb_len v1 - 1 < Lz -> vb_size v1 = vb_size v /\ vb_buf v1 = vb_buf v) ->
    vb_size v <= vb_size v1 -> (vb_size v1 = vb_size v \/ vb_size v1 <= vb_len v + Lz + 4096) ->
    (forall q, q <> vb_buf v -> q <> vb_buf v1 -> a_live A' q = a_live A q) ->
    (vb_buf v1 = vb_buf v \/ (a_live A (vb_buf v1) = None /\ a_live A' (vb_buf v) = None)) ->
    a_livebytes A' = a_livebytes A + vb_size v1 - vb_size v -> a_nlive A' = a_nlive A ->
    vb_error v = 0 ->
    4096 <= S -> S + 40 <= alloc_ceiling -> (S + 40 <= 0x10000 \/ 0x63000 <= S) ->
    (S + 40 <= vb_buf v1 \/ vb_buf v1 + vb_size v1 <= S) -> ~ (S < HS + Z.of_nat (length hs) /\ HS < S + 40) ->
    (forall m'', munch [(bv_unsigned sp - VPRINTF_STACK, bv_unsigned sp); (S, S + 40); (vb_buf v1, vb_buf v1 + vb_size v1)] mb m'' ->
                 mapped m'' (bv_unsigned sp - VPRINTF_STACK) VPRINTF_STACK ->
                 cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) VPRINTF_STACK
                        (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40)) (blk (vb_buf v1) (vb_size v1)) m m'') ->
    evt rsegs (rz_at rsegs md' T)
        (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp xt0 xt1 xt2 (Z_to_bv 64 S) (Z_to_bv 64 Afmt)
                 (Z_to_bv 64 (vb_size v1)) (Z_to_bv 64 (vb_len v1)) (Z_to_bv 64 (vb_size v1 - vb_len v1 - 1)) xa3 xa4 xa5 xa6 xa7
                 xs2 (Z_to_bv 64 Lz) s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            bvmap_empty (Z_to_bv 64 0x1992c) (Z_to_bv 32 0) None mt (seg_rom rsegs)).
  Proof.
    intros until Lz. intros MDH' MDL' AINVb MU WM CFP MIt MDF STt FR VSBC VINV1 E1 EL VLS1 VLB1 VNE1 U81 LBS1 SSPt VAA1 HSB1
           ELz TRUNC SZ1 SZ2 LIVEq REL LBp NLp E0 Slo Shi SimgN DSB1 HSDS CFK.
    pose proof VINV1 as VINV0. (first [ dand8 VINV0 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV0 as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    pose proof (HOUT _ _ _ HPRE) as OL. rewrite <- ELz in OL.
    assert (L0 : 0 <= Lz) by (rewrite ELz; lia).
    (* [comment removed for export] *)
    zstep. if_cases KM; zify_cond KM.
    - unsign KM.
      eapply vp_tail8; try eassumption; try lia.
    - unsign KM. zstep.
      eapply vp_tail8; try eassumption; try lia.
  Qed.

  #[using="K SPHI LO CEIL ST SP16 TP EM LBUD NBUD SSP HSH HSB HPRE VHI VLO VAA ART ARL HF VOBJ A2 A1 A0 MI AINV lo canary hs HS slots VA Afmt v S A P2 P1 HOUT HLA OUT PRE nargs la FMT AI Clg"] Lemma VSB_vprintf_cps :
    realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 VSB_vprintf_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    rewrite A0, A1, A2.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S v false AINV VOBJ)) as dR_5; dand11 dR_5 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S v false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof alloc_ceiling_val as CV.
    pose proof VOBJ as VOBJ0. vsb_open VOBJ0. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). cbn [al_segs LayoutP0] in U8.
    pose proof VINV as VINV0. (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. pose proof HLA as HLA'. rewrite <- HLA' in ART.
    pose proof (bytes_at_bound _ _ _ _ HSB) as HSBB.
    pose proof SSP as SSP0. destruct SSP0 as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2.
    pose proof VAA as VAA0. unfold va_area in VAA0.
    pose proof (bytes_at_bound _ _ _ _ VAA0) as VAB. rewrite u64s_length in VAB.
    unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK, EXT_MAX, RO_TOP, IMG_LO in *. unfold VSB_vprintf_entry.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    (* [comment removed for export] *)
    pose proof Simg as SimgN. unfold off_image in SimgN. cbn [al_image_lo al_image_hi LayoutP0] in SimgN.
    (* [comment removed for export] *)
    assert (HSG : HS + Z.of_nat (length hs) <= alloc_ceiling
                  /\ ~ (S < HS + Z.of_nat (length hs) /\ HS < S + 40)
                  /\ ~ (vb_buf v < HS + Z.of_nat (length hs) /\ HS < vb_buf v + vb_size v)).
    { destruct HSH as [[R1 R2] | (q & k & LQ & Q1 & Q2 & QS & QB & _)].
      - unfold IMG_LO, RO_TOP in R1, R2.
        pose proof Bimg as BimgN. unfold off_image in BimgN. cbn [al_image_lo al_image_hi LayoutP0] in BimgN. lia.
      - (first [ pose proof ((as_live_ok A m md _ _ AINV LQ)) as dR_8; dand5 dR_8 as _ _ _ QHI _ | destruct (as_live_ok A m md _ _ AINV LQ) as (_ & _ & _ & QHI & _) ]).
        pose proof (as_live_disjoint A m md _ _ _ _ AINV LQ VLS QS) as D1.
        pose proof (as_live_disjoint A m md _ _ _ _ AINV LQ VLB QB) as D2. lia. }
    (first [ dand3 HSG as HSC HSDS HSDB | destruct HSG as (HSC & HSDS & HSDB) ]).
    pose proof (munch_refl [(bv_unsigned sp - 8368, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8368, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v)]).
    { cbn. split; [left; lia|]. split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf v), (vb_size v); split; [exact VLB|lia]| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 64%nat ST.
    do 9 zstep.
    (* [comment removed for export] *)
    zstep.
    carve_frame 16%nat ST.
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. klia K1. } clear K1.
    zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. revert K2. vm_compute. congruence. } clear K2.
    zstep. zstep. if_cases K3; zify_cond K3. { exfalso. klia K3. } clear K3.
    zstep. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. unsign K4. klia K4. } clear K4.
    zstep. zstep. zstep.
    release_frame FR0 ST (bv_unsigned sp - 64).
    (* [comment removed for export] *)
    pose proof (rw_cells_read_sub rsegs _ _ _ 34 1 VSBC ltac:(lia) ltac:(cbn; lia)) as RDF.
    rewrite Vfl in RDF. unfold VSB_FLAGS_LIVE in RDF.
    match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end.
    zstep. zstep. zstep. if_cases K5; zify_cond K5. { dead K5. } clear K5 RDF.
    (* [comment removed for export] *)
    zstep. if_cases K6; zify_cond K6. { exfalso. klia K6. } clear K6.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      exfalso. rewrite Verr in KE. apply KE. reflexivity.
    - (* [comment removed for export] *)
      assert (E0 : vb_error v = 0) by exact Verr.
      clear KE Verr.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB rsegs _ _ [] _ _ [_;_;_;_;_;_] [8; 8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases KI; zify_cond KI. 2:{ rewrite Vind in KI. dead KI. } clear KI.
      zstep.
      (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (vp_iter _ gp tp _ _ _ (Z_to_bv 64 S) (Z_to_bv 64 Afmt) _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ sp
                  S Afmt VA slots HS hs canary lo v _ m _ s3 s2 s1 s0 ra _ _ bs0);
          [ reflexivity | reflexivity | exact MU | exact WM | assumption | reflexivity | exact ST | exact FR
          | exact VSBC | exact VINV0 | exact U8 | exact LBS | exact HF | unfold IMG_LO; exact ARL | unfold RO_TOP; lia
          | split; assumption | exact VAA0 | exact VLO | exact VHI | exact HPRE | exact HSB | lia | lia
          | exact Bimg | lia | exact DSB | lia | lia | exact CEIL | unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK; lia | lia ]. }
      cbv beta. intros ms1 IT1.
      (first [ dex16 IT1 as rax1 y0 y1 y2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 j81 bs1 m1; dand14 IT1 as -> MU1 WM1 MI1 ST1 FR1 VSBC1 U81 LBS1 HF1 SSPa VAA1 HSB1 OL | dand30 IT1 as rax1 y0 y1 y2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 j81 bs1 m1 -> MU1 WM1 MI1 ST1 FR1 VSBC1 U81 LBS1 HF1 SSPa VAA1 HSB1 OL | destruct IT1 as (rax1 & y0 & y1 & y2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & j81 & bs1 & m1
                       & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VSBC1 & U81 & LBS1 & HF1 & SSPa & VAA1 & HSB1 & OL) ]).
      clear MU WM ST FR VSBC U8 HF HSB SSP1 SSP2 VAA0. rename MU1 into MU. rename WM1 into WM.
      destruct SSPa as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2. unfold va_area in VAA1.
      (* [comment removed for export] *)
      zstep. if_cases KF; zify_cond KF.
      + (* [comment removed for export] *)
        unsign KF.
        eapply (vp_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ A md m m1 v bs1 j81 (Z.of_nat (length (OUT slots hs))));
          [ exact MDH | exact MDL | exact AINV | exact MU | exact WM | exact CFP | exact MI1 | exact (md_frame_refl _ MDL MDH)
          | exact ST1 | exact FR1 | exact VSBC1 | exact VINV0 | exact E0 | reflexivity | exact VLS | exact VLB | exact VNE
          | exact U81 | exact LBS1 | split; assumption | exact VAA1 | exact HSB1 | reflexivity
          | intros _; split; reflexivity | lia | lia | intros q _ _; reflexivity | left; reflexivity | lia | reflexivity | exact E0
          | exact Slo | exact Shi | exact SimgN | exact DSB | exact HSDS | ].
        intros m'' MU'' MP. unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK in MU'', MP |- *.
        eapply (cframe_noalloc LayoutP0); [exact MU'' | | exact MP | intros a X; left; exact X].
        intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
      + (* [comment removed for export] *)
        unsign KF.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        apply rz_stop.
        pose proof (ainv_munch LayoutP0 A m _ md _ AINV MU WM CFP) as AINV1.
        pose proof Bimg as BimgN. unfold off_image in BimgN. cbn [al_image_lo al_image_hi LayoutP0] in BimgN.
        assert (EE : al_errno LayoutP0 = 270516) by (vm_compute; reflexivity).
        (* [comment removed for export] *)
        lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          pose proof (crange_stack (L:=LayoutP0) A mx md (bv_unsigned sp - 64) 64 AINV1 ltac:(lia) ltac:(lia)
                        (rw_cells_mapped LayoutP0 mx _ _ FR1 ltac:(off_image_solve LayoutP0))) as CF1;
          pose proof (crange_stack (L:=LayoutP0) A mx md VA (Z.of_nat (length (u64s slots))) AINV1 ltac:(lia) ltac:(rewrite u64s_length; lia)
                        (bytes_at_mapped LayoutP0 mx _ _ VAA1 ltac:(apply (@off_image_stack _ LayoutP0 _); rewrite ?u64s_length; lia))) as CF2;
          pose proof (crange_image_ro (L:=LayoutP0) A mx md Afmt (Z.of_nat (cells_size FMT)) AINV1
                        ltac:(cbn [al_image_lo LayoutP0]; lia) ltac:(cbn [al_rw_lo LayoutP0]; lia) ltac:(lia)) as CF3;
          pose proof (crange_data (L:=LayoutP0) A mx md 197672 (Z.of_nat (cells_size [C8 (Z_to_bv 64 402376)])) AINV1
                        ltac:(cbn [al_rw_lo LayoutP0]; lia) ltac:(cbn [al_image_hi LayoutP0 cells_size csize Nat.add]; lia) ltac:(lia)
                        ltac:(intros i Hi Hs; cbn [al_static LayoutP0 cells_size csize Nat.add] in Hs, Hi; unfold p0_static in Hs; lia)
                        ltac:(rewrite EE; cbn; lia)) as CF4;
          pose proof (crange_data (L:=LayoutP0) A mx md 402376 (Z.of_nat (cells_size [C8 canary])) AINV1
                        ltac:(cbn [al_rw_lo LayoutP0]; lia) ltac:(cbn [al_image_hi LayoutP0 cells_size csize Nat.add]; lia) ltac:(lia)
                        ltac:(intros i Hi Hs; cbn [al_static LayoutP0 cells_size csize Nat.add] in Hs, Hi; unfold p0_static in Hs; lia)
                        ltac:(rewrite EE; cbn; lia)) as CF5
        end.
        assert (CF6 : crange A m1 HS (Z.of_nat (length hs))).
        { destruct HSH as [[R1 R2] | (q & k & LQ & Q1 & Q2 & QS & QB & NE)].
          - unfold IMG_LO, RO_TOP in R1, R2. apply (crange_image_ro (L:=LayoutP0) A m1 md _ _ AINV1); cbn [al_image_lo al_rw_lo LayoutP0]; lia.
          - apply (crange_block (L:=LayoutP0) A m1 md q k _ _ AINV1 LQ Q1 Q2). lia. }
        eapply VSB_extend_cps;
          [ exact AINV1 | exact MI1 | reflexivity | reflexivity
          | split; [exact VSBC1|]; split; [exact VINV0|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|];
            exists bs1; split; [exact U81|]; split; [exact LBS1| intros X; discriminate X]
          | lia | unfold EXT_MAX; lia
          | eapply Z.le_trans; [| exact LBUD]; apply Z.add_le_mono_l; apply vsb_extendsize_mono; lia | exact NBUD | exact TP
          | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
          | rewrite unsigned_lit by lia; reflexivity
          | rewrite unsigned_lit by lia; exact ST1 | exact CEIL | rewrite unsigned_lit by lia; unfold EXT_STACK, REALLOC_STACK; lia
          | rewrite unsigned_lit by lia; lia | ].
        clear VSBC1 U81.
        intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' v' AINV' MI' MDF VOBJ' LIVEq ST' XOUT.
        pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
        rewrite unsigned_lit in XOUT, ST' by lia.
        (first [ pose proof ((vsb_obj_geom LayoutP0 A' m' md' S v' false AINV' VOBJ')) as dR_11; dand11 dR_11 as _ _ _ _ B16' Blo' Bhi' Bimg' DSB' Smap' Bmap' | pose proof (vsb_obj_geom LayoutP0 A' m' md' S v' false AINV' VOBJ') as (_ & _ & _ & _ & B16' & Blo' & Bhi' & Bimg' & DSB' & Smap' & Bmap') ]).
        pose proof VOBJ' as VOBJ1. vsb_open VOBJ1. (first [ dex1 VBUF as bs2; dand3 VBUF as U82 LBS2 _ | dand4 VBUF as bs2 U82 LBS2 _ | destruct VBUF as (bs2 & U82 & LBS2 & _) ]). cbn [al_segs LayoutP0] in U82.
        pose proof VINV as VINV1. (first [ dand8 VINV as Vsz' Vlen' Verr' Vind' Vfl' Vb0' Vb47' Vbm' | destruct VINV as (Vsz' & Vlen' & Verr' & Vind' & Vfl' & Vb0' & Vb47' & Vbm') ]).
        destruct XOUT as (nb & Er & Ev & COPY & REL & LBx & NLx & FRK); subst r; unfold EXT_STACK, REALLOC_STACK in FRK.   (* [comment removed for export] *)
        * (* [comment removed for export] *)
          subst v'. clear Verr'. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent vsb_set_buf_size] in FRK, VSBC, VLS0, VLB0, VNE0, U82, LBS2, VINV1,
            Vsz', Vlen', Vind', Vfl', Vb0', Vb47', Vbm', B16', Blo', Bhi', Bimg', DSB', Smap', Bmap', REL, LIVEq |- *.
          (first [ pose proof ((vsb_extendsize_spec (vb_size v + (Z.of_nat (length (OUT slots hs)) - (vb_size v - vb_len v - 1))) ltac:(lia))) as dR_14; dand3 dR_14 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size v + (Z.of_nat (length (OUT slots hs)) - (vb_size v - vb_len v - 1))) ltac:(lia)) as (NS1 & NS2 & NS3) ]).
          pose proof (vsb_extendsize_tight (vb_size v + (Z.of_nat (length (OUT slots hs)) - (vb_size v - vb_len v - 1)))) as NST.
          set (nsz := vsb_extendsize (vb_size v + (Z.of_nat (length (OUT slots hs)) - (vb_size v - vb_len v - 1)))) in *.
          pose proof Bimg' as BimgN'. unfold off_image in BimgN'. cbn [al_image_lo al_image_hi LayoutP0] in BimgN'.
          (* [comment removed for export] *)
          assert (HSDB' : ~ (nb < HS + Z.of_nat (length hs) /\ HS < nb + nsz)).
          { destruct HSH as [[R1 R2] | (q & k & LQ & Q1 & Q2 & QS & QB & NE)].
            - unfold IMG_LO, RO_TOP in R1, R2. clear -R1 R2 BimgN'. lia.
            - eapply (blk_avoids_crange A A' m1 m' _ _ _ nb nsz HS _ FRK CF6);
                [ destruct hs; [congruence | cbn [length]; lia] | clear -HSC CV CEIL LO SPR; lia | clear -Vb0'; lia | clear -NS1 KF Vsz Vlen; lia | ].
              intros x Hx [[_ XB] | XS]; [clear -Hx XB HSDB; lia | clear -Hx XS HSDS; lia]. }
          clear BimgN'.
          (* [comment removed for export] *)
          hide DSB. hide DSB'. hide HSDB'. hide Vbm. hide Vbm'. hide REL. hide_slow.
          clear ST1. acall_xfer FRK. clear AINV1 CF1 CF2 CF3 CF4 CF5 CF6 BimgN.
          unhide DSB. unhide DSB'. unhide HSDB'. unhide Vbm. unhide Vbm'. unhide REL. unhide_slow.
          set (W2 := [(bv_unsigned sp - 8368, bv_unsigned sp); (S, S + 40); (nb, nb + nsz)]).
          pose proof (munch_refl W2 m') as MU2. pose proof (wmono_refl rsegs m') as WM2.
          assert (CFP2 : client_fp LayoutP0 A' W2)
            by (subst W2; cbn; split; [left; lia|]; split; [right; left; exists S, 40; split; [exact VLS0|lia]|];
                split; [right; left; exists nb, nsz; split; [exact VLB0|lia]| exact I]).
          subst W2.
          rename ST' into ST1.
          rz_resume MDH' MDL'.
          (* [comment removed for export] *)
          zstep. if_true.
          apply fr_recast8 in FR1.
          (* [comment removed for export] *)
          eapply evt_cut.
          { eapply (vp_iter _ gp tp _ _ _ (Z_to_bv 64 S) (Z_to_bv 64 Afmt) _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ sp
                      S Afmt VA slots HS hs canary lo (vsb_set_buf_size v nb nsz) _ m' _ s3 s2 s1 s0 ra _ _ bs2);
              [ reflexivity | reflexivity | exact MU2 | exact WM2 | assumption | reflexivity | exact ST1 | exact FR1
              | exact VSBC | exact VINV1 | exact U82 | exact LBS2 | exact HF1 | unfold IMG_LO; exact ARL | unfold RO_TOP; clear -ART HLA'; lia
              | split; assumption | exact VAA1 | exact VLO | exact VHI | exact HPRE | exact HSB1
              | cbn [vb_buf vb_len vb_size vsb_set_buf_size]; clear -HSDB' Vlen; lia | clear -HSC CEIL; lia
              | exact Bimg' | exact Bhi' | exact DSB' | exact Slo | exact Shi | exact CEIL | unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK; clear -LO; lia | exact SPHI ]. }
          cbv beta. intros ms2 IT2.
          (first [ dex16 IT2 as rax2 z0 z1 z2 za3 za4 za5 za6 za7 z3 z4 z5 z6 j82 bs3 m2; dand14 IT2 as -> MU3 WM3 MI3 ST3 FR3 VSBC3 U83 LBS3 HF3 SSPb VAA3 HSB3 _ | dand30 IT2 as rax2 z0 z1 z2 za3 za4 za5 za6 za7 z3 z4 z5 z6 j82 bs3 m2 -> MU3 WM3 MI3 ST3 FR3 VSBC3 U83 LBS3 HF3 SSPb VAA3 HSB3 _ | destruct IT2 as (rax2 & z0 & z1 & z2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & j82 & bs3 & m2
                           & -> & MU3 & WM3 & MI3 & ST3 & FR3 & VSBC3 & U83 & LBS3 & HF3 & SSPb & VAA3 & HSB3 & _) ]).
          cbn [vb_buf vb_len vb_size vsb_set_buf_size] in MU3, LBS3, U83.
          clear MU2 WM2 ST1 FR1 VSBC U82 HF1 HSB1 SSP1 SSP2 VAA1.
          destruct SSPb as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2. unfold va_area in VAA3.
          (* [comment removed for export] *)
          zstep. if_cases KF2; zify_cond KF2; cbn [vb_size vb_len vb_buf vsb_set_buf_size] in KF2.
          2:{ exfalso. unsign KF2. clear -KF2 NS1 Vlen Vsz KF OL. lia. }
          clear KF2.
          eapply (vp_tail0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' md' m' _ (vsb_set_buf_size v nb nsz) _ _ (Z.of_nat (length (OUT slots hs))));
            [ exact MDH' | exact MDL' | exact AINV' | exact MU3 | exact WM3 | exact CFP2 | assumption | exact MDF
            | exact ST3 | exact FR3 | exact VSBC3 | exact VINV1 | exact E0 | reflexivity | exact VLS0 | exact VLB0 | exact VNE0
            | exact U83 | exact LBS3 | split; assumption | exact VAA3 | exact HSB3 | reflexivity
            | cbn [vb_size vb_len vb_buf vsb_set_buf_size]; intros X; exfalso; clear -X NS1 Vlen Vsz KF OL; lia
            | cbn [vb_size vsb_set_buf_size]; clear -NS1 KF Vlen; lia
            | cbn [vb_size vsb_set_buf_size]; clear -NST KF Vlen Vsz OL; lia
            | exact LIVEq | exact REL | cbn [vb_size vsb_set_buf_size]; exact LBx | exact NLx | exact E0
            | exact Slo | exact Shi | exact SimgN | exact DSB' | exact HSDS | ].
          intros m'' MU'' MP. unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK in MU'', MP |- *.
          cbn [vb_size vb_len vb_buf vsb_set_buf_size] in MU'' |- *.
          eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
            [ exact MU | | exact FRK | lia | lia | intros a X; exact X
            | intros a X; left; exact X
            | exact MU'' | | exact MP ].
          -- intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
          -- intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
  Qed.
  End VP.

  (* [comment removed for export] *)
  #[using="P2 P1 HOUT HLA nargs"] Lemma VSB_printf_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (S : Z) (v : vsb_rec)
           (Afmt : Z) (HS : Z) (hs : list byte) (canary : word) (lo : Z) (T : TSet),
      let slots := [a2; a3; a4; a5; a6; a7] in
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 Afmt ->
      vsb_obj LayoutP0 A m S v false ->
      ro_cells rsegs m Afmt FMT -> IMG_LO <= Afmt -> Afmt + la <= RO_TOP ->
      PRE slots HS hs -> bytes_at rsegs m HS hs -> str_home A S v HS hs ->
      ssp_cells m canary ->
      vb_size v + Z.of_nat (length (OUT slots hs)) <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size v + Z.of_nat (length (OUT slots hs))) <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + PRINTF_STACK <= bv_unsigned sp ->
      bv_unsigned sp + 64 <= 2^47 ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
              (v' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          vsb_obj LayoutP0 A' m' S v' false ->
          (vb_error v <> 0 -> r = -1 /\ v' = v) ->
          (vb_error v = 0 -> r = 0 /\ vb_error v' = 0 /\
             (  vb_len v' = vb_len v + Z.of_nat (length (OUT slots hs))
             \/ (vb_len v' = vb_size v - 1 /\ vb_size v' = vb_size v /\ vb_buf v' = vb_buf v))) ->
          vb_len v <= vb_len v' <= vb_len v + Z.of_nat (length (OUT slots hs)) ->
          vb_size v <= vb_size v' <= Z.max (vb_size v) (vb_len v' + 4096) ->   (* [comment removed for export] *)
          (forall q, q <> vb_buf v -> q <> vb_buf v' -> a_live A' q = a_live A q) ->
          (vb_buf v' = vb_buf v \/ (a_live A (vb_buf v') = None /\ a_live A' (vb_buf v) = None)) ->
          a_livebytes A' = a_livebytes A + vb_size v' - vb_size v -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          stk rsegs m' lo (bv_unsigned sp) ->
          ssp_cells m' canary -> bytes_at rsegs m' HS hs ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) PRINTF_STACK
                   (fun a => blk (vb_buf v) (vb_size v) a \/ (S <= a < S + 40))
                   (blk (vb_buf v') (vb_size v')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 VSB_printf_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    intros until T. cbv zeta. intros AINV MI A0 A1 VOBJ HF ARL ART HPRE HSB HSH SSP EM LBUD NBUD TP SP16 ST CEIL LO SPHI K.
    rewrite A0, A1.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S v false AINV VOBJ)) as dR_16; dand11 dR_16 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md S v false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof alloc_ceiling_val as CV.
    pose proof VOBJ as VOBJ0. vsb_open VOBJ0. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). cbn [al_segs LayoutP0] in U8.
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    pose proof SSP as SSP0. destruct SSP0 as [SSP1 SSP2]. unfold GOT_SSP, SSP_GUARD in SSP1, SSP2.
    pose proof (bytes_at_bound _ _ _ _ HSB) as HSBB. pose proof (ro_cells_bound _ _ _ _ HF) as AB.
    pose proof HLA as HLA'. pose proof ART as ART'. rewrite <- HLA' in ART'. unfold RO_TOP in ART'. pose proof ARL as ARL'. unfold IMG_LO in ARL'.
    unfold PRINTF_STACK, VPRINTF_STACK, EXT_STACK, REALLOC_STACK in *. unfold VSB_printf_entry.
    assert (HSG : HS + Z.of_nat (length hs) <= alloc_ceiling
                  /\ ~ (S < HS + Z.of_nat (length hs) /\ HS < S + 40)
                  /\ ~ (vb_buf v < HS + Z.of_nat (length hs) /\ HS < vb_buf v + vb_size v)).
    { destruct HSH as [[R1 R2] | (q & k & LQ & Q1 & Q2 & QS & QB & _)].
      - unfold IMG_LO, RO_TOP in R1, R2.
        pose proof Bimg as BimgN. unfold off_image in BimgN. cbn [al_image_lo al_image_hi LayoutP0] in BimgN.
        pose proof Simg as SimgN. unfold off_image in SimgN. cbn [al_image_lo al_image_hi LayoutP0] in SimgN.
        clear -R1 R2 BimgN SimgN CV. lia.
      - (first [ pose proof ((as_live_ok A m md _ _ AINV LQ)) as dR_18; dand5 dR_18 as _ _ _ QHI _ | destruct (as_live_ok A m md _ _ AINV LQ) as (_ & _ & _ & QHI & _) ]).
        pose proof (as_live_disjoint A m md _ _ _ _ AINV LQ VLS QS) as D1.
        pose proof (as_live_disjoint A m md _ _ _ _ AINV LQ VLB QB) as D2. clear -Q1 Q2 QHI D1 D2. lia. }
    (first [ dand3 HSG as HSC HSDS HSDB | destruct HSG as (HSC & HSDS & HSDB) ]).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 8432, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (CFP : client_fp LayoutP0 A [(bv_unsigned sp - 8432, bv_unsigned sp); (S, S + 40); (vb_buf v, vb_buf v + vb_size v)]).
    { cbn. split; [left; lia|]. split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf v), (vb_size v); split; [exact VLB|lia]| exact I]. }
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 64%nat ST.
    do 10 zstep. zstep.
    (* [comment removed for export] *)
    apply rz_stop.
    pose proof (ainv_munch LayoutP0 A m _ md _ AINV MU WM CFP) as AINV1.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (L:=LayoutP0) A mx md (bv_unsigned sp - 64) 64 AINV1 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped LayoutP0 mx _ _ FR ltac:(off_image_solve LayoutP0))) as CF1;
      pose proof (crange_sub (L:=LayoutP0) A mx _ _ (bv_unsigned sp + -48) 48 CF1 ltac:(lia) ltac:(lia) ltac:(lia)) as CF2;
      pose proof (crange_sub (L:=LayoutP0) A mx _ _ (bv_unsigned sp + -64) 16 CF1 ltac:(lia) ltac:(lia) ltac:(lia)) as CF3 end.
    apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [FR1 FR2].
    cbn [cells_size csize Nat.add] in FR2. replace (bv_unsigned sp + -64 + Z.of_nat 16) with (bv_unsigned sp + -48) in FR2 by lia.
    eapply (VSB_vprintf_cps _ _ gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ md A S v
              Afmt (bv_unsigned sp + -48) [a2; a3; a4; a5; a6; a7] HS hs canary lo T);
      [ exact AINV1 | assumption | reflexivity | reflexivity | reflexivity
      | split; [exact VSBC|]; split; [exact VINV|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|];
        exists bs0; split; [exact U8|]; split; [exact LBS| intros X; discriminate X]
      | exact HF | exact ARL | exact ART
      | unfold va_area; cbn [u64s]; rewrite !app_nil_r;
        pose proof (bytes_at_of_rw_cells _ _ _ _ FR2) as B2; cbn [cells_bytes cbytes] in B2; rewrite app_nil_r in B2; exact B2
      | rewrite unsigned_lit by lia; lia | cbn [length]; lia
      | exact HPRE | exact HSB | exact HSH | split; assumption | exact EM | exact LBUD | exact NBUD | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK; lia
      | rewrite unsigned_lit by lia; lia | ].
    clear VSBC U8 HF HSB SSP1 SSP2.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' v' AINV' MI' MDF VOBJ' RE RO LENB SZB LIVEq REL LBv NLv ST' SSP' VAA' HSB' FRK.
    pose proof (as_lazy_nil A' m' md' AINV') as [MDL' MDH'].
    rewrite unsigned_lit in ST', FRK by lia. unfold VPRINTF_STACK, EXT_STACK, REALLOC_STACK in FRK.
    clear ST. acall_xfer FRK. clear AINV1 CF1 CF2 CF3.
    rz_resume MDH' MDL'.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    lazymatch type of FR1 with rw_cells _ ?mq _ ?cs1 => lazymatch type of FR2 with rw_cells _ _ _ ?cs2 =>
      assert (FR : rw_cells rsegs mq (bv_unsigned sp + -64) (cs1 ++ cs2))
        by (apply (proj2 (rw_cells_app rsegs _ _ [_;_] _)); split; [exact FR1|]; cbn [cells_size csize Nat.add];
            eapply rwc_eq; [exact FR2|lia]);
      clear FR1 FR2; cbn [app] in FR end end.
    release_frame FR ST' (bv_unsigned sp).
    cps_done.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ r A' _ md' v');
      [ exact AINV' | exact MI' | exact MDF | exact VOBJ' | exact RE | exact RO | exact LENB | exact SZB | exact LIVEq | exact REL | exact LBv | exact NLv
      | exact ST' | exact SSP' | exact HSB' | ].
    eapply (cframe_extend LayoutP0 _ _ _ _ _ _ _ _ _ _ m _ m' _ _ _);
      [ exact MU | | exact FRK | lia | lia | intros a X; exact X | intros a X; left; exact X
      | exact (munch_refl [] m') | | eapply (stk_mapped (L:=LayoutP0)); [exact ST' | exact CEIL | lia | lia] ].
    - intros a Ha NO. cbn [outside] in NO. unfold blk. lia.
    - intros a Ha NO. cbn [outside] in NO. exfalso. exact (NO I).
  Qed.
End S.

(* [comment removed for export] *)
Section Inst.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Definition VSB_vprintf_c_cps    := VSB_vprintf_cps FMT_C 3 1 PRE_C OUT_C eq_refl HOUT_C pc1_c pc2_c.
  Definition VSB_vprintf_pfx_cps  := VSB_vprintf_cps FMT_PFX 6 2 PRE_PFX OUT_PFX eq_refl HOUT_PFX pc1_pfx pc2_pfx.
  Definition VSB_vprintf_host_cps := VSB_vprintf_cps FMT_HOST 13 3 PRE_HOST OUT_HOST eq_refl HOUT_HOST pc1_host pc2_host.
  Definition VSB_printf_c_cps     := VSB_printf_cps FMT_C 3 1 PRE_C OUT_C eq_refl HOUT_C pc1_c pc2_c.
  Definition VSB_printf_pfx_cps   := VSB_printf_cps FMT_PFX 6 2 PRE_PFX OUT_PFX eq_refl HOUT_PFX pc1_pfx pc2_pfx.
  Definition VSB_printf_host_cps  := VSB_printf_cps FMT_HOST 13 3 PRE_HOST OUT_HOST eq_refl HOUT_HOST pc1_host pc2_host.
End Inst.
End V_VS46q.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg V_veao0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_VS46q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.

Module V_vejx2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strchr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr.R_memcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg V_veao0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_VS46q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
Definition A_fmtc : Z := 0x11925.      (* [comment removed for export] *)
Definition A_fmthost : Z := 0x1088c.   (* [comment removed for export] *)
Definition A_fmtpfx : Z := 0x104c4.    (* [comment removed for export] *)

Lemma fmt_c_at : forall m, mem_inv rsegs m -> ro_cells rsegs m A_fmtc FMT_C.
Proof.
  intros m MI. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia|]. cbn [cells_bytes cbytes app].
  apply (ro_bytes_at rsegs m); [exact MI| unfold A_fmtc; lia| cbn; unfold A_fmtc; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma fmt_host_at : forall m, mem_inv rsegs m -> ro_cells rsegs m A_fmthost FMT_HOST.
Proof.
  intros m MI. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia|]. cbn [cells_bytes cbytes app].
  apply (ro_bytes_at rsegs m); [exact MI| unfold A_fmthost; lia| cbn; unfold A_fmthost; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma fmt_pfx_at : forall m, mem_inv rsegs m -> ro_cells rsegs m A_fmtpfx FMT_PFX.
Proof.
  intros m MI. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia|]. cbn [cells_bytes cbytes app].
  apply (ro_bytes_at rsegs m); [exact MI| unfold A_fmtpfx; lia| cbn; unfold A_fmtpfx; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma u8arr_sub : forall m B bs (i : Z) (n : nat),
  u8arr rsegs m B bs -> 0 <= i -> (Z.to_nat i + n <= length bs)%nat ->
  bytes_at rsegs m (B + i) (firstn n (skipn (Z.to_nat i) bs)).
Proof.
  intros m B bs i n [BA _] Hi Hn.
  rewrite <- (firstn_skipn (Z.to_nat i) bs) in BA. apply bytes_at_app in BA. destruct BA as [_ BA].
  rewrite firstn_length_le in BA by lia. replace (B + Z.of_nat (Z.to_nat i)) with (B + i) in BA by lia.
  eapply bytes_at_prefix. rewrite <- (firstn_skipn n (skipn (Z.to_nat i) bs)) in BA. exact BA.
Qed.

(* [comment removed for export] *)
Definition LIT_apos : list byte := [Z_to_bv 8 38; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 111; Z_to_bv 8 115; Z_to_bv 8 59].
Definition LIT_quot : list byte := [Z_to_bv 8 38; Z_to_bv 8 113; Z_to_bv 8 117; Z_to_bv 8 111; Z_to_bv 8 116; Z_to_bv 8 59].
Definition LIT_amp : list byte := [Z_to_bv 8 38; Z_to_bv 8 97; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 59].
Lemma lit_apos_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1264a LIT_apos.
Proof. intros m MI. apply (ro_bytes_at rsegs m); [exact MI| lia| cbn; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.
Lemma lit_quot_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x110c0 LIT_quot.
Proof. intros m MI. apply (ro_bytes_at rsegs m); [exact MI| lia| cbn; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.
Lemma lit_amp_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10899 LIT_amp.
Proof. intros m MI. apply (ro_bytes_at rsegs m); [exact MI| lia| cbn; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma cstr_split : forall (l : list byte) (n : nat), nth_error l n = Some (Z_to_bv 8 0) ->
  exists z, (z <= n)%nat /\ l = firstn z l ++ Z_to_bv 8 0 :: skipn (S z) l /\ ~ In (Z_to_bv 8 0) (firstn z l)
            /\ find_byte 0 l = Some z /\ length (firstn z l) = z.
Proof.
  intros l n Hn.
  destruct (find_byte 0 l) as [z|] eqn:F.
  - (first [ pose proof ((find_byte_Some _ _ _ F)) as dR_1; dand3 dR_1 as LZ (b & Hb & Hb0) MIN | destruct (find_byte_Some _ _ _ F) as (LZ & (b & Hb & Hb0) & MIN) ]).
    assert (Eb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite Hb0; reflexivity). subst b.
    exists z. assert (ZN : (z <= n)%nat).
    { destruct (Nat.le_gt_cases z n) as [X|X]; [exact X|]. exfalso. exact (MIN n _ X Hn eq_refl). }
    split; [exact ZN|]. split; [| split; [| split; [reflexivity| apply firstn_length_le; lia]]].
    + (first [ pose proof ((nth_error_split l z _ Hb)) as dR_2; dex2 dR_2 as pre post; destruct dR_2 as [E L] | pose proof ((nth_error_split l z _ Hb)) as dR_2; dand4 dR_2 as pre post E L | destruct (nth_error_split l z _ Hb) as (pre & post & E & L) ]). rewrite E at 1.
      rewrite E. rewrite firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia.
      f_equal. f_equal. replace (S z) with (length (pre ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn; lia).
      replace (pre ++ Z_to_bv 8 0 :: post) with ((pre ++ [Z_to_bv 8 0]) ++ post) by (rewrite <- app_assoc; reflexivity).
      rewrite skipn_app, skipn_all, Nat.sub_diag; reflexivity.
    + intros IN. apply In_nth_error in IN. destruct IN as [j Hj].
      assert (J : (j < z)%nat). { pose proof (nth_error_lt _ _ _ Hj) as J. rewrite firstn_length_le in J by lia. exact J. }
      rewrite nth_error_firstn in Hj. replace (j <? z)%nat with true in Hj by (symmetry; apply Nat.ltb_lt; exact J). exact (MIN j _ J Hj eq_refl).
  - exfalso. exact (find_byte_None _ _ F _ _ Hn eq_refl).
Qed.

Lemma u8arr_suffix : forall m B bs (i : Z),
  u8arr rsegs m B bs -> 0 <= i -> (Z.to_nat i <= length bs)%nat -> bytes_at rsegs m (B + i) (skipn (Z.to_nat i) bs).
Proof.
  intros m B bs i [BA _] Hi Hn.
  rewrite <- (firstn_skipn (Z.to_nat i) bs) in BA. apply bytes_at_app in BA. destruct BA as [_ BA].
  rewrite firstn_length_le in BA by lia. replace (B + Z.of_nat (Z.to_nat i)) with (B + i) in BA by lia. exact BA.
Qed.

(* [comment removed for export] *)
Lemma nonul_firstn : forall (str : list byte) k, ~ In (Z_to_bv 8 0) str -> find_byte 0 (firstn k str) = None.
Proof.
  intros str k NZ. apply find_byte_notin. intros b IN E. apply NZ.
  replace (Z_to_bv 8 0) with b; [| apply bv_eq; rewrite E; reflexivity].
  rewrite <- (firstn_skipn k str). apply in_app_iff. left. exact IN.
Qed.

Lemma host_arg_ok : forall (str : list byte) (jx : nat) (HS : Z),
  ~ In (Z_to_bv 8 0) str -> (jx < length str)%nat -> 0 < HS -> Z.of_nat jx + 1 < 2^31 - 16 ->
  str_arg_ok (Z_to_bv 64 (Z.of_nat jx)) HS (firstn (S jx) str)
  /\ Z.of_nat (length (out_s (Z_to_bv 64 (Z.of_nat jx)) (firstn (S jx) str))) = Z.of_nat jx.
Proof.
  intros str jx HS NZ JL H0 JB.
  assert (SJ : sint32 (Z_to_bv 64 (Z.of_nat jx)) = Z.of_nat jx).
  { unfold sint32. rewrite unsigned_lit by lia. apply swrap32_id. lia. }
  assert (FB : find_byte 0 (firstn (Z.to_nat (Z.of_nat jx)) (firstn (S jx) str)) = None).
  { rewrite Nat2Z.id. rewrite firstn_firstn. replace (Nat.min jx (S jx)) with jx by lia. apply nonul_firstn. exact NZ. }
  assert (LH : length (firstn (S jx) str) = S jx) by (apply firstn_length_le; lia).
  split.
  - unfold str_arg_ok. rewrite SJ. unfold INT_MAX. split; [lia|]. split; [exact H0|]. split.
    + unfold memchr_ok. rewrite FB. rewrite LH. lia.
    + rewrite LH. lia.
  - unfold out_s, strnlen_res. rewrite SJ, FB. rewrite Nat2Z.id, firstn_firstn. replace (Nat.min jx (S jx)) with jx by lia.
    rewrite firstn_length_le by lia. reflexivity.
Qed.

Lemma sx32_small' : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z. lia.
Qed.

Lemma signed_small : forall z, (0 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit by lia.
  destruct (Z.ltb_spec0 z (2^63)); lia.
Qed.

(* [comment removed for export] *)
Section CF.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Lemma cframe_munch_win : forall o o' (sp win : Z) V N m mk m' Wf,
    cframe LayoutP0 o o' sp win V N m mk -> munch Wf mk m' ->
    (forall a, ~ outside Wf a -> sp - win <= a < sp) -> mapped m' (sp - win) win ->
    cframe LayoutP0 o o' sp win V N m m'.
  Proof.
    (intros o o' sp win V N m mk m' Wf; (first [ intro dR_22; dand3 dR_22 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros MU IN MAP). split; [| split; [exact MAP| exact C3]].
    intros a Ha NO VIS NW NE NV. destruct (C1 a Ha NO VIS NW NE NV) as [E NO']. split; [| exact NO'].
    rewrite <- E. apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia.
    destruct (Classical_Prop.classic (outside Wf a)) as [X|X]; [exact X|]. exfalso. pose proof (IN a X). lia.
  Qed.
End CF.

Definition LIT_http : list byte := [Z_to_bv 8 104; Z_to_bv 8 116; Z_to_bv 8 116; Z_to_bv 8 112; Z_to_bv 8 58; Z_to_bv 8 47; Z_to_bv 8 47].
Definition LIT_https : list byte := [Z_to_bv 8 104; Z_to_bv 8 116; Z_to_bv 8 116; Z_to_bv 8 112; Z_to_bv 8 115; Z_to_bv 8 58; Z_to_bv 8 47; Z_to_bv 8 47].
Lemma lit_http_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x110b8 LIT_http.
Proof. intros m MI. apply (ro_bytes_at rsegs m); [exact MI| lia| cbn; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.
Lemma lit_https_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x11acf LIT_https.
Proof. intros m MI. apply (ro_bytes_at rsegs m); [exact MI| lia| cbn; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma ssp_of_img : forall m, img_ok0 m -> exists canary, ssp_cells m canary.
Proof.
  intros m IMG. destruct (rw_guard_any m) as [g G]. exists g. split; [| exact G].
  destruct IMG as (_ & _ & _ & _ & GS & _). exact GS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition tinv {AI : AllocSpec LayoutP0} (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z) (sp : word)
  (m : mem) (md : Model) (A : AS) (yi : vsb_rec) (bs : list byte) (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z) : Prop :=
  vi = Some yi /\
  ainv Ak mk mdk /\ mem_inv rsegs mk /\ md_frame md mdk /\ stk rsegs mk lo (bv_unsigned sp + -112) /\
  henv_ok LayoutP0 VI0 H mk /\ img_ok0 mk /\
  rw_cells rsegs mk VEP (vep_cells v tag q) /\
  vsb_obj LayoutP0 Ak mk (v Fvsb) vvk false /\ VEP <> vb_buf vvk /\
  (a_livebytes Ak = a_livebytes A + vb_size vvk - vb_size vv /\ a_nlive Ak = a_nlive A) /\   (* [comment removed for export] *)
  vb_len vv <= vb_len vvk <= vb_len vv + e /\
  vb_size vv <= vb_size vvk <= Z.max (vb_size vv) (vb_len vvk + 4096) /\
  (vb_buf vvk = vb_buf vv \/ (a_live A (vb_buf vvk) = None /\ a_live Ak (vb_buf vv) = None)) /\
  (forall r, r <> vb_buf vv -> r <> vb_buf vvk -> a_live Ak r = a_live A r) /\
  cframe LayoutP0 (owned A) (owned Ak) (bv_unsigned sp) 8544
         (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                   \/ vsb_blocks (v Finclude_src) yi a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
         (blk (vb_buf vvk) (vb_size vvk)) m mk /\
  vsb_obj LayoutP0 Ak mk (v Finclude_src) yi true /\ u8arr rsegs mk (vb_buf yi) bs /\ Z.of_nat (length bs) = vb_size yi /\
  v Finclude_src <> vb_buf vvk /\ vb_buf yi <> vb_buf vvk.

End CEIL.


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 1.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HFL : 0 <= v Fflags < 16.
  Hypothesis HET : bool01 (v Femptytag).
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis HLM : v Flast_mark = 1.
  Hypothesis HAZ : v Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LayoutP0 A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis SZB : vb_size vv <= vb_len vv + 4096.
  Hypothesis LENB : vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  Let FRAME (c0 : cell) : list cell :=
    [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation TINV := (tinv VEP v tag q vv vi H lo sp m md A).

  Local Ltac unpack_tinv TI :=
    (first [ dand21 TI as EVI AINVk MIk MDFk STk HENVk IMGk VEPC SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & IMGk & VEPC & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_4; dand7 dR_4 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ)) as dR_5; dand11 dR_5 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0;
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV LS NES) as DVS;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV LB NEB) as DVB;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A VEP = Some 312, LS : a_live A (v Fvsb) = Some 40, LB : a_live A (vb_buf vv) = Some (vb_size vv) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ)) as dR_6; dand11 dR_6 as SI16 SIlo SIhi SIimg BI16 BIlo BIhi BIimg DSBI SImap BImap | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap) ]);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint A m md VEP 312 _ _ AINV VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LBI (not_eq_sym NIBB)) as DBBI
    end.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HFL (conj HET
      (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB (conj SZB (conj LENB (conj LBUD (conj NBUD (conj HVI (conj TP (conj SP16 (conj RA2
      (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)

  #[using="NEB NES SOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV T a1 a0 tp gp"] Lemma tinv_ext : forall yi bs Ak mk mdk vvk e Wf m' c0,
    TINV yi bs Ak mk mdk vvk e -> munch Wf mk m' -> wmono rsegs mk m' -> mem_inv rsegs m' ->
    (Wf = [] \/ exists l h, Wf = [(l, h)] /\ bv_unsigned sp - 8544 <= l /\ h <= bv_unsigned sp) ->
    stk rsegs m' lo (bv_unsigned sp + -112) -> rw_cells rsegs m' (bv_unsigned sp + -112) (FRAME c0) -> csize c0 = 8%nat ->
    TINV yi bs Ak m' mdk vvk e.
  Proof.
    touch_all.
    intros yi bs Ak mk mdk vvk e Wf m' c0 TI MU WM MI' HW ST' FR' C0.
    unpack_tinv TI. prelims. clear VEPC0. yi_facts EVI.
    (first [ pose proof ((vsb_obj_geom LayoutP0 Ak mk mdk (v Fvsb) vvk false AINVk SOBJk)) as dR_7; dand11 dR_7 as _ _ _ _ _ Bklo Bkhi _ _ _ _ | pose proof (vsb_obj_geom LayoutP0 Ak mk mdk (v Fvsb) vvk false AINVk SOBJk) as (_ & _ & _ & _ & _ & Bklo & Bkhi & _ & _ & _ & _) ]).
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    assert (LSIk : a_live Ak (v Finclude_src) = Some 40) by exact (proj1 (proj2 (proj2 IOBJk))).
    (first [ pose proof ((as_live_ok Ak mk mdk _ _ AINVk LSIk)) as dR_8; dand5 dR_8 as _ _ _ SIkhi _ | pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as (_ & _ & _ & SIkhi & _) ]).
    assert (LBIk : a_live Ak (vb_buf yi) = Some (vb_size yi)) by exact (proj1 (proj2 (proj2 (proj2 IOBJk)))).
    (first [ pose proof ((as_live_ok Ak mk mdk _ _ AINVk LBIk)) as dR_9; dand5 dR_9 as _ _ _ BIkhi _ | pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as (_ & _ & _ & BIkhi & _) ]).
    (first [ pose proof ((as_live_ok Ak mk mdk _ _ AINVk (proj1 (proj2 (proj2 SOBJk))))) as dR_10; dand5 dR_10 as _ _ _ Skhi _ | pose proof (as_live_ok Ak mk mdk _ _ AINVk (proj1 (proj2 (proj2 SOBJk)))) as (_ & _ & _ & Skhi & _) ]).
    (* [comment removed for export] *)
    assert (OUT : forall a, a < bv_unsigned sp - 8544 \/ bv_unsigned sp <= a -> outside Wf a).
    { intros a Ha. destruct HW as [-> | (l & h & -> & L1 & L2)]; cbn; [exact I|]. split; [clear - Ha L1 L2; lia| exact I]. }
    assert (DJ : forall a n, a + n <= bv_unsigned sp - 8544 \/ bv_unsigned sp <= a -> disjoint_from Wf a n).
    { intros a n Ha. destruct HW as [-> | (l & h & -> & L1 & L2)]; cbn; [exact I|]. split; [clear - Ha L1 L2; lia| exact I]. }
    assert (CFPW : client_fp LayoutP0 Ak Wf).
    { destruct HW as [-> | (l & h & -> & L1 & L2)]; cbn; [exact I|]. split; [left; clear - L1 L2 CEIL LO LAY ACV G3 SPH; lia| exact I]. }
    split; [exact EVI|]. split; [exact (ainv_munch LayoutP0 Ak mk m' mdk Wf AINVk MU WM CFPW)|]. split; [exact MI'|]. split; [exact MDFk|].
    split; [exact ST'|].
    split. { eapply (henv_ok_munch LayoutP0); [exact HENVk | exact MU | exact WM |]. intros a Ha. apply OUT.
             pose proof (proj1 (proj1 HENVk)) as EB. cbn [vi_bss VI0] in EB. rewrite EB in Ha. unfold h_hd, h_wrk, h_req in Ha. clear - Ha SPH Evsc ACV G2 CEIL LO. lia. }
    split. { eapply img_ok0_munch; [exact MU | | exact IMGk]. intros a Ha. apply OUT. unfold IMG0_LO, IMG0_HI in Ha. clear - Ha ACV CEIL LO. lia. }
    split. { eapply rw_cells_transport; [exact VEPC | exact MU | exact WM |]. apply DJ. rewrite (vep_cells_size v tag q TAG PADS). clear - Vhi CEIL LO; lia. }
    split. { eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | apply DJ | apply DJ]; [clear - Skhi CEIL LO; lia | clear - Bkhi CEIL LO; lia]. }
    split; [exact NEBk|]. split; [exact BUDk|]. split; [exact LENk|]. split; [exact SZk|]. split; [exact RELk|]. split; [exact LIVEk|].
    split. { eapply cframe_munch_win; [exact CFk | exact MU | |].
             - intros a NO. destruct HW as [E | (l & h & E & L1 & L2)]; rewrite E in NO; cbn in NO; [exfalso; exact (NO I)|]. clear - NO L1 L2. lia.
             - eapply (window_mapped LayoutP0 m' lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                 [exact ST' | exact FR' | cbv delta [FRAME]; cbn [cells_size csize Nat.add]; rewrite C0; clear; lia | exact CEIL | clear - LO; lia | clear; lia]. }
    split. { eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | apply DJ | apply DJ]; [clear - SIkhi CEIL LO; lia | clear - BIkhi CEIL LO; lia]. }
    split. { eapply u8arr_transport; [exact U8k | exact MU | exact WM | apply DJ]. rewrite LBS. clear - BIkhi CEIL LO; lia. }
    split; [exact LBS|]. split; [exact NISBk| exact NIBBk].
  Qed.

 
  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma printf_call : forall (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte)
      (HLA : Z.of_nat (cells_size FMT) = la) (HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z)
      (P1 : pass1_stmt FMT la) (P2 : pass2_stmt FMT la nargs PRE OUT)
      (yi : vsb_rec) (bs : list byte)
      (xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Afmt HS : Z) (hs : list byte) (n : Z) (ret : Z) (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z) (c0 : cell),
    TINV yi bs Ak mk mdk vvk e ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME c0) -> csize c0 = 8%nat ->
    ro_cells rsegs mk Afmt FMT -> IMG_LO <= Afmt -> Afmt + la <= RO_TOP ->
    PRE [xa2; xa3; xa4; xa5; xa6; xa7] HS hs -> bytes_at rsegs mk HS hs ->
    ((IMG_LO <= HS /\ HS + Z.of_nat (length hs) <= RO_TOP) \/ (vb_buf yi <= HS /\ HS + Z.of_nat (length hs) <= vb_buf yi + vb_size yi /\ hs <> [])) ->
    Z.of_nat (length (OUT [xa2; xa3; xa4; xa5; xa6; xa7] hs)) = n ->
    0 <= e -> e + n <= vb_len yi + 8 ->
    0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (Ak' : AS) (mk' : mem) (mdk' : Model) (vvk' : vsb_rec),
        TINV yi bs Ak' mk' mdk' vvk' (e + n) ->
        rw_cells rsegs mk' (bv_unsigned sp + -112) (FRAME c0) ->
        realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 VEP) xs1
                                        (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6')
                                   bvmap_empty (Z_to_bv 64 ret) (Z_to_bv 32 0) None mk' (seg_rom rsegs)) mdk') T) ->
    realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    (Z_to_bv 64 (v Fvsb)) (Z_to_bv 64 Afmt) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 VSB_printf_entry) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until c0. intros TI FR C0 HF ARL ART HPRE HSB HOME HN E0 BUD RETR RET2 K'.
    unpack_tinv TI. prelims. clear VEPC0. yi_facts EVI. cbv beta delta [FRAME] in FR.
    pose proof (as_lazy_nil _ _ _ AINVk) as [MDLk MDHk].
    (first [ pose proof ((vsb_obj_geom LayoutP0 Ak mk mdk (v Fvsb) vvk false AINVk SOBJk)) as dR_11; dand11 dR_11 as _ _ _ _ Bk16 Bklo Bkhi Bkimg DSBk _ Bkmap | pose proof (vsb_obj_geom LayoutP0 Ak mk mdk (v Fvsb) vvk false AINVk SOBJk) as (_ & _ & _ & _ & Bk16 & Bklo & Bkhi & Bkimg & DSBk & _ & Bkmap) ]).
    pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk. pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk.
    pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk. pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk.
    pose proof (proj1 (proj2 SOBJk)) as VINVk. pose proof (proj1 VINVk) as Vszk. pose proof (proj1 (proj2 VINVk)) as Vlenk.
    pose proof (proj1 (proj2 IOBJ)) as VINVI. pose proof (proj1 VINVI) as VszI. pose proof (proj1 (proj2 VINVI)) as VlenI.
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    destruct (ssp_of_img mk IMGk) as [can SSP].
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB. rewrite C0 in FRB.
    pose proof (HOUT _ _ _ HPRE) as HNB. rewrite HN in HNB.
    pose proof (Zle_0_nat (length (OUT [xa2; xa3; xa4; xa5; xa6; xa7] hs))) as HN0. rewrite HN in HN0.
    assert (HSH : str_home Ak (v Fvsb) vvk HS hs).
    { destruct HOME as [L|(R1 & R2 & R3)]; [left; exact L| right].
      exists (vb_buf yi), (vb_size yi). split; [exact LBIk|]. split; [exact R1|]. split; [exact R2|].
      split; [exact NIBS|]. split; [exact NIBBk| exact R3]. }
    eapply (VSB_printf_cps FMT la nargs PRE OUT HLA HOUT P1 P2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk mdk Ak (v Fvsb) vvk Afmt HS hs can lo T);
      [ exact AINVk | exact MIk | reflexivity | reflexivity | exact SOBJk | exact HF | exact ARL | exact ART
      | exact HPRE | exact HSB | exact HSH | exact SSP
      | rewrite HN; unfold EXT_MAX; revert LENk SZk LENB SZB E0 BUD Vszk Vlenk VlenI HN0; rewrite EVI; clear; intros; lia
      | rewrite HN; pose proof (vsb_extendsize_tight (vb_size vvk + n)) as EXTk;
        revert EXTk LENk SZk LENB SZB LBUD E0 BUD Vszk Vlenk VlenI HN0 Vlen0 BUDk; rewrite EVI; clear; intros; lia
      | revert NBUD BUDk; clear; intros; lia
      | exact TP
      | rewrite unsigned_lit by lia; clear - SP16; lia
      | rewrite unsigned_lit by lia; exact STk | exact CEIL
      | unfold PRINTF_STACK, VPRINTF_STACK, EXT_STACK, REALLOC_STACK; rewrite unsigned_lit by lia; clear - LO; lia
      | rewrite unsigned_lit by lia; clear - SPH G3; lia | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r Ak' mk' mdk' vv' AINV' MI' MDF' SOBJ' _ _ LEN' SZ' LIVE' REL' LB' NL' ST' _ _ CF'.
    rewrite unsigned_lit in ST', CF' by lia. unfold PRINTF_STACK, VPRINTF_STACK, EXT_STACK, REALLOC_STACK in CF'.
    rewrite HN in LEN'.
    rewrite (ret_pc_even ret RETR RET2).
    (first [ pose proof ((vsb_obj_geom LayoutP0 Ak' mk' mdk' (v Fvsb) vv' false AINV' SOBJ')) as dR_12; dand11 dR_12 as _ _ _ _ B'16 B'lo B'hi B'img DSB' _ B'map | pose proof (vsb_obj_geom LayoutP0 Ak' mk' mdk' (v Fvsb) vv' false AINV' SOBJ') as (_ & _ & _ & _ & B'16 & B'lo & B'hi & B'img & DSB' & _ & B'map) ]).
    (* [comment removed for export] *)
    assert (FRESH : forall r k, a_live Ak r = Some k -> r <> vb_buf vvk -> r <> vb_buf vv').
    { intros r0 k0 L0 N0 E0'. destruct REL' as [R|[R _]]; [exact (N0 (eq_trans E0' R))|]. rewrite <- E0' in R. rewrite R in L0. discriminate L0. }
    pose proof (FRESH VEP 312 LVk NEBk) as NEB'.
    pose proof (FRESH _ _ LSIk NISBk) as NISB'.
    pose proof (FRESH _ _ LBIk NIBBk) as NIBB'.
    assert (VC : vcover H Ak [VEP; v Finclude_src; vb_buf yi] (fun a => blk (vb_buf vvk) (vb_size vvk) a \/ v Fvsb <= a < v Fvsb + 40)).
    { intros a [X|X]; left; [exists (vb_buf vvk), (vb_size vvk) | exists (v Fvsb), 40]; (split; [assumption|]);
        [ unfold blk in X; split; [| clear - X; lia]; intros [E|[E|[E|[]]]]; [exact (NEBk E) | exact (NISBk E) | exact (NIBBk E)]
        | split; [| clear - X; lia]; intros [E|[E|[E|[]]]]; [exact (NES E) | exact (NISS E) | exact (NIBS E)] ]. }
    assert (HC : hcover Ak [] (fun a => blk (vb_buf vvk) (vb_size vvk) a \/ v Fvsb <= a < v Fvsb + 40)).
    { intros a [X|X]; [exists (vb_buf vvk), (vb_size vvk) | exists (v Fvsb), 40]; (split; [assumption|]); (split; [intros []|]); unfold blk in X; clear - X; lia. }
    pose proof (henv_call H Ak Ak' mk mk' mdk (bv_unsigned sp + -112) _ _ _ [] AINVk CF' HG ltac:(clear - CEIL LO; lia) ltac:(clear - SPH; lia) HC HENVk) as HENV''.
    pose proof (img_call H Ak Ak' mk mk' mdk (bv_unsigned sp + -112) _ _ _ _ AINVk CF' HG ltac:(clear - CEIL LO; lia) VC IMGk) as IMG''.
    pose proof (rw_cells_call_blk H Ak Ak' mk mk' mdk (bv_unsigned sp + -112) _ _ _ _ AINVk CF' HG ltac:(clear - CEIL LO; lia) VEP 312 VEP _ VC
                  ltac:(left; reflexivity) LVk ltac:(clear; lia) ltac:(rewrite (vep_cells_size v tag q TAG PADS); clear; lia) VEPC) as VEPC''.
    assert (LSI' : a_live Ak' (v Finclude_src) = Some 40) by (rewrite (LIVE' _ NISBk NISB'); exact LSIk).
    assert (LBI' : a_live Ak' (vb_buf yi) = Some (vb_size yi)) by (rewrite (LIVE' _ NIBBk NIBB'); exact LBIk).
    pose proof (vsb_obj_call H Ak Ak' mk mk' mdk (bv_unsigned sp + -112) _ _ _ _ AINVk CF' HG ltac:(clear - CEIL LO; lia) (v Finclude_src) yi true VC
                  ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) LSI' LBI' IOBJk) as IOBJ''.
    pose proof (u8arr_bound _ _ _ _ U8k) as U8B.
    pose proof (u8arr_call_blk H Ak Ak' mk mk' mdk (bv_unsigned sp + -112) _ _ _ _ AINVk CF' HG ltac:(clear - CEIL LO; lia) (vb_buf yi) (vb_size yi) (vb_buf yi) bs VC
                  ltac:(right; right; left; reflexivity) LBIk ltac:(clear; lia) ltac:(rewrite LBS; clear; lia) U8k) as U8''.
    pose proof (rw_cells_call_stack H Ak Ak' mk mk' mdk _ _ _ _ _ AINVk CF' ltac:(clear - CEIL LO; lia) ltac:(clear; lia) (bv_unsigned sp + -112) _ VC FR
                  ltac:(clear; lia) ltac:(cbn [cells_size csize Nat.add]; rewrite C0; clear - SPH Evsc; lia)) as FR''.
    assert (MAP' : mapped mk' (bv_unsigned sp - 8544) 8544).
    { eapply (window_mapped LayoutP0 mk' lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
        [exact ST' | exact FR'' | cbn [cells_size csize Nat.add]; rewrite C0; clear; lia | exact CEIL | clear - LO; lia | clear; lia]. }
    eapply K'; [| exact FR''].
    split; [exact EVI|]. split; [exact AINV'|]. split; [exact MI'|]. split; [exact (md_frame_trans _ _ _ MDFk MDF')|].
    split; [exact ST'|]. split; [exact HENV''|]. split; [exact IMG''|]. split; [exact VEPC''|].
    split; [exact SOBJ'|]. split; [exact NEB'|]. split; [revert BUDk LB' NL'; clear; intros; lia|].
    split; [clear - LENk LEN' HN0; lia|].
    split; [clear - LENk LEN' SZk SZ' HN0; lia|].
    split.
    { (* [comment removed for export] *)
      destruct (Z.eq_dec (vb_buf vv') (vb_buf vv)) as [E|NE]; [left; exact E| right]. split.
      - destruct (Z.eq_dec (vb_buf vv') (vb_buf vvk)) as [E2|NE2].
        + rewrite E2. destruct RELk as [R|[R _]]; [exfalso; apply NE; rewrite E2; exact R| exact R].
        + destruct REL' as [R|[R _]]; [exfalso; exact (NE2 R)|]. rewrite <- (LIVEk _ NE NE2). exact R.
      - destruct (Z.eq_dec (vb_buf vv) (vb_buf vvk)) as [E3|NE3].
        + destruct REL' as [R|[_ R]]; [exfalso; apply NE; rewrite R, E3; reflexivity|]. rewrite E3. exact R.
        + rewrite (LIVE' _ NE3 (not_eq_sym NE)). destruct RELk as [R|[_ R]]; [exfalso; exact (NE3 (eq_sym R))| exact R]. }
    split.
    { intros r0 R1 R2. destruct (Z.eq_dec r0 (vb_buf vvk)) as [E|NE].
      - rewrite E. destruct REL' as [R|[_ R]]; [exfalso; apply R2; rewrite E, R; reflexivity|]. rewrite R.
        rewrite E in R1. destruct RELk as [R'|[R' _]]; [exfalso; exact (R1 R')| symmetry; exact R'].
      - rewrite (LIVE' r0 NE R2). exact (LIVEk r0 R1 NE). }
    split.
    { eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mk');
        [ exact CFk
        | eapply (cframe_reframe LayoutP0); [exact CF' | clear; lia | clear; lia | exact MAP']
        | clear; lia | clear; lia | exact MAP' | intros a X; exact X
        | intros a [X|X]; [left; exact X | right; right; right; left; exact X]
        | intros a X; right; left; exact X ]. }
    split; [exact IOBJ''|]. split; [exact U8''|]. split; [exact LBS|]. split; [exact NISB'| exact NIBB'].
  Qed.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma printf_c_call : forall (yi : vsb_rec) (bs : list byte)
      (xt0 xt1 xt2 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (ch : word) (ret : Z) (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z) (c0 : cell),
    TINV yi bs Ak mk mdk vvk e ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME c0) -> csize c0 = 8%nat ->
    0 <= e -> e + 1 <= vb_len yi + 8 ->
    0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (Ak' : AS) (mk' : mem) (mdk' : Model) (vvk' : vsb_rec),
        TINV yi bs Ak' mk' mdk' vvk' (e + 1) ->
        rw_cells rsegs mk' (bv_unsigned sp + -112) (FRAME c0) ->
        realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 VEP) xs1
                                        (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6')
                                   bvmap_empty (Z_to_bv 64 ret) (Z_to_bv 32 0) None mk' (seg_rom rsegs)) mdk') T) ->
    realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    (Z_to_bv 64 (v Fvsb)) (Z_to_bv 64 A_fmtc) ch xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 VSB_printf_entry) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until c0. intros TI FR C0 E0 BUD RETR RET2 K'.
    eapply (printf_call FMT_C 3 1 PRE_C OUT_C eq_refl HOUT_C pc1_c pc2_c yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A_fmtc IMG_LO [] 1 ret Ak mk mdk vvk e c0);
      [ exact TI | exact FR | exact C0 | apply fmt_c_at; exact (proj1 (proj2 (proj2 TI))) | unfold IMG_LO, A_fmtc; clear; lia | unfold RO_TOP, A_fmtc; clear; lia
      | exists ch; reflexivity | apply bytes_at_nil; unfold IMG_LO; clear; lia | left; unfold IMG_LO, RO_TOP; cbn; clear; lia
      | reflexivity | exact E0 | exact BUD | exact RETR | exact RET2 | exact K' ].
  Qed.


  (* [comment removed for export] *)
  Local Ltac normal_tail IH TI FR i :=
    zstep; zstep; zstep; zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply (printf_c_call yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; apply rz_stop;
        replace (vb_buf yi + i + 1) with (vb_buf yi + (i + 1)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac entity_tail IH TI FR i w :=
    zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply (printf_c_call yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; zstep; apply rz_stop;
        replace (vb_buf yi + i + w) with (vb_buf yi + (i + w)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + w));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac ptr_small G :=
    try (rewrite Z.mod_small in G by
      (lazymatch goal with IR : (0 <= _ <= vb_len ?yi)%Z, VB : (vb_buf ?yi + vb_size ?yi < _)%Z, VL : (0 <= vb_len ?yi < vb_size ?yi)%Z, VZ : (0 < vb_buf ?yi)%Z |- _ =>
         revert IR VB VL VZ; clear; intros; lia end)).

  (* [comment removed for export] *)
  Local Ltac rd_byte U8 ik adr RD :=
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let bq := fresh "bq" in let Hq := fresh "Hq" in
      destruct (nth_error bs (Z.to_nat ik)) as [bq|] eqn:Hq;
      [ pose proof (byte_range bq);
        pose proof (u8arr_read rsegs mx B bs ik bq adr U8 Hq) as RD;
        lazymatch goal with IR : (0 <= _ <= vb_len _)%Z |- _ =>
          specialize (RD ltac:(clear - IR; lia) ltac:(unfold wa; f_equal; clear; lia)) end
      | exfalso; apply nth_error_None in Hq;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert Hq LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end ]
    end.

  (* [comment removed for export] *)
  Local Ltac bcmp_call U8 i w LIT LITAT :=
    zstep;
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let vq := fresh "vq" in let Mq := fresh "Mq" in
      destruct (memcmp_model_total (firstn w (skipn (Z.to_nat i) bs)) LIT w) as [vq Mq];
      [ rewrite firstn_length_le; [clear; lia|]; rewrite skipn_length;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end
      | cbn; clear; lia
      | eapply evt_cut;
        [ eapply bcmp_spec with (ls := firstn w (skipn (Z.to_nat i) bs)) (rs := LIT) (v := vq);
          [ rewrite unsigned_lit by lia;
            first [ apply (u8arr_sub mx B bs i w U8) | replace B with (B + i)%Z at 1 by (clear; lia); apply (u8arr_sub mx B bs i w U8) ];
            lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
              revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
              clear; intros; lia end
          | rewrite unsigned_lit by lia; apply LITAT; assumption
          | rewrite unsigned_lit by lia; exact Mq
          | assumption ]
        | ] ];
      (* [comment removed for export] *)
      let ms := fresh "ms" in let PO := fresh "PO" in let mq := fresh "mq" in
      let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIq" in
      intros ms PO; unfold memcmp_post in PO; destruct_exs PO;
      (first [ dand6 PO as E MUc WMc MIc _ _ | destruct PO as (E & MUc & WMc & MIc & _ & _) ]); subst ms;
      lazymatch type of MUc with munch [] mx ?mq =>
        lazymatch goal with TI : TINV _ bs _ mx _ _ _, FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MIo : mem_inv _ mx |- _ =>
          eapply (rw_cells_transport rsegs [] mx mq) in FR; [| exact MUc | exact WMc | exact I];
          try (lazymatch goal with VEPC : rw_cells _ mx VEP _ |- _ =>
                 eapply (rw_cells_transport rsegs [] mx mq) in VEPC; [| exact MUc | exact WMc | exact I] end);
          eapply (stk_transport_disjoint rsegs [] mx mq) in STq; [| exact MUc | exact WMc | exact I];
          eapply (u8arr_transport rsegs [] mx mq) in U8; [| exact MUc | exact WMc | exact I];
          let TI' := fresh "TI" in
          pose proof (tinv_ext _ _ _ _ _ _ _ [] mq _ TI MUc WMc MIc (or_introl eq_refl) STq FR eq_refl) as TI';
          clear TI MUc WMc MIo; rename TI' into TI;
          repeat match goal with Hx : rw_cells _ mx _ _ |- _ => clear Hx | Hx : ov_read_bytes _ mx _ _ = _ |- _ => clear Hx end
        end
      end;
      try (lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end)
    end.

  (* [comment removed for export] *)
  Local Ltac ent4_block IH TI FR U8 i G4 :=
    lazymatch goal with E0 : (0 <= ?e)%Z, BUD : (?e + _ + 1 <= _)%Z, IR : (0 <= i <= _)%Z, MEAS : (_ - i <= Z.of_nat _)%Z,
                        NUL : nth_error _ (Z.to_nat _) = Some (Z_to_bv 8 0), IL : (i < _)%Z |- _ =>
    lazymatch type of U8 with u8arr _ _ ?B _ =>
      (* [comment removed for export] *)
      let RD := fresh "RD" in
      rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
      rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
      rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
      rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
      do 6 zstep;
      let E1 := fresh "E1" in
      zstep; if_cases E1;
      [ (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 4;
        [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
      | clear E1;
        rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
        rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
        rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
        rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
        do 6 zstep;
        let E2 := fresh "E2" in
        zstep; if_cases E2;
        [ (* [comment removed for export] *) do 2 zstep; entity_tail IH TI FR i 4;
          [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
        | clear E2;
          (* [comment removed for export] *)
          let G5 := fresh "G5" in
          zstep; zstep; if_cases G5; zify_cond G5; ptr_small G5;
          [ (* [comment removed for export] *)
            normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
          | zstep; zstep; zstep;
            bcmp_call U8 i 5%nat LIT_amp lit_amp_at;
            let Q3 := fresh "Q3" in
            zstep; if_cases Q3;
            [ (* [comment removed for export] *)
              normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
            | (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 5;
              [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G5; lia | clear - BUD G5; lia | clear - MEAS G5; lia | exact NUL] ] ] ] ]
    end end.



  (* [comment removed for export] *)
  Local Ltac printf_c_site TI FR BUDTAC :=
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply (printf_c_call yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | BUDTAC | clear; lia | reflexivity | ];
      [ lazymatch goal with E0 : (0 <= e)%Z |- _ => exact E0 | _ => clear; lia end
      | clear TI FR;
        repeat match goal with Hx : rw_cells _ mk _ _ |- _ => clear Hx | Hx : stk _ mk _ _ |- _ => clear Hx | Hx : mem_inv _ mk |- _ => clear Hx
                             | Hx : u8arr _ mk _ _ |- _ => clear Hx | Hx : munch _ _ mk |- _ => clear Hx | Hx : wmono _ _ mk |- _ => clear Hx end;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR; cbv beta delta [FRAME] in FR;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2; clear MDL2 MDH2 ]
    end.

  (* [comment removed for export] *)
  Local Ltac tinv_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mx _ _ _ =>
      repeat match goal with
      | Hx : vsb_obj _ _ ?my (v Finclude_src) _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : Z.of_nat (length _) = vb_size _ |- _ => clear Hx
      | Hx : rw_cells _ ?my VEP _ |- _ => clear Hx
      | Hx : mem_inv _ ?my |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : stk _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : u8arr _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      end end;
    let X := fresh "TIc" in pose proof TI as X;
    destruct X as (_ & _ & MIk & _ & STk & _ & _ & VEPC & _ & _ & _ & _ & _ & _ & _ & _ & IOk & U8k & LBS & _ & _);
    unfold vep_cells in VEPC.


  (* [comment removed for export] *)
  Local Ltac env_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mk _ _ _ =>
      let HE := fresh "HENVk" in let IM := fresh "IMGk" in
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HE;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IM;
      let GLOB := fresh "GLOBk" in let HOBJ := fresh "HOBJk" in
      destruct HE as [GLOB HOBJ];
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let CNT := fresh "CNT" in
      pose proof GLOB as (EBSS & BSS & CP & [c CNT]); cbn [al_segs LayoutP0] in BSS, CP, CNT; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_14; dand3 dR_14 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      let GV := fresh "GVSC" in
      (first [ pose proof (IM) as dR_17; dand4 dR_17 as _ _ GV _ | pose proof IM as (_ & _ & GV & _) ]); unfold GOT_vsc in GV
    end.


  Local Ltac unhide_disj_vimg := try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end.

  (* [comment removed for export] *)
  Local Ltac tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      repeat match goal with Hi : img_ok0 ?mm |- _ => lazymatch mm with m => fail | _ => clear Hi end end;
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & IMGk & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8o & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      assert (TI2 : TINV yi bs Ak mc mdk vvk e);
      [ split; [exact EVI'|]; split; [exact (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk)|]; split; [exact MIq|]; split; [exact MDFk|];
        split; [exact STq|]; split; [exact HENV2|];
        split; [eapply img_ok0_munch; [exact MU | | exact IMGk]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside];
                unhide_disj_vimg; revert Ha; geo_lia |];
        split; [unfold vep_cells; lazymatch goal with EVC : v Fvc = _ |- _ => try rewrite EVC end; exact VEPq|];
        split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia] |];
        split; [exact NEBk|]; split; [exact BUDk|]; split; [exact LENk|]; split; [exact SZk|]; split; [exact RELk|]; split; [exact LIVEk|];
        split; [ lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
                   eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
                   [ exact CFk
                   | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
                     eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | clear; lia | clear; lia
                   | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] end |];
        split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia] |];
        split; [eapply u8arr_transport; [exact U8o | exact MU | exact WM |]; rewrite LBS'; cbn; unhide DVBI; revert DVBI BIk; geo_lia |];
        split; [exact LBS'|]; split; [exact NISBk| exact NIBBk]
      | clear AINVk MDFk IMGk SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8o LBS' NISBk NIBBk EVI' LVk LBk LSk DVBk Bk Sk LSIk LBIk SIk BIk CFPk ]
    end end end.





End S.
End V_vejx2.


Module V_veifi.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strchr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr.R_memcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg V_veao0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_VS46q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vejx2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 1.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HFL : 0 <= v Fflags < 16.
  Hypothesis HET : bool01 (v Femptytag).
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis HLM : v Flast_mark = 1.
  Hypothesis HAZ : v Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LayoutP0 A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis SZB : vb_size vv <= vb_len vv + 4096.
  Hypothesis LENB : vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  Let FRAME (c0 : cell) : list cell :=
    [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation TINV := (tinv VEP v tag q vv vi H lo sp m md A).

  Local Ltac unpack_tinv TI :=
    (first [ dand21 TI as EVI AINVk MIk MDFk STk HENVk IMGk VEPC SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & IMGk & VEPC & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0;
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV LS NES) as DVS;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV LB NEB) as DVB;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A VEP = Some 312, LS : a_live A (v Fvsb) = Some 40, LB : a_live A (vb_buf vv) = Some (vb_size vv) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ)) as dR_4; dand11 dR_4 as SI16 SIlo SIhi SIimg BI16 BIlo BIhi BIimg DSBI SImap BImap | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap) ]);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint A m md VEP 312 _ _ AINV VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LBI (not_eq_sym NIBB)) as DBBI
    end.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HFL (conj HET
      (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB (conj SZB (conj LENB (conj LBUD (conj NBUD (conj HVI (conj TP (conj SP16 (conj RA2
      (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)

  #[using="NEB NES SOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)

 

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma seg_end : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z),
    TINV yi bs Ak mk mdk vvk e ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME (C8 (Z_to_bv 64 (VEP + 280)))) ->
    0 <= e -> e + 1 <= vb_len yi + 8 ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b5f4) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until e. intros TI FR E0 BUD.
    pose proof TI as TI0. unpack_tinv TI0. prelims. clear VEPC0. yi_facts EVI. cbv beta delta [FRAME] in FR.
    pose proof (as_lazy_nil _ _ _ AINVk) as [MDLk MDHk].
    unfold vep_cells in VEPC.
    hide_disj. hide_slow.
    apply rz_go; [exact MDHk | exact MDLk |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | exact E0 | exact BUD | clear; lia | reflexivity | ].
    clear VEPC FR MIk STk TI SOBJk IOBJk U8k CFk RELk LIVEk LENk SZk HENVk IMGk AINVk MDFk MDLk MDHk NEBk BUDk NISBk NIBBk EVI LBS.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A2 m2 md2 vv2 TI2 FR2.
    pose proof TI2 as TI. unpack_tinv TI.
    pose proof (as_lazy_nil _ _ _ AINVk) as [MDL2 MDH2].
    cbv beta delta [FRAME] in FR2. unfold vep_cells in VEPC.
    rz_resume MDH2 MDL2.
    (* [comment removed for export] *)
    zstep. zstep.
    apply rz_stop.
    pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk. pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk.
    pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk. pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk.
    assert (LVk : a_live A2 VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); exact VLV).
    (first [ pose proof ((vsb_obj_geom LayoutP0 A2 m2 md2 (v Fvsb) vv2 false AINVk SOBJk)) as dR_5; dand11 dR_5 as _ _ _ _ Bk16 Bklo Bkhi Bkimg DSBk _ Bkmap | pose proof (vsb_obj_geom LayoutP0 A2 m2 md2 (v Fvsb) vv2 false AINVk SOBJk) as (_ & _ & _ & _ & Bk16 & Bklo & Bkhi & Bkimg & DSBk & _ & Bkmap) ]).
    pose proof (as_live_disjoint A2 m2 md2 VEP 312 (vb_buf vv2) (vb_size vv2) AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk. hide DVBk.
    vep_split3 VEPC 45%nat VEPa VEPp VEPb.
    pose proof (crange_block (L:=LayoutP0) A2 m2 md2 VEP 312 VEP 280 AINVk LVk ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as CRa.
    pose proof (crange_block (L:=LayoutP0) A2 m2 md2 VEP 312 (VEP + 288) 24 AINVk LVk ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as CRb.
    unfold VSB_destroy_entry.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 md2 A2 (VEP + 280) (v Finclude_src) yi true lo);
      [ exact AINVk | exact MIk | reflexivity | cbn [w64]; exact VEPp
      | right; exists VEP, 312; split; [exact LVk|]; split; [unhide NIS; unhide NIB; intros [X|[X|[]]]; [exact (NIS X)| exact (NIB X)] | clear; lia]
      | exact IOBJk | exact TP
      | rewrite unsigned_lit by lia; unhide SP16; clear - SP16; lia
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; exact STk | exact CEIL
      | unfold DESTROY_STACK, FREE_STACK; rewrite unsigned_lit by lia; clear - LO; lia
      | rewrite unsigned_lit by lia; clear - SPH G3; lia | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A3 m3 md3 AINV3 MI3 MDF3 ST3 PSC3 LVS3 LVB3 LIVE3 LBd3 NLd3 CF3.
    rewrite unsigned_lit in ST3, CF3 by lia. unfold DESTROY_STACK, FREE_STACK in CF3.
    pose proof (as_lazy_nil _ _ _ AINV3) as [MDL3 MDH3].
    assert (HC2 : hcover A2 [] (fun a => blk (v Finclude_src) 40 a \/ blk (vb_buf yi) (vb_size yi) a \/ VEP + 280 <= a < VEP + 280 + 8))
      by (hcover_destroy LSIk LBIk LVk).
    pose proof (henv_call H A2 A3 m2 m3 md2 (bv_unsigned sp + -112) _ _ _ [] AINVk CF3 HG ltac:(clear - CEIL LO; lia) ltac:(clear - SPH; lia) HC2 HENVk) as HENV3.
    pose proof (rw_cells_call_stack H A2 A3 m2 m3 md2 _ _ _ _ [] AINVk CF3 ltac:(clear - CEIL LO; lia) ltac:(clear; lia) (bv_unsigned sp + -112) _ (hcover_vcover H A2 [] _ HC2) FR2
                  ltac:(clear; lia) ltac:(cbn; clear - SPH Evsc; lia)) as FR3.
    assert (LV3 : a_live A3 VEP = Some 312) by (unhide NIS; unhide NIB; rewrite (LIVE3 VEP (not_eq_sym NIS) (not_eq_sym NIB)); exact LVk).
    assert (LS3 : a_live A3 (v Fvsb) = Some 40) by (unhide NISS; unhide NIBS; rewrite (LIVE3 _ (not_eq_sym NISS) (not_eq_sym NIBS)); exact LSk).
    assert (LB3 : a_live A3 (vb_buf vv2) = Some (vb_size vv2)) by (unhide NISBk; unhide NIBBk; rewrite (LIVE3 _ (not_eq_sym NISBk) (not_eq_sym NIBBk)); exact LBk).
    assert (SOBJ3 : vsb_obj LayoutP0 A3 m3 (v Fvsb) vv2 false).
    { eapply (vsb_obj_call H A2 A3 m2 m3 md2 (bv_unsigned sp + -112) _ _ _ [v Fvsb; vb_buf vv2] AINVk CF3 HG ltac:(clear - CEIL LO; lia) (v Fvsb) vv2 false);
        [ | left; reflexivity | right; left; reflexivity | exact LS3 | exact LB3 | exact SOBJk ].
      intros a Ha. left. revert a Ha. hcover_destroy LSIk LBIk LVk. }
    xfer_piece CF3 VEPa CRa. xfer_piece CF3 VEPb CRb.
    clear FR2 STk CRa CRb.
    cbn [w64] in PSC3. vep_join3 VEPa PSC3 VEPb VEPC3.
    pose proof (munch_refl [(VEP, VEP + 312)] m3) as MU3. pose proof (wmono_refl rsegs m3) as WM3.
    rz_resume MDH3 MDL3.
    (* [comment removed for export] *)
    zstep.
    do 15 zstep.
    try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    cps_done.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m4 end.
    release_frame FR3 ST3 (bv_unsigned sp).
    assert (CFP4 : client_fp LayoutP0 A3 [(VEP, VEP + 312)]) by (cbn; split; [right; left; exists VEP, 312; split; [exact LV3| clear; lia]| exact I]).
    pose proof (ainv_munch LayoutP0 A3 m3 m4 md3 _ AINV3 MU3 WM3 CFP4) as AINV4.
    assert (HENV4 : henv_ok LayoutP0 VI0 H m4).
    { eapply (henv_ok_munch LayoutP0); [exact HENV3 | exact MU3 | exact WM3 |].
      intros a Ha. unfold h_hd, h_wrk, h_req in Ha. cbn [outside]. revert Ha.
      lazymatch goal with EB : h_bss H = _ |- _ => idtac | _ => pose proof (proj1 (proj1 HENV3)) as EBSS; cbn [vi_bss VI0] in EBSS end.
      lazymatch goal with EB : h_bss H = _ |- _ => rewrite EB end. geo_lia. }
    assert (SOBJ4 : vsb_obj LayoutP0 A3 m4 (v Fvsb) vv2 false).
    { eapply (vsb_obj_munch LayoutP0); [exact SOBJ3 | exact MU3 | exact WM3 | |]; cbn.
      - unhide DVS. clear - DVS. lia.
      - unhide DVBk. clear - DVBk. lia. }
    unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A3 m4 md3 (fupd (fupd v Finclude_src 0) Finclude_continue 0) vv2);
      [ exact AINV4 | assumption | exact (md_frame_trans _ _ _ MDFk MDF3) | exact ST3 | exact HENV4
      | | | left; reflexivity | left; reflexivity | reflexivity | exact SOBJ4
      | rewrite EVI; clear - LENk BUD; lia | clear - SZk; lia | | rewrite EVI | rewrite EVI ].
    - (* [comment removed for export] *)
      split; [exact LV3|]. split; [| split; [exact TAG| exact PADS]].
      cbn [al_segs LayoutP0]. unfold vep_cells. cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. exact VEPC3.
    - (* [comment removed for export] *)
      apply vkeep_fupd; [apply vkeep_fupd; [apply vkeep_refl| in_tac]| in_tac].
    - (* [comment removed for export] *)
      destruct RELk as [R|[R1 R2]]; [left; exact R| right]. split; [exact R1|].
      rewrite (LIVE3 _ (not_eq_sym NISB) (not_eq_sym NIBB)). exact R2.
    - (* [comment removed for export] *)
      split; [exact LVS3|]. split; [exact LVB3|].
      split; [intros rr R1 R2 R3 R4; rewrite (LIVE3 rr R3 R4); exact (LIVEk rr R1 R2)|].
      revert BUDk LBd3 NLd3; clear; intros; lia.
    - (* [comment removed for export] *)
      lazymatch goal with |- cframe _ _ _ _ _ ?VF _ _ _ =>
        assert (CFB : cframe LayoutP0 (owned A2) (owned A3) (bv_unsigned sp) 8544 VF nowhere m2 m4) end.
      { eapply (cframe_extend LayoutP0 _ _ (bv_unsigned sp + -112) _ (bv_unsigned sp) _ _ _ _ _ m2 m2 m3 m4 [] _);
          [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF3 | clear; lia | clear; lia
          | | intros a X; left; exact X | exact MU3 | | eapply (stk_mapped (L:=LayoutP0)); [exact ST3 | exact CEIL | clear -LO; lia | clear; lia] ].
        + intros a [X|[X|X]]; [right; right; right; left; left; exact X | right; right; right; left; right; exact X | left; split; [clear -Vlo; lia| clear -X; lia]].
        + intros a Ha NO. cbn [outside] in NO. right; left. left. split; [clear - Vlo; lia| clear - NO; lia]. }
      eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m m2 m4);
        [ exact CFk | exact CFB | clear; lia | clear; lia
        | eapply (stk_mapped (L:=LayoutP0)); [exact ST3 | exact CEIL | clear -LO; lia | clear; lia]
        | intros a X; exact X | intros a X; right; exact X | intros a X; left; exact X ].
  Qed.

  (* [comment removed for export] *)
  Local Ltac normal_tail IH TI FR i :=
    zstep; zstep; zstep; zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; apply rz_stop;
        replace (vb_buf yi + i + 1) with (vb_buf yi + (i + 1)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac entity_tail IH TI FR i w :=
    zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; zstep; apply rz_stop;
        replace (vb_buf yi + i + w) with (vb_buf yi + (i + w)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + w));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac ptr_small G :=
    try (rewrite Z.mod_small in G by
      (lazymatch goal with IR : (0 <= _ <= vb_len ?yi)%Z, VB : (vb_buf ?yi + vb_size ?yi < _)%Z, VL : (0 <= vb_len ?yi < vb_size ?yi)%Z, VZ : (0 < vb_buf ?yi)%Z |- _ =>
         revert IR VB VL VZ; clear; intros; lia end)).

  (* [comment removed for export] *)
  Local Ltac rd_byte U8 ik adr RD :=
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let bq := fresh "bq" in let Hq := fresh "Hq" in
      destruct (nth_error bs (Z.to_nat ik)) as [bq|] eqn:Hq;
      [ pose proof (byte_range bq);
        pose proof (u8arr_read rsegs mx B bs ik bq adr U8 Hq) as RD;
        lazymatch goal with IR : (0 <= _ <= vb_len _)%Z |- _ =>
          specialize (RD ltac:(clear - IR; lia) ltac:(unfold wa; f_equal; clear; lia)) end
      | exfalso; apply nth_error_None in Hq;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert Hq LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end ]
    end.

  (* [comment removed for export] *)
  Local Ltac bcmp_call U8 i w LIT LITAT :=
    zstep;
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let vq := fresh "vq" in let Mq := fresh "Mq" in
      destruct (memcmp_model_total (firstn w (skipn (Z.to_nat i) bs)) LIT w) as [vq Mq];
      [ rewrite firstn_length_le; [clear; lia|]; rewrite skipn_length;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end
      | cbn; clear; lia
      | eapply evt_cut;
        [ eapply bcmp_spec with (ls := firstn w (skipn (Z.to_nat i) bs)) (rs := LIT) (v := vq);
          [ rewrite unsigned_lit by lia;
            first [ apply (u8arr_sub mx B bs i w U8) | replace B with (B + i)%Z at 1 by (clear; lia); apply (u8arr_sub mx B bs i w U8) ];
            lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
              revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
              clear; intros; lia end
          | rewrite unsigned_lit by lia; apply LITAT; assumption
          | rewrite unsigned_lit by lia; exact Mq
          | assumption ]
        | ] ];
      (* [comment removed for export] *)
      let ms := fresh "ms" in let PO := fresh "PO" in let mq := fresh "mq" in
      let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIq" in
      intros ms PO; unfold memcmp_post in PO; destruct_exs PO;
      (first [ dand6 PO as E MUc WMc MIc _ _ | destruct PO as (E & MUc & WMc & MIc & _ & _) ]); subst ms;
      lazymatch type of MUc with munch [] mx ?mq =>
        lazymatch goal with TI : TINV _ bs _ mx _ _ _, FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MIo : mem_inv _ mx |- _ =>
          eapply (rw_cells_transport rsegs [] mx mq) in FR; [| exact MUc | exact WMc | exact I];
          try (lazymatch goal with VEPC : rw_cells _ mx VEP _ |- _ =>
                 eapply (rw_cells_transport rsegs [] mx mq) in VEPC; [| exact MUc | exact WMc | exact I] end);
          eapply (stk_transport_disjoint rsegs [] mx mq) in STq; [| exact MUc | exact WMc | exact I];
          eapply (u8arr_transport rsegs [] mx mq) in U8; [| exact MUc | exact WMc | exact I];
          let TI' := fresh "TI" in
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ [] mq _ TI MUc WMc MIc (or_introl eq_refl) STq FR eq_refl) as TI';
          clear TI MUc WMc MIo; rename TI' into TI;
          repeat match goal with Hx : rw_cells _ mx _ _ |- _ => clear Hx | Hx : ov_read_bytes _ mx _ _ = _ |- _ => clear Hx end
        end
      end;
      try (lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end)
    end.

  (* [comment removed for export] *)
  Local Ltac ent4_block IH TI FR U8 i G4 :=
    lazymatch goal with E0 : (0 <= ?e)%Z, BUD : (?e + _ + 1 <= _)%Z, IR : (0 <= i <= _)%Z, MEAS : (_ - i <= Z.of_nat _)%Z,
                        NUL : nth_error _ (Z.to_nat _) = Some (Z_to_bv 8 0), IL : (i < _)%Z |- _ =>
    lazymatch type of U8 with u8arr _ _ ?B _ =>
      (* [comment removed for export] *)
      let RD := fresh "RD" in
      rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
      rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
      rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
      rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
      do 6 zstep;
      let E1 := fresh "E1" in
      zstep; if_cases E1;
      [ (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 4;
        [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
      | clear E1;
        rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
        rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
        rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
        rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
        do 6 zstep;
        let E2 := fresh "E2" in
        zstep; if_cases E2;
        [ (* [comment removed for export] *) do 2 zstep; entity_tail IH TI FR i 4;
          [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
        | clear E2;
          (* [comment removed for export] *)
          let G5 := fresh "G5" in
          zstep; zstep; if_cases G5; zify_cond G5; ptr_small G5;
          [ (* [comment removed for export] *)
            normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
          | zstep; zstep; zstep;
            bcmp_call U8 i 5%nat LIT_amp lit_amp_at;
            let Q3 := fresh "Q3" in
            zstep; if_cases Q3;
            [ (* [comment removed for export] *)
              normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
            | (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 5;
              [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G5; lia | clear - BUD G5; lia | clear - MEAS G5; lia | exact NUL] ] ] ] ]
    end end.



  (* [comment removed for export] *)
  Local Ltac printf_c_site TI FR BUDTAC :=
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | BUDTAC | clear; lia | reflexivity | ];
      [ lazymatch goal with E0 : (0 <= e)%Z |- _ => exact E0 | _ => clear; lia end
      | clear TI FR;
        repeat match goal with Hx : rw_cells _ mk _ _ |- _ => clear Hx | Hx : stk _ mk _ _ |- _ => clear Hx | Hx : mem_inv _ mk |- _ => clear Hx
                             | Hx : u8arr _ mk _ _ |- _ => clear Hx | Hx : munch _ _ mk |- _ => clear Hx | Hx : wmono _ _ mk |- _ => clear Hx end;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR; cbv beta delta [FRAME] in FR;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2; clear MDL2 MDH2 ]
    end.

  (* [comment removed for export] *)
  Local Ltac tinv_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mx _ _ _ =>
      repeat match goal with
      | Hx : vsb_obj _ _ ?my (v Finclude_src) _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : Z.of_nat (length _) = vb_size _ |- _ => clear Hx
      | Hx : rw_cells _ ?my VEP _ |- _ => clear Hx
      | Hx : mem_inv _ ?my |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : stk _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : u8arr _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      end end;
    let X := fresh "TIc" in pose proof TI as X;
    destruct X as (_ & _ & MIk & _ & STk & _ & _ & VEPC & _ & _ & _ & _ & _ & _ & _ & _ & IOk & U8k & LBS & _ & _);
    unfold vep_cells in VEPC.


  (* [comment removed for export] *)
  Local Ltac env_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mk _ _ _ =>
      let HE := fresh "HENVk" in let IM := fresh "IMGk" in
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HE;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IM;
      let GLOB := fresh "GLOBk" in let HOBJ := fresh "HOBJk" in
      destruct HE as [GLOB HOBJ];
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let CNT := fresh "CNT" in
      pose proof GLOB as (EBSS & BSS & CP & [c CNT]); cbn [al_segs LayoutP0] in BSS, CP, CNT; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_7; dand3 dR_7 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      let GV := fresh "GVSC" in
      (first [ pose proof (IM) as dR_10; dand4 dR_10 as _ _ GV _ | pose proof IM as (_ & _ & GV & _) ]); unfold GOT_vsc in GV
    end.


  Local Ltac unhide_disj_vimg := try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end.

  (* [comment removed for export] *)
  Local Ltac tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      repeat match goal with Hi : img_ok0 ?mm |- _ => lazymatch mm with m => fail | _ => clear Hi end end;
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & IMGk & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8o & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      assert (TI2 : TINV yi bs Ak mc mdk vvk e);
      [ split; [exact EVI'|]; split; [exact (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk)|]; split; [exact MIq|]; split; [exact MDFk|];
        split; [exact STq|]; split; [exact HENV2|];
        split; [eapply img_ok0_munch; [exact MU | | exact IMGk]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside];
                unhide_disj_vimg; revert Ha; geo_lia |];
        split; [unfold vep_cells; lazymatch goal with EVC : v Fvc = _ |- _ => try rewrite EVC end; exact VEPq|];
        split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia] |];
        split; [exact NEBk|]; split; [exact BUDk|]; split; [exact LENk|]; split; [exact SZk|]; split; [exact RELk|]; split; [exact LIVEk|];
        split; [ lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
                   eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
                   [ exact CFk
                   | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
                     eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | clear; lia | clear; lia
                   | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] end |];
        split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia] |];
        split; [eapply u8arr_transport; [exact U8o | exact MU | exact WM |]; rewrite LBS'; cbn; unhide DVBI; revert DVBI BIk; geo_lia |];
        split; [exact LBS'|]; split; [exact NISBk| exact NIBBk]
      | clear AINVk MDFk IMGk SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8o LBS' NISBk NIBBk EVI' LVk LBk LSk DVBk Bk Sk LSIk LBIk SIk BIk CFPk ]
    end end end.





End S.
End V_veifi.


Module V_veibx.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strchr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr.R_memcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg V_veao0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_VS46q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vejx2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veifi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 1.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HFL : 0 <= v Fflags < 16.
  Hypothesis HET : bool01 (v Femptytag).
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis HLM : v Flast_mark = 1.
  Hypothesis HAZ : v Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LayoutP0 A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis SZB : vb_size vv <= vb_len vv + 4096.
  Hypothesis LENB : vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  Let FRAME (c0 : cell) : list cell :=
    [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation TINV := (tinv VEP v tag q vv vi H lo sp m md A).

  Local Ltac unpack_tinv TI :=
    (first [ dand21 TI as EVI AINVk MIk MDFk STk HENVk IMGk VEPC SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & IMGk & VEPC & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0;
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV LS NES) as DVS;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV LB NEB) as DVB;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A VEP = Some 312, LS : a_live A (v Fvsb) = Some 40, LB : a_live A (vb_buf vv) = Some (vb_size vv) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ)) as dR_4; dand11 dR_4 as SI16 SIlo SIhi SIimg BI16 BIlo BIhi BIimg DSBI SImap BImap | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap) ]);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint A m md VEP 312 _ _ AINV VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LBI (not_eq_sym NIBB)) as DBBI
    end.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HFL (conj HET
      (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB (conj SZB (conj LENB (conj LBUD (conj NBUD (conj HVI (conj TP (conj SP16 (conj RA2
      (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)

  #[using="NEB NES SOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)

 

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac normal_tail IH TI FR i :=
    zstep; zstep; zstep; zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; apply rz_stop;
        replace (vb_buf yi + i + 1) with (vb_buf yi + (i + 1)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac entity_tail IH TI FR i w :=
    zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; zstep; apply rz_stop;
        replace (vb_buf yi + i + w) with (vb_buf yi + (i + w)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + w));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac ptr_small G :=
    try (rewrite Z.mod_small in G by
      (lazymatch goal with IR : (0 <= _ <= vb_len ?yi)%Z, VB : (vb_buf ?yi + vb_size ?yi < _)%Z, VL : (0 <= vb_len ?yi < vb_size ?yi)%Z, VZ : (0 < vb_buf ?yi)%Z |- _ =>
         revert IR VB VL VZ; clear; intros; lia end)).

  (* [comment removed for export] *)
  Local Ltac rd_byte U8 ik adr RD :=
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let bq := fresh "bq" in let Hq := fresh "Hq" in
      destruct (nth_error bs (Z.to_nat ik)) as [bq|] eqn:Hq;
      [ pose proof (byte_range bq);
        pose proof (u8arr_read rsegs mx B bs ik bq adr U8 Hq) as RD;
        lazymatch goal with IR : (0 <= _ <= vb_len _)%Z |- _ =>
          specialize (RD ltac:(clear - IR; lia) ltac:(unfold wa; f_equal; clear; lia)) end
      | exfalso; apply nth_error_None in Hq;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert Hq LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end ]
    end.

  (* [comment removed for export] *)
  Local Ltac bcmp_call U8 i w LIT LITAT :=
    zstep;
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let vq := fresh "vq" in let Mq := fresh "Mq" in
      destruct (memcmp_model_total (firstn w (skipn (Z.to_nat i) bs)) LIT w) as [vq Mq];
      [ rewrite firstn_length_le; [clear; lia|]; rewrite skipn_length;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end
      | cbn; clear; lia
      | eapply evt_cut;
        [ eapply bcmp_spec with (ls := firstn w (skipn (Z.to_nat i) bs)) (rs := LIT) (v := vq);
          [ rewrite unsigned_lit by lia;
            first [ apply (u8arr_sub mx B bs i w U8) | replace B with (B + i)%Z at 1 by (clear; lia); apply (u8arr_sub mx B bs i w U8) ];
            lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
              revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
              clear; intros; lia end
          | rewrite unsigned_lit by lia; apply LITAT; assumption
          | rewrite unsigned_lit by lia; exact Mq
          | assumption ]
        | ] ];
      (* [comment removed for export] *)
      let ms := fresh "ms" in let PO := fresh "PO" in let mq := fresh "mq" in
      let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIq" in
      intros ms PO; unfold memcmp_post in PO; destruct_exs PO;
      (first [ dand6 PO as E MUc WMc MIc _ _ | destruct PO as (E & MUc & WMc & MIc & _ & _) ]); subst ms;
      lazymatch type of MUc with munch [] mx ?mq =>
        lazymatch goal with TI : TINV _ bs _ mx _ _ _, FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MIo : mem_inv _ mx |- _ =>
          eapply (rw_cells_transport rsegs [] mx mq) in FR; [| exact MUc | exact WMc | exact I];
          try (lazymatch goal with VEPC : rw_cells _ mx VEP _ |- _ =>
                 eapply (rw_cells_transport rsegs [] mx mq) in VEPC; [| exact MUc | exact WMc | exact I] end);
          eapply (stk_transport_disjoint rsegs [] mx mq) in STq; [| exact MUc | exact WMc | exact I];
          eapply (u8arr_transport rsegs [] mx mq) in U8; [| exact MUc | exact WMc | exact I];
          let TI' := fresh "TI" in
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ [] mq _ TI MUc WMc MIc (or_introl eq_refl) STq FR eq_refl) as TI';
          clear TI MUc WMc MIo; rename TI' into TI;
          repeat match goal with Hx : rw_cells _ mx _ _ |- _ => clear Hx | Hx : ov_read_bytes _ mx _ _ = _ |- _ => clear Hx end
        end
      end;
      try (lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end)
    end.

  (* [comment removed for export] *)
  Local Ltac ent4_block IH TI FR U8 i G4 :=
    lazymatch goal with E0 : (0 <= ?e)%Z, BUD : (?e + _ + 1 <= _)%Z, IR : (0 <= i <= _)%Z, MEAS : (_ - i <= Z.of_nat _)%Z,
                        NUL : nth_error _ (Z.to_nat _) = Some (Z_to_bv 8 0), IL : (i < _)%Z |- _ =>
    lazymatch type of U8 with u8arr _ _ ?B _ =>
      (* [comment removed for export] *)
      let RD := fresh "RD" in
      rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
      rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
      rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
      rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
      do 6 zstep;
      let E1 := fresh "E1" in
      zstep; if_cases E1;
      [ (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 4;
        [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
      | clear E1;
        rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
        rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
        rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
        rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
        do 6 zstep;
        let E2 := fresh "E2" in
        zstep; if_cases E2;
        [ (* [comment removed for export] *) do 2 zstep; entity_tail IH TI FR i 4;
          [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
        | clear E2;
          (* [comment removed for export] *)
          let G5 := fresh "G5" in
          zstep; zstep; if_cases G5; zify_cond G5; ptr_small G5;
          [ (* [comment removed for export] *)
            normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
          | zstep; zstep; zstep;
            bcmp_call U8 i 5%nat LIT_amp lit_amp_at;
            let Q3 := fresh "Q3" in
            zstep; if_cases Q3;
            [ (* [comment removed for export] *)
              normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
            | (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 5;
              [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G5; lia | clear - BUD G5; lia | clear - MEAS G5; lia | exact NUL] ] ] ] ]
    end end.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma seg_loop : forall (n : nat) (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e i : Z),
    TINV yi bs Ak mk mdk vvk e ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME (C8 (Z_to_bv 64 (VEP + 280)))) ->
    0 <= e -> 0 <= i <= vb_len yi -> e + (vb_len yi - i) + 1 <= vb_len yi + 8 -> vb_len yi - i <= Z.of_nat n ->
    nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    (Z_to_bv 64 (vb_buf yi + i)) (Z_to_bv 64 0x10899) (Z_to_bv 64 0x11925) (Z_to_bv 64 0x1264a) (Z_to_bv 64 0x110c0)
                                    xs7 (Z_to_bv 64 (vb_buf yi + vb_len yi)) (Z_to_bv 64 38) (Z_to_bv 64 0x3b746c26) (Z_to_bv 64 0x3b746726)
                                    xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b4dc) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    induction n as [|n IH]; intros until i; intros TI FR E0 IR BUD MEAS NUL.
    { (* [comment removed for export] *)
      pose proof TI as TI0. unpack_tinv TI0. prelims. clear VEPC0.
      pose proof (as_lazy_nil _ _ _ AINVk) as [MDLk MDHk].
      pose proof (proj1 (proj2 IOBJk)) as VINVI. pose proof (proj1 VINVI) as VszI. pose proof (proj1 (proj2 VINVI)) as VlenI.
      assert (EI : i = vb_len yi) by (clear - IR MEAS; lia).
      pose proof (u8arr_read rsegs mk (vb_buf yi) bs i (Z_to_bv 8 0) (Z_to_bv 64 (vb_buf yi + i)) U8k ltac:(rewrite EI; exact NUL) ltac:(clear - IR; lia) eq_refl) as RD.
      hide_disj. hide_slow.
      apply rz_go; [exact MDHk | exact MDLk |].
      zstep. clear RD. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1. lia. }
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
      apply rz_stop. eapply ((@seg_end _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | exact E0 | clear - BUD IR; lia]. }
    pose proof TI as TI0. unpack_tinv TI0. prelims. clear VEPC0.
    pose proof (as_lazy_nil _ _ _ AINVk) as [MDLk MDHk].
    pose proof (proj1 (proj2 IOBJk)) as VINVI. pose proof (proj1 VINVI) as VszI. pose proof (proj1 (proj2 VINVI)) as VlenI.
    (first [ pose proof (VINVI) as dR_6; dand8 dR_6 as _ _ _ _ _ Vb0I Vb47I _ | pose proof VINVI as (_ & _ & _ & _ & _ & Vb0I & Vb47I & _) ]).
    pose proof (u8arr_bound _ _ _ _ U8k) as U8B.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hb; [| apply nth_error_None in Hb; exfalso; clear - Hb IR LBS VlenI; lia].
    pose proof (byte_range b) as RBb.
    pose proof (u8arr_read rsegs mk (vb_buf yi) bs i b (Z_to_bv 64 (vb_buf yi + i)) U8k Hb ltac:(clear - IR; lia) eq_refl) as RD.
    unfold vep_cells in VEPC.
    hide_disj. hide_slow.
    apply rz_go; [exact MDHk | exact MDLk |].
    (* [comment removed for export] *)
    zstep. clear RD.
    zstep. if_cases KA; zify_cond KA.
    - (* [comment removed for export] *)
      assert (IL : i < vb_len yi).
      { destruct (Z.eq_dec i (vb_len yi)) as [E|NE]; [| clear - NE IR; lia].
        exfalso. rewrite E, NUL in Hb. injection Hb as Eb. rewrite <- Eb in KA. change (bv_unsigned (Z_to_bv 8 0)) with 0 in KA. clear - KA. lia. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases G6; zify_cond G6; ptr_small G6.
      all: cycle 1.
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        bcmp_call U8k i 6%nat LIT_apos lit_apos_at.
        zstep. if_cases Q1; zify_cond Q1.
        { (* [comment removed for export] *) zstep. zstep. zstep. entity_tail IH TI FR i 6;
            [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G6; lia | clear - BUD G6; lia | clear - MEAS G6; lia | exact NUL]. }
        zstep. zstep. zstep.
        bcmp_call U8k i 6%nat LIT_quot lit_quot_at.
        zstep. if_cases Q2; zify_cond Q2.
        { (* [comment removed for export] *) zstep. zstep. zstep. entity_tail IH TI FR i 6;
            [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G6; lia | clear - BUD G6; lia | clear - MEAS G6; lia | exact NUL]. }
        (* [comment removed for export] *)
        zstep. zstep. if_cases G4; zify_cond G4; ptr_small G4. { exfalso. clear - G4 G6. lia. }
        ent4_block IH TI FR U8k i G4.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases G4; zify_cond G4; ptr_small G4.
        * (* [comment removed for export] *)
          zstep. zstep. if_cases G5; zify_cond G5; ptr_small G5. 2:{ exfalso. clear - G4 G5. lia. }
          normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL].
        * ent4_block IH TI FR U8k i G4.
    - zstep. if_cases KZ; zify_cond KZ.
      + (* [comment removed for export] *)
        apply rz_stop. eapply ((@seg_end _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | exact E0 | clear - BUD IR; lia].
      + (* [comment removed for export] *)
        assert (IL : i < vb_len yi).
        { destruct (Z.eq_dec i (vb_len yi)) as [E|NE]; [| clear - NE IR; lia].
          exfalso. rewrite E, NUL in Hb. injection Hb as Eb. rewrite <- Eb in KZ. apply KZ. reflexivity. }
        normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL].
  Qed.


  (* [comment removed for export] *)
  Local Ltac printf_c_site TI FR BUDTAC :=
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | BUDTAC | clear; lia | reflexivity | ];
      [ lazymatch goal with E0 : (0 <= e)%Z |- _ => exact E0 | _ => clear; lia end
      | clear TI FR;
        repeat match goal with Hx : rw_cells _ mk _ _ |- _ => clear Hx | Hx : stk _ mk _ _ |- _ => clear Hx | Hx : mem_inv _ mk |- _ => clear Hx
                             | Hx : u8arr _ mk _ _ |- _ => clear Hx | Hx : munch _ _ mk |- _ => clear Hx | Hx : wmono _ _ mk |- _ => clear Hx end;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR; cbv beta delta [FRAME] in FR;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2; clear MDL2 MDH2 ]
    end.

  (* [comment removed for export] *)
  Local Ltac tinv_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mx _ _ _ =>
      repeat match goal with
      | Hx : vsb_obj _ _ ?my (v Finclude_src) _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : Z.of_nat (length _) = vb_size _ |- _ => clear Hx
      | Hx : rw_cells _ ?my VEP _ |- _ => clear Hx
      | Hx : mem_inv _ ?my |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : stk _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : u8arr _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      end end;
    let X := fresh "TIc" in pose proof TI as X;
    destruct X as (_ & _ & MIk & _ & STk & _ & _ & VEPC & _ & _ & _ & _ & _ & _ & _ & _ & IOk & U8k & LBS & _ & _);
    unfold vep_cells in VEPC.


  (* [comment removed for export] *)
  Local Ltac env_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mk _ _ _ =>
      let HE := fresh "HENVk" in let IM := fresh "IMGk" in
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HE;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IM;
      let GLOB := fresh "GLOBk" in let HOBJ := fresh "HOBJk" in
      destruct HE as [GLOB HOBJ];
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let CNT := fresh "CNT" in
      pose proof GLOB as (EBSS & BSS & CP & [c CNT]); cbn [al_segs LayoutP0] in BSS, CP, CNT; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_7; dand3 dR_7 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      let GV := fresh "GVSC" in
      (first [ pose proof (IM) as dR_10; dand4 dR_10 as _ _ GV _ | pose proof IM as (_ & _ & GV & _) ]); unfold GOT_vsc in GV
    end.


  Local Ltac unhide_disj_vimg := try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end.

  (* [comment removed for export] *)
  Local Ltac tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      repeat match goal with Hi : img_ok0 ?mm |- _ => lazymatch mm with m => fail | _ => clear Hi end end;
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & IMGk & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8o & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      assert (TI2 : TINV yi bs Ak mc mdk vvk e);
      [ split; [exact EVI'|]; split; [exact (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk)|]; split; [exact MIq|]; split; [exact MDFk|];
        split; [exact STq|]; split; [exact HENV2|];
        split; [eapply img_ok0_munch; [exact MU | | exact IMGk]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside];
                unhide_disj_vimg; revert Ha; geo_lia |];
        split; [unfold vep_cells; lazymatch goal with EVC : v Fvc = _ |- _ => try rewrite EVC end; exact VEPq|];
        split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia] |];
        split; [exact NEBk|]; split; [exact BUDk|]; split; [exact LENk|]; split; [exact SZk|]; split; [exact RELk|]; split; [exact LIVEk|];
        split; [ lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
                   eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
                   [ exact CFk
                   | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
                     eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | clear; lia | clear; lia
                   | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] end |];
        split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia] |];
        split; [eapply u8arr_transport; [exact U8o | exact MU | exact WM |]; rewrite LBS'; cbn; unhide DVBI; revert DVBI BIk; geo_lia |];
        split; [exact LBS'|]; split; [exact NISBk| exact NIBBk]
      | clear AINVk MDFk IMGk SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8o LBS' NISBk NIBBk EVI' LVk LBk LSk DVBk Bk Sk LSIk LBIk SIk BIk CFPk ]
    end end end.





End S.
End V_veibx.


Module V_vea4z.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strchr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr.R_memcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg V_veao0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_VS46q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vejx2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veifi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veibx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 1.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HFL : 0 <= v Fflags < 16.
  Hypothesis HET : bool01 (v Femptytag).
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis HLM : v Flast_mark = 1.
  Hypothesis HAZ : v Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LayoutP0 A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis SZB : vb_size vv <= vb_len vv + 4096.
  Hypothesis LENB : vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  Let FRAME (c0 : cell) : list cell :=
    [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation TINV := (tinv VEP v tag q vv vi H lo sp m md A).

  Local Ltac unpack_tinv TI :=
    (first [ dand21 TI as EVI AINVk MIk MDFk STk HENVk IMGk VEPC SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & IMGk & VEPC & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0;
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV LS NES) as DVS;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV LB NEB) as DVB;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A VEP = Some 312, LS : a_live A (v Fvsb) = Some 40, LB : a_live A (vb_buf vv) = Some (vb_size vv) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ)) as dR_4; dand11 dR_4 as SI16 SIlo SIhi SIimg BI16 BIlo BIhi BIimg DSBI SImap BImap | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap) ]);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint A m md VEP 312 _ _ AINV VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LBI (not_eq_sym NIBB)) as DBBI
    end.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HFL (conj HET
      (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB (conj SZB (conj LENB (conj LBUD (conj NBUD (conj HVI (conj TP (conj SP16 (conj RA2
      (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)

  #[using="NEB NES SOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)

 

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac normal_tail IH TI FR i :=
    zstep; zstep; zstep; zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; apply rz_stop;
        replace (vb_buf yi + i + 1) with (vb_buf yi + (i + 1)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac entity_tail IH TI FR i w :=
    zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; zstep; apply rz_stop;
        replace (vb_buf yi + i + w) with (vb_buf yi + (i + w)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + w));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac ptr_small G :=
    try (rewrite Z.mod_small in G by
      (lazymatch goal with IR : (0 <= _ <= vb_len ?yi)%Z, VB : (vb_buf ?yi + vb_size ?yi < _)%Z, VL : (0 <= vb_len ?yi < vb_size ?yi)%Z, VZ : (0 < vb_buf ?yi)%Z |- _ =>
         revert IR VB VL VZ; clear; intros; lia end)).

  (* [comment removed for export] *)
  Local Ltac rd_byte U8 ik adr RD :=
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let bq := fresh "bq" in let Hq := fresh "Hq" in
      destruct (nth_error bs (Z.to_nat ik)) as [bq|] eqn:Hq;
      [ pose proof (byte_range bq);
        pose proof (u8arr_read rsegs mx B bs ik bq adr U8 Hq) as RD;
        lazymatch goal with IR : (0 <= _ <= vb_len _)%Z |- _ =>
          specialize (RD ltac:(clear - IR; lia) ltac:(unfold wa; f_equal; clear; lia)) end
      | exfalso; apply nth_error_None in Hq;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert Hq LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end ]
    end.

  (* [comment removed for export] *)
  Local Ltac bcmp_call U8 i w LIT LITAT :=
    zstep;
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let vq := fresh "vq" in let Mq := fresh "Mq" in
      destruct (memcmp_model_total (firstn w (skipn (Z.to_nat i) bs)) LIT w) as [vq Mq];
      [ rewrite firstn_length_le; [clear; lia|]; rewrite skipn_length;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end
      | cbn; clear; lia
      | eapply evt_cut;
        [ eapply bcmp_spec with (ls := firstn w (skipn (Z.to_nat i) bs)) (rs := LIT) (v := vq);
          [ rewrite unsigned_lit by lia;
            first [ apply (u8arr_sub mx B bs i w U8) | replace B with (B + i)%Z at 1 by (clear; lia); apply (u8arr_sub mx B bs i w U8) ];
            lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
              revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
              clear; intros; lia end
          | rewrite unsigned_lit by lia; apply LITAT; assumption
          | rewrite unsigned_lit by lia; exact Mq
          | assumption ]
        | ] ];
      (* [comment removed for export] *)
      let ms := fresh "ms" in let PO := fresh "PO" in let mq := fresh "mq" in
      let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIq" in
      intros ms PO; unfold memcmp_post in PO; destruct_exs PO;
      (first [ dand6 PO as E MUc WMc MIc _ _ | destruct PO as (E & MUc & WMc & MIc & _ & _) ]); subst ms;
      lazymatch type of MUc with munch [] mx ?mq =>
        lazymatch goal with TI : TINV _ bs _ mx _ _ _, FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MIo : mem_inv _ mx |- _ =>
          eapply (rw_cells_transport rsegs [] mx mq) in FR; [| exact MUc | exact WMc | exact I];
          try (lazymatch goal with VEPC : rw_cells _ mx VEP _ |- _ =>
                 eapply (rw_cells_transport rsegs [] mx mq) in VEPC; [| exact MUc | exact WMc | exact I] end);
          eapply (stk_transport_disjoint rsegs [] mx mq) in STq; [| exact MUc | exact WMc | exact I];
          eapply (u8arr_transport rsegs [] mx mq) in U8; [| exact MUc | exact WMc | exact I];
          let TI' := fresh "TI" in
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ [] mq _ TI MUc WMc MIc (or_introl eq_refl) STq FR eq_refl) as TI';
          clear TI MUc WMc MIo; rename TI' into TI;
          repeat match goal with Hx : rw_cells _ mx _ _ |- _ => clear Hx | Hx : ov_read_bytes _ mx _ _ = _ |- _ => clear Hx end
        end
      end;
      try (lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end)
    end.

  (* [comment removed for export] *)
  Local Ltac ent4_block IH TI FR U8 i G4 :=
    lazymatch goal with E0 : (0 <= ?e)%Z, BUD : (?e + _ + 1 <= _)%Z, IR : (0 <= i <= _)%Z, MEAS : (_ - i <= Z.of_nat _)%Z,
                        NUL : nth_error _ (Z.to_nat _) = Some (Z_to_bv 8 0), IL : (i < _)%Z |- _ =>
    lazymatch type of U8 with u8arr _ _ ?B _ =>
      (* [comment removed for export] *)
      let RD := fresh "RD" in
      rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
      rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
      rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
      rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
      do 6 zstep;
      let E1 := fresh "E1" in
      zstep; if_cases E1;
      [ (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 4;
        [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
      | clear E1;
        rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
        rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
        rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
        rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
        do 6 zstep;
        let E2 := fresh "E2" in
        zstep; if_cases E2;
        [ (* [comment removed for export] *) do 2 zstep; entity_tail IH TI FR i 4;
          [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
        | clear E2;
          (* [comment removed for export] *)
          let G5 := fresh "G5" in
          zstep; zstep; if_cases G5; zify_cond G5; ptr_small G5;
          [ (* [comment removed for export] *)
            normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
          | zstep; zstep; zstep;
            bcmp_call U8 i 5%nat LIT_amp lit_amp_at;
            let Q3 := fresh "Q3" in
            zstep; if_cases Q3;
            [ (* [comment removed for export] *)
              normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
            | (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 5;
              [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G5; lia | clear - BUD G5; lia | clear - MEAS G5; lia | exact NUL] ] ] ] ]
    end end.


  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma seg_mid : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e i0 : Z),
    TINV yi bs Ak mk mdk vvk e ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME (C8 (Z_to_bv 64 (VEP + 280)))) ->
    0 <= e -> 0 <= i0 <= vb_len yi -> e + (vb_len yi - i0) + 1 <= vb_len yi + 8 ->
    nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    (Z_to_bv 64 (vb_buf yi + i0)) (Z_to_bv 64 (vb_len yi)) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b49c) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until i0. intros TI FR E0 IR BUD NUL.
    pose proof TI as TI0. unpack_tinv TI0. prelims. clear VEPC0. yi_facts EVI. cbv beta delta [FRAME] in FR.
    pose proof (as_lazy_nil _ _ _ AINVk) as [MDLk MDHk].
    pose proof (proj1 (proj2 IOBJk)) as VINVI. pose proof (proj1 VINVI) as VszI. pose proof (proj1 (proj2 VINVI)) as VlenI.
    pose proof IOBJk as IO. vsb_open IO. clear VBUF.
    (first [ pose proof ((as_live_ok Ak mk mdk _ _ AINVk VLS)) as dR_6; dand5 dR_6 as _ _ SIklo SIkhi _ | pose proof (as_live_ok Ak mk mdk _ _ AINVk VLS) as (_ & _ & SIklo & SIkhi & _) ]).
    unfold vep_cells in VEPC.
    pose proof (munch_refl [(bv_unsigned sp + -112 - 32, bv_unsigned sp + -112)] mk) as MU. pose proof (wmono_refl rsegs mk) as WM.
    hide_disj. hide_slow.
    apply rz_go; [exact MDHk | exact MDLk |].
    (* [comment removed for export] *)
    zstep. zstep.
    call_fr (VSB_data_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk (v Finclude_src) yi lo) by
      (idtac; [> reflexivity | exact VSBC | exact VINV | exact SIklo | exact SIkhi
              | rewrite unsigned_lit by lia; exact STk | rewrite unsigned_lit by lia; clear - LO; lia | exact CEIL
              | rewrite unsigned_lit by lia; clear - SPH G3; lia | exact MIk ]).
    lazymatch goal with S : stk _ ?mq lo _, MIq : mem_inv _ ?mq |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ _ mq _ TI MU WM MIq ltac:(right; eexists _, _; split; [reflexivity| clear; lia]) S FR eq_refl) as TI1;
      rename S into STq end.
    clear TI VSBC VLS VLB VNE MU WM.
    (* [comment removed for export] *)
    do 14 zstep.
    apply rz_stop.
    eapply ((@seg_loop _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) (Z.to_nat (vb_len yi - i0)) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i0);
      [ exact TI1 | exact FR | exact E0 | exact IR | exact BUD | clear - IR; lia | exact NUL ].
  Qed.

  (* [comment removed for export] *)
  Local Ltac printf_c_site TI FR BUDTAC :=
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | BUDTAC | clear; lia | reflexivity | ];
      [ lazymatch goal with E0 : (0 <= e)%Z |- _ => exact E0 | _ => clear; lia end
      | clear TI FR;
        repeat match goal with Hx : rw_cells _ mk _ _ |- _ => clear Hx | Hx : stk _ mk _ _ |- _ => clear Hx | Hx : mem_inv _ mk |- _ => clear Hx
                             | Hx : u8arr _ mk _ _ |- _ => clear Hx | Hx : munch _ _ mk |- _ => clear Hx | Hx : wmono _ _ mk |- _ => clear Hx end;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR; cbv beta delta [FRAME] in FR;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2; clear MDL2 MDH2 ]
    end.

  (* [comment removed for export] *)
  Local Ltac tinv_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mx _ _ _ =>
      repeat match goal with
      | Hx : vsb_obj _ _ ?my (v Finclude_src) _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : Z.of_nat (length _) = vb_size _ |- _ => clear Hx
      | Hx : rw_cells _ ?my VEP _ |- _ => clear Hx
      | Hx : mem_inv _ ?my |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : stk _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : u8arr _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      end end;
    let X := fresh "TIc" in pose proof TI as X;
    destruct X as (_ & _ & MIk & _ & STk & _ & _ & VEPC & _ & _ & _ & _ & _ & _ & _ & _ & IOk & U8k & LBS & _ & _);
    unfold vep_cells in VEPC.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma seg_pfx : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (incl : Z) (j : list byte),
    TINV yi bs Ak mk mdk vvk 0 ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME (CB 8 j)) ->
    0 <= incl < 256 ->
    nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl) xs5 (Z_to_bv 64 (VEP + 280)) xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b378) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until j. intros TI FR INCL NUL.
    prelims. clear VEPC0. pose proof (proj1 TI) as EVI. yi_facts EVI.
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_7; dand8 dR_7 as VszI VlenI _ _ _ Vb0I Vb47I _ | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & _) ]).
    tinv_open TI. cbv beta delta [FRAME] in FR.
    pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDLk MDHk].
    destruct (nth_error bs 0) as [b0|] eqn:Hb0; [| apply nth_error_None in Hb0; exfalso; clear - Hb0 LBS VszI; lia].
    pose proof (byte_range b0) as RB0.
    pose proof (u8arr_read rsegs mk (vb_buf yi) bs 0 b0 (Z_to_bv 64 (vb_buf yi)) U8k Hb0 ltac:(clear; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD.
    hide_disj. hide_slow.
    apply rz_go; [exact MDHk | exact MDLk |].
    (* [comment removed for export] *)
    zstep. clear RD. zstep. zstep. zstep. zstep. zstep. zstep.
    printf_c_site TI FR ltac:(clear - VlenI; lia).
    tinv_open TI.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    printf_c_site TI FR ltac:(clear - VlenI; lia).
    tinv_open TI.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -104)] mx) as MU2; pose proof (wmono_refl rsegs mx) as WM2 end.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of MU2 with munch _ ?mo mx =>
        pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ _ mx _ TI MU2 WM2 MIk ltac:(right; eexists _, _; split; [reflexivity| clear; lia]) STk FR eq_refl) as TI3;
        clear TI MU2 WM2; repeat match goal with Hx : rw_cells _ mo _ _ |- _ => clear Hx | Hx : u8arr _ mo _ _ |- _ => clear Hx end
      end end.
    rename TI3 into TI. tinv_open TI. rewrite EURL in VEPC.
    (* [comment removed for export] *)
    zstep. if_cases KS; zify_cond KS.
    - (* [comment removed for export] *)
      apply rz_stop. replace (Z_to_bv 64 (vb_buf yi)) with (Z_to_bv 64 (vb_buf yi + 0)) by (f_equal; clear; lia).
      eapply (seg_mid yi bs); [exact TI | exact FR | clear; lia | clear - VlenI; lia | clear - VlenI; lia | exact NUL].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      zstep. if_cases U1; zify_cond U1. 2:{ exfalso. clear - U1. lia. } clear U1.
      zstep. zstep. zstep. zstep.
      zstep. if_cases U2; zify_cond U2. { exfalso. clear - U2. lia. } clear U2.
      zstep. if_cases U3; zify_cond U3. 2:{ exfalso. clear - U3. lia. } clear U3.
      zstep. if_cases U4; zify_cond U4. 2:{ exfalso. clear - U4. lia. } clear U4.
      zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      lazymatch type of TI with TINV _ _ ?Ak3 ?m3 ?md3 ?vv3 ?e3 =>
        eapply ((@printf_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) FMT_PFX 6 2 PRE_PFX OUT_PFX eq_refl HOUT_PFX pc1_pfx pc2_pfx yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                   A_fmtpfx 67947 [] 1 _ Ak3 m3 md3 vv3 e3);
        [ exact TI | exact FR | reflexivity | apply fmt_pfx_at; exact MIk | unfold IMG_LO, A_fmtpfx; clear; lia | unfold RO_TOP, A_fmtpfx; clear; lia
        | exists (Z_to_bv 64 0); split; [reflexivity|]; split; [reflexivity|];
          let SZ0 := fresh "SZ0" in assert (SZ0 : sint32 (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity);
          unfold str_arg_ok, memchr_ok; rewrite SZ0; unfold INT_MAX; clear; cbv; intuition congruence
        | apply bytes_at_nil; clear; lia | left; unfold IMG_LO, RO_TOP; cbn; clear; lia
        | vm_compute; reflexivity | clear; lia | clear - VlenI; lia | clear; lia | reflexivity | ] end.
      clear TI FR. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR. cbv beta delta [FRAME] in FR.
      pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL4 MDH4]. rz_resume MDH4 MDL4.
      (* [comment removed for export] *)
      zstep. apply rz_stop. replace (Z_to_bv 64 (vb_buf yi)) with (Z_to_bv 64 (vb_buf yi + 0)) by (f_equal; clear; lia).
      eapply (seg_mid yi bs); [exact TI | exact FR | clear; lia | clear - VlenI; lia | clear - VlenI; lia | exact NUL].
  Qed.

  (* [comment removed for export] *)
  Local Ltac env_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mk _ _ _ =>
      let HE := fresh "HENVk" in let IM := fresh "IMGk" in
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HE;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IM;
      let GLOB := fresh "GLOBk" in let HOBJ := fresh "HOBJk" in
      destruct HE as [GLOB HOBJ];
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let CNT := fresh "CNT" in
      pose proof GLOB as (EBSS & BSS & CP & [c CNT]); cbn [al_segs LayoutP0] in BSS, CP, CNT; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_8; dand3 dR_8 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      let GV := fresh "GVSC" in
      (first [ pose proof (IM) as dR_11; dand4 dR_11 as _ _ GV _ | pose proof IM as (_ & _ & GV & _) ]); unfold GOT_vsc in GV
    end.


  Local Ltac unhide_disj_vimg := try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end.

  (* [comment removed for export] *)
  Local Ltac tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      repeat match goal with Hi : img_ok0 ?mm |- _ => lazymatch mm with m => fail | _ => clear Hi end end;
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & IMGk & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8o & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      assert (TI2 : TINV yi bs Ak mc mdk vvk e);
      [ split; [exact EVI'|]; split; [exact (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk)|]; split; [exact MIq|]; split; [exact MDFk|];
        split; [exact STq|]; split; [exact HENV2|];
        split; [eapply img_ok0_munch; [exact MU | | exact IMGk]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside];
                unhide_disj_vimg; revert Ha; geo_lia |];
        split; [unfold vep_cells; lazymatch goal with EVC : v Fvc = _ |- _ => try rewrite EVC end; exact VEPq|];
        split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia] |];
        split; [exact NEBk|]; split; [exact BUDk|]; split; [exact LENk|]; split; [exact SZk|]; split; [exact RELk|]; split; [exact LIVEk|];
        split; [ lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
                   eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
                   [ exact CFk
                   | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
                     eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | clear; lia | clear; lia
                   | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] end |];
        split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia] |];
        split; [eapply u8arr_transport; [exact U8o | exact MU | exact WM |]; rewrite LBS'; cbn; unhide DVBI; revert DVBI BIk; geo_lia |];
        split; [exact LBS'|]; split; [exact NISBk| exact NIBBk]
      | clear AINVk MDFk IMGk SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8o LBS' NISBk NIBBk EVI' LVk LBk LSk DVBk Bk Sk LSIk LBIk SIk BIk CFPk ]
    end end end.





End S.
End V_vea4z.


Module V_ved28.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strchr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr.R_memcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg V_veao0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_VS46q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vejx2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veifi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veibx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vea4z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 1.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HFL : 0 <= v Fflags < 16.
  Hypothesis HET : bool01 (v Femptytag).
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis HLM : v Flast_mark = 1.
  Hypothesis HAZ : v Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LayoutP0 A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis SZB : vb_size vv <= vb_len vv + 4096.
  Hypothesis LENB : vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  Let FRAME (c0 : cell) : list cell :=
    [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation TINV := (tinv VEP v tag q vv vi H lo sp m md A).

  Local Ltac unpack_tinv TI :=
    (first [ dand21 TI as EVI AINVk MIk MDFk STk HENVk IMGk VEPC SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & IMGk & VEPC & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0;
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV LS NES) as DVS;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV LB NEB) as DVB;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A VEP = Some 312, LS : a_live A (v Fvsb) = Some 40, LB : a_live A (vb_buf vv) = Some (vb_size vv) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ)) as dR_4; dand11 dR_4 as SI16 SIlo SIhi SIimg BI16 BIlo BIhi BIimg DSBI SImap BImap | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap) ]);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint A m md VEP 312 _ _ AINV VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LBI (not_eq_sym NIBB)) as DBBI
    end.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HFL (conj HET
      (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB (conj SZB (conj LENB (conj LBUD (conj NBUD (conj HVI (conj TP (conj SP16 (conj RA2
      (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)

  #[using="NEB NES SOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)

 

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac normal_tail IH TI FR i :=
    zstep; zstep; zstep; zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; apply rz_stop;
        replace (vb_buf yi + i + 1) with (vb_buf yi + (i + 1)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac entity_tail IH TI FR i w :=
    zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; zstep; apply rz_stop;
        replace (vb_buf yi + i + w) with (vb_buf yi + (i + w)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + w));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac ptr_small G :=
    try (rewrite Z.mod_small in G by
      (lazymatch goal with IR : (0 <= _ <= vb_len ?yi)%Z, VB : (vb_buf ?yi + vb_size ?yi < _)%Z, VL : (0 <= vb_len ?yi < vb_size ?yi)%Z, VZ : (0 < vb_buf ?yi)%Z |- _ =>
         revert IR VB VL VZ; clear; intros; lia end)).

  (* [comment removed for export] *)
  Local Ltac rd_byte U8 ik adr RD :=
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let bq := fresh "bq" in let Hq := fresh "Hq" in
      destruct (nth_error bs (Z.to_nat ik)) as [bq|] eqn:Hq;
      [ pose proof (byte_range bq);
        pose proof (u8arr_read rsegs mx B bs ik bq adr U8 Hq) as RD;
        lazymatch goal with IR : (0 <= _ <= vb_len _)%Z |- _ =>
          specialize (RD ltac:(clear - IR; lia) ltac:(unfold wa; f_equal; clear; lia)) end
      | exfalso; apply nth_error_None in Hq;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert Hq LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end ]
    end.

  (* [comment removed for export] *)
  Local Ltac bcmp_call U8 i w LIT LITAT :=
    zstep;
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let vq := fresh "vq" in let Mq := fresh "Mq" in
      destruct (memcmp_model_total (firstn w (skipn (Z.to_nat i) bs)) LIT w) as [vq Mq];
      [ rewrite firstn_length_le; [clear; lia|]; rewrite skipn_length;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end
      | cbn; clear; lia
      | eapply evt_cut;
        [ eapply bcmp_spec with (ls := firstn w (skipn (Z.to_nat i) bs)) (rs := LIT) (v := vq);
          [ rewrite unsigned_lit by lia;
            first [ apply (u8arr_sub mx B bs i w U8) | replace B with (B + i)%Z at 1 by (clear; lia); apply (u8arr_sub mx B bs i w U8) ];
            lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
              revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
              clear; intros; lia end
          | rewrite unsigned_lit by lia; apply LITAT; assumption
          | rewrite unsigned_lit by lia; exact Mq
          | assumption ]
        | ] ];
      (* [comment removed for export] *)
      let ms := fresh "ms" in let PO := fresh "PO" in let mq := fresh "mq" in
      let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIq" in
      intros ms PO; unfold memcmp_post in PO; destruct_exs PO;
      (first [ dand6 PO as E MUc WMc MIc _ _ | destruct PO as (E & MUc & WMc & MIc & _ & _) ]); subst ms;
      lazymatch type of MUc with munch [] mx ?mq =>
        lazymatch goal with TI : TINV _ bs _ mx _ _ _, FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MIo : mem_inv _ mx |- _ =>
          eapply (rw_cells_transport rsegs [] mx mq) in FR; [| exact MUc | exact WMc | exact I];
          try (lazymatch goal with VEPC : rw_cells _ mx VEP _ |- _ =>
                 eapply (rw_cells_transport rsegs [] mx mq) in VEPC; [| exact MUc | exact WMc | exact I] end);
          eapply (stk_transport_disjoint rsegs [] mx mq) in STq; [| exact MUc | exact WMc | exact I];
          eapply (u8arr_transport rsegs [] mx mq) in U8; [| exact MUc | exact WMc | exact I];
          let TI' := fresh "TI" in
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ [] mq _ TI MUc WMc MIc (or_introl eq_refl) STq FR eq_refl) as TI';
          clear TI MUc WMc MIo; rename TI' into TI;
          repeat match goal with Hx : rw_cells _ mx _ _ |- _ => clear Hx | Hx : ov_read_bytes _ mx _ _ = _ |- _ => clear Hx end
        end
      end;
      try (lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end)
    end.

  (* [comment removed for export] *)
  Local Ltac ent4_block IH TI FR U8 i G4 :=
    lazymatch goal with E0 : (0 <= ?e)%Z, BUD : (?e + _ + 1 <= _)%Z, IR : (0 <= i <= _)%Z, MEAS : (_ - i <= Z.of_nat _)%Z,
                        NUL : nth_error _ (Z.to_nat _) = Some (Z_to_bv 8 0), IL : (i < _)%Z |- _ =>
    lazymatch type of U8 with u8arr _ _ ?B _ =>
      (* [comment removed for export] *)
      let RD := fresh "RD" in
      rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
      rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
      rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
      rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
      do 6 zstep;
      let E1 := fresh "E1" in
      zstep; if_cases E1;
      [ (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 4;
        [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
      | clear E1;
        rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
        rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
        rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
        rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
        do 6 zstep;
        let E2 := fresh "E2" in
        zstep; if_cases E2;
        [ (* [comment removed for export] *) do 2 zstep; entity_tail IH TI FR i 4;
          [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
        | clear E2;
          (* [comment removed for export] *)
          let G5 := fresh "G5" in
          zstep; zstep; if_cases G5; zify_cond G5; ptr_small G5;
          [ (* [comment removed for export] *)
            normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
          | zstep; zstep; zstep;
            bcmp_call U8 i 5%nat LIT_amp lit_amp_at;
            let Q3 := fresh "Q3" in
            zstep; if_cases Q3;
            [ (* [comment removed for export] *)
              normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
            | (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 5;
              [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G5; lia | clear - BUD G5; lia | clear - MEAS G5; lia | exact NUL] ] ] ] ]
    end end.



  (* [comment removed for export] *)
  Local Ltac printf_c_site TI FR BUDTAC :=
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | BUDTAC | clear; lia | reflexivity | ];
      [ lazymatch goal with E0 : (0 <= e)%Z |- _ => exact E0 | _ => clear; lia end
      | clear TI FR;
        repeat match goal with Hx : rw_cells _ mk _ _ |- _ => clear Hx | Hx : stk _ mk _ _ |- _ => clear Hx | Hx : mem_inv _ mk |- _ => clear Hx
                             | Hx : u8arr _ mk _ _ |- _ => clear Hx | Hx : munch _ _ mk |- _ => clear Hx | Hx : wmono _ _ mk |- _ => clear Hx end;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR; cbv beta delta [FRAME] in FR;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2; clear MDL2 MDH2 ]
    end.

  (* [comment removed for export] *)
  Local Ltac tinv_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mx _ _ _ =>
      repeat match goal with
      | Hx : vsb_obj _ _ ?my (v Finclude_src) _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : Z.of_nat (length _) = vb_size _ |- _ => clear Hx
      | Hx : rw_cells _ ?my VEP _ |- _ => clear Hx
      | Hx : mem_inv _ ?my |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : stk _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : u8arr _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      end end;
    let X := fresh "TIc" in pose proof TI as X;
    destruct X as (_ & _ & MIk & _ & STk & _ & _ & VEPC & _ & _ & _ & _ & _ & _ & _ & _ & IOk & U8k & LBS & _ & _);
    unfold vep_cells in VEPC.


  (* [comment removed for export] *)
  Local Ltac env_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mk _ _ _ =>
      let HE := fresh "HENVk" in let IM := fresh "IMGk" in
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HE;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IM;
      let GLOB := fresh "GLOBk" in let HOBJ := fresh "HOBJk" in
      destruct HE as [GLOB HOBJ];
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let CNT := fresh "CNT" in
      pose proof GLOB as (EBSS & BSS & CP & [c CNT]); cbn [al_segs LayoutP0] in BSS, CP, CNT; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_6; dand3 dR_6 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      let GV := fresh "GVSC" in
      (first [ pose proof (IM) as dR_9; dand4 dR_9 as _ _ GV _ | pose proof IM as (_ & _ & GV & _) ]); unfold GOT_vsc in GV
    end.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma seg_err_tail : forall (yi : vsb_rec)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z) (j0 : list byte),
    vi = Some yi ->
    ainv Ak mk mdk -> mem_inv rsegs mk -> md_frame md mdk -> stk rsegs mk lo (bv_unsigned sp + -112) ->
    henv_ok LayoutP0 VI0 H mk ->
    rw_cells rsegs mk VEP (vep_cells (fupd v Fstate (vi_st VI0 S_TagError)) tag q) ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME (CB 8 j0)) ->
    vsb_obj LayoutP0 Ak mk (v Fvsb) vvk false -> VEP <> vb_buf vvk ->
    vb_len vv <= vb_len vvk <= vb_len vv + e -> 0 <= e <= vb_len yi + 8 ->
    vb_size vv <= vb_size vvk <= Z.max (vb_size vv) (vb_len vvk + 4096) ->
    (vb_buf vvk = vb_buf vv \/ (a_live A (vb_buf vvk) = None /\ a_live Ak (vb_buf vv) = None)) ->
    (forall r, r <> vb_buf vv -> r <> vb_buf vvk -> a_live Ak r = a_live A r) ->
    (a_livebytes Ak = a_livebytes A + vb_size vvk - vb_size vv /\ a_nlive Ak = a_nlive A) ->   (* [comment removed for export] *)
    cframe LayoutP0 (owned A) (owned Ak) (bv_unsigned sp) 8544
           (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                     \/ vsb_blocks (v Finclude_src) yi a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
           (blk (vb_buf vvk) (vb_size vvk)) m mk ->
    vsb_obj LayoutP0 Ak mk (v Finclude_src) yi true -> v Finclude_src <> vb_buf vvk -> vb_buf yi <> vb_buf vvk ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 (Z_to_bv 64 (VEP + 280)) xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b824) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until j0. intros EVI AINVk MIk MDFk STk HENVk VEPC FR SOBJk NEBk LENk EB SZk RELk LIVEk BUDk CFk IOBJk NISBk NIBBk.
    prelims. clear VEPC0. yi_facts EVI. cbv beta delta [FRAME] in FR. unfold vep_cells in VEPC.
    pose proof (as_lazy_nil _ _ _ AINVk) as [MDLk MDHk].
    pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk. pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk.
    pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk. pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk.
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    pose proof (as_live_disjoint Ak mk mdk VEP 312 (vb_buf vvk) (vb_size vvk) AINVk LVk LBk NEBk) as DVBk.
    hide_disj. hide_slow.
    apply rz_go; [exact MDHk | exact MDLk |].
    (* [comment removed for export] *)
    do 17 zstep.
    try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    apply rz_stop.
    release_frame FR STk (bv_unsigned sp).
    vep_split3 VEPC 45%nat VEPa VEPp VEPb.
    pose proof (crange_block (L:=LayoutP0) Ak mk mdk VEP 312 VEP 280 AINVk LVk ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as CRa.
    pose proof (crange_block (L:=LayoutP0) Ak mk mdk VEP 312 (VEP + 288) 24 AINVk LVk ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as CRb.
    unfold VSB_destroy_entry.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk mdk Ak (VEP + 280) (v Finclude_src) yi true lo);
      [ exact AINVk | exact MIk | reflexivity | cbn [w64]; exact VEPp
      | right; exists VEP, 312; split; [exact LVk|]; split; [unhide NIS; unhide NIB; intros [X|[X|[]]]; [exact (NIS X)| exact (NIB X)] | clear; lia]
      | exact IOBJk | exact TP | unhide SP16; exact SP16 | unhide RA2; exact RA2 | exact STk | exact CEIL
      | unfold DESTROY_STACK, FREE_STACK; clear - LO; lia | clear - SPH G3; lia | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A3 m3 md3 AINV3 MI3 MDF3 ST3 PSC3 LVS3 LVB3 LIVE3 LBd3 NLd3 CF3.
    unfold DESTROY_STACK, FREE_STACK in CF3.
    assert (HC2 : hcover Ak [] (fun a => blk (v Finclude_src) 40 a \/ blk (vb_buf yi) (vb_size yi) a \/ VEP + 280 <= a < VEP + 280 + 8))
      by (hcover_destroy LSIk LBIk LVk).
    pose proof (henv_call H Ak A3 mk m3 mdk (bv_unsigned sp) _ _ _ [] AINVk CF3 HG ltac:(clear - CEIL LO; lia) SPH HC2 HENVk) as HENV3.
    assert (LV3 : a_live A3 VEP = Some 312) by (unhide NIS; unhide NIB; rewrite (LIVE3 VEP (not_eq_sym NIS) (not_eq_sym NIB)); exact LVk).
    assert (LS3 : a_live A3 (v Fvsb) = Some 40) by (unhide NISS; unhide NIBS; rewrite (LIVE3 _ (not_eq_sym NISS) (not_eq_sym NIBS)); exact LSk).
    assert (LB3 : a_live A3 (vb_buf vvk) = Some (vb_size vvk)) by (unhide NISBk; unhide NIBBk; rewrite (LIVE3 _ (not_eq_sym NISBk) (not_eq_sym NIBBk)); exact LBk).
    assert (SOBJ3 : vsb_obj LayoutP0 A3 m3 (v Fvsb) vvk false).
    { eapply (vsb_obj_call H Ak A3 mk m3 mdk (bv_unsigned sp) _ _ _ [v Fvsb; vb_buf vvk] AINVk CF3 HG ltac:(clear - CEIL LO; lia) (v Fvsb) vvk false);
        [ | left; reflexivity | right; left; reflexivity | exact LS3 | exact LB3 | exact SOBJk ].
      intros a Ha. left. revert a Ha. hcover_destroy LSIk LBIk LVk. }
    xfer_piece CF3 VEPa CRa. xfer_piece CF3 VEPb CRb.
    cbn [w64] in PSC3. vep_join3 VEPa PSC3 VEPb VEPC3.
    unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A3 m3 md3 (fupd (fupd v Fstate (vi_st VI0 S_TagError)) Finclude_src 0) vvk);
      [ exact AINV3 | exact MI3 | exact (md_frame_trans _ _ _ MDFk MDF3) | exact ST3 | exact HENV3
      | | | right; reflexivity | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact HIC | reflexivity | exact SOBJ3
      | rewrite EVI; clear - LENk EB; lia | clear - SZk; lia | | rewrite EVI | rewrite EVI ].
    - split; [exact LV3|]. split; [| split; [exact TAG| exact PADS]].
      cbn [al_segs LayoutP0]. unfold vep_cells. cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. unfold vep_cells in VEPC3. cbn [fupd vf_beq vf_index N.eqb Pos.eqb] in VEPC3. exact VEPC3.
    - apply vkeep_fupd; [apply vkeep_fupd; [apply vkeep_refl| in_tac]| in_tac].
    - destruct RELk as [R|[R1 R2]]; [left; exact R| right]. split; [exact R1|].
      rewrite (LIVE3 _ (not_eq_sym NISB) (not_eq_sym NIBB)). exact R2.
    - split; [exact LVS3|]. split; [exact LVB3|].
      split; [intros rr R1 R2 R3 R4; rewrite (LIVE3 rr R3 R4); exact (LIVEk rr R1 R2)|].
      revert BUDk LBd3 NLd3; clear; intros; lia.
    - eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8208 8544 _ _ _ _ _ _ m mk m3);
        [ exact CFk | exact CF3 | clear; lia | clear; lia
        | eapply (stk_mapped (L:=LayoutP0)); [exact ST3 | exact CEIL | clear -LO; lia | clear; lia]
        | intros a X; exact X
        | intros a [X|[X|X]]; right; [right; right; right; left; left; exact X | right; right; right; left; right; exact X | left; split; [clear -Vlo; lia| clear -X; lia]]
        | intros a X; left; exact X ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac henv_rebuild MU WM CNT HENV2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch goal with GLOBk : glob_ok _ _ H mk, HOBJk : hobj_ok _ _ H mk |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT2" in
      (first [ pose proof (GLOBk) as dR_10; dand4 dR_10 as EBSS BSS CP _ | pose proof GLOBk as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP;
      destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
      assert (HENV2 : henv_ok LayoutP0 VI0 H mc);
      [ split;
        [ eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact C];
          [ eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS; cbn; geo_lia]
          | eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; unfold h_cp; geo_lia] ]
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJk | exact MU | exact WM |];
          let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; revert Ha; geo_lia ]
      | clear BSS CP C c EBSS ]
    end end.

  Local Ltac to_err_tail TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & _ & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & _ & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      let AINV2 := fresh "AINV2" in pose proof (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk) as AINV2;
      let SOBJ2 := fresh "SOBJ2" in
      assert (SOBJ2 : vsb_obj LayoutP0 Ak mc (v Fvsb) vvk false);
      [ eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn;
        [ unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia ] |];
      let IOBJ2 := fresh "IOBJ2" in
      assert (IOBJ2 : vsb_obj LayoutP0 Ak mc (v Finclude_src) yi true);
      [ eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn;
        [ unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia ] |];
      let CF2 := fresh "CF2" in
      lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
        assert (CF2 : cframe LayoutP0 (owned A) (owned Ak) (bv_unsigned sp) 8544 VT NT m mc);
        [ eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
          [ exact CFk
          | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
            eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
              [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
          | clear; lia | clear; lia
          | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
              [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
          | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] |]
      end;
      unhide_neqs;
        eapply (seg_err_tail yi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mc mdk vvk e);
        [ exact EVI' | exact AINV2 | exact MIq | exact MDFk | exact STq | exact HENV2
        | unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VI0 st0];
          lazymatch goal with EVC : v Fvc = _, HAZ : v Fattr_vsb = 0 |- _ => rewrite EVC, HAZ end; exact VEPq
        | exact FRq | exact SOBJ2 | exact NEBk | exact LENk
        | lazymatch goal with VL : (0 <= vb_len yi < _)%Z |- _ => revert VL LENk; clear; intros; lia end
        | exact SZk | exact RELk | exact LIVEk | exact BUDk | exact CF2
        | exact IOBJ2 | exact NISBk | exact NIBBk ]
    end end end.

  (* [comment removed for export] *)
  #[using="W K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma seg_http : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (incl : Z) (j : list byte),
    TINV yi bs Ak mk mdk vvk 0 ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME (CB 8 j)) ->
    0 <= incl < 256 -> 8 <= vb_len yi ->
    nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl) xs5 (Z_to_bv 64 (VEP + 280)) xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b450) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until j. intros TI FR INCL L8 NUL.
    prelims. clear VEPC0. pose proof (proj1 TI) as EVI. yi_facts EVI.
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_15; dand8 dR_15 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    tinv_open TI. cbv beta delta [FRAME] in FR.
    pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDLk MDHk].
    (* [comment removed for export] *)
    assert (NUL7 : nth_error (skipn 7 bs) (Z.to_nat (vb_len yi) - 7) = Some (Z_to_bv 8 0)).
    { rewrite nth_error_skipn. replace (7 + (Z.to_nat (vb_len yi) - 7))%nat with (Z.to_nat (vb_len yi)) by (clear - L8; lia). exact NUL. }
    (first [ pose proof ((cstr_split (skipn 7 bs) _ NUL7)) as dR_16; dex1 dR_16 as z; dand5 dR_16 as ZLE SPLIT NONUL FZ LZ | pose proof ((cstr_split (skipn 7 bs) _ NUL7)) as dR_16; dand6 dR_16 as z ZLE SPLIT NONUL FZ LZ | destruct (cstr_split (skipn 7 bs) _ NUL7) as (z & ZLE & SPLIT & NONUL & FZ & LZ) ]).
    pose proof (u8arr_suffix mk (vb_buf yi) bs 7 U8k ltac:(clear; lia) ltac:(clear - LBS VlenI L8; lia)) as STR.
    change (Z.to_nat 7) with 7%nat in STR. rewrite SPLIT in STR.
    assert (LREST : length (skipn 7 bs) = (length bs - 7)%nat) by (rewrite skipn_length; reflexivity).
    assert (LSL : Z.of_nat (length (skipn (S z) (skipn 7 bs))) = vb_size yi - 8 - Z.of_nat z).
    { rewrite skipn_length, LREST. clear - LBS ZLE VlenI L8. lia. }
    pose proof (munch_refl [(bv_unsigned sp + -112 - 32, bv_unsigned sp + -112)] mk) as MU. pose proof (wmono_refl rsegs mk) as WM.
    hide_disj. hide_slow.
    apply rz_go; [exact MDHk | exact MDLk |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    call_fr (strchr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk (firstn z (skipn 7 bs)) (skipn (S z) (skipn 7 bs)) lo) by
      (idtac; [> rewrite unsigned_lit by lia; exact STk
              | rewrite unsigned_lit by lia; exact STR
              | exact NONUL
              | rewrite unsigned_lit by lia; rewrite LZ, LSL; unhide VbmI; clear - VbmI ZLE VlenI L8 LBS; lia
              | exact MIk
              | rewrite unsigned_lit by lia; clear - LO; lia
              | rewrite !unsigned_lit by lia; rewrite LZ, LSL; left;
                lazymatch goal with BIhi : (vb_buf yi + vb_size yi <= alloc_ceiling)%Z |- _ => clear - BIhi CEIL LO ZLE; lia end ]).
    lazymatch goal with S : stk _ ?mq lo _, MIq : mem_inv _ ?mq |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ _ mq _ TI MU WM MIq ltac:(right; eexists _, _; split; [reflexivity| clear; lia]) S FR eq_refl) as TI1;
      rename S into STq; clear TI MU WM; rename TI1 into TI end.
    repeat match goal with Hb : bytes_at _ _ (vb_buf yi + 7) _ |- _ => clear Hb end.
    tinv_open TI.
    pose proof (u8arr_suffix _ (vb_buf yi) bs 7 U8k ltac:(clear; lia) ltac:(clear - LBS VlenI L8; lia)) as STR.
    change (Z.to_nat 7) with 7%nat in STR. rewrite SPLIT in STR.
    unfold strchr_val. change (47 mod 256 =? 0) with false. cbv iota. change (47 mod 256) with 47. unfold strchr_res.
    destruct (find_byte 47 (firstn z (skipn 7 bs))) as [jx|] eqn:FJ.
    - (* [comment removed for export] *)
      (first [ pose proof ((find_byte_Some _ _ _ FJ)) as dR_17; dand3 dR_17 as JLT _ _ | destruct (find_byte_Some _ _ _ FJ) as (JLT & _ & _) ]). rewrite LZ in JLT.
      (* [comment removed for export] *)
      zstep. if_cases KQ; zify_cond KQ.
      { exfalso. revert KQ Vb0I Vb47I JLT ZLE VlenI. clear; intros; lia. }
      clear KQ.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -104)] mx) as MU2; pose proof (wmono_refl rsegs mx) as WM2 end.
      zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch type of MU2 with munch _ ?mo mx =>
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ _ mx _ TI MU2 WM2 MIk ltac:(right; eexists _, _; split; [reflexivity| clear; lia]) STk FR eq_refl) as TI3;
          clear TI MU2 WM2; repeat match goal with Hx : rw_cells _ mo _ _ |- _ => clear Hx | Hx : u8arr _ mo _ _ |- _ => clear Hx | Hx : bytes_at _ mo _ _ |- _ => clear Hx end
        end end.
      rename TI3 into TI. tinv_open TI.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      printf_c_site TI FR ltac:(clear - VlenI; lia).
      tinv_open TI.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      replace (vb_buf yi + 7 + Z.of_nat jx - (vb_buf yi + 7)) with (Z.of_nat jx) by (clear; lia).
      rewrite (swrap32_id (Z.of_nat jx)) by (revert JLT ZLE VlenI LENB Vlen0; rewrite EVI; clear; intros; lia).
      destruct (host_arg_ok (firstn z (skipn 7 bs)) jx (vb_buf yi + 7) NONUL ltac:(rewrite LZ; exact JLT) ltac:(clear - Vb0I; lia)
                  ltac:(revert JLT ZLE VlenI LENB Vlen0; rewrite EVI; clear; intros; lia)) as [HARG HOUTL].
      assert (HSB : bytes_at rsegs mk' (vb_buf yi + 7) (firstn (S jx) (firstn z (skipn 7 bs)))).
      { pose proof (u8arr_suffix _ (vb_buf yi) bs 7 U8k ltac:(clear; lia) ltac:(clear - LBS VlenI L8; lia)) as STR'.
        change (Z.to_nat 7) with 7%nat in STR'. rewrite SPLIT in STR'.
        rewrite <- (firstn_skipn (S jx) (firstn z (skipn 7 bs))) in STR'. rewrite <- app_assoc in STR'.
        apply bytes_at_prefix in STR'. exact STR'. }
      assert (HSL : length (firstn (S jx) (firstn z (skipn 7 bs))) = S jx) by (apply firstn_length_le; rewrite LZ; clear - JLT; lia).
      apply rz_stop.
      lazymatch type of TI with TINV _ _ ?Ak3 ?m3 ?md3 ?vv3 ?e3 =>
        eapply ((@printf_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) FMT_HOST 13 3 PRE_HOST OUT_HOST eq_refl HOUT_HOST pc1_host pc2_host yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                   A_fmthost (vb_buf yi + 7) (firstn (S jx) (firstn z (skipn 7 bs))) (7 + Z.of_nat jx) _ Ak3 m3 md3 vv3 e3);
        [ exact TI | exact FR | reflexivity | apply fmt_host_at; exact MIk | unfold IMG_LO, A_fmthost; clear; lia | unfold RO_TOP, A_fmthost; clear; lia
        | eexists _, _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact HARG]
        | exact HSB
        | right; rewrite HSL; split; [clear; lia|]; split; [revert JLT ZLE VlenI LBS L8; clear; intros; lia|];
          let E := fresh "E" in intros E; apply (f_equal (@length byte)) in E; rewrite HSL in E; discriminate E
        | unfold OUT_HOST; cbn [nth_error]; rewrite !length_app, Nat2Z.inj_add, Nat2Z.inj_add, HOUTL; unfold TXT_HOST, out_c; cbn [length]; clear; lia
        | clear; lia | clear - JLT ZLE VlenI L8; lia | clear; lia | reflexivity | ] end.
      clear TI FR. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR. cbv beta delta [FRAME] in FR.
      replace (vb_buf yi + 7 + Z.of_nat jx) with (vb_buf yi + (7 + Z.of_nat jx)) by (clear; lia).
      eapply ((@seg_mid _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | clear; lia | clear - JLT ZLE VlenI L8; lia | clear - JLT ZLE VlenI L8; lia | exact NUL].
    - (* [comment removed for export] *)
      zstep. if_cases KQ; zify_cond KQ. 2:{ exfalso. apply KQ. reflexivity. } clear KQ.
      (* [comment removed for export] *)
      env_open TI. rewrite EVC in VEPC.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (munch_refl W mx) as MU; cbv delta [W] in MU; pose proof (wmono_refl rsegs mx) as WM end.
      do 15 zstep.
      zstep. carve_frame 48%nat STk. do 8 zstep.
      lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ => release_frame FR2 STk (bv_unsigned sp + -112)%Z end.
      clear BSS GVSC CP VC WK U8k. try clear STR.
      (* [comment removed for export] *)
      rewrite HAZ in VEPC.
      zstep. zstep. zstep. zstep.
      zstep. if_cases KZ; zify_cond KZ. 2:{ exfalso. apply KZ. reflexivity. } clear KZ.
      apply rz_stop.
      henv_rebuild MU WM CNT HENV2. to_err_tail TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI.
  Qed.

  Local Ltac unhide_disj_vimg := try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end.

  (* [comment removed for export] *)
  Local Ltac tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      repeat match goal with Hi : img_ok0 ?mm |- _ => lazymatch mm with m => fail | _ => clear Hi end end;
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & IMGk & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8o & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      assert (TI2 : TINV yi bs Ak mc mdk vvk e);
      [ split; [exact EVI'|]; split; [exact (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk)|]; split; [exact MIq|]; split; [exact MDFk|];
        split; [exact STq|]; split; [exact HENV2|];
        split; [eapply img_ok0_munch; [exact MU | | exact IMGk]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside];
                unhide_disj_vimg; revert Ha; geo_lia |];
        split; [unfold vep_cells; lazymatch goal with EVC : v Fvc = _ |- _ => try rewrite EVC end; exact VEPq|];
        split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia] |];
        split; [exact NEBk|]; split; [exact BUDk|]; split; [exact LENk|]; split; [exact SZk|]; split; [exact RELk|]; split; [exact LIVEk|];
        split; [ lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
                   eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
                   [ exact CFk
                   | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
                     eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | clear; lia | clear; lia
                   | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] end |];
        split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia] |];
        split; [eapply u8arr_transport; [exact U8o | exact MU | exact WM |]; rewrite LBS'; cbn; unhide DVBI; revert DVBI BIk; geo_lia |];
        split; [exact LBS'|]; split; [exact NISBk| exact NIBBk]
      | clear AINVk MDFk IMGk SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8o LBS' NISBk NIBBk EVI' LVk LBk LSk DVBk Bk Sk LSIk LBIk SIk BIk CFPk ]
    end end end.





End S.
End V_ved28.


Module V_vencr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strchr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr.R_memcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg V_veao0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_VS46q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vejx2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veifi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veibx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vea4z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_ved28.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 1.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HFL : 0 <= v Fflags < 16.
  Hypothesis HET : bool01 (v Femptytag).
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis HLM : v Flast_mark = 1.
  Hypothesis HAZ : v Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LayoutP0 A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis SZB : vb_size vv <= vb_len vv + 4096.
  Hypothesis LENB : vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  Let FRAME (c0 : cell) : list cell :=
    [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation TINV := (tinv VEP v tag q vv vi H lo sp m md A).

  Local Ltac unpack_tinv TI :=
    (first [ dand21 TI as EVI AINVk MIk MDFk STk HENVk IMGk VEPC SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & IMGk & VEPC & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0;
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV LS NES) as DVS;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV LB NEB) as DVB;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A VEP = Some 312, LS : a_live A (v Fvsb) = Some 40, LB : a_live A (vb_buf vv) = Some (vb_size vv) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ)) as dR_4; dand11 dR_4 as SI16 SIlo SIhi SIimg BI16 BIlo BIhi BIimg DSBI SImap BImap | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap) ]);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint A m md VEP 312 _ _ AINV VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LBI (not_eq_sym NIBB)) as DBBI
    end.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HFL (conj HET
      (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB (conj SZB (conj LENB (conj LBUD (conj NBUD (conj HVI (conj TP (conj SP16 (conj RA2
      (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)

  #[using="NEB NES SOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)

 

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac normal_tail IH TI FR i :=
    zstep; zstep; zstep; zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; apply rz_stop;
        replace (vb_buf yi + i + 1) with (vb_buf yi + (i + 1)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac entity_tail IH TI FR i w :=
    zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; zstep; apply rz_stop;
        replace (vb_buf yi + i + w) with (vb_buf yi + (i + w)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + w));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac ptr_small G :=
    try (rewrite Z.mod_small in G by
      (lazymatch goal with IR : (0 <= _ <= vb_len ?yi)%Z, VB : (vb_buf ?yi + vb_size ?yi < _)%Z, VL : (0 <= vb_len ?yi < vb_size ?yi)%Z, VZ : (0 < vb_buf ?yi)%Z |- _ =>
         revert IR VB VL VZ; clear; intros; lia end)).

  (* [comment removed for export] *)
  Local Ltac rd_byte U8 ik adr RD :=
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let bq := fresh "bq" in let Hq := fresh "Hq" in
      destruct (nth_error bs (Z.to_nat ik)) as [bq|] eqn:Hq;
      [ pose proof (byte_range bq);
        pose proof (u8arr_read rsegs mx B bs ik bq adr U8 Hq) as RD;
        lazymatch goal with IR : (0 <= _ <= vb_len _)%Z |- _ =>
          specialize (RD ltac:(clear - IR; lia) ltac:(unfold wa; f_equal; clear; lia)) end
      | exfalso; apply nth_error_None in Hq;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert Hq LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end ]
    end.

  (* [comment removed for export] *)
  Local Ltac bcmp_call U8 i w LIT LITAT :=
    zstep;
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let vq := fresh "vq" in let Mq := fresh "Mq" in
      destruct (memcmp_model_total (firstn w (skipn (Z.to_nat i) bs)) LIT w) as [vq Mq];
      [ rewrite firstn_length_le; [clear; lia|]; rewrite skipn_length;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end
      | cbn; clear; lia
      | eapply evt_cut;
        [ eapply bcmp_spec with (ls := firstn w (skipn (Z.to_nat i) bs)) (rs := LIT) (v := vq);
          [ rewrite unsigned_lit by lia;
            first [ apply (u8arr_sub mx B bs i w U8) | replace B with (B + i)%Z at 1 by (clear; lia); apply (u8arr_sub mx B bs i w U8) ];
            lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
              revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
              clear; intros; lia end
          | rewrite unsigned_lit by lia; apply LITAT; assumption
          | rewrite unsigned_lit by lia; exact Mq
          | assumption ]
        | ] ];
      (* [comment removed for export] *)
      let ms := fresh "ms" in let PO := fresh "PO" in let mq := fresh "mq" in
      let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIq" in
      intros ms PO; unfold memcmp_post in PO; destruct_exs PO;
      (first [ dand6 PO as E MUc WMc MIc _ _ | destruct PO as (E & MUc & WMc & MIc & _ & _) ]); subst ms;
      lazymatch type of MUc with munch [] mx ?mq =>
        lazymatch goal with TI : TINV _ bs _ mx _ _ _, FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MIo : mem_inv _ mx |- _ =>
          eapply (rw_cells_transport rsegs [] mx mq) in FR; [| exact MUc | exact WMc | exact I];
          try (lazymatch goal with VEPC : rw_cells _ mx VEP _ |- _ =>
                 eapply (rw_cells_transport rsegs [] mx mq) in VEPC; [| exact MUc | exact WMc | exact I] end);
          eapply (stk_transport_disjoint rsegs [] mx mq) in STq; [| exact MUc | exact WMc | exact I];
          eapply (u8arr_transport rsegs [] mx mq) in U8; [| exact MUc | exact WMc | exact I];
          let TI' := fresh "TI" in
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ [] mq _ TI MUc WMc MIc (or_introl eq_refl) STq FR eq_refl) as TI';
          clear TI MUc WMc MIo; rename TI' into TI;
          repeat match goal with Hx : rw_cells _ mx _ _ |- _ => clear Hx | Hx : ov_read_bytes _ mx _ _ = _ |- _ => clear Hx end
        end
      end;
      try (lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end)
    end.

  (* [comment removed for export] *)
  Local Ltac ent4_block IH TI FR U8 i G4 :=
    lazymatch goal with E0 : (0 <= ?e)%Z, BUD : (?e + _ + 1 <= _)%Z, IR : (0 <= i <= _)%Z, MEAS : (_ - i <= Z.of_nat _)%Z,
                        NUL : nth_error _ (Z.to_nat _) = Some (Z_to_bv 8 0), IL : (i < _)%Z |- _ =>
    lazymatch type of U8 with u8arr _ _ ?B _ =>
      (* [comment removed for export] *)
      let RD := fresh "RD" in
      rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
      rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
      rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
      rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
      do 6 zstep;
      let E1 := fresh "E1" in
      zstep; if_cases E1;
      [ (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 4;
        [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
      | clear E1;
        rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
        rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
        rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
        rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
        do 6 zstep;
        let E2 := fresh "E2" in
        zstep; if_cases E2;
        [ (* [comment removed for export] *) do 2 zstep; entity_tail IH TI FR i 4;
          [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
        | clear E2;
          (* [comment removed for export] *)
          let G5 := fresh "G5" in
          zstep; zstep; if_cases G5; zify_cond G5; ptr_small G5;
          [ (* [comment removed for export] *)
            normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
          | zstep; zstep; zstep;
            bcmp_call U8 i 5%nat LIT_amp lit_amp_at;
            let Q3 := fresh "Q3" in
            zstep; if_cases Q3;
            [ (* [comment removed for export] *)
              normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
            | (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 5;
              [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G5; lia | clear - BUD G5; lia | clear - MEAS G5; lia | exact NUL] ] ] ] ]
    end end.



  (* [comment removed for export] *)
  Local Ltac printf_c_site TI FR BUDTAC :=
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | BUDTAC | clear; lia | reflexivity | ];
      [ lazymatch goal with E0 : (0 <= e)%Z |- _ => exact E0 | _ => clear; lia end
      | clear TI FR;
        repeat match goal with Hx : rw_cells _ mk _ _ |- _ => clear Hx | Hx : stk _ mk _ _ |- _ => clear Hx | Hx : mem_inv _ mk |- _ => clear Hx
                             | Hx : u8arr _ mk _ _ |- _ => clear Hx | Hx : munch _ _ mk |- _ => clear Hx | Hx : wmono _ _ mk |- _ => clear Hx end;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR; cbv beta delta [FRAME] in FR;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2; clear MDL2 MDH2 ]
    end.

  (* [comment removed for export] *)
  Local Ltac tinv_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mx _ _ _ =>
      repeat match goal with
      | Hx : vsb_obj _ _ ?my (v Finclude_src) _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : Z.of_nat (length _) = vb_size _ |- _ => clear Hx
      | Hx : rw_cells _ ?my VEP _ |- _ => clear Hx
      | Hx : mem_inv _ ?my |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : stk _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : u8arr _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      end end;
    let X := fresh "TIc" in pose proof TI as X;
    destruct X as (_ & _ & MIk & _ & STk & _ & _ & VEPC & _ & _ & _ & _ & _ & _ & _ & _ & IOk & U8k & LBS & _ & _);
    unfold vep_cells in VEPC.


  (* [comment removed for export] *)
  Local Ltac env_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mk _ _ _ =>
      let HE := fresh "HENVk" in let IM := fresh "IMGk" in
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HE;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IM;
      let GLOB := fresh "GLOBk" in let HOBJ := fresh "HOBJk" in
      destruct HE as [GLOB HOBJ];
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let CNT := fresh "CNT" in
      pose proof GLOB as (EBSS & BSS & CP & [c CNT]); cbn [al_segs LayoutP0] in BSS, CP, CNT; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_6; dand3 dR_6 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      let GV := fresh "GVSC" in
      (first [ pose proof (IM) as dR_9; dand4 dR_9 as _ _ GV _ | pose proof IM as (_ & _ & GV & _) ]); unfold GOT_vsc in GV
    end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac henv_rebuild MU WM CNT HENV2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch goal with GLOBk : glob_ok _ _ H mk, HOBJk : hobj_ok _ _ H mk |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT2" in
      (first [ pose proof (GLOBk) as dR_10; dand4 dR_10 as EBSS BSS CP _ | pose proof GLOBk as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP;
      destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
      assert (HENV2 : henv_ok LayoutP0 VI0 H mc);
      [ split;
        [ eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact C];
          [ eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS; cbn; geo_lia]
          | eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; unfold h_cp; geo_lia] ]
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJk | exact MU | exact WM |];
          let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; revert Ha; geo_lia ]
      | clear BSS CP C c EBSS ]
    end end.

  Local Ltac to_err_tail TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & _ & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & _ & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      let AINV2 := fresh "AINV2" in pose proof (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk) as AINV2;
      let SOBJ2 := fresh "SOBJ2" in
      assert (SOBJ2 : vsb_obj LayoutP0 Ak mc (v Fvsb) vvk false);
      [ eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn;
        [ unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia ] |];
      let IOBJ2 := fresh "IOBJ2" in
      assert (IOBJ2 : vsb_obj LayoutP0 Ak mc (v Finclude_src) yi true);
      [ eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn;
        [ unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia ] |];
      let CF2 := fresh "CF2" in
      lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
        assert (CF2 : cframe LayoutP0 (owned A) (owned Ak) (bv_unsigned sp) 8544 VT NT m mc);
        [ eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
          [ exact CFk
          | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
            eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
              [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
          | clear; lia | clear; lia
          | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
              [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
          | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] |]
      end;
      unhide_neqs;
        eapply ((@seg_err_tail _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mc mdk vvk e);
        [ exact EVI' | exact AINV2 | exact MIq | exact MDFk | exact STq | exact HENV2
        | unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VI0 st0];
          lazymatch goal with EVC : v Fvc = _, HAZ : v Fattr_vsb = 0 |- _ => rewrite EVC, HAZ end; exact VEPq
        | exact FRq | exact SOBJ2 | exact NEBk | exact LENk
        | lazymatch goal with VL : (0 <= vb_len yi < _)%Z |- _ => revert VL LENk; clear; intros; lia end
        | exact SZk | exact RELk | exact LIVEk | exact BUDk | exact CF2
        | exact IOBJ2 | exact NISBk | exact NIBBk ]
    end end end.


  Local Ltac unhide_disj_vimg := try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end.

  (* [comment removed for export] *)
  Local Ltac tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      repeat match goal with Hi : img_ok0 ?mm |- _ => lazymatch mm with m => fail | _ => clear Hi end end;
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & IMGk & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8o & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      assert (TI2 : TINV yi bs Ak mc mdk vvk e);
      [ split; [exact EVI'|]; split; [exact (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk)|]; split; [exact MIq|]; split; [exact MDFk|];
        split; [exact STq|]; split; [exact HENV2|];
        split; [eapply img_ok0_munch; [exact MU | | exact IMGk]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside];
                unhide_disj_vimg; revert Ha; geo_lia |];
        split; [unfold vep_cells; lazymatch goal with EVC : v Fvc = _ |- _ => try rewrite EVC end; exact VEPq|];
        split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia] |];
        split; [exact NEBk|]; split; [exact BUDk|]; split; [exact LENk|]; split; [exact SZk|]; split; [exact RELk|]; split; [exact LIVEk|];
        split; [ lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
                   eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
                   [ exact CFk
                   | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
                     eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | clear; lia | clear; lia
                   | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] end |];
        split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia] |];
        split; [eapply u8arr_transport; [exact U8o | exact MU | exact WM |]; rewrite LBS'; cbn; unhide DVBI; revert DVBI BIk; geo_lia |];
        split; [exact LBS'|]; split; [exact NISBk| exact NIBBk]
      | clear AINVk MDFk IMGk SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8o LBS' NISBk NIBBk EVI' LVk LBk LSk DVBk Bk Sk LSIk LBIk SIk BIk CFPk ]
    end end end.
  (* [comment removed for export] *)
  #[using="W K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma seg_https : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (incl : Z) (j : list byte),
    TINV yi bs Ak mk mdk vvk 0 ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME (CB 8 j)) ->
    0 <= incl < 256 -> 9 <= vb_len yi ->
    nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl) xs5 (Z_to_bv 64 (VEP + 280)) xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b724) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until j. intros TI FR INCL L9 NUL.
    prelims. clear VEPC0. pose proof (proj1 TI) as EVI. yi_facts EVI.
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_19; dand8 dR_19 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    tinv_open TI. cbv beta delta [FRAME] in FR.
    pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDLk MDHk].
    env_open TI. rewrite EVC in VEPC.
    pose proof (rw_cells_read_sub rsegs _ _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF.
    change (Z.to_nat 4) with 4%nat in RDF.
    match type of RDF with _ = Some ?r => let r' := eval cbn in r in change r with r' in RDF end.
    rewrite (unsigned_lit (v Fflags)) in RDF by (clear - HFL; lia).
    pose proof (munch_refl W mk) as MU. cbv delta [W] in MU. pose proof (wmono_refl rsegs mk) as WM.
    clear U8k.
    hide_disj. hide_slow.
    apply rz_go; [exact MDHk | exact MDLk |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. clear RDF. zstep. zstep. zstep. zstep. zstep. zstep.
    clear BSS GVSC CP VC WK.
    zstep. if_cases KF; zify_cond KF.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      do 5 zstep. zstep. carve_frame 48%nat STk. do 8 zstep.
      lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ => release_frame FR2 STk (bv_unsigned sp + -112)%Z end.
      henv_rebuild MU WM CNT HENV2.
      tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2.
      clear TI MU WM HENV2 GLOBk HOBJk CNT. rename TI2 into TI. tinv_open TI.
      (* [comment removed for export] *)
      assert (NUL8 : nth_error (skipn 8 bs) (Z.to_nat (vb_len yi) - 8) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_skipn. replace (8 + (Z.to_nat (vb_len yi) - 8))%nat with (Z.to_nat (vb_len yi)) by (clear - L9; lia). exact NUL. }
      (first [ pose proof ((cstr_split (skipn 8 bs) _ NUL8)) as dR_20; dex1 dR_20 as z; dand5 dR_20 as ZLE SPLIT NONUL FZ LZ | pose proof ((cstr_split (skipn 8 bs) _ NUL8)) as dR_20; dand6 dR_20 as z ZLE SPLIT NONUL FZ LZ | destruct (cstr_split (skipn 8 bs) _ NUL8) as (z & ZLE & SPLIT & NONUL & FZ & LZ) ]).
      assert (LREST : length (skipn 8 bs) = (length bs - 8)%nat) by (rewrite skipn_length; reflexivity).
      assert (LSL : Z.of_nat (length (skipn (S z) (skipn 8 bs))) = vb_size yi - 9 - Z.of_nat z).
      { rewrite skipn_length, LREST. clear - LBS ZLE VlenI L9. lia. }
      pose proof (u8arr_suffix _ (vb_buf yi) bs 8 U8k ltac:(clear; lia) ltac:(clear - LBS VlenI L9; lia)) as STR.
      change (Z.to_nat 8) with 8%nat in STR. rewrite SPLIT in STR.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (munch_refl [(bv_unsigned sp + -112 - 32, bv_unsigned sp + -112)] mx) as MUs;
        pose proof (munch_refl W mx) as MU; cbv delta [W] in MU; pose proof (wmono_refl rsegs mx) as WM end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      call_fr (strchr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (firstn z (skipn 8 bs)) (skipn (S z) (skipn 8 bs)) lo) by
        (idtac; [> rewrite unsigned_lit by lia; exact STk
                | rewrite unsigned_lit by lia; exact STR
                | exact NONUL
                | rewrite unsigned_lit by lia; rewrite LZ, LSL; unhide VbmI; clear - VbmI ZLE VlenI L9 LBS; lia
                | exact MIk
                | rewrite unsigned_lit by lia; clear - LO; lia
                | rewrite !unsigned_lit by lia; rewrite LZ, LSL; left;
                  lazymatch goal with BIhi : (vb_buf yi + vb_size yi <= alloc_ceiling)%Z |- _ => clear - BIhi CEIL LO ZLE; lia end ]).
      lazymatch goal with S : stk _ ?mq lo _, MIq : mem_inv _ ?mq |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename S into STq; rename MIq into MIr end.
      repeat match goal with Hb : bytes_at _ _ (vb_buf yi + 8) _ |- _ => clear Hb end.
      unfold strchr_val. change (47 mod 256 =? 0) with false. cbv iota. change (47 mod 256) with 47. unfold strchr_res.
      destruct (find_byte 47 (firstn z (skipn 8 bs))) as [jx|] eqn:FJ.
      + (* [comment removed for export] *)
        (first [ pose proof ((find_byte_Some _ _ _ FJ)) as dR_21; dand3 dR_21 as JLT _ _ | destruct (find_byte_Some _ _ _ FJ) as (JLT & _ & _) ]). rewrite LZ in JLT.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ _ mq _ TI MUs (ltac:(lazymatch goal with W0 : wmono _ _ mq |- _ => exact W0 end)) MIr
                        ltac:(right; eexists _, _; split; [reflexivity| clear; lia]) STq FR eq_refl) as TI1 end.
        clear TI MUs MU WM. rename TI1 into TI. tinv_open TI.
        zstep. if_cases KQ; zify_cond KQ.
        { exfalso. revert KQ Vb0I Vb47I JLT ZLE VlenI. clear; intros; lia. }
        clear KQ.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -104)] mx) as MU2; pose proof (wmono_refl rsegs mx) as WM2 end.
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          lazymatch type of MU2 with munch _ ?mo mx =>
            pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ _ mx _ TI MU2 WM2 MIk ltac:(right; eexists _, _; split; [reflexivity| clear; lia]) STk FR eq_refl) as TI3;
            clear TI MU2 WM2; repeat match goal with Hx : rw_cells _ mo _ _ |- _ => clear Hx | Hx : u8arr _ mo _ _ |- _ => clear Hx | Hx : bytes_at _ mo _ _ |- _ => clear Hx end
          end end.
        rename TI3 into TI. tinv_open TI.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        printf_c_site TI FR ltac:(clear - VlenI; lia).
        tinv_open TI.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        replace (vb_buf yi + 8 + Z.of_nat jx - (vb_buf yi + 8)) with (Z.of_nat jx) by (clear; lia).
        rewrite (swrap32_id (Z.of_nat jx)) by (revert JLT ZLE VlenI LENB Vlen0; rewrite EVI; clear; intros; lia).
        destruct (host_arg_ok (firstn z (skipn 8 bs)) jx (vb_buf yi + 8) NONUL ltac:(rewrite LZ; exact JLT) ltac:(clear - Vb0I; lia)
                    ltac:(revert JLT ZLE VlenI LENB Vlen0; rewrite EVI; clear; intros; lia)) as [HARG HOUTL].
        assert (HSB : bytes_at rsegs mk' (vb_buf yi + 8) (firstn (S jx) (firstn z (skipn 8 bs)))).
        { pose proof (u8arr_suffix _ (vb_buf yi) bs 8 U8k ltac:(clear; lia) ltac:(clear - LBS VlenI L9; lia)) as STR'.
          change (Z.to_nat 8) with 8%nat in STR'. rewrite SPLIT in STR'.
          rewrite <- (firstn_skipn (S jx) (firstn z (skipn 8 bs))) in STR'. rewrite <- app_assoc in STR'.
          apply bytes_at_prefix in STR'. exact STR'. }
        assert (HSL : length (firstn (S jx) (firstn z (skipn 8 bs))) = S jx) by (apply firstn_length_le; rewrite LZ; clear - JLT; lia).
        apply rz_stop.
        lazymatch type of TI with TINV _ _ ?Ak3 ?m3 ?md3 ?vv3 ?e3 =>
          eapply ((@printf_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) FMT_HOST 13 3 PRE_HOST OUT_HOST eq_refl HOUT_HOST pc1_host pc2_host yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                     A_fmthost (vb_buf yi + 8) (firstn (S jx) (firstn z (skipn 8 bs))) (7 + Z.of_nat jx) _ Ak3 m3 md3 vv3 e3);
          [ exact TI | exact FR | reflexivity | apply fmt_host_at; exact MIk | unfold IMG_LO, A_fmthost; clear; lia | unfold RO_TOP, A_fmthost; clear; lia
          | eexists _, _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact HARG]
          | exact HSB
          | right; rewrite HSL; split; [clear; lia|]; split; [revert JLT ZLE VlenI LBS L9; clear; intros; lia|];
            let E := fresh "E" in intros E; apply (f_equal (@length byte)) in E; rewrite HSL in E; discriminate E
          | unfold OUT_HOST; cbn [nth_error]; rewrite !length_app, Nat2Z.inj_add, Nat2Z.inj_add, HOUTL; unfold TXT_HOST, out_c; cbn [length]; clear; lia
          | clear; lia | clear - JLT ZLE VlenI L9; lia | clear; lia | reflexivity | ] end.
        clear TI FR. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR. cbv beta delta [FRAME] in FR.
        replace (vb_buf yi + 8 + Z.of_nat jx) with (vb_buf yi + (8 + Z.of_nat jx)) by (clear; lia).
        eapply ((@seg_mid _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | clear; lia | clear - JLT ZLE VlenI L9; lia | clear - JLT ZLE VlenI L9; lia | exact NUL].
      + (* [comment removed for export] *)
        zstep. if_cases KQ; zify_cond KQ. 2:{ exfalso. apply KQ. reflexivity. } clear KQ.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HENVk.
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IMGk.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
          eapply (henv_ok_munch LayoutP0) in HENVk; [| exact MUs | lazymatch goal with W0 : wmono _ _ mq |- _ => exact W0 end
            | intros ? Ha; pose proof (proj1 (proj1 HENVk)) as EB; cbn [vi_bss VI0] in EB; rewrite EB in Ha; unfold h_hd, h_wrk, h_req in Ha; cbn [outside]; revert Ha; geo_lia];
          eapply img_ok0_munch in IMGk; [| exact MUs | intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; revert Ha; geo_lia] end.
        clear MUs.
        unhide V16 || idtac.
        call_fr (vep_error_ok VEP v tag q H lo) by
          (idtac; [> reflexivity | exact VEPC | exact TAG | exact PADS | exact EVC | exact HENVk | exact HG | exact IMGk
                  | exact Vlo | lazymatch goal with V16 : VEP mod 16 = 0 |- _ => clear - V16; lia | _ => idtac end | exact Vhi
                  | rewrite unsigned_lit by lia; exact STq | unfold VEPERR_STACK; rewrite unsigned_lit by lia; clear - LO; lia | exact CEIL
                  | rewrite unsigned_lit by lia; clear - SPH; lia | exact MIr ]).
        lazymatch goal with HE : henv_ok _ _ H ?mq, S : stk _ ?mq lo _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
          rename HE into HENVe; rename S into STq;
          pose proof (munch_refl [(VEP, VEP + 312)] mq) as MUe; pose proof (wmono_refl rsegs mq) as WMe end.
        clear HENVk IMGk U8k.
        (* [comment removed for export] *)
        rewrite HAZ in VEPC. rewrite EVC in VEPC.
        zstep. zstep. zstep. zstep.
        zstep. if_cases KZ; zify_cond KZ. { exfalso. apply KZ. reflexivity. } clear KZ.
        apply rz_stop.
        lazymatch type of MUe with munch _ _ ?mq =>
          eapply (henv_ok_munch LayoutP0) in HENVe; [| exact MUe | exact WMe
            | intros ? Ha; pose proof (proj1 (proj1 HENVe)) as EB; cbn [vi_bss VI0] in EB; rewrite EB in Ha; unfold h_hd, h_wrk, h_req in Ha; cbn [outside];
              unhide_disj_vimg; revert Ha; geo_lia ] end.
        clear MUe WMe.
        to_err_tail TI MU WM HENVe LAY ACV G2 G3 Evsc DVS DVSI DVBI.
    - (* [comment removed for export] *)
      do 5 zstep. zstep. carve_frame 48%nat STk. do 8 zstep.
      lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ => release_frame FR2 STk (bv_unsigned sp + -112)%Z end.
      (* [comment removed for export] *)
      rewrite HAZ in VEPC.
      zstep. zstep. zstep. zstep.
      zstep. if_cases KZ; zify_cond KZ. 2:{ exfalso. apply KZ. reflexivity. } clear KZ.
      apply rz_stop.
      henv_rebuild MU WM CNT HENV2. to_err_tail TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI.
  Qed.





End S.
End V_vencr.


Module V_ve32b.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSgtv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_memchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_strchr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSgtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vetlt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_memchr.R_memcmp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strchr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_sn2fc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_pc6ck.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require R_vsqhq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_veobg V_veao0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc.R_snq16 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_sn2fc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck.R_pcgt7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_pc6ck OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcbh7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq.R_pcrlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_vsqhq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_VS46q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veobg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_veao0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vejx2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veifi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veibx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vea4z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_ved28 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vencr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold VEPERR_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 1.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HFL : 0 <= v Fflags < 16.
  Hypothesis HET : bool01 (v Femptytag).
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis HLM : v Flast_mark = 1.
  Hypothesis HAZ : v Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LayoutP0 A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis SZB : vb_size vv <= vb_len vv + 4096.
  Hypothesis LENB : vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  Let FRAME (c0 : cell) : list cell :=
    [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation TINV := (tinv VEP v tag q vv vi H lo sp m md A).

  Local Ltac unpack_tinv TI :=
    (first [ dand21 TI as EVI AINVk MIk MDFk STk HENVk IMGk VEPC SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & IMGk & VEPC & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0;
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV LS NES) as DVS;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV LB NEB) as DVB;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A VEP = Some 312, LS : a_live A (v Fvsb) = Some 40, LB : a_live A (vb_buf vv) = Some (vb_size vv) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ)) as dR_4; dand11 dR_4 as SI16 SIlo SIhi SIimg BI16 BIlo BIhi BIimg DSBI SImap BImap | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap) ]);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint A m md VEP 312 _ _ AINV VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LBI (not_eq_sym NIBB)) as DBBI
    end.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HFL (conj HET
      (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB (conj SZB (conj LENB (conj LBUD (conj NBUD (conj HVI (conj TP (conj SP16 (conj RA2
      (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  #[using="SPH LO CEIL NEB NES SOBJ HG VBASE VOBJ AINV md m ra lo vv q tag v"] Lemma CFP : client_fp LayoutP0 A W.
  Proof.
    prelims. cbn. split; [left; lia|]. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  #[using="NEB NES SOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)

 

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac normal_tail IH TI FR i :=
    zstep; zstep; zstep; zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; apply rz_stop;
        replace (vb_buf yi + i + 1) with (vb_buf yi + (i + 1)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac entity_tail IH TI FR i w :=
    zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; zstep; apply rz_stop;
        replace (vb_buf yi + i + w) with (vb_buf yi + (i + w)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + w));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac ptr_small G :=
    try (rewrite Z.mod_small in G by
      (lazymatch goal with IR : (0 <= _ <= vb_len ?yi)%Z, VB : (vb_buf ?yi + vb_size ?yi < _)%Z, VL : (0 <= vb_len ?yi < vb_size ?yi)%Z, VZ : (0 < vb_buf ?yi)%Z |- _ =>
         revert IR VB VL VZ; clear; intros; lia end)).

  (* [comment removed for export] *)
  Local Ltac rd_byte U8 ik adr RD :=
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let bq := fresh "bq" in let Hq := fresh "Hq" in
      destruct (nth_error bs (Z.to_nat ik)) as [bq|] eqn:Hq;
      [ pose proof (byte_range bq);
        pose proof (u8arr_read rsegs mx B bs ik bq adr U8 Hq) as RD;
        lazymatch goal with IR : (0 <= _ <= vb_len _)%Z |- _ =>
          specialize (RD ltac:(clear - IR; lia) ltac:(unfold wa; f_equal; clear; lia)) end
      | exfalso; apply nth_error_None in Hq;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert Hq LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end ]
    end.

  (* [comment removed for export] *)
  Local Ltac bcmp_call U8 i w LIT LITAT :=
    zstep;
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let vq := fresh "vq" in let Mq := fresh "Mq" in
      destruct (memcmp_model_total (firstn w (skipn (Z.to_nat i) bs)) LIT w) as [vq Mq];
      [ rewrite firstn_length_le; [clear; lia|]; rewrite skipn_length;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end
      | cbn; clear; lia
      | eapply evt_cut;
        [ eapply bcmp_spec with (ls := firstn w (skipn (Z.to_nat i) bs)) (rs := LIT) (v := vq);
          [ rewrite unsigned_lit by lia;
            first [ apply (u8arr_sub mx B bs i w U8) | replace B with (B + i)%Z at 1 by (clear; lia); apply (u8arr_sub mx B bs i w U8) ];
            lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
              revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
              clear; intros; lia end
          | rewrite unsigned_lit by lia; apply LITAT; assumption
          | rewrite unsigned_lit by lia; exact Mq
          | assumption ]
        | ] ];
      (* [comment removed for export] *)
      let ms := fresh "ms" in let PO := fresh "PO" in let mq := fresh "mq" in
      let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIq" in
      intros ms PO; unfold memcmp_post in PO; destruct_exs PO;
      (first [ dand6 PO as E MUc WMc MIc _ _ | destruct PO as (E & MUc & WMc & MIc & _ & _) ]); subst ms;
      lazymatch type of MUc with munch [] mx ?mq =>
        lazymatch goal with TI : TINV _ bs _ mx _ _ _, FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MIo : mem_inv _ mx |- _ =>
          eapply (rw_cells_transport rsegs [] mx mq) in FR; [| exact MUc | exact WMc | exact I];
          try (lazymatch goal with VEPC : rw_cells _ mx VEP _ |- _ =>
                 eapply (rw_cells_transport rsegs [] mx mq) in VEPC; [| exact MUc | exact WMc | exact I] end);
          eapply (stk_transport_disjoint rsegs [] mx mq) in STq; [| exact MUc | exact WMc | exact I];
          eapply (u8arr_transport rsegs [] mx mq) in U8; [| exact MUc | exact WMc | exact I];
          let TI' := fresh "TI" in
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ [] mq _ TI MUc WMc MIc (or_introl eq_refl) STq FR eq_refl) as TI';
          clear TI MUc WMc MIo; rename TI' into TI;
          repeat match goal with Hx : rw_cells _ mx _ _ |- _ => clear Hx | Hx : ov_read_bytes _ mx _ _ = _ |- _ => clear Hx end
        end
      end;
      try (lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end)
    end.

  (* [comment removed for export] *)
  Local Ltac ent4_block IH TI FR U8 i G4 :=
    lazymatch goal with E0 : (0 <= ?e)%Z, BUD : (?e + _ + 1 <= _)%Z, IR : (0 <= i <= _)%Z, MEAS : (_ - i <= Z.of_nat _)%Z,
                        NUL : nth_error _ (Z.to_nat _) = Some (Z_to_bv 8 0), IL : (i < _)%Z |- _ =>
    lazymatch type of U8 with u8arr _ _ ?B _ =>
      (* [comment removed for export] *)
      let RD := fresh "RD" in
      rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
      rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
      rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
      rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
      do 6 zstep;
      let E1 := fresh "E1" in
      zstep; if_cases E1;
      [ (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 4;
        [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
      | clear E1;
        rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
        rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
        rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
        rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
        do 6 zstep;
        let E2 := fresh "E2" in
        zstep; if_cases E2;
        [ (* [comment removed for export] *) do 2 zstep; entity_tail IH TI FR i 4;
          [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
        | clear E2;
          (* [comment removed for export] *)
          let G5 := fresh "G5" in
          zstep; zstep; if_cases G5; zify_cond G5; ptr_small G5;
          [ (* [comment removed for export] *)
            normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
          | zstep; zstep; zstep;
            bcmp_call U8 i 5%nat LIT_amp lit_amp_at;
            let Q3 := fresh "Q3" in
            zstep; if_cases Q3;
            [ (* [comment removed for export] *)
              normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
            | (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 5;
              [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G5; lia | clear - BUD G5; lia | clear - MEAS G5; lia | exact NUL] ] ] ] ]
    end end.



  (* [comment removed for export] *)
  Local Ltac printf_c_site TI FR BUDTAC :=
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | BUDTAC | clear; lia | reflexivity | ];
      [ lazymatch goal with E0 : (0 <= e)%Z |- _ => exact E0 | _ => clear; lia end
      | clear TI FR;
        repeat match goal with Hx : rw_cells _ mk _ _ |- _ => clear Hx | Hx : stk _ mk _ _ |- _ => clear Hx | Hx : mem_inv _ mk |- _ => clear Hx
                             | Hx : u8arr _ mk _ _ |- _ => clear Hx | Hx : munch _ _ mk |- _ => clear Hx | Hx : wmono _ _ mk |- _ => clear Hx end;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR; cbv beta delta [FRAME] in FR;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2; clear MDL2 MDH2 ]
    end.

  (* [comment removed for export] *)
  Local Ltac tinv_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mx _ _ _ =>
      repeat match goal with
      | Hx : vsb_obj _ _ ?my (v Finclude_src) _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : Z.of_nat (length _) = vb_size _ |- _ => clear Hx
      | Hx : rw_cells _ ?my VEP _ |- _ => clear Hx
      | Hx : mem_inv _ ?my |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : stk _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : u8arr _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      end end;
    let X := fresh "TIc" in pose proof TI as X;
    destruct X as (_ & _ & MIk & _ & STk & _ & _ & VEPC & _ & _ & _ & _ & _ & _ & _ & _ & IOk & U8k & LBS & _ & _);
    unfold vep_cells in VEPC.


  (* [comment removed for export] *)
  Local Ltac env_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mk _ _ _ =>
      let HE := fresh "HENVk" in let IM := fresh "IMGk" in
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HE;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IM;
      let GLOB := fresh "GLOBk" in let HOBJ := fresh "HOBJk" in
      destruct HE as [GLOB HOBJ];
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let CNT := fresh "CNT" in
      pose proof GLOB as (EBSS & BSS & CP & [c CNT]); cbn [al_segs LayoutP0] in BSS, CP, CNT; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_6; dand3 dR_6 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      let GV := fresh "GVSC" in
      (first [ pose proof (IM) as dR_9; dand4 dR_9 as _ _ GV _ | pose proof IM as (_ & _ & GV & _) ]); unfold GOT_vsc in GV
    end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac henv_rebuild MU WM CNT HENV2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch goal with GLOBk : glob_ok _ _ H mk, HOBJk : hobj_ok _ _ H mk |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT2" in
      (first [ pose proof (GLOBk) as dR_10; dand4 dR_10 as EBSS BSS CP _ | pose proof GLOBk as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP;
      destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
      assert (HENV2 : henv_ok LayoutP0 VI0 H mc);
      [ split;
        [ eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact C];
          [ eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS; cbn; geo_lia]
          | eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; unfold h_cp; geo_lia] ]
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJk | exact MU | exact WM |];
          let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; revert Ha; geo_lia ]
      | clear BSS CP C c EBSS ]
    end end.

  Local Ltac to_err_tail TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & _ & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & _ & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      let AINV2 := fresh "AINV2" in pose proof (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk) as AINV2;
      let SOBJ2 := fresh "SOBJ2" in
      assert (SOBJ2 : vsb_obj LayoutP0 Ak mc (v Fvsb) vvk false);
      [ eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn;
        [ unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia ] |];
      let IOBJ2 := fresh "IOBJ2" in
      assert (IOBJ2 : vsb_obj LayoutP0 Ak mc (v Finclude_src) yi true);
      [ eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn;
        [ unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia ] |];
      let CF2 := fresh "CF2" in
      lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
        assert (CF2 : cframe LayoutP0 (owned A) (owned Ak) (bv_unsigned sp) 8544 VT NT m mc);
        [ eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
          [ exact CFk
          | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
            eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
              [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
          | clear; lia | clear; lia
          | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
              [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
          | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] |]
      end;
      unhide_neqs;
        eapply ((@seg_err_tail _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mc mdk vvk e);
        [ exact EVI' | exact AINV2 | exact MIq | exact MDFk | exact STq | exact HENV2
        | unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VI0 st0];
          lazymatch goal with EVC : v Fvc = _, HAZ : v Fattr_vsb = 0 |- _ => rewrite EVC, HAZ end; exact VEPq
        | exact FRq | exact SOBJ2 | exact NEBk | exact LENk
        | lazymatch goal with VL : (0 <= vb_len yi < _)%Z |- _ => revert VL LENk; clear; intros; lia end
        | exact SZk | exact RELk | exact LIVEk | exact BUDk | exact CF2
        | exact IOBJ2 | exact NISBk | exact NIBBk ]
    end end end.


  Local Ltac unhide_disj_vimg := try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end.

  (* [comment removed for export] *)
  Local Ltac tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      repeat match goal with Hi : img_ok0 ?mm |- _ => lazymatch mm with m => fail | _ => clear Hi end end;
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & IMGk & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8o & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      assert (TI2 : TINV yi bs Ak mc mdk vvk e);
      [ split; [exact EVI'|]; split; [exact (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk)|]; split; [exact MIq|]; split; [exact MDFk|];
        split; [exact STq|]; split; [exact HENV2|];
        split; [eapply img_ok0_munch; [exact MU | | exact IMGk]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside];
                unhide_disj_vimg; revert Ha; geo_lia |];
        split; [unfold vep_cells; lazymatch goal with EVC : v Fvc = _ |- _ => try rewrite EVC end; exact VEPq|];
        split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia] |];
        split; [exact NEBk|]; split; [exact BUDk|]; split; [exact LENk|]; split; [exact SZk|]; split; [exact RELk|]; split; [exact LIVEk|];
        split; [ lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
                   eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
                   [ exact CFk
                   | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
                     eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | clear; lia | clear; lia
                   | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] end |];
        split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia] |];
        split; [eapply u8arr_transport; [exact U8o | exact MU | exact WM |]; rewrite LBS'; cbn; unhide DVBI; revert DVBI BIk; geo_lia |];
        split; [exact LBS'|]; split; [exact NISBk| exact NIBBk]
      | clear AINVk MDFk IMGk SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8o LBS' NISBk NIBBk EVI' LVk LBk LSk DVBk Bk Sk LSIk LBIk SIk BIk CFPk ]
    end end end.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV a1 a0"] Lemma seg_main4 : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (incl : Z) (j : list byte),
    TINV yi bs Ak mk mdk vvk 0 ->
    rw_cells rsegs mk (bv_unsigned sp + -112) (FRAME (CB 8 j)) ->
    0 <= incl < 256 ->
    nth_error bs (Z.to_nat (vb_len yi)) = Some (Z_to_bv 8 0) ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    (Z_to_bv 64 (vb_buf yi)) (Z_to_bv 64 (vb_len yi)) (Z_to_bv 64 incl) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b334) (Z_to_bv 32 0) None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all.
    intros until j. intros TI FR INCL NUL.
    prelims. clear VEPC0. pose proof (proj1 TI) as EVI. yi_facts EVI.
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_19; dand8 dR_19 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    tinv_open TI. cbv beta delta [FRAME] in FR.
    pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDLk MDHk].
    hide_disj. hide_slow.
    apply rz_go; [exact MDHk | exact MDLk |].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KB; zify_cond KB; rewrite signed_small in KB by (clear - VlenI VszI; lia).
    { (* [comment removed for export] *)
      apply rz_stop. eapply ((@seg_pfx _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | exact INCL | exact NUL]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmp_call U8k 0 7%nat LIT_http lit_http_at.
    zstep. if_cases Q1; zify_cond Q1.
    { (* [comment removed for export] *)
      apply rz_stop.
      eapply ((@seg_http _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | exact INCL | clear - KB; lia | exact NUL]. }
    (* [comment removed for export] *)
    zstep. zstep. if_cases K8; zify_cond K8.
    { apply rz_stop.
      eapply ((@seg_pfx _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | exact INCL | exact NUL]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    bcmp_call U8k 0 8%nat LIT_https lit_https_at.
    zstep. if_cases Q2; zify_cond Q2.
    { (* [comment removed for export] *)
      apply rz_stop.
      eapply ((@seg_https _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | exact INCL | clear - KB K8; lia | exact NUL]. }
    apply rz_stop.
    eapply ((@seg_pfx _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs); [exact TI | exact FR | exact INCL | exact NUL].
  Qed.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV A a1 a0 vv AI Clg"] Lemma seg_main3 : forall (yi : vsb_rec) (xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (mq : mem) (j : list byte) (c : list byte),
    vi = Some yi ->
    munch W m mq -> wmono rsegs m mq -> mem_inv rsegs mq -> stk rsegs mq lo (bv_unsigned sp + -112) ->
    rw_cells rsegs mq (bv_unsigned sp + -112) (FRAME (CB 8 j)) ->
    rw_cells rsegs mq VEP (vep_cells v tag q) ->
    rw_cells rsegs mq (h_vsc H + 1304) [CB 16 c] ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    (Z_to_bv 64 (v Finclude_src)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b1f0) (Z_to_bv 32 0) None mq (seg_rom rsegs)) md) T.
  Proof.
    touch_all.
    intros until c. intros EVI MU WM MIq STq FR VEPC CNT.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    prelims. clear VEPC0. yi_facts EVI. cbv beta delta [FRAME] in FR. cbv delta [W] in MU. unfold vep_cells in VEPC. rewrite EVC in VEPC.
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_20; dand8 dR_20 as VszI VlenI _ _ _ Vb0I Vb47I VbmI | pose proof VINVI as (VszI & VlenI & _ & _ & _ & Vb0I & Vb47I & VbmI) ]).
    destruct HENV as [GLOB HOBJ].
    (* [comment removed for export] *)
    assert (IOBJq : vsb_obj LayoutP0 A mq (v Finclude_src) yi true).
    { eapply (vsb_obj_munch LayoutP0); [exact IOBJ | exact MU | exact WM | |]; cbn; [revert DVSI SIhi | revert DVBI BIhi]; geo_lia. }
    pose proof IOBJq as IO. vsb_open IO. (first [ dex1 VBUF as bs; dand3 VBUF as U8q LBS NULf | dand4 VBUF as bs U8q LBS NULf | destruct VBUF as (bs & U8q & LBS & NULf) ]). specialize (NULf eq_refl). cbn [al_segs LayoutP0] in U8q.
    hide MI. hide ST. clear HMH || idtac. hide_disj. hide_slow.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep.
    call_fr (VSB_data_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq (v Finclude_src) yi lo) by
      (idtac; [> reflexivity | exact VSBC | exact VINV | exact SIlo | exact SIhi
              | rewrite unsigned_lit by lia; exact STq | rewrite unsigned_lit by lia; clear - LO; lia | exact CEIL
              | rewrite unsigned_lit by lia; clear - SPH G3; lia | exact MIq ]).
    lazymatch goal with S : stk _ ?mx lo _, M : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename S into STq; rename M into MIq end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    call_fr (VSB_len_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx (v Finclude_src) yi true lo) by
      (idtac; [> reflexivity | exact VSBC | exact VINV | exact SIlo | exact SIhi
              | rewrite unsigned_lit by lia; exact STq | rewrite unsigned_lit by lia; clear - LO; lia | exact CEIL
              | rewrite unsigned_lit by lia; clear - SPH G3; lia | exact MIq ]) end.
    lazymatch goal with S : stk _ ?mx lo _, M : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename S into STq; rename M into MIq; rename mx into mc end.
    unfold vsb_result. rewrite IERR. change (0 =? 0) with true. cbv iota.
    clear VSBC VLS VLB VNE VINV.
    (* [comment removed for export] *)
    henv_rebuild MU WM CNT HENVc.
    assert (TI : TINV yi bs A mc md vv 0).
    { split; [exact EVI|]. split; [exact (ainv_munch LayoutP0 A m mc md _ AINV MU WM CFP)|]. split; [exact MIq|].
      split; [apply md_frame_refl; [exact MDL| exact MDH]|]. split; [exact STq|]. split; [exact HENVc|].
      split; [eapply img_ok0_munch; [exact MU | | exact IMG]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside]; unhide_disj_vimg; revert Ha; geo_lia|].
      split; [unfold vep_cells; rewrite EVC; exact VEPC|].
      split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJ | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Shi | unhide DVB; revert DVB Bhi]; geo_lia|].
      split; [unhide NEB; exact NEB|]. split; [split; [clear; lia| reflexivity]|]. split; [clear; lia|]. split; [clear; lia|].
      split; [left; reflexivity|]. split; [intros; reflexivity|].
      split; [eapply (cframe_noalloc LayoutP0); [exact MU | apply W_cover | | intros ? X; right; left; exact X];
              eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                [exact STq | exact FR | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia] |].
      split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJ | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIhi | unhide DVBI; revert DVBI BIhi]; geo_lia|].
      split; [exact U8q|]. split; [exact LBS|]. unhide_neqs. split; [exact NISB| exact NIBB]. }
    clear U8q CNT GLOB HOBJ.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small' (v Finclude_continue)) by (unhide HIC; clear - HIC; destruct HIC; lia).
    zstep. zstep. if_cases KI; zify_cond KI.
    - (* [comment removed for export] *)
      zstep. apply rz_stop. eapply (seg_main4 yi bs); [exact TI | exact FR | clear; lia | exact NULf].
    - (* [comment removed for export] *)
      zstep. zstep. apply rz_stop. eapply (seg_main4 yi bs); [exact TI | exact FR | clear; lia | exact NULf].
  Qed.



End S.
End V_ve32b.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vejx2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veifi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_veibx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vea4z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_ved28 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_vencr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_vek4w.V_ve32b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac call_consts_in H ::= unfold VEPERR_STACK in H.
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 1.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HFL : 0 <= v Fflags < 16.
  Hypothesis HET : bool01 (v Femptytag).
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis HLM : v Flast_mark = 1.
  Hypothesis HAZ : v Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LayoutP0 A m (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis SZB : vb_size vv <= vb_len vv + 4096.
  Hypothesis LENB : vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  (* [comment removed for export] *)
  Hypothesis LBUD : a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NBUD : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  Let FRAME (c0 : cell) : list cell :=
    [c0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Notation TINV := (tinv VEP v tag q vv vi H lo sp m md A).

  Local Ltac unpack_tinv TI :=
    (first [ dand21 TI as EVI AINVk MIk MDFk STk HENVk IMGk VEPC SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & IMGk & VEPC & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK, PRINTF_STACK, VPRINTF_STACK, EXT_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_2; dand7 dR_2 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fvsb) vv false AINV SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (proj1 (proj2 (proj1 (proj2 SOBJ)))) as Vlen0;
    pose proof (as_live_disjoint A m md VEP 312 (v Fvsb) 40 AINV VLV LS NES) as DVS;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf vv) (vb_size vv) AINV VLV LB NEB) as DVB;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A VEP = Some 312, LS : a_live A (v Fvsb) = Some 40, LB : a_live A (vb_buf vv) = Some (vb_size vv) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ)) as dR_4; dand11 dR_4 as SI16 SIlo SIhi SIimg BI16 BIlo BIhi BIimg DSBI SImap BImap | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) _ true AINV IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap) ]);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint A m md VEP 312 _ _ AINV VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint A m md _ _ _ _ AINV LB LBI (not_eq_sym NIBB)) as DBBI
    end.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HFL (conj HET
      (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB (conj SZB (conj LENB (conj LBUD (conj NBUD (conj HVI (conj TP (conj SP16 (conj RA2
      (conj ST (conj CEIL (conj LO (conj SPH K))))))))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  #[using="SPH LO CEIL NEB NES SOBJ HG VBASE VOBJ AINV md m ra lo vv q tag v"] Lemma CFP : client_fp LayoutP0 A W.
  Proof.
    prelims. cbn. split; [left; lia|]. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  #[using="NEB NES SOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)

 

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac normal_tail IH TI FR i :=
    zstep; zstep; zstep; zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; apply rz_stop;
        replace (vb_buf yi + i + 1) with (vb_buf yi + (i + 1)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac entity_tail IH TI FR i w :=
    zstep; zstep;
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | | clear; lia | reflexivity | ];
      [ | |
        let TI2 := fresh "TI" in let FR2 := fresh "FR" in
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI2 FR2;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI2))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2;
        (* [comment removed for export] *)
        zstep; zstep; apply rz_stop;
        replace (vb_buf yi + i + w) with (vb_buf yi + (i + w)) by (clear; lia);
        eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + w));
        [ exact TI2 | exact FR2 | .. ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac ptr_small G :=
    try (rewrite Z.mod_small in G by
      (lazymatch goal with IR : (0 <= _ <= vb_len ?yi)%Z, VB : (vb_buf ?yi + vb_size ?yi < _)%Z, VL : (0 <= vb_len ?yi < vb_size ?yi)%Z, VZ : (0 < vb_buf ?yi)%Z |- _ =>
         revert IR VB VL VZ; clear; intros; lia end)).

  (* [comment removed for export] *)
  Local Ltac rd_byte U8 ik adr RD :=
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let bq := fresh "bq" in let Hq := fresh "Hq" in
      destruct (nth_error bs (Z.to_nat ik)) as [bq|] eqn:Hq;
      [ pose proof (byte_range bq);
        pose proof (u8arr_read rsegs mx B bs ik bq adr U8 Hq) as RD;
        lazymatch goal with IR : (0 <= _ <= vb_len _)%Z |- _ =>
          specialize (RD ltac:(clear - IR; lia) ltac:(unfold wa; f_equal; clear; lia)) end
      | exfalso; apply nth_error_None in Hq;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert Hq LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end ]
    end.

  (* [comment removed for export] *)
  Local Ltac bcmp_call U8 i w LIT LITAT :=
    zstep;
    lazymatch type of U8 with u8arr _ ?mx ?B ?bs =>
      let vq := fresh "vq" in let Mq := fresh "Mq" in
      destruct (memcmp_model_total (firstn w (skipn (Z.to_nat i) bs)) LIT w) as [vq Mq];
      [ rewrite firstn_length_le; [clear; lia|]; rewrite skipn_length;
        lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
          revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
          clear; intros; lia end
      | cbn; clear; lia
      | eapply evt_cut;
        [ eapply bcmp_spec with (ls := firstn w (skipn (Z.to_nat i) bs)) (rs := LIT) (v := vq);
          [ rewrite unsigned_lit by lia;
            first [ apply (u8arr_sub mx B bs i w U8) | replace B with (B + i)%Z at 1 by (clear; lia); apply (u8arr_sub mx B bs i w U8) ];
            lazymatch goal with LBS : Z.of_nat (length bs) = _, VlenI : (0 <= vb_len _ < vb_size _)%Z |- _ =>
              revert LBS VlenI; repeat match goal with G : (_ <= _ + vb_len _)%Z |- _ => revert G | G : (_ < vb_len _)%Z |- _ => revert G | G : (_ <= _ <= vb_len _)%Z |- _ => revert G | G : (_ <= vb_len _)%Z |- _ => revert G | G : (~ _ < _)%Z |- _ => revert G | G : (vb_len _ <> _)%Z |- _ => revert G end;
              clear; intros; lia end
          | rewrite unsigned_lit by lia; apply LITAT; assumption
          | rewrite unsigned_lit by lia; exact Mq
          | assumption ]
        | ] ];
      (* [comment removed for export] *)
      let ms := fresh "ms" in let PO := fresh "PO" in let mq := fresh "mq" in
      let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIq" in
      intros ms PO; unfold memcmp_post in PO; destruct_exs PO;
      (first [ dand6 PO as E MUc WMc MIc _ _ | destruct PO as (E & MUc & WMc & MIc & _ & _) ]); subst ms;
      lazymatch type of MUc with munch [] mx ?mq =>
        lazymatch goal with TI : TINV _ bs _ mx _ _ _, FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MIo : mem_inv _ mx |- _ =>
          eapply (rw_cells_transport rsegs [] mx mq) in FR; [| exact MUc | exact WMc | exact I];
          try (lazymatch goal with VEPC : rw_cells _ mx VEP _ |- _ =>
                 eapply (rw_cells_transport rsegs [] mx mq) in VEPC; [| exact MUc | exact WMc | exact I] end);
          eapply (stk_transport_disjoint rsegs [] mx mq) in STq; [| exact MUc | exact WMc | exact I];
          eapply (u8arr_transport rsegs [] mx mq) in U8; [| exact MUc | exact WMc | exact I];
          let TI' := fresh "TI" in
          pose proof ((@tinv_ext _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) _ _ _ _ _ _ _ [] mq _ TI MUc WMc MIc (or_introl eq_refl) STq FR eq_refl) as TI';
          clear TI MUc WMc MIo; rename TI' into TI;
          repeat match goal with Hx : rw_cells _ mx _ _ |- _ => clear Hx | Hx : ov_read_bytes _ mx _ _ = _ |- _ => clear Hx end
        end
      end;
      try (lazymatch goal with
      | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      end)
    end.

  (* [comment removed for export] *)
  Local Ltac ent4_block IH TI FR U8 i G4 :=
    lazymatch goal with E0 : (0 <= ?e)%Z, BUD : (?e + _ + 1 <= _)%Z, IR : (0 <= i <= _)%Z, MEAS : (_ - i <= Z.of_nat _)%Z,
                        NUL : nth_error _ (Z.to_nat _) = Some (Z_to_bv 8 0), IL : (i < _)%Z |- _ =>
    lazymatch type of U8 with u8arr _ _ ?B _ =>
      (* [comment removed for export] *)
      let RD := fresh "RD" in
      rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
      rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
      rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
      rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
      do 6 zstep;
      let E1 := fresh "E1" in
      zstep; if_cases E1;
      [ (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 4;
        [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
      | clear E1;
        rd_byte U8 (i + 1) (Z_to_bv 64 (B + i + 1)) RD; zstep; clear RD;
        rd_byte U8 i (Z_to_bv 64 (B + i)) RD; zstep; clear RD;
        rd_byte U8 (i + 2) (Z_to_bv 64 (B + i + 2)) RD; zstep; clear RD;
        rd_byte U8 (i + 3) (Z_to_bv 64 (B + i + 3)) RD; zstep; clear RD;
        do 6 zstep;
        let E2 := fresh "E2" in
        zstep; if_cases E2;
        [ (* [comment removed for export] *) do 2 zstep; entity_tail IH TI FR i 4;
          [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G4; lia | clear - BUD G4; lia | clear - MEAS G4; lia | exact NUL]
        | clear E2;
          (* [comment removed for export] *)
          let G5 := fresh "G5" in
          zstep; zstep; if_cases G5; zify_cond G5; ptr_small G5;
          [ (* [comment removed for export] *)
            normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
          | zstep; zstep; zstep;
            bcmp_call U8 i 5%nat LIT_amp lit_amp_at;
            let Q3 := fresh "Q3" in
            zstep; if_cases Q3;
            [ (* [comment removed for export] *)
              normal_tail IH TI FR i; [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR IL; lia | clear - BUD IL; lia | clear - MEAS IL; lia | exact NUL]
            | (* [comment removed for export] *) do 3 zstep; entity_tail IH TI FR i 5;
              [clear - E0; lia | clear - BUD IL; lia | clear - E0; lia | clear - IR G5; lia | clear - BUD G5; lia | clear - MEAS G5; lia | exact NUL] ] ] ] ]
    end end.



  (* [comment removed for export] *)
  Local Ltac printf_c_site TI FR BUDTAC :=
    apply rz_stop;
    lazymatch type of TI with TINV ?yi ?bs ?Ak ?mk ?mdk ?vvk ?e =>
      eapply ((@printf_c_call _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mk mdk vvk e);
      [ exact TI | exact FR | reflexivity | | BUDTAC | clear; lia | reflexivity | ];
      [ lazymatch goal with E0 : (0 <= e)%Z |- _ => exact E0 | _ => clear; lia end
      | clear TI FR;
        repeat match goal with Hx : rw_cells _ mk _ _ |- _ => clear Hx | Hx : stk _ mk _ _ |- _ => clear Hx | Hx : mem_inv _ mk |- _ => clear Hx
                             | Hx : u8arr _ mk _ _ |- _ => clear Hx | Hx : munch _ _ mk |- _ => clear Hx | Hx : wmono _ _ mk |- _ => clear Hx end;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? TI FR; cbv beta delta [FRAME] in FR;
        let MDL2 := fresh "MDL" in let MDH2 := fresh "MDH" in
        pose proof (as_lazy_nil _ _ _ (proj1 (proj2 TI))) as [MDL2 MDH2];
        rz_resume MDH2 MDL2; clear MDL2 MDH2 ]
    end.

  (* [comment removed for export] *)
  Local Ltac tinv_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mx _ _ _ =>
      repeat match goal with
      | Hx : vsb_obj _ _ ?my (v Finclude_src) _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : Z.of_nat (length _) = vb_size _ |- _ => clear Hx
      | Hx : rw_cells _ ?my VEP _ |- _ => clear Hx
      | Hx : mem_inv _ ?my |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : stk _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      | Hx : u8arr _ ?my _ _ |- _ => lazymatch my with m => fail | _ => clear Hx end
      end end;
    let X := fresh "TIc" in pose proof TI as X;
    destruct X as (_ & _ & MIk & _ & STk & _ & _ & VEPC & _ & _ & _ & _ & _ & _ & _ & _ & IOk & U8k & LBS & _ & _);
    unfold vep_cells in VEPC.


  (* [comment removed for export] *)
  Local Ltac env_open TI :=
    lazymatch type of TI with TINV _ _ _ ?mk _ _ _ =>
      let HE := fresh "HENVk" in let IM := fresh "IMGk" in
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 TI)))))) as HE;
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 TI))))))) as IM;
      let GLOB := fresh "GLOBk" in let HOBJ := fresh "HOBJk" in
      destruct HE as [GLOB HOBJ];
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let CNT := fresh "CNT" in
      pose proof GLOB as (EBSS & BSS & CP & [c CNT]); cbn [al_segs LayoutP0] in BSS, CP, CNT; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_6; dand3 dR_6 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      let GV := fresh "GVSC" in
      (first [ pose proof (IM) as dR_9; dand4 dR_9 as _ _ GV _ | pose proof IM as (_ & _ & GV & _) ]); unfold GOT_vsc in GV
    end.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac henv_rebuild MU WM CNT HENV2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch goal with GLOBk : glob_ok _ _ H mk, HOBJk : hobj_ok _ _ H mk |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT2" in
      (first [ pose proof (GLOBk) as dR_10; dand4 dR_10 as EBSS BSS CP _ | pose proof GLOBk as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP;
      destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
      assert (HENV2 : henv_ok LayoutP0 VI0 H mc);
      [ split;
        [ eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact C];
          [ eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS; cbn; geo_lia]
          | eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; unfold h_cp; geo_lia] ]
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJk | exact MU | exact WM |];
          let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; revert Ha; geo_lia ]
      | clear BSS CP C c EBSS ]
    end end.

  Local Ltac to_err_tail TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & _ & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & _ & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      let AINV2 := fresh "AINV2" in pose proof (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk) as AINV2;
      let SOBJ2 := fresh "SOBJ2" in
      assert (SOBJ2 : vsb_obj LayoutP0 Ak mc (v Fvsb) vvk false);
      [ eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn;
        [ unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia ] |];
      let IOBJ2 := fresh "IOBJ2" in
      assert (IOBJ2 : vsb_obj LayoutP0 Ak mc (v Finclude_src) yi true);
      [ eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn;
        [ unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia ] |];
      let CF2 := fresh "CF2" in
      lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
        assert (CF2 : cframe LayoutP0 (owned A) (owned Ak) (bv_unsigned sp) 8544 VT NT m mc);
        [ eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
          [ exact CFk
          | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
            eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
              [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
          | clear; lia | clear; lia
          | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
              [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
          | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] |]
      end;
      unhide_neqs;
        eapply ((@seg_err_tail _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ak mc mdk vvk e);
        [ exact EVI' | exact AINV2 | exact MIq | exact MDFk | exact STq | exact HENV2
        | unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb vi_st VI0 st0];
          lazymatch goal with EVC : v Fvc = _, HAZ : v Fattr_vsb = 0 |- _ => rewrite EVC, HAZ end; exact VEPq
        | exact FRq | exact SOBJ2 | exact NEBk | exact LENk
        | lazymatch goal with VL : (0 <= vb_len yi < _)%Z |- _ => revert VL LENk; clear; intros; lia end
        | exact SZk | exact RELk | exact LIVEk | exact BUDk | exact CF2
        | exact IOBJ2 | exact NISBk | exact NIBBk ]
    end end end.


  Local Ltac unhide_disj_vimg := try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end.

  (* [comment removed for export] *)
  Local Ltac tinv_restore TI MU WM HENV2 LAY ACV G2 G3 Evsc DVS DVSI DVBI TI2 :=
    lazymatch type of MU with munch _ ?mk ?mc =>
    lazymatch type of TI with TINV ?yi ?bs ?Ak _ ?mdk ?vvk ?e =>
    lazymatch goal with STq : stk _ mc lo _, FRq : rw_cells _ mc (bv_unsigned sp + -112)%Z _, VEPq : rw_cells _ mc VEP _, MIq : mem_inv _ mc |- _ =>
      repeat match goal with Hi : img_ok0 ?mm |- _ => lazymatch mm with m => fail | _ => clear Hi end end;
      let X := fresh "TIx" in pose proof TI as X;
      destruct X as (EVI' & AINVk & _ & MDFk & _ & _ & IMGk & _ & SOBJk & NEBk & BUDk & LENk & SZk & RELk & LIVEk & CFk & IOBJk & U8o & LBS' & NISBk & NIBBk);
      let LVk := fresh "LVk" in
      assert (LVk : a_live Ak VEP = Some 312) by (unhide NEB; unhide NEBk; rewrite (LIVEk VEP NEB NEBk); lazymatch goal with V : a_live A VEP = Some 312 |- _ => exact V end);
      let LBk := fresh "LBk" in pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBk;
      let LSk := fresh "LSk" in pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk;
      let DVBk := fresh "DVBk" in
      pose proof (as_live_disjoint Ak mk mdk VEP 312 _ _ AINVk LVk LBk ltac:(unhide NEBk; exact NEBk)) as DVBk;
      let Bk := fresh "Bk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBk) as Bk; (first [ dand5 Bk as _ _ _ Bk _ | destruct Bk as (_ & _ & _ & Bk & _) ]);
      let Sk := fresh "Sk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSk) as Sk; (first [ dand5 Sk as _ _ _ Sk _ | destruct Sk as (_ & _ & _ & Sk & _) ]);
      let LSIk := fresh "LSIk" in pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk;
      let LBIk := fresh "LBIk" in pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk;
      let SIk := fresh "SIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LSIk) as SIk; (first [ dand5 SIk as _ _ _ SIk _ | destruct SIk as (_ & _ & _ & SIk & _) ]);
      let BIk := fresh "BIk" in pose proof (as_live_ok Ak mk mdk _ _ AINVk LBIk) as BIk; (first [ dand5 BIk as _ _ _ BIk _ | destruct BIk as (_ & _ & _ & BIk & _) ]);
      let CFPk := fresh "CFPk" in
      assert (CFPk : client_fp LayoutP0 Ak [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)]);
      [ cbn; split; [left; clear - CEIL LO LAY ACV G3 SPH; lia|]; split; [left; clear - CEIL LO LAY ACV G2 G3 SPH Evsc; lia|];
        split; [right; left; exists VEP, 312; split; [exact LVk| clear; lia]| exact I] |];
      assert (TI2 : TINV yi bs Ak mc mdk vvk e);
      [ split; [exact EVI'|]; split; [exact (ainv_munch LayoutP0 Ak mk mc mdk _ AINVk MU WM CFPk)|]; split; [exact MIq|]; split; [exact MDFk|];
        split; [exact STq|]; split; [exact HENV2|];
        split; [eapply img_ok0_munch; [exact MU | | exact IMGk]; intros ? Ha; unfold IMG0_LO, IMG0_HI in Ha; cbn [outside];
                unhide_disj_vimg; revert Ha; geo_lia |];
        split; [unfold vep_cells; lazymatch goal with EVC : v Fvc = _ |- _ => try rewrite EVC end; exact VEPq|];
        split; [eapply (vsb_obj_munch LayoutP0); [exact SOBJk | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Sk; geo_lia | revert DVBk Bk; geo_lia] |];
        split; [exact NEBk|]; split; [exact BUDk|]; split; [exact LENk|]; split; [exact SZk|]; split; [exact RELk|]; split; [exact LIVEk|];
        split; [ lazymatch type of CFk with cframe _ _ _ _ _ ?VT ?NT m mk =>
                   eapply (cframe_seq LayoutP0 _ _ _ (bv_unsigned sp) 8544 8544 8544 _ _ _ _ _ _ m mk mc);
                   [ exact CFk
                   | eapply (cframe_stores LayoutP0); [exact MU | apply W_cover |];
                     eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | clear; lia | clear; lia
                   | eapply (window_mapped LayoutP0 mc lo (bv_unsigned sp + -112) (bv_unsigned sp) 8544);
                       [exact STq | exact FRq | cbn; clear; lia | exact CEIL | clear - LO; lia | clear; lia]
                   | intros ? X; exact X | intros ? X; right; exact X | intros ? X; left; exact X ] end |];
        split; [eapply (vsb_obj_munch LayoutP0); [exact IOBJk | exact MU | exact WM | |]; cbn; [unhide DVSI; revert DVSI SIk; geo_lia | unhide DVBI; revert DVBI BIk; geo_lia] |];
        split; [eapply u8arr_transport; [exact U8o | exact MU | exact WM |]; rewrite LBS'; cbn; unhide DVBI; revert DVBI BIk; geo_lia |];
        split; [exact LBS'|]; split; [exact NISBk| exact NIBBk]
      | clear AINVk MDFk IMGk SOBJk NEBk BUDk LENk SZk RELk LIVEk CFk IOBJk U8o LBS' NISBk NIBBk EVI' LVk LBk LSk DVBk Bk Sk LSIk LBIk SIk BIk CFPk ]
    end end end.



  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV A a1 a0 vi vv AI Clg"] Lemma seg_main2 : forall (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (mq : mem) (j : list byte) (c : list byte),
    munch W m mq -> wmono rsegs m mq -> mem_inv rsegs mq -> stk rsegs mq lo (bv_unsigned sp + -112) ->
    rw_cells rsegs mq (bv_unsigned sp + -112) (FRAME (CB 8 j)) ->
    rw_cells rsegs mq VEP (vep_cells v tag q) ->
    rw_cells rsegs mq (h_vsc H + 1304) [CB 16 c] ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1
                                    xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b1d4) (Z_to_bv 32 0) None mq (seg_rom rsegs)) md) T.
  Proof.
    touch_all.
    intros until c. intros MU WM MIq STq FR VEPC CNT.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    prelims. clear VEPC0. cbv beta delta [FRAME] in FR. cbv delta [W] in MU. unfold vep_cells in VEPC. rewrite EVC in VEPC.
    destruct HENV as [GLOB HOBJ].
    hide MI. hide ST. clear HMH || idtac.
    assert (EV : (exists yi, vi = Some yi) \/ vi = None) by (clear; destruct vi; [left; eexists; reflexivity | right; reflexivity]).
    destruct EV as [[yi EVI]|EVI].
    - (* [comment removed for export] *)
      yi_facts EVI. hide_disj. hide_slow.
      apply rz_go; [exact MDH | exact MDL |].
      zstep. zstep. if_cases KT; zify_cond KT. { exfalso. unhide INZ. clear - KT INZ SIlo SIhi ACV. lia. } clear KT.
      zstep. zstep. if_cases KW; zify_cond KW.
      + apply rz_stop. eapply ((@seg_main3 _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi); [exact EVI | exact MU | exact WM | exact MIq | exact STq | exact FR | unfold vep_cells; rewrite EVC; exact VEPC | exact CNT].
      + (* [comment removed for export] *)
        rewrite HLM in VEPC.
        zstep. rewrite (sx32_small' 1) by (clear; lia). zstep. zstep. if_cases KL; zify_cond KL. { exfalso. clear - KL. lia. } clear KL.
        apply rz_stop. rewrite <- HLM in VEPC.
        eapply ((@seg_main3 _ AI VEP v tag q vv vi H lo ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md A T AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K) yi); [exact EVI | exact MU | exact WM | exact MIq | exact STq | exact FR | unfold vep_cells; rewrite EVC; exact VEPC | exact CNT].
    - (* [comment removed for export] *)
      pose proof HVI as ISRC. rewrite EVI in ISRC. rewrite ISRC in VEPC.
      (* [comment removed for export] *)
      (first [ pose proof (GLOB) as dR_19; dand4 dR_19 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]). cbn [al_segs LayoutP0] in BSS, CP. cbn [vi_bss VI0] in EBSS. rewrite EBSS in BSS.
      eapply (rw_cells_transport rsegs _ m mq) in BSS; [| exact MU | exact WM | cbn; geo_lia].
      (first [ pose proof (HOBJ) as dR_20; dand3 dR_20 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]).
      (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
      cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
      eapply (rw_cells_transport rsegs _ m mq) in VC; [| exact MU | exact WM | cbn; revert LP1 LR1; geo_lia].
      eapply (rw_cells_transport rsegs _ m mq) in WK; [| exact MU | exact WM | cbn; revert LP2 LR2; geo_lia].
      pose proof IMG as (_ & _ & GVSC & _). unfold GOT_vsc in GVSC.
      eapply (ro_cells_transport rsegs _ m mq) in GVSC; [| exact MU | cbn; geo_lia].
      hide_disj. hide_slow.
      apply rz_go; [exact MDH | exact MDL |].
      zstep. zstep. if_cases KT; zify_cond KT. 2:{ exfalso. apply KT. reflexivity. } clear KT.
      (* [comment removed for export] *)
      do 15 zstep. clear BSS VC WK GVSC CP.
      do 14 zstep.
      try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR STq (bv_unsigned sp).
      (* [comment removed for export] *)
      zstep. carve_frame 48%nat STq. do 8 zstep.
      try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -48)%Z _ |- _ => release_frame FR2 STq (bv_unsigned sp) end.
      cps_done.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m4 end.
      henv_rebuild MU WM CNT HENV4.
      pose proof (ainv_munch LayoutP0 A m m4 md _ AINV MU WM CFP) as AINV4.
      assert (SOBJ4 : vsb_obj LayoutP0 A m4 (v Fvsb) vv false).
      { eapply (vsb_obj_munch LayoutP0); [exact SOBJ | exact MU | exact WM | |]; cbn; [unhide DVS; revert DVS Shi | unhide DVB; revert DVB Bhi]; geo_lia. }
      unhide_neqs.
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A m4 md v vv);
        [ exact AINV4 | exact MIq | apply md_frame_refl; [exact MDL| exact MDH] | exact STq | exact HENV4
        | split; [exact VLV|]; split; [| split; [exact TAG| exact PADS]]; cbn [al_segs LayoutP0]; unfold vep_cells; rewrite EVC, ISRC; exact VEPC
        | apply vkeep_refl | left; reflexivity | exact HIC | exact ISRC | exact SOBJ4
        | rewrite EVI; clear - Vlen0; lia | clear; lia | left; reflexivity | rewrite EVI; split; [intros; reflexivity| split; reflexivity] | rewrite EVI ].
      eapply (cframe_noalloc LayoutP0); [exact MU | apply W_cover | | intros ? X; right; left; exact X].
      eapply (stk_mapped (L:=LayoutP0)); [exact STq | exact CEIL | clear -LO; lia | clear; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="FRAME W K SPH LO CEIL ST RA2 SP16 TP HVI NBUD LBUD LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL IMG HG HENV VBASE VOBJ A1 A0 MI AINV A lo H vi vv q tag v VEP AI Clg"] Lemma dit_entry :
    realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               bvmap_empty (Z_to_bv 64 vep_do_include_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.
  Proof.
    rewrite A0, A1. unfold vep_do_include_entry.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH].
    prelims.
    pose proof VEPC0 as VEPC. clear VEPC0. unfold vep_cells in VEPC. rewrite EVC in VEPC.
    destruct HENV as [GLOB HOBJ].
    (first [ pose proof (GLOB) as dR_23; dand4 dR_23 as EBSS BSS CP [cnt CNT] | pose proof GLOB as (EBSS & BSS & CP & [cnt CNT]) ]). cbn [al_segs LayoutP0] in BSS, CP, CNT. cbn [vi_bss VI0] in EBSS. rewrite EBSS in BSS.
    (first [ pose proof (HOBJ) as dR_24; dand3 dR_24 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]).
    (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
    pose proof IMG as (_ & _ & GVSC & _). unfold GOT_vsc in GVSC.
    pose proof (munch_refl W m) as MU. cbv delta [W] in MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof MI as MIw. pose proof ST as STw. hide MI. hide ST.
    clear HMH || idtac. hide_disj. hide_slow.
    apply rz_go; [exact MDH | exact MDL |].
    carve_frame 112%nat STw.
    (* [comment removed for export] *)
    do 14 zstep.
    zstep. zstep. zstep. if_cases KT; zify_cond KT. 2:{ exfalso. clear - KT. lia. } clear KT.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small' (v Femptytag)) by (clear - HET; unhide HET; destruct HET; lia).
    zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      clear BSS CP VC WK GVSC.
      apply rz_stop.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        eapply (seg_main2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx);
        [ exact MU | exact WM | exact MIw | exact STw | exact FR | unfold vep_cells; rewrite EVC; exact VEPC | exact CNT ] end.
    - (* [comment removed for export] *)
      do 15 zstep.
      zstep. carve_frame 48%nat STw. do 8 zstep.
      lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ => release_frame FR2 STw (bv_unsigned sp + -112)%Z end.
      clear BSS CP VC WK GVSC.
      apply rz_stop.
      destruct (rw_cells_forget _ _ _ _ CNT) as [c' CNT']. cbn [cells_size csize Nat.add] in CNT'.
      lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        eapply (seg_main2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx);
        [ exact MU | exact WM | exact MIw | exact STw | exact FR | unfold vep_cells; rewrite EVC; exact VEPC | exact CNT' ] end.
  Qed.

End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem vep_do_include_tag_ok {AI : AllocSpec LayoutP0} : vep_do_include_tag_stmt.
Proof.
  unfold vep_do_include_tag_stmt. intros until T.
  intros AINV MI A0 A1 VOBJ VBASE HENV HG IMG HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBUD NBUD HVI TP SP16 RA2 ST CEIL LO SPH K.
  eapply dit_entry; eassumption.
Qed.

End CEIL.
