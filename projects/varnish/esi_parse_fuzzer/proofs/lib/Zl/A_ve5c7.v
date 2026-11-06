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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4.

Module A_VS41f.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpya4 AIcp3q7 AIcpq85 AIcpnnp AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSe3i A_VSa8f.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
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
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Definition VSB_vprintf_entry : Z := 0x8a350.
Definition VSB_printf_entry : Z := 0x8a8a4.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma got_ssp_cell : forall v, consts_hold LPA v -> ro_cells rsegs v GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)].
Proof. intros v CH. apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity. Qed.

Lemma guard_any : forall M : mem, exists g, ro_cells rsegs M SSP_GUARD [C8 g].
Proof.
  intros M. destruct (rw_C8_any M SSP_GUARD ltac:(unfold SSP_GUARD; lia) ltac:(unfold SSP_GUARD; lia)
                        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [g [R _]].
  exists g. exact R.
Qed.

Lemma ssp_any : forall v, consts_hold LPA v -> exists canary, ssp_cells v canary.
Proof. intros v CH. destruct (guard_any v) as [g G]. exists g. split; [exact (got_ssp_cell v CH)| exact G]. Qed.

End CEIL.

(* [comment removed for export] *)
Section Cells.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variable v : mem.
  Hypothesis CH : consts_hold LPA v.
  Local Ltac cl := apply (consts_lookup v _ _ CH); vm_compute; reflexivity.

  #[using="CH"] Lemma strnlen_icpt_cells_of_consts : strnlen_icpt_cells v.
  Proof.
    split; [apply asan_inited_cell_of_bytes; cl|].
    split; [apply ro_C8_of_bytes; cl|].
    split; [apply ro_C8_of_bytes; cl|].
    split. { eapply (ro_C1_of_nth v 0x1466e8 pa_common_flags_bytes 251); [cl| reflexivity]. }
    split; [apply ro_C8_of_bytes; cl|].
    exact (map_cells_of_consts v CH).
  Qed.

  #[using="CH"] Lemma vficpt_cells_of_consts : vficpt_cells v.
  Proof.
    unfold vficpt_cells. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
    first [ apply asan_inited_cell_of_bytes; cl
          | apply ro_C8_of_bytes; cl
          | apply ro_C4_of_bytes; cl
          | (eapply (ro_C1_of_nth v 0x1466e8 pa_common_flags_bytes 84); [cl| reflexivity])
          | exact (map_cells_of_consts v CH)
          | exact (asan_memset_cells_of_consts v CH)
          | exact (asan_memcpy_cells_of_consts v CH) ].
  Qed.

  (* [comment removed for export] *)
  #[using="CH"] Lemma vsnicpt_cells_of_consts : bytes_at rsegs v 0xaa910 (le8 (Z_to_bv 64 0xa14f4)) -> vsnicpt_cells v.
  Proof.
    intros R. unfold vsnicpt_cells. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
    first [ apply asan_inited_cell_of_bytes; cl
          | (apply ro_C8_of_bytes; exact R)
          | apply ro_C8_of_bytes; cl
          | (eapply (ro_C1_of_nth v 0x1466e8 pa_common_flags_bytes 84); [cl| reflexivity]) ].
  Qed.
End Cells.

(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition vsnreal_ok : Prop := forall v, consts_hold LPA v -> bytes_at rsegs v 0xaa910 (le8 (Z_to_bv 64 0xa14f4)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sfi_intro : forall v A la D n HS hs SB K zlo zhi,
  consts_hold LPA v -> vsnreal_ok ->
  range_ok v A la -> range_ok v D (Z.of_nat n) -> hs_shadow v HS hs ->
  bytes_at rsegs v SB (zeros K) -> zsh_bounds SB K zlo zhi -> (2147446784 <= SB)%Z (* [comment removed for export] *) ->
  sfi A la D n HS hs SB K zlo zhi v.
Proof.
  intros v A la D n HS hs SB K zlo zhi CH VR RA RD HSS ZB ZBD SBL.
  split; [| exact (vsnicpt_cells_of_consts v CH (VR v CH))].
  split; [| split; [exact (asan_memset_cells_of_consts v CH)| exact (vficpt_cells_of_consts v CH)]].
  split; [exact (asan_memcpy_cells_of_consts v CH)|]. split; [exact (strnlen_icpt_cells_of_consts v CH)|].
  split; [exact RA|]. split; [exact RD|]. split; [exact HSS|]. split; [exact ZB|]. split; [exact ZBD| exact SBL].
Qed.

End CEIL2.

(* [comment removed for export] *)
Section SS.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma zsh_of_stack_shadow : forall (v : mem) SB N lo hi lo' hi',
    stack_shadow LPA v SB N lo hi -> 0 <= lo -> lo + 64 <= lo' -> lo' <= hi' -> hi' + 64 <= hi -> hi' + 16 <= 2^47 -> kHighMemBeg <= lo' ->
    bytes_at rsegs v SB (zeros (Z.to_nat N)) /\ zsh_bounds SB (Z.to_nat N) lo' hi'.
  Proof.
    (intros v SB N lo hi lo' hi'; (first [ intro dR_11; dand6 dR_11 as B N0 Lq Hh SLO T | intros (B & N0 & Lq & Hh & SLO & T) ]); intros L0 H1 H2 H3 H4 H5).
    split; [exact B|]. unfold zsh_bounds, sha, shadow_off, kHighShadowEnd_z, kHighMemBeg_z. unfold sh, kShadowOffset, kHighMemBeg in *. all_app_facts.
    rewrite Z2Nat.id by lia.
    assert (lo / 8 + 8 <= lo' / 8) by (Z.div_mod_to_equations; lia).
    assert (hi' / 8 + 8 <= hi / 8) by (Z.div_mod_to_equations; lia).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.
  Lemma stack_shadow_again : forall (v v' : mem) SB N lo hi K,
    stack_shadow LPA v SB N lo hi -> bytes_at rsegs v' SB (zeros K) -> K = Z.to_nat N -> stack_shadow LPA v' SB N lo hi.
  Proof. intros v v' SB N lo hi K (B & R) ZB ->. split; [exact ZB| exact R]. Qed.
End SS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : AIcptdg.pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis VSNREAL : vsnreal_ok.

  (* [comment removed for export] *)
  Definition str_home (A : AS) (S : Z) (v : vsb_rec) (HS : Z) (hs : list byte) : Prop :=
    (hs = [] /\ (HS = 0 \/ 0x10000 <= HS < 0x60a000) (* [comment removed for export] *)) \/ exists q k, a_live A q = Some k /\ q <= HS /\ HS + Z.of_nat (length hs) <= q + k /\ q <> S /\ q <> vb_buf v
                       /\ In (Z_to_bv 8 0) hs.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (S : Z) (vr : vsb_rec)
            (Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (lo SB N : Z) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) S vr false.
  (* [comment removed for export] *)
  Hypothesis HF : forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT.   (* [comment removed for export] *)
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  Hypothesis AFR : forall v, cenv v -> range_ok v Afmt la.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis VAA : va_area (aview A0 m0) VA slots.
  Hypothesis VLO : bv_unsigned sp <= VA.
  Hypothesis VHI : VA + 8 * Z.of_nat (length slots) <= 2^47.
  (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSL : SLOTS slots.
  Hypothesis HSB : bytes_at rsegs (aview A0 m0) HS hs.
  Hypothesis HSH : str_home A0 S vr HS hs.
  Hypothesis EM : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + Z.of_nat (length (OUT slots hs)) + 1) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 0 1.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VPRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      vsb_obj LPA A' v' S vr' false ->
      (vb_error vr <> 0 -> r = -1 /\ vr' = vr) ->
      (vb_error vr = 0 -> r = 0 /\ vb_error vr' = 0 /\
         (  vb_len vr' = vb_len vr + Z.of_nat (length (OUT slots hs))
         \/ (vb_len vr' = vb_size vr - 1 /\ vb_size vr' = vb_size vr /\ vb_buf vr' = vb_buf vr))) ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A0 q) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      frames_aged A0 A' 0 1 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      stk rsegs v' lo (bv_unsigned sp) ->
      va_area v' VA slots -> bytes_at rsegs v' HS hs ->
      stack_shadow LPA v' SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64) ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VPRINTF_STACK
               (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
               (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj HLA (conj HOUT (conj HOUT1 (conj P1 (conj P2 (conj PCM (conj FBY (conj VSNREAL
      (conj AINV00 (conj SOBJ (conj HF (conj ARL (conj ART (conj AFR (conj VAA (conj VLO (conj VHI (conj HPRE (conj HSL (conj HSB (conj HSH
      (conj EM (conj LBM (conj NLV (conj SCM (conj PRM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO (conj SPHI (conj STKSH K))))))))))))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Definition fr_alloc1 (A A1 : AS) (ff : Z) : Prop :=
       a_frame A ff = None /\ a_frame A1 ff = Some (1, 0%nat)
    /\ (forall g k' age', g <> ff -> a_frame A g = Some (k', age') -> a_frame A1 g = Some (k', if Z.eqb k' 1 then Datatypes.S age' else age'))
    /\ (forall g, g <> ff -> a_frame A g = None -> a_frame A1 g = None)
    /\ (forall q0, a_live A1 q0 = a_live A q0) /\ a_livebytes A1 = a_livebytes A /\ a_tinycred A1 = a_tinycred A /\ a_nlive A1 = a_nlive A
    /\ a_seccred A1 = a_seccred A
    /\ a_primcred A1 = a_primcred A   (* [comment removed for export] *)
    /\ ff mod 32 = 0 /\ app_range LPA ff 128 (* [comment removed for export] *) /\ ff + 128 <= alloc_ceiling /\ 0 <= sh ff /\ sh ff + 16 <= SHMAX.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K STKSH SPHI LO CEIL SP16 TP FY SCM PRM NLV LBM EM HSH HSB HSL HPRE VHI VLO VAA AFR ART ARL HF SOBJ AINV00 Afmt VSNREAL FBY PCM SLOTS fbytes P2 P1 HOUT1 HOUT HLA PRE nargs la FMT"] Lemma vp_exit : forall (xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs4 xs6 xs7 xs8 xs9 xs10 : word) (d ff r : Z) (A1 A2 : AS) (m2 : mem) (md2 : Model)
                       (vr2 : vsb_rec) (j88 fj shj : list byte),
    0 <= d <= 16 ->
    ainv A2 m2 md2 -> mem_inv rsegs (aview A2 m2) -> amd_frame md0 md2 ->
    stk rsegs (aview A2 m2) lo (bv_unsigned sp + -192 - d) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -192 - d) [CB 88 j88] ->
    stk rsegs (aview A2 m2) (bv_unsigned sp + -192 - d + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -104)
             [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    fr_alloc1 A0 A1 ff -> frames_same A1 A2 ->
    length fj = 120%nat -> rw_cells rsegs (aview A2 m2) ff [CB 120 fj] ->
    length shj = 16%nat -> rw_cells rsegs (aview A2 m2) (sh ff) [CB 16 shj] ->
    vsb_obj LPA A2 (aview A2 m2) S vr2 false ->
    (vb_error vr <> 0 -> r = -1 /\ vr2 = vr) ->
    (vb_error vr = 0 -> r = 0 /\ vb_error vr2 = 0 /\
       (vb_len vr2 = vb_len vr + Z.of_nat (length (OUT slots hs)) \/ (vb_len vr2 = vb_size vr - 1 /\ vb_size vr2 = vb_size vr /\ vb_buf vr2 = vb_buf vr))) ->
    vb_len vr <= vb_len vr2 <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
    vb_size vr <= vb_size vr2 <= Z.max (vb_size vr) (vb_len vr2 + 4096) ->
    (vb_buf vr2 = vb_buf vr \/ (a_live A1 (vb_buf vr2) = None /\ a_live A2 (vb_buf vr) = None)) ->
    (forall p, p <> vb_buf vr -> p <> vb_buf vr2 -> a_live A2 p = a_live A1 p) ->
    a_livebytes A2 = a_livebytes A1 + vb_size vr2 - vb_size vr ->
    a_tinycred A2 = a_tinycred A1 -> a_nlive A2 = a_nlive A1 ->
    a_seccred A1 - (vsb_pot vr2 - vsb_pot vr) <= a_seccred A2 <= a_seccred A1 ->
    a_primcred A1 - (vsb_ppot vr2 - vsb_ppot vr) <= a_primcred A2 <= a_primcred A1 ->   (* [comment removed for export] *)
    va_area (aview A2 m2) VA slots -> bytes_at rsegs (aview A2 m2) HS hs ->
    stack_shadow LPA (aview A2 m2) SB N (bv_unsigned sp - (192 + 16 + (80 + ASTK)) - 64) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned A2) (bv_unsigned sp) VPRINTF_STACK
           (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
           (fun a => frm ff 1 a \/ newblk (vb_buf vr2) (vb_size vr2) a) (aview A0 m0) (aview A2 m2) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -192 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - d))
                                    a0 a1 (Z_to_bv 64 r) a3 a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 S) xs4 (Z_to_bv 64 ff) xs6 xs7
                                    xs8 xs9 xs10 (Z_to_bv 64 (sh ff)) t3 t4 t5 t6)
                               F (Z_to_bv 64 0x8a6c8) fc None m2 (seg_rom rsegs)) md2) T.
  Proof.
    touch_all. intros until shj. intros D0 AINV MI MDF STlo SCR STpad FRH FA FS12 LFJ FFC LSH SHC SOBJ2 KE KO LEN2 SZ2 REL2 LIVEq2 LB2 TC2 NL2 SC2 PR2 VAA2 HSB2 STKSH2 CF02.
    prelims.
    (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PR1 FAL FLO FHI SH0 SH1 | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PR1 & FAL & FLO & FHI & SH0 & SH1) ]). rewrite SHMAX_val in SH1. all_app_facts.
    pose proof (as_minv LPA A2 _ _ AINV) as [_ MH].
    assert (FF2 : a_frame A2 ff = Some (1, 0%nat)) by (rewrite (FS12 ff); exact FF1).
    (* [comment removed for export] *)
    release_frame SCR STlo (bv_unsigned sp + -192 - d + 88).
    pose proof (stk_merge rsegs _ _ _ _ STlo STpad ltac:(keeplia D0 LO CEIL ACV)) as STm. clear STlo STpad.
    destruct (stk_carve rsegs _ lo _ 88 STm ltac:(keeplia D0 LO CEIL ACV)) as [STlo [j88' FRL]]. clear STm.
    change (Z.of_nat 88) with 88 in STlo, FRL. replace (bv_unsigned sp + -104 - 88) with (bv_unsigned sp + -192) in STlo, FRL by lia.
    assert (FR : rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -192)
                   [CB 88 j88'; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (proj2 (rw_cells_app rsegs _ _ [CB 88 j88'] _)). split; [exact FRL|]. cbn [cells_size csize Nat.add].
      eapply rwc_eq; [exact FRH| lia]. }
    clear FRL FRH.
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -192 - d) _ STlo ltac:(keeplia D0 LO CEIL ACV)) as [STlo' STpad]. clear STlo. rename STlo' into STlo.
    (* [comment removed for export] *)
    (first [ pose proof ((fframe_flag A2 m2 md2 ff 1 0%nat AINV FF2)) as dR_2; dex2 dR_2 as fa fb; dand6 dR_2 as FAW FB FRO FRW FOW FNI | pose proof ((fframe_flag A2 m2 md2 ff 1 0%nat AINV FF2)) as dR_2; dand8 dR_2 as fa fb FAW FB FRO FRW FOW FNI | destruct (fframe_flag A2 m2 md2 ff 1 0%nat AINV FF2) as (fa & fb & FAW & FB & FRO & FRW & FOW & FNI) ]).
    change (fsize 1) with 128 in FRO. replace (ff + 128 - 8) with (ff + 120) in FRO by lia.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (SOBJ2) as dR_4; dand6 dR_4 as _ VINV2 VLS VLB VNE _ | pose proof SOBJ2 as (_ & VINV2 & VLS & VLB & VNE & _) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 1 0%nat _ _ AINV FF2 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 1 0%nat _ _ AINV FF2 VLB) as DJfB.
    change (fsize 1) with 128 in DJfS, DJfB.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLS FOW) as OWS.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLB FOW) as OWB.
    pose proof (owned_outside_fframe A2 m2 md2 ff 1 0%nat _ AINV FF2 FOW) as [OWF OWSH].
    change (fsize 1) with 128 in OWF, OWSH. change (128 / 8) with 16 in OWSH.
    (* [comment removed for export] *)
    pose proof (bytes_at_bound _ _ _ _ VAA2) as VAB. rewrite u64s_length in VAB.
    hide DJfS. hide DJfB. hide OWS. hide OWB. hide DSB. hide HSB2. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(sh ff, sh ff + 16); (ff, ff + 8); (fa, fa + 1)] (aview A2 m2)) as MU.
    pose proof (wmono_refl rsegs (aview A2 m2)) as WM.
    assert (CFR : client_fp_rel LPA A2 [ff] (aview A2 m2) [(sh ff, sh ff + 16); (ff, ff + 8); (fa, fa + 1)]).
    { unfold client_fp_rel. split; [| split; [| split; [| exact I]]].
      - right; right; right; left. exists ff, 1, 0%nat. split; [exact FF2|]. change (fsize 1 / 8) with 16. lia.
      - right; right; left. exists ff, 1, 0%nat. split; [exact FF2|]. change (fsize 1) with 128. lia.
      - right; right; right; right. exists ff, 1, 0%nat, (Z_to_bv 64 fa). split; [left; reflexivity|]. split; [exact FF2|].
        split; [exact FB|]. rewrite unsigned_lit by (keeplia FAW ACV); split; reflexivity. }
    hide FB.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. fix_neg. sb1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. fix_neg. do 16 sb1.
    (* [comment removed for export] *)
    zstep. unhide OWS. unhide OWB. try clear FRO. sb1. hide OWS. hide OWB. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    do 13 zstep. zstep.
    try replace (bv_unsigned sp + -192 + 192) with (bv_unsigned sp) by lia.
    try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with ST1 : stk _ ?mq lo _, ST2 : stk _ ?mq (bv_unsigned sp + -192 - d) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (stk_merge rsegs mq _ _ _ ST1 ST2 ltac:(keeplia D0 LO CEIL ACV)) as STm; clear ST1 ST2 end.
    lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -192) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      release_frame FRq STm (bv_unsigned sp) end.
    (* [comment removed for export] *)
    lazymatch goal with FLq : rw_cells _ ?mq fa [C1 ?b] |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (flag_cleared (Clg:=Clg) mq fa FLq FNI ltac:(keeplia FAW ACV)) as FL end.
    unhide FB. astop_rel1 AINV FF2 FB MU WM CFR FL.
    (first [ pose proof ((as_release_spec LPA A2 m2 md2 ff 1 0%nat AINV FF2)) as dR_5; dand11 dR_5 as RN RO RL RLB RTC RSC RPC RNL RH RE ROW | destruct (as_release_spec LPA A2 m2 md2 ff 1 0%nat AINV FF2) as (RN & RO & RL & RLB & RTC & RSC & RPC & RNL & RH & RE & ROW) ]).
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ r (a_release A2 ff) m1 md1 vr2);
      [ assumption | assumption
      | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]]
      | (* [comment removed for export] *)
        unhide DJfS; unhide DJfB; unhide OWS; unhide OWB;
        (first [ pose proof (SOBJ2) as dR_6; dand6 dR_6 as XC XI XLS XLB XNE XB | pose proof SOBJ2 as (XC & XI & XLS & XLB & XNE & XB) ]); split; [| split; [exact XI| split; [rewrite RL; exact XLS| split; [rewrite RL; exact XLB| split; [exact XNE|]]]]];
        [ eapply (rw_cells_munch LPA); [exact XC| exact MU| exact WM|]; rewrite vsb_cells_size; change (Z.of_nat 40) with 40;
          intros a Ha; cbn; keeplia Ha DJfS OWS SH1 Slo
        | (first [ dex1 XB as bs; dand3 XB as [UB UW] LENx NULx | dand4 XB as bs [UB UW] LENx NULx | destruct XB as (bs & [UB UW] & LENx & NULx) ]); exists bs; split; [| split; [exact LENx| exact NULx]]; split;
          [ eapply (bytes_at_munch LPA); [exact UB| exact MU| rewrite LENx; intros a Ha; cbn; keeplia Ha DJfB OWB SH1 Blo]
          | eapply wr_at_transport; [exact UW| exact WM] ] ]
      | exact KE | exact KO | exact LEN2 | exact SZ2
      | intros p Hp1 Hp2; rewrite RL, (LIVEq2 p Hp1 Hp2); apply LV1
      | destruct REL2 as [E|[E1 E2]]; [left; exact E| right; split; [rewrite <- (LV1 (vb_buf vr2)); exact E1| rewrite RL; exact E2]]
      | eapply (frames_aged_alloc_release A0 A1 A2 m2 md2 ff 1); [right; reflexivity| exact FN| exact FF1| exact AGE| exact NONE| exact FS12| exact AINV| exists 0%nat; exact FF2]
      | rewrite RLB, LB2, LB1; reflexivity
      | rewrite RTC, TC2, TC1; reflexivity
      | rewrite RNL, NL2, NL1; reflexivity
      | rewrite RSC; try (generalize alloc_ceiling_val); clear - SC2 SC1; try pose proof alloc_ceiling_val as ACV__; lia
      | rewrite RPC; clear - PR2 PR1; lia (* [comment removed for export] *)
      | assumption
      | | | | ]
    end.
    - (* [comment removed for export] *)
      unfold va_area in *. eapply (bytes_at_munch LPA); [exact VAA2| exact MU|]. rewrite u64s_length. intros a Ha. cbn. keeplia Ha VAB VLO SH1 FHI FAW LO CEIL ACV SPR.
    - (* [comment removed for export] *)
      unhide HSB2. pose proof HSH as [[E EHS]|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL)].
      + rewrite E. apply bytes_at_nil. pose proof (bytes_at_bound _ _ _ _ HSB2) as Bq. keeplia Bq.
      + assert (LQ2 : a_live A2 hq = Some hk).
        { rewrite (LIVEq2 hq NQB); [rewrite (LV1 hq); exact LQ|].
          intros Ehq. destruct REL2 as [Eb|[Eb _]]; [exact (NQB (eq_trans Ehq Eb))|]. rewrite <- Ehq, (LV1 hq), LQ in Eb. discriminate Eb. }
        pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 1 0%nat _ _ AINV FF2 LQ2) as DJfQ. change (fsize 1) with 128 in DJfQ.
        pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV LQ2 FOW) as OWQ.
        (first [ pose proof ((live_geomP LPA A2 m2 md2 hq _ AINV LQ2)) as dR_8; dand4 dR_8 as _ _ Qlo _ | pose proof (live_geomP LPA A2 m2 md2 hq _ AINV LQ2) as (_ & _ & Qlo & _) ]). unfold kHighMemBeg in Qlo. all_app_facts.
        eapply (bytes_at_munch LPA); [exact HSB2| exact MU|]. intros a Ha. cbn. keeplia Ha Q1 Q2 DJfQ OWQ SH1 Qlo.
    - (* [comment removed for export] *)
      assert (M0 : 0 <= bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) by keeplia CEIL LO ACV.
      assert (M1 : bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64 <= Z.max (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) alloc_ceiling) by (clear; lia).
      assert (M2 : Z.max (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) alloc_ceiling <= bv_unsigned sp + 64) by keeplia CEIL LO ACV.
      pose proof (stack_shadow_sub LPA _ SB N _ _ _ _ STKSH2 M1 (Z.le_refl _) M0) as SSx.
      (first [ pose proof ((crange_stack_shadow (Clg:=Clg) LPA A2 m2 md2 SB N _ _ AINV SSx ltac:(clear; lia))) as dR_9; dand3 dR_9 as _ _ CRS | pose proof (crange_stack_shadow (Clg:=Clg) LPA A2 m2 md2 SB N _ _ AINV SSx ltac:(clear; lia)) as (_ & _ & CRS) ]). clear SSx M0 M1 M2.
      (first [ pose proof (STKSH2) as dR_10; dand6 dR_10 as SSB SSN _ _ SSC SST | pose proof STKSH2 as (SSB & SSN & _ & _ & SSC & SST) ]).
      pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *).
      eapply stack_shadow_again; [exact STKSH2| | reflexivity].
      eapply (bytes_at_munch LPA); [exact SSB| exact MU|]. rewrite zeros_length, Z2Nat.id by exact SSN.
      intros a Ha. cbn.
      assert (NOa : ~ owned A2 a). { destruct (CRS (a - SB) ltac:(keeplia Ha)) as [X _]. replace (SB + (a - SB)) with a in X by lia. exact X. }
      assert (NFa : a <> fa) by (intros ->; exact (NOa FOW)).
      unfold kHighMemBeg in SST. all_app_facts. keeplia Ha NFa SSC SST SHC8 SH1 FHI FLO ACV.
    - (* [comment removed for export] *)
      ufs. eapply (cframe_release (owned A0) (owned A2) (owned (a_release A2 ff))); [exact CF02| exact MU| | keeplia LO CEIL ACV| keeplia SPR| | | intros a X; right; exact X].
      + intros a Ha NO. cbn [outside] in NO.
        assert (CS : sh ff <= a < sh ff + 16 \/ ff <= a < ff + 8 \/ a = fa) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia). clear NO.
        destruct CS as [X|[X|X]]; [left; left; right; change (fsize 1 / 8) with 16; exact X| left; left; left; change (fsize 1) with 128; keeplia X| right; rewrite X; exact FOW].
      + intros i Hi. cbn. keeplia Hi SH1 FHI FAW LO CEIL ACV.
      + intros a Oa. apply ROW in Oa. destruct Oa as [X|[X|X]]; [left; exact X| right; left; left; change (fsize 1) with 128 in *; keeplia X| right; left; right; exact X].
  Qed.
End S.
End A_VS41f.


Module A_VSqtv.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpya4 AIcp3q7 AIcpq85 AIcpnnp AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSe3i A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47.B_Cf6tv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : AIcptdg.pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis VSNREAL : vsnreal_ok.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (S : Z) (vr : vsb_rec)
            (Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (lo SB N : Z) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) S vr false.
  (* [comment removed for export] *)
  Hypothesis HF : forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT.   (* [comment removed for export] *)
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  Hypothesis AFR : forall v, cenv v -> range_ok v Afmt la.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis VAA : va_area (aview A0 m0) VA slots.
  Hypothesis VLO : bv_unsigned sp <= VA.
  Hypothesis VHI : VA + 8 * Z.of_nat (length slots) <= 2^47.
  (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSL : SLOTS slots.
  Hypothesis HSB : bytes_at rsegs (aview A0 m0) HS hs.
  Hypothesis HSH : str_home A0 S vr HS hs.
  Hypothesis EM : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + Z.of_nat (length (OUT slots hs)) + 1) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 0 1.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VPRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      vsb_obj LPA A' v' S vr' false ->
      (vb_error vr <> 0 -> r = -1 /\ vr' = vr) ->
      (vb_error vr = 0 -> r = 0 /\ vb_error vr' = 0 /\
         (  vb_len vr' = vb_len vr + Z.of_nat (length (OUT slots hs))
         \/ (vb_len vr' = vb_size vr - 1 /\ vb_size vr' = vb_size vr /\ vb_buf vr' = vb_buf vr))) ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A0 q) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      frames_aged A0 A' 0 1 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      stk rsegs v' lo (bv_unsigned sp) ->
      va_area v' VA slots -> bytes_at rsegs v' HS hs ->
      stack_shadow LPA v' SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64) ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VPRINTF_STACK
               (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
               (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj HLA (conj HOUT (conj HOUT1 (conj P1 (conj P2 (conj PCM (conj FBY (conj VSNREAL
      (conj AINV00 (conj SOBJ (conj HF (conj ARL (conj ART (conj AFR (conj VAA (conj VLO (conj VHI (conj HPRE (conj HSL (conj HSB (conj HSH
      (conj EM (conj LBM (conj NLV (conj SCM (conj PRM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO (conj SPHI (conj STKSH K))))))))))))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Definition SCRATCH (ff : Z) (j0 j16 : list byte) : list cell :=
    [CB 24 j0; C8 (Z_to_bv 64 2147450880);
     C8 (Z_to_bv 64 ((S + 4) / 8 + 2147450880)); C8 (Z_to_bv 64 (S + 4)); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 Afmt); CB 16 j16; C8 (Z_to_bv 64 ff)].

  (* [comment removed for export] *)
  Let vp_exit' := vp_exit FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY VSNREAL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 S vr Afmt VA slots HS hs lo SB N T AINV00 SOBJ HF ARL ART AFR VAA VLO VHI HPRE HSL HSB HSH EM LBM NLV SCM PRM FY TP SP16 CEIL LO SPHI STKSH K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="vp_exit' K STKSH SPHI LO CEIL SP16 TP FY SCM PRM NLV LBM EM HSH HSB HSL HPRE VHI VLO VAA AFR ART ARL HF SOBJ AINV00 VSNREAL FBY PCM SLOTS fbytes P2 P1 HOUT1 HOUT HLA PRE nargs la FMT"] Lemma vp_tail : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (d ff : Z) (A1 A2 : AS) (m2 : mem) (md2 : Model)
                       (vq : vsb_rec) (j0 j16 fj shj : list byte),
    let L := Z.of_nat (length (OUT slots hs)) in
    0 <= d <= 16 ->
    ainv A2 m2 md2 -> mem_inv rsegs (aview A2 m2) -> amd_frame md0 md2 ->
    stk rsegs (aview A2 m2) lo (bv_unsigned sp + -192 - d) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -192 - d) (SCRATCH ff j0 j16) ->
    stk rsegs (aview A2 m2) (bv_unsigned sp + -192 - d + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -104)
             [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    fr_alloc1 A0 A1 ff ->
    frames_same A1 A2 ->
    length fj = 120%nat -> rw_cells rsegs (aview A2 m2) ff [CB 120 fj] ->
    length shj = 16%nat -> rw_cells rsegs (aview A2 m2) (sh ff) [CB 16 shj] ->
    vsb_obj LPA A2 (aview A2 m2) S vq false ->
    vb_error vr = 0 -> vb_error vq = 0 -> vb_len vq = vb_len vr ->
    (L <= vb_size vq - vb_len vr - 1 \/ (vb_size vq = vb_size vr /\ vb_buf vq = vb_buf vr)) ->
    vb_size vr <= vb_size vq <= Z.max (vb_size vr) (vb_len vr + L + 4096) ->
    (vb_buf vq = vb_buf vr \/ (a_live A1 (vb_buf vq) = None /\ a_live A2 (vb_buf vr) = None)) ->
    (forall p, p <> vb_buf vr -> p <> vb_buf vq -> a_live A2 p = a_live A1 p) ->
    a_livebytes A2 = a_livebytes A1 + vb_size vq - vb_size vr ->
    a_tinycred A2 = a_tinycred A1 -> a_nlive A2 = a_nlive A1 ->
    a_seccred A1 - (vsb_pot vq - vsb_pot vr) <= a_seccred A2 <= a_seccred A1 ->
    a_primcred A1 - (vsb_ppot vq - vsb_ppot vr) <= a_primcred A2 <= a_primcred A1 ->   (* [comment removed for export] *)
    va_area (aview A2 m2) VA slots -> bytes_at rsegs (aview A2 m2) HS hs ->
    stack_shadow LPA (aview A2 m2) SB N (bv_unsigned sp - (192 + 16 + (80 + ASTK)) - 64) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned A2) (bv_unsigned sp) VPRINTF_STACK
           (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
           (fun a => frm ff 1 a \/ newblk (vb_buf vq) (vb_size vq) a) (aview A0 m0) (aview A2 m2) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -192 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - d))
                                    a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 S) (Z_to_bv 64 ((S + 8) / 8 + 2147450880))
                                    (Z_to_bv 64 ((S + 16) / 8 + 2147450880)) (Z_to_bv 64 ((S + 24) / 8 + 2147450880))
                                    (Z_to_bv 64 (S + 24)) (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 L) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
                               F (Z_to_bv 64 0x8a5c8) fc None m2 (seg_rom rsegs)) md2) T.
  Proof.
    touch_all. intros until shj. cbv zeta. intros D0 AINV MI MDF STlo SCR STpad FRH FA FS12 LFJ FFC LSH SHC SOBJq E0 EQ0 LENQ FIT SZQ RELQ LIVEqQ LBQ TCQ NLQ SCQ PRQ VAA2 HSB2 STKSH2 CF02.
    prelims.
    pose proof FA as FA'. (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PR1 FAL FLO FHI SH0 SH1 | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PR1 & FAL & FLO & FHI & SH0 & SH1) ]). rewrite SHMAX_val in SH1. all_app_facts.
    pose proof (as_minv LPA A2 _ _ AINV) as [_ MH].
    assert (FF2 : a_frame A2 ff = Some (1, 0%nat)) by (rewrite (FS12 ff); exact FF1).
    pose proof (HOUT _ _ _ HPRE) as OL.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LPA A2 m2 md2 S vq false AINV SOBJq)) as dR_2; dand11 dR_2 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A2 m2 md2 S vq false AINV SOBJq) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof SOBJq as SO. vsb_open SO. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs U8 LBS _ | destruct VBUF as (bs & U8 & LBS & _) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 1 0%nat _ _ AINV FF2 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 1 0%nat _ _ AINV FF2 VLB) as DJfB.
    change (fsize 1) with 128 in DJfS, DJfB.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ S 40 AINV VLS) as SHS0. fold_cl_segs. fold_aview.
    change (shpat 40) with (repeat (Z_to_bv 8 0) 5) in SHS0.
    remember (repeat (Z_to_bv 8 0) 5) as zsS eqn:EzsS in SHS0.
    assert (LZS : Z.of_nat (length zsS) = 5) by (rewrite EzsS; reflexivity).
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(exact Shi)) as SHSB. rewrite SHMAX_val in SHSB. change ((40 + 7) / 8) with 5 in SHSB.
    pose proof (bytes_at_bound _ _ _ _ VAA2) as VAB. rewrite u64s_length in VAB.
    hide DJfS. hide DJfB. hide DSB. hide HSB2. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(S, S + 40)] (aview A2 m2)) as MU.
    pose proof (wmono_refl rsegs (aview A2 m2)) as WM.
    assert (CFP : client_fp LPA A2 (aview A2 m2) [(S, S + 40)]) by (cbn; split; [right; left; exists S, 40; split; [exact VLS| lia]| exact I]).
    unfold vsb_cells in VSBC. cbv delta [SCRATCH] in SCR.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    vrechk SHS0 EzsS (S + 16) 8 0. vrechk SHS0 EzsS (S + 24) 8 0.
    (* [comment removed for export] *)
    zstep. rewrite LENQ. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. unsign KU. klia KU. } clear KU.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    replace (vb_size vq - (vb_len vr + 1)) with (vb_size vq - vb_len vr - 1) by (clear; lia).
    (* [comment removed for export] *)
    lazymatch goal with |- evt ?segs ?Q (MS ?R ?F0 ?pc ?fc0 None ?m ?rom) =>
      eapply (evt_cut segs (fun ms => ms = MS (bvmap_set (Z_to_bv 5 13)
                                               (Z_to_bv 64 (Z.min (vb_size vq - vb_len vr - 1) (Z.of_nat (length (OUT slots hs))))) R)
                                            F0 (Z_to_bv 64 0x8a600) fc0 None m rom) Q);
      [ zstep; if_cases KM; zify_cond KM; rewrite !signed_lit_small in KM by (keeplia Vsz Vlen LENQ OL);
        [ apply evt_done; cbv beta; rewrite Z.min_l by (keeplia KM OL Vsz Vlen LENQ); simp_regs; reflexivity
        | zstep; apply evt_done; cbv beta; rewrite Z.min_r by (keeplia KM OL Vsz Vlen LENQ); simp_regs; reflexivity ]
      | let ms := fresh "ms" in intros ms ->; simp_regs ]
    end.
    set (mn := Z.min (vb_size vq - vb_len vr - 1) (Z.of_nat (length (OUT slots hs)))) in *.
    assert (MN : 0 <= mn <= Z.of_nat (length (OUT slots hs)) /\ mn <= vb_size vq - vb_len vr - 1) by (subst mn; keeplia Vsz Vlen LENQ OL).
    assert (MC : mn = Z.of_nat (length (OUT slots hs)) \/ (mn = vb_size vq - vb_len vr - 1 /\ vb_size vq = vb_size vr /\ vb_buf vq = vb_buf vr))
      by (subst mn; clear - FIT Vsz Vlen LENQ OL; try pose proof alloc_ceiling_val as ACV__; destruct FIT as [X|[X1 X2]]; [left; lia| destruct (Z.le_gt_cases (Z.of_nat (length (OUT slots hs))) (vb_size vq - vb_len vr - 1)); [left; lia| right; split; [lia| split; assumption]]]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    vrechk SHS0 EzsS (S + 24) 8 0.
    zstep. unhide DJfS. try clear U8. zstep. hide DJfS.
    zstep. if_cases KU; zify_cond KU. { exfalso. unsign KU. klia KU. } clear KU.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    rewrite Vfl in VSBC. unfold VSB_FLAGS_LIVE in VSBC.
    lazymatch goal with |- evt ?segs ?Q (MS ?R ?F0 ?pc ?fc0 None ?m ?rom) =>
      eapply (evt_cut segs (fun ms => exists x10 x13 x14 : word,
                              ms = MS (bvmap_set (Z_to_bv 5 10) x10 (bvmap_set (Z_to_bv 5 13) x13 (bvmap_set (Z_to_bv 5 14) x14 R)))
                                      F0 (Z_to_bv 64 0x8a668) fc0 None m rom) Q);
      [ zstep; if_cases KR; zify_cond KR;
        [ apply evt_done; cbv beta; do 3 eexists; simp_regs; reflexivity
        | zstep; zstep; zstep; zstep;
          (let T := fresh "SHT" in pose proof SHS0 as T; rewrite EzsS in T; shadow_addr T 4; clear T);
          zstep; lit0; chk_branch;
          lazymatch goal with VSBCq : rw_cells _ ?mx S _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            pose proof (rw_cells_read_sub rsegs _ _ _ 32 1 VSBCq ltac:(lia) ltac:(cbn; lia)) as RDF;
            match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end end;
          zstep; clear RDF; zstep;
          zstep; if_cases KF; zify_cond KF;
          [ apply evt_done; cbv beta; do 3 eexists; simp_regs; reflexivity
          | exfalso; try (generalize alloc_ceiling_val); clear - KF; try pose proof alloc_ceiling_val as ACV__; cbv in KF; lia] ]
      | let ms := fresh "ms" in let x10 := fresh "xa0" in let x13 := fresh "xa3" in let x14 := fresh "xa4" in
        (intros ms; (first [ intro dR_8; dand4 dR_8 as x10 x13 x14 -> | intros (x10 & x13 & x14 & ->) ])); simp_regs ]
    end.
    (* [comment removed for export] *)
    zstep. if_cases KA; zify_cond KA; [exfalso; rewrite ?signed_lit_small in KA by (keeplia Vsz Vlen LENQ OL MN); keeplia KA MN Vsz Vlen LENQ|]. clear KA.
    rewrite EQ0 in VSBC.
    vrechk SHS0 EzsS (S + 4) 4 0.
    zstep. zstep. zstep. zstep.
    try rewrite CellsX.sx32_zero. try (rewrite (unsigned_lit 0) by lia). try change (Z.b2z (0 <? 1) + -1)%Z with 0%Z.
    change (Z.b2z (0 <? 1)) with 1.
    (* [comment removed for export] *)
    astop AINV MU WM CFP.
    lazymatch goal with AIq : ainv A2 ?mq ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ => rename AIq into AINVt end.
    lazymatch goal with SCRq : rw_cells _ ?ma (bv_unsigned sp + -192 - d) _ |- _ =>
      destruct (rw_cells_forget rsegs _ _ _ SCRq) as [j88 SCR']; cbn [cells_size csize Nat.add] in SCR'; clear SCRq end.
    unhide_neqs. unhide DJfS. unhide DJfB. unhide DSB. unhide HSB2.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
    eapply (vp_exit' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff 0 A1 A2 mq mdq (vsb_set_len vq (vb_len vr + mn)) j88 fj shj);
      [ exact D0 | exact AINVt | assumption
      | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]]
      | assumption | exact SCR' | assumption | assumption | exact FA' | exact FS12 | exact LFJ | assumption | exact LSH | assumption
      | | | | | | | | | | | | | | | | ]   (* [comment removed for export] *)
    end.
    - (* [comment removed for export] *)
      unfold vsb_obj, vsb_set_len, vsb_cells. cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent].
      split. { rewrite EQ0, Vfl. unfold VSB_FLAGS_LIVE. assumption. }
      split. { unfold vsb_inv. cbn [vb_error vb_buf vb_size vb_len vb_flags vb_indent]. clear - VINV MN LENQ EQ0; try pose proof alloc_ceiling_val as ACV__. unfold vsb_inv in VINV.
               (first [ dand9 VINV as X1 X2 X3 X4 X5 X6 X7 X8 X9 | destruct VINV as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9) ]). rewrite EQ0. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; try lia. }
      split; [exact VLS|]. split; [exact VLB|]. split; [exact VNE|].
      (first [ pose proof (SOBJq) as dR_6; dand6 dR_6 as _ _ _ _ _ (bs' & U8' & LBS' & _) | pose proof SOBJq as (_ & _ & _ & _ & _ & (bs' & U8' & LBS' & _)) ]).
      exists bs'. cbn [vb_buf vb_size]. split; [| split; [exact LBS'| intros X; discriminate X]].
      split; [eapply (bytes_at_munch LPA); [exact (proj1 U8')| exact MU| rewrite LBS'; intros a Ha; cbn; keeplia Ha DSB]| eapply wr_at_transport; [exact (proj2 U8')| exact WM]].
    - intros NE; exfalso; exact (NE E0).
    - intros _. split; [reflexivity|]. unfold vsb_set_len. cbn [vb_error vb_len vb_size vb_buf]. split; [exact EQ0|].
      destruct MC as [X|(X1 & X2 & X3)]; [left; rewrite X; lia| right; split; [rewrite X1, X2; lia| split; [exact X2| exact X3]]].
    - unfold vsb_set_len. cbn [vb_len]. keeplia MN.
    - unfold vsb_set_len. cbn [vb_len vb_size]. destruct MC as [X|(X1 & X2 & X3)]; [keeplia SZQ X MN| keeplia X2 Vsz].
    - exact RELQ.
    - exact LIVEqQ.
    - exact LBQ.
    - exact TCQ.
    - exact NLQ.
    - unfold vsb_pot in *. unfold vsb_set_len. cbn [vb_size]. exact SCQ.
    - unfold vsb_ppot in *. unfold vsb_set_len. cbn [vb_size]. exact PRQ.   (* [comment removed for export] *)
    - unfold va_area in *. eapply (bytes_at_munch LPA); [exact VAA2| exact MU|]. rewrite u64s_length. intros a Ha. cbn. keeplia Ha VAB VLO LO CEIL ACV Shi.
    - eapply (bytes_at_munch LPA); [exact HSB2| exact MU|].
      pose proof HSH as [[E EHS]|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL)].
      + rewrite E. intros a Ha. cbn in Ha. exfalso. keeplia Ha.
      + assert (LQ2 : a_live A2 hq = Some hk).
        { rewrite (LIVEqQ hq NQB); [rewrite (LV1 hq); exact LQ|].
          intros Ehq. destruct RELQ as [Eb|[Eb _]]; [exact (NQB (eq_trans Ehq Eb))|]. rewrite <- Ehq, (LV1 hq), LQ in Eb. discriminate Eb. }
        pose proof (as_live_disjoint LPA A2 m2 md2 _ _ _ _ AINV LQ2 VLS NQS) as DQS.
        intros a Ha. cbn. keeplia Ha Q1 Q2 DQS.
    - lazymatch goal with SSq : stack_shadow _ ?mx SB N _ _ |- stack_shadow _ _ SB N _ _ =>
        (first [ pose proof (SSq) as dR_7; dand6 dR_7 as SSB SSN _ _ SSC SST | pose proof SSq as (SSB & SSN & _ & _ & SSC & SST) ]); eapply stack_shadow_again; [exact SSq| | reflexivity];
        eapply (bytes_at_munch LPA); [exact SSB| exact MU|]; rewrite zeros_length, Z2Nat.id by exact SSN;
        intros a Ha; cbn; unfold kHighMemBeg in SST; all_app_facts; keeplia Ha SST Slo end.
    - ufs. pose proof (proj1 (proj2 CF02)) as MP2.
      eapply (cframe_after _ _ _ _ _ _ (aview A0 m0) (aview A2 m2)); [exact CF02| exact MU| |
        eapply (mapped_munch _ _ _ _ _ MU); [keeplia SPR LO CEIL ACV| keeplia SPR| intros i Hi; cbn; keeplia Hi Shi CEIL LO| exact MP2]].
      intros a Ha NO. cbn [outside] in NO. right; left; right. keeplia Ha NO.
  Qed.
End S.
End A_VSqtv.


Module A_VS160.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpya4 AIcp3q7 AIcpq85 AIcpnnp AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSe3i A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47.B_Cf6tv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSqtv.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsnicpt_post, VSNPRINTF_ICPT_STACK in H.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : AIcptdg.pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis VSNREAL : vsnreal_ok.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (S : Z) (vr : vsb_rec)
            (Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (lo SB N : Z) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) S vr false.
  (* [comment removed for export] *)
  Hypothesis HF : forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT.   (* [comment removed for export] *)
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  Hypothesis AFR : forall v, cenv v -> range_ok v Afmt la.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis VAA : va_area (aview A0 m0) VA slots.
  Hypothesis VLO : bv_unsigned sp <= VA.
  Hypothesis VHI : VA + 8 * Z.of_nat (length slots) <= 2^47.
  (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSL : SLOTS slots.
  Hypothesis HSB : bytes_at rsegs (aview A0 m0) HS hs.
  Hypothesis HSH : str_home A0 S vr HS hs.
  Hypothesis EM : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + Z.of_nat (length (OUT slots hs)) + 1) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 0 1.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VPRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      vsb_obj LPA A' v' S vr' false ->
      (vb_error vr <> 0 -> r = -1 /\ vr' = vr) ->
      (vb_error vr = 0 -> r = 0 /\ vb_error vr' = 0 /\
         (  vb_len vr' = vb_len vr + Z.of_nat (length (OUT slots hs))
         \/ (vb_len vr' = vb_size vr - 1 /\ vb_size vr' = vb_size vr /\ vb_buf vr' = vb_buf vr))) ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A0 q) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      frames_aged A0 A' 0 1 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      stk rsegs v' lo (bv_unsigned sp) ->
      va_area v' VA slots -> bytes_at rsegs v' HS hs ->
      stack_shadow LPA v' SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64) ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VPRINTF_STACK
               (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
               (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj HLA (conj HOUT (conj HOUT1 (conj P1 (conj P2 (conj PCM (conj FBY (conj VSNREAL
      (conj AINV00 (conj SOBJ (conj HF (conj ARL (conj ART (conj AFR (conj VAA (conj VLO (conj VHI (conj HPRE (conj HSL (conj HSB (conj HSH
      (conj EM (conj LBM (conj NLV (conj SCM (conj PRM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO (conj SPHI (conj STKSH K))))))))))))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let SCRATCH' := SCRATCH S Afmt.
  Definition FFRAME (apc : word) (j3 j5 j9 : list byte) : list cell :=
    [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x17931); C8 (Z_to_bv 64 0x8a350); CB 8 j3; C8 (Z_to_bv 64 VA); CB 24 j5; C8 apc; CB 48 j9].

  Definition vp_iter_post (d ff : Z) (vq : vsb_rec) (m : mem) (xra : word) (j0 j16 j3 j5 j9 : list byte) : machine_state -> Prop :=
    fun ms => exists (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (bs1 : list byte) (m1 : mem),
      let L := Z.of_nat (length (OUT slots hs)) in
      ms = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -192 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - d))
                   (Z_to_bv 64 (vb_size vq - vb_len vq - 1)) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) (Z_to_bv 64 S) (Z_to_bv 64 ((S + 8) / 8 + 2147450880))
                   (Z_to_bv 64 ((S + 16) / 8 + 2147450880)) (Z_to_bv 64 ((S + 24) / 8 + 2147450880))
                   (Z_to_bv 64 (S + 24)) (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 L) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
              F (Z_to_bv 64 0x8a5a8) fc None m1 (seg_rom rsegs)
      /\ munch [(bv_unsigned sp + -192 - d - VSNPRINTF_ICPT_STACK, bv_unsigned sp + -192 - d); (vb_buf vq + vb_len vq, vb_buf vq + vb_size vq); (ff + 64, ff + 72)] m m1
      /\ wmono rsegs m m1 /\ mem_inv rsegs m1
      /\ stk rsegs m1 lo (bv_unsigned sp + -192 - d)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -192 - d) (SCRATCH' ff j0 j16)
      /\ rw_cells rsegs m1 ff (FFRAME (Z_to_bv 64 VA) j3 j5 j9)
      /\ rw_cells rsegs m1 S (vsb_cells vq)
      /\ u8arr rsegs m1 (vb_buf vq) bs1 /\ Z.of_nat (length bs1) = vb_size vq
      /\ ro_cells rsegs m1 Afmt FMT /\ va_area m1 VA slots /\ bytes_at rsegs m1 HS hs
      /\ stack_shadow LPA m1 SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64)
      /\ L < 2^31.

  (* [comment removed for export] *)
  #[using="K STKSH SPHI LO CEIL SP16 TP FY SCM PRM NLV LBM EM HSH HSB HSL HPRE VHI VLO VAA AFR ART ARL HF SOBJ AINV00 T vr A0 md0 m0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra VSNREAL FBY PCM SLOTS fbytes P2 P1 HOUT1 HOUT HLA PRE nargs la AI"] Lemma vp_iter : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs11 apc : word) (d ff : Z) (vq : vsb_rec)
                       (m : mem) (j0 j16 j3 j5 j9 bs : list byte),
    0 <= d <= 16 ->
    mem_inv rsegs m -> cenv m ->
    stk rsegs m lo (bv_unsigned sp + -192 - d) ->
    rw_cells rsegs m (bv_unsigned sp + -192 - d) (SCRATCH' ff j0 j16) ->
    rw_cells rsegs m ff (FFRAME apc j3 j5 j9) ->
    ff mod 32 = 0 -> app_range LPA ff 128 (* [comment removed for export] *) -> ff + 128 <= alloc_ceiling ->
    rw_cells rsegs m S (vsb_cells vq) -> vsb_inv vq false ->
    kHighMemBeg <= S -> S + 40 <= alloc_ceiling -> S mod 16 = 0 ->
    bytes_at rsegs m (sh S) (shpat 40) ->
    u8arr rsegs m (vb_buf vq) bs -> Z.of_nat (length bs) = vb_size vq ->
    app_range LPA (vb_buf vq) (vb_size vq) (* [comment removed for export] *) -> vb_buf vq + vb_size vq <= alloc_ceiling ->
    (S + 40 <= vb_buf vq \/ vb_buf vq + vb_size vq <= S) ->
    (ff + 128 <= S - 16 \/ S + 40 <= ff) -> (ff + 128 <= vb_buf vq - 16 \/ vb_buf vq + vb_size vq <= ff) ->
    vb_size vq <= 2^30 ->
    range_ok m (vb_buf vq + vb_len vq) (vb_size vq - vb_len vq) ->
    ro_cells rsegs m Afmt FMT -> va_area m VA slots -> bytes_at rsegs m HS hs -> hs_shadow m HS hs ->
    HS + Z.of_nat (length hs) <= lo -> (hs = [] \/ ff + 128 <= HS \/ HS + Z.of_nat (length hs) <= ff) ->
    ~ (vb_buf vq + vb_len vq < HS + Z.of_nat (length hs) /\ HS < vb_buf vq + vb_size vq) ->
    stack_shadow LPA m SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64) ->
    evt rsegs (vp_iter_post d ff vq m xra j0 j16 j3 j5 j9)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -192 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - d))
                   a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) (Z_to_bv 64 S) (Z_to_bv 64 ((S + 8) / 8 + 2147450880))
                   (Z_to_bv 64 ((S + 16) / 8 + 2147450880)) (Z_to_bv 64 ((S + 24) / 8 + 2147450880))
                   (Z_to_bv 64 (S + 24)) (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (S + 8)) xs11 (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8a4f4) fc None m (seg_rom rsegs)).
  Proof.
    touch_all. intros until bs. intros D0 MI CE ST SCR FFR FAL FLO FHI VSBC VINV Slo Shi S16 SHS U8 LBS Blo Bhi DSB DJfS DJfB VQ31 RD HFq VAAq HSBq HSS HSL' HFD HSD STKSH'. all_app_facts.
    prelims.
    pose proof (HOUT _ _ _ HPRE) as OL.
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    pose proof (sh_boundL (Clg:=Clg) ff 128 ltac:(keeplia FLO) ltac:(lia) ltac:(exact FHI)) as SHF1. rewrite SHMAX_val in SHF1. change ((128 + 7) / 8) with 16 in SHF1.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(lia) ltac:(exact Shi)) as SHSB. rewrite SHMAX_val in SHSB. change ((40 + 7) / 8) with 5 in SHSB.
    change (shpat 40) with (repeat (Z_to_bv 8 0) 5) in SHS.
    remember (repeat (Z_to_bv 8 0) 5) as zsS eqn:EzsS in SHS.
    assert (LZS : Z.of_nat (length zsS) = 5) by (rewrite EzsS; reflexivity).
    pose proof (bytes_at_bound _ _ _ _ VAAq) as VAB. rewrite u64s_length in VAB.
    pose proof (ro_cells_bound _ _ _ _ HFq) as AB. pose proof ART as ART'. rewrite <- HLA in ART'. unfold RO_TOP in ART'. unfold IMG_LO in ARL.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp + -192 - d - VSNPRINTF_ICPT_STACK, bv_unsigned sp + -192 - d);
                            (vb_buf vq + vb_len vq, vb_buf vq + vb_size vq); (ff + 64, ff + 72)] m) as MU.
    unfold VSNPRINTF_ICPT_STACK in MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    set (nD := Z.to_nat (vb_size vq - vb_len vq)).
    assert (END : Z.of_nat nD = vb_size vq - vb_len vq) by (subst nD; keeplia Vlen).
    destruct (zsh_of_stack_shadow m SB N _ _ (bv_unsigned sp + -192 - d - 7808) (bv_unsigned sp + -192 - d) STKSH'
                ltac:(keeplia SPR LO CEIL ACV) ltac:(keeplia D0) ltac:(keeplia D0) ltac:(keeplia D0) ltac:(keeplia SPHI D0) ltac:(unfold kHighMemBeg; keeplia LO CEIL ACV D0)) as [ZB ZBD].
    pose proof (sfi_intro m Afmt la (vb_buf vq + vb_len vq) nD HS hs SB (Z.to_nat N) _ _ (proj1 CE) VSNREAL (AFR m CE)
                  ltac:(rewrite END; exact RD) HSS ZB ZBD ltac:(pose proof (stack_shadow_pure _ _ _ _ _ STKSH') as SSP__; clear - SSP__ V16C; unfold sh, kShadowOffset in *; try pose proof alloc_ceiling_val as ACV__; lia)) as SFI.
    hide DSB. hide DJfS. hide DJfB. hide HSBq. unfold va_area in VAAq.
    unfold vsb_cells in VSBC. cbv delta [SCRATCH' SCRATCH] in SCR. cbv delta [FFRAME] in FFR.
    (* [comment removed for export] *)
    zstep. unhide DJfS. unhide DJfB. try clear ZB. zstep. hide DJfS. hide DJfB.
    (* [comment removed for export] *)
    vrechk SHS EzsS (S + 8) 8 0. vrechk SHS EzsS (S + 24) 8 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. unsign KU. klia KU. } clear KU.
    (* [comment removed for export] *)
    vrechk SHS EzsS (S + 16) 8 0.
    zstep. zstep. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. unsign KU. klia KU. } clear KU.
    zstep. zstep.
    replace (vb_size vq - (vb_len vq + 1) + 1) with (vb_size vq - vb_len vq) by (clear; lia).
    (* [comment removed for export] *)
    lazymatch goal with U8q : u8arr _ ?mx (vb_buf vq) bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (rw_cells_of_u8arr _ _ _ _ U8q) as BUFC; clear U8q;
      apply (rw_cells_split_CB rsegs _ _ [] _ _ [] [Z.to_nat (vb_len vq); nD]%nat) in BUFC; [| cbn; keeplia LBS END Vlen];
      cbn [mk_CB_cells app] in BUFC;
      apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in BUFC; destruct BUFC as [PREF DST];
      cbn [cells_size csize] in DST;
      replace (vb_buf vq + Z.of_nat (Z.to_nat (vb_len vq) + 0)) with (vb_buf vq + vb_len vq) in DST by (keeplia Vlen);
      pose proof (lowP_sfi Afmt la (vb_buf vq + vb_len vq) nD HS hs SB (Z.to_nat N) _ _ ltac:(keeplia HLA) _ _ _ MU
                    ltac:(cbn; unfold kHighMemBeg_z; keeplia LO CEIL ACV D0 Blo FLO Vlen) SFI) as SFI1; clear SFI
    end.
    rewrite <- END.
    (* [comment removed for export] *)
    zstep.
    destruct (ssp_any _ (proj1 CE)) as [canary SSP0].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (SSP1 : ssp_cells mx canary) by (eapply lowP_ssp_cells; [exact MU| cbn; unfold kHighMemBeg_z; keeplia LO CEIL ACV D0 Blo FLO Vlen| exact SSP0]) end.
    clear SSP0.
    unhide HSBq.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HSB1 : bytes_at rsegs mx HS hs)
        by (eapply (bytes_at_munch LPA); [exact HSBq| exact MU|]; destruct HFD as [E|HFD']; [rewrite E; intros a Ha; cbn in Ha; exfalso; keeplia Ha|];
            intros a Ha; cbn; keeplia Ha HFD' HSD HSL' LO CEIL ACV D0 END Vlen) end.
    clear HSBq. unhide DSB. unhide DJfS. unhide DJfB.
    icall (vsnprintf_icpt_gen_spec FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo Afmt (vb_buf vq + vb_len vq) nD VA slots HS hs _ canary SB (Z.to_nat N))
      by (try rewrite !unsigned_lit by (keeplia SPR LO CEIL ACV D0);
          lazymatch goal with
          | |- stk _ _ _ _ => eassumption
          | |- ro_cells _ _ Afmt _ => eassumption
          | |- ssp_cells _ _ => exact SSP1
          | |- rw_cells _ _ _ [CB _ _] => exact DST
          | |- va_area _ _ _ => unfold va_area; eassumption
          | |- bytes_at _ _ HS _ => exact HSB1
          | |- PRE _ _ _ => exact HPRE
          | |- SLOTS _ => exact HSL
          | |- mem_inv _ _ => assumption
          | |- sfi _ _ _ _ _ _ _ _ _ _ _ => exact SFI1
          | |- dst_ok _ _ => unfold dst_ok, IMG_LO, IMG_HI; keeplia Blo END Vlen
          | |- dst_zone _ _ => unfold dst_zone, kHighMemBeg_z; keeplia Blo END Vlen   (* [comment removed for export] *)
          | |- @eq _ _ _ => first [ reflexivity | f_equal; keeplia END ]
          | |- (_ <= _)%nat => keeplia END Vlen
          | |- ~ _ => clear - HSD END Vlen; try pose proof alloc_ceiling_val as ACV__; intros [X Y]; apply HSD; split; lia
          | |- _ => unfold VSNPRINTF_ICPT_STACK, GLOBALS_TOP, RO_TOP, IMG_LO, kHighMemBeg_z in *; keeplia LO CEIL ACV D0 SPR VLO VHI VAB ARL ART ART' HLA AB Blo Bhi END Vlen Vsz HSL' VQ31
          end).
    hide DSB. hide DJfS. hide DJfB.
    lazymatch goal with X : stk _ ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST1 end.
    (* [comment removed for export] *)
    lazymatch goal with DSTq : rw_cells _ ?mq (vb_buf vq + vb_len vq) [CB ?n2 ?l2], PREFq : rw_cells _ _ (vb_buf vq) [CB ?n1 ?l1] |- _ =>
      pose proof (rw_CB_length _ _ _ _ _ DSTq) as LD;
      assert (BUFC : rw_cells rsegs mq (vb_buf vq) [CB n1 l1; CB n2 l2])
        by (apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact PREFq|]; cbn [cells_size csize];
            eapply rwc_eq; [exact DSTq| keeplia Vlen]);
      pose proof (CellsX.rw_cells_recast rsegs _ _ _ [CB (n1 + n2)%nat (l1 ++ l2)] BUFC
                    ltac:(cbn; rewrite length_app, (rw_CB_length _ _ _ _ _ PREFq), LD; split; [reflexivity|exact I])
                    ltac:(cbn [cells_bytes cbytes]; rewrite <- app_assoc, app_nil_r; reflexivity)) as BUF1;
      clear BUFC PREFq DSTq; apply u8arr_of_rw_cells in BUF1;
      assert (LB1 : Z.of_nat (length (l1 ++ l2)) = vb_size vq) by (rewrite length_app, (rw_CB_length _ _ _ _ _ ltac:(apply rw_cells_of_u8arr; exact BUF1)) || (rewrite length_app, firstn_length, LD; keeplia LBS END Vlen))
    end.
    (* [comment removed for export] *)
    zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ?signed_lit_small in KB by (keeplia OL); keeplia KB OL|]. clear KB.
    zstep.
    (* [comment removed for export] *)
    vrechk SHS EzsS (S + 24) 8 0.
    zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. unsign KU. klia KU. } clear KU.
    (* [comment removed for export] *)
    vrechk SHS EzsS (S + 16) 8 0.
    zstep. zstep. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
    replace (vb_size vq - (vb_len vq + 1)) with (vb_size vq - vb_len vq - 1) by (clear; lia).
    (* [comment removed for export] *)
    apply evt_done. unfold vp_iter_post.
    hot_eexists_all.
    split; [reflexivity|]. split; [unfold VSNPRINTF_ICPT_STACK; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST1|].
    split; [cbv delta [SCRATCH' SCRATCH]; assumption|]. split; [cbv delta [FFRAME]; assumption|]. split; [unfold vsb_cells; assumption|].
    split; [exact BUF1|]. split; [exact LB1|].
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [| exact OL].
    lazymatch goal with PO : sfi _ _ _ _ _ _ _ _ _ _ ?mx |- _ =>
      pose proof PO as [[S2x _] _]; (first [ dand7 S2x as _ _ _ _ _ ZB1 _ | destruct S2x as (_ & _ & _ & _ & _ & ZB1 & _) ]) end.
    eapply stack_shadow_again; [exact STKSH'| exact ZB1| reflexivity].
  Qed.
End S.
End A_VS160.


Module A_VSe90.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpya4 AIcp3q7 AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VSbb4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSbb4.A_VSzjj.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSe3i A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47.B_Cf6tv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS160.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
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
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsnicpt_post, VSNPRINTF_ICPT_STACK in H.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma mapped_wmono {AI : AsanAlloc LPA} : forall (m m' : mem) a n,
  mapped m a n -> wmono rsegs m m' -> 0 <= a -> a + n <= 2^64 -> (forall i, 0 <= i < n -> ~ in_image LPA (a + i)) -> mapped m' a n.
Proof.
  intros m m' a n MP WM A0 AN NI i Hi E.
  pose proof (MP i Hi) as M1. specialize (WM (wz (a + i))). unfold wview in WM. rewrite E in WM.
  assert (NIi : ~ in_image LPA (bv_unsigned (wz (a + i)))) by (rewrite unsigned_lit by lia; exact (NI i Hi)).
  pose proof (as_find_segment_outside LPA (wz (a + i)) NIi) as FS.
  fold_cl_segs. rewrite FS in WM.
  destruct (m (wz (a + i))) as [b|] eqn:Em; [| exact (M1 eq_refl)]. exact (WM ltac:(discriminate) eq_refl).
Qed.

(* [comment removed for export] *)
Lemma memchr_len_le_length : forall P hs, In (Z_to_bv 8 0) hs -> 0 <= P -> memchr_len 0 P hs <= Z.of_nat (length hs).
Proof.
  intros P hs IN P0. unfold memchr_len.
  destruct (find_byte 0 (firstn (Z.to_nat P) hs)) as [i|] eqn:E.
  - (first [ pose proof ((find_byte_Some _ _ _ E)) as dR_1; dand3 dR_1 as Hi _ _ | destruct (find_byte_Some _ _ _ E) as (Hi & _ & _) ]). rewrite firstn_length in Hi. lia.
  - apply In_nth_error in IN. destruct IN as [j Hj]. pose proof (nth_error_lt _ _ _ Hj) as LJ.
    destruct (Z.le_gt_cases P (Z.of_nat j)) as [X|X]; [lia|]. exfalso.
    apply (find_byte_None _ _ E j (Z_to_bv 8 0)); [| reflexivity].
    rewrite nth_error_firstn. replace (j <? Z.to_nat P)%nat with true; [exact Hj|]. symmetry. apply Nat.ltb_lt. lia.
Qed.

End CEIL.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : AIcptdg.pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis VSNREAL : vsnreal_ok.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (S : Z) (vr : vsb_rec)
            (Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (lo SB N : Z) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) S vr false.
  (* [comment removed for export] *)
  Hypothesis HF : forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT.   (* [comment removed for export] *)
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  Hypothesis AFR : forall v, cenv v -> range_ok v Afmt la.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis VAA : va_area (aview A0 m0) VA slots.
  Hypothesis VLO : bv_unsigned sp <= VA.
  Hypothesis VHI : VA + 8 * Z.of_nat (length slots) <= 2^47.
  (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSL : SLOTS slots.
  Hypothesis HSB : bytes_at rsegs (aview A0 m0) HS hs.
  Hypothesis HSH : str_home A0 S vr HS hs.
  Hypothesis EM : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + Z.of_nat (length (OUT slots hs)) + 1) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 0 1.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VPRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      vsb_obj LPA A' v' S vr' false ->
      (vb_error vr <> 0 -> r = -1 /\ vr' = vr) ->
      (vb_error vr = 0 -> r = 0 /\ vb_error vr' = 0 /\
         (  vb_len vr' = vb_len vr + Z.of_nat (length (OUT slots hs))
         \/ (vb_len vr' = vb_size vr - 1 /\ vb_size vr' = vb_size vr /\ vb_buf vr' = vb_buf vr))) ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A0 q) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      frames_aged A0 A' 0 1 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      stk rsegs v' lo (bv_unsigned sp) ->
      va_area v' VA slots -> bytes_at rsegs v' HS hs ->
      stack_shadow LPA v' SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64) ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VPRINTF_STACK
               (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
               (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj HLA (conj HOUT (conj HOUT1 (conj P1 (conj P2 (conj PCM (conj FBY (conj VSNREAL
      (conj AINV00 (conj SOBJ (conj HF (conj ARL (conj ART (conj AFR (conj VAA (conj VLO (conj VHI (conj HPRE (conj HSL (conj HSB (conj HSH
      (conj EM (conj LBM (conj NLV (conj SCM (conj PRM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO (conj SPHI (conj STKSH K))))))))))))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Let SCRATCH' := SCRATCH S Afmt.
  Let FFRAME' := FFRAME VA.
  Let vp_tail' := vp_tail FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY VSNREAL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 S vr Afmt VA slots HS hs lo SB N T AINV00 SOBJ HF ARL ART AFR VAA VLO VHI HPRE HSL HSB HSH EM LBM NLV SCM PRM FY TP SP16 CEIL LO SPHI STKSH K.
  Let vp_iter' := vp_iter FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY VSNREAL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 S vr Afmt VA slots HS hs lo SB N T AINV00 SOBJ HF ARL ART AFR VAA VLO VHI HPRE HSL HSB HSH EM LBM NLV SCM PRM FY TP SP16 CEIL LO SPHI STKSH K.

  (* [comment removed for export] *)
  Definition W1 (ff b sz : Z) : list (Z * Z) :=
    [(bv_unsigned sp - VPRINTF_STACK, bv_unsigned sp); (ff, ff + 72); (sh ff, sh ff + 16); (b, b + sz)].

  (* [comment removed for export] *)
  #[using="AI16 vp_iter' vp_tail' K STKSH SPHI LO CEIL SP16 TP FY SCM PRM NLV LBM EM HSH HSB HSL HPRE VHI VLO VAA AFR ART ARL HF SOBJ AINV00 VSNREAL FBY PCM SLOTS fbytes P2 P1 HOUT1 HOUT HLA OUT PRE nargs la FMT"] Lemma vp_loop : forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs11 apc : word) (d ff : Z) (A1 : AS) (mB : mem) (mdB : Model)
                       (m : mem) (j0 j16 j3 j5 j9 shj bs : list byte),
    0 <= d <= 16 -> (bv_unsigned sp + -192 - d) mod 16 = 0 ->
    ainv A1 mB mdB -> amd_frame md0 mdB -> fr_alloc1 A0 A1 ff ->
    munch (W1 ff (vb_buf vr) (vb_size vr)) (aview A1 mB) m -> wmono rsegs (aview A1 mB) m -> client_fp LPA A1 (aview A1 mB) (W1 ff (vb_buf vr) (vb_size vr)) ->
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -192 - d) ->
    rw_cells rsegs m (bv_unsigned sp + -192 - d) (SCRATCH' ff j0 j16) ->
    stk rsegs m (bv_unsigned sp + -192 - d + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs m (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs m ff (FFRAME' apc j3 j5 j9) ->
    length shj = 16%nat -> rw_cells rsegs m (sh ff) [CB 16 shj] ->
    vsb_obj LPA A1 (aview A1 mB) S vr false -> vb_error vr = 0 ->
    u8arr rsegs m (vb_buf vr) bs -> Z.of_nat (length bs) = vb_size vr ->
    va_area (aview A1 mB) VA slots -> bytes_at rsegs (aview A1 mB) HS hs ->
    stack_shadow LPA (aview A1 mB) SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned A1) (bv_unsigned sp) VPRINTF_STACK
           (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40)) (frm ff 1) (aview A0 m0) (aview A1 mB) ->
    evt rsegs (EvtAcct.srz_at_r rsegs (ahull A1) (alhull A1) (aeager A1) mB mdB T)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -192 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - d))
                   a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) (Z_to_bv 64 S) (Z_to_bv 64 ((S + 8) / 8 + 2147450880))
                   (Z_to_bv 64 ((S + 16) / 8 + 2147450880)) (Z_to_bv 64 ((S + 24) / 8 + 2147450880))
                   (Z_to_bv 64 (S + 24)) (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (S + 8)) xs11 (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x8a4f4) fc None m (seg_rom rsegs)).
  Proof.
    touch_all. intros until bs. intros D0 AL16 AINV1 MDF1 FA MU1 WM1 CFP1 MI ST SCR STpad FRH FFR LSH SHC SOBJ1 E0 U8 LBS VAA1 HSB1 STKSH1 CFB.
    prelims. cbv delta [W1] in MU1, CFP1. ufs.
    pose proof FA as FA'. (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PR1 FAL FLO FHI SH0 SH1 | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PR1 & FAL & FLO & FHI & SH0 & SH1) ]). rewrite SHMAX_val in SH1. all_app_facts.
    pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    pose proof (HOUT _ _ _ HPRE) as OL.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LPA A1 mB mdB S vr false AINV1 SOBJ1)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A1 mB mdB S vr false AINV1 SOBJ1) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (SOBJ1) as dR_4; dand6 dR_4 as VSBC0 VINV VLS VLB VNE (bs0 & U80 & LBS0 & _) | pose proof SOBJ1 as (VSBC0 & VINV & VLS & VLB & VNE & (bs0 & U80 & LBS0 & _)) ]).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts.
    pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff 1 0%nat _ _ AINV1 FF1 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff 1 0%nat _ _ AINV1 FF1 VLB) as DJfB.
    change (fsize 1) with 128 in DJfS, DJfB.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(exact Shi)) as SHSB. rewrite SHMAX_val in SHSB. change ((40 + 7) / 8) with 5 in SHSB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(exact Bhi)) as SHBB. rewrite SHMAX_val in SHBB.
    pose proof (bytes_at_bound _ _ _ _ VAA1) as VAB. rewrite u64s_length in VAB.
    assert (EML : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX) by exact EM. unfold EXT_MAX in EML.
    (* [comment removed for export] *)
    assert (VSBC : rw_cells rsegs m S (vsb_cells vr)).
    { eapply (rw_cells_munch LPA); [exact VSBC0| exact MU1| exact WM1|]. rewrite vsb_cells_size. change (Z.of_nat 40) with 40. intros a Ha. cbn. keeplia Ha Shi DJfS SH1 Slo DSB LO CEIL ACV. }
    (* [comment removed for export] *)
    assert (SHDS : sh ff + 16 <= sh S \/ sh S + 5 <= sh ff) by (unfold sh; clear - DJfS FAL S16; try pose proof alloc_ceiling_val as ACV__; mlia).
    assert (SHDB : sh ff + 16 <= sh (vb_buf vr) \/ sh (vb_buf vr) + (vb_size vr + 7) / 8 <= sh ff) by (unfold sh; clear - DJfB FAL Vbm Vsz; try pose proof alloc_ceiling_val as ACV__; mlia).
    pose proof (cenv_intro A1 mB mdB AINV1) as CEB.
    assert (CE : cenv m)   (* [comment removed for export] *)
      by (eapply cenv_munch2; [exact CEB| exact MU1| repeat (apply Forall_cons); try apply Forall_nil;
            first [ apply (app_shadow_const_free2 LPA ff 128 16 FLO_a eq_refl eq_refl); clear; lia
                  | unfold const_free_ivl2, const_free_ivl, CONSTS_TOP, CONSTS_TOP2; cbn; keeplia LO CEIL ACV FLO Blo ] ]).
    pose proof (as_live_shadow LPA _ _ _ S 40 AINV1 VLS) as SHS0. fold_cl_segs. fold_aview.
    assert (SHS : bytes_at rsegs m (sh S) (shpat 40)).
    { eapply (bytes_at_munch LPA); [exact SHS0| exact MU1|]. change (Z.of_nat (length (shpat 40))) with 5.
      intros a Ha. cbn. keeplia Ha SHSB SHDS Slo Blo FLO LO CEIL ACV. }
    clear SHS0.
    pose proof (as_live_shadow LPA _ _ _ (vb_buf vr) (vb_size vr) AINV1 VLB) as BSH0. fold_cl_segs. fold_aview.
    assert (BSH : bytes_at rsegs m (sh (vb_buf vr)) (shpat (vb_size vr))).
    { eapply (bytes_at_munch LPA); [exact BSH0| exact MU1|]. rewrite shpat_length by (keeplia Vsz).
      intros a Ha. cbn. keeplia Ha SHBB SHDB Slo Blo FLO LO CEIL ACV. }
    clear BSH0.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (MW : forall a, 0 <= a -> a < alloc_ceiling -> mapped (aview A1 mB) (sh a - sh a mod 8) 8 -> mapped m (sh a - sh a mod 8) 8).
    { intros a Ha1 Ha2 MP. pose proof (sh_word_bound (Clg:=Clg) a Ha1 Ha2) as WB. rewrite SHMAX_val in WB.
      pose proof (sh_lo a Ha1) as SLO.
      pose proof (Z.mod_pos_bound (sh a) 8 ltac:(lia)) as M8.
      eapply mapped_wmono; [exact MP| exact WM1| keeplia WB| keeplia WB ACV| intros i Hi; unfold in_image; cbn; keeplia Hi SLO M8]. }
    assert (RD : range_ok m (vb_buf vr + vb_len vr) (vb_size vr - vb_len vr)).
    { eapply (shadowed_range_ok m _ _ (vb_buf vr) (vb_size vr)); [exact BSH| try (generalize alloc_ceiling_val); clear - Vbm; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia| keeplia Blo| keeplia Vlen| keeplia Vlen| keeplia Vlen
        | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; keeplia Blo Vlen Bhi ACV
        | apply MW; [unfold kHighMemBeg; keeplia Blo Vlen| keeplia Bhi Vlen| eapply live_shadow_word; [exact AINV1| exact VLB| keeplia Vlen]]
        | apply MW; [unfold kHighMemBeg; keeplia Blo Vlen| keeplia Bhi Vlen| eapply live_shadow_word; [exact AINV1| exact VLB| keeplia Vlen]] ]. }
    (* [comment removed for export] *)
    assert (HSX : (hs = [] /\ (HS = 0 \/ 0x10000 <= HS < 0x60a000) /\ hs_shadow m HS hs /\ bytes_at rsegs m HS hs)
                  \/ exists hq hk, a_live A1 hq = Some hk /\ hq <= HS /\ HS + Z.of_nat (length hs) <= hq + hk /\ hq <> S /\ hq <> vb_buf vr /\ In (Z_to_bv 8 0) hs
                        /\ app_rangeF LPA hq hk (* [comment removed for export] *) /\ hq + hk <= alloc_ceiling /\ (ff + 128 <= hq - 16 \/ hq + hk <= ff)
                        /\ (hq + hk <= S \/ S + 40 <= hq) /\ (hq + hk <= vb_buf vr \/ vb_buf vr + vb_size vr <= hq)
                        /\ hs_shadow m HS hs /\ bytes_at rsegs m HS hs).
    { pose proof HSH as [[E EHS]|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL)].
      - left. split; [exact E|]. split; [exact EHS|]. split; [left; exact E|]. rewrite E. apply bytes_at_nil. keeplia EHS.
      - right. exists hq, hk. rewrite <- (LV1 hq) in LQ.
        (first [ pose proof ((live_geomP LPA A1 mB mdB hq _ AINV1 LQ)) as dR_6; dand5 dR_6 as _ Q16 Qlo Qhi _ | pose proof (live_geomP LPA A1 mB mdB hq _ AINV1 LQ) as (_ & Q16 & Qlo & Qhi & _) ]). unfold kHighMemBeg in Qlo. all_app_facts.
        pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff 1 0%nat _ _ AINV1 FF1 LQ) as DJfQ. change (fsize 1) with 128 in DJfQ.
        pose proof (as_live_disjoint LPA A1 mB mdB _ _ _ _ AINV1 LQ VLS NQS) as DQS.
        pose proof (as_live_disjoint LPA A1 mB mdB _ _ _ _ AINV1 LQ VLB NQB) as DQB.
        assert (SHDQ : sh ff + 16 <= sh hq \/ sh hq + (hk + 7) / 8 <= sh ff) by (unfold sh; clear - DJfQ FAL Q16; try pose proof alloc_ceiling_val as ACV__; mlia).
        pose proof (sh_boundL (Clg:=Clg) hq hk ltac:(keeplia Qlo) ltac:(keeplia Q1 Q2) ltac:(exact Qhi)) as SHQB. rewrite SHMAX_val in SHQB.
        assert (LH1 : (1 <= length hs)%nat) by (destruct hs; [destruct HNUL| cbn; lia]).
        assert (HSBm : bytes_at rsegs m HS hs)
          by (eapply (bytes_at_munch LPA); [exact HSB1| exact MU1| intros a Ha; cbn; keeplia Ha Q1 Q2 Qlo Qhi DJfQ DQS DQB SHQB SH1 LO CEIL ACV]).
        repeat (split; [first [exact LQ| exact Q1| exact Q2| exact NQS| exact NQB| exact HNUL| exact Qlo_a| exact Qhi| exact DJfQ| exact DQS| exact DQB]|]).
        split; [| exact HSBm].
        right. exists (Z.of_nat (length hs)). split; [keeplia LH1|]. split; [| intros P HP; apply memchr_len_le_length; [exact HNUL| exact HP]].
        pose proof (as_live_shadow LPA _ _ _ hq hk AINV1 LQ) as QSH0. fold_cl_segs. fold_aview.
        assert (QSH : bytes_at rsegs m (sh hq) (shpat hk))
          by (eapply (bytes_at_munch LPA); [exact QSH0| exact MU1| rewrite shpat_length by (keeplia Q1 Q2); intros a Ha; cbn; keeplia Ha SHQB SHDQ Slo Blo FLO LO CEIL ACV]).
        eapply (shadowed_range_ok m _ _ hq hk); [exact QSH| try (generalize alloc_ceiling_val); clear - Q16; try pose proof alloc_ceiling_val as ACV__; Z.div_mod_to_equations; lia| keeplia Qlo| exact Q1| exact Q2| keeplia LH1
          | unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; keeplia Qlo Qhi Q1 Q2 LH1 ACV
          | apply MW; [unfold kHighMemBeg; keeplia Qlo Q1| keeplia Qhi Q2 LH1| eapply live_shadow_word; [exact AINV1| exact LQ| keeplia Q1 Q2 LH1]]
          | apply MW; [unfold kHighMemBeg; keeplia Qlo Q1 LH1| keeplia Qhi Q2 LH1| eapply live_shadow_word; [exact AINV1| exact LQ| keeplia Q1 Q2 LH1]] ]. }
    assert (HSS : hs_shadow m HS hs) by (destruct HSX as [(_ & _ & X & _)|(hq & hk & X)]; [exact X| clear - X; tauto]).
    assert (HSBm : bytes_at rsegs m HS hs) by (destruct HSX as [(_ & _ & _ & X)|(hq & hk & X)]; [exact X| clear - X; tauto]).
    assert (HFD : hs = [] \/ ff + 128 <= HS \/ HS + Z.of_nat (length hs) <= ff)
      by (destruct HSX as [(E & _)|(hq & hk & _ & Q1 & Q2 & _ & _ & _ & _ & _ & DJfQ & _)]; [left; exact E| right; keeplia Q1 Q2 DJfQ]).
    assert (HSD : ~ (vb_buf vr + vb_len vr < HS + Z.of_nat (length hs) /\ HS < vb_buf vr + vb_size vr)).
    { destruct HSX as [(E & EHS & _)|(hq & hk & _ & Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & DQB & _)]; [rewrite E; cbn; keeplia EHS Vlen Blo| keeplia Q1 Q2 DQB Vlen]. }
    assert (HSL' : HS + Z.of_nat (length hs) <= lo).
    { destruct HSX as [(E & EHS & _)|(hq & hk & _ & Q1 & Q2 & _ & _ & _ & _ & Qhi & _)]; [rewrite E; cbn; keeplia EHS CEIL ACV| keeplia Q1 Q2 Qhi CEIL]. }
    (* [comment removed for export] *)
    assert (VAAm : va_area m VA slots).
    { unfold va_area in *. eapply (bytes_at_munch LPA); [exact VAA1| exact MU1|]. rewrite u64s_length. intros a Ha. cbn. keeplia Ha VAB VLO SH1 FHI Bhi LO CEIL ACV. }
    assert (STKSHm : stack_shadow LPA m SB N (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) (bv_unsigned sp + 64)).
    { (first [ pose proof (STKSH1) as dR_7; dand6 dR_7 as SSB SSN _ _ SSC SST | pose proof STKSH1 as (SSB & SSN & _ & _ & SSC & SST) ]). unfold kHighMemBeg in SST. all_app_facts.
      pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *).
      eapply stack_shadow_again; [exact STKSH1| | reflexivity].
      eapply (bytes_at_munch LPA); [exact SSB| exact MU1|]. rewrite zeros_length, Z2Nat.id by exact SSN.
      intros a Ha. cbn. keeplia Ha SSC SST SHC8 SH1 FLO Blo LO CEIL ACV. }
    pose proof (HF m MI) as HFm.
    hide DSB. hide DJfS. hide DJfB. hide HSX.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (vp_iter' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff vr m j0 j16 j3 j5 j9 bs);
        [ exact D0 | exact MI | exact CE | exact ST | exact SCR | exact FFR | exact FAL | exact FLO_a | exact FHI
        | exact VSBC | exact VINV | unfold kHighMemBeg; exact Slo | exact Shi | exact S16 | exact SHS | exact U8 | exact LBS
        | first [exact Blo_a | exact Blo'_a | eassumption] | exact Bhi | unhide DSB; exact DSB | unhide DJfS; exact DJfS | unhide DJfB; exact DJfB
        | keeplia EML OL | exact RD | exact HFm | exact VAAm | exact HSBm | exact HSS | exact HSL' | exact HFD | exact HSD | ufs; exact STKSHm ]. }
    cbv beta. intros ms' POST.
    (first [ dex17 POST as rax t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' bs1 m1; dand15 POST as -> MUi WMi MI1 ST1 SCR1 FFR1 VSBC1 BUF1 LB1' HF1 VAA2 HSB2 STKSH2 OL1 | dand32 POST as rax t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' bs1 m1 -> MUi WMi MI1 ST1 SCR1 FFR1 VSBC1 BUF1 LB1' HF1 VAA2 HSB2 STKSH2 OL1 | destruct POST as (rax & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & bs1 & m1 & -> & MUi & WMi & MI1 & ST1 & SCR1 & FFR1 & VSBC1 & BUF1 & LB1' & HF1 & VAA2 & HSB2 & STKSH2 & OL1) ]).
    clear SCR FFR VSBC U8 SHS BSH HFm VAAm HSBm STKSHm HSS RD CE.
    unfold VSNPRINTF_ICPT_STACK in MUi. ufs.
    transport_after_call rsegs m m1 MUi WMi.
    clear MI. rename MI1 into MI.
    (* [comment removed for export] *)
    zstep. if_cases KF; zify_cond KF; rewrite ?signed_lit_small in KF by (keeplia Vsz Vlen OL).
    - (* [comment removed for export] *)
      destruct (rw_cells_forget rsegs _ _ _ FFR1) as [fj FFC]. pose proof (rw_CB_length _ _ _ _ _ FFC) as LFJ. cbn [cells_size csize Nat.add] in FFC, LFJ.
      astop AINV1 MU1 WM1 CFP1.
      lazymatch goal with AIq : ainv A1 ?mq ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      eapply (vp_tail' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 A1 mq mdq vr j0 j16 fj shj);
        [ exact D0 | exact AIq | exact MI
        | eapply amd_frame_trans; [exact MDF1| apply amd_frame_sbm; [exact SBM| exact MH1]]
        | exact ST1 | exact SCR1 | exact STpad | exact FRH | exact FA' | intros g; reflexivity | exact LFJ | exact FFC | exact LSH | exact SHC
        | split; [exact VSBC1|]; split; [exact VINV|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|]; exists bs1; split; [exact BUF1| split; [exact LB1'| intros X; discriminate X]]
        | exact E0 | exact E0 | reflexivity
        | left; keeplia KF
        | keeplia Vlen
        | left; reflexivity
        | intros p _ _; reflexivity
        | clear; lia | reflexivity | reflexivity | clear; lia | clear; lia (* [comment removed for export] *)
        | exact VAA2 | exact HSB2 | ufs; exact STKSH2
        | eapply cframe_newV; [eapply (cframe_after _ _ _ _ _ _ (aview A0 m0) (aview A1 mB)); [exact CFB| exact MU1| |
            eapply mapped_wmono; [exact (proj1 (proj2 CFB))| exact WM1| keeplia SPR LO CEIL ACV| keeplia SPR| intros i Hi; unfold in_image; cbn; keeplia Hi SPR LO CEIL ACV] ] | ] ]
      end.
      + intros a Ha NO. cbn [outside] in NO.
        assert (CS : (bv_unsigned sp - (192 + 16 + (80 + 8192)) <= a < bv_unsigned sp) \/ (ff <= a < ff + 72) \/ (sh ff <= a < sh ff + 16) \/ (vb_buf vr <= a < vb_buf vr + vb_size vr))
          by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia). clear NO.
        destruct CS as [X|[X|[X|X]]]; [left; exact X| right; right; left; left; change (fsize 1) with 128; keeplia X| right; right; left; right; change (fsize 1 / 8) with 16; exact X
          | right; left; left; left; split; [keeplia Vb0| exact X]].
      + intros a [X|X]; [left; exact X| right; left; exact X].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. revert KU. dead_b2z. } clear KU.
      zstep. zstep.
      astop AINV1 MU1 WM1 CFP1.
      lazymatch goal with AIq : ainv A1 ?mq ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ => rename AIq into AINVa end.
      set (addlen := Z.of_nat (length (OUT slots hs)) - (vb_size vr - vb_len vr - 1)) in *.
      assert (AD1 : 1 <= addlen /\ vb_size vr + addlen = vb_len vr + Z.of_nat (length (OUT slots hs)) + 1) by (subst addlen; keeplia KF Vlen).
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      eapply (VSB_extend_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq mdq A1 S addlen vr lo);
        [ exact AINVa | exact MI | reflexivity
        | subst addlen; first [reflexivity| f_equal; keeplia KF Vlen Vsz OL| apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; cbn [bv_modulus]; keeplia KF Vlen Vsz OL]
        | split; [exact VSBC1|]; split; [exact VINV|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|]; exists bs1; split; [exact BUF1| split; [exact LB1'| intros X; discriminate X]]
        | keeplia AD1 | unfold EXT_MAX; keeplia AD1 EML Vlen
        | rewrite LB1; eapply Z.le_trans; [| exact LBM]; apply Z.add_le_mono_l; apply vsb_extendsize_mono; keeplia AD1 Vlen
        | rewrite NL1; exact NLV | intros _; rewrite SC1; exact SCM | apply prim_room_ext; [keeplia Vsz AD1| rewrite PR1; exact PRM] (* [comment removed for export] *) | exact TP
        | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); exact AL16
        | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); exact ST1 | exact CEIL
        | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV D0); ufs; keeplia LO D0 | ]
      end.
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' r A2 mE mdE vr'. cbv zeta.
      intros AINV2 MI2 MDF2 SOBJ' LIVEq' FS12 TC2 NL2 ST2 OUTC.
      rewrite unsigned_lit in ST2, OUTC by (keeplia SPR LO CEIL ACV D0). ufs.
      replace (ret_pc (Z_to_bv 64 0x8a5c4)) with (Z_to_bv 64 0x8a5c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (as_minv LPA A2 _ _ AINV2) as [_ MH2].
      assert (FF2 : a_frame A2 ff = Some (1, 0%nat)) by (rewrite (FS12 ff); exact FF1).
      (* [comment removed for export] *)
      assert (MPof : forall (v : mem) jj, stk rsegs v lo (bv_unsigned sp + -192 - d) -> rw_cells rsegs v (bv_unsigned sp + -192 - d) [CB 88 jj] ->
                 stk rsegs v (bv_unsigned sp + -192 - d + 88) (bv_unsigned sp + -104) ->
                 rw_cells rsegs v (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                 mapped v (bv_unsigned sp - (192 + 16 + (80 + 8192))) (192 + 16 + (80 + 8192))).
      { intros v jj X1 X2 X3 X4.
        pose proof (stk_release rsegs _ _ _ _ X1 X2 ltac:(keeplia LO CEIL ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
        pose proof (stk_merge rsegs _ _ _ _ Y1 X3 ltac:(keeplia LO CEIL ACV D0)) as Y2.
        pose proof (stk_release rsegs _ _ _ _ Y2 X4 ltac:(keeplia LO CEIL ACV D0)) as Y3. cbn [cells_size csize Nat.add] in Y3.
        eapply (stk_mapped (L:=LPA)); [exact Y3| exact CEIL| keeplia LO| keeplia SPR]. }
      destruct OUTC as (nb & Er & Evr & COPY & FRESH & DEAD & LBe & SCe & PRe & CFe); subst r.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      + (* [comment removed for export] *)
        (first [ pose proof ((vsb_extendsize_spec (vb_size vr + addlen) ltac:(unfold EXT_MAX in *; keeplia AD1 EML Vsz Vlen))) as dR_10; dand3 dR_10 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size vr + addlen) ltac:(unfold EXT_MAX in *; keeplia AD1 EML Vsz Vlen)) as (NS1 & NS2 & NS3) ]).
        pose proof (vsb_extendsize_tight (vb_size vr + addlen)) as NS4.
        pose proof (vsb_extendsize_cap (vb_size vr + addlen) ltac:(unfold EXT_MAX; keeplia AD1 EML Vlen)) as NS5.
        set (ns := vsb_extendsize (vb_size vr + addlen)) in *.
        (* [comment removed for export] *)
        unhide DSB. unhide DJfS. unhide DJfB. unhide HSX.
        lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ ma (bv_unsigned sp + -192 - d) 88 AINVa ltac:(keeplia ACV CEIL LO D0) ltac:(keeplia SPR D0)
                        (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SCR1 ltac:(off_image_solve LPA))) as CR1;
          apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CFe) in SCR1;
            [| exact CR1 | cbn [FFRAME SCRATCH Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; unfold newblk, blk in X; keeplia Hi X Shi Bhi SHSB SHBB SPR LO CEIL ACV D0] ];
          clear CR1
        end.
        lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          apply (stk_ccall_any A1 A2 _ _ ma mb xsp win V Nn _ _ AINVa CFe) in STpad;
            [| keeplia LO CEIL ACV D0 | intros a Ha X; unfold newblk, blk in X; keeplia Ha X Shi Bhi SHSB SHBB SPR LO CEIL ACV D0 ]
        end.
        lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ ma (bv_unsigned sp + -104) 104 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                        (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRH ltac:(off_image_solve LPA))) as CR2;
          apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CFe) in FRH;
            [| exact CR2 | cbn [FFRAME SCRATCH Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; unfold newblk, blk in X; keeplia Hi X Shi Bhi SHSB SHBB SPR LO CEIL ACV D0] ];
          clear CR2
        end.
        lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CFe ff) in FFR1;
            [| eapply crange_fframe; [exact AINVa| exact FF1| clear; lia| cbn; change (fsize 1) with 128; clear; lia| cbn; clear; lia]
             | cbn [FFRAME SCRATCH Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia FHI LO CEIL D0|];
               intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJfS DJfB SHSB SHBB FLO ]
        end.
        lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CFe (sh ff)) in SHC;
            [| eapply crange_fshadow; [exact AINVa| exact FF1| clear; lia| cbn; change (fsize 1 / 8) with 16; clear; lia| cbn; clear; lia]
             | cbn [FFRAME SCRATCH Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SH1 LO CEIL ACV D0|];
               intros i Hi X; unfold newblk, blk in X; keeplia Hi X SHDS SHDB Slo Blo SH1 ]
        end.
        lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          unfold va_area in VAA2;
          apply (bytes_at_ccall LPA A1 A2 xsp win V Nn ma mb CFe VA) in VAA2;
            [| rewrite u64s_length; eapply (crange_stack (L:=LPA) A1 _ _ ma); [exact AINVa| keeplia VLO LO CEIL ACV| keeplia VAB| rewrite <- (u64s_length slots); eapply (bytes_at_mapped LPA); [exact VAA2| off_image_solve LPA || (unfold off_image; keeplia VLO VAB LO CEIL ACV)]]
             | rewrite u64s_length; split; [keeplia VLO D0| intros i Hi X; unfold newblk, blk in X; keeplia Hi X VLO Shi Bhi SHSB SHBB LO CEIL ACV] ]
        end.
        lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          assert (HSB3 : bytes_at rsegs mb HS hs);
          [ destruct HSX as [(E & EHS & _)|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL & Qlo & Qhi & DJfQ & DQS & DQB & _)];
            [ rewrite E; apply bytes_at_nil; keeplia EHS
            | change (app_rangeF LPA hq hk) with (app_range LPA hq hk) in Qlo; all_app_facts;
              pose proof (sh_boundL (Clg:=Clg) hq hk ltac:(keeplia Qlo) ltac:(keeplia Q1 Q2) ltac:(exact Qhi)) as SHQB; rewrite SHMAX_val in SHQB;
              apply (bytes_at_ccall LPA A1 A2 xsp win V Nn ma mb CFe HS) in HSB2;
              [ exact HSB2
              | eapply (crange_block (L:=LPA) A1); [exact AINVa| exact LQ| exact Q1| exact Q2| clear; lia]
              | split; [keeplia Q1 Q2 Qhi LO CEIL D0| intros i Hi X; unfold newblk, blk in X; keeplia Hi X Q1 Q2 DQS DQB Qlo SHSB SHBB] ] ]
          | clear HSB2 ]
        end.
        lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
          assert (STKSH3 : stack_shadow LPA mb SB N (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) (bv_unsigned sp + 64));
          [ (first [ pose proof (STKSH2) as dR_11; dand6 dR_11 as SSB SSN _ _ SSC SST | pose proof STKSH2 as (SSB & SSN & _ & _ & SSC & SST) ]); unfold kHighMemBeg in SST; all_app_facts;
            pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *);
            assert (M0 : 0 <= bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) by keeplia CEIL LO ACV;
            assert (M1 : bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64 <= Z.max (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) alloc_ceiling) by (clear; lia);
            pose proof (stack_shadow_sub LPA _ SB N _ _ _ _ STKSH2 M1 (Z.le_refl _) M0) as SSx;
            pose proof (crange_stack_shadow (Clg:=Clg) LPA A1 _ _ SB N _ _ AINVa SSx ltac:(clear; lia)) as CRS; clear SSx M0 M1;
            eapply stack_shadow_again; [exact STKSH2| | reflexivity];
            apply (bytes_at_ccall LPA A1 A2 xsp win V Nn ma mb CFe SB);
            [ rewrite zeros_length, Z2Nat.id by exact SSN; exact CRS
            | rewrite zeros_length, Z2Nat.id by exact SSN; split; [keeplia SSC SST SHC8 LO CEIL ACV D0| intros i Hi X; unfold newblk, blk in X; keeplia Hi X SSC SST SHC8 Slo Blo SHSB SHBB]
            | exact SSB ]
          | clear STKSH2 ]
        end.
        hide DSB. hide DJfS. hide DJfB. hide HSX.
        (* [comment removed for export] *)
        pose proof SOBJ' as SOBJ2. rewrite Evr in SOBJ2.
        (first [ pose proof ((vsb_obj_geom LPA A2 _ _ S _ false AINV2 SOBJ2)) as dR_12; dand11 dR_12 as _ _ _ _ NB16 NBlo NBhi _ DSNB _ _ | pose proof (vsb_obj_geom LPA A2 _ _ S _ false AINV2 SOBJ2) as (_ & _ & _ & _ & NB16 & NBlo & NBhi & _ & DSNB & _ & _) ]).
        (first [ pose proof (SOBJ2) as dR_13; dand6 dR_13 as VSBC2 VINV2 VLS2 VLB2 VNE2 (bs2 & U82 & LBS2 & _) | pose proof SOBJ2 as (VSBC2 & VINV2 & VLS2 & VLB2 & VNE2 & (bs2 & U82 & LBS2 & _)) ]).
        unfold vsb_set_buf_size in NB16, NBlo, NBhi, DSNB, VLB2, VNE2, U82, LBS2. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent] in NB16, NBlo, NBhi, DSNB, VLB2, VNE2, U82, LBS2.
        unfold kHighMemBeg in NBlo. all_app_facts.
        pose proof (as_frame_blk_disjoint LPA A2 _ _ ff 1 0%nat _ _ AINV2 FF2 VLS2) as DJfS2.
        pose proof (as_frame_blk_disjoint LPA A2 _ _ ff 1 0%nat _ _ AINV2 FF2 VLB2) as DJfNB.
        change (fsize 1) with 128 in DJfS2, DJfNB.
        pose proof (sh_boundL (Clg:=Clg) nb ns ltac:(keeplia NBlo) ltac:(keeplia NS1 Vsz AD1) ltac:(exact NBhi)) as SHNB. rewrite SHMAX_val in SHNB.
        assert (NQ : forall hq hk, a_live A1 hq = Some hk -> hq <> nb) by (intros hq hk LQ ->; rewrite FRESH in LQ; discriminate LQ).
        (* [comment removed for export] *)
        destruct (rw_cells_forget rsegs _ _ _ SCR1) as [j88 SCR88]. cbn [SCRATCH cells_size csize Nat.add] in SCR88.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
          pose proof (munch_refl [(bv_unsigned sp - (192 + 16 + (80 + 8192)), bv_unsigned sp); (ff, ff + 72); (sh ff, sh ff + 16); (nb, nb + ns)] (aview A2 mq)) as MU2;
          pose proof (wmono_refl rsegs (aview A2 mq)) as WM2;
          assert (CFP2 : client_fp LPA A2 (aview A2 mq) [(bv_unsigned sp - (192 + 16 + (80 + 8192)), bv_unsigned sp); (ff, ff + 72); (sh ff, sh ff + 16); (nb, nb + ns)]);
          [ cbn; split; [left; split; [keeplia LO CEIL| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - (192 + 16 + (80 + 8192)))) with (192 + 16 + (80 + 8192)) by (clear; lia);
              eapply (MPof _ _); [exact ST2| exact SCR88| exact STpad| exact FRH]]]|];
            split; [right; right; left; exists ff, 1, 0%nat; split; [exact FF2| change (fsize 1) with 128; clear; lia]|];
            split; [right; right; right; exists ff, 1, 0%nat; split; [exact FF2| change (fsize 1 / 8) with 16; clear; lia]|];
            split; [right; left; exists nb, ns; split; [exact VLB2| clear; lia]| exact I]
          | ]
        end.
        pose proof (MPof _ _ ST2 SCR88 STpad FRH) as MPb. clear SCR88.
        ago AINV2. fold_cl_segs.
        (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity]. clear KZ.
        (* [comment removed for export] *)
        unhide HSX.
        assert (HSS2_HSD2 : hs_shadow (aview A2 mE) HS hs /\ ~ (nb + vb_len vr < HS + Z.of_nat (length hs) /\ HS < nb + ns)).
        { destruct HSX as [(E & EHS & _)|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL & Qlo & Qhi & DJfQ & DQS & DQB & _)].
          - split; [left; exact E| rewrite E; cbn; keeplia EHS NBlo Vlen].
          - assert (LQ2 : a_live A2 hq = Some hk) by (rewrite (LIVEq' hq NQB ltac:(rewrite Evr; cbn [vb_buf vsb_set_buf_size]; exact (NQ hq hk LQ))); exact LQ).
            pose proof (as_live_disjoint LPA A2 _ _ _ _ _ _ AINV2 LQ2 VLB2 (NQ hq hk LQ)) as DQNB.
            assert (LH1 : (1 <= length hs)%nat) by (destruct hs; [destruct HNUL| cbn; lia]).
            split; [| keeplia Q1 Q2 DQNB Vlen].
            right. exists (Z.of_nat (length hs)). split; [keeplia LH1|]. split; [| intros P HP; apply memchr_len_le_length; [exact HNUL| exact HP]].
            eapply (live_range_ok A2); [exact AINV2| exact LQ2| exact Q1| exact Q2| keeplia LH1]. }
        destruct HSS2_HSD2 as [HSS2 HSD2]. hide HSX.
        pose proof (as_live_shadow LPA _ _ _ S 40 AINV2 VLS2) as SHS2. fold_cl_segs. fold_aview.
        eapply evt_cut.
        { eapply (vp_iter' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff (vsb_set_buf_size vr nb ns) (aview A2 mE) j0 j16 j3 j5 j9 bs2);
            unfold vsb_set_buf_size; cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent];
            [ exact D0 | exact MI2 | exact (cenv_intro A2 _ _ AINV2) | exact ST2 | exact SCR1 | exact FFR1 | exact FAL | exact FLO_a | exact FHI
            | exact VSBC2 | exact VINV2 | unfold kHighMemBeg; exact Slo | exact Shi | exact S16 | exact SHS2 | exact U82 | exact LBS2
            | exact NBlo_a | exact NBhi | exact DSNB | unhide DJfS; exact DJfS | exact DJfNB
            | keeplia NS5 | eapply (live_range_ok A2); [exact AINV2| exact VLB2| keeplia Vlen| keeplia Vlen| keeplia NS1 AD1 Vlen]
            | exact (HF _ MI2) | exact VAA2 | exact HSB3 | exact HSS2 | exact HSL' | exact HFD | exact HSD2 | ufs; exact STKSH3 ]. }
        cbv beta. intros ms2 POST2.
        (first [ dex17 POST2 as rax2 t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x bs3 m3; dand15 POST2 as -> MUj WMj MI3 ST3 SCR3 FFR3 VSBC3 BUF3 LB3 HF3 VAA3 HSB4 STKSH4 OL2 | dand32 POST2 as rax2 t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x bs3 m3 -> MUj WMj MI3 ST3 SCR3 FFR3 VSBC3 BUF3 LB3 HF3 VAA3 HSB4 STKSH4 OL2 | destruct POST2 as (rax2 & t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & bs3 & m3 & -> & MUj & WMj & MI3 & ST3 & SCR3 & FFR3 & VSBC3 & BUF3 & LB3 & HF3 & VAA3 & HSB4 & STKSH4 & OL2) ]).
        unfold vsb_set_buf_size in MUj, VSBC3, BUF3, LB3. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent] in MUj, VSBC3, BUF3, LB3, ST3, SCR3, FFR3.
        clear SCR1 FFR1 VSBC2 U82 SHS2 VAA2 HSB3 STKSH3.
        unfold VSNPRINTF_ICPT_STACK in MUj.
        (* [comment removed for export] *)
        lazymatch type of MUj with munch ?Wj _ _ =>
          apply (rw_cells_transport rsegs Wj (aview A2 mE) m3) in FRH; [| exact MUj | exact WMj | cbn [disjoint_from]; simpl_sizes; keeplia D0 NBhi CEIL LO FHI];
          apply (stk_transport_disjoint rsegs Wj (aview A2 mE) m3) in STpad; [| exact MUj | exact WMj | cbn [disjoint_from]; keeplia D0 NBhi CEIL LO FHI];
          apply (rw_cells_transport rsegs Wj (aview A2 mE) m3) in SHC; [| exact MUj | exact WMj | cbn [disjoint_from]; simpl_sizes; keeplia D0 SH1 NBlo Vlen FLO CEIL LO ACV];
          lazymatch type of MU2 with munch ?W2 _ _ =>
            apply (munch_trans W2 _ (aview A2 mE) m3) in MU2; [| eapply (munch_weaken Wj W2 (aview A2 mE) m3); [unfold sub_fp; cbn [outside]; intros x__ Hx__; keeplia Hx__ D0 Vlen| exact MUj]] end;
          apply (wmono_trans rsegs _ (aview A2 mE) m3) in WM2; [| exact WMj]
        end.
        clear ST2 MUj.
        (* [comment removed for export] *)
        unfold vsb_set_buf_size. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent].
        (* [comment removed for export] *)
        zstep. if_cases KF2; zify_cond KF2; rewrite ?signed_lit_small in KF2 by (keeplia NS5 NS1 AD1 Vsz Vlen OL); [| exfalso; keeplia KF2 NS1 AD1 Vlen].
        destruct (rw_cells_forget rsegs _ _ _ FFR3) as [fj FFC]. pose proof (rw_CB_length _ _ _ _ _ FFC) as LFJ. cbn [cells_size csize Nat.add] in FFC, LFJ.
        astop AINV2 MU2 WM2 CFP2.
        lazymatch goal with AIq : ainv A2 ?mq ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ => rename AIq into AINVc end.
        pose proof (vsb_pot_credit _ _ vr nb addlen ltac:(keeplia Vsz) ltac:(keeplia AD1) SCe) as PC. pose proof (vsb_ppot_credit _ _ vr nb addlen ltac:(keeplia Vsz) ltac:(keeplia AD1) PRe) as PP.   (* [comment removed for export] *)
        destruct (rw_cells_forget rsegs _ _ _ SCR3) as [j88' SCR88']. cbn [SCRATCH cells_size csize Nat.add] in SCR88'.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
        eapply (vp_tail' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 A2 mq mdq (vsb_set_buf_size vr nb ns) j0 j16 fj shj);
          unfold vsb_set_buf_size; cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent];
          [ exact D0 | exact AINVc | exact MI3
          | eapply amd_frame_trans; [exact MDF1|]; eapply amd_frame_sbm_l; [exact SBM| exact MH1|]; eapply amd_frame_trans; [exact MDF2| apply amd_frame_sbm; [exact SBM0| exact MH2]]
          | exact ST3 | exact SCR3 | exact STpad | exact FRH | exact FA' | exact FS12 | exact LFJ | exact FFC | exact LSH | exact SHC
          | split; [exact VSBC3|]; split; [exact VINV2|]; split; [exact VLS2|]; split; [exact VLB2|]; split; [exact VNE2|]; exists bs3; split; [exact BUF3| split; [exact LB3| intros X; discriminate X]]
          | exact E0 | exact E0 | reflexivity
          | left; keeplia KF2
          | keeplia NS1 NS4 AD1 Vlen Vsz
          | right; split; [exact FRESH| exact DEAD]
          | intros p X1 X2; apply (LIVEq' p X1); rewrite Evr; exact X2
          | rewrite LBe; clear; lia | rewrite TC2, TC1; reflexivity | rewrite NL2, NL1; reflexivity | exact PC | exact PP (* [comment removed for export] *)
          | exact VAA3 | exact HSB4 | ufs; exact STKSH4
          | ]
        end.
        (* [comment removed for export] *)
        lazymatch type of CFe with cframe _ _ _ _ _ _ _ ?ma ?mb =>
          eapply cframe_newV;
          [ eapply (cframe_after _ _ _ _ _ _ (aview A0 m0) mb);
            [ eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A0 m0) ma mb);
              [ eapply (cframe_after _ _ _ _ _ _ (aview A0 m0) (aview A1 mB) ma); [exact CFB| exact MU1| |
                  eapply mapped_wmono; [exact (proj1 (proj2 CFB))| exact WM1| keeplia SPR LO CEIL ACV| keeplia SPR| intros i Hi; unfold in_image; cbn; keeplia Hi SPR LO CEIL ACV] ]
              | eapply (cframe_reframe LPA _ _ _ _ (bv_unsigned sp) (192 + 16 + (80 + 8192))); [exact CFe| keeplia D0| keeplia D0| exact MPb]
              | clear; lia | clear; lia | exact MPb
              | intros a X; exact X | intros a X; right; exact X | intros a X; exact X ]
            | exact MU2 | | eapply (MPof _ _); [exact ST3| exact SCR88'| exact STpad| exact FRH] ]
          | intros a [X|X]; [left; left; exact X| left; right; left; exact X] ]
        end.
        * intros a Ha NO. cbn [outside] in NO.
          assert (CS : (bv_unsigned sp - (192 + 16 + (80 + 8192)) <= a < bv_unsigned sp) \/ (ff <= a < ff + 72) \/ (sh ff <= a < sh ff + 16) \/ (vb_buf vr <= a < vb_buf vr + vb_size vr))
            by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia). clear NO.
          destruct CS as [X|[X|[X|X]]]; [left; exact X| right; right; left; left; change (fsize 1) with 128; keeplia X| right; right; left; right; change (fsize 1 / 8) with 16; exact X
            | right; left; left; left; split; [keeplia Vb0| exact X]].
        * intros a Ha NO. cbn [outside] in NO.
          assert (CS : (bv_unsigned sp - (192 + 16 + (80 + 8192)) <= a < bv_unsigned sp) \/ (ff <= a < ff + 72) \/ (sh ff <= a < sh ff + 16) \/ (nb <= a < nb + ns))
            by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia). clear NO.
          destruct CS as [X|[X|[X|X]]]; [left; exact X| right; right; left; left; left; change (fsize 1) with 128; keeplia X| right; right; left; left; right; change (fsize 1 / 8) with 16; exact X
            | right; right; left; right; left; left; split; [keeplia NBlo| exact X]].
  Qed.
End S.
End A_VSe90.


Module A_VSq5u.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpya4 AIcp3q7 AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSe3i A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VEr47.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require B_Co6gg B_Leaves.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_ImgLow OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47.B_Cf6tv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.B_Co6gg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.B_Leaves OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSe90.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @CEIL; @D0; @ACV; @Slo; @VAB; @LFJ; @SPR; @Shi; @FLO; @SPHI; @Vsz; @Ha__; @Vb0; @SZ; @SR; @VLO; @FHI; @S8; @NZ; @H; @Q2; @Qhi; @SST; @ACV__; @ARL; @Dd; @Bhi; @EHS; @K0; @SH1n; @DJfS; @SHSB; @SHDS; @HLA; @ART; @KA; @KU; @DJfB; @Blo0; @Hx__; @NO])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, ASSERT_STACK, ASSERT_STATE_STACK, INDENT_STACK in H.

(* [comment removed for export] *)
Lemma mod16_of_mod32_vp : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
  intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
  replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma rw_CB8_C8 : forall segs m a pre (j : list byte) rest,
  rw_cells segs m a (pre ++ CB 8 j :: rest) -> rw_cells segs m a (pre ++ C8 (le_bytes_to_word j) :: rest).
Proof.
  intros segs m a pre j rest H. pose proof H as [[W _] _].
  apply cells_wf_app in W. destruct W as [W1 W2]. cbn in W2. destruct W2 as [LJ W3].
  eapply rw_cells_recast; [exact H| |].
  - apply cells_wf_app. split; [exact W1|]. cbn. split; [exact I| exact W3].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite (le8_of_bytes8 j LJ). reflexivity.
Qed.

End CEIL.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : AIcptdg.pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis VSNREAL : vsnreal_ok.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (S : Z) (vr : vsb_rec)
            (Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (lo SB N : Z) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) S vr false.
  (* [comment removed for export] *)
  Hypothesis HF : forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT.   (* [comment removed for export] *)
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  Hypothesis AFR : forall v, cenv v -> range_ok v Afmt la.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis VAA : va_area (aview A0 m0) VA slots.
  Hypothesis VLO : bv_unsigned sp <= VA.
  Hypothesis VHI : VA + 8 * Z.of_nat (length slots) <= 2^47.
  (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSL : SLOTS slots.
  Hypothesis HSB : bytes_at rsegs (aview A0 m0) HS hs.
  Hypothesis HSH : str_home A0 S vr HS hs.
  Hypothesis EM : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + Z.of_nat (length (OUT slots hs)) + 1) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 0 1.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VPRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      vsb_obj LPA A' v' S vr' false ->
      (vb_error vr <> 0 -> r = -1 /\ vr' = vr) ->
      (vb_error vr = 0 -> r = 0 /\ vb_error vr' = 0 /\
         (  vb_len vr' = vb_len vr + Z.of_nat (length (OUT slots hs))
         \/ (vb_len vr' = vb_size vr - 1 /\ vb_size vr' = vb_size vr /\ vb_buf vr' = vb_buf vr))) ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A0 q) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      frames_aged A0 A' 0 1 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      stk rsegs v' lo (bv_unsigned sp) ->
      va_area v' VA slots -> bytes_at rsegs v' HS hs ->
      stack_shadow LPA v' SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64) ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VPRINTF_STACK
               (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
               (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj HLA (conj HOUT (conj HOUT1 (conj P1 (conj P2 (conj PCM (conj FBY (conj VSNREAL
      (conj AINV00 (conj SOBJ (conj HF (conj ARL (conj ART (conj AFR (conj VAA (conj VLO (conj VHI (conj HPRE (conj HSL (conj HSB (conj HSH
      (conj EM (conj LBM (conj NLV (conj SCM (conj PRM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO (conj SPHI (conj STKSH K))))))))))))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Let SCRATCH' := SCRATCH S Afmt.
  Let FFRAME' := FFRAME VA.
  (* [comment removed for export] *)
  Local Ltac pose_exit :=
    pose proof (vp_exit FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY VSNREAL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 S vr Afmt VA slots HS hs lo SB N T AINV00 SOBJ HF ARL ART AFR VAA VLO VHI HPRE HSL HSB HSH EM LBM NLV SCM PRM FY TP SP16 CEIL LO SPHI STKSH K) as vp_exit'.
  Local Ltac pose_loop :=
    pose proof (vp_loop FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY VSNREAL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 S vr Afmt VA slots HS hs lo SB N T AINV00 SOBJ HF ARL ART AFR VAA VLO VHI HPRE HSL HSB HSH EM LBM NLV SCM PRM FY TP SP16 CEIL LO SPHI STKSH K) as vp_loop'.

  (* [comment removed for export] *)
  Local Ltac vsb_leaf_call SPEC VSBC VINV0 SHS CE MU STc :=
    icall SPEC
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STACK, ASSERT_STATE_STACK, INDENT_STACK, kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV0
                | (eexists _, _; split; [exact SHS| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | (eapply cenv_munch2; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil;
                     first [ (* [comment removed for export] *)
                             lazymatch goal with |- const_free_ivl2 (sh ?f, _) =>
                               lazymatch goal with FA : app_rangeF LPA f ?n |- _ => apply (app_shadow_const_free2 LPA f n _ FA eq_refl eq_refl); clear; vm_compute; discriminate end end
                           | unfold const_free_ivl2, const_free_ivl, CONSTS_TOP, CONSTS_TOP2; cbn; lia ] ])
                | exact STc
                | assumption
                | lia ]);
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into STc end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 K STKSH SPHI LO CEIL SP16 TP FY SCM PRM NLV LBM EM HSH HSB HSL HPRE VHI VLO VAA AFR ART ARL HF SOBJ AINV00 N SB hs HS slots vr VSNREAL FBY PCM SLOTS fbytes P2 P1 HOUT1 HOUT HLA OUT PRE nargs la FMT"] Theorem VSB_vprintf_ok : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv rsegs (aview A0 m0) ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 Afmt -> a2 = Z_to_bv 64 VA ->
    stk rsegs (aview A0 m0) lo (bv_unsigned sp) ->
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 VSB_vprintf_entry) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros until t6. intros MI Ha0 Ha1 Ha2 ST. subst a0 a1 a2. unfold VSB_vprintf_entry.
    prelims.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof (HOUT _ _ _ HPRE) as OL.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    clear Smap Bmap Simg Bimg.
    pose proof SOBJ as (_ & VINV & VLS & VLB & VNE & _).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts.
    pose proof (bytes_at_bound _ _ _ _ VAA) as VAB. rewrite u64s_length in VAB.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(exact Shi)) as SHSB. rewrite SHMAX_val in SHSB. change ((40 + 7) / 8) with 5 in SHSB.
    (* [comment removed for export] *)
    pose proof (shpat_sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(exact Shi)) as SHSBp. rewrite SHMAX_val in SHSBp.
    assert (IMGLO : 0 < IMG_LO) by (unfold IMG_LO; reflexivity).
    hide DSB.
    (* [comment removed for export] *)
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (uar_cells_of_consts _ (proj1 CE)) as [UARG UARV]. fold_aview. open_map_cells MC.
    hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (192 + 16 + (80 + 8192)), bv_unsigned sp)] (aview A0 m0)) as MU.
    pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    assert (WMAP : mapped (aview A0 m0) (bv_unsigned sp - (192 + 16 + (80 + 8192))) (192 + 16 + (80 + 8192)))
      by (eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]).
    assert (CFP : client_fp LPA A0 (aview A0 m0) [(bv_unsigned sp - (192 + 16 + (80 + 8192)), bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [lia|]. split; [lia|].
      replace (bv_unsigned sp - (bv_unsigned sp - (192 + 16 + (80 + 8192)))) with (192 + 16 + (80 + 8192)) by lia. exact WMAP. }
    hide HSB.
    ago AINV00. fold_cl_segs.
    (* [comment removed for export] *)
    carve_frame 104%nat ST. rename FR into FRH. carve_frame 88%nat ST. rename FR into FR0.
    (* [comment removed for export] *)
    do 15 zstep.
    (* [comment removed for export] *)
    zstep. try replace (bv_unsigned sp + -192 + 192) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    assert (AL16a : (bv_unsigned sp + -192) mod 16 = 0).
    { pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as Dv. rewrite SP16, Z.add_0_r in Dv. rewrite Dv.
      replace (16 * (bv_unsigned sp / 16) + -192) with ((bv_unsigned sp / 16 - 12) * 16) by lia. apply Z_mod_mult. }
    (first [ pose proof ((land_align32_w (bv_unsigned sp + -192) ltac:(keeplia SPR LO CEIL ACV) AL16a)) as dR_3; dex1 dR_3 as d; dand3 dR_3 as Dd ELAND AL32 | pose proof ((land_align32_w (bv_unsigned sp + -192) ltac:(keeplia SPR LO CEIL ACV) AL16a)) as dR_3; dand4 dR_3 as d Dd ELAND AL32 | destruct (land_align32_w (bv_unsigned sp + -192) ltac:(keeplia SPR LO CEIL ACV) AL16a) as (d & Dd & ELAND & AL32) ]). clear AL16a.
    rewrite ELAND. clear ELAND. assert (D0 : 0 <= d <= 16) by (try (generalize alloc_ceiling_val); clear - Dd; try pose proof alloc_ceiling_val as ACV__; lia). clear Dd.
    pose proof (mod16_of_mod32_vp _ AL32) as AL16.
    (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -104).
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -192 - d + 88) _ ST ltac:(keeplia D0 LO CEIL ACV)) as [STl STpad]. clear ST.
    destruct (stk_carve rsegs _ lo _ 88 STl ltac:(keeplia D0 LO CEIL ACV)) as [STlo [jp SCR]]. clear STl.
    change (Z.of_nat 88) with 88 in STlo, SCR.
    replace (bv_unsigned sp + -192 - d + 88 - 88) with (bv_unsigned sp + -192 - d) in STlo, SCR by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). if_false.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP. fold_cl_segs.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, SBq : same_but_materialized md0 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename SBq into SBMa end.
    lazymatch goal with MIq : mem_inv _ ?ma |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      rename MIq into MIa;
      assert (MPW : mapped ma (bv_unsigned sp + -192 - d - ASTK) ASTK)
        by (unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact STlo | exact CEIL | keeplia LO D0 | keeplia D0]) end.
    eapply (smalloc_acall 1);
      [ exact AINVa | exact MIa | right; reflexivity | reflexivity | change (fsize 1) with 128; clear; lia
      | exact (frames_young_smalloc A0 1 0%nat 1%nat FY (or_intror (conj eq_refl (le_n 1%nat))))
      | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); exact AL16
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); unfold ASTK; keeplia CEIL LO D0
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); exact MPW | ].
    clear MPW.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A1 mB mdB fj fa fb
           AINV1 MI1 MDF1 LV1 LB1 TC1 NL1 SC1 PR1 NZ FN FF1 AGE NONE GEOM LFJ FFC SHC FRO CF1.
    clear FRO. pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    change (Z.to_nat (fsize 1 - 8)) with 120%nat in LFJ, FFC. change (Z.to_nat (fsize 1 / 8)) with 16%nat in SHC.
    (first [ dand5 GEOM as FAL FLO FHI SH0 SH1 | destruct GEOM as (FAL & FLO & FHI & SH0 & SH1) ]).
    change (fsize 1) with 128 in FHI, FLO. change (fsize 1 / 8) with 16 in SH1. unfold kHighMemBeg in FLO. all_app_facts.
    pose proof SH1 as SH1n. rewrite SHMAX_val in SH1n.
    rewrite unsigned_lit in CF1 by (keeplia SPR D0 LO CEIL ACV). unfold ASTK in CF1.
    assert (FA : fr_alloc1 A0 A1 ff).
    { split; [exact FN|]. split; [exact FF1|]. split; [exact AGE|]. split; [exact NONE|]. split; [exact LV1|]. split; [exact LB1|].
      split; [exact TC1|]. split; [exact NL1|]. split; [exact SC1|]. split; [exact PR1|]. split; [exact FAL|]. split; [exact FLO_a|]. split; [exact FHI|].
      split; [exact SH0| exact SH1]. }
    assert (VLS1 : a_live A1 S = Some 40) by (rewrite (LV1 S); exact VLS).
    assert (VLB1 : a_live A1 (vb_buf vr) = Some (vb_size vr)) by (rewrite (LV1 (vb_buf vr)); exact VLB).
    (* [comment removed for export] *)
    unhide HSB.
    lazymatch type of CF1 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -192 - d) 88 AINVa ltac:(keeplia ACV CEIL LO D0) ltac:(keeplia SPR D0)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SCR ltac:(off_image_solve LPA))) as CR0;
      lazymatch type of SCR with rw_cells _ _ _ ?cs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 _ cs) in SCR;
        [ | exact CR0 | cbn [Cells.cells_size Cells.csize Nat.add length app firstn skipn]; rewrite ?firstn_length, ?skipn_length;
                        split; [keeplia D0| intros i Hi X; exact X] ] end;
      clear CR0;
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -104) 104 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRH ltac:(off_image_solve LPA))) as CRH;
      lazymatch type of FRH with rw_cells _ _ _ ?cs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 _ cs) in FRH;
        [ | exact CRH | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; exact X] ] end;
      clear CRH;
      apply (stk_ccall_any A0 A1 _ _ ma mb xsp win V Nn _ _ AINVa CF1) in STlo; [| exact CEIL | intros a Ha X; exact X];
      apply (stk_ccall_any A0 A1 _ _ ma mb xsp win V Nn _ _ AINVa CF1) in STpad; [| keeplia CEIL LO ACV D0 | intros a Ha X; exact X];
      assert (SOBJ1 : vsb_obj LPA A1 mb S vr false);
      [ eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| | keeplia LO CEIL D0| exact VLS1| exact VLB1| intros a Ha X; exact X];
        eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi ACV CEIL LO]
      | ];
      assert (VAAa : bytes_at rsegs ma VA (u64s slots))
        by (eapply (bytes_at_munch LPA); [exact VAA| exact MU| rewrite u64s_length; intros a__ Ha__; cbn; keeplia Ha__ VLO]);
      assert (VAA1 : va_area mb VA slots);
      [ unfold va_area; apply (bytes_at_ccall LPA A0 A1 xsp win V Nn ma mb CF1 VA);
        [ rewrite u64s_length; eapply (crange_stack (L:=LPA) A0 _ _ ma); [exact AINVa| keeplia VLO LO CEIL ACV| keeplia VAB|];
          rewrite <- (u64s_length slots); eapply (bytes_at_mapped LPA); [exact VAAa| off_image_solve LPA || (unfold off_image; keeplia VLO VAB LO CEIL ACV)]
        | rewrite u64s_length; split; [keeplia VLO D0| intros i Hi X; exact X]
        | exact VAAa ]
      | clear VAAa ];
      assert (HSB1 : bytes_at rsegs mb HS hs);
      [ pose proof HSH as HSH'; destruct HSH' as [[E EHS]|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL)];
        [ rewrite E; apply bytes_at_nil; keeplia EHS
        | (first [ pose proof ((live_geomP LPA A0 _ _ hq hk AINV00 LQ)) as dR_5; dand5 dR_5 as _ _ Qlo Qhi _ | pose proof (live_geomP LPA A0 _ _ hq hk AINV00 LQ) as (_ & _ & Qlo & Qhi & _) ]); unfold kHighMemBeg in Qlo; all_app_facts;
          apply (bytes_at_ccall LPA A0 A1 xsp win V Nn ma mb CF1 HS);
          [ eapply (crange_block (L:=LPA) A0); [exact AINVa| exact LQ| exact Q1| exact Q2| clear; lia]
          | split; [keeplia Q1 Q2 Qhi LO CEIL D0| intros i Hi X; exact X]
          | eapply (bytes_at_munch LPA); [exact HSB| exact MU| intros a__ Ha__; cbn; keeplia Ha__ Q1 Q2 Qhi LO CEIL] ] ]
      | ];
      assert (STKSH1 : stack_shadow LPA mb SB N (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) (bv_unsigned sp + 64));
      [ pose proof STKSH as (SSB & SSN & _ & _ & SSC & SST); unfold kHighMemBeg in SST; all_app_facts;
        pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *);
        assert (SSBa : bytes_at rsegs ma SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
          by (eapply (bytes_at_munch LPA); [exact SSB| exact MU| rewrite repeat_length, Z2Nat.id by exact SSN; intros a__ Ha__; cbn; keeplia Ha__ SSC SST SHC8 LO CEIL ACV]);
        pose proof (stack_shadow_again _ _ SB N _ _ _ STKSH SSBa eq_refl) as SSa;
        assert (M0 : 0 <= bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) by keeplia CEIL LO ACV;
        assert (M1 : bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64 <= Z.max (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) alloc_ceiling) by (clear; lia);
        pose proof (stack_shadow_sub LPA _ SB N _ _ _ _ SSa M1 (Z.le_refl _) M0) as SSx;
        pose proof (crange_stack_shadow (Clg:=Clg) LPA A0 _ _ SB N _ _ AINVa SSx ltac:(clear; lia)) as CRS; clear SSx M0 M1;
        eapply stack_shadow_again; [exact STKSH| | reflexivity];
        apply (bytes_at_ccall LPA A0 A1 xsp win V Nn ma mb CF1 SB);
        [ rewrite zeros_length, Z2Nat.id by exact SSN; exact CRS
        | rewrite zeros_length, Z2Nat.id by exact SSN; split; [keeplia SSC SST SHC8 LO CEIL ACV D0| intros i Hi X; exact X]
        | exact SSBa ]
      | ]
    end.
    hide HSB.
    fold_cl_segs. clear UARV UARG Che Ghe Cme Gme Cmb Gmb Csh Gsh MIa HID.
    (* [comment removed for export] *)
    pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff 1 0%nat _ _ AINV1 FF1 VLS1) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff 1 0%nat _ _ AINV1 FF1 VLB1) as DJfB.
    change (fsize 1) with 128 in DJfS, DJfB.
    pose proof (sh_lo ff ltac:(keeplia FLO)) as SHFlo.   (* [comment removed for export] *)
    assert (SHDS : sh ff + 16 <= sh S \/ sh S + 5 <= sh ff) by (unfold sh; clear - DJfS FAL S16; try pose proof alloc_ceiling_val as ACV__; mlia).
    pose proof (as_live_shadow LPA _ _ _ S 40 AINV1 VLS1) as SHS0. fold_cl_segs. fold_aview.
    (first [ pose proof (SOBJ1) as dR_6; dand6 dR_6 as VSBC0 _ _ _ _ (bs0 & U80 & LBS0 & _) | pose proof SOBJ1 as (VSBC0 & _ & _ & _ & _ & (bs0 & U80 & LBS0 & _)) ]).
    pose proof (cenv_intro A1 mB mdB AINV1) as CE1.
    (* [comment removed for export] *)
    assert (MPof : forall (v : mem) jj, stk rsegs v lo (bv_unsigned sp + -192 - d) -> rw_cells rsegs v (bv_unsigned sp + -192 - d) [CB 88 jj] ->
               stk rsegs v (bv_unsigned sp + -192 - d + 88) (bv_unsigned sp + -104) ->
               rw_cells rsegs v (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
               mapped v (bv_unsigned sp - (192 + 16 + (80 + 8192))) (192 + 16 + (80 + 8192))).
    { intros v jj X1 X2 X3 X4.
      pose proof (stk_release rsegs _ _ _ _ X1 X2 ltac:(keeplia LO CEIL ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
      pose proof (stk_merge rsegs _ _ _ _ Y1 X3 ltac:(keeplia LO CEIL ACV D0)) as Y2.
      pose proof (stk_release rsegs _ _ _ _ Y2 X4 ltac:(keeplia LO CEIL ACV D0)) as Y3. cbn [cells_size csize Nat.add] in Y3.
      eapply (stk_mapped (L:=LPA)); [exact Y3| exact CEIL| keeplia LO| keeplia SPR]. }
    destruct (rw_cells_forget rsegs _ _ _ SCR) as [j88 SCR88]. cbn [cells_size csize Nat.add] in SCR88.
    pose proof (MPof _ _ STlo SCR88 STpad FRH) as MPB. clear SCR88.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (192 + 16 + (80 + 8192)), bv_unsigned sp); (ff, ff + 72); (sh ff, sh ff + 16)] (aview A1 mB)) as MU1.
    pose proof (wmono_refl rsegs (aview A1 mB)) as WM1.
    assert (CFP1 : client_fp LPA A1 (aview A1 mB) [(bv_unsigned sp - (192 + 16 + (80 + 8192)), bv_unsigned sp); (ff, ff + 72); (sh ff, sh ff + 16)]).
    { cbn. split; [left; split; [keeplia LO CEIL| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - (192 + 16 + (80 + 8192)))) with (192 + 16 + (80 + 8192)) by (clear; lia); exact MPB]]|].
      split; [right; right; left; exists ff, 1, 0%nat; split; [exact FF1| change (fsize 1) with 128; clear; lia]|].
      split; [right; right; right; exists ff, 1, 0%nat; split; [exact FF1| change (fsize 1 / 8) with 16; clear; lia]| exact I]. }
    hide DJfS. hide DJfB. hide VSBC0. hide U80. hide SHS0. hide VAA1. hide HSB1. hide STKSH1.
    unfold zcells in SHC. cbn [repeat] in SHC.
    ago AINV1. fold_cl_segs. fix_ret_pc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite (shr3_div8 ff). zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. change (ff / 8 + 2147450880) with (sh ff).
    (* [comment removed for export] *)
    fix_neg. sb1. sb1. sb1. sb1.
    (* [comment removed for export] *)
    zstep. fix_neg. sb1. sb1. sb1. sb1.
    (* [comment removed for export] *)
    zstep. fix_neg. sb1. sb1. sb1. sb1.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    sb1.
    (* [comment removed for export] *)
    unhide VSBC0. unhide SHS0. unhide DJfS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (VSBC : rw_cells rsegs mx S (vsb_cells vr))
        by (eapply (rw_cells_munch LPA); [exact VSBC0| exact MU1| exact WM1| rewrite vsb_cells_size; change (Z.of_nat 40) with 40; intros a__ Ha__; cbn; keeplia Ha__ Shi DJfS SH1n Slo SHSB LO CEIL ACV]);
      assert (SHS : bytes_at rsegs mx (sh S) (shpat 40))
        by (eapply (bytes_at_munch LPA); [exact SHS0| exact MU1| change (Z.of_nat (length (shpat 40))) with 5; intros a__ Ha__; cbn; keeplia Ha__ SHSB SHDS Slo FLO LO CEIL ACV])
    end.
    clear VSBC0 SHS0. hide DJfS.
    unfold vsb_cells in VSBC.
    assert (S8 : S mod 8 = 0) by (apply mod8_of_mod16; exact S16).
    (* [comment removed for export] *)
    zstep. zstep. vsb_leaf_call assert_VSB_integrity_ok VSBC VINV SHS CE1 MU1 STlo.
    (* [comment removed for export] *)
    zstep. zstep. zstep. vsb_leaf_call assert_VSB_state_ok VSBC VINV SHS CE1 MU1 STlo.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KA; zify_cond KA.
    { exfalso. rewrite Z.mod_small in KA by (unfold IMG_LO, RO_TOP in *; keeplia ARL ART IMGLO HLA). unfold IMG_LO in *. keeplia KA ARL IMGLO. }
    clear KA.
    (* [comment removed for export] *)
    zstep. if_cases KU; zify_cond KU. { dead KU. } clear KU.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [lia| exact S8]. } clear KU.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 11.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      exfalso. rewrite Verr in KE. revert KE. vm_compute. first [ intros X; discriminate X | intros X; apply X; reflexivity | congruence ].
    - (* [comment removed for export] *)
      assert (E0 : vb_error vr = 0) by exact Verr.
      clear KE.
      (* [comment removed for export] *)
      do 3 zstep.
      (* [comment removed for export] *)
      zstep. zstep. vsb_leaf_call vsb_indent_ok VSBC VINV SHS CE1 MU1 STlo.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. rewrite (shr3_div8 (S + 8)). zstep. rewrite (shr3_div8 (S + 24)). zstep. rewrite (shr3_div8 (S + 16)).
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      lazymatch type of FFC with rw_cells _ ?mx _ [?c1; ?c2; ?c3; ?c4; ?c5; CB 80 ?j80] =>
        apply (rw_cells_split_CB rsegs mx ff [c1; c2; c3; c4; c5] 80 j80 [] [24; 8; 48]%nat) in FFC; [| reflexivity];
        cbn [mk_CB_cells app] in FFC end.
      lazymatch type of FFC with rw_cells _ ?mx _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; CB 8 ?j8; ?c8] =>
        apply (rw_CB8_C8 rsegs mx ff [c1; c2; c3; c4; c5; c6] j8 [c8]) in FFC; cbn [app] in FFC end.
      destruct (rw_cells_forget rsegs _ _ _ SHC) as [shj SHC2]. pose proof (rw_CB_length _ _ _ _ _ SHC2) as LSH. cbn [cells_size csize Nat.add] in SHC2, LSH.
      (* [comment removed for export] *)
      unhide U80. unhide VAA1. unhide HSB1. unhide STKSH1. unhide DJfB.
      lazymatch type of MU1 with munch ?W _ ?mx =>
        assert (U8 : u8arr rsegs mx (vb_buf vr) bs0)
          by (apply (u8arr_transport rsegs W (aview A1 mB) mx); [exact U80| exact MU1| exact WM1| cbn [disjoint_from]; rewrite LBS0; keeplia Bhi CEIL LO DJfB SH1n Blo Vsz])
      end.
      (* [comment removed for export] *)
      pose_loop.
      change (Z_to_bv 64 (sh ff)) with (Z_to_bv 64 (ff / 8 + 2147450880)).
      lazymatch goal with MIq : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      eapply (vp_loop' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff A1 mB mdB mx _ _ _ _ _ shj bs0);
        [ exact D0 | exact AL16 | exact AINV1
        | eapply amd_frame_sbm_l; [exact SBMa| exact MH| exact MDF1]
        | exact FA
        | eapply munch_weaken; [| exact MU1]; unfold sub_fp, W1; ufs; cbn [outside]; intros x__ Hx__; keeplia Hx__
        | exact WM1
        | unfold W1; ufs; cbn; split; [left; split; [keeplia LO CEIL| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - (192 + 16 + (80 + 8192)))) with (192 + 16 + (80 + 8192)) by (clear; lia); exact MPB]]|];
          split; [right; right; left; exists ff, 1, 0%nat; split; [exact FF1| change (fsize 1) with 128; clear; lia]|];
          split; [right; right; right; exists ff, 1, 0%nat; split; [exact FF1| change (fsize 1 / 8) with 16; clear; lia]|];
          split; [right; left; exists (vb_buf vr), (vb_size vr); split; [exact VLB1| clear; lia]| exact I]
        | exact MIq | exact STlo | exact SCR | exact STpad | exact FRH | exact FFC | exact LSH | exact SHC2
        | exact SOBJ1 | exact E0 | exact U8 | exact LBS0 | exact VAA1 | exact HSB1 | ufs; exact STKSH1
        | ]
      end.
      (* [comment removed for export] *)
      ufs. eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A0 m0) _ (aview A1 mB) (aview A1 mB) _ []);
        [ exact MU | intros a Ha NO; left; cbn [outside] in NO; keeplia Ha NO
        | exact CF1 | keeplia D0 | keeplia D0
        | intros a X; exfalso; exact X | intros a X; left; exact X
        | exact (munch_refl [] (aview A1 mB))
        | intros a Ha NO; cbn [outside] in NO; exfalso; exact (NO I)
        | exact MPB ].
  Qed.
End S.
End A_VSq5u.


Module A_VSt8w.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpya4 AIcp3q7 AIcpq85 AIcpnnp AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSe3i A_VSa8f.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
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
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fr_alloc0 (A A1 : AS) (ff : Z) : Prop :=
       a_frame A ff = None /\ a_frame A1 ff = Some (0, 0%nat)
    /\ (forall g k' age', g <> ff -> a_frame A g = Some (k', age') -> a_frame A1 g = Some (k', if Z.eqb k' 0 then Datatypes.S age' else age'))
    /\ (forall g, g <> ff -> a_frame A g = None -> a_frame A1 g = None)
    /\ (forall q0, a_live A1 q0 = a_live A q0) /\ a_livebytes A1 = a_livebytes A /\ a_tinycred A1 = a_tinycred A /\ a_nlive A1 = a_nlive A
    /\ a_seccred A1 = a_seccred A
    /\ a_primcred A1 = a_primcred A   (* [comment removed for export] *)
    /\ ff mod 32 = 0 /\ app_range LPA ff 64 (* [comment removed for export] *) /\ ff + 64 <= alloc_ceiling /\ 0 <= sh ff /\ sh ff + 8 <= SHMAX.

  (* [comment removed for export] *)
  Lemma frames_aged_alloc0_mid_release : forall (A A1 A2 : AS) m2 md2 ff (n0 n1 : nat),
    a_frame A ff = None -> a_frame A1 ff = Some (0, 0%nat) ->
    (forall g k' age', g <> ff -> a_frame A g = Some (k', age') ->
        a_frame A1 g = Some (k', if Z.eqb k' 0 then S age' else age')) ->
    (forall g, g <> ff -> a_frame A g = None -> a_frame A1 g = None) ->
    frames_aged A1 A2 n0 n1 -> ainv A2 m2 md2 ->
    frames_aged A (a_release A2 ff) (S n0) n1.
  Proof.
    intros A A1 A2 m2 md2 ff n0 n1 FN FF AGE NONE [AG NN] AI2.
    destruct (AG ff 0 0%nat FF) as (d2 & HF2 & _).
    destruct (as_release_spec LPA A2 m2 md2 ff 0 _ AI2 HF2) as (RN & RO & _).
    split.
    - intros g k' age' HG.
      assert (NE : g <> ff) by (intros ->; rewrite FN in HG; discriminate HG).
      rewrite (RO g NE). pose proof (AGE g k' age' NE HG) as HG1.
      destruct (AG g _ _ HG1) as (d & HG2 & Hd). rewrite HG2.
      destruct (Z.eqb_spec k' 0) as [->|NK].
      + exists (S d)%nat. split; [f_equal; f_equal; lia|]. unfold fbound in *. cbn in *. lia.
      + exists d. split; [reflexivity|]. unfold fbound in *. rewrite (proj2 (Z.eqb_neq k' 0) NK) in *.
        destruct (Z.eqb k' 1); lia.
    - intros g HG. destruct (Z.eq_dec g ff) as [->|NE]; [exact RN|].
      rewrite (RO g NE). exact (NN g (NONE g NE HG)).
  Qed.

  (* [comment removed for export] *)
  Lemma frames_young_alloc0 : forall A A1 ff, frames_young A 1 1 -> fr_alloc0 A A1 ff -> frames_young A1 0 1.
  Proof.
    intros A A1 ff FY0 (FN & FF & AGE & NONE & _) g k age HG K01.
    destruct (Z.eq_dec g ff) as [->|NE].
    - rewrite FF in HG. injection HG as <- <-. unfold fbound, fslots. cbn. lia.
    - destruct (a_frame A g) as [[k0 age0]|] eqn:HG0.
      + rewrite (AGE g k0 age0 NE HG0) in HG. injection HG as <- EA.
        pose proof (FY0 g k0 age0 HG0 K01) as Y. unfold fbound in *.
        destruct K01 as [-> | ->]; cbn in *; subst age; cbn; lia.
      + rewrite (NONE g NE HG0) in HG. discriminate HG.
  Qed.

  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : AIcptdg.pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis VSNREAL : vsnreal_ok.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x2 x3 x4 x5 x6 x7 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (S : Z) (vr : vsb_rec)
            (Afmt : Z) (HS : Z) (hs : list byte) (lo SB N : Z) (T : TSet).
  Let slots : list word := [x2; x3; x4; x5; x6; x7].
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) S vr false.
  Hypothesis HF : forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT.
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  Hypothesis AFR : forall v, cenv v -> range_ok v Afmt la.          (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSL : SLOTS slots.
  Hypothesis HSB : bytes_at rsegs (aview A0 m0) HS hs.
  Hypothesis HSH : str_home A0 S vr HS hs.
  Hypothesis EM : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + Z.of_nat (length (OUT slots hs)) + 1) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 1 1.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + PRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - PRINTF_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      vsb_obj LPA A' v' S vr' false ->
      (vb_error vr <> 0 -> r = -1 /\ vr' = vr) ->
      (vb_error vr = 0 -> r = 0 /\ vb_error vr' = 0 /\
         (  vb_len vr' = vb_len vr + Z.of_nat (length (OUT slots hs))
         \/ (vb_len vr' = vb_size vr - 1 /\ vb_size vr' = vb_size vr /\ vb_buf vr' = vb_buf vr))) ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A0 q) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      frames_aged A0 A' 1 1 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      stk rsegs v' lo (bv_unsigned sp) ->
      bytes_at rsegs v' HS hs ->
      stack_shadow LPA v' SB N (bv_unsigned sp - PRINTF_STACK - 64) (bv_unsigned sp + 64) ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) PRINTF_STACK
               (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
               (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj HLA (conj HOUT (conj HOUT1 (conj P1 (conj P2 (conj PCM (conj FBY (conj VSNREAL
      (conj AINV00 (conj SOBJ (conj HF (conj ARL (conj ART (conj AFR (conj HPRE (conj HSL (conj HSB (conj HSH
      (conj EM (conj LBM (conj NLV (conj SCM (conj PRM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO (conj SPHI (conj STKSH K)))))))))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Definition PFRAME : list cell :=
    [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K STKSH SPHI LO CEIL SP16 TP FY SCM PRM NLV LBM EM HSH HSB HSL HPRE AFR ART ARL HF SOBJ AINV00 VSNREAL FBY PCM SLOTS fbytes P2 P1 HOUT1 HOUT HLA PRE nargs la FMT"] Lemma pf_exit : forall (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (d ff r : Z) (A1 A2 : AS) (m2 : mem) (md2 : Model)
                       (vr2 : vsb_rec) (j8 fj shj : list byte),
    0 <= d <= 16 ->
    ainv A2 m2 md2 -> mem_inv rsegs (aview A2 m2) -> amd_frame md0 md2 ->
    stk rsegs (aview A2 m2) lo (bv_unsigned sp + -128 - d) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -128 - d) [CB 8 j8; C8 (Z_to_bv 64 ff)] ->
    stk rsegs (aview A2 m2) (bv_unsigned sp + -128 - d + 16) (bv_unsigned sp + -112) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -112) PFRAME ->
    fr_alloc0 A0 A1 ff -> frames_aged A1 A2 0 1 ->
    length fj = 56%nat -> rw_cells rsegs (aview A2 m2) ff [CB 56 fj] ->
    length shj = 8%nat -> rw_cells rsegs (aview A2 m2) (sh ff) [CB 8 shj] ->
    vsb_obj LPA A2 (aview A2 m2) S vr2 false ->
    (vb_error vr <> 0 -> r = -1 /\ vr2 = vr) ->
    (vb_error vr = 0 -> r = 0 /\ vb_error vr2 = 0 /\
       (vb_len vr2 = vb_len vr + Z.of_nat (length (OUT slots hs)) \/ (vb_len vr2 = vb_size vr - 1 /\ vb_size vr2 = vb_size vr /\ vb_buf vr2 = vb_buf vr))) ->
    vb_len vr <= vb_len vr2 <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
    vb_size vr <= vb_size vr2 <= Z.max (vb_size vr) (vb_len vr2 + 4096) ->
    (vb_buf vr2 = vb_buf vr \/ (a_live A1 (vb_buf vr2) = None /\ a_live A2 (vb_buf vr) = None)) ->
    (forall p, p <> vb_buf vr -> p <> vb_buf vr2 -> a_live A2 p = a_live A1 p) ->
    a_livebytes A2 = a_livebytes A1 + vb_size vr2 - vb_size vr ->
    a_tinycred A2 = a_tinycred A1 -> a_nlive A2 = a_nlive A1 ->
    a_seccred A1 - (vsb_pot vr2 - vsb_pot vr) <= a_seccred A2 <= a_seccred A1 ->
    a_primcred A1 - (vsb_ppot vr2 - vsb_ppot vr) <= a_primcred A2 <= a_primcred A1 ->   (* [comment removed for export] *)
    bytes_at rsegs (aview A2 m2) HS hs ->
    stack_shadow LPA (aview A2 m2) SB N (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + ASTK))) - 64) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned A2) (bv_unsigned sp) PRINTF_STACK
           (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
           (fun a => frm ff 0 a \/ newblk (vb_buf vr2) (vb_size vr2) a) (aview A0 m0) (aview A2 m2) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -128 - d)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48))
                                    (Z_to_bv 64 (bv_unsigned sp + -128 - d))
                                    (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 Afmt) (Z_to_bv 64 S) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff)
                                    s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x8a9bc) fc None m2 (seg_rom rsegs)) md2) T.
  Proof.
    touch_all. intros until shj. intros D0 AINV MI MDF STlo SCR STpad FRH FA AG12 LFJ FFC LSH SHC SOBJ2 KE KO LEN2 SZ2 REL2 LIVEq2 LB2 TC2 NL2 SC2 PR2 HSB2 STKSH2 CF02.
    prelims.
    destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PR1 & FAL & FLO & FHI & SH0 & SH1). rewrite SHMAX_val in SH1. all_app_facts.
    pose proof (as_minv LPA A2 _ _ AINV) as [_ MH].
    assert (FF2 : a_frame A2 ff = Some (0, 0%nat)).
    { destruct AG12 as [AG _]. destruct (AG ff 0 0%nat FF1) as (dd & E & Hd). unfold fbound in Hd. cbn in Hd.
      replace dd with 0%nat in E by lia. exact E. }
    (* [comment removed for export] *)
    release_frame SCR STlo (bv_unsigned sp + -128 - d + 16).
    pose proof (stk_merge rsegs _ _ _ _ STlo STpad ltac:(keeplia D0 LO CEIL ACV)) as STm. clear STlo STpad.
    destruct (stk_carve rsegs _ lo _ 16 STm ltac:(keeplia D0 LO CEIL ACV)) as [STlo [j16 FRL]]. clear STm.
    change (Z.of_nat 16) with 16 in STlo, FRL. replace (bv_unsigned sp + -112 - 16) with (bv_unsigned sp + -128) in STlo, FRL by lia.
    assert (FR : rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -128) (CB 16 j16 :: PFRAME)).
    { apply (proj2 (rw_cells_app rsegs _ _ [CB 16 j16] _)). split; [exact FRL|]. cbn [cells_size csize Nat.add].
      eapply rwc_eq; [exact FRH| lia]. }
    clear FRL FRH. unfold PFRAME in FR.
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -128 - d) _ STlo ltac:(keeplia D0 LO CEIL ACV)) as [STlo' STpad]. clear STlo. rename STlo' into STlo.
    (* [comment removed for export] *)
    destruct (fframe_flag A2 m2 md2 ff 0 0%nat AINV FF2) as (fa & fb & FAW & FB & FRO & FRW & FOW & FNI).
    change (fsize 0) with 64 in FRO. replace (ff + 64 - 8) with (ff + 56) in FRO by lia.
    (* [comment removed for export] *)
    pose proof (vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap).
    pose proof SOBJ2 as (_ & VINV2 & VLS & VLB & VNE & _).
    unfold kHighMemBeg in Slo, Blo. all_app_facts.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 0%nat _ _ AINV FF2 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 0%nat _ _ AINV FF2 VLB) as DJfB.
    change (fsize 0) with 64 in DJfS, DJfB.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLS FOW) as OWS.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLB FOW) as OWB.
    pose proof (owned_outside_fframe A2 m2 md2 ff 0 0%nat _ AINV FF2 FOW) as [OWF OWSH].
    change (fsize 0) with 64 in OWF, OWSH. change (64 / 8) with 8 in OWSH.
    hide DJfS. hide DJfB. hide OWS. hide OWB. hide DSB. hide HSB2. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(sh ff, sh ff + 8); (ff, ff + 8); (fa, fa + 1)] (aview A2 m2)) as MU.
    pose proof (wmono_refl rsegs (aview A2 m2)) as WM.
    assert (CFR : client_fp_rel LPA A2 [ff] (aview A2 m2) [(sh ff, sh ff + 8); (ff, ff + 8); (fa, fa + 1)]).
    { unfold client_fp_rel. split; [| split; [| split; [| exact I]]].
      - right; right; right; left. exists ff, 0, 0%nat. split; [exact FF2|]. change (fsize 0 / 8) with 8. lia.
      - right; right; left. exists ff, 0, 0%nat. split; [exact FF2|]. change (fsize 0) with 64. lia.
      - right; right; right; right. exists ff, 0, 0%nat, (Z_to_bv 64 fa). split; [left; reflexivity|]. split; [exact FF2|].
        split; [exact FB|]. rewrite unsigned_lit by (keeplia FAW ACV); split; reflexivity. }
    hide FB.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. fix_neg. sb1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. fix_neg. do 8 sb1.
    (* [comment removed for export] *)
    zstep. unhide OWS. unhide OWB. try clear FRO. sb1. hide OWS. hide OWB. zstep.
    (* [comment removed for export] *)
    zstep. try replace (bv_unsigned sp + -48 + -80) with (bv_unsigned sp + -128) by lia.
    do 8 zstep. zstep.
    try replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with ST1 : stk _ ?mq lo _, ST2 : stk _ ?mq (bv_unsigned sp + -128 - d) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (stk_merge rsegs mq _ _ _ ST1 ST2 ltac:(keeplia D0 LO CEIL ACV)) as STm; clear ST1 ST2 end.
    lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -128) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      release_frame FRq STm (bv_unsigned sp) end.
    (* [comment removed for export] *)
    lazymatch goal with FLq : rw_cells _ ?mq fa [C1 ?b] |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (flag_cleared (Clg:=Clg) mq fa FLq FNI ltac:(keeplia FAW ACV)) as FL end.
    unhide FB. astop_rel1 AINV FF2 FB MU WM CFR FL.
    destruct (as_release_spec LPA A2 m2 md2 ff 0 0%nat AINV FF2) as (RN & RO & RL & RLB & RTC & RSC & RPC & RNL & RH & RE & ROW).
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ r (a_release A2 ff) m1 md1 vr2);
      [ assumption | assumption
      | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]]
      | (* [comment removed for export] *)
        unhide DJfS; unhide DJfB; unhide OWS; unhide OWB;
        pose proof SOBJ2 as (XC & XI & XLS & XLB & XNE & XB); split; [| split; [exact XI| split; [rewrite RL; exact XLS| split; [rewrite RL; exact XLB| split; [exact XNE|]]]]];
        [ eapply (rw_cells_munch LPA); [exact XC| exact MU| exact WM|]; rewrite vsb_cells_size; change (Z.of_nat 40) with 40;
          intros a Ha; cbn; keeplia Ha DJfS OWS SH1 Slo
        | destruct XB as (bs & [UB UW] & LENx & NULx); exists bs; split; [| split; [exact LENx| exact NULx]]; split;
          [ eapply (bytes_at_munch LPA); [exact UB| exact MU| rewrite LENx; intros a Ha; cbn; keeplia Ha DJfB OWB SH1 Blo]
          | eapply wr_at_transport; [exact UW| exact WM] ] ]
      | exact KE | exact KO | exact LEN2 | exact SZ2
      | intros p Hp1 Hp2; rewrite RL, (LIVEq2 p Hp1 Hp2); apply LV1
      | destruct REL2 as [E|[E1 E2]]; [left; exact E| right; split; [rewrite <- (LV1 (vb_buf vr2)); exact E1| rewrite RL; exact E2]]
      | eapply (frames_aged_alloc0_mid_release A0 A1 A2 m2 md2 ff 0%nat 1%nat); [exact FN| exact FF1| exact AGE| exact NONE| exact AG12| exact AINV]
      | rewrite RLB, LB2, LB1; reflexivity
      | rewrite RTC, TC2, TC1; reflexivity
      | rewrite RNL, NL2, NL1; reflexivity
      | rewrite RSC; try (generalize alloc_ceiling_val); clear - SC2 SC1; try pose proof alloc_ceiling_val as ACV__; lia
      | rewrite RPC; clear - PR2 PR1; lia (* [comment removed for export] *)
      | assumption
      | | | ]
    end.
    - (* [comment removed for export] *)
      unhide HSB2. pose proof HSH as [[E EHS]|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL)].
      + rewrite E. apply bytes_at_nil. pose proof (bytes_at_bound _ _ _ _ HSB2) as Bq. keeplia Bq.
      + assert (LQ2 : a_live A2 hq = Some hk).
        { rewrite (LIVEq2 hq NQB); [rewrite (LV1 hq); exact LQ|].
          intros Ehq. destruct REL2 as [Eb|[Eb _]]; [exact (NQB (eq_trans Ehq Eb))|]. rewrite <- Ehq, (LV1 hq), LQ in Eb. discriminate Eb. }
        pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 0 0%nat _ _ AINV FF2 LQ2) as DJfQ. change (fsize 0) with 64 in DJfQ.
        pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV LQ2 FOW) as OWQ.
        pose proof (live_geomP LPA A2 m2 md2 hq _ AINV LQ2) as (_ & _ & Qlo & _). unfold kHighMemBeg in Qlo. all_app_facts.
        eapply (bytes_at_munch LPA); [exact HSB2| exact MU|]. intros a Ha. cbn. keeplia Ha Q1 Q2 DJfQ OWQ SH1 Qlo.
    - (* [comment removed for export] *)
      assert (M0 : 0 <= bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) - 64) by keeplia CEIL LO ACV.
      assert (M1 : bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) - 64 <= Z.max (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) - 64) alloc_ceiling) by (clear; lia).
      pose proof (stack_shadow_sub LPA _ SB N _ _ _ _ STKSH2 M1 (Z.le_refl _) M0) as SSx.
      pose proof (crange_stack_shadow (Clg:=Clg) LPA A2 m2 md2 SB N _ _ AINV SSx ltac:(clear; lia)) as (_ & _ & CRS). clear SSx M0 M1.
      pose proof STKSH2 as (SSB & SSN & _ & _ & SSC & SST).
      pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *).
      eapply stack_shadow_again; [exact STKSH2| | reflexivity].
      eapply (bytes_at_munch LPA); [exact SSB| exact MU|]. rewrite zeros_length, Z2Nat.id by exact SSN.
      intros a Ha. cbn.
      assert (NOa : ~ owned A2 a). { destruct (CRS (a - SB) ltac:(keeplia Ha)) as [X _]. replace (SB + (a - SB)) with a in X by lia. exact X. }
      assert (NFa : a <> fa) by (intros ->; exact (NOa FOW)).
      unfold kHighMemBeg in SST. all_app_facts. keeplia Ha NFa SSC SST SHC8 SH1 FHI FLO ACV.
    - (* [comment removed for export] *)
      ufs. eapply (cframe_release (owned A0) (owned A2) (owned (a_release A2 ff))); [exact CF02| exact MU| | keeplia LO CEIL ACV| keeplia SPR| | | intros a X; right; exact X].
      + intros a Ha NO. cbn [outside] in NO.
        assert (CS : sh ff <= a < sh ff + 8 \/ ff <= a < ff + 8 \/ a = fa) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia). clear NO.
        destruct CS as [X|[X|X]]; [left; left; right; change (fsize 0 / 8) with 8; exact X| left; left; left; change (fsize 0) with 64; keeplia X| right; rewrite X; exact FOW].
      + intros i Hi. cbn. keeplia Hi SH1 FHI FAW LO CEIL ACV.
      + intros a Oa. apply ROW in Oa. destruct Oa as [X|[X|X]]; [left; exact X| right; left; left; change (fsize 0) with 64 in *; keeplia X| right; left; right; exact X].
  Qed.
End S.
End A_VSt8w.


Module A_VS8zm.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpya4 AIcp3q7 AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_VSe3i A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_VEr47.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47.B_Cf6tv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSt8w.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : AIcptdg.pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis VSNREAL : vsnreal_ok.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x2 x3 x4 x5 x6 x7 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (S : Z) (vr : vsb_rec)
            (Afmt : Z) (HS : Z) (hs : list byte) (lo SB N : Z) (T : TSet).
  Let slots : list word := [x2; x3; x4; x5; x6; x7].
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) S vr false.
  Hypothesis HF : forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT.
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  Hypothesis AFR : forall v, cenv v -> range_ok v Afmt la.          (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSL : SLOTS slots.
  Hypothesis HSB : bytes_at rsegs (aview A0 m0) HS hs.
  Hypothesis HSH : str_home A0 S vr HS hs.
  Hypothesis EM : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + Z.of_nat (length (OUT slots hs)) + 1) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 1 1.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + PRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - PRINTF_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      vsb_obj LPA A' v' S vr' false ->
      (vb_error vr <> 0 -> r = -1 /\ vr' = vr) ->
      (vb_error vr = 0 -> r = 0 /\ vb_error vr' = 0 /\
         (  vb_len vr' = vb_len vr + Z.of_nat (length (OUT slots hs))
         \/ (vb_len vr' = vb_size vr - 1 /\ vb_size vr' = vb_size vr /\ vb_buf vr' = vb_buf vr))) ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A0 q) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      frames_aged A0 A' 1 1 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      stk rsegs v' lo (bv_unsigned sp) ->
      bytes_at rsegs v' HS hs ->
      stack_shadow LPA v' SB N (bv_unsigned sp - PRINTF_STACK - 64) (bv_unsigned sp + 64) ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) PRINTF_STACK
               (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
               (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj HLA (conj HOUT (conj HOUT1 (conj P1 (conj P2 (conj PCM (conj FBY (conj VSNREAL
      (conj AINV00 (conj SOBJ (conj HF (conj ARL (conj ART (conj AFR (conj HPRE (conj HSL (conj HSB (conj HSH
      (conj EM (conj LBM (conj NLV (conj SCM (conj PRM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO (conj SPHI (conj STKSH K)))))))))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  Local Ltac pose_exit :=
    pose proof (pf_exit FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY VSNREAL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x2 x3 x4 x5 x6 x7 F fc m0 md0 A0 S vr Afmt HS hs lo SB N T AINV00 SOBJ HF ARL ART AFR HPRE HSL HSB HSH EM LBM NLV SCM PRM FY TP SP16 CEIL LO SPHI STKSH K) as pf_exit'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 K STKSH SPHI LO CEIL SP16 TP FY SCM PRM NLV LBM EM HSH HSB HSL HPRE AFR ART ARL HF SOBJ AINV00 slots N SB hs HS vr VSNREAL FBY PCM SLOTS fbytes P2 P1 HOUT1 HOUT HLA OUT PRE nargs la FMT"] Theorem VSB_printf_ok : forall (t0 t1 t2 a0 a1 t3 t4 t5 t6 : word),
    mem_inv rsegs (aview A0 m0) ->
    a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 Afmt ->
    stk rsegs (aview A0 m0) lo (bv_unsigned sp) ->
    srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 x2 x3 x4 x5 x6 x7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 VSB_printf_entry) fc None m0 (seg_rom rsegs)) md0) T.
  Proof.
    touch_all. intros until t6. intros MI Ha0 Ha1 ST. subst a0 a1. unfold VSB_printf_entry.
    prelims.
    pose proof (as_minv LPA A0 _ _ AINV00) as [_ MH].
    pose proof (HOUT _ _ _ HPRE) as OL.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    clear Smap Bmap Simg Bimg.
    pose proof SOBJ as (_ & VINV & VLS & VLB & VNE & _).
    pose proof VINV as VINVx. (first [ dand9 VINVx as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm Vsm | destruct VINVx as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm & Vsm) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(exact Shi)) as SHSB. rewrite SHMAX_val in SHSB. change ((40 + 7) / 8) with 5 in SHSB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(exact Bhi)) as SHBB. rewrite SHMAX_val in SHBB.
    hide DSB.
    (* [comment removed for export] *)
    pose proof (cenv_intro A0 m0 md0 AINV00) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (uar_cells_of_consts _ (proj1 CE)) as [UARG UARV]. fold_aview. open_map_cells MC.
    hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))), bv_unsigned sp)] (aview A0 m0)) as MU.
    pose proof (wmono_refl rsegs (aview A0 m0)) as WM.
    assert (WMAP : mapped (aview A0 m0) (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192)))) (128 + 16 + (192 + 16 + (80 + 8192))))
      by (eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]).
    assert (CFP : client_fp LPA A0 (aview A0 m0) [(bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))), bv_unsigned sp)]).
    { cbn. split; [| exact I]. left. split; [lia|]. split; [lia|].
      replace (bv_unsigned sp - (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))))) with (128 + 16 + (192 + 16 + (80 + 8192))) by lia. exact WMAP. }
    hide HSB.
    ago AINV00. fold_cl_segs.
    (* [comment removed for export] *)
    carve_frame 112%nat ST. rename FR into FRH. carve_frame 16%nat ST. rename FR into FR0.
    (* [comment removed for export] *)
    do 10 zstep.
    (* [comment removed for export] *)
    zstep. try replace (bv_unsigned sp + -128 + 80) with (bv_unsigned sp + -48) by lia.
    (* [comment removed for export] *)
    zstep.
    assert (AL16a : (bv_unsigned sp + -128) mod 16 = 0).
    { pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as Dv. rewrite SP16, Z.add_0_r in Dv. rewrite Dv.
      replace (16 * (bv_unsigned sp / 16) + -128) with ((bv_unsigned sp / 16 - 8) * 16) by lia. apply Z_mod_mult. }
    (first [ pose proof ((land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a)) as dR_3; dex1 dR_3 as d; dand3 dR_3 as Dd ELAND AL32 | pose proof ((land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a)) as dR_3; dand4 dR_3 as d Dd ELAND AL32 | destruct (land_align32_w (bv_unsigned sp + -128) ltac:(keeplia SPR LO CEIL ACV) AL16a) as (d & Dd & ELAND & AL32) ]). clear AL16a.
    rewrite ELAND. clear ELAND. assert (D0 : 0 <= d <= 16) by (try (generalize alloc_ceiling_val); clear - Dd; try pose proof alloc_ceiling_val as ACV__; lia). clear Dd.
    pose proof (mod16_of_mod32_vp _ AL32) as AL16.
    (* [comment removed for export] *)
    release_frame FR0 ST (bv_unsigned sp + -112).
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -128 - d + 16) _ ST ltac:(keeplia D0 LO CEIL ACV)) as [STl STpad]. clear ST.
    destruct (stk_carve rsegs _ lo _ 16 STl ltac:(keeplia D0 LO CEIL ACV)) as [STlo [jp SCR]]. clear STl.
    change (Z.of_nat 16) with 16 in STlo, SCR.
    replace (bv_unsigned sp + -128 - d + 16 - 16) with (bv_unsigned sp + -128 - d) in STlo, SCR by lia.
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    do 8 zstep.
    (* [comment removed for export] *)
    zstep. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). if_false.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    astop AINV00 MU WM CFP. fold_cl_segs.
    lazymatch goal with AIq : ainv A0 ?mq ?mdq, SBq : same_but_materialized md0 ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVa; rename SBq into SBMa end.
    lazymatch goal with MIq : mem_inv _ ?ma |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      rename MIq into MIa;
      assert (MPW : mapped ma (bv_unsigned sp + -128 - d - ASTK) ASTK)
        by (unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact STlo | exact CEIL | keeplia LO D0 | keeplia D0]) end.
    eapply (smalloc_acall 0);
      [ exact AINVa | exact MIa | left; reflexivity | reflexivity | change (fsize 0) with 64; clear; lia
      | exact (frames_young_smalloc A0 0 1%nat 1%nat FY (or_introl (conj eq_refl (le_n 1%nat))))
      | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); exact AL16
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); unfold ASTK; keeplia CEIL LO D0
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); exact MPW | ].
    clear MPW.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A1 mB mdB fj fa fb
           AINV1 MI1 MDF1 LV1 LB1 TC1 NL1 SC1 PR1 NZ FN FF1 AGE NONE GEOM LFJ FFC SHC FRO CF1.
    clear FRO. pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
    change (Z.to_nat (fsize 0 - 8)) with 56%nat in LFJ, FFC. change (Z.to_nat (fsize 0 / 8)) with 8%nat in SHC.
    (first [ dand5 GEOM as FAL FLO FHI SH0 SH1 | destruct GEOM as (FAL & FLO & FHI & SH0 & SH1) ]).
    change (fsize 0) with 64 in FHI, FLO. change (fsize 0 / 8) with 8 in SH1. unfold kHighMemBeg in FLO. all_app_facts.
    pose proof SH1 as SH1n. rewrite SHMAX_val in SH1n.
    rewrite unsigned_lit in CF1 by (keeplia SPR D0 LO CEIL ACV). unfold ASTK in CF1.
    assert (FA : fr_alloc0 A0 A1 ff).
    { split; [exact FN|]. split; [exact FF1|]. split; [exact AGE|]. split; [exact NONE|]. split; [exact LV1|]. split; [exact LB1|].
      split; [exact TC1|]. split; [exact NL1|]. split; [exact SC1|]. split; [exact PR1|]. split; [exact FAL|]. split; [exact FLO_a|]. split; [exact FHI|].
      split; [exact SH0| exact SH1]. }
    assert (VLS1 : a_live A1 S = Some 40) by (rewrite (LV1 S); exact VLS).
    assert (VLB1 : a_live A1 (vb_buf vr) = Some (vb_size vr)) by (rewrite (LV1 (vb_buf vr)); exact VLB).
    (* [comment removed for export] *)
    unhide HSB.
    lazymatch type of CF1 with cframe _ _ _ ?xsp ?win ?V ?Nn ?ma ?mb =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -128 - d) 16 AINVa ltac:(keeplia ACV CEIL LO D0) ltac:(keeplia SPR D0)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SCR ltac:(off_image_solve LPA))) as CR0;
      lazymatch type of SCR with rw_cells _ _ _ ?cs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 _ cs) in SCR;
        [ | exact CR0 | cbn [Cells.cells_size Cells.csize Nat.add length app firstn skipn]; split; [keeplia D0| intros i Hi X; exact X] ] end;
      clear CR0;
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A0 _ _ ma (bv_unsigned sp + -112) 112 AINVa ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRH ltac:(off_image_solve LPA))) as CRH;
      lazymatch type of FRH with rw_cells _ _ _ ?cs =>
        apply (rw_cells_ccall LPA A0 A1 xsp win V Nn ma mb CF1 _ cs) in FRH;
        [ | exact CRH | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; exact X] ] end;
      clear CRH;
      apply (stk_ccall_any A0 A1 _ _ ma mb xsp win V Nn _ _ AINVa CF1) in STlo; [| exact CEIL | intros a Ha X; exact X];
      apply (stk_ccall_any A0 A1 _ _ ma mb xsp win V Nn _ _ AINVa CF1) in STpad; [| keeplia CEIL LO ACV D0 | intros a Ha X; exact X];
      assert (SOBJ1 : vsb_obj LPA A1 mb S vr false);
      [ eapply (vsb_obj_ccall A0 A1); [exact AINVa| exact CF1| | keeplia LO CEIL D0| exact VLS1| exact VLB1| intros a Ha X; exact X];
        eapply vsb_obj_munch; [exact SOBJ| exact MU| exact WM| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi ACV CEIL LO]
      | ];
      assert (HSB1 : bytes_at rsegs mb HS hs);
      [ pose proof HSH as HSH'; destruct HSH' as [[E EHS]|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL)];
        [ rewrite E; apply bytes_at_nil; keeplia EHS
        | (first [ pose proof ((live_geomP LPA A0 _ _ hq hk AINV00 LQ)) as dR_5; dand5 dR_5 as _ _ Qlo Qhi _ | pose proof (live_geomP LPA A0 _ _ hq hk AINV00 LQ) as (_ & _ & Qlo & Qhi & _) ]); unfold kHighMemBeg in Qlo; all_app_facts;
          apply (bytes_at_ccall LPA A0 A1 xsp win V Nn ma mb CF1 HS);
          [ eapply (crange_block (L:=LPA) A0); [exact AINVa| exact LQ| exact Q1| exact Q2| clear; lia]
          | split; [keeplia Q1 Q2 Qhi LO CEIL D0| intros i Hi X; exact X]
          | eapply (bytes_at_munch LPA); [exact HSB| exact MU| intros a__ Ha__; cbn; keeplia Ha__ Q1 Q2 Qhi LO CEIL] ] ]
      | ];
      assert (STKSH1 : stack_shadow LPA mb SB N (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) - 64) (bv_unsigned sp + 64));
      [ pose proof STKSH as (SSB & SSN & _ & _ & SSC & SST); unfold kHighMemBeg in SST; all_app_facts;
        pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *);
        assert (SSBa : bytes_at rsegs ma SB (repeat (Z_to_bv 8 0) (Z.to_nat N)))
          by (eapply (bytes_at_munch LPA); [exact SSB| exact MU| rewrite repeat_length, Z2Nat.id by exact SSN; intros a__ Ha__; cbn; keeplia Ha__ SSC SST SHC8 LO CEIL ACV]);
        pose proof (stack_shadow_again _ _ SB N _ _ _ STKSH SSBa eq_refl) as SSa;
        assert (M0 : 0 <= bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) - 64) by keeplia CEIL LO ACV;
        assert (M1 : bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) - 64 <= Z.max (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) - 64) alloc_ceiling) by (clear; lia);
        pose proof (stack_shadow_sub LPA _ SB N _ _ _ _ SSa M1 (Z.le_refl _) M0) as SSx;
        pose proof (crange_stack_shadow (Clg:=Clg) LPA A0 _ _ SB N _ _ AINVa SSx ltac:(clear; lia)) as CRS; clear SSx M0 M1;
        eapply stack_shadow_again; [exact STKSH| | reflexivity];
        apply (bytes_at_ccall LPA A0 A1 xsp win V Nn ma mb CF1 SB);
        [ rewrite zeros_length, Z2Nat.id by exact SSN; exact CRS
        | rewrite zeros_length, Z2Nat.id by exact SSN; split; [keeplia SSC SST SHC8 LO CEIL ACV D0| intros i Hi X; exact X]
        | exact SSBa ]
      | ]
    end.
    hide HSB.
    fold_cl_segs. clear UARV UARG Che Ghe Cme Gme Cmb Gmb Csh Gsh MIa HID.
    (* [comment removed for export] *)
    pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff 0 0%nat _ _ AINV1 FF1 VLS1) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff 0 0%nat _ _ AINV1 FF1 VLB1) as DJfB.
    change (fsize 0) with 64 in DJfS, DJfB.
    pose proof (sh_lo ff ltac:(keeplia FLO)) as SHFlo.   (* [comment removed for export] *)
    assert (SHDS : sh ff + 8 <= sh S \/ sh S + 5 <= sh ff) by (unfold sh; clear - DJfS FAL S16; try pose proof alloc_ceiling_val as ACV__; mlia).
    assert (SHDB : sh ff + 8 <= sh (vb_buf vr) \/ sh (vb_buf vr) + (vb_size vr + 7) / 8 <= sh ff) by (unfold sh; clear - DJfB FAL Vbm Vsz; try pose proof alloc_ceiling_val as ACV__; mlia).
    (* [comment removed for export] *)
    assert (MPof : forall (v : mem) jj, stk rsegs v lo (bv_unsigned sp + -128 - d) -> rw_cells rsegs v (bv_unsigned sp + -128 - d) [CB 16 jj] ->
               stk rsegs v (bv_unsigned sp + -128 - d + 16) (bv_unsigned sp + -112) ->
               rw_cells rsegs v (bv_unsigned sp + -112) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7] ->
               mapped v (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192)))) (128 + 16 + (192 + 16 + (80 + 8192)))).
    { intros v jj X1 X2 X3 X4.
      pose proof (stk_release rsegs _ _ _ _ X1 X2 ltac:(keeplia LO CEIL ACV D0)) as Y1. cbn [cells_size csize Nat.add] in Y1.
      pose proof (stk_merge rsegs _ _ _ _ Y1 X3 ltac:(keeplia LO CEIL ACV D0)) as Y2.
      pose proof (stk_release rsegs _ _ _ _ Y2 X4 ltac:(keeplia LO CEIL ACV D0)) as Y3. cbn [cells_size csize Nat.add] in Y3.
      eapply (stk_mapped (L:=LPA)); [exact Y3| exact CEIL| keeplia LO| keeplia SPR]. }
    destruct (rw_cells_forget rsegs _ _ _ SCR) as [j16 SCR16]. cbn [cells_size csize Nat.add] in SCR16.
    pose proof (MPof _ _ STlo SCR16 STpad FRH) as MPB. clear SCR16.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))), bv_unsigned sp); (ff, ff + 40); (sh ff, sh ff + 8)] (aview A1 mB)) as MU1.
    pose proof (wmono_refl rsegs (aview A1 mB)) as WM1.
    assert (CFP1 : client_fp LPA A1 (aview A1 mB) [(bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))), bv_unsigned sp); (ff, ff + 40); (sh ff, sh ff + 8)]).
    { cbn. split; [left; split; [keeplia LO CEIL| split; [keeplia SPR| replace (bv_unsigned sp - (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))))) with (128 + 16 + (192 + 16 + (80 + 8192))) by (clear; lia); exact MPB]]|].
      split; [right; right; left; exists ff, 0, 0%nat; split; [exact FF1| change (fsize 0) with 64; clear; lia]|].
      split; [right; right; right; exists ff, 0, 0%nat; split; [exact FF1| change (fsize 0 / 8) with 8; clear; lia]| exact I]. }
    hide DJfS. hide DJfB. hide SHDS. hide SHDB. hide HSB1. hide STKSH1.
    unfold zcells in SHC. cbn [repeat] in SHC.
    ago AINV1. fold_cl_segs. fix_ret_pc.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite (shr3_div8 ff). zstep. change (ff / 8 + 2147450880) with (sh ff). zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. fix_neg. sb1. sb1. sb1. sb1.
    (* [comment removed for export] *)
    zstep. fix_neg. sb1. sb1. sb1. sb1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    unhide HSB1. unhide STKSH1. unhide DJfS. unhide DJfB. unhide SHDS. unhide SHDB.
    astop AINV1 MU1 WM1 CFP1.
    lazymatch goal with AIq : ainv A1 ?mq ?mdq, SBq : same_but_materialized mdB ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
      rename AIq into AINVb; rename SBq into SBMb end.
    (* [comment removed for export] *)
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) _) _ =>
      pose proof FRH as FRH2; apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_] _)) in FRH2; destruct FRH2 as [_ FRV];
      cbn [cells_size csize Nat.add] in FRV; replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in FRV by (clear; lia) end.
    lazymatch goal with MIq : mem_inv _ (aview A1 ?mq) |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
    eapply (VSB_vprintf_ok FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY VSNREAL
              _ _ gp tp _ _ _ _ _ _ _ s7 s8 s9 s10 s11 F fc mq mdq A1 S vr Afmt (bv_unsigned sp + -48) slots HS hs lo SB N T);
      [ exact AINVb
      | eapply vsb_obj_munch; [exact SOBJ1| exact MU1| exact WM1| intros a__ Ha__; cbn; keeplia Ha__ Shi Bhi DJfS DJfB SH1n Slo Blo LO CEIL ACV]
      | exact HF | exact ARL | exact ART | exact AFR
      | unfold va_area; change slots with [x2; x3; x4; x5; x6; x7]; cbn [u64s]; rewrite !app_nil_r;
        pose proof (bytes_at_of_rw_cells _ _ _ _ FRV) as B2; cbn [cells_bytes cbytes app] in B2; rewrite ?app_nil_r in B2; exact B2
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); keeplia D0
      | change slots with [x2; x3; x4; x5; x6; x7]; cbn [length]; keeplia SPHI
      | exact HPRE | exact HSL
      | eapply (bytes_at_munch LPA); [exact HSB1| exact MU1|];
        pose proof HSH as HSH'; destruct HSH' as [[E EHS]|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL)];
        [ rewrite E; cbn; intros a__ Ha__; exfalso; keeplia Ha__
        | (first [ pose proof ((live_geomP LPA A0 _ _ hq hk AINV00 LQ)) as dR_6; dand5 dR_6 as _ _ Qlo Qhi _ | pose proof (live_geomP LPA A0 _ _ hq hk AINV00 LQ) as (_ & _ & Qlo & Qhi & _) ]); unfold kHighMemBeg in Qlo; all_app_facts;
          assert (LQ1 : a_live A1 hq = Some hk) by (rewrite (LV1 hq); exact LQ);
          pose proof (as_frame_blk_disjoint LPA A1 mB mdB ff 0 0%nat _ _ AINV1 FF1 LQ1) as DJfQ; change (fsize 0) with 64 in DJfQ;
          intros a__ Ha__; cbn; keeplia Ha__ Q1 Q2 Qlo Qhi DJfQ SH1n LO CEIL ACV ]
      | (* [comment removed for export] *) pose proof HSH as HSH'; destruct HSH' as [X|(hq & hk & LQ & REST)]; [left; exact X| right; exists hq, hk; split; [rewrite (LV1 hq); exact LQ| exact REST]]
      | exact EM | rewrite LB1; exact LBM | rewrite NL1; exact NLV | rewrite SC1; exact SCM | rewrite PR1; exact PRM (* [comment removed for export] *)
      | exact (frames_young_alloc0 A0 A1 ff FY FA)
      | exact TP
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); exact AL16
      | exact CEIL
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); ufs; keeplia LO D0
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); keeplia SPHI D0
      | (* [comment removed for export] *)
        rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); ufs;
        (first [ pose proof (STKSH1) as dR_7; dand6 dR_7 as SSB SSN _ _ SSC SST | pose proof STKSH1 as (SSB & SSN & _ & _ & SSC & SST) ]); unfold kHighMemBeg in SST; all_app_facts;
        pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *);
        assert (M0 : 0 <= bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) - 64) by keeplia CEIL LO ACV;
        eapply stack_shadow_again; [eapply (stack_shadow_sub LPA _ SB N); [exact STKSH1| keeplia D0| keeplia D0| exact M0] | | reflexivity];
        eapply (bytes_at_munch LPA); [exact SSB| exact MU1| rewrite ?zeros_length, ?repeat_length, Z2Nat.id by exact SSN; intros a__ Ha__; cbn; keeplia Ha__ SSC SST SHC8 SH1n FLO ACV CEIL LO]
      | (* [comment removed for export] *)
      | exact MIq | reflexivity | reflexivity | reflexivity
      | rewrite unsigned_lit by (keeplia SPR D0 LO CEIL ACV); exact STlo ]
    end.
    cbv zeta. intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' r A2 mE mdE vr2.
    intros AINV2 MI2 MDF2 SOBJ2 KE KO LEN2 SZ2 LIVEq2 REL2 AG12 LB2 TC2 NL2 SC2 PR2 ST2 VAA2 HSB2 STKSH2 CFe.
    rewrite unsigned_lit in ST2, STKSH2, CFe by (keeplia SPR D0 LO CEIL ACV). ufs.
    replace (ret_pc (Z_to_bv 64 0x8a9bc)) with (Z_to_bv 64 0x8a9bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (as_minv LPA A2 _ _ AINV2) as [_ MH2].
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LPA A2 _ _ S vr2 false AINV2 SOBJ2)) as dR_8; dand11 dR_8 as _ _ _ _ NB16 NBlo NBhi _ DSNB _ _ | pose proof (vsb_obj_geom LPA A2 _ _ S vr2 false AINV2 SOBJ2) as (_ & _ & _ & _ & NB16 & NBlo & NBhi & _ & DSNB & _ & _) ]).
    unfold kHighMemBeg in NBlo. all_app_facts.
    pose proof SH1n as SH1m.
    destruct (rw_cells_forget rsegs _ _ _ SCR) as [j16a SCRa]. cbn [cells_size csize Nat.add] in SCRa.
    pose proof (MPof _ _ STlo SCRa STpad FRH) as MPa. clear SCRa.
    (* [comment removed for export] *)
    lazymatch type of CFe with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ ma (bv_unsigned sp + -128 - d) 16 AINVb ltac:(keeplia ACV CEIL LO D0) ltac:(keeplia SPR D0)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ SCR ltac:(off_image_solve LPA))) as CR1;
      apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CFe) in SCR;
        [| exact CR1 | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; unfold newblk, blk in X; keeplia Hi X Shi Bhi SHSB SHBB SPR LO CEIL ACV D0] ];
      clear CR1;
      apply (stk_ccall_any A1 A2 _ _ ma mb xsp win V Nn _ _ AINVb CFe) in STpad;
        [| keeplia LO CEIL ACV D0 | intros a Ha X; unfold newblk, blk in X; keeplia Ha X Shi Bhi SHSB SHBB SPR LO CEIL ACV D0 ];
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ ma (bv_unsigned sp + -112) 112 AINVb ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FRH ltac:(off_image_solve LPA))) as CR2;
      apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CFe) in FRH;
        [| exact CR2 | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia D0| intros i Hi X; unfold newblk, blk in X; keeplia Hi X Shi Bhi SHSB SHBB SPR LO CEIL ACV D0] ];
      clear CR2;
      apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CFe ff) in FFC;
        [| eapply crange_fframe; [exact AINVb| exact FF1| clear; lia| cbn; change (fsize 0) with 64; clear; lia| cbn; clear; lia]
         | cbn [Cells.cells_size Cells.csize Nat.add length app firstn skipn]; rewrite ?firstn_length, ?skipn_length, ?LFJ; split; [keeplia FHI LO CEIL D0|];
           intros i Hi X; unfold newblk, blk in X; keeplia Hi X DJfS DJfB SHSB SHBB FLO ];
      apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CFe (sh ff)) in SHC;
        [| eapply crange_fshadow; [exact AINVb| exact FF1| clear; lia| cbn; change (fsize 0 / 8) with 8; clear; lia| cbn; clear; lia]
         | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SH1m LO CEIL ACV D0|];
           intros i Hi X; unfold newblk, blk in X; keeplia Hi X SHDS SHDB Slo Blo SH1m ]
    end.
    (* [comment removed for export] *)
    destruct (rw_cells_forget rsegs _ _ _ FFC) as [fj2 FFC2]. pose proof (rw_CB_length _ _ _ _ _ FFC2) as LFJ2. cbn [cells_size csize Nat.add] in FFC2, LFJ2.
    destruct (rw_cells_forget rsegs _ _ _ SHC) as [shj SHC2]. pose proof (rw_CB_length _ _ _ _ _ SHC2) as LSH. cbn [cells_size csize Nat.add] in SHC2, LSH.
    pose_exit.
    eapply (pf_exit' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d ff r A1 A2 mE mdE vr2 _ fj2 shj);
      [ exact D0 | exact AINV2 | exact MI2
      | eapply amd_frame_sbm_l; [exact SBMa| exact MH| eapply amd_frame_trans; [exact MDF1| eapply amd_frame_sbm_l; [exact SBMb| exact MH1| exact MDF2]]]
      | exact ST2 | exact SCR | exact STpad | exact FRH | exact FA | exact AG12 | exact LFJ2 | exact FFC2 | exact LSH | exact SHC2
      | exact SOBJ2 | exact KE | exact KO | exact LEN2 | exact SZ2
      | exact REL2
      | exact LIVEq2 | exact LB2 | exact TC2 | exact NL2 | exact SC2 | exact PR2 (* [comment removed for export] *) | exact HSB2
      | ufs; (first [ pose proof (STKSH2) as dR_9; dand3 dR_9 as SSB2 SSN2 _ | pose proof STKSH2 as (SSB2 & SSN2 & _) ]); eapply stack_shadow_again; [exact STKSH1| exact SSB2| reflexivity]
      | ].
    (* [comment removed for export] *)
    ufs. lazymatch type of CFe with cframe _ _ _ _ _ _ _ ?ma ?mb =>
      eapply cframe_newV;
      [ eapply (cframe_seq LPA _ (owned A1) _ _ (128 + 16 + (192 + 16 + (80 + 8192))) _ _
                 (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40)) (frm ff 0) _ _ _ _ (aview A0 m0) ma mb);
        [ eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A0 m0) _ (aview A1 mB) ma _ _);
          [ exact MU | intros a Ha NO; left; cbn [outside] in NO; keeplia Ha NO
          | exact CF1 | keeplia D0 | keeplia D0
          | intros a X; exfalso; exact X | intros a X; left; exact X
          | exact MU1
          | intros a Ha NO; cbn [outside] in NO;
            assert (CS : (bv_unsigned sp - (128 + 16 + (192 + 16 + (80 + 8192))) <= a < bv_unsigned sp) \/ (ff <= a < ff + 40) \/ (sh ff <= a < sh ff + 8)) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia); clear NO;
            destruct CS as [X|[X|X]]; [left; exact X| right; right; left; change (fsize 0) with 64; keeplia X| right; right; right; change (fsize 0 / 8) with 8; exact X]
          | exact MPa ]
        | eapply (cframe_reframe LPA _ _ _ _ (bv_unsigned sp) (128 + 16 + (192 + 16 + (80 + 8192)))); [exact CFe| keeplia D0| keeplia D0|]
        | clear; lia | clear; lia |
        | intros a X; exact X | intros a X; right; exact X | intros a X; exact X ]
      | intros a [X|X]; [left; left; exact X| left; right; left; exact X] ]
    end.
    all: lazymatch type of SCR with rw_cells _ ?mx _ _ =>
           destruct (rw_cells_forget rsegs _ _ _ SCR) as [j16' SCR16']; cbn [cells_size csize Nat.add] in SCR16';
           eapply (MPof _ _); [exact ST2| exact SCR16'| exact STpad| exact FRH] end.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vsnreal_holds : vsnreal_ok.
Proof. intros v CH. apply (consts_lookup v _ _ CH). vm_compute. reflexivity. Qed.

End CEIL.

(* [comment removed for export] *)
Section Inst.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Definition VSB_printf_c_ok    := VSB_printf_ok FMT_C 3 1 PRE_C OUT_C eq_refl HOUT_C HOUT1_C OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pc1_c.pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_p0nl.pc2_c
                                     FMTB_C SLOTS_C pcm_fmt_c FBY_C vsnreal_holds.
  Definition VSB_printf_pfx_ok  := VSB_printf_ok FMT_PFX 6 2 PRE_PFX OUT_PFX eq_refl HOUT_PFX HOUT1_PFX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pf3s.pc1_pfx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_p0nl.pc2_pfx
                                     FMTB_PFX SLOTS_S pcm_fmt_pfx FBY_PFX vsnreal_holds.
  Definition VSB_printf_host_ok := VSB_printf_ok FMT_HOST 13 3 PRE_HOST OUT_HOST eq_refl HOUT_HOST HOUT1_HOST OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pis0.pc1_host OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_p0nl.pc2_host
                                     FMTB_HOST SLOTS_S pcm_fmt_host FBY_HOST vsnreal_holds.
End Inst.
End A_VS8zm.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_veqih.

Module A_veq11.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require RA_vju4 RA_vrdi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pf3s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pis0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_p0nl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vju4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpkua AIcpnnp AIcptdg AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpoo5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpoo5.AIcp1os OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcp8zl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Potrl A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_La0bg A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vei6d A_vez59 A_VSe3i A_VSa8f A_VStbd A_VEr47 A_VSbb4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_veqih.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_veqih.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_fmtc : Z := 0x23840.      (* [comment removed for export] *)
Definition A_fmtpfx : Z := 0x23ee0.    (* [comment removed for export] *)
Definition A_fmthost : Z := 0x23de0.   (* [comment removed for export] *)
Definition A_http : Z := 0x23d60.      (* [comment removed for export] *)
Definition A_https : Z := 0x23e00.     (* [comment removed for export] *)
Definition A_apos : Z := 0x23f00.      (* [comment removed for export] *)   (* [comment removed for export] *)
Definition A_quot : Z := 0x23f20.      (* [comment removed for export] *)
Definition A_lt : Z := 0x23f40.        (* [comment removed for export] *)
Definition A_gt : Z := 0x23f60.        (* [comment removed for export] *)
Definition A_amp : Z := 0x23f80.       (* [comment removed for export] *)

Lemma fmt_c_at : forall m, mem_inv rsegs m -> ro_cells rsegs m A_fmtc FMT_C.
Proof.
  intros m MI. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia|]. cbn [cells_bytes cbytes app].
  apply (ro_bytes_at rsegs m); [exact MI| unfold A_fmtc; lia| cbn; unfold A_fmtc; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma fmt_pfx_at : forall m, mem_inv rsegs m -> ro_cells rsegs m A_fmtpfx FMT_PFX.
Proof.
  intros m MI. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia|]. cbn [cells_bytes cbytes app].
  apply (ro_bytes_at rsegs m); [exact MI| unfold A_fmtpfx; lia| cbn; unfold A_fmtpfx; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma fmt_host_at : forall m, mem_inv rsegs m -> ro_cells rsegs m A_fmthost FMT_HOST.
Proof.
  intros m MI. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia|]. cbn [cells_bytes cbytes app].
  apply (ro_bytes_at rsegs m); [exact MI| unfold A_fmthost; lia| cbn; unfold A_fmthost; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Definition LIT_http : list byte := [Z_to_bv 8 104; Z_to_bv 8 116; Z_to_bv 8 116; Z_to_bv 8 112; Z_to_bv 8 58; Z_to_bv 8 47; Z_to_bv 8 47].
Definition LIT_https : list byte := [Z_to_bv 8 104; Z_to_bv 8 116; Z_to_bv 8 116; Z_to_bv 8 112; Z_to_bv 8 115; Z_to_bv 8 58; Z_to_bv 8 47; Z_to_bv 8 47].
Definition LIT_apos : list byte := [Z_to_bv 8 38; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 111; Z_to_bv 8 115; Z_to_bv 8 59].
Definition LIT_quot : list byte := [Z_to_bv 8 38; Z_to_bv 8 113; Z_to_bv 8 117; Z_to_bv 8 111; Z_to_bv 8 116; Z_to_bv 8 59].
Definition LIT_lt : list byte := [Z_to_bv 8 38; Z_to_bv 8 108; Z_to_bv 8 116; Z_to_bv 8 59].
Definition LIT_gt : list byte := [Z_to_bv 8 38; Z_to_bv 8 103; Z_to_bv 8 116; Z_to_bv 8 59].
Definition LIT_amp : list byte := [Z_to_bv 8 38; Z_to_bv 8 97; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 59].
Local Ltac lit_at A := intros m MI; apply (ro_bytes_at rsegs m); [exact MI| unfold A; lia| cbn; unfold A; lia| apply ro_bytes_b_sound; vm_compute; reflexivity].
Lemma lit_http_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_http LIT_http. Proof. lit_at A_http. Qed.
Lemma lit_https_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_https LIT_https. Proof. lit_at A_https. Qed.
Lemma lit_apos_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_apos LIT_apos. Proof. lit_at A_apos. Qed.
Lemma lit_quot_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_quot LIT_quot. Proof. lit_at A_quot. Qed.
Lemma lit_lt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_lt LIT_lt. Proof. lit_at A_lt. Qed.
Lemma lit_gt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_gt LIT_gt. Proof. lit_at A_gt. Qed.
Lemma lit_amp_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_amp LIT_amp. Proof. lit_at A_amp. Qed.

(* [comment removed for export] *)
Section FmtRange.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma fmt_c_range : forall v, cenv v -> range_ok v A_fmtc 3.
  Proof. intros v CE. eapply (global_range_ok v A_fmtc 3 32); [exact CE| gdesc_in| unfold A_fmtc; lia| unfold A_fmtc; lia| lia| unfold pa_static, A_fmtc; cbn; lia| unfold pa_static, A_fmtc; cbn; lia]. Qed.
  Lemma fmt_pfx_range : forall v, cenv v -> range_ok v A_fmtpfx 6.
  Proof. intros v CE. eapply (global_range_ok v A_fmtpfx 6 32); [exact CE| gdesc_in| unfold A_fmtpfx; lia| unfold A_fmtpfx; lia| lia| unfold pa_static, A_fmtpfx; cbn; lia| unfold pa_static, A_fmtpfx; cbn; lia]. Qed.
  Lemma fmt_host_range : forall v, cenv v -> range_ok v A_fmthost 13.
  Proof. intros v CE. eapply (global_range_ok v A_fmthost 13 32); [exact CE| gdesc_in| unfold A_fmthost; lia| unfold A_fmthost; lia| lia| unfold pa_static, A_fmthost; cbn; lia| unfold pa_static, A_fmthost; cbn; lia]. Qed.
End FmtRange.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac astopk AINV MU WM CF :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    apply (astop_lemma (L:=L) A m md _ _ _ _ _ _ _ _ AINV MU WM CF);
    let m1 := fresh "mq" in let md1 := fresh "mdq" in
    let A1 := fresh "AINVq" in let EV := fresh "EVq" in let SB := fresh "SBq" in let HID := fresh "HIDq" in
    intros m1 md1 A1 EV SB HID; clear HID
  end.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.   (* [comment removed for export] *)
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.
  (* [comment removed for export] *)
  Let W : list (Z * Z) := [(bv_unsigned sp - DOINCL_STACK, bv_unsigned sp); (h_ff H + 1336, h_ff H + 1352); (VEP, VEP + 312)].
  (* [comment removed for export] *)
  Definition FRAME (scratch : list cell) : list cell :=
    scratch ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 T md0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp ra N SB lo vi vr q tag vv"] Lemma CFP : client_fp LPA A0 (aview A0 m0) W.
  Proof.
    touch_all. prelims. pose proof VOBJ as (VLV & _). pose proof (proj1 HENV) as [ageh HFRh]. cbn.
    split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))))) with (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) by lia; exact WMAP00|].
    split; [right; right; left; exists (h_ff H), HCLASS, ageh; split; [exact HFRh|]; change (fsize HCLASS) with 8192; lia|].
    split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 T A0 md0 m0 fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 tp gp ra N SB lo vi q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - DOINCL_STACK <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40) \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    touch_all. prelims. pose proof VOBJ as (VLV & _). (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_1; dand4 dR_1 as _ _ VEPlo _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & _ & VEPlo & _) ]).
    unfold kHighMemBeg in VEPlo. all_app_facts.
    intros P a Ha NO. cbn [outside W] in NO. unfold h_vsc.
    assert (C3 : (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) <= a < bv_unsigned sp)
                 \/ (h_ff H + 32 + 1304 <= a < h_ff H + 32 + 1320) \/ (VEP <= a < VEP + 312)) by (try (generalize alloc_ceiling_val); clear - NO; try pose proof alloc_ceiling_val as ACV__; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; right; exact X | right; left; split; [try (generalize alloc_ceiling_val); clear -VEPlo; try pose proof alloc_ceiling_val as ACV__; lia| exact X]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition tinv (yi : vsb_rec) (bs : list byte) (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z) : Prop :=
    vi = Some yi /\
    ainv Ak mk mdk /\ mem_inv rsegs (aview Ak mk) /\ amd_frame md0 mdk /\ stk rsegs (aview Ak mk) lo (bv_unsigned sp + -160) /\
    henv_ok LPA VIA H Ak (aview Ak mk) /\
    rw_cells rsegs (aview Ak mk) VEP (vep_cells vv tag q) /\
    vsb_obj LPA Ak (aview Ak mk) (vv Fvsb) vvk false /\ VEP <> vb_buf vvk /\
    vb_len vr <= vb_len vvk <= vb_len vr + e /\
    vb_size vr <= vb_size vvk <= Z.max (vb_size vr) (vb_len vvk + 4096) /\
    (vb_buf vvk = vb_buf vr \/ (a_live A0 (vb_buf vvk) = None /\ a_live Ak (vb_buf vr) = None)) /\
    (forall r, r <> vb_buf vr -> r <> vb_buf vvk -> a_live Ak r = a_live A0 r) /\
    a_livebytes Ak = a_livebytes A0 + vb_size vvk - vb_size vr /\ a_tinycred Ak = a_tinycred A0 /\ a_nlive Ak = a_nlive A0 /\
    a_seccred A0 - (vsb_pot vvk - vsb_pot vr) <= a_seccred Ak <= a_seccred A0 /\
    a_primcred A0 - (vsb_ppot vvk - vsb_ppot vr) <= a_primcred Ak <= a_primcred A0 /\   (* [comment removed for export] *)
    frames_same A0 Ak /\
    stack_shadow LPA (aview Ak mk) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64) /\
    cframe LPA (owned A0) (owned Ak) (bv_unsigned sp) DOINCL_STACK
           (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                     \/ vsb_blocks (vv Finclude_src) yi a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
           (newblk (vb_buf vvk) (vb_size vvk)) (aview A0 m0) (aview Ak mk) /\
    vsb_obj LPA Ak (aview Ak mk) (vv Finclude_src) yi true /\ u8arr rsegs (aview Ak mk) (vb_buf yi) bs /\ Z.of_nat (length bs) = vb_size yi /\
    vv Finclude_src <> vb_buf vvk /\ vb_buf yi <> vb_buf vvk.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Local Ltac yi_facts EVI :=
    lazymatch goal with VLV : a_live A0 VEP = Some 312, LS : a_live A0 (vv Fvsb) = Some 40, LB : a_live A0 (vb_buf vr) = Some (vb_size vr) |- _ =>
    let HV := fresh "HV" in pose proof HVI as HV; rewrite EVI in HV;
    destruct HV as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB);
    pose proof (vsb_obj_geom LPA A0 m0 md0 (vv Finclude_src) _ true AINV00 IOBJ) as (SI16 & SIlo & SIhi & SIimg & BI16 & BIlo & BIhi & BIimg & DSBI & SImap & BImap);
    pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI; pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI;
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 (vv Finclude_src) 40 AINV00 VLV LSI (not_eq_sym NIS)) as DVSI;
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 _ _ AINV00 VLV LBI (not_eq_sym NIB)) as DVBI;
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LS LSI (not_eq_sym NISS)) as DSSI;
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LS LBI (not_eq_sym NIBS)) as DSBI2;
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LB LSI (not_eq_sym NISB)) as DBSI;
    pose proof (as_live_disjoint LPA A0 m0 md0 _ _ _ _ AINV00 LB LBI (not_eq_sym NIBB)) as DBBI;
    unfold kHighMemBeg in SIlo, BIlo
    end.

  (* [comment removed for export] *)
  Local Ltac geom :=
    pose proof VOBJ as (VLV & VEPC0 & TAG8 & PADS); fold_cl_segs;
    pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _);
    pose proof (vsb_obj_geom LPA A0 m0 md0 S vr false AINV00 SOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap);
    pose proof (proj1 (proj2 (proj2 SOBJ))) as LS; pose proof (proj1 (proj2 (proj2 (proj2 SOBJ)))) as LB;
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 S 40 AINV00 VLV LS NES) as DVS;
    pose proof (as_live_disjoint LPA A0 m0 md0 VEP 312 (vb_buf vr) (vb_size vr) AINV00 VLV LB NEB) as DVB;
    unfold kHighMemBeg in VEPlo, Slo, Blo; all_app_facts;
    pose proof (proj1 HENV) as [ageh HFRh]; pose proof (proj1 VBASE) as EVC.

  Local Ltac keepmlia_tac := idtac.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00 T fc F tp gp"] Lemma tinv_xfer : forall yi bs Ak mk mdk vvk e Wf (v' : mem) mq mdq sc,
    tinv yi bs Ak mk mdk vvk e ->
    munch Wf (aview Ak mk) v' -> wmono rsegs (aview Ak mk) v' -> mem_inv rsegs v' ->
    (forall a, ~ outside Wf a -> bv_unsigned sp - DOINCL_STACK <= a < bv_unsigned sp + -160) ->
    stk rsegs v' lo (bv_unsigned sp + -160) ->
    rw_cells rsegs v' (bv_unsigned sp + -160) (FRAME sc) -> cells_size sc = 56%nat ->
    ainv Ak mq mdq -> aview Ak mq = v' -> amd_frame mdk mdq ->
    tinv yi bs Ak mq mdq vvk e.
  Proof.
    touch_all. intros until sc. intros TI MU WM MI' WIN ST' FR' SC40 AINVq EV MDF'.
    unpack_tinv TI. prelims. geom. yi_facts EVI. unfold tinv. rewrite EV. cbv delta [FRAME] in FR'.
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    (first [ pose proof ((live_geomP LPA Ak mk mdk _ _ AINVk LVk)) as dR_3; dand5 dR_3 as _ _ _ VEPkhi _ | pose proof (live_geomP LPA Ak mk mdk _ _ AINVk LVk) as (_ & _ & _ & VEPkhi & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA Ak mk mdk S vvk false AINVk SOBJk)) as dR_4; dand8 dR_4 as _ _ Skhi _ _ _ Bkhi _ | pose proof (vsb_obj_geom LPA Ak mk mdk S vvk false AINVk SOBJk) as (_ & _ & Skhi & _ & _ & _ & Bkhi & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA Ak mk mdk (vv Finclude_src) yi true AINVk IOBJk)) as dR_5; dand8 dR_5 as _ _ SIkhi _ _ _ BIkhi _ | pose proof (vsb_obj_geom LPA Ak mk mdk (vv Finclude_src) yi true AINVk IOBJk) as (_ & _ & SIkhi & _ & _ & _ & BIkhi & _) ]).
    assert (OUT : forall a, (a < bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) \/ bv_unsigned sp + -160 <= a) -> outside Wf a).
    { intros a Ha. destruct (Classical_Prop.classic (outside Wf a)) as [X|X]; [exact X|]. exfalso. pose proof (WIN a X) as Y. ufs. try (generalize alloc_ceiling_val); clear - Ha Y; try pose proof alloc_ceiling_val as ACV__. lia. }
    split; [exact EVI|]. split; [exact AINVq|]. split; [exact MI'|]. split; [exact (amd_frame_trans _ _ _ MDFk MDF')|]. split; [exact ST'|].
    split. { eapply (henv_ok_munch LPA); [exact HENVk| exact MU| exact WM| exact HG|].
             intros a Ha. apply OUT. left. pose proof (proj1 (proj1 (proj2 HENVk))) as EB. cbn [vi_bss_vsc vi_bss_cp VIA] in Ha.
             unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha.
             pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF. rewrite SHMAX_val in SHF.
             change ((8192 + 7) / 8) with 1024 in SHF. change (8192 / 8) with 1024 in Ha.
             keeplia Ha GCE GHI SHF ACV CEIL LO. }
    split. { eapply (rw_cells_munch LPA); [exact VEPC| exact MU| exact WM|]. rewrite (vep_cells_size vv tag q TAG8 PADS). change (Z.of_nat 312) with 312.
             intros a Ha. apply OUT. left. keeplia Ha VEPkhi ACV CEIL LO. }
    split. { eapply vsb_obj_munch; [exact SOBJk| exact MU| exact WM|]. intros a Ha. apply OUT. left. keeplia Ha Skhi Bkhi ACV CEIL LO. }
    split; [exact NEBk|]. split; [exact LENk|]. split; [exact SZk|]. split; [exact RELk|]. split; [exact LIVEk|].
    split; [exact LBk|]. split; [exact TCk|]. split; [exact NLk|]. split; [exact SCk|]. split; [exact PCk|]. split; [exact FSk|].
    split. { (first [ pose proof (STKSHk) as dR_6; dand6 dR_6 as SSB SSN _ _ SSC SST | pose proof STKSHk as (SSB & SSN & _ & _ & SSC & SST) ]). unfold kHighMemBeg in SST. all_app_facts.
             eapply stack_shadow_again; [exact STKSHk| | reflexivity].
             eapply (bytes_at_munch LPA); [exact SSB| exact MU|]. rewrite ?zeros_length, ?repeat_length, Z2Nat.id by exact SSN.
             intros a Ha. apply OUT. left. keeplia Ha SST ACV CEIL LO. }
    split. { ufs. eapply cframe_after; [exact CFk| exact MU| intros a Ha NO; left; pose proof (WIN a NO) as Y; ufs; try (generalize alloc_ceiling_val); clear - Y; try pose proof alloc_ceiling_val as ACV__; lia|].
             eapply (window_mapped LPA _ lo (bv_unsigned sp + -160) (bv_unsigned sp));
               [exact ST' | exact FR' | rewrite cells_size_app, SC40; cbn [cells_size csize Nat.add]; clear; lia | exact CEIL | keeplia LO | clear; lia]. }
    split. { eapply vsb_obj_munch; [exact IOBJk| exact MU| exact WM|]. intros a Ha. apply OUT. left. keeplia Ha SIkhi BIkhi ACV CEIL LO. }
    split. { destruct U8k as [UB UW]. split; [| eapply wr_at_transport; [exact UW| exact WM]].
             eapply (bytes_at_munch LPA); [exact UB| exact MU|]. rewrite LBS. intros a Ha. apply OUT. left. keeplia Ha BIkhi ACV CEIL LO. }
    split; [exact LBS|]. split; [exact NISBk| exact NIBBk].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00"] Lemma printf_call : forall (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte)
      (HLA : Z.of_nat (cells_size FMT) = la) (HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z)
      (HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z)
      (P1 : pass1_stmt FMT la) (P2 : pass2_stmt FMT la nargs PRE OUT) (fbytes : list byte) (SLOTS : list word -> Prop)
      (PCM : AIcptdg.pcm_stmt fbytes SLOTS) (FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0])
      (yi : vsb_rec) (bs : list byte)
      (xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (Afmt HS : Z) (hs : list byte) (n : Z) (ret : Z) (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z) (sc : list cell),
    tinv yi bs Ak mk mdk vvk e ->
    rw_cells rsegs (aview Ak mk) (bv_unsigned sp + -160) (FRAME sc) -> cells_size sc = 56%nat ->
    (forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT) -> IMG_LO <= Afmt -> Afmt + la <= RO_TOP -> (forall v, cenv v -> range_ok v Afmt la) ->
    PRE [xa2; xa3; xa4; xa5; xa6; xa7] HS hs -> SLOTS [xa2; xa3; xa4; xa5; xa6; xa7] -> bytes_at rsegs (aview Ak mk) HS hs ->
    ((hs = [] /\ (HS = 0 \/ 0x10000 <= HS < 0x60a000)) \/ (vb_buf yi <= HS /\ HS + Z.of_nat (length hs) <= vb_buf yi + vb_size yi /\ In (Z_to_bv 8 0) hs)) ->
    Z.of_nat (length (OUT [xa2; xa3; xa4; xa5; xa6; xa7] hs)) = n ->
    0 <= e -> e + n <= vb_len yi + 8 ->
    0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (Ak' : AS) (mk' : mem) (mdk' : Model) (vvk' : vsb_rec),
        tinv yi bs Ak' mk' mdk' vvk' (e + n) ->
        rw_cells rsegs (aview Ak' mk') (bv_unsigned sp + -160) (FRAME sc) ->
        srealizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' xs0 xs1
                                        (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6')
                                   F (Z_to_bv 64 ret) fc None mk' (seg_rom rsegs)) mdk') T) ->
    srealizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp xt0 xt1 xt2 xs0 xs1
                                    (Z_to_bv 64 (vv Fvsb)) (Z_to_bv 64 Afmt) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 VSB_printf_entry) fc None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all. intros until sc. intros TI FR SC40 HF ARL ART AFR HPRE HSL HSB HOME HN E0 BUD RETR RET2 K'.
    unpack_tinv TI. prelims. geom. yi_facts EVI. cbv delta [FRAME] in FR.
    pose proof (as_minv LPA Ak _ _ AINVk) as [_ MHk].
    pose proof LENB as LENB'. rewrite EVI in LENB'. pose proof LBM as LBM'. rewrite EVI in LBM'. pose proof SCM as SCM'. rewrite EVI in SCM'.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LPA Ak mk mdk S vvk false AINVk SOBJk)) as dR_7; dand11 dR_7 as _ _ _ _ Bk16 Bklo Bkhi Bkimg DSBk _ Bkmap | pose proof (vsb_obj_geom LPA Ak mk mdk S vvk false AINVk SOBJk) as (_ & _ & _ & _ & Bk16 & Bklo & Bkhi & Bkimg & DSBk & _ & Bkmap) ]).
    pose proof (proj1 (proj2 (proj2 SOBJk))) as LSk. pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBFk.
    pose proof (proj1 (proj2 SOBJk)) as VINVk. (first [ pose proof (VINVk) as dR_8; dand3 dR_8 as Vszk Vlenk _ | pose proof VINVk as (Vszk & Vlenk & _) ]).
    pose proof (proj1 (proj2 SOBJ)) as VINV0. (first [ pose proof (VINV0) as dR_9; dand3 dR_9 as Vsz0 Vlen0 _ | pose proof VINV0 as (Vsz0 & Vlen0 & _) ]).
    pose proof (proj1 (proj2 IOBJ)) as VINVI. (first [ pose proof (VINVI) as dR_10; dand3 dR_10 as VszI VlenI _ | pose proof VINVI as (VszI & VlenI & _) ]).
    pose proof (proj1 (proj2 (proj2 IOBJk))) as LSIk. pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBIk.
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    (first [ pose proof ((live_geomP LPA Ak mk mdk _ _ AINVk LSIk)) as dR_11; dand5 dR_11 as _ _ SIklo SIkhi _ | pose proof (live_geomP LPA Ak mk mdk _ _ AINVk LSIk) as (_ & _ & SIklo & SIkhi & _) ]).
    (first [ pose proof ((live_geomP LPA Ak mk mdk _ _ AINVk LBIk)) as dR_12; dand5 dR_12 as _ _ BIklo BIkhi _ | pose proof (live_geomP LPA Ak mk mdk _ _ AINVk LBIk) as (_ & _ & BIklo & BIkhi & _) ]).
    unfold kHighMemBeg in Bklo, SIklo, BIklo. all_app_facts.
    pose proof (HOUT _ _ _ HPRE) as HNB. rewrite HN in HNB.
    pose proof (Zle_0_nat (length (OUT [xa2; xa3; xa4; xa5; xa6; xa7] hs))) as HN0. rewrite HN in HN0.
    assert (HSH' : str_home Ak S vvk HS hs).
    { destruct HOME as [L|(R1 & R2 & R3)]; [left; exact L| right].
      exists (vb_buf yi), (vb_size yi). split; [exact LBIk|]. split; [exact R1|]. split; [exact R2|].
      split; [exact NIBS|]. split; [exact NIBBk| exact R3]. }
    pose proof (vsb_extendsize_tight (vb_size vvk + n + 1)) as XT.
    pose proof (vsb_pot_diff vr vvk ltac:(keeplia SZk)) as PD.
    hide DSB. hide DSBI. hide DSBk. hide RELk. hide HOME.
    eapply (VSB_printf_ok FMT la nargs PRE OUT HLA HOUT HOUT1 P1 P2 fbytes SLOTS PCM FBY vsnreal_holds
              (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
              xa2 xa3 xa4 xa5 xa6 xa7 F fc mk mdk Ak S vvk Afmt HS hs lo SB N T);
      [ exact AINVk | exact SOBJk | exact HF | exact ARL | exact ART | exact AFR | exact HPRE | exact HSL | exact HSB | exact HSH'
      | unfold EXT_MAX; rewrite HN; keeplia LENk SZk LENB' SZB E0 BUD Vszk Vlenk Vsz0 Vlen0 VlenI HN0
      | rewrite HN; keeplia XT LBk LENk SZk LBM' SZB E0 BUD Vsz0 Vlen0 Vszk Vlenk VlenI HN0
      | rewrite NLk; exact NLV
      | clear - PD SCk SCM' SZk LENk Vlen0 Vsz0 Vlenk E0 BUD HN0 VlenI; try pose proof alloc_ceiling_val as ACV__; unhide_all; mlia
      | pose proof (vsb_ppot_range vvk) as PPR; unfold PPOT_CAP in *; keeplia PCk PRM PPR (* [comment removed for export] *)
      | apply lib_frames_young; exact (frames_same_lib A0 Ak FSk LF)
      | exact TP
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); clear - SP16 SPR LO CEIL ACV; try pose proof alloc_ceiling_val as ACV__; mlia
      | exact CEIL
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; keeplia LO
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); keeplia SPHI
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; eapply (stack_shadow_sub LPA _ SB N); [exact STKSHk| clear; lia| clear; lia| keeplia CEIL LO ACV]
      | (* [comment removed for export] *)
      | exact MIk | reflexivity | reflexivity
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); exact STk ].
    cbv zeta. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r Ak' mk' mdk' vv'.
    intros AINV' MI' MDF' SOBJ' KE KO LEN' SZ' LIVE' REL' AG' LB' TC' NL' SC' PC' ST' HSB' STKSH' CF'.
    rewrite unsigned_lit in ST', STKSH', CF' by (keeplia SPR LO CEIL ACV). ufs.
    rewrite HN in LEN'.
    rewrite (ret_pc_even ret RETR RET2).
    pose proof (as_minv LPA Ak' _ _ AINV') as [_ MH'].
    (first [ pose proof ((vsb_obj_geom LPA Ak' mk' mdk' S vv' false AINV' SOBJ')) as dR_13; dand11 dR_13 as _ _ _ _ B'16 B'lo B'hi _ DSB' _ _ | pose proof (vsb_obj_geom LPA Ak' mk' mdk' S vv' false AINV' SOBJ') as (_ & _ & _ & _ & B'16 & B'lo & B'hi & _ & DSB' & _ & _) ]). unfold kHighMemBeg in B'lo. all_app_facts.
    (* [comment removed for export] *)
    assert (FRESH : forall r0 k0, a_live Ak r0 = Some k0 -> r0 <> vb_buf vvk -> r0 <> vb_buf vv').
    { intros r0 k0 L0 N0 E0'. destruct REL' as [R|[R _]]; [exact (N0 (eq_trans E0' R))|]. rewrite <- E0' in R. rewrite R in L0. discriminate L0. }
    pose proof (FRESH VEP 312 LVk NEBk) as NEB'.
    pose proof (FRESH _ _ LSIk NISBk) as NISB'.
    pose proof (FRESH _ _ LBIk NIBBk) as NIBB'.
    assert (LSI' : a_live Ak' (vv Finclude_src) = Some 40) by (rewrite (LIVE' _ NISBk NISB'); exact LSIk).
    assert (LBI' : a_live Ak' (vb_buf yi) = Some (vb_size yi)) by (rewrite (LIVE' _ NIBBk NIBB'); exact LBIk).
    (* [comment removed for export] *)
    assert (HENV' : henv_ok LPA VIA H Ak' (aview Ak' mk')).
    { eapply (henv_ok_acall_gen H Ak Ak'); [exact AINVk| exact CF'| exact HENVk| keeplia CEIL LO
        | intros ff k age HFf; (first [ pose proof ((proj1 AG' ff k age HFf)) as dR_14; dex1 dR_14 as d; destruct dR_14 as [Ed _] | pose proof ((proj1 AG' ff k age HFf)) as dR_14; dand3 dR_14 as d Ed _ | destruct (proj1 AG' ff k age HFf) as (d & Ed & _) ]); exists (age + d)%nat; exact Ed|].
      intros a [X|X].
      - exists (vb_buf vvk), (vb_size vvk). split; [exact LBFk|]. unfold newblk, blk in X. keeplia X.
      - exists S, 40. split; [exact LSk|]. left. keeplia X. }
    (* [comment removed for export] *)
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia Slo) ltac:(clear; lia) ltac:(exact Shi)) as SHSB. rewrite SHMAX_val in SHSB. change ((40 + 7) / 8) with 5 in SHSB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vvk) (vb_size vvk) ltac:(keeplia Bklo) ltac:(keeplia Vszk) ltac:(exact Bkhi)) as SHBk. rewrite SHMAX_val in SHBk.
    pose proof (as_live_disjoint LPA Ak mk mdk VEP 312 _ _ AINVk LVk LBFk NEBk) as DVBk.
    pose proof (as_live_disjoint LPA Ak mk mdk VEP 312 S 40 AINVk LVk LSk NES) as DVSk.
    pose proof (as_live_disjoint LPA Ak mk mdk _ _ _ _ AINVk LSIk LBFk NISBk) as DSIBk.
    pose proof (as_live_disjoint LPA Ak mk mdk _ _ _ _ AINVk LBIk LBFk NIBBk) as DBIBk.
    pose proof (as_live_disjoint LPA Ak mk mdk _ _ _ _ AINVk LSIk LSk NISS) as DSIS.
    pose proof (as_live_disjoint LPA Ak mk mdk _ _ _ _ AINVk LBIk LSk NIBS) as DBIS.
    pose proof (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA)) as MPF.
    replace (Z.of_nat (cells_size (sc ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]))) with 160 in MPF
      by (rewrite cells_size_app, SC40; reflexivity).
    pose proof (crange_stack (Clg:=Clg) (L:=LPA) Ak _ _ (aview Ak mk) (bv_unsigned sp + -160) 160 AINVk ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR) MPF) as CRF. clear MPF.
    lazymatch type of CF' with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA Ak Ak' xsp win V Nn ma mb CF' VEP) in VEPC;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) Ak _ _ VEP 312 VEP 312 AINVk LVk ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))
         | rewrite (vep_cells_size vv tag q TAG8 PADS); change (Z.of_nat 312) with 312; split;
           [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVBk DVSk SHSB SHBk VEPlo] ];
      lazymatch type of FR with rw_cells _ _ _ ?fcs =>
        apply (rw_cells_ccall LPA Ak Ak' xsp win V Nn ma mb CF' (bv_unsigned sp + -160) fcs) in FR;
        [| replace (Z.of_nat (cells_size fcs)) with 160 by (rewrite cells_size_app, SC40; reflexivity); exact CRF
         | rewrite cells_size_app, SC40; cbn [cells_size csize Nat.add length app]; split;
           [keeplia SPR| intros i Hi X; unfold newblk, blk in X; keeplia Hi X Shi Bkhi SHSB SHBk ACV CEIL LO SPR] ] end;
      assert (IOBJ' : vsb_obj LPA Ak' mb (vv Finclude_src) yi true);
      [ eapply (vsb_obj_ccall Ak Ak'); [exact AINVk| exact CF'| exact IOBJk| keeplia CEIL LO| exact LSI'| exact LBI'|];
        intros a Ha X; unfold newblk, blk in X; keeplia Ha X DSIBk DBIBk DSIS DBIS SHSB SHBk SIklo BIklo
      | ];
      apply (u8arr_ccall LPA Ak Ak' xsp win V Nn ma mb CF' (vb_buf yi)) in U8k;
        [| rewrite LBS; exact (crange_block (Clg:=Clg) (L:=LPA) Ak _ _ (vb_buf yi) (vb_size yi) (vb_buf yi) (vb_size yi) AINVk LBIk ltac:(clear; lia) ltac:(clear; lia) ltac:(keeplia VszI))
         | rewrite LBS; split; [keeplia BIkhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DBIBk DBIS SHSB SHBk BIklo] ]
    end.
    clear CRF.
    assert (MAP' : mapped (aview Ak' mk') (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192))))) (160 + (128 + 16 + (192 + 16 + (80 + 8192))))).
    { eapply (window_mapped LPA _ lo (bv_unsigned sp + -160) (bv_unsigned sp));
        [exact ST' | exact FR | rewrite cells_size_app, SC40; cbn [cells_size csize Nat.add]; clear; lia | exact CEIL | keeplia LO | clear; lia]. }
    eapply K'; [| exact FR].
    unhide RELk.
    split; [exact EVI|]. split; [exact AINV'|]. split; [exact MI'|]. split; [exact (amd_frame_trans _ _ _ MDFk MDF')|].
    split; [exact ST'|]. split; [exact HENV'|]. split; [exact VEPC|].
    split; [exact SOBJ'|]. split; [exact NEB'|].
    split; [keeplia LENk LEN' HN0|].
    split; [keeplia LENk LEN' SZk SZ' HN0|].
    split.
    { (* [comment removed for export] *)
      destruct (Z.eq_dec (vb_buf vv') (vb_buf vr)) as [Eb|NE]; [left; exact Eb| right]. split.
      - destruct (Z.eq_dec (vb_buf vv') (vb_buf vvk)) as [E2|NE2].
        + rewrite E2. destruct RELk as [R|[R _]]; [exfalso; apply NE; rewrite E2; exact R| exact R].
        + destruct REL' as [R|[R _]]; [exfalso; exact (NE2 R)|]. rewrite <- (LIVEk _ NE NE2). exact R.
      - destruct (Z.eq_dec (vb_buf vr) (vb_buf vvk)) as [E3|NE3].
        + destruct REL' as [R|[_ R]]; [exfalso; apply NE; rewrite R, E3; reflexivity|]. rewrite E3. exact R.
        + rewrite (LIVE' _ NE3 (not_eq_sym NE)). destruct RELk as [R|[_ R]]; [exfalso; exact (NE3 (eq_sym R))| exact R]. }
    split.
    { intros r0 R1 R2. destruct (Z.eq_dec r0 (vb_buf vvk)) as [Eb|NE].
      - rewrite Eb. destruct REL' as [R|[_ R]]; [exfalso; apply R2; rewrite Eb, R; reflexivity|]. rewrite R.
        rewrite Eb in R1. destruct RELk as [R'|[R' _]]; [exfalso; exact (R1 R')| symmetry; exact R'].
      - rewrite (LIVE' r0 NE R2). exact (LIVEk r0 R1 NE). }
    split; [rewrite LB', LBk; clear; lia|]. split; [rewrite TC', TCk; reflexivity|]. split; [rewrite NL', NLk; reflexivity|].
    split; [keeplia SCk SC'|]. split; [keeplia PCk PC'|].   (* [comment removed for export] *)
    split; [intros ff; rewrite (lib_frames_same Ak Ak' 1%nat 1%nat (frames_same_lib A0 Ak FSk LF) AG' ff); apply FSk|].
    split; [exact (stack_shadow_again _ _ SB N _ _ _ STKSHk (proj1 STKSH') eq_refl)|].
    split.
    { eapply (cframe_seq LPA _ _ _ (bv_unsigned sp) (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) (160 + (128 + 16 + (192 + 16 + (80 + 8192))))
                (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) _ _ _ _ _ _ (aview A0 m0) (aview Ak mk) (aview Ak' mk'));
        [ exact CFk
        | eapply (cframe_reframe LPA _ _ _ _ (bv_unsigned sp) (160 + (128 + 16 + (192 + 16 + (80 + 8192))))); [exact CF' | clear; lia | clear; lia | exact MAP']
        | clear; lia | clear; lia | exact MAP' | intros a X; exact X
        | intros a [X|X]; [left; exact X | right; right; right; left; exact X]
        | intros a X; right; left; exact X ]. }
    split; [exact IOBJ'|]. split; [exact U8k|]. split; [exact LBS|]. split; [exact NISB'| exact NIBB'].
  Qed.

  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00"] Lemma printf_c_call : forall (yi : vsb_rec) (bs : list byte)
      (xt0 xt1 xt2 xs0 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
      (ch : word) (ret : Z) (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z) (sc : list cell),
    tinv yi bs Ak mk mdk vvk e ->
    rw_cells rsegs (aview Ak mk) (bv_unsigned sp + -160) (FRAME sc) -> cells_size sc = 56%nat ->
    0 <= e -> e + 1 <= vb_len yi + 8 ->
    0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (Ak' : AS) (mk' : mem) (mdk' : Model) (vvk' : vsb_rec),
        tinv yi bs Ak' mk' mdk' vvk' (e + 1) ->
        rw_cells rsegs (aview Ak' mk') (bv_unsigned sp + -160) (FRAME sc) ->
        srealizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' xs0 xs1
                                        (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3' t4' t5' t6')
                                   F (Z_to_bv 64 ret) fc None mk' (seg_rom rsegs)) mdk') T) ->
    srealizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp xt0 xt1 xt2 xs0 xs1
                                    (Z_to_bv 64 (vv Fvsb)) (Z_to_bv 64 A_fmtc) ch xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 VSB_printf_entry) fc None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all. intros until sc. intros TI FR SC40 E0 BUD RETR RET2 K'.
    eapply (printf_call FMT_C 3 1 PRE_C OUT_C eq_refl HOUT_C HOUT1_C OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_pc1_c.pc1_c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.RA_vrdi.RA_p0nl.pc2_c FMTB_C SLOTS_C pcm_fmt_c FBY_C yi bs
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A_fmtc 0 [] 1 ret Ak mk mdk vvk e sc);
      [ exact TI | exact FR | exact SC40 | apply fmt_c_at | unfold IMG_LO, A_fmtc; clear; lia | unfold RO_TOP, A_fmtc; clear; lia | apply fmt_c_range
      | exists ch; reflexivity | exact I | apply bytes_at_nil; clear; lia | left; split; [reflexivity| clear; lia]
      | reflexivity | exact E0 | exact BUD | exact RETR | exact RET2 | exact K' ].
  Qed.
End S.
End A_veq11.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSa8f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VStbd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VEr47 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_VSbb4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS41f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSqtv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS160 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSe90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSq5u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VSt8w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_VS8zm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_veqih OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_ve5c7.A_veq11.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis VOBJ : vep_obj LPA A0 (aview A0 m0) VEP vv tag q.
  Hypothesis VBASE : vep_base H VEP vv.
  Hypothesis HENV : henv_ok LPA VIA H A0 (aview A0 m0).
  Hypothesis HFL : 0 <= vv Fflags < 16.
  Hypothesis HET : bool01 (vv Femptytag).
  Hypothesis HIC : bool01 (vv Finclude_continue).
  Hypothesis HLM : vv Flast_mark = 1.
  Hypothesis HAZ : vv Fattr_vsb = 0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) (vv Fvsb) vr false.
  Hypothesis NES : VEP <> vv Fvsb.
  Hypothesis NEB : VEP <> vb_buf vr.
  Hypothesis SZB : vb_size vr <= vb_len vr + 4096.
  Hypothesis LENB : vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29.
  Hypothesis LBM : a_livebytes A0 + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis LF : lib_frames A0.
  Hypothesis HVI : match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A0 (aview A0 m0) (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis WMAP00 : mapped (aview A0 m0) (bv_unsigned sp - DOINCL_STACK) DOINCL_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K :
    forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vep) (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
      vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
      (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
      vsb_obj LPA A' v' (vv Fvsb) vr' false ->
      vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      match vi with
      | None => (forall r, a_live A' r = a_live A0 r) /\ a_livebytes A' = a_livebytes A0 /\ a_nlive A' = a_nlive A0
      | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                   (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A0 r) /\
                   a_livebytes A' = a_livebytes A0 + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A0 - 2
      end ->
      frames_aged A0 A' 1 1 -> a_tinycred A' = a_tinycred A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) DOINCL_STACK
             (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                       \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                       \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
             (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.
  Let S := vv Fvsb.

  Local Ltac touch_all :=
    pose proof (conj AINV00 (conj VOBJ (conj VBASE (conj HENV (conj HFL (conj HET (conj HIC (conj HLM (conj HAZ (conj SOBJ (conj NES (conj NEB
      (conj SZB (conj LENB (conj LBM (conj NLV (conj SCM (conj PRM (conj LF (conj HVI (conj TP (conj SP16 (conj WMAP00 (conj CEIL (conj LO (conj SPHI
      (conj STKSH K))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A0 m0 md0 H AINV00 (proj1 HENV)) as HG;
    pose proof HG as (G16 & GCE & GHI); unfold HFSIZE in GHI;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    assert (ES : S = vv Fvsb) by reflexivity;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Let TINV := tinv VEP vv tag q vr vi H lo SB N sp m0 md0 A0.
  Let FRAME' := FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Local Ltac pose_parts :=
    pose proof (printf_c_call VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as printf_c_call';
    pose proof (tinv_xfer VEP vv tag q vr vi H lo SB N ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 A0 T
                  AINV00 VOBJ VBASE HENV HFL HET HIC HLM HAZ SOBJ NES NEB SZB LENB LBM NLV SCM PRM LF HVI TP SP16 WMAP00 CEIL LO SPHI STKSH K) as tinv_xfer'.

  Local Ltac unpack_tinv TI :=
    (first [ dand26 TI as EVI AINVk MIk MDFk STk HENVk VEPC SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk | destruct TI as (EVI & AINVk & MIk & MDFk & STk & HENVk & VEPC & SOBJk & NEBk & LENk & SZk & RELk & LIVEk & LBk & TCk & NLk & SCk & PCk & FSk & STKSHk
                    & CFk & IOBJk & U8k & LBS & NISBk & NIBBk) ]).

  (* [comment removed for export] *)
  Definition SCR5 : list cell :=
    [C8 (Z_to_bv 64 ((VEP + 288) / 8 + 2147450880)); C8 (Z_to_bv 64 (VEP + 288)); C8 (Z_to_bv 64 (VEP + 280)); C8 (Z_to_bv 64 A_gt); C8 (Z_to_bv 64 A_amp);
     C8 (Z_to_bv 64 A_quot); C8 (Z_to_bv 64 A_lt)].   (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="AI16 S K STKSH SPHI LO CEIL WMAP00 SP16 TP HVI LF SCM PRM NLV LBM LENB SZB NEB NES SOBJ HAZ HLM HIC HET HFL HENV VBASE VOBJ AINV00"] Lemma seg_end : forall (yi : vsb_rec) (bs : list byte)
      (xra xt0 xt1 xt2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word)
      (Ak : AS) (mk : mem) (mdk : Model) (vvk : vsb_rec) (e : Z),
    TINV yi bs Ak mk mdk vvk e ->
    rw_cells rsegs (aview Ak mk) (bv_unsigned sp + -160) (FRAME' SCR5) ->
    0 <= e -> e + 1 <= vb_len yi + 8 ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp xt0 xt1 xt2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                                    (Z_to_bv 64 (VEP + 8)) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 (Z_to_bv 64 ((VEP + 8) / 8 + 2147450880)) xt3 xt4 xt5 xt6)
                               F (Z_to_bv 64 0x8f07c) fc None mk (seg_rom rsegs)) mdk) T.
  Proof.
    touch_all. intros until e. intros TI FR E0 BUD. pose_parts.
    pose proof TI as TI0. unpack_tinv TI. prelims.
    pose proof VOBJ as (VLV & _ & TAG8 & PADS). fold_cl_segs.
    (first [ pose proof ((live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV)) as dR_2; dand7 dR_2 as _ VEP16 VEPlo VEPhi _ _ _ | pose proof (live_geomP LPA A0 m0 md0 VEP _ AINV00 VLV) as (_ & VEP16 & VEPlo & VEPhi & _ & _ & _) ]). unfold kHighMemBeg in VEPlo. all_app_facts.
    pose proof (mod8_of_mod16 VEP VEP16) as V8.
    pose proof HVI as HVI'. rewrite EVI in HVI'. (first [ dand9 HVI' as INZ IOBJ IERR NIS NIB NISS NISB NIBS NIBB | destruct HVI' as (INZ & IOBJ & IERR & NIS & NIB & NISS & NISB & NIBS & NIBB) ]).
    pose proof (as_minv LPA Ak _ _ AINVk) as [_ MHk].
    assert (LVk : a_live Ak VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    (* [comment removed for export] *)
    pose proof (conj (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) (sh_top_le' VEP 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi))) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVk LVk) as SHV. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV. remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    pose proof VEPC as VEPCf. unfold vep_cells in VEPC. cbv delta [FRAME' FRAME SCR5] in FR. cbn [app] in FR.
    hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview Ak mk)) as MU. pose proof (wmono_refl rsegs (aview Ak mk)) as WM.
    ago AINVk. fold_cl_segs.
    (* [comment removed for export] *)
    vrechk SHV EzsV (VEP + 8) 8 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    astopk AINVk MU WM I.
    pose proof (tinv_xfer' yi bs Ak mk mdk vvk e [] _ mq mdq SCR5 TI0 MU WM MIk ltac:(intros a X; exfalso; exact (X I)) STk FR eq_refl AINVq EVq (amd_frame_sbm _ _ SBq MHk)) as TIq.
    rewrite <- EVq in FR.
    clear TI0 MU WM SHV.
    eapply (printf_c_call' yi bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) 0x8f098 Ak mq mdq vvk e SCR5);
      [ exact TIq | cbv delta [FRAME SCR5]; cbn [app]; exact FR | reflexivity | exact E0 | exact BUD | clear; lia | reflexivity | ].
    clear TIq FR. clear dependent mq. try clear SBq. try (clear dependent mdq).
    clear EVI AINVk MIk MDFk STk HENVk VEPC VEPCf SOBJk NEBk LENk SZk RELk LIVEk LBk TCk NLk SCk PCk FSk STKSHk CFk IOBJk U8k LBS NISBk NIBBk MHk LVk.
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A1 m1 md1 vv1 TI1 FR1.
    unpack_tinv TI1. cbv delta [FRAME SCR5] in FR1. cbn [app] in FR1.
    pose proof (as_minv LPA A1 _ _ AINVk) as [_ MH1].
    assert (LV1 : a_live A1 VEP = Some 312) by (rewrite (LIVEk VEP NEB NEBk); exact VLV).
    pose proof (proj1 (proj2 (proj2 SOBJk))) as LS1. pose proof (proj1 (proj2 (proj2 (proj2 SOBJk)))) as LBF1.
    pose proof (proj1 (proj2 (proj2 IOBJk))) as LSI1. pose proof (proj1 (proj2 (proj2 (proj2 IOBJk)))) as LBI1.
    (first [ pose proof ((vsb_obj_geom LPA A1 m1 md1 S vv1 false AINVk SOBJk)) as dR_4; dand11 dR_4 as _ S1lo S1hi _ _ B1lo B1hi _ DSB1 _ _ | pose proof (vsb_obj_geom LPA A1 m1 md1 S vv1 false AINVk SOBJk) as (_ & S1lo & S1hi & _ & _ & B1lo & B1hi & _ & DSB1 & _ & _) ]).
    (first [ pose proof ((vsb_obj_geom LPA A1 m1 md1 (vv Finclude_src) yi true AINVk IOBJk)) as dR_5; dand11 dR_5 as _ SI1lo SI1hi _ _ BI1lo BI1hi _ _ _ _ | pose proof (vsb_obj_geom LPA A1 m1 md1 (vv Finclude_src) yi true AINVk IOBJk) as (_ & SI1lo & SI1hi & _ & _ & BI1lo & BI1hi & _ & _ & _ & _) ]).
    unfold kHighMemBeg in S1lo, B1lo, SI1lo, BI1lo. all_app_facts.
    pose proof (proj1 (proj2 SOBJk)) as VINV1. pose proof VINV1 as (Vsz1 & _).
    pose proof (proj1 (proj2 IOBJ)) as VINVI. pose proof VINVI as (VszI & _).
    pose proof (conj (sh_boundL (Clg:=Clg) S 40 ltac:(keeplia S1lo) ltac:(clear; lia) ltac:(exact S1hi)) (sh_top_le' S 40 ltac:(keeplia S1lo) ltac:(clear; lia) ltac:(exact S1hi))) as SHS1. rewrite SHMAX_val in SHS1.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf vv1) (vb_size vv1) ltac:(keeplia B1lo) ltac:(keeplia Vsz1) ltac:(exact B1hi)) (sh_top_le' (vb_buf vv1) (vb_size vv1) ltac:(keeplia B1lo) ltac:(keeplia Vsz1) ltac:(exact B1hi))) as SHB1. rewrite SHMAX_val in SHB1.
    pose proof (conj (sh_boundL (Clg:=Clg) (vv Finclude_src) 40 ltac:(keeplia SI1lo) ltac:(clear; lia) ltac:(exact SI1hi)) (sh_top_le' (vv Finclude_src) 40 ltac:(keeplia SI1lo) ltac:(clear; lia) ltac:(exact SI1hi))) as SHSI1. rewrite SHMAX_val in SHSI1.
    pose proof (conj (sh_boundL (Clg:=Clg) (vb_buf yi) (vb_size yi) ltac:(keeplia BI1lo) ltac:(keeplia VszI) ltac:(exact BI1hi)) (sh_top_le' (vb_buf yi) (vb_size yi) ltac:(keeplia BI1lo) ltac:(keeplia VszI) ltac:(exact BI1hi))) as SHBI1. rewrite SHMAX_val in SHBI1.
    unhide_neqs.
    pose proof (as_live_disjoint LPA A1 m1 md1 VEP 312 _ _ AINVk LV1 LSI1 (not_eq_sym NIS)) as DVSI.
    pose proof (as_live_disjoint LPA A1 m1 md1 VEP 312 _ _ AINVk LV1 LBI1 (not_eq_sym NIB)) as DVBI.
    pose proof (as_live_disjoint LPA A1 m1 md1 VEP 312 _ _ AINVk LV1 LS1 NES) as DVS1.
    pose proof (as_live_disjoint LPA A1 m1 md1 VEP 312 _ _ AINVk LV1 LBF1 NEBk) as DVB1.
    pose proof (as_live_disjoint LPA A1 m1 md1 _ _ _ _ AINVk LS1 LSI1 (not_eq_sym NISS)) as DSSI.
    pose proof (as_live_disjoint LPA A1 m1 md1 _ _ _ _ AINVk LS1 LBI1 (not_eq_sym NIBS)) as DSBI.
    pose proof (as_live_disjoint LPA A1 m1 md1 _ _ _ _ AINVk LBF1 LSI1 (not_eq_sym NISBk)) as DBSI.
    pose proof (as_live_disjoint LPA A1 m1 md1 _ _ _ _ AINVk LBF1 LBI1 (not_eq_sym NIBBk)) as DBBI.
    hide_neqs. hide DSB1.
    (* [comment removed for export] *)
    unfold vep_cells in VEPC.
    (first [ pose proof ((rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (vv Finclude_src))) VEPC eq_refl)) as dR_6; dand3 dR_6 as VA VM VBk | pose proof (rw_cells_split3 rsegs _ VEP _ 45 (C8 (Z_to_bv 64 (vv Finclude_src))) VEPC eq_refl) as (VA & VM & VBk) ]). clear VEPC.
    cbn [firstn skipn cells_size csize Nat.add length fupd vf_beq vf_index N.eqb Pos.eqb] in VA, VM, VBk.
    change (Z.of_nat 280) with 280 in VM. change (Z.of_nat 280) with 280 in VBk. change (Z.of_nat 8) with 8 in VBk.
    replace (VEP + 280 + 8) with (VEP + 288) in VBk by lia.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A1 m1)) as MU2. pose proof (wmono_refl rsegs (aview A1 m1)) as WM2.
    hide DVSI. hide DVBI. hide DVS1. hide DVB1. hide DSSI. hide DSBI. hide DBSI. hide DBBI.
    ago AINVk. fold_cl_segs.
    zstep. zstep.
    astopk AINVk MU2 WM2 I. rewrite <- EVq in *. clear EVq.
    unhide_neqs.
    eapply (VSB_destroy_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ A1 (VEP + 280) (vv Finclude_src) yi true lo);
      [ exact AINVq | exact MIk | reflexivity | exact VM
      | eapply cobj_block; [exact LV1| cbn; intros [X|[X|X]]; [exact (NIS X)| exact (NIB X)| exact X] | lia | lia]
      | rewrite Z.add_mod, V8 by lia; reflexivity
      | keeplia VEPhi
      | exact IOBJk | exact TP
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); clear - SP16 SPR LO CEIL ACV; try pose proof alloc_ceiling_val as ACV__; mlia
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); exact STk | exact CEIL
      | rewrite unsigned_lit by (keeplia SPR LO CEIL ACV); ufs; keeplia LO | ].
    hide_neqs.
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A2 mc mdc. cbv zeta.
    intros AINV2 MI2 MDF2 FRS2 LB2 TC2 NL2 SC2 PC2 ST2 PSC DEADS DEADB LIVEq2 CF2.
    rewrite unsigned_lit in ST2, CF2 by (keeplia SPR LO CEIL ACV). ufs.
    replace (ret_pc (Z_to_bv 64 0x8f0a0)) with (Z_to_bv 64 0x8f0a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (as_minv LPA A2 _ _ AINV2) as [_ MH2].
    unhide_neqs.
    assert (LV2 : a_live A2 VEP = Some 312) by (rewrite (LIVEq2 VEP (not_eq_sym NIS) (not_eq_sym NIB)); exact LV1).
    assert (LS2 : a_live A2 S = Some 40) by (rewrite (LIVEq2 S (not_eq_sym NISS) (not_eq_sym NIBS)); exact LS1).
    assert (LBF2 : a_live A2 (vb_buf vv1) = Some (vb_size vv1)) by (rewrite (LIVEq2 _ (not_eq_sym NISBk) (not_eq_sym NIBBk)); exact LBF1).
    (* [comment removed for export] *)
    assert (HENV2 : henv_ok LPA VIA H A2 (aview A2 mc)).
    { eapply (henv_ok_acall_gen H A1 A2); [exact AINVq| exact CF2| exact HENVk| keeplia CEIL LO| intros ff k age HFf; exists age; rewrite (FRS2 ff); exact HFf|].
      intros a [X|[X|X]].
      - exists (vv Finclude_src), 40. split; [exact LSI1|]. unfold newblk, blk in X. keeplia X.
      - exists (vb_buf yi), (vb_size yi). split; [exact LBI1|]. unfold newblk, blk in X. keeplia X.
      - exists VEP, 312. split; [exact LV1|]. left. keeplia X. }
    (* [comment removed for export] *)
    unhide DVSI. unhide DVBI. unhide DVS1. unhide DVB1. unhide DSSI. unhide DSBI. unhide DBSI. unhide DBBI.
    pose proof (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR1 ltac:(off_image_solve LPA)) as MPF. cbn [cells_size csize Nat.add length] in MPF.
    lazymatch type of CF2 with cframe _ (owned _) (owned _) ?xsp ?win ?V ?Nn ?ma ?mb =>
      apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 VEP) in VA;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ VEP 312 VEP 280 AINVq LV1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))
         | cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add]; split;
           [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVSI DVBI SHSI1 SHBI1 VEPlo] ];
      apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 (VEP + 288)) in VBk;
        [| exact (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ VEP 312 (VEP + 288) 24 AINVq LV1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))
         | cbn [cells_size csize Nat.add length]; split;
           [keeplia VEPhi ACV CEIL LO| intros i Hi X; unfold newblk, blk in X; keeplia Hi X DVSI DVBI SHSI1 SHBI1 VEPlo] ];
      lazymatch type of FR1 with rw_cells _ _ _ ?fcs =>
        apply (rw_cells_ccall LPA A1 A2 xsp win V Nn ma mb CF2 (bv_unsigned sp + -160) fcs) in FR1;
        [| exact (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ ma (bv_unsigned sp + -160) 160 AINVq ltac:(keeplia ACV CEIL LO) ltac:(keeplia SPR) MPF)
         | cbn [Cells.cells_size Cells.csize Nat.add length app]; split; [keeplia SPR|];
           intros i Hi X; unfold newblk, blk in X; keeplia Hi X SI1hi BI1hi SHSI1 SHBI1 VEPhi ACV CEIL LO ] end;
      assert (SOBJ2 : vsb_obj LPA A2 mb S vv1 false);
      [ eapply (vsb_obj_ccall A1 A2); [exact AINVq| exact CF2| exact SOBJk| keeplia CEIL LO| exact LS2| exact LBF2|];
        intros a Ha X; unfold newblk, blk in X; keeplia Ha X DSSI DSBI DBSI DBBI DVS1 DVB1 SHSI1 SHBI1 S1lo B1lo VEPlo
      | ];
      assert (STKSH2 : stack_shadow LPA mb SB N (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) - 64) (bv_unsigned sp + 64));
      [ (first [ pose proof (STKSHk) as dR_7; dand6 dR_7 as SSB SSN _ _ SSC SST | pose proof STKSHk as (SSB & SSN & _ & _ & SSC & SST) ]); unfold kHighMemBeg in SST; all_app_facts;
        pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *);
        assert (M0 : 0 <= bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) - 64) by keeplia CEIL LO ACV;
        assert (M1 : bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) - 64 <= Z.max (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) - 64) alloc_ceiling) by (clear; lia);
        pose proof (stack_shadow_sub LPA _ SB N _ _ _ _ STKSHk M1 (Z.le_refl _) M0) as SSx;
        pose proof (crange_stack_shadow (Clg:=Clg) LPA A1 _ _ SB N _ _ AINVq SSx ltac:(clear; lia)) as CRS; clear SSx M0 M1;
        eapply stack_shadow_again; [exact STKSHk| | reflexivity];
        apply (bytes_at_ccall LPA A1 A2 xsp win V Nn ma mb CF2 SB);
        [ rewrite zeros_length, Z2Nat.id by exact SSN; exact CRS
        | rewrite zeros_length, Z2Nat.id by exact SSN; split; [keeplia SSC SST SHC8 LO CEIL ACV| intros i Hi X; unfold newblk, blk in X; keeplia Hi X SSC SST SHC8 SI1lo BI1lo VEPlo SHSI1 SHBI1]
        | exact SSB ]
      | ]
    end.
    clear MPF. hide DVSI. hide DVBI. hide DSSI. hide DSBI. hide DBSI. hide DBBI.
    (* [comment removed for export] *)
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINV2 LV2) as SHV. fold_cl_segs. fold_aview.
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV. rewrite <- EzsV in SHV.
    pose proof (proj1 HENV) as [ageh HFRh].
    pose proof (as_frame_blk_disjoint (Clg:=Clg) LPA A2 mc mdc (h_ff H) HCLASS ageh VEP 312 AINV2 ltac:(rewrite (FRS2 (h_ff H)), (FSk (h_ff H)); exact HFRh) LV2) as DJfV.
    change (fsize HCLASS) with 8192 in DJfV.
    hide_neqs.
    (* [comment removed for export] *)
    assert (MP2 : mapped (aview A2 mc) (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192))))) (160 + (128 + 16 + (192 + 16 + (80 + 8192)))))
      by (eapply (window_mapped LPA _ lo (bv_unsigned sp + -160) (bv_unsigned sp)); [exact ST2| exact FR1| cbn [cells_size csize Nat.add]; clear; lia| exact CEIL| keeplia LO| clear; lia]).
    pose proof (munch_refl [(VEP + 288, VEP + 292)] (aview A2 mc)) as MU3. pose proof (wmono_refl rsegs (aview A2 mc)) as WM3.
    assert (CFP3 : client_fp LPA A2 (aview A2 mc) [(VEP + 288, VEP + 292)]) by (cbn; split; [right; left; exists VEP, 312; split; [exact LV2| clear; lia]| exact I]).
    ago AINV2. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vrechk SHV EzsV (VEP + 288) 4 1.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    do 13 zstep. zstep.
    try replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (VEPC3 : rw_cells rsegs mx VEP (vep_cells (fupd (fupd vv Finclude_continue 0) Finclude_src 0) tag q));
      [ rewrite <- vep_cells_include_src; unfold vep_cells; cbn [firstn skipn fupd vf_beq vf_index N.eqb Pos.eqb];
        lazymatch type of VA with rw_cells _ _ _ ?pre => apply (rw_cells_join3 rsegs mx VEP pre); [exact VA| exact PSC|] end;
        eapply rwc_eq; [exact VBk| cbn [cells_size csize Nat.add length]; rewrite ?TAG8; cbn [Nat.add]; change (Z.of_nat 280) with 280; change (Z.of_nat 8) with 8; lia]
      | ] end.
    clear VA VBk PSC.
    lazymatch goal with FRq : rw_cells _ ?mx (bv_unsigned sp + -160) _, STq : stk _ ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      release_frame FRq STq (bv_unsigned sp); rename STq into STv end.
    astop AINV2 MU3 WM3 CFP3.
    lazymatch goal with AIq : ainv A2 ?mq ?mdq |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ => rename AIq into AINV3 end.
    unhide_neqs. unhide DSB1.
    lazymatch goal with MIq : mem_inv _ (aview A2 ?mq) |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mq _) ?mdq) _ =>
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 mq mdq (fupd (fupd vv Finclude_continue 0) Finclude_src 0) vv1);
      [ exact AINV3 | exact MIq
      | eapply amd_frame_trans; [exact MDFk|]; eapply amd_frame_sbm_l; [exact SBq| exact MH1|]; eapply amd_frame_trans; [exact MDF2| apply amd_frame_sbm; [exact SBM| exact MH2]]
      | exact STv
      | eapply (henv_ok_munch LPA); [exact HENV2| exact MU3| exact WM3| exact HG|];
        intros a Ha; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha; change (8192 / 8) with 1024 in Ha;
        pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(keeplia GCE) ltac:(clear; lia) ltac:(keeplia GHI)) as SHF; rewrite SHMAX_val in SHF; change ((8192 + 7) / 8) with 1024 in SHF;
        cbn [outside]; keeplia Ha DJfV GCE GHI SHF VEPlo ACV CEIL LO
      | split; [exact LV2|]; split; [exact VEPC3|]; split; [exact TAG8| exact PADS]
      | vkeep_tac (vkeep_refl vv [Fstate; Finclude_src; Finclude_continue])
      | left; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; left; reflexivity
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | eapply vsb_obj_munch; [exact SOBJ2| exact MU3| exact WM3| intros a Ha; cbn; keeplia Ha DVS1 DVB1 VEPlo]
      | rewrite EVI; cbv iota beta; keeplia LENk E0 BUD
      | exact SZk
      | destruct RELk as [R|[R1 R2]]; [left; exact R| right; split; [exact R1| rewrite (LIVEq2 _ (not_eq_sym NISB) (not_eq_sym NIBB)); exact R2]]
      | rewrite EVI; cbv iota beta; split; [exact DEADS|]; split; [exact DEADB|]; split;
        [ intros r_ R1_ R2_ R3 R4; rewrite (LIVEq2 r_ R3 R4); exact (LIVEk r_ R1_ R2_)
        | split; [rewrite LB2, LBk; clear; lia| rewrite NL2, NLk; clear; lia] ]
      | split; [intros ff k age HFf; exists 0%nat; rewrite Nat.add_0_r, (FRS2 ff), (FSk ff); split; [exact HFf| clear; lia]
              | intros ff HFf; rewrite (FRS2 ff), (FSk ff); exact HFf]
      | rewrite TC2; exact TCk | rewrite SC2; exact SCk | rewrite PC2; exact PCk (* [comment removed for export] *)
      | ]
    end.
    (* [comment removed for export] *)
    assert (MP3f : forall v, stk rsegs v lo (bv_unsigned sp) -> mapped v (bv_unsigned sp - (160 + (128 + 16 + (192 + 16 + (80 + 8192))))) (160 + (128 + 16 + (192 + 16 + (80 + 8192)))))
      by (intros v STx; eapply (stk_mapped (L:=LPA)); [exact STx | exact CEIL | keeplia LO | clear; lia]).
    ufs. rewrite EVI. cbv iota beta.
    eapply cframe_after; [| exact MU3| intros a Ha NO; cbn [outside] in NO; right; left; left; split; [keeplia VEPlo| keeplia NO]| apply MP3f; exact STv].
    eapply (cframe_seq LPA _ (owned A1) _ (bv_unsigned sp) (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) (160 + (128 + 16 + (192 + 16 + (80 + 8192))))
              (160 + (128 + 16 + (192 + 16 + (80 + 8192)))) _ _ _ _ _ _ (aview A0 m0) _ (aview A2 mc));
      [ exact CFk
      | eapply (cframe_reframe LPA _ _ _ _ (bv_unsigned sp) (160 + (128 + 16 + (192 + 16 + (80 + 8192))))); [exact CF2| clear; lia| clear; lia| exact MP2]
      | clear; lia | clear; lia | exact MP2
      | intros a X; exact X
      | intros a [X|[X|X]]; right; [right; right; right; left; left; exact X| right; right; right; left; right; exact X| left; split; [keeplia VEPlo| keeplia X]]
      | intros a X; left; exact X ].
  Qed.
End S.
