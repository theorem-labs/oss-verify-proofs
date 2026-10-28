(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface Atp_pid Atp_defs Atp_h_defs El_defs El_hdr El_h2 El_h3 El_act El_a08.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem arm8_proof : arm_stmt 8 0x3c494.
Proof.
  unfold arm_stmt. intros until p50. intros EA AE HK.
  pose proof AE as AE'.
  destruct AE' as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                   & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).

  unfold el_act, el_throwing. rewrite EA. cbn [Z.eqb Pos.eqb orb]. apply implM_ret_bind.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold implM. iprefix.

  step. step.
  eapply evt_cut.
  { eapply (getdbl_spec E OK) with (s := st) (q := sp0) (node := sp0 + 296);
      [exact AI| exact ROOT| exact HEAP| exact FRM| exact MI| lia| lia| rewrite ELO; exact ST| rewrite ELO; lia| lia| rewrite EB; lia| rewrite EDOC; lia]. }
  cbv beta. intros ms2 PO. unfold getdbl_post in PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FRM2).
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  rewrite ELO in ST2.
  assert (MU2' : munch [(lo, sp0); (sp0 + 8, sp0 + 296)]%Z m m2) by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros x Hx; lia).
  pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG2.
  apply (rw_cells_agree _ _ _ _ _ AG2) in RES; [| intros y Hy; cbn in Hy; cbn [outside]; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in OS; [| intros y Hy; cbn in Hy; cbn [outside]; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in ERR; [| intros y Hy; cbn in Hy; cbn [outside]; unfold LX_ERRNO, RATP in Hy; lia].
  assert (HEAP2 : RHEAP st (ae_LB E) m2)
    by (eapply LH_frame; [exact HEAP| exact MU2| exact WM2|]; constructor; [apply W_ok_stack; cbn; lia| constructor]).
  destruct (act_env_call E m0 m m2 s00 st st LB D d sp0 lo B errv errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos jres jos j313 j329 j361 j416 j441
              nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc fc' AE MU2' WM2 MI2 ST2 HEAP2 eq_refl eq_refl ERR RES OS FRM2) as (AE2 & _ & _).
  clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.

  step.
  ihere. apply HK. unfold EL_EXIT in *.
  eapply act_post_here; [exact AE2| reflexivity| reflexivity].
Qed.
End WithCeiling0.
