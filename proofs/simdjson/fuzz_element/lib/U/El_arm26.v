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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface Atp_pid Atp_defs Atp_h_defs Atp_elem Atp_arrl Atp_arr Atp_obj El_defs El_hdr El_h2 El_h3 El_act.
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

Theorem atp_level : rmalloc_stmt -> rfree_stmt -> forall E, aenv_ok E -> forall d, atp_elem_stmt E d.
Proof.
  intros HM HF E OK d. induction d as [|d IH].
  - apply (atp_elem E OK 0%nat); intros d' Ed; discriminate Ed.
  - apply (atp_elem E OK (S d)); intros d' Ed; injection Ed as <-.
    + exact (atp_obj E OK d IH HM HF).
    + exact (atp_arr E OK d IH).
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Theorem arm26_proof : arm_stmt 26 0x3c4dc.
  Proof.
    unfold arm_stmt. intros until p50. intros EA AE HK.
    pose proof AE as AE'.
    destruct AE' as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                     & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (el_root_elem E OK) as [EL NR].

    unfold el_act, el_throwing. rewrite EA. cbn [Z.eqb Pos.eqb orb].
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.

    step. step. step. step. step.
    ihere. to_implM. rewrite <- EP1.
    eapply implM_bind.
    { unfold el_root in ROOT.
      eapply (atp_level HM HF E OK TAPE_MAX_DEPTH (ae_p1 E) 1 _ sp0 (sp0 + 8) (sp0 + 296) (ae_PTR E)) with (s := st);
        [exact AI| exists []; split; [reflexivity| change (zlength (@nil Z)) with 0; lia]| exact EL| lia| lia| exact ROOT| lia| rewrite EB; lia| lia| exact RES| lia| rewrite EDOC; lia| rewrite EB; lia
        | exact HEAP| rewrite EB; exact AUX| rewrite EDOC; lia| rewrite ELO; exact ST| rewrite ELO; unfold elem_need, ATP_LEAFX, RMALLOC_STACK; change (Z.of_nat TAPE_MAX_DEPTH) with 1024; lia
        | clear - AL16; replace sp0 with (sp0 + 528 + (-33) * 16) by lia; rewrite Z.mod_add by lia; exact AL16| exact ERR| exact MI]. }
    cbv beta. intros [] st2 ms2 PO. unfold hpost in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & (errv2 & ERR2) & AUX2 & FA2 & SO2 & RR).
    unfold lvl_R in RR. destruct RR as (HEAP2 & PRES2 & (jr2 & j2 & code2 & jn2 & RC2 & _)).
    destruct (rw_cells_forget _ _ _ _ RC2) as [jres' RES2]. cbn [cells_size csize Nat.add] in RES2. clear RC2.
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
    rewrite ELO in ST2. rewrite EB in AUX2. replace (sp0 + 8 + 24) with (sp0 + 32) in PRES2 by lia.
    destruct (act_env_pres E m0 m m2 s00 st st2 LB D d sp0 lo B errv errv2 bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos jres' j313 j329 j361 j416 j441
                nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc fc AE PRES2 MI2 ST2 HEAP2 FA2 SO2 ERR2 AUX2 RES2 FRM) as (AE2 & _ & _).

    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    unfold implM. iprefix. step.
    ihere. apply HK. unfold EL_EXIT in *.
    eapply act_post_here; [exact AE2| exact FA2| exact SO2].
  Qed.
End Proofs.
End WithCeiling0.
