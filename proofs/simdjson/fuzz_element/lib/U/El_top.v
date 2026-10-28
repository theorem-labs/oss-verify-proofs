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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1 SjStage1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require SjAlloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface Sj_h_parse Atp_defs Atp_h_defs El_defs El_hdr El_h1 El_h2 El_exit El_h3.
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

Ltac reassoc HH :=
  cbv beta;
  lazymatch goal with
  | |- implM _ (mbind (mbind _ _) _) _ _ _ =>
      apply implM_bind_assoc; eapply implM_bind_cong;
      [ let a := fresh "a" in let s := fresh "s" in let ms := fresh "ms" in let H := fresh "HH" in intros a s ms H; reassoc H | exact HH ]
  | _ => exact HH
  end.
Ltac reassoc_top :=
  cbv beta;
  lazymatch goal with
  | |- implM _ (mbind (mbind _ _) _) _ _ _ =>
      apply implM_bind_assoc; eapply implM_bind_cong;
      [ let a := fresh "a" in let s := fresh "s" in let ms := fresh "ms" in let H := fresh "HH" in intros a s ms H; reassoc H | ]
  end.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis S2 : stage2t_stmt.
  Hypothesis ACT : el_act_stmt.

  Theorem rfuzz_one_of_parts : rfuzz_one_stmt.
  Proof.
    unfold rfuzz_one_stmt. intros until canary.
    intros HEAP LXS SJS SEW SSP AUX SPB B62 ST CEIL GLO LO ERR TP MI AL16 PL FRM HA0 HA1.
    assert (B63 : B < 2^62) by lia.
    unfold ElModel.fuzz_one, fuzz_one_with. cbn [bind ret lib_malloc lib_free lops Target.ops cho].
    eapply (lftoi_vec_cps HM HF); try eassumption.
    cbv beta. intros v st1 ms1 VP. unfold vec_post in VP.
    destruct VP as (x1 & t0' & t1' & t2' & xs0 & xs1 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & xs2 & xs3 & xs4 & xs5 & xs7 & xs8 & t3' & t4' & t5' & t6' & m1 & errv1 & A & cap & bv & jr
                    & j0 & c8 & c16 & c24 & c32 & c40 & j48 & jel & jpa & j416 & j441 & sel
                    & -> & -> & CAPB & MI1 & ST1 & ERR1 & AUX1 & FA1 & SO1 & HEAP1 & VR1 & PRES1 & SJS1 & PL1 & J0 & SCR & J48 & JEL & JPA & XSEL & SELB & SELD & XFD & SAVE).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK in LO.
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST1 as [? _]; assumption).
    pose proof PL1 as (_ & _ & D0 & DN & _ & _). assert (ZD0 : 0 <= zlength d) by (unfold zlength; lia).
    assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR1.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.

    pose proof VR1 as VRC. unfold vrep, vblk, rblock_range in VRC. cbv beta iota zeta in VRC.
    destruct VRC as (_ & _ & _ & _ & _ & (APOS & A16 & N16 & AC & _) & CAP1).
    assert (L7 : Z.land A 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; lia).
    assert (AR : 0 < A < 2^63) by (clear - APOS AC CAP1 N16 CEIL; lia).
    clear N16 CAP1.
    unfold implM. iprefix.
    zstep. if_cases KA; zify_cond KA;
      try solve [exfalso; rewrite ?unsigned_lit in KA by (clear - AR; lia); clear - KA AR; lia]. clear KA.
    zstep. zstep. if_cases KB; zify_cond KB;
      try solve [exfalso; rewrite ?unsigned_lit, ?land64_mod, ?Z.mod_small in KB by (clear - AR; lia); rewrite ?L7 in KB; clear - KB; lia]. clear KB.
    step. step.
    destruct (el_fd_ok d) eqn:FD.
    -
      if_cases K; zify_cond K; [exfalso; try rewrite land64_mod, Z.mod_small in K by lia; lia|]. clear K.
      ihere. to_implM. unfold el_parse_phase. cbn [bind ret lib_malloc lib_free lops Target.ops cho].
      reassoc_top.
      specialize (SELD eq_refl). subst sel.
      eapply (lftoi_parse_cps HM HF S2) with (m0 := m) (s00 := s) (init := init);
        [exact HEAP| exact LXS| exact HEAP1| exact AUX1| lia| (clear - B63; lia)| exact ST1| exact CEIL'| exact GLO| unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK; lia
        | rewrite ELX; exact ERR1| exact MI1| replace (bv_unsigned sp - 528 + 528) with (bv_unsigned sp) by lia; exact AL16| exact FRM| exact FA1| exact SO1
        | exact VR1| exact CAPB| exact PRES1| exact SJS1| exact PL1| exact FD| exact J0| exact SCR| exact J48| exact JEL| exact JPA| exact XSEL| exact XFD| exact SAVE|].
      cbv beta. intros psb ptp pim pix poc pia st2 ms2 GP.
      eapply (lftoi_back HF ACT) with (m0 := m); try eassumption.
    -
      if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
      ihere. to_implM. apply implM_ret_bind.

      pose proof (rw_cells_join _ _ _ _ _ J0 SCR ltac:(cbn [cells_size csize Nat.add]; lia)) as Q1.
      pose proof (rw_cells_join _ _ _ _ _ Q1 J48 ltac:(cbn [app cells_size csize Nat.add]; lia)) as Q2.
      pose proof (rw_cells_join _ _ _ _ _ Q2 JEL ltac:(cbn [app cells_size csize Nat.add]; lia)) as Q3.
      pose proof (rw_cells_join _ _ _ _ _ Q3 JPA ltac:(cbn [app cells_size csize Nat.add]; lia)) as Q4. cbn [app] in Q4.
      destruct (rw_cells_forget _ _ _ _ Q4) as [jlow LOW]. cbn [cells_size csize Nat.add] in LOW.
      pose proof (rw_cells_join _ _ _ _ _ XSEL XFD ltac:(cbn [cells_size csize Nat.add]; lia)) as Q5. cbn [app] in Q5.
      destruct (rw_cells_forget _ _ _ _ Q5) as [jmid MID]. cbn [cells_size csize Nat.add] in MID.
      clear Q1 Q2 Q3 Q4 Q5.
      destruct VR1 as (ELS & SZ & SV & BLK).

      pose proof (tp_of_pres _ _ _ _ LXS PRES1) as TPC1.
      subst tp. eapply (vexit_cps HF); try eassumption; try lia.
      replace (bv_unsigned sp) with (bv_unsigned sp - 528 + 528) by lia. apply pres_X3. exact PRES1.
  Qed.
End Proofs.
End WithCeiling0.
