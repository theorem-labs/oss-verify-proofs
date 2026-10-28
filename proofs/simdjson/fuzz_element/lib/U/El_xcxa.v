(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import STree Malloc MallocCtrl Prog KInv MI_Inv Monad Target SjModel AtpModel ElModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks MallocFacts_B MallocFacts_inv MallocKit_B F_malloc_free F_malloc_fast Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require MallocFacts_inv3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memset Sj_iface El_xmalloc El_xalloc.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Ltac st1 := step; fix_lit_store; try nrm.
Ltac probe := match goal with |- ?g => idtac "PROBE"; idtac g end; fail "PROBE".

Ltac br K := try (if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; try (exfalso; first [lia | apply K; reflexivity | congruence])).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma pw_munch : forall m' m W, pweq m' m -> munch W m m'.
Proof. intros m' m W PW x _. apply PW. Qed.
Lemma pw_wmono : forall m' m, pweq m' m -> wmono usegs m m'.
Proof. intros m' m PW x H. rewrite (pw_wview m' m x PW). exact H. Qed.

Lemma rheap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono usegs m m' -> (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) -> rheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM HW a Ha HC. split; [| apply WM]. apply MU. unfold wa. rewrite unsigned_lit by lia. apply HW; assumption.
Qed.

Lemma rw_cells_skip1 : forall (m : word -> option byte) A c cs,
  rw_cells usegs m A (c :: cs) -> rw_cells usegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[Hwf Hb] Hw]. cbn [cells_wf] in Hwf. destruct Hwf as [Hc Hcs].
  cbn [cells_bytes] in Hb. apply Mem.bytes_at_app in Hb as [_ Hb]. rewrite (cbytes_length c Hc) in Hb.
  split; [split; [exact Hcs| exact Hb]|]. cbn [cells_size] in Hw. destruct Hw as (W0 & W1 & W).
  split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply W. lia.
Qed.

Definition cxa_pre_post (sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo usp : Z) : machine_state -> Prop :=
  fun ms1 => exists a1 a2 m1 (j0 j1 : list byte),
    ms1 = MS (mkR (wz 0xc20e0) (wz (usp + -80)) gp tp t0 t1 t2 (wz 16) (wz 144) (wz 144) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz rmalloc_entry) fc None m1 (seg_rom usegs)
    /\ munch [(usp - 80, usp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (usp + -80)
    /\ rw_cells usegs m1 (usp + -80) [CB 8 j1; C8 s1; C8 (wz 144); C8 (wz 0x7c044)]
    /\ rw_cells usegs m1 (usp + -48) [C8 (wz 144); C8 (wz 0x7b924)]
    /\ rw_cells usegs m1 (usp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra].

Lemma cxa_pre_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m lo,
  let usp := bv_unsigned sp in
  stk usegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - 80 -> mem_inv usegs m ->
  rw_cells usegs m 0x10fd38 [C4 (wz 0); C4 (wz 0)] ->
  evt usegs (cxa_pre_post sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m lo usp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 16) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x7b904) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros usp ST CEIL LO MI MR0. subst usp. pose proof alloc_ceiling_range as CR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold wz.

  st1. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
  st1. st1. st1.

  st1. st1. st1. st1.

  st1. carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 junk0 [] [8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
  st1. st1. st1. st1. st1. st1. st1.
  st1. br K1.
  st1. st1. st1.

  st1. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk1 [] [8;8;8;8]%nat) in FR1; [|reflexivity]. cbn [mk_CB_cells app] in FR1.
  st1. st1. st1.

  st1. st1. st1. br K2.

  st1. st1. br K3.

  st1. st1. br K4.

  st1. st1. st1. br K5.

  st1. st1. br K6.
  st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold cxa_pre_post.
  match goal with FRa : rw_cells _ ?mm (bv_unsigned sp + -80) _, FRb : rw_cells _ _ (bv_unsigned sp + -48) _, FRc : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ =>
    do 5 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|];
    split; [exact FRa|]; split; [exact FRb| exact FRc] end.
Qed.

Lemma cxa_mid_walk : forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (usp A : Z),
  sp = wz (usp + -48) -> 0 < A < 2^64 -> 80 <= usp -> usp <= 2^64 ->
  rw_cells usegs m (usp + -48) [C8 (wz 144); C8 (wz 0x7b924)] -> mem_inv usegs m ->
  evt usegs (fun ms2 =>
      ms2 = MS (mkR (wz 0x7b93c) (wz (usp + -32)) gp tp t0 t1 t2 (wz 144) (wz A) (wz A) (wz 0) (wz 144) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0xd0c68) fc None m (seg_rom usegs))
    (MS (mkR (wz 0x7c044) sp gp tp t0 t1 t2 (wz 144) s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (wz 0x7c044)) fc None m (seg_rom usegs)).
Proof.
  intros until A. intros -> HA HU UT FR MI. rewrite ret_pc_even by lia. unfold wz in *.

  st1. br K. st1. st1. st1. st1.

  st1. st1. br K2. st1. st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

Lemma cxa_end_walk : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0c s1c : word) F fc m (usp A : Z) (j0 : list byte),
  sp = wz (usp + -32) -> 0 < A -> A + 144 < 2^64 -> 80 <= usp -> usp <= 2^64 ->
  rw_cells usegs m (usp + -32) [CB 8 j0; C8 s1c; C8 s0c; C8 ra] -> mem_inv usegs m ->
  evt usegs (fun ms3 =>
      ms3 = MS (mkR ra (wz usp) gp tp t0 t1 t2 s0c s1c (wz (A + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m (seg_rom usegs))
    (MS (mkR (wz 0x7b93c) sp gp tp t0 t1 t2 (wz 144) (wz A) (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (wz 0x7b93c)) fc None m (seg_rom usegs)).
Proof.
  intros until j0. intros -> HA HA2 HU UT FR MI. rewrite ret_pc_even by lia. unfold wz in *.

  st1. st1. st1. st1. st1. st1.
  apply evt_done. replace (usp + -32 + 32) with usp by lia. reflexivity.
Qed.

Definition cxa_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B : Z) (m : word -> option byte)
    (r : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' blk (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (blk + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m' /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range blk 144 /\ RHEAP s' ((r, blk, 144) :: LB) m'
    /\ rw_cells usegs m' blk [CB 144 (zeros 144)].

Theorem cxa_alloc_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (lo B : Z) (errv : word),
  let usp := bv_unsigned sp in
  RHEAP s LB m -> rauxv_ok m B -> usp <= B ->
  stk usegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - 80 - RMALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = wz RATP ->
  rw_cells usegs m 0x10fd38 [C4 (wz 0); C4 (wz 0)] ->
  implM usegs (AtpModel.newnt lops EL_EXC) s (cxa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 16) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x7b904) fc None m (seg_rom usegs)).
Proof.
  intros until errv. intros usp HP AUX SPB ST CEIL LO ERR MI TP MR0. subst usp.
  pose proof alloc_ceiling_range as CR. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RMALLOC_STACK in LO.
  unfold AtpModel.newnt. cbn [bind ret lib_malloc unreachable lops Target.ops]. unfold EL_EXC.

  eapply implM_evt; [eapply (cxa_pre_walk ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST CEIL ltac:(lia) MI MR0)|].
  intros ms1 (a1' & a2' & m1 & j0 & j1 & -> & MU1 & WM1 & MI1 & ST1 & FRa & FRb & FRc).
  assert (HP1 : RHEAP s LB m1).
  { eapply RHEAP_frame_proof; [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia| apply Forall_nil]. }
  assert (ERR1 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
  { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn [cells_size csize Nat.add disjoint_from]. repeat split; try exact I; lia. }

  eapply implM_bind.
  { unfold wz. eapply (rmalloc_spec_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB 144 lo B errv HP1 AUX1);
      rewrite ?unsigned_lit by lia; [lia| exact ST1| exact CEIL| unfold RMALLOC_STACK; lia| exact ERR1| exact MI1| exact TP| reflexivity| lia]. }
  intros r s' ms2 POST. unfold rmalloc_post_x in POST.
  destruct POST as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & RP2 & FA2 & SO2 & RES).
  rewrite unsigned_lit in ST2, RP2 by lia.
  destruct r as [p|].
  2:{   apply implM_unr. }
  destruct RES as (A & junk & -> & RB & HX & BLK & _).
  apply implM_ret. rewrite ret_pc_even by lia.
  pose proof RB as (RB1 & RB2 & RB3 & RB4 & RB5).
  destruct HX as (st' & LB0 & PERM & Hst & MR2 & [BL AR] & g & idx & SL & S31).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C2.
  destruct (MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL' & INV & _ & _ & _ & CRR).
  assert (Hin : In (p, A, 144) LB0) by (eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact PERM| left; reflexivity]).
  assert (FRa2 : rw_cells usegs m2 (bv_unsigned sp + -80 + Z.of_nat 8) [C8 s1; C8 (wz 144); C8 (wz 0x7c044)]).
  { apply (rw_cells_skip1 m2 _ (CB 8 j1)). eapply rheap_pres_rw_cells; [exact RP2| exact FRa| left; cbn; lia]. }
  assert (FRb2 : rw_cells usegs m2 (bv_unsigned sp + -48) [C8 (wz 144); C8 (wz 0x7b924)]).
  { eapply rheap_pres_rw_cells; [exact RP2| exact FRb| left; cbn; lia]. }
  assert (FRc2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
  { eapply rheap_pres_rw_cells; [exact RP2| exact FRc| left; cbn; lia]. }
  assert (BLK2 := BLK).

  eapply evt_cut.
  { eapply (aa_tail_spec (Z_to_bv 64 0xc20e0) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
              (wz 0x7c044) (wz 144) s1 F fc m2 st' L BL' LS LB0 p A 144 MR2 MI2 C2 INV CRR Hin); rewrite ?unsigned_lit by lia.
    - intros g' i' SL'. rewrite SL in SL'. injection SL' as <- <-. exact S31.
    - lia.
    - replace (bv_unsigned sp - 80 + 8) with (bv_unsigned sp + -80 + Z.of_nat 8) by lia. exact FRa2.
    - lia.
    - lia. }
  intros ms3 X. unfold aa3_post in X. rewrite unsigned_lit in X by lia.
  destruct X as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m3 & -> & PW & MI3).
  replace (bv_unsigned sp - 80 + 32) with (bv_unsigned sp + -48) by lia.

  eapply evt_cut.
  { eapply (cxa_mid_walk (wz (bv_unsigned sp + -48)) gp tp w0 w1 w2 s1 y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F fc m3 (bv_unsigned sp) A eq_refl);
      [lia| lia| lia| eapply pw_rw_cells; [exact PW| exact FRb2]| exact MI3]. }
  intros ms4 ->.

  eapply evt_cut.
  { unfold wz. eapply (memset_callZ) with (D := A) (C := 0) (N := 144) (junk := junk); [| exact MI3| lia| lia| lia| lia].
    eapply pw_rw_cells; [exact PW| exact BLK2]. }
  intros ms5 X. unfold memset_postZ in X.
  destruct X as (z0 & z1 & z2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & z3 & z4 & z5 & z6 & m4 & -> & MU4 & WM4 & MI4 & ZB).

  eapply evt_cut.
  { eapply (cxa_end_walk (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp z0 z1 z2 q1 q2 q3 q4 q5 q6 q7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6 ra s0 s1 F fc m4 (bv_unsigned sp) A j0 eq_refl);
      [lia| lia| lia| lia| | exact MI4].
    eapply rw_cells_transport; [eapply pw_rw_cells; [exact PW| exact FRc2]| exact MU4| exact WM4|].
    cbn [cells_size csize Nat.add disjoint_from]. repeat split; try exact I; lia. }
  intros ms6 ->. apply evt_done.

  assert (HP2 : RHEAP s' ((p, A, 144) :: LB) m2). { exists st', LB0. split; [exact PERM|]. split; [exact Hst|]. split; [exact MR2|]. split; [exact BL| exact AR]. }
  assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a -> outside [(bv_unsigned sp - 80, bv_unsigned sp)] a /\ outside [(A, A + 144)] a).
  { intros a Ha HC. cbn [outside]. destruct HC as [H|[H|(b & Hb & Hr)]].
    - clear - H Ha RB4 CEIL LO. repeat split; try exact I; lia.
    - unfold ralloc_static in H. clear - H Ha RB5 CEIL LO CR. repeat split; try exact I; lia.
    - pose proof (RHEAP_block_range_proof _ _ _ _ HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5).
      assert (NE : blk_id b <> p).
      { intros EQ. pose proof (RHEAP_blocks_nodup_proof _ _ _ HP2) as ND. cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
        apply NI. rewrite <- EQ. apply in_map. exact Hb. }
      pose proof (RHEAP_blocks_disjoint_proof _ _ _ b (p, A, 144) HP2 ltac:(right; exact Hb) ltac:(left; reflexivity) NE) as DJ.
      cbn [blk_addr blk_size blk_id fst snd] in DJ, Hr, Q4. clear - Hr Ha Q4 CEIL LO DJ. repeat split; try exact I; lia. }
  unfold cxa_post. do 14 eexists. exists m4, A, errv2.
  split; [unfold wz; rewrite (Z_to_bv_bv_unsigned sp); reflexivity|]. split; [exact MI4|].
  split. {
    assert (FRa2' : rw_cells usegs m2 (bv_unsigned sp + -80) [CB 8 j1; C8 s1; C8 (wz 144); C8 (wz 0x7c044)]).
    { eapply rheap_pres_rw_cells; [exact RP2| exact FRa| left; cbn; lia]. }
    pose proof (stk_of_rw_cells usegs _ _ _ FRa2') as Xa. pose proof (stk_of_rw_cells usegs _ _ _ FRb2) as Xb. pose proof (stk_of_rw_cells usegs _ _ _ FRc2) as Xc.
    cbn [cells_size csize Nat.add] in Xa, Xb, Xc.
    replace (bv_unsigned sp + -80 + 32) with (bv_unsigned sp + -48) in Xa by lia.
    replace (bv_unsigned sp + -48 + 16) with (bv_unsigned sp + -32) in Xb by lia.
    replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) in Xc by lia.
    replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in ST2 by lia.
    assert (STF : stk usegs m2 lo (bv_unsigned sp)).
    { eapply stk_merge; [exact ST2| | lia]. eapply stk_merge; [exact Xa| | lia]. eapply stk_merge; [exact Xb| exact Xc| lia]. }
    eapply stk_transport_disjoint; [eapply pw_stk; [exact PW| exact STF]| exact MU4| exact WM4|].
    cbn [disjoint_from]. clear - RB4 CEIL LO. repeat split; try exact I; lia. }
  split. {   eapply rw_cells_transport; [eapply pw_rw_cells; [exact PW| exact ERR2]| exact MU4| exact WM4|].
    subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn [cells_size csize Nat.add disjoint_from]. clear - RB5. repeat split; try exact I; lia. }
  split. {   eapply rauxv_ok_frame; [| exact MU4| exact WM4|].
    - eapply rauxv_ok_frame; [exact AUX2| apply (pw_munch m3 m2 []); exact PW| apply pw_wmono; exact PW| apply Forall_nil].
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold RAUXV_CELL. clear - RB4 RB5 CEIL LO SPB. lia. }
  split. {
    eapply rheap_pres_trans. { eapply (rheap_pres_of_munch LB _ _ m m1 MU1 WM1). intros a Ha HC. exact (proj1 (CLI a Ha HC)). }
    eapply rheap_pres_trans. { eapply rheap_pres_weaken; [exact RP2| lia| intros b Hb; exact Hb]. }
    eapply rheap_pres_trans. { eapply (rheap_pres_of_munch LB _ [] m2 m3); [apply pw_munch; exact PW| apply pw_wmono; exact PW| intros; exact I]. }
    eapply (rheap_pres_of_munch LB _ _ m3 m4 MU4 WM4). intros a Ha HC. exact (proj2 (CLI a Ha HC)). }
  split; [exact FA2|]. split; [exact SO2|]. split; [exact RB|].
  split. {
    eapply RHEAP_frame_proof; [| exact MU4| exact WM4|].
    - eapply RHEAP_frame_proof; [exact HP2| apply (pw_munch m3 m2 []); exact PW| apply pw_wmono; exact PW| apply Forall_nil].
    - apply Forall_cons; [| apply Forall_nil]. right. right. exists (p, A, 144). split; [left; reflexivity|]. cbn. lia. }
  exact ZB.
Qed.
End WithCeiling0.
