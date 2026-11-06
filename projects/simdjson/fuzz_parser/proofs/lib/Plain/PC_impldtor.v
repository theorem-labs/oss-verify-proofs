(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require RMalloc_ifaceP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PC_kit PC_docdtor PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition PIMPL_DTOR : Z := 0x38590.
Definition IMPLDTOR_STACK : Z := 16 + RFREE_STACK.

(* [comment removed for export] *)
Definition impl_rm (pim psi poc pia : bptr) (LB : list block) : list block :=
  lb_remove pim (lb_remove psi (lb_remove poc (lb_remove pia LB))).

Definition impldtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (pim psi poc pia : bptr) (lo B : Z) (m : mem) (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres (impl_rm pim psi poc pia LB) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (impl_rm pim psi poc pia LB) m'.

Definition impldtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (pim psi poc pia : bptr) (AIM ASI AOC AIA nim nsi noc nia lo B : Z) (errv v0 : word),
  RHEAP s LB m -> In (pim, AIM, nim) LB -> In (psi, ASI, nsi) LB -> In (poc, AOC, noc) LB -> In (pia, AIA, nia) LB ->
  List.NoDup [pim; psi; poc; pia] -> 72 <= nim ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - IMPLDTOR_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  rw_cells psegs m AIM [C8 v0] -> rw_cells psegs m (AIM + 16) [C8 (Z_to_bv 64 ASI)] ->
  rw_cells psegs m (AIM + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA)] ->
  a0 = Z_to_bv 64 AIM ->
  implM psegs (HarnessP.impl_dtor raw_free (pim, psi, poc, pia)) s
        (impldtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB pim psi poc pia lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PIMPL_DTOR) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Ltac keep_blk HPR H b :=
  eapply rheap_pres_rw_cells; [exact HPR| exact H| right; right; exists b; split; [| cbn; lia]].

Section Proof.
  Hypothesis ODA : opdelete_arr_stmt.
  Hypothesis OD : opdelete_stmt.
  Theorem impldtor_proof : impldtor_stmt.
  Proof.
    unfold impldtor_stmt. intros until v0. intros HP INM INS INO INA ND NIM AUX SPB ST LOA LOS ERR MI TP IM0 IM16 IM56 A0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold IMPLDTOR_STACK, RFREE_STACK in LOS. atop_facts.
    subst tp. rewrite errno_lit in ERR. unfold RERRNO in ERR.
    assert (NE : pim <> psi /\ pim <> poc /\ pim <> pia /\ psi <> poc /\ psi <> pia /\ poc <> pia).
    { apply NoDup_cons_iff in ND as [N1 ND]. apply NoDup_cons_iff in ND as [N2 ND]. apply NoDup_cons_iff in ND as [N3 _].
      cbn in N1, N2, N3. repeat split; intros E; subst; tauto. }
    destruct NE as (NE1 & NE2 & NE3 & NE4 & NE5 & NE6).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HP INM) as (BM1 & BM2 & BM3 & BM4 & BM5).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HP INS) as (BS1 & BS2 & BS3 & BS4 & BS5).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HP INO) as (BO1 & BO2 & BO3 & BO4 & BO5).
    pose proof (RMalloc_ifaceP.RHEAP_block_range_proof s LB m _ HP INA) as (BA1 & BA2 & BA3 & BA4 & BA5).
    cbn [blk_addr blk_size fst snd] in *.
    (* [comment removed for export] *)
    assert (OTH : forall b, In b LB -> blk_id b <> pim -> blk_addr b + blk_size b <= AIM \/ AIM + nim <= blk_addr b).
    { intros b Hb Hn. pose proof (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof s LB m (pim, AIM, nim) b HP INM Hb ltac:(cbn; congruence)) as D.
      cbn [blk_addr blk_size fst snd] in D. lia. }
    assert (LBB : forall b, In b LB -> blk_addr b + blk_size b <= ATOP)
      by (intros b Hb; destruct (RMalloc_ifaceP.RHEAP_block_range_proof s LB m b HP Hb) as (_ & _ & _ & R4 & _); exact R4).
    assert (INRM : forall b, In b (impl_rm pim psi poc pia LB) -> In b LB /\ blk_id b <> pim).
    { intros b Hb. unfold impl_rm in Hb. split.
      - apply lb_remove_in_inv in Hb. apply lb_remove_in_inv in Hb. apply lb_remove_in_inv in Hb. apply lb_remove_in_inv in Hb. exact Hb.
      - exact (lb_remove_in_ne _ _ _ Hb). }
    (* [comment removed for export] *)
    assert (OWN : forall L a, (forall b, In b L -> In b LB /\ blk_id b <> pim) -> 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a ->
              outside [(lo, bv_unsigned sp); (AIM, AIM + 72)] a).
    { intros L a HL Ha Hc. cbn. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| lia|].
      destruct (HL b Hb) as [Hb' Hn]. pose proof (OTH b Hb' Hn). pose proof (LBB b Hb'). lia. }
    unfold HarnessP.impl_dtor, HarnessP.opdelete.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (AIM, AIM + 72)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    carve_frame 16%nat ST.
    subst a0. unfold PIMPL_DTOR.
    do 7 zstep.
    if_cases K1; zify_cond K1; [exfalso; lia|].
    do 1 zstep.
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP1 : RHEAP s LB mx)
        by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
            apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [right; right; exists (pim, AIM, nim); split; [exact INM| cbn; lia]| apply Forall_nil]);
      assert (AUX1 : rauxv_ok mx B)
        by (eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil])
    end.
    clear HP AUX.
    (* [comment removed for export] *)
    eapply implM_bind.
    { eapply ODA with (lo := lo) (B := B) (A := AIA) (n := nia); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP1 | exact INA | exact AUX1 | exact ST | exact MI | (rewrite errno_lit; unfold RERRNO; exact ERR) | (unfold RFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s1' ms1 PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & HP2).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPR by lia. rewrite errno_lit in ERR2. unfold RERRNO in ERR2.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    assert (INM2 : In (pim, AIM, nim) (lb_remove pia LB)) by (apply lb_remove_keep_in; [exact INM| cbn; congruence]).
    assert (INS2 : In (psi, ASI, nsi) (lb_remove pia LB)) by (apply lb_remove_keep_in; [exact INS| cbn; congruence]).
    assert (INO2 : In (poc, AOC, noc) (lb_remove pia LB)) by (apply lb_remove_keep_in; [exact INO| cbn; congruence]).
    lazymatch goal with FR : rw_cells psegs _ (bv_unsigned sp + -16) ?cs |- _ =>
      assert (FR2 : rw_cells psegs m2 (bv_unsigned sp + -16) cs) by (eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]); clear FR end.
    lazymatch goal with H : rw_cells psegs _ AIM ?cs |- _ =>
      assert (IM0b : rw_cells psegs m2 AIM cs) by (keep_blk HPR H (pim, AIM, nim); exact INM2); clear H end.
    lazymatch goal with H : rw_cells psegs _ (AIM + 16) ?cs |- _ =>
      assert (IM16b : rw_cells psegs m2 (AIM + 16) cs) by (keep_blk HPR H (pim, AIM, nim); exact INM2); clear H end.
    lazymatch goal with H : rw_cells psegs _ (AIM + 56) ?cs |- _ =>
      assert (IM56b : rw_cells psegs m2 (AIM + 56) cs) by (keep_blk HPR H (pim, AIM, nim); exact INM2); clear H end.
    clear ST MI ERR AUX1.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (AIM, AIM + 72)] m2) as MU2. pose proof (wmono_refl psegs m2) as WM2.
    do 3 zstep.
    if_cases K2; zify_cond K2; [exfalso; lia|].
    do 1 zstep.
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP3 : RHEAP s1' (lb_remove pia LB) mx)
        by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP2| exact MU2| exact WM2|];
            apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [right; right; exists (pim, AIM, nim); split; [exact INM2| cbn; lia]| apply Forall_nil]);
      assert (AUX3 : rauxv_ok mx B)
        by (eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil])
    end.
    clear HP2 AUX2.
    (* [comment removed for export] *)
    eapply implM_bind.
    { eapply ODA with (lo := lo) (B := B) (A := AOC) (n := noc); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP3 | exact INO2 | exact AUX3 | exact ST2 | exact MI2 | (rewrite errno_lit; unfold RERRNO; exact ERR2) | (unfold RFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s2' ms2 PO.
    destruct PO as (v0' & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & HPR2 & FAE2 & SOE2 & HP4).
    rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR2 by lia. rewrite errno_lit in ERR4. unfold RERRNO in ERR4.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    assert (INM4 : In (pim, AIM, nim) (lb_remove poc (lb_remove pia LB))) by (apply lb_remove_keep_in; [exact INM2| cbn; congruence]).
    assert (INS4 : In (psi, ASI, nsi) (lb_remove poc (lb_remove pia LB))) by (apply lb_remove_keep_in; [exact INS2| cbn; congruence]).
    lazymatch goal with FR : rw_cells psegs _ (bv_unsigned sp + -16) ?cs |- _ =>
      assert (FR4 : rw_cells psegs m4 (bv_unsigned sp + -16) cs) by (eapply rheap_pres_rw_cells; [exact HPR2| exact FR| left; cbn; lia]); clear FR end.
    lazymatch goal with H : rw_cells psegs _ AIM ?cs |- _ =>
      assert (IM0c : rw_cells psegs m4 AIM cs) by (keep_blk HPR2 H (pim, AIM, nim); exact INM4); clear H end.
    lazymatch goal with H : rw_cells psegs _ (AIM + 16) ?cs |- _ =>
      assert (IM16c : rw_cells psegs m4 (AIM + 16) cs) by (keep_blk HPR2 H (pim, AIM, nim); exact INM4); clear H end.
    lazymatch goal with H : rw_cells psegs _ (AIM + 56) ?cs |- _ =>
      assert (IM56c : rw_cells psegs m4 (AIM + 56) cs) by (keep_blk HPR2 H (pim, AIM, nim); exact INM4); clear H end.
    clear ST2 MI2 ERR2 AUX3.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp); (AIM, AIM + 72)] m4) as MU4. pose proof (wmono_refl psegs m4) as WM4.
    do 6 zstep.
    if_cases K3; zify_cond K3; [exfalso; lia|].
    do 1 zstep.
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP5 : RHEAP s2' (lb_remove poc (lb_remove pia LB)) mx)
        by (eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP4| exact MU4| exact WM4|];
            apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [right; right; exists (pim, AIM, nim); split; [exact INM4| cbn; lia]| apply Forall_nil]);
      assert (AUX5 : rauxv_ok mx B)
        by (eapply rauxv_ok_frame; [exact AUX4| exact MU4| exact WM4| repeat (apply Forall_cons; [cbn; unfold RAUXV_CELL in *; lia|]); apply Forall_nil])
    end.
    clear HP4 AUX4.
    (* [comment removed for export] *)
    eapply implM_bind.
    { eapply ODA with (lo := lo) (B := B) (A := ASI) (n := nsi); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP5 | exact INS4 | exact AUX5 | exact ST4 | exact MI4 | (rewrite errno_lit; unfold RERRNO; exact ERR4) | (unfold RFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s3' ms3 PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m6 & -> & MI6 & ST6 & ERR6 & AUX6 & HPR3 & FAE3 & SOE3 & HP6).
    rewrite ?unsigned_lit in ST6 by lia. rewrite ?unsigned_lit in HPR3 by lia. rewrite errno_lit in ERR6. unfold RERRNO in ERR6.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; rpc) end.
    assert (INM6 : In (pim, AIM, nim) (lb_remove psi (lb_remove poc (lb_remove pia LB)))) by (apply lb_remove_keep_in; [exact INM4| cbn; congruence]).
    lazymatch goal with FR : rw_cells psegs _ (bv_unsigned sp + -16) ?cs |- _ =>
      assert (FR6 : rw_cells psegs m6 (bv_unsigned sp + -16) cs) by (eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia]); clear FR end.
    clear ST4 MI4 ERR4 AUX5.
    apply implM_from_evt.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m6) as MU6. pose proof (wmono_refl psegs m6) as WM6.
    do 6 zstep.
    release_frame FR6 ST6 (bv_unsigned sp).
    apply evt_done.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HP7 : RHEAP s3' (lb_remove psi (lb_remove poc (lb_remove pia LB))) mx)
        by (eapply RHEAP_stack_frame; [exact HP6| exact MU6| exact WM6| repeat constructor; cbn; lia]);
      assert (AUX7 : rauxv_ok mx B) by (eapply rauxv_ok_stack_frame; [exact AUX6| exact MU6| exact WM6| repeat constructor; cbn; lia])
    end.
    (* [comment removed for export] *)
    eapply implM_mono.
    { eapply (proj1 (proj2 OD)) with (lo := lo) (B := B) (A := AIM) (n := nim); try reflexivity; unfold RATP; rewrite ?unsigned_lit by lia;
        first [exact HP7 | exact INM6 | exact AUX7 | exact ST6 | exact MI6 | (rewrite errno_lit; unfold RERRNO; exact ERR6) | (unfold RFREE_STACK; lia) | lia]. }
    cbv beta. intros [] s4' ms4 PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & m8 & -> & MI8 & ST8 & ERR8 & AUX8 & HPR4 & FAE4 & SOE4 & HP8).
    unfold impldtor_post. do 16 eexists. exists errv. split; [reflexivity|].
    split; [exact MI8|]. split; [exact ST8|]. split; [exact ERR8|]. split; [exact AUX8|].
    split.
    { fold (impl_rm pim psi poc pia LB) in HPR4.
      eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| intros a Ha Hc; exact (OWN _ a INRM Ha Hc)]|].
      eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; unfold impl_rm in Hb;
        apply lb_remove_in_inv in Hb; apply lb_remove_in_inv in Hb; apply lb_remove_in_inv in Hb; exact Hb]|].
      eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU2| exact WM2| intros a Ha Hc; exact (OWN _ a INRM Ha Hc)]|].
      eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPR2| lia| intros b Hb; unfold impl_rm in Hb;
        apply lb_remove_in_inv in Hb; apply lb_remove_in_inv in Hb; exact Hb]|].
      eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU4| exact WM4| intros a Ha Hc; exact (OWN _ a INRM Ha Hc)]|].
      eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HPR3| lia| intros b Hb; unfold impl_rm in Hb;
        apply lb_remove_in_inv in Hb; exact Hb]|].
      eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU6| exact WM6| intros a Ha Hc; cbn; destruct Hc as [Hc|[Hc|Hc]]; [lia| lia|];
        destruct Hc as (b & Hb & Hr); destruct (INRM b Hb) as [Hb' _]; pose proof (LBB b Hb'); lia]|].
      exact HPR4. }
    split; [congruence|]. split; [congruence|]. exact HP8.
  Qed.
End Proof.
End CANSEC1.
