(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn MallocFacts_B MallocFacts_inv3 MallocHINV.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_fp RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].

Section PAD. Context {CE__ : Ceiling} {RN__ : RunRnd}.

  Lemma mul_mod16 : forall s i, s mod 16 = 0 -> (s * i) mod 16 = 0.
  Proof. intros s i H. rewrite Z.mul_comm, Z.mul_mod, H, Z.mul_0_r by std_lia__. reflexivity. Qed.

  Lemma rheap_blk_pad : forall s LB m p A n, RHEAP s LB m -> In (p, A, n) LB ->
    exists pad : list byte, bytes_at usegs m (A + n) pad /\ Z.of_nat (length pad) = (- (A + n)) mod 16.
  Proof.
    intros s LB m p A n (st & LB0 & PERM & STRIP & MR & BL & AR) IN.
    assert (IN0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact IN]).
    pose proof (areach_cinv_proof st LB0 AR) as CI.
    pose proof (proj1 (Forall_forall (blk_ok st) LB0) (ci_blks _ _ CI) _ IN0) as BK.
    destruct (bk_slot _ _ BK) as (g & i & b & SL & HO & FB & Hi & NF & off & Hoff & HA & HS & _).
    pose proof (bk_size _ _ BK) as Hn. unfold blk_slot, blk_addr, blk_size in SL, FB, HA, HS, Hn. cbn [fst snd] in SL, FB, HA, HS, Hn.
    destruct (ci_slts _ _ CI _ _ _ SL) as (_ & SP & _).
    pose proof (ci_gmetas _ _ CI _ _ HO) as GO.
    pose proof (go_mem _ _ _ GO) as GM. pose proof (go_stride _ _ _ GO) as (GS1 & GS2).
    pose proof (go_li _ _ _ GO) as GL.
    destruct (go_region _ _ _ GO) as (r & Hr & RK & B0 & B16 & LAST & _).
    unfold sstart_of in LAST. unfold slot_start' in SP. rewrite GM in LAST, SP. cbn [default fst snd] in LAST, SP.
    set (stride := get_stride (get_meta_rec st g)) in *.
    assert (CONC : conc st (fst p) = r_base r + (snd b + (UNIT + stride * i))).
    { unfold conc, get_region. rewrite SP. cbn [aadd fst snd]. rewrite Hr. reflexivity. }
    rewrite CONC in HA. unfold UNIT, IB in HA, HS, LAST, GS1, GS2.
    destruct (rregion_facts st m (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2).
    pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst b) r Hr RK) as [(W0 & W1 & WW) _].
    assert (MON : stride * (i + 1) <= stride * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (E1 : stride * (i + 1) = stride * i + stride) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; reflexivity).
    pose proof (mul_mod16 stride i GS2) as P16.
    set (P := stride * i) in *.
    clear CI BK GO SH NF HO SL.
    set (L := (- (A + n)) mod 16).
    assert (HL : 0 <= L < 16 /\ (A + n + L) mod 16 = 0) by (subst L; split; [apply Z.mod_pos_bound; lia| Z.div_mod_to_equations; lia]).
    assert (FIT : A + n + L <= r_base r + snd b + 16 + P + stride) by (Z.div_mod_to_equations; lia).
    assert (LO : r_base r <= A + n) by lia.
    assert (HI1 : A + n + L <= r_base r + snd b + 16 + stride * (i + 1)) by lia.
    assert (HI2 : stride * (i + 1) <= stride * (m_last_idx (get_meta_rec st g) + 1)) by exact MON.
    assert (HI3 : snd b + 16 + stride * (m_last_idx (get_meta_rec st g) + 1) <= round_up_pg (r_len r)) by exact LAST.
    assert (HI : A + n + L <= r_base r + round_up_pg (r_len r)) by lia.
    assert (RP : 0 < round_up_pg (r_len r)) by lia.
    specialize (RI1 RP). specialize (RI2 RP).
    exists (map (fun k => default (Z_to_bv 8 0) (m (wa (A + n + Z.of_nat k)))) (seq 0 (Z.to_nat L))).
    unfold bytes_at. rewrite !length_map, !length_seq. split; [|lia].
    split; [lia|]. split; [lia|].
    intros k Hk.
    rewrite nth_error_map, (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact Hk). rewrite seq_nth by exact Hk. cbn [option_map Nat.add].
    assert (AK : 0 <= A + n + Z.of_nat k < 2 ^ 64) by lia.
    rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia).
    specialize (WW (A + n + Z.of_nat k - r_base r) ltac:(lia)).
    replace (r_base r + (A + n + Z.of_nat k - r_base r)) with (A + n + Z.of_nat k) in WW by lia.
    rewrite ref_wview_overlay in WW by (rewrite wa_unsigned by lia; lia).
    destruct (m (wa (A + n + Z.of_nat k))); [reflexivity| exfalso; apply WW; reflexivity].
  Qed.

  Lemma cstate_blk_pad : forall s LBall LB L m sp tp lo B p A n,
    cstate s LBall LB L m sp tp lo B -> In (p, A, n) LBall ->
    exists pad : list byte, bytes_at usegs m (A + n) pad /\ Z.of_nat (length pad) = (- (A + n)) mod 16.
  Proof. intros s LBall LB L m sp tp lo B p A n (HP & _) IN. exact (rheap_blk_pad _ _ _ _ _ _ HP IN). Qed.
End PAD.
