(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_fs_defs RT_state RT_rep RT_facts0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Definition geo_ok (Σ : rtsA) : Prop := layout_ok (lay Σ) /\ regs_wf Σ /\ sec_wf Σ /\ fs_wf Σ.

Lemma geo_of_wf0 : forall Σ, rt_wf0 Σ -> geo_ok Σ.
Proof. intros Σ (H1 & H2 & _ & H4 & _ & H6 & _). exact (conj H1 (conj H2 (conj H4 H6))). Qed.
Lemma geo_of_wf : forall Σ, rt_wf Σ -> geo_ok Σ.
Proof. intros Σ (H1 & H2 & _ & H4 & _ & H6 & _). exact (conj H1 (conj H2 (conj H4 H6))). Qed.
Lemma geo_of_ART : forall Σ m, ART_A Σ m -> geo_ok Σ.
Proof. intros Σ m H. exact (geo_of_wf Σ (ART_wf Σ m H)). Qed.

Section G.
Variables (Σ : rtsA).
Hypothesis HG : geo_ok Σ.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma g_grant : forall b n, In (b, n) (startup_grants L) -> grant_ok L b n.
Proof.
  clear - HG. intros b n Hin. destruct HG as (HL & _). unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & G1 & _ & _ & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  unfold startup_grants in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; assumption.
Qed.

Lemma g_apart : forall i j g1 g2, (i < j)%nat -> nth_error (startup_grants L) i = Some g1 -> nth_error (startup_grants L) j = Some g2 ->
  apart (fst g1) (snd g1) (fst g2) (snd g2).
Proof.
  clear - HG. destruct HG as (HL & _). unfold layout_ok in HL. repeat match type of HL with _ /\ ?R => destruct HL as [_ HL] end. exact HL.
Qed.

Lemma g_prb : l_PRB L <= SB /\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000 /\ SB mod 2 ^ 16 = 0.
Proof. clear - HG. destruct HG as (HL & _). unfold layout_ok in HL. destruct HL as (_ & _ & _ & _ & _ & Hsb & Hsb2 & _). lia. Qed.

Lemma g_sp0 : sp_window_lo <= rtA_sp0 Σ <= sp_window_hi /\ rtA_sp0 Σ mod 16 = 0.
Proof. clear - HG. destruct HG as (HL & _). unfold layout_ok in HL. destruct HL as (H1 & H2 & _). unfold rtA_sp0. split; assumption. Qed.

Lemma g_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ 0x7fff7f800000 <= l_ACEIL L.
Proof. clear - HG. destruct g_sp0 as [[H1 H2] _]. unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, sp_window_lo, sp_window_hi in *. lia. Qed.

Lemma g_frame_in : forall f k, In (f, k) (frames Σ) ->
  (k = 5%nat \/ k = 0%nat \/ k = 4%nat \/ k = 1%nat \/ k = 3%nat \/ k = 2%nat) /\ l_FSB L + 0x9000 <= f /\ f + fs_size k <= l_FSB L + 0xb09000.
Proof.
  clear - HG. intros f k Hin. destruct HG as (_ & _ & _ & HF). destruct HF as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (f, k) Hin) as (Hk & (p & Hp & Hf & _)). cbn [fst snd] in *. split; [exact Hk|].
  unfold frame_addr, fs_size, fsz, NF in *. rewrite Z.shiftl_mul_pow2 by lia. subst f.
  destruct Hk as [Hk | [Hk | [Hk | [Hk | [Hk | Hk]]]]]; subst k.
  - change (Z.of_nat 5) with 5 in *. change (2 ^ (14 - 5)) with 512 in Hp. change (64 * 2 ^ 5) with 2048. lia.
  - change (Z.of_nat 2) with 2 in *. change (2 ^ (14 - 2)) with 4096 in Hp. change (64 * 2 ^ 2) with 256. lia.
  - change (Z.of_nat 4) with 4 in *. change (2 ^ (14 - 4)) with 1024 in Hp. change (64 * 2 ^ 4) with 1024. lia.
  - change (Z.of_nat 1) with 1 in *. change (2 ^ (14 - 1)) with 8192 in Hp. change (64 * 2 ^ 1) with 128. lia.
  - change (Z.of_nat 3) with 3 in *. change (2 ^ (14 - 3)) with 2048 in Hp. change (64 * 2 ^ 3) with 512. lia.
  - change (Z.of_nat 2) with 2 in *. change (2 ^ (14 - 2)) with 4096 in Hp. change (64 * 2 ^ 2) with 256. lia.
Qed.

Lemma g_frame : forall f k, In (f, k) (frames Σ) -> l_FSB L + 0x9000 <= f /\ f + fs_size k <= l_FSB L + 0xb09000 /\ 0 < fs_size k.
Proof.
  clear - HG. intros f k Hin. destruct (g_frame_in f k Hin) as (Hk & H1 & H2). split; [exact H1|]. split; [exact H2|].
  unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma g_slot_geo : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + r_muser (pr Σ c) /\ r_muser (pr Σ c) <= kUserCap
  /\ 32 <= ClassSize c /\ ClassSize c mod 32 = 0.
Proof.
  clear - HG. intros c i st Hc Hn. destruct HG as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
  pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
  unfold p_abeg, rb in *.
  assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
    replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia). repeat split; lia.
Qed.

Lemma g_slot_apart : forall c i c' i' st st', 1 <= c <= 31 -> 1 <= c' <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  nth_error (r_st (pr Σ c')) i' = Some st' -> (c <> c' \/ i <> i') ->
  p_abeg SB c i + ClassSize c <= p_abeg SB c' i' \/ p_abeg SB c' i' + ClassSize c' <= p_abeg SB c i.
Proof.
  clear - HG. intros c i c' i' st st' Hc Hc' Hn Hn' Hne.
  pose proof (g_slot_geo c i st Hc Hn) as (A1 & A2 & A3 & _). pose proof (g_slot_geo c' i' st' Hc' Hn') as (B1 & B2 & B3 & _).
  destruct (Z.eq_dec c c') as [<-|Hcc].
  - destruct Hne as [Hne|Hne]; [lia|]. unfold p_abeg. pose proof (ClassSize_range c Hc) as (Hcs & _).
    destruct (Nat.lt_ge_cases i i') as [Hl|Hl].
    + left. assert (Z.of_nat i * ClassSize c + ClassSize c <= Z.of_nat i' * ClassSize c).
      { replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
    + right. assert (Z.of_nat i' * ClassSize c + ClassSize c <= Z.of_nat i * ClassSize c).
      { replace (Z.of_nat i' * ClassSize c + ClassSize c) with ((Z.of_nat i' + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
  - unfold rb, kUserCap in *. lia.
Qed.

End G.

End GWIN.
