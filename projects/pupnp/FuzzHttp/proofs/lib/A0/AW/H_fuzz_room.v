(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HCount H_room_pot H_phdr H_pent_kit H_pparse_stmt H_pappend_stmt.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HCEIL : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation lbrm := (lb_remove (am_K_eqb FI AI)).
Local Notation psum := (psum FI AI).
Local Notation szok := (szok FI AI).
Variable N0 : Z.

Definition rinv (j B w kd N : Z) (LB : BL) : Prop :=
  szok LB
  /\ 3 * psum (lowf 16) LB <= 3 * j + 2 * w + 3 * kd
  /\ 3 * psum (stepf 17) LB <= 3 * j + 2 * w
  /\ 2 * psum (stepf 49) LB <= 2 * j + w
  /\ 3 * psum (ramp 24 65) LB <= 123 * j + 41 * w
  /\ (forall T, 97 <= T -> 2 * psum (ramp 81 T) LB <= 2 * j * (T - 81) + 5 * w)
  /\ 2 * psum (fun s => Z.max 0 (s - 81)) LB <= 2 * B + 5 * w
  /\ 2 * (N - N0) <= 2 * j + 2 * kd + w.

#[using="Type"] Lemma nsec1_cases : forall n, 0 <= n -> nsec1 n = 0 \/ (nsec1 n = 1 /\ 64513 <= n).
Proof.
  intros n Hn. unfold nsec1. destruct (Z.eq_dec (a0_cls n) 0) as [E|E].
  - right. split; [| exact (proj1 (a0_cls0_iff n Hn) E)]. apply Z.eqb_eq in E. rewrite E. reflexivity.
  - left. apply Z.eqb_neq in E. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma rinv_weaken : forall j B w kd N LB j' B' w', rinv j B w kd N LB -> j <= j' -> B <= B' -> w <= w' -> rinv j' B' w' kd N LB.
Proof.
  intros j B w kd N LB j' B' w' (SZ & C1 & C2 & C3 & C4 & C6 & CB & CN) Hj HB Hw.
  split; [exact SZ|]. repeat (split; [lia|]). split; [| split; [lia| lia]].
  intros T HT. specialize (C6 T HT). nia.
Qed.

#[using="Type"] Lemma rinv_cons_special : forall j B w kd N LB (b : BLK) N' sz, rinv j B w kd N LB -> blk_size b = sz -> 0 <= sz -> N <= N' <= N + 1 ->
  rinv (j + 1) (B + sz) w kd N' (b :: LB).
Proof.
  intros j B w kd N LB b N' sz (SZ & C1 & C2 & C3 & C4 & C6 & CB & CN) E S0 HN.
  split; [constructor; [rewrite E; exact S0| exact SZ]|]. rewrite !psum_cons, E.
  pose proof (lowf_range 16 sz). pose proof (stepf_range 17 sz). pose proof (stepf_range 49 sz). pose proof (ramp_range 24 65 sz ltac:(lia)).
  repeat (split; [lia|]). split; [| split; [lia| lia]].
  intros T HT. specialize (C6 T HT). rewrite psum_cons, E. pose proof (ramp_range 81 T sz ltac:(lia)). nia.
Qed.

#[using="Type"] Lemma rinv_repl_special : forall j B w kd N LB k (b : BLK) N' sz, rinv j B w kd N LB -> blk_size b = sz -> 0 <= sz -> N <= N' <= N + 1 ->
  rinv (j + 1) (B + sz) w kd N' (b :: lbrm k LB).
Proof.
  intros j B w kd N LB k b N' sz (SZ & C1 & C2 & C3 & C4 & C6 & CB & CN) E S0 HN.
  split; [constructor; [rewrite E; exact S0| apply szok_remove; exact SZ]|]. rewrite !psum_cons, E.
  pose proof (lowf_range 16 sz). pose proof (stepf_range 17 sz). pose proof (stepf_range 49 sz). pose proof (ramp_range 24 65 sz ltac:(lia)).
  pose proof (psum_remove_le FI AI (lowf 16) k LB (fun s => proj1 (lowf_range 16 s))).
  pose proof (psum_remove_le FI AI (stepf 17) k LB (fun s => proj1 (stepf_range 17 s))).
  pose proof (psum_remove_le FI AI (stepf 49) k LB (fun s => proj1 (stepf_range 49 s))).
  pose proof (psum_remove_le FI AI (ramp 24 65) k LB (fun s => proj1 (ramp_range 24 65 s ltac:(lia)))).
  pose proof (psum_remove_le FI AI (fun s => Z.max 0 (s - 81)) k LB (fun s => Z.le_max_l 0 (s - 81))).
  repeat (split; [lia|]). split; [| split; [lia| lia]].
  intros T HT. specialize (C6 T HT). rewrite psum_cons, E. pose proof (ramp_range 81 T sz ltac:(lia)).
  pose proof (psum_remove_le FI AI (ramp 81 T) k LB (fun s => proj1 (ramp_range 81 T s ltac:(lia)))). nia.
Qed.

#[using="Type"] Lemma rinv_realloc_gen : forall j B w kd N LB k A n (b : BLK) n' w' kd' N',
  rinv j B w kd N LB -> In (k, A, n) LB -> blk_size b = n' -> 0 <= n' ->
  3 * (lowf 16 n' - lowf 16 n) <= 2 * (w' - w) + 3 * (kd' - kd) ->
  3 * (stepf 17 n' - stepf 17 n) <= 2 * (w' - w) ->
  2 * (stepf 49 n' - stepf 49 n) <= w' - w ->
  3 * (ramp 24 65 n' - ramp 24 65 n) <= 41 * (w' - w) ->
  (forall T, 97 <= T -> 2 * (ramp 81 T n' - ramp 81 T n) <= 5 * (w' - w)) ->
  2 * (Z.max 0 (n' - 81) - Z.max 0 (n - 81)) <= 5 * (w' - w) ->
  2 * (N' - N) <= 2 * (kd' - kd) + (w' - w) ->
  rinv j B w' kd' N' (b :: lbrm k LB).
Proof.
  intros j B w kd N LB k A n b n' w' kd' N' (SZ & C1 & C2 & C3 & C4 & C6 & CB & CN) HIN E S0 D1 D2 D3 D4 D6 DB DN.
  pose proof (psum_remove FI AI (lowf 16) k LB (k, A, n) (fun s => proj1 (lowf_range 16 s)) HIN eq_refl) as R1.
  pose proof (psum_remove FI AI (stepf 17) k LB (k, A, n) (fun s => proj1 (stepf_range 17 s)) HIN eq_refl) as R2.
  pose proof (psum_remove FI AI (stepf 49) k LB (k, A, n) (fun s => proj1 (stepf_range 49 s)) HIN eq_refl) as R3.
  pose proof (psum_remove FI AI (ramp 24 65) k LB (k, A, n) (fun s => proj1 (ramp_range 24 65 s ltac:(lia))) HIN eq_refl) as R4.
  pose proof (psum_remove FI AI (fun s => Z.max 0 (s - 81)) k LB (k, A, n) (fun s => Z.le_max_l 0 (s - 81)) HIN eq_refl) as RB.
  cbn [blk_size snd] in R1, R2, R3, R4, RB.
  split; [constructor; [rewrite E; exact S0| apply szok_remove; exact SZ]|].
  rewrite !psum_cons, E.
  repeat (split; [lia|]). split; [| split; [lia| lia]].
  intros T HT. specialize (C6 T HT). specialize (D6 T HT). rewrite psum_cons, E.
  pose proof (psum_remove FI AI (ramp 81 T) k LB (k, A, n) (fun s => proj1 (ramp_range 81 T s ltac:(lia))) HIN eq_refl) as R6. cbn [blk_size snd] in R6. lia.
Qed.

#[using="Type"] Lemma rinv_hgrow : forall n N LB N' LB' j B w kd dw, hgrow FI AI n N LB N' LB' -> rinv j B w kd N LB -> 2 <= dw -> 2 * Z.max 5 n <= 5 * dw ->
  rinv j B (w + dw) kd N' LB'.
Proof.
  intros n N LB N' LB' j B w kd dw HG RI D2 DG.
  destruct HG as [N LB|N LB k k' A A' c c' len HIN LC LN CU NEED CG]; [apply (rinv_weaken j B w kd N LB j B (w + dw) RI); lia|].
  assert (S0 : 0 <= c + 1) by (destruct RI as (SZ & _); unfold H_room_pot.szok in SZ; rewrite Forall_forall in SZ; exact (SZ _ HIN)).
  pose proof (lowf_anti 16 (c + 1) (c' + 1) ltac:(lia)). pose proof (stepf_range 17 (c' + 1)). pose proof (stepf_range 17 (c + 1)).
  pose proof (stepf_range 49 (c' + 1)). pose proof (stepf_range 49 (c + 1)). pose proof (ramp_lip 24 65 (c + 1) (c' + 1) ltac:(lia) ltac:(lia)).
  pose proof (nsec1_range (c' + 1)) as NR.
  apply (rinv_realloc_gen j B w kd N LB k A (c + 1) (k', A', c' + 1) (c' + 1) (w + dw) kd (N + nsec1 (c' + 1)) RI HIN eq_refl); try lia.
  intros T HT. pose proof (ramp_lip 81 T (c + 1) (c' + 1) ltac:(lia) ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma rinv_newline : forall j B w kd N (LB : BL) d tlz l nc vc (bd bv bn bh : BLK),
  rinv j B w kd N LB -> 1 <= tlz -> 1 <= l -> tlz + l + 1 <= d -> tlz <= nc <= tlz + 5 -> l <= vc <= l + 5 ->
  blk_size bd = 24 -> blk_size bv = vc + 1 -> blk_size bn = nc + 1 -> blk_size bh = 88 ->
  rinv j B (w + d) kd (N + nsec1 (nc + 1) + nsec1 (vc + 1)) (bd :: bv :: bn :: bh :: LB).
Proof.
  intros j B w kd N LB d tlz l nc vc bd bv bn bh (SZ & C1 & C2 & C3 & C4 & C6 & CB & CN) T1 L1 DD NC VC E1 E2 E3 E4.
  split; [repeat (constructor; [lia|]); exact SZ|]. rewrite !psum_cons, E1, E2, E3, E4.
  change (lowf 16 24) with 0. change (lowf 16 88) with 0. change (stepf 17 24) with 1. change (stepf 17 88) with 1. change (stepf 49 24) with 0. change (stepf 49 88) with 1.
  change (ramp 24 65 24) with 0. change (ramp 24 65 88) with 41. change (Z.max 0 (24 - 81)) with 0. change (Z.max 0 (88 - 81)) with 7.
  pose proof (lowf_range 16 (vc + 1)). pose proof (lowf_range 16 (nc + 1)).
  destruct (stepf_cases 17 (vc + 1)) as [[-> ?]|[-> ?]]; destruct (stepf_cases 17 (nc + 1)) as [[-> ?]|[-> ?]];
  destruct (stepf_cases 49 (vc + 1)) as [[-> ?]|[-> ?]]; destruct (stepf_cases 49 (nc + 1)) as [[-> ?]|[-> ?]]; try (exfalso; lia);
  (pose proof (ramp_le 24 65 (vc + 1) ltac:(lia)); pose proof (ramp_le 24 65 (nc + 1) ltac:(lia));
   destruct (nsec1_cases (nc + 1) ltac:(lia)) as [-> |[-> ?]]; destruct (nsec1_cases (vc + 1) ltac:(lia)) as [-> |[-> ?]]; try (exfalso; lia);
   (repeat (split; [lia|])); (split; [| split; [lia| lia]]);
   intros T HT; specialize (C6 T HT); rewrite !psum_cons, E1, E2, E3, E4;
   pose proof (ramp_le 81 T (vc + 1) ltac:(lia)); pose proof (ramp_le 81 T (nc + 1) ltac:(lia)); pose proof (ramp_le 81 T 88 ltac:(lia)); pose proof (ramp_le 81 T 24 ltac:(lia)); lia).
Qed.

#[using="Type"] Lemma rinv_hline : forall d N LB N' LB' j B w kd, hline FI AI d N LB N' LB' -> rinv j B w kd N LB -> rinv j B (w + d) kd N' LB'.
Proof.
  intros d N LB N' LB' j B w kd HL RI.
  destruct HL as [N LB d tlz l kh kn kv kd0 H NA nc VA vc D T1 L1 D1 D2 NC VC|N LB d l N1 LB1 N2 LB2 D2 [L0 LD] G1 G2].
  - exact (rinv_newline j B w kd N LB d tlz l nc vc (kd0, D, 24) (kv, VA, vc + 1) (kn, NA, nc + 1) (kh, H, 88) RI T1 L1 D2 NC VC eq_refl eq_refl eq_refl eq_refl).
  - pose proof (rinv_hgrow 2 N LB N1 LB1 j B w kd 2 G1 RI ltac:(lia) ltac:(lia)) as R1.
    destruct (Z.eq_dec l 0) as [-> |LN].
    +
      destruct G2 as [N1 LB1|N1 LB1 k k' A A' c c' len HIN LC LN' CU NEED CG]; [| exfalso; lia].
      apply (rinv_weaken j B (w + 2) kd N1 LB1 j B (w + d) R1); lia.
    + pose proof (rinv_hgrow l N1 LB1 N2 LB2 j B (w + 2) kd (d - 2) G2 R1 ltac:(lia) ltac:(lia)) as R2.
      replace (w + d) with (w + 2 + (d - 2)) by lia. exact R2.
Qed.
#[using="Type"] Lemma rinv_hlines : forall d N LB N' LB', hlines FI AI d N LB N' LB' -> forall j B w kd, rinv j B w kd N LB -> rinv j B (w + d) kd N' LB'.
Proof.
  intros d N LB N' LB' H. induction H as [N LB|d1 d2 N LB N1 LB1 N2 LB2 HL HLS IH]; intros j B w kd RI; [rewrite Z.add_0_r; exact RI|].
  replace (w + (d1 + d2)) with (w + d1 + d2) by lia. exact (IH j B (w + d1) kd (rinv_hline d1 N LB N1 LB1 j B w kd HL RI)).
Qed.

#[using="Type"] Lemma rinv_part2 : forall j B w kd N (LB : BL) d tlz nc (bn bh : BLK),
  rinv j B w kd N LB -> 1 <= tlz -> tlz + 1 <= d -> tlz <= nc <= tlz + 5 -> blk_size bn = nc + 1 -> blk_size bh = 88 ->
  rinv (j + 1) (B + 88) (w + d) kd (N + nsec1 (nc + 1)) (bn :: bh :: LB).
Proof.
  intros j B w kd N LB d tlz nc bn bh RI T1 D1 NC E3 E4.
  pose proof (rinv_cons_special j B w kd N LB bh N 88 RI E4 ltac:(lia) ltac:(lia)) as (SZ & C1 & C2 & C3 & C4 & C6 & CB & CN).
  split; [constructor; [rewrite E3; lia| exact SZ]|]. rewrite !psum_cons in *. rewrite E3, E4 in *.
  pose proof (lowf_range 16 (nc + 1)). pose proof (ramp_le 24 65 (nc + 1) ltac:(lia)).
  destruct (stepf_cases 17 (nc + 1)) as [[-> ?]|[-> ?]]; destruct (stepf_cases 49 (nc + 1)) as [[-> ?]|[-> ?]]; try (exfalso; lia);
  (destruct (nsec1_cases (nc + 1) ltac:(lia)) as [-> |[-> ?]]; try (exfalso; lia); (repeat (split; [lia|])); (split; [| split; [lia| lia]]);
   intros T HT; specialize (C6 T HT); rewrite !psum_cons in *; rewrite E3, E4 in *; pose proof (ramp_le 81 T (nc + 1) ltac:(lia)); lia).
Qed.
#[using="Type"] Lemma rinv_part3 : forall j B w kd N (LB : BL) d tlz l nc vc (bv bn bh : BLK),
  rinv j B w kd N LB -> 1 <= tlz -> 1 <= l -> tlz + l + 1 <= d -> tlz <= nc <= tlz + 5 -> l <= vc <= l + 5 ->
  blk_size bv = vc + 1 -> blk_size bn = nc + 1 -> blk_size bh = 88 ->
  rinv (j + 1) (B + 88) (w + d) kd (N + nsec1 (nc + 1) + nsec1 (vc + 1)) (bv :: bn :: bh :: LB).
Proof.
  intros j B w kd N LB d tlz l nc vc bv bn bh RI T1 L1 D2 NC VC E2 E3 E4.
  pose proof (rinv_cons_special j B w kd N LB bh N 88 RI E4 ltac:(lia) ltac:(lia)) as (SZ & C1 & C2 & C3 & C4 & C6 & CB & CN).
  split; [constructor; [rewrite E2; lia| constructor; [rewrite E3; lia| exact SZ]]|]. rewrite !psum_cons in *. rewrite E2, E3, E4 in *.
  pose proof (lowf_range 16 (vc + 1)). pose proof (lowf_range 16 (nc + 1)).
  destruct (stepf_cases 17 (vc + 1)) as [[-> ?]|[-> ?]]; destruct (stepf_cases 17 (nc + 1)) as [[-> ?]|[-> ?]];
  destruct (stepf_cases 49 (vc + 1)) as [[-> ?]|[-> ?]]; destruct (stepf_cases 49 (nc + 1)) as [[-> ?]|[-> ?]]; try (exfalso; lia);
  (pose proof (ramp_le 24 65 (vc + 1) ltac:(lia)); pose proof (ramp_le 24 65 (nc + 1) ltac:(lia));
   destruct (nsec1_cases (nc + 1) ltac:(lia)) as [-> |[-> ?]]; destruct (nsec1_cases (vc + 1) ltac:(lia)) as [-> |[-> ?]]; try (exfalso; lia);
   (repeat (split; [lia|])); (split; [| split; [lia| lia]]);
   intros T HT; specialize (C6 T HT); rewrite !psum_cons in *; rewrite E2, E3, E4 in *;
   pose proof (ramp_le 81 T (vc + 1) ltac:(lia)); pose proof (ramp_le 81 T (nc + 1) ltac:(lia)); lia).
Qed.
#[using="Type"] Lemma rinv_hpart : forall d N LB N' LB' j B w kd, hpart FI AI d N LB N' LB' -> rinv j B w kd N LB -> rinv (j + 1) (B + 88) (w + d) kd N' LB'.
Proof.
  intros d N LB N' LB' j B w kd HP RI.
  destruct HP as [N LB d D0|N LB d kh H D2|N LB d tlz kh kn H NA nc T1 D1 NC|N LB d tlz l kh kn kv H NA nc VA vc T1 L1 D1 D2 NC VC|N LB d N1 LB1 D2 G1].
  - apply (rinv_weaken j B w kd N LB _ _ _ RI); lia.
  - pose proof (rinv_cons_special j B w kd N LB (kh, H, 88) N 88 RI eq_refl ltac:(lia) ltac:(lia)) as R. apply (rinv_weaken _ _ _ _ _ _ _ _ _ R); lia.
  - exact (rinv_part2 j B w kd N LB d tlz nc (kn, NA, nc + 1) (kh, H, 88) RI T1 D1 NC eq_refl eq_refl).
  - exact (rinv_part3 j B w kd N LB d tlz l nc vc (kv, VA, vc + 1) (kn, NA, nc + 1) (kh, H, 88) RI T1 L1 D2 NC VC eq_refl eq_refl eq_refl).
  - pose proof (rinv_hgrow 2 N LB N1 LB1 j B w kd d G1 RI D2 ltac:(lia)) as R. apply (rinv_weaken _ _ _ _ _ _ _ _ _ R); lia.
Qed.

#[using="Type"] Lemma rinv_edel1 : forall N LB N' LB' j B w kd, edel1 FI AI N LB N' LB' -> rinv j B w kd N LB -> rinv j B w (kd + 1) N' LB'.
Proof.
  intros N LB N' LB' j B w kd HD RI.
  destruct HD as [N LB k k' A A' c c' HIN CC].
  pose proof (lowf_range 16 (c' + 1)). pose proof (lowf_range 16 (c + 1)). pose proof (stepf_mono 17 (c' + 1) (c + 1) ltac:(lia)). pose proof (stepf_mono 49 (c' + 1) (c + 1) ltac:(lia)).
  pose proof (ramp_mono 24 65 (c' + 1) (c + 1) ltac:(lia)). pose proof (nsec1_range (c' + 1)) as NR.
  apply (rinv_realloc_gen j B w kd N LB k A (c + 1) (k', A', c' + 1) (c' + 1) w (kd + 1) (N + nsec1 (c' + 1)) RI HIN eq_refl); try lia.
  intros T HT. pose proof (ramp_mono 81 T (c' + 1) (c + 1) ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma rinv_edels : forall k N LB N' LB', edels FI AI k N LB N' LB' -> forall j B w kd, rinv j B w kd N LB -> rinv j B w (kd + k) N' LB'.
Proof.
  intros k N LB N' LB' H. induction H as [N LB|k N LB N1 LB1 N2 LB2 HD HDS IH]; intros j B w kd RI; [rewrite Z.add_0_r; exact RI|].
  replace (kd + (k + 1)) with (kd + 1 + k) by lia. exact (IH j B w (kd + 1) (rinv_edel1 N LB N1 LB1 j B w kd HD RI)).
Qed.

#[using="Type"] Lemma rinv_pfirst : forall N LB N' LB' j B w kd, pfirst FI AI N LB N' LB' -> rinv j B w kd N LB -> rinv (j + 1) (B + (2^26 + 6)) w kd N' LB'.
Proof.
  intros N LB N' LB' j B w kd HP RI. destruct HP as [N LB|N LB k A n Hn|N LB k k' A n Hn].
  - apply (rinv_weaken j B w kd N LB _ _ _ RI); lia.
  - pose proof (nsec1_range n). pose proof (rinv_cons_special j B w kd N LB (k, A, n) (N + nsec1 n) n RI eq_refl ltac:(lia) ltac:(lia)) as R. apply (rinv_weaken _ _ _ _ _ _ _ _ _ R); lia.
  - pose proof (nsec1_range n). pose proof (rinv_repl_special j B w kd N LB k (k', A, n) (N + nsec1 n) n RI eq_refl ltac:(lia) ltac:(lia)) as R. apply (rinv_weaken _ _ _ _ _ _ _ _ _ R); lia.
Qed.

#[using="Type"] Lemma rinv_pappended : forall (s : PS) (LB : BL) (t : pstA FI AI) n src (s1 : PS) (LB1 : BL) (t1 : pstA FI AI) j B w kd,
  pappended FI AI s LB t n src s1 LB1 t1 -> rinv j B w kd (am_nsec FI AI s) LB -> 0 <= pa_cap FI AI t -> 0 <= n ->
  rinv (j + 1) (B + (pa_cap FI AI t + n + 6)) w kd (am_nsec FI AI s1) LB1.
Proof.
  intros s LB t n src s1 LB1 t1 j B w kd (A' & cap' & ok' & bs' & _ & ALT & CAPR & _) RI C0 N0'.
  destruct ALT as [(_ & -> & _ & _ & ->)|(k' & _ & -> & -> & _ & CG)]; [apply (rinv_weaken j B w kd _ LB _ _ _ RI); lia|].
  pose proof (nsec1_range (cap' + 1)).
  destruct (pa_okm FI AI t) as [k|]; cbn [lb_keepA].
  - pose proof (rinv_repl_special j B w kd _ LB k (k', A', cap' + 1) (am_nsec FI AI s + nsec1 (cap' + 1)) (cap' + 1) RI eq_refl ltac:(lia) ltac:(lia)) as R. apply (rinv_weaken _ _ _ _ _ _ _ _ _ R); lia.
  - pose proof (rinv_cons_special j B w kd _ LB (k', A', cap' + 1) (am_nsec FI AI s + nsec1 (cap' + 1)) (cap' + 1) RI eq_refl ltac:(lia) ltac:(lia)) as R. apply (rinv_weaken _ _ _ _ _ _ _ _ _ R); lia.
Qed.

#[using="Type"] Lemma psum_le_bytes : forall (LB : BL), szok LB -> psum (fun s => Z.max 0 (s - 81)) LB <= lb_bytes FI AI LB.
Proof.
  induction LB as [|b LB IH]; intros SZ; [cbn; lia|]. apply Forall_cons_iff in SZ. destruct SZ as [S0 SZ]. specialize (IH SZ).
  rewrite psum_cons. cbn [lb_bytes fold_right]. fold (lb_bytes FI AI LB). lia.
Qed.
#[using="Type"] Lemma rinv_init : forall (LB : BL), szok LB -> Z.of_nat (length LB) <= 2 -> rinv 2 (lb_bytes FI AI LB) 0 0 N0 LB.
Proof.
  intros LB SZ L2.
  pose proof (psum_le_len FI AI (lowf 16) LB 1 (fun s => proj2 (lowf_range 16 s))). pose proof (psum_le_len FI AI (stepf 17) LB 1 (fun s => proj2 (stepf_range 17 s))).
  pose proof (psum_le_len FI AI (stepf 49) LB 1 (fun s => proj2 (stepf_range 49 s))). pose proof (psum_le_len FI AI (ramp 24 65) LB 41 (fun s => proj2 (ramp_range 24 65 s ltac:(lia)))).
  pose proof (psum_le_bytes LB SZ).
  split; [exact SZ|]. repeat (split; [lia|]). split; [| split; [lia| lia]].
  intros T HT. pose proof (psum_le_len FI AI (ramp 81 T) LB (T - 81) (fun s => proj2 (ramp_range 81 T s ltac:(lia)))). nia.
Qed.

Definition RW : Z := 2^26.
Definition RKD : Z := 128005.
Definition RBMAX : Z := 2^27 + (2^26 + 6) + (2^26 + 6) + 88.
#[using="Type"] Lemma cap_close : forall X num den csz cap, 0 < den -> 0 <= csz -> den * X <= num -> ((num / den + 1) * csz <=? cap) = true -> (X + 1) * csz <= cap.
Proof. intros X num den csz cap Hd Hc HX HT. apply Z.leb_le in HT. assert (X <= num / den) by (apply Z.div_le_lower_bound; lia). nia. Qed.
Definition rtab (c : Z) : bool := (97 <=? a0_nmin c) && (((10 * (a0_nmin c - 81) + 5 * RW) / (2 * (a0_nmin c - 81)) + 1) * a0_csz c <=? A0_CAP c).
#[using="Type"] Lemma rtab_ok : forall c, 6 <= c <= 30 -> rtab c = true.
Proof. intros c Hc. exact (a0_chk_ok rtab 25 6 ltac:(vm_compute; reflexivity) c ltac:(lia)). Qed.

#[using="Type"] Lemma rinv_budget_nc : forall j B w kd N (LB : BL) (s' : PS) n, rinv j B w kd N LB -> j <= 5 -> B <= RBMAX -> 0 <= w <= RW -> 0 <= kd <= RKD ->
  0 <= n <= A0_MAXREQ -> (a0_cls n = 0 -> am_nsec FI AI s' + 1 <= A0_NSEC_MAX) -> am_budget FI AI s' LB n.
Proof.
  intros j B w kd N LB s' n RI Hj HB Hw Hk Hn HCNT.
  apply (rinv_weaken j B w kd N LB 5 RBMAX RW) in RI; [| lia| lia| lia]. destruct RI as (SZ & C1 & C2 & C3 & C4 & C6 & CB & CN).
  assert (SZB : forall b, In b LB -> 0 <= blk_size b) by (unfold H_room_pot.szok in SZ; rewrite Forall_forall in SZ; exact SZ).
  assert (NM : forall b c, In b LB -> a0_cls (blk_size b) = c -> c <> 0 -> c <> 1 -> a0_nmin c <= blk_size b).
  { intros b c Hb E C0 C1'. subst c. apply a0_nmin_le; [| exact C0]. destruct (Z.eq_dec (blk_size b) 0) as [Z0|NZ]; [exfalso; apply C1'; rewrite Z0; reflexivity| specialize (SZB b Hb); lia]. }
  unfold am_budget, RW, RKD, RBMAX, A0_MAXREQ in *. pose proof (a0_cls_range n ltac:(lia)) as CR. destruct (a0_cls_low n ltac:(lia)) as (_ & N5 & _).
  destruct (a0_cls n =? 0) eqn:E0.
  -
    pose proof (lbc_le_psumM FI AI (ramp 81 64513) 64432 0 LB ltac:(lia) (fun s => proj1 (ramp_range 81 64513 s ltac:(lia)))
                  ltac:(intros b Hb E; rewrite ramp_top; [lia| lia| exact (proj1 (a0_cls0_iff _ (SZB b Hb)) E)])) as L0.
    pose proof (bytes0_le_psum FI AI 81 LB ltac:(lia) SZ) as BY. specialize (C6 64513 ltac:(lia)).
    unfold A0_SEC_CNT, A0_SEC_BYTES. split; [lia|]. split; [lia|]. apply HCNT. apply Z.eqb_eq. exact E0.
  - apply Z.eqb_neq in E0. set (c := a0_cls n) in *.
    destruct (Z_le_gt_dec 6 c) as [C6'|CL].
    + pose proof (rtab_ok c ltac:(lia)) as RT. unfold rtab in RT. apply andb_true_iff in RT. destruct RT as [T97 RT]. apply Z.leb_le in T97.
      pose proof (lbc_le_psumM FI AI (ramp 81 (a0_nmin c)) (a0_nmin c - 81) c LB ltac:(lia) (fun s => proj1 (ramp_range 81 (a0_nmin c) s ltac:(lia)))
                    ltac:(intros b Hb E; rewrite ramp_top; [lia| lia| apply (NM b c Hb E); lia])) as LC.
      specialize (C6 (a0_nmin c) T97).
      assert (CS : 0 <= a0_csz c) by (pose proof (a0_chk_ok (fun c => 0 <=? a0_csz c) 25 6 ltac:(vm_compute; reflexivity) c ltac:(lia)) as X; apply Z.leb_le in X; exact X).
      apply (cap_close (lbc FI AI LB c) (10 * (a0_nmin c - 81) + 5 * 2^26) (2 * (a0_nmin c - 81)) (a0_csz c) (A0_CAP c)); [lia| exact CS| nia| exact RT].
    + assert (CC : c = 1 \/ c = 2 \/ c = 3 \/ c = 4) by lia. destruct CC as [E|[E|[E|E]]]; rewrite E in *.
      * pose proof (lbc_le_psum FI AI (lowf 16) 1 LB (fun s => proj1 (lowf_range 16 s))
                      ltac:(intros b Hb Eb; destruct (lowf_cases 16 (blk_size b)) as [[_ G]|[-> _]]; [exfalso; pose proof (proj1 (a0_cls_low _ (SZB b Hb)) Eb); lia| lia])) as L1.
        apply (cap_close _ (15 + 2 * 2^26 + 3 * 128005) 3 _ _); [lia| vm_compute; discriminate| lia| vm_compute; reflexivity].
      * pose proof (lbc_le_psum FI AI (stepf 17) 2 LB (fun s => proj1 (stepf_range 17 s))
                      ltac:(intros b Hb Eb; pose proof (NM b 2 Hb Eb ltac:(lia) ltac:(lia)) as G; change (a0_nmin 2) with 17 in G; destruct (stepf_cases 17 (blk_size b)) as [[_ G']|[-> _]]; lia)) as L2.
        apply (cap_close _ (15 + 2 * 2^26) 3 _ _); [lia| vm_compute; discriminate| lia| vm_compute; reflexivity].
      * pose proof (lbc_le_psum FI AI (stepf 49) 3 LB (fun s => proj1 (stepf_range 49 s))
                      ltac:(intros b Hb Eb; pose proof (NM b 3 Hb Eb ltac:(lia) ltac:(lia)) as G; change (a0_nmin 3) with 49 in G; destruct (stepf_cases 49 (blk_size b)) as [[_ G']|[-> _]]; lia)) as L3.
        apply (cap_close _ (10 + 2^26) 2 _ _); [lia| vm_compute; discriminate| lia| vm_compute; reflexivity].
      * pose proof (lbc_le_psumM FI AI (ramp 24 65) 41 4 LB ltac:(lia) (fun s => proj1 (ramp_range 24 65 s ltac:(lia)))
                      ltac:(intros b Hb Eb; pose proof (NM b 4 Hb Eb ltac:(lia) ltac:(lia)) as G; change (a0_nmin 4) with 65 in G; rewrite ramp_top; lia)) as L4.
        apply (cap_close _ (615 + 41 * 2^26) 123 _ _); [lia| vm_compute; discriminate| lia| vm_compute; reflexivity].
Qed.

#[using="Type"] Lemma hpart_nonneg : forall d N LB N' LB', hpart FI AI d N LB N' LB' -> 0 <= d.
Proof. intros d N LB N' LB' H. destruct H; lia. Qed.

End W.

Definition FZ_NSEC_H : Z := 13552000.

Section R.
Context {HCEIL : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Local Notation K := (am_K FI AI).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).

#[using="Type"] Lemma pfirst_nsec : forall N (LB : BL) N' (LB' : BL), pfirst FI AI N LB N' LB' -> N <= N' <= N + 1.
Proof. intros N LB N' LB' H. destruct H as [N LB|N LB k A n Hn|N LB k k' A n Hn]; [lia| |]; pose proof (nsec1_range n); lia. Qed.
#[using="Type"] Lemma edels_nsec : forall k N (LB : BL) N' (LB' : BL), edels FI AI k N LB N' LB' -> 0 <= k /\ N <= N' <= N + k.
Proof.
  intros k N LB N' LB' H. induction H as [N LB|k N LB N1 LB1 N2 LB2 HD HDS IH]; [lia|].
  destruct HD as [N LB k0 k' A A' c c' HIN CC]. pose proof (nsec1_range (c' + 1)). lia.
Qed.

#[using="Type"] Lemma fuzz_room : forall (s : PS) (LB : BL) m (t0 : pstA FI AI) (c M : Z) src,
  RHEAP_A FI AI s LB m -> am_nsec FI AI s + FZ_NSEC_H <= A0_NSEC_MAX -> Z.of_nat (length LB) <= 2 -> lb_bytes FI AI LB <= 2^27 -> 0 <= c <= 2^26 -> 0 <= M <= RKD ->
  pa_cap FI AI t0 = 0 ->
  am_budget_le FI AI s LB (c + 6)
  /\ forall (sa : PS) (LBa : BL) (ta : pstA FI AI), pappended FI AI s LB t0 c src sa LBa ta -> pbud FI AI c M 0 sa LBa.
Proof.
  intros s LB m t0 c M src HR P2 L2 BY Hc HM CAP0. set (N0 := am_nsec FI AI s) in *.
  assert (SZ : H_room_pot.szok FI AI LB) by (apply Forall_forall; intros b Hb; destruct (am_block_range FI AI _ _ _ _ HR Hb) as (_ & _ & R & _); exact R).
  pose proof (rinv_init FI AI N0 LB SZ L2) as R0.
  assert (BUDG : forall j B w kd N (LBx : BL) (sx : PS) n, rinv FI AI N0 j B w kd N LBx -> j <= 5 -> B <= RBMAX -> 0 <= w <= c -> 0 <= kd <= M -> am_nsec FI AI sx = N -> 0 <= n <= A0_MAXREQ ->
                   N + 1 <= N0 + FZ_NSEC_H -> am_budget FI AI sx LBx n).
  { intros j B w kd N LBx sx n RI Hj HB Hw Hk E Hn HCN. apply (rinv_budget_nc FI AI N0 j B w kd N LBx sx n RI Hj HB); [unfold RW; lia| lia| exact Hn| intros _; rewrite E; lia]. }
  unfold RBMAX, RKD, FZ_NSEC_H, CG_A, CG_B, CG_SL in *.
  split; [intros n Hn; apply (BUDG 2 _ 0 0 N0 LB s n R0); unfold A0_MAXREQ; try reflexivity; lia|].
  intros sa LBa ta PA.
  pose proof (rinv_pappended FI AI N0 s LB t0 c src sa LBa ta 2 _ 0 0 PA R0 ltac:(lia) ltac:(lia)) as R1. rewrite CAP0 in R1.
  assert (NA : N0 <= am_nsec FI AI sa <= N0 + 1).
  { destruct PA as (A' & cap' & ok' & bs' & _ & ALT & _). destruct ALT as [(_ & _ & _ & _ & E)|(k' & _ & _ & E & _)]; [fold N0 in E; lia| pose proof (nsec1_range (cap' + 1)); fold N0 in E; lia]. }
  unfold pbud. split; [intros n Hn; apply (BUDG _ _ 0 0 _ LBa sa n R1); unfold A0_MAXREQ; try reflexivity; lia|].
  intros N1 LB1 s1 PF E1. pose proof (pfirst_nsec _ _ _ _ PF) as NF. pose proof (rinv_pfirst FI AI N0 _ _ _ _ _ _ 0 0 PF R1) as R2N. pose proof R2N as R2. rewrite <- E1 in R2.
  split.
  - unfold hbud. intros N' LB' s' n (d1 & d2 & Nx & LBx & HLS & HPT & DS & GD) E' Hn.
    pose proof (hlines_nonneg FI AI _ _ _ _ _ HLS). pose proof (hpart_nonneg FI AI _ _ _ _ _ HPT).
    pose proof (rinv_hpart FI AI N0 d2 _ _ _ _ _ _ _ _ HPT (rinv_hlines FI AI N0 d1 _ _ _ _ HLS _ _ _ _ R2)) as R4.
    apply (BUDG _ _ _ 0 _ LB' s' n R4); try lia. rewrite E1 in GD. unfold CG_A, CG_B, CG_SL in GD. lia.
  - intros d N2 LB2 s2 G2 HLS2 Dd E2 G20 CPL. unfold ebud. intros k N3 LB3 s3 EDS Kk E3. unfold hbud. intros N' LB' s' n (d1 & d2 & Nx & LBx & HLS & HPT & DS & GD) E' Hn.
    pose proof (hlines_nonneg FI AI _ _ _ _ _ HLS). pose proof (hpart_nonneg FI AI _ _ _ _ _ HPT).
    pose proof (rinv_hlines FI AI N0 d _ _ _ _ HLS2 _ _ _ _ R2N) as R3. rewrite <- E2 in R3.
    pose proof (edels_nsec _ _ _ _ _ EDS) as [_ NE]. rewrite E2 in NE.
    pose proof (rinv_edels FI AI N0 k _ _ _ _ EDS _ _ _ _ R3) as R5. rewrite <- E3 in R5.
    pose proof (rinv_hpart FI AI N0 d2 _ _ _ _ _ _ _ _ HPT (rinv_hlines FI AI N0 d1 _ _ _ _ HLS _ _ _ _ R5)) as R6.
    apply (BUDG _ _ _ _ _ LB' s' n R6); try lia. rewrite E3 in GD. unfold CG_A, CG_B, CG_SL in GD, CPL. lia.
Qed.
End R.
