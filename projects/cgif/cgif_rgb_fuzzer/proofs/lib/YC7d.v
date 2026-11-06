(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z
YC53.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b.
Lemma arr8_setz_mem : forall (m m' : word -> option byte) base l h v,
arr8 trasegs m base l -> 0 <= h < zlen l -> 0 <= v < 256 ->
mbyte trasegs m' (base + h) = Some (Z_to_bv 8 v) ->
(forall j, 0 <= j < zlen l -> j <> h -> mbyte trasegs m' (base + j) = mbyte trasegs m (base + j)) ->
arr8 trasegs m' base (setz l h v).
Proof.
intros m m' base l h v Ha Hh Hv Hb Hk j Hjl. rewrite length_setz in Hjl.
assert (Hz : 0 <= Z.of_nat j < zlen l) by (unfold zlen; lia).
destruct (Z.eq_dec (Z.of_nat j) h) as [Ej | Ej].
- subst h. pose proof (getz_setz_same l (Z.of_nat j) v Hh) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G. split; [exact Hb | exact Hv].
- pose proof (getz_setz_other l h (Z.of_nat j) v ltac:(lia) ltac:(lia) Ej) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G.
rewrite (Hk (Z.of_nat j) Hz Ej). exact (Ha j ltac:(unfold zlen in Hz; lia)).
Qed.
Lemma arr32_setz_mem : forall (m m' : word -> option byte) base l h v,
arr32 trasegs m base l -> 0 <= h < zlen l -> 0 <= v < 2 ^ 32 ->
val_mem trasegs m' (base + 4 * h) 4 v ->
(forall j, 0 <= j < zlen l -> j <> h -> forall k, 0 <= k < 4 -> mbyte trasegs m' (base + 4 * j + k) = mbyte trasegs m (base + 4 * j + k)) ->
arr32 trasegs m' base (setz l h v).
Proof.
intros m m' base l h v Ha Hh Hv Hb Hk j Hjl. rewrite length_setz in Hjl.
assert (Hz : 0 <= Z.of_nat j < zlen l) by (unfold zlen; lia).
destruct (Z.eq_dec (Z.of_nat j) h) as [Ej | Ej].
- subst h. pose proof (getz_setz_same l (Z.of_nat j) v Hh) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G. split; [exact Hb | exact Hv].
- pose proof (getz_setz_other l h (Z.of_nat j) v ltac:(lia) ltac:(lia) Ej) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G.
destruct (Ha j ltac:(unfold zlen in Hz; lia)) as [A1 A2]. split; [|exact A2].
intros kk Hkk. rewrite (Hk (Z.of_nat j) Hz Ej (Z.of_nat kk) ltac:(lia)). exact (A1 kk Hkk).
Qed.
Lemma arr8_set_col_mem : forall (m m' : word -> option byte) base l h (c : colour),
arr8 trasegs m base l -> 0 <= h -> 3 * h + 3 <= zlen l -> colour_ok c ->
mbyte trasegs m' (base + 3 * h) = Some (Z_to_bv 8 (cR c)) -> mbyte trasegs m' (base + 3 * h + 1) = Some (Z_to_bv 8 (cG c)) ->
mbyte trasegs m' (base + 3 * h + 2) = Some (Z_to_bv 8 (cB c)) ->
(forall j, 0 <= j < zlen l -> ~ (3 * h <= j < 3 * h + 3) -> mbyte trasegs m' (base + j) = mbyte trasegs m (base + j)) ->
arr8 trasegs m' base (set_col l h c).
Proof.
intros m m' base l h c Ha Hh Hlen (Rr & Rg & Rb) B0 B1 B2 Hk j Hjl.
assert (Hjl' : (j < length l)%nat) by (pose proof (zlen_set_col l h c) as X; unfold zlen in X; lia).
assert (Hz : 0 <= Z.of_nat j < zlen l) by (unfold zlen; lia).
pose proof (getz_set_col l h c (Z.of_nat j) Hh ltac:(lia) Hlen) as G. unfold getz in G. rewrite Nat2Z.id in G. rewrite G.
destruct (Z.eqb_spec (Z.of_nat j) (3 * h)) as [E0|N0]; [rewrite E0; split; [exact B0 | exact Rr]|].
destruct (Z.eqb_spec (Z.of_nat j) (3 * h + 1)) as [E1|N1]; [rewrite E1; split; [rewrite Z.add_assoc; exact B1 | exact Rg]|].
destruct (Z.eqb_spec (Z.of_nat j) (3 * h + 2)) as [E2|N2]; [rewrite E2; split; [rewrite Z.add_assoc; exact B2 | exact Rb]|].
rewrite (Hk (Z.of_nat j) Hz ltac:(lia)). exact (Ha j Hjl').
Qed.
Lemma obj_at_cht_set_cnt : forall (m m' : word -> option byte) c v0 v1 v2 v3 v4 v5 v6 v5',
obj_at trasegs m c LAY_Cht [v0; v1; v2; v3; v4; v5; v6] ->
(forall a, c <= a < c + 48 -> ~ (c + 40 <= a < c + 44) -> mbyte trasegs m' a = mbyte trasegs m a) ->
val_mem trasegs m' (c + 40) 4 v5' -> 0 <= v5' < 2 ^ 32 ->
obj_at trasegs m' c LAY_Cht [v0; v1; v2; v3; v4; v5'; v6].
Proof.
intros m m' c v0 v1 v2 v3 v4 v5 v6 v5' Hobj KEEP Hv Hr.
cbn [obj_at LAY_Cht] in Hobj |- *. unfold field_ok in *. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hobj |- *.
destruct Hobj as ([A0 B0] & [A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6] & _).
assert (K : forall off n v, val_mem trasegs m (c + off) n v -> 0 <= off -> (off + Z.of_nat n <= 40 \/ 44 <= off) -> off + Z.of_nat n <= 48 -> val_mem trasegs m' (c + off) n v).
{ intros off n v Hvm H0 H1 H2 kk Hkk. rewrite <- (Hvm kk Hkk). apply KEEP; lia. }
split; [split; [apply K; [exact A0 | lia | cbn; lia | cbn; lia] | exact B0]|].
split; [split; [apply K; [exact A1 | lia | cbn; lia | cbn; lia] | exact B1]|].
split; [split; [apply K; [exact A2 | lia | cbn; lia | cbn; lia] | exact B2]|].
split; [split; [apply K; [exact A3 | lia | cbn; lia | cbn; lia] | exact B3]|].
split; [split; [apply K; [exact A4 | lia | cbn; lia | cbn; lia] | exact B4]|].
split; [split; [exact Hv | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hr]|].
split; [split; [apply K; [exact A6 | lia | cbn; lia | cbn; lia] | exact B6]|]. exact I.
Qed.
End b.
Section d.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Lemma hk_tbl_apart : forall lyc Sc W regs mem md k C l1 x l2 y, hcore_raw lyc Sc W regs mem md k C ->
ac_blocks tb C = l1 ++ x :: l2 -> In y (l1 ++ l2) -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros lyc Sc W regs mem md k C l1 x l2 y HC El Hy.
pose proof (hcore_AR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ HC) as HAR.
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & HPerm & _). rewrite El in HPerm.
apply (rg_sep_head_in B LAWS lyc Sc W mem md x (PROT ++ l1 ++ l2) y HAR).
- eapply Permutation_trans; [exact HPerm|]. rewrite app_assoc. apply Permutation_sym.
rewrite app_assoc. apply Permutation_middle.
- apply in_app_iff. right. exact Hy.
Qed.
Lemma hk_tbl_apart_nth : forall lyc Sc W regs mem md k C (p q : nat) x y, hcore_raw lyc Sc W regs mem md k C ->
nth_error (ac_blocks tb C) p = Some x -> nth_error (ac_blocks tb C) q = Some y -> p <> q ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
intros lyc Sc W regs mem md k C p q x y HC Hp Hq Hne.
destruct (nth_error_split _ _ Hp) as (l1 & l2 & El & Hlen).
assert (Hy : In y (l1 ++ l2)).
{ rewrite El in Hq. destruct (Nat.lt_ge_cases q p) as [Hlt | Hge].
- rewrite nth_error_app1 in Hq by lia. apply in_app_iff. left. exact (nth_error_In _ _ Hq).
- rewrite nth_error_app2 in Hq by lia. destruct (q - length l1)%nat as [|m] eqn:Em; [lia|]. cbn in Hq.
apply in_app_iff. right. exact (nth_error_In _ _ Hq). }
pose proof (hk_tbl_apart _ _ _ _ _ _ _ _ l1 x l2 y HC El Hy) as Hd. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.
Lemma hk_tbl_other_kept : forall lyc Sc W regs mem md k C l1 x l2 (mem' : word -> option byte), hcore_raw lyc Sc W regs mem md k C ->
ac_blocks tb C = l1 ++ x :: l2 ->
(forall a, 0 <= a < alloc_ceiling -> ~ (fst x <= a < fst x + req_size (snd x)) -> aview trasegs (w_H W) mem' a = aview trasegs (w_H W) mem a) ->
forall y, In y (l1 ++ l2) -> rg_blk_kept (w_H W) (w_H W) mem mem' (fst y) (req_size (snd y)).
Proof.
intros lyc Sc W regs mem md k C l1 x l2 mem' HC El Hk y Hy i Hi.
pose proof (hcore_AR B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ HC) as HAR.
pose proof (hk_tbl_apart _ _ _ _ _ _ _ _ l1 x l2 y HC El Hy) as Hd. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (Hyin : In y (ablocks B lyc Sc)).
{ destruct y as [yb yn]. apply (hcore_in_tbl B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH _ _ _ _ _ _ _ _ _ _ HC).
rewrite El. apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy | Hy]; [left; exact Hy | right; right; exact Hy]. }
destruct y as [yb yn]. cbn [fst snd] in *.
destruct (al_blocks _ _ LAWS lyc Sc W mem md yb yn HAR Hyin) as (_ & H4096 & Hceil & _).
apply Hk; [lia | lia].
Qed.
End d.
