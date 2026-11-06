(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame. 
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import GDesc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition IMG_HULL : Z * Z := (0x10000, GD_IMG_END).

Definition lib_sh (m : mem) : Prop :=
  Forall (fun g => bytes_at bgbsegs m (shad (gd_beg g)) (ushadow (gd_size g))) GDESC.

Lemma ushadow_length : forall n, 0 <= n -> Z.of_nat (length (ushadow n)) = (n + 7) / 8.
Proof.
  intros n Hn. unfold ushadow. rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia).
  pose proof (Z.div_mod n 8 ltac:(lia)) as E. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B.
  destruct (Z.eqb_spec (n mod 8) 0) as [H0|H0]; cbn [length Z.of_nat].
  - rewrite Z.add_0_r. apply Z.div_unique with (r := 7); lia.
  - change (Z.pos (Pos.of_succ_nat 0)) with 1. apply Z.div_unique with (r := n mod 8 - 1); lia.
Qed.

Lemma gd_shadow_in_hull : forall g, In g GDESC ->
  shad (fst IMG_HULL) <= shad (gd_beg g)
  /\ shad (gd_beg g) + Z.of_nat (length (ushadow (gd_size g))) <= shad (snd IMG_HULL - 1) + 1.
Proof.
  intros g Hg. pose proof (GDESC_bounds g Hg) as (A & (S1 & S2) & _ & LO & HI).
  rewrite ushadow_length by lia. unfold IMG_HULL, shad. cbn [fst snd].
  assert (A8 : gd_beg g mod 8 = 0).
  { pose proof (Z.div_mod (gd_beg g) 32 ltac:(lia)) as E. rewrite A in E.
    replace (gd_beg g) with (4 * (gd_beg g / 32) * 8) by lia. apply Z.mod_mul. lia. }
  pose proof (Z.div_mod (gd_beg g) 8 ltac:(lia)) as E8. rewrite A8 in E8.
  assert (X1 : 0x10000 / 8 <= gd_beg g / 8) by (apply Z.div_le_mono; lia).
  assert (X2 : (gd_size g + 7) / 8 <= (GD_IMG_END - 1 - gd_beg g) / 8 + 1).
  { replace ((GD_IMG_END - 1 - gd_beg g) / 8 + 1) with ((GD_IMG_END - 1 - gd_beg g + 1 * 8) / 8) by (rewrite Z.div_add by lia; reflexivity).
    apply Z.div_le_mono; lia. }
  assert (X3 : (GD_IMG_END - 1) / 8 = gd_beg g / 8 + (GD_IMG_END - 1 - gd_beg g) / 8).
  { replace (GD_IMG_END - 1) with ((GD_IMG_END - 1 - gd_beg g) + (gd_beg g / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  lia.
Qed.

Lemma lib_sh_transport : forall W (m m' : mem), lib_sh m -> munch W m m' ->
  disjoint_from W (shad (fst IMG_HULL)) (shad (snd IMG_HULL - 1) + 1 - shad (fst IMG_HULL)) -> lib_sh m'.
Proof.
  intros W m m' H MU D. unfold lib_sh in *. apply Forall_forall. intros g Hg.
  pose proof (proj1 (Forall_forall _ _) H g Hg) as X. cbv beta in X.
  destruct (gd_shadow_in_hull g Hg) as (B1 & B2).
  apply (bytes_at_transport bgbsegs W m m' _ _ X MU).
  assert (GEN : forall a n a' n', a <= a' -> a' + n' <= a + n -> disjoint_from W a n -> disjoint_from W a' n').
  { clear. intros a n a' n' L1 L2. induction W as [|[lo hi] W IH]; intros D; cbn [disjoint_from] in *; [exact I|].
    destruct D as [D1 D2]. split; [lia | exact (IH D2)]. }
  apply (GEN (shad (fst IMG_HULL)) (shad (snd IMG_HULL - 1) + 1 - shad (fst IMG_HULL))); [exact B1 | lia | exact D].
Qed.

