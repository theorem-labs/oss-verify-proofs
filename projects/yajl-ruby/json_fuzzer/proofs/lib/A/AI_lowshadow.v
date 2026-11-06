(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AI_shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Notation LS_LO := 0x7fffa000%Z (only parsing).
Notation LS_HI := 0x800b8600%Z (only parsing).   (* [comment removed for export] *)

Definition a_glob_shadow_runs : list (Z * Z * Z) :=
  [(0x7fffc204, 1, 0x6); (0x7fffc205, 3, 0xf9); (0x7fffc20e, 1, 0x1); (0x7fffc20f, 5, 0xf9); (0x7fffc216, 1, 0x2); (0x7fffc217, 5, 0xf9);
   (0x7fffc220, 1, 0x1); (0x7fffc221, 7, 0xf9); (0x7fffc22a, 1, 0x6); (0x7fffc22b, 5, 0xf9); (0x7fffc232, 1, 0x6); (0x7fffc233, 5, 0xf9);
   (0x7fffc23c, 4, 0xf9); (0x7fffc242, 1, 0x5); (0x7fffc243, 5, 0xf9); (0x7fffc250, 1, 0x5); (0x7fffc251, 3, 0xf9); (0x7fffc259, 1, 0x7);
   (0x7fffc25a, 6, 0xf9); (0x7fffc262, 1, 0x2); (0x7fffc263, 5, 0xf9); (0x7fffc268, 1, 0x7); (0x7fffc269, 3, 0xf9); (0x7fffc26d, 1, 0x2);
   (0x7fffc26e, 2, 0xf9); (0x7fffc271, 1, 0x3); (0x7fffc272, 2, 0xf9); (0x7fffc296, 1, 0x7); (0x7fffc297, 5, 0xf9); (0x7fffc2a2, 1, 0x3);
   (0x7fffc2a3, 5, 0xf9); (0x7fffc2a9, 1, 0x5); (0x7fffc2aa, 2, 0xf9); (0x7fffc2ac, 1, 0x4); (0x7fffc2ad, 3, 0xf9); (0x7fffc2b0, 1, 0x5);
   (0x7fffc2b1, 3, 0xf9); (0x7fffc2b4, 1, 0x4); (0x7fffc2b5, 3, 0xf9); (0x7fffc2b9, 1, 0x5); (0x7fffc2ba, 2, 0xf9); (0x7fffc2dc, 8, 0xf9);
   (0x7fffc2ec, 1, 0x4); (0x7fffc2ed, 3, 0xf9); (0x7fffc2f6, 1, 0x3); (0x7fffc2f7, 5, 0xf9); (0x7fffc2fd, 1, 0x5); (0x7fffc2fe, 2, 0xf9);
   (0x7fffc301, 1, 0x4); (0x7fffc302, 2, 0xf9); (0x7fffc305, 1, 0x6); (0x7fffc306, 2, 0xf9); (0x7fffc309, 1, 0x5); (0x7fffc30a, 2, 0xf9);
   (0x7fffc30e, 2, 0xf9); (0x7fffc311, 1, 0x7); (0x7fffc312, 2, 0xf9); (0x7fffc316, 1, 0x3); (0x7fffc317, 5, 0xf9); (0x7fffc31d, 1, 0x6);
   (0x7fffc31e, 2, 0xf9); (0x7fffc321, 1, 0x5); (0x7fffc322, 2, 0xf9); (0x7fffc329, 1, 0x3); (0x7fffc32a, 6, 0xf9); (0x7fffc333, 1, 0x2);
   (0x7fffc334, 4, 0xf9); (0x7fffc357, 1, 0x4); (0x7fffc358, 4, 0xf9); (0x7fffc362, 1, 0x6); (0x7fffc363, 5, 0xf9); (0x7fffc369, 1, 0x6);
   (0x7fffc36a, 2, 0xf9); (0x7fffc372, 1, 0x1); (0x7fffc373, 5, 0xf9); (0x7fffc37a, 1, 0x2); (0x7fffc37b, 5, 0xf9); (0x7fffc382, 1, 0x1);
   (0x7fffc383, 5, 0xf9); (0x7fffc38c, 1, 0x2); (0x7fffc38d, 7, 0xf9); (0x7fffc399, 1, 0x3); (0x7fffc39a, 6, 0xf9); (0x7fffc3a3, 1, 0x6);
   (0x7fffc3a4, 4, 0xf9); (0x7fffc3ac, 1, 0x6); (0x7fffc3ad, 7, 0xf9); (0x7fffc3bb, 5, 0xf9); (0x7fffc3c6, 1, 0x5); (0x7fffc3c7, 5, 0xf9);
   (0x7fffc3d1, 1, 0x1); (0x7fffc3d2, 6, 0xf9); (0x7fffc3d9, 1, 0x6); (0x7fffc3da, 2, 0xf9); (0x7fffc3e3, 1, 0x1); (0x7fffc3e4, 4, 0xf9);
   (0x7fffc3ea, 1, 0x3); (0x7fffc3eb, 5, 0xf9); (0x7fffc3f2, 1, 0x7); (0x7fffc3f3, 5, 0xf9); (0x7fffc400, 1, 0x2); (0x7fffc401, 3, 0xf9);
   (0x7fffc404, 1, 0x2); (0x7fffc405, 3, 0xf9); (0x7fffc408, 1, 0x2); (0x7fffc409, 3, 0xf9); (0x7fffc40c, 1, 0x2); (0x7fffc40d, 3, 0xf9);
   (0x7fffc410, 1, 0x2); (0x7fffc411, 3, 0xf9); (0x7fffc414, 1, 0x2); (0x7fffc415, 3, 0xf9); (0x7fffc418, 1, 0x2); (0x7fffc419, 3, 0xf9);
   (0x7fffc41c, 1, 0x2); (0x7fffc41d, 3, 0xf9); (0x7fffc420, 1, 0x2); (0x7fffc421, 3, 0xf9); (0x7fffc428, 1, 0x3); (0x7fffc429, 7, 0xf9);
   (0x7fffc436, 1, 0x6); (0x7fffc437, 5, 0xf9); (0x7fffc43e, 1, 0x3); (0x7fffc43f, 5, 0xf9); (0x7fffc445, 1, 0x4); (0x7fffc446, 2, 0xf9);
   (0x7fffc449, 1, 0x3); (0x7fffc44a, 2, 0xf9); (0x8000d1f7, 5, 0xf9); (0x8000d200, 4, 0xf9); (0x8000d208, 4, 0xf9); (0x8000d270, 552, 0xf9)].

(* [comment removed for export] *)
Fixpoint run_lookup (l : list (Z * Z * Z)) (a : Z) : Z :=
  match l with
  | [] => 0
  | (s, n, v) :: l' => if (s <=? a) && (a <? s + n) then v else run_lookup l' a
  end.
Definition low_shadow_byte (a : Z) : byte :=
  if (a <? 0x7fffc204) || (0x8000d498 <=? a) then Z_to_bv 8 0 else Z_to_bv 8 (run_lookup a_glob_shadow_runs a).

Lemma low_shadow_byte_zero : forall a, a < 0x7fffc204 \/ 0x8000d498 <= a -> low_shadow_byte a = Z_to_bv 8 0.
Proof.
  intros a H. unfold low_shadow_byte.
  destruct (Z.ltb_spec a 0x7fffc204); [reflexivity|]. destruct (Z.leb_spec 0x8000d498 a); [reflexivity|]. exfalso; lia.
Qed.

(* [comment removed for export] *)
Fixpoint zrange (a : Z) (n : nat) : list Z := match n with O => [] | S k => a :: zrange (a + 1) k end.
Lemma zrange_length : forall a n, length (zrange a n) = n.
Proof. intros a n; revert a; induction n; intros; cbn; [reflexivity| now rewrite IHn]. Qed.
Lemma zrange_nth : forall a n i, (i < n)%nat -> nth_error (zrange a n) i = Some (a + Z.of_nat i).
Proof.
  intros a n; revert a; induction n as [|n IH]; intros a i Hi; [lia|].
  destruct i as [|i]; cbn [zrange nth_error]; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Definition low_shadow_bytes (a : Z) (n : nat) : list byte := map low_shadow_byte (zrange a n).
Lemma low_shadow_bytes_length : forall a n, length (low_shadow_bytes a n) = n.
Proof. intros. unfold low_shadow_bytes. rewrite length_map. apply zrange_length. Qed.
Lemma low_shadow_bytes_nth : forall a n i, (i < n)%nat -> nth_error (low_shadow_bytes a n) i = Some (low_shadow_byte (a + Z.of_nat i)).
Proof. intros. unfold low_shadow_bytes. rewrite nth_error_map, zrange_nth by assumption. reflexivity. Qed.
Lemma low_shadow_bytes_zero : forall a n, a + Z.of_nat n <= 0x7fffc204 \/ 0x8000d498 <= a ->
  low_shadow_bytes a n = repeat (Z_to_bv 8 0) n.
Proof.
  intros a n H. unfold low_shadow_bytes. revert a H. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [zrange map repeat]. rewrite low_shadow_byte_zero by lia. f_equal. apply IH. lia.
Qed.

Section WithSegs.
(* [comment removed for export] *)
Definition low_shadow_ok (m : mem) : Prop :=
  forall a, LS_LO <= a < LS_HI -> wview asegs m (wa a) <> None /\ mrd asegs m (wa a) = Some (low_shadow_byte a).

Lemma low_shadow_stk : forall m lo hi, low_shadow_ok m -> LS_LO <= lo -> hi <= LS_HI -> stk asegs m lo hi.
Proof.
  intros m lo hi H Hlo Hhi. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a ltac:(lia)) as [W R].
  split; [exact W| eexists; exact R].
Qed.

Lemma low_shadow_bytes_at : forall m a n, low_shadow_ok m -> LS_LO <= a -> a + Z.of_nat n <= LS_HI ->
  bytes_at asegs m a (low_shadow_bytes a n).
Proof.
  intros m a n H Ha Hn. split; [lia|]. split; [rewrite low_shadow_bytes_length; lia|].
  intros i Hi. rewrite low_shadow_bytes_length in Hi. rewrite low_shadow_bytes_nth by exact Hi.
  apply (proj2 (H (a + Z.of_nat i) ltac:(lia))).
Qed.

Lemma low_shadow_rw : forall m a n, low_shadow_ok m -> LS_LO <= a -> a + Z.of_nat n <= LS_HI ->
  rw_cells asegs m a [CB n (low_shadow_bytes a n)].
Proof.
  intros m a n H Ha Hn. split; [split|].
  - cbn. split; [apply low_shadow_bytes_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply low_shadow_bytes_at; assumption.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma low_shadow_u8arr : forall m a n, low_shadow_ok m -> LS_LO <= a -> a + Z.of_nat n <= LS_HI ->
  u8arr asegs m a (low_shadow_bytes a n).
Proof.
  intros m a n H Ha Hn. apply (u8arr_of_rw_cells asegs m a n). apply low_shadow_rw; assumption.
Qed.

Lemma low_shadow_transport : forall W m m',
  low_shadow_ok m -> munch W m m' -> wmono asegs m m' -> disjoint_from W LS_LO (LS_HI - LS_LO) -> low_shadow_ok m'.
Proof.
  intros W m m' H MU WM D a Ha. destruct (H a Ha) as [W1 R1]. split.
  - apply WM. exact W1.
  - unfold mrd in *. rewrite (MU (wa a)); [exact R1|]. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma low_shadow_granules : forall m a n bs, low_shadow_ok m -> LS_LO <= a -> a + Z.of_nat n <= LS_HI ->
  low_shadow_bytes a n = bs -> u8arr asegs m a bs.
Proof. intros m a n bs H Ha Hn <-. apply low_shadow_u8arr; assumption. Qed.

(* [comment removed for export] *)
Lemma musl_statics_shadow_clean : forall m A n, low_shadow_ok m -> 0x5cfdd0 <= A -> 1 <= n -> A + n <= 0x603000 ->
  exists ws, shadow_window asegs m 0x7fff8000 A n ws /\ range_clean 0x7fff8000 A n ws.
Proof.
  intros m A n H HA Hn HAn.
  pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) ltac:(lia)) as G; cbv zeta in G.
  set (lo := shw_lo 0x7fff8000 A) in *. set (hi := shw_hi 0x7fff8000 A n) in *.
  assert (R1 : Z.shiftr A 3 = A / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (R2 : Z.shiftr (A + n + -1) 3 = (A + n + -1) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (BLO : 0x800b1fb8 <= lo) by (unfold lo, shw_lo, al8 in *; rewrite R1 in *; Z.div_mod_to_equations; lia).
  assert (BHI : hi <= 0x800b8600) by (unfold hi, shw_hi, al8 in *; rewrite R2 in *; Z.div_mod_to_equations; lia).
  exists (low_shadow_bytes lo (Z.to_nat (hi - lo))). split.
  - split; [| rewrite low_shadow_bytes_length; lia]. apply low_shadow_bytes_at; [exact H | lia | lia].
  - intros g Hg. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    rewrite low_shadow_bytes_zero by lia. apply nth_error_repeat. lia.
Qed.

(* [comment removed for export] *)
Lemma rodata_shadow_clean : forall m A n, low_shadow_ok m -> 0x10000 <= A -> 1 <= n -> A + n <= 0x21020 ->
  exists ws, shadow_window asegs m 0x7fff8000 A n ws /\ range_clean 0x7fff8000 A n ws.
Proof.
  intros m A n H HA Hn HAn.
  pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) ltac:(lia)) as G; cbv zeta in G.
  set (lo := shw_lo 0x7fff8000 A) in *. set (hi := shw_hi 0x7fff8000 A n) in *.
  assert (R1 : Z.shiftr A 3 = A / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (R2 : Z.shiftr (A + n + -1) 3 = (A + n + -1) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (BLO : 0x7fffa000 <= lo) by (unfold lo, shw_lo, al8 in *; rewrite R1 in *; Z.div_mod_to_equations; lia).
  assert (BHI : hi <= 0x7fffc208) by (unfold hi, shw_hi, al8 in *; rewrite R2 in *; Z.div_mod_to_equations; lia).
  assert (G2B : 0x7fff8000 + Z.shiftr (A + n + -1) 3 < 0x7fffc204) by (rewrite R2; Z.div_mod_to_equations; lia).
  exists (low_shadow_bytes lo (Z.to_nat (hi - lo))). split.
  - split; [| rewrite low_shadow_bytes_length; lia]. apply low_shadow_bytes_at; [exact H | lia | lia].
  - intros g Hg. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    rewrite low_shadow_bytes_nth by lia. f_equal.
    replace (lo + Z.of_nat (Z.to_nat (0x7fff8000 + g - lo))) with (0x7fff8000 + g) by lia.
    apply low_shadow_byte_zero. lia.
Qed.
End WithSegs.
