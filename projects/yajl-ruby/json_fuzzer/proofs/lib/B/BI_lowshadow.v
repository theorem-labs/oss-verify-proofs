(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BI_shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Notation LS_LO := 0x7fffa000%Z (only parsing).
Notation LS_HI := 0x800b8600%Z (only parsing).   (* [comment removed for export] *)

Definition a_glob_shadow_runs : list (Z * Z * Z) :=
  [(0x7fffc20c, 1, 0x6); (0x7fffc20d, 3, 0xf9); (0x7fffc21a, 1, 0x2); (0x7fffc21b, 5, 0xf9); (0x7fffc224, 1, 0x1); (0x7fffc225, 7, 0xf9);
   (0x7fffc22e, 1, 0x6); (0x7fffc22f, 5, 0xf9); (0x7fffc236, 1, 0x6); (0x7fffc237, 5, 0xf9); (0x7fffc240, 4, 0xf9); (0x7fffc246, 1, 0x5);
   (0x7fffc247, 5, 0xf9); (0x7fffc254, 1, 0x5); (0x7fffc255, 3, 0xf9); (0x7fffc25a, 1, 0x2); (0x7fffc25b, 5, 0xf9); (0x7fffc260, 1, 0x7);
   (0x7fffc261, 3, 0xf9); (0x7fffc265, 1, 0x2); (0x7fffc266, 2, 0xf9); (0x7fffc269, 1, 0x3); (0x7fffc26a, 2, 0xf9); (0x7fffc28e, 1, 0x7);
   (0x7fffc28f, 5, 0xf9); (0x7fffc295, 1, 0x5); (0x7fffc296, 2, 0xf9); (0x7fffc298, 1, 0x4); (0x7fffc299, 3, 0xf9); (0x7fffc29c, 1, 0x5);
   (0x7fffc29d, 3, 0xf9); (0x7fffc2a0, 1, 0x4); (0x7fffc2a1, 3, 0xf9); (0x7fffc2a5, 1, 0x5); (0x7fffc2a6, 2, 0xf9); (0x7fffc2c8, 8, 0xf9);
   (0x7fffc2d0, 1, 0x4); (0x7fffc2d1, 3, 0xf9); (0x7fffc2dd, 1, 0x5); (0x7fffc2de, 2, 0xf9); (0x7fffc2e1, 1, 0x4); (0x7fffc2e2, 2, 0xf9);
   (0x7fffc2e5, 1, 0x6); (0x7fffc2e6, 2, 0xf9); (0x7fffc2e9, 1, 0x5); (0x7fffc2ea, 2, 0xf9); (0x7fffc2ee, 2, 0xf9); (0x7fffc2f1, 1, 0x7);
   (0x7fffc2f2, 2, 0xf9); (0x7fffc2f6, 1, 0x3); (0x7fffc2f7, 5, 0xf9); (0x7fffc2fd, 1, 0x6); (0x7fffc2fe, 2, 0xf9); (0x7fffc301, 1, 0x5);
   (0x7fffc302, 2, 0xf9); (0x7fffc309, 1, 0x3); (0x7fffc30a, 6, 0xf9); (0x7fffc313, 1, 0x2); (0x7fffc314, 4, 0xf9); (0x7fffc337, 1, 0x4);
   (0x7fffc338, 4, 0xf9); (0x7fffc33d, 1, 0x6); (0x7fffc33e, 2, 0xf9); (0x7fffc346, 1, 0x1); (0x7fffc347, 5, 0xf9); (0x7fffc34e, 1, 0x2);
   (0x7fffc34f, 5, 0xf9); (0x7fffc356, 1, 0x1); (0x7fffc357, 5, 0xf9); (0x7fffc360, 1, 0x2); (0x7fffc361, 7, 0xf9); (0x7fffc36d, 1, 0x3);
   (0x7fffc36e, 6, 0xf9); (0x7fffc377, 1, 0x6); (0x7fffc378, 4, 0xf9); (0x7fffc380, 1, 0x6); (0x7fffc381, 7, 0xf9); (0x7fffc38f, 5, 0xf9);
   (0x7fffc39a, 1, 0x5); (0x7fffc39b, 5, 0xf9); (0x7fffc3a5, 1, 0x1); (0x7fffc3a6, 6, 0xf9); (0x7fffc3ad, 1, 0x6); (0x7fffc3ae, 2, 0xf9);
   (0x7fffc3b2, 1, 0x3); (0x7fffc3b3, 5, 0xf9); (0x7fffc3ba, 1, 0x7); (0x7fffc3bb, 5, 0xf9); (0x7fffc3c8, 1, 0x2); (0x7fffc3c9, 3, 0xf9);
   (0x7fffc3cc, 1, 0x2); (0x7fffc3cd, 3, 0xf9); (0x7fffc3d0, 1, 0x2); (0x7fffc3d1, 3, 0xf9); (0x7fffc3d4, 1, 0x2); (0x7fffc3d5, 3, 0xf9);
   (0x7fffc3d8, 1, 0x2); (0x7fffc3d9, 3, 0xf9); (0x7fffc3dc, 1, 0x2); (0x7fffc3dd, 3, 0xf9); (0x7fffc3e0, 1, 0x2); (0x7fffc3e1, 3, 0xf9);
   (0x7fffc3e4, 1, 0x2); (0x7fffc3e5, 3, 0xf9); (0x7fffc3e8, 1, 0x2); (0x7fffc3e9, 3, 0xf9); (0x7fffc3f0, 1, 0x3); (0x7fffc3f1, 7, 0xf9);
   (0x7fffc3fa, 1, 0x3); (0x7fffc3fb, 5, 0xf9); (0x7fffc401, 1, 0x4); (0x7fffc402, 2, 0xf9); (0x7fffc405, 1, 0x3); (0x7fffc406, 2, 0xf9);
   (0x8000d373, 5, 0xf9); (0x8000d37c, 4, 0xf9); (0x8000d384, 4, 0xf9); (0x8000d3ec, 496, 0xf9)].

(* [comment removed for export] *)
Fixpoint run_lookup (l : list (Z * Z * Z)) (a : Z) : Z :=
  match l with
  | [] => 0
  | (s, n, v) :: l' => if (s <=? a) && (a <? s + n) then v else run_lookup l' a
  end.
Definition low_shadow_byte (a : Z) : byte :=
  if (a <? 0x7fffc20c) || (0x8000d5dc <=? a) then Z_to_bv 8 0 else Z_to_bv 8 (run_lookup a_glob_shadow_runs a).

Lemma low_shadow_byte_zero : forall a, a < 0x7fffc20c \/ 0x8000d5dc <= a -> low_shadow_byte a = Z_to_bv 8 0.
Proof.
  intros a H. unfold low_shadow_byte.
  destruct (Z.ltb_spec a 0x7fffc20c); [reflexivity|]. destruct (Z.leb_spec 0x8000d5dc a); [reflexivity|]. exfalso; lia.
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
Lemma low_shadow_bytes_zero : forall a n, a + Z.of_nat n <= 0x7fffc20c \/ 0x8000d5dc <= a ->
  low_shadow_bytes a n = repeat (Z_to_bv 8 0) n.
Proof.
  intros a n H. unfold low_shadow_bytes. revert a H. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [zrange map repeat]. rewrite low_shadow_byte_zero by lia. f_equal. apply IH. lia.
Qed.

Section WithSegs.
(* [comment removed for export] *)
Definition low_shadow_ok (m : mem) : Prop :=
  forall a, LS_LO <= a < LS_HI -> wview bsegs m (wa a) <> None /\ mrd bsegs m (wa a) = Some (low_shadow_byte a).

Lemma low_shadow_stk : forall m lo hi, low_shadow_ok m -> LS_LO <= lo -> hi <= LS_HI -> stk bsegs m lo hi.
Proof.
  intros m lo hi H Hlo Hhi. split; [lia|]. split; [lia|]. intros a Ha. destruct (H a ltac:(lia)) as [W R].
  split; [exact W| eexists; exact R].
Qed.

Lemma low_shadow_bytes_at : forall m a n, low_shadow_ok m -> LS_LO <= a -> a + Z.of_nat n <= LS_HI ->
  bytes_at bsegs m a (low_shadow_bytes a n).
Proof.
  intros m a n H Ha Hn. split; [lia|]. split; [rewrite low_shadow_bytes_length; lia|].
  intros i Hi. rewrite low_shadow_bytes_length in Hi. rewrite low_shadow_bytes_nth by exact Hi.
  apply (proj2 (H (a + Z.of_nat i) ltac:(lia))).
Qed.

Lemma low_shadow_rw : forall m a n, low_shadow_ok m -> LS_LO <= a -> a + Z.of_nat n <= LS_HI ->
  rw_cells bsegs m a [CB n (low_shadow_bytes a n)].
Proof.
  intros m a n H Ha Hn. split; [split|].
  - cbn. split; [apply low_shadow_bytes_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply low_shadow_bytes_at; assumption.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma low_shadow_u8arr : forall m a n, low_shadow_ok m -> LS_LO <= a -> a + Z.of_nat n <= LS_HI ->
  u8arr bsegs m a (low_shadow_bytes a n).
Proof.
  intros m a n H Ha Hn. apply (u8arr_of_rw_cells bsegs m a n). apply low_shadow_rw; assumption.
Qed.

Lemma low_shadow_transport : forall W m m',
  low_shadow_ok m -> munch W m m' -> wmono bsegs m m' -> disjoint_from W LS_LO (LS_HI - LS_LO) -> low_shadow_ok m'.
Proof.
  intros W m m' H MU WM D a Ha. destruct (H a Ha) as [W1 R1]. split.
  - apply WM. exact W1.
  - unfold mrd in *. rewrite (MU (wa a)); [exact R1|]. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D| lia].
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma low_shadow_granules : forall m a n bs, low_shadow_ok m -> LS_LO <= a -> a + Z.of_nat n <= LS_HI ->
  low_shadow_bytes a n = bs -> u8arr bsegs m a bs.
Proof. intros m a n bs H Ha Hn <-. apply low_shadow_u8arr; assumption. Qed.

(* [comment removed for export] *)
Lemma musl_statics_shadow_clean : forall m A n, low_shadow_ok m -> 0x5d0810 <= A -> 1 <= n -> A + n <= 0x603000 ->
  exists ws, shadow_window bsegs m 0x7fff8000 A n ws /\ range_clean 0x7fff8000 A n ws.
Proof.
  intros m A n H HA Hn HAn.
  pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) ltac:(lia)) as G; cbv zeta in G.
  set (lo := shw_lo 0x7fff8000 A) in *. set (hi := shw_hi 0x7fff8000 A n) in *.
  assert (R1 : Z.shiftr A 3 = A / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (R2 : Z.shiftr (A + n + -1) 3 = (A + n + -1) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (BLO : 0x800b2100 <= lo) by (unfold lo, shw_lo, al8 in *; rewrite R1 in *; Z.div_mod_to_equations; lia).
  assert (BHI : hi <= 0x800b8600) by (unfold hi, shw_hi, al8 in *; rewrite R2 in *; Z.div_mod_to_equations; lia).
  exists (low_shadow_bytes lo (Z.to_nat (hi - lo))). split.
  - split; [| rewrite low_shadow_bytes_length; lia]. apply low_shadow_bytes_at; [exact H | lia | lia].
  - intros g Hg. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    rewrite low_shadow_bytes_zero by lia. apply nth_error_repeat. lia.
Qed.

(* [comment removed for export] *)
Lemma rodata_shadow_clean : forall m A n, low_shadow_ok m -> 0x10000 <= A -> 1 <= n -> A + n <= 0x21060 ->
  exists ws, shadow_window bsegs m 0x7fff8000 A n ws /\ range_clean 0x7fff8000 A n ws.
Proof.
  intros m A n H HA Hn HAn.
  pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) ltac:(lia)) as G; cbv zeta in G.
  set (lo := shw_lo 0x7fff8000 A) in *. set (hi := shw_hi 0x7fff8000 A n) in *.
  assert (R1 : Z.shiftr A 3 = A / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (R2 : Z.shiftr (A + n + -1) 3 = (A + n + -1) / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (BLO : 0x7fffa000 <= lo) by (unfold lo, shw_lo, al8 in *; rewrite R1 in *; Z.div_mod_to_equations; lia).
  assert (BHI : hi <= 0x7fffc210) by (unfold hi, shw_hi, al8 in *; rewrite R2 in *; Z.div_mod_to_equations; lia).
  assert (G2B : 0x7fff8000 + Z.shiftr (A + n + -1) 3 < 0x7fffc20c) by (rewrite R2; Z.div_mod_to_equations; lia).
  exists (low_shadow_bytes lo (Z.to_nat (hi - lo))). split.
  - split; [| rewrite low_shadow_bytes_length; lia]. apply low_shadow_bytes_at; [exact H | lia | lia].
  - intros g Hg. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    rewrite low_shadow_bytes_nth by lia. f_equal.
    replace (lo + Z.of_nat (Z.to_nat (0x7fff8000 + g - lo))) with (0x7fff8000 + g) by lia.
    apply low_shadow_byte_zero. lia.
Qed.
End WithSegs.
