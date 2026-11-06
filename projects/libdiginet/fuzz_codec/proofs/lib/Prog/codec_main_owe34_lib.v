From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_owe_lib.
Import ListNotations.
Open Scope Z_scope.

(** The delta test (addiw t, delta, -0x40; bltu t, -0x80 -> E_RANGE) on the sign-extended delta: the branch is
    taken exactly when delta is outside [-64, 63]. *)
Lemma delta_out : forall x, - 2 ^ 31 <= x < 2 ^ 31 ->
  bv_swrap 32 (x mod 18446744073709551616 + -64) mod 18446744073709551616 < 18446744073709551488 ->
  x < -64 \/ 63 < x.
Proof.
  intros x Hx H. unfold bv_swrap, bv_wrap in H.
  replace (bv_half_modulus 32) with (2 ^ 31) in H by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) in H by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma delta_in : forall x, - 2 ^ 31 <= x < 2 ^ 31 ->
  18446744073709551488 <= bv_swrap 32 (x mod 18446744073709551616 + -64) mod 18446744073709551616 ->
  -64 <= x <= 63.
Proof.
  intros x Hx H. unfold bv_swrap, bv_wrap in H.
  replace (bv_half_modulus 32) with (2 ^ 31) in H by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) in H by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

(** owe()'s VPOT case (fuzz_codec.c:163-167). *)
Lemma owe3_spec_ok : forall d a b c delta bytes n, a < d_strips d -> -64 <= delta <= 63 ->
  owe_spec 3 (Some d) a b c delta bytes n = (0, ([0xb0; u8 (Z.lor 0x40 a); u8 (delta + 64)], KEY 8 0, 0)).
Proof.
  intros d a b c delta bytes n Ha Hd. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); [lia|].
  destruct (Z.ltb_spec delta (-64)); [lia|]. destruct (Z.ltb_spec 63 delta); [lia|]. reflexivity.
Qed.

Lemma owe3_spec_rng : forall d a b c delta bytes n, d_strips d <= a \/ delta < -64 \/ 63 < delta ->
  fst (owe_spec 3 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  destruct (Z.leb_spec (d_strips d) a); destruct (Z.ltb_spec delta (-64)); destruct (Z.ltb_spec 63 delta);
    try reflexivity; lia.
Qed.

(** owe()'s JOG case (fuzz_codec.c:169-173): no desk needed. *)
Lemma owe4_spec_ok : forall od a b c delta bytes n, -64 <= delta <= 63 ->
  owe_spec 4 od a b c delta bytes n = (0, ([0xb0; 0x5c; u8 (delta + 64)], KEY 8 0, 0)).
Proof.
  intros od a b c delta bytes n Hd. unfold owe_spec.
  destruct od as [d|]; cbn [negb orb Z.eqb Pos.eqb]; cbv beta iota zeta;
    (destruct (Z.ltb_spec delta (-64)); [lia|]); (destruct (Z.ltb_spec 63 delta); [lia|]); reflexivity.
Qed.

Lemma owe4_spec_rng : forall od a b c delta bytes n, delta < -64 \/ 63 < delta ->
  fst (owe_spec 4 od a b c delta bytes n) = E_RANGE.
Proof.
  intros od a b c delta bytes n H. unfold owe_spec.
  destruct od as [d|]; cbn [negb orb Z.eqb Pos.eqb]; cbv beta iota zeta;
    destruct (Z.ltb_spec delta (-64)); destruct (Z.ltb_spec 63 delta); try reflexivity; lia.
Qed.

(** The frame constant at FP + 0 stored with sh: B0 5C. *)
Lemma le2_b05c : le2 (Z_to_bv 64 23728) = [b8 0xb0; b8 0x5c].
Proof.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  repeat (apply f_equal2; [ apply byte_eq; reflexivity | ]). reflexivity.
Qed.

(** The key both cases owe. *)
Lemma key8 : KEY 8 0 = 524288.
Proof. reflexivity. Qed.
