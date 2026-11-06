(** strtol(s, &end, 10)'s answer on the C string s, as the RELEASED musl strtol walk states it: plugin-hostd/fuzz_command,
    origin/ossv/recipes (25e3d17bdb50), proofs/plugin-hostd/fuzz_command/lib/Prog/strtol_c.v (strtol_contract: a0 =
    s10_val str, *endptr = A + s10_end str, for bytes_at A (str ++ [NUL])). That walk is relocated onto fuzz_headamp
    (lib/Prog/strtol{,_c}.v, __intscan{,_c}.v, __shlim{,_c}.v, __errno_location{,_c}.v and lib/Spec/CType.v; U/ twins
    for the UBSan build), so the model functions live there and this file only re-exports them: c_space, c_digit and
    skip_space from lib/Spec/CType.v, and LMIN, ndig, dval, sign_split and the s10_* family from
    lib/Prog/__intscan_c.v. The unit holds ONE copy of each. fuzz_headamp's reading of the parse ([parse_key],
    Pod/Headamp.v) takes the relocated postcondition as it is, with no new strtol proof.

    C semantics (C11 7.22.1.4, musl src/stdlib/strtol.c + src/internal/intscan.c): skip isspace (' ', '\t' .. '\r'),
    one optional sign, the longest run of decimal digits; the value saturates at LONG_MIN / LONG_MAX (64-bit long);
    *end = s + (spaces + sign + digits), or s when there is no digit. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Export CType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Export __intscan_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Facts *)
Lemma dval_mono : forall s acc, 0 <= acc -> acc <= dval acc s.
Proof.
  induction s as [|b s IH]; intros acc Ha; cbn [dval]; [lia|].
  destruct (c_digit b) eqn:E; [|lia].
  unfold c_digit in E. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  specialize (IH (10 * acc + (bv_unsigned b - 48)) ltac:(lia)). lia.
Qed.

Lemma s10_mag_nonneg : forall s, 0 <= s10_mag s.
Proof. intros s. unfold s10_mag. pose proof (dval_mono (s10_rest s) 0 ltac:(lia)). lia. Qed.

Lemma length_sign_split : forall t, (length (snd (sign_split t)) <= length t)%nat.
Proof.
  intros [|b r]; cbn [sign_split snd length]; [lia|].
  destruct (bv_unsigned b =? 45); [cbn; lia|]. destruct (bv_unsigned b =? 43); cbn; lia.
Qed.

Lemma length_skip_space : forall s, (length (skip_space s) <= length s)%nat.
Proof. induction s as [|b s IH]; cbn [skip_space length]; [lia|]. destruct (c_space b); cbn; lia. Qed.

(** The clamp to [LONG_MIN, LONG_MAX] keeps the sign and every value in [0, 48): the tests c < 0 and c >= k (for
    0 <= k < 2^63) read the same on the clamped and the exact value. *)
Lemma s10_val_lt0 : forall s, (s10_val s <? 0) = (s10_signed s <? 0).
Proof.
  intros s. unfold s10_val, LMIN.
  destruct (Z.ltb_spec (s10_signed s) 0); [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma s10_val_ge : forall s k, 0 <= k < LMIN -> (k <=? s10_val s) = (k <=? s10_signed s).
Proof.
  intros s k Hk. unfold s10_val in *. unfold LMIN in *.
  destruct (Z.leb_spec k (s10_signed s)); [apply Z.leb_le | apply Z.leb_gt]; lia.
Qed.

Lemma s10_val_small : forall s, - LMIN <= s10_signed s < LMIN -> s10_val s = s10_signed s.
Proof. intros s H. unfold s10_val. lia. Qed.
