(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge SysStep Cells Step Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sx32_mod32 : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 (v mod 2^32)) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound v (2^32)); lia). rewrite swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. change (2^32) with 4294967296. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma land253 : forall g, 0 <= g < 256 -> (Z.land g 253 =? 1) = ((g =? 1) || (g =? 3)).
Proof.
  intros g Hg.
  assert (H : forall n, (n < 256)%nat -> (Z.land (Z.of_nat n) 253 =? 1) = ((Z.of_nat n =? 1) || (Z.of_nat n =? 3))).
  { intros n Hn. do 256 (destruct n as [|n]; [reflexivity|]). lia. }
  rewrite <- (Z2Nat.id g) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma land64_small : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land64_neg : forall x, - 2 ^ 64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2 ^ 64.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.

(* [comment removed for export] *)
Lemma set0_len_norm : forall len, 0 <= len < 2^31 ->
  Z.land (Z.land (bv_swrap 32 (0 - Z.b2z (9223372036854775808 <? Z.lxor len 9223372036854775808))) 18446744073709551615) len = len.
Proof.
  intros len Hl. destruct (Z.eq_dec len 0) as [->|NE]; [reflexivity|].
  change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia.
  replace (2^63 <? len + 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  change (Z.land (bv_swrap 32 (0 - Z.b2z true)) 18446744073709551615) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma lxor_ones31 : forall x, 0 <= x < 2^31 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof.
  intros x Hx. change 2147483647 with (Z.ones 31).
  assert (E : Z.lxor x (Z.ones 31) = ((Z.lnot x) mod 2^31)%Z).
  { rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 31).
    - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
      destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 31%Z; [apply Z.log2_lt_pow2; lia|lia]. }
  rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^31)) with (2^31 - 1)%Z.
  pose proof (Z.add_lnot_diag x). replace (Z.lnot x) with (-x - 1)%Z by lia.
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma objsize_tail : forall r len, 0 <= len < 65536 -> 2 <= r <= 4 ->
  Z.lor (Z.land (Z.b2z (9223372036854775808 + r <? Z.lxor (Z.lxor len 2147483647) 9223372036854775808) + -1) 18446744073709551615)
        (Z.land (bv_swrap 32 (r + len)) 18446744073709551615) = r + len.
Proof.
  intros r len Hl Hr. rewrite lxor_ones31 by lia. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia.
  replace (2^63 + r <? 2147483647 - len + 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.b2z]. change (Z.land (1 + -1) 18446744073709551615) with 0. rewrite Z.lor_0_l.
  rewrite swrap32_small by lia. apply land64_small. lia.
Qed.

(* [comment removed for export] *)
Lemma srliw8_small : forall x, 0 <= x < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 8) = x / 256.
Proof.
  intros x Hx. unfold bv_wrap. unfold bv_modulus. rewrite (Z.mod_small x) by (cbn; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  apply swrap32_small. split; [pose proof (Z.div_pos x 256); lia| apply Z.div_lt_upper_bound; lia].
Qed.

(* [comment removed for export] *)
Lemma der_hl_range : forall n, 0 <= n < 65536 -> 2 <= der_hl n <= 4.
Proof.
  intros n Hn. destruct (Z_lt_le_dec n 128) as [A|A]; [rewrite der_hl_small by lia; lia|].
  destruct (Z_lt_le_dec n 256) as [B|B]; [rewrite der_hl_mid by lia; lia| rewrite der_hl_big by lia; lia].
Qed.

(* [comment removed for export] *)
Definition bret (b : bool) : Z := if b then 1 else 0.

(* [comment removed for export] *)
Definition sct_ok (adr : bptr -> Z) (x : sctr bptr) : Prop :=
  (sc_version x = -1 \/ 0 <= sc_version x < 256) /\ 0 <= sc_hash x < 256 /\ 0 <= sc_sigalg x < 256
  /\ (forall q n, sc_sig x = Some (q, n) -> 0 < adr q < 2^64 /\ 0 < n <= 65535)
  /\ (forall q n, sc_blob x = Some (q, n) -> 0 < adr q < 2^64)
  /\ (forall q, sc_logid x = Some q -> 0 < adr q < 2^64)
  /\ 0 <= sc_extlen x <= 65535 /\ 0 <= sc_bloblen x <= 65535
  /\ (forall q n, sc_ext x = Some (q, n) -> 0 < adr q < 2^64) /\ sc_extlen x = match sc_ext x with Some (_, n) => n | None => 0 end
  /\ sc_bloblen x = match sc_blob x with Some (_, n) => n | None => 0 end.
