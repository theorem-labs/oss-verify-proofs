(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SCW (W : Z) : Z := Z.shiftr ((4503599627370496 * W) mod 2^64) 58.

Lemma SCW_bits : forall W, 0 <= W -> SCW W = Z.land (Z.shiftr W 6) 63.
Proof.
  intros W HW. unfold SCW. apply Z.bits_inj'. intros k Hk.
  rewrite Z.shiftr_spec by lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  destruct (Z.lt_ge_cases k 6) as [Hl|Hg].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia.
    change 4503599627370496 with (2^52). rewrite Z.mul_comm, <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec by lia.
    f_equal. lia.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma SCW_range : forall W, 0 <= W -> 0 <= SCW W <= 63.
Proof.
  intros W HW. rewrite SCW_bits by exact HW. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.shiftr W 6) (2^6) ltac:(lia)). change (2^6) with 64 in *. change (Z.ones 6) with 63. lia.
Qed.

Lemma TB1_SCW : forall W, 0 <= W < 2^64 -> Z.land (Z.shiftr W 5 mod 2^64) 126 = 2 * SCW W.
Proof.
  intros W HW. rewrite Z.mod_small by (split; [apply Z.shiftr_nonneg; lia | rewrite Z.shiftr_div_pow2 by lia;
    apply Z.div_lt_upper_bound; [lia|]; change (2^5 * 2^64) with (2^69); lia]).
  rewrite SCW_bits by lia. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec. destruct (Z.eq_dec k 0) as [->|Hk0].
  - change (Z.testbit 126 0) with false. rewrite andb_false_r. symmetry. rewrite Z.bit0_odd, Z.odd_mul. reflexivity.
  - change 2 with (2^1). rewrite Z.mul_comm, <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec by lia.
    rewrite Z.land_spec, !Z.shiftr_spec by lia.
    destruct (Z.lt_ge_cases k 7) as [Hl|Hg].
    + replace (Z.testbit 126 k) with true by (destruct (Z.eq_dec k 1) as [->|]; [reflexivity|];
        destruct (Z.eq_dec k 2) as [->|]; [reflexivity|]; destruct (Z.eq_dec k 3) as [->|]; [reflexivity|];
        destruct (Z.eq_dec k 4) as [->|]; [reflexivity|]; destruct (Z.eq_dec k 5) as [->|]; [reflexivity|];
        assert (k = 6) as -> by lia; reflexivity).
      change 63 with (Z.ones 6). rewrite Z.testbit_ones by lia.
      replace ((0 <=? k - 1) && (k - 1 <? 6)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite !andb_true_r. f_equal. lia.
    + replace (Z.testbit 126 k) with false.
      2:{ symmetry. apply (AxBits.testbit_high 7 126 k); lia. }
      change 63 with (Z.ones 6). rewrite Z.testbit_ones by lia.
      replace ((0 <=? k - 1) && (k - 1 <? 6)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
      rewrite !andb_false_r. reflexivity.
Qed.


(* [comment removed for export] *)
Definition Ez (regs : bvmap 5 word) (vals : list Z) : env := Env (reg_ev regs (fun k => wa (nth (k - 32) vals 0))) (fun _ => []).

Lemma zatom : forall regs vals n v, Nat.ltb n 32 = false -> nth (n - 32) vals 0 = v -> 0 <= v < 2^64 ->
  bv_unsigned (ev (Ez regs vals) n) = v.
Proof. intros regs vals n v Hn Hv Hr. unfold Ez. cbn [ev]. unfold reg_ev. rewrite Hn, Hv. apply u_wa_small. exact Hr. Qed.

Lemma zreg : forall regs vals k, Nat.ltb k 32 = true -> ev (Ez regs vals) k = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. intros regs vals k Hk. unfold Ez. cbn [ev]. unfold reg_ev. rewrite Hk. reflexivity. Qed.

Ltac dsc_rw :=
  match goal with
  | H : bv_unsigned (ev ?E ?n) = ?v |- context [bv_unsigned (ev ?E ?n)] => rewrite H
  end.
Ltac dsc_mod :=
  match goal with
  | H : ?lo <= ?x <= ?hi |- context [?x mod 2^64] => rewrite (mod64_of_range x lo hi H eq_refl eq_refl)
  end.

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

(* [comment removed for export] *)
Ltac zpost_one :=
  first [ reflexivity
        | (rewrite adenot_z; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; reflexivity)
        | (rewrite adenot_z; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; f_equal; ring)
        | (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; reflexivity)
        | (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; f_equal; ring) ].

(* [comment removed for export] *)
Ltac zpost_reg HR' :=
  first [ (srg HR'; reflexivity)
        | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; reflexivity)
        | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply wa_eqm; f_equal; ring) ].

(* [comment removed for export] *)
Lemma land_mod32 : forall a b, (Z.land a b) mod 2^32 = Z.land (a mod 2^32) (b mod 2^32).
Proof.
  intros a b. apply Z.bits_inj'. intros i Hi. destruct (Z_lt_le_dec i 32) as [L|L].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.land_spec, !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. rewrite Z.land_spec, !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma act_span_mod32 : forall k, 0 <= k <= 255 ->
  (bv_swrap 32 (Z.shiftl 2 (k mod 32)) + -1) mod 2^32 = (2 ^ (Z.land k 31 + 1) - 1) mod 2^32.
Proof.
  intros k Hk. rewrite Zplus_mod, swrap32_mod, <- Zplus_mod. f_equal.
  assert (E : k mod 32 = Z.land k 31) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity).
  rewrite E, Z.shiftl_mul_pow2 by (pose proof (land31_bound k ltac:(lia)); lia). rewrite Z.pow_add_r by (pose proof (land31_bound k ltac:(lia)); lia). ring.
Qed.

Lemma act_avail_le : forall NFR k, 0 <= NFR <= 2^32-1 -> 0 <= k <= 255 ->
  word_to_le_bytes 4 (wa (Z.land (ext_Z true 0 4 NFR mod 2^64) ((bv_swrap 32 (Z.shiftl 2 (k mod 32)) + -1) mod 2^64)))
  = word_to_le_bytes 4 (wa (Z.land NFR (2 ^ (Z.land k 31 + 1) - 1))).
Proof.
  intros NFR k HN Hk. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. change (8 * Z.of_nat 4) with 32.
  rewrite !land_mod32, !mod64_32, ext4_swrap, swrap32_mod, act_span_mod32 by exact Hk. reflexivity.
Qed.

Lemma act_freed_le : forall NFR k, 0 <= NFR <= 2^32-1 -> 0 <= k <= 255 ->
  word_to_le_bytes 4 (wa (Z.land (ext_Z true 0 4 NFR mod 2^64) (bv_swrap 32 (0 - bv_swrap 32 (Z.shiftl 2 (k mod 32))) mod 2^64)))
  = word_to_le_bytes 4 (wa (Z.ldiff NFR (2 ^ (Z.land k 31 + 1) - 1))).
Proof.
  intros NFR k HN Hk. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. change (8 * Z.of_nat 4) with 32.
  rewrite !land_mod32, !mod64_32, ext4_swrap, !swrap32_mod.
  assert (Hl : 0 <= Z.land k 31 < 32) by (apply land31_bound; lia).
  assert (E : k mod 32 = Z.land k 31) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity).
  rewrite E, Z.shiftl_mul_pow2 by lia. rewrite Zminus_mod, swrap32_mod, <- Zminus_mod.
  set (j := Z.land k 31) in *.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z_lt_le_dec i 32) as [L|L].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.ldiff_spec. f_equal.
    replace (0 - 2 * 2 ^ j) with (Z.lnot (2 ^ (j + 1) - 1)) by (unfold Z.lnot; rewrite <- Z.sub_1_r; rewrite Z.pow_add_r by lia; change (2^1) with 2; ring).
    rewrite Z.lnot_spec by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma act_freed_le2 : forall NFR k, 0 <= NFR <= 2^32-1 -> 0 <= k <= 255 ->
  word_to_le_bytes 4 (wa (Z.land (ext_Z true 0 4 NFR mod 2^64)
                          ((bv_swrap 32 (0 - bv_swrap 32 (Z.shiftl 2 (k mod 32)) mod 2^64) mod 2^64) mod 2^64)))
  = word_to_le_bytes 4 (wa (Z.ldiff NFR (2 ^ (Z.land k 31 + 1) - 1))).
Proof.
  intros NFR k HN Hk. rewrite Z.mod_mod by lia.
  replace (bv_swrap 32 (0 - bv_swrap 32 (Z.shiftl 2 (k mod 32)) mod 2^64)) with (bv_swrap 32 (0 - bv_swrap 32 (Z.shiftl 2 (k mod 32)))).
  - apply act_freed_le; assumption.
  - apply swrap32_eqm. rewrite Zminus_mod, (Zminus_mod 0 (bv_swrap 32 (Z.shiftl 2 (k mod 32)) mod 2^64)), mod64_32. reflexivity.
Qed.
