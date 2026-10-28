From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import seqH_kit.
Open Scope Z_scope.

Ltac uckz_split :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)] =>
      let L := fresh "UL" in destruct (Z.ltb_spec a b) as [L|L]; [try (exfalso; lia) | try (exfalso; lia)]
  end;
  cbn [Z.b2z]; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent.

Ltac uckz := uckz_split; uck.

Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx.
  change 18446744073709551615 with (Z.ones 64) at 1.
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros n Hn.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.ltb_spec n 64) as [L|L].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    - rewrite Z.ones_spec_high by lia.
      assert (T : Z.testbit x n = false).
      { rewrite <- (Z.mod_small x (2^64)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite T. reflexivity. }
  rewrite E, Z.land_ones by lia.
  assert (LN : Z.lnot x = (18446744073709551615 - x) + (-1) * 2^64) by (rewrite Z.lnot_eq_pred_opp; lia).
  rewrite LN.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
