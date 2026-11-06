From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Lib Require Import PropExec MState Mem Cells.
Import ListNotations.
Open Scope Z_scope.

Definition L_NS : Z := 500000000.

Definition knock_cells (st : Z) (p1 opened due heard : word) (g : Z) (p2 : word) : list cell :=
  [C4 (Z_to_bv 64 st); C4 p1; C8 opened; C8 due; C8 heard; C4 (Z_to_bv 64 g); C4 p2].

Lemma knock_sx32_unsigned : forall s, 0 <= s < 2^32 ->
  bv_unsigned (sx32 (Z_to_bv 64 s)) = if Z.ltb s (2^31) then s else s + (2^64 - 2^32).
Proof.
  intros s Hs. unfold sx32.
  rewrite (unsigned_lit s) by lia.
  rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity.
  replace (bv_modulus 32) with (2^32) by reflexivity.
  destruct (Z.ltb_spec s (2^31)).
  - rewrite (Z.mod_small (s + 2^31) (2^32)) by lia.
    replace (s + 2^31 - 2^31) with s by lia. apply Z.mod_small. lia.
  - replace (s + 2^31) with ((s - 2^31) + 1 * 2^32) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (s - 2^31) (2^32)) by lia.
    replace (s - 2^31 - 2^31) with ((s + (2^64 - 2^32)) + (-1) * 2^64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma knock_sx32_eqb : forall s c, 0 <= s < 2^32 -> 0 <= c < 2^31 ->
  bv_eqb (sx32 (Z_to_bv 64 s)) (Z_to_bv 64 c) = Z.eqb s c.
Proof.
  intros s c Hs Hc. unfold bv_eqb. rewrite knock_sx32_unsigned by lia. rewrite (unsigned_lit c) by lia.
  destruct (Z.ltb_spec s (2^31)); [reflexivity|].
  destruct (Z.eqb_spec (s + (2^64 - 2^32)) c); destruct (Z.eqb_spec s c); first [reflexivity | exfalso; lia].
Qed.
