(* What [Regen.STR_END], held by a state's facts, says of an environment: the string area (launch
   variable 12, its length blob 15) ends on an 8-byte boundary.  At LPS 727298f3
   the strings sit under the stack's page-aligned top, so their END is aligned and their start is not;
   the strnlen contracts read the end. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val State Plan Notation ValProofs Regen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations W64 Val St Plan ValP.
Open Scope Z_scope.

Module StrEnd.

Lemma has_fact_holds : forall E fs f, facts_hold E fs -> has_fact f fs = true -> fact_holds E f.
Proof.
  intros E fs f HF. induction fs as [|g fs IH]; intros HH; [discriminate HH|].
  cbn [has_fact] in HH. inversion HF as [|? ? Hg HF']; subst.
  destruct (fact_eqb f g) eqn:E1; [apply fact_eqb_eq in E1; subst g; exact Hg | exact (IH HF' HH)].
Qed.

Theorem str_end_mod8 : forall E fs, facts_hold E fs -> has_fact Regen.STR_END fs = true ->
  ((bv_unsigned (ev E 12%uint63) + bv_unsigned (den E (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))) mod 2 ^ 64) mod 8 = 0.
Proof.
  intros E fs HF HH. pose proof (has_fact_holds E fs _ HF HH) as HS.
  unfold Regen.STR_END in HS. cbn [fact_holds] in HS.
  change (den E (VAlu ALU_AND ?a ?b)) with (bv_and (den E a) (den E b)) in HS.
  change (den E (VAlu ALU_ADD ?a ?b)) with (bv_add (den E a) (den E b)) in HS.
  assert (D12 : den E (VP 12%uint63 (wp 0%uint63)) = ev E 12%uint63) by (cbn [den]; apply bv_add_0_r; reflexivity).
  rewrite D12 in HS. apply (f_equal bv_unsigned) in HS.
  rewrite bv_and_unsigned, bv_add_unsigned in HS.
  change (bv_unsigned (den E (VL (wp 7%uint63)))) with 7 in HS. change (bv_unsigned (den E (VL (wp 0%uint63)))) with 0 in HS.
  change 7 with (Z.ones 3) in HS. rewrite Z.land_ones in HS by lia. change (2 ^ 3) with 8 in HS.
  unfold bv_wrap in HS. rewrite bv_modulus_64 in HS. exact HS.
Qed.

(* the same with the sum's range known: the end itself is a multiple of 8 *)
Theorem str_end_aligned : forall E fs, facts_hold E fs -> has_fact Regen.STR_END fs = true ->
  bv_unsigned (ev E 12%uint63) + bv_unsigned (den E (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63)) <= 2 ^ 64 ->
  (bv_unsigned (ev E 12%uint63) + bv_unsigned (den E (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))) mod 8 = 0.
Proof.
  intros E fs HF HH HR. pose proof (str_end_mod8 E fs HF HH) as X.
  set (s := bv_unsigned (ev E 12%uint63) + bv_unsigned (den E (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))) in *.
  pose proof (bv_unsigned_in_range _ (ev E 12%uint63)) as R1.
  destruct (Z.eq_dec s (2 ^ 64)) as [Eq|Ne]; [rewrite Eq; reflexivity|].
  rewrite (Z.mod_small s (2 ^ 64)) in X; [exact X|]. unfold bv_modulus in R1.
  pose proof (bv_unsigned_in_range _ (den E (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))) as R2. unfold bv_modulus in R2.
  change (Z.of_N 64) with 64 in R1, R2. lia.
Qed.

End StrEnd.
