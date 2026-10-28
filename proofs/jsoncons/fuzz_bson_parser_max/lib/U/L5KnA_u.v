(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5Kn_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5KA.

Fixpoint zpolyA (V : nat -> Z) (e : expr) : option Z :=
  match e with
  | ELit z => Some z
  | EVar n => Some (V n)
  | EAlu ALU_ADD a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x + y) | _, _ => None end
  | EAlu ALU_SUB a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x - y) | _, _ => None end
  | EAlu ALU_SRL a (ELit s) =>
      if (Z.leb 0 s && Z.ltb s 64)%bool then match zpolyA V a with Some x => Some (x mod 18446744073709551616 / 2 ^ s) | None => None end else None
  | EMd M_MUL a b => match zpolyA V a, zpolyA V b with Some x, Some y => Some (x * y) | _, _ => None end
  | _ => None
  end.

Lemma zpolyA_sound E V e : forall zz, L5K.zagree E V e -> zpolyA V e = Some zz -> bv_unsigned (edenot E e) = zz mod BL.MM.
Proof.
  induction e; intros zz HA HZ; cbn [zpolyA L5K.zagree] in HA, HZ; try discriminate; cbn [edenot].
  - inversion HZ; subst. rewrite Z_to_bv_unsigned. reflexivity.
  - inversion HZ; subst. rewrite <- HA. symmetry. apply Z.mod_small. apply (BL.bvu_range (ev E n)).
  - destruct HA as [HA1 HA2]. destruct op; try discriminate.
    + destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
      rewrite (BL.zalu_sound ALU_ADD _ _ ((bv_unsigned (edenot E e1) + bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
      rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zplus_mod. reflexivity.
    + destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
      rewrite (BL.zalu_sound ALU_SUB _ _ ((bv_unsigned (edenot E e1) - bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
      rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zminus_mod. reflexivity.
    + destruct e2 as [s| | | | | | |]; try discriminate.
      destruct (Z.leb 0 s && Z.ltb s 64)%bool eqn:Hs; try discriminate. apply andb_prop in Hs as [Hs0 Hs1]. apply Z.leb_le in Hs0. apply Z.ltb_lt in Hs1.
      destruct (zpolyA V e1) as [x|] eqn:E1; try discriminate. inversion HZ; subst.
      rewrite (BL.zalu_sound ALU_SRL _ _ (bv_unsigned (edenot E e1) / 2 ^ (bv_unsigned (edenot E (ELit s)) mod 64))) by reflexivity.
      rewrite (IHe1 x HA1 eq_refl). cbn [edenot]. rewrite BG.unsigned_lit by lia.
      rewrite (Z.mod_small s 64) by lia. rewrite BL.MM_val.
      symmetry. apply Z.mod_small. split. apply Z.div_pos. apply Z.mod_pos_bound. lia. lia.
      apply Z.div_lt_upper_bound. lia. assert (0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
      pose proof (Z.mod_pos_bound x 18446744073709551616 ltac:(lia)). nia.
  - destruct HA as [HA1 HA2]. destruct op; try discriminate.
    destruct (zpolyA V e1) as [x|] eqn:E1; destruct (zpolyA V e2) as [y|] eqn:E2; try discriminate. inversion HZ; subst.
    rewrite (BL.zmd_sound M_MUL _ _ ((bv_unsigned (edenot E e1) * bv_unsigned (edenot E e2)) mod BL.MM)) by reflexivity.
    rewrite (IHe1 x HA1 eq_refl), (IHe2 y HA2 eq_refl). rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma zpolyA_val E V e z v : L5K.zagree E V e -> zpolyA V e = Some z -> z mod BL.MM = v -> bv_unsigned (edenot E e) = v.
Proof. intros HA HZ Hv. rewrite (zpolyA_sound E V e z HA HZ). exact Hv. Qed.
Lemma zpolyA_word E V e z v : L5K.zagree E V e -> zpolyA V e = Some z -> z mod BL.MM = v -> edenot E e = Z_to_bv 64 v.
Proof. intros HA HZ Hv. apply BG.word_of_unsigned. eapply zpolyA_val; eauto. Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Definition zeros_at (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

Lemma kentry_KZero E M b off ne a n :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E ne) = n ->
  0 <= a + off -> 0 < n -> a + off + n <= 2 ^ 64 ->
  zeros_at M (a + off) n -> kentry_ok segs E M (KZero (SA b off) ne).
Proof.
  intros Ha Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ. rewrite L5K.estart_e, Ha, Hn.
  split. lia. intros i Hi. apply Hz. lia.
Qed.
Lemma zeros_of_KZero E M b off ne a n :
  kentry_ok segs E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E ne) = n -> zeros_at M (a + off) n.
Proof.
  intros (Hf & Hz) Ha Hn i Hi. unfold elenZ in Hz. rewrite L5K.estart_e, Ha, Hn in Hz. apply Hz. lia.
Qed.
Lemma zeros_at_sub M a n a' n' : zeros_at M a n -> a <= a' -> a' + n' <= a + n -> zeros_at M a' n'.
Proof. intros Hz H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Hz. lia. Qed.
Lemma zeros_at_agree1 M M' a n : (forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> zeros_at M a n -> zeros_at M' a n.
Proof. intros HA Hz i Hi. rewrite HA by lia. apply Hz. lia. Qed.
Lemma zeros_at_defined M a n : zeros_at M a n -> L5.defined M a n.
Proof. intros Hz i Hi. rewrite (Hz i Hi). discriminate. Qed.
(* [comment removed for export] *)
Lemma u8_of_zeros M a n i : zeros_at M a n -> 0 <= i < n -> 0 <= a + i < 2 ^ 64 -> L5.u8_at segs M (a + i) 0.
Proof.
  intros Hz Hi Hr. unfold L5.u8_at. cbn [rdn]. rewrite (Hz i Hi). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_to_le_bytes_1_mod z : 0 <= z < 2 ^ 64 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 (z mod 256)].
Proof.
  intros Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma u8_of_KWord1_mod E M b off e a v :
  kentry_ok segs E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  L5.u8_at segs M (a + off) (v mod 256).
Proof.
  intros K Ha Hv. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). unfold L5.u8_at.
  rewrite L5K.adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd.
  rewrite word_to_le_bytes_1_mod in Rd. exact Rd. rewrite <- Hv. apply (BL.bvu_range (edenot E e)).
Qed.
End WithSegs.
End L5KA.
