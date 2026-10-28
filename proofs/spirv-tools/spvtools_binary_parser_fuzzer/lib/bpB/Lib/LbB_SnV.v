(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Conv LbB_DKit LbB_DKitN LbB_SnStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require PmStepS1 PmBody1S1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma sn_w4 : forall v, 0 <= v < 2 ^ 32 ->
  word_to_le_bytes 4 (ext_val true 0 4 (Z_to_bv 64 v)) = word_to_le_bytes 4 (Z_to_bv 64 v).
Proof. intros v Hv. rewrite PmStepS1.ext_val_sx4 by lia. apply PmBody1S1.w2lb4_sx32. lia. Qed.

Lemma sn_br : forall v, 0 < v < 2 ^ 32 -> branch_taken BC_EQ (ext_val true 0 4 (Z_to_bv 64 v)) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv. rewrite PmStepS1.ext_val_sx4 by lia. unfold PrsNeeds.sx32.
  destruct (Z.ltb_spec v (2 ^ 31)); rewrite HLib.br_eq by lia; apply Z.eqb_neq; lia.
Qed.
Lemma sn_br0 : branch_taken BC_EQ (ext_val true 0 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_br_k4 : forall v, 0 <= v < 4 -> branch_taken BC_GEU (ext_val true 0 4 (Z_to_bv 64 v)) (Z_to_bv 64 4) = false.
Proof.
  intros v Hv. rewrite PmStepS1.ext_val_sx4 by lia. unfold PrsNeeds.sx32.
  destruct (Z.ltb_spec v (2 ^ 31)); [| lia]. rewrite HLib.br_geu by lia. apply Bool.negb_false_iff, Z.ltb_lt. lia.
Qed.
Lemma sn_br_e16 : forall v, 0 <= v < 16 -> branch_taken BC_LTU (Z_to_bv 64 15) (ext_val true 0 4 (Z_to_bv 64 v)) = false.
Proof.
  intros v Hv. rewrite PmStepS1.ext_val_sx4 by lia. unfold PrsNeeds.sx32.
  destruct (Z.ltb_spec v (2 ^ 31)); [| lia]. rewrite HLib.br_ltu by lia. apply Z.ltb_ge. lia.
Qed.

Lemma sn_w2 : forall bw, 0 <= bw < 2 ^ 32 ->
  word_to_le_bytes 2 (sext 64 (alu32 ALU_SRL (low32 (alu64 ALU_ADD (ext_val true 0 4 (Z_to_bv 64 bw)) (Z_to_bv 64 31)))
                                          (low32 (Z_to_bv 64 5))))
  = word_to_le_bytes 2 (Z_to_bv 64 (sn_nw bw)).
Proof.
  intros bw Hb. rewrite w_srlw. unfold v_srlw.
  rewrite PmStepS1.ext_val_sx4 by lia.
  assert (E5 : bv_unsigned (Z_to_bv 64 5) mod 32 = 5) by (vm_compute; reflexivity). rewrite E5.
  assert (EA : bv_wrap 32 (bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 (PrsGrammar.sx32 bw)) (Z_to_bv 64 31))) = (bw + 31) mod 2 ^ 32).
  { cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
    unfold PrsGrammar.sx32. destruct (Z.ltb_spec bw (2 ^ 31)); Z.div_mod_to_equations; lia. }
  rewrite EA. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  set (v5 := (bw + 31) mod 2 ^ 32 / 32).
  assert (R5 : 0 <= v5 < 2 ^ 27) by (unfold v5; Z.div_mod_to_equations; lia).
  assert (ES : bv_swrap 32 v5 = v5).
  { unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 32) with 4294967296. change (4294967296 / 2) with 2147483648.
    rewrite Z.mod_small by (clear - R5; lia). clear; lia. }
  rewrite ES. unfold sn_nw. fold v5. apply word_to_le_bytes_low; [lia|].
  intros i Hi. cbn in Hi. symmetry. apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma rw_C4_of_CB : forall m a (v : word), rw_cells asegs m a [CB 4 (word_to_le_bytes 4 v)] -> rw_cells asegs m a [C4 v].
Proof.
  intros m a v [[_ BA] WR]. split; [split|].
  - cbn. exact (conj I I).
  - cbn [cells_bytes cbytes] in BA |- *. exact BA.
  - cbn [cells_size csize] in WR |- *. exact WR.
Qed.
Lemma rw_C8_of_CB : forall m a (v : word), rw_cells asegs m a [CB 8 (word_to_le_bytes 8 v)] -> rw_cells asegs m a [C8 v].
Proof.
  intros m a v [[_ BA] WR]. split; [split|].
  - cbn. exact (conj I I).
  - cbn [cells_bytes cbytes] in BA |- *. exact BA.
  - cbn [cells_size csize] in WR |- *. exact WR.
Qed.
Lemma rw_C2_of_CB : forall m a (v : word), rw_cells asegs m a [CB 2 (word_to_le_bytes 2 v)] -> rw_cells asegs m a [C2 v].
Proof.
  intros m a v [[_ BA] WR]. split; [split|].
  - cbn. exact (conj I I).
  - cbn [cells_bytes cbytes] in BA |- *. exact BA.
  - cbn [cells_size csize] in WR |- *. exact WR.
Qed.

Lemma kword_of_cell4 : forall E m (a : saddr) x v (e : expr),
  cell4 ASEGS m x v -> estart E a = x -> 0 <= x -> x + 4 <= 2 ^ 64 -> edenot E e = Z_to_bv 64 v ->
  kentry_ok asegs E m (KWord a 4 e).
Proof.
  intros E m a x v e [Hv Hr] Ha H0 H1 He. cbn [kentry_ok].
  assert (FL : flat E a (Z.of_nat 4)) by (unfold flat; rewrite Ha; cbn; lia).
  split; [lia|]. split; [exact FL|].
  rewrite He. replace (adenot E a) with (Z_to_bv 64 x); [exact Hr|].
  apply bv_eq. rewrite (flat_u E a _ FL), Ha. apply unsigned_lit. lia.
Qed.

Lemma shk_last_of_addressable : forall m A n x, addressable m A n -> n mod 8 <> 0 ->
  A + 8 * (n / 8) <= x < A + n -> LbB_Kit.shk m x (n mod 8).
Proof.
  intros m A n x (Hn & SH) E Hx. pose proof SH as (HA & HA8 & _).
  assert (R : A <= x < A + 8 * Z.of_nat (length (shadow_of n))) by (rewrite shadow_of_length by lia; unfold nsh; Z.div_mod_to_equations; nia).
  destruct (LbB_Conv.shk_of_SHAD m A _ x SH R) as (b & Hb & K).
  replace (Z.to_nat ((x - A) / 8)) with (Z.to_nat (n / 8)) in Hb by (f_equal; Z.div_mod_to_equations; nia).
  rewrite (shadow_of_nth_last n ltac:(lia) E) in Hb. injection Hb as <-.
  unfold b8 in K. rewrite Z_to_bv_unsigned, bv_wrap_small in K by (change (bv_modulus 8) with 256; Z.div_mod_to_equations; lia). exact K.
Qed.

Lemma rw_C8s_of_ftbl : forall W B m T es e0 k,
  (forall i e, nth_error (e0 :: es) i = Some e -> fent_in (k + 8 * Z.of_nat i, 8%nat, e) T = true) ->
  ftbl W B m T ->
  rw_cells asegs m (B + k) (map (fun e => C8 (edenot (wenv W) e)) (e0 :: es)).
Proof.
  intros W B m T es. induction es as [|e1 es IH]; intros e0 k HI HT.
  - cbn [map]. apply rw_C8_of_CB. pose proof (HI 0%nat e0 eq_refl) as K. cbn [Z.of_nat] in K. rewrite Z.mul_0_r, Z.add_0_r in K.
    exact (ftbl_In W B m T k 8%nat e0 HT (fent_in_In _ _ K)).
  - change (map (fun e => C8 (edenot (wenv W) e)) (e0 :: e1 :: es))
      with ([C8 (edenot (wenv W) e0)] ++ map (fun e => C8 (edenot (wenv W) e)) (e1 :: es)).
    apply rw_cells_app. split.
    + apply rw_C8_of_CB. pose proof (HI 0%nat e0 eq_refl) as K. cbn [Z.of_nat] in K. rewrite Z.mul_0_r, Z.add_0_r in K.
      exact (ftbl_In W B m T k 8%nat e0 HT (fent_in_In _ _ K)).
    + cbn [cells_size csize]. replace (B + k + Z.of_nat (8 + 0)) with (B + (k + 8)) by lia.
      apply IH; [| exact HT]. intros i e Hi. pose proof (HI (S i) e Hi) as K.
      replace (k + 8 + 8 * Z.of_nat i) with (k + 8 * Z.of_nat (S i)) by lia. exact K.
Qed.
