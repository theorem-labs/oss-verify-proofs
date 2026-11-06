(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "N"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "or"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_and"; "bv_modulus"; "bv_signed"; "bv_swrap"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "pow"; "of_N"; "lt"; "le"; "ltb"; "shiftl"; "sub"; "add"; "land"; "lor"; "shiftr"; "to_nat"; "eqb"; "lxor"; "mul"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "zholds"; "zl_of"; "zr_of"; "psupported"; "sx32"; "zeval"; "zle"; "zalu"; "zcond"; "zsublist"; "zsupported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "sv"; "eval"; "ext_low"; "rl"; "sublist"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "skipn"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "branch_cond"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "@LinuxProcessSemantics.Riscv.Sem"; "alu"; "branch_taken"; "low32"; "@Stdlib.Lists.List"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition toS (n : Z) (x : Z) : Z := ltac2:(tb__ "0|2|
SeVx;SfZ2M0Vn;A2M1A2S0S1eS0L_;S13R1SfG0S15Vn;Z1A2A2A2R1S15R1G1A2X1ex2Ty;").

Definition zalu (n : Z) (op : aluop) (a b : Z) : Z := ltac2:(tb__ "0|8|
S3aS0Lop;Vop;SeS16Va;Vb;A2SfZ2Vn;A2M0A2SeS15Va;Vb;A2G0A2SeS14Va;SeVb;Vn;A2M1A2G0A2S1eS0L_;M2S13S22Vn;Va;A2M3S22Vn;Vb;A2A2Z1M4Z0M5X1ex2G2S13SeVa;G0A2M6SeVb;G0A2M7A2G4G5X1ex2S1cG6G7A2S19G6G1A2SeS19G3G1A2G0A2S18G6G7A2S17G6G7A2X3axa").

Definition sx32 (x : Z) : Z := ltac2:(tb__ "0|0|
SeS22Z20Vx;A2SfZ2Z40A2A2").

Fixpoint zle (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: t => b mod 256 + 256 * zle t
  end.

Definition zsublist (i k : Z) (l : list Z) : list Z := ltac2:(tb__ "0|0|
S38S0S1aVk;A1S39S0S1aVi;A1Vl;A3A3").

Fixpoint zeval (zr : positive -> Z) (zl : positive -> list Z) (e : sv) : Z :=
  match e with
  | SLit z => z mod 2 ^ 64
  | SVar i => zr i mod 2 ^ 64
  | SAlu op a b => zalu 64 op (zeval zr zl a) (zeval zr zl b)
  | SAluW op a b => sx32 (zalu 32 op (zeval zr zl a mod 2 ^ 32) (zeval zr zl b mod 2 ^ 32))
  | SMd M_MUL a b => (zeval zr zl a * zeval zr zl b) mod 2 ^ 64
  | SMdW M_MUL a b => sx32 ((zeval zr zl a * zeval zr zl b) mod 2 ^ 32)
  | SMd _ _ _ | SMdW _ _ _ => 0
  | SExt sgn w a => if sgn then (toS (Z.of_N w) (zeval zr zl a)) mod 2 ^ 64
                    else (zeval zr zl a) mod 2 ^ (Z.of_N w)
  | SLBytes l i k => (zle (zsublist (zeval zr zl i) k (zl l))) mod 2 ^ 64
  end.

Fixpoint zsupported (e : sv) : bool :=
  match e with
  | SLit _ | SVar _ => true
  | SAlu _ a b | SAluW _ a b => zsupported a && zsupported b
  | SMd M_MUL a b | SMdW M_MUL a b => zsupported a && zsupported b
  | SMd _ _ _ | SMdW _ _ _ => false
  | SExt _ w a => (0 <? Z.of_N w) && (Z.of_N w <=? 64) && zsupported a
  | SLBytes _ i k => (0 <=? k) && (k <=? 8) && zsupported i
  end.

Definition zr_of (rho : valuation) : positive -> Z := fun i => bv_unsigned (rw rho i).
Definition zl_of (rho : valuation) : positive -> list Z := ltac2:(tb__ "0|2|
S2S36S8Q8M0A1M1S0G1S7G0R1A2Lb;S34Vrho;R1A2A4Ll;").

Lemma two_n : ltac2:(tb__ "0|0|
S1S3S0SbR1A1SfZ2S10R1A1A2A3Fn;").
Proof. intros n. reflexivity. Qed.
Lemma two32 : bv_modulus 32 = 2 ^ 32. Proof. reflexivity. Qed.
Lemma half64 : bv_half_modulus 64 = 2 ^ 63. Proof. reflexivity. Qed.
Lemma half32 : bv_half_modulus 32 = 2 ^ 31. Proof. reflexivity. Qed.

Lemma urange_n : ltac2:(tb__ "0|1|
S1S8R1A1S4S12Z0S7R2R1A2M0A2S11G0SfZ2S10R2A1A2A2A2Fa;Fn;").
Proof. intros n a. rewrite <- two_n. apply bv_unsigned_in_range. Qed.

Lemma bv_swrap_toS : ltac2:(tb__ "0|0|
S1S0S11Z0S10R2A1A2S3S0SdR3R2A2S22S10R3A1R2A2A3F_;Fx;Fn;").
Proof.
  intros n x Hn. unfold bv_swrap, bv_wrap, toS.
  assert (HM : bv_modulus n = 2 ^ Z.of_N n) by apply two_n.
  assert (HH : bv_half_modulus n = 2 ^ (Z.of_N n - 1)).
  { unfold bv_half_modulus. rewrite HM. replace (Z.of_N n) with (Z.of_N n - 1 + 1) at 1 by lia.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r. apply Z.div_mul. lia. }
  rewrite HM, HH.
  set (h := 2 ^ (Z.of_N n - 1)) in *.
  assert (Hh : 0 < h) by (subst h; apply Z.pow_pos_nonneg; lia).
  assert (HM2 : 2 ^ Z.of_N n = 2 * h).
  { subst h. replace (Z.of_N n) with (Z.of_N n - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
  rewrite HM2.
  pose proof (Z.mod_pos_bound x (2 * h) ltac:(lia)) as Hb.
  assert (E1 : (x + h) mod (2 * h) = (x mod (2 * h) + h) mod (2 * h)).
  { rewrite Z.add_mod_idemp_l by lia. reflexivity. }
  rewrite E1.
  destruct (x mod (2 * h) <? h) eqn:E.
  - apply Z.ltb_lt in E. rewrite (Z.mod_small (x mod (2 * h) + h)) by lia. lia.
  - apply Z.ltb_ge in E.
    rewrite <- (Z.mod_unique (x mod (2 * h) + h) (2 * h) 1 (x mod (2 * h) + h - 2 * h)) by lia. lia.
Qed.

Lemma bv_signed_toS : ltac2:(tb__ "0|0|
S1S8R1A1S11Z0S10R2A1A2S3S0ScR3R2A2S22S10R3A1S7R3R2A2A2A3F_;Fa;Fn;").
Proof. intros n a Hn. unfold bv_signed. apply bv_swrap_toS. exact Hn. Qed.

Lemma toS_mod : ltac2:(tb__ "0|0|
S0S0S11Z0R2A2S3S0S22R3SeR2SfZ2R3A2A2A2S22R3R2A2A3F_;Fx;Fn;").
Proof. intros n x Hn. unfold toS. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma toS_mod_back : ltac2:(tb__ "0|1|
S0S0S11Z0R2A2S3S0SeS22R3R2A2SfZ2R3A2M0A2SeR2G0A2A3F_;Fx;Fn;").
Proof.
  intros n x Hn. unfold toS.
  destruct (x mod 2 ^ n <? 2 ^ (n - 1)).
  - apply Z.mod_mod. lia.
  - replace (x mod 2 ^ n - 2 ^ n) with (x mod 2 ^ n + (-1) * 2 ^ n) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma shamt_val_n : ltac2:(tb__ "0|0|
S1S8R1A1S0S6S4S3S0R1Z3fA3S3S1R3Q40A3A2S4S3S0R1Z1fA3S3S1R3Q20A3A2A2S3S0S7R4SaR4R3S9R4R2A2A3A2SeS7R4R3A2S10R4A1A2A3F_;Fm;Fb;Fn;").
Proof.
  intros n b m Hm. rewrite bv_and_unsigned, Z_to_bv_unsigned.
  destruct Hm as [[-> ->]|[-> ->]].
  - change (bv_wrap 64 63) with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
  - change (bv_wrap 32 31) with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma zalu_sound : ltac2:(tb__ "0|0|
S1S0S3aS8R3A1S8R4A1S6S4S3S0R4Z3fA3S3S1R5Q40A3A2S4S3S0R4Z1fA3S3S1R5Q20A3A2A2S3S0S7R6S3eR6R5R4R3R2A5A2S2aS10R6A1R4S7R6R3A2S7R6R2A2A4A3F_;Fb;Fa;Fop;Fm;Fn;").
Proof.
  intros n m op a b Hm.
  assert (Hn : 0 < Z.of_N n) by (destruct Hm as [[_ ->]|[_ ->]]; cbn; lia).
  pose proof (urange_n n a) as Ha. pose proof (urange_n n b) as Hb.
  assert (Ma : bv_unsigned a mod 2 ^ Z.of_N n = bv_unsigned a) by (apply Z.mod_small; lia).
  assert (Mb : bv_unsigned b mod 2 ^ Z.of_N n = bv_unsigned b) by (apply Z.mod_small; lia).
  destruct op; cbn [alu zalu].
  - rewrite bv_add_unsigned. unfold bv_wrap. rewrite two_n. reflexivity.
  - rewrite bv_sub_unsigned. unfold bv_wrap. rewrite two_n. reflexivity.
  - rewrite bv_shiftl_unsigned, (shamt_val_n n b m Hm). unfold bv_wrap. rewrite two_n. reflexivity.
  - unfold bv_lts. rewrite !bv_signed_toS by exact Hn.
    destruct (toS (Z.of_N n) (bv_unsigned a) <? toS (Z.of_N n) (bv_unsigned b));
      rewrite Z_to_bv_unsigned; unfold bv_wrap; rewrite two_n; apply Z.mod_small;
      split; try lia; apply Z.pow_gt_1; lia.
  - unfold bv_ltu. rewrite Ma, Mb.
    destruct (bv_unsigned a <? bv_unsigned b);
      rewrite Z_to_bv_unsigned; unfold bv_wrap; rewrite two_n; apply Z.mod_small;
      split; try lia; apply Z.pow_gt_1; lia.
  - rewrite bv_xor_unsigned, Ma, Mb. reflexivity.
  - rewrite bv_shiftr_unsigned, (shamt_val_n n b m Hm), Ma. reflexivity.
  - rewrite bv_ashiftr_unsigned, (shamt_val_n n b m Hm), bv_signed_toS by exact Hn.
    unfold bv_wrap. rewrite two_n. reflexivity.
  - rewrite bv_or_unsigned, Ma, Mb. reflexivity.
  - rewrite bv_and_unsigned, Ma, Mb. reflexivity.
Qed.

Lemma low32_val : ltac2:(tb__ "0|1|
S8Q40M0A1S3S0S7Q20S40R1A1A2SeS7G0R1A2SfZ2Z20A2A2A3Fw;").
Proof.
  intros w. unfold low32. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0.
  rewrite Z.shiftr_0_r. unfold bv_wrap. rewrite two32. reflexivity.
Qed.

Lemma sext64_32_val : ltac2:(tb__ "0|2|
S8Q20M0A1S3S0S7Q40M1S3dG0G1R1A3A2S27S7G0R1A2A1A3Fv;").
Proof.
  intros v. unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_wrap. rewrite two64.
  unfold sx32. rewrite bv_signed_toS by (cbn; lia). reflexivity.
Qed.

Lemma sx32_mod : ltac2:(tb__ "0|0|
S0S3S0S27SeR1SfZ2Z20A2A2A1S27R1A1A3Fx;").
Proof. intros x. unfold sx32. rewrite toS_mod by lia. reflexivity. Qed.

Lemma ext_low_val : ltac2:(tb__ "0|5|
S1eS1S8Q40M0A1S11Z0S10R2A1A2S12S10R3A1Z40M1A2S3S0S7G0S33R5R4R3A3A2S1eS0Lsgn;R5SeS22S10R4A1M2S7G0R3A2M3A2SfZ2M4G1A2A2SeG3SfG4G2A2A2X1ex2A3F_;F_;Fv;Fw;Fsgn;").
Proof.
  intros sgn w v Hw Hw64. unfold ext_low. destruct sgn.
  - unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_wrap. rewrite two64.
    rewrite bv_signed_toS by exact Hw. rewrite bv_extract_unsigned.
    change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap. rewrite two_n.
    rewrite toS_mod by exact Hw. reflexivity.
  - unfold zext. rewrite bv_zero_extend_unsigned'. rewrite bv_extract_unsigned.
    change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap. rewrite !two_n. change (Z.of_N 64) with 64.
    apply Z.mod_small. pose proof (Z.mod_pos_bound (bv_unsigned v) (2 ^ Z.of_N w) ltac:(apply Z.pow_pos_nonneg; lia)).
    split; [lia|]. eapply Z.lt_le_trans; [apply H|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_byte_shiftl8 : ltac2:(tb__ "0|2|
S0S0S4S12Z0M0R2A2M1S11R2Z100A2A2G1S3S0S17R4S14R3Z8A2A2G0A3F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_dec k 8) as [Hl|Hh].
  - rewrite Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite (SymSoundA.testbit_high_small a 8 k) by lia. reflexivity.
Qed.

Lemma lor_byte_shiftl8 : ltac2:(tb__ "0|2|
S0S0S4S12Z0R2A2M0S11R2Z100M1A2A2G0S3S0S18R4S14R3Z8A2A2S16R4S1dG1R3A2A2A3F_;F_;Fb;Fa;").
Proof.
  intros a b Ha Hb.
  pose proof (land_byte_shiftl8 a b Ha Hb) as HL.
  rewrite <- Z.lxor_lor by exact HL.
  rewrite <- Z.add_nocarry_lxor by exact HL.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia.
Qed.

Lemma zle_nonneg : ltac2:(tb__ "0|0|
S1fS0A1S12Z0S29R1A1A2Fl;").
Proof. induction l as [|x t IH]; cbn; [lia|]. pose proof (Z.mod_pos_bound x 256 ltac:(lia)). lia. Qed.

Lemma bytes_le_to_Z_zle : ltac2:(tb__ "0|2|
S1fS8Q8M0A1M1A1S3S0S3cR1A1S29S36G1S0G1S7G0R1A2Lb;R1A4A1A3Fbs;").
Proof.
  induction bs as [|b t IH]; [reflexivity|]. cbn [bytes_le_to_Z map zle].
  rewrite IH. pose proof (urange_n 8 b) as Hb. change (Z.of_N 8) with 8 in Hb. change (2 ^ 8) with 256 in Hb.
  rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  apply lor_byte_shiftl8; [lia | apply zle_nonneg].
Qed.

Lemma zsublist_map : ltac2:(tb__ "0|3|
S0S0S1fS8Q8M0A1M1A1S3S1fS0A1S36G1S0G1S7G0R1A2Lb;M2S35R3R2R1A3A4S2cR3R2S36G1S0G2R1A4A3A3Fl;Fk;Fi;").
Proof.
  intros i k l. unfold sublist, zsublist. rewrite <- firstn_map, <- skipn_map. reflexivity.
Qed.

Theorem eval_zeval : ltac2:(tb__ "0|0|
S2fS31S3S1eS2dR1A1S20A3S3S0S7Q40S32R3R2A2A2S28S25R3A1S24R3A1R2A3A3F_;Fe;Frho;").
Proof.
  intros rho e. induction e; cbn [zsupported zeval eval]; intros Hs.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. reflexivity.
  - unfold zr_of. symmetry. apply Z.mod_small. apply urange.
  - apply andb_prop in Hs as [H1 H2]. rewrite <- (IHe1 H1), <- (IHe2 H2).
    unfold alu64. apply (zalu_sound 64 63). left; auto.
  - apply andb_prop in Hs as [H1 H2]. rewrite <- (IHe1 H1), <- (IHe2 H2).
    rewrite sext64_32_val. unfold alu32. rewrite (zalu_sound 32 31) by (right; auto).
    rewrite !low32_val. reflexivity.
  - destruct op; try discriminate. apply andb_prop in Hs as [H1 H2]. rewrite <- (IHe1 H1), <- (IHe2 H2).
    cbn [mul_div]. rewrite bv_mul_unsigned. unfold bv_wrap. rewrite two64. reflexivity.
  - destruct op; try discriminate. apply andb_prop in Hs as [H1 H2]. rewrite <- (IHe1 H1), <- (IHe2 H2).
    cbn [mul_div]. rewrite sext64_32_val, bv_mul_unsigned, !low32_val. unfold bv_wrap. rewrite two32.
    rewrite <- (Zmult_mod (bv_unsigned (eval rho e1)) (bv_unsigned (eval rho e2)) (2 ^ 32)). reflexivity.
  - apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.leb_le in H2.
    rewrite <- (IHe H3). apply ext_low_val; assumption.
  - apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2].
    rewrite <- (IHe H3). unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    rewrite bytes_le_to_Z_zle, zsublist_map. reflexivity.
Qed.

Definition zcond (c : branch_cond) (a b : Z) : bool := ltac2:(tb__ "0|4|
S3bS1eLc;Vc;S1bVa;Vb;A2M0S21G0A1S13S22Z40M1Va;A2S22G1Vb;A2A2M2S21G2A1S13Va;Vb;A2M3S21G3A1X3bx6").

Fixpoint zholds (zr : positive -> Z) (zl : positive -> list Z) (p : sprop) : Prop :=
  match p with
  | SPBranch c a b => zcond c (zeval zr zl a) (zeval zr zl b) = true
  | SPNot q => ~ zholds zr zl q
  | SPUlt a b => zeval zr zl a < zeval zr zl b
  | SPUle a b => zeval zr zl a <= zeval zr zl b
  | SPEq a b => zeval zr zl a = zeval zr zl b
  | SPTrue => True
  | SPAlign i a => 0 <= a /\ (zr i mod 2 ^ 64) mod 2 ^ a = 0
  end.

Fixpoint psupported (p : sprop) : bool :=
  match p with
  | SPBranch _ a b | SPUlt a b | SPUle a b | SPEq a b => zsupported a && zsupported b
  | SPNot q => psupported q
  | SPTrue | SPAlign _ _ => true
  end.

Lemma branch_taken_zcond : ltac2:(tb__ "0|2|
S3bS8Q40M0A1M1G1S3S1eS3fR3R2R1A3S2bR3S7G0R2A2S7G0R1A2A3A3Fb;Fa;Fc;").
Proof.
  intros c a b. destruct c; cbn [branch_taken zcond]; unfold bv_eqb, bv_lts, bv_ltu; try reflexivity.
  - rewrite !bv_signed_toS by (cbn; lia). reflexivity.
  - rewrite !bv_signed_toS by (cbn; lia). reflexivity.
Qed.

Theorem holds_zholds : ltac2:(tb__ "0|0|
S2fS2eS3S1eS26R1A1S20A3S5S30R3R2A2S23S25R3A1S24R3A1R2A3A2F_;Fp;Frho;").
Proof.
  intros rho p. induction p; cbn [psupported holds zholds]; intros Hs.
  - apply andb_prop in Hs as [H1 H2]. rewrite branch_taken_zcond, !eval_zeval by assumption. tauto.
  - specialize (IHp Hs). tauto.
  - apply andb_prop in Hs as [H1 H2]. rewrite !eval_zeval by assumption. tauto.
  - apply andb_prop in Hs as [H1 H2]. rewrite !eval_zeval by assumption. tauto.
  - apply andb_prop in Hs as [H1 H2]. rewrite bv_eq. rewrite !eval_zeval by assumption. tauto.
  - tauto.
  - unfold zr_of. rewrite (Z.mod_small (bv_unsigned (rw rho i)) (2 ^ 64)) by apply urange. tauto.
Qed.

Corollary holds_of_zholds : ltac2:(tb__ "0|0|
S2fS2eS3S1eS26R1A1S20A3S23S25R3A1S24R3A1R2A3S30R4R3A2F_;F_;Fp;Frho;").
Proof. intros rho p Hs Hz. apply (proj2 (holds_zholds rho p Hs)). exact Hz. Qed.

Lemma Forall_holds_of_zholds : ltac2:(tb__ "0|0|
S2fS1fS2eA1S3S1eS41S2eS26R1A3S20A3S37S2eS23S25R3A1S24R3A1A2R2A3S37S2eS30R4A1R3A3F_;F_;Fps;Frho;").
Proof.
  intros rho ps Hs Hz. apply Forall_forall. intros p Hp. apply holds_of_zholds.
  - exact (proj1 (forallb_forall _ _) Hs p Hp).
  - exact (proj1 (Forall_forall _ _) Hz p Hp).
Qed.

Lemma zeval_ext : ltac2:(tb__ "0|4|
S2S0Fx;M0G0S2S1fS0A1M1Fx;M2G2S31S2S3S0R6R1A1R5R1A1M3A3Fi;S2S3G1G3R4R1A1A3Fl;S3S0S28R7R5R3A3S28R6R4R3A3A3F_;F_;Fe;Fzl';Fzl;Fzr';Fzr;").
Proof.
  intros zr zr' zl zl' e Hr Hl. induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe, ?Hr, ?Hl; reflexivity.
Qed.

Lemma zholds_ext : ltac2:(tb__ "0|4|
S2S0Fx;M0G0S2S1fS0A1M1Fx;M2G2S2eS2S3S0R6R1A1R5R1A1M3A3Fi;S2S3G1G3R4R1A1A3Fl;S5S23R7R5R3A3S23R6R4R3A3A2F_;F_;Fp;Fzl';Fzl;Fzr';Fzr;").
Proof.
  intros zr zr' zl zl' p Hr Hl. induction p; cbn; rewrite ?(zeval_ext zr zr' zl zl') by assumption; try tauto.
  rewrite Hr. tauto.
Qed.
