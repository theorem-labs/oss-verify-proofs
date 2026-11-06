(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "not"; "iff"; "and"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "land"; "lor"; "modulo"; "sub"; "testbit"; "to_nat"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes"; "nthb"; "HI"; "C1M"; "BNZ"; "BZ"; "M64"; "NOZ"; "WRD"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "SLit"; "rl"; "sv"; "valuation"; "SExt"; "SLBytes"; "SPBranch"; "holds"; "SAlu"; "sublist"; "SPNot"; "@Corelib.Init.Datatypes"; "false"; "nat"; "list"; "bool"; "length"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_NE"; "ALU_AND"; "ALU_OR"; "ALU_SUB"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HasZero.HZ"; "Tz"; "zb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import HasZero.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition nthb (l : list byte) (i : Z) : Z := ltac2:(tb__ "0|1|
S19Q8M0S35S1aG0A1SfVi;A1Vl;S1bG0Z0A2A4A2").

Lemma sublist_1 : ltac2:(tb__ "0|0|
S0S2aS1aQ8A1A1S5Z0R2A2S1S0S2fS26R3Z1R2A3A1S11R2R3A2A3F_;Fl;Fi;").
Proof.
  intros i l Hi. unfold sublist, nthb. change (Z.to_nat 1) with 1%nat.
  remember (Z.to_nat i) as n. clear Heqn Hi i. revert n.
  induction l as [|b t IH]; intros n.
  - rewrite skipn_nil. cbn. destruct n; cbn; rewrite Z_to_bv_unsigned; reflexivity.
  - destruct n as [|n]; cbn.
    + rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
    + apply IH.
Qed.

Lemma byte_load_val : ltac2:(tb__ "0|2|
S20S1fS1S0S19Q40M0S1cR2S21S28Q8S22P3M1R1Z1A3A3A2A2S11S1eR2G1A2S19G0S1cR2R1A2A2A2A3Fe;Frho;").
Proof.
  intros rho e. cbn [eval]. unfold le_bytes_to_word. rewrite sublist_1 by apply (proj1 (urange _)).
  assert (R : 0 <= nthb (rl rho 3) (bv_unsigned (eval rho e)) < 256).
  { unfold nthb. pose proof (bv_unsigned_in_range _ (nth (Z.to_nat (bv_unsigned (eval rho e))) (rl rho 3) (Z_to_bv 8 0))) as X.
    change (bv_modulus 8) with 256 in X. lia. }
  unfold ext_low, zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned, Z_to_bv_unsigned.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap. rewrite two64.
  change (bv_modulus 8) with 256.
  set (v := nthb (rl rho 3) (bv_unsigned (eval rho e))) in *.
  rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

Definition C1M : Z := 72340172838076672.
Definition HI : Z := 9259542123273814144.
Definition M64 : Z := 18446744073709551615.

Lemma testbit_M64 : ltac2:(tb__ "0|0|
S0S5Z0R1A2S1S2bSeS16R2A2S10R2Z40A2A3F_;Fi;").
Proof.
  intros i Hi. change M64 with (Z.ones 64).
  destruct (Z.ltb_spec i 64); [apply Z.ones_spec_low; lia | apply Z.ones_spec_high; lia].
Qed.

Lemma testbit_small_high : ltac2:(tb__ "0|1|
S0S0S4S5Z0R2A2S7R2S9Z2Z40M0A2A2A2S5G0R2A2S1S2bSeR4R3A2S28A3F_;F_;Fi;Fx;").
Proof.
  intros x i Hx Hi. destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma noz_Tz : ltac2:(tb__ "0|2|
S0S4S5Z0M0R1A2S7R1S9Z2Z40A2M1A2A2S1S0SaSbScSdS13R2A2G1A2R2A2S12A2S12A3S1S0S36R3A1G0A3F_;F_;Fx;").
Proof.
  intros x Hx E.
  set (y := (x + HZ.ONESNEG) mod 2 ^ 64).
  assert (Hy : 0 <= y < 2 ^ 64) by (subst y; apply Z.mod_pos_bound; lia).
  assert (Ec : (C1M - x) mod 2 ^ 64 = Z.lxor y M64).
  { unfold M64. rewrite lxor_ones64 by exact Hy. subst y. unfold HZ.ONESNEG, C1M.
    replace (x + 18374403900871474943) with ((x - 72340172838076673) + 1 * 2 ^ 64) by (cbn; lia).
    rewrite Z.mod_add by lia.
    replace (72340172838076672 - x) with (-(x - 72340172838076673) - 1) by lia.
    set (u := x - 72340172838076673).
    destruct (Z.lt_ge_cases u 0).
    - rewrite (Z.mod_small (- u - 1)) by (cbn in *; lia).
      replace u with ((u + 2 ^ 64) + (-1) * 2 ^ 64) at 2 by lia. rewrite Z.mod_add by lia.
      rewrite Z.mod_small by (cbn in *; lia). lia.
    - rewrite (Z.mod_small u) by (cbn in *; lia).
      replace (- u - 1) with ((2 ^ 64 - 1 - u) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
      rewrite Z.mod_small by (cbn in *; lia). lia. }
  rewrite Ec in E.
  unfold HZ.Tz. fold y. change HZ.ALLONES with M64. change HZ.HIGHS with HI.
  apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
  pose proof (f_equal (fun w => Z.testbit w i) E) as Ei. cbn beta in Ei.
  rewrite !Z.land_spec, !Z.lor_spec, !Z.lxor_spec in *.
  rewrite testbit_M64 in * by lia.
  destruct (Z.ltb_spec i 64).
  - destruct (Z.testbit y i), (Z.testbit x i), (Z.testbit HI i); cbn in *; congruence.
  - rewrite (testbit_small_high y i) by lia. reflexivity.
Qed.

Lemma noz_bytes : ltac2:(tb__ "0|5|
S2aS1aQ8M0A1M1A1S1S29S2cG1R1A2U8M2A3S1S0SaSbScSdS13S2fR2A1M3A2S9Z2Z40A2A2G3A2S12A2S12A3S29S2dR1G2A2S2S1S0S19G0S35G1R2R5S1bG0Z0M4A2A4A2G4A3A1F_;Fi;F_;F_;Fbs;").
Proof.
  intros bs Hlen E.
  pose proof (bytes_le_to_Z_range bs Hlen) as R.
  pose proof (noz_Tz _ R E) as T.
  set (x := bytes_le_to_Z bs) in *.

  assert (A : forall n, (n <= 8)%nat -> forall k, (k < n)%nat -> HZ.zb x k <> 0).
  { induction n as [|n IH]; intros Hn k Hk; [lia|].
    destruct (Nat.eq_dec k n) as [->|Hne]; [|apply IH; lia].
    intros Zn. apply (HZ.Tz_haszero x n R ltac:(lia) Zn); [|exact T]. intros j Hj. apply IH; lia. }
  intros i Hi. rewrite <- (zb_of_bytes bs i) by (rewrite Hlen; exact Hi). apply (A 8%nat); lia.
Qed.

Definition BNZ (e : sv) : sprop := ltac2:(tb__ "0|0|
S23S31S21S28Q8S22P3Ve;Z1A3A3S1dZ0A1A3").
Definition BZ (e : sv) : sprop := ltac2:(tb__ "0|0|
S27S23S31S21S28Q8S22P3Ve;Z1A3A3S1dZ0A1A3A1").
Definition WRD (e : sv) : sv := SLBytes 3 e 8.
Definition NOZ (e : sv) : sprop := ltac2:(tb__ "0|2|
S23S30S25S32S25S33S25S34S1dZ101010101010100A1S18Ve;A1M0A3G0A3S1dZ8080808080808080A1M1A3G1A3").

Lemma holds_BNZ : ltac2:(tb__ "0|0|
S20S1fS3S24R2S14R1A1A2S2S1S0S11S1eR2P3A2S19Q40S1cR2R1A2A2A2Z0A3A1A2Fe;Frho;").
Proof.
  intros rho e. unfold BNZ. cbn [holds branch_taken]. unfold bv_eqb.
  rewrite byte_load_val. cbn [eval]. rewrite lit_unsigned. change (0 mod 2 ^ 64) with 0.
  rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
Qed.

Lemma holds_BZ : ltac2:(tb__ "0|0|
S20S1fS3S24R2S15R1A1A2S1S0S11S1eR2P3A2S19Q40S1cR2R1A2A2A2Z0A3A2Fe;Frho;").
Proof.
  intros rho e. unfold BZ. change (holds rho (SPNot (BNZ e))) with (~ holds rho (BNZ e)).
  pose proof (holds_BNZ rho e) as [H1 H2]. split; intros H.
  - destruct (Z.eq_dec (nthb (rl rho 3) (bv_unsigned (eval rho e))) 0) as [E|E]; [exact E|].
    exfalso. apply H. apply H2. exact E.
  - intros HB. exact (H1 HB H).
Qed.

Lemma holds_BNZ' : ltac2:(tb__ "0|2|
S20S1fS3S24R2S27S23S30S21S28Q8S22P3M0R1Z1A3A3S1dZ0M1A1A3A1A2S2S1S0S11S1eR2G0A2S19Q40S1cR2R1A2A2A2G1A3A1A2Fe;Frho;").
Proof.
  intros rho e. cbn [holds branch_taken]. unfold bv_eqb.
  rewrite byte_load_val. cbn [eval]. rewrite lit_unsigned. change (0 mod 2 ^ 64) with 0.
  rewrite Z.eqb_eq. tauto.
Qed.

Lemma holds_BZ' : ltac2:(tb__ "0|2|
S20S1fS3S24R2S23S30S21S28Q8S22P3M0R1Z1A3A3S1dZ0M1A1A3A2S1S0S11S1eR2G0A2S19Q40S1cR2R1A2A2A2G1A3A2Fe;Frho;").
Proof.
  intros rho e. cbn [holds branch_taken]. unfold bv_eqb.
  rewrite byte_load_val. cbn [eval]. rewrite lit_unsigned. change (0 mod 2 ^ 64) with 0.
  rewrite Z.eqb_eq. tauto.
Qed.

Lemma length_sublist_le : ltac2:(tb__ "0|1|
S0S0S2aS1aQ8A1M0A1S2eS2cG0S26R3R2R1A3A2SfR2A1A2Fl;Fk;Fi;").
Proof. intros. unfold sublist. rewrite length_firstn. lia. Qed.

Lemma nthb_sublist8 : ltac2:(tb__ "0|0|
S2aS1aQ8A1A1S0S29S5Z0R2A2S2dR2U8A2S1S0S37S2fS26R4Z8R5A3A1R3A2S11R5S6R4S8R3A1A2A2A3F_;F_;Fk;Fi;Fl;").
Proof.
  intros l i k Hi Hk.
  destruct (Nat.lt_ge_cases k (length (sublist i 8 l))) as [Hlt|Hge].
  - rewrite zb_of_bytes by exact Hlt. unfold nthb, sublist.
    rewrite nth_firstn. destruct (Nat.ltb_spec k (Z.to_nat 8)); [|lia].
    rewrite nth_skipn. f_equal. f_equal. lia.
  - unfold HZ.zb. pose proof (bytes_le_to_Z_bound (sublist i 8 l)) as B.
    assert (P : 2 ^ (8 * Z.of_nat (length (sublist i 8 l))) <= 2 ^ (8 * Z.of_nat k)) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.div_small by lia. cbn.
    unfold nthb. rewrite nth_overflow; [rewrite Z_to_bv_unsigned; reflexivity|].
    unfold sublist in Hge. rewrite length_firstn, length_skipn in Hge. lia.
Qed.

Lemma holds_NOZ : ltac2:(tb__ "0|0|
S20S1fS24R2S17R1A1A2S29S2dR1U8A2S2S1S0S11S1eR5P3A2S6S19Q40S1cR5R4A2A2S8R2A1A2A2Z0A3A1F_;Fk;F_;Fe;Frho;").
Proof.
  intros rho e H k Hk. unfold NOZ, WRD in H. cbn [holds branch_taken eval] in H. unfold bv_eqb in H.
  apply Z.eqb_eq in H. rewrite and_val, or_val, sub_val, !lit_unsigned in H.
  change (72340172838076672 mod 2 ^ 64) with C1M in H. change (9259542123273814144 mod 2 ^ 64) with HI in H.
  unfold le_bytes_to_word in H. rewrite Z_to_bv_unsigned in H.
  set (bs := sublist (bv_unsigned (eval rho e)) 8 (rl rho 3)) in *.
  pose proof (bytes_le_to_Z_bound bs) as B. pose proof (length_sublist_le (bv_unsigned (eval rho e)) 8 (rl rho 3)) as L. fold bs in L.
  assert (R : 0 <= bytes_le_to_Z bs < 2 ^ 64).
  { assert (2 ^ (8 * Z.of_nat (length bs)) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
  unfold bv_wrap in H. rewrite two64 in H. rewrite !(Z.mod_small (bytes_le_to_Z bs) (2 ^ 64)) in H by exact R.
  rewrite <- (nthb_sublist8 (rl rho 3) (bv_unsigned (eval rho e)) k) by (try lia; apply (proj1 (urange _))).
  fold bs. revert k Hk.

  assert (A : forall n, (n <= 8)%nat -> forall k, (k < n)%nat -> HZ.zb (bytes_le_to_Z bs) k <> 0).
  { induction n as [|n IH]; intros Hn k Hk; [lia|].
    destruct (Nat.eq_dec k n) as [->|Hne]; [|apply IH; lia].
    intros Zn. apply (HZ.Tz_haszero _ n R ltac:(lia) Zn); [| exact (noz_Tz _ R H)]. intros j Hj. apply IH; lia. }
  intros k Hk. apply (A 8%nat); lia.
Qed.

Section Pure.
Variable l : list byte. Variable z : Z.
Hypothesis FN0 : nthb l z = 0.
Hypothesis FN1 : ltac2:(tb__ "0|1|
S0S4S5Z0M0R1A2S7R1Vz;A2A2S2S1S0S11Vl;R2A2G0A3A1F_;Fi;").
Lemma fn_step : ltac2:(tb__ "0|1|
S0S5Z0M0R1A2S5R2Vz;A2S2S1S0S11Vl;R3A2G0A3A1S5S6R4Z1A2Vz;A2F_;F_;F_;Fc;").
Proof using FN0. intros c Hc Hle Hnz. destruct (Z.eq_dec c z) as [->|]; [contradiction|lia]. Qed.
Lemma fn_found : ltac2:(tb__ "0|1|
S0S5Z0M0R1A2S5R2Vz;A2S1S0S11Vl;R3A2G0A3S1S0R4Vz;A3F_;F_;F_;Fc;").
Proof using FN1. intros c Hc Hle Hz. destruct (Z.eq_dec c z) as [->|]; [reflexivity|]. exfalso. apply (FN1 c); lia. Qed.
Lemma fn_word : ltac2:(tb__ "0|1|
S0S5Z0M0R1A2S5R2Vz;A2S29S2dR1U8A2S2S1S0S11Vl;S6R5S8R2A1A2A2G0A3A1F_;Fk;S5S6R4Z8A2Vz;A2F_;F_;F_;Fc;").
Proof using FN0.
  intros c Hc Hle Hnz. destruct (Z.lt_ge_cases z (c + 8)); [|lia]. exfalso.
  apply (Hnz (Z.to_nat (z - c))); [lia|]. rewrite Z2Nat.id by lia. replace (c + (z - c)) with z by lia. exact FN0.
Qed.
End Pure.
