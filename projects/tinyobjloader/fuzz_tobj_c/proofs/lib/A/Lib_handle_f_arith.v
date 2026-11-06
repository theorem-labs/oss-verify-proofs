(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "le"; "modulo"; "sub"; "pow"; "div"; "land"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "SAlu"; "SLit"; "sprop"; "SPUle"; "soff"; "SVar"; "holds"; "sv"; "SMd"; "rw"; "valuation"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_arith"; "pA"; "o16A"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "needA"; "oRFXe"; "o4A"; "M16"; "orfx"; "vDTS"; "vKTS"; "M32"; "a16"; "ts_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_arith.TS"; "pNXT'"; "pPRV'"; "pRFX'"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "M64v"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pA : sv := SVar 418.
Definition vDTS : positive := 350%positive. Definition vKTS : positive := 351%positive.
Definition M16 : sv := SLit 18446744073709551600. Definition M32 : sv := SLit 18446744073709551584.
Definition needA : sv := ltac2:(tb__ "0|1|
SeS1bSeS1bSeS1cSeS1bSeS1dS20SfZ3A1M0A3SfZ1eA1A3S2dA3SeS1dS20SfZ4A1A3A3SeS1cSeS1bSeS1eSeS1bS20SfZ7A1A3G0A3SfZfA1A3S29A3A3").
Definition a16 : sv := ltac2:(tb__ "0|0|
SeS1cSeS1bSeS1dS20SfZ2A1A3SfZfA1A3S29A3").
Definition o16A : sv := SAlu ALU_SLL pA (SLit 4).
Definition o4A : sv := SAlu ALU_SLL pA (SLit 2).
Definition orfx : sv := ltac2:(tb__ "0|0|
SeS1eSeS1bS20SfZ7A1A3SfZ3A1A3").
Definition oNXTe : sv := SAlu ALU_ADD o16A o4A.
Definition oPRV : sv := SAlu ALU_ADD o16A a16.
Definition oPRVe : sv := SAlu ALU_ADD oPRV o4A.
Definition oRFX : sv := SAlu ALU_ADD oPRV a16.
Definition oRFXe : sv := SAlu ALU_ADD oRFX orfx.
Definition ts_facts : list sprop := ltac2:(tb__ "0|1|
S19S10S11S22S23A2S19S10S11S24S25A2S19S10S11S22S13S2cA1M0A2S19S10S11S23G0A2S19S10S11S24G0A2S19S10S11S25G0A2S19S10S11S27G0A2S19S10S11SfZ0A1S21A2S19S10S11S21S22A2S19S10S11S23S24A2S19S10S11S25S27A2S1aS10A1A3A3A3A3A3A3A3A3A3A3A3").

Definition need_facts : list sprop := ltac2:(tb__ "0|0|
S19S10S11S26S16S1fSfZ25A1S20A3A2S19S10S11S26SfZ10000000000A1A2S1aS10A1A3A3").

Lemma ts_arith : ltac2:(tb__ "0|b|
S9S9SbS2Z4M0R2A2S2R2S5Z2M1Z14A2A2A2S4S0S1G0R3A2ZfM2A2M3S3G3Z10M4A2A2S9S6S0R4Z7M5A2Z8M6A2S9S4S0R1G2A2M7S3G7G4A2A2S9S4S0S1G6R6A2Z1eA2M8S3G8Z20A2A2S9S2S0S0R1S1G4R7A2A2R2A2R6A2SbS2S1G0R8A2M9R5A2SbS2R5S0G9G2A2A2SbSbS2Z0R4A2S2R4S0R8G5A2A2A2SbS2R4R3A2SbS2R3S0R4G2A2A2SbSaS9R2S1G1R5A2MaA3S2S0S0S1G4R8A2GaA2R4A2R7A2A2A2A2A2A2A2F_;Tx1;Tx2;Tr8;Tx16;F_;Fk;Fa;").
Proof.
  intros a k Ha x16 r8 x2 x1 Hk.
  pose proof (Z.mod_pos_bound (4 * a + 15) 16 ltac:(lia)) as MM16.
  assert (R8 : 0 <= r8 <= a + 7). { subst r8. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
  pose proof (Z.mod_pos_bound (r8 + 15) 16 ltac:(lia)) as M2.
  assert (X1 : x1 = 2 * x16).
  { subst x1 x16. replace (8 * a + 30) with (2 * (4 * a + 15)) by lia.
    change 32 with (2 * 16). rewrite (Z.mul_mod_distr_l (4 * a + 15) 16 2) by lia. lia. }
  repeat split; try lia.
Qed.

Lemma U_and_lit : ltac2:(tb__ "0|1|
S18S15S9SaS9ScQ40M0SdR3SeS1cR2SfR1A1A3A2A2S7ScG0SdR3R2A2A2S3R1S34A2A2A3Fm;Fa;Frho;").
Proof. intros. cbn [eval]. rewrite and_val, lit_unsigned, M64v_eq. reflexivity. Qed.

Section TS.
Variable rho : valuation.
Let a := bv_unsigned (rw rho 418).
Let k := bv_unsigned (rw rho vKTS).
Hypothesis Ha : 4 <= a <= 2 ^ 20.
Let x16 : ltac2:(tb__ "0|0|
S9") := ltac2:(tb__ "0|1|
S4S0S1Z4Va;A2ZfA2M0S3G0Z10A2A2").
Let r8 := (a + 7) / 8.

Lemma U_pA : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S20A2A2Va;A3"). Proof using . reflexivity. Qed.
Lemma U_o16A : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S21A2A2S1Z10Va;A2A3").
Proof using Ha. unfold o16A. rewrite U_sll_lit, U_pA. change (2 ^ (4 mod 64)) with 16. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_o4A : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S28A2A2S1Z4Va;A2A3").
Proof using Ha. unfold o4A. rewrite U_sll_lit, U_pA. change (2 ^ (2 mod 64)) with 4. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_a16 : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S2eA2A2Vx16;A3").
Proof using Ha.
  unfold a16. fold o4A. unfold M16. rewrite U_and_lit, U_add, U_o4A, U_lit. unfold M64v.
  change (15 mod 18446744073709551616) with 15. change (18446744073709551600 mod 18446744073709551616) with (2 ^ 64 - 2 ^ 4).
  rewrite Z.mod_small by lia. rewrite land_high_mask by lia. subst x16. change (2 ^ 4) with 16. lia.
Qed.
Lemma U_orfx : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S2aA2A2Vr8;A3").
Proof using Ha.
  unfold orfx. rewrite U_srl_lit, U_add, U_pA, U_lit. unfold M64v. change (7 mod 18446744073709551616) with 7.
  change (2 ^ (3 mod 64)) with 8. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma x16_range : ltac2:(tb__ "0|1|
SbS2S1Z4Va;A2M0Vx16;A2S2Vx16;S0G0ZfA2A2A2").
Proof using k r8. pose proof (Z.mod_pos_bound (4 * a + 15) 16 ltac:(lia)). subst x16. lia. Qed.
Lemma r8_range : ltac2:(tb__ "0|0|
SbS2Z0Vr8;A2S2Vr8;S0Va;Z7A2A2A2").
Proof using Ha k x16. subst r8. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.
Lemma U_oNXTe : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S22A2A2S0S1Z10Va;A2S1Z4Va;A2A2A3").
Proof using Ha. unfold oNXTe. rewrite U_add, U_o16A, U_o4A. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_oPRV : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S23A2A2S0S1Z10Va;A2Vx16;A2A3").
Proof using Ha. pose proof x16_range. unfold oPRV. rewrite U_add, U_o16A, U_a16. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_oPRVe : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S24A2A2S0S0S1Z10Va;A2Vx16;A2S1Z4Va;A2A2A3").
Proof using Ha. pose proof x16_range. unfold oPRVe. rewrite U_add, U_oPRV, U_o4A. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_oRFX : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S25A2A2S0S0S1Z10Va;A2Vx16;A2Vx16;A2A3").
Proof using Ha. pose proof x16_range. unfold oRFX. rewrite U_add, U_oPRV, U_a16. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_oRFXe : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S27A2A2S0S0S0S1Z10Va;A2Vx16;A2Vx16;A2Vr8;A2A3").
Proof using Ha. pose proof x16_range. pose proof r8_range. unfold oRFXe. rewrite U_add, U_oRFX, U_orfx. unfold M64v. rewrite Z.mod_small by lia. lia. Qed.
Lemma U_needA : ltac2:(tb__ "0|3|
SaS9ScQ40SdVrho;S26A2A2S0S0S4S0S1Z8Va;A2Z1eA2M0S3G0Z20A2A2S1Z10M1Va;A2A2S4S0Vr8;ZfA2M2S3G2G1A2A2A2A3").
Proof using Ha.
  pose proof r8_range.
  unfold needA, M16, M32. rewrite U_add, U_add, U_and_lit, U_add, U_sll_lit, U_lit, U_sll_lit, U_and_lit, U_add, U_lit.
  fold orfx. rewrite U_orfx, !U_pA. unfold M64v.
  change (2 ^ (3 mod 64)) with 8. change (2 ^ (4 mod 64)) with 16.
  change (30 mod 18446744073709551616) with 30. change (15 mod 18446744073709551616) with 15.
  change (18446744073709551584 mod 18446744073709551616) with (2 ^ 64 - 2 ^ 5).
  change (18446744073709551600 mod 18446744073709551616) with (2 ^ 64 - 2 ^ 4).
  rewrite (Z.mod_small (a * 8)) by lia. rewrite (Z.mod_small (a * 8 + 30)) by lia. rewrite (Z.mod_small (a * 16)) by lia.
  rewrite (Z.mod_small (r8 + 15)) by lia.
  rewrite !land_high_mask by lia.
  pose proof (Z.mod_pos_bound (a * 8 + 30) (2 ^ 5) ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 15) (2 ^ 4) ltac:(lia)).
  change (2 ^ 5) with 32 in *. change (2 ^ 4) with 16 in *.
  rewrite (Z.mod_small (a * 8 + 30 - _ + a * 16)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma need_facts_ok : Forall (holds rho) need_facts.
Proof using Ha.
  pose proof r8_range as R. pose proof U_needA as N.
  pose proof (Z.mod_pos_bound (8 * a + 30) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (r8 + 15) 16 ltac:(lia)).
  assert (B : bv_unsigned (eval rho needA) <= 37 * a) by (rewrite N; subst r8; pose proof (Z.div_le_upper_bound (a+7) 8 (a) ltac:(lia)); nia).
  unfold need_facts. repeat constructor; cbn [holds].
  - rewrite U_mul, U_lit, U_pA. unfold M64v. change (37 mod 18446744073709551616) with 37. rewrite Z.mod_small by lia. lia.
  - rewrite U_lit. unfold M64v. change (1099511627776 mod 18446744073709551616) with 1099511627776. lia.
Qed.

Lemma ts_facts_ok : ltac2:(tb__ "0|0|
S14Vrho;S11S26S13S2cA1A2A2S33S10S14Vrho;A1S2fA3F_;").
Proof using Ha.
  intros Hn. cbn [holds] in Hn. rewrite U_needA in Hn. change (bv_unsigned (eval rho (SVar vKTS))) with k in Hn.
  pose proof x16_range as X. pose proof r8_range as R.
  destruct (ts_arith a k Ha Hn) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  unfold ts_facts. repeat constructor; cbn [holds];
    rewrite ?U_oNXTe, ?U_oPRV, ?U_oPRVe, ?U_oRFX, ?U_oRFXe, ?U_o16A, ?U_lit; try change (bv_unsigned (eval rho (SVar vKTS))) with k; unfold M64v; try lia.
Qed.

Definition pNXT' : sv := ltac2:(tb__ "0|0|
SeS1bS13S2bA1S21A3").
Definition pPRV' : sv := SAlu ALU_ADD pNXT' a16.
Definition pRFX' : sv := SAlu ALU_ADD pPRV' a16.
Hypothesis Hd : ltac2:(tb__ "0|0|
S2ScQ40S17Vrho;S2bA2A2Z7fff7f800000A2").
Let d := bv_unsigned (rw rho vDTS).
Lemma d_range : 0 <= d.
Proof using Ha k r8 x16. pose proof (bv_urange (rw rho vDTS)). lia. Qed.
Lemma U_pNXT' : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S30A2A2S0Vd;S1Z10Va;A2A2A3").
Proof using Ha Hd. pose proof d_range. unfold pNXT'. rewrite U_add, U_o16A. cbn [eval]. fold d. unfold M64v. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma U_pPRV' : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S31A2A2S0S0Vd;S1Z10Va;A2A2Vx16;A2A3").
Proof using Ha Hd. pose proof d_range. pose proof x16_range. unfold pPRV'. rewrite U_add, U_pNXT', U_a16. unfold M64v. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma U_pRFX' : ltac2:(tb__ "0|0|
SaS9ScQ40SdVrho;S32A2A2S0S0S0Vd;S1Z10Va;A2A2Vx16;A2Vx16;A2A3").
Proof using Ha Hd. pose proof d_range. pose proof x16_range. unfold pRFX'. rewrite U_add, U_pPRV', U_a16. unfold M64v. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma soff_smallU : ltac2:(tb__ "0|1|
S15S8ScQ40M0SdVrho;R1A2A2S5Z2Z3fA2A2SaS9S12Vrho;R2A2ScG0SdVrho;R2A2A2A3F_;Fe;").
Proof using .
  intros e He. unfold soff. rewrite bv_signed_U. pose proof (bv_urange (eval rho e)).
  destruct (Zsigned_spec (bv_unsigned (eval rho e))) as [[_ X]|[X _]]; [exact X | exfalso; lia].
Qed.
Lemma nxt_eqs : ltac2:(tb__ "0|1|
SbSaS9S0ScQ40SdVrho;S30A2A2M0S12Vrho;SfZ0A1A2A2S0Vd;S12Vrho;S21A2A2A3SaS9S0G0S12Vrho;S28A2A2S0Vd;S12Vrho;S22A2A2A3A2").
Proof using Ha Hd.
  pose proof d_range. pose proof x16_range. rewrite U_pNXT', soff_lit_small by lia.
  rewrite !soff_smallU by (rewrite ?U_o16A, ?U_o4A, ?U_oNXTe; lia). rewrite U_o16A, U_o4A, U_oNXTe. lia.
Qed.
Lemma prv_eqs : ltac2:(tb__ "0|1|
SbSaS9S0ScQ40SdVrho;S31A2A2M0S12Vrho;SfZ0A1A2A2S0Vd;S12Vrho;S23A2A2A3SaS9S0G0S12Vrho;S28A2A2S0Vd;S12Vrho;S24A2A2A3A2").
Proof using Ha Hd.
  pose proof d_range. pose proof x16_range. rewrite U_pPRV', soff_lit_small by lia.
  rewrite !soff_smallU by (rewrite ?U_oPRV, ?U_o4A, ?U_oPRVe; lia). rewrite U_oPRV, U_o4A, U_oPRVe. lia.
Qed.
Lemma rfx_eqs : ltac2:(tb__ "0|1|
SbSaS9S0ScQ40SdVrho;S32A2A2M0S12Vrho;SfZ0A1A2A2S0Vd;S12Vrho;S25A2A2A3SaS9S0G0S12Vrho;S2aA2A2S0Vd;S12Vrho;S27A2A2A3A2").
Proof using Ha Hd.
  pose proof d_range. pose proof x16_range. pose proof r8_range. rewrite U_pRFX', soff_lit_small by lia.
  rewrite !soff_smallU by (rewrite ?U_oRFX, ?U_orfx, ?U_oRFXe; lia). rewrite U_oRFX, U_orfx, U_oRFXe. lia.
Qed.
End TS.
