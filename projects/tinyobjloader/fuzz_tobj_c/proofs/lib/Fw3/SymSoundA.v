(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "iff"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "bv_and"; "bv_extract"; "bv_or"; "bv_sub"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "pow"; "le"; "lt"; "sub"; "add"; "divide"; "land"; "testbit"; "opp"; "lor"; "mul"; "of_nat"; "shiftl"; "shiftr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sv"; "valuation"; "sprop"; "holds"; "SLit"; "ext_low"; "rw"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "ffmt"; "aluop"; "awidth"; "csrop"; "fcvt_ty"; "msize"; "mulop"; "ALU_ADD"; "ALU_SUB"; "Ecall"; "amoop"; "branch_cond"; "fariop"; "fcmpop"; "fmaop"; "fminmaxop"; "fmvdir"; "fsgnop"; "ALU_AND"; "ALU_OR"; "ALU_SLL"; "ALU_SRL"; "M_MUL"; "@Corelib.Init.Datatypes"; "Some"; "bool"; "option"; "list"; "prod"; "false"; "None"; "pair"; "nat"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "low32"; "alu32"; "mul_div"; "core"; "Core"; "c_fcsr"; "c_fregs"; "c_pc"; "c_regs"; "c_resv"; "exec"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "machine_result"; "Build_machine_state"; "MachineFault"; "MachineOk"; "MachineUnmodeled"; "ms_fcsr"; "ms_fregs"; "ms_mem"; "ms_pc"; "ms_pc_val"; "ms_regs"; "ms_resv"; "ms_rom"; "step"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "zext"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "snorm"; "addk_base"; "align_sum"; "as_addlit"; "tzb"; "add_cancel"; "addlit_view"; "align_lin"; "align_of"; "align_sv"; "and_mask_fold"; "and_mask_fold2"; "and_mask_gen"; "high_mask_j"; "instr_at"; "lit_align"; "lit_of"; "mk_add_nn"; "mk_addk"; "mk_alu"; "mk_alu_f"; "mk_alu_ln"; "mk_alu_nl"; "mk_alu_nn"; "mk_aluw"; "mk_ext"; "mk_md"; "mk_mdw"; "mk_sub_nn"; "snormc"; "zmod64"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SpecBridge"; "interp_eff0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA"; "core_of"; "lift_result"; "ms_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Export SpecBridge.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma two64 : bv_modulus 64 = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma urange : ltac2:(tb__ "0|2|
S8Q40M0A1S4S12Z0S9G0R1A2M1A2S13G1S11Z2Z40A2A2A2Fa;").
Proof. intros a. pose proof (bv_unsigned_in_range 64 a). rewrite two64 in H. exact H. Qed.

Lemma Z_to_bv64_mod : ltac2:(tb__ "0|1|
S0S3S8Q40M0A1SaG0S10R1S11Z2Z40A2A2A2SaG0R1A2A3Fz;").
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite two64. apply Z.mod_mod. lia.
Qed.

Lemma Z_to_bv64_eq_iff : ltac2:(tb__ "0|2|
S0S0S7S3S8Q40M0A1SaG0R2A2SaG0R1A2A3S3S0S10R2S11Z2Z40A2M1A2S10R1G1A2A3A2Fy;Fx;").
Proof.
  intros x y. rewrite bv_eq, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. tauto.
Qed.

Lemma snorm_mod : ltac2:(tb__ "0|1|
S0S3S0S10S66R1A1S11Z2Z40A2M0A2S10R1G0A2A3Fz;").
Proof.
  intros z. unfold snorm.
  destruct (Z.ltb_spec (z mod 2 ^ 64) (2 ^ 63)).
  - apply Z.mod_mod. lia.
  - replace (z mod 2 ^ 64 - 2 ^ 64) with (z mod 2 ^ 64 + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma Z_to_bv64_snorm : ltac2:(tb__ "0|1|
S0S3S8Q40M0A1SaG0S66R1A1A2SaG0R1A2A3Fz;").
Proof. intros z. apply Z_to_bv64_eq_iff. apply snorm_mod. Qed.

Lemma zmod64_eq : ltac2:(tb__ "0|0|
S0S3S0S84R1A1S10R1S11Z2Z40A2A2A3Fz;").
Proof.
  intros z. unfold zmod64, M64.
  destruct (Z.leb_spec 0 z); [|reflexivity].
  destruct (Z.ltb_spec z (2 ^ 64)); [|reflexivity].
  symmetry. apply Z.mod_small. lia.
Qed.

Lemma snormc_eq : ltac2:(tb__ "0|0|
S0S3S0S83R1A1S66R1A1A3Fz;").
Proof. intros z. unfold snormc, snorm, M63, M64. rewrite zmod64_eq. reflexivity. Qed.

Lemma bv_add_Z : ltac2:(tb__ "0|2|
S8Q40M0A1M1S0S3G1SbG0R2SaG0R1A2A3SaG0S15S9G0R2A2R1A2A2A3Fk;Fa;").
Proof.
  intros a k. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma bv_add_ZZ : ltac2:(tb__ "0|1|
S0S0S3S8Q40M0A1SbG0SaG0R2A2SaG0R1A2A3SaG0S15R2R1A2A2A3Fk;Fx;").
Proof.
  intros x k. rewrite bv_add_Z. apply Z_to_bv64_eq_iff.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma bv_add_0_r : ltac2:(tb__ "0|2|
S8Q40M0A1M1S3G1SbG0R1SaG0Z0A2A3R1A3Fa;").
Proof.
  intros a. rewrite bv_add_Z, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma lit_of_sound : ltac2:(tb__ "0|1|
S21S8Q40A1M0S3G0S1fR2S76R1A1A2R1A3Fw;Frho;").
Proof. intros. unfold lit_of. cbn. apply Z_to_bv_bv_unsigned. Qed.

Lemma addk_base_sound : ltac2:(tb__ "0|1|
S21S20S0S3S8Q40M0A1S1fR3S67R2R1A2A2SbG0S1fR3R2A2SaG0R1A2A3A3Fs;Fb;Frho;").
Proof.
  intros rho b s. unfold addk_base. cbn.
  destruct (Z.eqb_spec (snorm s) 0) as [E|E]; cbn.
  - rewrite <- Z_to_bv64_snorm, E, bv_add_0_r. reflexivity.
  - rewrite Z_to_bv64_snorm. reflexivity.
Qed.

Lemma as_addlit_sound : ltac2:(tb__ "0|2|
S21S20S20S0S3S41S43S20S0A2M0A1S69R3A1S3fG0S46S20S0R2R1A4A2A3S3S8Q40M1A1S1fR5R4A2SbG1S1fR5R3A2SaG1R2A2A3A3F_;Fx;Fb;Fa;Frho;").
Proof.
  intros rho a b x H. destruct a; cbn in H; try discriminate.
  destruct op; try discriminate. destruct a2; try discriminate.
  inversion H; subst. reflexivity.
Qed.

Lemma addlit_case : ltac2:(tb__ "0|2|
S21S20S0S3S8Q40M0A1S1fR3S41S43S20S0A2M1A1S20Lx;S69R2A1G1G1S20Lp;R1S20S0S67R2S15R1R4A2A2Lx;Lb;X43x1Lp;S67R2R1A2X41x2A2SbG0S1fR3R2A2SaG0R1A2A3A3Fk;Fa;Frho;").
Proof.
  intros rho a k. destruct (as_addlit a) as [[b x]|] eqn:H.
  - rewrite (as_addlit_sound rho a b x H), addk_base_sound.
    rewrite !bv_add_Z. apply Z_to_bv64_eq_iff.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, Zplus_mod_idemp_l. f_equal. lia.
  - apply addk_base_sound.
Qed.

Lemma mk_addk_sound : ltac2:(tb__ "0|1|
S21S20S0S3S8Q40M0A1S1fR3S78R2R1A2A2SbG0S1fR3R2A2SaG0R1A2A3A3Fk;Fa;Frho;").
Proof.
  intros rho a k. unfold mk_addk.
  destruct a as [x| | | | | | | ]; try apply addlit_case.
  cbn. rewrite Z_to_bv64_mod, bv_add_ZZ. reflexivity.
Qed.

Lemma bv_add_comm64 : ltac2:(tb__ "0|2|
S8Q40M0A1M1G1S3G1SbG0R2R1A3SbG0R1R2A3A3Fb;Fa;").
Proof. intros. apply bv_eq. rewrite !bv_add_unsigned. f_equal. lia. Qed.

Lemma bv_sub_addneg : ltac2:(tb__ "0|2|
S8Q40M0A1M1S0S3G1SfG0R2SaG0R1A2A3SbG0R2SaG0S19R1A1A2A3A3Fy;Fa;").
Proof.
  intros. apply bv_eq. rewrite bv_sub_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64.
  rewrite Zminus_mod_idemp_r, Zplus_mod_idemp_r. f_equal; lia || idtac. all: try lia.
Qed.

Lemma addlit_view_sound : ltac2:(tb__ "0|1|
S21S20S20S0S3S43S20S0A2S6cR3A1S46S20S0R2R1A4A3S3S8Q40M0A1S1fR5R4A2SbG0S1fR5R3A2SaG0R2A2A3A3F_;Fk;Fb;Fe;Frho;").
Proof.
  intros rho e b k H. unfold addlit_view in H.
  destruct (as_addlit e) as [[b' k']|] eqn:E.
  - inversion H; subst. apply as_addlit_sound. exact E.
  - inversion H; subst. symmetry. apply bv_add_0_r.
Qed.

Lemma mk_sub_nn_sound : ltac2:(tb__ "0|0|
S21S20S20S3S8Q40A1S1fR3S82R2R1A2A2S48S30S1fR3R2A2S1fR3R1A2A3A3Fb;Fa;Frho;").
Proof.
  intros rho a b. unfold mk_sub_nn.
  destruct (addlit_view a) as [ba x] eqn:Ea. destruct (addlit_view b) as [bb y] eqn:Eb.
  destruct (sv_eqb ba bb) eqn:E; [|reflexivity].
  rewrite (addlit_view_sound rho a ba x Ea), (addlit_view_sound rho b bb y Eb).
  rewrite (sv_eqb_sound _ _ E). cbn [eval]. unfold alu64, alu.
  apply bv_eq. rewrite Z_to_bv_unsigned, bv_sub_unsigned, !bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64.
  rewrite <- (Zminus_mod (bv_unsigned (eval rho bb) + x mod 2 ^ 64) (bv_unsigned (eval rho bb) + y mod 2 ^ 64)).
  replace (bv_unsigned (eval rho bb) + x mod 2 ^ 64 - (bv_unsigned (eval rho bb) + y mod 2 ^ 64))
    with (x mod 2 ^ 64 - y mod 2 ^ 64) by lia.
  rewrite <- Zminus_mod. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma add_cancel_sound : ltac2:(tb__ "0|1|
S21S20S20S20S3S41S20A1S6bR3R2A2S3fS20R1A2A3S3S8Q40M0A1SbG0S1fR5R4A2S1fR5R3A2A3S1fR5R2A2A3F_;Fr;Fb;Fa;Frho;").
Proof.
  intros rho a b r H. unfold add_cancel in H.
  destruct b as [| |op b1 b2| | | | |]; try discriminate. destruct op; try discriminate.
  destruct (sv_eqb a b2) eqn:E; [|discriminate]. injection H as E'. subst r.
  rewrite (sv_eqb_sound _ _ E). cbn [eval]. unfold alu64, alu.
  apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap. rewrite two64.
  rewrite Zplus_mod_idemp_r.
  replace (bv_unsigned (eval rho b2) + (bv_unsigned (eval rho b1) - bv_unsigned (eval rho b2)))
    with (bv_unsigned (eval rho b1)) by lia.
  rewrite Z.mod_small; [reflexivity|]. apply urange.
Qed.

Lemma mk_add_nn_sound : ltac2:(tb__ "0|0|
S21S20S20S3S8Q40A1S1fR3S77R2R1A2A2S48S2fS1fR3R2A2S1fR3R1A2A3A3Fb;Fa;Frho;").
Proof.
  intros rho a b. unfold mk_add_nn, alu64, alu.
  destruct (add_cancel a b) as [r|] eqn:E1.
  - symmetry. apply add_cancel_sound. exact E1.
  - destruct (add_cancel b a) as [r|] eqn:E2; [|reflexivity].
    rewrite bv_add_comm64. symmetry. apply add_cancel_sound. exact E2.
Qed.

Lemma shamt_zero : ltac2:(tb__ "0|2|
S0S3S0S10R1Z40A2Z0M0A3S3S0S9Q40M1ScG1SaG1R2A2SaG1Z3fA2A3A2G0A3F_;Fy;").
Proof.
  intros y Hy. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  change (63 mod 2 ^ 64) with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64.
  rewrite <- Znumtheory.Zmod_div_mod; try lia. exists (2 ^ 58). reflexivity.
Qed.

Lemma mk_alu_nl_sound : ltac2:(tb__ "0|0|
S21S29S20S0S3S8Q40A1S1fR4S7cR3R2R1A3A2S48R3S1fR4R2A2S1fR4S24R1A1A2A3A3Fy;Fa;Fop;Frho;").
Proof.
  intros rho op a y. unfold mk_alu_nl. cbn [eval].
  destruct op; try reflexivity.
  - rewrite mk_addk_sound. reflexivity.
  - rewrite mk_addk_sound. unfold alu64, alu. symmetry. apply bv_sub_addneg.
  - destruct (Z.eqb_spec (y mod 64) 0) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_shiftl_unsigned, (shamt_zero y E).
    rewrite Z.shiftl_0_r. apply bv_wrap_small. rewrite two64. apply urange.
  - destruct (Z.eqb_spec (y mod 2 ^ 64) 0) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_xor_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. rewrite two64, E. apply Z.lxor_0_r.
  - destruct (Z.eqb_spec (y mod 64) 0) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_shiftr_unsigned, (shamt_zero y E).
    rewrite Z.shiftr_0_r. reflexivity.
  - destruct (Z.eqb_spec (y mod 64) 0) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq_signed. rewrite bv_ashiftr_signed, (shamt_zero y E).
    rewrite Z.shiftr_0_r. apply bv_swrap_bv_signed.
  - destruct (Z.eqb_spec (y mod 2 ^ 64) 0) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_or_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. rewrite two64, E. apply Z.lor_0_r.
  -   rewrite zmod64_eq. unfold MAXU.
    destruct (Z.eqb_spec (y mod 2 ^ 64) (2 ^ 64 - 1)) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_and_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. rewrite two64, E. change (2 ^ 64 - 1) with (Z.ones 64).
    rewrite Z.land_ones by lia. apply Z.mod_small. apply urange.
Qed.

Lemma mk_alu_ln_sound : ltac2:(tb__ "0|0|
S21S29S0S20S3S8Q40A1S1fR4S7bR3R2R1A3A2S48R3S1fR4S24R2A1A2S1fR4R1A2A3A3Fb;Fx;Fop;Frho;").
Proof.
  intros rho op x b. unfold mk_alu_ln. cbn [eval].
  destruct op; try reflexivity.
  - rewrite mk_addk_sound. unfold alu64, alu. apply bv_add_comm64.
  - destruct (Z.eqb_spec (x mod 2 ^ 64) 0) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_xor_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. rewrite two64, E. apply Z.lxor_0_l.
  - destruct (Z.eqb_spec (x mod 2 ^ 64) 0) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_or_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. rewrite two64, E. apply Z.lor_0_l.
  -   rewrite zmod64_eq. unfold MAXU.
    destruct (Z.eqb_spec (x mod 2 ^ 64) (2 ^ 64 - 1)) as [E|E]; [|reflexivity].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_and_unsigned, Z_to_bv_unsigned.
    unfold bv_wrap. rewrite two64, E. change (2 ^ 64 - 1) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. apply urange.
Qed.

Lemma mk_alu_nn_sound : ltac2:(tb__ "0|0|
S21S29S20S20S3S8Q40A1S1fR4S7dR3R2R1A3A2S48R3S1fR4R2A2S1fR4R1A2A3A3Fb;Fa;Fop;Frho;").
Proof.
  intros rho op a b. unfold mk_alu_nn.
  destruct op; try reflexivity.
  - apply mk_add_nn_sound.
  - apply mk_sub_nn_sound.
  - destruct (sv_eqb a b) eqn:E; [|reflexivity]. rewrite (sv_eqb_sound _ _ E). cbn [eval].
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_xor_unsigned, Z_to_bv_unsigned, Z.lxor_nilpotent. reflexivity.
  - destruct (sv_eqb a b) eqn:E; [|reflexivity]. rewrite (sv_eqb_sound _ _ E).
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_or_unsigned. apply Z.lor_diag.
  - destruct (sv_eqb a b) eqn:E; [|reflexivity]. rewrite (sv_eqb_sound _ _ E).
    unfold alu64, alu. symmetry. apply bv_eq. rewrite bv_and_unsigned. apply Z.land_diag.
Qed.

Lemma mk_alu_sound : ltac2:(tb__ "0|0|
S21S29S20S20S3S8Q40A1S1fR4S79R3R2R1A3A2S48R3S1fR4R2A2S1fR4R1A2A3A3Fb;Fa;Fop;Frho;").
Proof.
  intros rho op a b. unfold mk_alu.
  destruct a as [x| | | | | | | ] eqn:Ea; destruct b as [y| | | | | | | ] eqn:Eb;
    rewrite <- ?Ea, <- ?Eb;
    first [ rewrite lit_of_sound, Ea, Eb; reflexivity
          | rewrite Eb; apply mk_alu_nl_sound
          | rewrite Ea; apply mk_alu_ln_sound
          | apply mk_alu_nn_sound ].
Qed.

Lemma mk_aluw_sound : ltac2:(tb__ "0|1|
S21S29S20S20S3S8Q40M0A1S1fR4S7eR3R2R1A3A2S64Q20G0S4aR3S49S1fR4R2A2A1S49S1fR4R1A2A1A3A3A3Fb;Fa;Fop;Frho;").
Proof.
  intros rho op a b. unfold mk_aluw.
  destruct a as [x| | | | | | | ] eqn:Ea, b as [y| | | | | | | ] eqn:Eb;
    rewrite <- ?Ea, <- ?Eb; try reflexivity.
  rewrite lit_of_sound, Ea, Eb. reflexivity.
Qed.

Lemma mk_md_sound : ltac2:(tb__ "0|1|
S21S2eS20S20S3S8Q40M0A1S1fR4S80R3R2R1A3A2S4bG0R3S1fR4R2A2S1fR4R1A2A4A3Fb;Fa;Fop;Frho;").
Proof.
  intros rho op a b. unfold mk_md.
  destruct a as [x| | | | | | | ] eqn:Ea, b as [y| | | | | | | ] eqn:Eb;
    rewrite <- ?Ea, <- ?Eb; try reflexivity.
  rewrite lit_of_sound, Ea, Eb. reflexivity.
Qed.

Lemma mk_mdw_sound : ltac2:(tb__ "0|2|
S21S2eS20S20S3S8Q40M0A1S1fR4S81R3R2R1A3A2S64Q20M1G0S4bG1R3S49S1fR4R2A2A1S49S1fR4R1A2A1A4A3A3Fb;Fa;Fop;Frho;").
Proof.
  intros rho op a b. unfold mk_mdw.
  destruct a as [x| | | | | | | ] eqn:Ea, b as [y| | | | | | | ] eqn:Eb;
    rewrite <- ?Ea, <- ?Eb; try reflexivity.
  rewrite lit_of_sound, Ea, Eb. reflexivity.
Qed.

Lemma extract_0_64 : ltac2:(tb__ "0|2|
S8Q40M0A1M1S3G1SdG0Q0G0R1A4R1A3Fv;").
Proof.
  intros v. apply bv_eq. rewrite bv_extract_unsigned. cbn. rewrite Z.shiftr_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma sext_64_64 : ltac2:(tb__ "0|2|
S8Q40M0A1M1S3G1S64G0G0R1A3R1A3Fv;").
Proof.
  intros v. unfold sext. apply bv_eq. rewrite bv_sign_extend_unsigned.
  unfold bv_signed, bv_swrap, bv_wrap.
  pose proof (bv_unsigned_in_range 64 v) as H. rewrite two64 in *.
  change (bv_half_modulus 64) with (2 ^ 63).
  destruct (Z_lt_le_dec (bv_unsigned v) (2 ^ 63)).
  - rewrite (Z.mod_small (bv_unsigned v + 2 ^ 63)) by lia.
    replace (bv_unsigned v + 2 ^ 63 - 2 ^ 63) with (bv_unsigned v) by lia.
    apply Z.mod_small. lia.
  - replace (bv_unsigned v + 2 ^ 63) with ((bv_unsigned v - 2 ^ 63) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (bv_unsigned v - 2 ^ 63)) by lia.
    replace (bv_unsigned v - 2 ^ 63 - 2 ^ 63) with (bv_unsigned v + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma zext_64_64 : ltac2:(tb__ "0|2|
S8Q40M0A1M1S3G1S65G0G0R1A3R1A3Fv;").
Proof.
  intros v. unfold zext. apply bv_eq. rewrite bv_zero_extend_unsigned'.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma ext_low_64 : ltac2:(tb__ "0|2|
S40S8Q40M0A1M1S3G1S25R2G0R1A3R1A3Fv;Fsgn;").
Proof.
  intros sgn v. unfold ext_low. rewrite extract_0_64.
  destruct sgn; [apply sext_64_64 | apply zext_64_64].
Qed.

Lemma mk_ext_sound : ltac2:(tb__ "0|0|
S21S40S2S20S3S8Q40A1S1fR4S7fR3R2R1A3A2S25R3R2S1fR4R1A2A3A3Fa;Fw;Fsgn;Frho;").
Proof.
  intros rho sgn w a. unfold mk_ext.
  destruct a as [x| | | | | | | ] eqn:Ea; rewrite <- ?Ea;
    [rewrite lit_of_sound, Ea; reflexivity | ..];
    (destruct ((negb sgn || sgn) && (w =? 64)%N) eqn:E; [|reflexivity]);
    apply andb_prop in E as [_ E]; apply N.eqb_eq in E; subst w;
    symmetry; apply ext_low_64.
Qed.

Lemma align_of_sound : ltac2:(tb__ "0|2|
S21S42S22A1S1S54S22S23R3A1R2A3S4S12Z0M0S6eR3R2A2M1A2S3S0S10S9Q40S26R4R2A2A2S11Z2G1A2A2G0A3A2F_;Fi;Ffacts;Frho;").
Proof.
  intros rho facts i Hall. induction facts as [|f rest IH]; cbn.
  - split; [lia|]. rewrite Z.pow_0_r. apply Z.mod_1_r.
  - inversion Hall as [|f' rest' Hf Hrest]; subst. destruct (IH Hrest) as [IH1 IH2].
    destruct f; try (split; assumption).
    destruct (Pos.eqb_spec i i0) as [<-|Hne]; [|split; assumption].
    cbn in Hf. destruct Hf as [Ha Hmod].
    destruct (Z.le_ge_cases a (align_of rest i)).
    + rewrite Z.max_r by lia. split; assumption.
    + rewrite Z.max_l by lia. split; assumption.
Qed.

Lemma testbit_high_small : ltac2:(tb__ "0|1|
S0S0S0S12Z0M0R2A2S4S12G0R4A2S13R4S11Z2R3A2A2A2S12R4R3A2S3S40S18R6R4A2S44A3F_;F_;F_;Fn;FA;Fk;").
Proof.
  intros k A n HA Hk Hn.
  rewrite <- (Z.mod_small k (2 ^ A)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma testbit_congr : ltac2:(tb__ "0|2|
S0S0S0S0S12Z0M0R2A2S3S0S10R5S11Z2R3A2M1A2S10R4G1A2A3S4S12G0R3A2S13R3R4A2A2S3S40S18R7R4A2S18R6R4A2A3F_;F_;F_;Fn;FA;Fy;Fx;").
Proof.
  intros x y A n HA Hxy Hn.
  rewrite <- (Z.mod_pow2_bits_low x A n) by lia. rewrite <- (Z.mod_pow2_bits_low y A n) by lia.
  rewrite Hxy. reflexivity.
Qed.

Lemma land_low_congr : ltac2:(tb__ "0|3|
S0S0S0S0S12Z0M0R1A2S4S12G0R3A2S13R3S11Z2M1R2A2A2A2S3S0S10R6S11G1R3A2M2A2S10R5G2A2A3S3S0S17R7R5A2S17R6R5A2A3F_;F_;F_;FA;Fk;Fy;Fx;").
Proof.
  intros x y k A HA Hk Hxy. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases n A).
  - rewrite (testbit_congr x y A n) by lia. reflexivity.
  - rewrite (testbit_high_small k A n) by lia. rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma land_bound : ltac2:(tb__ "0|3|
S0S0S0S12Z0M0R1A2S4S12G0R3A2S13R3S11Z2M1R2A2A2A2S4S12G0S17R5R4A2M2A2S13G2S11G1R3A2A2A2F_;F_;FA;Fk;Fx;").
Proof.
  intros x k A HA Hk.
  assert (H0 : 0 <= Z.land x k) by (apply Z.land_nonneg; right; lia).
  split; [exact H0|].
  apply (proj2 (Z.bounded_iff_bits_nonneg A (Z.land x k) HA H0)).
  intros n Hn. rewrite Z.land_spec, (testbit_high_small k A n) by lia. apply Bool.andb_false_r.
Qed.

Lemma mod_pow2_of_mod_2_64 : ltac2:(tb__ "0|3|
S0S0S4S12Z0R1A2S12R1Z40M0A2A2S3S0S10S10R3S11Z2M1G0A2A2S11G1R2A2M2A2S10R3G2A2A3F_;FA;Fz;").
Proof.
  intros z A HA. rewrite <- Znumtheory.Zmod_div_mod; try lia.
  exists (2 ^ (64 - A)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma and_lit_eq : ltac2:(tb__ "0|6|
S8Q40M0A1M1S0S0S0S4S12Z0M2R1A2S12R1Z40M3A2A2S4S12G2R3A2S13R3S11Z2M4R2A2A2A2S3S0S10S9G0R6A2S11G4R3A2M5A2S10R5G5A2A3S3G1ScG0R7SaG0R5A2A3SaG0S17S10R6S11G4G3A2A2R5A2A2A3F_;F_;F_;FA;Fk;Fc;Fw;").
Proof.
  intros w c k A HA Hk Hc. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64.
  assert (2 ^ A <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small k) by lia.
  pose proof (land_bound (c mod 2 ^ 64) k A ltac:(lia) Hk).
  rewrite (Z.mod_small (Z.land (c mod 2 ^ 64) k)) by lia.
  apply (land_low_congr _ _ k A); try lia. rewrite mod_pow2_of_mod_2_64 by lia. exact Hc.
Qed.

Lemma congr_add : ltac2:(tb__ "0|5|
S0S0S0S4S12Z0M0R1A2S12R1Z40M1A2A2S3S0S10R4S11Z2M2R2A2A2G0A3S3S0S10S10S15R5S10R4S11G2G1A2M3A2A2G3A2S11G2R3A2M4A2S10R4G4A2A3F_;F_;FA;Fc;Fx;").
Proof.
  intros x c A HA Hx.
  rewrite mod_pow2_of_mod_2_64 by lia.
  rewrite <- Zplus_mod_idemp_r, mod_pow2_of_mod_2_64 by lia.
  rewrite <- Zplus_mod_idemp_l, Hx, Z.add_0_l. apply Z.mod_mod. lia.
Qed.

Lemma congr_sub : ltac2:(tb__ "0|5|
S0S0S0S4S12Z0M0R1A2S12R1Z40M1A2A2S3S0S10R4S11Z2M2R2A2A2G0A3S3S0S10S10S14S10R4S11G2G1A2M3A2R5A2G3A2S11G2R3A2M4A2S10R4G4A2A3F_;F_;FA;Fc0;Fx;").
Proof.
  intros x c0 A HA Hx.
  rewrite mod_pow2_of_mod_2_64 by lia.
  rewrite <- Zminus_mod_idemp_l, mod_pow2_of_mod_2_64 by lia.
  rewrite <- Zminus_mod_idemp_r, Hx, Z.sub_0_r. apply Z.mod_mod. lia.
Qed.

Lemma congr_sub_add : ltac2:(tb__ "0|5|
S0S0S0S0S4S12Z0M0R1A2S12R1Z40M1A2A2S3S0S10R5S11Z2M2R2A2A2G0A3S3S0S10S10S14S10R5S11G2G1A2M3A2S10S15R6S10R4G3A2A2G3A2A2G3A2S11G2R3A2M4A2S10S14R5R4A2G4A2A3F_;F_;FA;Fc;Fc0;Fx;").
Proof.
  intros x c0 c A HA Hx.
  rewrite mod_pow2_of_mod_2_64 by lia.
  rewrite <- Zminus_mod_idemp_r. rewrite mod_pow2_of_mod_2_64 by lia.
  rewrite <- Zminus_mod_idemp_l. rewrite mod_pow2_of_mod_2_64 by lia.
  rewrite Zminus_mod_idemp_l.
  rewrite <- (Zplus_mod_idemp_l x). rewrite Hx. rewrite Z.add_0_l.
  rewrite mod_pow2_of_mod_2_64 by lia. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma land_mod_2_64 : ltac2:(tb__ "0|1|
S0S0S4S12Z0R2A2S13R2S11Z2Z40A2M0A2A2S3S0S17R3S10R2G0A2A2S17R3R2A2A3F_;Fm;Fs;").
Proof.
  intros s m Hs. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases n 64).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit s n) with false; [reflexivity|].
    symmetry. rewrite <- (Z.mod_small s (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma land_high_mask : ltac2:(tb__ "0|5|
S0S0S4S12Z0M0R1A2S12R1Z40M1A2A2S4S12G0R3A2S13R3S11Z2M2G1A2M3A2A2S3S0S17R4S14G3S11G2R3A2M4A2A2S14R4S10R4G4A2A2A3F_;F_;Fj;Fs;").
Proof.
  intros s j Hj Hs.
  assert (E : 2 ^ 64 - 2 ^ j = (- 2 ^ j) mod 2 ^ 64).
  { destruct (Z.eq_dec j 64) as [->|Hne].
    - rewrite Z.sub_diag. rewrite Z_mod_zero_opp_full; [reflexivity|]. apply Z.mod_same. lia.
    - rewrite Z_mod_nz_opp_full.
      + rewrite Z.mod_small; [lia|]. split; [lia|]. apply Z.pow_lt_mono_r; lia.
      + rewrite Z.mod_small. 2: { split; [lia|]. apply Z.pow_lt_mono_r; lia. } pose proof (Z.pow_pos_nonneg 2 j). lia. }
  rewrite E, land_mod_2_64 by lia.
  replace (- 2 ^ j) with (Z.lnot (Z.ones j)).
  2:{ unfold Z.ones. rewrite Z.shiftl_1_l. unfold Z.lnot. lia. }
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  rewrite (Z.div_mod s (2 ^ j)) at 2 by lia. lia.
Qed.

Lemma high_mask_sub_eq : ltac2:(tb__ "0|6|
S0S0S0S4S12Z0M0R1A2S12R1Z40M1A2A2S3S0S10R4S11Z2M2R2A2A2G0A3S3S0S14S10S15R5R4A2S11G2G1A2M3A2M4S10G4S11G2R3A2M5A2A2S10S15R5S14R4S10R4G5A2A2A2G3A2A3F_;F_;Fj;Fcm;Fx;").
Proof.
  intros x cm j Hj Hx.
  rewrite mod_pow2_of_mod_2_64 by lia.
  assert (M1 : (x + cm) mod 2 ^ j = cm mod 2 ^ j).
  { rewrite <- Zplus_mod_idemp_l, Hx, Z.add_0_l. reflexivity. }
  rewrite M1.
  replace (x + (cm - cm mod 2 ^ j)) with ((x + cm) - cm mod 2 ^ j) by lia.
  rewrite <- (Zminus_mod_idemp_l (x + cm)).
  symmetry. apply Z.mod_small.
  pose proof (Z.mod_pos_bound (x + cm) (2 ^ 64) ltac:(lia)) as B.
  pose proof (Z.mod_pos_bound cm (2 ^ j) ltac:(lia)) as B2.
  assert (cm mod 2 ^ j <= (x + cm) mod 2 ^ 64).
  { rewrite <- M1, <- (mod_pow2_of_mod_2_64 (x + cm) j) by lia. apply Z.mod_le; lia. }
  lia.
Qed.

Lemma high_mask_j_sound : ltac2:(tb__ "0|2|
S0S0S3S41S0A1S73R2A1S3fS0R1A2A3S4S12Z0R2A2S3S0S10R3S11Z2M0Z40A2M1A2S14G1S11G0R2A2A2A3A2F_;Fj;Fk;").
Proof.
  intros k j H. unfold high_mask_j in H. rewrite zmod64_eq in H. unfold M64 in H.
  destruct (0 <? 2 ^ 64 - k mod 2 ^ 64) eqn:E1; [|discriminate].
  destruct (2 ^ 64 - k mod 2 ^ 64 =? 2 ^ Z.log2 (2 ^ 64 - k mod 2 ^ 64)) eqn:E2; [|discriminate].
  inversion H; subst j. apply Z.ltb_lt in E1. apply Z.eqb_eq in E2.
  split; [apply Z.log2_nonneg|]. lia.
Qed.

Lemma and_high_eq : ltac2:(tb__ "0|7|
S8Q40M0A1M1S0S0S0S4S12Z0M2R1A2S12R1Z40M3A2A2S3S0S10R3S11Z2M4G3A2M5A2S14G5S11G4R2A2A2A3S3S0S10S9G0R6A2S11G4R3A2A2G2A3S3G1ScG0SbG0R7SaG0R6A2A3SaG0R5A2A3SbG0R7SaG0S14S10R6G5A2M6S10G6S11G4R4A2A2A2A2A3A3F_;F_;F_;Fj;Fk;Fc;Fx;").
Proof.
  intros x c k j Hj Hk Hx. apply bv_eq.
  rewrite bv_and_unsigned, !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite Hk. pose proof (urange x) as Hxr.
  rewrite land_high_mask by (try lia; apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small (c mod 2 ^ 64 - (c mod 2 ^ 64) mod 2 ^ j)).
  2:{ pose proof (Z.mod_pos_bound c (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (c mod 2 ^ 64) (2 ^ j) ltac:(lia)).
      pose proof (Z.mod_le (c mod 2 ^ 64) (2 ^ j) ltac:(lia) ltac:(lia)). lia. }
  apply high_mask_sub_eq; assumption.
Qed.

Lemma sext64_32_mod : ltac2:(tb__ "0|3|
S8Q20M0A1S0S4S12Z0R1A2S12R1Z20A2A2S3S0S10S9Q40M1S64G0G1R3A3A2S11Z2R2A2M2A2S10S9G0R3A2G2A2A3F_;FA;Fv;").
Proof.
  intros v A HA. unfold sext. rewrite bv_sign_extend_unsigned.
  unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
  assert (D64 : (2 ^ A | 2 ^ 64)). { exists (2 ^ (64 - A)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (D32 : (2 ^ A | 2 ^ 32)). { exists (2 ^ (32 - A)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ A)) by (try lia; exact D64).
  rewrite Zminus_mod. rewrite (Z.mod_mod_divide _ (2 ^ 32) (2 ^ A)) by (try lia; exact D32).
  rewrite <- Zminus_mod. f_equal. lia.
Qed.

Lemma low32_mod : ltac2:(tb__ "0|2|
S8Q40M0A1S0S4S12Z0R1A2S12R1Z20A2A2S3S0S10S9Q20S49R3A1A2S11Z2R2A2M1A2S10S9G0R3A2G1A2A3F_;FA;Fw;").
Proof.
  intros w A HA. unfold low32. rewrite bv_extract_unsigned.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  apply Z.mod_mod_divide. exists (2 ^ (32 - A)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma aluw_sub_low : ltac2:(tb__ "0|3|
S8Q40M0A1M1G1S0S4S12Z0R1A2S12R1Z20A2A2S3S0S10S9G0S64Q20G0S4aS30S49R4A1S49R3A1A3A3A2S11Z2R2A2M2A2S10S14S9G0R4A2S9G0R3A2A2G2A2A3F_;FA;Fb;Fa;").
Proof.
  intros a b A HA. rewrite sext64_32_mod by lia. unfold alu32, alu. rewrite bv_sub_unsigned.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_mod_divide _ (2 ^ 32) (2 ^ A)).
  2:{ exists (2 ^ (32 - A)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite Zminus_mod, !low32_mod by lia. rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma aluw_add_low : ltac2:(tb__ "0|3|
S8Q40M0A1M1G1S0S4S12Z0R1A2S12R1Z20A2A2S3S0S10S9G0S64Q20G0S4aS2fS49R4A1S49R3A1A3A3A2S11Z2R2A2M2A2S10S15S9G0R4A2S9G0R3A2A2G2A2A3F_;FA;Fb;Fa;").
Proof.
  intros a b A HA. rewrite sext64_32_mod by lia. unfold alu32, alu. rewrite bv_add_unsigned.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_mod_divide _ (2 ^ 32) (2 ^ A)).
  2:{ exists (2 ^ (32 - A)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite Zplus_mod, !low32_mod by lia. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma and_mask_fold_sound : ltac2:(tb__ "0|1|
S21S42S22A1S20S0S20S54S22S23R5A1R4A3S3S41S20A1S70R5R4R3A3S3fS20R2A2A3S3S8Q40M0A1ScG0S1fR7R5A2SaG0R4A2A3S1fR7R3A2A3F_;F_;Fr;Fk;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e k r Hall H.
  assert (AL : forall i, 0 <= align_of facts i /\ bv_unsigned (rw rho i) mod 2 ^ (align_of facts i) = 0)
    by (intros; apply align_of_sound; exact Hall).
  assert (OKlow : forall i, ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64))%bool = true ->
            0 <= k < 2 ^ align_of facts i /\ align_of facts i <= 64).
  { intros i E. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3. auto. }
  assert (OKhigh : forall i j,
            match high_mask_j k with
            | Some j0 => if ((0 <=? j0) && (j0 <=? align_of facts i) && (align_of facts i <=? 64))%bool then Some j0 else None
            | None => None end = Some j ->
            0 <= j <= 64 /\ k mod 2 ^ 64 = 2 ^ 64 - 2 ^ j /\ bv_unsigned (rw rho i) mod 2 ^ j = 0).
  { intros i j E. destruct (high_mask_j k) as [j0|] eqn:Hj; [|discriminate].
    destruct ((0 <=? j0) && (j0 <=? align_of facts i) && (align_of facts i <=? 64))%bool eqn:E2; [|discriminate].
    inversion E; subst j. apply andb_prop in E2 as [E2 E4]. apply andb_prop in E2 as [E2 E3].
    apply Z.leb_le in E2. apply Z.leb_le in E3. apply Z.leb_le in E4.
    destruct (high_mask_j_sound k j0 Hj) as [_ Hk]. destruct (AL i) as [HA0 Hx].
    split; [lia|]. split; [exact Hk|].

    rewrite (Znumtheory.Zmod_div_mod (2 ^ j0) (2 ^ align_of facts i)); try lia.
    + rewrite Hx. apply Z.mod_0_l. lia.
    + exists (2 ^ (align_of facts i - j0)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  unfold and_mask_fold in H.
  destruct e as [| i | op a b | op a b | | | |]; try discriminate.
  -
    destruct ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64))%bool eqn:E.
    + inversion H; subst r. destruct (OKlow i E) as [Hk HA]. destruct (AL i) as [HA0 Hx].
      cbn [eval]. rewrite (and_lit_eq (rw rho i) 0 k (align_of facts i)); try lia.
      * rewrite Z.mod_0_l by lia. rewrite Z.land_0_l. reflexivity.
      * rewrite Hx, Z.mod_0_l by lia. reflexivity.
    + destruct (match high_mask_j k with Some j0 => _ | None => None end) as [j|] eqn:Eh; [|discriminate].
      inversion H; subst r. destruct (OKhigh i j Eh) as (Hj & Hk & Hx).
      cbn [eval]. rewrite <- (bv_add_0_r (rw rho i)) at 1.
      rewrite (and_high_eq (rw rho i) 0 k j Hj Hk Hx).
      rewrite Z.mod_0_l, Z.mod_0_l, Z.sub_0_r by lia. apply bv_add_0_r.
  - destruct op; try discriminate.
    +
      destruct a as [|i| | | | | |]; try discriminate. destruct b as [c| | | | | | |]; try discriminate.
      destruct ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64))%bool eqn:E.
      * inversion H; subst r. destruct (OKlow i E) as [Hk HA]. destruct (AL i) as [HA0 Hx].
        cbn [eval]. apply (and_lit_eq _ c k (align_of facts i)); try lia.
        unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        apply congr_add; [lia | exact Hx].
      * destruct (match high_mask_j k with Some j0 => _ | None => None end) as [j|] eqn:Eh; [|discriminate].
        inversion H; subst r. destruct (OKhigh i j Eh) as (Hj & Hk & Hx).
        rewrite addk_base_sound. cbn [eval]. unfold alu64, alu.
        apply (and_high_eq (rw rho i) c k j Hj Hk Hx).
    + destruct a as [c0| | | | | | |]; try discriminate.
      destruct b as [|i|op2 a2 b2| | | | |]; try discriminate.
      * destruct ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64))%bool eqn:E; [|discriminate].
        inversion H; subst r. destruct (OKlow i E) as [Hk HA]. destruct (AL i) as [HA0 Hx].
        cbn [eval]. apply (and_lit_eq _ c0 k (align_of facts i)); try lia.
        unfold alu64, alu. rewrite bv_sub_unsigned, Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        apply congr_sub; [lia | exact Hx].
      * destruct op2; try discriminate.
        destruct a2 as [|i| | | | | |]; try discriminate. destruct b2 as [c| | | | | | |]; try discriminate.
        destruct ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64))%bool eqn:E; [|discriminate].
        inversion H; subst r. destruct (OKlow i E) as [Hk HA]. destruct (AL i) as [HA0 Hx].
        cbn [eval]. apply (and_lit_eq _ (c0 - c) k (align_of facts i)); try lia.
        unfold alu64, alu. rewrite bv_sub_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        apply congr_sub_add; [lia | exact Hx].
  -
    assert (OK32 : forall i, ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64) && (align_of facts i <=? 32))%bool = true ->
              0 <= k < 2 ^ align_of facts i /\ align_of facts i <= 32).
    { intros i E. apply andb_prop in E as [E E4]. destruct (OKlow i E) as [Hk _]. apply Z.leb_le in E4. auto. }
    destruct op; try discriminate.
    +
      destruct a as [|i| | | | | |]; try discriminate. destruct b as [c| | | | | | |]; try discriminate.
      destruct ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64) && (align_of facts i <=? 32))%bool eqn:E; [|discriminate].
      inversion H; subst r. destruct (OK32 i E) as [Hk HA]. destruct (AL i) as [HA0 Hx].
      cbn [eval]. apply (and_lit_eq _ c k (align_of facts i)); try lia.
      rewrite aluw_add_low by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      rewrite Zplus_mod, Hx, Z.add_0_l, mod_pow2_of_mod_2_64 by lia. apply Z.mod_mod. lia.
    +
      destruct a as [c0| | | | | | |]; try discriminate.
      destruct b as [|i|op2 a2 b2| | | | |]; try discriminate.
      * destruct ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64) && (align_of facts i <=? 32))%bool eqn:E; [|discriminate].
        inversion H; subst r. destruct (OK32 i E) as [Hk HA]. destruct (AL i) as [HA0 Hx].
        cbn [eval]. apply (and_lit_eq _ c0 k (align_of facts i)); try lia.
        rewrite aluw_sub_low by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        rewrite Zminus_mod, Hx, Z.sub_0_r, mod_pow2_of_mod_2_64 by lia. apply Z.mod_mod. lia.
      * destruct op2; try discriminate.
        destruct a2 as [|i| | | | | |]; try discriminate. destruct b2 as [c| | | | | | |]; try discriminate.
        destruct ((0 <=? k) && (k <? 2 ^ align_of facts i) && (align_of facts i <=? 64) && (align_of facts i <=? 32))%bool eqn:E; [|discriminate].
        inversion H; subst r. destruct (OK32 i E) as [Hk HA]. destruct (AL i) as [HA0 Hx].
        cbn [eval]. apply (and_lit_eq _ (c0 - c) k (align_of facts i)); try lia.
        rewrite aluw_sub_low by lia. unfold alu64, alu. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        rewrite <- (mod_pow2_of_mod_2_64 (c0 mod 2 ^ 64 - _) (align_of facts i)) by lia.
        apply congr_sub_add; [lia | exact Hx].
Qed.

Lemma bv_and_comm64 : ltac2:(tb__ "0|2|
S8Q40M0A1M1G1S3G1ScG0R2R1A3ScG0R1R2A3A3Fb;Fa;").
Proof. intros. apply bv_eq. rewrite !bv_and_unsigned. apply Z.land_comm. Qed.

Lemma shamt_val : ltac2:(tb__ "0|1|
S0S3S0S9Q40M0ScG0SaG0R1A2SaG0Z3fA2A3A2S10R1Z40A2A3Fk;").
Proof.
  intros k. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  change (63 mod 2 ^ 64) with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6) with 64.
  apply Z.mod_mod_divide. exists (2 ^ 58). reflexivity.
Qed.

Lemma snorm_range : ltac2:(tb__ "0|2|
S0S4S12S19S11Z2Z3fA2M0A1S66R1A1M1A2S13G1G0A2A2Fc;").
Proof.
  intros c. unfold snorm. pose proof (Z.mod_pos_bound c (2^64) ltac:(lia)).
  destruct (Z.ltb_spec (c mod 2^64) (2^63)); lia.
Qed.

Lemma add_val : ltac2:(tb__ "0|2|
S8Q40M0A1M1G1S3S0S9G0S48S2fR2R1A3A2S10S15S9G0R2A2S9G0R1A2A2S11Z2Z40A2A2A3Fy;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. rewrite two64. reflexivity. Qed.
Lemma sub_val : ltac2:(tb__ "0|2|
S8Q40M0A1M1G1S3S0S9G0S48S30R2R1A3A2S10S14S9G0R2A2S9G0R1A2A2S11Z2Z40A2A2A3Fy;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite two64. reflexivity. Qed.
Lemma and_val : ltac2:(tb__ "0|2|
S8Q40M0A1M1G1S3S0S9G0S48S3aR2R1A3A2S17S9G0R2A2S9G0R1A2A2A3Fy;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_and_unsigned. reflexivity. Qed.
Lemma or_val_A : ltac2:(tb__ "0|2|
S8Q40M0A1M1G1S3S0S9G0S48S3bR2R1A3A2S1aS9G0R2A2S9G0R1A2A2A3Fy;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_or_unsigned. reflexivity. Qed.
Lemma sll_val : ltac2:(tb__ "0|2|
S8Q40M0A1S0S3S0S9G0S48S3cR2SaG0R1A2A3A2S10S1dS9G0R2A2S10R1Z40M1A2A2S11Z2G1A2A2A3Fk;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_shiftl_unsigned, shamt_val. unfold bv_wrap. rewrite two64. reflexivity. Qed.
Lemma srl_val : ltac2:(tb__ "0|1|
S8Q40M0A1S0S3S0S9G0S48S3dR2SaG0R1A2A3A2S1eS9G0R2A2S10R1Z40A2A2A3Fk;Fx;").
Proof. intros. unfold alu64, alu. rewrite bv_shiftr_unsigned, shamt_val. reflexivity. Qed.
Lemma mul_val : ltac2:(tb__ "0|2|
S8Q40M0A1M1G1S3S0S9G0S4bG0S3eR2R1A4A2S10S1bS9G0R2A2S9G0R1A2A2S11Z2Z40A2A2A3Fy;Fx;").
Proof. intros. unfold mul_div. rewrite bv_mul_unsigned. unfold bv_wrap. rewrite two64. reflexivity. Qed.

Lemma divide_pow2_le : ltac2:(tb__ "0|1|
S0S0S0S4S12Z0R2A2S12R2R1A2A2S16S11Z2M0R2A2R4A2S16S11G0R4A2R5A2F_;F_;Fn;Fm;Fa;").
Proof.
  intros a m n Hmn [q ->]. exists (q * 2 ^ (n - m)).
  rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia.
Qed.

Lemma divide_mod64 : ltac2:(tb__ "0|2|
S0S0S4S12Z0R1A2S12R1Z40M0A2A2S16S11Z2M1R2A2R3A2S16S11G1R3A2S10R4S11G1G0A2A2A2F_;F_;Fn;Fa;").
Proof.
  intros a n Hn Hd. pose proof (Z_div_mod_eq_full a (2 ^ 64)) as E.
  replace (a mod 2 ^ 64) with (a - 2 ^ 64 * (a / 2 ^ 64)) by lia.
  apply Z.divide_sub_r; [exact Hd|]. apply Z.divide_mul_l. exists (2 ^ (64 - n)).
  rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma mod0_bits : ltac2:(tb__ "0|2|
S0S0S12Z0M0R1A2M1S3S0S10R3S11Z2R2A2A2G0A3S0S4G1S13R1R4A2A2S3S40S18R6R2A2S44A3F_;Fi;F_;F_;Fn;Fx;").
Proof.
  intros x n Hn H i Hi. rewrite <- (Z.mod_pow2_bits_low x n i) by lia. rewrite H. apply Z.bits_0.
Qed.

Lemma bits_mod0 : ltac2:(tb__ "0|2|
S0S0S12Z0M0R1A2M1S0S4G1S13R1R3A2A2S3S40S18R5R2A2S44A3F_;Fi;S3S0S10R4S11Z2R3A2A2G0A3F_;F_;Fn;Fx;").
Proof.
  intros x n Hn H. apply Z.bits_inj_0. intros i.
  destruct (Z.lt_ge_cases i 0); [apply Z.testbit_neg_r; lia|].
  destruct (Z.lt_ge_cases i n).
  - rewrite Z.mod_pow2_bits_low by lia. apply H. lia.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma tzb_sound : ltac2:(tb__ "0|2|
S47S0S0S12Z0M0R1A2S4S4S12G0S6aR4R3R2A3M1A2S12G1S1cR4A1A2A2S0S4S12R3R1A2S13R1S15R3S6aR5R4R3A3A2A2A2S3S40S18R5R2A2S44A3F_;Fj;A2F_;Fi;Fm;Ffuel;").
Proof.
  induction fuel as [|f IH]; intros m i Hi; cbn [tzb].
  - split; [lia|]. intros j Hj. lia.
  - destruct (Z.testbit m i) eqn:T.
    + split; [lia|]. intros j Hj. lia.
    + destruct (IH m (i + 1) ltac:(lia)) as [R B]. split; [lia|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|]; [exact T|]. apply B. lia.
Qed.

Lemma lit_align_sound : ltac2:(tb__ "0|3|
S0S4S4S12Z0S75R1A1M0A2S12G0Z40M1A2A2S16S11Z2M2G0A2S10R1S11G2G1A2A2A2A2Fz;").
Proof.
  intros z. unfold lit_align. rewrite zmod64_eq. set (m := z mod 2 ^ 64).
  destruct (Z.eqb_spec m 0) as [E|E].
  - split; [lia|]. rewrite E. apply Z.divide_0_r.
  - destruct (tzb_sound 64 m 0 ltac:(lia)) as [R B]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in R. split; [lia|].
    apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. apply bits_mod0; [lia|]. intros i Hi. apply B. lia.
Qed.

Lemma divide_pow2_0 : ltac2:(tb__ "0|0|
S0S16S11Z2Z0A2R1A2Fa;").
Proof. intros a. rewrite Z.pow_0_r. apply Z.divide_1_l. Qed.

Lemma align_sv_sound : ltac2:(tb__ "0|1|
S21S42S22A1S20S54S22S23R3A1R2A3S4S4S12Z0S6fR3R2A2M0A2S12G0Z40A2A2S16S11Z2G0A2S9Q40S1fR4R2A2A2A2A2F_;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e Hf. induction e; cbn [align_sv]; try (split; [lia | apply divide_pow2_0]).
  - pose proof (lit_align_sound z) as [A B]. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. auto.
  - destruct (align_of_sound rho facts i Hf) as [A B]. split; [lia|]. cbn [eval].
    apply (divide_pow2_le _ _ (align_of facts i)); [lia|]. apply Z.mod_divide; [apply Z.pow_nonzero; lia | exact B].
  - destruct IHe1 as [A1 B1]. destruct IHe2 as [A2 B2].
    pose proof (urange (eval rho e1)) as R1. pose proof (urange (eval rho e2)) as R2.
    destruct op; try (split; [lia | apply divide_pow2_0]); cbn [eval].
    +   split; [lia|]. rewrite add_val.
      apply divide_mod64; [lia|]. apply Z.divide_add_r; eapply divide_pow2_le; [|exact B1| |exact B2]; lia.
    +   split; [lia|]. rewrite sub_val.
      apply divide_mod64; [lia|]. apply Z.divide_sub_r; eapply divide_pow2_le; [|exact B1| |exact B2]; lia.
    +   destruct e2 as [k| | | | | | |]; try (split; [lia | apply divide_pow2_0]).
      cbn [align_sv eval]. pose proof (Z.mod_pos_bound k 64 ltac:(lia)) as K. split; [lia|]. rewrite sll_val.
      rewrite Z.shiftl_mul_pow2 by lia. apply divide_mod64; [lia|].
      apply (divide_pow2_le _ _ (align_sv facts e1 + k mod 64)); [lia|].
      rewrite Z.pow_add_r by lia. apply Z.mul_divide_mono_r. exact B1.
    +   destruct e2 as [k| | | | | | |]; try (split; [lia | apply divide_pow2_0]).
      cbn [align_sv eval]. pose proof (Z.mod_pos_bound k 64 ltac:(lia)) as K. split; [lia|]. rewrite srl_val.
      rewrite Z.shiftr_div_pow2 by lia.
      destruct (Z.le_gt_cases (k mod 64) (align_sv facts e1)).
      * rewrite Z.max_r by lia. destruct B1 as [q Hq]. rewrite Hq. exists q.
        replace (2 ^ align_sv facts e1) with (2 ^ (align_sv facts e1 - k mod 64) * 2 ^ (k mod 64))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        rewrite Z.mul_assoc. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
      * rewrite Z.max_l by lia. apply divide_pow2_0.
    +   split; [lia|]. rewrite or_val_A.
      apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. apply bits_mod0; [lia|]. intros i Hi.
      rewrite Z.lor_spec.
      rewrite (mod0_bits (bv_unsigned (eval rho e1)) (align_sv facts e1)); [ | lia | | lia].
      2:{ destruct B1 as [q ->]. apply Z_mod_mult. }
      rewrite (mod0_bits (bv_unsigned (eval rho e2)) (align_sv facts e2)); [reflexivity | lia | | lia].
      destruct B2 as [q ->]. apply Z_mod_mult.
    +   split; [lia|]. rewrite and_val.
      apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. apply bits_mod0; [lia|]. intros i Hi.
      rewrite Z.land_spec.
      destruct (Z.le_gt_cases (align_sv facts e2) (align_sv facts e1)).
      * rewrite Z.max_l in Hi by lia.
        rewrite (mod0_bits (bv_unsigned (eval rho e1)) (align_sv facts e1)); [reflexivity | lia | | lia].
        apply Z_mod_mult || (destruct B1 as [q ->]; apply Z_mod_mult).
      * rewrite Z.max_r in Hi by lia.
        rewrite (mod0_bits (bv_unsigned (eval rho e2)) (align_sv facts e2)); [apply Bool.andb_false_r | lia | | lia].
        destruct B2 as [q ->]. apply Z_mod_mult.
  -
    destruct IHe1 as [A1 B1]. destruct IHe2 as [A2 B2].
    set (j := Z.min 32 (Z.min (align_sv facts e1) (align_sv facts e2))).
    assert (J1 : (2 ^ j | bv_unsigned (eval rho e1))%Z) by (eapply divide_pow2_le; [|exact B1]; lia).
    assert (J2 : (2 ^ j | bv_unsigned (eval rho e2))%Z) by (eapply divide_pow2_le; [|exact B2]; lia).
    assert (NZ : 2 ^ j <> 0) by (apply Z.pow_nonzero; lia).
    destruct op; try (split; [lia | apply divide_pow2_0]); cbn [eval]; (split; [lia|]);
      apply (proj1 (Z.mod_divide _ _ NZ));
      [ rewrite aluw_add_low by lia; apply (proj2 (Z.mod_divide _ _ NZ)); apply Z.divide_add_r; assumption
      | rewrite aluw_sub_low by lia; apply (proj2 (Z.mod_divide _ _ NZ)); apply Z.divide_sub_r; assumption ].
  -   destruct IHe1 as [A1 B1]. destruct IHe2 as [A2 B2].
    destruct op; try (split; [lia | apply divide_pow2_0]). cbn [eval]. split; [lia|]. rewrite mul_val.
    apply divide_mod64; [lia|]. apply (divide_pow2_le _ _ (align_sv facts e1 + align_sv facts e2)); [lia|].
    rewrite Z.pow_add_r by lia.
    eapply Z.divide_trans; [apply Z.mul_divide_mono_r; exact B1 | apply Z.mul_divide_mono_l; exact B2].
Qed.

Lemma and_mask_gen_sound : ltac2:(tb__ "0|1|
S21S42S22A1S20S0S20S54S22S23R5A1R4A3S3S41S20A1S72R5R4R3A3S3fS20R2A2A3S3S8Q40M0A1ScG0S1fR7R5A2SaG0R4A2A3S1fR7R3A2A3F_;F_;Fr;Fk;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e k r Hf H. unfold and_mask_gen in H.
  destruct (Z.leb_spec 0 k); [|discriminate]. destruct (Z.ltb_spec k (2 ^ align_sv facts e)); [|discriminate].
  injection H as <-. destruct (align_sv_sound rho facts e Hf) as [A B].
  cbn [eval]. rewrite (and_lit_eq (eval rho e) 0 k (align_sv facts e)); try lia.
  - rewrite Z.mod_0_l by lia. rewrite Z.land_0_l. reflexivity.
  - rewrite Z.mod_0_l by lia. destruct B as [q Hq]. rewrite Hq. apply Z_mod_mult.
Qed.

Lemma align_lin_sound : ltac2:(tb__ "0|2|
S21S42S22A1S20S0S0S54S22S23R5A1R4A3S3S43S0S0A2S6dR5R4A2S46S0S0R3R2A4A3S4S4S12Z0R4A2S12R4Z40M0A2A2S6S0S0S4S16S11Z2M1R5A2R1A2S3S0S9Q40S1fR8R6A2A2S10S15R1R4A2S11G1G0A2A2A3A2LN;A2A2F_;F_;Fc;Fj;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e. induction e; intros j c Hf H;
    try (cbn [align_lin] in H; injection H as <- <-;
         match goal with |- context [eval rho ?ee] => pose proof (align_sv_sound rho facts ee Hf) as [A B] end;
         split; [exact A|]; eexists; split; [exact B|];
         rewrite Z.add_0_r; symmetry; apply Z.mod_small; apply urange).
  - cbn [align_lin] in H. injection H as <- <-. split; [lia|]. exists 0. split; [apply Z.divide_0_r|].
    cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64. reflexivity.
  -
    assert (NORM : forall e' j' c', 0 <= j' <= 64 ->
              (exists N, (2 ^ j' | N)%Z /\ bv_unsigned (eval rho e') = (N + c') mod 2 ^ 64) ->
              0 <= align_norm (j', c') <= 64 /\ (2 ^ align_norm (j', c') | bv_unsigned (eval rho e'))%Z).
    { intros e' j' c' Hj (N & D & U). unfold align_norm. cbn [fst snd].
      pose proof (lit_align_sound c') as [La Lc].
      split; [lia|]. rewrite U. rewrite <- Zplus_mod_idemp_r.
      apply divide_mod64; [lia|]. apply Z.divide_add_r.
      - eapply divide_pow2_le; [|exact D]. lia.
      - eapply divide_pow2_le; [|exact Lc]. lia. }
    destruct op; try (cbn [align_lin] in H; injection H as <- <-;
         match goal with |- context [eval rho ?ee] => pose proof (align_sv_sound rho facts ee Hf) as [A B] end;
         split; [exact A|]; eexists; split; [exact B|];
         rewrite Z.add_0_r; symmetry; apply Z.mod_small; apply urange).
    +
      cbn [align_lin] in H. fold (align_lin facts e1) in H. fold (align_lin facts e2) in H.
      destruct (align_lin facts e1) as [ja ca] eqn:E1. destruct (align_lin facts e2) as [jb cb] eqn:E2.
      injection H as <- <-.
      destruct (IHe1 ja ca Hf eq_refl) as (A1 & N1 & D1 & U1). destruct (IHe2 jb cb Hf eq_refl) as (A2 & N2 & D2 & U2).
      split; [lia|]. exists (N1 + N2). split.
      * apply Z.divide_add_r; eapply divide_pow2_le; [|exact D1| |exact D2]; lia.
      * cbn [eval]. rewrite add_val, U1, U2. rewrite <- Z.add_mod by lia. f_equal. lia.
    +
      cbn [align_lin] in H. fold (align_lin facts e1) in H. fold (align_lin facts e2) in H.
      destruct (align_lin facts e1) as [ja ca] eqn:E1. destruct (align_lin facts e2) as [jb cb] eqn:E2.
      injection H as <- <-.
      destruct (IHe1 ja ca Hf eq_refl) as (A1 & X1). destruct (IHe2 jb cb Hf eq_refl) as (A2 & X2).
      destruct (NORM e1 ja ca A1 X1) as [B1 D1]. destruct (NORM e2 jb cb A2 X2) as [B2 D2].
      set (j1 := align_norm (ja, ca)) in *. set (j2 := align_norm (jb, cb)) in *.
      split; [lia|]. exists (bv_unsigned (eval rho (SAlu ALU_AND e1 e2))). split.
      2:{ rewrite Z.add_0_r. symmetry. apply Z.mod_small. apply urange. }
      cbn [eval]. rewrite and_val.
      pose proof (urange (eval rho e1)) as R1. pose proof (urange (eval rho e2)) as R2.
      apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. apply bits_mod0; [lia|]. intros i Hi.
      rewrite Z.land_spec.
      destruct (Z.le_gt_cases j2 j1).
      * rewrite Z.max_l in Hi by lia.
        rewrite (mod0_bits (bv_unsigned (eval rho e1)) j1); [reflexivity | lia | | lia].
        destruct D1 as [q ->]. apply Z_mod_mult.
      * rewrite Z.max_r in Hi by lia.
        rewrite (mod0_bits (bv_unsigned (eval rho e2)) j2); [apply Bool.andb_false_r | lia | | lia].
        destruct D2 as [q ->]. apply Z_mod_mult.
Qed.

Lemma align_sum_sound : ltac2:(tb__ "0|1|
S21S42S22A1S20S54S22S23R3A1R2A3S4S4S12Z0S68R3R2A2M0A2S12G0Z40A2A2S16S11Z2G0A2S9Q40S1fR4R2A2A2A2A2F_;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e Hf. unfold align_sum. destruct (align_lin facts e) as [j c] eqn:E.
  destruct (align_lin_sound rho facts e j c Hf E) as (A & N & D & U).
  pose proof (lit_align_sound c) as [La Lc]. unfold align_norm. cbn [fst snd].
  split; [lia|]. rewrite U. rewrite <- Zplus_mod_idemp_r.
  apply divide_mod64; [lia|]. apply Z.divide_add_r.
  - eapply divide_pow2_le; [|exact D]. lia.
  - eapply divide_pow2_le; [|exact Lc]. lia.
Qed.

Lemma or_aligned_add : ltac2:(tb__ "0|3|
S21S42S22A1S20S0S54S22S23R4A1R3A3S12Z0R2A2S13R3S11Z2S68R5R4A2A2A2S3S8Q40M0A1SeG0S1fR7R5A2M1SaG0R4A2M2A3SbG0G1G2A3A3F_;F_;F_;Fk;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e k Hf Hk0 Hk.
  destruct (align_sum_sound rho facts e Hf) as [A B].
  assert (Hand : Z.land (bv_unsigned (eval rho e)) k = 0).
  { pose proof (and_lit_eq (eval rho e) 0 k (align_sum facts e)) as E.
    assert (E' : bv_and (eval rho e) (Z_to_bv 64 k) = Z_to_bv 64 (Z.land (0 mod 2 ^ 64) k)).
    { apply E; try lia. rewrite Z.mod_0_l by lia. destruct B as [q Hq]. rewrite Hq. apply Z_mod_mult. }
    rewrite Z.mod_0_l, Z.land_0_l in E' by lia.
    apply (f_equal bv_unsigned) in E'. rewrite bv_and_unsigned, !Z_to_bv_unsigned in E'.
    unfold bv_wrap in E'. rewrite two64 in E'.
    assert (2 ^ align_sum facts e <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite (Z.mod_small k), (Z.mod_small 0) in E' by lia. exact E'. }
  pose proof (urange (eval rho e)) as R.
  assert (2 ^ align_sum facts e <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  apply bv_eq. rewrite bv_or_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite (Z.mod_small k) by lia.
  rewrite <- Z.lxor_lor by exact Hand. rewrite <- Z.add_nocarry_lxor by exact Hand.
  symmetry. apply Z.mod_small. split; [lia|].
  apply Z.add_nocarry_lt_pow2; [exact Hand | lia | lia].
Qed.

Lemma and_mask_fold2_sound : ltac2:(tb__ "0|1|
S21S42S22A1S20S0S20S54S22S23R5A1R4A3S3S41S20A1S71R5R4R3A3S3fS20R2A2A3S3S8Q40M0A1ScG0S1fR7R5A2SaG0R4A2A3S1fR7R3A2A3F_;F_;Fr;Fk;Fe;Ffacts;Frho;").
Proof.
  intros rho facts e k r Hf H. unfold and_mask_fold2 in H.
  destruct (and_mask_fold facts e k) as [r0|] eqn:E.
  - injection H as <-. exact (and_mask_fold_sound rho facts e k r0 Hf E).
  - exact (and_mask_gen_sound rho facts e k r Hf H).
Qed.

Lemma mk_alu_f_sound : ltac2:(tb__ "0|0|
S21S42S22A1S29S20S20S54S22S23R5A1R4A3S3S8Q40A1S1fR6S7aR5R4R3R2A4A2S48R4S1fR6R3A2S1fR6R2A2A3A3F_;Fb;Fa;Fop;Ffacts;Frho;").
Proof.
  intros rho facts op a b Hall. unfold mk_alu_f.
  destruct op; try apply mk_alu_sound.
  {   destruct b as [k| | | | | | |]; try apply mk_alu_sound.
    destruct ((0 <=? k) &&& (k <? 2 ^ align_sum facts a)) eqn:E; [|apply mk_alu_sound].
    destruct (Z.leb_spec 0 k); [|discriminate]. destruct (Z.ltb_spec k (2 ^ align_sum facts a)); [|discriminate].
    rewrite mk_alu_sound. change (eval rho (SLit k)) with (Z_to_bv 64 k). unfold alu64, alu.
    symmetry. apply (or_aligned_add rho facts); assumption. }
  assert (CaseA : forall k', a = SLit k' ->
      eval rho match and_mask_fold2 facts b k' with Some r => r | None => mk_alu ALU_AND a b end
      = alu64 ALU_AND (eval rho a) (eval rho b)).
  { intros k' ->. destruct (and_mask_fold2 facts b k') eqn:E; [|apply mk_alu_sound].
    change (eval rho (SLit k')) with (Z_to_bv 64 k').
    symmetry. unfold alu64, alu. rewrite bv_and_comm64. apply (and_mask_fold2_sound rho facts); assumption. }
  destruct b as [k| | | | | | |].
  1:{ destruct (and_mask_fold2 facts a k) eqn:E; [|apply mk_alu_sound].
      change (eval rho (SLit k)) with (Z_to_bv 64 k).
      symmetry. unfold alu64, alu. apply (and_mask_fold2_sound rho facts); assumption. }
  all: destruct a as [k'| | | | | | |]; first [apply (CaseA k' eq_refl) | apply mk_alu_sound].
Qed.

Definition core_of (ms : machine_state) : core := ltac2:(tb__ "0|0|
S4dS60Vms;A1S5cVms;A1S5fVms;A1S5bVms;A1S61Vms;A1A5").

Definition ms_of (ms : machine_state) (c : core) (m : word -> option byte) : machine_state := ltac2:(tb__ "0|0|
S57S51Vc;A1S4fVc;A1S50Vc;A1S45S8Q40A1A1S52Vc;A1S4eVc;A1Vm;S62Vms;A1A8").

Definition lift_result (ms : machine_state)
    (r : machine_result (core * (word -> option byte))) : machine_result machine_state := ltac2:(tb__ "0|3|
S56S43S4cS8Q40A1S41S8Q8A1A1F_;M0A2M1A1S56S55A1M2Lr;Vr;G1G1G2Lresult;R1S4cG0S59S55S89Vms;R2R1A3A2Lm';Lc;X43x1Lresult;S58S55A1S5aS55A1X56x3").

Lemma non_ecall_filter : ltac2:(tb__ "0|16|
S27S27S3S41S27A1M0S27G0Li;R2S8Q5A1M1S8Q14A1S3fS27R4A2M2Limm;Lrd;M3G3G1S8Q15A1G2Limm;Lrd;G1G1S8QcA1M4S3fS27R5A2M5Limm;Lrs1;Lrd;M6S33G1G1S8QdA1S3fS27R6A2M7Limm;Lrs2;Lrs1;Lc;S2dS40G1G1G4S3fS27R7A2M8Limm;Lrs1;Lrd;Lsigned;Lsz;S2dG1G1G4G7Limm;M9Lrs2;Lrs1;MaLsz;S29G1G1G9Lrs1;Lrd;MbLop;S29G1G1S8Q6A1G7Lshamt;Lrs1;Lrd;Lop;S29G1G1G1G7Lrs2;Lrs1;Lrd;McLop;MdG6S29G1G1G1G7Lshamt;Lrs1;Lrd;Lop;GdS8Q4A1MeGeGeG1G1G8Lrs1;Lrd;MfLsucc;Lpred;Lfm;G6S45S27A1S3fS27R2A2S2eGcLop;M10G10S2aS40S40GfLrl;Laq;Lw;S2aS40S40G1G1G1S3fS27R8A2M11Lrs2;Lrs1;Lrd;Lrl;Laq;Lw;S32S2aS40S40G1G1G1S3fS27R9A2M12Lrs2;Lrs1;Lrd;Lrl;Laq;Lw;Lop;S2bG1G1G4G7Lcsr;M13Lrs1;Lrd;Lop;S2bG1G1G13Luimm;Lrd;Lop;S28GbLfmt;S28GaLfmt;S36S28G1G1G1G1S8Q3A1M14G12Lrm;Lrs3;Lrs2;Lrs1;Lrd;Lfmt;Lop;S34S28G1G1G1G14G11Lrm;Lrs2;Lrs1;Lrd;Lfmt;Lop;S28G1G1G14G7Lrm;Lrs1;Lrd;Lfmt;S39S28G1G1G1G8Lrs2;Lrs1;Lrd;Lfmt;M15Lop;S37G15Lop;S35G15Lop;S2cS2cG1G1G14G8Lrm;Lrs1;Lrd;Lsrc;Ldst;S38S28G1G1G7Lrs1;Lrd;Lfmt;Ldir;S28G1G1G5Lrs1;Lrd;Lfmt;X27x23S3fS27R1A2A3S4S3S27R3R2A3S5S3S27R2S31A3A1A2F_;Fi0;Fi;").
Proof. intros i i0 H. destruct i; inversion H; split; congruence. Qed.

Lemma decode_size4 : ltac2:(tb__ "0|18|
S27S27S0S3S41S27A1M0S0G0Lisz;R1S45S27A1M1S1S1G0Lp;R1S1G1Lp0;S1S1G0Lp0;R1S1G1Lp1;S1S1G0Lp1;R1S1G1Lp2;M2G2S27G0Li;R6S8Q5A1M3S8Q14A1S3fS27R8A2M4Limm;Lrd;M5G5G3S8Q15A1G4Limm;Lrd;G3G3S8QcA1M6S3fS27R9A2M7Limm;Lrs1;Lrd;M8S33G3G3S8QdA1S3fS27RaA2M9Limm;Lrs2;Lrs1;Lc;S2dS40G3G3G6S3fS27RbA2MaLimm;Lrs1;Lrd;Lsigned;Lsz;S2dG3G3G6G9Limm;MbLrs2;Lrs1;McLsz;S29G3G3GbLrs1;Lrd;MdLop;S29G3G3S8Q6A1G9Lshamt;Lrs1;Lrd;Lop;S29G3G3G3G9Lrs2;Lrs1;Lrd;MeLop;MfG8S29G3G3G3G9Lshamt;Lrs1;Lrd;Lop;GfS8Q4A1M10G10G10G3G3GaLrs1;Lrd;M11Lsucc;Lpred;Lfm;G8G1S3fS27R6A2S2eGeLop;M12G12S2aS40S40G11Lrl;Laq;Lw;S2aS40S40G3G3G3S3fS27RcA2M13Lrs2;Lrs1;Lrd;Lrl;Laq;Lw;S32S2aS40S40G3G3G3S3fS27RdA2M14Lrs2;Lrs1;Lrd;Lrl;Laq;Lw;Lop;S2bG3G3G6G9Lcsr;M15Lrs1;Lrd;Lop;S2bG3G3G15Luimm;Lrd;Lop;S28GdLfmt;S28GcLfmt;S36S28G3G3G3G3S8Q3A1M16G14Lrm;Lrs3;Lrs2;Lrs1;Lrd;Lfmt;Lop;S34S28G3G3G3G16G13Lrm;Lrs2;Lrs1;Lrd;Lfmt;Lop;S28G3G3G16G9Lrm;Lrs1;Lrd;Lfmt;S39S28G3G3G3GaLrs2;Lrs1;Lrd;Lfmt;M17Lop;S37G17Lop;S35G17Lop;S2cS2cG3G3G16GaLrm;Lrs1;Lrd;Lsrc;Ldst;S38S28G3G3G9Lrs1;Lrd;Lfmt;Ldir;S28G3G3G7Lrs1;Lrd;Lfmt;X27x23X1x3Lp1;G1X1x3Lp0;G1X1x3Lp;S1G1Lp;X0x3S3fS27R2A2A3S4S3S0R2Z4A3S4S3S27R4R3A3S5S3S27R3S31A3A1A2A2F_;Fisz;Fi0;Fi;").
Proof.
  intros i i0 isz H.
  destruct isz as [|p|p]; try discriminate; destruct p as [p|p|]; try discriminate;
    destruct p as [p|p|]; try discriminate; destruct p; try discriminate.
  split; [reflexivity|]. apply non_ecall_filter. exact H.
Qed.

Lemma step_instr_at : ltac2:(tb__ "0|1|
S42S85A1S55S0S27S3S8Q40M0A1S5eR3A1SaG0R2A2A3S3S41S27A1S74R5R3A2S3fS27R2A2A3S5S3S27R3S31A3A1S3S56S55A1S63R7R6A2S88R6S86R7S53SaG0Z4A2R4S87R6A1A3S5dR6A1A3A2A3F_;F_;F_;Fi;Fpc;Fms;Fsegs;").
Proof.
  intros segs ms pc i Hpc Hi Hne.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. rewrite Hpc. unfold instr_at in Hi.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses. destruct (is_ecall w) eqn:He.
  - inversion Hi. subst. contradiction.
  - destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
    apply decode_size4 in Hi as (-> & -> & _).
    rewrite <- interp_eff_interp_eff0.
    unfold lift_result, core_of, ms_of, RiscvSemantics.interp_eff, RiscvSemantics.drop_access_report.
    destruct ms; cbn. destruct (RiscvSemantics.interp_eff_accesses segs _ _) as [[[c mm] acc]| |]; reflexivity.
Qed.

Lemma step_ecall_at : forall segs ms pc,
  ms_pc ms = Z_to_bv 64 pc ->
  instr_at segs pc = Some Ecall ->
  RiscvSemantics.step segs ms = MachineOk
    {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
       ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
       ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Proof.
  intros segs ms pc Hpc Hi.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. rewrite Hpc. unfold instr_at in Hi.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses. destruct (is_ecall w) eqn:He.
  - destruct ms; reflexivity.
  - destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
    apply decode_size4 in Hi as (_ & _ & Hc). exfalso. apply Hc. reflexivity.
Qed.
