(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "bv_signed"; "bv_swrap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sv"; "valuation"; "holds"; "sprop"; "SPBranch"; "SAlu"; "ss_next"; "SPNot"; "SLit"; "agree_below"; "ss_facts"; "sstate"; "SMd"; "sprop_below"; "SPEq"; "ext_low"; "sobj"; "SPTrue"; "SPUle"; "SPUlt"; "SVar"; "rw"; "@Corelib.Init.Logic"; "eq"; "iff"; "and"; "not"; "or"; "True"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "sub"; "le"; "pow"; "lt"; "ltb"; "mul"; "shiftr"; "add"; "of_N"; "div"; "eqb"; "lxor"; "@Corelib.Init.Datatypes"; "list"; "bool"; "Some"; "true"; "option"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "M64v"; "Zsigned"; "and_hmask"; "zconj"; "zp"; "H63v"; "ext_width_ok"; "msubst_facts"; "zsext"; "zv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "RsSymJump"; "mkLeaf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "add_facts"; "vn_state"; "SPfamE"; "enode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_sub"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.NArith.BinNat.N"; "le"; "lt"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "BC_GE"; "BC_GEU"; "BC_LT"; "BC_LTU"; "BC_NE"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SLT"; "ALU_SLTU"; "ALU_SRA"; "ALU_SRL"; "ALU_SUB"; "ALU_XOR"; "M_MUL"; "M_MULH"; "M_MULHU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_check"; "import_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgGlue"; "to_enodeI"; "vmeasI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundM SymFrame SymSoundR SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CfgGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint msubst_facts (s : wsub) (F : list sprop) : option (list sprop) :=
  match F with
  | [] => Some []
  | p :: r => match sprop_subst s p, msubst_facts s r with
              | Some p', Some r' => Some (p' :: r')
              | _, _ => None
              end
  end.

Lemma msubst_facts_sound : ltac2:(tb__ "0|1|
S9S57S32SbA1M0G0S1eS36G0A1S40R3R2A2S34G0R1A2A3S49SbSaR5A1R2A3S49SbSaS58R6R5A2A1R4A3F_;F_;FF';FF;Fs;Frho;").
Proof.
  intros rho s F. induction F as [|p r IH]; intros F' H HF; [constructor|].
  cbn in H. destruct (sprop_subst s p) as [p'|] eqn:Ep; [|discriminate].
  destruct (msubst_facts s r) as [r'|] eqn:Er; [|discriminate]. injection H as <-.
  inversion HF as [|p'' r'' Hp Hr]; subst.
  constructor.
  - apply (proj1 (sprop_subst_sound rho s p p' Ep)). exact Hp.
  - eapply IH; [reflexivity | exact Hr].
Qed.

Ltac glue_subst s F :=
  let fv := eval vm_compute in (msubst_facts s F) in
  lazymatch fv with
  | Some ?l => apply (msubst_facts_sound _ s F l); [vm_compute; reflexivity|]
  end.

Definition M64v : Z := 18446744073709551616.
Lemma M64v_eq : 2 ^ 64 = M64v. Proof. reflexivity. Qed.

Lemma U_add : ltac2:(tb__ "0|1|
S9S8S8S1eS1S3Q40M0S7R3SdS63R2R1A3A2A2S25S2dS3G0S7R3R2A2A2S3G0S7R3R1A2A2A2S39A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. rewrite add_val, M64v_eq. reflexivity. Qed.
Lemma U_sub : ltac2:(tb__ "0|1|
S9S8S8S1eS1S3Q40M0S7R3SdS6aR2R1A3A2A2S25S26S3G0S7R3R2A2A2S3G0S7R3R1A2A2A2S39A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. rewrite sub_val, M64v_eq. reflexivity. Qed.
Lemma U_lit : ltac2:(tb__ "0|0|
S9S1S1eS1S3Q40S7R2S10R1A1A2A2S25R1S39A2A3Fc;Frho;").
Proof. intros. cbn [eval]. rewrite lit_unsigned, M64v_eq. reflexivity. Qed.
Lemma eval_var : ltac2:(tb__ "0|0|
S9S0S1eS4Q40A1S7R2S1cR1A1A2S1dR2R1A2A3Fi;Frho;").
Proof. reflexivity. Qed.
Lemma U_sltu : ltac2:(tb__ "0|1|
S9S8S8S1eS1S3Q40M0S7R3SdS67R2R1A3A2A2S33S1L_;S2aS3G0S7R3R2A2A2S3G0S7R3R1A2A2A2Z1Z0X33x2A3Fb;Fa;Frho;").
Proof.
  intros. cbn [eval]. unfold alu64, alu, bv_ltu.
  destruct (bv_unsigned (eval rho a) <? bv_unsigned (eval rho b)); reflexivity.
Qed.
Lemma U_range : ltac2:(tb__ "0|2|
S4Q40M0A1S20S27Z0S3G0R1A2M1A2S29G1S39A2A2Fw;").
Proof. intros w. rewrite <- M64v_eq. apply urange. Qed.
Lemma U_mul : ltac2:(tb__ "0|1|
S9S8S8S1eS1S3Q40M0S7R3S14S6cR2R1A3A2A2S25S2bS3G0S7R3R2A2A2S3G0S7R3R1A2A2A2S39A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. rewrite mul_val, M64v_eq. reflexivity. Qed.

Definition H63v : Z := 9223372036854775808.
Definition Zsigned (u : Z) : Z := ltac2:(tb__ "0|0|
S33S1L_;S2aVu;S3eA2Vu;S26Vu;S39A2X33x2").
Lemma Zsigned_spec : ltac2:(tb__ "0|2|
S1S22S20S29R1Z8000000000000000M0A2S1eS1S3aR1A1M1R1A3A2S20S27G0R1A2S1eS1G1S26R1Z10000000000000000A2A3A2A2Fu;").
Proof. intros u. unfold Zsigned, H63v, M64v. destruct (Z.ltb_spec u 9223372036854775808); lia. Qed.
Lemma bv_signed_U : ltac2:(tb__ "0|1|
S4Q40M0A1S1eS1S5G0R1A2S3aS3G0R1A2A1A3Fw;").
Proof.
  intros w. pose proof (urange w) as R. unfold Zsigned, H63v, M64v.
  destruct (Z.ltb_spec (bv_unsigned w) 9223372036854775808).
  - apply signed_small. change (2 ^ 63) with 9223372036854775808. lia.
  - unfold bv_signed, bv_swrap, bv_wrap in *. rewrite two64 in *.
    change (bv_half_modulus 64) with (9223372036854775808) in *.
    change (2 ^ 64) with 18446744073709551616 in *.
    replace (bv_unsigned w + 9223372036854775808)
      with ((bv_unsigned w - 9223372036854775808) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma swrap_mod : ltac2:(tb__ "0|1|
S1S1eS1S25S6Q40R1A2S28Z2Z40A2M0A2S25R1G0A2A3Fx;").
Proof.
  intros x. unfold bv_swrap, bv_wrap. rewrite two64. change (bv_half_modulus 64) with (2 ^ 63).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma U_of_signed : ltac2:(tb__ "0|1|
S4Q40M0A1S1eS1S3G0R1A2S25S5G0R1A2S28Z2Z40A2A2A3Fw;").
Proof.
  intros w. pose proof (urange w). unfold bv_signed. rewrite swrap_mod. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma U_slt : ltac2:(tb__ "0|1|
S9S8S8S1eS1S3Q40M0S7R3SdS66R2R1A3A2A2S33S1L_;S2aS3aS3G0S7R3R2A2A2A1S3aS3G0S7R3R1A2A2A1A2Z1Z0X33x2A3Fb;Fa;Frho;").
Proof.
  intros. cbn [eval]. unfold alu64, alu, bv_lts. rewrite !bv_signed_U.
  destruct (Zsigned _ <? Zsigned _); reflexivity.
Qed.
Lemma U_mulh : ltac2:(tb__ "0|1|
S9S8S8S1eS1S3Q40M0S7R3S14S6dR2R1A3A2A2S25S2cS2bS3aS3G0S7R3R2A2A2A1S3aS3G0S7R3R1A2A2A1A2Z40A2S39A2A3Fb;Fa;Frho;").
Proof.
  intros. cbn [eval]. unfold mul_div, bv_mulhss. rewrite lit_unsigned, !bv_signed_U, M64v_eq. reflexivity.
Qed.
Lemma U_mulhu : ltac2:(tb__ "0|1|
S9S8S8S1eS1S3Q40M0S7R3S14S6eR2R1A3A2A2S25S2cS2bS3G0S7R3R2A2A2S3G0S7R3R1A2A2A2Z40A2S39A2A3Fb;Fa;Frho;").
Proof.
  intros. cbn [eval]. unfold mul_div, bv_mulhuu. rewrite lit_unsigned, M64v_eq. reflexivity.
Qed.
Lemma U_sra_lit : ltac2:(tb__ "0|1|
S9S8S1S1eS1S3Q40M0S7R3SdS68R2S10R1A1A3A2A2S25S2cS3aS3G0S7R3R2A2A2A1S25R1Z40A2A2S39A2A3Fk;Fa;Frho;").
Proof.
  intros. cbn [eval]. unfold alu64, alu.
  rewrite U_of_signed, bv_ashiftr_signed, shamt_val, bv_signed_U, swrap_mod, M64v_eq. reflexivity.
Qed.

Lemma holds_ule : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3S1aR2R1A2A2S27S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A2A2Fb;Fa;Frho;").
Proof. intros. cbn. tauto. Qed.
Lemma holds_ult : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3S1bR2R1A2A2S29S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A2A2Fb;Fa;Frho;").
Proof. intros. cbn. tauto. Qed.
Lemma holds_eq : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3S16R2R1A2A2S1eS1S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A3A2Fb;Fa;Frho;").
Proof. intros. cbn [holds]. split; [intros ->; reflexivity | intros H; apply bv_eq; exact H]. Qed.
Lemma holds_neq : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3SfS16R2R1A2A1A2S21S1eS1S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A3A1A2Fb;Fa;Frho;").
Proof. intros. cbn [holds]. rewrite bv_eq. tauto. Qed.
Lemma holds_beq : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3ScS5dR2R1A3A2S1eS1S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A3A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_eqb. rewrite Z.eqb_eq. tauto. Qed.
Lemma holds_nbeq : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3SfScS5dR2R1A3A1A2S21S1eS1S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A3A1A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_eqb. rewrite Z.eqb_eq. tauto. Qed.
Lemma holds_bne : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3ScS62R2R1A3A2S21S1eS1S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A3A1A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_eqb. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto. Qed.
Lemma holds_nbne : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3SfScS62R2R1A3A1A2S1eS1S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A3A2Fb;Fa;Frho;").
Proof.
  intros. cbn [holds branch_taken]. unfold bv_eqb. rewrite Bool.negb_true_iff.
  destruct (Z.eqb_spec (bv_unsigned (eval rho a)) (bv_unsigned (eval rho b))); split; intros; try tauto; congruence.
Qed.
Lemma holds_bltu : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3ScS61R2R1A3A2S29S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_ltu. rewrite Z.ltb_lt. tauto. Qed.
Lemma holds_nbltu : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3SfScS61R2R1A3A1A2S27S3Q40M0S7R3R1A2A2S3G0S7R3R2A2A2A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_ltu. rewrite Z.ltb_lt. lia. Qed.
Lemma holds_bgeu : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3ScS5fR2R1A3A2S27S3Q40M0S7R3R1A2A2S3G0S7R3R2A2A2A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_ltu. rewrite Bool.negb_true_iff, Z.ltb_ge. lia. Qed.
Lemma holds_nbgeu : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3SfScS5fR2R1A3A1A2S29S3Q40M0S7R3R2A2A2S3G0S7R3R1A2A2A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_ltu. rewrite Bool.negb_true_iff, Z.ltb_ge. lia. Qed.
Lemma holds_blt : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3ScS60R2R1A3A2S29S3aS3Q40M0S7R3R2A2A2A1S3aS3G0S7R3R1A2A2A1A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_lts. rewrite !bv_signed_U, Z.ltb_lt. tauto. Qed.
Lemma holds_nblt : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3SfScS60R2R1A3A1A2S27S3aS3Q40M0S7R3R1A2A2A1S3aS3G0S7R3R2A2A2A1A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_lts. rewrite !bv_signed_U, Z.ltb_lt. lia. Qed.
Lemma holds_bge : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3ScS5eR2R1A3A2S27S3aS3Q40M0S7R3R1A2A2A1S3aS3G0S7R3R2A2A2A1A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_lts. rewrite !bv_signed_U, Bool.negb_true_iff, Z.ltb_ge. lia. Qed.
Lemma holds_nbge : ltac2:(tb__ "0|1|
S9S8S8S1fSaR3SfScS5eR2R1A3A1A2S29S3aS3Q40M0S7R3R2A2A2A1S3aS3G0S7R3R1A2A2A1A2A2Fb;Fa;Frho;").
Proof. intros. cbn [holds branch_taken]. unfold bv_lts. rewrite !bv_signed_U, Bool.negb_true_iff, Z.ltb_ge. lia. Qed.
Lemma holds_true : ltac2:(tb__ "0|0|
S9S1fSaR1S19A2S23A2Frho;").
Proof. intros. cbn. tauto. Qed.

Lemma U_zext_w : ltac2:(tb__ "0|1|
S2S4Q40M0A1S5bR2G0A2S1eS1S3G0S17S38R3R2A3A2S25S3G0R2A2S28Z2S2eR3A1A2A2A3F_;Fv;Fw;").
Proof.
  intros w v Hw. unfold ext_low, zext. rewrite bv_zero_extend_unsigned, bv_extract_0_unsigned by exact Hw.
  unfold bv_wrap, bv_modulus. reflexivity.
Qed.
Definition zsext (w : Z) (m : Z) : Z := ltac2:(tb__ "0|1|
S33S1L_;S2aVm;S28Z2M0S26Vw;Z1A2A2A2Vm;S26S2dVm;S39A2S28G0Vw;A2A2X33x2").
Lemma U_sext_w : ltac2:(tb__ "0|2|
S2S4Q40M0A1S5cQ0R2A2S5bR3G0A2S1eS1S3G0S17S35R4R3A3A2S41S2eR4A1M1S25S3G0R3A2S28Z2G1A2A2A2A3F_;F_;Fv;Fw;").
Proof.
  intros w v Hw0 Hw. unfold ext_low, sext, zsext. rewrite bv_sign_extend_unsigned, <- M64v_eq.
  unfold bv_signed. rewrite bv_extract_0_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  set (m := bv_unsigned v mod 2 ^ Z.of_N w).
  assert (Hm : 0 <= m < 2 ^ Z.of_N w) by (subst m; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  assert (Hh : 2 ^ Z.of_N w = 2 * 2 ^ (Z.of_N w - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (Hp : 0 < 2 ^ (Z.of_N w - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (H64 : 2 ^ Z.of_N w <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  change (Z.of_N 64) with 64.
  assert (Hhalf : 2 ^ Z.of_N w `div` 2 = 2 ^ (Z.of_N w - 1)).
  { rewrite Hh. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  rewrite !Hhalf.
  destruct (Z.ltb_spec m (2 ^ (Z.of_N w - 1))).
  - rewrite (Z.mod_small (m + _) (2 ^ Z.of_N w)) by lia.
    replace (m + 2 ^ (Z.of_N w - 1) - 2 ^ (Z.of_N w - 1)) with m by lia.
    apply Z.mod_small. lia.
  - replace (m + 2 ^ (Z.of_N w - 1)) with ((m - 2 ^ (Z.of_N w - 1)) + 1 * 2 ^ Z.of_N w) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (m - _)) by lia.
    replace (m - 2 ^ (Z.of_N w - 1) - 2 ^ (Z.of_N w - 1)) with ((m + 2 ^ 64 - 2 ^ Z.of_N w) + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Definition ext_width_ok (w : N) : bool := match w with 8%N | 16%N | 32%N => true | _ => false end.
Lemma ext_width_ok_bounds : ltac2:(tb__ "0|0|
S2S1eS33S3fR1A1S35A3S20S5cQ0R2A2S5bR2Q40A2A2F_;Fw;").
Proof.
  intros w H. unfold ext_width_ok in H.
  destruct w as [|p]; [discriminate|].
  repeat (destruct p as [p|p|]; try discriminate); lia.
Qed.

Definition and_hmask (k : Z) : option Z :=
  match k with
  | 18446744073709551614 | -2 => Some 2
  | 18446744073709551612 | -4 => Some 4
  | 18446744073709551608 | -8 => Some 8
  | 18446744073709551600 | -16 => Some 16
  | 18446744073709551584 | -32 => Some 32
  | 18446744073709551552 | -64 => Some 64
  | 18446744073709547520 | -4096 => Some 4096
  | _ => None
  end.
Lemma and_hmask_sound : ltac2:(tb__ "0|1|
S1S1S1eS36S1A1S3bR2A1S34S1R1A2A3S24S1S1S20S20S27Z0R1A2S27R1Z40A2A2S20S1eS1R3S28Z2R1A2M0A3S1eS1S25R4S39A2S26S39G0A2A3A2A2Lj;A2F_;Fm;Fk;").
Proof.
  intros k m H. unfold and_hmask in H.
  repeat match type of H with
  | (match ?k with _ => _ end) = _ => destruct k; try discriminate
  end;
  injection H as <-;
  first [ exists 1; split; [lia|]; split; reflexivity
        | exists 2; split; [lia|]; split; reflexivity
        | exists 3; split; [lia|]; split; reflexivity
        | exists 4; split; [lia|]; split; reflexivity
        | exists 5; split; [lia|]; split; reflexivity
        | exists 6; split; [lia|]; split; reflexivity
        | exists 12; split; [lia|]; split; reflexivity ].
Qed.
Lemma U_and_hmask : ltac2:(tb__ "0|2|
S9S8S1S1S1eS36S1A1S3bR2A1S34S1R1A2A3S1eS1S3Q40M0S7R5SdS64R4S10R3A1A3A2A2S26S3G0S7R5R4A2A2M1S25G1R2A2A2A3F_;Fm;Fk;Fa;Frho;").
Proof.
  intros rho a k m H. destruct (and_hmask_sound k m H) as (j & Hj & -> & Hk).
  cbn [eval]. unfold alu64, alu. rewrite bv_and_unsigned, lit_unsigned.
  pose proof (U_range (eval rho a)) as R. rewrite <- M64v_eq in *. rewrite Hk. unfold M64v in *.
  apply land_high_mask; [exact Hj | exact R].
Qed.

Fixpoint zv (rho : valuation) (e : sv) : Z :=
  match e with
  | SLit c => c mod M64v
  | SVar i => bv_unsigned (rw rho i)
  | SAlu ALU_ADD a b => (zv rho a + zv rho b) mod M64v
  | SAlu ALU_SUB a b => (zv rho a - zv rho b) mod M64v
  | SAlu ALU_SLTU a b => if zv rho a <? zv rho b then 1 else 0
  | SAlu ALU_SLT a b => if Zsigned (zv rho a) <? Zsigned (zv rho b) then 1 else 0
  | SAlu ALU_SRA a (SLit k) => (Z.shiftr (Zsigned (zv rho a)) (k mod 64)) mod M64v
  | SAlu ALU_SLL a (SLit k) => (zv rho a * 2 ^ (k mod 64)) mod M64v
  | SAlu ALU_SRL a (SLit k) => zv rho a / 2 ^ (k mod 64)
  | SAlu ALU_XOR a (SLit k) => if (k mod M64v =? M64v - 1) then M64v - 1 - zv rho a else bv_unsigned (eval rho e)
  | SAlu ALU_AND a (SLit k) => match and_hmask k with
                              | Some m => zv rho a - (zv rho a) mod m
                              | None => bv_unsigned (eval rho e)
                              end
  | SMd M_MUL a b => (zv rho a * zv rho b) mod M64v
  | SMd M_MULH a b => (Z.shiftr (Zsigned (zv rho a) * Zsigned (zv rho b)) 64) mod M64v
  | SMd M_MULHU a b => (Z.shiftr (zv rho a * zv rho b) 64) mod M64v
  | SExt sgn w a => if ext_width_ok w then
                      (if sgn then zsext (Z.of_N w) (zv rho a mod 2 ^ Z.of_N w) else zv rho a mod 2 ^ Z.of_N w)
                    else bv_unsigned (eval rho e)
  | _ => bv_unsigned (eval rho e)
  end.

Lemma U_sll_lit : ltac2:(tb__ "0|1|
S9S8S1S1eS1S3Q40M0S7R3SdS65R2S10R1A1A3A2A2S25S2bS3G0S7R3R2A2A2S28Z2S25R1Z40A2A2A2S39A2A3Fk;Fa;Frho;").
Proof.
  intros. cbn [eval]. rewrite sll_val, Z.shiftl_mul_pow2, M64v_eq by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.
Lemma U_srl_lit : ltac2:(tb__ "0|1|
S9S8S1S1eS1S3Q40M0S7R3SdS69R2S10R1A1A3A2A2S2fS3G0S7R3R2A2A2S28Z2S25R1Z40A2A2A2A3Fk;Fa;Frho;").
Proof.
  intros. cbn [eval]. rewrite srl_val, Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). reflexivity.
Qed.

Lemma lxor_ones64 : ltac2:(tb__ "0|2|
S1S20S27Z0R1A2S29R1S28Z2Z40A2M0A2A2S1eS1S31R2S26G0Z1A2M1A2S26G1R2A2A3F_;Fx;").
Proof.
  intros x Hx.
  replace (2 ^ 64 - 1) with (Z.lnot (- 2 ^ 64)) by (unfold Z.lnot; lia).
  rewrite <- Z.lnot_lxor_r, <- Z.add_nocarry_lxor.
  - unfold Z.lnot. lia.
  - replace (- 2 ^ 64) with (Z.lnot (Z.ones 64)) by (rewrite Z.ones_equiv; unfold Z.lnot; lia).
    rewrite <- Z.ldiff_land. apply Z.ldiff_ones_r_low; [lia|].
    destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma U_xor_m1 : ltac2:(tb__ "0|2|
S9S8S1S1eS33S30S25R1S39A2S26S39Z1A2M0A2S35A3S1eS1S3Q40M1S7R4SdS6bR3S10R2A1A3A2A2S26G0S3G1S7R4R3A2A2A2A3F_;Fc;Fa;Frho;").
Proof.
  intros rho a c Hc. apply Z.eqb_eq in Hc. cbn [eval]. unfold alu64, alu. rewrite bv_xor_unsigned, lit_unsigned.
  rewrite M64v_eq in *. rewrite Hc. pose proof (U_range (eval rho a)) as R. rewrite <- M64v_eq in *.
  apply lxor_ones64. unfold M64v in R. lia.
Qed.

Lemma zv_sound : ltac2:(tb__ "0|0|
S9S8S1eS1S42R2R1A2S3Q40S7R2R1A2A2A3Fe;Frho;").
Proof.
  intros rho e. induction e; try reflexivity; try (destruct op; try reflexivity).
  - cbn [zv]. rewrite IHe1, IHe2, U_add. reflexivity.
  - cbn [zv]. rewrite IHe1, IHe2, U_sub. reflexivity.
  - destruct e2; try reflexivity. cbn [zv]. cbn [zv] in IHe1. rewrite IHe1, U_sll_lit. reflexivity.
  - cbn [zv]. rewrite IHe1, IHe2, U_slt. reflexivity.
  - cbn [zv]. rewrite IHe1, IHe2, U_sltu. reflexivity.
  - destruct e2; try reflexivity. cbn [zv]. cbn [zv] in IHe1.
    destruct (z mod M64v =? M64v - 1) eqn:E; [|reflexivity]. rewrite IHe1, (U_xor_m1 rho e1 z E). reflexivity.
  - destruct e2; try reflexivity. cbn [zv]. cbn [zv] in IHe1. rewrite IHe1, U_srl_lit. reflexivity.
  - destruct e2; try reflexivity. cbn [zv]. cbn [zv] in IHe1. rewrite IHe1, U_sra_lit. reflexivity.
  - destruct e2; try reflexivity. cbn [zv]. cbn [zv] in IHe1.
    destruct (and_hmask z) as [m|] eqn:E; [|reflexivity]. rewrite IHe1, (U_and_hmask rho e1 z m E). reflexivity.
  - cbn [zv]. rewrite IHe1, IHe2, U_mul. reflexivity.
  - cbn [zv]. rewrite IHe1, IHe2, U_mulh. reflexivity.
  - cbn [zv]. rewrite IHe1, IHe2, U_mulhu. reflexivity.
  - cbn [zv eval]. destruct (ext_width_ok w) eqn:E; [|reflexivity].
    destruct (ext_width_ok_bounds w E) as [E1 E2]. destruct sgn.
    + rewrite IHe, U_sext_w by assumption. reflexivity.
    + rewrite IHe, U_zext_w by assumption. reflexivity.
Qed.

Fixpoint zp (rho : valuation) (p : sprop) : Prop :=
  match p with
  | SPUle a b => zv rho a <= zv rho b
  | SPUlt a b => zv rho a < zv rho b
  | SPEq a b => zv rho a = zv rho b
  | SPNot q => ~ zp rho q
  | SPBranch BC_EQ a b => zv rho a = zv rho b
  | SPBranch BC_NE a b => zv rho a <> zv rho b
  | SPBranch BC_LTU a b => zv rho a < zv rho b
  | SPBranch BC_GEU a b => zv rho b <= zv rho a
  | SPBranch BC_LT a b => Zsigned (zv rho a) < Zsigned (zv rho b)
  | SPBranch BC_GE a b => Zsigned (zv rho b) <= Zsigned (zv rho a)
  | SPTrue => True
  | SPAlign i a => 0 <= a /\ (bv_unsigned (rw rho i)) mod 2 ^ a = 0
  end.

Lemma zp_iff : ltac2:(tb__ "0|0|
S9SbS1fS3dR2R1A2SaR2R1A2A2Fp;Frho;").
Proof.
  intros rho p. induction p; cbn [zp]; rewrite ?zv_sound.
  - destruct c; rewrite ?zv_sound.
    + rewrite holds_beq. tauto.
    + rewrite holds_bne. tauto.
    + rewrite holds_blt. tauto.
    + rewrite holds_bge. tauto.
    + rewrite holds_bltu. tauto.
    + rewrite holds_bgeu. tauto.
  - cbn [holds]. tauto.
  - rewrite holds_ult. tauto.
  - rewrite holds_ule. tauto.
  - rewrite holds_eq. tauto.
  - cbn. tauto.
  - cbn. tauto.
Qed.

Fixpoint zconj (rho : valuation) (l : list sprop) : Prop :=
  match l with [] => True | p :: t => zp rho p /\ zconj rho t end.

Lemma zconj_Forall : ltac2:(tb__ "0|0|
S9S32SbA1S3cR2R1A2S49SbSaR3A1R2A3F_;Fl;Frho;").
Proof.
  intros rho l. induction l as [|p t IH]; cbn [zconj]; intros H; constructor.
  - apply (proj1 (zp_iff rho p)). tauto.
  - apply IH. tauto.
Qed.
Lemma Forall_zconj : ltac2:(tb__ "0|0|
S9S32SbA1S49SbSaR2A1R1A3S3cR3R2A2F_;Fl;Frho;").
Proof.
  intros rho l H. induction H as [|p t Hp Ht IH]; cbn [zconj]; [exact I|].
  split; [apply (proj2 (zp_iff rho p)); exact Hp | exact IH].
Qed.
Lemma holds_zp : ltac2:(tb__ "0|0|
S9SbSaR2R1A2S3dR3R2A2F_;Fp;Frho;").
Proof. intros rho p. apply (proj2 (zp_iff rho p)). Qed.

Ltac Forall_facts H :=
  repeat lazymatch type of H with
    | Forall _ (_ :: _) => let H1 := fresh "F" in apply Forall_cons_iff in H as [H1 H]
    | Forall _ [] => clear H
    | Forall _ (_ ++ _) => let H1 := fresh "F" in apply Forall_app in H as [H1 H]; Forall_facts H1
    end.

Ltac concrete_facts H :=
  lazymatch type of H with
  | Forall ?P ?l => let l' := eval vm_compute in l in change (Forall P l') in H
  end.

Lemma Forall_pick : forall {A} (P : A -> Prop) l i x, Forall P l -> nth_error l i = Some x -> P x.
Proof. intros A P l i x H Hn. apply (proj1 (Forall_forall P l) H). eapply nth_error_In; eauto. Qed.
Ltac pick_facts H idxs :=
  let rec go l := lazymatch l with
    | nil => clear H
    | ?i :: ?t => pose proof (Forall_pick _ _ i _ H eq_refl); go t
    end in go idxs.

Ltac concrete_svs :=
  repeat match goal with
    | |- context [eval _ ?a] => let a' := eval vm_compute in a in progress change a with a'
    end.

Ltac zholds_rw_in H :=
  first [ apply (proj1 (holds_ule _ _ _)) in H | apply (proj1 (holds_ult _ _ _)) in H
        | apply (proj1 (holds_eq _ _ _)) in H | apply (proj1 (holds_neq _ _ _)) in H
        | apply (proj1 (holds_beq _ _ _)) in H | apply (proj1 (holds_nbeq _ _ _)) in H
        | apply (proj1 (holds_bne _ _ _)) in H | apply (proj1 (holds_nbne _ _ _)) in H
        | apply (proj1 (holds_bltu _ _ _)) in H | apply (proj1 (holds_nbltu _ _ _)) in H
        | apply (proj1 (holds_bgeu _ _ _)) in H | apply (proj1 (holds_nbgeu _ _ _)) in H
        | apply (proj1 (holds_blt _ _ _)) in H | apply (proj1 (holds_nblt _ _ _)) in H
        | apply (proj1 (holds_bge _ _ _)) in H | apply (proj1 (holds_nbge _ _ _)) in H ];
  repeat (rewrite ?U_add, ?U_sub, ?U_sltu, ?U_slt, ?U_mul, ?U_mulh, ?U_sra_lit, ?U_lit, ?eval_var in H).
Ltac zholds_rw_goal :=
  first [ apply (proj2 (holds_ule _ _ _)) | apply (proj2 (holds_ult _ _ _))
        | apply (proj2 (holds_eq _ _ _)) | apply (proj2 (holds_neq _ _ _))
        | apply (proj2 (holds_beq _ _ _)) | apply (proj2 (holds_nbeq _ _ _))
        | apply (proj2 (holds_bne _ _ _)) | apply (proj2 (holds_nbne _ _ _))
        | apply (proj2 (holds_bltu _ _ _)) | apply (proj2 (holds_nbltu _ _ _))
        | apply (proj2 (holds_bgeu _ _ _)) | apply (proj2 (holds_nbgeu _ _ _))
        | apply (proj2 (holds_blt _ _ _)) | apply (proj2 (holds_nblt _ _ _))
        | apply (proj2 (holds_bge _ _ _)) | apply (proj2 (holds_nbge _ _ _))
        | idtac ];
  repeat (rewrite ?U_add, ?U_sub, ?U_sltu, ?U_slt, ?U_mul, ?U_mulh, ?U_sra_lit, ?U_lit, ?eval_var).

Ltac Forall_goal := repeat first [apply Forall_nil | apply Forall_cons].

Ltac split_ltb :=
  repeat match goal with
    | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
    | H : context [Z.ltb ?x ?y] |- _ => destruct (Z.ltb_spec x y)
    end.

Ltac name_words :=
  repeat match goal with
    | |- context [bv_unsigned (rw ?r ?i)] =>
        let x := fresh "w" in pose proof (U_range (rw r i)); set (x := bv_unsigned (rw r i)) in *; clearbody x
    | H : context [bv_unsigned (rw ?r ?i)] |- _ =>
        let x := fresh "w" in pose proof (U_range (rw r i)); set (x := bv_unsigned (rw r i)) in *; clearbody x
    end;
  repeat match goal with
    | |- context [bv_unsigned ?v] =>
        let x := fresh "u" in pose proof (U_range v); set (x := bv_unsigned v) in *; clearbody x
    | H : context [bv_unsigned ?v] |- _ =>
        lazymatch type of H with
        | 0 <= bv_unsigned v < M64v => fail
        | _ => let x := fresh "u" in pose proof (U_range v); set (x := bv_unsigned v) in *; clearbody x
        end
    end.

Ltac is_zlit e :=
  lazymatch e with
  | Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac
  end.
Ltac eval_pows :=
  repeat match goal with
    | |- context [Z.pow (Zpos ?a) (Zpos ?b)] =>
        let v := eval vm_compute in (Z.pow (Zpos a) (Zpos b)) in change (Z.pow (Zpos a) (Zpos b)) with v in *
    | H : context [Z.pow (Zpos ?a) (Zpos ?b)] |- _ =>
        let v := eval vm_compute in (Z.pow (Zpos a) (Zpos b)) in change (Z.pow (Zpos a) (Zpos b)) with v in *
    end.
Ltac elim_shiftr :=
  repeat match goal with
    | |- context [Z.shiftr ?e (Zpos ?k)] => rewrite (Z.shiftr_div_pow2 e (Zpos k)) in * by lia
    | H : context [Z.shiftr ?e (Zpos ?k)] |- _ => rewrite (Z.shiftr_div_pow2 e (Zpos k)) in * by lia
    end; eval_pows.
Ltac divmod_lit1 e c :=
  is_zlit e; is_zlit c;
  let v := eval vm_compute in (e mod c) in change (e mod c) with v in *;
  let v := eval vm_compute in (e / c) in change (e / c) with v in *.
Ltac divmod_euclid e c :=
  is_zlit c;
  pose proof (Z.div_mod e c ltac:(lia));
  pose proof (Z.mod_pos_bound e c ltac:(lia));
  let q := fresh "q" in let r := fresh "r" in
  set (r := e mod c) in *; set (q := e / c) in *; clearbody r q.
Ltac divmod_lits :=
  repeat match goal with
    | |- context [?e mod ?c] => divmod_lit1 e c
    | H : context [?e mod ?c] |- _ => divmod_lit1 e c
    | |- context [?e / ?c] => divmod_lit1 e c
    | H : context [?e / ?c] |- _ => divmod_lit1 e c
    end.
Ltac elim_divmod :=
  unfold M64v in *; eval_pows; divmod_lits; elim_shiftr; divmod_lits;
  Z.to_euclidean_division_equations.
Ltac elim_mod64 := elim_divmod.

Ltac split_conj_hyps :=
  repeat match goal with
    | H : _ /\ _ |- _ => let H1 := fresh "F" in destruct H as [H1 H]
    | H : True |- _ => clear H
    end.
Ltac elim_Zsigned :=
  repeat match goal with
    | |- context [Zsigned ?e] =>
        let x := fresh "sg" in pose proof (Zsigned_spec e); set (x := Zsigned e) in *; clearbody x
    | H : context [Zsigned ?e] |- _ =>
        let x := fresh "sg" in pose proof (Zsigned_spec e); set (x := Zsigned e) in *; clearbody x
    end.
Ltac zfacts1 :=
  name_words; unfold H63v in *; unfold zsext in *; elim_divmod; elim_Zsigned; split_ltb.

Ltac zv_interp e := lazymatch e with
  | SVar _ => idtac | SLit _ => idtac
  | SAlu ALU_ADD _ _ => idtac | SAlu ALU_SUB _ _ => idtac | SAlu ALU_SLTU _ _ => idtac
  | SAlu ALU_SLT _ _ => idtac | SAlu ALU_SRA _ (SLit _) => idtac
  | SAlu ALU_SLL _ (SLit _) => idtac | SAlu ALU_SRL _ (SLit _) => idtac | SAlu ALU_XOR _ (SLit _) => idtac | SAlu ALU_AND _ (SLit _) => idtac | SExt _ _ _ => idtac
  | SMd M_MUL _ _ => idtac | SMd M_MULH _ _ => idtac | SMd M_MULHU _ _ => idtac
  end.
Ltac zv_goal :=
  repeat match goal with
    | |- context [bv_unsigned (eval ?r ?e)] => zv_interp e; rewrite <- (zv_sound r e); cbn [zv ext_width_ok Z.of_N and_hmask]
    | H : context [bv_unsigned (eval ?r ?e)] |- _ => zv_interp e; rewrite <- (zv_sound r e) in H; cbn [zv ext_width_ok Z.of_N and_hmask] in H
    end.
Ltac zfacts :=
  repeat match goal with
    | H : Forall (holds ?r) _ |- _ => apply (Forall_zconj r) in H; cbn [zconj zp zv ext_width_ok Z.of_N and_hmask] in H
    | H : holds ?r ?p |- _ => apply (holds_zp r p) in H; cbn [zp zv ext_width_ok Z.of_N and_hmask] in H
    end;
  split_conj_hyps;
  lazymatch goal with
  | |- Forall (holds ?r) ?l => apply (zconj_Forall r l); cbn [zconj zp zv ext_width_ok Z.of_N and_hmask]
  | |- holds ?r ?p => apply (proj1 (zp_iff r p)); cbn [zp zv ext_width_ok Z.of_N and_hmask]
  | |- _ => idtac
  end;
  zv_goal; zfacts1; repeat split.

Ltac euclid_cleanup :=
  repeat match goal with
  | H : (Zpos ?c <> 0) -> _ |- _ => specialize (H ltac:(lia))
  | H : (0 < Zpos ?c) -> _ |- _ => specialize (H ltac:(lia))
  | H : (Zpos ?c < 0) -> _ |- _ => clear H
  | H : (Zpos ?c = 0) -> _ |- _ => clear H
  end.
Ltac zero_quotients :=
  repeat match goal with
  | H : ?x = Zpos ?c * ?q + ?r |- _ =>
      is_var q; assert (q = 0) by lia; subst q; rewrite Z.mul_0_r, Z.add_0_l in H
  end.
Ltac zsimp := euclid_cleanup; zero_quotients.

Lemma eexit_post_I0 : ltac2:(tb__ "0|0|
S32S4fA1S32S51A1S50OF_;F_;S0S9S32S52A1S32S43A1S52S59S43S46S54R1A1S45A2R2A3S9S11R7R6R1A3S4bRaS47RaR9S54R4A1R2A4S4dS22S55RbRaS4aS52S56S72S9S11RaR9R1A3Lr;A1R7A4S73R5R3A2R1A5S48RbRaR9R8R6R1A6A2Lw;A3F_;Frho;F_;FP;Fposts;Fcuts;Frho0;Fn;FK;Fsegs;").
Proof.
  intros segs K n rho0 cuts posts P Hin rho Hag w [Hsm Hk]. exists w. split; [apply wsteps_refl|].
  right. exists (mkLeaf (vn_state P) RsSymJump), rho. auto.
Qed.

Lemma holds_list_agree : ltac2:(tb__ "0|1|
S0S9S9S32SbA1S11R4R3R2A3S1eS33S5aSbS15R5A1R2A3S35A3S49SbSaR5A1M0R3A3S49SbG0R4A3F_;F_;F_;FF;Frho';Frho;Fn;").
Proof.
  intros n rho rho' F Hag Hb HF. induction HF as [|p t Hp Ht IH]; [constructor|].
  cbn in Hb. apply andb_prop in Hb as [Hb1 Hb2]. constructor; [|apply IH; exact Hb2].
  apply (proj1 (holds_agree n rho rho' p Hag Hb1)). exact Hp.
Qed.

Theorem call_sound_keep : ltac2:(tb__ "0|3|
S32S4fA1S4dOF_;S32S51A1S50OF_;F_;M0G0S13S13S57S32S18A1M1S32S43A1S4eS9S1eS36G1A1S6fR7R6R5A3S34G1R4A2A3S1eS33S70R8R7R6R5R4A5S35A3S1eS33S5aSbS15SeR9A1A1S12R9A1A3S35A3S9S4cRfReS47RfRdRaR1A4S48RfRcSeRaA1R1R7A5A4Frho1;S43S9S59S43R2R9A3S11SeReA1M2R8R2A3S4cR13R12S47R13R10S53S12RfA1S71RdG2S44R4A1SeRfA1RcA5A2R3A4RaA4F_;F_;Frho';FL;S4cR10RfS47R10ReRcR6A4R7A4F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FK';FK;Fok;Fsegs;").
Proof.
  intros segs ok K K' C Pre s R Posts Q rho He Hchk Hb Hsum Hcont.
  intros n HgQ w Hsp. pose proof (SP_facts segs K C rho w Hsp) as HF.
  revert w Hsp. apply (call_sound segs ok K K' C Pre s R Posts Q rho He Hchk Hsum); [|exact HgQ].
  intros L rho' HinL Hag. eapply triple_conseq; [| intros w' Hw'; exact Hw' | apply (Hcont L rho' HinL Hag)].
  intros w' [Hsm Hk]. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm| |].
  - eapply holds_list_agree; [exact Hag | exact Hb | exact HF].
  - apply forallb_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) Hb p Hp) as Hp'.
    eapply sprop_below_mono; [|exact Hp']. unfold import_post, import_next. cbn [ss_next set_objs subst_state].
    apply pos_add_nat_ge.
Qed.

Theorem call_complete_keep : ltac2:(tb__ "0|3|
S32S4fA1S32S51A1S50OF_;F_;M0G0S13S13S57S32S18A1M1S32S43A1S4dOF_;S9S1eS36G1A1S6fR7R6R5A3S34G1R4A2A3S1eS33S70R8R7R6R5R4A5S35A3S1eS33S5aSbS15SeR9A1A1S12R9A1A3S35A3S9S4bReS47ReRdRaR1A4S48ReRcSeRaA1R1R7A5A3Frho1;S43S9S59S43R2R9A3S11SeReA1M2R8R2A3S4bR12S47R12R10S53S12RfA1S71RdG2S44R4A1SeRfA1RcA5A2R3A4RaA3F_;F_;Frho';FL;S4bRfS47RfReRcR6A4R7A3F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC;FK';FK;Fsegs;").
Proof.
  intros segs K K' C Pre s R Posts Q rho He Hchk Hb Hsum Hcont.
  intros w Hsp. pose proof (SP_facts segs K C rho w Hsp) as HF.
  revert w Hsp. apply (call_complete segs K K' C Pre s R Posts Q rho He Hchk Hsum).
  intros L rho' HinL Hag. eapply etriple_conseq; [| intros w' Hw'; exact Hw' | apply (Hcont L rho' HinL Hag)].
  intros w' [Hsm Hk]. split; [|exact Hk]. apply smatch_add_facts; [exact Hsm| |].
  - eapply holds_list_agree; [exact Hag | exact Hb | exact HF].
  - apply forallb_forall. intros p Hp. pose proof (proj1 (forallb_forall _ _) Hb p Hp) as Hp'.
    eapply sprop_below_mono; [|exact Hp']. unfold import_post, import_next. cbn [ss_next set_objs subst_state].
    apply pos_add_nat_ge.
Qed.

Definition vTop : sv := SLit (2 ^ 64 - 1).

Tactic Notation "in_nth" integer(n) := do n right; left; reflexivity.

Example zfacts_selftest : forall rho,
  Forall (holds rho)
    [SPNot (SPBranch BC_EQ (SAlu ALU_ADD (SAlu ALU_ADD (SVar 15) (SVar 120)) (SLit 1)) (SAlu ALU_ADD (SVar 15) (SVar 17)));
     SPUlt (SVar 120) (SVar 17); SPUle (SVar 17) (SLit (2 ^ 40)); SPUle (SVar 15) (SLit (2 ^ 47))] ->
  Forall (holds rho)
    [SPUlt (SAlu ALU_ADD (SVar 120) (SLit 1)) (SVar 17);
     SPBranch BC_LTU (SAlu ALU_ADD (SVar 15) (SAlu ALU_ADD (SVar 120) (SLit 1))) (SAlu ALU_ADD (SVar 15) (SVar 17))].
Proof. intros rho HF. zfacts; lia. Qed.

Example zfacts_selftest_mulh : forall rho,
  Forall (holds rho)
    [SPBranch BC_NE (SMd M_MULH (SVar 123) (SLit 10)) (SAlu ALU_SRA (SMd M_MUL (SVar 123) (SLit 10)) (SLit 63));
     SPUle (SVar 123) (SLit 2147483647)] -> False.
Proof. intros rho HF. zfacts; lia. Qed.

Example zfacts_selftest_neg : forall rho,
  Forall (holds rho)
    [SPBranch BC_NE (SAlu ALU_SLT (SLit 0) (SVar 123)) (SAlu ALU_SLT (SAlu ALU_SUB (SLit 0) (SVar 123)) (SLit 0));
     SPUle (SVar 123) (SLit 2147483647)] -> False.
Proof. intros rho HF. zfacts; lia. Qed.

Example zfacts_selftest_meas : forall rho,
  Forall (holds rho) [SPUle (SVar 120) (SLit 5)] ->
  bv_unsigned (eval rho (SAlu ALU_ADD (SVar 120) (SLit 1))) <= bv_unsigned (eval rho (SLit 7)).
Proof. intros rho HF. zfacts; lia. Qed.

Example zfacts_selftest_idx : forall rho,
  Forall (holds rho) [SPUle (SVar 121) (SLit 4294967295)] ->
  holds rho (SPEq (SAlu ALU_SRL (SAlu ALU_SLL (SVar 121) (SLit 32)) (SLit 29)) (SAlu ALU_SLL (SVar 121) (SLit 3))).
Proof. intros rho HF. zfacts; lia. Qed.

Example zfacts_selftest_sext : forall rho,
  Forall (holds rho)
    [SPBranch BC_NE (SAlu ALU_SLT (SExt true 32 (SVar 150)) (SLit 0))
                    (SAlu ALU_SLT (SAlu ALU_ADD (SVar 33) (SExt true 32 (SVar 150))) (SVar 33));
     SPUle (SVar 33) (SLit 1099511627776)] -> False.
Proof. intros rho HF. zfacts; lia. Qed.
