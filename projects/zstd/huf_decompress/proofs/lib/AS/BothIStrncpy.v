(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (12 recorded proofs replaced by written proofs (length_strncpy_sealed_bytes, sealed8_nz, align15_4087 and 9 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SumsLib BSum2_code BothIMemset.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanIStrncpy () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib2AS7ZStores5zerosC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib2AS7ZStores<length_zerosC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:length_appI47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib2AS<BothIStrncpy7sealed8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib2AS<BothIStrncpyDstrncpy_sealed_bytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS7SumsLib2b_C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00C47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib2AS;BothIMemset7align15C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib2AS7StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega6VarMap1t03K59OSSVerify5KrLib2AS7SumsLib4cpyH01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib2AS7SumsLib4memkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib2AS<RefMemcpyLib:wbytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib6memk_nC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy2MZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy3HMCC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC59OSSVerify5KrLib2AS<RefMemcpyLib;store_ok_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib2AS<RefMemcpyLib4at_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib7code_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib2AS5Hoare6ret_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib5Lists4List2InC59OSSVerify5KrLib2AS5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib5msetkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions9bv_signedC46Stdlib9micromega;ZifyClasses7rew_iffC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib2AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib4wr_sC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC59OSSVerify5KrLib2AS8PropExec4c_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4btgtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_jal_x0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib=msetk_extend1C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib2AS5Hoare?regs_agree_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare>regs_agree_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib2AS8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare@regs_agree_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib:runs_transC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7MmapSim:step_sb_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_addiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib2AS<BothIStrncpy>asanreflect_fxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63944C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib2AS<BothIStrncpy>istrncpy_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_638fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63900C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63904C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63908C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_6390cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63910C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63914C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63918C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_6391cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63920C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63924C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63928C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_6392cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63930C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63934C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_6393cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_6394cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_6395cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63960C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63964C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7W_63968C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy=istrncpy_clobC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy6at8_nwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy6MK8_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63948C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib2AS:BSum2_code7D_6394cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib8v_add_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_add_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib6mc_lbuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy:sealed8_nzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib8sb_val_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib5mc_sbC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib2AS7SumsLib>asanreflect_fxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63904C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63908C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_6390cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63910C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63914C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63918C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_6391cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy9copy_iterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy5copy8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib2AS7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_lbuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7step_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_andiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib2AS;BothIMemset9u_align15C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_andi_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy<align15_4087C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;BothIMemset=align15_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare?regs_agree_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy9fill_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_638fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63900C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63924C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63928C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_6392cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63930C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63934C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_63938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:BSum2_code7D_6393cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy8MZ_finalC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relC35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1C59OSSVerify5KrImgGTgt_huf_decompress_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpyCasan_istrncpy_entryC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib2AS8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1c59OSSVerify5KrLib2AS<BothIStrncpy?asan_sealed_srcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpyCasan_sealed_src_imgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpy<istrncpy_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare4at_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS<BothIStrncpyBasan_istrncpy_codeC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition istrncpy_words : list (bv 32) :=
  [W_638fc; W_63900; W_63904; W_63908; W_6390c; W_63910; W_63914; W_63918;
   W_6391c; W_63920; W_63924; W_63928; W_6392c; W_63930; W_63934; W_63938;
   W_6393c; W_63940; W_63944; W_63948; W_6394c; W_63950; W_63954; W_63958;
   W_6395c; W_63960; W_63964; W_63968].

(* [comment removed for export] *)
Definition istrncpy_clob : list reg := [11; 12; 13; 14; 15].

(* [comment removed for export] *)
Definition sealed8 : list byte :=
  [Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e].
Definition strncpy_sealed_bytes : list byte := sealed8 ++ zeros 4087.

Lemma length_strncpy_sealed_bytes : length strncpy_sealed_bytes = 4095%nat.
Proof. unfold strncpy_sealed_bytes. rewrite length_app, length_zeros. reflexivity. Qed.

Lemma sealed8_nz : forall j, (0 <= j < 8)%Z -> bv_unsigned (b_ sealed8 j) <> 0%Z.
Proof.
  intros j Hj.
  assert (E : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%Z) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst j; cbv; discriminate.
Qed.

(* [comment removed for export] *)
Lemma align15_4087 : forall d : word, align15 4087 d <> 0%Z.
Proof.
  intros d H. unfold align15 in H. rewrite Z.land_lor_distr_l in H.
  apply Z.lor_eq_0_iff in H as [H _]. cbv in H. discriminate.
Qed.

Section ISTRNCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 istrncpy_words.
  (* [comment removed for export] *)
  Hypothesis Hsrc : rdn segs mem0 src 8%nat = Some sealed8.
  Hypothesis Hnul : rdn segs mem0 (at_ src 8) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis Hsnw : (bv_unsigned src + 9 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Hok : store_ok segs mem0 dst 4095%nat = true.
  Hypothesis Hnw : (bv_unsigned dst + 4095 < 2 ^ 64)%Z.
  Hypothesis Hdisj : (bv_unsigned dst + 4095 <= bv_unsigned src \/ bv_unsigned src + 9 <= bv_unsigned dst)%Z.

  #[local] Abbreviation CL := (fun r => In r istrncpy_clob).

  (* [comment removed for export] *)
  Ltac condv :=
    rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.

  (* [comment removed for export] *)
  Lemma HMC : cpyH segs mem0 dst src 8 sealed8.
  Proof.
    pose proof (u64_range dst). pose proof (u64_range src).
    apply CPYH.
    - lia.
    - reflexivity.
    - exact Hsrc.
    - cbn [length]. eapply (store_ok_sub segs mem0 dst dst 4095%nat 8%nat); [lia | exact Hok | lia | cbn; lia].
    - lia.
    - lia.
    - lia.
  Qed.

  #[local] Abbreviation MK := (memk mem0 dst sealed8).
  (* [comment removed for export] *)
  Definition MZ (k : Z) : word -> option byte := msetk (MK 8) (at_ dst 8) (Z_to_bv 8 0) k.

  Lemma MZ_0 : MZ 0 = MK 8.
  Proof. reflexivity. Qed.

  Lemma MZ_final : MZ 4087 = wbytes mem0 dst strncpy_sealed_bytes.
  Proof.
    unfold MZ, msetk, strncpy_sealed_bytes, zeros. rewrite (memk_n _ _ _ _ _ _ HMC).
    rewrite wbytes_app. reflexivity.
  Qed.

  Lemma MK8_ok : store_ok segs (MK 8) (at_ dst 8) (Z.to_nat 4087) = true.
  Proof.
    unfold memk. pose proof (u64_range dst).
    apply (store_ok_at segs mem0 dst 4095%nat); [lia | exact Hok | lia | cbn; lia].
  Qed.

  Lemma at8_nw : (bv_unsigned (at_ dst 8) + 4087 < 2 ^ 64)%Z.
  Proof. pose proof (u64_range dst). rewrite at_u by lia. lia. Qed.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at istrncpy_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60
                    & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HMC) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (memk _ _ _ ?a) _) _ =>
                     first [constr_eq a kk | replace (memk mem0 dst sealed8 a) with (memk mem0 dst sealed8 kk) by (f_equal; lia)] end.
  Ltac msb F D kk :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HMC) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia
        | gres; rwH; reflexivity | apply sb_val_b | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac mz_at kk := match goal with |- msteps _ (mkst _ _ (MZ ?a) _) _ =>
                     first [constr_eq a kk | replace (MZ a) with (MZ kk) by (f_equal; lia)] end.
  Ltac mzsb F D kk :=
    mz_at kk; unfold MZ;
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ (at_ dst 8) kk) (v := Z_to_bv 64 0) (b := Z_to_bv 8 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi, ?at_at; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | reflexivity
        | apply (wr_s segs (MK 8) (at_ dst 8) 4087 (Z_to_bv 8 0) ltac:(lia) at8_nw MK8_ok); cbn; lia ]
      | step_simpl];
    rewrite (msetk_extend1 (MK 8) (at_ dst 8) (Z_to_bv 8 0) kk) by lia; fold (MZ (kk + 1)); vn.

  (* [comment removed for export] *)
  Lemma fill_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ dst (8 + k) -> getr regs 12 = at_ dst 4095 ->
    (0 <= k)%Z -> (8 + k < 4095)%Z -> (Z.of_nat i = 4095 - 8 - k - 1)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 68) (MZ k) rom) (mkst regs' ret (MZ 4087) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H12 Hk Hkn Hi.
    - eexists. split.
      + mzsb C68 D_63940 k.                                (* [comment removed for export] *)
        an C72 D_63944.                                    (* [comment removed for export] *)
        ab_ft C76 D_63948 ltac:(condz).                    (* [comment removed for export] *)
        an C80 D_6394c.                                    (* [comment removed for export] *)
        aret C108 D_63968 ret.
        mz_at 4087%Z. apply mst_refl.
      + unfold istrncpy_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + (k + 1)) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
      + eexists. split.
        * mzsb C68 D_63940 k.
          an C72 D_63944.
          ab_tk C76 D_63948 ltac:(condz).                  (* [comment removed for export] *)
          mz_at (k + 1)%Z. apply mst_refl.
        * post. unfold istrncpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Lemma copy_iter : forall regs (j : Z),
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 4095 ->
    getr regs 13 = Z_to_bv 64 j -> (0 <= j < 8)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 8) (MK j) rom) (mkst regs' (at_ base 8) (MK (j + 1)) rom)
      /\ getr regs' 10 = dst /\ getr regs' 11 = src /\ getr regs' 12 = Z_to_bv 64 4095
      /\ getr regs' 13 = Z_to_bv 64 (j + 1) /\ regs_agree CL regs regs'.
  Proof.
    get_code. intros regs j H10 H11 H12 H13 Hj. pose proof (u64_range dst). pose proof (u64_range src).
    eexists. split.
    - av C8 D_63904 (at_ src j) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
      mlbu C12 D_63908 j.                                              (* [comment removed for export] *)
      ab_ft C16 D_6390c
        ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; pose proof (u8_range (b_ sealed8 j));
              rewrite (u_Z2bv (bv_unsigned (b_ sealed8 j))) by lia; rewrite (u_Z2bv 0) by lia;
              apply sealed8_nz; lia).                                  (* [comment removed for export] *)
      av C20 D_63910 (at_ dst j) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
      an C24 D_63914.                                                  (* [comment removed for export] *)
      msb C28 D_63918 j.                                               (* [comment removed for export] *)
      ab_tk C32 D_6391c ltac:(condv).                                  (* [comment removed for export] *)
      mk_at (j + 1)%Z. apply mst_refl.
    - post; try (unfold istrncpy_clob; solve_regs_agree). unfold v_addi. unorm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma copy8 : forall regs0 rr,
    regs_agree CL regs0 rr ->
    getr rr 10 = dst -> getr rr 11 = src -> getr rr 12 = Z_to_bv 64 4095 ->
    getr rr 13 = Z_to_bv 64 0 ->
    exists regs',
      msteps segs (mkst rr (at_ base 8) (MK 0) rom) (mkst regs' (at_ base 8) (MK 8) rom)
      /\ getr regs' 10 = dst /\ getr regs' 11 = src /\ getr regs' 12 = Z_to_bv 64 4095
      /\ getr regs' 13 = Z_to_bv 64 8 /\ regs_agree CL regs0 regs'.
  Proof.
    intros regs0 rr K A B C D.
    Ltac cp_iter :=
      match goal with
      | K : regs_agree _ ?regs0 ?rr, A : getr ?rr 10 = _, B : getr ?rr 11 = _, C : getr ?rr 12 = _, D : getr ?rr 13 = Z_to_bv 64 ?v |- _ =>
        let jj := eval vm_compute in v in
        let jj1 := eval vm_compute in (v + 1)%Z in
        change (Z_to_bv 64 v) with (Z_to_bv 64 jj) in D;
        try change (memk mem0 dst sealed8 v) with (memk mem0 dst sealed8 jj);
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK jj1) rom)
                 (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                           /\ getr r 13 = Z_to_bv 64 jj1 /\ regs_agree CL regs0 r));
        [ destruct (copy_iter rr jj A B C D ltac:(lia)) as (r' & RUN & B10 & B11 & B12 & B13 & K');
          exists r'; split; [exact RUN | repeat split; try assumption; eapply regs_agree_trans; [exact K | exact K']]
        | cbv beta; clear rr K A B C D; intros rr (A & B & C & D & K) ]
      end.
    do 8 cp_iter.
    exists rr. split; [apply mst_refl | repeat split; assumption].
  Qed.

  Theorem istrncpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 4095 ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom)
                  (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs.
    rewrite <- MZ_final.
    change (mkst regs (at_ base 0) mem0 rom) with (mkst regs (at_ base 0) (MK 0) rom).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 0) rom)
             (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                       /\ getr r 13 = Z_to_bv 64 0 /\ regs_agree CL regs r)).
    { eexists. split.
      - ab_ft C0 D_638fc ltac:(condz).                                  (* [comment removed for export] *)
        an C4 D_63900.                                                   (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold istrncpy_clob. solve_regs_agree. }
    cbv beta. intros r0 (A10 & A11 & A12 & A13 & K0).
    (* [comment removed for export] *)
    destruct (copy8 regs r0 K0 A10 A11 A12 A13) as (r8 & RUN8 & L10 & L11 & L12 & L13 & K8).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 8) rom)
             (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                       /\ getr r 13 = Z_to_bv 64 8 /\ regs_agree CL regs r)).
    { exists r8. split; [exact RUN8 | repeat split; assumption]. }
    cbv beta. clear r8 RUN8 L10 L11 L12 L13 K8. intros r8 (L10 & L11 & L12 & L13 & K8).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ 0) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + 0) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
    { eexists. split.
      - av C8 D_63904 (at_ src 8) ltac:(apply v_add_at; lia).         (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lbu with (b := Z_to_bv 8 0);
            [exact C12 | reflexivity | exact D_63908
            | gres; rwH; imm_norm; rewrite at_addi; replace (at_ src (8 + 0)) with (at_ src 8) by (f_equal; lia);
              unfold memk; change (firstn (Z.to_nat 8) sealed8) with sealed8;
              rewrite rdn_wbytes_out;
              [ exact Hnul
              | change (length sealed8) with 8%nat; rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | change (length sealed8) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ]
          | step_simpl]; vn.                                             (* [comment removed for export] *)
        ab_tk C16 D_6390c ltac:(condz).                                (* [comment removed for export] *)
        change (memk mem0 dst sealed8 8) with (MZ 0).
        av C40 D_63924 (at_ dst 8) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
        an C44 D_63928.                                                  (* [comment removed for export] *)
        (* [comment removed for export] *)
        an C48 D_6392c.
        av C52 D_63930 (Z_to_bv 64 (align15 4087 (at_ dst 8)))
           ltac:(rewrite <- (u_align15 4087 (at_ dst 8)) by lia; symmetry; apply Z_to_bv_bv_unsigned).
        pose proof (align15_4087 (at_ dst 8)) as HA. pose proof (align15_range 4087 (at_ dst 8) ltac:(lia)) as HAR.
        ab_ft C56 D_63934 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; rewrite !u_Z2bv by lia; exact HA).
        ab_ft C60 D_63938 ltac:(condz).                                 (* [comment removed for export] *)
        av C64 D_6393c (at_ dst 4095) ltac:(apply v_add_at; lia).       (* [comment removed for export] *)
        apply mst_refl.
      - post.
        + rewrite <- H1. apply K8. unfold istrncpy_clob. cbn. intros [X|[X|[X|[X|[X|[]]]]]]; discriminate.
        + unfold istrncpy_clob in *. ra_chain. }
    cbv beta. intros r9 (M1 & M11 & M12 & K9).
    destruct (fill_loop (Z.to_nat 4086) r9 ret 0 Hret M1 M11 M12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r10 & RUN & K10).
    exists r10. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End ISTRNCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.zstd.huf_decompress.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_istrncpy_entry : word := 0x63890.
Definition asan_sealed_src : Z := 0x1182b.  (* [comment removed for export] *)

Lemma asan_istrncpy_code :
  code_at AsanUbsan.M.loaded_segments asan_istrncpy_entry 0 istrncpy_words.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanIStrncpy ()) [] "p%0p;1p;2p;3p;6p;4g0000j19Tg000Uj1JTg0013j1BTg00amj1?Tg00d9j2=Tg01ULj21Tg003aj30j1>Tg00:Sj1@Tg00Y:j26Tg00GPj27Tg02kHj1ITg02l0j2HTg02lMj62Tg004;j2FTg00;1j1CTg00mUj4:Tg01TJj2;Tg02lej2ATg02mCj3DTg01NQj4ETg015Jj3<Tg02mkR0f0R1';p=Gg02o:R2/=1,;0p=5g00P:R3f1R4/A1g00PZR530p=4f5f4R6f3R7f2R8;D4P1CEp=3A<8419<67p=8g007J#9#9R7#9#9#9#JR6#BR8#?R4g00JBR1,=2#GR9g01amS00,18R:30R;%@7R7,61R<#5R=g01bgS01,18R>504R?16<7R<#5R@g01caS02,18RA504RB16<7R<#5RCg01d[S03,18RD504RE16<7R<#5RFg01eUS04,18RG504RH16<7R<#5RIg01fOS05,18RJ504RK16<7R<#5RLg01gIS06,18RM504RN16<7R<#5S07g01hCS08,18RO504RP16<7R<#5S09g01i=S0:,18RQ504RR16<7R<#5S0;g01j7S0<,18RS504RT16<7R<#5S0=g01k1S0>,18S0?504RU16<7R<#5S0@g01kkS0A,18S0B504RV16<7R<#5S0Cg01leS0D,18S0E504RW16<7R<#5S0Fg01m_S0G,18S0H504RX16<7R<#5S0Ig01nYS0J,18S0K504RY16<7R<#5S0Lg01oSS0M,18S0N504RZ16<7R<#5S0Og020MS0P,18S0Q504R[16<7R<#5S0Rg01[RS0S,18S0T504R\16<7R<#5S0Ug01]FS0V,18S0W504R]16<7R<#5S0Xg021GS0Y,18S0Z504R^16<7R<#5S0[g022AS0\,18S0]504R_16<7R<#5S0^g023;S0_,18S0`504R`16<7R<#5S0ag0245S0b,18S0c504Ra16<7R<#5S0dg024oS0e,18S0f504Rb16<7R<#5S0gg025iS0h,18S0i504Rc16<7R<#5S0jg026cS0k,18S0l504Rd16<7R<#5S0mg027]S0n,18S0o504Re16<7#5S0pg028WS0q,18S0r504R<g00QWS0s'7S0t'7R7'7Rf'7Rg'7Rh'7Ri'7Rj'7Rk'7Rl'7Rm'7Rn'7Ro'7Rp'7Rq'7Rr'7Rs'7Rt'7Ru'7Rv'7Rw'7Rx'7Ry'7Rz'7R{'7R|'7R}'7P;P4P4%>4R~%I6,H8R6P9P:E2R:1F35R514;:dP?P}P?P4P4P~P6P=P>E2R>P514?>dPBP|PBP4P4P~P6P@PAE2RAP514BAdPEP{PEP4P4P~P6PCPDE2RDP514EDdPHPzPHP4P4P~P6PFPGE2RGP514HGdPKPyPKP4P4P~P6PIPJE2RJP514KJdPNPxPNP4P4P~P6PLPME2RMP514NMdPPPwPPP4P4P~P6Q07POE2ROP514POdPRPvPRP4P4P~P6Q09PQE2RQP514RQdPTPuPTP4P4P~P6Q0;PSE2RSP514TSdPUPtPUP4P4P~P6Q0=Q0?E2RtP514UtdPVPsPVP4P4P~P6Q0@Q0BE2RsP514VsdPWPrPWP4P4P~P6Q0CQ0EE2RrP514WrdPXPqPXP4P4P~P6Q0FQ0HE2RqP514XqdPYPpPYP4P4P~P6Q0IQ0KE2RpP514YpdPZPoPZP4P4P~P6Q0LQ0NE2RoP514ZodP[PnP[P4P4P~P6Q0OQ0QE2RnP514[ndP\PmP\P4P4P~P6Q0RQ0TE2RmP514\mdP]PlP]P4P4P~P6Q0UQ0WE2RlP514]ldP^PkP^P4P4P~P6Q0XQ0ZE2RkP514^kdP_PjP_P4P4P~P6Q0[Q0]E2RjP514_jdP`PiP`P4P4P~P6Q0^Q0`E2RiP514`idPaPhPaP4P4P~P6Q0aQ0cE2RhP514ahdPbPgPbP4P4P~P6Q0dQ0fE2RgP514bgdPcPfPcP4P4P~P6Q0gQ0iE2RfP514cfdPdP7PdP4P4P~P6Q0jQ0lE2R7P514d7dPeQ0tPeP4P4P~P6Q0mQ0oE2R7P514e7dP<Q0sP<P4P4P~P6Q0pQ0rE2R6P514<6dg00MdE3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3E3P0P2P1P8Q00P8Q01P8Q02P8Q03P8Q04P8Q05P8Q06P8Q08P8Q0:P8Q0<P8Q0>P8Q0AP8Q0DP8Q0GP8Q0JP8Q0MP8Q0PP8Q0SP8Q0VP8Q0YP8Q0\P8Q0_P8Q0bP8Q0eP8Q0hP8Q0kP8Q0nP8Q0q%C8D8D8D8D8D8D8D8D8D8D8D8D8D8D8C:eP0P2P1g01`jC:eo"). Qed.

(* [comment removed for export] *)
Lemma asan_sealed_src_img : forall mem,
  (forall i, (asan_sealed_src <= i < asan_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
  rdn AsanUbsan.M.loaded_segments mem (Z_to_bv 64 asan_sealed_src) 8 = Some sealed8
  /\ rdn AsanUbsan.M.loaded_segments mem (at_ (Z_to_bv 64 asan_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof.
ltac2:(KReplay.run1 (kr_t_AsanIStrncpy ()) [] "h02Hxh11xh27__arithh34__ffh48__varmaph55__with61zh76__sat0h86__sat1h94__x1h:2Hah;3Hx0h<1oh=1yh>5Hnoneh?1ih@1mhA3memhB1np;1p;2p;3p;4p;6p;7p;<p;Bp;8g0000j12Tg000Uj1YTg0013j1TTg00amj1cTg00@Oj10Tg00:Sj15Tg00Y:R0j21Tg00DSj2GTg00?mj1STg003aj33Tg00;Qj1OTg0026j1;Tg01ULj2JTg00d9j2`Tg00;1j1^Tg015Jj38Tg004;j2BTg00XZR1j1NTg00V3j2pTg00D7R2j24Tg00YWj1bTg00Z5j4kTg00VPj2iTg00G4R3j26Tg00W8j3hTg00W\j1gTg00<Oj1fTg00<mj1eTg00=Xj2?Tg00ZXj3KTg00[;j3dTg00AXj2}Tg00B:j2|Tg00Bfj3{Tg00CEj4zTg00[^j4aTg00FJj2>Tg01Aej3xTg00GPj2ETg030Bj3RTg030hj6]Tg017Xj4PTg00<1j2wTg00>;j2vTg005Qj7[j6LTg02[=j2uTg00Ifj6XTg031Qj7ZTg00l\j4rTg01NQj4oTg02SNj4nTg032Ij2qTg016Mj3mTg00_Yl<sTg00`>lBtTg00`dl<_Tg00>^j4QTg00Gkj7lTg00?Ij7jTg00A4j8yTf0R4#2#2p==f3R5f2R6'4f1R7/64'Ep=9g02mkR8P6P7P4Cnp=D1q749m56p=<g00L_R9/B4p=:g006kR:P9P9P9P1P1f5R1f4R;P5P6P7P4M<sp=WP9P9P9P9P9P9P0P4P7P6P0P5P;P1f6R0f7R<f8f9MBtp=IP9P9P2P<P2P0P1P;P5P6P7P4M<_p=Vg00JBR2/44p=@P9P7g00NlP4CQp=AP7g00J`R=g00K?R>P>g00K_R?P4g00L?Flp=7P9P7g00OSP4CQp=FP9P;P5P6P7P4ELp=C1674,E6p=HP9P9P3P<P3P0P1P;P5P6P7P4M<_p=UP6P=P>P>P?P7P4Fjp=MP5P=P>P>P?P6P7P4Gyp=\g007JR=#2R1#2R0#2R3#2#=R<#YR@#TRA%Y3RB#TRC#cRD]1g033<REP4P4%00#5R0,1EC9P61G@7O1%SCRF53D[^?9%OCRG#cRH%03#0#2#=#=#0#2#0#2#0#0#5RI,G@RJg008k#;RK#;#;#;#;#;#;#;RL5D7RMg007o,JGRN33%53R3,`JRO=D7KRP1GB2%^CRQ58C,JGRR53HPHPFX1ARS?DJLRTA3H4NX<HPB%0=RU#0RV#0RW#=#5RXPBPXC<PB%=V#0#0#5RVPBPVC<PB%2URU#2RV#0#2RX#0#5RYPBPYC<RYPB%=V#0#5RVPBPVC<PB%0U#0#=#5RUPBPUC<PB%2X#5RXPBPXC<PB%0W#2#5RWPBPWC<=8CQ58C98CY58C58C58C58C58C,JG,BHA3HTNdPMP8PLP7PSPJPI%NLRM,14RT%51R1%5<R<'pRY'4X6911IMRW/4YRX11I3RU/4YRVP4X19RZ1474#bX=9X19R[PWPUPZPZPZP9P9g00aI1174Ck#:X@9XB9R\PIPI%:IR]PMP3PZPZ%N4#:X1:R:PLP3%:3EWR^M:IPYPY%:YR_GV1i1<R`1621%@<162Y[[Ra%@1Rbg00QWRcAh1<7UW:R<%@Y\c^:bRbg00N@Rc#^Rd%OcRc%g9Re%f9Rf%e9Rg1?9IRh1?935K9Ri1?91=d9@R1'A'71}g?R?P4P6g00P:Rjg00PZRk'B1|46=3jkdA{927CzRkb3b4b5PVP4b2b7b8CaPXe1>@JRXPdPcPePf1?92RV/Ah,7gP?Pkb3b4b5%@IP4b2P`PaP<PbPdPcPePf1Fh1,7gP?Pkb3b4b516IYP4b2b7b85xIRjDCPX1>@4RlPl11XMC9PA1>@7Rm,G@RnP;P4O1=3DFX1ARFP6PmP9PI1>@6RD,44Ro?HDTPI1>@5R5P511I0R5C9RT]0X69PIPmPmPWC9Rp14IDRq16DWRr'EAHqDURsPqPrPqPZP3O1Rr,1IRt,6Dp-0Ru/BqA3uqqe9RqqPZ1674#bX=9X19RvPDPD%:DRwPWPtPZPZPZP\PIPIP]PMPrP^M:IGUE]P4CPPsPdPc1w97RsPfPg1v9=R^,Ah,7gRr1F^i,7g5Mg%S>R>1?909K9h,F^,7g9MgrRrC\P?Pkb3b4b5X99PIP4P4PUC9PIP7P7P5C9Rh[^99P41>@;P7O2R;b2b;W0AHqD5Rq^0pePXPjP4F[O2P71u@7RpEXW0X1AFZELPHADSOKR5A3H4RX<HPBP2PBP2C<=8CQ,JG,BHA3H5RdPPP8PKP7PSPO11X3RS%NKR8,14RP/4YX69PI1143R5/18RG/4YX6911U8RQ/4YRC%5=R=,1UR2/4YRBPZP[PQP2PZPZPZP\PUPU%:UR[P8P=PZPZP:PKP=%:=EWR:M:IPYPYP_GVP`PaP<PbPdPcPePf1?9=9K9iR_/A1,7gP?Pkb3b4b5PBP4b2b7b8CaPCePXPjDC1>@OROPJP3PI%@5X69PdPcPePf1AVi,7gP?Pkb3b4b5%@UP4b2PXPjDCPI165YX69P`PaP<PbPdPcPePf1Fi1,7gP?Pkb3b4b516UYP4b2b7b8PXPjDCCrRYDCPOPlPl11O8C9PAPnPFP6PmP9PSAHoDPPT]0X69PIP5PDPDPGC9PT]0X69PUPmPmPQC9Rm14UDRT16DQRG'EAHTD2R5PTPGPTPZP=O1R=,1URG,6D1BuTA3uTTe9RTTPZPvPDPDPwPQPGPZPZPZP\PUPUP[A39UUeP8P=P:M:IGUE]P4CPP5PdPcPsPfPg1Ai^,7g1F^_,7g5MgP>PrC\P?Pkb3b4b5X99PUP4P4P2C9Ph[^99P;b2b;W0Pq^0mePXPjDCPOPYP4F[O2P7PpEXW0X1AFZELCo1G@ERE=D7L=3HN1`E3=D7K=3HR'EeW>WAo"). Qed.

Theorem asan_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
  (forall i, (asan_sealed_src <= i < asan_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
  store_ok AsanUbsan.M.loaded_segments mem0 dst 4095%nat = true ->
  (bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
  (bv_unsigned dst + 4095 <= asan_sealed_src \/ asan_sealed_src + 9 <= bv_unsigned dst)%Z ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 asan_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs asan_istrncpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
    /\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanIStrncpy ()) [] "h07__arithh14__ffh27__sat13h37__sat14h48__varmaph55__with62Hah75regs'h82H1h93H10h:3H11h;3H12h<5Hdisjh=2Hnh>5Hnoneh?3Hnwh@3HokhA4HrethB2HshC1ahD1bhE3dsthF1ihG4mem0hH1rhI4regshJ3rethK3romhL1xhM1zp;1p;2p;3p;4p;5p;6p;Dp;7g0000j12Tg000Uj1FTg0013j1DTg00amj1HTg00@Oj16Tg00nLj2_Tg00D7j28Tg00:Sj14Tg00Y:j29Tg00G4j25Tg00GPR0j2ATg00DSj2;Tg00?mj1RTg003aj33Tg0026j11Tg00]Ej4[Tg00FJj2BTg00V3j2XTg00I3j2WTg00o8j1VTg015jj2>Tg016Mj3<Tg00olj2=Tg034@j2UTg00;Qj1MTg01ULj2JTg00d9j2ITg00;1j1NTg015Jj3STg01Unj5@Tg00cCj3GTg01;>j3KTg011>j3TTg011Uj3LTg012Mj2QTg00VPj2nTg00W8j3mTg00W\j1lTg00<Oj1kTg00<mj1jTg00=Xj2?Tg00ZXj3fTg00[;j3eTg00>^j4ETg00AXj2^Tg004;j2`Tg00B:j2aTg00Bfj3bTg00CEj4\Tg01Aej3cTg005Qj6dTg035HlDZTg036Ij1gTg00Ifj6hTg02SNj4YTg00Gkj7iTf0R1#1#1p=P%11#1#1#1p=O%11#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=]%11#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0%61#6p=7g02mkR2f2R3f1R4P1CYp=:P4g00J`g00K?R5P5g00K_R5P1g00L?Fip=Cg007JR6#2R7#2R8#2R9#2#2#2R:#FR;#DR<%F9R=#DR>#HR?]LP?\<%67R@#FRA/_<RBg00L_RCg033<RD/81%68#4R8,9DRE,51'Af6RF1;;4O1%R>53?[]Fg00P:R?P2f5RGf4RHg008k#1RI#1#P#ORJ#1#P#O#]#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0C[g00PZRK331B;G%66RL#7#7#7#7#7#4RM'9%47R7%4:R:'XRN'51B;FRO/9M/8D18EO'W%VH%46R6g00MdRH1>A6d5<A,=F=3<Gf7R6%2@#4ROPH1>AOd5<A'=f9RO53<f8RE%6@#4R@PH1>A@d5<A'=1;;DRD53<%2L#2#4RLPH1>ALd5<A,=O1;;M53<f=RM/UE%M>RL#HRHA:MDJg007o,JLR@33%49,IDRP=:MIg00JBRQ,;=%N>5S>,JLRL53H'AP0f>R0?:DJ=3H@A:0PI=3HLg01ZOR>PMg02o:R=f@RRP0D@P>P1f<RSf?RTg009JRU5GRP0D@5K2%DARAg029Q9TA1WHRA?LM1'AX7B,QBP1A:RDJ=3H@fAR@?:PI=3HLP<1I=QP>P@P4fDRLfBRHD@P>P1PRfC=GLUPHD@5K2ALA@1'AX7B,QBXD<P2P=PHP@PDPRg037;P4P1PC%79#2#2#2#2#2#6#2#6#2#7#4R91918/5NXMC1n7:RR15Q718Q:15QN[[R@18Q7RHg00QWR2Am7:4UW6R:18QN\2^6HRHg00N@R2#NRB%M2R2%lCRA%kCRL%jCRUPC1?C9R>1?C85fCg00OSRP1?C7=eC;R7CE'C1^U5R5P1P31`?K1a13=3?KdAbCQ4C\RKb1b4b51998/5NP1b0b2b31;;9,B;PRP@P:PHPBP2PAPLPC1?CQg00NlP>CE,CUP5PKb1b4b518Q9P1b0b2b3PRP@P:PHPBP2PAPLPCP>PPP7CE,CUP5PKb1b4b5159NP1b0b2b35c9Ed1B;D/98/5NePSf;f:PTP0POPEP6PFPGMDZP=%g=EhW=WBP4P1O2n2001000000121000000bCW;W:W9W8WAW<W?W@W>XJ<WIWKXE<WGo"). Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
