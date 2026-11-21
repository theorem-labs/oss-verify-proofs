(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (land15_range, align15_range, u_align15 and 5 more)). *)
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
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import SumsLib Sums_code.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanIMemset () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02c59OSSVerify5KrLib2AS;AsanIMemset<land15_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanIMemset7align15C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init5Logic4True00C59OSSVerify5KrLib2AS8PropExec;Z_lor_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7bv_wrapK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4v_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_andiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@land_lor_distr_lC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z<lor_eq_0_iffC59OSSVerify5KrLib2AS7SumsLib:rep8_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib7code_atC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib2AS5Hoare6ret_okC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subc59OSSVerify5KrLib2AS;AsanIMemset6cbyte_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib5msetkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib2AS5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC45stdpp9bitvector;definitions9bv_signedC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib2AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib2AS7SumsLib4wr_sC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC59OSSVerify5KrLib2AS8PropExec4c_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4btgtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_jal_x0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib=msetk_extend1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib2AS5Hoare?regs_agree_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare>regs_agree_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib2AS8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare@regs_agree_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<RefMemcpyLib:runs_transC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib2AS7MmapSim:step_sb_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_addiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib2AS;AsanIMemset>asanreflect_fxC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib2AS9Sums_code7W_634e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_634e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_634ecC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib2AS;AsanIMemset=imemset_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_634fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63500C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63504C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63508C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_6350cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63510C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63514C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63518C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_6351cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63520C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63524C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_63528C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7W_6352cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanIMemset<imemset_clobC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2AS9Sums_code7D_634f0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib2AS9Sums_code7D_634f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_6352cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanIMemset5cpat_C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib2AS8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib2AS8PropExec<step_bltu_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib<msetk_extendC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanIMemset:cpat_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_ltK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib2AS8PropExec<step_bltu_tkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib2AS7SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_6351cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63520C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63524C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63528C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib2AS;AsanIMemset=align15_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7step_orC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib2AS;AsanIMemset9u_align15C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_andi_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib2AS7SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanIMemset;align15_n16C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib2AS8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib8v_add_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_add_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib:v_slli_mulC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec<step_slli_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib8v_or_shlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib:step_or_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare4at_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare?regs_agree_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specc59OSSVerify5KrLib2AS;AsanIMemset7al_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanIMemset7bl_loopC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib2AS9Sums_code7D_634d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SumsLib>asanreflect_fxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib2AS9Sums_code7D_634d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_634d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_634f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_634fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63500C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63504C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63508C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_6350cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63510C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63514C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_63518C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_634dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_634e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Sums_code7D_634e4C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relC35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1C59OSSVerify5KrImgGTgt_huf_decompress_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanIMemsetBasan_imemset_entryC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc59OSSVerify5KrLib2AS;AsanIMemset;imemset_runC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS;AsanIMemsetAasan_imemset_codeC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition imemset_words : list (bv 32) :=
  [W_634d0; W_634d4; W_634d8; W_634dc; W_634e0; W_634e4; W_634e8; W_634ec;
   W_634f0; W_634f4; W_634f8; W_634fc; W_63500; W_63504; W_63508; W_6350c;
   W_63510; W_63514; W_63518; W_6351c; W_63520; W_63524; W_63528; W_6352c].

(* [comment removed for export] *)
Definition imemset_clob : list reg := [11; 12; 13].

(* [comment removed for export] *)
Definition align15 (n : Z) (s : word) : Z := Z.land (Z.lor n (bv_unsigned s)) 15.

Lemma land15_range : forall x, (0 <= x)%Z -> (0 <= Z.land x 15 < 16)%Z.
Proof.
  intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma align15_range : forall n s, (0 <= n)%Z -> (0 <= align15 n s < 16)%Z.
Proof.
  intros n s Hn. unfold align15. apply land15_range. apply Z.lor_nonneg. pose proof (u64_range s). lia.
Qed.

Lemma u_align15 : forall n (s : word), (0 <= n < 2 ^ 64)%Z ->
  bv_unsigned (v_andi (v_or (Z_to_bv 64 n) s) 15) = align15 n s.
Proof.
  intros n s Hn. pose proof (u64_range s) as Hs.
  pose proof (Z_lor_range n (bv_unsigned s) Hn Hs) as Hl.
  unfold v_andi, v_or, align15. rewrite (u_Z2bv n) by lia.
  rewrite (u_Z2bv (Z.lor n (bv_unsigned s))) by lia.
  change (bv_wrap 64 15) with 15%Z.
  pose proof (land15_range (Z.lor n (bv_unsigned s)) ltac:(lia)).
  apply u_Z2bv; lia.
Qed.

Lemma align15_n16 : forall n s, (0 <= n)%Z -> align15 n s = 0%Z -> (n mod 16 = 0)%Z.
Proof.
  intros n s Hn H. unfold align15 in H. pose proof (u64_range s).
  rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
  change 15%Z with (Z.ones 4) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Definition cbyte_ (c : word) : byte := Z_to_bv 8 (bv_unsigned c).
Definition cpat_ (c : word) : word := Z_to_bv 64 (bv_unsigned c * M8).

Lemma cpat_bytes : forall c : word, (bv_unsigned c < 256)%Z ->
  word_to_le_bytes 8 (cpat_ c) = repeat (cbyte_ c) 8.
Proof. intros c Hc. pose proof (u64_range c). apply rep8_bytes. lia. Qed.

Section IMEMSET.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables s c : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 imemset_words.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.
  (* [comment removed for export] *)
  Hypothesis HC256 : align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z.

  #[local] Abbreviation cbyte := (cbyte_ c).
  #[local] Abbreviation cpat := (cpat_ c).
  #[local] Abbreviation MS := (msetk mem0 s (cbyte_ c)).
  #[local] Abbreviation CL := (fun r => In r imemset_clob).

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemset_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & _).

  (* [comment removed for export] *)
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ s kk) (v := c) (b := cbyte);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
      | step_simpl];
    rewrite (msetk_extend1 mem0 s cbyte kk) by lia; vn.

  (* [comment removed for export] *)
  Ltac msd F D kk :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ s kk) (v := cpat);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
      | step_simpl];
    rewrite (cpat_bytes c) by lia;
    rewrite (msetk_extend mem0 s cbyte kk 8) by lia; change (Z.of_nat 8) with 8%Z; zlit_at; vn.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bl_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = c -> getr regs 13 = at_ s k -> getr regs 12 = at_ s n ->
    (0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 24) (MS k) rom) (mkst regs' ret (MS n) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - eexists. split.
      + msb C24 D_634e8 k.                        (* [comment removed for export] *)
        an C28 D_634ec.                           (* [comment removed for export] *)
        ab_ft C32 D_634f0 ltac:(condz).           (* [comment removed for export] *)
        an C36 D_634f4.                           (* [comment removed for export] *)
        aret C92 D_6352c ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemset_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s (k + 1)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + eexists. split.
        * msb C24 D_634e8 k.
          an C28 D_634ec.
          ab_tk C32 D_634f0 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold imemset_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = cpat -> getr regs 13 = at_ s k -> getr regs 12 = at_ s n ->
    (0 <= k)%Z -> (k + 16 <= n)%Z -> (Z.of_nat i * 16 = n - k - 16)%Z ->
    (bv_unsigned c < 256)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 76) (MS k) rom) (mkst regs' ret (MS n) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hk16 Hi Hc256.
    - eexists. split.
      + msd C76 D_6351c k.                        (* [comment removed for export] *)
        msd C80 D_63520 (k + 8)%Z.                (* [comment removed for export] *)
        an C84 D_63524.                           (* [comment removed for export] *)
        ab_ft C88 D_63528 ltac:(condz).           (* [comment removed for export] *)
        aret C92 D_6352c ret.
        replace (k + 8 + 8)%Z with n by lia. apply mst_refl.
      + unfold imemset_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s (k + 16)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + eexists. split.
        * msd C76 D_6351c k.
          msd C80 D_63520 (k + 8)%Z.
          an C84 D_63524.
          ab_tk C88 D_63528 ltac:(condz).         (* [comment removed for export] *)
          replace (k + 8 + 8)%Z with (k + 16)%Z by lia. apply mst_refl.
        * post. unfold imemset_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 16)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hc256) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem imemset_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom)
                  (mkst regs' ret (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) rom)
      /\ regs_agree CL regs regs'.
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    pose proof (align15_range n s Hn) as HA.
    change (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) with (MS n). change mem0 with (MS 0).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MS 0) rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = c /\ getr r 12 = Z_to_bv 64 n
                       /\ getr r 13 = Z_to_bv 64 (align15 n s) /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_634d0.                            (* [comment removed for export] *)
        av C4 D_634d4 (Z_to_bv 64 (align15 n s))
           ltac:(rewrite <- (u_align15 n s) by lia; symmetry; apply Z_to_bv_bv_unsigned).  (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold imemset_clob. solve_regs_agree. }
    cbv beta. intros r0 (R1 & R10 & R11 & R12 & R13 & AG0).
    destruct (Z.eq_dec (align15 n s) 0) as [HA0|HA0].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + eexists. split.
        * ab_tk C8 D_634d8 ltac:(condz).          (* [comment removed for export] *)
          ab_tk C40 D_634f8 ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_6352c ret.
          rewrite Hz. apply mst_refl.
        * exact AG0.
      + pose proof (HC256 HA0 Hnz) as Hc256.
        pose proof (align15_n16 n s Hn HA0) as Hn16.
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_tk C8 D_634d8 ltac:(condz).       (* [comment removed for export] *)
             ab_ft C40 D_634f8 ltac:(condz).      (* [comment removed for export] *)
             av C44 D_634fc (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             av C48 D_63500 (Z_to_bv 64 (bv_unsigned c * 2 ^ 8)) ltac:(apply v_slli_mul; lia).  (* [comment removed for export] *)
             av_or C52 D_63504 (Z_to_bv 64 (bv_unsigned c * 257))
               ltac:(rewrite v_or_shl by (unorm; lia); f_equal; lia).                        (* [comment removed for export] *)
             av C56 D_63508 (Z_to_bv 64 (bv_unsigned c * 257 * 2 ^ 16))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C60 D_6350c (Z_to_bv 64 (bv_unsigned c * 16843009))
               ltac:(rewrite v_or_shl by (unorm; lia); unorm; f_equal; lia).                 (* [comment removed for export] *)
             av C64 D_63510 (Z_to_bv 64 (bv_unsigned c * 16843009 * 2 ^ 32))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C68 D_63514 (cpat_ c)
               ltac:(rewrite v_or_shl by (unorm; lia); unfold cpat_, M8; unorm; f_equal; lia). (* [comment removed for export] *)
             an C72 D_63518.                      (* [comment removed for export] *)
             apply mst_refl.
          -- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
        * cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
          assert (Hdiv : (n = 16 * (n / 16))%Z) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
          assert (Hi : exists i : nat, (Z.of_nat i * 16 = n - 0 - 16)%Z) by (exists (Z.to_nat (n / 16 - 1)); lia).
          destruct Hi as (i & Hi).
          destruct (al_loop i r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia) Hi Hc256) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + eexists. split.
        * ab_ft C8 D_634d8 ltac:(condz).          (* [comment removed for export] *)
          ab_tk C12 D_634dc ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_6352c ret.
          rewrite Hz. apply mst_refl.
        * exact AG0.
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C8 D_634d8 ltac:(condz).       (* [comment removed for export] *)
             ab_ft C12 D_634dc ltac:(condz).      (* [comment removed for export] *)
             av C16 D_634e0 (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             an C20 D_634e4.                      (* [comment removed for export] *)
             apply mst_refl.
          -- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
        * cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
          destruct (bl_loop (Z.to_nat (n - 1)) r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMSET.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.zstd.huf_decompress.images Require Import Asan.

(* [comment removed for export] *)
Definition asan_imemset_entry : word := 0x634a0.

Lemma asan_imemset_code :
  code_at Asan.M.loaded_segments asan_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem asan_imemset : forall mem0 (s c : word) n rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
  store_ok Asan.M.loaded_segments mem0 s (Z.to_nat n) = true ->
  (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps Asan.M.loaded_segments
           (mkst regs asan_imemset_entry mem0 rom)
           (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
    /\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanIMemset ()) [] "h05HC256h12Hnh23Hnwh33Hokh41bh51ch64mem0h71nh81rh94regsh:5regs'h;3reth<3romh=1sp;1p;2p;4p;3p;5p;>p;6g000Lj10Tg00Cmj15Tg00DKj17Tg00X2j1>Tg00PEj18Tg00Ybj2NTg0000j2CTg00Dnj26Tg00XTj2@Tg0011j11Tg001Oj2=Tg002Lj29Tg02?@j1:Tg02m3j4PTg008`j32Tg00LDj2OTg012Ej1MTg00Y1j2HTg00ZNj1DTg00[Bj33Tg00[ej24Tg00O_j2;Tg01FAj5<Tg021[j3BTg00d4j3ATg00afj3ETg00_Fj3FTg00_]j3GTg002hj2?Tg00`Uj2ITg02n3l>JTg02RBj1KTg00U?j6LTg00@NR0#0R1#0#0R2#0#0#0R3#5R4#7R5%52R2#7R6#>[R7g00?RR8%81R9#5R:/N5R;g00@0R<f3R='Cf6R>,64f4R?'@%11%13'='9g00BFg02j^R1f8R@f7RAf5RB#:CPg00Bf321O>@=28<A28A<#Mf9R8,64%03#0#1'9[[P5g02kmR3/H<%DB%10g01SGR<53:,4A=25>%09#1=3:<,4@f<RC525%89#1=3:<,48=25Cf:R9%80#0#0#1=3:<'41;4C525g01LPR<PCP>fAR0f=RDD<P<f0R<f;f@f?,64,;2f>#:5B65A0PDD<5E1%7:R:g01iN9F:<W8?GC<'?X:;,I;[[[[[X45P1P3P9P8P@PAP>g02o2P=f2f1P<PBP?M>JP3%K3ELW0W3W2W1X;5W9X<7W7X55X=5W6o"). Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
