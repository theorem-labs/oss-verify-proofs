(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses for this unit's binaries): changed L_b84, L_bec, ffp_entry and 1 more; added FILE_cells4, cur_reg, file_cells4 and 7 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/U/CJ/F10/F_fmt_fp_nf_u.v, lines 40-41, 108-170, 261-421, 436-462, 475-525. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Arr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memset_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memcpy_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fwritex_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_pad_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_frexpl_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_main_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_split.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_splitR.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFp_splitH.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import FmtFp_facts_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import FmtFp_facts2_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_lib_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_calls_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_pre_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_pre2_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_pre3_u5.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_pre4_u5.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import StoreFast.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFpNF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require F_fmt_fp_u5.
(* Several imported modules each define their own [rsegs] (F_memset_u5, F_memcpy_u5, F_fmt_fp_calls_u5):
   a goal and a hypothesis can carry convertible but not syntactically equal copies, which [hyp]
   (syntactic) refuses with "Not equal".  [hyp] is shadowed once: the original first, then
   [assumption], which unifies up to conversion. *)
Ltac hyp0 := hyp.
Ltac hyp := first [hyp0 | assumption].
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @mem_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @ro_bytes_at]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_lib_u5; @zb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @INF_LC]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Corelib; @Init; @Datatypes; @list]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Init; @Datatypes; @nat]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Corelib; @Init; @Datatypes; @comparison]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Image; @ro_bytes_b_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Image; @ro_bytes_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Arr; @u8ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @NAN_LC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @INF_UC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @NAN_UC]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @f128_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @nfs_INF_u8ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @nfs_NAN_u8ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @nfs_inf_u8ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @nfs_nan_u8ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @nfs_addr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @nf_str]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @micromega; @Tauto; @AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_frexpl_u5; @f128_le_cases]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Logic; @conj]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Init; @Logic; @I]; [@Corelib; @Init; @Logic; @False_ind]; [@Corelib; @Init; @Datatypes; @list_ind]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @bytes_le_to_Z]; [@Corelib; @Init; @Logic; @and_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_nonneg]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_modulus]; [@stdpp; @bitvector; @definitions; @bv_unsigned_in_range]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_nonneg]; [@Corelib; @Init; @Datatypes; @cons]; [@Stdlib; @ZArith; @BinInt; @Z; @bits_inj']; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit]; [@Corelib; @Init; @Datatypes; @orb]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @Bool; @Bool; @orb_false_r]; [@Stdlib; @ZArith; @BinInt; @Z; @testbit_neg_r]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @Bool; @Bool; @andb_false_r]; [@Stdlib; @ZArith; @BinInt; @Z; @pow2_bits_eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl_spec]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @ZArith; @BinInt; @Z; @lor_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @land_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@stdpp; @tactics; @f_equal_help]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_comm]; [@Stdlib; @ZArith; @BinInt; @Z; @land_assoc]; [@stdpp; @bitvector; @definitions; @bv_wrap]; [@Corelib; @Lists; @ListDef; @firstn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @lor_shl8_land32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @bytes_le_to_Z_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @land_mod_pow2_small]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@stdpp; @bitvector; @definitions; @Z_to_bv_unsigned]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @le_bytes_to_word]; [@Corelib; @Lists; @ListDef; @skipn]; [@Corelib; @Init; @Datatypes; @O]; [@stdpp; @bitvector; @definitions; @bv_extract]; [@Corelib; @Numbers; @BinNums; @N0]; [@Stdlib; @ZArith; @BinInt; @Z; @of_N]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @w4_core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @extract_low_mod]; [@Stdlib; @NArith; @BinNat; @N; @lt]; [@Stdlib; @ZArith; @Znat; @N2Z; @inj_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit]; [@LinuxProcessSemantics; @Riscv; @Prelude; @zext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @zext_small]; [@stdpp; @bitvector; @definitions; @bv_signed]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @LiaTuning; @zify_done]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @ZArith; @Zdiv; @Zminus_mod_idemp_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @signed_of_extract]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @unsigned_lit_wrap]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @sext_small]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @FmtFp; @Fp]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_state]; [@Corelib; @Init; @Logic; @ex]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @MS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @mkR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @FmtFp; @Wfp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @FP; @frm0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @wfile]; [@Corelib; @Init; @Nat; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @ssp_cells]; [@LinuxProcessSemantics; @Riscv; @Sem; @reg_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @FmtFp; @finv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @C4]; [@Stdlib; @ZArith; @BinInt; @Z; @b2z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFp_split; @ffp_sign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @FmtFp; @yv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @FmtFp; @hi_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @got_ssp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_pad_u5; @ssp_guard]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @FmtFp; @fmt_fp_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @hi64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @SoftFloat; @lo64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_memcpy_u5; @rsegs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @FILE_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @fmt_fp_nf]; [@Corelib; @Init; @Datatypes; @Some]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @fpclassifyl]; [@Corelib; @Init; @Datatypes; @app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @zsub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @PREFIX_STR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_step]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TNode]; [@LinuxProcessSemantics; @Riscv; @Prelude; @TEmpty]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ms_svc_pending]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @machine_result]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @step]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lift_result]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @interp_eff0]; [@LinuxProcessSemantics; @Riscv; @Sem; @exec]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@LinuxProcessSemantics; @Riscv; @Sem; @Core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@stdpp; @bitvector; @definitions; @bv_add]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @lit_add_lit]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_addi]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tset]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap_set]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tget]; [@LinuxProcessSemantics; @Riscv; @Sem; @w0]; [@LinuxProcessSemantics; @Riscv; @Sem; @core]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @step_gen]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@LinuxProcessSemantics; @Riscv; @DecodeC; @decode_any]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_addsext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @fpclassifyl_postv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @fpclassifyl_callv]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @ivl]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_even]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Corelib; @Init; @Peano; @lt]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w0_lit]; [@Corelib; @Init; @Datatypes; @negb]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_lts]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GE]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Bool; @Bool; @negb_true_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @SFModel; @signed_of_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_lib_u5; @fpclassifyl_range]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Corelib; @Init; @Logic; @proj2]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@Stdlib; @Bool; @Bool; @andb_true_iff]; [@Stdlib; @micromega; @Tauto; @X]; [@Corelib; @Init; @Logic; @f_equal]; [@Corelib; @BinNums; @PosDef; @Pos; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @pos_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_pre4_u5; @zsub_length]; [@Corelib; @Init; @Peano; @le]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @Tauto; @OR]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @nf_str_length]; [@Stdlib; @Lists; @List; @length_app]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_andi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @leaf1_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @letf2_callv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @rw_cells_transport]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @disjoint_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_transport_disjoint]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_weaken]; [@Stdlib; @micromega; @Tauto; @TT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @outside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @sub_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @nfs_addr_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_merge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cells_bytes]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @ov_read_bytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineFault]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @MachineUnmodeled]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cb_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_read_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @csize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @wa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @wa_of_Z_to_bv]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @inr64_unsigned_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_land_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_neq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @w4_bit5]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @Bool; @Bool; @negb_false_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @load_u64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_pre4_u5; @bytes_at_slice]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_pre2_u5; @prefix_u8ro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_pre4_u5; @zb_length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @bytes_at]; [@Stdlib; @ZArith; @Znat; @Z2Nat; @id]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_pre4_u5; @zb_zsub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_split]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @fwritex_postZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_pre4_u5; @fwritex_callR]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @bytes_at_transport]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_merge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @w4s_bit5]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @nfs_u8ro]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @Lists; @List; @length_skipn]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_lui]; [@stdpp; @bitvector; @definitions; @bv_concat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_lui]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_and]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_and]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_ltu]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@Stdlib; @ZArith; @BinInt; @Z; @add_assoc]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @Z_to_bv_lit_self]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_release]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@stdpp; @bitvector; @definitions; @bv_and]; [@stdpp; @bitvector; @definitions; @bv_not]; [@LinuxProcessSemantics; @Riscv; @Sem; @w1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @ret_pc_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @w1_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_done]; [@Corelib; @Init; @Logic; @ex_intro]; [@LinuxProcessSemantics; @Riscv; @Prelude; @tree]; [@Stdlib; @Lists; @List; @app_assoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_pre4_u5; @zb_app]; [@Stdlib; @Lists; @List; @skipn_skipn]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Ubsan; @Ubsan_loaded_segments]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_slli]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_slli]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @bv_lts_zero_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @unsigned_lit_land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_gt]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_auipc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @unsigned_Z_to_bv_add_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @b_auipc]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms_Prop; @not_iff_morphism]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @le_land0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @lo64_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @hi64_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @signbitl_postv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @signbitl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @signbitl_callv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @SFW1_lemmas; @land_W64_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_lib_u5; @signbitl_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_lib_u5; @shl52_land64]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @write_to_mem]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @Z_to_le_bytes]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_bound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @mem_inv_store_cbytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @rw_cells_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Cells; @cell_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @StoreFast; @rw_cells_frame_n]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @StoreFast; @munch_write_n]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @inside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_write]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @StoreFast; @stk_write_n]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @FmtFp; @L_bec]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @F128_SIGNBIT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @PAD_POS]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_lib_u5; @land_bit11]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @MARK_POS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_lib_u5; @le8_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_8']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @zr_mod_any]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sltiu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sltiu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_lib_u5; @land_bit0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @ZBridge; @v_sltiu_b2z]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_xor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @lo64_flip_sign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_calls_u5; @hi64_flip_sign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @munch_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @wmono_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @MState; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @SFW1_lemmas; @lo64_words]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @FA; @SFW1_lemmas; @hi64_words]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_carve]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @rw_cells_split_CB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Tac; @mk_CB_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fwritex_u5; @rw_cells_app]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @alu_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Frame; @stk_of_rw_cells]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Mem; @le4]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Step; @store_bytes_4']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @FmtFp; @L_b84]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_u5; @FMT_FP_DEPTH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Lib; @Exec; @evt_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @fmt_fp_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_u5; @fmt_fp_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @NF; @ffp_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @fmt_fp_nf_stmt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @fmt_fp']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @fmt_fp_facts']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @nonfinite_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @nonfinite]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @fmt_fp'_nonfinite]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @fmt_fp_nf_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @fmt_fp_nf_w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @Spec; @FmtFp; @fmt_fp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CJ; @F6; @FmtFpNF; @fmt_fp'_finite]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_u5; @fmt_fp_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_u5; @fmt_fp_spec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @U5; @CJ; @F6; @F_fmt_fp_nf_u5; @fmt_fp'_stmt]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= transport_chunks_extra_wfile m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= transport_call_extra_wfile segs W m m' MU WM.
Local Ltac lia ::= lia3.

(* [comment removed for export] *)
Module NF.
(* [comment removed for export] *)
Lemma nfs_inf_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 71419 (zb INF_LC).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SM0|600;!1,10|30;!1+0!1,12!1,6|@16fb;!1'7'8!1,9+:!1+;+:!1,<+=!1+>+=!1+@+=!2,E+=4!2'I:,C!2,K+L,M!4'J#1#3vv=!3+N+L!2'O#1#3,M!3'P+=,F#2}3!1'T?!2'S4@|10;!1,6B!1,60!2'UCD!1,6|11;!2'S4F!2'QGE$x;R+=#1!2'^1,FC%~R!2'Q,FD!2'^1,FE!2'Q,FC$m;R%~R!1+01!1+23$MI;R!2'3'4#1vd!8'5'4#245#1&__arith;R&__wit;R67&__varmap;R89&__ff;R!7,?:'A+B+B,C!4,D+=!2,E+=,F,G;,H<>!2'Q,F4#1vd!4'R!2'QAEH!<'V+=+='QI'Q$x;R+=$y;R+=!1'W!2'Q#2#1AG!B'X+=+=+=+=+=+='SIII'S$n;R+=$m;R+=!2,K+=!4'Y+=+='Z!2'S#2#144!2,K+=4@F!<'[+\+=+=+='T'TII$x;R+\!2,K+=!1'T#1?F!2,K+=FEE!2,K+=E&__sat1;R!2'^0CD%~RJK&__sat0;R$Ha;RL$~R+^2!3'^3CD#2%Ha;RL%~R+^2!2'Q,FE&__sat1;R!1#2vd!2,K+^4!2'^5,FCJK&__arith;R&__wit;R67&__varmap;R89&__ff;R!7,?:'A+B+B,C!4,D+=!3,^6+=;!2,E+=F,G!3,^7+=!2,E+=C1,H<>H#1!2'Q!2'S4!1'T!2'^835E!4'^9'454vv=!3+N+L!3'^:'445,M!4'^;'4#245").
Qed.
Lemma nfs_nan_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 78834 (zb NAN_LC).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SM0|600;!1,10|30;!1+0!1,12!1,6|@33f2;!1'7'^<!1,9+:!1+;+:!1,<+=!1+>+=!1+@+=!2,E+=4!2'I:,C!2,K+L,M!4'J#1#3vv=!3+N+L!2'O#1#3,M!3'P+=,F#2}3!1'T?!2'S4@|10;!1,6B!1,60!2'UCD!1,6|11;!2'S4F!2'QGE$x;R+=#1!2'^1,FC%~R!2'Q,FD!2'^1,FE!2'Q,FC$m;R%~R!1+01!1+23$MI;R!2'3'4#1vd!8'5'4#245#1&__arith;R&__wit;R67&__varmap;R89&__ff;R!7,?:'A+B+B,C!4,D+=!2,E+=,F,G;,H<>!2'Q,F4#1vd!4'R!2'QAEH!<'V+=+='QI'Q$x;R+=$y;R+=!1'W!2'Q#2#1AG!B'X+=+=+=+=+=+='SIII'S$n;R+=$m;R+=!2,K+=!4'Y+=+='Z!2'S#2#144!2,K+=4@F!<'[+\+=+=+='T'TII$x;R+\!2,K+=!1'T#1?F!2,K+=FEE!2,K+=E&__sat1;R!2'^0CD%~RJK&__sat0;R$Ha;RL$~R+^2!3'^3CD#2%Ha;RL%~R+^2!2'Q,FE&__sat1;R!1#2vd!2,K+^4!2'^5,FCJK&__arith;R&__wit;R67&__varmap;R89&__ff;R!7,?:'A+B+B,C!4,D+=!3,^6+=;!2,E+=F,G!3,^7+=!2,E+=C1,H<>H#1!2'Q!2'S4!1'T!2'^835E!4'^9'454vv=!3+N+L!3'^:'445,M!4'^;'4#245").
Qed.
Lemma nfs_INF_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 73921 (zb INF_UC).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SM0|600;!1,10|30;!1+0!1,12!1,6|@20c1;!1'7'^=!1,9+:!1+;+:!1,<+=!1+>+=!1+@+=!2,E+=4!2'I:,C!2,K+L,M!4'J#1#3vv=!3+N+L!2'O#1#3,M!3'P+=,F#2}3!1'T?!2'S4@|10;!1,6B!1,60!2'UCD!1,6|11;!2'S4F!2'QGE$x;R+=#1!2'^1,FC%~R!2'Q,FD!2'^1,FE!2'Q,FC$m;R%~R!1+01!1+23$MI;R!2'3'4#1vd!8'5'4#245#1&__arith;R&__wit;R67&__varmap;R89&__ff;R!7,?:'A+B+B,C!4,D+=!2,E+=,F,G;,H<>!2'Q,F4#1vd!4'R!2'QAEH!<'V+=+='QI'Q$x;R+=$y;R+=!1'W!2'Q#2#1AG!B'X+=+=+=+=+=+='SIII'S$n;R+=$m;R+=!2,K+=!4'Y+=+='Z!2'S#2#144!2,K+=4@F!<'[+\+=+=+='T'TII$x;R+\!2,K+=!1'T#1?F!2,K+=FEE!2,K+=E&__sat1;R!2'^0CD%~RJK&__sat0;R$Ha;RL$~R+^2!3'^3CD#2%Ha;RL%~R+^2!2'Q,FE&__sat1;R!1#2vd!2,K+^4!2'^5,FCJK&__arith;R&__wit;R67&__varmap;R89&__ff;R!7,?:'A+B+B,C!4,D+=!3,^6+=;!2,E+=F,G!3,^7+=!2,E+=C1,H<>H#1!2'Q!2'S4!1'T!2'^835E!4'^9'454vv=!3+N+L!3'^:'445,M!4'^;'4#245").
Qed.
Lemma nfs_NAN_u8ro : forall m, mem_inv rsegs m -> u8ro rsegs m 78076 (zb NAN_UC).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SM0|600;!1,10|30;!1+0!1,12!1,6|@30fc;!1'7'^>!1,9+:!1+;+:!1,<+=!1+>+=!1+@+=!2,E+=4!2'I:,C!2,K+L,M!4'J#1#3vv=!3+N+L!2'O#1#3,M!3'P+=,F#2}3!1'T?!2'S4@|10;!1,6B!1,60!2'UCD!1,6|11;!2'S4F!2'QGE$x;R+=#1!2'^1,FC%~R!2'Q,FD!2'^1,FE!2'Q,FC$m;R%~R!1+01!1+23$MI;R!2'3'4#1vd!8'5'4#245#1&__arith;R&__wit;R67&__varmap;R89&__ff;R!7,?:'A+B+B,C!4,D+=!2,E+=,F,G;,H<>!2'Q,F4#1vd!4'R!2'QAEH!<'V+=+='QI'Q$x;R+=$y;R+=!1'W!2'Q#2#1AG!B'X+=+=+=+=+=+='SIII'S$n;R+=$m;R+=!2,K+=!4'Y+=+='Z!2'S#2#144!2,K+=4@F!<'[+\+=+=+='T'TII$x;R+\!2,K+=!1'T#1?F!2,K+=FEE!2,K+=E&__sat1;R!2'^0CD%~RJK&__sat0;R$Ha;RL$~R+^2!3'^3CD#2%Ha;RL%~R+^2!2'Q,FE&__sat1;R!1#2vd!2,K+^4!2'^5,FCJK&__arith;R&__wit;R67&__varmap;R89&__ff;R!7,?:'A+B+B,C!4,D+=!3,^6+=;!2,E+=F,G!3,^7+=!2,E+=C1,H<>H#1!2'Q!2'S4!1'T!2'^835E!4'^9'454vv=!3+N+L!3'^:'445,M!4'^;'4#245").
Qed.
Definition nfs_addr (y1 t : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!2'^?!2'^A#2#2,F$y1;R+=$t;R+=-LRN$~R+L+=!2'^?!2'^@#1!1,6|500;,F2-LRN$~R+L+=02!1,6|@20c1;!1,6|@30fc;-LRN$~R+L+=02!1,6|@16fb;!1,6|@33f2;").
Lemma nfs_u8ro : forall m y1 t, mem_inv rsegs m -> u8ro rsegs m (nfs_addr y1 t) (zb (nf_str y1 t)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90|30;|500;!2'^?!2'^A#5#5,F!1,6|@20c1;!1,6|@30fc;!1,6|@16fb;!1,6|@33f2;!1+;+=!2'^?!2'^A#4#4,F$m;R%~R!1+0!1,1|600;!1+2!1+0!1,10$y1;R+=$t;R+=$MI;R!2'3'4#3vd&b;R!2'^?!2'^@#2!1,61,F+L-LRN$b;R+L!4'^;'4#6-LRN$~R+L+=#12-LRN$~R+L+=2234-LRN$~R+L+=2256!1'7-LRN$~R+L7#12-LRN$~R+L722'^='^>-LRN$~R+L722'8'^<#12&b;R8+L-LRN$b;R+L!4'^;'4#7-LRN$~R+L+=#1234!1'7-LRN$~R+L7#12'^='^>#12!2'^B#6#3!2'^C#6#3&b;R8+L-LRN$b;R+L!4'^;'4#7-LRN$~R+L+=#1256!1'7-LRN$~R+L7#12'8'^<#12!2'^D#6#3!2'^E#6#3!4'^;'4#4!2'^F#3#2!1'7!2'^G#3#2").
Qed.
Lemma nfs_addr_range : forall y1 t, (71419 <= nfs_addr y1 t <= 78834)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SG0!1,6|@16fb;!2'^?!2'^A#4#4,F!1,6|@20c1;!1,6|@30fc;!1,6|@33f2;-LRN$~R+L+=#12-LRN$~R+L+=1223-LRN$~R+L+=1204!2'^?!2'^A#3#3,F-LRN$~R+L+=#1223!1,9+:!1+;+:!1,<+=!1+>+=!1+@+=!2,E+=0!2,E+=2!2,E+=4!2'I<,C!4'J#1#3vv!2,K+L,M!3+N+L!2'O#1#3,M!3'P+=,F#2!2,E+=3-LRN$~R+L+=#1204!7,?<'A+B+B,C!4,D+==,G?,H!2'Q04!2'^F#2#1$y1;R+=$t;R+=vd&b;R!2'^?!2'^@#1!1,6|500;,F+L-LRN$b;R+L!2+^H!2'Q05!2'Q54#12&b;R6+L-LRN$b;R+L!2+^H!2'Q07!2'Q74#12&__arith;R&__wit;R89&__varmap;R:;&__ff;R!7,^I<'A+B+B,C!7,?<'A+B+B,C!4,D+==,G>,H!7,?<'A+B+B,C!4,D+=>,G?,H@A!2+^H!2'Q02!2'Q24#1&__arith;R&__wit;R89&__varmap;R:;&__ff;R!7,^I<'A+B+B,C!7,?<'A+B+B,C!4,D+==,GB,H!7,?<'A+B+B,C!4,D+=B,G?,H@A!2+^H!2'Q03!2'Q34#1&b;R6+L-LRN$b;R+L!2+^H!2'Q0C!2'QC4#12&__arith;R&__wit;R89&__varmap;R:;&__ff;R!7,^I<'A+B+B,C!7,?<'A+B+B,C!4,D+==,G=,HD@A!2+^H!2'Q00E#1&__arith;R&__wit;R89&__varmap;R:;&__ff;R!7,^I<'A+B+B,CD!7,?<'A+B+B,C!4,D+=?,G?,H@A!2+^HE!2'Q44#1!2+^H!2'Q0F!2'QF4").
Qed.

Lemma le_land0 : forall a b, (Z.land (f128_le a b) 18446744073709551615 = 0 <-> f128_le a b = 0)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SG0!2'^A#2#1!1,^L,^M!1,6,^M!2'^A#3#2!3+N+=31!2+^K!3+N+=3,F!3+N+=32!1,6|^B7fffffffffffffff;!2'^A#4#3$z;R+=!2'^O!3+N+=!2'^@#16,F!3+N+=#1,F!3+N+=6,F!3+N+=1,F$e;R+=-=RN$z;R+=w#13+^S$~R+^T+^2$~R+^T+^S!2'^A#5#4!3+N+=<,F!3+N+=<2!2'^A#6#5!3+N+=,F,F%x;R@@$H;R@!2,K+=,F!2'^A#7#6!3+N+=2,F%x;RDD$H;RD&H0;R!6'^R+=2;,^U,F#1+^S!2'^VD#1$a;R+=$b;R+=&o;R!2'^J#2#1!2+^K!3+N+=01!2+^K!3+N+=0,F!3+N+=02!6'^N45!2'^O!3+N+=!2'^@!2'^A#3#26,F!3+N+=!2'^A#3#2,F$~R4!1$E;R!3+N+=71!6'^P+=18vv!4,^Q%x;R9:%x;R:9$H;R9&H0;R!6'^R+=6;,^U,F#1+^S!2'^V:#1$H;R:&H0;R!6'^R+=1$e;R+=-=RN$z;R+=w#13+^S$~R+^T+^S$~R+^T+^2,^U,F#1+^S!2'^V9#1!2'^O!3+N+=!2'^@16,F:<#1#1$~R5!1$H;R!2+^K!3+N+=7,F!3+N+=72!6'^N=>!2'^O!3+N+=!2'^@!2'^A#5#46,F!3+N+=!2'^A#5#4,F$~R=!1$E;R!3+N+=?,F!6'^P+=,F8vv!4,^QAABB!2'^O!3+N+=!2'^@,F6,F@C#1#1$~R>!1$E;R!3+N+=?2!6'^P+=28vv!4,^QEEFF!2'^O!3+N+=!2'^@26,FDC#1#1#1#1#1").
Qed.
Ltac nfs_eq y1 t Kn := unfold nfs_addr; rewrite ?le_land0 in Kn; destruct (Z.eqb_spec (Z.land t 32) 0); destruct (Z.eqb_spec (f128_le y1 y1) 0); try lia; reflexivity.

Ltac nf_mseq := cbv delta [mkR]; repeat first [ reflexivity | lia | progress f_equal ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ nf_mseq | .. ].

(* [comment removed for export] *)
Lemma bytes_le_to_Z_nonneg : forall bs, (0 <= bytes_le_to_Z bs)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SC0|30;!1,10!1+01!1+;2!2'Q,F!1'^X#1!1+@+=!2,E+=,F!2'Q,F#3!2'Q,F#2%~R!2'Q,F!2'^Z#2#1!2+^H78%~R!2+^H8!2'Q,F#1!2'Q,F!2'^Z#3#2!2'^\1#4!1,60!2'_0!1'^X#3<!1+0#1!2'^\#2#1!2'Q,F?%~R!2'Q,F!2'_0#2#17%~R8!2'Q,F!2'_0#3#2$bs;R3!5'^W2$bs;R34vd&__arith;R&__wit;R!1,9+:!1+;+:&__varmap;R!1,<+=!1+>+=&__ff;R!7,?5'A+B+B,C!4,D+=6,G6,H!2'I5,C!4'J#1#3vv!2,K+L,M!3+N+L!2'O#1#3,M!3'P+=,F#2!2'Q,F,F#1!2'Q,F!1'^X!1,92$b;R2$bs;R3$IH;R4vd&H;R$a;R+=$b;R+=!5'^Y9:%~R!2+^H!2'Q,F#2!2'Q,F#1!2'Q,F!2'^Z#3#2$~R9$~R%~R!2+^H!2'Q,F#3!2'Q,F#2!2'Q,F!2'^Z#4#3#1!2'^[#2#1%a;R+=%b;R+=:!3#1;=!4,^Q!2'Q,F;!2'Q,F=&H;R$n;R+_1$b;R>!5'^Y@!2'^1?!1'_2#2!2'Q,F!2'^\#2#1$~R@$~R!2'^1!2'^\#3#2!1'_2#3#2!2'_3#2#1%n;R+_1%b;R>@!2#11#5&H;R$a;R+=$n;R+=!5'^YAB%~R!2'Q,F#2!2'Q,F!2'_0#3#2$~RA$~R%~R!2'Q,F#3!2'Q,F!2'_0#4#3#1!2'_4#2#1%a;R+=%n;R+=B!3#1!1'^X#4<#3!2'Q,F!1'^X!3,_52#3#2#1").
Qed.
Lemma lor_shl8_land32 : forall x y, (0 <= x < 256)%Z -> (0 <= y)%Z -> Z.land (Z.lor x (Z.shiftl y 8)) 32 = Z.land x 32.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SW0!2'Q,F#2|30;!1,61|500;!1,63!2'Q,F#1!2'_0#52!2'^Z#66!2'_87#2!2'_84#2!2'_8#6#2!2'_84#3!2'_86#2!2'_8#7#3!2'_7=;!2'_:#22!1,6|21;!2'^?@#2!2'_8#:#6!2'_9B!2'_8#9!2'_:#62!3+N+=@#4!3+N+=@#5!2'_8#<#2!2'Q,F@!2'_8#<@!2'_7H,M!2'_8#;@!2'_:@2!1,9+:!1+;+:!1,<+=!1+>+=!1+@+=!2,E+=@!2,E+=,F!2'IP,C!4'J#1#3vv!2,K+L,M!3+N+L!2'O#1#3,M!3'P+=,F#2|10;!7,?P'A+B+B,C!4,D+=R,G!2,_H+=,^M,H$x;R+=$y;R+=$Hx;R!2+^H0!2'^1#2!1,6|800;$Hy;R0!3'_6!2'^@!2'^Z#4!2'_0#324!2'^@#44$n;R+=$Hn;R5!6'^P+L!2'_789$b;R+L!3+N+L#1!2'_8!2'^@#74#3!6'^P+L!2'_7:9$b;R+L!3+N+L!2'_7!2'_8!2'^Z#7!2'_0#62#3;#1!6'^P+L!2'_9:<$b;R+L!3+N+L!2'_7#1;>!6'^P+L!2'_8#5?$b;R+L!3+N+L!2'_7!2'_9=#1;>!6'^P+LA$b;R+L!3+N+L!2'_7!2'_9=!2'_8#6!2'_:#32#1!2'_7=#1&r;R!2'_;@#2!2+_<!3+N+=@#2A&b;R!2'^?@#3+L-_<RN$b;R+L$r;R!2+_<!3+N+=@#5#1!3+N+L!2'_7C#2!2'_7B#2#22$e;RD!1$e;RE!7'^R+=@$n;R+=%Hn;R5!3+N+L!2'_7!2'_9F!2'_8#;?,M!2'_7F,M$Hn;RG!6'^P+L,_=$b;R+L!3+N+L!2'_7!2'_9H#1,MI!6'^P+LJ$b;R+L!3+N+L!2'_7#1,MI!2,K+L!2'_7J,M!2'_9J,_=!1'_>J!2'_8#:K!3'_?#:K&__arith;R&__wit;RLM&__varmap;RNO&__ff;R!7,?P'A+B+B,C!4,D+=!3,_@+=Q!2,E+=2,_AR,HST!2'^1K,F#1#6#1#5#1$n;R!1'_BD!1$N5;R!1'_BE!6'^P+L,_=$b;R+L!3+N+L#1!2'_7!2'_8#;#7,_=!6'^P+L,_=$b;R+L!3+N+L,_=#1!2,K+L,_=!2'_7B,_=!1'_CB!2'_7C,_=!1'_CC#1!2'_8!2'U!1,6U@#2!3'_D@#2&__arith;R&__wit;RLM&__varmap;RNO&__ff;R!7,?P'A+B+B,C!4,D+=R,GQ,HSTG#1<!4'_E#52#2&__arith;R$__x1;R+=&__wit;RLM&__varmap;R!2,_F+=#2O&__ff;R!8,_GP'A+B+B,CV!1,_I+BVST%__x1;R+=%~R50!2#1#3#28!3'_J#66#2!2'_8!2'^@#64#2!3'_K#64#2!2'_8!2'^@74#2!3'_K74#2").
Qed.
Lemma land_mod_pow2_small : forall v k m, (0 <= k)%Z -> (0 <= m < 2^k)%Z -> Z.land (v mod 2^k) m = Z.land v m.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SP0!2'Q,F#2|10;!1,61!1'_L#4!2'^@#53!2'^@#6#4!2'^@3#3!1'^@#5!2'^@#33$z;R+=!3+N+=#1#4!2'U2#4!2'^02#4!2'^1,F2%~R<%~R!2'Q,F#5!2'^1,F!2'U2#6!2'Q,F2$Ha;R>$~R+^2!3'^32#7#2!2'U2#7%Ha;R>%~R+^2!2'Q,F@!1#2vd!2,K+^4!2'^5,F2<%~R!2'Q,F#6!2'^1,F@!1,9+:!1+;+:!1+>+=!1+@+=!2,_H+=,^M!7,?G'A+B+B,C!4,D+=!2,E+=,F,GH,H!7,^IG'A+B+B,CI!7,?G'A+B+B,C!4,D+=H,_A!2,_H+=1,H!1,_I+B!2'IG,C!4'J#1#3vv!2,K+L,M!3+N+L!2'O#1#3,M!3'P+=,F#2!2'Q,F#1&__sat1;R;=&__sat0;R?A&__sat1;RBC&__arith;R$__x1;R+=&__wit;RDE&__varmap;R!2,_F+=#2F&__ff;R!8,_GG'A+B+B,CIKILM%__x1;R+=%~RN0!2#1#8#6$v;R+=$k;R+=$m;R+=$Hk;R0$Hm;R!2+^H0!2'^1#2!2'U2#3!6'^R+=4$z;R+=!3+N+=!2'^@#1#45!6'^R+=!2'^@#56$z;R+=!3+N+=#15!8'_M+=+=776#3!2,K%~R+=+=7!6'^P+=89!6'^P+=!2'_N#3:9!3'_O#3:&__sat1;R;=&__sat0;R?A&__sat1;RBC&__arith;R$__x2;R+=$__x1;R+=&__wit;RDE&__varmap;R!4,_P+=!2,_F+=#3#2!1,<+=F&__ff;R!8,_GG'A+B+B,CJKJLM%__x2;R+=%__x1;R+=%~R!2+^HN!2'^1#1#2!2+^H0!2'^1#2#3!3#1!2'U2#8#7#58!3'_Q#3#4O6!2'_R3#3!2'^@4#3!3'_S#53#3!2'_N#5:!3'_Q#5#4O").
Qed.
Lemma w4_core : forall (b : byte) (l : list byte),
  Z.land (bv_unsigned (le_bytes_to_word (firstn 4 (skipn 0 (b :: l))))) 32 = Z.land (bv_unsigned b) 32.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "ST0|30;!1,10!1+01|600;!1,13}3!3'_U25#1!3,_52#26!1'^X7!2'_T48|500;!1,6:!2'^@!2'^\1#3;!2'^@8;!2'^\1#2!1,9+:!1+;+:!1+>+=!1+@+=!2,E+=,F!2,_H+=,^M!1,6|800;!7,^IB'A+B+B,C!7,?B'A+B+B,C!4,D+=C,GD,H!7,?B'A+B+B,C!4,D+=D,_A!2,E+=E,H!2'IB,C!4'J#1#3vv!2,K+L,M!3+N+L!2'O#1#3,M!3'P+=,F#2!2'^@>;|10;!1,6J!1,63!2'UKL!1,<+=!2'Q,FL!2'^1,FK%~RO!2'^1,FM!2'Q,FK!2,E+=;$b;R2$l;R!1+;2vdvd!6'^P+=9$z;R+=!3+N+=!2'^@#1;<vd!6'^P+==$z;R+=!3+N+=#1<vd!4'_V>!1'^X6&R;R!2'_31#2!2+^H!2'Q,F>!2'^1>!1'_21&__arith;R$__x1;R+=&__wit;R?@&__varmap;R!2,_F+=#2A&__ff;R!8,_GB'A+B+B,CF!1,_I+BFGH%__x1;R+=%~R!2+^H!2'Q,F#1!2'^1#1E!2+^H!2'Q,F#2!2'^1#2E!2#1!2'^\1#4#2!1'_W6!3+N+==I!2'^@!2'_N8M;!5'_X8L;&__arith;R&__wit;R?@&__varmap;RNA&__ff;R!7,?B'A+B+B,C!4,D+=C,G!2,E+=L,HGHO#1&__sat1;R!2'^0KL%~RPQ&__sat0;R$Ha;RR$~R+^2!3'^3KL#2%Ha;RR%~R+^2!2'Q,FM&__sat1;R!1#2vd!2,K+^4!2'^5,FKPQ&__arith;R&__wit;R?@&__varmap;RNA&__ff;R!7,^IB'A+B+B,C!7,?B'A+B+B,C!4,D+=C,GS,H!7,?B'A+B+B,C!4,D+=S,_A!3,^7+=!2,E+=K4,HGH!2+^H!2'Q,F;!2'^1;M#1!3+N+=!2'^@9;I!2'^\4!2'_Y48!2'_Z48!3+N+=!2'^@!2'^\4!1'_[7;I!3+N+=!2'^@!2'^\4!1'_[!3'_U2}4!3'_\2,`0!3,_52#2#1;I").
Qed.
Lemma w4_bit5 : forall (b : byte) (l : list byte),
  Z.land (bv_unsigned (zext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 0 (b :: l))))))) 32 = Z.land (bv_unsigned b) 32.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^30|30;!1,10!1+01|600;!1,13!1+04|500;!1,16}4!1'_[!3'_U28!3'_\2,`0!3,_52#2#1!4'`14,`279!2'^\7:!2'_Y4;!1,66!2'^@!2'^\1#3=$z;R+=!3+N+=!2'^@#1=>!2'^\49|10;!1,6A!2'UB=!1,9+:!1+;+:!1,<+=!1+>+=!1+@+=!2,E+=,F!2,E+==!7,?H'A+B+B,C!4,D+=I,GJ,H!2'IH,C!4'J#1#3vv!2,K+L,M!3+N+L!2'O#1#3,M!3'P+=,F#2!2'Q,F=!2'^0B=!2'^1,FB%~RN!2'^1,FC%~RPQ!2'Q,FB$Ha;RS$~R+^2!3'^3B=#2%Ha;RS%~R+^2!2'Q,FCvd!2,K+^4!2'^5,FBP!1#2V!2,E+=B!3,^7+=X7!2'^1,F=!1,63!2'UB[%~R!2'Q,F[!2'^1,F\!2,_H+=,^M!7,?H'A+B+B,C!4,D+=I,G^1,H$b;R2$l;R!1+;2!6'^P5<$b;R5!3+N+=!2'^@!2'^\4#1=>!6'^P+=;?!6'^P+=!2'_N@!2'UB!1'`37?!6'^P+=!2'^@@=$z;R+=!3+N+=#1>!2'`4#2#1!2'^@!2'_N@C=!5'_X@==&__arith;R&__wit;RDE&__varmap;RFG&__ff;RKLMN#1&__sat1;ROR&__sat0;RTU&__sat1;RWQ&__arith;R&__wit;RDE&__varmap;RFG&__ff;R!7,^IH'A+B+B,CK!7,?H'A+B+B,C!4,D+=J,_AY,HLM!2+^HN!2'^1=C#1;!3'`579!4'R!2'`6,`27Z!<'V+_1+='`6'`3'^1'`7,`2,F!2,K+=,F7=!2,K+==&__arith;R&__wit;RDE&__varmap;RFG&__ff;R!7,?H'A+B+B,C!4,D+=I,_AJ,HLMZ#1!2'^\4<!2'`8;&R;R!2'_37:!2+^H!2'Q,F;!2'^1;!1'_27&__sat3;ROR&__sat2;RTU&__sat1;R!2'^0B[%~RP^0&__sat0;R$Ha;RS$~R+^2!3'^3B[#2%Ha;RS%~R+^2!2'Q,F\&__sat1;RW^0&__sat3;R!1#5VQ&__arith;R$__x1;R+=&__wit;RDE&__varmap;R!2,_F+=#2G&__ff;R!8,_GH'A+B+B,C!7,^IH'A+B+B,C^2!7,?H'A+B+B,C!4,D+=^1,_AY,H!1,_I+B!7,^IH'A+B+B,C^2!7,?H'A+B+B,C!4,D+=^1,_A!3,^7+=X4,HLM%__x1;R+=%~R!2+^H!2'Q,F#1!2'^1#1C!2+^H!2'Q,F#2!2'^1#2\!2#1!2'^\7!4'`14,`27!1'_[!3'_U28!3'_\2,`0!3,_52#:#9#8!3'`974:!2'`:7:").
Qed.
Lemma w4s_bit5 : forall (b : byte) (l : list byte),
  Z.land (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn 0 (b :: l))))))) 32 = Z.land (bv_unsigned b) 32.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^K0|30;!1,10!1+01|600;!1,13!1+04|500;!1,16}4!1'_[!3'_U28!3'_\2,`0!3,_52#2#1!4'`14,`279!2'`;7:!2'_Y4;!1,66!2'^@!2'^\1#3=|10;!1,6?!1,63!2'U@A!2'_N;B!2'^@#1=$z;R+=!3+N+=D>!2'^\49!2'`<7#1!2'U@=!2'_NGH!2'`=H@!2'S#1J!2'_:KJ!2'_N#2H%~R+=+=!2'^\4!1'_[!3'_U28!3'_\2,`0!3,_52#3#2!3+N+=#1Ovd!2,K+=OP!2'^0@=!2'^1,F@!2'Q,F=%~RT!2'^1,FH%~RSU!2'Q,F@$Ha;RW$~R+^2!3'^3@=#2!2'Q,FH%Ha;RW%~R+^2Y!3+N+=@,F!2'_NH@!2+^H!2'Q,F\!2'^1\@!2'`EH@vd!2,K+^4!2'^5,F@S!1,9+:!1+;+:!1,<+=!1+>+=!1+@+=!2,_H+=,^M!2,_H+=?!2'I^7,C!4'J#1#3vv!2,K+L,M!3+N+L!2'O#1#3,M!3'P+=,F#2!3+N+=!2'_N#1HI!2'^@!2'^\1#5=!2'^\4!1'_[!3'_U28!3'_\2,`0!3,_52#4#3!3+N+=#2^>vd!2,K+=^>^?!2,E+=,F!2,E+==!7,?^7'A+B+B,C!4,D+=^A,G^B,H&__arith;R&__wit;R^3^4&__varmap;R^5^6&__ff;R^C^:^;T#1!1#2^2!2,E+=@&__sat1;RRV&__sat0;RXZ&__sat1;R^EU&__arith;R&__wit;R^3^4&__varmap;R^5^6&__ff;R!7,^I^7'A+B+B,C^C!7,?^7'A+B+B,C!4,D+=^B,_A!3,^7+=^F7,H^:^;!2+^HT!2'^1=H#1!2'^1,F=!2'Q,FA%~R^I!2'^1,FB$b;R2$l;R!1+;2!6'^P5<$b;R5!3+N+=!2'^@!2'^\4#1=>!6'^P+=CE!6'^P+=!2'^@;=$z;R+=!3+N+=#1>!6'^P+=!2'`<7FE&v;RF+=!6'^R+=!2'^@I=$z;R+=!3+N+=#1!2'^@!2'^\1#4=&H;Rvd!6'^P+=!2'_NLH$z;R+=!3+N+=M#1!8'_M+=+=!1'_N#1!1'_NLHH!8'_M+=N'_N'_N#1L!2,K%~R+=N'_N&heq_v;RQP&__sat2;RRV&__sat1;RXZ&__sat0;R!2'`>H@%~RY%~RW!2'Q,FJ&H;R!2'`?H@%~R!1'_B[!3+N+=H!2'S!2'`@@J\&H0;R!2'`AH@%~RS^0&H1;R!2'`BH@%~R!2'^1@,F!2+^H!2'^1@\!2'Q\,F&H2;R!2'`CH@%~R[!3+N+=J,F&H3;R!2'`DH@%~R[!3+N+=\H&H4;Rvd,^U^1^1vd&H0;R!1#5^2^0&zh;R#2+^2&__sat1;R$a;RW!2#;#1#2%a;RWY&__sat2;R!1#<^2U&__arith;R$__x2;R+=$__x1;R+=&__wit;R^3^4&__varmap;R!4,_P+=!2,_F+=#3#2^5^6&__ff;R!7,?^7'A+B+B,C!4,D+=^8,`F!3,_@+=!3,^6+=^8^9^9,H^:^;%__x2;R+=%__x1;R+=!3+N+=#1!2'_:!2'S#1#2#2!2#1J#@!3+N+=#;!2'_:!2'S#;JJ!2,K+=H!2'_N!2'_:!2'_NKHJH!3'`GKJH^<^<!6'^R+=M$z;R+=!3+N+=D^=!6'^P+=!2'^@#2=$z;R+=!3+N+=#1^=!2'`4#4#3!2'^@M=!5'_X#2==&heq_v;R^@^?^D&heq_v;R^@^?^G!2'_N!2'`<7#2H#1!2'^@G=!5'_XG==&heq_v;RQP^D&heq_v;RQP^G;!3'`H79!4'R!2'`6,`27^H!<'V+_1+='`6'`3'^1'`7,`2,F!2,K+=,F7=!2,K+==&__arith;R&__wit;R^3^4&__varmap;R^5^6&__ff;R!7,?^7'A+B+B,C!4,D+=^A,_A^B,H^:^;^H#1!2'^@C=!5'_X;A=&__arith;R&__wit;R^3^4&__varmap;R^5^6&__ff;R!7,?^7'A+B+B,C!4,D+=^A,G!2,E+=A,H^:^;^I#1&__sat1;R!2'^0@A%~RS^J&__sat0;R$Ha;RW$~R+^2!3'^3@A#2%Ha;RW%~R+^2!2'Q,FB&__sat1;R^E^J&__arith;R&__wit;R^3^4&__varmap;R^5^6&__ff;R!7,^I^7'A+B+B,C^C!7,?^7'A+B+B,C!4,D+=^B,_A!3,^7+=^F4,H^:^;!2+^HT!2'^1=B#1!2'^\4<!1'`I;!3'`J74:!2'`K7:").
Qed.
Lemma rw_cells_retype_nf : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] WR] W' EB ES. unfold rw_cells, cells_at. rewrite EB, ES. auto.
Qed.
Definition FILE_cells4 (fl0 b1 b2 b3 : byte) (j1r : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
  [C4 (le_bytes_to_word [fl0; b1; b2; b3]); CB 28 j1r; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].
Lemma file_cells4 : forall m Fp fl0 b1 b2 b3 j1r WEND WPOS j2 lbfw,
  rw_cells rsegs m Fp (FILE_cells fl0 (b1 :: b2 :: b3 :: j1r) WEND WPOS j2 lbfw) <->
  rw_cells rsegs m Fp (FILE_cells4 fl0 b1 b2 b3 j1r WEND WPOS j2 lbfw).
Proof.
  intros. unfold FILE_cells, FILE_cells4.
  assert (E : cells_bytes [C4 (le_bytes_to_word [fl0; b1; b2; b3]); CB 28 j1r; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw]
              = cells_bytes [CB 1 [fl0]; CB 31 (b1 :: b2 :: b3 :: j1r); C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw]).
  { cbn [cells_bytes cbytes app]. rewrite (le4_of_bytes [fl0; b1; b2; b3]) by reflexivity. reflexivity. }
  split; intros H.
  - pose proof H as [[W _] _]. cbn in W.
    eapply rw_cells_retype_nf; [exact H | cbn; repeat split; try lia; destruct W as (_ & W1 & _ & _ & W2 & _); cbn in W1; try lia; exact W2 | exact E | reflexivity].
  - pose proof H as [[W _] _]. cbn in W.
    eapply rw_cells_retype_nf; [exact H | cbn; repeat split; try lia; destruct W as (_ & W1 & _ & _ & W2 & _); try lia; exact W2 | symmetry; exact E | reflexivity].
Qed.

Lemma flags4_ferr : forall (fl0 b1 b2 b3 : byte), Z.land (bv_unsigned fl0) 32 = 0%Z ->
  Z.land (bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3])) 32 = 0%Z.
Proof.
  intros fl0 b1 b2 b3 H. rewrite StrFun.le_bytes_to_word4.
  pose proof (bv_unsigned_in_range 8 fl0). pose proof (bv_unsigned_in_range 8 b1). pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3).
  unfold bv_modulus in *. cbn -[Z.add Z.mul Z.land bv_unsigned Z.le Z.lt] in *.
  change 32%Z with (2^5)%Z in H |- *. rewrite zb_land_pow2 in H |- * by lia.
  replace ((bv_unsigned fl0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) / 2 ^ 5)%Z
    with (bv_unsigned fl0 / 2^5 + (4 * bv_unsigned b1 + 1024 * bv_unsigned b2 + 262144 * bv_unsigned b3) * 2)%Z
    by (change (2^5)%Z with 32%Z; Z.to_euclidean_division_equations; lia).
  rewrite Z.mod_add by lia. exact H.
Qed.

Lemma land32_sx32 : forall ww : word, Z.land (bv_unsigned (sx32 ww)) 32 = Z.land (bv_unsigned ww) 32.
Proof.
  intros ww. transitivity (Z.land (Z.land (bv_unsigned (sx32 ww)) 63) 32). { rewrite <- Z.land_assoc. reflexivity. }
  change 63%Z with (2^6 - 1)%Z. rewrite land_sx32_mask by lia.
  transitivity (Z.land (Z.land (bv_unsigned ww) (2^6 - 1)) 32). 2:{ rewrite <- Z.land_assoc. reflexivity. }
  change (2^6 - 1)%Z with (Z.ones 6). rewrite Z.land_ones by lia. f_equal.
  pose proof (bv_unsigned_in_range 64 ww). Z.to_euclidean_division_equations. lia.
Qed.
Lemma zx32_le4 : forall fl0 b1 b2 b3 : byte, bv_unsigned (zx32 (le_bytes_to_word [fl0; b1; b2; b3])) = bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3]).
Proof.
  intros. unfold zx32.
  assert (R : (0 <= bv_unsigned (le_bytes_to_word [fl0; b1; b2; b3]) < 2^32)%Z).
  { rewrite StrFun.le_bytes_to_word4. pose proof (bv_unsigned_in_range 8 fl0). pose proof (bv_unsigned_in_range 8 b1).
    pose proof (bv_unsigned_in_range 8 b2). pose proof (bv_unsigned_in_range 8 b3). unfold bv_modulus in *. cbn -[Z.add Z.mul Z.le Z.lt bv_unsigned] in *. lia. }
  rewrite Z.mod_small by lia. apply unsigned_lit. lia.
Qed.

Lemma nf_strings : forall m, mem_inv rsegs m ->
  bytes_at rsegs m 71419 (zb INF_LC) /\ bytes_at rsegs m 78834 (zb NAN_LC)
  /\ bytes_at rsegs m 73921 (zb INF_UC) /\ bytes_at rsegs m 78076 (zb NAN_UC).
Proof.
  intros m MI. exact (conj (nfs_inf_u8ro m MI) (conj (nfs_nan_u8ro m MI) (conj (nfs_INF_u8ro m MI) (nfs_NAN_u8ro m MI)))).
Qed.

Ltac cur_reg R k :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
  eval cbv beta iota delta [tget] in (match tget p R with Some v => v | None => Z_to_bv 64 0 end).


Section FmtFp.
  Variables (ra sp gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (ya yb fw : word)      (* [comment removed for export] *)
            (F : bvmap 5 word) (m0 : word -> option byte)
            (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
            (w p fl t : Z) (o0 o1 : list Z) (ret : Z).
  Definition yv : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S30|600;!1,10|10;!2'S!2'^\1/ya;!2'`@!2'U!1,62!1,60!2'^\1/yb;").
  Definition Fp : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'^\!1,1|600;/fw;").
  Definition usp : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'^\!1,1|600;/sp;").

  Hypothesis HM : fmt_fp_nf o0 yv w p fl t = Some (o1, ret).
  Hypothesis SPLO : (5152 <= bv_unsigned sp)%Z.
  Hypothesis SPHI : (bv_unsigned sp < 2^63)%Z.
  Hypothesis GLO : (1036936 <= bv_unsigned sp - 4640)%Z.   (* [comment removed for export] *)
  Hypothesis AF : (bv_unsigned sp <= Fp)%Z.
  Hypothesis AB : (bv_unsigned sp <= B)%Z.
  Hypothesis Hw : (0 <= w <= 1)%Z.
  Hypothesis Hp : (-2^31 <= p < 2^20)%Z.   (* [comment removed for export] *)
  Hypothesis Hfl : (0 <= fl < 2^32)%Z.
  Hypothesis Ht : (0 <= t < 256)%Z.
  Hypothesis ROOM : (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z.
  Hypothesis J256 : (length junk0 < 256)%nat.
  (* [comment removed for export] *)
  Definition ctx_all : unit :=
    let _ := (ra, sp, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, ya, yb, fw, F, m0,
              fl0, j1, j2, lbfw, B, junk0, canary, w, p, fl, t, o0, o1, ret) in tt.

  Definition Wfp : list (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!2+`L+=+=!2'^\!1,1|600;/sp;!3,_50!4,`M+=+=!2'_:1!1,6|<220;1!3,_50!4,`M+=+=!2'S/B;!1'T!2'^8+=/o0;!2'S/B;!1'T!2'^8+=/o1;!3,_50!4,`M+=+=!2'S'`N!1,6|508;!2'S'`N!1,6|510;!1,90").

  Definition fmt_fp_post (m : word -> option byte) : machine_state -> Prop := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S;0!1,1|600;!1+00|30;!1+0!1,12%~R1!1+23|21;!1,15!2'`Q61|500;!1+0!1,18!2'^\0/sp;$m;R4$ms';R+`O!2+`P1$t0;R1!2+`P1$t1;R1!2+`P1$t2;R1!2+`P1$a1;R1!2+`P1$a2;R1!2+`P1$a3;R1!2+`P1$a4;R1!2+`P1$a5;R1!2+`P1$a6;R1!2+`P1$a7;R1!2+`P1$t3;R1!2+`P1$t4;R1!2+`P1$t5;R1!2+`P1$t6;R1!2+`P7$Ft;R7!2+`P9$fc';R9!2+`P4$m';R4!2+^H!3+N+`O#B!7'`R!O'`S/ra;/sp;/gp;/tp;#A#@#?/s0e;/s1e;!2'_Y0/ret;#>#=#<#;#:#9#8/s2e;/s3e;/s4e;/s5e;/s6e;/s7e;/s8e;/s9e;/s10e;/s11e;#7#6#5#4#3!1'`T/ra;#2!1,_I1#1!1'`U'4!2+^H!3'`V'`W#C#1!2+^H!3'`X'4#C#1!2+^H!2'3'4#1!2+^H!1'`Y#2!2+^H!4'`Z'4#1!2'_::!1,6|<220;:!2+^H!9'`[#1'`N/fl0;/j1;/j2;/lbfw;/B;!1'7/o1;!3'_\3!2'`\!2'^8+=/o1;!2'^8+=/o0;/junk0;!2+^H!2'a0#1/canary;%k;R!1+06%~R!1'_B!3+N+=!2'^\6#1!1,6|32;!3+N1!2'a1#5#2!2'a1/F;#2").

  (* [comment removed for export] *)
  Definition hi_cells (pad256 : list byte) : list cell :=
    [CB 256 pad256; C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) (pad256 : list byte) : Prop :=
    mem_inv rsegs m /\ munch Wfp m0 m /\ wmono rsegs m0 m
    /\ rw_cells rsegs m (bv_unsigned sp + -368) (hi_cells pad256)
    /\ stk rsegs m (bv_unsigned sp - 4640) (bv_unsigned sp + -1056)
    /\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let GOT := fresh "GOT" in let SSP := fresh "SSP" in
    destruct H as (MI & MU & WM & FRhi & ST & GOT & SSP); unfold Wfp in MU; unfold hi_cells in FRhi; unfold got_ssp, ssp_guard in GOT, SSP.
  Ltac mk_finv := unfold finv, Wfp, hi_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | idtac]|]; split; hyp.

  Ltac dest_wfile H := let FC := fresh "FC" in let BUF := fresh "BUF" in let FLG := fresh "FLG" in let LBF := fresh "LBF" in
    let Bpos := fresh "Bpos" in let Bhi := fresh "Bhi" in let SEPfb := fresh "SEPfb" in
    destruct H as (FC & BUF & FLG & LBF & Bpos & Bhi & SEPfb); unfold FILE_cells in FC; cbv delta [F_memcpy_u5.rsegs] in FC, BUF; fold rsegs in FC, BUF.
  Ltac mk_wfile := unfold wfile, FILE_cells; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [lia|]; split; lia.

  Ltac prune := try clear HM.
  (* [comment removed for export] *)
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  (* [comment removed for export] *)
  Ltac clear_fat :=
    repeat match goal with
           | H : evt _ _ _ |- _ => clear H
           | H : forall _, _ |- _ => clear H
           | H : _ = Some _ |- _ => clear H
           | H : Some _ = _ |- _ => clear H
           | H : u32arr _ _ _ _ |- _ => clear H
           | H : rw_cells _ _ _ _ |- _ => clear H
           | H : wfile _ _ _ _ _ _ _ _ _ |- _ => clear H
           end.
  (* [comment removed for export] *)
  Ltac clear_logic :=
    repeat match goal with
           | H : _ \/ _ |- _ => clear H
           | H : _ <-> _ |- _ => clear H
           | H : ~ _ |- _ => clear H
           | H : zboxed _ _ |- _ => clear H
           end.
  Local Ltac slia ::= first [ exact I | solve [clear_fat; clear_logic; lia] | solve [clear_fat; lia] | lia | split; [lia|exact I] ].

  Notation POST := (fmt_fp_post m0).
  Notation SPv := (Z_to_bv 64 (bv_unsigned sp + -1056)).
  Notation S0v := (Z_to_bv 64 (bv_unsigned sp)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_bec :
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) fc pad jk80 jk8 jk3 jk12 jk37 jbig
      (y1 prefix pl plz pfx : Z),
    finv m pad -> frm0 fc ->
    rw_cells rsegs m (bv_unsigned sp + -544)
      [C8 (Z_to_bv 64 0); CB 80 jk80; C8 (Z_to_bv 64 plz); C8 (Z_to_bv 64 pfx); C8 (Z_to_bv 64 pl); CB 8 jk8] ->
    rw_cells rsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 jk3] ->
    rw_cells rsegs m (bv_unsigned sp + -417) [CB 12 jk12] ->
    rw_cells rsegs m (bv_unsigned sp + -405) [CB 37 jk37] ->
    rw_cells rsegs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    (0 <= prefix <= 6)%Z -> (0 <= pl <= 1)%Z -> plz = Z.b2z (pl =? 0)%Z -> pfx = (68786 + prefix)%Z ->
    ffp_sign yv fl = (y1, prefix, pl) ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (-5)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) (Z_to_bv 64 t) (Z_to_bv 64 1036928) (Z_to_bv 64 512) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) x28 x29 x30 x31)
          F (Z_to_bv 64 0xb4a3c) fc None m (seg_rom rsegs)).
  Proof using AB AF GLO HM Hfl Ht Hw J256 ROOM SPHI SPLO.
    (* [Hp] is not in this lemma's [Proof using] list: keep [lia] from reading it. *)
    clear Hp.
    intros until pfx. intros FI FRM FRs E2 EB BF BIGb WF Hpre Hpl Hplz Hpfx HS. dest_finv FI. dest_wfile WF. pose_word_ranges.

    pose proof HM as HM'. unfold fmt_fp_nf in HM'. rewrite HS in HM'. cbv beta iota in HM'.
    zs. zs. zs. call fpclassifyl_callv. 1:{ hyp. }
    zs. zs. if_cases Kc; zify_cond Kc; rewrite signed_of_Z in Kc by (pose proof (fpclassifyl_range y1); lia).
    2:{ exfalso. rewrite (proj2 (Z.leb_gt _ _)) in HM' by lia. discriminate HM'. }
    rewrite (proj2 (Z.leb_le _ _) Kc) in HM'. rewrite (proj2 (Z.leb_le 0 w) (proj1 Hw)), (proj2 (Z.leb_le w 1) (proj2 Hw)) in HM'. cbn [andb] in HM'.
    injection HM' as Eo1 Eret. try clear HM'.
    assert (EL : (Z.of_nat (length o1) = Z.of_nat (length o0) + pl + 3)%Z) by (rewrite <- Eo1; try unfold out; rewrite !app_length, nf_str_length, (zsub_length PREFIX_STR) by (cbn; lia); lia).
    assert (LJ1 : length j1 = 31%nat) by (destruct FC as [[W _] _]; cbn in W; tauto).
    assert (EJ : exists b1 b2 b3 j1r, j1 = b1 :: b2 :: b3 :: j1r)
      by (destruct j1 as [|b1 [|b2 [|b3 j1r]]]; try (cbn in LJ1; discriminate LJ1); exists b1, b2, b3, j1r; reflexivity).
    destruct EJ as (b1 & b2 & b3 & j1r & EJ).
    set (c0 := zb o0) in *. assert (Lc0 : length c0 = length o0) by (subst c0; apply zb_length).
    set (pbs := zb (zsub PREFIX_STR prefix pl)) in *.
    assert (Lpx : length (zsub PREFIX_STR prefix pl) = Z.to_nat pl) by (apply zsub_length; cbn; lia).
    assert (Lpbs : length pbs = Z.to_nat pl) by (subst pbs; rewrite zb_length; exact Lpx).
    set (sbs := zb (nf_str y1 t)) in *.
    assert (Lsbs : length sbs = 3%nat) by (subst sbs; rewrite zb_length; apply nf_str_length).

    zs. zs. zs. zs. zs. zs. call letf2_callv. 1:{ hyp. }

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
    assert (J640 : forall (t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v : word) (S : Z),
      (forall mq, mem_inv rsegs mq -> bytes_at rsegs mq S sbs) -> (0 <= S)%Z -> (S + 3 <= 1036936)%Z ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0xb4b24) SPv gp tp t0v t1v t2v sp (Z_to_bv 64 (3 + pl)) a0v a1v a2v a3v a4v a5v a6v a7v
                 (Z_to_bv 64 p) (Z_to_bv 64 S) (Z_to_bv 64 1036928) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) t3v t4v t5v t6v)
            F (Z_to_bv 64 0xb4c84) fc None mcur (seg_rom rsegs)))
    end.
    { intros t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v S SBYf RS0 RS1.

      rewrite EJ in FC. apply (proj1 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. unfold FILE_cells4 in FC.
      zs. zs. rewrite zx32_le4, (flags4_ferr fl0 b1 b2 b3 FLG). zs. if_cases Kfe; zify_cond Kfe; [exfalso; lia|].

      zs. rewrite Hpfx. zs. zs.
      match goal with MIq : mem_inv _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (bytes_at_slice _ _ _ (Z.to_nat prefix) (Z.to_nat pl) (prefix_u8ro _ MIq) ltac:(rewrite zb_length; cbn; lia)) as SRC end.
      rewrite Z2Nat.id in SRC by lia. rewrite <- zb_zsub in SRC by lia. change (zb (zsub PREFIX_STR prefix pl)) with pbs in SRC.
      destruct (stk_split rsegs _ _ (bv_unsigned sp + -1056 - 64) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      apply (proj2 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. rewrite <- EJ in FC.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb
          | exact SRC
          | rewrite Lpbs, Z2Nat.id by lia; reflexivity
          | rewrite Lpbs; lia
          | exact STf
          | first [hyp | assumption]   (* same three-way [rsegs] shadow as :337 *)
          | lia | lia | lia | lia | lia | lia | lia | lia | lia ]
        | clear FC BUF STf; post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 64)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge rsegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      try clear SRC. try clear POST. clear FLG LBF Bpos Bhi SEPfb.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ (c0 ++ pbs) _ |- _ => dest_wfile X end.
      assert (LA : length (c0 ++ pbs) = (length c0 + Z.to_nat pl)%nat) by (rewrite app_length, Lpbs; reflexivity).
      assert (LK : length (skipn (length pbs) junk0) = (length junk0 - Z.to_nat pl)%nat) by (rewrite length_skipn, Lpbs; reflexivity).

      rewrite EJ in FC. apply (proj1 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. unfold FILE_cells4 in FC.
      zs. zs. rewrite land32_sx32, (flags4_ferr fl0 b1 b2 b3 FLG). zs. if_cases Kfe2; zify_cond Kfe2; [exfalso; lia|].

      zs. zs. zs.
      match goal with MIq : mem_inv _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (SBYf _ MIq) as SRC2 end.
      destruct (stk_split rsegs _ _ (bv_unsigned sp + -1056 - 64) _ ST ltac:(lia)) as [STlo STf]. clear ST.
      apply (proj2 (file_cells4 _ _ _ _ _ _ _ _ _ _ _)) in FC. rewrite <- EJ in FC.
      zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply fwritex_callR;
          [ exact FC | exact BUF | exact FLG | exact LBF | exact Bpos | exact Bhi | exact SEPfb
          | exact SRC2
          | rewrite Lsbs; reflexivity
          | rewrite Lsbs; lia
          | exact STf
          (* The U/ twin of CJ/F10/F_fmt_fp_nf.v:333, same three-way [rsegs] shadow:
             F_memset_u5 (:12), F_memcpy_u5 (:13) and F_fmt_fp_calls_u5 (:24) each
             declare their own [Definition rsegs], so [hyp]'s [constr_eq] rejects a
             convertible-but-not-syntactically-equal hypothesis.  [assumption]
             unifies up to conversion. *)
          | first [hyp | assumption]
          | lia | lia | lia | lia | lia | lia | lia | lia | lia ]
        | clear FC BUF STf; post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -1056 - 64)%Z _ |- _ =>
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge rsegs mm _ _ _ STlo X ltac:(lia)) as ST end; clear STlo X end.
      try clear SRC2. try clear POST.
      lazymatch goal with X : wfile _ _ _ _ _ _ _ ((c0 ++ pbs) ++ sbs) _ |- _ => rename X into WF3 end.

      zs. zs. zs. zs.

      lazymatch goal with |- evt _ _ (MS ?R ?Fq _ ?fcq _ ?mq _) =>
      let y5 := cur_reg R 5%Z in let y6 := cur_reg R 6%Z in let y7 := cur_reg R 7%Z in
      let y10 := cur_reg R 10%Z in let y11 := cur_reg R 11%Z in let y12 := cur_reg R 12%Z in let y13 := cur_reg R 13%Z in
      let y14 := cur_reg R 14%Z in let y15 := cur_reg R 15%Z in let y16 := cur_reg R 16%Z in let y17 := cur_reg R 17%Z in
      let y18 := cur_reg R 18%Z in let y19 := cur_reg R 19%Z in
      let y28 := cur_reg R 28%Z in let y29 := cur_reg R 29%Z in let y30 := cur_reg R 30%Z in let y31 := cur_reg R 31%Z in
      assert (J6fc : evt rsegs POST
        (MS (mkR (Z_to_bv 64 0xb4cbc) SPv gp tp y5 y6 y7 sp (Z_to_bv 64 (3 + pl)) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
                 (Z_to_bv 64 1036928) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) y28 y29 y30 y31)
            Fq (Z_to_bv 64 0xb4d40) fcq None mq (seg_rom rsegs)))
      end.
      { zs. if_cases Klt; zify_cond Klt; [exfalso; lia|].
        zs. zs. rewrite Eret. zs. zs. zs. if_cases Kcan; zify_cond Kcan; try (exfalso; clear -Kcan; apply Kcan; reflexivity).
        do 15 zs.

        release_frame BIGb ST (bv_unsigned sp + -544)%Z.
        release_frame FRs ST (bv_unsigned sp + -424)%Z.
        release_frame E2 ST (bv_unsigned sp + -417)%Z.
        release_frame EB ST (bv_unsigned sp + -405)%Z.
        release_frame BF ST (bv_unsigned sp + -368)%Z.
        release_frame FRhi ST (bv_unsigned sp)%Z.
        zs.
        apply evt_done. unfold fmt_fp_post.
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [ ms_eq | ].
        split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [hyp|]. split; [exact ST|].
        split. { replace (zb o1) with ((c0 ++ pbs) ++ sbs) by (subst c0 pbs sbs; rewrite <- Eo1; try unfold out; rewrite !zb_app, ?app_assoc; reflexivity).
                 replace (skipn (length o1 - length o0) junk0) with (skipn (length sbs) (skipn (length pbs) junk0)) by (rewrite skipn_skipn; f_equal; lia).
                 exact WF3. }
        split; [unfold ssp_cells, got_ssp, ssp_guard; split; hyp | intros k Hk; reflexivity ]. }
      if_cases Kzp; zify_cond Kzp; [ exact J6fc |].

      zs. if_cases Kw2; zify_cond Kw2; first [exact J6fc | exfalso; lia]. }

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
    assert (J5c0 : forall (t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v : word) (S : Z),
      (forall mq, mem_inv rsegs mq -> bytes_at rsegs mq S sbs) -> (0 <= S)%Z -> (S + 3 <= 1036936)%Z ->
      evt rsegs POST
        (MS (mkR (Z_to_bv 64 0xb4b24) SPv gp tp t0v t1v t2v sp (Z_to_bv 64 (Z.land t 32)) a0v a1v a2v a3v a4v a5v a6v a7v
                 (Z_to_bv 64 p) (Z_to_bv 64 S) (Z_to_bv 64 1036928) (Z_to_bv 64 pl) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 y1)) (Z_to_bv 64 (lo64 y1)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) t3v t4v t5v t6v)
            F (Z_to_bv 64 0xb4c04) fc None mcur (seg_rom rsegs)))
    end.
    { intros t0v t1v t2v a0v a1v a2v a3v a4v a5v a6v a7v t3v t4v t5v t6v S SBYf RS0 RS1.
      zs. zs. try replace (bv_swrap 32 (pl + 3))%Z with (3 + pl)%Z by (rewrite swrap32_eq; mlia). replace (Z_to_bv 64 (pl + 3)) with (Z_to_bv 64 (3 + pl)) by (f_equal; lia).
      zs. if_cases Kla; zify_cond Kla; [ eapply J640; [exact SBYf | lia | lia] |].
      zs. if_cases Kw1; zify_cond Kw1; first [ eapply J640; [exact SBYf | lia | lia] | exfalso; lia ]. }

    zs. if_cases Kt; zify_cond Kt.
    -
      zs. zs. zs. zs. zs. zs. if_cases Kn; zify_cond Kn;
        [ | zs ];
        first [ apply (proj1 (F_frexpl_u5.f128_le_land64_zero _ _)) in Kn
              | let K := fresh in assert (K : f128_le y1 y1 <> 0%Z) by (intros E; apply Kn; apply (proj2 (F_frexpl_u5.f128_le_land64_zero _ _)); exact E); clear Kn; rename K into Kn ];
        (eapply J5c0; [ intros mq MIq; subst sbs; unfold nf_str; rewrite Kt;
                        first [ rewrite Kn | replace (f128_le y1 y1 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kn)) ];
                        cbn [negb Z.eqb]; pose proof (nf_strings mq MIq) as NS;
                        first [ exact (proj1 NS) | exact (proj1 (proj2 NS)) | exact (proj1 (proj2 (proj2 NS))) | exact (proj2 (proj2 (proj2 NS))) ]
                      | lia | lia ]).
    -
      zs. zs. zs. zs. zs. zs. if_cases Kn; zify_cond Kn; zs;
        first [ apply (proj1 (F_frexpl_u5.f128_le_land64_zero _ _)) in Kn
              | let K := fresh in assert (K : f128_le y1 y1 <> 0%Z) by (intros E; apply Kn; apply (proj2 (F_frexpl_u5.f128_le_land64_zero _ _)); exact E); clear Kn; rename K into Kn ];
        (eapply J5c0; [ intros mq MIq; subst sbs; unfold nf_str; replace (Z.land t 32 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kt));
                        first [ rewrite Kn | replace (f128_le y1 y1 =? 0)%Z with false by (symmetry; exact (proj2 (Z.eqb_neq _ _) Kn)) ];
                        cbn [negb Z.eqb]; pose proof (nf_strings mq MIq) as NS;
                        first [ exact (proj1 NS) | exact (proj1 (proj2 NS)) | exact (proj1 (proj2 (proj2 NS))) | exact (proj2 (proj2 (proj2 NS))) ]
                      | lia | lia ]).
  Qed.

  Lemma L_b84 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) fc pad jk jk1 jk2 jk3 jbig,
    finv m pad -> frm0 fc ->
    rw_cells rsegs m (bv_unsigned sp + -544) [C8 (Z_to_bv 64 0); CB 112 jk] ->
    rw_cells rsegs m (bv_unsigned sp + -424) [C4 (Z_to_bv 64 0); CB 3 jk1] ->
    rw_cells rsegs m (bv_unsigned sp + -417) [CB 12 jk2] ->
    rw_cells rsegs m (bv_unsigned sp + -405) [CB 37 jk3] ->
    rw_cells rsegs m (bv_unsigned sp + -1056) [CB 512 jbig] ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 sp (Z_to_bv 64 (-5)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 p) (Z_to_bv 64 t) (Z_to_bv 64 1036928) (Z_to_bv 64 512) SPv (Z_to_bv 64 w) (Z_to_bv 64 (hi64 yv)) (Z_to_bv 64 (lo64 yv)) (Z_to_bv 64 Fp) (Z_to_bv 64 fl) x28 x29 x30 x31)
          F (Z_to_bv 64 0xb49d4) fc None m (seg_rom rsegs)).
  Proof using AB AF GLO HM Hfl Ht Hw J256 ROOM SPHI SPLO.
    clear Hp.
    intros until jbig. intros FI FRM FRs E2 EB BF BIGb WF. dest_finv FI. dest_wfile WF. pose_word_ranges.
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).
    pose proof (lo64_range yv) as Rylo. pose proof (hi64_range yv) as Ryhi.
    zs. zs. zs. call signbitl_callv. 1:{ hyp. }
    zs. if_cases Ks; zify_cond Ks; rewrite land_W64_small in Ks by (pose proof (signbitl_range yv); lia).
    -   zs. zs. zs. zs. if_cases Km; zify_cond Km; rewrite shl52_land64 in Km by lia.
      +
        zs. zs. zs. zs. zs.
        eapply L_bec with (prefix := 3%Z) (pl := 1%Z); [ mk_finv | hyp | hyp | hyp | hyp | hyp | hyp | mk_wfile | lia | lia | reflexivity | reflexivity | ].
        unfold ffp_sign. cbv beta delta [MARK_POS]. rewrite land_bit11. decide_tests_b. reflexivity.
      + zs. rewrite land_bit0. zs. zs. if_cases Kp; zify_cond Kp.
        *
          rewrite Kp in FRs |- *. zs. zs. zs. zs. change (Z.b2z (0 <? 1)) with 1%Z. zs. zs.
          eapply L_bec with (prefix := 1%Z) (pl := 0%Z); [ mk_finv | hyp | hyp | hyp | hyp | hyp | hyp | mk_wfile | lia | lia | reflexivity | reflexivity | ].
          unfold ffp_sign. cbv beta delta [MARK_POS PAD_POS]. rewrite land_bit11, land_bit0. decide_tests_b. reflexivity.
        *
          replace (fl mod 2)%Z with 1%Z in FRs |- * by lia.
          zs. zs. zs. zs. zs. change (Z.b2z (1 <? 1)) with 0%Z. zs. zs.
          eapply L_bec with (prefix := 6%Z) (pl := 1%Z); [ mk_finv | hyp | hyp | hyp | hyp | hyp | hyp | mk_wfile | lia | lia | reflexivity | reflexivity | ].
          unfold ffp_sign. cbv beta delta [MARK_POS PAD_POS]. rewrite land_bit11, land_bit0. decide_tests_b. reflexivity.
    -
      zs. zs. zs. zs. zs. zs. zs. rewrite <- hi64_flip_sign.
      replace (Z_to_bv 64 (lo64 yv)) with (Z_to_bv 64 (lo64 (Z.lxor yv F128_SIGNBIT))) by (rewrite lo64_flip_sign; reflexivity).
      zs. zs. zs.
      eapply L_bec with (prefix := 0%Z) (pl := 1%Z); [ mk_finv | hyp | hyp | hyp | hyp | hyp | hyp | mk_wfile | lia | lia | reflexivity | reflexivity | ].
      unfold ffp_sign. decide_tests_b. reflexivity.
  Qed.

  Lemma ffp_entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
    stk rsegs m0 (bv_unsigned sp - 4640) (bv_unsigned sp) ->
    mem_inv rsegs m0 ->
    frm0 fc ->
    wfile m0 Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m0 canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e fw ya yb a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
          F (Z_to_bv 64 0xb4924) fc None m0 (seg_rom rsegs)).
  Proof using AB AF GLO HM Hfl Ht Hw J256 ROOM SPHI SPLO.
    clear Hp.
    intros until fc. intros ST MI FRM WF (GOT & SSP) -> -> -> -> Hps. dest_wfile WF.
    cbv delta [F_memcpy_u5.rsegs] in GOT, SSP. fold rsegs in GOT, SSP.
    pose proof (munch_refl Wfp m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold Wfp in MU.
    pose_word_ranges. unfold got_ssp, ssp_guard in *.
    assert (Rya : (0 <= bv_unsigned ya < 2^64)%Z) by apply (zr_word ya).
    assert (Ryb : (0 <= bv_unsigned yb < 2^64)%Z) by apply (zr_word yb).
    assert (Rfw : (0 <= Fp < 2^64)%Z) by apply (zr_word fw).

    replace fw with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
    replace ya with (Z_to_bv 64 (lo64 yv)) by (unfold yv; rewrite lo64_words by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
    replace yb with (Z_to_bv 64 (hi64 yv)) by (unfold yv; rewrite hi64_words by lia; rewrite Z_to_bv_bv_unsigned; reflexivity).
    carve_frame 544%nat ST.
    zstep. zstep0. do 13 zstep. zstep.

    apply (rw_cells_split_CB rsegs _ _ [_] 432 _ _ [112; 4; 3; 12; 37; 256; 8]%nat) in FR; [ | reflexivity ].
    cbn [mk_CB_cells app] in FR.
    name_cb 112%nat FR. name_cb 4%nat FR. name_cb 3%nat FR. name_cb 12%nat FR. name_cb 37%nat FR. name_cb 256%nat FR. name_cb 8%nat FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [FRs FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [E2 FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [EB FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR. destruct FR as [BF FRhi]. cbn [cells_size csize Nat.add] in FRhi.
    match type of E2 with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -424)%Z in E2 by lia end.
    match type of EB with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -417)%Z in EB by lia end.
    match type of BF with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -405)%Z in BF by lia end.
    match type of FRhi with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -368)%Z in FRhi by lia end.
    do 7 zstep.
    zstep. zstep.   zstep.   zstep.
    zstep.
    zstep. if_cases Kps; zify_cond Kps.
    { exfalso. apply Hps. exact Kps. }
    zstep. zstep. zstep.
    do 4 zstep. replace (bv_unsigned sp + -544 - 512)%Z with (bv_unsigned sp + -1056)%Z by lia.
    zstep. zstep. replace (bv_unsigned sp + -544 - 4096)%Z with (bv_unsigned sp + -4640)%Z by lia.

    destruct (stk_split rsegs _ _ (bv_unsigned sp + -4632) _ ST ltac:(lia)) as [ST1 ST2]. clear ST.
    destruct (stk_carve rsegs _ _ _ 8 ST1 ltac:(cbn; lia)) as [_ [jp PROBE]]. clear ST1.
    match type of PROBE with rw_cells _ _ ?A _ => replace A with (bv_unsigned sp + -4640)%Z in PROBE by lia end.
    zstep0.
    pose proof (stk_of_rw_cells rsegs _ _ _ PROBE) as ST1.
    match type of ST1 with stk _ _ _ ?A => replace A with (bv_unsigned sp + -4632)%Z in ST1 by (cbn; lia) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (stk_merge rsegs mm _ _ _ ST1 ST2 ltac:(lia)) as ST end. clear ST1 ST2 PROBE.
    zstep. if_cases Kpr; zify_cond Kpr.
    { exfalso. revert Kpr. rewrite !signed_of_Z by lia. lia. }
    zstep.
    carve_frame 512%nat ST. rename FR into BIGb.
    zstep0.
    replace (bv_unsigned sp + -4640)%Z with (bv_unsigned sp - 4640)%Z in ST by lia.
    eapply L_b84; [ | hyp | exact FRs | exact E2 | exact EB | exact BF | exact BIGb | mk_wfile ].
    mk_finv.
  Qed.

End FmtFp.
End NF.

(* [comment removed for export] *)
Definition fmt_fp_nf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (junk0 : list byte) (canary : word)
         (w p fl t : Z) (o0 o1 : list Z) (ret : Z),
    let y := (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z in
    let Fp := bv_unsigned a0 in
    fmt_fp_nf o0 y w p fl t = Some (o1, ret) ->
    (5152 <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^63)%Z -> (1036936 <= bv_unsigned sp - F_fmt_fp_u5.FMT_FP_DEPTH)%Z ->
    (bv_unsigned sp <= Fp)%Z -> (bv_unsigned sp <= B)%Z ->
    (0 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z ->
    (Z.of_nat (length o1) <= Z.of_nat (length o0) + Z.of_nat (length junk0))%Z -> (length junk0 < 256)%nat ->
    stk rsegs m (bv_unsigned sp - F_fmt_fp_u5.FMT_FP_DEPTH) (bv_unsigned sp) ->
    mem_inv rsegs m ->
    frm0 fc ->
    wfile m Fp fl0 j1 j2 lbfw B (zb o0) junk0 ->
    ssp_cells m canary ->
    a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t -> bv_unsigned a7 <> 5%Z ->
    evt rsegs (F_fmt_fp_u5.fmt_fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp fl0 j1 j2 lbfw B o0 o1 junk0 canary ret m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb4924) fc None m (seg_rom rsegs)).

Lemma fmt_fp_nf_spec : fmt_fp_nf_stmt.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SV0|600;!1,10!1+01|21;|500;|30;!1+0!1,15!1+;6!1+;+=!2+`L8+=|10;!1,6:!3+N!1+29!6'aE#3!2'S!2'^\1#V!2'`@!2'U;!1,60!2'^\1#U#7#6#5#4!2,aF9!4,`M8+=#2#1!2'Q!1,6|<420;!2'^\1#^3!2'^1!2'^\1#^4!2'U;!1,6|51f;!2'Q!1,6|C7d288;!2'_:!2'^\1#^5'gF!2'Q!2'^\1#^6!2'^\1#[!2'Q!2'^\1#^7#?!2'Q,F#=!2+^HB!2'Q#=!1,6,^M|4f;|44;!2+^H!2'Q!1'bY!2'U;!1,6D#=!2'^1#=!2'U;!1,6E!2+^HB!2'^1#=!2'U;!1,64!2+^HB!2'^1#=!1,6|800;!2'Q!1'T!2'^8+=#<!2'S!1'T!2'^8+=#=!1'T!2'^86#C!2'bI!2'^86#D}bO!2'^\1#^>!4'`Z'4#K!2'_:K'gFK!2'3'4#L!1'`Y#N!9'`[#N!2'^\1#^9#M#L#K#J#I!1'7#B#H!2'a0#O#H!3+N2#^8!2'_Y1#H!1'_B!3+N+=!2'^\1#^8!1,63!M'gI#^I#^H#^G#^F#^B#^A#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#W!2'^\1#^@#T#S#R#Q#P#I#H#O#N#G#U!7'`R!O'`S#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#[#Z#Y#X#W!2'_Y1!1,6|C34924;#V!1,_I2#U!1'`U'4!3'a>'4STvd$ra;R2$sp;R2$gp;R2$tp;R2$t0;R2$t1;R2$t2;R2$s0;R2$s1;R2$a0;R2$a1;R2$a2;R2$a3;R2$a4;R2$a5;R2$a6;R2$a7;R2$s2;R2$s3;R2$s4;R2$s5;R2$s6;R2$s7;R2$s8;R2$s9;R2$s10;R2$s11;R2$t3;R2$t4;R2$t5;R2$t6;R2$F;R!2'`Q!1,132$fc;R!1+0!1,14$m;R%~R2!1+26$fl0;R6$j1;R7$j2;R7$lbfw;R2$B;R+=$junk0;R7$canary;R2$w;R+=$p;R+=$fl;R+=$t;R+=$o0;R8$o1;R8$ret;R+=vd$HM;R<$SPLO;R=$SPHI;R>$GLO;R?$AF;R@$AB;RA$Hw;RC$Hp;RF$Hfl;RG$Ht;RH$ROOM;RI$J256;RJ$ST;RL$MI;RM$FRM;RN$WF;RO$SSP;RP$Ha3;RQ$Ha4;RQ$Ha5;RQ$Ha6;RQ$Hps;RRvd!6'gG'4!M'gH#^I#^H#^G#^F#^B#^A#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#^@#W#T#S#R#Q#P#O#N#I#H#G#UST!^H'gJ#^I#^H#^G#^F#^B#^A#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#^?#^>#^@#W#U#T#S#R#Q#P#O#N#M#L#K#J#I#H#G#F#E#D#C#B#A#@#>#=#<#;#^E#^D#^C#^=#^<#^;#^:#^9#[#Z#Y#X#V#:#9#8#7#6#5#4#3#2#1$ms';R+`O$H;R!N'gH#^J#^I#^H#^G#^C#^B#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0#^A#X#U#T#S#R#Q#P#O#J#I#H#V#1#1U%~R<%~R=%~R>%~R?%~R@%~RA%~RC%~RF%~RG%~RH%~RI%~RJ%~RL%~RM%~RN%~RO%~RP%~RQ%~RQ%~RQ%~RQ%~RRU'gK").
Qed.

(* [comment removed for export] *)
Definition fmt_fp_facts' (y fl p t : Z) : Prop := nonfinite y fl \/ F_fmt_fp_u5.fmt_fp_facts y fl p t.

Definition fmt_fp'_stmt : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 0 "SC0|600;!1,10!1+01|21;|500;|30;!1+0!1,15!1+;6!1+;+=|10;!1,69!2+`L8+=|4f;!2'Q!1'bY!2'U:!1,6<#@|44;!2'Q,F#@!1,64!2'^\1#^B!3+N2#^<!2'_Y1#L%ra;R2%sp;R2%gp;R2%tp;R2%t0;R2%t1;R2%t2;R2%s0;R2%s1;R2%a0;R2%a1;R2%a2;R2%a3;R2%a4;R2%a5;R2%a6;R2%a7;R2%s2;R2%s3;R2%s4;R2%s5;R2%s6;R2%s7;R2%s8;R2%s9;R2%s10;R2%s11;R2%t3;R2%t4;R2%t5;R2%t6;R2%F;R!2'`Q!1,132%fc;R!1+0!1,14%m;R%~R2!1+26%fl0;R6%j1;R7%j2;R7%lbfw;R2%B;R+=%junk0;R7%canary;R2%w;R+=%p;R+=%fl;R+=%t;R+=%o0;R8%o1;R8%ret;R+=&y;R!2'S!2'^\1#V!2'`@!2'U:!1,60!2'^\1#U+=&Fp;R!2'^\1#X+=%~R!3+N!1+2;!6'gL#5#2#9#8#7#6!2,aF;!4,`M8+=#4#3%~R!4'gM#3#8#9#7%~R!2'Q!1,6|<420;!2'^\1#^6%~R!2'^1!2'^\1#^7!2'U:!1,6|51f;%~R!2'Q!1,6|C7d288;!2'_:!2'^\1#^8'gF%~R!2'Q!2'^\1#^9#6%~R!2'Q!2'^\1#^:#B%~R!2+^H=!2'Q#@!1,6,^M%~R!2+^H=!2'^1#@!2'U:!1,6>%~R!2+^H?!2'^1#@!2'U:@%~R!2+^H?!2'^1#@!1,6|800;%~R!1'_B!3+N+=!2'^Z#A@!1,6|621;%~R!2'Q!1'T!2'^8+=#@!2'S!1'T!2'^8+=#A!1'T!2'^86#G%~R!2'bI!2'^86#H}bO%~R!4'`Z'4#O!2'_:A'gFA%~R!2'3'4#P%~R!1'`Y#R%~R!9'`[#R#B#Q#P#O#N#M!1'7#F#L%~R!2'a0#S#L%~RB%~RB%~RB%~RB%~R!1'_B!3+N+=!2'^\1#^<!1,63!3'a>'4!M'gI#^M#^L#^K#^J#^F#^E#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#[#I#X#W#V#U#T#M#L#S#R#K#Y!7'`R!O'`S#^M#^L#^K#^J#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#[!2'_Y1!1,6|C34924;#Z!1,_I2#Y!1'`U'4").

Lemma fmt_fp'_spec : fmt_fp'_stmt.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^E0|600;!1,10!1+01|21;|500;|30;!1+0!1,15!1+;6!1+;+=!2+`L8+=!1+29!2'^\1#V|10;!1,6<!2'U=!1,60!3+N:!6'gL#3!2'S;!2'`@>!2'^\1#U#7#6#5#4!2,aF9!4,`M8+=#2#1!4'gM!2'S!2'^\1#W!2'`@>;#6#7#5!2'Q!1,6|<420;!2'^\1#^4!2'^1!2'^\1#^5!2'U=!1,6|51f;!2'Q!1,6|C7d288;!2'_:!2'^\1#^6'gF!2'Q!2'^\1#^7!2'^\1#\!2'Q!2'^\1#^8#@|4f;!2'Q!1'bY!2'U=!1,6F#>!2+^HG!2'Q#>!1,6,^M|44;!2+^HG!2'^1#>!2'U=!1,6I!2'Q,F#>!1,64!2+^HK!2'^1#>!2'U=L!2+^HK!2'^1#>!1,6|800;!1'_B!3+N+=!2'^Z#?L!1,6|621;!2'Q!1'T!2'^8+=#>!2'S!1'T!2'^8+=#?!1'T!2'^86#E!2'bI!2'^86#F}bO!2'^\1#^@!4'`Z'4#M!2'_:R'gFR!2'3'4#N!1'`Y#P!9'`[#P!2'^\1#^;#O#N#M#L#K!1'7#D#J!2'a0#Q#J!3+N2#^:!2'_Y1#J!1'_B!3+N+=!2'^\1#^:!1,63!2'^\1#^A!2'SZ!2'`@>R!2'gP[#M!2'^\1#^B!2'gP!2'S^0!2'`@>Z#N!1'_B^1!2'^\1#^D!2'_Y1!1,6|C34924;!1,_I2!1'`U'4!2'^\1#^C!2'gP!2'S^7!2'`@>^0#O!2'S^3!2'`@>^7!6'gL#N^9#R#Q#P#O!4,`M8+=#N#M$o;R:!3+N:#1!2,aF9^;!6'aE#N^9#R#Q#P#O!2,aF9!4,`M8+=#M#L!2'^\1#^E!2'S^?!2'`@>^3!6'gT#N^9#R#Q#P#O!2'gP^@#Q!4'gV^@#Q#R#P!2'S!2'^\1#^F!2'`@>^?vd$ra;R2$sp;R2$gp;R2$tp;R2$t0;R2$t1;R2$t2;R2$s0;R2$s1;R2$a0;R2$a1;R2$a2;R2$a3;R2$a4;R2$a5;R2$a6;R2$a7;R2$s2;R2$s3;R2$s4;R2$s5;R2$s6;R2$s7;R2$s8;R2$s9;R2$s10;R2$s11;R2$t3;R2$t4;R2$t5;R2$t6;R2$F;R!2'`Q!1,132$fc;R!1+0!1,14$m;R%~R2!1+26$fl0;R6$j1;R7$j2;R7$lbfw;R2$B;R+=$junk0;R7$canary;R2$w;R+=$p;R+=$fl;R+=$t;R+=$o0;R8$o1;R8$ret;R+=vd$HM;R?$FACTS;R@$SPLO;RA$SPHI;RB$GLO;RC$AF;RD$AB;RE$Hw;RH$Hp;RJ$Hfl;RM$Ht;RN$Hta;RO$ROOM;RP$J256;RQ$ST;RS$MI;RT$FRM;RU$WF;RV$SSP;RW$Ha3;RX$Ha4;RX$Ha5;RX$Ha6;RX$Hps;RY&s;R!2'gN[#M!2+gO\!1'_B\-gORN$s;R!2+gO^1^2!3'a>'4!M'gI#^M#^L#^K#^J#^F#^E#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#[^3#X#W#V#U#T#M#L#S#R#K#Y!7'`R!O'`S#^M#^L#^K#^J#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#[^4#Z^5#Y^6#12$n;R^1!1$NF;R^8&HM;R!6'^R:^:^<#K^=!7'gQ#N^9#R#Q#P#O#1!3+N:^=^>!^I'gR#^O#^N#^M#^L#^K#^J#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#[#Z#Y#X#W#V#U#T#S#R#Q#P#O#N#M#1#J#I#H#G#F!8'gS#O^@#S#R#Q#P^;#1#D#C#B#@#?#>#=#<#;#:#9#8#7#6#5#1$n;R^2!1$FIN;R!1'_B^8&HM;R!6'^R:^:^<#K^A!7'gU#N^9#R#Q#P#O#1!3+N:^A^>!6'^N^B^C!3'a>'4!M'gI#^O#^N#^M#^L#^H#^G#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^0!2'^\1#^F#Z#Y#X#W#V#O#N#U#T#M#[!7'`R!O'`S#^O#^N#^M#^L#^K#^J#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0^4#\^5#[^6$~R^B!1$NF;R!2'gP^D#R!2'^V!3'a>'4!M'gI#^Q#^P#^O#^N#^J#^I#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^2!2'^\1#^H#\#[#Z#Y#X#Q#P#W#V#O#^0!7'`R!O'`S#^Q#^P#^O#^N#^M#^L#^K#^J#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#^2^4#^1^5#^0^6!1#4#1#1$~R^C!1$FACTS;R!4'gV^D#R#S#Q!^K'gW#^Q#^P#^O#^N#^M#^L#^K#^J#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#[#Z#Y#X#W#V#U#T#S#R#Q#P#O#3#1#L#K#J#I#H#G#F#E#D#C#B#A#@#?#>#=#<#;#:#9#8#7#1#K#1%~R?%~R@%~RA%~RB%~RC%~RD%~RE%~RH%~RJ%~RM%~RN%~RO%~RP%~RQ%~RS%~RT%~RU%~RV%~RW%~RX%~RX%~RX%~RX%~RY!3'a>'4!M'gI#^K#^J#^I#^H#^D#^C#^:#^9#^8#^7#^6#^5#^4#^3#^2#^1#Y^0#V#U#T#S#R#K#J#Q#P#I#W!7'`R!O'`S#^K#^J#^I#^H#^G#^F#^E#^D#^C#^B#^A#^@#^?#^>#^=#^<#^;#^:#^9#^8#^7#^6#^5#^4#^3#^2#^1#^0#\#[#Z#Y^4#X^5#W^6'gX").
Qed.
