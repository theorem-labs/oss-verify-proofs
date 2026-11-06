(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Numbers; @BinNums; @Z]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@stdpp; @bitvector; @definitions; @bv_swrap]; [@Stdlib; @NArith; @BinNat; @N; @mul]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Stdlib; @NArith; @BinNat; @N; @of_nat]; [@stdpp; @bitvector; @definitions; @bv]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ext_Z]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Lists; @ListDef; @firstn]; [@Corelib; @Lists; @ListDef; @skipn]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @bytes_le_to_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @blob_bytes]; [@LinuxProcessSemantics; @Riscv; @Instr; @mulop]; [@Corelib; @Init; @Datatypes; @true]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Instr; @aluop]; [@LinuxProcessSemantics; @Riscv; @Prelude; @sext]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu32]; [@LinuxProcessSemantics; @Riscv; @Sem; @low32]; [@LinuxProcessSemantics; @Riscv; @Sem; @mul_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ext_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @expr]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @ones]; [@Stdlib; @ZArith; @BinInt; @Z; @land_ones]; [@Corelib; @Init; @Datatypes; @nil]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_spec]; [@Corelib; @Init; @Datatypes; @BoolSpec]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_spec]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Corelib; @Init; @Logic; @and_ind]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@Stdlib; @micromega; @Tauto; @AND]; [@Corelib; @Init; @Logic; @eq_sym]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @micromega; @EnvRing; @PEopp]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_add]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Corelib; @Init; @Logic; @False]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ones64z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @land_ones64z']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @snorm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @snorm_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zmod64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @two64z]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr]; [@Stdlib; @ZArith; @BinInt; @Z; @div_small]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftr_div_pow2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zdiv64]; [@Corelib; @Init; @Datatypes; @andb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @two64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @two32z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ones32z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @land64]; [@Stdlib; @ZArith; @BinInt; @Z; @shiftl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zalu]; [@Stdlib; @ZArith; @BinInt; @Z; @lxor]; [@Stdlib; @ZArith; @BinInt; @Z; @lor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @land32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zaluw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zmd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zfastw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @wrap64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zfastm]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @O]; [@Corelib; @Init; @Datatypes; @comparison]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Init; @Datatypes; @fst]; [@Stdlib; @Lists; @List; @fold_right]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lins]; [@Corelib; @Init; @Datatypes; @snd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lscale_terms]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EMd]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ELit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lterms]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EAlu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @coeffs_div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @is_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zalu_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @unlin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ladd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lscale]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @shamt_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zaluw_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EAluw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zmd_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zmdw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EMdw]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bv_eqb]; [@stdpp; @bitvector; @definitions; @BV]; [@Corelib; @Init; @Logic; @I]; [@stdpp; @bitvector; @definitions; @BvWf]; [@Corelib; @Lists; @ListDef; @nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ridx]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EVar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @saddr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @split_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @SA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @edenot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @a_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @a_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @expr_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sym_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @SSR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sr_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_log]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_know]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_resv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zmod64_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zdiv64_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @two64m1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @all_factsb]; [@Stdlib; @Lists; @List; @filter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @is_factb]; [@Corelib; @Init; @Datatypes; @list_ind]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @all_factsb_filter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @facts_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @erange_f]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @erange_fuel]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ctz_fuel]; [@Corelib; @Numbers; @BinNums; @positive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ctzp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ctzq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @and_mask_align]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @terms_galign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lins_e]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @find_and_atom_k]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ctz64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pageup_low]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ealign0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pageup_align]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sfact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sum_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sum_subst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @erange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_test_rel]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @shares_var]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_apart0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_align]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_slack]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xinside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xinside0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @novars]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xinside_num_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xlo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xinside_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xinside_num]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sub_itv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sub_itv_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @disj_sides_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @base_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @disj_sides]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KWord]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KZero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KImg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KAlign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KRange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KWr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sub_itv_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KDisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KFill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KUnk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @disj_sides_x_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @disj_sides_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sub_itv_x_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @in_sides_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @in_sides]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @in_sides_x_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @in_sides_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @SPrep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xhi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zlit64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_set]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_get]; [@Corelib; @Numbers; @BinNums; @positive_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ptree]; [@Corelib; @Numbers; @BinNums; @xI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @PTLeaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @PTNode]; [@Corelib; @Numbers; @BinNums; @xO]; [@Corelib; @Init; @Logic; @eq_trans]; [@Corelib; @Init; @Logic; @f_equal]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zbytes_le_to_Z]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sidecond]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @know_lookupA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @coeffs_divk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkAlu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @narrow_mask]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkAnd0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @nubE_acc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @expr_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @evalS_def]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @evalS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zfast]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EExt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zext_fast]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @conc_try]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @conc_try_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @closedb]; [@Corelib; @Init; @Datatypes; @negb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @conc_limit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @probeS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @all_eval_toS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @evalS_def_None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @eval_closed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @nubE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @subexprs]; [@LinuxProcessSemantics; @Riscv; @Instr; @branch_cond]; [@LinuxProcessSemantics; @Riscv; @Sem; @branch_taken]; [@Corelib; @Init; @Datatypes; @orb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @itv_lts]; [@Corelib; @Init; @Datatypes; @option_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @itv_ltu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @foldK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkAluK0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkMd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pow2_log]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkAluK]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zsx32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sx32_stable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zband32]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkAluw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkAluwK0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @extK0]; [@LinuxProcessSemantics; @Riscv; @Instr; @msize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @wr_covered_br]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @wr_covered]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @SCStoreOk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @cond_probe]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @concretize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @itab]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @itab_lookup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @itab_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_gss]; [@Corelib; @Init; @Datatypes; @nat_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @itab_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @mk_itab_fuel]; [@Stdlib; @PArith; @BinPos; @Pos; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_gso]; [@Corelib; @Init; @Datatypes; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_get_leaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @mk_itab_fuel_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @scripts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @sym_exec_go]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @clr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @sym_execS_go]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @sym_execT_go]; [@Stdlib; @Lists; @List; @existsb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @kentry_readable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @know_bytes_cov]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @kentry_overlay]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @esize_budget]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @sym_execSX_go]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @WithSegs; @sym_execTX_go]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kcut]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Module AX2K.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive expr : Type :=
| ELit  (z : Z)                              (* [comment removed for export] *)
| EVar  (n : nat)                            (* [comment removed for export] *)
| EAlu  (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EExt  (sx : bool) (lo n : nat) (e : expr)  (* [comment removed for export] *)
| EBlob (sx : bool) (k : nat) (i : Z) (n : nat).
                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Record env : Type := Env { ev : nat -> word; eb : nat -> list byte }.

Definition ext_Z (sx : bool) (lo n : nat) (z : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S40|10;!1,60|30;!1,62$sx;R+0$lo;R+1$n;R+1$z;R+2&u;R!2'3!2'4#1!2'51!2'73!1'8#3!2'51!2'73!1'8#2+2-0RN$sx;R+0+2#52!2'9!2':!1,;2!1'<#3#1#1").

Definition ext_val (sx : bool) (lo n : nat) (v : word) : word := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!1,;|600;$sx;R+0$lo;R+1$n;R+1$v;R!1+=0!2'>0!4'?#4#3#2!2'@0#1").

Definition blob_bytes (bs : list byte) (i : Z) (n : nat) : list byte := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S10!1+=!1,;|30;$bs;R!1+A0$i;R+2$n;R+1!3'B0#1!3'C0!1'D#2#3").

Definition blob_val (sx : bool) (bs : list byte) (i : Z) (n : nat) : word := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S20|30;!1,;0$sx;R+0$bs;R!1+A!1+=1$i;R+2$n;R+1!2'>!1,;|600;&u;R!1'E!3'F#3#2#1+2-0RN$sx;R+0+2#52!2'9!2':1!1'<#2#1#1").

Fixpoint edenot (E : env) (e : expr) : word :=
  match e with
  | ELit z => Z_to_bv 64 z
  | EVar n => ev E n
  | EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | EMd op a b => mul_div op (edenot E a) (edenot E b)
  | EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
  | EExt sx lo n a => ext_val sx lo n (edenot E a)
  | EBlob sx k i n => blob_val sx (eb E k) i n
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aluop_eqb (a b : aluop) : bool :=
  match a, b with
  | ALU_ADD, ALU_ADD | ALU_SUB, ALU_SUB | ALU_SLL, ALU_SLL | ALU_SLT, ALU_SLT
  | ALU_SLTU, ALU_SLTU | ALU_XOR, ALU_XOR | ALU_SRL, ALU_SRL | ALU_SRA, ALU_SRA
  | ALU_OR, ALU_OR | ALU_AND, ALU_AND => true
  | _, _ => false
  end.

Definition mulop_eqb (a b : mulop) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+G$b;R+G-GRN$a;R+G+0#28-GRN$b;R+G+0#18,H,I,I,I,I,I,I,I-GRN$b;R+G+0#18,I,H,I,I,I,I,I,I-GRN$b;R+G+0#18,I,I,H,I,I,I,I,I-GRN$b;R+G+0#18,I,I,I,H,I,I,I,I-GRN$b;R+G+0#18,I,I,I,I,H,I,I,I-GRN$b;R+G+0#18,I,I,I,I,I,H,I,I-GRN$b;R+G+0#18,I,I,I,I,I,I,H,I-GRN$b;R+G+0#18,I,I,I,I,I,I,I,H").

Fixpoint expr_eqb (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => Nat.eqb a b
  | EAlu o a b, EAlu o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EAluw o a b, EAluw o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMd o a b, EMd o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMdw o a b, EMdw o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EExt s l n a, EExt s' l' n' a' =>
      Bool.eqb s s' && Nat.eqb l l' && Nat.eqb n n' && expr_eqb a a'
  | EBlob s k i n, EBlob s' k' i' n' =>
      Bool.eqb s s' && Nat.eqb k k' && Z.eqb i i' && Nat.eqb n n'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zalu (op : aluop) (x y : Z) : Z :=
  bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)).
Definition zaluw (op : aluop) (x y : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!1,;|600;|500;$op;R+J$x;R+2$y;R+2!2'@0vd!3'K!1,;10!3'L#3!1'M!2'>0#2!1'M!2'>0#1!1+=0").
Definition zmd (op : mulop) (x y : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S10!1,;|600;$op;R+G$x;R+2$y;R+2!2'@0!4'N0#3!2'>0#2!2'>0#1").
Definition zmdw (op : mulop) (x y : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S30!1,;|600;|500;!1,;1$op;R+G$x;R+2$y;R+2!2'@0vd!3'K20!4'N2#3!1'M!2'>0#2!1'M!2'>0#1!1+=0").
Definition zext_lit (sx : bool) (lo n : nat) (x : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!1,;|600;$sx;R+0$lo;R+1$n;R+1$x;R+2!2'@0!4'O#4#3#2!2'>0#1").

Definition is_lit (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!1,S+2$e;R+P-PRN$e;R+P!1+Q+2#18$z;R+2!2,R+2#1$n;R+10$op;R+J$a;R+P$b;R+P0$op;R+J$a;R+P$b;R+P0$op;R+G$a;R+P$b;R+P0$op;R+G$a;R+P$b;R+P0$sx;R+0$lo;R+1$n;R+1$e0;R+P0$sx;R+0$k;R+1$i;R+2$n;R+10").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition two64z : Z := 2 ^ 64.
Definition two64 : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10|10;!2'5!1,60!1,6|600;").         (* [comment removed for export] *)
Definition two64m1 : Z := two64 - 1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition two63z : Z := 2 ^ 63.
Definition mtwo63z : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'T!2'5!1,6|10;!1,6|51f;").
Definition two32z : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10|10;!2'5!1,60!1,6|500;").
Definition two31z : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'5!1,6|10;!1,6|4f;").
Definition ones64z : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'U!1,6|600;").          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition snorm_ref (k : Z) : Z :=
  let m := (k mod two64z)%Z in if Z.leb (2 ^ 63) m then (m - two64z)%Z else m.
(* [comment removed for export] *)
Definition snorm (k : Z) : Z :=
  if (if Z.leb mtwo63z k then Z.ltb k two63z else false) then k
  else let m := Z.land k ones64z in if Z.leb two63z m then (m - two64z)%Z else m.
Lemma land_ones64z' : forall a, Z.land a ones64z = (a mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1,6|600;!1+\+2$a;R+2!3'V#10&__arith;R&__wit;R!1,W+X!1+A+X&__varmap;R!1,Y+2!1+Z+2&__ff;R!7,[1'^0+^1+^1,^2!4,^3+2!2,^4+2,^5,^6!2,^4+20,^7!2'^81,^2!4'^9#1#3vv!2,^:+0,H!3+^;+0!2'^<#1#3,H!3'^=+2,^5#2!2'^>,^50#1").
Qed.
Lemma snorm_eq : forall k, snorm k = snorm_ref k.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_I0|10;!1,60|600;!1,62!2'513!2'3#14|51f;!1,66!2'517!1'T8!2'^@9#2-0RN$~R+0+2!2'^@8#12!2'^B#14#1!2'3#24!2'^D13!2'^E,^51!2'^E,^54%~R>%~R!2'^>,^53?!2'^>,^51$Ha;RA$~R+^F!3'^G13#2!2'^>,^54%Ha;RA%~R+^FC!1,W+X!1+A+X!1,Y+2!1+Z+2!1+\+2!2,^4+2,^5!2,^4+21!3,^I+2K!1,;2!2'^8I,^2!4'^9#1#3vv!2,^:+0,H!3+^;+0!2'^<#1#3,H!3'^=+2,^5#2!2'^>9#2!2'^A#68!2'3#64-0RN$~R+0+2!2'^@8Q2!2'^BQ4Q!2'3#:4-0RN$~R+0+2!2'^@8S2!2'^BS4S!2'3#>4!3'^N#B4#5%~RC!2'^>,^5!2'3#C4!2'^D17%~R>%~R!2'^>,^57!2'^E,^58$Ha;RA$~R+^F!3'^G17#2%Ha;RA%~R+^F!2'^>,^58!2'^O#G4!3+^;+24,^5!1'^P^0!2'4#H4!2'3#H4%~R^1!3+^;+2#H!2'^Q!2'74^2^3!2'^C#H4!2'3#I4%~R?!2+^J!2'^>,^5^6!2'^E^64!2'^R#I4!2'^E4,^5!2'3#J4%~R^9!2+^J!2'^E4^:!2'^>^:,^5!2'^S#J4%~R^0!3+^;+2!2'4#K4,^5!2'^T#K4%~R^0!3+^;+2!2'3#L4#L!2'4#L4!2'3#M4!2'^>,^5#1!2'^E#14!2'^>,^5#3!2'^E#44!2,^V+2#2!3,^I+2K!1,;6!2,^X+2,^Y!1,S+^1!7,[I'^0+^1+^1,^2!4,^3+2^H,^H^G,^7!2'^E#28!2'3#?4!2'^O#C4%~R^1!3+^;+2#D!2'^Q!2'74!2'4#D4!2'3#D4!2'^C#D4!2'3#E4!2'^>,^5^P%~R?!2+^J^Q!2'^E^P4!2'^R#E4!2'3#F4%~R^9!2+^J!2'^E4^T!2'^>^T,^5!2'^S#F4%~R^0!3+^;+2!2'4#G4,^5!2'^T#G4%~R^0!3+^;+2^3#H!7,[I'^0+^1+^1,^2!4,^3+2J,^6^H,^7!2'^Q#>4!1,6,^Y!2'^Q#?4!2'^N#>4%~R!2'^>,^5#>%~RC!2'^>,^5!2'3#@4!7,[I'^0+^1+^1,^2!4,^3+2!2,_3+2^G,^6^H,^7!3,_4+2^HL!2'^Q#34!2'^Q#C4!2'^Q#A4!2'^Q#B4!2'^N#C4%~R!2'^>,^5#C%~RC^Q!2'^O#H4%~R^1!3+^;+2#I!2'^Q!2'74!2'4#I4^6!2'^C#I4%~R?!2+^J!2'^>,^5^:!2'^E^:4!2'^R#J4!2'3#K4%~R^9!2+^J!2'^E4_@!2'^>_@,^5!2'^S#K4%~R^0!3+^;+2^@,^5!2'^T#L4%~R^0!3+^;+2^A#M!2'4#M4!2'3#N4!2'^Q#14$k;R+2vd!6'^?+25$z;R+2!3+^;+2-0RN$~R+0+2-0RN$~R+0+0:2!2'^A#28,I2#2;-0RN$~R+0+2!2'^@8<2!2'^B<4<&B;R!3'^C#14&__sat1;R=@&__sat0;RBD&__arith;R&__wit;REF&__varmap;RGH&__ff;R!7,[I'^0+^1+^1,^2!4,^3+2J,^HL,^7MN?#1!2+^J!2'^>,^55!2'^E54&b;R!2'^K9#2!3+^LO!2'^E#29:&b0;R!2'^@9#3+0-^LRN$b;R+0$~R!3+^L!2'^>9#5!2'^E#59#1!3+^;+2-0RN$~R+0+2-0RN$~R+0+0#22P,I2#6RR#22$~R!2'^>9#4!1$H1;R!2'^>9#5&b;R!2'^M#68!3+^L!2'^E#68!2'^>8#6P&b0;R!2'^A#78+0-^LRN$b;R+0$~R!3+^L!2'^E#98!2'^>8#9#1!3+^;+2-0RN$~R+0+2#22#:TT#22$~R!2'^E#88!1$H2;R!2'^E#98&b;R!2'^K,^5#:!3+^L!2'^>,^5#:!2'^E#:,^5!2'^@,^5#:&b0;R!2'^@,^5#;+0-^LRN$b;R+0$~R!3+^L!2'^>,^5#=!2'^E#=,^5#1!3+^;+2#>-0RN$~R+0+2!2'^@8U2!2'^BU4U#22$~R!2'^>,^5#<!1$H3;R!2'^>,^5#=!6'^?+2#>$z;R+2!3+^;+2#?;&b;R!2'^K8#>!3+^L!2'^>8#>!2'^E#>8!2'^@8#>&b0;R!2'^@8#?+0-^LRN$b;R+0$~R!3+^L!2'^>8#A!2'^E#A8#1!3+^;+2#B-0RN$~R+0+2#22!2'^B#B4#B#22$~R!2'^>8#@!1$H;R!2'^>8#A&__sat8;RVW&__sat7;RXY&__sat6;RZ[&__sat5;R=@&__sat4;RBD&H0;R\^4&H4;R^5^7&H5;R^8^;&H6;R^<^=&H7;R^>^?&q;R^@+2&r;R^A+2!5'^U^B^C!3+^;+2#N!2'^B#N4$~R^B$~R!2'^E#24!2$H8;R^D$H9;R^E&__arith;R$__x1;R+2&__wit;REF&__varmap;R^FH&__ff;R!8,^WI'^0+^1+^1,^2!7,[I'^0+^1+^1,^2!4,^3+2^G,^6^H,^7^I!8,^WI'^0+^1+^1,^2^J^I!7,[I'^0+^1+^1,^2!4,^3+2^H,^Z!3,^[+2^HL,^7MN%__x1;R+2%~R!2'^>8#1%~R^K!3+^;+2#3!2'^B#34!3#1#S#B#J#2#1#M#1$~R!2'^E#@8!1$H;R!2'^E#A8&__sat8;RVW&__sat7;RXY&__sat6;RZ[&__sat5;R=@&__sat4;RBD&H0;R\^4&H4;R^5^7&H5;R^8^;&H6;R^<^=&H7;R^>^?&q;R^@+2&r;R^A+2!5'^U^B^C!3+^;+2#N#N$~R^B$~R!2'^E#24!2$H8;R^D$H9;R^E&__arith;R$__x1;R+2&__wit;REF&__varmap;R^FH&__ff;R!7,[I'^0+^1+^1,^2!4,^3+2^H,^Z^H,^7MN%__x1;R+2!3+^;+2#1#1!1#1#S#2#1#M#1U!3'^\#>4&__sat8;R!3'^N#>4#1%~RC!2'^>,^5^L&__sat7;RXY&__sat6;RZ[&__sat5;R=@&__sat4;RBD&H;R^M^N&H0;R^O^R&H4;R^S^U&H5;R^V^W&H6;R^X^Y&q;R^2+2&r;R^6+2!5'^U^B^C!2+^J!2'^>,^5#J!2'^E#J4$~R^B$~R!2'^E#24!2$H7;R^D$H8;R^E&__arith;R$__x1;R+2&__wit;REF&__varmap;R^FH&__ff;R!8,^WI'^0+^1+^1,^2^Z^I!8,^WI'^0+^1+^1,^2^J^I!7,_0I'^0+^1+^1,^2^Z!7,[I'^0+^1+^1,^2!4,^3+2^H,^HL,^7MN%__x1;R+2%~R^B%~R^K!2+^J^D!2'^E#34!3#1#O#B#F#2#1#I#1$~R!2'^E#<,^5!1$H3;R!2'^E#=,^5&H;R!4'_1+2U^[!6'_2+2!2'3!2'^Q#>!2'7^\44$z;R+2!3+^;+2#1_0!3'^\^[4&__sat8;R_1_2&__sat7;RXY&__sat6;RZ[&__sat5;R=@&__sat4;RBD&H;R^M^N&H0;R^O^R&H4;R^S^U&H5;R^V^W&H6;R^X^Y&q;R^2+2&r;R^6+2!5'^U^B^C!2+^J!2'^>,^5!2'^Q#J4!2'^E!2'^Q#J44$~R^B$~R!2'^E#24!2$H7;R^D$H8;R^E&__arith;R$__x1;R+2&__wit;REF&__varmap;R^FH&__ff;R!8,^WI'^0+^1+^1,^2!7,[I'^0+^1+^1,^2!4,^3+2^H,^HJ,^7^I!8,^WI'^0+^1+^1,^2_3^I!7,_0I'^0+^1+^1,^2!7,[I'^0+^1+^1,^2!4,^3+2J,^6_4,^7!7,[I'^0+^1+^1,^2!4,^3+2_4,^HL,^7MN%__x1;R+2%~R!2'^E#1,^5%~RO!2+^J!2'^>,^5_5!2'^E_54!3#1#O#B#J#2#1#IU!4'_5#>^\4&__sat8;R_1_2&__sat7;RXY&__sat6;RZ[&__sat5;R=@&__sat4;RBD&H;R^M^N&H0;R^O^R&H4;R^S^U&H5;R^V^W&H6;R^X^Y&q;R^2+2&r;R^6+2!5'^U^B^C^1$~R^B$~R!2'^E#24!2$H7;R^D$H8;R^E&__arith;R&__wit;REF&__varmap;RGH&__ff;R!6,_6I'^0+^1+^1,^2!7,[I'^0+^1+^1,^2!4,^3+2L,^ZJ,^7MN%~R^0+_7#1#2#1#I!3+^;+2^[U!6'_2+2_0$z;R+2!3+^;+2#@;&b;R!2'^K8_0!3+^L!2'^>8_0!2'^E_08!2'^@8_0&b0;R!2'^@8!2'^Q#@4+0-^LRN$b;R+0$~R!3+^L!2'^>8!2'^Q#B4!2'^E!2'^Q#B48#1!3+^;+2#C-0RN$~R+0+2#22!2'^B_64_6#22$~R!2'^>8_7!1$H;R!2'^>8_8&__sat8;R_9_:&__sat7;RXY&__sat6;RZ[&__sat5;R=@&__sat4;RBD&H0;R_;_<&H4;R_=_>&H5;R_?_A&H6;R_B_C&H7;R_D_E&q;R_F+2&r;R_G+2!5'^U^B^C!3+^;+2#O!2'^B!2'^Q#O44$~R^B$~R!2'^E#24!2$H8;R^D$H9;R^E&__arith;R$__x1;R+2&__wit;REF&__varmap;R^FH&__ff;R!7,[I'^0+^1+^1,^2!4,^3+2^H,^Z!3,^[+2_4L,^7MN%__x1;R+2!3+^;+2#1!2'^B_H4!1#1#T#2#1#N#1$~R!2'^E_78!1$H;R!2'^E_88&__sat8;R_9_:&__sat7;RXY&__sat6;RZ[&__sat5;R=@&__sat4;RBD&H0;R_;_<&H4;R_=_>&H5;R_?_A&H6;R_B_C&H7;R_D_E&q;R_F+2&r;R_G+2!5'^U^B^C!3+^;+2#O!2'^Q#O4$~R^B$~R!2'^E#24!2$H8;R^D$H9;R^E&__arith;R$__x1;R+2&__wit;REF&__varmap;R^FH&__ff;R!8,^WI'^0+^1+^1,^2!7,[I'^0+^1+^1,^2!4,^3+2_4,^H^G,^7^I!8,^WI'^0+^1+^1,^2_3^I!7,[I'^0+^1+^1,^2!4,^3+2^H,^Z_4,^7MN%__x1;R+2%~R!2'^E_H8%~RO!3+^;+2#3_5!3#1#T#B#O#2#1#N#1^L#1#1#1$~R!2'^>8#8!1$H2;R!2'^>8#9!2,^:+2T#1#1$~R!2'^E#49!1$H1;R!2'^E#59!2,^:+2R#1!2'_8#1'_9!1'_:#1!3+^;+2!1'_;#1!1'_<#1").
Qed.

(* [comment removed for export] *)
Definition zmod64 (z : Z) : Z :=
  if (if Z.leb 0 z then Z.ltb z two64z else false) then z else Z.land z ones64z.
Lemma zmod64_eq : forall z, zmod64 z = (z mod 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SA0|10;!1,60|600;!1,62!2'513!2'3#14!2'^@,^5#2!2'^A#54!2'3#54!2'^>,^5#3!2'3#94!2'^>,^51!1+\+2!2,^X+2,^Y!7,[<'^0+^1+^1,^2!4,^3+2=,^H!3,^I+2!2,^4+21!1,;2,^7!1,S+^1!7,[<'^0+^1+^1,^2!4,^3+2!2,^4+2,^5,^6=,^7$z;R+2vd!6'^?+25$z;R+2!3+^;+2-0RN$~R+0+2-0RN$~R+0+062!2'^A#24,I2#2#1!2'3#24&b;R!2'^K,^5#1!3+^L!2'^>,^5#1!2'^E#1,^5!2'^@,^5#1&b0;R6+0-^LRN$b;R+0$~R!3+^L!2'^>,^5#4!2'^E#4,^5#1!3+^;+2-0RN$~R+0+2-0RN$~R+0+0#227,I2#588#22$~R9!1$H;R!2'^>,^5#4&b;R!2'^M#54!3+^L!2'^E#54!2'^>4#57&b0;R!2'^A#64+0-^LRN$b;R+0$~R!3+^L!2'^E#84!2'^>4#8#1!3+^;+2-0RN$~R+0+2#22#9::#22$~R!2'^E#74!1$H0;R!2'^E#84!4'_1+2:#9!3'^\#94&__sat2;R!2'^D13%~R!2'^E,^51%~R!2'^>,^53!2'^E,^54&__sat1;R$Ha;R;$~R+^F!3'^G13#2%Ha;R;%~R+^F!2'^>,^54&__arith;R$__x1;R+2&__wit;R!1,W+X!1+A+X&__varmap;R!2,^V+2#2!1+Z+2&__ff;R!8,^W<'^0+^1+^1,^2>?!8,^W<'^0+^1+^1,^2@?!7,_0<'^0+^1+^1,^2@>!2'^8<,^2!4'^9#1#3vv!2,^:+0,H!3+^;+0!2'^<#1#3,H!3'^=+2,^5#2%__x1;R+2%~R!2'^E#14%~R!2'^>,^5#2!2+^J9!2'^E#34!3#1#<#4#8#1$~R!2'^>4#7!1$H0;R!2'^>4#8!2,^:+2:#1#1$~R!2'^E#3,^5!1$H;R!2'^E#4,^5!2,^:+28#1!2'_8#1'_9!1'_:#1!3+^;+2!1'_=#15").
Qed.
Definition zdiv64 (z : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$z;R+2-0RN$~R+0+2-0RN$~R+0+0!2'^@,^5#12!2'^A#1'_>,I2,^5!2'_?#1!1,6|600;").
Lemma zdiv64_eq : forall z, zdiv64 z = (z / 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SJ0|10;!1,60|600;!1,62!2'513!2'^A#54!2'^>,^5#3!2'4#94!2'^D13!2'^>,^53%~R!2'^E,^51%~R9!2'^E,^54!2'^>,^51$Ha;R;$~R+^F!3'^G13#2%Ha;R;%~R+^F!2'^>,^54!1,W+X!1+A+X!1+Z+2!1+\+2!2,^X+2,^Y!7,[A'^0+^1+^1,^2!4,^3+2B,^H!3,^I+2!2,^4+21!1,;2,^7!1,S+^1!2,^4+2,^5!7,[A'^0+^1+^1,^2!4,^3+2E,^6B,^7!2'^8A,^2!4'^9#1#3vv!2,^:+0,H!3+^;+0!2'^<#1#3,H!3'^=+2,^5#2&__arith;R&__wit;R>?&__varmap;R!1,Y+2@&__ff;R!7,[A'^0+^1+^1,^2!4,^3+2E,^6!2,^4+23,^7GH9#1$z;R+2vd&b;R!2'^K,^5#1!3+^L!2'^>,^5#1!2'^E#1,^5!2'^@,^5#1&b0;R!2'^@,^5#2+0-^LRN$b;R+0$~R!3+^L!2'^>,^5#4!2'^E#4,^5#1!3+^;+2-0RN$~R+0+2-0RN$~R+0+0#225,I2,^5!2'_?#53!2'4#54#22$~R6!1$H;R!2'^>,^5#4&b;R!2'^M#54!3+^L!2'^E#54!2'^>4#55&b0;R!2'^A#64+0-^LRN$b;R+0$~R!3+^L!2'^E#84!2'^>4#8#1!3+^;+2-0RN$~R+0+2#22,^5!2'_?#937#22$~R!2'^E#74!1$H0;R!2'^E#84!4'_1+27,^5!3'_@#94&__sat2;R8:&__sat1;R<=&__arith;R$__x1;R+2&__wit;R>?&__varmap;R!2,^V+2#2@&__ff;R!8,^WA'^0+^1+^1,^2CD!8,^WA'^0+^1+^1,^2FD!7,_0A'^0+^1+^1,^2FCGH%__x1;R+2%~R!2'^E#14%~R!2'^>,^5#2!2+^J6!2'^E#34!3#1#<#4#8#1$~R!2'^>4#7!1$H0;R!2'^>4#8!3'_A#93&__sat2;R8:&__sat1;R<=I#1#1$~R!2'^E#3,^5!1$H;R!2'^E#4,^5!3'_A#53I#1!3+^;+2!1'_B#1!2'4#14").
Qed.

(* [comment removed for export] *)
Definition wrap64 (z : Z) : Z :=
  if (Z.leb 0 z && Z.ltb z two64)%bool then z else (z mod two64)%Z.

Definition sx32 (r : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$r;R+2-0RN$~R+0+2!2'^A#1!1,6|O00000000;2#1!2'^Q#1!1,6|^B7fffffff00000000;").

(* [comment removed for export] *)
Definition ones32z : Z := Z.ones 32.
Definition land64 (z : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$z;R+2-0RN$~R+0+2!2'_C!2'^@,^5#1!2'^A#1'_D2#1!2'_8#1'_9").
Definition land32 (z : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$z;R+2-0RN$~R+0+2!2'_C!2'^@,^5#1!2'^A#1'_E2#1!2'_8#1'_F").

Definition zfast (op : aluop) (x y : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!2'_8#1!1,6|51f;!3'_I#3#2#1$op;R+J$x;R+2$y;R+2-JRN$op;R+J+2#3:&t;R!2'^Q#2#1+2-0RN$~R+0+2!2'^A#1'_D2#1!2'^B#1'_D&t;R!2'^B#2#1+2-0RN$~R+0+2!2'^@,^5#12#1!2'^Q#1'_D!1'_G!2'_H#201-0RN$~R+0+2!2'^A#2#12!1,6,^Y,^5!2'_J#2#1!2'_?#201!2'_K#2#1!2'_8#2#1").

Definition zfastw (op : aluop) (x y : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S30!1'_M#2!2'_8#1!1,6|4f;!3'_N#3#2#1$op;R+J$x;R+2$y;R+2-JRN$op;R+J+2#3:!1'_L!1'_M!2'^Q#2#1!1'_L!1'_M!2'^B#2#1!1'_L!1'_M!2'_H01222!1'_L!2'_?01222").

Definition zfastm (op : mulop) (x y : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S10!3'_O#3#2#1$op;R+G$x;R+2$y;R+2-GRN$op;R+G+2#38!1'_G!2'7#2#10000000").

(* [comment removed for export] *)
Definition zext_fast (sx : bool) (lo n : nat) (x : Z) : Z :=
  let k := (8 * Z.of_nat n)%Z in
  let u := Z.land (Z.shiftr x (8 * Z.of_nat lo)) (Z.ones k) in
  if sx then match n with
             | O => wrap64 u
             | _ => if Z.ltb u (Z.shiftl 1 (k - 1)) then wrap64 u else wrap64 (u - Z.shiftl 1 k + two64)
             end
  else wrap64 u.

(* [comment removed for export] *)
Definition zalu_l (op : aluop) (x y : Z) : Z := zfast op (wrap64 x) (wrap64 y).
Definition zaluw_l (op : aluop) (x y : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$op;R+J$x;R+2$y;R+2!3'_P#3!1'_Q#2!1'_Q#1").
Definition zmd_l (op : mulop) (x y : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$op;R+G$x;R+2$y;R+2!3'_R#3!1'_Q#2!1'_Q#1").

Definition lin : Type := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S01<sc;!2+_S+2!1+A!2+_S+2+P").

Definition ctor_ix (e : expr) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S60}1}2}3}4}5}6$e;R+P-PRN$e;R+P+1#18$z;R+2,_T$n;R+10$op;R+J$a;R+P$b;R+P1$op;R+J$a;R+P$b;R+P2$op;R+G$a;R+P$b;R+P3$op;R+G$a;R+P$b;R+P4$sx;R+0$lo;R+1$n;R+1$e0;R+P5$sx;R+0$k;R+1$i;R+2$n;R+1}7").
Definition aluop_ix (op : aluop) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S80}1}2}3}4}5}6}7}8$op;R+J-JRN$op;R+J+1#1:,_T01234567}9").
Definition mulop_ix (op : mulop) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S60}1}2}3}4}5}6$op;R+G-GRN$op;R+G+1#18,_T012345}7").
Definition bool_ix (b : bool) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$b;R+0-0RN$b;R+0+1#12}1,_T").
Definition lexc (c k : comparison) : comparison := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$c;R+_U$k;R+_U-_URN$c;R+_U+_U#23#1#2#2").

Fixpoint expr_cmp (x y : expr) {struct x} : comparison :=
  match x, y with
  | ELit a, ELit b => Z.compare a b
  | EVar a, EVar b => Nat.compare a b
  | EAlu o a b, EAlu o' a' b' =>
      lexc (Nat.compare (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EAluw o a b, EAluw o' a' b' =>
      lexc (Nat.compare (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMd o a b, EMd o' a' b' =>
      lexc (Nat.compare (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMdw o a b, EMdw o' a' b' =>
      lexc (Nat.compare (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EExt s l n e, EExt s' l' n' e' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
           (lexc (Nat.compare l l') (lexc (Nat.compare n n') (expr_cmp e e')))
  | EBlob s k i n, EBlob s' k' i' n' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
           (lexc (Nat.compare k k') (lexc (Z.compare i i') (Nat.compare n n')))
  | _, _ => Nat.compare (ctor_ix x) (ctor_ix y)
  end.

(* [comment removed for export] *)
Fixpoint lins (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb (snorm k) 0 then [] else [(snorm k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then
        (let s := snorm (k + k') in if Z.eqb s 0 then rest else (s, a') :: rest)
      else match expr_cmp a a' with
           | Lt => if Z.eqb (snorm k) 0 then ts else (snorm k, a) :: ts
           | _ => (k', a') :: lins k a rest
           end
  end.

Definition ladd (x y : lin) : lin := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+_S+2+P!1+A0$x;R'_V$y;R'_V!4,_W+21!1'_;!2'^Q!3'_X+21#2!3'_X+21#1!5'_Y10$t;R0$acc;R1!3'_Z!3'_X+2+P#2!3'_[+2+P#2#1!3'_[+21#1!3'_[+21#2").

Fixpoint lscale_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest =>
      let k' := snorm (m * k) in
      if Z.eqb k' 0 then lscale_terms m rest else (k', a) :: lscale_terms m rest
  end.

Definition lscale (m : Z) (x : lin) : lin := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1+A!2+_S+2+P$m;R+2$x;R'_V!4,_W+20!1'_;!2'7#2!3'_X+20#1!2'_\#2!3'_[+20#1").

(* [comment removed for export] *)
Fixpoint lin_of (e : expr) : lin :=
  match e with
  | ELit z => (snorm z, [])
  | EAlu ALU_ADD a b => ladd (lin_of a) (lin_of b)
  | EAlu ALU_SUB a b => ladd (lin_of a) (lscale (-1) (lin_of b))
  | EAlu ALU_SLL a (ELit s) => lscale (2 ^ (s mod 64)) (lin_of a)
  | EMd M_MUL (ELit k) a => lscale k (lin_of a)
  | EMd M_MUL a (ELit k) => lscale k (lin_of a)
  | _ => (0%Z, [(1%Z, e)])
  end.

Definition lterm (t : Z * expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!3'_X+2+P#1!3'_[+2+P#1$t;R!2+_S+2+P-0RN$~R+0+P!2'`00!1,6,^Y21!3,`1,`2!1,`301").

Fixpoint lterms (ts : list (Z * expr)) : expr :=
  match ts with
  | [] => ELit 0
  | [t] => lterm t
  | t :: rest => EAlu ALU_ADD (lterm t) (lterms rest)
  end.

Definition unlin (x : lin) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S40!2+_S+2+P!1+A0!3'_X+21#3!1'`4!3'_[+21#3$x;R'_V-ARN$x;R!1+A0+P!3'_[+21#12!1,`3!3'_X+21#1$p;R0$l;R!1+A0-0RN$~R+0+P!2'`02,^523!3,`5,`63!1,`32").

(* [comment removed for export] *)
Fixpoint coeffs_div (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, _) :: rest => (Z.eqb (k mod m) 0 && coeffs_div m rest)%bool
  end.

Definition lin_lowbits (e : expr) (k : Z) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2'5!1,6|10;#2!1+A!2+_S+2+P$e;R+P$k;R+2&l;R!1'`7#2'_V-0RN$~R+0!1+Q+2!2'`80!3'_[+21#12!2,R+2!2'3!3'_X+21#10!1,S+2").

(* [comment removed for export] *)
Definition shamt_of (e : expr) (bits : Z) : option Z :=
  match e with
  | ELit s => Some (s mod 2 ^ bits)%Z
  | _ => lin_lowbits e bits
  end.

Definition mkAlu (op : aluop) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S>0!1'`9#2!1'`7#3!1'`7#2!1,`>,^Y!1,6|22;!2'`?#24!2'5!1,6|10;#1!3,`5#4#3#2!1,`3#1-QRN$x;R!1+Q+2+P02$z;R+2!3,`5#5#4#3-QRN$x;R!1+Q+2+P52$s;R+2!3,`5#5#487!1'`7#1!2'`?#14!3,`5#3#2#1-QRN$x;R!1+Q+2+P!1'`9#12$z;R+27-QRN$x;R!1+Q+2+P;2$s;R+2!3,`5#4#38<$op;R+J$a;R+P$b;R+P-QRN$x;R!1+Q+2+P02$x;R+2-QRN$x;R!1+Q+2+P02$y;R+2!1,`3!3'`:#5#2#1-JRN$op;R+J+P#4:!1'`;!2'`<12!1'`;!2'`<1!2'`=32-QRN$x;R!1+Q+2+P52$s;R+2!1'`;!2'`=6!1'`7#477779977-JRN$op;R+J+P#3:!1'`;!2'`<2:!1'`;!2'`<2!2'`=3:-QRN$x;R!1+Q+2+P;2$s;R+2!1'`;!2'`=61<<<<==<<").

Definition mkAluw (op : aluop) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S70!1'`9#2!3,`A#4#3#2!1,6|21;!1,`3#1-QRN$x;R!1+Q+2+P02$z;R+2!3,`A#5#4#3-QRN$x;R!1+Q+2+P!2'`?#222$s;R+2-QRN$x;R!1+Q+2+P!1'`9#42$x;R+2!1,`3!3'`@#6#1#2!3,`A#5#431!3,`A#3#2#1-QRN$x;R!1+Q+2+P!1'`9#12$z;R+21-QRN$x;R!1+Q+2+P!2'`?#122$s;R+2-QRN$x;R!1+Q+2+P!1'`9#32$x;R+2!1,`3!3'`@#5#1#2!3,`A#4#335$op;R+J$a;R+P$b;R+P-QRN$x;R!1+Q+2+P02$x;R+2-QRN$x;R!1+Q+2+P02$y;R+2!1,`3!3'`@#5#2#1-JRN$op;R+J+P#4:1141114411-JRN$op;R+J+P#3:5565556655").

Definition mkMd (op : mulop) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!1'`9#2!3,`1#4#3#2$op;R+G$a;R+P$b;R+P-QRN$x;R!1+Q+2+P02$x;R+2-QRN$x;R!1+Q+2+P02$y;R+2!1,`3!3'`B#5#2#1-GRN$op;R+G+P#48!1'`;!2'`=#1!1'`7#21111111-QRN$x;R!1+Q+2+P!1'`9#12$y;R+2-GRN$op;R+G+P#48!1'`;!2'`=#1!1'`7#31111111!3,`1#3#2#1").

Definition mkMdw (op : mulop) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S10!1'`9#2$op;R+G$a;R+P$b;R+P-QRN$x;R!1+Q+2+P02$x;R+2-QRN$x;R!1+Q+2+P02$y;R+2!1,`3!3'`C#5#2#1!3,`D#4#3#2!3,`D#3#2#1").

(* [comment removed for export] *)
Definition mkExt (sx : bool) (lo n : nat) (e : expr) : expr :=
  match e with
  | ELit x => ELit (zext_fast sx lo n (wrap64 x))   (* [comment removed for export] *)
  | _ =>
    if (Nat.eqb lo 0 && Nat.eqb n 8)%bool then e
    else match e with
         | EExt false lo' n' e' =>
             if (Nat.leb (lo + n) n' && Nat.leb n' 8)%bool then EExt sx (lo' + lo) n e'
             else EExt sx lo n e
         | _ => EExt sx lo n e
         end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

Definition sr_get (sr : list expr) (r : reg) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!1,;|21;!1,`3,^5$sr;R!1+A+P$r;R!1+=0-0RN$~R+0+P!3'`E0#1!3,`F0,^5vv,`G!2'`H0,^521!4'`I+P!1'`J#1#21").

Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

Definition sr_id : list expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "SN0}1}2}3}4}5}6}7}8}9}:};}<}=}>}?}@}A}B}C}D}E}F}G}H}I}J}K}L}M}N!3,`K+P!1,`L,_T!3,`K+P!1,`L0!3,`K+P!1,`L1!3,`K+P!1,`L2!3,`K+P!1,`L3!3,`K+P!1,`L4!3,`K+P!1,`L5!3,`K+P!1,`L6!3,`K+P!1,`L7!3,`K+P!1,`L8!3,`K+P!1,`L9!3,`K+P!1,`L:!3,`K+P!1,`L;!3,`K+P!1,`L<!3,`K+P!1,`L=!3,`K+P!1,`L>!3,`K+P!1,`L?!3,`K+P!1,`L@!3,`K+P!1,`LA!3,`K+P!1,`LB!3,`K+P!1,`LC!3,`K+P!1,`LD!3,`K+P!1,`LE!3,`K+P!1,`LF!3,`K+P!1,`LG!3,`K+P!1,`LH!3,`K+P!1,`LI!3,`K+P!1,`LJ!3,`K+P!1,`LK!3,`K+P!1,`LL!3,`K+P!1,`LM!3,`K+P!1,`L}O!1,W+P").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record saddr : Type := SA { a_base : expr; a_off : Z }.

Definition split_lit (e : expr) : expr * Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S50!2+_S+P+2!4,_W+P+2#5,^5!4,_W+P+2#7,^5!4,_W+P+2#8,^5!4,_W+P+2#4,^5$e;R+P-PRN$e;R+P0#18$z;R+2!4,_W+P+2!1,`3,^5#1$n;R+1!4,_W+P+2#2,^5$op;R+J$b;R+P$b0;R+P-JRN$op;R+J0#3:-PRN$b0;R+P0#18$z;R+2!4,_W+P+2#3#1$n;R+11$op0;R+J$a;R+P$b1;R+P2$op0;R+J$a;R+P$b1;R+P2$op0;R+G$a;R+P$b1;R+P2$op0;R+G$a;R+P$b1;R+P2$sx;R+0$lo;R+1$n;R+1$e0;R+P3$sx;R+0$k;R+1$i;R+2$n;R+13444444444$op;R+J$a;R+P$b;R+P4$op;R+G$a;R+P$b;R+P4$op;R+G$a;R+P$b;R+P4$sx;R+0$lo;R+1$n;R+1$e0;R+P1$sx;R+0$k;R+1$i;R+2$n;R+11").

Definition to_saddr (e : expr) (imm : Z) : saddr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$e;R+P$imm;R+2-_SRN$p;R!2+_S+P+2+`M!1'`N#21$b;R+P$k;R+2!2,`O#2!2'^Q#1#3").

Definition adenot (E : env) (a : saddr) : word := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$E;R+`P$a;R+`M!2'`Q!2'`R#2!1'`S#1!1'`T#1").

Definition saddr_eqb (a b : saddr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+`M$b;R+`M!2'_C!2'`U!1'`S#2!1'`S#1!2'`0!1'`T#2!1'`T#1").

(* [comment removed for export] *)
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

(* [comment removed for export] *)
Inductive kentry : Type :=
| KWord (a : saddr) (w : nat) (v : expr)      (* [comment removed for export] *)
| KZero (a : saddr) (n : expr)                (* [comment removed for export] *)
| KBlob (a : saddr) (n : expr) (k : nat)      (* [comment removed for export] *)
| KImg  (lo hi : Z)                           (* [comment removed for export] *)
| KAlign (e : expr) (m : Z)                   (* [comment removed for export] *)
| KRange (e : expr) (lo hi : Z)               (* [comment removed for export] *)
| KWr (a : saddr) (n : expr)                  (* [comment removed for export] *)
| KDisj (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
                                              (* [comment removed for export] *)
| KFill (a : saddr) (n : expr) (c : Z)        (* [comment removed for export] *)
| KUnk (a : saddr) (n : expr).                 (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : expr)                     (* [comment removed for export] *)
| SCDisj     (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCInside   (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCStoreOk  (a : saddr) (n : nat)                      (* [comment removed for export] *)
| SCReadBase (a : saddr) (n : nat) (sx : bool) (e : expr)  (* [comment removed for export] *)
| SCEq       (a b : expr).                              (* [comment removed for export] *)

Record sym_state : Type := SSR {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;       (* [comment removed for export] *)
  s_know : list kentry;
  s_next : nat;               (* [comment removed for export] *)
  s_resv : option saddr       (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Abbreviation SS p r l k n := (SSR p r l k n None).

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S20!1,;|21;!1'`X#4$ss;R+`V$rd;R!1+=0$e;R+P$npc;R+2!6,`W#1-0RN$~R+0!1+A+P!3'`E0#3!3,`F0,^5vv,`G!2'`H0,^521!3'`Y1!1'`J#3#2!1'`Z#4!1'`[#4!1'`\#4!1'a0#4").

Definition sjump (ss : sym_state) (npc : Z) : sym_state := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$ss;R+`V$npc;R+2!6,`W#1!1'`X#2!1'`Z#2!1'`[#2!1'`\#2!1'a0#2").

(* [comment removed for export] *)
Definition clr (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (s_regs ss) (s_log ss) (s_know ss) (s_next ss) None.
Definition s_clean (ss : sym_state) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$ss;R+`V-QRN$x;R!1+Q+`M+0!1'a0#12$s;R+`M,I,H").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rangerel := RInside (delta : Z) | RDisjoint | RPartial | RUnknown.

(* [comment removed for export] *)
Definition rel_lit (rb : expr) (rk : Z) (rn : Z) (kb : expr) (kk : Z) (kn : Z) : rangerel :=
  if expr_eqb rb kb then
    if (Z.leb kk rk && Z.leb (rk + rn) (kk + kn))%bool then RInside (rk - kk)
    else if (Z.leb (rk + rn) kk || Z.leb (kk + kn) rk)%bool then RDisjoint
    else RPartial
  else RUnknown.

Definition elen (n : nat) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$n;R+1!1,`3!1'8#1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_strip (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_ADD v (ELit c) => (v, c)
  | _ => (e, 0%Z)
  end.
Fixpoint find_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest =>
      if expr_eqb e e' then Some (lo, hi) else
      match e with
      | ELit _ => find_range rest e
      | _ =>
        let '(v, c) := lit_strip e in
        let '(v', c') := lit_strip e' in
        if expr_eqb v v' then
          let d := (c - c')%Z in
          if (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2 ^ 64) && Z.leb 0 (lo + d) && Z.ltb (hi + d) (2 ^ 64))%bool
          then Some ((lo + d)%Z, (hi + d)%Z) else find_range rest e
        else find_range rest e
      end
  | _ :: rest => find_range rest e
  end.

(* [comment removed for export] *)
Fixpoint find_align (kn : list kentry) (e : expr) : option Z :=
  match kn with
  | [] => None
  | KAlign e' m :: rest => if expr_eqb e e' then Some m else find_align rest e
  | _ :: rest => find_align rest e
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zmod64_eq2 : forall z, zmod64 z = (z mod two64)%Z. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'a1").
Qed.
Lemma zdiv64_eq2 : forall z, zdiv64 z = (z / two64)%Z. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00'a2").
Qed.

Definition clampi (r : Z * Z) : Z * Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!2+_S+2+2$r;R0-_SRN$r;R!2+_S+2+20#11$lo;R+2$hi;R+2!4,_W+2+2!2'a3#2,^5!2'a4#1'a5").

(* [comment removed for export] *)
Definition mask_cover (h : Z) : Z :=
  if Z.ltb h 0 then 0 else (2 ^ (Z.log2_up (h + 1)) - 1)%Z.

Definition lit_shamt (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!1,S+2$e;R+P-PRN$e;R+P!1+Q+2#18$s;R+2!2,R+2!2'3#1!1,6|600;$n;R+10$op;R+J$a;R+P$b;R+P0$op;R+J$a;R+P$b;R+P0$op;R+G$a;R+P$b;R+P0$op;R+G$a;R+P$b;R+P0$sx;R+0$lo;R+1$n;R+1$e0;R+P0$sx;R+0$k;R+1$i;R+2$n;R+10").

(* [comment removed for export] *)
Definition zsigned64 (v : Z) : Z := if Z.leb two63z v then (v - two64)%Z else v.

(* [comment removed for export] *)
Fixpoint lin_range (rng : expr -> option (Z * Z)) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match ts with
  | [] => Some (c, c)
  | (k, a) :: rest =>
      match rng a, lin_range rng c rest with
      | Some (al, ah), Some (lo, hi) =>
          if Z.leb 0 k then Some ((lo + k * al)%Z, (hi + k * ah)%Z)
          else Some ((lo + k * ah)%Z, (hi + k * al)%Z)
      | _, _ => None
      end
  end.

Definition lin_trivial (l : lin) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!2+_S+2+P!1+A0$l;R'_V-_SRN$l;R!2+_S+21+0#11$c;R+2$l0;R1-ARN$l0;R!1+A0+0#12,I$p;R0$l1;R!1+A0-_SRN$p;R!2+_S+2+P+0#21$k;R+2$e;R+P-ARN$l1;R!1+A0+0#32!2'_C!2'`0#6,^5!2'`0#2!1,6,^Y$p0;R0$l2;R!1+A0,I").

Fixpoint erange_f (fuel : nat) (kn : list kentry) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_f fuel' in
  match find_range kn e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange kn) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          match (match b, erange kn a with
                 | ELit m, Some (al, ah) =>
                     let m' := (m mod two64)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (al / 2 ^ j) (ah / 2 ^ j) && Z.eqb (al / 2 ^ j) (ah / 2 ^ j))%bool
                     then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
              then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := (2 ^ (8 * Z.of_nat n))%Z in
      if sx then
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.

(* [comment removed for export] *)
Definition erange_fuel : nat := 64%nat.
Global Opaque erange_fuel.
(* [comment removed for export] *)
Definition is_factb (K : kentry) : bool :=
  match K with KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ | KWr _ _ => true | _ => false end.
(* [comment removed for export] *)
Fixpoint all_factsb (kn : list kentry) : bool :=
  match kn with [] => true | K :: rest => if is_factb K then all_factsb rest else false end.
Definition facts_of (kn : list kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!1+A+a6$kn;R0-0RN$~R+00!1'a7#12#1!3'a8+a6'a9#1").
Lemma all_factsb_filter : forall kn, all_factsb kn = true -> List.filter is_factb kn = kn.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!1+A+a6%~R!3+^;+0!1'a7#1,H!3+^;0!3'a8+a6'a9#2#2!1,W+a6!3'a8+a6'a9#5!3,`K+a6#6#5!3,`K+a6#4#3$kn;R0!5'a:+a6$kn;R01vd$~R!3+^;+0,H,H!2,^:02%~R!3+^;+0!1'a72,H!3+^;0!3'a8+a6'a922$K;R+a6$rest;R0$IH;R1vd&b;R!1'a9#3+0-0RN$b;R+0%~R!3+^;+0-0RN$~R+0+0#12!1'a7#4,I,H!3+^;0-0RN$~R+00#22!3,`K+a6#6334#12$H;R!3+^;+0!1'a7#3,H!6'^?0#4$l;R0!3+^;0!3,`K+a6#6#14!2,^:0!3,`K+a6#5#4!3'a8+a6'a9#4!1#3#1$H;R!3+^;+0,I,H&H0;R!6'_2+0,I$e;R+0-0RN$b;R+0w#12+_7+^F,`G,H#1+_7!2'a;!3+^;034#1%~R!3+^;+0!1'a7!3,`K+a6#3#2,H!3+^;0!3'a8+a6'a955#1").
Qed.
Lemma facts_of_filter : forall kn, facts_of kn = List.filter is_factb kn.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S40!1+A+a6!3'a8+a6'a9#5!1'a7#3!3'a8+a6'a9#4$kn;R0vd&b;R!1'a7#1+0&E;R!2,^:+0#1!3+^;+0!1'a7#2#1!1-0RN$b;R+0%E;R!3+^;+0!1'a7#4#1!3+^;0-0RN$~R+00#22#511#22$E;R!3+^;+02,H!4'_103#4!2'a<#4#1$E;R!3+^;+02,I!2,^:03#1!3+^;0!1'a=#1!3'a8+a6'a9#1").
Qed.
Definition erange0 (kn : list kentry) (e : expr) : option (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$kn;R!1+A+a6$e;R+P!3'a>'a?!1'a=#2#1").

(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := (m mod two64)%Z in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', (s + (2 ^ j - 1))%Z)
      else (e, 0%Z)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', (s1 + s2)%Z)
  | _ => (e, 0%Z)
  end.

(* [comment removed for export] *)
Fixpoint ctz_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if (Z.eqb (z mod 2) 0)%Z then (1 + ctz_fuel f (z / 2))%Z else 0%Z
  end.
Definition ctz64 (z : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$z;R+2!2'a@}^C#1").

(* [comment removed for export] *)
Fixpoint ctzp (f : nat) (p : positive) : Z :=
  match f with
  | O => 0%Z
  | S f' => match p with xO q => Z.succ (ctzp f' q) | _ => 0%Z end
  end.
Definition ctzq (z : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!2'aB}<#1$z;R+2-2RN$z;R+2+2#13!1,6|34;$p;R+aA0$p;R+aA0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition and_mask_align (mk : Z) : Z :=
  let m' := (mk mod two64)%Z in
  let s := Z.log2 (two64 - m') in
  if (Z.eqb (two64 - m') (2 ^ s) && Z.ltb 0 s && Z.ltb s 64)%bool then s else 0%Z.
Definition atom_galign (a : expr) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$a;R+P-PRN$a;R+P+2#18$z;R+2!1'aC#1$n;R+1,^5$op;R+J$a0;R+P$b;R+P-JRN$op;R+J+2#3:,^5,^5,^5,^5,^5,^5,^5,^5,^5-PRN$b;R+P+2#18$mk;R+2!1'aD#1$n;R+1,^5$op0;R+J$a1;R+P$b0;R+P,^5$op0;R+J$a1;R+P$b0;R+P,^5$op0;R+G$a1;R+P$b0;R+P,^5$op0;R+G$a1;R+P$b0;R+P,^5$sx;R+0$lo;R+1$n;R+1$e;R+P,^5$sx;R+0$k;R+1$i;R+2$n;R+1,^5$op;R+J$a0;R+P$b;R+P,^5$op;R+G$a0;R+P$b;R+P,^5$op;R+G$a0;R+P$b;R+P,^5$sx;R+0$lo;R+1$n;R+1$e;R+P,^5$sx;R+0$k;R+1$i;R+2$n;R+1,^5").
Fixpoint terms_galign (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 12%Z
  | (k, a) :: r => Z.min (Z.min 12 (ctzq k + atom_galign a)) (terms_galign r)
  end.
Definition lin_galign (l : lin) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!1+A!2+_S+2+P$l;R'_V!2'a4!1'aC!3'_X+20#1!1'aE!3'_[+20#1").
(* [comment removed for export] *)
Definition round_itv (g : Z) (lo hi : Z) : Z * Z :=
  if Z.ltb 0 g then let m := (2 ^ g)%Z in (((lo + m - 1) / m) * m, (hi / m) * m)%Z else (lo, hi).

Definition erange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let r := erange0 kn e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  (* [comment removed for export] *)
  let g := lin_galign (lin_of e) in
  let rnd := fun p : Z * Z => Some (round_itv g (fst p) (snd p)) in
  match erange0 kn (unlin (lin_of e')) with     (* [comment removed for export] *)
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => rnd (Z.max lo (lo' - s), Z.min hi hi')
        | None => rnd ((lo' - s)%Z, hi')
        end
      else match r with Some p => rnd p | None => None end
  | None => match r with Some p => rnd p | None => None end
  end.


(* [comment removed for export] *)
Definition base_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match e with ELit z => let v := (z mod two64)%Z in Some (v, v) | _ => erange kn e end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ealign0 (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (z mod two64)
  | EAlu ALU_ADD a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_SUB a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_AND a b => Z.max (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_OR a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign0 kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign0 kn a + ealign0 kn b)%Z 64
  | _ => 0%Z
  end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lins_e (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb k 0 then [] else [(k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then (let s := (k + k')%Z in if Z.eqb s 0 then rest else (s, a') :: rest)
      else (k', a') :: lins_e k a rest
  end.

Definition lsub_e (ts2 ts1 : list (Z * expr)) : list (Z * expr) := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+_S+2+P!1+A0$ts2;R1$ts1;R1!5'_Y10$t;R0$acc;R1!3'aF!1'T!3'_X+2+P#2!3'_[+2+P#2#1#2#1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint find_and_atom_k (sg : Z) (ts : list (Z * expr)) : option (expr * Z) :=
  match ts with
  | [] => None
  | (k, EAlu ALU_AND y (ELit mm)) :: r =>
      if (Z.eqb k sg && Z.ltb 0 mm && Z.eqb (Z.land (mm + 1) mm) 0)%bool then Some (y, mm) else find_and_atom_k sg r
  | _ :: r => find_and_atom_k sg r
  end.

Definition find_and_atom (ts : list (Z * expr)) : option (expr * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$ts;R!1+A!2+_S+2+P!2'aG!1,6,^Y#1").

Definition pageup_low_k (sg : Z) (e : expr) (m : Z) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S70!1'`7#2!2+_S+P+2!1+Q+2!2+_S+2+P!1+A3!2'^Q#1!1,6,^Y!1,S+2$sg;R+2$e;R+P$m;R+2&l;R0'_V-QRN$x;R!1+Q12!2'aG#4!3'_[+24#12$p;R1-_SRN$p;R!2+_S+P+22#11$y;R+P$mm;R+2-0RN$~R+02!2'_C!2'_C!2'^A,^5#5!2'`0!2'35#5,^5!2'^@5'_D2&ly;R0'_V&rest;R!3'aF!1'T#8!3,`5,aH#3!1,`3#2!3'_[+24#54-ARN$x;R!1+A32!5'_Y43$t;R3$acc;R4!3'aF!2'7#;!3'_X+2+P#2!3'_[+2+P#2#1!3'_[+24#2#12!2,R+2!2'3!2'^Q!3'_X+24#6!2'7#9!3'_X+24#2#7$p;R3$l0;R!1+A3666").

(* [comment removed for export] *)
Definition pageup_low (e : expr) (m : Z) : option Z :=
  match pageup_low_k 1 e m with
  | Some r => Some r
  | None => pageup_low_k (-1) e m
  end.

Definition pageup_align (e : expr) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S40!2+_S+P+2!1,6,^Y!3'_[+2!1+A!2+_S+2+P#1|10;$e;R+P&l;R!1'`7#1'_V-QRN$x;R!1+Q0+2-QRN$x;R!1+Q0!1+Q0!2'aG122$p;R0!2,R0#1!2'aG!1,`>,^Y22$p;R0-_SRN$p;R!2+_S+P+2+2#11$y;R+P$mm;R+2&m;R!2'^Q#11+2&k;R!1'aI#1+2-0RN$~R+0+2!2'_C!2'`0#2!2'5!1,63#1!2'^@#1!1,6|600;2-QRN$x;R!1+Q+2+2!2'aJ#7#22$z;R+2-2RN$z;R+2+2#13#2$p;R+aA,^5$p;R+aA,^5,^5,^5,^5").

Definition ealign (kn : list kentry) (e : expr) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$kn;R!1+A+a6$e;R+P!2'a3!2'aK!1'a=#2#1!1'aL#1").

(* [comment removed for export] *)
Definition lin_nowrap (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

(* [comment removed for export] *)
Definition srl_rem (e : expr) (m : Z) : expr := EAlu ALU_AND e (ELit (m - 1)%Z).

(* [comment removed for export] *)
Definition highmask_s (mk : Z) : option Z :=
  let m' := (mk mod two64)%Z in
  let s := Z.log2 (two64 - m') in
  if (Z.eqb (two64 - m') (2 ^ s) && Z.ltb 0 s && Z.ltb s 64)%bool then Some s else None.

Fixpoint srl_expand (kn : list kentry) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expand kn rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let m := (2 ^ ((s mod two64) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrap kn e)%bool then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((s mod two64) mod 64) (ealign kn e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          (* [comment removed for export] *)
          match highmask_s mk with
          | Some s =>
              if lin_nowrap kn e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.

(* [comment removed for export] *)
Fixpoint has_srl (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => false
  | (_, EAlu ALU_SRL _ (ELit _)) :: _ => true
  | _ :: rest => has_srl rest
  end.
(* [comment removed for export] *)
Definition sfact : Type := (list (Z * expr) * (Z * Z))%type.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sum_fact_x (allkn : list kentry) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expand allkn ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.

(* [comment removed for export] *)
Definition fact_nowrap (allkn : list kentry) (e : expr) (hi : Z) : bool :=
  let l := lin_of e in
  match lin_range (erange allkn) (fst l) (snd l) with
  | Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
  | None => false
  end.

Fixpoint sum_facts (allkn kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_facts allkn rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrap allkn e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_x allkn ts (lo - c)%Z (hi - c)%Z ++ sum_facts allkn rest
            else sum_facts allkn rest
        | _ => sum_facts allkn rest
        end
      end
  | _ :: rest => sum_facts allkn rest
  end.

(* [comment removed for export] *)
Fixpoint coef_of (a : expr) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, a') :: r => if expr_eqb a a' then k else coef_of a r
  end.

(* [comment removed for export] *)
Fixpoint fact_quot (fts ts : list (Z * expr)) (acc : option Z) : option Z :=
  match fts with
  | [] => acc
  | (k, a) :: r =>
      if Z.eqb k 0 then None else
      let K := coef_of a ts in
      if Z.eqb K 0 then None else
      if negb (Z.eqb (K mod k) 0) then None else
      let q := (K / k)%Z in
      match acc with
      | None => fact_quot r ts (Some q)
      | Some q0 => if Z.eqb q0 q then fact_quot r ts acc else None
      end
  end.

Definition sub_fact (q : Z) (fts ts : list (Z * expr)) : list (Z * expr) := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!2+_S+2+P!1+A0$q;R+2$fts;R1$ts;R1!5'_Y10$t;R0$acc;R1!3'aF!1'T!2'7#5!3'_X+2+P#2!3'_[+2+P#2#1#1#2").

(* [comment removed for export] *)
Fixpoint sum_subst (fs : list sfact) (ts : list (Z * expr)) (lo hi : Z) (hit : bool)
  : list (Z * expr) * (Z * Z) * bool :=
  match fs with
  | [] => (ts, (lo, hi), hit)
  | (fts, (flo, fhi)) :: r =>
      match fact_quot fts ts None with
      | Some q =>
          let ts' := sub_fact q fts ts in
          if Z.leb 0 q then sum_subst r ts' (lo + q * flo)%Z (hi + q * fhi)%Z true
          else sum_subst r ts' (lo + q * fhi)%Z (hi + q * flo)%Z true
      | None => sum_subst r ts lo hi hit
      end
  end.

Definition lin_test_rel (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S30!1+A!2+_S+2+P!2+_S+2+2!2+_S01$kn;R!1+A+a6$c;R+2$ts;R0$test;R%~R+2%~R+2+0-ARN$x;R!1+A'aM+0!2'aN#4#42,I$s;R'aM$l;R!1+A'aM-_SRN$x;R!2+_S2+0+0!5'aO!3,`K'aM#2#1#4,^5,^5,I1$p;R2$b;R+0-_SRN$p;R!2+_S01+0#21$ts';R0$p0;R1-_SRN$p0;R!2+_S+2+2+0#11$lo0;R+2$hi0;R+2-0RN$b;R+0+0#52-QRN$x;R!1+Q1+0!3'aP!1'aQ#<#;#42$p;R1-_SRN$p;R!2+_S+2+2+0#11$lo;R+2$hi;R+2!2#<!2'^Q#2#5!2'^Q#1#4,I,I").

Definition lin_test (kn : list kentry) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!2+_S+2+2$kn;R!1+A+a6$c;R+2$ts;R!1+A!2+_S+2+P$test;R%~R+2%~R+2+0-QRN$x;R!1+Q0+0!3'aP!1'aQ#4#3#22$p;R0-_SRN$p;R!2+_S+2+2+0#11$lo;R+2$hi;R+2-0RN$~R+0+0!2#4#2#12,H!4'aR#7#6#5#4!4'aR#4#3#2#1").

(* [comment removed for export] *)
Fixpoint srl_scale_need (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, EAlu ALU_SRL _ (ELit s)) :: rest => Z.max (((s mod two64) mod 64) - ctz64 k)%Z (srl_scale_need rest)
  | _ :: rest => srl_scale_need rest
  end.
Definition zcdiv (a b : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+2$b;R+2!1'T!2'4!1'T#2#1").
Definition lin_srange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   (* [comment removed for export] *)
    let sc := (2 ^ j)%Z in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expand kn ts in
    let '(c3, t3) := (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) in
    match lin_range (erange kn) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition lin_nowrapR (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expand kn (snd l) in            (* [comment removed for export] *)
  if lin_test kn (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else (* [comment removed for export] *)
    match lin_srange kn e with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint mentions_var (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar w => Nat.eqb v w
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if mentions_var v a then true else mentions_var v b
  | EExt _ _ _ a => mentions_var v a
  | EBlob _ _ _ _ => false
  end.
Fixpoint shares_var (e1 e2 : expr) : bool :=
  match e2 with
  | ELit _ => false
  | EVar w => mentions_var w e1
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if shares_var e1 a then true else shares_var e1 b
  | EExt _ _ _ a => shares_var e1 a
  | EBlob _ _ _ _ => false
  end.
Fixpoint novars (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if novars a then novars b else false
  | EExt _ _ _ a => novars a
  | EBlob _ _ _ _ => true
  end.
(* [comment removed for export] *)
Definition related (b1 b2 : expr) : bool :=
  if shares_var b1 b2 then true else novars b2.

(* [comment removed for export] *)
Definition lin_apart0 (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  (lin_nowrapR kn b1 && lin_nowrapR kn b2 &&
   let l1 := lin_of b1 in let l2 := lin_of b2 in
   lin_test kn (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
            (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.
Definition lin_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S00$kn;R!1+A+a6$b1;R+P$k1;R+2$n1;R+2$b2;R+P$k2;R+2$n2;R+2-0RN$~R+0+0!2'aS#6#32!7'aT#7#6#5#4#3#2#1,I").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zlit64 (z : Z) : Z := if (Z.leb 0 z && Z.ltb z two64)%bool then z else (z mod two64)%Z.

(* [comment removed for export] *)
Definition lin_brange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  match sum_facts kn kn with
  | [] => None
  | fs =>
      match sum_subst fs (snd l) 0 0 false with
      | (ts', (lo0, hi0), true) =>
          match lin_range (erange kn) (fst l) ts' with
          | Some (lo, hi) =>
              let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
              if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi') else None
          | None => None
          end
      | _ => None
      end
  end.

Definition xlo (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (lo, _) => Some lo
         | None => match lin_brange kn e with
                   | Some (lo, _) => Some lo
                   | None => match lin_srange kn e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
                   end
         end
  end.
Definition xhi (kn : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange kn e with
         | Some (_, hi) => Some hi
         | None => match lin_brange kn e with
                   | Some (_, hi) => Some hi
                   | None => match lin_srange kn e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
                   end
         end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xterms := list (expr * Z).

Fixpoint xt_nowrap (kn : list kentry) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapR kn e && xt_nowrap kn r end.
Fixpoint xt_const (ts : xterms) : Z :=
  match ts with [] => 0 | (e, k) :: r => (fst (lin_of e) + k + xt_const r)%Z end.
Fixpoint xt_lin (ts : xterms) : list (Z * expr) :=
  match ts with [] => [] | (e, _) :: r => fold_right (fun t acc => lins_e (fst t) (snd t) acc) (xt_lin r) (snd (lin_of e)) end.

(* [comment removed for export] *)
Definition lin_ge0_scaled (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expand kn ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) in
    lin_test kn (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.

(* [comment removed for export] *)
Fixpoint lin_align (al : expr -> Z) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 12%Z
  | (k, a) :: r => Z.min (Z.min 12 (ctzq k + Z.max 0 (al a))) (lin_align al r)
  end.
Definition lin_slack (al : expr -> Z) (c : Z) (ts : list (Z * expr)) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$al;R%~R+P+2$c;R+2$ts;R!1+A!2+_S+2+P!2'5!1,6|10;!2'a4!1'aC#2!2'aU#3#1").
Definition slack_test (al : expr -> Z) (c : Z) (ts : list (Z * expr)) : Z -> Z -> bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$al;R%~R+P+2$c;R+2$ts;R!1+A!2+_S+2+P$lo;R+2$~R+2-0RN$~R+0+0!2'^@,^5#22,H-0RN$~R+0+0!2'^@#2!1,`>|<000;2,I!2'^A!1'T!3'aV#5#4#3#2").
(* [comment removed for export] *)
Definition slack_test2 (al : expr -> Z) (c1 : Z) (t1 : list (Z * expr)) (c : Z) (ts : list (Z * expr)) : Z -> Z -> bool :=
  fun lo _ => if Z.leb 0 lo then true else if Z.leb lo (-4096) then false
              else if Z.ltb (- (lin_slack al c1 t1)) lo then true else Z.ltb (- (lin_slack al c ts)) lo.

(* [comment removed for export] *)
Definition lin_ge0 (kn : list kentry) (pos neg : xterms) : bool :=
  let al := ealign kn in   (* [comment removed for export] *)
  (xt_nowrap kn pos && xt_nowrap kn neg &&
   (* [comment removed for export] *)
   (let c1 := (xt_const pos - xt_const neg)%Z in let t1 := lsub_e (xt_lin pos) (xt_lin neg) in
    if lin_test kn c1 t1 (slack_test al c1 t1) then true
    else let '(c2, t2) := srl_expand kn t1 in
         if lin_test kn (c1 + c2)%Z t2 (slack_test2 al c1 t1 (c1 + c2)%Z t2) then true
         else (* [comment removed for export] *)
         if (if has_srl t2 then
               let '(c3, t3) := srl_expand kn t2 in
               lin_test kn (c1 + c2 + c3)%Z t3 (slack_test2 al c1 t1 (c1 + c2 + c3)%Z t3)
             else false) then true
         else (* [comment removed for export] *)
           lin_ge0_scaled kn c1 t1))%bool.

(* [comment removed for export] *)
Definition xinside0 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if lin_ge0 kn [(b1, k1)] [(b2, k2)] then lin_ge0 kn [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
(* [comment removed for export] *)
Definition xinside_num (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xlo kn b2, xhi kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match base_range kn b1, xhi kn n1, xlo kn n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition xinside (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if shares_var b1 b2 then xinside0 kn b1 k1 n1 b2 k2 n2
  else if novars b2 then
         (if xinside_num kn b1 k1 n1 b2 k2 n2 then true
          else match n1 with ELit _ => false | _ => xinside0 kn b1 k1 n1 b2 k2 n2 end)
       else false.


(* [comment removed for export] *)
Definition sub_itv (allkn : list kentry) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xlo allkn m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else (* [comment removed for export] *)
    if (Z.leb 0 n && Z.ltb n two64)%bool then xinside allkn b k (ELit n) (a_base c) (a_off c) m else false.

(* [comment removed for export] *)
Fixpoint kdisj_apart (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv allkn b1 k1 n1 c1 m1 then sub_itv allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv allkn b1 k1 n1 c2 m2 then sub_itv allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  end.

(* [comment removed for export] *)
Definition ranges_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if expr_eqb b2 b1 then (Z.leb (k1 + n1) k2 || Z.leb (k2 + n2) k1)%bool else
  if (match base_range kn b1, base_range kn b2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apart kn kn b1 k1 n1 b2 k2 n2 then true
  else lin_apart kn b1 k1 n1 b2 k2 n2.

Definition sub_itv_x (kn : list kentry) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S00$kn;R!1+A+a6$b;R+P$k;R+2$n;R+P$c;R+`M$m;R+P!7'aW#6#5#4#3!1'`S#2!1'`T#2#1").

Fixpoint kdisj_apart_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_x allkn b1 k1 n1 c1 m1 then sub_itv_x allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_x allkn b1 k1 n1 c2 m2 then sub_itv_x allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition end_hi (kn : list kentry) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
  match n with
  | ELit _ => None
  | _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
         then match find_range (facts_of kn) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
              | Some (_, ehi) => Some ehi
              | None => None
              end
         else None
  end.

Definition ranges_apart_x (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apart kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_range kn b1, base_range kn b2, xhi kn n1, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_x kn kn b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Record sprep := SPrep {
  sp_rng : option (Z * Z);          (* [comment removed for export] *)
  sp_h1 : option Z;                 (* [comment removed for export] *)
  sp_D : list (saddr * expr);       (* [comment removed for export] *)
  sp_Dx : list (saddr * expr) }.    (* [comment removed for export] *)

Fixpoint disj_sides (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides allkn rest b1 k1 n1 in
      let r1 := if sub_itv allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides allkn rest b1 k1 n1
  end.

Fixpoint disj_sides_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_x allkn rest b1 k1 n1 in
      let r1 := if sub_itv_x allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_x allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_x allkn rest b1 k1 n1
  end.

Fixpoint in_sides (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv allkn b2 k2 n2 c m then true else in_sides allkn r b2 k2 n2
  end.

Fixpoint in_sides_x (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_x allkn b2 k2 n2 c m then true else in_sides_x allkn r b2 k2 n2
  end.

(* [comment removed for export] *)
Definition xinside_num_br (kn : list kentry) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match xlo kn b2, xhi kn b2 with
  | Some lo2, Some hi2 =>
      if Z.eqb lo2 hi2 then
        match br1, xhi kn n1, xlo kn n2 with
        | Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
        | _, _, _ => false
        end
      else false
  | _, _ => false
  end.
Definition xinside_br (kn : list kentry) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 8 "S20!7'aX#;#9#8#7#6#5#4!7'aX#<#:#9#8#7#6#5$kn;R!1+A+a6$br1;R!1+Q!2+_S+2+2$b1;R+P$k1;R+2$n1;R+P$b2;R+P$k2;R+2$n2;R+P-0RN$~R+0+0!2'aS#6#32!7'aX#8#6#5#4#3#2#1-0RN$~R+0+0!1'aY#32-0RN$~R+0+0!8'aZ#8#7#6#5#4#3#2#12,H-PRN$n1;R+P+0#48$z;R+2,I$n;R+1!7'aX#9#7#6#5#4#3#2$op;R+J$a;R+P$b;R+P0$op;R+J$a;R+P$b;R+P0$op;R+G$a;R+P$b;R+P0$op;R+G$a;R+P$b;R+P0$sx;R+0$lo;R+1$n;R+1$e;R+P1$sx;R+0$k;R+1$i;R+2$n;R+11,I").
Definition sub_itv_br (allkn : list kentry) (br : option (Z * Z)) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S20!1'`S#2!1'`T#2$allkn;R!1+A+a6$br;R!1+Q!2+_S+2+2$b;R+P$k;R+2$n;R+2$c;R+`M$m;R+P-0RN$~R+0+0-0RN$~R+0+0!2'_C!2'`U#50!2'^@1#42-QRN$x;R!1+Q+2+0!2'a[#7#12$ml;R+2!2'^@!2'^Q#5#4!2'^Q!1'`T#3#1,I,I2,H-0RN$~R+0+0!2'_C!2'^@,^5#3!2'^A#3'_D2!8'a\#7#6#5#4!1,`3#301#1,I").
Definition sub_itv_x_br (kn : list kentry) (br : option (Z * Z)) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S00$kn;R!1+A+a6$br;R!1+Q!2+_S+2+2$b;R+P$k;R+2$n;R+P$c;R+`M$m;R+P!8'a\#7#6#5#4#3!1'`S#2!1'`T#2#1").
Fixpoint disj_sides_br (allkn : list kentry) (br : option (Z * Z)) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_br allkn br rest b1 k1 n1 in
      let r1 := if sub_itv_br allkn br b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_br allkn br b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_br allkn br rest b1 k1 n1
  end.
Fixpoint disj_sides_x_br (allkn : list kentry) (br : option (Z * Z)) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_x_br allkn br rest b1 k1 n1 in
      let r1 := if sub_itv_x_br allkn br b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_x_br allkn br b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_x_br allkn br rest b1 k1 n1
  end.
Fixpoint in_sides_br (allkn : list kentry) (br : option (Z * Z)) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_br allkn br b2 k2 n2 c m then true else in_sides_br allkn br r b2 k2 n2
  end.
Fixpoint in_sides_x_br (allkn : list kentry) (br : option (Z * Z)) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_x_br allkn br b2 k2 n2 c m then true else in_sides_x_br allkn br r b2 k2 n2
  end.
Lemma xinside_num_br_eq : forall kn b1 k1 n1 b2 k2 n2,
  xinside_num_br kn (base_range kn b1) b1 k1 n1 b2 k2 n2 = xinside_num kn b1 k1 n1 b2 k2 n2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$kn;R!1+A+a6$b1;R+P$k1;R+2$n1;R+P$b2;R+P$k2;R+2$n2;R+P!2,^:+0!7'b0#7#6#5#4#3#2#1").
Qed.
Lemma xinside_br_eq : forall kn b1 k1 n1 b2 k2 n2,
  xinside_br kn (base_range kn b1) b1 k1 n1 b2 k2 n2 = xinside kn b1 k1 n1 b2 k2 n2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$kn;R!1+A+a6$b1;R+P$k1;R+2$n1;R+P$b2;R+P$k2;R+2$n2;R+P!2,^:+0!7'aW#7#6#5#4#3#2#1").
Qed.
Lemma sub_itv_br_eq : forall allkn b k n c m, sub_itv_br allkn (base_range allkn b) b k n c m = sub_itv allkn b k n c m.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$allkn;R!1+A+a6$b;R+P$k;R+2$n;R+2$c;R+`M$m;R+P!2,^:+0!6'b1#6#5#4#3#2#1").
Qed.
Lemma sub_itv_x_br_eq : forall kn b k n c m, sub_itv_x_br kn (base_range kn b) b k n c m = sub_itv_x kn b k n c m.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$kn;R!1+A+a6$b;R+P$k;R+2$n;R+P$c;R+`M$m;R+P!2,^:+0!6'b2#6#5#4#3#2#1").
Qed.
Lemma disj_sides_br_eq : forall allkn kn b1 k1 n1, disj_sides_br allkn (base_range allkn b1) kn b1 k1 n1 = disj_sides allkn kn b1 k1 n1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SM0!1+A+a6!2+_S+`M+P!1+A1!3,`K+a6#1#3!5'b5#>#8#<#;#:!2'b4#>#<!6'^?24$l;R2!3+^;2#1!5'b5#?#9#=#<#;!2,^:24!6'b3#>5#8#<#;#:#7!3,`K+a6!3,b6#3#2#1#8!5'b5#<#6#:#9#8!2'b4#<#:!6'^?28$l;R2!3+^;2#1!5'b5#=#7#;#:#9!2,^:28!6'b3#<9#6#:#9#8#5!3,`K+a6!2,b7#2#1#6!3,`K+a6!3,b8#3#2#1#8!3,`K+a6!2,b9#2#1#6!3,`K+a6!2,b:#2#1#6!3,`K+a6!3,b;#3#2#1#8!3,`K+a6!2,b<#2#1#6!5'b5#@#:#>#=#<!2'b4#A#?!4,_W+`M+P#3#2!4,_W+`M+P#5#4-0RN$~R+02!7'b=#AB#?#>#=#3#22!3,`K1D#1#1!5'b5#A#;#?#>#=-0RN$~R+02!6'b1#A#?#>#=#3#22!3,`K1DFF-0RN$~R+02!6'b1#@#>#=#<#2#12!3,`K1!4,_W+`M+P#4#3AA!2'b4#@#>!3,`K+a6!4,b>#4#3#2#1#:!3,`K+a6!3,b?#3#2#1#8!3,`K+a6!2,b@#2#1#6$allkn;R0$kn;R0$b1;R+P$k1;R+2$n1;R+2!5'a:+a6$kn;R0!3+^;2!6'b3#6!2'b4#6#4#1#4#3#2!5'b5#6#1#4#3#2!2,^:2!5'b5#5!1,W+a6#3#2#1$K;R+a6$rest;R0$IH;R!3+^;2!6'b3#7!2'b4#7#5#1#5#4#3!5'b5#7#1#5#4#3-a6RN$k;R+a6!3+^;2!6'b3#9!2'b4#9#73#7#6#5!5'b5#93#7#6#5#3:$a;R+`M$w;R+1$v;R+P!3$a;R+`M$w;R+1$v;R+Pvd6!3+^;2!6'b3#>57#<#;#:!5'b5#>7#<#;#:#3#2#1$a;R+`M$n;R+P!2$a;R+`M$n;R+Pvd:!3+^;2!6'b3#<9;#:#9#8!5'b5#<;#:#9#8#2#1$a;R+`M$n;R+P$k;R+1!3$a;R+`M$n;R+P$k;R+1vd6!3+^;2!6'b3#>5<#<#;#:!5'b5#><#<#;#:#3#2#1$lo;R+2$hi;R+2!2$lo;R+2$hi;R+2vd:!3+^;2!6'b3#<9=#:#9#8!5'b5#<=#:#9#8#2#1$e;R+P$m;R+2!2$e;R+P$m;R+2vd:!3+^;2!6'b3#<9>#:#9#8!5'b5#<>#:#9#8#2#1$e;R+P$lo;R+2$hi;R+2!3$e;R+P$lo;R+2$hi;R+2vd6!3+^;2!6'b3#>5?#<#;#:!5'b5#>?#<#;#:#3#2#1$a;R+`M$n;R+P!2$a;R+`M$n;R+Pvd:!3+^;2!6'b3#<9@#:#9#8!5'b5#<@#:#9#8#2#1$a1;R+`M$n1;R+P$a2;R+`M$n2;R+P!4$a1;R+`M$n0;R+P$a2;R+`M$n2;R+Pvd!6'^?2A$l;R2!3+^;2-0RN$~R+02!7'b=#AB#?#>#=#5#42!3,`K1CEE-0RN$~R+02!6'b1#A#?#>#=#5#42!3,`K1CGG!2,^:2-0RN$~R+02!6'b1#@#>#=#<#4#32!3,`K1!4,_W+`M+P#2#1HH!6'b3#@I#:#>#=#<#9!3+^;2!6'b3#@IJ#>#=#<!5'b5#@J#>#=#<#4#3#2#1$a;R+`M$n;R+P$c;R+2!3$a;R+`M$n;R+P$c;R+2vd6!3+^;2!6'b3#>5K#<#;#:!5'b5#>K#<#;#:#3#2#1$a;R+`M$n;R+P!2$a;R+`M$n;R+Pvd:!3+^;2!6'b3#<9L#:#9#8!5'b5#<L#:#9#8#2#1#4").
Qed.
Lemma disj_sides_x_br_eq : forall allkn kn b1 k1 n1, disj_sides_x_br allkn (base_range allkn b1) kn b1 k1 n1 = disj_sides_x allkn kn b1 k1 n1.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SM0!1+A+a6!2+_S+`M+P!1+A1!3,`K+a6#1#3!5'bB#>#8#<#;#:!2'b4#>#<!6'^?24$l;R2!3+^;2#1!5'bB#?#9#=#<#;!2,^:24!6'bA#>5#8#<#;#:#7!3,`K+a6!3,b6#3#2#1#8!5'bB#<#6#:#9#8!2'b4#<#:!6'^?28$l;R2!3+^;2#1!5'bB#=#7#;#:#9!2,^:28!6'bA#<9#6#:#9#8#5!3,`K+a6!2,b7#2#1#6!3,`K+a6!3,b8#3#2#1#8!3,`K+a6!2,b9#2#1#6!3,`K+a6!2,b:#2#1#6!3,`K+a6!3,b;#3#2#1#8!3,`K+a6!2,b<#2#1#6!5'bB#@#:#>#=#<!2'b4#A#?!4,_W+`M+P#3#2!4,_W+`M+P#5#4-0RN$~R+02!7'bC#AB#?#>#=#3#22!3,`K1D#1#1!5'bB#A#;#?#>#=-0RN$~R+02!6'b2#A#?#>#=#3#22!3,`K1DFF-0RN$~R+02!6'b2#@#>#=#<#2#12!3,`K1!4,_W+`M+P#4#3AA!2'b4#@#>!3,`K+a6!4,b>#4#3#2#1#:!3,`K+a6!3,b?#3#2#1#8!3,`K+a6!2,b@#2#1#6$allkn;R0$kn;R0$b1;R+P$k1;R+2$n1;R+P!5'a:+a6$kn;R0!3+^;2!6'bA#6!2'b4#6#4#1#4#3#2!5'bB#6#1#4#3#2!2,^:2!5'bB#5!1,W+a6#3#2#1$K;R+a6$rest;R0$IH;R!3+^;2!6'bA#7!2'b4#7#5#1#5#4#3!5'bB#7#1#5#4#3-a6RN$k;R+a6!3+^;2!6'bA#9!2'b4#9#73#7#6#5!5'bB#93#7#6#5#3:$a;R+`M$w;R+1$v;R+P!3$a;R+`M$w;R+1$v;R+Pvd6!3+^;2!6'bA#>57#<#;#:!5'bB#>7#<#;#:#3#2#1$a;R+`M$n;R+P!2$a;R+`M$n;R+Pvd:!3+^;2!6'bA#<9;#:#9#8!5'bB#<;#:#9#8#2#1$a;R+`M$n;R+P$k;R+1!3$a;R+`M$n;R+P$k;R+1vd6!3+^;2!6'bA#>5<#<#;#:!5'bB#><#<#;#:#3#2#1$lo;R+2$hi;R+2!2$lo;R+2$hi;R+2vd:!3+^;2!6'bA#<9=#:#9#8!5'bB#<=#:#9#8#2#1$e;R+P$m;R+2!2$e;R+P$m;R+2vd:!3+^;2!6'bA#<9>#:#9#8!5'bB#<>#:#9#8#2#1$e;R+P$lo;R+2$hi;R+2!3$e;R+P$lo;R+2$hi;R+2vd6!3+^;2!6'bA#>5?#<#;#:!5'bB#>?#<#;#:#3#2#1$a;R+`M$n;R+P!2$a;R+`M$n;R+Pvd:!3+^;2!6'bA#<9@#:#9#8!5'bB#<@#:#9#8#2#1$a1;R+`M$n1;R+P$a2;R+`M$n2;R+P!4$a1;R+`M$n0;R+P$a2;R+`M$n2;R+Pvd!6'^?2A$l;R2!3+^;2-0RN$~R+02!7'bC#AB#?#>#=#5#42!3,`K1CEE-0RN$~R+02!6'b2#A#?#>#=#5#42!3,`K1CGG!2,^:2-0RN$~R+02!6'b2#@#>#=#<#4#32!3,`K1!4,_W+`M+P#2#1HH!6'bA#@I#:#>#=#<#9!3+^;2!6'bA#@IJ#>#=#<!5'bB#@J#>#=#<#4#3#2#1$a;R+`M$n;R+P$c;R+2!3$a;R+`M$n;R+P$c;R+2vd6!3+^;2!6'bA#>5K#<#;#:!5'bB#>K#<#;#:#3#2#1$a;R+`M$n;R+P!2$a;R+`M$n;R+Pvd:!3+^;2!6'bA#<9L#:#9#8!5'bB#<L#:#9#8#2#1#4").
Qed.
Lemma in_sides_br_eq : forall allkn D b2 k2 n2, in_sides_br allkn (base_range allkn b2) D b2 k2 n2 = in_sides allkn D b2 k2 n2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!2+_S+`M+P!1+A0!3,`K0#3#2!5'bE#<#2#:#9#8!2'b4#<#:!3,`K0!4,_W+`M+P#4#3#2$allkn;R!1+A+a6$D;R1$b2;R+P$k2;R+2$n2;R+2!5'a:0$D;R1!3+^;+0!6'bD#6!2'b4#6#4#1#4#3#2!5'bE#6#1#4#3#2!2,^:+0!5'bE#5!1,W0#3#2#1$a;R0-_SRN$p;R!2+_S+`M+P%l;R1%~R!3+^;+0!6'bD#8!2'b4#8#6#1#6#5#4!5'bE#8#1#6#5#4!3+^;+0!6'bD#9!2'b4#9#72#7#6#5!5'bE#92#7#6#5#11$s;R+`M$e;R+P!2$c;R+`M$m;R+P$r;R1$IH;R!3+^;+0!6'bD#;!2'b4#;#9#1#9#8#7!5'bE#;#1#9#8#7vd!6'^?+03$b;R+0!3+^;+0-0RN$~R+0+0!7'b=#=!2'b4#=#;#;#:#9#5#42,H#1-0RN$~R+0+0!6'b1#=#;#:#9#5#42,H!5'bE#=#3#;#:#9!2,^:+0-0RN$~R+0+0!6'b1#<#:#9#8#4#32,H3!6'bD#<4#2#:#9#8#1!3+^;+0!6'bD#<45#:#9#8!5'bE#<5#:#9#8#2#1#4").
Qed.
Lemma in_sides_x_br_eq : forall allkn D b2 k2 n2, in_sides_x_br allkn (base_range allkn b2) D b2 k2 n2 = in_sides_x allkn D b2 k2 n2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!2+_S+`M+P!1+A0!3,`K0#3#2!5'bG#<#2#:#9#8!2'b4#<#:!3,`K0!4,_W+`M+P#4#3#2$allkn;R!1+A+a6$D;R1$b2;R+P$k2;R+2$n2;R+P!5'a:0$D;R1!3+^;+0!6'bF#6!2'b4#6#4#1#4#3#2!5'bG#6#1#4#3#2!2,^:+0!5'bG#5!1,W0#3#2#1$a;R0-_SRN$p;R!2+_S+`M+P%l;R1%~R!3+^;+0!6'bF#8!2'b4#8#6#1#6#5#4!5'bG#8#1#6#5#4!3+^;+0!6'bF#9!2'b4#9#72#7#6#5!5'bG#92#7#6#5#11$s;R+`M$e;R+P!2$c;R+`M$m;R+P$r;R1$IH;R!3+^;+0!6'bF#;!2'b4#;#9#1#9#8#7!5'bG#;#1#9#8#7vd!6'^?+03$b;R+0!3+^;+0-0RN$~R+0+0!7'bC#=!2'b4#=#;#;#:#9#5#42,H#1-0RN$~R+0+0!6'b2#=#;#:#9#5#42,H!5'bG#=#3#;#:#9!2,^:+0-0RN$~R+0+0!6'b2#<#:#9#8#4#32,H3!6'bF#<4#2#:#9#8#1!3+^;+0!6'bF#<45#:#9#8!5'bG#<5#:#9#8#2#1#4").
Qed.

Definition mk_sprep (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : sprep := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S20!2+_S+`M+P!1,W0$kn;R!1+A+a6$b1;R+P$k1;R+2$n1;R+P&br;R!2'b4#4#3!1+Q!2+_S+2+2!4,bH#1!2'bI#5#2-PRN$n1;R+P!1+A0#28$z1;R+2!6'b3#6#2#6#5#4!1'bJ#1$n;R+11$op;R+J$a;R+P$b;R+P1$op;R+J$a;R+P$b;R+P1$op;R+G$a;R+P$b;R+P1$op;R+G$a;R+P$b;R+P1$sx;R+0$lo;R+1$n;R+1$e;R+P1$sx;R+0$k;R+1$i;R+2$n;R+11!6'bA#5#1#5#4#3#2").

(* [comment removed for export] *)
Definition ranges_apart_p (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  let br2 := base_range kn b2 in   (* [comment removed for export] *)
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if expr_eqb b2 b1 then (Z.leb (k1 + m1) k2 || Z.leb (k2 + m2) k1)%bool else   (* [comment removed for export] *)
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides_br kn br2 (sp_D sp) b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x_br kn br2 (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ptree (A : Type) : Type := PTLeaf | PTNode (l : ptree A) (o : option A) (r : ptree A).
Arguments PTLeaf {A}. Arguments PTNode {A} _ _ _.
Fixpoint pt_get {A} (t : ptree A) (k : positive) {struct k} : option A :=
  match t with
  | PTLeaf => None
  | PTNode l o r => match k with xH => o | xO k' => pt_get l k' | xI k' => pt_get r k' end
  end.
Fixpoint pt_set {A} (k : positive) (v : A) (t : ptree A) {struct k} : ptree A :=
  match t with
  | PTLeaf => match k with
              | xH => PTNode PTLeaf (Some v) PTLeaf
              | xO k' => PTNode (pt_set k' v PTLeaf) None PTLeaf
              | xI k' => PTNode PTLeaf None (pt_set k' v PTLeaf)
              end
  | PTNode l o r => match k with
                    | xH => PTNode l (Some v) r
                    | xO k' => PTNode (pt_set k' v l) o r
                    | xI k' => PTNode l o (pt_set k' v r)
                    end
  end.
Lemma pt_gss : forall A (k : positive) (v : A) t, pt_get (pt_set k v t) k = Some v.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SH3lcd;gbKd;lcd;gbLd;<scd;!1+Q#5%v;R#3%t;R!1+bN#4!3+^;0!3'bL#5!4'bK#5#3#2#1#3!2,R#5#2!1+bN#5!1+Q#7!1,bO#5!2,R#7#3!1,bP#6!2#3#26!1+Q#6!1,bO#4!2,R#6#2!1+bN#9!1+Q#:!1+bN#;!1+Q#<!1,bO#:!4,bQ#<#3#2#1!2,R#<#8!1,bR#5!1,bR#4!1,bR#:!1+Q#4!2,R#4#2!2,R#:#8$A;R{cd;$k;R+aA!5'bM$k;R+aA1$k;R+aA$IHk;R1$v;R#4$t;R2-bNRN$p;R!1+bN#6!3+^;3!3'bL#7!4'bK#74#3#145#12vd7!3+^;8!3'bL#6!4'bK#69#269:$l;R!1+bN#6$o;R!1+Q#7$r;R!1+bN#8!3$t1;R;$o;R<$t2;R=vd!2#9#8#1!3+^;>!3'bL#<!4'bK#<?#8@?A#3#2#1$k;R+aA$IHk;R1$v;R#4$t;R2-bNRN$p;R!1+bN#6!3+^;3!3'bL#7!4'bK#7B#3#1B5#12vd7!3+^;8!3'bL#6!4'bK#6C#26C:$l;R!1+bN#6$o;R!1+Q#7$r;R!1+bN#8!3$t1;R;$o;R<$t2;R=vd!2#9#8#3!3+^;>!3'bL#<!4'bK#<D#8@DA#3#2#1$v;R#2$t;R!1+bN#3-bNRN$p;R!1+bN#4!3+^;0!3'bL#5!4'bK#5,^Y#3#1,^Y!2,R#5#3#12vd!2,^:EF!3+^;E!3'bL#4!4'bK#4,^Y#2!1,bP#4,^YF$l;R!1+bN#4$o;R!1+Q#5$r;R!1+bN#6!3$t1;R!1+bN#7$o;R!1+Q#8$t2;R;vd!2,^:<G!3+^;<!3'bL#:!4'bK#:,^Y#8!4,bQ#:#3#2#1,^YG#3#2#1#1").
Qed.
Lemma pt_gso : forall A (k k' : positive) (v : A) t, k <> k' -> pt_get (pt_set k' v t) k = pt_get t k.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`?4lcd;gbKd;lcd;gbLd;lcd;g^?d;<scd;!1+bN#5!1'^P!3+^;+aA#4#3!1+Q#7!4'bK#7#4#3#2%k';R+aA%v;R#4%t;R0%~R1!3+^;2!3'bL#73#5!3'bL#7#2#5!1+bN#7!1,bO#6!1+Q#9!4'bK#9#4#3#2!1,bO#7!3'bL#9#29!1+bN#8!1,bO#8!1,bO#4!1+Q#;!1,bO#5!4'bK#;?#4#2!1,bO#9!3'bL#;#2A!1,bO#3!1'^P!3+^;+aA9C!1+Q#:!1,bP#:!3'bL#:F#8!1,S#;$o;RE!3+^;>#1H%k';R+aA%v;R#<%t;R!1+bN#=%~R1!3+^;!1+Q#?!3'bL#?!4'bK#?#4#3#2#5!3'bL#?#2#5!1,bO#2!1+Q#=!3+^;L!3'bL#=!1,bP#=#3!1,S#=!1+bN#>!1'^P!3+^;+aA=#3!1+Q#@!4'bK#@#4#3#2%k';R+aA%v;R#=%t;RN%~RO!3+^;P!3'bL#@Q?!3'bL#@#2?!1,bOK!1+Q#>!2,^:T!1,S#>!1,bR#4!1'^P!3+^;+aAV#3!1,bR#5%k';R+aA%v;R#=%t;RN%~RW!3+^;P!3'bL#@QX!3'bL#@#2X!1,bR#2!1,bOZ!1+bN#<!1'^P!3+^;+aA,^Y#3!4'bK#>#4#3#2%k';R+aA%v;R#;%t;R\%~R^0!3+^;T!3'bL#>^1,^Y!3'bL#>#2,^Y|11;!1+Q#<!2,^:^4!1,S#<!3'bL#:!4'bK#:#4#3F#8!3+^;+aA#8#4%~R+aA+aA$f;R^8!1#1#:!2,^:^8,bO!2'a;+_7!1#3#1!1'^P^7!4'bK#:=#3F!3'bL#:F<!1,bO#=!1'^P!3+^;+aA^?A!3'bL#@#2#>!1+Q#A%k';R+aA%v;R#B%t;R!1+bN#C%~R1!3+^;!1+Q#E!3'bL#E!4'bK#E#4#3#2#5!3'bL#E#2#5!1,bO#<!1+Q#C!3'bL#C#5#3!1+bN#D!1+Q#F!4'bK#F#4#3#2%k';R+aA%v;R#C%t;R^G%~RO!3+^;^H!3'bL#F^I?!3'bL#F#2?!1+Q#D%k';R+aA%v;R#C%t;R^G%~RW!3+^;^H!3'bL#F^IX!3'bL#F#2X!1,bR#3%k';R+aA%v;R#A%t;R!1+bN#B%~R^0!3+^;^K!3'bL#D!4'bK#D#4#3#2,^Y!3'bL#D#2,^Y!1,bO#;!1+Q#B!3+^;+aA#>#:!1,bO#?$f;R^8!1#1#@!1'^P^Q!1,bO#:!4,bQ#@#4#3#2!4'bK#@^U#9^V!1,bO#>!3'bL#@^V^X!4'bK#;X#4#2!1'^P!3+^;+aA9^M!1,bR#6!1,bR#7!4'bK#:V#3F!1,bR#9!1'^P!3+^;+aA^?_2!1,bR#:!4'bK#@_4#9^V!1+bN#6!4'bK#9,^Y#4#2!1'^P!3+^;+aA?,^Y%k';R+aA%v;R#:%t;R!1+bN#;%~R1!3+^;L!3'bL#=!4'bK#=#4#3#2#5!3'bL#=#2#5!3+^;>!3'bL#;!1,bP#;#3H%k';R+aA%v;R#;%t;R\%~RO!3+^;T!3'bL#>^1?!3'bL#>#2?%k';R+aA%v;R#;%t;R\%~RW!3+^;T!3'bL#>^1X!3'bL#>#2X!1+bN#:%k';R+aA%v;R#9%t;R_=%~R^0!3+^;^4!3'bL#<!4'bK#<#4#3#2,^Y!3'bL#<#2,^Y!2,^:E!1,S#:!1+Q#8!1,bP#8!4'bK#8,^Y#3_A!1'^P!3+^;+aA^O,^Y!4,bQ#>#4#3#2!4'bK#>,^Y#9_D!3'bL#9#2_0!1,bR#8!3'bL#;#2_2!1'^P!3+^;+aA_0C!1,bRK!1,bRZ|10;!3'bL#:F_G!1,bR#=!1'^P!3+^;+aA_NA!3'bL#@#4#>!1,bR#>!3'bL#@^V_Q!1'^P!3+^;+aA_0^M!2,^:^8,bR!1'^P!3+^;+aA_N_2!1,bR#<!3'bL#C#7#3!1,bR#;!1,bR#?!1'^P!3+^;+aAX,^Y!1'^P!3+^;+aA_X,^Y!3'bL#7#2,^Y!3'bL#9#2,^Y!1'^P!3+^;+aA,^YC!2,^:_@!1,S#8!3'bL#8_A,^Y!1'^P!3+^;+aA,^YA!2,^:T#3!3'bL#>_D,^Y!1'^P!3+^;+aA,^Y^M!1'^P!3+^;+aA,^Y_2!3+^;+aA,^Y,^Y!1'^P`9!2,^:+aA,^Y!1#2#1!1,bP#6!4,bQ#<#4#3#2$A;R{cd;$k;R+aA!5'bM$k;R+aA4$k;R+aA$IHk;R4$k';R+aA-aARN$p;R+aA%v;R#6%t;R5%~R!1'^P!3+^;+aA6#3!3+^;7!3'bL#989:#13$p;R+aA!1$k';R+aA$v;R#7$t;R;-bNRN$p;R!1+bN#9%~R!1'^P!3+^;+aA<=!3+^;>!3'bL#;@AB#12vd$~RD!6'^?EGI!2-aARN$p;R+aA%IHk;RJ%H;R!1'^P!3+^;+aAK6M#83$p;R+aA!1$k;R+aA$IHk;RR$H;R!1'^P!3+^;+aAS9U#1$p;R+aA!1$k;R+aA$IHk;RY$H;R!1'^P!3+^;+aA[9U#1$IHk;R^2$H;R!1'^P!3+^;+aA^3?^5#7#1^6!4#7#4#3Fvd$H0;R^7&Heq;R!6'bS+aAAA?!6'bT^8+aA^9,bO,bO^:!6'bT+aA+aA,bO#9#5#1!3+^;+aAA?^;^<%~RD!3+^;E!3'bL#:^=<^>$l;R!1+bN#9$o;R!1+Q#:$r;R!1+bN#;!3$t1;R\$o;RL$t2;RNvd$~R^@!6'^?P^A$o;RP!3+^;^B#1!3'bL#A#3#?!2-aARN$p;R+aA%IHk;R^C%H;R!1'^P!3+^;+aAK^D!3+^;^E^F^F#>3$p;R+aA!1$k;R+aA$IHk;R^J$H;R!1'^P!3+^;+aAS^?!2,^:^K!3'bL#D#6C#1$p;R+aA!1$k;R+aA$IHk;R^L$H;R!1'^P!3+^;+aA[^?!2,^:^K!3'bL#D#6^M#1$IHk;R^N$H;R!1'^P!3+^;+aA^3^O!2,^:^P!3'bL#B#4,^Y#=#1!3'bL#@!4'bK#@#:#9#2#>!4#=#:#9#2vd$H0;R^Q&Heq;R!6'bS+aA^R^R^O!6'bT^8+aA^S,bO,bO^:!6'bT+aA+aA,bO#?#;#1!3+^;+aA^R^O^;^T%~R^@!3+^;P!3'bL#@^W^X^Y#3#2#1#1$p;R+aA!1$k';R+aA$v;R#7$t;R;-bNRN$p;R!1+bN#9%~R!1'^P!3+^;+aA<V!3+^;>!3'bL#;^ZAB#12vd$~R^[!2-aARN$p;R+aA%IHk;RJ%H;R!1'^P!3+^;+aAK^\M#83$p;R+aA!1$k;R+aA$IHk;RR$H;R!1'^P!3+^;+aAS_0U#1$p;R+aA!1$k;R+aA$IHk;RY$H;R!1'^P!3+^;+aA[_0U#1$IHk;R^2$H;R!1'^P!3+^;+aA^3X^5#7#1%~R^[!3+^;E!3'bL#:_1<^>$l;R!1+bN#9$o;R!1+Q#:$r;R!1+bN#;!3$t1;R\$o;RL$t2;RNvd$~R_3!2,^:P^A%~R_3!3+^;P!3'bL#@_5^X^Y#3#2#1#1$v;R#5$t;R_6-bNRN$p;R!1+bN#7%~R!1'^P!3+^;+aA6,^Y!3+^;7!3'bL#9_79:#12vd$~R_8!2-aARN$p;R+aA%IHk;R_9%H;R!1'^P!3+^;+aAK,^Y_:#63$p;R+aA!1$k;R+aA$IHk;R_;$H;R!1'^P!3+^;+aAS,^Y^5#1$p;R+aA!1$k;R+aA$IHk;R_<$H;R!1'^P!3+^;+aA[,^Y^5#1$IHk;R_>$H;R!1'^P!3+^;+aA^3,^Y_?#5#1%~R_8!3+^;_@!3'bL#8_B6!3'bL#8_A6$l;R!1+bN#7$o;R!1+Q#8$r;R!1+bN#9!3$t1;R_=$o;R>$t2;R\vd$~R_C!2,^:T!3'bL#>#2#<%~R_C!3+^;T!3'bL#>_E^D!3'bL#>_D^D#3#2#1$k;R+aA$IHk;R4$k';R+aA-aARN$p;R+aA%v;R#6%t;R5%~R!1'^P!3+^;+aA^\#3!3+^;7!3'bL#98_0_F#13$p;R+aA!1$k';R+aA$v;R#7$t;R;-bNRN$p;R!1+bN#9%~R!1'^P!3+^;+aA_G=!3+^;>!3'bL#;@_2_H#12vd$~R_I!2-aARN$p;R+aA%IHk;RJ%H;R!1'^P!3+^;+aAZ6M#83$p;R+aA!1$k;R+aA$IHk;RR$H;R!1'^P!3+^;+aA_J9U#1$p;R+aA!1$k;R+aA$IHk;RY$H;R!1'^P!3+^;+aA_K9U#1$IHk;R^2$H;R!1'^P!3+^;+aA_L?^5#7#1%~R_I!3+^;E!3'bL#:^=_G_M$l;R!1+bN#9$o;R!1+Q#:$r;R!1+bN#;!3$t1;R\$o;RL$t2;RNvd$~R_O!2,^:P_P%~R_O!3+^;P!3'bL#@^W_Q_R#3#2#1#1$p;R+aA!1$k';R+aA$v;R#7$t;R;-bNRN$p;R!1+bN#9%~R!1'^P!3+^;+aA_GV!3+^;>!3'bL#;^Z_2_H#12vd$~R_S!6'^?EGI!2-aARN$p;R+aA%IHk;RJ%H;R!1'^P!3+^;+aAZ^\M#83$p;R+aA!1$k;R+aA$IHk;RR$H;R!1'^P!3+^;+aA_J_0U#1$p;R+aA!1$k;R+aA$IHk;RY$H;R!1'^P!3+^;+aA_K_0U#1$IHk;R^2$H;R!1'^P!3+^;+aA_LX^5#7#1^6!4#7#4#3Fvd$H0;R^7&Heq;R!6'bS+aA_2_2X!6'bT^8+aA^9,bR,bR_T!6'bT+aA+aA,bR#9#5#1!3+^;+aA_2X^;^<%~R_S!3+^;E!3'bL#:_1_G_M$l;R!1+bN#9$o;R!1+Q#:$r;R!1+bN#;!3$t1;R\$o;RL$t2;RNvd$~R_U!6'^?P_P$o;RP!3+^;^B#1!3'bL#A#5#?!2-aARN$p;R+aA%IHk;R^C%H;R!1'^P!3+^;+aAZ_V!3+^;^E_W_W#>3$p;R+aA!1$k;R+aA$IHk;R^J$H;R!1'^P!3+^;+aA_J_N!2,^:^K!3'bL#D#8C#1$p;R+aA!1$k;R+aA$IHk;R^L$H;R!1'^P!3+^;+aA_K_N!2,^:^K!3'bL#D#8^M#1$IHk;R^N$H;R!1'^P!3+^;+aA_L_X!2,^:^P!3'bL#B#6,^Y#=#1!3'bL#@!4'bK#@#:#9#4#>!4#=#:#9#4vd$H0;R^Q&Heq;R!6'bS+aA_Y_Y_X!6'bT^8+aA^S,bR,bR_T!6'bT+aA+aA,bR#?#;#1!3+^;+aA_Y_X^;^T%~R_U!3+^;P!3'bL#@_5_Q_R#3#2#1#1$v;R#5$t;R_6-bNRN$p;R!1+bN#7%~R!1'^P!3+^;+aA^\,^Y!3+^;7!3'bL#9_7_0_F#12vd$~R_Z!2-aARN$p;R+aA%IHk;R_9%H;R!1'^P!3+^;+aAZ,^Y_:#63$p;R+aA!1$k;R+aA$IHk;R_;$H;R!1'^P!3+^;+aA_J,^Y^5#1$p;R+aA!1$k;R+aA$IHk;R_<$H;R!1'^P!3+^;+aA_K,^Y^5#1$IHk;R_>$H;R!1'^P!3+^;+aA_L,^Y_?#5#1%~R_Z!3+^;_@!3'bL#8_B^\!3'bL#8_A^\$l;R!1+bN#7$o;R!1+Q#8$r;R!1+bN#9!3$t1;R_=$o;R>$t2;R\vd$~R_[!2,^:T!3'bL#>#4#<%~R_[!3+^;T!3'bL#>_E_V!3'bL#>_D_V#3#2#1$k';R+aA-aARN$p;R+aA%v;R#4%t;R0%~R^0!3+^;2!3'bL#73,^Y_\#13$p;R+aA!1$k';R+aA$v;R#5$t;R_6-bNRN$p;R!1+bN#7%~R!1'^P!3+^;+aA,^Y=!3+^;7!3'bL#9!4'bK#9?#4#2,^Y`0#12vd$~R`1`2%~R`1!3+^;_@!3'bL#8!4'bK#8=#3_A,^Y`3$l;R!1+bN#7$o;R!1+Q#8$r;R!1+bN#9!3$t1;R_=$o;R>$t2;R\vd$~R`4`5%~R`4!3+^;T!3'bL#>!4'bK#>^U#9_D,^Y`6#3#2#1#1$p;R+aA!1$k';R+aA$v;R#5$t;R_6-bNRN$p;R!1+bN#7%~R!1'^P!3+^;+aA,^YV!3+^;7!3'bL#9!4'bK#9X#4#2,^Y`0#12vd$~R`7`2%~R`7!3+^;_@!3'bL#8!4'bK#8V#3_A,^Y`3$l;R!1+bN#7$o;R!1+Q#8$r;R!1+bN#9!3$t1;R_=$o;R>$t2;R\vd$~R`8`5%~R`8!3+^;T!3'bL#>!4'bK#>_4#9_D,^Y`6#3#2#1#1$v;R#3$t;R!1+bN#4-bNRN$p;R!1+bN#5%~R`:!3+^;2!3'bL#7!4'bK#7,^Y#4#2,^Y_\#12vd$~R`:&Heq;R`;`9!2'a;!3+^;2!2,R#7#4!1,S#7`<%~R`:!3+^;!1+Q#6!3'bL#6!4'bK#6,^Y#3`=,^Y!3'bL#6`=,^Y$l;R!1+bN#5$o;R!1+Q#6$r;R!1+bN#7!3$t1;R;$o;R7$t2;R_=vd$~R`:&Heq;R`;`9!2'a;!3+^;L!2,R#=#:#4`<%~R`:!3+^;^4!3'bL#<!4'bK#<,^Y#9`>,^Y!3'bL#<`>,^Y#3#2#1#1").
Qed.
Lemma pt_get_leaf : forall A (k : positive), pt_get (@PTLeaf A) k = None.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S12lcd;gbLd;<scd;!1$k;R+aA!2,^:!1+Q#4!1,S#4#1$A;R{cd;$k;R+aA-aARN$p;R+aA!3+^;!1+Q#3!3'bL#3!1,bP#3#1!1,S#3#13$p;R+aA0$p;R+aA0!2,^:!1+Q#2!1,S#2").
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive lres :=
| LHit (v : expr) (scs : list sidecond) (hints : list bool)
| LMiss (scs : list sidecond) (hints : list bool)     (* [comment removed for export] *)
| LStuck.

Fixpoint zbytes_le_to_Z (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Z.lor b (Z.shiftl (zbytes_le_to_Z rest) 8)
  end.

Definition lit_of_bytes (sx : bool) (n : nat) (bs : list Z) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$sx;R+0$n;R+1$bs;R!1+A+2!1,`3&u;R!1'bU#1+2-0RN$sx;R+0+2#42!2'9!2':!1,;|30;!1'<#3#1#1").

(* [comment removed for export] *)
Fixpoint log_byte_lit (log : list sentry) (rb : expr) (rk : Z) : option Z :=
  match log with
  | [] => None
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk 1 kb kk (Z.of_nat w) with
      | RInside d => match v with
                     | ELit z => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
                     | _ => None
                     end
      | RDisjoint => log_byte_lit rest rb rk
      | _ => None
      end
  end.

(* [comment removed for export] *)
Fixpoint log_bytes_lit (log : list sentry) (rb : expr) (rk : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match log_byte_lit log rb rk, log_bytes_lit log rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Fixpoint log_lookup (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookup kn rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookup kn rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookup kn rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint img_bytes (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' =>
      match seg_rom segs (Z_to_bv 64 a) with
      | Some b => match img_bytes segs (a + 1) n' with
                  | Some r => Some (bv_unsigned b :: r)
                  | None => None
                  end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition fill_lit (sx : bool) (n : nat) (c : Z) : expr :=
  lit_of_bytes sx n (repeat (c mod 256)%Z n).

(* [comment removed for export] *)
Fixpoint know_byte_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) : option Z :=
  match kn with
  | [] => None
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w (ELit z) =>
          match rel_lit rb rk 1 kb kk (Z.of_nat w) with
          | RInside d => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KZero (SA kb kk) (ELit l0) =>
          match rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)%Z with
          | RInside _ => Some 0%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KFill (SA kb kk) (ELit l0) c =>
          match rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)%Z with
          | RInside _ => Some (c mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.ltb rk hi)%bool then
                match seg_rom segs (Z_to_bv 64 rk) with
                | Some b => Some (bv_unsigned b)
                | None => None            (* [comment removed for export] *)
                end
              else know_byte_lit segs rest rb rk
          | _ => know_byte_lit segs rest rb rk
          end
      | _ => know_byte_lit segs rest rb rk
      end
  end.

(* [comment removed for export] *)
Fixpoint know_bytes_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) (n : nat)
  : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match know_byte_lit segs kn rb rk, know_bytes_lit segs kn rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Fixpoint know_lookupA0 (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0 allkn in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinside allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinside allkn rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (l0 mod 2^64)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (l0 mod 2^64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erange allkn len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match img_bytes segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.

(* [comment removed for export] *)
Definition know_lookupA (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match know_lookupA0 allkn segs kn rb rk n sx hints acc with
  | LMiss acc' hints' =>
      match know_bytes_lit segs kn rb rk n with
      | Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
      | None => LMiss acc' hints'
      end
  | r => r
  end.

Definition know_lookup (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres := ltac2:(Rpl.RP.run_i (rplG ()) 8 "S00$segs;R!1+A+bV$kn;R!1+A+a6$rb;R+P$rk;R+2$n;R+1$sx;R+0$hints;R!1+A+0$acc;R!1+A+bW!9'bX#7#8#7#6#5#4#3#2#1").

(* [comment removed for export] *)
Fixpoint coeffs_divk (kn : list kentry) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0) && coeffs_divk kn m rest)%bool
  end.

Definition lin_lowbits_kn (kn : list kentry) (e : expr) (k : Z) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!2'5!1,6|10;#2!1+A!2+_S+2+P$kn;R!1+A+a6$e;R+P$k;R+2&l;R!1'`7#2'_V-0RN$~R+0!1+Q+2!3'bY#40!3'_[+21#12!2,R+2!2'3!3'_X+21#10!2'aJ#30").   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.

(* [comment removed for export] *)
Fixpoint lsplit_divc (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divc m rest in
      if Z.eqb (k mod m) 0 then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

(* [comment removed for export] *)
Definition lin_nowrap_l (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  match lin_range (erange kn) c ts with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
  | None => false
  end.

Definition mkSrl (kn : list kentry) (a : expr) (s : Z) : expr :=
  let l := lin_of a in
  let m := (2 ^ s)%Z in
  if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrap kn a)%bool
  then unlin ((fst l / m)%Z, ldiv_terms m (snd l))     (* [comment removed for export] *)
  else
    (* [comment removed for export] *)
    match (if (negb (lin_trivial l) && lin_nowrap kn a)%bool then lsplit_divc m (snd l) else ([], [])) with
    | ((_ :: _) as dts, (_ :: _) as rts) =>
        match (if lin_nowrap_l kn (fst l) rts then erange kn (unlin (fst l, rts)) else None) with
        | Some (lo, hi) =>
            if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
            else mkAlu ALU_SRL a (ELit s)
        | None => mkAlu ALU_SRL a (ELit s)
        end
    | _ => mkAlu ALU_SRL a (ELit s)
    end.

(* [comment removed for export] *)
Fixpoint lowbits (kn : list kentry) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (2 ^ j)%Z in
  let dflt := if Z.leb j (ealign kn e) then Some 0%Z else lin_lowbits_kn kn e j in
  match e with
  | ELit z => Some ((z mod two64) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | _ => dflt
  end.

(* [comment removed for export] *)
Fixpoint lsplit_div (kn : list kentry) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_div kn m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

(* [comment removed for export] *)
Definition and_high_split (kn : list kentry) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
  let m := (2 ^ j)%Z in
  let cA := (c - c mod m)%Z in
  let r := unlin ((c mod m)%Z, rts) in
  match erange kn r with
  | Some (lo, hi) =>
      if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
      else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  | None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
  end.

Definition and_low_split (kn : list kentry) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S30!1+A!2+_S+2+P!2+_S+2+2!2'4#2#5$kn;R!1+A+a6$bk;R+P$j;R+2$c;R+2$rts;R0&m;R!2'5!1,6|10;#3+2&r;R!1'`;!4,_W+20!2'3#3#1#2+P-QRN$x;R!1+Q1+P!2'aQ#7#12$p;R1-_SRN$p;R!2+_S+2+2+P#11$lo;R+2$hi;R+2-0RN$~R+0+P!2'`02!2'4#1#52!1'`;!4,_W+20!2'^B!2'3#7#5!2'72#5#6!3'bZ,aH#4#9!3'bZ,aH#1#6").

(* [comment removed for export] *)
Definition mkAnd0 (kn : list kentry) (a b : expr) : expr :=
  match b with
  | ELit k =>
      let k' := (k mod two64)%Z in
      let j := Z.log2 (two64 - k') in
      if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool then
        (* [comment removed for export] *)
        (if Z.leb j (ealign kn a) then a
         else let l := lin_of a in
              if (negb (lin_trivial l) && coeffs_divk kn (2 ^ j) (snd l))%bool
              then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
              else (* [comment removed for export] *)
                match (if lin_trivial l then ([], snd l) else lsplit_div kn (2 ^ j) (snd l)) with
                | ((_ :: _) as dts, (_ :: _) as rts) => and_high_split kn b j (fst l) dts rts
                | _ => (* [comment removed for export] *)
                       mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrl kn a j)
                end)
      else
        let j2 := Z.log2 (k' + 1) in
        if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
          (* [comment removed for export] *)
          (if Z.leb j2 (ealign kn a) then ELit 0
           else match lowbits kn a j2 with        (* [comment removed for export] *)
           | Some v => ELit v
           | None =>
           if lin_trivial (lin_of a) then mkAlu ALU_AND a b
           else match lin_lowbits_kn kn a j2 with
                | Some v => ELit v
                | None => (* [comment removed for export] *)
                    match lsplit_div kn (2 ^ j2) (snd (lin_of a)) with
                    | (_ :: _, (_ :: _) as rts) => and_low_split kn b j2 (fst (lin_of a)) rts
                    | _ => mkAlu ALU_AND a b
                    end
                end
           end)
        else (* [comment removed for export] *)
          let j3 := (Z.log2 k' + 1)%Z in
          if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
            match lin_lowbits_kn kn a j3 with
            | Some v => ELit (Z.land v k')
            | None => mkAlu ALU_AND a b
            end
          else mkAlu ALU_AND a b
  | _ => mkAlu ALU_AND a b
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition narrow_mask (kn : list kentry) (a : expr) (k' : Z) : option Z :=
  let i := ctz64 k' in
  let m := (k' + 2 ^ i)%Z in
  let j := Z.log2 m in
  if (Z.ltb 0 k' && Z.eqb m (2 ^ j) && Z.ltb j 64)%bool then
    match xhi kn a with
    | Some h => if Z.ltb h (2 ^ j) then Some (two64 - 2 ^ i)%Z else None
    | None => None
    end
  else None.

Definition mkAnd (kn : list kentry) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S30!3'b\#4#3#2!3'b\#6#5#4!3'b\#7#6#5$kn;R!1+A+a6$a;R+P$b;R+P-PRN$b;R+P+P#18$k;R+2-QRN$x;R!1+Q+2+P!3'b[#4#3!2'3#1'_D2$m;R+2!3'b\#5#4!1,`3#10$n;R+10$op;R+J$a0;R+P$b0;R+P1$op;R+J$a0;R+P$b0;R+P1$op;R+G$a0;R+P$b0;R+P1$op;R+G$a0;R+P$b0;R+P1$sx;R+0$lo;R+1$n;R+1$e;R+P2$sx;R+0$k;R+1$i;R+2$n;R+12").

Definition mkAndK (kn : list kentry) (a b : expr) : expr :=
  match a, b with
  | EAlu ALU_AND x (ELit m1), ELit k => mkAnd kn x (ELit (Z.land (m1 mod two64) (k mod two64))%Z)
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
      (* [comment removed for export] *)
      let i' := ((i mod two64) mod 64)%Z in
      if Z.eqb (m mod two64) (2 ^ i') then mkAnd kn x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
      else mkAnd kn a b
  | _, _ => mkAnd kn a b
  end.

(* [comment removed for export] *)
Definition or_disjoint (kn : list kentry) (a b : expr) : bool :=
  match erange kn b with
  | Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealign kn a)))%bool
  | None => false
  end.

Definition mkOr (kn : list kentry) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (zalu ALU_OR x y)
  | _, _ =>
      if or_disjoint kn a b then mkAlu ALU_ADD a b
      else if or_disjoint kn b a then mkAlu ALU_ADD a b
      else (* [comment removed for export] *)
           match b with
           | ELit c => mkAlu ALU_ADD (mkAndK kn a (ELit (Z.lnot (c mod two64)))) (ELit c)
           | _ => match a with
                  | ELit c => mkAlu ALU_ADD (mkAndK kn b (ELit (Z.lnot (c mod two64)))) (ELit c)
                  | _ => EAlu ALU_OR a b
                  end
           end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Fixpoint closedb (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => closedb a && closedb b
  | EExt _ _ _ a => closedb a
  | EBlob _ _ _ _ => false
  end.

Fixpoint esubst (s r e : expr) : expr :=
  if expr_eqb e s then r else
  match e with
  | EAlu op a b => EAlu op (esubst s r a) (esubst s r b)
  | EAluw op a b => EAluw op (esubst s r a) (esubst s r b)
  | EMd op a b => EMd op (esubst s r a) (esubst s r b)
  | EMdw op a b => EMdw op (esubst s r a) (esubst s r b)
  | EExt sx lo n a => EExt sx lo n (esubst s r a)
  | _ => e
  end.

(* [comment removed for export] *)
Fixpoint eval_closed (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod two64)%Z
  | EVar _ => None
  | EAlu op a b => match eval_closed a, eval_closed b with
                   | Some x, Some y => Some (zalu op x y) | _, _ => None end
  | EAluw op a b => match eval_closed a, eval_closed b with
                    | Some x, Some y => Some (zaluw op x y) | _, _ => None end
  | EMd op a b => match eval_closed a, eval_closed b with
                  | Some x, Some y => Some (zmd op x y) | _, _ => None end
  | EMdw op a b => match eval_closed a, eval_closed b with
                   | Some x, Some y => Some (zmdw op x y) | _, _ => None end
  | EExt sx lo n a => match eval_closed a with
                      | Some x => Some (zext_lit sx lo n x) | None => None end
  | EBlob _ _ _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint subexprs (e : expr) : list expr :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => subexprs a ++ subexprs b ++ [e]
  | EExt _ _ _ a => subexprs a ++ [e]
  | _ => [e]
  end.

(* [comment removed for export] *)
Fixpoint all_eval_to (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match eval_closed (esubst s (ELit lo) e) with
           | Some w => if Z.eqb w v then all_eval_to s e v (lo + 1) c else false   (* [comment removed for export] *)
           | None => false
           end
  end.

Fixpoint evalS (s : expr) (z : Z) (e : expr) : option Z :=
  if expr_eqb e s then Some z else
  match e with
  | ELit w => Some (wrap64 w)
  | EVar _ => None
  | EAlu op a b => match evalS s z a with
                   | Some x => match evalS s z b with Some y => Some (zfast op x y) | None => None end
                   | None => None
                   end
  | EAluw op a b => match evalS s z a with
                    | Some x => match evalS s z b with Some y => Some (zfastw op x y) | None => None end
                    | None => None
                    end
  | EMd op a b => match evalS s z a with
                  | Some x => match evalS s z b with Some y => Some (zfastm op x y) | None => None end
                  | None => None
                  end
  | EMdw op a b => match evalS s z a with
                   | Some x => match evalS s z b with Some y => Some (zmdw op x y) | None => None end
                   | None => None
                   end
  | EExt sx lo n a => match evalS s z a with
                      | Some x => Some (zext_fast sx lo n x) | None => None end   (* [comment removed for export] *)
  | EBlob _ _ _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint all_eval_toS (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalS s (wrap64 lo) e with
           | Some w => if Z.eqb w v then all_eval_toS s e v (lo + 1) c else false
           | None => false
           end
  end.

(* [comment removed for export] *)
Definition probeS (s e : expr) (v z : Z) : bool :=
  match evalS s (wrap64 z) e with Some w => Z.eqb w v | None => false end.

Fixpoint memE (e : expr) (l : list expr) : bool :=
  match l with [] => false | x :: r => if expr_eqb e x then true else memE e r end.

Fixpoint nubE_acc (l acc : list expr) : list expr :=
  match l with
  | [] => []
  | x :: r => if memE x acc then nubE_acc r acc else x :: nubE_acc r (x :: acc)
  end.
Definition nubE (l : list expr) : list expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$l;R!1+A+P!2'c0#1!1,W+P").

Definition conc_limit : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,6|<000;").

(* [comment removed for export] *)
Fixpoint evalS_def (s e : expr) : bool :=
  if expr_eqb e s then true else
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if evalS_def s a then evalS_def s b else false
  | EExt _ _ _ a => evalS_def s a
  | EBlob _ _ _ _ => false
  end.

Fixpoint conc_try (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try kn e rest else
      if negb (evalS_def s e) then conc_try kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_try kn e rest
                else conc_try kn e rest
            | None => conc_try kn e rest
            end
          else conc_try kn e rest
      | None => conc_try kn e rest
      end
  end.

(* [comment removed for export] *)
Fixpoint conc_try_ref (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try_ref kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_try_ref kn e rest
                else conc_try_ref kn e rest
            | None => conc_try_ref kn e rest
            end
          else conc_try_ref kn e rest
      | None => conc_try_ref kn e rest
      end
  end.

Lemma evalS_def_None : forall s e z, evalS_def s e = false -> evalS s z e = None.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^@0!1+Q+2!1,S+2!1,`3#1!2,R+2#5!2,R+2!1'_Q#4!3+^;+0,H,I-0RN$b;R+0w#12+^F+_7!6'_2+0,H$e;R+06,`G,I#1$H;R5&H0;R7+_7!2'a;!3+^;031#1!1,`L#1!3+^;+0-0RN$~R+0+0#12,H,I,I!3+^;+0,I,I!2,^:01$H;R;<%~R!3+^;+0!2'c2#5#1,I!3+^;0!3'c3#6#4#21%~R!3+^;+0!2'c2#7#1,I!3+^;0!3'c3#8#6#21!3,`5#5#4#2!2'c2#:#6!2'c2#:#4!3+^;+0-0RN$~R+0+0#12,H-0RN$~R+0+0A2B,I,I!2,R+2#9!3'c3#;#9#7!3'c3#<#:#6!2'a;!3+^;0D1#1$H;R5&H0;R7+_7G!2'c2#9#3!3+^;+0-0RN$~R+0+0!2'c2#9#52I,I,I!2,^:+0#1!3+^;+0!2'c2#;#7#1!3+^;+0!2'c2#=#9#1!3'c3#?#=#;%~R!3+^;+0#2,I!3+^;0N1!3+^;+0-0RN$~R+0+0#32!2'c2#?#9,I,I!3'c3#@#>#<!3'c3#A#?#;!2,R+2!3'c4#?#2#1-QRN$x;R!1+Q+20R2$y;R+2S1!2'c2#<#8!3+^;+0U,H!3+^;0!3'c3#>#<#:1%~R5W!3+^;+0!2'c2#>#8,I&o;RN0!1-QRN$o;R!1+Q+2%IHe1;R%~R5!3+^;0#21!3+^;0-QRN$x;R!1+Q+20#22$x;R+2111#12$z;R+2!1$z0;R+2$IHe1;R%~R5!3+^;0!2,R+2#21<#1$IHe1;R%~R5!3+^;011<#3!3'c3#?#=#9!1#8#1!3+^;+0U,I%~R;W!1#2!2,^:+0,I!3,`A#5#4#2!2,R+2!3'_P#?#2#1-QRN$x;R!1+Q+20R2$y;R+2^41!3,`1#5#4#2!2,R+2!3'_R#?#2#1-QRN$x;R!1+Q+20R2$y;R+2^71!3,`D#5#4#2!2,R+2!3'`C#?#2#1-QRN$x;R!1+Q+20R2$y;R+2^:1!4,c5#5#4#3#2!2,R+2!4'c6#9#8#7#1!4,c7#4#3#2#1!2,R+2#8$s;R+P$e;R+P$z;R+2!:'c1$e;R+P%~R!3+^;+0!2'c2#4#1,I!3+^;0!3'c3#5#3#21$z0;R+2vd&b;R!2'`U2#4+0-0RN$b;R+0%~R!3+^;+0-0RN$~R+0+0#12,H,H,I!3+^;0-0RN$~R+00#22341#128$H;R5&H0;R7+_7!2'a;!3+^;041#1%~R!3+^;+0!2'c2#42,I!3+^;0!3'c3#5#3!1,`3#21$n;R+1vd&b;R!2'`U9#4+0-0RN$b;R+0%~R:!3+^;0-0RN$~R+00#22311#128=%~R!3+^;+0!2'c2#49,I!3+^;0!3'c3#5#3!1,`L#21$op;R+J$e1;R+P$IHe1;R>$e2;R+P$IHe2;R?vd&b;R!2'`U@#8+0-0RN$b;R+0%~RC!3+^;0-0RN$~R+00#22D-QRN$x;R!1+Q+20E2$x;R+2-QRN$x;R!1+Q+20F2$y;R+2!2,R+2!3'c4#:#2#1111#12H$H;RJ&b;RA+0&E1;RKL!3-0RN$b;R+0%E1;RM%IHe1;RO%H;RP!3+^;0-QRN$x;R!1+Q+20Q2$x;R+2T11#22$E1;RV$IHe1;RX$H;RY!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20Q2$x;R+2-QRN$x;R!1+Q+20#22$y;R+2S111Z[\$E1;R^0$IHe1;R^1$H;R;!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20#12$x;R+2T11<N^2#1#7#3%~R!3+^;+0!2'c2#8@,I!3+^;0!3'c3#9#7!3,`5#6#5#31$op;R+J$e1;R+P$IHe1;R>$e2;R+P$IHe2;R?vd&b;R!2'`U^3#8+0-0RN$b;R+0%~RC!3+^;0-0RN$~R+00#22D-QRN$x;R!1+Q+20E2$x;R+2-QRN$x;R!1+Q+20F2$y;R+2!2,R+2!3'_P#:#2#1111#12H$H;RJ&b;RA+0&E1;RKL!3-0RN$b;R+0%E1;RM%IHe1;RO%H;RP!3+^;0-QRN$x;R!1+Q+20Q2$x;R+2^511#22$E1;RV$IHe1;RX$H;RY!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20Q2$x;R+2-QRN$x;R!1+Q+20#22$y;R+2^4111Z[\$E1;R^0$IHe1;R^1$H;R;!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20#12$x;R+2^511<N^2#1#7#3%~R!3+^;+0!2'c2#8^3,I!3+^;0!3'c3#9#7!3,`A#6#5#31$op;R+G$e1;R+P$IHe1;R>$e2;R+P$IHe2;R?vd&b;R!2'`U^6#8+0-0RN$b;R+0%~RC!3+^;0-0RN$~R+00#22D-QRN$x;R!1+Q+20E2$x;R+2-QRN$x;R!1+Q+20F2$y;R+2!2,R+2!3'_R#:#2#1111#12H$H;RJ&b;RA+0&E1;RKL!3-0RN$b;R+0%E1;RM%IHe1;RO%H;RP!3+^;0-QRN$x;R!1+Q+20Q2$x;R+2^811#22$E1;RV$IHe1;RX$H;RY!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20Q2$x;R+2-QRN$x;R!1+Q+20#22$y;R+2^7111Z[\$E1;R^0$IHe1;R^1$H;R;!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20#12$x;R+2^811<N^2#1#7#3%~R!3+^;+0!2'c2#8^6,I!3+^;0!3'c3#9#7!3,`1#6#5#31$op;R+G$e1;R+P$IHe1;R>$e2;R+P$IHe2;R?vd&b;R!2'`U^9#8+0-0RN$b;R+0%~RC!3+^;0-0RN$~R+00#22D-QRN$x;R!1+Q+20E2$x;R+2-QRN$x;R!1+Q+20F2$y;R+2!2,R+2!3'`C#:#2#1111#12H$H;RJ&b;RA+0&E1;RKL!3-0RN$b;R+0%E1;RM%IHe1;RO%H;RP!3+^;0-QRN$x;R!1+Q+20Q2$x;R+2^;11#22$E1;RV$IHe1;RX$H;RY!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20Q2$x;R+2-QRN$x;R!1+Q+20#22$y;R+2^:111Z[\$E1;R^0$IHe1;R^1$H;R;!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20#12$x;R+2^;11<N^2#1#7#3%~R!3+^;+0!2'c2#8^9,I!3+^;0!3'c3#9#7!3,`D#6#5#31$sx;R+0$lo;R+1$n;R+1$e;R+P$IHe;R?vd&b;R!2'`U^<#8+0-0RN$b;R+0%~R!3+^;+0-0RN$~R+0+0#12,HB,I!3+^;0-0RN$~R+00#22D-QRN$x;R!1+Q+20!3'c3#;#9#52$x;R+2^=11#12$H;R5&H0;R!6'_2+0,H$e0;R+06,`G,I#1+_7G$H;R!3+^;+0I,I!6'^?01$o;R0!3+^;0-QRN$x;R!1+Q+20#12$x;R+2^=11<!3'c3#:#8#4!1#3#1%~R!3+^;+0!2'c2#8^<,I!3+^;0!3'c3#9#7!4,c5#6#5#4#31$sx;R+0$k;R+1$i;R+2$n;R+1vd&b;R!2'`U^>#7+0-0RN$b;R+0%~R:!3+^;0-0RN$~R+00#22^?11#12$H;R5&H0;R7+_7!2'a;!3+^;0^?1#1=%~R!3+^;+0!2'c2#7^>,I!3+^;0!3'c3#8#6!4,c7#5#4#3#21#2").
Qed.
Lemma conc_try_eq : forall kn e cands, conc_try kn e cands = conc_try_ref kn e cands.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SW0!1+A+P!1+Q+2!1'c:#4!2'c2#4#6!2+_S+2+2!2'aQ#7#4!2'^@!2'^B#1#2'c<!1'_Q#2!3'c3#77#9!2'^A#2#3!2'^B#2#3!1,6|10;!2'^Q#3!2'4:;-0RN$~R+0+092,H-0RN$~R+0+0!4'c=#8#:#1#22!4'c=#8#:#1<,I!1,6,^Y!1'D!2'^Q:>!5'c>#8#:#1#3?!2,R+2#1!3'c9#7#6#3!3'c9#;#:#7!3'c9#:#9#6!3'c9#8#7#4!2'c2#5#7!3'c9#<#;#8-QRN$x;R!1+Q41!2'aQ#8#52$p;R4-_SRN$p;R!2+_S+2+21#11$lo;R+2$hi;R+2-0RN$~R+0162-QRN$x;R!1+Q+21!3'c3#87#:2$v;R+2-0RN$~R+01-0RN$~R+0+092,H-0RN$~R+0+0!4'c=#9#;#1#22!4'c=#9#;#1<,I2-0RN$~R+01!5'c>#9#;#1#3?2AGGCCE!3'c9#?#>#;!3'c9#>#=#:-QRN$x;R!1+Q41!2'aQ#;#82$p;R4-_SRN$p;R!2+_S+2+21#11$lo;R+2$hi;R+2-0RN$~R+0162-QRN$x;R!1+Q+21!3'c3#;7#=2$v;R+2-0RN$~R+01-0RN$~R+0+092,H-0RN$~R+0+0!4'c=#<#>#1#22!4'c=#<#>#1<,I2-0RN$~R+01!5'c>#<#>#1#3?2AIIJJC!2'c2#6#8!2'aQ#:#7!3'c9#=#<#9-QRN$x;R!1+Q41M2$p;R4-_SRN$p;R!2+_S+2+21#11$lo;R+2$hi;R+2-0RN$~R+0162-QRN$x;R!1+Q+21!3'c3#:7#<2$v;R+2-0RN$~R+01-0RN$~R+0+092,H-0RN$~R+0+0!4'c=#;#=#1#22!4'c=#;#=#1<,I2-0RN$~R+01!5'c>#;#=#1#3?2AJJNND!3'c9#@#?#<!3'c9#A#@#=!3'c9#B#A#>!2'^B#3#4!3'c9#C#B#?!2,^:1R!3,`K+P#3#2$kn;R!1+A+a6$e;R+P$cands;R0!5'a:+P$cands;R0!3+^;1!3'c8#4#3#1!3'c9#4#3#1!2,^:1!3'c9#3#2!1,W+P$s;R+P$rest;R0$IH;R!3+^;1!3'c8#5#4#1!3'c9#5#4#1vd!6'^?1!3'c9#6#5#2$o;R1!3+^;1-0RN$~R+0122#1-0RN$~R+01!1'c;32#1-QRN$x;R!1+Q4152$p;R4-_SRN$p;R!2+_S+2+21#11$lo;R+2$hi;R+2-0RN$~R+0162-QRN$x;R!1+Q+2182$v;R+2-0RN$~R+01=2-0RN$~R+01@2A#5#5#4#4#1-0RN$~R+0122B-QRN$x;R!1+Q4152$p;R4-_SRN$p;R!2+_S+2+21#11$lo;R+2$hi;R+2-0RN$~R+0162-QRN$x;R!1+Q+2182$v;R+2-0RN$~R+01=2-0RN$~R+01@2ACCDDB&b;R!1'c:#3+0-0RN$b;R+0!3+^;1-0RN$~R+01#12E-0RN$~R+01!1'c;F2EH-0RN$~R+01#12EH#12!2,^:1B&b;R3+0&Hd;R!2,^:+0#1!3+^;+0F#1!1-0RN$b;R+0%Hd;R!3+^;+0!2'c2#7#9#1!3+^;1-0RN$~R+01!1'c;#22CKK#22$Hd;R!3+^;+0L,Hvd!2,^:1O!3+^;1-0RN$~R+01!1'c;,H2DOO$Hd;R!3+^;+0L,Ivd&o;RM!1+Q4-QRN$o;R!1+Q4!3+^;1G-QRN$x;R!1+Q41#12$p;R4-_SRN$p;R!2+_S+2+21#11$lo;R+2$hi;R+2-0RN$~R+0162-QRN$x;R!1+Q+21!3'c3#<7#>2$v;R+2-0RN$~R+01-0RN$~R+0+092,H-0RN$~R+0+0!4'c=#=#?#1#22!4'c=#=#?#1<,I2-0RN$~R+01!5'c>#=#?#1#3?2APPIIG#12$p;R4!1$p;R4-_SRN$p;R!2+_S+2+2!3+^;1J-_SRN$p;R!2+_S+2+21#11$lo;R+2$hi;R+2-0RN$~R+0162-QRN$x;R!1+Q+21!3'c3#=7#?2$v;R+2-0RN$~R+01-0RN$~R+0+092,H-0RN$~R+0+0!4'c=#>#@#1#22!4'c=#>#@#1<,I2-0RN$~R+01!5'c>#>#@#1#3?2AQQPP#11$z;R+2$z;R+2!2$lo;R+2$hi;R+2!6'^?1!1,S+2$o;R1!3+^;1R-0RN$~R+01!2'^@:'c<2-QRN$x;R!1+Q+21#12$v;R+2-0RN$~R+01-0RN$~R+0+0!2'^A#3#42,H-0RN$~R+0+0!4'c=#@#B#1#32!4'c=#@#B#1!2'^Q#4!2'4S;,I2-0RN$~R+01!5'c>#@#B#1#4!1'D!2'^QS>2ATTRR&b;R6+0-0RN$b;R+0!3+^;1T-0RN$~R+01#12TT#12UU!3'c3#>7#@!4'c?#>#@7#8#2#1#1!2,^:1C!3+^;1-0RN$~R+01!1'c;,I2DOO#1!3'c8#6#5#2#1!3+^;1!3'c8#6#5V!3'c9#6#5V#1").
Qed.

Definition concretize (kn : list kentry) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$kn;R!1+A+a6$e;R+P-0RN$~R+0!1+Q+2!1'c:#12!1'c@#1!3'c8#2#1!1'cA!1'cB#1").

(* [comment removed for export] *)
Definition foldK (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match erange kn e with
         | Some (lo, hi) => if Z.eqb lo hi then ELit lo
                            else match concretize kn e with Some v => ELit v | None => e end
         | None => match concretize kn e with Some v => ELit v | None => e end   (* [comment removed for export] *)
         end
  end.

Definition lit_branch (c : branch_cond) (x y : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S10!1,;|600;$c;R+cC$x;R+2$y;R+2!3'cD#3!2'>0#2!2'>0#1").

(* [comment removed for export] *)
Definition cond_on_eq (c : branch_cond) : bool :=
  match c with
  | BC_EQ => true | BC_NE => false | BC_LT => false | BC_GE => true
  | BC_LTU => false | BC_GEU => true
  end.

(* [comment removed for export] *)
Definition itv_ltu (al ah bl bh : Z) : option bool :=
  if Z.ltb ah bl then Some true else if Z.leb bh al then Some false else None.

(* [comment removed for export] *)
Definition itv_lts (al ah bl bh : Z) : option bool :=
  let h := (2 ^ 63)%Z in
  if ((Z.ltb ah h && Z.ltb bh h) || (Z.leb h al && Z.leb h bl))%bool then itv_ltu al ah bl bh
  else if (Z.leb h al && Z.ltb bh h)%bool then Some true
  else if (Z.ltb ah h && Z.leb h bl)%bool then Some false
  else None.

Definition range_branch (c : branch_cond) (al ah bl bh : Z) : option bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S80!1+Q+0!2'cE!2'^A#3#2!2'^A#1#4!2,R+0,I!2'_C!2'_C!2'`0#4#3!2'`0#2#1!2'`0#4#2!2,R+0,H!1,S+0!4'cF#4#3#2#1!4'cH#4#3#2#1$c;R+cC$al;R+2$ah;R+2$bl;R+2$bh;R+2-cCRN$c;R+cC0#56-0RN$~R+00122-0RN$~R+003245-0RN$~R+00124-0RN$~R+0032256!4'cG+0+0'c;67!4'cG+0+0'c;7").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition diff_branch (c : branch_cond) (a b : expr) : option bool :=
  match c with
  | BC_EQ | BC_NE =>
      match is_lit (mkAlu ALU_SUB a b) with
      | Some z => let e := Z.eqb (z mod two64) 0 in Some (match c with BC_EQ => e | _ => negb e end)
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition lin_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let ltu := if lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] then Some true
             else if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then Some false else None in
  match c with
  | BC_LTU => ltu
  | BC_GEU => option_map negb ltu
  | BC_LT | BC_GE =>
      match erange kn a, erange kn b with
      | Some (_, ah), Some (_, bh) =>
          if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
          then match c with BC_LT => ltu | _ => option_map negb ltu end
          else None
      | _, _ => None
      end
  | BC_EQ | BC_NE =>
      (* [comment removed for export] *)
      if (lin_ge0 kn [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0 kn [(a, (-1)%Z)] [(b, 0%Z)])%bool
      then Some (match c with BC_EQ => false | _ => true end)
      else
      (* [comment removed for export] *)
      if (if lin_ge0 kn [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 kn [(b, 0%Z)] [(a, 0%Z)] else false)
      then Some (match c with BC_EQ => true | _ => false end)
      else None
  end.

Definition decide_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match erange kn a, erange kn b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branch kn c a b      (* [comment removed for export] *)
             end
           end
  end.


(* [comment removed for export] *)
Definition mkSlt (kn : list kentry) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
  match a, b with
  | ELit _, ELit _ => mkAlu op a b
  | _, _ => match decide_branch kn c a b with
            | Some true => ELit 1
            | Some false => ELit 0
            | None => mkAlu op a b
            end
  end.

Definition mkAluK0 (kn : list kentry) (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_SLTU => mkSlt kn BC_LTU ALU_SLTU a b
  | ALU_SLT => mkSlt kn BC_LT ALU_SLT a b
  | ALU_AND => match a, b with
               | ELit _, ELit _ => mkAnd kn a b
               | ELit _, _ => mkAndK kn b a      (* [comment removed for export] *)
               | _, _ => mkAndK kn a b
               end
  | ALU_OR => if expr_eqb a b then a else mkOr kn a b
  | ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
               | None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
                                else mkAlu op a b
               | _, _ => mkAlu op a b
               end
  | ALU_SRL => match is_lit a, shamt_of b 6 with
               | None, Some s => mkSrl kn a s
               | _, _ => mkAlu op a b
               end
  | _ => mkAlu op a b
  end.

(* [comment removed for export] *)
Definition zsx32 (v : Z) : Z := ((bv_swrap 32 v) mod two64)%Z.

Definition mkAluK (kn : list kentry) (op : aluop) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$kn;R!1+A+a6$op;R+J$a;R+P$b;R+P!2'cI#4!4'cJ#4#3#2#1").

(* [comment removed for export] *)
Definition pow2_log (m : Z) : option Z :=
  let m' := (m mod two64)%Z in
  let k := Z.log2 m' in
  if (Z.ltb 0 m' && Z.eqb m' (2 ^ k) && Z.ltb k 64)%bool then Some k else None.

Definition mkMdK (kn : list kentry) (op : mulop) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S50!3'cK#4#3#2!3'cK#3#2#1!1'cL#1!3'cK#6#5#4!3'cK#7#6#5$kn;R!1+A+a6$op;R+G$a;R+P$b;R+P-QRN$x;R!1+Q+2+P!1'`9#22$z;R+20-GRN$op;R+G+P#3811111-PRN$b;R+P+P#18$m;R+2-QRN$x;R!1+Q+2+P22$k;R+2!4'cM#6,cN#4!1,`3#10$n;R+10$op0;R+J$a0;R+P$b0;R+P3$op0;R+J$a0;R+P$b0;R+P3$op0;R+G$a0;R+P$b0;R+P3$op0;R+G$a0;R+P$b0;R+P3$sx;R+0$lo;R+1$n;R+1$e;R+P4$sx;R+0$k;R+1$i;R+2$n;R+141-PRN$b;R+P+P#18$m;R+2-QRN$x;R!1+Q+2+P22$k;R+2!4'cM#6,aH#4!1,`3!2'^B!2'5!1,6|10;#1!1,6,^Y0$n;R+10$op0;R+J$a0;R+P$b0;R+P3$op0;R+J$a0;R+P$b0;R+P3$op0;R+G$a0;R+P$b0;R+P3$op0;R+G$a0;R+P$b0;R+P3$sx;R+0$lo;R+1$n;R+1$e;R+P4$sx;R+0$k;R+1$i;R+2$n;R+14").

(* [comment removed for export] *)
Definition sx32_stable (lo hi : Z) : bool :=
  (Z.ltb hi (2 ^ 31) || Z.leb (two64 - 2 ^ 31) lo)%bool.

(* [comment removed for export] *)
Definition zband32 (kn : list kentry) (d : expr) : bool :=
  let l := lin_of d in
  match lin_range (erange kn) (fst l) (snd l) with
  | Some (lo, hi) => (Z.ltb (- 2 ^ 31) lo && Z.ltb hi (2 ^ 31))%bool
  | None => false
  end.

Definition mkAluwK0 (kn : list kentry) (op : aluop) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S30!2+_S+2+2&d;R!3'bZ#3#2#1+P-QRN$x;R!1+Q+2+P!1'`9#12$v;R+2!1,`3!1'cO#1-QRN$x;R!1+Q0+P!2'aQ#5#12$p;R0-_SRN$p;R!2+_S+2+2+P#11$lo;R+2$hi;R+2-0RN$~R+0+P!2'cP#2#12#4-0RN$~R+0+P!2'cQ#8#42#4!3'cR#7#6#5-0RN$~R+0+P!2'cQ#5#12#1!3'cR#4#3#2!3'cR#3#2#1$kn;R!1+A+a6$op;R+J$a;R+P$b;R+P-JRN$op;R+J+P#3:1122222222").

Definition mkAluwK (kn : list kentry) (op : aluop) (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$kn;R!1+A+a6$op;R+J$a;R+P$b;R+P!2'cI#4!4'cS#4#3#2#1").

(* [comment removed for export] *)
Definition extK0 (kn : list kentry) (v : expr) : expr :=
  match v with
  | EExt sx O n e =>
      if Nat.leb n 7 then
        match erange kn e with
        | Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
        | None => v
        end
      else v
  | _ => v
  end.

Definition extK (kn : list kentry) (v : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$kn;R!1+A+a6$v;R+P!2'cI#2!2'cT#2#1").

Definition msize_bytes (sz : msize) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S30}1}2}4$sz;R+cU-cURN$sz;R+cU+1#14012}8").

(* [comment removed for export] *)
Definition flat_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond :=
  match base_range kn (a_base a) with
  | Some (lo, hi) =>
      if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool
      then [] else [SCFlat a (elen n)]
  | None => [SCFlat a (elen n)]
  end.

(* [comment removed for export] *)
Fixpoint wr_covered (allkn kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xlo allkn len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinside allkn (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_covered allkn rest a n
  | _ :: rest => wr_covered allkn rest a n
  end.

(* [comment removed for export] *)
Fixpoint wr_covered_br (allkn : list kentry) (br : option (Z * Z)) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xlo allkn len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinside_br allkn br (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_covered_br allkn br rest a n
  | _ :: rest => wr_covered_br allkn br rest a n
  end.
Lemma wr_covered_br_eq : forall allkn kn a n, wr_covered_br allkn (base_range allkn (a_base a)) kn a n = wr_covered allkn kn a n.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SN0!1+A+a6!3,`K+a6#1#3!4'cW#=#8#;#:!2'b4#=!1'`S#;!6'^?+02$b;R+0!3+^;+0#1!4'cW#>#9#<#;!2,^:+02!5'cV#=3#8#;#:#7!3,`K+a6!3,b6#3#2#1#8!4'cW#;#6#9#8!2'b4#;!1'`S#9!6'^?+06$b;R+0!3+^;+0#1!4'cW#<#7#:#9!2,^:+06!5'cV#;7#6#9#8#5!3,`K+a6!2,b7#2#1#6!3,`K+a6!3,b8#3#2#1#8!3,`K+a6!2,b9#2#1#6!3,`K+a6!2,b:#2#1#6!3,`K+a6!3,b;#3#2#1#8!3,`K+a6!2,b<#2#1#7!4'cW#?#:#=#<!1'`S#>!1'`T#>-0RN$~R+0+0!2'_C!2'`U@#4!2'^@#3A2-QRN$x;R!1+Q+2+0!2'a[#@#22$l;R+2!2'^@!2'^Q!1'`T#?!1'8#>!2'^Q#4#1,I,I!1'8#=!1,`3C!4'cW#@#;#>#=!1'`S#=!1'`T#=!2'b4#?F!5'cV#?H#:#=#<!3,`K+a6!2,b<!2,`O#3#2#1#:!3,`K+a6!4,b>#4#3#2#1#:!3,`K+a6!3,b?#3#2#1#8!3,`K+a6!2,b@#2#1#6$allkn;R0$kn;R0$a;R+`M$n;R+1!5'a:+a6$kn;R0!3+^;+0!5'cV#5!2'b4#5!1'`S#3#1#3#2!4'cW#5#1#3#2!2,^:+0!4'cW#4!1,W+a6#2#1$K;R+a6$rest;R0$IH;R!3+^;+0!5'cV#6!2'b4#6!1'`S#4#1#4#3!4'cW#6#1#4#3-a6RN$k;R+a6!3+^;+0!5'cV#8!2'b4#8!1'`S#61#6#5!4'cW#81#6#5#3:$a;R+`M$w;R+1$v;R+P!3$a0;R+`M$w;R+1$v;R+Pvd4!3+^;+0!5'cV#=35#;#:!4'cW#=5#;#:#3#2#1$a;R+`M$n;R+P!2$a0;R+`M$n0;R+Pvd8!3+^;+0!5'cV#;79#9#8!4'cW#;9#9#8#2#1$a;R+`M$n;R+P$k;R+1!3$a0;R+`M$n0;R+P$k;R+1vd4!3+^;+0!5'cV#=3:#;#:!4'cW#=:#;#:#3#2#1$lo;R+2$hi;R+2!2$lo;R+2$hi;R+2vd8!3+^;+0!5'cV#;7;#9#8!4'cW#;;#9#8#2#1$e;R+P$m;R+2!2$e;R+P$m;R+2vd8!3+^;+0!5'cV#;7<#9#8!4'cW#;<#9#8#2#1$e;R+P$lo;R+2$hi;R+2!3$e;R+P$lo;R+2$hi;R+2vd4!3+^;+0!5'cV#=3=#;#:!4'cW#==#;#:#3#2#1$a;R+`M$n;R+P!2$a0;R+`M-`MRN$s;R+`M%n;R+P!3+^;+0!5'cV#<!2'b4#<!1'`S#:>#:#9!4'cW#<>#:#9#11$a_base;R+P$a_off;R+2!2$kb;R+P$kk;R+2$len;R+Pvd!6'^?+0?$b;R+0!3+^;+0-0RN$~R+0+0B2,H-0RN$~R+0+0!8'a\#@!2'b4#@@@AD#4#3#22,H#1-0RN$~R+0+0B2,H-0RN$~R+0+0!7'aW#@@AD#4#3#22,HE!2,^:+0-0RN$~R+0+0-0RN$~R+0+0!2'_C!2'`UF#3!2'^@#2G2-QRN$x;R!1+Q+2+0!2'a[#?#12$l;R+2!2'^@!2'^QAC!2'^Q#3#1,I,I2,H-0RN$~R+0+0!7'aW#?FG!1,`3!1'8#<#3#2#12,H?I#9!3+^;+0!5'cV#?HJ#=#<!4'cW#?J#=#<#2#1#2#1$a1;R+`M$n1;R+P$a2;R+`M$n2;R+P!4$a1;R+`M$n1;R+P$a2;R+`M$n2;R+Pvd!6'^?+0?$b;R+0!3+^;+0#1E!2,^:+0?I#9!3+^;+0!5'cV#?HK#=#<!4'cW#?K#=#<#4#3#2#1$a;R+`M$n;R+P$c;R+2!3$a0;R+`M$n0;R+P$c;R+2vd4!3+^;+0!5'cV#=3L#;#:!4'cW#=L#;#:#3#2#1$a;R+`M$n;R+P!2$a0;R+`M$n0;R+Pvd8!3+^;+0!5'cV#;7M#9#8!4'cW#;M#9#8#2#1#3").
Qed.

Definition storeok_sc (kn : list kentry) (a : saddr) (n : nat) : list sidecond := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S10!1,W+bW$kn;R!1+A+a6$a;R+`M$n;R+1-0RN$~R+0!1+A+bW!5'cV#3!2'b4#3!1'`S#2#3#2#120!3,`K+bW!2,cX#2#10").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record scripts : Type := SCR {
  sc_dirs  : list bool;     (* [comment removed for export] *)
  sc_reads : list expr;     (* [comment removed for export] *)
  sc_hints : list bool      (* [comment removed for export] *)
}.

Inductive stepres :=
| SOk (ss : sym_state) (scs : list sidecond) (scr : scripts)
| SStop.

(* [comment removed for export] *)
Definition conc_expr (kn : list kentry) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | _ => match concretize kn e with Some v => ELit v | None => e end
  end.

(* [comment removed for export] *)
Definition cond_probe (c : branch_cond) (a b : expr) : expr * bool :=
  match c with
  | BC_EQ => (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z), true)    (* [comment removed for export] *)
  | BC_NE => (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1%Z), false)
  | BC_LT => (EAlu ALU_SLT a b, true)
  | BC_GE => (EAlu ALU_SLT a b, false)
  | BC_LTU => (EAlu ALU_SLTU a b, true)
  | BC_GEU => (EAlu ALU_SLTU a b, false)
  end.

Definition enum_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!1+Q+0$kn;R!1+A+a6$c;R+cC$a;R+P$b;R+P-_SRN$x;R!2+_S+P+00!3'cY#3#2#11$e;R+P$pos;R+0-QRN$x;R!1+Q+20!2'cZ#6#22$v;R+2&z;R!2'`0!2'3#1'_D,^5+0!2,R+0-0RN$pos;R+0+0#32!1'c;#1#1!1,S+0").

(* [comment removed for export] *)
Definition to_saddrK (kn : list kentry) (e : expr) (imm : Z) : saddr :=
  match split_lit e with
  | (ELit _, _) => to_saddr e imm
  | _ => match concretize kn (mkAlu ALU_ADD e (ELit imm)) with
         | Some v => SA (ELit 0) v
         | None => to_saddr e imm
         end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition amo_sz (wd : awidth) : msize := match wd with AW => SZ4 | AD => SZ8 end.
(* [comment removed for export] *)
Definition amo_sx (wd : awidth) : bool := match wd with AW => true | AD => false end.

(* [comment removed for export] *)
Definition amo_alignedb (kn : list kentry) (e : expr) (wd : awidth) : bool :=
  match lin_lowbits_kn kn e (match wd with AW => 2 | AD => 3 end) with
  | Some r => Z.eqb r 0
  | None => false
  end.

(* [comment removed for export] *)
Definition resv_inval (r : option saddr) (a : saddr) : option (option saddr) :=
  match r with
  | None => Some None
  | Some ra =>
      if saddr_eqb ra a then Some None
      else if (expr_eqb (a_base ra) (a_base a) && negb (Z.eqb ((a_off ra - a_off a) mod two64) 0))%bool
           then Some r
           else None
  end.

(* [comment removed for export] *)
Definition amo_aluop (op : amoop) : option (option aluop) :=
  match op with
  | AMO_SWAP => Some None
  | AMO_ADD => Some (Some ALU_ADD)
  | AMO_XOR => Some (Some ALU_XOR)
  | AMO_AND => Some (Some ALU_AND)
  | AMO_OR => Some (Some ALU_OR)
  | _ => None
  end.

(* [comment removed for export] *)
Definition amo_newval (kn : list kentry) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
  match aop with
  | None => src
  | Some o => match wd with AW => mkAluwK kn o old src | AD => mkAluK kn o old src end
  end.

(* [comment removed for export] *)
Definition sym_read (segs : list Segment) (ss : sym_state) (fk : list kentry) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookup fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extK fk v, flat_sc fk a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupA fk segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extK fk v, flat_sc fk a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_sc fk a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.

Definition sym_step (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  let fk := facts_of (s_know ss) in   (* [comment removed for export] *)
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwK fk ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_expr fk (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branch fk c a b with
            | Some t => Some t
            | None => match decide_branch fk c (conc_expr fk a) (conc_expr fk b) with
                      | Some t => Some t
                      | None => enum_branch fk c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrK fk (g rs) (bv_signed imm) in
      match sym_read segs ss fk scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK fk (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_sc fk a n ++ storeok_sc fk a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0 in
        match sym_read segs ss fk scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_sc fk a n ++ storeok_sc fk a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedb fk e wd then
            let a := to_saddrK fk e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_read segs ss fk scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newval fk wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_sc fk a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.



(* [comment removed for export] *)
Definition sidecond_eqb (x y : sidecond) : bool :=
  match x, y with
  | SCFlat a n, SCFlat a' n' => saddr_eqb a a' && expr_eqb n n'
  | SCStoreOk a n, SCStoreOk a' n' => saddr_eqb a a' && Nat.eqb n n'
  | SCDisj a n b m, SCDisj a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | SCInside a n b m, SCInside a' n' b' m' =>
      saddr_eqb a a' && expr_eqb n n' && saddr_eqb b b' && expr_eqb m m'
  | _, _ => false
  end.

Fixpoint sc_mem (x : sidecond) (l : list sidecond) : bool :=
  match l with [] => false | y :: t => sidecond_eqb x y || sc_mem x t end.

Fixpoint sc_add (news acc : list sidecond) : list sidecond :=
  match news with
  | [] => acc
  | x :: t => sc_add t (if sc_mem x acc then acc else x :: acc)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition itab : Type := ptree instr.
Definition itab_lookup (t : itab) (pc : Z) : option instr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1,S+c\$t;R'c[$pc;R+2-2RN$pc;R+2!1+Q+c\#130$p;R+aA!3'bL+c\#3#1$p;R+aA0").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition itab_entry (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | None => None
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (i, sz) => if Z.eqb sz 4 then Some i else None
              | None => None
              end
  end.
Fixpoint mk_itab_fuel (n : nat) (pc : Z) (t : itab) : itab :=
  match n with
  | O => t
  | S n' => mk_itab_fuel n' (pc + 4)%Z
            (match pc, itab_entry pc with
             | Zpos p, Some i => pt_set p i t
             | _, _ => t
             end)
  end.
(* [comment removed for export] *)
Definition mk_itab (lo : Z) (n : nat) : itab := mk_itab_fuel n lo PTLeaf.
Definition itab_sound (t : itab) : Prop := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!1+Q+c\$t;R'c[%pc;R+2%i;R+c\%~R!3+^;0!2'd0#3#2!2,R+c\#1!3+^;0!1'd1#3!2,R+c\#2").
Lemma mk_itab_fuel_sound : forall n pc t, itab_sound t -> itab_sound (mk_itab_fuel n pc t).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SG1lgd2d;g^?d;!1'd4#1%pc;R+2%t;R'c[%~R0!1'd4!3'd5#4#3#2!1'd1!1,6#1!1+Q+c\!1'd1!1,6#2!1,6#4!1'd15!2,R+c\#1!1,S+c\!2,R+c\#2!2,R+c\#3$e;R3-QRN$o;R!1+Q+c\w#12$~R+c\+_7+^F!3+^;+aA#1#:!3+^;+aA#2#;!1'^P=!2,R+c\#5!2,R+c\#6!3+^;+aA#3#<!2,R+c\#7!2,R+c\#8!2,R+c\#9!3+^;3#1B!4'bK+c\#=#9#@$n;R+1!4'd3$n;R+11$pc;R+2$t;R'c[$Ht;R0vd#1!1'd4!3'd5,_T#3#2$n;R+1$IH;R1$pc;R+2$t;R'c[$Ht;R0vd!3#4!2'^Q#3!1,6|20;-2RN$pc;R+2'c[#33#2$p;R+aA-QRN$x;R!1+Q+c\'c[22$i;R+c\!4'bK+c\#2#1#4#3$p;R+aA#3-2RN$z;R+2!1'd4-2RN$pc;R+2'c[#13#3$p;R+aA-QRN$x;R!1+Q+c\'c[22$i;R+c\!4'bK+c\#2#1#5#4$p;R+aA#4#33#1$p;R+aA!1$p;R+aA&o;R23&E;R!2,^:3#1!3+^;34#1!1-QRN$o;R!1+Q+c\%E;R!3+^;36#1!1'd4-QRN$x;R!1+Q+c\'c[#22$i;R+c\!4'bK+c\#6#1#9#8#22$i;R+c\!1$i;R+c\$E;R!3+^;3!1'd1!1,6#57vd$pc';R+2$i';R+c\vd-2RN$z;R+2%~R!3+^;3-2RN$pc;R+23#138$p;R+aA!3'bL+c\!4'bK+c\#:#6#=#1$p;R+aA89!3+^;3!1'd1#2:#23$H;R!3+^;387&H0;R!6'_238;,`G9#1+_7!2'a;!3+^;3!1'd1,^5:#1$p;R+aA!1$p';R+aA&s;R!2'd6#1#:!2+d7<!1'^P<-d7RN$s;R!2+d7=>%~R!3+^;3!3'bL+c\!4'bK+c\#<#8#?#3?!3+^;36@#12$e;R=!1$e;RA!6'^?+aA#=$p';R+aA%~R!3+^;3!3'bL+c\!4'bK+c\#>#:#A#1B!3+^;34C!6'^?3D$o;R3%~RE!3+^;3!1'd1!1,6#?C$H;R!3+^;3D@&H0;R!6'bT3+c\$e;R3-QRN$o;R!1+Q+c\+c\#12$i;R+c\#1#;!2,R+c\#:B#1!3+^;+c\#:#7!1$H;R!3+^;+c\#;#8!6'_2+c\#<$i';R+c\!3+^;3!1'd1!1,6#A7#;#9#1#1!3'bL+c\F#=!4'd2+c\#=#9#@#4#1#1$n;R>!1$Hne;R!1'^PA!6'^?3!3'bL+c\#@#4$o;R3%~RE!3+^;3!1'd1!1,6#6C!2#?5#6!3'bL+c\F#4!6'd8+c\#4#=#9#@#1#1#1$p;R+aA!1$p';R+aA$H;R!3+^;38:&H0;R!6'_238;,`G!2,R+c\#4#1+_7!2'a;!3+^;3!1'd1!1,`>#3?#1#1%~R!3+^;3!2'd0!4'bK+c\#8#4#;#27!3+^;3!1'd1#39!1'd4!4'bK+c\#6#2#9#1$E;R!3+^;3!1'd1!1,6#38#6#1#1$p;R+aA!1$p;R+aA#3#1!1'd4!3'd5!1,d9#5#3#2#1").
Qed.
Lemma mk_itab_sound : forall lo n, itab_sound (mk_itab lo n).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S=1lgd:d;g^?d;!1,bP+c\!1+Q+c\!1,S+c\!3'bL+c\0#1!2,R+c\#2!2,R+c\#3!2,R+c\#1$e;R1-QRN$o;R!1+Q+c\w#12$~R+c\+_7+^F!2,R+c\#4!2,R+c\#5!3+^;1!1'd1!1,6#39!3+^;125!6'_2127,`G8#1$lo;R+2$n;R+1!4'd;#1#20vd$pc;R+2$i;R+c\vd-2RN$z;R+2%~R!3+^;1-2RN$pc;R+21#132$p;R+aA3$p;R+aA24!3+^;1!1'd1#25#23$H;R!3+^;126&H0;R!6'_2127,`G4#1+_7!2'a;!3+^;1!1'd1,^55#1$p;R+aA!1$p;R+aA!6'^?12$o;R1%~R!3+^;1#18:$H;R;&H0;R<+_7!2'a;:#13!2'd:+c\#1#1$p;R+aA!1$p;R+aA$H;R;&H0;R<+_7!2'a;!3+^;1!1'd1!1,`>#39#1#1%~R!3+^;1!2'd00#26!3+^;1!1'd1#34!1'd40").
Qed.

(* [comment removed for export] *)
Fixpoint sym_exec_go (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_step segs i ss scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  sym_exec_go f false stops scr' ss' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
  end.

Definition sym_exec (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
           (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+A+bW!1'd>#2$fuel;R+1$first;R+0$stops;R!1+A+2$scr;R+d<$ss;R+`V$acc;R0!7'd=#6#5#4#31#1!4,_W!2+_S+`V0+d<!4,_W+`V01#1#3").

(* [comment removed for export] *)
Definition scr_nil : scripts := SCR [] [] [].

Fixpoint sym_execS_go (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then ss else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then ss else ck) else
          match decode_any w with
          | None => if s_clean ss then ss else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then ss else ck) else
              match sym_step segs i ss scr_nil with
              | SOk ss' [] _ => sym_execS_go f false stops ss' (if s_clean ss' then ss' else ck)
              | _ => if s_clean ss then ss else ck
              end
          end
      end
  end.

Definition sym_execS (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!1'd>#1$fuel;R+1$first;R+0$stops;R!1+A+2$ss;R+`V!5'd?#4#3#200").

(* [comment removed for export] *)
Fixpoint sym_execT_go (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_step segs i ss scr_nil with
          | SOk ss' [] _ => sym_execT_go t f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.

Definition sym_execT (t : itab) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S10!1'd>#1$t;R'c[$fuel;R+1$first;R+0$stops;R!1+A+2$ss;R+`V!6'd@#5#4#3#200").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zf_covers (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  (match len with
   | ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)%Z with RInside _ => true | _ => false end
   | _ => false
   end) || xinside allkn rb rk (elen n) kb kk len.

(* [comment removed for export] *)
Definition kentry_overlay (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      zf_covers allkn rb rk n kb kk len
  | _ => false
  end.

(* [comment removed for export] *)
Definition kentry_readable (allkn : list kentry) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
  | _ => kentry_overlay allkn rb rk n K
  end.

(* [comment removed for export] *)
Fixpoint know_byte_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) : bool :=
  match kn with
  | [] => false
  | K :: rest =>
      let lit kb kk (l : Z) := match rel_lit rb rk 1 kb kk l with RInside _ => true | _ => false end in
      (match K with
       | KWord (SA kb kk) w _ => img && lit kb kk (Z.of_nat w)
       | KZero (SA kb kk) (ELit l0) | KFill (SA kb kk) (ELit l0) _ | KBlob (SA kb kk) (ELit l0) _
       | KUnk (SA kb kk) (ELit l0) => lit kb kk (l0 mod 2 ^ 64)%Z
       | KImg lo hi =>
           img && match rb with
                  | ELit 0 => Z.leb lo rk && Z.ltb rk hi &&
                              match seg_rom segs (Z_to_bv 64 rk) with Some _ => true | None => false end
                  | _ => false
                  end
       | _ => false
       end) || know_byte_cov img rest rb rk
  end%bool.

Fixpoint know_bytes_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => know_byte_cov img kn rb rk && know_bytes_cov img kn rb (rk + 1) n'
  end.

Definition kn_readable (allkn kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S10!1+A+a6$allkn;R0$kn;R0$rb;R+P$rk;R+2$n;R+1!2'cE!3'dA+a6!4'dB#5#3#2#1#4!5'dC,H#4#3#2#1").
Definition kn_overlay (allkn kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S10!1+A+a6$allkn;R0$kn;R0$rb;R+P$rk;R+2$n;R+1!2'cE!3'dA+a6!4'dD#5#3#2#1#4!5'dC,I#4#3#2#1").

(* [comment removed for export] *)
Fixpoint evars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ | EBlob _ _ _ _ => true
  | EVar v => Nat.ltb v b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => evars_lt b x && evars_lt b y
  | EExt _ _ _ x => evars_lt b x
  end.

(* [comment removed for export] *)
Fixpoint find_readbase (i : nat) (scs : list sidecond) : option (saddr * nat * bool) :=
  match scs with
  | [] => None
  | SCReadBase a n sx (EVar j) :: rest => if Nat.eqb j i then Some (a, n, sx) else find_readbase i rest
  | _ :: rest => find_readbase i rest
  end.

(* [comment removed for export] *)
Definition x_dischargeable (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  let kn := s_know ss in
  let fk := facts_of kn in
  match sc with
  | SCReadBase a n sx (EVar j) =>
      (match rb with
       | Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
       | None => false
       end)
      && Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
      && Nat.leb 1 n && Nat.leb n 8 && kn_readable fk kn (a_base a) (a_off a) n
  | SCFlat a (ELit z) =>
      Z.leb 1 z && Z.leb z 8 && kn_readable fk kn (a_base a) (a_off a) (Z.to_nat z)
  | SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlay fk kn (a_base a) (a_off a) n
  | _ => false
  end%bool.

Definition x_filter (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
  match scs with
  | [] => []          (* [comment removed for export] *)
  | _ => let rb := find_readbase (s_next ss) scs in
         List.filter (fun sc => negb (x_dischargeable ss ss' rb sc)) scs
  end.

(* [comment removed for export] *)
Fixpoint esize_budget (e : expr) (b : nat) {struct e} : option nat :=
  match b with
  | O => None
  | S b' =>
      match e with
      | ELit _ | EVar _ | EBlob _ _ _ _ => Some b'
      | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y =>
          match esize_budget x b' with Some b'' => esize_budget y b'' | None => None end
      | EExt _ _ _ x => esize_budget x b'
      end
  end.
Definition esize_le (e : expr) (k : nat) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$e;R+P$k;R+1-QRN$x;R!1+Q+1+0!2'dE#2#12$n;R+1,H,I").

(* [comment removed for export] *)
Definition rd_of (i : instr) : option reg :=
  match i with
  | Lui rd _ | Auipc rd _ | Jal rd _ | Jalr rd _ _ | Load _ _ rd _ _
  | OpImm _ rd _ _ | ShiftImm _ rd _ _ | Op _ rd _ _ | OpImm32 rd _ _ | ShiftImm32 _ rd _ _ | Op32 _ rd _ _
  | Mul _ rd _ _ | Mul32 _ rd _ _ | Lr _ _ _ rd _ | Sc _ _ _ rd _ _ | Amo _ _ _ _ rd _ _ => Some rd
  | _ => None
  end.

(* [comment removed for export] *)
Definition cap_rd (K : nat) (i : instr) (ss : sym_state) : sym_state :=
  match K with
  | O => ss
  | _ =>
      match rd_of i with
      | None => ss
      | Some rd =>
          if bv_eqb rd 0 then ss
          else if esize_le (sr_get (s_regs ss) rd) K then ss
          else SSR (s_pc ss) (sr_upd (s_regs ss) (ridx rd) (EVar (s_next ss)))
                   (s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss)
      end
  end.

Definition sym_stepX (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_step segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')            (* [comment removed for export] *)
      then SOk (cap_rd K i ss') (x_filter ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.

(* [comment removed for export] *)
Fixpoint sym_execSX_go (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then ss else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then ss else ck) else
          match decode_any w with
          | None => if s_clean ss then ss else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then ss else ck) else
              match sym_stepX K i ss scr_nil with
              | SOk ss' [] _ => sym_execSX_go K f false stops ss' (if s_clean ss' then ss' else ck)
              | _ => if s_clean ss then ss else ck
              end
          end
      end
  end.

Definition sym_execSX (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S10!1'd>#1$K;R+1$fuel;R+1$first;R+0$stops;R!1+A+2$ss;R+`V!6'dF#5#4#3#200").

Fixpoint sym_execTX_go (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepX K i ss scr_nil with
          | SOk ss' [] _ => sym_execTX_go t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.

Definition sym_execTX (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S10!1'd>#1$t;R'c[$K;R+1$fuel;R+1$first;R+0$stops;R!1+A+2$ss;R+`V!7'dG#6#5#4#3#200").



End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kcut (mk : saddr -> expr -> kentry) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0 kn [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0 kn [(wb, wk)] [(kb, kk)] then lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            (* [comment removed for export] *)
        then if lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    (* [comment removed for export] *)
             then lin_ge0 kn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  (* [comment removed for export] *)
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0 kn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.

Definition kzero_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S00$kn;R!1+A+a6$wb;R+P$wk;R+2$wn;R+P$kb;R+P$kk;R+2$len;R+P!8'dH,b7#7#6#5#4#3#2#1").
Definition kfill_cut (c : Z) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 8 "S00$c;R+2$kn;R!1+A+a6$wb;R+P$wk;R+2$wn;R+P$kb;R+P$kk;R+2$len;R+P!8'dH$a;R+`M$n;R+P!3,b?#2#1#:#7#6#5#4#3#2#1").
Definition kunk_cut (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S00$kn;R!1+A+a6$wb;R+P$wk;R+2$wn;R+P$kb;R+P$kk;R+2$len;R+P!8'dH,b@#7#6#5#4#3#2#1").

(* [comment removed for export] *)
Definition ktrim (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (l0 : Z) (k : Z) (w : nat) : list kentry :=
  let l := (l0 mod 2 ^ 64)%Z in
  let hi1 := Z.min k (kk + l) in
  let r1 := if Z.ltb kk hi1 then [mk (SA kb kk) (ELit (hi1 - kk))] else [] in
  let lo2 := Z.max kk (k + Z.of_nat w) in
  let r2 := if Z.ltb lo2 (kk + l) then [mk (SA kb lo2) (ELit (kk + l - lo2))] else [] in
  r1 ++ r2.

(* [comment removed for export] *)
Definition kword_cut (kb : expr) (kk : Z) (w' : nat) (v : expr) (k : Z) (w : nat) : list kentry :=
  match v with
  | ELit _ =>
      let n1 := (k - kk)%Z in                                (* [comment removed for export] *)
      let r1 := if Z.ltb 0 n1 then [KWord (SA kb kk) (Z.to_nat n1) (mkExt false 0 (Z.to_nat n1) v)] else [] in
      let d := (k + Z.of_nat w - kk)%Z in                    (* [comment removed for export] *)
      let r2 := if Z.ltb d (Z.of_nat w')
                then [KWord (SA kb (kk + d)) (w' - Z.to_nat d) (mkExt false (Z.to_nat d) (w' - Z.to_nat d) v)]
                else [] in
      r1 ++ r2
  | _ => []
  end.

(* [comment removed for export] *)
Definition prune_zf (mk : saddr -> expr -> kentry) (allkn : list kentry) (wb : expr) (k : Z) (w : nat)
           (K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
           (diffbase : unit -> list kentry * list sidecond * list bool)
  : list kentry * list sidecond * list bool :=
  (* [comment removed for export] *)
  if expr_eqb kb wb then
    match len with
    | ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
    | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
           else (kcut mk allkn wb k (elen w) kb kk len, [], hints)
    end
  else if apart tt then ([K], [], hints)
  else match kcut mk allkn wb k (elen w) kb kk len with
       | [] => diffbase tt
       | cut => (cut, [], hints)
       end.

Definition prune1 (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_x allkn (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   (* [comment removed for export] *)
    | false :: hs => ([], [], hs)                          (* [comment removed for export] *)
    | [] => ([], [], [])                                   (* [comment removed for export] *)
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1 ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) (2 ^ 64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zf KZero allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zf (fun a n => KFill a n c) allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zf KUnk allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_x allkn (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
      else if ranges_apart_x allkn (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   (* [comment removed for export] *)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod 2 ^ 64)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Fixpoint prune (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1 allkn wa w wv K hints in
      let '(r, scs2, hs2) := prune allkn wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Definition prune1p (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_p allkn sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)   (* [comment removed for export] *)
    | false :: hs => ([], [], hs)                          (* [comment removed for export] *)
    | [] => ([], [], [])                                   (* [comment removed for export] *)
    end in
  match K with
  | KAlign _ _ => ([K], [], hints)
  | KRange _ _ _ => ([K], [], hints)
  | KWr _ _ => ([K], [], hints)
  | KDisj _ _ _ _ => ([K], [], hints)
  | KImg lo hi =>
      match a_base wa with
      | ELit 0 =>
          let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
          let lo2 := Z.max lo (k + Z.of_nat w) in
          let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
          (r1 ++ r2, [], hints)
      | _ => if Z.ltb (hi - lo) (2 ^ 64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
             else ([], [], hints)
      end
  | KZero (SA kb kk) len =>
      prune_zf KZero allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KFill (SA kb kk) len c =>
      prune_zf (fun a n => KFill a n c) allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KUnk (SA kb kk) len =>
      prune_zf KUnk allkn (a_base wa) k w K kb kk len
               (fun _ => ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then
        (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
         then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))   (* [comment removed for export] *)
      else if ranges_apart_p allkn sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)   (* [comment removed for export] *)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then
        match len with
        | ELit l0 =>
            let l := (l0 mod 2 ^ 64)%Z in
            (if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
             then ([K], [], hints) else ([], [], hints))
        | _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
        end
      else diffbase (SA kb kk) len
  end.

Fixpoint prunep (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1p allkn sp wa w wv K hints in
      let '(r, scs2, hs2) := prunep allkn sp wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Definition ranges_apart_pc (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if expr_eqb b2 b1 then (Z.leb (k1 + m1) k2 || Z.leb (k2 + m2) k1)%bool else   (* [comment removed for export] *)
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides_br kn br2 (sp_D sp) b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x_br kn br2 (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Definition kbase (K : kentry) : option expr :=
  match K with
  | KZero (SA kb _) _ | KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ | KFill (SA kb _) _ _ | KUnk (SA kb _) _ => Some kb
  | _ => None
  end.

(* [comment removed for export] *)
Definition prune1pc (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
  (br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
  let k := a_off wa in
  let diffbase (ka : saddr) (kl : expr) :=
    let apart := ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
    if apart then ([K], [], hints) else
    match hints with
    | true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
    | false :: hs => ([], [], hs)
    | [] => ([], [], [])
    end in
  match K with
  | KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1p allkn sp wa w wv K hints
  | KZero (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kzero_cut allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KFill (SA kb kk) len c =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kfill_cut c allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KUnk (SA kb kk) len =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
      else match kunk_cut allkn (a_base wa) k (elen w) kb kk len with
           | [] => diffbase (SA kb kk) len
           | cut => (cut, [], hints)
           end
  | KWord (SA kb kk) w' v =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else if ranges_apart_pc allkn sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
      then ([K], [], hints)
      else diffbase (SA kb kk) (elen w')
  | KBlob (SA kb kk) len bk =>
      if expr_eqb kb (a_base wa) then prune1p allkn sp wa w wv K hints
      else diffbase (SA kb kk) len
  end.

Fixpoint br_lookup (c : list (expr * option (Z * Z))) (b : expr) : option (option (Z * Z)) :=
  match c with
  | [] => None
  | (b', r) :: rest => if expr_eqb b b' then Some r else br_lookup rest b
  end.

Fixpoint prunepc (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(br2, cache') :=
        match kbase K with
        | Some kb => match br_lookup cache kb with
                     | Some r => (r, cache)
                     | None => let r := base_range allkn kb in (r, (kb, r) :: cache)
                     end
        | None => (None, cache)
        end in
      let '(kept, scs1, hs1) := prune1pc allkn sp wa w wv K hints br2 in
      let '(r, scs2, hs2) := prunepc allkn sp wa w wv rest hs1 cache' in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Fixpoint carry (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry older kn hints in
      let fk := facts_of kn1 in
      let '(kn2, scs2, hs2) := prunepc fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in   (* [comment removed for export] *)
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.




End AX2K.
