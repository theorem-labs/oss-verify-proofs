(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3 AxSymExec3B.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @spiece]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Numbers; @BinNums; @Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @listZ_eqb]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @amap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mkind_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @am_kind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @KHOLE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @is_tok_kind]; [@Stdlib; @Lists; @List; @forallb]; [@Corelib; @Init; @Datatypes; @negb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @is_fog]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @is_hole]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @acs]; [@Corelib; @Lists; @ListDef; @nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @s_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_ss]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ELit]; [@Corelib; @Numbers; @BinNums; @Z0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @s_know]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @s_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @s_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sym_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @ACS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_maps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_totsz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_ylo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_eager]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_ghost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_abytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_brk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_fd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @a_tidset]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @SSR]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sentry]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @saddr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @with_ss]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mk_ss]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sr_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @set_kn]; [@Corelib; @Init; @Datatypes; @app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @Some]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @two64]; [@LinuxProcessSemantics; @Riscv; @Instr; @aluop]; [@LinuxProcessSemantics; @Riscv; @Instr; @mulop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @lit_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @reg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @mkAlu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @mkMd]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@Stdlib; @Lists; @List; @fold_right]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @expr_vars]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @a_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @am_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @am_len]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @fst]; [@Corelib; @Init; @Datatypes; @snd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @afd]; [@Corelib; @Init; @Datatypes; @orb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @ltb]; [@Stdlib; @Lists; @List; @existsb]; [@Corelib; @Init; @Datatypes; @andb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr_eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Init; @Datatypes; @true]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @all_live]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @split_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @live_vars]; [@Stdlib; @Lists; @List; @filter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_gc_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ptree]; [@Corelib; @Init; @Datatypes; @unit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @expr_vars_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @PTLeaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @pt_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @vkey]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @expr_all_live_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @live_vars_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_gc_entry_t]; [@Corelib; @Init; @Logic; @eq]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Init; @Logic; @f_equal]; [@Stdlib; @PArith; @BinPos; @Pos; @to_nat]; [@Stdlib; @PArith; @BinPos; @Pos; @of_succ_nat]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @PArith; @Pnat; @SuccNat2Pos; @id_succ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @live_agree]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Corelib; @Init; @Logic; @not]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @pt_set]; [@Corelib; @Init; @Datatypes; @tt]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @pt_gss]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @in_live_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @pt_gso]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @vkey_inj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @expr_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @live_agree_var]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EVar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EAlu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EAluw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EMd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EMdw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EExt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @EBlob]; [@Corelib; @Init; @Datatypes; @list_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @live_agree_expr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @pt_get_leaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @live_agree_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @SA]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @Lists; @List; @In]; [@Stdlib; @Lists; @List; @existsb_exists]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @False]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Lists; @List; @forallb_forall]; [@Corelib; @Init; @Logic; @True]; [@Corelib; @Init; @Logic; @I]; [@Stdlib; @Bool; @Bool; @andb_true_r]; [@Stdlib; @Bool; @Bool; @andb_assoc]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @forallb_expr_vars]; [@stdpp; @tactics; @f_equal_help]; [@Stdlib; @Lists; @List; @filter_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @live_vars_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWord]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KZero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KImg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @expr_all_live_t_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KAlign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KRange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KWr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KDisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KFill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @KUnk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @cs_gc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @cs_gc_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @expr_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @saddr_vars_lt]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @fresh_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sidecond]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @carryK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @mkbc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @facts_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @s_log]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @sym_execTXBI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @mk_kix]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @carry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sym_execTX]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @bctx]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@Corelib; @Classes; @RelationClasses; @symmetry]; [@Corelib; @Classes; @RelationClasses; @eq_Symmetric]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @sym_execTX_know]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @carryK_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @sym_execTXBI_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @run_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @run_block_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @saddr_eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @ranges_apart_xB]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @Logic; @FunctionalExtensionality; @functional_extensionality]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kentry_apart_bB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kentry_apart_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ranges_apart_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @ranges_apart_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @sprep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @ranges_apart_pB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kentry_apart_bpB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kentry_apart_bp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ranges_apart_p]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @ranges_apart_pB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @mk_sprepB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kimg_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @bc_fk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_unfillB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_unfill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @mk_sprep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @bc_fk_mkbc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @mk_sprepB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kentry_apart_bpB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_unfillM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_unfillB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwr_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kzero_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kfill_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kunk_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kzero_cutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kfill_cutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kunk_cutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @havoc1B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @havoc1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kzero_cutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kfill_cutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kunk_cutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kentry_apart_bB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @havoc1pB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @havoc1p]; [@Stdlib; @Lists; @List; @flat_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_havocB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_havoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @havoc1pB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_havocM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_havocB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kcutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwr_cutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwr_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kcut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kcutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @cutout1B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @cutout1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwr_cutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @cutout1pB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @cutout1p]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_cutoutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_cutout]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @cutout1pB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_cutoutM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_cutoutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kimg_cut1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lres]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @know_lookupB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kreadZB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kreadZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @know_lookup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @know_lookupB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kread8eB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kread8e]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwritableB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwritable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @xloB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @xinsideB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @xlo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @xinside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @xloB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @xinsideB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwritable_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwritable_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @xhiB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @xhi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @xhiB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kzero_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kzero_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kfill_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kfill_x]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @off_image_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @off_image_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @base_rangeB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @flat_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @flat_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @base_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @base_rangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @lin_ge0B]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @len_eqbB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @len_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @xterms]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin_ge0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @lin_ge0B_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @ealignB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @page_alignedB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @page_aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @ealign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @ealignB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @pc]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xlo1B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xlo1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin_brange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @zlit64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @erangeB]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @lin_srangeB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @erange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @lin_srange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @erangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @lin_srangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @lin_brangeB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @lin_brangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xhi1B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xhi1]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @deand]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xb2B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xb2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xlo1B_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xhi1B_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xlo2B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xlo2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xb2B_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xhi2B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @xhi2]; [@Corelib; @Init; @Datatypes; @nat_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kread_bytesB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kread_bytes]; [@Corelib; @Init; @Datatypes; @O]; [@Corelib; @Numbers; @BinNums; @xH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kreadZB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kread_bytesB_eqf']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @add_kn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @zbytes_le_to_Z]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @esub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @nxt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @escale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @residue_fact]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @bump]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @set_reg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @eadd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @esize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @bigb]; [@Corelib; @Lists; @ListDef; @seq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_havoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_bigsubst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mkind]; [@Stdlib; @Lists; @List; @find]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @find_containingB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @find_containing]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @mkSrlB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @shadow_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @shadow_ofB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @shadow_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @mkSrl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @mkSrlB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @KRWLAZY]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @shadow_factsB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @shadow_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @find_containingB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @shadow_ofB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @vis_cost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @shadow_factsB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @flat_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @vis_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @vis_add_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @find_disj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @disj_side_fact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_shdisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_shdisj_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @reg_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @page_up]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mmap_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mmap_len_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @inside_mapsB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @inside_maps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @safe_rangeB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @safe_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @CEIL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @inside_mapsB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @grant_keep_bB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @grant_keep_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @safe_rangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kimg_clip]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_grant_filterB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_grant_filter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @grant_keep_bB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_rezeroB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_rezero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_rezeroM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_rezeroB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @fixed_in_arm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @fixed_args]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @KRW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @KNONE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @KNONELAZY]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @fixed_in_args]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @fixed_in_args_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @budget_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @rekind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mmap_fixed_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mmap_fixed_in_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @ENOMEM_RET]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @dest_lfact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @dest_rfact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @AM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @replace_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mmap_destroyed_with]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mmap_destroyed_with_ref]; [@Corelib; @Lists; @ListDef; @map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @dest_cases]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_mprotect]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_mprotect_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @amap_matchB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @amap_match]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @len_eqbB_eqf]; [@Stdlib; @Lists; @List; @fold_left]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_unfillM_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @page_alignedB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kzero_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @amap_matchB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_munmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_munmap_ref]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @KFOG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @vis_here]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_unvis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_unvis_ref]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @SPIN_WORD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @ret_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @after_call]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kimg_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_havocM_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @off_image_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwritable_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_fill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_fill_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @copy_factsB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @copy_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kread8eB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kread_bytesB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @copy_factsB_eqf']; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @after_call2]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @NCS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kblob_prefix]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @copy_factsB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_copy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_copy_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @x_memiszero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @eaddz]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kwritableB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_miz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_miz_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @img_covB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @img_cov]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @x_istrncpy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @x_sealed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @SEALED_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_istrncpy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_istrncpy_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @x_popfree]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @popfree_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @x_sniff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @sniff_tab]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @sniff_cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kn_readableB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_readable_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @extKB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @kn_readable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @extK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @kn_readableB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @img_covB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3B; @AX2B; @extKB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_sniff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @summary_sniff_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @e_envp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @V_ENVC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @e_auxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @e_str0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @V_L0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @V_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kentry_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kw_argv1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @e_argv1w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @V_ARGC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @e_str1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @asubst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @esubst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @FdFile]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @nt_set]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @nt_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @erename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @a_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @arename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @evars_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kvars_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @emaxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kmaxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @krename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mrename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @prename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @frename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @evars_fo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kvars_fo]; [@Stdlib; @Lists; @List; @rev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @number_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @csvars_fo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @node_rename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @compact_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @saddr_eqb_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kflat_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kentry_eqb_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kimg_sub_covered]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kunk_covered]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_incl1_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @s_resv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @regs_match_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_incl_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @kn_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @maps_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @pairs_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @fd_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @list_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @amap_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @pair_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @afd_eqb]; [@Stdlib; @Bool; @Bool; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @loopctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @shape]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @respell_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @hw_go]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @WithSegs; @mk_itab_ranges_acc]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @e_atrandom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @e_auxb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @e_atrb]; [@Corelib; @Lists; @ListDef; @repeat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @e_sp0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @atable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @ACS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @mk_ss]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @a_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @init_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @NX0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @amap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @MBASE_MIN]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @init_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @vis_cost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @escale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @V_BRK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @FdStd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @init_acs_of_with]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @init_kn]; [@Corelib; @Init; @Nat; @of_num_uint]; [@Corelib; @Init; @Number; @UIntDecimal]; [@Corelib; @Init; @Decimal; @D2]; [@Corelib; @Init; @Decimal; @D5]; [@Corelib; @Init; @Decimal; @D6]; [@Corelib; @Init; @Decimal; @D3]; [@Corelib; @Init; @Decimal; @Nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @init_acs_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @ASAN]; [@Corelib; @Init; @Decimal; @D7]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCore; @APC; @BOTH]].

Import ListNotations.
Open Scope Z_scope.

Module APC.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import AX2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CEIL : Z := 0x7fff7f800000.
(* [comment removed for export] *)
Definition KHI : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition FLOOR : Z := 0x2aaaaaaab000.
(* [comment removed for export] *)
Definition MBASE_MIN : Z := 0x154555557000.
(* [comment removed for export] *)
Definition PID_MAX : Z := 4194304.

Record atable : Type := AT {
  img_lo : Z; img_hi : Z;          (* [comment removed for export] *)
  n_res : nat;                     (* [comment removed for export] *)
  shadow_off : Z;                  (* [comment removed for export] *)
  a_entry : Z;                     (* [comment removed for export] *)
  rw_lo : Z; rw_len : Z;           (* [comment removed for export] *)
  ph_addr_z : Z; ph_ent_z : Z; ph_num_z : Z;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  x_imemset : Z; x_imemcpy : Z; x_memset : Z; x_memcpy : Z; x_memiszero : Z;
  (* [comment removed for export] *)
  x_istrncpy : Z; x_sealed : Z; x_popfree : Z;
  (* [comment removed for export] *)
  x_sniff : Z; sniff_tab : Z; sniff_cell : Z;
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z              (* [comment removed for export] *)
}.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive spiece : Type := SPLit (bs : list Z) | SPBlob (k : nat).

Inductive shape : Type :=
| SNil
| SExit (code : Z)
| SEmitP (fd : Z) (ps : list spiece) (s : shape)   (* [comment removed for export] *)
| SAlt2 (a b : shape)
| SCase (e : expr) (mid : Z) (s1 s2 : shape)
| SHole (h : nat)                            (* [comment removed for export] *)
| SNext.                                     (* [comment removed for export] *)

Definition salt2 (a b : shape) : shape :=
  match a, b with SNil, _ => b | _, SNil => a | _, _ => SAlt2 a b end.

Fixpoint listZ_eqb (x y : list Z) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => Z.eqb a b && listZ_eqb x' y' | _, _ => false end.
Definition spiece_eqb (x y : spiece) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1+2+3$x;R+0$y;R+0-0RN$x;R+0+1#22$a;R0-0RN$y;R+0+1#22$b;R0!2'4#2#1$k;R+5,6$k;R+5-0RN$y;R+0+1#22$bs;R0,6$k';R+5!2'7#2#1").
Fixpoint spieces_eqb (x y : list spiece) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => spiece_eqb a b && spieces_eqb x' y' | _, _ => false end.
Fixpoint shape_eqb (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb a a' && shape_eqb b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb a a' && shape_eqb b b'
  | SHole h, SHole h' => Nat.eqb h h'
  | SNext, SNext => true
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mkind : Type := KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE.   (* [comment removed for export] *)

Definition mkind_eqb (a b : mkind) : bool :=
  match a, b with
  | KRW, KRW | KRWLAZY, KRWLAZY | KNONE, KNONE | KNONELAZY, KNONELAZY | KFOG, KFOG | KHOLE, KHOLE => true
  | _, _ => false
  end.

(* [comment removed for export] *)
Record amap : Type := AM {
  am_base : expr;       (* [comment removed for export] *)
  am_len  : expr;       (* [comment removed for export] *)
  am_kind : mkind
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_tok_kind (k : mkind) : bool := match k with KFOG | KHOLE => true | _ => false end.
Definition is_hole (m : amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$m;R+8!2'9!1':#1,;").
Definition is_fog (m : amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$m;R+8!1'<!1':#1").
Definition no_fog (ms : list amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$ms;R!1+2+8!3'=+8$m;R+8!1'>!1'?#1#1").
Definition no_holes (ms : list amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$ms;R!1+2+8!3'=+8$m;R+8!1'>!1'@#1#1").


(* [comment removed for export] *)
Inductive afd : Type :=
| FdStd                                   (* [comment removed for export] *)
| FdFile (k : nat) (len off : expr)       (* [comment removed for export] *)
| FdDir.                                  (* [comment removed for export] *)

Record acs : Type := ACS {
  a_ss    : sym_state;          (* [comment removed for export] *)
  a_maps  : list amap;          (* [comment removed for export] *)
  a_totsz : Z;                  (* [comment removed for export] *)
  a_ylo   : Z;                  (* [comment removed for export] *)
  a_eager : Z;                  (* [comment removed for export] *)
  a_vis   : list (expr * expr); (* [comment removed for export] *)
  a_ghost : list (expr * expr); (* [comment removed for export] *)
  a_abytes : Z;                 (* [comment removed for export] *)
  a_brk   : expr;               (* [comment removed for export] *)
  a_fd    : afd;
  a_tidset : bool               (* [comment removed for export] *)
}.

Definition reg (cs : acs) (n : nat) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$n;R+5!4'B+C#1!1'D!1'E#2!1,F,G").
Definition kn (cs : acs) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+A!1'H!1'E#1").
Definition pc (cs : acs) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+A!1'I!1'E#1").
Definition nxt (cs : acs) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+A!1'J!1'E#1").

Definition with_ss (cs : acs) (ss : sym_state) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$ss;R+K!;,L#1!1'M#2!1'N#2!1'O#2!1'P#2!1'Q#2!1'R#2!1'S#2!1'T#2!1'U#2!1'V#2").
Definition mk_ss (p : Z) (sr : list expr) (k : list kentry) (nx : nat) : sym_state := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$p;R+3$sr;R!1+2+C$k;R!1+2+W$nx;R+5!6,X#4#3!1,Y+Z#2#1!1,[+\").
Definition set_reg (cs : acs) (n : nat) (e : expr) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$cs;R+A$n;R+5$e;R+C&ss;R!1'E#3+K!2'^0#4!4'^1!1'I#1!3'^2!1'D#1#3#2!1'H#1!1'J#1").
Definition set_pc (cs : acs) (p : Z) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$p;R+3&ss;R!1'E#2+K!2'^0#3!4'^1#2!1'D#1!1'H#1!1'J#1").
Definition set_kn (cs : acs) (k : list kentry) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$k;R!1+2+W&ss;R!1'E#2+K!2'^0#3!4'^1!1'I#1!1'D#1#2!1'J#1").
Definition add_kn (cs : acs) (k : list kentry) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$k;R!1+2+W!2'^3#2!3'^4+W#1!1'^5#2").
Definition bump (cs : acs) (d : nat) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$d;R+5&ss;R!1'E#2+K!2'^0#3!4'^1!1'I#1!1'D#1!1'H#1!2'^6!1'J#1#2").
Definition set_regs (cs : acs) (sr : list expr) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$sr;R!1+2+C&ss;R!1'E#2+K!2'^0#3!4'^1!1'I#1#2!1'H#1!1'J#1").

Definition lit_of (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!1,[+3$e;R+C-CRN$e;R+C!1+^7+3#18$z;R+3!2,^8+3!2'^9#1'^:$n;R+50$op;R+^;$a;R+C$b;R+C0$op;R+^;$a;R+C$b;R+C0$op;R+^<$a;R+C$b;R+C0$op;R+^<$a;R+C$b;R+C0$sx;R+1$lo;R+5$n;R+5$e0;R+C0$sx;R+1$k;R+5$i;R+3$n;R+50").
Definition reg_lit (cs : acs) (n : nat) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$n;R+5!1'^=!2'^>#2#1").

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition esub (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+C$b;R+C!3'^?,^@#2#1").
Definition escale (c : Z) (e : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$c;R+3$e;R+C!3'^A,^B!1,F#2#1").
Definition eaddz (a : expr) (z : Z) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+C$z;R+3!3'^?,^C#2!1,F#1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint expr_vars (e : expr) (acc : list nat) : list nat :=
  match e with
  | ELit _ => acc
  | EVar n => if existsb (Nat.eqb n) acc then acc else n :: acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars x (expr_vars y acc)
  | EExt _ _ _ x => expr_vars x acc
  | EBlob _ _ _ _ => acc
  end.

Definition live_vars (cs : acs) : list nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S60!1+2+5!1'^F#3!2'^E!1'^F#2!2'^E#1#3!2'^E1!2'^E#2#4!2+^I+C+C$p;R4$acc;R0!2'^E!3'^J+C+C#2!2'^E!3'^K+C+C#2#1$cs;R+A&acc;R!5'^D0+C'^E!1,Y+5!1'D!1'E#10&acc;R!5'^D0+W$K;R+W$acc;R0-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C!2'^E1!2'^E#1#4$a;R+\$n;R+C2$a;R+\$n;R+C$k;R+53$lo;R+3$hi;R+3#3$e;R+C$m;R+3#3$e;R+C$lo;R+3$hi;R+3#4$a;R+\$n;R+C2$a1;R+\$n1;R+C$a2;R+\$n2;R+C#5$a;R+\$n;R+C$c;R+33$a;R+\$n;R+C2#1!1'^5#20&acc;R!5'^D0+8$m;R+8$acc;R0!2'^E!1'^G#2!2'^E!1'^H#2#1#1!1'M#30&acc;R!5'^D045#1!1'Q#40&acc;R!5'^D045#1!1'R#50&acc;R-^LRN$x;R+^L0!1'U#63#1$k;R+5$l;R+C$o;R+C!2'^E#2!2'^E#1#4#10!2'^E!1'T#7#1").

Definition all_live (live : list nat) (e : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$live;R!1+2+5$e;R+C!3'=+5$v;R+5!2'^M!2'^N#1/nx0;!3'^O+5!1'7#1#3!2'^E#1!1,Y+5").

Definition kn_gc_entry (spb : expr) (spk : Z) (live : list nat) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S30!2'^S#2#1-\RN$a;R+\+1#21$b;R+C$k;R+3-CRN$n0;R+C+1#38$n;R+3!1'>!2'^P!2'^Q#3#9!2'^R0#8$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k0;R+5$i;R+3$n;R+5,^U!1'>!2'^P!2'^Q#3#:!2'^R0#9$spb;R+C$spk;R+3$live;R!1+2+5$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!1'>!2'^P!2'^Q#2#9!2'^R!2'^S#1!1'^T#4#8$a;R+\$n0;R+C1$a;R+\$n0;R+C$k0;R+5-\RN$a;R+\+1#31$b;R+C$k;R+3-CRN$n0;R+C+1#48$n;R+32$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k1;R+5$i;R+3$n;R+5,^U$lo;R+3$hi;R+3,^U$e;R+C$m;R+3!2'^V#4#2$e;R+C$lo;R+3$hi;R+3!2'^V#5#3$a;R+\$n;R+C,^U$a1;R+\$n1;R+C$a2;R+\$n2;R+C!2'^P!2'^P!2'^P!2'^V#6!1'^F#4!2'^V#6#3!2'^V#6!1'^F#2!2'^V#6#1$a;R+\$n0;R+C$c;R+3-\RN$a;R+\+1#31$b;R+C$k;R+3-CRN$n0;R+C+1#48$n;R+32$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k0;R+5$i;R+3$n;R+5,^U$a;R+\$n0;R+C1").

Definition cs_gc_ref (cs : acs) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+A-^IRN$x;R!2+^I+C+3+A!1'^W!2'^>#1}21$spb;R+C$spk;R+3&live;R!1'^X#3!1+2+5!2'^3#4!3'^Y+W!3'^Z#3#2#1!1'^5#4").

(* [comment removed for export] *)
Definition vkey (n : nat) : positive := Pos.of_succ_nat n.
Fixpoint expr_vars_t (e : expr) (acc : ptree unit) : ptree unit :=
  match e with
  | ELit _ => acc
  | EVar n => pt_set (vkey n) tt acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_t x (expr_vars_t y acc)
  | EExt _ _ _ x => expr_vars_t x acc
  | EBlob _ _ _ _ => acc
  end.
Definition live_vars_t (cs : acs) : ptree unit := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S60!1+^[+^\!1'^F#3!2'_0!1'^F#2!2'_0#1#3!2'_01!2'_0#2#4!2+^I+C+C$p;R4$acc;R0!2'_0!3'^J+C+C#2!2'_0!3'^K+C+C#2#1$cs;R+A&acc;R!5'^D0+C'_0!1,_1+^\!1'D!1'E#10&acc;R!5'^D0+W$K;R+W$acc;R0-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C!2'_01!2'_0#1#4$a;R+\$n;R+C2$a;R+\$n;R+C$k;R+53$lo;R+3$hi;R+3#3$e;R+C$m;R+3#3$e;R+C$lo;R+3$hi;R+3#4$a;R+\$n;R+C2$a1;R+\$n1;R+C$a2;R+\$n2;R+C#5$a;R+\$n;R+C$c;R+33$a;R+\$n;R+C2#1!1'^5#20&acc;R!5'^D0+8$m;R+8$acc;R0!2'_0!1'^G#2!2'_0!1'^H#2#1#1!1'M#30&acc;R!5'^D045#1!1'Q#40&acc;R!5'^D045#1!1'R#50&acc;R-^LRN$x;R+^L0!1'U#63#1$k;R+5$l;R+C$o;R+C!2'_0#2!2'_0#1#4#10!2'_0!1'T#7#1").
Definition in_live_t (t : ptree unit) (v : nat) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+^[+^\$v;R+5-^7RN$x;R!1+^7+^\+1!3'_2+^\#2!1'_3#12$u;R+^\,^U,6").
Fixpoint expr_all_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if Nat.ltb n nx0 then true else in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_t t x then expr_all_live_t t y else false
  | EExt _ _ _ x => expr_all_live_t t x
  | EBlob _ _ _ _ => true
  end.
Definition kn_gc_entry_t (spb : expr) (spk : Z) (t : ptree unit) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S30!2'^S#2#1-\RN$a;R+\+1#21$b;R+C$k;R+3-CRN$n0;R+C+1#38$n;R+3!1'>!2'^P!2'^Q#3#9!2'^R0#8$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k0;R+5$i;R+3$n;R+5,^U!1'>!2'^P!2'^Q#3#:!2'^R0#9$spb;R+C$spk;R+3$t;R!1+^[+^\$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!1'>!2'^P!2'^Q#2#9!2'^R!2'^S#1!1'^T#4#8$a;R+\$n0;R+C1$a;R+\$n0;R+C$k0;R+5-\RN$a;R+\+1#31$b;R+C$k;R+3-CRN$n0;R+C+1#48$n;R+32$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k1;R+5$i;R+3$n;R+5,^U$lo;R+3$hi;R+3,^U$e;R+C$m;R+3!2'_4#4#2$e;R+C$lo;R+3$hi;R+3!2'_4#5#3$a;R+\$n;R+C,^U$a1;R+\$n1;R+C$a2;R+\$n2;R+C!2'^P!2'^P!2'^P!2'_4#6!1'^F#4!2'_4#6#3!2'_4#6!1'^F#2!2'_4#6#1$a;R+\$n0;R+C$c;R+3-\RN$a;R+\+1#31$b;R+C$k;R+3-CRN$n0;R+C+1#48$n;R+32$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k0;R+5$i;R+3$n;R+5,^U$a;R+\$n0;R+C1").
Definition cs_gc (cs : acs) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+A-^IRN$x;R!2+^I+C+3+A!1'^W!2'^>#1}21$spb;R+C$spk;R+3&live;R!1'_5#3!1+^[+^\!2'^3#4!3'^Y+W!3'_6#3#2#1!1'^5#4").

(* [comment removed for export] *)
Definition live_agree (acc : list nat) (t : ptree unit) : Prop :=
  forall v, existsb (Nat.eqb v) acc = in_live_t t v.
Lemma vkey_inj : forall a b, vkey a = vkey b -> a = b.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80!1'_;#3!1'_;#2!1'_:0!1'_:!1'_;#4!1,_=#4!1'_>#4!1,_=#6!1,_=#5$a;R+5$b;R+5$H;R!3+_7+_8!1'_3#2!1'_3#1&H;R!6'_9+_8+5'_:01#1!3+_7+52!1'_:1&H;R!6'_<+53$n;R+5!3+_7+5#13#145!3+_7+542&H;R!6'_<+53$n;R+5!3+_7+56#1#145!3+_7+574!6'_9+5+5$t;R+5-5RN$n;R+5+5#12#7$~R+5#167#1").
Qed.
Lemma live_agree_var : forall acc t n,
  live_agree acc t -> live_agree (if existsb (Nat.eqb n) acc then acc else n :: acc) (pt_set (vkey n) tt t).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SO0!1+2+5!3+_7+5#1#3!3+_7+5#2#4!1'_B2!1'7#3!1'7#5!1'_3#3!3+_7+5#3#5!1'7#1!1'7#7!3'^O+59#9!3,_C+5#7#9-1RN$~R+10:2#9;!1+^7+^\-^7RN$x;R!1+^7+^\+1#12$u;R+^\,^U,6!1'7#6!3'^O+5?#8!1'7#9!1'7#:!3'^O+5!1'7#8#:!1'_3#6!4'_D+^\D,_E#7!1'_3#4!3'_2+^\#7F!3'^O+55<!1'7#4!3'^O+55#9!3'^O+5A#=!3+_7+5#7#9!3+_7+5#8#:!3+_7+_8FD$acc;R0$t;R!1+^[+^\$n;R+5$H;R!2'_?#3#2vd$v;R+5vd&s;R!2'_@#1#3!2+_A1!1'_B1-_ARN$s;R!2+_A23!3+_7+1!3'^O+54-1RN$~R+10!3'^O+55#72#7!3,_C+5#5#7-^7RN$x;R!1+^7+^\+1!3'_2+^\!4'_D+^\!1'_3#5,_E#662$u;R+^\,^U,6#12$e;R2!1$e;R7!6'_F+5#6$v;R+5!3+_7+1!3'^O+58<-^7RN$x;R!1+^7+^\+1!3'_2+^\!4'_D+^\!1'_3#7,_E#8!1'_3#12$u;R+^\,^U,6!6'_F=!2,^8+^\,_E$o;R=!3+_7+1!3'^O+59<>&b;R@+1&E;R!2,_G+1#1!3+_7+1:#1!1-1RN$b;R+1%E;R!3+_7+1!3'^O+5A#;#1!3+_7+1!3'^O+5B-1RN$~R+10#22#<!3,_C+5#:#<,^U#22$E;R!3+_7+1C,^U#1$E;R!3+_7+1C,6vd!6'_F+1,^U$b;R+1!3+_7+1!2'^M#1!3'^O+5B#<,^U!2,_G+1,^U!2'7#9#9!1'_H#9!3+_7+1!3'^O+5A!3,_C+5#9#;,^U#1!3'_2+^\ED!4'_I+^\D,_E#7#4#1#1$n;R3!1$NE;R!1'_B7!6'_F=G$o;R=!3+_7+1H>vd!6'_<+1!3'^O+5I#8$b;R+1!3+_7+1H#1&b;R@+1-1RN$b;R+1!3+_7+1!3'^O+5?-1RN$~R+10#12#:!3,_C+5#8#:!3'^O+5?#:#12!2,_G+1Jvd&r;R!2'_J#5#7!2+_K!3+_7+5#5#7!2'7#5#7&b;R!2'7#6#8+1-_KRN$b;R+1$r;R!2+_K!3+_7+5#8#:#1!3+_7+1!2'^M#2KK#22$e;RL!1$e;RM!2'_L!3+_7+1!2'^M,^UKK!1#6#1#1$n;R!1'_BL!1$n0;R!1'_BM!2,_G+1K#1!3+_7+1!3'^O+55;J!2'_M#7#4!1#5#4!3+_7+1!3'^O+5I-1RN$~R+10@2#8!3,_C+5#6#8-^7RN$x;R!1+^7+^\+1G2$u;R+^\,^U,6!3'_2+^\EF!6'_N+^\FD,_E#7vd$HK;RN!1#2!3'_O#5#7#1!1'_BN#1!3+_7+1!3'^O+58-1RN$~R+10!3'^O+54#52#5!3,_C+5#3#5!2'_M!4'_D+^\6,_E#4#1!2'_?-1RN$~R+10!3'^O+5!1'7#2#42#4!3,_C+5#2#4!4'_D+^\!1'_3#2,_E#3").
Qed.
Lemma live_agree_expr : forall e acc t, live_agree acc t -> live_agree (expr_vars e acc) (expr_vars_t e t).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S>0!1+2+5!1+^[+^\!2'_?#2#1%acc;R0%t;R1%~R2!2'_?!2'^E#4#3!2'_0#4#2!1,F#4!1,_R#4!3#4#3#2#1!3#6!2'^E#5#3!2'_0#5#26!3,_S#8#7#5!3,_T#8#7#5!3,_U#8#7#5!3,_V#8#7#5!4,_W#8#7#6#5!4,_X#7#6#5#4$e;R+C!:'_P$e;R+C3$z;R+3$acc;R0$t;R1$H;R2vd#1!2'_?!2'^E4#3!2'_04#2$n;R+5$acc;R0$t;R1$H;R2vd!4'_Q#3#2#4#1!2'_?!2'^E5#3!2'_05#2$op;R+^;$e1;R+C$IHe1;R3$e2;R+C$IHe2;R3$acc;R0$t;R1$H;R2vd7!2'_?!2'^E8#3!2'_08#2$op;R+^;$e1;R+C$IHe1;R3$e2;R+C$IHe2;R3$acc;R0$t;R1$H;R2vd7!2'_?!2'^E9#3!2'_09#2$op;R+^<$e1;R+C$IHe1;R3$e2;R+C$IHe2;R3$acc;R0$t;R1$H;R2vd7!2'_?!2'^E:#3!2'_0:#2$op;R+^<$e1;R+C$IHe1;R3$e2;R+C$IHe2;R3$acc;R0$t;R1$H;R2vd7!2'_?!2'^E;#3!2'_0;#2$sx;R+1$lo;R+5$n;R+5$e;R+C$IHe;R3$acc;R0$t;R1$H;R2vd6!2'_?!2'^E<#3!2'_0<#2$sx;R+1$k;R+5$i;R+3$n;R+5$acc;R0$t;R1$H;R2vd#1!2'_?!2'^E=#3!2'_0=#2#1").
Qed.
Lemma live_agree_fold : forall (X : Type) (f : X -> list nat -> list nat) (g : X -> ptree unit -> ptree unit) (l : list X) acc t,
  (forall a acc t, live_agree acc t -> live_agree (f a acc) (g a t)) ->
  live_agree acc t -> live_agree (fold_right f acc l) (fold_right g t l).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S33lcd;g^Dbd;lcd;g_Yd;<scd;!1+2+5!1+^[+^\!3,_C#;#3#2$X;R{cd;$f;R%~R#1%~R00$g;R%~R#2%~R11$l;R!1+2#3$acc;R0$t;R1$Hfg;R%a;R#6%acc;R0%t;R1%~R!2'_?#2#1!2'_?!2#9#4#3!2#8#4#2$H;R!2'_?#3#2!5'_Y#8$l;R!1+2#8!2'_?!5'^D0#9#8#5#1!5'^D1#9#7#4#1#1$a;R#8$r;R!1+2#9$IH;R!2'_?!5'^D0#:#9#6#1!5'^D1#:#8#5#1vd!4#5#3!5'^D0#;#:#7#2!5'^D1#;#9#6#2#1!2'_?!5'^D0#;#:#72!5'^D1#;#9#62#5").
Qed.
Lemma live_vars_agree : forall cs, live_agree (live_vars cs) (live_vars_t cs).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^H0!1+2+5!1'U#1!2+^I+C+C!3'^J+C+C#2!3'^K+C+C#2$p;R2$acc;R0!2'^E3!2'^E4#1!1'^G#2!1'^H#2$m;R+8$acc;R0!2'^E6!2'^E7#1!1'^F#3!1'^F#2!2'^E:!2'^E#1#3!2'^E9!2'^E#2#4$K;R+W$acc;R0-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C!2'^E9!2'^E#1#4$a;R+\$n;R+C;$a;R+\$n;R+C$k;R+5<$lo;R+3$hi;R+3#3$e;R+C$m;R+3#3$e;R+C$lo;R+3$hi;R+3#4$a;R+\$n;R+C;$a1;R+\$n1;R+C$a2;R+\$n2;R+C#5$a;R+\$n;R+C$c;R+3<$a;R+\$n;R+C;!1,Y+5!1'D!1'E#1!1'^5#1!1'M#1!1'Q#1!1'R#1!5'^D025!5'^D025!5'^D0+88!5'^D0+W=!5'^D0+C'^E>?@ABC!1'D!1'E#4!1'^5#4!1'M#4!1'Q#4!1'R#4!1+^[+^\$p;R2$acc;RJ!2'_03!2'_04#1$m;R+8$acc;RJ!2'_06!2'_07#1!2'_0:!2'_0#1#3!2'_09!2'_0#2#4$K;R+W$acc;RJ-WRN$K;R+WJ#2:$a;R+\$w;R+5$v;R+C!2'_09!2'_0#1#4$a;R+\$n;R+CM$a;R+\$n;R+C$k;R+5N$lo;R+3$hi;R+3#3$e;R+C$m;R+3#3$e;R+C$lo;R+3$hi;R+3#4$a;R+\$n;R+CM$a1;R+\$n1;R+C$a2;R+\$n2;R+C#5$a;R+\$n;R+C$c;R+3N$a;R+\$n;R+CM!1,_1+^\!5'^DJ2K!5'^DJ2K!5'^DJ+8L!5'^DJ+WO!5'^DJ+C'_0P?@ABC!1+^7+^\!1'_3#1!2'_?>P!2'_?#2#1!1'U#5!2'^E#1#8!2'_0#1#7!2'^E#1#:!2'_0#1#9!2'^E#1#6!2'_0#1#5!1'D!1'E#3!5'^D0+C'^E>^0!1'^5#3!5'^D0+W=^1^2!1'M#3!5'^D0+88^3^4!1'Q#3!5'^D025^5^6!1'R#3!5'^DJ+C'_0P^0!5'^DJ+WO^9^2!5'^DJ+8L^:^4!5'^DJ2K^;^6!3'^K+C+C#4$a;R2$acc;R0$t;RJ$~RU!4'_Z!3'^J+C+C#4!2'^E^=#3!2'_0^=#2!4'_Z^=#3#2#1!1'^H#4!2'^E:[!2'^E9!2'^E#2#7!2'_0:\!2'_09!2'_0#2#6!1'^F!2,`0#4#3!2$a;R+\-\RN$s;R+\%n;R+C!2'_?!2'^E:W!2'_0:X#11$a_base;R+C$a_off;R+3!2$a_base0;R+C$a_off0;R+3$n;R+C!4'_Z!1'^F!2,`0#3#2!2'^E#1#;!2'_0#1#:!4'_Z#1#;#:#9#2#1#2#1!2'_?!2'^E9!2'^E#2#:!2'_09!2'_0#2#9!4'_Z^D!2'^E#2#=!2'_0#2#<!4'_Z#2#=#<#;$cs;R+Avd!4'_Z!1'T#1-^LRN$x;R+^L013D$k;R+5$l;R+C$o;R+C!2'^E#2!2'^E#1!5'^D025!5'^D025!5'^D0+88!5'^D0+W=!5'^D0+C'^E>EFGHID-^LRN$x;R+^LJ13Q$k;R+5$l;R+C$o;R+C!2'_0#2!2'_0#1!5'^DJ2K!5'^DJ2K!5'^DJ+8L!5'^DJ+WO!5'^DJ+C'_0PEFGHIQ&A0;Rvd$v;R+5vd!6'_FR!1,[+^\$o;RR!3+_7+1!3'^O+5!1'7#2>-^7RN$x;R!1+^7+^\+1#12$u;R+^\,^U,6!2,_G+1,6!3'_2+^\PS!2'_[+^\S!3+_7+1!3'^O+5!1'7#1>!2'_MP#1TT&A5;R$acc;R0$t;RJ$H;RU&a;RV+^L-^LRN$a;R+^L!2'_?-^LRN$x;R+^L0#13#5$k;R+5$l;R+C$o;R+C!2'^E#2W#5-^LRN$x;R+^LJ#13#4$k;R+5$l;R+C$o;R+C!2'_0#2X#4#13#2$k;R+5$len;R+C$off;R+C!3$k;R+5$len;R+C$off;R+C!4'_Z#2YZ!4'_Z#1#:#9#8#3#2#1#2%acc;R0%t;RJ%~RU!2'_?-^LRN$x;R+^L0V3#3$k;R+5$l;R+C$o;R+C!2'^E#2[#3-^LRN$x;R+^LJV3#2$k;R+5$l;R+C$o;R+C!2'_0#2\#2!3#1!5'^D025^7^8!5'^DJ2K^<^8!8'_\25K^8^7^<^>!8'_\25K^6^5^;^>!8'_\+88L^4^3^:$a;R+8$acc;R0$t;RJ$~RU!4'_Z!1'^G#4!2'^E^?#3!2'_0^?#2!4'_Z^?#3#2#1!8'_\+W=O^2^1^9$a;R+W$acc;R0$t;RJ$H;RU-WRN$k;R+W!2'_?-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C!2'^E9!2'^E#1#7$a;R+\$n;R+C^@$a;R+\$n;R+C$k;R+5^A$lo;R+3$hi;R+3#6$e;R+C$m;R+3#6$e;R+C$lo;R+3$hi;R+3#7$a;R+\$n;R+C^@$a1;R+\$n1;R+C$a2;R+\$n2;R+C#8$a;R+\$n;R+C$c;R+3^A$a;R+\$n;R+C^@-WRN$K;R+WJ#1:$a;R+\$w;R+5$v;R+C!2'_09!2'_0#1#6$a;R+\$n;R+C^B$a;R+\$n;R+C$k;R+5^C$lo;R+3$hi;R+3#5$e;R+C$m;R+3#5$e;R+C$lo;R+3$hi;R+3#6$a;R+\$n;R+C^B$a1;R+\$n1;R+C$a2;R+\$n2;R+C#7$a;R+\$n;R+C$c;R+3^C$a;R+\$n;R+C^B#4:$a;R+\$w;R+5$v;R+C!3$a;R+\-\RN$s;R+\%w;R+5%v;R+C!2'_?!2'^E9Y!2'_09Z#11$a_base;R+C$a_off;R+3!2$a_base0;R+C$a_off0;R+3$w;R+5$v;R+C!4'_Z^D!2'^E#1#=!2'_0#1#<!4'_Z#1#=#<#;#2#1#3#2#1$a;R+\$n;R+C^E$a;R+\$n;R+C$k;R+5!3$a;R+\-\RN$s;R+\%n;R+C%k;R+5^F#11$a_base;R+C$a_off;R+3!2$a_base0;R+C$a_off0;R+3$n;R+C$k;R+5^G#2#1#3#2#1$lo;R+3$hi;R+3!2$lo;R+3$hi;R+3#5#2#1$e;R+C$m;R+3!2$e;R+C$m;R+3#5#2#1$e;R+C$lo;R+3$hi;R+3!3$e;R+C$lo;R+3$hi;R+3#7#3#2#1$a;R+\$n;R+C^E$a1;R+\$n1;R+C$a2;R+\$n2;R+C!4$a1;R+\$n1;R+C$a2;R+\$n2;R+C#9#4#3#2#1$a;R+\$n;R+C$c;R+3!3$a;R+\-\RN$s;R+\%n;R+C%c;R+3^F#11$a_base;R+C$a_off;R+3!2$a_base0;R+C$a_off0;R+3$n;R+C$c;R+3^G#2#1#3#2#1$a;R+\$n;R+C^E!8'_\+C'^E'_0^0>P$a;R+C$acc;R0$t;RJ$~RU!4'_Z#4#3#2#1#2!2'_?!1'^X#1!1'_5#1").
Qed.
Lemma forallb_expr_vars : forall P e acc,
  forallb P (expr_vars e acc) = (forallb P (expr_vars e []) && forallb P acc)%bool.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^70!1+2+5!2'^E#2#1!1,Y+5!2'^E#22!3'=+5#4#1!1,F#2!2,_G+1#1!1'7#5!3'=+5#8#5!3'^O+5!1'7#4#3!1#7#5!2'^P#18!1#8#6!3'=+5#;#8!1#9#7!3'=+5#:#7!3'=+5#<#9%~R#1+1!1+2#2%~R!3+_7+1!3'^O#3#2#1,^U!2+`2#4$x;R#4!2+`3!3'`4#5#1#3!3+_7+1!1#4#1,^U!3'`4+5#2#@%~R!3+_7+1!2'7#2#1,^U!3+_7+5#3#2!2'^P:,^U!1'`=:!3'=+5#7#4!2'^P!3'=+5#7-1RN$~R+10!3'^O+57222!3,_C+5#52H!1,_R#2%acc;R0!3+_7+1!3'=+5#51!2'^P!3'=+5#53!3'=+5#5#1!3'=+5#7#1%acc;R0!3+_7+1!3'=+5#71!2'^P!3'=+5#73L!3'=+5#8!2'^E#52!2'^E#3#1!3'=+5#8O!2'^E#42!3'=+5#9#2!2'^P!3'=+5#9!2'^E#6QR!2'^E#32!3'=+5#8T!3'=+5#8#1!2'^PUV!3'=+5#9!2'^E#62!2'^PNU!3'=+5#9Q!2'^PYV!1#2#1!6'_F+1!2'^PNP$b;R+1!3+_7+1#1S!6'_F+1W$b;R+1!3+_7+1!2'^PX#1S!6'_F+1Y$b;R+1!3+_7+1!2'^PX!2'^PZR!2'^P#1R!6'_F+1[$b;R+1!3+_7+1#1!2'^P!2'^PXZR!2,_G+1[!2'^PNW!3'`>NUV!3'=+5#8!2'^E#5T!1#4TP\!3'=+5#8!2'^E#5O!1#4O!3,_S#6#5#3!3,_T#6#5#3!3,_U#6#5#3!3,_V#6#5#3!4,_W#6#5#4#3!4,_X#5#4#3#2$P;R%~R+5+1$e;R+C!:'_P$e;R+C%acc;R0!3+_7+1!3'=+5#41!2'^P!3'=+5#434$z;R+3$acc;R0vd!2,_G+1!2'^P!3'=+5#424!3+_7+1!3'=+5#4!2'^E5#1!2'^P!3'=+5#4!2'^E524$n;R+5$acc;R0vd&b;R!3'^O+5!1'7#2#1+1&E;R6!3+_7+1!3'^O+5!1'7#3#2#1!1-1RN$b;R+1%E;R!3+_7+1!3'^O+57#4#1!3+_7+1!3'=+5#8-1RN$~R+10#22#5!3,_C+5#6#5!2'^P!3'=+5#8-1RN$~R+10!3'^O+5!1'7#6222!3,_C+5#628#22$E;R!3+_7+19,^Uvd!6'_F+1:$b;R+1!3+_7+18;&b;R:+1&Pn;R6!3+_7+1<#1!1-1RN$b;R+1%Pn;R!3+_7+1!1#:#8#1!3+_7+1=!2'^P#2=#22$Pn;R!3+_7+1>,^U!2,_G+1!2'^P,^U?$Pn;R!3+_7+1>,6vd&b;R?+1&F;R6!3+_7+1=#1!1-1RN$b;R+1%F;R!3+_7+1!3'=+5#=#:#1!3+_7+1#2,6#22$F;R!3+_7+1@,^U!2'_L!3+_7+1,^U,6&H;R$A;R{g=d;$f;RA$l;RB!5'`1C%~R!2+`2#3$x;R#3!2+`3!3'`4#4#1#2!3+_7+1!1#3#1,^U!3+_7+1!3'^O#4#3#2,^U%~R!3+_7+1!3'^O#3#2#1,^U!2+`2#4$x;R#4!2+`3!3'`4#5#1#3!3+_7+1!1#4#1,^U$~RC$~R%~R!2+`2#4$x;R#4!2+`3!3'`4#5#1#3!3+_7+1!1#4#1,^U!3+_7+1!3'^O#5#4#3,^U#2!3'`5#3#2#1%A;R{g=d;%f;RA%l;RBC&E;R!4#1+5!1'7#<#;#8!2+`2+5$x;R+5!2+`3!3'`4+5#1#<!3+_7+1!2'7#=#1,^U!5'`6+5$x;R+5!2+`3!3'`4+5#1#=!3+_7+1!2'7#>#1,^U+`7$x;R+5$~R!1$x;R+5!2+`3!3'`4+5#1#>!3+_7+1!2'7#?#1,^U#1!2$x;R+5$H;R!2+`3!3'`4+5#1#?!3+_7+1!2'7#@#1,^U!5'`1D!3+_7+1!2'7#A#2,^U+`7$~RD$~R!3+_7+1!2'7#B#3,^U!2$Hx;R!3'`4+5#4#B$Ex;R!3+_7+1!2'7#D#5,^U&H;R$n;R+5$m;R+5!5'`1E%~R!3+_7+5#2#1!3+_7+1!2'7#3#2,^U%~R!3+_7+1!2'7#2#1,^U!3+_7+5#3#2$~RE$~R%~R!3+_7+5#3#2!3+_7+1!2'7#4#3,^U#2!2'`8#2#1%n;R+5%m;R+5E&Ex;R!3#1#F#7#2!3+_7+5#F#7!7'_<+5#G$x;R+5%Hx;R!3'`4+5#1#G+`7$Hx;R!3'`4+5#G#F&C;R!6'`9%~R!3+_7+1!3'=+5#J#G,^U%x;R+5%~R!3'`4+5#1#I!3+_7+1!1#M#2,^U%~R%x;R+5%~R!3'`4+5#1#H!3+_7+1!1#L#2,^U!3+_7+1!3'=+5#K#H,^U!3'`:+5#J#G#>#H#1!3+_7+1!1#J#H,^U&C;R!6'_<+1!1#K#I$b;R+1!3+_7+1#1,^U#1,6#B!3+_7+1,6,^U&H;R!6'_<+1,6$e;R+1-1RN$b;R+1w#12+`7+`;,`<,^U#1+`7!2'_L+`7#1#8#1#4#2#1#1#2#1#1$F;R!3+_7+1@,6!2,_G+1,6#1!3+_7+1?!2'^P,6?#1FG!3+_7+1HI$E;R!3+_7+19,6vd!6'_F+1:$b;R+1!3+_7+1!2'^P<8;!2,_G+1!2'^P:HFG!3+_7+1!3'=+5#7!3,_C+5#5#4I#1!3+_7+1!3'=+5#4!2'^EJ#1!2'^P!3'=+5#4!2'^EJ24$op;R+^;$e1;R+C$IHe1;RK$e2;R+C$IHe2;RM$acc;R0vd^0!3+_7+1!3'=+5#8!2'^E^1#1!2'^P!3'=+5#8!2'^E^12V$op;R+^;$e1;R+C$IHe1;RK$e2;R+C$IHe2;RM$acc;R0vd^0!3+_7+1!3'=+5#8!2'^E^2#1!2'^P!3'=+5#8!2'^E^22V$op;R+^<$e1;R+C$IHe1;RK$e2;R+C$IHe2;RM$acc;R0vd^0!3+_7+1!3'=+5#8!2'^E^3#1!2'^P!3'=+5#8!2'^E^32V$op;R+^<$e1;R+C$IHe1;RK$e2;R+C$IHe2;RM$acc;R0vd^0!3+_7+1!3'=+5#8!2'^E^4#1!2'^P!3'=+5#8!2'^E^42V$sx;R+1$lo;R+5$n;R+5$e;R+C$IHe;RM$acc;R0vd\!3+_7+1!3'=+5#8!2'^E^5#1!2'^P!3'=+5#8!2'^E^52V$sx;R+1$k;R+5$i;R+3$n;R+5$acc;R0vd!2,_G+1!2'^P!3'=+5#72L!3+_7+1!3'=+5#7!2'^E^6#1!2'^P!3'=+5#7!2'^E^62L#1").
Qed.
Lemma expr_all_live_t_eq : forall acc t e, live_agree acc t -> expr_all_live_t t e = all_live acc e.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SW0!2'^N#1/nx0;!1'7#1$v;R+5!2'^M0!3'^O+51#6!1,Y+5!2'^E#13!2,_G+1,^U!1,F#1!3'^O+51#5!2'^N#2/nx0;!3'^O+5!1'7#2#6!2'^M-5RN$m;R+5+1/nx0;2,6$m';R+5!2'`?#2#17-5RN$m;R+5+1/nx0;2,6$m';R+5!2'`?#3#1-5RN$m;R+5+1/nx0;2,6$m';R+5!2'`?#4#1!3'^O+5!1'7#3#7!2,_G+1!2'^M;9!1,_R#1!3+_7+1!2'_4#5#1!3'=+5$v;R+5!2'^M0!3'^O+51#74$v;R+5!2'^M0!3'^O+51#9!3+_7+1!2'_4#7#1!3'=+5A4$v;R+5!2'^M0!3'^O+51#:!2'^E#43!3'=+5CD!2'^E#23!3'=+5CF!2'_4#9#5!2'_4#9#3$v;R+5!2'^M0!3'^O+51#;!2'^E#53!3'=+5JK!2'^PL!3'=+5J!2'^E#33!3'=+5$v;R+5!2'^M0!3'^O+51#=K!3'=+5$v;R+5!2'^M0!3'^O+51#<D!6'_F+1!2'^PEG$b;R+1!3+_7+1-1RN$~R+1+1H2I,6#1!6'_F+1E$b;R+1!3+_7+1-1RN$~R+1+1#12I,6M!6'_F+1G$b;R+1!3+_7+1-1RN$~R+1+1L2#1,6M&b;RE+1!1-1RN$b;R+1%IHe1;R!3+_7+1!2'_4#:#6#1!3+_7+1-1RN$~R+1+1#22N,6!2'^P#2N#12$IHe1;R!3+_7+1H,^U!2,_G+1!2'^P,^UO$IHe1;R!3+_7+1H,6!2,_G+1!2'^P,6O#4!2'_4#8#2#1!2'_4#8#4#3!3'=+5C!2'^E#4F!3'`@C#4F!3,_S#5#4#2!3,_T#5#4#2!3,_U#5#4#2!3,_V#5#4#2!4,_W#5#4#3#2!4,_X#4#3#2#1$acc;R!1+2+5$t;R!1+^[+^\$e;R+C$H;R!2'_?#3#2vd!:'_P$e;R+C!3+_7+1!2'_4#4#1!3'=+524$z;R+3vd5!3+_7+1!2'_4#46!3'=+52!2'^E63$n;R+5vd!6'_<+17$b;R+1!3+_7+1-1RN$~R+1+182,^U#1!2'^P!2'^M89,^Uvd!6'_F+1:$b;R+1!3+_7+1-1RN$~R+1+1;2,^U9#1&b;R0+1-1RN$b;R+1!3+_7+1-1RN$~R+1+1<2,^U=!2'^M<=#12>>!2'^P:,^U!1'`=:!3+_7+1-1RN$~R+1+102,^U7!2'^P!2'^M07,^U!2'_M#4#1!1#2#1!3+_7+1!2'_4#4?!3'=+52!2'^E?3$op;R+^;$e1;R+C$IHe1;R@$e2;R+C$IHe2;RBvdP!3+_7+1!2'_4#8Q!3'=+5C!2'^EQ3$op;R+^;$e1;R+C$IHe1;R@$e2;R+C$IHe2;RBvdP!3+_7+1!2'_4#8R!3'=+5C!2'^ER3$op;R+^<$e1;R+C$IHe1;R@$e2;R+C$IHe2;RBvdP!3+_7+1!2'_4#8S!3'=+5C!2'^ES3$op;R+^<$e1;R+C$IHe1;R@$e2;R+C$IHe2;RBvdP!3+_7+1!2'_4#8T!3'=+5C!2'^ET3$sx;R+1$lo;R+5$n;R+5$e;R+C$IHe;RBvd#1!3+_7+1!2'_4#8U!3'=+5C!2'^EU3$sx;R+1$k;R+5$i;R+3$n;R+5vd5!3+_7+1!2'_4#7V!3'=+5A!2'^EV3#2!3+_7+1!2'_4#3#2!2'^V#4#2").
Qed.
Lemma cs_gc_eq : forall cs, cs_gc cs = cs_gc_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^;0!1'^5#5!1+2+W!1'^3#6!3'_6#2#1!1'_5#6!1'^5#6!3'^Z#2#1!1'^X#6!1'_5#?!3,`D#3#2#1!1'^X#?!1'_5#B!2,`0#4#3!3,`D:#2#1!1'^X#B!1'_5#=!2,`E#2#1!1'^X#=!2,_G+1-CRN$n0;R+C+1#18$n;R+3!1'>!2'^P!2'^Q#4#=!2'^R!2'^S#3#1#<$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k0;R+5$i;R+3$n;R+5,^U!1'_5#@!2,`0#3#2!2,`EB#1!1'^X#@!3,`F#3#2#1!1'>!2'^P!2'^Q#5#?!2'^R!2'^S#4#1#>!3,`F:#2#1!2,_G+1,^U!1'_5#<!2,`G#2#1!1'^X#<!2'^VK#2!2,`I#2#1!1'^X#>!2'^VN#3!1'_5#>!3,`J#3#2#1!2,`K#2#1!2,`KB#1!1'^F#4!2'^VDT!1'_5#A!1'^F#3!2'_4VW!2'_4V#2!1'^X#A!2'^VZ!1'^F#5!2'^P[!2'^VZ#4!2'^P\!2'^VZW!2'^P^0!2'^VZ#2!2'^VD#3!1'^F#2!2'^VD^3!2'^VD#1!4,`L#4#3#2#1!3,`M#3#2#1!3,`M:#2#1!2,`N#2#1!2,`NB#1$cs;R+Avd&p;R!1'^W!2'^>#1}2!2+^I+C+3-^IRN$p;R!2+^I+C+3!3+_7+A-^IRN$x;R!2+^I+C+3+A#11$spb;R+C$spk;R+3!2'^3#5!3'^Y+W!3'_6#2#1!1'_5#50-^IRN$x;R!2+^I+C+3+A#11$spb;R+C$spk;R+3!2'^3#5!3'^Y+W!3'^Z#2#1!1'^X#50#11$e;R+C$z;R+3!2$spb;R+C$spk;R+3!8'`A1+A22!3'^Y+W34!3'^Y+W54!2,_G%~R1+A2!5'`B+W35$K;R+W&H;R!1'`C#7!2'_?!1'^X#7!1'_5#7-WRN$k;R+W!3+_7+1!4'_6#5#4!1'_5#9#1!4'^Z#5#4!1'^X#9#1#2:$a;R+\$w;R+5$v;R+C!3$a;R+\-\RN$s;R+\%w;R+5%v;R+C!3+_7+1!4'_6#;#:67!4'^Z#;#:87#11$a_base;R+C$a_off;R+3!2$b;R+C$kk;R+3$w;R+5$v;R+Cvd!2,_G+1!1'>!2'^P!2'^Q#4#>!2'^R!2'^S#3!1'^T#2#=!3+_7+1!4'_6#>#=9;!4'^Z#>#=<;#2#1#3#2#1$a;R+\$n;R+C!2$a;R+\-\RN$s;R+\%n;R+C!3+_7+1!4'_6#9#8=>!4'^Z#9#8?>#11$a_base;R+C$a_off;R+3!2$b;R+C$kk;R+3$l;R+Cvd@!3+_7+1!4'_6#<#;AC!4'^Z#<#;DC#2#1#2#1$a;R+\$n;R+C$k;R+5!3$a;R+\-\RN$s;R+\%n;R+C%k;R+5!3+_7+1!4'_6#;#:6E!4'^Z#;#:8E#11$a_base;R+C$a_off;R+3!2$b;R+C$kk;R+3$l;R+C$bk;R+5vd!2,_G+1-CRN$n0;R+C+1#28$n;R+3F$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k1;R+5$i;R+3$n;R+5,^U!3+_7+1!4'_6#>#=9G!4'^Z#>#=<G#2#1#3#2#1$lo;R+3$hi;R+3!2$lo;R+3$hi;R+3vdH!3+_7+1!4'_6#8#7IJ!4'^Z#8#7KJ#2#1$e;R+C$m;R+3!2$e;R+C$m;R+3vd!6'_F+1L$b;R+1!3+_7+1#1!2'^V?#3!2,_G+1L!2'_4I#2!4'`HKI#2#5!3+_7+1!4'_6#8#7IM!4'^Z#8#7KM#2#1$e;R+C$lo;R+3$hi;R+3!3$e;R+C$lo;R+3$hi;R+3vd!6'_F+1O$b;R+1!3+_7+1#1!2'^V8#4!2,_G+1O!2'_4P#3!4'`HNP#3#7!3+_7+1!4'_6#:#9PQ!4'^Z#:#9NQ#3#2#1$a;R+\$n;R+C!2$a;R+\-\RN$s;R+\%n;R+C!3+_7+1!4'_6#9#8=R!4'^Z#9#8?R#11$a_base;R+C$a_off;R+3!2$b;R+C$kk;R+3$n;R+CvdH!3+_7+1!4'_6#<#;AS!4'^Z#<#;DS#2#1#2#1$a1;R+\$n1;R+C$a2;R+\$n2;R+C!4$a1;R+\$n1;R+C$a2;R+\$n2;R+Cvd!6'_F+1U$b;R+1!3+_7+1!2'^P!2'^P!2'^P#1!2'_4V#4XY^1!6'_F+1^2$b;R+1!3+_7+1!2'^P!2'^P!2'^P[#1XY^1!6'_F+1^4$b;R+1!3+_7+1!2'^P!2'^P\#1Y^1!6'_F+1^5$b;R+1!3+_7+1!2'^P^0#1^1!2,_G+1!2'^P!2'^P!2'^PU^2^4^5!2'_4A#1!4'`HDA#1#9!2'_4A^3!4'`HDA^3#9!2'_4A#3!4'`HDA#3#9!2'_4AT!4'`HDAT#9!3+_7+1!4'_6#<#;A^6!4'^Z#<#;D^6#4#3#2#1$a;R+\$n;R+C$c;R+3!3$a;R+\-\RN$s;R+\%n;R+C%c;R+3!3+_7+1!4'_6#;#:6^7!4'^Z#;#:8^7#11$a_base;R+C$a_off;R+3!2$b;R+C$kk;R+3$l;R+C$c;R+3vd!2,_G+1-CRN$n0;R+C+1#28$n;R+3F$n;R+5,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^;$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$op;R+^<$a0;R+C$b0;R+C,^U$sx;R+1$lo;R+5$n;R+5$e;R+C,^U$sx;R+1$k0;R+5$i;R+3$n;R+5,^U!3+_7+1!4'_6#>#=9^8!4'^Z#>#=<^8#2#1#3#2#1$a;R+\$n;R+C!2$a;R+\-\RN$s;R+\%n;R+C!3+_7+1!4'_6#9#8=^9!4'^Z#9#8?^9#11$a_base;R+C$a_off;R+3!2$b;R+C$kk;R+3$l;R+Cvd@!3+_7+1!4'_6#<#;A^:!4'^Z#<#;D^:#2#1#2#14#2#1!3+_7+A!1'`O#1!1'`P#1").
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.
Definition saddr_vars_lt (b : nat) (a : saddr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$b;R+5$a;R+\!2'`Q#2!1'^F#1").

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : nat) (s : shape) : bool :=
  match s with
  | SNil | SExit _ | SHole _ | SNext => true
  | SEmitP _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.
Definition kentry_vars_lt (b : nat) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2'`R#5#3!2'^P!2'`R#4#2!2'`Q#4#1!2'^P0!2'`Q#5#2$b;R+5$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C!2'^P0!2'`Q#5#1$a;R+\$n;R+C1$a;R+\$n;R+C$k;R+52$lo;R+3$hi;R+3,^U$e;R+C$m;R+3!2'`Q#4#2$e;R+C$lo;R+3$hi;R+3!2'`Q#5#3$a;R+\$n;R+C1$a1;R+\$n1;R+C$a2;R+\$n2;R+C!2'^P!2'^P!2'^P!2'`R#6#4!2'`Q#6#3!2'`R#6#2!2'`Q#6#1$a;R+\$n;R+C$c;R+32$a;R+\$n;R+C1").
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Fixpoint kn_vars_lt (b : nat) (k : list kentry) : bool :=
  match k with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition pairs_vars_lt (b : nat) (l : list (expr * expr)) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!2+^I+C+C$b;R+5$l;R!1+20!3'=0$p;R0!2'^P!2'`Q#3!3'^J+C+C#1!2'`Q#3!3'^K+C+C#1#1").
Definition maps_vars_lt (b : nat) (ms : list amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$b;R+5$ms;R!1+2+8!3'=+8$m;R+8!2'^P!2'`Q#3!1'^G#1!2'`Q#3!1'^H#1#1").
Definition fd_vars_lt (b : nat) (f : afd) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$b;R+5$f;R+^L-^LRN$f;R+^L+1#13,^U$k;R+5$l;R+C$o;R+C!2'^P!2'`Q#5#2!2'`Q#5#1,^U").
(* [comment removed for export] *)
Definition fresh_ok (cs : acs) : bool :=
  let v := nxt cs in
  sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
  && maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && Nat.leb nx0 v.

(* [comment removed for export] *)
Definition run_block_ref (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let ss' := sym_execTX segs IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carry (s_log ss') (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
(* [comment removed for export] *)
Definition run_block (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in                 (* [comment removed for export] *)
    let ss' := sym_execTXBI segs bc kx IT K fuel true stops (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    match carryK bc (s_log ss') (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Lemma run_block_eq : forall K fuel stops cs, run_block K fuel stops cs = run_block_ref K fuel stops cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "U^B0!1+^7+A!1+2+W!1+2+`U!2+^I12!1+2+1!1'E#3!1'H5!1'`X6!1'`W7!1,Y+Z!1,[+\!6,X!1'I5!1'D596!1'J5:!9'`Z/segs;8!1'`[6/IT;#6#5,^U#4;!1,Y+1!1'E#7!1'H>!6,X!1'I>!1'D>9?!1'J>:!9'`Z/segs;!1'`W!1'`X?!1'`[?/IT;#:#9,^U#8@!1,[+A!7'a0/segs;/IT;#6#5,^U#4;!1'`YC!1'HC!7'a0/segs;/IT;#:#9,^U#8@-^IRN$p;R!2+^I120#21$kn';R1$l0;R2-2RN$l0;R!1+2+`U0#12!2,^8+A!2'^0#7!4'^1!1'IF!1'DF#2!1'JF$s;R+`U$l1;R!1+2+`UB-^IRN$x;R!2+^I340!3'`\DE=1$p;R3$l;R4G!1'E#2!1'HI!6,X!1'II!1'DI9J!1'JI:!7'a0/segs;/IT;#5#4,^U#3K!1'HL!4'`V8DE=!1'`XE!1'`WO!4'`VPDE=!2+^I34!1'E#8!7'a0/segs;/IT;#;#:,^U#9!6,X!1'IS!1'DS9!1'HS!1'JS:!1+2+Z%hints;R4R%kn;R1V%log;RUW%bc;R+a3X!1+_7+a3!1+_71!1+_7R!4'a44R!1+_74\!4'a41V[^0!4'a4UW!1+_7U^1!4'a4+a3XZ^2%fk;R1+a3!4'a41+a3[Z%kn;R11!4'a411[[!1'`YL!3'`\^8M=!1'E#6!1'H^:!6,X!1'I^:!1'D^:9^;!1'J^::!7'a0/segs;/IT;#9#8,^U#7^<-^IRN$x;R!2+^I340^91$p;R3$l;R4-^IRN$p;R!2+^I120#21$kn';R1$l0;R2-2RN$l0;R!1+2+`U0#12!2,^8+A!2'^0#6!4'^1!1'I^=!1'D^=#2!1'J^=$s;R+`U$l1;R!1+2+`UB!1'`W!1'`XJ!9'`Z/segs;^?!1'`[J/IT;#5#4,^U#3K!9'`Z/segs;!1'`W!1'`X^;!1'`[^;/IT;#9#8,^U#7^<$K;R+5$fuel;R+5$stops;R!1+2+3$cs;R+Avd&b;R!1'`T#1+1-1RN$b;R+1!3+_70-1RN$~R+10#12-^IRN$x;R!2+^I340!4'`V8!1'`Y<!1'H<=1$p;R3$l;R4-^IRN$p;R!2+^I120#21$kn';R1$l0;R2-2RN$l0;R!1+2+`U0#12!2,^8+A!2'^0#7!4'^1!1'IA!1'DA#2!1'JA$s;R+`U$l1;R!1+2+`UBB-1RN$~R+10#12HB#12vd!6'_F+KL$s;R+K!3+_70-^IRN$x;R!2+^I340!4'`V8!1'`Y#1!1'H#1=1$p;R3$l;R4-^IRN$p;R!2+^I120#21$kn';R1$l0;R2-2RN$l0;R!1+2+`U0#12!2,^8+A!2'^0#7!4'^1!1'I#5!1'D#5#2!1'J#5$s;R+`U$l1;R!1+2+`UBH!2$lemma;R!3+_71M!1'HK!9'`S0!1+_70!1'a10-^IRN$x;R!2+^I340N1$p;R3$l;R4G-^IRN$x;R!2+^I340Q1$p;R3$l;R4G!6'_9R0$~RR-^IRN$x;R!2+^I340#11$p;R3$l;R4-^IRN$p;R!2+^I120#21$kn';R1$l0;R2-2RN$l0;R!1+2+`U0#12!2,^8+A!2'^0#8!4'^1!1'IT!1'DT#2!1'JT$s;R+`U$l1;R!1+2+`UBNQ!@'a2Y^3!3'a5Y^3!4'a6+a3X^2!4'a6UW^1!4'a61V^0!4'a64R\!1'a7R'`V8P!7'a2^4^5!3'a5^4^5!4'a61+a3Z!1'a7+a3'`W7O!7'a2^6^7!3'a5^6^7!4'a611[!1'a71'`X6E!6'a81[!1'a91E6#1DD!2'a:UDEE!2'a:1E==!2'a:4=HH!2'a:0H!7'a;/segs;/IT;#5#4,^U#3K!6'_FR^9$p;RR!3+_70-^IRN$x;R!2+^I340#11$p;R3$l;R4GH!2,_G0^>!4'`V!1'`W!1'`XM^8M=!3'a<^8M=^@!9'a=/segs;J/IT;#5#4,^U#3K!2,_G1J!3+_70-^IRN$x;R!2+^I340!4'`V^?!1'`Y^@!1'H^@=1$p;R3$l;R4-^IRN$p;R!2+^I120#21$kn';R1$l0;R2-2RN$l0;R!1+2+`U0#12!2,^8+A!2'^0#6!4'^1!1'I^A!1'D^A#2!1'J^A$s;R+`U$l1;R!1+2+`UB^>!2,_G0B!3+_70!4'a>#4#3#2#1!4'a?#4#3#2#1").
Qed.

Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$K;R+5$fuel;R+5$stops;R!1+2+3$cs;R+A-^7RN$x;R!1+^7+A!1+^7+A!4'a>#4#3#2#12$cs';R+A!2,^8+A!1'`O#1!1,[+A").

Definition kentry_eqb (x y : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S50!2'a@#6#3!2'^P!2'a@#4#2!2'^Q#3#1!2'^P0!2'^Q#5#2!2'aA#3#1!2'aA#4#1$x;R+W$y;R+W-WRN$x;R+W+1#2:$a;R+\$w;R+5$v;R+C-WRN$y;R+W+1#4:$a';R+\$w';R+5$v';R+C!2'^P!2'^P0!2'7#5#2!2'^Q#4#1$a0;R+\$n;R+C,6$a0;R+\$n;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n;R+C$c;R+3,6$a0;R+\$n;R+C,6$a;R+\$n;R+C-WRN$y;R+W+1#3:$a0;R+\$w;R+5$v;R+C,6$a';R+\$n';R+C1$a0;R+\$n0;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n0;R+C$c;R+3,6$a0;R+\$n0;R+C,6$a;R+\$n;R+C$k;R+5-WRN$y;R+W+1#4:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n0;R+C,6$a';R+\$n';R+C$k';R+5!2'^P2!2'7#4#1$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n0;R+C$c;R+3,6$a0;R+\$n0;R+C,6$lo;R+3$hi;R+3-WRN$y;R+W+1#3:$a;R+\$w;R+5$v;R+C,6$a;R+\$n;R+C,6$a;R+\$n;R+C$k;R+5,6$lo';R+3$hi';R+3!2'^P!2'aA#4#23$e;R+C$m;R+3,6$e;R+C$lo0;R+3$hi0;R+3,6$a;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a;R+\$n;R+C$c;R+3,6$a;R+\$n;R+C,6$e;R+C$m;R+3-WRN$y;R+W+1#3:$a;R+\$w;R+5$v;R+C,6$a;R+\$n;R+C,6$a;R+\$n;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e';R+C$m';R+3!2'^P!2'^Q#4#23$e0;R+C$lo;R+3$hi;R+3,6$a;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a;R+\$n;R+C$c;R+3,6$a;R+\$n;R+C,6$e;R+C$lo;R+3$hi;R+3-WRN$y;R+W+1#4:$a;R+\$w;R+5$v;R+C,6$a;R+\$n;R+C,6$a;R+\$n;R+C$k;R+5,6$lo0;R+3$hi0;R+3,6$e0;R+C$m;R+3,6$e';R+C$lo';R+3$hi';R+3!2'^P!2'^P!2'^Q#6#3!2'aA#5#24$a;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a;R+\$n;R+C$c;R+3,6$a;R+\$n;R+C,6$a;R+\$n;R+C-WRN$y;R+W+1#3:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n0;R+C,6$a0;R+\$n0;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a';R+\$n';R+C1$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n0;R+C$c;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C-WRN$y;R+W+1#5:$a;R+\$w;R+5$v;R+C,6$a;R+\$n;R+C,6$a;R+\$n;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a;R+\$n;R+C,6$a1';R+\$n1';R+C$a2';R+\$n2';R+C!2'^P!2'^P!2'^P!2'a@#8#4!2'^Q#7#3!2'a@#6#2!2'^Q#5#1$a;R+\$n;R+C$c;R+3,6$a;R+\$n;R+C,6$a;R+\$n;R+C$c;R+3-WRN$y;R+W+1#4:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n0;R+C,6$a0;R+\$n0;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a';R+\$n';R+C$c';R+3!2'^P24$a0;R+\$n0;R+C,6$a;R+\$n;R+C-WRN$y;R+W+1#3:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n0;R+C,6$a0;R+\$n0;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n0;R+C$c;R+3,6$a';R+\$n';R+C1").

Definition amap_eqb (x y : amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$x;R+8$y;R+8!2'^P!2'^P!2'^Q!1'^G#2!1'^G#1!2'^Q!1'^H#2!1'^H#1!2'9!1':#2!1':#1").

Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (x y : list T) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => eqb a b && list_eqb eqb x' y'
  | _, _ => false
  end.

Definition pair_eqb (x y : expr * expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!2+^I+C+C$x;R0$y;R0!2'^P!2'^Q!3'^J+C+C#2!3'^J+C+C#1!2'^Q!3'^K+C+C#2!3'^K+C+C#1").

Definition afd_eqb (x y : afd) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$x;R+^L$y;R+^L-^LRN$x;R+^L+1#23-^LRN$y;R+^L+1#13,^U$k;R+5$len;R+C$off;R+C,6,6$k;R+5$l;R+C$o;R+C-^LRN$y;R+^L+1#43,6$k';R+5$l';R+C$o';R+C!2'^P!2'^P!2'7#6#3!2'^Q#5#2!2'^Q#4#1,6-^LRN$y;R+^L+1#13,6$k;R+5$len;R+C$off;R+C,6,^U").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b (allkn : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_x allkn ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_x allkn ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_x allkn ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_x allkn ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_x allkn ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_x allkn ub uk un b k l
  end.

Definition kentry_apart_bB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S30-\RN$a;R+\+1#21$b;R+C$k;R+3!7'aB#9#8#7#6#2#1#3-\RN$a;R+\+1#31$b;R+C$k;R+3!7'aB#:#9#8#7#2#1#4!2'aD#1#2$bc;R+a3$ub;R+C$uk;R+3$un;R+C$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!2'^P!2'`?#4}8!7'aB#:#9#8#7#2#1!1,F!1'^T#4$a;R+\$l;R+C0$a;R+\$l;R+C$k0;R+51$lo;R+3$hi;R+3!2'^P!2'^P!2'^P!2'^R,G#2!2'^R#2#1!2'aC2'^:!7'aB#7#6#5#4!1,F,G#2!1,F2$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C0$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+31$a;R+\$l;R+C0").

Lemma kentry_apart_bB_eqf : forall fk, kentry_apart_bB (mkbc fk) = kentry_apart_b fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S@0%K;R+W+1%un;R+C0%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1!2'`?#4}8!1,F!1'^T#4-\RN$a;R+\+1#21$b;R+C$k;R+3!6#5#9#8#7#2#1#3-\RN$a;R+\+1#31$b;R+C$k;R+3!6#6#:#9#8#2#1#4!2'aD#1#2!2'^P!2'^P!2'^R,G#2!2'^R#2#1!2'aC7'^:!1,F,G!1,F7-\RN$a;R+\+1#21$b;R+C$k;R+3!7'aH#:#9#8#7#2#1#3-\RN$a;R+\+1#31$b;R+C$k;R+3!7'aH#;#:#9#8#2#1#4-\RN$a;R+\+1#21$b;R+C$k;R+3!7'aH#9#8#7#6#2#1#3-\RN$a;R+\+1#31$b;R+C$k;R+3!7'aH#:#9#8#7#2#1#4!1'`W#5$fk;R!1+2+W!5'aE+C%uk;R+31!1'aF!1'`W#1!1'aG#1$x;R+C!5'aE+31!2'aF!1'`W#2#1!2'aG#2#1$x0;R+3!5'aE+C0!3'aF!1'`W#3#2#1!3'aG#3#2#1$x1;R+C!5'aE+W+1!4'aF!1'`W#4#3#2#1!4'aG#4#3#2#1$x2;R+Wvd!6'_F2!1'aH#5$b;R2!3+_7+1-WRN$K;R+W+1#2:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!2'^P3!6#6#:#9#8#2#14$a;R+\$l;R+C5$a;R+\$l;R+C$k0;R+56$lo;R+3$hi;R+3!2'^P8!6#3#7#6#59#2:$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C5$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+36$a;R+\$l;R+C5-WRN$K;R+W+1#2:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!2'^P3!7'aH#;#:#9#8#2#14$a;R+\$l;R+C;$a;R+\$l;R+C$k0;R+5<$lo;R+3$hi;R+3!2'^P8!7'aH#8#7#6#59#2:$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C;$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+3<$a;R+\$l;R+C;!2,_G+1-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!2'^P3!7'aH#:#9#8#7#2#14$a;R+\$l;R+C=$a;R+\$l;R+C$k0;R+5>$lo;R+3$hi;R+3!2'^P8!7'aH#7#6#5#49#2:$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+3>$a;R+\$l;R+C=!1'aB?!1'aI#5!3+_7+1!5'aF?#4#3#2#1!5'aG#5#4#3#2#1").
Qed.
#[local] Hint Rewrite kentry_apart_bB_eqf : bceq.


(* [comment removed for export] *)
Definition kentry_apart_bp (allkn : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => Nat.leb w 8 && ranges_apart_p allkn sp ub uk un b k (ELit (Z.of_nat w))
  | KZero (SA b k) l => ranges_apart_p allkn sp ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_p allkn sp ub uk un b k l
  | KImg lo hi => Z.leb 0 lo && Z.leb lo hi && Z.ltb (hi - lo) two64 && ranges_apart_p allkn sp ub uk un (ELit 0) lo (ELit (hi - lo))
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr (SA b k) n => ranges_apart_p allkn sp ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_p allkn sp ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_p allkn sp ub uk un b k l
  end.

Definition kentry_apart_bpB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S30-\RN$a;R+\+1#21$b;R+C$k;R+3!8'aK#:#9#8#7#6#2#1#3-\RN$a;R+\+1#31$b;R+C$k;R+3!8'aK#;#:#9#8#7#2#1#4!2'aD#1#2$bc;R+a3$sp;R+aJ$ub;R+C$uk;R+3$un;R+C$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!2'^P!2'`?#4}8!8'aK#;#:#9#8#7#2#1!1,F!1'^T#4$a;R+\$l;R+C0$a;R+\$l;R+C$k0;R+51$lo;R+3$hi;R+3!2'^P!2'^P!2'^P!2'^R,G#2!2'^R#2#1!2'aC2'^:!8'aK#8#7#6#5#4!1,F,G#2!1,F2$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C0$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+31$a;R+\$l;R+C0").

Lemma kentry_apart_bpB_eqf : forall fk, kentry_apart_bpB (mkbc fk) = kentry_apart_bp fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SA0%K;R+W+1%un;R+C0%uk;R+31%sp;R+aJ%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1!2'`?#4}8!1,F!1'^T#4-\RN$a;R+\+1#21$b;R+C$k;R+3!7#5#:#9#8#7#2#1#3-\RN$a;R+\+1#31$b;R+C$k;R+3!7#6#;#:#9#8#2#1#4!2'aD#1#2!2'^P!2'^P!2'^R,G#2!2'^R#2#1!2'aC8'^:!1,F,G!1,F8-\RN$a;R+\+1#21$b;R+C$k;R+3!8'aN#;#:#9#8#7#2#1#3-\RN$a;R+\+1#31$b;R+C$k;R+3!8'aN#<#;#:#9#8#2#1#4-\RN$a;R+\+1#21$b;R+C$k;R+3!8'aN#:#9#8#7#6#2#1#3-\RN$a;R+\+1#31$b;R+C$k;R+3!8'aN#;#:#9#8#7#2#1#4!1'`W#6$fk;R!1+2+W!5'aE+aJ%ub;R+C2!1'aL!1'`W#1!1'aM#1$x;R+aJ!5'aE+C2!2'aL!1'`W#2#1!2'aM#2#1$x0;R+C!5'aE+31!3'aL!1'`W#3#2#1!3'aM#3#2#1$x1;R+3!5'aE+C0!4'aL!1'`W#4#3#2#1!4'aM#4#3#2#1$x2;R+C!5'aE+W+1!5'aL!1'`W#5#4#3#2#1!5'aM#5#4#3#2#1$x3;R+Wvd!6'_F3!1'aN#6$b;R3!3+_7+1-WRN$K;R+W+1#2:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!2'^P4!7#6#;#:#9#8#2#15$a;R+\$l;R+C6$a;R+\$l;R+C$k0;R+57$lo;R+3$hi;R+3!2'^P9!7#3#8#7#6#5:#2;$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+37$a;R+\$l;R+C6-WRN$K;R+W+1#2:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!2'^P4!8'aN#<#;#:#9#8#2#15$a;R+\$l;R+C<$a;R+\$l;R+C$k0;R+5=$lo;R+3$hi;R+3!2'^P9!8'aN#9#8#7#6#5:#2;$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C<$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+3=$a;R+\$l;R+C<!2,_G+1-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$k;R+3!2'^P4!8'aN#;#:#9#8#7#2#15$a;R+\$l;R+C>$a;R+\$l;R+C$k0;R+5?$lo;R+3$hi;R+3!2'^P9!8'aN#8#7#6#5#4:#2;$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+3?$a;R+\$l;R+C>!1'aK@!1'aO#6!3+_7+1!6'aL@#5#4#3#2#1!6'aM#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.



Definition kimg_b (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C,6$a;R+\$n;R+C,6$a;R+\$n;R+C$k;R+5,6$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a;R+\$n;R+C$c;R+3,6$a;R+\$n;R+C,6").

(* [comment removed for export] *)
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$bc;R+a3$ub;R+C$uk;R+3$un;R+C&sp;R!4'aP#4#3#2#1+aJ!3'^Y+W$K;R+W!2'^M!1'aQ#1!6'aL#6#2#5#4#3#1!1'aR#5").

Lemma kn_unfillB_eqf : forall fk, kn_unfillB (mkbc fk) = kn_unfill fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+2+W%un;R+C0%sp;R+aJ%ub;R+C%uk;R+3%un;R+C%K;R+W+1!1'aQ#1!1'aR!1'`W#5$K;R+W!2'^M3!6'aM#6!4'aU#6#5#4#3#5#4#3#1!3'^Y+W5#5%b1;R+C%k1;R+3%n1;R+C+aJ!1'`W#4$fk;R0!5'aE+C%uk;R+31!1'aS!1'`W#1!1'aT#1$x;R+C!5'aE+31!2'aS!1'`W#2#1!2'aT#2#1$x0;R+3!5'aE+C0!3'aS!1'`W#3#2#1!3'aT#3#2#1$x1;R+Cvd!6'_F2!1'aM#4$b;R2!3+_70!3'^Y+W$K;R+W!2'^M3!5#2!4'aP!1'`W#6#5#4#3#5#4#3#146!6'_F7!1'aU#4$s;R7!3+_70!3'^Y+W$K;R+W!2'^M3!6'aM#6!3#2#5#4#3#5#4#3#146!6'_F0#4$l;R0!3+_70!3'^Y+W5#16!2,_G0!3'^Y+W$K;R+W!2'^M3!6'aM#5!4'aU#5#4#3#2#4#3#2#1#4!1'aR8!1'aV#4!1'aP8!1'aW#4!1'aL8!1'aX#4!3+_70!4'aS8#3#2#1!4'aT#4#3#2#1").
Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
Lemma kn_unfillM_eq : kn_unfillM = kn_unfill. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+2+W%ub;R+C%uk;R+3%un;R+C0!5'aE01'aY'aT$k;R0vd!1'aZ#1!3+_71!1'aY#1!1'aT#1").
Qed.



(* [comment removed for export] *)
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition havoc1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1+2+W!1,Y+W$k;R0$ub;R+C$uk;R+3$un;R+C$K;R+W-1RN$~R+10!2'^M!1'a[#1!5'aG#5#4#3#2#12!3,_C+W#11-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C1$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#9#8#7#6#2#1#3$a;R+\$n;R+C$k0;R+51$lo;R+3$hi;R+31$e;R+C$m;R+31$e;R+C$lo;R+3$hi;R+31$a;R+\$n;R+C1$a1;R+\$n1;R+C$a2;R+\$n2;R+C1$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#:#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#9#8#7#6#2#1#3").

Definition havoc1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1+2+W!1,Y+W$bc;R+a3$ub;R+C$uk;R+3$un;R+C$K;R+W-1RN$~R+10!2'^M!1'a[#1!5'aF#5#4#3#2#12!3,_C+W#11-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C1$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b2#9#8#7#6#2#1#3$a;R+\$n;R+C$k;R+51$lo;R+3$hi;R+31$e;R+C$m;R+31$e;R+C$lo;R+3$hi;R+31$a;R+\$n;R+C1$a1;R+\$n1;R+C$a2;R+\$n2;R+C1$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b3#:#3#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b4#9#8#7#6#2#1#3").

Lemma havoc1B_eqf : forall fk, havoc1B (mkbc fk) = havoc1 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SB0!1+2+W%K;R+W0%un;R+C1%ub;R+C%uk;R+3%un;R+C%K;R+W+1!1'a[#2!1,Y+W!3,_C+W#25!1'`W#:-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b27#9#8#7#2#1#3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b3!1'`W#;#3#:#9#8#2#1#4!2'^M4!5'aG#6#5#4#3#2-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#;#:#9#8#2#1#4-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#:#9#8#7#2#1#3-1RN$~R+10:26-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#:#9#8#7#2#1#3$a;R+\$n;R+C$k0;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$n;R+C5$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3;$a;R+\$len;R+C<%wb;R+C%wk;R+3%wn;R+C%kb;R+C%kk;R+3%len;R+C0-\RN$a;R+\0#21$kb;R+C$kk;R+3!6#5#9#8#7#2#1#3%c;R+3>!1'`W#5$fk;R0!5'aE+C%uk;R+32!1'b5!1'`W#1!1'b6#1$x;R+C!5'aE+32!2'b5!1'`W#2#1!2'b6#2#1$x0;R+3!5'aE+C1!3'b5!1'`W#3#2#1!3'b6#3#2#1$x1;R+C!5'aE+W0!4'b5!1'`W#4#3#2#1!4'b6#4#3#2#1$x2;R+Wvd!6'_F3!1'aG#5$b;R3!3+_70-1RN$~R+10!2'^M4!4#1#5#4#3#226-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C8$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$n;R+C5$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+39$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b47#9#8#7#2#1#3=!6'_F>!1'b1#5$l;R>!3+_70-1RN$~R+10:26-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C8$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$n;R+C5$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+39$a;R+\$len;R+C?=!6'_F@$c;R+3!2'b0#1#6$l;R@!3+_70-1RN$~R+10:26-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C8$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$n;R+C5$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!7#6#3#:#9#8#2#1#4$a;R+\$len;R+C<=!6'_F>!1'a\#5$l;R>!3+_70-1RN$~R+10:26-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C?$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$n;R+C5$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3;$a;R+\$len;R+C<=!2,_G0-1RN$~R+10!2'^M!1'a[#1!5'aG#5#4#3#2#12!3,_C+W#15-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#9#8#7#6#2#1#3$a;R+\$n;R+C$k0;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$n;R+C5$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#:#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#9#8#7#6#2#1#3!1'b2A!1'b7#5!1'b3A!1'b8#5!1'b4A!1'b9#5!1'aFA!1'b:#5!3+_70!5'b5A#4#3#2#1!5'b6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite havoc1B_eqf : bceq.


Definition havoc1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+2+W!1,Y+W$k;R0$sp;R+aJ$ub;R+C$uk;R+3$un;R+C$K;R+W-1RN$~R+10!2'^M!1'a[#1!6'aM#6#5#4#3#2#12!3,_C+W#11-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C1$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#:#8#7#6#2#1#3$a;R+\$n;R+C$k0;R+51$lo;R+3$hi;R+31$e;R+C$m;R+31$e;R+C$lo;R+3$hi;R+31$a;R+\$n;R+C1$a1;R+\$n1;R+C$a2;R+\$n2;R+C1$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#;#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#:#8#7#6#2#1#3").

Definition havoc1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+2+W!1,Y+W$bc;R+a3$sp;R+aJ$ub;R+C$uk;R+3$un;R+C$K;R+W-1RN$~R+10!2'^M!1'a[#1!6'aL#6#5#4#3#2#12!3,_C+W#11-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C1$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b2#:#8#7#6#2#1#3$a;R+\$n;R+C$k;R+51$lo;R+3$hi;R+31$e;R+C$m;R+31$e;R+C$lo;R+3$hi;R+31$a;R+\$n;R+C1$a1;R+\$n1;R+C$a2;R+\$n2;R+C1$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b3#;#3#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b4#:#8#7#6#2#1#3").

Lemma havoc1pB_eqf : forall fk, havoc1pB (mkbc fk) = havoc1p fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SC0!1+2+W%K;R+W0%un;R+C1%uk;R+32%sp;R+aJ%ub;R+C%uk;R+3%un;R+C%K;R+W+1!1'a[#2!1,Y+W!3,_C+W#26!1'`W#;-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b28#9#8#7#2#1#3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b3!1'`W#<#3#:#9#8#2#1#4!2'^M5!6'aM#7#6#5#4#3#2-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#<#:#9#8#2#1#4-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#;#9#8#7#2#1#3-1RN$~R+10;27-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#;#9#8#7#2#1#3$a;R+\$n;R+C$k0;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$n;R+C6$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3<$a;R+\$len;R+C=%wb;R+C%wk;R+3%wn;R+C%kb;R+C%kk;R+3%len;R+C0-\RN$a;R+\0#21$kb;R+C$kk;R+3!6#5#9#8#7#2#1#3%c;R+3?!1'`W#6$fk;R0!5'aE+aJ%ub;R+C3!1'b;!1'`W#1!1'b<#1$x;R+aJ!5'aE+C3!2'b;!1'`W#2#1!2'b<#2#1$x0;R+C!5'aE+32!3'b;!1'`W#3#2#1!3'b<#3#2#1$x1;R+3!5'aE+C1!4'b;!1'`W#4#3#2#1!4'b<#4#3#2#1$x2;R+C!5'aE+W0!5'b;!1'`W#5#4#3#2#1!5'b<#5#4#3#2#1$x3;R+Wvd!6'_F4!1'aM#6$b;R4!3+_70-1RN$~R+10!2'^M5!5#1#6#5#4#3#227-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C9$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$n;R+C6$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3:$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b48#9#8#7#2#1#3>!6'_F?!1'b1#6$l;R?!3+_70-1RN$~R+10;27-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C9$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$n;R+C6$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3:$a;R+\$len;R+C@>!6'_FA$c;R+3!2'b0#1#7$l;RA!3+_70-1RN$~R+10;27-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C9$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$n;R+C6$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!7#6#3#:#9#8#2#1#4$a;R+\$len;R+C=>!6'_F?!1'a\#6$l;R?!3+_70-1RN$~R+10;27-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C@$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$n;R+C6$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3<$a;R+\$len;R+C=>!2,_G0-1RN$~R+10!2'^M!1'a[#1!6'aM#6#5#4#3#2#12!3,_C+W#16-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#:#8#7#6#2#1#3$a;R+\$n;R+C$k0;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$n;R+C6$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#;#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#:#8#7#6#2#1#3!1'b2B!1'b7#6!1'b3B!1'b8#6!1'b4B!1'b9#6!1'aLB!1'aX#6!3+_70!6'b;B#5#4#3#2#1!6'b<#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$k;R!1+2+W$ub;R+C$uk;R+3$un;R+C&sp;R!4'aU#4#3#2#1+aJ!4'b=+W+W!5'b<#5#1#4#3#2#5").

Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$bc;R+a3$ub;R+C$uk;R+3$un;R+C&sp;R!4'aP#4#3#2#1+aJ!4'b=+W+W!5'b;#5#1#4#3#2!1'aR#5").

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+2+W%un;R+C0%sp;R+aJ%ub;R+C%uk;R+3%un;R+C%K;R+W0!1'`W#5!1'aR3!5'b<#5!4'aU#5#4#3#2#4#3#2!4'b=+W+W5#5%b1;R+C%k1;R+3%n1;R+C+aJ!1'`W#4$fk;R0!5'aE+C%uk;R+31!1'b>!1'`W#1!1'b?#1$x;R+C!5'aE+31!2'b>!1'`W#2#1!2'b?#2#1$x0;R+3!5'aE+C0!3'b>!1'`W#3#2#1!3'b?#3#2#1$x1;R+Cvd!6'_F2!1'b<#4$l;R2!3+_70!4'b=+W+W!4#1!4'aP3#4#3#2#4#3#246!6'_F7!1'aU#4$s;R7!3+_70!4'b=+W+W!5'b<#5!3#1#4#3#2#4#3#246!6'_F0#4$l;R0!3+_70!4'b=+W+W5#16!2,_G0!4'b=+W+W!5'b<#4!4'aU#4#3#2#1#3#2#1#4!1'aR8!1'aV#4!1'aP8!1'aW#4!1'b;8!1'b@#4!3+_70!4'b>8#3#2#1!4'b?#4#3#2#1").
Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+2+W%ub;R+C%uk;R+3%un;R+C0!5'aE01'bA'b?$k;R0vd!1'bB#1!3+_71!1'bA#1!1'b?#1").
Qed.



(* [comment removed for export] *)
Definition kwr_cut (k : list kentry) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcut KWr k ub uk un kb kk len.

Definition kwr_cutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S00$bc;R+a3$ub;R+C$uk;R+3$un;R+C$kb;R+C$kk;R+3$len;R+C!8'bC#7,`K#6#5#4#3#2#1").

Lemma kwr_cutB_eqf : forall fk, kwr_cutB (mkbc fk) = kwr_cut fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80!1+2+W%len;R+C0%kk;R+31%kb;R+C2%un;R+C3%~R+\%~R+C+W%mk;R5%wb;R+C%wk;R+3%wn;R+C3!1'`W#7$fk;R0!5'aE+C%uk;R+34!1'bD!1'`W#1!1'bE#1$x;R+C!5'aE+34!2'bD!1'`W#2#1!2'bE#2#1$x0;R+3!5'aE+C3!3'bD!1'`W#3#2#1!3'bE#3#2#1$x1;R+C!5'aE+C2!4'bD!1'`W#4#3#2#1!4'bE#4#3#2#1$x2;R+C!5'aE+31!5'bD!1'`W#5#4#3#2#1!5'bE#5#4#3#2#1$x3;R+3!5'aE+C0!6'bD!1'`W#6#5#4#3#2#1!6'bE#6#5#4#3#2#1$x4;R+Cvd!6'_F6$mk;R5!2'bF#1#8$l;R6!3+_70!7#1,`K#7#6#5#4#3#2!8'bF,`K#8#7#6#5#4#3#2!2,_G0!8'bF,`K#7#6#5#4#3#2#1!1'bC7!1'bG#7!3+_70!7'bD7#6#5#4#3#2#1!7'bE#7#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite kwr_cutB_eqf : bceq.


Definition cutout1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1+2+W!1,Y+W$k;R0$ub;R+C$uk;R+3$un;R+C$K;R+W-1RN$~R+10!5'aG#5#4#3#2#12!3,_C+W#11-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C1$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#9#8#7#6#2#1#3$a;R+\$n;R+C$k0;R+51$lo;R+3$hi;R+31$e;R+C$m;R+31$e;R+C$lo;R+3$hi;R+31$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'bE#9#8#7#6#2#1#3$a1;R+\$n1;R+C$a2;R+\$n2;R+C1$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#:#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#9#8#7#6#2#1#3").

Definition cutout1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1+2+W!1,Y+W$bc;R+a3$ub;R+C$uk;R+3$un;R+C$K;R+W-1RN$~R+10!5'aF#5#4#3#2#12!3,_C+W#11-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C1$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b2#9#8#7#6#2#1#3$a;R+\$n;R+C$k;R+51$lo;R+3$hi;R+31$e;R+C$m;R+31$e;R+C$lo;R+3$hi;R+31$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'bD#9#8#7#6#2#1#3$a1;R+\$n1;R+C$a2;R+\$n2;R+C1$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b3#:#3#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b4#9#8#7#6#2#1#3").

Lemma cutout1B_eqf : forall fk, cutout1B (mkbc fk) = cutout1 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SE0!1+2+W%K;R+W0%un;R+C1%kb;R+C%kk;R+3%len;R+C0%ub;R+C%uk;R+3%un;R+C3!1,Y+W!3,_C+W#25!1'`W#:-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b27#9#8#7#2#1#3-\RN$a;R+\0#21$kb;R+C$kk;R+3!6#5#9#8#7#2#1#3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b3!1'`W#;#3#:#9#8#2#1#4-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b47#9#8#7#2#1#3!5'aG#6#5#4#3#2-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'bE#:#9#8#7#2#1#3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#;#:#9#8#2#1#4-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#:#9#8#7#2#1#3-1RN$~R+10<26-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#:#9#8#7#2#1#3$a;R+\$n;R+C$k0;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$len;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3>$a;R+\$len;R+C?%ub;R+C%uk;R+3%un;R+C%K;R+W+1%wb;R+C%wk;R+3%wn;R+C3%c;R+3B!1'`W#5$fk;R0!5'aE+C%uk;R+32!1'bH!1'`W#1!1'bI#1$x;R+C!5'aE+32!2'bH!1'`W#2#1!2'bI#2#1$x0;R+3!5'aE+C1!3'bH!1'`W#3#2#1!3'bI#3#2#1$x1;R+C!5'aE+W0!4'bH!1'`W#4#3#2#1!4'bI#4#3#2#1$x2;R+Wvd!6'_F4!1'bE#5$l;R4!3+_70-1RN$~R+10!5'aF!1'`W#6#5#4#3#226-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C8$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$len;R+C9$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3:$a;R+\$len;R+C;@!6'_FA!1'aG#5$b;RA!3+_70-1RN$~R+10!4#1#5#4#3#226-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C8$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$len;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3:$a;R+\$len;R+C;@!6'_FB!1'b1#5$l;RB!3+_70-1RN$~R+10<26-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C8$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$len;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3:$a;R+\$len;R+C9@!6'_FC$c;R+3!2'b0#1#6$l;RC!3+_70-1RN$~R+10<26-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C8$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$len;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!7#6#3#:#9#8#2#1#4$a;R+\$len;R+C?@!6'_FB!1'a\#5$l;RB!3+_70-1RN$~R+10<26-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C9$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$len;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3>$a;R+\$len;R+C?@!2,_G0-1RN$~R+10!5'aG#5#4#3#2#12!3,_C+W#15-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C5$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#9#8#7#6#2#1#3$a;R+\$n;R+C$k0;R+55$lo;R+3$hi;R+35$e;R+C$m;R+35$e;R+C$lo;R+3$hi;R+35$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'bE#9#8#7#6#2#1#3$a1;R+\$n1;R+C$a2;R+\$n2;R+C5$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#:#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#9#8#7#6#2#1#3!1'b2D!1'b7#5!1'b3D!1'b8#5!1'b4D!1'b9#5!1'aFD!1'b:#5!1'bDD!1'bJ#5!3+_70!5'bHD#4#3#2#1!5'bI#5#4#3#2#1").
Qed.
#[local] Hint Rewrite cutout1B_eqf : bceq.


Definition cutout1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+2+W!1,Y+W$k;R0$sp;R+aJ$ub;R+C$uk;R+3$un;R+C$K;R+W-1RN$~R+10!6'aM#6#5#4#3#2#12!3,_C+W#11-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C1$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#:#8#7#6#2#1#3$a;R+\$n;R+C$k0;R+51$lo;R+3$hi;R+31$e;R+C$m;R+31$e;R+C$lo;R+3$hi;R+31$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'bE#:#8#7#6#2#1#3$a1;R+\$n1;R+C$a2;R+\$n2;R+C1$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#;#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#:#8#7#6#2#1#3").

Definition cutout1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+2+W!1,Y+W$bc;R+a3$sp;R+aJ$ub;R+C$uk;R+3$un;R+C$K;R+W-1RN$~R+10!6'aL#6#5#4#3#2#12!3,_C+W#11-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C1$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b2#:#8#7#6#2#1#3$a;R+\$n;R+C$k;R+51$lo;R+3$hi;R+31$e;R+C$m;R+31$e;R+C$lo;R+3$hi;R+31$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'bD#:#8#7#6#2#1#3$a1;R+\$n1;R+C$a2;R+\$n2;R+C1$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b3#;#3#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b4#:#8#7#6#2#1#3").

Lemma cutout1pB_eqf : forall fk, cutout1pB (mkbc fk) = cutout1p fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SF0!1+2+W%K;R+W0%un;R+C1%uk;R+32%kb;R+C%kk;R+3%len;R+C0%ub;R+C%uk;R+3%un;R+C4!1,Y+W!3,_C+W#26!1'`W#;-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b28#9#8#7#2#1#3-\RN$a;R+\0#21$kb;R+C$kk;R+3!6#5#9#8#7#2#1#3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b3!1'`W#<#3#:#9#8#2#1#4-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b48#9#8#7#2#1#3!6'aM#7#6#5#4#3#2-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'bE#;#9#8#7#2#1#3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#<#:#9#8#2#1#4-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#;#9#8#7#2#1#3-1RN$~R+10=27-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#;#9#8#7#2#1#3$a;R+\$n;R+C$k0;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$len;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3?$a;R+\$len;R+C@%sp;R+aJ%ub;R+C%uk;R+3%un;R+C%K;R+W+1%wb;R+C%wk;R+3%wn;R+C4%c;R+3C!1'`W#6$fk;R0!5'aE+aJ%ub;R+C3!1'bK!1'`W#1!1'bL#1$x;R+aJ!5'aE+C3!2'bK!1'`W#2#1!2'bL#2#1$x0;R+C!5'aE+32!3'bK!1'`W#3#2#1!3'bL#3#2#1$x1;R+3!5'aE+C1!4'bK!1'`W#4#3#2#1!4'bL#4#3#2#1$x2;R+C!5'aE+W0!5'bK!1'`W#5#4#3#2#1!5'bL#5#4#3#2#1$x3;R+Wvd!6'_F5!1'bE#6$l;R5!3+_70-1RN$~R+10!6'aL!1'`W#7#6#5#4#3#227-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C9$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$len;R+C:$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3;$a;R+\$len;R+C<A!6'_FB!1'aM#6$b;RB!3+_70-1RN$~R+10!5#1#6#5#4#3#227-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C9$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$len;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3;$a;R+\$len;R+C<A!6'_FC!1'b1#6$l;RC!3+_70-1RN$~R+10=27-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C9$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$len;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3;$a;R+\$len;R+C:A!6'_FD$c;R+3!2'b0#1#7$l;RD!3+_70-1RN$~R+10=27-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C9$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$len;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!7#6#3#:#9#8#2#1#4$a;R+\$len;R+C@A!6'_FC!1'a\#6$l;RC!3+_70-1RN$~R+10=27-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C:$a;R+\$n;R+C$k;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$len;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3?$a;R+\$len;R+C@A!2,_G0-1RN$~R+10!6'aM#6#5#4#3#2#12!3,_C+W#16-WRN$K;R+W0#1:$a;R+\$w;R+5$v;R+C6$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'a\#:#8#7#6#2#1#3$a;R+\$n;R+C$k0;R+56$lo;R+3$hi;R+36$e;R+C$m;R+36$e;R+C$lo;R+3$hi;R+36$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'bE#:#8#7#6#2#1#3$a1;R+\$n1;R+C$a2;R+\$n2;R+C6$a;R+\$len;R+C$c;R+3-\RN$a;R+\0#31$kb;R+C$kk;R+3!8'b0#3#;#9#8#7#2#1#4$a;R+\$len;R+C-\RN$a;R+\0#21$kb;R+C$kk;R+3!7'b1#:#8#7#6#2#1#3!1'b2E!1'b7#6!1'b3E!1'b8#6!1'b4E!1'b9#6!1'aLE!1'aX#6!1'bDE!1'bJ#6!3+_70!6'bKE#5#4#3#2#1!6'bL#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$k;R!1+2+W$ub;R+C$uk;R+3$un;R+C&sp;R!4'aU#4#3#2#1+aJ!4'b=+W+W!5'bL#5#1#4#3#2#5").

Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$bc;R+a3$ub;R+C$uk;R+3$un;R+C&sp;R!4'aP#4#3#2#1+aJ!4'b=+W+W!5'bK#5#1#4#3#2!1'aR#5").

Lemma kn_cutoutB_eqf : forall fk, kn_cutoutB (mkbc fk) = kn_cutout fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+2+W%un;R+C0%sp;R+aJ%ub;R+C%uk;R+3%un;R+C%K;R+W0!1'`W#5!1'aR3!5'bL#5!4'aU#5#4#3#2#4#3#2!4'b=+W+W5#5%b1;R+C%k1;R+3%n1;R+C+aJ!1'`W#4$fk;R0!5'aE+C%uk;R+31!1'bM!1'`W#1!1'bN#1$x;R+C!5'aE+31!2'bM!1'`W#2#1!2'bN#2#1$x0;R+3!5'aE+C0!3'bM!1'`W#3#2#1!3'bN#3#2#1$x1;R+Cvd!6'_F2!1'bL#4$l;R2!3+_70!4'b=+W+W!4#1!4'aP3#4#3#2#4#3#246!6'_F7!1'aU#4$s;R7!3+_70!4'b=+W+W!5'bL#5!3#1#4#3#2#4#3#246!6'_F0#4$l;R0!3+_70!4'b=+W+W5#16!2,_G0!4'b=+W+W!5'bL#4!4'aU#4#3#2#1#3#2#1#4!1'aR8!1'aV#4!1'aP8!1'aW#4!1'bK8!1'bO#4!3+_70!4'bM8#3#2#1!4'bN#4#3#2#1").
Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.

Definition kn_cutoutM (k : list kentry) := kn_cutoutB (mkbc k).
Lemma kn_cutoutM_eq : kn_cutoutM = kn_cutout. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+2+W%ub;R+C%uk;R+3%un;R+C0!5'aE01'bP'bN$k;R0vd!1'bQ#1!3+_71!1'bP#1!1'bN#1").
Qed.



(* [comment removed for export] *)
Definition kn_keep (k : list kentry) (ws : list (expr * expr)) : list kentry :=
  let wss := map (fun w => (split_lit (fst w), xlo k (snd w))) ws in
  let test (b : expr) (o : Z) (n : option Z) : bool :=
    let mine := List.filter (fun w => expr_eqb (fst (fst w)) b) wss in
    match mine with
    | [] => true
    | _ => existsb (fun w => let wk := snd (fst w) in
                             match snd w with
                             | Some wl => Z.ltb 0 wl && Z.ltb wk (match n with Some n => o + n | None => wk + 1 end) && Z.ltb o (wk + wl)
                             | None => true
                             end) mine
    end in
  List.filter (fun K => match K with
                        | KWord (SA b o) w _ => test b o (Some (Z.of_nat w))
                        | KZero (SA b o) n => test b o (xhi k n)
                        | KBlob (SA b o) n _ => test b o (xhi k n)
                        | KFill (SA b o) n _ => test b o (xhi k n)
                        | KUnk (SA b o) n => test b o (xhi k n)
                        | _ => true
                        end) k.

(* [comment removed for export] *)
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
      else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
  | _ => [K]
  end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$k;R!1+2+W$a;R+3$n;R+3!4'b=+W+W!2'bR#2#1#3").

(* [comment removed for export] *)
Definition kimg_clip (k : list kentry) : list kentry :=
  List.filter (fun K => match K with KImg lo hi => Z.leb (img_lo A) lo && Z.leb lo hi && Z.leb hi (img_hi A) | _ => true end) k.

(* [comment removed for export] *)
Definition kreadZ (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookup segs k b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.

Definition kreadZB (bc : bctx) (b : expr) (off : Z) (n : nat) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S40!1+^7+3!1+2+`U!1+2+1!1,[+3$bc;R+a3$b;R+C$off;R+3$n;R+5-bSRN$x;R+bS0!8'bT/segs;#4#3#2#1,6!1,Y+1!1,Y+`U3$v;R+C$scs;R1$hints;R2-CRN$v;R+C0#38$z;R+3-2RN$scs;R!1+2+`U0#32!2,^8+3!2'^9#1'^:$s;R+`U$l;R!1+2+`U3$n0;R+53$op;R+^;$a;R+C$b0;R+C3$op;R+^;$a;R+C$b0;R+C3$op;R+^<$a;R+C$b0;R+C3$op;R+^<$a;R+C$b0;R+C3$sx;R+1$lo;R+5$n0;R+5$e;R+C3$sx;R+1$k;R+5$i;R+3$n0;R+53$scs;R1$hints;R233").

Lemma kreadZB_eqf : forall fk, kreadZB (mkbc fk) = kreadZ fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;0!1+^7+3%n;R+50%rb;R+C%rk;R+3%n;R+5%sx;R+1%hints;R!1+2+1%acc;R!1+2+`U+bS!1,Y+1!1,Y+`U!1+2+`U!1+2+1!1,[+3-2RN$scs;R!1+2+`U0#32!2,^8+3!2'^9#1'^:$s;R+`U$l;R!1+2+`U7-CRN$v;R+C0#38$z;R+38$n0;R+57$op;R+^;$a;R+C$b0;R+C7$op;R+^;$a;R+C$b0;R+C7$op;R+^<$a;R+C$b0;R+C7$op;R+^<$a;R+C$b0;R+C7$sx;R+1$lo;R+5$n0;R+5$e;R+C7$sx;R+1$k0;R+5$i;R+3$n0;R+57!1'`W#4$fk;R!1+2+W!5'aE+C%off;R+31!1'bU!1'`W#1!1'bV#1$x;R+C!5'aE+31!2'bU!1'`W#2#1!2'bV#2#1$x0;R+3!5'aE+50!3'bU!1'`W#3#2#1!3'bV#3#2#1$x1;R+5vd!6'_F2!2'bW/segs;#4$l;R2!3+_70-bSRN$x;R+bS0!6#1#4#3#2,6343$v;R+C$scs;R5$hints;R6-CRN$v;R+C0#38$z;R+38$n0;R+57$op;R+^;$a;R+C$b0;R+C7$op;R+^;$a;R+C$b0;R+C7$op;R+^<$a;R+C$b0;R+C7$op;R+^<$a;R+C$b0;R+C7$sx;R+1$lo;R+5$n0;R+5$e;R+C7$sx;R+1$k;R+5$i;R+3$n0;R+57$scs;R5$hints;R677-bSRN$x;R+bS0!8'bW/segs;#5#4#3#2,6343$v;R+C$scs;R5$hints;R69$scs;R5$hints;R677!2,_G0-bSRN$x;R+bS0!8'bW/segs;#4#3#2#1,6343$v;R+C$scs;R5$hints;R69$scs;R5$hints;R677!2'bT/segs;:!2'bX#4/segs;!3+_70!4'bU:#3#2#1!4'bV#4#3#2#1").
Qed.
#[local] Hint Rewrite kreadZB_eqf : bceq.


(* [comment removed for export] *)
Definition kread8e (k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookup segs k b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Definition kread8eB (bc : bctx) (b : expr) (off : Z) : option expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!1+^7+C!1+2+`U!1+2+1!1,[+C$bc;R+a3$b;R+C$off;R+3-bSRN$x;R+bS0!8'bT/segs;#3#2#1}8,6!1,Y+1!1,Y+`U3$v;R+C$scs;R1$hints;R2-2RN$scs;R!1+2+`U0#22!2,^8+C#3$s;R+`U$l;R!1+2+`U3$scs;R1$hints;R233").

Lemma kread8eB_eqf : forall fk, kread8eB (mkbc fk) = kread8e fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S:0!1+^7+C%rb;R+C%rk;R+3%n;R+5%sx;R+1%hints;R!1+2+1%acc;R!1+2+`U+bS}8!1,Y+1!1,Y+`U!1+2+`U!1+2+1!1,[+C-2RN$scs;R!1+2+`U0#22!2,^8+C#3$s;R+`U$l;R!1+2+`U7!1'`W#3$fk;R!1+2+W!5'aE+C%off;R+30!1'bY!1'`W#1!1'bZ#1$x;R+C!5'aE+30!2'bY!1'`W#2#1!2'bZ#2#1$x0;R+3vd!6'_F1!2'bW/segs;#3$l;R1!3+_70-bSRN$x;R+bS0!6#1#3#22,6343$v;R+C$scs;R5$hints;R68$scs;R5$hints;R677-bSRN$x;R+bS0!8'bW/segs;#4#3#22,6343$v;R+C$scs;R5$hints;R68$scs;R5$hints;R677!2,_G0-bSRN$x;R+bS0!8'bW/segs;#3#2#12,6343$v;R+C$scs;R5$hints;R68$scs;R5$hints;R677!2'bT/segs;9!2'bX#3/segs;!3+_70!3'bY9#2#1!3'bZ#3#2#1").
Qed.
#[local] Hint Rewrite kread8eB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kwritable (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xlo allkn wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinside allkn b off (ELit n) wb wk wn)%bool then true
      else kwritable allkn rest b off n
  | _ :: rest => kwritable allkn rest b off n
  end.

Fixpoint kwritableB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xloB bc wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideB bc b off (ELit n) wb wk wn)%bool then true
      else kwritableB bc rest b off n
  | _ :: rest => kwritableB bc rest b off n
  end.

Lemma kwritableB_eqf : forall fk, kwritableB (mkbc fk) = kwritable fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SD0!1+2+W%n;R+3+1%off;R+31!2'^P!2'^Q#8#2!2'^R#1#7!1'`W#@!2'^S#2#1!2'^R!2'^S#8#75-1RN$~R+1+132-^7RN$x;R!1+^7+3+1!2'c04#32$wl;R+36,6,6!2'^P!2'^R,G#6!2'aC#6'^:!1,F#6!5'b\#?#9#7#6#5!5'b\#>#8#6#5#4!5'b\#@#:#8#7#6-1RN$~R+1+1!2'^P8!7'c3#@#8#79#2#1#32,^U<-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C:$a;R+\$n0;R+C;$a;R+\$n0;R+C$k1;R+5:$lo;R+3$hi;R+3;$e;R+C$m;R+3;$e;R+C$lo;R+3$hi;R+3:$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^7RN$x;R!1+^7+3+1!2'c2#@#32$wl;R+36,6,62,^U=$a1;R+\$n1;R+C$a2;R+\$n2;R+C<$a;R+\$n0;R+C$c;R+3:$a;R+\$n0;R+C;%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1%e;R+C!1+^7+3!5'b\#=#7#5#4#3!1'`W#;!3,_C+W#6#5$fk;R0!5'aE0%b;R+C2!1'b[!1'`W#1!1'b\#1$k;R0!5'aE+C2!2'b[!1'`W#2#1!2'b\#2#1$b;R+C!5'aE+31!3'b[!1'`W#3#2#1!3'b\#3#2#1$off;R+3!5'aE+3+1!4'b[!1'`W#4#3#2#1!4'b\#4#3#2#1$n;R+3!8'_Y+W$k;R0%b;R+C%off;R+3%n;R+3!3+_7+1!5'b[!1'`W#9#4#3#2#1!5'b\#9#4#3#2#1$b;R+C$off;R+3$n;R+3!2,_G+1!5'b\#8!1,Y+W#3#2#1$K;R+W$rest;R0$IH;R%b;R+C%off;R+3%n;R+3!3+_7+1!5'b[!1'`W#:#4#3#2#1!5'b\#:#4#3#2#1$b;R+C$off;R+3$n;R+3vd!6'_F+1!5'b\#;#5#3#2#1$b;R+1!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C#4$a;R+\$n0;R+C#3$a;R+\$n0;R+C$k1;R+5#4$lo;R+3$hi;R+3#3$e;R+C$m;R+3#3$e;R+C$lo;R+3$hi;R+3#4$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+172,^U-1RN$~R+1+1!2'^P8!7'c14#8#79#2#1#32,^U#5$a1;R+\$n1;R+C$a2;R+\$n2;R+C#5$a;R+\$n0;R+C$c;R+3#4$a;R+\$n0;R+C#3>!6'_F?!1'c3#;$b;R?!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C:$a;R+\$n0;R+C;$a;R+\$n0;R+C$k1;R+5:$lo;R+3$hi;R+3;$e;R+C$m;R+3;$e;R+C$lo;R+3$hi;R+3:$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+172,^U-1RN$~R+1+1!2'^P8!6#5#8#79#2#1#32,^U<$a1;R+\$n1;R+C$a2;R+\$n2;R+C<$a;R+\$n0;R+C$c;R+3:$a;R+\$n0;R+C;>!6'_F@!1'c2#;$o;R@!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C:$a;R+\$n0;R+C;$a;R+\$n0;R+C$k1;R+5:$lo;R+3$hi;R+3;$e;R+C$m;R+3;$e;R+C$lo;R+3$hi;R+3:$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^7RN$x;R!1+^7+3+1!1#5#32$wl;R+36,6,62,^U=$a1;R+\$n1;R+C$a2;R+\$n2;R+C<$a;R+\$n0;R+C$c;R+3:$a;R+\$n0;R+C;>!2,_G+1-WRN$k0;R+W+1#6:$a;R+\$w;R+5$v;R+C;$a;R+\$n0;R+CA$a;R+\$n0;R+C$k1;R+5;$lo;R+3$hi;R+3A$e;R+C$m;R+3A$e;R+C$lo;R+3$hi;R+3;$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+1-1RN$~R+1+1!2'^P!2'^Q#7#2!2'^R#1#62-^7RN$x;R!1+^7+3+1!2'c2#?#32$wl;R+3!2'^R!2'^S#7#65,6,62,^U-1RN$~R+1+1!2'^P!2'^P!2'^R,G#5!2'aC#5'^:!7'c3#?#7#6!1,F#5#2#1#32,^U:$a1;R+\$n1;R+C$a2;R+\$n2;R+C:$a;R+\$n0;R+C$c;R+3;$a;R+\$n0;R+CA!1'c0B!1'c4#;!1'c1B!1'c5#;!5'b[B#5#3#2#1!3#4#3#2#1!3+_7+1!5'b[BC#3#2#1!5'b\#;C#3#2#1#4#3#2#1").
Qed.
#[local] Hint Rewrite kwritableB_eqf : bceq.


Fixpoint kwritable_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhi allkn n, xlo allkn wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n wb wk wn then true
      else kwritable_x allkn rest b off n
  | _ :: rest => kwritable_x allkn rest b off n
  end.

Fixpoint kwritable_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhiB bc n, xloB bc wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n wb wk wn then true
      else kwritable_xB bc rest b off n
  | _ :: rest => kwritable_xB bc rest b off n
  end.

Lemma kwritable_xB_eqf : forall fk, kwritable_xB (mkbc fk) = kwritable_x fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SD0!1+2+W%n;R+C+1%off;R+31!2'^P!2'^Q#8#2!2'^R#1#7!1'`W#@!2'^S#3#1!2'^R!2'^S#9#25-^7RN$x;R!1+^7+3+1!2'c0!1'`W#A#42$wl;R+36,6-1RN$~R+1+132-^7RN$x;R!1+^7+3+1!2'c84#62$nh;R+37,6,6!5'c7#?#9#7#6#5!5'c7#>#8#6#5#4!2'c9#@#6!5'c7#@#:#8#7#6-1RN$~R+1+1!7'c3#@#8#7#6#2#1#32,^U<-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C9$a;R+\$n0;R+C:$a;R+\$n0;R+C$k1;R+59$lo;R+3$hi;R+3:$e;R+C$m;R+3:$e;R+C$lo;R+3$hi;R+39$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^7RN$x;R!1+^7+3+1;2$nh;R+3-^7RN$x;R!1+^7+3+1!2'c2#A#42$wl;R+36,6,6,62,^U=$a1;R+\$n1;R+C$a2;R+\$n2;R+C<$a;R+\$n0;R+C$c;R+39$a;R+\$n0;R+C:%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1%e;R+C!1+^7+3!5'c7#=#7#5#4#3!1'`W#;!3,_C+W#6#5$fk;R0!5'aE0%b;R+C2!1'c6!1'`W#1!1'c7#1$k;R0!5'aE+C2!2'c6!1'`W#2#1!2'c7#2#1$b;R+C!5'aE+31!3'c6!1'`W#3#2#1!3'c7#3#2#1$off;R+3!5'aE+C+1!4'c6!1'`W#4#3#2#1!4'c7#4#3#2#1$n;R+C!8'_Y+W$k;R0%b;R+C%off;R+3%n;R+C!3+_7+1!5'c6!1'`W#9#4#3#2#1!5'c7#9#4#3#2#1$b;R+C$off;R+3$n;R+C!2,_G+1!5'c7#8!1,Y+W#3#2#1$K;R+W$rest;R0$IH;R%b;R+C%off;R+3%n;R+C!3+_7+1!5'c6!1'`W#:#4#3#2#1!5'c7#:#4#3#2#1$b;R+C$off;R+3$n;R+Cvd!6'_F+1!5'c7#;#5#3#2#1$b;R+1!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C#4$a;R+\$n0;R+C#3$a;R+\$n0;R+C$k1;R+5#4$lo;R+3$hi;R+3#3$e;R+C$m;R+3#3$e;R+C$lo;R+3$hi;R+3#4$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+182,^U-1RN$~R+1+1!7'c14#8#7#6#2#1#32,^U#5$a1;R+\$n1;R+C$a2;R+\$n2;R+C#5$a;R+\$n0;R+C$c;R+3#4$a;R+\$n0;R+C#3>!6'_F?!1'c3#;$b;R?!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C9$a;R+\$n0;R+C:$a;R+\$n0;R+C$k1;R+59$lo;R+3$hi;R+3:$e;R+C$m;R+3:$e;R+C$lo;R+3$hi;R+39$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+182,^U-1RN$~R+1+1!6#5#8#7#6#2#1#32,^U<$a1;R+\$n1;R+C$a2;R+\$n2;R+C<$a;R+\$n0;R+C$c;R+39$a;R+\$n0;R+C:>!6'_F@!1'c9#;$o;R@!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C9$a;R+\$n0;R+C:$a;R+\$n0;R+C$k1;R+59$lo;R+3$hi;R+3:$e;R+C$m;R+3:$e;R+C$lo;R+3$hi;R+39$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^7RN$x;R!1+^7+3+1!1#5#62$nh;R+37,6,62,^U=$a1;R+\$n1;R+C$a2;R+\$n2;R+C<$a;R+\$n0;R+C$c;R+39$a;R+\$n0;R+C:>!6'_F@!1'c2#;$o;R@!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C9$a;R+\$n0;R+C:$a;R+\$n0;R+C$k1;R+59$lo;R+3$hi;R+3:$e;R+C$m;R+3:$e;R+C$lo;R+3$hi;R+39$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^7RN$x;R!1+^7+3+1;2$nh;R+3-^7RN$x;R!1+^7+3+1!1#6#42$wl;R+36,6,6,62,^U=$a1;R+\$n1;R+C$a2;R+\$n2;R+C<$a;R+\$n0;R+C$c;R+39$a;R+\$n0;R+C:>!2,_G+1-WRN$k0;R+W+1#6:$a;R+\$w;R+5$v;R+C:$a;R+\$n0;R+CA$a;R+\$n0;R+C$k1;R+5:$lo;R+3$hi;R+3A$e;R+C$m;R+3A$e;R+C$lo;R+3$hi;R+3:$a;R+\$wn;R+C-\RN$a;R+\+1#21$wb;R+C$wk;R+3-1RN$~R+1+1-1RN$~R+1+1!2'^P!2'^Q#7#2!2'^R#1#62-^7RN$x;R!1+^7+3+1!2'c9#?#52$nh;R+3-^7RN$x;R!1+^7+3+1!2'c2#@#42$wl;R+3!2'^R!2'^S#8#25,6,6,62,^U-1RN$~R+1+1!7'c3#?#7#6#5#2#1#32,^U9$a1;R+\$n1;R+C$a2;R+\$n2;R+C9$a;R+\$n0;R+C$c;R+3:$a;R+\$n0;R+CA!1'c0B!1'c4#;!1'c8B!1'c:#;!1'c1B!1'c5#;!5'c6B#5#3#2#1!3#4#3#2#1!3+_7+1!5'c6BC#3#2#1!5'c7#;C#3#2#1#4#3#2#1").
Qed.
#[local] Hint Rewrite kwritable_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kzero_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n zb zk zn then true
      else kzero_x allkn rest b off n
  | _ :: rest => kzero_x allkn rest b off n
  end.

Fixpoint kzero_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n zb zk zn then true
      else kzero_xB bc rest b off n
  | _ :: rest => kzero_xB bc rest b off n
  end.

Lemma kzero_xB_eqf : forall fk, kzero_xB (mkbc fk) = kzero_x fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SD0!1+2+W%n;R+C+1%off;R+31!2'^P!2'^Q#8#2!2'^R#1#7!1'`W#@!2'^S#3#1!2'^R!2'^S#9#25-^7RN$x;R!1+^7+3+1!2'c0!1'`W#A#42$zl;R+36,6-1RN$~R+1+132-^7RN$x;R!1+^7+3+1!2'c84#62$nh;R+37,6,6!5'c<#?#9#7#6#5!2'c9#@#6!5'c<#@#:#8#7#6-1RN$~R+1+1!7'c3#@#8#7#6#2#1#32,^U;!5'c<#>#8#6#5#4-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C9$a;R+\$zn;R+C-\RN$a;R+\+1#21$zb;R+C$zk;R+3-1RN$~R+1+1-1RN$~R+1+132-^7RN$x;R!1+^7+3+1:2$nh;R+3-^7RN$x;R!1+^7+3+1!2'c2#A#42$zl;R+36,6,6,62,^U<$a;R+\$n0;R+C$k1;R+59$lo;R+3$hi;R+3=$e;R+C$m;R+3=$e;R+C$lo;R+3$hi;R+39$a;R+\$n0;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C;$a;R+\$n0;R+C$c;R+39$a;R+\$n0;R+C=%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1%e;R+C!1+^7+3!5'c<#=#7#5#4#3!1'`W#;!3,_C+W#6#5$fk;R0!5'aE0%b;R+C2!1'c;!1'`W#1!1'c<#1$k;R0!5'aE+C2!2'c;!1'`W#2#1!2'c<#2#1$b;R+C!5'aE+31!3'c;!1'`W#3#2#1!3'c<#3#2#1$off;R+3!5'aE+C+1!4'c;!1'`W#4#3#2#1!4'c<#4#3#2#1$n;R+C!8'_Y+W$k;R0%b;R+C%off;R+3%n;R+C!3+_7+1!5'c;!1'`W#9#4#3#2#1!5'c<#9#4#3#2#1$b;R+C$off;R+3$n;R+C!2,_G+1!5'c<#8!1,Y+W#3#2#1$K;R+W$rest;R0$IH;R%b;R+C%off;R+3%n;R+C!3+_7+1!5'c;!1'`W#:#4#3#2#1!5'c<#:#4#3#2#1$b;R+C$off;R+3$n;R+Cvd!6'_F+1!5'c<#;#5#3#2#1$b;R+1!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C#4$a;R+\$zn;R+C-\RN$a;R+\+1#21$zb;R+C$zk;R+3-1RN$~R+1+182,^U-1RN$~R+1+1!7'c14#8#7#6#2#1#32,^U#5$a;R+\$n0;R+C$k1;R+5#4$lo;R+3$hi;R+3#3$e;R+C$m;R+3#3$e;R+C$lo;R+3$hi;R+3#4$a;R+\$n0;R+C#3$a1;R+\$n1;R+C$a2;R+\$n2;R+C#5$a;R+\$n0;R+C$c;R+3#4$a;R+\$n0;R+C#3>!6'_F?!1'c3#;$b;R?!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C9$a;R+\$zn;R+C-\RN$a;R+\+1#21$zb;R+C$zk;R+3-1RN$~R+1+182,^U-1RN$~R+1+1!6#5#8#7#6#2#1#32,^U;$a;R+\$n0;R+C$k1;R+59$lo;R+3$hi;R+3=$e;R+C$m;R+3=$e;R+C$lo;R+3$hi;R+39$a;R+\$n0;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C;$a;R+\$n0;R+C$c;R+39$a;R+\$n0;R+C=>!6'_F@!1'c9#;$o;R@!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C9$a;R+\$zn;R+C-\RN$a;R+\+1#21$zb;R+C$zk;R+3-1RN$~R+1+1-1RN$~R+1+132-^7RN$x;R!1+^7+3+1!1#5#62$nh;R+37,6,62,^U<$a;R+\$n0;R+C$k1;R+59$lo;R+3$hi;R+3=$e;R+C$m;R+3=$e;R+C$lo;R+3$hi;R+39$a;R+\$n0;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C;$a;R+\$n0;R+C$c;R+39$a;R+\$n0;R+C=>!6'_F@!1'c2#;$o;R@!3+_7+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C9$a;R+\$zn;R+C-\RN$a;R+\+1#21$zb;R+C$zk;R+3-1RN$~R+1+1-1RN$~R+1+132-^7RN$x;R!1+^7+3+1:2$nh;R+3-^7RN$x;R!1+^7+3+1!1#6#42$zl;R+36,6,6,62,^U<$a;R+\$n0;R+C$k1;R+59$lo;R+3$hi;R+3=$e;R+C$m;R+3=$e;R+C$lo;R+3$hi;R+39$a;R+\$n0;R+C=$a1;R+\$n1;R+C$a2;R+\$n2;R+C;$a;R+\$n0;R+C$c;R+39$a;R+\$n0;R+C=>!2,_G+1-WRN$k0;R+W+1#6:$a;R+\$w;R+5$v;R+C=$a;R+\$zn;R+C-\RN$a;R+\+1#21$zb;R+C$zk;R+3-1RN$~R+1+1-1RN$~R+1+1!2'^P!2'^Q#7#2!2'^R#1#62-^7RN$x;R!1+^7+3+1!2'c9#?#52$nh;R+3-^7RN$x;R!1+^7+3+1!2'c2#@#42$zl;R+3!2'^R!2'^S#8#25,6,6,62,^U-1RN$~R+1+1!7'c3#?#7#6#5#2#1#32,^U9$a;R+\$n0;R+C$k1;R+5=$lo;R+3$hi;R+3A$e;R+C$m;R+3A$e;R+C$lo;R+3$hi;R+3=$a;R+\$n0;R+CA$a1;R+\$n1;R+C$a2;R+\$n2;R+C9$a;R+\$n0;R+C$c;R+3=$a;R+\$n0;R+CA!1'c0B!1'c4#;!1'c8B!1'c:#;!1'c1B!1'c5#;!5'c;B#5#3#2#1!3#4#3#2#1!3+_7+1!5'c;BC#3#2#1!5'c<#;C#3#2#1#4#3#2#1").
Qed.
#[local] Hint Rewrite kzero_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kfill_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinside allkn b off n zb zk zn)%bool then true
      else kfill_x allkn rest b off n c
  | _ :: rest => kfill_x allkn rest b off n c
  end.

Fixpoint kfill_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideB bc b off n zb zk zn)%bool then true
      else kfill_xB bc rest b off n c
  | _ :: rest => kfill_xB bc rest b off n c
  end.

Lemma kfill_xB_eqf : forall fk, kfill_xB (mkbc fk) = kfill_x fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SJ0!1+2+W%c;R+3+1%n;R+C1%off;R+32!1,c?|800;!2'^9#34!2'aA5!2'^9#74!2'^P!2'^P6!2'^Q#:#2!2'^R#1#9!1'`W#C!2'^S#3#1!2'^R!2'^S#;#29-^7RN$x;R!1+^7+3+1!2'c0!1'`W#D#52$zl;R+3:,6-1RN$~R+1+172-^7RN$x;R!1+^7+3+1!2'c88#82$nh;R+3;,6,6!6'c>#A#:#8#7#6#5!6'c>#@#9#7#6#5#4!6'c>#B#;#9#8#7#6!2'c9#C#8!6'c>#C#<#:#9#8#7-1RN$~R+1+1!2'^P6!7'c3#C#:#9#8#2#1#42,^UA-WRN$k0;R+W+1#8:$a;R+\$w;R+5$v;R+C=$a;R+\$n0;R+C>$a;R+\$n0;R+C$k1;R+5=$lo;R+3$hi;R+3>$e;R+C$m;R+3>$e;R+C$lo;R+3$hi;R+3=$a;R+\$n0;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C?$a;R+\$zn;R+C$c';R+3-\RN$a;R+\+1#31$zb;R+C$zk;R+3-1RN$~R+1+1-1RN$~R+1+172-^7RN$x;R!1+^7+3+1@2$nh;R+3-^7RN$x;R!1+^7+3+1!2'c2#D#52$zl;R+3:,6,6,62,^UB$a;R+\$n0;R+C>%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1%e;R+C!1+^7+3!6'c>#?#8#6#5#4#3!2'aA5!2'^9#64!1'`W#=!3,_C+W#7#6$fk;R0!5'aE0%b;R+C3!1'c=!1'`W#1!1'c>#1$k;R0!5'aE+C3!2'c=!1'`W#2#1!2'c>#2#1$b;R+C!5'aE+32!3'c=!1'`W#3#2#1!3'c>#3#2#1$off;R+3!5'aE+C1!4'c=!1'`W#4#3#2#1!4'c>#4#3#2#1$n;R+C!5'aE+3+1!5'c=!1'`W#5#4#3#2#1!5'c>#5#4#3#2#1$c;R+3!9'_Y+W$k;R0%b;R+C%off;R+3%n;R+C%c;R+3!3+_7+1!6'c=!1'`W#;#5#4#3#2#1!6'c>#;#5#4#3#2#1$b;R+C$off;R+3$n;R+C$c;R+3!2,_G+1!6'c>#:!1,Y+W#4#3#2#1$K;R+W$rest;R0$IH;R%b;R+C%off;R+3%n;R+C%c;R+3!3+_7+1!6'c=!1'`W#<#5#4#3#2#1!6'c>#<#5#4#3#2#1$b;R+C$off;R+3$n;R+C$c;R+3vd!6'_F+1!6'c>#=#6#4#3#2#1$b;R+1!3+_7+1-WRN$k0;R+W+1#8:$a;R+\$w;R+5$v;R+C#4$a;R+\$n0;R+C#3$a;R+\$n0;R+C$k1;R+5#4$lo;R+3$hi;R+3#3$e;R+C$m;R+3#3$e;R+C$lo;R+3$hi;R+3#4$a;R+\$n0;R+C#3$a1;R+\$n1;R+C$a2;R+\$n2;R+C#5$a;R+\$zn;R+C$c';R+3-\RN$a;R+\+1#31$zb;R+C$zk;R+3-1RN$~R+1+1<2,^U-1RN$~R+1+1!2'^P6!7'c18#:#9#8#2#1#42,^U#6$a;R+\$n0;R+C#3C!6'_FD!1'c3#=$b;RD!3+_7+1-WRN$k0;R+W+1#8:$a;R+\$w;R+5$v;R+C=$a;R+\$n0;R+C>$a;R+\$n0;R+C$k1;R+5=$lo;R+3$hi;R+3>$e;R+C$m;R+3>$e;R+C$lo;R+3$hi;R+3=$a;R+\$n0;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C?$a;R+\$zn;R+C$c';R+3-\RN$a;R+\+1#31$zb;R+C$zk;R+3-1RN$~R+1+1<2,^U-1RN$~R+1+1!2'^P6!6#6#:#9#8#2#1#42,^UA$a;R+\$n0;R+C>C!6'_FE!1'c9#=$o;RE!3+_7+1-WRN$k0;R+W+1#8:$a;R+\$w;R+5$v;R+C=$a;R+\$n0;R+C>$a;R+\$n0;R+C$k1;R+5=$lo;R+3$hi;R+3>$e;R+C$m;R+3>$e;R+C$lo;R+3$hi;R+3=$a;R+\$n0;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C?$a;R+\$zn;R+C$c';R+3-\RN$a;R+\+1#31$zb;R+C$zk;R+3-1RN$~R+1+1-1RN$~R+1+172-^7RN$x;R!1+^7+3+1!1#6#82$nh;R+3;,6,62,^UB$a;R+\$n0;R+C>C!6'_FE!1'c2#=$o;RE!3+_7+1-WRN$k0;R+W+1#8:$a;R+\$w;R+5$v;R+C=$a;R+\$n0;R+C>$a;R+\$n0;R+C$k1;R+5=$lo;R+3$hi;R+3>$e;R+C$m;R+3>$e;R+C$lo;R+3$hi;R+3=$a;R+\$n0;R+C>$a1;R+\$n1;R+C$a2;R+\$n2;R+C?$a;R+\$zn;R+C$c';R+3-\RN$a;R+\+1#31$zb;R+C$zk;R+3-1RN$~R+1+1-1RN$~R+1+172-^7RN$x;R!1+^7+3+1@2$nh;R+3-^7RN$x;R!1+^7+3+1!1#7#52$zl;R+3:,6,6,62,^UB$a;R+\$n0;R+C>C!2,_G+1-WRN$k0;R+W+1#7:$a;R+\$w;R+5$v;R+C>$a;R+\$n0;R+CF$a;R+\$n0;R+C$k1;R+5>$lo;R+3$hi;R+3F$e;R+C$m;R+3F$e;R+C$lo;R+3$hi;R+3>$a;R+\$n0;R+CF$a1;R+\$n1;R+C$a2;R+\$n2;R+C=$a;R+\$zn;R+C$c';R+3-\RN$a;R+\+1#31$zb;R+C$zk;R+3-1RN$~R+1+1-1RN$~R+1+1!2'^P!2'^PG!2'^Q#9#2!2'^R#1#82-^7RN$x;R!1+^7+3+1!2'c9#B#72$nh;R+3-^7RN$x;R!1+^7+3+1!2'c2#C#52$zl;R+3!2'^R!2'^S#:#29,6,6,62,^U-1RN$~R+1+1!2'^PG!7'c3#B#9#8#7#2#1#42,^U?$a;R+\$n0;R+CF!1'c0H!1'c4#=!1'c8H!1'c:#=!1'c1H!1'c5#=!6'c=H#6#4#3#2#1!4#5#4#3#2#1!3+_7+1!6'c=HI#4#3#2#1!6'c>#=I#4#3#2#1#5#4#3#2#1").
Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!1'c@/A;$bc;R+a3$b;R+C$off;R+3$n;R+C!7'aB#4#3#2#1!1,F,G0!1,F!2'aD!1'cA/A;0").

Lemma off_image_xB_eqf : forall fk, off_image_xB (mkbc fk) = off_image_x fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60%n;R+C+1%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1!1,F,G!1'c@/A;!1,F!2'aD!1'cA/A;3!1'`W#4$fk;R!1+2+W!5'aE+C%off;R+30!1'cB!1'`W#1!1'cC#1$x;R+C!5'aE+30!2'cB!1'`W#2#1!2'cC#2#1$x0;R+3!5'aE+C+1!3'cB!1'`W#3#2#1!3'cC#3#2#1$x1;R+Cvd!6'_F1!1'aH#4$b;R1!3+_7+1!6#1#4#3#2234!7'aH#5#4#3#2234!2,_G+1!7'aH#4#3#2#1234!1'aB5!1'aI#4!3+_7+1!4'cB5#3#2#1!4'cC#4#3#2#1").
Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flat_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xlo k n, xhi k n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Definition flat_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!2+^I+3+3$bc;R+a3$b;R+C$off;R+3$n;R+C-^7RN$x;R!1+^70+1!2'cD#4#32$p;R0-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3-^7RN$x;R!1+^7+3+1!2'c0#7#42$nl;R+3-^7RN$x;R!1+^7+3+1!2'c8#8#52$nh;R+3!2'^P!2'^P!2'^R,G!2'^S#4#7!2'^R!2'^S!2'^S#3#7#1'^:!2'aC,G#2,6,6,6").

Lemma flat_xB_eqf : forall fk, flat_xB (mkbc fk) = flat_x fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;0%n;R+C+1%e;R+C!1+^7+3!2+^I+3+3!2'cD!1'`W#5#4!2'aC,G#2!2'^P!2'^P!2'^R,G!2'^S#4#8!2'^R!2'^S!2'^S#3#8#1'^:4-^7RN$x;R!1+^7+3+1!2'c9#9#62$nh;R+35,6-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3-^7RN$x;R!1+^7+3+1!2'c2#8#52$nl;R+36,6-^7RN$x;R!1+^72+1!2'cG#5#42$p;R27,6%e;R+C!1+^72!1'`W#4$fk;R!1+2+W!5'aE+C%off;R+30!1'cE!1'`W#1!1'cF#1$x;R+C!5'aE+30!2'cE!1'`W#2#1!2'cF#2#1$x0;R+3!5'aE+C+1!3'cE!1'`W#3#2#1!3'cF#3#2#1$x1;R+Cvd!6'_F1!1'c9#4$o;R1!3+_7+1-^7RN$x;R!1+^72+132$p;R2-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3-^7RN$x;R!1+^7+3+1!2'c0!1'`W#8#52$nl;R+3-^7RN$x;R!1+^7+3+1!1#5#62$nh;R+35,6,6,68!6'_F1!1'c2#4$o;R1!3+_7+1-^7RN$x;R!1+^72+132$p;R2-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3-^7RN$x;R!1+^7+3+1!1#4#52$nl;R+36,6,68!6'_F9!1'cG#4$o;R9!3+_7+1-^7RN$x;R!1+^72+1!1#1#42$p;R27,68!2,_G+1-^7RN$x;R!1+^72+1!2'cG#4#32$p;R2-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3-^7RN$x;R!1+^7+3+1!2'c2#7#42$nl;R+3-^7RN$x;R!1+^7+3+1!2'c9#8#52$nh;R+3!2'^P!2'^P!2'^R,G!2'^S#4#7!2'^R!2'^S!2'^S#3#7#1'^:4,6,6,6!1'cD:!1'cH#4!1'c0:!1'c4#4!1'c8:!1'c:#4!3+_7+1!4'cE:#3#2#1!4'cF#4#3#2#1").
Qed.
#[local] Hint Rewrite flat_xB_eqf : bceq.



(* [comment removed for export] *)
Definition ehi (k : list kentry) (e : expr) : option Z := xhi k e.
Definition elo (k : list kentry) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$k;R!1+2+W$e;R+C!2'c2#2#1").

(* [comment removed for export] *)
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]).

Definition len_eqbB (bc : bctx) (n m : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!2+^I+C+3!1,Y0!3,_C0!4,cJ+C+3#2,G1!3,_C0!4,cJ+C+3#1,G1$bc;R+a3$n;R+C$m;R+C!2'^M!2'^Q#2#1!2'^P!3'cI#323!3'cI#332").

Lemma len_eqbB_eqf : forall fk, len_eqbB (mkbc fk) = len_eqb fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80%pos;R'cM%neg;R'cM+1!2'^Q#3#2!2+^I+C+3!1,Y2!3,_C2!4,cJ+C+3#3,G3!3,_C2!4,cJ+C+3#2,G3!3,_C2!4,cJ+C+3#1,G3!1'`W#3$fk;R!1+2+W!5'aE+C%m;R+C+1!1'cK!1'`W#1!1'cL#1$x;R+C!5'aE+C+1!2'cK!1'`W#2#1!2'cL#2#1$x0;R+Cvd!6'_F0!1'cN#3$b;R0!3+_7+1!2'^M1!2'^P!2#145!2#154!2'^M1!2'^P!3'cN#445!3'cN#454!2,_G+1!2'^M!2'^Q#2#1!2'^P!3'cN#356!3'cN#365!1'cI7!1'cO#3!3+_7+1!3'cK7#2#1!3'cL#3#2#1").
Qed.
#[local] Hint Rewrite len_eqbB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_diff (e f : expr) : option Z :=
  match esub e f with ELit z => Some (z mod two64) | _ => None end.

(* [comment removed for export] *)
Definition page_aligned (k : list kentry) (e : expr) : bool :=
  match e with
  | ELit z => Z.eqb (z mod 4096) 0
  | _ => Z.leb 12 (ealign k e)
  end.

Definition page_alignedB (bc : bctx) (e : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!1,c?|34;!2'^R0!2'cP#5#4!2'^R0!2'cP#6#5$bc;R+a3$e;R+C-CRN$e;R+C+1#18$z;R+3!2'aA!2'^9#1!1,c?|<000;,G$n;R+5!2'^R0!2'cP#3#2$op;R+^;$a;R+C$b;R+C1$op;R+^;$a;R+C$b;R+C1$op;R+^<$a;R+C$b;R+C1$op;R+^<$a;R+C$b;R+C1$sx;R+1$lo;R+5$n;R+5$e0;R+C2$sx;R+1$k;R+5$i;R+3$n;R+52").

Lemma page_alignedB_eqf : forall fk, page_alignedB (mkbc fk) = page_aligned fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90%e;R+C+3!2'aA!2'^9#1!1,c?|<000;,G!1,c?|34;!2'^R2!1#4#5!2'^R2!1#5#6!2'^R2!2'cS#6#5!2'^R2!2'cS#7#6!2'^R2!2'cS#5#4!1'`W#2$fk;R!1+2+W!5'aE+C+1!1'cQ!1'`W#1!1'cR#1$x;R+Cvd!6'_F0!1'cS#2$z;R0!3+_7+1-CRN$e;R+C+1#28$z;R+31$n;R+5!2'^R2!1#2#3$op;R+^;$a;R+C$b;R+C3$op;R+^;$a;R+C$b;R+C3$op;R+^<$a;R+C$b;R+C3$op;R+^<$a;R+C$b;R+C3$sx;R+1$lo;R+5$n;R+5$e0;R+C4$sx;R+1$k;R+5$i;R+3$n;R+54-CRN$e;R+C+1#28$z;R+31$n;R+5!2'^R2!2'cS#4#3$op;R+^;$a;R+C$b;R+C5$op;R+^;$a;R+C$b;R+C5$op;R+^<$a;R+C$b;R+C5$op;R+^<$a;R+C$b;R+C5$sx;R+1$lo;R+5$n;R+5$e0;R+C6$sx;R+1$k0;R+5$i;R+3$n;R+56!2,_G+1-CRN$e;R+C+1#18$z;R+31$n;R+5!2'^R2!2'cS#3#2$op;R+^;$a;R+C$b;R+C7$op;R+^;$a;R+C$b;R+C7$op;R+^<$a;R+C$b;R+C7$op;R+^<$a;R+C$b;R+C7$sx;R+1$lo;R+5$n;R+5$e0;R+C5$sx;R+1$k0;R+5$i;R+3$n;R+55!1'cP8!1'cT#2!3+_7+1!2'cQ8#1!2'cR#2#1").
Qed.
#[local] Hint Rewrite page_alignedB_eqf : bceq.



(* [comment removed for export] *)
Definition kn_contra (k : list kentry) : bool :=
  existsb (fun K => match K with
                    | KRange e lo hi =>
                        if Z.ltb hi lo then true else
                        match e with
                        | EVar _ => false
                        | _ => let l := lin_of e in
                               match snd l with
                               | _ :: _ :: _ =>
                                   match lin_range (erange k) (fst l) (snd l) with
                                   | Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
                                   | None => false
                                   end
                               | _ => false
                               end
                        end
                    | _ => false
                    end) k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition caller_saved : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

Fixpoint sr_fresh (sr : list expr) (ixs : list nat) (nx : nat) : list expr :=
  match ixs with
  | [] => sr
  | i :: t => sr_fresh (sr_upd sr i (EVar nx)) t (S nx)
  end.

Definition NCS : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00}@").

Definition ret_lit (cs : acs) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!1+^7+3!1,[+3$cs;R+A-CRN$x;R+C0!2'^>#1}18$r;R+3-1RN$~R+10!2'^P!2'^P!2'aA!2'^9#1!1,c?|10;,G!2'aC#1'^:!2'^R,G#12!2,^8+3#11$n;R+51$op;R+^;$a;R+C$b;R+C1$op;R+^;$a;R+C$b;R+C1$op;R+^<$a;R+C$b;R+C1$op;R+^<$a;R+C$b;R+C1$sx;R+1$lo;R+5$n;R+5$e;R+C1$sx;R+1$k;R+5$i;R+3$n;R+51").

(* [comment removed for export] *)
Definition after_call (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) : option acs :=
  let ss := a_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt nx k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS)))
  else None.
(* [comment removed for export] *)
Definition after_call2 (cs : acs) (ret : Z) (rv : option expr) (k' : list kentry) (extra : nat) : option acs :=
  let ss := a_ss cs in
  let nx := s_next ss in
  let sr1 := sr_fresh (s_regs ss) caller_saved nx in
  let sr2 := match rv with Some e => sr_upd sr1 10 e | None => sr1 end in
  if (fresh_ok cs && kn_vars_lt (nx + NCS + extra) k' && match rv with Some e => expr_vars_lt nx e | None => true end)%bool
  then Some (with_ss cs (mk_ss ret sr2 k' (nx + NCS + extra)))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition page_up (len : Z) : Z := ((len + 4095) / 4096) * 4096.

Definition is_ecall_at (cs : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S40!1'cU#1|20;|500;!1+cV!1,cW2$cs;R+A!2'^P!2'^P!2'^R,G0!2'aC!2'^S0!1,c?1'^:-^7RN$x;R!1+^73+1!2'cX/segs;!2'cY!1,cW|600;02$w;R3!1'cZ#1,6").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xlo1 (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange k e, lin_brange k e with
         | Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
         | Some (lo, _), None => Some lo
         | None, Some (lo', _) => Some lo'
         | None, None => match lin_srange k e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
         end
  end.

Definition xlo1B (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e, lin_brangeB bc e with
         | Some (lo, _), Some (lo', _) => Some (Z.max lo lo')
         | Some (lo, _), None => Some lo
         | None, Some (lo', _) => Some lo'
         | None, None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end   (* [comment removed for export] *)
         end
  end.

Lemma xlo1B_eqf : forall fk, xlo1B (mkbc fk) = xlo1 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SV0!1+^7+3!2+^I+3+3%e;R+C!1+^71!2,^8+3!1'd1#1!1'`W#4!2'd24#3!1#5#6-^IRN$p0;R!2+^I+3+30#11$lo';R+3$z0;R+3!2,^8+3!2'd3#5#2!2,^8+3#2!1#2#3-^IRN$p;R!2+^I+3+30#11$lo';R+3$z;R+38-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+38!1,[+3!1'`W#6!2'd2=#5!1#4#5-^7RN$x;R!1+^710>2$p;R1-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3-^7RN$x;R!1+^710!1#7#82$p0;R178-^7RN$x;R!1+^710?2$p;R1:-^7RN$x;R!1+^710!2'd4=#52$p;R1;<!1'`W#7!2'd2A#6-^7RN$x;R!1+^710B2$p;R1-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3-^7RN$x;R!1+^710!1#8#92$p0;R178-^7RN$x;R!1+^71062$p;R1:-^7RN$x;R!1+^710!2'd4A#62$p;R1;<!2'd0#7#6-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3-^7RN$x;R!1+^710D2$p0;R178!2'd0#4#3-^7RN$x;R!1+^710F2$p;R1:-^7RN$x;R!1+^710!2'd6#4#32$p;R1;<-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3-^7RN$x;R!1+^710!2'd0#9#82$p0;R178!2'd0#6#5-^7RN$x;R!1+^710I2$p;R1:-^7RN$x;R!1+^710!2'd6#6#52$p;R1;<-^7RN$x;R!1+^710!2'd5#6#52$p;R1HJ-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3-^7RN$x;R!1+^710!2'd0#:#92$p0;R178-^7RN$x;R!1+^710D2$p;R1:-^7RN$x;R!1+^710!2'd6#7#62$p;R1;<-^7RN$x;R!1+^710!2'd5#7#62$p;R1LM-CRN$e;R+C0#28$z;R+33$n;R+5-^7RN$x;R!1+^710!2'd5#4#32$p;R1EG$op;R+^;$a;R+C$b;R+CK$op;R+^;$a;R+C$b;R+CK$op;R+^<$a;R+C$b;R+CK$op;R+^<$a;R+C$b;R+CK$sx;R+1$lo;R+5$n;R+5$e0;R+CN$sx;R+1$k0;R+5$i;R+3$n;R+5N-^7RN$x;R!1+^710>2$p;R1H-^7RN$x;R!1+^710I2$p;R1:-^7RN$x;R!1+^710?2$p;R1;<-^7RN$x;R!1+^710B2$p;R1L-^7RN$x;R!1+^710D2$p;R1:-^7RN$x;R!1+^71062$p;R1;<-^7RN$x;R!1+^710?2$p;R1HJ-^7RN$x;R!1+^71062$p;R1LM-^7RN$x;R!1+^710!2'd5#5#42$p;R1-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3-^7RN$x;R!1+^710!2'd0#8#72$p0;R178-^7RN$x;R!1+^710!2'd0#5#42$p;R1:-^7RN$x;R!1+^710!2'd6#5#42$p;R1;<!1'`W#2$fk;R!1+2+W!5'aE+C0!1'c[!1'`W#1!1'c\#1$x;R+Cvd!6'_F2!1'd0#2$o;R2!3+_70-CRN$e;R+C0#28$z;R+33$n;R+5-^7RN$x;R!1+^71052$p;R1-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3-^7RN$x;R!1+^71062$p0;R178-^7RN$x;R!1+^71092$p;R1:-^7RN$x;R!1+^710!2'd44#32$p;R1;<$op;R+^;$a;R+C$b;R+C@$op;R+^;$a;R+C$b;R+C@$op;R+^<$a;R+C$b;R+C@$op;R+^<$a;R+C$b;R+C@$sx;R+1$lo;R+5$n;R+5$e0;R+CC$sx;R+1$k;R+5$i;R+3$n;R+5CO!6'_F2!1'd6#2$o;R2!3+_70-CRN$e;R+C0#28$z;R+33$n;R+5-^7RN$x;R!1+^71052$p;R1E-^7RN$x;R!1+^710F2$p;R1:-^7RN$x;R!1+^71092$p;R1;<$op;R+^;$a;R+C$b;R+CP$op;R+^;$a;R+C$b;R+CP$op;R+^<$a;R+C$b;R+CP$op;R+^<$a;R+C$b;R+CP$sx;R+1$lo;R+5$n;R+5$e0;R+CQ$sx;R+1$k;R+5$i;R+3$n;R+5QO!6'_F2!1'd5#2$o;R2!3+_70-CRN$e;R+C0#28$z;R+33$n;R+5-^7RN$x;R!1+^71092$p;R1EG$op;R+^;$a;R+C$b;R+CR$op;R+^;$a;R+C$b;R+CR$op;R+^<$a;R+C$b;R+CR$op;R+^<$a;R+C$b;R+CR$sx;R+1$lo;R+5$n;R+5$e0;R+CS$sx;R+1$k;R+5$i;R+3$n;R+5SO!2,_G0-CRN$e;R+C0#18$z;R+33$n;R+5-^7RN$x;R!1+^710!2'd5#3#22$p;R1-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3-^7RN$x;R!1+^710I2$p0;R178-^7RN$x;R!1+^710!2'd0#3#22$p;R1:-^7RN$x;R!1+^710!2'd6#3#22$p;R1;<$op;R+^;$a;R+C$b;R+CT$op;R+^;$a;R+C$b;R+CT$op;R+^<$a;R+C$b;R+CT$op;R+^<$a;R+C$b;R+CT$sx;R+1$lo;R+5$n;R+5$e0;R+CK$sx;R+1$k0;R+5$i;R+3$n;R+5K!1'd2U!1'd7#2!1'd4U!1'd8#2!1'd9U!1'd:#2!3+_70!2'c[U#1!2'c\#2#1").
Qed.
#[local] Hint Rewrite xlo1B_eqf : bceq.


Definition xhi1 (k : list kentry) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erange k e, lin_brange k e with
         | Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
         | Some (_, hi), None => Some hi
         | None, Some (_, hi') => Some hi'
         | None, None => match lin_srange k e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
         end
  end.

Definition xhi1B (bc : bctx) (e : expr) : option Z :=
  match e with
  | ELit z => Some (zlit64 z)
  | _ => match erangeB bc e, lin_brangeB bc e with
         | Some (_, hi), Some (_, hi') => Some (Z.min hi hi')
         | Some (_, hi), None => Some hi
         | None, Some (_, hi') => Some hi'
         | None, None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end   (* [comment removed for export] *)
         end
  end.

Lemma xhi1B_eqf : forall fk, xhi1B (mkbc fk) = xhi1 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SV0!1+^7+3!2+^I+3+3%e;R+C!1+^71!2,^8+3!1'd1#1!1'`W#4!2'd24#3!1#5#6-^IRN$p0;R!2+^I+3+30#11$z0;R+3$hi';R+3!2,^8+3!2'd=#4#1!2,^8+3#1!1#2#3-^IRN$p;R!2+^I+3+30#11$z;R+3$hi';R+38-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+38!1,[+3!1'`W#6!2'd2=#5!1#4#5-^7RN$x;R!1+^710>2$p;R1-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3-^7RN$x;R!1+^710!1#7#82$p0;R178-^7RN$x;R!1+^710?2$p;R1:-^7RN$x;R!1+^710!2'd4=#52$p;R1;<!1'`W#7!2'd2A#6-^7RN$x;R!1+^710B2$p;R1-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3-^7RN$x;R!1+^710!1#8#92$p0;R178-^7RN$x;R!1+^71062$p;R1:-^7RN$x;R!1+^710!2'd4A#62$p;R1;<!2'd0#7#6-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3-^7RN$x;R!1+^710D2$p0;R178!2'd0#4#3-^7RN$x;R!1+^710F2$p;R1:-^7RN$x;R!1+^710!2'd6#4#32$p;R1;<-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3-^7RN$x;R!1+^710!2'd0#9#82$p0;R178!2'd0#6#5-^7RN$x;R!1+^710I2$p;R1:-^7RN$x;R!1+^710!2'd6#6#52$p;R1;<-^7RN$x;R!1+^710!2'd5#6#52$p;R1HJ-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3-^7RN$x;R!1+^710!2'd0#:#92$p0;R178-^7RN$x;R!1+^710D2$p;R1:-^7RN$x;R!1+^710!2'd6#7#62$p;R1;<-^7RN$x;R!1+^710!2'd5#7#62$p;R1LM-CRN$e;R+C0#28$z;R+33$n;R+5-^7RN$x;R!1+^710!2'd5#4#32$p;R1EG$op;R+^;$a;R+C$b;R+CK$op;R+^;$a;R+C$b;R+CK$op;R+^<$a;R+C$b;R+CK$op;R+^<$a;R+C$b;R+CK$sx;R+1$lo;R+5$n;R+5$e0;R+CN$sx;R+1$k0;R+5$i;R+3$n;R+5N-^7RN$x;R!1+^710>2$p;R1H-^7RN$x;R!1+^710I2$p;R1:-^7RN$x;R!1+^710?2$p;R1;<-^7RN$x;R!1+^710B2$p;R1L-^7RN$x;R!1+^710D2$p;R1:-^7RN$x;R!1+^71062$p;R1;<-^7RN$x;R!1+^710?2$p;R1HJ-^7RN$x;R!1+^71062$p;R1LM-^7RN$x;R!1+^710!2'd5#5#42$p;R1-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3-^7RN$x;R!1+^710!2'd0#8#72$p0;R178-^7RN$x;R!1+^710!2'd0#5#42$p;R1:-^7RN$x;R!1+^710!2'd6#5#42$p;R1;<!1'`W#2$fk;R!1+2+W!5'aE+C0!1'd;!1'`W#1!1'd<#1$x;R+Cvd!6'_F2!1'd0#2$o;R2!3+_70-CRN$e;R+C0#28$z;R+33$n;R+5-^7RN$x;R!1+^71052$p;R1-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3-^7RN$x;R!1+^71062$p0;R178-^7RN$x;R!1+^71092$p;R1:-^7RN$x;R!1+^710!2'd44#32$p;R1;<$op;R+^;$a;R+C$b;R+C@$op;R+^;$a;R+C$b;R+C@$op;R+^<$a;R+C$b;R+C@$op;R+^<$a;R+C$b;R+C@$sx;R+1$lo;R+5$n;R+5$e0;R+CC$sx;R+1$k;R+5$i;R+3$n;R+5CO!6'_F2!1'd6#2$o;R2!3+_70-CRN$e;R+C0#28$z;R+33$n;R+5-^7RN$x;R!1+^71052$p;R1E-^7RN$x;R!1+^710F2$p;R1:-^7RN$x;R!1+^71092$p;R1;<$op;R+^;$a;R+C$b;R+CP$op;R+^;$a;R+C$b;R+CP$op;R+^<$a;R+C$b;R+CP$op;R+^<$a;R+C$b;R+CP$sx;R+1$lo;R+5$n;R+5$e0;R+CQ$sx;R+1$k;R+5$i;R+3$n;R+5QO!6'_F2!1'd5#2$o;R2!3+_70-CRN$e;R+C0#28$z;R+33$n;R+5-^7RN$x;R!1+^71092$p;R1EG$op;R+^;$a;R+C$b;R+CR$op;R+^;$a;R+C$b;R+CR$op;R+^<$a;R+C$b;R+CR$op;R+^<$a;R+C$b;R+CR$sx;R+1$lo;R+5$n;R+5$e0;R+CS$sx;R+1$k;R+5$i;R+3$n;R+5SO!2,_G0-CRN$e;R+C0#18$z;R+33$n;R+5-^7RN$x;R!1+^710!2'd5#3#22$p;R1-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3-^7RN$x;R!1+^710I2$p0;R178-^7RN$x;R!1+^710!2'd0#3#22$p;R1:-^7RN$x;R!1+^710!2'd6#3#22$p;R1;<$op;R+^;$a;R+C$b;R+CT$op;R+^;$a;R+C$b;R+CT$op;R+^<$a;R+C$b;R+CT$op;R+^<$a;R+C$b;R+CT$sx;R+1$lo;R+5$n;R+5$e0;R+CK$sx;R+1$k0;R+5$i;R+3$n;R+5K!1'd2U!1'd7#2!1'd4U!1'd8#2!1'd9U!1'd:#2!3+_70!2'd;U#1!2'd<#2#1").
Qed.
#[local] Hint Rewrite xhi1B_eqf : bceq.



(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := m mod two64 in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', s + (2 ^ j - 1))
      else (e, 0)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', s1 + s2)
  | _ => (e, 0)
  end.

Definition xb2 (k : list kentry) (e : expr) : option (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2+^I+3+3!1+^70!1,[0$k;R!1+2+W$e;R+C&plain;R-^7RN$x;R!1+^7+31!2'c\#2#12$lo;R+3-^7RN$x;R!1+^7+31!2'd<#3#22$hi;R+3!2,^80!4,cJ+3+3#2#1221-^IRN$x;R!2+^I+C+31!1'd>#21$e';R+C$s;R+3-1RN$~R+11!2'aA#1,G2#3-^7RN$x;R!1+^7+31!2'c\#5#22$lo';R+3-^7RN$x;R!1+^7+31!2'd<#6#32$hi';R+3-1RN$~R+11!2'^R#3#22-^7RN$plain;R!1+^701#52$p;R0-^IRN$p;R!2+^I+3+31#11$lo;R+3$hi;R+3!2,^80!4,cJ+3+3!2'd3#2!2'aD#5#6!2'd=#1#4!2,^80!4,cJ+3+3!2'aD#2#3#1#5#4#3").

Definition xb2B (bc : bctx) (e : expr) : option (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2+^I+3+3!1+^70!1,[0$bc;R+a3$e;R+C&plain;R-^7RN$x;R!1+^7+31!2'c[#2#12$lo;R+3-^7RN$x;R!1+^7+31!2'd;#3#22$hi;R+3!2,^80!4,cJ+3+3#2#1221-^IRN$x;R!2+^I+C+31!1'd>#21$e';R+C$s;R+3-1RN$~R+11!2'aA#1,G2#3-^7RN$x;R!1+^7+31!2'c[#5#22$lo';R+3-^7RN$x;R!1+^7+31!2'd;#6#32$hi';R+3-1RN$~R+11!2'^R#3#22-^7RN$plain;R!1+^701#52$p;R0-^IRN$p;R!2+^I+3+31#11$lo;R+3$hi;R+3!2,^80!4,cJ+3+3!2'd3#2!2'aD#5#6!2'd=#1#4!2,^80!4,cJ+3+3!2'aD#2#3#1#5#4#3").

Lemma xb2B_eqf : forall fk, xb2B (mkbc fk) = xb2 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SK0!2+^I+3+3!1+^70%e;R+C!1+^7+3!1'd>#2!2'aA#1,G!1'`W#5!1#4#5!2,^80!4,cJ+3+3#2#1!1,[0-^7RN$x;R!1+^7+31!2'c[5#42$lo;R+3-^7RN$x;R!1+^7+3162$hi;R+3788!2'^R#3#2-^7RN$x;R!1+^7+31!2'c[!1'`W#7#62$lo;R+3-^7RN$x;R!1+^7+31!1#6#72$hi;R+3788-^IRN$p;R!2+^I+3+31#11$lo;R+3$hi;R+3!2,^80!4,cJ+3+3!2'd3#2!2'aD#5#6!2'd=#1#4!2,^80!4,cJ+3+3!2'aD#2#3#1!1#5#6-^7RN$x;R!1+^7+31!2'd<#6#52$hi;R+378-^7RN$x;R!1+^7+31!2'c\#5#42$lo;R+3?8!2'd<#6#3-^7RN$x;R!1+^7+31!2'd<#8#72$hi;R+378-^7RN$x;R!1+^7+31!2'c\#7#62$lo;R+3B8-^7RN$x;R!1+^7+31!2'd<#7#62$hi;R+378-^7RN$x;R!1+^7+31!2'c\#6#52$lo;R+3D8-^IRN$x;R!2+^I+C+3131$e';R+C$s;R+3-1RN$~R+1142@-^7RN$x;R!1+^7+31!2'c\#5#22$lo';R+3-^7RN$x;R!1+^7+31A2$hi';R+3-1RN$~R+11:2-^7RN$plain;R!1+^701C2$p;R0<=CE@-^7RN$x;R!1+^7+31!1#3#42$lo;R+3?8-^7RN$x;R!1+^7+31>2$lo;R+3B8-^7RN$x;R!1+^7+31!2'c\#4#32$lo;R+3-^7RN$x;R!1+^7+31!2'd<#5#42$hi;R+3788!1'`W#2$fk;R!1+2+W!5'aE+C1!1'd?!1'`W#1!1'd@#1$x;R+Cvd!6'_F2!1'd<#2$o;R2!3+_71-^IRN$x;R!2+^I+C+3131$e';R+C$s;R+3-1RN$~R+11429-^7RN$x;R!1+^7+31!2'c[5#22$lo';R+3-^7RN$x;R!1+^7+31!1#4#32$hi';R+3-1RN$~R+11:2-^7RN$plain;R!1+^701;2$p;R0<=;-^7RN$x;R!1+^7+31!2'c[!1'`W#6#52$lo;R+3-^7RN$x;R!1+^7+31>2$hi;R+37889F!6'_F2!1'c\#2$o;R2!3+_71-^IRN$x;R!2+^I+C+3131$e';R+C$s;R+3-1RN$~R+1142G-^7RN$x;R!1+^7+31!1#3#22$lo';R+3-^7RN$x;R!1+^7+31A2$hi';R+3-1RN$~R+11:2-^7RN$plain;R!1+^701H2$p;R0<=H-^7RN$x;R!1+^7+3162$lo;R+3D8GF!2,_G1-^IRN$x;R!2+^I+C+31!1'd>#11$e';R+C$s;R+3-1RN$~R+1142I-^7RN$x;R!1+^7+31!2'c\#4#22$lo';R+3-^7RN$x;R!1+^7+31!2'd<#5#32$hi';R+3-1RN$~R+11:2-^7RN$plain;R!1+^701E2$p;R0<=E@I!1'c[J!1'dA#2!1'd;J!1'dB#2!3+_71!2'd?J#1!2'd@#2#1").
Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 (k : list kentry) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+^I+3+3!1+^7+3$k;R!1+2+W$e;R+C-^7RN$x;R!1+^701!2'd@#2#12$p;R0-^IRN$p;R!2+^I+3+31#11$lo;R+3$z;R+3!2,^8+3#2!1,[+3").

Definition xlo2B (bc : bctx) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+^I+3+3!1+^7+3$bc;R+a3$e;R+C-^7RN$x;R!1+^701!2'd?#2#12$p;R0-^IRN$p;R!2+^I+3+31#11$lo;R+3$z;R+3!2,^8+3#2!1,[+3").

Lemma xlo2B_eqf : forall fk, xlo2B (mkbc fk) = xlo2 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!1+^7+3!2+^I+3+3%e;R+C!1+^71-^IRN$p;R!2+^I+3+30#11$lo;R+3$z;R+3!2,^8+3#2!1,[+3!1'`W#2$fk;R!1+2+W!5'aE+C0!1'dC!1'`W#1!1'dD#1$x;R+Cvd!6'_F2!1'd@#2$o;R2!3+_70-^7RN$x;R!1+^710!1#1#22$p;R134-^7RN$x;R!1+^710!2'd@#3#22$p;R134!2,_G0-^7RN$x;R!1+^710!2'd@#2#12$p;R134!1'd?5!1'dE#2!3+_70!2'dC5#1!2'dD#2#1").
Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 (k : list kentry) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+^I+3+3!1+^7+3$k;R!1+2+W$e;R+C-^7RN$x;R!1+^701!2'd@#2#12$p;R0-^IRN$p;R!2+^I+3+31#11$z;R+3$hi;R+3!2,^8+3#1!1,[+3").

Definition xhi2B (bc : bctx) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+^I+3+3!1+^7+3$bc;R+a3$e;R+C-^7RN$x;R!1+^701!2'd?#2#12$p;R0-^IRN$p;R!2+^I+3+31#11$z;R+3$hi;R+3!2,^8+3#1!1,[+3").

Lemma xhi2B_eqf : forall fk, xhi2B (mkbc fk) = xhi2 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!1+^7+3!2+^I+3+3%e;R+C!1+^71-^IRN$p;R!2+^I+3+30#11$z;R+3$hi;R+3!2,^8+3#1!1,[+3!1'`W#2$fk;R!1+2+W!5'aE+C0!1'dF!1'`W#1!1'dG#1$x;R+Cvd!6'_F2!1'd@#2$o;R2!3+_70-^7RN$x;R!1+^710!1#1#22$p;R134-^7RN$x;R!1+^710!2'd@#3#22$p;R134!2,_G0-^7RN$x;R!1+^710!2'd@#2#12$p;R134!1'd?5!1'dE#2!3+_70!2'dF5#1!2'dG#2#1").
Qed.
#[local] Hint Rewrite xhi2B_eqf : bceq.



(* [comment removed for export] *)
Definition fact_ok (k : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi =>
      match xlo2 k e, xhi2 k e with
      | Some l, Some h => Z.leb lo l && Z.leb h hi
      | _, _ => false
      end
  | KAlign e m => Z.ltb 0 m && Z.eqb m (2 ^ (Z.log2 m)) && Z.leb (Z.log2 m) (ealign k e)
  | KDisj (SA b1 k1) n1 (SA b2 k2) n2 => ranges_apart_x k b1 k1 n1 b2 k2 n2
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint kread_bytes (fuel : nat) (k : list kentry) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZ k b off 1, kread_bytes f k b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Fixpoint kread_bytesB (bc : bctx) (fuel : nat) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZB bc b off 1, kread_bytesB bc f b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Lemma kread_bytesB_eqf' : forall fk fuel, kread_bytesB (mkbc fk) fuel = kread_bytes fuel fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SB0!1+2+3!1+^70%off;R+31%b;R+C2!1'`W#3!3+_73!2'dI4#1!2'dJ#1#3!1,_=#2!1,_=#3}1!1,c?,dL!2'^S#39!2,^80!3,_C+3#2#1!1,[0-^7RN$x;R!1+^701!4'dJ#6#8#4:2$rest;R0;<-^7RN$x;R!1+^7+31!4'bV#7#3#282$z;R+3=<%b;R+C%off;R+3%n;R+5!1+^7+3!1'`W#6!1,_=#4$fk;R!1+2+W$fuel;R+5!4'dH$fuel;R+55!5'aE+C2!2'dI!1'`W#2,dK!2'dJ,dK#2$x;R+C!5'aE+31!3'dI4,dK#1!3'dJ,dK#3#1$x0;R+3!2,_G1!4'dJ,dK#4#2#1$f;R+5$IH;R5!5'aE+C2!2'dI!1'`W#46!2'dJ6#4$x;R+C!5'aE+31!3'dI!1'`W#57#1!3'dJ7#5#1$x0;R+3vd!6'_F3!2'dJ#4#6$o;R3!3+_71-^7RN$x;R!1+^7+31!4'bU!1'`W#7#3#282$z;R+3-^7RN$x;R!1+^701!2#2#4:2$rest;R0;<<>!6'_F?!1'bV#6$o;R?!3+_71-^7RN$x;R!1+^7+31!3#1#3#282$z;R+3=<>!2,_G1-^7RN$x;R!1+^7+31!4'bV#6#2#182$z;R+3-^7RN$x;R!1+^701!4'dJ#5#7#3!2'^S#292$rest;R0;<<!1'bU@!1'dM#6!2'dI@#4#3!3+_71!4'dI@A#2#1!4'dJA#6#2#1#1").
Qed.
Lemma kread_bytesB_eqf : forall fk, kread_bytesB (mkbc fk) = (fun fuel => kread_bytes fuel fk).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$fk;R!1+2+W!5'aE+5%b;R+C%off;R+3!1+^7!1+2+3!1'dI!1'`W#1$fuel;R+5!2'dJ#1#2$fuel;R+5!2'dN#2#1").
Qed.
#[local] Hint Rewrite kread_bytesB_eqf' kread_bytesB_eqf : bceq.


Definition node_join (cs : acs) (b : expr) (off : Z) (n : nat) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S50!1+^7+A}1!1'^5#4!1+2+3!1,[+A$cs;R+A$b;R+C$off;R+3$n;R+5-1RN$~R+10!2'^P!2'^P!2'`?1#1!2'`?#1}8!4'cF2#3#2!1,F!1'^T#12-^7RN$x;R!1+^730!4'dJ#12#3#22$bs;R3!2,^8+A!2'dO#5!3,_C+W!3,`D!2,`0#4#3#2!1,F!1'dP#1!1,Y+W44").

Fixpoint drop_ixs (ixs : list nat) (i : nat) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if existsb (Nat.eqb i) ixs then drop_ixs ixs (S i) r else K :: drop_ixs ixs (S i) r
  end.

(* [comment removed for export] *)
Definition residue_fact (k : list kentry) (e ne : expr) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1 k e', xhi1 k e' with
    | Some lo', Some _ => if Z.leb s lo' then [KRange (esub e' ne) 0 s] else []
    | _, _ => []
    end
  else [].

Definition node_fresh (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S60!1+2+W|10;!1+^7+A!1'dS#8}1!1,[+A$cs;R+A$r;R+5$logc;R+3$base;R!1+^7+C&k;R!1'^5#40&c;R!2'dQ!1,c?1#3+3&b;R-^7RN$base;R!1+^7+C+C#32$b;R+C#1!1,F,G+C&e;R!2'dR!2'^>#7#6#1+C-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^N,dK#7!2'^N#7}P!2'^R,G#6!2'^R#6!1,c?|508;!2'^R#6!2'cS#4#1!2'`Q3#2!2'`Q3#1!1'`T#82-^7RN$x;R!1+^7+32!2'dD#4#12$lo;R+3-^7RN$x;R!1+^7+32!2'dG#5#22$hi;R+3&v;R!1'dS#:+5&ne;R!2'dT#6!1,_R#1+C&kres;R!3'dU#8#5#10&kf;R!3,_C+W!3,`J!1,_R#3!2'dV!2'aD!2'^S#5#8!1,c?,dL#8!2'dV#4#8!3,_C+W!3,`J!2'dR#6#2,G,G#10!2,^8+A!2'dW!3'dX!2'dO#>#1#=!2'dY#8#34555").

(* [comment removed for export] *)
Definition node_droprange (cs : acs) (b n : expr) : acs :=
  let '(bb, bk) := split_lit b in set_kn cs (kn_havoc (kn cs) bb bk n).

(* [comment removed for export] *)
Definition node_bump (cs : acs) (m : nat) : option acs :=
  if Nat.leb (nxt cs) m then Some (bump cs (m - nxt cs)) else None.

(* [comment removed for export] *)
Definition node_havoc (cs : acs) (rs : list nat) : option acs :=
  if (fresh_ok cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool then
    let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (sr_fresh (s_regs ss) rs (s_next ss)) (s_know ss) (s_next ss + length rs)))
  else None.

(* [comment removed for export] *)
Fixpoint esize (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  | _ => 1%nat
  end.
Definition bigb (K : nat) (e : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$K;R+5$e;R+C!2'^N#2!1'dZ#1").
Fixpoint kn_bigsubst (K : nat) (k : list kentry) (nx : nat) : list kentry * nat :=
  match k with
  | [] => ([], 0%nat)
  | KWord a w v :: r =>
      if bigb K v then let '(r', c) := kn_bigsubst K r (S nx) in (KWord a w (EVar nx) :: r', S c)
      else let '(r', c) := kn_bigsubst K r nx in (KWord a w v :: r', c)
  | x :: r => let '(r', c) := kn_bigsubst K r nx in (x :: r', c)
  end.
Definition node_havocbig (cs : acs) (K : nat) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40}1!1+^7+A!1+2+W!1,[+A$cs;R+A$K;R+5&rs;R!3'^Y+5$r;R+5!2'd[#2!2'^>#3#1!2'd\0}O!1+2+5-^7RN$x;R!1+^7+A1!2'e0#3#12$cs1;R+A-1RN$~R+11!1'`T#12&nx1;R!1'dS#1+5-^IRN$x;R!2+^I2+51!3'e1#4!1'^5#2#11$k';R2$c;R+5!2,^8+A!2'^0#4!4'^1!1'cU#4!1'D!1'E#4#2!2'^6#3#133").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside k b off n (am_base m) 0 (am_len m)) ms.

Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S00$bc;R+a3$ms;R!1+2+8$kinds;R!1+2+e2$b;R+C$off;R+3$n;R+C!3'e3+8$m;R+8!2'^P!2'^P!1'>!1'?#1!3'^O+e2!1'9!1':#1#5!7'c1#7#4#3#2!1'^G#1,G!1'^H#1#5").

Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S=0!1+2+8!1+2+e2!1+^7+8%n;R+C2%off;R+33%b;R+C4%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1!1'>!1'?#1!1'9!1':#1!2'^P7!3'^O+e28#6!1'^G#1!1'^H#1!1'`W#6$fk;R!1+2+W!5'aE0%kinds;R15!1'e4!1'`W#1!1'e5#1$x;R0!5'aE15!2'e4!1'`W#2#1!2'e5#2#1$x0;R1!5'aE+C4!3'e4!1'`W#3#2#1!3'e5#3#2#1$x1;R+C!5'aE+33!4'e4!1'`W#4#3#2#1!4'e5#4#3#2#1$x2;R+3!5'aE+C2!5'e4!1'`W#5#4#3#2#1!5'e5#5#4#3#2#1$x3;R+Cvd!6'_F6!1'c3#6$b;R6!3+_72!3'e3+8$m;R+8!2'^P9!6#2#5#4#3:,G;#6!3'e3+8$m;R+8!2'^P9!7'c3#8#5#4#3:,G;#6!2,_G2!3'e3+8$m;R+8!2'^P!2'^P7!3'^O+e28#5!7'c3#7#4#3#2:,G;#5!1'c1<!1'c5#6!3+_72!6'e4<#5#4#3#2#1!6'e5#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!2+^I+C+3!1,c?|11;$bc;R+a3$b;R+C$n;R+C-^IRN$x;R!2+^I+C+3!2+^I0+C!1'^W!2'dY!3'e6#3#21!1,F!1'e7/A;1$sb;R+C$sk;R+3!4,cJ0+C!4,cJ+C+3#2#1!3'e6#5#31").

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S70!2+^I+C+3!2+^I0+C%a;R+C%s;R+3+C!1,c?|11;!1,F!1'e7/A;!4,cJ+C+3#2#1!1'`W#3$fk;R!1+2+W!5'aE+C%n;R+C1!1'e8!1'`W#1!1'e9#1$x;R+C!5'aE+C1!2'e8!1'`W#2#1!2'e9#2#1$x0;R+Cvd!6'_F2!1'e:#3$e;R2!3+_71-^IRN$x;R!2+^I+C+31!1'^W!2'dY!2#1#3341$sb;R+C$sk;R+3!4,cJ0+C5!2#3#43-^IRN$x;R!2+^I+C+31!1'^W!2'dY!3'e:#4#3341$sb;R+C$sk;R+3!4,cJ0+C5!3'e:#6#43!2,_G1-^IRN$x;R!2+^I+C+31!1'^W!2'dY!3'e:#3#2341$sb;R+C$sk;R+3!4,cJ0+C5!3'e:#5#33!1'e66!1'e;#3!3+_71!3'e86#2#1!3'e9#3#2#1").
Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  match find_containing k ms [KRWLAZY] sb sk sn with
  | Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
  | None => []
  end.

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S40!2+^I+C+3!1+2+W!2,`0#3#2!1,Y+W$bc;R+a3$ms;R!1+2+8$b;R+C$n;R+C-^IRN$x;R!2+^I0+C1!3'e8#4#2#11$p;R0$sn;R+C-^IRN$p;R!2+^I+C+31#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+81!6'e4#8#7!3,_C+e2,e<!1,Y+e2#2#1#32$a;R+8!3,_C+W!2,`K2#4!3,_C+W!2,`E2#433").

Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S=0!1+2+W!1+2+8%n;R+C0!2+^I+C+3%b;R+C%n;R+C!2+^I3+C!3,_C+e2,e<!1,Y+e2!2,`0#3#2!1,Y+W!3,_C+W!2,`K6#4!3,_C+W!2,`E6#47!3'e9#5#3#2-^IRN$x;R!2+^I3+C091$p;R3$sn;R+C-^IRN$p;R!2+^I+C+30#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+80!6'e5#9#85#2#1#32$a;R+887%ms;R1%kinds;R!1+2+e2%b;R+C%off;R+3%n;R+C!1+^7+8!1'`W#4$fk;R0!5'aE1%b;R+C2!1'e=!1'`W#1!1'e>#1$x;R1!5'aE+C2!2'e=!1'`W#2#1!2'e>#2#1$x0;R+C!5'aE+C0!3'e=!1'`W#3#2#1!3'e>#3#2#1$x1;R+Cvd!6'_F4!1'e9#4$p;R4!3+_70-^IRN$x;R!2+^I3+C0!2#1#3#21$p;R3$sn;R+C-^IRN$p;R!2+^I+C+30#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+80!6'e4!1'`W#9#85#2#1#32$a;R+887:!6'_F;!1'e5#4$o;R;!3+_70-^IRN$x;R!2+^I3+C091$p;R3$sn;R+C-^IRN$p;R!2+^I+C+30#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+80!5#5#85#2#1#32$a;R+887:!2,_G0-^IRN$x;R!2+^I3+C0!3'e9#4#2#11$p;R3$sn;R+C-^IRN$p;R!2+^I+C+30#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+80!6'e5#8#75#2#1#32$a;R+887!1'e4<!1'e?#4!1'e8<!1'e@#4!3+_70!4'e=<#3#2#1!4'e>#4#3#2#1").
Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)
Definition vis_cost (nhi : Z) : Z := nhi + nhi / 8 + 16384.

(* [comment removed for export] *)
Definition vis_add_ref (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k0 b n in
  match xhi k0 n with
  | Some nhi =>
  if (Z.leb 3 (ealign k0 b) && Z.leb 3 (ealign k0 n) && flat_x k0 bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p)
                           && ranges_apart_x k0 bb bk n pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts k0 (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.
(* [comment removed for export] *)
Definition vis_add (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in let bc := mkbc k0 in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc n with
  | Some nhi =>
  if (Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p)
                           && ranges_apart_xB bc bb bk n pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^Z0!1+2+W%e;R+C+3!1'^5#4!1+^7+A!1'^W#4!2+^I+C+3!1'^5#7!3'e8!1'`W6#6#5!1'^5#;!1'`W8!2'c89#9!1,c?|11;!1'^5#<!1'`W<!1'dS#<!2'`Q>#;!2'`Q>#:!2+^I+C+C!1'^W!3'^J+C+C#1!1'^5#?!1'`WC!3'^K+C+C#3!4'cED#2#1E!7'aBD#:#9#=#2#1E!7'aBD#6#5#7#2#1E!1'Q#<!1'R#<!1'P#<!1'S#<!1'eA#1!2'^R!2'^S!2'^SKLM/LIMIT;!1'cU#<!1'D!1'E#<!1'M#<!1'N#<!1'O#<!3,_CA!4,cJ+C+C#;#:I!2'^SLM!1'T#<!1'U#<!1'V#<!2,^8+A!;,L!4'^1OP!3'^4+W!4'e==Q#;#:#9>QRSKTJUVWX!1,[+A!3'e96#6#5!2'^P!2'^R;!2'cS<#;!2'^R;!2'cS<#:!2'^P!2'^P!2'^P\!4'cF<#7#6#:?@!4'cFC#2#1E!7'aHC#6#5#7#2#1E!2'^P!2'^P!2'^P^0!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P!2'^P^1!7'aHC#:#9#=#2#1E^2I!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P^1^2JN-1RN$~R+13^32!2,^8+A!;,L!4'^1OP!3'^4+W!4'e><Q#;#:#9>QRSKTJUVWXZ-^IRN$x;R!2+^I+C+3341$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C3[1$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33!2'c98#92$nhi;R+3^4Z%b;R+C%off;R+3%n;R+C+1!3#;#2#1E%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1!6#;#6#5#7#2#1E%ms;R!1+2+8%b;R+C%n;R+C0%b;R+C%n;R+C!2+^I5+C%e;R+C!1+^7+3!1'^W#3!1'^5#6!1'^5#:!1'dS#;!2'`Q^@#:!2'`Q^@#9!1'^5#>!4'cF^C#2#1E!7'aH^C#6#5#7#2#1E!1'Q#;!1'R#;!1'P#;!1'S#;!2'^R!2'^S!2'^S^H^IM/LIMIT;!1'cU#;!1'D!1'E#;!1'M#;!1'N#;!1'O#;!3,_CA!4,cJ+C+C#:#9^F!2'^S^IM!1'T#;!1'U#;!1'V#;-^IRN$x;R!2+^I+C+33^=1$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C3!3'e9^>#5#41$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33!2'c9^?#82$nhi;R+3-1RN$~R+13!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^R;!2'cS8#:!2'^R;!2'cS8#9!4'cF8#7#6#9^A^B!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P!2'^P^D!7'aH^C#:#9#<#2#1E^E^F!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P^D^E^G^J2!2,^8+A!;,L!4'^1^K^L!3'^4+W!4'e>8^M#:#9#8^@^M^N^O^H^P^G^Q^R^S^TZZ!1'`W2!1'`W^C!4'cE^W#2#1E!7'aB^W#6#5#7#2#1E$cs;R+A$b;R+C$n;R+C$k;R0vdvd!6'_F1!1'cS2$z;R1!3+_73-^IRN$x;R!2+^I+C+3341$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C371$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33:2$nhi;R+3-1RN$~R+13!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^R;!1#8#;!2'^R;!1#8#:!4'cE=#7#6#:?@!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P!2'^PFGHI!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^PFHJN2YZZ^5!6'_F^6!1'cF2$b;R^6!3+_73-^IRN$x;R!2+^I+C+3341$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C371$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33:2$nhi;R+3-1RN$~R+13!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P\!3#8#7#6#:?@!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P!2'^P^7GHI!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P^7HJN2YZZ^5!6'_F^8!1'aH2$b;R^8!3+_73-^IRN$x;R!2+^I+C+3341$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C371$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33:2$nhi;R+3-1RN$~R+13!2'^P!2'^P!2'^P^0!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P!2'^P^1!6#;#:#9#=#2#1E^9I!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P^1^9JN2YZZ^5!6'_F^:!1'e>2$l;R^:!3+_73-^IRN$x;R!2+^I+C+3341$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C371$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33:2$nhi;R+3-1RN$~R+13^32!2,^8+A!;,L!4'^1OP!3'^4+W!3#8Q#;#:#9>QRSKTJUVWXZZ^5!6'_F^;!1'e92$p;R^;!3+_73-^IRN$x;R!2+^I+C+3341$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C3!2#3#6#51$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33:2$nhi;R+3^4Z^5!6'_F^<!1'c92$o;R^<!3+_73-^IRN$x;R!2+^I+C+3341$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C3[1$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33!1#7#92$nhi;R+3^4Z^5!2,_G3^U!1'c8^V!1'c:2!1'e8^V!1'e@2!1'e=^V!1'eB2!1'aB^V!1'aI2!1'cE^V!1'eC2!1'cP^V!1'cT2!3+_73-^IRN$x;R!2+^I+C+33^=1$bb;R+C$bk;R+3-^IRN$x;R!2+^I5+C3!3'e8!1'`W^>#5#41$p;R5$sn;R+C-^IRN$p;R!2+^I+C+33#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33!2'c8!1'`W^?#82$nhi;R+3-1RN$~R+13!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^R;!2'cP9#:!2'^R;!2'cP9#9!4'cE9#7#6#9^A^B!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P!2'^P^X!7'aB^W#:#9#<#2#1E^Y^F!3'=A$p;RA-^IRN$x;R!2+^I+C+3+1B1$pb;R+C$pk;R+3!2'^P^X^Y^G^J2!2,^8+A!;,L!4'^1^K^L!3'^4+W!4'e=9^M#:#9#8^@^M^N^O^H^P^G^Q^R^S^TZZ^U!3+_73!4'eD#4#3#2#1!4'eE#4#3#2#1").
Qed.


(* [comment removed for export] *)
Fixpoint find_disj (k : list kentry) (b1 b2 : expr) : option (expr * Z * expr * expr * Z * expr) :=
  match k with
  | [] => None
  | KDisj (SA c1 o1) n1 (SA c2 o2) n2 :: r =>
      if (expr_eqb c1 b1 && expr_eqb c2 b2)%bool then Some (c1, o1, n1, c2, o2, n2)
      else if (expr_eqb c1 b2 && expr_eqb c2 b1)%bool then Some (c2, o2, n2, c1, o1, n1)
      else find_disj r b1 b2
  | _ :: r => find_disj r b1 b2
  end.
(* [comment removed for export] *)
Definition disj_side_fact (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : option kentry :=
  match xlo2 k nA, base_range k cB with
  | Some n, Some (_, bhi) => if (Z.leb 0 n && Z.leb n (bhi + oB))%bool then Some (KRange (esub (eaddz cB oB) (eaddz cA oA)) n (bhi + oB)) else None
  | _, _ => None
  end.
Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (acs * acs) := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S90!2+^I+C+3!2+^I0+C!2+^I1+C!2+^I2+3!2+^I3+C!2+^I+A+A!1+^75!1,Y+W!1,[5$cs;R+A$b1;R+C$b2;R+C&k;R!1'^5#3!1+2+W-^7RN$x;R!1+^746!3'eF#1#3#22$p;R4-^IRN$p;R!2+^I3+C6#11$p0;R3$n2;R+C-^IRN$p0;R!2+^I2+36#21$p1;R2$o2;R+3-^IRN$p1;R!2+^I1+C6#21$p2;R1$c2;R+C-^IRN$p2;R!2+^I0+C6#21$p3;R0$n1;R+C-^IRN$p3;R!2+^I+C+36#21$c1;R+C$o1;R+3-1RN$x;R+16!4'cF#<#2#1#32-1RN$x;R+16!4'cF#<#5#7#92-^7RN$x;R!1+^7+W6!6'eG#<#2#1#3#5#72$K1;R+W-^7RN$x;R!1+^7+W6!6'eG#=#6#8#:#3#22$K2;R+W!2,^85!4,cJ+A+A!2'dO#A!3,_C+W#27!2'dO#A!3,_C+W#1788888").

(* [comment removed for export] *)
Definition node_shdisj_ref (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_of k b1 n1 in let '(sb2, sk2, sn2) := shadow_of k b2 n2 in
  if (Z.leb 3 (ealign k b1) && Z.leb 3 (ealign k n1) && Z.leb 3 (ealign k b2) && Z.leb 3 (ealign k n2)
      && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
      && match xhi k b1, xhi k n1, xhi k b2, xhi k n2 with
         | Some h1, Some m1, Some h2, Some m2 => Z.leb (h1 + m1) (2 ^ 47) && Z.leb (h2 + m2) (2 ^ 47)
         | _, _, _, _ => false end
      && ranges_apart_x k c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.
(* [comment removed for export] *)
Definition node_shdisj (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_ofB bc b1 n1 in let '(sb2, sk2, sn2) := shadow_ofB bc b2 n2 in
  if (Z.leb 3 (ealignB bc b1) && Z.leb 3 (ealignB bc n1) && Z.leb 3 (ealignB bc b2) && Z.leb 3 (ealignB bc n2)
      && flat_xB bc c1 o1 n1 && flat_xB bc c2 o2 n2 && flat_xB bc sb1 sk1 sn1 && flat_xB bc sb2 sk2 sn2
      && match xhiB bc b1, xhiB bc n1, xhiB bc b2, xhiB bc n2 with
         | Some h1, Some m1, Some h2, Some m2 => Z.leb (h1 + m1) (2 ^ 47) && Z.leb (h2 + m2) (2 ^ 47)
         | _, _, _, _ => false end
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.

Lemma node_shdisj_eq : forall cs b1 n1 b2 n2, node_shdisj cs b1 n1 b2 n2 = node_shdisj_ref cs b1 n1 b2 n2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^00%e;R+C+3!1'^5#5!1+^7+A!1'^W#5!2+^I+C+3!1'^5#:!3'e8!1'`W5#9#8!1'^5#>!3'e8!1'`W7#;#:!1,c?|11;!1#=#A!1'^5#B!1'`W;!1'^5#C!1'`W=!1'^5#D!1'`W?!1'^5#E|10;!2'dQ!1,c?B!1,c?|50f;!2'^P!2'^R!2'^S#4#3C!2'^R!2'^S#2#1C-^7RN$x;R!1+^7+3+1!2'c8<#A2$h1;R+3-^7RN$x;R!1+^7+3+1!2'c8>#A2$m1;R+3-^7RN$x;R!1+^7+3+1!2'c8@#A2$h2;R+3-^7RN$x;R!1+^7+3+1!2'c8!1'`WA#A2$m2;R+3D,6,6,6,6!7'aB<#<#;#@#:#9#>!3,_C+W!4,`L!2,`0#6#5#7!2,`0#2#1#3!1,Y+W!2,^8+A!2'dO#BG!1,[+A!3'e95#9#8!3'e97#;#:!2'^P!2'^P!2'^P!2'^R9!2'cS;#A!2'^R9!2'cS;#@!2'^R9!2'cS;#?!2'^R9!2'cS;#>!2'^P!2'^P!2'^P!2'^PL!4'cF;#<#;#@!4'cF;#:#9#>!4'cF;#6#5#7!4'cF;#2#1#3!7'aH;#<#;#@#:#9#>-^IRN$x;R!2+^I+C+3231$c1;R+C$o1;R+3-^IRN$x;R!2+^I+C+3231$c2;R+C$o2;R+3-^IRN$x;R!2+^I4+C2J1$p;R4$sn1;R+C-^IRN$p;R!2+^I+C+32#21$sb1;R+C$sk1;R+3-^IRN$x;R!2+^I4+C2K1$p;R4$sn2;R+C-^IRN$p;R!2+^I+C+32#21$sb2;R+C$sk2;R+3-1RN$~R+12!2'^P!2'^PM-^7RN$x;R!1+^7+3+1!2'c9;#A2$h1;R+3-^7RN$x;R!1+^7+3+1!2'c9=#A2$m1;R+3-^7RN$x;R!1+^7+3+1!2'c9?#A2$h2;R+3-^7RN$x;R!1+^7+3+1!2'c9A#A2$m2;R+3D,6,6,6,6N2HI%b;R+C%off;R+3%n;R+C+1%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1!2'^PME%b;R+C%n;R+C!2+^I4+C%e;R+C!1+^7+3!1'^W#4!1'^5#9!1'^5#=!1'^5#A!2,^8+A!2'dO#AG-^IRN$x;R!2+^I+C+32U1$c1;R+C$o1;R+3-^IRN$x;R!2+^I+C+32U1$c2;R+C$o2;R+3-^IRN$x;R!2+^I4+C2!3'e9V#8#71$p;R4$sn1;R+C-^IRN$p;R!2+^I+C+32#21$sb1;R+C$sk1;R+3-^IRN$x;R!2+^I4+C2!3'e9W#:#91$p;R4$sn2;R+C-^IRN$p;R!2+^I+C+32#21$sb2;R+C$sk2;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^R9!2'cSX#@!2'^R9!2'cSX#?!2'^R9!2'cSX#>!2'^R9!2'cSX#=!4'cFX#<#;#?!4'cFX#:#9#=!4'cFX#6#5#7!4'cFX#2#1#3-^7RN$x;R!1+^7+3+1!2'c9X#@2$h1;R+3-^7RN$x;R!1+^7+3+1!2'c9;#@2$m1;R+3-^7RN$x;R!1+^7+3+1!2'c9=#@2$h2;R+3-^7RN$x;R!1+^7+3+1!2'c9?#@2$m2;R+3D,6,6,6,6!7'aHX#<#;#?#:#9#=2YI!1'`W1!1'`WX$cs;R+A$b1;R+C$n1;R+C$b2;R+C$n2;R+Cvdvd!6'_F0!1'cS1$z;R0!3+_72-^IRN$x;R!2+^I+C+3231$c1;R+C$o1;R+3-^IRN$x;R!2+^I+C+3231$c2;R+C$o2;R+3-^IRN$x;R!2+^I4+C261$p;R4$sn1;R+C-^IRN$p;R!2+^I+C+32#21$sb1;R+C$sk1;R+3-^IRN$x;R!2+^I4+C281$p;R4$sn2;R+C-^IRN$p;R!2+^I+C+32#21$sb2;R+C$sk2;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^R9:!2'^R9!1#=#@!2'^R9!1#=#?!2'^R9!1#=#>!4'cE<#<#;#@!4'cE<#:#9#>!4'cE<#6#5#7!4'cE<#2#1#3EF2HIO!6'_FP!1'cF1$b;RP!3+_72-^IRN$x;R!2+^I+C+3231$c1;R+C$o1;R+3-^IRN$x;R!2+^I+C+3231$c2;R+C$o2;R+3-^IRN$x;R!2+^I4+C261$p;R4$sn1;R+C-^IRN$p;R!2+^I+C+32#21$sb1;R+C$sk1;R+3-^IRN$x;R!2+^I4+C281$p;R4$sn2;R+C-^IRN$p;R!2+^I+C+32#21$sb2;R+C$sk2;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^PL!3#=#<#;#@!3#=#:#9#>!3#=#6#5#7!3#=#2#1#3EF2HIO!6'_FQ!1'aH1$b;RQ!3+_72-^IRN$x;R!2+^I+C+3231$c1;R+C$o1;R+3-^IRN$x;R!2+^I+C+3231$c2;R+C$o2;R+3-^IRN$x;R!2+^I4+C261$p;R4$sn1;R+C-^IRN$p;R!2+^I+C+32#21$sb1;R+C$sk1;R+3-^IRN$x;R!2+^I4+C281$p;R4$sn2;R+C-^IRN$p;R!2+^I+C+32#21$sb2;R+C$sk2;R+3-1RN$~R+12!2'^PR!6#=#<#;#@#:#9#>2HIO!6'_FS!1'e91$p;RS!3+_72-^IRN$x;R!2+^I+C+3231$c1;R+C$o1;R+3-^IRN$x;R!2+^I+C+3231$c2;R+C$o2;R+3-^IRN$x;R!2+^I4+C2!2#5#9#81$p;R4$sn1;R+C-^IRN$p;R!2+^I+C+32#21$sb1;R+C$sk1;R+3-^IRN$x;R!2+^I4+C2!2#9#;#:1$p;R4$sn2;R+C-^IRN$p;R!2+^I+C+32#21$sb2;R+C$sk2;R+3-1RN$~R+12!2'^PRN2HIO!6'_FT!1'c91$o;RT!3+_72-^IRN$x;R!2+^I+C+3231$c1;R+C$o1;R+3-^IRN$x;R!2+^I+C+3231$c2;R+C$o2;R+3-^IRN$x;R!2+^I4+C2J1$p;R4$sn1;R+C-^IRN$p;R!2+^I+C+32#21$sb1;R+C$sk1;R+3-^IRN$x;R!2+^I4+C2K1$p;R4$sn2;R+C-^IRN$p;R!2+^I+C+32#21$sb2;R+C$sk2;R+3-1RN$~R+12!2'^P!2'^PM-^7RN$x;R!1+^7+3+1:2$h1;R+3-^7RN$x;R!1+^7+3+1!1#>#A2$m1;R+3-^7RN$x;R!1+^7+3+1!1#?#A2$h2;R+3-^7RN$x;R!1+^7+3+1!1#@#A2$m2;R+3D,6,6,6,6N2HIO!2,_G2Z!1'c8[!1'c:1!1'e8[!1'e@1!1'aB[!1'aI1!1'cE[!1'eC1!1'cP[!1'cT1!3+_72-^IRN$x;R!2+^I+C+32U1$c1;R+C$o1;R+3-^IRN$x;R!2+^I+C+32U1$c2;R+C$o2;R+3-^IRN$x;R!2+^I4+C2!3'e8!1'`WV#8#71$p;R4$sn1;R+C-^IRN$p;R!2+^I+C+32#21$sb1;R+C$sk1;R+3-^IRN$x;R!2+^I4+C2!3'e8!1'`WW#:#91$p;R4$sn2;R+C-^IRN$p;R!2+^I+C+32#21$sb2;R+C$sk2;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^R9!2'cP\#@!2'^R9!2'cP\#?!2'^R9!2'cP\#>!2'^R9!2'cP\#=!4'cE\#<#;#?!4'cE\#:#9#=!4'cE\#6#5#7!4'cE\#2#1#3-^7RN$x;R!1+^7+3+1!2'c8\#@2$h1;R+3-^7RN$x;R!1+^7+3+1!2'c8<#@2$m1;R+3-^7RN$x;R!1+^7+3+1!2'c8>#@2$h2;R+3-^7RN$x;R!1+^7+3+1!2'c8@#@2$m2;R+3D,6,6,6,6!7'aB\#<#;#?#:#9#=2YIZ!3+_72!5'eH#5#4#3#2#1!5'eI#5#4#3#2#1").
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_len_ref (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in
      match xlo k le, xhi k le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealign k le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.
(* [comment removed for export] *)
Definition mmap_len (cs : acs) : option (expr * Z * Z) :=
  match reg_lit cs 11 with
  | Some len => if Z.ltb 0 len then Some (ELit (page_up len), page_up len, page_up len) else None
  | None =>
      let le := reg cs 11 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match xloB bc le, xhiB bc le with
      | Some lo, Some hi =>
          if (Z.ltb 0 lo && Z.leb 12 (ealignB bc le) && Z.leb hi (2 ^ 46))%bool then Some (le, lo, hi) else None
      | _, _ => None
      end
  end.

Lemma mmap_len_eq : forall cs, mmap_len cs = mmap_len_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SP0%e;R+C+3!1'^5#1!2+^I+C+3!2+^I2+3!1+^73};!2'eJ#25!1'eK#1!1,[3-1RN$~R+14!2'aC,G#12!2,^83!4,cJ2+3!4,cJ+C+3!1,F7778!1'^5#2!1'`W:!2'^>#25!2'c0;<!1'^5#3!1'`W>!2'^>#35!2'aC,G#2!1,c?|34;!2'^>#45|10;!2'^R#1!2'dQ!1,c?D!1,c?|50e;!2,^83!4,cJ2+3!4,cJ+C+3C#2#1-1RN$~R+14!2'^P!2'^PA!2'^RB!2'cS!1'^5#4CE2F8-^7RN$x;R!1+^7+34!2'c9>@2$hi;R+3G8-^7RN$x;R!1+^7+3462$len;R+39-^7RN$x;R!1+^7+34!2'c2:<2$lo;R+3H8%e;R+C!1+^7+3!2'eJ#15!2'^>#15!2,^83!4,cJ2+3!4,cJ+C+3@#2#1-^7RN$x;R!1+^7+34K2$len;R+39-^7RN$x;R!1+^7+34!2'c21L2$lo;R+3-^7RN$x;R!1+^7+34!2'c9:<2$hi;R+3-1RN$~R+14!2'^P!2'^PA!2'^RB!2'cS>@E2M888!1'`W1$cs;R+Avdvd!6'_F0!1'cS1$z;R0!3+_74-^7RN$x;R!1+^7+3462$len;R+39-^7RN$x;R!1+^7+34=2$lo;R+3-^7RN$x;R!1+^7+34!2'c8?@2$hi;R+3-1RN$~R+14!2'^P!2'^PA!2'^RB!1#3CE2F888I!6'_FJ!1'c91$o;RJ!3+_74-^7RN$x;R!1+^7+3462$len;R+39-^7RN$x;R!1+^7+34=2$lo;R+3-^7RN$x;R!1+^7+34!1#2@2$hi;R+3G88I!6'_FJ!1'c21$o;RJ!3+_74-^7RN$x;R!1+^7+3462$len;R+39-^7RN$x;R!1+^7+34!1#1<2$lo;R+3H8I!2,_G4N!1'c0O!1'c41!1'c8O!1'c:1!1'cPO!1'cT1!3+_74-^7RN$x;R!1+^7+34K2$len;R+39-^7RN$x;R!1+^7+34!2'c0OL2$lo;R+3-^7RN$x;R!1+^7+34!2'c8;<2$hi;R+3-1RN$~R+14!2'^P!2'^PA!2'^RB!2'cP?@E2M888N!3+_74!1'eL#1!1'eM#1").
Qed.


(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len
  end.

Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinsideB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.

Lemma inside_mapsB_eqf : forall fk, inside_mapsB (mkbc fk) = inside_maps fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S<0!1+2+8%len;R+C+1%off;R+31!5'eO#;#5#3#2#1!1'>!1'?#7!1'^G#7!1'^H#7!5'eO#<#6#4#3#2!2'^M!2'^P4!7'c3#<#4#3#25,G67%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1!1'`W#;!3,_C+8#6#5$fk;R!1+2+W!5'aE0%b;R+C2!1'eN!1'`W#1!1'eO#1$ms;R0!5'aE+C2!2'eN!1'`W#2#1!2'eO#2#1$b;R+C!5'aE+31!3'eN!1'`W#3#2#1!3'eO#3#2#1$off;R+3!5'aE+C+1!4'eN!1'`W#4#3#2#1!4'eO#4#3#2#1$len;R+C!8'_Y+8$ms;R0%b;R+C%off;R+3%len;R+C!3+_7+1!5'eN!1'`W#9#4#3#2#1!5'eO#9#4#3#2#1$b;R+C$off;R+3$len;R+C!2,_G+1!5'eO#8!1,Y+8#3#2#1$m;R+8$rest;R0$IH;R%b;R+C%off;R+3%len;R+C!3+_7+1!5'eN!1'`W#:#4#3#2#1!5'eO#:#4#3#2#1$b;R+C$off;R+3$len;R+Cvd!6'_F+13$b;R+1!3+_7+1!2'^M!2'^P4!7'c1!1'`W#<#4#3#25,G6#18!6'_F9!1'c3#;$b;R9!3+_7+1!2'^M!2'^P4!6#1#4#3#25,G678!2,_G+1!2'^M!2'^P!1'>!1'?#6!7'c3#;#3#2#1!1'^G#6,G!1'^H#63!1'c1:!1'c5#;!5'eN:#5#3#2#1!3#4#3#2#1!3+_7+1!5'eN:;#3#2#1!5'eO#;;#3#2#1#4#3#2#1").
Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (Z.leb CEIL (lo + off) && Z.leb (hi + off + lh) two64)                   (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
    | _, _ => false
    end) || inside_maps k ms b off len)%bool.

Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | Some lh, Some (lo, hi) =>
        (Z.leb CEIL (lo + off) && Z.leb (hi + off + lh) two64)                   (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
    | _, _ => false
    end) || inside_mapsB bc ms b off len)%bool.

Lemma safe_rangeB_eqf : forall fk, safe_rangeB (mkbc fk) = safe_range fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SD0!1+2+8%len;R+C+1%off;R+31%b;R+C2%ms;R03!2+^I+3+3!2'^S#2#7!2'^S!2'^S#1#7#4!1'c@/A;!1'cA/A;-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M!2'^P!2'^R'eR6!2'^R7'^:!2'^P!2'^R86!2'^R79-^7RN$x;R!1+^75+1!2'cD!1'`W#7#52$p;R5:,6!2'c9#6#2!5'eO#6#5#4#3#2!2'^M-^7RN$x;R!1+^7+3+1<2$lh;R+3-^7RN$x;R!1+^75+1!2'cG#7#52$p;R5:,6,6=%e;R+C!1+^7+3%e;R+C!1+^75!2'^S#2#6!2'^S!2'^S#1#6#4!1'`W#5$fk;R!1+2+W!5'aE03!1'eP!1'`W#1!1'eQ#1$x;R0!5'aE+C2!2'eP!1'`W#2#1!2'eQ#2#1$x0;R+C!5'aE+31!3'eP!1'`W#3#2#1!3'eQ#3#2#1$x1;R+3!5'aE+C+1!4'eP!1'`W#4#3#2#1!4'eQ#4#3#2#1$x2;R+Cvd!6'_F4!1'eO#5$b;R4!3+_7+1!2'^M-^7RN$x;R!1+^7+3+1!2'c8!1'`W#6#22$lh;R+3;,6!4#1#5#4#3#2>!6'_F?!1'c9#5$o;R?!3+_7+1!2'^M-^7RN$x;R!1+^7+3+1!1#1#22$lh;R+3;,6=>!6'_F@!1'cG#5$o;R@!3+_7+1!2'^M-^7RN$x;R!1+^7+3+1<2$lh;R+3-^7RN$x;R!1+^75+1!1#2#52$p;R5:,6,6=>!2,_G+1!2'^M-^7RN$x;R!1+^7+3+1!2'c9#5#12$lh;R+3-^7RN$x;R!1+^75+1!2'cG#6#42$p;R5-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M!2'^P!2'^R'eRA!2'^RB'^:!2'^P!2'^R8A!2'^RB9,6,6!5'eO#5#4#3#2#1!1'cDC!1'cH#5!1'c8C!1'c:#5!1'eNC!1'eS#5!3+_7+1!5'ePC#4#3#2#1!5'eQ#5#4#3#2#1").
Qed.
#[local] Hint Rewrite safe_rangeB_eqf : bceq.



Definition grant_keep_b (k : list kentry) (ms : list amap) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20-\RN$a;R+\+1#21$b;R+C$o;R+3!5'eQ#7#6#2#1#3-\RN$a;R+\+1#31$b;R+C$o;R+3!5'eQ#8#7#2#1#4$k;R!1+2+W$ms;R!1+2+8$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$o;R+3!2'^P!2'`?#4}8!5'eQ#8#7#2#1!1,F!1'^T#4$a;R+\$l;R+C0$a;R+\$l;R+C$k0;R+51$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C0$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+31$a;R+\$l;R+C0").

Definition grant_keep_bB (bc : bctx) (ms : list amap) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20-\RN$a;R+\+1#21$b;R+C$o;R+3!5'eP#7#6#2#1#3-\RN$a;R+\+1#31$b;R+C$o;R+3!5'eP#8#7#2#1#4$bc;R+a3$ms;R!1+2+8$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$o;R+3!2'^P!2'`?#4}8!5'eP#8#7#2#1!1,F!1'^T#4$a;R+\$l;R+C0$a;R+\$l;R+C$k;R+51$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C0$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+31$a;R+\$l;R+C0").

Lemma grant_keep_bB_eqf : forall fk, grant_keep_bB (mkbc fk) = grant_keep_b fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;0!1+2+8%ms;R0%b;R+C%off;R+3%len;R+C+1!2'`?#4}8!1,F!1'^T#4-\RN$a;R+\+1#21$b;R+C$o;R+3!4#5#7#2#1#3-\RN$a;R+\+1#31$b;R+C$o;R+3!4#6#8#2#1#4-\RN$a;R+\+1#21$b;R+C$o;R+3!5'eQ#8#7#2#1#3-\RN$a;R+\+1#31$b;R+C$o;R+3!5'eQ#9#8#2#1#4-\RN$a;R+\+1#21$b;R+C$o;R+3!5'eQ#7#6#2#1#3-\RN$a;R+\+1#31$b;R+C$o;R+3!5'eQ#8#7#2#1#4!1'`W#3$fk;R!1+2+W!5'aE0%K;R+W+1!1'eT!1'`W#1!1'eU#1$x;R0!5'aE+W+1!2'eT!1'`W#2#1!2'eU#2#1$x0;R+Wvd!6'_F1!1'eQ#3$b;R1!3+_7+1-WRN$K;R+W+1#2:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$o;R+3!2'^P2!4#6#8#2#13$a;R+\$l;R+C4$a;R+\$l;R+C$k;R+55$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C4$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+35$a;R+\$l;R+C4-WRN$K;R+W+1#2:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$o;R+3!2'^P2!5'eQ#9#8#2#13$a;R+\$l;R+C6$a;R+\$l;R+C$k0;R+57$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+37$a;R+\$l;R+C6!2,_G+1-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C-\RN$a;R+\+1#31$b;R+C$o;R+3!2'^P2!5'eQ#8#7#2#13$a;R+\$l;R+C8$a;R+\$l;R+C$k0;R+59$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C8$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$l;R+C$c;R+39$a;R+\$l;R+C8!1'eP:!1'eV#3!3+_7+1!3'eT:#2#1!3'eU#3#2#1").
Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter (k : list kentry) (ms : list amap) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$k;R!1+2+W$ms;R!1+2+8!1'eW!3'^Y+W!2'eU#2#1#2").

Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$bc;R+a3$ms;R!1+2+8!1'eW!3'^Y+W!2'eT#2#1!1'aR#2").

Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!1+2+W!1+2+8%ms;R1%K;R+W+1!2'eU#3#2!1'eW!3'^Y+W3#3!1'`W#2$fk;R0!5'aE10!1'eX!1'`W#1!1'eY#1$x;R1vd!6'_F2!1'eU#2$b;R2!3+_70!1'eW!3'^Y+W!1#1#2!1'aR!1'`W#34!6'_F0#2$l;R0!3+_70!1'eW!3'^Y+W3#14!2,_G0!1'eW!3'^Y+W!2'eU#2#1#2!1'aR5!1'aV#2!1'eT5!1'eZ#2!3+_70!2'eX5#1!2'eY#2#1").
Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.



(* [comment removed for export] *)
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.

Definition budget_ok (cs : acs) (extra : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$extra;R+3!2'^R!2'^S!2'^S!1'P#2!1'S#2#1/LIMIT;").

(* [comment removed for export] *)
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m with
                     | ELit _ => []
                     | mb => [KDisj (SA mb 0) (am_len m) (SA nb 0) ne]
                     end) ms.

(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_kend (base ne : expr) (nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (4096 * (KHI / 4096 + 1) + nlo) CEIL]
  end.

Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && Z.leb (KHI + 2 * nhi) (a_ylo cs) && Z.leb (a_ylo cs) FLOOR
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := KRange (EVar v) (KHI / 4096 + 1) ((CEIL - nlo) / 4096) :: null_kend base ne nlo ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filter (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs - 2 * nhi) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && Z.leb (img_hi A) alo && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_val (k : list kentry) (a b : expr) : bool :=
  if expr_eqb a b then true
  else (if lin_ge0 k [(a, 0%Z)] [(b, 0%Z)] then lin_ge0 k [(b, 0%Z)] [(a, 0%Z)] else false).
(* [comment removed for export] *)
Definition find_hole (k : list kentry) (ms : list amap) (a ne : expr) : option amap :=
  List.find (fun m => is_hole m && same_val k a (am_base m) && same_val k ne (am_len m)) ms.
(* [comment removed for export] *)
Definition unhole (ms : list amap) (h : amap) : list amap :=
  List.map (fun m => if (is_hole m && amap_eqb m h)%bool then AM (am_base m) (am_len m) KFOG else m) ms.

(* [comment removed for export] *)
Definition mmap_fixed_grant (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
           (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let m := AM a ne kind in
  let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
  let k' := ksh ++ kn_grant_filter k ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.

Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs KHI with
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
      else None
  | None =>
      (* [comment removed for export] *)
      match fixed_args cs CEIL with
      | Some (b, off, ne, nlo, nhi) =>
          match find_hole k (a_maps cs) a ne with
          | Some h =>
              let ms0 := unhole (a_maps cs) h in
              if (forallb (fun m => negb (is_hole m) || ranges_apart_x k b off ne (am_base m) 0 (am_len m)) ms0
                  && (negb eager || budget_ok cs nhi)
                  && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
              then mmap_fixed_grant cs ms0 b off ne nhi kind eager visible
              else None
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition kn_rezero (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bp k sp ub uk un K
                        | _ => true
                        end) k.

Definition kn_rezeroB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!6'aL#9#5#8#7#6#4$bc;R+a3$ub;R+C$uk;R+3$un;R+C&sp;R!4'aP#4#3#2#1+aJ!3'^Y+W$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C0$a;R+\$n;R+C,^U$a;R+\$n;R+C$k;R+50$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C,^U$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$n;R+C$c;R+30$a;R+\$n;R+C,^U!1'aR#5").

Lemma kn_rezeroB_eqf : forall fk, kn_rezeroB (mkbc fk) = kn_rezero fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;0!1+2+W%un;R+C0%sp;R+aJ%ub;R+C%uk;R+3%un;R+C%K;R+W+1!5#5!4'aP!1'`W#9#8#7#6#8#7#6#4!1'aR!1'`W#5!6'aM#9!4'aU#9#8#7#6#8#7#6#4!3'^Y+W$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C5$a;R+\$n;R+C,^U$a;R+\$n;R+C$k0;R+55$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C,^U$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$n;R+C$c;R+35$a;R+\$n;R+C,^U#5%b1;R+C%k1;R+3%n1;R+C+aJ!6'aM#9!3#5#8#7#6#8#7#6#4!6'aM#8!4'aU#8#7#6#5#7#6#5#4!1'`W#4$fk;R0!5'aE+C%uk;R+31!1'e[!1'`W#1!1'e\#1$x;R+C!5'aE+31!2'e[!1'`W#2#1!2'e\#2#1$x0;R+3!5'aE+C0!3'e[!1'`W#3#2#1!3'e\#3#2#1$x1;R+Cvd!6'_F2!1'aM#4$b;R2!3+_70!3'^Y+W$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C3$a;R+\$n;R+C,^U$a;R+\$n;R+C$k;R+53$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C,^U$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$n;R+C$c;R+33$a;R+\$n;R+C,^U46!6'_F7!1'aU#4$s;R7!3+_70!3'^Y+W$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C8$a;R+\$n;R+C,^U$a;R+\$n;R+C$k;R+58$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C,^U$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$n;R+C$c;R+38$a;R+\$n;R+C,^U46!6'_F0#4$l;R0!3+_70!3'^Y+W$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C5$a;R+\$n;R+C,^U$a;R+\$n;R+C$k;R+55$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C,^U$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$n;R+C$c;R+35$a;R+\$n;R+C,^U#16!2,_G0!3'^Y+W$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C9$a;R+\$n;R+C,^U$a;R+\$n;R+C$k0;R+59$lo;R+3$hi;R+3,^U$e;R+C$m;R+3,^U$e;R+C$lo;R+3$hi;R+3,^U$a;R+\$n;R+C,^U$a1;R+\$n1;R+C$a2;R+\$n2;R+C,^U$a;R+\$n;R+C$c;R+39$a;R+\$n;R+C,^U#4!1'aR:!1'aV#4!1'aP:!1'aW#4!1'aL:!1'aX#4!3+_70!4'e[:#3#2#1!4'e\#4#3#2#1").
Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.

Definition kn_rezeroM (k : list kentry) := kn_rezeroB (mkbc k).
Lemma kn_rezeroM_eq : kn_rezeroM = kn_rezero. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+2+W%ub;R+C%uk;R+3%un;R+C0!5'aE01'f0'e\$k;R0vd!1'f1#1!3+_71!1'f0#1!1'e\#1").
Qed.



(* [comment removed for export] *)
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.

(* [comment removed for export] *)
Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs CEIL with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containing k (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition fixed_in_args (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs CEIL with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containingB bc (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.

Lemma fixed_in_args_eq : forall cs arm, fixed_in_args cs arm = fixed_in_args_ref cs arm.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SK0!1+2+e2%ms;R!1+2+8%kinds;R0%b;R+C%off;R+3%n;R+C!1+^7+8!1'^5#2!2+^I+C+3!2+^I3+C!2+^I4+3!2+^I5+3!2+^I6+8!1+^77!2'f3#3'eR!1'M#<!1,Y+e2!3,_C+e2,f4!3,_C+e2,f5!3,_C+e2,f6;!3,_C+e2,e<;-f2RN$arm;R+f20#;3<=<!1'dS#=}:!2,^87!4,cJ6+8!4,cJ5+3!4,cJ4+3!4,cJ3+C!4,cJ+C+3#3#2#4#6#8#1!1,[7-1RN$~R+18!2'^P!2'`Q?#4!2'`Q?!2'^>#=@2AB!2'f3#2'eR!1'^5#;!1'M#;-f2RN$arm;R+f20#:3<=<!1'dS#<-1RN$~R+18!2'^P!2'`QH#4!2'`QH!2'^>#<@2AB-^7RN$x;R!1+^768D2$p;R6-^IRN$p;R!2+^I5+38#11$p0;R5$nhi;R+3-^IRN$p0;R!2+^I4+38#21$p1;R4$nlo;R+3-^IRN$p1;R!2+^I3+C8#21$p2;R3$ne;R+C-^IRN$p2;R!2+^I+C+38#21$b;R+C$off;R+3-^7RN$x;R!1+^7+88!6'e5EFG#2#1#32$m;R+8IBB$cs;R+A$arm;R+f2vdvd!6'_F1!1'e52$o;R1!3+_78-^7RN$x;R!1+^76892$p;R6-^IRN$p;R!2+^I5+38#11$p0;R5$nhi;R+3-^IRN$p0;R!2+^I4+38#21$p1;R4$nlo;R+3-^IRN$p1;R!2+^I3+C8#21$p2;R3$ne;R+C-^IRN$p2;R!2+^I+C+38#21$b;R+C$off;R+3-^7RN$x;R!1+^7+88!5#::>#2#1#32$m;R+8CBB-^7RN$x;R!1+^76892$p;R6-^IRN$p;R!2+^I5+38#11$p0;R5$nhi;R+3-^IRN$p0;R!2+^I4+38#21$p1;R4$nlo;R+3-^IRN$p1;R!2+^I3+C8#21$p2;R3$ne;R+C-^IRN$p2;R!2+^I+C+38#21$b;R+C$off;R+3-^7RN$x;R!1+^7+88!6'e5!1'^5#<:>#2#1#32$m;R+8CBB!2,_G8J!1'e4!1'`W2!1'e?2!3+_78-^7RN$x;R!1+^768D2$p;R6-^IRN$p;R!2+^I5+38#11$p0;R5$nhi;R+3-^IRN$p0;R!2+^I4+38#21$p1;R4$nlo;R+3-^IRN$p1;R!2+^I3+C8#21$p2;R3$ne;R+C-^IRN$p2;R!2+^I+C+38#21$b;R+C$off;R+3-^7RN$x;R!1+^7+88!6'e4!1'`WEFG#2#1#32$m;R+8IBBJ!3+_78!2'f7#2#1!2'f8#2#1").
Qed.


(* [comment removed for export] *)
Definition mmap_fixed_in_ref (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfill k b off ne)
                  | ArmF => kimg_clip (kn_rezero k b off ne)
                  | ArmG => kimg_clip (kn_cutout k b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.
(* [comment removed for export] *)
Definition mmap_fixed_in (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfillB bc b off ne)
                  | ArmF => kimg_clip (kn_rezeroB bc b off ne)
                  | ArmG => kimg_clip (kn_cutoutB bc b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.

Lemma mmap_fixed_in_eq : forall cs arm, mmap_fixed_in cs arm = mmap_fixed_in_ref cs arm.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^R0!1+2+W%ub;R+C%uk;R+3%un;R+C0!1'^5#2!1+^7+A!2+^I+C+3!2+^I4+C!2+^I5+3!2+^I6+3!2+^I7+8!2'f7#3#2-f2RN$arm;R+f2+1#=3!2'f9#>#7,^U,^U!1,c?|20;!2'^S!1'cU#>;!1'E#>!1'D=!1'^5#>!1'`W?!1'eW!4'aS@#2#1#3!1'eW!3#<#2#1#3!1'J=!1+2+8!1'M#>!2'f:E#9-f2RN$arm;R+f2D#=3FEF!1'N#>!1'O#>!1'P#>-f2RN$arm;R+f2+3#=3!2'^SJ#7JJ!1'Q#>!1'R#>!1'S#>!1'T#>!1'U#>!1'V#>!;,L!4'^1<>-f2RN$arm;R+f20#=3A!1'eW!4'e[@#2#1#3BCGHIKLMNOPQ}:!2'^>#>S!2,`0#2#1!2,`KU#3!2,`EU#3!2,^8+AR!1,[+A!1'eW!4'e\?#2#1#3!1'eW!4'bN?#2#1#3!;,L!4'^1<>-f2RN$arm;R+f20#=3!1'eW!4'aT?#2#1#3Z[CGHIKLMNOPQ!2,^8+A\-^7RN$x;R!1+^78392$p;R8-^IRN$p;R!2+^I7+83#11$p0;R7$m;R+8-^IRN$p0;R!2+^I6+33#21$p1;R6$nhi;R+3-^IRN$p1;R!2+^I5+33#21$p2;R5$nlo;R+3-^IRN$p2;R!2+^I4+C3#21$p3;R4$ne;R+C-^IRN$p3;R!2+^I+C+33#21$b;R+C$off;R+3-1RN$~R+13:2-f2RN$arm;R+f23#=3!4'eD\T#3!3,_C+WV!3,_C+WW!1'^5\^0^0YY!;,L!4'^1<>-f2RN$arm;R+f20#=3AB[CGHIKLMNOPQ!2,^8+A^2!;,L!4'^1<>-f2RN$arm;R+f20#=3BZ[CGHIKLMNOPQ!2,^8+A^4!2'f7#2#1-f2RN$arm;R+f2+1#<3!2'f9#=#7,^U,^U!2'^S!1'cU#=;!1'E#=!1'D^9!1'^5#=!1'J^9!1'M#=!2'f:^=#9-f2RN$arm;R+f2D#<3^>^=^>!1'N#=!1'O#=!1'P#=-f2RN$arm;R+f2+3#<3!2'^S^B#7^B^B!1'Q#=!1'R#=!1'S#=!1'T#=!1'U#=!1'V#=!;,L!4'^1^8^:-f2RN$arm;R+f20#<3!1'eW!4'aT^;#2#1#3!1'eW!4'e\^;#2#1#3!1'eW!4'bN^;#2#1#3^<^?^@^A^C^D^E^F^G^H^I!2'^>#=S!2,^8+A^J-^7RN$x;R!1+^783^62$p;R8-^IRN$p;R!2+^I7+83#11$p0;R7$m;R+8-^IRN$p0;R!2+^I6+33#21$p1;R6$nhi;R+3-^IRN$p1;R!2+^I5+33#21$p2;R5$nlo;R+3-^IRN$p2;R!2+^I4+C3#21$p3;R4$ne;R+C-^IRN$p3;R!2+^I+C+33#21$b;R+C$off;R+3-1RN$~R+13^72-f2RN$arm;R+f23#<3!4'eD^J^K#3!3,_C+WV!3,_C+WW!1'^5^J^L^LYY!1'`W2!1'`W^;!;,L!4'^1^8^:-f2RN$arm;R+f20#<3!1'eW!4'aS^O#2#1#3!1'eW!4'e[^O#2#1#3!1'eW!4'bM^O#2#1#3^<^?^@^A^C^D^E^F^G^H^I!2,^8+A^P$cs;R+A$arm;R+f2vdvd!6'_F1!1'bN2$l;R1!3+_73-^7RN$x;R!1+^78392$p;R8-^IRN$p;R!2+^I7+83#11$p0;R7$m;R+8-^IRN$p0;R!2+^I6+33#21$p1;R6$nhi;R+3-^IRN$p1;R!2+^I5+33#21$p2;R5$nlo;R+3-^IRN$p2;R!2+^I4+C3#21$p3;R4$ne;R+C-^IRN$p3;R!2+^I+C+33#21$b;R+C$off;R+3-1RN$~R+13:2-f2RN$arm;R+f23#=3!4'eDRT#3!3,_C+WV!3,_C+WW!1'^5RXXYY^1!6'_F1!1'e\2$l;R1!3+_73-^7RN$x;R!1+^78392$p;R8-^IRN$p;R!2+^I7+83#11$p0;R7$m;R+8-^IRN$p0;R!2+^I6+33#21$p1;R6$nhi;R+3-^IRN$p1;R!2+^I5+33#21$p2;R5$nlo;R+3-^IRN$p2;R!2+^I4+C3#21$p3;R4$ne;R+C-^IRN$p3;R!2+^I+C+33#21$b;R+C$off;R+3-1RN$~R+13:2-f2RN$arm;R+f23#=3!4'eD^2T#3!3,_C+WV!3,_C+WW!1'^5^2^3^3YY^1!6'_F1!1'aT2$l;R1!3+_73-^7RN$x;R!1+^78392$p;R8-^IRN$p;R!2+^I7+83#11$p0;R7$m;R+8-^IRN$p0;R!2+^I6+33#21$p1;R6$nhi;R+3-^IRN$p1;R!2+^I5+33#21$p2;R5$nlo;R+3-^IRN$p2;R!2+^I4+C3#21$p3;R4$ne;R+C-^IRN$p3;R!2+^I+C+33#21$b;R+C$off;R+3-1RN$~R+13:2-f2RN$arm;R+f23#=3!4'eD^4T#3!3,_C+WV!3,_C+WW!1'^5^4^5^5YY^1!2,_G3^M!1'aS^N!1'aZ2!1'e[^N!1'f12!1'bM^N!1'bQ2!3+_73-^7RN$x;R!1+^783^62$p;R8-^IRN$p;R!2+^I7+83#11$p0;R7$m;R+8-^IRN$p0;R!2+^I6+33#21$p1;R6$nhi;R+3-^IRN$p1;R!2+^I5+33#21$p2;R5$nlo;R+3-^IRN$p2;R!2+^I4+C3#21$p3;R4$ne;R+C-^IRN$p3;R!2+^I+C+33#21$b;R+C$off;R+3-1RN$~R+13^72-f2RN$arm;R+f23#<3!4'eD^P^K#3!3,_C+WV!3,_C+WW!1'^5^P^Q^QYY^M!3+_73!2'f;#2#1!2'f<#2#1").
Qed.


(* [comment removed for export] *)
Definition ENOMEM_RET : Z := two64 - 12.

(* [comment removed for export] *)
Definition refuse (cs : acs) : acs := set_pc (set_reg cs 10 (ELit ENOMEM_RET)) (pc cs + 4).

(* [comment removed for export] *)
Definition replace_entry (ms : list amap) (m : amap) (pieces : list amap) : list amap :=
  flat_map (fun m' => if amap_eqb m' m then pieces else [m']) ms.

(* [comment removed for export] *)
Definition dest_lfact (a mb : expr) (lne : bool) : kentry :=
  if lne then KRange (esub a mb) 1 (two64 - 1) else KRange (esub a mb) 0 0.
Definition dest_rfact (a ne mb ml : expr) (rne : bool) : kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!2'dR!2'dY#3#2!2'dY#5#4!1,c?,dL$a;R+C$ne;R+C$mb;R+C$ml;R+C$rne;R+1-1RN$rne;R+1+W#12!3,`J01!2'aD'^:1!3,`J0,G,G").

Definition mmap_destroyed_with_ref (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in      (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutout k b off ne)) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).
(* [comment removed for export] *)
Definition mmap_destroyed_with (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) (lne rne : bool) : acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let lp := if lne then [AM mb (esub a mb) (am_kind m)] else [] in
  let rp := if rne then [AM (eadd a ne) (esub (eadd mb ml) (eadd a ne)) (am_kind m)] else [] in
  let hp := if hole then [AM a ne KHOLE] else [] in      (* [comment removed for export] *)
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit ENOMEM_RET))
             (dest_lfact a mb lne :: dest_rfact a ne mb ml rne :: kimg_clip (kn_cutoutB bc b off ne)) (s_next ss))
      (hp ++ replace_entry (a_maps cs) m (lp ++ rp)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs).

Lemma mmap_destroyed_with_eq : forall hole cs b off ne m lne rne, mmap_destroyed_with hole cs b off ne m lne rne = mmap_destroyed_with_ref hole cs b off ne m lne rne.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^60%ub;R+C%uk;R+3%un;R+C!1+2+W!1'^5#7!1,c?|20;!2'^S!1'cU#82!1'E#8}:!1,F'f=!3'^2!1'D456!2'^>#85!1'^G#4!3'f>89#3!1'^H#4!5'f?8#59;#2!1'J4!1+2+8!1,Y+8!1':#4!2'dY8#5!3'^4+8-1RN$hole;R+1>#92!3,_C+8!3,f@8#5,;??!3'fA!1'M#8#4!3'^4+8-1RN$lne;R+1>#32!3,_C+8!3,f@9!2'dR89@??-1RN$rne;R+1>#22!3,_C+8!3,f@A!2'dR!2'dY9;A@??!1'N#8!1'O#8!1'P#8!1'Q#8!1'R#8!1'S#8!1'T#8!1'U#8!1'V#8!2'^S!1'cU#72!1'E#7!3'^2!1'DM56!2'^>#75!1'^G#3!3'f>OP#2!1'^H#3!5'f?O#4PR#1!1'JM!1':#3!2'dYO#4!3'^4+8-1RN$hole;R+1>#82!3,_C+8!3,f@O#4,;??!3'fA!1'M#7#3!3'^4+8-1RN$lne;R+1>#22!3,_C+8!3,f@P!2'dROPU??-1RN$rne;R+1>#12!3,_C+8!3,f@V!2'dR!2'dYPRVU??!1'N#7!1'O#7!1'P#7!1'Q#7!1'R#7!1'S#7!1'T#7!1'U#7!1'V#7!;,L!4'^1LN!3,_C+WQ!3,_C+WS!1'eW!4'bN1#6#5#4TWXYZ[\^0^1^2^3!1'`W1$hole;R+1$cs;R+A$b;R+C$off;R+3$ne;R+C$m;R+8$lne;R+1$rne;R+1vdvd!6'_F0!1'bN1$l;R0!3+_7+A!;,L!4'^137!3,_C+W:!3,_C+W<!1'eW!3#1#7#6#5=BCDEFGHIJK!;,L!4'^137!3,_C+W:!3,_C+W<!1'eW!4'bN!1'^5#8#7#6#5=BCDEFGHIJK!2,_G+A^4!1'bM^5!1'bQ1!3+_7+A!;,L!4'^1LN!3,_C+WQ!3,_C+WS!1'eW!4'bM^5#6#5#4TWXYZ[\^0^1^2^3^4!3+_7+A!8'fB#8#7#6#5#4#3#2#1!8'fC#8#7#6#5#4#3#2#1").
Qed.


(* [comment removed for export] *)
Definition dest_cases (cs : acs) (ne : expr) (m : amap) : list (bool * bool) :=
  let k := kn cs in
  let a := reg cs 10 in
  let mb := am_base m in let ml := am_len m in
  let ls := if lin_ge0 k [(a, -1)] [(mb, 0)] then [true]                                   (* [comment removed for export] *)
            else if (expr_eqb a mb || lin_ge0 k [(mb, 0)] [(a, 0)])%bool then [false]    (* [comment removed for export] *)
            else [true; false] in
  let rs := if lin_ge0 k [(mb, -1); (ml, 0)] [(a, 0); (ne, 0)] then [true]                 (* [comment removed for export] *)
            else if lin_ge0 k [(a, 0); (ne, 0)] [(mb, 0); (ml, 0)] then [false]           (* [comment removed for export] *)
            else [true; false] in
  flat_map (fun l => map (fun r => (l, r)) rs) ls.

Definition mmap_destroyed (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S10!2+^I+1+1$hole;R+1$cs;R+A$b;R+C$off;R+3$ne;R+C$m;R+8!4'fD0+A$lr;R0!8'fB#7#6#5#4#3#2!3'^J+1+1#1!3'^K+1+1#1!3'fE#5#2#1").

(* [comment removed for export] *)
Definition mmap_gate (cs : acs) : option (Z * Z * bool) :=
  match reg_lit cs 17, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some prot, Some flags, Some m1, Some 0 =>
      if negb (Z.eqb m1 (two64 - 1)) then None
      else Some (prot, flags, match reg_lit cs 10 with Some 0 => true | _ => false end)
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition node_mmap2 (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_null cs KRW true true               (* [comment removed for export] *)
                 | 3, 0x4022 => mmap_null cs KRWLAZY false true        (* [comment removed for export] *)
                 | 0, 0x22 => mmap_null cs KNONE false false           (* [comment removed for export] *)
                 | 0, 0x4022 => mmap_null cs KNONELAZY false false     (* [comment removed for export] *)
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x32 => mmap_fixed_free cs KRW true true          (* [comment removed for export] *)
                 | 0, 0x4032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x32 => mmap_fixed_free cs KNONE false false      (* [comment removed for export] *)
                 | _, _ => None
                 end in
      match g with Some csG => Some (refuse cs, csG) | None => None end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_mmapin (hole : bool) (cs : acs) : option (acs * acs * list acs) :=
  match mmap_gate cs with
  | Some (prot, flags, false) =>
      let arm := match prot, flags with
                 | 3, 0x32 => Some ArmE
                 | 3, 0x4032 => Some ArmF
                 | 0, 0x32 => Some ArmG
                 | _, _ => None
                 end in
      match arm with
      | Some arm =>
          match fixed_in_args cs arm, mmap_fixed_in cs arm with
          | Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed hole cs b off ne m)
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mprotect_ref (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs CEIL with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfill k b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs CEIL with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfillB bc b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Lemma node_mprotect_eq : forall cs, node_mprotect cs = node_mprotect_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^K0%ms;R!1+2+8%kinds;R!1+2+e2%b;R+C%off;R+3%n;R+C!1+^7+8!1'^5#1!1+^7+A}A!2'eJ#23!1,[+A}<!2'eJ#;6!2+^I+C+3!2+^I8+C!2+^I9+3!2+^I:+3!2'f3#>'eR!1'M#G!3,_C+e2,f5!3,_C+e2,f6!1,Y+e2!1'dS#H}:!2'^>#H@!2'^P!2'^P!2'f9#H#8!2'`Q?#4!2'`Q?A!1,c?|20;!2'^S!1'cU#HC!1'E#H!1,F,G!3'^2!1'DE@F!1'^5#H!1'JE!2'f:!1'M#H#1!1'N#H!1'O#H!2'^S!1'P#H#8!1'Q#H!1'R#H!1'S#H!1'T#H!1'U#H!1'V#H!;,L!4'^1DG!1'eW!4'aS!1'`WH#3#2#4IJKLMNOPQRS!2,`0#3#2!2,`KU#4!2,`EU#4!1'^5#G!6'e5X=>#2#1#3!;,L!4'^1DG!1'eW!4'aTH#3#2#4IJKLMNOPQRS-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_85$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_85$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_85$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^7+3272$z0;R+3-3RN$z0;R+32#135$p7;R+_8-_8RN$p7;R+_82#13$p8;R+_8-_8RN$p8;R+_82#13$p9;R+_85$p9;R+_85-^7RN$x;R!1+^7;2<2$p9;R;-^IRN$p9;R!2+^I:+32#11$p10;R:$nhi;R+3-^IRN$p10;R!2+^I9+32#21$p11;R9$nlo;R+3-^IRN$p11;R!2+^I8+C2#21$p12;R8$ne;R+C-^IRN$p12;R!2+^I+C+32#21$b;R+C$off;R+3-^7RN$x;R!1+^7+82Y2$m;R+8-1RN$~R+12B2!4'eDZA#4!3,_C+WV!3,_C+WW!1'^5Z555$p8;R+_855$p7;R+_855$p6;R+_855$p5;R+_855555$p1;R+_8555$p;R+_855%ub;R+C%uk;R+3%un;R+C!1+2+W!;,L!4'^1DG!1'eW!3#G#3#2#4IJKLMNOPQRS!2'eJ#13!2'eJ#:6!2'f3#='eR!1'^5#F!1'M#F!1'dS#G!2'^>#G@!2'^P!2'^P!2'f9#G#8!2'`Q^6#4!2'`Q^6^7!2'^S!1'cU#GC!1'E#G!3'^2!1'D^:@F!1'J^:!2'f:=#1!1'N#G!1'O#G!2'^S!1'P#G#8!1'Q#G!1'R#G!1'S#G!1'T#G!1'U#G!1'V#G!;,L!4'^1^9^;!1'eW!4'aTX#3#2#4^<^=^>^?^@^A^B^C^D^E^F-^7RN$x;R!1+^7+32^12$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_85$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_85$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_85$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^7+32^22$z0;R+3-3RN$z0;R+32#135$p7;R+_8-_8RN$p7;R+_82#13$p8;R+_8-_8RN$p8;R+_82#13$p9;R+_85$p9;R+_85-^7RN$x;R!1+^7;2^32$p9;R;-^IRN$p9;R!2+^I:+32#11$p10;R:$nhi;R+3-^IRN$p10;R!2+^I9+32#21$p11;R9$nlo;R+3-^IRN$p11;R!2+^I8+C2#21$p12;R8$ne;R+C-^IRN$p12;R!2+^I+C+32#21$b;R+C$off;R+3-^7RN$x;R!1+^7+82!6'e5^4^5>#2#1#32$m;R+8-1RN$~R+12^82!4'eD^G^7#4!3,_C+WV!3,_C+WW!1'^5^G555$p8;R+_855$p7;R+_855$p6;R+_855$p5;R+_855555$p1;R+_8555$p;R+_855!1'`W1!;,L!4'^1^9^;!1'eW!4'aS!1'`WX#3#2#4^<^=^>^?^@^A^B^C^D^E^F$cs;R+Avdvd!6'_F0!1'e51$o;R0!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_85$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_85$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_85$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^7+3272$z0;R+3-3RN$z0;R+32#135$p7;R+_8-_8RN$p7;R+_82#13$p8;R+_8-_8RN$p8;R+_82#13$p9;R+_85$p9;R+_85-^7RN$x;R!1+^7;2<2$p9;R;-^IRN$p9;R!2+^I:+32#11$p10;R:$nhi;R+3-^IRN$p10;R!2+^I9+32#21$p11;R9$nlo;R+3-^IRN$p11;R!2+^I8+C2#21$p12;R8$ne;R+C-^IRN$p12;R!2+^I+C+32#21$b;R+C$off;R+3-^7RN$x;R!1+^7+82!5#F=>#2#1#32$m;R+8-1RN$~R+12B2!4'eDTA#4!3,_C+WV!3,_C+WW!1'^5T555$p8;R+_855$p7;R+_855$p6;R+_855$p5;R+_855555$p1;R+_8555$p;R+_855[!6'_F\!1'aT1$l;R\!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_85$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_85$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_85$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^7+3272$z0;R+3-3RN$z0;R+32#135$p7;R+_8-_8RN$p7;R+_82#13$p8;R+_8-_8RN$p8;R+_82#13$p9;R+_85$p9;R+_85-^7RN$x;R!1+^7;2<2$p9;R;-^IRN$p9;R!2+^I:+32#11$p10;R:$nhi;R+3-^IRN$p10;R!2+^I9+32#21$p11;R9$nlo;R+3-^IRN$p11;R!2+^I8+C2#21$p12;R8$ne;R+C-^IRN$p12;R!2+^I+C+32#21$b;R+C$off;R+3-^7RN$x;R!1+^7+82Y2$m;R+8-1RN$~R+12B2!4'eD^0A#4!3,_C+WV!3,_C+WW!1'^5^0555$p8;R+_855$p7;R+_855$p6;R+_855$p5;R+_855555$p1;R+_8555$p;R+_855[!2,_G2^H!1'aS^I!1'aZ1!1'e4^I!1'e?1!3+_72-^7RN$x;R!1+^7+32^12$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_85$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_85$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_85$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^7+32^22$z0;R+3-3RN$z0;R+32#135$p7;R+_8-_8RN$p7;R+_82#13$p8;R+_8-_8RN$p8;R+_82#13$p9;R+_85$p9;R+_85-^7RN$x;R!1+^7;2^32$p9;R;-^IRN$p9;R!2+^I:+32#11$p10;R:$nhi;R+3-^IRN$p10;R!2+^I9+32#21$p11;R9$nlo;R+3-^IRN$p11;R!2+^I8+C2#21$p12;R8$ne;R+C-^IRN$p12;R!2+^I+C+32#21$b;R+C$off;R+3-^7RN$x;R!1+^7+82!6'e4!1'`W^4^5>#2#1#32$m;R+8-1RN$~R+12^82!4'eD^J^7#4!3,_C+WV!3,_C+WW!1'^5^J555$p8;R+_855$p7;R+_855$p6;R+_855$p5;R+_855555$p1;R+_8555$p;R+_855^H!3+_72!1'fF#1!1'fG#1").
Qed.


(* [comment removed for export] *)
Definition node_mprotect2 (cs : acs) : option (acs * acs) :=
  match node_mprotect cs with Some csG => Some (refuse cs, csG) | None => None end.

(* [comment removed for export] *)

Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$bc;R+a3$b;R+C$n;R+C$m;R+8!2'^P!2'^P!1'>!1'?#1!2'^Q#3!1'^G#1!3'cK#4#2!1'^H#1").

Lemma amap_matchB_eqf : forall fk, amap_matchB (mkbc fk) = amap_match fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S50%m;R+8+1%n;R+C%m;R+C+1!2'^P!1'>!1'?#2!2'^Q#4!1'^G#2!1'^H#2!1'`W#4$fk;R!1+2+W!5'aE+C%n;R+C0!1'fH!1'`W#1!1'fI#1$x;R+C!5'aE+C0!2'fH!1'`W#2#1!2'fI#2#1$x0;R+C!5'aE+8+1!3'fH!1'`W#3#2#1!3'fI#3#2#1$x1;R+8vd!6'_F1!1'cL#4$b;R1!3+_7+1!2'^P2!2#1#33!2'^P2!3'cL#5#33!2,_G+1!2'^P!2'^P!1'>!1'?#1!2'^Q#3!1'^G#1!3'cL#4#2!1'^H#1!1'cK4!1'fJ#4!3+_7+1!4'fH4#3#2#1!4'fI#4#3#2#1").
Qed.
#[local] Hint Rewrite amap_matchB_eqf : bceq.



(* [comment removed for export] *)
Definition node_munmap_ref (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_match k b ne) (a_maps cs) && page_aligned k b && flat_x k bb bk ne
          && match xhi k b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in
                               Z.leb 3 (ealign k (fst p)) && Z.leb 3 (ealign k (snd p))
                               && xinside k pb pk (snd p) bb bk ne && kzero_x k k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in kn_unfill kk sb sk sn) gone (kn_unfill k bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_match k b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_munmap (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_xB bc pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_xB bc pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_matchB bc b ne) (a_maps cs) && page_alignedB bc b && flat_xB bc bb bk ne
          && match xhiB bc b with Some hi => Z.ltb (hi + nhi) two64 | None => false end
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in
                               Z.leb 3 (ealignB bc (fst p)) && Z.leb 3 (ealignB bc (snd p))
                               && xinsideB bc pb pk (snd p) bb bk ne && kzero_xB bc k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in kn_unfillM kk sb sk sn) gone (kn_unfillB bc bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_matchB bc b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_munmap_eq : forall cs, node_munmap cs = node_munmap_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_X0%b;R+C%n;R+C%m;R+8+1!1'^5#1!1+^7+A}A!2'eJ#23!1,[+A!2+^I+C+3!2+^I6+3!1'eL#;}:!1'^W!2'^>#@9!2'^>#B9!1'M#B!1'^5#B!1'`W=!2'cQ>;!4'cE>#2#1#4!2'aC!2'^S#1#6'^:-^7RN$x;R!1+^7+3+1!2'c8>;2$hi;R+3A,6!2+^I+C+C!3'^J+C+C#1!1'^WD!1'^5#E!1'`WF!3'^J+C+C#3!3'^K+C+C#3!3'e8GHI!1,c?|11;!1'^5#I!1'`WL!3'^J+C+C#7!3'^K+C+C#7!7'c1M#6#5O#9#8#;!5'c;ML#2#1#3!7'aBG#2#1I#5#4#7!1'Q#B!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3!1'>RS!1,c?|20;!2'^S!1'cU#BU!1'E#B!1,F,G!3'^2!1'DW9X!1+2+W!1'^5#D!1'`W[!3'^K+C+C#1-^IRN$p0;R!2+^I+C+3Z#21$sb;R+C$sk;R+3!4'aY#6#2#1#3$kk;RZ$p;RC-^IRN$x;R!2+^I6+CZ!3'e8\D^01$p0;R6$sn;R+C^1!1'JW!4'^1VY!5'fKZC^2T!4'aS>#2#1#4^3!2'^>#C9!1'N#B!1'O#B!1'P#B!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3RS!1'R#B!3'^4CT^:!1'S#B!1'T#B!1'U#B!1'V#B!3'^O+8!3'fI=;#4<!4'cF=#2#1#4!2'^P!2'^P^@!2'cR=;^A!2'^P^B-^7RN$x;R!1+^7+3+1!2'c9=;2$hi;R+3A,6!3'e9FHI!2'^P!2'^RK!2'cSLN!2'^RK!2'cSLO!5'c<LL#2#1#3!7'aHF#2#1I#5#4#7!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3!1'>^GS!2'^P^C!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1^D1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P!2'^P^E!7'c3L#6#5O#9#8#;^F^H!3'e9[D^0-^IRN$p0;R!2+^I+C+3Z#21$sb;R+C$sk;R+3!4'aT#6#2#1#3!4'aT=#2#1#4!1'^5#C!3'^Y+8$m;R+8!1'>!4'fI^M^5#5#1<!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3^GS!3'^4C^H^:-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12^I2!2,^8+A!;,L!4'^1VY!5'fKZC$kk;RZ$p;RC-^IRN$x;R!2+^I6+CZ^J1$p0;R6$sn;R+C^K^H^L^3^N^6^7^8^O^P^<^=^>^?55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855%e;R+C+3!2'^P^@?!2,^8+A!;,L^4^N^6^7^8^9^;^<^=^>^?%b;R+C%off;R+3%n;R+C+1!3#A#2#1#4!2'^P^EP!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1J1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P^WQT%ub;R+C%uk;R+3%un;R+CZ!2'^P!2'^P^S^AB%k;RZ^U!2,^8+A!;,L!4'^1VY!5'fKZC^2T^L^3^N^6^7^8^9^;^<^=^>^?%e;R+C+1!1#A;-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P^W^F$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1J1$p0;R6$sn;R+C_2%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1!2'^P^BB!6#D#2#1I#5#4#7!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3!1'>_6S%b;R+C%n;R+C!2+^I6+C%e;R+C!1+^7+3!2,^8+A!;,L!4'^1VY!5'fKZC$kk;RZ$p;RC-^IRN$x;R!2+^I6+CZ^J1$p0;R6$sn;R+C^1^H^L^3^N^6^7^8^O^P^<^=^>^?%k;RZ^Y!2'eJ#13!1'eL#:!1'^W!2'^>#?9!1'^5#A!2'^>#A9!1'M#A!1'^5#H!7'aH[#2#1I#5#4#7!1'Q#A!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3!1'>_C_D!2'^S!1'cU#AU!1'E#A!3'^2!1'D_G9X!1'J_G!1'N#A!1'O#A!1'P#A!1'R#A!1'S#A!1'T#A!1'U#A!1'V#A-^7RN$x;R!1+^7+32_<2$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^772_=2$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32_>1$bb;R+C$bk;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!3'^O+8!3'fI_?_@#4_A!2'cR_?_@!4'cF_?#2#1#4-^7RN$x;R!1+^7+3+1!2'c9_?_@2$hi;R+3A,6!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1!3'e9[HI1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P!2'^P!2'^P!2'^RK!2'cS_BN!2'^RK!2'cS_BO!7'c3_B#6#5O#9#8#;!5'c<_B_B#2#1#3_E2!2,^8+A!;,L!4'^1_F_H!5'fKZC$kk;RZ$p;RC-^IRN$x;R!2+^I6+CZ!3'e9^MD^01$p0;R6$sn;R+C^K_E!4'aT_?#2#1#4_I!3'^Y+8$m;R+8!1'>!4'fI=;#5#1_A_J_K_L!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3_C_D!3'^4C_E_M_N_O_P_Q55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855!1'`W1!1'`W_?!1'`W_B!7'aB\#2#1I#5#4#7!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3!1'>_V_D$cs;R+Avdvd!6'_F0!1'fI1$b;R0!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!3'^O+8!2#A;#4<?@B!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1J1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P!2'^P!2'^P!2'^RK!2'cPMN!2'^RK!2'cPMOPQT2!2,^8+A!;,L^4!3'^Y+8$m;R+8!1'>!3#B^5#5#1<^6^7^8^9^;^<^=^>^?55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F^R!1'cS1$z;R^R!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P!2'^P!2'^P^S@B!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1J1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P!2'^P!2'^P!2'^RK!1#HN!2'^RK!1#HOPQT2^T55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F^U!1'cF1$b;R^U!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P!2'^P!2'^P^S^VB^X2^T55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F^Y!1'aT1$l;R^Y!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P^Z^X2!2,^8+A!;,L!4'^1VY!5'fKZC^2T^V^3^N^6^7^8^9^;^<^=^>^?55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F^[!1'c<1$b;R^[!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P^Z!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1J1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P^W!4#HL#2#1#3T2^\55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F_0!1'cR1$b;R_0!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P^@_1^AB!3'=C_3T2^\55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F_4!1'aH1$b;R_4!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P_5!3'=C_3_72!2,^8+A!;,L!4'^1VY!5'fKZC^2_7^L^3^N^6^7^8!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3_6S!3'^4C_7^:^<^=^>^?55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F_8!1'e91$p;R_8!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P_5!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1!2#DHI1$p0;R6$sn;R+C_2^H2!2,^8+A!;,L!4'^1VY!5'fKZC$kk;RZ$p;RC-^IRN$x;R!2+^I6+CZ!2#CD^01$p0;R6$sn;R+C^1^H^L^3^N^6^7^8^O^P^<^=^>^?55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F_9!1'c91$o;R_9!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P!2'^P^B-^7RN$x;R!1+^7+3+1_12$hi;R+3A,6!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1^D1$p0;R6$sn;R+C_2^H2_:55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F_4!1'c31$b;R_4!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12!2'^P^C!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1^D1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P!2'^P^E!6#H#6#5O#9#8#;^F^H2_:55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!6'_F_;'aT$l;R_;!3+_72-^7RN$x;R!1+^7+3242$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^77282$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32:1$bb;R+C$bk;R+3-1RN$~R+12^I2!2,^8+A!;,L!4'^1VY!5'fKZC$kk;RZ$p;RC-^IRN$x;R!2+^I6+CZ^J1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3Z#21$sb;R+C$sk;R+3!4#G#6#2#1#3^H^L^3^N^6^7^8^O^P^<^=^>^?55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855^Q!2,_G2_R'aY'fL!1'c1_S!1'c51!1'c8_S!1'c:1!1'e8_S!1'e@1!1'aB_S!1'aI1!1'cQ_S!1'fM1!1'c;_S!1'fN1!1'aS_S!1'aZ1!1'cE_S!1'eC1!1'cP_S!1'cT1!1'fH_S!1'fO1!3+_72-^7RN$x;R!1+^7+32_<2$z;R+3-3RN$z;R+32#135$p;R+_8-_8RN$p;R+_82#13$p0;R+_8-_8RN$p0;R+_82#13$p1;R+_8-_8RN$p1;R+_82#13$p2;R+_8-_8RN$p2;R+_82#13$p3;R+_85$p3;R+_8-_8RN$p3;R+_82#13$p4;R+_8-_8RN$p4;R+_82#13$p5;R+_85$p5;R+_8-_8RN$p5;R+_82#13$p6;R+_8-_8RN$p6;R+_82#13$p7;R+_85$p7;R+_85-^7RN$x;R!1+^772_=2$p7;R7-^IRN$p7;R!2+^I6+32#11$p8;R6$nhi;R+3-^IRN$p8;R!2+^I+C+32#21$ne;R+C$nlo;R+3-^IRN$x;R!2+^I+C+32_>1$bb;R+C$bk;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!3'^O+8!3'fH_T_@#4_A!2'cQ_T_@!4'cE_T#2#1#4-^7RN$x;R!1+^7+3+1!2'c8_T_@2$hi;R+3A,6!3'=C$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3-^IRN$x;R!2+^I6+C+1!3'e8\HI1$p0;R6$sn;R+C-^IRN$p0;R!2+^I+C+3+1#21$sb;R+C$sk;R+3!2'^P!2'^P!2'^P!2'^RK!2'cP_UN!2'^RK!2'cP_UO!7'c1_U#6#5O#9#8#;!5'c;_U_B#2#1#3_W2!2,^8+A!;,L!4'^1_F_H!5'fKZC$kk;RZ$p;RC-^IRN$x;R!2+^I6+CZ!3'e8!1'`W^MD^01$p0;R6$sn;R+C^1_W!4'aS_T#2#1#4_I!3'^Y+8$m;R+8!1'>!4'fH>;#5#1_A_J_K_L!3'^YC$p;RC-^IRN$x;R!2+^I+C+3+1E1$pb;R+C$pk;R+3_V_D!3'^4C_W_M_N_O_P_Q55$p6;R+_8555$p4;R+_8555$p2;R+_855$p1;R+_855$p0;R+_855$p;R+_855_R!3+_72!1'fP#1!1'fQ#1").
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_req (cs : acs) : option Z :=
  match lit_diff (reg cs 10) (a_brk cs) with
  | Some d => if (Z.ltb 0 d && Z.eqb (d mod 4096) 0 && Z.leb d (2 ^ 40))%bool then Some d else None
  | None => None
  end.

(* [comment removed for export] *)
Definition brk_base_ok (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (page_aligned k b
   && match xlo k b, xhi k b with
      | Some lo, Some hi => Z.ltb 0 lo && Z.leb (img_hi A) lo && Z.leb (hi + d) KHI
      | _, _ => false
      end)%bool.

(* [comment removed for export] *)
Definition brk_grow_possible (cs : acs) (d : Z) : bool :=
  let k := kn cs in let '(bb, bk) := split_lit (a_brk cs) in
  (brk_base_ok cs d && no_fog (a_maps cs)
   && forallb (fun m => ranges_apart_x k bb bk (ELit (d + 4096)) (am_base m) 0 (am_len m)) (a_maps cs)  (* [comment removed for export] *)
   && budget_ok cs d)%bool.

(* [comment removed for export] *)
Definition brk_grow_blocked (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (brk_base_ok cs d
   && existsb (fun m => negb (is_fog m)
                        && lin_ge0 k [(am_base m, -1); (am_len m, 0)] [(b, 0)]      (* [comment removed for export] *)
                        && lin_ge0 k [(b, d - 1)] [(am_base m, 0)])               (* [comment removed for export] *)
              (a_maps cs))%bool.

(* [comment removed for export] *)
Definition node_brk1 (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 214 =>
      let ok := match reg_lit cs 10 with
                | Some 0 => true
                | _ => match brk_req cs with Some d => brk_grow_blocked cs d | None => false end
                end in
      if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_grow_possible cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kn_grant_filter k (a_maps cs) in
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
        match vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
        | Some csB' => Some (csA, csB')
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)

Definition node_settid (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 96 =>
      if (negb (a_tidset cs) && fresh_ok cs)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) (KRange (EVar v) 1 (PID_MAX - 1) :: s_know ss) (S v))
                 (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) true)
      else None
  | _ => None
  end.

Definition node_exit (cs : acs) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S40!1+^7+3!1,[+3}:-_8RN$p1;R+_80#13$p2;R+_8-_8RN$p2;R+_80#13$p3;R+_8-_8RN$p3;R+_80#13$p4;R+_8-_8RN$p4;R+_80#13$p5;R+_81$p5;R+_8-_8RN$p5;R+_80#13$p6;R+_81$p6;R+_81-^7RN$x;R!1+^7+30!2'eJ#922$code;R+3!2,^8+3!2'fR#1!1,c?|77f;11$p4;R+_811$p3;R+_811$p2;R+_811$cs;R+A-^7RN$x;R!1+^7+30!2'eJ#1}A2$z;R+3-3RN$z;R+30#131$p;R+_8-_8RN$p;R+_80#13$p0;R+_8-_8RN$p0;R+_80#13$p1;R+_81$p1;R+_831$p0;R+_8-_8RN$p0;R+_80#13$p1;R+_83$p1;R+_8111$p;R+_811").

(* [comment removed for export] *)

Fixpoint list_set_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match l, i with
  | [], _ => []
  | _ :: r, O => x :: r
  | y :: r, S i' => y :: list_set_nth i' x r
  end.
Fixpoint list_insert_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match i, l with
  | O, _ => x :: l
  | S i', y :: r => y :: list_insert_nth i' x r
  | S _, [] => [x]
  end.

Definition fog_token (sz : Z) : amap := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$sz;R+3!3,f@!1,F,G!1,F#1,fS").

Definition with_maps (cs : acs) (ms : list amap) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+A$ms;R!1+2+8!;,L!1'E#2#1!1'N#2!1'O#2!1'P#2!1'Q#2!1'R#2!1'S#2!1'T#2!1'U#2!1'V#2").

(* [comment removed for export] *)
Definition node_fog (cs : acs) (i : nat) (sz : Z) : option acs :=
  match nth_error (a_maps cs) i with
  | Some m =>
      if (negb (is_fog m) && Z.leb 0 sz && Z.ltb sz two64
          && match xhi (kn cs) (am_len m) with Some h => Z.leb h sz | None => false end)%bool
      then Some (with_maps cs (list_set_nth i (fog_token sz) (a_maps cs)))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_fognew (cs : acs) (i : nat) (sz : Z) : option acs :=
  if (Nat.leb i (length (a_maps cs)) && Z.leb 0 sz && Z.ltb sz two64)%bool
  then Some (with_maps cs (list_insert_nth i (fog_token sz) (a_maps cs)))
  else None.

(* [comment removed for export] *)
Definition node_ghost (cs : acs) (b n : expr) : option acs :=
  match xhi (kn cs) n with
  | Some nhi =>
      if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
      then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs ++ [(b, n)])
                     (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition vis_here (b n : expr) (p : expr * expr) : bool := (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool.

Definition node_unvis_ref (cs : acs) (b n : expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S60!1+2+W!1+^7+A!2+^I+C+3!2+^I+C+C!1,c?|11;!1,[+A$cs;R+A$b;R+C$n;R+C&k;R!1'^5#30-^IRN$x;R!2+^I+C+31!1'^W#31$bb;R+C$bk;R+3-^IRN$x;R!2+^I2+C1!3'e9#3#5#41$p;R2$sn;R+C-^IRN$p;R!2+^I+C+31#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+31!2'c9#7#92$bh;R+3-^7RN$x;R!1+^7+31!2'c9#8#92$nh;R+3-1RN$~R+11!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!3'^O3!2'fT#;#:!1'Q#<!2'^R4!2'cS#9#;!2'^R4!2'cS#9#:!4'cF#9#8#7#:!2'^R!2'^S#2#1'eR!4'cF#9#4#3#5!5'c<#9#9#4#3#52&k1;R!4'aT#9#8#7#:0&k2;R!4'aT#1#5#4#60&ss;R!1'E#>+K!2,^8+A!;,L!4'^1!1'I#1!1'D#1#2!1'J#1!1'M#?!1'N#?!1'O#?!1'P#?!3'^Y3$p;R3!1'>!3'fT#?#>#1!1'Q#?!3'^43!1'R#?!3,_C3!4,cJ+C+C#>#=!1,Y3!1'S#?!1'T#?!1'U#?!1'V#?555").
(* [comment removed for export] *)
Definition node_unvis (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc b, xhiB bc n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) CEIL
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn)%bool
      then
        let k1 := kn_unfillB bc bb bk n in
        let k2 := kn_unfillM k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

Lemma node_unvis_eq : forall cs b n, node_unvis cs b n = node_unvis_ref cs b n.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^P0%e;R+C+3!1'^5#3!1+^7+A!1'^W#3!2+^I+C+3!1'^5#6!3'e8!1'`W5#5#4!1'^5#:!1'`W7!2'c88#9!1'^5#;!1'`W:!2'c8;#9!2+^I+C+C!1'Q#<!3'^O=!2'fT#;#:>!1,c?|11;!1'^5#<!1'`WA!2'^R!2'^S#2#1'eR!5'c;BA#4#3#5!1'E#<!1'IE!1'DE!1'JE!1'M#<!1'N#<!1'O#<!1'P#<!3'^Y=$p;R=!1'>!3'fT#<#;#1>!1,Y=!3'^4=!1'R#<!3,_C=!4,cJ+C+C#;#:N!1'S#<!1'T#<!1'U#<!1'V#<!2,^8+A!;,L!4'^1FG!4'aY!4'aSB#8#7#:#4#3#5HIJKLMOPQRS!1,[+A!3'e95#5#4!2'c97#9!2'c9:#9!2'^P!2'^P?!2'^R@!2'cSA#;!2'^R@!2'cSA#:!2'^P!2'^P!2'^PY!4'cFA#8#7#:C!4'cFA#4#3#5!2'^PZ!5'c<AA#4#3#5!4'aTA#8#7#:-^IRN$x;R!2+^I+C+3231$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C2V1$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+32W2$bh;R+3-^7RN$x;R!1+^7+32X2$nh;R+3-1RN$~R+12[2!2,^8+A!;,L!4'^1FG!4'aT\#4#3#5HIJKLMOPQRSUUU%b;R+C%off;R+3%n;R+C+1!3#9#8#7#:!1+2+W%ub;R+C%uk;R+3%un;R+C^3%k;R^3^1!2,^8+A!;,L!4'^1FG!4'aY\#4#3#5HIJKLMOPQRS%b;R+C%n;R+C!2+^I4+C-1RN$~R+12[2^6U%e;R+C!1+^7+3%k;R^3^4!1'^W#2!1'^5#5!1'^5#9!1'Q#;!3'^O=!2'fT#:#9^>!1'E#;!1'I^@!1'D^@!1'J^@!1'M#;!1'N#;!1'O#;!1'P#;!3'^Y=$p;R=!1'>!3'fT#;#:#1^>!3'^4=!1'R#;!3,_C=!4,cJ+C+C#:#9N!1'S#;!1'T#;!1'U#;!1'V#;-^IRN$x;R!2+^I+C+32^;1$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C2!3'e9^<#4#31$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+32!2'c9^=#82$bh;R+3-^7RN$x;R!1+^7+32!2'c97#82$nh;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P^?!2'^R@!2'cS:#:!2'^R@!2'cS:#9!4'cF:#8#7#9C!4'cF:#4#3#5!5'c<::#4#3#52!2,^8+A!;,L!4'^1^A^B!4'aT!4'aT:#8#7#9#4#3#5^C^D^E^F^G^H^I^J^K^L^MUUU!1'`W1$cs;R+A$b;R+C$n;R+Cvdvd!6'_F0!1'cS1$z;R0!3+_72-^IRN$x;R!2+^I+C+3231$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C261$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+3292$bh;R+3-^7RN$x;R!1+^7+32<2$nh;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P?!2'^R@!1#9#;!2'^R@!1#9#:!4'cEB#8#7#:C!4'cEB#4#3#5D2TUUU^0!6'_F^1!1'cF1$b;R^1!3+_72-^IRN$x;R!2+^I+C+3231$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C261$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+3292$bh;R+3-^7RN$x;R!1+^7+32<2$nh;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^PY^2C!3#9#4#3#5D2TUUU^0!6'_F^4!1'aT1$l;R^4!3+_72-^IRN$x;R!2+^I+C+3231$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C261$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+3292$bh;R+3-^7RN$x;R!1+^7+32<2$nh;R+3-1RN$~R+12!2'^PZD2!2,^8+A!;,L!4'^1FG!4'aY^2#4#3#5HIJKLMOPQRSUUU^0!6'_F^5!1'c<1$b;R^5!3+_72-^IRN$x;R!2+^I+C+3231$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C261$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+3292$bh;R+3-^7RN$x;R!1+^7+32<2$nh;R+3-1RN$~R+12!2'^PZ!4#9A#4#3#52^6UUU^0!6'_F^7!1'e91$p;R^7!3+_72-^IRN$x;R!2+^I+C+3231$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C2!2#3#5#41$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+3292$bh;R+3-^7RN$x;R!1+^7+32<2$nh;R+3^8UU^0!6'_F^9!1'c91$o;R^9!3+_72-^IRN$x;R!2+^I+C+3231$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C2V1$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+32!1#7#92$bh;R+3-^7RN$x;R!1+^7+32!1#8#92$nh;R+3^8UU^0!6'_F^:'aT$l;R^:!3+_72-^IRN$x;R!2+^I+C+3231$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C2V1$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+32W2$bh;R+3-^7RN$x;R!1+^7+32X2$nh;R+3-1RN$~R+12[2!2,^8+A!;,L!4'^1FG!4#9\#4#3#5HIJKLMOPQRSUUU^0!2,_G2^N'aY'fL!1'c8^O!1'c:1!1'e8^O!1'e@1!1'c;^O!1'fN1!1'aS^O!1'aZ1!1'cE^O!1'eC1!1'cP^O!1'cT1!3+_72-^IRN$x;R!2+^I+C+32^;1$bb;R+C$bk;R+3-^IRN$x;R!2+^I4+C2!3'e8!1'`W^<#4#31$p;R4$sn;R+C-^IRN$p;R!2+^I+C+32#21$sb;R+C$sk;R+3-^7RN$x;R!1+^7+32!2'c8!1'`W^=#82$bh;R+3-^7RN$x;R!1+^7+32!2'c88#82$nh;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P^?!2'^R@!2'cP;#:!2'^R@!2'cP;#9!4'cE;#8#7#9C!4'cE;#4#3#5!5'c;;:#4#3#52!2,^8+A!;,L!4'^1^A^B!4'aY!4'aS;#8#7#9#4#3#5^C^D^E^F^G^H^I^J^K^L^MUUU^N!3+_72!3'fU#3#2#1!3'fV#3#2#1").
Qed.


(* [comment removed for export] *)
Definition node_havocbrk (cs : acs) (lo hi : Z) : option acs :=
  match xlo (kn cs) (a_brk cs), xhi (kn cs) (a_brk cs) with
  | Some l, Some h =>
      if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (EVar v) (a_fd cs) (a_tidset cs))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_intro (cs : acs) (lo hi : Z) : option acs :=
  if (fresh_ok cs && Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64)%bool then
    let v := nxt cs in let ss := a_ss cs in
    Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v)))
  else None.

(* [comment removed for export] *)
Definition SPIN_WORD : Z := 0x6f.
Definition node_spin (cs : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S50!1'cU#1|20;|500;!1,cW2!1+cV3$cs;R+A!2'^P!2'^P!2'^R,G0!2'aC!2'^S0!1,c?1'^:-^7RN$x;R!1+^74+1!2'cX/segs;!2'cY!1,cW|600;02$w;R4!2'aA!2'fW3#1'fX,6").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition summary_fill_ref (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xlo k ne, xhi k ne, xhi k dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_x k k db dk ne && kwritable_x k k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_x k k db dk ne then
              let k1 := kn_havoc k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_fill (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xloB bc ne, xhiB bc ne, xhiB bc dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_xB bc k db dk ne && kwritable_xB bc k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_xB bc k db dk ne then
              let k1 := kn_havocM k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.

Lemma summary_fill_eq : forall cs entry cmax, summary_fill cs entry cmax = summary_fill_ref cs entry cmax.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^X0!1+2+W%b;R+C%off;R+3%n;R+C+1%k;R01!1'^5#3!1+^7+A!1'>!2'aA!1'cU#4#3!1,[+A!1'fY#4};!2'eJ#58!1'>!2'aC#1#4}:!1'^W!2'^>#6;!1'^5#8!1'`W=}<!2'^>#8?!2'c0>@!1'^5#9!1'`WB!2'^>#9?!2'c8CD!1'^5#:!1'`WF!2'^>#:;!2'c8GH|10;!2'^P!2'^P!2'^R,G#3!2'^R#2!2'dQ!1,c?J!1,c?|508;!2'aC!2'^S#1#2'^:!2'aA#2,G!2'^>#;;!2,^8+CM!1'^5#;!4'fZ#;#7NO!1,c?|800;!2'aA!2'^9#6Q,G!1'`WO!2'^>#;?!4#8O#5#4T!1+^70!2,^80O!2'^>#<?!2'^9#2'^:!1,[0-CRN$dst;R+CVM8$d;R+3-CRN$ne;R+CVX8$n;R+3!2,^80!3'f[!1'^5#=Y#1$n;R+5Z$op;R+^;$a;R+C$b;R+CZ$op;R+^;$a;R+C$b;R+CZ$op;R+^<$a;R+C$b;R+CZ$op;R+^<$a;R+C$b;R+CZ$sx;R+1$lo;R+5$n;R+5$e;R+CZ$sx;R+1$k0;R+5$i;R+3$n;R+5Z$n;R+5Z$op;R+^;$a;R+C$b;R+CZ$op;R+^;$a;R+C$b;R+CZ$op;R+^<$a;R+C$b;R+CZ$op;R+^<$a;R+C$b;R+CZ$sx;R+1$lo;R+5$n;R+5$e;R+CZ$sx;R+1$k0;R+5$i;R+3$n;R+5Z-1RN$~R+1V!4'cBS#5#4T2W[!1'^5#<!2,^8+C!2'^>#<;!2'aC,G#4!2'^9#7Q!2'aA^3,G!2,`0#6#5-1RN$~R+1+W^42!2,`E^5X!3,`M^5X^3!4'bA#1#6#5X!4'fZ#<#8^1-1RN$~R+10^22!3,_C+W^6^7^7!2'c2=@!2'c9BD!2'c9FH!5'c7OO#5#4T!2'^P!2'^PR!5'c<OO#5#4T^<-1RN$~R+1V!4'cCO#5#4T2W[!5'c7^0^0#6#5X!4'b?#1#6#5X-1RN$~R+14526-^7RN$x;R!1+^7+3472$ret;R+3-^7RN$x;R!1+^7+3492$c;R+3-1RN$~R+14:26-^IRN$x;R!2+^I+C+34<1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34^92$nlo;R+3-^7RN$x;R!1+^7+34^:2$nhi;R+3-^7RN$x;R!1+^7+34^;2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14^=2P-^7RN$x;R!1+^704^>2$k0;R0-1RN$~R+14^?2!4'fZ#<#8^1-1RN$~R+10^22!3,_C+W^6^@^@66666666-1RN$~R+14^?2^86%e;R+C!1+^7+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14^=2P-^7RN$x;R!1+^704^>2$k0;R0^B66%k;R0%ub;R+C%uk;R+3%un;R+C0!4#9#1#6#5X!1'>!2'aA!1'cU#3#2!1'fY#3!2'eJ#48!1'>!2'aC#1#3!1'^W!2'^>#5;!1'^5#7!2'^>#7?!2'^>#9;!4'fZ#:#7!2,^8+CHF!2'^>#:?!2,^80F-CRN$dst;R+CVH8$d;R+3-CRN$ne;R+CVT8$n;R+3!2,^80!3'f[^0Y#1$n;R+5Z$op;R+^;$a;R+C$b;R+CZ$op;R+^;$a;R+C$b;R+CZ$op;R+^<$a;R+C$b;R+CZ$op;R+^<$a;R+C$b;R+CZ$sx;R+1$lo;R+5$n;R+5$e;R+CZ$sx;R+1$k0;R+5$i;R+3$n;R+5Z$n;R+5Z$op;R+^;$a;R+C$b;R+CZ$op;R+^;$a;R+C$b;R+CZ$op;R+^<$a;R+C$b;R+CZ$op;R+^<$a;R+C$b;R+CZ$sx;R+1$lo;R+5$n;R+5$e;R+CZ$sx;R+1$k0;R+5$i;R+3$n;R+5Z-1RN$~R+1+W^42!2,`E^5T!3,`M^5T^3!4'b?#1#6#5T-1RN$~R+14^G26-^7RN$x;R!1+^7+34^H2$ret;R+3-^7RN$x;R!1+^7+34^I2$c;R+3-1RN$~R+14^J26-^IRN$x;R!2+^I+C+34^K1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34!2'c2^L^M2$nlo;R+3-^7RN$x;R!1+^7+34!2'c9=@2$nhi;R+3-^7RN$x;R!1+^7+34!2'c9B^N2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2^O-1RN$~R+14!2'^P!2'^PR!5'c<FF#5#4^P!5'c7FF#5#4^P2^O-^7RN$x;R!1+^704-1RN$~R+1V!4'cCF#5#4^P2^Q^R2$k0;R0-1RN$~R+14!5'c7OO#6#5T2!4'fZ#;#8N-1RN$~R+10^22!3,_C+W^S^T^T66666666!1'`W3!4'bA#1#6#5T$cs;R+A$entry;R+3$cmax;R+3vdvd!6'_F2!1'c73$b;R2!3+_74-1RN$~R+14526-^7RN$x;R!1+^7+3472$ret;R+3-^7RN$x;R!1+^7+3492$c;R+3-1RN$~R+14:26-^IRN$x;R!2+^I+C+34<1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34A2$nlo;R+3-^7RN$x;R!1+^7+34E2$nhi;R+3-^7RN$x;R!1+^7+34I2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14!2'^P!2'^PR!5'c;SO#5#4TU2P-^7RN$x;R!1+^704\2$k0;R0-1RN$~R+14!4#9^0#6#5X2^866666666^A!6'_F2!1'c<3$b;R2!3+_74-1RN$~R+14526-^7RN$x;R!1+^7+3472$ret;R+3-^7RN$x;R!1+^7+3492$c;R+3-1RN$~R+14:26-^IRN$x;R!2+^I+C+34<1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34A2$nlo;R+3-^7RN$x;R!1+^7+34E2$nhi;R+3-^7RN$x;R!1+^7+34I2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14!2'^P!2'^PRU^<2P-^7RN$x;R!1+^704\2$k0;R0^B6666666^A!6'_F1!1'cC3$b;R1!3+_74-1RN$~R+14526-^7RN$x;R!1+^7+3472$ret;R+3-^7RN$x;R!1+^7+3492$c;R+3-1RN$~R+14:26-^IRN$x;R!2+^I+C+34<1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34A2$nlo;R+3-^7RN$x;R!1+^7+34E2$nhi;R+3-^7RN$x;R!1+^7+34I2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14^=2P-^7RN$x;R!1+^704-1RN$~R+1V!3#8#5#4T2W[2$k0;R0^B6666666^A!6'_F^C!1'c93$o;R^C!3+_74-1RN$~R+14526-^7RN$x;R!1+^7+3472$ret;R+3-^7RN$x;R!1+^7+3492$c;R+3-1RN$~R+14:26-^IRN$x;R!2+^I+C+34<1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34A2$nlo;R+3-^7RN$x;R!1+^7+34!1#6D2$nhi;R+3-^7RN$x;R!1+^7+34!1#7H2$dhi;R+3^D66666^A!6'_F^C!1'c23$o;R^C!3+_74-1RN$~R+14526-^7RN$x;R!1+^7+3472$ret;R+3-^7RN$x;R!1+^7+3492$c;R+3-1RN$~R+14:26-^IRN$x;R!2+^I+C+34<1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34!1#5@2$nlo;R+3-^7RN$x;R!1+^7+34^:2$nhi;R+3-^7RN$x;R!1+^7+34^;2$dhi;R+3^D66666^A!6'_F^E'b?$l;R^E!3+_74-1RN$~R+14526-^7RN$x;R!1+^7+3472$ret;R+3-^7RN$x;R!1+^7+3492$c;R+3-1RN$~R+14:26-^IRN$x;R!2+^I+C+34<1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34^92$nlo;R+3-^7RN$x;R!1+^7+34^:2$nhi;R+3-^7RN$x;R!1+^7+34^;2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14^=2P-^7RN$x;R!1+^704^>2$k0;R0-1RN$~R+14^?2!4'fZ#<#8^1-1RN$~R+10^22!3,_C+W^6^F^F66666666^A!2,_G4^U'bA'f\!1'c0^V!1'c43!1'c8^V!1'c:3!1'cB^V!1'g03!1'c;^V!1'fN3!1'c6^V!1'g13!3+_74-1RN$~R+14^G26-^7RN$x;R!1+^7+34^H2$ret;R+3-^7RN$x;R!1+^7+34^I2$c;R+3-1RN$~R+14^J26-^IRN$x;R!2+^I+C+34^K1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34!2'c0!1'`W^L^M2$nlo;R+3-^7RN$x;R!1+^7+34!2'c8>@2$nhi;R+3-^7RN$x;R!1+^7+34!2'c8C^N2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2^O-1RN$~R+14!2'^P!2'^PR!5'c;GF#5#4^P!5'c6GF#5#4^P2^O-^7RN$x;R!1+^704-1RN$~R+1V!4'cBG#5#4^P2^Q^R2$k0;R0-1RN$~R+14!5'c6SO#6#5T2!4'fZ#;#8N-1RN$~R+10^22!3,_C+W^S^W^W66666666^U!3+_74!3'g2#3#2#1!3'g3#3#2#1").
Qed.


(* [comment removed for export] *)
Fixpoint copy_facts (fuel : nat) (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8e k sb sk with Some _ => true | None => match kread_bytes 8 k sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8e k sb sk with
               | Some v => Some v
               | None => match kread_bytes 8 k sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_facts f k sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookup segs k sb sk 1 false [] [], copy_facts f k sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Fixpoint copy_factsB (bc : bctx) (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8eB bc sb sk with Some _ => true | None => match kread_bytesB bc 8 sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8eB bc sb sk with
               | Some v => Some v
               | None => match kread_bytesB bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_factsB bc f sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookupB segs bc sb sk 1 false [] [], copy_factsB bc f sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Lemma copy_factsB_eqf' : forall fk fuel, copy_factsB (mkbc fk) fuel = copy_facts fuel fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^D0!1+2+W!1+^70%n;R+31%dk;R+32%db;R+C3%sk;R+34%sb;R+C5!1'`W#3!3+_76!2'g47#1!2'g5#1#3!1'`W#4!1'`W#5!1'`W#6!1,_=#2!1,_=#3!1,_=#4!1,_=#5!1,_=#6!1,c?|30;!2'^RA#2!1'`W#:!3'bYC#6#5!1+2+3}8!4'dICF#6#5!1+^7+C!2,^8+C#1!2,^8+C!1,F!1'dP#1!1,[+C!2'^S#6A!2'^S#4A!2'aD#3A!2,^80!3,_C+W!3,`D!2,`0#6#5F#2#1!1,[0!1,c?,dL!2'^RQ#2}1!1,Y+1!1,Y+`U!8'bT/segs;C#6#5S,6TU!1+2+`U!1+2+1!2'^S#8Q!2'^S#6Q!2'aD#5Q!2,^80!3,_C+W!3,`D!2,`0#8#7S#4#1!2,^80!1,Y+W!3'bZ#:#6#5!4'dJF#:#6#5-^7RN$x;R!1+^7E+1^22$l;RE,^U,6!2'^PB-^7RN$x;R!1+^7+C+1^12$e;R+C,^U^3-^7RN$x;R!1+^7EH^22$bs;REJK-^7RN$x;R!1+^701!7'g5#9#;#7L#5MN2$rest;R0OP-^7RN$x;R!1+^7+C1-^7RN$x;R!1+^7+CH^12$v;R+CI^52$v;R+C^6P-2RN$scs;R!1+2+`U1#22-^7RN$x;R!1+^701!7'g5#;#=#9Y#7Z[2$rest;R0\P$s;R+`U$l;R!1+2+`UP-1RN$~R+11^42^7-1RN$~R+11R2-bSRN$x;R+bS1!8'bW/segs;#:#6#5S,6TU3$v;R+C$scs;RW$hints;RX^8$scs;RW$hints;RXPP^0%fuel;R+5%b;R+C%off;R+3!1+^7E!3#1F#6#5-1RN$~R+11R2-bSRN$x;R+bS1V3$v;R+C$scs;RW$hints;RX^8$scs;RW$hints;RXPP^0%b;R+C%off;R+3H!2#1#6#5%rb;R+C%rk;R+3%n;R+5%sx;R+1%hints;R!1+2+1%acc;R!1+2+`U+bS!3'bZ#9#5#4!4'dJF#9#5#4!1'`W#9!1,_=#7$fk;R0$fuel;R+5!4'dH$fuel;R+58!5'aE+C5!2'g4!1'`W#2,dK!2'g5,dK#2$x;R+C!5'aE+34!3'g47,dK#1!3'g5,dK#3#1$x0;R+3!5'aE+C3!4'g49,dK#2#1!4'g5,dK#4#2#1$x1;R+C!5'aE+32!5'g4:,dK#3#2#1!5'g5,dK#5#3#2#1$x2;R+3!5'aE+31!6'g4;,dK#4#3#2#1!6'g5,dK#6#4#3#2#1$x3;R+3!2,_G1!7'g5,dK#7#5#4#3#2#1$f;R+5$IH;R8!5'aE+C5!2'g49<!2'g5<#4$x;R+C!5'aE+34!3'g4:=#1!3'g5=#5#1$x0;R+3!5'aE+C3!4'g4;>#2#1!4'g5>#6#2#1$x1;R+C!5'aE+32!5'g4!1'`W#7?#3#2#1!5'g5?#7#3#2#1$x2;R+3!5'aE+31!6'g4!1'`W#8@#4#3#2#1!6'g5@#8#4#3#2#1$x3;R+3vd!6'_F6!2'g5#7#9$o;R6!3+_71-1RN$~R+11!2'^PB-^7RN$x;R!1+^7+C+1D2$e;R+C,^U-^7RN$x;R!1+^7E+1G2$l;RE,^U,62-^7RN$x;R!1+^7+C1-^7RN$x;R!1+^7+CHD2$v;R+CI-^7RN$x;R!1+^7EHG2$bs;REJK2$v;R+C-^7RN$x;R!1+^701!5#2#7L#5MN2$rest;R0OPP-1RN$~R+11R2-bSRN$x;R+bS1V3$v;R+C$scs;RW$hints;RX-2RN$scs;R!1+2+`U1#22-^7RN$x;R!1+^701!5#4#9Y#7Z[2$rest;R0\P$s;R+`U$l;R!1+2+`UP$scs;RW$hints;RXPP^0^9!6'_F^:$fuel;R+5!2'dJ#1#:$o;R^:!3+_71-1RN$~R+11!2'^PB-^7RN$x;R!1+^7+C+1D2$e;R+C,^U-^7RN$x;R!1+^7E+1^;2$l;RE,^U,62-^7RN$x;R!1+^7+C1-^7RN$x;R!1+^7+CHD2$v;R+CI-^7RN$x;R!1+^7EH^;2$bs;REJK2$v;R+C^6P^<^9!6'_F^=!1'bZ#9$o;R^=!3+_71-1RN$~R+11!2'^PB-^7RN$x;R!1+^7+C+1^>2$e;R+C,^U^32-^7RN$x;R!1+^7+C1-^7RN$x;R!1+^7+CH^>2$v;R+CI^52$v;R+C^6P^<^9!6'_F^?!2'bW/segs;#9$l;R^?!3+_71-1RN$~R+11^42^7-1RN$~R+11R2-bSRN$x;R+bS1!6#1#6#5S,6TU3$v;R+C$scs;RW$hints;RX^8$scs;RW$hints;RXPP^0^9!2,_G1-1RN$~R+11!2'^P!2'^RA#1-^7RN$x;R!1+^7+C+1^@2$e;R+C,^U-^7RN$x;R!1+^7E+1^A2$l;RE,^U,62-^7RN$x;R!1+^7+C1-^7RN$x;R!1+^7+CH^@2$v;R+CI-^7RN$x;R!1+^7EH^A2$bs;REJK2$v;R+C-^7RN$x;R!1+^701!7'g5#8#:#6!2'^S#5A#4!2'^S#3A!2'aD#2A2$rest;R0!2,^80!3,_C+W!3,`D!2,`0#5#4F#2#1PP-1RN$~R+11!2'^RQ#12-bSRN$x;R+bS1!8'bW/segs;#9#5#4S,6TU3$v;R+C$scs;RW$hints;RX-2RN$scs;R!1+2+`U1#22-^7RN$x;R!1+^701!7'g5#:#<#8!2'^S#7Q#6!2'^S#5Q!2'aD#4Q2$rest;R0!2,^80!3,_C+W!3,`D!2,`0#7#6S#4#1P$s;R+`U$l;R!1+2+`UP$scs;RW$hints;RXPP^0!2'bT/segs;^B!2'bX#9/segs;!1'bY^B!1'g6#9!1'dI^B!1'g7#9!2'g4^B#7#6!3+_71!7'g4^B^C#5#4#3#2#1!7'g5^C#9#5#4#3#2#1#1").
Qed.
Lemma copy_factsB_eqf : forall fk, copy_factsB (mkbc fk) = (fun fuel => copy_facts fuel fk).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10!1+2+W$fk;R0!5'aE+5%sb;R+C%sk;R+3%db;R+C%dk;R+3%n;R+3!1+^70!1'g4!1'`W#1$fuel;R+5!2'g5#1#2$fuel;R+5!2'g8#2#1").
Qed.
#[local] Hint Rewrite copy_factsB_eqf' copy_factsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kblob_prefix (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (nlo : Z) : list kentry :=
  match List.find (fun K => match K with
                             | KBlob (SA b o) (ELit n0) _ => expr_eqb b sb && Z.eqb o sk && Z.ltb 0 n0 && Z.leb n0 nlo
                             | _ => false
                             end) k with
  | Some (KBlob _ (ELit n0) j) => [KBlob (SA db dk) (ELit n0) j]
  | _ => []
  end.

Definition summary_copy_ref (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo k ne, xhi k ne, xhi k dst, xhi k src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_x k k db dk ne && ranges_apart_x k db dk ne sb sk ne)%bool then
              let k1 := kn_havoc k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_x k k sb sk ne && flat_x k sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_x k k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_x k sb sk ne)%bool then
                         match copy_facts (Z.to_nat nhi) k sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ k1)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_copy (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xloB bc ne, xhiB bc ne, xhiB bc dst, xhiB bc src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := kn_havocM k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_xB bc k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_xB bc sb sk ne)%bool then
                         match copy_factsB bc (Z.to_nat nhi) sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ k1)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_copy_eq : forall cs entry, summary_copy cs entry = summary_copy_ref cs entry.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SaH0!1+2+W!1+^70%fuel;R+5%sb;R+C%sk;R+3%db;R+C%dk;R+3%n;R+31!1+^7+A!1'>!2'aA!1'cU#3#2!1,[+A!1'fY#3}:!1'^W!2'^>#47};!1'^W!2'^>#69!1'^5#8!1'`W;}<!2'^>#8=!2'c0<>!1'^5#9!1'`W@!2'^>#9=!2'c8AB!1'^5#:!1'`WD!2'^>#:7!2'c8EF!1'^5#;!1'`WH!2'^>#;9!2'c8IJ|10;!2'^P!2'^P!2'^P!2'^R,G#4!2'^R#3!2'dQ!1,c?L!1,c?|508;!2'aC!2'^S#2#3'^:!2'aC!2'^S#1#3'^:!2'aA#3,G!2'^>#<7!2,^8+CO!1'^5#<!4'fZ#<#9PQ!1'`WQ!2'^>#<=!2,^80Q!2'^>#==!1'^5#>!2'^9#2'^:!1,[0-CRN$dst;R+C1O8$d;R+3-CRN$ne;R+C1V8$n;R+3!2,^80!3'f[WX#1$n;R+5Y$op;R+^;$a;R+C$b;R+CY$op;R+^;$a;R+C$b;R+CY$op;R+^<$a;R+C$b;R+CY$op;R+^<$a;R+C$b;R+CY$sx;R+1$lo;R+5$n;R+5$e;R+CY$sx;R+1$k0;R+5$i;R+3$n;R+5Y$n;R+5Y$op;R+^;$a;R+C$b;R+CY$op;R+^;$a;R+C$b;R+CY$op;R+^<$a;R+C$b;R+CY$op;R+^<$a;R+C$b;R+CY$sx;R+1$lo;R+5$n;R+5$e;R+CY$sx;R+1$k0;R+5$i;R+3$n;R+5Y-1RN$~R+11!4'cBS#8#7T2UZ!1'^5#=!1'`W\!7'aB^0#9#8V#7#6V!2'^P!5'c6^0\#9#8V^1!2'aC,G#5!2'^P^3!5'c;^0\#7#6V!2,^8+C!2'^>#=7!2,`0#9#8!2,`E^6V!4'fZ#=#:^5!3,_C+W^7!4'bA#1#9#8V!2'^R#5!1,c?|;000;!1'`WW!2'^>#>=!4'cE^:#8#7^;!1'g9#5!2,^8+C!2'^>#?7!2'^>#?=!4'fZ#?#<^>!3'^4+W#1!4'bA#3#;#:^?!5'c6^:W#8#7^;!2,^8+C!2'^>#>7|30;!1,c?^C!2'g;^D!1'^T#1!2,`0#;!2'^S#:^E}8|800;!1,c?^H-1RN$~R+1+5!2'^P!2'^P!2'^P!2'aA#6#5!2'aA!2'^9#5^D,G!2'^R#5^I^32!1'g9!2'dV#5^D,dK!2'd\,dK^J!4'fD+5+W$i;R+5!3,`D^F^G!1,_R!2'^6!2'^6!1'dS#?'g<#1^K!6'g=W#8#7#:#9#6!2'aC,G#6!2,`0#:#9!2,`N^O^;!4'bA#2#:#9^;!5'g:#>#;^B!3'^4+W^L!3'^4+W^M-1RN$~R+10^N2!3,_C+W^P^Q^Q^J-1RN$~R+13!2'^P^A^<2^R5!1'^5#@!1'`W^T!2'^>#@=!5'c6^U^T#:#9^V!2,^8+C!2'^>#@7!2,`0#=!2'^S#<^E!1,_R!2'^6!2'^6!1'dS#A'g<#1-1RN$~R+1+5!2'^P!2'^P!2'^P!2'aA#8#7!2'aA!2'^9#7^D,G!2'^R#7^I!2'aC,G#72!1'g9!2'dV#7^D,dK!2'd\,dK^[!4'fD+5+W$i;R+5!3,`D^Y^G^Z^\!6'g=^T#:#9#<#;#8!2'aC,G#8!2,`0#<#;!2,`N_3^V!4'bA#4#<#;^V!5'g:#@#=^X!3'^4+W_0!3'^4+W_1-1RN$~R+10_22!3,_C+W_4_5_5^[-1RN$~R+13!2'^P^W!4'cE^U#:#9^V2_65!1'^5#A!1'`W_8!2'^>#A=!5'c6_9_8#;#:_:!2,^8+C!2'^>#A7!2,`0#>!2'^S#=^E-1RN$~R+1+5!2'^P!2'^P!2'^P!2'aA#9#8!2'aA!2'^9#8^D,G!2'^R#8^I_22!1'g9!2'dV#8^D,dK!2'd\,dK_>!4'fD+5+W$i;R+5!3,`D_=^G!1,_R!2'^6!2'^6!1'dS#B'g<#1_?!6'g=_8#;#:#=#<#9!2'aC,G#9!2,`0#=#<!2,`N_C_:!4'bA#5#=#<_:!5'g:#A#>_<!3'^4+W_@!3'^4+W_A-1RN$~R+10_B2!3,_C+W_D_E_E_>-1RN$~R+13!2'^P_;!4'cE_9#;#:_:2_F5!2'c2;>!2'c9@B!2'c9DF!2'c9HJ-1RN$~R+11!4'cCQ#8#7T2UZ!5'c7\\#9#8V!2'^P_M!7'aH\#9#8V#7#6V!2'^P^3!5'c<\\#7#6V!4'cFW#8#7^;!2'^P^9_P!7'g5^=W#8#7#:#9#5!2'^P!5'c7WW#8#7^;_P!4'b?#2#:#9^;-1RN$~R+13_S2!5'g:#>#;^B!3'^4+W^L!3'^4+W^M-1RN$~R+10^N2!3,_C+W^P_T_T^J5!4'cF^T#:#9^V!2'^P!5'c7^T^T#:#9^V_V!4'b?#4#<#;^V-1RN$~R+13_W2!5'g:#@#=^X!3'^4+W_0!3'^4+W_1-1RN$~R+10_22!3,_C+W_4_X_X^[5!4'cF_8#;#:_:!2'^P!5'c7_8_8#;#:_:_Z!4'b?#5#=#<_:-1RN$~R+13_[2!5'g:#A#>_<!3'^4+W_@!3'^4+W_A-1RN$~R+10_B2!3,_C+W_D_\_\_>5-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33_H2$nlo;R+3-^7RN$x;R!1+^7+33_I2$nhi;R+3-^7RN$x;R!1+^7+33_J2$dhi;R+3-^7RN$x;R!1+^7+33_K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703_L2$k0;R0-1RN$~R+13_N2-1RN$~R+13_O2!4'fZ#=#:^5!3,_C+W^7!4'b?#1#9#8V-CRN$ne;R+C3V8$z;R+3-1RN$~R+13_Q2-^7RN$x;R!1+^703_R2$kc;R0!4'fZ#?#<^>!3'^4+W#1!4'b?#3#;#:^?_U_U$n;R+5_U$op;R+^;$a;R+C$b;R+C_Y$op;R+^;$a;R+C$b;R+C_Y$op;R+^<$a;R+C$b;R+C_Y$op;R+^<$a;R+C$b;R+C_Y$sx;R+1$lo;R+5$n;R+5$e;R+C`0$sx;R+1$k2;R+5$i;R+3$n;R+5`055555555%b;R+C%off;R+3%n;R+C+1!1'^5#2!3#<#8#7^;-1RN$~R+13!2'^P^A`42^R5-1RN$~R+13!2'^P^W!3#>#:#9^V2_65-1RN$~R+13!2'^P_;!3#?#;#:_:2_F5%k;R0`2-1RN$~R+13!2'^P!4#<W#8#7^;_P2^R5-1RN$~R+13!2'^P!4#>^T#:#9^V_V2_65-1RN$~R+13!2'^P!4#?_8#;#:_:_Z2_F5!2'^P_M^1-1RN$~R+13_S2^R5-1RN$~R+13_W2_65-1RN$~R+13_[2_F5-CRN$ne;R+C3V8$z;R+3-1RN$~R+13_Q2-^7RN$x;R!1+^703_R2$kc;R0^@`=`=$n;R+5`=$op;R+^;$a;R+C$b;R+C`>$op;R+^;$a;R+C$b;R+C`>$op;R+^<$a;R+C$b;R+C`>$op;R+^<$a;R+C$b;R+C`>$sx;R+1$lo;R+5$n;R+5$e;R+C`?$sx;R+1$k2;R+5$i;R+3$n;R+5`?-1RN$~R+13_O2^8`@%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1%e;R+C!1+^7+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703_L2$k0;R0-1RN$~R+13_N2`A555%k;R0%ub;R+C%uk;R+3%un;R+C0!4#<#2#:#9^;-1RN$~R+13_S2!5'g:#>#;^B!3'^4+W^L!3'^4+W^M-1RN$~R+10^N2!3,_C+W^P`F`F^J5!4#>#4#<#;^V-1RN$~R+13_W2!5'g:#@#=^X!3'^4+W_0!3'^4+W_1-1RN$~R+10_22!3,_C+W_4`H`H^[5!4#?#5#=#<_:-1RN$~R+13_[2!5'g:#A#>_<!3'^4+W_@!3'^4+W_A-1RN$~R+10_B2!3,_C+W_D`J`J_>5!1'>!2'aA!1'cU#2#1!1'fY#2!1'^W!2'^>#37!1'^W!2'^>#59!1'^5#7!2'^>#7=!2'^>#97!2'^>#:9!2'^>#;7!4'fZ#;#9!2,^8+C`TH!2'^>#;=!2,^80H-CRN$dst;R+C1`T8$d;R+3-CRN$ne;R+C1T8$n;R+3!2,^80!3'f[\X#1$n;R+5Y$op;R+^;$a;R+C$b;R+CY$op;R+^;$a;R+C$b;R+CY$op;R+^<$a;R+C$b;R+CY$op;R+^<$a;R+C$b;R+CY$sx;R+1$lo;R+5$n;R+5$e;R+CY$sx;R+1$k0;R+5$i;R+3$n;R+5Y$n;R+5Y$op;R+^;$a;R+C$b;R+CY$op;R+^;$a;R+C$b;R+CY$op;R+^<$a;R+C$b;R+CY$op;R+^<$a;R+C$b;R+CY$sx;R+1$lo;R+5$n;R+5$e;R+CY$sx;R+1$k0;R+5$i;R+3$n;R+5Y!2,`E^6T!4'cF\#8#7V!4'fD+5+W$i;R+5!3,`D^F^G!1,_R!2'^6!2'^6!1'dS#>'g<#1^K!6'g=\#8#7#:#9#6!2,`N^OV!4'b?#2#:#9V-1RN$~R+13!2'^P!5'c7\\#8#7V`Z2!5'g:#=#;^5!3'^4+W`[!3'^4+W`\-1RN$~R+10^N2!3,_C+Wa0a1a1^J5!1'^5#?!4'fD+5+W$i;R+5!3,`D^Y^G!1,_R!2'^6!2'^6!1'dS#@'g<#1^\!6'g=a3#:#9#<#;#8!2,`N_3^?!4'b?#4#<#;^?-1RN$~R+13!2'^P!5'c7a3a3#:#9^?!4'cFa3#:#9^?2!5'g:#?#=^>!3'^4+Wa4!3'^4+Wa5-1RN$~R+10_22!3,_C+Wa6a7a7^[5!4'fD+5+W$i;R+5!3,`D_=^G^Z_?!6'g=^T#;#:#=#<#9!2,`N_C^V!4'b?#5#=#<^V-1RN$~R+13!2'^P!5'c7^T^T#;#:^V!4'cF^T#;#:^V2!5'g:#@#>^X!3'^4+Wa9!3'^4+Wa:-1RN$~R+10_B2!3,_C+Wa;a<a<_>5-1RN$~R+13`L25-^7RN$x;R!1+^7+33`M2$ret;R+3-^IRN$x;R!2+^I+C+33`N1$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33`O1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33!2'c2`P`Q2$nlo;R+3-^7RN$x;R!1+^7+33!2'c9;>2$nhi;R+3-^7RN$x;R!1+^7+33!2'c9@`R2$dhi;R+3-^7RN$x;R!1+^7+33!2'c9D`S2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2`U-^7RN$x;R!1+^703-1RN$~R+11!4'cCH#8#7`V2`W`X2$k0;R0-1RN$~R+13!2'^P!5'c7QQ#9#8T!7'aHQ#9#8T#7#6T2-1RN$~R+13!2'^P^3!5'c<QQ#7#6T2!4'fZ#<#:P!3,_C+W`Y!4'b?#1#9#8T-CRN$ne;R+C3T8$z;R+3-1RN$~R+13!2'^P^9`Z2-^7RN$x;R!1+^703!7'g5^=\#8#7#:#9#52$kc;R0!4'fZ#>#<^B!3'^4+W#1!4'b?#3#;#:^;a2a2$n;R+5a2$op;R+^;$a;R+C$b;R+Ca8$op;R+^;$a;R+C$b;R+Ca8$op;R+^<$a;R+C$b;R+Ca8$op;R+^<$a;R+C$b;R+Ca8$sx;R+1$lo;R+5$n;R+5$e;R+Ca=$sx;R+1$k2;R+5$i;R+3$n;R+5a=55555555!1'`W`3!4'cE^0#8#7V!4'bA#2#:#9V-1RN$~R+13!2'^P!5'c6^0\#8#7Va@2!5'g:#=#;^5!3'^4+W`[!3'^4+W`\-1RN$~R+10^N2!3,_C+Wa0aAaA^J5!1'`Wa3!4'bA#4#<#;^?-1RN$~R+13!2'^P!5'c6aCa3#:#9^?!4'cEaC#:#9^?2!5'g:#?#=^>!3'^4+Wa4!3'^4+Wa5-1RN$~R+10_22!3,_C+Wa6aDaD^[5!4'bA#5#=#<^V-1RN$~R+13!2'^P!5'c6^U^T#;#:^V!4'cE^U#;#:^V2!5'g:#@#>^X!3'^4+Wa9!3'^4+Wa:-1RN$~R+10_B2!3,_C+Wa;aFaF_>5$cs;R+A$entry;R+3vdvd!6'_F2$fuel;R+5!2'g5#1!1'^5#3$o;R2!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33?2$nlo;R+3-^7RN$x;R!1+^7+33C2$nhi;R+3-^7RN$x;R!1+^7+33G2$dhi;R+3-^7RN$x;R!1+^7+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703[2$k0;R0-1RN$~R+13^22-1RN$~R+13^42^8-CRN$ne;R+C3V8$z;R+3-1RN$~R+13!2'^P^9^<2-^7RN$x;R!1+^703!6#<^=#8#7#:#9#52$kc;R0^@^S^S$n;R+5^S$op;R+^;$a;R+C$b;R+C_7$op;R+^;$a;R+C$b;R+C_7$op;R+^<$a;R+C$b;R+C_7$op;R+^<$a;R+C$b;R+C_7$sx;R+1$lo;R+5$n;R+5$e;R+C_G$sx;R+1$k2;R+5$i;R+3$n;R+5_G55555555`1!6'_F`2!1'cF`3$b;R`2!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33?2$nlo;R+3-^7RN$x;R!1+^7+33C2$nhi;R+3-^7RN$x;R!1+^7+33G2$dhi;R+3-^7RN$x;R!1+^7+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703[2$k0;R0-1RN$~R+13^22-1RN$~R+13^42^8-CRN$ne;R+C3V8$z;R+3-1RN$~R+13!2'^P^9`42-^7RN$x;R!1+^703_R2$kc;R0^@`5`5$n;R+5`5$op;R+^;$a;R+C$b;R+C`6$op;R+^;$a;R+C$b;R+C`6$op;R+^<$a;R+C$b;R+C`6$op;R+^<$a;R+C$b;R+C`6$sx;R+1$lo;R+5$n;R+5$e;R+C`7$sx;R+1$k2;R+5$i;R+3$n;R+5`755555555`1!6'_F`8!1'c7`3$b;R`8!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33?2$nlo;R+3-^7RN$x;R!1+^7+33C2$nhi;R+3-^7RN$x;R!1+^7+33G2$dhi;R+3-^7RN$x;R!1+^7+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703[2$k0;R0-1RN$~R+13!2'^P!4#;\#9#8V^12-1RN$~R+13^42^8-CRN$ne;R+C3V8$z;R+3-1RN$~R+13_Q2-^7RN$x;R!1+^703_R2$kc;R0^@`9`9$n;R+5`9$op;R+^;$a;R+C$b;R+C`:$op;R+^;$a;R+C$b;R+C`:$op;R+^<$a;R+C$b;R+C`:$op;R+^<$a;R+C$b;R+C`:$sx;R+1$lo;R+5$n;R+5$e;R+C`;$sx;R+1$k2;R+5$i;R+3$n;R+5`;55555555`1!6'_F`8!1'c<`3$b;R`8!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33?2$nlo;R+3-^7RN$x;R!1+^7+33C2$nhi;R+3-^7RN$x;R!1+^7+33G2$dhi;R+3-^7RN$x;R!1+^7+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703[2$k0;R0-1RN$~R+13`<2-1RN$~R+13!2'^P^3!4#;\#7#6V2^8`@55555555`1!6'_F`2!1'cC`3$b;R`2!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33?2$nlo;R+3-^7RN$x;R!1+^7+33C2$nhi;R+3-^7RN$x;R!1+^7+33G2$dhi;R+3-^7RN$x;R!1+^7+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703-1RN$~R+11!3#:#8#7T2UZ2$k0;R0-1RN$~R+13`<2`A55555555`1!6'_F`B!1'aH`3$b;R`B!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33?2$nlo;R+3-^7RN$x;R!1+^7+33C2$nhi;R+3-^7RN$x;R!1+^7+33G2$dhi;R+3-^7RN$x;R!1+^7+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703_L2$k0;R0-1RN$~R+13!2'^P_M!6#;#9#8V#7#6V2`A55555555`1!6'_F`C!1'c9`3$o;R`C!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33?2$nlo;R+3-^7RN$x;R!1+^7+33!1#7B2$nhi;R+3-^7RN$x;R!1+^7+33!1#8F2$dhi;R+3-^7RN$x;R!1+^7+33!1#9J2$shi;R+3`D55555`1!6'_F`C!1'c2`3$o;R`C!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33!1#6>2$nlo;R+3-^7RN$x;R!1+^7+33_I2$nhi;R+3-^7RN$x;R!1+^7+33_J2$dhi;R+3-^7RN$x;R!1+^7+33_K2$shi;R+3`D55555`1!6'_F`E'b?$l;R`E!3+_73-1RN$~R+13425-^7RN$x;R!1+^7+3362$ret;R+3-^IRN$x;R!2+^I+C+3381$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33:1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33_H2$nlo;R+3-^7RN$x;R!1+^7+33_I2$nhi;R+3-^7RN$x;R!1+^7+33_J2$dhi;R+3-^7RN$x;R!1+^7+33_K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^7RN$x;R!1+^703_L2$k0;R0-1RN$~R+13_N2-1RN$~R+13_O2!4'fZ#=#:^5!3,_C+W^7!4#;#1#9#8V-CRN$ne;R+C3V8$z;R+3-1RN$~R+13_Q2-^7RN$x;R!1+^703_R2$kc;R0!4'fZ#?#<^>!3'^4+W#1!4#=#3#;#:^?`G`G$n;R+5`G$op;R+^;$a;R+C$b;R+C`I$op;R+^;$a;R+C$b;R+C`I$op;R+^<$a;R+C$b;R+C`I$op;R+^<$a;R+C$b;R+C`I$sx;R+1$lo;R+5$n;R+5$e;R+C`K$sx;R+1$k2;R+5$i;R+3$n;R+5`K55555555`1!2,_G3a>'bA'f\!1'c0a?!1'c4`3!1'c8a?!1'c:`3!1'aBa?!1'aI`3!1'cBa?!1'g0`3!1'c;a?!1'fN`3!1'c6a?!1'g1`3!1'cEa?!1'eC`3!1'g4a?!1'g>`3!3+_73-1RN$~R+13`L25-^7RN$x;R!1+^7+33`M2$ret;R+3-^IRN$x;R!2+^I+C+33`N1$db;R+C$dk;R+3-^IRN$x;R!2+^I+C+33`O1$sb;R+C$sk;R+3-^7RN$x;R!1+^7+33!2'c0!1'`W`P`Q2$nlo;R+3-^7RN$x;R!1+^7+33!2'c8<>2$nhi;R+3-^7RN$x;R!1+^7+33!2'c8A`R2$dhi;R+3-^7RN$x;R!1+^7+33!2'c8E`S2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2`U-^7RN$x;R!1+^703-1RN$~R+11!4'cBI#8#7`V2`W`X2$k0;R0-1RN$~R+13!2'^P!5'c6SQ#9#8T!7'aBS#9#8T#7#6T2-1RN$~R+13!2'^P^3!5'c;SQ#7#6T2!4'fZ#<#:P!3,_C+W`Y!4'bA#1#9#8T-CRN$ne;R+C3T8$z;R+3-1RN$~R+13!2'^P^9a@2-^7RN$x;R!1+^703!7'g4^0^=#8#7#:#9#52$kc;R0!4'fZ#>#<^B!3'^4+W#1!4'bA#3#;#:^;aBaB$n;R+5aB$op;R+^;$a;R+C$b;R+CaE$op;R+^;$a;R+C$b;R+CaE$op;R+^<$a;R+C$b;R+CaE$op;R+^<$a;R+C$b;R+CaE$sx;R+1$lo;R+5$n;R+5$e;R+CaG$sx;R+1$k2;R+5$i;R+3$n;R+5aG55555555a>!3+_73!2'g?#2#1!2'g@#2#1").
Qed.


(* [comment removed for export] *)
Definition summary_miz_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xlo k ne, xhi k ne, xhi k beg, xlo k sp, xhi k sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritable k k qb qk 16
              && ranges_apart_x k qb qk (ELit 16) bb bk ne && kzero_x k k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havoc k qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_miz (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xloB bc ne, xhiB bc ne, xhiB bc beg, xloB bc sp, xhiB bc sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritableB bc k qb qk 16
              && ranges_apart_xB bc qb qk (ELit 16) bb bk ne && kzero_xB bc k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havocB bc qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_miz_eq : forall cs, summary_miz cs = summary_miz_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^H0!1+2+W%ub;R+C%uk;R+3%un;R+C0!1'^5#1!1+^7+A!1'gA/A;!1'>!2'aA!1'cU#24!1,[+A!1'fY#2}:!1'^W!2'^>#38}2|40;!1,gC;!1'^W!2'gB!2'^>#5:<!1'^5#7!1'`W>};!2'^>#7@!2'c0?A!1'^5#8!1'`WC!2'^>#8@!2'c8DE!1'^5#9!1'`WG!2'^>#98!2'c8HI!1'^5#:!1'`WK!2'^>#::!2'c0LM!1'^5#;!1'`WO!2'^>#;:!2'c8PQ|10;|30;!1,c?;!2'^P!2'^P!2'^P!2'^P!2'^R,G#5!2'^R#4!2'dQ!1,c?S!1,c?|508;!2'^R!2'^S!2'^S#3#4!1,c?T'^:!2'^RU#2!2'aC#1'^:!1'^5#<!1'`WW!1,FU!2'^>#<@!7'aBX#7#6Y#9#8Z!5'c;XW#9#8Z!2,^8+C!1,F!1,c?,dL!2'c9CE!2'c9GI!2'^PV!5'b\WW#7#6U!5'c<WW#9#8Z!4'fZ#<#:^0!4'b?W#7#6Y-1RN$~R+13!2'^P!2'^P^3!7'aHW#7#6Y#9#8Z^42^56-^7RN$x;R!1+^7+33!2'c9OQ2$sphi;R+3^66-1RN$~R+13526-^7RN$x;R!1+^7+3372$ret;R+3-^IRN$x;R!2+^I+C+3391$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33=1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33!2'c2>A2$nlo;R+3-^7RN$x;R!1+^7+33^12$nhi;R+3-^7RN$x;R!1+^7+33^22$bhi;R+3-^7RN$x;R!1+^7+33!2'c2KM2$splo;R+3^766666%k;R0%b;R+C%off;R+3%n;R+3+1%k;R0%b;R+C%off;R+3%n;R+C+1%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1%e;R+C!1+^7+3!1'>!2'aA!1'cU#14!1'fY#1!1'^W!2'^>#28!1'^W!2'gB!2'^>#4:<!1'^5#6!2'^>#6@!2'^>#88!2'^>#9:!2'^>#;@-1RN$~R+13^=26-^7RN$x;R!1+^7+33^>2$ret;R+3-^IRN$x;R!2+^I+C+33^?1$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33^@1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33!2'c2^A^B2$nlo;R+3-^7RN$x;R!1+^7+33!2'c9>A2$nhi;R+3-^7RN$x;R!1+^7+33!2'c9C^C2$bhi;R+3-^7RN$x;R!1+^7+33!2'c2G^D2$splo;R+3-^7RN$x;R!1+^7+33!2'c9KM2$sphi;R+3-1RN$~R+13!2'^P!2'^P!2'^PV!5'b\OO#7#6U!7'aHO#7#6Y#9#8^E!5'c<OO#9#8^E2!4'fZ#;#:^0!4'b?O#7#6Y6666666!1'`W2$cs;R+Avdvd!6'_F1!1'b?2$l;R1!3+_73-1RN$~R+13526-^7RN$x;R!1+^7+3372$ret;R+3-^IRN$x;R!2+^I+C+3391$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33=1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33B2$nlo;R+3-^7RN$x;R!1+^7+33F2$nhi;R+3-^7RN$x;R!1+^7+33J2$bhi;R+3-^7RN$x;R!1+^7+33N2$splo;R+3-^7RN$x;R!1+^7+33R2$sphi;R+3-1RN$~R+13!2'^P!2'^P!2'^PV!5'b[XW#7#6U[\2!4'fZ#<#:^0!3#;#7#6Y6666666^8!6'_F^9!1'b\2$b;R^9!3+_73-1RN$~R+13526-^7RN$x;R!1+^7+3372$ret;R+3-^IRN$x;R!2+^I+C+3391$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33=1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33B2$nlo;R+3-^7RN$x;R!1+^7+33F2$nhi;R+3-^7RN$x;R!1+^7+33J2$bhi;R+3-^7RN$x;R!1+^7+33N2$splo;R+3-^7RN$x;R!1+^7+33R2$sphi;R+3-1RN$~R+13!2'^P!2'^P!2'^PV!4#;W#7#6U[\2^56666666^8!6'_F^:!1'c<2$b;R^:!3+_73-1RN$~R+13526-^7RN$x;R!1+^7+3372$ret;R+3-^IRN$x;R!2+^I+C+3391$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33=1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33B2$nlo;R+3-^7RN$x;R!1+^7+33F2$nhi;R+3-^7RN$x;R!1+^7+33J2$bhi;R+3-^7RN$x;R!1+^7+33N2$splo;R+3-^7RN$x;R!1+^7+33R2$sphi;R+3-1RN$~R+13!2'^P!2'^P^3[!4#;W#9#8Z2^56666666^8!6'_F^;!1'aH2$b;R^;!3+_73-1RN$~R+13526-^7RN$x;R!1+^7+3372$ret;R+3-^IRN$x;R!2+^I+C+3391$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33=1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33B2$nlo;R+3-^7RN$x;R!1+^7+33F2$nhi;R+3-^7RN$x;R!1+^7+33J2$bhi;R+3-^7RN$x;R!1+^7+33N2$splo;R+3-^7RN$x;R!1+^7+33R2$sphi;R+3-1RN$~R+13!2'^P!2'^P^3!6#;#7#6Y#9#8Z^42^56666666^8!6'_F^<!1'c92$o;R^<!3+_73-1RN$~R+13526-^7RN$x;R!1+^7+3372$ret;R+3-^IRN$x;R!2+^I+C+3391$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33=1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33B2$nlo;R+3-^7RN$x;R!1+^7+33!1#7E2$nhi;R+3-^7RN$x;R!1+^7+33!1#8I2$bhi;R+3-^7RN$x;R!1+^7+33N2$splo;R+3-^7RN$x;R!1+^7+33!1#:Q2$sphi;R+3^6666666^8!6'_F^<!1'c22$o;R^<!3+_73-1RN$~R+13526-^7RN$x;R!1+^7+3372$ret;R+3-^IRN$x;R!2+^I+C+3391$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33=1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33!1#6A2$nlo;R+3-^7RN$x;R!1+^7+33^12$nhi;R+3-^7RN$x;R!1+^7+33^22$bhi;R+3-^7RN$x;R!1+^7+33!1#9M2$splo;R+3^766666^8!2,_G3^F!1'c0^G!1'c42!1'c8^G!1'c:2!1'aB^G!1'aI2!1'c;^G!1'fN2!1'b[^G!1'gD2!1'b>^G!1'bB2!3+_73-1RN$~R+13^=26-^7RN$x;R!1+^7+33^>2$ret;R+3-^IRN$x;R!2+^I+C+33^?1$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+33^@1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+33!2'c0!1'`W^A^B2$nlo;R+3-^7RN$x;R!1+^7+33!2'c8?A2$nhi;R+3-^7RN$x;R!1+^7+33!2'c8D^C2$bhi;R+3-^7RN$x;R!1+^7+33!2'c0H^D2$splo;R+3-^7RN$x;R!1+^7+33!2'c8LM2$sphi;R+3-1RN$~R+13!2'^P!2'^P!2'^PV!5'b[PO#7#6U!7'aBP#7#6Y#9#8^E!5'c;PO#9#8^E2!4'fZ#;#:^0!4'b>P#7#6Y6666666^F!3+_73!1'gE#1!1'gF#1").
Qed.


(* [comment removed for export] *)
Definition img_cov (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.

Definition img_covB (bc : bctx) (a b : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$bc;R+a3$a;R+3$b;R+3!3'^O+W$K;R+W-WRN$K;R+W+1#1:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n;R+C,6$a0;R+\$n;R+C$k;R+5,6$lo;R+3$hi;R+3!2'^P!2'^R#2#5!2'^R#4#1$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n;R+C$c;R+3,6$a0;R+\$n;R+C,6!1'aR#3").
Lemma img_covB_eqf : forall fk, img_covB (mkbc fk) = img_cov fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S30!1+2+W!2'^P!2'^R#2#6!2'^R#5#1!1'`W#3$fk;R0!5'aE+3%b;R+3+1!1'gG!1'`W#1!1'gH#1$x;R+3!5'aE+3+1!2'gG!1'`W#2#1!2'gH#2#1$x0;R+3vd!6'_F0#3$l;R0!3+_7+1!3'^O+W$K;R+W-WRN$K;R+W+1#1:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n;R+C,6$a0;R+\$n;R+C$k;R+5,6$lo;R+3$hi;R+31$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n;R+C$c;R+3,6$a0;R+\$n;R+C,6#1!3'^O+W$K;R+W-WRN$K;R+W+1#1:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n;R+C,6$a0;R+\$n;R+C$k0;R+5,6$lo;R+3$hi;R+31$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n;R+C$c;R+3,6$a0;R+\$n;R+C,6#4!2,_G+1!3'^O+W$K;R+W-WRN$K;R+W+1#1:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n;R+C,6$a0;R+\$n;R+C$k0;R+5,6$lo;R+3$hi;R+3!2'^P!2'^R#2#5!2'^R#4#1$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n;R+C$c;R+3,6$a0;R+\$n;R+C,6#3!1'aR2!1'aV#3!3+_7+1!3'gG2#2#1!3'gH#3#2#1").
Qed.
#[local] Hint Rewrite img_covB_eqf : bceq.



(* [comment removed for export] *)
Definition SEALED_W : Z := 0x3e64656c6165733c.

(* [comment removed for export] *)
Definition summary_istrncpy_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhi k dst with
      | Some dhi =>
          match (if off_image_x k db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_x k k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_x k db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havoc k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_istrncpy (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhiB bc dst with
      | Some dhi =>
          match (if off_image_xB bc db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_xB bc k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_xB bc db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havocM k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.

Lemma summary_istrncpy_eq : forall cs, summary_istrncpy cs = summary_istrncpy_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^E0!1+2+W%b;R+C%off;R+3%n;R+C+1%k;R01!1'^5#1!1+^7+A!1'gI/A;!1'>!2'aA!1'cU#25!1,[+A!1'fY#2};!2'eJ#39}<!2'eJ#4;!1'gJ/A;!1,c?|;7ff;!1'>!2'^P!2'aA#2=!2'aA#1>}:!1'^W!2'^>#5@!1'^5#7!1'`WB!2'^>#7@!2'c8CD!1+^70!1'^5#8!1'`WG!1,F>!2,^80G!2'^>#8@!1'^5#9!2'^9#1'^:!1,[0-CRN$dst;R+CFK8$d;R+3!2,^80!3'f[LM>$n0;R+5N$op;R+^;$a;R+C$b;R+CN$op;R+^;$a;R+C$b;R+CN$op;R+^<$a;R+C$b;R+CN$op;R+^<$a;R+C$b;R+CN$sx;R+1$lo;R+5$n0;R+5$e;R+CN$sx;R+1$k0;R+5$i;R+3$n0;R+5N!1,c?|31;!2'^S=P!2'^P!2'^P!2'aC!2'^S#2>'^:!2'^R,G=!2'aCQ'^:!3'gH#1=Q!1,F,G!1,FP!7'aB!1'`WL#4#3IT=U!2,^8+C!2'^>#9@}8!3,`D!2,`0#4#3X!1,F'gK!2,`E!2,`0#4!2'^S#3!1,c?|30;!1,F!1,c?|;7f7;!3,_C+WY!3,_C+WZ!4'bA#1#4#3I!4'fZ#9#7W[!2'c9BD-1RN$~R+1F!4'cCG#3#2I2JO!2'^P!2'^PR!5'c7LL#4#3IS!2'^P^2!7'aHL#4#3IT=U!3,_C+WY!3,_C+WZ!4'b?#1#4#3I-1RN$~R+14627-^7RN$x;R!1+^7+3482$ret;R+3-^7RN$x;R!1+^7+34:2$src;R+3-^7RN$x;R!1+^7+34<2$n;R+3-1RN$~R+14?27-^IRN$x;R!2+^I+C+34A1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34^02$dhi;R+3-^7RN$x;R!1+^704^12$k0;R0-1RN$~R+14^32!4'fZ#9#7W^4777777%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1%e;R+C!1+^7+3%k;R0%ub;R+C%uk;R+3%un;R+C0!1'>!2'aA!1'cU#15!1'fY#1!2'eJ#29!2'eJ#3;!1'^W!2'^>#4@!1'^5#6!2'^>#6@!2,^80B-CRN$dst;R+CFD8$d;R+3!2,^80!3'f[GM>$n0;R+5N$op;R+^;$a;R+C$b;R+CN$op;R+^;$a;R+C$b;R+CN$op;R+^<$a;R+C$b;R+CN$op;R+^<$a;R+C$b;R+CN$sx;R+1$lo;R+5$n0;R+5$e;R+CN$sx;R+1$k0;R+5$i;R+3$n0;R+5N!2,^8+CK-1RN$~R+14^927-^7RN$x;R!1+^7+34^:2$ret;R+3-^7RN$x;R!1+^7+34^;2$src;R+3-^7RN$x;R!1+^7+34^<2$n;R+3-1RN$~R+14?27-^IRN$x;R!2+^I+C+34^=1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34!2'c9^>^?2$dhi;R+3-^7RN$x;R!1+^704-1RN$~R+1F!4'cCB#3#2I2^@^A2$k0;R0-1RN$~R+14!2'^P!2'^P!2'^PR!5'c7GG#4#3IS!7'aHG#4#3IT=U2!4'fZ#8#7^B^4777777!1'`W3$cs;R+Avdvd!6'_F2!1'c73$b;R2!3+_74-1RN$~R+14627-^7RN$x;R!1+^7+3482$ret;R+3-^7RN$x;R!1+^7+34:2$src;R+3-^7RN$x;R!1+^7+34<2$n;R+3-1RN$~R+14?27-^IRN$x;R!2+^I+C+34A1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34E2$dhi;R+3-^7RN$x;R!1+^704-1RN$~R+1F!4'cBH#3#2I2JO2$k0;R0-1RN$~R+14!2'^P!2'^P!2'^PR!4#8L#4#3ISV2\777777^5!6'_F1!1'cC3$b;R1!3+_74-1RN$~R+14627-^7RN$x;R!1+^7+3482$ret;R+3-^7RN$x;R!1+^7+34:2$src;R+3-^7RN$x;R!1+^7+34<2$n;R+3-1RN$~R+14?27-^IRN$x;R!2+^I+C+34A1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34E2$dhi;R+3-^7RN$x;R!1+^704-1RN$~R+1F!3#7#3#2I2JO2$k0;R0-1RN$~R+14!2'^P^2V2\777777^5!6'_F^6!1'aH3$b;R^6!3+_74-1RN$~R+14627-^7RN$x;R!1+^7+3482$ret;R+3-^7RN$x;R!1+^7+34:2$src;R+3-^7RN$x;R!1+^7+34<2$n;R+3-1RN$~R+14?27-^IRN$x;R!2+^I+C+34A1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34E2$dhi;R+3-^7RN$x;R!1+^704^12$k0;R0-1RN$~R+14!2'^P^2!6#8#4#3IT=U2\777777^5!6'_F^7!1'c93$o;R^7!3+_74-1RN$~R+14627-^7RN$x;R!1+^7+3482$ret;R+3-^7RN$x;R!1+^7+34:2$src;R+3-^7RN$x;R!1+^7+34<2$n;R+3-1RN$~R+14?27-^IRN$x;R!2+^I+C+34A1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34!1#6D2$dhi;R+3-^7RN$x;R!1+^704^12$k0;R0-1RN$~R+14^32\777777^5!6'_F^8'b?$l;R^8!3+_74-1RN$~R+14627-^7RN$x;R!1+^7+3482$ret;R+3-^7RN$x;R!1+^7+34:2$src;R+3-^7RN$x;R!1+^7+34<2$n;R+3-1RN$~R+14?27-^IRN$x;R!2+^I+C+34A1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34^02$dhi;R+3-^7RN$x;R!1+^704^12$k0;R0-1RN$~R+14^32!4'fZ#9#7W!3,_C+WY!3,_C+WZ!4#8#1#4#3I777777^5!2,_G4^C'bA'f\!1'c8^D!1'c:3!1'aB^D!1'aI3!1'cB^D!1'g03!1'c6^D!1'g13!3+_74-1RN$~R+14^927-^7RN$x;R!1+^7+34^:2$ret;R+3-^7RN$x;R!1+^7+34^;2$src;R+3-^7RN$x;R!1+^7+34^<2$n;R+3-1RN$~R+14?27-^IRN$x;R!2+^I+C+34^=1$db;R+C$dk;R+3-^7RN$x;R!1+^7+34!2'c8!1'`W^>^?2$dhi;R+3-^7RN$x;R!1+^704-1RN$~R+1F!4'cBC#3#2I2^@^A2$k0;R0-1RN$~R+14!2'^P!2'^P!2'^PR!5'c6HG#4#3IS!7'aBH#4#3IT=U2!4'fZ#8#7^B[777777^C!3+_74!1'gL#1!1'gM#1").
Qed.


(* [comment removed for export] *)
Definition popfree_facts (lb : expr) (lk : Z) (cnt c s : Z) (K : nat) : list kentry :=
  map (fun t => KWord (SA lb (lk + 4 * (cnt - 1 - Z.of_nat t))) 4 (ELit ((c + Z.of_nat t * s) / 16))) (seq 0 K).
Definition summary_popfree (cs : acs) (args : list expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S@0!1+2+C!1+2+W!1+^7+A!1,[+A}:}<}C};|20;!1,c?8!1,c?|500;!1,F!2'g;9#6!1,Y+W}>|40;}?$cs;R+A$args;R0&k;R!1'^5#21-1RN$~R+12!1'>!2'aA!1'cU#3!1'gN/A;23-2RN$args;R!1+2+C2#223$e;R+C$l;R!1+2+C-CRN$e;R+C2#28$K;R+3-2RN$l;R!1+2+C2#22-^7RN$x;R!1+^7+32!2'eJ#642$i;R+3-^7RN$x;R!1+^7+32!2'eJ#752$c;R+3-^7RN$x;R!1+^7+32!2'eJ#8}E2$s;R+3-^7RN$x;R!1+^7+32!2'eJ#962$n;R+3&e;R!2'^>#:7+C&cnt;R!2'aD#2#5+3&lo;R!2'gB#2!1'gO!2'g;9#3+C-^IRN$x;R!2+^I+C+32!1'^W#11$lb;R+C$lk;R+3-^7RN$x;R!1+^7+32!2'c2#=#52$el;R+3-^7RN$x;R!1+^7+32!2'c9#>#62$eh;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^R,G#;!2'aC#;#8!2'^R!2'g;9#8#2!2'aC#1'^:!2'^R,G#:!2'^R,G#9!2'aC!2'^S#:!2'g;#6#9'^:!2'^R,G#<!2'^R#<#6!2'aC!2'^S!1'cU#A:'^:!1'`T#A!5'c7#?#?#4#3;!4'cC#?#4#3;2&k1;R!4'b?#?#4#3;1&kunk;R-1RN$~R+11!2'aC#=#72!3,_C+W!2,`N!2,`0#5#4!1,F!2'g;9!2'aD#7#=<<1&sr;R!1'D!1'E#C0&sr';R!3'^2!3'^2!3'^2!3'^2#14!1,F#;5!1,F!2'^S#=!2'g;#9#<=!1,F!2'dV!2'^S#=!2'g;!2'aD#9!1,c?,dL#<!1,c?>?#80!2,^8+A!2'^0#E!4'^1!2'^S!1'cU#E:#1!3'^4+W!6'gP#8#7#:#>#=!1'g9#@!3'^4+W#3#4!1'dS#E3333333$e0;R+C$l0;R!1+2+C3$n;R+53$op;R+^;$a;R+C$b;R+C3$op;R+^;$a;R+C$b;R+C3$op;R+^<$a;R+C$b;R+C3$op;R+^<$a;R+C$b;R+C3$sx;R+1$lo;R+5$n;R+5$e0;R+C3$sx;R+1$k0;R+5$i;R+3$n;R+53").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_readable_x (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        xinside k rb rk ne kb kk len
                    | _ => false
                    end) k.

Definition summary_sniff_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_sniff A)) then None else
  match ret_lit cs with
  | Some ret =>
    let buf := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(bb, bk) := split_lit buf in
    let '(qb, qk) := split_lit (eaddz sp (-8)) in
    match xhi k ne, xhi k buf, xlo k sp, xhi k sp with
    | Some nhi, Some bhi, Some splo, Some sphi =>
      let m := Z.min nhi 8 in
      if (Z.ltb (bhi + 8) two64 && Z.leb 32 splo && Z.ltb sphi two64 && Z.leb (sniff_tab A + 16 + 8) splo
          && flat_x k qb qk (ELit 8) && kwritable k k qb qk 8
          && flat_x k bb bk (ELit 8)
          && ranges_apart_x k qb qk (ELit 8) bb bk (ELit 8)
          && ranges_apart_x k qb qk (ELit 8) (ELit 0) (sniff_cell A) (ELit 8)
          && (Z.eqb m 0 || (flat_x k bb bk (ELit m) && kn_readable segs k k bb bk (Z.to_nat m))
              || kn_readable_x k bb bk ne)             (* [comment removed for export] *)
          && img_cov k (sniff_tab A) (sniff_tab A + 16)
          && (Z.leb nhi 2 ||
              (Z.leb 3 (ealign k buf) && flat_x k (ELit 0) (sniff_cell A) (ELit 8)
               && match xlo k buf with Some blo => Z.ltb 0 blo | None => false end &&
               match know_lookup segs k (ELit 0) (sniff_cell A) 8 false [] [] with
               | LHit esb [] _ =>
                 let sa := eadd esb (mkSrl k buf 3) in let '(hb, hk) := split_lit sa in
                 match xhi k esb with
                 | Some ehi =>
                     Z.ltb (ehi + bhi / 8 + 1) two64
                     && flat_x k hb hk (ELit 1)
                     && ranges_apart_x k qb qk (ELit 8) hb hk (ELit 1)
                     && match know_lookup segs k hb hk 1 false [] [] with
                        | LHit v0 [] _ =>
                                        (* [comment removed for export] *)
                                        let v := extK k v0 in
                                        match erange k v with
                                        | Some (lo, hi) => Z.eqb hi 0 || (Z.leb m lo && Z.leb hi 127)
                                                           (* [comment removed for export] *)
                                                           || (Z.leb hi 127 && lin_ge0 k [(v, 0%Z)] [(ne, 0%Z)])
                                        | None => false
                                        end
                        | _ => false
                        end
                 | None => false
                 end
               | _ => false
               end)))%bool
      then after_call cs ret None (kn_havoc k qb qk (ELit 8))
      else None
    | _, _, _, _ => None
    end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_sniff (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_sniff A)) then None else
  match ret_lit cs with
  | Some ret =>
    let buf := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(bb, bk) := split_lit buf in
    let '(qb, qk) := split_lit (eaddz sp (-8)) in
    match xhiB bc ne, xhiB bc buf, xloB bc sp, xhiB bc sp with
    | Some nhi, Some bhi, Some splo, Some sphi =>
      let m := Z.min nhi 8 in
      if (Z.ltb (bhi + 8) two64 && Z.leb 32 splo && Z.ltb sphi two64 && Z.leb (sniff_tab A + 16 + 8) splo
          && flat_xB bc qb qk (ELit 8) && kwritableB bc k qb qk 8
          && flat_xB bc bb bk (ELit 8)
          && ranges_apart_xB bc qb qk (ELit 8) bb bk (ELit 8)
          && ranges_apart_xB bc qb qk (ELit 8) (ELit 0) (sniff_cell A) (ELit 8)
          && (Z.eqb m 0 || (flat_xB bc bb bk (ELit m) && kn_readableB segs bc k bb bk (Z.to_nat m))
              || kn_readable_x k bb bk ne)             (* [comment removed for export] *)
          && img_covB bc (sniff_tab A) (sniff_tab A + 16)
          && (Z.leb nhi 2 ||
              (Z.leb 3 (ealignB bc buf) && flat_xB bc (ELit 0) (sniff_cell A) (ELit 8)
               && match xloB bc buf with Some blo => Z.ltb 0 blo | None => false end &&
               match know_lookupB segs bc (ELit 0) (sniff_cell A) 8 false [] [] with
               | LHit esb [] _ =>
                 let sa := eadd esb (mkSrlB bc buf 3) in let '(hb, hk) := split_lit sa in
                 match xhiB bc esb with
                 | Some ehi =>
                     Z.ltb (ehi + bhi / 8 + 1) two64
                     && flat_xB bc hb hk (ELit 1)
                     && ranges_apart_xB bc qb qk (ELit 8) hb hk (ELit 1)
                     && match know_lookupB segs bc hb hk 1 false [] [] with
                        | LHit v0 [] _ =>
                                        (* [comment removed for export] *)
                                        let v := extKB bc v0 in
                                        match erangeB bc v with
                                        | Some (lo, hi) => Z.eqb hi 0 || (Z.leb m lo && Z.leb hi 127)
                                                           (* [comment removed for export] *)
                                                           || (Z.leb hi 127 && lin_ge0B bc [(v, 0%Z)] [(ne, 0%Z)])
                                        | None => false
                                        end
                        | _ => false
                        end
                 | None => false
                 end
               | _ => false
               end)))%bool
      then after_call cs ret None (kn_havocB bc qb qk (ELit 8))
      else None
    | _, _, _, _ => None
    end
  | None => None
  end.

Lemma summary_sniff_eq : forall cs, summary_sniff cs = summary_sniff_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`J0%e;R+C+3!1'^5#1!1+^7+A!1'gQ/A;!1'>!2'aA!1'cU#23!1,[+A!1'fY#2}:!1'^W!2'^>#37}2|30;!1,gC:!1'^W!2'gB!2'^>#59;!1'^5#7!1'`W=};!2'^>#7?!2'c8>@!1'^5#8!1'`WB!2'^>#87!2'c8CD!1'^5#9!1'`WF!2'^>#99!2'c0GH!1'^5#:!1'`WJ!2'^>#:9!2'c8KL!1,c?:!1'gR/A;|40;!2'^SO!1,c?P!2'^P!2'^P!2'^P!2'aC!2'^S#3N'^:!2'^R!1,c?|500;#2!2'aC#1'^:!2'^R!2'^SQN#2!1'^5#;!1'`WS!1,FN!5'b[TS#6#5N!7'aBT#6#5U#8#7U!1,F,G!1'gS/A;!7'aBT#6#5UXYU!2'd=#4N!2'aA[,G!1,F[!1'g9[!6'gT/segs;TS#8#7^1!4'gUS#8#7!2'^>#;?!3'gGTOQ!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^PR!4'cET#6#5UV!4'cET#8#7UWZ!2'^M!2'^M\!2'^P!4'cET#8#7^0^2^3^4|10;!2'^R#4!1,c?^6|11;!1,c?^8!2'^>#;7!1#:^:!4'cETXYU!2'aC,G#1-^7RN$x;R!1+^7+3+1!2'c0T^:2$blo;R+3^=,6}8!1,Y+1!1,Y+`U!8'bT/segs;TXY^?,6^@^A!1+2+`U!1+2+1!1'^5#>!2'^>#>7!1'^W!2'dY#3!3'e6!1'`W^E^F^9!1'^5#@!1'`W^H!2'c8^I#5!1,c?,dL!2'aC!2'^S!2'^S#1!2'dV#9N^K'^:!1'^5#A!1'`W^M!1,F^K!7'aB^N#<#;U#3#2^O!2'^P!2'^P^L!4'cE^N#3#2^O^P}1!8'bT/segs;^N#3#2^R,6^@^A!2+^I+3+3!1'^5#D!1'`W^U!2'gV^V#3!2'^R#1!1,c?|63f;!2'^M!2'aA#1,G!2'^P!2'^R!2'd=#@N#2^X!1'^5#G!1'`W^Z!2+^I+C+3!1,Y^\!3,_C^\!4,cJ+C+3!2'^>#G?,G_0-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M^Y!2'^P^X!3'cI^[!3,_C^\!4,cJ+C+3!2'gV^[#6,G_0_1!1,[+C!4'fZ#;#9_3!4'b>T#6#5U!2'c9=@!2'c9BD!2'c9JL!2'^PR!4'cFS#6#5U!4'cFS#8#7U!2'^P!2'^P_8!5'b\SS#6#5N_9!4'cFS#8#7^0!2'^M!2'^M\!2'^P_;!6'gW/segs;SS#8#7^1^3!3'gHSOQ!2'^P!2'^P!2'^P!2'^P_:!7'aHS#6#5U#8#7U!7'aHS#6#5UXYU_<_=!2'^R^9!2'cSS^:!2'^P_?!4'cFSXYU!8'bW/segs;SXY^?,6^@^A!1'^W!2'dY#3!3'e:^E^F^9!2'^P^L!4'cF^M#3#2^O!8'bW/segs;^M#3#2^R,6^@^A!2'd5^U!2'gX^U#3!3,_C^\!4,cJ+C+3!2'gX^Z#6,G_0-bSRN$x;R+bS+1_D3$v0;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^7RN$x;R!1+^7^T+1_E2$p;R^T-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M^Y!2'^P^X!3'cN^Z_F_1,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6!2'^P!2'^P_C!7'aH^M#<#;U#3#2^O_G-bSRN$x;R+bS+1_A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1_B1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1!2'c9^H#52$ehi;R+3_H,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6!4'fZ#;#9_3!4'b?S#6#5U-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32_52$nhi;R+3-^7RN$x;R!1+^7+32_62$bhi;R+3-^7RN$x;R!1+^7+32!2'c2FH2$splo;R+3-^7RN$x;R!1+^7+32_72$sphi;R+3-1RN$~R+12!2'^P_>!2'^M^7!2'^P!2'^P_@-^7RN$x;R!1+^7+3+1!2'c2S^:2$blo;R+3^=,6_I2_J555555%e;R+C!1+^7^T!2'^P!2'^P_?^<^>%v;R+C+C%b;R+C%off;R+3%n;R+C+1!3#:#6#5U-2RN$scs;R!1+2+`U+1#22-^7RN$x;R!1+^7^T+1_E2$p;R^T-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M^Y!2'^P^X!3'cI^[_F_1,6$s;R+`U$l;R!1+2+`U,6-bSRN$x;R+bS+1^S3$v0;R+C$scs;R^C$hints;R^D_Q$scs;R^C$hints;R^D,6,6%a;R+3%b;R+3+1!2'^P!2'^P!2'^P!2'^P_8V_9WZ!2'^P_T!2'^M!2'^M\!2'^P_;^2^3!2'^P_@^>!2'^P_C^P!2'^M^7!2'^P_V-bSRN$x;R+bS+1^B3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1^G1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P_W_R,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6!1+2+W%ub;R+C%uk;R+3%un;R+C_Y%kn;R_Y%rb;R+C%rk;R+3%n;R+5+1%rb;R+C%rk;R+3%n;R+5%sx;R+1%hints;R!1+2+1%acc;R!1+2+`U+bS%k;R_Y%b;R+C%off;R+3%n;R+3+1%pos;R'cM%neg;R'cM+1!2'^P!2'^P!2'^P!2'^P_:WZ_<_=%a;R+C%s;R+3+C%b1;R+C%k1;R+3%n1;R+C%b2;R+C%k2;R+3%n2;R+C+1%e;R+C!1+^7+3!1'>!2'aA!1'cU#13!1'fY#1!1'^W!2'^>#27!1'^W!2'gB!2'^>#49;!1'^5#6!2'^>#6?!2'^>#77!2'^>#89!4'gUJ#8#7!2'^>#:?!2'^>#:7!1'^5#=!2'^>#=7!1'^5#?!1'^5#C!1'^5#F!3,_C^\!4,cJ+C+3!2'^>#F?,G_0-1RN$~R+12`625-^7RN$x;R!1+^7+32`72$ret;R+3-^IRN$x;R!2+^I+C+32`81$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32`91$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32!2'c9`:`;2$nhi;R+3-^7RN$x;R!1+^7+32!2'c9=`<2$bhi;R+3-^7RN$x;R!1+^7+32!2'c2B`=2$splo;R+3-^7RN$x;R!1+^7+32!2'c9FH2$sphi;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^PR!4'cFJ#6#5U!5'b\JJ#6#5N!4'cFJ#8#7U!7'aHJ#6#5U#8#7U!7'aHJ#6#5UXYU!2'^M!2'^M\!2'^P!4'cFJ#8#7^0!6'gW/segs;JJ#8#7^1`>!3'gHJOQ!2'^M^7!2'^P!2'^P!2'^P!2'^R^9!2'cSJ`?!4'cFJXYU-^7RN$x;R!1+^7+3+1!2'c2J`?2$blo;R+3^=,6-bSRN$x;R+bS+1!8'bW/segs;JXY^?,6^@^A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1!1'^W!2'dY#3!3'e:`@`A^91$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1!2'c9`B#52$ehi;R+3!2'^P!2'^P!2'^P^L!4'cF^H#3#2^O!7'aH^H#<#;U#3#2^O-bSRN$x;R+bS+1!8'bW/segs;^H#3#2^R,6^@^A3$v0;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^7RN$x;R!1+^7^T+1!2'd5`C!2'gX`C#32$p;R^T-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M^Y!2'^P^X!3'cN`D!3,_C^\!4,cJ+C+3!2'gX`D#6,G_0`E,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62!4'fZ#:#9_3!4'b?J#6#5U555555!1'`W1!1'`W`C!1'`W`D$cs;R+Avdvd!6'_F0!1'cS1$z;R0!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P^5!2'^M^7!2'^P!2'^P!2'^P!2'^R^9^;^<^>-bSRN$x;R+bS+1^B3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1^G1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P^Q-bSRN$x;R+bS+1^S3$v0;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^7RN$x;R!1+^7^T+1!2'd2^V^W2$p;R^T_2,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_4555555_K!6'_F_L!1'd51$o;R_L!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P^5!2'^M^7!2'^P_M-bSRN$x;R+bS+1^B3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1^G1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P^Q-bSRN$x;R+bS+1^S3$v0;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^7RN$x;R!1+^7^T+1!1#C^W2$p;R^T_2,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_4555555_K!6'_F_N!1'gX1$e;R_N!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P^5!2'^M^7!2'^P_M-bSRN$x;R+bS+1^B3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1^G1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P^Q-bSRN$x;R+bS+1^S3$v0;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^7RN$x;R!1+^7^T+1!2'd5^U!1#C#32$p;R^T-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M^Y!2'^P^X!3'cI^[!3,_C^\!4,cJ+C+3!1#F#6,G_0_1,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_4555555_K!6'_F_O!1'cF1$b;R_O!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^PR_PV!3#:#8#7UWZ!2'^M!2'^M\!2'^P!3#:#8#7^0^2^3^4!2'^M^7!2'^P!2'^P!2'^P_?!3#:XYU^>-bSRN$x;R+bS+1^B3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1^G1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P!2'^P!2'^P^L!3#@#3#2^O^P_R,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_4555555_K!6'_F_S!1'gH1$b;R_S!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P!2'^P_U!2#:OQ_X2_4555555_K!6'_F_Z!1'b?1$l;R_Z!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P!2'^P_U_=_X2!4'fZ#;#9_3_P555555_K!6'_F_[!2'gW/segs;1$b;R_[!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P!2'^P!2'^P_T!2'^M!2'^M\!2'^P_;!4#:S#8#7^1^3_=_X2_J555555_K!6'_F_\!2'bW/segs;1$l;R_\!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P!2'^P!2'^P_T_<_=!2'^M^7!2'^P_V-bSRN$x;R+bS+1!6#:XY^?,6^@^A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1^G1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P_W-bSRN$x;R+bS+1!6#@#3#2^R,6^@^A3$v0;R+C$scs;R^C$hints;R^D_Q$scs;R^C$hints;R^D,6,6,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_F`0!1'b\1$b;R`0!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P_8!4#:S#6#5N_9WZ_<_=!2'^M^7!2'^P_V-bSRN$x;R+bS+1_A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1^G1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P_W-bSRN$x;R+bS+1_D3$v0;R+C$scs;R^C$hints;R^D_Q$scs;R^C$hints;R^D,6,6,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_F`1!1'cN1$b;R`1!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P`2!2'^M^7!2'^P_V-bSRN$x;R+bS+1_A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1^G1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P_W-bSRN$x;R+bS+1_D3$v0;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^7RN$x;R!1+^7^T+1_E2$p;R^T-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M^Y!2'^P^X!2#F_F_1,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_F`3!1'e:1$e;R`3!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P`2!2'^M^7!2'^P_V-bSRN$x;R+bS+1_A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1!1'^W!2'dY#3!2#=^F^91$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P_W_G,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_F`4!1'aH1$b;R`4!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32A2$nhi;R+3-^7RN$x;R!1+^7+32E2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32M2$sphi;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P_:!6#:#6#5U#8#7U!6#:#6#5UXYU_<_=!2'^M^7!2'^P_V-bSRN$x;R+bS+1_A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1_B1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1^J2$ehi;R+3!2'^P!2'^P_C!6#@#<#;U#3#2^O_G,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_F`5!1'c91$o;R`5!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32!1#6@2$nhi;R+3-^7RN$x;R!1+^7+32!1#7D2$bhi;R+3-^7RN$x;R!1+^7+32I2$splo;R+3-^7RN$x;R!1+^7+32!1#9L2$sphi;R+3-1RN$~R+12!2'^P_>!2'^M^7!2'^P_V-bSRN$x;R+bS+1_A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1_B1$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1!1#?#52$ehi;R+3_H,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_F`5!1'c21$o;R`5!3+_72-1RN$~R+12425-^7RN$x;R!1+^7+3262$ret;R+3-^IRN$x;R!2+^I+C+3281$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32<1$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32_52$nhi;R+3-^7RN$x;R!1+^7+32_62$bhi;R+3-^7RN$x;R!1+^7+32!1#8H2$splo;R+3-^7RN$x;R!1+^7+32_72$sphi;R+3-1RN$~R+12!2'^P_>!2'^M^7!2'^P!2'^P_@-^7RN$x;R!1+^7+3+1^;2$blo;R+3^=,6_I2_J555555_K!2,_G2`F!1'c0`G!1'c41!1'c8`G!1'c:1!1'aB`G!1'aI1!1'e6`G!1'e;1!1'cI`G!1'cO1!1'b[`G!1'gD1!2'bT/segs;`G!2'bX1/segs;!2'gT/segs;`G!2'gY/segs;1!1'b>`G!1'bB1!1'gG`G!1'gZ1!1'cE`G!1'eC1!1'gV`G!1'g[1!1'd2`G!1'd71!1'cP`G!1'cT1!3+_72-1RN$~R+12`625-^7RN$x;R!1+^7+32`72$ret;R+3-^IRN$x;R!2+^I+C+32`81$bb;R+C$bk;R+3-^IRN$x;R!2+^I+C+32`91$qb;R+C$qk;R+3-^7RN$x;R!1+^7+32!2'c8!1'`W`:`;2$nhi;R+3-^7RN$x;R!1+^7+32!2'c8>`<2$bhi;R+3-^7RN$x;R!1+^7+32!2'c0C`=2$splo;R+3-^7RN$x;R!1+^7+32!2'c8GH2$sphi;R+3-1RN$~R+12!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^PR!4'cEK#6#5U!5'b[KJ#6#5N!4'cEK#8#7U!7'aBK#6#5U#8#7U!7'aBK#6#5UXYU!2'^M!2'^M\!2'^P!4'cEK#8#7^0!6'gT/segs;KJ#8#7^1`>!3'gGKOQ!2'^M^7!2'^P!2'^P!2'^P!2'^R^9!2'cPK`?!4'cEKXYU-^7RN$x;R!1+^7+3+1!2'c0K`?2$blo;R+3^=,6-bSRN$x;R+bS+1!8'bT/segs;KXY^?,6^@^A3$esb;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^IRN$x;R!2+^I+C+3+1!1'^W!2'dY#3!3'e6!1'`W`@`A^91$hb;R+C$hk;R+3-^7RN$x;R!1+^7+3+1!2'c8!1'`W`B#52$ehi;R+3!2'^P!2'^P!2'^P^L!4'cE^I#3#2^O!7'aB^I#<#;U#3#2^O-bSRN$x;R+bS+1!8'bT/segs;^I#3#2^R,6^@^A3$v0;R+C$scs;R^C$hints;R^D-2RN$scs;R!1+2+`U+1#22-^7RN$x;R!1+^7^T+1!2'd2`H!2'gV`H#32$p;R^T-^IRN$p;R!2+^I+3+3+1#11$lo;R+3$hi;R+3!2'^M^Y!2'^P^X!3'cI`I!3,_C^\!4,cJ+C+3!2'gV`I#6,G_0`E,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,6,6$s;R+`U$l;R!1+2+`U,6$scs;R^C$hints;R^D,6,62!4'fZ#:#9_3!4'b>K#6#5U555555`F!3+_72!1'g\#1!1'h0#1").
Qed.


(* [comment removed for export] *)
Definition V_S1 : nat := 0.     (* [comment removed for export] *)
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00}2").
Definition V_L0 : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00}3").     (* [comment removed for export] *)
Definition V_W : nat := 4.      (* [comment removed for export] *)
Definition V_BRK : nat := 5.    (* [comment removed for export] *)
Definition V_S2 : nat := 6.     (* [comment removed for export] *)
Definition V_L1 : nat := 7.     (* [comment removed for export] *)
Definition V_UID : nat := 8.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sp0 : expr := eadd (escale 32768 (EVar V_S1)) (escale 16 (EVar V_S2)).
(* [comment removed for export] *)
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10!1,c?|30;!2'dY'h1!2'dY!2'dT0!1,_R'h2!1,F0").
Definition e_str0 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'gB'h3!1,c?|720;").
Definition e_str1 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'dY'h4!2'gB!1,_R'h5!1,c?,dL").
Definition e_atrandom : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'dY'h4!2'dT!1,c?|30;!1,_R'h6").
(* [comment removed for export] *)
Definition e_atr8 : expr :=
  eadd (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).

(* [comment removed for export] *)
Definition e_argv1w : expr := EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar V_ARGC)) e_str1.

(* [comment removed for export] *)
Definition node_envscan (cs : acs) : option acs :=
  let k := kn cs in
  if (Z.eqb (pc cs) (x_envscan A) && len_eqb k (reg cs 9) e_envp)%bool then
    Some (set_pc (set_reg (set_reg cs 9 (eadd (reg cs 9) (eadd (escale 8 (EVar V_ENVC)) (ELit 8)))) 10 (ELit 0)) (x_envscan_k A))
  else None.

(* [comment removed for export] *)
Definition node_pnscan (cs : acs) : option acs :=
  let k := kn cs in
  match reg_lit cs 10, reg_lit cs 12 with
  | Some p, Some 47 =>
      if (Z.eqb (pc cs) (x_pnscan A) && len_eqb k (reg cs 11) (eaddz e_str0 1)
          && kwritable k k (ELit 0) p 8 && Z.leb (img_lo A) p && Z.leb (p + 8) (img_hi A) && fresh_ok cs)%bool then
        let v := nxt cs in
        let k' := kn_havoc (kimg_cut k p 8) (ELit 0) p (ELit 8) in
        let ss := a_ss cs in
        Some (with_ss cs (mk_ss (x_pnscan_k A) (sr_upd (sr_upd (s_regs ss) 11 (EVar v)) 13 (ELit 0)) k' (S v)))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition kw_argv1 (v : expr) : kentry := KWord (SA e_sp0 16) 8 v.

Definition node_layout (cs : acs) (args : list expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S50!1+2+W!1+^7+A!1'h8'h9!1,[+A!1,_R'h:$cs;R+A$args;R!1+2+C&k;R!1'^5#20-1RN$~R+11!1'>!3'^O+W!1'h72#123&k';R!3'^Y+W$K;R+W!1'>!2'h72#1#10-2RN$args;R!1+2+C1#323$e;R+C$l;R!1+2+C-CRN$e;R+C1#28$z;R+3-3RN$z;R+31#13-2RN$l;R!1+2+C1#22-^7RN$x;R!1+^7+31!2'c9#542$hi;R+3-1RN$~R+11!2'^R#1!1,c?,dL2!2,^8+A!2'^3#8!3,_C+W!1'h8!1,F,G#533$e0;R+C$l0;R!1+2+C3$p;R+_8-_8RN$p;R+_81#13$p0;R+_83$p0;R+_83-2RN$l;R!1+2+C1#32-^7RN$x;R!1+^7+31!2'c2#642$lo;R+3-1RN$~R+11!2'^R!1,c?|10;#12!2,^8+A!2'^3#9!3,_C+W!1'h8'h;#633$e0;R+C$l0;R!1+2+C3$p;R+_83$n;R+53$op;R+^;$a;R+C$b;R+C3$op;R+^;$a;R+C$b;R+C3$op;R+^<$a;R+C$b;R+C3$op;R+^<$a;R+C$b;R+C3$sx;R+1$lo;R+5$n;R+5$e0;R+C3$sx;R+1$k0;R+5$i;R+3$n;R+53").


(* [comment removed for export] *)

Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && forallb (fun K => existsb (kentry_eqb K) (kn cs)) (kn ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint esubst (J : nat) (e : expr) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => if Nat.eqb n J then e else x
  | EAlu op a b => mkAlu op (esubst J e a) (esubst J e b)
  | EAluw op a b => mkAluw op (esubst J e a) (esubst J e b)
  | EMd op a b => mkMd op (esubst J e a) (esubst J e b)
  | EMdw op a b => mkMdw op (esubst J e a) (esubst J e b)
  | EExt sx lo n a => EExt sx lo n (esubst J e a)
  | EBlob _ _ _ _ => x
  end.
(* [comment removed for export] *)
Definition asubst (J : nat) (e : expr) (a : saddr) : saddr := SA (esubst J e (a_base a)) (a_off a).
Definition ksubst (J : nat) (e : expr) (K : kentry) : kentry := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!3'h<#6#5#3!3'h<#5#4#2!3'h=#5#4#1!3'h=#6#5#2$J;R+5$e;R+C$K;R+W-WRN$K;R+W+W#1:$a;R+\$w;R+5$v;R+C!3,`D0#2!3'h=#6#5#1$a;R+\$n;R+C!2,`E12$a;R+\$n;R+C$k;R+5!3,`F03#1$lo;R+3$hi;R+3#3$x;R+C$m;R+3!2,`I!3'h=#5#4#2#1$x;R+C$lo;R+3$hi;R+3!3,`J!3'h=#6#5#3#2#1$a;R+\$n;R+C!2,`K12$a1;R+\$n1;R+C$a2;R+\$n2;R+C!4,`L!3'h<#7#6#4!3'h=#7#6#3!3'h<#7#6#2!3'h=#7#6#1$a;R+\$n;R+C$c;R+3!3,`M03#1$a;R+\$n;R+C!2,`N12").
Definition psubst (J : nat) (e : expr) (p : expr * expr) : expr * expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$J;R+5$e;R+C$p;R!2+^I+C+C!4,cJ+C+C!3'h=#3#2!3'^J+C+C#1!3'h=#3#2!3'^K+C+C#1").
Definition msubst (J : nat) (e : expr) (m : amap) : amap := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$J;R+5$e;R+C$m;R+8!3,f@!3'h=#3#2!1'^G#1!3'h=#3#2!1'^H#1!1':#1").
Definition fsubst (J : nat) (e : expr) (f : afd) : afd := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$J;R+5$e;R+C$f;R+^L-^LRN$f;R+^L+^L#13#1$k;R+5$l;R+C$o;R+C!3,h>#3!3'h=#6#5#2!3'h=#6#5#1#1").
(* [comment removed for export] *)
Definition inst (inv : acs) (J : nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (map (ksubst J e) (kn inv)) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint nt_set (t : list (option nat)) (i : nat) (d : nat) {struct i} : list (option nat) :=
  match i, t with
  | O, [] => [Some d]
  | O, _ :: rest => Some d :: rest
  | S j, [] => None :: nt_set [] j d
  | S j, x :: rest => x :: nt_set rest j d
  end.
Definition nt_get (t : list (option nat)) (i : nat) : option nat := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1+^7+5$t;R!1+20$i;R+5!4'B0#1#2!1,[+5").
Lemma nt_get_set : forall t i d j, nt_get (nt_set t i d) j = if Nat.eqb j i then Some d else nt_get t j.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "ST0!1+^7+5!1+20!1,[+5!2,^8+5#2!4'B0#1#32%t;R1%d;R+5%j;R+5!3+_70!4'B0#1!3'h?#3#4#22-1RN$~R+10!2'7#1#4234!2,^8+5#3!4'B0#2#12!1,Y0!2'7#1,dK!4'B0#182!2'7,dK,dK!4'B0,dK82!2,_G02!1$j;R+5=#1!1,_=#1!2'7?,dK!2,^8+5#4!4'B0?82!3,_C0#3#2!2,^8+5#7!4'B0#1C2!2,^8+5#6!3,_C0#2#1!4'B0,dKG2!3,_C0#4#3!2,^8+5#8!4'B0?I2!1,_=#6!1,_=#5!2'7#1#7!2,^8+5#5!1,_=#7!1,_=#:!1,_=#9!1,_=#;vd$t;R1$i;R+5!5'dH$i;R+55$t;R1$d;R+5$j;R+5-2RN$l;R!1+20!3+_70!4'B0#2!3'h?#1,dK#32-1RN$~R+10!2'7#2,dK267#32-5RN$n;R+5!3+_70!4'B0#1!3'h?8,dK#32-1RN$~R+10926:#12vd!2,_G03!3+_70!4'B0,dK!3'h?8,dK#22-1RN$~R+10;23<$n;R+5!1$j;R+5vd-5RN$n;R+5!3+_70-5RN$n;R+50#122$m;R+522#12=$n;R+5>!3+_70!4'B0?!3'h?8,dK#42-1RN$~R+10@2AB#1$o;R0$l;R!1+20!2$x;R0$rest;R1-5RN$n;R+5!3+_70!4'B0#1!3'h?C,dK#72-1RN$~R+1092DE#52vd!2,_G0F!3+_70!4'B0,dK!3'h?G,dK#62-1RN$~R+10;2FH$n;R+5!1$j;R+5vd!2,_G04!3+_70!4'B0?!3'h?I,dK#82-1RN$~R+10@2JK#1#2#1$i;R+5$IH;R5$t;R1$d;R+5$j;R+5-2RN$l;R!1+20!3+_70!4'B0#2!3'h?#1L#32-1RN$~R+10!2'7#2L267#32-5RN$n;R+5!3+_70!4'B0#1!3'h?8L#32-1RN$~R+10!2'7#1L26:#12vd=!3+_70!4'B0,dK!3'h?8M#22-1RN$~R+10!2'7,dKM23<$n;R+5!1$j;R+5vd!6'_F0-1RN$~R+10N2A:$o;R0!3+_70#1-1RN$~R+10!2'7#2#82O2&b;RN+1-1RN$b;R+1!3+_70-1RN$~R+10#12F!4'B0#382-1RN$~R+10#12F2#12-5RN$n;R+5!3+_70FF#22!2,_G0O$n;R+5!1$j;R+5!2,_G0D#1-5RN$n;R+5!3+_70:2#22=$n;R+5>!4'B0#1!3'h?8#7#42!3#68#4#1!3+_70!4'B0?!3'h?8P#42-1RN$~R+10!2'7?P2AB#1$o;R0$l;R!1+20!2$x;R0$rest;R1-5RN$n;R+5!3+_70!4'B0#1!3'h?CQ#72-1RN$~R+10!2'7#1Q2DE#52vd!2,_G0#2!3+_70!4'B0,dK!3'h?GR#62-1RN$~R+10!2'7,dKR2FH$n;R+5!1$j;R+5vd!3#:#3#8#1!3+_70!4'B0?!3'h?IS#82-1RN$~R+10!2'7?S2JK#1#2#1#1#2%t;R1%i;R+5%d;R+5%j;R+5!3+_70!2'h@!3'h?#4#3#2#1-1RN$~R+10!2'7#1#323!2'h@#4#1").
Qed.
(* [comment removed for export] *)
Fixpoint mk_fwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_fwd rest with
      | Some t => match nt_get t s with None => Some (nt_set t s d) | Some _ => None end
      | None => None
      end
  end.
(* [comment removed for export] *)
Fixpoint mk_bwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_bwd rest with
      | Some t => match nt_get t d with None => Some (nt_set t d s) | Some _ => None end
      | None => None
      end
  end.

Fixpoint erename (t : list (option nat)) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar v => match nt_get t v with Some d => EVar d | None => e end
  | EAlu op a b => EAlu op (erename t a) (erename t b)
  | EAluw op a b => EAluw op (erename t a) (erename t b)
  | EMd op a b => EMd op (erename t a) (erename t b)
  | EMdw op a b => EMdw op (erename t a) (erename t b)
  | EExt sx lo n a => EExt sx lo n (erename t a)
  | EBlob _ _ _ _ => e
  end.
Definition arename (t : list (option nat)) (a : saddr) : saddr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2!1+^7+5$a;R+\!2,`0!2'hA#2!1'^F#1!1'hB#1").
Definition krename (t : list (option nat)) (K : kentry) : kentry := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40!2'hC#5#3!2'hC#4#2!2'hA#4#1!2'hA#5#2$t;R!1+2!1+^7+5$K;R+W-WRN$K;R+W+W#1:$a;R+\$w;R+5$v;R+C!3,`D0#2!2'hA#5#1$a;R+\$n;R+C!2,`E12$a;R+\$n;R+C$k;R+5!3,`F03#1$lo;R+3$hi;R+3#3$x;R+C$m;R+3!2,`I!2'hA#4#2#1$x;R+C$lo;R+3$hi;R+3!3,`J!2'hA#5#3#2#1$a;R+\$n;R+C!2,`K12$a1;R+\$n1;R+C$a2;R+\$n2;R+C!4,`L!2'hC#6#4!2'hA#6#3!2'hC#6#2!2'hA#6#1$a;R+\$n;R+C$c;R+3!3,`M03#1$a;R+\$n;R+C!2,`N12").
Definition prename (t : list (option nat)) (p : expr * expr) : expr * expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2!1+^7+5$p;R!2+^I+C+C!4,cJ+C+C!2'hA#2!3'^J+C+C#1!2'hA#2!3'^K+C+C#1").
Definition mrename (t : list (option nat)) (m : amap) : amap := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2!1+^7+5$m;R+8!3,f@!2'hA#2!1'^G#1!2'hA#2!1'^H#1!1':#1").
Definition frename (t : list (option nat)) (f : afd) : afd := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2!1+^7+5$f;R+^L-^LRN$f;R+^L+^L#13#1$k;R+5$l;R+C$o;R+C!3,h>#3!2'hA#5#2!2'hA#5#1#1").

(* [comment removed for export] *)
Fixpoint evars_all (ok : nat -> bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => ok v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_all ok a && evars_all ok b
  | EExt _ _ _ a => evars_all ok a
  | EBlob _ _ _ _ => true
  end.
Definition kvars_all (ok : nat -> bool) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40!2'hD#5!1'^F#3!1'^F#2!2'^P!2'hD#41!2'hD#4#1!2'^P0!2'hD#5#2$ok;R%~R+5+1$K;R+W-WRN$K;R+W+1#1:$a;R+\$w;R+5$v;R+C!2'^P0!2'hD#5#1$a;R+\$n;R+C2$a;R+\$n;R+C$k;R+53$lo;R+3$hi;R+3,^U$x;R+C$m;R+3!2'hD#4#2$x;R+C$lo;R+3$hi;R+3!2'hD#5#3$a;R+\$n;R+C2$a1;R+\$n1;R+C$a2;R+\$n2;R+C!2'^P!2'^P!2'^P!2'hD#6!1'^F#4!2'hD#6#3!2'hD#61!2'hD#6#1$a;R+\$n;R+C$c;R+33$a;R+\$n;R+C2").
Definition csvars_all (ok : nat -> bool) (cs : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+^I+C+C$p;R0!2'^P!2'hD#3!3'^J+C+C#1!2'hD#3!3'^K+C+C#1$ok;R%~R+5+1$cs;R+A!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!3'=+C!1'hD#2!1'D!1'E#1!3'=+W!1'hE#2!1'^5#1!3'=+8$m;R+8!2'^P!2'hD#3!1'^G#1!2'hD#3!1'^H#1!1'M#1!3'=01!1'Q#1!3'=01!1'R#1!2'hD#2!1'T#1-^LRN$x;R+^L+1!1'U#13,^U$k;R+5$l;R+C$o;R+C!2'^P!2'hD#5#2!2'hD#5#1,^U").

(* [comment removed for export] *)
Fixpoint emaxv (e : expr) (acc : nat) : nat :=
  match e with
  | ELit _ => acc
  | EVar v => Nat.max acc (S v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => emaxv a (emaxv b acc)
  | EExt _ _ _ a => emaxv a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kmaxv (K : kentry) (acc : nat) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40!1'^F#3!1'^F#2!2'hF1!2'hF#1#3!2'hF0!2'hF#2#4$K;R+W$acc;R+5-WRN$K;R+W+5#2:$a;R+\$w;R+5$v;R+C!2'hF0!2'hF#1#4$a;R+\$n;R+C2$a;R+\$n;R+C$k;R+53$lo;R+3$hi;R+3#3$x;R+C$m;R+3!2'hF#2#3$x;R+C$lo;R+3$hi;R+3!2'hF#3#4$a;R+\$n;R+C2$a1;R+\$n1;R+C$a2;R+\$n2;R+C!2'hF!1'^F#4!2'hF#3!2'hF1!2'hF#1#5$a;R+\$n;R+C$c;R+33$a;R+\$n;R+C2").
Definition csmaxv (cs : acs) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!2+^I+C+C$p;R0$acc;R+5!2'hF!3'^J+C+C#2!2'hF!3'^K+C+C#2#1$cs;R+A&acc;R!5'^D+5+C'hF,dK!1'D!1'E#1+5&acc;R!5'^D+5+W'hG#1!1'^5#2+5&acc;R!5'^D+5+8$m;R+8$acc;R+5!2'hF!1'^G#2!2'hF!1'^H#2#1#1!1'M#3+5&acc;R!5'^D+501#1!1'Q#4+5&acc;R!5'^D+501#1!1'R#5+5&acc;R-^LRN$x;R+^L+5!1'U#63#1$k;R+5$l;R+C$o;R+C!2'hF#2!2'hF#1#4#1+5!2'hF!1'T#7#1").

Definition rename_cs (t : list (option nat)) (cs : acs) (nx : nat) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!2+^I+C+C!1'hJ#3$t;R!1+2!1+^7+5$cs;R+A$nx;R+5!;,L!4'^1!1'cU#2!4'fD+C+C!1'hA#3!1'D!1'E#2!4'fD+W+W!1'hH#3!1'^5#2#1!4'fD+8+8!1'hI#3!1'M#2!1'N#2!1'O#2!1'P#2!4'fD001!1'Q#2!4'fD001!1'R#2!1'S#2!2'hA#3!1'T#2!2'hK#3!1'U#2!1'V#2").

(* [comment removed for export] *)
Definition node_rename (gb : nat) (cs : acs) (m : list (nat * nat)) : option acs :=
  if forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m then
    match mk_fwd m, mk_bwd m with
    | Some fw, Some bw =>
        let ok (v : nat) := match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end in
        if (csvars_all ok cs && match s_log (a_ss cs) with [] => true | _ => false end)%bool then
          let cs1 := rename_cs fw cs 0%nat in
          Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) (kn cs1) (Nat.max gb (csmaxv cs1))))
        else None
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Fixpoint bt_set (t : list bool) (i : nat) {struct i} : list bool :=
  match i, t with
  | O, [] => [true]
  | O, _ :: rest => true :: rest
  | S j, [] => false :: bt_set [] j
  | S j, x :: rest => x :: bt_set rest j
  end.
Definition bt_get (t : list bool) (i : nat) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2+1$i;R+5!4'B+1#1#2,6").
(* [comment removed for export] *)
Fixpoint evars_fo (gb : nat) (e : expr) (acc : list nat * list bool) : list nat * list bool :=
  match e with
  | ELit _ => acc
  | EVar v => if Nat.ltb v gb then acc else if bt_get (snd acc) v then acc else (v :: fst acc, bt_set (snd acc) v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_fo gb b (evars_fo gb a acc)
  | EExt _ _ _ a => evars_fo gb a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kvars_fo (gb : nat) (K : kentry) (acc : list nat * list bool) : list nat * list bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S50!2+^I!1+2+5!1+2+1!3'hL#6!1'^F#3#4!1'^F#2!3'hL#5#1!3'hL#52#3!3'hL#6#21$gb;R+5$K;R+W$acc;R0-WRN$K;R+W0#2:$a;R+\$w;R+5$v;R+C!3'hL#6#11$a;R+\$n;R+C3$a;R+\$n;R+C$k;R+54$lo;R+3$hi;R+3#3$x;R+C$m;R+3!3'hL#5#2#3$x;R+C$lo;R+3$hi;R+3!3'hL#6#3#4$a;R+\$n;R+C3$a1;R+\$n1;R+C$a2;R+\$n2;R+C!3'hL#7#1!3'hL#72!3'hL#7#3!3'hL#7!1'^F#4#5$a;R+\$n;R+C$c;R+34$a;R+\$n;R+C3").
Definition csvars_fo (gb : nat) (cs : acs) : list nat := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S60!1+2+5!1+2+1!2+^I01!2+^I+C+C!3'^K+C+C#1!3'^J+C+C#1$gb;R+5$cs;R+A&acc;R!5'fK2+C$acc;R2$e;R+C!3'hL#4#1#2!1'D!1'E#1!4,cJ01!1,Y+5!1,Y+12&acc;R!5'fK2+W$acc;R2$K;R+W!3'hM#5#1#2!1'^5#2#12&acc;R!5'fK2+8$acc;R2$m;R+8!3'hL#6!1'^H#1!3'hL#6!1'^G#1#2!1'M#3#12&acc;R!5'fK23$acc;R2$p;R3!3'hL#74!3'hL#75#2!1'Q#4#12&acc;R!5'fK23$acc;R2$p;R3!3'hL#84!3'hL#85#2!1'R#5#12&acc;R-^LRN$x;R+^L2!1'U#63#1$k;R+5$l;R+C$o;R+C!3'hL#:#1!3'hL#:#2#4#12&acc;R!3'hL#8!1'T#7#12!2'hN+5!3'^J01#1").
Fixpoint number_from (i : nat) (l : list nat) : list (nat * nat) :=
  match l with [] => [] | v :: rest => (v, i) :: number_from (S i) rest end.
Definition compact_map (gb : nat) (cs : acs) : list (nat * nat) := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$gb;R+5$cs;R+A!2'hO#2!2'hP#2#1").
Definition node_compact (gb : nat) (cs : acs) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$gb;R+5$cs;R+A!3'hQ#2#1!2'hR#2#1").

(* [comment removed for export] *)
Fixpoint regs_match_h (lo hi : nat) (seen : list nat) (rs ts : list expr) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' =>
      match t with
      | EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool
                  then (negb (existsb (Nat.eqb v) seen) && regs_match_h lo hi (v :: seen) rs' ts')%bool
                  else (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      | _ => (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      end
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition saddr_eqb_h (x y : saddr) : bool :=
  saddr_eqb x y || expr_eqb (eaddz (a_base x) (a_off x)) (eaddz (a_base y) (a_off y)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cover1 (k : list kentry) (b : expr) (i : Z) : option Z :=
  match k with
  | [] => None
  | K :: rest =>
      let hit := match K with
                 | KWord (SA kb kk) w _ =>
                     if (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool then Some (kk + Z.of_nat w) else None
                 | KZero (SA kb kk) (ELit l) | KFill (SA kb kk) (ELit l) _ | KBlob (SA kb kk) (ELit l) _ | KUnk (SA kb kk) (ELit l) =>
                     if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l) else None
                 | _ => None
                 end in
      match hit with Some e => Some e | None => cover1 rest b i end
  end.
Fixpoint cover_x (fuel : nat) (k : list kentry) (b : expr) (i : Z) (stop : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb stop i then true else
           match cover1 k b i with
           | Some e => if Z.ltb i e then cover_x f k b e stop else false
           | None => false
           end
  end.
(* [comment removed for export] *)
Definition kunk_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KUnk (SA b o) (ELit n) =>
      (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.leb (img_lo A) (img_hi A) && flat_x k b o (ELit n) && off_image_x k b o (ELit n) && cover_x (S (length k)) k b o (o + n))%bool
  | _ => false
  end.

Definition kentry_eqb_h (x y : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2'hS#6#3!2'^P!2'hS#4#2!2'^Q#3#1!2'^P0!2'^Q#5#2$x;R+W$y;R+W!2'^M!2'h7#2#1-WRN$x;R+W+1#2:$a;R+\$w;R+5$v;R+C-WRN$y;R+W+1#4:$a';R+\$w';R+5$v';R+C!2'^P!2'^P0!2'7#5#2!2'^Q#4#1$a0;R+\$n;R+C,6$a0;R+\$n;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n;R+C$c;R+3,6$a0;R+\$n;R+C,6$a;R+\$n;R+C-WRN$y;R+W+1#3:$a0;R+\$w;R+5$v;R+C,6$a';R+\$n';R+C1$a0;R+\$n0;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n0;R+C$c;R+3,6$a0;R+\$n0;R+C,6$a;R+\$n;R+C$k;R+5-WRN$y;R+W+1#4:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n0;R+C,6$a';R+\$n';R+C$k';R+5!2'^P2!2'7#4#1$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n0;R+C$c;R+3,6$a0;R+\$n0;R+C,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a;R+\$n;R+C-WRN$y;R+W+1#3:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n0;R+C,6$a0;R+\$n0;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a';R+\$n';R+C1$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n0;R+C$c;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a;R+\$n;R+C$c;R+3-WRN$y;R+W+1#4:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n0;R+C,6$a0;R+\$n0;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a';R+\$n';R+C$c';R+3!2'^P2!2'aA#4#1$a0;R+\$n0;R+C,6$a;R+\$n;R+C-WRN$y;R+W+1#3:$a0;R+\$w;R+5$v;R+C,6$a0;R+\$n0;R+C,6$a0;R+\$n0;R+C$k;R+5,6$lo;R+3$hi;R+3,6$e;R+C$m;R+3,6$e;R+C$lo;R+3$hi;R+3,6$a0;R+\$n0;R+C,6$a1;R+\$n1;R+C$a2;R+\$n2;R+C,6$a0;R+\$n0;R+C$c;R+3,6$a';R+\$n';R+C1").
(* [comment removed for export] *)
Definition kflat_h (k : list kentry) (K : kentry) : bool :=
  match K with
  | KWord (SA b o) w _ => flat_x k b o (ELit (Z.of_nat w))
  | KZero (SA b o) n | KBlob (SA b o) n _ | KWr (SA b o) n | KFill (SA b o) n _ | KUnk (SA b o) n => flat_x k b o n
  | _ => true
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_sub_covered (k : list kentry) (K : kentry) : bool :=
  match K with
  | KImg lo hi => existsb (fun X => match X with KImg lo' hi' => Z.leb lo' lo && Z.leb hi hi' | _ => false end) k
  | _ => false
  end.
Definition kn_incl1_h (k : list kentry) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$k;R!1+2+W$K;R+W-1RN$~R+1+1!3'^O+W$X;R+W!2'h7#1#2#22,^U-1RN$~R+1+1-1RN$~R+1+1!2'hT#2#12!3'^O+W$X;R+W!2'hU#1#2#2,62,^U-1RN$~R+1+1!2'hV#2#12,^U!2'hW#2#1").
Definition kn_incl_h (k : list kentry) (tk : list kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1+2+W$k;R0$tk;R0!3'=+W!1'hX#2#1").

Definition entails_h (lo hi : nat) (cs : acs) (ch : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S80!1'E#1!1'^5#1!1'M#1!1'Q#1!1'R#1!1'T#1!1'U#1!2+^I+C+C$lo;R+5$hi;R+5$cs;R+A$ch;R+A!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'^P!2'aA!1'cU#2!1'cU#1-2RN$x;R!1+2+Z+1!1'`Y02,^U$s;R+Z$l;R!1+2+Z,6-^7RN$x;R!1+^7+\+1!1'hY02$s;R+\,6,^U!5'hZ#4#3!1,Y+5!1'D!1'E#2!1'D0!2'h[!1'^5#21!2'h\#41!2'i0#42!2'i1#43!2'i1#44!2'`Q#45!2'i2#46!4'i3+8'i4!1'M#22!4'i37'i5!1'Q#23!4'i37'i5!1'R#24!2'^Q!1'T#25!2'i6!1'U#26!2'i7!1'V#2!1'V#1!2'^R!1'N#2!1'N#1!2'^R!1'O#1!1'O#2!2'^R!1'P#2!1'P#1!2'^R!1'S#2!1'S#1").

(* [comment removed for export] *)
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat).
Definition lc_bnd (c : loopctx) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$c;R+i8-i8RN$c;R+i8+5#12$lc_head;R+3$lc_next;R+A$lc_lo;R+5$hi;R+5#1$jc_id;R+5$jc_st;R+A$jc_sh;R+i9$b;R+5$jc_lo;R+5#2").

(* [comment removed for export] *)
Definition loop_ok (cs0 : acs) (J : nat) (N : expr) (inv : acs) : option Z :=
  let lo := S J in let hi := nxt inv in
  if (fresh_ok cs0 && Nat.leb (nxt cs0) J && Nat.ltb J hi && fresh_ok inv
      && expr_vars_lt (nxt cs0) N
      && match s_log (a_ss inv) with [] => true | _ => false end
      && Nat.eqb (length (s_regs (a_ss inv))) 32
      && kn_vars_lt lo (kn inv) && maps_vars_lt lo (a_maps inv) && pairs_vars_lt lo (a_vis inv) && pairs_vars_lt lo (a_ghost inv)
      && expr_vars_lt lo (a_brk inv) && fd_vars_lt lo (a_fd inv)
      && forallb (fun r => match r with EVar v => true | _ => expr_vars_lt lo r end) (s_regs (a_ss inv))
      && regs_match_h lo hi [] (s_regs (a_ss inv)) (s_regs (a_ss inv)))%bool
  then match xhi (kn cs0) N with Some nhi => if Z.ltb nhi two64 then Some nhi else None | None => None end
  else None.

(* [comment removed for export] *)
Definition loop_body_state (J : nat) (N : expr) (nhi : Z) (inv : acs) : acs :=
  add_kn inv [KRange (EVar J) 0 (nhi - 1); KRange (esub N (EVar J)) 1 nhi].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition branch_probe (cs : acs) : option expr :=
  match itab_lookup IT (pc cs) with
  | Some (Branch c rs1 rs2 _) =>
      Some (fst (cond_probe c (sr_get (s_regs (a_ss cs)) rs1) (sr_get (s_regs (a_ss cs)) rs2)))
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint diff_regs (i : nat) (ra rb : list expr) : list nat :=
  match ra, rb with
  | a :: ra', b :: rb' => if expr_eqb a b then diff_regs (S i) ra' rb' else i :: diff_regs (S i) ra' rb'
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition node_diamond_join (nx : nat) (joinpc : Z) (rs : list nat) (ca cb : acs) : option acs :=
  let hv := nodup Nat.eq_dec (diff_regs 0 (s_regs (a_ss ca)) (s_regs (a_ss cb)) ++ rs) in
  let v0 := Nat.max nx (Nat.max (nxt ca) (nxt cb)) in
  let hi := (v0 + length hv)%nat in
  let regsJ := sr_fresh (s_regs (a_ss ca)) hv v0 in
  let knJ := List.filter (fun K => existsb (fun X => kentry_eqb X K) (kn cb)) (kn ca) in
  let csJ := with_ss ca (mk_ss joinpc regsJ knJ hi) in
  if (Z.eqb (pc ca) joinpc && Z.eqb (pc cb) joinpc
      && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
      && Nat.eqb (length regsJ) 32
      && Nat.leb nx0 v0
      && entails_h v0 hi ca csJ && entails_h v0 hi cb csJ)%bool
  then Some csJ else None.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition via_ok (cs js : acs) (lo : nat) : bool :=
  (match s_log (a_ss js) with [] => true | _ => false end
   && Nat.eqb (length (s_regs (a_ss js))) 32
   && Nat.leb nx0 (nxt cs) && Nat.leb (nxt cs) lo && Nat.leb lo (nxt js))%bool.

(* [comment removed for export] *)
Definition node_abstractcell (cs : acs) (b : expr) (n : Z) : option acs :=
  let '(bb, bo) := split_lit b in
  let K := KUnk (SA bb bo) (ELit n) in
  if kunk_covered (kn cs) K then Some (set_kn cs (K :: kn_cutout (kn cs) bb bo (ELit n))) else None.

(* [comment removed for export] *)
Definition respell_ok (k : list kentry) (a e : expr) : bool :=
  match decide_branch k BC_EQ a e with
  | Some true => true
  | _ => (* [comment removed for export] *)
      match erange k (mkAlu ALU_SUB a e) with
      | Some (lo, hi) => Z.eqb lo 0 && Z.eqb hi 0
      | None => false
      end
  end.
Definition node_respell (cs : acs) (r : nat) (e : expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$cs;R+A$r;R+5$e;R+C-1RN$~R+1!1+^7+A!2'^P!2'^P!2'^P!2'^N,dK#2!2'^N#2}P!2'`Q!1'dS#3#1!3'i:!1'^5#3!2'^>#3#2#12!2,^8+A!3'dX#3#2#1!1,[+A").

(* [comment removed for export] *)
Definition sa_of (b : expr) : saddr := let '(bb, bo) := split_lit b in SA bb bo.
Fixpoint hw_apply (k : list kentry) (a : saddr) (x : nat) (found : bool) : list kentry :=
  match k with
  | [] => []
  | KWord a' w v :: r =>
      if saddr_eqb a' a then (if found then hw_apply r a x true else KWord a' w (EVar x) :: hw_apply r a x true)
      else KWord a' w v :: hw_apply r a x found
  | K :: r => K :: hw_apply r a x found
  end.
(* [comment removed for export] *)
Fixpoint hw_val (k : list kentry) (a : saddr) : expr :=
  match k with
  | [] => ELit 0
  | KWord a' _ v :: r => if saddr_eqb a' a then v else hw_val r a
  | _ :: r => hw_val r a
  end.
Fixpoint hw_go (k : list kentry) (bs : list expr) (x : nat) : list kentry :=
  match bs with
  | [] => k
  | b :: r => hw_go (hw_apply k (sa_of b) x false) r (S x)
  end.
Definition node_havocwords (cs : acs) (bs : list expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1'J#1$cs;R+A$bs;R!1+2+C-1RN$~R+1!1+^7+A!1'`T#22&ss;R!1'E#2+K!2,^8+A!2'^0#3!4'^1!1'I#1!1'D#1!3'i;!1'H#1#20!2'^60!2'i<+C#2!1,[+A").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS : list Z :=
  [x_imemset A; x_imemcpy A; x_memset A; x_memcpy A; x_memiszero A; x_envscan A; x_pnscan A] ++ stops_more A.

(* [comment removed for export] *)
Fixpoint mk_itab_ranges_acc (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => mk_itab_ranges_acc rs' (mk_itab_fuel segs n lo t)
  end.
Definition mk_itab_ranges (rs : list (Z * nat)) : itab := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$rs;R!1+2!2+^I+3+5!2'i=#1!1,_1+i>").

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BRK_ASLR : Z := 0x80000000.
Definition NX0 : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00}9").   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition K_RND : nat := 25.

(* [comment removed for export] *)
Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'^W'i?").
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!3'^J+C+3'i@!2'^S!3'^K+C+3'i@!2'g;!1,c?|40;#3}8|30;$i;R+3$ty;R+3$v;R+C!3,_C+W!3,`D!2,`0012!1,F#2!3,_C+W!3,`D!2,`00!2'^S1!1,c?32#1!1,Y+W").

(* [comment removed for export] *)
Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
  [KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 2047;
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000; KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE9;
   KRange e_sp0 0x7fff80000000 0x7fffffffff40;
   KRange (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE;
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  (* [comment removed for export] *)
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 4 6 (ELit 4096)
  ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
  ++ [atr;
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].

(* [comment removed for export] *)
Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2,`E!2,`0!3'^J+C+3'iA!3'^K+C+3'iA!1,F!1,c?|40;").
(* [comment removed for export] *)
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.
(* [comment removed for export] *)
Definition init_kn_zero (A : atable) : list kentry := init_kn_with atr_entry_zero A.

Definition init_regs : list expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10}2!3'^2!3'iB+C!1,F,G}P0'iC").
(* [comment removed for export] *)
Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (ELit CEIL, ELit (2^47 - CEIL))].

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2'aD!1'cA#1!1'c@#1|10;$kn0;R!1+2+W$A;R+iD!;,iE!4'iF!1'iG#1'iH#2'iI!1,Y+iJ0'iK,G!1'iL#1!1,Y!2+^I+C+C!2'^S!1'iM0!1'iM!2'aD!2'dQ!1,c?1!1,c?|50f;'eR!2'iN!1,c?|<000;!1,_R'iO,iP,6").
Definition init_acs_of (A : atable) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$A;R+iD!2'iQ!1'iR#1#1").        (* [comment removed for export] *)
Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ba64; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1ea4; x_imemcpy := 0xe1e28; x_memset := 0x116934; x_memcpy := 0x116530; x_memiszero := 0xe2508;
     x_istrncpy := 0xe23b8; x_sealed := 0x1205f; x_popfree := 0x52a70;
     x_sniff := 0x1414dc; sniff_tab := 0x24f40; sniff_cell := 0x14bf00;
     x_envscan := 0x10d5e4; x_envscan_k := 0x10d5f0; x_pnscan := 0x10d6a8; x_pnscan_k := 0x10d6b4;
     stops_more := [0x506e4; 0x51d08; 0xddd88; 0xee070; 0xee200]  (* [comment removed for export] *) |}.

(* [comment removed for export] *)
Definition ASAN_TEXT_LO : Z := 0x4ba64.
Definition ASAN_TEXT_N : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'iS!1,iT!1,iU!1,iV!1,iU!1,iU!1,iW!1,iX,iY").
Definition asan_init : acs := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'iZ'i[").

(* [comment removed for export] *)
Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x671000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x4ba54; rw_lo := 0x142000; rw_len := 0x52f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xe1e94; x_imemcpy := 0xe1e18; x_memset := 0x116924; x_memcpy := 0x116520; x_memiszero := 0xe24f8;
     x_istrncpy := 0xe23a8; x_sealed := 0x1205f; x_popfree := 0x52a60;
     x_sniff := 0x1414cc; sniff_tab := 0x24f40; sniff_cell := 0x14bf80;   (* [comment removed for export] *)
     x_envscan := 0x10d5d4; x_envscan_k := 0x10d5e0; x_pnscan := 0x10d698; x_pnscan_k := 0x10d6a4;
     stops_more := [0x506d4; 0x51cf8; 0xddd78; 0xee060; 0xee1f0] |}.
Definition BOTH_TEXT_LO : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,c?|B0ba54;").
Definition BOTH_TEXT_N : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'iS!1,iT!1,iU!1,iV!1,iU!1,iU!1,iW!1,i\,iY").
Definition both_init : acs := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'iZ'j0").

End APC.
