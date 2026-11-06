(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AxSymExec3BK.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @spiece]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Numbers; @BinNums; @Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @listZ_eqb]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @false]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mkind]; [@Corelib; @Init; @Datatypes; @true]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @amap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mkind_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @am_kind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @KHOLE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @is_tok_kind]; [@Stdlib; @Lists; @List; @forallb]; [@Corelib; @Init; @Datatypes; @negb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @is_fog]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @is_hole]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @acs]; [@Corelib; @Lists; @ListDef; @nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @expr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_ss]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ELit]; [@Corelib; @Numbers; @BinNums; @Z0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_know]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_pc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_next]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sym_state]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @ACS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_maps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_totsz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_ylo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_eager]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_ghost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_abytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_brk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_fd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_tidset]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_hna]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @a_hlz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kentry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @SSR]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sentry]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @saddr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @with_ss]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mk_ss]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sr_upd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @set_kn]; [@Corelib; @Init; @Datatypes; @app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Init; @Datatypes; @option]; [@Corelib; @Init; @Datatypes; @Some]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @two64]; [@LinuxProcessSemantics; @Riscv; @Instr; @aluop]; [@LinuxProcessSemantics; @Riscv; @Instr; @mulop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @lit_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @reg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkAlu]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkMd]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@Corelib; @Init; @Logic; @eq_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EAlu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EMd]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EVar]; [@Corelib; @Init; @Datatypes; @O]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_sp0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @eadd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_sppg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @escale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @V_S2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @esub]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_envp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @V_ENVC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @eaddz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_auxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_str0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @V_L0]; [@Corelib; @Numbers; @BinNums; @xH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @V_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @split_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_atrandom]; [@Corelib; @Init; @Datatypes; @orb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @ltb]; [@Stdlib; @Lists; @List; @existsb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @expr_vars]; [@Corelib; @Init; @Datatypes; @andb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @expr_eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @all_live]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @a_base]; [@Corelib; @Init; @Datatypes; @prod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @live_vars]; [@Stdlib; @Lists; @List; @filter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_gc_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ptree]; [@Corelib; @Init; @Datatypes; @unit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @vkey]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @expr_all_live_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @live_vars_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_gc_entry_t]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Init; @Logic; @f_equal]; [@Stdlib; @PArith; @BinPos; @Pos; @to_nat]; [@Stdlib; @PArith; @BinPos; @Pos; @of_succ_nat]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Datatypes; @S]; [@Stdlib; @PArith; @Pnat; @SuccNat2Pos; @id_succ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @live_agree]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Corelib; @Init; @Logic; @not]; [@Corelib; @Init; @Datatypes; @cons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_set]; [@Corelib; @Init; @Datatypes; @tt]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_gss]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_spec]; [@Corelib; @Init; @Datatypes; @reflect]; [@Corelib; @Init; @Logic; @False_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @in_live_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_gso]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @vkey_inj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @expr_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @expr_vars_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @live_agree_var]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EAluw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EMdw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EExt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EBlob]; [@Stdlib; @Lists; @List; @fold_right]; [@Corelib; @Init; @Datatypes; @list_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @live_agree_expr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @afd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @hop]; [@Corelib; @Init; @Datatypes; @fst]; [@Corelib; @Init; @Datatypes; @snd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @am_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @am_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @PTLeaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @pt_get_leaf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @live_agree_fold]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @SA]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @ex]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @Lists; @List; @In]; [@Stdlib; @Lists; @List; @existsb_exists]; [@Corelib; @Init; @Logic; @ex_ind]; [@Corelib; @Init; @Logic; @False]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Lists; @List; @forallb_forall]; [@Corelib; @Init; @Logic; @True]; [@Corelib; @Init; @Logic; @I]; [@Stdlib; @Bool; @Bool; @andb_true_r]; [@Stdlib; @Bool; @Bool; @andb_assoc]; [@Stdlib; @Arith; @PeanoNat; @Nat; @leb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @forallb_expr_vars]; [@stdpp; @tactics; @f_equal_help]; [@Stdlib; @Lists; @List; @filter_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @live_vars_agree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KWord]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KZero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KImg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @expr_all_live_t_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KAlign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KRange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KWr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KDisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KFill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KUnk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @cs_gc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @cs_gc_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @expr_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @saddr_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @hop_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @hop_n]; [@Corelib; @Classes; @Morphisms; @trans_co_eq_inv_impl_morphism]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @fresh_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sidecond]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @carryK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @mkbc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @facts_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_log]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @sym_execTXBI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @mk_kix]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @carry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sym_execTX]; [@Corelib; @Classes; @RelationClasses; @eq_Transitive]; [@Corelib; @Classes; @Morphisms; @reflexive_proper]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @bctx]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_eq_dom_reflexive]; [@Corelib; @Classes; @RelationClasses; @eq_Reflexive]; [@Corelib; @Classes; @RelationClasses; @symmetry]; [@Corelib; @Classes; @RelationClasses; @eq_Symmetric]; [@Corelib; @Classes; @Morphisms; @eq_proper_proxy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @sym_execTX_know]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @carryK_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @sym_execTXBI_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @run_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @run_block_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @saddr_eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @ranges_apart_xB]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @Logic; @FunctionalExtensionality; @functional_extensionality]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kentry_apart_bB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kentry_apart_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ranges_apart_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @ranges_apart_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @sprep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @ranges_apart_pB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kentry_apart_bpB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kentry_apart_bp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ranges_apart_p]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @ranges_apart_pB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @mk_sprepB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kimg_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @bc_fk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_unfillB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_unfill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mk_sprep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @bc_fk_mkbc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @mk_sprepB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kentry_apart_bpB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_unfillM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_unfillB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwr_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kzero_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kfill_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kunk_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kzero_cutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kfill_cutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kunk_cutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @havoc1B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @havoc1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kzero_cutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kfill_cutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kunk_cutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kentry_apart_bB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @havoc1pB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @havoc1p]; [@Stdlib; @Lists; @List; @flat_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_havocB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_havoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @havoc1pB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_havocM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_havocB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kcutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwr_cutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwr_cut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kcut]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kcutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @cutout1B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @cutout1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwr_cutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @cutout1pB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @cutout1p]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_cutoutB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_cutout]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @cutout1pB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_cutoutM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_cutoutB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kimg_cut1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lres]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @know_lookupB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kreadZB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kreadZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @know_lookup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @know_lookupB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kread8eB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kread8e]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwritableB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwritable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @xloB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @xinsideB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xlo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xinside]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @xloB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @xinsideB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwritable_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwritable_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @xhiB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xhi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @xhiB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kzero_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kzero_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kfill_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kfill_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @off_image_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @off_image_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @base_rangeB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @flat_xB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @flat_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @base_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @base_rangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @lin_ge0B]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @len_eqbB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @len_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xterms]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_ge0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @lin_ge0B_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @ealignB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @page_alignedB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @page_aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ealign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @ealignB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @pc]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @fetch_word]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @is_ecall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xlo1B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xlo1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_brange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zlit64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @erangeB]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @lin_srangeB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @erange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @lin_srange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @erangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @lin_srangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @lin_brangeB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @lin_brangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xhi1B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xhi1]; [@Stdlib; @ZArith; @BinInt; @Z; @min]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @deand]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xb2B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xb2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xlo1B_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xhi1B_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xlo2B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xlo2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xb2B_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xhi2B]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @xhi2]; [@Corelib; @Init; @Datatypes; @nat_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kread_bytesB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kread_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kreadZB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kread_bytesB_eqf']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @add_kn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @zbytes_le_to_Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @nxt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @residue_fact]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @bump]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @set_reg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @esize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @bigb]; [@Corelib; @Lists; @ListDef; @seq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_havoc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_bigsubst]; [@Stdlib; @Lists; @List; @find]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @find_containingB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @find_containing]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @mkSrlB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @shadow_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_ofB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkSrl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @mkSrlB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @lit_lazy_holds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_bandB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_band]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @flat_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @KRWLAZY]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_factsB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @find_containingB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_ofB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_bandB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @vis_cost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shadow_factsB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @vis_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @vis_add_ref]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @find_disj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @disj_side_fact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @disj_var_fact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_shdisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_shdisj_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @reg_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @page_up]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_len_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @inside_mapsB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @inside_maps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @iv_coalesce]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @iv_sort]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @lit_ivs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @inside_runsB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @inside_runs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @safe_rangeB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @safe_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_top]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @inside_mapsB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @inside_runsB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @grant_keep_bB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @grant_keep_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @safe_rangeB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kimg_clip]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_grant_filterB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_grant_filter]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @grant_keep_bB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_rezeroB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_rezero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_rezeroM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_rezeroB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @fixed_in_arm]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @fixed_args]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @TOPC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @KRW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @KNONE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @KNONELAZY]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @fixed_in_args]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @fixed_in_args_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @budget_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @rekind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @HSub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @HCons]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_fixed_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_fixed_in_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @ENOMEM_RET]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @dest_lfact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @dest_rfact]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @AM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @replace_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_destroyed_with]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_destroyed_with_ref]; [@Corelib; @Lists; @ListDef; @map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @dest_cases]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_null]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @gap_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @no_holes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @add_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @grant_vlo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @null_kend]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kdisj_fixed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kdisj_new]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kdisj_shadow_twin]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @contra_cs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @first_run]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @zcdiv']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_contra]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_mmap2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_gate]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_fixed_free]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_null_nosplit_contra]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mmap_fixed_free1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_mprotect]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_mprotect_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @amap_matchB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @amap_match]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @len_eqbB_eqf]; [@Stdlib; @Lists; @List; @fold_left]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_unfillM_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @page_alignedB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kzero_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @amap_matchB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_munmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_munmap_ref]; [@Stdlib; @ZArith; @BinInt; @Z; @land]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @KFOG]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @vis_here]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @CEIL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_unvis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_unvis_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kfind_litword]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kimg_cut]; [@Stdlib; @Lists; @List; @nth_error]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @hop_sub]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @SPIN_WORD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @ret_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @after_call]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_havocM_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @off_image_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwritable_xB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_fill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_fill_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @copy_factsB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @copy_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kread8eB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kread_bytesB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @copy_factsB_eqf']; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @after_call2]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @NCS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kblob_prefix]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @copy_factsB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_copy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_copy_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @x_memiszero]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kwritableB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_miz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_miz_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @img_covB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @img_cov]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @x_istrncpy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @x_sealed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @SEALED_W]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_istrncpy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_istrncpy_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @x_popfree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @popfree_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @x_sniff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @sniff_tab]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @sniff_cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kn_readableB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_readable_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @extKB]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kn_readable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @extK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @kn_readableB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @img_covB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3BK; @AX2BK; @extKB_eqf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_sniff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @summary_sniff_ref]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kentry_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kw_argv1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_argv1w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @V_ARGC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @e_str1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @asubst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @esubst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @FdFile]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @nt_set]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @nt_get]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @erename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @a_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @arename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @evars_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kvars_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @emaxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kmaxv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @krename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mrename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @prename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @frename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @hrename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @evars_fo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kvars_fo]; [@Stdlib; @Lists; @List; @rev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @number_from]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @csvars_fo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @node_rename]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @compact_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @saddr_eqb_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kflat_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kentry_eqb_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kimg_sub_covered]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kunk_covered]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_incl1_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @s_resv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @regs_match_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_incl_h]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @kn_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @maps_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @pairs_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @fd_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @hist_vars_lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @list_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @amap_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @pair_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @afd_eqb]; [@Stdlib; @Bool; @Bool; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @hop_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @loopctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @shape]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @respell_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @hw_go]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @WithSegs; @mk_itab_ranges_acc]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @e_atrb]; [@Corelib; @Lists; @ListDef; @repeat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @e_sp0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @atable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @ACS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @mk_ss]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @a_entry]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @init_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @NX0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @amap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @MBASE_MIN]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @init_vis]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @vis_cost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @escale]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @V_BRK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @FdStd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @hop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @init_acs_of_with]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @init_kn]; [@Corelib; @Init; @Nat; @of_num_uint]; [@Corelib; @Init; @Number; @UIntDecimal]; [@Corelib; @Init; @Decimal; @D2]; [@Corelib; @Init; @Decimal; @D4]; [@Corelib; @Init; @Decimal; @D7]; [@Corelib; @Init; @Decimal; @D1]; [@Corelib; @Init; @Decimal; @Nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @init_acs_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @ASAN]; [@Corelib; @Init; @Decimal; @D5]; [@Corelib; @Init; @Decimal; @D0]; [@Corelib; @Init; @Decimal; @D9]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanCoreK; @APCK; @BOTH]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module APCK.
Import AX2K. Import AX2BK.

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
Definition TOPC : Z := 0x7fffff800000.

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

(* [comment removed for export] *)
Fixpoint hole_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SAlt2 a b => hole_only a && hole_only b
  | SCase _ _ a b => hole_only a && hole_only b
  | _ => false
  end.

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
Inductive hop : Type := HCons (b n : expr) | HSub (b n : expr).
Definition kind_noneb (k : mkind) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$k;R+8-8RN$k;R+8+1#16,6,6,9,9,6,6").
Definition kind_lazyb (k : mkind) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$k;R+8-8RN$k;R+8+1#16,6,9,6,9,6,6").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_tok_kind (k : mkind) : bool := match k with KFOG | KHOLE => true | _ => false end.
Definition is_hole (m : amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$m;R+:!2';!1'<#1,=").
Definition is_fog (m : amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$m;R+:!1'>!1'<#1").
Definition no_fog (ms : list amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$ms;R!1+2+:!3'?+:$m;R+:!1'@!1'A#1#1").
Definition no_holes (ms : list amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$ms;R!1+2+:!3'?+:$m;R+:!1'@!1'B#1#1").


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
  a_tidset : bool;              (* [comment removed for export] *)
  a_hna   : list hop;           (* [comment removed for export] *)
  a_hlz   : list hop            (* [comment removed for export] *)
}.

Definition reg (cs : acs) (n : nat) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$n;R+5!4'D+E#1!1'F!1'G#2!1,H,I").
Definition kn (cs : acs) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+C!1'J!1'G#1").
Definition pc (cs : acs) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+C!1'K!1'G#1").
Definition nxt (cs : acs) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+C!1'L!1'G#1").

Definition with_ss (cs : acs) (ss : sym_state) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$ss;R+M!=,N#1!1'O#2!1'P#2!1'Q#2!1'R#2!1'S#2!1'T#2!1'U#2!1'V#2!1'W#2!1'X#2!1'Y#2!1'Z#2").
Definition mk_ss (p : Z) (sr : list expr) (k : list kentry) (nx : nat) : sym_state := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$p;R+3$sr;R!1+2+E$k;R!1+2+[$nx;R+5!6,\#4#3!1,^0+^1#2#1!1,^2+^3").
Definition set_reg (cs : acs) (n : nat) (e : expr) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$cs;R+C$n;R+5$e;R+E&ss;R!1'G#3+M!2'^4#4!4'^5!1'K#1!3'^6!1'F#1#3#2!1'J#1!1'L#1").
Definition set_pc (cs : acs) (p : Z) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$p;R+3&ss;R!1'G#2+M!2'^4#3!4'^5#2!1'F#1!1'J#1!1'L#1").
Definition set_kn (cs : acs) (k : list kentry) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$k;R!1+2+[&ss;R!1'G#2+M!2'^4#3!4'^5!1'K#1!1'F#1#2!1'L#1").
Definition add_kn (cs : acs) (k : list kentry) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$k;R!1+2+[!2'^7#2!3'^8+[#1!1'^9#2").
Definition bump (cs : acs) (d : nat) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$d;R+5&ss;R!1'G#2+M!2'^4#3!4'^5!1'K#1!1'F#1!1'J#1!2'^:!1'L#1#2").
Definition set_regs (cs : acs) (sr : list expr) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$sr;R!1+2+E&ss;R!1'G#2+M!2'^4#3!4'^5!1'K#1#2!1'J#1!1'L#1").

Definition lit_of (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S10!1,^2+3$e;R+E-ERN$e;R+E!1+^;+3#18$z;R+3!2,^<+3!2'^=#1'^>$n;R+50$op;R+^?$a;R+E$b;R+E0$op;R+^?$a;R+E$b;R+E0$op;R+^@$a;R+E$b;R+E0$op;R+^@$a;R+E$b;R+E0$sx;R+1$lo;R+5$n;R+5$e0;R+E0$sx;R+1$k;R+5$i;R+3$n;R+50").
Definition reg_lit (cs : acs) (n : nat) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$n;R+5!1'^A!2'^B#2#1").

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition esub (a b : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+E$b;R+E!3'^C,^D#2#1").
Definition escale (c : Z) (e : expr) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$c;R+3$e;R+E!3'^E,^F!1,H#2#1").
Definition eaddz (a : expr) (z : Z) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+E$z;R+3!3'^C,^G#2!1,H#1").

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
Definition V_HW : nat := 9.     (* [comment removed for export] *)
Definition V_S2A : nat := 10.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_sppg : expr := eadd (escale 32768 (EVar V_S1)) (escale 4096 (EVar V_S2A)).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_sp0 : expr :=
  EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar V_S1))
       (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar V_S2)) (EMd M_MUL (ELit 4096) (EVar V_S2A))).
Lemma e_sp0_unfold : e_sp0 = eadd e_sppg (escale 16 (EVar V_S2)).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S40|40;!1,^K0}6|<000;vv!2,^H+E!3,^I,^G!3,^J,^F!1,H!1,^K|?0000;!1,^L,^M!3,^I,^G!3,^J,^F!1,H1!1,^L2!3,^J,^F!1,H!1,^K3!1,^L}:!3+^N+E'^O!2'^P'^Q!2'^R1!1,^L'^S").
Qed.

(* [comment removed for export] *)
Definition e_top : expr := eaddz e_sppg (-8388608).
Definition e_stk_len : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10|10;!2'^T!1,H!2'^U!2'^V!1,^K0!1,^K|50f;!1,^K|G000000;'^Q").

(* [comment removed for export] *)
Definition e_envp : expr := eadd e_sp0 (eadd (escale 8 (EVar V_ARGC)) (ELit 16)).
Definition e_auxv : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10!1,^K|30;!2'^P'^W!2'^P!2'^R0!1,^L'^X!1,H0").
Definition e_str0 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'^Y'^Z!1,^K|720;").
Definition e_str1 : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'^P'^[!2'^Y!1,^L'^\!1,^K,_0").
Definition e_atrandom : expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'^P'^[!2'^R!1,^K|30;!1,^L'_1").
(* [comment removed for export] *)
Definition e_auxb : expr * Z := split_lit e_auxv.
Definition e_atrb : expr * Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'_2'_3").


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

Definition live_vars (cs : acs) : list nat :=
  let acc := fold_right expr_vars [] (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars (a_base a) (expr_vars v acc)
                                      | KZero a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KBlob a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KWr a n => expr_vars (a_base a) (expr_vars n acc)
                                      | KFill a n _ => expr_vars (a_base a) (expr_vars n acc)
                                      | KUnk a n => expr_vars (a_base a) (expr_vars n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars (am_base m) (expr_vars (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars (fst p) (expr_vars (snd p) acc)) acc (a_ghost cs) in
  (* [comment removed for export] *)
  let acc := fold_right (fun hp acc => match hp with HCons b n | HSub b n => expr_vars b (expr_vars n acc) end) acc (a_hna cs) in
  let acc := fold_right (fun hp acc => match hp with HCons b n | HSub b n => expr_vars b (expr_vars n acc) end) acc (a_hlz cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars l (expr_vars o acc) | _ => acc end in
  expr_vars (a_brk cs) acc.

Definition all_live (live : list nat) (e : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$live;R!1+2+5$e;R+E!3'?+5$v;R+5!2'_4!2'_5#1/nx0;!3'_6+5!1'7#1#3!2'_7#1!1,^0+5").

Definition kn_gc_entry (spb : expr) (spk : Z) (live : list nat) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S30!2'^U#2#1-^3RN$a;R+^3+1#21$b;R+E$k;R+3-ERN$n0;R+E+1#38$n;R+3!1'@!2'_8!2'_9#3#9!2'_:0#8$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k0;R+5$i;R+3$n;R+5,9!1'@!2'_8!2'_9#3#:!2'_:0#9$spb;R+E$spk;R+3$live;R!1+2+5$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!1'@!2'_8!2'_9#2#9!2'_:!2'^U#1!1'_;#4#8$a;R+^3$n0;R+E1$a;R+^3$n0;R+E$k0;R+5-^3RN$a;R+^3+1#31$b;R+E$k;R+3-ERN$n0;R+E+1#48$n;R+32$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k1;R+5$i;R+3$n;R+5,9$lo;R+3$hi;R+3,9$e;R+E$m;R+3!2'_<#4#2$e;R+E$lo;R+3$hi;R+3!2'_<#5#3$a;R+^3$n;R+E,9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!2'_8!2'_8!2'_8!2'_<#6!1'_=#4!2'_<#6#3!2'_<#6!1'_=#2!2'_<#6#1$a;R+^3$n0;R+E$c;R+3-^3RN$a;R+^3+1#31$b;R+E$k;R+3-ERN$n0;R+E+1#48$n;R+32$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k0;R+5$i;R+3$n;R+5,9$a;R+^3$n0;R+E1").

Definition cs_gc_ref (cs : acs) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+C-_>RN$x;R!2+_>+E+3+C!1'_2!2'^B#1}21$spb;R+E$spk;R+3&live;R!1'_?#3!1+2+5!2'^7#4!3'_@+[!3'_A#3#2#1!1'^9#4").

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
Definition live_vars_t (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_t PTLeaf (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
                                      | KZero a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KWr a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KFill a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KUnk a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_t (am_base m) (expr_vars_t (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_ghost cs) in
  let acc := fold_right (fun hp acc => match hp with HCons b n | HSub b n => expr_vars_t b (expr_vars_t n acc) end) acc (a_hna cs) in   (* [comment removed for export] *)
  let acc := fold_right (fun hp acc => match hp with HCons b n | HSub b n => expr_vars_t b (expr_vars_t n acc) end) acc (a_hlz cs) in   (* [comment removed for export] *)
  let acc := match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o acc) | _ => acc end in
  expr_vars_t (a_brk cs) acc.
Definition in_live_t (t : ptree unit) (v : nat) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+_B+_C$v;R+5-^;RN$x;R!1+^;+_C+1!3'_D+_C#2!1'_E#12$u;R+_C,9,6").
Fixpoint expr_all_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if Nat.ltb n nx0 then true else in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_t t x then expr_all_live_t t y else false
  | EExt _ _ _ x => expr_all_live_t t x
  | EBlob _ _ _ _ => true
  end.
Definition kn_gc_entry_t (spb : expr) (spk : Z) (t : ptree unit) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S30!2'^U#2#1-^3RN$a;R+^3+1#21$b;R+E$k;R+3-ERN$n0;R+E+1#38$n;R+3!1'@!2'_8!2'_9#3#9!2'_:0#8$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k0;R+5$i;R+3$n;R+5,9!1'@!2'_8!2'_9#3#:!2'_:0#9$spb;R+E$spk;R+3$t;R!1+_B+_C$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!1'@!2'_8!2'_9#2#9!2'_:!2'^U#1!1'_;#4#8$a;R+^3$n0;R+E1$a;R+^3$n0;R+E$k0;R+5-^3RN$a;R+^3+1#31$b;R+E$k;R+3-ERN$n0;R+E+1#48$n;R+32$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k1;R+5$i;R+3$n;R+5,9$lo;R+3$hi;R+3,9$e;R+E$m;R+3!2'_F#4#2$e;R+E$lo;R+3$hi;R+3!2'_F#5#3$a;R+^3$n;R+E,9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!2'_8!2'_8!2'_8!2'_F#6!1'_=#4!2'_F#6#3!2'_F#6!1'_=#2!2'_F#6#1$a;R+^3$n0;R+E$c;R+3-^3RN$a;R+^3+1#31$b;R+E$k;R+3-ERN$n0;R+E+1#48$n;R+32$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k0;R+5$i;R+3$n;R+5,9$a;R+^3$n0;R+E1").
Definition cs_gc (cs : acs) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$cs;R+C-_>RN$x;R!2+_>+E+3+C!1'_2!2'^B#1}21$spb;R+E$spk;R+3&live;R!1'_G#3!1+_B+_C!2'^7#4!3'_@+[!3'_H#3#2#1!1'^9#4").

(* [comment removed for export] *)
Definition live_agree (acc : list nat) (t : ptree unit) : Prop :=
  forall v, existsb (Nat.eqb v) acc = in_live_t t v.
Lemma vkey_inj : forall a b, vkey a = vkey b -> a = b.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80!1'_L#3!1'_L#2!1'_K0!1'_K!1'_L#4!1,_N#4!1'_O#4!1,_N#6!1,_N#5$a;R+5$b;R+5$H;R!3+^N+_I!1'_E#2!1'_E#1&H;R!6'_J+_I+5'_K01#1!3+^N+52!1'_K1&H;R!6'_M+53$n;R+5!3+^N+5#13#145!3+^N+542&H;R!6'_M+53$n;R+5!3+^N+56#1#145!3+^N+574!6'_J+5+5$t;R+5-5RN$n;R+5+5#12#7$~R+5#167#1").
Qed.
Lemma live_agree_var : forall acc t n,
  live_agree acc t -> live_agree (if existsb (Nat.eqb n) acc then acc else n :: acc) (pt_set (vkey n) tt t).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SO0!1+2+5!3+^N+5#1#3!3+^N+5#2#4!1'_S2!1'7#3!1'7#5!1'_E#3!3+^N+5#3#5!1'7#1!1'7#7!3'_6+59#9!3,_T+5#7#9-1RN$~R+10:2#9;!1+^;+_C-^;RN$x;R!1+^;+_C+1#12$u;R+_C,9,6!1'7#6!3'_6+5?#8!1'7#9!1'7#:!3'_6+5!1'7#8#:!1'_E#6!4'_U+_CD,_V#7!1'_E#4!3'_D+_C#7F!3'_6+55<!1'7#4!3'_6+55#9!3'_6+5A#=!3+^N+5#7#9!3+^N+5#8#:!3+^N+_IFD$acc;R0$t;R!1+_B+_C$n;R+5$H;R!2'_P#3#2vd$v;R+5vd&s;R!2'_Q#1#3!2+_R1!1'_S1-_RRN$s;R!2+_R23!3+^N+1!3'_6+54-1RN$~R+10!3'_6+55#72#7!3,_T+5#5#7-^;RN$x;R!1+^;+_C+1!3'_D+_C!4'_U+_C!1'_E#5,_V#662$u;R+_C,9,6#12$e;R2!1$e;R7!6'_W+5#6$v;R+5!3+^N+1!3'_6+58<-^;RN$x;R!1+^;+_C+1!3'_D+_C!4'_U+_C!1'_E#7,_V#8!1'_E#12$u;R+_C,9,6!6'_W=!2,^<+_C,_V$o;R=!3+^N+1!3'_6+59<>&b;R@+1&E;R!2,^H+1#1!3+^N+1:#1!1-1RN$b;R+1%E;R!3+^N+1!3'_6+5A#;#1!3+^N+1!3'_6+5B-1RN$~R+10#22#<!3,_T+5#:#<,9#22$E;R!3+^N+1C,9#1$E;R!3+^N+1C,6vd!6'_W+1,9$b;R+1!3+^N+1!2'_4#1!3'_6+5B#<,9!2,^H+1,9!2'7#9#9!1'_X#9!3+^N+1!3'_6+5A!3,_T+5#9#;,9#1!3'_D+_CED!4'_Y+_CD,_V#7#4#1#1$n;R3!1$NE;R!1'_S7!6'_W=G$o;R=!3+^N+1H>vd!6'_M+1!3'_6+5I#8$b;R+1!3+^N+1H#1&b;R@+1-1RN$b;R+1!3+^N+1!3'_6+5?-1RN$~R+10#12#:!3,_T+5#8#:!3'_6+5?#:#12!2,^H+1Jvd&r;R!2'_Z#5#7!2+_[!3+^N+5#5#7!2'7#5#7&b;R!2'7#6#8+1-_[RN$b;R+1$r;R!2+_[!3+^N+5#8#:#1!3+^N+1!2'_4#2KK#22$e;RL!1$e;RM!2'_\!3+^N+1!2'_4,9KK!1#6#1#1$n;R!1'_SL!1$n0;R!1'_SM!2,^H+1K#1!3+^N+1!3'_6+55;J!2'`0#7#4!1#5#4!3+^N+1!3'_6+5I-1RN$~R+10@2#8!3,_T+5#6#8-^;RN$x;R!1+^;+_C+1G2$u;R+_C,9,6!3'_D+_CEF!6'`1+_CFD,_V#7vd$HK;RN!1#2!3'`2#5#7#1!1'_SN#1!3+^N+1!3'_6+58-1RN$~R+10!3'_6+54#52#5!3,_T+5#3#5!2'`0!4'_U+_C6,_V#4#1!2'_P-1RN$~R+10!3'_6+5!1'7#2#42#4!3,_T+5#2#4!4'_U+_C!1'_E#2,_V#3").
Qed.
Lemma live_agree_expr : forall e acc t, live_agree acc t -> live_agree (expr_vars e acc) (expr_vars_t e t).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S>0!1+2+5!1+_B+_C!2'_P#2#1%acc;R0%t;R1%~R2!2'_P!2'_7#4#3!2'`4#4#2!1,H#4!1,^L#4!3#4#3#2#1!3#6!2'_7#5#3!2'`4#5#26!3,^I#8#7#5!3,`6#8#7#5!3,^J#8#7#5!3,`7#8#7#5!4,`8#8#7#6#5!4,`9#7#6#5#4$e;R+E!:'`3$e;R+E3$z;R+3$acc;R0$t;R1$H;R2vd#1!2'_P!2'_74#3!2'`44#2$n;R+5$acc;R0$t;R1$H;R2vd!4'`5#3#2#4#1!2'_P!2'_75#3!2'`45#2$op;R+^?$e1;R+E$IHe1;R3$e2;R+E$IHe2;R3$acc;R0$t;R1$H;R2vd7!2'_P!2'_78#3!2'`48#2$op;R+^?$e1;R+E$IHe1;R3$e2;R+E$IHe2;R3$acc;R0$t;R1$H;R2vd7!2'_P!2'_79#3!2'`49#2$op;R+^@$e1;R+E$IHe1;R3$e2;R+E$IHe2;R3$acc;R0$t;R1$H;R2vd7!2'_P!2'_7:#3!2'`4:#2$op;R+^@$e1;R+E$IHe1;R3$e2;R+E$IHe2;R3$acc;R0$t;R1$H;R2vd7!2'_P!2'_7;#3!2'`4;#2$sx;R+1$lo;R+5$n;R+5$e;R+E$IHe;R3$acc;R0$t;R1$H;R2vd6!2'_P!2'_7<#3!2'`4<#2$sx;R+1$k;R+5$i;R+3$n;R+5$acc;R0$t;R1$H;R2vd#1!2'_P!2'_7=#3!2'`4=#2#1").
Qed.
Lemma live_agree_fold : forall (X : Type) (f : X -> list nat -> list nat) (g : X -> ptree unit -> ptree unit) (l : list X) acc t,
  (forall a acc t, live_agree acc t -> live_agree (f a acc) (g a t)) ->
  live_agree acc t -> live_agree (fold_right f acc l) (fold_right g t l).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S33lcd;g`:bd;lcd;g`;d;<scd;!1+2+5!1+_B+_C!3,_T#;#3#2$X;R{cd;$f;R%~R#1%~R00$g;R%~R#2%~R11$l;R!1+2#3$acc;R0$t;R1$Hfg;R%a;R#6%acc;R0%t;R1%~R!2'_P#2#1!2'_P!2#9#4#3!2#8#4#2$H;R!2'_P#3#2!5'`;#8$l;R!1+2#8!2'_P!5'`:0#9#8#5#1!5'`:1#9#7#4#1#1$a;R#8$r;R!1+2#9$IH;R!2'_P!5'`:0#:#9#6#1!5'`:1#:#8#5#1vd!4#5#3!5'`:0#;#:#7#2!5'`:1#;#9#6#2#1!2'_P!5'`:0#;#:#72!5'`:1#;#9#62#5").
Qed.
Lemma live_vars_agree : forall cs, live_agree (live_vars cs) (live_vars_t cs).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_10!1+2+5!1'W#1!2'_7#1#3!2'_7#22$hp;R+`>$acc;R0-`>RN$hp;R+`>0#22$b;R+E$n;R+E3$b;R+E$n;R+E3!2+_>+E+E!3'`?+E+E#2!3'`@+E+E#2$p;R5$acc;R0!2'_76!2'_77#1!1'`A#2!1'`B#2$m;R+:$acc;R0!2'_79!2'_7:#1!1'_=#3!1'_=#2!2'_7=2!2'_7<!2'_7#2#4$K;R+[$acc;R0-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E!2'_7<!2'_7#1#4$a;R+^3$n;R+E>$a;R+^3$n;R+E$k;R+5?$lo;R+3$hi;R+3#3$e;R+E$m;R+3#3$e;R+E$lo;R+3$hi;R+3#4$a;R+^3$n;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#5$a;R+^3$n;R+E$c;R+3?$a;R+^3$n;R+E>!1,^0+5!1'F!1'G#1!1'^9#1!1'O#1!1'S#1!1'T#1!1'Y#1!1'Z#1!5'`:0+`>4!5'`:0+`>4!5'`:058!5'`:058!5'`:0+:;!5'`:0+[@!5'`:0+E'_7ABCDEFGH!1'F!1'G#4!1'^9#4!1'O#4!1'S#4!1'T#4!1'Y#4!1'Z#4!1+_B+_C!2'`4#1#3!2'`4#2R$hp;R+`>$acc;RQ-`>RN$hp;R+`>Q#22$b;R+E$n;R+ES$b;R+E$n;R+ES$p;R5$acc;RQ!2'`46!2'`47#1$m;R+:$acc;RQ!2'`49!2'`4:#1!2'`4=R!2'`4<!2'`4#2#4$K;R+[$acc;RQ-[RN$K;R+[Q#2:$a;R+^3$w;R+5$v;R+E!2'`4<!2'`4#1#4$a;R+^3$n;R+EW$a;R+^3$n;R+E$k;R+5X$lo;R+3$hi;R+3#3$e;R+E$m;R+3#3$e;R+E$lo;R+3$hi;R+3#4$a;R+^3$n;R+EW$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#5$a;R+^3$n;R+E$c;R+3X$a;R+^3$n;R+EW!1,`C+_C!5'`:Q+`>T!5'`:Q+`>T!5'`:Q5U!5'`:Q5U!5'`:Q+:V!5'`:Q+[Y!5'`:Q+E'`4ZBCDEFGH!1+^;+_C!1'_E#1!2'_PAZ!2'_P#2#1!1'W#5!2'_7#1#8!2'`4#1#7!2'_7#1#:!2'`4#1#9!2'_7#1#6!2'_7#2^8!2'`4#1#5!2'`4#2^:!1'F!1'G#3!5'`:0+E'_7A^<!1'^9#3!5'`:0+[@^=^>!1'O#3!5'`:0+:;^?^@!1'S#3!5'`:058^A^B!1'T#3!5'`:058^C^D!1'Y#3!5'`:0+`>4^E^F!1'Z#3!5'`:Q+E'`4Z^<!5'`:Q+[Y^I^>!5'`:Q+:V^J^@!5'`:Q5U^K^B!5'`:Q5U^L^D!5'`:Q+`>T^M^F!2'_7#1#7!2'`4#1#6!2$b;R+E$n;R+E!4'`<#2^O^P!4'`<#1#7#6#5#2#1$a;R+`>$acc;R0$t;RQ$H;R^2-`>RN$h;R+`>!2'_P-`>RN$hp;R+`>0#12$b;R+E$n;R+E^9$b;R+E$n;R+E^9-`>RN$hp;R+`>Q#12$b;R+E$n;R+E^;$b;R+E$n;R+E^;#42$b;R+E$n;R+E^Q$b;R+E$n;R+E^Q!3'`@+E+E#4$a;R5$acc;R0$t;RQ$~R^2!4'`<!3'`?+E+E#4!2'_7^S#3!2'`4^S#2!4'`<^S#3#2#1!1'`B#4!2'_7=^8!2'_7<!2'_7#2#7!2'`4=^:!2'`4<!2'`4#2#6!1'_=!2,`F#4#3!2$a;R+^3-^3RN$s;R+^3%n;R+E!2'_P!2'_7=^4!2'`4=^5#11$a_base;R+E$a_off;R+3!2$a_base0;R+E$a_off0;R+3$n;R+E!4'`<!1'_=!2,`F#3#2!2'_7#1#;!2'`4#1#:!4'`<#1#;#:#9#2#1#2#1!2'_P!2'_7<!2'_7#2#:!2'`4<!2'`4#2#9!4'`<^Z!2'_7#2#=!2'`4#2#<!4'`<#2#=#<#;$cs;R+Cvd!4'`<!1'V#1-`=RN$x;R+`=013I$k;R+5$l;R+E$o;R+E!2'_7#2!2'_7#1!5'`:0+`>4!5'`:0+`>4!5'`:058!5'`:058!5'`:0+:;!5'`:0+[@!5'`:0+E'_7AJKLMNOPI-`=RN$x;R+`=Q13[$k;R+5$l;R+E$o;R+E!2'`4#2!2'`4#1!5'`:Q+`>T!5'`:Q+`>T!5'`:Q5U!5'`:Q5U!5'`:Q+:V!5'`:Q+[Y!5'`:Q+E'`4ZJKLMNOP[&A0;Rvd$v;R+5vd!6'_W\!1,^2+_C$o;R\!3+^N+1!3'_6+5!1'7#2A-^;RN$x;R!1+^;+_C+1#12$u;R+_C,9,6!2,^H+1,6!3'_D+_CZ^0!2'`D+_C^0!3+^N+1!3'_6+5!1'7#1A!2'`0Z#1^1^1&A5;R$acc;R0$t;RQ$H;R^2&a;R^3+`=-`=RN$a;R+`=!2'_P-`=RN$x;R+`=0#13#5$k;R+5$l;R+E$o;R+E!2'_7#2^4#5-`=RN$x;R+`=Q#13#4$k;R+5$l;R+E$o;R+E!2'`4#2^5#4#13#2$k;R+5$len;R+E$off;R+E!3$k;R+5$len;R+E$off;R+E!4'`<#2^6^7!4'`<#1#:#9#8#3#2#1#2%acc;R0%t;RQ%~R^2!2'_P-`=RN$x;R+`=0^33#3$k;R+5$l;R+E$o;R+E^9#3-`=RN$x;R+`=Q^33#2$k;R+5$l;R+E$o;R+E^;#2!3#1!5'`:0+`>4^G^H!5'`:Q+`>T^N^H!8'`E+`>4T^H^G^N^R!8'`E+`>4T^F^E^M^R!8'`E58U^D^C^L^T!8'`E58U^B^A^K^T!8'`E+:;V^@^?^J$a;R+:$acc;R0$t;RQ$~R^2!4'`<!1'`A#4!2'_7^U#3!2'`4^U#2!4'`<^U#3#2#1!8'`E+[@Y^>^=^I$a;R+[$acc;R0$t;RQ$H;R^2-[RN$k;R+[!2'_P-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E!2'_7<^O$a;R+^3$n;R+E^V$a;R+^3$n;R+E$k;R+5^W$lo;R+3$hi;R+3#6$e;R+E$m;R+3#6$e;R+E$lo;R+3$hi;R+3#7$a;R+^3$n;R+E^V$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#8$a;R+^3$n;R+E$c;R+3^W$a;R+^3$n;R+E^V-[RN$K;R+[Q#1:$a;R+^3$w;R+5$v;R+E!2'`4<^P$a;R+^3$n;R+E^X$a;R+^3$n;R+E$k;R+5^Y$lo;R+3$hi;R+3#5$e;R+E$m;R+3#5$e;R+E$lo;R+3$hi;R+3#6$a;R+^3$n;R+E^X$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#7$a;R+^3$n;R+E$c;R+3^Y$a;R+^3$n;R+E^X#4:$a;R+^3$w;R+5$v;R+E!3$a;R+^3-^3RN$s;R+^3%w;R+5%v;R+E!2'_P!2'_7<^6!2'`4<^7#11$a_base;R+E$a_off;R+3!2$a_base0;R+E$a_off0;R+3$w;R+5$v;R+E!4'`<^Z!2'_7#1#=!2'`4#1#<!4'`<#1#=#<#;#2#1#3#2#1$a;R+^3$n;R+E^[$a;R+^3$n;R+E$k;R+5!3$a;R+^3-^3RN$s;R+^3%n;R+E%k;R+5^\#11$a_base;R+E$a_off;R+3!2$a_base0;R+E$a_off0;R+3$n;R+E$k;R+5_0#2#1#3#2#1$lo;R+3$hi;R+3!2$lo;R+3$hi;R+3#5#2#1$e;R+E$m;R+3!2$e;R+E$m;R+3#5#2#1$e;R+E$lo;R+3$hi;R+3!3$e;R+E$lo;R+3$hi;R+3#7#3#2#1$a;R+^3$n;R+E^[$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!4$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#9#4#3#2#1$a;R+^3$n;R+E$c;R+3!3$a;R+^3-^3RN$s;R+^3%n;R+E%c;R+3^\#11$a_base;R+E$a_off;R+3!2$a_base0;R+E$a_off0;R+3$n;R+E$c;R+3_0#2#1#3#2#1$a;R+^3$n;R+E^[!8'`E+E'_7'`4^<AZ$a;R+E$acc;R0$t;RQ$~R^2!4'`<#4#3#2#1#2!2'_P!1'_?#1!1'_G#1").
Qed.
Lemma forallb_expr_vars : forall P e acc,
  forallb P (expr_vars e acc) = (forallb P (expr_vars e []) && forallb P acc)%bool.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^70!1+2+5!2'_7#2#1!1,^0+5!2'_7#22!3'?+5#4#1!1,H#2!2,^H+1#1!1'7#5!3'?+5#8#5!3'_6+5!1'7#4#3!1#7#5!2'_8#18!1#8#6!3'?+5#;#8!1#9#7!3'?+5#:#7!3'?+5#<#9%~R#1+1!1+2#2%~R!3+^N+1!3'_6#3#2#1,9!2+`H#4$x;R#4!2+`I!3'`J#5#1#3!3+^N+1!1#4#1,9!3'`J+5#2#@%~R!3+^N+1!2'7#2#1,9!3+^N+5#3#2!2'_8:,9!1'`S:!3'?+5#7#4!2'_8!3'?+5#7-1RN$~R+10!3'_6+57222!3,_T+5#52H!1,^L#2%acc;R0!3+^N+1!3'?+5#51!2'_8!3'?+5#53!3'?+5#5#1!3'?+5#7#1%acc;R0!3+^N+1!3'?+5#71!2'_8!3'?+5#73L!3'?+5#8!2'_7#52!2'_7#3#1!3'?+5#8O!2'_7#42!3'?+5#9#2!2'_8!3'?+5#9!2'_7#6QR!2'_7#32!3'?+5#8T!3'?+5#8#1!2'_8UV!3'?+5#9!2'_7#62!2'_8NU!3'?+5#9Q!2'_8YV!1#2#1!6'_W+1!2'_8NP$b;R+1!3+^N+1#1S!6'_W+1W$b;R+1!3+^N+1!2'_8X#1S!6'_W+1Y$b;R+1!3+^N+1!2'_8X!2'_8ZR!2'_8#1R!6'_W+1[$b;R+1!3+^N+1#1!2'_8!2'_8XZR!2,^H+1[!2'_8NW!3'`TNUV!3'?+5#8!2'_7#5T!1#4TP\!3'?+5#8!2'_7#5O!1#4O!3,^I#6#5#3!3,`6#6#5#3!3,^J#6#5#3!3,`7#6#5#3!4,`8#6#5#4#3!4,`9#5#4#3#2$P;R%~R+5+1$e;R+E!:'`3$e;R+E%acc;R0!3+^N+1!3'?+5#41!2'_8!3'?+5#434$z;R+3$acc;R0vd!2,^H+1!2'_8!3'?+5#424!3+^N+1!3'?+5#4!2'_75#1!2'_8!3'?+5#4!2'_7524$n;R+5$acc;R0vd&b;R!3'_6+5!1'7#2#1+1&E;R6!3+^N+1!3'_6+5!1'7#3#2#1!1-1RN$b;R+1%E;R!3+^N+1!3'_6+57#4#1!3+^N+1!3'?+5#8-1RN$~R+10#22#5!3,_T+5#6#5!2'_8!3'?+5#8-1RN$~R+10!3'_6+5!1'7#6222!3,_T+5#628#22$E;R!3+^N+19,9vd!6'_W+1:$b;R+1!3+^N+18;&b;R:+1&Pn;R6!3+^N+1<#1!1-1RN$b;R+1%Pn;R!3+^N+1!1#:#8#1!3+^N+1=!2'_8#2=#22$Pn;R!3+^N+1>,9!2,^H+1!2'_8,9?$Pn;R!3+^N+1>,6vd&b;R?+1&F;R6!3+^N+1=#1!1-1RN$b;R+1%F;R!3+^N+1!3'?+5#=#:#1!3+^N+1#2,6#22$F;R!3+^N+1@,9!2'_\!3+^N+1,9,6&H;R$A;R{g?d;$f;RA$l;RB!5'`GC%~R!2+`H#3$x;R#3!2+`I!3'`J#4#1#2!3+^N+1!1#3#1,9!3+^N+1!3'_6#4#3#2,9%~R!3+^N+1!3'_6#3#2#1,9!2+`H#4$x;R#4!2+`I!3'`J#5#1#3!3+^N+1!1#4#1,9$~RC$~R%~R!2+`H#4$x;R#4!2+`I!3'`J#5#1#3!3+^N+1!1#4#1,9!3+^N+1!3'_6#5#4#3,9#2!3'`K#3#2#1%A;R{g?d;%f;RA%l;RBC&E;R!4#1+5!1'7#<#;#8!2+`H+5$x;R+5!2+`I!3'`J+5#1#<!3+^N+1!2'7#=#1,9!5'`L+5$x;R+5!2+`I!3'`J+5#1#=!3+^N+1!2'7#>#1,9+`M$x;R+5$~R!1$x;R+5!2+`I!3'`J+5#1#>!3+^N+1!2'7#?#1,9#1!2$x;R+5$H;R!2+`I!3'`J+5#1#?!3+^N+1!2'7#@#1,9!5'`GD!3+^N+1!2'7#A#2,9+`M$~RD$~R!3+^N+1!2'7#B#3,9!2$Hx;R!3'`J+5#4#B$Ex;R!3+^N+1!2'7#D#5,9&H;R$n;R+5$m;R+5!5'`GE%~R!3+^N+5#2#1!3+^N+1!2'7#3#2,9%~R!3+^N+1!2'7#2#1,9!3+^N+5#3#2$~RE$~R%~R!3+^N+5#3#2!3+^N+1!2'7#4#3,9#2!2'`N#2#1%n;R+5%m;R+5E&Ex;R!3#1#F#7#2!3+^N+5#F#7!7'_M+5#G$x;R+5%Hx;R!3'`J+5#1#G+`M$Hx;R!3'`J+5#G#F&C;R!6'`O%~R!3+^N+1!3'?+5#J#G,9%x;R+5%~R!3'`J+5#1#I!3+^N+1!1#M#2,9%~R%x;R+5%~R!3'`J+5#1#H!3+^N+1!1#L#2,9!3+^N+1!3'?+5#K#H,9!3'`P+5#J#G#>#H#1!3+^N+1!1#J#H,9&C;R!6'_M+1!1#K#I$b;R+1!3+^N+1#1,9#1,6#B!3+^N+1,6,9&H;R!6'_M+1,6$e;R+1-1RN$b;R+1w#12+`M+`Q,`R,9#1+`M!2'_\+`M#1#8#1#4#2#1#1#2#1#1$F;R!3+^N+1@,6!2,^H+1,6#1!3+^N+1?!2'_8,6?#1FG!3+^N+1HI$E;R!3+^N+19,6vd!6'_W+1:$b;R+1!3+^N+1!2'_8<8;!2,^H+1!2'_8:HFG!3+^N+1!3'?+5#7!3,_T+5#5#4I#1!3+^N+1!3'?+5#4!2'_7J#1!2'_8!3'?+5#4!2'_7J24$op;R+^?$e1;R+E$IHe1;RK$e2;R+E$IHe2;RM$acc;R0vd^0!3+^N+1!3'?+5#8!2'_7^1#1!2'_8!3'?+5#8!2'_7^12V$op;R+^?$e1;R+E$IHe1;RK$e2;R+E$IHe2;RM$acc;R0vd^0!3+^N+1!3'?+5#8!2'_7^2#1!2'_8!3'?+5#8!2'_7^22V$op;R+^@$e1;R+E$IHe1;RK$e2;R+E$IHe2;RM$acc;R0vd^0!3+^N+1!3'?+5#8!2'_7^3#1!2'_8!3'?+5#8!2'_7^32V$op;R+^@$e1;R+E$IHe1;RK$e2;R+E$IHe2;RM$acc;R0vd^0!3+^N+1!3'?+5#8!2'_7^4#1!2'_8!3'?+5#8!2'_7^42V$sx;R+1$lo;R+5$n;R+5$e;R+E$IHe;RM$acc;R0vd\!3+^N+1!3'?+5#8!2'_7^5#1!2'_8!3'?+5#8!2'_7^52V$sx;R+1$k;R+5$i;R+3$n;R+5$acc;R0vd!2,^H+1!2'_8!3'?+5#72L!3+^N+1!3'?+5#7!2'_7^6#1!2'_8!3'?+5#7!2'_7^62L#1").
Qed.
Lemma expr_all_live_t_eq : forall acc t e, live_agree acc t -> expr_all_live_t t e = all_live acc e.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SW0!2'_5#1/nx0;!1'7#1$v;R+5!2'_40!3'_6+51#6!1,^0+5!2'_7#13!2,^H+1,9!1,H#1!3'_6+51#5!2'_5#2/nx0;!3'_6+5!1'7#2#6!2'_4-5RN$m;R+5+1/nx0;2,6$m';R+5!2'`U#2#17-5RN$m;R+5+1/nx0;2,6$m';R+5!2'`U#3#1-5RN$m;R+5+1/nx0;2,6$m';R+5!2'`U#4#1!3'_6+5!1'7#3#7!2,^H+1!2'_4;9!1,^L#1!3+^N+1!2'_F#5#1!3'?+5$v;R+5!2'_40!3'_6+51#74$v;R+5!2'_40!3'_6+51#9!3+^N+1!2'_F#7#1!3'?+5A4$v;R+5!2'_40!3'_6+51#:!2'_7#43!3'?+5CD!2'_7#23!3'?+5CF!2'_F#9#5!2'_F#9#3$v;R+5!2'_40!3'_6+51#;!2'_7#53!3'?+5JK!2'_8L!3'?+5J!2'_7#33!3'?+5$v;R+5!2'_40!3'_6+51#=K!3'?+5$v;R+5!2'_40!3'_6+51#<D!6'_W+1!2'_8EG$b;R+1!3+^N+1-1RN$~R+1+1H2I,6#1!6'_W+1E$b;R+1!3+^N+1-1RN$~R+1+1#12I,6M!6'_W+1G$b;R+1!3+^N+1-1RN$~R+1+1L2#1,6M&b;RE+1!1-1RN$b;R+1%IHe1;R!3+^N+1!2'_F#:#6#1!3+^N+1-1RN$~R+1+1#22N,6!2'_8#2N#12$IHe1;R!3+^N+1H,9!2,^H+1!2'_8,9O$IHe1;R!3+^N+1H,6!2,^H+1!2'_8,6O#4!2'_F#8#2#1!2'_F#8#4#3!3'?+5C!2'_7#4F!3'`VC#4F!3,^I#5#4#2!3,`6#5#4#2!3,^J#5#4#2!3,`7#5#4#2!4,`8#5#4#3#2!4,`9#4#3#2#1$acc;R!1+2+5$t;R!1+_B+_C$e;R+E$H;R!2'_P#3#2vd!:'`3$e;R+E!3+^N+1!2'_F#4#1!3'?+524$z;R+3vd5!3+^N+1!2'_F#46!3'?+52!2'_763$n;R+5vd!6'_M+17$b;R+1!3+^N+1-1RN$~R+1+182,9#1!2'_8!2'_489,9vd!6'_W+1:$b;R+1!3+^N+1-1RN$~R+1+1;2,99#1&b;R0+1-1RN$b;R+1!3+^N+1-1RN$~R+1+1<2,9=!2'_4<=#12>>!2'_8:,9!1'`S:!3+^N+1-1RN$~R+1+102,97!2'_8!2'_407,9!2'`0#4#1!1#2#1!3+^N+1!2'_F#4?!3'?+52!2'_7?3$op;R+^?$e1;R+E$IHe1;R@$e2;R+E$IHe2;RBvdP!3+^N+1!2'_F#8Q!3'?+5C!2'_7Q3$op;R+^?$e1;R+E$IHe1;R@$e2;R+E$IHe2;RBvdP!3+^N+1!2'_F#8R!3'?+5C!2'_7R3$op;R+^@$e1;R+E$IHe1;R@$e2;R+E$IHe2;RBvdP!3+^N+1!2'_F#8S!3'?+5C!2'_7S3$op;R+^@$e1;R+E$IHe1;R@$e2;R+E$IHe2;RBvdP!3+^N+1!2'_F#8T!3'?+5C!2'_7T3$sx;R+1$lo;R+5$n;R+5$e;R+E$IHe;RBvd#1!3+^N+1!2'_F#8U!3'?+5C!2'_7U3$sx;R+1$k;R+5$i;R+3$n;R+5vd5!3+^N+1!2'_F#7V!3'?+5A!2'_7V3#2!3+^N+1!2'_F#3#2!2'_<#4#2").
Qed.
Lemma cs_gc_eq : forall cs, cs_gc cs = cs_gc_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^;0!1'^9#5!1+2+[!1'^7#6!3'_H#2#1!1'_G#6!1'^9#6!3'_A#2#1!1'_?#6!1'_G#?!3,`Z#3#2#1!1'_?#?!1'_G#B!2,`F#4#3!3,`Z:#2#1!1'_?#B!1'_G#=!2,`[#2#1!1'_?#=!2,^H+1-ERN$n0;R+E+1#18$n;R+3!1'@!2'_8!2'_9#4#=!2'_:!2'^U#3#1#<$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k0;R+5$i;R+3$n;R+5,9!1'_G#@!2,`F#3#2!2,`[B#1!1'_?#@!3,`\#3#2#1!1'@!2'_8!2'_9#5#?!2'_:!2'^U#4#1#>!3,`\:#2#1!2,^H+1,9!1'_G#<!2,a0#2#1!1'_?#<!2'_<K#2!2,a2#2#1!1'_?#>!2'_<N#3!1'_G#>!3,a3#3#2#1!2,a4#2#1!2,a4B#1!1'_=#4!2'_<DT!1'_G#A!1'_=#3!2'_FVW!2'_FV#2!1'_?#A!2'_<Z!1'_=#5!2'_8[!2'_<Z#4!2'_8\!2'_<ZW!2'_8^0!2'_<Z#2!2'_<D#3!1'_=#2!2'_<D^3!2'_<D#1!4,a5#4#3#2#1!3,a6#3#2#1!3,a6:#2#1!2,a7#2#1!2,a7B#1$cs;R+Cvd&p;R!1'_2!2'^B#1}2!2+_>+E+3-_>RN$p;R!2+_>+E+3!3+^N+C-_>RN$x;R!2+_>+E+3+C#11$spb;R+E$spk;R+3!2'^7#5!3'_@+[!3'_H#2#1!1'_G#50-_>RN$x;R!2+_>+E+3+C#11$spb;R+E$spk;R+3!2'^7#5!3'_@+[!3'_A#2#1!1'_?#50#11$e;R+E$z;R+3!2$spb;R+E$spk;R+3!8'`W1+C22!3'_@+[34!3'_@+[54!2,^H%~R1+C2!5'`X+[35$K;R+[&H;R!1'`Y#7!2'_P!1'_?#7!1'_G#7-[RN$k;R+[!3+^N+1!4'_H#5#4!1'_G#9#1!4'_A#5#4!1'_?#9#1#2:$a;R+^3$w;R+5$v;R+E!3$a;R+^3-^3RN$s;R+^3%w;R+5%v;R+E!3+^N+1!4'_H#;#:67!4'_A#;#:87#11$a_base;R+E$a_off;R+3!2$b;R+E$kk;R+3$w;R+5$v;R+Evd!2,^H+1!1'@!2'_8!2'_9#4#>!2'_:!2'^U#3!1'_;#2#=!3+^N+1!4'_H#>#=9;!4'_A#>#=<;#2#1#3#2#1$a;R+^3$n;R+E!2$a;R+^3-^3RN$s;R+^3%n;R+E!3+^N+1!4'_H#9#8=>!4'_A#9#8?>#11$a_base;R+E$a_off;R+3!2$b;R+E$kk;R+3$l;R+Evd@!3+^N+1!4'_H#<#;AC!4'_A#<#;DC#2#1#2#1$a;R+^3$n;R+E$k;R+5!3$a;R+^3-^3RN$s;R+^3%n;R+E%k;R+5!3+^N+1!4'_H#;#:6E!4'_A#;#:8E#11$a_base;R+E$a_off;R+3!2$b;R+E$kk;R+3$l;R+E$bk;R+5vd!2,^H+1-ERN$n0;R+E+1#28$n;R+3F$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k1;R+5$i;R+3$n;R+5,9!3+^N+1!4'_H#>#=9G!4'_A#>#=<G#2#1#3#2#1$lo;R+3$hi;R+3!2$lo;R+3$hi;R+3vdH!3+^N+1!4'_H#8#7IJ!4'_A#8#7KJ#2#1$e;R+E$m;R+3!2$e;R+E$m;R+3vd!6'_W+1L$b;R+1!3+^N+1#1!2'_<?#3!2,^H+1L!2'_FI#2!4'a1KI#2#5!3+^N+1!4'_H#8#7IM!4'_A#8#7KM#2#1$e;R+E$lo;R+3$hi;R+3!3$e;R+E$lo;R+3$hi;R+3vd!6'_W+1O$b;R+1!3+^N+1#1!2'_<8#4!2,^H+1O!2'_FP#3!4'a1NP#3#7!3+^N+1!4'_H#:#9PQ!4'_A#:#9NQ#3#2#1$a;R+^3$n;R+E!2$a;R+^3-^3RN$s;R+^3%n;R+E!3+^N+1!4'_H#9#8=R!4'_A#9#8?R#11$a_base;R+E$a_off;R+3!2$b;R+E$kk;R+3$n;R+EvdH!3+^N+1!4'_H#<#;AS!4'_A#<#;DS#2#1#2#1$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!4$a1;R+^3$n1;R+E$a2;R+^3$n2;R+Evd!6'_W+1U$b;R+1!3+^N+1!2'_8!2'_8!2'_8#1!2'_FV#4XY^1!6'_W+1^2$b;R+1!3+^N+1!2'_8!2'_8!2'_8[#1XY^1!6'_W+1^4$b;R+1!3+^N+1!2'_8!2'_8\#1Y^1!6'_W+1^5$b;R+1!3+^N+1!2'_8^0#1^1!2,^H+1!2'_8!2'_8!2'_8U^2^4^5!2'_FA#1!4'a1DA#1#9!2'_FA^3!4'a1DA^3#9!2'_FA#3!4'a1DA#3#9!2'_FAT!4'a1DAT#9!3+^N+1!4'_H#<#;A^6!4'_A#<#;D^6#4#3#2#1$a;R+^3$n;R+E$c;R+3!3$a;R+^3-^3RN$s;R+^3%n;R+E%c;R+3!3+^N+1!4'_H#;#:6^7!4'_A#;#:8^7#11$a_base;R+E$a_off;R+3!2$b;R+E$kk;R+3$l;R+E$c;R+3vd!2,^H+1-ERN$n0;R+E+1#28$n;R+3F$n;R+5,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^?$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$op;R+^@$a0;R+E$b0;R+E,9$sx;R+1$lo;R+5$n;R+5$e;R+E,9$sx;R+1$k0;R+5$i;R+3$n;R+5,9!3+^N+1!4'_H#>#=9^8!4'_A#>#=<^8#2#1#3#2#1$a;R+^3$n;R+E!2$a;R+^3-^3RN$s;R+^3%n;R+E!3+^N+1!4'_H#9#8=^9!4'_A#9#8?^9#11$a_base;R+E$a_off;R+3!2$b;R+E$kk;R+3$l;R+Evd@!3+^N+1!4'_H#<#;A^:!4'_A#<#;D^:#2#1#2#14#2#1!3+^N+C!1'a8#1!1'a9#1").
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
Definition saddr_vars_lt (b : nat) (a : saddr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$b;R+5$a;R+^3!2'a:#2!1'_=#1").

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : nat) (s : shape) : bool :=
  match s with
  | SNil | SExit _ | SHole _ | SNext => true
  | SEmitP _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.
Definition kentry_vars_lt (b : nat) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2'a;#5#3!2'_8!2'a;#4#2!2'a:#4#1!2'_80!2'a:#5#2$b;R+5$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E!2'_80!2'a:#5#1$a;R+^3$n;R+E1$a;R+^3$n;R+E$k;R+52$lo;R+3$hi;R+3,9$e;R+E$m;R+3!2'a:#4#2$e;R+E$lo;R+3$hi;R+3!2'a:#5#3$a;R+^3$n;R+E1$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!2'_8!2'_8!2'_8!2'a;#6#4!2'a:#6#3!2'a;#6#2!2'a:#6#1$a;R+^3$n;R+E$c;R+32$a;R+^3$n;R+E1").
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Fixpoint kn_vars_lt (b : nat) (k : list kentry) : bool :=
  match k with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition pairs_vars_lt (b : nat) (l : list (expr * expr)) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!2+_>+E+E$b;R+5$l;R!1+20!3'?0$p;R0!2'_8!2'a:#3!3'`?+E+E#1!2'a:#3!3'`@+E+E#1#1").
Definition maps_vars_lt (b : nat) (ms : list amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$b;R+5$ms;R!1+2+:!3'?+:$m;R+:!2'_8!2'a:#3!1'`A#1!2'a:#3!1'`B#1#1").
Definition hop_b (h : hop) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$h;R+`>-`>RN$h;R+`>+E#12$b;R+E$n;R+E#2$b;R+E$n;R+E#2").
Definition hop_n (h : hop) : expr := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$h;R+`>-`>RN$h;R+`>+E#12$b;R+E$n;R+E#1$b;R+E$n;R+E#1").
Definition hist_vars_lt (b : nat) (hs : list hop) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$b;R+5$hs;R!1+2+`>!3'?+`>$h;R+`>!2'_8!2'a:#3!1'a<#1!2'a:#3!1'a=#1#1").
Definition fd_vars_lt (b : nat) (f : afd) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$b;R+5$f;R+`=-`=RN$f;R+`=+1#13,9$k;R+5$l;R+E$o;R+E!2'_8!2'a:#5#2!2'a:#5#1,9").
(* [comment removed for export] *)
Definition fresh_ok (cs : acs) : bool :=
  let v := nxt cs in
  sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
  && maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && Nat.leb nx0 v
  && hist_vars_lt v (a_hna cs) && hist_vars_lt v (a_hlz cs).

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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "U^B0!1+^;+C!1+2+[!1+2+a@!2+_>12!1+2+1!1'G#3!1'J5!1'aC6!1'aB7!1,^0+^1!1,^2+^3!6,\!1'K5!1'F596!1'L5:!9'aE/segs;8!1'aF6/IT;#6#5,9#4;!1,^0+1!1'G#7!1'J>!6,\!1'K>!1'F>9?!1'L>:!9'aE/segs;!1'aB!1'aC?!1'aF?/IT;#:#9,9#8@!1,^2+C!7'aH/segs;/IT;#6#5,9#4;!1'aDC!1'JC!7'aH/segs;/IT;#:#9,9#8@-_>RN$p;R!2+_>120#21$kn';R1$l0;R2-2RN$l0;R!1+2+a@0#12!2,^<+C!2'^4#7!4'^5!1'KF!1'FF#2!1'LF$s;R+a@$l1;R!1+2+a@B-_>RN$x;R!2+_>340!3'aGDE=1$p;R3$l;R4G!1'G#2!1'JI!6,\!1'KI!1'FI9J!1'LI:!7'aH/segs;/IT;#5#4,9#3K!1'JL!4'aA8DE=!1'aCE!1'aBO!4'aAPDE=!2+_>34!1'G#8!7'aH/segs;/IT;#;#:,9#9!6,\!1'KS!1'FS9!1'JS!1'LS:!1+2+^1%hints;R4R%kn;R1V%log;RUW%bc;R+aKX!1+^N+aK!1+^N1!1+^NR!4'aL4R!1+^N4\!4'aL1V[^0!4'aLUW!1+^NU^1!4'aL+aKXZ^2%fk;R1+aK!4'aL1+aK[Z%kn;R11!4'aL11[[!1'aDL!3'aG^8M=!1'G#6!1'J^:!6,\!1'K^:!1'F^:9^;!1'L^::!7'aH/segs;/IT;#9#8,9#7^<-_>RN$x;R!2+_>340^91$p;R3$l;R4-_>RN$p;R!2+_>120#21$kn';R1$l0;R2-2RN$l0;R!1+2+a@0#12!2,^<+C!2'^4#6!4'^5!1'K^=!1'F^=#2!1'L^=$s;R+a@$l1;R!1+2+a@B!1'aB!1'aCJ!9'aE/segs;^?!1'aFJ/IT;#5#4,9#3K!9'aE/segs;!1'aB!1'aC^;!1'aF^;/IT;#9#8,9#7^<$K;R+5$fuel;R+5$stops;R!1+2+3$cs;R+Cvd&b;R!1'a?#1+1-1RN$b;R+1!3+^N0-1RN$~R+10#12-_>RN$x;R!2+_>340!4'aA8!1'aD<!1'J<=1$p;R3$l;R4-_>RN$p;R!2+_>120#21$kn';R1$l0;R2-2RN$l0;R!1+2+a@0#12!2,^<+C!2'^4#7!4'^5!1'KA!1'FA#2!1'LA$s;R+a@$l1;R!1+2+a@BB-1RN$~R+10#12HB#12vd!6'_W+ML$s;R+M!3+^N0-_>RN$x;R!2+_>340!4'aA8!1'aD#1!1'J#1=1$p;R3$l;R4-_>RN$p;R!2+_>120#21$kn';R1$l0;R2-2RN$l0;R!1+2+a@0#12!2,^<+C!2'^4#7!4'^5!1'K#5!1'F#5#2!1'L#5$s;R+a@$l1;R!1+2+a@BH!2$lemma;R!3+^N1M!1'JK!9'a>0!1+^N0!1'aI0-_>RN$x;R!2+_>340N1$p;R3$l;R4G-_>RN$x;R!2+_>340Q1$p;R3$l;R4G!6'_JR0$~RR-_>RN$x;R!2+_>340#11$p;R3$l;R4-_>RN$p;R!2+_>120#21$kn';R1$l0;R2-2RN$l0;R!1+2+a@0#12!2,^<+C!2'^4#8!4'^5!1'KT!1'FT#2!1'LT$s;R+a@$l1;R!1+2+a@BNQ!@'aJY^3!3'aMY^3!4'aN+aKX^2!4'aNUW^1!4'aN1V^0!4'aN4R\!1'aOR'aA8P!7'aJ^4^5!3'aM^4^5!4'aN1+aKZ!1'aO+aK'aB7O!7'aJ^6^7!3'aM^6^7!4'aN11[!1'aO1'aC6E!6'aP1[!1'aQ1E6#1DD!2'aRUDEE!2'aR1E==!2'aR4=HH!2'aR0H!7'aS/segs;/IT;#5#4,9#3K!6'_WR^9$p;RR!3+^N0-_>RN$x;R!2+_>340#11$p;R3$l;R4GH!2,^H0^>!4'aA!1'aB!1'aCM^8M=!3'aT^8M=^@!9'aU/segs;J/IT;#5#4,9#3K!2,^H1J!3+^N0-_>RN$x;R!2+_>340!4'aA^?!1'aD^@!1'J^@=1$p;R3$l;R4-_>RN$p;R!2+_>120#21$kn';R1$l0;R2-2RN$l0;R!1+2+a@0#12!2,^<+C!2'^4#6!4'^5!1'K^A!1'F^A#2!1'L^A$s;R+a@$l1;R!1+2+a@B^>!2,^H0B!3+^N0!4'aV#4#3#2#1!4'aW#4#3#2#1").
Qed.

Definition run_block_gc (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$K;R+5$fuel;R+5$stops;R!1+2+3$cs;R+C-^;RN$x;R!1+^;+C!1+^;+C!4'aV#4#3#2#12$cs';R+C!2,^<+C!1'a8#1!1,^2+C").

Definition kentry_eqb (x y : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S50!2'aX#6#3!2'_8!2'aX#4#2!2'_9#3#1!2'_80!2'_9#5#2!2'aY#3#1!2'aY#4#1$x;R+[$y;R+[-[RN$x;R+[+1#2:$a;R+^3$w;R+5$v;R+E-[RN$y;R+[+1#4:$a';R+^3$w';R+5$v';R+E!2'_8!2'_80!2'7#5#2!2'_9#4#1$a0;R+^3$n;R+E,6$a0;R+^3$n;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n;R+E$c;R+3,6$a0;R+^3$n;R+E,6$a;R+^3$n;R+E-[RN$y;R+[+1#3:$a0;R+^3$w;R+5$v;R+E,6$a';R+^3$n';R+E1$a0;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n0;R+E$c;R+3,6$a0;R+^3$n0;R+E,6$a;R+^3$n;R+E$k;R+5-[RN$y;R+[+1#4:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n0;R+E,6$a';R+^3$n';R+E$k';R+5!2'_82!2'7#4#1$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n0;R+E$c;R+3,6$a0;R+^3$n0;R+E,6$lo;R+3$hi;R+3-[RN$y;R+[+1#3:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n;R+E,6$a;R+^3$n;R+E$k;R+5,6$lo';R+3$hi';R+3!2'_8!2'aY#4#23$e;R+E$m;R+3,6$e;R+E$lo0;R+3$hi0;R+3,6$a;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a;R+^3$n;R+E$c;R+3,6$a;R+^3$n;R+E,6$e;R+E$m;R+3-[RN$y;R+[+1#3:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n;R+E,6$a;R+^3$n;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e';R+E$m';R+3!2'_8!2'_9#4#23$e0;R+E$lo;R+3$hi;R+3,6$a;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a;R+^3$n;R+E$c;R+3,6$a;R+^3$n;R+E,6$e;R+E$lo;R+3$hi;R+3-[RN$y;R+[+1#4:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n;R+E,6$a;R+^3$n;R+E$k;R+5,6$lo0;R+3$hi0;R+3,6$e0;R+E$m;R+3,6$e';R+E$lo';R+3$hi';R+3!2'_8!2'_8!2'_9#6#3!2'aY#5#24$a;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a;R+^3$n;R+E$c;R+3,6$a;R+^3$n;R+E,6$a;R+^3$n;R+E-[RN$y;R+[+1#3:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n0;R+E,6$a0;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a';R+^3$n';R+E1$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n0;R+E$c;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E-[RN$y;R+[+1#5:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n;R+E,6$a;R+^3$n;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a;R+^3$n;R+E,6$a1';R+^3$n1';R+E$a2';R+^3$n2';R+E!2'_8!2'_8!2'_8!2'aX#8#4!2'_9#7#3!2'aX#6#2!2'_9#5#1$a;R+^3$n;R+E$c;R+3,6$a;R+^3$n;R+E,6$a;R+^3$n;R+E$c;R+3-[RN$y;R+[+1#4:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n0;R+E,6$a0;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a';R+^3$n';R+E$c';R+3!2'_824$a0;R+^3$n0;R+E,6$a;R+^3$n;R+E-[RN$y;R+[+1#3:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n0;R+E,6$a0;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n0;R+E$c;R+3,6$a';R+^3$n';R+E1").

Definition amap_eqb (x y : amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$x;R+:$y;R+:!2'_8!2'_8!2'_9!1'`A#2!1'`A#1!2'_9!1'`B#2!1'`B#1!2';!1'<#2!1'<#1").

Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (x y : list T) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => eqb a b && list_eqb eqb x' y'
  | _, _ => false
  end.

Definition pair_eqb (x y : expr * expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!2+_>+E+E$x;R0$y;R0!2'_8!2'_9!3'`?+E+E#2!3'`?+E+E#1!2'_9!3'`@+E+E#2!3'`@+E+E#1").
Definition hop_eqb (x y : hop) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!2'_8!2'_9#4#2!2'_9#3#1$x;R+`>$y;R+`>-`>RN$x;R+`>+1#22$b;R+E$n;R+E-`>RN$y;R+`>+1#32$b';R+E$n';R+E0$b0;R+E$n0;R+E,6$b;R+E$n;R+E-`>RN$y;R+`>+1#32$b0;R+E$n0;R+E,6$b';R+E$n';R+E0").

Definition afd_eqb (x y : afd) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$x;R+`=$y;R+`=-`=RN$x;R+`=+1#23-`=RN$y;R+`=+1#13,9$k;R+5$len;R+E$off;R+E,6,6$k;R+5$l;R+E$o;R+E-`=RN$y;R+`=+1#43,6$k';R+5$l';R+E$o';R+E!2'_8!2'_8!2'7#6#3!2'_9#5#2!2'_9#4#1,6-`=RN$y;R+`=+1#13,6$k;R+5$len;R+E$off;R+E,6,9").

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

Definition kentry_apart_bB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S30-^3RN$a;R+^3+1#21$b;R+E$k;R+3!7'aZ#9#8#7#6#2#1#3-^3RN$a;R+^3+1#31$b;R+E$k;R+3!7'aZ#:#9#8#7#2#1#4!2'a\#1#2$bc;R+aK$ub;R+E$uk;R+3$un;R+E$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!2'_8!2'`U#4}8!7'aZ#:#9#8#7#2#1!1,H!1'_;#4$a;R+^3$l;R+E0$a;R+^3$l;R+E$k0;R+51$lo;R+3$hi;R+3!2'_8!2'_8!2'_8!2'_:,I#2!2'_:#2#1!2'a[2'^>!7'aZ#7#6#5#4!1,H,I#2!1,H2$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E0$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+31$a;R+^3$l;R+E0").

Lemma kentry_apart_bB_eqf : forall fk, kentry_apart_bB (mkbc fk) = kentry_apart_b fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S@0%K;R+[+1%un;R+E0%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1!2'`U#4}8!1,H!1'_;#4-^3RN$a;R+^3+1#21$b;R+E$k;R+3!6#5#9#8#7#2#1#3-^3RN$a;R+^3+1#31$b;R+E$k;R+3!6#6#:#9#8#2#1#4!2'a\#1#2!2'_8!2'_8!2'_:,I#2!2'_:#2#1!2'a[7'^>!1,H,I!1,H7-^3RN$a;R+^3+1#21$b;R+E$k;R+3!7'b3#:#9#8#7#2#1#3-^3RN$a;R+^3+1#31$b;R+E$k;R+3!7'b3#;#:#9#8#2#1#4-^3RN$a;R+^3+1#21$b;R+E$k;R+3!7'b3#9#8#7#6#2#1#3-^3RN$a;R+^3+1#31$b;R+E$k;R+3!7'b3#:#9#8#7#2#1#4!1'aB#5$fk;R!1+2+[!5'b0+E%uk;R+31!1'b1!1'aB#1!1'b2#1$x;R+E!5'b0+31!2'b1!1'aB#2#1!2'b2#2#1$x0;R+3!5'b0+E0!3'b1!1'aB#3#2#1!3'b2#3#2#1$x1;R+E!5'b0+[+1!4'b1!1'aB#4#3#2#1!4'b2#4#3#2#1$x2;R+[vd!6'_W2!1'b3#5$b;R2!3+^N+1-[RN$K;R+[+1#2:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!2'_83!6#6#:#9#8#2#14$a;R+^3$l;R+E5$a;R+^3$l;R+E$k0;R+56$lo;R+3$hi;R+3!2'_88!6#3#7#6#59#2:$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+36$a;R+^3$l;R+E5-[RN$K;R+[+1#2:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!2'_83!7'b3#;#:#9#8#2#14$a;R+^3$l;R+E;$a;R+^3$l;R+E$k0;R+5<$lo;R+3$hi;R+3!2'_88!7'b3#8#7#6#59#2:$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E;$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+3<$a;R+^3$l;R+E;!2,^H+1-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!2'_83!7'b3#:#9#8#7#2#14$a;R+^3$l;R+E=$a;R+^3$l;R+E$k0;R+5>$lo;R+3$hi;R+3!2'_88!7'b3#7#6#5#49#2:$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+3>$a;R+^3$l;R+E=!1'aZ?!1'b4#5!3+^N+1!5'b1?#4#3#2#1!5'b2#5#4#3#2#1").
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

Definition kentry_apart_bpB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S30-^3RN$a;R+^3+1#21$b;R+E$k;R+3!8'b6#:#9#8#7#6#2#1#3-^3RN$a;R+^3+1#31$b;R+E$k;R+3!8'b6#;#:#9#8#7#2#1#4!2'a\#1#2$bc;R+aK$sp;R+b5$ub;R+E$uk;R+3$un;R+E$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!2'_8!2'`U#4}8!8'b6#;#:#9#8#7#2#1!1,H!1'_;#4$a;R+^3$l;R+E0$a;R+^3$l;R+E$k0;R+51$lo;R+3$hi;R+3!2'_8!2'_8!2'_8!2'_:,I#2!2'_:#2#1!2'a[2'^>!8'b6#8#7#6#5#4!1,H,I#2!1,H2$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E0$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+31$a;R+^3$l;R+E0").

Lemma kentry_apart_bpB_eqf : forall fk, kentry_apart_bpB (mkbc fk) = kentry_apart_bp fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SA0%K;R+[+1%un;R+E0%uk;R+31%sp;R+b5%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1!2'`U#4}8!1,H!1'_;#4-^3RN$a;R+^3+1#21$b;R+E$k;R+3!7#5#:#9#8#7#2#1#3-^3RN$a;R+^3+1#31$b;R+E$k;R+3!7#6#;#:#9#8#2#1#4!2'a\#1#2!2'_8!2'_8!2'_:,I#2!2'_:#2#1!2'a[8'^>!1,H,I!1,H8-^3RN$a;R+^3+1#21$b;R+E$k;R+3!8'b9#;#:#9#8#7#2#1#3-^3RN$a;R+^3+1#31$b;R+E$k;R+3!8'b9#<#;#:#9#8#2#1#4-^3RN$a;R+^3+1#21$b;R+E$k;R+3!8'b9#:#9#8#7#6#2#1#3-^3RN$a;R+^3+1#31$b;R+E$k;R+3!8'b9#;#:#9#8#7#2#1#4!1'aB#6$fk;R!1+2+[!5'b0+b5%ub;R+E2!1'b7!1'aB#1!1'b8#1$x;R+b5!5'b0+E2!2'b7!1'aB#2#1!2'b8#2#1$x0;R+E!5'b0+31!3'b7!1'aB#3#2#1!3'b8#3#2#1$x1;R+3!5'b0+E0!4'b7!1'aB#4#3#2#1!4'b8#4#3#2#1$x2;R+E!5'b0+[+1!5'b7!1'aB#5#4#3#2#1!5'b8#5#4#3#2#1$x3;R+[vd!6'_W3!1'b9#6$b;R3!3+^N+1-[RN$K;R+[+1#2:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!2'_84!7#6#;#:#9#8#2#15$a;R+^3$l;R+E6$a;R+^3$l;R+E$k0;R+57$lo;R+3$hi;R+3!2'_89!7#3#8#7#6#5:#2;$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+37$a;R+^3$l;R+E6-[RN$K;R+[+1#2:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!2'_84!8'b9#<#;#:#9#8#2#15$a;R+^3$l;R+E<$a;R+^3$l;R+E$k0;R+5=$lo;R+3$hi;R+3!2'_89!8'b9#9#8#7#6#5:#2;$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E<$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+3=$a;R+^3$l;R+E<!2,^H+1-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$k;R+3!2'_84!8'b9#;#:#9#8#7#2#15$a;R+^3$l;R+E>$a;R+^3$l;R+E$k0;R+5?$lo;R+3$hi;R+3!2'_89!8'b9#8#7#6#5#4:#2;$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+3?$a;R+^3$l;R+E>!1'b6@!1'b:#6!3+^N+1!6'b7@#5#4#3#2#1!6'b8#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.



Definition kimg_b (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n;R+E,6$a;R+^3$n;R+E$k;R+5,6$lo;R+3$hi;R+3,9$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a;R+^3$n;R+E$c;R+3,6$a;R+^3$n;R+E,6").

(* [comment removed for export] *)
Definition kn_unfill (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => kimg_b K || kentry_apart_bp k sp ub uk un K) k.

Definition kn_unfillB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$bc;R+aK$ub;R+E$uk;R+3$un;R+E&sp;R!4'b;#4#3#2#1+b5!3'_@+[$K;R+[!2'_4!1'b<#1!6'b7#6#2#5#4#3#1!1'b=#5").

Lemma kn_unfillB_eqf : forall fk, kn_unfillB (mkbc fk) = kn_unfill fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+2+[%un;R+E0%sp;R+b5%ub;R+E%uk;R+3%un;R+E%K;R+[+1!1'b<#1!1'b=!1'aB#5$K;R+[!2'_43!6'b8#6!4'b@#6#5#4#3#5#4#3#1!3'_@+[5#5%b1;R+E%k1;R+3%n1;R+E+b5!1'aB#4$fk;R0!5'b0+E%uk;R+31!1'b>!1'aB#1!1'b?#1$x;R+E!5'b0+31!2'b>!1'aB#2#1!2'b?#2#1$x0;R+3!5'b0+E0!3'b>!1'aB#3#2#1!3'b?#3#2#1$x1;R+Evd!6'_W2!1'b8#4$b;R2!3+^N0!3'_@+[$K;R+[!2'_43!5#2!4'b;!1'aB#6#5#4#3#5#4#3#146!6'_W7!1'b@#4$s;R7!3+^N0!3'_@+[$K;R+[!2'_43!6'b8#6!3#2#5#4#3#5#4#3#146!6'_W0#4$l;R0!3+^N0!3'_@+[5#16!2,^H0!3'_@+[$K;R+[!2'_43!6'b8#5!4'b@#5#4#3#2#4#3#2#1#4!1'b=8!1'bA#4!1'b;8!1'bB#4!1'b78!1'bC#4!3+^N0!4'b>8#3#2#1!4'b?#4#3#2#1").
Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM (k : list kentry) := kn_unfillB (mkbc k).
Lemma kn_unfillM_eq : kn_unfillM = kn_unfill. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+2+[%ub;R+E%uk;R+3%un;R+E0!5'b001'bD'b?$k;R0vd!1'bE#1!3+^N1!1'bD#1!1'b?#1").
Qed.



(* [comment removed for export] *)
Definition kwr_b (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition havoc1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1+2+[!1,^0+[$k;R0$ub;R+E$uk;R+3$un;R+E$K;R+[-1RN$~R+10!2'_4!1'bF#1!5'b2#5#4#3#2#12!3,_T+[#11-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E1$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#9#8#7#6#2#1#3$a;R+^3$n;R+E$k0;R+51$lo;R+3$hi;R+31$e;R+E$m;R+31$e;R+E$lo;R+3$hi;R+31$a;R+^3$n;R+E1$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E1$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#:#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#9#8#7#6#2#1#3").

Definition havoc1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1+2+[!1,^0+[$bc;R+aK$ub;R+E$uk;R+3$un;R+E$K;R+[-1RN$~R+10!2'_4!1'bF#1!5'b1#5#4#3#2#12!3,_T+[#11-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E1$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bJ#9#8#7#6#2#1#3$a;R+^3$n;R+E$k;R+51$lo;R+3$hi;R+31$e;R+E$m;R+31$e;R+E$lo;R+3$hi;R+31$a;R+^3$n;R+E1$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E1$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bK#:#3#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bL#9#8#7#6#2#1#3").

Lemma havoc1B_eqf : forall fk, havoc1B (mkbc fk) = havoc1 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SB0!1+2+[%K;R+[0%un;R+E1%ub;R+E%uk;R+3%un;R+E%K;R+[+1!1'bF#2!1,^0+[!3,_T+[#25!1'aB#:-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bJ7#9#8#7#2#1#3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bK!1'aB#;#3#:#9#8#2#1#4!2'_44!5'b2#6#5#4#3#2-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#;#:#9#8#2#1#4-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#:#9#8#7#2#1#3-1RN$~R+10:26-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#:#9#8#7#2#1#3$a;R+^3$n;R+E$k0;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$n;R+E5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3;$a;R+^3$len;R+E<%wb;R+E%wk;R+3%wn;R+E%kb;R+E%kk;R+3%len;R+E0-^3RN$a;R+^30#21$kb;R+E$kk;R+3!6#5#9#8#7#2#1#3%c;R+3>!1'aB#5$fk;R0!5'b0+E%uk;R+32!1'bM!1'aB#1!1'bN#1$x;R+E!5'b0+32!2'bM!1'aB#2#1!2'bN#2#1$x0;R+3!5'b0+E1!3'bM!1'aB#3#2#1!3'bN#3#2#1$x1;R+E!5'b0+[0!4'bM!1'aB#4#3#2#1!4'bN#4#3#2#1$x2;R+[vd!6'_W3!1'b2#5$b;R3!3+^N0-1RN$~R+10!2'_44!4#1#5#4#3#226-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E8$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$n;R+E5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+39$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bL7#9#8#7#2#1#3=!6'_W>!1'bI#5$l;R>!3+^N0-1RN$~R+10:26-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E8$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$n;R+E5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+39$a;R+^3$len;R+E?=!6'_W@$c;R+3!2'bH#1#6$l;R@!3+^N0-1RN$~R+10:26-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E8$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$n;R+E5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!7#6#3#:#9#8#2#1#4$a;R+^3$len;R+E<=!6'_W>!1'bG#5$l;R>!3+^N0-1RN$~R+10:26-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E?$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$n;R+E5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3;$a;R+^3$len;R+E<=!2,^H0-1RN$~R+10!2'_4!1'bF#1!5'b2#5#4#3#2#12!3,_T+[#15-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#9#8#7#6#2#1#3$a;R+^3$n;R+E$k0;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$n;R+E5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#:#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#9#8#7#6#2#1#3!1'bJA!1'bO#5!1'bKA!1'bP#5!1'bLA!1'bQ#5!1'b1A!1'bR#5!3+^N0!5'bMA#4#3#2#1!5'bN#5#4#3#2#1").
Qed.
#[local] Hint Rewrite havoc1B_eqf : bceq.


Definition havoc1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+2+[!1,^0+[$k;R0$sp;R+b5$ub;R+E$uk;R+3$un;R+E$K;R+[-1RN$~R+10!2'_4!1'bF#1!6'b8#6#5#4#3#2#12!3,_T+[#11-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E1$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#:#8#7#6#2#1#3$a;R+^3$n;R+E$k0;R+51$lo;R+3$hi;R+31$e;R+E$m;R+31$e;R+E$lo;R+3$hi;R+31$a;R+^3$n;R+E1$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E1$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#;#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#:#8#7#6#2#1#3").

Definition havoc1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+2+[!1,^0+[$bc;R+aK$sp;R+b5$ub;R+E$uk;R+3$un;R+E$K;R+[-1RN$~R+10!2'_4!1'bF#1!6'b7#6#5#4#3#2#12!3,_T+[#11-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E1$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bJ#:#8#7#6#2#1#3$a;R+^3$n;R+E$k;R+51$lo;R+3$hi;R+31$e;R+E$m;R+31$e;R+E$lo;R+3$hi;R+31$a;R+^3$n;R+E1$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E1$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bK#;#3#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bL#:#8#7#6#2#1#3").

Lemma havoc1pB_eqf : forall fk, havoc1pB (mkbc fk) = havoc1p fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SC0!1+2+[%K;R+[0%un;R+E1%uk;R+32%sp;R+b5%ub;R+E%uk;R+3%un;R+E%K;R+[+1!1'bF#2!1,^0+[!3,_T+[#26!1'aB#;-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bJ8#9#8#7#2#1#3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bK!1'aB#<#3#:#9#8#2#1#4!2'_45!6'b8#7#6#5#4#3#2-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#<#:#9#8#2#1#4-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#;#9#8#7#2#1#3-1RN$~R+10;27-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#;#9#8#7#2#1#3$a;R+^3$n;R+E$k0;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$n;R+E6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3<$a;R+^3$len;R+E=%wb;R+E%wk;R+3%wn;R+E%kb;R+E%kk;R+3%len;R+E0-^3RN$a;R+^30#21$kb;R+E$kk;R+3!6#5#9#8#7#2#1#3%c;R+3?!1'aB#6$fk;R0!5'b0+b5%ub;R+E3!1'bS!1'aB#1!1'bT#1$x;R+b5!5'b0+E3!2'bS!1'aB#2#1!2'bT#2#1$x0;R+E!5'b0+32!3'bS!1'aB#3#2#1!3'bT#3#2#1$x1;R+3!5'b0+E1!4'bS!1'aB#4#3#2#1!4'bT#4#3#2#1$x2;R+E!5'b0+[0!5'bS!1'aB#5#4#3#2#1!5'bT#5#4#3#2#1$x3;R+[vd!6'_W4!1'b8#6$b;R4!3+^N0-1RN$~R+10!2'_45!5#1#6#5#4#3#227-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E9$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$n;R+E6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3:$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bL8#9#8#7#2#1#3>!6'_W?!1'bI#6$l;R?!3+^N0-1RN$~R+10;27-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E9$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$n;R+E6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3:$a;R+^3$len;R+E@>!6'_WA$c;R+3!2'bH#1#7$l;RA!3+^N0-1RN$~R+10;27-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E9$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$n;R+E6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!7#6#3#:#9#8#2#1#4$a;R+^3$len;R+E=>!6'_W?!1'bG#6$l;R?!3+^N0-1RN$~R+10;27-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E@$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$n;R+E6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3<$a;R+^3$len;R+E=>!2,^H0-1RN$~R+10!2'_4!1'bF#1!6'b8#6#5#4#3#2#12!3,_T+[#16-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#:#8#7#6#2#1#3$a;R+^3$n;R+E$k0;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$n;R+E6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#;#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#:#8#7#6#2#1#3!1'bJB!1'bO#6!1'bKB!1'bP#6!1'bLB!1'bQ#6!1'b7B!1'bC#6!3+^N0!6'bSB#5#4#3#2#1!6'bT#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$k;R!1+2+[$ub;R+E$uk;R+3$un;R+E&sp;R!4'b@#4#3#2#1+b5!4'bU+[+[!5'bT#5#1#4#3#2#5").

Definition kn_havocB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$bc;R+aK$ub;R+E$uk;R+3$un;R+E&sp;R!4'b;#4#3#2#1+b5!4'bU+[+[!5'bS#5#1#4#3#2!1'b=#5").

Lemma kn_havocB_eqf : forall fk, kn_havocB (mkbc fk) = kn_havoc fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+2+[%un;R+E0%sp;R+b5%ub;R+E%uk;R+3%un;R+E%K;R+[0!1'aB#5!1'b=3!5'bT#5!4'b@#5#4#3#2#4#3#2!4'bU+[+[5#5%b1;R+E%k1;R+3%n1;R+E+b5!1'aB#4$fk;R0!5'b0+E%uk;R+31!1'bV!1'aB#1!1'bW#1$x;R+E!5'b0+31!2'bV!1'aB#2#1!2'bW#2#1$x0;R+3!5'b0+E0!3'bV!1'aB#3#2#1!3'bW#3#2#1$x1;R+Evd!6'_W2!1'bT#4$l;R2!3+^N0!4'bU+[+[!4#1!4'b;3#4#3#2#4#3#246!6'_W7!1'b@#4$s;R7!3+^N0!4'bU+[+[!5'bT#5!3#1#4#3#2#4#3#246!6'_W0#4$l;R0!3+^N0!4'bU+[+[5#16!2,^H0!4'bU+[+[!5'bT#4!4'b@#4#3#2#1#3#2#1#4!1'b=8!1'bA#4!1'b;8!1'bB#4!1'bS8!1'bX#4!3+^N0!4'bV8#3#2#1!4'bW#4#3#2#1").
Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

Definition kn_havocM (k : list kentry) := kn_havocB (mkbc k).
Lemma kn_havocM_eq : kn_havocM = kn_havoc. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+2+[%ub;R+E%uk;R+3%un;R+E0!5'b001'bY'bW$k;R0vd!1'bZ#1!3+^N1!1'bY#1!1'bW#1").
Qed.



(* [comment removed for export] *)
Definition kwr_cut (k : list kentry) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry :=
  kcut KWr k ub uk un kb kk len.

Definition kwr_cutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) (kb : expr) (kk : Z) (len : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S00$bc;R+aK$ub;R+E$uk;R+3$un;R+E$kb;R+E$kk;R+3$len;R+E!8'b[#7,a4#6#5#4#3#2#1").

Lemma kwr_cutB_eqf : forall fk, kwr_cutB (mkbc fk) = kwr_cut fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80!1+2+[%len;R+E0%kk;R+31%kb;R+E2%un;R+E3%~R+^3%~R+E+[%mk;R5%wb;R+E%wk;R+3%wn;R+E3!1'aB#7$fk;R0!5'b0+E%uk;R+34!1'b\!1'aB#1!1'c0#1$x;R+E!5'b0+34!2'b\!1'aB#2#1!2'c0#2#1$x0;R+3!5'b0+E3!3'b\!1'aB#3#2#1!3'c0#3#2#1$x1;R+E!5'b0+E2!4'b\!1'aB#4#3#2#1!4'c0#4#3#2#1$x2;R+E!5'b0+31!5'b\!1'aB#5#4#3#2#1!5'c0#5#4#3#2#1$x3;R+3!5'b0+E0!6'b\!1'aB#6#5#4#3#2#1!6'c0#6#5#4#3#2#1$x4;R+Evd!6'_W6$mk;R5!2'c1#1#8$l;R6!3+^N0!7#1,a4#7#6#5#4#3#2!8'c1,a4#8#7#6#5#4#3#2!2,^H0!8'c1,a4#7#6#5#4#3#2#1!1'b[7!1'c2#7!3+^N0!7'b\7#6#5#4#3#2#1!7'c0#7#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite kwr_cutB_eqf : bceq.


Definition cutout1 (k : list kentry) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1+2+[!1,^0+[$k;R0$ub;R+E$uk;R+3$un;R+E$K;R+[-1RN$~R+10!5'b2#5#4#3#2#12!3,_T+[#11-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E1$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#9#8#7#6#2#1#3$a;R+^3$n;R+E$k0;R+51$lo;R+3$hi;R+31$e;R+E$m;R+31$e;R+E$lo;R+3$hi;R+31$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'c0#9#8#7#6#2#1#3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E1$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#:#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#9#8#7#6#2#1#3").

Definition cutout1B (bc : bctx) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!1+2+[!1,^0+[$bc;R+aK$ub;R+E$uk;R+3$un;R+E$K;R+[-1RN$~R+10!5'b1#5#4#3#2#12!3,_T+[#11-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E1$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bJ#9#8#7#6#2#1#3$a;R+^3$n;R+E$k;R+51$lo;R+3$hi;R+31$e;R+E$m;R+31$e;R+E$lo;R+3$hi;R+31$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'b\#9#8#7#6#2#1#3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E1$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bK#:#3#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bL#9#8#7#6#2#1#3").

Lemma cutout1B_eqf : forall fk, cutout1B (mkbc fk) = cutout1 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SE0!1+2+[%K;R+[0%un;R+E1%kb;R+E%kk;R+3%len;R+E0%ub;R+E%uk;R+3%un;R+E3!1,^0+[!3,_T+[#25!1'aB#:-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bJ7#9#8#7#2#1#3-^3RN$a;R+^30#21$kb;R+E$kk;R+3!6#5#9#8#7#2#1#3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bK!1'aB#;#3#:#9#8#2#1#4-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bL7#9#8#7#2#1#3!5'b2#6#5#4#3#2-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'c0#:#9#8#7#2#1#3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#;#:#9#8#2#1#4-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#:#9#8#7#2#1#3-1RN$~R+10<26-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#:#9#8#7#2#1#3$a;R+^3$n;R+E$k0;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$len;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3>$a;R+^3$len;R+E?%ub;R+E%uk;R+3%un;R+E%K;R+[+1%wb;R+E%wk;R+3%wn;R+E3%c;R+3B!1'aB#5$fk;R0!5'b0+E%uk;R+32!1'c3!1'aB#1!1'c4#1$x;R+E!5'b0+32!2'c3!1'aB#2#1!2'c4#2#1$x0;R+3!5'b0+E1!3'c3!1'aB#3#2#1!3'c4#3#2#1$x1;R+E!5'b0+[0!4'c3!1'aB#4#3#2#1!4'c4#4#3#2#1$x2;R+[vd!6'_W4!1'c0#5$l;R4!3+^N0-1RN$~R+10!5'b1!1'aB#6#5#4#3#226-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E8$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$len;R+E9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3:$a;R+^3$len;R+E;@!6'_WA!1'b2#5$b;RA!3+^N0-1RN$~R+10!4#1#5#4#3#226-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E8$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$len;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3:$a;R+^3$len;R+E;@!6'_WB!1'bI#5$l;RB!3+^N0-1RN$~R+10<26-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E8$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$len;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3:$a;R+^3$len;R+E9@!6'_WC$c;R+3!2'bH#1#6$l;RC!3+^N0-1RN$~R+10<26-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E8$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$len;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!7#6#3#:#9#8#2#1#4$a;R+^3$len;R+E?@!6'_WB!1'bG#5$l;RB!3+^N0-1RN$~R+10<26-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E9$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$len;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3>$a;R+^3$len;R+E?@!2,^H0-1RN$~R+10!5'b2#5#4#3#2#12!3,_T+[#15-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E5$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#9#8#7#6#2#1#3$a;R+^3$n;R+E$k0;R+55$lo;R+3$hi;R+35$e;R+E$m;R+35$e;R+E$lo;R+3$hi;R+35$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'c0#9#8#7#6#2#1#3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E5$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#:#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#9#8#7#6#2#1#3!1'bJD!1'bO#5!1'bKD!1'bP#5!1'bLD!1'bQ#5!1'b1D!1'bR#5!1'b\D!1'c5#5!3+^N0!5'c3D#4#3#2#1!5'c4#5#4#3#2#1").
Qed.
#[local] Hint Rewrite cutout1B_eqf : bceq.


Definition cutout1p (k : list kentry) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+2+[!1,^0+[$k;R0$sp;R+b5$ub;R+E$uk;R+3$un;R+E$K;R+[-1RN$~R+10!6'b8#6#5#4#3#2#12!3,_T+[#11-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E1$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#:#8#7#6#2#1#3$a;R+^3$n;R+E$k0;R+51$lo;R+3$hi;R+31$e;R+E$m;R+31$e;R+E$lo;R+3$hi;R+31$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'c0#:#8#7#6#2#1#3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E1$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#;#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#:#8#7#6#2#1#3").

Definition cutout1pB (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S20!1+2+[!1,^0+[$bc;R+aK$sp;R+b5$ub;R+E$uk;R+3$un;R+E$K;R+[-1RN$~R+10!6'b7#6#5#4#3#2#12!3,_T+[#11-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E1$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bJ#:#8#7#6#2#1#3$a;R+^3$n;R+E$k;R+51$lo;R+3$hi;R+31$e;R+E$m;R+31$e;R+E$lo;R+3$hi;R+31$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'b\#:#8#7#6#2#1#3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E1$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bK#;#3#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bL#:#8#7#6#2#1#3").

Lemma cutout1pB_eqf : forall fk, cutout1pB (mkbc fk) = cutout1p fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SF0!1+2+[%K;R+[0%un;R+E1%uk;R+32%kb;R+E%kk;R+3%len;R+E0%ub;R+E%uk;R+3%un;R+E4!1,^0+[!3,_T+[#26!1'aB#;-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bJ8#9#8#7#2#1#3-^3RN$a;R+^30#21$kb;R+E$kk;R+3!6#5#9#8#7#2#1#3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bK!1'aB#<#3#:#9#8#2#1#4-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bL8#9#8#7#2#1#3!6'b8#7#6#5#4#3#2-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'c0#;#9#8#7#2#1#3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#<#:#9#8#2#1#4-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#;#9#8#7#2#1#3-1RN$~R+10=27-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#;#9#8#7#2#1#3$a;R+^3$n;R+E$k0;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$len;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3?$a;R+^3$len;R+E@%sp;R+b5%ub;R+E%uk;R+3%un;R+E%K;R+[+1%wb;R+E%wk;R+3%wn;R+E4%c;R+3C!1'aB#6$fk;R0!5'b0+b5%ub;R+E3!1'c6!1'aB#1!1'c7#1$x;R+b5!5'b0+E3!2'c6!1'aB#2#1!2'c7#2#1$x0;R+E!5'b0+32!3'c6!1'aB#3#2#1!3'c7#3#2#1$x1;R+3!5'b0+E1!4'c6!1'aB#4#3#2#1!4'c7#4#3#2#1$x2;R+E!5'b0+[0!5'c6!1'aB#5#4#3#2#1!5'c7#5#4#3#2#1$x3;R+[vd!6'_W5!1'c0#6$l;R5!3+^N0-1RN$~R+10!6'b7!1'aB#7#6#5#4#3#227-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E9$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$len;R+E:$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3;$a;R+^3$len;R+E<A!6'_WB!1'b8#6$b;RB!3+^N0-1RN$~R+10!5#1#6#5#4#3#227-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E9$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$len;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3;$a;R+^3$len;R+E<A!6'_WC!1'bI#6$l;RC!3+^N0-1RN$~R+10=27-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E9$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$len;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3;$a;R+^3$len;R+E:A!6'_WD$c;R+3!2'bH#1#7$l;RD!3+^N0-1RN$~R+10=27-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E9$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$len;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!7#6#3#:#9#8#2#1#4$a;R+^3$len;R+E@A!6'_WC!1'bG#6$l;RC!3+^N0-1RN$~R+10=27-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E:$a;R+^3$n;R+E$k;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$len;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3?$a;R+^3$len;R+E@A!2,^H0-1RN$~R+10!6'b8#6#5#4#3#2#12!3,_T+[#16-[RN$K;R+[0#1:$a;R+^3$w;R+5$v;R+E6$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bG#:#8#7#6#2#1#3$a;R+^3$n;R+E$k0;R+56$lo;R+3$hi;R+36$e;R+E$m;R+36$e;R+E$lo;R+3$hi;R+36$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'c0#:#8#7#6#2#1#3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E6$a;R+^3$len;R+E$c;R+3-^3RN$a;R+^30#31$kb;R+E$kk;R+3!8'bH#3#;#9#8#7#2#1#4$a;R+^3$len;R+E-^3RN$a;R+^30#21$kb;R+E$kk;R+3!7'bI#:#8#7#6#2#1#3!1'bJE!1'bO#6!1'bKE!1'bP#6!1'bLE!1'bQ#6!1'b7E!1'bC#6!1'b\E!1'c5#6!3+^N0!6'c6E#5#4#3#2#1!6'c7#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$k;R!1+2+[$ub;R+E$uk;R+3$un;R+E&sp;R!4'b@#4#3#2#1+b5!4'bU+[+[!5'c7#5#1#4#3#2#5").

Definition kn_cutoutB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$bc;R+aK$ub;R+E$uk;R+3$un;R+E&sp;R!4'b;#4#3#2#1+b5!4'bU+[+[!5'c6#5#1#4#3#2!1'b=#5").

Lemma kn_cutoutB_eqf : forall fk, kn_cutoutB (mkbc fk) = kn_cutout fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+2+[%un;R+E0%sp;R+b5%ub;R+E%uk;R+3%un;R+E%K;R+[0!1'aB#5!1'b=3!5'c7#5!4'b@#5#4#3#2#4#3#2!4'bU+[+[5#5%b1;R+E%k1;R+3%n1;R+E+b5!1'aB#4$fk;R0!5'b0+E%uk;R+31!1'c8!1'aB#1!1'c9#1$x;R+E!5'b0+31!2'c8!1'aB#2#1!2'c9#2#1$x0;R+3!5'b0+E0!3'c8!1'aB#3#2#1!3'c9#3#2#1$x1;R+Evd!6'_W2!1'c7#4$l;R2!3+^N0!4'bU+[+[!4#1!4'b;3#4#3#2#4#3#246!6'_W7!1'b@#4$s;R7!3+^N0!4'bU+[+[!5'c7#5!3#1#4#3#2#4#3#246!6'_W0#4$l;R0!3+^N0!4'bU+[+[5#16!2,^H0!4'bU+[+[!5'c7#4!4'b@#4#3#2#1#3#2#1#4!1'b=8!1'bA#4!1'b;8!1'bB#4!1'c68!1'c:#4!3+^N0!4'c88#3#2#1!4'c9#4#3#2#1").
Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.

Definition kn_cutoutM (k : list kentry) := kn_cutoutB (mkbc k).
Lemma kn_cutoutM_eq : kn_cutoutM = kn_cutout. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+2+[%ub;R+E%uk;R+3%un;R+E0!5'b001'c;'c9$k;R0vd!1'c<#1!3+^N1!1'c;#1!1'c9#1").
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
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$k;R!1+2+[$a;R+3$n;R+3!4'bU+[+[!2'c=#2#1#3").

(* [comment removed for export] *)
Definition kimg_clip (k : list kentry) : list kentry :=
  List.filter (fun K => match K with KImg lo hi => Z.leb (img_lo A) lo && Z.leb lo hi && Z.leb hi (img_hi A) | _ => true end) k.

(* [comment removed for export] *)
Definition kreadZ (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookup segs k b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.

Definition kreadZB (bc : bctx) (b : expr) (off : Z) (n : nat) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S40!1+^;+3!1+2+a@!1+2+1!1,^2+3$bc;R+aK$b;R+E$off;R+3$n;R+5-c>RN$x;R+c>0!8'c?/segs;#4#3#2#1,6!1,^0+1!1,^0+a@3$v;R+E$scs;R1$hints;R2-ERN$v;R+E0#38$z;R+3-2RN$scs;R!1+2+a@0#32!2,^<+3!2'^=#1'^>$s;R+a@$l;R!1+2+a@3$n0;R+53$op;R+^?$a;R+E$b0;R+E3$op;R+^?$a;R+E$b0;R+E3$op;R+^@$a;R+E$b0;R+E3$op;R+^@$a;R+E$b0;R+E3$sx;R+1$lo;R+5$n0;R+5$e;R+E3$sx;R+1$k;R+5$i;R+3$n0;R+53$scs;R1$hints;R233").

Lemma kreadZB_eqf : forall fk, kreadZB (mkbc fk) = kreadZ fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;0!1+^;+3%n;R+50%rb;R+E%rk;R+3%n;R+5%sx;R+1%hints;R!1+2+1%acc;R!1+2+a@+c>!1,^0+1!1,^0+a@!1+2+a@!1+2+1!1,^2+3-2RN$scs;R!1+2+a@0#32!2,^<+3!2'^=#1'^>$s;R+a@$l;R!1+2+a@7-ERN$v;R+E0#38$z;R+38$n0;R+57$op;R+^?$a;R+E$b0;R+E7$op;R+^?$a;R+E$b0;R+E7$op;R+^@$a;R+E$b0;R+E7$op;R+^@$a;R+E$b0;R+E7$sx;R+1$lo;R+5$n0;R+5$e;R+E7$sx;R+1$k0;R+5$i;R+3$n0;R+57!1'aB#4$fk;R!1+2+[!5'b0+E%off;R+31!1'c@!1'aB#1!1'cA#1$x;R+E!5'b0+31!2'c@!1'aB#2#1!2'cA#2#1$x0;R+3!5'b0+50!3'c@!1'aB#3#2#1!3'cA#3#2#1$x1;R+5vd!6'_W2!2'cB/segs;#4$l;R2!3+^N0-c>RN$x;R+c>0!6#1#4#3#2,6343$v;R+E$scs;R5$hints;R6-ERN$v;R+E0#38$z;R+38$n0;R+57$op;R+^?$a;R+E$b0;R+E7$op;R+^?$a;R+E$b0;R+E7$op;R+^@$a;R+E$b0;R+E7$op;R+^@$a;R+E$b0;R+E7$sx;R+1$lo;R+5$n0;R+5$e;R+E7$sx;R+1$k;R+5$i;R+3$n0;R+57$scs;R5$hints;R677-c>RN$x;R+c>0!8'cB/segs;#5#4#3#2,6343$v;R+E$scs;R5$hints;R69$scs;R5$hints;R677!2,^H0-c>RN$x;R+c>0!8'cB/segs;#4#3#2#1,6343$v;R+E$scs;R5$hints;R69$scs;R5$hints;R677!2'c?/segs;:!2'cC#4/segs;!3+^N0!4'c@:#3#2#1!4'cA#4#3#2#1").
Qed.
#[local] Hint Rewrite kreadZB_eqf : bceq.


(* [comment removed for export] *)
Definition kread8e (k : list kentry) (b : expr) (off : Z) : option expr :=
  match know_lookup segs k b off 8 false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Definition kread8eB (bc : bctx) (b : expr) (off : Z) : option expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!1+^;+E!1+2+a@!1+2+1!1,^2+E$bc;R+aK$b;R+E$off;R+3-c>RN$x;R+c>0!8'c?/segs;#3#2#1}8,6!1,^0+1!1,^0+a@3$v;R+E$scs;R1$hints;R2-2RN$scs;R!1+2+a@0#22!2,^<+E#3$s;R+a@$l;R!1+2+a@3$scs;R1$hints;R233").

Lemma kread8eB_eqf : forall fk, kread8eB (mkbc fk) = kread8e fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S:0!1+^;+E%rb;R+E%rk;R+3%n;R+5%sx;R+1%hints;R!1+2+1%acc;R!1+2+a@+c>}8!1,^0+1!1,^0+a@!1+2+a@!1+2+1!1,^2+E-2RN$scs;R!1+2+a@0#22!2,^<+E#3$s;R+a@$l;R!1+2+a@7!1'aB#3$fk;R!1+2+[!5'b0+E%off;R+30!1'cD!1'aB#1!1'cE#1$x;R+E!5'b0+30!2'cD!1'aB#2#1!2'cE#2#1$x0;R+3vd!6'_W1!2'cB/segs;#3$l;R1!3+^N0-c>RN$x;R+c>0!6#1#3#22,6343$v;R+E$scs;R5$hints;R68$scs;R5$hints;R677-c>RN$x;R+c>0!8'cB/segs;#4#3#22,6343$v;R+E$scs;R5$hints;R68$scs;R5$hints;R677!2,^H0-c>RN$x;R+c>0!8'cB/segs;#3#2#12,6343$v;R+E$scs;R5$hints;R68$scs;R5$hints;R677!2'c?/segs;9!2'cC#3/segs;!3+^N0!3'cD9#2#1!3'cE#3#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SD0!1+2+[%n;R+3+1%off;R+31!2'_8!2'_9#8#2!2'_:#1#7!1'aB#@!2'^U#2#1!2'_:!2'^U#8#75-1RN$~R+1+132-^;RN$x;R!1+^;+3+1!2'cH4#32$wl;R+36,6,6!2'_8!2'_:,I#6!2'a[#6'^>!1,H#6!5'cG#?#9#7#6#5!5'cG#>#8#6#5#4!5'cG#@#:#8#7#6-1RN$~R+1+1!2'_88!7'cK#@#8#79#2#1#32,9<-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E:$a;R+^3$n0;R+E;$a;R+^3$n0;R+E$k1;R+5:$lo;R+3$hi;R+3;$e;R+E$m;R+3;$e;R+E$lo;R+3$hi;R+3:$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^;RN$x;R!1+^;+3+1!2'cJ#@#32$wl;R+36,6,62,9=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E<$a;R+^3$n0;R+E$c;R+3:$a;R+^3$n0;R+E;%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1%e;R+E!1+^;+3!5'cG#=#7#5#4#3!1'aB#;!3,_T+[#6#5$fk;R0!5'b00%b;R+E2!1'cF!1'aB#1!1'cG#1$k;R0!5'b0+E2!2'cF!1'aB#2#1!2'cG#2#1$b;R+E!5'b0+31!3'cF!1'aB#3#2#1!3'cG#3#2#1$off;R+3!5'b0+3+1!4'cF!1'aB#4#3#2#1!4'cG#4#3#2#1$n;R+3!8'`;+[$k;R0%b;R+E%off;R+3%n;R+3!3+^N+1!5'cF!1'aB#9#4#3#2#1!5'cG#9#4#3#2#1$b;R+E$off;R+3$n;R+3!2,^H+1!5'cG#8!1,^0+[#3#2#1$K;R+[$rest;R0$IH;R%b;R+E%off;R+3%n;R+3!3+^N+1!5'cF!1'aB#:#4#3#2#1!5'cG#:#4#3#2#1$b;R+E$off;R+3$n;R+3vd!6'_W+1!5'cG#;#5#3#2#1$b;R+1!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E#4$a;R+^3$n0;R+E#3$a;R+^3$n0;R+E$k1;R+5#4$lo;R+3$hi;R+3#3$e;R+E$m;R+3#3$e;R+E$lo;R+3$hi;R+3#4$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+172,9-1RN$~R+1+1!2'_88!7'cI4#8#79#2#1#32,9#5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#5$a;R+^3$n0;R+E$c;R+3#4$a;R+^3$n0;R+E#3>!6'_W?!1'cK#;$b;R?!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E:$a;R+^3$n0;R+E;$a;R+^3$n0;R+E$k1;R+5:$lo;R+3$hi;R+3;$e;R+E$m;R+3;$e;R+E$lo;R+3$hi;R+3:$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+172,9-1RN$~R+1+1!2'_88!6#5#8#79#2#1#32,9<$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E<$a;R+^3$n0;R+E$c;R+3:$a;R+^3$n0;R+E;>!6'_W@!1'cJ#;$o;R@!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E:$a;R+^3$n0;R+E;$a;R+^3$n0;R+E$k1;R+5:$lo;R+3$hi;R+3;$e;R+E$m;R+3;$e;R+E$lo;R+3$hi;R+3:$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^;RN$x;R!1+^;+3+1!1#5#32$wl;R+36,6,62,9=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E<$a;R+^3$n0;R+E$c;R+3:$a;R+^3$n0;R+E;>!2,^H+1-[RN$k0;R+[+1#6:$a;R+^3$w;R+5$v;R+E;$a;R+^3$n0;R+EA$a;R+^3$n0;R+E$k1;R+5;$lo;R+3$hi;R+3A$e;R+E$m;R+3A$e;R+E$lo;R+3$hi;R+3;$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+1-1RN$~R+1+1!2'_8!2'_9#7#2!2'_:#1#62-^;RN$x;R!1+^;+3+1!2'cJ#?#32$wl;R+3!2'_:!2'^U#7#65,6,62,9-1RN$~R+1+1!2'_8!2'_8!2'_:,I#5!2'a[#5'^>!7'cK#?#7#6!1,H#5#2#1#32,9:$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E:$a;R+^3$n0;R+E$c;R+3;$a;R+^3$n0;R+EA!1'cHB!1'cL#;!1'cIB!1'cM#;!5'cFB#5#3#2#1!3#4#3#2#1!3+^N+1!5'cFBC#3#2#1!5'cG#;C#3#2#1#4#3#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SD0!1+2+[%n;R+E+1%off;R+31!2'_8!2'_9#8#2!2'_:#1#7!1'aB#@!2'^U#3#1!2'_:!2'^U#9#25-^;RN$x;R!1+^;+3+1!2'cH!1'aB#A#42$wl;R+36,6-1RN$~R+1+132-^;RN$x;R!1+^;+3+1!2'cP4#62$nh;R+37,6,6!5'cO#?#9#7#6#5!5'cO#>#8#6#5#4!2'cQ#@#6!5'cO#@#:#8#7#6-1RN$~R+1+1!7'cK#@#8#7#6#2#1#32,9<-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E9$a;R+^3$n0;R+E:$a;R+^3$n0;R+E$k1;R+59$lo;R+3$hi;R+3:$e;R+E$m;R+3:$e;R+E$lo;R+3$hi;R+39$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^;RN$x;R!1+^;+3+1;2$nh;R+3-^;RN$x;R!1+^;+3+1!2'cJ#A#42$wl;R+36,6,6,62,9=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E<$a;R+^3$n0;R+E$c;R+39$a;R+^3$n0;R+E:%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1%e;R+E!1+^;+3!5'cO#=#7#5#4#3!1'aB#;!3,_T+[#6#5$fk;R0!5'b00%b;R+E2!1'cN!1'aB#1!1'cO#1$k;R0!5'b0+E2!2'cN!1'aB#2#1!2'cO#2#1$b;R+E!5'b0+31!3'cN!1'aB#3#2#1!3'cO#3#2#1$off;R+3!5'b0+E+1!4'cN!1'aB#4#3#2#1!4'cO#4#3#2#1$n;R+E!8'`;+[$k;R0%b;R+E%off;R+3%n;R+E!3+^N+1!5'cN!1'aB#9#4#3#2#1!5'cO#9#4#3#2#1$b;R+E$off;R+3$n;R+E!2,^H+1!5'cO#8!1,^0+[#3#2#1$K;R+[$rest;R0$IH;R%b;R+E%off;R+3%n;R+E!3+^N+1!5'cN!1'aB#:#4#3#2#1!5'cO#:#4#3#2#1$b;R+E$off;R+3$n;R+Evd!6'_W+1!5'cO#;#5#3#2#1$b;R+1!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E#4$a;R+^3$n0;R+E#3$a;R+^3$n0;R+E$k1;R+5#4$lo;R+3$hi;R+3#3$e;R+E$m;R+3#3$e;R+E$lo;R+3$hi;R+3#4$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+182,9-1RN$~R+1+1!7'cI4#8#7#6#2#1#32,9#5$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#5$a;R+^3$n0;R+E$c;R+3#4$a;R+^3$n0;R+E#3>!6'_W?!1'cK#;$b;R?!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E9$a;R+^3$n0;R+E:$a;R+^3$n0;R+E$k1;R+59$lo;R+3$hi;R+3:$e;R+E$m;R+3:$e;R+E$lo;R+3$hi;R+39$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+182,9-1RN$~R+1+1!6#5#8#7#6#2#1#32,9<$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E<$a;R+^3$n0;R+E$c;R+39$a;R+^3$n0;R+E:>!6'_W@!1'cQ#;$o;R@!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E9$a;R+^3$n0;R+E:$a;R+^3$n0;R+E$k1;R+59$lo;R+3$hi;R+3:$e;R+E$m;R+3:$e;R+E$lo;R+3$hi;R+39$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^;RN$x;R!1+^;+3+1!1#5#62$nh;R+37,6,62,9=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E<$a;R+^3$n0;R+E$c;R+39$a;R+^3$n0;R+E:>!6'_W@!1'cJ#;$o;R@!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E9$a;R+^3$n0;R+E:$a;R+^3$n0;R+E$k1;R+59$lo;R+3$hi;R+3:$e;R+E$m;R+3:$e;R+E$lo;R+3$hi;R+39$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+1-1RN$~R+1+132-^;RN$x;R!1+^;+3+1;2$nh;R+3-^;RN$x;R!1+^;+3+1!1#6#42$wl;R+36,6,6,62,9=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E<$a;R+^3$n0;R+E$c;R+39$a;R+^3$n0;R+E:>!2,^H+1-[RN$k0;R+[+1#6:$a;R+^3$w;R+5$v;R+E:$a;R+^3$n0;R+EA$a;R+^3$n0;R+E$k1;R+5:$lo;R+3$hi;R+3A$e;R+E$m;R+3A$e;R+E$lo;R+3$hi;R+3:$a;R+^3$wn;R+E-^3RN$a;R+^3+1#21$wb;R+E$wk;R+3-1RN$~R+1+1-1RN$~R+1+1!2'_8!2'_9#7#2!2'_:#1#62-^;RN$x;R!1+^;+3+1!2'cQ#?#52$nh;R+3-^;RN$x;R!1+^;+3+1!2'cJ#@#42$wl;R+3!2'_:!2'^U#8#25,6,6,62,9-1RN$~R+1+1!7'cK#?#7#6#5#2#1#32,99$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E9$a;R+^3$n0;R+E$c;R+3:$a;R+^3$n0;R+EA!1'cHB!1'cL#;!1'cPB!1'cR#;!1'cIB!1'cM#;!5'cNB#5#3#2#1!3#4#3#2#1!3+^N+1!5'cNBC#3#2#1!5'cO#;C#3#2#1#4#3#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SD0!1+2+[%n;R+E+1%off;R+31!2'_8!2'_9#8#2!2'_:#1#7!1'aB#@!2'^U#3#1!2'_:!2'^U#9#25-^;RN$x;R!1+^;+3+1!2'cH!1'aB#A#42$zl;R+36,6-1RN$~R+1+132-^;RN$x;R!1+^;+3+1!2'cP4#62$nh;R+37,6,6!5'cT#?#9#7#6#5!2'cQ#@#6!5'cT#@#:#8#7#6-1RN$~R+1+1!7'cK#@#8#7#6#2#1#32,9;!5'cT#>#8#6#5#4-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E9$a;R+^3$zn;R+E-^3RN$a;R+^3+1#21$zb;R+E$zk;R+3-1RN$~R+1+1-1RN$~R+1+132-^;RN$x;R!1+^;+3+1:2$nh;R+3-^;RN$x;R!1+^;+3+1!2'cJ#A#42$zl;R+36,6,6,62,9<$a;R+^3$n0;R+E$k1;R+59$lo;R+3$hi;R+3=$e;R+E$m;R+3=$e;R+E$lo;R+3$hi;R+39$a;R+^3$n0;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E;$a;R+^3$n0;R+E$c;R+39$a;R+^3$n0;R+E=%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1%e;R+E!1+^;+3!5'cT#=#7#5#4#3!1'aB#;!3,_T+[#6#5$fk;R0!5'b00%b;R+E2!1'cS!1'aB#1!1'cT#1$k;R0!5'b0+E2!2'cS!1'aB#2#1!2'cT#2#1$b;R+E!5'b0+31!3'cS!1'aB#3#2#1!3'cT#3#2#1$off;R+3!5'b0+E+1!4'cS!1'aB#4#3#2#1!4'cT#4#3#2#1$n;R+E!8'`;+[$k;R0%b;R+E%off;R+3%n;R+E!3+^N+1!5'cS!1'aB#9#4#3#2#1!5'cT#9#4#3#2#1$b;R+E$off;R+3$n;R+E!2,^H+1!5'cT#8!1,^0+[#3#2#1$K;R+[$rest;R0$IH;R%b;R+E%off;R+3%n;R+E!3+^N+1!5'cS!1'aB#:#4#3#2#1!5'cT#:#4#3#2#1$b;R+E$off;R+3$n;R+Evd!6'_W+1!5'cT#;#5#3#2#1$b;R+1!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E#4$a;R+^3$zn;R+E-^3RN$a;R+^3+1#21$zb;R+E$zk;R+3-1RN$~R+1+182,9-1RN$~R+1+1!7'cI4#8#7#6#2#1#32,9#5$a;R+^3$n0;R+E$k1;R+5#4$lo;R+3$hi;R+3#3$e;R+E$m;R+3#3$e;R+E$lo;R+3$hi;R+3#4$a;R+^3$n0;R+E#3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#5$a;R+^3$n0;R+E$c;R+3#4$a;R+^3$n0;R+E#3>!6'_W?!1'cK#;$b;R?!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E9$a;R+^3$zn;R+E-^3RN$a;R+^3+1#21$zb;R+E$zk;R+3-1RN$~R+1+182,9-1RN$~R+1+1!6#5#8#7#6#2#1#32,9;$a;R+^3$n0;R+E$k1;R+59$lo;R+3$hi;R+3=$e;R+E$m;R+3=$e;R+E$lo;R+3$hi;R+39$a;R+^3$n0;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E;$a;R+^3$n0;R+E$c;R+39$a;R+^3$n0;R+E=>!6'_W@!1'cQ#;$o;R@!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E9$a;R+^3$zn;R+E-^3RN$a;R+^3+1#21$zb;R+E$zk;R+3-1RN$~R+1+1-1RN$~R+1+132-^;RN$x;R!1+^;+3+1!1#5#62$nh;R+37,6,62,9<$a;R+^3$n0;R+E$k1;R+59$lo;R+3$hi;R+3=$e;R+E$m;R+3=$e;R+E$lo;R+3$hi;R+39$a;R+^3$n0;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E;$a;R+^3$n0;R+E$c;R+39$a;R+^3$n0;R+E=>!6'_W@!1'cJ#;$o;R@!3+^N+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E9$a;R+^3$zn;R+E-^3RN$a;R+^3+1#21$zb;R+E$zk;R+3-1RN$~R+1+1-1RN$~R+1+132-^;RN$x;R!1+^;+3+1:2$nh;R+3-^;RN$x;R!1+^;+3+1!1#6#42$zl;R+36,6,6,62,9<$a;R+^3$n0;R+E$k1;R+59$lo;R+3$hi;R+3=$e;R+E$m;R+3=$e;R+E$lo;R+3$hi;R+39$a;R+^3$n0;R+E=$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E;$a;R+^3$n0;R+E$c;R+39$a;R+^3$n0;R+E=>!2,^H+1-[RN$k0;R+[+1#6:$a;R+^3$w;R+5$v;R+E=$a;R+^3$zn;R+E-^3RN$a;R+^3+1#21$zb;R+E$zk;R+3-1RN$~R+1+1-1RN$~R+1+1!2'_8!2'_9#7#2!2'_:#1#62-^;RN$x;R!1+^;+3+1!2'cQ#?#52$nh;R+3-^;RN$x;R!1+^;+3+1!2'cJ#@#42$zl;R+3!2'_:!2'^U#8#25,6,6,62,9-1RN$~R+1+1!7'cK#?#7#6#5#2#1#32,99$a;R+^3$n0;R+E$k1;R+5=$lo;R+3$hi;R+3A$e;R+E$m;R+3A$e;R+E$lo;R+3$hi;R+3=$a;R+^3$n0;R+EA$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E9$a;R+^3$n0;R+E$c;R+3=$a;R+^3$n0;R+EA!1'cHB!1'cL#;!1'cPB!1'cR#;!1'cIB!1'cM#;!5'cSB#5#3#2#1!3#4#3#2#1!3+^N+1!5'cSBC#3#2#1!5'cT#;C#3#2#1#4#3#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SJ0!1+2+[%c;R+3+1%n;R+E1%off;R+32!1,^K|800;!2'^=#34!2'aY5!2'^=#74!2'_8!2'_86!2'_9#:#2!2'_:#1#9!1'aB#C!2'^U#3#1!2'_:!2'^U#;#29-^;RN$x;R!1+^;+3+1!2'cH!1'aB#D#52$zl;R+3:,6-1RN$~R+1+172-^;RN$x;R!1+^;+3+1!2'cP8#82$nh;R+3;,6,6!6'cV#A#:#8#7#6#5!6'cV#@#9#7#6#5#4!6'cV#B#;#9#8#7#6!2'cQ#C#8!6'cV#C#<#:#9#8#7-1RN$~R+1+1!2'_86!7'cK#C#:#9#8#2#1#42,9A-[RN$k0;R+[+1#8:$a;R+^3$w;R+5$v;R+E=$a;R+^3$n0;R+E>$a;R+^3$n0;R+E$k1;R+5=$lo;R+3$hi;R+3>$e;R+E$m;R+3>$e;R+E$lo;R+3$hi;R+3=$a;R+^3$n0;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E?$a;R+^3$zn;R+E$c';R+3-^3RN$a;R+^3+1#31$zb;R+E$zk;R+3-1RN$~R+1+1-1RN$~R+1+172-^;RN$x;R!1+^;+3+1@2$nh;R+3-^;RN$x;R!1+^;+3+1!2'cJ#D#52$zl;R+3:,6,6,62,9B$a;R+^3$n0;R+E>%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1%e;R+E!1+^;+3!6'cV#?#8#6#5#4#3!2'aY5!2'^=#64!1'aB#=!3,_T+[#7#6$fk;R0!5'b00%b;R+E3!1'cU!1'aB#1!1'cV#1$k;R0!5'b0+E3!2'cU!1'aB#2#1!2'cV#2#1$b;R+E!5'b0+32!3'cU!1'aB#3#2#1!3'cV#3#2#1$off;R+3!5'b0+E1!4'cU!1'aB#4#3#2#1!4'cV#4#3#2#1$n;R+E!5'b0+3+1!5'cU!1'aB#5#4#3#2#1!5'cV#5#4#3#2#1$c;R+3!9'`;+[$k;R0%b;R+E%off;R+3%n;R+E%c;R+3!3+^N+1!6'cU!1'aB#;#5#4#3#2#1!6'cV#;#5#4#3#2#1$b;R+E$off;R+3$n;R+E$c;R+3!2,^H+1!6'cV#:!1,^0+[#4#3#2#1$K;R+[$rest;R0$IH;R%b;R+E%off;R+3%n;R+E%c;R+3!3+^N+1!6'cU!1'aB#<#5#4#3#2#1!6'cV#<#5#4#3#2#1$b;R+E$off;R+3$n;R+E$c;R+3vd!6'_W+1!6'cV#=#6#4#3#2#1$b;R+1!3+^N+1-[RN$k0;R+[+1#8:$a;R+^3$w;R+5$v;R+E#4$a;R+^3$n0;R+E#3$a;R+^3$n0;R+E$k1;R+5#4$lo;R+3$hi;R+3#3$e;R+E$m;R+3#3$e;R+E$lo;R+3$hi;R+3#4$a;R+^3$n0;R+E#3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E#5$a;R+^3$zn;R+E$c';R+3-^3RN$a;R+^3+1#31$zb;R+E$zk;R+3-1RN$~R+1+1<2,9-1RN$~R+1+1!2'_86!7'cI8#:#9#8#2#1#42,9#6$a;R+^3$n0;R+E#3C!6'_WD!1'cK#=$b;RD!3+^N+1-[RN$k0;R+[+1#8:$a;R+^3$w;R+5$v;R+E=$a;R+^3$n0;R+E>$a;R+^3$n0;R+E$k1;R+5=$lo;R+3$hi;R+3>$e;R+E$m;R+3>$e;R+E$lo;R+3$hi;R+3=$a;R+^3$n0;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E?$a;R+^3$zn;R+E$c';R+3-^3RN$a;R+^3+1#31$zb;R+E$zk;R+3-1RN$~R+1+1<2,9-1RN$~R+1+1!2'_86!6#6#:#9#8#2#1#42,9A$a;R+^3$n0;R+E>C!6'_WE!1'cQ#=$o;RE!3+^N+1-[RN$k0;R+[+1#8:$a;R+^3$w;R+5$v;R+E=$a;R+^3$n0;R+E>$a;R+^3$n0;R+E$k1;R+5=$lo;R+3$hi;R+3>$e;R+E$m;R+3>$e;R+E$lo;R+3$hi;R+3=$a;R+^3$n0;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E?$a;R+^3$zn;R+E$c';R+3-^3RN$a;R+^3+1#31$zb;R+E$zk;R+3-1RN$~R+1+1-1RN$~R+1+172-^;RN$x;R!1+^;+3+1!1#6#82$nh;R+3;,6,62,9B$a;R+^3$n0;R+E>C!6'_WE!1'cJ#=$o;RE!3+^N+1-[RN$k0;R+[+1#8:$a;R+^3$w;R+5$v;R+E=$a;R+^3$n0;R+E>$a;R+^3$n0;R+E$k1;R+5=$lo;R+3$hi;R+3>$e;R+E$m;R+3>$e;R+E$lo;R+3$hi;R+3=$a;R+^3$n0;R+E>$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E?$a;R+^3$zn;R+E$c';R+3-^3RN$a;R+^3+1#31$zb;R+E$zk;R+3-1RN$~R+1+1-1RN$~R+1+172-^;RN$x;R!1+^;+3+1@2$nh;R+3-^;RN$x;R!1+^;+3+1!1#7#52$zl;R+3:,6,6,62,9B$a;R+^3$n0;R+E>C!2,^H+1-[RN$k0;R+[+1#7:$a;R+^3$w;R+5$v;R+E>$a;R+^3$n0;R+EF$a;R+^3$n0;R+E$k1;R+5>$lo;R+3$hi;R+3F$e;R+E$m;R+3F$e;R+E$lo;R+3$hi;R+3>$a;R+^3$n0;R+EF$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E=$a;R+^3$zn;R+E$c';R+3-^3RN$a;R+^3+1#31$zb;R+E$zk;R+3-1RN$~R+1+1-1RN$~R+1+1!2'_8!2'_8G!2'_9#9#2!2'_:#1#82-^;RN$x;R!1+^;+3+1!2'cQ#B#72$nh;R+3-^;RN$x;R!1+^;+3+1!2'cJ#C#52$zl;R+3!2'_:!2'^U#:#29,6,6,62,9-1RN$~R+1+1!2'_8G!7'cK#B#9#8#7#2#1#42,9?$a;R+^3$n0;R+EF!1'cHH!1'cL#=!1'cPH!1'cR#=!1'cIH!1'cM#=!6'cUH#6#4#3#2#1!4#5#4#3#2#1!3+^N+1!6'cUHI#4#3#2#1!6'cV#=I#4#3#2#1#5#4#3#2#1").
Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  ranges_apart_x k b off n (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)).

Definition off_image_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!1'cW/A;$bc;R+aK$b;R+E$off;R+3$n;R+E!7'aZ#4#3#2#1!1,H,I0!1,H!2'a\!1'cX/A;0").

Lemma off_image_xB_eqf : forall fk, off_image_xB (mkbc fk) = off_image_x fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60%n;R+E+1%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1!1,H,I!1'cW/A;!1,H!2'a\!1'cX/A;3!1'aB#4$fk;R!1+2+[!5'b0+E%off;R+30!1'cY!1'aB#1!1'cZ#1$x;R+E!5'b0+30!2'cY!1'aB#2#1!2'cZ#2#1$x0;R+3!5'b0+E+1!3'cY!1'aB#3#2#1!3'cZ#3#2#1$x1;R+Evd!6'_W1!1'b3#4$b;R1!3+^N+1!6#1#4#3#2234!7'b3#5#4#3#2234!2,^H+1!7'b3#4#3#2#1234!1'aZ5!1'b4#4!3+^N+1!4'cY5#3#2#1!4'cZ#4#3#2#1").
Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flat_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match base_range k b, xlo k n, xhi k n with
  | Some (lo, hi), Some nl, Some nh => (Z.leb 0 (lo + off) && Z.leb (hi + off + nh) two64 && Z.ltb 0 nl)%bool
  | _, _, _ => false
  end.

Definition flat_xB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!2+_>+3+3$bc;R+aK$b;R+E$off;R+3$n;R+E-^;RN$x;R!1+^;0+1!2'c[#4#32$p;R0-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!2'cH#7#42$nl;R+3-^;RN$x;R!1+^;+3+1!2'cP#8#52$nh;R+3!2'_8!2'_8!2'_:,I!2'^U#4#7!2'_:!2'^U!2'^U#3#7#1'^>!2'a[,I#2,6,6,6").

Lemma flat_xB_eqf : forall fk, flat_xB (mkbc fk) = flat_x fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;0%n;R+E+1%e;R+E!1+^;+3!2+_>+3+3!2'c[!1'aB#5#4!2'a[,I#2!2'_8!2'_8!2'_:,I!2'^U#4#8!2'_:!2'^U!2'^U#3#8#1'^>4-^;RN$x;R!1+^;+3+1!2'cQ#9#62$nh;R+35,6-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!2'cJ#8#52$nl;R+36,6-^;RN$x;R!1+^;2+1!2'd1#5#42$p;R27,6%e;R+E!1+^;2!1'aB#4$fk;R!1+2+[!5'b0+E%off;R+30!1'c\!1'aB#1!1'd0#1$x;R+E!5'b0+30!2'c\!1'aB#2#1!2'd0#2#1$x0;R+3!5'b0+E+1!3'c\!1'aB#3#2#1!3'd0#3#2#1$x1;R+Evd!6'_W1!1'cQ#4$o;R1!3+^N+1-^;RN$x;R!1+^;2+132$p;R2-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!2'cH!1'aB#8#52$nl;R+3-^;RN$x;R!1+^;+3+1!1#5#62$nh;R+35,6,6,68!6'_W1!1'cJ#4$o;R1!3+^N+1-^;RN$x;R!1+^;2+132$p;R2-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!1#4#52$nl;R+36,6,68!6'_W9!1'd1#4$o;R9!3+^N+1-^;RN$x;R!1+^;2+1!1#1#42$p;R27,68!2,^H+1-^;RN$x;R!1+^;2+1!2'd1#4#32$p;R2-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!2'cJ#7#42$nl;R+3-^;RN$x;R!1+^;+3+1!2'cQ#8#52$nh;R+3!2'_8!2'_8!2'_:,I!2'^U#4#7!2'_:!2'^U!2'^U#3#7#1'^>4,6,6,6!1'c[:!1'd2#4!1'cH:!1'cL#4!1'cP:!1'cR#4!3+^N+1!4'c\:#3#2#1!4'd0#4#3#2#1").
Qed.
#[local] Hint Rewrite flat_xB_eqf : bceq.



(* [comment removed for export] *)
Definition ehi (k : list kentry) (e : expr) : option Z := xhi k e.
Definition elo (k : list kentry) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$k;R!1+2+[$e;R+E!2'cJ#2#1").

(* [comment removed for export] *)
Definition len_eqb (k : list kentry) (n m : expr) : bool :=
  expr_eqb n m || (lin_ge0 k [(n, 0%Z)] [(m, 0%Z)] && lin_ge0 k [(m, 0%Z)] [(n, 0%Z)]).

Definition len_eqbB (bc : bctx) (n m : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!2+_>+E+3!1,^00!3,_T0!4,d4+E+3#2,I1!3,_T0!4,d4+E+3#1,I1$bc;R+aK$n;R+E$m;R+E!2'_4!2'_9#2#1!2'_8!3'd3#323!3'd3#332").

Lemma len_eqbB_eqf : forall fk, len_eqbB (mkbc fk) = len_eqb fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80%pos;R'd7%neg;R'd7+1!2'_9#3#2!2+_>+E+3!1,^02!3,_T2!4,d4+E+3#3,I3!3,_T2!4,d4+E+3#2,I3!3,_T2!4,d4+E+3#1,I3!1'aB#3$fk;R!1+2+[!5'b0+E%m;R+E+1!1'd5!1'aB#1!1'd6#1$x;R+E!5'b0+E+1!2'd5!1'aB#2#1!2'd6#2#1$x0;R+Evd!6'_W0!1'd8#3$b;R0!3+^N+1!2'_41!2'_8!2#145!2#154!2'_41!2'_8!3'd8#445!3'd8#454!2,^H+1!2'_4!2'_9#2#1!2'_8!3'd8#356!3'd8#365!1'd37!1'd9#3!3+^N+1!3'd57#2#1!3'd6#3#2#1").
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

Definition page_alignedB (bc : bctx) (e : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!1,^K|34;!2'_:0!2'd:#5#4!2'_:0!2'd:#6#5$bc;R+aK$e;R+E-ERN$e;R+E+1#18$z;R+3!2'aY!2'^=#1!1,^K|<000;,I$n;R+5!2'_:0!2'd:#3#2$op;R+^?$a;R+E$b;R+E1$op;R+^?$a;R+E$b;R+E1$op;R+^@$a;R+E$b;R+E1$op;R+^@$a;R+E$b;R+E1$sx;R+1$lo;R+5$n;R+5$e0;R+E2$sx;R+1$k;R+5$i;R+3$n;R+52").

Lemma page_alignedB_eqf : forall fk, page_alignedB (mkbc fk) = page_aligned fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90%e;R+E+3!2'aY!2'^=#1!1,^K|<000;,I!1,^K|34;!2'_:2!1#4#5!2'_:2!1#5#6!2'_:2!2'd=#6#5!2'_:2!2'd=#7#6!2'_:2!2'd=#5#4!1'aB#2$fk;R!1+2+[!5'b0+E+1!1'd;!1'aB#1!1'd<#1$x;R+Evd!6'_W0!1'd=#2$z;R0!3+^N+1-ERN$e;R+E+1#28$z;R+31$n;R+5!2'_:2!1#2#3$op;R+^?$a;R+E$b;R+E3$op;R+^?$a;R+E$b;R+E3$op;R+^@$a;R+E$b;R+E3$op;R+^@$a;R+E$b;R+E3$sx;R+1$lo;R+5$n;R+5$e0;R+E4$sx;R+1$k;R+5$i;R+3$n;R+54-ERN$e;R+E+1#28$z;R+31$n;R+5!2'_:2!2'd=#4#3$op;R+^?$a;R+E$b;R+E5$op;R+^?$a;R+E$b;R+E5$op;R+^@$a;R+E$b;R+E5$op;R+^@$a;R+E$b;R+E5$sx;R+1$lo;R+5$n;R+5$e0;R+E6$sx;R+1$k0;R+5$i;R+3$n;R+56!2,^H+1-ERN$e;R+E+1#18$z;R+31$n;R+5!2'_:2!2'd=#3#2$op;R+^?$a;R+E$b;R+E7$op;R+^?$a;R+E$b;R+E7$op;R+^@$a;R+E$b;R+E7$op;R+^@$a;R+E$b;R+E7$sx;R+1$lo;R+5$n;R+5$e0;R+E5$sx;R+1$k0;R+5$i;R+3$n;R+55!1'd:8!1'd>#2!3+^N+1!2'd;8#1!2'd<#2#1").
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

Definition ret_lit (cs : acs) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S20!1+^;+3!1,^2+3$cs;R+C-ERN$x;R+E0!2'^B#1}18$r;R+3-1RN$~R+10!2'_8!2'_8!2'aY!2'^=#1!1,^K|10;,I!2'a[#1'^>!2'_:,I#12!2,^<+3#11$n;R+51$op;R+^?$a;R+E$b;R+E1$op;R+^?$a;R+E$b;R+E1$op;R+^@$a;R+E$b;R+E1$op;R+^@$a;R+E$b;R+E1$sx;R+1$lo;R+5$n;R+5$e;R+E1$sx;R+1$k;R+5$i;R+3$n;R+51").

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

Definition is_ecall_at (cs : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S40!1'd?#1|20;|500;!1+d@!1,dA2$cs;R+C!2'_8!2'_8!2'_:,I0!2'a[!2'^U0!1,^K1'^>-^;RN$x;R!1+^;3+1!2'dB/segs;!2'dC!1,dA|600;02$w;R3!1'dD#1,6").

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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SV0!1+^;+3!2+_>+3+3%e;R+E!1+^;1!2,^<+3!1'dH#1!1'aB#4!2'dI4#3!1#5#6-_>RN$p0;R!2+_>+3+30#11$lo';R+3$z0;R+3!2,^<+3!2'dJ#5#2!2,^<+3#2!1#2#3-_>RN$p;R!2+_>+3+30#11$lo';R+3$z;R+38-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+38!1,^2+3!1'aB#6!2'dI=#5!1#4#5-^;RN$x;R!1+^;10>2$p;R1-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3-^;RN$x;R!1+^;10!1#7#82$p0;R178-^;RN$x;R!1+^;10?2$p;R1:-^;RN$x;R!1+^;10!2'dK=#52$p;R1;<!1'aB#7!2'dIA#6-^;RN$x;R!1+^;10B2$p;R1-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3-^;RN$x;R!1+^;10!1#8#92$p0;R178-^;RN$x;R!1+^;1062$p;R1:-^;RN$x;R!1+^;10!2'dKA#62$p;R1;<!2'dG#7#6-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3-^;RN$x;R!1+^;10D2$p0;R178!2'dG#4#3-^;RN$x;R!1+^;10F2$p;R1:-^;RN$x;R!1+^;10!2'dM#4#32$p;R1;<-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3-^;RN$x;R!1+^;10!2'dG#9#82$p0;R178!2'dG#6#5-^;RN$x;R!1+^;10I2$p;R1:-^;RN$x;R!1+^;10!2'dM#6#52$p;R1;<-^;RN$x;R!1+^;10!2'dL#6#52$p;R1HJ-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3-^;RN$x;R!1+^;10!2'dG#:#92$p0;R178-^;RN$x;R!1+^;10D2$p;R1:-^;RN$x;R!1+^;10!2'dM#7#62$p;R1;<-^;RN$x;R!1+^;10!2'dL#7#62$p;R1LM-ERN$e;R+E0#28$z;R+33$n;R+5-^;RN$x;R!1+^;10!2'dL#4#32$p;R1EG$op;R+^?$a;R+E$b;R+EK$op;R+^?$a;R+E$b;R+EK$op;R+^@$a;R+E$b;R+EK$op;R+^@$a;R+E$b;R+EK$sx;R+1$lo;R+5$n;R+5$e0;R+EN$sx;R+1$k0;R+5$i;R+3$n;R+5N-^;RN$x;R!1+^;10>2$p;R1H-^;RN$x;R!1+^;10I2$p;R1:-^;RN$x;R!1+^;10?2$p;R1;<-^;RN$x;R!1+^;10B2$p;R1L-^;RN$x;R!1+^;10D2$p;R1:-^;RN$x;R!1+^;1062$p;R1;<-^;RN$x;R!1+^;10?2$p;R1HJ-^;RN$x;R!1+^;1062$p;R1LM-^;RN$x;R!1+^;10!2'dL#5#42$p;R1-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3-^;RN$x;R!1+^;10!2'dG#8#72$p0;R178-^;RN$x;R!1+^;10!2'dG#5#42$p;R1:-^;RN$x;R!1+^;10!2'dM#5#42$p;R1;<!1'aB#2$fk;R!1+2+[!5'b0+E0!1'dE!1'aB#1!1'dF#1$x;R+Evd!6'_W2!1'dG#2$o;R2!3+^N0-ERN$e;R+E0#28$z;R+33$n;R+5-^;RN$x;R!1+^;1052$p;R1-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3-^;RN$x;R!1+^;1062$p0;R178-^;RN$x;R!1+^;1092$p;R1:-^;RN$x;R!1+^;10!2'dK4#32$p;R1;<$op;R+^?$a;R+E$b;R+E@$op;R+^?$a;R+E$b;R+E@$op;R+^@$a;R+E$b;R+E@$op;R+^@$a;R+E$b;R+E@$sx;R+1$lo;R+5$n;R+5$e0;R+EC$sx;R+1$k;R+5$i;R+3$n;R+5CO!6'_W2!1'dM#2$o;R2!3+^N0-ERN$e;R+E0#28$z;R+33$n;R+5-^;RN$x;R!1+^;1052$p;R1E-^;RN$x;R!1+^;10F2$p;R1:-^;RN$x;R!1+^;1092$p;R1;<$op;R+^?$a;R+E$b;R+EP$op;R+^?$a;R+E$b;R+EP$op;R+^@$a;R+E$b;R+EP$op;R+^@$a;R+E$b;R+EP$sx;R+1$lo;R+5$n;R+5$e0;R+EQ$sx;R+1$k;R+5$i;R+3$n;R+5QO!6'_W2!1'dL#2$o;R2!3+^N0-ERN$e;R+E0#28$z;R+33$n;R+5-^;RN$x;R!1+^;1092$p;R1EG$op;R+^?$a;R+E$b;R+ER$op;R+^?$a;R+E$b;R+ER$op;R+^@$a;R+E$b;R+ER$op;R+^@$a;R+E$b;R+ER$sx;R+1$lo;R+5$n;R+5$e0;R+ES$sx;R+1$k;R+5$i;R+3$n;R+5SO!2,^H0-ERN$e;R+E0#18$z;R+33$n;R+5-^;RN$x;R!1+^;10!2'dL#3#22$p;R1-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3-^;RN$x;R!1+^;10I2$p0;R178-^;RN$x;R!1+^;10!2'dG#3#22$p;R1:-^;RN$x;R!1+^;10!2'dM#3#22$p;R1;<$op;R+^?$a;R+E$b;R+ET$op;R+^?$a;R+E$b;R+ET$op;R+^@$a;R+E$b;R+ET$op;R+^@$a;R+E$b;R+ET$sx;R+1$lo;R+5$n;R+5$e0;R+EK$sx;R+1$k0;R+5$i;R+3$n;R+5K!1'dIU!1'dN#2!1'dKU!1'dO#2!1'dPU!1'dQ#2!3+^N0!2'dEU#1!2'dF#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SV0!1+^;+3!2+_>+3+3%e;R+E!1+^;1!2,^<+3!1'dH#1!1'aB#4!2'dI4#3!1#5#6-_>RN$p0;R!2+_>+3+30#11$z0;R+3$hi';R+3!2,^<+3!2'dT#4#1!2,^<+3#1!1#2#3-_>RN$p;R!2+_>+3+30#11$z;R+3$hi';R+38-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+38!1,^2+3!1'aB#6!2'dI=#5!1#4#5-^;RN$x;R!1+^;10>2$p;R1-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3-^;RN$x;R!1+^;10!1#7#82$p0;R178-^;RN$x;R!1+^;10?2$p;R1:-^;RN$x;R!1+^;10!2'dK=#52$p;R1;<!1'aB#7!2'dIA#6-^;RN$x;R!1+^;10B2$p;R1-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3-^;RN$x;R!1+^;10!1#8#92$p0;R178-^;RN$x;R!1+^;1062$p;R1:-^;RN$x;R!1+^;10!2'dKA#62$p;R1;<!2'dG#7#6-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3-^;RN$x;R!1+^;10D2$p0;R178!2'dG#4#3-^;RN$x;R!1+^;10F2$p;R1:-^;RN$x;R!1+^;10!2'dM#4#32$p;R1;<-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3-^;RN$x;R!1+^;10!2'dG#9#82$p0;R178!2'dG#6#5-^;RN$x;R!1+^;10I2$p;R1:-^;RN$x;R!1+^;10!2'dM#6#52$p;R1;<-^;RN$x;R!1+^;10!2'dL#6#52$p;R1HJ-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3-^;RN$x;R!1+^;10!2'dG#:#92$p0;R178-^;RN$x;R!1+^;10D2$p;R1:-^;RN$x;R!1+^;10!2'dM#7#62$p;R1;<-^;RN$x;R!1+^;10!2'dL#7#62$p;R1LM-ERN$e;R+E0#28$z;R+33$n;R+5-^;RN$x;R!1+^;10!2'dL#4#32$p;R1EG$op;R+^?$a;R+E$b;R+EK$op;R+^?$a;R+E$b;R+EK$op;R+^@$a;R+E$b;R+EK$op;R+^@$a;R+E$b;R+EK$sx;R+1$lo;R+5$n;R+5$e0;R+EN$sx;R+1$k0;R+5$i;R+3$n;R+5N-^;RN$x;R!1+^;10>2$p;R1H-^;RN$x;R!1+^;10I2$p;R1:-^;RN$x;R!1+^;10?2$p;R1;<-^;RN$x;R!1+^;10B2$p;R1L-^;RN$x;R!1+^;10D2$p;R1:-^;RN$x;R!1+^;1062$p;R1;<-^;RN$x;R!1+^;10?2$p;R1HJ-^;RN$x;R!1+^;1062$p;R1LM-^;RN$x;R!1+^;10!2'dL#5#42$p;R1-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3-^;RN$x;R!1+^;10!2'dG#8#72$p0;R178-^;RN$x;R!1+^;10!2'dG#5#42$p;R1:-^;RN$x;R!1+^;10!2'dM#5#42$p;R1;<!1'aB#2$fk;R!1+2+[!5'b0+E0!1'dR!1'aB#1!1'dS#1$x;R+Evd!6'_W2!1'dG#2$o;R2!3+^N0-ERN$e;R+E0#28$z;R+33$n;R+5-^;RN$x;R!1+^;1052$p;R1-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3-^;RN$x;R!1+^;1062$p0;R178-^;RN$x;R!1+^;1092$p;R1:-^;RN$x;R!1+^;10!2'dK4#32$p;R1;<$op;R+^?$a;R+E$b;R+E@$op;R+^?$a;R+E$b;R+E@$op;R+^@$a;R+E$b;R+E@$op;R+^@$a;R+E$b;R+E@$sx;R+1$lo;R+5$n;R+5$e0;R+EC$sx;R+1$k;R+5$i;R+3$n;R+5CO!6'_W2!1'dM#2$o;R2!3+^N0-ERN$e;R+E0#28$z;R+33$n;R+5-^;RN$x;R!1+^;1052$p;R1E-^;RN$x;R!1+^;10F2$p;R1:-^;RN$x;R!1+^;1092$p;R1;<$op;R+^?$a;R+E$b;R+EP$op;R+^?$a;R+E$b;R+EP$op;R+^@$a;R+E$b;R+EP$op;R+^@$a;R+E$b;R+EP$sx;R+1$lo;R+5$n;R+5$e0;R+EQ$sx;R+1$k;R+5$i;R+3$n;R+5QO!6'_W2!1'dL#2$o;R2!3+^N0-ERN$e;R+E0#28$z;R+33$n;R+5-^;RN$x;R!1+^;1092$p;R1EG$op;R+^?$a;R+E$b;R+ER$op;R+^?$a;R+E$b;R+ER$op;R+^@$a;R+E$b;R+ER$op;R+^@$a;R+E$b;R+ER$sx;R+1$lo;R+5$n;R+5$e0;R+ES$sx;R+1$k;R+5$i;R+3$n;R+5SO!2,^H0-ERN$e;R+E0#18$z;R+33$n;R+5-^;RN$x;R!1+^;10!2'dL#3#22$p;R1-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3-^;RN$x;R!1+^;10I2$p0;R178-^;RN$x;R!1+^;10!2'dG#3#22$p;R1:-^;RN$x;R!1+^;10!2'dM#3#22$p;R1;<$op;R+^?$a;R+E$b;R+ET$op;R+^?$a;R+E$b;R+ET$op;R+^@$a;R+E$b;R+ET$op;R+^@$a;R+E$b;R+ET$sx;R+1$lo;R+5$n;R+5$e0;R+EK$sx;R+1$k0;R+5$i;R+3$n;R+5K!1'dIU!1'dN#2!1'dKU!1'dO#2!1'dPU!1'dQ#2!3+^N0!2'dRU#1!2'dS#2#1").
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

Definition xb2 (k : list kentry) (e : expr) : option (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2+_>+3+3!1+^;0!1,^20$k;R!1+2+[$e;R+E&plain;R-^;RN$x;R!1+^;+31!2'dF#2#12$lo;R+3-^;RN$x;R!1+^;+31!2'dS#3#22$hi;R+3!2,^<0!4,d4+3+3#2#1221-_>RN$x;R!2+_>+E+31!1'dU#21$e';R+E$s;R+3-1RN$~R+11!2'aY#1,I2#3-^;RN$x;R!1+^;+31!2'dF#5#22$lo';R+3-^;RN$x;R!1+^;+31!2'dS#6#32$hi';R+3-1RN$~R+11!2'_:#3#22-^;RN$plain;R!1+^;01#52$p;R0-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3!2,^<0!4,d4+3+3!2'dJ#2!2'a\#5#6!2'dT#1#4!2,^<0!4,d4+3+3!2'a\#2#3#1#5#4#3").

Definition xb2B (bc : bctx) (e : expr) : option (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2+_>+3+3!1+^;0!1,^20$bc;R+aK$e;R+E&plain;R-^;RN$x;R!1+^;+31!2'dE#2#12$lo;R+3-^;RN$x;R!1+^;+31!2'dR#3#22$hi;R+3!2,^<0!4,d4+3+3#2#1221-_>RN$x;R!2+_>+E+31!1'dU#21$e';R+E$s;R+3-1RN$~R+11!2'aY#1,I2#3-^;RN$x;R!1+^;+31!2'dE#5#22$lo';R+3-^;RN$x;R!1+^;+31!2'dR#6#32$hi';R+3-1RN$~R+11!2'_:#3#22-^;RN$plain;R!1+^;01#52$p;R0-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3!2,^<0!4,d4+3+3!2'dJ#2!2'a\#5#6!2'dT#1#4!2,^<0!4,d4+3+3!2'a\#2#3#1#5#4#3").

Lemma xb2B_eqf : forall fk, xb2B (mkbc fk) = xb2 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SK0!2+_>+3+3!1+^;0%e;R+E!1+^;+3!1'dU#2!2'aY#1,I!1'aB#5!1#4#5!2,^<0!4,d4+3+3#2#1!1,^20-^;RN$x;R!1+^;+31!2'dE5#42$lo;R+3-^;RN$x;R!1+^;+3162$hi;R+3788!2'_:#3#2-^;RN$x;R!1+^;+31!2'dE!1'aB#7#62$lo;R+3-^;RN$x;R!1+^;+31!1#6#72$hi;R+3788-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3!2,^<0!4,d4+3+3!2'dJ#2!2'a\#5#6!2'dT#1#4!2,^<0!4,d4+3+3!2'a\#2#3#1!1#5#6-^;RN$x;R!1+^;+31!2'dS#6#52$hi;R+378-^;RN$x;R!1+^;+31!2'dF#5#42$lo;R+3?8!2'dS#6#3-^;RN$x;R!1+^;+31!2'dS#8#72$hi;R+378-^;RN$x;R!1+^;+31!2'dF#7#62$lo;R+3B8-^;RN$x;R!1+^;+31!2'dS#7#62$hi;R+378-^;RN$x;R!1+^;+31!2'dF#6#52$lo;R+3D8-_>RN$x;R!2+_>+E+3131$e';R+E$s;R+3-1RN$~R+1142@-^;RN$x;R!1+^;+31!2'dF#5#22$lo';R+3-^;RN$x;R!1+^;+31A2$hi';R+3-1RN$~R+11:2-^;RN$plain;R!1+^;01C2$p;R0<=CE@-^;RN$x;R!1+^;+31!1#3#42$lo;R+3?8-^;RN$x;R!1+^;+31>2$lo;R+3B8-^;RN$x;R!1+^;+31!2'dF#4#32$lo;R+3-^;RN$x;R!1+^;+31!2'dS#5#42$hi;R+3788!1'aB#2$fk;R!1+2+[!5'b0+E1!1'dV!1'aB#1!1'dW#1$x;R+Evd!6'_W2!1'dS#2$o;R2!3+^N1-_>RN$x;R!2+_>+E+3131$e';R+E$s;R+3-1RN$~R+11429-^;RN$x;R!1+^;+31!2'dE5#22$lo';R+3-^;RN$x;R!1+^;+31!1#4#32$hi';R+3-1RN$~R+11:2-^;RN$plain;R!1+^;01;2$p;R0<=;-^;RN$x;R!1+^;+31!2'dE!1'aB#6#52$lo;R+3-^;RN$x;R!1+^;+31>2$hi;R+37889F!6'_W2!1'dF#2$o;R2!3+^N1-_>RN$x;R!2+_>+E+3131$e';R+E$s;R+3-1RN$~R+1142G-^;RN$x;R!1+^;+31!1#3#22$lo';R+3-^;RN$x;R!1+^;+31A2$hi';R+3-1RN$~R+11:2-^;RN$plain;R!1+^;01H2$p;R0<=H-^;RN$x;R!1+^;+3162$lo;R+3D8GF!2,^H1-_>RN$x;R!2+_>+E+31!1'dU#11$e';R+E$s;R+3-1RN$~R+1142I-^;RN$x;R!1+^;+31!2'dF#4#22$lo';R+3-^;RN$x;R!1+^;+31!2'dS#5#32$hi';R+3-1RN$~R+11:2-^;RN$plain;R!1+^;01E2$p;R0<=E@I!1'dEJ!1'dX#2!1'dRJ!1'dY#2!3+^N1!2'dVJ#1!2'dW#2#1").
Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 (k : list kentry) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+_>+3+3!1+^;+3$k;R!1+2+[$e;R+E-^;RN$x;R!1+^;01!2'dW#2#12$p;R0-_>RN$p;R!2+_>+3+31#11$lo;R+3$z;R+3!2,^<+3#2!1,^2+3").

Definition xlo2B (bc : bctx) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+_>+3+3!1+^;+3$bc;R+aK$e;R+E-^;RN$x;R!1+^;01!2'dV#2#12$p;R0-_>RN$p;R!2+_>+3+31#11$lo;R+3$z;R+3!2,^<+3#2!1,^2+3").

Lemma xlo2B_eqf : forall fk, xlo2B (mkbc fk) = xlo2 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!1+^;+3!2+_>+3+3%e;R+E!1+^;1-_>RN$p;R!2+_>+3+30#11$lo;R+3$z;R+3!2,^<+3#2!1,^2+3!1'aB#2$fk;R!1+2+[!5'b0+E0!1'dZ!1'aB#1!1'd[#1$x;R+Evd!6'_W2!1'dW#2$o;R2!3+^N0-^;RN$x;R!1+^;10!1#1#22$p;R134-^;RN$x;R!1+^;10!2'dW#3#22$p;R134!2,^H0-^;RN$x;R!1+^;10!2'dW#2#12$p;R134!1'dV5!1'd\#2!3+^N0!2'dZ5#1!2'd[#2#1").
Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 (k : list kentry) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+_>+3+3!1+^;+3$k;R!1+2+[$e;R+E-^;RN$x;R!1+^;01!2'dW#2#12$p;R0-_>RN$p;R!2+_>+3+31#11$z;R+3$hi;R+3!2,^<+3#1!1,^2+3").

Definition xhi2B (bc : bctx) (e : expr) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2+_>+3+3!1+^;+3$bc;R+aK$e;R+E-^;RN$x;R!1+^;01!2'dV#2#12$p;R0-_>RN$p;R!2+_>+3+31#11$z;R+3$hi;R+3!2,^<+3#1!1,^2+3").

Lemma xhi2B_eqf : forall fk, xhi2B (mkbc fk) = xhi2 fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!1+^;+3!2+_>+3+3%e;R+E!1+^;1-_>RN$p;R!2+_>+3+30#11$z;R+3$hi;R+3!2,^<+3#1!1,^2+3!1'aB#2$fk;R!1+2+[!5'b0+E0!1'e0!1'aB#1!1'e1#1$x;R+Evd!6'_W2!1'dW#2$o;R2!3+^N0-^;RN$x;R!1+^;10!1#1#22$p;R134-^;RN$x;R!1+^;10!2'dW#3#22$p;R134!2,^H0-^;RN$x;R!1+^;10!2'dW#2#12$p;R134!1'dV5!1'd\#2!3+^N0!2'e05#1!2'e1#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SB0!1+2+3!1+^;0%off;R+31%b;R+E2!1'aB#3!3+^N3!2'e34#1!2'e4#1#3!1,_N#2!1,_N#3}1!1,^K,_0!2'^U#39!2,^<0!3,_T+3#2#1!1,^20-^;RN$x;R!1+^;01!4'e4#6#8#4:2$rest;R0;<-^;RN$x;R!1+^;+31!4'cA#7#3#282$z;R+3=<%b;R+E%off;R+3%n;R+5!1+^;+3!1'aB#6!1,_N#4$fk;R!1+2+[$fuel;R+5!4'e2$fuel;R+55!5'b0+E2!2'e3!1'aB#2,^M!2'e4,^M#2$x;R+E!5'b0+31!3'e34,^M#1!3'e4,^M#3#1$x0;R+3!2,^H1!4'e4,^M#4#2#1$f;R+5$IH;R5!5'b0+E2!2'e3!1'aB#46!2'e46#4$x;R+E!5'b0+31!3'e3!1'aB#57#1!3'e47#5#1$x0;R+3vd!6'_W3!2'e4#4#6$o;R3!3+^N1-^;RN$x;R!1+^;+31!4'c@!1'aB#7#3#282$z;R+3-^;RN$x;R!1+^;01!2#2#4:2$rest;R0;<<>!6'_W?!1'cA#6$o;R?!3+^N1-^;RN$x;R!1+^;+31!3#1#3#282$z;R+3=<>!2,^H1-^;RN$x;R!1+^;+31!4'cA#6#2#182$z;R+3-^;RN$x;R!1+^;01!4'e4#5#7#3!2'^U#292$rest;R0;<<!1'c@@!1'e5#6!2'e3@#4#3!3+^N1!4'e3@A#2#1!4'e4A#6#2#1#1").
Qed.
Lemma kread_bytesB_eqf : forall fk, kread_bytesB (mkbc fk) = (fun fuel => kread_bytes fuel fk).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00$fk;R!1+2+[!5'b0+5%b;R+E%off;R+3!1+^;!1+2+3!1'e3!1'aB#1$fuel;R+5!2'e4#1#2$fuel;R+5!2'e6#2#1").
Qed.
#[local] Hint Rewrite kread_bytesB_eqf' kread_bytesB_eqf : bceq.


Definition node_join (cs : acs) (b : expr) (off : Z) (n : nat) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S50!1+^;+C}1!1'^9#4!1+2+3!1,^2+C$cs;R+C$b;R+E$off;R+3$n;R+5-1RN$~R+10!2'_8!2'_8!2'`U1#1!2'`U#1}8!4'd02#3#2!1,H!1'_;#12-^;RN$x;R!1+^;30!4'e4#12#3#22$bs;R3!2,^<+C!2'e7#5!3,_T+[!3,`Z!2,`F#4#3#2!1,H!1'e8#1!1,^0+[44").

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

Definition node_fresh (cs : acs) (r : nat) (logc : Z) (base : option expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S60!1+2+[|10;!1+^;+C!1'e9#8}1!1,^2+C$cs;R+C$r;R+5$logc;R+3$base;R!1+^;+E&k;R!1'^9#40&c;R!2'^V!1,^K1#3+3&b;R-^;RN$base;R!1+^;+E+E#32$b;R+E#1!1,H,I+E&e;R!2'^T!2'^B#7#6#1+E-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_5,^M#7!2'_5#7}P!2'_:,I#6!2'_:#6!1,^K|508;!2'_:#6!2'd=#4#1!2'a:3#2!2'a:3#1!1'a?#82-^;RN$x;R!1+^;+32!2'd[#4#12$lo;R+3-^;RN$x;R!1+^;+32!2'e1#5#22$hi;R+3&v;R!1'e9#:+5&ne;R!2'^R#6!1,^L#1+E&kres;R!3'e:#8#5#10&kf;R!3,_T+[!3,a3!1,^L#3!2'e;!2'a\!2'^U#5#8!1,^K,_0#8!2'e;#4#8!3,_T+[!3,a3!2'^T#6#2,I,I#10!2,^<+C!2'e<!3'e=!2'e7#>#1#=!2'^P#8#34555").

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
Definition bigb (K : nat) (e : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$K;R+5$e;R+E!2'_5#2!1'e>#1").
Fixpoint kn_bigsubst (K : nat) (k : list kentry) (nx : nat) : list kentry * nat :=
  match k with
  | [] => ([], 0%nat)
  | KWord a w v :: r =>
      if bigb K v then let '(r', c) := kn_bigsubst K r (S nx) in (KWord a w (EVar nx) :: r', S c)
      else let '(r', c) := kn_bigsubst K r nx in (KWord a w v :: r', c)
  | x :: r => let '(r', c) := kn_bigsubst K r nx in (x :: r', c)
  end.
Definition node_havocbig (cs : acs) (K : nat) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40}1!1+^;+C!1+2+[!1,^2+C$cs;R+C$K;R+5&rs;R!3'_@+5$r;R+5!2'e?#2!2'^B#3#1!2'e@0}O!1+2+5-^;RN$x;R!1+^;+C1!2'eA#3#12$cs1;R+C-1RN$~R+11!1'a?#12&nx1;R!1'e9#1+5-_>RN$x;R!2+_>2+51!3'eB#4!1'^9#2#11$k';R2$c;R+5!2,^<+C!2'^4#4!4'^5!1'd?#4!1'F!1'G#4#2!2'^:#3#133").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside k b off n (am_base m) 0 (am_len m)) ms.

Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S00$bc;R+aK$ms;R!1+2+:$kinds;R!1+2+8$b;R+E$off;R+3$n;R+E!3'eC+:$m;R+:!2'_8!2'_8!1'@!1'A#1!3'_6+8!1';!1'<#1#5!7'cI#7#4#3#2!1'`A#1,I!1'`B#1#5").

Lemma find_containingB_eqf : forall fk, find_containingB (mkbc fk) = find_containing fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S=0!1+2+:!1+2+8!1+^;+:%n;R+E2%off;R+33%b;R+E4%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1!1'@!1'A#1!1';!1'<#1!2'_87!3'_6+88#6!1'`A#1!1'`B#1!1'aB#6$fk;R!1+2+[!5'b00%kinds;R15!1'eD!1'aB#1!1'eE#1$x;R0!5'b015!2'eD!1'aB#2#1!2'eE#2#1$x0;R1!5'b0+E4!3'eD!1'aB#3#2#1!3'eE#3#2#1$x1;R+E!5'b0+33!4'eD!1'aB#4#3#2#1!4'eE#4#3#2#1$x2;R+3!5'b0+E2!5'eD!1'aB#5#4#3#2#1!5'eE#5#4#3#2#1$x3;R+Evd!6'_W6!1'cK#6$b;R6!3+^N2!3'eC+:$m;R+:!2'_89!6#2#5#4#3:,I;#6!3'eC+:$m;R+:!2'_89!7'cK#8#5#4#3:,I;#6!2,^H2!3'eC+:$m;R+:!2'_8!2'_87!3'_6+88#5!7'cK#7#4#3#2:,I;#5!1'cI<!1'cM#6!3+^N2!6'eD<#5#4#3#2#1!6'eE#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!2+_>+E+3!1,^K|11;$bc;R+aK$b;R+E$n;R+E-_>RN$x;R!2+_>+E+3!2+_>0+E!1'_2!2'^P!3'eF#3#21!1,H!1'eG/A;1$sb;R+E$sk;R+3!4,d40+E!4,d4+E+3#2#1!3'eF#5#31").

Lemma shadow_ofB_eqf : forall fk, shadow_ofB (mkbc fk) = shadow_of fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S70!2+_>+E+3!2+_>0+E%a;R+E%s;R+3+E!1,^K|11;!1,H!1'eG/A;!4,d4+E+3#2#1!1'aB#3$fk;R!1+2+[!5'b0+E%n;R+E1!1'eH!1'aB#1!1'eI#1$x;R+E!5'b0+E1!2'eH!1'aB#2#1!2'eI#2#1$x0;R+Evd!6'_W2!1'eJ#3$e;R2!3+^N1-_>RN$x;R!2+_>+E+31!1'_2!2'^P!2#1#3341$sb;R+E$sk;R+3!4,d40+E5!2#3#43-_>RN$x;R!2+_>+E+31!1'_2!2'^P!3'eJ#4#3341$sb;R+E$sk;R+3!4,d40+E5!3'eJ#6#43!2,^H1-_>RN$x;R!2+_>+E+31!1'_2!2'^P!3'eJ#3#2341$sb;R+E$sk;R+3!4,d40+E5!3'eJ#5#33!1'eF6!1'eK#3!3+^N1!3'eH6#2#1!3'eI#3#2#1").
Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_lazy_holds (m : amap) (slo shi : Z) : bool :=
  (negb (is_fog m) && mkind_eqb (am_kind m) KRWLAZY &&
   match am_base m, am_len m with
   | ELit B, ELit L => (Z.leb 0 B && Z.ltb 0 L && Z.ltb (B + L) two64 && Z.leb B slo && Z.leb shi (B + L))%bool
   | _, _ => false
   end)%bool.
Definition shadow_band (k : list kentry) (ms : list amap) (b n : expr) (sb : expr) (sk : Z) (sn : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S20!1'eG/A;!1,^K|30;$k;R!1+2+[$ms;R!1+2+:$b;R+E$n;R+E$sb;R+E$sk;R+3$sn;R+E!2'_8!4'd0#7#3#2#1-^;RN$x;R!1+^;+3+1!2'cJ#7#52$blo;R+3-^;RN$x;R!1+^;+3+1!2'cQ#8#62$bhi;R+3-^;RN$x;R!1+^;+3+1!2'cQ#9#62$nhi;R+3!3'_6+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n0;R+E,6$a;R+^3$n0;R+E$k0;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n';R+E-^3RN$a1;R+^3+1#41$a_base;R+E$a_off;R+3-ERN$a_base;R+E+1#28$lo;R+3-3RN$a_off;R+3+1#23-ERN$n1;R+E+1#68$L;R+3-^3RN$a2;R+^3+1#61$b';R+E$a_off0;R+3-3RN$a_off0;R+3+1#13!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_9#2#C!2'_9#7#B!2'_:,I#4!2'_:,I#3!2'a[!2'^U#4#3'^>!3'_6+:$m;R+:!3'eL#1!2'^U0!2'e;#?1!2'^U0!2'e;#51#D!3'_6+:$m;R+:!3'eL#1!2'^U0!2'e;!2'^U#5#41!2'^U0!2'e;!2'^U#>#=1#D$p;R+_I,6$p;R+_I,6$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo0;R+5$n0;R+5$e;R+E,6$sx;R+1$k0;R+5$i;R+3$n0;R+5,6$p;R+_I,6$p;R+_I,6$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo;R+5$n0;R+5$e;R+E,6$sx;R+1$k0;R+5$i;R+3$n0;R+5,6$a;R+^3$n0;R+E$c;R+3,6$a;R+^3$n0;R+E,6#:,6,6,6").
Definition shadow_bandB (bc : bctx) (ms : list amap) (b n : expr) (sb : expr) (sk : Z) (sn : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 7 "S20!1'eG/A;!1,^K|30;$bc;R+aK$ms;R!1+2+:$b;R+E$n;R+E$sb;R+E$sk;R+3$sn;R+E!2'_8!4'c\#7#3#2#1-^;RN$x;R!1+^;+3+1!2'cH#7#52$blo;R+3-^;RN$x;R!1+^;+3+1!2'cP#8#62$bhi;R+3-^;RN$x;R!1+^;+3+1!2'cP#9#62$nhi;R+3!3'_6+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n0;R+E,6$a;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n';R+E-^3RN$a1;R+^3+1#41$a_base;R+E$a_off;R+3-ERN$a_base;R+E+1#28$lo;R+3-3RN$a_off;R+3+1#23-ERN$n1;R+E+1#68$L;R+3-^3RN$a2;R+^3+1#61$b';R+E$a_off0;R+3-3RN$a_off0;R+3+1#13!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_9#2#C!2'_9#7#B!2'_:,I#4!2'_:,I#3!2'a[!2'^U#4#3'^>!3'_6+:$m;R+:!3'eL#1!2'^U0!2'e;#?1!2'^U0!2'e;#51#D!3'_6+:$m;R+:!3'eL#1!2'^U0!2'e;!2'^U#5#41!2'^U0!2'e;!2'^U#>#=1#D$p;R+_I,6$p;R+_I,6$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo0;R+5$n0;R+5$e;R+E,6$sx;R+1$k;R+5$i;R+3$n0;R+5,6$p;R+_I,6$p;R+_I,6$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo;R+5$n0;R+5$e;R+E,6$sx;R+1$k;R+5$i;R+3$n0;R+5,6$a;R+^3$n0;R+E$c;R+3,6$a;R+^3$n0;R+E,6!1'b=#:,6,6,6").
Lemma shadow_bandB_eqf : forall fk, shadow_bandB (mkbc fk) = shadow_band fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SI0!1+2+[!1+2+:%sn;R+E+1%sk;R+32%sb;R+E3%n;R+E4%b;R+E%off;R+3%n;R+E+1!2'cH!1'aB#8#6!2'_:,I#4!2'_:,I#3!2'a[!2'^U#4#3'^>!1'eG/A;!1,^K|30;$m;R+:!3'eL#1!2'^U;!2'e;#?<!2'^U;!2'e;#5<$m;R+:!3'eL#1!2'^U;!2'e;!2'^U#5#4<!2'^U;!2'e;!2'^U#>#=<-^3RN$a2;R+^3+1#61$b';R+E$a_off0;R+3-3RN$a_off0;R+3+1#13!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_9#2#D!2'_9#7#C89:!3'_6+:=#E!3'_6+:>#E$p;R+_I,6$p;R+_I,6$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n0;R+E,6$a;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n';R+E-^3RN$a1;R+^3+1#41$a_base;R+E$a_off;R+3-ERN$a_base;R+E+1#28$lo;R+3-3RN$a_off;R+3+1#23-ERN$n1;R+E+1#68$L;R+3?$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo0;R+5$n0;R+5$e;R+E,6$sx;R+1$k;R+5$i;R+3$n0;R+5,6$p;R+_I,6$p;R+_I,6$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo;R+5$n0;R+5$e;R+E,6$sx;R+1$k;R+5$i;R+3$n0;R+5,6$a;R+^3$n0;R+E$c;R+3,6$a;R+^3$n0;R+E,6!3'_6+[@!1'b=!1'aB#;!4'd0#8#4#3#2!2'cJ#8#6!2'cQ#9#7!2'cQ#:#7!2'_8B-^;RN$x;R!1+^;+3+1C2$blo;R+3-^;RN$x;R!1+^;+3+1D2$bhi;R+3-^;RN$x;R!1+^;+3+1E2$nhi;R+3!3'_6+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n0;R+E,6$a;R+^3$n0;R+E$k0;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n';R+E-^3RN$a1;R+^3+1#41$a_base;R+E$a_off;R+3-ERN$a_base;R+E+1#28$lo;R+3-3RN$a_off;R+3+1#23-ERN$n1;R+E+1#68$L;R+3?$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo0;R+5$n0;R+5$e;R+E,6$sx;R+1$k0;R+5$i;R+3$n0;R+5,6$p;R+_I,6$p;R+_I,6$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo;R+5$n0;R+5$e;R+E,6$sx;R+1$k0;R+5$i;R+3$n0;R+5,6$a;R+^3$n0;R+E$c;R+3,6$a;R+^3$n0;R+E,6#;,6,6,6%e;R+E!1+^;+3!1'aB#7$fk;R0!5'b01%b;R+E5!1'eM!1'aB#1!1'eN#1$x;R1!5'b0+E5!2'eM!1'aB#2#1!2'eN#2#1$x0;R+E!5'b0+E4!3'eM!1'aB#3#2#1!3'eN#3#2#1$x1;R+E!5'b0+E3!4'eM!1'aB#4#3#2#1!4'eN#4#3#2#1$x2;R+E!5'b0+32!5'eM!1'aB#5#4#3#2#1!5'eN#5#4#3#2#1$x3;R+3!5'b0+E+1!6'eM!1'aB#6#5#4#3#2#1!6'eN#6#5#4#3#2#1$x4;R+Evd!6'_W6!1'd0#7$b;R6!3+^N+1!2'_8!3#1#4#3#2-^;RN$x;R!1+^;+3+172$blo;R+3-^;RN$x;R!1+^;+3+1!2'cP!1'aB#9#72$bhi;R+3-^;RN$x;R!1+^;+3+1!2'cP!1'aB#:#72$nhi;R+3A,6,6,6F!6'_WG!1'cQ#7$o;RG!3+^N+1!2'_8B-^;RN$x;R!1+^;+3+172$blo;R+3-^;RN$x;R!1+^;+3+1!1#2#72$bhi;R+3-^;RN$x;R!1+^;+3+1!1#3#72$nhi;R+3A,6,6,6F!6'_WG!1'cJ#7$o;RG!3+^N+1!2'_8B-^;RN$x;R!1+^;+3+1!1#1#62$blo;R+3-^;RN$x;R!1+^;+3+1D2$bhi;R+3-^;RN$x;R!1+^;+3+1E2$nhi;R+3A,6,6,6F!6'_W0#7$l;R0!3+^N+1!2'_8B-^;RN$x;R!1+^;+3+1C2$blo;R+3-^;RN$x;R!1+^;+3+1D2$bhi;R+3-^;RN$x;R!1+^;+3+1E2$nhi;R+3!3'_6+[@#4,6,6,6F!2,^H+1!2'_8!4'd0#7#3#2#1-^;RN$x;R!1+^;+3+1!2'cJ#7#52$blo;R+3-^;RN$x;R!1+^;+3+1!2'cQ#8#62$bhi;R+3-^;RN$x;R!1+^;+3+1!2'cQ#9#62$nhi;R+3!3'_6+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E,6$a;R+^3$n0;R+E,6$a;R+^3$n0;R+E$k0;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n';R+E-^3RN$a1;R+^3+1#41$a_base;R+E$a_off;R+3-ERN$a_base;R+E+1#28$lo;R+3-3RN$a_off;R+3+1#23-ERN$n1;R+E+1#68$L;R+3-^3RN$a2;R+^3+1#61$b';R+E$a_off0;R+3-3RN$a_off0;R+3+1#13!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_9#2#C!2'_9#7#B89:!3'_6+:=#D!3'_6+:>#D$p;R+_I,6$p;R+_I,6$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo0;R+5$n0;R+5$e;R+E,6$sx;R+1$k0;R+5$i;R+3$n0;R+5,6$p;R+_I,6$p;R+_I,6$n0;R+5,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^?$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$op;R+^@$a;R+E$b0;R+E,6$sx;R+1$lo;R+5$n0;R+5$e;R+E,6$sx;R+1$k0;R+5$i;R+3$n0;R+5,6$a;R+^3$n0;R+E$c;R+3,6$a;R+^3$n0;R+E,6#:,6,6,6!1'b=H!1'bA#7!1'cHH!1'cL#7!1'cPH!1'cR#7!1'c\H!1'eO#7!3+^N+1!7'eMH#6#5#4#3#2#1!7'eN#7#6#5#4#3#2#1").
Qed.
#[local] Hint Rewrite shadow_bandB_eqf : bceq.

Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S40!1+2+[!2+_>+E+3!2,`F#2#1!1,^0+[$k;R0$ms;R!1+2+:$b;R+E$n;R+E-_>RN$x;R!2+_>1+E0!3'eI#4#2#11$p;R1$sn;R+E-_>RN$p;R!2+_>+E+30#21$sb;R+E$sk;R+3-1RN$~R+10!2'_4-^;RN$x;R!1+^;+:+1!6'eE#8#7!3,_T+8,eP!1,^0+8#2#1#32$a;R+:,9,6!7'eN#8#7#6#5#2#1#32!3,_T+[!2,a42#3!3,_T+[!2,`[2#333").

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S40!2+_>+E+3!1+2+[!2,`F#2#1!1,^0+[$bc;R+aK$ms;R!1+2+:$b;R+E$n;R+E-_>RN$x;R!2+_>0+E1!3'eH#4#2#11$p;R0$sn;R+E-_>RN$p;R!2+_>+E+31#21$sb;R+E$sk;R+3-1RN$~R+11!2'_4-^;RN$x;R!1+^;+:+1!6'eD#8#7!3,_T+8,eP!1,^0+8#2#1#32$a;R+:,9,6!7'eM#8#7#6#5#2#1#32!3,_T+[!2,a42#3!3,_T+[!2,`[2#333").

Lemma shadow_factsB_eqf : forall fk, shadow_factsB (mkbc fk) = shadow_facts fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S@0!1+2+[!1+2+:%n;R+E0%ms;R1%b;R+E%n;R+E%sb;R+E%sk;R+3%sn;R+E+1!2+_>+E+3!3,_T+8,eP!1,^0+8-^;RN$x;R!1+^;+:+1!6'eD!1'aB#9#85#2#1#32$a;R+:,9,6!2,`F#2#1!1,^0+[!3,_T+[!2,a47#3!3,_T+[!2,`[7#38!3'eI#5#3#2!7'eN#9#8#7#6#2#1#3-_>RN$x;R!2+_>4+E0:1$p;R4$sn;R+E-_>RN$p;R!2+_>+E+30#21$sb;R+E$sk;R+3-1RN$~R+10!2'_4-^;RN$x;R!1+^;+:+1!6'eE#9#85#2#1#32$a;R+:,9,6;298%b;R+E%n;R+E!2+_>4+E%ms;R1%kinds;R!1+2+8%b;R+E%off;R+3%n;R+E!1+^;+:!1'aB#4$fk;R0!5'b01%b;R+E2!1'eQ!1'aB#1!1'eR#1$x;R1!5'b0+E2!2'eQ!1'aB#2#1!2'eR#2#1$x0;R+E!5'b0+E0!3'eQ!1'aB#3#2#1!3'eR#3#2#1$x1;R+Evd!6'_W3!1'eN#4$b;R3!3+^N0-_>RN$x;R!2+_>4+E0!3'eH!1'aB#5#3#21$p;R4$sn;R+E-_>RN$p;R!2+_>+E+30#21$sb;R+E$sk;R+3-1RN$~R+10!2'_46!6#5#8#7#6#2#1#3298<!6'_W=!1'eI#4$p;R=!3+^N0-_>RN$x;R!2+_>4+E0!2#1#3#21$p;R4$sn;R+E-_>RN$p;R!2+_>+E+30#21$sb;R+E$sk;R+3-1RN$~R+10!2'_46;298<!6'_W>!1'eE#4$o;R>!3+^N0-_>RN$x;R!2+_>4+E0:1$p;R4$sn;R+E-_>RN$p;R!2+_>+E+30#21$sb;R+E$sk;R+3-1RN$~R+10!2'_4-^;RN$x;R!1+^;+:+1!5#5#85#2#1#32$a;R+:,9,6;298<!2,^H0-_>RN$x;R!2+_>4+E0!3'eI#4#2#11$p;R4$sn;R+E-_>RN$p;R!2+_>+E+30#21$sb;R+E$sk;R+3-1RN$~R+10!2'_4-^;RN$x;R!1+^;+:+1!6'eE#8#75#2#1#32$a;R+:,9,6!7'eN#8#7#6#5#2#1#3298!1'eD?!1'eS#4!1'eH?!1'eT#4!1'eM?!1'eU#4!3+^N0!4'eQ?#3#2#1!4'eR#4#3#2#1").
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
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs))
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
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : forall cs b n k, vis_add cs b n k = vis_add_ref cs b n k.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_10!1+2+[%e;R+E+3!1'^9#4!1+^;+C!1'_2#4!2+_>+E+3!1'^9#7!3'eH!1'aB6#6#5!1'^9#;!1'aB8!2'cP9#9!1,^K|11;!1'^9#<!1'aB<!1'e9#<!2'a:>#;!2'a:>#:!2+_>+E+E!1'_2!3'`?+E+E#1!1'^9#?!1'aBC!3'`@+E+E#3!4'c\D#2#1E!7'aZD#:#9#=#2#1E!7'aZD#6#5#7#2#1E!1'S#<!1'T#<!1'R#<!1'U#<!1'eV#1!2'_:!2'^U!2'^UKLM/LIMIT;!1'd?#<!1'F!1'G#<!1'O#<!1'P#<!1'Q#<!3,_TA!4,d4+E+E#;#:I!2'^ULM!1'V#<!1'W#<!1'X#<!1'Y#<!1'Z#<!2,^<+C!=,N!4'^5OP!3'^8+[!4'eQ=Q#;#:#9>QRSKTJUVWXYZ!1,^2+C!3'eI6#6#5!2'_8!2'_:;!2'd=<#;!2'_:;!2'd=<#:!2'_8!2'_8!2'_8^1!4'd0<#7#6#:?@!4'd0C#2#1E!7'b3C#6#5#7#2#1E!2'_8!2'_8!2'_8^2!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8!2'_8^3!7'b3C#:#9#=#2#1E^4I!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8^3^4JN-1RN$~R+13^52!2,^<+C!=,N!4'^5OP!3'^8+[!4'eR<Q#;#:#9>QRSKTJUVWXYZ\-_>RN$x;R!2+_>+E+3341$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E3^01$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33!2'cQ8#92$nhi;R+3^6\%b;R+E%off;R+3%n;R+E+1!3#;#2#1E%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1!6#;#6#5#7#2#1E%ms;R!1+2+:%b;R+E%n;R+E0%b;R+E%n;R+E!2+_>5+E%e;R+E!1+^;+3!1'_2#3!1'^9#6!1'^9#:!1'e9#;!2'a:^B#:!2'a:^B#9!1'^9#>!4'd0^E#2#1E!7'b3^E#6#5#7#2#1E!1'S#;!1'T#;!1'R#;!1'U#;!2'_:!2'^U!2'^U^J^KM/LIMIT;!1'd?#;!1'F!1'G#;!1'O#;!1'P#;!1'Q#;!3,_TA!4,d4+E+E#:#9^H!2'^U^KM!1'V#;!1'W#;!1'X#;!1'Y#;!1'Z#;-_>RN$x;R!2+_>+E+33^?1$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E3!3'eI^@#5#41$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33!2'cQ^A#82$nhi;R+3-1RN$~R+13!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_:;!2'd=8#:!2'_:;!2'd=8#9!4'd08#7#6#9^C^D!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8!2'_8^F!7'b3^E#:#9#<#2#1E^G^H!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8^F^G^I^L2!2,^<+C!=,N!4'^5^M^N!3'^8+[!4'eR8^O#:#9#8^B^O^P^Q^J^R^I^S^T^U^V^W^X\\!1'aB2!1'aB^E!4'c\^[#2#1E!7'aZ^[#6#5#7#2#1E$cs;R+C$b;R+E$n;R+E$k;R0vdvd!6'_W1!1'd=2$z;R1!3+^N3-_>RN$x;R!2+_>+E+3341$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E371$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33:2$nhi;R+3-1RN$~R+13!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_:;!1#8#;!2'_:;!1#8#:!4'c\=#7#6#:?@!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8!2'_8FGHI!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8FHJN2[\\^7!6'_W^8!1'd02$b;R^8!3+^N3-_>RN$x;R!2+_>+E+3341$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E371$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33:2$nhi;R+3-1RN$~R+13!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8^1!3#8#7#6#:?@!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8!2'_8^9GHI!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8^9HJN2[\\^7!6'_W^:!1'b32$b;R^:!3+^N3-_>RN$x;R!2+_>+E+3341$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E371$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33:2$nhi;R+3-1RN$~R+13!2'_8!2'_8!2'_8^2!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8!2'_8^3!6#;#:#9#=#2#1E^;I!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8^3^;JN2[\\^7!6'_W^<!1'eR2$l;R^<!3+^N3-_>RN$x;R!2+_>+E+3341$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E371$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33:2$nhi;R+3-1RN$~R+13^52!2,^<+C!=,N!4'^5OP!3'^8+[!3#8Q#;#:#9>QRSKTJUVWXYZ\\^7!6'_W^=!1'eI2$p;R^=!3+^N3-_>RN$x;R!2+_>+E+3341$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E3!2#3#6#51$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33:2$nhi;R+3^6\^7!6'_W^>!1'cQ2$o;R^>!3+^N3-_>RN$x;R!2+_>+E+3341$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E3^01$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33!1#7#92$nhi;R+3^6\^7!2,^H3^Y!1'cP^Z!1'cR2!1'eH^Z!1'eT2!1'eQ^Z!1'eW2!1'aZ^Z!1'b42!1'c\^Z!1'eO2!1'd:^Z!1'd>2!3+^N3-_>RN$x;R!2+_>+E+33^?1$bb;R+E$bk;R+3-_>RN$x;R!2+_>5+E3!3'eH!1'aB^@#5#41$p;R5$sn;R+E-_>RN$p;R!2+_>+E+33#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33!2'cP!1'aB^A#82$nhi;R+3-1RN$~R+13!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_:;!2'd:9#:!2'_:;!2'd:9#9!4'c\9#7#6#9^C^D!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8!2'_8^\!7'aZ^[#:#9#<#2#1E_0^H!3'?A$p;RA-_>RN$x;R!2+_>+E+3+1B1$pb;R+E$pk;R+3!2'_8^\_0^I^L2!2,^<+C!=,N!4'^5^M^N!3'^8+[!4'eQ9^O#:#9#8^B^O^P^Q^J^R^I^S^T^U^V^W^X\\^Y!3+^N3!4'eX#4#3#2#1!4'eY#4#3#2#1").
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
(* [comment removed for export] *)
Definition scaled_var (e : expr) : option (Z * nat) :=
  match e with
  | EMd M_MUL (ELit c) (EVar v) => if (Z.ltb 0 c && Z.ltb c two64)%bool then Some (c, v) else None
  | EVar v => Some (1, v)
  | _ => None
  end.
Definition zcdiv' (a b : Z) : Z := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$a;R+3$b;R+3!1'eZ!2'e;!1'eZ#2#1").
Definition disj_var_fact (k : list kentry) (cA : expr) (oA : Z) (nA : expr) (cB : expr) (oB : Z) : list kentry :=
  match cA, nA, scaled_var cB with
  | ELit a, ELit na, Some (c, v) =>
      (* [comment removed for export] *)
      match xhi k (EVar v) with
      | Some vhi =>
          let lo := zcdiv' (a + oA + na - oB) c in
          if (Z.leb 0 a && Z.ltb a two64 && Z.leb 0 na && Z.ltb na two64 && Z.leb 0 lo && Z.leb lo vhi
              && Z.ltb (c * vhi) two64)%bool
          then [KRange (EVar v) lo vhi] else []
      | None => []
      end
  | _, _, _ =>
      match scaled_var cA, cB with
      | Some (c, v), ELit b =>
          (* [comment removed for export] *)
          match xlo k (EVar v), xhi k (EVar v), xlo2 k nA with
          | Some vlo, Some vhi, Some nlo =>
              let hi := (b + oB - oA - nlo) / c in
              if (Z.leb 0 b && Z.ltb b two64 && Z.leb 0 nlo && Z.leb 0 vlo && Z.leb vlo hi && Z.leb hi vhi
                  && Z.ltb (c * vhi) two64)%bool
              then [KRange (EVar v) vlo hi] else []
          | _, _, _ => []
          end
      | _, _ => []
      end
  end.

Definition node_casedisj (cs : acs) (b1 b2 : expr) : option (acs * acs) := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S80!2+_>+E+3!2+_>0+E!2+_>1+E!2+_>2+3!2+_>3+E!2+_>+C+C!1+^;5!1,^25$cs;R+C$b1;R+E$b2;R+E&k;R!1'^9#3!1+2+[-^;RN$x;R!1+^;46!3'e[#1#3#22$p;R4-_>RN$p;R!2+_>3+E6#11$p0;R3$n2;R+E-_>RN$p0;R!2+_>2+36#21$p1;R2$o2;R+3-_>RN$p1;R!2+_>1+E6#21$p2;R1$c2;R+E-_>RN$p2;R!2+_>0+E6#21$p3;R0$n1;R+E-_>RN$p3;R!2+_>+E+36#21$c1;R+E$o1;R+3-1RN$x;R+16!4'd0#<#2#1#32-1RN$x;R+16!4'd0#<#5#7#92-^;RN$x;R!1+^;+[6!6'e\#<#2#1#3#5#72$K1;R+[-^;RN$x;R!1+^;+[6!6'e\#=#6#8#:#3#22$K2;R+[!2,^<5!4,d4+C+C!2'e7#A!3,_T+[#2!6'f0#>#4#3#5#7#9!2'e7#A!3,_T+[#1!6'f0#>#7#9#;#4#377777").

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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^00%e;R+E+3!1'^9#5!1+^;+C!1'_2#5!2+_>+E+3!1'^9#:!3'eH!1'aB5#9#8!1'^9#>!3'eH!1'aB7#;#:!1,^K|11;!1#=#A!1'^9#B!1'aB;!1'^9#C!1'aB=!1'^9#D!1'aB?!1'^9#E|10;!2'^V!1,^KB!1,^K|50f;!2'_8!2'_:!2'^U#4#3C!2'_:!2'^U#2#1C-^;RN$x;R!1+^;+3+1!2'cP<#A2$h1;R+3-^;RN$x;R!1+^;+3+1!2'cP>#A2$m1;R+3-^;RN$x;R!1+^;+3+1!2'cP@#A2$h2;R+3-^;RN$x;R!1+^;+3+1!2'cP!1'aBA#A2$m2;R+3D,6,6,6,6!7'aZ<#<#;#@#:#9#>!3,_T+[!4,a5!2,`F#6#5#7!2,`F#2#1#3!1,^0+[!2,^<+C!2'e7#BG!1,^2+C!3'eI5#9#8!3'eI7#;#:!2'_8!2'_8!2'_8!2'_:9!2'd=;#A!2'_:9!2'd=;#@!2'_:9!2'd=;#?!2'_:9!2'd=;#>!2'_8!2'_8!2'_8!2'_8L!4'd0;#<#;#@!4'd0;#:#9#>!4'd0;#6#5#7!4'd0;#2#1#3!7'b3;#<#;#@#:#9#>-_>RN$x;R!2+_>+E+3231$c1;R+E$o1;R+3-_>RN$x;R!2+_>+E+3231$c2;R+E$o2;R+3-_>RN$x;R!2+_>4+E2J1$p;R4$sn1;R+E-_>RN$p;R!2+_>+E+32#21$sb1;R+E$sk1;R+3-_>RN$x;R!2+_>4+E2K1$p;R4$sn2;R+E-_>RN$p;R!2+_>+E+32#21$sb2;R+E$sk2;R+3-1RN$~R+12!2'_8!2'_8M-^;RN$x;R!1+^;+3+1!2'cQ;#A2$h1;R+3-^;RN$x;R!1+^;+3+1!2'cQ=#A2$m1;R+3-^;RN$x;R!1+^;+3+1!2'cQ?#A2$h2;R+3-^;RN$x;R!1+^;+3+1!2'cQA#A2$m2;R+3D,6,6,6,6N2HI%b;R+E%off;R+3%n;R+E+1%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1!2'_8ME%b;R+E%n;R+E!2+_>4+E%e;R+E!1+^;+3!1'_2#4!1'^9#9!1'^9#=!1'^9#A!2,^<+C!2'e7#AG-_>RN$x;R!2+_>+E+32U1$c1;R+E$o1;R+3-_>RN$x;R!2+_>+E+32U1$c2;R+E$o2;R+3-_>RN$x;R!2+_>4+E2!3'eIV#8#71$p;R4$sn1;R+E-_>RN$p;R!2+_>+E+32#21$sb1;R+E$sk1;R+3-_>RN$x;R!2+_>4+E2!3'eIW#:#91$p;R4$sn2;R+E-_>RN$p;R!2+_>+E+32#21$sb2;R+E$sk2;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_:9!2'd=X#@!2'_:9!2'd=X#?!2'_:9!2'd=X#>!2'_:9!2'd=X#=!4'd0X#<#;#?!4'd0X#:#9#=!4'd0X#6#5#7!4'd0X#2#1#3-^;RN$x;R!1+^;+3+1!2'cQX#@2$h1;R+3-^;RN$x;R!1+^;+3+1!2'cQ;#@2$m1;R+3-^;RN$x;R!1+^;+3+1!2'cQ=#@2$h2;R+3-^;RN$x;R!1+^;+3+1!2'cQ?#@2$m2;R+3D,6,6,6,6!7'b3X#<#;#?#:#9#=2YI!1'aB1!1'aBX$cs;R+C$b1;R+E$n1;R+E$b2;R+E$n2;R+Evdvd!6'_W0!1'd=1$z;R0!3+^N2-_>RN$x;R!2+_>+E+3231$c1;R+E$o1;R+3-_>RN$x;R!2+_>+E+3231$c2;R+E$o2;R+3-_>RN$x;R!2+_>4+E261$p;R4$sn1;R+E-_>RN$p;R!2+_>+E+32#21$sb1;R+E$sk1;R+3-_>RN$x;R!2+_>4+E281$p;R4$sn2;R+E-_>RN$p;R!2+_>+E+32#21$sb2;R+E$sk2;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_:9:!2'_:9!1#=#@!2'_:9!1#=#?!2'_:9!1#=#>!4'c\<#<#;#@!4'c\<#:#9#>!4'c\<#6#5#7!4'c\<#2#1#3EF2HIO!6'_WP!1'd01$b;RP!3+^N2-_>RN$x;R!2+_>+E+3231$c1;R+E$o1;R+3-_>RN$x;R!2+_>+E+3231$c2;R+E$o2;R+3-_>RN$x;R!2+_>4+E261$p;R4$sn1;R+E-_>RN$p;R!2+_>+E+32#21$sb1;R+E$sk1;R+3-_>RN$x;R!2+_>4+E281$p;R4$sn2;R+E-_>RN$p;R!2+_>+E+32#21$sb2;R+E$sk2;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8L!3#=#<#;#@!3#=#:#9#>!3#=#6#5#7!3#=#2#1#3EF2HIO!6'_WQ!1'b31$b;RQ!3+^N2-_>RN$x;R!2+_>+E+3231$c1;R+E$o1;R+3-_>RN$x;R!2+_>+E+3231$c2;R+E$o2;R+3-_>RN$x;R!2+_>4+E261$p;R4$sn1;R+E-_>RN$p;R!2+_>+E+32#21$sb1;R+E$sk1;R+3-_>RN$x;R!2+_>4+E281$p;R4$sn2;R+E-_>RN$p;R!2+_>+E+32#21$sb2;R+E$sk2;R+3-1RN$~R+12!2'_8R!6#=#<#;#@#:#9#>2HIO!6'_WS!1'eI1$p;RS!3+^N2-_>RN$x;R!2+_>+E+3231$c1;R+E$o1;R+3-_>RN$x;R!2+_>+E+3231$c2;R+E$o2;R+3-_>RN$x;R!2+_>4+E2!2#5#9#81$p;R4$sn1;R+E-_>RN$p;R!2+_>+E+32#21$sb1;R+E$sk1;R+3-_>RN$x;R!2+_>4+E2!2#9#;#:1$p;R4$sn2;R+E-_>RN$p;R!2+_>+E+32#21$sb2;R+E$sk2;R+3-1RN$~R+12!2'_8RN2HIO!6'_WT!1'cQ1$o;RT!3+^N2-_>RN$x;R!2+_>+E+3231$c1;R+E$o1;R+3-_>RN$x;R!2+_>+E+3231$c2;R+E$o2;R+3-_>RN$x;R!2+_>4+E2J1$p;R4$sn1;R+E-_>RN$p;R!2+_>+E+32#21$sb1;R+E$sk1;R+3-_>RN$x;R!2+_>4+E2K1$p;R4$sn2;R+E-_>RN$p;R!2+_>+E+32#21$sb2;R+E$sk2;R+3-1RN$~R+12!2'_8!2'_8M-^;RN$x;R!1+^;+3+1:2$h1;R+3-^;RN$x;R!1+^;+3+1!1#>#A2$m1;R+3-^;RN$x;R!1+^;+3+1!1#?#A2$h2;R+3-^;RN$x;R!1+^;+3+1!1#@#A2$m2;R+3D,6,6,6,6N2HIO!2,^H2Z!1'cP[!1'cR1!1'eH[!1'eT1!1'aZ[!1'b41!1'c\[!1'eO1!1'd:[!1'd>1!3+^N2-_>RN$x;R!2+_>+E+32U1$c1;R+E$o1;R+3-_>RN$x;R!2+_>+E+32U1$c2;R+E$o2;R+3-_>RN$x;R!2+_>4+E2!3'eH!1'aBV#8#71$p;R4$sn1;R+E-_>RN$p;R!2+_>+E+32#21$sb1;R+E$sk1;R+3-_>RN$x;R!2+_>4+E2!3'eH!1'aBW#:#91$p;R4$sn2;R+E-_>RN$p;R!2+_>+E+32#21$sb2;R+E$sk2;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_:9!2'd:\#@!2'_:9!2'd:\#?!2'_:9!2'd:\#>!2'_:9!2'd:\#=!4'c\\#<#;#?!4'c\\#:#9#=!4'c\\#6#5#7!4'c\\#2#1#3-^;RN$x;R!1+^;+3+1!2'cP\#@2$h1;R+3-^;RN$x;R!1+^;+3+1!2'cP<#@2$m1;R+3-^;RN$x;R!1+^;+3+1!2'cP>#@2$h2;R+3-^;RN$x;R!1+^;+3+1!2'cP@#@2$m2;R+3D,6,6,6,6!7'aZ\#<#;#?#:#9#=2YIZ!3+^N2!5'f1#5#4#3#2#1!5'f2#5#4#3#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SP0%e;R+E+3!1'^9#1!2+_>+E+3!2+_>2+3!1+^;3};!2'f3#25!1'f4#1!1,^23-1RN$~R+14!2'a[,I#12!2,^<3!4,d42+3!4,d4+E+3!1,H7778!1'^9#2!1'aB:!2'^B#25!2'cH;<!1'^9#3!1'aB>!2'^B#35!2'a[,I#2!1,^K|34;!2'^B#45|10;!2'_:#1!2'^V!1,^KD!1,^K|50e;!2,^<3!4,d42+3!4,d4+E+3C#2#1-1RN$~R+14!2'_8!2'_8A!2'_:B!2'd=!1'^9#4CE2F8-^;RN$x;R!1+^;+34!2'cQ>@2$hi;R+3G8-^;RN$x;R!1+^;+3462$len;R+39-^;RN$x;R!1+^;+34!2'cJ:<2$lo;R+3H8%e;R+E!1+^;+3!2'f3#15!2'^B#15!2,^<3!4,d42+3!4,d4+E+3@#2#1-^;RN$x;R!1+^;+34K2$len;R+39-^;RN$x;R!1+^;+34!2'cJ1L2$lo;R+3-^;RN$x;R!1+^;+34!2'cQ:<2$hi;R+3-1RN$~R+14!2'_8!2'_8A!2'_:B!2'd=>@E2M888!1'aB1$cs;R+Cvdvd!6'_W0!1'd=1$z;R0!3+^N4-^;RN$x;R!1+^;+3462$len;R+39-^;RN$x;R!1+^;+34=2$lo;R+3-^;RN$x;R!1+^;+34!2'cP?@2$hi;R+3-1RN$~R+14!2'_8!2'_8A!2'_:B!1#3CE2F888I!6'_WJ!1'cQ1$o;RJ!3+^N4-^;RN$x;R!1+^;+3462$len;R+39-^;RN$x;R!1+^;+34=2$lo;R+3-^;RN$x;R!1+^;+34!1#2@2$hi;R+3G88I!6'_WJ!1'cJ1$o;RJ!3+^N4-^;RN$x;R!1+^;+3462$len;R+39-^;RN$x;R!1+^;+34!1#1<2$lo;R+3H8I!2,^H4N!1'cHO!1'cL1!1'cPO!1'cR1!1'd:O!1'd>1!3+^N4-^;RN$x;R!1+^;+34K2$len;R+39-^;RN$x;R!1+^;+34!2'cHOL2$lo;R+3-^;RN$x;R!1+^;+34!2'cP;<2$hi;R+3-1RN$~R+14!2'_8!2'_8A!2'_:B!2'd:?@E2M888N!3+^N4!1'f5#1!1'f6#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S<0!1+2+:%len;R+E+1%off;R+31!5'f8#;#5#3#2#1!1'@!1'A#7!1'`A#7!1'`B#7!5'f8#<#6#4#3#2!2'_4!2'_84!7'cK#<#4#3#25,I67%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1!1'aB#;!3,_T+:#6#5$fk;R!1+2+[!5'b00%b;R+E2!1'f7!1'aB#1!1'f8#1$ms;R0!5'b0+E2!2'f7!1'aB#2#1!2'f8#2#1$b;R+E!5'b0+31!3'f7!1'aB#3#2#1!3'f8#3#2#1$off;R+3!5'b0+E+1!4'f7!1'aB#4#3#2#1!4'f8#4#3#2#1$len;R+E!8'`;+:$ms;R0%b;R+E%off;R+3%len;R+E!3+^N+1!5'f7!1'aB#9#4#3#2#1!5'f8#9#4#3#2#1$b;R+E$off;R+3$len;R+E!2,^H+1!5'f8#8!1,^0+:#3#2#1$m;R+:$rest;R0$IH;R%b;R+E%off;R+3%len;R+E!3+^N+1!5'f7!1'aB#:#4#3#2#1!5'f8#:#4#3#2#1$b;R+E$off;R+3$len;R+Evd!6'_W+13$b;R+1!3+^N+1!2'_4!2'_84!7'cI!1'aB#<#4#3#25,I6#18!6'_W9!1'cK#;$b;R9!3+^N+1!2'_4!2'_84!6#1#4#3#25,I678!2,^H+1!2'_4!2'_8!1'@!1'A#6!7'cK#;#3#2#1!1'`A#6,I!1'`B#63!1'cI:!1'cM#;!5'f7:#5#3#2#1!3#4#3#2#1!3+^N+1!5'f7:;#3#2#1!5'f8#;;#3#2#1#4#3#2#1").
Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint lit_ivs (ms : list amap) : list (Z * Z) :=
  match ms with
  | [] => []
  | m :: r => if is_fog m then lit_ivs r else
              match am_base m, am_len m with
              | ELit a, ELit n =>      (* [comment removed for export] *)
                  if (Z.leb 0 a && Z.ltb 0 n && Z.ltb (a + n) two64)%bool then (a, n) :: lit_ivs r else lit_ivs r
              | _, _ => lit_ivs r
              end
  end.
Fixpoint iv_insert (p : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => [p]
  | q :: r => if Z.leb (fst p) (fst q) then p :: l else q :: iv_insert p r
  end.
Fixpoint iv_sort (l : list (Z * Z)) : list (Z * Z) :=
  match l with [] => [] | p :: r => iv_insert p (iv_sort r) end.
(* [comment removed for export] *)
Fixpoint iv_coalesce (l : list (Z * Z)) : list (Z * Z * nat) :=
  match l with
  | [] => []
  | (a, n) :: r => match iv_coalesce r with
                   | (b, m, k) :: r' => if (Z.eqb (a + n) b && Z.ltb 0 n && Z.ltb 0 m)%bool then (a, n + m, S k) :: r'
                                        else (a, n, 1%nat) :: (b, m, k) :: r'
                   | [] => [(a, n, 1%nat)]
                   end
  end.
(* [comment removed for export] *)
Definition inside_runs (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match base_range k b, xhi k len with
  | Some (lo, hi), Some lh =>
      existsb (fun t : Z * Z * nat => let '(a, n, _) := t in (Z.leb a (lo + off) && Z.leb (hi + off + lh) (a + n))%bool)
              (iv_coalesce (iv_sort (lit_ivs ms)))
  | _, _ => false
  end.
Definition inside_runsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!2+_>+3+3!2+_>0+5$bc;R+aK$ms;R!1+2+:$b;R+E$off;R+3$len;R+E-^;RN$x;R!1+^;0+1!2'c[#5#32$p;R0-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!2'cP#8#42$lh;R+3!3'_61$t;R1-_>RN$t;R!2+_>0+5+1#11$p;R0$n0;R+5-_>RN$p;R!2+_>+3+3+1#21$a;R+3$n;R+3!2'_8!2'_:#2!2'^U#8#;!2'_:!2'^U!2'^U#7#;#6!2'^U#2#1!1'f9!1'f:!1'f;#8,6,6").
Lemma inside_runsB_eqf : forall fk, inside_runsB (mkbc fk) = inside_runs fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S<0!1+2+:%len;R+E+1%off;R+31%e;R+E!1+^;+3!2+_>+3+3!2+_>4+5!2'^U#2#1!3'_65$t;R5-_>RN$t;R!2+_>4+5+1#11$p;R4$n0;R+5-_>RN$p;R!2+_>+3+3+1#21$a;R+3$n;R+3!2'_8!2'_:#2!2'^U#8#<!2'_:!2'^U!2'^U#7#<#66!1'f9!1'f:!1'f;#9-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!2'cQ#9#52$lh;R+37,6-^;RN$x;R!1+^;4+1!2'd1#6#42$p;R48,6%e;R+E!1+^;4!1'aB#5$fk;R!1+2+[!5'b00%b;R+E2!1'f<!1'aB#1!1'f=#1$x;R0!5'b0+E2!2'f<!1'aB#2#1!2'f=#2#1$x0;R+E!5'b0+31!3'f<!1'aB#3#2#1!3'f=#3#2#1$x1;R+3!5'b0+E+1!4'f<!1'aB#4#3#2#1!4'f=#4#3#2#1$x2;R+Evd!6'_W3!1'cQ#5$o;R3!3+^N+1-^;RN$x;R!1+^;4+1!2'c[!1'aB#6#42$p;R4-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!1#4#52$lh;R+37,6,69!6'_W:!1'd1#5$o;R:!3+^N+1-^;RN$x;R!1+^;4+1!1#1#42$p;R48,69!2,^H+1-^;RN$x;R!1+^;4+1!2'd1#5#32$p;R4-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3-^;RN$x;R!1+^;+3+1!2'cQ#8#42$lh;R+3!3'_65$t;R5-_>RN$t;R!2+_>4+5+1#11$p;R4$n0;R+5-_>RN$p;R!2+_>+3+3+1#21$a;R+3$n;R+3!2'_8!2'_:#2!2'^U#8#;!2'_:!2'^U!2'^U#7#;#66!1'f9!1'f:!1'f;#8,6,6!1'c[;!1'd2#5!1'cP;!1'cR#5!3+^N+1!5'f<;#4#3#2#1!5'f=#5#4#3#2#1").
Qed.
#[local] Hint Rewrite inside_runsB_eqf : bceq.

(* [comment removed for export] *)
Definition safe_range (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhi k len, base_range k b with
    | Some lh, Some (lo, hi) =>
        (lin_ge0 k [(b, off)] [(e_top, 0%Z)] && Z.leb (hi + off + lh) two64)     (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
    | _, _ => false
    end) || inside_maps k ms b off len || inside_runs k ms b off len)%bool.   (* [comment removed for export] *)

Definition safe_rangeB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  ((match xhiB bc len, base_rangeB bc b with
    | Some lh, Some (lo, hi) =>
        (lin_ge0B bc [(b, off)] [(e_top, 0%Z)] && Z.leb (hi + off + lh) two64)   (* [comment removed for export] *)
        || (Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A))    (* [comment removed for export] *)
    | _, _ => false
    end) || inside_mapsB bc ms b off len || inside_runsB bc ms b off len)%bool.

Lemma safe_rangeB_eqf : forall fk, safe_rangeB (mkbc fk) = safe_range fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SN0!1+2+:%len;R+E+1%off;R+31%b;R+E2%ms;R03!1'aB#6!2'cP5#2!2+_>+3+3!2'c[!1'aB#7#5!2+_>+E+3!1,^09!3,_T9!4,d4+E+3#8#7:!3,_T9!4,d4+E+3'f@,I:!2'^U!2'^U#1#7#4!2'_:='^>!1'cW/A;!1'cX/A;!2'_8!2'_:?!2'^U#2#7!2'_:=@-^;RN$x;R!1+^;+3+162$lh;R+3-^;RN$x;R!1+^;7+182$p;R7-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4!2'_8!3'd3!1'aB#:;<>A,6,6!4#1#5#4#3#2!2'cQ#6#2-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4!2'_8!3'd8#:;<>A!5'f8#6#5#4#3#2!5'f=#6#5#4#3#2!2'_4!2'_4-^;RN$x;R!1+^;+3+1D2$lh;R+3-^;RN$x;R!1+^;7+1!2'd1#7#52$p;R7E,6,6FG%pos;R'd7%neg;R'd7+1%e;R+E!1+^;+3%e;R+E!1+^;7!2'^U!2'^U#1#6#4!1'aB#5$fk;R!1+2+[!5'b003!1'f>!1'aB#1!1'f?#1$x;R0!5'b0+E2!2'f>!1'aB#2#1!2'f?#2#1$x0;R+E!5'b0+31!3'f>!1'aB#3#2#1!3'f?#3#2#1$x1;R+3!5'b0+E+1!4'f>!1'aB#4#3#2#1!4'f?#4#3#2#1$x2;R+Evd!6'_W4!1'f=#5$b;R4!3+^N+1!2'_4!2'_4B!5'f75#5#4#3#2CH!6'_W4!1'f8#5$b;R4!3+^N+1!2'_4!2'_4BCGH!6'_WI!1'd8#5$b;RI!3+^N+1!2'_4!2'_4-^;RN$x;R!1+^;+3+162$lh;R+3-^;RN$x;R!1+^;7+182$p;R7-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4!2'_8!2#5;<>A,6,6FGH!6'_WJ!1'cQ#5$o;RJ!3+^N+1!2'_4!2'_4-^;RN$x;R!1+^;+3+1!1#1#22$lh;R+3-^;RN$x;R!1+^;7+182$p;R7E,6,6FGH!6'_WK!1'd1#5$o;RK!3+^N+1!2'_4!2'_4-^;RN$x;R!1+^;+3+1D2$lh;R+3-^;RN$x;R!1+^;7+1!1#2#52$p;R7E,6,6FGH!2,^H+1!2'_4!2'_4-^;RN$x;R!1+^;+3+1!2'cQ#5#12$lh;R+3-^;RN$x;R!1+^;7+1!2'd1#6#42$p;R7-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4!2'_8!3'd8#9!3,_T9!4,d4+E+3#7#6:<!2'_:L'^>!2'_8!2'_:?!2'^U#2#6!2'_:L@,6,6!5'f8#5#4#3#2#1!5'f=#5#4#3#2#1!1'c[M!1'd2#5!1'cPM!1'cR#5!1'd3M!1'd9#5!1'f7M!1'fA#5!1'f<M!1'fB#5!3+^N+1!5'f>M#4#3#2#1!5'f?#5#4#3#2#1").
Qed.
#[local] Hint Rewrite safe_rangeB_eqf : bceq.



Definition grant_keep_b (k : list kentry) (ms : list amap) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20-^3RN$a;R+^3+1#21$b;R+E$o;R+3!5'f?#7#6#2#1#3-^3RN$a;R+^3+1#31$b;R+E$o;R+3!5'f?#8#7#2#1#4$k;R!1+2+[$ms;R!1+2+:$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$o;R+3!2'_8!2'`U#4}8!5'f?#8#7#2#1!1,H!1'_;#4$a;R+^3$l;R+E0$a;R+^3$l;R+E$k0;R+51$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E0$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+31$a;R+^3$l;R+E0").

Definition grant_keep_bB (bc : bctx) (ms : list amap) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20-^3RN$a;R+^3+1#21$b;R+E$o;R+3!5'f>#7#6#2#1#3-^3RN$a;R+^3+1#31$b;R+E$o;R+3!5'f>#8#7#2#1#4$bc;R+aK$ms;R!1+2+:$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$o;R+3!2'_8!2'`U#4}8!5'f>#8#7#2#1!1,H!1'_;#4$a;R+^3$l;R+E0$a;R+^3$l;R+E$k;R+51$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E0$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+31$a;R+^3$l;R+E0").

Lemma grant_keep_bB_eqf : forall fk, grant_keep_bB (mkbc fk) = grant_keep_b fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;0!1+2+:%ms;R0%b;R+E%off;R+3%len;R+E+1!2'`U#4}8!1,H!1'_;#4-^3RN$a;R+^3+1#21$b;R+E$o;R+3!4#5#7#2#1#3-^3RN$a;R+^3+1#31$b;R+E$o;R+3!4#6#8#2#1#4-^3RN$a;R+^3+1#21$b;R+E$o;R+3!5'f?#8#7#2#1#3-^3RN$a;R+^3+1#31$b;R+E$o;R+3!5'f?#9#8#2#1#4-^3RN$a;R+^3+1#21$b;R+E$o;R+3!5'f?#7#6#2#1#3-^3RN$a;R+^3+1#31$b;R+E$o;R+3!5'f?#8#7#2#1#4!1'aB#3$fk;R!1+2+[!5'b00%K;R+[+1!1'fC!1'aB#1!1'fD#1$x;R0!5'b0+[+1!2'fC!1'aB#2#1!2'fD#2#1$x0;R+[vd!6'_W1!1'f?#3$b;R1!3+^N+1-[RN$K;R+[+1#2:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$o;R+3!2'_82!4#6#8#2#13$a;R+^3$l;R+E4$a;R+^3$l;R+E$k;R+55$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E4$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+35$a;R+^3$l;R+E4-[RN$K;R+[+1#2:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$o;R+3!2'_82!5'f?#9#8#2#13$a;R+^3$l;R+E6$a;R+^3$l;R+E$k0;R+57$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+37$a;R+^3$l;R+E6!2,^H+1-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E-^3RN$a;R+^3+1#31$b;R+E$o;R+3!2'_82!5'f?#8#7#2#13$a;R+^3$l;R+E8$a;R+^3$l;R+E$k0;R+59$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E8$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$l;R+E$c;R+39$a;R+^3$l;R+E8!1'f>:!1'fE#3!3+^N+1!3'fC:#2#1!3'fD#3#2#1").
Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter (k : list kentry) (ms : list amap) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$k;R!1+2+[$ms;R!1+2+:!1'fF!3'_@+[!2'fD#2#1#2").

Definition kn_grant_filterB (bc : bctx) (ms : list amap) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$bc;R+aK$ms;R!1+2+:!1'fF!3'_@+[!2'fC#2#1!1'b=#2").

Lemma kn_grant_filterB_eqf : forall fk, kn_grant_filterB (mkbc fk) = kn_grant_filter fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S60!1+2+[!1+2+:%ms;R1%K;R+[+1!2'fD#3#2!1'fF!3'_@+[3#3!1'aB#2$fk;R0!5'b010!1'fG!1'aB#1!1'fH#1$x;R1vd!6'_W2!1'fD#2$b;R2!3+^N0!1'fF!3'_@+[!1#1#2!1'b=!1'aB#34!6'_W0#2$l;R0!3+^N0!1'fF!3'_@+[3#14!2,^H0!1'fF!3'_@+[!2'fD#2#1#2!1'b=5!1'bA#2!1'fC5!1'fI#2!3+^N0!2'fG5#1!2'fH#2#1").
Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.

Definition budget_ok (cs : acs) (extra : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$extra;R+3!2'_:!2'^U!2'^U!1'R#2!1'U#2#1/LIMIT;").

(* [comment removed for export] *)
Definition kdisj_new1 (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA nb 0) ne]) ms.

Definition kdisj_merged (ms : list amap) (nb ne : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!2+_>+3+3!2+_>0+5!1+2+[!1,^0+[$ms;R!1+2+:$nb;R+E$ne;R+E!4'bU1+[$t;R1-_>RN$t;R!2+_>0+52#11$p;R0$k;R+5-_>RN$p;R!2+_>+3+32#21$a;R+3$n;R+3-1RN$~R+12!2'`U}2#32!3,_T+[!4,a5!2,`F!1,H#2,I!1,H#1!2,`F#7,I#633!1'f9!1'f:!1'f;#3").

(* [comment removed for export] *)
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  kdisj_merged ms nb ne ++ kdisj_new1 ms nb ne.

(* [comment removed for export] *)
Definition grant_vlo (ms : list amap) (nlo : Z) : Z :=
  fold_left (fun acc (t : Z * Z * nat) => let '(lo, n, _) := t in
                                          if Z.ltb (lo - 4096) nlo then Z.max acc ((lo + n) / 4096) else acc)
            (iv_coalesce (iv_sort (lit_ivs ms)))
            (if Z.ltb (img_lo A - 4096) nlo then img_hi A / 4096 else 1).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stk_len0 : expr := esub (ELit (2^47 + 8388608)) e_sp0.
(* [comment removed for export] *)
Definition kdisj_stk_extra : list (expr * Z * expr) :=
  [(fst e_auxb, snd e_auxb, esub (ELit (2^47)) e_auxv);          (* [comment removed for export] *)
   (fst e_atrb, snd e_atrb, esub (ELit (2^47)) e_atrandom)].     (* [comment removed for export] *)
Definition kdisj_fixed (k : list kentry) (nb ne : expr) : list kentry :=
  [KDisj (SA (ELit (img_lo A)) 0) (ELit (img_hi A - img_lo A)) (SA nb 0) ne;
   KDisj (SA e_sp0 (-8388608)) e_stk_len0 (SA nb 0) ne]                                          (* [comment removed for export] *)
  ++ flat_map (fun t : expr * Z * expr => let '(b, off, len) := t in
                 if lin_ge0 k [(b, off)] [(e_top, 0%Z)] then [KDisj (SA b off) len (SA nb 0) ne] else [])
              kdisj_stk_extra                                                                    (* [comment removed for export] *)
  ++ [KDisj (SA e_top 0) e_stk_len (SA nb 0) ne].

(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
      (if kind_noneb (am_kind m) then HCons (am_base m) (am_len m) :: a_hna cs else a_hna cs)
      (if kind_lazyb (am_kind m) then HCons (am_base m) (am_len m) :: a_hlz cs else a_hlz cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_kend (base ne : expr) (nlo : Z) : list kentry :=
  match ne with
  | ELit _ => []
  | _ => [KRange (eadd base ne) (4096 + nlo) TOPC]
  end.

(* [comment removed for export] *)
Definition kdisj_shadow_twin (k : list kentry) (K : kentry) : list kentry :=
  match K with
  | KDisj (SA b1 0) n1 (SA b2 0) n2 =>
      let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
      let '(sb1, sk1, sn1) := shadow_of k b1 n1 in let '(sb2, sk2, sn2) := shadow_of k b2 n2 in
      if (Z.leb 3 (ealign k b1) && Z.leb 3 (ealign k n1) && Z.leb 3 (ealign k b2) && Z.leb 3 (ealign k n2)
          && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
          && match xhi k (eadd b1 n1), xhi k (eadd b2 n2), xhi k b1, xhi k n1, xhi k b2, xhi k n2 with
             | Some e1, Some e2, Some h1, Some m1, Some h2, Some m2 =>
                 Z.leb e1 (2 ^ 47) && Z.leb e2 (2 ^ 47) && Z.ltb (h1 + m1) two64 && Z.ltb (h2 + m2) two64
             | _, _, _, _, _, _ => false end)%bool
      then [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2] else []
  | _ => []
  end.

(* [comment removed for export] *)
Definition contra_cs (cs : acs) : acs := set_kn cs (KRange (ELit 0) 1 0 :: kn cs).

(* [comment removed for export] *)
Definition first_run (ms : list amap) : option (Z * Z) :=
  match iv_coalesce (iv_sort (lit_ivs ms)) with
  | (lo, n, _) :: _ => Some (lo, lo + n)
  | [] => None
  end.

Definition mmap_null (split : bool) (cs : acs) (kind : mkind) (eager visible : bool) : option (acs * acs) :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let vlo := grant_vlo (a_maps cs) nlo in
        let vhi := (TOPC - nlo) / 4096 in
        let kd := kdisj_fixed (kn cs) base ne ++ kdisj_new (a_maps cs) base ne in
        let kv := KRange (EVar v) vlo vhi :: null_kend base ne nlo ++ kn cs in   (* [comment removed for export] *)
        let kfacts := KRange (EVar v) vlo vhi :: null_kend base ne nlo
                      ++ kd ++ flat_map (kdisj_shadow_twin kv) kd in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filter (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs) in
        let fin (c : acs) := if visible then vis_add c base ne (kmem ++ kn c) else Some c in
        let single := match fin cs1 with Some c => Some (contra_cs c, c) | None => None end in
        (* [comment removed for export] *)
        if negb (split && visible) then single else
        match first_run (a_maps cs) with
        | Some (lo, hi) =>
            let vtopL := (lo - nlo) / 4096 in      (* [comment removed for export] *)
            let vbotH := zcdiv' hi 4096 in         (* [comment removed for export] *)
            if (Z.leb vbotH vlo || Z.ltb vtopL vlo)%bool then single     (* [comment removed for export] *)
            else if Z.ltb vhi vbotH then                                  (* [comment removed for export] *)
              match fin (set_kn cs1 (KRange (EVar v) vlo vtopL :: kn cs1)) with
              | Some c => Some (contra_cs c, c) | None => None end
            else
              match fin (set_kn cs1 (KRange (EVar v) vlo vtopL :: kn cs1)),
                    fin (set_kn cs1 (KRange (EVar v) vbotH vhi :: kn cs1)) with
              | Some cL, Some cH => Some (cL, cH)
              | _, _ => None
              end
        | None => single
        end
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      (* [comment removed for export] *)
      if (page_aligned k a && Z.ltb 0 alo && (Z.leb (img_hi A) alo || off_image_x k b off ne) && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
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

Definition mmap_fixed_free1 (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs CEIL with     (* [comment removed for export] *)
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
Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option (acs * acs) :=
  match mmap_fixed_free1 cs kind eager visible with Some c => Some (contra_cs c, c) | None => None end.

(* [comment removed for export] *)
Definition kn_rezero (k : list kentry) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprep k ub uk un in
  List.filter (fun K => match K with
                        | KWord _ _ _ | KBlob _ _ _ | KFill _ _ _ => kentry_apart_bp k sp ub uk un K
                        | _ => true
                        end) k.

Definition kn_rezeroB (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S10!6'b7#9#5#8#7#6#4$bc;R+aK$ub;R+E$uk;R+3$un;R+E&sp;R!4'b;#4#3#2#1+b5!3'_@+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E0$a;R+^3$n;R+E,9$a;R+^3$n;R+E$k;R+50$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E,9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$n;R+E$c;R+30$a;R+^3$n;R+E,9!1'b=#5").

Lemma kn_rezeroB_eqf : forall fk, kn_rezeroB (mkbc fk) = kn_rezero fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S;0!1+2+[%un;R+E0%sp;R+b5%ub;R+E%uk;R+3%un;R+E%K;R+[+1!5#5!4'b;!1'aB#9#8#7#6#8#7#6#4!1'b=!1'aB#5!6'b8#9!4'b@#9#8#7#6#8#7#6#4!3'_@+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E5$a;R+^3$n;R+E,9$a;R+^3$n;R+E$k0;R+55$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E,9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$n;R+E$c;R+35$a;R+^3$n;R+E,9#5%b1;R+E%k1;R+3%n1;R+E+b5!6'b8#9!3#5#8#7#6#8#7#6#4!6'b8#8!4'b@#8#7#6#5#7#6#5#4!1'aB#4$fk;R0!5'b0+E%uk;R+31!1'fJ!1'aB#1!1'fK#1$x;R+E!5'b0+31!2'fJ!1'aB#2#1!2'fK#2#1$x0;R+3!5'b0+E0!3'fJ!1'aB#3#2#1!3'fK#3#2#1$x1;R+Evd!6'_W2!1'b8#4$b;R2!3+^N0!3'_@+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E3$a;R+^3$n;R+E,9$a;R+^3$n;R+E$k;R+53$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E,9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$n;R+E$c;R+33$a;R+^3$n;R+E,946!6'_W7!1'b@#4$s;R7!3+^N0!3'_@+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E8$a;R+^3$n;R+E,9$a;R+^3$n;R+E$k;R+58$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E,9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$n;R+E$c;R+38$a;R+^3$n;R+E,946!6'_W0#4$l;R0!3+^N0!3'_@+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E5$a;R+^3$n;R+E,9$a;R+^3$n;R+E$k;R+55$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E,9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$n;R+E$c;R+35$a;R+^3$n;R+E,9#16!2,^H0!3'_@+[$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E9$a;R+^3$n;R+E,9$a;R+^3$n;R+E$k0;R+59$lo;R+3$hi;R+3,9$e;R+E$m;R+3,9$e;R+E$lo;R+3$hi;R+3,9$a;R+^3$n;R+E,9$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,9$a;R+^3$n;R+E$c;R+39$a;R+^3$n;R+E,9#4!1'b=:!1'bA#4!1'b;:!1'bB#4!1'b7:!1'bC#4!3+^N0!4'fJ:#3#2#1!4'fK#4#3#2#1").
Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.

Definition kn_rezeroM (k : list kentry) := kn_rezeroB (mkbc k).
Lemma kn_rezeroM_eq : kn_rezeroM = kn_rezero. Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!1+2+[%ub;R+E%uk;R+3%un;R+E0!5'b001'fL'fK$k;R0vd!1'fM#1!3+^N1!1'fL#1!1'fK#1").
Qed.



(* [comment removed for export] *)
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.

(* [comment removed for export] *)
Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs TOPC with
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
  match fixed_args cs TOPC with
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SK0!1+2+8%ms;R!1+2+:%kinds;R0%b;R+E%off;R+3%n;R+E!1+^;+:!1'^9#2!2+_>+E+3!2+_>3+E!2+_>4+3!2+_>5+3!2+_>6+:!1+^;7!2'fO#3'fP!1'O#<!1,^0+8!3,_T+8,fQ!3,_T+8,fR!3,_T+8,fS;!3,_T+8,eP;-fNRN$arm;R+fN0#;3<=<!1'e9#=}:!2,^<7!4,d46+:!4,d45+3!4,d44+3!4,d43+E!4,d4+E+3#3#2#4#6#8#1!1,^27-1RN$~R+18!2'_8!2'a:?#4!2'a:?!2'^B#=@2AB!2'fO#2'fP!1'^9#;!1'O#;-fNRN$arm;R+fN0#:3<=<!1'e9#<-1RN$~R+18!2'_8!2'a:H#4!2'a:H!2'^B#<@2AB-^;RN$x;R!1+^;68D2$p;R6-_>RN$p;R!2+_>5+38#11$p0;R5$nhi;R+3-_>RN$p0;R!2+_>4+38#21$p1;R4$nlo;R+3-_>RN$p1;R!2+_>3+E8#21$p2;R3$ne;R+E-_>RN$p2;R!2+_>+E+38#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:8!6'eEEFG#2#1#32$m;R+:IBB$cs;R+C$arm;R+fNvdvd!6'_W1!1'eE2$o;R1!3+^N8-^;RN$x;R!1+^;6892$p;R6-_>RN$p;R!2+_>5+38#11$p0;R5$nhi;R+3-_>RN$p0;R!2+_>4+38#21$p1;R4$nlo;R+3-_>RN$p1;R!2+_>3+E8#21$p2;R3$ne;R+E-_>RN$p2;R!2+_>+E+38#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:8!5#::>#2#1#32$m;R+:CBB-^;RN$x;R!1+^;6892$p;R6-_>RN$p;R!2+_>5+38#11$p0;R5$nhi;R+3-_>RN$p0;R!2+_>4+38#21$p1;R4$nlo;R+3-_>RN$p1;R!2+_>3+E8#21$p2;R3$ne;R+E-_>RN$p2;R!2+_>+E+38#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:8!6'eE!1'^9#<:>#2#1#32$m;R+:CBB!2,^H8J!1'eD!1'aB2!1'eS2!3+^N8-^;RN$x;R!1+^;68D2$p;R6-_>RN$p;R!2+_>5+38#11$p0;R5$nhi;R+3-_>RN$p0;R!2+_>4+38#21$p1;R4$nlo;R+3-_>RN$p1;R!2+_>3+E8#21$p2;R3$ne;R+E-_>RN$p2;R!2+_>+E+38#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:8!6'eD!1'aBEFG#2#1#32$m;R+:IBBJ!3+^N8!2'fT#2#1!2'fU#2#1").
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
        let a := reg cs 10 in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                       (match arm with ArmG => HCons a ne :: HSub a ne :: a_hna cs | _ => HSub a ne :: a_hna cs end)
                       (match arm with ArmF => HCons a ne :: HSub a ne :: a_hlz cs | _ => HSub a ne :: a_hlz cs end) in
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
        let a := reg cs 10 in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                       (match arm with ArmG => HCons a ne :: HSub a ne :: a_hna cs | _ => HSub a ne :: a_hna cs end)
                       (match arm with ArmF => HCons a ne :: HSub a ne :: a_hlz cs | _ => HSub a ne :: a_hlz cs end) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.

Lemma mmap_fixed_in_eq : forall cs arm, mmap_fixed_in cs arm = mmap_fixed_in_ref cs arm.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_20!1+2+[%ub;R+E%uk;R+3%un;R+E0!1'^9#2!1+^;+C!2+_>+E+3!2+_>4+E!2+_>5+3!2+_>6+3!2+_>7+:!2'fT#3#2-fNRN$arm;R+fN+1#=3!2'fV#>#7,9,9!1,^K|20;!2'^U!1'd?#>;!1'G#>!1'F=!1'^9#>!1'aB?!1'fF!4'b>@#2#1#3!1'fF!3#<#2#1#3!1'L=!1+2+:!1'O#>!2'fWE#9-fNRN$arm;R+fND#=3FEF!1'P#>!1'Q#>!1'R#>-fNRN$arm;R+fN+3#=3!2'^UJ#7JJ!1'S#>!1'T#>!1'U#>!1'V#>!1'W#>!1'X#>!1+2+`>}:!2'^B#>S!2,fXT#3!3,_T+`>U!1'Y#>!2,fYT#3-fNRN$arm;R+fNR#=3VV!3,_T+`>WV!3,_T+`>U!1'Z#>-fNRN$arm;R+fNR#=3Y!3,_T+`>WYY!=,N!4'^5<>-fNRN$arm;R+fN0#=3A!1'fF!4'fJ@#2#1#3BCGHIKLMNOPQXZ!2,`F#2#1!2,a4\#3!2,`[\#3!2,^<+C[!1,^2+C!1'fF!4'fK?#2#1#3!1'fF!4'c9?#2#1#3!=,N!4'^5<>-fNRN$arm;R+fN0#=3!1'fF!4'b??#2#1#3^4^5CGHIKLMNOPQXZ!2,^<+C^6-^;RN$x;R!1+^;8392$p;R8-_>RN$p;R!2+_>7+:3#11$p0;R7$m;R+:-_>RN$p0;R!2+_>6+33#21$p1;R6$nhi;R+3-_>RN$p1;R!2+_>5+33#21$p2;R5$nlo;R+3-_>RN$p2;R!2+_>4+E3#21$p3;R4$ne;R+E-_>RN$p3;R!2+_>+E+33#21$b;R+E$off;R+3-1RN$~R+13:2-fNRN$arm;R+fN3#=3!4'eX^6T#3!3,_T+[^0!3,_T+[^1!1'^9^6^7^7^3^3!=,N!4'^5<>-fNRN$arm;R+fN0#=3AB^5CGHIKLMNOPQXZ!2,^<+C^9!=,N!4'^5<>-fNRN$arm;R+fN0#=3B^4^5CGHIKLMNOPQXZ!2,^<+C^;!2'fT#2#1-fNRN$arm;R+fN+1#<3!2'fV#=#7,9,9!2'^U!1'd?#=;!1'G#=!1'F^@!1'^9#=!1'L^@!1'O#=!2'fW^D#9-fNRN$arm;R+fND#<3^E^D^E!1'P#=!1'Q#=!1'R#=-fNRN$arm;R+fN+3#<3!2'^U^I#7^I^I!1'S#=!1'T#=!1'U#=!1'V#=!1'W#=!1'X#=!2'^B#=S!2,fX^Q#3!3,_T+`>^R!1'Y#=!2,fY^Q#3-fNRN$arm;R+fNR#<3^S^S!3,_T+`>^T^S!3,_T+`>^R!1'Z#=-fNRN$arm;R+fNR#<3^V!3,_T+`>^T^V^V!=,N!4'^5^?^A-fNRN$arm;R+fN0#<3!1'fF!4'b?^B#2#1#3!1'fF!4'fK^B#2#1#3!1'fF!4'c9^B#2#1#3^C^F^G^H^J^K^L^M^N^O^P^U^W!2,^<+C^X-^;RN$x;R!1+^;83^=2$p;R8-_>RN$p;R!2+_>7+:3#11$p0;R7$m;R+:-_>RN$p0;R!2+_>6+33#21$p1;R6$nhi;R+3-_>RN$p1;R!2+_>5+33#21$p2;R5$nlo;R+3-_>RN$p2;R!2+_>4+E3#21$p3;R4$ne;R+E-_>RN$p3;R!2+_>+E+33#21$b;R+E$off;R+3-1RN$~R+13^>2-fNRN$arm;R+fN3#<3!4'eX^X^Q#3!3,_T+[^0!3,_T+[^1!1'^9^X^Y^Y^3^3!1'aB2!1'aB^B!=,N!4'^5^?^A-fNRN$arm;R+fN0#<3!1'fF!4'b>^\#2#1#3!1'fF!4'fJ^\#2#1#3!1'fF!4'c8^\#2#1#3^C^F^G^H^J^K^L^M^N^O^P^U^W!2,^<+C_0$cs;R+C$arm;R+fNvdvd!6'_W1!1'c92$l;R1!3+^N3-^;RN$x;R!1+^;8392$p;R8-_>RN$p;R!2+_>7+:3#11$p0;R7$m;R+:-_>RN$p0;R!2+_>6+33#21$p1;R6$nhi;R+3-_>RN$p1;R!2+_>5+33#21$p2;R5$nlo;R+3-_>RN$p2;R!2+_>4+E3#21$p3;R4$ne;R+E-_>RN$p3;R!2+_>+E+33#21$b;R+E$off;R+3-1RN$~R+13:2-fNRN$arm;R+fN3#=3!4'eX[T#3!3,_T+[^0!3,_T+[^1!1'^9[^2^2^3^3^8!6'_W1!1'fK2$l;R1!3+^N3-^;RN$x;R!1+^;8392$p;R8-_>RN$p;R!2+_>7+:3#11$p0;R7$m;R+:-_>RN$p0;R!2+_>6+33#21$p1;R6$nhi;R+3-_>RN$p1;R!2+_>5+33#21$p2;R5$nlo;R+3-_>RN$p2;R!2+_>4+E3#21$p3;R4$ne;R+E-_>RN$p3;R!2+_>+E+33#21$b;R+E$off;R+3-1RN$~R+13:2-fNRN$arm;R+fN3#=3!4'eX^9T#3!3,_T+[^0!3,_T+[^1!1'^9^9^:^:^3^3^8!6'_W1!1'b?2$l;R1!3+^N3-^;RN$x;R!1+^;8392$p;R8-_>RN$p;R!2+_>7+:3#11$p0;R7$m;R+:-_>RN$p0;R!2+_>6+33#21$p1;R6$nhi;R+3-_>RN$p1;R!2+_>5+33#21$p2;R5$nlo;R+3-_>RN$p2;R!2+_>4+E3#21$p3;R4$ne;R+E-_>RN$p3;R!2+_>+E+33#21$b;R+E$off;R+3-1RN$~R+13:2-fNRN$arm;R+fN3#=3!4'eX^;T#3!3,_T+[^0!3,_T+[^1!1'^9^;^<^<^3^3^8!2,^H3^Z!1'b>^[!1'bE2!1'fJ^[!1'fM2!1'c8^[!1'c<2!3+^N3-^;RN$x;R!1+^;83^=2$p;R8-_>RN$p;R!2+_>7+:3#11$p0;R7$m;R+:-_>RN$p0;R!2+_>6+33#21$p1;R6$nhi;R+3-_>RN$p1;R!2+_>5+33#21$p2;R5$nlo;R+3-_>RN$p2;R!2+_>4+E3#21$p3;R4$ne;R+E-_>RN$p3;R!2+_>+E+33#21$b;R+E$off;R+3-1RN$~R+13^>2-fNRN$arm;R+fN3#<3!4'eX_0^Q#3!3,_T+[^0!3,_T+[^1!1'^9_0_1_1^3^3^Z!3+^N3!2'fZ#2#1!2'f[#2#1").
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
Definition dest_rfact (a ne mb ml : expr) (rne : bool) : kentry := ltac2:(Rpl.RP.run_i (rplG ()) 5 "S20!2'^T!2'^P#3#2!2'^P#5#4!1,^K,_0$a;R+E$ne;R+E$mb;R+E$ml;R+E$rne;R+1-1RN$rne;R+1+[#12!3,a301!2'a\'^>1!3,a30,I,I").

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
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
      (HSub a ne :: a_hna cs) (HSub a ne :: a_hlz cs).
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
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
      (HSub a ne :: a_hna cs) (HSub a ne :: a_hlz cs).

Lemma mmap_destroyed_with_eq : forall hole cs b off ne m lne rne, mmap_destroyed_with hole cs b off ne m lne rne = mmap_destroyed_with_ref hole cs b off ne m lne rne.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^<0%ub;R+E%uk;R+3%un;R+E!1+2+[!1'^9#7!1,^K|20;!2'^U!1'd?#82!1'G#8}:!1,H'f\!3'^6!1'F456!2'^B#85!1'`A#4!3'g089#3!1'`B#4!5'g18#59;#2!1'L4!1+2+:!1,^0+:!1'<#4!2'^P8#5!3'^8+:-1RN$hole;R+1>#92!3,_T+:!3,g28#5,=??!3'g3!1'O#8#4!3'^8+:-1RN$lne;R+1>#32!3,_T+:!3,g29!2'^T89@??-1RN$rne;R+1>#22!3,_T+:!3,g2A!2'^T!2'^P9;A@??!1'P#8!1'Q#8!1'R#8!1'S#8!1'T#8!1'U#8!1'V#8!1'W#8!1'X#8!2,fX8#5!3,_T+`>L!1'Y#8!3,_T+`>L!1'Z#8!2'^U!1'd?#72!1'G#7!3'^6!1'FP56!2'^B#75!1'`A#3!3'g0RS#2!1'`B#3!5'g1R#4SU#1!1'LP!1'<#3!2'^PR#4!3'^8+:-1RN$hole;R+1>#82!3,_T+:!3,g2R#4,=??!3'g3!1'O#7#3!3'^8+:-1RN$lne;R+1>#22!3,_T+:!3,g2S!2'^TRSX??-1RN$rne;R+1>#12!3,_T+:!3,g2Y!2'^T!2'^PSUYX??!1'P#7!1'Q#7!1'R#7!1'S#7!1'T#7!1'U#7!1'V#7!1'W#7!1'X#7!2,fXR#4!3,_T+`>^7!1'Y#7!3,_T+`>^7!1'Z#7!=,N!4'^5OQ!3,_T+[T!3,_T+[V!1'fF!4'c91#6#5#4WZ[\^0^1^2^3^4^5^6^8^9!1'aB1$hole;R+1$cs;R+C$b;R+E$off;R+3$ne;R+E$m;R+:$lne;R+1$rne;R+1vdvd!6'_W0!1'c91$l;R0!3+^N+C!=,N!4'^537!3,_T+[:!3,_T+[<!1'fF!3#1#7#6#5=BCDEFGHIJKMN!=,N!4'^537!3,_T+[:!3,_T+[<!1'fF!4'c9!1'^9#8#7#6#5=BCDEFGHIJKMN!2,^H+C^:!1'c8^;!1'c<1!3+^N+C!=,N!4'^5OQ!3,_T+[T!3,_T+[V!1'fF!4'c8^;#6#5#4WZ[\^0^1^2^3^4^5^6^8^9^:!3+^N+C!8'g4#8#7#6#5#4#3#2#1!8'g5#8#7#6#5#4#3#2#1").
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

Definition mmap_destroyed (hole : bool) (cs : acs) (b : expr) (off : Z) (ne : expr) (m : amap) : list acs := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S10!2+_>+1+1$hole;R+1$cs;R+C$b;R+E$off;R+3$ne;R+E$m;R+:!4'g60+C$lr;R0!8'g4#7#6#5#4#3#2!3'`?+1+1#1!3'`@+1+1#1!3'g7#5#2#1").

(* [comment removed for export] *)
Definition mmap_gate (cs : acs) : option (Z * Z * bool) :=
  match reg_lit cs 17, reg_lit cs 12, reg_lit cs 13, reg_lit cs 14, reg_lit cs 15 with
  | Some 222, Some prot, Some flags, Some m1, Some 0 =>
      if negb (Z.eqb m1 (two64 - 1)) then None
      else Some (prot, flags, match reg_lit cs 10 with Some 0 => true | _ => false end)
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition node_mmap2 (split : bool) (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_null split cs KRW true true               (* [comment removed for export] *)
                 | 3, 0x4022 => mmap_null split cs KRWLAZY false true        (* [comment removed for export] *)
                 | 0, 0x22 => mmap_null split cs KNONE false false           (* [comment removed for export] *)
                 | 0, 0x4022 => mmap_null split cs KNONELAZY false false     (* [comment removed for export] *)
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x32 => mmap_fixed_free cs KRW true true          (* [comment removed for export] *)
                 | 0, 0x4032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x32 => mmap_fixed_free cs KNONE false false      (* [comment removed for export] *)
                 (* [comment removed for export] *)
                 | 3, 0x104022 | 3, 0x104032 => mmap_fixed_free cs KRWLAZY false false   (* [comment removed for export] *)
                 | 0, 0x104022 | 0, 0x104032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | _, _ => None
                 end in
      match g with Some p => Some p | None => None end
  | None => None
  end.

(* [comment removed for export] *)
Lemma mmap_null_nosplit_contra : forall cs kind eager visible csa csb,
  mmap_null false cs kind eager visible = Some (csa, csb) -> kn_contra (kn csa) = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SaY0!2+_>+C+C!1+^;0!2,^<0!4,d4+C+C#2#1!2+_>+E+3!2+_>3+3!1'e9#>!1'O#>!1+^;+C}:!1,^K|<000;!1,^L5!2'^R9:!2'e;!2'a\'fP#19!3,a3:!2'g<6#1<!3'g=;#2#1!1'^9#>!3'^8+[!3'g>?;#2!3'g?6;#2!8'g;#>!3'^6!1'F!1'G#>8;!3'^8+[!3,_T+[=!3'^8+[>!3'^8+[@!4'bU+[+[!1'g@!3,_T+[=!3'^8+[>?@!2'fH?6!1,_N5!3,g2;#2#=#3#<!1'Q#>!2,`F;,I!1,^0+[!2,^<0!4,d4+C+C!1'gA#1#1!1,^20-^;RN$x;R!1+^;+C1-1RN$visible;R+17#;2!4'eXA;#2!3'^8+[!3,_T+[!2,a4B#2!3,_T+[!2,`[B#2C!1'^9A!2,^<+CA2$c;R+CDE!2+_>+3+3!2'gC#19!1'O#A!2'g<I#4!2'e;!2'a\#2#49!1'e9#A!1,^LL!2'^R9M!3'^6!1'F!1'G#A8N!2'e;!2'a\'fP#49!3,a3MJP!3'g=N#5#4!1'^9#A!3'^8+[!3'g>SN#5!3'g?IN#5!2'fHSI!1,_NL!1'Q#A!8'g;#AO!3'^8+[!3,_T+[Q!3'^8+[R!3'^8+[T!4'bU+[+[!1'g@!3,_T+[Q!3'^8+[RSTUV!3,g2N#5#@#6#?W!2,`FN,I!3,_T+[!2,a4Y#5!3,_T+[!2,`[Y#5C!1'^9X!2'a[PH!2'^7X!3,_T+[!3,a3MJK[-1RN$visible;R+17#>2!4'eX^0N#5!3'^8+[Z!1'^9^0!2,^<+C^0!1'e9#B!1,^L^2!2'^R9^3!3'^6!1'F!1'G#B8^4!1'O#B!2'e;!2'a\'fP#59!3,a3^3!2'g<^6#5^7!3'g=^4#6#5!1'^9#B!3'^8+[!3'g>^:^4#6!3'g?^6^4#6!2'fH^:^6!1,_N^2!1'Q#B!8'g;#B^5!3'^8+[!3,_T+[^8!3'^8+[^9!3'^8+[^;!4'bU+[+[!1'g@!3,_T+[^8!3'^8+[^9^:^;^<^=!3,g2^4#6#A#7#@^>!2'gC#29!2'^7^?!3,_T+[!3,a3^3^@^7!1'^9^?!2,`F^4,I!2,^<0!4,d4+C+C#5#4!3+^N+1!1'gD!1'^9#6,9!1'e9#?!1'O#?!1,^L^E!2'^R9^G!3,a3^G!2'g<^F#1<!3'g=^H#2#1!1'^9#?!3'^8+[!3'g>^K^H#2!3'g?^F^H#2!8'g;#?!3'^6!1'F!1'G#?8^H!3'^8+[!3,_T+[^I!3'^8+[^J!3'^8+[^L!4'bU+[+[!1'g@!3,_T+[^I!3'^8+[^J^K^L!2'fH^K^F!1,_N^E!3,g2^H#2#>#3#=!1'Q#?!2,`F^H,I-^;RN$x;R!1+^;+C1-1RN$visible;R+17#<2!4'eX^M^H#2!3'^8+[!3,_T+[!2,a4^N#2!3,_T+[!2,`[^N#2C!1'^9^M!2,^<+C^M2$c;R+CDE!2'g<^6#4!3,a3^3^PP!3'g=^4#5#4!3'^8+[!3'g>^:^4#5!3'g?^6^4#5!8'g;#B^5!3'^8+[!3,_T+[^Q!3'^8+[^R!3'^8+[^S!4'bU+[+[!1'g@!3,_T+[^Q!3'^8+[^R^:^S^<^=!3,g2^4#5#A#6#@^>!3,_T+[!2,a4^B#5!3,_T+[!2,`[^B#5C!1'^9^T!2'^7^T!3,_T+[!3,a3^3^PK^V-1RN$visible;R+17#?2!4'eX^W^4#5!3'^8+[^U!1'^9^W!2,^<+C^W!1'e9#C!1,^L^Y!2'^R9^Z!1'O#C!3,a3^Z!2'g<^\#5^7!3'g=^[#6#5!1'^9#C!3'^8+[!3'g>_2^[#6!3'g?^\^[#6!8'g;#C!3'^6!1'F!1'G#C8^[!3'^8+[!3,_T+[_0!3'^8+[_1!3'^8+[_3!4'bU+[+[!1'g@!3,_T+[_0!3'^8+[_1_2_3!2'fH_2^\!1,_N^Y!3,g2^[#6#B#7#A!1'Q#C!2'^7_4!3,_T+[!3,a3^Z^@^7!1'^9_4!2,`F^[,I!3,a3M!2'g<I#1<!3'g=N#2#1!3'^8+[!3'g>SN#2!3'g?IN#2!8'g;#AO!3'^8+[!3,_T+[_7!3'^8+[_8!3'^8+[_9!4'bU+[+[!1'g@!3,_T+[_7!3'^8+[_8S_9UV!3,g2N#2#@#3#?W-^;RN$x;R!1+^;+C1-1RN$visible;R+17#>2!4'eX_:N#2!3'^8+[!3,_T+[!2,a4Y#2!3,_T+[!2,`[Y#2C!1'^9_:!2,^<+C_:2$c;R+CDE!1'O#D!2'g<_<#4!1'e9#D!1,^L_>!2'^R9_?!3'^6!1'F!1'G#D8_@!3,a3_?_=P!3'g=_@#5#4!1'^9#D!3'^8+[!3'g>_D_@#5!3'g?_<_@#5!3'^8+[!3,_T+[_B!3'^8+[_C!3'^8+[_E!4'bU+[+[!1'g@!3,_T+[_B!3'^8+[_C_D_E!2'fH_D_<!1,_N_>!3,g2_@#5#C!1'Q#D!8'g;#D_A_F_G_H#6#B_I!2,`F_@,I!3,_T+[!2,a4_K#5!3,_T+[!2,`[_K#5C!1'^9_J!2'^7_J!3,_T+[!3,a3_?_=K_M-1RN$visible;R+17#A2!4'eX_N_@#5!3'^8+[_L!1'^9_N!2,^<+C_N!1'e9#E!1,^L_P!2'^R9_Q!3'^6!1'F!1'G#E8_R!1'O#E!2'g<_T#5!3,a3_Q_U^7!3'g=_R#6#5!1'^9#E!3'^8+[!3'g>_X_R#6!3'g?_T_R#6!3'^8+[!3,_T+[_V!3'^8+[_W!3'^8+[_Y!4'bU+[+[!1'g@!3,_T+[_V!3'^8+[_W_X_Y!2'fH_X_T!1,_N_P!3,g2_R#6#D!1'Q#E!8'g;#E_S_Z_[_\#7#C`0!2'^7`1!3,_T+[!3,a3_Q^@^7!1'^9`1!2,`F_R,I!3,_T+[!2,a4`3#6!3,_T+[!2,`[`3#6C!3,a3^3!2'g<^6#2!2'e;!2'a\'fP#29!3'g=^4#3#2!3'^8+[!3'g>^:^4#3!3'g?^6^4#3!8'g;#B^5!3'^8+[!3,_T+[`5!3'^8+[`6!3'^8+[`7!4'bU+[+[!1'g@!3,_T+[`5!3'^8+[`6^:`7^<^=!3,g2^4#3#A#1#@^>-^;RN$x;R!1+^;+C1-1RN$visible;R+17#?2!4'eX`8^4#3!3'^8+[!3,_T+[!2,a4^B#3!3,_T+[!2,`[^B#3C!1'^9`8!2,^<+C`82$c;R+CDE!2'e;!2'a\#2#59!8'g;#E_S_Z_[_\#4#C`0!1'^9`;-1RN$visible;R+17#B2!4'eX`;_R#6!3'^8+[`4`<!2,^<+C`;-^;RN$x;R!1+^;+C1`=2$c;R+CDE!2'^7`;!3,_T+[!3,a3_Q_U`:`<-1RN$visible;R+17#B2!4'eX`?_R#6!3'^8+[`4!1'^9`?!2,^<+C`?!1'e9#F!1,^L`A!2'^R9`B!1'O#F!2'e;!2'a\'fP#69!3,a3`B!2'g<`D#6`E!3'g=`C#7#6!1'^9#F!3'^8+[!3'g>`H`C#7!3'g?`D`C#7!8'g;#F!3'^6!1'F!1'G#F8`C!3'^8+[!3,_T+[`F!3'^8+[`G!3'^8+[`I!4'bU+[+[!1'g@!3,_T+[`F!3'^8+[`G`H`I!2'fH`H`D!1,_N`A!3,g2`C#7#E#5#D!1'Q#F!2'^7`J!3,_T+[!3,a3`B^@`E!1'^9`J!2,`F`C,I!1'O#H!2'g<`M#8!2'e;!2'a\#2#89!1'e9#H!1,^L`P!2'^R9`Q!2'e;!2'a\'fP#89!3,a3`Q`N`S!3'g=`R#9#8!1'^9#H!3'^8+[!3'g>`V`R#9!3'g?`M`R#9!8'g;#H!3'^6!1'F!1'G#H8`R!3'^8+[!3,_T+[`T!3'^8+[`U!3'^8+[`W!4'bU+[+[!1'g@!3,_T+[`T!3'^8+[`U`V`W!2'fH`V`M!1,_N`P!3,g2`R#9#G#7#F!1'Q#H!2,`F`R,I!3,_T+[!2,a4`Y#9!3,_T+[!2,`[`Y#9C!1'^9`X!2'^7`X!3,_T+[!3,a3`Q`N`O`[-1RN$visible;R+17#E2!4'eX`\`R#9!3'^8+[`Z!1'^9`\!2,^<+C`\!1'e9#I!1,^La1!2'^R9a2!1'O#I!2'e;!2'a\'fP#99!3,a3a2!2'g<a4#9a5!3'g=a3#:#9!1'^9#I!3'^8+[!3'g>a8a3#:!3'g?a4a3#:!8'g;#I!3'^6!1'F!1'G#I8a3!3'^8+[!3,_T+[a6!3'^8+[a7!3'^8+[a9!4'bU+[+[!1'g@!3,_T+[a6!3'^8+[a7a8a9!2'fHa8a4!1,_Na1!3,g2a3#:#H#8#G!1'Q#I!2'^7a:!3,_T+[!3,a3a2^@a5!1'^9a:!2,`Fa3,I!2,^<0!4,d4+C+C#A#@!3+^N+1!1'gD^:,9!8'g;#D_A_F_G_H#3#B_I-^;RN$x;R!1+^;+C1-1RN$visible;R+17#A2!4'eXa?_@#5!3'^8+[_L!1'^9a?!2,^<+Ca?2$c;R+CDE!1'O#G!2'g<aA#7!2'e;!2'a\#2#79!1'e9#G!1,^LaD!2'^R9aE!2'e;!2'a\'fP#79!3,a3aEaBaG!3'g=aF#8#7!1'^9#G!3'^8+[!3'g>aJaF#8!3'g?aAaF#8!8'g;#G!3'^6!1'F!1'G#G8aF!3'^8+[!3,_T+[aH!3'^8+[aI!3'^8+[aK!4'bU+[+[!1'g@!3,_T+[aH!3'^8+[aIaJaK!2'fHaJaA!1,_NaD!3,g2aF#8#F#6#E!1'Q#G!2,`FaF,I!3,_T+[!2,a4aM#8!3,_T+[!2,`[aM#8C!1'^9aL!2'^7aL!3,_T+[!3,a3aEaBaCaO-1RN$visible;R+17#D2!4'eXaPaF#8!3'^8+[aN!1'^9aP!2,^<+CaP!2'^7`X!3,_T+[!3,a3`Q^@`S`[!2,^<0!4,d4+C+C#@#?!2,^<0!4,d4+C+C#C#B!3+^N+1!1'gD_D,9!1'G#4!1'gA#3$e;R1-^;RN$o;R!1+^;0w#12$~R0+`M+`Q$cs;R+C$kind;R+8$eager;R+1$visible;R+1$csa;R+C$csb;R+C$H;R!3+^N1!5'g8,6#6#5#4#32&o;R!1'f5#7!1+^;4!1-^;RN$o;R!1+^;4%H;R!3+^N1-^;RN$x;R!1+^;41#12$p;R4-_>RN$p;R!2+_>3+31#11$p0;R3$nhi;R+3-_>RN$p0;R!2+_>+E+31#21$ne;R+E$nlo;R+3-1RN$~R+11!2'_8!2'_8!2'_8!2'_8!1'a?#>!2'a:5#2!2'g9#>#3!2'_4!1'@#<!2'fV#>#3!1'g:62-1RN$~R+11!1'@!2'_8,6#;2F-^;RN$x;R!1+^;G1!1'gB62$p;RG-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3-1RN$~R+11!2'_4!2'_:HJ!2'a[KJ2-^;RN$x;R!1+^;+C1-1RN$visible;R+17#>2!4'eXXN#5!3'^8+[Z[!2,^<+CX2$c;R+CDE-1RN$~R+11\2-^;RN$x;R!1+^;+C1^12$c;R+CDE-^;RN$x;R!1+^;+C1^12$cL;R+C-^;RN$x;R!1+^;+C1-1RN$visible;R+17#?2!4'eX^A^4#6!3'^8+[!3,_T+[!2,a4^B#6!3,_T+[!2,`[^B#6C!1'^9^A!2,^<+C^A2$cH;R+C2EEFEE^C^D#12$p;R4!1$p;R4-_>RN$p;R!2+_>3+3%H;R!3+^N1-_>RN$p;R!2+_>3+31#11$p0;R3$nhi;R+3-_>RN$p0;R!2+_>+E+31#21$ne;R+E$nlo;R+3-1RN$~R+11!2'_8!2'_8!2'_8!2'_8!1'a?#?!2'a:^E#2!2'g9#?#3!2'_4!1'@#=!2'fV#?#3!1'g:^F2-1RN$~R+11!1'@!2'_8,6#<2^O-^;RN$x;R!1+^;G1!1'gB^F2$p;RG-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3-1RN$~R+11!2'_4!2'_:H^P!2'a[K^P2-^;RN$x;R!1+^;+C1-1RN$visible;R+17#?2!4'eX^T^4#5!3'^8+[^U^V!2,^<+C^T2$c;R+CDE-1RN$~R+11\2-^;RN$x;R!1+^;+C1^X2$c;R+CDE-^;RN$x;R!1+^;+C1^X2$cL;R+C-^;RN$x;R!1+^;+C1-1RN$visible;R+17#@2!4'eX_5^[#6!3'^8+[!3,_T+[!2,a4_6#6!3,_T+[!2,`[_6#6C!1'^9_5!2,^<+C_52$cH;R+C2EE^OE!2,^<0!4,d4+C+C#7#6!3+^N+1!1'gD!1'^9#8,9#11$p;R3$z;R+3!2$p;R3-_>RN$p;R!2+_>+E+3%z;R+3%H;R!3+^N1-_>RN$p0;R!2+_>+E+31#21$ne;R+E$nlo;R+3-1RN$~R+11!2'_8!2'_8!2'_8!2'_8!1'a?#A!2'a:L#2!2'g9#A#3!2'_4!1'@#?!2'fV#A#3!1'g:I2-1RN$~R+11!1'@!2'_8,6#>2_;-^;RN$x;R!1+^;G1!1'gBI2$p;RG-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3-1RN$~R+11!2'_4!2'_:H_=!2'a[K_=2-^;RN$x;R!1+^;+C1-1RN$visible;R+17#A2!4'eX_J_@#5!3'^8+[_L_M!2,^<+C_J2$c;R+CDE-1RN$~R+11\2-^;RN$x;R!1+^;+C1_O2$c;R+CDE-^;RN$x;R!1+^;+C1_O2$cL;R+C-^;RN$x;R!1+^;+C1-1RN$visible;R+17#B2!4'eX`2_R#6!3'^8+[`4!1'^9`2!2,^<+C`22$cH;R+C2EE_;E!2,^<0!4,d4+C+C#;#:!3+^N+1!1'gD!1'^9#<,9#11$e;R+E$z;R+3!2$ne;R+E$nlo;R+3$nhi;R+3$H;R!3+^N1-1RN$~R+11!2'_8!2'_8!2'_8!2'_8!1'a?#B!2'a:^2#3!2'g9#B#1!2'_4!1'@#@!2'fV#B#1!1'g:^62-1RN$~R+11!1'@!2'_8,6#?2`9-^;RN$x;R!1+^;G1!1'gB^62$p;RG-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3-1RN$~R+11!2'_4!2'_:H_U!2'a[`:_U2`>-1RN$~R+11!2'a[^7H2-^;RN$x;R!1+^;+C1`@2$c;R+CDE-^;RN$x;R!1+^;+C1`@2$cL;R+C-^;RN$x;R!1+^;+C1-1RN$visible;R+17#C2!4'eX`K`C#7!3'^8+[!3,_T+[!2,a4`L#7!3,_T+[!2,`[`L#7C!1'^9`K!2,^<+C`K2$cH;R+C2EE`9E!2,^<0!4,d4+C+C#>#=&b;R!2'_8!2'_8!2'_8!2'_8!1'a?#C!2'a:^Y#4!2'g9#C#2!2'_4!1'@#A!2'fV#C#2!1'g:^\+1!1-1RN$b;R+1%H;R!3+^N1-1RN$~R+11#12-1RN$~R+11!1'@!2'_8,6#B2`>-^;RN$x;R!1+^;G1!1'gB_T2$p;RG-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3-1RN$~R+11!2'_4!2'_:H`N!2'a[`O`N2-^;RN$x;R!1+^;+C1-1RN$visible;R+17#E2!4'eX`X`R#9!3'^8+[`Z`[!2,^<+C`X2$c;R+CDE-1RN$~R+11!2'a[`SH2-^;RN$x;R!1+^;+C1a02$c;R+CDE-^;RN$x;R!1+^;+C1a02$cL;R+C-^;RN$x;R!1+^;+C1-1RN$visible;R+17#F2!4'eXa;a3#:!3'^8+[!3,_T+[!2,a4a<#:!3,_T+[!2,`[a<#:C!1'^9a;!2,^<+Ca;2$cH;R+C2EE`>Ea=a>#12$H;R!3+^N1-1RN$~R+11!1'@!2'_8,6#A2a@-^;RN$x;R!1+^;G1!1'gB_<2$p;RG-_>RN$p;R!2+_>+3+31#11$lo;R+3$hi;R+3-1RN$~R+11!2'_4!2'_:HaB!2'a[aCaB2-^;RN$x;R!1+^;+C1-1RN$visible;R+17#D2!4'eXaLaF#8!3'^8+[aNaO!2,^<+CaL2$c;R+CDE-1RN$~R+11!2'a[aGH2-^;RN$x;R!1+^;+C1aQ2$c;R+CDE-^;RN$x;R!1+^;+C1aQ2$cL;R+C-^;RN$x;R!1+^;+C1-1RN$visible;R+17#E2!4'eXaR`R#9!3'^8+[`Z!1'^9aR!2,^<+CaR2$cH;R+C2EEa@aS&o;R`=7!1-^;RN$o;R!1+^;+C%H;R!3+^N1-^;RN$x;R!1+^;+C1#12$c;R+CDEaTaU#12$a;R+C!1$a;R+C$H;R!3+^N1D!2,^<0!4,d4+C+C#D#C&H0;R!6'_J1+C$e;R1-^;RN$o;R!1+^;0+C#12$p;R0-_>RN$p;R!2+_>+C+C+C#11$a;R+C$a;R+C#1#3!2,^<0!4,d4+C+C!1'gA#2#2!2,^<0!4,d4+C+C#E#D#1!3+^N+C#2#D!1&H0;R!6'_J1+C$e;R1-^;RN$o;R!1+^;0+C#12$p;R0-_>RN$p;R!2+_>+C+C+C#11$a;R+C$a;R+C#2!=,N!4'^5!1'KaV!1'FaV!3,_T+[!3,a3!1,H,I!1,^K,_0,I!1'^9#4!1'LaV!1'O#4!1'P#4!1'Q#4!1'R#4!1'S#4!1'T#4!1'U#4!1'V#4!1'W#4!1'X#4!1'Y#4!1'Z#4!2,^<0!4,d4+C+CaW#3!2,^<0!4,d4+C+C#F#E#2!3+^N+CaW#F!1$H;R!3+^N+C!1'gA#4#G!6'_M+C!1'gA#5$csa;R+C%~R!3+^N+C#6#H!3+^N+1!1'gD!1'^9#2,9$_H;R!3+^N+C#5#G!2,^H+1,9#H#1#1#1#1$H;R!3+^N1E!2,^<0!4,d4+C+C#B#A&H0;R!6'_M1EaX,`RaT#1+`M!2'_\aU#1#2$H;R!3+^N1EaS&H0;R!6'_M1EaX,`Ra=#1+`M!2'_\a>#1#2#2#1#2#1#1$H;R!3+^N1E!2,^<0!4,d4+C+C#4#3&H0;R!6'_M1EaX,`R^C#1+`M!2'_\^D#1#2").
Qed.
Lemma node_mmap2_nosplit_contra : forall cs csa csb,
  node_mmap2 false cs = Some (csa, csb) -> kn_contra (kn csa) = true.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SeQ0!2+_>+C+C!1+^;0!2,^<0!4,d4+C+C#2#1!2+_>+3+3!2+_>3+1!1,^20!4'gG#P,fS,6,6-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5655555!4'gG#R,eP,6,6-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5855555!2,^<0#1!2,^<0!4,d4+C+C#5#4!3+^N+1!1'gD!1'^9#6,9!4'gG#Q,fS,6,6-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5=55555!4'gG#S,eP,6,6-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5?55555-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5!4'gG#S,fS,6,655555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5!4'gG#U,eP,6,655555!2,^<0!4,d4+C+C#;#:!3+^N+1!1'gD!1'^9#<,9!4'gG#T,fS,6,6-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5E55555!4'gG#V,eP,6,6-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5G55555!2,^<0!4,d4+C+C#>#=-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5!4'gG#U,fS,6,655555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5!4'gG#W,eP,6,655555-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5!4'gG#V,fS,6,655555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5!4'gG#X,eP,6,655555-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5!4'gG#X,fS,6,655555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5!4'gG#Z,eP,6,655555!2,^<0!4,d4+C+C#C#B!3+^N+1!1'gD!1'^9#D,9-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5!4'gG#Z,fS,6,655555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5!4'gG#\,eP,6,655555!2,^<0!4,d4+C+C#E#D!4'gG#^0,fS,6,6-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5U55555!4'gG#W,fS,6,6!4'gG#^2,eP,6,6-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5X55555!4'gG#Y,eP,6,6!2,^<0!4,d4+C+C#H#G-_>RN$p;R!2+_>+C+C+C#11$a;R+C$a;R+C#1!2,^<0!4,d4+C+C#4#3!2,^<0!4,d4+C+C#I#H-_>RN$p;R!2+_>+C+C+C#11$a;R+C$a;R+C#2!2,^<0!4,d4+C+C#J#I!3+^N+C#6#K!3+^N+1!1'gD!1'^9#2,9-3RN$flags;R+31#B35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^1,fS,6,655555555$p5;R+_I5!5'g8,6#U,fR,6,6555$p1;R+_I555$p;R+_I5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5!4'gG#^7,fS,6,655555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5!4'gG#^9,eP,6,655555!2,^<0!4,d4+C+C#9#8!2,^<0!4,d4+C+C#8#7-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#E35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^4,eP,6,955555555$p7;R+_I5!5'g8,6#X,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55!2,^<0!4,d4+C+C#:#9!3+^N+1!1'gD!1'^9#;,9-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^3,fS,6,655555555$p5;R+_I5!5'g8,6#W,fR,6,6555$p1;R+_I555$e;R1-^;RN$o;R!1+^;0w#12$~R0+`M+`Q$Hg;R!3+^N15^<&H;R!6'_M15^?,`RC#1+`M!2'_\D#1!2,^<0!4,d4+C+C#<#;-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^5,fS,6,655555555$p5;R+_I5!5'g8,6#Y,fR,6,6555$p1;R+_I55!3+^N+1!1'gD!1'^9#?,9!2,^<0!4,d4+C+C#?#>!2,^<0!4,d4+C+C#@#?!3+^N+1!1'gD!1'^9#A,9!1$p;R+_I$Hg;R!3+^N15^D&H;R!6'_M15^?,`R^E#1+`M!2'_\^F#1#1-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^7,fS,6,655555555$p5;R+_I5!5'g8,6#[,fR,6,6555!2,^<0!4,d4+C+C#A#@!3+^N+1!1'gD!1'^9#B,9!2,^<0!4,d4+C+C#B#A-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^9,fS,6,655555555$p5;R+_I5!5'g8,6#^0,fR,6,655!2,^<0!4,d4+C+C#D#C!3+^N+1!1'gD!1'^9#E,9!2,^<0!4,d4+C+C#F#E!1$p;R+_I$Hg;R!3+^N15T&H;R!6'_M15^?,`R^O#1+`M!2'_\!3+^N+1!1'gD!1'^9#G,9#1#1-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^;,fS,6,655555555$p5;R+_I5!5'g8,6#^2,fR,6,65!2,^<0!4,d4+C+C#G#F!3+^N+1!1'gD!1'^9#H,9!1$p;R+_I$Hg;R!3+^N15[&H;R!6'_M15^?,`R^1#1+`M!2'_\!3+^N+1!1'gD!1'^9#J,9#1#1-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^=,fS,6,655555555$p5;R+_I5!5'g8,6#^4,fR,6,6!3+^N+1!1'gD!1'^9#K,9!2,^<0!4,d4+C+C#K#J!2,^<0!4,d4+C+C#L#K!1$p;R+_I$Hg;R!3+^N15^W&H;R!6'_M15^?,`R^X#1+`M!2'_\!3+^N+1!1'gD!1'^9#M,9#1#1-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^?,fS,6,655555555!2,^<0!4,d4+C+C#M#L!3+^N+1!1'gD!1'^9#N,9!2,^<0!4,d4+C+C#N#M-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^A,fS,6,65555555!2,^<0!4,d4+C+C#P#O!3+^N+1!1'gD!1'^9#Q,9!2,^<0!4,d4+C+C#Q#P!2,^<0!4,d4+C+C#R#Q!1$p;R+_I$Hg;R!3+^N15_4&H;R!6'_M15^?,`R_5#1+`M!2'_\!3+^N+1!1'gD!1'^9#S,9#1#1-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^C,fS,6,6555555!2,^<0!4,d4+C+C#S#R!3+^N+1!1'gD!1'^9#T,9!2,^<0!4,d4+C+C#T#S!2,^<0!4,d4+C+C#U#T!3+^N+1!1'gD!1'^9#V,9$Hg;R!3+^N15_:&H;R!6'_M15^?,`R_;#1+`M!2'_\_<#1!1$p;R+_I_=#1-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^E,fS,6,655555!2,^<0!4,d4+C+C#V#U!3+^N+1!1'gD!1'^9#W,9!2,^<0!4,d4+C+C#W#V!2,^<0!4,d4+C+C#X#W!1$p;R+_I$Hg;R!3+^N15_B&H;R!6'_M15^?,`R_C#1+`M!2'_\!3+^N+1!1'gD!1'^9#Y,9#1#1-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^G,fS,6,65555!2,^<0!4,d4+C+C#Y#X!3+^N+1!1'gD!1'^9#Z,9!2,^<0!4,d4+C+C#Z#Y!2,^<0!4,d4+C+C#[#Z!1$p;R+_I$Hg;R!3+^N15_H&H;R!6'_M15^?,`R_I#1+`M!2'_\!3+^N+1!1'gD!1'^9#\,9#1#1-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^I,fS,6,6555!2,^<0!4,d4+C+C#\#[!3+^N+1!1'gD!1'^9#^0,9!2,^<0!4,d4+C+C#^0#\!2,^<0!4,d4+C+C#^1#^0!1$p;R+_I$Hg;R!3+^N15_N&H;R!6'_M15^?,`R_O#1+`M!2'_\!3+^N+1!1'gD!1'^9#^2,9#1#1-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^K,fS,6,655!2,^<0!4,d4+C+C#^2#^1!3+^N+1!1'gD!1'^9#^3,9!2,^<0!4,d4+C+C#^3#^2!2,^<0!4,d4+C+C#^4#^3!1$p;R+_I$Hg;R!3+^N15_T&H;R!6'_M15^?,`R_U#1+`M!2'_\!3+^N+1!1'gD!1'^9#^5,9#1#1-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^M,fS,6,65!2,^<0!4,d4+C+C#^5#^4!3+^N+1!1'gD!1'^9#^6,9!2,^<0!4,d4+C+C#^6#^5!2,^<0!4,d4+C+C#^7#^6!1$p;R+_I$Hg;R!3+^N15_Z&H;R!6'_M15^?,`R_[#1+`M!2'_\!3+^N+1!1'gD!1'^9#^8,9#1#1-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^O,fS,6,6!2,^<0!4,d4+C+C#^8#^7!3+^N+1!1'gD!1'^9#^9,9!2,^<0!4,d4+C+C#^9#^8!2,^<0!4,d4+C+C#^:#^9!1$p;R+_I$Hg;R!3+^N15`3&H;R!6'_M15^?,`R`4#1+`M!2'_\!3+^N+1!1'gD!1'^9#^;,9#1#1!2,^<0!4,d4+C+C#^;#^:!3+^N+1!1'gD!1'^9#^<,9!2,^<0!4,d4+C+C#^<#^;!2,^<0!4,d4+C+C#^=#^<!3+^N+1!1'gD!1'^9#^>,9$Hg;R!3+^N15`8&H;R!6'_M15^?,`R`9#1+`M!2'_\`:#1!1$p;R+_I`;#1$Hg;R!3+^N15_[&H;R!6'_M15^?,`R`1#1+`M!2'_\`2#1$Hg;R!3+^N15_U&H;R!6'_M15^?,`R_X#1+`M!2'_\_Y#1$Hg;R!3+^N15_O&H;R!6'_M15^?,`R_R#1+`M!2'_\_S#1$Hg;R!3+^N15_I&H;R!6'_M15^?,`R_L#1+`M!2'_\_M#1$Hg;R!3+^N15_C&H;R!6'_M15^?,`R_F#1+`M!2'_\_G#1$Hg;R!3+^N15_;&H;R!6'_M15^?,`R_@#1+`M!2'_\_A#1$Hg;R!3+^N15_5&H;R!6'_M15^?,`R_8#1+`M!2'_\_9#1!2,^<0!4,d4+C+C#O#N$Hg;R!3+^N15`D&H;R!6'_M15^?,`R_2#1+`M!2'_\_3#1!3+^N+1!1'gD!1'^9#P,9$Hg;R!3+^N15_0&H;R!6'_M15^?,`R`D#1+`M!2'_\`F#1!1$p;R+_I`G#1$Hg;R!3+^N15^1&H;R!6'_M15^?,`R^3#1+`M!2'_\^V#1$Hg;R!3+^N15^O&H;R!6'_M15^?,`R^R#1+`M!2'_\^S#1$Hg;R!3+^N15P&H;R!6'_M15^?,`R^M#1+`M!2'_\^N#1!3+^N15^K!6'_M15^?,`RP#1!2'_\Q#1!1$p;R+_I$Hg;R`L&H;R`M+`M`N#1$Hg;R!3+^N15^E&H;R!6'_M15^?,`R^I#1+`M!2'_\^J#1!2,^<0!4,d4+C+C#=#<$Hg;R!3+^N15`Q&H;R!6'_M15^?,`RI#1+`M!2'_\^C#1!3+^N+1!1'gD!1'^9#>,9$Hg;R!3+^N15^A&H;R!6'_M15^?,`R`Q#1+`M!2'_\`S#1!1$p;R+_I`T#1-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#G35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^6,eP,6,955555555$p7;R+_I5!5'g8,6#Z,fQ,9,9555$p3;R+_I555$p1;R+_I5!1$p;R+_I$Hg;R!3+^N15^I&H;R!6'_M15^?,`R^K#1+`M!2'_\!3+^N+1!1'gD!1'^9#C,9#1#1-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^9,eP,6,955555555$p7;R+_I5!5'g8,6#^0,fQ,9,9555$p3;R+_I555-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^;,eP,6,955555555$p7;R+_I5!5'g8,6#^2,fQ,9,9555$p3;R+_I55-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^=,eP,6,955555555$p7;R+_I5!5'g8,6#^4,fQ,9,9555-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^?,eP,6,955555555$p7;R+_I5!5'g8,6#^6,fQ,9,955-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^A,eP,6,955555555$p7;R+_I5!5'g8,6#^8,fQ,9,95-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^C,eP,6,955555555$p7;R+_I5!5'g8,6#^:,fQ,9,9-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^E,eP,6,955555555-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^G,eP,6,95555555-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^I,eP,6,9555555-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^K,eP,6,955555-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^M,eP,6,95555-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^O,eP,6,9555-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^Q,eP,6,955-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^S,eP,6,95-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^U,eP,6,9!2,^<0!4,d4+C+C#^>#^=!3+^N+1!1'gD!1'^9#^?,9!2,^<0!4,d4+C+C#^?#^>!2,^<0!4,d4+C+C#^@#^?!1$p;R+_I$Hg;R!3+^N15a<&H;R!6'_M15^?,`Ra=#1+`M!2'_\!3+^N+1!1'gD!1'^9#^A,9#1#1!2,^<0!4,d4+C+C#^A#^@!3+^N+1!1'gD!1'^9#^B,9!2,^<0!4,d4+C+C#^B#^A!2,^<0!4,d4+C+C#^C#^B!3+^N+1!1'gD!1'^9#^D,9$Hg;R!3+^N15aA&H;R!6'_M15^?,`RaB#1+`M!2'_\aC#1!1$p;R+_IaD#1$Hg;R!3+^N15`9&H;R!6'_M15^?,`Ra:#1+`M!2'_\a;#1$Hg;R!3+^N15`4&H;R!6'_M15^?,`R`6#1+`M!2'_\`7#1$Hg;R!3+^N15^X&H;R!6'_M15^?,`R^[#1+`M!2'_\^\#1!1$p;R+_I$Hg;R!3+^N15I&H;R!6'_M15^?,`R^D#1+`M!2'_\!3+^N+1!1'gD!1'^9#@,9#1#1!1$p;R+_I$Hg;R!3+^N15C&H;R!6'_M15^?,`R^A#1+`M!2'_\!3+^N+1!1'gD!1'^9#=,9#1#1-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5!4'gG#^6,fS,6,655555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5!4'gG#^8,eP,6,655555!2,^<0!4,d4+C+C!1'gA#1#1-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^8,fS,6,62$c;R+CaM555555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^:,eP,6,62$c;R+CaM555555-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#E35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IaO$p16;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^4,eP,6,62$c;R+CaM555555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#X,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IaO$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55-^;RN$x;R!1+^;+C1!4'gI#^7,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5aQ55555-^;RN$x;R!1+^;+C1!4'gI#^9,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5aS55555-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaT$p14;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^3,fS,6,62$c;R+CaM555555555$p5;R+_I5-^;RN$x;R!1+^;+C1!4'gI#W,fR,6,62$c;R+CaM5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaT$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555-^;RN$x;R!1+^;+C1!4'gI#^;,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5aV55555-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaW$p14;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^5,fS,6,62$c;R+CaM555555555$p5;R+_I5-^;RN$x;R!1+^;+C1!4'gI#Y,fR,6,62$c;R+CaM5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaW$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I55-^;RN$x;R!1+^;+C1!4'gI#^=,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5aY55555-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaZ$p14;R+_I5aQ55555555$p5;R+_I5-^;RN$x;R!1+^;+C1!4'gI#[,fR,6,62$c;R+CaM5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaZ$p14;R+_I5555555555$p5;R+_I55555-^;RN$x;R!1+^;+C1!4'gI#^?,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5a\55555-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib0$p14;R+_I5aS55555555$p5;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^0,fR,6,62$c;R+CaM5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib0$p14;R+_I5555555555$p5;R+_I5555-^;RN$x;R!1+^;+C1!4'gI#^A,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5b255555-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib3$p14;R+_I5aV55555555$p5;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^2,fR,6,62$c;R+CaM5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib3$p14;R+_I5555555555$p5;R+_I555-^;RN$x;R!1+^;+C1!4'gI#^C,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5b555555-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib6$p14;R+_I5aY55555555$p5;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^4,fR,6,62$c;R+CaM5-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib6$p14;R+_I5555555555$p5;R+_I55-^;RN$x;R!1+^;+C1!4'gI#^E,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5b955555-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib:$p14;R+_I5a\55555555!4'gI#^6,fR,6,6-^;RN$x;R!1+^;+C1!4'gI#^G,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5b=55555-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib>$p14;R+_I5b25555555-^;RN$x;R!1+^;+C1!4'gI#^I,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5b@55555-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbA$p14;R+_I5b5555555-^;RN$x;R!1+^;+C1!4'gI#^K,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5bC55555-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbD$p14;R+_I5b955555-^;RN$x;R!1+^;+C1!4'gI#^M,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5bF55555-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbG$p14;R+_I5b=5555-^;RN$x;R!1+^;+C1!4'gI#^O,fS,6,62$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5bI55555-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbJ$p14;R+_I5b@555!4'gI#^Q,fS,6,6-^;RN$x;R!1+^;+C1bL2$c;R+CaM5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5bM55555-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbN$p14;R+_I5bC55-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^S,fS,6,62$c;R+CaM555555-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbP$p14;R+_I5bF5-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^U,fS,6,62$c;R+CaM555555-_IRN$p13;R+_I1#13$p14;R+_IbR$p14;R+_I5bI-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^W,fS,6,62$c;R+CaM555555-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^Y,fS,6,62$c;R+CaM55555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^[,fS,6,62$c;R+CaM5555-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_0,fS,6,62$c;R+CaM555!2,^<0!4,d4+C+C#^D#^C!3+^N+1!1'gD!1'^9#^E,9!2,^<0!4,d4+C+C#^E#^D!2,^<0!4,d4+C+C#^F#^E!1$p;R+_I$Hg;R!3+^N15bZ&H;R!6'_M15^?,`Rb[#1+`M!2'_\!3+^N+1!1'gD!1'^9#^G,9#1#1-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_2,fS,6,62$c;R+CaM55!2,^<0!4,d4+C+C#^G#^F!3+^N+1!1'gD!1'^9#^H,9!2,^<0!4,d4+C+C#^H#^G!2,^<0!4,d4+C+C#^I#^H!1$p;R+_I$Hg;R!3+^N15c3&H;R!6'_M15^?,`Rc4#1+`M!2'_\!3+^N+1!1'gD!1'^9#^J,9#1#1-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_4,fS,6,62$c;R+CaM5!2,^<0!4,d4+C+C#^J#^I!3+^N+1!1'gD!1'^9#^K,9!2,^<0!4,d4+C+C#^K#^J!2,^<0!4,d4+C+C#^L#^K!1$p;R+_I$Hg;R!3+^N15c9&H;R!6'_M15^?,`Rc:#1+`M!2'_\!3+^N+1!1'gD!1'^9#^M,9#1#1!4'gI#_6,fS,6,6!2,^<0!4,d4+C+C#^M#^L!3+^N+1!1'gD!1'^9#^N,9!2,^<0!4,d4+C+C#^N#^M!2,^<0!4,d4+C+C#^O#^N!3+^N+1!1'gD!1'^9#^P,9$Hg;R!3+^N15c?&H;R!6'_M15^?,`Rc@#1+`M!2'_\cA#1!1$p;R+_IcB#1!1+^;+C-^;RN$x;R!1+^;+C1#12$c;R+CaM5!2,^<0!4,d4+C+C#^P#^O$e;R1-^;RN$o;R!1+^;0+C#12$p;R0\#3!2,^<0!4,d4+C+C!1'gA#2#2!2,^<0!4,d4+C+C#^Q#^P!1'G#4$e;R1-^;RN$o;R!1+^;0+C#12$p;R0^2!=,N!4'^5!1'KcJ!1'FcJ!3,_T+[!3,a3!1,H,I!1,^K,_0,I!1'^9#4!1'LcJ!1'O#4!1'P#4!1'Q#4!1'R#4!1'S#4!1'T#4!1'U#4!1'V#4!1'W#4!1'X#4!1'Y#4!1'Z#4!1'gA#3!2,^<0!4,d4+C+CcL#3!2,^<0!4,d4+C+C#^R#^Q!1'gA#4!1'gA#5!2,^H+1,9$Hg;R!3+^N15c4&H;R!6'_M15^?,`Rc7#1+`M!2'_\c8#1$Hg;R!3+^N15b[&H;R!6'_M15^?,`Rc1#1+`M!2'_\c2#1$Hg;R!3+^N15aB&H;R!6'_M15^?,`RbX#1+`M!2'_\bY#1$Hg;R!3+^N15a=&H;R!6'_M15^?,`Ra?#1+`M!2'_\a@#1!1$p;R+_I$Hg;R!3+^N1bT`8!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_IbU5a:a;#23$p;R+_Ia>$p;R+_I!1$p;R+_I$Hg;R!3+^N1bUa<!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_IbV5a?a@#23$p;R+_IaE$p;R+_I!1$p;R+_I$Hg;R!3+^N1bVaA!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_IbW5bXbY#23$p;R+_Ib\$p;R+_I!1$p;R+_I$Hg;R!3+^N1bWbZ!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_Ic05c1c2#23$p;R+_Ic5$p;R+_I!1$p;R+_I$Hg;R!3+^N1c0c3!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_Ic65c7c8#23$p;R+_Ic;$p;R+_I!1$p;R+_I$Hg;R!3+^N1c6c9!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5-^;RN$x;R!1+^;+C1c<2$c;R+CaM5c=c>#23$p;R+_IcC$p;R+_IcC$Hg;R!3+^N1-^;RN$x;R!1+^;+C1!4'gI#_5,fS,6,62$c;R+CaM5c:&o;Rc<cD!1-^;RN$o;R!1+^;+C%Hg;R!3+^N1cEc@cA#12$a;R+C!1$a;R+C$Hg;R!3+^N1aMcF&H;R!6'_J1+CcGcHcI#1!3+^N+C#2#^P!1&H;R!6'_J1+CcKcMcN#2!3+^N+CcL#^R!1$H;R!3+^N+CcO#^S!6'_M+CcP$ga;R+C%~R!3+^N+C#6#^T^5$H;R!3+^N+C#5#^ScQ#^T#1#1#1#1cB#2#1#1cR#1#1cS#1#1cT#1#1cU#1#1aF#1#1-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib:$p14;R+_I5555555555-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_Ib>$p14;R+_I555555555-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbA$p14;R+_I55555555-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbD$p14;R+_I5555555-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbG$p14;R+_I555555-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbJ$p14;R+_I55555-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbN$p14;R+_I5555-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IbP$p14;R+_I555-_IRN$p13;R+_I1#13$p14;R+_IbR$p14;R+_I55-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^<,eP,6,62$c;R+CaM555555-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#G35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id3$p16;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^6,eP,6,62$c;R+CaM555555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#Z,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id3$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^>,eP,6,62$c;R+CaM555555-^;RN$x;R!1+^;+C1!4'gI#^=,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5d655555-^;RN$x;R!1+^;+C1!4'gI#^?,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5d855555-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id9$p16;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^9,eP,6,62$c;R+CaM555555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^0,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id9$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555-^;RN$x;R!1+^;+C1!4'gI#^A,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5d;55555-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id<$p16;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^;,eP,6,62$c;R+CaM555555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^2,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id<$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I55-^;RN$x;R!1+^;+C1!4'gI#^C,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5d>55555-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id?$p16;R+_I5d655555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^4,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id?$p16;R+_I5555555555$p7;R+_I55555-^;RN$x;R!1+^;+C1!4'gI#^E,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5dA55555-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdB$p16;R+_I5d855555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^6,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdB$p16;R+_I5555555555$p7;R+_I5555-^;RN$x;R!1+^;+C1!4'gI#^G,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5dD55555-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdE$p16;R+_I5d;55555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^8,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdE$p16;R+_I5555555555$p7;R+_I555-^;RN$x;R!1+^;+C1!4'gI#^I,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5dG55555-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdH$p16;R+_I5d>55555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^:,fQ,9,92$c;R+CaM5-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdH$p16;R+_I5555555555$p7;R+_I55-^;RN$x;R!1+^;+C1!4'gI#^K,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5dK55555-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdL$p16;R+_I5dA55555555!4'gI#^<,fQ,9,9-^;RN$x;R!1+^;+C1!4'gI#^M,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5dO55555-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdP$p16;R+_I5dD5555555-^;RN$x;R!1+^;+C1!4'gI#^O,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5dR55555-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdS$p16;R+_I5dG555555-^;RN$x;R!1+^;+C1!4'gI#^Q,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5dU55555-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdV$p16;R+_I5dK55555-^;RN$x;R!1+^;+C1!4'gI#^S,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5dX55555-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdY$p16;R+_I5dO5555-^;RN$x;R!1+^;+C1!4'gI#^U,eP,6,62$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5d[55555-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id\$p16;R+_I5dR555!4'gI#^W,eP,6,6-^;RN$x;R!1+^;+C1e12$c;R+CaM5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5e255555-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Ie3$p16;R+_I5dU55-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^Y,eP,6,62$c;R+CaM555555-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Ie5$p16;R+_I5dX5-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^[,eP,6,62$c;R+CaM555555-_IRN$p15;R+_I1#13$p16;R+_Ie7$p16;R+_I5d[-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_0,eP,6,62$c;R+CaM555555-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_2,eP,6,62$c;R+CaM55555-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_4,eP,6,62$c;R+CaM5555-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_6,eP,6,62$c;R+CaM555-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_8,eP,6,62$c;R+CaM55-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1!4'gI#_:,eP,6,62$c;R+CaM5!3+^N+1!1'gD!1'^9#^Q,9!4'gI#_<,eP,6,6!2,^<0!4,d4+C+C#^U#^T!3+^N+1!1'gD!1'^9#^V,9$Hg;R!3+^N15!2,^<0!4,d4+C+C#^T#^S&H;R!6'_M15^?,`ReA#1+`M!2'_\eB#1!1$p;R+_IeC#1!1$p;R+_I$Hg;R!3+^N1e9aA!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_Ie:5bXbY#23$p;R+_Ib\$p;R+_I!1$p;R+_I$Hg;R!3+^N1e:bZ!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_Ie;5c1c2#23$p;R+_Ic5$p;R+_I!1$p;R+_I$Hg;R!3+^N1e;c3!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_Ie<5c7c8#23$p;R+_Ic;$p;R+_I!1$p;R+_I$Hg;R!3+^N1e<c9!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_Ie=5c=c>#23$p;R+_IcC$p;R+_I!1$p;R+_I$Hg;R!3+^N1e=c?!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_Ie>5cFe?#23$p;R+_I!1$p;R+_I$Hg;R!3+^N15cI&H;R!6'_M15^?,`RcN#1+`M!2'_\!3+^N+1!1'gD!1'^9#^S,9#1#1$p;R+_I!1$p;R+_I$Hg;R!3+^N1e>cI!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5-^;RN$x;R!1+^;+C1e@2$c;R+CaM5!2,^<0!4,d4+C+C#^S#^R!3+^N+1!1'gD!1'^9#^T,9#23$p;R+_IeD$p;R+_IeD$Hg;R!3+^N1-^;RN$x;R!1+^;+C1!4'gI#_;,eP,6,62$c;R+CaM5cN&o;Re@cD!1-^;RN$o;R!1+^;+C%Hg;R!3+^N1cEeAeB#12$a;R+C!1$a;R+C$Hg;R!3+^N1aM!2,^<0!4,d4+C+C#^V#^U&H;R!6'_J1+CcGcH!2,^<0!4,d4+C+C#^W#^V#1!3+^N+C#2#^V!1&H;R!6'_J1+CcKcM!2,^<0!4,d4+C+C#^X#^W#2!3+^N+CcL#^X!1$H;R!3+^N+CcO#^Y!6'_M+CcP$ga;R+C%~R!3+^N+C#6#^Z^5$H;R!3+^N+C#5#^YcQ#^Z#1#1#1#1eC#2#1#1$Hg;R!3+^N15c@&H;R!6'_M15^?,`RcF#1+`M!2'_\e?#1#1#1$Hg;R!3+^N15c:&H;R!6'_M15^?,`Rc=#1+`M!2'_\c>#1#1#1cR#1#1cS#1#1cT#1#1-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdL$p16;R+_I5555555555-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdP$p16;R+_I555555555-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdS$p16;R+_I55555555-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdV$p16;R+_I5555555-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IdY$p16;R+_I555555-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id\$p16;R+_I55555-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Ie3$p16;R+_I5555-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Ie5$p16;R+_I555-_IRN$p15;R+_I1#13$p16;R+_Ie7$p16;R+_I55-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I5W55555-_IRN$p16;R+_I1#13$p17;R+_I5$p17;R+_I-_IRN$p17;R+_I1#13$p18;R+_I5$p18;R+_I-_IRN$p18;R+_I1#13$p19;R+_I5$p19;R+_I-_IRN$p19;R+_I1#13$p20;R+_I5$p20;R+_I-_IRN$p20;R+_I1#13$p21;R+_I5$p21;R+_I-_IRN$p21;R+_I1#13$p22;R+_I5$p22;R+_I5Z55555$cs;R+C$csa;R+C$csb;R+C$H;R!3+^N1!2'gE,6#32&o;R!1'gF#4!1+^;4!1-^;RN$o;R!1+^;4%H;R!3+^N1-^;RN$x;R!1+^;41#12$p;R4-_>RN$p;R!2+_>3+11#11$p0;R3$isnull;R+1-_>RN$p0;R!2+_>+3+31#21$prot;R+3$flags;R+3-^;RN$g;R!1+^;01-1RN$isnull;R+11#32-3RN$prot;R+31#23-3RN$flags;R+31#135$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#J,fS,6,655555555$p5;R+_I5!5'g8,6#A,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#335$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#L,eP,6,955555555$p7;R+_I5!5'g8,6#C,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#23-3RN$flags;R+31#135$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I7$p14;R+_I5!4'gG#J,fS,6,655555555$p5;R+_I5!4'gG#A,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I7$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#335$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I9$p16;R+_I5!4'gG#L,eP,6,655555555$p7;R+_I5!4'gG#C,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I9$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I52$p;R0:55;<#12$p;R4!1$p;R4-_>RN$p;R!2+_>3+1%H;R!3+^N1-_>RN$p;R!2+_>3+11#11$p0;R3$isnull;R+1-_>RN$p0;R!2+_>+3+31#21$prot;R+3$flags;R+3-^;RN$g;R!1+^;01-1RN$isnull;R+11#32-3RN$prot;R+31#23-3RN$flags;R+31#135$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#K,fS,6,655555555$p5;R+_I5!5'g8,6#B,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#335$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#M,eP,6,955555555$p7;R+_I5!5'g8,6#D,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#23-3RN$flags;R+31#135$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I>$p14;R+_I5!4'gG#K,fS,6,655555555$p5;R+_I5!4'gG#B,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I>$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#335$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I@$p16;R+_I5!4'gG#M,eP,6,655555555$p7;R+_I5!4'gG#D,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I@$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I52$p;R0:5!2,^<0!4,d4+C+C#7#6!3+^N+1!1'gD!1'^9#8,9#11$p;R3$b;R+1!2$p;R3-_>RN$p;R!2+_>+3+3%b;R+1%H;R!3+^N1-_>RN$p0;R!2+_>+3+31#21$prot;R+3$flags;R+3-^;RN$g;R!1+^;01-1RN$isnull;R+11#32-3RN$prot;R+31#23-3RN$flags;R+31#135$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#M,fS,6,655555555$p5;R+_I5!5'g8,6#D,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#335$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#O,eP,6,955555555$p7;R+_I5!5'g8,6#F,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#23-3RN$flags;R+31#135$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IA$p14;R+_I5!4'gG#M,fS,6,655555555$p5;R+_I5!4'gG#D,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IA$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#335$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IB$p16;R+_I5!4'gG#O,eP,6,655555555$p7;R+_I5!4'gG#F,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IB$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I52$p;R0:5CD#11$z;R+3$z;R+3!2$prot;R+3$flags;R+3$isnull;R+1$H;R!3+^N1-^;RN$g;R!1+^;01-1RN$isnull;R+11#12-3RN$prot;R+31#33-3RN$flags;R+31#235$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#N,fS,6,655555555$p5;R+_I5!5'g8,6#E,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#435$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#P,eP,6,955555555$p7;R+_I5!5'g8,6#G,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#33-3RN$flags;R+31#235$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IF$p14;R+_I5!4'gG#N,fS,6,655555555$p5;R+_I5!4'gG#E,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IF$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#435$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IH$p16;R+_I5!4'gG#P,eP,6,655555555$p7;R+_I5!4'gG#G,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IH$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I52$p;R0:5I&o;R-1RN$isnull;R+11#22-3RN$prot;R+31#43-3RN$flags;R+31#335$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#O,fS,6,655555555$p5;R+_I5!5'g8,6#F,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#535$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#Q,eP,6,955555555$p7;R+_I5!5'g8,6#H,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#43-3RN$flags;R+31#335$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IJ$p14;R+_I5!4'gG#O,fS,6,655555555$p5;R+_I5!4'gG#F,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IJ$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#535$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IK$p16;R+_I5!4'gG#Q,eP,6,655555555$p7;R+_I5!4'gG#H,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IK$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I51&Hg;R!2,^H1#1!3+^N1-1RN$isnull;R+11#32-3RN$prot;R+31#53-3RN$flags;R+31#435$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#P,fS,6,655555555$p5;R+_I5!5'g8,6#G,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#635$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#R,eP,6,955555555$p7;R+_I5!5'g8,6#I,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#53-3RN$flags;R+31#435$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IL$p14;R+_I5655555555$p5;R+_I5!4'gG#G,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IL$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#635$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IM$p16;R+_I5855555555$p7;R+_I5!4'gG#I,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IM$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5#1!2-^;RN$o;R!1+^;0%Hg;R!3+^N1-1RN$isnull;R+11#52-3RN$prot;R+31#73-3RN$flags;R+31#635$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#R,fS,6,655555555$p5;R+_I5!5'g8,6#I,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#835$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#T,eP,6,955555555$p7;R+_I5!5'g8,6#K,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#73-3RN$flags;R+31#635$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IN$p14;R+_I5!4'gG#R,fS,6,655555555$p5;R+_I5!4'gG#I,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IN$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#835$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IO$p16;R+_I5!4'gG#T,eP,6,655555555$p7;R+_I5!4'gG#K,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IO$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5#1%H;R!3+^N1-^;RN$g;R!1+^;01#22$p;R0:5PQ#22$p;R0!1$p;R0-_>RN$p;R!2+_>+C+C%Hg;R!3+^N1-1RN$isnull;R+11#72-3RN$prot;R+31#93-3RN$flags;R+31#835$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#T,fS,6,655555555$p5;R+_I5!5'g8,6#K,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#:35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#V,eP,6,955555555$p7;R+_I5!5'g8,6#M,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#93-3RN$flags;R+31#835$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IR$p14;R+_I5E55555555$p5;R+_I5!4'gG#K,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IR$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#:35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IS$p16;R+_I5G55555555$p7;R+_I5!4'gG#M,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IS$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5:%H;R!3+^N1!2,^<0#2T!3+^N+1!1'gD!1'^9#F,9#11$a;R+C$a;R+C!2$ga;R+C$gb;R+C$Hg;R!3+^N1-1RN$isnull;R+11#:2-3RN$prot;R+31#<3-3RN$flags;R+31#;35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#W,fS,6,655555555$p5;R+_I5!5'g8,6#N,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#=35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#Y,eP,6,955555555$p7;R+_I5!5'g8,6#P,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#<3-3RN$flags;R+31#;35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IV$p14;R+_I5W55555555$p5;R+_I5!4'gG#N,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IV$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#=35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IY$p16;R+_I5Z55555555$p7;R+_I5!4'gG#P,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IY$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I52$H;R!3+^N1!2,^<0!4,d4+C+C#3#2[&H0;R!6'_J1+C$e;R1-^;RN$o;R!1+^;0+C#12$p;R0\#4^0^1#1!3+^N+C#3#H!1&H0;R!6'_J1+C$e;R1-^;RN$o;R!1+^;0+C#12$p;R0^2#6;^3#2!3+^N+C#5#J!1$H;R^4!6'_M+C#7$csa;R+C%~R!3+^N+C#7#L^5$H;R^4!1-1RN$b;R+1%Hg;R!3+^N1-1RN$isnull;R+11#12-3RN$prot;R+31#C3^6$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#D35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^3,eP,6,955555555$p7;R+_I5!5'g8,6#W,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#C3-3RN$flags;R+31#B35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I^7$p14;R+_I5!4'gG#^1,fS,6,655555555$p5;R+_I5!4'gG#U,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I^7$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#D35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I^8$p16;R+_I5!4'gG#^3,eP,6,655555555$p7;R+_I5!4'gG#W,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I^8$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5^9!3+^N+1!1'gD!1'^9#:,9#@2$Hg;R!3+^N1-3RN$prot;R+31#B3-3RN$flags;R+31#A35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^0,fS,6,655555555$p5;R+_I5!5'g8,6#T,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#C35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^2,eP,6,955555555$p7;R+_I5!5'g8,6#V,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5^:!1-3RN$z;R+3%Hg;R!3+^N1-3RN$prot;R+31#13-3RN$flags;R+31#C35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^2,fS,6,655555555$p5;R+_I5!5'g8,6#V,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I^;$p;R+_I5^<^=#C3$Hg;R!3+^N1^6^9!1-3RN$z;R+3%Hg;R!3+^N1-3RN$flags;R+31#135$p;R+_I^>$p;R+_I5CD#C3^@$p;R+_I!1$p;R+_I$Hg;R!3+^N1^>^A!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I^B5I^C#23$p;R+_I^G$p;R+_I!1$p;R+_I$Hg;R!3+^N1^B^D!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p0;R+_I1#13$p1;R+_I^H$p1;R+_I55^I^J#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1^H^K!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I^L5^M^N#23$p;R+_I^P$p;R+_I!1$p;R+_I$Hg;R!3+^N1^LT!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I^Q5^R^S#23$p;R+_I^T$p;R+_I!1$p;R+_I$Hg;R!3+^N1^Q[!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I^U5^3^V#23$p;R+_I^Y$p;R+_I!1$p;R+_I$Hg;R!3+^N1^U^W!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p4;R+_I1#13$p5;R+_I^Z$p5;R+_I5!5'g8,6#^6,fR,6,6^[^\#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1^Z_0!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I_15_2_3#23$p;R+_I_6$p;R+_I!1$p;R+_I$Hg;R!3+^N1_1_4!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I_75_8_9#23$p;R+_I_>$p;R+_I!1$p;R+_I$Hg;R!3+^N1_7_:!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I_?5_@_A#23$p;R+_I_D$p;R+_I!1$p;R+_I$Hg;R!3+^N1_?_B!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I_E5_F_G#23$p;R+_I_J$p;R+_I!1$p;R+_I$Hg;R!3+^N1_E_H!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I_K5_L_M#23$p;R+_I_P$p;R+_I!1$p;R+_I$Hg;R!3+^N1_K_N!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I_Q5_R_S#23$p;R+_I_V$p;R+_I!1$p;R+_I$Hg;R!3+^N1_Q_T!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I_W5_X_Y#23$p;R+_I_\$p;R+_I!1$p;R+_I$Hg;R!3+^N1_W_Z!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I`05`1`2#23$p;R+_I`5$p;R+_I!1$p;R+_I$Hg;R!3+^N1`0`3!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#^Q,fS,6,6`6`7#23$p;R+_I`<$p;R+_I`<$Hg;R!3+^N1!5'g8,6#^P,fS,6,6`4!7'gH#^Q,fS,6,6#^;#^:#1#1#1`=#1#1`>#1#1`?#1#1`@#1#1`A#1#1`B#1#1`C#1#1`E#1#1$p;R+_I`H$Hg;R!3+^N1!5'g8,6#^5,fR,6,6^X!7'gH#^6,fR,6,6#M#L#1#1#1`I#1#1`J#1#1`K#1#1$p;R+_I`O`P#1#1`R#1#1$p;R+_I`U#1$p;R+_I!1$p;R+_I$Hg;R!3+^N1^;C!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p;R+_I1#13$p0;R+_I`V$p0;R+_I55`Q`S#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1`VI!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#I35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^8,eP,6,955555555$p7;R+_I5!5'g8,6#\,fQ,9,9555$p3;R+_I555$p1;R+_I5^E^F#23$p;R+_I`W$p;R+_I`W$Hg;R!3+^N1-3RN$flags;R+31#H35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^7,eP,6,955555555$p7;R+_I5!5'g8,6#[,fQ,9,9555$p3;R+_I555$p1;R+_I5^D!1-3RN$z;R+3%Hg;R!3+^N1-3RN$flags;R+31#135$p1;R+_I`X$p1;R+_I5^I^J#I3`P$p;R+_I!1$p;R+_I$Hg;R!3+^N1`X^K!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I`Y5^M^N#23$p;R+_I^P$p;R+_I!1$p;R+_I$Hg;R!3+^N1`YT!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p2;R+_I1#13$p3;R+_I`Z$p3;R+_I55^R^S#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1`Z[!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I`[5^3^V#23$p;R+_I^Y$p;R+_I!1$p;R+_I$Hg;R!3+^N1`[^W!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I`\5^[^\#23$p;R+_I`H$p;R+_I!1$p;R+_I$Hg;R!3+^N1`\_0!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_Ia05_2_3#23$p;R+_I_6$p;R+_I!1$p;R+_I$Hg;R!3+^N1a0_4!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p6;R+_I1#13$p7;R+_Ia1$p7;R+_I5!5'g8,6#^<,fQ,9,9_8_9#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1a1_:!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_Ia25_@_A#23$p;R+_I_D$p;R+_I!1$p;R+_I$Hg;R!3+^N1a2_B!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_Ia35_F_G#23$p;R+_I_J$p;R+_I!1$p;R+_I$Hg;R!3+^N1a3_H!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_Ia45_L_M#23$p;R+_I_P$p;R+_I!1$p;R+_I$Hg;R!3+^N1a4_N!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_Ia55_R_S#23$p;R+_I_V$p;R+_I!1$p;R+_I$Hg;R!3+^N1a5_T!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_Ia65_X_Y#23$p;R+_I_\$p;R+_I!1$p;R+_I$Hg;R!3+^N1a6_Z!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_Ia75`1`2#23$p;R+_I`5$p;R+_I!1$p;R+_I$Hg;R!3+^N1a7`3!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_Ia85`6`7#23$p;R+_I`<$p;R+_I!1$p;R+_I$Hg;R!3+^N1a8`8!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_Ia95a:a;#23$p;R+_Ia>$p;R+_I!1$p;R+_I$Hg;R!3+^N1a9a<!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#^W,eP,6,9a?a@#23$p;R+_IaE$p;R+_IaE$Hg;R!3+^N1!5'g8,6#^V,eP,6,9a=!7'gH#^W,eP,6,9#^A#^@#1#1#1aF#1#1aG#1#1`=#1#1`>#1#1`?#1#1`@#1#1`A#1#1`B#1#1$p;R+_I_>$Hg;R!3+^N1!5'g8,6#^;,fQ,9,9_5!7'gH#^<,fQ,9,9#S#R#1#1#1`E#1#1aH#1#1`I#1#1$p;R+_I^T`J#1#1`K#1#1$p;R+_I`O#1#1#1$p;R+_IaI`T#1#1$p;R+_IaJ#1$Hg;R!3+^N1-3RN$prot;R+31#B3-3RN$flags;R+31#A35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaK$p14;R+_I5U55555555$p5;R+_I5!4'gG#T,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaK$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#C35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IaL$p16;R+_I5X55555555$p7;R+_I5!4'gG#V,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IaL$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5^:!1-3RN$z;R+3%Hg;R!3+^N1-3RN$prot;R+31#13-3RN$flags;R+31#C35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaN$p14;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^2,fS,6,62$c;R+CaM555555555$p5;R+_I5-^;RN$x;R!1+^;+C1!4'gI#V,fR,6,62$c;R+CaM5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaN$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_IaP$p;R+_I5^<^=#C3$Hg;R!3+^N1-3RN$flags;R+31#B35$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaR$p14;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^1,fS,6,62$c;R+CaM555555555$p5;R+_I5-^;RN$x;R!1+^;+C1!4'gI#U,fR,6,62$c;R+CaM5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IaR$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5^9!1-3RN$z;R+3%Hg;R!3+^N1-3RN$flags;R+31#135$p;R+_IaU$p;R+_I5CD#C3^@$p;R+_I!1$p;R+_I$Hg;R!3+^N1aU^A!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_IaX5I^C#23$p;R+_I^G$p;R+_I!1$p;R+_I$Hg;R!3+^N1aX^D!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p0;R+_I1#13$p1;R+_Ia[$p1;R+_I55^I^J#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1a[^K!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_Ib15^M^N#23$p;R+_I^P$p;R+_I!1$p;R+_I$Hg;R!3+^N1b1T!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_Ib45^R^S#23$p;R+_I^T$p;R+_I!1$p;R+_I$Hg;R!3+^N1b4[!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p3;R+_I1#13$p4;R+_Ib7$p4;R+_Ib85^3^V#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1b7^W!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p4;R+_I1#13$p5;R+_Ib;$p5;R+_I5-^;RN$x;R!1+^;+C1b<2$c;R+CaM5^[^\#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1b;_0!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_Ib?5_2_3#23$p;R+_I_6$p;R+_I!1$p;R+_I$Hg;R!3+^N1b?_4!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_IbB5_8_9#23$p;R+_I_>$p;R+_I!1$p;R+_I$Hg;R!3+^N1bB_:!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_IbE5_@_A#23$p;R+_I_D$p;R+_I!1$p;R+_I$Hg;R!3+^N1bE_B!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_IbH5_F_G#23$p;R+_I_J$p;R+_I!1$p;R+_I$Hg;R!3+^N1bH_H!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_IbK5_L_M#23$p;R+_I_P$p;R+_I!1$p;R+_I$Hg;R!3+^N1bK_N!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_IbO5_R_S#23$p;R+_I_V$p;R+_I!1$p;R+_I$Hg;R!3+^N1bO_T!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_IbQ5_X_Y#23$p;R+_I_\$p;R+_I!1$p;R+_I$Hg;R!3+^N1bQ_Z!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_IbS5`1`2#23$p;R+_I`5$p;R+_I!1$p;R+_I$Hg;R!3+^N1bS`3!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p13;R+_I1#13$p14;R+_IbT$p14;R+_I5bM`6`7#23$p;R+_IcV$p;R+_I`<$Hg;R!3+^N1-^;RN$x;R!1+^;+C1!4'gI#^P,fS,6,62$c;R+CaM5`4&o;RbLcD!1-^;RN$o;R!1+^;+C%Hg;R!3+^N1cE`9`:#12$a;R+C!1$a;R+C$Hg;R!3+^N1aMa:&H;R!6'_J1+CcGcHa<#1!3+^N+C#2#^>!1&H;R!6'_J1+CcKcMa=#2!3+^N+CcL#^@!1$H;R!3+^N+CcO#^A!6'_M+CcP$ga;R+C%~R!3+^N+C#6#^B^5$H;R!3+^N+C#5#^AcQ#^B#1#1#1#1`;#2#1#1`=#1#1`>#1#1`?#1#1`@#1#1`A#1#1`B#1#1`C#1#1`E#1#1$p;R+_I`H$Hg;R!3+^N1-^;RN$x;R!1+^;+C1!4'gI#^5,fR,6,62$c;R+CaM5^X&o;Rb<cD!1-^;RN$o;R!1+^;+C%Hg;R!3+^N1cE`D`F#12$a;R+C!1$a;R+C$Hg;R!3+^N1aM_2&H;R!6'_J1+CcGcH_4#1!3+^N+C#2#P!1&H;R!6'_J1+CcKcM_5#2!3+^N+CcL#R!1$H;R!3+^N+CcO#S!6'_M+CcP$ga;R+C%~R!3+^N+C#6#T^5$H;R!3+^N+C#5#ScQ#T#1#1#1#1`G#2#1#1$p;R+_I!1$p;R+_I$Hg;R!3+^N1b8^W!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p4;R+_I1#13$p5;R+_IcW$p5;R+_I55^[^\#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1cW_0!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_IcX5_2_3#23$p;R+_I_6$p;R+_I!1$p;R+_I$Hg;R!3+^N1cX_4!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_IcY5_8_9#23$p;R+_I_>$p;R+_I!1$p;R+_I$Hg;R!3+^N1cY_:!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_IcZ5_@_A#23$p;R+_I_D$p;R+_I!1$p;R+_I$Hg;R!3+^N1cZ_B!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_Ic[5_F_G#23$p;R+_I_J$p;R+_I!1$p;R+_I$Hg;R!3+^N1c[_H!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_Ic\5_L_M#23$p;R+_I_P$p;R+_I!1$p;R+_I$Hg;R!3+^N1c\_N!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_Id05_R_S#23$p;R+_I_V$p;R+_I!1$p;R+_I$Hg;R!3+^N1d0_T!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_Id15_X_Y#23$p;R+_I_\$p;R+_I!1$p;R+_I$Hg;R!3+^N1d1_Z!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_Id25`1`2#23$p;R+_I`5$p;R+_I!1$p;R+_I$Hg;R!3+^N1d2`3!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p13;R+_I1#13$p14;R+_IbT$p14;R+_I55`6`7#23$p;R+_IcV$p;R+_I`<aG#1#1`=#1#1`>#1#1`?#1#1`@#1#1`A#1#1`B#1#1`C#1#1`E#1#1$p;R+_I`HaH#1#1`I#1#1`J#1#1`K#1#1$p;R+_I`O`P#1#1`R#1#1$p;R+_I`U#1$p;R+_I!1$p;R+_I$Hg;R!3+^N1aPC!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p;R+_I1#13$p0;R+_Id4$p0;R+_I55`Q`S#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1d4I!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#I35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id5$p16;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^8,eP,6,62$c;R+CaM555555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#\,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id5$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5^E^F#23$p;R+_I`W$p;R+_I`W$Hg;R!3+^N1-3RN$flags;R+31#H35$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id7$p16;R+_I5-^;RN$x;R!1+^;+C1!4'gI#^7,eP,6,62$c;R+CaM555555555$p7;R+_I5-^;RN$x;R!1+^;+C1!4'gI#[,fQ,9,92$c;R+CaM5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_Id7$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5^D!1-3RN$z;R+3%Hg;R!3+^N1-3RN$flags;R+31#135$p1;R+_Id:$p1;R+_I5^I^J#I3`P$p;R+_I!1$p;R+_I$Hg;R!3+^N1d:^K!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_Id=5^M^N#23$p;R+_I^P$p;R+_I!1$p;R+_I$Hg;R!3+^N1d=T!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p2;R+_I1#13$p3;R+_Id@$p3;R+_I55^R^S#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1d@[!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_IdC5^3^V#23$p;R+_I^Y$p;R+_I!1$p;R+_I$Hg;R!3+^N1dC^W!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_IdF5^[^\#23$p;R+_I`H$p;R+_I!1$p;R+_I$Hg;R!3+^N1dF_0!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p5;R+_I1#13$p6;R+_IdI$p6;R+_IdJ5_2_3#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1dI_4!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p6;R+_I1#13$p7;R+_IdM$p7;R+_I5-^;RN$x;R!1+^;+C1dN2$c;R+CaM5_8_9#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1dM_:!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_IdQ5_@_A#23$p;R+_I_D$p;R+_I!1$p;R+_I$Hg;R!3+^N1dQ_B!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_IdT5_F_G#23$p;R+_I_J$p;R+_I!1$p;R+_I$Hg;R!3+^N1dT_H!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_IdW5_L_M#23$p;R+_I_P$p;R+_I!1$p;R+_I$Hg;R!3+^N1dW_N!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_IdZ5_R_S#23$p;R+_I_V$p;R+_I!1$p;R+_I$Hg;R!3+^N1dZ_T!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_Ie05_X_Y#23$p;R+_I_\$p;R+_I!1$p;R+_I$Hg;R!3+^N1e0_Z!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_Ie45`1`2#23$p;R+_I`5$p;R+_I!1$p;R+_I$Hg;R!3+^N1e4`3!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_Ie65`6`7#23$p;R+_I`<$p;R+_I!1$p;R+_I$Hg;R!3+^N1e6`8!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_Ie85a:a;#23$p;R+_Ia>$p;R+_I!1$p;R+_I$Hg;R!3+^N1e8a<!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p15;R+_I1#13$p16;R+_Ie9$p16;R+_I5e2a?a@#23$p;R+_IeE$p;R+_IaE$Hg;R!3+^N1-^;RN$x;R!1+^;+C1!4'gI#^V,eP,6,62$c;R+CaM5a=&o;Re1cD!1-^;RN$o;R!1+^;+C%Hg;R!3+^N1cEaBaC#12$a;R+C!1$a;R+C$Hg;R!3+^N1aMbX&H;R!6'_J1+CcGcHbZ#1!3+^N+C#2#^D!1&H;R!6'_J1+CcKcMb[#2!3+^N+CcL#^F!1$H;R!3+^N+CcO#^G!6'_M+CcP$ga;R+C%~R!3+^N+C#6#^H^5$H;R!3+^N+C#5#^GcQ#^H#1#1#1#1aD#2#1#1aF#1#1aG#1#1`=#1#1`>#1#1`?#1#1`@#1#1`A#1#1`B#1#1$p;R+_I_>$Hg;R!3+^N1-^;RN$x;R!1+^;+C1!4'gI#^;,fQ,9,92$c;R+CaM5_5&o;RdNcD!1-^;RN$o;R!1+^;+C%Hg;R!3+^N1cE_;_<#12$a;R+C!1$a;R+C$Hg;R!3+^N1aM_@&H;R!6'_J1+CcGcH_B#1!3+^N+C#2#V!1&H;R!6'_J1+CcKcM_C#2!3+^N+CcL#X!1$H;R!3+^N+CcO#Y!6'_M+CcP$ga;R+C%~R!3+^N+C#6#Z^5$H;R!3+^N+C#5#YcQ#Z#1#1#1#1_=#2#1#1$p;R+_I!1$p;R+_I$Hg;R!3+^N1dJ_4!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p6;R+_I1#13$p7;R+_IeF$p7;R+_I55_8_9#23$p;R+_I!1$p;R+_I$Hg;R!3+^N1eF_:!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_IeG5_@_A#23$p;R+_I_D$p;R+_I!1$p;R+_I$Hg;R!3+^N1eG_B!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_IeH5_F_G#23$p;R+_I_J$p;R+_I!1$p;R+_I$Hg;R!3+^N1eH_H!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_IeI5_L_M#23$p;R+_I_P$p;R+_I!1$p;R+_I$Hg;R!3+^N1eI_N!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_IeJ5_R_S#23$p;R+_I_V$p;R+_I!1$p;R+_I$Hg;R!3+^N1eJ_T!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_IeK5_X_Y#23$p;R+_I_\$p;R+_I!1$p;R+_I$Hg;R!3+^N1eK_Z!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_IeL5`1`2#23$p;R+_I`5$p;R+_I!1$p;R+_I$Hg;R!3+^N1eL`3!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_IeM5`6`7#23$p;R+_I`<$p;R+_I!1$p;R+_I$Hg;R!3+^N1eM`8!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_IeN5a:a;#23$p;R+_Ia>$p;R+_I!1$p;R+_I$Hg;R!3+^N1eNa<!1-_IRN$p;R+_I%Hg;R!3+^N1-_IRN$p15;R+_I1#13$p16;R+_Ie9$p16;R+_I55a?a@#23$p;R+_IeE$p;R+_IaEcU#1#1aF#1#1aG#1#1`=#1#1`>#1#1`?#1#1`@#1#1`A#1#1`B#1#1$p;R+_I_>`C#1#1`E#1#1aH#1#1`I#1#1$p;R+_I^T`J#1#1`K#1#1$p;R+_I`O#1#1#1$p;R+_IaI`T#1#1$p;R+_IaJ#1#6#L#1#1#1#2#1#1$Hg;R!3+^N1-1RN$isnull;R+11#42-3RN$prot;R+31#63-3RN$flags;R+31#535$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I5!5'g8,6#Q,fS,6,655555555$p5;R+_I5!5'g8,6#H,fR,6,6555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#735$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_I5$p16;R+_I5!5'g8,6#S,eP,6,955555555$p7;R+_I5!5'g8,6#J,fQ,9,9555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I5-3RN$prot;R+31#63-3RN$flags;R+31#535$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IeO$p14;R+_I5=55555555$p5;R+_I5!4'gG#H,fR,6,6$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I5$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I5$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_IeO$p14;R+_I5555555555$p5;R+_I55555$p1;R+_I555$p;R+_I5$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I-_IRN$p0;R+_I1#13$p1;R+_I5$p1;R+_I5-3RN$flags;R+31#735$p1;R+_I-_IRN$p1;R+_I1#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I1#13$p3;R+_I-_IRN$p3;R+_I1#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I1#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I1#13$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IeP$p16;R+_I5?55555555$p7;R+_I5!4'gG#J,fQ,9,9$p6;R+_I-_IRN$p6;R+_I1#13$p7;R+_I-_IRN$p7;R+_I1#13$p8;R+_I5$p8;R+_I-_IRN$p8;R+_I1#13$p9;R+_I5$p9;R+_I-_IRN$p9;R+_I1#13$p10;R+_I5$p10;R+_I-_IRN$p10;R+_I1#13$p11;R+_I5$p11;R+_I-_IRN$p11;R+_I1#13$p12;R+_I5$p12;R+_I-_IRN$p12;R+_I1#13$p13;R+_I5$p13;R+_I-_IRN$p13;R+_I1#13$p14;R+_I5$p14;R+_I-_IRN$p14;R+_I1#13$p15;R+_I5$p15;R+_I-_IRN$p15;R+_I1#13$p16;R+_IeP$p16;R+_I5555555555$p7;R+_I55555$p3;R+_I555$p1;R+_I5$p0;R+_I55$p;R+_I55$H;R`L&H0;R`M+`M`N#1#3#2#1#2#1#1$H;R!3+^N15^0&H0;R!6'_M15^?,`R;#1+`M!2'_\<#1#2").
Qed.

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
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs TOPC with    (* [comment removed for export] *)
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfill k b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                           (HSub (reg cs 10) ne :: a_hna cs) (a_hlz cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs TOPC with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfillB bc b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                           (HSub (reg cs 10) ne :: a_hna cs) (a_hlz cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Lemma node_mprotect_eq : forall cs, node_mprotect cs = node_mprotect_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^O0%ms;R!1+2+:%kinds;R!1+2+8%b;R+E%off;R+3%n;R+E!1+^;+:!1'^9#1!1+^;+C}A!2'f3#23!1,^2+C}<!2'f3#;6!2+_>+E+3!2+_>8+E!2+_>9+3!2+_>:+3!2'fO#>'fP!1'O#G!3,_T+8,fR!3,_T+8,fS!1,^0+8!1'e9#H}:!2'^B#H@!2'_8!2'_8!2'fV#H#8!2'a:?#4!2'a:?A!1,^K|20;!2'^U!1'd?#HC!1'G#H!1,H,I!3'^6!1'FE@F!1'^9#H!1'LE!2'fW!1'O#H#1!1'P#H!1'Q#H!2'^U!1'R#H#8!1'S#H!1'T#H!1'U#H!1'V#H!1'W#H!1'X#H!3,_T+`>!2,fXA#4!1'Y#H!1'Z#H!=,N!4'^5DG!1'fF!4'b>!1'aBH#3#2#4IJKLMNOPQRSTU!2,`F#3#2!2,a4W#4!2,`[W#4!1'^9#G!6'eEZ=>#2#1#3!=,N!4'^5DG!1'fF!4'b?H#3#2#4IJKLMNOPQRSTU-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;+3272$z0;R+3-3RN$z0;R+32#135$p7;R+_I-_IRN$p7;R+_I2#13$p8;R+_I-_IRN$p8;R+_I2#13$p9;R+_I5$p9;R+_I5-^;RN$x;R!1+^;;2<2$p9;R;-_>RN$p9;R!2+_>:+32#11$p10;R:$nhi;R+3-_>RN$p10;R!2+_>9+32#21$p11;R9$nlo;R+3-_>RN$p11;R!2+_>8+E2#21$p12;R8$ne;R+E-_>RN$p12;R!2+_>+E+32#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:2[2$m;R+:-1RN$~R+12B2!4'eX\A#4!3,_T+[X!3,_T+[Y!1'^9\555$p8;R+_I55$p7;R+_I55$p6;R+_I55$p5;R+_I55555$p1;R+_I555$p;R+_I55%ub;R+E%uk;R+3%un;R+E!1+2+[!=,N!4'^5DG!1'fF!3#G#3#2#4IJKLMNOPQRSTU!2'f3#13!2'f3#:6!2'fO#='fP!1'^9#F!1'O#F!1'e9#G!2'^B#G@!2'_8!2'_8!2'fV#G#8!2'a:^8#4!2'a:^8^9!2'^U!1'd?#GC!1'G#G!3'^6!1'F^<@F!1'L^<!2'fW=#1!1'P#G!1'Q#G!2'^U!1'R#G#8!1'S#G!1'T#G!1'U#G!1'V#G!1'W#G!1'X#G!3,_T+`>!2,fX^9#4!1'Y#G!1'Z#G!=,N!4'^5^;^=!1'fF!4'b?Z#3#2#4^>^?^@^A^B^C^D^E^F^G^H^I^J-^;RN$x;R!1+^;+32^32$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;+32^42$z0;R+3-3RN$z0;R+32#135$p7;R+_I-_IRN$p7;R+_I2#13$p8;R+_I-_IRN$p8;R+_I2#13$p9;R+_I5$p9;R+_I5-^;RN$x;R!1+^;;2^52$p9;R;-_>RN$p9;R!2+_>:+32#11$p10;R:$nhi;R+3-_>RN$p10;R!2+_>9+32#21$p11;R9$nlo;R+3-_>RN$p11;R!2+_>8+E2#21$p12;R8$ne;R+E-_>RN$p12;R!2+_>+E+32#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:2!6'eE^6^7>#2#1#32$m;R+:-1RN$~R+12^:2!4'eX^K^9#4!3,_T+[X!3,_T+[Y!1'^9^K555$p8;R+_I55$p7;R+_I55$p6;R+_I55$p5;R+_I55555$p1;R+_I555$p;R+_I55!1'aB1!=,N!4'^5^;^=!1'fF!4'b>!1'aBZ#3#2#4^>^?^@^A^B^C^D^E^F^G^H^I^J$cs;R+Cvdvd!6'_W0!1'eE1$o;R0!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;+3272$z0;R+3-3RN$z0;R+32#135$p7;R+_I-_IRN$p7;R+_I2#13$p8;R+_I-_IRN$p8;R+_I2#13$p9;R+_I5$p9;R+_I5-^;RN$x;R!1+^;;2<2$p9;R;-_>RN$p9;R!2+_>:+32#11$p10;R:$nhi;R+3-_>RN$p10;R!2+_>9+32#21$p11;R9$nlo;R+3-_>RN$p11;R!2+_>8+E2#21$p12;R8$ne;R+E-_>RN$p12;R!2+_>+E+32#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:2!5#F=>#2#1#32$m;R+:-1RN$~R+12B2!4'eXVA#4!3,_T+[X!3,_T+[Y!1'^9V555$p8;R+_I55$p7;R+_I55$p6;R+_I55$p5;R+_I55555$p1;R+_I555$p;R+_I55^0!6'_W^1!1'b?1$l;R^1!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;+3272$z0;R+3-3RN$z0;R+32#135$p7;R+_I-_IRN$p7;R+_I2#13$p8;R+_I-_IRN$p8;R+_I2#13$p9;R+_I5$p9;R+_I5-^;RN$x;R!1+^;;2<2$p9;R;-_>RN$p9;R!2+_>:+32#11$p10;R:$nhi;R+3-_>RN$p10;R!2+_>9+32#21$p11;R9$nlo;R+3-_>RN$p11;R!2+_>8+E2#21$p12;R8$ne;R+E-_>RN$p12;R!2+_>+E+32#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:2[2$m;R+:-1RN$~R+12B2!4'eX^2A#4!3,_T+[X!3,_T+[Y!1'^9^2555$p8;R+_I55$p7;R+_I55$p6;R+_I55$p5;R+_I55555$p1;R+_I555$p;R+_I55^0!2,^H2^L!1'b>^M!1'bE1!1'eD^M!1'eS1!3+^N2-^;RN$x;R!1+^;+32^32$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I5$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I5$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I5$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;+32^42$z0;R+3-3RN$z0;R+32#135$p7;R+_I-_IRN$p7;R+_I2#13$p8;R+_I-_IRN$p8;R+_I2#13$p9;R+_I5$p9;R+_I5-^;RN$x;R!1+^;;2^52$p9;R;-_>RN$p9;R!2+_>:+32#11$p10;R:$nhi;R+3-_>RN$p10;R!2+_>9+32#21$p11;R9$nlo;R+3-_>RN$p11;R!2+_>8+E2#21$p12;R8$ne;R+E-_>RN$p12;R!2+_>+E+32#21$b;R+E$off;R+3-^;RN$x;R!1+^;+:2!6'eD!1'aB^6^7>#2#1#32$m;R+:-1RN$~R+12^:2!4'eX^N^9#4!3,_T+[X!3,_T+[Y!1'^9^N555$p8;R+_I55$p7;R+_I55$p6;R+_I55$p5;R+_I55555$p1;R+_I555$p;R+_I55^L!3+^N2!1'gJ#1!1'gK#1").
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_mprotect2 (cs : acs) : option (acs * acs) :=
  match node_mprotect cs with Some csG => Some (contra_cs csG, csG) | None => None end.

(* [comment removed for export] *)

Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$bc;R+aK$b;R+E$n;R+E$m;R+:!2'_8!2'_8!1'@!1'A#1!2'_9#3!1'`A#1!3'd5#4#2!1'`B#1").

Lemma amap_matchB_eqf : forall fk, amap_matchB (mkbc fk) = amap_match fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S50%m;R+:+1%n;R+E%m;R+E+1!2'_8!1'@!1'A#2!2'_9#4!1'`A#2!1'`B#2!1'aB#4$fk;R!1+2+[!5'b0+E%n;R+E0!1'gL!1'aB#1!1'gM#1$x;R+E!5'b0+E0!2'gL!1'aB#2#1!2'gM#2#1$x0;R+E!5'b0+:+1!3'gL!1'aB#3#2#1!3'gM#3#2#1$x1;R+:vd!6'_W1!1'd6#4$b;R1!3+^N+1!2'_82!2#1#33!2'_82!3'd6#5#33!2,^H+1!2'_8!2'_8!1'@!1'A#1!2'_9#3!1'`A#1!3'd6#4#2!1'`B#1!1'd54!1'gN#4!3+^N+1!4'gL4#3#2#1!4'gM#4#3#2#1").
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
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                 (HSub b ne :: a_hna cs) (HSub b ne :: a_hlz cs))
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
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                 (HSub b ne :: a_hna cs) (HSub b ne :: a_hlz cs))
      else None
  | _, _ => None
  end.

Lemma node_munmap_eq : forall cs, node_munmap cs = node_munmap_ref cs.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`10%b;R+E%n;R+E%m;R+:+1!1'^9#1!1+^;+C}A!2'f3#23!1,^2+C!2+_>+E+3!2+_>6+3!1'f5#;}:!1'_2!2'^B#@9!2'^B#B9!1'O#B!1'^9#B!1'aB=!2'd;>;!4'c\>#2#1#4!2'a[!2'^U#1#6'^>-^;RN$x;R!1+^;+3+1!2'cP>;2$hi;R+3A,6!2+_>+E+E!3'`?+E+E#1!1'_2D!1'^9#E!1'aBF!3'`?+E+E#3!3'`@+E+E#3!3'eHGHI!1,^K|11;!1'^9#I!1'aBL!3'`?+E+E#7!3'`@+E+E#7!7'cIM#6#5O#9#8#;!5'cSML#2#1#3!7'aZG#2#1I#5#4#7!1'S#B!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3!1'@RS!1,^K|20;!2'^U!1'd?#BU!1'G#B!1,H,I!3'^6!1'FW9X!1+2+[!1'^9#D!1'aB[!3'`@+E+E#1-_>RN$p0;R!2+_>+E+3Z#21$sb;R+E$sk;R+3!4'bD#6#2#1#3$kk;RZ$p;RC-_>RN$x;R!2+_>6+EZ!3'eH\D^01$p0;R6$sn;R+E^1!1'LW!4'^5VY!5'gOZC^2T!4'b>>#2#1#4^3!2'^B#C9!1'P#B!1'Q#B!1'R#B!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3RS!1'T#B!3'^8CT^:!1'U#B!1'V#B!1'W#B!1'X#B!2,fX;#4!3,_T+`>^@!1'Y#B!3,_T+`>^@!1'Z#B!3'_6+:!3'gM=;#4<!4'd0=#2#1#4!2'_8!2'_8^C!2'd<=;^D!2'_8^E-^;RN$x;R!1+^;+3+1!2'cQ=;2$hi;R+3A,6!3'eIFHI!2'_8!2'_:K!2'd=LN!2'_:K!2'd=LO!5'cTLL#2#1#3!7'b3F#2#1I#5#4#7!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3!1'@^JS!2'_8^F!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1^G1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8!2'_8^H!7'cKL#6#5O#9#8#;^I^K!3'eI[D^0-_>RN$p0;R!2+_>+E+3Z#21$sb;R+E$sk;R+3!4'b?#6#2#1#3!4'b?=#2#1#4!1'^9#C!3'_@+:$m;R+:!1'@!4'gM^P^5#5#1<!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3^JS!3'^8C^K^:-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12^L2!2,^<+C!=,N!4'^5VY!5'gOZC$kk;RZ$p;RC-_>RN$x;R!2+_>6+EZ^M1$p0;R6$sn;R+E^N^K^O^3^Q^6^7^8^R^S^<^=^>^?^A^B55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55%e;R+E+3!2'_8^C?!2,^<+C!=,N^4^Q^6^7^8^9^;^<^=^>^?^A^B%b;R+E%off;R+3%n;R+E+1!3#A#2#1#4!2'_8^HP!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1J1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8^ZQT%ub;R+E%uk;R+3%un;R+EZ!2'_8!2'_8^V^DB%k;RZ^X!2,^<+C!=,N!4'^5VY!5'gOZC^2T^O^3^Q^6^7^8^9^;^<^=^>^?^A^B%e;R+E+1!1#A;-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8^Z^I$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1J1$p0;R6$sn;R+E_5%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1!2'_8^EB!6#D#2#1I#5#4#7!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3!1'@_9S%b;R+E%n;R+E!2+_>6+E%e;R+E!1+^;+3!2,^<+C!=,N!4'^5VY!5'gOZC$kk;RZ$p;RC-_>RN$x;R!2+_>6+EZ^M1$p0;R6$sn;R+E^1^K^O^3^Q^6^7^8^R^S^<^=^>^?^A^B%k;RZ^\!2'f3#13!1'f5#:!1'_2!2'^B#?9!1'^9#A!2'^B#A9!1'O#A!1'^9#H!7'b3[#2#1I#5#4#7!1'S#A!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3!1'@_F_G!2'^U!1'd?#AU!1'G#A!3'^6!1'F_J9X!1'L_J!1'P#A!1'Q#A!1'R#A!1'T#A!1'U#A!1'V#A!1'W#A!1'X#A!2,fX_C#4!3,_T+`>_U!1'Y#A!3,_T+`>_U!1'Z#A-^;RN$x;R!1+^;+32_?2$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;72_@2$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32_A1$bb;R+E$bk;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!3'_6+:!3'gM_B_C#4_D!2'd<_B_C!4'd0_B#2#1#4-^;RN$x;R!1+^;+3+1!2'cQ_B_C2$hi;R+3A,6!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1!3'eI[HI1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8!2'_8!2'_8!2'_:K!2'd=_EN!2'_:K!2'd=_EO!7'cK_E#6#5O#9#8#;!5'cT_E_E#2#1#3_H2!2,^<+C!=,N!4'^5_I_K!5'gOZC$kk;RZ$p;RC-_>RN$x;R!2+_>6+EZ!3'eI^PD^01$p0;R6$sn;R+E^N_H!4'b?_B#2#1#4_L!3'_@+:$m;R+:!1'@!4'gM=;#5#1_D_M_N_O!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3_F_G!3'^8C_H_P_Q_R_S_T_V_W55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55!1'aB1!1'aB_B!1'aB_E!7'aZ\#2#1I#5#4#7!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3!1'@_\_G$cs;R+Cvdvd!6'_W0!1'gM1$b;R0!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!3'_6+:!2#A;#4<?@B!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1J1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8!2'_8!2'_8!2'_:K!2'd:MN!2'_:K!2'd:MOPQT2!2,^<+C!=,N^4!3'_@+:$m;R+:!1'@!3#B^5#5#1<^6^7^8^9^;^<^=^>^?^A^B55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W^U!1'd=1$z;R^U!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8!2'_8!2'_8^V@B!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1J1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8!2'_8!2'_8!2'_:K!1#HN!2'_:K!1#HOPQT2^W55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W^X!1'd01$b;R^X!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8!2'_8!2'_8^V^YB^[2^W55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W^\!1'b?1$l;R^\!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8_0^[2!2,^<+C!=,N!4'^5VY!5'gOZC^2T^Y^3^Q^6^7^8^9^;^<^=^>^?^A^B55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W_1!1'cT1$b;R_1!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8_0!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1J1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8^Z!4#HL#2#1#3T2_255$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W_3!1'd<1$b;R_3!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8^C_4^DB!3'?C_6T2_255$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W_7!1'b31$b;R_7!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8_8!3'?C_6_:2!2,^<+C!=,N!4'^5VY!5'gOZC^2_:^O^3^Q^6^7^8!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3_9S!3'^8C_:^:^<^=^>^?^A^B55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W_;!1'eI1$p;R_;!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8_8!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1!2#DHI1$p0;R6$sn;R+E_5^K2!2,^<+C!=,N!4'^5VY!5'gOZC$kk;RZ$p;RC-_>RN$x;R!2+_>6+EZ!2#CD^01$p0;R6$sn;R+E^1^K^O^3^Q^6^7^8^R^S^<^=^>^?^A^B55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W_<!1'cQ1$o;R_<!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8!2'_8^E-^;RN$x;R!1+^;+3+1_42$hi;R+3A,6!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1^G1$p0;R6$sn;R+E_5^K2_=55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W_7!1'cK1$b;R_7!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12!2'_8^F!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1^G1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8!2'_8^H!6#H#6#5O#9#8#;^I^K2_=55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!6'_W_>'b?$l;R_>!3+^N2-^;RN$x;R!1+^;+3242$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;7282$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32:1$bb;R+E$bk;R+3-1RN$~R+12^L2!2,^<+C!=,N!4'^5VY!5'gOZC$kk;RZ$p;RC-_>RN$x;R!2+_>6+EZ^M1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3Z#21$sb;R+E$sk;R+3!4#G#6#2#1#3^K^O^3^Q^6^7^8^R^S^<^=^>^?^A^B55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55^T!2,^H2_X'bD'gP!1'cI_Y!1'cM1!1'cP_Y!1'cR1!1'eH_Y!1'eT1!1'aZ_Y!1'b41!1'd;_Y!1'gQ1!1'cS_Y!1'gR1!1'b>_Y!1'bE1!1'c\_Y!1'eO1!1'd:_Y!1'd>1!1'gL_Y!1'gS1!3+^N2-^;RN$x;R!1+^;+32_?2$z;R+3-3RN$z;R+32#135$p;R+_I-_IRN$p;R+_I2#13$p0;R+_I-_IRN$p0;R+_I2#13$p1;R+_I-_IRN$p1;R+_I2#13$p2;R+_I-_IRN$p2;R+_I2#13$p3;R+_I5$p3;R+_I-_IRN$p3;R+_I2#13$p4;R+_I-_IRN$p4;R+_I2#13$p5;R+_I5$p5;R+_I-_IRN$p5;R+_I2#13$p6;R+_I-_IRN$p6;R+_I2#13$p7;R+_I5$p7;R+_I5-^;RN$x;R!1+^;72_@2$p7;R7-_>RN$p7;R!2+_>6+32#11$p8;R6$nhi;R+3-_>RN$p8;R!2+_>+E+32#21$ne;R+E$nlo;R+3-_>RN$x;R!2+_>+E+32_A1$bb;R+E$bk;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!3'_6+:!3'gL_Z_C#4_D!2'd;_Z_C!4'c\_Z#2#1#4-^;RN$x;R!1+^;+3+1!2'cP_Z_C2$hi;R+3A,6!3'?C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3-_>RN$x;R!2+_>6+E+1!3'eH\HI1$p0;R6$sn;R+E-_>RN$p0;R!2+_>+E+3+1#21$sb;R+E$sk;R+3!2'_8!2'_8!2'_8!2'_:K!2'd:_[N!2'_:K!2'd:_[O!7'cI_[#6#5O#9#8#;!5'cS_[_E#2#1#3`02!2,^<+C!=,N!4'^5_I_K!5'gOZC$kk;RZ$p;RC-_>RN$x;R!2+_>6+EZ!3'eH!1'aB^PD^01$p0;R6$sn;R+E^1`0!4'b>_Z#2#1#4_L!3'_@+:$m;R+:!1'@!4'gL>;#5#1_D_M_N_O!3'_@C$p;RC-_>RN$x;R!2+_>+E+3+1E1$pb;R+E$pk;R+3_\_G!3'^8C`0_P_Q_R_S_T_V_W55$p6;R+_I555$p4;R+_I555$p2;R+_I55$p1;R+_I55$p0;R+_I55$p;R+_I55_X!3+^N2!1'gT#1!1'gU#1").
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
Definition brk_grow_maybe (cs : acs) (d : Z) : bool :=
  (brk_base_ok cs d && no_fog (a_maps cs))%bool.

(* [comment removed for export] *)
Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      (* [comment removed for export] *)
      if (brk_grow_maybe cs d && budget_ok cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kdisj_new (a_maps cs) b (ELit (d + 4096)) ++ kn_grant_filter k (a_maps cs) in
        let ss := a_ss cs in
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs) in
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
                 (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) true (a_hna cs) (a_hlz cs))
      else None
  | _ => None
  end.

Definition node_exit (cs : acs) : option Z := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S40!1+^;+3!1,^2+3}:-_IRN$p1;R+_I0#13$p2;R+_I-_IRN$p2;R+_I0#13$p3;R+_I-_IRN$p3;R+_I0#13$p4;R+_I-_IRN$p4;R+_I0#13$p5;R+_I1$p5;R+_I-_IRN$p5;R+_I0#13$p6;R+_I1$p6;R+_I1-^;RN$x;R!1+^;+30!2'f3#922$code;R+3!2,^<+3!2'gV#1!1,^K|77f;11$p4;R+_I11$p3;R+_I11$p2;R+_I11$cs;R+C-^;RN$x;R!1+^;+30!2'f3#1}A2$z;R+3-3RN$z;R+30#131$p;R+_I-_IRN$p;R+_I0#13$p0;R+_I-_IRN$p0;R+_I0#13$p1;R+_I1$p1;R+_I31$p0;R+_I-_IRN$p0;R+_I0#13$p1;R+_I3$p1;R+_I111$p;R+_I11").

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

Definition fog_token (sz : Z) : amap := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$sz;R+3!3,g2!1,H,I!1,H#1,gW").

Definition with_maps (cs : acs) (ms : list amap) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$cs;R+C$ms;R!1+2+:!=,N!1'G#2#1!1'P#2!1'Q#2!1'R#2!1'S#2!1'T#2!1'U#2!1'V#2!1'W#2!1'X#2!1'Y#2!1'Z#2").

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
                     (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition vis_here (b n : expr) (p : expr * expr) : bool := (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool.

Definition node_unvis_ref (cs : acs) (b n : expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S60!1+2+[!1+^;+C!2+_>+E+3!2+_>+E+E!1,^K|11;!1,^2+C$cs;R+C$b;R+E$n;R+E&k;R!1'^9#30-_>RN$x;R!2+_>+E+31!1'_2#31$bb;R+E$bk;R+3-_>RN$x;R!2+_>2+E1!3'eI#3#5#41$p;R2$sn;R+E-_>RN$p;R!2+_>+E+31#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+31!2'cQ#7#92$bh;R+3-^;RN$x;R!1+^;+31!2'cQ#8#92$nh;R+3-1RN$~R+11!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!3'_63!2'gX#;#:!1'S#<!2'_:4!2'd=#9#;!2'_:4!2'd=#9#:!4'd0#9#8#7#:!2'_:!2'^U#2#1'gY!4'd0#9#4#3#5!5'cT#9#9#4#3#52&k1;R!4'b?#9#8#7#:0&k2;R!4'b?#1#5#4#60&ss;R!1'G#>+M!2,^<+C!=,N!4'^5!1'K#1!1'F#1#2!1'L#1!1'O#?!1'P#?!1'Q#?!1'R#?!3'_@3$p;R3!1'@!3'gX#?#>#1!1'S#?!3'^83!1'T#?!3,_T3!4,d4+E+E#>#=!1,^03!1'U#?!1'V#?!1'W#?!1'X#?!1'Y#?!1'Z#?555").
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
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs))
      else None
  | _, _ => None
  end.

Lemma node_unvis_eq : forall cs b n, node_unvis cs b n = node_unvis_ref cs b n.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^T0%e;R+E+3!1'^9#3!1+^;+C!1'_2#3!2+_>+E+3!1'^9#6!3'eH!1'aB5#5#4!1'^9#:!1'aB7!2'cP8#9!1'^9#;!1'aB:!2'cP;#9!2+_>+E+E!1'S#<!3'_6=!2'gX#;#:>!1,^K|11;!1'^9#<!1'aBA!2'_:!2'^U#2#1'gY!5'cSBA#4#3#5!1'G#<!1'KE!1'FE!1'LE!1'O#<!1'P#<!1'Q#<!1'R#<!3'_@=$p;R=!1'@!3'gX#<#;#1>!1,^0=!3'^8=!1'T#<!3,_T=!4,d4+E+E#;#:N!1'U#<!1'V#<!1'W#<!1'X#<!1'Y#<!1'Z#<!2,^<+C!=,N!4'^5FG!4'bD!4'b>B#8#7#:#4#3#5HIJKLMOPQRSTU!1,^2+C!3'eI5#5#4!2'cQ7#9!2'cQ:#9!2'_8!2'_8?!2'_:@!2'd=A#;!2'_:@!2'd=A#:!2'_8!2'_8!2'_8[!4'd0A#8#7#:C!4'd0A#4#3#5!2'_8\!5'cTAA#4#3#5!4'b?A#8#7#:-_>RN$x;R!2+_>+E+3231$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E2X1$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+32Y2$bh;R+3-^;RN$x;R!1+^;+32Z2$nh;R+3-1RN$~R+12^02!2,^<+C!=,N!4'^5FG!4'b?^1#4#3#5HIJKLMOPQRSTUWWW%b;R+E%off;R+3%n;R+E+1!3#9#8#7#:!1+2+[%ub;R+E%uk;R+3%un;R+E^5%k;R^5^3!2,^<+C!=,N!4'^5FG!4'bD^1#4#3#5HIJKLMOPQRSTU%b;R+E%n;R+E!2+_>4+E-1RN$~R+12^02^8W%e;R+E!1+^;+3%k;R^5^6!1'_2#2!1'^9#5!1'^9#9!1'S#;!3'_6=!2'gX#:#9^@!1'G#;!1'K^B!1'F^B!1'L^B!1'O#;!1'P#;!1'Q#;!1'R#;!3'_@=$p;R=!1'@!3'gX#;#:#1^@!3'^8=!1'T#;!3,_T=!4,d4+E+E#:#9N!1'U#;!1'V#;!1'W#;!1'X#;!1'Y#;!1'Z#;-_>RN$x;R!2+_>+E+32^=1$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E2!3'eI^>#4#31$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+32!2'cQ^?#82$bh;R+3-^;RN$x;R!1+^;+32!2'cQ7#82$nh;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8^A!2'_:@!2'd=:#:!2'_:@!2'd=:#9!4'd0:#8#7#9C!4'd0:#4#3#5!5'cT::#4#3#52!2,^<+C!=,N!4'^5^C^D!4'b?!4'b?:#8#7#9#4#3#5^E^F^G^H^I^J^K^L^M^N^O^P^QWWW!1'aB1$cs;R+C$b;R+E$n;R+Evdvd!6'_W0!1'd=1$z;R0!3+^N2-_>RN$x;R!2+_>+E+3231$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E261$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+3292$bh;R+3-^;RN$x;R!1+^;+32<2$nh;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8?!2'_:@!1#9#;!2'_:@!1#9#:!4'c\B#8#7#:C!4'c\B#4#3#5D2VWWW^2!6'_W^3!1'd01$b;R^3!3+^N2-_>RN$x;R!2+_>+E+3231$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E261$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+3292$bh;R+3-^;RN$x;R!1+^;+32<2$nh;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8[^4C!3#9#4#3#5D2VWWW^2!6'_W^6!1'b?1$l;R^6!3+^N2-_>RN$x;R!2+_>+E+3231$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E261$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+3292$bh;R+3-^;RN$x;R!1+^;+32<2$nh;R+3-1RN$~R+12!2'_8\D2!2,^<+C!=,N!4'^5FG!4'bD^4#4#3#5HIJKLMOPQRSTUWWW^2!6'_W^7!1'cT1$b;R^7!3+^N2-_>RN$x;R!2+_>+E+3231$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E261$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+3292$bh;R+3-^;RN$x;R!1+^;+32<2$nh;R+3-1RN$~R+12!2'_8\!4#9A#4#3#52^8WWW^2!6'_W^9!1'eI1$p;R^9!3+^N2-_>RN$x;R!2+_>+E+3231$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E2!2#3#5#41$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+3292$bh;R+3-^;RN$x;R!1+^;+32<2$nh;R+3^:WW^2!6'_W^;!1'cQ1$o;R^;!3+^N2-_>RN$x;R!2+_>+E+3231$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E2X1$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+32!1#7#92$bh;R+3-^;RN$x;R!1+^;+32!1#8#92$nh;R+3^:WW^2!6'_W^<'b?$l;R^<!3+^N2-_>RN$x;R!2+_>+E+3231$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E2X1$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+32Y2$bh;R+3-^;RN$x;R!1+^;+32Z2$nh;R+3-1RN$~R+12^02!2,^<+C!=,N!4'^5FG!4#9^1#4#3#5HIJKLMOPQRSTUWWW^2!2,^H2^R'bD'gP!1'cP^S!1'cR1!1'eH^S!1'eT1!1'cS^S!1'gR1!1'b>^S!1'bE1!1'c\^S!1'eO1!1'd:^S!1'd>1!3+^N2-_>RN$x;R!2+_>+E+32^=1$bb;R+E$bk;R+3-_>RN$x;R!2+_>4+E2!3'eH!1'aB^>#4#31$p;R4$sn;R+E-_>RN$p;R!2+_>+E+32#21$sb;R+E$sk;R+3-^;RN$x;R!1+^;+32!2'cP!1'aB^?#82$bh;R+3-^;RN$x;R!1+^;+32!2'cP8#82$nh;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8^A!2'_:@!2'd:;#:!2'_:@!2'd:;#9!4'c\;#8#7#9C!4'c\;#4#3#5!5'cS;:#4#3#52!2,^<+C!=,N!4'^5^C^D!4'bD!4'b>;#8#7#9#4#3#5^E^F^G^H^I^J^K^L^M^N^O^P^QWWW^R!3+^N2!3'gZ#3#2#1!3'g[#3#2#1").
Qed.


(* [comment removed for export] *)
Definition node_havocbrk (cs : acs) (lo hi : Z) : option acs :=
  match xlo (kn cs) (a_brk cs), xhi (kn cs) (a_brk cs) with
  | Some l, Some h =>
      if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (EVar v) (a_fd cs) (a_tidset cs) (a_hna cs) (a_hlz cs))
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
Fixpoint kfind_litword (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match k with
  | [] => None
  | KWord (SA b' off') n' (ELit c) :: r =>
      if (expr_eqb b' b && Z.eqb off' off && Nat.eqb n' n)%bool then Some c else kfind_litword r b off n
  | _ :: r => kfind_litword r b off n
  end.

Definition node_absword (cs : acs) (b : expr) (off : Z) (n : nat) (lo hi : Z) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S60!1+^;+C}1!1+2+[!1'^9#9!1,^L#3!1,^2+C$cs;R+C$b;R+E$off;R+3$n;R+5$lo;R+3$hi;R+3-1RN$~R+10!2'_8!2'_8!1'a?#6!2'`U1#3!2'`U#3}82-^;RN$x;R!1+^;+30!4'g\!1'^9#6#5#4#32$c;R+3-1RN$~R+10!2'_8!2'_8!2'_8!2'_:#3#1!2'_:#1#2!2'_:,I#3!2'a[#2'^>2&v;R!1'e9#7+5&ss;R!1'G#8+M&k0;R-1RN$~R+12!2'_9#8!1,H,I2!3'h03#7!1'_;#632&k';R!3,_T+[!3,`Z!2,`F#9#8#74!3,_T+[!3,a34#6#5!4'bW#1#9#8!1,H!1'_;#72!2,^<+C!2'^4#;!4'^5!1'K#3!1'F#3#1!1,_N#4555").

(* [comment removed for export] *)
Definition hop_sub (b n eb en : expr) (h : hop) : hop :=
  let g y := if expr_eqb y n then en else y in
  match h with
  | HCons x y => if expr_eqb x b then HCons eb (g y) else h
  | HSub x y => if expr_eqb x b then HSub eb (g y) else h
  end.
Definition node_habs (cs : acs) (i : nat) (lo hi nlo nhi : Z) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 6 "S70!1+^;+C!1+2+[!1,^0+[!1,^K|34;!1,^K|<000;!4'h2#=#<#4#3!1,^2+C$cs;R+C$i;R+5$lo;R+3$hi;R+3$nlo;R+3$nhi;R+3-^;RN$x;R!1+^;+`>0!3'h1+`>!1'Z#6#52$ev;R+`>&b;R!1'a<#1+E&n;R!1'a=#2+E&k;R!1'^9#91-^;RN$x;R!1+^;+30!2'cJ#1#32$blo;R+3-^;RN$x;R!1+^;+30!2'cQ#2#42$bhi;R+3-^;RN$x;R!1+^;+30!2'cQ#3!2'^P#5#42$ehi;R+3-^;RN$x;R!1+^;+30!2'cJ#4#52$nl;R+3-^;RN$x;R!1+^;+30!2'cQ#5#62$nh;R+3-1RN$~R+10!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!1'a?#?!2'_:#=#5!2'_:#4#<!2'_:#3#<!2'_:#;#2!2'_:#1#:!2'_:,I#=!2'a[#<'^>!2'_:,I#;2&v;R!1'e9#?+5&eb;R!1,^L#1+E&en;R!1,^L!1,_N#2+E&facts;R!3'^8+[!3,_T+[!3,a3#2#@#?!3,_T+[!3,a3#1#>#=!3,_T+[!3,a3!2'^P#2#1,I#?2!3'^8+[-1RN$~R+11!2'_:3!2'd=#9#;2!3,_T+[!2,a2#2422-1RN$~R+11!2'_:3!2'd=#9#:2!3,_T+[!2,a2#14221&ss;R!1'G#C+M!2,^<+C!=,N!4'^5!1'K#1!1'F#1!3'^8+[#2!1'J#1!1,_N!1,_N#5!1'O#D!1'P#D!1'Q#D!1'R#D!1'S#D!1'T#D!1'U#D!1'V#D!1'W#D!1'X#D!4'g6+`>+`>5!1'Y#D!4'g6+`>+`>5!1'Z#D6666666").

(* [comment removed for export] *)
Definition SPIN_WORD : Z := 0x6f.
Definition node_spin (cs : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S50!1'd?#1|20;|500;!1,dA2!1+d@3$cs;R+C!2'_8!2'_8!2'_:,I0!2'a[!2'^U0!1,^K1'^>-^;RN$x;R!1+^;4+1!2'dB/segs;!2'dC!1,dA|600;02$w;R4!2'aY!2'h33#1'h4,6").

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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^X0!1+2+[%b;R+E%off;R+3%n;R+E+1%k;R01!1'^9#3!1+^;+C!1'@!2'aY!1'd?#4#3!1,^2+C!1'h5#4};!2'f3#58!1'@!2'a[#1#4}:!1'_2!2'^B#6;!1'^9#8!1'aB=}<!2'^B#8?!2'cH>@!1'^9#9!1'aBB!2'^B#9?!2'cPCD!1'^9#:!1'aBF!2'^B#:;!2'cPGH|10;!2'_8!2'_8!2'_:,I#3!2'_:#2!2'^V!1,^KJ!1,^K|508;!2'a[!2'^U#1#2'^>!2'aY#2,I!2'^B#;;!2,^<+EM!1'^9#;!4'h6#;#7NO!1,^K|800;!2'aY!2'^=#6Q,I!1'aBO!2'^B#;?!4#8O#5#4T!1+^;0!2,^<0O!2'^B#<?!2'^=#2'^>!1,^20-ERN$dst;R+EVM8$d;R+3-ERN$ne;R+EVX8$n;R+3!2,^<0!3'h0!1'^9#=Y#1$n;R+5Z$op;R+^?$a;R+E$b;R+EZ$op;R+^?$a;R+E$b;R+EZ$op;R+^@$a;R+E$b;R+EZ$op;R+^@$a;R+E$b;R+EZ$sx;R+1$lo;R+5$n;R+5$e;R+EZ$sx;R+1$k0;R+5$i;R+3$n;R+5Z$n;R+5Z$op;R+^?$a;R+E$b;R+EZ$op;R+^?$a;R+E$b;R+EZ$op;R+^@$a;R+E$b;R+EZ$op;R+^@$a;R+E$b;R+EZ$sx;R+1$lo;R+5$n;R+5$e;R+EZ$sx;R+1$k0;R+5$i;R+3$n;R+5Z-1RN$~R+1V!4'cYS#5#4T2W[!1'^9#<!2,^<+E!2'^B#<;!2'a[,I#4!2'^=#7Q!2'aY^3,I!2,`F#6#5-1RN$~R+1+[^42!2,`[^5X!3,a6^5X^3!4'bY#1#6#5X!4'h6#<#8^1-1RN$~R+10^22!3,_T+[^6^7^7!2'cJ=@!2'cQBD!2'cQFH!5'cOOO#5#4T!2'_8!2'_8R!5'cTOO#5#4T^<-1RN$~R+1V!4'cZO#5#4T2W[!5'cO^0^0#6#5X!4'bW#1#6#5X-1RN$~R+14526-^;RN$x;R!1+^;+3472$ret;R+3-^;RN$x;R!1+^;+3492$c;R+3-1RN$~R+14:26-_>RN$x;R!2+_>+E+34<1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34^92$nlo;R+3-^;RN$x;R!1+^;+34^:2$nhi;R+3-^;RN$x;R!1+^;+34^;2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14^=2P-^;RN$x;R!1+^;04^>2$k0;R0-1RN$~R+14^?2!4'h6#<#8^1-1RN$~R+10^22!3,_T+[^6^@^@66666666-1RN$~R+14^?2^86%e;R+E!1+^;+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14^=2P-^;RN$x;R!1+^;04^>2$k0;R0^B66%k;R0%ub;R+E%uk;R+3%un;R+E0!4#9#1#6#5X!1'@!2'aY!1'd?#3#2!1'h5#3!2'f3#48!1'@!2'a[#1#3!1'_2!2'^B#5;!1'^9#7!2'^B#7?!2'^B#9;!4'h6#:#7!2,^<+EHF!2'^B#:?!2,^<0F-ERN$dst;R+EVH8$d;R+3-ERN$ne;R+EVT8$n;R+3!2,^<0!3'h0^0Y#1$n;R+5Z$op;R+^?$a;R+E$b;R+EZ$op;R+^?$a;R+E$b;R+EZ$op;R+^@$a;R+E$b;R+EZ$op;R+^@$a;R+E$b;R+EZ$sx;R+1$lo;R+5$n;R+5$e;R+EZ$sx;R+1$k0;R+5$i;R+3$n;R+5Z$n;R+5Z$op;R+^?$a;R+E$b;R+EZ$op;R+^?$a;R+E$b;R+EZ$op;R+^@$a;R+E$b;R+EZ$op;R+^@$a;R+E$b;R+EZ$sx;R+1$lo;R+5$n;R+5$e;R+EZ$sx;R+1$k0;R+5$i;R+3$n;R+5Z-1RN$~R+1+[^42!2,`[^5T!3,a6^5T^3!4'bW#1#6#5T-1RN$~R+14^G26-^;RN$x;R!1+^;+34^H2$ret;R+3-^;RN$x;R!1+^;+34^I2$c;R+3-1RN$~R+14^J26-_>RN$x;R!2+_>+E+34^K1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34!2'cJ^L^M2$nlo;R+3-^;RN$x;R!1+^;+34!2'cQ=@2$nhi;R+3-^;RN$x;R!1+^;+34!2'cQB^N2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2^O-1RN$~R+14!2'_8!2'_8R!5'cTFF#5#4^P!5'cOFF#5#4^P2^O-^;RN$x;R!1+^;04-1RN$~R+1V!4'cZF#5#4^P2^Q^R2$k0;R0-1RN$~R+14!5'cOOO#6#5T2!4'h6#;#8N-1RN$~R+10^22!3,_T+[^S^T^T66666666!1'aB3!4'bY#1#6#5T$cs;R+C$entry;R+3$cmax;R+3vdvd!6'_W2!1'cO3$b;R2!3+^N4-1RN$~R+14526-^;RN$x;R!1+^;+3472$ret;R+3-^;RN$x;R!1+^;+3492$c;R+3-1RN$~R+14:26-_>RN$x;R!2+_>+E+34<1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34A2$nlo;R+3-^;RN$x;R!1+^;+34E2$nhi;R+3-^;RN$x;R!1+^;+34I2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14!2'_8!2'_8R!5'cSSO#5#4TU2P-^;RN$x;R!1+^;04\2$k0;R0-1RN$~R+14!4#9^0#6#5X2^866666666^A!6'_W2!1'cT3$b;R2!3+^N4-1RN$~R+14526-^;RN$x;R!1+^;+3472$ret;R+3-^;RN$x;R!1+^;+3492$c;R+3-1RN$~R+14:26-_>RN$x;R!2+_>+E+34<1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34A2$nlo;R+3-^;RN$x;R!1+^;+34E2$nhi;R+3-^;RN$x;R!1+^;+34I2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14!2'_8!2'_8RU^<2P-^;RN$x;R!1+^;04\2$k0;R0^B6666666^A!6'_W1!1'cZ3$b;R1!3+^N4-1RN$~R+14526-^;RN$x;R!1+^;+3472$ret;R+3-^;RN$x;R!1+^;+3492$c;R+3-1RN$~R+14:26-_>RN$x;R!2+_>+E+34<1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34A2$nlo;R+3-^;RN$x;R!1+^;+34E2$nhi;R+3-^;RN$x;R!1+^;+34I2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14^=2P-^;RN$x;R!1+^;04-1RN$~R+1V!3#8#5#4T2W[2$k0;R0^B6666666^A!6'_W^C!1'cQ3$o;R^C!3+^N4-1RN$~R+14526-^;RN$x;R!1+^;+3472$ret;R+3-^;RN$x;R!1+^;+3492$c;R+3-1RN$~R+14:26-_>RN$x;R!2+_>+E+34<1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34A2$nlo;R+3-^;RN$x;R!1+^;+34!1#6D2$nhi;R+3-^;RN$x;R!1+^;+34!1#7H2$dhi;R+3^D66666^A!6'_W^C!1'cJ3$o;R^C!3+^N4-1RN$~R+14526-^;RN$x;R!1+^;+3472$ret;R+3-^;RN$x;R!1+^;+3492$c;R+3-1RN$~R+14:26-_>RN$x;R!2+_>+E+34<1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34!1#5@2$nlo;R+3-^;RN$x;R!1+^;+34^:2$nhi;R+3-^;RN$x;R!1+^;+34^;2$dhi;R+3^D66666^A!6'_W^E'bW$l;R^E!3+^N4-1RN$~R+14526-^;RN$x;R!1+^;+3472$ret;R+3-^;RN$x;R!1+^;+3492$c;R+3-1RN$~R+14:26-_>RN$x;R!2+_>+E+34<1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34^92$nlo;R+3-^;RN$x;R!1+^;+34^:2$nhi;R+3-^;RN$x;R!1+^;+34^;2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2P-1RN$~R+14^=2P-^;RN$x;R!1+^;04^>2$k0;R0-1RN$~R+14^?2!4'h6#<#8^1-1RN$~R+10^22!3,_T+[^6^F^F66666666^A!2,^H4^U'bY'h7!1'cH^V!1'cL3!1'cP^V!1'cR3!1'cY^V!1'h83!1'cS^V!1'gR3!1'cN^V!1'h93!3+^N4-1RN$~R+14^G26-^;RN$x;R!1+^;+34^H2$ret;R+3-^;RN$x;R!1+^;+34^I2$c;R+3-1RN$~R+14^J26-_>RN$x;R!2+_>+E+34^K1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34!2'cH!1'aB^L^M2$nlo;R+3-^;RN$x;R!1+^;+34!2'cP>@2$nhi;R+3-^;RN$x;R!1+^;+34!2'cPC^N2$dhi;R+3-1RN$~R+14K2-1RN$~R+14L2^O-1RN$~R+14!2'_8!2'_8R!5'cSGF#5#4^P!5'cNGF#5#4^P2^O-^;RN$x;R!1+^;04-1RN$~R+1V!4'cYG#5#4^P2^Q^R2$k0;R0-1RN$~R+14!5'cNSO#6#5T2!4'h6#;#8N-1RN$~R+10^22!3,_T+[^S^W^W66666666^U!3+^N4!3'h:#3#2#1!3'h;#3#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^D0!1+2+[!1+^;0%n;R+31%dk;R+32%db;R+E3%sk;R+34%sb;R+E5!1'aB#3!3+^N6!2'h<7#1!2'h=#1#3!1'aB#4!1'aB#5!1'aB#6!1,_N#2!1,_N#3!1,_N#4!1,_N#5!1,_N#6!1,^K|30;!2'_:A#2!1'aB#:!3'cDC#6#5!1+2+3}8!4'e3CF#6#5!1+^;+E!2,^<+E#1!2,^<+E!1,H!1'e8#1!1,^2+E!2'^U#6A!2'^U#4A!2'a\#3A!2,^<0!3,_T+[!3,`Z!2,`F#6#5F#2#1!1,^20!1,^K,_0!2'_:Q#2}1!1,^0+1!1,^0+a@!8'c?/segs;C#6#5S,6TU!1+2+a@!1+2+1!2'^U#8Q!2'^U#6Q!2'a\#5Q!2,^<0!3,_T+[!3,`Z!2,`F#8#7S#4#1!2,^<0!1,^0+[!3'cE#:#6#5!4'e4F#:#6#5-^;RN$x;R!1+^;E+1^22$l;RE,9,6!2'_8B-^;RN$x;R!1+^;+E+1^12$e;R+E,9^3-^;RN$x;R!1+^;EH^22$bs;REJK-^;RN$x;R!1+^;01!7'h=#9#;#7L#5MN2$rest;R0OP-^;RN$x;R!1+^;+E1-^;RN$x;R!1+^;+EH^12$v;R+EI^52$v;R+E^6P-2RN$scs;R!1+2+a@1#22-^;RN$x;R!1+^;01!7'h=#;#=#9Y#7Z[2$rest;R0\P$s;R+a@$l;R!1+2+a@P-1RN$~R+11^42^7-1RN$~R+11R2-c>RN$x;R+c>1!8'cB/segs;#:#6#5S,6TU3$v;R+E$scs;RW$hints;RX^8$scs;RW$hints;RXPP^0%fuel;R+5%b;R+E%off;R+3!1+^;E!3#1F#6#5-1RN$~R+11R2-c>RN$x;R+c>1V3$v;R+E$scs;RW$hints;RX^8$scs;RW$hints;RXPP^0%b;R+E%off;R+3H!2#1#6#5%rb;R+E%rk;R+3%n;R+5%sx;R+1%hints;R!1+2+1%acc;R!1+2+a@+c>!3'cE#9#5#4!4'e4F#9#5#4!1'aB#9!1,_N#7$fk;R0$fuel;R+5!4'e2$fuel;R+58!5'b0+E5!2'h<!1'aB#2,^M!2'h=,^M#2$x;R+E!5'b0+34!3'h<7,^M#1!3'h=,^M#3#1$x0;R+3!5'b0+E3!4'h<9,^M#2#1!4'h=,^M#4#2#1$x1;R+E!5'b0+32!5'h<:,^M#3#2#1!5'h=,^M#5#3#2#1$x2;R+3!5'b0+31!6'h<;,^M#4#3#2#1!6'h=,^M#6#4#3#2#1$x3;R+3!2,^H1!7'h=,^M#7#5#4#3#2#1$f;R+5$IH;R8!5'b0+E5!2'h<9<!2'h=<#4$x;R+E!5'b0+34!3'h<:=#1!3'h==#5#1$x0;R+3!5'b0+E3!4'h<;>#2#1!4'h=>#6#2#1$x1;R+E!5'b0+32!5'h<!1'aB#7?#3#2#1!5'h=?#7#3#2#1$x2;R+3!5'b0+31!6'h<!1'aB#8@#4#3#2#1!6'h=@#8#4#3#2#1$x3;R+3vd!6'_W6!2'h=#7#9$o;R6!3+^N1-1RN$~R+11!2'_8B-^;RN$x;R!1+^;+E+1D2$e;R+E,9-^;RN$x;R!1+^;E+1G2$l;RE,9,62-^;RN$x;R!1+^;+E1-^;RN$x;R!1+^;+EHD2$v;R+EI-^;RN$x;R!1+^;EHG2$bs;REJK2$v;R+E-^;RN$x;R!1+^;01!5#2#7L#5MN2$rest;R0OPP-1RN$~R+11R2-c>RN$x;R+c>1V3$v;R+E$scs;RW$hints;RX-2RN$scs;R!1+2+a@1#22-^;RN$x;R!1+^;01!5#4#9Y#7Z[2$rest;R0\P$s;R+a@$l;R!1+2+a@P$scs;RW$hints;RXPP^0^9!6'_W^:$fuel;R+5!2'e4#1#:$o;R^:!3+^N1-1RN$~R+11!2'_8B-^;RN$x;R!1+^;+E+1D2$e;R+E,9-^;RN$x;R!1+^;E+1^;2$l;RE,9,62-^;RN$x;R!1+^;+E1-^;RN$x;R!1+^;+EHD2$v;R+EI-^;RN$x;R!1+^;EH^;2$bs;REJK2$v;R+E^6P^<^9!6'_W^=!1'cE#9$o;R^=!3+^N1-1RN$~R+11!2'_8B-^;RN$x;R!1+^;+E+1^>2$e;R+E,9^32-^;RN$x;R!1+^;+E1-^;RN$x;R!1+^;+EH^>2$v;R+EI^52$v;R+E^6P^<^9!6'_W^?!2'cB/segs;#9$l;R^?!3+^N1-1RN$~R+11^42^7-1RN$~R+11R2-c>RN$x;R+c>1!6#1#6#5S,6TU3$v;R+E$scs;RW$hints;RX^8$scs;RW$hints;RXPP^0^9!2,^H1-1RN$~R+11!2'_8!2'_:A#1-^;RN$x;R!1+^;+E+1^@2$e;R+E,9-^;RN$x;R!1+^;E+1^A2$l;RE,9,62-^;RN$x;R!1+^;+E1-^;RN$x;R!1+^;+EH^@2$v;R+EI-^;RN$x;R!1+^;EH^A2$bs;REJK2$v;R+E-^;RN$x;R!1+^;01!7'h=#8#:#6!2'^U#5A#4!2'^U#3A!2'a\#2A2$rest;R0!2,^<0!3,_T+[!3,`Z!2,`F#5#4F#2#1PP-1RN$~R+11!2'_:Q#12-c>RN$x;R+c>1!8'cB/segs;#9#5#4S,6TU3$v;R+E$scs;RW$hints;RX-2RN$scs;R!1+2+a@1#22-^;RN$x;R!1+^;01!7'h=#:#<#8!2'^U#7Q#6!2'^U#5Q!2'a\#4Q2$rest;R0!2,^<0!3,_T+[!3,`Z!2,`F#7#6S#4#1P$s;R+a@$l;R!1+2+a@P$scs;RW$hints;RXPP^0!2'c?/segs;^B!2'cC#9/segs;!1'cD^B!1'h>#9!1'e3^B!1'h?#9!2'h<^B#7#6!3+^N1!7'h<^B^C#5#4#3#2#1!7'h=^C#9#5#4#3#2#1#1").
Qed.
Lemma copy_factsB_eqf : forall fk, copy_factsB (mkbc fk) = (fun fuel => copy_facts fuel fk).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10!1+2+[$fk;R0!5'b0+5%sb;R+E%sk;R+3%db;R+E%dk;R+3%n;R+3!1+^;0!1'h<!1'aB#1$fuel;R+5!2'h=#1#2$fuel;R+5!2'h@#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SaH0!1+2+[!1+^;0%fuel;R+5%sb;R+E%sk;R+3%db;R+E%dk;R+3%n;R+31!1+^;+C!1'@!2'aY!1'd?#3#2!1,^2+C!1'h5#3}:!1'_2!2'^B#47};!1'_2!2'^B#69!1'^9#8!1'aB;}<!2'^B#8=!2'cH<>!1'^9#9!1'aB@!2'^B#9=!2'cPAB!1'^9#:!1'aBD!2'^B#:7!2'cPEF!1'^9#;!1'aBH!2'^B#;9!2'cPIJ|10;!2'_8!2'_8!2'_8!2'_:,I#4!2'_:#3!2'^V!1,^KL!1,^K|508;!2'a[!2'^U#2#3'^>!2'a[!2'^U#1#3'^>!2'aY#3,I!2'^B#<7!2,^<+EO!1'^9#<!4'h6#<#9PQ!1'aBQ!2'^B#<=!2,^<0Q!2'^B#==!1'^9#>!2'^=#2'^>!1,^20-ERN$dst;R+E1O8$d;R+3-ERN$ne;R+E1V8$n;R+3!2,^<0!3'h0WX#1$n;R+5Y$op;R+^?$a;R+E$b;R+EY$op;R+^?$a;R+E$b;R+EY$op;R+^@$a;R+E$b;R+EY$op;R+^@$a;R+E$b;R+EY$sx;R+1$lo;R+5$n;R+5$e;R+EY$sx;R+1$k0;R+5$i;R+3$n;R+5Y$n;R+5Y$op;R+^?$a;R+E$b;R+EY$op;R+^?$a;R+E$b;R+EY$op;R+^@$a;R+E$b;R+EY$op;R+^@$a;R+E$b;R+EY$sx;R+1$lo;R+5$n;R+5$e;R+EY$sx;R+1$k0;R+5$i;R+3$n;R+5Y-1RN$~R+11!4'cYS#8#7T2UZ!1'^9#=!1'aB\!7'aZ^0#9#8V#7#6V!2'_8!5'cN^0\#9#8V^1!2'a[,I#5!2'_8^3!5'cS^0\#7#6V!2,^<+E!2'^B#=7!2,`F#9#8!2,`[^6V!4'h6#=#:^5!3,_T+[^7!4'bY#1#9#8V!2'_:#5!1,^K|;000;!1'aBW!2'^B#>=!4'c\^:#8#7^;!1'hA#5!2,^<+E!2'^B#?7!2'^B#?=!4'h6#?#<^>!3'^8+[#1!4'bY#3#;#:^?!5'cN^:W#8#7^;!2,^<+E!2'^B#>7|30;!1,^K^C!2'hC^D!1'_;#1!2,`F#;!2'^U#:^E}8|800;!1,^K^H-1RN$~R+1+5!2'_8!2'_8!2'_8!2'aY#6#5!2'aY!2'^=#5^D,I!2'_:#5^I^32!1'hA!2'e;#5^D,^M!2'e@,^M^J!4'g6+5+[$i;R+5!3,`Z^F^G!1,^L!2'^:!2'^:!1'e9#?'hD#1^K!6'hEW#8#7#:#9#6!2'a[,I#6!2,`F#:#9!2,a7^O^;!4'bY#2#:#9^;!5'hB#>#;^B!3'^8+[^L!3'^8+[^M-1RN$~R+10^N2!3,_T+[^P^Q^Q^J-1RN$~R+13!2'_8^A^<2^R5!1'^9#@!1'aB^T!2'^B#@=!5'cN^U^T#:#9^V!2,^<+E!2'^B#@7!2,`F#=!2'^U#<^E!1,^L!2'^:!2'^:!1'e9#A'hD#1-1RN$~R+1+5!2'_8!2'_8!2'_8!2'aY#8#7!2'aY!2'^=#7^D,I!2'_:#7^I!2'a[,I#72!1'hA!2'e;#7^D,^M!2'e@,^M^[!4'g6+5+[$i;R+5!3,`Z^Y^G^Z^\!6'hE^T#:#9#<#;#8!2'a[,I#8!2,`F#<#;!2,a7_3^V!4'bY#4#<#;^V!5'hB#@#=^X!3'^8+[_0!3'^8+[_1-1RN$~R+10_22!3,_T+[_4_5_5^[-1RN$~R+13!2'_8^W!4'c\^U#:#9^V2_65!1'^9#A!1'aB_8!2'^B#A=!5'cN_9_8#;#:_:!2,^<+E!2'^B#A7!2,`F#>!2'^U#=^E-1RN$~R+1+5!2'_8!2'_8!2'_8!2'aY#9#8!2'aY!2'^=#8^D,I!2'_:#8^I_22!1'hA!2'e;#8^D,^M!2'e@,^M_>!4'g6+5+[$i;R+5!3,`Z_=^G!1,^L!2'^:!2'^:!1'e9#B'hD#1_?!6'hE_8#;#:#=#<#9!2'a[,I#9!2,`F#=#<!2,a7_C_:!4'bY#5#=#<_:!5'hB#A#>_<!3'^8+[_@!3'^8+[_A-1RN$~R+10_B2!3,_T+[_D_E_E_>-1RN$~R+13!2'_8_;!4'c\_9#;#:_:2_F5!2'cJ;>!2'cQ@B!2'cQDF!2'cQHJ-1RN$~R+11!4'cZQ#8#7T2UZ!5'cO\\#9#8V!2'_8_M!7'b3\#9#8V#7#6V!2'_8^3!5'cT\\#7#6V!4'd0W#8#7^;!2'_8^9_P!7'h=^=W#8#7#:#9#5!2'_8!5'cOWW#8#7^;_P!4'bW#2#:#9^;-1RN$~R+13_S2!5'hB#>#;^B!3'^8+[^L!3'^8+[^M-1RN$~R+10^N2!3,_T+[^P_T_T^J5!4'd0^T#:#9^V!2'_8!5'cO^T^T#:#9^V_V!4'bW#4#<#;^V-1RN$~R+13_W2!5'hB#@#=^X!3'^8+[_0!3'^8+[_1-1RN$~R+10_22!3,_T+[_4_X_X^[5!4'd0_8#;#:_:!2'_8!5'cO_8_8#;#:_:_Z!4'bW#5#=#<_:-1RN$~R+13_[2!5'hB#A#>_<!3'^8+[_@!3'^8+[_A-1RN$~R+10_B2!3,_T+[_D_\_\_>5-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33_H2$nlo;R+3-^;RN$x;R!1+^;+33_I2$nhi;R+3-^;RN$x;R!1+^;+33_J2$dhi;R+3-^;RN$x;R!1+^;+33_K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03_L2$k0;R0-1RN$~R+13_N2-1RN$~R+13_O2!4'h6#=#:^5!3,_T+[^7!4'bW#1#9#8V-ERN$ne;R+E3V8$z;R+3-1RN$~R+13_Q2-^;RN$x;R!1+^;03_R2$kc;R0!4'h6#?#<^>!3'^8+[#1!4'bW#3#;#:^?_U_U$n;R+5_U$op;R+^?$a;R+E$b;R+E_Y$op;R+^?$a;R+E$b;R+E_Y$op;R+^@$a;R+E$b;R+E_Y$op;R+^@$a;R+E$b;R+E_Y$sx;R+1$lo;R+5$n;R+5$e;R+E`0$sx;R+1$k2;R+5$i;R+3$n;R+5`055555555%b;R+E%off;R+3%n;R+E+1!1'^9#2!3#<#8#7^;-1RN$~R+13!2'_8^A`42^R5-1RN$~R+13!2'_8^W!3#>#:#9^V2_65-1RN$~R+13!2'_8_;!3#?#;#:_:2_F5%k;R0`2-1RN$~R+13!2'_8!4#<W#8#7^;_P2^R5-1RN$~R+13!2'_8!4#>^T#:#9^V_V2_65-1RN$~R+13!2'_8!4#?_8#;#:_:_Z2_F5!2'_8_M^1-1RN$~R+13_S2^R5-1RN$~R+13_W2_65-1RN$~R+13_[2_F5-ERN$ne;R+E3V8$z;R+3-1RN$~R+13_Q2-^;RN$x;R!1+^;03_R2$kc;R0^@`=`=$n;R+5`=$op;R+^?$a;R+E$b;R+E`>$op;R+^?$a;R+E$b;R+E`>$op;R+^@$a;R+E$b;R+E`>$op;R+^@$a;R+E$b;R+E`>$sx;R+1$lo;R+5$n;R+5$e;R+E`?$sx;R+1$k2;R+5$i;R+3$n;R+5`?-1RN$~R+13_O2^8`@%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1%e;R+E!1+^;+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03_L2$k0;R0-1RN$~R+13_N2`A555%k;R0%ub;R+E%uk;R+3%un;R+E0!4#<#2#:#9^;-1RN$~R+13_S2!5'hB#>#;^B!3'^8+[^L!3'^8+[^M-1RN$~R+10^N2!3,_T+[^P`F`F^J5!4#>#4#<#;^V-1RN$~R+13_W2!5'hB#@#=^X!3'^8+[_0!3'^8+[_1-1RN$~R+10_22!3,_T+[_4`H`H^[5!4#?#5#=#<_:-1RN$~R+13_[2!5'hB#A#>_<!3'^8+[_@!3'^8+[_A-1RN$~R+10_B2!3,_T+[_D`J`J_>5!1'@!2'aY!1'd?#2#1!1'h5#2!1'_2!2'^B#37!1'_2!2'^B#59!1'^9#7!2'^B#7=!2'^B#97!2'^B#:9!2'^B#;7!4'h6#;#9!2,^<+E`TH!2'^B#;=!2,^<0H-ERN$dst;R+E1`T8$d;R+3-ERN$ne;R+E1T8$n;R+3!2,^<0!3'h0\X#1$n;R+5Y$op;R+^?$a;R+E$b;R+EY$op;R+^?$a;R+E$b;R+EY$op;R+^@$a;R+E$b;R+EY$op;R+^@$a;R+E$b;R+EY$sx;R+1$lo;R+5$n;R+5$e;R+EY$sx;R+1$k0;R+5$i;R+3$n;R+5Y$n;R+5Y$op;R+^?$a;R+E$b;R+EY$op;R+^?$a;R+E$b;R+EY$op;R+^@$a;R+E$b;R+EY$op;R+^@$a;R+E$b;R+EY$sx;R+1$lo;R+5$n;R+5$e;R+EY$sx;R+1$k0;R+5$i;R+3$n;R+5Y!2,`[^6T!4'd0\#8#7V!4'g6+5+[$i;R+5!3,`Z^F^G!1,^L!2'^:!2'^:!1'e9#>'hD#1^K!6'hE\#8#7#:#9#6!2,a7^OV!4'bW#2#:#9V-1RN$~R+13!2'_8!5'cO\\#8#7V`Z2!5'hB#=#;^5!3'^8+[`[!3'^8+[`\-1RN$~R+10^N2!3,_T+[a0a1a1^J5!1'^9#?!4'g6+5+[$i;R+5!3,`Z^Y^G!1,^L!2'^:!2'^:!1'e9#@'hD#1^\!6'hEa3#:#9#<#;#8!2,a7_3^?!4'bW#4#<#;^?-1RN$~R+13!2'_8!5'cOa3a3#:#9^?!4'd0a3#:#9^?2!5'hB#?#=^>!3'^8+[a4!3'^8+[a5-1RN$~R+10_22!3,_T+[a6a7a7^[5!4'g6+5+[$i;R+5!3,`Z_=^G^Z_?!6'hE^T#;#:#=#<#9!2,a7_C^V!4'bW#5#=#<^V-1RN$~R+13!2'_8!5'cO^T^T#;#:^V!4'd0^T#;#:^V2!5'hB#@#>^X!3'^8+[a9!3'^8+[a:-1RN$~R+10_B2!3,_T+[a;a<a<_>5-1RN$~R+13`L25-^;RN$x;R!1+^;+33`M2$ret;R+3-_>RN$x;R!2+_>+E+33`N1$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33`O1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33!2'cJ`P`Q2$nlo;R+3-^;RN$x;R!1+^;+33!2'cQ;>2$nhi;R+3-^;RN$x;R!1+^;+33!2'cQ@`R2$dhi;R+3-^;RN$x;R!1+^;+33!2'cQD`S2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2`U-^;RN$x;R!1+^;03-1RN$~R+11!4'cZH#8#7`V2`W`X2$k0;R0-1RN$~R+13!2'_8!5'cOQQ#9#8T!7'b3Q#9#8T#7#6T2-1RN$~R+13!2'_8^3!5'cTQQ#7#6T2!4'h6#<#:P!3,_T+[`Y!4'bW#1#9#8T-ERN$ne;R+E3T8$z;R+3-1RN$~R+13!2'_8^9`Z2-^;RN$x;R!1+^;03!7'h=^=\#8#7#:#9#52$kc;R0!4'h6#>#<^B!3'^8+[#1!4'bW#3#;#:^;a2a2$n;R+5a2$op;R+^?$a;R+E$b;R+Ea8$op;R+^?$a;R+E$b;R+Ea8$op;R+^@$a;R+E$b;R+Ea8$op;R+^@$a;R+E$b;R+Ea8$sx;R+1$lo;R+5$n;R+5$e;R+Ea=$sx;R+1$k2;R+5$i;R+3$n;R+5a=55555555!1'aB`3!4'c\^0#8#7V!4'bY#2#:#9V-1RN$~R+13!2'_8!5'cN^0\#8#7Va@2!5'hB#=#;^5!3'^8+[`[!3'^8+[`\-1RN$~R+10^N2!3,_T+[a0aAaA^J5!1'aBa3!4'bY#4#<#;^?-1RN$~R+13!2'_8!5'cNaCa3#:#9^?!4'c\aC#:#9^?2!5'hB#?#=^>!3'^8+[a4!3'^8+[a5-1RN$~R+10_22!3,_T+[a6aDaD^[5!4'bY#5#=#<^V-1RN$~R+13!2'_8!5'cN^U^T#;#:^V!4'c\^U#;#:^V2!5'hB#@#>^X!3'^8+[a9!3'^8+[a:-1RN$~R+10_B2!3,_T+[a;aFaF_>5$cs;R+C$entry;R+3vdvd!6'_W2$fuel;R+5!2'h=#1!1'^9#3$o;R2!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33?2$nlo;R+3-^;RN$x;R!1+^;+33C2$nhi;R+3-^;RN$x;R!1+^;+33G2$dhi;R+3-^;RN$x;R!1+^;+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03[2$k0;R0-1RN$~R+13^22-1RN$~R+13^42^8-ERN$ne;R+E3V8$z;R+3-1RN$~R+13!2'_8^9^<2-^;RN$x;R!1+^;03!6#<^=#8#7#:#9#52$kc;R0^@^S^S$n;R+5^S$op;R+^?$a;R+E$b;R+E_7$op;R+^?$a;R+E$b;R+E_7$op;R+^@$a;R+E$b;R+E_7$op;R+^@$a;R+E$b;R+E_7$sx;R+1$lo;R+5$n;R+5$e;R+E_G$sx;R+1$k2;R+5$i;R+3$n;R+5_G55555555`1!6'_W`2!1'd0`3$b;R`2!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33?2$nlo;R+3-^;RN$x;R!1+^;+33C2$nhi;R+3-^;RN$x;R!1+^;+33G2$dhi;R+3-^;RN$x;R!1+^;+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03[2$k0;R0-1RN$~R+13^22-1RN$~R+13^42^8-ERN$ne;R+E3V8$z;R+3-1RN$~R+13!2'_8^9`42-^;RN$x;R!1+^;03_R2$kc;R0^@`5`5$n;R+5`5$op;R+^?$a;R+E$b;R+E`6$op;R+^?$a;R+E$b;R+E`6$op;R+^@$a;R+E$b;R+E`6$op;R+^@$a;R+E$b;R+E`6$sx;R+1$lo;R+5$n;R+5$e;R+E`7$sx;R+1$k2;R+5$i;R+3$n;R+5`755555555`1!6'_W`8!1'cO`3$b;R`8!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33?2$nlo;R+3-^;RN$x;R!1+^;+33C2$nhi;R+3-^;RN$x;R!1+^;+33G2$dhi;R+3-^;RN$x;R!1+^;+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03[2$k0;R0-1RN$~R+13!2'_8!4#;\#9#8V^12-1RN$~R+13^42^8-ERN$ne;R+E3V8$z;R+3-1RN$~R+13_Q2-^;RN$x;R!1+^;03_R2$kc;R0^@`9`9$n;R+5`9$op;R+^?$a;R+E$b;R+E`:$op;R+^?$a;R+E$b;R+E`:$op;R+^@$a;R+E$b;R+E`:$op;R+^@$a;R+E$b;R+E`:$sx;R+1$lo;R+5$n;R+5$e;R+E`;$sx;R+1$k2;R+5$i;R+3$n;R+5`;55555555`1!6'_W`8!1'cT`3$b;R`8!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33?2$nlo;R+3-^;RN$x;R!1+^;+33C2$nhi;R+3-^;RN$x;R!1+^;+33G2$dhi;R+3-^;RN$x;R!1+^;+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03[2$k0;R0-1RN$~R+13`<2-1RN$~R+13!2'_8^3!4#;\#7#6V2^8`@55555555`1!6'_W`2!1'cZ`3$b;R`2!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33?2$nlo;R+3-^;RN$x;R!1+^;+33C2$nhi;R+3-^;RN$x;R!1+^;+33G2$dhi;R+3-^;RN$x;R!1+^;+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03-1RN$~R+11!3#:#8#7T2UZ2$k0;R0-1RN$~R+13`<2`A55555555`1!6'_W`B!1'b3`3$b;R`B!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33?2$nlo;R+3-^;RN$x;R!1+^;+33C2$nhi;R+3-^;RN$x;R!1+^;+33G2$dhi;R+3-^;RN$x;R!1+^;+33K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03_L2$k0;R0-1RN$~R+13!2'_8_M!6#;#9#8V#7#6V2`A55555555`1!6'_W`C!1'cQ`3$o;R`C!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33?2$nlo;R+3-^;RN$x;R!1+^;+33!1#7B2$nhi;R+3-^;RN$x;R!1+^;+33!1#8F2$dhi;R+3-^;RN$x;R!1+^;+33!1#9J2$shi;R+3`D55555`1!6'_W`C!1'cJ`3$o;R`C!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33!1#6>2$nlo;R+3-^;RN$x;R!1+^;+33_I2$nhi;R+3-^;RN$x;R!1+^;+33_J2$dhi;R+3-^;RN$x;R!1+^;+33_K2$shi;R+3`D55555`1!6'_W`E'bW$l;R`E!3+^N3-1RN$~R+13425-^;RN$x;R!1+^;+3362$ret;R+3-_>RN$x;R!2+_>+E+3381$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33:1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33_H2$nlo;R+3-^;RN$x;R!1+^;+33_I2$nhi;R+3-^;RN$x;R!1+^;+33_J2$dhi;R+3-^;RN$x;R!1+^;+33_K2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2R-^;RN$x;R!1+^;03_L2$k0;R0-1RN$~R+13_N2-1RN$~R+13_O2!4'h6#=#:^5!3,_T+[^7!4#;#1#9#8V-ERN$ne;R+E3V8$z;R+3-1RN$~R+13_Q2-^;RN$x;R!1+^;03_R2$kc;R0!4'h6#?#<^>!3'^8+[#1!4#=#3#;#:^?`G`G$n;R+5`G$op;R+^?$a;R+E$b;R+E`I$op;R+^?$a;R+E$b;R+E`I$op;R+^@$a;R+E$b;R+E`I$op;R+^@$a;R+E$b;R+E`I$sx;R+1$lo;R+5$n;R+5$e;R+E`K$sx;R+1$k2;R+5$i;R+3$n;R+5`K55555555`1!2,^H3a>'bY'h7!1'cHa?!1'cL`3!1'cPa?!1'cR`3!1'aZa?!1'b4`3!1'cYa?!1'h8`3!1'cSa?!1'gR`3!1'cNa?!1'h9`3!1'c\a?!1'eO`3!1'h<a?!1'hF`3!3+^N3-1RN$~R+13`L25-^;RN$x;R!1+^;+33`M2$ret;R+3-_>RN$x;R!2+_>+E+33`N1$db;R+E$dk;R+3-_>RN$x;R!2+_>+E+33`O1$sb;R+E$sk;R+3-^;RN$x;R!1+^;+33!2'cH!1'aB`P`Q2$nlo;R+3-^;RN$x;R!1+^;+33!2'cP<>2$nhi;R+3-^;RN$x;R!1+^;+33!2'cPA`R2$dhi;R+3-^;RN$x;R!1+^;+33!2'cPE`S2$shi;R+3-1RN$~R+13M2-1RN$~R+13N2`U-^;RN$x;R!1+^;03-1RN$~R+11!4'cYI#8#7`V2`W`X2$k0;R0-1RN$~R+13!2'_8!5'cNSQ#9#8T!7'aZS#9#8T#7#6T2-1RN$~R+13!2'_8^3!5'cSSQ#7#6T2!4'h6#<#:P!3,_T+[`Y!4'bY#1#9#8T-ERN$ne;R+E3T8$z;R+3-1RN$~R+13!2'_8^9a@2-^;RN$x;R!1+^;03!7'h<^0^=#8#7#:#9#52$kc;R0!4'h6#>#<^B!3'^8+[#1!4'bY#3#;#:^;aBaB$n;R+5aB$op;R+^?$a;R+E$b;R+EaE$op;R+^?$a;R+E$b;R+EaE$op;R+^@$a;R+E$b;R+EaE$op;R+^@$a;R+E$b;R+EaE$sx;R+1$lo;R+5$n;R+5$e;R+EaG$sx;R+1$k2;R+5$i;R+3$n;R+5aG55555555a>!3+^N3!2'hG#2#1!2'hH#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^H0!1+2+[%ub;R+E%uk;R+3%un;R+E0!1'^9#1!1+^;+C!1'hI/A;!1'@!2'aY!1'd?#24!1,^2+C!1'h5#2}:!1'_2!2'^B#38}2|40;!1,hJ;!1'_2!2'^Y!2'^B#5:<!1'^9#7!1'aB>};!2'^B#7@!2'cH?A!1'^9#8!1'aBC!2'^B#8@!2'cPDE!1'^9#9!1'aBG!2'^B#98!2'cPHI!1'^9#:!1'aBK!2'^B#::!2'cHLM!1'^9#;!1'aBO!2'^B#;:!2'cPPQ|10;|30;!1,^K;!2'_8!2'_8!2'_8!2'_8!2'_:,I#5!2'_:#4!2'^V!1,^KS!1,^K|508;!2'_:!2'^U!2'^U#3#4!1,^KT'^>!2'_:U#2!2'a[#1'^>!1'^9#<!1'aBW!1,HU!2'^B#<@!7'aZX#7#6Y#9#8Z!5'cSXW#9#8Z!2,^<+E!1,H!1,^K,_0!2'cQCE!2'cQGI!2'_8V!5'cGWW#7#6U!5'cTWW#9#8Z!4'h6#<#:^0!4'bWW#7#6Y-1RN$~R+13!2'_8!2'_8^3!7'b3W#7#6Y#9#8Z^42^56-^;RN$x;R!1+^;+33!2'cQOQ2$sphi;R+3^66-1RN$~R+13526-^;RN$x;R!1+^;+3372$ret;R+3-_>RN$x;R!2+_>+E+3391$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33=1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33!2'cJ>A2$nlo;R+3-^;RN$x;R!1+^;+33^12$nhi;R+3-^;RN$x;R!1+^;+33^22$bhi;R+3-^;RN$x;R!1+^;+33!2'cJKM2$splo;R+3^766666%k;R0%b;R+E%off;R+3%n;R+3+1%k;R0%b;R+E%off;R+3%n;R+E+1%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1%e;R+E!1+^;+3!1'@!2'aY!1'd?#14!1'h5#1!1'_2!2'^B#28!1'_2!2'^Y!2'^B#4:<!1'^9#6!2'^B#6@!2'^B#88!2'^B#9:!2'^B#;@-1RN$~R+13^=26-^;RN$x;R!1+^;+33^>2$ret;R+3-_>RN$x;R!2+_>+E+33^?1$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33^@1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33!2'cJ^A^B2$nlo;R+3-^;RN$x;R!1+^;+33!2'cQ>A2$nhi;R+3-^;RN$x;R!1+^;+33!2'cQC^C2$bhi;R+3-^;RN$x;R!1+^;+33!2'cJG^D2$splo;R+3-^;RN$x;R!1+^;+33!2'cQKM2$sphi;R+3-1RN$~R+13!2'_8!2'_8!2'_8V!5'cGOO#7#6U!7'b3O#7#6Y#9#8^E!5'cTOO#9#8^E2!4'h6#;#:^0!4'bWO#7#6Y6666666!1'aB2$cs;R+Cvdvd!6'_W1!1'bW2$l;R1!3+^N3-1RN$~R+13526-^;RN$x;R!1+^;+3372$ret;R+3-_>RN$x;R!2+_>+E+3391$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33=1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33B2$nlo;R+3-^;RN$x;R!1+^;+33F2$nhi;R+3-^;RN$x;R!1+^;+33J2$bhi;R+3-^;RN$x;R!1+^;+33N2$splo;R+3-^;RN$x;R!1+^;+33R2$sphi;R+3-1RN$~R+13!2'_8!2'_8!2'_8V!5'cFXW#7#6U[\2!4'h6#<#:^0!3#;#7#6Y6666666^8!6'_W^9!1'cG2$b;R^9!3+^N3-1RN$~R+13526-^;RN$x;R!1+^;+3372$ret;R+3-_>RN$x;R!2+_>+E+3391$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33=1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33B2$nlo;R+3-^;RN$x;R!1+^;+33F2$nhi;R+3-^;RN$x;R!1+^;+33J2$bhi;R+3-^;RN$x;R!1+^;+33N2$splo;R+3-^;RN$x;R!1+^;+33R2$sphi;R+3-1RN$~R+13!2'_8!2'_8!2'_8V!4#;W#7#6U[\2^56666666^8!6'_W^:!1'cT2$b;R^:!3+^N3-1RN$~R+13526-^;RN$x;R!1+^;+3372$ret;R+3-_>RN$x;R!2+_>+E+3391$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33=1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33B2$nlo;R+3-^;RN$x;R!1+^;+33F2$nhi;R+3-^;RN$x;R!1+^;+33J2$bhi;R+3-^;RN$x;R!1+^;+33N2$splo;R+3-^;RN$x;R!1+^;+33R2$sphi;R+3-1RN$~R+13!2'_8!2'_8^3[!4#;W#9#8Z2^56666666^8!6'_W^;!1'b32$b;R^;!3+^N3-1RN$~R+13526-^;RN$x;R!1+^;+3372$ret;R+3-_>RN$x;R!2+_>+E+3391$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33=1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33B2$nlo;R+3-^;RN$x;R!1+^;+33F2$nhi;R+3-^;RN$x;R!1+^;+33J2$bhi;R+3-^;RN$x;R!1+^;+33N2$splo;R+3-^;RN$x;R!1+^;+33R2$sphi;R+3-1RN$~R+13!2'_8!2'_8^3!6#;#7#6Y#9#8Z^42^56666666^8!6'_W^<!1'cQ2$o;R^<!3+^N3-1RN$~R+13526-^;RN$x;R!1+^;+3372$ret;R+3-_>RN$x;R!2+_>+E+3391$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33=1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33B2$nlo;R+3-^;RN$x;R!1+^;+33!1#7E2$nhi;R+3-^;RN$x;R!1+^;+33!1#8I2$bhi;R+3-^;RN$x;R!1+^;+33N2$splo;R+3-^;RN$x;R!1+^;+33!1#:Q2$sphi;R+3^6666666^8!6'_W^<!1'cJ2$o;R^<!3+^N3-1RN$~R+13526-^;RN$x;R!1+^;+3372$ret;R+3-_>RN$x;R!2+_>+E+3391$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33=1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33!1#6A2$nlo;R+3-^;RN$x;R!1+^;+33^12$nhi;R+3-^;RN$x;R!1+^;+33^22$bhi;R+3-^;RN$x;R!1+^;+33!1#9M2$splo;R+3^766666^8!2,^H3^F!1'cH^G!1'cL2!1'cP^G!1'cR2!1'aZ^G!1'b42!1'cS^G!1'gR2!1'cF^G!1'hK2!1'bV^G!1'bZ2!3+^N3-1RN$~R+13^=26-^;RN$x;R!1+^;+33^>2$ret;R+3-_>RN$x;R!2+_>+E+33^?1$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+33^@1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+33!2'cH!1'aB^A^B2$nlo;R+3-^;RN$x;R!1+^;+33!2'cP?A2$nhi;R+3-^;RN$x;R!1+^;+33!2'cPD^C2$bhi;R+3-^;RN$x;R!1+^;+33!2'cHH^D2$splo;R+3-^;RN$x;R!1+^;+33!2'cPLM2$sphi;R+3-1RN$~R+13!2'_8!2'_8!2'_8V!5'cFPO#7#6U!7'aZP#7#6Y#9#8^E!5'cSPO#9#8^E2!4'h6#;#:^0!4'bVP#7#6Y6666666^F!3+^N3!1'hL#1!1'hM#1").
Qed.


(* [comment removed for export] *)
Definition img_cov (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.

Definition img_covB (bc : bctx) (a b : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$bc;R+aK$a;R+3$b;R+3!3'_6+[$K;R+[-[RN$K;R+[+1#1:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n;R+E,6$a0;R+^3$n;R+E$k;R+5,6$lo;R+3$hi;R+3!2'_8!2'_:#2#5!2'_:#4#1$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n;R+E$c;R+3,6$a0;R+^3$n;R+E,6!1'b=#3").
Lemma img_covB_eqf : forall fk, img_covB (mkbc fk) = img_cov fk.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S30!1+2+[!2'_8!2'_:#2#6!2'_:#5#1!1'aB#3$fk;R0!5'b0+3%b;R+3+1!1'hN!1'aB#1!1'hO#1$x;R+3!5'b0+3+1!2'hN!1'aB#2#1!2'hO#2#1$x0;R+3vd!6'_W0#3$l;R0!3+^N+1!3'_6+[$K;R+[-[RN$K;R+[+1#1:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n;R+E,6$a0;R+^3$n;R+E$k;R+5,6$lo;R+3$hi;R+31$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n;R+E$c;R+3,6$a0;R+^3$n;R+E,6#1!3'_6+[$K;R+[-[RN$K;R+[+1#1:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n;R+E,6$a0;R+^3$n;R+E$k0;R+5,6$lo;R+3$hi;R+31$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n;R+E$c;R+3,6$a0;R+^3$n;R+E,6#4!2,^H+1!3'_6+[$K;R+[-[RN$K;R+[+1#1:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n;R+E,6$a0;R+^3$n;R+E$k0;R+5,6$lo;R+3$hi;R+3!2'_8!2'_:#2#5!2'_:#4#1$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n;R+E$c;R+3,6$a0;R+^3$n;R+E,6#3!1'b=2!1'bA#3!3+^N+1!3'hN2#2#1!3'hO#3#2#1").
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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^E0!1+2+[%b;R+E%off;R+3%n;R+E+1%k;R01!1'^9#1!1+^;+C!1'hP/A;!1'@!2'aY!1'd?#25!1,^2+C!1'h5#2};!2'f3#39}<!2'f3#4;!1'hQ/A;!1,^K|;7ff;!1'@!2'_8!2'aY#2=!2'aY#1>}:!1'_2!2'^B#5@!1'^9#7!1'aBB!2'^B#7@!2'cPCD!1+^;0!1'^9#8!1'aBG!1,H>!2,^<0G!2'^B#8@!1'^9#9!2'^=#1'^>!1,^20-ERN$dst;R+EFK8$d;R+3!2,^<0!3'h0LM>$n0;R+5N$op;R+^?$a;R+E$b;R+EN$op;R+^?$a;R+E$b;R+EN$op;R+^@$a;R+E$b;R+EN$op;R+^@$a;R+E$b;R+EN$sx;R+1$lo;R+5$n0;R+5$e;R+EN$sx;R+1$k0;R+5$i;R+3$n0;R+5N!1,^K|31;!2'^U=P!2'_8!2'_8!2'a[!2'^U#2>'^>!2'_:,I=!2'a[Q'^>!3'hO#1=Q!1,H,I!1,HP!7'aZ!1'aBL#4#3IT=U!2,^<+E!2'^B#9@}8!3,`Z!2,`F#4#3X!1,H'hR!2,`[!2,`F#4!2'^U#3!1,^K|30;!1,H!1,^K|;7f7;!3,_T+[Y!3,_T+[Z!4'bY#1#4#3I!4'h6#9#7W[!2'cQBD-1RN$~R+1F!4'cZG#3#2I2JO!2'_8!2'_8R!5'cOLL#4#3IS!2'_8^2!7'b3L#4#3IT=U!3,_T+[Y!3,_T+[Z!4'bW#1#4#3I-1RN$~R+14627-^;RN$x;R!1+^;+3482$ret;R+3-^;RN$x;R!1+^;+34:2$src;R+3-^;RN$x;R!1+^;+34<2$n;R+3-1RN$~R+14?27-_>RN$x;R!2+_>+E+34A1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34^02$dhi;R+3-^;RN$x;R!1+^;04^12$k0;R0-1RN$~R+14^32!4'h6#9#7W^4777777%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1%e;R+E!1+^;+3%k;R0%ub;R+E%uk;R+3%un;R+E0!1'@!2'aY!1'd?#15!1'h5#1!2'f3#29!2'f3#3;!1'_2!2'^B#4@!1'^9#6!2'^B#6@!2,^<0B-ERN$dst;R+EFD8$d;R+3!2,^<0!3'h0GM>$n0;R+5N$op;R+^?$a;R+E$b;R+EN$op;R+^?$a;R+E$b;R+EN$op;R+^@$a;R+E$b;R+EN$op;R+^@$a;R+E$b;R+EN$sx;R+1$lo;R+5$n0;R+5$e;R+EN$sx;R+1$k0;R+5$i;R+3$n0;R+5N!2,^<+EK-1RN$~R+14^927-^;RN$x;R!1+^;+34^:2$ret;R+3-^;RN$x;R!1+^;+34^;2$src;R+3-^;RN$x;R!1+^;+34^<2$n;R+3-1RN$~R+14?27-_>RN$x;R!2+_>+E+34^=1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34!2'cQ^>^?2$dhi;R+3-^;RN$x;R!1+^;04-1RN$~R+1F!4'cZB#3#2I2^@^A2$k0;R0-1RN$~R+14!2'_8!2'_8!2'_8R!5'cOGG#4#3IS!7'b3G#4#3IT=U2!4'h6#8#7^B^4777777!1'aB3$cs;R+Cvdvd!6'_W2!1'cO3$b;R2!3+^N4-1RN$~R+14627-^;RN$x;R!1+^;+3482$ret;R+3-^;RN$x;R!1+^;+34:2$src;R+3-^;RN$x;R!1+^;+34<2$n;R+3-1RN$~R+14?27-_>RN$x;R!2+_>+E+34A1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34E2$dhi;R+3-^;RN$x;R!1+^;04-1RN$~R+1F!4'cYH#3#2I2JO2$k0;R0-1RN$~R+14!2'_8!2'_8!2'_8R!4#8L#4#3ISV2\777777^5!6'_W1!1'cZ3$b;R1!3+^N4-1RN$~R+14627-^;RN$x;R!1+^;+3482$ret;R+3-^;RN$x;R!1+^;+34:2$src;R+3-^;RN$x;R!1+^;+34<2$n;R+3-1RN$~R+14?27-_>RN$x;R!2+_>+E+34A1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34E2$dhi;R+3-^;RN$x;R!1+^;04-1RN$~R+1F!3#7#3#2I2JO2$k0;R0-1RN$~R+14!2'_8^2V2\777777^5!6'_W^6!1'b33$b;R^6!3+^N4-1RN$~R+14627-^;RN$x;R!1+^;+3482$ret;R+3-^;RN$x;R!1+^;+34:2$src;R+3-^;RN$x;R!1+^;+34<2$n;R+3-1RN$~R+14?27-_>RN$x;R!2+_>+E+34A1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34E2$dhi;R+3-^;RN$x;R!1+^;04^12$k0;R0-1RN$~R+14!2'_8^2!6#8#4#3IT=U2\777777^5!6'_W^7!1'cQ3$o;R^7!3+^N4-1RN$~R+14627-^;RN$x;R!1+^;+3482$ret;R+3-^;RN$x;R!1+^;+34:2$src;R+3-^;RN$x;R!1+^;+34<2$n;R+3-1RN$~R+14?27-_>RN$x;R!2+_>+E+34A1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34!1#6D2$dhi;R+3-^;RN$x;R!1+^;04^12$k0;R0-1RN$~R+14^32\777777^5!6'_W^8'bW$l;R^8!3+^N4-1RN$~R+14627-^;RN$x;R!1+^;+3482$ret;R+3-^;RN$x;R!1+^;+34:2$src;R+3-^;RN$x;R!1+^;+34<2$n;R+3-1RN$~R+14?27-_>RN$x;R!2+_>+E+34A1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34^02$dhi;R+3-^;RN$x;R!1+^;04^12$k0;R0-1RN$~R+14^32!4'h6#9#7W!3,_T+[Y!3,_T+[Z!4#8#1#4#3I777777^5!2,^H4^C'bY'h7!1'cP^D!1'cR3!1'aZ^D!1'b43!1'cY^D!1'h83!1'cN^D!1'h93!3+^N4-1RN$~R+14^927-^;RN$x;R!1+^;+34^:2$ret;R+3-^;RN$x;R!1+^;+34^;2$src;R+3-^;RN$x;R!1+^;+34^<2$n;R+3-1RN$~R+14?27-_>RN$x;R!2+_>+E+34^=1$db;R+E$dk;R+3-^;RN$x;R!1+^;+34!2'cP!1'aB^>^?2$dhi;R+3-^;RN$x;R!1+^;04-1RN$~R+1F!4'cYC#3#2I2^@^A2$k0;R0-1RN$~R+14!2'_8!2'_8!2'_8R!5'cNHG#4#3IS!7'aZH#4#3IT=U2!4'h6#8#7^B[777777^C!3+^N4!1'hS#1!1'hT#1").
Qed.


(* [comment removed for export] *)
Definition popfree_facts (lb : expr) (lk : Z) (cnt c s : Z) (K : nat) : list kentry :=
  map (fun t => KWord (SA lb (lk + 4 * (cnt - 1 - Z.of_nat t))) 4 (ELit ((c + Z.of_nat t * s) / 16))) (seq 0 K).
Definition summary_popfree (cs : acs) (args : list expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S@0!1+2+E!1+2+[!1+^;+C!1,^2+C}:}<}C};|20;!1,^K8!1,^K|500;!1,H!2'hC9#6!1,^0+[}>|40;}?$cs;R+C$args;R0&k;R!1'^9#21-1RN$~R+12!1'@!2'aY!1'd?#3!1'hU/A;23-2RN$args;R!1+2+E2#223$e;R+E$l;R!1+2+E-ERN$e;R+E2#28$K;R+3-2RN$l;R!1+2+E2#22-^;RN$x;R!1+^;+32!2'f3#642$i;R+3-^;RN$x;R!1+^;+32!2'f3#752$c;R+3-^;RN$x;R!1+^;+32!2'f3#8}E2$s;R+3-^;RN$x;R!1+^;+32!2'f3#962$n;R+3&e;R!2'^B#:7+E&cnt;R!2'a\#2#5+3&lo;R!2'^Y#2!1'eZ!2'hC9#3+E-_>RN$x;R!2+_>+E+32!1'_2#11$lb;R+E$lk;R+3-^;RN$x;R!1+^;+32!2'cJ#=#52$el;R+3-^;RN$x;R!1+^;+32!2'cQ#>#62$eh;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_:,I#;!2'a[#;#8!2'_:!2'hC9#8#2!2'a[#1'^>!2'_:,I#:!2'_:,I#9!2'a[!2'^U#:!2'hC#6#9'^>!2'_:,I#<!2'_:#<#6!2'a[!2'^U!1'd?#A:'^>!1'a?#A!5'cO#?#?#4#3;!4'cZ#?#4#3;2&k1;R!4'bW#?#4#3;1&kunk;R-1RN$~R+11!2'a[#=#72!3,_T+[!2,a7!2,`F#5#4!1,H!2'hC9!2'a\#7#=<<1&sr;R!1'F!1'G#C0&sr';R!3'^6!3'^6!3'^6!3'^6#14!1,H#;5!1,H!2'^U#=!2'hC#9#<=!1,H!2'e;!2'^U#=!2'hC!2'a\#9!1,^K,_0#<!1,^K>?#80!2,^<+C!2'^4#E!4'^5!2'^U!1'd?#E:#1!3'^8+[!6'hV#8#7#:#>#=!1'hA#@!3'^8+[#3#4!1'e9#E3333333$e0;R+E$l0;R!1+2+E3$n;R+53$op;R+^?$a;R+E$b;R+E3$op;R+^?$a;R+E$b;R+E3$op;R+^@$a;R+E$b;R+E3$op;R+^@$a;R+E$b;R+E3$sx;R+1$lo;R+5$n;R+5$e0;R+E3$sx;R+1$k0;R+5$i;R+3$n;R+53").

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
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`J0%e;R+E+3!1'^9#1!1+^;+C!1'hW/A;!1'@!2'aY!1'd?#23!1,^2+C!1'h5#2}:!1'_2!2'^B#37}2|30;!1,hJ:!1'_2!2'^Y!2'^B#59;!1'^9#7!1'aB=};!2'^B#7?!2'cP>@!1'^9#8!1'aBB!2'^B#87!2'cPCD!1'^9#9!1'aBF!2'^B#99!2'cHGH!1'^9#:!1'aBJ!2'^B#:9!2'cPKL!1,^K:!1'hX/A;|40;!2'^UO!1,^KP!2'_8!2'_8!2'_8!2'a[!2'^U#3N'^>!2'_:!1,^K|500;#2!2'a[#1'^>!2'_:!2'^UQN#2!1'^9#;!1'aBS!1,HN!5'cFTS#6#5N!7'aZT#6#5U#8#7U!1,H,I!1'hY/A;!7'aZT#6#5UXYU!2'dT#4N!2'aY[,I!1,H[!1'hA[!6'hZ/segs;TS#8#7^1!4'h[S#8#7!2'^B#;?!3'hNTOQ!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8R!4'c\T#6#5UV!4'c\T#8#7UWZ!2'_4!2'_4\!2'_8!4'c\T#8#7^0^2^3^4|10;!2'_:#4!1,^K^6|11;!1,^K^8!2'^B#;7!1#:^:!4'c\TXYU!2'a[,I#1-^;RN$x;R!1+^;+3+1!2'cHT^:2$blo;R+3^=,6}8!1,^0+1!1,^0+a@!8'c?/segs;TXY^?,6^@^A!1+2+a@!1+2+1!1'^9#>!2'^B#>7!1'_2!2'^P#3!3'eF!1'aB^E^F^9!1'^9#@!1'aB^H!2'cP^I#5!1,^K,_0!2'a[!2'^U!2'^U#1!2'e;#9N^K'^>!1'^9#A!1'aB^M!1,H^K!7'aZ^N#<#;U#3#2^O!2'_8!2'_8^L!4'c\^N#3#2^O^P}1!8'c?/segs;^N#3#2^R,6^@^A!2+_>+3+3!1'^9#D!1'aB^U!2'h\^V#3!2'_:#1!1,^K|63f;!2'_4!2'aY#1,I!2'_8!2'_:!2'dT#@N#2^X!1'^9#G!1'aB^Z!2+_>+E+3!1,^0^\!3,_T^\!4,d4+E+3!2'^B#G?,I_0-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4^Y!2'_8^X!3'd3^[!3,_T^\!4,d4+E+3!2'h\^[#6,I_0_1!1,^2+E!4'h6#;#9_3!4'bVT#6#5U!2'cQ=@!2'cQBD!2'cQJL!2'_8R!4'd0S#6#5U!4'd0S#8#7U!2'_8!2'_8_8!5'cGSS#6#5N_9!4'd0S#8#7^0!2'_4!2'_4\!2'_8_;!6'i0/segs;SS#8#7^1^3!3'hOSOQ!2'_8!2'_8!2'_8!2'_8_:!7'b3S#6#5U#8#7U!7'b3S#6#5UXYU_<_=!2'_:^9!2'd=S^:!2'_8_?!4'd0SXYU!8'cB/segs;SXY^?,6^@^A!1'_2!2'^P#3!3'eJ^E^F^9!2'_8^L!4'd0^M#3#2^O!8'cB/segs;^M#3#2^R,6^@^A!2'dL^U!2'i1^U#3!3,_T^\!4,d4+E+3!2'i1^Z#6,I_0-c>RN$x;R+c>+1_D3$v0;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-^;RN$x;R!1+^;^T+1_E2$p;R^T-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4^Y!2'_8^X!3'd8^Z_F_1,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6!2'_8!2'_8_C!7'b3^M#<#;U#3#2^O_G-c>RN$x;R+c>+1_A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1_B1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1!2'cQ^H#52$ehi;R+3_H,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6!4'h6#;#9_3!4'bWS#6#5U-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32_52$nhi;R+3-^;RN$x;R!1+^;+32_62$bhi;R+3-^;RN$x;R!1+^;+32!2'cJFH2$splo;R+3-^;RN$x;R!1+^;+32_72$sphi;R+3-1RN$~R+12!2'_8_>!2'_4^7!2'_8!2'_8_@-^;RN$x;R!1+^;+3+1!2'cJS^:2$blo;R+3^=,6_I2_J555555%e;R+E!1+^;^T!2'_8!2'_8_?^<^>%v;R+E+E%b;R+E%off;R+3%n;R+E+1!3#:#6#5U-2RN$scs;R!1+2+a@+1#22-^;RN$x;R!1+^;^T+1_E2$p;R^T-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4^Y!2'_8^X!3'd3^[_F_1,6$s;R+a@$l;R!1+2+a@,6-c>RN$x;R+c>+1^S3$v0;R+E$scs;R^C$hints;R^D_Q$scs;R^C$hints;R^D,6,6%a;R+3%b;R+3+1!2'_8!2'_8!2'_8!2'_8_8V_9WZ!2'_8_T!2'_4!2'_4\!2'_8_;^2^3!2'_8_@^>!2'_8_C^P!2'_4^7!2'_8_V-c>RN$x;R+c>+1^B3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1^G1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8_W_R,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6!1+2+[%ub;R+E%uk;R+3%un;R+E_Y%kn;R_Y%rb;R+E%rk;R+3%n;R+5+1%rb;R+E%rk;R+3%n;R+5%sx;R+1%hints;R!1+2+1%acc;R!1+2+a@+c>%k;R_Y%b;R+E%off;R+3%n;R+3+1%pos;R'd7%neg;R'd7+1!2'_8!2'_8!2'_8!2'_8_:WZ_<_=%a;R+E%s;R+3+E%b1;R+E%k1;R+3%n1;R+E%b2;R+E%k2;R+3%n2;R+E+1%e;R+E!1+^;+3!1'@!2'aY!1'd?#13!1'h5#1!1'_2!2'^B#27!1'_2!2'^Y!2'^B#49;!1'^9#6!2'^B#6?!2'^B#77!2'^B#89!4'h[J#8#7!2'^B#:?!2'^B#:7!1'^9#=!2'^B#=7!1'^9#?!1'^9#C!1'^9#F!3,_T^\!4,d4+E+3!2'^B#F?,I_0-1RN$~R+12`625-^;RN$x;R!1+^;+32`72$ret;R+3-_>RN$x;R!2+_>+E+32`81$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32`91$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32!2'cQ`:`;2$nhi;R+3-^;RN$x;R!1+^;+32!2'cQ=`<2$bhi;R+3-^;RN$x;R!1+^;+32!2'cJB`=2$splo;R+3-^;RN$x;R!1+^;+32!2'cQFH2$sphi;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8R!4'd0J#6#5U!5'cGJJ#6#5N!4'd0J#8#7U!7'b3J#6#5U#8#7U!7'b3J#6#5UXYU!2'_4!2'_4\!2'_8!4'd0J#8#7^0!6'i0/segs;JJ#8#7^1`>!3'hOJOQ!2'_4^7!2'_8!2'_8!2'_8!2'_:^9!2'd=J`?!4'd0JXYU-^;RN$x;R!1+^;+3+1!2'cJJ`?2$blo;R+3^=,6-c>RN$x;R+c>+1!8'cB/segs;JXY^?,6^@^A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1!1'_2!2'^P#3!3'eJ`@`A^91$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1!2'cQ`B#52$ehi;R+3!2'_8!2'_8!2'_8^L!4'd0^H#3#2^O!7'b3^H#<#;U#3#2^O-c>RN$x;R+c>+1!8'cB/segs;^H#3#2^R,6^@^A3$v0;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-^;RN$x;R!1+^;^T+1!2'dL`C!2'i1`C#32$p;R^T-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4^Y!2'_8^X!3'd8`D!3,_T^\!4,d4+E+3!2'i1`D#6,I_0`E,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62!4'h6#:#9_3!4'bWJ#6#5U555555!1'aB1!1'aB`C!1'aB`D$cs;R+Cvdvd!6'_W0!1'd=1$z;R0!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8^5!2'_4^7!2'_8!2'_8!2'_8!2'_:^9^;^<^>-c>RN$x;R+c>+1^B3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1^G1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8^Q-c>RN$x;R+c>+1^S3$v0;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-^;RN$x;R!1+^;^T+1!2'dI^V^W2$p;R^T_2,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_4555555_K!6'_W_L!1'dL1$o;R_L!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8^5!2'_4^7!2'_8_M-c>RN$x;R+c>+1^B3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1^G1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8^Q-c>RN$x;R+c>+1^S3$v0;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-^;RN$x;R!1+^;^T+1!1#C^W2$p;R^T_2,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_4555555_K!6'_W_N!1'i11$e;R_N!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8^5!2'_4^7!2'_8_M-c>RN$x;R+c>+1^B3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1^G1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8^Q-c>RN$x;R+c>+1^S3$v0;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-^;RN$x;R!1+^;^T+1!2'dL^U!1#C#32$p;R^T-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4^Y!2'_8^X!3'd3^[!3,_T^\!4,d4+E+3!1#F#6,I_0_1,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_4555555_K!6'_W_O!1'd01$b;R_O!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8R_PV!3#:#8#7UWZ!2'_4!2'_4\!2'_8!3#:#8#7^0^2^3^4!2'_4^7!2'_8!2'_8!2'_8_?!3#:XYU^>-c>RN$x;R+c>+1^B3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1^G1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8!2'_8!2'_8^L!3#@#3#2^O^P_R,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_4555555_K!6'_W_S!1'hO1$b;R_S!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8!2'_8_U!2#:OQ_X2_4555555_K!6'_W_Z!1'bW1$l;R_Z!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8!2'_8_U_=_X2!4'h6#;#9_3_P555555_K!6'_W_[!2'i0/segs;1$b;R_[!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8!2'_8!2'_8_T!2'_4!2'_4\!2'_8_;!4#:S#8#7^1^3_=_X2_J555555_K!6'_W_\!2'cB/segs;1$l;R_\!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8!2'_8!2'_8_T_<_=!2'_4^7!2'_8_V-c>RN$x;R+c>+1!6#:XY^?,6^@^A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1^G1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8_W-c>RN$x;R+c>+1!6#@#3#2^R,6^@^A3$v0;R+E$scs;R^C$hints;R^D_Q$scs;R^C$hints;R^D,6,6,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_W`0!1'cG1$b;R`0!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8_8!4#:S#6#5N_9WZ_<_=!2'_4^7!2'_8_V-c>RN$x;R+c>+1_A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1^G1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8_W-c>RN$x;R+c>+1_D3$v0;R+E$scs;R^C$hints;R^D_Q$scs;R^C$hints;R^D,6,6,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_W`1!1'd81$b;R`1!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8`2!2'_4^7!2'_8_V-c>RN$x;R+c>+1_A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1^G1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8_W-c>RN$x;R+c>+1_D3$v0;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-^;RN$x;R!1+^;^T+1_E2$p;R^T-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4^Y!2'_8^X!2#F_F_1,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_W`3!1'eJ1$e;R`3!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8`2!2'_4^7!2'_8_V-c>RN$x;R+c>+1_A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1!1'_2!2'^P#3!2#=^F^91$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8_W_G,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_W`4!1'b31$b;R`4!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32A2$nhi;R+3-^;RN$x;R!1+^;+32E2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32M2$sphi;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8_:!6#:#6#5U#8#7U!6#:#6#5UXYU_<_=!2'_4^7!2'_8_V-c>RN$x;R+c>+1_A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1_B1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1^J2$ehi;R+3!2'_8!2'_8_C!6#@#<#;U#3#2^O_G,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_W`5!1'cQ1$o;R`5!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32!1#6@2$nhi;R+3-^;RN$x;R!1+^;+32!1#7D2$bhi;R+3-^;RN$x;R!1+^;+32I2$splo;R+3-^;RN$x;R!1+^;+32!1#9L2$sphi;R+3-1RN$~R+12!2'_8_>!2'_4^7!2'_8_V-c>RN$x;R+c>+1_A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1_B1$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1!1#?#52$ehi;R+3_H,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62_J555555_K!6'_W`5!1'cJ1$o;R`5!3+^N2-1RN$~R+12425-^;RN$x;R!1+^;+3262$ret;R+3-_>RN$x;R!2+_>+E+3281$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32<1$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32_52$nhi;R+3-^;RN$x;R!1+^;+32_62$bhi;R+3-^;RN$x;R!1+^;+32!1#8H2$splo;R+3-^;RN$x;R!1+^;+32_72$sphi;R+3-1RN$~R+12!2'_8_>!2'_4^7!2'_8!2'_8_@-^;RN$x;R!1+^;+3+1^;2$blo;R+3^=,6_I2_J555555_K!2,^H2`F!1'cH`G!1'cL1!1'cP`G!1'cR1!1'aZ`G!1'b41!1'eF`G!1'eK1!1'd3`G!1'd91!1'cF`G!1'hK1!2'c?/segs;`G!2'cC1/segs;!2'hZ/segs;`G!2'i2/segs;1!1'bV`G!1'bZ1!1'hN`G!1'i31!1'c\`G!1'eO1!1'h\`G!1'i41!1'dI`G!1'dN1!1'd:`G!1'd>1!3+^N2-1RN$~R+12`625-^;RN$x;R!1+^;+32`72$ret;R+3-_>RN$x;R!2+_>+E+32`81$bb;R+E$bk;R+3-_>RN$x;R!2+_>+E+32`91$qb;R+E$qk;R+3-^;RN$x;R!1+^;+32!2'cP!1'aB`:`;2$nhi;R+3-^;RN$x;R!1+^;+32!2'cP>`<2$bhi;R+3-^;RN$x;R!1+^;+32!2'cHC`=2$splo;R+3-^;RN$x;R!1+^;+32!2'cPGH2$sphi;R+3-1RN$~R+12!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8R!4'c\K#6#5U!5'cFKJ#6#5N!4'c\K#8#7U!7'aZK#6#5U#8#7U!7'aZK#6#5UXYU!2'_4!2'_4\!2'_8!4'c\K#8#7^0!6'hZ/segs;KJ#8#7^1`>!3'hNKOQ!2'_4^7!2'_8!2'_8!2'_8!2'_:^9!2'd:K`?!4'c\KXYU-^;RN$x;R!1+^;+3+1!2'cHK`?2$blo;R+3^=,6-c>RN$x;R+c>+1!8'c?/segs;KXY^?,6^@^A3$esb;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-_>RN$x;R!2+_>+E+3+1!1'_2!2'^P#3!3'eF!1'aB`@`A^91$hb;R+E$hk;R+3-^;RN$x;R!1+^;+3+1!2'cP!1'aB`B#52$ehi;R+3!2'_8!2'_8!2'_8^L!4'c\^I#3#2^O!7'aZ^I#<#;U#3#2^O-c>RN$x;R+c>+1!8'c?/segs;^I#3#2^R,6^@^A3$v0;R+E$scs;R^C$hints;R^D-2RN$scs;R!1+2+a@+1#22-^;RN$x;R!1+^;^T+1!2'dI`H!2'h\`H#32$p;R^T-_>RN$p;R!2+_>+3+3+1#11$lo;R+3$hi;R+3!2'_4^Y!2'_8^X!3'd3`I!3,_T^\!4,d4+E+3!2'h\`I#6,I_0`E,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,6,6$s;R+a@$l;R!1+2+a@,6$scs;R^C$hints;R^D,6,62!4'h6#:#9_3!4'bVK#6#5U555555`F!3+^N2!1'i5#1!1'i6#1").
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_sp8 : expr := eadd (eadd (escale 4096 (EVar V_S1)) (escale 512 (EVar V_S2A))) (escale 2 (EVar V_S2)).  (* [comment removed for export] *)
Definition e_atr8 : expr :=
  eadd e_sp8 (eadd (EVar V_ARGC) (eadd (EVar V_ENVC) (EVar V_W))).

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

Definition node_layout (cs : acs) (args : list expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S50!1+2+[!1+^;+C!1'i8'i9!1,^2+C!1,^L'i:$cs;R+C$args;R!1+2+E&k;R!1'^9#20-1RN$~R+11!1'@!3'_6+[!1'i72#123&k';R!3'_@+[$K;R+[!1'@!2'i72#1#10-2RN$args;R!1+2+E1#323$e;R+E$l;R!1+2+E-ERN$e;R+E1#28$z;R+3-3RN$z;R+31#13-2RN$l;R!1+2+E1#22-^;RN$x;R!1+^;+31!2'cQ#542$hi;R+3-1RN$~R+11!2'_:#1!1,^K,_02!2,^<+C!2'^7#8!3,_T+[!1'i8!1,H,I#533$e0;R+E$l0;R!1+2+E3$p;R+_I-_IRN$p;R+_I1#13$p0;R+_I3$p0;R+_I3-2RN$l;R!1+2+E1#32-^;RN$x;R!1+^;+31!2'cJ#642$lo;R+3-1RN$~R+11!2'_:!1,^K|10;#12!2,^<+C!2'^7#9!3,_T+[!1'i8'i;#633$e0;R+E$l0;R!1+2+E3$p;R+_I3$n;R+53$op;R+^?$a;R+E$b;R+E3$op;R+^?$a;R+E$b;R+E3$op;R+^@$a;R+E$b;R+E3$op;R+^@$a;R+E$b;R+E3$sx;R+1$lo;R+5$n;R+5$e0;R+E3$sx;R+1$k0;R+5$i;R+3$n;R+53").


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
   && list_eqb hop_eqb (a_hna cs) (a_hna ch) && list_eqb hop_eqb (a_hlz cs) (a_hlz ch)
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
Definition ksubst (J : nat) (e : expr) (K : kentry) : kentry := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S40!3'i<#6#5#3!3'i<#5#4#2!3'i=#5#4#1!3'i=#6#5#2$J;R+5$e;R+E$K;R+[-[RN$K;R+[+[#1:$a;R+^3$w;R+5$v;R+E!3,`Z0#2!3'i=#6#5#1$a;R+^3$n;R+E!2,`[12$a;R+^3$n;R+E$k;R+5!3,`\03#1$lo;R+3$hi;R+3#3$x;R+E$m;R+3!2,a2!3'i=#5#4#2#1$x;R+E$lo;R+3$hi;R+3!3,a3!3'i=#6#5#3#2#1$a;R+^3$n;R+E!2,a412$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!4,a5!3'i<#7#6#4!3'i=#7#6#3!3'i<#7#6#2!3'i=#7#6#1$a;R+^3$n;R+E$c;R+3!3,a603#1$a;R+^3$n;R+E!2,a712").
Definition psubst (J : nat) (e : expr) (p : expr * expr) : expr * expr := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$J;R+5$e;R+E$p;R!2+_>+E+E!4,d4+E+E!3'i=#3#2!3'`?+E+E#1!3'i=#3#2!3'`@+E+E#1").
Definition msubst (J : nat) (e : expr) (m : amap) : amap := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$J;R+5$e;R+E$m;R+:!3,g2!3'i=#3#2!1'`A#1!3'i=#3#2!1'`B#1!1'<#1").
Definition hsubst (J : nat) (e : expr) (h : hop) : hop := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S20!3'i=#5#4#2!3'i=#5#4#1$J;R+5$e;R+E$h;R+`>-`>RN$h;R+`>+`>#12$b;R+E$n;R+E!2,fY01$b;R+E$n;R+E!2,fX01").
Definition fsubst (J : nat) (e : expr) (f : afd) : afd := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$J;R+5$e;R+E$f;R+`=-`=RN$f;R+`=+`=#13#1$k;R+5$l;R+E$o;R+E!3,i>#3!3'i=#6#5#2!3'i=#6#5#1#1").
(* [comment removed for export] *)
Definition inst (inv : acs) (J : nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (map (ksubst J e) (kn inv)) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv) (map (hsubst J e) (a_hna inv)) (map (hsubst J e) (a_hlz inv)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint nt_set (t : list (option nat)) (i : nat) (d : nat) {struct i} : list (option nat) :=
  match i, t with
  | O, [] => [Some d]
  | O, _ :: rest => Some d :: rest
  | S j, [] => None :: nt_set [] j d
  | S j, x :: rest => x :: nt_set rest j d
  end.
Definition nt_get (t : list (option nat)) (i : nat) : option nat := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1+^;+5$t;R!1+20$i;R+5!4'D0#1#2!1,^2+5").
Lemma nt_get_set : forall t i d j, nt_get (nt_set t i d) j = if Nat.eqb j i then Some d else nt_get t j.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "ST0!1+^;+5!1+20!1,^2+5!2,^<+5#2!4'D0#1#32%t;R1%d;R+5%j;R+5!3+^N0!4'D0#1!3'i?#3#4#22-1RN$~R+10!2'7#1#4234!2,^<+5#3!4'D0#2#12!1,^00!2'7#1,^M!4'D0#182!2'7,^M,^M!4'D0,^M82!2,^H02!1$j;R+5=#1!1,_N#1!2'7?,^M!2,^<+5#4!4'D0?82!3,_T0#3#2!2,^<+5#7!4'D0#1C2!2,^<+5#6!3,_T0#2#1!4'D0,^MG2!3,_T0#4#3!2,^<+5#8!4'D0?I2!1,_N#6!1,_N#5!2'7#1#7!2,^<+5#5!1,_N#7!1,_N#:!1,_N#9!1,_N#;vd$t;R1$i;R+5!5'e2$i;R+55$t;R1$d;R+5$j;R+5-2RN$l;R!1+20!3+^N0!4'D0#2!3'i?#1,^M#32-1RN$~R+10!2'7#2,^M267#32-5RN$n;R+5!3+^N0!4'D0#1!3'i?8,^M#32-1RN$~R+10926:#12vd!2,^H03!3+^N0!4'D0,^M!3'i?8,^M#22-1RN$~R+10;23<$n;R+5!1$j;R+5vd-5RN$n;R+5!3+^N0-5RN$n;R+50#122$m;R+522#12=$n;R+5>!3+^N0!4'D0?!3'i?8,^M#42-1RN$~R+10@2AB#1$o;R0$l;R!1+20!2$x;R0$rest;R1-5RN$n;R+5!3+^N0!4'D0#1!3'i?C,^M#72-1RN$~R+1092DE#52vd!2,^H0F!3+^N0!4'D0,^M!3'i?G,^M#62-1RN$~R+10;2FH$n;R+5!1$j;R+5vd!2,^H04!3+^N0!4'D0?!3'i?I,^M#82-1RN$~R+10@2JK#1#2#1$i;R+5$IH;R5$t;R1$d;R+5$j;R+5-2RN$l;R!1+20!3+^N0!4'D0#2!3'i?#1L#32-1RN$~R+10!2'7#2L267#32-5RN$n;R+5!3+^N0!4'D0#1!3'i?8L#32-1RN$~R+10!2'7#1L26:#12vd=!3+^N0!4'D0,^M!3'i?8M#22-1RN$~R+10!2'7,^MM23<$n;R+5!1$j;R+5vd!6'_W0-1RN$~R+10N2A:$o;R0!3+^N0#1-1RN$~R+10!2'7#2#82O2&b;RN+1-1RN$b;R+1!3+^N0-1RN$~R+10#12F!4'D0#382-1RN$~R+10#12F2#12-5RN$n;R+5!3+^N0FF#22!2,^H0O$n;R+5!1$j;R+5!2,^H0D#1-5RN$n;R+5!3+^N0:2#22=$n;R+5>!4'D0#1!3'i?8#7#42!3#68#4#1!3+^N0!4'D0?!3'i?8P#42-1RN$~R+10!2'7?P2AB#1$o;R0$l;R!1+20!2$x;R0$rest;R1-5RN$n;R+5!3+^N0!4'D0#1!3'i?CQ#72-1RN$~R+10!2'7#1Q2DE#52vd!2,^H0#2!3+^N0!4'D0,^M!3'i?GR#62-1RN$~R+10!2'7,^MR2FH$n;R+5!1$j;R+5vd!3#:#3#8#1!3+^N0!4'D0?!3'i?IS#82-1RN$~R+10!2'7?S2JK#1#2#1#1#2%t;R1%i;R+5%d;R+5%j;R+5!3+^N0!2'i@!3'i?#4#3#2#1-1RN$~R+10!2'7#1#323!2'i@#4#1").
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
Definition arename (t : list (option nat)) (a : saddr) : saddr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2!1+^;+5$a;R+^3!2,`F!2'iA#2!1'_=#1!1'iB#1").
Definition krename (t : list (option nat)) (K : kentry) : kentry := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40!2'iC#5#3!2'iC#4#2!2'iA#4#1!2'iA#5#2$t;R!1+2!1+^;+5$K;R+[-[RN$K;R+[+[#1:$a;R+^3$w;R+5$v;R+E!3,`Z0#2!2'iA#5#1$a;R+^3$n;R+E!2,`[12$a;R+^3$n;R+E$k;R+5!3,`\03#1$lo;R+3$hi;R+3#3$x;R+E$m;R+3!2,a2!2'iA#4#2#1$x;R+E$lo;R+3$hi;R+3!3,a3!2'iA#5#3#2#1$a;R+^3$n;R+E!2,a412$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!4,a5!2'iC#6#4!2'iA#6#3!2'iC#6#2!2'iA#6#1$a;R+^3$n;R+E$c;R+3!3,a603#1$a;R+^3$n;R+E!2,a712").
Definition prename (t : list (option nat)) (p : expr * expr) : expr * expr := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2!1+^;+5$p;R!2+_>+E+E!4,d4+E+E!2'iA#2!3'`?+E+E#1!2'iA#2!3'`@+E+E#1").
Definition mrename (t : list (option nat)) (m : amap) : amap := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2!1+^;+5$m;R+:!3,g2!2'iA#2!1'`A#1!2'iA#2!1'`B#1!1'<#1").
Definition hrename (t : list (option nat)) (h : hop) : hop := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S20!2'iA#4#2!2'iA#4#1$t;R!1+2!1+^;+5$h;R+`>-`>RN$h;R+`>+`>#12$b;R+E$n;R+E!2,fY01$b;R+E$n;R+E!2,fX01").
Definition frename (t : list (option nat)) (f : afd) : afd := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2!1+^;+5$f;R+`=-`=RN$f;R+`=+`=#13#1$k;R+5$l;R+E$o;R+E!3,i>#3!2'iA#5#2!2'iA#5#1#1").

(* [comment removed for export] *)
Fixpoint evars_all (ok : nat -> bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => ok v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_all ok a && evars_all ok b
  | EExt _ _ _ a => evars_all ok a
  | EBlob _ _ _ _ => true
  end.
Definition kvars_all (ok : nat -> bool) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40!2'iD#5!1'_=#3!1'_=#2!2'_8!2'iD#41!2'iD#4#1!2'_80!2'iD#5#2$ok;R%~R+5+1$K;R+[-[RN$K;R+[+1#1:$a;R+^3$w;R+5$v;R+E!2'_80!2'iD#5#1$a;R+^3$n;R+E2$a;R+^3$n;R+E$k;R+53$lo;R+3$hi;R+3,9$x;R+E$m;R+3!2'iD#4#2$x;R+E$lo;R+3$hi;R+3!2'iD#5#3$a;R+^3$n;R+E2$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!2'_8!2'_8!2'_8!2'iD#6!1'_=#4!2'iD#6#3!2'iD#61!2'iD#6#1$a;R+^3$n;R+E$c;R+33$a;R+^3$n;R+E2").
Definition csvars_all (ok : nat -> bool) (cs : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2+_>+E+E$p;R0!2'_8!2'iD#3!3'`?+E+E#1!2'iD#3!3'`@+E+E#1$h;R+`>!2'_8!2'iD#3!1'a<#1!2'iD#3!1'a=#1$ok;R%~R+5+1$cs;R+C!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!3'?+E!1'iD#2!1'F!1'G#1!3'?+[!1'iE#2!1'^9#1!3'?+:$m;R+:!2'_8!2'iD#3!1'`A#1!2'iD#3!1'`B#1!1'O#1!3'?01!1'S#1!3'?01!1'T#1!2'iD#2!1'V#1-`=RN$x;R+`=+1!1'W#13,9$k;R+5$l;R+E$o;R+E!2'_8!2'iD#5#2!2'iD#5#1,9!3'?+`>2!1'Y#1!3'?+`>2!1'Z#1").

(* [comment removed for export] *)
Fixpoint emaxv (e : expr) (acc : nat) : nat :=
  match e with
  | ELit _ => acc
  | EVar v => Nat.max acc (S v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => emaxv a (emaxv b acc)
  | EExt _ _ _ a => emaxv a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kmaxv (K : kentry) (acc : nat) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S40!1'_=#3!1'_=#2!2'iF1!2'iF#1#3!2'iF0!2'iF#2#4$K;R+[$acc;R+5-[RN$K;R+[+5#2:$a;R+^3$w;R+5$v;R+E!2'iF0!2'iF#1#4$a;R+^3$n;R+E2$a;R+^3$n;R+E$k;R+53$lo;R+3$hi;R+3#3$x;R+E$m;R+3!2'iF#2#3$x;R+E$lo;R+3$hi;R+3!2'iF#3#4$a;R+^3$n;R+E2$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!2'iF!1'_=#4!2'iF#3!2'iF1!2'iF#1#5$a;R+^3$n;R+E$c;R+33$a;R+^3$n;R+E2").
Definition csmaxv (cs : acs) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S30!2+_>+E+E$p;R0$acc;R+5!2'iF!3'`?+E+E#2!2'iF!3'`@+E+E#2#1$h;R+`>$acc;R+5!2'iF!1'a<#2!2'iF!1'a=#2#1$cs;R+C&acc;R!5'`:+5+E'iF,^M!1'F!1'G#1+5&acc;R!5'`:+5+['iG#1!1'^9#2+5&acc;R!5'`:+5+:$m;R+:$acc;R+5!2'iF!1'`A#2!2'iF!1'`B#2#1#1!1'O#3+5&acc;R!5'`:+501#1!1'S#4+5&acc;R!5'`:+501#1!1'T#5+5&acc;R-`=RN$x;R+`=+5!1'W#63#1$k;R+5$l;R+E$o;R+E!2'iF#2!2'iF#1#4#1+5&acc;R!5'`:+5+`>2#1!1'Y#7+5&acc;R!5'`:+5+`>2#1!1'Z#8+5!2'iF!1'V#9#1").

Definition rename_cs (t : list (option nat)) (cs : acs) (nx : nat) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S30!2+_>+E+E!1'iJ#3!1'iL#3$t;R!1+2!1+^;+5$cs;R+C$nx;R+5!=,N!4'^5!1'd?#2!4'g6+E+E!1'iA#3!1'F!1'G#2!4'g6+[+[!1'iH#3!1'^9#2#1!4'g6+:+:!1'iI#3!1'O#2!1'P#2!1'Q#2!1'R#2!4'g6001!1'S#2!4'g6001!1'T#2!1'U#2!2'iA#3!1'V#2!2'iK#3!1'W#2!1'X#2!4'g6+`>+`>2!1'Y#2!4'g6+`>+`>2!1'Z#2").

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
Definition bt_get (t : list bool) (i : nat) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$t;R!1+2+1$i;R+5!4'D+1#1#2,6").
(* [comment removed for export] *)
Fixpoint evars_fo (gb : nat) (e : expr) (acc : list nat * list bool) : list nat * list bool :=
  match e with
  | ELit _ => acc
  | EVar v => if Nat.ltb v gb then acc else if bt_get (snd acc) v then acc else (v :: fst acc, bt_set (snd acc) v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_fo gb b (evars_fo gb a acc)
  | EExt _ _ _ a => evars_fo gb a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kvars_fo (gb : nat) (K : kentry) (acc : list nat * list bool) : list nat * list bool := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S50!2+_>!1+2+5!1+2+1!3'iM#6!1'_=#3#4!1'_=#2!3'iM#5#1!3'iM#52#3!3'iM#6#21$gb;R+5$K;R+[$acc;R0-[RN$K;R+[0#2:$a;R+^3$w;R+5$v;R+E!3'iM#6#11$a;R+^3$n;R+E3$a;R+^3$n;R+E$k;R+54$lo;R+3$hi;R+3#3$x;R+E$m;R+3!3'iM#5#2#3$x;R+E$lo;R+3$hi;R+3!3'iM#6#3#4$a;R+^3$n;R+E3$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E!3'iM#7#1!3'iM#72!3'iM#7#3!3'iM#7!1'_=#4#5$a;R+^3$n;R+E$c;R+34$a;R+^3$n;R+E3").
Definition csvars_fo (gb : nat) (cs : acs) : list nat := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S80!1+2+5!1+2+1!2+_>01!2+_>+E+E!3'`@+E+E#1!3'`?+E+E#1!1'a=#1!1'a<#1$gb;R+5$cs;R+C&acc;R!5'gO2+E$acc;R2$e;R+E!3'iM#4#1#2!1'F!1'G#1!4,d401!1,^0+5!1,^0+12&acc;R!5'gO2+[$acc;R2$K;R+[!3'iN#5#1#2!1'^9#2#12&acc;R!5'gO2+:$acc;R2$m;R+:!3'iM#6!1'`B#1!3'iM#6!1'`A#1#2!1'O#3#12&acc;R!5'gO23$acc;R2$p;R3!3'iM#74!3'iM#75#2!1'S#4#12&acc;R!5'gO23$acc;R2$p;R3!3'iM#84!3'iM#85#2!1'T#5#12&acc;R-`=RN$x;R+`=2!1'W#63#1$k;R+5$l;R+E$o;R+E!3'iM#:#1!3'iM#:#2#4#12&acc;R!3'iM#8!1'V#7#12&acc;R!5'gO2+`>$acc;R2$h;R+`>!3'iM#;6!3'iM#;7#2!1'Y#8#12&acc;R!5'gO2+`>$acc;R2$h;R+`>!3'iM#<6!3'iM#<7#2!1'Z#9#12!2'iO+5!3'`?01#1").
Fixpoint number_from (i : nat) (l : list nat) : list (nat * nat) :=
  match l with [] => [] | v :: rest => (v, i) :: number_from (S i) rest end.
Definition compact_map (gb : nat) (cs : acs) : list (nat * nat) := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$gb;R+5$cs;R+C!2'iP#2!2'iQ#2#1").
Definition node_compact (gb : nat) (cs : acs) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$gb;R+5$cs;R+C!3'iR#2#1!2'iS#2#1").

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

Definition kentry_eqb_h (x y : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2'iT#6#3!2'_8!2'iT#4#2!2'_9#3#1!2'_80!2'_9#5#2$x;R+[$y;R+[!2'_4!2'i7#2#1-[RN$x;R+[+1#2:$a;R+^3$w;R+5$v;R+E-[RN$y;R+[+1#4:$a';R+^3$w';R+5$v';R+E!2'_8!2'_80!2'7#5#2!2'_9#4#1$a0;R+^3$n;R+E,6$a0;R+^3$n;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n;R+E$c;R+3,6$a0;R+^3$n;R+E,6$a;R+^3$n;R+E-[RN$y;R+[+1#3:$a0;R+^3$w;R+5$v;R+E,6$a';R+^3$n';R+E1$a0;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n0;R+E$c;R+3,6$a0;R+^3$n0;R+E,6$a;R+^3$n;R+E$k;R+5-[RN$y;R+[+1#4:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n0;R+E,6$a';R+^3$n';R+E$k';R+5!2'_82!2'7#4#1$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n0;R+E$c;R+3,6$a0;R+^3$n0;R+E,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a;R+^3$n;R+E-[RN$y;R+[+1#3:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n0;R+E,6$a0;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a';R+^3$n';R+E1$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n0;R+E$c;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a;R+^3$n;R+E$c;R+3-[RN$y;R+[+1#4:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n0;R+E,6$a0;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a';R+^3$n';R+E$c';R+3!2'_82!2'aY#4#1$a0;R+^3$n0;R+E,6$a;R+^3$n;R+E-[RN$y;R+[+1#3:$a0;R+^3$w;R+5$v;R+E,6$a0;R+^3$n0;R+E,6$a0;R+^3$n0;R+E$k;R+5,6$lo;R+3$hi;R+3,6$e;R+E$m;R+3,6$e;R+E$lo;R+3$hi;R+3,6$a0;R+^3$n0;R+E,6$a1;R+^3$n1;R+E$a2;R+^3$n2;R+E,6$a0;R+^3$n0;R+E$c;R+3,6$a';R+^3$n';R+E1").
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
Definition kn_incl1_h (k : list kentry) (K : kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S00$k;R!1+2+[$K;R+[-1RN$~R+1+1!3'_6+[$X;R+[!2'i7#1#2#22,9-1RN$~R+1+1-1RN$~R+1+1!2'iU#2#12!3'_6+[$X;R+[!2'iV#1#2#2,62,9-1RN$~R+1+1!2'iW#2#12,9!2'iX#2#1").
Definition kn_incl_h (k : list kentry) (tk : list kentry) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1+2+[$k;R0$tk;R0!3'?+[!1'iY#2#1").

Definition entails_h (lo hi : nat) (cs : acs) (ch : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S:0!1'G#1!1'^9#1!1'O#1!1'S#1!1'T#1!1'V#1!1'W#1!1'Y#1!1'Z#1!2+_>+E+E$lo;R+5$hi;R+5$cs;R+C$ch;R+C!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'_8!2'aY!1'd?#2!1'd?#1-2RN$x;R!1+2+^1+1!1'aD02,9$s;R+^1$l;R!1+2+^1,6-^;RN$x;R!1+^;+^3+1!1'iZ02$s;R+^3,6,9!5'i[#4#3!1,^0+5!1'F!1'G#2!1'F0!2'i\!1'^9#21!2'j0#41!2'j1#42!2'j2#43!2'j2#44!2'a:#45!2'j3#46!2'j4#47!2'j4#48!4'j5+:'j6!1'O#22!4'j59'j7!1'S#23!4'j59'j7!1'T#24!2'_9!1'V#25!2'j8!1'W#26!2'j9!1'X#2!1'X#1!4'j5+`>'j:!1'Y#27!4'j5+`>'j:!1'Z#28!2'_:!1'P#2!1'P#1!2'_:!1'Q#1!1'Q#2!2'_:!1'R#2!1'R#1!2'_:!1'U#2!1'U#1").

(* [comment removed for export] *)
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat).
Definition lc_bnd (c : loopctx) : nat := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$c;R+j;-j;RN$c;R+j;+5#12$lc_head;R+3$lc_next;R+C$lc_lo;R+5$hi;R+5#1$jc_id;R+5$jc_st;R+C$jc_sh;R+j<$b;R+5$jc_lo;R+5#2").

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
Definition node_respell (cs : acs) (r : nat) (e : expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 3 "S00$cs;R+C$r;R+5$e;R+E-1RN$~R+1!1+^;+C!2'_8!2'_8!2'_8!2'_5,^M#2!2'_5#2}P!2'a:!1'e9#3#1!3'j=!1'^9#3!2'^B#3#2#12!2,^<+C!3'e=#3#2#1!1,^2+C").

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
Definition node_havocwords (cs : acs) (bs : list expr) : option acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S10!1'L#1$cs;R+C$bs;R!1+2+E-1RN$~R+1!1+^;+C!1'a?#22&ss;R!1'G#2+M!2,^<+C!2'^4#3!4'^5!1'K#1!1'F#1!3'j>!1'J#1#20!2'^:0!2'j?+E#2!1,^2+C").

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
Definition mk_itab_ranges (rs : list (Z * nat)) : itab := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$rs;R!1+2!2+_>+3+5!2'j@#1!1,`C+jA").

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BRK_ASLR : Z := 0x80000000.
Definition NX0 : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00};").   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition K_RND : nat := 25.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition auxw (i : Z) (ty : Z) (v : expr) : list kentry :=
  [KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty); KWord (SA (fst e_auxb) (snd e_auxb + 16 * i + 8)) 8 v].

(* [comment removed for export] *)
Definition init_kn_with (atr : kentry) (A : atable) : list kentry :=
  [KRange (EVar V_S1) 0xFFFF0000 0xFFFFFFFF; KRange (EVar V_S2) 0 255; KRange (EVar V_S2A) 0 7;   (* [comment removed for export] *)
   KRange (eaddz e_atrandom 16) 0x7fff800000c0 0x800000000000;
   KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE7;              (* [comment removed for export] *)
   KRange e_auxv (0x7fff80000000 + 24) (2^47 - 176);        (* [comment removed for export] *)
   KRange e_sp0 0x7fff80000000 0x7fffffffff40;
   KRange e_sp8 0xFFFF0000000 0xFFFFFFFFFE8;
   KRange e_sppg 0x7fff80000000 0x7ffffffff000;                                   (* [comment removed for export] *)
   KRange (eadd (escale 4096 (EVar V_S1)) (escale 512 (EVar V_S2A))) 0xFFFF0000000 0xFFFFFFFFE00;   (* [comment removed for export] *)
   KRange (EVar V_ARGC) 1 1024; KRange (EVar V_ENVC) 0 256; KRange (EVar V_L0) 0 131071; KRange (EVar V_L1) 0 131071;
   KRange (EVar V_UID) 0 0xFFFFFFFE; KRange (EVar V_HW) 0x112d 0x20112d;
   KRange (EVar V_W) 0 280000; KRange (EVar V_BRK) (img_hi A / 4096) ((img_hi A + BRK_ASLR) / 4096);
   KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_sp0 (-8388608)) (ELit 8388608);
   KWord (SA e_sp0 0) 8 (EVar V_ARGC); KWord (SA e_sp0 8) 8 e_str0; kw_argv1 e_argv1w]
  (* [comment removed for export] *)
  ++ auxw 0 3 (ELit (ph_addr_z A)) ++ auxw 1 4 (ELit (ph_ent_z A)) ++ auxw 2 5 (ELit (ph_num_z A)) ++ auxw 4 6 (ELit 4096)
  ++ auxw 3 16 (EVar V_HW)   (* [comment removed for export] *)
  ++ auxw 5 11 (EVar V_UID) ++ auxw 6 12 (EVar V_UID) ++ auxw 7 23 (ELit 0) ++ auxw 8 25 e_atrandom ++ auxw 9 0 (ELit 0)
  ++ [atr;
      KImg (img_lo A) (img_hi A); KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))].

(* [comment removed for export] *)
Definition atr_entry : kentry := KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND.
Definition atr_entry_zero : kentry := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2,`[!2,`F!3'`?+E+3'jB!3'`@+E+3'jB!1,H!1,^K|40;").
(* [comment removed for export] *)
Definition init_kn (A : atable) : list kentry := init_kn_with atr_entry A.
(* [comment removed for export] *)
Definition init_kn_zero (A : atable) : list kentry := init_kn_with atr_entry_zero A.

Definition init_regs : list expr := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10}2!3'^6!3'jC+E!1,H,I}P0'jD").
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition init_vis (A : atable) : list (expr * expr) :=
  [(ELit (img_lo A), ELit (img_hi A - img_lo A)); (e_top, e_stk_len)].

Definition init_acs_of_with (kn0 : list kentry) (A : atable) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 2 "S30!2'a\!1'cX#1!1'cW#1|10;!1,^0+jR$kn0;R!1+2+[$A;R+jE!=,jF!4'jG!1'jH#1'jI#2'jJ!1,^0+jK0'jL,I!1'jM#1!1,^0!2+_>+E+E!2'^U!1'jN0!1'jN!2'a\!2'^V!1,^K1!1,^K|50f;'gY!2'jO!1,^K|<000;!1,^L'jP,jQ,622").
Definition init_acs_of (A : atable) : acs := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S00$A;R+jE!2'jS!1'jT#1#1").        (* [comment removed for export] *)
Definition init_acs_of_zero (A : atable) : acs := init_acs_of_with (init_kn_zero A) A.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ASAN : atable :=
  {| img_lo := 0x10000; img_hi := 0x68f000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x56174; rw_lo := 0x148000; rw_len := 0x547000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x90b0c; x_imemcpy := 0x90a90; x_memset := 0x1413ac; x_memcpy := 0x140fa8; x_memiszero := 0x91058;
     x_istrncpy := 0x90f38; x_sealed := 0x11e39; x_popfree := 0x5c824;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x12f068; x_envscan_k := 0x12f074; x_pnscan := 0x12f12c; x_pnscan_k := 0x12f138;
     stops_more := [0x5a498; 0x5babc; 0x80688; 0x871d0; 0x871e4; 0x871f8; 0x8cb88; 0x8cc58; 0x9a198; 0x9b0a4; 0x9b234; 0xa4e50] |}.

(* [comment removed for export] *)
Definition ASAN_TEXT_LO : Z := 0x56174.
Definition ASAN_TEXT_N : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'jU!1,jV!1,jW!1,jX!1,jY!1,jY!1,jZ!1,jW,j[").
Definition asan_init : acs := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'j\'k0").

(* [comment removed for export] *)
Definition BOTH : atable :=
  {| img_lo := 0x10000; img_hi := 0x694000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x56d20; rw_lo := 0x14e000; rw_len := 0x546000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x916b8; x_imemcpy := 0x9163c; x_memset := 0x1463d0; x_memcpy := 0x145fcc; x_memiszero := 0x91c04;
     x_istrncpy := 0x91ae4; x_sealed := 0x11e49; x_popfree := 0x5d3d0;
     x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x13408c; x_envscan_k := 0x134098; x_pnscan := 0x134150; x_pnscan_k := 0x13415c;
     stops_more := [0x5b044; 0x5c668; 0x81234; 0x87d7c; 0x87d90; 0x87da4; 0x8d734; 0x8d804; 0x9ad44; 0x9bc50; 0x9bde0; 0xa59fc] |}.
Definition BOTH_TEXT_LO : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1,^K|B16d20;").
Definition BOTH_TEXT_N : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'jU!1,jV!1,jW!1,k1!1,jW!1,k2!1,k3!1,jX,j[").
Definition both_init : acs := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'j\'k4").

End APCK.
