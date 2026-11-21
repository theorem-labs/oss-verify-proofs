(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Pm6StdioWrite.v: the whole file restated over the budget carrier rzb, its Rpl name table repointed at the twins. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact): changed loop1_b, loop2_b, ref_stdio_write_b; added Hrdr; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/BudgetWit/Pm10StdioWriteB.v, 399 lines within its lines 62-679. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes LibWritev LibWritevX Frame RefMemcpyLib
  Pm6StdioDefs Pm6StdioWrite_run1 Pm6StdioWrite_run2 Pm6_code_af000_b0000 .
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.BudgetWit Require Import SpinAlgB LibWritevXB.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@LinuxProcessSemantics; @LinuxProcessSem; @Run; @config]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @TSet]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @SpinAlgB; @rzb]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Plain; @M; @loaded_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @SpinAlgB; @rzb_conseq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_emit]; [@Corelib; @Init; @Datatypes; @nil]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_emit_nil_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @SpinAlgB; @rzb_nonempty]; [@Stdlib; @Lists; @List; @skipn_app]; [@Corelib; @Init; @Datatypes; @app]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Lists; @ListDef; @skipn]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Peano; @le]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@Corelib; @Init; @Nat; @sub]; [@Corelib; @Init; @Logic; @eq]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Corelib; @Init; @Datatypes; @O]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @Arith; @PeanoNat; @Nat; @sub]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_sub_max]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Corelib; @Init; @Datatypes; @cons]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Corelib; @Numbers; @BinNums; @xH]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Corelib; @Init; @Datatypes; @None]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @eq_ind]; [@Stdlib; @Lists; @List; @skipn_all_iff]; [@Corelib; @Init; @Logic; @proj1]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @u64_range]; [@Stdlib; @ZArith; @BinInt; @Z; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Corelib; @Init; @Logic; @not]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Init; @Logic; @or_intror]; [@Corelib; @Init; @Logic; @conj]; [@Corelib; @Init; @Logic; @or_introl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StepTac; @u_Z2bv]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@Corelib; @Init; @Logic; @False]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Hoare; @at_]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @RI]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@stdpp; @bitvector; @definitions; @BV]; [@Corelib; @Init; @Logic; @I]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @sw_regs_but]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @LM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@Corelib; @Init; @Datatypes; @Some]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn_ext]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @store_ok_mono]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatExec; @wbytes]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Frame; @wbytes_outside]; [@Stdlib; @micromega; @ZifyClasses; @not_morph]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatExec; @length_N_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Frame; @in_rng]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @wbytes_grows]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @sw_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @LM_rdn]; [@Stdlib; @micromega; @ZifyClasses; @or_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@stdpp; @bitvector; @definitions; @BvWf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @mem_sw2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @SpinAlgB; @rzb_msteps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @rz_emit_nil_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @finish_b]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_addi]; [@Corelib; @Init; @Datatypes; @nat_ind]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Lists; @ListDef; @map]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @WriteEv]; [@Corelib; @Init; @Logic; @False_ind]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Corelib; @Init; @Datatypes; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @sw_retry_a]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_succ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @LM_store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @LM_wbytes8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @RI_but]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @LibWritevXB; @rz_writev1_wallX_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6_code_af000_b0000; @W_af2a0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6_code_af000_b0000; @F_af2a0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6_code_af000_b0000; @E_af2a0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SeqExec; @rdn_wbytes_hit8]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatExec; @rdn_wbytes_out]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @RefMemcpyLib; @rdn_skipn]; [@LinuxProcessSemantics; @LinuxProcessSem; @BvBase; @word_to_nat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibWritev; @word_to_nat_Z]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @TASK_SIZE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @regupd]; [@Stdlib; @Lists; @List; @length_skipn]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eq_dec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @sw_c2_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @WalkTac; @wf_getr_chain]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Init; @Datatypes; @false]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @finish_nil_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @sw_c2_ne]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @pc_af254]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @le_gt_cases]; [@Corelib; @Init; @Logic; @or_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @LibWritevXB; @rz_writev2_wallX_b]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @id]; [@Stdlib; @Lists; @List; @length_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @u_at_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @skipn_app_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @sw_retry_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @Loop; @loop1_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_1; @skipn_app_ge]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @LM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run1; @mem_sw1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioDefs; @sw_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioDefs; @Build_sw_post]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @v_add]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioDefs; @sw_file]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioDefs; @ssp_cells]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdEntry]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_lookup]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fds]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdChannel]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_halted]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_lazy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Hoare; @ret_ok]; [@Corelib; @Init; @Logic; @eq_sym]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibWritev; @u64_roundtrip']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_2; @sw_post_of_LM]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @finish_nil_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @RI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @loop1_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @loop2_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @LM_refl]; [@Corelib; @Numbers; @BinNums; @positive]; [@Corelib; @Numbers; @BinNums; @xO]; [@Corelib; @Numbers; @BinNums; @xI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run1; @sw_enter_eq]; [@Stdlib; @ZArith; @BinInt; @Z; @sub_diag]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @LibWritevXB; @rz_writev1_zeroX_b]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6_code_af000_b0000; @W_af218]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6_code_af000_b0000; @F_af218]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6_code_af000_b0000; @E_af218]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @sw_c1_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @RI_but]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @BudgetWit; @Pm6StdioWriteB; @FPX_2; @pc_af1cc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run2; @sw_c1_ne]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm6StdioWrite_run1; @sw_enter]].

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.


(* [comment removed for export] *)
Lemma rz_emit_nil_b : forall c K, SpinAlgB.rzb RSEGS scfg c K -> SpinAlgB.rzb RSEGS scfg c (t_emit [] K).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S10!2'5!1,6+7#2$c;R+0$K;R'1$H;R!4+2'3/scfg;#2#1!7,4'3/scfg;#3#20#1!3'80#2!2'9#2!5':'3/scfg;#3#2#1").
Qed.

Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SI5lcd;g;d;lcd;g<d;lcd;g=d;lcd;g>d;<scd;!1+@#5!2'=#5#3!2'C#41!1+@#6!3'<#6!3'>#6#5#4#3!3+D+?,F2!1'K#4!1'K1!2'I,H!2'J67!2,O+G6!2,O+G7!2'T67!2'=#7#5!2'J!1'K#7!1'K!2'=#8#6!2'I,H=!1+^<+G!2,^D+G,H!2,^G+G|10;!2,^G+G|11;!2,^G+G,^5!1,^K+^>!1'K#:!1'K!2'=#;#9!2'JEF!3'>#7#6#5$A;R{cd;$k;R+?$l1;R!1+@#2$l2;R!1+@#3$Hk;R!2+A#3!2'=#4#2!6'B0!3'<#5!3'>#5#4#3!3'>#52#2$l;R0!3+D3#14&H;R!4'E5!3+D+G,H8!<'L+?+G!1+D+?'K!1+D+G$x;R+?$y;R+?!3'M!3+D+G!1'K#2!1'K#1!3+D+?#2#1!2'N#2#1,F,H!2,O+G,H28!B'P+?+?+?+G+G+G'Q'K'K'K$n;R+G$m;R+G!2'I,H!2'J#2#1'R#46917:&Hk0;R!4'S!2+A#41;!<'L+?+G+A'K'T'U#46917:#1;&cstr;R!1'V#5!2'T,H!1'K#5&cstr0;R!1'V<!2'T,H!1'K<&H3;R!2'W,H=!2+X!2+Y!2'Z,H=!3+D+G>=!2+Y!2'T=,H!3+D+G>,H&z3;R!2'I,H!2'J!1'K#8!1'K!2'=#9#7+G&__arith;R$__p2;Rw$__p1;Rw$__x3;R+G$__x2;R+G$__x1;R+G&__wit;R!3,[+\!2,^0!3,^1+G!3,^2+G!2,^3+G!1,^4,^5!2,^6+G}2!2,^6+G,F,^7!1,6+\!1+@+\&__varmap;R!4,^8+G!2,^9+G#3#2!2,^9+G#4!1+^:+G&__ff;R!8,^;?'^=+^>+^>,^?!7,^@?'^=+^>+^>,^?!7,^A?'^=+^>+^>,^?!7,^B?'^=+^>+^>,^?!4,^C+G@,^E!3,^F+GAB,^H!6,^I?'^=+^>+^>,^?#6!7,^A?'^=+^>+^>,^?!6,^I?'^=+^>+^>,^?#7!7,^B?'^=+^>+^>,^?!4,^C+GC,^J@,^HD!8,^;?'^=+^>+^>,^?!7,^B?'^=+^>+^>,^?!4,^C+GA,^LB,^HD!7,^B?'^=+^>+^>,^?!4,^C+G@,^JC,^H!2'^M?,^?!4'^N#1#3vv!2,O+^O,^P!3+D+^O!2'^Q#1#3,^P!3'^R+G,H#2%__p2;Rw%__p1;Rw%__x3;R+G%__x2;R+G%__x1;R+G%~R!2+X!2+Y!2'Z,H!2'J#2#3#4!2+Y#5!3+D+G#1,H%~R!2'T#3#4!3+D+G,H#3!7#1!2'TG,H!3+D+G#2GFE#2#3#65!6'^S+?,F$n;R+?!3+D!1+@#7!3'<#7H!3'>#7#1#4!3'<#7H#4!2,O34!2'C#5!2'=#6#4#1!3'>#5#4!3'<#5#3#2!4';#5#4#3#2").
Qed.

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S86lcd;g^Td;lcd;g<d;lcd;g=d;lcd;gBd;lcd;g>d;<scd;!1+@#5!3'>#5#4#3!2'=#5#3!3'>#5!2'C#42#2!1+@#6!2'=#6#4!3'>#6!2'C#55#3!1,6#5$A;R{cd;$k;R+?$l1;R!1+@#2$l2;R!1+@#3$Hk;R!2+A!2'=#4#2#3!6'B0!3'<#513$l;R0!3+D4#16!6'B07$l;R0!3+D4!3'<#6#166!2,O031!4'^U%~R!2+A2#4!3+D4!3'>#6#5#4!1,6#6%~R!3+D017!2+A5#5!3'^T#5#4#3#1!3'>#5#4!3'<#5#3#2!4';#5#4#3#2").
Qed.

(* [comment removed for export] *)
Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
  bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
  \/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S\0|600;!1,^W0|10;!1,^[2!1,^[0!2'^Z34!2'^Y1#4!2'^X!2'^Y1#5#4!3+D+G75!3+D+G!2'^X!2'^Y1#6#55!1'_29!2'^X!2'^Y1#7#6!2'^Y1!2'_31;!3+D+G;5!2'^X!2'^Y1#8#7!2'^Y1!2'_31>!3+D+G?>!3+D+G?,H!3+D+G>5!2+YAB!2'_834%~R!2'Z,H3%~R!2'T,H4!2'Z,H5!2'T,H3$Ha;RF$~R+_9!3'_:34#2%Ha;RF%~R+_9!2'T,H5}1!1,6+\!1+@+\!4,^8+G!2,^9+G#3#2!1,_;+G!1+^:+G!1+^<+G!2,^G+G,^5!2,^G+G2!3,_=+GOP!3,_>+G!2,^D+G31!6,_<N'^=+^>+^>,^?!7,^BN'^=+^>+^>,^?!4,^C+GQ,^JR,^H!1,^K+^>!2,^D+G,H!2'^MN,^?!4'^N#1#3vv!2,O+^O,^P!3+D+^O!2'^Q#1#3,^P!3'^R+G,H#2%~R!3+D+G!2'^X#1#25+_?!2'^Y1#;!2'^Y1!2'_@#4#3!2'^X6#3$b;R!1+^V1$k;R+G$Hk;R!2'T,H#1$Hle;R!2'T!2'^X!2'^Y1#3#25vd&H;R!1'^\#4!2+Y!2'T,H6!2'Z65&s;R!2'_075!2+_18!1'_28-_1RN$s;R!2+_19:!2+X!3+D+G<;!2+Y!3+D+G<,H=#12$e;R9!1$E;R=!3,_4@C!4,_5AB!6'B+G5$z;R+G!3+D+G!2'^Y1!2'_31#1,Hvv!2,O+G,H!3+D+G!2'^Y1!2'_315,H>#1#1#1$n;R:!1$NE;R!1'_2=!3,_6@C!6'B+G>$z;R+G!3+D+G#1!2'^X!2'^Y1#9#8!2,O+G>?!3'_7>&__sat1;RDE&__sat0;RGH&__arith;R$__p1;Rw$__x2;R+G$__x1;R+G&__wit;R!3,[+\!2,^0!3,^1+G!2,^6+G}2!3,^1+G!2,^6+GI!2,^6+G,F,^7JK&__varmap;RLM&__ff;R!8,^;N'^=+^>+^>,^?ST!8,^;N'^=+^>+^>,^?!7,^AN'^=+^>+^>,^?!7,^BN'^=+^>+^>,^?!4,^C+GU,^LO,^H!6,^IN'^=+^>+^>,^?#5T!8,^;N'^=+^>+^>,^?!7,^BN'^=+^>+^>,^?!4,^C+GU,^LP,^HT!7,^BN'^=+^>+^>,^?!4,^C+GU,^LQ,^HVW%__p1;Rw%__x2;R+G%__x1;R+G%~RX%~R!2+Y!2'T,H#2#4%~R!2'T,H#4!2'T,H!2'^X#4#5!6#1!2'ZY5#:Y#4#7#9&__sat1;RDE&__sat0;RGH&__arith;R$__x2;R+G$__x1;R+G&__wit;RJK&__varmap;RLM&__ff;R!8,^;N'^=+^>+^>,^?ST!8,^;N'^=+^>+^>,^?!7,^BN'^=+^>+^>,^?!4,^C+GQ,^LR,^HT!7,^BN'^=+^>+^>,^?!4,^C+GQ,^ER,^HVW%__x2;R+G%__x1;R+G%~RX%~R!2'T!2'^X#2#35!2'Z!2'^X#3#45!4#1#:Y#4#8#1!2+X!3+D+GZ[!2+Y!3+D+GZ,H!3+D+G[5").
Qed.

Section Loop.
  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : word -> option byte.
  Variable model : Model.
  Variable K : TSet.

  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis Flo : (0xc7000 <= f)%Z.
  Hypothesis Fhi : (f + 232 <= 0xf9890)%Z.
  Hypothesis FD : (0 < fd < 2147483648)%Z.
  Hypothesis Hfd : fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Hypothesis Hrdr : m_channel_reader model = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hret : ret_ok ret.
  Hypothesis HKnil : K [].
  Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
  Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
  Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
  Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
  Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
  Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
  Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
  Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
  Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
  Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xf9890) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
  Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
  Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

  (* [comment removed for export] *)
  Definition LM (m : word -> option byte) : Prop :=
    (forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

  (* [comment removed for export] *)
  Hypothesis HK : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = e8 -> getr regs' 9 = e9 ->
     getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
     getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
     getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
     getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
     LM m ->
     SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K.

  (* [comment removed for export] *)
  Definition RI (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
    /\ getr regs 21 = Z_to_bv 64 0xf9890 /\ getr regs 3 = g3 /\ getr regs 4 = g4
    /\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
    /\ getr regs 26 = g26 /\ getr regs 27 = g27.

  Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S`30|21;!1,^W0!1,^W|600;!1+^V2!2'_A13|10;!3,_E1!1,^[5,_F!2'_32!2'J/su;!1,^[|630;!3+D3!2'_D#367|30;!3,_E1!1,^[9,_F!3,_E1!1,^[|31;,_F!2'_32/f;!3,_E1!1,^[|45;,_F!2'_32!1,^[|C79890;|11;!3,_E1!1,^[?,_F|20;!3,_E1!1,^[A,_F!3,_E1!1,^[|47;,_F!3,_E1!1,^[|48;,_F!3,_E1!1,^[|49;,_F!3,_E1!1,^[|4a;,_F|4b;!3,_E1!1,^[G,_F!3+D3!2'_D#7:/l;!3+D3!2'_D#;;<!3+D3!2'_D#?=>!3+D3!2'_D#C@/g3;!3+D3!2'_D#GB/g4;!3+D3!2'_D#KC/g23;!3+D3!2'_D#OD/g24;!3+D3!2'_D#SE/g25;!3+D3!2'_D#WF/g26;!3+D3!2'_D#[6!2'_D#\6!2'_D#^2:!2'_D#^2;!2'_D#^2=!2'_D#^2@!2'_D#^2B!2'_D#^2C!2'_D#^2D!2'_D#^2E!2'_D#^2F!2'_D#^2H!3+D3S!2'_D#^3:!2'_D#^6;!2'_D#^6=!2'_D#^6@!2'_D#^6B!2'_D#^6C!2'_D#^6D!2'_D#^6E!2'_D#^6F!2'_D#^6H!3+D3^1!2'_D#^7;!2'_D#^:=!2'_D#^:@!2'_D#^:B!2'_D#^:C!2'_D#^:D!2'_D#^:E!2'_D#^:F!2'_D#^:H!3+D3^;!2'_D#^;=!2'_D#^>@!2'_D#^>B!2'_D#^>C!2'_D#^>D!2'_D#^>E!2'_D#^>F!2'_D#^>H!3+D3^D!2'_D#^?@!2'_D#^BB!2'_D#^BC!2'_D#^BD!2'_D#^BE!2'_D#^BF!2'_D#^BH!3+D3^L!2'_D#^CB!2'_D#^FC!2'_D#^FD!2'_D#^FE!2'_D#^FF!2'_D#^FH!3+D3^S!2'_D#^GC!2'_D#^JD!2'_D#^JE!2'_D#^JF!2'_D#^JH!3+D3^Y!2'_D#^KD!2'_D#^NE!2'_D#^NF!2'_D#^NH!3+D3_1!2'_D#^OE!2'_D#^RF!2'_D#^RH!3+D3_5!2'_D#^SF!2'_D#^VH!2'_D#^W6!2'_D#^W:!3+D3_:/l;!2'_D#^W;!3+D3_<<!2'_D#^W=!3+D3_>>!2'_D#^W@!3+D3_@/g3;!2'_D#^WB!3+D3_B/g4;!2'_D#^WC!3+D3_D/g23;!2'_D#^WD!3+D3_F/g24;!2'_D#^WE!3+D3_H/g25;!2'_D#^WF!3+D3_J/g26;!2'_D#^WH!3+D3_L/g27;!2+Y_K_M!2+Y_I_N!2+Y_G_O!2+Y_E_P!2+Y_C_Q!2+Y_A_R!2+Y_?_S!2+Y_=_T!2+Y_;_U!3+D3!2'_D#^X67!3+D3!2'_D#^X:/l;!3+D3!2'_D#^X;<!3+D3!2'_D#^X=>!3+D3!2'_D#^X@/g3;!3+D3!2'_D#^XB/g4;!3+D3!2'_D#^XC/g23;!3+D3!2'_D#^XD/g24;!3+D3!2'_D#^XE/g25;$regs;R4$regs';R4$H;R!1'_B#2!5'_C8!2+Y!3+D3!2'_D#3:/l;!2+Y!3+D3!2'_D#3;<!2+Y!3+D3!2'_D#3=>!2+Y!3+D3!2'_D#3@/g3;!2+Y!3+D3!2'_D#3B/g4;!2+Y!3+D3!2'_D#3C/g23;!2+Y!3+D3!2'_D#3D/g24;!2+Y!3+D3!2'_D#3E/g25;!2+Y!3+D3!2'_D#3F/g26;!3+D3!2'_D#3H/g27;%~R!2'_G#3#2!1'_B#3$~R8$~R!2+Y!3+D3!2'_D#4:/l;!2+Y!3+D3!2'_D#4;<!2+Y!3+D3!2'_D#4=>!2+Y!3+D3!2'_D#4@/g3;!2+Y!3+D3!2'_D#4B/g4;!2+Y!3+D3!2'_D#4C/g23;!2+Y!3+D3!2'_D#4D/g24;!2+Y!3+D3!2'_D#4E/g25;!2+Y!3+D3!2'_D#4F/g26;!3+D3!2'_D#4H/g27;!2$R2;R!3+D3!2'_D#567$H;R!2+Y!3+D3!2'_D#6:/l;!2+Y!3+D3!2'_D#6;<!2+Y!3+D3!2'_D#6=>!2+Y!3+D3!2'_D#6@/g3;!2+Y!3+D3!2'_D#6B/g4;!2+Y!3+D3!2'_D#6C/g23;!2+Y!3+D3!2'_D#6D/g24;!2+Y!3+D3!2'_D#6E/g25;!2+Y!3+D3!2'_D#6F/g26;!3+D3!2'_D#6H/g27;!5'_CI!2+Y!3+D3!2'_D#7;<!2+Y!3+D3!2'_D#7=>!2+Y!3+D3!2'_D#7@/g3;!2+Y!3+D3!2'_D#7B/g4;!2+Y!3+D3!2'_D#7C/g23;!2+Y!3+D3!2'_D#7D/g24;!2+Y!3+D3!2'_D#7E/g25;!2+Y!3+D3!2'_D#7F/g26;!3+D3!2'_D#7H/g27;%~R!2'_G#7#6!1'_B#7$~RI$~R!2+Y!3+D3!2'_D#8;<!2+Y!3+D3!2'_D#8=>!2+Y!3+D3!2'_D#8@/g3;!2+Y!3+D3!2'_D#8B/g4;!2+Y!3+D3!2'_D#8C/g23;!2+Y!3+D3!2'_D#8D/g24;!2+Y!3+D3!2'_D#8E/g25;!2+Y!3+D3!2'_D#8F/g26;!3+D3!2'_D#8H/g27;!2$R8;R!3+D3!2'_D#9:/l;$H;R!2+Y!3+D3!2'_D#:;<!2+Y!3+D3!2'_D#:=>!2+Y!3+D3!2'_D#:@/g3;!2+Y!3+D3!2'_D#:B/g4;!2+Y!3+D3!2'_D#:C/g23;!2+Y!3+D3!2'_D#:D/g24;!2+Y!3+D3!2'_D#:E/g25;!2+Y!3+D3!2'_D#:F/g26;!3+D3!2'_D#:H/g27;!5'_CJ!2+Y!3+D3!2'_D#;=>!2+Y!3+D3!2'_D#;@/g3;!2+Y!3+D3!2'_D#;B/g4;!2+Y!3+D3!2'_D#;C/g23;!2+Y!3+D3!2'_D#;D/g24;!2+Y!3+D3!2'_D#;E/g25;!2+Y!3+D3!2'_D#;F/g26;!3+D3!2'_D#;H/g27;%~R!2'_G#;#:!1'_B#;$~RJ$~R!2+Y!3+D3!2'_D#<=>!2+Y!3+D3!2'_D#<@/g3;!2+Y!3+D3!2'_D#<B/g4;!2+Y!3+D3!2'_D#<C/g23;!2+Y!3+D3!2'_D#<D/g24;!2+Y!3+D3!2'_D#<E/g25;!2+Y!3+D3!2'_D#<F/g26;!3+D3!2'_D#<H/g27;!2$R9;R!3+D3!2'_D#=;<$H;R!2+Y!3+D3!2'_D#>=>!2+Y!3+D3!2'_D#>@/g3;!2+Y!3+D3!2'_D#>B/g4;!2+Y!3+D3!2'_D#>C/g23;!2+Y!3+D3!2'_D#>D/g24;!2+Y!3+D3!2'_D#>E/g25;!2+Y!3+D3!2'_D#>F/g26;!3+D3!2'_D#>H/g27;!5'_CK!2+Y!3+D3!2'_D#?@/g3;!2+Y!3+D3!2'_D#?B/g4;!2+Y!3+D3!2'_D#?C/g23;!2+Y!3+D3!2'_D#?D/g24;!2+Y!3+D3!2'_D#?E/g25;!2+Y!3+D3!2'_D#?F/g26;!3+D3!2'_D#?H/g27;%~R!2'_G#?#>!1'_B#?$~RK$~R!2+Y!3+D3!2'_D#@@/g3;!2+Y!3+D3!2'_D#@B/g4;!2+Y!3+D3!2'_D#@C/g23;!2+Y!3+D3!2'_D#@D/g24;!2+Y!3+D3!2'_D#@E/g25;!2+Y!3+D3!2'_D#@F/g26;!3+D3!2'_D#@H/g27;!2$R21;R!3+D3!2'_D#A=>$H;R!2+Y!3+D3!2'_D#B@/g3;!2+Y!3+D3!2'_D#BB/g4;!2+Y!3+D3!2'_D#BC/g23;!2+Y!3+D3!2'_D#BD/g24;!2+Y!3+D3!2'_D#BE/g25;!2+Y!3+D3!2'_D#BF/g26;!3+D3!2'_D#BH/g27;!5'_CL!2+Y!3+D3!2'_D#CB/g4;!2+Y!3+D3!2'_D#CC/g23;!2+Y!3+D3!2'_D#CD/g24;!2+Y!3+D3!2'_D#CE/g25;!2+Y!3+D3!2'_D#CF/g26;!3+D3!2'_D#CH/g27;%~R!2'_G#C#B!1'_B#C$~RL$~R!2+Y!3+D3!2'_D#DB/g4;!2+Y!3+D3!2'_D#DC/g23;!2+Y!3+D3!2'_D#DD/g24;!2+Y!3+D3!2'_D#DE/g25;!2+Y!3+D3!2'_D#DF/g26;!3+D3!2'_D#DH/g27;!2$R3;R!3+D3!2'_D#E@/g3;$H;R!2+Y!3+D3!2'_D#FB/g4;!2+Y!3+D3!2'_D#FC/g23;!2+Y!3+D3!2'_D#FD/g24;!2+Y!3+D3!2'_D#FE/g25;!2+Y!3+D3!2'_D#FF/g26;!3+D3!2'_D#FH/g27;!5'_CM!2+Y!3+D3!2'_D#GC/g23;!2+Y!3+D3!2'_D#GD/g24;!2+Y!3+D3!2'_D#GE/g25;!2+Y!3+D3!2'_D#GF/g26;!3+D3!2'_D#GH/g27;%~R!2'_G#G#F!1'_B#G$~RM$~R!2+Y!3+D3!2'_D#HC/g23;!2+Y!3+D3!2'_D#HD/g24;!2+Y!3+D3!2'_D#HE/g25;!2+Y!3+D3!2'_D#HF/g26;!3+D3!2'_D#HH/g27;!2$R4;R!3+D3!2'_D#IB/g4;$H;R!2+Y!3+D3!2'_D#JC/g23;!2+Y!3+D3!2'_D#JD/g24;!2+Y!3+D3!2'_D#JE/g25;!2+Y!3+D3!2'_D#JF/g26;!3+D3!2'_D#JH/g27;!5'_CN!2+Y!3+D3!2'_D#KD/g24;!2+Y!3+D3!2'_D#KE/g25;!2+Y!3+D3!2'_D#KF/g26;!3+D3!2'_D#KH/g27;%~R!2'_G#K#J!1'_B#K$~RN$~R!2+Y!3+D3!2'_D#LD/g24;!2+Y!3+D3!2'_D#LE/g25;!2+Y!3+D3!2'_D#LF/g26;!3+D3!2'_D#LH/g27;!2$R23;R!3+D3!2'_D#MC/g23;$H;R!2+Y!3+D3!2'_D#ND/g24;!2+Y!3+D3!2'_D#NE/g25;!2+Y!3+D3!2'_D#NF/g26;!3+D3!2'_D#NH/g27;!5'_CO!2+Y!3+D3!2'_D#OE/g25;!2+Y!3+D3!2'_D#OF/g26;!3+D3!2'_D#OH/g27;%~R!2'_G#O#N!1'_B#O$~RO$~R!2+Y!3+D3!2'_D#PE/g25;!2+Y!3+D3!2'_D#PF/g26;!3+D3!2'_D#PH/g27;!2$R24;R!3+D3!2'_D#QD/g24;$H;R!2+Y!3+D3!2'_D#RE/g25;!2+Y!3+D3!2'_D#RF/g26;!3+D3!2'_D#RH/g27;!5'_CP!2+Y!3+D3!2'_D#SF/g26;!3+D3!2'_D#SH/g27;%~R!2'_G#S#R!1'_B#S$~RP$~R!2+Y!3+D3!2'_D#TF/g26;!3+D3!2'_D#TH/g27;!2$R25;R!3+D3!2'_D#UE/g25;$H;R!2+Y!3+D3!2'_D#VF/g26;!3+D3!2'_D#VH/g27;!5'_CQ!3+D3!2'_D#WH/g27;%~R!2'_G#W#V!1'_B#W$~RQ$~R!3+D3!2'_D#XH/g27;!2$R26;R!3+D3!2'_D#YF/g26;$R27;R!3+D3!2'_D#ZH/g27;$H;R!2'_G#[#Z!5'_CR!2+Y!3+D3!2'_D#[:!2'_D#\:!2+Y!3+D3!2'_D#[;!2'_D#\;!2+Y!3+D3!2'_D#[=!2'_D#\=!2+Y!3+D3!2'_D#[@!2'_D#\@!2+Y!3+D3!2'_D#[B!2'_D#\B!2+Y!3+D3!2'_D#[C!2'_D#\C!2+Y!3+D3!2'_D#[D!2'_D#\D!2+Y!3+D3!2'_D#[E!2'_D#\E!2+Y!3+D3!2'_D#[F!2'_D#\F!3+D3!2'_D#[H!2'_D#\H!1'_B#[$~RR$~R!2+Y!3+D3!2'_D#\:!2'_D#^0:!2+Y!3+D3!2'_D#\;!2'_D#^0;!2+Y!3+D3!2'_D#\=!2'_D#^0=!2+Y!3+D3!2'_D#\@!2'_D#^0@!2+Y!3+D3!2'_D#\B!2'_D#^0B!2+Y!3+D3!2'_D#\C!2'_D#^0C!2+Y!3+D3!2'_D#\D!2'_D#^0D!2+Y!3+D3!2'_D#\E!2'_D#^0E!2+Y!3+D3!2'_D#\F!2'_D#^0F!3+D3!2'_D#\H!2'_D#^0H!2$P2;R!3+D3!2'_D#^06!2'_D#^16$H;R!2+Y!3+D3!2'_D#^1:S!2+Y!3+D3!2'_D#^1;T!2+Y!3+D3!2'_D#^1=U!2+Y!3+D3!2'_D#^1@V!2+Y!3+D3!2'_D#^1BW!2+Y!3+D3!2'_D#^1CX!2+Y!3+D3!2'_D#^1DY!2+Y!3+D3!2'_D#^1EZ!2+Y!3+D3!2'_D#^1F[!3+D3!2'_D#^1H\!5'_C^0!2+Y!3+D3T!2'_D#^3;!2+Y!3+D3U!2'_D#^3=!2+Y!3+D3V!2'_D#^3@!2+Y!3+D3W!2'_D#^3B!2+Y!3+D3X!2'_D#^3C!2+Y!3+D3Y!2'_D#^3D!2+Y!3+D3Z!2'_D#^3E!2+Y!3+D3[!2'_D#^3F!3+D3\!2'_D#^3H!1'_B#^2$~R^0$~R!2+Y!3+D3!2'_D#^3;!2'_D#^4;!2+Y!3+D3!2'_D#^3=!2'_D#^4=!2+Y!3+D3!2'_D#^3@!2'_D#^4@!2+Y!3+D3!2'_D#^3B!2'_D#^4B!2+Y!3+D3!2'_D#^3C!2'_D#^4C!2+Y!3+D3!2'_D#^3D!2'_D#^4D!2+Y!3+D3!2'_D#^3E!2'_D#^4E!2+Y!3+D3!2'_D#^3F!2'_D#^4F!3+D3!2'_D#^3H!2'_D#^4H!2$P8;R!3+D3!2'_D#^4:!2'_D#^5:$H;R!2+Y!3+D3!2'_D#^5;^1!2+Y!3+D3!2'_D#^5=^2!2+Y!3+D3!2'_D#^5@^3!2+Y!3+D3!2'_D#^5B^4!2+Y!3+D3!2'_D#^5C^5!2+Y!3+D3!2'_D#^5D^6!2+Y!3+D3!2'_D#^5E^7!2+Y!3+D3!2'_D#^5F^8!3+D3!2'_D#^5H^9!5'_C^:!2+Y!3+D3^2!2'_D#^7=!2+Y!3+D3^3!2'_D#^7@!2+Y!3+D3^4!2'_D#^7B!2+Y!3+D3^5!2'_D#^7C!2+Y!3+D3^6!2'_D#^7D!2+Y!3+D3^7!2'_D#^7E!2+Y!3+D3^8!2'_D#^7F!3+D3^9!2'_D#^7H!1'_B#^6$~R^:$~R!2+Y!3+D3!2'_D#^7=!2'_D#^8=!2+Y!3+D3!2'_D#^7@!2'_D#^8@!2+Y!3+D3!2'_D#^7B!2'_D#^8B!2+Y!3+D3!2'_D#^7C!2'_D#^8C!2+Y!3+D3!2'_D#^7D!2'_D#^8D!2+Y!3+D3!2'_D#^7E!2'_D#^8E!2+Y!3+D3!2'_D#^7F!2'_D#^8F!3+D3!2'_D#^7H!2'_D#^8H!2$P9;R!3+D3!2'_D#^8;!2'_D#^9;$H;R!2+Y!3+D3!2'_D#^9=^;!2+Y!3+D3!2'_D#^9@^<!2+Y!3+D3!2'_D#^9B^=!2+Y!3+D3!2'_D#^9C^>!2+Y!3+D3!2'_D#^9D^?!2+Y!3+D3!2'_D#^9E^@!2+Y!3+D3!2'_D#^9F^A!3+D3!2'_D#^9H^B!5'_C^C!2+Y!3+D3^<!2'_D#^;@!2+Y!3+D3^=!2'_D#^;B!2+Y!3+D3^>!2'_D#^;C!2+Y!3+D3^?!2'_D#^;D!2+Y!3+D3^@!2'_D#^;E!2+Y!3+D3^A!2'_D#^;F!3+D3^B!2'_D#^;H!1'_B#^:$~R^C$~R!2+Y!3+D3!2'_D#^;@!2'_D#^<@!2+Y!3+D3!2'_D#^;B!2'_D#^<B!2+Y!3+D3!2'_D#^;C!2'_D#^<C!2+Y!3+D3!2'_D#^;D!2'_D#^<D!2+Y!3+D3!2'_D#^;E!2'_D#^<E!2+Y!3+D3!2'_D#^;F!2'_D#^<F!3+D3!2'_D#^;H!2'_D#^<H!2$P21;R!3+D3!2'_D#^<=!2'_D#^==$H;R!2+Y!3+D3!2'_D#^=@^D!2+Y!3+D3!2'_D#^=B^E!2+Y!3+D3!2'_D#^=C^F!2+Y!3+D3!2'_D#^=D^G!2+Y!3+D3!2'_D#^=E^H!2+Y!3+D3!2'_D#^=F^I!3+D3!2'_D#^=H^J!5'_C^K!2+Y!3+D3^E!2'_D#^?B!2+Y!3+D3^F!2'_D#^?C!2+Y!3+D3^G!2'_D#^?D!2+Y!3+D3^H!2'_D#^?E!2+Y!3+D3^I!2'_D#^?F!3+D3^J!2'_D#^?H!1'_B#^>$~R^K$~R!2+Y!3+D3!2'_D#^?B!2'_D#^@B!2+Y!3+D3!2'_D#^?C!2'_D#^@C!2+Y!3+D3!2'_D#^?D!2'_D#^@D!2+Y!3+D3!2'_D#^?E!2'_D#^@E!2+Y!3+D3!2'_D#^?F!2'_D#^@F!3+D3!2'_D#^?H!2'_D#^@H!2$P3;R!3+D3!2'_D#^@@!2'_D#^A@$H;R!2+Y!3+D3!2'_D#^AB^L!2+Y!3+D3!2'_D#^AC^M!2+Y!3+D3!2'_D#^AD^N!2+Y!3+D3!2'_D#^AE^O!2+Y!3+D3!2'_D#^AF^P!3+D3!2'_D#^AH^Q!5'_C^R!2+Y!3+D3^M!2'_D#^CC!2+Y!3+D3^N!2'_D#^CD!2+Y!3+D3^O!2'_D#^CE!2+Y!3+D3^P!2'_D#^CF!3+D3^Q!2'_D#^CH!1'_B#^B$~R^R$~R!2+Y!3+D3!2'_D#^CC!2'_D#^DC!2+Y!3+D3!2'_D#^CD!2'_D#^DD!2+Y!3+D3!2'_D#^CE!2'_D#^DE!2+Y!3+D3!2'_D#^CF!2'_D#^DF!3+D3!2'_D#^CH!2'_D#^DH!2$P4;R!3+D3!2'_D#^DB!2'_D#^EB$H;R!2+Y!3+D3!2'_D#^EC^S!2+Y!3+D3!2'_D#^ED^T!2+Y!3+D3!2'_D#^EE^U!2+Y!3+D3!2'_D#^EF^V!3+D3!2'_D#^EH^W!5'_C^X!2+Y!3+D3^T!2'_D#^GD!2+Y!3+D3^U!2'_D#^GE!2+Y!3+D3^V!2'_D#^GF!3+D3^W!2'_D#^GH!1'_B#^F$~R^X$~R!2+Y!3+D3!2'_D#^GD!2'_D#^HD!2+Y!3+D3!2'_D#^GE!2'_D#^HE!2+Y!3+D3!2'_D#^GF!2'_D#^HF!3+D3!2'_D#^GH!2'_D#^HH!2$P23;R!3+D3!2'_D#^HC!2'_D#^IC$H;R!2+Y!3+D3!2'_D#^ID^Y!2+Y!3+D3!2'_D#^IE^Z!2+Y!3+D3!2'_D#^IF^[!3+D3!2'_D#^IH^\!5'_C_0!2+Y!3+D3^Z!2'_D#^KE!2+Y!3+D3^[!2'_D#^KF!3+D3^\!2'_D#^KH!1'_B#^J$~R_0$~R!2+Y!3+D3!2'_D#^KE!2'_D#^LE!2+Y!3+D3!2'_D#^KF!2'_D#^LF!3+D3!2'_D#^KH!2'_D#^LH!2$P24;R!3+D3!2'_D#^LD!2'_D#^MD$H;R!2+Y!3+D3!2'_D#^ME_1!2+Y!3+D3!2'_D#^MF_2!3+D3!2'_D#^MH_3!5'_C_4!2+Y!3+D3_2!2'_D#^OF!3+D3_3!2'_D#^OH!1'_B#^N$~R_4$~R!2+Y!3+D3!2'_D#^OF!2'_D#^PF!3+D3!2'_D#^OH!2'_D#^PH!2$P25;R!3+D3!2'_D#^PE!2'_D#^QE$H;R!2+Y!3+D3!2'_D#^QF_5!3+D3!2'_D#^QH_6!5'_C_7!3+D3_6!2'_D#^SH!1'_B#^R$~R_7$~R!3+D3!2'_D#^SH!2'_D#^TH!2$P26;R!3+D3!2'_D#^TF!2'_D#^UF$P27;R!3+D3!2'_D#^UH_8vd!6'B3_9$b;R3!2+Y!3+D3#17_V!6'B3_:$b;R3!2+Y_W!2+Y!3+D3#1/l;_U!6'B3_<$b;R3!2+Y_W!2+Y_X!2+Y!3+D3#1<_T!6'B3_>$b;R3!2+Y_W!2+Y_X!2+Y_Y!2+Y!3+D3#1>_S!6'B3_@$b;R3!2+Y_W!2+Y_X!2+Y_Y!2+Y_Z!2+Y!3+D3#1/g3;_R!6'B3_B$b;R3!2+Y_W!2+Y_X!2+Y_Y!2+Y_Z!2+Y_[!2+Y!3+D3#1/g4;_Q!6'B3_D$b;R3!2+Y_W!2+Y_X!2+Y_Y!2+Y_Z!2+Y_[!2+Y_\!2+Y!3+D3#1/g23;_P!6'B3_F$b;R3!2+Y_W!2+Y_X!2+Y_Y!2+Y_Z!2+Y_[!2+Y_\!2+Y`0!2+Y!3+D3#1/g24;_O!6'B3_H$b;R3!2+Y_W!2+Y_X!2+Y_Y!2+Y_Z!2+Y_[!2+Y_\!2+Y`0!2+Y`1!2+Y!3+D3#1/g25;_N!6'B3_J$b;R3!2+Y_W!2+Y_X!2+Y_Y!2+Y_Z!2+Y_[!2+Y_\!2+Y`0!2+Y`1!2+Y`2!2+Y!3+D3#1/g26;_M!6'B3_L$b;R3!2+Y_W!2+Y_X!2+Y_Y!2+Y_Z!2+Y_[!2+Y_\!2+Y`0!2+Y`1!2+Y`2!2+Y!3+D3!2'_D#^XF/g26;!3+D3#1/g27;!4,_5!3+D3_97_V#^R!4,_5_;_U#^N!4,_5_=_T#^J!4,_5_?_S#^F!4,_5_A_R#^B!4,_5_C_Q#^>!4,_5_E_P#^:!4,_5_G_O#^6!4,_5_I_N#^2!4,_5_K_M#[#Z_8#1!2'_D#^VF#2!2'_D#^VE#6!2'_D#^VD#:!2'_D#^VC#>!2'_D#^VB#B!2'_D#^V@#F!2'_D#^V=#J!2'_D#^V;#N!2'_D#^V:#R!2'_D#^V6#V!1'_B#^V#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1").
Qed.

  Lemma LM_refl : LM mem1.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S70!1,^W|600;!1+^V0!2'^Y0#1!1'_2!2+Y!2'T!2'J/su;!1,^[|628;2!2'Z2!2'J/su;!1,^[|608;|30;!1+_H!1+^V!1,^W4!1/mem1;#2!4,_5%x;R1%~R3!3+D566!2'_I/mem1;/mem1;$x;R1$~R3!2,O56!1'_J/mem1;").
Qed.

  Lemma LM_rdn : forall m (a : word) n bs,
    LM m -> rdn RSEGS mem1 a n = Some bs ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    (bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
    rdn RSEGS m a n = Some bs.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SU0|600;!1,^W0!1+^V1|30;!1+^V!1,^W3!1+_H4!1+@4!1,^[|628;!2'J/su;7!2'^Y1#1!1,^[|608;!2'J/su;:!1'_2!2+Y!2'T89!2'Z9;!1/mem1;#2%x;R2%~R<!3+D5!1#7#2=!1+_H6|10;!1,^[@!1,^[0!2'^ZAB!2'^Y1#:!2'^Y1#<!2'T,HA}3}2!2,^6+GH}1!1,_;+G!1+^<+G!2,^G+G|21;!2,^G+G@|22;!3,_=+GM!2,^G+GO!1,^K+^>!2,^G+G,^5!3,^F+GR!2,^D+G7!3,^F+GR!2,^D+G:$m;R%~R25$a;R2$n;R+?$bs;R6$H0;R!1'_K#4!5'_C>!2'_I/mem1;#5%~R!3+D?!4'_L'3/mem1;#4#3!2,_M6#2%~R!2'T!2'^X!2'^Y1#5!1'K#4C%~R!2+X!2'T!2'^X!2'^Y1#6!1'K#58!2'T;!2'^Y1#6!3+D?!4'_L'3#8#7#6!2,_M6#5$~R>$~R!2'_I/mem1;#6!2$E;R%x;R2%~R<!3+D5!1#9#2=$G;R!2'_I/mem1;#8$H;R!3+D?!4'_L'3/mem1;#8#7!2,_M6#6$Hnw;R!2'T!2'^X!2'^Y1#9!1'K#8C$D;R!2+X!2'T!2'^XD!1'K#98!2'T;D!6'B?!4'_L'3/mem1;#;#:$o;R?!3+D?#1!2,_M6#:#3!4'_L'3#<#;#:!7'_N'3#:#</mem1;#;#2$x;R2$Hx;R!2+Y!2'TE9!2'Z9!2'^XE!1'K#;!2#7#2&cstr;R!1'V#<!2'T,H!1'K#<&__sat74;R!2'_8AB%~R!2'Z,HA%~R!2'T,HB!2'Z,HC&__sat73;R$Ha;RF$~R+_9!3'_:AB#2%Ha;RF%~R+_9!2'T,HC&__arith;R$__x4;R+G$__x3;R+G$__x2;R+G$__x1;R+G&__wit;R!3,[+\!2,^0!3,^1+G!2,^6+GG!3,^1+GI!2,^6+GJ,^7!3,[+\!2,^0!3,^1+G!2,^6+G}4!3,^1+GI!2,^6+G,F,^7!1,6+\!1+@+\&__varmap;R!4,^8+G!4,^8+GK#3!2,^9+G#5#2!4,^8+G!2,^9+G#4#5K!1+^:+G&__ff;R!8,^;L'^=+^>+^>,^?!7,^AL'^=+^>+^>,^?!7,^BL'^=+^>+^>,^?!4,^C+GM,^LN,^H!7,^BL'^=+^>+^>,^?!4,^C+GN,^EP,^HQ!8,^;L'^=+^>+^>,^?!7,^@L'^=+^>+^>,^?!7,^BL'^=+^>+^>,^?!4,^C+GP,^LS,^H!7,^BL'^=+^>+^>,^?!4,^C+GT,^LM,^HQ!6,_<L'^=+^>+^>,^?!7,^AL'^=+^>+^>,^?!7,^BL'^=+^>+^>,^?!4,^C+GS,^LN,^H!7,^BL'^=+^>+^>,^?!4,^C+GN,^ET,^H!2'^ML,^?!4'^N#1#3vv!2,O+^O,^P!3+D+^O!2'^Q#1#3,^P!3'^R+G,H#2%__x4;R+G%__x3;R+G%__x2;R+G%__x1;R+G%~R!2+Y!2'T#3#2!2'Z#2!2'^X#3#4%~R!2+X!2'T!2'^X#4#5!2'J#27!2'T!2'J#2:#4%~R!2+Y!2'T!2'J#37#4!2'Z#4!2'J#3:+_?!6#1!1'K#@!2'^Y1#A!2'^Y1#6/su;#5#7#2#1#1").
Qed.

  Lemma LM_store_ok : forall m (a : word) n,
    LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S80!1,^W|600;!1+^V0|30;!1+_H!1+^V!1,^W2!2'^Y0#1!1'_2!2+Y!2'T!2'J/su;!1,^[|628;4!2'Z4!2'J/su;!1,^[|608;!1/mem1;#2%x;R1%~R5!3+D3!1#6#26$m;R%~R13$a;R1$n;R+?$H0;R!1'_K#3!5'_C7!2'_I/mem1;#4%~R!3+D+^O!4'_O'3/mem1;#3#2,^P!3+D+^O!4'_O'3#5#4#3,^P$~R7$~R!2'_I/mem1;#5!2$E;R%x;R1%~R5!3+D3!1#8#26$G;R!2'_I/mem1;#7$H;R!3+D+^O!4'_O'3/mem1;#7#6,^P!7'_P'3#7/mem1;#9#8#2#1#2#1#1").
Qed.

  Lemma LM_wbytes8 : forall m (a : Z) (v : word),
    LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
    LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S_00|600;!1,^W0!1+^V1|30;!1+^V!1,^W3!1+_H4!1,^[|628;!2'J/su;6!2'^Y1#1!1,^[|608;!2'J/su;9!1'_2!2+Y!2'T78!2'Z8:!1/mem1;#2%x;R2%~R;!3+D5!1#6#2<!1,^[3}8!2'_31#;!2'_R?#:!4'_Q#<@A#2!2'_31#9!2'_R?#8!3'_Q#:CD!2'^Y1!2'_31#<!2'^Y1#3!1'K#1!2'^XFH!1'K?!2'^X#1J!2'^Y1#2!2'T#;L!2'^X#;J!2'ZLN!2+YMO!1'_2P!2'^X#;>!2'ZLR!2+YMS$x;R+G#1!B'P+G+G+G+G+G+G'^XUUU'^X$n;R+G$m;R+G!2,O+G!4'_W+G+G'_X!2'^X#2#1#;#;!2,O+G#;J>!<'_Y+?+G+G+G'K'KUU$x;R+?!2,O+GH?>!2,O+G>}4!2,^6+GW}3!2,^6+G,F}2!2,^6+G[}1!2,^6+G^0!1,6+\!1+@+\!2,^9+G#3!1+^:+G!1+^<+G|11;!2,^G+G^7!2,^D+G6!3,^F+G^8^9|10;!2,^G+G^;!2,^D+G9!3,^F+G^8^=!1,^K+^>!2,^G+G,^5!3,_=+G^@!2,^D+G>!2'^M^6,^?!4'^N#1#3vv!2,O+^O,^P!3+D+^O!2'^Q#1#3,^P!3'^R+G,H#2!2'^Y1@!3,[+\!2,^0!3,^1+G\!3,^1+G^1Z,^7^2!4,^8+G^4#2!1,_;+G|P00000000;!1,^[^G!1,^[|630;!1,^[^;!1,^[0!2'_8^J^K!2'^Z^J^K%~R!2'Z,H^J%~R!2'T,H^K!2'Z,H^M!2'T,H^J$Ha;R^O$~R+_9!3'_:^J^K#2%Ha;R^O%~R+_9!2'T,H^M!7,^B^6'^=+^>+^>,^?!4,^C+G^A,^L!3,^F+G^<^=,^H!1,^[|^2000000000000;!7,^B^6'^=+^>+^>,^?!4,^C+G^<,^L!2,^D+G^S,^H!3,_>+G!2,^D+G^J1!2'T!2'^X#1>!2'J#29!2'T#3^S!4#1/su;#>#6/SUhi;!3'_7#;&__arith;R$__x2;R+G$__x1;R+G&__wit;R^E^3&__varmap;R^F^5&__ff;R!8,^;^6'^=+^>+^>,^?!7,^B^6'^=+^>+^>,^?!4,^C+G!3,^F+G^<^9,^L^@,^H^?!8,^;^6'^=+^>+^>,^?!7,^B^6'^=+^>+^>,^?!4,^C+G!3,_=+G!2,^D+G^H!2,^D+G^I,^L^<,^H^?!7,^B^6'^=+^>+^>,^?!4,^C+G!2,^D+G,H,^L^@,^H^B^C%__x2;R+G%__x1;R+G%~R!2'T!2'J#26#1%~R!2'T!2'^X^H^I#3!2'T,H#3!4#1/su;#<#5/SUlo;&__sat74;R^L^N&__sat73;R^P^Q&__arith;R$__x2;R+G$__x1;R+G&__wit;R^E^3&__varmap;R^F^5&__ff;R!8,^;^6'^=+^>+^>,^?^R^?!8,^;^6'^=+^>+^>,^?^T^?!7,^B^6'^=+^>+^>,^?!4,^C+G^@,^E^U,^H^B^C%__x2;R+G%__x1;R+G%~R^V%~R^W!2'Z#3^M^X!2'=4A!2'_Z?#:!2'TN^M$m;R%~R25$a;R+G$v;R2$H;R!1'_K#3!5'_C=!2'_I/mem1;#4%~R!2'T7#3%~R!2'T!2'^X#4>:!1'_K!3'_Q#6!2'_31#5!2'_R?#4$~R=$~R!2'_I/mem1;#5!2$E;R%x;R2%~R;!3+D5!1#8#2<$G;R!2'_I/mem1;#7$Hlo;R!2'T7#7$Hhi;R!2'T!2'^X#8>:!4,_5%x;R2%~R;!3+D5B<!2'_I/mem1;E$x;R2$Hx;R;!6'B5!1#<#2$o;R5!3+D5#1!1/mem1;#3!2#6#2#1B!6'_SA#<@#2vd!6'B+??$n;R+?!1'_2!2+Y!2'TFG!2'ZGI!6'B+G#;$z;R+G!1'_2!2+Y!2'T#1G!2'ZGKvd!4'EQ!1'_2T!3'_TPT!6'_UMOMS!1'_VM!<'L+G+G'ZU'Z$x;R+G$y;R+G!1'_V!2'Z#2#1LL!2,O+GLNRV&__arith;R$__x3;R+G$__x2;R+G$__x1;R+G&__wit;R!3,[+\!2,^0!3,^1+GX!3,^1+G!2,^6+GYZ,^7!3,[+\!2,^0!3,^1+GX!3,^1+G\^1,^7^2^3&__varmap;R!4,^8+G^4#2!2,^9+G#4^5&__ff;R!8,^;^6'^=+^>+^>,^?!6,_<^6'^=+^>+^>,^?!7,^A^6'^=+^>+^>,^?!7,^B^6'^=+^>+^>,^?!4,^C+G^:,^L^<,^H!7,^B^6'^=+^>+^>,^?!4,^C+G^<,^E^>,^H^?!8,^;^6'^=+^>+^>,^?!7,^B^6'^=+^>+^>,^?!4,^C+G^A,^L^>,^H^?!8,^;^6'^=+^>+^>,^?!7,^B^6'^=+^>+^>,^?!4,^C+G^:,^L^@,^H^?!6,_<^6'^=+^>+^>,^?!7,^A^6'^=+^>+^>,^?!7,^B^6'^=+^>+^>,^?!4,^C+G^@,^L^<,^H!7,^B^6'^=+^>+^>,^?!4,^C+G^<,^E^A,^H^B^C%__x3;R+G%__x2;R+G%__x1;R+G%~R%~R!2+Y!2'T!2'J#36#2!2'Z#2!2'J#39+_?%~R!2'T!2'^X#2>!2'J#49%~R!2'T!2'J#56#3%~R!2+Y!2'T#4#5!2'Z#5!2'^X#4>+_?!6#1/su;G#<#2#4#5Q^D^Y^Z^[!1'_2!3'_[#2@!1'K^Z!6'B+??$n;R+?!2'TI^M!6'B+G#;$z;R+G!2'TK^Mvd!4'E^\!2'TR^M!<'L+G+G'TU'T$x;R+G$y;R+G!1'_V!2'T#2#1NRV^M^M!2,O+G^M&__sat74;R^L^N&__sat73;R^P^Q&__arith;R$__x2;R+G$__x1;R+G&__wit;R^E^3&__varmap;R^F^5&__ff;R!8,^;^6'^=+^>+^>,^?^R^?!8,^;^6'^=+^>+^>,^?^T^?!7,^B^6'^=+^>+^>,^?!4,^C+G^A,^L^U,^H^B^C%__x2;R+G%__x1;R+G%~R^V%~R^W!2'T!2'^X#3>^M^X^\^D^Y^Z^[!5'_\/mem1;#:E#3!3'`0D#:C#2#1#1").
Qed.

  (* [comment removed for export] *)
  Lemma finish_b : forall regs m,
    RI regs -> LM m ->
    SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs (0xaf260 : word) m (seg_rom RSEGS)) model) K.
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SeX0|21;!1,^W0|600;!1,^W2!1+^V3!2'_A14|30;|10;!1,^[7!3,_E18,_F!1,^[|630;!2'_33!2'J/su;:!3+D4!2'_D#49;!1,^[6!3,_E1=,_F|31;!1,^[?!3,_E1@,_F!2'_33/f;|45;!1,^[C!3,_E1D,_F!1,^[|C79890;!2'_33F|11;!1,^[H!3,_E1I,_F|20;!1,^[K!3,_E1L,_F!1,^[|47;!3,_E1N,_F|48;!1,^[P!3,_E1Q,_F!1,^[|49;!3,_E1S,_F|4a;!1,^[U!3,_E1V,_F|4b;!1,^[X!3,_E1Y,_F!1,^[|C2f260;!3,_E3[,_F!1'`3'3!2'_D#69!3+D4!2'_D#8>/l;!2'_D#:>!3+D4!2'_D#<AB!2'_D#>A!3+D4!2'_D#@EG!2'_D#BE!3+D4!2'_D#DJ/g3;!2'_D#FJ!3+D4!2'_D#HM/g4;!2'_D#JM!3+D4!2'_D#LO/g23;!2'_D#NO!3+D4!2'_D#PR/g24;!2'_D#RR!3+D4!2'_D#TT/g25;!2'_D#VT!3+D4!2'_D#XW/g26;!2'_D#ZW!2'J/su;=!2'_33^D}8!1'K^F!2'^X#1^G!1,^[2!2'^Z8^I$z;R+G!2'T^H^J!2'^X^D^G!2'^X^D=$x;R+G#1$x;R+G$y;R+G!1'_V!2'T#2#1$n;R+G$m;R+G!2,O+G!4'_W+G+G'_X!2'^X#2#1!<'_Y+?+G+G+G'K'K^N^N$x;R+?!2,O+G!1'K#1^F=!2,O+G=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^P^D^D!2,O+G^D^G=^Q!2,O+G^J!2'_88^I%~R!2'Z,H8%~R!2'T,H^I!2'Z,H^J!2'T,H8$Ha;R^V$~R+_9!3'_:8^I#2%Ha;R^V%~R+_9!2'T,H^J!1,6+\!1+@+\!2,^9+G#2!1+^:+G!1+^<+G!2,^G+G,^5!1,^[|^2000000000000;!7,^B_0'^=+^>+^>,^?!4,^C+G_1,^L!2,^D+G_2,^H!1,^K+^>!2,^D+G=!3,^F+G_1_5!3,_=+G_6_5!3,_>+G!2,^D+G83!2'^M_0,^?!4'^N#1#3vv!2,O+^O,^P!3+D+^O!2'^Q#1#3,^P!3'^R+G,H#2!2'T#1_2!2'J#2=!2#1/su;/SUhi;!2'^Y3^E|P00000000;!1,^[_?!3,_=+G!2,^D+G_@!2,^D+G:!7,^B_0'^=+^>+^>,^?!4,^C+G_A,^L_1,^H!2,^D+G,H!2'^X_@:!2'T_D#1!2#1/su;/SUlo;!3'_7^D&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^L_6,^H_9_:%__x1;R+G%~R_E!2'T,H_<_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G_6,^E_8,^H_9_:%__x1;R+G%~R_;!2'Z_<^J_=!1,^[|628;!2'J/su;_H!1,^[|608;!2'J/su;_J$z;R+G!2+X!2'T^H_I!2'T_K#1!2'T^L_I!2'T_K^D!2'T^M_I!2,O+G_I!2,^D+G_H!3,^F+G_1_Q!3,^F+G_1!2,^D+G_J!2'J#1=!2'J#1_H!2'J#1_J!1#1/su;|40;!1,^[_X!2'J/su;_Y!2'_33_Z!2'^X_Z^G!2'^X_Z=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^P_Z_Z!2,O+G_Z^G=^Q!3,^F+G_1!2,^D+G_Y!3,_=+G`2_5!2'J#2_Y!2'^Y3_[!3'_7_Z&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^L`2,^H_9_:%__x1;R+G%~R_E!2'T,H`4_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G`2,^E_8,^H_9_:%__x1;R+G%~R_;!2'Z`4^J_=!2'T_\_I!2'T_K_Z!2'T`0_I!2'J#1_Y!2'J/su;Q!2'_33`;!2'^X`;^G!2'^X`;=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^P`;`;!2,O+G`;^G=^Q!3,^F+G_1!2,^D+GQ!3,_=+G`@_5!2'J#2Q!2'^Y3`<!3'_7`;&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^L`@,^H_9_:%__x1;R+G%~R_E!2'T,H`B_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G`@,^E_8,^H_9_:%__x1;R+G%~R_;!2'Z`B^J_=!2'T`=_I!2'T_K`;!2'T`>_I!2'J#1Q|500;!1,^[`I!2'J/su;`J!2'_33`K!2'^X`K^G!2'^X`K=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^P`K`K!2,O+G`K^G=^Q!3,^F+G_1!2,^D+G`J!3,_=+G`P_5!2'J#2`J!2'^Y3`L!3'_7`K&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^L`P,^H_9_:%__x1;R+G%~R_E!2'T,H`R_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G`P,^E_8,^H_9_:%__x1;R+G%~R_;!2'Z`R^J_=!2'T`M_I!2'T_K`K!2'T`N_I!2'J#1`J!1,^[|508;!2'J/su;`Y!2'_33`Z!2'^X`Z^G!2'^X`Z=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^P`Z`Z!2,O+G`Z^G=^Q!3,^F+G_1!2,^D+G`Y!3,_=+Ga2_5!2'J#2`Y!2'^Y3`[!3'_7`Z&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^La2,^H_9_:%__x1;R+G%~R_E!2'T,Ha4_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+Ga2,^E_8,^H_9_:%__x1;R+G%~R_;!2'Za4^J_=!2'T`\_I!2'T_K`Z!2'Ta0_I!2'J#1`Y|510;!1,^[a;!2'J/su;a<!2'_33a=!2'^Xa=^G!2'^Xa==!B'P+G+G+G+G+G+G'^X^N^N^N'^X^Pa=a=!2,O+Ga=^G=^Q!3,^F+G_1!2,^D+Ga<!3,_=+GaB_5!2'J#2a<!2'^Y3a>!3'_7a=&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^LaB,^H_9_:%__x1;R+G%~R_E!2'T,HaD_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+GaB,^E_8,^H_9_:%__x1;R+G%~R_;!2'ZaD^J_=!2'Ta?_I!2'T_Ka=!2'Ta@_I!2'J#1a<|518;!1,^[aK!2'J/su;aL!2'_33aM!2'^XaM^G!2'^XaM=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^PaMaM!2,O+GaM^G=^Q!3,^F+G_1!2,^D+GaL!3,_=+GaR_5!2'J#2aL!2'^Y3aN!3'_7aM&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^LaR,^H_9_:%__x1;R+G%~R_E!2'T,HaT_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+GaR,^E_8,^H_9_:%__x1;R+G%~R_;!2'ZaT^J_=!2'TaO_I!2'T_KaM!2'TaP_I!2'J#1aL!2'J/su;^I!2'_33a[!2'^Xa[^G!2'^Xa[=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^Pa[a[!2,O+Ga[^G=^Q!3,^F+G_1!2,^D+G^I!3,_=+Gb3_5!2'J#2^I!2'^Y3a\!3'_7a[&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^Lb3,^H_9_:%__x1;R+G%~R_E!2'T,Hb5_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+Gb3,^E_8,^H_9_:%__x1;R+G%~R_;!2'Zb5^J_=!2'Tb0_I!2'T_Ka[!2'Tb1_I!2'J#1^I!2'_33_K!2'_R^F/can;!2'^X_K^G!2'^X_K=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^P_K_K!2,O+G_K^G=^Q!3,_=+G_S_5!2'J#2_J!2'^Y3b<!3'_7_K&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^L_S,^H_9_:%__x1;R+G%~R_E!2'T,HbB_F&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^E_8,^H_9_:%__x1;R+G%~R_;!2'ZbB^J_=!2'Tb>_I!2'T_K_K!2'Tb?_I!2'^XF^G!2'^XF=!2'TbI^J!B'P+G+G+G+G+G+G'^X^N^N^N'^X^PFF!2,O+GF^G=^Q!1,_;+G!2,^D+GF!3,_=+GbM_5!2'^Y3G!3'_7F&__arith;R&__wit;R^Y^Z&__varmap;RbL^\&__ff;R!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^LbM,^H_9_:!2'T,HF#1&__sat74;R^T^U&__sat73;R^W^X&__arith;R&__wit;R^Y^Z&__varmap;RbL^\&__ff;R!7,^B_0'^=+^>+^>,^?!4,^C+GbM,^E_8,^H_9_:!2'ZF^J#1!2'TbH_I!2'T_KF!2'TbI_I!1,^[|618;!2'^X/f;bT!2'_33bU!2'^XbU^G!2'^XbU=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^PbUbU!2,O+GbU^G=^Q!1,^[|768;!7,^B_0'^=+^>+^>,^?!4,^C+G!3,_=+G_1!2,^D+GbZ,^LbM,^H!3,_=+G_1!2,^D+GbT!3,_=+Gb\_5!2'T!2'^X#1bZF!2'^X#2bT!2#1/f;/Fhi;!2'^Y3bV!1,^[|C47000;!7,^B_0'^=+^>+^>,^?!4,^C+G!2,^D+Gc5,^L_1,^H!2'Tc5#1!2#1/f;/Flo;!3'_7bU&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?c6_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^Lb\,^H_9_:%__x1;R+G%~Rc7!2'T,Hc2c8&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?b[_4!7,^B_0'^=+^>+^>,^?!4,^C+Gb\,^E_8,^H_9_:%__x1;R+G%~Rc1!2'Zc2^Jc3!2'TbW_I!2'T_KbU!2'TbX_I}2}1!3,[+\!2,^0!3,^1+G!2,^6+Gc=!3,^1+G!2,^6+Gc>!2,^6+G,F,^7^Y!4,^8+G!2,^9+G#3#2bL!2,^G+G7!7,^B_0'^=+^>+^>,^?!4,^C+G_A,^LcA,^H!3,^F+GcA_Q!6,^I_0'^=+^>+^>,^?#5!2'T_D#3!2'J#4_H!1,^[|620;!2'^X/f;cG!2'_33cH!2'^XcH^G!2'^XcH=!B'P+G+G+G+G+G+G'^X^N^N^N'^X^PcHcH!2,O+GcH^G=^Q!3,_=+G_1!2,^D+GcG!3,_=+GcM_5!2'^X#2cG!2'^Y3cI!3'_7cH&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?c6_4!7,^B_0'^=+^>+^>,^?!4,^C+G_C,^LcM,^H_9_:%__x1;R+G%~Rc7!2'T,HcOc8&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?b[_4!7,^B_0'^=+^>+^>,^?!4,^C+GcM,^E_8,^H_9_:%__x1;R+G%~Rc1!2'ZcO^Jc3!2'TcJ_I!2'T_KcH!2'TcK_I|32;!1,^[cU!2'_33/su;!1,^[,^5|42;!1,^[cY!1,^[|43;|44;!1,^[c\|46;!1,^[d1!3,_E1Ivv,_F!2'`:1I!3,_E1Lvv,_F!2'`:1L!3,_E1Nvv,_F!2'`:1N!3,_E1Qvv,_F!2'`:1Q!3,_E1Svv,_F!2'`:1S!3,_E1Vvv,_F!2'`:1V!3,_E1Yvv,_F!2'`:1Y!5'`2/fx;#^1\#^0^0!3,_E1cV,_F!3+D4!2'_D#1d;/l;!3+D4!2'_D#19cW!3,_E1cX,_F!3+D4!2'_D#1d>/ret;!3+D4!2'_D#1>/e8;!3+D4!2'_D#1A/e9;!3,_E1cZ,_F!3+D4!2'_D#1dB/e18;!3,_E1c[,_F!3+D4!2'_D#1dD/e19;!3,_E1d0,_F!3+D4!2'_D#1dF/e20;!3+D4!2'_D#1E/e21;!3,_E1d2,_F!3+D4!2'_D#1dI/e22;!2'_D#1J!2'_D#^1J!2'_D#1M!2'_D#^1M!2'_D#1O!2'_D#^1O!2'_D#1R!2'_D#^1R!2'_D#1T!2'_D#^1T!2'_D#1W!2'_D#^1W!2'_D#1Z!2'_D#^1Z!2'_D#^3J!3+`9'3!5'`2/fx;#^4\#^3^0!5'`2/fx;#2/ret;!4'`;#^3/f;/bufp;/bufsz;^0!2'_D#^4M!2'_D#^4O!2'_D#^4R!2'_D#^4T!2'_D#^4W!2'_D#^4Z!2'_D#^7M!3+D4!2'_D#6d;/l;!2'_D#^8O!2'_D#^8R!2'_D#^8T!2'_D#^8W!2'_D#^8Z!2'_D#^;O!3+D4!2'_D#:9cW!2'_D#^<R!2'_D#^<T!2'_D#^<W!2'_D#^<Z!2'_D#^?R!3+D4!2'_D#>d>/ret;!2'_D#^@T!2'_D#^@W!2'_D#^@Z!2'_D#^CT!3+D4!2'_D#B>/e8;!2'_D#^DW!2'_D#^DZ!2'_D#^GW!3+D4!2'_D#FA/e9;!2'_D#^HZ!3+D4!2'_D#JdB/e18;!3+D4!2'_D#NdD/e19;!3+D4!2'_D#RdF/e20;!3+D4!2'_D#VE/e21;!3+D4!2'_D#ZdI/e22;!3+D4dL!2'_D#_3J!3+D4!2'_D#^5M!2'_D#_7M!3+D4!2'_D#^9O!2'_D#_;O!3+D4!2'_D#^=R!2'_D#_?R!3+D4!2'_D#^AT!2'_D#_CT!3+D4!2'_D#^EW!2'_D#_GW$regs;R5$m;R%~R4!1+_H!1+^V!1,^W6$RIr;R!1'_B#2$LMm;R!1'_K#2!5'_C<!2+Y!3+D4!2'_D#4>/l;!2+Y!3+D4!2'_D#4AB!2+Y!3+D4!2'_D#4EG!2+Y!3+D4!2'_D#4J/g3;!2+Y!3+D4!2'_D#4M/g4;!2+Y!3+D4!2'_D#4O/g23;!2+Y!3+D4!2'_D#4R/g24;!2+Y!3+D4!2'_D#4T/g25;!2+Y!3+D4!2'_D#4W/g26;!3+D4!2'_D#4Z/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#4\#3^0/model;/K;$~R<$~R!2+Y!3+D4!2'_D#5>/l;!2+Y!3+D4!2'_D#5AB!2+Y!3+D4!2'_D#5EG!2+Y!3+D4!2'_D#5J/g3;!2+Y!3+D4!2'_D#5M/g4;!2+Y!3+D4!2'_D#5O/g23;!2+Y!3+D4!2'_D#5R/g24;!2+Y!3+D4!2'_D#5T/g25;!2+Y!3+D4!2'_D#5W/g26;!3+D4!2'_D#5Z/g27;!2$R2;R!3+D4^1;$H;R!2+Y!3+D4!2'_D#7>/l;!2+Y!3+D4!2'_D#7AB!2+Y!3+D4!2'_D#7EG!2+Y!3+D4!2'_D#7J/g3;!2+Y!3+D4!2'_D#7M/g4;!2+Y!3+D4!2'_D#7O/g23;!2+Y!3+D4!2'_D#7R/g24;!2+Y!3+D4!2'_D#7T/g25;!2+Y!3+D4!2'_D#7W/g26;!3+D4!2'_D#7Z/g27;!5'_C^2!2+Y!3+D4!2'_D#8AB!2+Y!3+D4!2'_D#8EG!2+Y!3+D4!2'_D#8J/g3;!2+Y!3+D4!2'_D#8M/g4;!2+Y!3+D4!2'_D#8O/g23;!2+Y!3+D4!2'_D#8R/g24;!2+Y!3+D4!2'_D#8T/g25;!2+Y!3+D4!2'_D#8W/g26;!3+D4!2'_D#8Z/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#8\#7^0/model;/K;$~R^2$~R!2+Y!3+D4!2'_D#9AB!2+Y!3+D4!2'_D#9EG!2+Y!3+D4!2'_D#9J/g3;!2+Y!3+D4!2'_D#9M/g4;!2+Y!3+D4!2'_D#9O/g23;!2+Y!3+D4!2'_D#9R/g24;!2+Y!3+D4!2'_D#9T/g25;!2+Y!3+D4!2'_D#9W/g26;!3+D4!2'_D#9Z/g27;!2$R8;R!3+D4^3/l;$H;R!2+Y!3+D4!2'_D#;AB!2+Y!3+D4!2'_D#;EG!2+Y!3+D4!2'_D#;J/g3;!2+Y!3+D4!2'_D#;M/g4;!2+Y!3+D4!2'_D#;O/g23;!2+Y!3+D4!2'_D#;R/g24;!2+Y!3+D4!2'_D#;T/g25;!2+Y!3+D4!2'_D#;W/g26;!3+D4!2'_D#;Z/g27;!5'_C^4!2+Y!3+D4!2'_D#<EG!2+Y!3+D4!2'_D#<J/g3;!2+Y!3+D4!2'_D#<M/g4;!2+Y!3+D4!2'_D#<O/g23;!2+Y!3+D4!2'_D#<R/g24;!2+Y!3+D4!2'_D#<T/g25;!2+Y!3+D4!2'_D#<W/g26;!3+D4!2'_D#<Z/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#<\#;^0/model;/K;$~R^4$~R!2+Y!3+D4!2'_D#=EG!2+Y!3+D4!2'_D#=J/g3;!2+Y!3+D4!2'_D#=M/g4;!2+Y!3+D4!2'_D#=O/g23;!2+Y!3+D4!2'_D#=R/g24;!2+Y!3+D4!2'_D#=T/g25;!2+Y!3+D4!2'_D#=W/g26;!3+D4!2'_D#=Z/g27;!2$R9;R!3+D4^5B$H;R!2+Y!3+D4!2'_D#?EG!2+Y!3+D4!2'_D#?J/g3;!2+Y!3+D4!2'_D#?M/g4;!2+Y!3+D4!2'_D#?O/g23;!2+Y!3+D4!2'_D#?R/g24;!2+Y!3+D4!2'_D#?T/g25;!2+Y!3+D4!2'_D#?W/g26;!3+D4!2'_D#?Z/g27;!5'_C^6!2+Y!3+D4!2'_D#@J/g3;!2+Y!3+D4!2'_D#@M/g4;!2+Y!3+D4!2'_D#@O/g23;!2+Y!3+D4!2'_D#@R/g24;!2+Y!3+D4!2'_D#@T/g25;!2+Y!3+D4!2'_D#@W/g26;!3+D4!2'_D#@Z/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#@\#?^0/model;/K;$~R^6$~R!2+Y!3+D4!2'_D#AJ/g3;!2+Y!3+D4!2'_D#AM/g4;!2+Y!3+D4!2'_D#AO/g23;!2+Y!3+D4!2'_D#AR/g24;!2+Y!3+D4!2'_D#AT/g25;!2+Y!3+D4!2'_D#AW/g26;!3+D4!2'_D#AZ/g27;!2$R21;R!3+D4^7G$H;R!2+Y!3+D4!2'_D#CJ/g3;!2+Y!3+D4!2'_D#CM/g4;!2+Y!3+D4!2'_D#CO/g23;!2+Y!3+D4!2'_D#CR/g24;!2+Y!3+D4!2'_D#CT/g25;!2+Y!3+D4!2'_D#CW/g26;!3+D4!2'_D#CZ/g27;!5'_C^8!2+Y!3+D4!2'_D#DM/g4;!2+Y!3+D4!2'_D#DO/g23;!2+Y!3+D4!2'_D#DR/g24;!2+Y!3+D4!2'_D#DT/g25;!2+Y!3+D4!2'_D#DW/g26;!3+D4!2'_D#DZ/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#D\#C^0/model;/K;$~R^8$~R!2+Y!3+D4!2'_D#EM/g4;!2+Y!3+D4!2'_D#EO/g23;!2+Y!3+D4!2'_D#ER/g24;!2+Y!3+D4!2'_D#ET/g25;!2+Y!3+D4!2'_D#EW/g26;!3+D4!2'_D#EZ/g27;!2$R3;R!3+D4^9/g3;$H;R!2+Y!3+D4!2'_D#GM/g4;!2+Y!3+D4!2'_D#GO/g23;!2+Y!3+D4!2'_D#GR/g24;!2+Y!3+D4!2'_D#GT/g25;!2+Y!3+D4!2'_D#GW/g26;!3+D4!2'_D#GZ/g27;!5'_C^:!2+Y!3+D4!2'_D#HO/g23;!2+Y!3+D4!2'_D#HR/g24;!2+Y!3+D4!2'_D#HT/g25;!2+Y!3+D4!2'_D#HW/g26;!3+D4!2'_D#HZ/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#H\#G^0/model;/K;$~R^:$~R!2+Y!3+D4!2'_D#IO/g23;!2+Y!3+D4!2'_D#IR/g24;!2+Y!3+D4!2'_D#IT/g25;!2+Y!3+D4!2'_D#IW/g26;!3+D4!2'_D#IZ/g27;!2$R4;R!3+D4^;/g4;$H;R!2+Y!3+D4!2'_D#KO/g23;!2+Y!3+D4!2'_D#KR/g24;!2+Y!3+D4!2'_D#KT/g25;!2+Y!3+D4!2'_D#KW/g26;!3+D4!2'_D#KZ/g27;!5'_C^<!2+Y!3+D4!2'_D#LR/g24;!2+Y!3+D4!2'_D#LT/g25;!2+Y!3+D4!2'_D#LW/g26;!3+D4!2'_D#LZ/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#L\#K^0/model;/K;$~R^<$~R!2+Y!3+D4!2'_D#MR/g24;!2+Y!3+D4!2'_D#MT/g25;!2+Y!3+D4!2'_D#MW/g26;!3+D4!2'_D#MZ/g27;!2$R23;R!3+D4^=/g23;$H;R!2+Y!3+D4!2'_D#OR/g24;!2+Y!3+D4!2'_D#OT/g25;!2+Y!3+D4!2'_D#OW/g26;!3+D4!2'_D#OZ/g27;!5'_C^>!2+Y!3+D4!2'_D#PT/g25;!2+Y!3+D4!2'_D#PW/g26;!3+D4!2'_D#PZ/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#P\#O^0/model;/K;$~R^>$~R!2+Y!3+D4!2'_D#QT/g25;!2+Y!3+D4!2'_D#QW/g26;!3+D4!2'_D#QZ/g27;!2$R24;R!3+D4^?/g24;$H;R!2+Y!3+D4!2'_D#ST/g25;!2+Y!3+D4!2'_D#SW/g26;!3+D4!2'_D#SZ/g27;!5'_C^@!2+Y!3+D4!2'_D#TW/g26;!3+D4!2'_D#TZ/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#T\#S^0/model;/K;$~R^@$~R!2+Y!3+D4!2'_D#UW/g26;!3+D4!2'_D#UZ/g27;!2$R25;R!3+D4^A/g25;$H;R!2+Y!3+D4!2'_D#WW/g26;!3+D4!2'_D#WZ/g27;!5'_C^B!3+D4!2'_D#XZ/g27;!4+2'3/scfg;!2,`1!5'`2/fx;#X\#W^0/model;/K;$~R^B$~R!3+D4!2'_D#YZ/g27;!2$R26;R!3+D4^C/g26;$R27;R!3+D4!2'_D#[Z/g27;&e;R!W'`4/fx;#\#[^0/su;/f;/l;/bufp;/bufsz;/can;/ret;/e8;/e9;/e18;/e19;/e20;/e21;/e22;#V#R#N#J/SUlo;/SUhi;/Flo;/Fhi;/Hret;!8'`5#[^E^F!2'_R^F/ret;#Y/M8;!6'B+G^D^K!4'E!2'T^L^J!2'T^M^J!<'L+G+G'T^N'T^O^L^M^R^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G_7,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^X_<=^J_=_>_G!6'B+G^D_L!4'E!2+X_M_N!2+X_O_N!6'`6_M_N_O_N!<'L+G+G'T^N'T^O^L^M^R_I_I_P!1'_V_N&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+G_7,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^L_6,^H_9_:%__x1;R+G!2+X!2'T!2'^X_T=_U!2'T_V_T_W_>_G!8'`5#[_[^F!2'_R^F/e8;#Y/M16;!6'B+G_Z^K!4'E!2'T_\^J!2'T`0^J!<'L+G+G'T^N'T^O_\`0`1^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G`3,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^X`4=^J_=`5`6!6'B+G_Z_L!4'E!2+X`7`8!2+X`9`8!6'`6`7`8`9`8!<'L+G+G'T^N'T^O_\`0`1_I_I_P!1'_V`8&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+G`3,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^L`2,^H_9_:%__x1;R+G!2+X!2'T!2'^X`:=_U!2'T_V`:_W`5`6!8'`5#[`<^F!2'_R^F/e9;#Y/M24;!6'B+G`;^K!4'E!2'T`=^J!2'T`>^J!<'L+G+G'T^N'T^O`=`>`?^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G`A,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^X`B=^J_=`C`D!6'B+G`;_L!4'E!2+X`E`F!2+X`G`F!6'`6`E`F`G`F!<'L+G+G'T^N'T^O`=`>`?_I_I_P!1'_V`F&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+G`A,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^L`@,^H_9_:%__x1;R+G!2+X!2'T!2'^X`H=_U!2'T_V`H_W`C`D!8'`5#[`L^F!2'_R^F/e18;#Y/M32;!6'B+G`K^K!4'E!2'T`M^J!2'T`N^J!<'L+G+G'T^N'T^O`M`N`O^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+G`Q,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^X`R=^J_=`S`T!6'B+G`K_L!4'E!2+X`U`V!2+X`W`V!6'`6`U`V`W`V!<'L+G+G'T^N'T^O`M`N`O_I_I_P!1'_V`V&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+G`Q,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^L`P,^H_9_:%__x1;R+G!2+X!2'T!2'^X`X=_U!2'T_V`X_W`S`T!8'`5#[`[^F!2'_R^F/e19;#Y/M40;!6'B+G`Z^K!4'E!2'T`\^J!2'Ta0^J!<'L+G+G'T^N'T^O`\a0a1^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+Ga3,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^Xa4=^J_=a5a6!6'B+G`Z_L!4'E!2+Xa7a8!2+Xa9a8!6'`6a7a8a9a8!<'L+G+G'T^N'T^O`\a0a1_I_I_P!1'_Va8&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+Ga3,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^La2,^H_9_:%__x1;R+G!2+X!2'T!2'^Xa:=_U!2'T_Va:_Wa5a6!8'`5#[a>^F!2'_R^F/e20;#Y/M48;!6'B+Ga=^K!4'E!2'Ta?^J!2'Ta@^J!<'L+G+G'T^N'T^Oa?a@aA^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+GaC,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^XaD=^J_=aEaF!6'B+Ga=_L!4'E!2+XaGaH!2+XaIaH!6'`6aGaHaIaH!<'L+G+G'T^N'T^Oa?a@aA_I_I_P!1'_VaH&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+GaC,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^LaB,^H_9_:%__x1;R+G!2+X!2'T!2'^XaJ=_U!2'T_VaJ_WaEaF!8'`5#[aN^F!2'_R^F/e21;#Y/M56;!6'B+GaM^K!4'E!2'TaO^J!2'TaP^J!<'L+G+G'T^N'T^OaOaPaQ^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+GaS,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^XaT=^J_=aUaV!6'B+GaM_L!4'E!2+XaWaX!2+XaYaX!6'`6aWaXaYaX!<'L+G+G'T^N'T^OaOaPaQ_I_I_P!1'_VaX&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+GaS,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^LaR,^H_9_:%__x1;R+G!2+X!2'T!2'^XaZ=_U!2'T_VaZ_WaUaV!8'`5#[a\^F!2'_R^F/e22;#Y/M64;!6'B+Ga[^K!4'E!2'Tb0^J!2'Tb1^J!<'L+G+G'T^N'T^Ob0b1b2^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+Gb4,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^Xb5=^J_=b6b7!6'B+Ga[_L!4'E!2+Xb8b9!2+Xb:b9!6'`6b8b9b:b9!<'L+G+G'T^N'T^Ob0b1b2_I_I_P!1'_Vb9&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+Gb4,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^Lb3,^H_9_:%__x1;R+G!2+X!2'T!2'^Xb;=_U!2'T_Vb;_Wb6b7!8'`5#[b<^Fb=#Y/M72;!6'B+G_K^K!4'E!2'Tb>^J!2'Tb?^J!<'L+G+G'T^N'T^Ob>b?b@^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_3_4!7,^B_0'^=+^>+^>,^?!4,^C+GbA,^L_8,^H_9_:%__x1;R+G%~R_;!2'T!2'^XbB=^J_=bCbD!6'B+G_K_L!4'E!2+XbEbF!2+XbGbF!6'`6bEbFbGbF!<'L+G+G'T^N'T^Ob>b?b@_I_I_P!1'_VbF&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+GbA,^L_R,^H!7,^B_0'^=+^>+^>,^?!4,^C+G_S,^L_S,^H_9_:%__x1;R+G!2+X!2'T!2'^X_V=_U!2'T_V_V_WbCbD!8'`5#[G^Fb=#Y/Mcan;!6'B+GF^K!4'E!2'TbH^JbJ!<'L+G+G'T^N'T^ObHbIbK^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R&__wit;R^Y^Z&__varmap;RbL^\&__ff;R!7,^B_0'^=+^>+^>,^?!4,^C+GbN,^L_8,^H_9_:bJ#1bObP!6'B+GF_L!4'E!2+XbQbR!2+XbSbR!6'`6bQbRbSbR!<'L+G+G'T^N'T^ObHbIbK_I_I_P!3'`7bRbR!2,OwbR&__arith;R$__p1;Rw$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?_B_4!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+GbN,^L_R,^H!6,^I_0'^=+^>+^>,^?#4_9_:%__p1;Rw%__x1;R+G%~R_E!2+X!2'TbI!2'J#2_H#3!3#1bR/su;/SUlo;bObP!8'`5#[bV^F!2'_R^F/bufp;#Y/Mbuf;!6'B+GbU^K!4'E!2'TbW^J!2'TbX^J!<'L+G+G'T^N'T^ObWbXbY^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?b[_4!7,^B_0'^=+^>+^>,^?!4,^C+Gc0,^L_8,^H_9_:%__x1;R+G%~Rc1!2'T!2'^Xc2=^Jc3c4c9!6'B+GbU_L!4'E!2+Xc:c;!2+Xc<c;!6'`6c:c;c<c;!<'L+G+G'T^N'T^ObWbXbY_I_I_P!1'_Vc;&__arith;R$__p1;Rw$__x2;R+G$__x1;R+G&__wit;Rc?^Z&__varmap;Rc@^\&__ff;R!8,^;_0'^=+^>+^>,^?b[_4!8,^;_0'^=+^>+^>,^?cB_4!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+Gc0,^LcC,^HcD_9_:%__p1;Rw%__x2;R+G%__x1;R+G%~Rc1%~RcE!2+X!2'T!2'^X!2'^X#3bT=cF#5!5#1c;/su;/f;/Fhi;/SUlo;c4c9!8'`5#[cI^F!2'_R^F/bufsz;#Y/Mbsz;!6'B+GcH^K!4'E!2'TcJ^J!2'TcK^J!<'L+G+G'T^N'T^OcJcKcL^J^J^S&__sat74;R^T^U&__sat73;R^W^X&__arith;R$__x1;R+G&__wit;R^Y^Z&__varmap;R^[^\&__ff;R!8,^;_0'^=+^>+^>,^?b[_4!7,^B_0'^=+^>+^>,^?!4,^C+GcN,^L_8,^H_9_:%__x1;R+G%~Rc1!2'T!2'^XcO=^Jc3cPcQ!6'B+GcH_L!4'E!2+XcRcS!2+XcTcS!6'`6cRcScTcS!<'L+G+G'T^N'T^OcJcKcL_I_I_P!1'_VcS&__arith;R$__p1;Rw$__x2;R+G$__x1;R+G&__wit;Rc?^Z&__varmap;Rc@^\&__ff;R!8,^;_0'^=+^>+^>,^?b[_4!8,^;_0'^=+^>+^>,^?cB_4!7,^@_0'^=+^>+^>,^?!7,^B_0'^=+^>+^>,^?!4,^C+GcN,^LcC,^HcD_9_:%__p1;Rw%__x2;R+G%__x1;R+G%~Rc1%~RcE!2+X!2'T!2'^X!2'^X#3cG=cF#5!5#1cS/su;/f;/Fhi;/SUlo;cPcQ!2+`85$regs';R5!2+Y!3+`9'3!5'`2/fx;#^0vd!3,_E3[vv,_F!2'`:3[4#\^0!5'`2/fx;#1/ret;!4'`;#\/f;/bufp;/bufsz;^0!2+Y!3+D4!2'_D#1!3,_E1cVvv,_F!2'`:1cV/l;!2+Y!3+D4!2'_D#1!3,_E18vv,_F!2'`:18cW!2+Y!3+D4!2'_D#1!3,_E1cXvv,_F!2'`:1cX/ret;!2+Y!3+D4!2'_D#1!3,_E1=vv,_F!2'`:1=/e8;!2+Y!3+D4!2'_D#1!3,_E1@vv,_F!2'`:1@/e9;!2+Y!3+D4!2'_D#1!3,_E1cZvv,_F!2'`:1cZ/e18;!2+Y!3+D4!2'_D#1!3,_E1c[vv,_F!2'`:1c[/e19;!2+Y!3+D4!2'_D#1!3,_E1d0vv,_F!2'`:1d0/e20;!2+Y!3+D4!2'_D#1!3,_E1Dvv,_F!2'`:1D/e21;!2+Y!3+D4!2'_D#1!3,_E1d2vv,_F!2'`:1d2/e22;!2+Y!3+D4!2'_D#1d3!2'_D#^0d3!2+Y!3+D4!2'_D#1d4!2'_D#^0d4!2+Y!3+D4!2'_D#1d5!2'_D#^0d5!2+Y!3+D4!2'_D#1d6!2'_D#^0d6!2+Y!3+D4!2'_D#1d7!2'_D#^0d7!2+Y!3+D4!2'_D#1d8!2'_D#^0d8!3+D4!2'_D#1d9!2'_D#^0d9-`8RN$~R!2+`85$regs';R5!2+Y!3+`9'3d:!5'`2/fx;#1/ret;!4'`;#^0/f;/bufp;/bufsz;^0!2+Yd<!2+Yd=!2+Yd?!2+Yd@!2+YdA!2+YdC!2+YdE!2+YdG!2+YdH!2+YdJ!2+Y!3+D4dKdL!2+Y!3+D4dMdN!2+Y!3+D4dOdP!2+Y!3+D4dQdR!2+Y!3+D4dSdT!2+Y!3+D4dUdV!3+D4dWdX!4+2'3/scfg;!2,`1d:/model;/K;#11$x;R5$~R!1$regs';R5!2+Y!3+`9'3!5'`2/fx;#^2\#^1^0!5'`2/fx;#1/ret;!4'`;#^1/f;/bufp;/bufsz;^0!2+Yd<!2+Yd=!2+Yd?!2+Yd@!2+YdA!2+YdC!2+YdE!2+YdG!2+YdH!2+YdJ!2+Y!3+D4dK!2'_D#^2J!2+Y!3+D4dM!2'_D#^2M!2+Y!3+D4dO!2'_D#^2O!2+Y!3+D4dQ!2'_D#^2R!2+Y!3+D4dS!2'_D#^2T!2+Y!3+D4dU!2'_D#^2W!3+D4dW!2'_D#^2Z#1!2$regs2;R5$H;R!2+Y!3+`9'3!5'`2/fx;#^3\#^2^0!5'`2/fx;#1/ret;!4'`;#^2/f;/bufp;/bufsz;^0!2+Yd<!2+Yd=!2+Yd?!2+Yd@!2+YdA!2+YdC!2+YdE!2+YdG!2+YdH!2+YdJ!2+Y!3+D4dKdY!2+Y!3+D4dM!2'_D#^3M!2+Y!3+D4dO!2'_D#^3O!2+Y!3+D4dQ!2'_D#^3R!2+Y!3+D4dS!2'_D#^3T!2+Y!3+D4dU!2'_D#^3W!3+D4dW!2'_D#^3Z!5'_CdZ!2+Y!3+D4!2'_D#2d;/l;!2+Y!3+D4!2'_D#29cW!2+Y!3+D4!2'_D#2d>/ret;!2+Y!3+D4!2'_D#2>/e8;!2+Y!3+D4!2'_D#2A/e9;!2+Y!3+D4!2'_D#2dB/e18;!2+Y!3+D4!2'_D#2dD/e19;!2+Y!3+D4!2'_D#2dF/e20;!2+Y!3+D4!2'_D#2E/e21;!2+Y!3+D4!2'_D#2dI/e22;!2+Y!3+D4!2'_D#2J!2'_D#^4J!2+Y!3+D4!2'_D#2Md[!2+Y!3+D4!2'_D#2Od\!2+Y!3+D4!2'_D#2Re0!2+Y!3+D4!2'_D#2Te1!2+Y!3+D4!2'_D#2We2!3+D4!2'_D#2Ze3!4+2'3/scfg;!2,`1!5'`2/fx;#^4\#^3^0/model;/K;$~RdZ$~R!2+Y!3+D4!2'_D#3d;/l;!2+Y!3+D4!2'_D#39cW!2+Y!3+D4!2'_D#3d>/ret;!2+Y!3+D4!2'_D#3>/e8;!2+Y!3+D4!2'_D#3A/e9;!2+Y!3+D4!2'_D#3dB/e18;!2+Y!3+D4!2'_D#3dD/e19;!2+Y!3+D4!2'_D#3dF/e20;!2+Y!3+D4!2'_D#3E/e21;!2+Y!3+D4!2'_D#3dI/e22;!2+Y!3+D4!2'_D#3J!2'_D#^5J!2+Y!3+D4!2'_D#3M!2'_D#^5M!2+Y!3+D4!2'_D#3O!2'_D#^5O!2+Y!3+D4!2'_D#3R!2'_D#^5R!2+Y!3+D4!2'_D#3T!2'_D#^5T!2+Y!3+D4!2'_D#3W!2'_D#^5W!3+D4!2'_D#3Z!2'_D#^5Z!2$RUN;R!3+`9'3!5'`2/fx;#^6\#^5^0!5'`2/fx;#4/ret;!4'`;#^5/f;/bufp;/bufsz;^0$H;R!2+Y!3+D4!2'_D#5d;/l;!2+Y!3+D4!2'_D#59cW!2+Y!3+D4!2'_D#5d>/ret;!2+Y!3+D4!2'_D#5>/e8;!2+Y!3+D4!2'_D#5A/e9;!2+Y!3+D4!2'_D#5dB/e18;!2+Y!3+D4!2'_D#5dD/e19;!2+Y!3+D4!2'_D#5dF/e20;!2+Y!3+D4!2'_D#5E/e21;!2+Y!3+D4!2'_D#5dI/e22;!2+Y!3+D4!2'_D#5J!2'_D#^7J!2+Y!3+D4!2'_D#5Me4!2+Y!3+D4!2'_D#5O!2'_D#^7O!2+Y!3+D4!2'_D#5R!2'_D#^7R!2+Y!3+D4!2'_D#5T!2'_D#^7T!2+Y!3+D4!2'_D#5W!2'_D#^7W!3+D4!2'_D#5Z!2'_D#^7Z!5'_Ce5!2+Y!3+D4^1cW!2+Y!3+D4!2'_D#6d>/ret;!2+Y!3+D4!2'_D#6>/e8;!2+Y!3+D4!2'_D#6A/e9;!2+Y!3+D4!2'_D#6dB/e18;!2+Y!3+D4!2'_D#6dD/e19;!2+Y!3+D4!2'_D#6dF/e20;!2+Y!3+D4!2'_D#6E/e21;!2+Y!3+D4!2'_D#6dI/e22;!2+Y!3+D4!2'_D#6J!2'_D#^8J!2+Y!3+D4!2'_D#6M!2'_D#^8M!2+Y!3+D4!2'_D#6Oe6!2+Y!3+D4!2'_D#6Re7!2+Y!3+D4!2'_D#6Te8!2+Y!3+D4!2'_D#6We9!3+D4!2'_D#6Ze:!4+2'3/scfg;!2,`1!5'`2/fx;#^8\#^7^0/model;/K;$~Re5$~R!2+Y!3+D4!2'_D#79cW!2+Y!3+D4!2'_D#7d>/ret;!2+Y!3+D4!2'_D#7>/e8;!2+Y!3+D4!2'_D#7A/e9;!2+Y!3+D4!2'_D#7dB/e18;!2+Y!3+D4!2'_D#7dD/e19;!2+Y!3+D4!2'_D#7dF/e20;!2+Y!3+D4!2'_D#7E/e21;!2+Y!3+D4!2'_D#7dI/e22;!2+Y!3+D4!2'_D#7J!2'_D#^9J!2+Y!3+D4!2'_D#7M!2'_D#^9M!2+Y!3+D4!2'_D#7O!2'_D#^9O!2+Y!3+D4!2'_D#7R!2'_D#^9R!2+Y!3+D4!2'_D#7T!2'_D#^9T!2+Y!3+D4!2'_D#7W!2'_D#^9W!3+D4!2'_D#7Z!2'_D#^9Z!2$Q10;R!3+D4!2'_D#8d;/l;$H;R!2+Y!3+D4!2'_D#99cW!2+Y!3+D4!2'_D#9d>/ret;!2+Y!3+D4!2'_D#9>/e8;!2+Y!3+D4!2'_D#9A/e9;!2+Y!3+D4!2'_D#9dB/e18;!2+Y!3+D4!2'_D#9dD/e19;!2+Y!3+D4!2'_D#9dF/e20;!2+Y!3+D4!2'_D#9E/e21;!2+Y!3+D4!2'_D#9dI/e22;!2+Y!3+D4!2'_D#9J!2'_D#^;J!2+Y!3+D4!2'_D#9M!2'_D#^;M!2+Y!3+D4!2'_D#9Oe;!2+Y!3+D4!2'_D#9R!2'_D#^;R!2+Y!3+D4!2'_D#9T!2'_D#^;T!2+Y!3+D4!2'_D#9W!2'_D#^;W!3+D4!2'_D#9Z!2'_D#^;Z!5'_Ce<!2+Y!3+D4!2'_D#:d>/ret;!2+Y!3+D4^3/e8;!2+Y!3+D4!2'_D#:A/e9;!2+Y!3+D4!2'_D#:dB/e18;!2+Y!3+D4!2'_D#:dD/e19;!2+Y!3+D4!2'_D#:dF/e20;!2+Y!3+D4!2'_D#:E/e21;!2+Y!3+D4!2'_D#:dI/e22;!2+Y!3+D4!2'_D#:J!2'_D#^<J!2+Y!3+D4!2'_D#:M!2'_D#^<M!2+Y!3+D4!2'_D#:O!2'_D#^<O!2+Y!3+D4!2'_D#:Re=!2+Y!3+D4!2'_D#:Te>!2+Y!3+D4!2'_D#:We?!3+D4!2'_D#:Ze@!4+2'3/scfg;!2,`1!5'`2/fx;#^<\#^;^0/model;/K;$~Re<$~R!2+Y!3+D4!2'_D#;d>/ret;!2+Y!3+D4!2'_D#;>/e8;!2+Y!3+D4!2'_D#;A/e9;!2+Y!3+D4!2'_D#;dB/e18;!2+Y!3+D4!2'_D#;dD/e19;!2+Y!3+D4!2'_D#;dF/e20;!2+Y!3+D4!2'_D#;E/e21;!2+Y!3+D4!2'_D#;dI/e22;!2+Y!3+D4!2'_D#;J!2'_D#^=J!2+Y!3+D4!2'_D#;M!2'_D#^=M!2+Y!3+D4!2'_D#;O!2'_D#^=O!2+Y!3+D4!2'_D#;R!2'_D#^=R!2+Y!3+D4!2'_D#;T!2'_D#^=T!2+Y!3+D4!2'_D#;W!2'_D#^=W!3+D4!2'_D#;Z!2'_D#^=Z!2$Q2;R!3+D4!2'_D#<9cW$H;R!2+Y!3+D4!2'_D#=d>/ret;!2+Y!3+D4!2'_D#=>/e8;!2+Y!3+D4!2'_D#=A/e9;!2+Y!3+D4!2'_D#=dB/e18;!2+Y!3+D4!2'_D#=dD/e19;!2+Y!3+D4!2'_D#=dF/e20;!2+Y!3+D4!2'_D#=E/e21;!2+Y!3+D4!2'_D#=dI/e22;!2+Y!3+D4!2'_D#=J!2'_D#^?J!2+Y!3+D4!2'_D#=M!2'_D#^?M!2+Y!3+D4!2'_D#=O!2'_D#^?O!2+Y!3+D4!2'_D#=ReA!2+Y!3+D4!2'_D#=T!2'_D#^?T!2+Y!3+D4!2'_D#=W!2'_D#^?W!3+D4!2'_D#=Z!2'_D#^?Z!5'_CeB!2+Y!3+D4!2'_D#>>/e8;!2+Y!3+D4^5/e9;!2+Y!3+D4!2'_D#>dB/e18;!2+Y!3+D4!2'_D#>dD/e19;!2+Y!3+D4!2'_D#>dF/e20;!2+Y!3+D4!2'_D#>E/e21;!2+Y!3+D4!2'_D#>dI/e22;!2+Y!3+D4!2'_D#>J!2'_D#^@J!2+Y!3+D4!2'_D#>M!2'_D#^@M!2+Y!3+D4!2'_D#>O!2'_D#^@O!2+Y!3+D4!2'_D#>R!2'_D#^@R!2+Y!3+D4!2'_D#>TeC!2+Y!3+D4!2'_D#>WeD!3+D4!2'_D#>ZeE!4+2'3/scfg;!2,`1!5'`2/fx;#^@\#^?^0/model;/K;$~ReB$~R!2+Y!3+D4!2'_D#?>/e8;!2+Y!3+D4!2'_D#?A/e9;!2+Y!3+D4!2'_D#?dB/e18;!2+Y!3+D4!2'_D#?dD/e19;!2+Y!3+D4!2'_D#?dF/e20;!2+Y!3+D4!2'_D#?E/e21;!2+Y!3+D4!2'_D#?dI/e22;!2+Y!3+D4!2'_D#?J!2'_D#^AJ!2+Y!3+D4!2'_D#?M!2'_D#^AM!2+Y!3+D4!2'_D#?O!2'_D#^AO!2+Y!3+D4!2'_D#?R!2'_D#^AR!2+Y!3+D4!2'_D#?T!2'_D#^AT!2+Y!3+D4!2'_D#?W!2'_D#^AW!3+D4!2'_D#?Z!2'_D#^AZ!2$Q1;R!3+D4!2'_D#@d>/ret;$H;R!2+Y!3+D4!2'_D#A>/e8;!2+Y!3+D4!2'_D#AA/e9;!2+Y!3+D4!2'_D#AdB/e18;!2+Y!3+D4!2'_D#AdD/e19;!2+Y!3+D4!2'_D#AdF/e20;!2+Y!3+D4!2'_D#AE/e21;!2+Y!3+D4!2'_D#AdI/e22;!2+Y!3+D4!2'_D#AJ!2'_D#^CJ!2+Y!3+D4!2'_D#AM!2'_D#^CM!2+Y!3+D4!2'_D#AO!2'_D#^CO!2+Y!3+D4!2'_D#AR!2'_D#^CR!2+Y!3+D4!2'_D#ATeF!2+Y!3+D4!2'_D#AW!2'_D#^CW!3+D4!2'_D#AZ!2'_D#^CZ!5'_CeG!2+Y!3+D4!2'_D#BA/e9;!2+Y!3+D4!2'_D#BdB/e18;!2+Y!3+D4!2'_D#BdD/e19;!2+Y!3+D4!2'_D#BdF/e20;!2+Y!3+D4^7/e21;!2+Y!3+D4!2'_D#BdI/e22;!2+Y!3+D4!2'_D#BJ!2'_D#^DJ!2+Y!3+D4!2'_D#BM!2'_D#^DM!2+Y!3+D4!2'_D#BO!2'_D#^DO!2+Y!3+D4!2'_D#BR!2'_D#^DR!2+Y!3+D4!2'_D#BT!2'_D#^DT!2+Y!3+D4!2'_D#BWeH!3+D4!2'_D#BZeI!4+2'3/scfg;!2,`1!5'`2/fx;#^D\#^C^0/model;/K;$~ReG$~R!2+Y!3+D4!2'_D#CA/e9;!2+Y!3+D4!2'_D#CdB/e18;!2+Y!3+D4!2'_D#CdD/e19;!2+Y!3+D4!2'_D#CdF/e20;!2+Y!3+D4!2'_D#CE/e21;!2+Y!3+D4!2'_D#CdI/e22;!2+Y!3+D4!2'_D#CJ!2'_D#^EJ!2+Y!3+D4!2'_D#CM!2'_D#^EM!2+Y!3+D4!2'_D#CO!2'_D#^EO!2+Y!3+D4!2'_D#CR!2'_D#^ER!2+Y!3+D4!2'_D#CT!2'_D#^ET!2+Y!3+D4!2'_D#CW!2'_D#^EW!3+D4!2'_D#CZ!2'_D#^EZ!2$Q8;R!3+D4!2'_D#D>/e8;$H;R!2+Y!3+D4!2'_D#EA/e9;!2+Y!3+D4!2'_D#EdB/e18;!2+Y!3+D4!2'_D#EdD/e19;!2+Y!3+D4!2'_D#EdF/e20;!2+Y!3+D4!2'_D#EE/e21;!2+Y!3+D4!2'_D#EdI/e22;!2+Y!3+D4!2'_D#EJ!2'_D#^GJ!2+Y!3+D4!2'_D#EM!2'_D#^GM!2+Y!3+D4!2'_D#EO!2'_D#^GO!2+Y!3+D4!2'_D#ER!2'_D#^GR!2+Y!3+D4!2'_D#ET!2'_D#^GT!2+Y!3+D4!2'_D#EWeJ!3+D4!2'_D#EZ!2'_D#^GZ!5'_CeK!2+Y!3+D4!2'_D#FdB/e18;!2+Y!3+D4!2'_D#FdD/e19;!2+Y!3+D4!2'_D#FdF/e20;!2+Y!3+D4!2'_D#FE/e21;!2+Y!3+D4!2'_D#FdI/e22;!2+Y!3+D4^9!2'_D#^HJ!2+Y!3+D4!2'_D#FM!2'_D#^HM!2+Y!3+D4!2'_D#FO!2'_D#^HO!2+Y!3+D4!2'_D#FR!2'_D#^HR!2+Y!3+D4!2'_D#FT!2'_D#^HT!2+Y!3+D4!2'_D#FW!2'_D#^HW!3+D4!2'_D#FZeL!4+2'3/scfg;!2,`1!5'`2/fx;#^H\#^G^0/model;/K;$~ReK$~R!2+Y!3+D4!2'_D#GdB/e18;!2+Y!3+D4!2'_D#GdD/e19;!2+Y!3+D4!2'_D#GdF/e20;!2+Y!3+D4!2'_D#GE/e21;!2+Y!3+D4!2'_D#GdI/e22;!2+Y!3+D4!2'_D#GJ!2'_D#^IJ!2+Y!3+D4!2'_D#GM!2'_D#^IM!2+Y!3+D4!2'_D#GO!2'_D#^IO!2+Y!3+D4!2'_D#GR!2'_D#^IR!2+Y!3+D4!2'_D#GT!2'_D#^IT!2+Y!3+D4!2'_D#GW!2'_D#^IW!3+D4!2'_D#GZ!2'_D#^IZ!2$Q9;R!3+D4!2'_D#HA/e9;$H;R!2+Y!3+D4!2'_D#IdB/e18;!2+Y!3+D4!2'_D#IdD/e19;!2+Y!3+D4!2'_D#IdF/e20;!2+Y!3+D4!2'_D#IE/e21;!2+Y!3+D4!2'_D#IdI/e22;!2+Y!3+D4!2'_D#IJ!2'_D#^KJ!2+Y!3+D4!2'_D#IM!2'_D#^KM!2+Y!3+D4!2'_D#IO!2'_D#^KO!2+Y!3+D4!2'_D#IR!2'_D#^KR!2+Y!3+D4!2'_D#IT!2'_D#^KT!2+Y!3+D4!2'_D#IW!2'_D#^KW!3+D4!2'_D#IZ!2'_D#^KZ!5'_CeM!2+Y!3+D4!2'_D#JdD/e19;!2+Y!3+D4!2'_D#JdF/e20;!2+Y!3+D4!2'_D#JE/e21;!2+Y!3+D4!2'_D#JdI/e22;!2+Y!3+D4!2'_D#JJ!2'_D#^LJ!2+Y!3+D4^;!2'_D#^LM!2+Y!3+D4!2'_D#JO!2'_D#^LO!2+Y!3+D4!2'_D#JR!2'_D#^LR!2+Y!3+D4!2'_D#JT!2'_D#^LT!2+Y!3+D4!2'_D#JW!2'_D#^LW!3+D4!2'_D#JZ!2'_D#^LZ!4+2'3/scfg;!2,`1!5'`2/fx;#^L\#^K^0/model;/K;$~ReM$~R!2+Y!3+D4!2'_D#KdD/e19;!2+Y!3+D4!2'_D#KdF/e20;!2+Y!3+D4!2'_D#KE/e21;!2+Y!3+D4!2'_D#KdI/e22;!2+Y!3+D4!2'_D#KJ!2'_D#^MJ!2+Y!3+D4!2'_D#KM!2'_D#^MM!2+Y!3+D4!2'_D#KO!2'_D#^MO!2+Y!3+D4!2'_D#KR!2'_D#^MR!2+Y!3+D4!2'_D#KT!2'_D#^MT!2+Y!3+D4!2'_D#KW!2'_D#^MW!3+D4!2'_D#KZ!2'_D#^MZ!2$Q18;R!3+D4!2'_D#LdB/e18;$H;R!2+Y!3+D4!2'_D#MdD/e19;!2+Y!3+D4!2'_D#MdF/e20;!2+Y!3+D4!2'_D#ME/e21;!2+Y!3+D4!2'_D#MdI/e22;!2+Y!3+D4!2'_D#MJ!2'_D#^OJ!2+Y!3+D4!2'_D#MM!2'_D#^OM!2+Y!3+D4!2'_D#MO!2'_D#^OO!2+Y!3+D4!2'_D#MR!2'_D#^OR!2+Y!3+D4!2'_D#MT!2'_D#^OT!2+Y!3+D4!2'_D#MW!2'_D#^OW!3+D4!2'_D#MZ!2'_D#^OZ!5'_CeN!2+Y!3+D4!2'_D#NdF/e20;!2+Y!3+D4!2'_D#NE/e21;!2+Y!3+D4!2'_D#NdI/e22;!2+Y!3+D4!2'_D#NJ!2'_D#^PJ!2+Y!3+D4!2'_D#NM!2'_D#^PM!2+Y!3+D4^=!2'_D#^PO!2+Y!3+D4!2'_D#NR!2'_D#^PR!2+Y!3+D4!2'_D#NT!2'_D#^PT!2+Y!3+D4!2'_D#NW!2'_D#^PW!3+D4!2'_D#NZ!2'_D#^PZ!4+2'3/scfg;!2,`1!5'`2/fx;#^P\#^O^0/model;/K;$~ReN$~R!2+Y!3+D4!2'_D#OdF/e20;!2+Y!3+D4!2'_D#OE/e21;!2+Y!3+D4!2'_D#OdI/e22;!2+Y!3+D4!2'_D#OJ!2'_D#^QJ!2+Y!3+D4!2'_D#OM!2'_D#^QM!2+Y!3+D4!2'_D#OO!2'_D#^QO!2+Y!3+D4!2'_D#OR!2'_D#^QR!2+Y!3+D4!2'_D#OT!2'_D#^QT!2+Y!3+D4!2'_D#OW!2'_D#^QW!3+D4!2'_D#OZ!2'_D#^QZ!2$Q19;R!3+D4!2'_D#PdD/e19;$H;R!2+Y!3+D4!2'_D#QdF/e20;!2+Y!3+D4!2'_D#QE/e21;!2+Y!3+D4!2'_D#QdI/e22;!2+Y!3+D4!2'_D#QJ!2'_D#^SJ!2+Y!3+D4!2'_D#QM!2'_D#^SM!2+Y!3+D4!2'_D#QO!2'_D#^SO!2+Y!3+D4!2'_D#QR!2'_D#^SR!2+Y!3+D4!2'_D#QT!2'_D#^ST!2+Y!3+D4!2'_D#QW!2'_D#^SW!3+D4!2'_D#QZ!2'_D#^SZ!5'_CeO!2+Y!3+D4!2'_D#RE/e21;!2+Y!3+D4!2'_D#RdI/e22;!2+Y!3+D4!2'_D#RJ!2'_D#^TJ!2+Y!3+D4!2'_D#RM!2'_D#^TM!2+Y!3+D4!2'_D#RO!2'_D#^TO!2+Y!3+D4^?!2'_D#^TR!2+Y!3+D4!2'_D#RT!2'_D#^TT!2+Y!3+D4!2'_D#RW!2'_D#^TW!3+D4!2'_D#RZ!2'_D#^TZ!4+2'3/scfg;!2,`1!5'`2/fx;#^T\#^S^0/model;/K;$~ReO$~R!2+Y!3+D4!2'_D#SE/e21;!2+Y!3+D4!2'_D#SdI/e22;!2+Y!3+D4!2'_D#SJ!2'_D#^UJ!2+Y!3+D4!2'_D#SM!2'_D#^UM!2+Y!3+D4!2'_D#SO!2'_D#^UO!2+Y!3+D4!2'_D#SR!2'_D#^UR!2+Y!3+D4!2'_D#ST!2'_D#^UT!2+Y!3+D4!2'_D#SW!2'_D#^UW!3+D4!2'_D#SZ!2'_D#^UZ!2$Q20;R!3+D4!2'_D#TdF/e20;$H;R!2+Y!3+D4!2'_D#UE/e21;!2+Y!3+D4!2'_D#UdI/e22;!2+Y!3+D4!2'_D#UJ!2'_D#^WJ!2+Y!3+D4!2'_D#UM!2'_D#^WM!2+Y!3+D4!2'_D#UO!2'_D#^WO!2+Y!3+D4!2'_D#UR!2'_D#^WR!2+Y!3+D4!2'_D#UT!2'_D#^WT!2+Y!3+D4!2'_D#UW!2'_D#^WW!3+D4!2'_D#UZ!2'_D#^WZ!5'_CeP!2+Y!3+D4!2'_D#VdI/e22;!2+Y!3+D4!2'_D#VJ!2'_D#^XJ!2+Y!3+D4!2'_D#VM!2'_D#^XM!2+Y!3+D4!2'_D#VO!2'_D#^XO!2+Y!3+D4!2'_D#VR!2'_D#^XR!2+Y!3+D4^A!2'_D#^XT!2+Y!3+D4!2'_D#VW!2'_D#^XW!3+D4!2'_D#VZ!2'_D#^XZ!4+2'3/scfg;!2,`1!5'`2/fx;#^X\#^W^0/model;/K;$~ReP$~R!2+Y!3+D4!2'_D#WdI/e22;!2+Y!3+D4!2'_D#WJ!2'_D#^YJ!2+Y!3+D4!2'_D#WM!2'_D#^YM!2+Y!3+D4!2'_D#WO!2'_D#^YO!2+Y!3+D4!2'_D#WR!2'_D#^YR!2+Y!3+D4!2'_D#WT!2'_D#^YT!2+Y!3+D4!2'_D#WW!2'_D#^YW!3+D4!2'_D#WZ!2'_D#^YZ!2$Q21;R!3+D4!2'_D#XE/e21;$H;R!2+Y!3+D4!2'_D#YdI/e22;!2+Y!3+D4!2'_D#YJ!2'_D#^[J!2+Y!3+D4!2'_D#YM!2'_D#^[M!2+Y!3+D4!2'_D#YO!2'_D#^[O!2+Y!3+D4!2'_D#YR!2'_D#^[R!2+Y!3+D4!2'_D#YT!2'_D#^[T!2+Y!3+D4!2'_D#YW!2'_D#^[W!3+D4!2'_D#YZ!2'_D#^[Z!5'_CeQ!2+Y!3+D4!2'_D#ZJ!2'_D#^\J!2+Y!3+D4!2'_D#ZM!2'_D#^\M!2+Y!3+D4!2'_D#ZO!2'_D#^\O!2+Y!3+D4!2'_D#ZR!2'_D#^\R!2+Y!3+D4!2'_D#ZT!2'_D#^\T!2+Y!3+D4^C!2'_D#^\W!3+D4!2'_D#ZZ!2'_D#^\Z!4+2'3/scfg;!2,`1!5'`2/fx;#^\\#^[^0/model;/K;$~ReQ$~R!2+Y!3+D4!2'_D#[J!2'_D#_0J!2+Y!3+D4!2'_D#[M!2'_D#_0M!2+Y!3+D4!2'_D#[O!2'_D#_0O!2+Y!3+D4!2'_D#[R!2'_D#_0R!2+Y!3+D4!2'_D#[T!2'_D#_0T!2+Y!3+D4!2'_D#[W!2'_D#_0W!3+D4!2'_D#[Z!2'_D#_0Z!2$Q22;R!3+D4!2'_D#\dI/e22;$H;R!2+Y!3+D4!2'_D#^0J!2'_D#_2J!2+Y!3+D4!2'_D#^0M!2'_D#_2M!2+Y!3+D4!2'_D#^0O!2'_D#_2O!2+Y!3+D4!2'_D#^0R!2'_D#_2R!2+Y!3+D4!2'_D#^0T!2'_D#_2T!2+Y!3+D4!2'_D#^0W!2'_D#_2W!3+D4!2'_D#^0Z!2'_D#_2Z!5'_CeR!2+Y!3+D4dN!2'_D#_3M!2+Y!3+D4dP!2'_D#_3O!2+Y!3+D4dR!2'_D#_3R!2+Y!3+D4dT!2'_D#_3T!2+Y!3+D4dV!2'_D#_3W!3+D4dX!2'_D#_3Z!4+2'3/scfg;!2,`1!5'`2/fx;#_3\#_2^0/model;/K;$~ReR$~R!2+Y!3+D4!2'_D#^2M!2'_D#_4M!2+Y!3+D4!2'_D#^2O!2'_D#_4O!2+Y!3+D4!2'_D#^2R!2'_D#_4R!2+Y!3+D4!2'_D#^2T!2'_D#_4T!2+Y!3+D4!2'_D#^2W!2'_D#_4W!3+D4!2'_D#^2Z!2'_D#_4Z!2$Q3;R!3+D4dY!2'_D#_5J$H;R!2+Y!3+D4d[!2'_D#_6M!2+Y!3+D4d\!2'_D#_6O!2+Y!3+D4e0!2'_D#_6R!2+Y!3+D4e1!2'_D#_6T!2+Y!3+D4e2!2'_D#_6W!3+D4e3!2'_D#_6Z!5'_CeS!2+Y!3+D4!2'_D#^5O!2'_D#_7O!2+Y!3+D4!2'_D#^5R!2'_D#_7R!2+Y!3+D4!2'_D#^5T!2'_D#_7T!2+Y!3+D4!2'_D#^5W!2'_D#_7W!3+D4!2'_D#^5Z!2'_D#_7Z!4+2'3/scfg;!2,`1!5'`2/fx;#_7\#_6^0/model;/K;$~ReS$~R!2+Y!3+D4!2'_D#^6O!2'_D#_8O!2+Y!3+D4!2'_D#^6R!2'_D#_8R!2+Y!3+D4!2'_D#^6T!2'_D#_8T!2+Y!3+D4!2'_D#^6W!2'_D#_8W!3+D4!2'_D#^6Z!2'_D#_8Z!2$Q4;R!3+D4e4!2'_D#_9M$H;R!2+Y!3+D4e6!2'_D#_:O!2+Y!3+D4e7!2'_D#_:R!2+Y!3+D4e8!2'_D#_:T!2+Y!3+D4e9!2'_D#_:W!3+D4e:!2'_D#_:Z!5'_CeT!2+Y!3+D4!2'_D#^9R!2'_D#_;R!2+Y!3+D4!2'_D#^9T!2'_D#_;T!2+Y!3+D4!2'_D#^9W!2'_D#_;W!3+D4!2'_D#^9Z!2'_D#_;Z!4+2'3/scfg;!2,`1!5'`2/fx;#_;\#_:^0/model;/K;$~ReT$~R!2+Y!3+D4!2'_D#^:R!2'_D#_<R!2+Y!3+D4!2'_D#^:T!2'_D#_<T!2+Y!3+D4!2'_D#^:W!2'_D#_<W!3+D4!2'_D#^:Z!2'_D#_<Z!2$Q23;R!3+D4e;!2'_D#_=O$H;R!2+Y!3+D4e=!2'_D#_>R!2+Y!3+D4e>!2'_D#_>T!2+Y!3+D4e?!2'_D#_>W!3+D4e@!2'_D#_>Z!5'_CeU!2+Y!3+D4!2'_D#^=T!2'_D#_?T!2+Y!3+D4!2'_D#^=W!2'_D#_?W!3+D4!2'_D#^=Z!2'_D#_?Z!4+2'3/scfg;!2,`1!5'`2/fx;#_?\#_>^0/model;/K;$~ReU$~R!2+Y!3+D4!2'_D#^>T!2'_D#_@T!2+Y!3+D4!2'_D#^>W!2'_D#_@W!3+D4!2'_D#^>Z!2'_D#_@Z!2$Q24;R!3+D4eA!2'_D#_AR$H;R!2+Y!3+D4eC!2'_D#_BT!2+Y!3+D4eD!2'_D#_BW!3+D4eE!2'_D#_BZ!5'_CeV!2+Y!3+D4!2'_D#^AW!2'_D#_CW!3+D4!2'_D#^AZ!2'_D#_CZ!4+2'3/scfg;!2,`1!5'`2/fx;#_C\#_B^0/model;/K;$~ReV$~R!2+Y!3+D4!2'_D#^BW!2'_D#_DW!3+D4!2'_D#^BZ!2'_D#_DZ!2$Q25;R!3+D4eF!2'_D#_ET$H;R!2+Y!3+D4eH!2'_D#_FW!3+D4eI!2'_D#_FZ!5'_CeW!3+D4!2'_D#^EZ!2'_D#_GZ!4+2'3/scfg;!2,`1!5'`2/fx;#_G\#_F^0/model;/K;$~ReW$~R!3+D4!2'_D#^FZ!2'_D#_HZ!2$Q26;R!3+D4eJ!2'_D#_IW$Q27;R!3+D4eL!2'_D#_JZ!:'`<'3/scfg;!5'`2/fx;#_K\#_J^0!5'`2/fx;#^I/ret;!4'`;#_J/f;/bufp;/bufsz;^0/model;/K;/Hh;/Hlazy;#^E!D/HK;#^I#_J#^A#^=#^9#^5#^1#Z#V#R#N#J!6'B4!2'_D#_KO$b;R4!3+D4#1/g23;#^Z!2'_D#^IO#>!6'B4!2'_D#_KR$b;R4!3+D4#1/g24;#^V!2'_D#^IR#:!6'B4!2'_D#_KT$b;R4!3+D4#1/g25;#^R!2'_D#^IT#6!6'B4!2'_D#_KW$b;R4!3+D4#1/g26;#^N!2'_D#^IW#2!6'B4!2'_D#_KZ$b;R4!3+D4#1/g27;#^M!2'_D#^IZ#1!6'B4!2'_D#_KJ$b;R4!3+D4#1/g3;#_5!2'_D#^IJ#F!6'B4!2'_D#_KM$b;R4!3+D4#1/g4;#_1!2'_D#^IM#B#_H#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#1#2#1#2").
Qed.

  Lemma finish_nil_b : forall regs m,
    RI regs -> LM m ->
    SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs (0xaf260 : word) m (seg_rom RSEGS)) model) (t_emit [] K).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S40|21;!1,^W|600;!1+^V1|30;$regs;R!2'_A!1,^W02$m;R%~R2!1+_H!1+^V!1,^W3$~R!1'_B#2$~R!1'_K#2!3'`=!2,`1!5'`2/fx;#4!3,_E1!1,^[|C2f260;,_F#3!1'`3'3/model;/K;!4'`>#4#3#2#1").
Qed.


  (* [comment removed for export] *)
  Lemma pc_af254 : v_addi (0xaf2dc : word) 4 = (0xaf2e0 : word).
  Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+^V#1!1+^V#2%~R!3+D!1+^V#3#2#1!3+D+G!2'^Y#4#3!2'^Y#4#2%~R!3+D+G!2'^Y#3#2!2'^Y#3#1!3+D!1+^V#4#3#2!1,^W|600;|20;!2'`A!3,_E4!1,^[|C2f2dc;,_F!1,^[5!1,^[|C2f2e0;!3,_E47,_F&H;R$n;R+`?$b1;R0$b2;R1!5'_C23%~R!3+D+G!2'^Y#3#2!2'^Y#3#1!3+D!1+^V#4#3#2$~R2$~R%~R!3+D+G!2'^Y#4#3!2'^Y#4#2!3+D!1+^V#5#4#3#1!3'`@#3#2#1%n;R+`?%b1;R0%b2;R13!4#1468vv!2,O+G7!3+D+G!2'^Y46!2'^Y48").
Qed.

  (* [comment removed for export] *)
  Lemma loop1_b : forall n regs m (k : nat) (b : word) (bs : list byte),
    (length bs <= n)%nat ->
    RI regs -> LM m ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
    getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
    (1 <= k < length bs)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
    rdn RSEGS mem1 b (length bs) = Some bs ->
    (bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
    (bv_unsigned b + Z.of_nat (length bs) <= 2 ^ 47)%Z ->
    (Z.of_nat (length bs) <= 2 ^ 30)%Z ->
    SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs (0xaf2ec : word) m (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
  Proof.
    induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b) as Hb.

    destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
    { eapply LM_store_ok; [exact LMm | exact SOK1]. }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
    { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
    eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
    set (m' := wbytes (wbytes m _ _) _ _).
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).

    eapply (LibWritevXB.rz_writev1_wallX_b RSEGS scfg regs1 (0xaf2dc : word) m' model W_af2a0 fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
      [ exact F_af2a0 | exact E_af2a0 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
      | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - unfold TASK_SIZE. u_norm. lia.
    - unfold TASK_SIZE. u_norm. lia.
    - u_norm. lia.
    - u_norm. lia.
    -
      intros k' K1 K2. rewrite pc_af254. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      +
        destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply finish_nil_b; [| exact LMm'].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      +
        destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma loop2_b : forall n regs m (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte),
    (length bs0 + length bs1 <= n)%nat ->
    RI regs -> LM m ->
    getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
    getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
    getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
    (1 <= k < length bs0 + length bs1)%nat ->
    rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
    rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
    rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
    rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
    rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
    rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
    (bv_unsigned b0 + Z.of_nat (length bs0) <= 2 ^ 47)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
    (bv_unsigned b1 + Z.of_nat (length bs1) <= 2 ^ 47)%Z ->
    (Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 2 ^ 30)%Z ->
    SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs (0xaf2ec : word) m (seg_rom RSEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
  Proof.
    induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    -
      destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (LibWritevXB.rz_writev2_wallX_b RSEGS scfg regs1 (0xaf2dc : word) m' model W_af2a0 fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
        [ exact F_af2a0 | exact E_af2a0 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_af254. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply finish_nil_b; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- rewrite length_skipn. lia.
    -
      destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (LibWritevXB.rz_writev1_wallX_b RSEGS scfg regs1 (0xaf2dc : word) m' model W_af2a0 fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) K);
        [ exact F_af2a0 | exact E_af2a0 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_af254. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply finish_nil_b; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (loop1_b (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
  Qed.

End Loop.
End FPX_1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].
Section FPX_2. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.


Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  (0xc7000 <= f)%Z -> (f + 232 <= 0xf9890)%Z ->
  LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
  sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "SjT0|600;!1,^W0!1+^V1|30;!1+^V!1,^W3!1+_H4%~R25|P00000000;!1,^[7!1,^[|630;!2'^X89!1,^[|^2000000000000;!1,^[|C47000;!1,^[|768;!1,^[|C79890;!1,^[|628;!2'^Y1#1!1,^[|608;%x;R2%~R!1'_2!2+Y!2'T!2'J#G?@!2'Z@!2'J#GA!3+D5!1#I#2!@'aG#J#H#F#E#D#C#B#A#@#?#>#=#<#;#:#2!4'`;#K#I#;#:|500;!1,^[D!2'^Y1#2|510;!1,^[G|518;!1,^[I!2'^Y1#3!1,^[0!2'^Y1#4|10;!1,^[N!2'^ZOL!2'^X#NE!2'_31Q}8!2'aJ#@#?!2'_RST!3'_Q#PRU|508;!1,^[W!2'^X#NX!2'_31Y!2'_RS#@!4'_QVZ[#5$o;R5!3+D5#1!1#R#6!4'_Q#PRU#5!1#P#5!@'aG#Q#O#M#L#K#J#I#H#G#F#E#D#C#B#A#5!1,^[3!2'J#O^4!2'_31^5!2'_RS#M!3'_Q#Q^6^7|40;!1,^[^9!2'J#O^:!2'_31^;!2'_RS#L!3'_Q^8^<^=|48;!1,^[^?!2'J#O^@!2'_31^A!2'_RS#K!3'_Q^>^B^C!2'J#OE!2'_31^E!2'_RS#J!3'_Q^D^F^G!2'J#OX!2'_31^I!2'_RS#I!3'_Q^H^J^K!2'J#OH!2'_31^M!2'_RS#H!3'_Q^L^N^O!2'J#OJ!2'_31^Q!2'_RS#G!3'_Q^P^R^S!2'J#OL!2'_31^U!2'_RS#F!3'_Q^T^V^W!2'J#OA!2'_31^Y!2'_RS#E!3'_Q^X^Z^[!2'J#O?!2'_31_0!2'_31#D!2'_RS_2!3'_Q^\_1_3!1,^[|620;!2'J#O_5!2'_31_6!2'_31#C!2'_RS_8!3'_Q_4_7_9!1,^[|618;!2'J#O_;!2'_31_<!2'_RS#B!4'_Q_:_=_>#5!4'_Q_4_7_9#5!4'_Q^\_1_3#5!4'_Q^X^Z^[#5!4'_Q^T^V^W#5!4'_Q^P^R^S#5!4'_Q^L^N^O#5!4'_Q^H^J^K#5!4'_Q^D^F^G#5!4'_Q^>^B^C#5!4'_Q^8^<^=#5!4'_Q#Q^6^7#5!1#Q#5!2'^Y1!2'_31!2'J#P^4!2'^Y1#6!1'K#1!2'^X_L_N!1'KS!2'^X#1_P$z;R+G!1'_2!2+Y!2'T#1_M!2'Z_M_Q!2'^Y1#5!2'T^5_S!2'^X^5_P!2'Z_S_U!2+Y_T_V!2'^X^5^4!2'Z_S_X!2+Y_T_Y$x;R+G#1!2'Z#2#1$x;R+G$y;R+G!1'_V_\!2,O+G_S$n;R+G$m;R+G!2,O+G!4'_W+G+G'_X!2'^X#2#1!<'_Y+?+G+G+G'K'K_[_[$x;R+?!2,O+G_NS^4!2,O+G^4!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^5^5!2,O+G^5_P^4`3!2'_8OL%~R!2'Z,HO%~R!2'T,HL!2'Z,HP!2'T,HO$Ha;R`7$~R+_9!3'_:OL#2%Ha;R`7%~R+_9!2'T,HP!1,6+\!1+@+\!4,^8+G!2,^9+G#3#2!1,_;+G!1+^:+G!1+^<+G!2,^G+G,^5!2,^D+G9!2,^G+GN!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+G!3,^F+G`?`@,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^E`?,^H!1,^K+^>!2,^D+G^4!3,^F+G`?`D!3,_=+G`E`D!2'^M`>,^?!4'^N#1#3vv!2,O+^O,^P!3+D+^O!2'^Q#1#3,^P!3'^R+G,H#2%~R!2+Y!2'T!2'J#19#2_\+_?!2'J#2^4!2'^X`J^4!2'^Y1#8!3#1`L#R#7!2'^Y1^6!2,^9+G#2!7,^B`>'^=+^>+^>,^?!4,^C+G!3,_=+G!2,^D+G8`@,^L`?,^H!2,^D+G,H!2'T:#1!2#1#R#A!7,^B`>'^=+^>+^>,^?!4,^C+G`?,^L!2,^D+G;,^H!3,_>+G!2,^D+GO1!2'T#1;!2#1#R#@!3'_7^5&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^L`E,^H`G`H%__x1;R+G%~R`R!2'T,H`J`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+G`E,^E`U,^H`G`H%__x1;R+G%~R`V!2'Z`JP`W!2'^X`N_P!2'=4^7!2'_ZS#M$z;R+G!2'T_QP$x;R+G$y;R+G!1'_V!2'T#2#1!2,O+GP!2'^Y1!2'_31!2'J#P^:!2'^Xa2_N!2'T^;_S!2'^X^;_P!2'Z_Sa5!2+Ya4a6!2'^X^;^4!2'Z_Sa8!2+Ya4a9!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^;^;!2,O+G^;_P^4`3!3,^F+G`?!2,^D+G^:!3,_=+Ga<`D!2'J#2^:!2'^Xa>^4!2'^Y1^<!3'_7^;&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^La<,^H`G`H%__x1;R+G%~R`R!2'T,Ha>`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Ga<,^E`U,^H`G`H%__x1;R+G%~R`V!2'Za>P`W!2'^Xa@_P!2'=4^=!2'_ZS#L!2'^Y1!2'_31!2'J#P^@!2'^XaE_N!2'T^A_S!2'^X^A_P!2'Z_SaH!2+YaGaI!2'^X^A^4!2'Z_SaK!2+YaGaL!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^A^A!2,O+G^A_P^4`3!3,^F+G`?!2,^D+G^@!3,_=+GaO`D!2'J#2^@!2'^XaQ^4!2'^Y1^B!3'_7^A&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^LaO,^H`G`H%__x1;R+G%~R`R!2'T,HaQ`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GaO,^E`U,^H`G`H%__x1;R+G%~R`V!2'ZaQP`W!2'^XaS_P!2'=4^C!2'_ZS#K!2'^Y1!2'_31!2'J#PE!2'^XaX_N!2'T^E_S!2'^X^E_P!2'Z_Sa[!2+YaZa\!2'^X^E^4!2'Z_Sb1!2+YaZb2!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^E^E!2,O+G^E_P^4`3!2,^D+GE!3,^F+G`?b5!3,_=+Gb6`D!2'J#2E!2'^Xb8^4!2'^Y1^F!3'_7^E&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^Lb6,^H`G`H%__x1;R+G%~R`R!2'T,Hb8`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Gb6,^E`U,^H`G`H%__x1;R+G%~R`V!2'Zb8P`W!2'^Xb:_P!2'=4^G!2'_ZS#J!2'^Y1!2'_31!2'J#PX!2'^Xb?_N!2'T^I_S!2'^X^I_P!2'Z_SbB!2+YbAbC!2'^X^I^4!2'Z_SbE!2+YbAbF!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^I^I!2,O+G^I_P^4`3!2,^D+GX!3,^F+G`?bI!3,_=+GbJ`D!2'J#2X!2'^XbL^4!2'^Y1^J!3'_7^I&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^LbJ,^H`G`H%__x1;R+G%~R`R!2'T,HbL`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GbJ,^E`U,^H`G`H%__x1;R+G%~R`V!2'ZbLP`W!2'^XbN_P!2'=4^K!2'_ZS#I!2'^Y1!2'_31!2'J#PH!2'^XbS_N!2'T^M_S!2'^X^M_P!2'Z_SbV!2+YbUbW!2'^X^M^4!2'Z_SbY!2+YbUbZ!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^M^M!2,O+G^M_P^4`3!2,^D+GH!3,^F+G`?c0!3,_=+Gc1`D!2'J#2H!2'^Xc3^4!2'^Y1^N!3'_7^M&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^Lc1,^H`G`H%__x1;R+G%~R`R!2'T,Hc3`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Gc1,^E`U,^H`G`H%__x1;R+G%~R`V!2'Zc3P`W!2'^Xc5_P!2'=4^O!2'_ZS#H!2'^Y1!2'_31!2'J#PJ!2'^Xc:_N!2'T^Q_S!2'^X^Q_P!2'Z_Sc=!2+Yc<c>!2'^X^Q^4!2'Z_Sc@!2+Yc<cA!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^Q^Q!2,O+G^Q_P^4`3!2,^D+GJ!3,^F+G`?cD!3,_=+GcE`D!2'J#2J!2'^XcG^4!2'^Y1^R!3'_7^Q&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^LcE,^H`G`H%__x1;R+G%~R`R!2'T,HcG`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GcE,^E`U,^H`G`H%__x1;R+G%~R`V!2'ZcGP`W!2'^XcI_P!2'=4^S!2'_ZS#G!2'^Y1!2'_31!2'J#PL!2'^XcN_N!2'T^U_S!2'^X^U_P!2'Z_ScQ!2+YcPcR!2'^X^U^4!2'Z_ScT!2+YcPcU!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^U^U!2,O+G^U_P^4`3!2,^D+GL!3,^F+G`?cX!3,_=+GcY`D!2'J#2L!2'^Xc[^4!2'^Y1^V!3'_7^U&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^LcY,^H`G`H%__x1;R+G%~R`R!2'T,Hc[`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GcY,^E`U,^H`G`H%__x1;R+G%~R`V!2'Zc[P`W!2'^Xd0_P!2'=4^W!2'_ZS#F!2'^Y1!2'_31!2'J#PA!2'^Xd5_N!2'T^Y_S!2'^X^Y_P!2'Z_Sd8!2+Yd7d9!2'^X^Y^4!2'Z_Sd;!2+Yd7d<!B'P+G+G+G+G+G+G'^X_[_[_['^X`2^Y^Y!2,O+G^Y_P^4`3!3,^F+G`?!2,^D+GA!3,_=+Gd?`D!2'J#2A!2'^XdA^4!2'^Y1^Z!3'_7^Y&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^Ld?,^H`G`H%__x1;R+G%~R`R!2'T,HdA`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Gd?,^E`U,^H`G`H%__x1;R+G%~R`V!2'ZdAP`W!2'^XdC_P!2'=4^[!2'_ZS#E!2'^Y1!2'_31!2'J#P?!2'^XdH_N!2'T_0_S!2'^X_0_P!2'Z_SdK!2+YdJdL!2'^X_0^4!2'Z_SdN!2+YdJdO!B'P+G+G+G+G+G+G'^X_[_[_['^X`2_0_0!2,O+G_0_P^4`3!3,^F+G`?!2,^D+G?!7,^B`>'^=+^>+^>,^?!4,^C+GdR,^L`A,^H!3,_=+GdR`D!2'J#2?!2'TdU#3!2'^XdU^4!2'^Y1_1!3'_7_0&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^LdR,^H`G`H%__x1;R+G%~R`R!2'T,HdU`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GdR,^E`U,^H`G`H%__x1;R+G%~R`V!2'ZdUP`W!2'^XdX_P!2'=4_3!2'_ZS_2!2'^Y1!2'_31!2'J#P_5!2'^Xe0_N!2'T_6_S!2'^X_6_P!2'Z_Se3!2+Ye2e4!2'^X_6^4!2'Z_Se6!2+Ye2e7!B'P+G+G+G+G+G+G'^X_[_[_['^X`2_6_6!2,O+G_6_P^4`3!3,^F+G`?!2,^D+G_5!3,_=+Ge:`D!2'J#2_5!2'^Xe<^4!2'^Y1_7!3'_7_6&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^Le:,^H`G`H%__x1;R+G%~R`R!2'T,He<`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Ge:,^E`U,^H`G`H%__x1;R+G%~R`V!2'Ze<P`W!2'^Xe>_P!2'=4_9!2'_ZS_8!2'^Y1!2'_31!2'J#P_;!2'^XeC_N!2'T_<_S!2'^X_<_P!2'Z_SeF!2+YeEeG!2'^X_<^4!2'Z_SeI!2+YeEeJ!B'P+G+G+G+G+G+G'^X_[_[_['^X`2_<_<!2,O+G_<_P^4`3!3,^F+G`?!2,^D+G_;!3,_=+GeM`D!2'J#2_;!2'^XeO^4!2'^Y1_=!3'_7_<&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^LeM,^H`G`H%__x1;R+G%~R`R!2'T,HeO`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GeM,^E`U,^H`G`H%__x1;R+G%~R`V!2'ZeOP`W!2'^XeQ_P!2'=4_>!2'_ZS#B!3'_Q_:_=_>!1,^[|610;!2'J#OeW!2'_31eX!2'_RS#A!2'^Y1!2'_31!2'J#PeW!2'^Xe[_N!2'TeX_S!2'^XeX_P!2'Z_Sf1!2+Yf0f2!2'^XeX^4!2'Z_Sf4!2+Yf0f5!B'P+G+G+G+G+G+G'^X_[_[_['^X`2eXeX!2,O+GeX_P^4`3!3,^F+G`?!2,^D+GeW!3,_=+Gf8`D!2'J#2eW!2'^Xf:^4!2'^Y1eY!3'_7eX&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`P`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^Lf8,^H`G`H%__x1;R+G%~R`R!2'T,Hf:`S&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Gf8,^E`U,^H`G`H%__x1;R+G%~R`V!2'Zf:P`W!2'^Xf<_P!2'=4eZ!2'_ZS#A!2'^Y1!2'_31!2'^X#OE!2'^XfA_N!2'TQ_S!2'^XQ_P!2'Z_SfD!2+YfCfE!2'^XQ^4!2'Z_SfG!2+YfCfH!B'P+G+G+G+G+G+G'^X_[_[_['^X`2QQ!2,O+GQ_P^4`3!3,_=+G`?b5!7,^B`>'^=+^>+^>,^?!4,^C+GfK,^L`A,^H!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?fL!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^E!3,_=+G`?c0,^H!3,_=+GfK`D!2'^X#1E%~R!2+Y!2'TfO#2!2'Z#2!2'^X#1H+_?!2'^X#2E!2'^XfQ^4!3#1`L#Q#6!2'^Y1R!7,^B`>'^=+^>+^>,^?!4,^C+G!2,^D+G<,^L`?,^H$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fU`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^LfK,^H`G`H!2'T<#1%__x1;R+G%~RfW!2'T,HfQ!2#1#Q#?!7,^B`>'^=+^>+^>,^?!4,^C+G!3,_=+G`?!2,^D+G=,^L!2,^D+G>,^H$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fZ`C!7,^B`>'^=+^>+^>,^?!4,^C+GfK,^E`U,^H`G`H!2'T!2'^X#1=>%__x1;R+G%~Rf\!2'ZfQP!2#1#Q#>!3'_7Q&__sat8;R`5`6&__sat7;R`8`9&__arith;RfVfXfY&__sat8;R`5`6&__sat7;R`8`9&__arith;Rf[g0g1!2'^XfT_P!2'=4U!2'_ZST$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fZ`C!7,^B`>'^=+^>+^>,^?!4,^C+GfN,^L`U,^H`G`H%__x1;R+G%~Rf\!2'TfRP!2'^Y1!2'_31!2'^X#OX!2'^Xg8_N!2'TY_S!2'^XY_P!2'Z_Sg;!2+Yg:g<!2'^XY^4!2'Z_Sg>!2+Yg:g?!B'P+G+G+G+G+G+G'^X_[_[_['^X`2YY!2,O+GY_P^4`3!3,_=+G`?bI!3,_=+GgB`D!2'^X#2X!2'^XgD^4!2'^Y1Z$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fU`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^LgB,^H`G`H%__x1;R+G%~RfW!2'T,HgD$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fZ`C!7,^B`>'^=+^>+^>,^?!4,^C+GgB,^E`U,^H`G`H%__x1;R+G%~Rf\!2'ZgDP!3'_7Y&__sat8;R`5`6&__sat7;R`8`9&__arith;RgGgHfY&__sat8;R`5`6&__sat7;R`8`9&__arith;RgIgJg1!2'^XgF_P!2'=4[!2'_ZS#@!1'KgM$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fZ`C!7,^B`>'^=+^>+^>,^?!4,^C+GgC,^L`U,^H`G`H%__x1;R+G%~Rf\!2'TgEP!3'_QVZ[!2'^X#NJ!2'_31gS!2'^Y1!2'_31!2'^X#OJ!2'^XgU_N!2'TgS_S!2'^XgS_P!2'Z_SgX!2+YgWgY!2'^XgS^4!2'Z_Sg[!2+YgWg\!B'P+G+G+G+G+G+G'^X_[_[_['^X`2gSgS!2,O+GgS_P^4`3!3,_=+G`?cD!7,^B`>'^=+^>+^>,^?!4,^C+Gh2,^L`A,^H!3,_=+Gh2`D!2'^X#1J!2'^X#2J!2'^Xh6^4!2'^Y1gT$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fU`C!7,^B`>'^=+^>+^>,^?!4,^C+G`Q,^Lh2,^H`G`H%__x1;R+G%~RfW!2'T,Hh6$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fZ`C!7,^B`>'^=+^>+^>,^?!4,^C+Gh2,^E`U,^H`G`H%__x1;R+G%~Rf\!2'Zh6P!3'_7gS&__sat8;R`5`6&__sat7;R`8`9&__arith;Rh9h:fY&__sat8;R`5`6&__sat7;R`8`9&__arith;Rh;h<g1!2'^Xh8_P$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?fZ`C!7,^B`>'^=+^>+^>,^?!4,^C+Gh4,^L`U,^H`G`H%__x1;R+G%~Rf\!2'Th7P!2'^X#IE!2'_31hA!2'aJ#;#:!2'_RShC!3'_Q#KhBhD!2'^X#IX!2'_31hF!2'_RS#;!3'_QhEhGhH!2'^X#IJ!2'_31hJ!3'_QhIhKhH!?'aG#L#J#H#G#F#E#D#C#B#A#@#?#>#=#<!2'_31!2'J#J^4!3'_Q#LhN^O!2'_31!2'J#J^:!3'_QhOhP^S!2'_31!2'J#J^@!3'_QhQhR^W!2'_31!2'J#JE!3'_QhShT^[!2'_31!2'J#JX!2'_RS#D!3'_QhUhVhW!2'_31!2'J#JH!2'_RS#C!3'_QhXhYhZ!2'_31!2'J#JJ!3'_Qh[h\_>!2'_31!2'J#JL!3'_Qi0i1eZ!2'_31!2'J#JA!3'_Qi2i3[!2'_31!2'J#J?!2'_RS!2'_31#?!3'_Qi4i5i6!2'_31!2'J#J_5!2'_RS!2'_31#>!3'_Qi7i8i9!2'_31!2'J#J_;!2'_RS#=!3'_Qi:i;i<!2'_31!2'J#JeW!2'_RS#<!1+@4!1+_Hi@!4'_L'3hIhBS$o;RiA!3+DiA#1!2,_Mi@!2'_RS!2'aJ#<#;$z;R+G!2'T!2'^X#1^4P!2#1#L#9&__sat8;R`5`6&__sat7;R`8`9&__arith;Rg6g7iE!2'^Y1hB!2#1#J#8!3'_7hA&__arith;RfVfXiH&__sat8;R`5`6&__sat7;R`8`9&__arith;Rf[g0iE!2'^X#JE!2'^Y1!2'_31iJ!2'^XiK_P!2'^X#JX!2'^Y1!2'_31iM!2'^XiN_N!2'^XiN_P$z;R+G!2+X!2'T!2'^XiJ_P#1!2'T_QiJ!2'^XhA_P!2'TiRhF!2'^XhF_P!2'TiThA!2'^XhA^4!2'TiVhF!2'^XhF^4!2'TiXhA!2,O+GhA!B'P+G+G+G+G+G+G'^X_[_[_['^X`2hAhAiZ_P^4`3!2,O+GhF!B'P+G+G+G+G+G+G'^X_[_[_['^X`2hFhFi\_P^4`3!2'^XfO^4!2'^X#1X!2'^Xj2^4!1#1#J!2'^Y1hG!3'_7hF&__arith;RgGgHiH&__sat8;R`5`6&__sat7;R`8`9&__arith;RgIgJiE!2'^XiG_P!2'^Xj5_P!2'=4hH!2'_ZS#;vd!6'B+GhA`\!4'E!2'TiRP!2'TiVP!<'L+G+G'T_['Ta0iRiVi[PPa1iFiGiI!2'Tj7P&__sat8;R`5`6&__sat7;R`8`9&__arith;RgPgQiEvd!6'B+GhF`\!4'E!2'TiTP!2'TiXP!<'L+G+G'T_['Ta0iTiXj0PPa1j<j5j6!2'Tj8P!2'^Y1!2'_31!2'^X#JJ!2'^Xj>_N$z;R+G!2+X!2'T_Qj>!2'T!2'^Xj>_P#1!2'TiRhJ!2'^XhJ_P!2'TjBhA!2'TiVhJ!2'^XhJ^4!2'TjEhA!2,O+GhJ!B'P+G+G+G+G+G+G'^X_[_[_['^X`2hJhJjG_P^4`3!2'^Xh5^4!2'^Y1hK!3'_7hJ&__arith;Rh9h:iH&__sat8;R`5`6&__sat7;R`8`9&__arith;Rh;h<iE!2'^XjJ_P&__sat8;R`5`6&__sat7;R`8`9&__arith;Rh?h@iE!6'B+?S$n;R+?!2'Tj?Pvd!6'B+GhJ`\!4'E!2'TjBP!2'TjEP!<'L+G+G'T_['Ta0jBjEjHPPa1jMjJjK!2'TjLPj9j:!2'TiThJ!2'TjBhF!2'TiXhJ!2'TjEhF!2,_Mi@hH$mem;R6$m;R6$su;R+G$f;R+G$ra;R2$s0;R2$s1;R2$s2;R2$s3;R2$s4;R2$s5;R2$s6;R2$can;R2$wb;R+G$n;R+G$s;R2$l;R2$bufp;R2$bufsz;R2$SUlo;R!2'T:#A$SUhi;R!2'T#B;$Flo;R!2'T<#B$Fhi;R!2'T!2'^X#C=>$H;R!3'aF#E!?'aG#G#E#C#B#A#@#?#>#=#<#;#:#9#8#7#F!5'_CB!2'_I!?'aG#H#F#D#C#B#A#@#?#>#=#<#;#:#9#8#G!6+aH#H#F#E#7#6!4'`;#G#E#7#6$~RB$~R!2'_I!?'aG#I#G#E#D#C#B#A#@#?#>#=#<#;#:#9#H!2$E;R%x;R2%~R!1'_2!2+Y!2'T!2'J#I?@!2'Z@!2'J#IA!3+D5!1#K#2!@'aG#L#J#H#G#F#E#D#C#B#A#@#?#>#=#<#2$G;R!2'_I!?'aG#K#I#G#F#E#D#C#B#A#@#?#>#=#<#;#J!;,aI#L#J#I#;#:C$x;R2$Hx1;R!1'_2!2+Y!2'T!2'J#K9@!2'Z@#K$Hx2;R!1'_2!2+Y!2'T!2'^X#KEF!2'ZF!2'^X#KH$Hx3;R!1'_2!2+Y!2'T!2'^X#LJK!2'ZK!2'^X#LL&Hx;R!1'^\#4!2+Y!2'T,HM!2'ZMPvd!6'B5\^0!6'B5^1^0!6'B5^2^0!6'B5^3^0vd!6'B5_?^0!6'B5_@^0!6'B5_A^0!6'B5_B^0!6'B5_C^0!6'B5_D^0!6'B5_E^0!6'B5_F^0!6'B5_G^0!6'B5_H^0!6'B5_I^0!6'B5_J^0!6'B5_K^0!2,O5_K_J!6'_S^7#Q^6#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'T_L_M!2'Z_M_Ovd!6'B+G^5_R!4'E!1'_2_W!1'_2_Z!3'_T_W_Z!6'_U_T_V_T_Y!1'_V_T!<'L+G+G'Z_['Z`0_S_S`1_U_X`4&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+G`E,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^E`F,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'T`J#3!2'Z#3`K+_?`M`N`X!1'_2!2+Y!2'T`N_S!2'Z_S`Y`Z`[!1'_2!3'_[#5^6!1'K`Z!6'B+?S$n;R+?!2'T_OPvd!6'B+G^5`\!4'E!2'T_UP!2'T_XP!<'L+G+G'T_['Ta0_U_X`4PPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+G`F,^L`U,^H`G`H%__x1;R+G%~R`V!2'T`KP`W`N`X!2'T`YP`Z`[_I!6'_S^=^8^<#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'Ta2_M!2'Z_Ma3vd!6'B+G^;_R!4'E!1'_2a7!1'_2a:!3'_Ta7a:!6'_Ua4a6a4a9!1'_Va4!<'L+G+G'Z_['Z`0_S_S`1a5a8a;&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+Ga<,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^Ea=,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'Ta>#3!2'Z#3a?+_?`Ma@aA!1'_2!2+Y!2'Ta@_S!2'Z_SaBaCaD!1'_2!3'_[#5^<!1'KaC!6'B+?S$n;R+?!2'Ta3Pvd!6'B+G^;`\!4'E!2'Ta5P!2'Ta8P!<'L+G+G'T_['Ta0a5a8a;PPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Ga=,^L`U,^H`G`H%__x1;R+G%~R`V!2'Ta?P`Wa@aA!2'TaBPaCaD_H!6'_S^C^>^B#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'TaE_M!2'Z_MaFvd!6'B+G^A_R!4'E!1'_2aJ!1'_2aM!3'_TaJaM!6'_UaGaIaGaL!1'_VaG!<'L+G+G'Z_['Z`0_S_S`1aHaKaN&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GaO,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^EaP,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'TaQ#3!2'Z#3aR+_?`MaSaT!1'_2!2+Y!2'TaS_S!2'Z_SaUaVaW!1'_2!3'_[#5^B!1'KaV!6'B+?S$n;R+?!2'TaFPvd!6'B+G^A`\!4'E!2'TaHP!2'TaKP!<'L+G+G'T_['Ta0aHaKaNPPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GaP,^L`U,^H`G`H%__x1;R+G%~R`V!2'TaRP`WaSaT!2'TaUPaVaW_G!6'_S^G^D^F#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'TaX_M!2'Z_MaYvd!6'B+G^E_R!4'E!1'_2b0!1'_2b3!3'_Tb0b3!6'_UaZa\aZb2!1'_VaZ!<'L+G+G'Z_['Z`0_S_S`1a[b1b4&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+Gb6,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^Eb7,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'Tb8#3!2'Z#3b9+_?`Mb:b;!1'_2!2+Y!2'Tb:_S!2'Z_Sb<b=b>!1'_2!3'_[#5^F!1'Kb=!6'B+?S$n;R+?!2'TaYPvd!6'B+G^E`\!4'E!2'Ta[P!2'Tb1P!<'L+G+G'T_['Ta0a[b1b4PPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Gb7,^L`U,^H`G`H%__x1;R+G%~R`V!2'Tb9P`Wb:b;!2'Tb<Pb=b>_F!6'_S^K^H^J#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'Tb?_M!2'Z_Mb@vd!6'B+G^I_R!4'E!1'_2bD!1'_2bG!3'_TbDbG!6'_UbAbCbAbF!1'_VbA!<'L+G+G'Z_['Z`0_S_S`1bBbEbH&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GbJ,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^EbK,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'TbL#3!2'Z#3bM+_?`MbNbO!1'_2!2+Y!2'TbN_S!2'Z_SbPbQbR!1'_2!3'_[#5^J!1'KbQ!6'B+?S$n;R+?!2'Tb@Pvd!6'B+G^I`\!4'E!2'TbBP!2'TbEP!<'L+G+G'T_['Ta0bBbEbHPPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GbK,^L`U,^H`G`H%__x1;R+G%~R`V!2'TbMP`WbNbO!2'TbPPbQbR_E!6'_S^O^L^N#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'TbS_M!2'Z_MbTvd!6'B+G^M_R!4'E!1'_2bX!1'_2b[!3'_TbXb[!6'_UbUbWbUbZ!1'_VbU!<'L+G+G'Z_['Z`0_S_S`1bVbYb\&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+Gc1,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^Ec2,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'Tc3#3!2'Z#3c4+_?`Mc5c6!1'_2!2+Y!2'Tc5_S!2'Z_Sc7c8c9!1'_2!3'_[#5^N!1'Kc8!6'B+?S$n;R+?!2'TbTPvd!6'B+G^M`\!4'E!2'TbVP!2'TbYP!<'L+G+G'T_['Ta0bVbYb\PPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Gc2,^L`U,^H`G`H%__x1;R+G%~R`V!2'Tc4P`Wc5c6!2'Tc7Pc8c9_D!6'_S^S^P^R#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'Tc:_M!2'Z_Mc;vd!6'B+G^Q_R!4'E!1'_2c?!1'_2cB!3'_Tc?cB!6'_Uc<c>c<cA!1'_Vc<!<'L+G+G'Z_['Z`0_S_S`1c=c@cC&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GcE,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^EcF,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'TcG#3!2'Z#3cH+_?`McIcJ!1'_2!2+Y!2'TcI_S!2'Z_ScKcLcM!1'_2!3'_[#5^R!1'KcL!6'B+?S$n;R+?!2'Tc;Pvd!6'B+G^Q`\!4'E!2'Tc=P!2'Tc@P!<'L+G+G'T_['Ta0c=c@cCPPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GcF,^L`U,^H`G`H%__x1;R+G%~R`V!2'TcHP`WcIcJ!2'TcKPcLcM_C!6'_S^W^T^V#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'TcN_M!2'Z_McOvd!6'B+G^U_R!4'E!1'_2cS!1'_2cV!3'_TcScV!6'_UcPcRcPcU!1'_VcP!<'L+G+G'Z_['Z`0_S_S`1cQcTcW&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GcY,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^EcZ,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'Tc[#3!2'Z#3c\+_?`Md0d1!1'_2!2+Y!2'Td0_S!2'Z_Sd2d3d4!1'_2!3'_[#5^V!1'Kd3!6'B+?S$n;R+?!2'TcOPvd!6'B+G^U`\!4'E!2'TcQP!2'TcTP!<'L+G+G'T_['Ta0cQcTcWPPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GcZ,^L`U,^H`G`H%__x1;R+G%~R`V!2'Tc\P`Wd0d1!2'Td2Pd3d4_B!6'_S^[^X^Z#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'Td5_M!2'Z_Md6vd!6'B+G^Y_R!4'E!1'_2d:!1'_2d=!3'_Td:d=!6'_Ud7d9d7d<!1'_Vd7!<'L+G+G'Z_['Z`0_S_S`1d8d;d>&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+Gd?,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^Ed@,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'TdA#3!2'Z#3dB+_?`MdCdD!1'_2!2+Y!2'TdC_S!2'Z_SdEdFdG!1'_2!3'_[#5^Z!1'KdF!6'B+?S$n;R+?!2'Td6Pvd!6'B+G^Y`\!4'E!2'Td8P!2'Td;P!<'L+G+G'T_['Ta0d8d;d>PPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Gd@,^L`U,^H`G`H%__x1;R+G%~R`V!2'TdBP`WdCdD!2'TdEPdFdG_A!6'_S_3^\_1#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'TdH_M!2'Z_MdIvd!6'B+G_0_R!4'E!1'_2dM!1'_2dP!3'_TdMdP!6'_UdJdLdJdO!1'_VdJ!<'L+G+G'Z_['Z`0_S_S`1dKdNdQ&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?dS!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^EdT,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+YdV!2'Z#3dW+_?`MdXdY!1'_2!2+Y!2'TdX_S!2'Z_SdZd[d\!1'_2!3'_[#5_1!1'Kd[!6'B+?S$n;R+?!2'TdIPvd!6'B+G_0`\!4'E!2'TdKP!2'TdNP!<'L+G+G'T_['Ta0dKdNdQPPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GdT,^L`U,^H`G`H%__x1;R+G%~R`V!2'TdWP`WdXdY!2'TdZPd[d\_@!6'_S_9_4_7#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'Te0_M!2'Z_Me1vd!6'B+G_6_R!4'E!1'_2e5!1'_2e8!3'_Te5e8!6'_Ue2e4e2e7!1'_Ve2!<'L+G+G'Z_['Z`0_S_S`1e3e6e9&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+Ge:,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^Ee;,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'Te<#3!2'Z#3e=+_?`Me>e?!1'_2!2+Y!2'Te>_S!2'Z_Se@eAeB!1'_2!3'_[#5_7!1'KeA!6'B+?S$n;R+?!2'Te1Pvd!6'B+G_6`\!4'E!2'Te3P!2'Te6P!<'L+G+G'T_['Ta0e3e6e9PPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Ge;,^L`U,^H`G`H%__x1;R+G%~R`V!2'Te=P`We>e?!2'Te@PeAeB_?!6'_S_>_:_=#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'TeC_M!2'Z_MeDvd!6'B+G_<_R!4'E!1'_2eH!1'_2eK!3'_TeHeK!6'_UeEeGeEeJ!1'_VeE!<'L+G+G'Z_['Z`0_S_S`1eFeIeL&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GeM,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^EeN,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'TeO#3!2'Z#3eP+_?`MeQeR!1'_2!2+Y!2'TeQ_S!2'Z_SeSeTeU!1'_2!3'_[#5_=!1'KeT!6'B+?S$n;R+?!2'TeDPvd!6'B+G_<`\!4'E!2'TeFP!2'TeIP!<'L+G+G'T_['Ta0eFeIeLPPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+GeN,^L`U,^H`G`H%__x1;R+G%~R`V!2'TePP`WeQeR!2'TeSPeTeU!4'_QeVeYeZ#5!6'_SeZeVeY#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'Te[_M!2'Z_Me\vd!6'B+GeX_R!4'E!1'_2f3!1'_2f6!3'_Tf3f6!6'_Uf0f2f0f5!1'_Vf0!<'L+G+G'Z_['Z`0_S_S`1f1f4f7&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+Gf8,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^Ef9,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+Y!2'Tf:#3!2'Z#3f;+_?`Mf<f=!1'_2!2+Y!2'Tf<_S!2'Z_Sf>f?f@!1'_2!3'_[#5eY!1'Kf?!6'B+?S$n;R+?!2'Te\Pvd!6'B+GeX`\!4'E!2'Tf1P!2'Tf4P!<'L+G+G'T_['Ta0f1f4f7PPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!8,^;`>'^=+^>+^>,^?`T`C!7,^B`>'^=+^>+^>,^?!4,^C+Gf9,^L`U,^H`G`H%__x1;R+G%~R`V!2'Tf;P`Wf<f=!2'Tf>Pf?f@!3+D5^3_K^2!2#7#5&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?`B`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?dS!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^Ed?,^H`G`H%__x2;R+G%__x1;R+G%~R`I%~R!2+YdV!2'Z#3dA+_?`M^1!6'_SU#PR#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'TfA_M!2'Z_MfBvd!6'B+GQ_R!4'E!1'_2fF!1'_2fI!3'_TfFfI!6'_UfCfEfCfH!1'_VfC!<'L+G+G'Z_['Z`0_S_S`1fDfGfJ&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?fM`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?fL!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^EfN,^H`G`H%__x2;R+G%__x1;R+G%~RfP%~R!2+Y!2'TfQ#3!2'Z#3fR+_?fSfTg2!1'_2!2+Y!2'TfT_S!2'Z_Sg3g4g5!1'_2!3'_[#5R!1'Kg4!6'B+?S$n;R+?!2'TfBPvd!6'B+GQ`\!4'E!2'TfDP!2'TfGP!<'L+G+G'T_['Ta0fDfGfJPPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;Rg6g7g1fTg2!2'Tg3Pg4g5\!6'_S[VZ#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'Tg8_M!2'Z_Mg9vd!6'B+GY_R!4'E!1'_2g=!1'_2g@!3'_Tg=g@!6'_Ug:g<g:g?!1'_Vg:!<'L+G+G'Z_['Z`0_S_S`1g;g>gA&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?fM`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GgB,^L`A,^H!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^EgC,^H`G`H%__x2;R+G%__x1;R+G%~RfP%~R!2+Y!2'TgD#3!2'Z#3gE+_?fSgFgK!1'_2!2+Y!2'TgF_S!2'Z_SgLgMgN!1'_2!3'_[#5ZgO!6'B+?S$n;R+?!2'Tg9Pvd!6'B+GY`\!4'E!2'Tg;P!2'Tg>P!<'L+G+G'T_['Ta0g;g>gAPPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;RgPgQg1gFgK!2'TgLPgMgN!4'_QgRgT[#5!6'_S[gRgT#5vd!6'B+?S$n;R+?!1'_2!2+Y!2'TgU_M!2'Z_MgVvd!6'B+GgS_R!4'E!1'_2gZ!1'_2h0!3'_TgZh0!6'_UgWgYgWg\!1'_VgW!<'L+G+G'Z_['Z`0_S_S`1gXg[h1&__sat8;R`5`6&__sat7;R`8`9&__arith;R$__x2;R+G$__x1;R+G&__wit;R`:`;&__varmap;R`<`=&__ff;R!8,^;`>'^=+^>+^>,^?!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?h3!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^E!3,_=+G`?cX,^H`C!6,_<`>'^=+^>+^>,^?!7,^A`>'^=+^>+^>,^?h3!7,^B`>'^=+^>+^>,^?!4,^C+G`A,^Eh4,^H`G`H%__x2;R+G%__x1;R+G%~R%~R!2+Y!2'Th5#2!2'Z#2!2'^X#1L+_?%~R!2+Y!2'Th6#3!2'Z#3h7+_?!3#1`L#Q#5h8h=!1'_2!2+Y!2'Th8_S!2'Z_Sh>gMgN!1'_2!3'_[#5gTgO!6'B+?S$n;R+?!2'TgVPvd!6'B+GgS`\!4'E!2'TgXP!2'Tg[P!<'L+G+G'T_['Ta0gXg[h1PPa1&__sat8;R`5`6&__sat7;R`8`9&__arith;Rh?h@g1h8h=!2'Th>PgMgN!3+D5!5'`;#P#N#@#?#5_Kvd!5'_\#LhIhL!5'_\#LhEhI!5'_\#L#KhE!5'_\#LhM#Kvd!5'_\#Li=!3'_Qi=i>i?!5'_\#Li:i=!5'_\#Li7i:!5'_\#Li4i7!5'_\#Li2i4!5'_\#Li0i2!5'_\#Lh[i0!5'_\#LhXh[!5'_\#LhUhX!5'_\#LhShU!5'_\#LhQhS!5'_\#LhOhQ!5'_\#L#LhO!1'_J#L!3'`0^O#LhN!3'`0^ShOhP!3'`0^WhQhR!3'`0^[hShT!3'`0hWhUhV!3'`0hZhXhY!3'`0_>h[h\!3'`0eZi0i1!3'`0[i2i3!3'`0i6i4i5!3'`0i9i7i8!3'`0i<i:i;!3'`0i?i=i>!2'_I#LhM#1!3'`0hD#KhB!3'`0hHhEhG!3'`0hHhIhK!2'_I#LCvd!6'BiAiBiC!6'BiA!4'_L'3hEhBSiC!5'`R'3#KhBhCvd!6'B+GhAiDiFiGiI!2'T!2'^XiG^4PiB!9'`S'3hHhEhGhBS!6'B+?S$n;R+?!2+X!2'TiLiN!2'TiOiKvd!6'B+GhA$z;R+G!2+X!2'T_QiN!2'TiP#1!6'B+GhFiQ!4'E!2+XiSiU!2+XiWiY!6'`6iSiUiWiY!<'L+G+G'T_['Ta0iRiVi[hFhFi\!<'L+G+G'T_['Ta0iTiXj0hAhAiZ&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!7,^@`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GfN,^LgB,^H!7,^B`>'^=+^>+^>,^?!4,^C+GgC,^LfK,^H`G`H%__x1;R+G!2+X!2'Tj1j2!2'Tj3fOj4j5j6iGiI!2+X!2'Tj7j5!2'Tj8iGj9j:j;!6'B+?S$n;R+?!2'TiOPj=j9j:!4'_L'3hLhBS!9'`S'3hHhIhKhBS!6'B+?S$n;R+?!2+X!2'TiLj>!2'Tj?iKvd!6'B+GhAj@!6'B+GhJiQ!4'E!2+XjAjC!2+XjDjF!6'`6jAjCjDjF!<'L+G+G'T_['Ta0iRiVi[hJhJjG!<'L+G+G'T_['Ta0jBjEjHhAhAiZ&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!7,^@`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GfN,^Lh2,^H!7,^B`>'^=+^>+^>,^?!4,^C+Gh4,^LfK,^H`G`H%__x1;R+G!2+X!2'Tj1h5!2'TjIfOj4jJjKiGiI!2+X!2'Tj7jJ!2'TjLiGj9j:j;jN!3+DiA!4'_L'3ChBS!2,_Mi@hDvd!6'BiA!4'_L'3hIhGS$o;RiA!3+DiA#1!2,_Mi@i?!5'`R'3hEhG#;vd!6'B+GhFiDj<j5j6!2'T!2'^Xj5^4P!4'_L'3hLhGS!9'`S'3hHhIhKhGS!6'B+?S$n;R+?!2+X!2'TiPj>!2'Tj?iNvd!6'B+GhFj@!6'B+GhJ$z;R+G!2+X!2'T!2'^XiM_P#1!2'T_QiM!4'E!2+XjOjP!2+XjQjR!6'`6jOjPjQjR!<'L+G+G'T_['Ta0iTiXj0hJhJjG!<'L+G+G'T_['Ta0jBjEjHhFhFi\&__arith;R$__x1;R+G&__wit;R`:`;&__varmap;R`O`=&__ff;R!7,^@`>'^=+^>+^>,^?!7,^B`>'^=+^>+^>,^?!4,^C+GgC,^Lh2,^H!7,^B`>'^=+^>+^>,^?!4,^C+Gh4,^LgB,^H`G`H%__x1;R+G!2+X!2'Tj3h5!2'TjIj2j4jJjKj5j6!2+X!2'Tj8jJ!2'TjLj5j9j:j=jN!3+DiA!4'_L'3ChGSjSvd!5'`R'3hIhK#;vd!6'B+GhJiDjMjJjK!2'T!2'^XjJ^4P!3+DiA!4'_L'3ChKSjS#2#1#1").
Qed.

Lemma pc_af1cc : v_addi (0xaf254 : word) 4 = (0xaf258 : word).
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S90!1+^V#1!1+^V#2%~R!3+D!1+^V#3#2#1!3+D+G!2'^Y#4#3!2'^Y#4#2%~R!3+D+G!2'^Y#3#2!2'^Y#3#1!3+D!1+^V#4#3#2!1,^W|600;|20;!2'`A!3,_E4!1,^[|C2f254;,_F!1,^[5!1,^[|C2f258;!3,_E47,_F&H;R$n;R+`?$b1;R0$b2;R1!5'_C23%~R!3+D+G!2'^Y#3#2!2'^Y#3#1!3+D!1+^V#4#3#2$~R2$~R%~R!3+D+G!2'^Y#4#3!2'^Y#4#2!3+D!1+^V#5#4#3#1!3'`@#3#2#1%n;R+`?%b1;R0%b2;R13!4#1468vv!2,O+G7!3+D+G!2'^Y46!2'^Y48").
Qed.

Theorem ref_stdio_write_b :
  forall regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
  (0xc7000 <= f)%Z -> (f + 232 <= 0xf9890)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= 2 ^ 47)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 2 ^ 47)%Z ->
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall regs' mem',
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
  SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs (0xaf1cc : word) mem (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
  intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hrdr Hh Hlazy WBP WPhi
         LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }

  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0xf9890) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }

  assert (HK' : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m ->
     SpinAlgB.rzb RSEGS scfg (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
  { intros. apply HK. all: try assumption.
    eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
    match goal with H : LM _ _ _ |- _ => exact H end. }
  pose proof (finish_nil_b scfg su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
  pose proof (loop1_b scfg su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2_b scfg su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  -
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    lazymatch goal with |- SpinAlgB.rzb _ _ (mkCfg (mkst _ _ ?M _) _) _ =>
      replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    destruct extra as [|x0 extra'].
    +
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (LibWritevXB.rz_writev1_zeroX_b RSEGS scfg regs1 (0xaf254 : word) mem1 model W_af218 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
        [ exact F_af218 | exact E_af218 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | unfold TASK_SIZE; u_norm; lia | unfold TASK_SIZE; u_norm; lia | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      rewrite pc_af1cc.
      destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
      apply FIN; [|exact LM1].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    +
      eapply (LibWritevXB.rz_writev1_wallX_b RSEGS scfg regs1 (0xaf254 : word) mem1 model W_af218 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
        [ exact F_af218 | exact E_af218 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * unfold TASK_SIZE. u_norm. lia.
      * unfold TASK_SIZE. u_norm. lia.
      * cbn [length] in LENE. lia.
      * lia.
      * intros k K1 K2. rewrite pc_af1cc.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply FIN; [|exact LM1].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  -
    destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    eapply (LibWritevXB.rz_writev2_wallX_b RSEGS scfg regs1 (0xaf254 : word) mem1 model W_af218 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
      [ exact F_af218 | exact E_af218 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
      | exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + unfold TASK_SIZE. u_norm. lia.
    + unfold TASK_SIZE. u_norm. lia.
    + unfold TASK_SIZE. u_norm. lia.
    + u_norm. lia.
    + u_norm. lia.
    + intros k K1 K2. rewrite pc_af1cc. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply FIN; [|exact LM1].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        eapply SpinAlgB.rzb_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
Qed.
End FPX_2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
