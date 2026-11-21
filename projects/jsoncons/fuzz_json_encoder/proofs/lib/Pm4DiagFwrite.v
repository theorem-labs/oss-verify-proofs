(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact, the 6144513-byte zero-filled stack window): changed dgm_cell_vis, fwrite1_run, fwrite2_run; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8DiagFwrite.v, 376 lines within its lines 51-548. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm4IcptLayout PmIcptDrvA DrvKitA DrvNodesLazyK As0DrvKitA Pm4DrvEntry Pm4Drv_defs Pm4DrvLib Pm4DrvRead Pm4DrvPiece Pm4DiagLoopK Pm4DrvStdio Pm4DrvPrintfK Pm4DrvPrintf1 Pm4DrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require L5Defs L5KnA L5Core ArtMem Pm4ArtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4DrvP_dpM1_pre Pm4DrvP_dpM1d Pm4DrvP_dpM2_pre Pm4DrvP_dpM2d.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @list]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Numbers; @BinNums; @Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframe]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @credit]; [@stdpp; @bitvector; @definitions; @bv]; [@Corelib; @Numbers; @BinNums; @Npos]; [@Corelib; @Init; @Datatypes; @option]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @Model]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv]; [@Stdlib; @Lists; @List; @In]; [@Corelib; @Init; @Datatypes; @pair]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagFwrite; @DGM_CELLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @di_inv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ri_inv]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @vml_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @aio_statics]; [@Corelib; @Init; @Logic; @and]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_got_lo]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_got_hi]; [@Corelib; @Init; @Logic; @eq]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@Corelib; @Init; @Datatypes; @None]; [@Corelib; @Lists; @ListDef; @Forall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @cell_is]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @hl_segs]; [@Corelib; @Init; @Datatypes; @fst]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Corelib; @Init; @Datatypes; @snd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @asc_cells]; [@Corelib; @Init; @Logic; @and_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @M; @loaded_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @mrestrict]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ahid]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@Corelib; @Init; @Logic; @eq_ind]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dla_segs]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Lists; @List; @Forall_forall]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @rdn_mrestrict_eq]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Peano; @lt]; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Numbers; @BinNums; @xH]; [@Corelib; @Init; @Logic; @or]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@Corelib; @Init; @Logic; @f_equal]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @ZArith; @BinInt; @Z; @max]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@Corelib; @Init; @Logic; @eq_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_refl]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Stdlib; @micromega; @ZifyInst; @of_nat_to_nat_eq]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @max_spec]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@Corelib; @Init; @Logic; @True]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Corelib; @Init; @Datatypes; @bool]; [@Corelib; @Init; @Datatypes; @true]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@Corelib; @Init; @Logic; @False_ind]; [@Corelib; @Init; @Datatypes; @false]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvStdio; @vis_low]; [@Corelib; @Init; @Datatypes; @cons]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Corelib; @Init; @Datatypes; @O]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @VarMap; @Empty]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AgentLib; @u64_lit]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @woff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @range_avoids]; [@LinuxProcessSemantics; @Riscv; @Prelude; @bvmap]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @event]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @getr]; [@stdpp; @bitvector; @definitions; @BV]; [@Corelib; @Init; @Logic; @I]; [@stdpp; @bitvector; @definitions; @BvWf]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdEntry]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @fd_lookup]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_fds]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @FdChannel]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @FPState]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @same_but_materialized]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @c_kept]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagFwrite; @stderrMA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagFwrite; @Wfw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @SpinAlg; @srealizes]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @mkCfg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @mkst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagFwrite; @FPX_1; @Fwrite; @dgm_cell_vis]; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvStdio; @img_cell]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StreamSim; @wseg_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @writable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvExit; @wsg_writable]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM1_pre; @AS0DRVP_dpM1_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @store_ok_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @defined]; [@Corelib; @Init; @Logic; @or_introl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtMem; @art_bytes1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM1_pre; @AS0DRVP_dpM1_pre; @dpM1_pre_conc]; [@Corelib; @Init; @Logic; @or_intror]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@Corelib; @Init; @Logic; @f_equal2]; [@Corelib; @Numbers; @BinNums; @N]; [@stdpp; @bitvector; @definitions; @bv_eq]; [@Corelib; @Init; @Logic; @ex]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @mem_grows]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @CatSim; @msteps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM1_pre; @AS0DRVP_dpM1_pre; @KS_dpM1_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u64_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @L5Defs; @L5; @u32_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ShapeAlg; @t_emit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Spec; @W]; [@Corelib; @Init; @Logic; @ex_ind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @in_block]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4Drv_defs; @IMG_W_A]; [@Corelib; @Init; @Logic; @ex_intro]; [@Corelib; @Init; @Logic; @conj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @CWA]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvPiece; @drv_piece]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @StoreOk; @store_ok_mono]; [@Corelib; @Init; @Datatypes; @orb]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Stdlib; @Bool; @Bool; @orb_true_iff]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms_Prop; @or_iff_morphism]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@Corelib; @Classes; @Morphisms; @Reflexive_partial_app_morphism]; [@Stdlib; @Bool; @Bool; @andb_true_iff]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvStdio; @rdn_tr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @sbm_fds']; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv_lzinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @lzinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @H_off_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @lazy_cover]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_lazy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @A_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @MInv]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_halted]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvPrintf1; @nl_pt]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_in_ranges]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_base_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn_length]; [@Corelib; @Init; @Datatypes; @length]; [@Corelib; @Lists; @ListDef; @map]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @WriteEv]; [@Corelib; @Init; @Datatypes; @app]; [@Stdlib; @Lists; @List; @app_nil_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_loop]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Corelib; @Init; @Nat; @add]; [@Corelib; @Init; @Peano; @le]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Stdlib; @Lists; @List; @length_app]; [@Corelib; @Init; @Logic; @eq_trans]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_regs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_buf]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma1]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEsub]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEc]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEadd]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @Peq]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@stdpp; @tactics; @f_equal_help]; [@Corelib; @Numbers; @BinNums; @positive]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_iov]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @WV_KEEP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @dinv_frame]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @sbm_vml]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0DrvKitA; @sbm_halted_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvLib; @ahid_sbm]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @cell_zero_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DrvStdio; @img_sh0]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @ART_POISON]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @IcptIfaceA; @icl_poison]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4IcptLayout; @aicl_poison]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @eq_decidable]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @byte_at]; [@Corelib; @Init; @Logic; @eq_sym]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM1d; @AS0DRVP_dpM1d; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM1d; @AS0DRVP_dpM1d; @dpM1d_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @u64_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM1d; @AS0DRVP_dpM1d; @KS_dpM1d]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @same_but_materialized_trans]; [@Corelib; @Init; @Datatypes; @andb_true_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DiagLoopK; @wv_done]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM2_pre; @AS0DRVP_dpM2_pre; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM2_pre; @AS0DRVP_dpM2_pre; @dpM2_pre_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM2_pre; @AS0DRVP_dpM2_pre; @KS_dpM2_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM2d; @AS0DRVP_dpM2d; @aligned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM2d; @AS0DRVP_dpM2d; @dpM2d_conc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @asan; @Pm4DrvP_dpM2d; @AS0DRVP_dpM2d; @KS_dpM2d]].

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition DGM_CELLS : list (Z * Z * Z) := [(1485784, 1, 1); (1452704, 8, 1351328); (1482488, 8, 2147450880)].
(* [comment removed for export] *)
Definition Wfw (S a : Z) : Prop := S - 2320 <= a < S \/ 1463376 <= a < 1463392 \/ 1463400 <= a < 1463416 \/ 1463424 <= a < 1463432 \/ 1463504 <= a < 1463508.
(* [comment removed for export] *)
Definition stderrMA (MV : word -> option byte) : Prop :=
  rdn ASEGS MV (Z_to_bv 64 1463408) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 7071720)) /\ rdn ASEGS MV (Z_to_bv 64 1463424) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 7071720))
  /\ rdn ASEGS MV (Z_to_bv 64 1463376) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\ rdn ASEGS MV (Z_to_bv 64 1463384) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Fwrite.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_ok L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hdgm : incl DGM_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation rom := (seg_rom ASEGS).

  Lemma dgm_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) DGM_CELLS ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
  Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hdgm _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x6c0000).
    { unfold DGM_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fwrite1_run : forall LB LK cr A M (model : Model) R (S canz : Z) (msg : list byte) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 721572 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 141025 -> getr R 11%bv = Z_to_bv 64 31 -> getr R 12%bv = Z_to_bv 64 1 -> getr R 13%bv = Z_to_bv 64 1463368 ->
    (* WINDOW, old beside new, here and at every WIN1/WIN3 and the second lemma below: was
       [usp - 8388608 <= a]; DRV_ZWIN (Pm4DrvEntry). *)
    (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1449984 -> MV (Z_to_bv 64 i) = None) ->
    (forall i, 1463368 <= i < 1463608 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 7069712) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS (fun _ => None) (Z_to_bv 64 141025) 31 = Some msg ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    K [] ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall r, In r c_kept -> getr R' r = getr R r) ->
        stderrMA (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wfw S a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wfw S a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xb02a4) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x6b940) M rom) model) (t_emit (W 2 msg) K).
  Proof.
    intros LB LK cr A M model R S canz msg K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 R12 R13 WIN IMG SEIMG CAN DATA FD2 HK0 KONT.
    pose proof Hsp as Hsp'.
    assert (PCg : forall LK' cr' A' M' (model' : Model), dinvA LB LK' cr' A' M' model' -> forall a n v, In (a, n, v) DGM_CELLS ->
                  rdn ASEGS (mrestrict (ahid A' model') M') (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros LK' cr' A' M' model' D' a n v Hin; exact (dgm_cell_vis _ _ _ _ _ _ a n v D' Hin)).
    assert (ICe : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (1463368 <=? a) && (a + Z.of_nat n <=? 1463608) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply SEIMG. lia. }
    assert (WSG : forall (MVx : word -> option byte) a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MVx a (Z.of_nat n)).
    { intros MVx a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable sp0 Hsp M0 MVx a n W B1 B2). }

    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpM1_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (AWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 2304) 2304).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 2304) 2304); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (ADF : L5Defs.L5.defined MV (V 2%nat - 2304) 2304).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 2304) 2304); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (ST910488 : rdn ASEGS MV (Z_to_bv 64 1485784) 1 = Some [Z_to_bv 8 1]).
    { rewrite <- (ArtMem.art_bytes1 1 ltac:(lia)). exact (PCg _ _ _ _ _ D 1485784 1 1 ltac:(unfold DGM_CELLS; cbn [In]; tauto)). }
    destruct (AS0DRVP_dpM1_pre.dpM1_pre_conc fx R MV V HS64 Hcan R1 R2 R10 R11 R12 R13 HSr HSa AWR ADF IMG
                (WSG MV 1463376 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MV 1463384 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MV 1463400 8%nat ltac:(vm_compute; reflexivity) eq_refl)
                (WSG MV 1463408 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MV 1463424 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MV 1463504 4%nat ltac:(vm_compute; reflexivity) eq_refl)
                ST910488 (PCg _ _ _ _ _ D 1452704 8 1351328 ltac:(unfold DGM_CELLS; cbn [In]; tauto))
                (ICe 1463508 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl) (ICe 1463400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)
                (ICe 1463504 4%nat (word_to_le_bytes 4 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl) (ICe 1463368 4%nat (word_to_le_bytes 4 (Z_to_bv 64 5)) ltac:(img_rd) eq_refl)
                (ICe 1463456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 7071720)) ltac:(img_rd) eq_refl) (ICe 1463464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)
                (ICe 1463440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1348464)) ltac:(img_rd) eq_refl) CAN (ICe 1463488 4%nat (word_to_le_bytes 4 (Z_to_bv 64 2)) ltac:(img_rd) eq_refl)) as
      (fx1 & R1' & MV1 & AGR & _ & AFRZ & AMS & AKS & Ar1 & Ar2 & Ar6 & Ar8 & Ar9 & Ar10 & Ar11 & Ar13 & Ar14 & Ar17 & Ar18 & Ar19 & Ar20 & Ar21 & Ar22
       & Am2272 & Am2280 & Am2288 & Am2296 & Am2264 & Am2256 & Am2248 & Am2240 & Am2232 & Am2224 & Am2216 & Am2208 & Am2200 & Aa891992 & Aa891984 & Aa891968 & Aa891960 & Aa892008 & Aa892088
       & Am2184 & Am2176 & Am2168 & Am2160 & Am2152 & Am2144 & Am2136 & Am56 & Am48 & Am40 & Am32 & Am24 & Am16 & Am8 & Ad1 & Ad2 & Ad3).
    unfold V in AFRZ, AMS; cbn beta iota in AFRZ, AMS. cbn [V] in *.
    assert (FRA : forall a, 0 <= a < 2 ^ 64 -> ~ Wfw S a -> MV1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
    { intros a Ha Hn. apply AFRZ; [exact Ha | | | | | | |]; intros X; apply Hn; unfold Wfw; lia. }
    assert (WCWA : forall a, Wfw S a -> CWA sp0 LB a).
    { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
      exists 0x165448, 0x165740. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
    apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx1 R (Z_to_bv 64 0x6b940) R1' (Z_to_bv 64 0x1493f8) MV1 (Wfw S) _ D AMS AGR FRA WCWA).
    intros M1 model1 D1 SBM1 VIS1 FRM1.
    subst MV1. set (MVa := mrestrict (ahid A model1) M1) in *.
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (WIN a n); assumption).
    assert (IMG1 : forall i, 65536 <= i < 1449984 -> MVa (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRA; [apply IMG; exact Hi | lia | unfold Wfw; clear - Hsp' HS1 HS2 Hi; lia]. }
    assert (cellLa : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && (a + Z.of_nat n <=? 10000000) && ((a + Z.of_nat n <=? 1463376) || (1463508 <=? a) || ((1463432 <=? a) && (a + Z.of_nat n <=? 1463504))) = true -> rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.leb_le in Hb1, Hb2. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb3.
      apply (rdn_tr MV MVa _ _ _ Hr); [exact Hb1 | lia|].
      intros i Hi. apply FRA; [lia|]. unfold Wfw. clear - Hsp' HS1 HS2 Hb1 Hb2 Hb3 Hi. lia. }
    assert (DATA1 : rdn ASEGS MVa (Z_to_bv 64 141025) 31 = Some msg).
    { apply (img_cell MVa 141025 31 _ DATA); [lia | cbn; lia | intros i Hi; apply IMG1; cbn in Hi; lia]. }
    assert (FDc : rdn ASEGS MVa (Z_to_bv 64 1463488) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
    { apply (cellLa 1463488 4%nat); [|reflexivity]. exact (ICe 1463488 4%nat (word_to_le_bytes 4 (Z_to_bv 64 2)) ltac:(img_rd) eq_refl). }
    assert (FD2a : fd_lookup (m_fds model1) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (sbm_fds' _ _ SBM1); exact FD2).

    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D1) as (HH1 & HL1 & HA1 & HM1 & Hh1).
    set (qlo := S - 2296) in *.
    assert (Hq : 0 <= qlo /\ qlo <= qlo + 32 /\ qlo + 32 + 16 <= 2 ^ 47) by (unfold qlo; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1463368 /\ (1463368 + 124 <= qlo \/ qlo + 32 + 16 <= 1463368 + 120) /\ 1463368 + 124 < 2 ^ 63) by (unfold qlo; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, qlo <= x < qlo + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model1) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); unfold qlo in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (LENm : length msg = 31%nat) by (exact (PropExec.rdn_length _ _ _ _ _ DATA)).
    unfold W. replace (map (WriteEv (Z_to_bv 64 2)) msg) with (map (WriteEv (Z_to_bv 64 2)) (msg ++ [])) by (rewrite app_nil_r; reflexivity).
    apply (wv_loop scfg (ahid A model1) A HH1 (m_vm_lazy model1) HL1 HA1 1463368 2 ltac:(lia) qlo (qlo + 32) Hq Hf NLq K HK0 31%nat true R1' M1 model1 (S - 2280) 1 141025 31 0 0 msg []).
    { rewrite length_app, LENm. cbn. lia. }
    { reflexivity. }
    { exact HM1. }
    { exact Hh1. }
    { exact FD2a. }
    { exact (di_rdr _ _ _ _ _ _ _ _ _ _ D1). }
    { unfold wv_regs. split; [exact Ar17|]. split; [exact Ar10|]. split; [exact Ar11|].
      split; [eapply eq_trans; [exact (AKS 12%nat ltac:(unfold AS0DRVP_dpM1_pre.KS_dpM1_pre; cbn [In]; repeat first [left; reflexivity | right])) | exact R12]|].
      split; [exact Ar9|]. split; [exact Ar18|]. split; [exact Ar22 | exact Ar19]. }
    { fold MVa. unfold wv_iov. split; [unfold qlo; lia|]. split; [unfold qlo; lia|]. split; [left; reflexivity|].
      split; [exact Am2280|]. split; [replace (S - 2280 + 8) with (S - 2272) by ring; exact Am2272|].
      split; [replace (Z_to_bv 64 (S - 2280)) with (Z_to_bv 64 (S - 2280 + 0)) by (f_equal; lia); apply (WIN1 (S - 2280) 16); [clear - Hsp' HS1 HS2; lia | clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold qlo; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA1|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); lia|].
      split; [intros _; split; reflexivity|]. intros X; discriminate X. }
    { lia. }
    { exact FDc. }

    intros R3 M3 model3 MI3 SBM3 KR3 FRM3 FRV3 GRM3 GRV3.
    assert (D3 : dinvA LB LK cr A M3 model3).
    { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M1 M3 model1 model3 D1).
      - intros a Ha Hn. apply FRM3; [exact Ha|]. intros X. apply Hn. unfold CWA. right; left. unfold qlo in X. clear - Hsp' HS1 HS2 X. lia.
      - exact GRM3.
      - exact (sbm_vml _ _ SBM3).
      - exact MI3.
      - rewrite (sbm_halted_eq _ _ SBM3). exact Hh1.
      - exact (sbm_rdrA _ _ SBM3). }
    pose proof (ahid_sbm A model1 model3 SBM3) as AH3.
    set (MVc := mrestrict (ahid A model3) M3) in *.
    assert (EQc : mrestrict (ahid A model1) M3 = MVc) by (unfold MVc; rewrite AH3; reflexivity).
    rewrite EQc in FRV3, GRV3. fold MVa in FRV3, GRV3.
    set (SC := S - 2304) in *.
    assert (cellA : forall off k (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 2304) && (Z.of_nat n <=? k) && (k <=? 2264) = true -> rdn ASEGS MVc (Z_to_bv 64 (SC + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (SC + off) with (S - k) by (unfold SC; lia).
      apply (rdn_tr MVa MVc _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold qlo; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (cellL : forall a (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && (a + Z.of_nat n <=? 10000000) = true -> rdn ASEGS MVc (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb1 & Hb2). apply Z.leb_le in Hb1, Hb2.
      apply (rdn_tr MVa MVc _ _ _ Hr); [exact Hb1 | lia|].
      intros i Hi. apply FRV3; unfold qlo; clear - Hsp' HS1 HS2 Hb1 Hb2 Hi; lia. }
    assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVc (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVa MVc _ GRV3); apply (WIN1 a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1449984 -> MVc (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [apply IMG1; exact Hi | lia | unfold qlo; clear - Hsp' HS1 HS2 Hi; lia]. }
    assert (SH0 : forall a, a = 2147468504 -> rdn ASEGS MVc (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { intros a Ha. apply Pm4ArtFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ ((a - 2147450880) * 8) 64 _ D3); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (R3k : forall r : reg, In r WV_KEEP -> getr R3 r = getr R1' r) by exact KR3.
    set (VC := fun n : nat => match n with
               | 2%nat => SC | 40%nat => canz | 33%nat => 140737488355311 | 34%nat => 0
               | 8%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 8))) | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 111%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 11)))
               | 112%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 12))) | 113%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 13)))
               | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18))) | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))
               | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20))) | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Cg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VC 2%nat)) by (eapply eq_trans; [exact (R3k 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Ar2]).
    assert (Cg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 31) by (eapply eq_trans; [exact (R3k 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Ar8]).
    assert (Cg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1463368) by (eapply eq_trans; [exact (R3k 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Ar9]).
    assert (Cg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7069712) by (eapply eq_trans; [exact (R3k 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Ar21]).
    assert (Cg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VC 110%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg11 : getr R3 (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 (VC 111%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg12 : getr R3 (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 (VC 112%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg13 : getr R3 (Z_to_bv 5 (Z.of_nat 13)) = Z_to_bv 64 (VC 113%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VC 118%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VC 119%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VC 120%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VC 122%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HSC : 0 <= VC 2%nat < 2 ^ 64) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
    assert (HSCr : 140735332552704 <= VC 2%nat <= 140737488355328) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
    assert (HSCa : AS0DRVP_dpM1d.aligned (VC 2%nat) 16).
    { cbn [VC]. unfold AS0DRVP_dpM1d.aligned, SC. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (CWR : L5Defs.L5.writable ASEGS MVc (VC 2%nat - 16) 16).
    { cbn [VC]. intros d k Hd Hk. apply (WIN3 (SC - 16) 16); unfold SC; clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MVc (VC 2%nat - 16) 16).
    { cbn [VC]. intros i Hi. apply (store_ok_defined sp0); [unfold SC; clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (SC - 16) 16); unfold SC; clear - Hsp' HS1 HS2 Hi; lia. }
    assert (Cv160 : L5Defs.L5.u64_at ASEGS MVc (VC 2%nat + 160) (VC 2%nat + 2304)).
    { cbn [VC]. replace (SC + 2304) with S by (unfold SC; ring). exact (cellA 160 2144 _ _ Am2144 eq_refl). }
    destruct (AS0DRVP_dpM1d.dpM1d_conc fx1 R3 MVc VC
         HSC (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) ltac:(cbn [VC]; lia) ltac:(cbn [VC]; lia) Hcan
         (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
         Cg2 Cg8 Cg9 Cg10 Cg11 Cg12 Cg13 Cg18 Cg19 Cg20 Cg21 Cg22 HSCr HSCa CWR CDF IMG3
         ltac:(cbn [VC]; lia) ltac:(cbn [VC]; lia) ltac:(cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia)
         (SH0 2147468504 eq_refl)
         (WSG MVc 1463400 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MVc 1463408 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MVc 1463424 8%nat ltac:(vm_compute; reflexivity) eq_refl)
         (cellL _ _ _ (cellLa _ _ _ (ICe 1463456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 7071720)) ltac:(img_rd) eq_refl) eq_refl) eq_refl)
         (cellL _ _ _ (cellLa _ _ _ (ICe 1463464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl) eq_refl) eq_refl)
         (cellL _ _ _ (cellLa _ _ _ CAN eq_refl) eq_refl)
         (cellA 40 2264 _ _ Am2264 eq_refl) (cellA 104 2200 _ _ Am2200 eq_refl) (cellA 96 2208 _ _ Am2208 eq_refl) (cellA 88 2216 _ _ Am2216 eq_refl) (cellA 80 2224 _ _ Am2224 eq_refl)
         (cellA 72 2232 _ _ Am2232 eq_refl) (cellA 64 2240 _ _ Am2240 eq_refl) (cellA 56 2248 _ _ Am2248 eq_refl) (cellA 48 2256 _ _ Am2256 eq_refl)
         (cellA 168 2136 _ _ Am2136 eq_refl) Cv160 (cellA 152 2152 _ _ Am2152 eq_refl) (cellA 144 2160 _ _ Am2160 eq_refl) (cellA 136 2168 _ _ Am2168 eq_refl)
         (cellA 128 2176 _ _ Am2176 eq_refl) (cellA 120 2184 _ _ Am2184 eq_refl)
         (PCg _ _ _ _ _ D3 1482488 8 2147450880 ltac:(unfold DGM_CELLS; cbn [In]; tauto))
         (cellA 2296 8 _ _ Am8 eq_refl) (cellA 2288 16 _ _ Am16 eq_refl) (cellA 2280 24 _ _ Am24 eq_refl) (cellA 2272 32 _ _ Am32 eq_refl)
         (cellA 2264 40 _ _ Am40 eq_refl) (cellA 2256 48 _ _ Am48 eq_refl) (cellA 2248 56 _ _ Am56 eq_refl)) as
      (fx3 & R4 & MV4 & CGR & _ & CFRZ & CMS & CKS & Cr1 & Cr2 & Cr8 & Cr9 & Cr10 & Cr11 & Cr12 & Cr13 & Cr14 & Cr15 & Cr18 & Cr19 & Cr20 & Cr21 & Cr22 & Ca892008 & Ca891992 & Ca891984).
    unfold VC in CFRZ, CMS; cbn beta iota in CFRZ, CMS. cbn [VC] in *.
    set (WC := fun a : Z => SC - 16 <= a < SC \/ 1463400 <= a < 1463416 \/ 1463424 <= a < 1463432).
    assert (FRC : forall a, 0 <= a < 2 ^ 64 -> ~ WC a -> MV4 (Z_to_bv 64 a) = MVc (Z_to_bv 64 a)).
    { intros a Ha Hn. apply CFRZ; [exact Ha | | | |]; intros X; apply Hn; unfold WC; clear - X; lia. }
    apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M3 model3 fx1 fx3 R3 (Z_to_bv 64 0x149404) R4 (Z_to_bv 64 0xb02a4) MV4 WC _ D3 CMS CGR FRC).
    { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; unfold SC in Ha; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
      exists 0x165448, 0x165740. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
    intros M4 model4 D4 SBM4 VIS4 FRM4.
    apply (KONT fx3 R4 M4 model4 D4).
    + exact (same_but_materialized_trans _ _ _ SBM1 (same_but_materialized_trans _ _ _ SBM3 SBM4)).
    +
      assert (KK : forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))).
      { intros x Hx. cbn [In] in Hx.
        repeat (destruct Hx as [<-|Hx];
                [eapply eq_trans; [apply CKS; unfold AS0DRVP_dpM1d.KS_dpM1d; cbn [In]; repeat first [left; reflexivity | right]|];
                 eapply eq_trans; [apply R3k; unfold WV_KEEP; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]|];
                 apply AKS; unfold AS0DRVP_dpM1_pre.KS_dpM1_pre; cbn [In]; repeat first [left; reflexivity | right]|]).
        destruct Hx. }
      intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr2|]; rewrite R2; f_equal; unfold SC; ring|].
      destruct Hr as [<-|Hr]; [exact (KK 3%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 4%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr8|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr9|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr18|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr19|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr20|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr21|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr22|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [exact (KK 23%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 24%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 25%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 26%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 27%nat ltac:(cbn [In]; tauto))|].
      destruct Hr.
    +
      rewrite VIS4. unfold stderrMA. split; [exact Ca891992|]. split; [exact Ca892008|].
      assert (T4 : forall a bs, rdn ASEGS MVa (Z_to_bv 64 a) 8 = Some bs -> (1463376 <=? a) && (a <=? 1463384) = true -> rdn ASEGS MV4 (Z_to_bv 64 a) 8 = Some bs).
      { intros a bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2.
        apply (rdn_tr MVc MV4 _ _ _ (cellL _ _ _ Hr ltac:(apply andb_true_intro; split; apply Z.leb_le; cbn; lia))); [lia | cbn; lia|].
        intros i Hi. apply FRC; [cbn in Hi; lia|]. unfold WC, SC. cbn in Hi. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
      split; [exact (T4 _ _ Aa891960 eq_refl) | exact (T4 _ _ Aa891968 eq_refl)].
    +
      intros a Ha Hn.
      rewrite FRM4 by (exact Ha || (intros X; apply Hn; unfold Wfw, WC, SC in *; clear - Hsp' HS1 HS2 X; lia)).
      rewrite FRM3 by (exact Ha || (intros X; apply Hn; unfold Wfw, qlo in *; clear - Hsp' HS1 HS2 X; lia)).
      apply FRM1; [exact Ha | exact Hn].
    +
      intros a Ha Hn. rewrite VIS4.
      rewrite FRC by (exact Ha || (intros X; apply Hn; unfold Wfw, WC, SC in *; clear - Hsp' HS1 HS2 X; lia)).
      rewrite FRV3 by (exact Ha || (intros X; apply Hn; unfold Wfw, qlo in *; clear - Hsp' HS1 HS2 X; lia)).
      apply FRA; [exact Ha | exact Hn].
    + intros a Ha. rewrite VIS4. apply CGR. apply GRV3. apply AGR. exact Ha.
  Qed.

  Lemma fwrite2_run : forall LB LK cr A M (model : Model) R (S canz : Z) (msg : list byte) K,
    dinvA LB LK cr A M model ->
    let MV := mrestrict (ahid A model) M in
    usp - 4096 <= S -> S + 32 <= usp -> S mod 16 = 0 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 721572 -> getr R 2%bv = Z_to_bv 64 S -> getr R 10%bv = Z_to_bv 64 91848 -> getr R 11%bv = Z_to_bv 64 31 -> getr R 12%bv = Z_to_bv 64 1 -> getr R 13%bv = Z_to_bv 64 1463368 ->
    (forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true) ->
    (forall i, 65536 <= i < 1449984 -> MV (Z_to_bv 64 i) = None) ->
    (forall i, 1463368 <= i < 1463608 -> MV (Z_to_bv 64 i) = None) ->
    rdn ASEGS MV (Z_to_bv 64 7069712) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    rdn ASEGS (fun _ => None) (Z_to_bv 64 91848) 31 = Some msg ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    K [] ->
    (forall (fx' : PropExec.FPState) R' M1 (model1 : Model),
        dinvA LB LK cr A M1 model1 -> same_but_materialized model model1 ->
        (forall r, In r c_kept -> getr R' r = getr R r) ->
        stderrMA (mrestrict (ahid A model1) M1) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wfw S a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        (forall a, 0 <= a < 2 ^ 64 -> ~ Wfw S a -> mrestrict (ahid A model1) M1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) ->
        (forall a : word, MV a <> None -> mrestrict (ahid A model1) M1 a <> None) ->
        srealizes ASEGS scfg (mkCfg (@mkst fx' R' (Z_to_bv 64 0xb02a4) M1 rom) model1) K) ->
    srealizes ASEGS scfg (mkCfg (@mkst fx R (Z_to_bv 64 0x6b940) M rom) model) (t_emit (W 2 msg) K).
  Proof.
    intros LB LK cr A M model R S canz msg K D MV HS1 HS2 HS16 Hcan R1 R2 R10 R11 R12 R13 WIN IMG SEIMG CAN DATA FD2 HK0 KONT.
    pose proof Hsp as Hsp'.
    assert (PCg : forall LK' cr' A' M' (model' : Model), dinvA LB LK' cr' A' M' model' -> forall a n v, In (a, n, v) DGM_CELLS ->
                  rdn ASEGS (mrestrict (ahid A' model') M') (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros LK' cr' A' M' model' D' a n v Hin; exact (dgm_cell_vis _ _ _ _ _ _ a n v D' Hin)).
    assert (ICe : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (1463368 <=? a) && (a + Z.of_nat n <=? 1463608) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hc. apply andb_prop in Hc as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply SEIMG. lia. }
    assert (WSG : forall (MVx : word -> option byte) a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MVx a (Z.of_nat n)).
    { intros MVx a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable sp0 Hsp M0 MVx a n W B1 B2). }

    set (V := fun n : nat => match n with 2%nat => S | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpM2_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (AWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 2304) 2304).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 2304) 2304); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (ADF : L5Defs.L5.defined MV (V 2%nat - 2304) 2304).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 2304) 2304); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (ST910488 : rdn ASEGS MV (Z_to_bv 64 1485784) 1 = Some [Z_to_bv 8 1]).
    { rewrite <- (ArtMem.art_bytes1 1 ltac:(lia)). exact (PCg _ _ _ _ _ D 1485784 1 1 ltac:(unfold DGM_CELLS; cbn [In]; tauto)). }
    destruct (AS0DRVP_dpM2_pre.dpM2_pre_conc fx R MV V HS64 Hcan R1 R2 R10 R11 R12 R13 HSr HSa AWR ADF IMG
                (WSG MV 1463376 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MV 1463384 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MV 1463400 8%nat ltac:(vm_compute; reflexivity) eq_refl)
                (WSG MV 1463408 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MV 1463424 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MV 1463504 4%nat ltac:(vm_compute; reflexivity) eq_refl)
                ST910488 (PCg _ _ _ _ _ D 1452704 8 1351328 ltac:(unfold DGM_CELLS; cbn [In]; tauto))
                (ICe 1463508 4%nat (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) ltac:(img_rd) eq_refl) (ICe 1463400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)
                (ICe 1463504 4%nat (word_to_le_bytes 4 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl) (ICe 1463368 4%nat (word_to_le_bytes 4 (Z_to_bv 64 5)) ltac:(img_rd) eq_refl)
                (ICe 1463456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 7071720)) ltac:(img_rd) eq_refl) (ICe 1463464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl)
                (ICe 1463440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1348464)) ltac:(img_rd) eq_refl) CAN (ICe 1463488 4%nat (word_to_le_bytes 4 (Z_to_bv 64 2)) ltac:(img_rd) eq_refl)) as
      (fx1 & R1' & MV1 & AGR & _ & AFRZ & AMS & AKS & Ar1 & Ar2 & Ar6 & Ar8 & Ar9 & Ar10 & Ar11 & Ar13 & Ar14 & Ar17 & Ar18 & Ar19 & Ar20 & Ar21 & Ar22
       & Am2272 & Am2280 & Am2288 & Am2296 & Am2264 & Am2256 & Am2248 & Am2240 & Am2232 & Am2224 & Am2216 & Am2208 & Am2200 & Aa891992 & Aa891984 & Aa891968 & Aa891960 & Aa892008 & Aa892088
       & Am2184 & Am2176 & Am2168 & Am2160 & Am2152 & Am2144 & Am2136 & Am56 & Am48 & Am40 & Am32 & Am24 & Am16 & Am8 & Ad1 & Ad2 & Ad3).
    unfold V in AFRZ, AMS; cbn beta iota in AFRZ, AMS. cbn [V] in *.
    assert (FRA : forall a, 0 <= a < 2 ^ 64 -> ~ Wfw S a -> MV1 (Z_to_bv 64 a) = MV (Z_to_bv 64 a)).
    { intros a Ha Hn. apply AFRZ; [exact Ha | | | | | | |]; intros X; apply Hn; unfold Wfw; lia. }
    assert (WCWA : forall a, Wfw S a -> CWA sp0 LB a).
    { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
      exists 0x165448, 0x165740. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
    apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model fx fx1 R (Z_to_bv 64 0x6b940) R1' (Z_to_bv 64 0x1493f8) MV1 (Wfw S) _ D AMS AGR FRA WCWA).
    intros M1 model1 D1 SBM1 VIS1 FRM1.
    subst MV1. set (MVa := mrestrict (ahid A model1) M1) in *.
    assert (WIN1 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVa (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MVa _ AGR); apply (WIN a n); assumption).
    assert (IMG1 : forall i, 65536 <= i < 1449984 -> MVa (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRA; [apply IMG; exact Hi | lia | unfold Wfw; clear - Hsp' HS1 HS2 Hi; lia]. }
    assert (cellLa : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && (a + Z.of_nat n <=? 10000000) && ((a + Z.of_nat n <=? 1463376) || (1463508 <=? a) || ((1463432 <=? a) && (a + Z.of_nat n <=? 1463504))) = true -> rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.leb_le in Hb1, Hb2. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in Hb3.
      apply (rdn_tr MV MVa _ _ _ Hr); [exact Hb1 | lia|].
      intros i Hi. apply FRA; [lia|]. unfold Wfw. clear - Hsp' HS1 HS2 Hb1 Hb2 Hb3 Hi. lia. }
    assert (DATA1 : rdn ASEGS MVa (Z_to_bv 64 91848) 31 = Some msg).
    { apply (img_cell MVa 91848 31 _ DATA); [lia | cbn; lia | intros i Hi; apply IMG1; cbn in Hi; lia]. }
    assert (FDc : rdn ASEGS MVa (Z_to_bv 64 1463488) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2))).
    { apply (cellLa 1463488 4%nat); [|reflexivity]. exact (ICe 1463488 4%nat (word_to_le_bytes 4 (Z_to_bv 64 2)) ltac:(img_rd) eq_refl). }
    assert (FD2a : fd_lookup (m_fds model1) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (sbm_fds' _ _ SBM1); exact FD2).

    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D1) as (HH1 & HL1 & HA1 & HM1 & Hh1).
    set (qlo := S - 2296) in *.
    assert (Hq : 0 <= qlo /\ qlo <= qlo + 32 /\ qlo + 32 + 16 <= 2 ^ 47) by (unfold qlo; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1463368 /\ (1463368 + 124 <= qlo \/ qlo + 32 + 16 <= 1463368 + 120) /\ 1463368 + 124 < 2 ^ 63) by (unfold qlo; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, qlo <= x < qlo + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model1) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); unfold qlo in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (LENm : length msg = 31%nat) by (exact (PropExec.rdn_length _ _ _ _ _ DATA)).
    unfold W. replace (map (WriteEv (Z_to_bv 64 2)) msg) with (map (WriteEv (Z_to_bv 64 2)) (msg ++ [])) by (rewrite app_nil_r; reflexivity).
    apply (wv_loop scfg (ahid A model1) A HH1 (m_vm_lazy model1) HL1 HA1 1463368 2 ltac:(lia) qlo (qlo + 32) Hq Hf NLq K HK0 31%nat true R1' M1 model1 (S - 2280) 1 91848 31 0 0 msg []).
    { rewrite length_app, LENm. cbn. lia. }
    { reflexivity. }
    { exact HM1. }
    { exact Hh1. }
    { exact FD2a. }
    { exact (di_rdr _ _ _ _ _ _ _ _ _ _ D1). }
    { unfold wv_regs. split; [exact Ar17|]. split; [exact Ar10|]. split; [exact Ar11|].
      split; [eapply eq_trans; [exact (AKS 12%nat ltac:(unfold AS0DRVP_dpM2_pre.KS_dpM2_pre; cbn [In]; repeat first [left; reflexivity | right])) | exact R12]|].
      split; [exact Ar9|]. split; [exact Ar18|]. split; [exact Ar22 | exact Ar19]. }
    { fold MVa. unfold wv_iov. split; [unfold qlo; lia|]. split; [unfold qlo; lia|]. split; [left; reflexivity|].
      split; [exact Am2280|]. split; [replace (S - 2280 + 8) with (S - 2272) by ring; exact Am2272|].
      split; [replace (Z_to_bv 64 (S - 2280)) with (Z_to_bv 64 (S - 2280 + 0)) by (f_equal; lia); apply (WIN1 (S - 2280) 16); [clear - Hsp' HS1 HS2; lia | clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold qlo; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA1|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D1); lia|].
      split; [intros _; split; reflexivity|]. intros X; discriminate X. }
    { lia. }
    { exact FDc. }

    intros R3 M3 model3 MI3 SBM3 KR3 FRM3 FRV3 GRM3 GRV3.
    assert (D3 : dinvA LB LK cr A M3 model3).
    { apply (dinv_frame scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M1 M3 model1 model3 D1).
      - intros a Ha Hn. apply FRM3; [exact Ha|]. intros X. apply Hn. unfold CWA. right; left. unfold qlo in X. clear - Hsp' HS1 HS2 X. lia.
      - exact GRM3.
      - exact (sbm_vml _ _ SBM3).
      - exact MI3.
      - rewrite (sbm_halted_eq _ _ SBM3). exact Hh1.
      - exact (sbm_rdrA _ _ SBM3). }
    pose proof (ahid_sbm A model1 model3 SBM3) as AH3.
    set (MVc := mrestrict (ahid A model3) M3) in *.
    assert (EQc : mrestrict (ahid A model1) M3 = MVc) by (unfold MVc; rewrite AH3; reflexivity).
    rewrite EQc in FRV3, GRV3. fold MVa in FRV3, GRV3.
    set (SC := S - 2304) in *.
    assert (cellA : forall off k (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 2304) && (Z.of_nat n <=? k) && (k <=? 2264) = true -> rdn ASEGS MVc (Z_to_bv 64 (SC + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (SC + off) with (S - k) by (unfold SC; lia).
      apply (rdn_tr MVa MVc _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold qlo; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (cellL : forall a (n : nat) bs, rdn ASEGS MVa (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && (a + Z.of_nat n <=? 10000000) = true -> rdn ASEGS MVc (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (Hb1 & Hb2). apply Z.leb_le in Hb1, Hb2.
      apply (rdn_tr MVa MVc _ _ _ Hr); [exact Hb1 | lia|].
      intros i Hi. apply FRV3; unfold qlo; clear - Hsp' HS1 HS2 Hb1 Hb2 Hi; lia. }
    assert (WIN3 : forall a n, usp - DRV_ZWIN <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MVc (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MVa MVc _ GRV3); apply (WIN1 a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1449984 -> MVc (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [apply IMG1; exact Hi | lia | unfold qlo; clear - Hsp' HS1 HS2 Hi; lia]. }
    assert (SH0 : forall a, a = 2147462360 -> rdn ASEGS MVc (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { intros a Ha. apply Pm4ArtFsInv.cell_zero_bytes; [right; reflexivity | lia | lia |]. intros j Hj. unfold byte_at.
      apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ ((a - 2147450880) * 8) 64 _ D3); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (R3k : forall r : reg, In r WV_KEEP -> getr R3 r = getr R1' r) by exact KR3.
    set (VC := fun n : nat => match n with
               | 2%nat => SC | 40%nat => canz | 33%nat => 140737488355311 | 34%nat => 0
               | 8%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 8))) | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 111%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 11)))
               | 112%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 12))) | 113%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 13)))
               | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18))) | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))
               | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20))) | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Cg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VC 2%nat)) by (eapply eq_trans; [exact (R3k 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Ar2]).
    assert (Cg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 31) by (eapply eq_trans; [exact (R3k 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Ar8]).
    assert (Cg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1463368) by (eapply eq_trans; [exact (R3k 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Ar9]).
    assert (Cg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 7069712) by (eapply eq_trans; [exact (R3k 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Ar21]).
    assert (Cg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VC 110%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg11 : getr R3 (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 (VC 111%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg12 : getr R3 (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 (VC 112%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg13 : getr R3 (Z_to_bv 5 (Z.of_nat 13)) = Z_to_bv 64 (VC 113%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VC 118%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VC 119%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VC 120%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Cg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VC 122%nat)) by (cbn [VC]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HSC : 0 <= VC 2%nat < 2 ^ 64) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
    assert (HSCr : 140735332552704 <= VC 2%nat <= 140737488355328) by (cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia).
    assert (HSCa : AS0DRVP_dpM2d.aligned (VC 2%nat) 16).
    { cbn [VC]. unfold AS0DRVP_dpM2d.aligned, SC. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (CWR : L5Defs.L5.writable ASEGS MVc (VC 2%nat - 16) 16).
    { cbn [VC]. intros d k Hd Hk. apply (WIN3 (SC - 16) 16); unfold SC; clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MVc (VC 2%nat - 16) 16).
    { cbn [VC]. intros i Hi. apply (store_ok_defined sp0); [unfold SC; clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (SC - 16) 16); unfold SC; clear - Hsp' HS1 HS2 Hi; lia. }
    assert (Cv160 : L5Defs.L5.u64_at ASEGS MVc (VC 2%nat + 160) (VC 2%nat + 2304)).
    { cbn [VC]. replace (SC + 2304) with S by (unfold SC; ring). exact (cellA 160 2144 _ _ Am2144 eq_refl). }
    destruct (AS0DRVP_dpM2d.dpM2d_conc fx1 R3 MVc VC
         HSC (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) ltac:(cbn [VC]; lia) ltac:(cbn [VC]; lia) Hcan
         (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
         Cg2 Cg8 Cg9 Cg10 Cg11 Cg12 Cg13 Cg18 Cg19 Cg20 Cg21 Cg22 HSCr HSCa CWR CDF IMG3
         ltac:(cbn [VC]; lia) ltac:(cbn [VC]; lia) ltac:(cbn [VC]; unfold SC; clear - Hsp' HS1 HS2; lia)
         (SH0 2147462360 eq_refl)
         (WSG MVc 1463400 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MVc 1463408 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG MVc 1463424 8%nat ltac:(vm_compute; reflexivity) eq_refl)
         (cellL _ _ _ (cellLa _ _ _ (ICe 1463456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 7071720)) ltac:(img_rd) eq_refl) eq_refl) eq_refl)
         (cellL _ _ _ (cellLa _ _ _ (ICe 1463464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 0)) ltac:(img_rd) eq_refl) eq_refl) eq_refl)
         (cellL _ _ _ (cellLa _ _ _ CAN eq_refl) eq_refl)
         (cellA 40 2264 _ _ Am2264 eq_refl) (cellA 104 2200 _ _ Am2200 eq_refl) (cellA 96 2208 _ _ Am2208 eq_refl) (cellA 88 2216 _ _ Am2216 eq_refl) (cellA 80 2224 _ _ Am2224 eq_refl)
         (cellA 72 2232 _ _ Am2232 eq_refl) (cellA 64 2240 _ _ Am2240 eq_refl) (cellA 56 2248 _ _ Am2248 eq_refl) (cellA 48 2256 _ _ Am2256 eq_refl)
         (cellA 168 2136 _ _ Am2136 eq_refl) Cv160 (cellA 152 2152 _ _ Am2152 eq_refl) (cellA 144 2160 _ _ Am2160 eq_refl) (cellA 136 2168 _ _ Am2168 eq_refl)
         (cellA 128 2176 _ _ Am2176 eq_refl) (cellA 120 2184 _ _ Am2184 eq_refl)
         (PCg _ _ _ _ _ D3 1482488 8 2147450880 ltac:(unfold DGM_CELLS; cbn [In]; tauto))
         (cellA 2296 8 _ _ Am8 eq_refl) (cellA 2288 16 _ _ Am16 eq_refl) (cellA 2280 24 _ _ Am24 eq_refl) (cellA 2272 32 _ _ Am32 eq_refl)
         (cellA 2264 40 _ _ Am40 eq_refl) (cellA 2256 48 _ _ Am48 eq_refl) (cellA 2248 56 _ _ Am56 eq_refl)) as
      (fx3 & R4 & MV4 & CGR & _ & CFRZ & CMS & CKS & Cr1 & Cr2 & Cr8 & Cr9 & Cr10 & Cr11 & Cr12 & Cr13 & Cr14 & Cr15 & Cr18 & Cr19 & Cr20 & Cr21 & Cr22 & Ca892008 & Ca891992 & Ca891984).
    unfold VC in CFRZ, CMS; cbn beta iota in CFRZ, CMS. cbn [VC] in *.
    set (WC := fun a : Z => SC - 16 <= a < SC \/ 1463400 <= a < 1463416 \/ 1463424 <= a < 1463432).
    assert (FRC : forall a, 0 <= a < 2 ^ 64 -> ~ WC a -> MV4 (Z_to_bv 64 a) = MVc (Z_to_bv 64 a)).
    { intros a Ha Hn. apply CFRZ; [exact Ha | | | |]; intros X; apply Hn; unfold WC; clear - X; lia. }
    apply (drv_piece scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M3 model3 fx1 fx3 R3 (Z_to_bv 64 0x149404) R4 (Z_to_bv 64 0xb02a4) MV4 WC _ D3 CMS CGR FRC).
    { intros a Ha. unfold CWA. destruct Ha as [Ha|Ha]; [right; left; unfold SC in Ha; clear - Hsp' HS1 HS2 Ha; lia|]. right; right.
      exists 0x165448, 0x165740. split; [unfold IMG_W_A; cbn [In]; tauto | clear - Ha; lia]. }
    intros M4 model4 D4 SBM4 VIS4 FRM4.
    apply (KONT fx3 R4 M4 model4 D4).
    + exact (same_but_materialized_trans _ _ _ SBM1 (same_but_materialized_trans _ _ _ SBM3 SBM4)).
    +
      assert (KK : forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R4 (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x))).
      { intros x Hx. cbn [In] in Hx.
        repeat (destruct Hx as [<-|Hx];
                [eapply eq_trans; [apply CKS; unfold AS0DRVP_dpM2d.KS_dpM2d; cbn [In]; repeat first [left; reflexivity | right]|];
                 eapply eq_trans; [apply R3k; unfold WV_KEEP; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]|];
                 apply AKS; unfold AS0DRVP_dpM2_pre.KS_dpM2_pre; cbn [In]; repeat first [left; reflexivity | right]|]).
        destruct Hx. }
      intros r Hr. unfold c_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr2|]; rewrite R2; f_equal; unfold SC; ring|].
      destruct Hr as [<-|Hr]; [exact (KK 3%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 4%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr8|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr9|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr18|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr19|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr20|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr21|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [eapply eq_trans; [exact Cr22|]; apply Z_to_bv_bv_unsigned|].
      destruct Hr as [<-|Hr]; [exact (KK 23%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 24%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 25%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 26%nat ltac:(cbn [In]; tauto))|].
      destruct Hr as [<-|Hr]; [exact (KK 27%nat ltac:(cbn [In]; tauto))|].
      destruct Hr.
    +
      rewrite VIS4. unfold stderrMA. split; [exact Ca891992|]. split; [exact Ca892008|].
      assert (T4 : forall a bs, rdn ASEGS MVa (Z_to_bv 64 a) 8 = Some bs -> (1463376 <=? a) && (a <=? 1463384) = true -> rdn ASEGS MV4 (Z_to_bv 64 a) 8 = Some bs).
      { intros a bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2.
        apply (rdn_tr MVc MV4 _ _ _ (cellL _ _ _ Hr ltac:(apply andb_true_intro; split; apply Z.leb_le; cbn; lia))); [lia | cbn; lia|].
        intros i Hi. apply FRC; [cbn in Hi; lia|]. unfold WC, SC. cbn in Hi. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
      split; [exact (T4 _ _ Aa891960 eq_refl) | exact (T4 _ _ Aa891968 eq_refl)].
    +
      intros a Ha Hn.
      rewrite FRM4 by (exact Ha || (intros X; apply Hn; unfold Wfw, WC, SC in *; clear - Hsp' HS1 HS2 X; lia)).
      rewrite FRM3 by (exact Ha || (intros X; apply Hn; unfold Wfw, qlo in *; clear - Hsp' HS1 HS2 X; lia)).
      apply FRM1; [exact Ha | exact Hn].
    +
      intros a Ha Hn. rewrite VIS4.
      rewrite FRC by (exact Ha || (intros X; apply Hn; unfold Wfw, WC, SC in *; clear - Hsp' HS1 HS2 X; lia)).
      rewrite FRV3 by (exact Ha || (intros X; apply Hn; unfold Wfw, qlo in *; clear - Hsp' HS1 HS2 X; lia)).
      apply FRA; [exact Ha | exact Hn].
    + intros a Ha. rewrite VIS4. apply CGR. apply GRV3. apply AGR. exact Ha.
  Qed.
End Fwrite.
End FPX_1.
