(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the reserved-interval ledger, the launch input's kernel build): changed AH, B2, I_FAKE and 107 more; added Hapc, Hbrk, Hfit and 23 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8ArtHandoffK.v, 588 lines within its lines 19-1152. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm4DefsK Pm4PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
  Pm4HandoffK Pm4ArtCellsK Pm4BssZeroK AsanNodesLibEK AsanNodesMmLibK HandoffLazyK.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface HeapIfaceA As0Tables ArtMem ArtRunsMem Pm4ArtLeaf Pm4ArtPoison Pm4ArtRzLog Pm4ArtAllocA Pm4ArtCls Pm4ArtDepotA Pm4ArtDepot
  ArtRuns ArtBridge Pm4ArtInitCache Pm4ArtInv Pm4ArtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmGlobKit.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @acs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @am_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffRolesK; @role]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @I_THREAD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @I_CTX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @I_FAKE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @I_PARR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @I_L2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @I_BLK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @I_DTLS]; [@Corelib; @Init; @Datatypes; @fst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @expr]; [@Corelib; @Numbers; @BinNums; @Z]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @split_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @spbE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @e_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @kn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bT]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ELit]; [@Corelib; @Numbers; @BinNums; @Z0]; [@Stdlib; @ZArith; @BinInt; @Z; @add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @env]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @AR]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @uE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @e_sp0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @topE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @botE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffRolesK; @rbase]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @ARN]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @as0_ar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @TP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @TSD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @LOFF]; [@Stdlib; @ZArith; @BinInt; @Z; @div]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @I_KSPACE]; [@Corelib; @Init; @Datatypes; @list]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @kentry]; [@Stdlib; @Lists; @List; @existsb]; [@Corelib; @Init; @Datatypes; @bool]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @saddr]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @false]; [@Corelib; @Init; @Datatypes; @andb]; [@Stdlib; @ZArith; @BinInt; @Z; @leb]; [@Corelib; @Init; @Datatypes; @option]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xlo]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @expr_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @am_len]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Init; @Datatypes; @snd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @a_vis]; [@Stdlib; @Lists; @List; @forallb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @art_sym_list]; [@Corelib; @Init; @Datatypes; @list_ind]; [@Corelib; @Init; @Logic; @eq]; [@Corelib; @Init; @Datatypes; @true]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @all_true]; [@Corelib; @Init; @Datatypes; @nil]; [@Corelib; @Init; @Logic; @I]; [@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @andb_prop]; [@Corelib; @Init; @Logic; @and]; [@Corelib; @Init; @Logic; @and_ind]; [@Corelib; @Init; @Logic; @conj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @hop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @hsplit]; [@Corelib; @Init; @Datatypes; @Some]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Init; @Datatypes; @app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @HSub]; [@Corelib; @Init; @Logic; @eq_ind]; [@Corelib; @Init; @Logic; @False]; [@Corelib; @Init; @Logic; @True]; [@Corelib; @Init; @Logic; @False_ind]; [@Corelib; @Init; @Datatypes; @None]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @HCons]; [@Corelib; @Init; @Logic; @eq_refl]; [@Corelib; @Init; @Logic; @f_equal]; [@stdpp; @tactics; @f_equal_help]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @expr_eqb_eq]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @E_RISX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @a_hlz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @hop_pre]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @hop_zone]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @vis_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @own_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @a_ghost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ealign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bBLK]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @vis_in]; [@Stdlib; @ZArith; @BinInt; @Z; @le]; [@Stdlib; @ZArith; @BinInt; @Z; @lt]; [@Stdlib; @ZArith; @BinInt; @Z; @pow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AgentLib; @u64_lit]; [@stdpp; @bitvector; @definitions; @bv_unsigned]; [@Corelib; @Numbers; @BinNums; @Npos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @edenot]; [@Corelib; @Numbers; @BinNums; @xH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0Tables; @AsanTab; @class_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0Tables; @AsanTab; @zrange]; [@Stdlib; @ZArith; @BinInt; @Z; @ltb_lt]; [@Corelib; @Init; @Logic; @proj1]; [@Stdlib; @Lists; @List; @In]; [@Stdlib; @Lists; @List; @forallb_forall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @As0Tables; @AsanTab; @in_ziota]; [@Stdlib; @ZArith; @BinInt; @Z; @to_nat]; [@Stdlib; @micromega; @ZMicromega; @ZArithProof]; [@Stdlib; @micromega; @VarMap; @Elt]; [@Stdlib; @micromega; @VarMap; @t]; [@Stdlib; @micromega; @Tauto; @IMPL]; [@Stdlib; @micromega; @RingMicromega; @Formula]; [@Stdlib; @micromega; @Tauto; @eKind]; [@Corelib; @Init; @Datatypes; @unit]; [@Stdlib; @micromega; @Tauto; @isProp]; [@Stdlib; @micromega; @Tauto; @AND]; [@Stdlib; @micromega; @Tauto; @A]; [@Stdlib; @micromega; @RingMicromega; @Build_Formula]; [@Stdlib; @micromega; @EnvRing; @PEc]; [@Stdlib; @micromega; @RingMicromega; @OpLe]; [@Stdlib; @micromega; @EnvRing; @PEX]; [@Corelib; @Init; @Datatypes; @tt]; [@Stdlib; @micromega; @RingMicromega; @OpLt]; [@Stdlib; @micromega; @EnvRing; @PEadd]; [@Stdlib; @micromega; @Tauto; @BFormula]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker_sound]; [@Stdlib; @micromega; @ZMicromega; @ZTautoChecker]; [@Stdlib; @micromega; @VarMap; @find]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4HandoffK; @as0_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @no_fog]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @a_maps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @hops_in_maps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @a_hna]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @vis_sh_wr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DefsK; @ASAN0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @vis_off_band]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @amap]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @amap_eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffBInvK; @M_LOW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffBInvK; @M_GAP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffBInvK; @M_HIGH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4HandoffK; @RESm0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffCellsK; @chk_word]; [@Corelib; @Init; @Logic; @proj2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @flat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @SA]; [@Stdlib; @ZArith; @BinInt; @Z; @of_nat]; [@stdpp; @bitvector; @definitions; @bv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @rdn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DefsK; @ASEGS0]; [@stdpp; @bitvector; @definitions; @Z_to_bv]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @word_to_le_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffCellsK; @hc_word]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanInitK; @LIMIT]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanInitK; @SINV0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4DefsK; @APH0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanInitK; @argH0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4PlanImagesK; @asan0_in_hull]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4PlanImagesK; @asan0_hull_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtMem; @cell]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @M; @loaded_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCellsK; @art_lit]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCellsK; @ART_LITW]; [@Corelib; @Init; @Logic; @ex]; [@Stdlib; @Lists; @List; @existsb_exists]; [@Corelib; @Init; @Logic; @ex_ind]; [@Stdlib; @ZArith; @BinInt; @Z; @eqb_eq]; [@Stdlib; @Arith; @PeanoNat; @Nat; @eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @cellL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffCellsK; @chk_zero]; [@Corelib; @Init; @Peano; @le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffCellsK; @hc_zero_cell]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffCellsK; @chk_wr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffCellsK; @hc_wr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtMem; @wr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @all_true_of]; [@Corelib; @Init; @Datatypes; @length]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @eaddz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bF]; [@Stdlib; @ZArith; @BinInt; @Z; @sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bL2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @tfE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @is_var_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @stE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @B1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @B2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @img_cover]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4BssZeroK; @DEP_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4BssZeroK; @DEP_HI]; [@Corelib; @Init; @Datatypes; @O]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @xlo_pos]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @lit_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bD]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @e_top]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @e_stk_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmGlobKit; @zruns]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @ART_IMG_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @ART_POISON]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @ART_IMG_HI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @glob_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @ART_GLOBALS]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff_rev]; [@Stdlib; @micromega; @ZifyClasses; @mkrel]; [@Corelib; @Init; @Logic; @iff_sym]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @is_nonneg]; [@Stdlib; @micromega; @SatDivMod; @Z_mod_nonneg_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @modulo]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_pos_nonneg]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_nonneg]; [@Stdlib; @micromega; @ZMicromega; @RatProof]; [@Stdlib; @micromega; @RingMicromega; @PsatzAdd]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulC]; [@Stdlib; @micromega; @EnvRing; @Pc]; [@Corelib; @Numbers; @BinNums; @Zneg]; [@Stdlib; @micromega; @RingMicromega; @PsatzIn]; [@Stdlib; @micromega; @ZMicromega; @DoneProof]; [@Stdlib; @micromega; @RingMicromega; @OpEq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @co_isp]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @vm_init_sp]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vmmaps]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @sp_window_lo]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @sp_window_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @e_sppg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @pagedown]; [@Stdlib; @micromega; @Tauto; @X]; [@Stdlib; @micromega; @EnvRing; @PEpow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @sym_all]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @amap_eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @uE_lit]; [@Stdlib; @micromega; @VarMap; @Empty]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffRolesK; @rlen]; [@Corelib; @Init; @Peano; @lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffRolesK; @role_lit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffRolesK; @role_geo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @nofog]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @len17]; [@Corelib; @Init; @Logic; @or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @img_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @img_hi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @role_shadow]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffRolesK; @role_apart]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_lt]; [@Stdlib; @micromega; @ZifyClasses; @rew_iff]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_le]; [@Corelib; @Init; @Logic; @not]; [@Stdlib; @micromega; @ZifyClasses; @not_morph]; [@Stdlib; @micromega; @Tauto; @NOT]; [@Stdlib; @micromega; @VarMap; @Branch]; [@Stdlib; @micromega; @Tauto; @OR]; [@Stdlib; @micromega; @EnvRing; @PEsub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @xlo_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @Mr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @co_know]; [@Stdlib; @ZArith; @BinInt; @Z; @mul]; [@Stdlib; @ZArith; @BinInt; @Z; @div_mod]; [@Stdlib; @micromega; @SatDivMod; @Z_div_nonneg_nonneg]; [@Stdlib; @micromega; @EnvRing; @PEmul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @rg]; [@Stdlib; @micromega; @ZifyClasses; @and_morph]; [@Stdlib; @micromega; @ZifyClasses; @impl_morph]; [@Stdlib; @micromega; @ZifyClasses; @eq_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @ra]; [@Corelib; @Init; @Logic; @or_ind]; [@Corelib; @Init; @Logic; @or_introl]; [@Corelib; @Init; @Logic; @or_intror]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtMem; @apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @sp0_win]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @spb_qs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_run_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @as0_rn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @rgl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @xpos]; [@Corelib; @Init; @Logic; @ex_intro]; [@Stdlib; @micromega; @ZMicromega; @CutProof]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @rg_hole]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_dtls]; [@Stdlib; @micromega; @RingMicromega; @PsatzMulE]; [@Stdlib; @micromega; @RingMicromega; @PsatzC]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @rg_img]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @ra_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_sptop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_ar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_qs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_t]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_ctx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_tp]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_tsd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_space_beg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_kbase]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_parr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_key]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_loff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_l2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_blk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_fs]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @split_lit_denot]; [@Corelib; @Init; @Logic; @iff_refl]; [@LinuxProcessSemantics; @Riscv; @Sem; @alu64]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_small]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @spb_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @u_add64]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @mkAlu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @mkAlu_denot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KWord]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KZero]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KBlob]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KImg]; [@Stdlib; @ZArith; @BinInt; @Z; @leb_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffBridgeK; @hb_img]; [@Corelib; @Init; @Datatypes; @andb_true_intro]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @in_hull]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KAlign]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KRange]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KWr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KDisj]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KFill]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @KUnk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @cellW]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @uE0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @ris_val]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @cellLb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @got_none]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_statics]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @wrK]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_stack_top]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @ar_stack_bottom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_thread]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4HandoffK; @as0_chk_parts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtRunsMem; @art_wr_of_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @hl_shadow_defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4PlanImagesK; @asan0_shadow_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @mkind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @am_kind]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @SHB_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @SHB_LEN]; [@LinuxProcessSemantics; @LinuxProcessSem; @RiscvSemantics; @store_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_inited]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @art_pc_hdr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @art_cls_rep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @art_cls0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @art_cls_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @cl_cache]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @cl_mu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @cl_au]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @cellZ]; [@Stdlib; @micromega; @ZifyClasses; @mkapp2]; [@Stdlib; @micromega; @ZifyClasses; @inj]; [@Stdlib; @micromega; @ZifyInst; @Inj_Z_Z]; [@Stdlib; @micromega; @ZifyClasses; @mkapp]; [@Corelib; @Lists; @ListDef; @nth]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtMem; @wr_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @wr0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @CLS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @cl_free]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @cl_mfa]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @cl_na]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @cl_nfr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @class_size_pos]; [@Corelib; @Lists; @ListDef; @Forall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCls; @art_cptr_ok]; [@stdpp; @base; @NoDup]; [@Corelib; @Lists; @ListDef; @Forall_nil]; [@stdpp; @base; @NoDup_nil_2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @kshadow_wr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_spb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_ris]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_gs0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_cls]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_primary]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @byte_at]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_cst]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @CFree]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_st]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_chunk_hdr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmHeapIfaceA; @shadow_blk_w]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_lch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_in_batches]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_batch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_qt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_qg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @bt_addr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_chunks]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtCellsK; @cell0_cat]; [@Corelib; @Init; @Nat; @add]; [@Stdlib; @Arith; @PeanoNat; @Nat; @add]; [@Stdlib; @ZArith; @Znat; @Nat2Z; @inj_add]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_sec]; [@Stdlib; @Lists; @List; @nth_error]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @sc_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @sc_msize]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @art_live]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtRuns; @aev]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @sc_u]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @sc_n]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @sc_quar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_chunk_hdrL]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @lock_sec]; [@Corelib; @Init; @Datatypes; @S]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_sec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_sec_committed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_log]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_sec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_batch_list]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @bt_items]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @CQuar]; [@Corelib; @Lists; @ListDef; @map]; [@Stdlib; @Lists; @List; @flat_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @CBatch]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @lock_quar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_batches_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_quar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_ia]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_ia]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @kentry_eqb]; [@LinuxProcessSemantics; @Riscv; @Instr; @aluop]; [@LinuxProcessSemantics; @Riscv; @Instr; @mulop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EVar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @kentry_eqb_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffBridgeK; @hb_kn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @kentry_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EAlu]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EAluw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EMd]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EMdw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EExt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @EBlob]; [@stdpp; @bitvector; @definitions; @Z_to_bv_bv_unsigned]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4BssZeroK; @as0_dep_rdn_zero]; [@Corelib; @Lists; @ListDef; @repeat]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffCellsK; @wleb_zero]; [@Corelib; @Init; @Nat; @of_num_uint]; [@Corelib; @Init; @Number; @UIntDecimal]; [@Corelib; @Init; @Decimal; @D1]; [@Corelib; @Init; @Decimal; @D6]; [@Corelib; @Init; @Decimal; @D3]; [@Corelib; @Init; @Decimal; @D8]; [@Corelib; @Init; @Decimal; @D4]; [@Corelib; @Init; @Decimal; @Nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @g_depot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @K0D]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtDepotA; @dp_nodes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @var_in]; [@Stdlib; @ZArith; @BinInt; @Z; @eq_dec]; [@Corelib; @Init; @Specif; @sumbool]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_dec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @img_zero4]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @u64_range]; [@Stdlib; @setoid_ring; @Ring_polynom; @PExpr]; [@Stdlib; @setoid_ring; @ZArithRing; @Zr_ring_lemma1]; [@Stdlib; @setoid_ring; @Ring_tac; @ring_subst_niter]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEadd]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEX]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEc]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEmul]; [@Stdlib; @setoid_ring; @Ring_polynom; @mk_monpol_list]; [@Stdlib; @ZArith; @BinInt; @Z; @opp]; [@Stdlib; @ZArith; @BinInt; @Z; @quotrem]; [@Stdlib; @setoid_ring; @Ring_polynom; @Mon]; [@Stdlib; @setoid_ring; @Ring_polynom; @Pol]; [@Stdlib; @setoid_ring; @Ring_polynom; @Peq]; [@Stdlib; @setoid_ring; @Ring_polynom; @norm_subst]; [@Corelib; @Init; @Datatypes; @comparison]; [@Corelib; @Init; @Datatypes; @Lt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtDepotA; @NID]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtDepotA; @STO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtDepotA; @MAP1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtDepotA; @DEP]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_depot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInitCache; @art_ic_mc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInitCache; @art_ic_mc_range]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_rt_ghost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_ghost]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_depot]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_ia]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_quar]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_sec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_chunks]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_primary]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @CAlloc]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_run_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_statics]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_rt_thread]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_alloc_rep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffCellsK; @hc_zero]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEsub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @KSH]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4HandoffK; @as0_A0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_EXTRA]; [@Corelib; @Lists; @ListDef; @Forall_cons]; [@Stdlib; @setoid_ring; @Ring_polynom; @PEpow]; [@Stdlib; @ZArith; @BinInt; @Z; @to_N]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_mul]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @A_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @in_shadow_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @page_allowedb]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_A0x]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @page_base_le]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @spiece]; [@Stdlib; @ZArith; @BinInt; @Z; @div_pos]; [@Stdlib; @ZArith; @BinInt; @Z; @div_le_mono]; [@Corelib; @Init; @Datatypes; @orb]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_size]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @allowA]; [@Stdlib; @Bool; @Bool; @orb_true_iff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @sh_lo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @pageup]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @sh_hi]; [@Stdlib; @Lists; @List; @in_flat_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @allow1]; [@Stdlib; @Lists; @List; @in_or_app]; [@Stdlib; @ZArith; @BinInt; @Z; @div_lt_upper_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_pos_bound]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_neg_bound]; [@Stdlib; @omega; @PreOmega; @Z; @div_0_r_ext]; [@Stdlib; @omega; @PreOmega; @Z; @mod_0_r_ext]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @shadow_off]; [@Stdlib; @Lists; @List; @existsb_app]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_allowed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4HandoffK; @as0_BASE]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @BINV_intro]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @vm_maps]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @segments_reserved]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @vm_noaccess]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @rn_HI]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_BASEx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanCeil; @bottomup_floor]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @a_totsz]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @KMAX]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanCeil; @alloc_ceiling]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @a_abytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @a_eager]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanAcct; @A_bytes]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4HandoffK; @as0_binv_main]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_EXTRA_wf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @BInv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @in_shadow_rw]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @bi_shdef]; [@Stdlib; @ZArith; @BinInt; @Z; @add_0_l]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtMem; @art_bytes1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_shdef]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PropExec; @seg_rom]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @shadow_blk]; [@Corelib; @Init; @Logic; @iff]; [@Corelib; @Classes; @Morphisms; @iff_impl_subrelation]; [@Stdlib; @Bool; @Bool; @andb_true_iff]; [@Corelib; @Classes; @Morphisms; @subrelation_proper]; [@Corelib; @Classes; @Morphisms; @respectful]; [@Corelib; @Classes; @Morphisms_Prop; @and_iff_morphism]; [@Corelib; @Program; @Basics; @impl]; [@Corelib; @Classes; @Morphisms; @subrelation_respectful]; [@Corelib; @Classes; @Morphisms; @subrelation_refl]; [@Corelib; @Classes; @Morphisms; @reflexive_proper_proxy]; [@Corelib; @Classes; @Morphisms; @reflexive_reflexive_proxy]; [@Corelib; @Classes; @RelationClasses; @iff_Reflexive]; [@Stdlib; @Bool; @Bool; @orb_prop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @byteZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @byte1]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @HSH_LO]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @HSH_HI]; [@Stdlib; @Lists; @List; @Forall_forall]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmGlobKit; @off_poison]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @PmGlobKit; @zruns_cover]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @glob_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @art_c_statics]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @art_fsinv_handoff]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @art_fs_geo]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @FS_BYTES]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_c_statics]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @art_cost_sum]; [@Stdlib; @Lists; @List; @fold_right]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_credit_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @app_mem]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @defined]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @blocks_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIface; @lb_remove]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframes_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @fframe]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanNodesMmLibK; @isp_facts_of]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanNodesMmLibK; @isp_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanNodesMmLibK; @u_e_top]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4PlanImagesK; @asan0_res_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @utop]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanNodesMmLibK; @u_e_stk_len]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @utop_bounds]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @vis_shadow_allowed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_client_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @art_lazy_chk]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @hsplit_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @is_rng]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @m_vm_lazy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @hreplay]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffBridgeK; @hb_lazy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @lazy_parts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @hl_hops_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @hlz_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @hl_replay]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @bKS]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @is_rng_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLazyK; @hl_replay_sub]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @ris_val2]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_lazy_zone]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @page_in_ranges]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLazyK; @hl_page_piece]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @pb_facts]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @lazy_piece]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_committed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @apx]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanK; @APK; @flat_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @ranges_apart_x]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @know_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @flat_x_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @estart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @a_base]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @a_off]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @ranges_apart_x_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @elenZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3K; @AX2K; @xhi]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @xhi_sound]; [@Stdlib; @ZArith; @BinInt; @Z; @compare]; [@Corelib; @Init; @Datatypes; @Gt]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @round_id]; [@Stdlib; @ZArith; @BinInt; @Z; @add_mod]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @win_nolazy]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @apx_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @round_al]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffLedgerK; @hl_off_band]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @cs_ok]; [@Stdlib; @ZArith; @ZArith_dec; @Z_lt_le_dec]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3SoundK; @AX2SK; @ealign_sound]; [@Stdlib; @ZArith; @BinInt; @Z; @divide]; [@Stdlib; @ZArith; @BinInt; @Z; @mod_divide]; [@Stdlib; @ZArith; @BinInt; @Z; @divide_trans]; [@Stdlib; @ZArith; @BinInt; @Z; @pow_add_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @round_apart]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_lazy_c1]; [@Stdlib; @Lists; @List; @in_app_or]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @own_window]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @vis_hi_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @win_allowed]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @vis_in_In]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_lazy_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @KN0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @ivZ]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AsanPlanSoundK; @APSK; @amap_den]; [@Stdlib; @Lists; @List; @in_map]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffRolesK; @role_in]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HandoffBridgeK; @hb_maps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @role_kn]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @seg_kn]; [@LinuxProcessSemantics; @LinuxProcessSem; @Run; @segment_reservation]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @Asan_segment_000]; [@LinuxProcessSemantics; @LinuxProcessSem; @MemImageType; @Segment]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @Asan_segment_001]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @Asan_segment_002]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @Asan_segment_003]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4PlanImagesK; @asan0_res_eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_kn_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @BINV_awf]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_binv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @art_fsg]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @art_fsg0]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtFsInv; @art_fsinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @ArtBridge; @BINV]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_eager_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_alloc_rep]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_fsinv]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_credit]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_client]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_kn_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_lazy_ok]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtHandoffK; @Derive; @as0_art_eager]; [@LinuxProcessSemantics; @LinuxProcessSem; @State; @VmMaps]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @Pm4ArtInv; @art_handoff_target]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @HeapIfaceA; @vml_of]].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).

Definition I_KSPACE : nat := 5.   Definition I_PARR : nat := 6.   Definition I_THREAD : nat := 7.   Definition I_CTX : nat := 8.
Definition I_FAKE : nat := 11.    Definition I_L2 : nat := 14.    Definition I_BLK : nat := 15.   Definition I_DTLS : nat := 10.

Definition e_at (k : list kentry) (b : expr) (off : Z) (w : nat) : expr :=
  match kfind_word k b off w with Some e => e | None => ELit 0 end.
Definition bT (cs : acs) : expr := am_base (role cs I_THREAD).
Definition bC (cs : acs) : expr := am_base (role cs I_CTX).
Definition bF (cs : acs) : expr := am_base (role cs I_FAKE).
Definition bP (cs : acs) : expr := am_base (role cs I_PARR).
Definition bL2 (cs : acs) : expr := am_base (role cs I_L2).
Definition bBLK (cs : acs) : expr := am_base (role cs I_BLK).
Definition bD (cs : acs) : expr := am_base (role cs I_DTLS).

Definition spbE (cs : acs) : expr := e_at (kn cs) (ELit 0) (1468568 + 32) 8.
Definition bK (cs : acs) : expr := fst (split_lit (spbE cs)).

Definition topE (cs : acs) : expr := e_at (kn cs) (bT cs) 8 8.
Definition botE (cs : acs) : expr := e_at (kn cs) (bT cs) 16 8.

Definition tfE (cs : acs) : expr := e_at (kn cs) (ELit 0) 0x23bdc8 8.
Definition stE (cs : acs) : expr := e_at (kn cs) (ELit 0) (0x23bdc8 + 24) 4.

Definition TP : Z := 0x69dfd0.
Definition TSD : Z := 0x6bf488.
Definition LOFF : Z := 0x10.

Definition as0_ar (E : env) (cs : acs) : asan_run :=
  AR (uE E e_sp0) (uE E (topE cs)) (uE E (botE cs)) (rbase E cs I_FAKE) (uE E (bK cs) + 0x10000).
Definition as0_rn (E : env) (cs : acs) : art_run :=
  ARN (as0_ar E cs) (rbase E cs I_THREAD) (rbase E cs I_CTX) TP 0 TSD LOFF ((uE E (bK cs) + 0x10000) / 65536)
      (rbase E cs I_KSPACE) (rbase E cs I_PARR) (rbase E cs I_L2) (rbase E cs I_BLK) (rbase E cs I_DTLS).

Definition is_var_in (k : list kentry) (e : expr) (lo hi : Z) : bool :=
  match e with EVar _ => existsb (kentry_eqb (KRange e lo hi)) k | _ => false end.

Definition B1 : Z := 4067256.
Definition B2 : Z := 4054672.
Definition img_cover (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg l h => (Z.leb l lo && Z.leb hi h)%bool | _ => false end) k.
Definition xlo_pos (k : list kentry) (e : expr) : bool := match xlo k e with Some lo => Z.ltb 0 lo | None => false end.
Definition lit_len (cs : acs) (i : nat) (L : Z) : bool := expr_eqb (am_len (role cs i)) (ELit L).
Definition vis_in (cs : acs) (b n : expr) : bool := existsb (fun p => (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool) (a_vis cs).

Definition glob_chk (k : list kentry) (g : Z * Z) : bool :=
  (((snd g / 8 =? 0) || chk_zero k (ELit 0) (fst g / 8 + 0x7fff8000) (snd g / 8)) && ((snd g mod 8 =? 0) || chk_word k (ELit 0) (fst g / 8 + 0x7fff8000 + snd g / 8) 1 (ELit (snd g mod 8)))
   && (0x10000 <=? fst g) && (fst g <? 0x6c0000) && (0 <=? snd g) && (snd g <? 8192))%bool.

Definition art_sym_list (cs : acs) : list bool :=
  let k := kn cs in
  [ ((17 =? Z.of_nat (length (a_maps cs))));
    (chk_word k (ELit 0) (1468568 + 32) 8 (spbE cs));
    (Z.eqb (snd (split_lit (spbE cs))) 0x10000);
    (chk_word k (ELit 0) (1468568 + 48) 8 (eaddz (spbE cs) (2 ^ 37)));
    (chk_word k (ELit 0) (1468568 + 64 + 8) 8 (bP cs));
    (chk_word k (ELit 0) TSD 8 (bC cs));
    (chk_word k (bC cs) 152 8 (bT cs));
    (chk_word k (bT cs) 0 8 (bC cs));
    (chk_word k (bC cs) 8 4 (ELit 0));
    (chk_word k (bT cs) 8 8 (topE cs));
    (chk_word k (bT cs) 16 8 (botE cs));
    (chk_word k (bT cs) 40 1 (ELit 0));
    (chk_word k (bT cs) 3168 1 (ELit 0));
    (chk_wr k (bT cs) 0 4096);
    (chk_zero k (bT cs) 80 3088);
    (chk_zero k (bK cs) 0x2000010000 4096);
    (chk_wr k (bK cs) 0x2000010000 4096);
    (chk_wr k (bF cs) 0 0xb09000);
    (chk_word k (ELit 0) TP 8 (bF cs));
    (chk_word k (bT cs) 72 8 (bF cs));
    (chk_word k (bF cs) 88 8 (ELit 20));
    (chk_zero k (bF cs) 0 88);
    (chk_zero k (bF cs) 96 (4096 + 32768 - 96));
    (chk_word k (ELit 0) 0x64bde8 8 (bL2 cs));
    (chk_word k (ELit 0) (0x23bdc8 + 16) 8 (bBLK cs));
    (chk_word k (ELit 0) 0x23bdc8 8 (tfE cs));
    (is_var_in k (tfE cs) 2 3);
    (chk_word k (ELit 0) (0x23bdc8 + 24) 4 (stE cs));
    (is_var_in k (stE cs) 2 3);
    (chk_wr k (ELit 0) 0x24bdd8 4194308);
    (chk_wr k (ELit 0) 0x23bdc8 32);
    (chk_wr k (bL2 cs) 0 (2 ^ 20));
    (chk_wr k (bBLK cs) 0 (2 ^ 23));
    (chk_word k (bL2 cs) 24 4 (ELit 0));
    (chk_word k (bL2 cs) 16 8 (e_at k (bL2 cs) 16 8));
    (chk_word k (ELit 0) B1 4 (e_at k (ELit 0) B1 4));
    (is_var_in k (e_at k (ELit 0) B1 4) 0 1);
    (chk_word k (ELit 0) B2 4 (e_at k (ELit 0) B2 4));
    (is_var_in k (e_at k (ELit 0) B2 4) 0 1);
    (img_cover k DEP_LO B2);
    (img_cover k (B2 + 4) B1);
    (img_cover k (B1 + 4) DEP_HI);
    (amap_eqb (role cs 0) M_LOW);
    (amap_eqb (role cs 1) M_GAP);
    (amap_eqb (role cs 2) M_HIGH);
    (xlo_pos k (bT cs));
    (xlo_pos k (bC cs));
    (xlo_pos k (bF cs));
    (lit_len cs I_KSPACE 0x2000011000);
    (lit_len cs I_PARR 0x800000);
    (lit_len cs I_THREAD 4096);
    (lit_len cs I_CTX 0x10000);
    (lit_len cs I_FAKE 0xb09000);
    (lit_len cs I_L2 0x100000);
    (lit_len cs I_BLK 0x800000);

    (lit_len cs I_DTLS 4096); (xlo_pos k (bD cs)); (chk_word k (ELit 0) (1468568 + 64 + 16) 8 (bP cs)); (vis_in cs (ELit 0x10000) (ELit 0x6b0000));
    (vis_in cs (bF cs) (ELit 0xb09000));
    (vis_in cs e_top e_stk_len);

    (img_cover k 0x15a000 0x162000);

    (chk_word k (ELit 0) (TP + 8) 8 (bD cs)); (chk_word k (bD cs) 24 8 (ELit TP));
    (forallb (fun z => chk_zero k (ELit 0) (fst z) (snd z)) (zruns ART_IMG_LO ART_POISON ART_IMG_HI));
    (forallb (glob_chk k) ART_GLOBALS) ]%bool.
Definition art_sym_chk (cs : acs) : bool := forallb (fun b => b) (art_sym_list cs).

Fixpoint all_true (l : list bool) : Prop := match l with [] => True | b :: r => b = true /\ all_true r end.
Lemma all_true_of : forall l, forallb (fun b => b) l = true -> all_true l.
Proof. induction l as [|b l IH]; intros H; [exact I|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2]. split; [exact H1 | exact (IH H2)]. Qed.

Definition bKS (cs : acs) : expr := am_base (role cs I_KSPACE).
(* [comment removed for export] *)
Definition E_RISX (cs : acs) : expr := EAlu Instr.ALU_ADD (bK cs) (ELit 0x2000010000).

Fixpoint hsplit (r : expr) (h : list hop) : option (list hop * list hop) :=
  match h with
  | [] => None
  | HSub b n :: t =>
      if (expr_eqb b r && expr_eqb n (ELit 4096))%bool then Some ([], t)
      else match hsplit r t with Some (h1, h2) => Some (HSub b n :: h1, h2) | None => None end
  | x :: t => match hsplit r t with Some (h1, h2) => Some (x :: h1, h2) | None => None end
  end.
Lemma hsplit_eq : forall r h h1 h2, hsplit r h = Some (h1, h2) -> h = h1 ++ HSub r (ELit 4096) :: h2.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S^D0!1+U+^F!2+^600!1+^11!2,^H1!4,^I00#2#1!1,C!1,B|<000;!2,^K#64!1,^?+^F$e;R2-^1RN$o;R!1+^11w#12$~R1+^M+^N!2'^G#;#8!1,^P1!2'^4#14-^6RN$p;R!2+^6002#11$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^F!2,^K#5#4#2#1!2'^G#<#9!2,^H1!4,^I00#7#6!2,^R2#1!2'^G#@#=!3+^<2#43!2,^Q#;#:!2,^H1!4,^I00#=#<!2,^K#C4!3+^<0!3,^A+^F!2,^Q#9#8#@!3'^J+^F#>!3,^A+^FC#=!2'^G#B#?!2,^H1#1!3+^<2!2,^H1#43!2,^K#F4!3+^<2!2,^H1!4,^I00#5#43!2,^K#I4-^6RN$p;R!2+^6000#11$l;R0$l;R0#1$e;R2-^1RN$o;R!1+^110#12$p;R1K#5!2,^H1!4,^I00#C#B-^6RN$p;R!2+^6000#11$l;R0$l;R0#2!3,^A+^F!2,^Q#@#?#7!3,^A+^F!2,^Q#?#>#6!2,^Q#C#B!3,^A+^FQ#J!2,^K#M4!2,^Q#B#A!2,^A+^FT!2,^K#L4!3,^A+^FV#8%~R00!3#6#9#8!2,^R2!2,^H1!4,^I00#9#8!3+^<293!2,^H1!4,^I00#<#;!2,^H1!4,^I006#>!2'^G#A#>!2'\!2'^4#5#?!2'^4#44!2,^H1!4,^I00#;#:!3,^A+^F!2,^K#<#;#C!2'^4#;#E!2'^4#:4!3+^<+X!2'^4#<#F,^=!3'^J+^F6!3,^A+^FS#J!2,^K#?#>!2,^H1!4,^I00#A#@!2,^K#G4!3+^<0!3,^A+^F!2,^K#=#<#D!3'^J+^F#B!3,^A+^F^:#A!3,^A+^F!2,^K#D#C#7!3,^A+^F!2,^K#C#B#6!2,^K#G#F!3,^A+^F^>#N!2,^K#Q4!2,^K#F#E!2,^A+^F^A!3,^A+^F!2,^K#P4#8$r;R+;$h;R0!5'^;+^F$h;R0%h1;R0%h2;R0%~R!3+^<2!2'^G#5#33!3+^<0#4!3'^J+^F#3!3,^A+^F5#2$h1;R0$h2;R0$H;R!3+^<2!2'^G#463&H0;R!6'^L2!2'^G#567,^@!2,^H1!4,^I00#3#2#1+^M!2'^O!3+^<06!3'^J+^F#4!3,^A+^F5#3#1$x;R+^F$t;R0$IH;R%h1;R0%h2;R0%~R!3+^<2!2'^G#6#33!3+^<0#4!3'^J+^F#3!3,^A+^F!2,^K#74#2$h1;R0$h2;R0$H;R!3+^<2!2'^G#7!3,^A+^F#5#43!1-^FRN$h;R+^F%H;R!3+^<2-^FRN$x;R+^F2#12$b;R+;$n;R+;-^1RN$x;R!1+^11282$p;R1-^6RN$p;R!2+^6002#11$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^F#6#2#19$b;R+;$n;R+;-XRN$~R+X2!2'\!2'^4#2#;:2!2,^H1!4,^I006#8-^1RN$x;R!1+^11282$p;R1;9!2,^H1!4,^I00#4#3!3+^<0!3,^A+^F#2#7!3'^J+^F#5!3,^A+^F!2,^K#:4#4#62$b;R+;$n;R+;!2$b;R+;$n;R+;$H;R!3+^<2-^1RN$x;R!1+^112<2$p;R1-^6RN$p;R!2+^6002#11$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^F!2,^Q#5#4#2#19=&o;R!2'^G#=#:2&Hs;R>!3+^<2!2'^G#>#;#1!3-^1RN$o;R!1+^11%Hs;R!3+^<2?#1%IH;R%h1;R0%h2;R0%~R@!3+^<0#A!3'^J+^F#3!3,^A+^F!2,^K#D4#2%H;R!3+^<2-^1RN$x;R!1+^112#32$p;R1-^6RN$p;R!2+^6002#11$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^FA#2#19BD#22$p;R1!1$p;R1-^6RN$p;R!2+^600%Hs;R!3+^<2EF%IH;R%h1;R0%h2;R0%~RG!3+^<0#C!3'^J+^F#3!3,^A+^FH#2%H;R!3+^<2-^6RN$p;R!2+^6002#31$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^F!2,^Q#<#;#2#1!2,^H1!4,^I00#?#>!3+^<0!3,^A+^FA#B!3'^J+^F#@!3,^A+^F!2,^K#E4#?#11$l;R0$l;R0!2$a1;R0$a2;R0$Hs;R!3+^<2!2'^G#E#B3$IH;R%h1;R0%h2;R0%~RI!3+^<0#F!3'^J+^F#3!3,^A+^FJ#2$H;R!3+^<2!2,^H1!4,^I00!3,^A+^F!2,^Q#=#<#4#3!2,^H1!4,^I00#B#A&H0;R!6'^S20L!2,^H1!4,^I00!3,^A+^F!2,^Q#>#=#5#4M#1!3+^<0#4#B!1&H0;R!6'^S20$e;R2-^1RN$o;R!1+^110#12$p;R1NO!2,^H1!4,^I00P#5!2,^H1!4,^I00#D#C#2!3+^<0P#D!1$H;R!3+^<0O#E!6'^L0!3,^A+^F!2,^Q#A#@#8$h1;R0%~R!3+^<0#8#F!3+^<0R!3'^J+^F#2!3,^A+^FS#G$H;R!3+^<0#7#E!6'^L0#8$h2;R0!3+^<0R!3'^J+^F!3,^A+^FQ#:!3,^A+^FS#1vd!8'^T00UU#I!3'^J+^F#9W!2,^RXUY!3+^<0!3,^A+^FT#I!3'^J+^F!3,^A+^FT#9W#F#1#F#1#1#1#2#1#1$Hs;R!3+^<2!2'^G#?#<9$IH;R%h1;R0%h2;R0%~RZ!3+^<0#@!3'^J+^F#3!3,^A+^FC#2$H;R!3+^<29[&H0;R!6'^L297,^@B#1+^M!2'^OD#1#1#;#3#2#1$b;R+;$n;R+;!2$b;R+;$n;R+;$H;R!3+^<2-XRN$~R+X2!2'\!2'^4#2#<:2!2,^H1!4,^I006#9-^1RN$x;R!1+^112<2$p;R1;9=&b0;R!2'\!2'^4#3#=!2'^4#24+X&Hb;R!2,^R+X#1!3+^<+X!2'\!2'^4#4#>!2'^4#34#1!2-XRN$b;R+X%Hb;R!3+^<+X!2'\!2'^4#6#@!2'^4#54#1%H;R!3+^<2-XRN$~R+X2#22\-^1RN$x;R!1+^112^02$p;R1-^6RN$p;R!2+^6002#11$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^F!2,^K#:#9#2#19[!3+^<0!3,^A+^F!2,^K#8#7#?!3'^J+^F#=!3,^A+^F!2,^K#B4#<#22$Hb;R!3+^<+X^1,^=$H;R!3+^<2!2,^H1!4,^I006#=^2&H0;R!6'^S20$e;R2-^1RN$o;R!1+^110#12$p;R1K#?\[#1!3+^<0#>#;!1&H0;R!6'^S20$e;R2-^1RN$o;R!1+^110#12$p;R1N6!2,^H1!4,^I006#?B#2!3+^<06#=!1$H;R!3+^<06#>!6'^L06$h1;R0%~R!3+^<0#B#?!3+^<0^3!3'^J+^F#2!3,^A+^FH#@$H;R!3+^<0#A#>!6'^L0#B$h2;R0!3+^<0^3!3'^J+^F6!3,^A+^FH#1&Hb;R!3'^B^4^5#6!2+^C!3+^<+X^4,^=!3+^<+X^5,^=!5'^D^6!3+^<+X!2'^4#;4,^=!3+^<0!3,^A+^F!2,^K#<#;#C!3'^J+^F6!3,^A+^F!2,^K#F4#C$~R^6$~R!3+^<+X!2'^4#<4,^=!2$B1;R!3+^<+X!2'^4#>#H,^=$B2;R!3+^<+X!2'^4#>4,^=&B1;R!3'^U#@#J#2!3+^<+;#@#J&B2;R!3'^U#@4#2!3+^<+;#@4!6'^V+;#L$b;R+;!3+^<0!3,^A+^F!2,^K#1#B#J^7!6'^V+;4$n;R+;!3+^<0!3,^A+^F!2,^K#M#1#J^7!2,^R0!3'^J+^F6!3,^A+^FV#I#A#1#B#2#2#1#1#?#1#?#1#1#1$Hb;R!3+^<+X^1,[$H;R!3+^<2-^1RN$x;R!1+^112?2$p;R1-^6RN$p;R!2+^6002#11$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^F!2,^K#9#8#2#19^2&o;R^02&Hs;R>!3+^<2E#1!3-^1RN$o;R!1+^11%Hs;R!3+^<2!2'^G#D#A#1%IH;R%h1;R0%h2;R0%~R@!3+^<0#E!3'^J+^F#3!3,^A+^F!2,^K#H4#2%H;R!3+^<2-^1RN$x;R!1+^112#32$p;R1-^6RN$p;R!2+^6002#11$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^F^8#2#19^9^;#22$p;R1!1$p;R1-^6RN$p;R!2+^600%Hs;R!3+^<2!2'^G#F#CF%IH;R%h1;R0%h2;R0%~RG!3+^<0#G!3'^J+^F#3!3,^A+^F!2,^K#J4#2%H;R!3+^<2-^6RN$p;R!2+^6002#31$h1;R0$h2;R0!2,^H1!4,^I00!3,^A+^F!2,^K#@#?#2#1M!3+^<0!3,^A+^F^8#F!3'^J+^F#D!3,^A+^FJ#C#11$l;R0$l;R0!2$a1;R0$a2;R0$Hs;R!3+^<2!2'^G#I#F3$IH;R%h1;R0%h2;R0%~RI!3+^<0#J!3'^J+^F#3!3,^A+^FS#2$H;R!3+^<2!2,^H1!4,^I00!3,^A+^F!2,^K#A#@#4#3!2,^H1!4,^I00#F#E&H0;R!6'^S20L!2,^H1!4,^I00!3,^A+^F!2,^K#B#A#5#4!2,^H1!4,^I00#G#F#1!3+^<0#4#F!1&H0;R!6'^S20$e;R2-^1RN$o;R!1+^110#12$p;R1N^<!2,^H1!4,^I00^=#5!2,^H1!4,^I00#H#G#2!3+^<0^=#H!1$H;R!3+^<0^<#I!6'^L0!3,^A+^F!2,^K#E#D#8$h1;R0%~R!3+^<0#8#J!3+^<0^?!3'^J+^F#2!3,^A+^F^@#K$H;R!3+^<0#7#I!6'^L0#8$h2;R0!3+^<0^?!3'^J+^F!3,^A+^F^>#:!3,^A+^F^@#1vd!8'^T00^B^B#M!3'^J+^F#9^C!2,^RX^BY!3+^<0!3,^A+^F^A#M!3'^J+^F!3,^A+^F^A#9^C#J#1#J#1#1#1#2#1#1$Hs;R!3+^<2!2'^G#C#@9$IH;R%h1;R0%h2;R0%~RZ!3+^<0#D!3'^J+^F#3!3,^A+^F^:#2$H;R!3+^<29!2,^H1!4,^I00#@#?&H0;R!6'^L297,^@^9#1+^M!2'^O^;#1#1#?#3#1#3#2#1#1#1").
Qed.

Definition is_rng (b n : expr) (b0 : expr) (L : Z) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 4 "S00$b;R+;$n;R+;$b0;R+;$L;R+<!2'\!2'^4#4#2!2'^4#3!1,C#1").
(* [comment removed for export] *)
Definition hop_pre (cs : acs) (x : hop) : bool :=
  match x with HSub _ _ => true | HCons b n => (is_rng b n (bBLK cs) 0x800000 || is_rng b n (bP cs) 0x800000)%bool end.
(* [comment removed for export] *)
Definition hop_zone (cs : acs) (x : hop) : bool :=
  match x with
  | HSub _ _ => true
  | HCons b n => (is_rng b n (bBLK cs) 0x800000 || is_rng b n (bP cs) 0x800000 || is_rng b n (bKS cs) 0x2000011000
                  || is_rng b n (ELit 0x7fff7000) 0x10000000 || is_rng b n (ELit 0x8fff7000) 0x20000000000 || is_rng b n (ELit 0x2008fff7000) 0xdfff0001000)%bool
  end.
(* [comment removed for export] *)
Definition vis_hi (k : list kentry) (p : expr * expr) : bool :=
  ((expr_eqb (fst p) e_top && expr_eqb (snd p) e_stk_len)
   || match xhi k (fst p), snd p with Some hi, ELit n => (0 <=? n) && (n <? 2 ^ 64) && (hi + n <=? 2 ^ 47) | _, _ => false end)%bool.
(* [comment removed for export] *)
Definition apx (k : list kentry) (zb : expr) (zn : Z) (p : expr * expr) : bool :=
  let '(zb', zk) := split_lit zb in let '(pb, pk) := split_lit (fst p) in
  (flat_x k zb' zk (ELit zn) && flat_x k pb pk (snd p) && ranges_apart_x k zb' zk (ELit zn) pb pk (snd p))%bool.
(* [comment removed for export] *)
Definition own_ok (cs : acs) (p : expr * expr) : bool :=
  let k := kn cs in
  (is_rng (fst p) (snd p) (bBLK cs) 0x800000
   || is_rng (fst p) (snd p) (E_RISX cs) 4096
   || (apx k (bKS cs) 0x2000011000 p && apx k (bP cs) 0x800000 p
       && (apx k (bBLK cs) 0x800000 p || (expr_eqb (snd p) (ELit 4096) && (12 <=? ealign k (fst p))))))%bool.
Definition art_lazy_chk (cs : acs) : bool := ltac2:(Rpl.RP.run_i (rplG ()) 1 "S50!1+U+^F!2+^600!1'^X#1!2+^6+;+;!1'_2#1$cs;R+0!2'\!2'\!2'\!2'\-^1RN$x;R!1+^11+X!2'^G!1'^W#122$p;R1-^6RN$p;R!2+^600+X#11$h1;R0$l;R0!3'^9+^F!1'^Y#4#2,[!3'^9+^F!1'^Z#12!3'^93$p;R3!2'\!2'^[!1'@#2#1!2'^\#2#1!3'^J3!1'^8#1!1'_0#1!2'^0!1,B|34;!2'_1!1'@#14!3'_3#14!1,C!1,B|G000000;").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma uE_lit : forall E z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S30|10;|600;!1,C#2$E;R+F$z;R+<$Hz;R!2+^C!2'_4,D#1!2'_5#1!2'_6!1,B0!1,B1vdvd!2'_7#2#1!3+^<+<!2'_8!1,_91!2'_:#32#2!3+^<+<!2'H#32#2").
Qed.

Lemma class_size_pos : forall c, 1 <= c <= 30 -> 0 < AsanTab.class_size c.
Proof.
  intros c Hc. assert (H : forallb (fun c => 0 <? AsanTab.class_size c) (AsanTab.zrange 1 30) = true) by vmc_refl.
  apply Z.ltb_lt. apply (proj1 (forallb_forall _ _) H). unfold AsanTab.zrange. apply AsanTab.in_ziota. change (Z.of_nat (Z.to_nat 30)) with 30. lia.
Qed.

(* THE SECTION'S PARAMETERS, old beside new.
     OLD  sp brk0 rdraw argv envp uid hw fs, with Hsp Hva;
          SINV0 APH0 sp rdraw brk0 argv envp uid hw, argH0 APH0 sp rdraw argv envp uid hw.
     NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order ([ifs] the
          input's filesystem, [fs] the plan's FS0).  The [HandoffBridgeK] Generic lemmas
          below take [SINV]/[argH] as arguments and are unchanged; the Section lemmas of
          Pm4ArtCellsK / Pm4HandoffK ([art_lit], [as0_binv_main]) are called by [eapply]. *)
Section Derive.
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)).
  Variables (ifs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue).
  Variables (nofile sigmask : word) (abrt : bool) (urnd : InputStream) (tmp0 : Fs.Fs).
  Variables (kb : KernelBuild) (execfn : list byte) (sdf : bool) (apc : N) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN0.
  #[local] Notation INP := (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc Hsp Hva.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKL : art_lits_chk cs = true.
  Hypothesis CHKS : art_sym_chk cs = true.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Notation rn := (as0_rn E cs).
  #[local] Notation T := (rbase E cs I_THREAD).
  #[local] Notation CTX := (rbase E cs I_CTX).
  #[local] Notation KB := (rbase E cs I_KSPACE).
  #[local] Notation SPB := (uE E (bK cs) + 0x10000).
  #[local] Notation SP0 := (uE E e_sp0).

  (* [comment removed for export] *)
  Hypothesis HGEO_SPB : KB < SPB <= KB + 65536 /\ SPB mod 65536 = 0.
  Hypothesis HGEO_STK : uE E (topE cs) = uE E (botE cs) + 8388608 /\ uE E (botE cs) mod 4096 = 0
                        /\ SP0 - 8388608 <= uE E (botE cs) + 4096 /\ uE E (botE cs) <= SP0 - 8388608 + 4096 /\ uE E (topE cs) <= 2 ^ 47.

  (* [comment removed for export] *)
  Hypothesis HSP16 : SP0 + 16 <= 2 ^ 47.
  Hypothesis HSPA : SP0 mod 16 = 0.                                    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac chk_split H := repeat (let X := fresh "C" in apply andb_prop in H as [H X]).

  Lemma nofog : no_fog (a_maps cs) = true.
  Proof. pose proof CHK0 as H. unfold as0_chk in H. chk_split H. exact H. Qed.

  Lemma cellW : forall b off w v, chk_word (kn cs) b off w v = true -> cellA FULL (uE E b + off) w (uE E v).
  Proof.
    intros b off w v H. unfold cell.
    exact (proj2 (hc_word ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off w v HC H)).
  Qed.
  Lemma cellL : forall a w v, In (a, w, v) ART_LITW -> cellA FULL a w v.
  Proof. intros a w v Hin. eapply art_lit; eassumption. Qed.

  Lemma cellLb : forall a w v,
    existsb (fun c => (Z.eqb (fst (fst c)) a && Nat.eqb (snd (fst c)) w && Z.eqb (snd c) v)%bool) ART_LITW = true -> cellA FULL a w v.
  Proof.
    intros a w v H. apply existsb_exists in H as ([[a' w'] v'] & Hin & Hb). cbn [fst snd] in Hb.
    apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
    exact (cellL _ _ _ Hin).
  Qed.
  Lemma cellZ : forall b off n a (w : nat), chk_zero (kn cs) b off n = true -> (w <= 8)%nat ->
    uE E b + off <= a -> a + Z.of_nat w <= uE E b + off + n -> cellA FULL a w 0.
  Proof.
    intros b off n a w H Hw H1 H2. unfold cell.
    exact (hc_zero_cell ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model b off n HC H a w Hw H1 H2).
  Qed.
  Lemma wrK : forall b off n, chk_wr (kn cs) b off n = true -> wrA FULL (uE E b + off) n.
  Proof.
    intros b off n H d k Hd Hk.
    exact (hc_wr ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off n HC H d k Hd Hk).
  Qed.

  Lemma len17 : length (a_maps cs) = 17%nat.
  Proof. pose proof (all_true_of _ CHKS) as H. cbn [all_true art_sym_list] in H. destruct H as [H _]. apply Z.eqb_eq in H. lia. Qed.

  Lemma sym_all : all_true (art_sym_list cs).
  Proof. exact (all_true_of _ CHKS). Qed.
  Ltac chk := let H := fresh in pose proof sym_all as H; cbn [all_true art_sym_list] in H; decompose [and] H; assumption.

  (* [comment removed for export] *)
  Lemma sp0_win : 0x7fff80000000 <= SP0 <= 2 ^ 47.
  Proof. destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & W & _). unfold sp_window_lo, sp_window_hi in W. unfold uE in *. lia. Qed.

  Lemma role_shadow : rbase E cs 0 = 0x7fff7000 /\ rlen E cs 0 = 0x10000000 /\ rbase E cs 1 = 0x8fff7000 /\ rlen E cs 1 = 0x20000000000
                      /\ rbase E cs 2 = 0x2008fff7000 /\ rlen E cs 2 = 0xdfff0001000.
  Proof.
    assert (H0 : amap_eqb (role cs 0) M_LOW = true) by chk. assert (H1 : amap_eqb (role cs 1) M_GAP = true) by chk.
    assert (H2 : amap_eqb (role cs 2) M_HIGH = true) by chk.
    apply amap_eqb_eq in H0. apply amap_eqb_eq in H1. apply amap_eqb_eq in H2. unfold rbase, rlen. rewrite H0, H1, H2.
    cbn [M_LOW M_GAP M_HIGH am_base am_len]. rewrite !uE_lit by lia. repeat split; reflexivity.
  Qed.

  Lemma rg : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i mod 4096 = 0 /\ 0 <= rbase E cs i /\ 0 < L /\ rbase E cs i + L <= SP0 - 8388608
    /\ (rbase E cs i + L <= 0x10000 \/ 0x6c0000 <= rbase E cs i)
    /\ ((3 <= i)%nat -> rbase E cs i + L <= 0x7fff7000 \/ 0x10007fff8000 <= rbase E cs i).
  Proof.
    intros i L Hi HL HLr. unfold lit_len in HL. apply expr_eqb_eq in HL.
    pose proof (role_lit E cs i L HL HLr) as El.
    destruct (role_geo ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i HC nofog ltac:(rewrite len17; exact Hi)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    rewrite El in *. cbn [img_lo img_hi ASAN0] in G4.
    repeat split; try assumption. intros H3.
    destruct role_shadow as (S0 & L0 & S1 & L1 & S2 & L2).
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 0 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A0.
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 1 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A1.
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 2 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A2.
    rewrite El, ?S0, ?L0, ?S1, ?L1, ?S2, ?L2 in *. lia.
  Qed.

  Lemma ra : forall i j Li Lj, (i < 17)%nat -> (j < 17)%nat -> i <> j -> lit_len cs i Li = true -> lit_len cs j Lj = true ->
    0 <= Li < 2 ^ 64 -> 0 <= Lj < 2 ^ 64 ->
    rbase E cs i + Li <= rbase E cs j \/ rbase E cs j + Lj <= rbase E cs i.
  Proof.
    intros i j Li Lj Hi Hj Hne HLi HLj Ri Rj. unfold lit_len in *. apply expr_eqb_eq in HLi. apply expr_eqb_eq in HLj.
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i j HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; exact Hj) Hne) as D.
    rewrite (role_lit E cs i Li HLi Ri), (role_lit E cs j Lj HLj Rj) in D. exact D.
  Qed.

  Lemma xpos : forall e, xlo_pos (kn cs) e = true -> 0 < uE E e.
  Proof.
    intros e H. unfold xlo_pos in H. destruct (xlo (kn cs) e) as [lo|] eqn:Hx; [|discriminate]. apply Z.ltb_lt in H.
    pose proof (xlo_sound ASEGS0 E _ (kn cs) e lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx). unfold uE. lia.
  Qed.

  Ltac lenok := first [assert_succeeds (idtac); (chk)].
  Ltac RG i L := let X := fresh "G" in pose proof (rg i L ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(chk) ltac:(lia)) as X.
  Ltac RA i j Li Lj := let X := fresh "D" in
    pose proof (ra i j Li Lj ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia)
                  ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as X.

  Lemma spb_qs : 65536 * (SPB / 65536) = SPB.
  Proof. destruct HGEO_SPB as (_ & Hm). pose proof (Z.div_mod SPB 65536 ltac:(lia)). lia. Qed.

  (* [comment removed for export] *)
  Lemma rgl : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i mod 4096 = 0 /\ 0 <= rbase E cs i /\ 0 < L /\ rbase E cs i + L <= SP0 - 8388608.
  Proof. intros i L Hi HL HLr. destruct (rg i L Hi HL HLr) as (G1 & G2 & G3 & G4 & _). auto. Qed.
  Lemma rg_img : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i + L <= 0x10000 \/ 0x6c0000 <= rbase E cs i.
  Proof. intros i L Hi HL HLr. destruct (rg i L Hi HL HLr) as (_ & _ & _ & _ & G5 & _). exact G5. Qed.
  Lemma rg_hole : forall i L, (3 <= i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i + L <= 0x7fff7000 \/ 0x10007fff8000 <= rbase E cs i.
  Proof. intros i L Hi HL HLr. destruct (rg i L ltac:(lia) HL HLr) as (_ & _ & _ & _ & _ & G6). apply G6. lia. Qed.
  (* [comment removed for export] *)
  Lemma ra_sub : forall i j Li Lj a n b m, (i < 17)%nat -> (j < 17)%nat -> i <> j -> lit_len cs i Li = true -> lit_len cs j Lj = true ->
    0 <= Li < 2 ^ 64 -> 0 <= Lj < 2 ^ 64 -> rbase E cs i <= a -> a + n <= rbase E cs i + Li -> rbase E cs j <= b -> b + m <= rbase E cs j + Lj ->
    apart a n b m.
  Proof.
    intros i j Li Lj a n b m Hi Hj Hne HLi HLj Ri Rj Ha Hn Hb Hm. unfold apart.
    destruct (ra i j Li Lj Hi Hj Hne HLi HLj Ri Rj) as [X|X]; [left | right]; lia.
  Qed.
  Ltac IDX := unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK, I_DTLS; lia.
  Ltac RASUB i j Li Lj := apply (ra_sub i j Li Lj); [IDX | IDX | IDX | chk | chk | lia | lia | lia | lia | lia | lia].

  Theorem as0_art_run_ok : art_run_ok rn.
  Proof.
    pose proof sp0_win as W. pose proof spb_qs as Q. destruct HGEO_SPB as ((K1 & K2) & K3).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    pose proof (rgl I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (p1 & p2 & p3 & p4).
    pose proof (rgl I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (t1 & t2 & t3 & t4).
    pose proof (rgl I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (c1 & c2 & c3 & c4).
    pose proof (rgl I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (l1 & l2 & l3 & l4).
    pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
    pose proof (rgl I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (f1 & f2 & f3 & f4).
    pose proof (xpos (bT cs) ltac:(chk)) as PT. pose proof (xpos (bC cs) ltac:(chk)) as PC. pose proof (xpos (bF cs) ltac:(chk)) as PF.
    change (uE E (bT cs)) with T in PT. change (uE E (bC cs)) with CTX in PC. change (uE E (bF cs)) with (rbase E cs I_FAKE) in PF.
    assert (QT : exists qt, T = 4096 * qt) by (exists (T / 4096); pose proof (Z.div_mod T 4096 ltac:(lia)); lia).
    assert (T4 : 4096 <= T) by (destruct QT as [qt Eq]; lia).
    assert (C4 : 4096 <= CTX) by (pose proof (Z.div_mod CTX 4096 ltac:(lia)); lia).
    assert (F4 : 4096 <= rbase E cs I_FAKE) by (pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)); lia).
    assert (KHOLE : 0x10007fff8000 <= KB).
    { destruct (rg_hole I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia. }
    unfold art_run_ok, art_geo, rn_HI, rn_spb, rn_ris, rn_spb, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES.
    cbn [as0_rn as0_ar rn_ar rn_t rn_ctx rn_tp rn_key rn_tsd rn_loff rn_qs rn_kbase rn_parr rn_l2 rn_blk ar_sptop ar_space_beg ar_fs]. unfold TP, TSD, LOFF.
    rewrite Q. change (2 ^ 20) with 0x100000. change (2 ^ 23) with 0x800000.

    split.
    { split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact T4|]. split; [lia|]. split; [exact (rg_img I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
      split; [exact (rg_hole I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
      split; [RASUB I_THREAD I_KSPACE 4096 0x2000011000|]. split; [exact QT|].
      split; [exact C4|]. split; [lia|].
      split; [destruct (rg_img I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
      split; [destruct (rg_hole I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
      split; [RASUB I_CTX I_KSPACE 0x10000 0x2000011000|].
      split; [RASUB I_THREAD I_CTX 4096 0x10000|]. lia. }
    split; [reflexivity|]. split; [exact g1|]. split; [lia|]. split; [lia|].
    split; [exact p1|].
    split; [destruct (rg_img I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|]. split; [lia|].
    split; [split; [lia|]; split; [|lia]; exact (rg_hole I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia))|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].

    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [RASUB I_L2 I_THREAD 0x100000 4096|]. split; [RASUB I_L2 I_CTX 0x100000 0x10000|]. split; [RASUB I_L2 I_KSPACE 0x100000 0x2000011000|].
    split; [unfold apart; destruct (rg_hole I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
    split; [RASUB I_BLK I_THREAD 0x800000 4096|]. split; [RASUB I_BLK I_CTX 0x800000 0x10000|]. split; [RASUB I_BLK I_KSPACE 0x800000 0x2000011000|].
    split; [unfold apart; destruct (rg_hole I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
    split; [RASUB I_PARR I_THREAD 0x800000 4096|]. split; [RASUB I_PARR I_CTX 0x800000 0x10000|]. split; [RASUB I_PARR I_KSPACE 0x800000 0x2000011000|].
    split; [RASUB I_PARR I_L2 0x800000 0x100000|]. split; [RASUB I_PARR I_BLK 0x800000 0x800000|].
    split; [RASUB I_FAKE I_THREAD 0xb09000 4096|]. split; [RASUB I_FAKE I_CTX 0xb09000 0x10000|]. split; [RASUB I_FAKE I_KSPACE 0xb09000 0x2000011000|].
    split; [RASUB I_FAKE I_L2 0xb09000 0x100000|]. split; [RASUB I_FAKE I_BLK 0xb09000 0x800000|]. split; [RASUB I_FAKE I_PARR 0xb09000 0x800000|].
    split; [lia|].
    split; [split; [lia|]; split; [|lia]; exact (rg_hole I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia))|].
    split; [exact (rg_img I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia))|]. split; [exact F4|].

    pose proof (rgl I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (d1 & d2 & d3 & d4).
    pose proof (xpos (bD cs) ltac:(chk)) as PD. change (uE E (bD cs)) with (rbase E cs I_DTLS) in PD.
    assert (D4 : 4096 <= rbase E cs I_DTLS) by (pose proof (Z.div_mod (rbase E cs I_DTLS) 4096 ltac:(lia)); lia).
    cbn [as0_rn rn_dtls].
    split; [destruct (rg_img I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|].
    split; [destruct (rg_img I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|].
    split; [RASUB I_FAKE I_KSPACE 0xb09000 0x2000011000|].
    split; [exact D4|]. split; [lia|].
    split; [exact (rg_img I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
    split; [split; [lia|]; split; [|lia]; exact (rg_hole I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
    split; [RASUB I_DTLS I_THREAD 4096 4096|]. split; [RASUB I_DTLS I_CTX 4096 0x10000|]. split; [RASUB I_DTLS I_KSPACE 4096 0x2000011000|].
    split; [RASUB I_DTLS I_PARR 4096 0x800000|]. split; [RASUB I_DTLS I_L2 4096 0x100000|]. split; [RASUB I_DTLS I_BLK 4096 0x800000|].
    split; [RASUB I_DTLS I_FAKE 4096 0xb09000|].

    split; [RASUB I_THREAD I_KSPACE 4096 0x2000011000|]. split; [RASUB I_CTX I_KSPACE 0x10000 0x2000011000|].
    split; [RASUB I_L2 I_KSPACE 0x100000 0x2000011000|]. split; [RASUB I_PARR I_KSPACE 0x800000 0x2000011000|].
    exact KHOLE.
  Qed.

  (* [comment removed for export] *)
  Lemma spb_val : uE E (spbE cs) = SPB.
  Proof.
    assert (Hs : Z.eqb (snd (split_lit (spbE cs))) 0x10000 = true) by chk. apply Z.eqb_eq in Hs.
    pose proof (split_lit_denot E (spbE cs) (bK cs) 0x10000) as Hd. unfold bK in Hd |- *.
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & _). RG I_KSPACE 0x2000011000. unfold bK in K1, K2.
    destruct (split_lit (spbE cs)) as [b k] eqn:Hspl. cbn [fst snd] in *. subst k. specialize (Hd eq_refl).
    unfold uE in *. rewrite Hd. apply u64_lit. lia.
  Qed.
  Lemma ris_val : uE E (eaddz (spbE cs) (2 ^ 37)) = SPB + 2 ^ 37.
  Proof.
    unfold eaddz, uE. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u64_lit by lia. fold (uE E (spbE cs)). rewrite spb_val.
    apply Z.mod_small. pose proof sp0_win. destruct HGEO_SPB as ((K1 & K2) & _). RG I_KSPACE 0x2000011000. unfold uE in *. lia.
  Qed.
  Lemma uE0 : uE E (ELit 0) = 0.
  Proof. apply uE_lit. lia. Qed.

  Ltac CL := apply cellLb; vm_compute; reflexivity.
  Ltac CW a w v := let X := fresh in pose proof (cellW (ELit 0) a w v ltac:(chk)) as X; rewrite uE0 in X; rewrite ?Z.add_0_l in X.

  (* [comment removed for export] *)
  Lemma got_none : forall a, 0x15a000 <= a < 0x162000 -> FULL (Z_to_bv 64 a) = None.
  Proof.
    intros a Ha. assert (H : img_cover (kn cs) 0x15a000 0x162000 = true) by chk.
    unfold img_cover in H. apply existsb_exists in H as (K & Hin & Hc).
    destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    apply (hb_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC Hin); [lia|].
    unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Theorem as0_art_rt_statics : art_rt_statics rn FULL.
  Proof.
    unfold art_rt_statics, art_rt_tlsgot, art_prim_consts, art_layout, art_tsd, art_alloc_rodata, art_rz_rodata, DRoD, rn_spb, rn_ris, rn_spb, SB, kHighMemEnd.
    cbn [as0_rn rn_qs rn_tp rn_key rn_tsd rn_ctx rn_t rn_loff]. unfold TP, TSD, LOFF. rewrite spb_qs.
    pose proof (cellW (ELit 0) (1468568 + 32) 8 (spbE cs) ltac:(chk)) as X1. rewrite uE0, spb_val in X1.
    pose proof (cellW (ELit 0) (1468568 + 48) 8 (eaddz (spbE cs) (2 ^ 37)) ltac:(chk)) as X2. rewrite uE0, ris_val in X2.
    pose proof (cellW (ELit 0) TSD 8 (bC cs) ltac:(chk)) as X3. rewrite uE0 in X3. unfold TSD in X3.
    pose proof (cellW (bC cs) 152 8 (bT cs) ltac:(chk)) as X4.
    change (uE E (bC cs)) with CTX in *. change (uE E (bT cs)) with T in *.
    RG I_THREAD 4096. RG I_CTX 0x10000. pose proof sp0_win.
    pose proof (xpos (bC cs) ltac:(chk)) as PC. change (uE E (bC cs)) with CTX in PC.
    assert (C4 : 4096 <= CTX) by (pose proof (Z.div_mod CTX 4096 ltac:(lia)); lia).
    repeat match goal with |- _ /\ _ => split end; try exact X1; try exact X2; try exact X3; try exact X4; try exact got_none; try CL; lia.
  Qed.

  Theorem as0_art_rt_thread : art_rt_thread rn FULL.
  Proof.
    unfold art_rt_thread. cbn [as0_rn as0_ar rn_t rn_ctx rn_tp rn_loff rn_ar ar_stack_top ar_stack_bottom]. unfold TP, LOFF.
    pose proof (wrK (bT cs) 0 4096 ltac:(chk)) as W. rewrite Z.add_0_r in W.
    pose proof (cellW (bT cs) 0 8 (bC cs) ltac:(chk)) as X1. rewrite Z.add_0_r in X1.
    pose proof (cellW (bC cs) 8 4 (ELit 0) ltac:(chk)) as X2. rewrite uE0 in X2.
    pose proof (cellW (bT cs) 8 8 (topE cs) ltac:(chk)) as X3. pose proof (cellW (bT cs) 16 8 (botE cs) ltac:(chk)) as X4.
    pose proof (cellW (bT cs) 40 1 (ELit 0) ltac:(chk)) as X5. rewrite uE0 in X5.
    pose proof (cellW (bT cs) 3168 1 (ELit 0) ltac:(chk)) as X6. rewrite uE0 in X6.
    repeat match goal with |- _ /\ _ => split end; try assumption. CL.
  Qed.

  (* [comment removed for export] *)
  Lemma kshadow_wr : wrA FULL (0x7fff8000 + 8192 * (SPB / 65536)) (2 ^ 34).
  Proof.
    destruct (as0_chk_parts cs CHK0) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & K3). RG I_KSPACE 0x2000011000.
    destruct G as (g1 & g2 & g3 & g4 & g5 & g6). specialize (g6 ltac:(unfold I_KSPACE; lia)).
    pose proof (Z.div_mod SPB 65536 ltac:(lia)) as DM. rewrite K3 in DM.
    set (q := SPB / 65536) in *.
    apply art_wr_of_defined; [lia | lia |].
    intros x Hx.
    apply (hl_shadow_defined ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH asan0_shadow_ok ltac:(cbn; unfold SHB_LO; lia)
             E cs R FULL model HC C1 C4 C5 M_HIGH 0x2008fff7000 0xdfff0001000 C8 eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
  Qed.

  Lemma wr0 : forall a, wrA FULL a 0.
  Proof. intros a d k Hd Hk. assert (k = 0%nat) by lia. subst k. reflexivity. Qed.

  Theorem as0_art_rt_primary : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_primary FSG rn (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_primary. cbn [art_gs0 g_inited g_cls as0_rn rn_t rn_qs]. unfold rn_spb, rn_ris, rn_spb. cbn [as0_rn rn_qs]. rewrite spb_qs.
    assert (ZT : chk_zero (kn cs) (bT cs) 80 3088 = true) by chk.
    assert (ZR : chk_zero (kn cs) (bK cs) 0x2000010000 4096 = true) by chk.
    assert (WR : chk_wr (kn cs) (bK cs) 0x2000010000 4096 = true) by chk.
    split; [|split; [|exact kshadow_wr]].
    - intros c Hc. split; apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia.
    - intros c Hc. split; [|split; [|split; [|split]]].
      + unfold art_cls_rep, art_cache_rep, art_region_rep, art_cls0. cbn [cl_cache cl_free cl_mfa cl_au cl_mu cl_na cl_nfr length]. change (Z.of_nat 0) with 0.
        pose proof (wrK (bK cs) 0x2000010000 4096 WR) as W.
        repeat match goal with |- _ /\ _ => split end;
          try (apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia);
          try (apply (cellZ (bK cs) 0x2000010000 4096 _ _ ZR); lia);
          try (intros j Hj; cbn in Hj; lia); try apply wr0.
        apply (wr_sub _ _ _ _ _ _ W); lia.
      + unfold art_cls_ok, art_cls0. cbn [cl_cache cl_free cl_mfa cl_au cl_mu cl_na cl_nfr length app]. pose proof (class_size_pos c Hc).
        repeat match goal with |- _ /\ _ => split end; try lia; try (exists 0; lia); try constructor.
      + unfold art_cls0. cbn [cl_cache]. intros H. congruence.
      + exists 0. reflexivity.
      + unfold art_cls0. cbn [cl_au]. intros H. lia.
  Qed.

  Theorem as0_art_rt_chunks : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_chunks FSG rn (art_gs0 FSG gfs0 k0) [] FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_chunks. cbn [art_gs0 g_cls g_st]. unfold art_cls0. cbn [cl_cache cl_free cl_au cl_mu app].
    intros c Hc. pose proof (class_size_pos c Hc) as Hs. split; [|split; [|split]].
    - intros x Hx. lia.
    - intros w [].
    - intros w _. reflexivity.
    - intros w (W1 & W2 & _). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lock_sec : cellA FULL (1468568 + 64 + 616) 4 0.
  Proof.
    apply (cell0_cat FULL (1468568 + 64 + 616) 1 3); [lia | lia | lia | CL | CL].
  Qed.
  Lemma lock_quar : cellA FULL (0x166b70 + 152) 4 0.
  Proof.
    apply (cell0_cat FULL (0x166b70 + 152) 1 3); [lia | lia | lia | CL |].
    apply (cell0_cat FULL (0x166b70 + 152 + 1) 1 2); [lia | lia | lia | CL | CL].
  Qed.

  Theorem as0_art_rt_sec : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_sec FSG rn (art_gs0 FSG gfs0 k0) [] FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_sec. cbn [art_gs0 g_sec g_sec_committed g_log as0_rn rn_parr length]. change (Z.of_nat 0) with 0.
    pose proof (cellW (ELit 0) (1468568 + 64 + 8) 8 (bP cs) ltac:(chk)) as X. rewrite uE0 in X.
    pose proof (cellW (ELit 0) (1468568 + 64 + 16) 8 (bP cs) ltac:(chk)) as X2. rewrite uE0 in X2.
    repeat match goal with |- _ /\ _ => split end; try exact lock_sec; try CL; try exact X; try exact X2.
    - intros H. congruence.
    - intros H. discriminate H.
    - intros i s H. destruct i; discriminate H.
    - intros p [].
    - lia.
  Qed.

  Theorem as0_art_rt_quar : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_quar FSG rn (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_quar. cbn [art_gs0 g_qt g_qg as0_rn rn_t length app map art_batches_bytes fold_right]. change (Z.of_nat 0) with 0.
    assert (ZT : chk_zero (kn cs) (bT cs) 80 3088 = true) by chk.
    repeat match goal with |- _ /\ _ => split end; try lia; try exact lock_quar; try CL.
    - exists 0, 0. repeat split; try reflexivity; apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia.
    - exists 0, 0. repeat split; try reflexivity; CL.
    - constructor.
    - intros b [].
    - intros b it [].
    - cbn. constructor.
    - intros b [].
  Qed.

  Theorem as0_art_rt_ia : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_ia FSG (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_ia. cbn [art_gs0 g_ia g_qt g_qg].
    repeat match goal with |- _ /\ _ => split end; try CL.
    - intros H. discriminate H.
    - intros _. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma var_in : forall e lo hi, is_var_in (kn cs) e lo hi = true -> lo <= uE E e <= hi.
  Proof.
    intros e lo hi H. unfold is_var_in in H. destruct e; try discriminate.
    apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC Hin) as HK. cbn [kentry_ok] in HK. unfold uE. lia.
  Qed.

  Lemma img_zero4 : forall lo hi a, img_cover (kn cs) lo hi = true -> lo <= a -> a + 4 <= hi -> DEP_LO <= a -> a + 4 <= DEP_HI -> cellA FULL a 4 0.
  Proof.
    intros lo hi a H H1 H2 H3 H4. unfold img_cover in H. apply existsb_exists in H as (K & Hin & Hc).
    destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    unfold cell.
    assert (HN : forall x : word, a <= bv_unsigned x < a + Z.of_nat 4 -> FULL x = None).
    { intros x Hx. cbn in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      apply (hb_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC Hin); [lia|].
      unfold in_hull, DEP_LO, DEP_HI in *. cbn [img_lo img_hi ASAN0]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    pose proof (as0_dep_rdn_zero FULL 4%nat a H3 ltac:(cbn; lia) HN) as Hz. unfold ASEGS0 in Hz. rewrite Hz.
    rewrite (wleb_zero 4 ltac:(lia)). reflexivity.
  Qed.

  Definition K0D : nat := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!1'fT!1,fU!1,fV!1,fW!1,fX!1,fY!1,fZ,f[").

  Theorem as0_art_rt_depot : forall (FSG : Type) (gfs0 : FSG), art_rt_depot FSG rn (art_gs0 FSG gfs0 K0D) FULL.
  Proof.
    intros FSG gfs0. unfold art_rt_depot, DInvD. cbn [art_gs0 g_depot as0_rn rn_l2 rn_blk]. unfold NID, STO, MAP1, DEP, apart.
    exists 1, (uE E (tfE cs)), (uE E (stE cs)).
    pose proof sp0_win as W. RG I_L2 0x100000. RG I_BLK 0x800000. RA I_L2 I_BLK 0x100000 0x800000.
    destruct G as (l1 & l2 & l3 & l4 & l5 & l6). destruct G0 as (b1 & b2 & b3 & b4 & b5 & b6).
    pose proof (var_in (tfE cs) 2 3 ltac:(chk)) as VT. pose proof (var_in (stE cs) 2 3 ltac:(chk)) as VS.
    pose proof (cellW (ELit 0) 0x23bdc8 8 (tfE cs) ltac:(chk)) as X1. rewrite uE0 in X1.
    pose proof (cellW (ELit 0) (0x23bdc8 + 24) 4 (stE cs) ltac:(chk)) as X2. rewrite uE0 in X2.
    pose proof (cellW (ELit 0) 0x64bde8 8 (bL2 cs) ltac:(chk)) as X3. rewrite uE0 in X3.
    pose proof (cellW (ELit 0) (0x23bdc8 + 16) 8 (bBLK cs) ltac:(chk)) as X4. rewrite uE0 in X4.
    pose proof (wrK (ELit 0) 0x24bdd8 4194308 ltac:(chk)) as W1. rewrite uE0 in W1.
    pose proof (wrK (ELit 0) 0x23bdc8 32 ltac:(chk)) as W2. rewrite uE0 in W2.
    pose proof (wrK (bL2 cs) 0 (2 ^ 20) ltac:(chk)) as W3. rewrite Z.add_0_r in W3.
    pose proof (wrK (bBLK cs) 0 (2 ^ 23) ltac:(chk)) as W4. rewrite Z.add_0_r in W4.
    change (uE E (bL2 cs)) with (rbase E cs I_L2) in *. change (uE E (bBLK cs)) with (rbase E cs I_BLK) in *.
    unfold K0D. change (Z.of_nat 16384) with 16384.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try CL.
    -
      intros b Hb.
      pose proof (cellW (ELit 0) B1 4 (e_at (kn cs) (ELit 0) B1 4) ltac:(chk)) as Y1. rewrite uE0 in Y1. pose proof (var_in (e_at (kn cs) (ELit 0) B1 4) 0 1 ltac:(chk)) as V1.
      pose proof (cellW (ELit 0) B2 4 (e_at (kn cs) (ELit 0) B2 4) ltac:(chk)) as Y2. rewrite uE0 in Y2. pose proof (var_in (e_at (kn cs) (ELit 0) B2 4) 0 1 ltac:(chk)) as V2.
      unfold B1, B2 in *.
      destruct (Z.eq_dec b 414840) as [->|N1]; [eexists; split; [exact Y1 | lia]|].
      destruct (Z.eq_dec b 411694) as [->|N2]; [eexists; split; [exact Y2 | lia]|].
      exists 0. split; [|lia].
      destruct (Z_lt_dec b 411694); [|destruct (Z_lt_dec b 414840)].
      + apply (img_zero4 DEP_LO 4054672); [chk | unfold DEP_LO; lia | lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
      + apply (img_zero4 (4054672 + 4) 4067256); [chk | lia | lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
      + apply (img_zero4 (4067256 + 4) DEP_HI); [chk | lia | unfold DEP_HI; lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
    -
      intros id Hid. assert (id = 1) by lia. subst id.
      pose proof (cellW (bL2 cs) 16 8 (e_at (kn cs) (bL2 cs) 16 8) ltac:(chk)) as N1. pose proof (cellW (bL2 cs) 24 4 (ELit 0) ltac:(chk)) as N2. rewrite uE0 in N2.
      change (uE E (bL2 cs)) with (rbase E cs I_L2) in *.
      exists (uE E (e_at (kn cs) (bL2 cs) 16 8)), 0. pose proof (u64_range (edenot E (e_at (kn cs) (bL2 cs) 16 8))). unfold uE in *.
      repeat split; try lia; [exact N1 | replace (rbase E cs I_L2 + 16 * 1 + 8) with (rbase E cs I_L2 + 24) by ring; exact N2].
  Qed.

  (* [comment removed for export] *)
  Theorem as0_art_rt_ghost : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_ghost FSG rn (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. assert (C : cellA FULL (0x166b70 + 72) 8 0xe666661) by CL.
    unfold art_rt_ghost. cbn [art_gs0 g_qt g_qg g_cls app]. split; [intros b it []|]. split; [|split; [intros b []|exact C]].
    intros c Hc. cbn [art_cls0 cl_au cl_mfa cl_cache length]. split; [intros X; exfalso; lia|]. pose proof (art_ic_mc_range c ltac:(lia)). cbn. lia.
  Qed.

  Theorem as0_art_alloc_rep : forall (FSG : Type) (gfs0 : FSG), art_alloc_rep FSG rn (art_gs0 FSG gfs0 K0D) [] FULL.
  Proof.
    intros FSG gfs0. unfold art_alloc_rep.
    exact (conj as0_art_run_ok (conj as0_art_rt_statics (conj as0_art_rt_thread (conj (as0_art_rt_primary FSG gfs0 K0D)
             (conj (as0_art_rt_chunks FSG gfs0 K0D) (conj (as0_art_rt_sec FSG gfs0 K0D) (conj (as0_art_rt_quar FSG gfs0 K0D)
             (conj (as0_art_rt_depot FSG gfs0) (conj (as0_art_rt_ia FSG gfs0 K0D) (conj (fun b (Hb : In b []) => match Hb with end) (as0_art_rt_ghost FSG gfs0 K0D))))))))))).
  Qed.

  (* [comment removed for export] *)
  Lemma byteZ : forall b off n a, chk_zero (kn cs) b off n = true -> uE E b + off <= a < uE E b + off + n -> byte_at FULL a 0.
  Proof.
    intros b off n a H Ha. unfold byte_at.
    destruct (hc_zero ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model b off n HC H) as (_ & _ & Hz).
    replace a with (uE E b + off + (a - (uE E b + off))) by ring. apply Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Definition KSH : Z := 0x7fff8000 + 8192 * (SPB / 65536).
  Definition as0_EXTRA : list (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S20!2+^6+<+<|10;!3,^A0!4,^I+<+<'h1!2'E'h1!2'_6!1,B1!1,B|502;!1,^?0").
  Definition as0_A0x : list (Z * Z) := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!3'h2'h3/cs;/E;").

  #[using="Type"] Lemma as0_EXTRA_wf : A_wf as0_EXTRA.
  Proof.
    clear Hapc. unfold A_wf, as0_EXTRA, KSH, page_size. constructor; [|constructor]. cbn [fst snd].
    set (q := SPB / 65536).
    replace (2147450880 + 8192 * q) with ((524280 + 2 * q) * 4096) by ring.
    replace ((524280 + 2 * q) * 4096 + 2 ^ 34) with ((524280 + 2 * q + 4194304) * 4096) by ring.
    rewrite !Z.mod_mul by lia. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma vis_shadow_allowed : forall b n a m, vis_in cs b n = true ->
    uE E b <= a -> a + m <= uE E b + uE E n -> (uE E b + uE E n) mod 8 = 0 -> 0 < m -> 0 <= a -> a + m <= 2 ^ 47 ->
    shadow_allowed as0_A0x a m.
  Proof.
    intros b n a m Hv H1 H2 H8 Hm Ha Hhi x [X1 X2]. unfold HeapIfaceA.S, HeapIfaceA.SB in X1, X2.
    unfold vis_in in Hv. apply existsb_exists in Hv as (p & Hp & Hb). apply andb_prop in Hb as [Eb En].
    apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. destruct p as [pb pn]. cbn [fst snd] in Eb, En. subst pb pn.
    pose proof (page_base_le (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat (Z_to_bv 64 x)) as (P1 & P2 & P3).
    assert (Hx : 0 <= x < 2 ^ 64).
    { pose proof (Z.div_pos a 8 Ha ltac:(lia)). assert ((a + m - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with (2 ^ 44) in *. lia. }
    rewrite u64_lit in P1, P2 by exact Hx.
    unfold as0_A0x, as0_A0, A0_of, page_allowedb. rewrite existsb_app. apply orb_true_iff. left.
    apply existsb_exists. exists (pagedown (sh_lo ASAN0 E (b, n)), pageup (sh_hi ASAN0 E (b, n))). split.
    - unfold allowA. apply in_flat_map. exists (b, n). split; [apply in_or_app; left; exact Hp|]. right. left. reflexivity.
    - cbn [fst snd]. unfold sh_lo, sh_hi, page_size. cbn [fst snd shadow_off ASAN0].
      assert (L1 : uE E b / 8 <= a / 8) by (apply Z.div_le_mono; lia).
      assert (L2 : (a + m - 1) / 8 < (uE E b + uE E n) / 8).
      { pose proof (Z.div_mod (uE E b + uE E n) 8 ltac:(lia)) as D. rewrite H8 in D.
        assert ((a + m - 1) / 8 <= (uE E b + uE E n - 1) / 8) by (apply Z.div_le_mono; lia).
        assert ((uE E b + uE E n - 1) / 8 < (uE E b + uE E n) / 8); [|lia].
        apply Z.div_lt_upper_bound; [lia|]. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Variables BUDGET LENMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= Pm4ArtInv.KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + 2 ^ 34 + BUDGET <= AsanInitK.LIMIT.
  Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs)) + Pm4ArtInv.KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  #[local] Notation MAPS0 := (vm_maps (m_vmmaps model)).
  #[local] Notation RESV0 := (vm_reserved (m_vmmaps model)).
  #[local] Notation NOACC0 := (vm_noaccess (m_vmmaps model)).
  Definition as0_BASEx : Z := ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00!2'hS'h3/cs;").

  Theorem as0_art_binv :
    BINV Asan.M.loaded_segments MAPS0 RESV0 NOACC0 (rn_HI rn) as0_BASEx BUDGET [] as0_A0x FULL (m_vmmaps model) (m_vm_lazy model).
  Proof.
    apply BINV_intro. unfold rn_HI. cbn [as0_rn as0_ar rn_ar ar_sptop].
    assert (Hb : a_eager cs + a_abytes cs + A_bytes as0_EXTRA + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. lia. }
    eapply as0_binv_main with (LENMAX := LENMAX) (KMAX := Pm4ArtInv.KMAX) (EXTRA := as0_EXTRA); first [eassumption | exact as0_EXTRA_wf].
  Qed.

  Lemma as0_shdef : forall a : word, in_shadow_rw (bv_unsigned a) -> FULL a <> None.
  Proof.
    assert (Hb : a_eager cs + a_abytes cs + A_bytes as0_EXTRA + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. lia. }
    assert (B : BInv ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
                     (uE E e_sp0 - 8388608) (as0_BASE as0_EXTRA cs) BUDGET [] (as0_A0 as0_EXTRA cs E) FULL model)
      by (eapply as0_binv_main with (LENMAX := LENMAX) (KMAX := Pm4ArtInv.KMAX) (EXTRA := as0_EXTRA); first [eassumption | exact as0_EXTRA_wf]).
    intros a Ha. eapply bi_shdef; [exact B | exact Ha].
  Qed.

  Lemma byte1 : forall a v, chk_word (kn cs) (ELit 0) a 1 (ELit v) = true -> 0 <= a < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> in_shadow_rw a -> byte_at FULL a v.
  Proof.
    intros a v H Ha Hv Hs. pose proof (cellW (ELit 0) a 1 (ELit v) H) as X. rewrite uE0, (uE_lit E v Hv), Z.add_0_l in X.
    unfold cell in X. rewrite (art_bytes1 v Hv) in X. cbn [rdn] in X. unfold byte_at.
    pose proof (as0_shdef (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; exact Hs)) as D.
    destruct (FULL (Z_to_bv 64 a)) as [b|]; [|contradiction]. injection X as ->. reflexivity.
  Qed.

  Lemma glob_ok : forall g, glob_chk (kn cs) g = true -> shadow_blk FULL (fst g) (snd g).
  Proof.
    intros [beg size] H. cbn [fst snd]. unfold glob_chk in H. cbn [fst snd] in H.
    rewrite !andb_true_iff in H. destruct H as (((((H1 & H2) & H3) & H4) & H5) & H6). apply Z.leb_le in H3, H5. apply Z.ltb_lt in H4, H6.
    assert (Q1 : 0x10000 / 8 <= beg / 8) by (apply Z.div_le_mono; lia). assert (Q2 : beg / 8 <= 0x6c0000 / 8) by (apply Z.div_le_mono; lia).
    change (0x10000 / 8) with 8192 in Q1. change (0x6c0000 / 8) with 884736 in Q2.
    assert (Q3 : 0 <= size / 8) by (apply Z.div_pos; lia). assert (Q4 : size / 8 <= 8192 / 8) by (apply Z.div_le_mono; lia). change (8192 / 8) with 1024 in Q4.
    pose proof (Z.mod_pos_bound size 8 ltac:(lia)) as Q5.
    unfold shadow_blk, shadow_zero, HeapIfaceA.S, HeapIfaceA.SB. split.
    - intros j Hj. apply orb_prop in H1 as [H1 | H1]; [apply Z.eqb_eq in H1; lia|]. apply (byteZ (ELit 0) (beg / 8 + 0x7fff8000) (size / 8)); [assumption | rewrite uE0; lia].
    - intros NZ. apply orb_prop in H2 as [H2 | H2]; [apply Z.eqb_eq in H2; contradiction|].
      apply byte1; [assumption | lia | lia | unfold in_shadow_rw, LSH_LO, LSH_HI; left; lia].
  Qed.

  Theorem as0_art_c_statics : art_c_statics rn FULL.
  Proof.
    unfold art_c_statics. cbn [as0_rn as0_ar rn_tp rn_dtls]. unfold TP.
    pose proof sp0_win as W.
    pose proof (rgl I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (d1 & d2 & d3 & d4).
    pose proof (xpos (bD cs) ltac:(chk)) as PD. change (uE E (bD cs)) with (rbase E cs I_DTLS) in PD.
    assert (D4 : 4096 <= rbase E cs I_DTLS) by (pose proof (Z.div_mod (rbase E cs I_DTLS) 4096 ltac:(lia)); lia).
    split; [repeat split; lia|].
    split; [CL|]. split; [CL|]. split; [CL|].
    split. { pose proof (cellW (ELit 0) (TP + 8) 8 (bD cs) ltac:(chk)) as X. rewrite uE0 in X. exact X. }
    split. { pose proof (cellW (bD cs) 24 8 (ELit TP) ltac:(chk)) as X. rewrite (uE_lit E TP) in X by (unfold TP; lia). exact X. }
    split.
    { intros x Hx OP. destruct (zruns_cover ART_POISON ART_IMG_LO ART_IMG_HI x Hx OP) as (z & Hz & Hzx).
      assert (HZ : forallb (fun z => chk_zero (kn cs) (ELit 0) (fst z) (snd z)) (zruns ART_IMG_LO ART_POISON ART_IMG_HI) = true) by chk.
      apply (byteZ (ELit 0) (fst z) (snd z)); [exact (proj1 (forallb_forall _ _) HZ z Hz) | rewrite uE0; lia]. }
    split; [|exact as0_shdef].
    assert (HG : forallb (glob_chk (kn cs)) ART_GLOBALS = true) by chk.
    apply Forall_forall. intros g Hg. exact (glob_ok g (proj1 (forallb_forall _ _) HG g Hg)).
  Qed.

  Theorem as0_art_fsinv : art_fsinv_handoff -> art_fsinv rn art_fsg0 [] [] FULL.
  Proof.
    intros FSH. apply FSH; cbn [as0_rn as0_ar rn_ar rn_t rn_tp ar_fs]; unfold TP.
    -
      unfold art_fs_geo, rn_HI, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES. cbn [as0_rn as0_ar rn_ar rn_t rn_tp ar_fs ar_sptop]. unfold TP.
      pose proof sp0_win as W. RG I_FAKE 0xb09000. RA I_FAKE I_THREAD 0xb09000 4096. RG I_THREAD 4096.
      destruct G as (f1 & f2 & f3 & f4 & f5 & f6). specialize (f6 ltac:(unfold I_FAKE; lia)).
      pose proof (xpos (bF cs) ltac:(chk)) as PF. change (uE E (bF cs)) with (rbase E cs I_FAKE) in PF.
      assert (F4 : 4096 <= rbase E cs I_FAKE) by (pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)); lia).
      repeat split; lia.
    - pose proof (wrK (bF cs) 0 0xb09000 ltac:(chk)) as W. rewrite Z.add_0_r in W. exact W.
    - pose proof (cellW (ELit 0) TP 8 (bF cs) ltac:(chk)) as X. rewrite uE0 in X. exact X.
    - exact (cellW (bT cs) 72 8 (bF cs) ltac:(chk)).
    - pose proof (cellW (bF cs) 88 8 (ELit 20) ltac:(chk)) as X. rewrite (uE_lit E 20) in X by lia. exact X.
    - intros a Ha Hn. change (rbase E cs I_FAKE) with (uE E (bF cs)) in *.
      destruct (Z_lt_dec a (uE E (bF cs) + 88)).
      + apply (byteZ (bF cs) 0 88); [chk | lia].
      + apply (byteZ (bF cs) 96 (4096 + 32768 - 96)); [chk | lia].
    - exact as0_art_c_statics.
  Qed.

  Theorem as0_art_credit : forall (FSG : Type) (gfs0 : FSG), art_credit_ok FSG BUDGET rn (art_gs0 FSG gfs0 K0D) [] (8192, BUDGET).
  Proof.
    intros FSG gfs0. assert (KD : Z.of_nat K0D = 16384) by (unfold K0D; vm_compute; reflexivity).
    unfold art_credit_ok, art_nret, art_nq, Pm4ArtInv.KMAX.
    cbn [art_gs0 g_log g_sec g_depot g_cls g_qt g_qg app fst snd length art_cost_sum fold_right art_live fold_left].
    unfold art_cls0. cbn [cl_mu cl_free cl_cache length]. change (Z.of_nat 0) with 0.
    repeat split; try lia.
  Qed.

  Theorem as0_art_client : art_client_ok rn [] [] [] as0_A0x FULL.
  Proof.
    unfold art_client_ok. cbn [as0_rn as0_ar rn_ar ar_sptop ar_fs ar_stack_top ar_stack_bottom map].
    pose proof sp0_win as W. destruct HGEO_STK as (S1 & S2 & S3 & S4 & S5).
    pose proof (isp_facts_of ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) as ISP.
    pose proof (u_e_top ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP) as UT. pose proof (u_e_stk_len ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP) as UL.
    pose proof (utop_bounds E) as UB.
    repeat match goal with |- _ /\ _ => split end; try lia.
    - intros b [].
    - constructor.
    -
      apply (vis_shadow_allowed e_top e_stk_len); [chk | lia | lia | rewrite UT, UL; replace (utop E + (2 ^ 47 - utop E)) with (2 ^ 47) by ring; reflexivity | lia | lia | lia].
    -
      RG I_FAKE 0xb09000. destruct G as (f1 & f2 & f3 & f4 & f5 & f6).
      apply (vis_shadow_allowed (bF cs) (ELit 0xb09000)); change (uE E (bF cs)) with (rbase E cs I_FAKE); rewrite ?(uE_lit E 0xb09000) by lia; unfold FS_BYTES; try lia; [chk|].
      pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)) as D. rewrite f1 in D.
      replace (rbase E cs I_FAKE + 11571200) with ((512 * (rbase E cs I_FAKE / 4096) + 1446400) * 8) by lia. apply Z.mod_mul. lia.
    -
      apply (vis_shadow_allowed (ELit 0x10000) (ELit 0x6b0000)); rewrite ?(uE_lit E 0x10000), ?(uE_lit E 0x6b0000) by lia; try lia; [chk | reflexivity].

  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CHKZ : art_lazy_chk cs = true.
  #[local] Notation PARR := (rbase E cs I_PARR).
  #[local] Notation BLKB := (rbase E cs I_BLK).
  #[local] Notation RIS := (SPB + 2 ^ 37).

  Lemma lazy_parts : exists h1 h2, a_hlz cs = h1 ++ HSub (E_RISX cs) (ELit 4096) :: h2 /\ forallb (hop_pre cs) h1 = true
    /\ forallb (hop_zone cs) (a_hlz cs) = true
    /\ forallb (fun p => vis_hi (kn cs) p && own_ok cs p)%bool (a_vis cs ++ a_ghost cs) = true
    /\ 12 <= ealign (kn cs) (bBLK cs) /\ vis_in cs (bBLK cs) (ELit 0x800000) = true.
  Proof.
    pose proof CHKZ as H. unfold art_lazy_chk in H.
    apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    destruct (hsplit (E_RISX cs) (a_hlz cs)) as [[h1 h2]|] eqn:Hs; [|discriminate].
    exists h1, h2. split; [exact (hsplit_eq _ _ _ _ Hs)|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [apply Z.leb_le; exact C4 | exact C5].
  Qed.

  Lemma is_rng_sound : forall b n b0 L, is_rng b n b0 L = true -> 0 <= L < 2 ^ 64 -> uE E b = uE E b0 /\ uE E n = L.
  Proof.
    intros b n b0 L H HL. unfold is_rng in H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst.
    split; [reflexivity | apply uE_lit; exact HL].
  Qed.

  Lemma ris_val2 : uE E (E_RISX cs) = RIS.
  Proof.
    unfold E_RISX, uE. cbn [edenot]. rewrite u_add64. cbn [edenot]. rewrite (u64_lit 0x2000010000) by lia.
    pose proof sp0_win. destruct HGEO_SPB as ((K1 & K2) & _).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    unfold uE in *. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma hlz_ok : hops_in_maps (a_maps cs) (a_hlz cs) = true.
  Proof. pose proof CHK0 as H. unfold as0_chk in H. repeat (apply andb_prop in H as [H ?]). assumption. Qed.

  (* [comment removed for export] *)
  Lemma lazy_piece : forall q, In q (m_vm_lazy model) ->
    let b := bv_unsigned (fst q) in let e := bv_unsigned (fst q) + bv_unsigned (snd q) in
    ((BLKB <= b /\ e <= BLKB + 0x800000) \/ (PARR <= b /\ e <= PARR + 0x800000) \/ (KB <= b /\ e <= KB + 0x2000011000)
     \/ (0x7fff7000 <= b /\ e <= 0x10007fff8000))
    /\ (e <= RIS \/ RIS + 4096 <= b) /\ b < e.
  Proof.
    intros q Hq. cbv zeta. rewrite (hb_lazy ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) in Hq.
    destruct lazy_parts as (h1 & h2 & Hsplit & Hpre & Hzone & _).
    pose proof (hl_hops_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model (a_hlz cs) HC nofog hlz_ok) as WF.
    destruct (hl_replay E (a_hlz cs) WF q Hq) as (P1 & P2 & b & n & Hb & P3 & P4).
    split; [|split; [|lia]].
    - pose proof (proj1 (forallb_forall _ _) Hzone (HCons b n) Hb) as Hz. cbn [hop_zone] in Hz.
      repeat (apply orb_prop in Hz as [Hz|Hz]).
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. left. change (uE E (bBLK cs)) with BLKB in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. right. left. change (uE E (bP cs)) with PARR in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. right. right. left. change (uE E (bKS cs)) with KB in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x7fff7000) in E1 by lia. right. right. right. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x8fff7000) in E1 by lia. right. right. right. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x2008fff7000) in E1 by lia. right. right. right. lia.
    - rewrite Hsplit in Hq, WF.
      pose proof (hl_replay_sub E h1 (E_RISX cs) (ELit 4096) h2 WF) as SUB. rewrite ris_val2, (uE_lit E 4096) in SUB by lia.
      apply SUB; [|exact Hq]. intros b' n' Hin.
      pose proof (proj1 (forallb_forall _ _) Hpre (HCons b' n') Hin) as Hp. cbn [hop_pre] in Hp.
      destruct HGEO_SPB as ((K1 & K2) & _).
      apply orb_prop in Hp as [Hp|Hp]; destruct (is_rng_sound _ _ _ _ Hp ltac:(lia)) as [E1 E2]; rewrite E1, E2.
      + change (uE E (bBLK cs)) with BLKB.
        destruct (ra I_BLK I_KSPACE 0x800000 0x2000011000 ltac:(IDX) ltac:(IDX) ltac:(IDX) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as [X|X]; [left | right]; lia.
      + change (uE E (bP cs)) with PARR.
        destruct (ra I_PARR I_KSPACE 0x800000 0x2000011000 ltac:(IDX) ltac:(IDX) ltac:(IDX) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as [X|X]; [left | right]; lia.
  Qed.

  Lemma pb_facts : forall x : word, bv_unsigned (page_base x) <= bv_unsigned x < bv_unsigned (page_base x) + 4096 /\ bv_unsigned (page_base x) mod 4096 = 0.
  Proof.
    intros x. pose proof (page_base_le (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat x) as (P1 & P2 & P3). auto.
  Qed.

  (* [comment removed for export] *)
  Lemma as0_lazy_c1 : forall (FSG : Type) (gfs0 : FSG) (k0 : nat) (w : word),
    page_in_ranges (page_base w) (m_vm_lazy model) = true -> art_lazy_zone FSG rn (art_gs0 FSG gfs0 k0) (bv_unsigned w).
  Proof.
    intros FSG gfs0 k0 w Hl. destruct (hl_page_piece w _ Hl) as (q & Hq & Q1 & Q2).
    destruct (pb_facts w) as ((P1 & P2) & _). destruct (lazy_piece q Hq) as (Hz & Hr & _). cbv zeta in Hz, Hr.
    destruct HGEO_SPB as ((K1 & K2) & _).
    assert (NC : ~ (RIS <= bv_unsigned w < RIS + 4096)) by lia.
    assert (NCOM : ~ art_committed FSG rn (art_gs0 FSG gfs0 k0) (bv_unsigned w)).
    { unfold art_committed, rn_ris, rn_spb. cbn [as0_rn as0_ar rn_ar rn_qs ar_space_beg art_gs0 g_cls g_sec_committed]. unfold art_cls0. cbn [cl_mu cl_mfa].
      rewrite spb_qs. intros [X|[(c & _ & [X|X])|(X & _)]]; [exact (NC X) | lia | lia | discriminate X]. }
    unfold art_lazy_zone. cbn [as0_rn as0_ar rn_ar rn_blk rn_kbase rn_parr]. change (2 ^ 23) with 0x800000.
    destruct Hz as [Z|[Z|[Z|Z]]].
    - right. left. lia.
    - right. right. split; [right; lia | exact NCOM].
    - right. right. split; [left; lia | exact NCOM].
    - left. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma win_nolazy : forall lo hi, lo mod 4096 = 0 -> hi mod 4096 = 0 ->
    (forall q, In q (m_vm_lazy model) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)) ->
    forall x : word, lo <= bv_unsigned x < hi -> page_in_ranges (page_base x) (m_vm_lazy model) = false.
  Proof.
    intros lo hi Hlo Hhi Hap x Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:Hl; [exfalso | reflexivity].
    destruct (hl_page_piece x _ Hl) as (q & Hq & Q1 & Q2). destruct (pb_facts x) as ((P1 & P2) & P3).
    pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.div_mod hi 4096 ltac:(lia)) as D2.
    pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as D3. rewrite Hlo in D1. rewrite Hhi in D2. rewrite P3 in D3.
    destruct (Hap q Hq) as [X|X]; lia.
  Qed.

  Lemma apx_sound : forall zb zn p, apx (kn cs) zb zn p = true -> 0 <= zn < 2 ^ 64 ->
    (uE E zb + zn <= uE E (fst p) \/ uE E (fst p) + uE E (snd p) <= uE E zb) /\ 0 < uE E (snd p) /\ uE E (fst p) + uE E (snd p) <= 2 ^ 64.
  Proof.
    intros zb zn p H Hzn. unfold apx in H. destruct (split_lit zb) as [zb' zk] eqn:Hz. destruct (split_lit (fst p)) as [pb pk] eqn:Hp.
    apply andb_prop in H as [H Hap]. apply andb_prop in H as [Fz Fp].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (flat_x_sound ASEGS0 E _ (kn cs) zb' zk (ELit zn) HK Fz) as (A1 & A2 & A3).
    pose proof (flat_x_sound ASEGS0 E _ (kn cs) pb pk (snd p) HK Fp) as (B1 & B2 & B3).
    pose proof (split_lit_denot E _ zb' zk Hz) as Dz. pose proof (split_lit_denot E _ pb pk Hp) as Dp.
    cbn [edenot] in A2, A3. rewrite (u64_lit zn) in A2, A3 by lia.
    assert (Ez : uE E zb = estart E (SA zb' zk)).
    { unfold uE. rewrite Dz. unfold estart in *; cbn [a_base a_off] in *. rewrite u64_lit by lia. reflexivity. }
    assert (Ep : uE E (fst p) = estart E (SA pb pk)).
    { unfold uE. rewrite Dp. unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E (snd p))). rewrite u64_lit by lia. reflexivity. }
    pose proof (ranges_apart_x_sound ASEGS0 E _ (kn cs) _ _ _ _ _ _ HK Hap) as D.
    unfold elenZ in D. cbn [edenot] in D. rewrite (u64_lit zn) in D by lia. rewrite <- Ez, <- Ep in D.
    split; [exact D|]. split; [exact B3|]. rewrite Ep. unfold uE. lia.
  Qed.

  Lemma vis_hi_sound : forall p, vis_hi (kn cs) p = true -> uE E (fst p) + uE E (snd p) <= 2 ^ 47.
  Proof.
    intros p H. unfold vis_hi in H. apply orb_prop in H as [H|H].
    - apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. rewrite H1, H2.
      pose proof (isp_facts_of ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) as ISP.
      rewrite (u_e_top ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP), (u_e_stk_len ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP). lia.
    - destruct (xhi (kn cs) (fst p)) as [hi|] eqn:Hx; [|discriminate]. destruct (snd p) as [n| | | | | | |] eqn:Hn; try discriminate.
      apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
      pose proof (xhi_sound ASEGS0 E _ (kn cs) (fst p) hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx) as X.
      unfold uE. cbn [edenot]. rewrite (u64_lit n) by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma round_apart : forall b n zl zh, zl mod 4096 = 0 -> zh mod 4096 = 0 -> (zh <= b \/ b + n <= zl) ->
    zh <= pagedown b \/ pageup (b + n) <= zl.
  Proof.
    intros b n zl zh Hl Hh Hap. unfold pagedown, pageup.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct Hap as [X|X]; [left | right]; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  Lemma round_al : forall z, pagedown z mod 4096 = 0 /\ pageup z mod 4096 = 0 /\ pagedown z <= z <= pageup z.
  Proof.
    intros z. unfold pagedown, pageup. rewrite !Z.mod_mul by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    repeat split; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  Lemma round_id : forall z, z mod 4096 = 0 -> pagedown z = z /\ pageup z = z.
  Proof.
    intros z Hz. unfold pagedown, pageup.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Lemma own_window : forall p, In p (a_vis cs ++ a_ghost cs) ->
    let lo := pagedown (uE E (fst p)) in let hi := pageup (uE E (fst p) + uE E (snd p)) in
    (BLKB <= lo /\ hi <= BLKB + 0x800000)
    \/ (forall x : word, lo <= bv_unsigned x < hi -> page_in_ranges (page_base x) (m_vm_lazy model) = false).
  Proof.
    intros p Hp. cbv zeta. destruct lazy_parts as (_ & _ & _ & _ & _ & Hvis & HalB & _).
    pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hb. apply andb_prop in Hb as [_ Hown].
    pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
    pose proof (rgl I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (p1 & p2 & p3 & p4).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    destruct HGEO_SPB as ((K1 & K2) & K3).
    unfold own_ok in Hown. apply orb_prop in Hown as [Hown|Hown]; [apply orb_prop in Hown as [Hown|Hown]|].
    -
      destruct (is_rng_sound _ _ _ _ Hown ltac:(lia)) as [E1 E2]. rewrite E1, E2. change (uE E (bBLK cs)) with BLKB.
      destruct (round_id BLKB b1) as [R1 _]. destruct (round_id (BLKB + 0x800000) ltac:(rewrite Z.add_mod, b1 by lia; reflexivity)) as [_ R2].
      left. rewrite R1, R2. lia.
    -
      destruct (is_rng_sound _ _ _ _ Hown ltac:(lia)) as [E1 E2]. rewrite E1, E2, ris_val2.
      assert (RA4 : RIS mod 4096 = 0).
      { pose proof (Z.div_mod SPB 65536 ltac:(lia)) as D. rewrite K3 in D. replace RIS with ((16 * (SPB / 65536) + 33554432) * 4096) by lia. apply Z.mod_mul. lia. }
      destruct (round_id RIS RA4) as [R1 _]. destruct (round_id (RIS + 4096) ltac:(rewrite Z.add_mod, RA4 by lia; reflexivity)) as [_ R2].
      right. rewrite R1, R2. apply win_nolazy; [exact RA4 | rewrite Z.add_mod, RA4 by lia; reflexivity |].
      intros q Hq. destruct (lazy_piece q Hq) as (_ & Hr & _). exact Hr.
    -
      apply andb_prop in Hown as [Hown HB]. apply andb_prop in Hown as [HK HP].
      destruct (apx_sound _ _ _ HK ltac:(lia)) as (AK & NPOS & NW). destruct (apx_sound _ _ _ HP ltac:(lia)) as (AP & _ & _).
      change (uE E (bKS cs)) with KB in AK. change (uE E (bP cs)) with PARR in AP.
      set (b := uE E (fst p)) in *. set (n := uE E (snd p)) in *.
      destruct (round_al b) as (L1 & _ & L3). destruct (round_al (b + n)) as (_ & H2 & H3).

      pose proof CHK0 as C0. unfold as0_chk in C0. repeat (apply andb_prop in C0 as [C0 ?]).
      match goal with Hf : forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true |- _ =>
        pose proof (proj1 (forallb_forall _ _) Hf p Hp) as Hband end.
      assert (ABAND : b + n <= 0x7fff7000 \/ 0x10007fff8000 <= b).
      { pose proof (hl_off_band ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model p) as OB.
        destruct (Z_lt_le_dec b 0x7fff7000) as [Hlt|Hge].
        - left. destruct (Z_lt_le_dec 0x7fff7000 (b + n)) as [Hin|]; [exfalso | lia].
          apply (OB 0x7fff7000 HC Hband); [fold b n; lia | unfold SHB_LO, SHB_LEN; lia].
        - right. destruct (Z_lt_le_dec b 0x10007fff8000) as [Hin|]; [exfalso | lia].
          apply (OB b HC Hband); [fold b n; lia | unfold SHB_LO, SHB_LEN; lia]. }

      assert (ABLK : (b + n <= BLKB \/ BLKB + 0x800000 <= b) \/ (BLKB <= b /\ b + n <= BLKB + 0x800000 /\ b mod 4096 = 0 /\ n = 4096)).
      { apply orb_prop in HB as [HB|HB].
        - destruct (apx_sound _ _ _ HB ltac:(lia)) as (AB & _ & _). change (uE E (bBLK cs)) with BLKB in AB. left. fold b n in AB. lia.
        - apply andb_prop in HB as [HB1 HB2]. apply expr_eqb_eq in HB1. apply Z.leb_le in HB2.
          assert (N4 : n = 4096) by (unfold n; rewrite HB1; apply uE_lit; lia).
          destruct (ealign_sound ASEGS0 E _ (kn cs) (fst p) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as ((EA1 & EA2) & EA3).
          assert (B4 : b mod 4096 = 0).
          { unfold b, uE. apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ ealign (kn cs) (fst p))); [|exact EA3].
            exists (2 ^ (ealign (kn cs) (fst p) - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
          pose proof (Z.div_mod b 4096 ltac:(lia)) as D1. pose proof (Z.div_mod BLKB 4096 ltac:(lia)) as D2. rewrite B4 in D1. rewrite b1 in D2.
          destruct (Z_lt_le_dec b BLKB); [left; left; lia|]. destruct (Z_lt_le_dec b (BLKB + 0x800000)); [right; lia | left; right; lia]. }
      destruct ABLK as [ABLK|(I1 & I2 & I3 & I4)].
      + right. apply win_nolazy; [exact L1 | exact H2 |].
        intros q Hq. destruct (lazy_piece q Hq) as (Hz & _ & Hne). cbv zeta in Hz, Hne.
        destruct Hz as [Z|[Z|[Z|Z]]].
        * destruct (round_apart b n BLKB (BLKB + 0x800000) b1 ltac:(rewrite Z.add_mod, b1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n PARR (PARR + 0x800000) p1 ltac:(rewrite Z.add_mod, p1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n KB (KB + 0x2000011000) g1 ltac:(rewrite Z.add_mod, g1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n 0x7fff7000 0x10007fff8000 ltac:(reflexivity) ltac:(reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
      + left. destruct (round_id b I3) as [R1 _]. destruct (round_id (b + n) ltac:(rewrite I4, Z.add_mod, I3 by lia; reflexivity)) as [_ R2].
        rewrite R1, R2. lia.
  Qed.

  Lemma vis_in_In : forall b n, vis_in cs b n = true -> In (b, n) (a_vis cs ++ a_ghost cs).
  Proof.
    intros b n Hv. unfold vis_in in Hv. apply existsb_exists in Hv as (p & Hp & Hb). apply andb_prop in Hb as [Eb En].
    apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. destruct p as [pb pn]. cbn [fst snd] in Eb, En. subst pb pn. apply in_or_app. left. exact Hp.
  Qed.

  (* [comment removed for export] *)
  Lemma win_allowed : forall (A : list (Z * Z)) lo hi (x : word), In (lo, hi) A -> lo mod 4096 = 0 -> hi mod 4096 = 0 ->
    lo <= bv_unsigned x < hi -> page_allowedb A (page_base x) = true.
  Proof.
    intros A lo hi x Hin Hlo Hhi Hx. unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. unfold page_size.
    destruct (pb_facts x) as ((P1 & P2) & P3).
    pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.div_mod hi 4096 ltac:(lia)) as D2.
    pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as D3. rewrite Hlo in D1. rewrite Hhi in D2. rewrite P3 in D3.
    apply andb_true_intro. split; apply Z.leb_le; lia.
  Qed.

  Theorem as0_art_lazy_ok : forall (FSG : Type) (gfs0 : FSG), art_lazy_ok FSG rn (art_gs0 FSG gfs0 K0D) as0_A0x (m_vm_lazy model).
  Proof.
    intros FSG gfs0. unfold art_lazy_ok. cbn [as0_rn as0_ar rn_ar rn_blk rn_qs]. change (2 ^ 23) with 0x800000.
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & K3).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
    split; [exact (as0_lazy_c1 FSG gfs0 K0D)|]. split; [|split].
    -
      intros w Hw. unfold as0_A0x, as0_A0, A0_of in Hw. apply in_app_or in Hw as [Hw|Hw].
      + unfold allowA in Hw. apply in_flat_map in Hw as (p & Hp & Hwp). unfold allow1 in Hwp. destruct Hwp as [<-|[<-|[]]]; cbn [fst snd].
        * destruct (own_window p Hp) as [X|X]; [right; left; exact X | right; right; exact X].
        * left. destruct lazy_parts as (_ & _ & _ & _ & _ & Hvis & _).
          pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hb. apply andb_prop in Hb as [Hhi _]. apply vis_hi_sound in Hhi.
          unfold sh_lo, sh_hi. cbn [shadow_off ASAN0]. pose proof (u64_range (edenot E (fst p))) as U1. pose proof (u64_range (edenot E (snd p))) as U2. unfold uE in *.
          unfold pagedown, pageup.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          split; lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + unfold as0_EXTRA in Hw. destruct Hw as [<-|[]]. cbn [fst snd]. left. unfold KSH.
        pose proof (Z.div_mod SPB 65536 ltac:(lia)) as D. rewrite K3 in D. lia.
    -
      intros x Hx. apply (win_allowed as0_A0x KSH (KSH + 2 ^ 34)).
      + unfold as0_A0x, as0_A0, A0_of. apply in_or_app. right. left. reflexivity.
      + unfold KSH. replace (2147450880 + 8192 * (SPB / 65536)) with ((524280 + 2 * (SPB / 65536)) * 4096) by ring. apply Z.mod_mul. lia.
      + unfold KSH. replace (2147450880 + 8192 * (SPB / 65536) + 2 ^ 34) with ((524280 + 2 * (SPB / 65536) + 4194304) * 4096) by ring. apply Z.mod_mul. lia.
      + unfold KSH. lia.
    -
      intros x Hx. destruct lazy_parts as (_ & _ & _ & _ & _ & _ & _ & Hvin).
      apply (win_allowed as0_A0x BLKB (BLKB + 0x800000)); [| exact b1 | rewrite Z.add_mod, b1 by lia; reflexivity | lia].
      unfold as0_A0x, as0_A0, A0_of. apply in_or_app. left. unfold allowA. apply in_flat_map. exists (bBLK cs, ELit 0x800000).
      split; [exact (vis_in_In _ _ Hvin)|]. unfold allow1. cbn [fst snd]. left.
      rewrite (uE_lit E 0x800000) by lia. change (uE E (bBLK cs)) with BLKB.
      destruct (round_id BLKB b1) as [R1 _]. destruct (round_id (BLKB + 0x800000) ltac:(rewrite Z.add_mod, b1 by lia; reflexivity)) as [_ R2].
      rewrite R1, R2. reflexivity.
  Qed.

  Lemma role_kn : forall i L a n, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i <= a -> a + n <= rbase E cs i + L ->
    exists q, In q (KN0 MAPS0 RESV0) /\ fst q <= a /\ a + n <= snd q.
  Proof.
    intros i L a n Hi HL HLr Ha Hn. exists (ivZ (amap_den E (role cs i))). split.
    - unfold KN0. apply in_map. apply in_or_app. right.
      rewrite (hb_maps ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC nofog). apply in_map. apply role_in. rewrite len17. exact Hi.
    - unfold lit_len in HL. apply expr_eqb_eq in HL. pose proof (role_lit E cs i L HL HLr) as El.
      unfold ivZ, amap_den. cbn [fst snd]. unfold rbase, rlen, uE in *. lia.
  Qed.
  (* The image's reserved intervals are a prefix of the model's ledger ([co_res]); the
     ledger itself is [vm_reserved (m_vmmaps model)] at LPS 727298f3 (fuzz_bigint's form). *)
  Lemma seg_kn : forall b sz, In (Z_to_bv 64 b, Z_to_bv 64 sz) (segments_reserved ASEGS0) -> 0 <= b < 2 ^ 64 -> 0 <= sz < 2 ^ 64 ->
    exists q, In q (KN0 MAPS0 RESV0) /\ fst q <= b /\ b + sz <= snd q.
  Proof.
    intros b sz Hin Hb Hs. exists (ivZ (Z_to_bv 64 b, Z_to_bv 64 sz)). split.
    - unfold KN0. apply in_map. apply in_or_app. left.
      destruct (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as (rx & Hres & _). rewrite Hres. apply in_or_app. left. exact Hin.
    - unfold ivZ. cbn [fst snd]. rewrite !u64_lit by lia. lia.
  Qed.

  Theorem as0_art_kn_ok : art_kn_ok MAPS0 RESV0 rn.
  Proof.
    unfold art_kn_ok, art_objs. cbn [as0_rn as0_ar rn_ar rn_t rn_ctx rn_kbase rn_parr rn_l2 rn_blk rn_dtls ar_fs]. unfold FS_BYTES.
    change (2 ^ 23) with 0x800000. change (2 ^ 20) with 0x100000.
    intros o Ho.
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_THREAD 4096); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_CTX 0x10000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_KSPACE 0x2000011000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_PARR 0x800000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_L2 0x100000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_BLK 0x800000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_FAKE 0xb09000); [IDX | chk | lia | lia | lia]|].
    pose proof seg_kn as SK. rewrite asan0_res_eq in SK.
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply SK; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply SK; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply SK; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply SK; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|[]]. cbn [fst snd]. apply (role_kn I_DTLS 4096); [IDX | chk | lia | lia | lia].
  Qed.

  Lemma as0_art_eager : art_eager_ok [] as0_A0x (m_vm_lazy model).
  Proof. split; [eapply BINV_awf; exact as0_art_binv | intros b x []]. Qed.

  Theorem as0_art_handoff : art_fsinv_handoff ->
    art_handoff_target art_fsg MAPS0 RESV0 NOACC0 as0_BASEx BUDGET art_fsinv rn art_fsg0 K0D 8192 BUDGET as0_A0x FULL (vml_of model).
  Proof.
    intros FSH. unfold art_handoff_target, vml_of. cbn [fst snd].
    exact (conj (as0_art_alloc_rep art_fsg art_fsg0) (conj (as0_art_fsinv FSH) (conj as0_art_binv (conj (as0_art_credit art_fsg art_fsg0) (conj as0_art_client (conj as0_art_kn_ok (conj (as0_art_lazy_ok art_fsg art_fsg0) as0_art_eager))))))).
  Qed.
End Derive.
