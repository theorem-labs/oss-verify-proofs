(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (file_start's recorded proof replaced by the plain proof of the same lemma in leptonica/kernel_fuzzer, at this binary's addresses, over the stack floor lo := rt_sp0 - STACK_SPAN, the span the start state guarantees writable). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_libiface D_clx D_usage D_open D_read D_rlkit D_loopdefs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_file1 () := "I47Corelib4Init5Peano2le00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K54Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib2K54Spec5Canon:open_classC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K54Spec5Canon6oclass03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs6OPENEDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:D_loopdefs2RLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC69OSSVerify5KrLib2K53A238RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs6path_bC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53Lib6NodesA8open_entC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A236D_defs9sigma0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs:path_slackC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53A236D_open;nth1_argv_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_open7oc_fileC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs8argv_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs:main_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib2K53A238RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53A238RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr02C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_read;opened_walkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs8asta_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:D_loopdefs2FDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface>PMfd_fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs?PMfd_mat_stableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib2K53A238RT_iface5mcostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib2K53A238RT_iface7call_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indC69OSSVerify5KrLib2K53A238RT_iface9unwind_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface;malloc_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2K53A238RT_iface=af_live_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_clx8CLX_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237D_rlkit@agree_stack_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kit8agree_onC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC69OSSVerify5KrLib2K53A23:D_loopdefs4DCTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:D_loopdefs:DCTX_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_read?first_read_walkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC69OSSVerify5KrLib2K53A23:D_loopdefs5LOOPSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC69OSSVerify5KrLib2K53A23:D_loopdefs6cap_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem<bytes_at_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs7MAINCTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53A238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface7rt_presC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C69OSSVerify5KrLib2K53A238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs:CREDIT_DRVC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K53A238RT_iface8e_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9ALLOC_RASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6e_readC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K54Spec5Canon6oclass00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K53A236D_defs4fds0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs8RET_OPENC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4TP_AC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A238RT_iface8LIVE_MAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236Layout<g_read_stageC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A237D_file1<cap_ok_65536C1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section File1.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.
Hypothesis AF : art_facts RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis VARGV : valid_argv argvb.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Lemma cap_ok_65536 : cap_ok 65536.
Proof.
ltac2:(KReplay.run1 (kr_t_D_file1 ()) ["File1"] "h07__arithh14__ffh28__varmaph35__with41kp;2p;1p;3p;4p;7p;<g0000R0j2;Tg000Jj11Tg000oj15Tg001MR1j19Tg001mj26Tg002Jj27Tg002gj34Tg003Aj2>Tg003\j1=Tg004AR2j2<Tg004]j23Tg0057j1MTg005Wj1LTg0067j1JTg006Uj1ITg0073j1ETg007^j28Tg008Aj4CTg008lj7BTg009Pj2ATg00:2j2@Tg00:^j3DTg00;=j4?Tg00;oj4FTg00<Zj4GTg00=5j4HTg00=Oj1:Tg00=nl<KTf0R3#:#:p=2%13#1p=0g00>SR4g00?2R5P0P1P2g00?Pg00@2R2g00@QR1f3f2R0f1R6P3M<Kp=NP4%22#2#2#2#2R7,;3g00@o#1R8#1#0#0#0#0#0#0#0#5R9%58R:%93'6,79545'>X44P21;27R4%92,6:,79R:9459P4%=8#1#5R8,<1R41351P7P81358CNg00ATR7#M%L7%J5%I5%E5R7g00B@g00B_R9P9g00C?R9P51851g00C_1858CCg00DFFB1A79P3P0g00DfR9g00EFR7'31@30=497dAD516C?b1b2b3P4P3b0CF135:CGCHo"). Qed.

Theorem file_start : Z.of_nat (length argvb) = 2 -> open_class (nth 1 (argv_Z argvb) []) fs = OCFile data ->
  cps asegs (OPENED RT OUT_rep ERR_rep XENV LIB argvb fs) (RL RT OUT_rep ERR_rep XENV LIB argvb fs data 0 65536).
Proof using AF MAL VARGV OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros HL HCL T c HO Hk.
  destruct HO as (Σ & usp & ap & path & gp & s1 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7
                  & m & ent & HA & HCTX & HSIG & HB & Hap & Hhi & HENT & _).
  rewrite nth1_argv_Z in HCL. pose proof (oc_file _ _ _ HCL) as (HD & _). unfold path_b in HENT. rewrite HD in HENT.
  injection HENT as <-.
  pose proof HCTX as (ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HSIG as (LV & FRS & CR & USP0' & SPW).
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  (* [comment removed for export] *)
  destruct (ASTA_unpack RT Σ _ _ c HA) as (ms0 & RS0 & HA').
  destruct RS0 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & ->).
  rewrite (ret_pc_even RET_OPEN) in HA' by (unfold RET_OPEN; lia).
  pose proof (opened_walk usp gp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W1') HA').
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & <- & Hc1').
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  apply (MAL Σ (PMfd (FD argvb 0) fs) (Z_to_bv 64 0xf9680) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2) s1
           (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) s3 (Z_to_bv 64 3) (Z_to_bv 64 65536) s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m 65536 lo); try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - lia.
  - rewrite LV. reflexivity.
  - unfold mcost, CREDIT_DRV in *. cbn. lia.
  - intros _. rewrite LV. cbn [sec_bytes]. unfold SEC_BYTES. lia.   (* [comment removed for export] *)
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok. rewrite EU, !unsigned_lit by lia. split; [cbn; tauto|]. left. ul.
  - intros cf2 (Σ' & p & Hc2 & LV' & FRS' & SP' & CR' & Pp & Pal & Ptop).
    destruct (ASTA_unpack RT Σ' _ _ cf2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & Hc2').
    destruct RS2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST2, PRES2.
    pose proof (af_live_range RT AF Σ' m2 p 65536 ART2 ltac:(rewrite LV'; left; reflexivity)) as (PR1 & PR2 & PR3).
    assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB stdout_init m2)
      by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                  _ m m2 _ _ _ CLX0 PRES2 WM2).
    pose proof (agree_stack_pres _ _ _ _ _ PRES2) as AG2.
    assert (HD0 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m)
      by (split; [exact HCTX| tauto]).
    assert (HD2 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m2)
      by exact (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ' usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m2 HD0 ART2 MI2 WM2 ST2
                  SP' CLX2 AG2).
    (* [comment removed for export] *)
    pose proof (first_read_walk usp p gp t0' t1' t2' s1 a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) s3 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6' F' fc' m2 ltac:(ul) MI2) as W2.
    rewrite (ret_pc_even 0xf9680) in Hc2' by lia.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ' _ fs _ _ W2') Hc2').
    intros cf3 Hc3. apply Hk.
    destruct (ASTA_unpack RT Σ' _ _ cf3 Hc3) as (ms3 & <- & Hc3').
    exists Σ', usp, ap, path, p, gp, t0', t1', t2', a3', a4', a5', a6', a7', (Z_to_bv 64 p), s8, s9, s10, s11, t3', t4', t5', t6'.
    exists c0, c1, c2, c3, c4, c5, c6, c7, F', fc', m2.
    change (Z.min (65536 - 0) 65536) with 65536.
    split; [exact Hc3'|]. split; [exact HD2|].
    split; [split; [rewrite LV', LV; reflexivity|]; split; [rewrite FRS'; exact FRS|]; split; [rewrite CR'; unfold mcost, CREDIT_DRV in *; cbn; lia|
             rewrite SP'; exact USP0']|].
    split; [apply bytes_at_nil; ul|]. split; [lia|]. split; [lia| exact cap_ok_65536].
Qed.

End File1.
