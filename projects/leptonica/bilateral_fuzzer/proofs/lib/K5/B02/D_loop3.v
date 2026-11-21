(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (STACK_SPAN as the guaranteed stack span; the recorded (KReplay) proof of seg_grow re-proved by tactics, after leptonica/colorfill_fuzzer's copy at this binary's addresses). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_libiface D_clx D_usage D_open D_read D_rlkit D_loopdefs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_D_loop3 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6decideK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z8eqb_reflC45stdpp;list_basics4list;list_filterC47Corelib4Init9Datatypes3fstC35stdpp4base6filterC69OSSVerify5KrLib2K53B028RT_iface;live_removeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic3and00I47Corelib4Init6Specif7sumbool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00C35stdpp9decidable8True_decC69OSSVerify5KrLib2K53B02:D_loopdefs5RGROWC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53B02:D_loopdefs2RLC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53B02:D_loopdefs4DCTXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53B02:D_loopdefs5LOOPSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53B02:D_loopdefs6cap_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs7MAINCTXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs6path_bC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53B028RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs8argv_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs:main_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53B028RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9rt_creditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs<cap_ok_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs=cap_ok_doubleC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53B028RT_iface=af_live_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs2FDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface>PMfd_fdfs_onlyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs?PMfd_mat_stableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00K46Stdlib9micromega=RingMicromega5Psatz07C69OSSVerify5KrLib2K53B028RT_iface5mcostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init5Logic3and01C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53B028RT_iface7call_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC69OSSVerify5KrLib2K53B028RT_iface9unwind_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface;malloc_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8rt_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState;ret_pc_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_clx8CLX_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_rlkit@agree_stack_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs:DCTX_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC69OSSVerify5KrLib2K53B028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specC69OSSVerify5KrLib2K53B025D_kit=agree_of_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface<af_live_disjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_read>grow_ret_walk1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4ASTAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs8asta_evtC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53B028RT_iface;checked_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_rlkit@checked_src_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface;checked_dstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_rlkit@checked_dst_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9icpt_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface:rt_pres_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_clx;CLX_pres_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_rlkitCagree_stack_pres_exC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_read>grow_ret_walk2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9free_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7rt_presC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface:rt_after_fC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B027D_loop3Blive_remove_secondC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_clx;CLX_pres_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:D_loopdefs=DCTX_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_read>grow_ret_walk3C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG6Shadow3accC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8e_mallocC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs:CREDIT_DRVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K53B028RT_iface8RT_STACKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9ALLOC_RASC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC69OSSVerify5KrLib2K53B028RT_iface8e_memcpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface6e_freeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface6e_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53B026D_defs4TP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026Layout<g_read_stageC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2K53B028RT_iface8LIVE_MAXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison02C69OSSVerify5KrLib2K53B028RT_iface9SEC_BYTESC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope Z_scope.

Lemma live_remove_second : forall nb n1 buf n2, nb <> buf -> live_remove buf [(nb, n1); (buf, n2)] = [(nb, n1)].
Proof.
ltac2:(KReplay.run1 (kr_t_D_loop3 ()) [] "h01xh11Hh21bh31yh42H0h53bufh61eh72n1h82n2h92nbp;3p;1p;2p;6p;4p10000p4p7210R0p1000\p4p710p8P0g0018R0p4p710p8g001Vj31Tg0020j10Tg002Ij22Tg002fj2ETg003Gj2=Tg003gj1<Tg004Gj15Tg004ej16Tg005@j17Tg005^j24Tg0062j1;Tg006Rj33Tg0072j2DTg007Lj1CTP0j6:Tg007nj1>Tg008Sj3?Tg0090j6@Tg009Dj2ATg00:Dj4BTg00:dR0f0R1g00;DR231p=9g00;dR3P3f1R4P1CBp=8f3R5=134#0g00<B1241#9f2R6=134#0R7[A1341#01264#9[R81256#9\71E41P1n2001000000120000000X33X03P8^33^03P1f5R8P5P4O31285#9P0P21=33R7#<R9g00<]R:%51R;#6R<%0<P9%7;,4<f8f7R<'8R;P:f6R=/2=#5R>#6R?%0?P9%7>,4?18<=R<%;7R?537R>P?n200100000021000010000R@537P@n200100000021000010000;1>X20P0g00==P:g00=]R@%0@P9g00>9,4@P:%54R@#6RA%0AP9%7@,4AP>P?n200100000021000010000RA937;PAn200100000021000010000=19>X2018=8=37?R0,D9f4R>/2>%C>E:P:%52R2#6RA%0AP9%72,4AP:1288#5R8#6R:%0:P9%78,4:P0P?n200100000021000010000R:937<P:n200100000021000010000=190e12=>P1E:b1b4P7P9%>7A?331/25#5R1#6X67%71X0718>5R>1864=37?537R4E@A37>?R>519e1A64=19>eW1X83X53X73X93o"). Qed.

Section Loop3.
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
Hypothesis FRE : free_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.
Local Notation CLXp := (CLX_pres OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img).
Local Notation CLXx := (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img).

Theorem seg_grow : forall len cap,
  cps asegs (RGROW RT OUT_rep ERR_rep XENV LIB argvb fs data len cap) (RL RT OUT_rep ERR_rep XENV LIB argvb fs data cap (2 * cap)).
Proof using AF MAL FRE MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
  intros len cap T c HR Hk.
  destruct HR as (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                  & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HD & HLS & HBUF & Hlc & Hcd & Htop & HCAP).
  pose proof HD as ((ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) & HB & Hap & Hhi & SPW).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HLS as (LV & FRS & CR & USP0').
  pose proof (cap_ok_range cap HCAP) as CAPR.
  pose proof (cap_ok_double cap HCAP Htop) as HCAP2. pose proof (cap_ok_range _ HCAP2) as CAPR2.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  set (lo := rt_sp0 RT Σ - STACK_SPAN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  (* [comment removed for export] *)
  apply (MAL Σ (PMfd (FD argvb cap) fs) (Z_to_bv 64 0x9611c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
           (Z_to_bv 64 buf) (Z_to_bv 64 (2 * cap)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) (Z_to_bv 64 cap) (Z_to_bv 64 3)
           (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6 F fc m (2 * cap) lo);
    try reflexivity; try assumption; try (match goal with |- _ - STACK_WIN <= lo => unfold lo, STACK_WIN; lia end).
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - lia.
  - rewrite LV. reflexivity.
  - unfold mcost, CREDIT_DRV in *. destruct (Z.leb_spec (2 * cap) 64512); lia.
  - intros _. rewrite LV. cbn [sec_bytes]. unfold SEC_BYTES.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
  - unfold call_ok. rewrite EU. split; [exact ST0|]. ul.
  - unfold unwind_ok. rewrite EU, !unsigned_lit by lia. split; [cbn; tauto|]. left. ul.
  - intros cf1 (Σ1 & nb & Hc1 & LV1 & FRS1 & SP1 & CR1 & Pnb & Pal & Ptop).
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & WM1 & ST1) & PRES1 & WR1 & ACC1) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST1, PRES1.
    rewrite (ret_pc_even 0x9611c) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1) by exact (CLXp _ m m1 _ _ _ CLX0 PRES1 WM1).
    pose proof (agree_stack_pres _ _ _ _ _ PRES1) as AG1.
    assert (HD1 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ1 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m1)
      by exact (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ Σ1 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m m1 HD ART1 MI1 WM1 ST1
                  SP1 CLX1 AG1).
    assert (HBUF1 : bytes_at asegs m1 buf (firstn (Z.to_nat cap) data)).
    { apply (bytes_at_agree asegs m m1 _ _ HBUF). apply (agree_of_pres _ _ _ _ _ _ PRES1).
      intros x Hx. rewrite length_firstn in Hx. right; right; left. exists buf, cap. split; [exact INB| lia]. }
    assert (INN1 : In (nb, 2 * cap) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    assert (INB1 : In (buf, cap) (rt_live RT Σ1)) by (rewrite LV1, LV; right; left; reflexivity).
    assert (DISJ : nb + 2 * cap <= buf \/ buf + cap <= nb).
    { apply (af_live_disj RT AF Σ1 m1 nb (2 * cap) buf cap [] [(buf, cap)] ART1); [rewrite LV1, LV; reflexivity| left; reflexivity]. }
    pose proof (af_live_range RT AF Σ1 m1 nb (2 * cap) ART1 INN1) as (NR1 & NR2 & NR3).
    (* [comment removed for export] *)
    pose proof (grow_ret_walk1 usp buf cap nb gp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 path) (Z_to_bv 64 buf)
                  (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1
                  ltac:(ul) ltac:(lia) MI1) as W1.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W1') Hc1').
    intros cf2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & <- & Hc2').
    set (bs := firstn (Z.to_nat cap) data) in *.
    assert (LBS : Z.of_nat (length bs) = cap) by (unfold bs; rewrite length_firstn; lia).
    apply (MCP Σ1 (PMfd (FD argvb cap) fs) (Z_to_bv 64 0x96138) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2'
             (Z_to_bv 64 2) (Z_to_bv 64 nb) (Z_to_bv 64 nb) (Z_to_bv 64 buf) (Z_to_bv 64 cap) a3' a4' a5' a6' a7' (Z_to_bv 64 path)
             (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11
             t3' t4' t5' t6' F' fc' m1 nb buf bs lo); try reflexivity; try assumption; try (match goal with |- _ - STACK_WIN <= lo => unfold lo, STACK_WIN; lia end).
    + apply PMfd_fdfs_only.
    + apply PMfd_mat_stable.
    + rewrite LBS. reflexivity.
    + ul.
    + ul.
    + lia.
    + rewrite LBS. exact (checked_src_live RT AF Σ1 m1 _ lo buf cap buf cap ART1 INB1 ltac:(try unfold lo; unfold STACK_WIN in *; lia) ltac:(try unfold lo; unfold STACK_WIN in *; lia) ltac:(rewrite SP1; try unfold lo; unfold STACK_WIN in *; lia)).
    + rewrite LBS. exact (checked_dst_live RT AF Σ1 m1 _ nb (2 * cap) nb cap ART1 INN1 ltac:(lia) ltac:(lia) ltac:(lia)).
    + rewrite LBS. lia.
    + unfold call_ok. rewrite EU, SP1. split; [exact ST1|]. ul.
    + intros cf3 Hc3.
      destruct (ASTA_unpack RT Σ1 _ _ cf3 Hc3) as (ms3 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BS2) & Hc3').
      destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
      rewrite EU in ST2, PRES2. rewrite LBS in PRES2.
      rewrite (ret_pc_even 0x96138) in Hc3' by lia.
      assert (CLX2 : CLX OUT_rep ERR_rep XENV LIB stdout_init m2)
        by exact (CLXx _ m1 m2 _ _ _ _ _ CLX1 PRES2 WM2 ltac:(intros x Hx; unfold SEGTOP_A in *; lia)).
      pose proof (agree_stack_pres_ex _ _ _ _ _ _ _ PRES2 ltac:(ul)) as AG2.
      assert (HD2 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ1 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m2).
      { apply (DCTX_agree RT OUT_rep ERR_rep XENV LIB argvb AF Σ1 Σ1 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m1 m2 HD1 ART2 MI2 WM2);
          [rewrite SP1; exact ST2| reflexivity| exact CLX2| exact AG2]. }
      (* [comment removed for export] *)
      pose proof (grow_ret_walk2 usp buf gp u0 u1 u2 (Z_to_bv 64 nb) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 path) (Z_to_bv 64 nb)
                    (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) s8 s9 s10 s11 u3 u4 u5 u6
                    F2 fc2 m2 MI2) as W2.
      lazymatch type of W2 with evt asegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ1 _ fs _ _ W2') Hc3').
      intros cf4 Hc4.
      destruct (ASTA_unpack RT Σ1 _ _ cf4 Hc4) as (ms4 & <- & Hc4').
      apply (FRE Σ1 (PMfd (FD argvb cap) fs) (Z_to_bv 64 0x96140) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) u0 u1 u2
               (Z_to_bv 64 2) (Z_to_bv 64 nb) (Z_to_bv 64 buf) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 path) (Z_to_bv 64 cap)
               (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 u3 u4 u5 u6
               F2 fc2 m2 buf cap lo); try reflexivity; try assumption; try (match goal with |- _ - STACK_WIN <= lo => unfold lo, STACK_WIN; lia end).
      * apply PMfd_fdfs_only.
      * apply PMfd_mat_stable.
      * unfold call_ok. rewrite EU, SP1. split; [exact ST2|]. ul.
      * unfold unwind_ok. rewrite EU, !unsigned_lit by lia. split; [cbn; tauto|]. left. ul.
      * intros cf5 (Σ2 & v & Hc5 & LV2 & FRS2 & SP2 & CR2).
        destruct (ASTA_unpack RT Σ2 _ _ cf5 Hc5) as (ms5 & (m3 & RS3 & (ART3 & MI3 & ST3) & PRES3) & Hc5').
        destruct RS3 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
        rewrite EU in ST3, PRES3.
        rewrite (ret_pc_even 0x96140) in Hc5' by lia.
        rewrite LV1, LV, live_remove_second in LV2 by lia.
        assert (CLX3 : CLX OUT_rep ERR_rep XENV LIB stdout_init m3)
          by exact (CLX_pres_nw OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img _ m2 m3 _ _ _ CLX2 PRES3).
        pose proof (agree_stack_pres _ _ _ _ _ PRES3) as AG3.
        assert (HD3 : DCTX RT OUT_rep ERR_rep XENV LIB argvb Σ2 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m3).
        { apply (DCTX_agree_nw RT OUT_rep ERR_rep XENV LIB argvb AF Σ1 Σ2 usp ap path c0 c1 c2 c3 c4 c5 c6 c7 m2 m3 HD2 ART3 MI3);
            [rewrite SP1; exact ST3| rewrite SP2, SP1; reflexivity| exact CLX3| exact AG3]. }
        assert (HBUF3 : bytes_at asegs m3 nb (firstn (Z.to_nat cap) data)).
        { apply (bytes_at_agree asegs m2 m3 _ _ BS2). apply (agree_of_pres _ _ _ _ _ _ PRES3).
          intros x Hx. rewrite LBS in Hx. right; right; left. exists nb, (2 * cap). rewrite LV2. split; [left; reflexivity| lia]. }
        (* [comment removed for export] *)
        pose proof (grow_ret_walk3 usp nb cap gp w0 w1 w2 v d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 path) (Z_to_bv 64 3)
                      (Z_to_bv 64 g_read_stage) (Z_to_bv 64 buf) s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m3 ltac:(lia) MI3) as W3.
        lazymatch type of W3 with evt asegs _ ?X =>
          assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
        clear W3.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ2 _ fs _ _ W3') Hc5').
        intros cf6 Hc6. apply Hk.
        destruct (ASTA_unpack RT Σ2 _ _ cf6 Hc6) as (ms6 & <- & Hc6').
        exists Σ2, usp, ap, path, nb, gp, w0, w1, w2, d3, d4, d5, d6, d7, (Z_to_bv 64 buf), s8, s9, s10, s11, w3, w4, w5, w6.
        exists c0, c1, c2, c3, c4, c5, c6, c7, F3, fc3, m3.
        split; [exact Hc6'|]. split; [exact HD3|].
        split; [split; [exact LV2|]; split; [rewrite FRS2, FRS1; exact FRS|]; split; [rewrite CR2, CR1; unfold mcost, CREDIT_DRV in *;
                 destruct (Z.leb_spec (2 * cap) 64512); lia| rewrite SP2, SP1; exact USP0']|].
        split; [exact HBUF3|]. split; [lia|]. split; [lia| exact HCAP2].
Qed.

End Loop3.
