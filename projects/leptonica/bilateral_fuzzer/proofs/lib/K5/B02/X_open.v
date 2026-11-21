(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs Require Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_frmkit D_iface D_defs D_kit D_clx D_rlkit X_openw.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_X_open () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_addC69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01C69OSSVerify5KrLib2K53Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame7outsideC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K53B028RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC69OSSVerify5KrLib2K53Lib6NodesA8open_entC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib2K53B028RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface:errno_cellC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2or00C69OSSVerify5KrLib2K53B027D_iface9ssp_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface3ARTC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53B028RT_iface4PMfdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4ASTAC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C69OSSVerify5KrLib2K53B028RT_iface6ret_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface:musl_afterC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC69OSSVerify5KrLib2K53B028RT_iface<af_sp0_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib2K53Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr01C69OSSVerify5KrLib2K53B027D_rlkit6stk_wrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem;wr_at_belowC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K53B027X_openw:open_walkAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs8asta_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs;ASTA_unpackC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init3Nat3addC46Stdlib5Lists4List:length_appC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib2K53B025D_kit>agree_of_munchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8rt_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Nodes6efferrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Nodes4eff0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defsBASTA_PM_mat_stableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS?mat_stable_pureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS>mat_stable_andC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6NodesA7open_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS5nretAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC69OSSVerify5KrLib2K53Lib5Nodes4aregC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z5ldiffC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC69OSSVerify5KrLib2K53Lib3Mem>bytes_at_boundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib2K53Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53B028RT_iface4ARTMC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC69OSSVerify5KrLib2K53B028RT_iface;af_with_fdsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6DecodeCopenat_errnos_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib2K53Lib7SysStep:mkR_set_a0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01c69OSSVerify5KrLib2K53B026X_open;nretA_MSsvcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface4frmWC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit>rw_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit>ro_cells_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027X_openw>open_walkB_errC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7rt_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9rt_framesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7aclientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface=client_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface7in_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface@in_fframe_shadowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53B025D_clxCclient_static_introC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8af_frameC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega5Tauto8GFormula02C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc69OSSVerify5KrLib2K53B026X_open;munch_mergeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs;ASTA_conseqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS<cps_realizesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC69OSSVerify5KrLib2K53Lib5RzCPS5macctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3HIDC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC69OSSVerify5KrLib2K52AS8AsanAcct8restrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS2HZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_frmkit;ASTF_conseqC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Fs4Open;alloc_fd_leK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega7Formula01C69OSSVerify5KrLib2K53B027X_openw=open_walkB_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B029RT_frmkit=ast_open_br_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface=open_contractC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8entry_stC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2K53Lib5RzCPS4cps2C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53Lib5RzCPS3ASTC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface7GOT_SSPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface9SSP_GUARDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_iface6e_openC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI47Corelib4Init5Logic4True00C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC69OSSVerify5KrLib2K53B028RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface:USTACK_TOPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53Lib3Mem4UTOPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs8asegs_wxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026D_defs;asegs_belowC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4OpenBopen_ignored_flagsc69OSSVerify5KrLib2K53B026X_open8pc_93368C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib2K53B029RT_frmkit?ast_open_fail_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B027D_ifaceEopen_refused_contractC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3cpsC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma nretA_MSsvc : forall R F pc x8 fc rv m ro r,
  nretA (MSsvc R F pc x8 fc rv m ro) (mkEffect r [] []) = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4)%bv fc None m ro.
Proof. reflexivity. Qed.

Lemma pc_93368 : (Z_to_bv 64 0x101a84 + Z_to_bv 64 4)%bv = Z_to_bv 64 0x101a88.
Proof.
ltac2:(KReplay.run1 (kr_t_X_open ()) [] "p;1p;2g002Fj12Tg002kj11Tg0053j13Tg00;Fj24Tf0#2#2p=0g009>R0#2#0#0#0#1#1#2#1#2#1#0#0#1#0#3%00#3'4o"). Qed.

Lemma munch_merge : forall (W1 W2 W : list (Z * Z)) m1 m2 m3, munch W1 m1 m2 -> munch W2 m2 m3 ->
  (forall x, outside W x -> outside W1 x /\ outside W2 x) -> munch W m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_X_open ()) [] "h01xh11Ah21Bh32H1h42H2h52HWh62Hxh71Wh82W1h92W2h:1ah;2m1h<2m2h=2m3h>1op;2p;1p;3p;6g00<Dj2;Tg00<dj1:Tg002Fj11Tg003Pj15Tg003nj17Tg004Qj19Tg00=Dj34Tg00>;j20Tg00?4R0j23Tg00?Oj22Tg00@9j36Tg000`j68Tg00@SR1/;1#:R2g009>#1#1#1R3#1#1#1#5R4#7R5%53#7#9R3[R6f5R7f2R8f1R934R:f6R;f0R<'0f9R=/09f8R>/09'3[^01f7R1124<'0P81249R?P<O2f:R@/0?10=?'3P0f;R01248R8'010@8P1f3R8O1P=P8O1563P<f=R?f4,24'01247,0?P3P0P;O1P?P1O1963<X>3P=P;P9O2P@P;O1P>P;P<O2E8W2W1P9P<O2n2001000000120000000b:W6X05A4;78eW5X4:W3X=6X<6W;X72X92W8o"). Qed.

Section XOpen.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, TP_A, ERRNO_A, SSP_GUARD in *; lia.

Theorem open_ok : open_contract RT.
Proof using AF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path s lo ent
    Ha0 Ha1 HB HNZ HSL HDD HENT HFREE ST LO SPW ERRN (g & G1 & G2) ART0 MI0 HTP HSEP.
  subst a0 a1 tp.
  intros T1 T2 c Hc Hk1 Hk2.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  assert (SEG : SEGTOP_A <= lo) by ul.
  assert (UTOPsp : usp <= 2^47).
  { pose proof (wr_at_below asegs m lo (usp - lo) MI0 (stk_wr m lo usp lo (usp - lo) ST ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)).
    unfold UTOP in *. lia. }
  pose proof (open_walkA usp path ra gp (Z_to_bv 64 0x64cf48) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo g ST SEG LO ltac:(lia) G1 G2 MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0xf75e4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x64cf48) (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0)
                       (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (-100)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x101a84) (Z_to_bv 64 56) fc None m1 (seg_rom asegs)) in *.
  assert (HB1 : bytes_at asegs m1 path (s ++ [Z_to_bv 8 0])).
  { apply (bytes_at_agree asegs m m1 _ _ HB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn.
    rewrite length_app in Hx. cbn [length] in Hx. split; [lia| exact I]. }
  unfold ASTA in Hc1'.
  apply (ast_open_br_f asegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun e ms => nretA msA (efferr e) = ms) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun fdw ms => nretA msA (eff0 fdw) = ms) (fun fdw mo => fdw = alloc_fd F0 /\ (ARTM RT Σ mo /\ PMfd (fd_insert F0 fdw ent) fs0 mo))
           s fs0 ent); [| | exact HENT| | | exact Hc1'| |].
  - exact (ASTA_PM_mat_stable RT AF Σ F0 fs0).
  - intros fdw. apply mat_stable_and; [apply mat_stable_pure| exact (ASTA_PM_mat_stable RT AF Σ _ fs0)].
  - intros ms <-. split; [| split; intros; reflexivity].
    split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [exact HNZ|]. split; [exact HSL|].
    split; [exact HDD|]. split; [reflexivity|].
    change (areg msA 11) with (Z_to_bv 64 path). pose proof (bytes_at_bound asegs m1 path _ HB1) as BB.
    rewrite unsigned_lit by (rewrite length_app in BB; cbn [length] in BB; lia). exact HB1.
  - intros mo (HAR & HF & HFS & HRD). split; [exact HFS|]. split; [split; [exact HAR| exact (conj HF (conj HFS HRD))]|].
    rewrite HF. split; [exact HFREE|]. split; [reflexivity|].
    split; [apply (af_with_fds RT AF); exact HAR| split; [reflexivity| split; [exact HFS| exact HRD]]].
  - (* [comment removed for export] *)
    intros c2 (e & He & Hc2). pose proof (openat_errnos_range e He) as HeR.
    assert (EQ : nretA msA (efferr e) = MS (mkR (Z_to_bv 64 0xf75e4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x64cf48) (Z_to_bv 64 path)
                   t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (- e)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0)
                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x101a88) fc None m1 (seg_rom asegs)).
    { unfold msA, efferr, eff0, errno_ret. rewrite nretA_MSsvc, mkR_set_a0, pc_93368. reflexivity. }
    rewrite EQ in Hc2.
    assert (ERR0 : exists errv, rw_cells asegs m (errno_cell (Z_to_bv 64 0x64cf48)) [C4 errv]) by (destruct ERRN as [H|H]; [eexists; exact H| exact H]).
    destruct ERR0 as (errv & ERR0).
    assert (EE : errno_cell (Z_to_bv 64 0x64cf48) = 0x64cea4) by (unfold errno_cell; rewrite unsigned_lit by lia; reflexivity).
    rewrite EE in ERR0.
    assert (ERR1 : rw_cells asegs m1 (bv_unsigned (Z_to_bv 64 0x64cf48) + -164) [C4 errv]).
    { rewrite unsigned_lit by lia. apply (rw_cells_agree asegs m m1 _ _ ERR0); [| exact WM1].
      apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    assert (G2' : ro_cells asegs m1 SSP_GUARD [C8 g]).
    { apply (ro_cells_agree asegs m m1 _ _ G2). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    pose proof (open_walkB_err usp path e ra gp (Z_to_bv 64 0x64cf48) t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m1 lo g errv junk ST1 SEG LO ltac:(lia) HeR FR1 G2' ERR1 ltac:(rewrite unsigned_lit; lia)
                  ltac:(rewrite unsigned_lit by lia; lia) MI1) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt RT AF Σ F0 fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk1.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m2 & RS & MU2 & WM2 & MI2 & ERR2 & ST2) & Hc3').
    rewrite unsigned_lit in MU2, ERR2 by lia.
    assert (ART2 : ART RT Σ m2).
    { apply (af_frame RT AF Σ m m2 (usp - 128) ART0); [lia| | exact (wmono_trans asegs m m1 m2 WM1 WM2)].
      intros a Ha. rewrite (MU2 a), (MU1 a); [reflexivity| |].
      - cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia| exact I].
      - cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia|]. split; [| exact I].
        intros Hin. apply Ha. right; left. apply client_static_intro. lia. }
    exists e, m2. split; [exact He|].
    eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
    split; [rewrite ESP; exact RS|].
    split; [| unfold errno_cell; rewrite unsigned_lit by lia; exact ERR2].
    split; [exact ART2|]. split; [exact MI2|]. split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|].
    split; [exact ST2|].
    apply (munch_merge [(usp - 96, usp)] [(usp + -112, usp + -96); (0x64cea4, 0x64cea4 + 4)] _ m m1 m2 MU1 MU2).
    intros x Hx. unfold errno_cell in Hx. rewrite unsigned_lit in Hx by lia. cbn in Hx |- *. intuition lia.
  - (* [comment removed for export] *)
    intros c2 (fdw & Hc2).
    pose proof Hc2 as (_ & _ & (Efd & _) & _). subst fdw.
    assert (Hc2' : AST SEGTOP_A (rt_allow RT Σ) (frmW (fun ms => nretA msA (eff0 (alloc_fd F0)) = ms))
                     (fun mo => ARTM RT Σ mo /\ PMfd (fd_insert F0 (alloc_fd F0) ent) fs0 mo) c2).
    { apply (ASTF_conseq SEGTOP_A _ _ _ _ _ c2 Hc2); [intros ms H; exact H| intros mo (_ & H); exact H]. }
    clear Hc2. rename Hc2' into Hc2.
    pose proof (LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open.alloc_fd_le F0) as AFL.
    set (fd := bv_unsigned (alloc_fd F0)) in *.
    assert (EFD : alloc_fd F0 = Z_to_bv 64 fd) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (FDR : 0 <= fd) by (pose proof (bv_unsigned_in_range 64 (alloc_fd F0)); lia).
    assert (EQ : nretA msA (eff0 (alloc_fd F0)) = MS (mkR (Z_to_bv 64 0xf75e4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x64cf48)
                   (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 fd) (Z_to_bv 64 path) (Z_to_bv 64 0x8000)
                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x101a88) fc None m1 (seg_rom asegs)).
    { unfold msA, eff0. rewrite nretA_MSsvc, mkR_set_a0, pc_93368, <- EFD. reflexivity. }
    rewrite EQ in Hc2.
    assert (G2' : ro_cells asegs m1 SSP_GUARD [C8 g]).
    { apply (ro_cells_agree asegs m m1 _ _ G2). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    pose proof (open_walkB_ok usp path fd ra gp (Z_to_bv 64 0x64cf48) t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m1 lo g junk ST1 SEG LO ltac:(lia) ltac:(lia) FR1 G2' MI1) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk2.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (RS & ST2) & Hc3').
    assert (ART1 : ART RT Σ m1).
    { apply (af_frame RT AF Σ m m1 (usp - 128) ART0); [lia| | exact WM1].
      intros a Ha. rewrite (MU1 a); [reflexivity|]. cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia| exact I]. }
    exists m1. eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
    split; [rewrite ESP, EFD; exact RS|].
    split; [exact ART1|]. split; [exact MI1|]. split; [exact WM1|]. split; [exact ST2|].
    intros x Hx. apply MU1. cbn in Hx |- *. intuition lia.
Qed.

Theorem open_refused_ok : open_refused_contract RT.
Proof using AF.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path s lo
    Ha0 Ha1 HB HNZ HSL HDD HENT ST LO SPW (errv & ERR0) (g & G1 & G2) ART0 MI0 HTP HSEP.
  subst a0 a1 tp.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  assert (SEG : SEGTOP_A <= lo) by ul.
  assert (UTOPsp : usp <= 2^47).
  { pose proof (wr_at_below asegs m lo (usp - lo) MI0 (stk_wr m lo usp lo (usp - lo) ST ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)).
    unfold UTOP in *. lia. }
  pose proof (open_walkA usp path ra gp (Z_to_bv 64 0x64cf48) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo g ST SEG LO ltac:(lia) G1 G2 MI0) as W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0xf75e4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x64cf48) (Z_to_bv 64 path) t1 t2 (Z_to_bv 64 0)
                       (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (-100)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x101a84) (Z_to_bv 64 56) fc None m1 (seg_rom asegs)) in *.
  assert (HB1 : bytes_at asegs m1 path (s ++ [Z_to_bv 8 0])).
  { apply (bytes_at_agree asegs m m1 _ _ HB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn.
    rewrite length_app in Hx. cbn [length] in Hx. split; [lia| exact I]. }
  unfold ASTA in Hc1'.
  apply (ast_open_fail_f asegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun e ms => nretA msA (efferr e) = ms) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo) s fs0); [| exact HENT| | | exact Hc1'|].
  - exact (ASTA_PM_mat_stable RT AF Σ F0 fs0).
  - intros ms <-. split; [| intros; reflexivity].
    split; [reflexivity|]. split; [reflexivity|]. split; [vm_compute; reflexivity|]. split; [exact HNZ|]. split; [exact HSL|].
    split; [exact HDD|]. split; [reflexivity|].
    change (areg msA 11) with (Z_to_bv 64 path). pose proof (bytes_at_bound asegs m1 path _ HB1) as BB.
    rewrite unsigned_lit by (rewrite length_app in BB; cbn [length] in BB; lia). exact HB1.
  - intros mo (HAR & HF & HFS & HRD). split; [exact HFS| split; [exact HAR| exact (conj HF (conj HFS HRD))]].
  - intros c2 (e & HeR & Hc2).
    assert (EQ : nretA msA (efferr e) = MS (mkR (Z_to_bv 64 0xf75e4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0x64cf48) (Z_to_bv 64 path)
                   t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (- e)) (Z_to_bv 64 path) (Z_to_bv 64 0x8000) (Z_to_bv 64 0)
                   (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 56) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x101a88) fc None m1 (seg_rom asegs)).
    { unfold msA, efferr, eff0, errno_ret. rewrite nretA_MSsvc, mkR_set_a0, pc_93368. reflexivity. }
    rewrite EQ in Hc2.
    assert (EE : errno_cell (Z_to_bv 64 0x64cf48) = 0x64cea4) by (unfold errno_cell; rewrite unsigned_lit by lia; reflexivity).
    rewrite EE in ERR0.
    assert (ERR1 : rw_cells asegs m1 (bv_unsigned (Z_to_bv 64 0x64cf48) + -164) [C4 errv]).
    { rewrite unsigned_lit by lia. apply (rw_cells_agree asegs m m1 _ _ ERR0); [| exact WM1].
      apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    assert (G2' : ro_cells asegs m1 SSP_GUARD [C8 g]).
    { apply (ro_cells_agree asegs m m1 _ _ G2). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    pose proof (open_walkB_err usp path e ra gp (Z_to_bv 64 0x64cf48) t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6 F fc m1 lo g errv junk ST1 SEG LO ltac:(lia) HeR FR1 G2' ERR1 ltac:(rewrite unsigned_lit; lia)
                  ltac:(rewrite unsigned_lit by lia; lia) MI1) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt RT AF Σ F0 fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m2 & RS & MU2 & WM2 & MI2 & ERR2 & ST2) & Hc3').
    rewrite unsigned_lit in MU2, ERR2 by lia.
    assert (ART2 : ART RT Σ m2).
    { apply (af_frame RT AF Σ m m2 (usp - 128) ART0); [lia| | exact (wmono_trans asegs m m1 m2 WM1 WM2)].
      intros a Ha. rewrite (MU2 a), (MU1 a); [reflexivity| |].
      - cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia| exact I].
      - cbn. split; [intros Hin; apply Ha; left; unfold USTACK_TOP in *; lia|]. split; [| exact I].
        intros Hin. apply Ha. right; left. apply client_static_intro. lia. }
    exists e, m2. split; [exact HeR|].
    eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
    split; [rewrite ESP; exact RS|].
    split; [| unfold errno_cell; rewrite unsigned_lit by lia; exact ERR2].
    split; [exact ART2|]. split; [exact MI2|]. split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|].
    split; [exact ST2|].
    apply (munch_merge [(usp - 96, usp)] [(usp + -112, usp + -96); (0x64cea4, 0x64cea4 + 4)] _ m m1 m2 MU1 MU2).
    intros x Hx. unfold errno_cell in Hx. rewrite unsigned_lit in Hx by lia. cbn in Hx |- *. intuition lia.
Qed.

End XOpen.
