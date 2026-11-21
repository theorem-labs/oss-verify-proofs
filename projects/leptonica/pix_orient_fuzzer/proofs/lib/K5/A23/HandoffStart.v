(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the m_channel_reader conjunct of PMfd and ASTA's frame frmW at the hand-off; the stack floor rt_sp0 - STACK_SPAN of Hstk and Husp, the span the start state guarantees writable; module paths qualified against the K5 twins; the recorded proofs replaced by plain proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_frmkit D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import SrzEqv HandoffKit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_HandoffStart () := "C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A238RT_iface4PMfdC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K52AG:HandoffKit9canon_cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs3CLXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs8argv_repC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6rt_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs9sigma0_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K52AS8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8rt_allowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG:HandoffKit2mHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface4ASTAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC69OSSVerify5KrLib2K53Lib5RzCPS5macctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS3HIDC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC69OSSVerify5KrLib2K52AS8AsanAcct8restrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface4frmWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface4ARTMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5RzCPS2HZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct4A_wfC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS8AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib2K52AS8AsanAcct=ranges_from_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K52AG:HandoffKit9hk_haltedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP6img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG:HandoffKit>hk_ranges_fromC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K56Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C69OSSVerify5KrLib2K52AS8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC69OSSVerify5KrLib2K53Lib2FP4frm0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6co_fdsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP4a_fdC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6fds_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS5co_fsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcct3mkHC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC69OSSVerify5KrLib2K52AG:HandoffKit5hk_HZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53A236D_defs5STARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8entry_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvK47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53A236Layout6a_mainC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A236D_defs4fds0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs7MAIN_RAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236D_defs4TP_AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23<HandoffStart5hk_fxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec5Stdio;stdout_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface9STACK_WINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI79OSSVerify5KrLib2K52AS8AsanPlan2AP3afd00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS8AsanPlan2AP3afd01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AG:HandoffKit=hole_of_canonC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib2K52AS=AsanPlanSound>asanreflect_fxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23<HandoffStart@start_of_handoffC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance hk_fx : K5.AS.PropExec.FPState := K5.AS.PropExec.fx0.   (* [comment removed for export] *)

Section Start.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (fs : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok asegs A nx0 LIMIT SINV argH fs E ch R FULL model.

(* [comment removed for export] *)
Variables (RT : rt_sig) (OUT_rep : stdout_st -> mem -> Prop) (ERR_rep XENV LIB : mem -> Prop) (argvb : list (list byte)).
(* [comment removed for export] *)
Variable (Σ : rts RT).
Hypothesis Hallow : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb (rt_allow RT Σ) p = true.
Hypothesis Hawf : A_wf (rt_allow RT Σ).
Hypothesis Hminv : MInv (rt_allow RT Σ) model.
Hypothesis Hartm : ARTM RT Σ model.
(* [comment removed for export] *)
Hypothesis Hfd : a_fd ch = AP.FdStd.

(* [comment removed for export] *)
#[local] Notation m := (mH FULL model (rt_allow RT Σ)).

(* [comment removed for export] *)
Variables (usp ap : Z).
Hypothesis R1 : getr R (Z_to_bv 5 1) = Z_to_bv 64 MAIN_RA.
Hypothesis R2 : getr R (Z_to_bv 5 2) = Z_to_bv 64 usp.
Hypothesis R4 : getr R (Z_to_bv 5 4) = Z_to_bv 64 TP_A.
Hypothesis R10 : getr R (Z_to_bv 5 10) = Z_to_bv 64 (Z.of_nat (length argvb)).
Hypothesis R11 : getr R (Z_to_bv 5 11) = Z_to_bv 64 ap.

(* [comment removed for export] *)
Hypothesis Hart : ART RT Σ m.
Hypothesis Hinv : mem_inv asegs m.
Hypothesis Hclx : CLX OUT_rep ERR_rep XENV LIB stdout_init m.
Hypothesis Hargv : argv_rep argvb m ap.
Hypothesis Hstk : stk asegs m (rt_sp0 RT Σ - STACK_SPAN) usp.
Hypothesis Hsig : sigma0_ok RT Σ usp.
Hypothesis Husp : usp mod 16 = 0 /\ usp < ap /\ rt_sp0 RT Σ - STACK_SPAN + 0x100000 <= usp.

Theorem start_of_handoff : START RT OUT_rep ERR_rep XENV LIB argvb fs (canon_cfg asegs R a_main FULL model).
Proof.
  unfold START.
  exists Σ, usp, ap,
    (getr R (Z_to_bv 5 3)), (getr R (Z_to_bv 5 5)), (getr R (Z_to_bv 5 6)), (getr R (Z_to_bv 5 7)), (getr R (Z_to_bv 5 8)),
    (getr R (Z_to_bv 5 9)), (getr R (Z_to_bv 5 12)), (getr R (Z_to_bv 5 13)), (getr R (Z_to_bv 5 14)), (getr R (Z_to_bv 5 15)),
    (getr R (Z_to_bv 5 16)), (getr R (Z_to_bv 5 17)), (getr R (Z_to_bv 5 18)), (getr R (Z_to_bv 5 19)), (getr R (Z_to_bv 5 20)),
    (getr R (Z_to_bv 5 21)), (getr R (Z_to_bv 5 22)), (getr R (Z_to_bv 5 23)), (getr R (Z_to_bv 5 24)), (getr R (Z_to_bv 5 25)),
    (getr R (Z_to_bv 5 26)), (getr R (Z_to_bv 5 27)), (getr R (Z_to_bv 5 28)), (getr R (Z_to_bv 5 29)), (getr R (Z_to_bv 5 30)),
    (getr R (Z_to_bv 5 31)), fp_regs, fp_csr, m.
  split; [|split; [exact Hart|split; [exact Hinv|split; [exact Hclx|split; [exact Hargv|split; [exact Hstk|split; [exact Hsig|exact Husp]]]]]]].
  unfold ASTA, AST. split; [|split; [|split]].
  - (* [comment removed for export] *) unfold macct. split; [exact Hawf|]. split; [exact Hminv|].
    split; [exact (hk_halted asegs A nx0 LIMIT SINV argH fs E ch R FULL model HC)|].
    split; [rewrite <- Hsegtop; exact (hk_ranges_from asegs A nx0 LIMIT SINV argH fs E ch R FULL model HC)|].
    unfold SEGTOP_A. lia.
  - (* [comment removed for export] *)
    unfold canon_cfg, canon_regs, entry_st, restrict, mkst, MS, mH. cbn [cfg_ms cfg_model]. unfold frmW. split.
    + rewrite R1, R2, R4, R10, R11. reflexivity.
    + cbn [ms_fcsr]. unfold FP.frm0. reflexivity.
  - (* [comment removed for export] *) split; [exact Hartm|]. unfold PMfd. split.
    { pose proof (APS.co_fds _ _ _ _ _ _ _ _ _ _ _ _ HC) as F. rewrite Hfd in F. exact F. }
    split; [exact (APS.co_fs _ _ _ _ _ _ _ _ _ _ _ _ HC)| exact (APS.co_rdr _ _ _ _ _ _ _ _ _ _ _ _ HC)].
  - (* [comment removed for export] *) intros a Ha Hna. cbn [cfg_ms cfg_model canon_cfg mkst ms_mem] in *.
    exact (hk_HZ asegs A nx0 LIMIT SINV argH fs HULL_ok E ch R FULL model HC (rt_allow RT Σ) Hallow a Ha Hna).
Qed.

(* [comment removed for export] *)
Theorem hole_of_start : forall T,
  (forall c, START RT OUT_rep ERR_rep XENV LIB argvb fs c -> realizes asegs c T) ->
  srealizes asegs (APS.cfg_of asegs R a_main FULL model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_HandoffStart ()) ["Start"] "h05Hmainh11Th21cp;8p;3p;6p;5g016gj85Tg01S=j34Tg007@j60Tg01T;j81Tg01U>j53Tg01VAj32Tg01W?g01X7p,2RTp,7OUT_repp,7ERR_repp,4XENVp,3LIBp,5argvbp,2fsf0R0G5g01G:R1f1R2f234[]2g01XlR3P1p,1RR4g01?3R5p,4FULLR6p,5modelR7P2P0P3P1P4P5P6P7E0g01Z3O2G1P1P4P5P6P7D3=212eW0W1o"). Qed.

End Start.
