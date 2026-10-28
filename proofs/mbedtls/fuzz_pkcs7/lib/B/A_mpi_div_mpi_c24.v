(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_mul_mpi P_mpi_cmp P_mpi_copy P_mpi_shift_l P_mpi_grow P_mpi_lset P_mpi_div_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_zeroize_and_free A_platform_zeroize A_mpi_add_int A_mpi_client2 A_mpi_copy A_mpi_grow A_mpi_shift_l A_mpi_cmp_mpi A_mpi_core_bitlen A_mpi_shift_r A_mpi_add_sub A_mpi_add_sub_ng A_mpi_div_stmtA BX_mpi_cmp_abs_stmt A_mpi_div_mpi_P A_mpi_div_mpi_C A_mpi_div_mpi_S_c24 A_mpi_div_mpi_M_c24 A_mpi_div_mpi_F_c24 A_mpi_div_mpi_L_c24 A_mpi_lset A_mpi_lset_ng A_mpi_mul_int A_mpi_mul_int_stmtV A_mpi_mul_int_ng A_mpi_cmp_mpi_raw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_copy_c24 A_mpi_grow_c24 A_mpi_shift_l_c24 A_mpi_add_sub_sz_c24 A_mpi_add_sub_o_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_div_mpi_c24 () : Init.string Init.list := ["Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.div_mpi_rem_Rs"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.A_MPI_DIV_MPI_E"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_div_stmtA.mpi_div_mpi_stmtA"; "div_mpi_PHI"; "div_mpi_FR"].


(* [comment removed for export] *)
Definition div_mpi_PF : Z := grow_PHI MPI_MAX_LIMBS + 4 * AVOL_CALL.
Definition div_mpi_FF (d : Z) : Z := copy_FR d + 4 * fr_charge (d + 1).
Definition div_mpi_PHI (dA dB : mpd) : Z := A_mpi_div_mpi_M_c24.dvV1 dA dB (md_n dA * A_mpi_div_mpi_L_c24.dvVrnd + div_mpi_PF).
Definition div_mpi_FR (dA : mpd) (d : Z) : Z := A_mpi_div_mpi_M_c24.dvF1 d (md_n dA * A_mpi_div_mpi_L_c24.dvFrnd d + div_mpi_FF d).

Lemma div_mpi_FR_val : forall dA d, div_mpi_FR dA d = md_n dA * (20 * d + 98) + 9 * d + 64.
Proof.
  intros dA d. unfold div_mpi_FR, div_mpi_FF, A_mpi_div_mpi_M_c24.dvF1, A_mpi_div_mpi_M_c24.dvF2, A_mpi_div_mpi_M_c24.dvF3, A_mpi_div_mpi_M_c24.dvF4, A_mpi_div_mpi_M_c24.dvF5, A_mpi_div_mpi_M_c24.dvF6,
    A_mpi_div_mpi_L_c24.dvFrnd, mul_int_FR, add_sub_FR, A_mpi_add_abs_W.add_abs_FR, copy_FR, grow_FR, shift_l_FR, calls_FR, fr_charge. ring.
Qed.
Lemma div_mpi_PHI_val : forall dA dB, div_mpi_PHI dA dB = md_n dA * 1200136 + 16 * md_n dB + 80040.
Proof.
  intros dA dB. unfold div_mpi_PHI, div_mpi_PF, A_mpi_div_mpi_M_c24.dvV1, A_mpi_div_mpi_M_c24.dvV2, A_mpi_div_mpi_M_c24.dvV4, A_mpi_div_mpi_M_c24.dvV5, A_mpi_div_mpi_M_c24.dvV6,
    A_mpi_div_mpi_L_c24.dvVrnd, A_mpi_div_mpi_L_c24.dvcMUL, A_mpi_div_mpi_L_c24.dvcSHL, A_mpi_div_mpi_L_c24.dvcAS, A_mpi_div_mpi_L_c24.dvcCP, copy_PHI, grow_PHI, MPI_MAX_LIMBS, AVOL_CALL. ring.
Qed.

Section WalkD.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_DV.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2_DV.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (X A B lo : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - MPI_DIV_MPI_STACK_A - arl_need_rt R.
  Hypothesis SLOS : lo <= bv_unsigned sp - 352 - arl_need_smalloc R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_DV in UARG; unfold A_SMALLOC_2_DV in SM2;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Variables (dX dA dB : mpd) (d : Z) (es : list mpd) (PHIb FRb : Z).   (* [comment removed for export] *)
  Hypothesis XE : X = md_addr dX.
  Hypothesis AE : A = md_addr dA.
  Hypothesis BE : B = md_addr dB.
  Hypothesis HNDk : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis H0M : HM asegs R HIA h LB LF m.
  Hypothesis NST : md_own dX <> LStatic.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis W0AS : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX.
  Hypothesis W0BLK : md_own dX = LHeap -> In (md_p dX, 4 * md_n dX) LB /\ 1 <= md_n dX.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis D0 : 0 <= d.

  Local Notation POSTD := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                             (div_mpi_rem_Rs LB dX dA dB) PHIb FRb lo m mo0).


  (* [comment removed for export] *)
  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis COPYX : mpi_copy_stmtA_x_c asegs R HIA A_MPI_COPY.
  Hypothesis GROW : mpi_grow_stmtA_c asegs R HIA A_MPI_GROW.
  Hypothesis BITLEN : mpi_core_bitlen_stmtA asegs AL A_MPI_CORE_BITLEN.
  Hypothesis SHL : mpi_shift_l_stmtA_c asegs R HIA A_MPI_SHIFT_L.
  Hypothesis CMP : mpi_cmp_mpi_stmtA asegs AL A_MPI_CMP_MPI_E.
  Hypothesis CMPR : mpi_cmp_mpi_raw_stmtA asegs AL A_MPI_CMP_MPI_E.
  Hypothesis CABS : mpi_cmp_abs_stmtA asegs AL BX_MPI_CMP_ABS.
  Hypothesis SHR : mpi_shift_r_stmtA asegs R HIA A_MPI_SHIFT_R_E.
  Hypothesis LSETNG : mpi_lset_ng_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis MULNG : mpi_mul_int_ng_stmtA asegs R HIA A_MPI_MUL_INT.
  Hypothesis MULI : mpi_mul_int_stmtA_v asegs R HIA A_MPI_MUL_INT.
  Hypothesis ASNG : add_sub_mpi_ng_stmtA_o (-1) asegs R HIA A_ADD_SUB_MPI.
  Hypothesis ASM : add_sub_mpi_stmtA_o_c (-1) asegs R HIA A_ADD_SUB_MPI.
  Hypothesis ASP : add_sub_mpi_stmtA_o_c 1 asegs R HIA A_ADD_SUB_MPI.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_CP.
  (* [comment removed for export] *)
  Hypothesis PHIB : PHIb = div_mpi_PHI dA dB.
  Hypothesis FRB : FRb = div_mpi_FR dA d.
  Hypothesis BUD : havol asegs R HIA h + PHIb <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FRb <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_DIV_MPI <= C24MAX.     (* [comment removed for export] *)
  Hypothesis UWX : uw_obj R (md_addr dX) 16 d.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis IA2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_c24 ()) "P,(0.$1.(2.VdA,)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.VdA,))))(0.$:.(;.$<.(=.(>.(?.VdA,)R2.)))$10.)(0.$:.(11.(?.VdA,)(8.+4.(9.VdA,)))$10.)")
(* [comment removed for export] *).
  Hypothesis IB2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_c24 ()) "P,(0.$1.(2.VdB,)$3.)P,Pi,$4.P,(5.(6.=R1.)(7.R1.(8.+4.(9.VdB,))))(0.$:.(;.$<.(=.(>.(?.VdB,)R2.)))$10.)(0.$:.(11.(?.VdB,)(8.+4.(9.VdB,)))$10.)")
(* [comment removed for export] *).
  Hypothesis ESA : md_addr dA <> md_addr dX -> In dA es.
  Hypothesis ESB : In dB es.
  Hypothesis NA0 : 0 <= md_n dA.
  Hypothesis NB0 : 0 <= md_n dB.
  Hypothesis BR10 : 0 <= B + 10 < 2^64.
  Hypothesis ESF : ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_c24 ()) "(12.$13.Le,$13.(5.(14.(15.VR,)(16.$17.VLB,(18.VLF,))Vlo,(19.R1.)+10.)(5.P,(0.$1.(2.R1.)$1:.)(5.(1;.(1<.$4.$4.)(1=.$4.$4.(?.R2.)(8.+4.(9.R2.)))VLB,)(6.+1.(9.R2.)))(5.(1>.(6.(>.(19.R1.)+10.)Vlo,)(6.(1?.&40.Vsp,)(19.R1.)))(5.P,(0.$1.(2.VdX,)$1:.)(1>.(6.(>.(19.R2.)+10.)(?.VdX,))(6.(>.(?.VdX,)(8.+4.(9.VdX,)))(19.R2.)))(5.(1>.(20.(0.$1.(2.VdX,)$1:.))(1>.(0.$1.(2.R1.)$21.)(1>.(6.(>.(?.VdX,)(8.+4.(9.VdX,)))(?.R1.))(6.(>.(?.R1.)(8.+4.(9.R1.)))(?.VdX,)))))(5.(1>.(6.(>.(19.VdX,)+10.)(19.R1.))(6.(>.(19.R1.)+10.)(19.VdX,)))P,(20.(0.$1.(2.R1.)$21.))(1>.(6.(>.(19.VdX,)+10.)(?.R2.))(6.(>.(?.R2.)(8.+4.(9.R2.)))(19.VdX,)))))))))Ves,)")
(* [comment removed for export] *).
  Variables (slo : Z).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO2 : slo <= lo.
  Hypothesis MX0 : mpd_at asegs m LB dX.
  Hypothesis OXs0 : aobj asegs AL CS m (md_addr dX) 16.
  Hypothesis ESM : Forall (fun e => mpd_at asegs m LB e /\ aobj asegs AL CS m (md_addr e) 16) es.
  Hypothesis SSH0 : sshad asegs AL m slo (bv_unsigned sp).

  #[using="IMG UARG SM2 NS1 NEEDR LOS SLO SLOS TOP SPA TPV LFB es XE AE BE HNDk DIMG H0M NST XW W0AS W0BLK D0 PZ ZF COPYX GROW BITLEN SHL CMP CMPR CABS SHR LSETNG MULNG MULI ASNG ASM ASP CALLOC PHIB FRB BUD BUDF C24H UWX SXA OA OB IA2 IB2 ESA ESB NA0 NB0 BR10 ESF slo SLO1 SLO2 MX0 OXs0 ESM SSH0"] Lemma dv_MAINW : ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_c24 ()) "Pt0,(22.&40.)Pt1,(22.&40.)Pt2,(22.&40.)Pa4,(22.&40.)Pa5,(22.&40.)Pa6,(22.&40.)Pa7,(22.&40.)Pt3,(22.&40.)Pt4,(22.&40.)Pt5,(22.&40.)Pt6,(22.&40.)P,(23.$<.VR,VHIA,Vh,Vmo0,)P,(24.$<.Vm,Vlo,(1?.&40.Vsp,))P,(25.$<.Vm,)P,(26.$<.Vm,(27.VR,)(28.$<.VR,VHIA,Vh,)(1?.&40.Vs0,)(1?.&40.Vsp,)Vd,)(29.$<.(2:.$<.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(2;.VLB,VdX,VdA,VdB,)VPHIb,VFRb,Vlo,Vm,Vmo0,)(2<.(2=.(2>.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(2?.&40.=)(2?.&40.VX,)(2?.&40.VA,)(2?.&40.VB,)R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(2?.&40.$30.)Vfc,(31.(22.&40.))Vm,(32.$<.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 HK0 ST MI UW. rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m H0M) as HTOP.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0). { exact (A_mpi_div_mpi_P.pro_walk R HIA IMG UARG SM2 NS1 NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m X A B lo LOS SLO SLOS TOP SPA TPV LFB t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 H0M ST MI BR10). }
    cbv beta. intros ms1 S1. unfold A_mpi_div_mpi_P.S1P in S1.
    ddestruct S1 as (FB & sp1 & h1 & m1 & xra & y0 & y1 & y2 & ya1 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & w0 & w1 & w2 & j1 & j2 & jz & jx & jy & jt & jp & jq & sl & sl2
                    & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & J1C & J2C & JZC & XC & YC & TC & TPC & FSH & SAVE & SPILL & LSL & SP152 & SPILL2 & LSL2 & SThi & STlo & MI1 & PRES0).
    ddestruct (frame_factsA R HIA CS h1 LB LF m1 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
    set (gapn := Z.to_nat (bv_unsigned sp + -104 - (sp1 + 216))).
    assert (GAP : Z.of_nat gapn = bv_unsigned sp + -104 - (sp1 + 216)) by (subst gapn; clear - SP1; lia).
    intros mo1 [HK1 MF1]. apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
    pose proof (mpi_copy_stmtA_of_x _ _ _ _ COPYX) as COPY.
    assert (PF0 : 4 * AVOL_CALL <= div_mpi_PF) by (unfold div_mpi_PF, grow_PHI, MPI_MAX_LIMBS, AVOL_CALL; clear; lia).
    assert (FF0 : 4 * fr_charge (d + 1) <= div_mpi_FF d) by (unfold div_mpi_FF, copy_FR, calls_FR, fr_charge; clear - D0; lia).
    assert (VRN : 0 <= A_mpi_div_mpi_L_c24.dvVrnd) by (unfold A_mpi_div_mpi_L_c24.dvVrnd, A_mpi_div_mpi_L_c24.dvcMUL, A_mpi_div_mpi_L_c24.dvcSHL, A_mpi_div_mpi_L_c24.dvcAS, A_mpi_div_mpi_L_c24.dvcCP, grow_PHI, MPI_MAX_LIMBS, AVOL_CALL; clear; lia).
    assert (FRN : 0 <= A_mpi_div_mpi_L_c24.dvFrnd d) by (unfold A_mpi_div_mpi_L_c24.dvFrnd, mul_int_FR, add_sub_FR, A_mpi_add_abs_W.add_abs_FR, copy_FR, shift_l_FR, calls_FR, fr_charge; clear - D0; lia).
    set (PHIr := md_n dA * A_mpi_div_mpi_L_c24.dvVrnd + div_mpi_PF). set (FRr := md_n dA * A_mpi_div_mpi_L_c24.dvFrnd d + div_mpi_FF d).
    assert (PHIR0 : 4 * AVOL_CALL <= PHIr) by (subst PHIr; clear - PF0 VRN NA0; nia).
    assert (FRR0 : 4 * fr_charge (d + 1) <= FRr) by (subst FRr; clear - FF0 FRN NA0; nia).
    assert (BM_PHI : A_mpi_div_mpi_M_c24.dvV1 dA dB PHIr <= PHIb) by (rewrite PHIB; unfold div_mpi_PHI; subst PHIr; clear; lia).
    assert (BM_FR : A_mpi_div_mpi_M_c24.dvF1 d FRr <= FRb) by (rewrite FRB; unfold div_mpi_FR; subst FRr; clear; lia).
    assert (BE_PHI : copy_PHI dA + 4 * AVOL_CALL <= PHIb).
    { rewrite PHIB. unfold div_mpi_PHI, A_mpi_div_mpi_M_c24.dvV1, A_mpi_div_mpi_M_c24.dvV2, A_mpi_div_mpi_M_c24.dvV4, A_mpi_div_mpi_M_c24.dvV5, A_mpi_div_mpi_M_c24.dvV6. fold PHIr.
      unfold copy_PHI, grow_PHI in *. unfold AVOL_CALL in *. clear - PHIR0 NA0 NB0. lia. }
    assert (BE_FR : copy_FR d + 4 * fr_charge (d + 1) <= FRb).
    { rewrite FRB. unfold div_mpi_FR, A_mpi_div_mpi_M_c24.dvF1, A_mpi_div_mpi_M_c24.dvF2, A_mpi_div_mpi_M_c24.dvF3, A_mpi_div_mpi_M_c24.dvF4, A_mpi_div_mpi_M_c24.dvF5, A_mpi_div_mpi_M_c24.dvF6. fold FRr.
      assert (K : copy_FR d + 4 * fr_charge (d + 1) <= FRr) by (subst FRr; unfold div_mpi_FF; clear - FRN NA0; nia).
      unfold copy_FR, grow_FR, shift_l_FR, calls_FR, fr_charge in *. clear - K D0. lia. }
    assert (PHI0 : 0 <= PHIb) by (clear - BE_PHI NA0; unfold copy_PHI, grow_PHI, AVOL_CALL in BE_PHI; lia).
    assert (FR0 : 0 <= FRb) by (clear - BE_FR D0; unfold copy_FR, calls_FR, fr_charge in BE_FR; lia).
    assert (FIN_PHI : grow_PHI MPI_MAX_LIMBS + 4 * AVOL_CALL <= div_mpi_PF) by (unfold div_mpi_PF; clear; lia).
    assert (FIN_FR : copy_FR d + 4 * fr_charge (d + 1) <= div_mpi_FF d) by (unfold div_mpi_FF; clear; lia).
    eapply (A_mpi_div_mpi_S_c24.dv_S R HIA IMG NS1 NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo
              LOS SLO SLOS TOP SPA TPV LFB dX dA dB d es PHIb FRb XE AE BE HNDk DIMG H0M NST XW W0AS W0BLK D0 FB sp1 w0 w1 w2 gapn SP1 SP1M GAP
              F64 FRSH CFB AP ESF PZ ZF BUD BUDF C24H COPY UWX SXA OA IA2 IB2 ESA ESB BE_PHI BE_FR OB CMPR CABS slo SLO1 SLO2 MX0 OXs0 ESM SSH0 MI PHI0 FR0 h1 m1 j1 j2 jz jx jy jt jp jq sl sl2);
      try eassumption.
    eapply (A_mpi_div_mpi_M_c24.dv_M R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo
              LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb AE BE HNDk DIMG H0M XW W0AS D0 FB sp1 w0 w1 w2 gapn SP1 SP1M GAP F64 FRSH CFB AP
              ESF PZ ZF BUD BUDF C24H COPYX SXA IA2 IB2 ESA ESB PHIr FRr PHIR0 FRR0 BM_PHI BM_FR NA0 NB0 OA OB CALLOC LSETNG GROW BITLEN SHL CMP ASNG SHR).
    - exact (A_mpi_div_mpi_F_c24.dv_FIN_ok R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo
              LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb XE AE HNDk DIMG H0M NST XW W0AS D0 FB sp1 w0 w1 w2 gapn SP1 SP1M GAP F64 FRSH CFB AP
              ESF PZ ZF BUD BUDF C24H COPYX SHR CMPR UWX SXA IA2 ESA slo SLO1 SLO2 SSH0 PHIr FRr ltac:(subst PHIr; clear - FIN_PHI VRN NA0; nia) ltac:(subst FRr; clear - FIN_FR FRN NA0; nia)).
    - exact (A_mpi_div_mpi_L_c24.dv_LOOP_ok R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo
              LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb HNDk DIMG H0M XW W0AS D0 FB sp1 w0 w1 w2 gapn SP1 SP1M GAP F64 FRSH CFB AP
              ESF PZ ZF BUD BUDF C24H COPYX SHL LSETNG MULNG MULI CMPR ASM ASP slo SLO1 SLO2 SSH0 div_mpi_PF (div_mpi_FF d) PF0 FF0
              (A_mpi_div_mpi_F_c24.dv_FIN_ok R HIA IMG NEEDR h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo0 X A B lo
                 LOS SLO TOP TPV LFB dX dA dB d es PHIb FRb XE AE HNDk DIMG H0M NST XW W0AS D0 FB sp1 w0 w1 w2 gapn SP1 SP1M GAP F64 FRSH CFB AP
                 ESF PZ ZF BUD BUDF C24H COPYX SHR CMPR UWX SXA IA2 ESA slo SLO1 SLO2 SSH0 div_mpi_PF (div_mpi_FF d) FIN_PHI FIN_FR)).
  Qed.

  End Call.

  Hypothesis HNDk : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis PZ : platform_zeroize_stmtA asegs R HIA A_PLATFORM_ZEROIZE.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis COPYX : mpi_copy_stmtA_x_c asegs R HIA A_MPI_COPY.
  Hypothesis GROW : mpi_grow_stmtA_c asegs R HIA A_MPI_GROW.
  Hypothesis BITLEN : mpi_core_bitlen_stmtA asegs AL A_MPI_CORE_BITLEN.
  Hypothesis SHL : mpi_shift_l_stmtA_c asegs R HIA A_MPI_SHIFT_L.
  Hypothesis CMP : mpi_cmp_mpi_stmtA asegs AL A_MPI_CMP_MPI_E.
  Hypothesis CMPR : mpi_cmp_mpi_raw_stmtA asegs AL A_MPI_CMP_MPI_E.
  Hypothesis CABS : mpi_cmp_abs_stmtA asegs AL BX_MPI_CMP_ABS.
  Hypothesis SHR : mpi_shift_r_stmtA asegs R HIA A_MPI_SHIFT_R_E.
  Hypothesis LSETNG : mpi_lset_ng_stmtA asegs R HIA A_MPI_LSET.
  Hypothesis MULNG : mpi_mul_int_ng_stmtA asegs R HIA A_MPI_MUL_INT.
  Hypothesis MULI : mpi_mul_int_stmtA_v asegs R HIA A_MPI_MUL_INT.
  Hypothesis ASNG : add_sub_mpi_ng_stmtA_o (-1) asegs R HIA A_ADD_SUB_MPI.
  Hypothesis ASM : add_sub_mpi_stmtA_o_c (-1) asegs R HIA A_ADD_SUB_MPI.
  Hypothesis ASP : add_sub_mpi_stmtA_o_c 1 asegs R HIA A_ADD_SUB_MPI.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_CP.

  #[using="IMG UARG SM2 NS1 NEEDR HNDk DIMG PZ ZF COPYX GROW BITLEN SHL CMP CMPR CABS SHR LSETNG MULNG MULI ASNG ASM ASP CALLOC"] Theorem A_mpi_div_mpi_spec_s_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_div_mpi_c24 ()) "(33.$<.VR,VHIA,$30.L,$13.LdA,$13.LdB,$13.(34.R2.R1.)L,$13.LdA,$13.L,$13.Ld,$4.(35.R3.R1.))")
(* [comment removed for export] *).
  Proof.
    unfold mpi_div_mpi_stmtA. intros until d.
    intros HH HK LFB MX MA MB SXA SXB SAB NST NXB OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO SLOS SSH SLO1 SLO2 TOP SPA TPV MI RAE OXA OAA OBA IA2 IB2 BUD UW UWX BUDF C24H -> -> -> ->.
    cbv beta in *.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    pose proof MX as [(CX0 & _ & X0 & _ & NRX & OWNX) _]. pose proof MA as [(CA0 & _ & A0 & _ & NRA & _) _]. pose proof MB as [(CB0 & _ & B0 & _ & NRB & _) _].
    pose proof (rw_cells_bound _ _ _ _ CX0) as XB. pose proof (rw_cells_bound _ _ _ _ CA0) as AB. pose proof (rw_cells_bound _ _ _ _ CB0) as BB.
    unfold mpi_cells in XB, AB, BB. cbn [cells_size csize Nat.add] in XB, AB, BB.
    pose proof XW as (XCW & XP).
    pose proof (client_wrange_where_A asegs R HIA h LB LF m LB (bv_unsigned sp) (md_addr dX) 16 lo HH ltac:(intros b' Hb; exact Hb) XCW ltac:(clear; lia) LOS ltac:(clear - SLO NEEDR; lia)) as XS.
    set (es := (if Z.eq_dec (md_addr dA) (md_addr dX) then [] else [dA]) ++ [dB]).
    assert (ESP : forall e, In e es -> (e = dA /\ md_addr dA <> md_addr dX) \/ e = dB).
    { intros e He. subst es. apply in_app_iff in He. destruct He as [He|He].
      - destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE]; [destruct He| destruct He as [<-|[]]; left; split; [reflexivity| exact NE]].
      - destruct He as [<-|[]]. right. reflexivity. }
    assert (EFACT : forall e, mpd_at asegs m LB e -> mpd_sep dX e -> opnd_sep dX e lo (bv_unsigned sp) -> client_range L (LB ++ fdata LF) lo (md_addr e) 16 -> md_addr e <> md_addr dX ->
              client_range L (LB ++ fdata LF) lo (md_addr e) 16
              /\ (md_own e = LHeap -> In (md_p e, 4 * md_n e) LB /\ 1 <= md_n e)
              /\ (md_addr e + 16 <= lo \/ bv_unsigned sp <= md_addr e)
              /\ (md_own dX = LHeap -> md_addr e + 16 <= md_p dX \/ md_p dX + 4 * md_n dX <= md_addr e)
              /\ (md_own dX <> LHeap \/ md_own e = LNull \/ md_p dX + 4 * md_n dX <= md_p e \/ md_p e + 4 * md_n e <= md_p dX)
              /\ (md_addr dX + 16 <= md_addr e \/ md_addr e + 16 <= md_addr dX)
              /\ (md_own e <> LNull -> md_addr dX + 16 <= md_p e \/ md_p e + 4 * md_n e <= md_addr dX)).
    { intros e ME SE OE CRE NE. ddestruct OE as (O1 & O2 & O3 & O4 & O5).
      split; [exact CRE|]. split; [intros O; exact (A_mpi_client2.mpd_heap_in asegs _ _ _ ME O)|]. split; [exact O4|]. split; [exact O2|].
      split; [destruct O3 as [C|[C|[C|C]]]; [exfalso; apply NE; rewrite C; reflexivity| left; exact C| right; left; exact C| right; right; exact C]|].
      split; [destruct SE as [C|C]; [exfalso; apply NE; rewrite C; reflexivity| clear - C; lia]| exact O1]. }
    assert (NBX : md_addr dB <> md_addr dX) by (intros E; apply NXB; symmetry; exact E).
    eapply (dv_MAINW h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo (md_addr dX) (md_addr dA) (md_addr dB) lo) with (dX := dX) (dA := dA) (dB := dB) (d := d) (es := es) (slo := slo);
      first
      [ eassumption | reflexivity
      | (clear - NRA; unfold MPI_MAX_LIMBS in NRA; lia) | (clear - NRB; unfold MPI_MAX_LIMBS in NRB; lia)
      | (clear - B0 BB; lia)
      | exact (proj1 OXA)
      | (intros O; exact (A_mpi_client2.mpd_heap_in asegs _ _ _ MX O))
      | (intros NE; subst es; apply in_app_iff; left; destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|_]; [exfalso; exact (NE E)| left; reflexivity])
      | (subst es; apply in_app_iff; right; left; reflexivity)
      | (apply Forall_forall; intros e He; destruct (ESP e He) as [[-> NE]| ->]; [exact (EFACT dA MA SXA OA CRA NE)| exact (EFACT dB MB SXB OB CRB NBX)])
      | (apply Forall_forall; intros e He; destruct (ESP e He) as [[-> NE]| ->]; [split; [exact MA| exact (proj1 OAA)]| split; [exact MB| exact (proj1 OBA)]])
      | first [ dv_c24 R HIA HNDk C24H | match goal with |- ?g => idtac "THM-LEFT:" g end ] ].
  Qed.
End WalkD.


