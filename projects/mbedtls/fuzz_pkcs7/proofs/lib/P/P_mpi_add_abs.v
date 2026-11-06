(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp P_mpi_copy
     P_mpi_add_abs_W P_mpi_add_abs_C P_mpi_add_abs_B.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_add_abs () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Spec.MpiJourney.XJ"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.P.P_mpi_add_abs_W.AA_FRAME"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.P.P_mpi_add_abs_B.opnd2"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Spec.Rep.limbs_val"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.P.P_mpi_add_abs_W.AA_VAL"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_mpi_add_abs_W.AA_POST"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"; "OSSVerify.KrLib.P.P_mpi_copy.mpi_copy_stmt"; "OSSVerify.KrLib.P.P_mpi_copy.P_MPI_COPY"; "OSSVerify.KrLib.Spec.MpiOpnd.mpi_add_abs_stmt'"; "OSSVerify.KrLib.P.P_mpi_addsub.P_MPI_ADD_ABS"; "OSSVerify.KrLib.P.P_mpi_addsub.mpi_add_abs_stmt"].


Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L5386298158.3000008S2zs1n1H". (* [comment removed for export] *)
Lemma lval_full : forall zs n, Z.of_nat (length zs) = n -> lval zs n = limbs_val zs.
Proof. intros zs n H. unfold lval. replace (Z.to_nat n) with (length zs) by lia. rewrite firstn_all. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section A.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (dA dB : mpd) (lo : Z) (MSF : Z) (j0 : list byte)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Hypothesis MSFE : MSF = P_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 176 - hl_stack L.
  Local Notation FRAME := (AA_FRAME ra s0 s1 s2 s3 s4 s5 j0).
  Local Notation POST := (AA_POST L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dA dB lo X sX nX pX xs0 padX ownX).
  Local Notation VAL := (AA_VAL dA dB).
  Hypothesis JCX : JC psegs L HI h LB m mo dX sp lo 64 FRAME.

  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ psegs L HI h LB m mo dX sp lo 64 FRAME []).
  Local Notation JBE dE := (JB psegs L LB m dX sp lo dE).
  Local Notation BJE dE := (BJ psegs sp dE).
  Local Notation OPND2 := (opnd2 L sp m LB lo X sX nX pX xs0 padX ownX).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1]; cbn [app] in HH1.
  Local Ltac wctx := try exact HFREE; try exact HCALLOC; try exact MSFE; try exact CA; try exact TP; try exact SPA; try exact SLO2; try exact JCX.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0@L13644265654.3  L21041645149.3  L21631969095.2  L29010566049.120L32761824045.1  L3521869107.2   L422967624.6    L42608597650.1  L52803347089.119L54425651213.3  L55661584084.121L59308583409.4  L59310648043.6  L60008970178.4  L780814420.4    00000900A00G01c01f01l02A02D03J03S04h05405I05U05aS2dE1r2HRS1k1r2HkS2zs1rS2ra2sp2s02s12s22s32s42s52j01X2sX2nX2pX3xs04padX4ownX1k2dE2zs3dXc1r2Hk4LENZ3EP02HR3SPB2X02EBS1rS1r2K1S2dA2dB2zs3dXc2HV3ZA'S1rS2ra2sp2s02s12s22s32s42s52j01X2sX2nX2pX3xs04padX4ownX1k2dE2zs3dXc1r2HkS2dE1r2HRS2ra2sp2s02s12s22s32s42s52j01X2sX2nX2pX3xs04padX4ownX1k2dE2zs3dXc1r2Hk4NZ102HR3SPB2X0S2dE1r2Hk2HRS2dE2zs1r4LENZ2HR3NTHS2dE1r2HR2K2S2dE1r2HR2K2". (* [comment removed for export] *)
  Lemma add_SCANLOOP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs ()) "Pk,$0.PdE,$1.Pzs,(2.(3.&40.))Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Praj,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Px19,(3.&40.)Px21,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Pr1,(3.&40.)Pr6,(3.&40.)Pr0,(3.&40.)Phc,(4.$5.VL,VHI,)PLBc,(2.$6.)Pmc,P,(3.&40.)(7.(3.&8.))Pmoc,$8.PdXc,$1.Pr,$9.P,(:.R1.(;.R1;.))P,(<.$5.VL,VHI,Vh,VLB,Vm,Vmo,(=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(>.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(?.$6.)R7.R6.R5.R4.R3.)P,(10.VL,Vsp,Vm,VLB,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,R1<.R7.R6.R4.)P,(11.$9.(12.R5.)+1.)P,(11.(2.(3.&40.))(13.R1>.)R1=.)P,(14.$5.R9.(15.R1?.)(16.R1>.))P,(11.$9.(;.(17.(3.&40.)R1?.))(18.R20.))P,(:.(18.R21.)+2710.)P,(19.=(15.R22.))P,(1:.(:.+1.R:.)(:.R:.(18.R23.)))P,(11.$9.(1;.R23.R;.)(1<.R23.))P,(11.$9.(1=.(1<.(13.R=.))(1<.R24.))(1>.VdA,VdB,))P,(11.(3.&40.)R15.(1?.&40.R=.))P,(11.(3.&40.)R15.(1?.&40.(1=.(20.+4.R>.)+4.)))P,(11.(3.&40.)R15.(1?.&40.(21.(15.R28.)+4.)))(22.$5.R12.(23.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VdA,VdB,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(24.(25.R24.(1?.&40.(21.(26.&40.Vsp,)+40.))Vgp,Vtp,R27.R26.R25.(1?.&40.VX,)R18.R16.(1?.&40.+4.)(1?.&40.(15.R29.))R23.R22.R21.R20.R1?.(1?.&40.(27.R29.))R1>.R17.R1=.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1<.R1;.R1:.R19.)VF,(1?.&40.+1?;18.)Vfc,(28.(3.&40.))R13.(29.$5.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until r; intros Hk J0 OP SG1 EZ EBY LENZ NZ10 EP0 HR ZA HV -> -> ->; [exfalso; clear - Hk HR; lia|].
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MI1.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep.
    destruct (nth_error zs (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENZ HR; lia].
    pose proof (u32ro_read psegs mc (md_p dE) zs (r - 1) w _ EBY NTH ltac:(clear - HR; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (limb32_w32_nth zs (Z.to_nat (r - 1)) w NTH) as LW. pose proof (w32_range w) as WR.
    zstep. if_cases K0; zify_cond K0; rewrite bv_unsigned_sx32 in K0; fold (w32 w) in K0.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K1; zify_cond K1; [| eapply add_retm16; [exact JCX| exact J0]].
      eapply add_J1; wctx; [exact J0| exact OP| clear - HR; lia| clear - K1; lia| exact SG1|]. rewrite EZ, ZA. exact HV.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_zero_iff _ WR)) in K0.
      assert (ZA' : lval zs (r - 1) = limbs_val zs).
      { rewrite <- ZA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ zs (r - 1)) by (clear - HR; lia). rewrite LW, K0. clear; lia. }
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (r - 1)); try eassumption; [clear - Hk; lia| clear - HR K2; lia| f_equal; clear; lia| f_equal; clear; lia| reflexivity].
      + (* [comment removed for export] *)
        assert (r = 1) as -> by (clear - K2 HR; lia). change (1 - 1) with 0 in ZA'. rewrite lval_0 in ZA'.
        eapply add_ret0; [exact JCX| exact J0| | exact SG1]. unfold mpd_val. rewrite SG1. clear - HV ZA'. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L20608685292.4  L23100341967.126L24349880210.3  L24691036956.4  L33085536913.2  L35839507041.2  L36683892759.1  L37070357933.2  L39172636981.0  L39399726678.142L39404153812.148L41117966897.149L44822572454.2  L49584625515.2  L51584070988.2  L5337555984.150 L53467490439.2  L59308579027.3  L59308628179.4  L61929812114.118L61934092688.125L64182719253.2  L6437276805.3   L65482851406.1  00000;00^00h01501<01D01H01P01Q02?03003Z03`03f03n04m05405@05Y06@06i07107;07>S1X2nE2pE1HS2ra2sp2s02s12s22s32s42s52j01X1p2xsS1X2Ea3SXBS2dA2dB2xs2HVS1n3NR1S2nE3NRES2nES2nE3NE1SS2ra2sp2s02s12s22s32s42s52j01X2Ea2nE2zs2xs3NRES2ra2sp2s02s12s22s32s42s52j01X2Ea2nE2pE2zs2xs3NRES2ra2sp2s02s12s22s32s42s52j01X2Ea2pE2zs2xsS1n2N1S1n2N1S2nE3NRES2ra2sp2s02s12s22s32s42s52j01X2Ea2pE2zs1p2xs3SXB2HB5Ha_st5Hl_stS1n3NR1S2nE2K02H01nS2nE2zs4LENE2K01n2xs4LEN1S2ra2sp2s02s12s22s32s42s52j01X1n2xs3NR1S2ra2sp2s02s12s22s32s42s52j01X1n1p2xs3NR1S2nE3NE1S2dA2dB2HVS1n". (* [comment removed for export] *)
  Lemma add_SCAN : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs ()) "PdE,$1.Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Praj,(3.&40.)Px9,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Px19,(3.&40.)Px20,(3.&40.)Px21,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)Phc,(4.$5.VL,VHI,)PLBc,(2.$6.)Pmc,P,(3.&40.)(7.(3.&8.))Pmoc,$8.PdXc,$1.P,(<.$5.VL,VHI,Vh,VLB,Vm,Vmo,(=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(>.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(?.$6.)R5.R4.R3.R2.R1.)P,(10.VL,Vsp,Vm,VLB,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,R1;.R5.R4.R2.)P,(11.$9.(1=.(1<.(13.R3.))(1<.(13.R1<.)))(1>.VdA,VdB,))(22.$5.R5.(23.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VdA,VdB,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(24.(25.R19.(1?.&40.(21.(26.&40.Vsp,)+40.))Vgp,Vtp,R1<.R1;.R1:.(1?.&40.VX,)R18.R17.R16.R15.R14.R13.R12.R11.R10.(1?.&40.(27.R1=.))R?.R>.R=.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(1?.&40.+1?:?4.)Vfc,(28.(3.&40.))R6.(29.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc; intros J0 OP HV.
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    destruct dXc as [X' sg n p xs pad' own]. pose proof J0 as JX; xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    clear HH1 SOK1 HPX1 FR1 ST1.
    destruct OP as [[DBJ B]|EQ].
    - (* [comment removed for export] *)
      destruct dE as [Ea sE nE pE zs padE ownE]. pose proof DBJ as [MB0 OB CRB CRBL SXB]. flat constr:(OB) 5%nat. intros OB1 OB2 OB3 OB4 OB5.
      flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B)) 8%nat. intros E0 E16 EAL LENE NRE ES OWNE0 OWNE1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ B))) 2%nat. intros (CE1 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CE1. unfold mpi_cells in CE1.
      pose proof (munch_refl [(X, X + 16)] mc) as MU; pose proof (wmono_refl psegs mc) as WM.
      zstep. rewrite zx16_small by (clear - NRE; lia). zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      match goal with MI2 : mem_inv psegs m2 |- _ =>
        pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ 1 J0 MU WM MI2 CX1 ltac:(left; reflexivity)) as J2 end.
      pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ B MU WM ltac:(cbn; clear - SXB; lia) ltac:(intros EN; cbn; pose proof (OB1 EN); clear - H; lia)) as B2.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B2.
      assert (B2' : BJE (mkMPD Ea sE nE pE zs padE ownE) LBc m2 (mkMPD X 1 n p xs padX own)) by (destruct B2 as [b1 b2 b3]; constructor; assumption).
      clear MU WM B J0 JX MX1 B2. rename B2' into B2. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl psegs m2) as WM.
      zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        eapply add_ret0; [exact JCX| exact J2| | reflexivity]. unfold mpd_val. cbn [md_sg md_limbs].
        destruct zs; [cbn [limbs_val] in HV; clear - HV; lia| exfalso; cbn [length] in LENE; clear - LENE K0; lia]. }
      assert (EN : ownE <> LNull) by (intros C; destruct (OWNE0 C); clear - K0 H0; lia).
      flat constr:((OWNE1 EN)) 6%nat. intros NE1 EP0 EPAL _ ESK _.
      flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B2)) 8%nat. intros _ _ _ _ _ _ _ OWNE2. flat constr:((OWNE2 EN)) 5%nat. intros _ _ _ EBY2 _.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in EBY2.
      zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
      eapply (add_SCANLOOP (Z.to_nat nE) (mkMPD Ea sE nE pE zs padE ownE) zs) with (r := nE); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        [clear - NE1; lia| exact J2| left; split; [exact DBJ| exact B2]| reflexivity| reflexivity| exact EBY2| exact LENE| clear - NRE; lia| exact EP0
        | clear - NE1; lia| apply lval_full; exact LENE| exact HV| reflexivity| f_equal; clear; lia| f_equal; clear; lia].
    - (* [comment removed for export] *)
      subst dE. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof (munch_refl [(X, X + 16)] mc) as MU; pose proof (wmono_refl psegs mc) as WM.
      zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      match goal with MI2 : mem_inv psegs m2 |- _ =>
        pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ 1 J0 MU WM MI2 CX1 ltac:(left; reflexivity)) as J2 end.
      clear MU WM J0 JX MX1. pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl psegs m2) as WM.
      zstep. if_cases K0; zify_cond K0.
      { eapply add_ret0; [exact JCX| exact J2| | reflexivity]. unfold mpd_val. cbn [md_sg md_limbs].
        destruct xs; [cbn [limbs_val] in HV |- *; clear - HV; lia| exfalso; cbn [length] in LEN1; clear - LEN1 K0; lia]. }
      assert (ON : own <> LNull) by (intros C; destruct (OWN0 C); clear - K0 H0; lia).
      flat constr:((OWN1 ON)) 8%nat. intros EO N1 XIN XPAL _ P0 PC PI. subst own.
      flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J2)) 12%nat. intros _ _ _ _ _ _ _ _ _ _ _ OWN2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OWN2.
      flat constr:((OWN2 ltac:(discriminate))) 6%nat. intros _ _ _ _ ARR2 _.
      zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
      eapply (add_SCANLOOP (Z.to_nat n) (mkMPD X 1 n p xs padX LHeap) xs) with (r := n); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        [clear - N1; lia| exact J2| right; reflexivity| reflexivity| reflexivity| apply u32arr_ro; exact ARR2| exact LEN1| clear - NR1; lia| exact P0
        | clear - N1; lia| apply lval_full; exact LEN1| exact HV| reflexivity| f_equal; clear; lia| f_equal; clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End A.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Spec.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr psegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  Local Ltac wctx8 a b c d e f := try exact a; try exact b; try exact c; try exact d; try exact e; try exact f.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01J0@L10307090133.2  L10317707088.1  L10357325628.156L10359409164.154L10753761994.13 L10754171340.9  L11478921847.2  L11734690100.6  L1175746480.1   L12283411672.131L13301871092.131L14106684376.130L17646078182.138L18366992939.6  L18521113596.3  L20662456646.1  L21716297469.2  L24417836163.7  L26727626090.4  L26981515745.4  L29010569984.202L3446086797.6   L34821254654.138L34821254654.139L38218545178.3  L38232090713.4  L38540402580.6  L38948636245.0  L38988038187.26 L39887139444.131L40228640085.0  L40230492638.4  L40254595421.7  L41288976216.131L42585448788.139L42585448788.140L43059482540.136L44866992728.131L44989272889.3  L45898055924.131L48325011009.3  L48429268312.131L49788159649.0  L50046069723.3  L51169429398.148L51169429398.155L5145216728.131 L51594954945.2  L51925114228.131L52101694457.9  L52391471400.4  L5259987632.149 L5259987632.156 L5262094874.148 L5262094874.155 L5262098304.154 L5287801372.12  L52985966244.8  L53297280983.2  L53482820749.8  L54310608745.3  L54391891673.10 L5670284798.138 L5670284798.139 L57355402471.2  L57933933556.131L58928056873.7  L58980375728.8  L59308628433.3  L59308628433.4  L59308632561.1  L59310648528.9  L59310730465.4  L59314955108.4  L59656785403.11 L59738961319.20 L61302938857.12 L63962036340.130L64081609434.1  L64979421756.7  L65294145718.7  L65486279189.8  L66958939429.8  L66963266466.5  L67966210416.1  L7274816372.131 L7282989406.4   L785248895.5    L8701789445.12  L8722184664.131 00000800901101i02R02j03003F03J03l04N05005R05a05j05n06606O06P06[06\07208H09m09n0:<0:R0:S0:T0;60;70;E0;[0<=0=Z0?F0@=0@_0@g0AI0AS0B50B60B@0C20Cj0DL0DT0E60EU0Ec0FX0GP0HB0I:0J20JT0Jn0K60KP0KY0L:0MP0O50O=0O_0P60PT0PZ0Pg0Pk0QD0QR0Qc0R>0R?0RM0Ro0S40SK0Sb0T<0TT0Tc0Tg0UI0UW0Ui0V90V[S1L4DIMGFS2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2Ba2zs2B03XBD3ABD3BBDS2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2Ba2zs2B03XBD3ABD3BBDS1L3HLS2sp2nB2pB2lo4SLO23ACL3BSP2n12p12R3S1L2nB2pB2n12p12R42I02I1S2nB1HS2nB2pB2zs4LENB3NB12BBS2spS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS1L2HI2sp1h1a1CS2sp2pA1HS2spS3xs02ysS1L3HLS2sp2Ba2lo4SLO23OB4FS2Aa2A01a1HFS1L3HLS2sp2lo4SLO23ACLS1L3HLS2ra2sp1X2pX3xs02Aa2pA2ys2Ba2pB2zs2lo4SLO23SPB2X03XBD3ABD3BBD3OB42HB5Ha_st5Hl_stS1L3HLS2sp2s01X2pX3xs02Aa2pA2ys2Ba2pB2zs2lo4SLO23SPB2X03XBD3ABD3BBD3OB42HB5Ha_st5Hl_st2s12s22s32s42s5FS1L2sp2lo4SLO2S2nB2pB2zs4LENB3NB12BBSFS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDSS2sp2Ba2lo3OB4S1L3HLS2sp2lo4SLO21d1HS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS1L3HLS2ra2sp1X2pX3xs02Aa2pA2ys2Ba2pB2zs2lo4SLO23SPA3SPB3XAL2X03XBD3ABD3BBD2XS2HB5Ha_st5Hl_stS1L3HLS2sp2s01X2pX3xs02Aa2pA2ys2Ba2pB2zs2lo4SLO23SPA3SPB3XAL2X03XBD3ABD3BBD2XS2HB5Ha_st5Hl_st2s12s22s32s42s5S1L3HLS2sp1X3xs02Aa2ys2Ba2zs2lo4SLO23SPB2X03XBD3ABD3BBDS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS1X2Ba1DS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS1X2Ba3KXBS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDSS1X2Aa3KAXS2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2A03XBD3ABD3BBDS2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2Ba2zs2A03XBD3ABD3BBDS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS3xs02zsS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS1L3HLS2sp2lo4SLO23ACL3DHI1a2HdS2ys2zs3xs12VXS2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2X03XBD3ABD3BBD2K2S2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2Ba2zs2X03XBD3ABD3BBDS2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2X03XBD3ABD3BBDS2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2Ba2zs2X03XBD3ABD3BBDS2sp1X3xs02Aa2sA2nA2pA2ys4padA4ownA2Ba2zs2X03XBD3ABD3BBDS1L3HLS2sp2lo4SLO23ACL3SPA3ACP3SPBS1L3HLS2sp2nX2pX2lo4SLO21HS2nB3NB1S1L3HLS2sp2nX2pX2lo4SLO21HS2sp2pB1HS1L2HI3HLS2sp1h2lo4SLO24HTOP1a2NOS1L3HLS2ra2sp1X2pX3xs02Aa2pA2ys2Ba2pB2zs2lo4SLO23SPB2X03XBD3ABD3BBD3OA42HB5Ha_st5Hl_stS1L3HLS2sp2s01X2pX3xs02Aa2pA2ys2Ba2pB2zs2lo4SLO23SPB2X03XBD3ABD3BBD3OA42HB5Ha_st5Hl_st2s12s22s32s42s5S2nB3NB1S2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS1L3HLS2sp1X2lo4SLO22XSS1L3HLS2sp2lo4SLO23ACL3ACP3SPBS1X2K2S1X2Ba3KXB2K2S2KRS2nX2pX2nB2pB1C2Q12Q23NX1S1X2Ba1E3KXB1CS1X2Aa1D1E2Ba3KAXS1L2HI3HLS2sp1h2lo4SLO21a1CFS1L2sp2lo4SLO2S2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS3xs0S1L3HLS2sp2lo4SLO21d2D1S1L3HLS2sp1X2lo4SLO22XSS1L3HLS2sp2nB2pB2lo4SLO21HS1X2nX2pX2Ba2nB2pB1C3KXBS2nX2pX2nB2pB1CS2spS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBDS2sp2Aa2lo3OA4S1L3HLS2sp2lo4SLO2S1L2HI2sp1h4HTOPS2sp1X3xs02Aa2ys2Ba2zs3XBD3ABD3BBD". (* [comment removed for export] *)
  Theorem P_mpi_add_abs_spec_o' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs ()) "PMSF,$9.P,(11.$9.R1.$2:.)P,(2;.$5.VL,VHI,$2<.R2.)(2=.$5.VL,VHI,$2>.R3.)")
(* [comment removed for export] *).
  Proof.
    intros MSF MSFE HCOPY. unfold mpi_add_abs_stmt', mpi_binop_stmtB', P_MPI_ADD_ABS. intros until lo.
    intros HH MX MA0 MB0 SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO2 ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    destruct dX as [X sX nX pX xs0 padX ownX]. destruct dA as [Aa sA nA pA ys padA ownA]. destruct dB as [Ba sB nB pB zs padB ownB].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX) 2%nat. intros FLt1 SGX. flat constr:(FLt1) 6%nat. flclear FLt1. intros CX0 XAL X0 LENX NRX OWNX. unfold mpi_cells in CX0. unfold MPI_MAX_LIMBS in NRX.
    flat constr:(MA0) 2%nat. intros FLt2 SGA. flat constr:(FLt2) 6%nat. flclear FLt2. intros CA0 _ A0 LENA NRA OWNA. flat constr:((opnd_view _ _ _ _ _ MB0)) 2%nat. intros FLt3 SGB. flat constr:(FLt3) 6%nat. flclear FLt3. intros CB0 _ B0 LENB NRB OWNB.
    pose proof (rw_cells_bound _ _ _ _ CX0) as XBD. pose proof (rw_cells_bound _ _ _ _ CA0) as ABD. pose proof (rw_cells_bound _ _ _ _ CB0) as BBD.
    unfold mpi_cells in ABD, BBD. cbn [cells_size csize Nat.add] in XBD, ABD, BBD.
    flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5. flat constr:(OB) 5%nat. intros OB1 OB2 OB3 OB4 OB5. flat constr:(XW) 3%nat. intros XCW XDW XP.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS.
    unfold mpd_sep in SXA, SXB, SAB. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SXA, SXB, SAB.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (conj HH I) as HHc. clear HH. pose proof (conj SOK I) as SOKc. clear SOK.
    do 8 zstep.
    replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by (clear; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    match type of FR with rw_cells _ _ _ (CB _ ?jk :: _) => set (j0 := jk) in FR end.
    change (rw_cells psegs m0 (bv_unsigned sp - 64) (AA_FRAME ra s0 s1 s2 s3 s4 s5 j0)) in FR.
    flat constr:(HHc) 2%nat. flclear HHc. intros HH _. flat constr:(SOKc) 2%nat. flclear SOKc. intros SOK _.
    assert (JCX : JC psegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (AA_FRAME ra s0 s1 s2 s3 s4 s5 j0)).
    { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption; try reflexivity; try (clear; lia). clear - SLO2. lia. }
    assert (J0 : XJ psegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (AA_FRAME ra s0 s1 s2 s3 s4 s5 j0) [] h LB m0 mo (mkMPD X sX nX pX xs0 padX ownX)).
    { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption; try reflexivity.
      - eapply (HEAP_munch psegs L HI) with (SP := lo); [exact HH| exact MU| exact WM| exact ACL|].
        intros a Ha NO. cbn in NO. left. clear - NO HTOP SLO2 HLS. lia.
      - apply mo_frame_refl.
      - eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Hd NW. cbn. split; [clear - Hd DHI ACL SLO2 HLS; lia| exact I].
      - eapply mpd_at_munch_any; [exact MX| exact MU| exact WM| cbn; split; [clear - XS SLO2 HLS; lia| exact I]|].
        cbn [md_own md_p md_n]. intros ON. cbn. split; [| exact I]. destruct (XLS ON); clear - H SLO2 HLS; lia.
      - apply mpd_out_refl. exact NST.
      - intros b Hb. left. exact Hb.
      - eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| clear - ACL SLO2 HLS; lia]. }
    assert (OPM : forall d, mpd_at psegs m LB d -> (md_addr d + 16 <= lo \/ bv_unsigned sp <= md_addr d) ->
                  (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ bv_unsigned sp <= md_p d) -> mpd_at psegs m0 LB d).
    { intros d Md D1 D2. eapply mpd_at_munch_any; [exact Md| exact MU| exact WM| cbn; split; [clear - D1 SLO2 HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (D2 ON); clear - H SLO2 HLS; lia| exact I]. }
    pose proof (OPM _ MA0 OA4 OA5) as MA. clear OPM.
    assert (MB : opnd_at psegs m0 LB (bv_unsigned sp) (mkMPD Ba sB nB pB zs padB ownB)).
    { eapply opnd_at_munch_any; [exact MB0| exact MU| exact WM| cbn; split; [clear - OB4 SLO2 HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (OB5 ON); clear - H SLO2 HLS; lia| exact I]. }
    pose proof J0 as JX. destruct JX as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1]. cbn [app md_addr md_p md_n md_own] in HH1, XP1.
    clear MU WM ST FR MI.
    rename m0 into mc.
    (* [comment removed for export] *)
    assert (IDA : Aa = X -> mkMPD Aa sA nA pA ys padA ownA = (mkMPD X sX nX pX xs0 padX ownX)) by (intros E; destruct SXA as [E'|D]; [symmetry; exact E'| exfalso; clear - D E; lia]).
    assert (IDB : Ba = X -> mkMPD Ba sB nB pB zs padB ownB = (mkMPD X sX nX pX xs0 padX ownX)) by (intros E; destruct SXB as [E'|D]; [symmetry; exact E'| exfalso; clear - D E; lia]).
    (* [comment removed for export] *)
    assert (JBA : Aa <> X -> JB psegs L LB m (mkMPD X sX nX pX xs0 padX ownX) sp lo (mkMPD Aa sA nA pA ys padA ownA) /\ BJ psegs sp (mkMPD Aa sA nA pA ys padA ownA) LB mc (mkMPD X sX nX pX xs0 padX ownX)).
    { intros NE. assert (D : X + 16 <= Aa \/ Aa + 16 <= X) by (destruct SXA as [E|D]; [exfalso; apply NE; injection E; auto| exact D]).
      split; [constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption; apply opnd_at_mpd; exact MA0|].
      constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; [apply opnd_at_mpd; exact MA| exact OA2|].
      intros EO AN. destruct OA3 as [C|[C|[C|C]]]; [exfalso; apply NE; injection C; auto| exfalso; exact (C EO)| exfalso; exact (AN C)| exact C]. }
    assert (JBB : Ba <> X -> JB psegs L LB m (mkMPD X sX nX pX xs0 padX ownX) sp lo (mkMPD Ba sB nB pB zs padB ownB) /\ BJ psegs sp (mkMPD Ba sB nB pB zs padB ownB) LB mc (mkMPD X sX nX pX xs0 padX ownX)).
    { intros NE. assert (D : X + 16 <= Ba \/ Ba + 16 <= X) by (destruct SXB as [E|D]; [exfalso; apply NE; injection E; auto| exact D]).
      split; [constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption|].
      constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; [exact MB| exact OB2|].
      intros EO BN. destruct OB3 as [C|[C|[C|C]]]; [exfalso; apply NE; injection C; auto| exfalso; exact (C EO)| exfalso; exact (BN C)| exact C]. }
    (* [comment removed for export] *)
    assert (VA : Z.abs (mpd_val (mkMPD Aa sA nA pA ys padA ownA)) = limbs_val ys) by (apply mpd_val_abs; exact SGA).
    unfold AA_VAL in *. unfold mpd_abs. cbn [md_limbs].
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep. if_cases KXB; zify_cond KXB; rewrite ?Z.mod_small in KXB by (clear - BBD; lia).
    - (* [comment removed for export] *)
      pose proof (IDB (eq_sym KXB)) as EB. injection EB as -> -> -> -> -> -> ->.
      zstep. if_cases KAX; zify_cond KAX; rewrite ?Z.mod_small in KAX by (clear - ABD; lia).
      + (* [comment removed for export] *)
        pose proof (IDA KAX) as EA. injection EA as -> -> -> -> -> -> ->.
        eapply (add_SCAN _ _ HFREE HCALLOC) with (dE := mkMPD X sX nX pX xs0 padX ownX); wctx8 MSFE CA TP SPA SLO2 JCX; [exact J0| right; reflexivity| unfold AA_VAL, mpd_abs; cbn [md_limbs]; clear; lia].
      + zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by (clear - BBD; lia); [| exfalso; clear - K2 KXB; lia].
        destruct (JBA ltac:(clear - KAX; lia)) as [DBJ B].
        eapply (add_SCAN _ _ HFREE HCALLOC) with (dE := mkMPD Aa sA nA pA ys padA ownA); wctx8 MSFE CA TP SPA SLO2 JCX; [exact J0| left; split; [exact DBJ| exact B]| unfold AA_VAL, mpd_abs; cbn [md_limbs]; clear; lia].
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KAX; zify_cond KAX; rewrite ?Z.mod_small in KAX by (clear - ABD; lia).
      + pose proof (IDA KAX) as EA. injection EA as -> -> -> -> -> -> ->.
        destruct (JBB ltac:(clear - KXB; lia)) as [DBJ B].
        eapply (add_SCAN _ _ HFREE HCALLOC) with (dE := mkMPD Ba sB nB pB zs padB ownB); wctx8 MSFE CA TP SPA SLO2 JCX; [exact J0| left; split; [exact DBJ| exact B]| unfold AA_VAL, mpd_abs; cbn [md_limbs]; clear; lia].
      + zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by (clear - BBD; lia); [exfalso; clear - K2 KXB; lia|].
        destruct (JBB ltac:(clear - KXB; lia)) as [DBJ B].
        assert (NEQA : (mkMPD X sX nX pX xs0 padX ownX) <> mkMPD Aa sA nA pA ys padA ownA) by (intros E; apply (f_equal md_addr) in E; cbn [md_addr] in E; clear - KAX E; lia).
        (* [comment removed for export] *)
        zstep. zstep.
        pose proof HCOPY as SPc. unfold mpi_copy_stmt, P_MPI_COPY in SPc.
        eapply aevtM_cut.
        { eapply SPc with (dX := mkMPD X sX nX pX xs0 padX ownX) (dY := mkMPD Aa sA nA pA ys padA ownA) (lo := lo) (h := h) (LB := LB); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
            rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO2 HLS ACL ACP; lia); try eassumption; try reflexivity.
          all: try (clear - SLO2 SPA SPB HLS ACL ACP HTOP; lia).
          all: try (rewrite <- MSFE; exact CA).
          all: try (split; [| split; [exact XDW| exact XP]]; intros a Ha; destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C; lia| right; left; exact C| right; right; exact C]).
          all: unfold copy_sep; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; split; [exact OA1|]; split; [exact OA2|];
                    split; [| split; [clear - OA4; lia| split; [intros AN; destruct (OA5 AN); [left; assumption| right; clear - H; lia]| intros; clear - A0 H; lia]]];
                    destruct OA3 as [C|C]; [left; exact C| right; exact C]. }
        cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
        flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m1 mo1 h1 LB1 dX1 r E PO. injection E as -> ->.
        rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO2 HLS ACL ACP; lia).
        flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 CR.
        replace (ret_pc (Z_to_bv 64 129776)) with (Z_to_bv 64 129776) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
        flat constr:(CR) 4%nat. flclear CR. intros CR1 CAD CPD CFR. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CAD, CPD, CFR.
        destruct dX1 as [X1 sg1 n1 p1 xs1 pad1 own1]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X1 pad1.
        flat constr:(OUT2) 5%nat. intros _ NS2 O3 O4 O5. cbn [md_addr md_own] in NS2.
        assert (NM1 : nX <= n1) by (destruct CR1 as [(_ & _ & Bn & _)|(_ & En & _)]; [exact Bn| rewrite En; apply Z.le_refl]).
        (* [comment removed for export] *)
        assert (J1 : XJ psegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (AA_FRAME ra s0 s1 s2 s3 s4 s5 j0) [] h1 LB1 m1 mo1 (mkMPD X sg1 n1 p1 xs1 padX own1)).
        { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption.
          - eapply heap_presx_rw_cells; [exact HPX2| exact (xj_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0)| apply client_range_stack; clear; lia|].
            unfold AA_FRAME, add_frame. cbn. split; [clear - XS SLO2 HLS; lia|]. destruct ownX; [exact I| |]; (split; [| exact I]); destruct (XLS ltac:(discriminate)); clear - H SLO2 HLS; lia.
          - eapply heap_presx_trans; [exact (xj_presx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0)|].
            eapply heap_presx_weaken; [exact HPX2| clear; lia| intros a Ho; exact Ho].
          - intros EO. eapply (new_limbs_apart_range psegs L HI h1 LB LB1 m1 m1 mo1 lo (mkMPD X sX nX pX xs0 padX ownX) (mkMPD X sg1 n1 p1 xs1 padX own1) X 16);
              cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try eassumption; try (clear; lia).
            + clear - DIMG; lia. + clear - DIMG; lia.
            + intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C HTOP SLO2 HLS ACL; lia| right; left; exact C| right; right; exact C]. }
        pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
        clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl psegs m1) as WM.
        zstep. if_cases KR; zify_cond KR.
        { (* [comment removed for export] *) destruct CR1 as [(-> & _)|[-> _]]; [exfalso; apply KR; reflexivity|].
          eapply add_ret; wctx8 MSFE CA TP SPA SLO2 JCX; [exact J1| right; reflexivity]. }
        destruct CR1 as [(-> & CV & _)|[-> _]]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
        (* [comment removed for export] *)
        assert (B1 : BJ psegs sp (mkMPD Ba sB nB pB zs padB ownB) LB1 m1 (mkMPD X sg1 n1 p1 xs1 padX own1)).
        { destruct B as [BA BS BL]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
          assert (D : X + 16 <= Ba \/ Ba + 16 <= X) by (destruct SXB as [E|D]; [exfalso; apply (f_equal md_addr) in E; cbn [md_addr] in E; clear - KXB E; lia| exact D]).
          constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
          - eapply opnd_at_heap_presx; [exact BA| exact HPX2| exact MI1| exact MI2| | | | | | clear; lia]; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
            + eapply client_range_sep; [exact CRB| intros b Hb; exact Hb| clear - OB4; lia].
            + intros EO. eapply client_range_sep; [exact (CRBL EO)| intros b Hb; exact Hb| destruct (OB5 ltac:(rewrite EO; discriminate)); [left; assumption| right; clear - H; lia]].
            + cbn. split; [clear - D; lia|]. destruct ownX; [exact I| | exfalso; exact (NST eq_refl)]. split; [| exact I]. destruct (OB2 eq_refl); [left|right]; assumption.
            + intros BN. cbn. split; [destruct (OB1 BN); [right|left]; assumption|].
              destruct ownX; [exact I| | exfalso; exact (NST eq_refl)]. split; [| exact I].
              destruct OB3 as [C|[C|[C|C]]]; [exfalso; apply (f_equal md_addr) in C; cbn [md_addr] in C; clear - KXB C; lia| exfalso; exact (C eq_refl)| exfalso; exact (BN C)| clear - C; lia].
            + intros b Hb. unfold mpd_blk in Hb. cbn [md_own md_p md_n] in Hb. destruct ownB; try (destruct Hb; fail). destruct Hb as [<-|[]].
              apply O4; [exact (proj1 (proj2 OWNB))|]. unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX; try (intros []; fail).
              intros [E|[]]. injection E as Q1 Q2.
              destruct OB3 as [C|[C|[C|C]]]; [apply (f_equal md_addr) in C; cbn [md_addr] in C; clear - KXB C; lia| exact (C eq_refl)| discriminate|].
              pose proof (proj1 OWNB) as NB1. pose proof (proj1 OWNX) as NX1. clear - C Q1 Q2 NB1 NX1. lia.
          - intros EO. eapply (new_limbs_apart_range psegs L HI h1 LB LB1 m1 m1 mo1 lo (mkMPD X sX nX pX xs0 padX ownX) (mkMPD X sg1 n1 p1 xs1 padX own1) Ba 16);
              cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try eassumption; try (clear; lia).
            + clear - DIMG; lia. + clear - DIMG; lia.
          - intros EO BN. destruct ownB; [exfalso; exact (BN eq_refl)| |].
            + destruct (new_limbs_apart_range psegs L HI h1 LB LB1 m1 m1 mo1 lo (mkMPD X sX nX pX xs0 padX ownX) (mkMPD X sg1 n1 p1 xs1 padX own1) pB (4 * nB) HH2 MX2 OUT2 CFR ACL
                          (proj1 DIMG) (proj2 DIMG) (CRBL eq_refl) ltac:(pose proof (proj1 OWNB); clear - H; lia)
                          ltac:(cbn [md_own md_p md_n]; intros EOX; destruct OB3 as [C|[C|[C|C]]]; [apply (f_equal md_addr) in C; cbn [md_addr] in C; clear - KXB C; lia| exfalso; exact (C EOX)| discriminate| clear - C; lia]) EO);
                cbn [md_p md_n] in H; [right| left]; exact H.
            + (* [comment removed for export] *)
              flat constr:(MX2) 2%nat. intros FLt4 _. flat constr:(FLt4) 6%nat. flclear FLt4. intros _ _ _ _ _ OW2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OW2. rewrite EO in OW2.
              flat constr:(OW2) 3%nat. flclear OW2. intros _ IN2 _. flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 _.
              flat constr:((proj1 (Forall_forall _ _) HBR2 _ IN2)) 5%nat. intros _ _ _ R3 R4. cbn in R3, R4.
              destruct OWNB as (NB1 & _ & BP0 & BBY & [BRO|[BSP _]]); [| clear - R3 BSP ACL SLO2 HLS NB1; cbn [md_p md_n] in BSP; lia].
              pose proof (u32ro_bound _ _ _ _ BBY) as BB.
              pose proof (ROIMG (pB + 0) (BRO 0 ltac:(clear - NB1; lia)) ltac:(clear - BB NB1 LENB; lia)) as I0.
              pose proof (ROIMG (pB + (4 * nB - 1)) (BRO (4 * nB - 1) ltac:(clear - NB1; lia)) ltac:(clear - BB NB1 LENB; lia)) as I1.
              clear - I0 I1 R4 NB1. lia. }
        eapply (add_SCAN _ _ HFREE HCALLOC) with (dE := mkMPD Ba sB nB pB zs padB ownB); wctx8 MSFE CA TP SPA SLO2 JCX; [exact J1| left; split; [exact DBJ| exact B1]|]. unfold AA_VAL, mpd_abs. cbn [md_limbs].
        assert (VX : Z.abs (mpd_val (mkMPD X sg1 n1 p1 xs1 padX own1)) = limbs_val xs1) by (apply mpd_val_abs; exact (proj2 MX2)).
        rewrite CV, VA in VX. clear - VX. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Theorem P_mpi_add_abs_spec_o : forall MSF, MSF = P_MEMSET_FUNC -> mpi_add_abs_stmt' psegs L HI P_MPI_ADD_ABS MSF.
  Proof.
    intros MSF ->. apply P_mpi_add_abs_spec_o'; [reflexivity|].
    apply P_mpi_copy_spec; try assumption. intros a H1 H2. exact (ROIMG a H2 H1).
  Qed.

  (* [comment removed for export] *)
  Theorem P_mpi_add_abs_spec' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs ()) "PMSF,$9.P,(11.$9.R1.$2:.)P,(2;.$5.VL,VHI,$2<.R2.)(2?.$5.VL,VHI,$2>.R3.)")
(* [comment removed for export] *).
  Proof. intros MSF E HC. apply mpi_binop_stmt_of_primeB. exact (P_mpi_add_abs_spec_o' MSF E HC). Qed.

  Theorem P_mpi_add_abs_spec : forall MSF, MSF = P_MEMSET_FUNC -> mpi_add_abs_stmt psegs L HI P_MPI_ADD_ABS MSF.
  Proof. intros MSF E. apply mpi_binop_stmt_of_primeB. exact (P_mpi_add_abs_spec_o MSF E). Qed.
End Spec.
