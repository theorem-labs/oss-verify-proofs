(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney MpiJourney2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp
     P_mpi_copy P_mpi_core_mla P_mpi_add_abs_W P_mpi_add_abs_C P_mpi_add_abs P_mpi_mul_int_W.
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
Ltac2 gd_tbl_P_mpi_mul_int () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.P.PImg.psegs"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Exec.evt"; "copy_self_post"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.P_MPI_COPY"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiJourney.XJ"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.MI_FRAME"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "OSSVerify.KrLib.Spec.Rep.limbs_val"; "Stdlib.ZArith.BinInt.Z.max"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.MI_POST"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.MpiJourney.JB"; "OSSVerify.KrLib.Spec.MpiJourney.BJ"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"; "OSSVerify.KrLib.P.P_mpi_copy.mpi_copy_stmt"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.mpi_mul_int_stmt"; "OSSVerify.KrLib.P.P_mpi_mul_int_W.P_MPI_MUL_INT"].


(* [comment removed for export] *)
Definition copy_self_post (segs : list Segment) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Lms',$0.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R2.(6.(7.O22.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.(8.&40.=)O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(9.O22.)O3.(:.(2.&40.))R1.(;.O23.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.(11.(12.&40.O21.)+30.)(12.&40.O21.))(13.(>.$?.$?.)))O1.R1.)(4.(14.O23.O1.R1.)(4.(15.O23.R1.)(16.O23.R1.O2.(12.&40.O21.)))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11741095640.45L19354909044.46L25382082548.46L26924648792.46L29520273615.46L31378308326.42L31392867444.46L37414286068.46L42594554710.45L43059690761.40L43442376564.45L43654564952.46L57030252976.1 L59499841752.46L6372250817.1  L7510805464.46 00000400800<00@00K00O00S00W00[00f00j00n01201601:01>S2spS2spS2spS2spS2sp2lo3SLOS2spS2spS2spS2spS2sp2lo3SLOS2spS2spS2spS2spS2spS2sp". (* [comment removed for export] *)
Lemma P_copy_self : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$?.P,(15.$18.R2.)P,(16.$18.R3.R2.(12.&40.R23.))P,(19.R3.(11.(12.&40.R24.)+30.))P,(5.$?.(1:.(12.&40.R25.)+10.)=)P,(5.(2.&40.)R1>.R1=.)(1;.$18.(1<.$18.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R6.R7.)(6.(7.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(8.&40.$1=.)R8.(:.(2.&40.))R7.(;.$18.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros MI ST SLO SPA ->. unfold P_MPI_COPY.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. flat constr:(ST) 3%nat. intros L0 _ _.
  carve_frame 48%nat ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl psegs mx) as WM end.
  do 6 zstep. replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by (clear; lia).
  zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
  do 7 zstep. release_frame FR ST (bv_unsigned sp).
  replace (Z_to_bv 64 (bv_unsigned sp - 48 + 48)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
  zstep. apply evt_done. unfold copy_self_post. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L13312809852.8L19524031615.8L23672843407.8L33371808075.8L41415985178.8L42470663613.8L44015172602.8L54240452684.800000800D00J00R00U00X00[00cS1v1n2HvS1n2dl2Hn2HdS1n2HnS1b1n2HbS1nS1nS1nS1v1n2Hv". (* [comment removed for export] *)
Lemma mul_fits : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pv,$?.Pb,$?.Pn,$?.Pdl,$?.P,(4.(19.=R4.)(1>.R4.(1?.+2.(20.+20.R2.))))P,(4.(19.=R4.)(1>.R4.(1?.+2.+20.)))P,(19.=R4.)P,(19.(21.R5.+1.)R4.)(1>.(20.R8.R7.)(1?.+2.(20.+20.R5.)))")
(* [comment removed for export] *).
Proof.
  intros v b n dl Hv Hb Hn Hd.
  apply (Z.lt_le_trans _ (2 ^ (32 * n) * 2 ^ 32)).
  - apply (Z.le_lt_trans _ (v * 2 ^ 32)); [apply Z.mul_le_mono_nonneg_l; lia|]. apply Z.mul_lt_mono_pos_r; lia.
  - rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section Body.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HCOPY : forall MSF, MSF = P_MEMSET_FUNC -> mpi_copy_stmt psegs L HI P_MPI_COPY MSF.
  Hypothesis HMLA : mpi_core_mla_vstmt psegs P_MPI_CORE_MLA.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (b lo : Z) (MSF : Z) (j0 : list byte)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own)
            (Aa sA nA pA : Z) (ys : list word) (padA : word) (ownA : limb_own).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Local Notation dA := (mkMPD Aa sA nA pA ys padA ownA).
  Hypothesis MSFE : MSF = P_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis BB : 0 <= b < 2^32.
  Variable wb : word.
  Hypothesis WB1 : bv_unsigned wb mod 2^32 = b.
  Hypothesis WB0 : bv_unsigned wb = 0 <-> b = 0.
  Local Notation FRAME := (MI_FRAME ra s0 s1 s2 s3 s4 s5 j0).
  Local Notation POST := (MI_POST L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dA b lo X sX nX pX xs0 padX ownX).
  Hypothesis JCX : JC psegs L HI h LB m mo dX sp lo 64 FRAME.
  Hypothesis MAG : mpd_at psegs m LB dA.       (* [comment removed for export] *)
  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ psegs L HI h LB m mo dX sp lo 64 FRAME []).
  Local Notation JBE dE := (JB psegs L LB m dX sp lo dE).
  Local Notation BJE dE := (BJ psegs sp dE).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]; cbn [app] in HH1.
  Local Ltac wctx := try exact MSFE; try exact CA; try exact TP; try exact SPA; try exact SLO2; try exact BB; try exact WB1; try exact WB0; try exact JCX.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00O0@L1123023902.1   L23100341967.163L23423450574.5  L2424855267.2   L27300803429.3  L30618271325.4  L31076078142.4  L32690113826.5  L34454857851.9  L39302427597.8  L39550497581.3  L41867728390.5  L42358704340.10 L47444575930.2  L57123003684.4  L57702397653.3  L57799308895.3  L58980668962.8  L59314923118.9  L60285755058.9  L60435619211.5  L62781514286.3  L64934269637.2  L66151427842.16 L66223264509.7  L6644069548.3   L67702776369.163L7978486879.3   L8060680993.0   L8355067807.3   L9949055884.9   00000401601E01K01N01[01`02202R02a02j03<03]03c04104:04B04_05<05Z05l06706@06c07707@08B08O08P08]092S2wbS2ra2sp2s02s12s22s32s42s51b2j01X2nX2nA2wb3WB01n3pXc2xs1S2ss2Sa3SaBS1L1S2ss3ACV2SBS1n2N1S1bS1n2ss2N13NLES3nXcS1L2sp2lo4SLO23HLSS1L2sp2lo3nXc3pXc3HLS3ACL3SLO2PCS1L4IMGC1S2ss1HS1b2sg2xsS1L3nXc3pXc3ACV2PCS1L2sp2lo1X4SLO23nXc3pXc3HLS2XS1HS1b2xsS1n3nXc2N13NX1S1b2BB2B1S2sp1S1CS1L2sp2lo3HLS3ACL3SLO3SPB3ACPS1b3nXc2xs3xs'1c3LV23FIT2LR1KS1L2sp2lo4SLO23nXc3pXc3HLS1a1OS1n2ss2N13NLE4SL10S1n3nXc3NX1S3nXc3NR1S3pXc2r04XPAL1q1r1H2H02q02H42sp3SPAS1n1S2ss2N13NLE2S01KS1c2CB2NES2ra2sp2s02s12s22s32s42s51b2j01X2nX2nA2wb3WB01n3pXc2xs1S2ss2Sa3SaBS3nXc2xs4LEN1SS3nXc2xs4LEN1S1L2lo3nXc3pXc3ACL2PC". (* [comment removed for export] *)
  Lemma mi_MLA : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pn,$?.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px19,(2.&40.)Px21,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Phc,(22.$18.VL,VHI,)PLBc,(23.$24.)Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$25.Psg,$?.PnXc,$?.PpXc,$?.Pxs,(23.(2.&40.))PS,$?.Pss,(23.(2.&40.))PSa,$?.PsgS,$?.PnS,$?.PpadS,(2.&40.)P,(26.$18.VL,VHI,Vh,VLB,Vm,Vmo,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(28.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(13.$24.)R>.R=.R<.R;.(27.VX,R:.R9.R8.R7.VpadX,$29.))P,(2:.$18.R=.R5.(=.$2;.(2<.(8.&40.R7.))(=.$2;.(2=.(8.&40.R4.))(=.$2;.(2=.(8.&40.R3.))(=.$2;.(2>.R2.)(13.$2;.))))))P,(2?.$18.R>.R8.(30.R7.))P,(19.+1.R24.)P,(19.R25.(31.(32.(2.&40.)R9.)))P,(19.(31.(32.(2.&40.)R:.))+2710.)P,(19.(21.R27.+1.)R?.)P,(33.(4.(5.$?.R=.R?.)(5.(23.(2.&40.))R<.R>.))(33.(19.(21.R=.(20.+4.(31.(32.(2.&40.)R<.))))R?.)(19.(21.R?.(20.+4.R10.))R=.)))P,(5.$?.(1:.R>.+4.)=)P,(1>.=R?.)P,(33.(19.(21.R10.(20.+4.(31.(32.(2.&40.)R?.))))(34.VL,))Pi,$?.P,(4.(19.=R1.)(1>.R1.(20.+4.(31.(32.(2.&40.)R10.)))))(5.$35.(36.$18.(37.(21.R12.R2.)))$38.))P,(33.(19.(21.R11.(20.+4.(31.(32.(2.&40.)R10.))))Vlo,)(19.(12.&40.Vsp,)R11.))P,(5.$?.(39.R11.R2=.)(3:.R13.))P,(1>.(3:.R14.)(1?.+2.(20.+20.R2>.)))P,(19.+1.Vb,)P,(19.R18.(3;.VnX,(21.VnA,+1.)))P,(5.$?.(20.(20.R1:.(3:.R17.))Vb,)(20.(3<.(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))Vb,))(3=.$18.R1<.(3>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)Vb,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(6.(7.R2>.(8.&40.(11.(12.&40.Vsp,)+40.))Vgp,Vtp,R31.R30.R2?.(8.&40.VX,)(8.&40.R32.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.(8.&40.R15.)R25.Vwb,R24.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R23.R22.R21.R20.)VF,(8.&40.+1?4:4.)Vfc,(:.(2.&40.))R1=.(;.$18.)))")
(* [comment removed for export] *).
  Proof.
    intros until padS. intros J CS SBY N1 NLE SL10 NX1 SEP S4 S0 SHI SLS HV VB B1 NXB VAL. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ _ XIN XPAL ARR1 P0 PC PI.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof (rw_cells_bound _ _ _ _ CS) as SaB. cbn [cells_size csize Nat.add] in SaB.
    assert (SB : S + 4 * Z.of_nat (length ss) <= alloc_ceiling).
    { destruct SHI as [C|RO]; [exact C|]. pose proof (RO (4 * Z.of_nat (length ss) - 1) ltac:(clear - NLE N1; lia)) as R1.
      pose proof (bytes_at_bound _ _ _ _ SBY) as K. rewrite u32s_length in K.
      pose proof (ROIMG _ R1 ltac:(clear - K S0 NLE N1; lia)). clear - H IMGC NLE N1. lia. }
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. rewrite zx16_small by (clear - NR1; lia). zstep. zstep. zstep. zstep.
    assert (HB4 : b - 1 = bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned wb + -1))) mod 2 ^ 32).
    { change (b - 1 = w32 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned wb + -1)))). rewrite Z_to_bv64_swrap32_mod32.
      replace (bv_unsigned wb + -1) with (bv_unsigned wb - 1) by (clear; lia). rewrite <- Zminus_mod_idemp_l. rewrite WB1. rewrite Z.mod_small; clear - BB B1; lia. }
    unfold mpi_core_mla_vstmt in HMLA.
    eapply aevtM_cut_evt; [exact MK1| eapply HMLA with (ds := xs) (ss := ss) (dl := nXc) (sl := n) (D := pXc) (S := S) (lo := lo) (b := b - 1);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); unfold MPI_CORE_MLA_STACK; try reflexivity; try eassumption|].
    - clear - N1 NLE SL10; lia.
    - clear - LEN1; lia.
    - clear - NX1; lia.
    - rewrite LEN1. exact SEP.
    - clear - XPAL. Z.div_mod_to_equations. lia.
    - right. exact S0.
    - rewrite LEN1. clear - PC ACV. lia.
    - clear - SB ACV. lia.
    - clear - SLO2 HLS; lia.
    - clear - SPA. Z.div_mod_to_equations. lia.
    - left. rewrite LEN1. clear - PC ACL SLO HLS. lia.
    - destruct SLS as [C|C]; [left; exact C| right; clear - C; lia].
    - cbv beta. intros ms' PO. unfold mpi_core_mla_vpost in PO.
      flat constr:(PO) 28%nat. flclear PO. intros z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 m2 xs' c -> MU2 WM2 MI2 ARR2 LEN2 SK2 CB LV2 ST2.
      unfold MPI_CORE_MLA_STACK in MU2. rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in MU2, ST2 by (clear - SPB SLO HLS ACL ACP; lia).
      replace (ret_pc (Z_to_bv 64 128188)) with (Z_to_bv 64 128188) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      (* [comment removed for export] *)
      rewrite HV in LV2. unfold lval in LV2 at 2. rewrite firstn_all2 in LV2 by (clear - LEN1; lia).
      replace (limbs_val xs + limbs_val xs * (b - 1)) with (limbs_val xs * b) in LV2 by (clear; lia).
      pose proof (mul_fits (limbs_val xs) b n nXc (conj (limbs_val_nonneg xs) VB) BB ltac:(clear - N1; lia) NX1) as FIT.
      pose proof (lval_range xs' nXc ltac:(clear - NX1 N1; lia)) as LR.
      assert (C0 : c = 0).
      { destruct (Z.eq_dec c 0) as [E|NE]; [exact E| exfalso].
        assert (K : 2 ^ (32 * nXc) * 1 <= 2 ^ (32 * nXc) * c) by (apply Z.mul_le_mono_nonneg_l; clear - CB NE; lia). clear - K LV2 FIT LR. lia. }
      subst c. rewrite Z.mul_0_r, Z.add_0_r in LV2. unfold lval in LV2. rewrite firstn_all2 in LV2 by (rewrite LEN2; clear - LEN1; lia).
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU2 WM2 MI2 ST2
                    ltac:(intros a NO; destruct (outside_dec [(pXc, pXc + 4 * nXc); (bv_unsigned sp - 64 - 48, bv_unsigned sp - 64)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O SLO2 HLS; lia])
                    ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H XS SLO2 HLS; lia) ARR2 LEN2) as J2.
      pose proof (munch_refl ([] : list ivl) m2) as MU'. pose proof (wmono_refl psegs m2) as WM'.
      zstep. zstep. eapply mi_ret; wctx; [exact J2|]. left. split; [reflexivity|]. cbn [md_n]. split; [| exact NXB].
      unfold mpd_val at 1. cbn [md_sg md_limbs]. rewrite LV2. rewrite <- VAL. clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L11803631744.5  L11913056983.11 L158429236.6    L18366992939.6  L19268950546.5  L22166426854.2  L2424859202.3   L26983617546.4  L28689927877.5  L29010569984.196L29971683454.3  L30818096100.5  L32321277570.8  L32690113826.5  L40614023308.7  L41822158169.3  L47343275948.2  L48456612600.6  L50545063073.0  L58980668962.8  L59308546259.8  L59308579027.4  L59308632561.1  L60285755058.9  L61288258649.4  L62781514286.3  L66151427842.16 L7282989406.4   L8695580055.5   L9949055884.9   00000400]01101@01O01X01a01m02>02?02H02X03203D03[03d03l04@04A04^05805D05H05f06406?06b07007@07US2spS1L2sp2lo4SLO23nXc3pXc2xs3HLS3ACL4LEN12PCS2nX2nA1n3nXc3NXB2NRS1L2HI2sp1h1a1CS2sp2lo2nA2pA1HS3nXc3NR1S2nA1n2NRS2Aa2A01a2HaS1L2sp2lo3HLS3SLOFS2nA1n2NRS2ys3xs12CV1H2H0S2nX2nA1n3nXc3NXB2NR2n12CNS1L2sp2lo4SLO23HLSS1L2sp2lo1X4SLO23HLS2XSS2nA1n2NRS2nA3NRAS2nA1n3nXc3NX12n12CNSS1L2sp2lo3HLS3ACL3SLO3SPB3ACPS2nA1n3nXc3NX12NR2n12CN2N0S2nA1n2NR2H0S2KRS1L2sp2lo4SLO23nXc3pXc3HLS1a1OS1L2sp2lo4SLO2S1n3nXc3NX1S2sp2r03SPA1q1r1H2H02q02H43pXc4XPALS2sp2lo2Aa3OA4S1L2HI2sp1h4HTOPS1L2lo3nXc3pXc3ACL2PC". (* [comment removed for export] *)
  Lemma mi_T : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pn,$?.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px21,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Phc,(22.$18.VL,VHI,)PLBc,(23.$24.)Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$25.PdXc,$3?.P,(26.$18.VL,VHI,Vh,VLB,Vm,Vmo,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(28.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(13.$24.)R5.R4.R3.R2.R1.)P,P,(40.(5.$?.VAa,VX,))(4.(41.$18.VL,VLB,Vm,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))(42.$18.Vsp,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R6.R5.R3.))P,P,(5.$?.VAa,VX,)(5.$3?.(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(5.$43.(44.R4.)$29.)P,(19.(21.R1<.+1.)(45.R5.))P,(19.(45.R6.)(3;.VnX,(21.R1=.+1.)))P,(5.$?.(46.R7.)VsX,)P,(5.$?.(3:.(47.R8.))(3:.Vxs0,))P,P,(5.$?.VAa,VX,)(5.$?.(39.(47.R:.)R21.)(3:.Vxs0,))P,(4.(19.+1.R21.)(19.R21.VnA,))P,(5.$?.(39.Vys,R22.)(3:.Vys,))P,(1>.(3:.Vys,)(1?.+2.(20.+20.R23.)))P,(19.+1.Vb,)(3=.$18.R?.(3>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)Vb,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(6.(7.R21.(8.&40.(11.(12.&40.Vsp,)+40.))Vgp,Vtp,R24.R23.R22.(8.&40.VX,)(8.&40.R25.)R20.(8.&40.VAa,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.Vwb,R17.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R16.R15.R14.R13.)VF,(8.&40.+1?494.)Vfc,(:.(2.&40.))R10.(;.$18.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J AJ AX OWNc NX1 NXB SGc LVc LVn NR HYS YB B1. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *. subst own sg.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad'.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ _ XIN XPAL ARR1 P0 PC PI.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep.
    destruct (Z.eq_dec Aa X) as [EA|NEA].
    - (* [comment removed for export] *)
      specialize (LVn EA).
      assert (VB : limbs_val xs < 2 ^ (32 * n)).
      { rewrite LVc, <- LVn. apply lval_range. clear - NR; lia. }
      pose proof (AX EA) as E. injection E as E1 E2 E3 E4 E5 E6 E7.
      eapply aevtM_cut_evt; [exact MK1| eapply P_copy_self with (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia);
        [exact MI1| exact ST1| clear - SLO2 HLS; lia| clear - SPA; Z.div_mod_to_equations; lia| rewrite EA; reflexivity]|].
      cbv beta. intros ms' (m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in MU2, ST2 by (clear - SPB SLO HLS ACL ACP; lia).
      replace (ret_pc (Z_to_bv 64 128160)) with (Z_to_bv 64 128160) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (ARR2 : u32arr psegs m2 pXc xs).
      { eapply u32arr_transport; [exact ARR1| exact MU2| exact WM2|]. cbn. clear - PC ACL SLO2 HLS LEN1. lia. }
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU2 WM2 MI2 ST2
                    ltac:(intros a NO; destruct (outside_dec [(bv_unsigned sp - 64 - 48, bv_unsigned sp - 64)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O SLO2 HLS; lia])
                    ltac:(cbn; clear - SLO HLS; lia) ltac:(cbn; clear - XS SLO2 HLS; lia) ARR2 eq_refl) as J2.
      pose proof J2 as JY. destruct JY as [MI2' _ _ _ _ _ _ MX2 _ _ _ _ _ _ _ _].
      flat constr:(MX2) 2%nat. intros (CX2 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
      pose proof (munch_refl ([] : list ivl) m2) as MU'. pose proof (wmono_refl psegs m2) as WM'.
      assert (LVn' : lval xs n = limbs_val xs) by (rewrite LVn, LVc; reflexivity).
      zstep. rewrite EA.
      eapply mi_MLA with (ss := xs); [exact J2| exact CX2| apply u32arr_ro; exact ARR2| clear - NR; lia| rewrite LEN1; clear - NX1; lia| rewrite LEN1; clear - NR1; lia| exact NX1
        | left; split; reflexivity| clear - XPAL; Z.div_mod_to_equations; lia| exact P0| left; rewrite LEN1; exact PC| left; rewrite LEN1; clear - PC ACL SLO HLS; lia
        | exact LVn'| exact VB| exact B1| clear - NXB NR; lia|].
      unfold mpd_val. cbn [md_sg md_limbs]. rewrite LVc, <- E2, <- E5. reflexivity.
    - (* [comment removed for export] *)
      flat constr:((AJ NEA)) 2%nat. intros DBJ B. pose proof DBJ as [MA0 OA CRA CRAL SXA]. flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B)) 8%nat. intros A0 A16 AAL LENA NRA AS OWNA0 OWNA1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      pose proof B as [BA BSS BSL]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BSS, BSL.
      pose proof (opnd_at_mpd_back _ _ _ _ _ _ _ MAG BA) as BAm.
      destruct (bj_client _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ [] hc LBc mc moc _ LBc lo J B ltac:(intros bb Hb _; exact Hb) ltac:(clear - SLO HLS; lia)) as [C1 C2].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in C1, C2.
      pose proof (HCOPY MSF MSFE) as SPc. unfold mpi_copy_stmt, P_MPI_COPY in SPc.
      eapply aevtM_cut.
      { eapply SPc with (dX := mkMPD X sX nXc pXc xs padX LHeap) (dY := dA) (lo := lo); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
          rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try reflexivity; try eassumption.
        - right. cbn [md_addr]. exact SXA.
        - unfold copy_sep. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
          split; [exact OA1|]. split; [exact BSS|]. split; [| split; [clear - OA4; lia| split; [intros AN; destruct (OA5 AN); clear - H; lia| intros a Ha; clear - Ha A0; lia]]].
          destruct ownA; [right; right; left; reflexivity| |]; right; right; right; apply BSL; [reflexivity| discriminate| reflexivity| discriminate].
        - split; [| split; [exact (proj1 (proj2 XW))| cbn [md_own md_addr md_p md_n]; exact XP1]]. cbn [md_addr].
          intros a Ha. destruct (xj_cwX _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J a Ha) as [C|[C|C]]; [left; rewrite HT1; clear - C; lia| right; left; exact C| right; right; exact C].
        - clear - SLO2; lia.
        - rewrite HT1. clear - HTOP; lia.
        - clear - SPA. Z.div_mod_to_equations. lia. }
      cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m1 mo1 h1 LB1 dX1 r E PO. injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 CR.
      replace (ret_pc (Z_to_bv 64 128160)) with (Z_to_bv 64 128160) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      flat constr:(CR) 2%nat. flclear CR. intros CR1 BK. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CR1, BK.
      assert (BK' : binop_keep LBc (mkMPD X sX nXc pXc xs padX LHeap) dX1).
      { flat constr:(BK) 3%nat. flclear BK. intros K1 K2 K3. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. cbn [md_n].
        destruct CR1 as [(_ & _ & K4 & _)|(_ & K4 & _)]; [exact K4| rewrite K4; apply Z.le_refl]. }
      pose proof (xj_call _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HT2 HH2 MX2 OUT2 HPX2 SOK2 BK') as J2.
      pose proof (bj_call _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ DBJ J B MI2 HH2 MX2 OUT2 HPX2 BK') as B2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      destruct dX1 as [X1 sg1 n1 p1 xs1 pad1 own1]. flat constr:(BK') 4%nat. flclear BK'. intros E1 E2 FR2 NM2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X1 pad1.
      clear MU WM JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 NM1 CX1.
      pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl psegs m1) as WM.
      zstep. if_cases KR; zify_cond KR.
      { (* [comment removed for export] *) destruct CR1 as [(-> & _)|(-> & _)]; [exfalso; apply KR; reflexivity|].
        eapply mi_ret; wctx; [exact J2| right; reflexivity]. }
      destruct CR1 as [(-> & CV & CN)|(-> & _)]; [| exfalso; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
      assert (EO1 : own1 = LHeap).
      { pose proof J2 as JY. destruct JY as [_ _ _ _ _ _ _ MX3 _ _ NS3 _ _ _ _ _]. cbn [md_own] in NS3.
        destruct own1; [| reflexivity| exfalso; exact (NS3 eq_refl)]. exfalso.
        flat constr:(MX3) 2%nat. intros FLt1 _. flat constr:(FLt1) 6%nat. flclear FLt1. intros _ _ _ _ _ OW. cbn [md_own md_p md_n] in OW. flat constr:(OW) 2%nat. flclear OW. intros _ N0. clear - N0 CN NX1 NR. lia. }
      subst own1.
      pose proof J2 as JY. xj_open JY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      flat constr:((opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ B2))) 2%nat. intros FLt2 SGA. flat constr:(FLt2) 6%nat. flclear FLt2. intros CA2 _ _ _ _ OWA2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CA2, OWA2, SGA. unfold mpi_cells in CA2.
      pose proof B2 as [_ BSS2 BSL2]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in BSS2, BSL2.
      flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B2)) 8%nat. intros _ _ _ _ _ _ _ OWNA2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OWNA2.
      destruct (OWNA2 ltac:(destruct ownA; [destruct (OWNA0 eq_refl); exfalso; clear - H0 NR; lia| discriminate| discriminate])) as (NA1 & PA0 & PA4 & ABY & ALS & AIN).
      (* [comment removed for export] *)
      assert (AV : limbs_val xs1 = limbs_val ys).
      { unfold mpd_val in CV. cbn [md_sg md_limbs] in CV. pose proof (limbs_val_nonneg xs1). pose proof (limbs_val_nonneg ys).
        flat constr:(MX1) 2%nat. intros _ SG1. cbn [md_sg] in SG1. destruct SG1 as [-> | ->]; destruct SGA as [-> | ->]; clear - CV H H0; lia. }
      eapply mi_MLA with (ss := ys) (S := pA); [exact J2| exact CA2| exact ABY| clear - NR; lia| rewrite LENA; clear - NR; lia| rewrite LENA; clear - NRA; lia| clear - CN NX1; lia
        | | exact PA4| exact PA0| | rewrite LENA; exact ALS| rewrite AV; exact HYS| rewrite AV; exact YB| exact B1| clear - CN NXB NR; lia|].
      + right. rewrite LENA. destruct (BSL2 eq_refl ltac:(destruct ownA; [destruct (OWNA0 eq_refl); exfalso; clear - H0 NR; lia| discriminate| discriminate])) as [D|D]; [right; exact D| left; exact D].
      + rewrite LENA. destruct ownA; [destruct (OWNA0 eq_refl); exfalso; clear - H0 NR; lia| |].
        * left. flat constr:((AIN eq_refl)) 2%nat. intros AIN0 _. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
          flat constr:((proj1 (Forall_forall _ _) HBR0 _ AIN0)) 5%nat. intros _ _ _ R3 _. exact R3.
        * right. flat constr:(MAG) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros _ _ _ _ _ OWS. cbn [md_own md_p md_n md_limbs] in OWS. flat constr:(OWS) 5%nat. flclear OWS. intros _ _ _ _ RO. exact RO.
      + unfold mpd_val. cbn [md_sg md_limbs]. unfold mpd_val in CV. cbn [md_sg md_limbs] in CV. rewrite CV. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L10642801822.2  L10774442601.164L15864777803.9  L2059982179.4   L2101813687.162 L23072471841.0  L23100341967.160L25069632707.1  L27485105529.6  L31166230855.7  L32027975233.0  L38900785985.4  L50943842389.2  L52627813748.162L52630056116.163L5412464964.9   L57097980552.3  L58948685323.3  L61804252431.0  L66928405.3     L68370415057.2  L9271121718.165 00000601001D01M02Q02R03D03G03V03j03k04404:05D06N06j07507@07A07K07Q08ES1n2N1S2ra2sp2s02s12s22s32s42s51b2j01X2nX2nA2BB2wb3WB01n1p2xs2P0S1L2sp2lo1n1p3ACL2PCS1n1p1a1OS2ra2sp2s02s12s22s32s42s51b2j01X2nX2nA2BB2wb3WB01n1p2xs3SPB2X02N12P0SS2ra2sp2s02s12s22s32s42s51b2j01X2nX2nA2wb3WB01p2xsS1pS2sp2lo1n1p1a1OS1L1n1p3ACV2N12P02PCSS1X1n1p1HS1n2N1S1L2ra2sp2s02s12s22s32s42s51b2j01X2nX2nA2BB2wb3WB01n1p2xs3SPB3ACV2X02N12PCS1L2ra2sp2s02s12s22s32s42s51b2j01X2nX2nA2BB2wb3WB01n1p2xs3SPB3ACV2X02N12PCS1L2sp2lo1n1p3HLS3ACL3SLO2PCS1n2xs4LEN1S1n2xs4LEN1SS1n3NR12N1S1n2N1S2ra2sp2s02s12s22s32s42s51b2j01X2nX2nA2wb3WB01n1p2xs". (* [comment removed for export] *)
  Lemma mi_FIN : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Px9,(2.&40.)Pa1,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Phc,(22.$18.VL,VHI,)PLBc,(23.$24.)Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$25.Psg,$?.Pn,$?.Pp,$?.Pxs,(23.(2.&40.))P,(26.$18.VL,VHI,Vh,VLB,Vm,Vmo,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(28.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(13.$24.)R8.R7.R6.R5.(27.VX,R4.R3.R2.R1.VpadX,$29.))P,(19.R4.(3;.VnX,(21.VnA,+1.)))P,(5.$?.(20.(3<.(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))Vb,)=)(3=.$18.R8.(3>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)Vb,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(6.(7.R1;.(8.&40.(11.(12.&40.Vsp,)+40.))Vgp,Vtp,R1>.R1=.R1<.(8.&40.VX,)R1:.(8.&40.R5.)R19.(8.&40.(20.+4.R6.))R18.R17.R16.R15.R14.R13.R12.R11.R10.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(8.&40.+1?524.)Vfc,(:.(2.&40.))R9.(;.$18.)))")
(* [comment removed for export] *).
  Proof.
    intros until xs. intros J NXB VAL0. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    flat constr:((OWN1 ltac:(discriminate))) 8%nat. intros _ N1 XIN XPAL ARR1 P0 PC PI.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep.
    pose proof P_memset_spec as SPm. unfold memset_stmt in SPm.
    assert (U1 : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; clear - P0 PC ACV N1; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (4 * n)) = 4 * n) by (apply unsigned_lit; clear - N1 NR1; lia).
    eapply aevtM_cut_evt; [exact MK1| eapply SPm; rewrite ?U1, ?U3; [replace (Z.to_nat (4 * n)) with (4 * length xs)%nat by (clear - LEN1; lia); apply u32arr_cells; exact ARR1| exact MI1]|].
    clear SPm. unfold memset_post. cbv beta. intros ms' PO.
    flat constr:(PO) 20%nat. flclear PO. intros z0 z1 z2 za1 za2 z3 z4 z5 z6 z7 z8 z9 z10 z11 m2 -> MU2 WM2 MI2 PA2.
    rewrite ?U1, ?U3 in MU2. rewrite ?U1, ?U3, ?(unsigned_lit 0) in PA2 by (clear; lia).
    replace (ret_pc (Z_to_bv 64 128300)) with (Z_to_bv 64 128300) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    change (0 mod 256) with 0 in PA2.
    assert (ARR2 : u32arr psegs m2 p (repeat (Z_to_bv 64 0) (Z.to_nat n))).
    { eapply u32arr_of_cells; [exact PA2|]. rewrite u32s_repeat0. f_equal. clear - N1; lia. }
    assert (ST2 : stk psegs m2 lo (bv_unsigned sp - 64)).
    { eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn. clear - PC ACL SLO HLS. lia. }
    pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J MU2 WM2 MI2 ST2
                  ltac:(intros a NO; destruct (outside_dec [(p, p + 4 * n)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                  ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H; lia) ARR2 ltac:(rewrite repeat_length; clear - LEN1; lia)) as J2.
    clear MU WM JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1 ARR1 MU2 WM2 PA2 ARR2 ST2 MI2.
    pose proof J2 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX1) 2%nat. intros (CX2 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
    flat constr:((OWN1 ltac:(discriminate))) 6%nat. intros _ _ _ _ ARR2' _.
    clear HH1 SOK1 HPX1 FR1.
    pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with MI3 : mem_inv psegs m3, CX3 : rw_cells psegs m3 X _ |- _ =>
      pose proof (xj_struct_sign _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ 1 J2 MU WM MI3 CX3 ltac:(left; reflexivity)) as J3 end.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J3.
    clear J2 JX MI1 ST1 HT1 MF1 MX1 AD1 PD1 NS1 OUT1 FRS1 XP1 NM1 CX2 MU WM ARR2'.
    pose proof J3 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX1) 2%nat. intros FLt4 _. flat constr:(FLt4) 6%nat. flclear FLt4. intros _ _ _ LEN3 _ FLt5. flat constr:(FLt5) 4%nat. flclear FLt5. intros _ _ _ ARR3. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ARR3, LEN3.
    clear HH1 SOK1 HPX1 FR1.
    pose proof (munch_refl [(p, p + 4 * n)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    pose proof (u32arr_store_ok psegs m3 p (repeat (Z_to_bv 64 0) (Z.to_nat n)) 0 _ ARR3 ltac:(rewrite repeat_length; clear - N1; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write psegs m3 p (repeat (Z_to_bv 64 0) (Z.to_nat n)) 0 v ARR3 ltac:(rewrite repeat_length; clear - N1; lia)) as ARR4 end.
    replace (p + 4 * 0) with (p + 0) in ARR4 by (clear; lia).
    clear ARR3. store_done.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with ST4 : stk psegs m4 _ _, MI4 : mem_inv psegs m4 |- _ =>
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J3 MU WM MI4 ST4
                    ltac:(intros a NO; left; destruct (outside_dec [(p, p + 4 * n)] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                    ltac:(cbn; clear - PC ACL SLO HLS; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H; lia) ARR4
                    ltac:(rewrite upd_length; reflexivity)) as J4 end.
    eapply mi_ret; wctx; [exact J4|]. left. split; [reflexivity|]. cbn [md_n]. split; [| exact NXB].
    rewrite VAL0. unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_upd by (rewrite repeat_length; clear - N1; lia).
    rewrite limbs_val_repeat0, limb32_repeat0.
    lazymatch goal with |- context [bv_unsigned ?v mod _] => let e := eval vm_compute in (bv_unsigned v mod 2 ^ 32) in change (bv_unsigned v mod 2^32) with e end.
    clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L16164355889.3  L19061415402.1  L2213969368.15  L22717164081.0  L23100341967.139L23100341967.166L23100341967.172L27177789875.15 L32879090465.0  L39172636981.0  L44397119921.2  L46756382136.171L47957488780.137L47957588755.138L49578233423.166L52476066706.172L56181220937.2  L57992923505.3  L58980668962.8  L59308546384.3  L59308633593.6  00000700;00H00I01401b02P02g02h02i03104704l05a06O07Q07X07c08@08J08US2nX2nAS2nXS1L2sp2lo3SLOSS2ra2sp2s02s12s22s32s42s51b2j01X3xs02wb3WB0S2ra2sp2s02s12s22s32s42s51b2j01X3xs02wb3WB02AnS2ra2sp2s02s12s22s32s42s51b2j01X3xs02wb3WB02AnS1L2HI2sp1h2hc4HTOP3HT1SSS2nX3NR1S1L2ra2sp2s02s12s22s32s42s51b2j01X3xs02BB2wb3WB03SPB3ACV2X02An3An03AnCS2ra2sp2s02s12s22s32s42s51b2j01X2nX3xs02BB2wb3WB03NR1S2ra2sp2s02s12s22s32s42s51b2j01X2nX3xs02BB2wb3WB03NR1S2ra2sp2s02s12s22s32s42s51b2j01X3xs02wb3WB02AnS2ra2sp2s02s12s22s32s42s51b2j01X2pX3xs02BB2wb3WB03SPB2X02EP2An3An0S2nX2KNS2nX2nA3NA0S1L2sp2lo3HLS3ACL3SLO3SPB3ACPS2nX2KN2N1S2An3An02KZ". (* [comment removed for export] *)
  Lemma mi_LSET : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Px9,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Phc,(22.$18.VL,VHI,)PLBc,(23.$24.)Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$25.P,(26.$18.VL,VHI,Vh,VLB,Vm,Vmo,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(28.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(13.$24.)R4.R3.R2.R1.(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(5.$?.(20.(3<.(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))Vb,)=)P,(19.=VnA,)(3=.$18.R4.(3>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)Vb,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(6.(7.R19.(8.&40.(11.(12.&40.Vsp,)+40.))Vgp,Vtp,R1<.R1;.R1:.(8.&40.VX,)R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(8.&40.+1?4<4.)Vfc,(:.(2.&40.))R5.(;.$18.)))")
(* [comment removed for export] *).
  Proof.
    intros until moc. intros J VAL0 NA0. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. rewrite zx16_small by (clear - NR1; lia).
    zstep. if_cases KN; zify_cond KN; rewrite ?Z.mod_small in KN by (clear - NR1; lia).
    - (* [comment removed for export] *)
      assert (EO : ownX = LNull).
      { destruct ownX; [reflexivity| | exfalso; exact (NST eq_refl)]. exfalso. flat constr:((OWN1 ltac:(discriminate))) 3%nat. intros _ N1 _. clear - N1 KN; lia. }
      flat constr:((OWN0 EO)) 2%nat. intros EP _.
      zstep. zstep. zstep.
      replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
      eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := 1) (sz := 4) (lo := lo);
        rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity;
        clear - SLO HLS ACL ACP HTOP HT1 NR1 SPB; try lia | ].
      intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
      flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HPc h2 HT2 RES2.
      replace (ret_pc (Z_to_bv 64 128228)) with (Z_to_bv 64 128228) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
      clear MU WM.
      destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
      { (* [comment removed for export] *)
        pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HPc HT2 HH2) as J2.
        pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
        pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
        zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
        eapply mi_retm16; wctx. exact J2. }
      replace (1 * 4) with (4 * 1) in * by (clear; lia).
      destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HPc HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - KN; lia)) as [J2 F2].
      flat constr:(HBA) 5%nat. intros An0 An16 _ AnC AnI. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      clear HPc JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 NM1 CX1 AD1 PD1.
      pose proof J2 as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      flat constr:(MX1) 2%nat. intros (CX2 & _) _. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV; lia|].
      zstep. zstep. if_cases KP; zify_cond KP; [| exfalso; apply KP; rewrite EP; reflexivity].
      pose proof (xg_null _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 EO) as D2.
      clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      clear HH1 HH2 HNEW SOK1 ST2 FR1 HPX1 MI1.
      zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D2 MU WM MI2 CX2) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
      zstep. replace (Z_to_bv 64 4) with (Z_to_bv 64 (4 * 1)) by reflexivity.
      eapply mi_FIN; wctx; [exact J5| clear - NA0; lia| exact VAL0].
    - (* [comment removed for export] *)
      assert (EO : ownX = LHeap).
      { destruct ownX; [(flat constr:((OWN0 eq_refl)) 2%nat; intros _ N0); exfalso; exact (KN N0)| reflexivity| exfalso; exact (NST eq_refl)]. }
      zstep. zstep. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. replace (nX * 4) with (4 * nX) by (clear; lia). zstep.
      assert (J' : XJ0 hc LBc mc moc (mkMPD X sX nX pX xs0 padX LHeap)) by (rewrite <- EO; exact J).
      eapply mi_FIN; wctx; [exact J'| clear - NA0; lia| exact VAL0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L18992955035.3  L23727568990.4  L2424859202.3   L29971683454.3  L31318245783.5  L38826201912.3  L39268637205.0  L39528177321.7  L44397119921.2  L44473972531.3  L47957489419.142L53465357057.11 L59308546259.6  L61929802144.139L61929802795.142L61929803438.140L67529933474.3  00000900F00O00X00j01301401N01V01_02V02e03704905306506>S2nA1n2NRS2nX1n3N102KGS2nA1n2NRS2nA1n2NRS2nX3xs01n4LEN12KGS2nX1n2KGSS2Aa2sA2nA2pA2ys4padA4ownAS2nX3NR1S2nX1n2KGS2ra2sp2s02s12s22s32s42s51b2j01X2nX3xs02BB2wb3WB01n3NR1S1n1q2KL1r1H2H0S2nX2nA1n2NR2KG2N0S2ra2sp2s02s12s22s32s42s51b2j01X3xs02nA2BB2wb3WB01n2NR4NA103SPB2X0S2ra2sp2s02s12s22s32s42s51b2j01X3xs02nA2BB2wb3WB01n2NR3N10S2ra2sp2s02s12s22s32s42s51b2j01X3xs02nA2BB2wb3WB01n2NR4NA103SPB2X0S1b2BB2KB". (* [comment removed for export] *)
  Lemma mi_FOUND : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pn,$?.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Phc,(22.$18.VL,VHI,)PLBc,(23.$24.)Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$25.P,(26.$18.VL,VHI,Vh,VLB,Vm,Vmo,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(28.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(13.$24.)R4.R3.R2.R1.(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,P,(40.(5.$?.VAa,VX,))(4.(41.$18.VL,VLB,Vm,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))(42.$18.Vsp,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R5.R4.(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))P,P,(5.$?.VAa,VX,)(5.$3?.(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(4.(19.+1.R1:.)(19.R1:.VnA,))P,(5.$?.(39.Vys,R1;.)(3:.Vys,))P,(19.VnA,+2710.)(3=.$18.R7.(3>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)Vb,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(6.(7.R19.(8.&40.(11.(12.&40.Vsp,)+40.))Vgp,Vtp,R1<.R1;.R1:.(8.&40.VX,)(8.&40.R1=.)R18.(8.&40.VAa,)Vwb,R17.R16.R15.R14.R13.R12.R11.R10.R?.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(8.&40.+1?420.)Vfc,(:.(2.&40.))R8.(;.$18.)))")
(* [comment removed for export] *).
  Proof.
    intros until moc. intros J AJ AX NR HYS NA10. jc_open. assert (NA0 : 0 <= nA) by (clear - NR; lia).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J)) 12%nat. intros HBR1 HAP1 ND1 MK1 XS X0 X16 XAL LEN1 NR1 OWN0 OWN1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    pose proof J as JX. xj_open JX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX1) 2%nat. intros (CX1 & _) SGX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX1, SGX. unfold mpi_cells in CX1.
    assert (YB : limbs_val ys < 2 ^ (32 * n)) by (rewrite <- HYS; apply lval_range; clear - NR; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *) apply (proj1 WB0) in KB. eapply mi_LSET; wctx; [exact J| rewrite KB; clear; lia| exact NA0]. }
    assert (KB' : b <> 0) by (intros E; exact (KB (proj2 WB0 E))). clear KB. rename KB' into KB.
    zstep. zstep. zstep. zstep. if_cases KL; zify_cond KL.
    { (* [comment removed for export] *) eapply mi_ret; wctx; [exact J| right; reflexivity]. }
    rewrite Z.shiftr_div_pow2 in KL by (clear; lia). change (2 ^ 4) with 16 in KL. rewrite ?Z.mod_small in KL by (clear - NR NA10; lia).
    assert (N10 : n < 10000) by (clear - KL NR; Z.div_mod_to_equations; lia).
    zstep. zstep. rewrite zx16_small by (clear - NR1; lia). zstep. if_cases KG; zify_cond KG; rewrite ?Z.mod_small in KG by (clear - NR NR1 N10; lia).
    - (* [comment removed for export] *)
      assert (EO : ownX = LHeap).
      { destruct ownX; [(flat constr:((OWN0 eq_refl)) 2%nat; intros _ N0); exfalso; clear - N0 KG NR; lia| reflexivity| exfalso; exact (NST eq_refl)]. }
      eapply (mi_T n) with (dXc := dX); wctx; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        [exact J| exact AJ| exact AX| exact EO| clear - KG; lia| clear - KG; lia| reflexivity| reflexivity| | exact NR| exact HYS| exact YB| clear - KB BB; lia].
      intros EA. pose proof (AX EA) as E. injection E as E1 E2 E3 E4 E5 E6 E7. rewrite <- E5. exact HYS.
    - (* [comment removed for export] *)
      eapply (mi_G L HI HFREE HCALLOC) with (dXc := dX); wctx; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try reflexivity.
      + (* [comment removed for export] *) unfold KC_stmt. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. intros until dXc. intros KJ KA KO KN KM KS KV KW.
        eapply (mi_T n); wctx; [exact KJ| intros NE; split; [exact (proj1 (AJ NE))| exact (KA NE)]| exact AX| exact KO| exact KN| exact KM| exact KS| exact KV
          | intros _; exact KW| exact NR| exact HYS| exact YB| clear - KB BB; lia].
      + exact J.
      + exact AJ.
      + clear - KG N10; lia.
      + clear - NR; lia.
      + unfold lval. rewrite firstn_all2 by (clear - KG LEN1; lia). reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L18992922267.2  L21041645149.3  L23970764156.132L31686774790.130L42608597650.1  L50968257341.2  L54425651213.3  L59308583409.4  L59310648043.6  L62517290823.2  L64912137160.4  L780814420.4    L7939067828.2   00000700?01f03103403:03C03O03d03j04604B04HS2nA2HRS1k1r2HkS2ra2sp2s02s12s22s32s42s51b2j01X2sX2nX2pX3xs04padX4ownX2nA2pA2ys2BB2wb3WB01k1r2Hk4LENY3PA02HR3SPB2X02EBS2ra2sp2s02s12s22s32s42s51b2j01X2sX2nX2pX3xs04padX4ownX2pA2ys2wb3WB01k1r2HkS1rS2pA1rS2nA1r2HRS2nA1r2Hk2HRS2nA2ys1r4LENY2HR3NTHS2ys1rS2nA1r2HR2K2S2nA1r2HR2K2S1b2sA". (* [comment removed for export] *)
  Lemma mi_SCANLOOP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "Pk,$48.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pr1,(2.&40.)Pr0,(2.&40.)Phc,(22.$18.VL,VHI,)PLBc,(23.$24.)Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$25.Pr,$?.P,(19.R1.(31.R19.))P,(26.$18.VL,VHI,Vh,VLB,Vm,Vmo,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.(28.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vj0,)(13.$24.)R6.R5.R4.R3.(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,P,(40.(5.$?.VAa,VX,))(4.(41.$18.VL,VLB,Vm,(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,))(42.$18.Vsp,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)R7.R6.(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))P,P,(5.$?.VAa,VX,)(5.$3?.(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)(27.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))P,(2?.$18.R7.VpA,(30.Vys,))P,(5.$?.(31.(32.(2.&40.)Vys,))VnA,)P,(19.VnA,+2710.)P,(1>.=VpA,)P,(4.(19.+1.R9.)(19.R9.VnA,))P,(5.$?.(39.Vys,R:.)(3:.Vys,))P,(5.(2.&40.)R11.(8.&40.R;.))P,(5.(2.&40.)R11.(8.&40.(11.(21.VpA,(20.+4.R<.))+4.)))(3=.$18.R>.(3>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,(27.VAa,VsA,VnA,VpA,Vys,VpadA,VownA,)Vb,Vlo,VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(6.(7.R21.(8.&40.(11.(12.&40.Vsp,)+40.))Vgp,Vtp,R24.R23.R22.(8.&40.VX,)R13.R12.(8.&40.VAa,)Vwb,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(8.&40.+1?408.)Vfc,(:.(2.&40.))R?.(;.$18.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until r; intros Hk J AJ AX EBY LENY NY10 PA0 HR YA -> ->; [exfalso; clear - Hk HR; lia|].
    jc_open; pose proof (bv_unsigned_in_range 64 sp) as SPB; change (bv_modulus 64) with (2^64) in SPB; pose proof alloc_ceiling_pos as ACP.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1); cbn [app] in HBR1, HAP1, ND1.
    pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI1.
    pose proof (u32ro_bound _ _ _ _ EBY) as EB.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    destruct (nth_error ys (Z.to_nat (r - 1))) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear - NTH LENY HR; lia].
    pose proof (u32ro_read psegs mc pA ys (r - 1) w _ EBY NTH ltac:(clear - HR; lia) ltac:(f_equal; clear; lia)) as RD.
    zstep. clear RD.
    pose proof (limb32_w32_nth ys (Z.to_nat (r - 1)) w NTH) as LW. pose proof (w32_range w) as WR.
    zstep. if_cases K0; zify_cond K0; rewrite bv_unsigned_sx32 in K0; fold (w32 w) in K0.
    - (* [comment removed for export] *)
      eapply mi_FOUND; wctx; [exact J| exact AJ| exact AX| exact HR| exact YA| exact NY10].
    - (* [comment removed for export] *)
      apply (proj1 (sxz_zero_iff _ WR)) in K0.
      assert (YA' : lval ys (r - 1) = limbs_val ys).
      { rewrite <- YA. replace r with (r - 1 + 1) at 2 by (clear; lia). rewrite (lval_succ ys (r - 1)) by (clear - HR; lia). rewrite LW, K0. clear; lia. }
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply IH with (r := r - 1); try eassumption; [clear - Hk; lia| clear - HR K2; lia| f_equal; clear; lia| f_equal; clear; lia].
      + (* [comment removed for export] *)
        assert (r = 1) as -> by (clear - K2 HR; lia). change (1 - 1) with 0 in YA'. rewrite lval_0 in YA'.
        zstep. eapply mi_LSET; wctx; [exact J| | clear - HR; lia]. unfold mpd_val. cbn [md_sg md_limbs]. rewrite <- YA'. clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Body.

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
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Hypothesis HMLA : mpi_core_mla_vstmt psegs P_MPI_CORE_MLA.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0@L1175746480.1   L12283411672.119L13301871092.119L14106684376.118L17646078182.121L18995052170.2  L27462318639.8  L32982742029.2  L3446086797.6   L36977691517.2  L38218545178.3  L38232090713.4  L38948636245.0  L39172636981.0  L39887139444.119L40228640085.0  L41288976216.119L42585448788.124L42585448788.125L43059482540.119L44866992728.119L454269955.7    L45898055924.119L47343275948.2  L47606469953.2  L48429268312.119L5145216728.119 L51925114228.119L52101694457.9  L5290668657.2   L53482820749.8  L54391891673.10 L5670284798.124 L5670284798.125 L57933933556.119L59310727507.4  L59314955108.4  L59435147825.145L61812331454.140L61812495125.144L63962036340.118L65294145718.7  L7274816372.119 L785248895.5    L7940923221.2   L8722184664.119 00000400O00j01E01`01h02B02J02`02h02i03703803903T03U04005L07707g08B08[09609>09F09a0:<0:W0;60;=0;W0<80=M0?10?L0?\0?f0@A0@c0AE0A`0B70BR0Bd0Bj0CES2spS2sp2a21X3xs02Aa2ys3XBD3ABDS2sp2a21X3xs02Aa2ys3XBD3ABDS2sp2a21X3xs02Aa2ys3XBD3ABDS2sp2a21X3xs02Aa2ys3XBD3ABDS2nA3NRAS1L3HLS2sp2nA2pA2lo4SLO21HS2nA3NRAS1L3HLS2sp2lo4SLO23ACLS2nA3NA1FS1L2sp2lo4SLO2SSS2sp2a21X3xs02Aa2ys3XBD3ABDSS2sp2a21X3xs02Aa2ys3XBD3ABDS1L3HLS2ra2sp2a21X2pX3xs02Aa2pA2ys1b2lo4SLO23SPA2BB3WB03SPB3XAL2X03XBD3ABD2XS2HB5Ha_st5Hl_stS1L3HLS2sp2s02a21X2pX3xs02Aa2pA2ys1b2lo4SLO23SPA2BB3WB03SPB3XAL2X03XBD3ABD2XS2HB5Ha_st5Hl_st2s12s22s32s42s5S1L3HLS2sp2a21X3xs02Aa2ys2lo4SLO23SPB2X03XBD3ABDS2sp2a21X3xs02Aa2ys3XBD3ABDS1L3HLS2sp2Aa2lo4SLO23OA4S2sp2a21X3xs02Aa2ys3XBD3ABDS2nA3NRAS2nA3NA1S2sp2a21X3xs02Aa2ys3XBD3ABDS2sp2a21X3xs02Aa2ys3XBD3ABDS2sp2a21X3xs02Aa2ys3XBD3ABDS1L3HLS2sp2lo4SLO23ACL3DHI1a2HdS2nA2pAS1L3HLS2sp2nX2pX2lo4SLO21HS1L2HI3HLS2sp1h2lo4SLO24HTOP1a2NOS1L3HLS2ra2sp2a21X2pX3xs02Aa2pA2ys1b2lo4SLO22BB3WB03SPB2X03XBD3ABD3OA42HB5Ha_st5Hl_stS1L3HLS2sp2s02a21X2pX3xs02Aa2pA2ys1b2lo4SLO22BB3WB03SPB2X03XBD3ABD3OA42HB5Ha_st5Hl_st2s12s22s32s42s5S2sp2a21X3xs02Aa2ys3XBD3ABDS2nA2ys4LENA3KA0S1X2Aa1D1ES2sp2a21X3xs02Aa2ys3XBD3ABDS2sp2a21X3xs02Aa2nA2ys3NRA3XBD3ABDS2sp2a21X3xs02Aa2nA2ys3NRA3XBD3ABDS2sp2a21X3xs02Aa2ys3XBD3ABDS1L3HLS2sp1X2lo4SLO22XSS2sp2a21X3xs02Aa2ys3XBD3ABDS1L3HLS2sp2lo4SLO2S2sA1bS2sp2a21X3xs02Aa2ys3XBD3ABD". (* [comment removed for export] *)
  Theorem P_mpi_mul_int_spec' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_int ()) "PMSF,$?.P,(5.$?.R1.$49.)P,(4:.$18.VL,VHI,$1=.R2.)(4;.$18.VL,VHI,$4<.R3.)")
(* [comment removed for export] *).
  Proof.
    intros MSF MSFE HCOPY0. unfold mpi_mul_int_stmt, P_MPI_MUL_INT. intros until lo.
    assert (HCOPY : forall MSF', MSF' = P_MEMSET_FUNC -> mpi_copy_stmt psegs L HI P_MPI_COPY MSF') by (intros MSF' ->; rewrite <- MSFE; exact HCOPY0).
    intros HH MX MA0 SXA NST OA CRA CRAL XW XLS ST SLO2 ACL HTOP SPA DHI TP MI SOK CA BB WB1 WB0 -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    destruct dX as [X sX nX pX xs0 padX ownX]. destruct dA as [Aa sA nA pA ys padA ownA].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    flat constr:(MX) 2%nat. intros FLt6 SGX. flat constr:(FLt6) 6%nat. flclear FLt6. intros CX0 XAL X0 LENX NRX OWNX. unfold mpi_cells in CX0. unfold MPI_MAX_LIMBS in NRX.
    flat constr:(MA0) 2%nat. intros FLt7 SGA. flat constr:(FLt7) 6%nat. flclear FLt7. intros CA0 _ A0 LENA NRA OWNA. unfold MPI_MAX_LIMBS in NRA.
    pose proof (rw_cells_bound _ _ _ _ CX0) as XBD. pose proof (rw_cells_bound _ _ _ _ CA0) as ABD.
    unfold mpi_cells in ABD. cbn [cells_size csize Nat.add] in XBD, ABD.
    flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5. flat constr:(XW) 3%nat. intros XCW XDW XP.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS.
    unfold mpd_sep in SXA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SXA.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (conj HH I) as HHc. clear HH. pose proof (conj SOK I) as SOKc. clear SOK.
    do 8 zstep.
    replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by (clear; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    match type of FR with rw_cells _ _ _ (CB _ ?jk :: _) => set (j0 := jk) in FR end.
    change (rw_cells psegs m0 (bv_unsigned sp - 64) (MI_FRAME ra s0 s1 s2 s3 s4 s5 j0)) in FR.
    flat constr:(HHc) 2%nat. flclear HHc. intros HH _. flat constr:(SOKc) 2%nat. flclear SOKc. intros SOK _.
    assert (JCX : JC psegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (MI_FRAME ra s0 s1 s2 s3 s4 s5 j0)).
    { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption; try reflexivity; try (clear; lia). clear - SLO2. lia. }
    assert (J0 : XJ psegs L HI h LB m mo (mkMPD X sX nX pX xs0 padX ownX) sp lo 64 (MI_FRAME ra s0 s1 s2 s3 s4 s5 j0) [] h LB m0 mo (mkMPD X sX nX pX xs0 padX ownX)).
    { constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption; try reflexivity.
      - eapply (HEAP_munch psegs L HI) with (SP := lo); [exact HH| exact MU| exact WM| exact ACL|].
        intros a Ha NO. cbn in NO. left. clear - NO HTOP SLO2 HLS. lia.
      - apply mo_frame_refl.
      - eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Hd NW. cbn. split; [clear - Hd DHI ACL SLO2 HLS; lia| exact I].
      - eapply mpd_at_munch_any; [exact MX| exact MU| exact WM| cbn; split; [clear - XS SLO2 HLS; lia| exact I]|].
        cbn [md_own md_p md_n]. intros ON. cbn. split; [| exact I]. destruct (XLS ON); clear - H SLO2 HLS; lia.
      - apply mpd_out_refl. exact NST.
      - intros bb Hb. left. exact Hb.
      - eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| clear - ACL SLO2 HLS; lia]. }
    assert (MA : mpd_at psegs m0 LB (mkMPD Aa sA nA pA ys padA ownA)).
    { eapply mpd_at_munch_any; [exact MA0| exact MU| exact WM| cbn; split; [clear - OA4 SLO2 HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (OA5 ON); clear - H SLO2 HLS; lia| exact I]. }
    pose proof J0 as JX. destruct JX as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1 NM1]. cbn [app md_addr md_p md_n md_own] in HH1, XP1.
    clear MU WM ST FR MI.
    rename m0 into mc.
    assert (AX : Aa = X -> mkMPD Aa sA nA pA ys padA ownA = mkMPD X sX nX pX xs0 padX ownX) by (intros E; destruct SXA as [E'|D]; [symmetry; exact E'| exfalso; clear - D E; lia]).
    assert (AJ : Aa <> X -> JB psegs L LB m (mkMPD X sX nX pX xs0 padX ownX) sp lo (mkMPD Aa sA nA pA ys padA ownA)
                            /\ BJ psegs sp (mkMPD Aa sA nA pA ys padA ownA) LB mc (mkMPD X sX nX pX xs0 padX ownX)).
    { intros NE. assert (D : X + 16 <= Aa \/ Aa + 16 <= X) by (destruct SXA as [E|D]; [exfalso; apply NE; injection E; auto| exact D]).
      split; [constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; try assumption; apply opnd_at_mpd; exact MA0|].
      constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; [apply opnd_at_mpd; exact MA| exact OA2|].
      intros EO AN. destruct OA3 as [C|[C|[C|C]]]; [exfalso; apply NE; injection C; auto| exfalso; exact (C EO)| exfalso; exact (AN C)| exact C]. }
    flat constr:(MA) 2%nat. intros FLt8 _. flat constr:(FLt8) 6%nat. flclear FLt8. intros CA1 _ _ _ _ OWNA1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CA1, OWNA1. unfold mpi_cells in CA1.
    pose proof (munch_refl ([] : list ivl) mc) as MU; pose proof (wmono_refl psegs mc) as WM.
    zstep. rewrite zx16_small by (clear - NRA; lia). zstep.
    zstep. if_cases KA0; zify_cond KA0; rewrite ?Z.mod_small in KA0 by (clear - NRA; lia).
    { (* [comment removed for export] *)
      eapply (mi_LSET L HI HCALLOC); try exact JCX; try eassumption.
      - unfold mpd_val. cbn [md_sg md_limbs]. destruct ys; [cbn [limbs_val]; clear; lia| exfalso; cbn [length] in LENA; clear - LENA KA0; lia].
      - clear - NRA; lia. }
    assert (AN : ownA <> LNull) by (intros C; rewrite C in OWNA; (flat constr:(OWNA) 2%nat; flclear OWNA; intros _ N0); exact (KA0 N0)).
    assert (AF : 1 <= nA /\ 0 < pA /\ bytes_at psegs mc pA (u32s ys)).
    { destruct ownA; [exfalso; exact (AN eq_refl)| |].
      - flat constr:(OWNA1) 4%nat. flclear OWNA1. intros N1 _ _ ARR. split; [exact N1|]. flat constr:(OWNA) 4%nat. intros _ AIN _ _.
        flat constr:((proj1 (Forall_forall _ _) HBR _ AIN)) 2%nat. intros R0 _. split; [exact R0| apply u32arr_ro; exact ARR].
      - flat constr:(OWNA1) 5%nat. flclear OWNA1. intros N1 _ P0 BY _. split; [exact N1|]. split; [exact P0| exact BY]. }
    flat constr:(AF) 3%nat. flclear AF. intros NA1 PA0 ABY.
    zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    eapply (mi_SCANLOOP L HI HFREE HCALLOC HCOPY HMLA IMGC) with (MSF := MSF) (k := Z.to_nat nA) (r := nA); try exact JCX; try eassumption;
      [clear - NA1; lia| clear - NRA; lia| clear - NA1; lia| apply lval_full; exact LENA| reflexivity| f_equal; clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Theorem P_mpi_mul_int_spec : forall MSF, MSF = P_MEMSET_FUNC -> mpi_mul_int_stmt psegs L HI P_MPI_MUL_INT MSF.
  Proof.
    intros MSF ->. apply P_mpi_mul_int_spec'; [reflexivity|].
    change P_MPI_COPY with P_mpi_copy.P_MPI_COPY. apply P_mpi_copy_spec; try assumption. intros a H1 H2. exact (ROIMG a H2 H1).
  Qed.
End Spec.
