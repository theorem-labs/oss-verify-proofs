(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney MpiClient MpiClientX MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_lset U_mpi_grow U_mpi_copy U_mpi_core_bitlen U_mpi_core_bitlen_z U_mpi_core_exp_mod_working_limbs U_mpi_core_montmul U_mpi_core_montmul_init U_mpi_core_to_mont_rep U_mpi_core_from_mont_rep U_mpi_core_exp_mod U_mpi_core_check_zero_ct U_mpi_divmod_stmt U_mpi_exp_mod_stmt U_mpi_get_mont_r2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require SysStep.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_exp_mod () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.add_sub_mpi_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "EM.Walk.ALIAS"; "Corelib.Init.Datatypes.true"; "EM.Walk.es"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.nil"; "EM.Walk.frame"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.USpec.MpiClient.cstate"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.MOK"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_divmod_stmt.exp_mod_R"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "EM.Walk.rr_cells"; "RocqVerifyHarness.AgentSubmission.USpec.MpiClientX.mpd_cx"; "EM.Walk.rr_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Nat.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.U_ZEROIZE_AND_FREE"; "EM.Walk.tstate"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "EM.Walk.set_limbs"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_exp_mod_working_limbs.exp_mod_working_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"].


Definition U_ADD_SUB_MPI : Z := 0x20a04.

(* [comment removed for export] *)
Definition add_sub_mpi_stmt_e (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pflip,$0.P,(1.(2.$0.R1.+1.)(2.$0.R1.-1.))Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.Ph,(7.O5.O4.O3.)PLB,(8.$9.)PdX,$:.PdA,$:.PdB,$:.Plo,$0.P,(;.O5.O4.O3.R6.R5.R8.R7.)P,(<.O5.R9.R6.R5.)P,(<.O5.R:.R7.R5.)P,(<.O5.R;.R8.R5.)P,(=.R8.R7.)P,(=.R9.R7.)P,(=.R9.R8.)P,(>.(2.$?.(10.R;.)$11.))P,(12.R<.R;.R9.(13.&40.R2?.))P,(12.R=.R;.R:.(13.&40.R30.))P,(14.O4.R?.R;.(15.R=.)+10.)P,P,(2.$?.(10.R>.)$16.)(14.O4.R11.R=.(17.R?.)(18.+4.(19.R?.)))P,(14.O4.R11.R=.(15.R>.)+10.)P,P,(2.$?.(10.R?.)$16.)(14.O4.R13.R?.(17.R10.)(18.+4.(19.R10.)))P,(1:.O4.R13.(13.&40.R35.)(1;.O5.O4.O3.R14.)R12.)P,P,(>.(2.$?.(10.R13.)$1<.))(1.(1=.(1>.(17.R14.)(18.+4.(19.R14.)))R11.)(1=.(13.&40.R37.)(17.R14.)))P,(1?.O5.R18.R11.(13.&40.R37.))P,(1=.R12.(20.(20.(13.&40.R38.)+>0.)(21.O4.)))P,(1=.(22.O4.)R13.)P,(1=.(13.&40.R3:.)(1;.O5.O4.O3.R19.))P,(2.$0.(23.(13.&40.R3;.)+10.)=)P,(1=.(24.O4.)(22.O4.))P,(2.(3.&40.)R3;.(25.&40.(26.O4.)))P,(27.O5.R1?.)P,(28.O5.O4.R20.)P,(29.O4.O1.+8.)P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))(2:.O5.R24.(2;.O5.O4.O3.R45.R44.R43.R42.R3>.R3=.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.(2<.R47.R22.R21.R20.R1?.)R1>.R25.R24.)(2=.(2>.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.(25.&40.R47.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(25.&40.O2.)R26.(2?.(3.&40.))R25.(30.O5.)))")
(* [comment removed for export] *).

Section EM.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr usegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis HCBL : mpi_core_bitlen_stmt usegs U_MPI_CORE_BITLEN.
  Hypothesis HCBLZ : mpi_core_bitlen_z_stmt usegs U_MPI_CORE_BITLEN.
  Hypothesis HWL : mpi_core_exp_mod_working_limbs_stmt usegs U_MPI_CORE_EXP_MOD_WORKING_LIMBS.
  Hypothesis HLSET : mpi_lset_stmt usegs L HI U_MPI_LSET U_MEMSET_FUNC.
  Hypothesis HR2 : mpi_get_mont_r2_stmt usegs L HI U_MPI_GET_MONT_R2 U_MEMSET_FUNC.
  Hypothesis HZF : zeroize_and_free_stmt usegs L HI U_ZEROIZE_AND_FREE U_MEMSET_FUNC.
  Hypothesis HCOPY : mpi_copy_stmt usegs L HI U_MPI_COPY U_MEMSET_FUNC.
  Hypothesis HCMP : mpi_cmp_mpi_stmt usegs U_MPI_CMP_MPI.
  Hypothesis HMOD : mpi_mod_mpi_stmt usegs L HI U_MPI_MOD_MPI U_MEMSET_FUNC.
  Hypothesis HGROW : mpi_grow_stmt usegs L HI U_MPI_GROW U_MEMSET_FUNC.
  Hypothesis HMMI : mpi_core_montmul_init_stmt usegs U_MPI_CORE_MONTMUL_INIT.
  Hypothesis HTOM : mpi_core_to_mont_rep_stmt usegs U_MPI_CORE_TO_MONT_REP.
  Hypothesis HCEM : mpi_core_exp_mod_stmt usegs U_MPI_CORE_EXP_MOD.
  Hypothesis HFROM : mpi_core_from_mont_rep_stmt usegs U_MPI_CORE_FROM_MONT_REP.
  Hypothesis HCZ : mpi_core_check_zero_ct_stmt usegs U_MPI_CORE_CHECK_ZERO_CT.
  Hypothesis HAS : add_sub_mpi_stmt_e usegs L HI U_ADD_SUB_MPI U_MEMSET_FUNC.
  Hypothesis HCMPO : mpi_cmp_mpi_stmt_o usegs U_MPI_CMP_MPI.
  Hypothesis HMF : mpi_free_stmt usegs L HI U_MPI_FREE U_MEMSET_FUNC.

  Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dX dA dE dN : mpd) (lo : Z).
  Hypothesis HH0 : HEAP usegs L HI h LB m mo.
  Hypothesis MX0 : mpd_at usegs m LB dX.
  Hypothesis MA0 : mpd_at usegs m LB dA.
  Hypothesis ME0 : mpd_at usegs m LB dE.
  Hypothesis MN0 : mpd_at usegs m LB dN.
  Hypothesis NN : md_n dN <= 4999.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis SXE : mpd_sep dX dE.
  Hypothesis SXN : mpd_sep dX dN.
  Hypothesis NXE : md_addr dX <> md_addr dE.
  Hypothesis NXN : md_addr dX <> md_addr dN.
  Hypothesis NSX : md_own dX <> LStatic.
  Hypothesis OPA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OPE : opnd_sep dX dE lo (bv_unsigned sp).
  Hypothesis OPN : opnd_sep dX dN lo (bv_unsigned sp).
  Hypothesis CRA : client_range L LB lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L LB lo (md_p dA) (4 * md_n dA).
  Hypothesis CRE : client_range L LB lo (md_addr dE) 16.
  Hypothesis CREL : md_own dE = LHeap -> client_range L LB lo (md_p dE) (4 * md_n dE).
  Hypothesis CRN : client_range L LB lo (md_addr dN) 16.
  Hypothesis CRNL : md_own dN = LHeap -> client_range L LB lo (md_p dN) (4 * md_n dN).
  Hypothesis WRX : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dX.
  Hypothesis XLO : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX.
  Hypothesis ST0 : stk usegs m lo (bv_unsigned sp).
  Hypothesis SLO : lo <= bv_unsigned sp - 720 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv usegs m.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis SOK0 : statics_ok usegs L m.
  Hypothesis CA : const_at L U_MEMSET_FUNC 8.

  Notation SP := (bv_unsigned sp).
  Notation SPc := (SP + -112).
  Notation POST := (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX
    (exp_mod_R LB dX dA dE dN) lo m mo).

  (* [comment removed for export] *)
  Definition ALIAS : bool := Z.eqb (md_addr dX) (md_addr dA).
  Definition es : list mpd := if ALIAS then [dE; dN] else [dA; dE; dN].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L43782101083.98 L54965713378.2  L59314955108.100L65499856427.98 L774698616.98   00000>00E00`00j01JS2ra2sp2dX3SPBS1L3ACPS2ra2sp2dX2dA4HPOS3SPB2AL1ES2ra2sp2dXS1L3HLS2ra2sp2dX2lo3SLO4HPOS3SPB". (* [comment removed for export] *)
  Lemma facts0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "(31.(32.=(15.VdX,))(31.(2.$0.(23.(15.VdX,)+8.)=)(31.(1.(1=.(1>.(15.VdX,)+10.)Vlo,)(1=.(13.&40.Vsp,)(15.VdX,)))(31.P,(2.$?.(10.VdX,)$16.)(31.(33.(34.$0.$0.)(35.$0.$0.(17.VdX,)(18.+4.(19.VdX,)))VLB,)(1=.+1.(19.VdX,)))(31.(36.(34.$0.$0.)Lb,(34.$0.$0.)(37.VL,(38.$0.$0.R1.)(39.$0.$0.R1.))VLB,)(31.(32.=(22.VL,))(31.(32.(13.&40.Vsp,)(3:.+2.+40.))P,(2.$3;.$3<.$3=.)(2.$:.VdA,VdX,))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(MX0) 2%nat. intros FLt1 SG. flat constr:(FLt1) 6%nat. flclear FLt1. intros HR HAL HPOS HL HN HO.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros BR _. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(WRX) 3%nat. flclear WRX. intros WW1 WW2 WW3.
    split; [exact HPOS|]. split; [exact HAL|].
    split; [exact (client_wrange_where L _ _ _ _ 16 lo WW1 ltac:(lia) BR DHI ACL ltac:(lia))|].
    split. { intros O. rewrite O in HO. flat constr:(HO) 3%nat. flclear HO. intros N1 IN _. auto. }
    split; [exact BR|]. split; [clear -ACP; lia|]. split; [lia|].
    intros AL. unfold ALIAS in AL. apply Z.eqb_eq in AL. destruct SXA as [E|E]; [symmetry; exact E| exfalso; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma ESF_ok : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "(36.$:.Le,$:.(31.(14.VL,VLB,Vlo,(15.R1.)+10.)(31.P,(2.$?.(10.R1.)$16.)(33.(34.$0.$0.)(35.$0.$0.(17.R2.)(18.+4.(19.R2.)))VLB,)(31.(1.(1=.(1>.(15.R1.)+10.)Vlo,)(1=.(13.&40.Vsp,)(15.R1.)))(31.P,(2.$?.(10.VdX,)$16.)(1.(1=.(1>.(15.R2.)+10.)(17.VdX,))(1=.(1>.(17.VdX,)(18.+4.(19.VdX,)))(15.R2.)))(31.(1.(>.(2.$?.(10.VdX,)$16.))(1.(2.$?.(10.R1.)$1<.)(1.(1=.(1>.(17.VdX,)(18.+4.(19.VdX,)))(17.R1.))(1=.(1>.(17.R1.)(18.+4.(19.R1.)))(17.VdX,)))))(31.(1.(1=.(1>.(15.VdX,)+10.)(15.R1.))(1=.(1>.(15.R1.)+10.)(15.VdX,)))P,(>.(2.$?.(10.R1.)$1<.))(1.(1=.(1>.(15.VdX,)+10.)(17.R2.))(1=.(1>.(17.R2.)(18.+4.(19.R2.)))(15.VdX,)))))))))$3>.)")
(* [comment removed for export] *).
  Proof using L sp m LB dX dA dE dN lo MA0 ME0 MN0 SXA SXE SXN NXE NXN OPA OPE OPN CRA CRE CRN.
    unfold es, ALIAS.
    destruct (Z.eqb (md_addr dX) (md_addr dA)) eqn:alias_flag;
      [| apply Z.eqb_neq in alias_flag; apply Forall_cons];
      repeat apply Forall_cons; try apply Forall_nil.
    all: lazymatch goal with
         | |- client_range _ _ _ (md_addr ?e) _ /\ _ =>
           lazymatch goal with
           | at_e : mpd_at _ _ _ e, op_e : opnd_sep _ e _ _, sep_e : mpd_sep _ e,
             cr_e : client_range _ _ _ (md_addr e) _, ne_e : md_addr dX <> md_addr e |- _ =>
             pose proof op_e as (lim_e & limx_e & dis_e & strd_e & _);
             pose proof at_e as ((_ & _ & _ & _ & _ & own_e) & _);
             split; [exact cr_e|]; split;
             [intros heap_e; rewrite heap_e in own_e; exact (proj1 (proj2 own_e))|];
             split; [exact strd_e|]; split; [exact limx_e|];
             split; [destruct dis_e as [same|far]; [exfalso; apply ne_e; rewrite same; reflexivity| exact far]|];
             split; [destruct sep_e as [same|far]; [exfalso; apply ne_e; rewrite same; reflexivity| exact far]| exact lim_e]
           end
         end.
  Qed.

  Lemma opndA : In dA es \/ dA = dX.
  Proof. unfold es. destruct ALIAS eqn:AL; [right; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0)))))) AL)| left; left; reflexivity]. Qed.
  Lemma opndE : In dE es.
  Proof. unfold es. destruct ALIAS; [left; reflexivity| right; left; reflexivity]. Qed.
  Lemma opndN : In dN es.
  Proof. unfold es. destruct ALIAS; [right; left; reflexivity| right; right; left; reflexivity]. Qed.

  (* [comment removed for export] *)
  Notation CST := (cstate usegs L HI h LB mo m SP lo SPc dX es).
  Local Ltac mc_inst lem :=
    exact (lem usegs L HI HLS DIMG HND IMGC SW ROIMG h LB mo m SP lo SPc dX es ACL
             ltac:(clear - SLO HLS; lia) ltac:(clear - sp; lia) HTOP
             (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0))))))) DHI NSX WRX
             (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok).
  Definition mc_init := ltac:(mc_inst @cs_init).
  Definition mc_final := ltac:(mc_inst @cs_final).
  Definition mc_binop_l := ltac:(mc_inst @cs_binop_l).
  Definition mc_binop_w := ltac:(mc_inst @cs_binop_w).
  Definition mc_munch := ltac:(mc_inst @cs_munch).
  Definition mc_hi_write := ltac:(mc_inst @cs_hi_write).
  Definition mc_sign_w := ltac:(mc_inst @cs_sign_w).
  Definition mc_ex_alloc := ltac:(mc_inst @cs_ex_alloc).
  Definition mc_ex_free := ltac:(mc_inst @cs_ex_free).
  Definition mc_local_facts := ltac:(mc_inst @cs_local_facts).
  Definition mc_w_facts := ltac:(mc_inst @cs_w_facts).
  Definition mc_ext_facts := ltac:(mc_inst @cs_ext_facts).
  Definition mc_opnd_sep_le := ltac:(mc_inst @cs_opnd_sep_le).
  Definition mc_opnd_sep_we := ltac:(mc_inst @cs_opnd_sep_we).
  Definition mc_opnd_sep_ww := ltac:(mc_inst @cs_opnd_sep_ww).
  Definition mc_ivs_w := ltac:(mc_inst @cs_ivs_w).
  Definition mc_intro_local := ltac:(mc_inst @cs_intro_local).
  Definition mc_drop_local := ltac:(mc_inst @cs_drop_local).
  Definition mc_heap_nop0 := ltac:(mc_inst @cs_heap_nop0).
  (* [comment removed for export] *)
  Local Ltac mc_inst' lem :=
    exact (lem usegs L HI HLS DIMG HND IMGC SW ROIMG h LB SP lo SPc dX es ACL
             ltac:(clear - SLO HLS; lia) ltac:(clear - sp; lia) HTOP
             (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0))))))) DHI NSX WRX
             (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok).
  Definition mc_blocks_disjoint := ltac:(mc_inst' @blocks_disjoint).
  Definition mc_blocks_eq_or := ltac:(mc_inst' @blocks_eq_or).
  Definition mc_limbs_low := ltac:(mc_inst' @mpd_limbs_low).
  Definition set_limbs (d : mpd) (xs : list word) : mpd := mkMPD (md_addr d) (md_sg d) (md_n d) (md_p d) xs (md_pad d) (md_own d).

  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -112)).
  Notation RUN moq mq R pc := (aevtM usegs moq POST (MS R F (Z_to_bv 64 pc) fc None mq (seg_rom usegs))).
  Local Ltac dest_cs H :=
    (flat constr:(H) 21%nat; flclear H; intros HH HTc MF LOK SA LA MW WOK EXOK SUB COV FRS EXT PX SOK MI ST CH CHS CXH CXS).
  (* [comment removed for export] *)
  Notation REGS := ([C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).
  (* [comment removed for export] *)
  Definition frame (lo16 c16 : list cell) : list (Z * list cell) := [(SP + -112, lo16); (SP + -96, c16); (SP + -80, REGS)].

  Lemma frame_chs : forall lo16 c16, cells_size lo16 = 16%nat -> cells_size c16 = 16%nat ->
    Forall (fun ac : Z * list cell => SPc <= fst ac /\ fst ac + Z.of_nat (cells_size (snd ac)) <= SP /\
      (forall d : mpd, In d [] -> fst ac + Z.of_nat (cells_size (snd ac)) <= md_addr d \/ md_addr d + 16 <= fst ac)) (frame lo16 c16).
  Proof.
    intros lo16 c16 S1 S2. unfold frame. constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; rewrite ?S1, ?S2; cbn [cells_size csize Nat.add].
    all: split; [lia|]; split; [lia|]; intros d [].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma cs_parts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)PCS,(8.(34.$0.(8.$3?.)))PCX,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-70.)VdX,$3>.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(31.(;.$45.VL,VHI,R8.R7.R:.R9.)(31.(2.$0.(1;.$45.VL,VHI,R8.)(1;.$45.VL,VHI,Vh,))(31.(47.Vmo,R9.)(31.(28.$45.VL,R:.)(31.(27.$45.R:.)(31.(1?.$45.R:.Vlo,(1>.(13.&40.Vsp,)-70.))(31.(36.(34.$0.(8.$3?.))Lac,(34.$0.(8.$3?.))(48.$45.R;.(38.$0.(8.$3?.)R1.)(39.$0.(8.$3?.)R1.))R3.)(31.(36.(34.$0.(8.$3?.))Lac,(34.$0.(8.$3?.))(48.$45.R;.(38.$0.(8.$3?.)R1.)(39.$0.(8.$3?.)R1.))R2.)(49.R9.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros until CX. intros CS_. dest_cs CS_. split; [exact HH|]. split; [exact HTc|]. split; [exact MF|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split; [exact CH|]. split; [exact CXH| exact (heap_mok _ _ HI _ _ _ _ HH)].
  Qed.

  (* [comment removed for export] *)
  Lemma cs_frame : forall mq moq hq LBq ls dW EX lo16 c16 CX,
    CST mq moq hq LBq ls dW EX (frame lo16 c16) CX ->
    rw_cells usegs mq SPc lo16 /\ rw_cells usegs mq (SP + -96) c16 /\ rw_cells usegs mq (SP + -80) REGS.
  Proof.
    intros until CX. intros CS_. dest_cs CS_. unfold frame in CH.
    pose proof (Forall_inv CH) as C0. pose proof (Forall_inv (Forall_inv_tail CH)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as C2. cbn [fst snd] in C0, C1, C2.
    exact (conj C0 (conj C1 C2)).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24928467276.9300000?S2ra2sp1d2N12N0". (* [comment removed for export] *)
  Lemma out_heap : forall mq LBq d, mpd_at usegs mq LBq d -> md_own d <> LStatic -> 1 <= md_n d -> md_own d = LHeap.
  Proof using ra sp.
    intros mq LBq d at_d not_static pos_n.
    destruct at_d as ((_ & _ & _ & _ & _ & own_d) & _).
    destruct (md_own d); [| reflexivity| contradiction].
    destruct own_d as (_ & zero_n). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac binop_post PO m2 mo2 h2 LB2 d2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR :=
    (flat constr:(PO) 31%nat; flclear PO; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 d2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR);
    injection E as -> ->; rewrite ?unsigned_lit in ST2 by lia; rewrite ?unsigned_lit in PX2 by lia.

  Local Ltac reopen CS hh htc mf sok mi st mk :=
    try clear hh; try clear htc; try clear mf; try clear sok; try clear mi; try clear st; try clear mk;
    (flat constr:((cs_parts _ _ _ _ _ _ _ _ _ CS)) 9%nat; intros hh htc mf sok mi st _ _ mk).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_ret : forall mq moq hq LBq dW lo16 c16 (r : Z)
      (xra x0 x1 x2 x3 x4 x5 x6 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dW [] (frame lo16 c16) [] -> cells_size lo16 = 16%nat -> cells_size c16 = 16%nat -> -2^31 < r <= 0 ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 x0 x1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x21800.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP DHI.
    intros mq moq hq LBq dW lo16 c16 r xra x0 x1 x2 x3 x4 x5 x6 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 st sz_lo sz_c r_rng.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ st) as (fr_lo & fr_c & fr_regs).
    destruct (mc_final _ _ _ _ _ _ _ _ st (Forall_nil _))
      as (heap_f & top_f & frm_f & at_f & out_f & keep_f & presx_f & sok_f & inv_f & stk_f & _).
    assert (stk_top : stk usegs mq lo SP).
    { pose proof (stk_release _ _ _ _ _ stk_f fr_lo ltac:(lia)) as stk1.
      rewrite sz_lo in stk1. replace (SP + -112 + Z.of_nat 16) with (SP + -96) in stk1 by lia.
      pose proof (stk_release _ _ _ _ _ stk1 fr_c ltac:(lia)) as stk2.
      rewrite sz_c in stk2. replace (SP + -96 + Z.of_nat 16) with (SP + -80) in stk2 by lia.
      pose proof (stk_release _ _ _ _ _ stk2 fr_regs ltac:(lia)) as stk3.
      cbn [cells_size csize Nat.add] in stk3. replace (SP + -80 + Z.of_nat 80) with SP in stk3 by lia. exact stk3. }
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (_ & _ & _ & _ & _ & _ & _ & _ & mok_q).
    do 12 step.
    apply aevtM_done.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, mq, moq, hq, LBq, dW, r.
    split; [reflexivity|]. split; [exact inv_f|]. split; [exact stk_top|]. split; [exact frm_f|].
    split; [exact top_f|]. split; [exact heap_f|]. split; [exact at_f|]. split; [exact out_f|].
    split; [exact presx_f|]. split; [exact sok_f|]. split; [exact r_rng| exact keep_f].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rr_ok (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "(31.(2.$0.(15.O1.)(1>.(13.&40.Vsp,)-60.))(31.(2.$0.(42.(4>.(3.&40.)(4?.O1.)))(19.O1.))(31.(31.(1=.=(19.O1.))(1=.(19.O1.)$50.))(31.(>.(2.$?.(10.O1.)$11.))(31.(1.(2.$0.(51.O1.)+1.)(2.$0.(51.O1.)-1.))(31.P,(2.$?.(10.O1.)$1<.)(31.(2.$0.(17.O1.)=)(2.$0.(19.O1.)=))P,(2.$?.(10.O1.)$16.)(31.(1=.+1.(19.O1.))(31.(32.=(17.O1.))(31.(1=.(1>.(17.O1.)(18.+4.(19.O1.)))(22.VL,))(2.$0.(23.(17.O1.)+10.)=))))))))))")
(* [comment removed for export] *).
  Definition rr_cells (d : mpd) : list cell := mpi_cells (md_p d) (Z_to_bv 64 (md_sg d)) (md_n d) (md_pad d).

  Lemma rr_lift : forall mq moq hq LBq dW dR lo16,
    CST mq moq hq LBq [] dW (mpd_blk dR) (frame lo16 (rr_cells dR)) (mpd_cx dR) -> cells_size lo16 = 16%nat -> rr_ok dR ->
    CST mq moq hq LBq [dR] dW [] [(SP + -112, lo16); (SP + -80, REGS)] [] /\ mpd_at usegs mq LBq dR.
  Proof.
    intros mq moq hq LBq dW dR lo16 CS_ SZL RR.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(RR) 7%nat. flclear RR. intros EAR HLR HNR NSR SGR RN RH.
    dest_cs CS_. unfold frame in CH, CHS.
    pose proof (Forall_inv CH) as C0. pose proof (Forall_inv (Forall_inv_tail CH)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as C2. cbn [fst snd] in C0, C1, C2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CHS))) as S2. cbn [fst snd] in S2.
    assert (MDR : mpd_at usegs mq LBq dR).
    { split; [| exact SGR]. unfold mpi_at. split; [rewrite EAR; exact C1|].
      split; [rewrite EAR; clear - SPA; lia|]. split; [rewrite EAR; clear - SLO ACL ACP HLS; lia|].
      split; [exact HLR|]. split; [exact HNR|].
      destruct (md_own dR) eqn:OR; [exact (RN eq_refl)| | exfalso; exact (NSR eq_refl)].
      flat constr:((RH eq_refl)) 4%nat. intros N1 P0 P4 P16. split; [exact N1|].
      unfold mpd_blk in EXOK. rewrite OR in EXOK. destruct (Forall_inv EXOK) as (INR & _ & _ & _). split; [exact INR|]. split; [exact P16|].
      unfold mpd_cx in CXH. rewrite OR in CXH. pose proof (Forall_inv CXH) as CXR. cbn [fst snd] in CXR.
      eapply u32arr_of_cells; [exact CXR| reflexivity]. }
    split; [| exact MDR].
    split; [exact HH|]. split; [exact HTc|]. split; [exact MF|].
    split. { constructor; [| constructor]. split; [exact MDR|]. split; [exact NSR|]. rewrite EAR. split; [lia|]. split; [lia| clear - SPA; lia]. }
    split. { intros i j di dj Hi Hj NE. destruct i as [|[|i]]; destruct j as [|[|j]]; cbn in Hi, Hj; try discriminate. exfalso; apply NE; reflexivity. }
    split. { intros i j di dj Hi Hj NE. destruct i as [|[|i]]; destruct j as [|[|j]]; cbn in Hi, Hj; try discriminate. exfalso; apply NE; reflexivity. }
    split; [exact MW|].
    split.
    { destruct WOK as (X1 & X2 & X3 & WB & WK). split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split.
      - intros OW. destruct (WB OW) as (N1 & N2 & N3). split; [cbn [flat_map]; rewrite app_nil_r; exact N2|]. split; [intros []| exact N3].
      - intros b Hb0 Hbq. destruct (WK b Hb0 Hbq) as [E|[Hl|He]]; [left; exact E| cbn in Hl; destruct Hl| right; left; cbn [flat_map]; rewrite app_nil_r; exact He]. }
    split; [constructor|].
    split; [exact SUB|].
    split.
    { intros b Hb. destruct (COV b Hb) as [X|[X|[X|X]]]; [left; exact X| cbn in X; destruct X| right; right; left; exact X| right; left; cbn [flat_map]; rewrite app_nil_r; exact X]. }
    split. { intros b Hb HL. cbn [flat_map] in Hb. rewrite app_nil_r in Hb. destruct (proj1 (Forall_forall _ _) EXOK b Hb) as (_ & X2 & _). exact (X2 HL). }
    split; [exact EXT|]. split; [exact PX|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split; [constructor; [exact C0| constructor; [exact C2| constructor]]|].
    split.
    { constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - rewrite SZL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia|]. split; [lia|]. intros d [<-|[]]. rewrite EAR. left; lia.
      - destruct S2 as (B1 & B2 & _). split; [exact B1|]. split; [exact B2|]. intros d [<-|[]]. rewrite EAR. right; lia. }
    split; constructor.
  Qed.

  Lemma rr_perm : forall mq moq hq LBq dW lo16 c16,
    CST mq moq hq LBq [] dW [] ((SP + -96, c16) :: [(SP + -112, lo16); (SP + -80, REGS)]) [] ->
    CST mq moq hq LBq [] dW [] (frame lo16 c16) [].
  Proof.
    intros mq moq hq LBq dW lo16 c16 CS_. dest_cs CS_.
    split; [exact HH|]. split; [exact HTc|]. split; [exact MF|]. split; [exact LOK|]. split; [exact SA|]. split; [exact LA|].
    split; [exact MW|]. split; [exact WOK|]. split; [exact EXOK|]. split; [exact SUB|]. split; [exact COV|]. split; [exact FRS|].
    split; [exact EXT|]. split; [exact PX|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split.
    { unfold frame. pose proof (Forall_inv CH) as C0. pose proof (Forall_inv (Forall_inv_tail CH)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as C2.
      constructor; [exact C1| constructor; [exact C0| constructor; [exact C2| constructor]]]. }
    split.
    { unfold frame. pose proof (Forall_inv CHS) as C0. pose proof (Forall_inv (Forall_inv_tail CHS)) as C1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CHS))) as C2.
      constructor; [exact C1| constructor; [exact C0| constructor; [exact C2| constructor]]]. }
    split; [exact CXH| exact CXS].
  Qed.

  Definition mc_free_local := ltac:(mc_inst @cs_free_local).

  (* [comment removed for export] *)
  Lemma L_clean2 : forall mq moq hq LBq dW dR lo16 (r : Z)
      (xra x0 x1 x2 x3 x4 x5 x6 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dW (mpd_blk dR) (frame lo16 (rr_cells dR)) (mpd_cx dR) -> cells_size lo16 = 16%nat -> rr_ok dR -> -2^31 < r <= 0 ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 x0 x1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x21a14.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR lo16 r xra x0 x1 x2 x3 x4 x5 x6 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 st sz_lo rr_d r_rng.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    destruct (rr_lift _ _ _ _ _ _ _ st sz_lo rr_d) as (st1 & at_r).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st1) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    pose proof rr_d as (addr_r & len_r & rng_r & ns_r & sg_r & null_r & heap_r).
    step. step. step.
    eapply aevtM_cut.
    { eapply (HMF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq (md_addr dR) (Z_to_bv 64 (md_sg dR)) (md_n dR) (md_p dR) (md_limbs dR) (md_pad dR) (md_own dR) lo).
      all: try rewrite spf_val.
      - exact heap_q.
      - exact (proj1 at_r).
      - exact ns_r.
      - apply client_wrange_stack; lia.
      - intros own_h. right. destruct (heap_r own_h) as (_ & _ & lim_r & _). lia.
      - intros a in_a in_data. exfalso. lia.
      - exact stk_q.
      - lia.
      - exact ACL.
      - lia.
      - lia.
      - exact DHI.
      - exact TP.
      - exact inv_q.
      - exact sok_q.
      - exact CA.
      - rewrite addr_r. reflexivity. }
    intros ms' mo' post.
    destruct post as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & mo2 & h2
                      & cfg_eq & inv2 & stk2 & frm2 & top2 & heap2 & cell2 & presx2 & sok2).
    injection cfg_eq as -> ->.
    rewrite spf_val in stk2, presx2.
    pose proof (mc_free_local _ _ _ _ _ _ _ _ _ 0%nat dR m2 mo2 h2 (md_pad dR) st1 eq_refl heap2 top2 frm2 presx2 sok2 inv2 stk2 cell2) as st2.
    cbn [set_nth] in st2.
    pose proof (proj1 (mc_drop_local _ _ _ _ _ _ _ _ _ _ st2)) as st3.
    cbn [app mpd_blk mpd_cx mpd_struct md_own md_addr md_p md_sg md_n md_pad] in st3.
    rewrite addr_r in st3. apply rr_perm in st3.
    rewrite ret_pc_even by (cbn; lia).
    pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
    step. step.
    eapply L_ret; [exact st3| exact sz_lo| reflexivity| exact r_rng].
  Qed.

  Lemma call_zf_T : forall (RET : Z) mq moq hq LBq dW lo16 cR dR (T tl : Z) (ts : list word)
      (x0 x1 x2 x3 x4 x5 x6 x7 x8 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dW ((T, 4 * tl) :: mpd_blk dR) (frame lo16 cR) ((T, [CB (4 * length ts)%nat (u32s ts)]) :: mpd_cx dR) ->
    cells_size lo16 = 16%nat -> cells_size cR = 16%nat -> Z.of_nat (length ts) = tl -> ~ In (T, 4 * tl) (mpd_blk dR) ->
    0 <= RET < 2^64 -> RET mod 2 = 0 -> rr_ok dR ->
    (forall m' mo' h' LB' (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : word),
       CST m' mo' h' LB' [] dW (mpd_blk dR) (frame lo16 cR) (mpd_cx dR) ->
       RUN mo' m' (mkR (Z_to_bv 64 RET) SPF gp tp y0 y1 y2 x0 x1 y3 y4 y5 y6 y7 y8 y9 y10 x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 y11 y12 y13 y14) RET) ->
    RUN moq mq (mkR (Z_to_bv 64 RET) SPF gp tp t0 t1 t2 x0 x1 (Z_to_bv 64 T) (Z_to_bv 64 (4 * tl)) a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 s9 s10 s11 t3 t4 t5 t6) U_ZEROIZE_AND_FREE.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros RET mq moq hq LBq dW lo16 cR dR T tl ts x0 x1 x2 x3 x4 x5 x6 x7 x8 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      st sz_lo sz_c len_ts t_fresh ret_rng ret_even rr_d cont.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    pose proof st as (heap_q & top_q & frm_q & _ & _ & _ & _ & _ & exok_q & _ & _ & _ & _ & _ & sok_q & inv_q & stk_q & _ & _ & cxh_q & cxs_q).
    pose proof (Forall_inv exok_q) as (t_in & _ & _ & t_pos).
    pose proof (Forall_inv cxh_q) as t_cells. cbn [fst snd] in t_cells, t_pos.
    pose proof (proj1 (Forall_forall _ _) (proj1 (heap_blocks _ _ HI _ _ _ _ heap_q)) _ t_in) as (t_gt0 & _ & _ & t_lim & _).
    cbn [fst snd] in t_gt0, t_lim.
    assert (t_size : Z.to_nat (4 * tl) = (4 * length ts)%nat) by lia.
    rewrite <- t_size in t_cells.
    eapply aevtM_cut.
    { eapply (HZF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq T (4 * tl) lo (u32s ts)).
      all: try rewrite spf_val.
      - exact heap_q.
      - right. exact (conj t_in t_cells).
      - lia.
      - exact stk_q.
      - lia.
      - exact ACL.
      - lia.
      - lia.
      - exact DHI.
      - exact TP.
      - exact inv_q.
      - exact sok_q.
      - exact CA.
      - reflexivity.
      - reflexivity. }
    intros ms' mo' post.
    destruct post as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & mo2 & h2
                      & cfg_eq & inv2 & stk2 & frm2 & top2 & heap2 & presx2 & sok2).
    injection cfg_eq as -> ->.
    rewrite spf_val in stk2, presx2.
    assert (cx_sub : Forall (fun ac : Z * list cell => In ac ((T, [CB (4 * length ts)%nat (u32s ts)]) :: mpd_cx dR)) (mpd_cx dR)).
    { apply Forall_forall. intros ac ac_in. right. exact ac_in. }
    assert (cx_in : Forall (fun ac : Z * list cell => exists B : Z * Z, In B (mpd_blk dR) /\ fst B <= fst ac /\ fst ac + Z.of_nat (cells_size (snd ac)) <= fst B + snd B) (mpd_cx dR)).
    { unfold mpd_cx, mpd_blk. destruct (md_own dR); try apply Forall_nil.
      apply Forall_cons; [| apply Forall_nil].
      exists (md_p dR, 4 * md_n dR). split; [left; reflexivity|]. cbn [fst snd cells_size csize Nat.add].
      destruct rr_d as (_ & len_r & _). lia. }
    pose proof (mc_ex_free _ _ _ _ _ _ _ _ _ _ _ m2 mo2 h2 T (4 * tl) st eq_refl t_fresh heap2 top2 frm2 presx2 sok2 inv2 stk2 cx_sub cx_in) as st2.
    rewrite ret_pc_even by lia.
    eapply cont. exact st2.
  Qed.

  Definition tstate (mq : mem) (moq : Model) (hq : HST usegs L HI) (LBq : list blk) (dW dR : mpd) (T tl : Z) (ts : list word) : Prop :=
    exists lo16, cells_size lo16 = 16%nat
      /\ CST mq moq hq LBq [] dW ((T, 4 * tl) :: mpd_blk dR) (frame lo16 (rr_cells dR)) ((T, [CB (4 * length ts)%nat (u32s ts)]) :: mpd_cx dR)
      /\ rr_ok dR /\ Z.of_nat (length ts) = tl /\ ~ In (T, 4 * tl) (mpd_blk dR).

  Lemma L_clean1 : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word) (r : Z)
      (xra x2 x3 x4 x7 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> -2^31 < r <= 0 ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 r) a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 tl) (Z_to_bv 64 T) x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x2193c.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts r xra x2 x3 x4 x7 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st r_rng.
    destruct ts_st as (lo16 & sz_lo & st & rr_d & len_ts & t_fresh).
    pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    pose proof st as (heap_q & _ & _ & _ & _ & _ & _ & _ & exok_q & _).
    pose proof (proj1 (Forall_forall _ _) (proj1 (heap_blocks _ _ HI _ _ _ _ heap_q)) _ (proj1 (Forall_inv exok_q)))
      as (t_gt0 & _ & _ & t_lim & _).
    cbn [fst snd] in t_gt0, t_lim.
    pose proof (heap_mok _ _ HI _ _ _ _ heap_q) as mok_q.
    step. step. step.
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 tl) ≪ 2)) with (Z_to_bv 64 (4 * tl))
      by (rewrite unsigned_lit, Z.shiftl_mul_pow2 by lia; f_equal; lia).
    eapply (call_zf_T 0x21948); [exact st| exact sz_lo| reflexivity| exact len_ts| exact t_fresh| lia| reflexivity| exact rr_d|].
    intros m' mo' h' LB' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 st'.
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st') as (_ & _ & _ & _ & _ & _ & _ & _ & mok').
    step. if_true. step.
    eapply L_clean2; [exact st'| exact sz_lo| exact rr_d| exact r_rng].
  Qed.

  Lemma L_clean1' : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word) (r : Z)
      (xra x1 x2 x3 x4 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> -2^31 < r <= 0 ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) x1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 tl) (Z_to_bv 64 T) x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x21938.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts r xra x1 x2 x3 x4 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st r_rng.
    pose proof ts_st as (lo16 & _ & st & _).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (_ & _ & _ & _ & _ & _ & _ & _ & mok_q).
    step.
    eapply L_clean1; [exact ts_st| exact r_rng].
  Qed.

  Lemma L_r2fail : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word) (r : Z)
      (xra x0 x1 x2 x3 x4 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> -2^31 < r <= 0 ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 x0 x1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 tl) (Z_to_bv 64 T) x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x218d8.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts r xra x0 x1 x2 x3 x4 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st r_rng.
    destruct ts_st as (lo16 & sz_lo & st & rr_d & len_ts & t_fresh).
    pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    pose proof st as (heap_q & _ & _ & _ & _ & _ & _ & _ & exok_q & _).
    pose proof (proj1 (Forall_forall _ _) (proj1 (heap_blocks _ _ HI _ _ _ _ heap_q)) _ (proj1 (Forall_inv exok_q)))
      as (t_gt0 & _ & _ & t_lim & _).
    cbn [fst snd] in t_gt0, t_lim.
    pose proof (heap_mok _ _ HI _ _ _ _ heap_q) as mok_q.
    step. step. step. step.
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 tl) ≪ 2)) with (Z_to_bv 64 (4 * tl))
      by (rewrite unsigned_lit, Z.shiftl_mul_pow2 by lia; f_equal; lia).
    eapply (call_zf_T 0x218e8); [exact st| exact sz_lo| reflexivity| exact len_ts| exact t_fresh| lia| reflexivity| exact rr_d|].
    intros m' mo' h' LB' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 st'.
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st') as (_ & _ & _ & _ & _ & _ & _ & _ & mok').
    step. step.
    eapply L_clean2; [exact st'| exact sz_lo| exact rr_d| exact r_rng].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma blk_apart : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pb1,$9.Pb2,$9.P,(;.$45.VL,VHI,R4.R3.R6.R5.)P,(33.$9.R3.R4.)P,(33.$9.R3.R5.)P,(>.(2.$9.R5.R4.))P,(32.=(39.$0.$0.R6.))P,(32.=(39.$0.$0.R6.))(1.(1=.(1>.(38.$0.$0.R8.)(39.$0.$0.R8.))(38.$0.$0.R7.))(1=.(1>.(38.$0.$0.R7.)(39.$0.$0.R7.))(38.$0.$0.R8.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq [B1 k1] [B2 k2] HH I1 I2 NE P1 P2. cbn in P1, P2 |- *.
    destruct (mc_blocks_eq_or _ _ _ _ _ _ HH I1 I2) as [E|NF]; [exfalso; exact (NE E)|]. cbn in NF.
    exact (mc_blocks_disjoint _ _ _ _ _ _ _ _ HH I1 I2 NF P1 P2).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L14252600409.184L14965883667.8  L16423634115.164L19596999701.161L19611939464.163L21921507852.164L28559306520.164L30618270697.2  L41200638159.162L41200639311.163L42718512692.161L42718954033.187L42729262377.162L48737075761.11 L51163452409.2  L59308731643.185L59310643408.7  L59310646096.184L6130122125.3   L8927147937.11  L9220441234.187 00000K00`01601[02@02V03=03D03Y03n04F04`05805_05f06@06R06i07107X08?S2ra2sp2dW2dR1T2ts1e2N03NE1S1L1T2tl4TIMG1e2R02R1S2ra2sp2dW2dR1T2ts3HNWS2ra2sp2dW2dR1T2ts3SPB3PR03NW13PW02T0S2ra2sp2dW2dR1T2ts3SPB3PR03NW13PW02T0S2ra2sp2dW2dR1T2ts3HNRS2ra2sp2dW2dR1T2tl2ts3SPB3PR03PW02KT2T0S1e3NE1S2ra2sp2dW2dR1T2ts2KRS2ra2sp2dW2dR1T2ts2KRS2ra2sp2dW2dR1T2tl2ts2KTS2ra2sp2dW2dR1T2tl2ts2KT1eS2ra2sp2dW2dR1T2tl2ts2KTS1L3HLS2sp2lo3SLO3ACL3SPB1e3PE03PE43NE1S1e3NE1S2ra2sp2dX2dW2dR1T2ts1e2AXS2dX1e1C2E12E23N01S2ra2sp2dW2dR1T2ts1e2APS2dW1e1XS1L3HLS2sp2lo3SLO3ACL3SPB1e3PE03PE43NE1S2ra2sp2dW2dR1T2ts3SPB3PR03PW02T01e3NE1". (* [comment removed for export] *)
  Lemma t_facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))P,(5:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(2.$?.(10.R6.)$16.)P,(2.$?.(10.R6.)$16.)(31.(31.(32.=(17.R8.))(31.(1=.(1>.(17.R8.)(18.+4.(19.R8.)))(22.VL,))(31.(2.$0.(23.(17.R8.)+10.)=)(31.(1=.+1.(19.R8.))(31.(2.$0.(42.(4>.(3.&40.)(4?.R8.)))(19.R8.))(1=.(19.R8.)$50.))))))(31.(31.(32.=R6.)(31.(1=.(1>.R6.(18.+4.R5.))(22.VL,))(31.(2.$0.(23.R6.+10.)=)(31.(32.=R5.)(1.(1=.(1>.R6.(18.+4.R5.))(5;.VL,))(1=.(5<.VL,)R6.))))))(31.(31.(32.=(17.R7.))(31.(1=.(1>.(17.R7.)(18.+4.(19.R7.)))(22.VL,))(31.(2.$0.(23.(17.R7.)+10.)=)(31.(1=.+1.(19.R7.))(31.(2.$0.(42.(4>.(3.&40.)(4?.R7.)))(19.R7.))(1=.(19.R7.)$50.))))))(31.(1.(1=.(1>.(17.R8.)(18.+4.(19.R8.)))R6.)(1=.(1>.R6.(18.+4.R5.))(17.R8.)))(31.(1.(1=.(1>.(17.R7.)(18.+4.(19.R7.)))R6.)(1=.(1>.R6.(18.+4.R5.))(17.R7.)))(31.(1.(1=.(1>.(17.R8.)(18.+4.(19.R8.)))(17.R7.))(1=.(1>.(17.R7.)(18.+4.(19.R7.)))(17.R8.)))Pe,$:.P,(33.$:.R1.$3>.)P,(>.(2.$?.(10.R2.)$1<.))(31.(1.(1=.(1>.(17.R3.)(18.+4.(19.R3.)))R9.)(1=.(1>.R9.(18.+4.R8.))(17.R3.)))(31.(1.(1=.(1>.(17.R3.)(18.+4.(19.R3.)))(17.R;.))(1=.(1>.(17.R;.)(18.+4.(19.R;.)))(17.R3.)))(31.(32.=(17.R3.))(31.(1=.(1>.(17.R3.)(18.+4.(19.R3.)))(22.VL,))(31.(2.$0.(23.(17.R3.)+4.)=)(1=.+1.(19.R3.)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until ts. intros (lo16 & SZ & CS_ & RR & TL & NIN) OW OR. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(RR) 7%nat. intros EAR HLR HNR NSR SGR RN RH. flat constr:((RH OR)) 4%nat. intros NR1 PR0 PR4 PALR.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 9%nat. intros FLt3 NSW EA _ LW _ _ HFW _. flat constr:(FLt3) 2%nat. flclear FLt3. intros FLt4 _. flat constr:(FLt4) 6%nat. flclear FLt4. intros _ _ _ HLW HNW HOW.
    pose proof HOW as HOW'. rewrite OW in HOW'. flat constr:(HOW') 4%nat. flclear HOW'. intros NW1 _ PALW _. flat constr:((HFW OW)) 4%nat. intros PW0 PW4 INW _.
    pose proof CS_ as CS2. dest_cs CS2. flat constr:(WOK) 5%nat. flclear WOK. intros _ _ _ WB _. flat constr:((WB OW)) 3%nat. intros WNL WNE WLB.
    flat constr:((Forall_inv EXOK)) 4%nat. intros INT TLB _ KT. cbn [snd] in KT.
    unfold mpd_blk in EXOK, NIN. rewrite OR in EXOK, NIN. flat constr:((Forall_inv (Forall_inv_tail EXOK))) 4%nat. intros INR RLB _ KR. cbn [snd] in KR.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BR _. flat constr:((proj1 (Forall_forall _ _) BR _ INT)) 5%nat. intros T0 TAL _ T4 TIMG. cbn in T0, TAL, T4, TIMG.
    assert (DWT : md_p dW + 4 * md_n dW <= T \/ T + 4 * tl <= md_p dW).
    { exact (blk_apart _ _ _ _ (md_p dW, 4 * md_n dW) (T, 4 * tl) HH INW INT ltac:(intros E; apply WNE; rewrite E; left; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
    assert (DRT : md_p dR + 4 * md_n dR <= T \/ T + 4 * tl <= md_p dR).
    { exact (blk_apart _ _ _ _ (md_p dR, 4 * md_n dR) (T, 4 * tl) HH INR INT ltac:(intros E; apply NIN; rewrite E; left; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
    assert (DWR : md_p dW + 4 * md_n dW <= md_p dR \/ md_p dR + 4 * md_n dR <= md_p dW).
    { exact (blk_apart _ _ _ _ (md_p dW, 4 * md_n dW) (md_p dR, 4 * md_n dR) HH INW INR ltac:(intros E; apply WNE; rewrite E; unfold mpd_blk; rewrite OR; right; left; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
    unfold MPI_MAX_LIMBS in *.
    split; [split; [exact PW0| split; [exact PW4| split; [exact PALW| split; [exact NW1| split; [exact HLW| lia]]]]]|].
    split; [split; [exact T0| split; [exact T4| split; [exact TAL| split; [lia| exact TIMG]]]]|].
    split; [split; [exact PR0| split; [exact PR4| split; [exact PALR| split; [exact NR1| split; [exact HLR| lia]]]]]|].
    split; [exact DWT|]. split; [exact DRT|]. split; [exact DWR|].
    intros e He NNe.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ e CS_ He)) 6%nat. intros ME _ _ _ HFE _.
    flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ e CS_ He)) 2%nat. intros SWE FLt5. flat constr:(FLt5) 5%nat. flclear FLt5. intros O1 O2 O3 O4 O5.
    flat constr:((proj1 (Forall_forall _ _) ESF_ok e He)) 7%nat. intros _ _ _ _ AWL AWA _.
    destruct (mpd_raw _ _ _ _ ME ltac:(intros O; exact (proj1 (HFE O)))) as (_ & _ & HLE & HNE & _ & _ & PBE).
    flat constr:((mc_limbs_low _ _ _ _ _ HH ME NNe)) 2%nat. intros PE0 PE4.
    flat constr:(ME) 2%nat. intros FLt6 _. flat constr:(FLt6) 6%nat. flclear FLt6. intros _ _ _ _ _ HOE.
    assert (NE1 : 1 <= md_n e) by (destruct (md_own e); [exfalso; exact (NNe eq_refl)| exact (proj1 HOE)| exact (proj1 HOE)]).
    split; [| split; [| split; [exact PE0| split; [exact PE4| split; [destruct PBE as [N0|[_ P4]]; [lia| exact P4]| exact NE1]]]]].
    - destruct (md_own e) eqn:OE; [exfalso; exact (NNe eq_refl)| |].
      + flat constr:((HFE eq_refl)) 4%nat. intros _ INE INEL _.
        refine (blk_apart _ _ _ _ (md_p e, 4 * md_n e) (T, 4 * tl) HH INE INT _ ltac:(cbn; lia) ltac:(cbn; lia)).
        intros E. rewrite <- E in TLB. pose proof (TLB INEL) as HX0. flat constr:((mpd_blk_heap _ _ HX0)) 2%nat. intros O0 E0. injection E0 as E1 E2.
        destruct AWL as [C|[C|C]]; [exact (C O0)| discriminate C|]. flat constr:((proj1 (proj2 (proj2 (proj2 facts0))) O0)) 2%nat. intros _ N01. first [clear - E1 E2 N01 NE1 C; lia| plia| lia].
      + flat constr:(HOE) 5%nat. flclear HOE. intros _ _ _ _ ROE.
        assert (B0 : 0 <= md_p e + 0 < 2 ^ 64) by (clear - PE0 PE4 ACL SLO SPB HLS NE1; lia).
        assert (I0 : 0 <= 0 < 4 * md_n e) by (clear - NE1; lia). assert (I1 : 0 <= 4 * md_n e - 1 < 4 * md_n e) by (clear - NE1; lia).
        assert (B1 : 0 <= md_p e + (4 * md_n e - 1) < 2 ^ 64) by (clear - PE0 PE4 ACL SLO SPB HLS NE1; lia).
        pose proof (ROIMG _ B0 (ROE 0 I0)) as R0. pose proof (ROIMG _ B1 (ROE (4 * md_n e - 1) I1)) as R1. clear - R0 R1 TIMG NE1. lia.
    - destruct O3 as [E|[X|[X|X]]]; [| rewrite OW in X; exfalso; exact (X eq_refl)| exfalso; exact (NNe X)| clear - X; lia].
      exfalso. destruct SWE as [E'|AP]; [| rewrite E in AP; lia]. flat constr:((proj1 (Forall_forall _ _) ESF_ok e He)) 7%nat. intros _ _ _ _ _ AX _. rewrite <- E, EA in AX. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w_cells : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)PCS,(8.(34.$0.(8.$3?.)))PCX,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-70.)VdX,$3>.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(31.(48.$45.R:.(15.VdX,)(5=.(17.R5.)(25.&40.(51.R5.))(19.R5.)(5>.R5.)))(31.(1.(2.$0.(51.R5.)+1.)(2.$0.(51.R5.)-1.))(31.(2.$0.(42.(4>.(3.&40.)(4?.R5.)))(19.R5.))(31.(31.(1=.=(19.R5.))(1=.(19.R5.)$50.))(2.$0.(15.R5.)(15.VdX,))))))")
(* [comment removed for export] *).
  Proof.
    intros until CX. intros CS_. flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 4%nat. intros FLt7 _ EA _. flat constr:(FLt7) 2%nat. flclear FLt7. intros FLt8 SG. flat constr:(FLt8) 6%nat. flclear FLt8. intros HR _ _ HL HN _. rewrite <- EA. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma a_cells : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)PCS,(8.(34.$0.(8.$3?.)))PCX,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-70.)VdX,$3>.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(5?.$0.Lp,$0.(5?.$0.Lsg,$0.(5?.$0.Ln,$0.(5?.(3.&40.)Lpad,(3.&40.)(31.(48.$45.R>.(15.VdA,)(5=.R4.(25.&40.R3.)R2.R1.))(1.(2.$0.R3.+1.)(2.$0.R3.-1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros until CX. intros CS_. destruct opndA as [IN| E].
    - flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ _ CS_ IN)) 2%nat. intros ((HR & _) & SG) _. do 4 eexists. exact (conj HR SG).
    - rewrite E. flat constr:((w_cells _ _ _ _ _ _ _ _ _ CS_)) 3%nat. intros HR SG _. do 4 eexists. exact (conj HR SG).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L60513437445.129L60856962093.12900000F00OS1L3HLS2ra2sp2lo3SLO1eS2ra2sp1e". (* [comment removed for export] *)
  Lemma e_raw : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)PCS,(8.(34.$0.(8.$3?.)))PCX,(8.(34.$0.(8.$3?.)))Pe,$:.P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-70.)VdX,$3>.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(33.$:.R2.$3>.)(31.(48.$45.R<.(15.R3.)(5=.(17.R3.)(25.&40.(51.R3.))(19.R3.)(5>.R3.)))(31.(60.$45.R<.(17.R3.)(58.(4?.R3.)))(31.(2.$0.(42.(4>.(3.&40.)(4?.R3.)))(19.R3.))(31.(31.(1=.=(19.R3.))(1=.(19.R3.)+2710.))(31.(1.(2.$0.(51.R3.)+1.)(2.$0.(51.R3.)-1.))(31.(1.(2.$0.(19.R3.)=)(31.(32.=(17.R3.))(2.$0.(23.(17.R3.)+4.)=)))(31.P,(>.(2.$?.(10.R3.)$1<.))(31.(32.=(17.R4.))(31.(1=.(1>.(17.R4.)(18.+4.(19.R4.)))(22.VL,))(1=.+1.(19.R4.))))P,(2.$?.(10.R3.)$1<.)(31.(2.$0.(17.R4.)=)(2.$0.(19.R4.)=)))))))))")
(* [comment removed for export] *).
  Proof using L HI HLS SW DIMG HND ROIMG IMGC ra sp m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP DHI.
    intros mq moq hq LBq ls dW EX CS CX e st e_in.
    pose proof (mc_ext_facts _ _ _ _ _ _ _ _ _ _ st e_in) as (at_e & _ & _ & _ & heap_e & _).
    pose proof st as (heap_q & _).
    destruct (mpd_raw _ _ _ _ at_e (fun o => proj1 (heap_e o))) as (_ & bytes_e & len_e & rng_e & sg_e & _ & pz_e).
    pose proof at_e as ((cells_e & _ & _ & _ & _ & own_e) & _).
    split; [exact cells_e|]. split; [exact bytes_e|]. split; [exact len_e|]. split; [exact rng_e|].
    split; [exact sg_e|]. split; [exact pz_e|].
    split.
    - intros not_null. destruct (mc_limbs_low _ _ _ _ _ heap_q at_e not_null) as (p_pos & p_lim).
      split; [exact p_pos|]. split; [exact p_lim|].
      destruct (md_own e); [contradiction| exact (proj1 own_e)| exact (proj1 own_e)].
    - intros is_null. rewrite is_null in own_e. exact own_e.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L2416225489.6   L28625184349.4  L28625516220.4  L40377502679.5  L55344112009.6  L61039157933.9  L65476495129.3  L66096060529.14400000B00N00Y00g01901T01_02<S2dR1T2tl1k2Hk3DRTS1T2tl2ts2TLS1T2tl1k2HkS2sp2lo1K4HKloS2dW2dR2an3Han3DWRS1L2sp2lo3ACL2dR1K4HKlo3PR4S2dW2an3HanS2ra2sp2dW2dR1T2ts3xs'3ts'2LT". (* [comment removed for export] *)
  Lemma core_munch : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pm2,P,(3.&40.)(5.(3.&8.))Pan,$0.Pk,$0.PK,$0.Pxs',(8.(3.&40.))Pts',(8.(3.&40.))P,(5:.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(2.$?.(10.R<.)$16.)P,(2.$?.(10.R<.)$16.)P,(61.(4:.(34.$0.$0.)(35.$0.$0.(17.R>.)(1>.(17.R>.)(18.+4.R8.)))(4:.(34.$0.$0.)(35.$0.$0.R<.(1>.R<.(18.+4.R7.)))(4:.(34.$0.$0.)(35.$0.$0.(20.(1>.(13.&40.Vsp,)-70.)R6.)(1>.(13.&40.Vsp,)-70.))(43.(34.$0.$0.)))))R12.R9.)P,(62.$45.R13.R:.)P,(27.$45.R;.)P,(1?.$45.R<.Vlo,(1>.(13.&40.Vsp,)-70.))P,(31.(1=.=R<.)(1=.R<.(19.R12.)))P,(31.(1=.=R<.)(1=.R<.R10.))P,(1=.=R<.)P,(1=.Vlo,(20.(1>.(13.&40.Vsp,)-70.)R=.))P,(63.$45.R11.(17.R16.)R=.)P,(2.$0.(42.(4>.(3.&40.)R>.))(19.R17.))P,(63.$45.R13.R16.R>.)P,(2.$40.(4>.(3.&40.)R?.)(4>.(3.&40.)R15.))(5:.R15.R1=.R1<.R1;.(64.R1:.R11.)R19.R18.R17.R10.)")
(* [comment removed for export] *).
  Proof.
    intros until ts'. intros TS OW OR MU WM MI2 ST2 Han Hk HK HKlo UX LX UT LT.
    flat constr:((t_facts _ _ _ _ _ _ _ _ _ TS OW OR)) 7%nat. intros FLt10 FLt11 FLt12 DWT DRT DWR EF. flat constr:(FLt10) 6%nat. flclear FLt10. intros PW0 PW4 PALW NW1 HLW HNW. flat constr:(FLt11) 5%nat. flclear FLt11. intros T0 T4 TAL TL0 TIMG. flat constr:(FLt12) 6%nat. flclear FLt12. intros PR0 PR4 PALR NR1 HLR HNR.
    destruct TS as (lo16 & SZ & CS_ & RR & TL & NIN). pose proof alloc_ceiling_pos as ACP.
    pose proof CS_ as CS2. flat constr:(CS2) 21%nat. flclear CS2. intros _ _ _ _ _ _ _ _ EXOK _ _ _ _ _ _ _ _ _ _ CXH _.
    unfold mpd_cx in CXH. rewrite OR in CXH. pose proof (Forall_inv (Forall_inv_tail CXH)) as CXR. cbn [fst snd] in CXR.
    exists lo16. split; [exact SZ|]. split; [| split; [exact RR| split; [rewrite <- TL, LT; reflexivity| exact NIN]]].
    eapply (mc_munch _ _ _ _ _ _ _ _ _ None true true); [exact CS_| exact MU| exact WM| exact MI2| exact ST2| | reflexivity| intros j d d' Hj; destruct j; discriminate Hj| | intros C; discriminate C|].
    - constructor; [| constructor; [| constructor; [| constructor]]]; unfold w_ok; cbn [fst snd].
      + right; right; left. split; [reflexivity|]. split; [exact OW|]. clear - Han; lia.
      + right; right; right. split; [reflexivity|]. exists (T, 4 * tl). split; [left; reflexivity|]. cbn [fst snd]. clear - Hk; lia.
      + left. clear - HK HKlo; lia.
    - cbn [set_limbs md_addr md_sg md_n md_p md_pad md_own md_limbs]. do 6 (split; [reflexivity|]). split.
      + intros C. exfalso. apply C. split; [reflexivity| exact OW].
      + intros _ _. split; [exact UX| exact LX].
    - intros _. split.
      + constructor; [cbn [fst snd]; apply u32arr_cells; exact UT|]. unfold mpd_cx. rewrite OR. constructor; [| constructor]. cbn [fst snd].
        eapply rw_cells_transport; [exact CXR| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. cbn. rewrite <- HLR in *.
        split; [clear - DWR Han HLW; lia|]. split; [clear - DRT Hk; lia|]. split; [clear - PR4 ACL HKlo HK; lia| exact I].
      + constructor; [cbn [fst snd]; exists (T, 4 * tl); split; [left; reflexivity|]; cbn [fst snd cells_size csize Nat.add]; rewrite LT; clear - TL; lia|].
        unfold mpd_cx, mpd_blk. rewrite OR. constructor; [| constructor]. cbn [fst snd cells_size csize Nat.add].
        exists (md_p dR, 4 * md_n dR). split; [right; left; reflexivity|]. cbn [fst snd]. rewrite <- HLR. lia.
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L39998703553.142L59314858098.117L59314858098.11800000J00h01FS2ra2sp2dE2dN2dW2dR2ts3HNES2ra2sp2dE2dN2dW2dR2ts2N14HON0S2ra2sp2dE2dN2dW2dR2ts2E14HOE0". (* [comment removed for export] *)
  Lemma core_kit : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))P,(5:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(2.$?.(10.R6.)$16.)P,(2.$?.(10.R6.)$16.)P,(1=.+1.(19.VdN,))P,(1=.+1.(19.VdE,))(31.(31.(63.$45.R>.(17.R:.)(4?.R:.))(31.(63.$45.R>.R8.R6.)(31.(60.$45.R>.(17.R9.)(58.(4?.R9.)))(31.(60.$45.R>.(17.VdN,)(58.(4?.VdN,)))(60.$45.R>.(17.VdE,)(58.(4?.VdE,)))))))(31.(31.(2.$0.(42.(4>.(3.&40.)(4?.VdN,)))(19.VdN,))(31.(2.$0.(42.(4>.(3.&40.)(4?.VdE,)))(19.VdE,))(31.(1=.(19.VdE,)+2710.)(31.(1=.(19.VdN,)+1387.)(2.$0.(42.(4>.(3.&40.)R6.))R7.)))))(31.(31.(48.$45.R>.(15.VdX,)(5=.(17.R:.)(25.&40.(51.R:.))(19.R:.)(5>.R:.)))(31.(48.$45.R>.(15.VdN,)(5=.(17.VdN,)(25.&40.(51.VdN,))(19.VdN,)(5>.VdN,)))(31.(48.$45.R>.(15.VdE,)(5=.(17.VdE,)(25.&40.(51.VdE,))(19.VdE,)(5>.VdE,)))(48.$45.R>.(1>.(13.&40.Vsp,)-60.)(53.R9.)))))(31.(31.(32.=(17.R:.))(31.(1=.(1>.(17.R:.)(18.+4.(19.R:.)))(22.VL,))(31.(2.$0.(23.(17.R:.)+10.)=)(31.(1=.+1.(19.R:.))(31.(2.$0.(42.(4>.(3.&40.)(4?.R:.)))(19.R:.))(1=.(19.R:.)$50.))))))(31.(31.(32.=R8.)(31.(1=.(1>.R8.(18.+4.R7.))(22.VL,))(31.(2.$0.(23.R8.+10.)=)(31.(32.=R7.)(1.(1=.(1>.R8.(18.+4.R7.))(5;.VL,))(1=.(5<.VL,)R8.))))))(31.(31.(32.=(17.R9.))(31.(1=.(1>.(17.R9.)(18.+4.(19.R9.)))(22.VL,))(31.(2.$0.(23.(17.R9.)+10.)=)(31.(1=.+1.(19.R9.))(31.(2.$0.(42.(4>.(3.&40.)(4?.R9.)))(19.R9.))(1=.(19.R9.)$50.))))))(31.(31.(1.(1=.(1>.(17.R:.)(18.+4.(19.R:.)))R8.)(1=.(1>.R8.(18.+4.R7.))(17.R:.)))(31.(1.(1=.(1>.(17.R9.)(18.+4.(19.R9.)))R8.)(1=.(1>.R8.(18.+4.R7.))(17.R9.)))(1.(1=.(1>.(17.R:.)(18.+4.(19.R:.)))(17.R9.))(1=.(1>.(17.R9.)(18.+4.(19.R9.)))(17.R:.)))))(31.(31.(1.(1=.(1>.(17.VdN,)(18.+4.(19.VdN,)))R8.)(1=.(1>.R8.(18.+4.R7.))(17.VdN,)))(31.(1.(1=.(1>.(17.VdN,)(18.+4.(19.VdN,)))(17.R:.))(1=.(1>.(17.R:.)(18.+4.(19.R:.)))(17.VdN,)))(31.(32.=(17.VdN,))(31.(1=.(1>.(17.VdN,)(18.+4.(19.VdN,)))(22.VL,))(2.$0.(23.(17.VdN,)+4.)=)))))(31.(1.(1=.(1>.(17.VdE,)(18.+4.(19.VdE,)))R8.)(1=.(1>.R8.(18.+4.R7.))(17.VdE,)))(31.(1.(1=.(1>.(17.VdE,)(18.+4.(19.VdE,)))(17.R:.))(1=.(1>.(17.R:.)(18.+4.(19.R:.)))(17.VdE,)))(31.(32.=(17.VdE,))(31.(1=.(1>.(17.VdE,)(18.+4.(19.VdE,)))(22.VL,))(2.$0.(23.(17.VdE,)+4.)=)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until ts. intros TS OW OR N1 E1.
    flat constr:((t_facts _ _ _ _ _ _ _ _ _ TS OW OR)) 7%nat. intros FW FT FR DWT DRT DWR EF.
    destruct TS as (lo16 & SZ & CS_ & RR & TL & NIN).
    flat constr:(ME0) 2%nat. intros FLt13 _. flat constr:(FLt13) 6%nat. flclear FLt13. intros _ _ _ HLE0 HNE0 HOE0. flat constr:(MN0) 2%nat. intros FLt14 _. flat constr:(FLt14) 6%nat. flclear FLt14. intros _ _ _ HLN0 HNN0 HON0.
    assert (NNn : md_own dN <> LNull) by (intros O; rewrite O in HON0; lia). assert (NNe : md_own dE <> LNull) by (intros O; rewrite O in HOE0; lia).
    flat constr:((EF dN opndN NNn)) 6%nat. intros DNT DNX PN0 PN4 PALN _. flat constr:((EF dE opndE NNe)) 6%nat. intros DET DEX PE0 PE4 PALE _.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 5%nat. intros CN_ BN HLN HNN _. flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 5%nat. intros CE_ BE HLE HNE _.
    flat constr:((w_cells _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros CW _.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros FLt15 _. flat constr:(FLt15) 2%nat. flclear FLt15. intros FLt16 _. flat constr:(FLt16) 6%nat. flclear FLt16. intros _ _ _ _ _ HOW. rewrite OW in HOW. flat constr:(HOW) 4%nat. flclear HOW. intros _ _ _ UW.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 3%nat. intros _ CH0 _.
    pose proof CS_ as CS2. flat constr:(CS2) 21%nat. flclear CS2. intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CXH _.
    unfold mpd_cx in CXH. rewrite OR in CXH. pose proof (Forall_inv CXH) as CXT. pose proof (Forall_inv (Forall_inv_tail CXH)) as CXR. cbn [fst snd] in CXT, CXR.
    split. { split; [exact UW|]. split; [exact (u32arr_of_cells _ _ _ _ _ _ CXT eq_refl)|]. split; [exact (u32arr_ro _ _ _ _ (u32arr_of_cells _ _ _ _ _ _ CXR eq_refl))|]. exact (conj BN BE). }
    split; [unfold MPI_MAX_LIMBS in HNE; repeat split; [exact HLN| exact HLE| lia| exact NN| exact TL]|].
    split; [exact (conj CW (conj CN_ (conj CE_ CH0)))|].
    split; [exact FW|]. split; [exact FT|]. split; [exact FR|]. split; [exact (conj DWT (conj DRT DWR))|].
    split; [exact (conj DNT (conj DNX (conj PN0 (conj PN4 PALN))))| exact (conj DET (conj DEX (conj PE0 (conj PE4 PALE))))].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac kit TS OW OR N1 E1 :=
    destruct (core_kit _ _ _ _ _ _ _ _ _ TS OW OR N1 E1) as
      ((UW & UT & ROR & RON & ROE) & (HLN & HLE & HNE & HNN & TL) & (CW & CN_ & CE_ & CH0)
       & (PW0 & PW4 & PALW & NW1 & HLW & HNW) & (T0 & T4 & TAL & TL0 & TIMG) & (PR0 & PR4 & PALR & NR1 & HLR & HNR)
       & (DWT & DRT & DWR) & (DNT & DNX & PN0 & PN4 & PALN) & (DET & DEX & PE0 & PE4 & PALE));
    unfold mpi_cells in CW, CN_, CE_; unfold rr_cells, mpi_cells in CH0; unfold MPI_MAX_LIMBS in HNW, HNR.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L24890867188.89L36946857996.88L8555823315.89 00000900@00NS2ra2sp1aS2ra2spS2ra2sp1a1k2Hk". (* [comment removed for export] *)
  Lemma mod16_4 : forall a, a mod 16 = 0 -> a mod 4 = 0.
  Proof. intros a H. apply Z.mod_divide in H; [| lia]. apply Z.mod_divide; [lia|]. flat constr:(H) 2%nat. flclear H. intros k Hk. exists (4 * k). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma L_addfix : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x7 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x21aac.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts xra x7 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    pose proof ts_st as (lo16 & sz_lo & st & rr_d & len_ts & t_fresh).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    pose proof (mc_w_facts _ _ _ _ _ _ _ _ _ st) as (at_w & ns_w & addr_w & wr_w & lo_w & cr_w & crl_w & _).
    pose proof (mc_ext_facts _ _ _ _ _ _ _ _ _ _ st opndN) as (at_n & cr_n & crl_n & _).
    pose proof (mc_opnd_sep_we _ _ _ _ _ _ _ _ _ _ st opndN) as (sep_wn & op_wn).
    pose proof (mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ st) as (_ & op_ww).
    do 5 step.
    eapply aevtM_cut.
    { eapply (HAS 1 (or_introl eq_refl) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq dW dN dW lo).
      all: try rewrite spf_val.
      - exact heap_q.
      - exact at_w.
      - exact at_n.
      - exact at_w.
      - exact sep_wn.
      - left; reflexivity.
      - destruct sep_wn as [same|[below|above]]; [left; symmetry; exact same| right; right; exact below| right; left; exact above].
      - exact ns_w.
      - exact op_wn.
      - exact op_ww.
      - exact cr_n.
      - exact crl_n.
      - exact cr_w.
      - exact crl_w.
      - exact wr_w.
      - exact lo_w.
      - exact stk_q.
      - lia.
      - exact ACL.
      - lia.
      - lia.
      - exact DHI.
      - exact TP.
      - exact inv_q.
      - exact sok_q.
      - exact CA.
      - rewrite addr_w. reflexivity.
      - reflexivity.
      - rewrite addr_w. reflexivity. }
    intros ms' mo' post.
    binop_post post m2 mo2 h2 LB2 d2 r2 cfg_eq inv2 stk2 frm2 top2 heap2 at2 out2 presx2 sok2 rel2.
    destruct rel2 as (r2_val & _ & pad2 & blk2 & n2).
    assert (ts2 : tstate m2 mo2 h2 LB2 d2 dR T tl ts).
    { exists lo16. split; [exact sz_lo|]. split; [| exact (conj rr_d (conj len_ts t_fresh))].
      exact (mc_binop_w _ _ _ _ _ _ _ _ _ m2 mo2 h2 LB2 d2 st heap2 top2 frm2 at2 out2 presx2 sok2 inv2 stk2 blk2 pad2 n2). }
    pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
    rewrite ret_pc_even by (cbn; lia).
    step.
    eapply L_clean1'; [exact ts2|].
    unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in r2_val. lia.
  Qed.

  Local Ltac cond_decide :=
    unfold bv_eqb, bv_ltu, bv_lts, bv_leu;
    rewrite ?unsigned_lit by lia;
    lazymatch goal with
    | |- negb _ = false => apply Bool.negb_false_iff, Z.eqb_eq; lia
    | |- negb _ = true => apply Bool.negb_true_iff, Z.eqb_neq; lia
    | |- Z.eqb _ _ = false => apply Z.eqb_neq; lia
    | |- Z.eqb _ _ = true => apply Z.eqb_eq; lia
    | |- Z.ltb _ _ = false => apply Z.ltb_ge; lia
    | |- Z.ltb _ _ = true => apply Z.ltb_lt; lia
    | |- Z.leb _ _ = false => apply Z.leb_gt; lia
    | |- Z.leb _ _ = true => apply Z.leb_le; lia
    end.
  Local Ltac if_false_x :=
    lazymatch goal with
    | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
        let E := fresh "E" in assert (E : c = false) by cond_decide; rewrite E; cbv_concl_iota; clear E
    end.
  Local Ltac land_zero_any :=
    repeat match goal with
    | |- context [Z.land ?p 7] => let E := fresh "E" in
        assert (E : Z.land p 7 = 0) by (change (Z.land p 7) with (Z.land p (Z.ones 3)); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia);
        rewrite E; clear E
    | |- context [Z.land ?p 3] => let E := fresh "E" in
        assert (E : Z.land p 3 = 0) by (change (Z.land p 3) with (Z.land p (Z.ones 2)); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia);
        rewrite E; clear E
    end.
  Lemma L_tail : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x7 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dW = LHeap -> 1 <= md_n dE ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x21a50.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts xra x7 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st heap_w ne_pos.
    pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    pose proof ts_st as (lo16 & sz_lo & st & rr_d & len_ts & t_fresh).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    destruct (a_cells _ _ _ _ _ _ _ _ _ st) as (pA & sgA & nA & padA & cells_A & sgA_val).
    unfold mpi_cells in cells_A.
    pose proof MA0 as ((_ & al_A & pos_A & _) & _).
    pose proof (rw_cells_bound _ _ _ _ cells_A) as bnd_A. cbn [cells_size csize Nat.add] in bnd_A.
    step. if_false_x. step. zsimp. land_zero_any. step. if_false.
    step; try zsimp. step; try zsimp. step; try zsimp.
    destruct sgA_val as [-> | ->]; step;
      (lazymatch goal with |- context [if ?c then _ else _] =>
         let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity) end); cbv_concl_iota.
    { step. step. eapply L_clean1; [exact ts_st| lia]. }
    pose proof (e_raw _ _ _ _ _ _ _ _ _ dE st opndE) as (cells_E & bytes_E & len_E & _ & _ & pz_E & nn_E & null_E).
    unfold mpi_cells in cells_E.
    assert (nnull_E : md_own dE <> LNull) by (intros is_null; destruct (null_E is_null); lia).
    destruct (nn_E nnull_E) as (pE_pos & pE_lim & _).
    assert (pE_al : md_p dE mod 4 = 0) by (destruct pz_E as [|(_ & al)]; [lia| exact al]).
    step. step. if_false_x. step. zsimp. land_zero_any. step. if_false.
    destruct (nth_error (u32s (md_limbs dE)) 0) as [b0|] eqn:nth_b0.
    2: { exfalso. apply nth_error_None in nth_b0. rewrite u32s_length in nth_b0. lia. }
    pose proof (u8ro_read _ _ _ _ 0 b0 _ bytes_E nth_b0 ltac:(lia) eq_refl) as rd_b0.
    step; try zsimp. step; try zsimp. step.
    if_cases odd_b.
    2: { step. step. eapply L_clean1; [exact ts_st| lia]. }
    pose proof (w_cells _ _ _ _ _ _ _ _ _ st) as (cells_W & sg_W & len_W & rng_W & addr_W).
    unfold mpi_cells in cells_W. unfold MPI_MAX_LIMBS in rng_W.
    pose proof (mc_w_facts _ _ _ _ _ _ _ _ _ st) as (at_w & _ & _ & _ & _ & _ & _ & hw_facts & _).
    destruct (hw_facts heap_w) as (pW_pos & pW_lim & _ & nW_pos).
    pose proof at_w as ((_ & _ & _ & _ & _ & own_w) & _). rewrite heap_w in own_w.
    destruct own_w as (_ & _ & pW_al & arr_w).
    step. step. step.
    replace (zx16 (Z_to_bv 64 (md_n dW))) with (Z_to_bv 64 (md_n dW))
      by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
    eapply aevtM_cut_evt; [exact mok_q| eapply (HCZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_p dW) (md_n dW) (md_limbs dW))| ].
    { exact (proj1 arr_w). }
    { lia. }
    { lia. }
    { apply mod16_4. exact pW_al. }
    { exact pW_pos. }
    { exact inv_q. }
    { reflexivity. }
    { reflexivity. }
    intros ms' post.
    destruct post as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & z & ms_eq & _ & _ & _ & v0_eq & z_nn & z_iff).
    subst ms' v0.
    rewrite ret_pc_even by (cbn; lia).
    step; try zsimp. step; try zsimp. step; try zsimp.
    pose proof (munch_refl [(md_addr dX, md_addr dX + 16)] mq) as mu.
    pose proof (wmono_refl usegs mq) as wm.
    clear cells_A cells_E bytes_E rd_b0 heap_q sok_q arr_w.
    step.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m2 end.
    set (sgn := if z =? 0 then 1 else -1).
    assert (sgn_ok : sgn = 1 \/ sgn = -1) by (unfold sgn; destruct (z =? 0); [left| right]; reflexivity).
    apply (rw_cells_C2_congr usegs m2 (md_addr dX) [C8 (Z_to_bv 64 (md_p dW))] _ sgn) in cells_W;
      [| unfold sgn, ct_mask; destruct (z =? 0); vm_compute; reflexivity].
    rewrite <- addr_W in mu, cells_W.
    pose proof (mc_sign_w _ _ _ _ _ _ _ _ _ m2 sgn st mu wm inv_q cells_W sgn_ok) as st2.
    assert (ts2 : tstate m2 moq hq LBq (set_sg dW sgn) dR T tl ts).
    { exists lo16. split; [exact sz_lo|]. split; [exact st2| exact (conj rr_d (conj len_ts t_fresh))]. }
    eapply L_addfix. exact ts2.
  Qed.

  Lemma L_core3 : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dW = LHeap -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dW -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21a34.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st heap_w heap_r nN_pos nN_W nN_R nE_pos tl_eq.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos. pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    assert (t_big : 2 * md_n dN + 1 <= tl)
      by (rewrite tl_eq; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    destruct (core_kit _ _ _ _ _ _ _ _ _ ts_st heap_w heap_r nN_pos nE_pos) as
      ((arrW & arrT & roR & roN & roE) & (lenN & lenE & nE_max & nN_max & lenT) & (cellW & cellN & cellE & cellR)
      & (pW_pos & pW_lim & pW_al & nW_pos & lenW & nW_max) & (T_pos & T_lim & T_al & tl_pos & T_img)
      & (pR_pos & pR_lim & pR_al & nR_pos & lenR & nR_max) & (sepWT & sepRT & sepWR)
      & (sepNT & sepNW & pN_pos & pN_lim & pN_al) & (sepET & sepEW & pE_pos & pE_lim & pE_al)).
    unfold mpi_cells in cellW, cellN, cellE. unfold rr_cells, mpi_cells in cellR. unfold MPI_MAX_LIMBS in nW_max, nR_max.
    pose proof ts_st as (lo16 & sz_lo & st & _).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    step. step. step; try zsimp.
    replace (zx16 (Z_to_bv 64 (md_n dN))) with (Z_to_bv 64 (md_n dN))
      by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
    step. step. step. step.
    eapply aevtM_cut_evt; [exact mok_q| eapply (HFROM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_p dW) (md_p dW) (md_p dN) (md_n dN) T lo (md_limbs dW) (md_limbs dW) (md_limbs dN) ts)| ].
      - exact arrW.
      - exact (proj1 arrW).
      - exact roN.
      - exact arrT.
      - clear - nN_pos nN_max; lia.
      - clear - nN_W lenW; lia.
      - clear - nN_W lenW; lia.
      - clear - lenN; lia.
      - clear - t_big lenT; lia.
      - rewrite lenW, lenT; exact sepWT.
      - rewrite lenW, lenT; exact sepWT.
      - rewrite lenN, lenT; exact sepNT.
      - rewrite lenN, lenW; exact sepNW.
      - apply mod16_4; exact pW_al.
      - apply mod16_4; exact pW_al.
      - exact pN_al.
      - apply mod16_4; exact T_al.
      - exact pW_pos.
      - exact pW_pos.
      - exact pN_pos.
      - exact T_pos.
      - rewrite lenW; clear - pW_lim ac_bnd; lia.
      - rewrite lenW; clear - pW_lim ac_bnd; lia.
      - rewrite lenN; clear - pN_lim ac_bnd; lia.
      - rewrite lenT; clear - T_lim ac_bnd; lia.
      - rewrite spf_val; exact stk_q.
      - rewrite spf_val; unfold MPI_CORE_FROM_MONT_REP_STACK; clear - SLO HLS; lia.
      - rewrite spf_val; clear - SPA; lia.
      - left; rewrite lenW; clear - pW_lim ACL; lia.
      - left; rewrite lenW; clear - pW_lim ACL; lia.
      - left; rewrite lenN; clear - pN_lim ACL; lia.
      - left; rewrite lenT; clear - T_lim ACL; lia.
      - exact inv_q.
      - vm_compute; reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
    - intros ms' post.
      destruct post as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & xs' & ts'
                        & ms_eq & mu2 & wm2 & inv2 & arrX2 & lenX2 & _ & arrT2 & lenT2 & _ & stk2).
      subst ms'.
      rewrite spf_val in mu2, stk2. unfold MPI_CORE_FROM_MONT_REP_STACK in mu2.
      pose proof (core_munch _ _ _ _ _ _ _ _ _ m2 (md_n dN) (2 * md_n dN + 1) 208 xs' ts' ts_st heap_w heap_r mu2 wm2 inv2 stk2
                    ltac:(clear - nN_pos nN_W; lia) ltac:(clear - nN_pos t_big; lia) ltac:(clear; lia) ltac:(clear - SLO HLS; lia)
                    arrX2 ltac:(rewrite lenX2; exact lenW) arrT2 lenT2) as ts2.
      rewrite ret_pc_even by (cbn; lia).
      eapply L_tail; [exact ts2| exact heap_w| exact nE_pos].
  Qed.

  Lemma L_core2 : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dW = LHeap -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dW -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x219dc.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HCEM HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st heap_w heap_r nN_pos nN_W nN_R nE_pos tl_eq.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos. pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    assert (t_big : 2 * md_n dN + 1 <= tl)
      by (rewrite tl_eq; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    destruct (core_kit _ _ _ _ _ _ _ _ _ ts_st heap_w heap_r nN_pos nE_pos) as
      ((arrW & arrT & roR & roN & roE) & (lenN & lenE & nE_max & nN_max & lenT) & (cellW & cellN & cellE & cellR)
      & (pW_pos & pW_lim & pW_al & nW_pos & lenW & nW_max) & (T_pos & T_lim & T_al & tl_pos & T_img)
      & (pR_pos & pR_lim & pR_al & nR_pos & lenR & nR_max) & (sepWT & sepRT & sepWR)
      & (sepNT & sepNW & pN_pos & pN_lim & pN_al) & (sepET & sepEW & pE_pos & pE_lim & pE_al)).
    unfold mpi_cells in cellW, cellN, cellE. unfold rr_cells, mpi_cells in cellR. unfold MPI_MAX_LIMBS in nW_max, nR_max.
    pose proof ts_st as (lo16 & sz_lo & st & _).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    do 6 (step; try zsimp).
    replace (zx16 (Z_to_bv 64 (md_n dN))) with (Z_to_bv 64 (md_n dN))
      by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
    replace (zx16 (Z_to_bv 64 (md_n dE))) with (Z_to_bv 64 (md_n dE))
      by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
    step; try zsimp. step; try zsimp. step.
    lazymatch goal with |- context [if ?c then _ else _] =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity) end; cbv_concl_iota.
    step. step. step.
    eapply aevtM_cut_evt; [exact mok_q| eapply (HCEM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_p dW) (md_p dW) (md_p dN) (md_n dN) (md_p dE) (md_n dE) (md_p dR) T lo
                                                  (md_limbs dW) (md_limbs dW) (md_limbs dN) (md_limbs dE) (md_limbs dR) ts)| ].
    - unfold mpi_core_exp_mod_pre.
      split; [exact arrW|].
      split; [exact (proj1 arrW)|].
      split; [exact roN|].
      split; [exact roE|].
      split; [exact roR|].
      split; [exact arrT|].
      split; [clear - nN_pos nN_max; lia|].
      split; [clear - nE_pos nE_max; lia|].
      split; [clear - nN_W lenW; lia|].
      split; [clear - nN_W lenW; lia|].
      split; [clear - lenN; lia|].
      split; [clear - lenE; lia|].
      split; [clear - nN_R lenR; lia|].
      split; [rewrite lenT, tl_eq; lia|].
      split; [rewrite lenW, lenT; exact sepWT|].
      split; [rewrite lenW, lenT; exact sepWT|].
      split; [rewrite lenN, lenT; exact sepNT|].
      split; [rewrite lenE, lenT; exact sepET|].
      split; [rewrite lenR, lenT; exact sepRT|].
      split; [rewrite lenN, lenW; exact sepNW|].
      split; [rewrite lenE, lenW; exact sepEW|].
      split; [apply mod16_4; exact pW_al|].
      split; [apply mod16_4; exact pW_al|].
      split; [exact pN_al|].
      split; [exact pE_al|].
      split; [apply mod16_4; exact pR_al|].
      split; [apply mod16_4; exact T_al|].
      split; [exact pW_pos|].
      split; [exact pW_pos|].
      split; [exact pN_pos|].
      split; [exact pE_pos|].
      split; [exact pR_pos|].
      split; [exact T_pos|].
      split; [rewrite lenW; clear - pW_lim ac_bnd; lia|].
      split; [rewrite lenW; clear - pW_lim ac_bnd; lia|].
      split; [rewrite lenN; clear - pN_lim ac_bnd; lia|].
      split; [rewrite lenE; clear - pE_lim ac_bnd; lia|].
      split; [rewrite lenR; clear - pR_lim ac_bnd; lia|].
      split; [rewrite lenT; clear - T_lim ac_bnd; lia|].
      split; [rewrite spf_val; exact stk_q|].
      split; [rewrite spf_val; unfold MPI_CORE_EXP_MOD_STACK; clear - SLO HLS; lia|].
      split; [rewrite spf_val; clear - SPA; lia|].
      split; [left; rewrite lenW; clear - pW_lim ACL; lia|].
      split; [left; rewrite lenW; clear - pW_lim ACL; lia|].
      split; [left; rewrite lenN; clear - pN_lim ACL; lia|].
      split; [left; rewrite lenE; clear - pE_lim ACL; lia|].
      split; [left; rewrite lenR; clear - pR_lim ACL; lia|].
      split; [left; rewrite lenT; clear - T_lim ACL; lia|].
      split; [exact inv_q|].
      vm_compute; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros ms' post.
      destruct post as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & xs' & ts'
                        & ms_eq & mu2 & wm2 & inv2 & arrX2 & lenX2 & _ & arrT2 & lenT2 & stk2).
      subst ms'.
      rewrite spf_val in mu2, stk2. unfold MPI_CORE_EXP_MOD_STACK in mu2.
      pose proof (core_munch _ _ _ _ _ _ _ _ _ m2 (md_n dN) (Z.of_nat (length ts)) 400 xs' ts' ts_st heap_w heap_r mu2 wm2 inv2 stk2
                    ltac:(clear - nN_pos nN_W; lia) ltac:(clear - lenT; lia) ltac:(clear; lia) ltac:(clear - SLO HLS; lia)
                    arrX2 ltac:(rewrite lenX2; exact lenW) arrT2 lenT2) as ts2.
      rewrite ret_pc_even by (cbn; lia).
      eapply L_core3; [exact ts2| exact heap_w| exact heap_r| exact nN_pos| | exact nN_R| exact nE_pos| exact tl_eq].
      cbn [set_limbs md_n]. exact nN_W.
  Qed.

  Lemma L_core : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dW = LHeap -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dW -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x219b0.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HMMI HTOM HCEM HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st heap_w heap_r nN_pos nN_W nN_R nE_pos tl_eq.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos. pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    assert (t_big : 2 * md_n dN + 1 <= tl)
      by (rewrite tl_eq; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    destruct (core_kit _ _ _ _ _ _ _ _ _ ts_st heap_w heap_r nN_pos nE_pos) as
      ((arrW & arrT & roR & roN & roE) & (lenN & lenE & nE_max & nN_max & lenT) & (cellW & cellN & cellE & cellR)
      & (pW_pos & pW_lim & pW_al & nW_pos & lenW & nW_max) & (T_pos & T_lim & T_al & tl_pos & T_img)
      & (pR_pos & pR_lim & pR_al & nR_pos & lenR & nR_max) & (sepWT & sepRT & sepWR)
      & (sepNT & sepNW & pN_pos & pN_lim & pN_al) & (sepET & sepEW & pE_pos & pE_lim & pE_al)).
    unfold mpi_cells in cellW, cellN, cellE. unfold rr_cells, mpi_cells in cellR. unfold MPI_MAX_LIMBS in nW_max, nR_max.
    pose proof ts_st as (lo16 & sz_lo & st & _).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    step. step.
    eapply aevtM_cut_evt; [exact mok_q| eapply (HMMI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_p dN) (md_limbs dN))| ].
    - exact roN.
    - clear - lenN nN_pos; lia.
    - exact pN_al.
    - exact pN_pos.
    - exact inv_q.
    - reflexivity.
    - intros ms' post.
      destruct post as (u0 & u1 & u2 & mm & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ms_eq & _ & _ & _).
      subst ms'.
      rewrite ret_pc_even by (cbn; lia).
      do 3 (step; try zsimp).
    replace (zx16 (Z_to_bv 64 (md_n dN))) with (Z_to_bv 64 (md_n dN))
      by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
      do 5 (step; try zsimp). step.
      eapply aevtM_cut_evt; [exact mok_q| eapply (HTOM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_p dW) (md_p dW) (md_p dR) (md_p dN) (md_n dN) T lo
                                                    (md_limbs dW) (md_limbs dW) (md_limbs dR) (md_limbs dN) ts)| ].
      + exact arrW.
      + exact (proj1 arrW).
      + exact roR.
      + exact roN.
      + exact arrT.
      + clear - nN_pos nN_max; lia.
      + clear - nN_W lenW; lia.
      + clear - nN_W lenW; lia.
      + clear - nN_R lenR; lia.
      + clear - lenN; lia.
      + clear - t_big lenT; lia.
      + rewrite lenW, lenT; exact sepWT.
      + rewrite lenW, lenT; exact sepWT.
      + rewrite lenR, lenT; exact sepRT.
      + rewrite lenN, lenT; exact sepNT.
      + rewrite lenN, lenW; exact sepNW.
      + apply mod16_4; exact pW_al.
      + apply mod16_4; exact pW_al.
      + apply mod16_4; exact pR_al.
      + exact pN_al.
      + apply mod16_4; exact T_al.
      + exact pW_pos.
      + exact pW_pos.
      + exact pR_pos.
      + exact pN_pos.
      + exact T_pos.
      + rewrite lenW; clear - pW_lim ac_bnd; lia.
      + rewrite lenW; clear - pW_lim ac_bnd; lia.
      + rewrite lenR; clear - pR_lim ac_bnd; lia.
      + rewrite lenN; clear - pN_lim ac_bnd; lia.
      + rewrite lenT; clear - T_lim ac_bnd; lia.
      + rewrite spf_val; exact stk_q.
      + rewrite spf_val; unfold MPI_CORE_MONTMUL_STACK; clear - SLO HLS; lia.
      + rewrite spf_val; clear - SPA; lia.
      + left; rewrite lenW; clear - pW_lim ACL; lia.
      + left; rewrite lenW; clear - pW_lim ACL; lia.
      + left; rewrite lenR; clear - pR_lim ACL; lia.
      + left; rewrite lenN; clear - pN_lim ACL; lia.
      + left; rewrite lenT; clear - T_lim ACL; lia.
      + exact inv_q.
      + vm_compute; reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + intros ms2 post2.
        destruct post2 as (w0 & w1 & w2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m2 & xs' & ts'
                          & ms_eq2 & mu2 & wm2 & inv2 & arrX2 & lenX2 & _ & arrT2 & lenT2 & _ & stk2).
        subst ms2.
        rewrite spf_val in mu2, stk2. unfold MPI_CORE_MONTMUL_STACK in mu2.
        pose proof (core_munch _ _ _ _ _ _ _ _ _ m2 (md_n dN) (2 * md_n dN + 1) 192 xs' ts' ts_st heap_w heap_r mu2 wm2 inv2 stk2
                      ltac:(clear - nN_pos nN_W; lia) ltac:(clear - nN_pos t_big; lia) ltac:(clear; lia) ltac:(clear - SLO HLS; lia)
                      arrX2 ltac:(rewrite lenX2; exact lenW) arrT2 lenT2) as ts2.
        rewrite ret_pc_even by (cbn; lia).
        eapply L_core2; [exact ts2| exact heap_w| exact heap_r| exact nN_pos| | exact nN_R| exact nE_pos| exact tl_eq].
        cbn [set_limbs md_n]. exact nN_W.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma t_binop_w : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pm2,P,(3.&40.)(5.(3.&8.))Pmo2,$6.Ph2,(7.$45.VL,VHI,)PLB2,(8.$9.)PdW2,$:.P,(5:.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(;.$45.VL,VHI,R4.R3.R6.R5.)P,(2.$0.(1;.$45.VL,VHI,R5.)(1;.$45.VL,VHI,R>.))P,(47.R10.R7.)P,(<.$45.R9.R6.R5.)P,(66.R10.R?.R7.R6.)P,(67.$45.VL,R11.(1>.(13.&40.Vsp,)-70.)(68.R10.)R14.R;.)P,(28.$45.VL,R<.)P,(27.$45.R=.)P,(1?.$45.R>.Vlo,(1>.(13.&40.Vsp,)-70.))P,Pb,$9.P,(33.$9.R1.(52.R<.))(1.(33.$9.R2.(52.R16.))(>.(33.$9.R2.R17.)))P,(2.(3.&40.)(5>.R<.)(5>.R15.))P,(1=.(19.R16.)(19.R=.))(5:.R12.R11.R10.R?.R>.R16.R15.R14.R13.)")
(* [comment removed for export] *).
  Proof.
    intros until dW2. intros (lo16 & SZ & CS_ & RR & TL & NIN) HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2 FRB PAD NLE.
    exists lo16. split; [exact SZ|]. split; [| exact (conj RR (conj TL NIN))].
    eapply mc_binop_w; [exact CS_| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB| exact PAD| exact NLE].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L26983617546.9800000@S2ra2sp1d1H1a2Ha". (* [comment removed for export] *)
  Lemma copy_sep_of_opnd : forall d1 d lo' SP', opnd_sep d1 d lo' SP' -> 0 <= md_addr d -> copy_sep d1 d lo' SP'.
  Proof. intros d1 d lo' SP' (O1 & O2 & O3 & O4 & O5) H. repeat (split; [assumption|]). intros a Ha. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma L_mid : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21968.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HCMP HMOD HGROW HMMI HTOM HCEM HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st heap_r nN_pos nN_R nE_pos tl_eq.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos. pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    pose proof NN as nN_max.
    assert (at_grow : forall m1 moq1 hq1 LB1 dW1 (ra1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 : word),
      tstate m1 moq1 hq1 LB1 dW1 dR T tl ts ->
      RUN moq1 m1 (mkR ra1 SPF gp tp u0 u1 u2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) v0 v1 v2 v3 v4 v5 v6 v7
        (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 u3 u4 u5 u6) 0x219a0).
    { intros m1 moq1 hq1 LB1 dW1 ra1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 ts1.
      pose proof ts1 as (lo1 & sz1 & st1 & rr1 & len1 & fresh1).
      pose proof (cs_parts _ _ _ _ _ _ _ _ _ st1) as (heap1 & top1 & frm1 & sok1 & inv1 & stk1 & _ & _ & mok1).
      pose proof (mc_w_facts _ _ _ _ _ _ _ _ _ st1) as (at_w1 & ns_w1 & addr_w1 & wr_w1 & _).
      pose proof (e_raw _ _ _ _ _ _ _ _ _ dN st1 opndN) as (cells_N & _ & _ & rng_N & _).
      unfold mpi_cells in cells_N.
      step; try zsimp.
      replace (zx16 (Z_to_bv 64 (md_n dN))) with (Z_to_bv 64 (md_n dN))
        by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
      step. step.
      eapply aevtM_cut.
      { eapply (HGROW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LB1 dW1 (md_n dN) lo).
        all: try rewrite spf_val.
        - exact heap1.
        - exact at_w1.
        - exact ns_w1.
        - exact wr_w1.
        - lia.
        - exact stk1.
        - clear - SLO HLS; lia.
        - exact ACL.
        - clear - top1 HTOP; lia.
        - clear - SPA; lia.
        - exact DHI.
        - exact TP.
        - exact inv1.
        - exact sok1.
        - exact CA.
        - rewrite addr_w1. reflexivity.
        - reflexivity. }
      intros ms' mo' post.
      binop_post post m2 mo2 h2 LB2 d2 r2 cfg_eq inv2 stk2 frm2 top2 heap2 at2 out2 presx2 sok2 rel2.
      destruct rel2 as (rel2 & blk2).
      assert (keep2 : md_pad d2 = md_pad dW1 /\ md_n dW1 <= md_n d2 /\ (r2 = 0 -> md_n dN <= md_n d2)).
      { destruct rel2 as [(r_ok & _ & n_eq & pad_eq & _)|(r_bad & ->)];
          [split; [exact pad_eq| lia]| split; [reflexivity| split; [lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in r_bad; lia]]]. }
      destruct keep2 as (pad2 & n2 & nN2).
      pose proof (t_binop_w _ _ _ _ _ _ _ _ _ m2 mo2 h2 LB2 d2 ts1 heap2 top2 frm2 at2 out2 presx2 sok2 inv2 stk2 blk2 pad2 n2) as ts2.
      pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
      rewrite ret_pc_even by (cbn; lia).
      assert (r2_cases : r2 = 0 \/ r2 = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct rel2 as [(r_ok & _)|(r_bad & _)]; [left| right]; assumption).
      destruct r2_cases as [-> | ->]; step;
        (lazymatch goal with |- context [if ?c then _ else _] =>
           let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity) end); cbv_concl_iota.
      - eapply L_core; [exact ts2| | exact heap_r| exact nN_pos| exact (nN2 eq_refl)| exact nN_R| exact nE_pos| exact tl_eq].
        destruct out2 as (_ & ns2 & _).
        apply (out_heap _ _ _ at2 ns2). specialize (nN2 eq_refl). lia.
      - eapply L_clean1'; [exact ts2|]. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. lia. }
    pose proof ts_st as (lo16 & sz_lo & st & rr_d & len_ts & t_fresh).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    pose proof MX0 as ((_ & al_X & pos_X & _) & _).
    pose proof (w_cells _ _ _ _ _ _ _ _ _ st) as (cells_W & _ & _ & _ & addr_W).
    unfold mpi_cells in cells_W.
    pose proof (rw_cells_bound _ _ _ _ cells_W) as bnd_W. cbn [cells_size csize Nat.add] in bnd_W.
    step. if_false_x. step. zsimp. land_zero_any. step. if_false. step.
    pose proof (munch_refl [(md_addr dX, md_addr dX + 16)] mq) as mu.
    pose proof (wmono_refl usegs mq) as wm.
    clear heap_q sok_q.
    step.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m1 end.
    rewrite <- addr_W in mu, cells_W.
    pose proof (mc_sign_w _ _ _ _ _ _ _ _ _ m1 1 st mu wm inv_q cells_W (or_introl eq_refl)) as st1.
    assert (ts1 : tstate m1 moq hq LBq (set_sg dW 1) dR T tl ts).
    { exists lo16. split; [exact sz_lo|]. split; [exact st1| exact (conj rr_d (conj len_ts t_fresh))]. }
    clear mu wm cells_W.
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st1) as (heap1 & top1 & frm1 & sok1 & inv1 & stk1 & _ & _ & mok1).
    pose proof (mc_w_facts _ _ _ _ _ _ _ _ _ st1) as (at_w1 & ns_w1 & addr_w1 & wr_w1 & lo_w1 & cr_w1 & crl_w1 & hp_w1 & _).
    pose proof (mc_ext_facts _ _ _ _ _ _ _ _ _ _ st1 opndN) as (at_n1 & cr_n1 & crl_n1 & _ & hp_n1 & _).
    pose proof (mc_opnd_sep_we _ _ _ _ _ _ _ _ _ _ st1 opndN) as (sep_wn1 & op_wn1).
    pose proof (mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ st1) as (_ & op_ww1).
    step. step. step.
    eapply aevtM_cut_evt; [exact mok1| eapply (HCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq (set_sg dW 1) dN)| ].
    - exact at_w1.
    - exact at_n1.
    - intros o. exact (proj1 (hp_w1 o)).
    - intros o. exact (proj1 (hp_n1 o)).
    - exact inv1.
    - rewrite addr_w1. reflexivity.
    - reflexivity.
    - intros ms' post.
      destruct post as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ms_eq & _ & _ & _).
      subst ms'.
      rewrite ret_pc_even by (cbn; lia).
      step. if_cases below_flag; [exact (at_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ts1)|].
      step. step. step. step.
      eapply aevtM_cut.
      { eapply (HMOD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq (set_sg dW 1) (set_sg dW 1) dN lo).
        all: try rewrite spf_val.
        - exact heap1.
        - exact at_w1.
        - exact at_w1.
        - exact at_n1.
        - left; reflexivity.
        - exact sep_wn1.
        - exact sep_wn1.
        - exact ns_w1.
        - rewrite addr_w1. exact NXN.
        - exact op_ww1.
        - exact op_wn1.
        - exact cr_w1.
        - exact crl_w1.
        - exact cr_n1.
        - exact crl_n1.
        - exact wr_w1.
        - exact lo_w1.
        - exact stk1.
        - clear - SLO HLS; lia.
        - exact ACL.
        - clear - top1 HTOP; lia.
        - clear - SPA; lia.
        - exact DHI.
        - exact TP.
        - exact inv1.
        - exact sok1.
        - exact CA.
        - rewrite addr_w1. reflexivity.
        - rewrite addr_w1. reflexivity.
        - reflexivity. }
      intros ms2 mo2 post2.
      binop_post post2 m2 mo2' h2 LB2 d2 r2 cfg_eq inv2 stk2 frm2 top2 heap2 at2 out2 presx2 sok2 rel2.
      destruct rel2 as ((_ & r2_rng) & _ & pad2 & blk2 & n2).
      pose proof (t_binop_w _ _ _ _ _ _ _ _ _ m2 mo2' h2 LB2 d2 ts1 heap2 top2 frm2 at2 out2 presx2 sok2 inv2 stk2 blk2 pad2 n2) as ts2.
      pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
      rewrite ret_pc_even by (cbn; lia).
      step. if_cases fail_flag.
      + eapply L_clean1'; [exact ts2| exact r2_rng].
      + exact (at_grow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ts2).
  Qed.

  Lemma L_copy : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21928.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HZF HCOPY HCMP HMOD HGROW HMMI HTOM HCEM HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dW dR T tl ts xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ts_st heap_r nN_pos nN_R nE_pos tl_eq.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos. pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    pose proof NN as nN_max.
    pose proof ts_st as (lo16 & sz_lo & st & rr_d & len_ts & t_fresh).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    pose proof (mc_w_facts _ _ _ _ _ _ _ _ _ st) as (at_w & ns_w & addr_w & wr_w & lo_w & cr_w & crl_w & _).
    pose proof (mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ st) as (_ & op_ww).
    assert (src : exists dS, mpd_at usegs mq LBq dS /\ mpd_sep dW dS /\ copy_sep dW dS lo SPc
                    /\ client_range L LBq lo (md_addr dS) 16 /\ (md_own dS = LHeap -> client_range L LBq lo (md_p dS) (4 * md_n dS))
                    /\ md_addr dS = md_addr dA).
    { destruct opndA as [in_A | eq_A].
      - pose proof (mc_ext_facts _ _ _ _ _ _ _ _ _ _ st in_A) as (at_A & cr_A & crl_A & _).
        pose proof (mc_opnd_sep_we _ _ _ _ _ _ _ _ _ _ st in_A) as (sep_wa & op_wa).
        pose proof at_A as ((_ & _ & pos_A & _) & _).
        exists dA. split; [exact at_A|]. split; [exact sep_wa|].
        split; [apply copy_sep_of_opnd; [exact op_wa| lia]|].
        split; [exact cr_A|]. split; [exact crl_A| reflexivity].
      - pose proof at_w as ((_ & _ & pos_W & _) & _).
        exists dW. split; [exact at_w|]. split; [left; reflexivity|].
        split; [apply copy_sep_of_opnd; [exact op_ww| lia]|].
        split; [exact cr_w|]. split; [exact crl_w| rewrite eq_A; exact addr_w]. }
    destruct src as (dS & at_S & sep_wS & cp_wS & cr_S & crl_S & addr_S).
    step. step. step.
    eapply aevtM_cut.
    { eapply (HCOPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq dW dS lo).
      all: try rewrite spf_val.
      - exact heap_q.
      - exact at_w.
      - exact ns_w.
      - exact at_S.
      - exact sep_wS.
      - exact cp_wS.
      - exact cr_S.
      - exact crl_S.
      - exact wr_w.
      - exact stk_q.
      - clear - SLO HLS; lia.
      - exact ACL.
      - clear - top_q HTOP; lia.
      - clear - SPA; lia.
      - exact DHI.
      - exact TP.
      - exact inv_q.
      - exact sok_q.
      - exact CA.
      - rewrite addr_w. reflexivity.
      - rewrite addr_S. reflexivity. }
    intros ms' mo' post.
    binop_post post m2 mo2 h2 LB2 d2 r2 cfg_eq inv2 stk2 frm2 top2 heap2 at2 out2 presx2 sok2 rel2.
    destruct rel2 as (r2_cases & _ & pad2 & blk2).
    assert (n2 : md_n dW <= md_n d2) by (destruct r2_cases as [(_ & _ & n_lo & _)|(_ & n_eq & _)]; lia).
    assert (r2_rng : -2^31 < r2 <= 0)
      by (destruct r2_cases as [(r_ok & _)|(r_bad & _)]; [| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in r_bad]; lia).
    pose proof (t_binop_w _ _ _ _ _ _ _ _ _ m2 mo2 h2 LB2 d2 ts_st heap2 top2 frm2 at2 out2 presx2 sok2 inv2 stk2 blk2 pad2 n2) as ts2.
    pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
    rewrite ret_pc_even by (cbn; lia).
    step. if_cases ok_flag.
    - eapply L_mid; [exact ts2| exact heap_r| exact nN_pos| exact nN_R| exact nE_pos| exact tl_eq].
    - step. eapply L_clean1; [exact ts2| exact r2_rng].
  Qed.

  Lemma cs_swap12 : forall mq moq hq LBq ls dW EX a b CS CX,
    CST mq moq hq LBq ls dW EX (a :: b :: CS) CX -> CST mq moq hq LBq ls dW EX (b :: a :: CS) CX.
  Proof.
    intros until CX. intros C.
    assert (SWAPF : forall (P : Z * list cell -> Prop), Forall P (a :: b :: CS) -> Forall P (b :: a :: CS)).
    { intros P HP. inversion HP as [|? ? Pa HP1]; subst. inversion HP1 as [|? ? Pb HP2]; subst.
      constructor; [exact Pb| constructor; [exact Pa| exact HP2]]. }
    unfold cstate in *.
    repeat match goal with
      | H : ?X /\ ?Y |- _ /\ _ => let H1 := fresh "H" in destruct H as [H1 H]; split; [first [exact H1 | exact (SWAPF _ H1)] |]
    end.
    first [exact C | exact (SWAPF _ C)].
  Qed.

  Lemma L_r2 : forall mq moq hq LBq dRR lo16 (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [dRR] dX [(T, 4 * tl)] [(SPc, lo16); (SP + -80, REGS)] [(T, [CB (4 * length ts)%nat (u32s ts)])] ->
    cells_size lo16 = 16%nat -> md_addr dRR = SP + -96 -> Z.of_nat (length ts) = tl ->
    1 <= md_n dN -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x218c8.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HR2 HZF HCOPY HCMP HMOD HGROW HMMI HTOM HCEM HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq dRR lo16 T tl ts xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 st sz_lo addr_RR len_ts nN_pos nE_pos tl_eq.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    pose proof (mc_local_facts _ _ _ _ _ _ _ _ _ 0%nat dRR st eq_refl) as (at_R & ns_R & wr_R & lo_R & _).
    pose proof (mc_ext_facts _ _ _ _ _ _ _ _ _ _ st opndN) as (at_N & cr_N & crl_N & _).
    pose proof (mc_opnd_sep_le _ _ _ _ _ _ _ _ _ 0%nat dRR dN st eq_refl opndN) as (sep_RN & op_RN).
    pose proof OPN as (_ & _ & _ & strd_N & _).
    step. step. step.
    eapply aevtM_cut.
    { eapply (HR2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq dRR dN lo).
      all: try rewrite spf_val.
      - exact heap_q.
      - exact at_R.
      - exact at_N.
      - exact sep_RN.
      - rewrite addr_RR. clear - strd_N SLO HLS. lia.
      - exact ns_R.
      - exact op_RN.
      - exact cr_N.
      - exact crl_N.
      - exact wr_R.
      - exact lo_R.
      - exact stk_q.
      - clear - SLO HLS; lia.
      - exact ACL.
      - clear - top_q HTOP; lia.
      - clear - SPA; lia.
      - exact DHI.
      - exact TP.
      - exact inv_q.
      - exact sok_q.
      - exact CA.
      - rewrite addr_RR. reflexivity.
      - reflexivity. }
    intros ms' mo' post.
    binop_post post m2 mo2 h2 LB2 d2 r2 cfg_eq inv2 stk2 frm2 top2 heap2 at2 out2 presx2 sok2 rel2.
    destruct rel2 as ((n_ok & r2_rng) & addr2 & _ & blk2).
    pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 0%nat dRR m2 mo2 h2 LB2 d2 st eq_refl heap2 top2 frm2 at2 out2 presx2 sok2 inv2 stk2 blk2) as st2.
    cbn [set_nth] in st2.
    destruct (mc_drop_local _ _ _ _ _ _ _ _ _ _ st2)
      as (st3 & fresh_T & sg2 & len2 & rng2 & _ & _ & _ & ns2 & null2 & heap_d2).
    cbn [app] in st3. unfold mpd_struct in st3. rewrite addr2, addr_RR in st3. apply cs_swap12 in st3.
    assert (rr2 : rr_ok d2).
    { split; [rewrite addr2; exact addr_RR|]. split; [exact len2|]. split; [exact rng2|]. split; [exact ns2|].
      split; [exact sg2|]. split; [exact null2|].
      intros own_h. destruct (heap_d2 own_h) as (_ & n1 & p_pos & p_lim & p_al & _).
      split; [exact n1|]. split; [exact p_pos|]. split; [exact p_lim| exact p_al]. }
    assert (ts2 : tstate m2 mo2 h2 LB2 dX d2 T tl ts).
    { exists lo16. split; [exact sz_lo|]. split; [exact st3|]. split; [exact rr2|]. split; [exact len_ts|].
      exact (Forall_inv fresh_T). }
    pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
    rewrite ret_pc_even by (cbn; lia).
    step. if_cases zero_flag.
    - unfold bv_eqb in zero_flag. apply Z.eqb_eq in zero_flag. rewrite !unsigned_lit_wrap in zero_flag.
      assert (r2_zero : r2 = 0) by (clear - zero_flag r2_rng; lia).
      specialize (n_ok r2_zero).
      destruct out2 as (_ & ns_out & _).
      eapply L_copy; [exact ts2| | exact nN_pos| exact n_ok| exact nE_pos| exact tl_eq].
      apply (out_heap _ _ _ at2 ns_out). lia.
    - eapply L_r2fail; [exact ts2| exact r2_rng].
  Qed.

  Lemma L_init : forall mq moq hq LBq lo16 c16 (T tl : Z) (ts : list word)
      (xra x6 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dX [(T, 4 * tl)] (frame lo16 c16) [(T, [CB (4 * length ts)%nat (u32s ts)])] ->
    cells_size lo16 = 16%nat -> cells_size c16 = 16%nat -> Z.of_nat (length ts) = tl -> 0 < T ->
    1 <= md_n dN -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) x6 (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21868.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HR2 HZF HCOPY HCMP HMOD HGROW HMMI HTOM HCEM HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq lo16 c16 T tl ts xra x6 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 st sz_lo sz_c len_ts T_pos nN_pos nE_pos tl_eq.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos.
    pose proof (cs_frame _ _ _ _ _ _ _ _ _ _ st) as (fr_lo & fr_c & fr_regs).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (_ & _ & _ & _ & inv_q & stk_q & _ & _ & mok_q).
    destruct (rw_cells_forget _ _ _ _ fr_c) as (junk & fr_j). rewrite sz_c in fr_j. clear fr_c.
    pose proof (munch_refl [(SP + -96, SP + -80)] mq) as mu.
    pose proof (wmono_refl usegs mq) as wm.
    step. step. step. step.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m1 end.
    set (rest := skipn 4 (skipn 8 junk)) in fr_j.
    assert (len_rest : length rest = 4%nat) by (destruct fr_j as ((wf & _) & _); cbn in wf; tauto).
    set (pad := le_bytes_to_word rest).
    apply (rw_cells_reshape _ _ _ _ (mpi_cells 0 (Z_to_bv 64 1) 0 pad)) in fr_j;
      [| cbn; tauto | cbn [cells_bytes cbytes mpi_cells]; unfold pad; rewrite le4_le_bytes_to_word by exact len_rest; reflexivity].
    pose proof (mc_hi_write _ _ _ _ _ _ _ _ _ (SP + -96) (SP + -80) [] m1 []
                  [(SP + -96, mpi_cells 0 (Z_to_bv 64 1) 0 pad); (SPc, lo16); (SP + -80, REGS)]
                  st mu wm inv_q stk_q ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl) as st1.
    assert (st2 : CST m1 moq hq LBq [] dX [(T, 4 * tl)] [(SP + -96, mpi_cells 0 (Z_to_bv 64 1) 0 pad); (SPc, lo16); (SP + -80, REGS)]
                    [(T, [CB (4 * length ts)%nat (u32s ts)])]).
    { apply st1.
      - intros j d d' nth_d. destruct j; discriminate nth_d.
      - constructor; [exact fr_j| constructor; [exact fr_lo| constructor; [exact fr_regs| constructor]]].
      - constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; rewrite ?sz_lo;
          cbn [cells_size csize mpi_cells Nat.add]; (split; [lia|]); (split; [lia|]); intros d []. }
    clear st1.
    pose proof (mc_intro_local _ _ _ _ _ _ _ _ _ (SP + -96) pad st2 ltac:(lia)) as st3.
    assert (st4 : CST m1 moq hq LBq [null_mpd (SP + -96) pad] dX [(T, 4 * tl)] [(SPc, lo16); (SP + -80, REGS)]
                    [(T, [CB (4 * length ts)%nat (u32s ts)])]).
    { apply st3.
      - constructor; [| constructor; [| constructor]]; cbn [fst snd]; rewrite ?sz_lo; cbn [cells_size csize Nat.add]; lia.
      - constructor. }
    step. if_true.
    eapply L_r2; [exact st4| exact sz_lo| reflexivity| exact len_ts| exact nN_pos| exact nE_pos| exact tl_eq].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L59314873579.12900000CS2ra2sp2dX1a2Ha1R1H". (* [comment removed for export] *)
  Lemma w_writable_SP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PCS,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-70.)VdX,$3>.R6.R5.R4.R3.(43.$:.)R2.(43.$9.)R1.(43.(34.$0.(8.$3?.))))(1:.VL,R4.(13.&40.Vsp,)(1;.$45.VL,VHI,R5.)R3.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq dW CS CS_.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros MWf NSW EA (WR1 & WR2 & WR3) _.
    pose proof CS_ as CS2. dest_cs CS2. flat constr:(WRX) 3%nat. flclear WRX. intros WW1 WW2 WW3.
    split; [| exact (conj WR2 WR3)].
    rewrite EA. intros a Ha. destruct (WW1 a Ha) as [C|[C|([B k] & Hb & R)]]; [left; rewrite HTc; exact C| right; left; exact C| right; right].
    exists (B, k). split; [| exact R]. apply SUB; [exact Hb|]. intros HW. flat constr:((mpd_blk_heap _ _ HW)) 2%nat. intros O E. injection E as -> ->. cbn in R. pose proof (WW3 O). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L59308743383.10500000YS1L3HLS2ra2sp2lo3SLO3ACL1a2Ha1B1k1R2S'2B4". (* [comment removed for export] *)
  Lemma ivs_SP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PCS,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-70.)VdX,$3>.R6.R5.R4.R3.(43.$:.)R2.(43.$9.)R1.(43.(34.$0.(8.$3?.))))Pa,$0.P,(31.(1=.=R1.)(32.R1.(3:.+2.+40.)))P,(69.VL,VLB,(13.&40.Vsp,)R2.)P,(6:.(68.VdX,)R3.)(31.(69.VL,R8.(13.&40.Vsp,)R4.)(6:.(68.R7.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq dW CS CS_ a Ha Hc Ho.
    flat constr:((mc_ivs_w _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros _ _ _ _ IVP. flat constr:((IVP a Ha Hc Ho)) 2%nat. intros C1 O1. split; [| exact O1].
    destruct Hc as [S|[D|([B k] & Hb & R)]]; [left; exact S| right; left; exact D|].
    destruct C1 as [S'|X]; [| right; exact X]. exfalso.
    flat constr:(facts0) 6%nat. flclear facts0. intros _ _ _ _ BR _. flat constr:((proj1 (Forall_forall _ _) BR _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in B4, R. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma L_e0 : forall mq moq hq LBq lo16 c16
      (xra x5 x6 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dX [] (frame lo16 c16) [] -> cells_size lo16 = 16%nat -> cells_size c16 = 16%nat ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) x5 x6 (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x218b0.
  Proof using L HI HLS SW DIMG HND ROIMG IMGC HLSET ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq lo16 c16 xra x5 x6 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 st sz_lo sz_c.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    pose proof (mc_w_facts _ _ _ _ _ _ _ _ _ st) as (at_w & ns_w & _ & wr_w & _).
    step. step. step.
    eapply aevtM_cut.
    { eapply (HLSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq dX 1 lo).
      all: try rewrite spf_val.
      - exact heap_q.
      - exact at_w.
      - exact ns_w.
      - exact wr_w.
      - lia.
      - exact stk_q.
      - clear - SLO HLS; lia.
      - exact ACL.
      - clear - top_q HTOP; lia.
      - clear - SPA; lia.
      - exact DHI.
      - exact TP.
      - exact inv_q.
      - exact sok_q.
      - exact CA.
      - reflexivity.
      - reflexivity. }
    intros ms' mo' post.
    binop_post post m2 mo2 h2 LB2 d2 r2 cfg_eq inv2 stk2 frm2 top2 heap2 at2 out2 presx2 sok2 rel2.
    destruct rel2 as (r2_cases & _ & blk2).
    assert (keep2 : md_pad d2 = md_pad dX /\ md_n dX <= md_n d2 /\ -2^31 < r2 <= 0).
    { destruct r2_cases as [(r_ok & n_eq & _ & _ & _ & pad_eq)|(r_bad & ->)];
        [split; [exact pad_eq| lia]| split; [reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in r_bad; lia]]. }
    destruct keep2 as (pad2 & n2 & r2_rng).
    pose proof (mc_binop_w _ _ _ _ _ _ _ _ _ m2 mo2 h2 LB2 d2 st heap2 top2 frm2 at2 out2 presx2 sok2 inv2 stk2 blk2 pad2 n2) as st2.
    pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
    rewrite ret_pc_even by (cbn; lia).
    step.
    eapply L_ret; [exact st2| exact sz_lo| exact sz_c| exact r2_rng].
  Qed.

  Lemma L_alloc : forall mq moq hq LBq lo16 c16
      (xra x5 x6 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dX [] (frame lo16 c16) [] -> cells_size lo16 = 16%nat -> cells_size c16 = 16%nat -> 1 <= md_n dN ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) x5 x6 (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21848.
  Proof using L HI HCALLOC HLS SW DIMG HND ROIMG IMGC HWL HLSET HR2 HZF HCOPY HCMP HMOD HGROW HMMI HTOM HCEM HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq lo16 c16 xra x5 x6 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 st sz_lo sz_c nN_pos.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    pose proof NN as nN_max.
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (heap_q & top_q & frm_q & sok_q & inv_q & stk_q & _ & _ & mok_q).
    pose proof (e_raw _ _ _ _ _ _ _ _ _ dE st opndE) as (cells_E & _ & _ & rng_E & _).
    pose proof (e_raw _ _ _ _ _ _ _ _ _ dN st opndN) as (cells_N & _ & _ & rng_N & _).
    unfold mpi_cells in cells_E, cells_N.
    step; try zsimp.
    replace (zx16 (Z_to_bv 64 (md_n dE))) with (Z_to_bv 64 (md_n dE))
      by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
    step.
    destruct (Z.eq_dec (md_n dE) 0) as [nE_zero | nE_nz].
    { rewrite nE_zero. if_true. eapply L_e0; [exact st| exact sz_lo| exact sz_c]. }
    if_false_x.
    step; try zsimp.
    replace (zx16 (Z_to_bv 64 (md_n dN))) with (Z_to_bv 64 (md_n dN))
      by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
    step.
    eapply aevtM_cut_evt; [exact mok_q| eapply (HWL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_n dN) (md_n dE))| ].
    - lia.
    - lia.
    - exact inv_q.
    - reflexivity.
    - reflexivity.
    - intros ms' post.
      destruct post as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ms_eq & _ & _ & _ & v0_eq).
      subst ms' v0.
      rewrite ret_pc_even by (cbn; lia).
      remember (exp_mod_working_limbs (md_n dN) (md_n dE)) as tl eqn:tl_eq.
      assert (tl_rng : 0 < tl <= 54990)
        by (rewrite tl_eq; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
      step. step. step.
      replace (Z_to_bv 64 260448) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
      eapply aevtM_cut.
      { eapply (heap_calloc usegs L HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LBq tl 4 lo).
        all: try rewrite spf_val.
        - exact heap_q.
        - exact stk_q.
        - exact ACL.
        - clear - SLO HLS; lia.
        - exact inv_q.
        - exact TP.
        - clear - top_q HTOP; lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - lia.
        - lia. }
      intros ms2 mo2 post2.
      destruct post2 as (w0 & w1 & w2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m2 & mo2'
                         & cfg_eq & inv2 & stk2 & frm2 & pres2 & h2 & top2 & outcome).
      injection cfg_eq as -> ->.
      rewrite spf_val in stk2, pres2.
      rewrite ret_pc_even by (cbn; lia).
      destruct outcome as [(-> & heap2) | (A & -> & range_A & heap2 & cells_A)].
      + pose proof (mc_heap_nop0 _ _ _ _ _ _ _ _ _ m2 mo2' h2 st heap2 top2 frm2 pres2 inv2 stk2) as st2.
        pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
        step. if_true. step. step.
        eapply L_ret; [exact st2| exact sz_lo| exact sz_c| lia].
      + pose proof range_A as (A_pos & _ & _ & A_lim & _).
        pose proof (@alloc_ceiling_bounds L) as ac_bnd.
        pose proof (mc_ex_alloc _ _ _ _ _ _ _ _ _ m2 mo2' h2 A (tl * 4) _ st heap2 top2 frm2 pres2 inv2 stk2 ltac:(lia) cells_A
                      ltac:(cbn [cells_size csize Nat.add]; lia)) as st2.
        assert (eq_bytes : repeat (Z_to_bv 8 0) (Z.to_nat (tl * 4)) = u32s (repeat (Z_to_bv 64 0) (Z.to_nat tl)))
          by (rewrite u32s_repeat0; f_equal; lia).
        assert (eq_size : Z.to_nat (tl * 4) = (4 * length (repeat (Z_to_bv 64 0) (Z.to_nat tl)))%nat)
          by (rewrite repeat_length; lia).
        rewrite eq_bytes, eq_size, (Z.mul_comm tl 4) in st2.
        pose proof (heap_mok _ _ HI _ _ _ _ heap2) as mok2.
        step. if_false_x.
        eapply L_init; [exact st2| exact sz_lo| exact sz_c| rewrite repeat_length; lia| exact A_pos| exact nN_pos| lia| exact tl_eq].
  Qed.

  Lemma L_C : forall mq moq hq LBq lo16 c16
      (xra x5 x6 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dX [] (frame lo16 c16) [] -> cells_size lo16 = 16%nat -> cells_size c16 = 16%nat -> 1 <= md_n dN ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) x5 x6 (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x217dc.
  Proof using L HI HCALLOC HLS SW DIMG HND ROIMG IMGC HCBL HCBLZ HWL HLSET HR2 HZF HCOPY HCMP HMOD HGROW HMMI HTOM HCEM HFROM HCZ HAS HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CREL CRN WRX SLO ACL HTOP SPA DHI TP CA.
    intros mq moq hq LBq lo16 c16 xra x5 x6 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 st sz_lo sz_c nN_pos.
    pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st) as (_ & _ & _ & _ & inv_q & _ & _ & _ & mok_q).
    pose proof (e_raw _ _ _ _ _ _ _ _ _ dE st opndE) as (cells_E & bytes_E & len_E & rng_E & _ & pz_E & nn_E & null_E).
    pose proof (e_raw _ _ _ _ _ _ _ _ _ dN st opndN) as (cells_N & bytes_N & len_N & rng_N & _ & pz_N & nn_N & null_N).
    unfold mpi_cells in cells_E, cells_N.
    pose proof ME0 as ((_ & al_E & pos_E & _) & _).
    pose proof (rw_cells_bound _ _ _ _ cells_E) as bnd_E. cbn [cells_size csize Nat.add] in bnd_E.
    assert (after_E : forall (u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 : word),
      RUN moq mq (mkR (Z_to_bv 64 0x217f4) SPF gp tp u0 u1 u2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) v0 v1 v2 v3 v4 v5 v6 v7
        (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) x5 x6 (Z_to_bv 64 0) x8 s9 s10 s11 u3 u4 u5 u6) 0x217f4).
    { intros u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6.
      step. step. if_cases big_E.
      - assert (nnull_N : md_own dN <> LNull) by (intros is_null; destruct (null_N is_null); lia).
        destruct (nn_N nnull_N) as (pN_pos & pN_lim & _).
        assert (pN_al : md_p dN mod 4 = 0) by (destruct pz_N as [|(_ & al)]; [lia| exact al]).
        step. step; try zsimp.
        replace (zx16 (Z_to_bv 64 (md_n dN))) with (Z_to_bv 64 (md_n dN))
          by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
        step.
        eapply aevtM_cut_evt; [exact mok_q| eapply (HCBL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_p dN) (md_n dN) (md_limbs dN))| ].
        + exact bytes_N.
        + exact rng_N.
        + lia.
        + exact pN_al.
        + exact pN_pos.
        + exact inv_q.
        + reflexivity.
        + reflexivity.
        + intros ms' post.
          destruct post as (w0 & w1 & w2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & ms_eq & _ & _ & _ & _).
          subst ms'.
          rewrite ret_pc_even by (cbn; lia).
          step. step. step. if_cases big_N.
          * eapply L_ret; [exact st| exact sz_lo| exact sz_c| lia].
          * eapply L_alloc; [exact st| exact sz_lo| exact sz_c| exact nN_pos].
      - step. eapply L_ret; [exact st| exact sz_lo| exact sz_c| lia]. }
    step. if_false_x. step. zsimp. land_zero_any. step. if_false.
    step. step; try zsimp.
    replace (zx16 (Z_to_bv 64 (md_n dE))) with (Z_to_bv 64 (md_n dE))
      by (unfold zx16; rewrite unsigned_lit, Z.mod_small by lia; reflexivity).
    step.
    destruct (Z.eq_dec (md_n dE) 0) as [nE_zero | nE_nz].
    - rewrite nE_zero.
      assert (pE_rng : 0 <= md_p dE < 2 ^ 64).
      { destruct (md_own dE) eqn:own_E.
        - destruct (null_E eq_refl) as (p0 & _). lia.
        - destruct (nn_E ltac:(discriminate)) as (p_pos & p_lim & _). lia.
        - destruct (nn_E ltac:(discriminate)) as (p_pos & p_lim & _). lia. }
      eapply aevtM_cut_evt; [exact mok_q| eapply (HCBLZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_p dE))| ].
      + exact inv_q.
      + exact pE_rng.
      + reflexivity.
      + reflexivity.
      + intros ms' post.
        destruct post as (w0 & w1 & w2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & ms_eq & _ & _ & _ & _).
        subst ms'.
        rewrite ret_pc_even by (cbn; lia).
        apply after_E.
    - assert (nnull_E : md_own dE <> LNull) by (intros is_null; destruct (null_E is_null); lia).
      destruct (nn_E nnull_E) as (pE_pos & pE_lim & _).
      assert (pE_al : md_p dE mod 4 = 0) by (destruct pz_E as [|(_ & al)]; [lia| exact al]).
      eapply aevtM_cut_evt; [exact mok_q| eapply (HCBL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (md_p dE) (md_n dE) (md_limbs dE))| ].
      + exact bytes_E.
      + exact rng_E.
      + lia.
      + exact pE_al.
      + exact pE_pos.
      + exact inv_q.
      + reflexivity.
      + reflexivity.
      + intros ms' post.
        destruct post as (w0 & w1 & w2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & ms_eq & _ & _ & _ & _).
        subst ms'.
        rewrite ret_pc_even by (cbn; lia).
        apply after_E.
  Qed.

  Lemma L_entry : forall (m1 : mem) (j32 : list (bv 8)) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
    munch [(lo, SP)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 -> stk usegs m1 lo SPc ->
    rw_cells usegs m1 SPc [CB 32 j32] -> rw_cells usegs m1 (SP + -80) REGS ->
    aevtM usegs mo POST (MS (mkR ra SPF gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dE))
      (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x21744) fc None m1 (seg_rom usegs)).
  Proof using L HI HCALLOC HLS SW DIMG HND ROIMG IMGC HCBL HCBLZ HWL HLSET HR2 HZF HCOPY HCMP HMOD HGROW HMMI HTOM HCEM HFROM HCZ HAS HCMPO HMF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRE CREL CRN WRX SLO ACL HTOP SPA DHI TP MI0 SOK0 CA.
    intros m1 j32 t0 t1 t2 a6 a7 t3 t4 t5 t6 mu1 wm1 inv1 stk1 fr32 frR.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos. pose proof (@alloc_ceiling_bounds L) as ac_bnd.
    apply (rw_cells_split_CB _ _ _ [] 32 j32 [] [16%nat; 16%nat]) in fr32; [| reflexivity].
    cbn [app mk_CB_cells] in fr32.
    apply (proj1 (rw_cells_app _ _ _ [CB 16 (firstn 16 j32)] [CB 16 (firstn 16 (skipn 16 j32))])) in fr32.
    destruct fr32 as (frA & frB). cbn [cells_size csize Nat.add] in frB.
    replace (SP + -112 + Z.of_nat 16) with (SP + -96) in frB by lia.
    assert (es_at : Forall (fun e => mpd_at usegs m LB e) es)
      by (unfold es; destruct ALIAS; repeat (apply Forall_cons; [assumption|]); apply Forall_nil).
    assert (apart0 : structs_apart []) by (intros i j di dj nth_i; destruct i; discriminate nth_i).
    pose proof (mc_init m1 [] (frame [CB 16 (firstn 16 j32)] [CB 16 (firstn 16 (skipn 16 j32))]) HH0 SOK0 MI0 MX0 es_at mu1 wm1 inv1 stk1
                  (Forall_nil _) apart0
                  ltac:(constructor; [exact frA| constructor; [exact frB| constructor; [exact frR| constructor]]])
                  (frame_chs [CB 16 (firstn 16 j32)] [CB 16 (firstn 16 (skipn 16 j32))] eq_refl eq_refl)) as st0.
    assert (spf_val : bv_unsigned SPF = SP + -112) by (apply unsigned_lit; lia).
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st0) as (_ & _ & _ & _ & _ & _ & _ & _ & mok0).
    pose proof (munch_refl [(SP + -112, SP + -80)] m1) as mu_f.
    pose proof (wmono_refl usegs m1) as wm_f.
    clear mu1 wm1.
    do 6 step. step. step; try zsimp. step; try zsimp. step; try zsimp. step. step.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m2 end.
    pose proof (mc_hi_write _ _ _ _ _ _ _ _ _ (SP + -112) (SP + -80) [] m2 [] (frame [CB 12 (firstn 12 (firstn 16 j32)); C4 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 (SP + -100)); C4 (Z_to_bv 64 65537); CB 4 (skipn 4 (skipn 8 (firstn 16 (skipn 16 j32))))])
                  st0 mu_f wm_f inv1 stk1 ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl) as st1.
    specialize (st1 ltac:(intros j d d' nth_d; destruct j; discriminate nth_d)
                    ltac:(constructor; [exact frA| constructor; [exact frB| constructor; [exact frR| constructor]]])
                    (frame_chs [CB 12 (firstn 12 (firstn 16 j32)); C4 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 (SP + -100)); C4 (Z_to_bv 64 65537); CB 4 (skipn 4 (skipn 8 (firstn 16 (skipn 16 j32))))] eq_refl eq_refl)).
    clear st0 mu_f wm_f.
    set (restB := skipn 4 (skipn 8 (firstn 16 (skipn 16 j32)))) in *.
    assert (len_restB : length restB = 4%nat) by (pose proof frB as ((wfB & _) & _); cbn in wfB; tauto).
    set (dT := mkMPD (SP + -96) 1 1 (SP + -100) [Z_to_bv 64 0] (le_bytes_to_word restB) LStatic).
    assert (tmp_ok : forall mx, rw_cells usegs mx SPc [CB 12 (firstn 12 (firstn 16 j32)); C4 (Z_to_bv 64 0)] -> rw_cells usegs mx (SP + -96) [C8 (Z_to_bv 64 (SP + -100)); C4 (Z_to_bv 64 65537); CB 4 (skipn 4 (skipn 8 (firstn 16 (skipn 16 j32))))] ->
                     stack_opnd usegs mx (bv_unsigned SPF) dT).
    { intros mx cellsA cellsB.
      assert (cellsT : rw_cells usegs mx (md_addr dT) (mpi_cells (md_p dT) (Z_to_bv 64 (md_sg dT)) (md_n dT) (md_pad dT))).
      { cbn [dT md_addr md_p md_sg md_n md_pad].
        eapply rw_cells_reshape; [exact cellsB| cbn; tauto| ].
        cbn [cells_bytes cbytes mpi_cells]. rewrite le4_le_bytes_to_word by exact len_restB.
        replace (le4 (Z_to_bv 64 65537)) with (le2 (Z_to_bv 64 1) ++ le2 (Z_to_bv 64 1))
          by (vm_compute; repeat (apply (f_equal2 (@cons byte)); [apply bv_eq; reflexivity|]); reflexivity).
        rewrite <- app_assoc. reflexivity. }
      assert (limbT : bytes_at usegs mx (SP + -100) (u32s [Z_to_bv 64 0])).
      { apply (proj1 (rw_cells_app _ _ _ [CB 12 (firstn 12 (firstn 16 j32))] [C4 (Z_to_bv 64 0)])) in cellsA.
        destruct cellsA as (_ & cellL). cbn [cells_size csize Nat.add] in cellL.
        replace (SP + -112 + Z.of_nat 12) with (SP + -100) in cellL by lia.
        exact (proj2 (proj1 cellL)). }
      rewrite spf_val. unfold stack_opnd. cbn [dT md_addr md_p md_sg md_n md_pad md_own md_limbs].
      split; [reflexivity|]. split; [exact cellsT|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
      split; [unfold MPI_MAX_LIMBS; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact limbT|].
      split; [lia|]. split; [lia| left; reflexivity]. }
    pose proof (mc_ext_facts _ _ _ _ _ _ _ _ _ _ st1 opndN) as (at_N1 & _ & _ & _ & hp_N1 & _).
    pose proof (e_raw _ _ _ _ _ _ _ _ _ dN st1 opndN) as (cells_N & bytes_N & len_N & rng_N & _ & pz_N & nn_N & null_N).
    unfold mpi_cells in cells_N.
    pose proof (cs_parts _ _ _ _ _ _ _ _ _ st1) as (_ & _ & _ & _ & inv2 & _ & _ & _ & _).
    assert (vT : mpd_val dT = 0) by (vm_compute; reflexivity).
    step. step. step.
    eapply aevtM_cut_evt; [exact mok0| eapply (HCMPO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LB dN dT)| ].
    - left. exact at_N1.
    - right. exact (tmp_ok m2 frA frB).
    - intros o. exact (proj1 (hp_N1 o)).
    - intros o. discriminate o.
    - exact inv2.
    - reflexivity.
    - reflexivity.
    - intros ms' post.
      destruct post as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & ms_eq & _ & _ & _).
      subst ms'.
      rewrite ret_pc_even by (cbn; lia).
      step. step. step.
      if_cases pos_flag.
      + eapply L_ret; [exact st1| reflexivity| reflexivity| lia].
      + zify_cond pos_flag.
        assert (val_pos : 0 < mpd_val dN - mpd_val dT).
        { destruct (Z.sgn_spec (mpd_val dN - mpd_val dT)) as [(gt & sg)|[(eq & sg)|(lt & sg)]];
            rewrite sg in pos_flag0, pos_flag1; [exact gt| lia| lia]. }
        assert (nN_pos : 1 <= md_n dN).
        { destruct (Z.eq_dec (md_n dN) 0) as [n_zero | n_nz]; [| lia].
          exfalso. assert (no_limbs : md_limbs dN = []) by (destruct (md_limbs dN); [reflexivity| cbn in len_N; lia]).
          rewrite vT in val_pos. unfold mpd_val in val_pos. rewrite no_limbs in val_pos. cbn in val_pos. lia. }
        assert (nnull_N : md_own dN <> LNull) by (intros is_null; destruct (null_N is_null); lia).
        destruct (nn_N nnull_N) as (pN_pos & pN_lim & _).
        assert (pN_al : md_p dN mod 4 = 0) by (destruct pz_N as [|(_ & al)]; [lia| exact al]).
        pose proof MN0 as ((_ & al_N & pos_N & _) & _).
        pose proof (rw_cells_bound _ _ _ _ cells_N) as bnd_N. cbn [cells_size csize Nat.add] in bnd_N.
        step. if_false_x. step. zsimp. land_zero_any. step. if_false.
        step. step. if_false_x. step. zsimp. land_zero_any. step. if_false.
        destruct (nth_error (u32s (md_limbs dN)) 0) as [b0|] eqn:nth_b0.
        2: { exfalso. apply nth_error_None in nth_b0. rewrite u32s_length in nth_b0. lia. }
        pose proof (u8ro_read _ _ _ _ 0 b0 _ bytes_N nth_b0 ltac:(lia) eq_refl) as rd_b0.
        step; try zsimp. step; try zsimp. step.
        if_cases even_flag.
        * eapply L_ret; [exact st1| reflexivity| reflexivity| lia].
        * pose proof (munch_refl [(SP + -112, SP + -80)] m2) as mu_g.
          pose proof (wmono_refl usegs m2) as wm_g.
          pose proof (cs_parts _ _ _ _ _ _ _ _ _ st1) as (_ & _ & _ & _ & _ & stk2 & _ & _ & _).
          clear rd_b0.
          step. step; try zsimp. step; try zsimp. step; try zsimp. step. step.
          lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m3 end.
          pose proof (mc_hi_write _ _ _ _ _ _ _ _ _ (SP + -112) (SP + -80) [] m3 [] (frame [CB 12 (firstn 12 (firstn 16 j32)); C4 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 (SP + -100)); C4 (Z_to_bv 64 65537); CB 4 (skipn 4 (skipn 8 (firstn 16 (skipn 16 j32))))])
                        st1 mu_g wm_g inv2 stk2 ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl) as st2.
          specialize (st2 ltac:(intros j d d' nth_d; destruct j; discriminate nth_d)
                          ltac:(constructor; [exact frA| constructor; [exact frB| constructor; [exact frR| constructor]]])
                          (frame_chs [CB 12 (firstn 12 (firstn 16 j32)); C4 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 (SP + -100)); C4 (Z_to_bv 64 65537); CB 4 (skipn 4 (skipn 8 (firstn 16 (skipn 16 j32))))] eq_refl eq_refl)).
          pose proof (mc_ext_facts _ _ _ _ _ _ _ _ _ _ st2 opndE) as (at_E2 & _ & _ & _ & hp_E2 & _).
          pose proof (cs_parts _ _ _ _ _ _ _ _ _ st2) as (_ & _ & _ & _ & inv3 & _ & _ & _ & _).
          step. step. step.
          eapply aevtM_cut_evt; [exact mok0| eapply (HCMPO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LB dE dT)| ].
          -- left. exact at_E2.
          -- right. exact (tmp_ok m3 frA frB).
          -- intros o. exact (proj1 (hp_E2 o)).
          -- intros o. discriminate o.
          -- exact inv3.
          -- reflexivity.
          -- reflexivity.
          -- intros ms2 post2.
             destruct post2 as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & ms_eq2 & _ & _ & _).
             subst ms2.
             rewrite ret_pc_even by (cbn; lia).
             step. if_cases neg_flag.
             ++ step. eapply L_ret; [exact st2| reflexivity| reflexivity| lia].
             ++ eapply L_C; [exact st2| reflexivity| reflexivity| exact nN_pos].
  Qed.
  End Walk.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L11075936116.108L17097338356.108L19685138523.108L19687428440.108L23124392564.108L25465666776.108L28125529944.108L29025845208.108L29135309044.108L31686769240.108L36180999398.105L41172169716.108L42780454045.108L43059266230.103L43679985268.107L5065130740.108 L55720577396.108L60692334296.108L61601561944.108L61747685364.108L62505661912.107L64270350808.108L65178513496.108L67541566890.107L67541566890.108L67758486644.10800000700>00E00L00S00Z00a00h00o01601=01D01K01c01j02102802?02F02M02T02[02b03=03X03_S2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1L3HLS2ra2sp2lo3SLO3SPBS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1L3HLS2ra2sp2lo3SLO3SPB2HBS1L3HLS2ra2sp2lo3SLO3SPB2HBS2ra2sp". (* [comment removed for export] *)
  Theorem U_mpi_exp_mod_spec : mpi_exp_mod_stmt_n usegs L HI U_MPI_EXP_MOD U_MEMSET_FUNC.
  Proof using L HI HCALLOC HLS SW DIMG HND ROIMG IMGC HCBL HCBLZ HWL HLSET HR2 HZF HCOPY HCMP HMOD HGROW HMMI HTOM HCEM HFROM HCZ HAS HCMPO HMF.
    unfold mpi_exp_mod_stmt_n, U_MPI_EXP_MOD.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB dX dA dE dN lo
      heap0 atX atA atE atN nN sXA sXE sXN nXE nXN nsX opA opE opN crA crAL crE crEL crN crNL wrX xlo stk0 slo acl htop spa dhi tp_eq
      inv0 ra2 sok0 ca ea0 ea1 ea2 ea3 ea4.
    subst a0 a1 a2 a3 a4.
    pose proof (bv_unsigned_in_range 64 sp) as sp_rng. change (bv_modulus 64) with (2^64) in sp_rng.
    pose proof alloc_ceiling_pos as ac_pos.
    pose proof (heap_mok _ _ HI _ _ _ _ heap0) as mok0.
    destruct (stk_carve _ _ _ _ 112 stk0 ltac:(cbn; lia)) as (stk1 & junk & fr112).
    change (Z.of_nat 112) with 112 in stk1, fr112.
    replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) in stk1, fr112 by lia.
    clear stk0.
    pose proof (conj heap0 (conj sok0 inv0)) as keep0. clear heap0 sok0.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as mu0.
    pose proof (wmono_refl usegs m) as wm0.
    do 5 step. do 10 step.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m1 end.
    destruct keep0 as (heap0 & sok_m & inv_m).
    apply (proj1 (rw_cells_app _ _ _ [CB 32 _] [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in fr112.
    destruct fr112 as (fr32 & frR). cbn [cells_size csize Nat.add] in frR.
    replace (bv_unsigned sp + -112 + Z.of_nat 32) with (bv_unsigned sp + -80) in frR by lia.
    exact (L_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB dX dA dE dN lo
             heap0 atX atA atE atN nN sXA sXE sXN nXE nXN nsX opA opE opN crA crE crEL crN wrX slo acl htop spa dhi tp_eq inv_m sok_m ca m1 _ t0 t1 t2 a6 a7 t3 t4 t5 t6 mu0 wm0 inv0 stk1 fr32 frR).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EM.
