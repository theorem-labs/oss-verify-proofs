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
  Notation SPc := (bv_unsigned sp + -112).
  Notation POST := (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (exp_mod_R LB dX dA dE dN) lo m mo).

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
  Proof.
    assert (FE : forall d, mpd_at usegs m LB d -> md_addr dX <> md_addr d -> mpd_sep dX d -> opnd_sep dX d lo SP -> client_range L LB lo (md_addr d) 16 ->
                 client_range L LB lo (md_addr d) 16 /\ (md_own d = LHeap -> In (md_p d, 4 * md_n d) LB)
                 /\ (md_addr d + 16 <= lo \/ SP <= md_addr d)
                 /\ (md_own dX = LHeap -> md_addr d + 16 <= md_p dX \/ md_p dX + 4 * md_n dX <= md_addr d)
                 /\ (md_own dX <> LHeap \/ md_own d = LNull \/ md_p dX + 4 * md_n dX <= md_p d \/ md_p d + 4 * md_n d <= md_p dX)
                 /\ (md_addr dX + 16 <= md_addr d \/ md_addr d + 16 <= md_addr dX)
                 /\ (md_own d <> LNull -> md_addr dX + 16 <= md_p d \/ md_p d + 4 * md_n d <= md_addr dX)).
    { intros d MD NE SEP (O1 & O2 & O3 & O4 & O5) CR. flat constr:(MD) 2%nat. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ _ HOB.
      split; [exact CR|]. split; [intros O; rewrite O in HOB; exact (proj1 (proj2 HOB))|]. split; [exact O4|]. split; [exact O2|].
      split. { destruct O3 as [E|X]; [exfalso; apply NE; rewrite E; reflexivity| exact X]. }
      split. { destruct SEP as [E|X]; [exfalso; apply NE; rewrite E; reflexivity| exact X]. }
      exact O1. }
    unfold es, ALIAS. destruct (Z.eqb_spec (md_addr dX) (md_addr dA)) as [AL|NAL].
    - constructor; [exact (FE dE ME0 NXE SXE OPE CRE)|]. constructor; [exact (FE dN MN0 NXN SXN OPN CRN)| constructor].
    - constructor; [exact (FE dA MA0 NAL SXA OPA CRA)|]. constructor; [exact (FE dE ME0 NXE SXE OPE CRE)|]. constructor; [exact (FE dN MN0 NXN SXN OPN CRN)| constructor].
  Qed.

  Lemma opndA : In dA es \/ dA = dX.
  Proof. unfold es. destruct ALIAS eqn:AL; [right; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0)))))) AL)| left; left; reflexivity]. Qed.
  Lemma opndE : In dE es.
  Proof. unfold es. destruct ALIAS; [left; reflexivity| right; left; reflexivity]. Qed.
  Lemma opndN : In dN es.
  Proof. unfold es. destruct ALIAS; [right; left; reflexivity| right; right; left; reflexivity]. Qed.

  (* [comment removed for export] *)
  Notation CST := (cstate usegs L HI h LB mo m SP lo SPc dX es).
  Local Ltac mc_inst H :=
    exact (H usegs L HI HLS DIMG HND IMGC SW ROIMG h LB mo m SP lo SPc dX es
             ACL ltac:(lia) ltac:(lia) HTOP (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0))))))) DHI NSX WRX
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
  Local Ltac mc_inst' H :=
    exact (H usegs L HI HLS DIMG HND IMGC SW ROIMG h LB SP lo SPc dX es
             ACL ltac:(lia) ltac:(lia) HTOP (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0))))))) DHI NSX WRX
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
  Proof.
    intros mq LBq d [(_ & _ & _ & _ & _ & HO) _] NS N1. destruct (md_own d) eqn:O; [| reflexivity| exfalso; exact (NS eq_refl)].
    flat constr:(HO) 2%nat. flclear HO. intros _ N0. lia.
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
  Proof.
    intros until t6. intros CS_ SZL SZ Hr.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 3%nat. intros CL CH0 CHR.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ ltac:(constructor))) 11%nat. intros HH HT MF MW OUT BK PX SOK MI ST _.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    do 10 zstep.
    release_frame CL ST (bv_unsigned sp + -96). release_frame CH0 ST (bv_unsigned sp + -80). release_frame CHR ST (bv_unsigned sp).
    zstep. zstep.
    apply aevtM_done. unfold mpi_binop_post. do 14 eexists. exists mq, moq, hq, LBq, dW, r.
    split; [rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|]. split; [exact HH|]. split; [exact MW|]. split; [exact OUT|].
    split; [exact PX|]. split; [exact SOK|]. split; [exact Hr| exact BK].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
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
  Proof.
    intros until t6. intros CS_ SZL RR Hr.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof RR as RR0. flat constr:(RR0) 7%nat. flclear RR0. intros EAR HLR HNR NSR SGR RN RH.
    destruct (rr_lift _ _ _ _ _ _ _ CS_ SZL RR) as [CSL MDR]. clear CS_.
    pose proof CSL as CS2. dest_cs CS2.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    zstep. zstep. zstep.
    pose proof HMF as SF. unfold mpi_free_stmt, U_MPI_FREE in SF.
    flat constr:(MDR) 2%nat. intros MAR _.
    eapply aevtM_cut.
    { eapply SF with (lo := lo) (h := hq) (LB := LBq) (X := md_addr dR); rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by lia;
        first [ exact HH | exact MAR | exact NSR | exact TP | exact MI | exact SOK | exact CA | exact ACL | exact DHI | exact ST | reflexivity
              | (intros a Ha; left; rewrite EAR in Ha; split; [lia| rewrite HTc; lia])
              | (intros O; flat constr:((RH O)) 4%nat; intros N1 P0 P4 P16; rewrite EAR; right; lia)
              | (intros a Ha Hd; exfalso; rewrite EAR in Ha; clear - Ha Hd DHI ACL SLO HLS; lia)
              | (rewrite EAR; f_equal; lia)
              | clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_free_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2 mo2 h2 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by lia.
    flat constr:(PO) 8%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 RW2 PX2 SOK2.
    replace (ret_pc (Z_to_bv 64 0x21a20)) with (Z_to_bv 64 0x21a20) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (mc_free_local _ _ _ _ _ _ _ _ _ 0%nat dR _ _ _ _ CSL eq_refl HH2 HT2 MF2 PX2 SOK2 MI2 ST2 RW2) as CSF.
    cbn [set_nth] in CSF.
    destruct (mc_drop_local _ _ _ _ _ _ _ _ _ _ CSF) as [CSD _].
    cbn [app mpd_blk mpd_cx mpd_struct md_own md_addr md_p md_sg md_n md_pad md_limbs] in CSD. rewrite EAR in CSD.
    pose proof (rr_perm _ _ _ _ _ _ _ CSD) as CS3.
    clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    zstep. zstep.
    eapply L_ret; [exact CS3| exact SZL| reflexivity| exact Hr].
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
  Proof.
    intros until t6. intros CS_ SZL SZ TL NIN RB RE RR K. flat constr:(RR) 3%nat. intros _ HLR _.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    pose proof CS_ as CS2. flat constr:(CS2) 21%nat. flclear CS2. intros _ _ _ _ _ _ _ _ EXOK _ _ _ _ _ _ _ _ _ _ CXH _.
    flat constr:((Forall_inv EXOK)) 4%nat. intros INT _ _ KP. cbn [snd] in KP. pose proof (Forall_inv CXH) as CXT. cbn [fst snd] in CXT.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BR _. flat constr:((proj1 (Forall_forall _ _) BR _ INT)) 5%nat. intros T0 _ _ T4 _. cbn in T0, T4.
    pose proof HZF as SZF. unfold zeroize_and_free_stmt in SZF.
    eapply aevtM_cut.
    { eapply SZF with (buf := T) (len := 4 * tl) (lo := lo) (h := hq) (LB := LBq) (junk := u32s ts); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc TL KP T0 T4; lia).
      all: try (right; split; [exact INT|]; replace (Z.to_nat (4 * tl)) with (4 * length ts)%nat by lia; exact CXT).
      all: match goal with |- ?gg => idtac "REMAIN" gg end. }
    clear SZF. cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    flat constr:(PO) 26%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 E MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
    injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
    replace (ret_pc (Z_to_bv 64 RET)) with (Z_to_bv 64 RET) by (symmetry; apply ret_pc_even; [lia| exact RE]).
    eapply K.
    eapply mc_ex_free; [exact CS_| reflexivity| exact NIN| exact HH2| exact HT2| exact MF2| exact PX2| exact SOK2| exact MI2| exact ST2| |].
    - apply Forall_forall. intros ac Hac. right. exact Hac.
    - unfold mpd_cx, mpd_blk. destruct (md_own dR); [constructor| | constructor]. constructor; [| constructor]. cbn [fst snd].
      exists (md_p dR, 4 * md_n dR). split; [left; reflexivity|]. cbn [fst snd cells_size csize Nat.add]. rewrite <- HLR. lia.
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.

  Definition tstate mq moq hq LBq dW dR T tl ts : Prop :=
    exists lo16, cells_size lo16 = 16%nat /\
      CST mq moq hq LBq [] dW ((T, 4 * tl) :: mpd_blk dR) (frame lo16 (rr_cells dR)) ((T, [CB (4 * length ts)%nat (u32s ts)]) :: mpd_cx dR) /\
      rr_ok dR /\ Z.of_nat (length ts) = tl /\ ~ In (T, 4 * tl) (mpd_blk dR).

  Lemma L_clean1 : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word) (r : Z)
      (xra x2 x3 x4 x7 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> -2^31 < r <= 0 ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 r) a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 tl) (Z_to_bv 64 T) x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x2193c.
  Proof.
    intros until t6. intros (lo16 & SZL & CS_ & RR & TL & NIN) Hr.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    pose proof CS_ as CS2. flat constr:(CS2) 10%nat. flclear CS2. intros _ _ _ _ _ _ _ _ EXOK _.
    flat constr:((Forall_inv EXOK)) 4%nat. intros INT _ _ KP. cbn [snd] in KP.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BR _. flat constr:((proj1 (Forall_forall _ _) BR _ INT)) 5%nat. intros T0 _ _ T4 _. cbn in T0, T4.
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
    replace (tl * 4) with (4 * tl) by lia.
    eapply call_zf_T; [exact CS_| exact SZL| reflexivity| exact TL| exact NIN| lia| reflexivity| exact RR|].
    clear mq moq hq LBq CS_ HH HTc MF SOK MI ST MK EXOK INT KP BR T0 T4.
    intros m2 mo2 h2 LB2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CS2.
    reopen CS2 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity].
    zstep.
    eapply L_clean2; [exact CS2| exact SZL| exact RR| exact Hr].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.

  Lemma L_clean1' : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word) (r : Z)
      (xra x1 x2 x3 x4 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> -2^31 < r <= 0 ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) x1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 tl) (Z_to_bv 64 T) x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x21938.
  Proof.
    intros until t6. intros TS Hr. pose proof TS as (lo16 & _ & CS_ & _). reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. eapply L_clean1; [exact TS| exact Hr].
  Qed.

  Lemma L_r2fail : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word) (r : Z)
      (xra x0 x1 x2 x3 x4 x7 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> -2^31 < r <= 0 ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 x0 x1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 tl) (Z_to_bv 64 T) x7 x8 s9 s10 s11 t3 t4 t5 t6) 0x218d8.
  Proof.
    intros until t6. intros (lo16 & SZL & CS_ & RR & TL & NIN) Hr.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    pose proof CS_ as CS2. flat constr:(CS2) 10%nat. flclear CS2. intros _ _ _ _ _ _ _ _ EXOK _.
    flat constr:((Forall_inv EXOK)) 4%nat. intros INT _ _ KP. cbn [snd] in KP.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BR _. flat constr:((proj1 (Forall_forall _ _) BR _ INT)) 5%nat. intros T0 _ _ T4 _. cbn in T0, T4.
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep. zstep.
    replace (tl * 4) with (4 * tl) by lia.
    eapply call_zf_T; [exact CS_| exact SZL| reflexivity| exact TL| exact NIN| lia| reflexivity| exact RR|].
    clear mq moq hq LBq CS_ HH HTc MF SOK MI ST MK EXOK INT KP BR T0 T4.
    intros m2 mo2 h2 LB2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CS2.
    reopen CS2 HH HTc MF SOK MI ST MK.
    zstep. zstep.
    eapply L_clean2; [exact CS2| exact SZL| exact RR| exact Hr].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
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
  Proof.
    intros until e. intros CS_ He. flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ _ CS_ He)) 6%nat. intros ME _ _ _ HFE _.
    destruct (mpd_raw _ _ _ _ ME ltac:(intros O; exact (proj1 (HFE O)))) as (HR & HB & HL & HN & SG & _ & PB).
    split; [exact HR|]. split; [exact HB|]. split; [exact HL|]. split; [exact HN|]. split; [exact SG|]. split; [exact PB|].
    flat constr:(ME) 2%nat. intros FLt9 _. flat constr:(FLt9) 6%nat. flclear FLt9. intros _ _ _ _ _ HO. split.
    - intros NNL. pose proof CS_ as CS2. dest_cs CS2. destruct (mpd_limbs_low usegs L HI HLS DIMG HND IMGC SW ROIMG h LB SP lo SPc dX es ACL ltac:(lia) ltac:(lia) HTOP
                 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0))))))) DHI NSX WRX (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok
                 _ _ _ _ _ HH ME NNL) as [P0 P4].
      split; [exact P0|]. split; [exact P4|]. destruct (md_own e); [exfalso; exact (NNL eq_refl)| exact (proj1 HO)| exact (proj1 HO)].
    - intros O. rewrite O in HO. exact HO.
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
  Proof.
    intros until t6. intros TS. pose proof TS as (lo16 & SZL & CS_ & RR & TL & NIN).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 6%nat. intros MN CRN_ CRNL_ LN HFN ASN.
    flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 2%nat. intros SWN OWN.
    flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros SWW OWW.
    pose proof HAS as SA. unfold add_sub_mpi_stmt_e, U_ADD_SUB_MPI in SA.
    eapply aevtM_cut.
    { eapply (SA 1 ltac:(left; reflexivity)) with (dX := dW) (dA := dN) (dB := dW) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?EA; reflexivity).
      destruct SWN as [E|[X|X]]; [left; symmetry; exact E| right; right; exact X| right; left; exact X]. }
    clear SA. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
    replace (ret_pc (Z_to_bv 64 0x21ac0)) with (Z_to_bv 64 0x21ac0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR2) 2%nat. flclear RR2. intros R1 FLt17. flat constr:(FLt17) 4%nat. flclear FLt17. intros EA2 PAD2 FRB2 NLE2.
    assert (TS2 : tstate m2 mo2 h2 LB2 dW2 dR T tl ts).
    { exists lo16. split; [exact SZL|]. split; [| exact (conj RR (conj TL NIN))].
      eapply mc_binop_w; [exact CS_| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB2| exact PAD2| exact NLE2]. }
    assert (Hr : -2^31 < r <= 0) by (destruct R1 as [[-> _]| ->]; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia).
    clear CS_ MA2 OUT2 PX2. pose proof TS2 as (lo2 & _ & CS2 & _). reopen CS2 HH HTc MF SOK MI ST MK.
    zstep. eapply L_clean1'; [exact TS2| exact Hr].
  Qed.

  Local Ltac cond_decide :=
    unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
    repeat match goal with
      | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
      | |- context [Z.ltb ?x ?y] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
      | |- context [Z.eqb ?x ?y] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
      | |- context [Z.b2z ?b] => progress cbn [Z.b2z]
      | |- context [negb ?b] => progress cbn [negb]
      | |- context [Z.lxor ?x ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
    end; reflexivity.
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
  Proof.
    intros until t6. intros TS OW EN1. pose proof TS as (lo16 & SZL & CS_ & RR & TL & NIN).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((a_cells _ _ _ _ _ _ _ _ _ CS_)) 6%nat. intros pa sga na pada CA_ SGA. unfold mpi_cells in CA_.
    pose proof MA0 as [(_ & AAL & APOS & _) _]. pose proof (rw_cells_bound _ _ _ _ CA_) as AB16. cbn [cells_size csize Nat.add] in AB16.
    zstep; if_false_x. zstep. land_zero_any. zstep. if_false.
    zstep. zstep. zstep. zstep; if_cases K0; zify_cond K0.
    { zstep. zstep. eapply L_clean1; [exact TS| lia]. }
    clear K0 CA_ SGA AB16.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 8%nat. intros CE_ BE HLE HNE _ PBE HFE _. unfold mpi_cells in CE_.
    destruct PBE as [N0|[PE0 PE4]]; [exfalso; lia|].
    pose proof (u32s_length (md_limbs dE)) as ULE. pose proof (u32ro_bound _ _ _ _ BE) as BEB.
    zstep. zstep; if_false_x. zstep. land_zero_any. zstep. if_false. rd8 BE 0. zstep. zstep; if_cases K1; zify_cond K1.
    2:{ zstep. zstep. eapply L_clean1; [exact TS| lia]. }
    clear K1 CE_ BE.
    flat constr:((w_cells _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CW SGW HLW HNW EAW. unfold mpi_cells in CW. unfold MPI_MAX_LIMBS in HNW.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 9%nat. intros FLt18 NSW _ _ LW _ _ HFW _. flat constr:(FLt18) 2%nat. flclear FLt18. intros FLt19 _. flat constr:(FLt19) 6%nat. flclear FLt19. intros _ _ _ _ _ HOW.
    rewrite OW in HOW. flat constr:(HOW) 4%nat. flclear HOW. intros NW1 _ PALW UW. flat constr:((HFW OW)) 3%nat. intros PW0 PW4 _.
    zstep. zstep. rewrite zx16_small by lia. zstep.
    pose proof HCZ as SCZ. unfold mpi_core_check_zero_ct_stmt, U_MPI_CORE_CHECK_ZERO_CT in SCZ.
    assert (PALW4 : md_p dW mod 4 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in PALW; [| lia]; (flat constr:(PALW) 2%nat; flclear PALW; intros k Hk); exists (4 * k); lia).
    eapply aevtM_cut_evt; [exact MK| eapply SCZ with (A := md_p dW) (n := md_n dW) (xs := md_limbs dW); try reflexivity;
      first [exact (u32arr_ro _ _ _ _ UW)| exact MI| exact PALW4| lia] |].
    clear SCZ. cbv beta. intros ms' PO. unfold mpi_core_check_zero_ct_post in PO.
    flat constr:(PO) 23%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? z -> _ _ _ -> Z0 _.
    replace (ret_pc (Z_to_bv 64 0x21a9c)) with (Z_to_bv 64 0x21a9c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    set (sg' := if z =? 0 then 1 else -1).
    assert (SG' : sg' = 1 \/ sg' = -1) by (subst sg'; destruct (z =? 0); [left| right]; reflexivity).
    pose proof (munch_refl [(md_addr dX, md_addr dX + 16)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    unfold ct_mask. destruct (Z.eqb_spec z 0) as [Ez|Nz].
    - zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      match goal with H : rw_cells usegs m1 (md_addr dX) _ |- _ => rename H into CW1 end.
      assert (TS1 : tstate m1 moq hq LBq (set_sg dW 1) dR T tl ts).
      { exists lo16. split; [exact SZL|]. split; [| exact (conj RR (conj TL NIN))]. eapply mc_sign_w; [exact CS_| rewrite EAW; exact MU| exact WM| assumption| rewrite EAW; unfold mpi_cells; exact CW1| left; reflexivity]. }
      clear CS_ MU WM CW1.
      eapply L_addfix. exact TS1.
    - zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      match goal with H : rw_cells usegs m1 (md_addr dX) _ |- _ => rename H into CW1 end.
      assert (TS1 : tstate m1 moq hq LBq (set_sg dW (-1)) dR T tl ts).
      { exists lo16. split; [exact SZL|]. split; [| exact (conj RR (conj TL NIN))]. eapply mc_sign_w; [exact CS_| rewrite EAW; exact MU| exact WM| assumption| rewrite EAW; unfold mpi_cells; exact CW1| right; reflexivity]. }
      clear CS_ MU WM CW1.
      eapply L_addfix. exact TS1.
  Qed.

  Lemma L_core3 : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dW = LHeap -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dW -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21a34.
  Proof.
    intros until t6. intros TS OW OR N1 NLE NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    assert (TL2 : 2 * md_n dN + 1 <= tl) by (rewrite TLE; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    pose proof TS as (lo16 & SZL & CS_ & RR_ & _ & NIN). kit TS OW OR N1 E1. reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep. rewrite zx16_small by lia. zstep. zstep. zstep. zstep.
    pose proof HFROM as STM. unfold mpi_core_from_mont_rep_stmt, U_MPI_CORE_FROM_MONT_REP in STM.
    eapply aevtM_cut_evt; [exact MK| eapply STM with (X := md_p dW) (A := md_p dW) (N := md_p dN) (an := md_n dN) (T := T) (lo := lo)
        (xs := md_limbs dW) (ys := md_limbs dW) (ns := md_limbs dN) (ts := ts);
        unfold MPI_CORE_FROM_MONT_REP_STACK; rewrite ?unsigned_lit by lia;
        first [ exact UW | exact (u32arr_ro _ _ _ _ UW) | exact RON | exact UT | exact MI | exact ST | reflexivity
              | apply mod16_4; assumption | assumption
              | clear - N1 HNN HLN HLE HNE HLW HNW NLE NLR HLR HNR TL TL2; lia
              | clear - PW0 PW4 T0 T4 PR0 PR4 PN0 PN4 N1 HLW HLR HLN TL ACL SLO SPB HLS SPA; lia
              | rewrite ?HLW, ?HLR, ?HLN, ?HLE, ?TL; assumption ] |].
    clear STM. cbv beta. intros ms' PO. unfold mpi_core_from_mont_rep_post in PO. unfold MPI_CORE_FROM_MONT_REP_STACK in PO.
    flat constr:(PO) 29%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 xs2 ts2 -> MU2 WM2 MI2 UX2 LX2 _ UT2 LT2 _ ST2.
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x21a50)) with (Z_to_bv 64 0x21a50) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (TS2 : tstate m2 moq hq LBq (set_limbs dW xs2) dR T tl ts2).
    { eapply (core_munch _ _ _ _ _ _ _ _ _ _ (md_n dN) (2 * md_n dN + 1) 208); [exact TS| exact OW| exact OR| | exact WM2| exact MI2| exact ST2| lia| lia| lia
        | clear - SLO HLS; lia| exact UX2| rewrite <- HLW, <- LX2; reflexivity| exact UT2| exact LT2].
      exact MU2. }
    pose proof TS2 as (lo16' & _ & CS2 & _). reopen CS2 HH HTc MF SOK MI ST MK.
    eapply L_tail; [exact TS2| exact OW| exact E1].
  Qed.

  Lemma L_core2 : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dW = LHeap -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dW -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x219dc.
  Proof.
    intros until t6. intros TS OW OR N1 NLE NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof TS as (lo16 & SZL & CS_ & RR_ & _ & NIN). kit TS OW OR N1 E1. reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep. rewrite zx16_small by lia. zstep. zstep. rewrite zx16_small by lia. zstep. zstep. zstep.
    zstep; if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; cbn; lia].
    clear K0. zstep. zstep. zstep.
    pose proof HCEM as STM. unfold mpi_core_exp_mod_stmt, U_MPI_CORE_EXP_MOD in STM.
    eapply aevtM_cut_evt; [exact MK| eapply STM with (X := md_p dW) (A := md_p dW) (N := md_p dN) (an := md_n dN) (E := md_p dE) (en := md_n dE) (RR := md_p dR) (T := T) (lo := lo)
        (xs := md_limbs dW) (ys := md_limbs dW) (ns := md_limbs dN) (es := md_limbs dE) (rs := md_limbs dR) (ts := ts); try reflexivity |].
    { unfold mpi_core_exp_mod_pre, MPI_CORE_EXP_MOD_STACK. rewrite ?unsigned_lit by lia. rewrite <- TLE.
      repeat match goal with |- _ /\ _ => split end;
        first [ exact UW | exact (u32arr_ro _ _ _ _ UW) | exact RON | exact ROE | exact ROR | exact UT | exact MI | exact ST | reflexivity
              | apply mod16_4; assumption | assumption
              | clear - N1 E1 HNN HLN HLE HNE HLW HNW NLE NLR HLR HNR TL; lia
              | clear - PW0 PW4 T0 T4 PR0 PR4 PN0 PN4 PE0 PE4 N1 E1 HLW HLR HLN HLE TL ACL SLO SPB HLS SPA; lia
              | rewrite ?HLW, ?HLR, ?HLN, ?HLE, ?TL; assumption ]. }
    clear STM. cbv beta. intros ms' PO. unfold mpi_core_exp_mod_post in PO. unfold MPI_CORE_EXP_MOD_STACK in PO.
    flat constr:(PO) 28%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 xs2 ts2 -> MU2 WM2 MI2 UX2 LX2 _ UT2 LT2 ST2.
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia. rewrite TL in MU2.
    replace (ret_pc (Z_to_bv 64 0x21a34)) with (Z_to_bv 64 0x21a34) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (TS2 : tstate m2 moq hq LBq (set_limbs dW xs2) dR T tl ts2).
    { eapply (core_munch _ _ _ _ _ _ _ _ _ _ (md_n dN) tl 400); [exact TS| exact OW| exact OR| | exact WM2| exact MI2| exact ST2| lia| lia| lia
        | clear - SLO HLS; lia| exact UX2| rewrite <- HLW, <- LX2; reflexivity| exact UT2| exact LT2].
      exact MU2. }
    pose proof TS2 as (lo16' & _ & CS2 & _). reopen CS2 HH HTc MF SOK MI ST MK.
    eapply L_core3; [exact TS2| exact OW| exact OR| exact N1| exact NLE| exact NLR| exact E1| exact TLE].
  Qed.

  Lemma L_core : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dW = LHeap -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dW -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x219b0.
  Proof.
    intros until t6. intros TS OW OR N1 NLE NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    assert (TL2 : 2 * md_n dN + 1 <= tl) by (rewrite TLE; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    pose proof TS as (lo16 & SZL & CS_ & RR_ & _ & NIN). kit TS OW OR N1 E1. reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep.
    pose proof HMMI as SMI. unfold mpi_core_montmul_init_stmt, U_MPI_CORE_MONTMUL_INIT in SMI.
    eapply aevtM_cut_evt; [exact MK| eapply SMI with (N := md_p dN) (ns := md_limbs dN); first [exact RON| exact MI| exact PALN| reflexivity| lia] |].
    clear SMI. cbv beta. intros ms' PO. unfold mpi_core_montmul_init_post in PO.
    flat constr:(PO) 19%nat. flclear PO. intros ? ? ? wmm ? ? ? ? ? ? ? ? ? ? ? -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x219b8)) with (Z_to_bv 64 0x219b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. zstep. rewrite zx16_small by lia. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof HTOM as STM. unfold mpi_core_to_mont_rep_stmt, U_MPI_CORE_TO_MONT_REP in STM.
    eapply aevtM_cut_evt; [exact MK| eapply STM with (X := md_p dW) (A := md_p dW) (RR := md_p dR) (N := md_p dN) (an := md_n dN) (T := T) (lo := lo)
        (xs := md_limbs dW) (ys := md_limbs dW) (rs := md_limbs dR) (ns := md_limbs dN) (ts := ts);
        unfold MPI_CORE_MONTMUL_STACK; rewrite ?unsigned_lit by lia;
        first [ exact UW | exact (u32arr_ro _ _ _ _ UW) | exact ROR | exact RON | exact UT | exact MI | exact ST | reflexivity
              | apply mod16_4; assumption | assumption
              | clear - N1 HNN HLN HLE HNE HLW HNW NLE NLR HLR HNR TL TL2; lia
              | clear - PW0 PW4 T0 T4 PR0 PR4 PN0 PN4 N1 HLW HLR HLN TL ACL SLO SPB HLS SPA; lia
              | rewrite ?HLW, ?HLR, ?HLN, ?HLE, ?TL; assumption ] |].
    clear STM. cbv beta. intros ms' PO. unfold mpi_core_montmul_post in PO. unfold MPI_CORE_MONTMUL_STACK in PO.
    flat constr:(PO) 29%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 xs2 ts2 -> MU2 WM2 MI2 UX2 LX2 _ UT2 LT2 _ ST2.
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x219dc)) with (Z_to_bv 64 0x219dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (TS2 : tstate m2 moq hq LBq (set_limbs dW xs2) dR T tl ts2).
    { eapply (core_munch _ _ _ _ _ _ _ _ _ _ (md_n dN) (2 * md_n dN + 1) 192); [exact TS| exact OW| exact OR| | exact WM2| exact MI2| exact ST2| lia| lia| lia
        | clear - SLO HLS; lia| exact UX2| rewrite <- HLW, <- LX2; reflexivity| exact UT2| exact LT2].
      exact MU2. }
    pose proof TS2 as (lo16' & _ & CS2 & _). reopen CS2 HH HTc MF SOK MI ST MK.
    eapply L_core2; [exact TS2| exact OW| exact OR| exact N1| exact NLE| exact NLR| exact E1| exact TLE].
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
  Proof.
    intros until t6. intros TS OR N1 NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof TS as (lo16 & SZL & CS_ & RR & TL & NIN). reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((w_cells _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CW SGW HLW HNW EAW. unfold mpi_cells in CW. unfold MPI_MAX_LIMBS in HNW.
    pose proof MX0 as [(_ & XAL & XPOS & _) _]. pose proof (rw_cells_bound _ _ _ _ CW) as XB16. cbn [cells_size csize Nat.add] in XB16.
    zstep; if_false_x. zstep. land_zero_any. zstep. if_false. zstep.
    pose proof (munch_refl [(md_addr dX, md_addr dX + 16)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : rw_cells usegs m1 (md_addr dX) _ |- _ => rename H into CW1 end.
    assert (TS1 : tstate m1 moq hq LBq (set_sg dW 1) dR T tl ts).
    { exists lo16. split; [exact SZL|]. split; [| exact (conj RR (conj TL NIN))].
      eapply mc_sign_w; [exact CS_| rewrite EAW; exact MU| exact WM| assumption| rewrite EAW; unfold mpi_cells; exact CW1| left; reflexivity]. }
    clear CS_ MU WM CW1. pose proof TS1 as (lo1 & _ & CS1 & _). reopen CS1 HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS1)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS1 opndN)) 6%nat. intros MN CRN_ CRNL_ LN HFN ASN.
    pose proof HCMP as SC. unfold mpi_cmp_mpi_stmt, U_MPI_CMP_MPI in SC.
    eapply aevtM_cut_evt; [exact MK| eapply SC with (dX := set_sg dW 1) (dY := dN) (LB := LBq);
      [exact MW| exact MN| intros O; exact (proj1 (HFW O))| intros O; exact (proj1 (HFN O))| exact MI| cbn [set_sg md_addr] in EA |- *; rewrite ?EA; reflexivity| reflexivity] |].
    clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO.
    flat constr:(PO) 18%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x21988)) with (Z_to_bv 64 0x21988) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (Z.sgn_spec (mpd_val (set_sg dW 1) - mpd_val dN)) as SG.
    assert (GROW : forall mq' moq' hq' LBq' dW' (yra y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
      tstate mq' moq' hq' LBq' dW' dR T tl ts ->
      aevtM usegs moq' POST
        (MS (mkR yra SPF gp tp y0 y1 y2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 y3 y4 y5 y6)
            F (Z_to_bv 64 0x219a0) fc None mq' (seg_rom usegs))).
    {
      intros until y6. intros TS'. pose proof TS' as (lo' & SZ' & CS' & RR' & TL' & NIN'). reopen CS' HH HTc MF SOK MI ST MK.
      flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS' opndN)) 5%nat. intros CN_ _ HLN HNN _. unfold mpi_cells in CN_.
      zstep. rewrite zx16_small by lia. zstep. zstep.
      flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS')) 10%nat. intros MW' NSW' EA' WRW' LW' CRW' CRWL' HFW' ASW' WA8'.
      pose proof HGROW as SGR. unfold mpi_grow_stmt, U_MPI_GROW in SGR.
      eapply aevtM_cut.
      { eapply SGR with (dX := dW') (nb := md_n dN) (lo := lo) (h := hq') (LB := LBq'); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc HNN; lia).
        all: try (rewrite ?EA'; reflexivity). }
      clear SGR. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      binop_post PO m3 mo3 h3 LB3 dW3 r E MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR3.
      replace (ret_pc (Z_to_bv 64 0x219ac)) with (Z_to_bv 64 0x219ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(RR3) 2%nat. flclear RR3. intros R1 FRB3.
      assert (PN3 : md_pad dW3 = md_pad dW' /\ md_n dW' <= md_n dW3 /\ (r = 0 -> md_n dN <= md_n dW3) /\ (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED)).
      { destruct R1 as [(Hr0 & _ & N3 & P3 & _)|[HrF ->]]; [| split; [reflexivity|]; split; [lia|]; split; [intros Hr0; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in HrF; lia| right; exact HrF]].
        split; [exact P3|]. split; [rewrite N3; lia|]. split; [intros _; rewrite N3; lia| left; exact Hr0]. }
      flat constr:(PN3) 4%nat. flclear PN3. intros PAD3 NLE3 NN3 Hr.
      assert (TS3 : tstate m3 mo3 h3 LB3 dW3 dR T tl ts).
      { eapply t_binop_w; [exact TS'| exact HH3| exact HT3| exact MF3| exact MA3| exact OUT3| exact PX3| exact SOK3| exact MI3| exact ST3| exact FRB3| exact PAD3| exact NLE3]. }
      pose proof (proj1 (proj2 OUT3)) as NS3.
      clear CS' MW' NSW' EA' WRW' LW' CRW' CRWL' HFW' ASW' WA8' R1 FRB3 OUT3 PX3. pose proof TS3 as (lo3 & _ & CS3 & _). reopen CS3 HH HTc MF SOK MI ST MK.
      zstep; if_cases K0; zify_cond K0.
      { eapply L_clean1'; [exact TS3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia]. }
      assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
      eapply L_core; [exact TS3| eapply out_heap; [exact MA3| exact NS3| pose proof (NN3 eq_refl); lia]| exact OR| exact N1| exact (NN3 eq_refl)| exact NLR| exact E1| exact TLE]. }
    zstep; if_cases K0; zify_cond K0.
    { eapply GROW. exact TS1. }
    zstep. zstep. zstep. zstep.
    flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dN CS1 opndN)) 2%nat. intros SWN OWN.
    flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS1)) 2%nat. intros SWW OWW.
    pose proof HMOD as SM. unfold mpi_mod_mpi_stmt, mpi_binop_stmt_nb, U_MPI_MOD_MPI in SM.
    eapply aevtM_cut.
    { eapply SM with (dX := set_sg dW 1) (dA := set_sg dW 1) (dB := dN) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?EA; reflexivity).
      all: try (cbn [set_sg md_addr]; rewrite ?EA, ?EAW; first [reflexivity| exact NXN]). }
    clear SM. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
    replace (ret_pc (Z_to_bv 64 0x2199c)) with (Z_to_bv 64 0x2199c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR2) 2%nat. flclear RR2. intros (_ & Hr) FLt20. flat constr:(FLt20) 4%nat. flclear FLt20. intros EA2 PAD2 FRB2 NLE2.
    assert (TS2 : tstate m2 mo2 h2 LB2 dW2 dR T tl ts).
    { eapply t_binop_w; [exact TS1| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB2| exact PAD2| exact NLE2]. }
    clear CS1 MW NSW EA WRW LW CRW CRWL HFW ASW WA8 MA2 OUT2 PX2. pose proof TS2 as (lo2 & _ & CS2 & _). reopen CS2 HH HTc MF SOK MI ST MK.
    zstep; if_cases K1; zify_cond K1.
    { eapply L_clean1'; [exact TS2| lia]. }
    eapply GROW. exact TS2.
  Qed.

  Lemma L_copy : forall mq moq hq LBq dW dR (T tl : Z) (ts : list word)
      (xra x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    tstate mq moq hq LBq dW dR T tl ts -> md_own dR = LHeap ->
    1 <= md_n dN -> md_n dN <= md_n dR -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) (Z_to_bv 64 T) (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21928.
  Proof.
    intros until t6. intros TS OR N1 NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof TS as (lo16 & SZL & CS_ & RR & TL & NIN). reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros SWW OWW.
    flat constr:(MW) 2%nat. intros FLt21 _. flat constr:(FLt21) 4%nat. flclear FLt21. intros _ _ WPOS _.
    pose proof HCOPY as SC. unfold mpi_copy_stmt, U_MPI_COPY in SC.
    assert (HY : exists dY, mpd_at usegs mq LBq dY /\ mpd_sep dW dY /\ copy_sep dW dY lo SPc /\ client_range L LBq lo (md_addr dY) 16
                 /\ (md_own dY = LHeap -> client_range L LBq lo (md_p dY) (4 * md_n dY)) /\ md_addr dY = md_addr dA).
    { destruct opndA as [IN|E].
      - flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dA CS_ IN)) 4%nat. intros MA CRA_ CRAL_ _. flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dA CS_ IN)) 2%nat. intros SWA OWA.
        flat constr:(MA) 2%nat. intros FLt22 _. flat constr:(FLt22) 4%nat. flclear FLt22. intros _ _ APOS _.
        exists dA. split; [exact MA|]. split; [exact SWA|]. split; [apply copy_sep_of_opnd; [exact OWA| lia]|]. auto.
      - exists dW. split; [exact MW|]. split; [exact SWW|]. split; [apply copy_sep_of_opnd; [exact OWW| lia]|]. split; [exact CRW|]. split; [exact CRWL|]. rewrite E. exact EA. }
    flat constr:(HY) 7%nat. flclear HY. intros dY MY SWY CSY CRY CRYL EY.
    eapply aevtM_cut.
    { eapply SC with (dX := dW) (dY := dY) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?EA, ?EY; reflexivity). }
    clear SC. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
    replace (ret_pc (Z_to_bv 64 0x21934)) with (Z_to_bv 64 0x21934) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR2) 4%nat. flclear RR2. intros R1 EA2 PAD2 FRB2.
    assert (PN2 : md_n dW <= md_n dW2 /\ (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED)).
    { destruct R1 as [(Hr0 & _ & N2)|(HrF & N2 & _)]; [split; [lia| left; exact Hr0]| split; [lia| right; exact HrF]]. }
    flat constr:(PN2) 2%nat. flclear PN2. intros NLE2 Hr.
    assert (TS2 : tstate m2 mo2 h2 LB2 dW2 dR T tl ts).
    { eapply t_binop_w; [exact TS| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB2| exact PAD2| exact NLE2]. }
    clear CS_ MW NSW EA WRW LW CRW CRWL HFW ASW WA8 MA2 OUT2 PX2 MY CSY CRY CRYL. pose proof TS2 as (lo2 & SZ2 & CS2 & _). reopen CS2 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    { assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. eapply L_mid; [exact TS2| exact OR| exact N1| exact NLR| exact E1| exact TLE]. }
    eapply L_clean1'; [exact TS2| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia].
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
  Proof.
    intros until t6. intros CS_ SZ EAR TL N1 E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dRR CS_ eq_refl)) 10%nat. intros MR NSR WRR LR CRR CRRL HFR AR1 AR2 AR8.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 6%nat. intros MN CRN_ CRNL_ LN HFN ASN.
    flat constr:((mc_opnd_sep_le _ _ _ _ _ _ _ _ _ 0 dRR dN CS_ eq_refl opndN)) 2%nat. intros SRN ORN.
    pose proof HR2 as SR. unfold mpi_get_mont_r2_stmt, U_MPI_GET_MONT_R2 in SR.
    eapply aevtM_cut.
    { eapply SR with (dX := dRR) (dN := dN) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?EAR; first [reflexivity| apply f_equal; lia]).
      all: try (rewrite EAR; clear - ASN AR1 AR2 SLO HLS; lia). }
    clear SR. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dR r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
    try (match goal with |- context [ret_pc (Z_to_bv 64 ?x)] => replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).
    flat constr:(RR2) 4%nat. flclear RR2. intros (RN & Hr) EA2 PAD2 FRB2.
    assert (CS2 : CST m2 mo2 h2 LB2 [dR] dX [(T, 4 * tl)] [(SPc, lo16); (SP + -80, REGS)] [(T, [CB (4 * length ts)%nat (u32s ts)])]).
    { pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 0 dRR m2 mo2 h2 LB2 dR CS_ eq_refl HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2 FRB2) as C2. cbn [set_nth] in C2. exact C2. }
    flat constr:((mc_drop_local _ _ _ _ _ _ _ _ _ _ CS2)) 11%nat. intros CS3 NINF SGR HLR HNR A1 A2 A8 NSR' RN0 RH.
    cbn [app] in CS3. unfold mpd_struct in CS3. rewrite EA2, EAR in CS3. apply cs_swap12 in CS3.
    assert (RRK : rr_ok dR).
    { split; [rewrite EA2; exact EAR|]. split; [exact HLR|]. split; [exact HNR|]. split; [exact NSR'|]. split; [exact SGR|]. split; [exact RN0|].
      intros O. flat constr:((RH O)) 6%nat. intros _ X1 X2 X3 X4 _. auto. }
    assert (NIN : ~ In (T, 4 * tl) (mpd_blk dR)) by (exact (Forall_inv NINF)).
    assert (TS3 : tstate m2 mo2 h2 LB2 dX dR T tl ts).
    { exists lo16. split; [exact SZ|]. split; [unfold frame, rr_cells; exact CS3| exact (conj RRK (conj TL NIN))]. }
    clear CS_ MR NSR WRR LR CRR CRRL HFR MN CRN_ CRNL_ LN HFN ASN SRN ORN MA2 OUT2 PX2 CS2.
    clear CS3. pose proof TS3 as (lo16' & _ & CS4 & _). reopen CS4 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    - assert (r = 0) by lia. subst r. pose proof (RN eq_refl) as NLR.
      assert (OR : md_own dR = LHeap) by (destruct (md_own dR) eqn:O; [destruct (RN0 eq_refl); lia| reflexivity| exfalso; exact (NSR' eq_refl)]).
      eapply L_copy; [exact TS3| exact OR| exact N1| exact NLR| exact E1| exact TLE].
    - eapply L_r2fail; [exact TS3| lia].
  Qed.

  Lemma L_init : forall mq moq hq LBq lo16 c16 (T tl : Z) (ts : list word)
      (xra x6 x8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dX [(T, 4 * tl)] (frame lo16 c16) [(T, [CB (4 * length ts)%nat (u32s ts)])] ->
    cells_size lo16 = 16%nat -> cells_size c16 = 16%nat -> Z.of_nat (length ts) = tl -> 0 < T ->
    1 <= md_n dN -> 1 <= md_n dE -> tl = exp_mod_working_limbs (md_n dN) (md_n dE) ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 tl) x6 (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21868.
  Proof.
    intros until t6. intros CS_ SZ1 SZ2 TL T0 N1 E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 3%nat. intros CHL CH0 CHR. reopen CS_ HH HTc MF SOK MI ST MK.
    assert (WF0 : cells_wf c16) by exact (proj1 (proj1 CH0)).
    assert (CH0' : rw_cells usegs mq (bv_unsigned sp + -96) [CB 16 (cells_bytes c16)]).
    { eapply rw_cells_reshape; [exact CH0| cbn [cells_wf cell_wf]; split; [rewrite cells_bytes_length by exact WF0; exact SZ2| exact I]|].
      cbn [cells_bytes cbytes]. apply app_nil_r. }
    clear CH0. set (j16 := cells_bytes c16) in CH0'.
    assert (L16 : length j16 = 16%nat) by (subst j16; rewrite cells_bytes_length by exact WF0; exact SZ2).
    zstep. zstep.
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp + -80)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : rw_cells usegs m3 (bv_unsigned sp + -96) _ |- _ => rename H into CH3 end.
    match goal with H : rw_cells usegs m3 (bv_unsigned sp + -80) _ |- _ => rename H into CHR3 end.
    match goal with H : rw_cells usegs m3 (bv_unsigned sp + -112) _ |- _ => rename H into CHL3 end.
    set (j4 := skipn 4 (skipn 8 j16)) in CH3.
    assert (L4 : length j4 = 4%nat) by (subst j4; rewrite !skipn_length, L16; reflexivity).
    assert (CH3' : rw_cells usegs m3 (bv_unsigned sp + -96) (mpi_cells 0 (Z_to_bv 64 1) 0 (wof j4))).
    { eapply rw_cells_reshape; [exact CH3| cbn; repeat split; exact I|].
      unfold mpi_cells, wof. cbn [cells_bytes cbytes app]. rewrite le4_le_bytes_to_word by exact L4.
      change (le4 (Z_to_bv 64 1)) with (le2 (Z_to_bv 64 1) ++ le2 (Z_to_bv 64 0)). rewrite <- !app_assoc. reflexivity. }
    clear CH3.
    assert (CS3 : CST m3 moq hq LBq [] dX [(T, 4 * tl)] [(SP + -96, mpi_cells 0 (Z_to_bv 64 1) 0 (wof j4)); (SPc, lo16); (SP + -80, REGS)] [(T, [CB (4 * length ts)%nat (u32s ts)])]).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -96) (bv_unsigned sp + -80) []);
        [exact CS_| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| intros j d d' Hj; destruct j; discriminate Hj| |].
      - constructor; [exact CH3'| constructor; [exact CHL3| constructor; [exact CHR3| constructor]]].
      - constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd]; rewrite ?SZ1; cbn [cells_size csize Nat.add mpi_cells].
        all: split; [lia|]; split; [lia|]; intros d []. }
    assert (CS4 : CST m3 moq hq LBq [null_mpd (bv_unsigned sp + -96) (wof j4)] dX [(T, 4 * tl)] [(SPc, lo16); (SP + -80, REGS)] [(T, [CB (4 * length ts)%nat (u32s ts)])]).
    { eapply mc_intro_local; [exact CS3| clear - SPA; lia| |constructor].
      constructor; [cbn [fst snd]; rewrite SZ1; lia| constructor; [cbn [fst snd cells_size csize Nat.add length]; lia| constructor]]. }
    clear CS_ CS3 MU WM CH3' CHR3 CHL3. try clear CHL. try clear CHR. reopen CS4 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity].
    eapply L_r2; [exact CS4| exact SZ1| reflexivity| exact TL| exact N1| exact E1| exact TLE].
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
  Proof.
    intros until t6. intros CS_ SZL SZ.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof (w_writable_SP _ _ _ _ _ _ CS_) as WRS.
    pose proof CS_ as CS2. dest_cs CS2.
    assert (WRF : mpd_writable L LBq (bv_unsigned sp + -112) (heap_top usegs L HI hq) dX).
    { flat constr:(WRS) 3%nat. flclear WRS. intros W1 W2 W3. split; [| split; [exact W2| exact W3]].
      intros a Ha. destruct (W1 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    zstep. zstep. zstep.
    pose proof HLSET as SL. unfold mpi_lset_stmt, U_MPI_LSET in SL.
    eapply aevtM_cut.
    { eapply SL with (lo := lo) (h := hq) (LB := LBq) (dX := dX) (z := 1); rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by lia;
        first [ exact HH | exact MW | exact NSX | exact WRF | exact TP | exact MI | exact SOK | exact CA | exact ACL | exact DHI | exact ST | reflexivity
              | clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m5 mo5 h5 LB5 dW5 r5 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI5 ST5 MF5 HT5 HH5 MA5 OUT5 PX5 SOK5 RR5.
    flat constr:(RR5) 3%nat. flclear RR5. intros R5 EA5 FRB5.
    replace (ret_pc (Z_to_bv 64 0x218bc)) with (Z_to_bv 64 0x218bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (RB : -2^31 < r5 <= 0) by (destruct R5 as [(-> & _)|(-> & _)]; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia).
    assert (PAD5 : md_pad dW5 = md_pad dX) by (destruct R5 as [(_ & _ & _ & _ & _ & P5)|(_ & ->)]; [exact P5| reflexivity]).
    assert (N5 : md_n dX <= md_n dW5) by (destruct R5 as [(_ & N5 & _)|(_ & ->)]; [rewrite N5; lia| lia]).
    assert (CS5 : CST m5 mo5 h5 LB5 [] dW5 [] (frame lo16 c16) []).
    { eapply mc_binop_w; [exact CS_| exact HH5| exact HT5| exact MF5| exact MA5| exact OUT5| exact PX5| exact SOK5| exact MI5| exact ST5| exact FRB5| exact PAD5| exact N5]. }
    clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK.
    zstep.
    eapply L_ret; [exact CS5| exact SZL| exact SZ| exact RB].
  Qed.

  Lemma L_alloc : forall mq moq hq LBq lo16 c16
      (xra x5 x6 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dX [] (frame lo16 c16) [] -> cells_size lo16 = 16%nat -> cells_size c16 = 16%nat -> 1 <= md_n dN ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) x5 x6 (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x21848.
  Proof.
    intros until t6. intros CS_ SZ1 SZ2 N1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS_)) 3%nat. intros CHL CH0 CHR. reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 5%nat. intros CE_ _ HLE HNE _. unfold mpi_cells in CE_.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 5%nat. intros CN_ _ HLN HNN _. unfold mpi_cells in CN_.
    zstep. rewrite zx16_small by lia. zstep; if_cases K0; zify_cond K0.
    { eapply L_e0; [exact CS_| exact SZ1| exact SZ2]. }
    rewrite ?unsigned_lit in K0 by lia.
    zstep. rewrite zx16_small by lia. zstep.
    pose proof HWL as SWL. unfold mpi_core_exp_mod_working_limbs_stmt, U_MPI_CORE_EXP_MOD_WORKING_LIMBS in SWL.
    eapply aevtM_cut_evt; [exact MK| eapply SWL with (an := md_n dN) (en := md_n dE); first [exact MI| reflexivity| lia] |].
    clear SWL. cbv beta. intros ms' PO. unfold mpi_core_exp_mod_working_limbs_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _ ->.
    try (match goal with |- context [ret_pc (Z_to_bv 64 ?x)] => replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).
    set (tl := exp_mod_working_limbs (md_n dN) (md_n dE)).
    assert (TLB : 3 <= tl < 2^20) by (subst tl; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    zstep. zstep. zstep.
    match goal with |- context [MS _ _ (Z_to_bv 64 ?x) _ _ _ _] => replace (Z_to_bv 64 x) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity) end.
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := tl) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by lia; try eassumption; try reflexivity; try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc TLB; lia) |].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    pose proof (f_equal cfg_ms E) as E1. pose proof (f_equal cfg_model E) as E2. cbn in E1, E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by lia.
    flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HPc h2 HT2 CASES.
    try (match goal with |- context [ret_pc (Z_to_bv 64 ?x)] => replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    destruct CASES as [[-> HH2] | (T & -> & HBT & HH2 & HNEW)].
    - assert (CS2 : CST m2 mo2 h2 LBq [] dX [] (frame lo16 c16) []).
      { eapply mc_heap_nop0; [exact CS_| exact HH2| exact HT2| exact MF2| exact HPc| exact MI2| exact ST2]. }
      clear CS_ CHL CH0 CHR CE_ CN_ HPc. reopen CS2 HH HTc MF SOK MI ST MK.
      zstep; if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      zstep. zstep. eapply L_ret; [exact CS2| exact SZ1| exact SZ2| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia].
    - flat constr:(HBT) 5%nat. intros T0 TAL _ T4 _.
      set (ts := repeat (Z_to_bv 64 0) (Z.to_nat tl)).
      assert (LTS : Z.of_nat (length ts) = tl) by (subst ts; rewrite repeat_length; lia).
      replace (tl * 4) with (4 * tl) in HH2, HBT by lia.
      assert (HNEW' : rw_cells usegs m2 T [CB (4 * length ts)%nat (u32s ts)]).
      { subst ts. rewrite u32s_repeat0, repeat_length. replace (4 * Z.to_nat tl)%nat with (Z.to_nat (tl * 4)) by lia. exact HNEW. }
      assert (CS2 : CST m2 mo2 h2 ((T, 4 * tl) :: LBq) [] dX [(T, 4 * tl)] (frame lo16 c16) [(T, [CB (4 * length ts)%nat (u32s ts)])]).
      { eapply mc_ex_alloc; [exact CS_| exact HH2| exact HT2| exact MF2| exact HPc| exact MI2| exact ST2| lia| exact HNEW'|]. cbn [cells_size csize Nat.add]. lia. }
      clear CS_ CHL CH0 CHR CE_ CN_ HPc HNEW HNEW'. reopen CS2 HH HTc MF SOK MI ST MK.
      zstep; if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|].
      eapply L_init; [exact CS2| exact SZ1| exact SZ2| exact LTS| exact T0| exact N1| lia| reflexivity].
  Qed.

  Lemma L_C : forall mq moq hq LBq lo16 c16
      (xra x5 x6 x8 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    CST mq moq hq LBq [] dX [] (frame lo16 c16) [] -> cells_size lo16 = 16%nat -> cells_size c16 = 16%nat -> 1 <= md_n dN ->
    RUN moq mq (mkR xra SPF gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) a0 a1 a2 a3 a4 a5 a6 a7
      (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) x5 x6 (Z_to_bv 64 0) x8 s9 s10 s11 t3 t4 t5 t6) 0x217dc.
  Proof.
    intros until t6. intros CS_ SZL SZ N1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof (opnd_view _ _ _ 0 _ (opnd_at_mpd _ _ _ 0 _ ME0)) as ((_ & EA8 & EA0 & _) & _).
    reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 8%nat. intros CE_ BE HLE HNE _ PBE HFE HZE. unfold mpi_cells in CE_.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 8%nat. intros CN_ BN HLN HNN _ PBN HFN _. unfold mpi_cells in CN_.
    pose proof (u32ro_bound _ _ _ _ BE) as BEB. pose proof (u32ro_bound _ _ _ _ BN) as BNB.
    pose proof CE_ as EB. apply rw_cells_bound in EB. cbn [cells_size csize Nat.add] in EB.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep. if_cases K1; zify_cond K1; [exfalso; apply K1; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact EA8|].
    zstep. zstep. rewrite zx16_small by lia. zstep.
    assert (STEP : forall (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
      aevtM usegs moq POST
      (MS (mkR (Z_to_bv 64 0x217f4) SPF gp tp y0 y1 y2 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 (core_bitlen (md_limbs dE) (md_n dE))) ya1 ya2 ya3 ya4 ya5 ya6 ya7
              (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 (md_addr dA)) x5 x6 (Z_to_bv 64 0) x8 s9 s10 s11 y3 y4 y5 y6)
          F (Z_to_bv 64 0x217f4) fc None mq (seg_rom usegs))).
    { intros. pose proof (core_bitlen_range (md_limbs dE) (md_n dE) ltac:(lia)) as BR1.
      zstep. zstep; if_cases K2; zify_cond K2.
      2:{ zstep. eapply L_ret; [exact CS_| exact SZL| exact SZ| lia]. }
      zstep. zstep. rewrite zx16_small by lia.
      destruct PBN as [N0|[PN0 PN4]]; [exfalso; lia|].
      zstep.
      pose proof HCBL as SB. unfold mpi_core_bitlen_stmt, U_MPI_CORE_BITLEN in SB.
      eapply aevtM_cut_evt; [exact MK| eapply SB with (A := md_p dN) (n := md_n dN) (xs := md_limbs dN); first [exact BN| exact MI| exact PN4| exact PN0| reflexivity| lia] |].
      clear SB. cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _ ->.
      replace (ret_pc (Z_to_bv 64 0x2183c)) with (Z_to_bv 64 0x2183c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (core_bitlen_range (md_limbs dN) (md_n dN) ltac:(lia)) as BR2.
      zstep. zstep. zstep; if_cases K3; zify_cond K3.
      - eapply L_ret; [exact CS_| exact SZL| exact SZ| lia].
      - eapply L_alloc; [exact CS_| exact SZL| exact SZ| exact N1]. }
    destruct (Z.eq_dec (md_n dE) 0) as [E0|EN0].
    - assert (P0 : md_p dE = 0).
      { destruct (md_own dE) eqn:O; [exact (proj1 (HZE eq_refl))| |]; exfalso; (flat constr:((HFE ltac:(congruence))) 3%nat; intros _ _ NE1); lia. }
      rewrite E0.
      pose proof HCBLZ as SB. unfold mpi_core_bitlen_z_stmt, U_MPI_CORE_BITLEN in SB.
      eapply aevtM_cut_evt; [exact MK| eapply SB with (A := md_p dE); first [exact MI| reflexivity| rewrite P0; lia] |].
      clear SB. cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _ ->.
      replace (ret_pc (Z_to_bv 64 0x217f4)) with (Z_to_bv 64 0x217f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (EC : core_bitlen [] 0 = core_bitlen (md_limbs dE) (md_n dE)).
      { rewrite E0. destruct (md_limbs dE); [reflexivity| cbn in HLE; exfalso; lia]. }
      rewrite EC. eapply STEP.
    - destruct PBE as [N0|[PE0 PE4]]; [exfalso; lia|].
      pose proof HCBL as SB. unfold mpi_core_bitlen_stmt, U_MPI_CORE_BITLEN in SB.
      eapply aevtM_cut_evt; [exact MK| eapply SB with (A := md_p dE) (n := md_n dE) (xs := md_limbs dE); first [exact BE| exact MI| exact PE4| exact PE0| reflexivity| lia] |].
      clear SB. cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _ ->.
      replace (ret_pc (Z_to_bv 64 0x217f4)) with (Z_to_bv 64 0x217f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply STEP.
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.

  Lemma L_entry : forall (m1 : mem) (j32 : list (bv 8)) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
    munch [(lo, SP)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 -> stk usegs m1 lo SPc ->
    rw_cells usegs m1 SPc [CB 32 j32] -> rw_cells usegs m1 (SP + -80) REGS ->
    aevtM usegs mo POST (MS (mkR ra SPF gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 (md_addr dE))
      (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x21744) fc None m1 (seg_rom usegs)).
  Proof.
    intros until t6. intros MU WM MI1 ST1 FR0 FR1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    assert (L32 : length j32 = 32%nat) by (pose proof (proj1 (proj1 (proj1 FR0))) as W; cbn in W; tauto).
    assert (FR0' : rw_cells usegs m1 SPc ([CB 16 (firstn 16 j32)] ++ [CB 16 (skipn 16 j32)])).
    { eapply rw_cells_reshape; [exact FR0| cbn; rewrite length_firstn, length_skipn, L32; cbn; repeat split| cbn; rewrite !app_nil_r, firstn_skipn; reflexivity]. }
    flat constr:((proj1 (rw_cells_app usegs _ _ _ _) FR0')) 2%nat. intros FA FB. cbn [cells_size csize Nat.add] in FB.
    match type of FB with rw_cells _ _ ?aa _ => replace aa with (SP + -96) in FB by lia end.
    assert (CS1 : CST m1 mo h LB [] dX [] (frame [CB 16 (firstn 16 j32)] [CB 16 (skipn 16 j32)]) []).
    { eapply mc_init; [exact HH0| exact SOK0| exact MI0| exact MX0| | exact MU| exact WM| exact MI1| exact ST1| constructor| intros i j di dj Hi; destruct i; discriminate Hi| |].
      - unfold es. destruct ALIAS; [constructor; [exact ME0| constructor; [exact MN0| constructor]]| constructor; [exact MA0| constructor; [exact ME0| constructor; [exact MN0| constructor]]]].
      - unfold frame. constructor; [exact FA| constructor; [exact FB| constructor; [exact FR1| constructor]]].
      - apply frame_chs; reflexivity. }
    clear FR0 FR0' FA FB FR1 MU WM MI1 ST1.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS1)) 3%nat. intros CL CH0 CHR. reopen CS1 HH HTc MF SOK MI ST MK.
    do 6 zstep.
    pose proof (munch_refl [(SPc, SP + -80)] m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    do 9 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    set (j4 := skipn 4 (skipn 8 (skipn 16 j32))) in CH0.
    assert (L4 : length j4 = 4%nat) by (subst j4; rewrite !length_skipn, L32; reflexivity).
    assert (CS2 : CST m2 mo h LB [] dX [] (frame [CB 12 (firstn 12 (firstn 16 j32)); C4 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 (SP + -100)); C4 (Z_to_bv 64 65537); CB 4 j4]) []).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ SPc (SP + -80) []);
        [exact CS1| exact MU1| exact WM1| assumption| assumption| lia| lia| constructor| reflexivity| intros j d d' Hj; destruct j; discriminate Hj| |].
      - unfold frame. constructor; [exact CL| constructor; [exact CH0| constructor; [exact CHR| constructor]]].
      - apply frame_chs; reflexivity. }
    clear CS1 MU1 WM1 CL CH0 CHR. reopen CS2 HH HTc MF SOK MI ST MK.
    assert (E4 : le4 (Z_to_bv 64 65537) = le2 (Z_to_bv 64 1) ++ le2 (Z_to_bv 64 1)).
    { vm_compute. repeat first [reflexivity| (apply bv_eq; reflexivity)| f_equal]. }
    set (dT := mkMPD (SP + -96) 1 1 (SP + -100) [Z_to_bv 64 0] (wof j4) LStatic).
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS2 opndN)) 6%nat. intros MN CRN_ CRNL_ LN HFN ASN.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS2)) 3%nat. intros CL2 CT0 CHR2.
    assert (CT2 : rw_cells usegs m2 (SP + -96) (mpi_cells (SP + -100) (Z_to_bv 64 1) 1 (wof j4))).
    { eapply rw_cells_reshape; [exact CT0| cbn; repeat split|].
      unfold mpi_cells, wof. cbn [cells_bytes cbytes app]. rewrite le4_le_bytes_to_word by exact L4.
      rewrite E4. rewrite <- !app_assoc. reflexivity. }
    assert (TOP : stack_opnd usegs m2 (SP + -112) dT).
    { pose proof (proj2 (proj1 (rw_cells_app usegs _ _ [CB 12 (firstn 12 (firstn 16 j32))] [C4 (Z_to_bv 64 0)]) CL2)) as C4T. cbn [cells_size csize] in C4T.
      match type of C4T with rw_cells _ _ ?aa _ => replace aa with (SP + -100) in C4T by lia end.
      assert (EU : u32s [Z_to_bv 64 0] = cells_bytes [C4 (Z_to_bv 64 0)]) by reflexivity.
      unfold stack_opnd, dT; cbn [md_own md_addr md_p md_sg md_n md_pad md_limbs].
      split; [reflexivity|]. split; [exact CT2|]. split; [clear - SPA; lia|]. split; [clear - SLO HLS ACL ACP SPB; lia|].
      split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; [lia|]. split; [clear - SPA; lia|].
      split; [clear - SLO HLS ACL ACP SPB; lia|]. split; [rewrite EU; exact (SysStep.rw_cells_bytes_at _ _ _ _ C4T)|].
      split; [lia|]. split; [clear - SLO HLS ACL ACP SPB; lia| left; reflexivity]. }
    pose proof HCMPO as SC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in SC.
    eapply aevtM_cut_evt; [exact MK| eapply SC with (dX := dN) (dY := dT) (LB := LB); rewrite ?unsigned_lit by lia;
      first [ left; exact MN | right; exact TOP | intros O; exact (proj1 (HFN O)) | intros O; discriminate O | exact MI | reflexivity
            | match goal with |- ?g => idtac "REMAINC1" g end ] |].
    clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO.
    flat constr:(PO) 18%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x21780)) with (Z_to_bv 64 0x21780) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (VT : mpd_val dT = 0) by (subst dT; vm_compute; reflexivity).
    rewrite VT, Z.sub_0_r.
    zstep. zstep. zstep; if_cases K0; zify_cond K0.
    { eapply L_ret; [exact CS2| reflexivity| reflexivity| lia]. }
    assert (NV : 0 < mpd_val dN).
    { destruct (Z.lt_trichotomy (mpd_val dN) 0) as [H|[H|H]]; [| |exact H]; exfalso;
        [rewrite (Z.sgn_neg _ H) in *| rewrite H in *; cbn [Z.sgn] in *]; lia. }
    repeat match goal with H : context [Z.sgn (mpd_val dN)] |- _ => clear H end.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS2 opndN)) 8%nat. intros CN_ BN HLN HNN SGN PBN HFNR HZN. unfold mpi_cells in CN_.
    pose proof (opnd_view _ _ _ 0 _ (opnd_at_mpd _ _ _ 0 _ MN0)) as ((_ & NA8 & NA0 & _) & _).
    pose proof CN_ as NB. apply rw_cells_bound in NB. cbn [cells_size csize Nat.add] in NB.
    assert (N1 : 1 <= md_n dN).
    { destruct (Z.eq_dec (md_n dN) 0) as [E0|E0]; [|lia]. exfalso.
      destruct (md_limbs dN) as [|x xs] eqn:LL; [| cbn [length] in HLN; lia].
      unfold mpd_val in NV. rewrite LL in NV. cbn in NV. lia. }
    destruct PBN as [N0|[PN0 PN4]]; [exfalso; lia|].
    assert (NNL : md_own dN <> LNull) by (intros O; destruct (HZN O); lia).
    flat constr:((HFNR NNL)) 3%nat. intros _ PNB _.
    pose proof (u32ro_bound _ _ _ _ BN) as BNB.
    zstep. if_cases Q1; zify_cond Q1; [exfalso; lia|].
    zstep. zstep. if_cases Q2; zify_cond Q2; [exfalso; apply Q2; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact NA8|].
    zstep. zstep. if_cases Q3; zify_cond Q3; [exfalso; lia|].
    zstep. zstep. if_cases Q4; zify_cond Q4; [exfalso; apply Q4; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact PN4|].
    pose proof (u32s_length (md_limbs dN)) as ULN.
    rd8 BN 0. zstep. zstep. if_cases Q5; zify_cond Q5.
    { eapply L_ret; [exact CS2| reflexivity| reflexivity| lia]. }
    clear Q1 Q2 Q3 Q4 Q5.
    pose proof (munch_refl [(SPc, SP + -80)] m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    clear CT2 TOP.
    do 9 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (CS3 : CST m3 mo h LB [] dX [] (frame [CB 12 (firstn 12 (firstn 16 j32)); C4 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 (SP + -100)); C4 (Z_to_bv 64 65537); CB 4 j4]) []).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ SPc (SP + -80) []);
        [exact CS2| exact MU2| exact WM2| assumption| assumption| lia| lia| constructor| reflexivity| intros j d d' Hj; destruct j; discriminate Hj| |].
      - unfold frame. constructor; [exact CL2| constructor; [exact CT0| constructor; [exact CHR2| constructor]]].
      - apply frame_chs; reflexivity. }
    clear CS2 MU2 WM2 CL2 CT0 CHR2 CN_ BN. reopen CS3 HH HTc MF SOK MI ST MK.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dE CS3 opndE)) 6%nat. intros ME CRE_ CREL_ LE HFE ASE.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ _ CS3)) 3%nat. intros CL3 CT3 _.
    assert (CT4 : rw_cells usegs m3 (SP + -96) (mpi_cells (SP + -100) (Z_to_bv 64 1) 1 (wof j4))).
    { eapply rw_cells_reshape; [exact CT3| cbn; repeat split|].
      unfold mpi_cells, wof. cbn [cells_bytes cbytes app]. rewrite le4_le_bytes_to_word by exact L4.
      rewrite E4. rewrite <- !app_assoc. reflexivity. }
    assert (TOP3 : stack_opnd usegs m3 (SP + -112) dT).
    { pose proof (proj2 (proj1 (rw_cells_app usegs _ _ [CB 12 (firstn 12 (firstn 16 j32))] [C4 (Z_to_bv 64 0)]) CL3)) as C4T. cbn [cells_size csize] in C4T.
      match type of C4T with rw_cells _ _ ?aa _ => replace aa with (SP + -100) in C4T by lia end.
      assert (EU : u32s [Z_to_bv 64 0] = cells_bytes [C4 (Z_to_bv 64 0)]) by reflexivity.
      unfold stack_opnd, dT; cbn [md_own md_addr md_p md_sg md_n md_pad md_limbs].
      split; [reflexivity|]. split; [exact CT4|]. split; [clear - SPA; lia|]. split; [clear - SLO HLS ACL ACP SPB; lia|].
      split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; [lia|]. split; [clear - SPA; lia|].
      split; [clear - SLO HLS ACL ACP SPB; lia|]. split; [rewrite EU; exact (SysStep.rw_cells_bytes_at _ _ _ _ C4T)|].
      split; [lia|]. split; [clear - SLO HLS ACL ACP SPB; lia| left; reflexivity]. }
    pose proof HCMPO as SC. unfold mpi_cmp_mpi_stmt_o, U_MPI_CMP_MPI in SC.
    eapply aevtM_cut_evt; [exact MK| eapply SC with (dX := dE) (dY := dT) (LB := LB); rewrite ?unsigned_lit by lia;
      first [ left; exact ME | right; exact TOP3 | intros O; exact (proj1 (HFE O)) | intros O; discriminate O | exact MI | reflexivity
            | match goal with |- ?g => idtac "REMAINC2" g end ] |].
    clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO.
    flat constr:(PO) 18%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x217d8)) with (Z_to_bv 64 0x217d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite VT, Z.sub_0_r.
    zstep; if_cases Q6; zify_cond Q6.
    { zstep. eapply L_ret; [exact CS3| reflexivity| reflexivity| lia]. }
    eapply L_C; [exact CS3| reflexivity| reflexivity| exact N1].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  End Walk.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L11075936116.108L17097338356.108L19685138523.108L19687428440.108L23124392564.108L25465666776.108L28125529944.108L29025845208.108L29135309044.108L31686769240.108L36180999398.105L41172169716.108L42780454045.108L43059266230.103L43679985268.107L5065130740.108 L55720577396.108L60692334296.108L61601561944.108L61747685364.108L62505661912.107L64270350808.108L65178513496.108L67541566890.107L67541566890.108L67758486644.10800000700>00E00L00S00Z00a00h00o01601=01D01K01c01j02102802?02F02M02T02[02b03=03X03_S2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1L3HLS2ra2sp2lo3SLO3SPBS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1L3HLS2ra2sp2lo3SLO3SPB2HBS1L3HLS2ra2sp2lo3SLO3SPB2HBS2ra2sp". (* [comment removed for export] *)
  Theorem U_mpi_exp_mod_spec : mpi_exp_mod_stmt_n usegs L HI U_MPI_EXP_MOD U_MEMSET_FUNC.
  Proof.
    unfold mpi_exp_mod_stmt_n, U_MPI_EXP_MOD. intros until lo.
    intros HH MX MA ME MN NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRAL CRE CREL CRN CRNL WRX XLO ST SLO ACL HTOP SPA DHI TP MI RA2 SOK CA -> -> -> -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (lock HH) as HHL. pose proof (lock MI) as MIL. pose proof (lock SOK) as SOKL. pose proof (lock ST) as STL. clear HH SOK.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 112%nat ST. set (JJ := junk) in FR. clearbody JJ.
    do 11 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : rw_cells usegs m1 _ _ |- _ => rename H into FRA end.
    flat constr:((proj1 (rw_cells_app usegs _ _ [CB 32 _] _) FRA)) 2%nat. intros FR0 FR1. clear FRA. cbn [cells_size csize Nat.add] in FR1.
    match type of FR1 with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -80) in FR1 by lia end.
    match type of FR0 with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -112) in FR0 by lia end.
    lazymatch type of FR0 with rw_cells _ _ _ [CB 32 ?j] => set (j32 := j) in FR0; clearbody j32 end.
    eapply L_entry; try eassumption; try exact (unlock _ HHL); try exact (unlock _ MIL); try exact (unlock _ SOKL); try exact (unlock _ STL).
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EM.
