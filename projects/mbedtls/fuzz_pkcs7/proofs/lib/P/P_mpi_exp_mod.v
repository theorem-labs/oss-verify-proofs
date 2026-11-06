(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts MpiJourney MpiClient MpiClientX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp
     P_mpi_lset P_mpi_grow P_mpi_copy P_mpi_core_bitlen P_mpi_core_bitlen_z P_mpi_core_exp_mod_working_limbs
     P_mpi_core_montmul P_mpi_core_montmul_init P_mpi_core_to_mont_rep P_mpi_core_from_mont_rep P_mpi_core_exp_mod
     P_mpi_core_check_zero_ct P_mpi_divmod_stmt P_mpi_exp_mod_stmt P_mpi_get_mont_r2.
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
Ltac2 gd_tbl_P_mpi_exp_mod () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.P.P_mpi_addsub.mpd_writable"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.HeapIface.hl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_mpi_addsub.mpi_binop_post"; "OSSVerify.KrLib.P.P_mpi_addsub.add_sub_mpi_R"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "EM.Walk.ALIAS"; "Corelib.Init.Datatypes.true"; "EM.Walk.es"; "OSSVerify.KrLib.Lib.Cells.cell"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.nil"; "EM.Walk.frame"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Spec.MpiClient.cstate"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.AEvt.MOK"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.P.P_mpi_divmod_stmt.exp_mod_R"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "OSSVerify.KrLib.Spec.Rep.MPI_MAX_LIMBS"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.mpd_blk"; "EM.Walk.rr_cells"; "OSSVerify.KrLib.Spec.MpiClientX.mpd_cx"; "EM.Walk.rr_ok"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Init.Nat.mul"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.P.P_mpi_free.P_ZEROIZE_AND_FREE"; "EM.Walk.tstate"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "EM.Walk.set_limbs"; "OSSVerify.KrLib.P.P_mpi_core_exp_mod_working_limbs.exp_mod_working_limbs"; "OSSVerify.KrLib.Spec.MpiVal.mpd_out"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.Spec.MpiVal.mpd_ivs"; "OSSVerify.KrLib.Lib.HeapIface.client_addr"; "OSSVerify.KrLib.Lib.Frame.outside"].


Definition P_ADD_SUB_MPI : Z := 0x1fec4.

(* [comment removed for export] *)
Definition add_sub_mpi_stmt_e (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pflip,$0.P,(1.(2.$0.R1.+1.)(2.$0.R1.-1.))Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.Ph,(7.O5.O4.O3.)PLB,(8.$9.)PdX,$:.PdA,$:.PdB,$:.Plo,$0.P,(;.O5.O4.O3.R6.R5.R8.R7.)P,(<.O5.R9.R6.R5.)P,(<.O5.R:.R7.R5.)P,(<.O5.R;.R8.R5.)P,(=.R8.R7.)P,(=.R9.R7.)P,(=.R9.R8.)P,(>.(2.$?.(10.R;.)$11.))P,(12.R<.R;.R9.(13.&40.R2?.))P,(12.R=.R;.R:.(13.&40.R30.))P,(14.O4.R?.R;.(15.R=.)+10.)P,P,(2.$?.(10.R>.)$16.)(14.O4.R11.R=.(17.R?.)(18.+4.(19.R?.)))P,(14.O4.R11.R=.(15.R>.)+10.)P,P,(2.$?.(10.R?.)$16.)(14.O4.R13.R?.(17.R10.)(18.+4.(19.R10.)))P,(1:.O4.R13.(13.&40.R35.)(1;.O5.O4.O3.R14.)R12.)P,P,(>.(2.$?.(10.R13.)$1<.))(1.(1=.(1>.(17.R14.)(18.+4.(19.R14.)))R11.)(1=.(13.&40.R37.)(17.R14.)))P,(1?.O5.R18.R11.(13.&40.R37.))P,(1=.R12.(20.(20.(13.&40.R38.)+>0.)(21.O4.)))P,(1=.(22.O4.)R13.)P,(1=.(13.&40.R3:.)(1;.O5.O4.O3.R19.))P,(2.$0.(23.(13.&40.R3;.)+10.)=)P,(1=.(24.O4.)(22.O4.))P,(2.(3.&40.)R3;.(25.&40.(26.O4.)))P,(27.O5.R1?.)P,(28.O5.O4.R20.)P,(29.O4.O1.+8.)P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))P,(2.(3.&40.)R39.(25.&40.(15.R1>.)))(2:.O5.R24.(2;.O5.O4.O3.R45.R44.R43.R42.R3>.R3=.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.(2<.R47.R22.R21.R20.R1?.)R1>.R25.R24.)(2=.(2>.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.(25.&40.R47.)R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(25.&40.O2.)R26.(2?.(3.&40.))R25.(30.O5.)))")
(* [comment removed for export] *).

Section EM.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr psegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis HCBL : mpi_core_bitlen_stmt psegs P_MPI_CORE_BITLEN.
  Hypothesis HCBLZ : mpi_core_bitlen_z_stmt psegs P_MPI_CORE_BITLEN.
  Hypothesis HWL : mpi_core_exp_mod_working_limbs_stmt psegs P_MPI_CORE_EXP_MOD_WORKING_LIMBS.
  Hypothesis HLSET : mpi_lset_stmt psegs L HI P_MPI_LSET P_MEMSET_FUNC.
  Hypothesis HR2 : mpi_get_mont_r2_stmt psegs L HI P_MPI_GET_MONT_R2 P_MEMSET_FUNC.
  Hypothesis HZF : zeroize_and_free_stmt psegs L HI P_ZEROIZE_AND_FREE P_MEMSET_FUNC.
  Hypothesis HCOPY : mpi_copy_stmt psegs L HI P_MPI_COPY P_MEMSET_FUNC.
  Hypothesis HCMP : mpi_cmp_mpi_stmt psegs P_MPI_CMP_MPI.
  Hypothesis HMOD : mpi_mod_mpi_stmt psegs L HI P_MPI_MOD_MPI P_MEMSET_FUNC.
  Hypothesis HGROW : mpi_grow_stmt psegs L HI P_MPI_GROW P_MEMSET_FUNC.
  Hypothesis HMMI : mpi_core_montmul_init_stmt psegs P_MPI_CORE_MONTMUL_INIT.
  Hypothesis HTOM : mpi_core_to_mont_rep_stmt psegs P_MPI_CORE_TO_MONT_REP.
  Hypothesis HCEM : mpi_core_exp_mod_stmt psegs P_MPI_CORE_EXP_MOD.
  Hypothesis HFROM : mpi_core_from_mont_rep_stmt psegs P_MPI_CORE_FROM_MONT_REP.
  Hypothesis HCZ : mpi_core_check_zero_ct_stmt psegs P_MPI_CORE_CHECK_ZERO_CT.
  Hypothesis HAS : add_sub_mpi_stmt_e psegs L HI P_ADD_SUB_MPI P_MEMSET_FUNC.

  Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (dX dA dE dN : mpd) (lo : Z).
  Hypothesis HH0 : HEAP psegs L HI h LB m mo.
  Hypothesis MX0 : mpd_at psegs m LB dX.
  Hypothesis MA0 : mpd_at psegs m LB dA.
  Hypothesis ME0 : mpd_at psegs m LB dE.
  Hypothesis MN0 : mpd_at psegs m LB dN.
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
  Hypothesis WRX : mpd_writable L LB (bv_unsigned sp) (heap_top psegs L HI h) dX.
  Hypothesis XLO : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX.
  Hypothesis ST0 : stk psegs m lo (bv_unsigned sp).
  Hypothesis SLO : lo <= bv_unsigned sp - 720 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top psegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv psegs m.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis SOK0 : statics_ok psegs L m.
  Hypothesis CA : const_at L P_MEMSET_FUNC 8.

  Notation SP := (bv_unsigned sp).
  Notation SPc := (bv_unsigned sp + -96).
  Notation POST := (mpi_binop_post psegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (exp_mod_R LB dX dA dE dN) lo m mo).

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
    assert (FE : forall d, mpd_at psegs m LB d -> md_addr dX <> md_addr d -> mpd_sep dX d -> opnd_sep dX d lo SP -> client_range L LB lo (md_addr d) 16 ->
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
  Notation CST := (cstate psegs L HI h LB mo m SP lo SPc dX es).
  Local Ltac mc_inst H :=
    exact (H psegs L HI HLS DIMG HND IMGC SW ROIMG h LB mo m SP lo SPc dX es
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
    exact (H psegs L HI HLS DIMG HND IMGC SW ROIMG h LB SP lo SPc dX es
             ACL ltac:(lia) ltac:(lia) HTOP (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0))))))) DHI NSX WRX
             (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok).
  Definition mc_blocks_disjoint := ltac:(mc_inst' @blocks_disjoint).
  Definition mc_blocks_eq_or := ltac:(mc_inst' @blocks_eq_or).
  Definition mc_limbs_low := ltac:(mc_inst' @mpd_limbs_low).
  Definition set_limbs (d : mpd) (xs : list word) : mpd := mkMPD (md_addr d) (md_sg d) (md_n d) (md_p d) xs (md_pad d) (md_own d).

  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -96)).
  Local Ltac dest_cs H :=
    (flat constr:(H) 21%nat; flclear H; intros HH HTc MF LOK SA LA MW WOK EXOK SUB COV FRS EXT PX SOK MI ST CH CHS CXH CXS).
  (* [comment removed for export] *)
  Notation REGS := ([C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).
  (* [comment removed for export] *)
  Definition frame (c16 : list cell) : list (Z * list cell) := [(SP + -96, c16); (SP + -80, REGS)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L19561307528.88L21368261110.88L47322195080.88L57491544310.8800000>00L00Z00hS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZ". (* [comment removed for export] *)
  Lemma frame_chs : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pc16,(8.$3?.)P,(2.$40.(41.R1.)#10.)(36.(34.$0.(8.$3?.))Lac,(34.$0.(8.$3?.))(31.(1=.(1>.(13.&40.Vsp,)-60.)(38.$0.(8.$3?.)R1.))(31.(1=.(1>.(38.$0.(8.$3?.)R1.)(42.(41.(39.$0.(8.$3?.)R1.))))(13.&40.Vsp,))Pd,$:.P,(33.$:.R1.(43.$:.))(1.(1=.(1>.(38.$0.(8.$3?.)R3.)(42.(41.(39.$0.(8.$3?.)R3.))))(15.R2.))(1=.(1>.(15.R2.)+10.)(38.$0.(8.$3?.)R3.)))))(44.R2.))")
(* [comment removed for export] *).
  Proof.
    intros c16 SZ. unfold frame. constructor; [| constructor; [| constructor]]; cbn [fst snd]; rewrite ?SZ; cbn [cells_size csize Nat.add].
    - split; [lia|]. split; [lia|]. intros d [].
    - split; [lia|]. split; [lia|]. intros d [].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma cs_parts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)PCS,(8.(34.$0.(8.$3?.)))PCX,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(31.(;.$45.VL,VHI,R8.R7.R:.R9.)(31.(2.$0.(1;.$45.VL,VHI,R8.)(1;.$45.VL,VHI,Vh,))(31.(47.Vmo,R9.)(31.(28.$45.VL,R:.)(31.(27.$45.R:.)(31.(1?.$45.R:.Vlo,(1>.(13.&40.Vsp,)-60.))(31.(36.(34.$0.(8.$3?.))Lac,(34.$0.(8.$3?.))(48.$45.R;.(38.$0.(8.$3?.)R1.)(39.$0.(8.$3?.)R1.))R3.)(31.(36.(34.$0.(8.$3?.))Lac,(34.$0.(8.$3?.))(48.$45.R;.(38.$0.(8.$3?.)R1.)(39.$0.(8.$3?.)R1.))R2.)(49.R9.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros until CX. intros CS_. dest_cs CS_. split; [exact HH|]. split; [exact HTc|]. split; [exact MF|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split; [exact CH|]. split; [exact CXH| exact (heap_mok _ _ HI _ _ _ _ HH)].
  Qed.

  (* [comment removed for export] *)
  Lemma cs_frame : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)Pc16,(8.$3?.)PCX,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R9.R8.R7.R6.R5.R4.R3.(44.R2.)R1.)(31.(48.$45.R:.(1>.(13.&40.Vsp,)-60.)R3.)(48.$45.R:.(1>.(13.&40.Vsp,)-50.)(4:.$3?.(4;.Vs8,)(4:.$3?.(4;.Vs7,)(4:.$3?.(4;.Vs6,)(4:.$3?.(4;.Vs5,)(4:.$3?.(4;.Vs4,)(4:.$3?.(4;.Vs3,)(4:.$3?.(4;.Vs2,)(4:.$3?.(4;.Vs1,)(4:.$3?.(4;.Vs0,)(4:.$3?.(4;.Vra,)(43.$3?.)))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros until CX. intros CS_. dest_cs CS_. pose proof (Forall_inv CH) as C0. pose proof (Forall_inv (Forall_inv_tail CH)) as C1. cbn [fst snd] in C0, C1. exact (conj C0 C1).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24928467276.9300000?S2ra2sp1d2N12N0". (* [comment removed for export] *)
  Lemma out_heap : forall mq LBq d, mpd_at psegs mq LBq d -> md_own d <> LStatic -> 1 <= md_n d -> md_own d = LHeap.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L15302269400.136L22446743512.136L24389775364.134L34705680216.136L3949578456.136 L41843875160.136L51454941784.136L5699067096.136 L58591023192.136L59506921496.133L60511374749.135L67280348888.136L7632799155.136 L7900592797.134 00000>00L00k01901G01U01c02102?02M02l03:03H03ZS2ra2sp3c162SZS2ra2sp3c162SZS1L3HLS2ra2sp2lo3SLO3c162SZ3SPBS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS1L3HLS2ra2sp2lo3SLO3c162SZ3SPBS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZ3SPB". (* [comment removed for export] *)
  Lemma L_ret : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.Pc16,(8.$3?.)Pr,$0.Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px2,(3.&40.)Px3,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R1?.R1>.R1=.R1<.(43.$:.)R1;.(43.$9.)(44.R1:.)(43.(34.$0.(8.$3?.))))P,(2.$40.(41.R1;.)#10.)P,(31.(32.(4<.(3:.+2.+1?.))R1;.)(1=.R1;.=))(2:.$45.R21.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R1;.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R11.R10.R?.R1:.R19.(25.&40.R1<.)R>.R=.R<.R;.R:.R9.R8.R18.R17.R16.R15.R14.R13.R12.Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(25.&40.+20;5<.)Vfc,(2?.(3.&40.))R22.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ SZ Hr.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros CH0 CHR.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ ltac:(constructor))) 11%nat. intros HH HT MF MW OUT BK PX SOK MI ST _.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    do 10 zstep.
    release_frame CH0 ST (bv_unsigned sp + -80). release_frame CHR ST (bv_unsigned sp).
    zstep. zstep.
    apply aevtM_done. unfold mpi_binop_post. do 14 eexists. exists mq, moq, hq, LBq, dW, r.
    split; [rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|]. split; [exact HH|]. split; [exact MW|]. split; [exact OUT|].
    split; [exact PX|]. split; [exact SOK|]. split; [exact Hr| exact BK].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rr_ok (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "(31.(2.$0.(15.O1.)(1>.(13.&40.Vsp,)-60.))(31.(2.$0.(42.(4>.(3.&40.)(4?.O1.)))(19.O1.))(31.(31.(1=.=(19.O1.))(1=.(19.O1.)$50.))(31.(>.(2.$?.(10.O1.)$11.))(31.(1.(2.$0.(51.O1.)+1.)(2.$0.(51.O1.)-1.))(31.P,(2.$?.(10.O1.)$1<.)(31.(2.$0.(17.O1.)=)(2.$0.(19.O1.)=))P,(2.$?.(10.O1.)$16.)(31.(1=.+1.(19.O1.))(31.(32.=(17.O1.))(31.(1=.(1>.(17.O1.)(18.+4.(19.O1.)))(22.VL,))(2.$0.(23.(17.O1.)+10.)=))))))))))")
(* [comment removed for export] *).
  Definition rr_cells (d : mpd) : list cell := mpi_cells (md_p d) (Z_to_bv 64 (md_sg d)) (md_n d) (md_pad d).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L12252534646.149L12294251000.144L20189507659.19 L29762660275.141L29762660275.143L38221228686.17 L38643945768.143L41114218273.17 L41415942734.144L42199950376.144L42250438172.149L42254634420.173L500186330.149  L55808652373.17 L59308628179.144L60902279467.17 L62991526192.173L67936743128.17 00000:00D00E00O00Y00f01R02302=02K03103W03o04J04Z04i053054S2ra2sp2dRS2ra2sp2dRFS2ra2sp2dRS2ra2sp2dRS1L2sp2lo3SLOS1L3HLS2ra2sp2lo3SLO3ACL2dR3SPB2N12P02P43HNRS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS2ra2sp2dRS2ra2sp2dR3HNRS1L3HLS2ra2sp2lo3SLO3ACL2dR3SPB3ACP2P0S1L3HLS2ra2sp2lo3SLO3ACL2dR3SPB3ACP2P0S2ra2sp2dR3SPB3HLR2N12P0S1L2HI2sp1h4HTOP2hq3SPB3HTcS2ra2sp2dR2P02K0S2sp2dR3SPB3HNRS2ra2sp2dRF". (* [comment removed for export] *)
  Lemma L_clean2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.Pr,$0.Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px2,(3.&40.)Px3,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R1?.R1>.R1=.R1<.(43.$:.)R1;.(52.R1:.)(44.(53.R1:.))(54.R1:.))P,(55.R1;.)P,(31.(32.(4<.(3:.+2.+1?.))R1;.)(1=.R1;.=))(2:.$45.R21.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R1;.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R11.R10.R?.R1:.R19.(25.&40.R1<.)R>.R=.R<.R;.R:.R9.R8.R18.R17.R16.R15.R14.R13.R12.Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(25.&40.+20<;<.)Vfc,(2?.(3.&40.))R22.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ RR Hr.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(RR) 7%nat. intros EAR HLR HNR NSR SGR RN RH. unfold MPI_MAX_LIMBS in HNR.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros CH0 CHR. unfold rr_cells, mpi_cells in CH0.
    reopen CS_ HH HTc MF SOK MI ST MK.
    destruct (md_own dR) eqn:OR; [| | exfalso; exact (NSR eq_refl)].
    - (* [comment removed for export] *) (flat constr:((RN eq_refl)) 2%nat; intros P0 N0). rewrite P0 in CH0.
      zstep. zstep; if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity].
      unfold mpd_blk, mpd_cx in CS_. rewrite OR in CS_.
      eapply L_ret; [exact CS_| reflexivity| exact Hr].
    - flat constr:((RH eq_refl)) 4%nat. intros N1 P0 P4 PAL.
      zstep. zstep; if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
      zstep. rewrite zx16_small by lia. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
      pose proof CS_ as CS2. flat constr:(CS2) 21%nat. flclear CS2. intros _ _ _ _ _ _ _ _ EXOK _ _ _ _ _ _ _ _ _ _ CXH _.
      unfold mpd_blk in EXOK. rewrite OR in EXOK. flat constr:((Forall_inv EXOK)) 2%nat. intros INR _.
      unfold mpd_cx in CXH. rewrite OR in CXH. pose proof (Forall_inv CXH) as CXR. cbn [fst snd] in CXR.
      zstep.
      pose proof HZF as SZ. unfold zeroize_and_free_stmt, P_ZEROIZE_AND_FREE in SZ.
      eapply aevtM_cut.
      { eapply SZ with (buf := md_p dR) (len := 4 * md_n dR) (lo := lo) (h := hq) (LB := LBq) (junk := u32s (md_limbs dR)); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc HNR; lia).
        - right. split; [exact INR|]. replace (Z.to_nat (4 * md_n dR)) with (4 * length (md_limbs dR))%nat by lia. exact CXR.
        - apply f_equal. lia. }
      clear SZ. cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 26%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 E MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
      injection E as -> ->. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in PX2 by lia.
      replace (ret_pc (Z_to_bv 64 0x20cd8)) with (Z_to_bv 64 0x20cd8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (CS2 : CST m2 mo2 h2 (lb_remove (md_p dR) LBq) [] dW [] (frame (rr_cells dR)) []).
      { eapply mc_ex_free; [exact CS_| unfold mpd_blk; rewrite OR; reflexivity| intros []| exact HH2| exact HT2| exact MF2| exact PX2| exact SOK2| exact MI2| exact ST2| constructor| constructor]. }
      clear CS_ CH0 CHR. reopen CS2 HH HTc MF SOK MI ST MK.
      zstep. zstep.
      eapply L_ret; [exact CS2| reflexivity| exact Hr].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L20644179179.146L27295032902.24 L35212815738.22 L38219455199.22 L41116639088.22 L42252535296.146L42254634420.170L55806477316.22 L66090029777.170L7044760976.170 00000W00X01B01R02602i03\04:04Q04kS2ra2sp3RET2cR2dR2tl2ts2SZ2TL2RB3SPB2KPFS1L3HLS2sp2lo3SLO3ACL1T2tl2ts3SPB2KP2T02T4S1L2sp2lo3SLO2tsS1L3HLS2sp2lo3SLO3ACL3SPA2ts3SPB3ACPS1L3HLS2ra2sp2lo3SLO3ACL3RET2cR2dR2ts2SZ2RB3SPB3ACPS1L3HLS2ra2sp2lo3SLO3ACL3RET2cR2dR2ts2SZ2RB3SPB3ACPS1L2HI2sp1h4HTOP2hq2ts3SPB3HTcS2ra2sp3RET2cR2dR2ts2SZS2ra2sp3RET2cR2dR2ts2SZ2RB". (* [comment removed for export] *)
  Lemma call_zf_T : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "PRET,$0.Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PcR,(8.$3?.)PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Px0,(3.&40.)Px1,(3.&40.)Px2,(3.&40.)Px3,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R20.R1?.R1>.R1=.(43.$:.)R1<.(4:.(34.$0.$0.)(35.$0.$0.R19.(18.+4.R18.))(52.R1:.))(44.R1;.)(4:.(34.$0.(8.$3?.))(35.$0.(8.$3?.)R19.(4:.$3?.(56.(57.#4.(4>.(3.&40.)R17.))(58.R17.))(43.$3?.)))(54.R1:.)))P,(2.$40.(41.R1<.)#10.)P,(2.$0.(42.(4>.(3.&40.)R19.))R1:.)P,(>.(33.(34.$0.$0.)(35.$0.$0.R1<.(18.+4.R1;.))(52.R1=.)))P,(31.(1=.=R25.)(32.R25.(3:.+2.+40.)))P,(2.$0.(23.R26.+2.)=)P,(55.R20.)P,Pm',P,(3.&40.)(5.(3.&8.))Pmo',$6.Ph',(7.$45.VL,VHI,)PLB',(8.$9.)Py0,(3.&40.)Py1,(3.&40.)Py2,(3.&40.)Py3,(3.&40.)Py4,(3.&40.)Py5,(3.&40.)Py6,(3.&40.)Py7,(3.&40.)Py8,(3.&40.)Py9,(3.&40.)Py10,(3.&40.)Py11,(3.&40.)Py12,(3.&40.)Py13,(3.&40.)Py14,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R13.R12.R11.R10.(43.$:.)R36.(52.R34.)(44.R35.)(54.R34.))(2:.$45.R13.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.(25.&40.R3<.)(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R10.R?.R>.R31.R30.R=.R<.R;.R:.R9.R8.R7.R6.R2?.R2>.R2=.R2<.R2;.R2:.R29.Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(25.&40.R3<.)Vfc,(2?.(3.&40.))R14.(30.$45.)))(2:.$45.R27.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.(25.&40.R29.)(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R15.R14.R13.R1>.R1=.(25.&40.R21.)(25.&40.(18.+4.R20.))R12.R11.R10.R?.R>.R=.R1<.R1;.R1:.R19.R18.R17.R16.Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.$59.)Vfc,(2?.(3.&40.))R28.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ SZ TL NIN RB RE RR K. flat constr:(RR) 3%nat. intros _ HLR _.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L41415794762.137L59861056406.137L62554427702.137L66395961358.13700000:00g01101>S2ra2sp2tsS1L3HLS2ra2sp2lo3SLO3ACL1T2tl2ts3SPB2KP2T02T4S2ra2sp2tsS2ra2sp2tl2ts". (* [comment removed for export] *)
  Lemma L_clean1 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pr,$0.Pxra,(3.&40.)Px3,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R1?.R1>.R1=.R1<.(43.$:.)R1;.(4:.(34.$0.$0.)(35.$0.$0.R19.(18.+4.R18.))(52.R1:.))(44.(53.R1:.))(4:.(34.$0.(8.$3?.))(35.$0.(8.$3?.)R19.(4:.$3?.(56.(57.#4.(4>.(3.&40.)R17.))(58.R17.))(43.$3?.)))(54.R1:.)))P,(55.R1;.)P,(2.$0.(42.(4>.(3.&40.)R19.))R1:.)P,(>.(33.(34.$0.$0.)(35.$0.$0.R1<.(18.+4.R1;.))(52.R1=.)))P,(31.(32.(4<.(3:.+2.+1?.))R1:.)(1=.R1:.=))(2:.$45.R23.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R1:.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R14.R13.R12.(25.&40.R1=.)(25.&40.R1>.)R11.R10.R?.R>.R=.R<.R;.R:.(25.&40.R1;.)R19.R18.R17.(25.&40.=)R16.R15.Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(25.&40.+20<:0.)Vfc,(2?.(3.&40.))R24.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ RR TL NIN Hr.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    pose proof CS_ as CS2. flat constr:(CS2) 10%nat. flclear CS2. intros _ _ _ _ _ _ _ _ EXOK _.
    flat constr:((Forall_inv EXOK)) 4%nat. intros INT _ _ KP. cbn [snd] in KP.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BR _. flat constr:((proj1 (Forall_forall _ _) BR _ INT)) 5%nat. intros T0 _ _ T4 _. cbn in T0, T4.
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
    replace (tl * 4) with (4 * tl) by lia.
    eapply call_zf_T; [exact CS_| reflexivity| exact TL| exact NIN| lia| reflexivity| exact RR|].
    clear mq moq hq LBq CS_ HH HTc MF SOK MI ST MK EXOK INT KP BR T0 T4.
    intros m2 mo2 h2 LB2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CS2.
    reopen CS2 HH HTc MF SOK MI ST MK.
    zstep. zstep; if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity].
    eapply L_clean2; [exact CS2| exact RR| exact Hr].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma L_clean1' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pr,$0.Pxra,(3.&40.)Px2,(3.&40.)Px3,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R1?.R1>.R1=.R1<.(43.$:.)R1;.(4:.(34.$0.$0.)(35.$0.$0.R19.(18.+4.R18.))(52.R1:.))(44.(53.R1:.))(4:.(34.$0.(8.$3?.))(35.$0.(8.$3?.)R19.(4:.$3?.(56.(57.#4.(4>.(3.&40.)R17.))(58.R17.))(43.$3?.)))(54.R1:.)))P,(55.R1;.)P,(2.$0.(42.(4>.(3.&40.)R19.))R1:.)P,(>.(33.(34.$0.$0.)(35.$0.$0.R1<.(18.+4.R1;.))(52.R1=.)))P,(31.(32.(4<.(3:.+2.+1?.))R1:.)(1=.R1:.=))(2:.$45.R23.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R1:.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R13.R12.R11.(25.&40.R1=.)(25.&40.R1>.)(25.&40.R1;.)R10.R?.R>.R=.R<.R;.R:.R19.R18.R17.R16.(25.&40.=)R15.R14.Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(25.&40.+20<9<.)Vfc,(2?.(3.&40.))R24.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ RR TL NIN Hr. reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. eapply L_clean1; [exact CS_| exact RR| exact TL| exact NIN| exact Hr].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L41415794762.138L59861056406.138L62123222198.138L66395961358.13800000:00g01101>S2ra2sp2tsS1L3HLS2ra2sp2lo3SLO3ACL1T2tl2ts3SPB2KP2T02T4S2ra2sp2tsS2ra2sp2tl2ts". (* [comment removed for export] *)
  Lemma L_r2fail : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pr,$0.Pxra,(3.&40.)Px2,(3.&40.)Px3,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R20.R1?.R1>.R1=.(43.$:.)R1<.(4:.(34.$0.$0.)(35.$0.$0.R1:.(18.+4.R19.))(52.R1;.))(44.(53.R1;.))(4:.(34.$0.(8.$3?.))(35.$0.(8.$3?.)R1:.(4:.$3?.(56.(57.#4.(4>.(3.&40.)R18.))(58.R18.))(43.$3?.)))(54.R1;.)))P,(55.R1<.)P,(2.$0.(42.(4>.(3.&40.)R1:.))R1;.)P,(>.(33.(34.$0.$0.)(35.$0.$0.R1=.(18.+4.R1<.))(52.R1>.)))P,(31.(32.(4<.(3:.+2.+1?.))R1;.)(1=.R1;.=))(2:.$45.R24.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R1;.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R13.R12.R11.(25.&40.R1>.)(25.&40.R1?.)(25.&40.R1<.)R10.R?.R>.R=.R<.R;.R:.R1:.R19.R18.R17.R16.R15.R14.Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(25.&40.+20<40.)Vfc,(2?.(3.&40.))R25.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ RR TL NIN Hr.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    pose proof CS_ as CS2. flat constr:(CS2) 10%nat. flclear CS2. intros _ _ _ _ _ _ _ _ EXOK _.
    flat constr:((Forall_inv EXOK)) 4%nat. intros INT _ _ KP. cbn [snd] in KP.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BR _. flat constr:((proj1 (Forall_forall _ _) BR _ INT)) 5%nat. intros T0 _ _ T4 _. cbn in T0, T4.
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep. zstep.
    replace (tl * 4) with (4 * tl) by lia.
    eapply call_zf_T; [exact CS_| reflexivity| exact TL| exact NIN| lia| reflexivity| exact RR|].
    clear mq moq hq LBq CS_ HH HTc MF SOK MI ST MK EXOK INT KP BR T0 T4.
    intros m2 mo2 h2 LB2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 CS2.
    reopen CS2 HH HTc MF SOK MI ST MK.
    zstep. zstep.
    eapply L_clean2; [exact CS2| exact RR| exact Hr].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition tstate mq moq hq LBq dW dR T tl ts : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "(31.(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.O9.O8.O7.O6.(43.$:.)O5.(4:.(34.$0.$0.)(35.$0.$0.O3.(18.+4.O2.))(52.O4.))(44.(53.O4.))(4:.(34.$0.(8.$3?.))(35.$0.(8.$3?.)O3.(4:.$3?.(56.(57.#4.(4>.(3.&40.)O1.))(58.O1.))(43.$3?.)))(54.O4.)))(31.(55.O4.)(31.(2.$0.(42.(4>.(3.&40.)O1.))O2.)(>.(33.(34.$0.$0.)(35.$0.$0.O3.(18.+4.O2.))(52.O4.))))))")
(* [comment removed for export] *).

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
    intros until ts. intros (CS_ & RR & TL & NIN) OW OR. pose proof alloc_ceiling_pos as ACP.
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
  Lemma w_cells : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)PCS,(8.(34.$0.(8.$3?.)))PCX,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(31.(48.$45.R:.(15.VdX,)(5=.(17.R5.)(25.&40.(51.R5.))(19.R5.)(5>.R5.)))(31.(1.(2.$0.(51.R5.)+1.)(2.$0.(51.R5.)-1.))(31.(2.$0.(42.(4>.(3.&40.)(4?.R5.)))(19.R5.))(31.(31.(1=.=(19.R5.))(1=.(19.R5.)$50.))(2.$0.(15.R5.)(15.VdX,))))))")
(* [comment removed for export] *).
  Proof.
    intros until CX. intros CS_. flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 4%nat. intros FLt7 _ EA _. flat constr:(FLt7) 2%nat. flclear FLt7. intros FLt8 SG. flat constr:(FLt8) 6%nat. flclear FLt8. intros HR _ _ HL HN _. rewrite <- EA. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma a_cells : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)PCS,(8.(34.$0.(8.$3?.)))PCX,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(5?.$0.Lp,$0.(5?.$0.Lsg,$0.(5?.$0.Ln,$0.(5?.(3.&40.)Lpad,(3.&40.)(31.(48.$45.R>.(15.VdA,)(5=.R4.(25.&40.R3.)R2.R1.))(1.(2.$0.R3.+1.)(2.$0.R3.-1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros until CX. intros CS_. destruct opndA as [IN| E].
    - flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ _ CS_ IN)) 2%nat. intros ((HR & _) & SG) _. do 4 eexists. exact (conj HR SG).
    - rewrite E. flat constr:((w_cells _ _ _ _ _ _ _ _ _ CS_)) 3%nat. intros HR SG _. do 4 eexists. exact (conj HR SG).
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020@L60513437445.129L60856962093.12900000F00OS1L3HLS2ra2sp2lo3SLO1eS2ra2sp1e". (* [comment removed for export] *)
  Lemma e_raw : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pls,(8.$:.)PdW,$:.PEX,(8.$9.)PCS,(8.(34.$0.(8.$3?.)))PCX,(8.(34.$0.(8.$3?.)))Pe,$:.P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(33.$:.R2.$3>.)(31.(48.$45.R<.(15.R3.)(5=.(17.R3.)(25.&40.(51.R3.))(19.R3.)(5>.R3.)))(31.(60.$45.R<.(17.R3.)(58.(4?.R3.)))(31.(2.$0.(42.(4>.(3.&40.)(4?.R3.)))(19.R3.))(31.(31.(1=.=(19.R3.))(1=.(19.R3.)+2710.))(31.(1.(2.$0.(51.R3.)+1.)(2.$0.(51.R3.)-1.))(31.(1.(2.$0.(19.R3.)=)(31.(32.=(17.R3.))(2.$0.(23.(17.R3.)+4.)=)))(31.P,(>.(2.$?.(10.R3.)$1<.))(31.(32.=(17.R4.))(31.(1=.(1>.(17.R4.)(18.+4.(19.R4.)))(22.VL,))(1=.+1.(19.R4.))))P,(2.$?.(10.R3.)$1<.)(31.(2.$0.(17.R4.)=)(2.$0.(19.R4.)=)))))))))")
(* [comment removed for export] *).
  Proof.
    intros until e. intros CS_ He. flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ _ CS_ He)) 6%nat. intros ME _ _ _ HFE _.
    destruct (mpd_raw _ _ _ _ ME ltac:(intros O; exact (proj1 (HFE O)))) as (HR & HB & HL & HN & SG & _ & PB).
    split; [exact HR|]. split; [exact HB|]. split; [exact HL|]. split; [exact HN|]. split; [exact SG|]. split; [exact PB|].
    flat constr:(ME) 2%nat. intros FLt9 _. flat constr:(FLt9) 6%nat. flclear FLt9. intros _ _ _ _ _ HO. split.
    - intros NNL. pose proof CS_ as CS2. dest_cs CS2. destruct (mpd_limbs_low psegs L HI HLS DIMG HND IMGC SW ROIMG h LB SP lo SPc dX es ACL ltac:(lia) ltac:(lia) HTOP
                 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0))))))) DHI NSX WRX (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok
                 _ _ _ _ _ HH ME NNL) as [P0 P4].
      split; [exact P0|]. split; [exact P4|]. destruct (md_own e); [exfalso; exact (NNL eq_refl)| exact (proj1 HO)| exact (proj1 HO)].
    - intros O. rewrite O in HO. exact HO.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L2416225489.6   L28625184349.4  L28625516220.4  L40377502679.5  L55344112009.6  L61039157933.9  L65476495129.3  L66096060529.14400000B00N00Y00g01901T01_02<S2dR1T2tl1k2Hk3DRTS1T2tl2ts2TLS1T2tl1k2HkS2sp2lo1K4HKloS2dW2dR2an3Han3DWRS1L2sp2lo3ACL2dR1K4HKlo3PR4S2dW2an3HanS2ra2sp2dW2dR1T2ts3xs'3ts'2LT". (* [comment removed for export] *)
  Lemma core_munch : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pm2,P,(3.&40.)(5.(3.&8.))Pan,$0.Pk,$0.PK,$0.Pxs',(8.(3.&40.))Pts',(8.(3.&40.))P,(5:.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(2.$?.(10.R<.)$16.)P,(2.$?.(10.R<.)$16.)P,(61.(4:.(34.$0.$0.)(35.$0.$0.(17.R>.)(1>.(17.R>.)(18.+4.R8.)))(4:.(34.$0.$0.)(35.$0.$0.R<.(1>.R<.(18.+4.R7.)))(4:.(34.$0.$0.)(35.$0.$0.(20.(1>.(13.&40.Vsp,)-60.)R6.)(1>.(13.&40.Vsp,)-60.))(43.(34.$0.$0.)))))R12.R9.)P,(62.$45.R13.R:.)P,(27.$45.R;.)P,(1?.$45.R<.Vlo,(1>.(13.&40.Vsp,)-60.))P,(31.(1=.=R<.)(1=.R<.(19.R12.)))P,(31.(1=.=R<.)(1=.R<.R10.))P,(1=.=R<.)P,(1=.Vlo,(20.(1>.(13.&40.Vsp,)-60.)R=.))P,(63.$45.R11.(17.R16.)R=.)P,(2.$0.(42.(4>.(3.&40.)R>.))(19.R17.))P,(63.$45.R13.R16.R>.)P,(2.$40.(4>.(3.&40.)R?.)(4>.(3.&40.)R15.))(5:.R15.R1=.R1<.R1;.(64.R1:.R11.)R19.R18.R17.R10.)")
(* [comment removed for export] *).
  Proof.
    intros until ts'. intros TS OW OR MU WM MI2 ST2 Han Hk HK HKlo UX LX UT LT.
    flat constr:((t_facts _ _ _ _ _ _ _ _ _ TS OW OR)) 7%nat. intros FLt10 FLt11 FLt12 DWT DRT DWR EF. flat constr:(FLt10) 6%nat. flclear FLt10. intros PW0 PW4 PALW NW1 HLW HNW. flat constr:(FLt11) 5%nat. flclear FLt11. intros T0 T4 TAL TL0 TIMG. flat constr:(FLt12) 6%nat. flclear FLt12. intros PR0 PR4 PALR NR1 HLR HNR.
    flat constr:(TS) 4%nat. flclear TS. intros CS_ RR TL NIN. pose proof alloc_ceiling_pos as ACP.
    pose proof CS_ as CS2. flat constr:(CS2) 21%nat. flclear CS2. intros _ _ _ _ _ _ _ _ EXOK _ _ _ _ _ _ _ _ _ _ CXH _.
    unfold mpd_cx in CXH. rewrite OR in CXH. pose proof (Forall_inv (Forall_inv_tail CXH)) as CXR. cbn [fst snd] in CXR.
    split; [| split; [exact RR| split; [rewrite <- TL, LT; reflexivity| exact NIN]]].
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
    flat constr:(TS) 4%nat. flclear TS. intros CS_ RR TL NIN.
    flat constr:(ME0) 2%nat. intros FLt13 _. flat constr:(FLt13) 6%nat. flclear FLt13. intros _ _ _ HLE0 HNE0 HOE0. flat constr:(MN0) 2%nat. intros FLt14 _. flat constr:(FLt14) 6%nat. flclear FLt14. intros _ _ _ HLN0 HNN0 HON0.
    assert (NNn : md_own dN <> LNull) by (intros O; rewrite O in HON0; lia). assert (NNe : md_own dE <> LNull) by (intros O; rewrite O in HOE0; lia).
    flat constr:((EF dN opndN NNn)) 6%nat. intros DNT DNX PN0 PN4 PALN _. flat constr:((EF dE opndE NNe)) 6%nat. intros DET DEX PE0 PE4 PALE _.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 5%nat. intros CN_ BN HLN HNN _. flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 5%nat. intros CE_ BE HLE HNE _.
    flat constr:((w_cells _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros CW _.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros FLt15 _. flat constr:(FLt15) 2%nat. flclear FLt15. intros FLt16 _. flat constr:(FLt16) 6%nat. flclear FLt16. intros _ _ _ _ _ HOW. rewrite OW in HOW. flat constr:(HOW) 4%nat. flclear HOW. intros _ _ _ UW.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros CH0 _.
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

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L244663455.179  L36253289358.15 L3752735275.17  L41114218273.15 L41850123796.17 L42250439301.147L42252550708.176L55808652373.15 L61272441839.179L65034811952.17600000=00J00K00l00m01S02902T02a02nS2ra2sp2dW2tsS1L2sp2lo3SLOFS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPFS1L3HLS2ra2sp2lo3SLO3ACL2dW2ts3SPB3ACPS1L3HLS2ra2sp2lo3SLO3ACL2dW2ts3SPB3ACPS1L2HI2sp1h4HTOP2hq3SPB3HTcS2ra2sp2dW2tsS2ra2sp2dW2ts". (* [comment removed for export] *)
  Lemma L_addfix : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pxra,(3.&40.)Px5,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(5:.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)(2:.$45.R1;.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R13.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R10.R?.R>.(25.&40.R15.)(25.&40.R16.)R=.R<.R;.R:.R9.R8.R7.R6.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R12.(25.&40.=)(25.&40.(15.VdE,))R11.Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(25.&40.+20=>8.)Vfc,(2?.(3.&40.))R1<.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros (CS_ & RR & TL & NIN).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 6%nat. intros MN CRN_ CRNL_ LN HFN ASN.
    flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 2%nat. intros SWN OWN.
    flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros SWW OWW.
    pose proof HAS as SA. unfold add_sub_mpi_stmt_e, P_ADD_SUB_MPI in SA.
    eapply aevtM_cut.
    { eapply (SA 1 ltac:(left; reflexivity)) with (dX := dW) (dA := dN) (dB := dW) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?EA; reflexivity).
      destruct SWN as [E|[X|X]]; [left; symmetry; exact E| right; right; exact X| right; left; exact X]. }
    clear SA. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
    replace (ret_pc (Z_to_bv 64 0x20dfc)) with (Z_to_bv 64 0x20dfc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR2) 2%nat. flclear RR2. intros R1 FLt17. flat constr:(FLt17) 4%nat. flclear FLt17. intros EA2 PAD2 FRB2 NLE2.
    assert (CS2 : CST m2 mo2 h2 LB2 [] dW2 ((T, 4 * tl) :: mpd_blk dR) (frame (rr_cells dR)) ((T, [CB (4 * length ts)%nat (u32s ts)]) :: mpd_cx dR)).
    { eapply mc_binop_w; [exact CS_| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB2| exact PAD2| exact NLE2]. }
    assert (Hr : -2^31 < r <= 0) by (destruct R1 as [[-> _]| ->]; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia).
    clear CS_ MA2 OUT2 PX2. reopen CS2 HH HTc MF SOK MI ST MK.
    zstep. eapply L_clean1'; [exact CS2| exact RR| exact TL| exact NIN| exact Hr].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@D4791203545.177 L15043131708.143L24897143244.155L25218070450.170L28922983928.173L36459744067.142L36950939294.154L38250001509.155L41096692127.145L42379109178.153L44622288685.176L49698585326.176L52514160305.143L54379423251.153L56534037331.155L57631424731.155L58234116789.155L59310679012.138L59314841581.142L61274419438.143L61274419565.135L62261528799.176L63784808468.17600000100B00V00j01>01O01c02D02U02m02n03X03i04@04X05<05T05h06K06\06f06g07QFS2ra2sp2dE2ts3ULES2ra2sp2dE2dW2ts3ULES2ra2sp2dE2dW2ts3ULES2ra2sp2dE2dW2ts3ULES2ra2sp2dE2ts3ULES2ra2sp2dE2dW2ts3ULES2ra2sp2dE2dW2ts3SPB3PE03ULE1k2HkS2ra2sp2dE2ts3ULES2ra2sp2dE2dW2ts3ULE3HNWFS2ra2sp2dX2dE2dW2ts3ULE3sg'2HB5Ha_st5Hl_stS2ra2sp2dE2ts3ULES2ra2sp2dX2dE2dW2ts3ULES2ra2sp2dE2dW2ts3ULE3HNWS2ra2sp2dE2dW2ts3SPB3PE03ULE3HLW3PW0S2ra2sp2dE2dW2ts3ULE3PW0S2ra2sp2dE2ts3EN12N0S2ra2sp2dE2ts3EN13SPB3HLE3PE03ULE1NS2ra2sp2dE2ts3ULES2ra2sp2tsFS2ra2sp2dX2dE2dW2ts3ULE3sg'2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  Lemma L_tail : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pxra,(3.&40.)Px5,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(5:.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)P,(2.$?.(10.R18.)$16.)P,(1=.+1.(19.VdE,))(2:.$45.R1=.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R15.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R12.R11.R10.(25.&40.R17.)(25.&40.R18.)R?.R>.R=.R<.R;.R:.R9.R8.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R14.(25.&40.=)(25.&40.(15.VdE,))R13.Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(25.&40.+20=:4.)Vfc,(2?.(3.&40.))R1>.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros (CS_ & RR & TL & NIN) OW EN1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((a_cells _ _ _ _ _ _ _ _ _ CS_)) 6%nat. intros pa sga na pada CA_ SGA. unfold mpi_cells in CA_.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep; if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) zstep. zstep. eapply L_clean1; [exact CS_| exact RR| exact TL| exact NIN| lia]. }
    clear K0 CA_ SGA.
    (* [comment removed for export] *)
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 8%nat. intros CE_ BE HLE HNE _ PBE HFE _. unfold mpi_cells in CE_.
    destruct PBE as [N0|[PE0 PE4]]; [exfalso; lia|].
    pose proof (u32s_length (md_limbs dE)) as ULE. pose proof (u32ro_bound _ _ _ _ BE) as BEB.
    zstep. rd8 BE 0. zstep. zstep; if_cases K1; zify_cond K1.
    2:{ zstep. zstep. eapply L_clean1; [exact CS_| exact RR| exact TL| exact NIN| lia]. }
    clear K1 CE_ BE.
    (* [comment removed for export] *)
    flat constr:((w_cells _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CW SGW HLW HNW EAW. unfold mpi_cells in CW. unfold MPI_MAX_LIMBS in HNW.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 9%nat. intros FLt18 NSW _ _ LW _ _ HFW _. flat constr:(FLt18) 2%nat. flclear FLt18. intros FLt19 _. flat constr:(FLt19) 6%nat. flclear FLt19. intros _ _ _ _ _ HOW.
    rewrite OW in HOW. flat constr:(HOW) 4%nat. flclear HOW. intros NW1 _ PALW UW. flat constr:((HFW OW)) 3%nat. intros PW0 PW4 _.
    zstep. zstep. rewrite zx16_small by lia. zstep.
    pose proof HCZ as SCZ. unfold mpi_core_check_zero_ct_stmt, P_MPI_CORE_CHECK_ZERO_CT in SCZ.
    assert (PALW4 : md_p dW mod 4 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in PALW; [| lia]; (flat constr:(PALW) 2%nat; flclear PALW; intros k Hk); exists (4 * k); lia).
    eapply aevtM_cut_evt; [exact MK| eapply SCZ with (A := md_p dW) (n := md_n dW) (xs := md_limbs dW); try reflexivity;
      first [exact (u32arr_ro _ _ _ _ UW)| exact MI| exact PALW4| lia] |].
    clear SCZ. cbv beta. intros ms' PO. unfold mpi_core_check_zero_ct_post in PO.
    flat constr:(PO) 23%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? z -> _ _ _ -> Z0 _.
    replace (ret_pc (Z_to_bv 64 0x20dd8)) with (Z_to_bv 64 0x20dd8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    set (sg' := if z =? 0 then 1 else -1).
    assert (SG' : sg' = 1 \/ sg' = -1) by (subst sg'; destruct (z =? 0); [left| right]; reflexivity).
    pose proof (munch_refl [(md_addr dX, md_addr dX + 16)] mq) as MU. pose proof (wmono_refl psegs mq) as WM.
    unfold ct_mask. destruct (Z.eqb_spec z 0) as [Ez|Nz].
    - zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      match goal with H : rw_cells psegs m1 (md_addr dX) _ |- _ => rename H into CW1 end.
      assert (CS1 : CST m1 moq hq LBq [] (set_sg dW 1) ((T, 4 * tl) :: mpd_blk dR) (frame (rr_cells dR)) ((T, [CB (4 * length ts)%nat (u32s ts)]) :: mpd_cx dR)).
      { eapply mc_sign_w; [exact CS_| rewrite EAW; exact MU| exact WM| assumption| rewrite EAW; unfold mpi_cells; exact CW1| left; reflexivity]. }
      clear CS_ MU WM CW1. reopen CS1 HH HTc MF SOK MI ST MK.
      eapply L_addfix. split; [exact CS1| exact (conj RR (conj TL NIN))].
    - zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      match goal with H : rw_cells psegs m1 (md_addr dX) _ |- _ => rename H into CW1 end.
      assert (CS1 : CST m1 moq hq LBq [] (set_sg dW (-1)) ((T, 4 * tl) :: mpd_blk dR) (frame (rr_cells dR)) ((T, [CB (4 * length ts)%nat (u32s ts)]) :: mpd_cx dR)).
      { eapply mc_sign_w; [exact CS_| rewrite EAW; exact MU| exact WM| assumption| rewrite EAW; unfold mpi_cells; exact CW1| right; reflexivity]. }
      clear CS_ MU WM CW1. reopen CS1 HH HTc MF SOK MI ST MK.
      eapply L_addfix. split; [exact CS1| exact (conj RR (conj TL NIN))].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0@L11370829691.20 L11371222877.27 L11978601293.21 L11978732395.27 L14402269102.19 L14402662280.27 L1473882406.21  L1474275584.27  L21549060627.19 L22597135989.177L29964740920.19 L30502797694.22 L30502928728.27 L30877874445.178L30877874480.203L3192925298.203 L33136280895.21 L33136395324.5  L33136411929.27 L36005622013.203L38142135889.19 L41114214998.20 L41114608240.27 L42252534025.178L42252534068.203L47492451383.170L48276669612.203L48874667665.19 L48875060919.27 L51697648194.27 L51697779300.19 L54084288190.203L54379423251.170L54423800513.122L60315857501.27 L60315988603.20 L64906471638.27 L64906602736.20 00000100a00b01G01H01I01J01o02F02d03@03A03i04A04i05X05Y05j06K07T07n07o08c09g0;;0;S0<;0<<0<i0=V0=W0>?0>Z0>k0>l0>m0>n0>oFS1L3HLS2sp2dN2lo3SLO3ACL2dW2dR1T2tl2ts3SPB2TL2T4FS1L2sp2dN2lo3ACL2dW2dR2ts3SPB3PW43HLWFFFS1L2sp2dN2lo3ACL2dW2dR2ts3SPB3HLN3PN4S2dE2dN2dW2dR2ts2N13HNNS2ra2sp2dE2dN2NN2dW2dR1T2ts2N1S2dE2dN2dW2dR2ts3NLE3HLW3HLNFS1L2sp2dN2lo3ACL2dW2dR1T2tl2ts3SPB2TL2T4S2ra2sp2dE2dN2dW2dR1T2tsS2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2S2ra2sp2dE2dN2dW2dR1T2ts2N13NLE3xs23ts23LX23LT2FS1L3HLS2sp2lo3SLOS1L3HLS2sp2dN2lo3SLO2dW2dR2ts3SPBS2ra2sp2dE2dN2dW2dR1T2tl2ts2N13SPB3TL23PW02T03PR03PN03PE03xs23ts23LX23LT2S2dE2dN2dW2dR2tl2ts3TL22TLFS1L3HLS2sp2dN2lo3SLO3ACL3SPA2dW2dR2ts2N13SPB3PN03PN4S1L3HLS2ra2sp2dE2dN2lo3SLO3ACL2dW2dR1T2ts3SPB3ACP3PW02T03PR03PN03PE0S1L3HLS2ra2sp2dE2dN2lo3SLO3ACL2dW2dR1T2ts3SPB3ACP3PW02T03PR03PN03PE03xs23ts23LX23LT2S2ra2sp2dE2dN2dW2dR1T2tsS2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2FS1L3HLS2sp2dN2lo3SLO3ACL2dW2dR2ts3SPB3HLN3PN4S1L3HLS2sp2dN2lo3SLO3ACL2dW2dR2ts3SPB3PW43HLWFS2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2S2ra2sp2dX2dE2dN2dW2dR1T2tsS2ra2sp2dN2N13SPBFFFF". (* [comment removed for export] *)
  Lemma L_core3 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pxra,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(5:.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(2.$?.(10.R17.)$16.)P,(2.$?.(10.R17.)$16.)P,(1=.+1.(19.VdN,))P,(1=.(19.VdN,)(19.R1:.))P,(1=.(19.VdN,)(19.R1:.))P,(1=.+1.(19.VdE,))P,(2.$0.R1:.(65.(19.VdN,)(19.VdE,)))(2:.$45.R21.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R19.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R17.R16.R15.(25.&40.R1;.)(25.&40.R1<.)R14.R13.R12.R11.R10.R?.R>.R=.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R18.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.+20=88.)Vfc,(2?.(3.&40.))R22.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros TS OW OR N1 NLE NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    assert (TL2 : 2 * md_n dN + 1 <= tl) by (rewrite TLE; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    flat constr:(TS) 4%nat. intros CS_ RR_ _ NIN. kit TS OW OR N1 E1. reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep. rewrite zx16_small by lia. zstep. zstep. zstep. zstep.
    pose proof HFROM as STM. unfold mpi_core_from_mont_rep_stmt, P_MPI_CORE_FROM_MONT_REP in STM.
    eapply aevtM_cut_evt; [exact MK| eapply STM with (X := md_p dW) (A := md_p dW) (N := md_p dN) (an := md_n dN) (T := T) (lo := lo)
        (xs := md_limbs dW) (ys := md_limbs dW) (ns := md_limbs dN) (ts := ts);
        unfold MPI_CORE_FROM_MONT_REP_STACK; rewrite ?unsigned_lit by lia;
        first [ exact UW | exact (u32arr_ro _ _ _ _ UW) | exact RON | exact UT | exact MI | exact ST | reflexivity
              | apply mod16_4; assumption | assumption
              | clear - N1 HNN HLN HLE HNE HLW HNW NLE NLR HLR HNR TL TL2; lia
              | clear - PW0 PW4 T0 T4 PR0 PR4 PN0 PN4 N1 HLW HLR HLN TL ACL SLO SPB HLS SPA; lia
              | rewrite ?HLW, ?HLR, ?HLN, ?HLE, ?TL; assumption
              | match goal with |- ?g => idtac "REMAIN3" g end ] |].
    clear STM. cbv beta. intros ms' PO. unfold mpi_core_from_mont_rep_post in PO. unfold MPI_CORE_FROM_MONT_REP_STACK in PO.
    flat constr:(PO) 29%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 xs2 ts2 -> MU2 WM2 MI2 UX2 LX2 _ UT2 LT2 _ ST2.
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x20da4)) with (Z_to_bv 64 0x20da4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (TS2 : tstate m2 moq hq LBq (set_limbs dW xs2) dR T tl ts2).
    { eapply (core_munch _ _ _ _ _ _ _ _ _ _ (md_n dN) (2 * md_n dN + 1) 208); [exact TS| exact OW| exact OR| | exact WM2| exact MI2| exact ST2| lia| lia| lia| clear - SLO HLS; lia| exact UX2| rewrite <- HLW, <- LX2; reflexivity| exact UT2| exact LT2].
      replace (bv_unsigned sp + -96 - 208) with (bv_unsigned sp + -96 + -208) by lia. exact MU2. }
    flat constr:(TS2) 2%nat. intros CS2 _. reopen CS2 HH HTc MF SOK MI ST MK.
    eapply L_tail; [exact TS2| exact OW| exact E1].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@L11370829691.20 L11371221981.32 L11978601293.21 L11978733547.32 L14402269102.19 L14402661128.32 L14729682622.202L1473882406.21  L1474276736.32  L16499464709.19 L16499859107.32 L16677079629.202L17437330228.32 L17437724562.20 L20424863796.32 L20424995986.19 L22597135989.176L2416027249.32  L2416419543.20  L29638259751.19 L29638389889.32 L29762660275.169L29964740920.19 L30502797694.22 L30502929880.32 L31225360556.202L3192925298.202 L32466267962.21 L32466398108.32 L35691656589.177L35691656624.202L36459744067.169L41114214998.20 L41114609392.32 L42252534025.177L42252534068.202L45353657683.176L47492451383.169L48874667665.19 L48875059767.32 L51697649346.32 L51697779300.19 L51892697081.19 L54379423251.169L5584136771.19  L5693442703.21  L5693574697.32  L60315858653.32 L60315988603.20 L60681106403.176L64906472534.32 L64906602736.20 L67747486015.21 L67747862588.5  L67747880345.32 00000100d00e01M01N01O02702802`02a03Q04@04A04B05205305Q05R05S05T05U05m06Q06R07=07e08T08U09=09U0:=0:U0:V0;M0<Q0=e0>D0>\0>]0?M0@=0@>0@T0@o0AC0AD0Al0Am0An0BF0BG0BH0BI0BZ0C>FS1L3HLS2sp2dE2dN2lo3SLO3ACL2dW2dR1T2tl2ts3SPB2TL2T4FS1L2sp2dE2dN2lo3ACL2dW2dR2ts3SPB3PW43HLWFFS2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2FS1L2sp2dE2dN2lo3ACL2dW2dR2ts3SPB3HLN3PN4FS1L3HLS2sp2dE2dN2lo3SLO3ACL2dW2dR2ts3SPB3PR43HLRS2ra2sp2dE2dN2dW2dR1T2tl2ts3TL03xs23ts23LX23LT2FFS1L3HLS2sp2dE2dN2lo3SLO3ACL2dW2dR2ts3SPB3HLE3PE4FS2ra2sp2dE2dN2NN2dW2dR1T2ts2N1FFFFS2ra2sp2dE2dN2dW2dR1T2tsS2dE2dN2dW2dR2ts3NLE3HLW3HLN3NLR3HLRFS1L2sp2dE2dN2lo3ACL2dW2dR1T2tl2ts3SPB2TL2T4S2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2S2ra2sp2dE2dN2dW2dR1T2ts2N13NLE3xs23ts23LX23LT2FS1L2sp2dE2dN2lo3ACL2dW2dR2ts3SPB3PR43HLRS2ra2sp2dE2dN2dW2dR1T2tsS2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2S2ra2sp2dE2dN2dW2dR1T2tsFS1L3HLS2sp2dE2dN2lo3SLO3ACL3SPA2dW2dR2ts2E13SPB3PE03PE4S1L3HLS2ra2sp2dE2dN2lo3SLO3ACL2dW2dR1T2ts3SPB3ACP3PW02T03PR03PN03PE0S1L3HLS2ra2sp2dE2dN2lo3SLO3ACL2dW2dR1T2ts3SPB3ACP3PW02T03PR03PN03PE03xs23ts23LX23LT2S2ra2sp2dE2dN2dW2dR1T2ts2E13HNES2ra2sp2dE2dN2dW2dR1T2tsFS1L3HLS2sp2dE2dN2lo3SLO3ACL2dW2dR2ts3SPB3HLN3PN4S1L3HLS2sp2dE2dN2lo3SLO3ACL2dW2dR2ts3SPB3PW43HLWFS2dE2dN2dW2dR2tl2ts2TLS2ra2sp2dX2dE2dN2dW2dR1T2tsS2dE2dN2dW2dR2ts3HLEFS1L2sp2dE2dN2lo3ACL2dW2dR2ts3SPB3HLE3PE4FFS2ra2sp2dE2dN2dW2dR1T2tsFFFS1L3HLS2sp2lo3SLOS1L3HLS2sp2dE2dN2lo3SLO2dW2dR2ts3SPB". (* [comment removed for export] *)
  Lemma L_core2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pxra,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(5:.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(2.$?.(10.R17.)$16.)P,(2.$?.(10.R17.)$16.)P,(1=.+1.(19.VdN,))P,(1=.(19.VdN,)(19.R1:.))P,(1=.(19.VdN,)(19.R1:.))P,(1=.+1.(19.VdE,))P,(2.$0.R1:.(65.(19.VdN,)(19.VdE,)))(2:.$45.R21.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R19.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R17.R16.R15.(25.&40.R1;.)(25.&40.R1<.)R14.R13.R12.R11.R10.R?.R>.R=.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R18.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.+20=48.)Vfc,(2?.(3.&40.))R22.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros TS OW OR N1 NLE NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(TS) 4%nat. intros CS_ RR_ _ NIN. kit TS OW OR N1 E1. reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep. rewrite zx16_small by lia. zstep. zstep. rewrite zx16_small by lia. zstep. zstep. zstep.
    zstep; if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; cbn; lia].
    clear K0. zstep. zstep. zstep.
    pose proof HCEM as STM. unfold mpi_core_exp_mod_stmt, P_MPI_CORE_EXP_MOD in STM.
    eapply aevtM_cut_evt; [exact MK| eapply STM with (X := md_p dW) (A := md_p dW) (N := md_p dN) (an := md_n dN) (E := md_p dE) (en := md_n dE) (RR := md_p dR) (T := T) (lo := lo)
        (xs := md_limbs dW) (ys := md_limbs dW) (ns := md_limbs dN) (es := md_limbs dE) (rs := md_limbs dR) (ts := ts); try reflexivity |].
    { unfold mpi_core_exp_mod_pre, MPI_CORE_EXP_MOD_STACK. rewrite ?unsigned_lit by lia. rewrite <- TLE.
      repeat match goal with |- _ /\ _ => split end;
        first [ exact UW | exact (u32arr_ro _ _ _ _ UW) | exact RON | exact ROE | exact ROR | exact UT | exact MI | exact ST | reflexivity
              | apply mod16_4; assumption | assumption
              | clear - N1 E1 HNN HLN HLE HNE HLW HNW NLE NLR HLR HNR TL; lia
              | clear - PW0 PW4 T0 T4 PR0 PR4 PN0 PN4 PE0 PE4 N1 E1 HLW HLR HLN HLE TL ACL SLO SPB HLS SPA; lia
              | rewrite ?HLW, ?HLR, ?HLN, ?HLE, ?TL; assumption
              | match goal with |- ?g => idtac "REMAIN2" g end ]. }
    clear STM. cbv beta. intros ms' PO. unfold mpi_core_exp_mod_post in PO. unfold MPI_CORE_EXP_MOD_STACK in PO.
    flat constr:(PO) 28%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 xs2 ts2 -> MU2 WM2 MI2 UX2 LX2 _ UT2 LT2 ST2.
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia. rewrite TL in MU2.
    replace (ret_pc (Z_to_bv 64 0x20d88)) with (Z_to_bv 64 0x20d88) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (TS2 : tstate m2 moq hq LBq (set_limbs dW xs2) dR T tl ts2).
    { eapply (core_munch _ _ _ _ _ _ _ _ _ _ (md_n dN) tl 400); [exact TS| exact OW| exact OR| | exact WM2| exact MI2| exact ST2| lia| lia| lia| clear - SLO HLS; lia| exact UX2| rewrite <- HLW, <- LX2; reflexivity| exact UT2| exact LT2].
      replace (bv_unsigned sp + -96 - 400) with (bv_unsigned sp + -96 + -400) by lia. exact MU2. }
    flat constr:(TS2) 2%nat. intros CS2 _. reopen CS2 HH HTc MF SOK MI ST MK.
    eapply L_core3; [exact TS2| exact OW| exact OR| exact N1| exact NLE| exact NLR| exact E1| exact TLE].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00a0@L10205084561.178L1054875052.218 L11370829691.20 L11371222877.27 L11978601293.21 L11978732395.27 L14402269102.19 L14402662280.27 L1473882406.21  L1474275584.27  L16499464709.19 L16499857955.27 L21099454780.5  L21099503641.27 L21099896895.21 L21549060627.19 L22583063757.192L2416026353.27  L2416419543.20  L25653858103.192L29762660275.185L29964740920.19 L30502797694.22 L30502928728.27 L3192925298.218 L32466267962.21 L32466399004.27 L36005622013.218L38142135889.19 L41114214998.20 L41114608240.27 L42252534025.193L42252534068.218L46533990147.178L47492451383.170L47492451383.185L48874667665.19 L48875060919.27 L51697648194.27 L51697779300.19 L54379423251.185L54423800513.122L55044134590.218L60315857501.27 L60315988603.20 L63693989261.193L63693989296.218L64906471638.27 L64906602736.20 00000f01N01O02?02@02e02f02g02h03M03N04;04L04m04n05E05c05d05e06=06U07907:07b08Q08R0970:@0:Z0:[0;O0<S0=g0>C0>[0?30?40?a0@N0@O0@j0A;0Ac0Ad0Ae0B=0Be0Bf0BgS2ra2sp2dE2dN2dW2dR1T2ts2N13SPB3HLN3PW02T03PR03PN03PE0S2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2FS1L3HLS2sp2dN2lo3SLO3ACL2dW2dR1T2tl2ts3SPB2TL2T4FS1L2sp2dN2lo3ACL2dW2dR2ts3SPB3PW43HLWFFFS1L2sp2dN2lo3ACL2dW2dR2ts3SPB3HLN3PN4FS1L3HLS2sp2dN2lo3SLO3ACL2dW2dR2ts3SPB3PR43HLRS1L3HLS2sp2lo3SLOS1L3HLS2sp2dN2lo3SLO2dW2dR2ts3SPBFS2dE2dN2dW2dR2ts2N13HNNS2ra2sp2dE2dN2NN2dW2dR1T2ts2N1FFS2ra2sp2dE2dN2dW2dR1T2tsS2ra2sp2dE2dN2dW2dR1T2tsS2dE2dN2dW2dR2ts3NLE3HLW3NLR3HLR3HLNFS1L2sp2dN2lo3ACL2dW2dR1T2tl2ts3SPB2TL2T4S2ra2sp2dE2dN2dW2dR1T2ts2N13NLE3xs23ts23LX23LT2FS1L2sp2dN2lo3ACL2dW2dR2ts3SPB3PR43HLRS2ra2sp2dE2dN2dW2dR1T2tl2ts2N13SPB3TL23PW02T03PR03PN03PE03xs23ts23LX23LT2S2dE2dN2dW2dR2tl2ts3TL22TLFS1L3HLS2sp2dN2lo3SLO3ACL3SPA2dW2dR2ts2N13SPB3PN03PN4S1L3HLS2ra2sp2dE2dN2lo3SLO3ACL2dW2dR1T2ts3SPB3ACP3PW02T03PR03PN03PE0S1L3HLS2ra2sp2dE2dN2lo3SLO3ACL2dW2dR1T2ts3SPB3ACP3PW02T03PR03PN03PE03xs23ts23LX23LT2S2ra2sp2dE2dN2dW2dR1T2ts3PN0S2ra2sp2dE2dN2dW2dR1T2tsS2ra2sp2dE2dN2dW2dR1T2tsFS1L3HLS2sp2dN2lo3SLO3ACL2dW2dR2ts3SPB3HLN3PN4S1L3HLS2sp2dN2lo3SLO3ACL2dW2dR2ts3SPB3PW43HLWFS2ra2sp2dX2dE2dN2dW2dR1T2tsS2ra2sp2dN2N13SPBS2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2FFS2ra2sp2dE2dN2dW2dR1T2tsS2ra2sp2dE2dN2dW2dR1T2ts3xs23ts23LX23LT2FF". (* [comment removed for export] *)
  Lemma L_core : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pxra,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(5:.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(2.$?.(10.R17.)$16.)P,(2.$?.(10.R17.)$16.)P,(1=.+1.(19.VdN,))P,(1=.(19.VdN,)(19.R1:.))P,(1=.(19.VdN,)(19.R1:.))P,(1=.+1.(19.VdE,))P,(2.$0.R1:.(65.(19.VdN,)(19.VdE,)))(2:.$45.R21.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R19.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R17.R16.R15.(25.&40.R1;.)(25.&40.R1<.)R14.R13.R12.R11.R10.R?.R>.R=.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R18.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.+20=1<.)Vfc,(2?.(3.&40.))R22.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros TS OW OR N1 NLE NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    assert (TL2 : 2 * md_n dN + 1 <= tl) by (rewrite TLE; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    flat constr:(TS) 4%nat. intros CS_ RR_ _ NIN. kit TS OW OR N1 E1. reopen CS_ HH HTc MF SOK MI ST MK.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof HMMI as SMI. unfold mpi_core_montmul_init_stmt, P_MPI_CORE_MONTMUL_INIT in SMI.
    eapply aevtM_cut_evt; [exact MK| eapply SMI with (N := md_p dN) (ns := md_limbs dN); first [exact RON| exact MI| exact PALN| reflexivity| lia] |].
    clear SMI. cbv beta. intros ms' PO. unfold mpi_core_montmul_init_post in PO.
    flat constr:(PO) 19%nat. flclear PO. intros ? ? ? wmm ? ? ? ? ? ? ? ? ? ? ? -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x20d24)) with (Z_to_bv 64 0x20d24) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite zx16_small by lia. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof HTOM as STM. unfold mpi_core_to_mont_rep_stmt, P_MPI_CORE_TO_MONT_REP in STM.
    eapply aevtM_cut_evt; [exact MK| eapply STM with (X := md_p dW) (A := md_p dW) (RR := md_p dR) (N := md_p dN) (an := md_n dN) (T := T) (lo := lo)
        (xs := md_limbs dW) (ys := md_limbs dW) (rs := md_limbs dR) (ns := md_limbs dN) (ts := ts);
        unfold MPI_CORE_MONTMUL_STACK; rewrite ?unsigned_lit by lia;
        first [ exact UW | exact (u32arr_ro _ _ _ _ UW) | exact ROR | exact RON | exact UT | exact MI | exact ST | reflexivity
              | apply mod16_4; assumption | assumption
              | clear - N1 HNN HLN HLE HNE HLW HNW NLE NLR HLR HNR TL TL2; lia
              | clear - PW0 PW4 T0 T4 PR0 PR4 PN0 PN4 N1 HLW HLR HLN TL ACL SLO SPB HLS SPA; lia
              | rewrite ?HLW, ?HLR, ?HLN, ?HLE, ?TL; assumption
              | match goal with |- ?g => idtac "REMAIN1" g end ] |].
    clear STM. cbv beta. intros ms' PO. unfold mpi_core_montmul_post in PO. unfold MPI_CORE_MONTMUL_STACK in PO.
    flat constr:(PO) 29%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 xs2 ts2 -> MU2 WM2 MI2 UX2 LX2 _ UT2 LT2 _ ST2.
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x20d48)) with (Z_to_bv 64 0x20d48) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (TS2 : tstate m2 moq hq LBq (set_limbs dW xs2) dR T tl ts2).
    { eapply (core_munch _ _ _ _ _ _ _ _ _ _ (md_n dN) (2 * md_n dN + 1) 192); [exact TS| exact OW| exact OR| | exact WM2| exact MI2| exact ST2| lia| lia| lia| clear - SLO HLS; lia| exact UX2| rewrite <- HLW, <- LX2; reflexivity| exact UT2| exact LT2].
      replace (bv_unsigned sp + -96 - 192) with (bv_unsigned sp + -96 + -192) by lia. exact MU2. }
    flat constr:(TS2) 2%nat. intros CS2 _. reopen CS2 HH HTc MF SOK MI ST MK.
    eapply L_core2; [exact TS2| exact OW| exact OR| exact N1| exact NLE| exact NLR| exact E1| exact TLE].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma t_binop_w : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pm2,P,(3.&40.)(5.(3.&8.))Pmo2,$6.Ph2,(7.$45.VL,VHI,)PLB2,(8.$9.)PdW2,$:.P,(5:.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(;.$45.VL,VHI,R4.R3.R6.R5.)P,(2.$0.(1;.$45.VL,VHI,R5.)(1;.$45.VL,VHI,R>.))P,(47.R10.R7.)P,(<.$45.R9.R6.R5.)P,(66.R10.R?.R7.R6.)P,(67.$45.VL,R11.(1>.(13.&40.Vsp,)-60.)(68.R10.)R14.R;.)P,(28.$45.VL,R<.)P,(27.$45.R=.)P,(1?.$45.R>.Vlo,(1>.(13.&40.Vsp,)-60.))P,Pb,$9.P,(33.$9.R1.(52.R<.))(1.(33.$9.R2.(52.R16.))(>.(33.$9.R2.R17.)))P,(2.(3.&40.)(5>.R<.)(5>.R15.))P,(1=.(19.R16.)(19.R=.))(5:.R12.R11.R10.R?.R>.R16.R15.R14.R13.)")
(* [comment removed for export] *).
  Proof.
    intros until dW2. intros (CS_ & RR & TL & NIN) HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2 FRB PAD NLE.
    split; [| exact (conj RR (conj TL NIN))].
    eapply mc_binop_w; [exact CS_| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB| exact PAD| exact NLE].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L26983617546.9800000@S2ra2sp1d1H1a2Ha". (* [comment removed for export] *)
  Lemma copy_sep_of_opnd : forall d1 d lo' SP', opnd_sep d1 d lo' SP' -> 0 <= md_addr d -> copy_sep d1 d lo' SP'.
  Proof. intros d1 d lo' SP' (O1 & O2 & O3 & O4 & O5) H. repeat (split; [assumption|]). intros a Ha. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0@D4791203545.141 L10514515003.17 L15320267806.197L15320268189.168L16075584458.166L2213966053.17  L22595088374.134L29010565666.167L29010566049.194L29727939172.17 L34287669872.19 L41114214986.17 L41114218273.15 L42250439817.175L42252537748.145L42252550707.174L42252550708.204L44622288685.140L45534252581.174L47742573966.15 L49698585326.140L52205273332.17 L53336319057.166L54147418798.177L55808652373.15 L59310684627.175L61996832439.174L62484960502.17 L63784808468.140L65209169712.167L66151410442.168L66279785561.177L7835592368.204 00000100200G00`00a00n01A01B01C01_01`02A02b03K04504_05H05I05Z05g06F06G06a07607Q08008A08L08k09809Q09f0:6FFS2ra2sp2dN2dW2ts1r2HrS2ra2sp2dN2ts3SPB1r2Hr2K0FS1L2sp2lo3SLOS2ra2sp2dN2NN2ts2N1FFS1L2HI2sp1h4HTOP3SPB3hq'3HTcFS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2ra2sp2dN2lo3SLO3ACL2dW2ts3SPB3ACPS1L3HLS2ra2sp2dN2lo3SLO3ACL2ts3SPB3ACP3dW'S1L3HLS2ra2sp2dN2lo3SLO3ACL2ts3SPB3ACP3dW'S1L3HLS2ra2sp2dN2lo3SLO3ACL2dW2ts3SPB3ACPFS2ra2sp2dN2ts3dW'S1L2sp2lo3SLOS2ra2sp2dX2dW2ts2HB5Ha_st5Hl_stFS2ra2sp2dN2ts2N13SPB3dW31HS2ra2sp2dN2ts3SPB3dW'S1L2HI2sp1h4HTOP2hq3SPB3HTcS2ra2sp2dN2ts3SPB3dW'1r3HrF3Hr0S2ra2sp2dN2ts3dW'S2sp2dN3HNNS2ra2sp2dX2dW2ts2HB5Ha_st5Hl_stS2ra2sp2dW2tsS2ra2sp2dN2ts3SPB1r2Hr2K0S2ra2sp2dN2ts3SPB3dW'S2ra2sp2dN2dW2ts". (* [comment removed for export] *)
  Lemma L_mid : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pxra,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(5:.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(2.$?.(10.R16.)$16.)P,(1=.+1.(19.VdN,))P,(1=.(19.VdN,)(19.R18.))P,(1=.+1.(19.VdE,))P,(2.$0.R18.(65.(19.VdN,)(19.VdE,)))(2:.$45.R1?.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R17.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R15.R14.R13.(25.&40.R19.)(25.&40.R1:.)R12.R11.R10.R?.R>.R=.R<.R;.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R16.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.+20<>0.)Vfc,(2?.(3.&40.))R20.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros TS OR N1 NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(TS) 4%nat. intros CS_ RR TL NIN. reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((w_cells _ _ _ _ _ _ _ _ _ CS_)) 5%nat. intros CW SGW HLW HNW EAW. unfold mpi_cells in CW. unfold MPI_MAX_LIMBS in HNW.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (munch_refl [(md_addr dX, md_addr dX + 16)] mq) as MU. pose proof (wmono_refl psegs mq) as WM.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : rw_cells psegs m1 (md_addr dX) _ |- _ => rename H into CW1 end.
    assert (TS1 : tstate m1 moq hq LBq (set_sg dW 1) dR T tl ts).
    { split; [| exact (conj RR (conj TL NIN))].
      eapply mc_sign_w; [exact CS_| rewrite EAW; exact MU| exact WM| assumption| rewrite EAW; unfold mpi_cells; exact CW1| left; reflexivity]. }
    clear CS_ MU WM CW1. flat constr:(TS1) 2%nat. intros CS1 _. reopen CS1 HH HTc MF SOK MI ST MK.
    (* [comment removed for export] *)
    zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS1)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS1 opndN)) 6%nat. intros MN CRN_ CRNL_ LN HFN ASN.
    pose proof HCMP as SC. unfold mpi_cmp_mpi_stmt, P_MPI_CMP_MPI in SC.
    eapply aevtM_cut_evt; [exact MK| eapply SC with (dX := set_sg dW 1) (dY := dN) (LB := LBq);
      [exact MW| exact MN| intros O; exact (proj1 (HFW O))| intros O; exact (proj1 (HFN O))| exact MI| cbn [set_sg md_addr] in EA |- *; rewrite ?EA; reflexivity| reflexivity] |].
    clear SC. cbv beta. intros ms' PO. unfold mpi_cmp_post in PO.
    flat constr:(PO) 18%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _.
    replace (ret_pc (Z_to_bv 64 0x20cf4)) with (Z_to_bv 64 0x20cf4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (Z.sgn_spec (mpd_val (set_sg dW 1) - mpd_val dN)) as SG.
    (* [comment removed for export] *)
    assert (GROW : forall mq' moq' hq' LBq' dW' (yra y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
      tstate mq' moq' hq' LBq' dW' dR T tl ts ->
      aevtM psegs moq' POST
        (MS (mkR yra SPF gp tp y0 y1 y2 (Z_to_bv 64 tl) (Z_to_bv 64 T) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 (md_addr dA)) x5 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 0) s9 s10 s11 y3 y4 y5 y6)
            F (Z_to_bv 64 0x20d0c) fc None mq' (seg_rom psegs))).
    { clear - HCALLOC HLS SW DIMG HND ROIMG IMGC HGROW HH0 MX0 MA0 ME0 MN0 NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRAL CRE CREL CRN CRNL WRX XLO ST0 SLO ACL HTOP SPA DHI TP MI0 RA2 SOK0 CA
               HCBL HCBLZ HWL HLSET HR2 HZF HCOPY HCMP HMOD HMMI HTOM HCEM HFROM HCZ HAS SPB ACP OR N1 NLR E1 TLE.
      intros until y6. intros TS'. flat constr:(TS') 4%nat. intros CS' RR' TL' NIN'. reopen CS' HH HTc MF SOK MI ST MK.
      flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS' opndN)) 5%nat. intros CN_ _ HLN HNN _. unfold mpi_cells in CN_.
      zstep. rewrite zx16_small by lia. zstep. zstep.
      flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS')) 10%nat. intros MW' NSW' EA' WRW' LW' CRW' CRWL' HFW' ASW' WA8'.
      pose proof HGROW as SGR. unfold mpi_grow_stmt, P_MPI_GROW in SGR.
      eapply aevtM_cut.
      { eapply SGR with (dX := dW') (nb := md_n dN) (lo := lo) (h := hq') (LB := LBq'); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
        all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc HNN; lia).
        all: try (rewrite ?EA'; reflexivity). }
      clear SGR. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
      binop_post PO m3 mo3 h3 LB3 dW3 r E MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR3.
      replace (ret_pc (Z_to_bv 64 0x20d18)) with (Z_to_bv 64 0x20d18) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      flat constr:(RR3) 2%nat. flclear RR3. intros R1 FRB3.
      assert (PN3 : md_pad dW3 = md_pad dW' /\ md_n dW' <= md_n dW3 /\ (r = 0 -> md_n dN <= md_n dW3) /\ (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED)).
      { destruct R1 as [(Hr0 & _ & N3 & P3 & _)|[HrF ->]]; [| split; [reflexivity|]; split; [lia|]; split; [intros Hr0; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in HrF; lia| right; exact HrF]].
        split; [exact P3|]. split; [rewrite N3; lia|]. split; [intros _; rewrite N3; lia| left; exact Hr0]. }
      flat constr:(PN3) 4%nat. flclear PN3. intros PAD3 NLE3 NN3 Hr.
      assert (TS3 : tstate m3 mo3 h3 LB3 dW3 dR T tl ts).
      { eapply t_binop_w; [exact TS'| exact HH3| exact HT3| exact MF3| exact MA3| exact OUT3| exact PX3| exact SOK3| exact MI3| exact ST3| exact FRB3| exact PAD3| exact NLE3]. }
      pose proof (proj1 (proj2 OUT3)) as NS3.
      clear CS' MW' NSW' EA' WRW' LW' CRW' CRWL' HFW' ASW' WA8' R1 FRB3 OUT3 PX3. flat constr:(TS3) 2%nat. intros CS3 _. reopen CS3 HH HTc MF SOK MI ST MK.
      zstep; if_cases K0; zify_cond K0.
      { eapply L_clean1'; [exact CS3| exact RR'| exact TL'| exact NIN'| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia]. }
      assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
      eapply L_core; [exact TS3| eapply out_heap; [exact MA3| exact NS3| pose proof (NN3 eq_refl); lia]| exact OR| exact N1| exact (NN3 eq_refl)| exact NLR| exact E1| exact TLE]. }
    zstep; if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) eapply GROW. exact TS1. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    flat constr:((mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dN CS1 opndN)) 2%nat. intros SWN OWN.
    flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS1)) 2%nat. intros SWW OWW.
    pose proof HMOD as SM. unfold mpi_mod_mpi_stmt, mpi_binop_stmt_nb, P_MPI_MOD_MPI in SM.
    eapply aevtM_cut.
    { eapply SM with (dX := set_sg dW 1) (dA := set_sg dW 1) (dB := dN) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?EA; reflexivity).
      all: try (cbn [set_sg md_addr]; rewrite ?EA, ?EAW; first [reflexivity| exact NXN]). }
    clear SM. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
    replace (ret_pc (Z_to_bv 64 0x20d08)) with (Z_to_bv 64 0x20d08) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR2) 2%nat. flclear RR2. intros (_ & Hr) FLt20. flat constr:(FLt20) 4%nat. flclear FLt20. intros EA2 PAD2 FRB2 NLE2.
    assert (TS2 : tstate m2 mo2 h2 LB2 dW2 dR T tl ts).
    { eapply t_binop_w; [exact TS1| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB2| exact PAD2| exact NLE2]. }
    clear CS1 MW NSW EA WRW LW CRW CRWL HFW ASW WA8 MA2 OUT2 PX2. flat constr:(TS2) 2%nat. intros CS2 _. reopen CS2 HH HTc MF SOK MI ST MK.
    zstep; if_cases K1; zify_cond K1.
    { eapply L_clean1'; [exact CS2| exact RR| exact TL| exact NIN| lia]. }
    eapply GROW. exact TS2.
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L10373523120.181L15320268189.171L29010565666.169L31823645074.152L3752735275.17  L41114218273.15 L42250733213.152L42252550708.181L50278634639.185L55808652373.15 L58242326278.146L61303316110.15 L64286596220.17 L66151410442.17100000=00Y00Z00o01001Q02<02g03G03b04404A04B04^S2ra2sp2dW2tsS2ra2sp2dW2ts3SPB2dY1r2Hr2K0FS2ra2sp2dA2dW2ts4APOSFS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2ra2sp2lo3SLO3ACL2dW2ts3SPB3ACP4WPOSS1L3HLS2ra2sp2lo3SLO3ACL2dW2ts3SPB3ACP4WPOSS2ra2sp2dW2ts2dY3dW22N23SPB4WPOSS1L2HI2sp1h4HTOP2hq3SPB3HTcS2ra2sp2dW2ts4WPOSS1L2sp2lo3SLOFS2ra2sp2dW2ts3SPB2dY1r2Hr2K0". (* [comment removed for export] *)
  Lemma L_copy : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PdR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pxra,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(5:.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(2.$?.(10.R16.)$16.)P,(1=.+1.(19.VdN,))P,(1=.(19.VdN,)(19.R18.))P,(1=.+1.(19.VdE,))P,(2.$0.R18.(65.(19.VdN,)(19.VdE,)))(2:.$45.R1?.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R17.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R15.R14.R13.(25.&40.R19.)(25.&40.R1:.)R12.R11.R10.R?.R>.R=.R<.R;.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R16.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.+20<8<.)Vfc,(2?.(3.&40.))R20.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros TS OR N1 NLR E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(TS) 4%nat. intros CS_ RR TL NIN. reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS_)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros SWW OWW.
    flat constr:(MW) 2%nat. intros FLt21 _. flat constr:(FLt21) 4%nat. flclear FLt21. intros _ _ WPOS _.
    pose proof HCOPY as SC. unfold mpi_copy_stmt, P_MPI_COPY in SC.
    (* [comment removed for export] *)
    assert (HY : exists dY, mpd_at psegs mq LBq dY /\ mpd_sep dW dY /\ copy_sep dW dY lo SPc /\ client_range L LBq lo (md_addr dY) 16
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
    replace (ret_pc (Z_to_bv 64 0x20c98)) with (Z_to_bv 64 0x20c98) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR2) 4%nat. flclear RR2. intros R1 EA2 PAD2 FRB2.
    assert (PN2 : md_n dW <= md_n dW2 /\ (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED)).
    { destruct R1 as [(Hr0 & _ & N2)|(HrF & N2 & _)]; [split; [lia| left; exact Hr0]| split; [lia| right; exact HrF]]. }
    flat constr:(PN2) 2%nat. flclear PN2. intros NLE2 Hr.
    assert (TS2 : tstate m2 mo2 h2 LB2 dW2 dR T tl ts).
    { eapply t_binop_w; [exact TS| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB2| exact PAD2| exact NLE2]. }
    clear CS_ MW NSW EA WRW LW CRW CRWL HFW ASW WA8 MA2 OUT2 PX2 MY CSY CRY CRYL. flat constr:(TS2) 2%nat. intros CS2 _. reopen CS2 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0.
    { assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. eapply L_mid; [exact TS2| exact OR| exact N1| exact NLR| exact E1| exact TLE]. }
    eapply L_clean1'; [exact CS2| exact RR| exact TL| exact NIN| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L15320268189.174L24928565580.177L27519199047.17 L29010565666.173L35977663465.16 L41114218273.15 L42250437140.145L42252550708.174L43588391822.15 L55808652373.15 L55865303600.174L66151410442.174L9978351147.10  00000F01E01F01G01H01i02T03?03L03g04505305KS2ra2sp3dRR2ts2dR1r2HrS1L3HLS2ra2sp2dN2lo3SLO3ACL3dRR2ts3EAR2N13SPB3ACP2dR3EA23NLR2H0FFFS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2ra2sp2lo3SLO3ACL3dRR2ts3EAR3SPB3ACPS1L3HLS2ra2sp2lo3SLO3ACL3dRR2ts3EAR3SPB3ACPS1L2sp2lo3SLOS1L2HI2sp1h4HTOP2hq3SPB3HTcS2ra2sp3dRR2tsS1L3HLS2ra2sp2lo3SLO3ACL3dRR2ts3EAR3SPB3ACP3AR82dR1r2Hr3EA22K0S1L3HLS2sp2dN2lo3SLO3ASN". (* [comment removed for export] *)
  Lemma L_r2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdRR,$:.PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pxra,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R19.R18.R17.R16.(4:.$:.R15.(43.$:.))VdX,(4:.(34.$0.$0.)(35.$0.$0.R14.(18.+4.R13.))(43.(34.$0.$0.)))(4:.(34.$0.(8.$3?.))(35.$0.(8.$3?.)(1>.(13.&40.Vsp,)-50.)(4:.$3?.(4;.Vs8,)(4:.$3?.(4;.Vs7,)(4:.$3?.(4;.Vs6,)(4:.$3?.(4;.Vs5,)(4:.$3?.(4;.Vs4,)(4:.$3?.(4;.Vs3,)(4:.$3?.(4;.Vs2,)(4:.$3?.(4;.Vs1,)(4:.$3?.(4;.Vs0,)(4:.$3?.(4;.Vra,)(43.$3?.))))))))))))(43.(34.$0.(8.$3?.))))(4:.(34.$0.(8.$3?.))(35.$0.(8.$3?.)R14.(4:.$3?.(56.(57.#4.(4>.(3.&40.)R12.))(58.R12.))(43.$3?.)))(43.(34.$0.(8.$3?.)))))P,(2.$0.(15.R16.)(1>.(13.&40.Vsp,)-60.))P,(2.$0.(42.(4>.(3.&40.)R14.))R15.)P,(1=.+1.(19.VdN,))P,(1=.+1.(19.VdE,))P,(2.$0.R18.(65.(19.VdN,)(19.VdE,)))(2:.$45.R1>.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R17.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R15.R14.R13.(25.&40.R19.)(25.&40.R1:.)R12.R11.R10.R?.R>.R=.R<.R;.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R16.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.+20<30.)Vfc,(2?.(3.&40.))R1?.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ EAR TL N1 E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    zstep. zstep. zstep.
    flat constr:((mc_local_facts _ _ _ _ _ _ _ _ _ 0 dRR CS_ eq_refl)) 10%nat. intros MR NSR WRR LR CRR CRRL HFR AR1 AR2 AR8.
    flat constr:((mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 6%nat. intros MN CRN_ CRNL_ LN HFN ASN.
    flat constr:((mc_opnd_sep_le _ _ _ _ _ _ _ _ _ 0 dRR dN CS_ eq_refl opndN)) 2%nat. intros SRN ORN.
    pose proof HR2 as SR. unfold mpi_get_mont_r2_stmt, P_MPI_GET_MONT_R2 in SR.
    eapply aevtM_cut.
    { eapply SR with (dX := dRR) (dN := dN) (lo := lo) (h := hq) (LB := LBq); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?EAR; first [reflexivity| apply f_equal; lia]).
      rewrite EAR. clear - ASN AR1 AR2 SLO HLS. lia. }
    clear SR. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dR r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR2.
    replace (ret_pc (Z_to_bv 64 0x20c3c)) with (Z_to_bv 64 0x20c3c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR2) 4%nat. flclear RR2. intros (RN & Hr) EA2 PAD2 FRB2.
    assert (CS2 : CST m2 mo2 h2 LB2 [dR] dX [(T, 4 * tl)] [(SP + -80, REGS)] [(T, [CB (4 * length ts)%nat (u32s ts)])]).
    { pose proof (mc_binop_l _ _ _ _ _ _ _ _ _ 0 dRR m2 mo2 h2 LB2 dR CS_ eq_refl HH2 HT2 MF2 MA2 OUT2 PX2 SOK2 MI2 ST2 FRB2) as C2. cbn [set_nth] in C2. exact C2. }
    (* [comment removed for export] *)
    flat constr:((mc_drop_local _ _ _ _ _ _ _ _ _ _ CS2)) 11%nat. intros CS3 NINF SGR HLR HNR A1 A2 A8 NSR' RN0 RH.
    cbn [app] in CS3. unfold mpd_struct in CS3. rewrite EA2, EAR in CS3.
    assert (RRK : rr_ok dR).
    { split; [rewrite EA2; exact EAR|]. split; [exact HLR|]. split; [exact HNR|]. split; [exact NSR'|]. split; [exact SGR|]. split; [exact RN0|].
      intros O. flat constr:((RH O)) 6%nat. intros _ X1 X2 X3 X4 _. auto. }
    assert (NIN : ~ In (T, 4 * tl) (mpd_blk dR)) by (exact (Forall_inv NINF)).
    assert (TS3 : tstate m2 mo2 h2 LB2 dX dR T tl ts) by (split; [exact CS3| exact (conj RRK (conj TL NIN))]).
    clear CS_ MR NSR WRR LR CRR CRRL HFR MN CRN_ CRNL_ LN HFN ASN SRN ORN MA2 OUT2 PX2 CS2 CS3. reopen TS3 HH HTc MF SOK MI ST MK || (pose proof TS3 as (CS3 & _); reopen CS3 HH HTc MF SOK MI ST MK).
    zstep; if_cases K0; zify_cond K0.
    - (* [comment removed for export] *) assert (r = 0) by lia. subst r. pose proof (RN eq_refl) as NLR.
      assert (OR : md_own dR = LHeap) by (destruct (md_own dR) eqn:O; [destruct (RN0 eq_refl); lia| reflexivity| exfalso; exact (NSR' eq_refl)]).
      eapply L_copy; [exact TS3| exact OR| exact N1| exact NLR| exact E1| exact TLE].
    - eapply L_r2fail; [exact (proj1 TS3)| exact RRK| exact TL| exact NIN| lia].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@D25171652884.134D25171652884.135D39517585209.134D55780705378.135L21363818053.134L29762660275.132L35161367924.133L44622288685.134L44622288685.135L49698585326.134L49698585326.135L52253708504.133L62042415875.132L63866730927.135L64331383062.134L6940456849.134 L8532465607.2   L9503834392.135 00000h01`02R03D03\03n04@05:06406Y07>07P07b08C08d09<09D09\S1L2HI2ra2sp1h4HTOP2hq2ts3j163SPB3HTc3L162HB5Ha_st5Hl_stS1L2HI2ra2sp1h4HTOP2hq2ts3j163SPB3HTc3L162HB5Ha_st5Hl_stS1L3HLS2ra2sp2lo3SLO2ts3j163SPB3L162HB5Ha_st5Hl_stS1L3HLS2ra2sp2lo3SLO2ts3j163SPB3L162HB5Ha_st5Hl_stS2ra2sp2ts3j163L162j42L4S2ra2sp2ts3j163L16S2ra2sp2ts3j163L16S1L3HLS2ra2sp2lo3SLO3ACL3DHI2ts3j163SPB3L162HB5Ha_st5Hl_stS1L3HLS2ra2sp2lo3SLO3ACL3DHI2ts3j163SPB3L162HB5Ha_st5Hl_stS2ra2sp2ts3j163SPB3L162HB5Ha_st5Hl_stS2ra2sp2ts3j163SPB3L162HB5Ha_st5Hl_stS2ra2sp2ts3j163L16S2ra2sp2ts3j163L16S2ra2sp2ts3j163L162HB5Ha_st5Hl_stS2ra2sp2ts3j163L162HB5Ha_st5Hl_stS2ra2sp2ts3j163L162j42L4S2sp3SPAS2ra2sp2ts3j163L162j42L4". (* [comment removed for export] *)
  Lemma L_init : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PT,$0.Ptl,$0.Pts,(8.(3.&40.))Pj16,(8.(3.&8.))Pxra,(3.&40.)Px1,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R19.R18.R17.R16.(43.$:.)VdX,(4:.(34.$0.$0.)(35.$0.$0.R15.(18.+4.R14.))(43.(34.$0.$0.)))(44.(4:.$3?.(56.#10.R12.)(43.$3?.)))(4:.(34.$0.(8.$3?.))(35.$0.(8.$3?.)R15.(4:.$3?.(56.(57.#4.(4>.(3.&40.)R13.))(58.R13.))(43.$3?.)))(43.(34.$0.(8.$3?.)))))P,(2.$0.(42.(4>.(3.&40.)R14.))R15.)P,(32.=R17.)P,(1=.+1.(19.VdN,))P,(1=.+1.(19.VdE,))P,(2.$0.R19.(65.(19.VdN,)(19.VdE,)))(2:.$45.R1>.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R17.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R14.R13.R12.(25.&40.R1:.)R16.(25.&40.R1;.)R11.R10.R?.R>.R=.R<.R;.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R15.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.+20;:<.)Vfc,(2?.(3.&40.))R1?.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ TL T0 N1 E1 TLE.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros CH0 CHR. reopen CS_ HH HTc MF SOK MI ST MK.
    assert (L16 : length j16 = 16%nat) by (pose proof (proj1 (proj1 (proj1 CH0))) as W; cbn in W; tauto).
    zstep. zstep.
    pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp + -80)] mq) as MU. pose proof (wmono_refl psegs mq) as WM.
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : rw_cells psegs m3 (bv_unsigned sp + -96) _ |- _ => rename H into CH3 end.
    match goal with H : rw_cells psegs m3 (bv_unsigned sp + -80) _ |- _ => rename H into CHR3 end.
    set (j4 := skipn 4 (skipn 8 j16)) in CH3.
    assert (L4 : length j4 = 4%nat) by (subst j4; rewrite !skipn_length, L16; reflexivity).
    assert (CH3' : rw_cells psegs m3 (bv_unsigned sp + -96) (mpi_cells 0 (Z_to_bv 64 1) 0 (wof j4))).
    { eapply rw_cells_reshape; [exact CH3| cbn; repeat split; exact I|].
      unfold mpi_cells, wof. cbn [cells_bytes cbytes app]. rewrite le4_le_bytes_to_word by exact L4.
      change (le4 (Z_to_bv 64 1)) with (le2 (Z_to_bv 64 1) ++ le2 (Z_to_bv 64 0)). rewrite <- !app_assoc. reflexivity. }
    clear CH3.
    assert (CS3 : CST m3 moq hq LBq [] dX [(T, 4 * tl)] (frame (mpi_cells 0 (Z_to_bv 64 1) 0 (wof j4))) [(T, [CB (4 * length ts)%nat (u32s ts)])]).
    { eapply (mc_hi_write _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -96) (bv_unsigned sp + -80) []);
        [exact CS_| exact MU| exact WM| assumption| assumption| lia| lia| constructor| reflexivity| intros j d d' Hj; destruct j; discriminate Hj| |].
      - unfold frame. constructor; [exact CH3'| constructor; [exact CHR3| constructor]].
      - apply frame_chs. reflexivity. }
    assert (CS4 : CST m3 moq hq LBq [null_mpd (bv_unsigned sp + -96) (wof j4)] dX [(T, 4 * tl)] [(SP + -80, REGS)] [(T, [CB (4 * length ts)%nat (u32s ts)])]).
    { eapply mc_intro_local; [exact CS3| clear - SPA; lia| constructor; [cbn [fst snd cells_size csize Nat.add length]; lia| constructor]| constructor]. }
    clear CS_ CS3 MU WM CH3' CHR3. try clear CH0. try clear CHR. reopen CS4 HH HTc MF SOK MI ST MK.
    zstep; if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity].
    eapply L_r2; [exact CS4| reflexivity| exact TL| exact N1| exact E1| exact TLE].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L59314873579.12900000CS2ra2sp2dX1a2Ha1R1H". (* [comment removed for export] *)
  Lemma w_writable_SP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PCS,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R6.R5.R4.R3.(43.$:.)R2.(43.$9.)R1.(43.(34.$0.(8.$3?.))))(1:.VL,R4.(13.&40.Vsp,)(1;.$45.VL,VHI,R5.)R3.)")
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
  Lemma ivs_SP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)PdW,$:.PCS,(8.(34.$0.(8.$3?.)))P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R6.R5.R4.R3.(43.$:.)R2.(43.$9.)R1.(43.(34.$0.(8.$3?.))))Pa,$0.P,(31.(1=.=R1.)(32.R1.(3:.+2.+40.)))P,(69.VL,VLB,(13.&40.Vsp,)R2.)P,(6:.(68.VdX,)R3.)(31.(69.VL,R8.(13.&40.Vsp,)R4.)(6:.(68.R7.)R4.))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L10123277521.15 L13596060800.15 L15302269400.133L22446743512.133L242487066.163  L24389775364.131L34705680216.133L3949578456.133 L41843875160.133L51454941784.133L5699067096.133 L57978040519.130L58591023192.133L59506921496.130L60513488151.132L61287041130.161L62132994542.163L64311902065.15 L6700308622.15  L67280348888.133L7632799155.133 L7900592797.131 00000K00W00e01301A01`01n02<02J02X02f03403B03P03o04=04R04V04c05105?05QS1L2HI2sp1h4HTOP2hq3SPB3HTcS2sp3SPA3SPBS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS1L3HLS2ra2sp2lo3SLO3c162SZ3SPBS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZS1L3HLS2ra2sp2lo3SLO3c162SZ3SPBS2ra2sp3c162SZS2ra2sp2dX3c162SZ3SPBS2spS1L2sp2lo3SLOS2ra2sp3c162SZS2ra2sp3c162SZS2ra2sp3c162SZ3SPB". (* [comment removed for export] *)
  Lemma L_e0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pc16,(8.$3?.)Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R18.R17.R16.R15.(43.$:.)VdX,(43.$9.)(44.R14.)(43.(34.$0.(8.$3?.))))P,(2.$40.(41.R15.)#10.)(2:.$45.R19.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R15.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R11.R10.R?.R14.R13.R>.R=.R<.R;.R:.R9.R8.R7.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R12.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(25.&40.+20;?0.)Vfc,(2?.(3.&40.))R1:.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ SZ.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros CH0 CHR.
    pose proof (w_writable_SP _ _ _ _ _ _ CS_) as WRS. pose proof (ivs_SP _ _ _ _ _ _ CS_) as IVP.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ ltac:(constructor))) 11%nat. intros HH HTc MF MW OUT BK PX SOK MI ST _.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. flat constr:(BK) 4%nat. flclear BK. intros EA PAD FRB NLE.
    do 12 zstep.
    release_frame CH0 ST (bv_unsigned sp + -80). release_frame CHR ST (bv_unsigned sp).
    zstep. try (replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    pose proof HLSET as SL. unfold mpi_lset_stmt, P_MPI_LSET in SL.
    eapply aevtM_mono.
    { eapply SL with (lo := lo) (h := hq) (LB := LBq) (dX := dX) (z := 1);
        first [ exact HH | exact MW | exact WRS | exact TP | exact MI | exact SOK | exact CA | exact ACL | exact DHI | exact ST | reflexivity | rewrite EA; reflexivity
              | exact (proj1 (proj2 OUT))
              | clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia
              | match goal with |- ?g => idtac "REMAINE0" g end ]. }
    cbv beta. intros c PO. unfold mpi_binop_post in PO |- *.
    flat constr:(PO) 22%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m5 mo5 h5 LB5 dW5 r5 -> PO.
    flat constr:(PO) 10%nat. flclear PO. intros MI5 ST5 MF5 HT5 HH5 MA5 OUT5 PX5 SOK5 RR5. flat constr:(RR5) 3%nat. flclear RR5. intros R5 EA5 FRB5.
    do 14 eexists. exists m5, mo5, h5, LB5, dW5, r5.
    split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [eapply mo_frame_trans; [exact MF| exact MF5]|]. split; [rewrite HT5; exact HTc|].
    split; [exact HH5|]. split; [exact MA5|].
    split. { eapply mpd_out_trans; [exact OUT| exact OUT5| exact FRB|]. intros b Hb. flat constr:((mpd_blk_heap _ _ Hb)) 2%nat. intros O ->. exact (proj1 (proj1 (proj2 (proj2 (proj2 facts0))) O)). }
    split. { eapply heap_presx_trans; [exact PX|]. intros a Ha Hc Ho. flat constr:((IVP a Ha Hc Ho)) 2%nat. intros C1 O1. exact (PX5 a Ha C1 O1). }
    split; [exact SOK5|].
    split; [destruct R5 as [(Hr0 & _)|[HrF _]]; [subst r5; lia| rewrite HrF; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia]|].
    split; [rewrite EA5; exact EA|]. split; [destruct R5 as [(_ & _ & _ & _ & _ & P5)|[_ ->]]; [rewrite P5; exact PAD| exact PAD]|]. split.
    - intros b Hb. destruct (FRB5 b Hb) as [Hb4|NIN]; [exact (FRB b Hb4)|].
      flat constr:(OUT) 5%nat. intros _ _ _ K2 _. destruct (in_dec blk_eq_dec2 b (mpd_blk dX)) as [Y|N]; [left; exact Y| right]. intros HbL. exact (NIN (K2 b HbL N)).
    - destruct R5 as [(_ & N5 & _)|[_ ->]]; [rewrite N5; lia| exact NLE].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L11765010229.172L20196769970.175L22007303991.144L22597161160.130L246891319.165  L24877094167.170L27575083321.131L28559041928.19 L33215054479.178L33374082811.144L40823643100.19 L41799534830.130L42250421143.164L42252586244.146L42716873236.178L45150910167.19 L45294559390.19 L45355672784.129L51896866947.176L55808587826.19 L59308633593.172L62875675035.131L66398439471.177L8171651384.172 00000L00i01601I01Y01i02<02M02m03D03Q03b04K05405T05j06?06P06m07Q07l08=08R09FS2ra2sp2dE2dN3HNE2K02tl1T2tsS2ra2sp2dE2dN3SPB2tl3TLB1T2T0S2ra2sp2dE2dNS2ra2sp2dE2dN2NN2N1S2ra2sp2dE2dN2tlS2ra2sp2dE2dN2tlS2ra2sp2dE2dN2NN2N1S2sp2dE2dN2tl3TLBS2ra2sp2dE2dN3SPB2tl1T2T02ts3LTSS2ra2sp2dE2dN2NN2N13SPBS2sp2dE2dN2tlS2ra2sp2dE2dN3HNES1L3HLS2ra2sp2dE2dN2lo3SLO3ACL3SPB3ACP2tlS1L3HLS2ra2sp2dE2dN2lo3SLO3ACL3SPB3ACP2tlS2ra2sp2dE2dN3SPB2tl3TLB1T2T02tsS1L2sp2dE2dN2lo3SLO2tlS2sp2dE2dN3SPB2tl3TLBS2ra2sp2dE2dN3HNES2ra2sp2dE2dN3SPB2tl3TLB1T2T0S1L2HI2sp1h2dE2dN4HTOP2hq3SPB3HTc2tlS2ra2sp2dE2dN2tl1T2T02ts2KZS2ra2sp2dE2dN3HNES2ra2sp2dE2dN2tl1T2tsS1L3HLS2ra2sp2dE2dN2lo3SLO3ACL3SPB2tl3TLB1T2T02T42ts". (* [comment removed for export] *)
  Lemma L_alloc : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pj16,(8.(3.&8.))Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px5,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R18.R17.R16.R15.(43.$:.)VdX,(43.$9.)(44.(4:.$3?.(56.#10.R14.)(43.$3?.)))(43.(34.$0.(8.$3?.))))P,(1=.+1.(19.VdN,))(2:.$45.R19.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R15.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R11.R10.R?.R14.R13.R>.R=.R<.R;.R:.R9.R8.R7.(25.&40.(15.VdN,))(25.&40.(15.VdX,))(25.&40.(15.VdA,))R12.(25.&40.=)(25.&40.(15.VdE,))(25.&40.=)Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(25.&40.+20;8<.)Vfc,(2?.(3.&40.))R1:.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ N1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((cs_frame _ _ _ _ _ _ _ _ _ CS_)) 2%nat. intros CH0 CHR. reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 5%nat. intros CE_ _ HLE HNE _. unfold mpi_cells in CE_.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 5%nat. intros CN_ _ HLN HNN _. unfold mpi_cells in CN_.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by lia. zstep; if_cases K0; zify_cond K0.
    { eapply L_e0; [exact CS_| reflexivity]. }
    rewrite ?unsigned_lit in K0 by lia.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by lia. zstep.
    pose proof HWL as SWL. unfold mpi_core_exp_mod_working_limbs_stmt, P_MPI_CORE_EXP_MOD_WORKING_LIMBS in SWL.
    eapply aevtM_cut_evt; [exact MK| eapply SWL with (an := md_n dN) (en := md_n dE); first [exact MI| reflexivity| lia] |].
    clear SWL. cbv beta. intros ms' PO. unfold mpi_core_exp_mod_working_limbs_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _ ->.
    replace (ret_pc (Z_to_bv 64 0x20b9c)) with (Z_to_bv 64 0x20b9c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    set (tl := exp_mod_working_limbs (md_n dN) (md_n dE)).
    assert (TLB : 3 <= tl < 2^20) by (subst tl; unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); lia).
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := tl) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by lia; try eassumption; try reflexivity; try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc TLB; lia) |].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by lia.
    flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HPc h2 HT2 CASES.
    replace (ret_pc (Z_to_bv 64 0x20ba8)) with (Z_to_bv 64 0x20ba8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    destruct CASES as [[-> HH2] | (T & -> & HBT & HH2 & HNEW)].
    - (* [comment removed for export] *)
      assert (CS2 : CST m2 mo2 h2 LBq [] dX [] (frame [CB 16 j16]) []).
      { eapply mc_heap_nop0; [exact CS_| exact HH2| exact HT2| exact MF2| exact HPc| exact MI2| exact ST2]. }
      clear CS_ CH0 CHR CE_ CN_ HPc. reopen CS2 HH HTc MF SOK MI ST MK.
      zstep; if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      zstep. zstep. eapply L_ret; [exact CS2| reflexivity| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia].
    - (* [comment removed for export] *)
      flat constr:(HBT) 5%nat. intros T0 TAL _ T4 _.
      set (ts := repeat (Z_to_bv 64 0) (Z.to_nat tl)).
      assert (LTS : Z.of_nat (length ts) = tl) by (subst ts; rewrite repeat_length; lia).
      replace (tl * 4) with (4 * tl) in HH2, HBT by lia.
      assert (HNEW' : rw_cells psegs m2 T [CB (4 * length ts)%nat (u32s ts)]).
      { subst ts. rewrite u32s_repeat0, repeat_length. replace (4 * Z.to_nat tl)%nat with (Z.to_nat (tl * 4)) by lia. exact HNEW. }
      assert (CS2 : CST m2 mo2 h2 ((T, 4 * tl) :: LBq) [] dX [(T, 4 * tl)] (frame [CB 16 j16]) [(T, [CB (4 * length ts)%nat (u32s ts)])]).
      { eapply mc_ex_alloc; [exact CS_| exact HH2| exact HT2| exact MF2| exact HPc| exact MI2| exact ST2| lia| exact HNEW'|]. cbn [cells_size csize Nat.add]. lia. }
      clear CS_ CH0 CHR CE_ CN_ HPc HNEW HNEW'. reopen CS2 HH HTc MF SOK MI ST MK.
      zstep; if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|].
      eapply L_init; [exact CS2| exact LTS| exact T0| exact N1| lia| reflexivity].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L12114030879.167L12114031006.150L19004371453.148L22597161291.150L27577183415.152L29967216424.152L42285604663.151L46530104509.165L47492451383.149L53519010976.138L5585890387.138 L59308628304.150L59310646096.138L59310761939.136L59323890902.153L62873576469.138L65123312311.165L8929152288.166 L8929152417.148 00000=00J00[00n01A01Z01g02702D02Q02j03=03Q03l04H04Y04f05B05[S2ra2sp2dE2dNS2ra2sp2dE2dNS2ra2sp2dE2dN3HNES2ra2sp2dE2dN2NN2N1S2ra2sp2dE2dN2NN2N1S2ra2sp2dE2dN3SPB3HLN3PN0S2ra2sp2dE2dNS2ra2sp2dE2dN2N1S2ra2sp2dE2dNS2ra2sp2dE2dNS2ra2sp2dE2dN3SPB3HLE3PE0S2ra2sp2dE2dN2N12N0S2ra2sp2dE2dN2E03NE1S2ra2sp2dE2dN2N13HNE2N03EN0S2ra2sp2dE2dN3SPB1b1l3HLE2E0S2ra2sp2dE2dN3HNES2ra2sp2dE2dNS2ra2sp2dE2dN2NN3SPB3PN03BR2S2ra2sp2dE2dN3SPB3HNE3BR1". (* [comment removed for export] *)
  Lemma L_C : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pj16,(8.(3.&8.))Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px2,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R16.R15.R14.R13.(43.$:.)VdX,(43.$9.)(44.(4:.$3?.(56.#10.R12.)(43.$3?.)))(43.(34.$0.(8.$3?.))))P,(1=.+1.(19.VdN,))(2:.$45.R17.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R13.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R:.R9.R8.R12.R11.(25.&40.(17.VdE,))(25.&40.(15.VdA,))(25.&40.(15.VdE,))(25.&40.=)(25.&40.(15.VdN,))(25.&40.=)(25.&40.(19.VdE,))R7.R10.(25.&40.(15.VdX,))R?.R>.R=.R<.R;.Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(25.&40.+20;18.)Vfc,(2?.(3.&40.))R18.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ N1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 8%nat. intros CE_ BE HLE HNE _ PBE HFE HZE. unfold mpi_cells in CE_.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 8%nat. intros CN_ BN HLN HNN _ PBN HFN _. unfold mpi_cells in CN_.
    pose proof (u32ro_bound _ _ _ _ BE) as BEB. pose proof (u32ro_bound _ _ _ _ BN) as BNB.
    do 7 zstep.
    (* [comment removed for export] *)
    assert (STEP : forall (y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 : word),
      aevtM psegs moq POST
      (MS (mkR (Z_to_bv 64 0x20b34) SPF gp tp y0 y1 y2 x0 x1 (Z_to_bv 64 (core_bitlen (md_limbs dE) (md_n dE))) ya1 ya2 ya3 ya4 ya5 ya6 ya7
              (Z_to_bv 64 (md_addr dN)) (Z_to_bv 64 (md_addr dX)) (Z_to_bv 64 (md_addr dA)) x5 (Z_to_bv 64 0) (Z_to_bv 64 (md_addr dE)) (Z_to_bv 64 0) s9 s10 s11 y3 y4 y5 y6)
          F (Z_to_bv 64 0x20b34) fc None mq (seg_rom psegs))).
    { intros. pose proof (core_bitlen_range (md_limbs dE) (md_n dE) ltac:(lia)) as BR1.
      (* [comment removed for export] *)
      zstep. zstep; if_cases K1; zify_cond K1.
      2:{ zstep. zstep. eapply L_ret; [exact CS_| reflexivity| lia]. }
      (* [comment removed for export] *)
      zstep. zstep. rewrite zx16_small by lia.
      destruct PBN as [N0|[PN0 PN4]]; [exfalso; lia|].
      zstep.
      pose proof HCBL as SB. unfold mpi_core_bitlen_stmt, P_MPI_CORE_BITLEN in SB.
      eapply aevtM_cut_evt; [exact MK| eapply SB with (A := md_p dN) (n := md_n dN) (xs := md_limbs dN); first [exact BN| exact MI| exact PN4| exact PN0| reflexivity| lia] |].
      clear SB. cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _ ->.
      replace (ret_pc (Z_to_bv 64 0x20b50)) with (Z_to_bv 64 0x20b50) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (core_bitlen_range (md_limbs dN) (md_n dN) ltac:(lia)) as BR2.
      zstep. zstep. zstep; if_cases K2; zify_cond K2.
      - eapply L_alloc; [exact CS_| exact N1].
      - eapply L_ret; [exact CS_| reflexivity| lia]. }
    destruct (Z.eq_dec (md_n dE) 0) as [E0|EN0].
    - (* [comment removed for export] *)
      assert (P0 : md_p dE = 0).
      { destruct (md_own dE) eqn:O; [exact (proj1 (HZE eq_refl))| |]; exfalso; (flat constr:((HFE ltac:(congruence))) 3%nat; intros _ _ NE1); lia. }
      rewrite E0.
      pose proof HCBLZ as SB. unfold mpi_core_bitlen_z_stmt, P_MPI_CORE_BITLEN in SB.
      eapply aevtM_cut_evt; [exact MK| eapply SB with (A := md_p dE); first [exact MI| reflexivity| rewrite P0; lia] |].
      clear SB. cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _ ->.
      replace (ret_pc (Z_to_bv 64 0x20b34)) with (Z_to_bv 64 0x20b34) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (EC : core_bitlen [] 0 = core_bitlen (md_limbs dE) (md_n dE)).
      { rewrite E0. destruct (md_limbs dE); [reflexivity| cbn in HLE; exfalso; lia]. }
      rewrite EC. eapply STEP.
    - destruct PBE as [N0|[PE0 PE4]]; [exfalso; lia|].
      pose proof HCBL as SB. unfold mpi_core_bitlen_stmt, P_MPI_CORE_BITLEN in SB.
      eapply aevtM_cut_evt; [exact MK| eapply SB with (A := md_p dE) (n := md_n dE) (xs := md_limbs dE); first [exact BE| exact MI| exact PE4| exact PE0| reflexivity| lia] |].
      clear SB. cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? -> _ _ _ ->.
      replace (ret_pc (Z_to_bv 64 0x20b34)) with (Z_to_bv 64 0x20b34) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply STEP.
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L12114030879.132L17688311343.132L2029329742.130 L3808455375.131 L41799535084.131L52067443989.130L59308546259.126L59308582510.109L59314841581.129L7005563203.131 L8463814133.130 L9249901920.131 00000?00N00]00l00m01L01b01o02L02^03=03LS2ra2sp2dE1k2HKS2ra2sp2dE1k2HKS2ra2sp2dE1k2HKS2ra2sp2dE1k2HKFS2ra2sp2dE1k2HK3SPB3HLE3PE03BEBS2ra2sp2dE1k2HK3SPB2N0S2ra2sp2dE2HKS2ra2sp2dE1k2HK3SPB3HLE3PE01NS2ra2sp2dE1k2HK2K1S2ra2sp2dE1k2HK3SPB3HLE3PE03BEBS2ra2sp2dE1k2HK". (* [comment removed for export] *)
  Lemma L_Bloop : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pj16,(8.(3.&8.))Pk,$40.Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px2,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R15.R14.R13.R12.(43.$:.)VdX,(43.$9.)(44.(4:.$3?.(56.#10.R11.)(43.$3?.)))(43.(34.$0.(8.$3?.))))P,(1=.+1.(19.VdN,))P,(31.(1=.+1.(42.R12.))(1=.(42.R12.)(19.VdE,)))(2:.$45.R17.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R12.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,(25.&40.(42.R13.))R9.R8.R11.R10.(25.&40.(17.VdE,))(25.&40.(15.VdA,))(25.&40.(15.VdE,))(25.&40.=)(25.&40.(15.VdN,))(25.&40.=)(25.&40.(19.VdE,))(25.&40.(20.(1>.(17.VdE,)(18.+4.(42.R13.)))+4.))R?.(25.&40.(15.VdX,))R>.R=.R<.R;.R:.Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(25.&40.+20:?4.)Vfc,(2?.(3.&40.))R18.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq j16 k. induction k as [|k IH]; intros until t6; intros CS_ N1 HK; [exfalso; lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 7%nat. intros CE_ BE HLE HNE SGE PBE _. unfold mpi_cells in CE_.
    destruct PBE as [N0|[PE0 PE4]]; [exfalso; lia|]. pose proof (u32ro_bound _ _ _ _ BE) as BEB.
    rd BE (Z.of_nat (S k) - 1).
    zstep; if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep; if_cases K1; zify_cond K1.
      { eapply L_C; [exact CS_| exact N1]. }
      zstep. rewrite (sx16_sign _ SGE). zstep; if_cases K2; zify_cond K2.
      + zstep. zstep. eapply L_ret; [exact CS_| reflexivity| lia].
      + eapply L_C; [exact CS_| exact N1].
    - zstep. zstep. zstep; if_cases K1; zify_cond K1.
      + replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia. replace (md_p dE + 4 * Z.of_nat (S k) - 4 + -4) with (md_p dE + 4 * Z.of_nat k - 4) by lia.
        eapply IH; [exact CS_| exact N1| rewrite ?unsigned_lit in K1 by lia; lia].
      + zstep. eapply L_C; [exact CS_| exact N1].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L36459744067.127L3692537938.129 L41415942734.129L41799534830.127L45355769948.128L63566623781.129L66869926316.12900000:00L00V00d01201D01]S2ra2sp2dES2ra2sp2dE3SPB3HLES2ra2sp2dES2ra2sp2dE3HNES2ra2sp2dE3HNES2ra2sp2dE3SPB3HLES2ra2sp2dE3SPB3HNE3PBE2K0". (* [comment removed for export] *)
  Lemma L_B : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pj16,(8.(3.&8.))Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px2,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R18.R17.R16.R15.(43.$:.)VdX,(43.$9.)(44.(4:.$3?.(56.#10.R14.)(43.$3?.)))(43.(34.$0.(8.$3?.))))P,(1=.+1.(19.VdN,))(2:.$45.R19.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R15.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R<.R;.R:.R14.R13.R9.(25.&40.(15.VdA,))(25.&40.(15.VdE,))(25.&40.=)(25.&40.(15.VdN,))(25.&40.=)R8.R7.R12.(25.&40.(15.VdX,))R11.R10.R?.R>.R=.Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(25.&40.+20:=8.)Vfc,(2?.(3.&40.))R1:.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ N1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dE CS_ opndE)) 7%nat. intros CE_ BE HLE HNE SGE PBE _. unfold mpi_cells in CE_.
    pose proof (u32ro_bound _ _ _ _ BE) as BEB.
    zstep. rewrite zx16_small by lia. zstep. zstep; if_cases K0; zify_cond K0.
    { eapply L_C; [exact CS_| exact N1]. }
    rewrite ?unsigned_lit in K0 by lia.
    zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep. zstep.
    replace (md_n dE * 4 + md_p dE + -4) with (md_p dE + 4 * Z.of_nat (Z.to_nat (md_n dE)) - 4) by lia.
    replace (Z_to_bv 64 (md_n dE)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (md_n dE)))) at 1 by (f_equal; lia).
    eapply L_Bloop; [exact CS_| exact N1| lia].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L12114020655.132L12114020905.135L12114031006.131L15043131708.135L2029329742.130 L22726186232.135L3808455375.131 L52067443989.130L52514145542.134L59308546259.125L59308582510.108L59314841581.129L59314841581.134L60931089674.131L62482813690.131L63389698527.137L8394643956.132 L8463814133.130 L9249901920.131 00000C00V00l01?01R01m02@02c03603L03Y04:04[05105205E05X06;06NS2ra2sp2dN1k2HK3ULNS2ra2sp2dN1k2HK3ULNS2ra2sp2dN1k2HK3ULN2K1S2ra2sp2dN1k2HK3ULNS2ra2sp2dN1k2HK3ULNS2ra2sp2dN1k2HK3SPB3PN03ULNS2ra2sp2dN1k2HK3ULNS2ra2sp2dN1k2HK3SPB3HLN3PN03BNB3ULNS2ra2sp2dN1k2HK3ULNS2ra2sp2dN1k2HK3SPB2N0S2ra2sp2dN2HKS2ra2sp2dN1k2HK3SPB3HLN3PN03ULN1NS2ra2sp2dN1k2HK3SPB3HLN3PN03ULN1NS2ra2sp2dN1k2HK3ULN2K1FS2ra2sp2dN1k2HK3ULNS2ra2sp2dN1k2HK3ULNS2ra2sp2dN1k2HK3SPB3HLN3PN03BNB3ULNS2ra2sp2dN1k2HK3ULN". (* [comment removed for export] *)
  Lemma L_Aloop : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pj16,(8.(3.&8.))Pk,$40.Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px2,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R15.R14.R13.R12.(43.$:.)VdX,(43.$9.)(44.(4:.$3?.(56.#10.R11.)(43.$3?.)))(43.(34.$0.(8.$3?.))))P,(31.(1=.+1.(42.R11.))(1=.(42.R11.)(19.VdN,)))(2:.$45.R16.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R11.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,(25.&40.(20.(1>.(17.VdN,)(18.+4.(42.R12.)))+4.))R8.R7.R10.R?.(25.&40.-4.)(25.&40.(15.VdA,))(25.&40.(15.VdE,))(25.&40.=)(25.&40.(15.VdN,))(25.&40.=)(25.&40.(17.VdN,))(25.&40.(42.R12.))R>.(25.&40.(15.VdX,))R=.R<.R;.R:.R9.Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(25.&40.+20::8.)Vfc,(2?.(3.&40.))R17.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq j16 k. induction k as [|k IH]; intros until t6; intros CS_ HK; [exfalso; lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 7%nat. intros CN_ BN HLN HNN SGN PBN _. unfold mpi_cells in CN_.
    destruct PBN as [N0|[PN0 PN4]]; [exfalso; lia|]. pose proof (u32ro_bound _ _ _ _ BN) as BNB. pose proof (u32s_length (md_limbs dN)) as ULN.
    rd BN (Z.of_nat (S k) - 1).
    zstep; if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep; if_cases K1; zify_cond K1.
      { eapply L_ret; [exact CS_| reflexivity| lia]. }
      zstep. rewrite (sx16_sign _ SGN). zstep; if_cases KB; zify_cond KB.
      { eapply L_ret; [exact CS_| reflexivity| lia]. }
      rd8 BN 0. zstep. zstep; if_cases KD; zify_cond KD.
      { eapply L_ret; [exact CS_| reflexivity| lia]. }
      eapply L_B; [exact CS_| lia].
    - zstep. zstep. zstep; if_cases K1; zify_cond K1.
      + replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia. replace (md_p dN + 4 * Z.of_nat (S k) - 4 + -4) with (md_p dN + 4 * Z.of_nat k - 4) by lia.
        eapply IH; [exact CS_| rewrite ?unsigned_lit in K1 by lia; lia].
      + zstep. eapply L_ret; [exact CS_| reflexivity| lia].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L11729960613.128L12114030621.128L21705506634.128L22595186682.127L3692537938.128 L41415942734.128L47492451383.127L62482820040.12600000I00S00e01601H01R01\01mS2ra2sp2dN3SPB3HNN3PBN2K0S2ra2sp2dNS2ra2sp2dN3SPB3HLNS2ra2sp2dN2NN3HNNS2ra2sp2dN3SPB3HLNS2ra2sp2dNS2ra2sp2dNS2ra2sp2dN2NN3HNN". (* [comment removed for export] *)
  Lemma L_A : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pmq,P,(3.&40.)(5.(3.&8.))Pmoq,$6.Phq,(7.$45.VL,VHI,)PLBq,(8.$9.)Pj16,(8.(3.&8.))Pxra,(3.&40.)Px0,(3.&40.)Px1,(3.&40.)Px2,(3.&40.)Px3,(3.&40.)Px4,(3.&40.)Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Px8,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(46.$45.VL,VHI,Vh,VLB,Vmo,Vm,(13.&40.Vsp,)Vlo,(1>.(13.&40.Vsp,)-60.)VdX,$3>.R18.R17.R16.R15.(43.$:.)VdX,(43.$9.)(44.(4:.$3?.(56.#10.R14.)(43.$3?.)))(43.(34.$0.(8.$3?.))))(2:.$45.R18.(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.R14.(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R:.R9.R8.R13.R12.(25.&40.(15.VdX,))(25.&40.(15.VdA,))(25.&40.(15.VdE,))(25.&40.=)(25.&40.(15.VdN,))(25.&40.=)R7.R6.R11.R10.R?.R>.R=.R<.R;.Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(25.&40.+20:88.)Vfc,(2?.(3.&40.))R19.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    reopen CS_ HH HTc MF SOK MI ST MK.
    flat constr:((e_raw _ _ _ _ _ _ _ _ _ dN CS_ opndN)) 7%nat. intros CN_ BN HLN HNN SGN PBN _. unfold mpi_cells in CN_.
    pose proof (u32ro_bound _ _ _ _ BN) as BNB.
    zstep. zstep. rewrite zx16_small by lia. zstep. zstep; if_cases K0; zify_cond K0.
    { eapply L_ret; [exact CS_| reflexivity| lia]. }
    rewrite ?unsigned_lit in K0 by lia.
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
    replace (md_n dN * 4 + md_p dN + -4) with (md_p dN + 4 * Z.of_nat (Z.to_nat (md_n dN)) - 4) by lia.
    replace (Z_to_bv 64 (md_n dN)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (md_n dN)))) by (f_equal; lia).
    eapply L_Aloop; [exact CS_| lia].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma L_entry : ltac2:(CDefT.buildp (gd_tbl_P_mpi_exp_mod ()) "Pm1,P,(3.&40.)(5.(3.&8.))Pj16,(8.(3.&8.))Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(61.(4:.(34.$0.$0.)(35.$0.$0.Vlo,(13.&40.Vsp,))(43.(34.$0.$0.)))Vm,R;.)P,(62.$45.Vm,R<.)P,(27.$45.R=.)P,(1?.$45.R>.Vlo,(1>.(13.&40.Vsp,)-60.))P,(48.$45.R?.(1>.(13.&40.Vsp,)-60.)(4:.$3?.(56.#10.R>.)(43.$3?.)))P,(48.$45.R10.(1>.(13.&40.Vsp,)-50.)(4:.$3?.(4;.Vs8,)(4:.$3?.(4;.Vs7,)(4:.$3?.(4;.Vs6,)(4:.$3?.(4;.Vs5,)(4:.$3?.(4;.Vs4,)(4:.$3?.(4;.Vs3,)(4:.$3?.(4;.Vs2,)(4:.$3?.(4;.Vs1,)(4:.$3?.(4;.Vs0,)(4:.$3?.(4;.Vra,)(43.$3?.))))))))))))(2:.$45.Vmo,(2;.$45.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(4=.VLB,VdX,VdA,VdE,VdN,)Vlo,Vm,Vmo,)(2=.(2>.Vra,(25.&40.(1>.(13.&40.Vsp,)-60.))Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.(15.VdX,))(25.&40.(15.VdA,))(25.&40.(15.VdE,))(25.&40.=)(25.&40.(15.VdN,))(25.&40.=)R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.+20:88.)Vfc,(2?.(3.&40.))R11.(30.$45.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MI1 ST1 FR0 FR1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    eapply L_A with (j16 := j16).
    eapply mc_init; [exact HH0| exact SOK0| exact MI0| exact MX0| | exact MU| exact WM| exact MI1| exact ST1| constructor| intros i j di dj Hi; destruct i; discriminate Hi| |].
    - unfold es. destruct ALIAS; [constructor; [exact ME0| constructor; [exact MN0| constructor]]| constructor; [exact MA0| constructor; [exact ME0| constructor; [exact MN0| constructor]]]].
    - unfold frame. constructor; [exact FR0| constructor; [exact FR1| constructor]].
    - apply frame_chs. pose proof (proj1 (proj1 (proj1 FR0))) as W. cbn in W. cbn. tauto.
  Qed.
  End Walk.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L11075936116.108L17097338356.108L19685138523.108L19687428440.108L23124392564.108L25465666776.108L28125529944.108L29025845208.108L29135309044.108L31686769240.108L36180999398.105L41172169716.108L42780454045.108L43059266230.103L43679985268.107L5065130740.108 L55720577396.108L60692334296.108L61601561944.108L61747685364.108L62505661912.107L64270350808.108L65178513496.108L67541566890.107L67541566890.108L67758486644.10800000700>00E00L00S00Z00a00h00o01601=01D01K01c01j02102802?02F02M02T02[02b03=03X03_S2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1L3HLS2ra2sp2lo3SLO3SPBS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1L3HLS2ra2sp2lo3SLO3SPB2HBS1L3HLS2ra2sp2lo3SLO3SPB2HBS2ra2sp". (* [comment removed for export] *)
  Theorem P_mpi_exp_mod_spec : mpi_exp_mod_stmt_n psegs L HI P_MPI_EXP_MOD P_MEMSET_FUNC.
  Proof.
    unfold mpi_exp_mod_stmt_n, P_MPI_EXP_MOD. intros until lo.
    intros HH MX MA ME MN NN SXA SXE SXN NXE NXN NSX OPA OPE OPN CRA CRAL CRE CREL CRN CRNL WRX XLO ST SLO ACL HTOP SPA DHI TP MI RA2 SOK CA -> -> -> -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (lock HH) as HHL. pose proof (lock MI) as MIL. pose proof (lock SOK) as SOKL. pose proof (lock ST) as STL. clear HH SOK.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    carve_frame 96%nat ST. set (JJ := junk) in FR. clearbody JJ.
    do 11 zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : rw_cells psegs m1 _ _ |- _ => rename H into FRA end.
    flat constr:((proj1 (rw_cells_app psegs _ _ [CB 16 _] _) FRA)) 2%nat. intros FR0 FR1. clear FRA. cbn [cells_size csize Nat.add] in FR1.
    match type of FR1 with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -80) in FR1 by lia end.
    match type of FR0 with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -96) in FR0 by lia end.
    lazymatch type of FR0 with rw_cells _ _ _ [CB 16 ?j] => set (j16 := j) in FR0; clearbody j16 end.
    eapply L_entry; try eassumption; try exact (unlock _ HHL); try exact (unlock _ MIL); try exact (unlock _ SOKL); try exact (unlock _ STL).
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EM.
