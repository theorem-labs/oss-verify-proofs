(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney MpiClient.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_lset U_mpi_shift_l U_mpi_shrink U_mpi_divmod_stmt U_mpi_exp_mod_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
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
Ltac2 gd_tbl_P_mpi_get_mont_r2 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "mont_r2_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "R2.Walk.es"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.USpec.MpiClient.cstate"; "Corelib.Init.Datatypes.nil"; "R2.Walk.frame"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "R2.Walk.REGS"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.MOK"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.MPI_MAX_LIMBS"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"].


Definition U_MPI_GET_MONT_R2 : Z := 0x24124.
Notation MPI_GET_MONT_R2_STACK := 608 (only parsing).

(* [comment removed for export] *)
Definition mont_r2_R (LB : list blk) (dX dN : mpd) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "(0.(0.P,(1.$2.O2.=)(3.(4.O3.)(4.O1.))(0.(5.(6.(7.+2.+1?.))O2.)(3.O2.=)))(0.(1.$2.(8.O1.)(8.O4.))(0.(1.(9.&40.)(:.O1.)(:.O4.))Pb,$;.P,(<.$;.R1.(=.O1.))(>.(<.$;.R2.(=.O4.))(?.(<.$;.R2.O5.))))))")
(* [comment removed for export] *).

Definition mpi_get_mont_r2_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "Pra,(9.&40.)Psp,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(10.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(11.(9.&8.))Pmo,$12.Ph,(13.O5.O4.O3.)PLB,(14.$;.)PdX,$15.PdN,$15.Plo,$2.P,(16.O5.O4.O3.R5.R4.R7.R6.)P,(17.O5.R8.R5.R4.)P,(17.O5.R9.R6.R4.)P,(18.R6.R5.)P,(?.(1.$2.(8.R7.)(8.R6.)))P,(?.(1.$19.(1:.R8.)$1;.))P,(1<.R9.R8.R7.(1=.&40.R2=.))P,(1>.O4.R;.R8.(8.R9.)+10.)P,P,(1.$19.(1:.R:.)$1?.)(1>.O4.R=.R:.(20.R;.)(21.+4.(4.R;.)))P,(22.O4.R=.(1=.&40.R30.)(23.O5.O4.O3.R>.)R<.)P,P,(?.(1.$19.(1:.R=.)$24.))(>.(3.(25.(20.R>.)(21.+4.(4.R>.)))R<.)(3.(1=.&40.R32.)(20.R>.)))P,(26.O5.R12.R<.(1=.&40.R32.))P,(3.R=.(27.(27.(1=.&40.R33.)+260.)(28.O4.)))P,(3.(29.O4.)R>.)P,(3.(1=.&40.R35.)(23.O5.O4.O3.R13.))P,(1.$2.(2:.(1=.&40.R36.)+10.)=)P,(3.(2;.O4.)(29.O4.))P,(1.(9.&40.)R36.(2<.&40.(2=.O4.)))P,(2>.O5.R19.)P,(2?.O5.O4.R1:.)P,(30.O4.O1.+8.)P,(1.(9.&40.)R34.(2<.&40.(8.R18.)))P,(1.(9.&40.)R34.(2<.&40.(8.R18.)))(31.O5.R1=.(32.O5.O4.O3.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.R1<.R1;.R1:.(33.R1;.R1:.R19.)R18.R1>.R1=.)(34.(35.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R20.(2<.&40.O2.)R1?.(36.(9.&40.))R1>.(37.O5.)))")
(* [comment removed for export] *).

Section R2.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr usegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis HLSET : mpi_lset_stmt usegs L HI U_MPI_LSET U_MEMSET_FUNC.
  Hypothesis HSHL : mpi_shift_l_stmt usegs L HI U_MPI_SHIFT_L U_MEMSET_FUNC.
  Hypothesis HMOD : mpi_mod_mpi_stmt usegs L HI U_MPI_MOD_MPI U_MEMSET_FUNC.
  Hypothesis HSHRINK : mpi_shrink_stmt usegs L HI U_MPI_SHRINK U_MEMSET_FUNC.

  Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dX dN : mpd) (lo : Z).
  Hypothesis HH0 : HEAP usegs L HI h LB m mo.
  Hypothesis MX0 : mpd_at usegs m LB dX.
  Hypothesis MN0 : mpd_at usegs m LB dN.
  Hypothesis SXN : mpd_sep dX dN.
  Hypothesis NEN : md_addr dX <> md_addr dN.
  Hypothesis NSX : md_own dX <> LStatic.
  Hypothesis OPN : opnd_sep dX dN lo (bv_unsigned sp).
  Hypothesis CRN : client_range L LB lo (md_addr dN) 16.
  Hypothesis CRNL : md_own dN = LHeap -> client_range L LB lo (md_p dN) (4 * md_n dN).
  Hypothesis WRX : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dX.
  Hypothesis XLO : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX.
  Hypothesis ST0 : stk usegs m lo (bv_unsigned sp).
  Hypothesis SLO : lo <= bv_unsigned sp - 608 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv usegs m.
  Hypothesis SOK0 : statics_ok usegs L m.
  Hypothesis CA : const_at L U_MEMSET_FUNC 8.

  Notation SP := (bv_unsigned sp).
  Notation SPc := (bv_unsigned sp + -32).
  Notation POST := (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (mont_r2_R LB dX dN) lo m mo).

  (* [comment removed for export] *)
  Definition es : list mpd := [dN].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L43782101083.70L54965713378.2 L65499856427.70L774698616.70  00000;00B00I00fS2sp2dX3SPBS1L3ACPS2sp2dXS1L3HLS2sp2dX2lo3SLO4HPOS3SPB". (* [comment removed for export] *)
  Lemma facts0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "(0.(5.=(8.VdX,))(0.(1.$2.(2:.(8.VdX,)+8.)=)(0.(>.(3.(25.(8.VdX,)+10.)Vlo,)(3.(1=.&40.Vsp,)(8.VdX,)))(0.P,(1.$19.(1:.VdX,)$1?.)(0.(<.(38.$2.$2.)(39.$2.$2.(20.VdX,)(21.+4.(4.VdX,)))VLB,)(3.+1.(4.VdX,)))(0.(3:.(38.$2.$2.)Lb,(38.$2.$2.)(3;.VL,(3<.$2.$2.R1.)(3=.$2.$2.R1.))VLB,)(0.(5.=(29.VL,))(5.(1=.&40.Vsp,)(7.+2.+40.))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(MX0) 2%nat. intros FLt1 SG. flat constr:(FLt1) 6%nat. flclear FLt1. intros HR HAL HPOS HL HN HO.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH0)) 2%nat. intros BR _. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(WRX) 3%nat. flclear WRX. intros WW1 WW2 WW3.
    split; [exact HPOS|]. split; [exact HAL|].
    split; [exact (client_wrange_where L _ _ _ _ 16 lo WW1 ltac:(lia) BR DHI ACL ltac:(lia))|].
    split. { intros O. rewrite O in HO. flat constr:(HO) 3%nat. flclear HO. intros N1 IN _. auto. }
    split; [exact BR|]. split; [clear -ACP; lia|]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma ESF_ok : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "(3:.$15.Le,$15.(0.(1>.VL,VLB,Vlo,(8.R1.)+10.)(0.P,(1.$19.(1:.R1.)$1?.)(<.(38.$2.$2.)(39.$2.$2.(20.R2.)(21.+4.(4.R2.)))VLB,)(0.(>.(3.(25.(8.R1.)+10.)Vlo,)(3.(1=.&40.Vsp,)(8.R1.)))(0.P,(1.$19.(1:.VdX,)$1?.)(>.(3.(25.(8.R2.)+10.)(20.VdX,))(3.(25.(20.VdX,)(21.+4.(4.VdX,)))(8.R2.)))(0.(>.(?.(1.$19.(1:.VdX,)$1?.))(>.(1.$19.(1:.R1.)$24.)(>.(3.(25.(20.VdX,)(21.+4.(4.VdX,)))(20.R1.))(3.(25.(20.R1.)(21.+4.(4.R1.)))(20.VdX,)))))(0.(>.(3.(25.(8.VdX,)+10.)(8.R1.))(3.(25.(8.R1.)+10.)(8.VdX,)))P,(?.(1.$19.(1:.R1.)$24.))(>.(3.(25.(8.VdX,)+10.)(20.R2.))(3.(25.(20.R2.)(21.+4.(4.R2.)))(8.VdX,)))))))))$3>.)")
(* [comment removed for export] *).
  Proof.
    unfold es. constructor; [| constructor].
    flat constr:(OPN) 5%nat. flclear OPN. intros O1 O2 O3 O4 O5. flat constr:(MN0) 2%nat. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ _ HOB.
    split; [exact CRN|]. split; [intros O; rewrite O in HOB; exact (proj1 (proj2 HOB))|]. split; [exact O4|]. split; [exact O2|].
    split. { destruct O3 as [E|X]; [exfalso; apply NEN; rewrite E; reflexivity| exact X]. }
    split. { destruct SXN as [E|X]; [exfalso; apply NEN; rewrite E; reflexivity| exact X]. }
    exact O1.
  Qed.

  (* [comment removed for export] *)
  Notation CST := (cstate usegs L HI h LB mo m SP lo SPc dX es).
  Local Ltac mc_inst H :=
    exact (H usegs L HI HLS DIMG HND IMGC SW ROIMG h LB mo m SP lo SPc dX es
             ACL ltac:(lia) ltac:(lia) HTOP (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 facts0)))))) DHI NSX WRX
             (proj1 (proj2 (proj2 facts0))) (proj1 (proj2 facts0)) (proj1 (proj2 (proj2 (proj2 facts0)))) ESF_ok).
  Definition mc_init := ltac:(mc_inst @cs_init).
  Definition mc_final := ltac:(mc_inst @cs_final).
  Definition mc_binop_w := ltac:(mc_inst @cs_binop_w).
  Definition mc_w_facts := ltac:(mc_inst @cs_w_facts).
  Definition mc_ext_facts := ltac:(mc_inst @cs_ext_facts).
  Definition mc_opnd_sep_we := ltac:(mc_inst @cs_opnd_sep_we).
  Definition mc_opnd_sep_ww := ltac:(mc_inst @cs_opnd_sep_ww).
  Definition mc_ivs_w := ltac:(mc_inst @cs_ivs_w).

  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Local Ltac dest_cs H :=
    (flat constr:(H) 21%nat; flclear H; intros HH HTc MF LOK SA LA MW WOK EXOK SUB COV FRS EXT PX SOK MI ST CH CHS CXH CXS).
  (* [comment removed for export] *)
  Definition REGS (j0 : list byte) : list cell := [CB 8 j0; C8 s1; C8 s0; C8 ra].
  Definition frame (j0 : list byte) : list (Z * list cell) := [(SP + -32, REGS j0)].

  Lemma cs_parts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "Pmq,P,(9.&40.)(11.(9.&8.))Pmoq,$12.Phq,(13.$3?.VL,VHI,)PLBq,(14.$;.)PdW,$15.Pj0,(14.(9.&8.))P,(40.$3?.VL,VHI,Vh,VLB,Vmo,Vm,(1=.&40.Vsp,)Vlo,(25.(1=.&40.Vsp,)-20.)VdX,$3>.R6.R5.R4.R3.(41.$15.)R2.(41.$;.)(42.R1.)(41.(38.$2.(14.$43.))))(0.(16.$3?.VL,VHI,R5.R4.R7.R6.)(0.(1.$2.(23.$3?.VL,VHI,R5.)(23.$3?.VL,VHI,Vh,))(0.(44.Vmo,R6.)(0.(2?.$3?.VL,R7.)(0.(2>.$3?.R7.)(0.(26.$3?.R7.Vlo,(25.(1=.&40.Vsp,)-20.))(0.(45.$3?.R7.(25.(1=.&40.Vsp,)-20.)(46.R2.))(47.R6.))))))))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq dW j0 CS_. dest_cs CS_. split; [exact HH|]. split; [exact HTc|]. split; [exact MF|]. split; [exact SOK|]. split; [exact MI|]. split; [exact ST|].
    split; [| exact (heap_mok _ _ HI _ _ _ _ HH)]. pose proof (Forall_inv CH) as CHR. cbn [fst snd] in CHR. exact CHR.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24928467276.6500000<S2sp1d2N12N0". (* [comment removed for export] *)
  Lemma out_heap : forall mq LBq d, mpd_at usegs mq LBq d -> md_own d <> LStatic -> 1 <= md_n d -> md_own d = LHeap.
  Proof.
    intros mq LBq d [(_ & _ & _ & _ & _ & HO) _] NS N1. destruct (md_own d) eqn:O; [| reflexivity| exfalso; exact (NS eq_refl)].
    flat constr:(HO) 2%nat. flclear HO. intros _ N0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma n_cells : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "Pmq,P,(9.&40.)(11.(9.&8.))Pmoq,$12.Phq,(13.$3?.VL,VHI,)PLBq,(14.$;.)PdW,$15.PCS,(14.(38.$2.(14.$43.)))P,(40.$3?.VL,VHI,Vh,VLB,Vmo,Vm,(1=.&40.Vsp,)Vlo,(25.(1=.&40.Vsp,)-20.)VdX,$3>.R6.R5.R4.R3.(41.$15.)R2.(41.$;.)R1.(41.(38.$2.(14.$43.))))(0.(45.$3?.R7.(8.VdN,)(48.(20.VdN,)(2<.&40.(49.VdN,))(4.VdN,)(:.VdN,)))(0.(3.=(4.VdN,))(3.(4.VdN,)$4:.)))")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq dW CS CS_. destruct (mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS_ ltac:(left; reflexivity)) as ([(HR & _ & _ & _ & HN & _) _] & _). split; [exact HR| exact HN].
  Qed.

  (* [comment removed for export] *)
  Local Ltac binop_post PO m2 mo2 h2 LB2 d2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR :=
    (flat constr:(PO) 31%nat; flclear PO; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m2 mo2 h2 LB2 d2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR);
    injection E as -> ->; rewrite ?unsigned_lit in ST2 by lia; rewrite ?unsigned_lit in PX2 by lia.

  Local Ltac reopen CS hh htc mf sok mi st chr mk :=
    try clear hh; try clear htc; try clear mf; try clear sok; try clear mi; try clear st; try clear chr; try clear mk;
    (flat constr:((cs_parts _ _ _ _ _ _ CS)) 8%nat; intros hh htc mf sok mi st chr mk).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L21887662552.100L33510041944.100L39941600002.99 L41564619544.98 L66083662040.10000000400800M00Q00US2spS2spS1L3HLS2sp2lo3SLO3SPBS2spS2sp". (* [comment removed for export] *)
  Lemma L_err : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "Pmq,P,(9.&40.)(11.(9.&8.))Pmoq,$12.Phq,(13.$3?.VL,VHI,)PLBq,(14.$;.)PdW,$15.Pj0,(14.(9.&8.))Pr,$2.Pxra,(9.&40.)Px0,(9.&40.)Px1,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)P,(40.$3?.VL,VHI,Vh,VLB,Vmo,Vm,(1=.&40.Vsp,)Vlo,(25.(1=.&40.Vsp,)-20.)VdX,$3>.R18.R17.R16.R15.(41.$15.)R14.(41.$;.)(42.R13.)(41.(38.$2.(14.$43.))))P,(0.(5.(6.(7.+2.+1?.))R13.)(3.R13.=))P,(?.(1.$2.R14.=))(31.$3?.R1:.(32.$3?.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(33.VLB,VdX,VdN,)Vlo,Vm,Vmo,)(34.(35.R14.(2<.&40.(25.(1=.&40.Vsp,)-20.))Vgp,Vtp,R11.R10.R?.R13.R12.(2<.&40.R15.)R>.R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(2<.&40.+2417<.)Vfc,(36.(9.&40.))R1;.(37.$3?.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS_ Hr NZ.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS_ ltac:(constructor))) 11%nat. intros HH HT MF MW OUT BK PX SOK MI ST CH.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (Forall_inv CH) as CHR. cbn [fst snd] in CHR. clear CH. unfold REGS in CHR.
    zstep. zstep. zstep. zstep.
    release_frame CHR ST (bv_unsigned sp).
    zstep.
    apply aevtM_done. unfold mpi_binop_post. flexi 14%nat. exists mq, moq, hq, LBq, dW, r.
    split; [rewrite ?Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|]. split; [exact HH|]. split; [exact MW|]. split; [exact OUT|].
    split; [exact PX|]. split; [exact SOK|].
    flat constr:(BK) 4%nat. flclear BK. intros EA EP FRB _. split; [split; [intros E0; exfalso; exact (NZ E0)| exact Hr]|]. split; [exact EA|]. split; [exact EP| exact FRB].
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L59314873579.10100000@S2sp2dX1a2Ha1R1H". (* [comment removed for export] *)
  Lemma w_writable_SP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "Pmq,P,(9.&40.)(11.(9.&8.))Pmoq,$12.Phq,(13.$3?.VL,VHI,)PLBq,(14.$;.)PdW,$15.PCS,(14.(38.$2.(14.$43.)))P,(40.$3?.VL,VHI,Vh,VLB,Vmo,Vm,(1=.&40.Vsp,)Vlo,(25.(1=.&40.Vsp,)-20.)VdX,$3>.R6.R5.R4.R3.(41.$15.)R2.(41.$;.)R1.(41.(38.$2.(14.$43.))))(22.VL,R4.(1=.&40.Vsp,)(23.$3?.VL,VHI,R5.)R3.)")
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

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308743383.7700000VS1L3HLS2sp2lo3SLO3ACL1a2Ha1B1k1R2S'2B4". (* [comment removed for export] *)
  Lemma ivs_SP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "Pmq,P,(9.&40.)(11.(9.&8.))Pmoq,$12.Phq,(13.$3?.VL,VHI,)PLBq,(14.$;.)PdW,$15.PCS,(14.(38.$2.(14.$43.)))P,(40.$3?.VL,VHI,Vh,VLB,Vmo,Vm,(1=.&40.Vsp,)Vlo,(25.(1=.&40.Vsp,)-20.)VdX,$3>.R6.R5.R4.R3.(41.$15.)R2.(41.$;.)R1.(41.(38.$2.(14.$43.))))Pa,$2.P,(0.(3.=R1.)(5.R1.(7.+2.+40.)))P,(4;.VL,VLB,(1=.&40.Vsp,)R2.)P,(4<.(4=.VdX,)R3.)(0.(4;.VL,R8.(1=.&40.Vsp,)R4.)(4<.(4=.R7.)R4.))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00j0@L13596060800.17 L15320268189.117L15320268189.147L15320268189.176L1546338210.117 L1546338210.147 L1546338210.176 L17329002384.194L21043164193.130L21887662552.184L22575357070.17 L22594989823.183L22597300214.116L24165412814.126L244712602.216  L2841491088.125 L29010565666.116L29010565666.146L29010565666.176L30552427596.19 L31106871138.199L33510041944.184L33709455575.17 L33945219470.127L33947300368.156L38441534856.14 L38671690799.17 L39941779735.183L41564619544.182L43903056315.15 L45290767137.14 L45290767137.15 L45290767137.17 L47742573966.15 L50249502174.17 L50809229511.182L53340367596.162L57459601756.17 L59310684627.127L61272228842.214L61303316110.17 L62132994539.130L62482945270.116L62484961693.17 L63821474456.17 L63967312560.116L64311902065.14 L66083662040.184L66151410442.117L66151410442.147L66151410442.176L6700308622.14  L7190718996.125 L7190718996.156 L7190718996.194 L7190733961.165 L7190734090.96  L7192832394.127 00000<00L00\00e01201?01L01T01_01c02002;02F02M02Q02X02Y02Z02[02\03>03B03Q03Y03a04104204G04K04f05G05h06I06V07107507N07^08308708D08O08Z08e08f08j08n09209B09R09b09o0:O0;00;Q0<20<R0=3S2sp3SPA3SPBS2sp3SPB1r2Hr2K0S2sp3SPB1r2Hr2K0S2sp1r2HrS2sp3SPB1r2K0S2sp3SPB1r2K0S2sp3SPB1r2K0S2sp3dW3S2sp2dX3SPBS2spS1L2sp2lo3SLOS2sp2dN3HNNS2sp2dN3HNNS2sp2dXS2spS2sp2dXFFFFS2sp3SPB3dW23N123dW34NLE33dW44NLE4S2spS2sp2dN3SPB3HNNS2sp3dW2S2sp3dW2S1L2HI2sp1h4HTOPFS1L3HLS2sp2lo3SLO3SPBS2spS1L2HI2sp1h4HTOP3SPB2h33HTcS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPA3SPB3ACPS1L2sp2lo3SLOS1L2HI2sp1h4HTOP3SPB2h23HTcS2spS2sp3SPB3dW23N123dW34NLE3S1L2HI2sp1h4HTOPS2sp2dX3SPB1r3HrF3Hr0S2spS1L2sp2lo3SLOS2sp2dX3SPBS2sp2dN3HNNS2sp2dN3HNNFS2spS2spS2spS2sp3SPB1r2Hr2K0S2sp3SPB1r2Hr2K0S2sp3SPB1r2Hr2K0S1L2sp2lo3SLOS1L3HLS2sp2dX2lo3SLO3ACL3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPB3ACP3dW2S1L3HLS2sp2lo3SLO3ACL3SPB3ACP3dW3S1L3HLS2sp2lo3SLO3ACL3SPB3ACP3dW3S1L3HLS2sp2dX2lo3SLO3ACL3SPB3ACPS1L3HLS2sp2lo3SLO3ACL3SPB3ACP3dW2". (* [comment removed for export] *)
  Lemma L_body : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "Pm1,P,(9.&40.)(11.(9.&8.))Pj0,(14.(9.&8.))Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)P,(40.$3?.VL,VHI,Vh,VLB,Vmo,Vm,(1=.&40.Vsp,)Vlo,(25.(1=.&40.Vsp,)-20.)VdX,$3>.R?.Vmo,Vh,VLB,(41.$15.)VdX,(41.$;.)(42.R>.)(41.(38.$2.(14.$43.))))(31.$3?.Vmo,(32.$3?.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(33.VLB,VdX,VdN,)Vlo,Vm,Vmo,)(34.(35.Vra,(2<.&40.(25.(1=.&40.Vsp,)-20.))Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(2<.&40.(8.VdX,))(2<.&40.(8.VdN,))R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(2<.&40.+24134.)Vfc,(36.(9.&40.))R10.(37.$3?.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros CS1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(MN0) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros RWN ALN NZN _ HNN _. unfold MPI_MAX_LIMBS in HNN.
    pose proof (rw_cells_bound _ _ _ _ RWN) as BDN. unfold mpi_cells in BDN. cbn [cells_size csize Nat.add] in BDN. clear RWN.
    reopen CS1 HH HTc MF SOK MI ST CHR MK.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS1)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    pose proof HLSET as SL. unfold mpi_lset_stmt, U_MPI_LSET in SL.
    eapply aevtM_cut.
    { eapply SL with (dX := dX) (z := 1) (lo := lo) (h := h) (LB := LB); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia). }
    clear SL. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m2 mo2 h2 LB2 dW2 r E MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PX2 SOK2 RR.
    replace (ret_pc (Z_to_bv 64 0x24144)) with (Z_to_bv 64 0x24144) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 3%nat. flclear RR. intros R1 EA2 FRB2.
    assert (PN2 : md_pad dW2 = md_pad dX /\ md_n dX <= md_n dW2 /\ (r = 0 -> md_own dW2 = LHeap /\ 1 <= md_n dW2) /\ (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED)).
    { destruct R1 as [(Hr0 & N2 & O2 & _ & _ & P2)|[HrF ->]]; [| split; [reflexivity|]; split; [lia|]; split; [intros Hr0; exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in HrF; lia| right; exact HrF]].
      split; [exact P2|]. split; [rewrite N2; lia|]. split; [intros _; split; [exact O2| rewrite N2; lia]| left; exact Hr0]. }
    flat constr:(PN2) 4%nat. flclear PN2. intros PAD2 NLE2 OWN2 Hr.
    assert (CS2 : CST m2 mo2 h2 LB2 [] dW2 [] (frame j0) []).
    { eapply mc_binop_w; [exact CS1| exact HH2| exact HT2| exact MF2| exact MA2| exact OUT2| exact PX2| exact SOK2| exact MI2| exact ST2| exact FRB2| exact PAD2| exact NLE2]. }
    clear MW NSW EA WRW LW CRW CRWL HFW ASW WA8 R1 MA2 OUT2 PX2 CS1 FRB2.
    reopen CS2 HH HTc MF SOK MI ST CHR MK.
    zstep; if_cases K0; zify_cond K0.
    { eapply L_err; [exact CS2| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| lia]. }
    assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0. flat constr:((OWN2 eq_refl)) 2%nat. intros OW2 N12. clear OWN2.
    (* [comment removed for export] *)
    flat constr:((n_cells _ _ _ _ _ _ CS2)) 2%nat. intros CN _. unfold mpi_cells in CN.
    zstep. if_cases KC; zify_cond KC; [exfalso; clear - KC NZN BDN; lia|].
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; rewrite ?land_7_mod in KA; clear - KA ALN BDN; lia|].
    zstep. rewrite zx16_small by lia. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. rewrite ?(unsigned_lit (md_n dN)) by lia.
    zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS2)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    pose proof HSHL as SSL. unfold mpi_shift_l_stmt, U_MPI_SHIFT_L in SSL.
    eapply aevtM_cut.
    { eapply SSL with (dX := dW2) (count := md_n dN * 64) (lo := lo) (h := h2) (LB := LB2); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc HNN; lia).
      all: try (rewrite ?EA; reflexivity).
      all: try (apply f_equal; lia). }
    clear SSL. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m3 mo3 h3 LB3 dW3 r E MI3 ST3 MF3 HT3 HH3 MA3 OUT3 PX3 SOK3 RR.
    replace (ret_pc (Z_to_bv 64 0x24164)) with (Z_to_bv 64 0x24164) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros R1 FLt4. flat constr:(FLt4) 4%nat. flclear FLt4. intros EA3 PAD3 FRB3 NLE3.
    assert (Hr : r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) by (destruct R1 as [(Hr0 & _)|HrF]; [left; exact Hr0| right; exact HrF]).
    assert (CS3 : CST m3 mo3 h3 LB3 [] dW3 [] (frame j0) []).
    { eapply mc_binop_w; [exact CS2| exact HH3| exact HT3| exact MF3| exact MA3| exact OUT3| exact PX3| exact SOK3| exact MI3| exact ST3| exact FRB3| exact PAD3| exact NLE3]. }
    pose proof (out_heap _ _ _ MA3 (proj1 (proj2 OUT3)) ltac:(lia)) as OW3.
    clear MW NSW EA WRW LW CRW CRWL HFW ASW WA8 R1 MA3 OUT3 PX3 CS2 FRB3 CN.
    reopen CS3 HH HTc MF SOK MI ST CHR MK.
    zstep; if_cases K0; zify_cond K0.
    { eapply L_err; [exact CS3| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia| lia]. }
    assert (r = 0) by (unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; lia). subst r. clear Hr K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    flat constr:((mc_w_facts _ _ _ _ _ _ _ _ _ CS3)) 10%nat. intros MW NSW EA WRW LW CRW CRWL HFW ASW WA8.
    destruct (mc_ext_facts _ _ _ _ _ _ _ _ _ dN CS3 ltac:(left; reflexivity)) as (MN & CRE & CREL & LN & HFN & ASN).
    destruct (mc_opnd_sep_we _ _ _ _ _ _ _ _ _ dN CS3 ltac:(left; reflexivity)) as [SWN OWN].
    flat constr:((mc_opnd_sep_ww _ _ _ _ _ _ _ _ _ CS3)) 2%nat. intros SWW OWW.
    pose proof HMOD as SM. unfold mpi_mod_mpi_stmt, mpi_binop_stmt_nb, U_MPI_MOD_MPI in SM.
    eapply aevtM_cut.
    { eapply SM with (dX := dW3) (dA := dW3) (dB := dN) (lo := lo) (h := h3) (LB := LB3); rewrite ?unsigned_lit by lia; try eassumption; try reflexivity.
      all: try (clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc; lia).
      all: try (rewrite ?EA; reflexivity).
      rewrite EA. exact NEN. }
    clear SM. cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    binop_post PO m4 mo4 h4 LB4 dW4 r E MI4 ST4 MF4 HT4 HH4 MA4 OUT4 PX4 SOK4 RR.
    replace (ret_pc (Z_to_bv 64 0x24178)) with (Z_to_bv 64 0x24178) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    flat constr:(RR) 2%nat. flclear RR. intros (_ & Hr) FLt5. flat constr:(FLt5) 4%nat. flclear FLt5. intros EA4 PAD4 FRB4 NLE4.
    assert (CS4 : CST m4 mo4 h4 LB4 [] dW4 [] (frame j0) []).
    { eapply mc_binop_w; [exact CS3| exact HH4| exact HT4| exact MF4| exact MA4| exact OUT4| exact PX4| exact SOK4| exact MI4| exact ST4| exact FRB4| exact PAD4| exact NLE4]. }
    pose proof (out_heap _ _ _ MA4 (proj1 (proj2 OUT4)) ltac:(lia)) as OW4.
    clear MW NSW EA WRW LW CRW CRWL HFW ASW WA8 MN CRE CREL LN HFN ASN SWN OWN SWW OWW MA4 OUT4 PX4 CS3 FRB4.
    reopen CS4 HH HTc MF SOK MI ST CHR MK.
    zstep; if_cases K0; zify_cond K0.
    2: { eapply L_err; [exact CS4| lia| lia]. }
    assert (r = 0) by lia. subst r. clear K0 Hr.
    (* [comment removed for export] *)
    flat constr:((n_cells _ _ _ _ _ _ CS4)) 2%nat. intros CN _. unfold mpi_cells in CN.
    pose proof (w_writable_SP _ _ _ _ _ _ CS4) as WRS. rewrite HTc in WRS.
    pose proof (ivs_SP _ _ _ _ _ _ CS4) as IVP.
    flat constr:((mc_final _ _ _ _ _ _ _ _ CS4 ltac:(constructor))) 11%nat. intros _ _ _ MW OUT BK PX _ _ _ _.
    flat constr:(BK) 4%nat. flclear BK. intros EA PAD FRB NLE.
    unfold REGS in CHR.
    zstep. rewrite zx16_small by lia. zstep. zstep. zstep. zstep.
    release_frame CHR ST (bv_unsigned sp).
    zstep.
    try (replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    pose proof HSHRINK as SS. unfold mpi_shrink_stmt, U_MPI_SHRINK in SS.
    eapply aevtM_mono.
    { eapply SS with (lo := lo) (h := h4) (LB := LB4) (dX := dW4) (nb := md_n dN); rewrite ?HTc by lia;
        first [ exact HH | exact MW | exact WRS | exact TP | exact MI | exact SOK | exact CA | exact ACL | exact DHI | exact ST | reflexivity | rewrite EA; reflexivity
              | intros C; rewrite C in OW4; discriminate OW4
              | clear - SLO HLS ACL ACP SPB SPA DHI HTOP HTc HNN; lia ]. }
    cbv beta. intros c PO. unfold mpi_binop_post in PO |- *.
    flat constr:(PO) 22%nat. flclear PO. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? m5 mo5 h5 LB5 dW5 r5 -> PO.
    flat constr:(PO) 10%nat. flclear PO. intros MI5 ST5 MF5 HT5 HH5 MA5 OUT5 PX5 SOK5 RR5. flat constr:(RR5) 2%nat. flclear RR5. intros R5 FRB5.
    flexi 14%nat. exists m5, mo5, h5, LB5, dW5, r5.
    split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [eapply mo_frame_trans; [exact MF| exact MF5]|]. split; [rewrite HT5; exact HTc|].
    split; [exact HH5|]. split; [exact MA5|].
    split. { eapply mpd_out_trans; [exact OUT| exact OUT5| exact FRB|]. intros b Hb. flat constr:((mpd_blk_heap _ _ Hb)) 2%nat. intros O ->. exact (proj1 (proj1 (proj2 (proj2 (proj2 facts0))) O)). }
    split. { eapply heap_presx_trans; [exact PX|]. intros a Ha Hc Ho. flat constr:((IVP a Ha Hc Ho)) 2%nat. intros C1 O1. exact (PX5 a Ha C1 O1). }
    split; [exact SOK5|].
    flat constr:(OUT5) 3%nat. intros EA5 NS5 _.
    split; [| split; [rewrite EA5; exact EA| split]].
    - split; [| destruct R5 as [(Hr0 & _)|[HrF _]]; [subst r5; lia| rewrite HrF; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; lia]].
      intros Hr0. destruct R5 as [(_ & _ & _ & _ & NB5 & _)|[HrF _]]; [exact NB5| exfalso; rewrite HrF in Hr0; discriminate Hr0].
    - destruct R5 as [(_ & _ & P5 & _)|[_ ->]]; [rewrite P5; exact PAD| exact PAD].
    - intros b Hb. destruct (FRB5 b Hb) as [Hb4|NIN].
      + exact (FRB b Hb4).
      + flat constr:(OUT) 5%nat. intros _ _ _ K2 _. destruct (in_dec blk_eq_dec2 b (mpd_blk dX)) as [Y|N]; [left; exact Y| right]. intros HbL. exact (NIN (K2 b HbL N)).
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L1427283182.79 L15283373200.79000004008S2spS2sp". (* [comment removed for export] *)
  Lemma L_entry : ltac2:(CDefT.buildp (gd_tbl_P_mpi_get_mont_r2 ()) "Pm1,P,(9.&40.)(11.(9.&8.))Pj0,(14.(9.&8.))Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)P,(4>.(4?.(38.$2.$2.)(39.$2.$2.Vlo,(1=.&40.Vsp,))(41.(38.$2.$2.)))Vm,R?.)P,(50.$3?.Vm,R10.)P,(2>.$3?.R11.)P,(26.$3?.R12.Vlo,(25.(1=.&40.Vsp,)-20.))P,(45.$3?.R13.(25.(1=.&40.Vsp,)-20.)(46.R12.))(31.$3?.Vmo,(32.$3?.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VdX,(33.VLB,VdX,VdN,)Vlo,Vm,Vmo,)(34.(35.Vra,(2<.&40.(25.(1=.&40.Vsp,)-20.))Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(2<.&40.(8.VdX,))(2<.&40.(8.VdN,))R?.R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(2<.&40.+24134.)Vfc,(36.(9.&40.))R14.(37.$3?.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MI1 ST1 FR1.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    apply L_body with (j0 := j0).
    eapply mc_init; [exact HH0| exact SOK0| exact MI0| exact MX0| unfold es; constructor; [exact MN0| constructor]| exact MU| exact WM| exact MI1| exact ST1
                    | constructor| intros i j di dj Hi; destruct i; discriminate Hi| unfold frame; constructor; [exact FR1| constructor]|].
    unfold frame. constructor; [| constructor]. cbn [fst snd cells_size csize Nat.add REGS]. split; [lia|]. split; [lia|]. intros d [].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Walk.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L21765854580.83L21887662552.82L27775132660.83L33510041944.83L34290115814.80L40872514717.83L43059266230.78L66083662040.83L67541566890.82L67541566890.83L9716869748.82 00000400800<00@00D00H00]00a01901Q01US2spS2spS2spS2spS2spS2spS1L3HLS2sp2lo3SLO3SPBS2spS1L3HLS2sp2lo3SLO3SPB2HBS1L3HLS2sp2lo3SLO3SPB2HBS2sp". (* [comment removed for export] *)
  Theorem U_mpi_get_mont_r2_spec : mpi_get_mont_r2_stmt usegs L HI U_MPI_GET_MONT_R2 U_MEMSET_FUNC.
  Proof.
    unfold mpi_get_mont_r2_stmt, U_MPI_GET_MONT_R2. intros until lo.
    intros HH MX MN SXN NEN NSX OPN CRN CRNL WRX XLO ST SLO ACL HTOP SPA DHI TP MI SOK CA -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (lock HH) as HHL. pose proof (lock MI) as MIL. pose proof (lock SOK) as SOKL. pose proof (lock ST) as STL. clear HH SOK.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST. set (JJ := junk) in FR. clearbody JJ.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with H : rw_cells usegs m1 _ _ |- _ => rename H into FR1 end.
    lazymatch type of FR1 with rw_cells _ _ _ [CB 8 ?j; _; _; _] => set (j0 := j) in FR1; clearbody j0 end.
    match type of FR1 with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -32) in FR1 by lia end.
    eapply L_entry; try eassumption; try exact (unlock _ HHL); try exact (unlock _ MIL); try exact (unlock _ SOKL); try exact (unlock _ STL).
  all: match goal with |- ?gg => idtac "ZEROLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End R2.
