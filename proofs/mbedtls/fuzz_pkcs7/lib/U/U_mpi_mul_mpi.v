(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux MpiWalkAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney MpiJourney2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_cmp U_mpi_copy U_mpi_core_mul U_mpi_add_abs_W U_mpi_add_abs_C U_mpi_add_abs U_mpi_mul_stmt U_mpi_mul_int_W U_mpi_mul_int U_mpi_mul_mpi_W.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
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
Ltac2 gd_tbl_P_mpi_mul_mpi () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Main.CST"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_stmt.mul_mpi_R"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "Main.temps"; "mm_frame"; "Main.LNK"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.JC"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.XJ"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Main.LNKA"; "Main.genuine"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_copy.copy_R"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.JB"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.BJ"; "Main.ST0"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_copy.mpi_copy_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_copy.U_MPI_COPY"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_stmt.mpi_mul_mpi_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_mul_stmt.U_MPI_MUL_MPI"].


(* [comment removed for export] *)
Lemma rw_cells_CB4_C4 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ppre,(0.$5.)Pbs,(0.(2.&8.))Ppost,(0.$5.)P,(6.R6.R5.R4.(7.$5.R3.(8.$5.(9.#4.R2.)R1.)))(6.R7.R6.R5.(7.$5.R4.(8.$5.(:.(;.R3.))R2.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A pre bs post H. flat constr:(H) 2%nat. intros (Hwf & _) _. apply cells_wf_app in Hwf. flat constr:(Hwf) 2%nat. flclear Hwf. intros H1 (H2 & H3). cbn in H2.
  eapply rw_cells_reshape; [exact H| |].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite le4_le_bytes_to_word by exact H2. reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18797602918.1100000;S1C1j1B1k1H". (* [comment removed for export] *)
Lemma blocks_apart_neq' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "PLB,(0.$<.)Pb1,$<.Pb2,$<.P,(=.R3.)P,(>.$<.R3.R4.)P,(>.$<.R3.R5.)P,(?.(10.$<.R5.R4.))(11.(12.(13.(14.$4.$4.R6.)(15.$4.$4.R6.))(14.$4.$4.R5.))(12.(13.(14.$4.$4.R5.)(15.$4.$4.R5.))(14.$4.$4.R6.)))")
(* [comment removed for export] *).
Proof.
  induction LB as [|[C j] r IH]; cbn; intros b1 b2 HA H1 H2 HNE; [destruct H1|].
  flat constr:(HA) 2%nat. flclear HA. intros HC Hr.
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - exfalso. apply HNE. congruence.
  - subst b1. destruct b2 as [B k]. cbn in *. exact (HC B k H2).
  - subst b2. destruct b1 as [B k]. cbn in *. destruct (HC B k H1); lia.
  - apply IH; assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mm_frame (tbp tbs tbn : Z) (pdB : word) (tap tas tan : Z) (pdA : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) : list cell := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "(7.$5.(16.O12.(17.&40.O11.)O10.O?.)(7.$5.(16.O>.(17.&40.O=.)O<.O;.)(8.$5.(18.O1.)(8.$5.(18.O2.)(8.$5.(18.O3.)(8.$5.(18.O4.)(8.$5.(18.O5.)(8.$5.(18.O6.)(8.$5.(18.O7.)(8.$5.(18.O8.)(8.$5.(18.O9.)(8.$5.(18.O:.)(19.$5.)))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Section Main.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (lo : Z) (MSF : Z)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (dA dB : mpd).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Local Notation SPJ := (Z_to_bv 64 (bv_unsigned sp - 112)).
  Hypothesis MSFE : MSF = U_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 304 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis HH : HEAP usegs L HI h LB m mo.
  Hypothesis MX : mpd_at usegs m LB dX.
  Hypothesis NST : ownX <> LStatic.
  Hypothesis XW : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dX.
  Hypothesis XLS : ownX <> LNull -> pX + 4 * nX <= lo \/ bv_unsigned sp <= pX.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis HCOPY : mpi_copy_stmt usegs L HI U_mpi_copy.U_MPI_COPY MSF.
  Hypothesis MI0 : mem_inv usegs m.
  Hypothesis SOK0 : statics_ok usegs L m.
  Local Notation POST := (mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (mul_mpi_R LB dX dA dB) lo m mo).

(* [comment removed for export] *)
  Definition genuine (d : mpd) : Prop := forall mq LBq SPq, opnd_at usegs mq LBq SPq d -> mpd_at usegs mq LBq d.
  Lemma genuine_of : forall mq LBq d, mpd_at usegs mq LBq d -> genuine d.
  Proof. intros mq LBq d M m' LB' SP' O. exact (opnd_at_mpd_back _ _ _ _ _ _ _ M O). Qed.

Lemma opnd_heap_mpd : forall mq LBq SPq d, opnd_at usegs mq LBq SPq d -> md_own d = LHeap -> mpd_at usegs mq LBq d.
  Proof. intros mq LBq SPq d [M|K] EO; [exact M|]. exfalso. flat constr:(K) 2%nat. flclear K. intros E _. rewrite EO in E. discriminate. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L1349803706.6100000LS1L3HLS2sp2lo4SLO23ACL3SPB1H". (* [comment removed for export] *)
  Lemma SPJU' : bv_unsigned SPJ = bv_unsigned sp - 112.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos. apply unsigned_lit. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition CST (E : list blk) (hq : HST usegs L HI) (LBq : list blk) (mq : mem) (moq : Model) (dXc : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "(1:.(1;.$1<.O3.)(1:.(1=.$1<.O3.Vlo,(1>.(1?.&40.Vsp,)+70.))(1:.(20.Vmo,O2.)(1:.(10.$4.(21.$1<.VL,VHI,O5.)(21.$1<.VL,VHI,Vh,))(1:.(22.$1<.VL,VHI,O5.O4.O3.O2.)(1:.(23.$1<.O3.O4.O1.)(1:.(10.$4.(24.O1.)VX,)(1:.(10.(2.&40.)(25.O1.)VpadX,)(1:.(?.(10.$26.(27.O1.)$28.))(1:.(12.VnX,(29.O1.))(1:.(2:.$1<.VL,O3.)(1:.(2;.$1<.VL,VLB,(1?.&40.Vsp,)(2<.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))Vm,O3.)(1:.Pb,$<.P,(>.$<.R1.O4.)(11.(>.$<.R2.VLB,)(11.(>.$<.R2.(2>.O1.))(>.$<.R2.O6.)))(1:.Pb,$<.P,(>.$<.R1.VLB,)P,(?.(>.$<.R2.(2>.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))))(>.$<.R3.O4.)(1:.Pb,$<.P,(>.$<.R1.(2>.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))P,(>.$<.R2.O4.)(10.(0.$<.)(2>.O1.)(2>.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))(1:.Pb,$<.P,(>.$<.R1.(2>.O1.))(11.(>.$<.R2.(2>.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))(?.(>.$<.R2.VLB,)))(1:.Pb,$<.P,(>.$<.R1.O6.)(1:.(?.(>.$<.R2.VLB,))(1:.(?.(>.$<.R2.(2>.O1.)))(1:.(>.$<.R2.O4.)(2?.=(15.$4.$4.R2.)))))P,(10.$26.(27.O1.)$30.)(11.(12.(13.VX,+10.)(31.O1.))(12.(13.(31.O1.)(32.+4.(29.O1.)))VX,)))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma cst_post : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Phq,(33.$1<.VL,VHI,)PLBq,(0.$<.)Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$34.PdXc,$35.Pr,$4.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(36.(19.$<.)R14.R13.R12.R11.R10.)P,(1=.$1<.R13.Vlo,(1?.&40.Vsp,))P,(11.(10.$4.R11.=)(10.$4.R11.$37.))(38.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(39.VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)Vlo,Vm,Vmo,(3:.(3;.(3<.Vra,Vsp,Vgp,Vtp,R11.R10.R?.Vs0,Vs1,(17.&40.R12.)R>.R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(3=.Vra,)Vfc,(3>.(2.&40.))R15.(3?.$1<.))R14.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros (MI & ST & MF & HT & HHq & MXq & AD & PD & NS & NM & SOK & HPX & O3 & O4 & O5 & FR & OE & XP) ST' HR.
    unfold mpi_binop_post. do 14 eexists. exists mq, moq, hq, LBq, dXc, r.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST'|]. split; [exact MF|]. split; [exact HT|]. split; [exact HHq|]. split; [exact MXq|].
    split. { unfold mpd_out. split; [exact AD|]. split; [exact NS|]. split; [| split; [exact O4| exact O5]].
             intros b Hb. destruct (O3 b Hb) as [C|[C|[]]]; [left; exact C| right; exact C]. }
    split; [exact HPX|]. split; [exact SOK|]. split; [exact HR|]. split; [exact AD|]. split; [exact PD|]. split; [exact FR| exact NM].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L10260583541.7 L3230248958.4  L3814313708.4  L39110260550.7 L39112330481.7 L39112346736.11L41924822481.3 L41924822481.6 L47765431294.4 L50175378201.5 L58657612043.4 L58661809173.5 L59308587026.6 L59314873579.7 L59656785403.9 L60154104878.4 L60739367998.2 L61062907419.4 L65514830347.2 00000100200300G00V01701?01N01Y01d01e02402D02V03103?03G03H03IFFFS1L4DIMG1p1n2EI1a2C1S1p1n1a1q1k1R1DS1L3HLS2sp2lo4SLO23ACL1p1n2EC1a1CS2sp1a1CS1L2HI2sp1h1a1CS1p1n3dXc1HS1p1n1B1j1DFS1L4DIMG1p1n2EIS1X2nX2pX1a1R2HoS1X2nX2pX1a2Ha1R1HS1L2HI3HLS2sp1h2lo4SLO21a1CS1X1p1n6XSfreeS1n4EPOSFS". (* [comment removed for export] *)
  Lemma cst_after_free : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Pp,$4.Pn,$4.PE,(0.(40.$4.$4.))Phq,(33.$1<.VL,VHI,)PLBq,(0.$<.)Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$34.PdXc,$35.Phq',(33.$1<.VL,VHI,)Pmq',P,(2.&40.)(3.(2.&8.))Pmoq',$34.P,(36.(8.(40.$4.$4.)(41.$4.$4.R;.(32.+4.R:.))R9.)R8.R7.R6.R5.R4.)P,Pb,(40.$4.$4.)P,(>.(40.$4.$4.)R1.R;.)(?.(10.$4.(14.$4.$4.R2.)R>.))P,(1;.$1<.R4.)P,(1=.$1<.R5.Vlo,(1>.(1?.&40.Vsp,)+70.))P,(20.R9.R5.)P,(10.$4.(21.$1<.VL,VHI,R8.)(21.$1<.VL,VHI,R=.))P,(22.$1<.VL,VHI,R9.(42.R11.R=.)R8.R7.)P,(2;.$1<.VL,(42.R12.R>.)(1>.(1?.&40.Vsp,)+70.)(8.(40.$4.$4.)(41.$4.$4.R12.(13.R12.(32.+4.R11.)))(19.(40.$4.$4.)))R=.R9.)P,(2:.$1<.VL,R:.)(36.R12.R<.(42.R14.R10.)R;.R:.R=.)")
(* [comment removed for export] *).
  Proof.
    intros until moq'. intros (MI & ST & MF & HT & HHq & MXq & AD & PD & NS & NM & SOK & HPX & O3 & O4 & O5 & FR & OE & XP) EP MI' ST' MF' HT' HH' PX' SOK'.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HHq)) 2%nat. intros HBRq HAPq. pose proof (HND _ _ _ _ HHq) as NDq.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
    destruct (OE (p, 4 * n) ltac:(left; reflexivity)) as (ENL & ENX & EIN & EPOS). cbn in EPOS.
    flat constr:((proj1 (Forall_forall _ _) HBRq _ EIN)) 5%nat. intros E0 _ _ EC EI. cbn in E0, EC, EI.
    flat constr:(XW) 3%nat. intros XCW XDW XPo. cbn [md_addr md_own md_p md_n] in XCW, XDW, XPo.
    flat constr:(MX) 2%nat. intros FLt1 _. flat constr:(FLt1) 6%nat. flclear FLt1. intros CX0 _ X0 _ _ OWX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX0, OWX.
    (* [comment removed for export] *)
    assert (KEEP : forall b, In b LB -> ~ In b (mpd_blk dX) -> In b (lb_remove p LBq) /\ b <> (p, 4 * n)).
    { intros b Hb NXb. pose proof (O4 b Hb NXb) as HbQ.
      assert (NE : b <> (p, 4 * n)) by (intros ->; exact (ENL Hb)).
      split; [| exact NE]. destruct b as [q k]. eapply in_lb_remove_other; [exact NDq| exact EIN| exact HbQ| exact NE]. }
    (* [comment removed for export] *)
    assert (XSfree : p + 4 * n <= X \/ X + 16 <= p).
    { apply (client_range_apart L (lb_remove p LBq) lo X 16 p (4 * n)); try (clear - EPOS; lia); try exact ACL; try exact EC.
      - intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C SLO2 HLS; lia| right; left; exact C| right; right].
        exists (q, k). split; [| exact R]. apply KEEP; [exact Hq|]. unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX; try (intros []; fail).
        intros [E1|[]]. injection E1 as E1a E1b. rewrite <- E1a, <- E1b in R. cbn in R. pose proof (XPo eq_refl). clear - H Ha R. lia.
      - clear - EI DIMG; lia.
      - intros B j HB. pose proof (In_lb_remove _ _ _ HB) as HB'.
        destruct (blocks_apart_neq' _ _ _ HAPq HB' EIN ltac:(intros EE; rewrite EE in HB; exact (lb_remove_notin _ _ _ NDq HB))) as [D|D]; cbn in D; clear - D; lia. }
    (* [comment removed for export] *)
    assert (XLfree : md_own dXc = LHeap -> In (md_p dXc, 4 * md_n dXc) (lb_remove p LBq) /\ (md_p dXc + 4 * md_n dXc <= p \/ p + 4 * n <= md_p dXc)).
    { intros EO. flat constr:(MXq) 2%nat. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ _ OW. rewrite EO in OW. flat constr:(OW) 4%nat. flclear OW. intros N1 XIN _ _.
      assert (NE : (md_p dXc, 4 * md_n dXc) <> (p, 4 * n)) by (intros E1; apply ENX; unfold mpd_blk; rewrite EO; left; exact E1).
      split; [eapply in_lb_remove_other; [exact NDq| exact EIN| exact XIN| exact NE]|].
      destruct (blocks_apart_neq' _ _ _ HAPq XIN EIN NE) as [D|D]; cbn in D; [left| right]; exact D. }
    split; [exact MI'|]. split; [exact ST'|]. split; [eapply mo_frame_trans; [exact MF| exact MF']|]. split; [rewrite HT'; exact HT|]. split; [exact HH'|].
    split.
    { eapply mpd_at_heap_presx; [exact MXq| exact PX'| exact MI| exact MI'| | | | |].
      - rewrite AD. intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C; lia| right; left; exact C| right; right].
        exists (q, k). split; [| exact R]. apply KEEP; [exact Hq|]. unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX; try (intros []; fail).
        intros [E1|[]]. injection E1 as E1a E1b. rewrite <- E1a, <- E1b in R. cbn in R. pose proof (XPo eq_refl). clear - H Ha R. lia.
      - intros EO a Ha. right; right. exists (md_p dXc, 4 * md_n dXc). split; [exact (proj1 (XLfree EO))| cbn; exact Ha].
      - rewrite AD. cbn. split; [clear - XSfree; lia| exact I].
      - intros EO. cbn. split; [| exact I]. pose proof (proj2 (XLfree EO)). clear - H. lia.
      - intros b Hb. unfold mpd_blk in Hb. destruct (md_own dXc) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (XLfree eq_refl)). }
    split; [exact AD|]. split; [exact PD|]. split; [exact NS|]. split; [exact NM|]. split; [exact SOK'|].
    split.
    { intros a Ha Hc Ho. flat constr:((HPX a Ha Hc Ho)) 2%nat. intros E1 W1. 
      assert (K : client_addr L (lb_remove p LBq) (bv_unsigned sp - 112) a /\ outside [(p, p + 4 * n)] a).
      { destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]].
        - split; [left; clear - C; lia|]. cbn. split; [| exact I]. clear - C EC ACL SLO2 HLS. lia.
        - split; [right; left; split; assumption|]. cbn. split; [| exact I]. clear - C1 EI DIMG. lia.
        - assert (NXb : ~ In (q, k) (mpd_blk dX)).
          { unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX eqn:EOX; try (intros []; fail). intros [E2|[]]. injection E2 as E2a E2b. rewrite <- E2a, <- E2b in R.
            unfold mpd_ivs in Ho. cbn in Ho, R. clear - Ho R. lia. }
          flat constr:((KEEP _ Hq NXb)) 2%nat. intros IN NE. split; [right; right; exists (q, k); split; [exact IN| exact R]|].
          cbn. split; [| exact I]. cbn in R.
          destruct (blocks_apart_neq' _ _ _ HAPq (O4 _ Hq NXb) EIN NE) as [D|D]; cbn in D; clear - D R; lia. }
      flat constr:(K) 2%nat. flclear K. intros K1 K2. flat constr:((PX' a Ha K1 K2)) 2%nat. intros E2 W2. split; [rewrite E2; exact E1| intros Wm; exact (W2 (W1 Wm))]. }
    split.
    { intros b Hb. pose proof (In_lb_remove _ _ _ Hb) as HbQ. destruct (O3 b HbQ) as [C|[C|[C|C]]]; [left; exact C| right; left; exact C| | right; right; exact C].
      exfalso. subst b. exact (lb_remove_notin _ _ _ NDq Hb). }
    split; [intros b Hb NXb; exact (proj1 (KEEP b Hb NXb))|].
    split; [intros b Hb Hb'; exact (O5 b Hb (In_lb_remove _ _ _ Hb'))|].
    split; [exact FR|].
    split.
    { intros b Hb. destruct (OE b ltac:(right; exact Hb)) as (N1 & N2 & N3 & N4). split; [exact N1|]. split; [exact N2|]. split; [| exact N4].
      destruct b as [q k]. apply In_lb_remove_keep; [exact N3| exact (EP _ Hb)]. }
    exact XP.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L38948636245.0 L40614023308.7 L52101694457.9 L52101785646.9 L52102064936.11L52108071704.3 L54391891673.10L6409729185.8  L785248895.5   00000100H00g01F01g01o02P02m03?SS1L3HLS2sp2lo1X4SLO22XSS1L3HLS2sp2lo4SLO23ACL3DHI1a2HdS1L3HLS2sp2lo4SLO23ACL3DHI1a2C1S1L3HLS2sp2lo4SLO23ACL1a1q1k1R2R3S2sp1a1CS1L2HI3HLS2sp1h2lo4SLO24HTOP1a2NOS1L3HLS2sp2lo4SLO23ACL3dXc2R3S1L3HLS2sp2lo4SLO2". (* [comment removed for export] *)
  Lemma cst_frame : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "PE,(0.$<.)Phq,(33.$1<.VL,VHI,)PLBq,(0.$<.)Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$34.PdXc,$35.Pmq',P,(2.&40.)(3.(2.&8.))P,(36.R7.R6.R5.R4.R3.R2.)P,(43.(8.(40.$4.$4.)(41.$4.$4.(1>.(1?.&40.Vsp,)+70.)(1?.&40.Vsp,))(19.(40.$4.$4.)))R5.R2.)P,(44.$1<.R6.R3.)P,(1;.$1<.R4.)P,(1=.$1<.R5.Vlo,(1>.(1?.&40.Vsp,)+70.))(36.R<.R;.R:.R6.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    intros until mq'. intros (MI & ST & MF & HT & HHq & MXq & AD & PD & NS & NM & SOK & HPX & O3 & O4 & O5 & FR & OE & XP) MU WM MI' ST'.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HHq)) 2%nat. intros HBRq _.
    flat constr:(XW) 3%nat. intros XCW XDW XPo. cbn [md_addr md_own md_p md_n] in XCW, XDW, XPo. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR0 DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS.
    split; [exact MI'|]. split; [exact ST'|]. split; [exact MF|]. split; [exact HT|].
    split. { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHq| exact MU| exact WM| exact ACL|]. intros a Ha NO. cbn in NO. left. rewrite HT. clear - NO HTOP SLO2 HLS. lia. }
    split. { eapply mpd_at_munch_any; [exact MXq| exact MU| exact WM| rewrite AD; cbn; clear - XS SLO2 HLS; lia|].
             intros ON. cbn. split; [| exact I]. flat constr:(MXq) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros _ _ _ _ _ OW.
             destruct (md_own dXc) eqn:EO; [exfalso; exact (ON eq_refl)| | exfalso; exact (NS eq_refl)]. flat constr:(OW) 3%nat. flclear OW. intros _ XIN _.
             flat constr:((proj1 (Forall_forall _ _) HBRq _ XIN)) 5%nat. intros _ _ _ R3 _. cbn in R3. clear - R3 ACL SLO2 HLS. lia. }
    split; [exact AD|]. split; [exact PD|]. split; [exact NS|]. split; [exact NM|].
    split. { eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Hd NW. cbn. split; [clear - Hd DHI ACL SLO2 HLS; lia| exact I]. }
    split. { eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn. split; [| exact I].
             destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]]; [clear - C; lia| clear - C1 DHI ACL SLO2 HLS; lia|].
             flat constr:((proj1 (Forall_forall _ _) HBR0 _ Hq)) 5%nat. intros _ _ _ R3 _. cbn in R3, R. clear - R R3 ACL SLO2 HLS. lia. }
    split; [exact O3|]. split; [exact O4|]. split; [exact O5|]. split; [exact FR|]. split; [exact OE| exact XP].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_EPI : forall (tbc tac : list cell) (t0 t1 t2 raj x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x22 x23 x24 t3 t4 t5 t6 : word)
      (hq : HST usegs L HI) (LBq : list blk) (mq : mem) (moq : Model) (dXc : mpd) (r : Z),
    CST [] hq LBq mq moq dXc ->
    rw_cells usegs mq (bv_unsigned sp - 112) (tbc ++ tac ++ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    cells_size tbc = 16%nat -> cells_size tac = 16%nat ->
    (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) ->
    aevtM usegs moq POST (MS (mkR raj SPJ gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 r) x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x20d78) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until r. intros C FR SZB SZA HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP. pose proof SPJU' as SPJU.
    flat constr:(C) 18%nat. intros MI ST MF HT HHq MXq AD PD NS NM SOK HPX O3 O4 O5 FRS OE XP.
    pose proof (heap_mok _ _ HI _ _ _ _ HHq) as MK.
    (* [comment removed for export] *)
    assert (FR' : rw_cells usegs mq (bv_unsigned sp - 112) (CB 32 (cells_bytes (tbc ++ tac)) :: [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { replace (tbc ++ tac ++ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        with ((tbc ++ tac) ++ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR by (rewrite <- !app_assoc; reflexivity).
      flat constr:(FR) 2%nat. intros (Hwf & _) _.
      eapply rw_cells_reshape; [exact FR| |].
      - cbn [cells_wf cell_wf]. apply cells_wf_app in Hwf. flat constr:(Hwf) 2%nat. flclear Hwf. intros W1 W2.
        split; [| repeat split; exact I]. rewrite cells_bytes_length by exact W1. rewrite !cells_size_app. cbn [cells_size csize]. rewrite SZB, SZA. reflexivity.
      - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite <- !app_assoc, ?app_nil_r. reflexivity. }
    clear FR. pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    do 12 zstep. rewrite ?SPJU.
    release_frame FR' ST (bv_unsigned sp).
    replace (Z_to_bv 64 (bv_unsigned sp - 112 + 112)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
    zstep. apply aevtM_done. eapply cst_post; [exact C| exact ST| exact HR].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_CLEAN_A : forall (tbc : list cell) (tap tas tan : Z) (ysA : list word) (pdA : word)
      (t0 t1 t2 raj x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x22 x23 x24 t3 t4 t5 t6 : word) hq LBq mq moq dXc (r : Z),
    CST (if tap =? 0 then [] else [(tap, 4 * tan)]) hq LBq mq moq dXc ->
    rw_cells usegs mq (bv_unsigned sp - 112) (tbc ++ mpi_cells tap (Z_to_bv 64 tas) tan pdA ++ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
    (tbc = [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] \/ exists tbp tbs tbn pdB, tbc = mpi_cells tbp (Z_to_bv 64 tbs) tbn pdB) ->
    (tap = 0 \/ mpd_at usegs mq LBq (mkMPD (bv_unsigned sp - 96) tas tan tap ysA pdA LHeap)) ->
    (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) ->
    aevtM usegs moq POST
      (MS (mkR raj SPJ gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 r) x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x20d58) fc None mq (seg_rom usegs)).
  Proof.
    intros until r. intros C FR TBC TA HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU' as SPJU.
    flat constr:(C) 18%nat. intros MI ST MF HT HHq MXq AD PD NS NM SOK HPX O3 O4 O5 FRS OE XP.
    pose proof (heap_mok _ _ HI _ _ _ _ HHq) as MK. flat constr:((heap_blocks _ _ HI _ _ _ _ HHq)) 2%nat. intros HBRq HAPq.
    (* [comment removed for export] *)
    assert (FR' : exists w1 w2 w3, rw_cells usegs mq (bv_unsigned sp - 112)
              ([C8 w1; C4 w2; C4 w3] ++ mpi_cells tap (Z_to_bv 64 tas) tan pdA ++ [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
    { destruct TBC as [-> | (tbp & tbs & tbn & pdB & ->)]; unfold mpi_cells in FR; cbn [app] in FR.
      - pose proof (rw_cells_join_C2C2 usegs mq (bv_unsigned sp - 112) [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) (Z_to_bv 64 0) _ FR) as K. cbn [app] in K. do 3 eexists. exact K.
      - pose proof (rw_cells_join_C2C2 usegs mq (bv_unsigned sp - 112) [C8 (Z_to_bv 64 tbp)] (Z_to_bv 64 tbs) (Z_to_bv 64 tbn) _ FR) as K. cbn [app] in K. do 3 eexists. exact K. }
    clear FR. flat constr:(FR') 4%nat. flclear FR'. intros w1 w2 w3 FR. unfold mpi_cells in FR. cbn [app] in FR.
    clear O3 O4 O5 FRS OE HPX.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp - 96)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with MI1 : mem_inv usegs m1 |- _ => rename MI1 into MI1' end.
    assert (MU' : munch [(bv_unsigned sp - 112, bv_unsigned sp)] mq m1).
    { eapply munch_weaken; [| exact MU]. intros a Ha. cbn in Ha |- *. clear - Ha. lia. }
    match goal with STx : stk usegs m1 _ _ |- _ => pose proof (cst_frame _ _ _ _ _ _ _ C MU' WM MI1' STx) as C1 end.
    destruct TA as [TA0 | MTA].
    - (* [comment removed for export] *)
      rewrite TA0 in *. zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
      eapply (mm_EPI [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 w3] (mpi_cells 0 (Z_to_bv 64 tas) tan pdA)); [exact C1| | reflexivity| reflexivity| exact HR].
      cbn [mpi_cells app]. assumption.
    - (* [comment removed for export] *)
      flat constr:(MTA) 2%nat. intros FLt4 _. flat constr:(FLt4) 6%nat. flclear FLt4. intros CTA _ _ LENA NRA FLt5. flat constr:(FLt5) 4%nat. flclear FLt5. intros NA1 AIN APAL AARR. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CTA, LENA, NRA, NA1, AIN, APAL, AARR.
      unfold MPI_MAX_LIMBS in NRA.
      flat constr:((proj1 (Forall_forall _ _) HBRq _ AIN)) 5%nat. intros A0 _ _ AC AI. cbn in A0, AC, AI.
      zstep. if_cases K; zify_cond K; [exfalso; rewrite ?Z.mod_small in K by (clear - A0 AC ACV; lia); clear - K A0; lia|].
      zstep. rewrite zx16_small by (clear - NRA; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
      assert (AARR1 : u32arr usegs m1 tap ysA).
      { eapply u32arr_transport; [exact AARR| exact MU| exact WM|]. cbn. clear - AC ACL SLO2 HLS LENA NA1. lia. }
      flat constr:(C1) 12%nat. intros _ _ MF1 HT1 HH1 _ _ _ _ _ SOK1 _.
      eapply aevtM_cut.
      { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := tap) (len := 4 * tan) (lo := lo) (junk := u32s ysA);
          rewrite ?SPJU; try eassumption; try reflexivity.
        - right. split; [exact AIN|]. replace (Z.to_nat (4 * tan)) with (4 * length ysA)%nat by (clear - LENA; lia). apply u32arr_cells. exact AARR1.
        - clear - NA1 NRA; lia.
        - clear - SLO2 HLS; lia.
        - rewrite HT1. clear - HTOP; lia.
        - clear - SPA. Z.div_mod_to_equations. lia.
        - rewrite <- MSFE. exact CA.
        - f_equal. clear; lia. }
      cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2 mo2 h2 E PO. injection E as -> ->.
      rewrite ?SPJU in PO.
      flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
      replace (ret_pc (Z_to_bv 64 134520)) with (Z_to_bv 64 134520) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (C2 : CST [] h2 (lb_remove tap LBq) m2 mo2 dXc).
      { replace (tap =? 0) with false in C1 by (symmetry; apply Z.eqb_neq; clear - A0; lia).
        eapply (cst_after_free tap tan []); [exact C1| intros b []| exact MI2| exact ST2| exact MF2| exact HT2| exact HH2| exact PX2| exact SOK2]. }
      match goal with FR1 : rw_cells usegs m1 (bv_unsigned sp - 112) _ |- _ =>
        assert (FR2 := heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 FR1 ltac:(cbn [cells_size csize Nat.add]; apply client_range_stack; clear; lia)
                         ltac:(cbn; clear - AC ACL SLO2 HLS NA1; lia)) end.
      eapply (mm_EPI [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 w3] (mpi_cells tap (Z_to_bv 64 tas) tan pdA)); [exact C2| | reflexivity| reflexivity| exact HR].
      cbn [mpi_cells app]. exact FR2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition temps (tbp tbn tap tan : Z) : list blk :=
    (if tbp =? 0 then [] else [(tbp, 4 * tbn)]) ++ (if tap =? 0 then [] else [(tap, 4 * tan)]).

  Lemma mm_CLEAN_B : forall (tbp tbs tbn : Z) (zsB : list word) (pdB : word) (tap tas tan : Z) (ysA : list word) (pdA : word)
      (t0 t1 t2 raj x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x22 x23 x24 t3 t4 t5 t6 : word)
      (hq : HST usegs L HI) (LBq : list blk) (mq : mem) (moq : Model) (dXc : mpd) (r : Z),
    a0 = Z_to_bv 64 tbp ->
    CST (temps tbp tbn tap tan) hq LBq mq moq dXc ->
    rw_cells usegs mq (bv_unsigned sp - 112) (mm_frame tbp tbs tbn pdB tap tas tan pdA ra s0 s1 s2 s3 s4 s5 s6 s7 s8) ->
    mpd_at usegs mq LBq (mkMPD (bv_unsigned sp - 112) tbs tbn tbp zsB pdB LHeap) ->
    (tap = 0 \/ mpd_at usegs mq LBq (mkMPD (bv_unsigned sp - 96) tas tan tap ysA pdA LHeap)) ->
    (tbp = 0 \/ tap = 0 \/ tbp <> tap) ->
    (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) ->
    aevtM usegs moq POST (MS (mkR raj SPJ gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 r) x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x20d4c) fc None mq (seg_rom usegs)).
  Proof.
    intros until r. intros -> C FR MTB TA DIS HR.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU' as SPJU.
    flat constr:(C) 18%nat. intros MI ST MF HT HHq MXq AD PD NS NM SOK HPX O3 O4 O5 FRS OE XP.
    pose proof (heap_mok _ _ HI _ _ _ _ HHq) as MK. flat constr:((heap_blocks _ _ HI _ _ _ _ HHq)) 2%nat. intros HBRq HAPq. pose proof (HND _ _ _ _ HHq) as NDq.
    unfold mm_frame, mpi_cells in FR. cbn [app] in FR.
    clear O3 O4 O5 FRS HPX.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl usegs mq) as WM.
      flat constr:(MTB) 2%nat. intros FLt6 _. flat constr:(FLt6) 6%nat. flclear FLt6. intros CTB _ _ LENB NRB FLt7. flat constr:(FLt7) 4%nat. flclear FLt7. intros NB1 BIN BPAL BARR. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CTB, LENB, NRB, NB1, BIN, BPAL, BARR.
      unfold MPI_MAX_LIMBS in NRB.
      flat constr:((proj1 (Forall_forall _ _) HBRq _ BIN)) 5%nat. intros B0 _ _ BC BI. cbn in B0, BC, BI.
      unfold temps in C. replace (tbp =? 0) with false in C by (symmetry; apply Z.eqb_neq; clear - B0; lia). cbn [app] in C.
      zstep. rewrite zx16_small by (clear - NRB; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
      eapply aevtM_cut.
      { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := tbp) (len := 4 * tbn) (lo := lo) (junk := u32s zsB);
          rewrite ?SPJU; try eassumption; try reflexivity.
        - right. split; [exact BIN|]. replace (Z.to_nat (4 * tbn)) with (4 * length zsB)%nat by (clear - LENB; lia). apply u32arr_cells. exact BARR.
        - clear - NB1 NRB; lia.
        - clear - SLO2 HLS; lia.
        - rewrite HT. clear - HTOP; lia.
        - clear - SPA. Z.div_mod_to_equations. lia.
        - rewrite <- MSFE. exact CA.
        - f_equal. clear; lia. }
      cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2 mo2 h2 E PO. injection E as -> ->.
      rewrite ?SPJU in PO.
      flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
      replace (ret_pc (Z_to_bv 64 134488)) with (Z_to_bv 64 134488) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (C2 : CST (if tap =? 0 then [] else [(tap, 4 * tan)]) h2 (lb_remove tbp LBq) m2 mo2 dXc).
      { eapply (cst_after_free tbp tbn); [exact C| | exact MI2| exact ST2| exact MF2| exact HT2| exact HH2| exact PX2| exact SOK2].
        intros b Hb. destruct (Z.eqb_spec tap 0) as [T0|T0]; [destruct Hb|]. destruct Hb as [<-|[]]. cbn. destruct DIS as [D|[D|D]]; [clear - D B0; lia| clear - D T0; lia| clear - D; lia]. }
      assert (FR2 := heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 FR ltac:(cbn [cells_size csize Nat.add]; apply client_range_stack; clear; lia)
                       ltac:(cbn; clear - BC ACL SLO2 HLS NB1; lia)).
      eapply (mm_CLEAN_A (mpi_cells tbp (Z_to_bv 64 tbs) tbn pdB)); [exact C2| cbn [mpi_cells app]; exact FR2| right; do 4 eexists; reflexivity| | exact HR].
      destruct TA as [TA0 | MTA]; [left; exact TA0| right].
      flat constr:(MTA) 2%nat. intros FLt8 _. flat constr:(FLt8) 6%nat. flclear FLt8. intros _ _ _ _ _ (NA1 & AIN & _). cbn [md_p md_n] in NA1, AIN.
      flat constr:((proj1 (Forall_forall _ _) HBRq _ AIN)) 5%nat. intros A0 _ _ AC AI. cbn in A0, AC, AI.
      assert (NE : (tap, 4 * tan) <> (tbp, 4 * tbn)) by (intros E; injection E as E1 E2; destruct DIS as [D|[D|D]]; clear - D A0 B0 E1; lia).
      eapply mpd_at_heap_presx; [exact MTA| exact PX2| exact MI| exact MI2| | | | |]; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + apply client_range_stack. clear; lia.
      + intros _ a Ha. right; right. exists (tap, 4 * tan). split; [| cbn; exact Ha]. eapply in_lb_remove_other; [exact NDq| exact BIN| exact AIN| exact NE].
      + cbn. split; [clear - BC ACL SLO2 HLS NB1; lia| exact I].
      + intros _. cbn. split; [| exact I]. destruct (blocks_apart_neq' _ _ _ HAPq AIN BIN NE) as [D|D]; cbn in D; clear - D; lia.
      + intros b [<-|[]]. eapply in_lb_remove_other; [exact NDq| exact BIN| exact AIN| exact NE].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_CLEAN : forall (tbp tbs tbn : Z) (zsB : list word) (pdB : word) (tap tas tan : Z) (ysA : list word) (pdA : word)
      (t0 t1 t2 raj x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x22 x23 x24 t3 t4 t5 t6 : word)
      (hq : HST usegs L HI) (LBq : list blk) (mq : mem) (moq : Model) (dXc : mpd) (r pc : Z),
    CST (temps tbp tbn tap tan) hq LBq mq moq dXc ->
    rw_cells usegs mq (bv_unsigned sp - 112) (mm_frame tbp tbs tbn pdB tap tas tan pdA ra s0 s1 s2 s3 s4 s5 s6 s7 s8) ->
    (tbp = 0 \/ mpd_at usegs mq LBq (mkMPD (bv_unsigned sp - 112) tbs tbn tbp zsB pdB LHeap)) ->
    (tap = 0 \/ mpd_at usegs mq LBq (mkMPD (bv_unsigned sp - 96) tas tan tap ysA pdA LHeap)) ->
    (tbp = 0 \/ tap = 0 \/ tbp <> tap) ->
    (r = 0 \/ r = MBEDTLS_ERR_MPI_ALLOC_FAILED) ->
    (pc = 0x20d44 \/ pc = 0x20d20 \/ pc = 0x20de4) ->
    aevtM usegs moq POST (MS (mkR raj SPJ gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 (Z_to_bv 64 r) x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None mq (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until pc. intros C FR TB TA DIS HR HPC.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU' as SPJU.
    flat constr:(C) 18%nat. intros MI ST MF HT HHq MXq AD PD NS NM SOK HPX O3 O4 O5 FRS OE XP.
    pose proof (heap_mok _ _ HI _ _ _ _ HHq) as MK. flat constr:((heap_blocks _ _ HI _ _ _ _ HHq)) 2%nat. intros HBRq HAPq. pose proof (HND _ _ _ _ HHq) as NDq.
    unfold mm_frame, mpi_cells in FR. cbn [app] in FR.
    clear O3 O4 O5 FRS HPX.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    destruct TB as [TB0 | MTB].
    - (* [comment removed for export] *)
      rewrite TB0 in *. unfold temps in C. cbn [Z.eqb app] in C.
      destruct HPC as [-> | [-> | ->]]; zstep; zstep; if_cases K; zify_cond K.
      2,3,5: exfalso; first [ apply K; reflexivity | vm_compute in K; first [ discriminate K | lia ] ].
      2,3: zstep.
      all: eapply (mm_CLEAN_A (mpi_cells 0 (Z_to_bv 64 tbs) tbn pdB)); [exact C| cbn [mpi_cells app]; exact FR| right; do 4 eexists; reflexivity| exact TA| exact HR].
    - (* [comment removed for export] *)
      flat constr:(MTB) 2%nat. intros FLt6 _. flat constr:(FLt6) 6%nat. flclear FLt6. intros CTB _ _ LENB NRB FLt7. flat constr:(FLt7) 4%nat. flclear FLt7. intros NB1 BIN BPAL BARR. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CTB, LENB, NRB, NB1, BIN, BPAL, BARR.
      unfold MPI_MAX_LIMBS in NRB.
      flat constr:((proj1 (Forall_forall _ _) HBRq _ BIN)) 5%nat. intros B0 _ _ BC BI. cbn in B0, BC, BI.
      destruct HPC as [-> | [-> | ->]]; zstep; zstep; if_cases K; zify_cond K.
      1,4,6: exfalso; rewrite ?Z.mod_small in K by (clear - B0 BC ACV; lia); clear - K B0; lia.
      all: eapply (mm_CLEAN_B tbp tbs tbn zsB pdB tap tas tan ysA pdA); [reflexivity| exact C| exact FR| exact MTB| exact TA| exact DIS| exact HR].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record LNK (h1 : HST usegs L HI) (LB1 : list blk) (m1 : mem) (mo1 : Model) (dAe dBe : mpd)
      (tbp tbs tbn : Z) (zsB : list word) (pdB : word) (tap tas tan : Z) (ysA : list word) (pdA : word) : Prop := {
    l_mi : mem_inv usegs m1;
    l_stk : stk usegs m1 lo (bv_unsigned sp - 112);
    l_heap : HEAP usegs L HI h1 LB1 m1 mo1;
    l_top : heap_top usegs L HI h1 = heap_top usegs L HI h;
    l_mf : mo_frame mo mo1;
    l_sok : statics_ok usegs L m1;
    l_X : mpd_at usegs m1 LB1 dX;
    l_presx : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m1;
    l_sub : forall b, In b LB -> In b LB1;
    l_new : forall b, In b LB1 -> In b LB \/ In b (temps tbp tbn tap tan);
    l_tmp : forall b, In b (temps tbp tbn tap tan) -> ~ In b LB /\ ~ In b (mpd_blk dX) /\ In b LB1 /\ 0 < snd b;
    l_fr : rw_cells usegs m1 (bv_unsigned sp - 112) (mm_frame tbp tbs tbn pdB tap tas tan pdA ra s0 s1 s2 s3 s4 s5 s6 s7 s8);
    l_JA : JB usegs L LB1 m1 dX SPJ lo dAe;
    l_BA : BJ usegs SPJ dAe LB1 m1 dX;
    l_JB : JB usegs L LB1 m1 dX SPJ lo dBe;
    l_BB : BJ usegs SPJ dBe LB1 m1 dX;
    l_TB : tbp = 0 \/ dBe = mkMPD (bv_unsigned sp - 112) tbs tbn tbp zsB pdB LHeap;
    l_TA : tap = 0 \/ dAe = mkMPD (bv_unsigned sp - 96) tas tan tap ysA pdA LHeap;
    l_dis : tbp = 0 \/ tap = 0 \/ tbp <> tap;
    l_AG : genuine dAe;
    l_BG : genuine dBe
  }.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11326729879.5 L13234202622.3 L21591057760.15L38232090713.5 L40132594475.6 L41261378637.7 L45315296503.1200000@00I00J00X00g00h00iS1L2HI2sp1h4HTOPS2sp2pX1CFS1L2sp2lo4SLO2S1L2HI2sp1h1a1CFF". (* [comment removed for export] *)
  Lemma lnk_JC : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.PdAe,$35.PdBe,$35.Ptbp,$4.Ptbs,$4.Ptbn,$4.PzsB,(0.(2.&40.))PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)P,(4:.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(4;.$1<.VL,VHI,R11.R10.R?.R>.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(17.&40.(1>.(1?.&40.Vsp,)+70.))Vlo,=(19.$5.))")
(* [comment removed for export] *).
  Proof.
    intros until pdA. intros K. destruct K. pose proof SPJU' as SPJU. flat constr:(XW) 3%nat. intros XCW XDW XP.
    constructor; rewrite ?SPJU; try assumption; try reflexivity; try (clear - SLO2 HLS; lia).
    - split; [| split; [exact XDW| exact XP]]. cbn [md_addr]. intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; rewrite l_top0; clear - C; lia| right; left; exact C| right; right].
      exists (q, k). split; [apply l_sub0; exact Hq| exact R].
    - cbn [md_own md_p md_n]. intros ON. destruct (XLS ON) as [C|C]; [left; exact C| right; clear - C; lia].
    - rewrite l_top0. clear - HTOP; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L44477913071.8L58202923367.8L59308586248.200000800R00XS2sp3SPBS1L3HLS2sp2lo4SLO23ACL3ACPS1i2Hi". (* [comment removed for export] *)
  Lemma lnk_XJ0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.PdAe,$35.PdBe,$35.Ptbp,$4.Ptbs,$4.Ptbn,$4.PzsB,(0.(2.&40.))PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)P,(4:.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(4<.$1<.VL,VHI,R11.R10.R?.R>.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(17.&40.(1>.(1?.&40.Vsp,)+70.))Vlo,=(19.$5.)(19.$<.)R11.R10.R?.R>.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))")
(* [comment removed for export] *).
  Proof.
    intros until pdA. intros K. destruct K. pose proof SPJU' as SPJU. flat constr:(XW) 3%nat. intros XCW XDW XP.
    constructor; rewrite ?SPJU, ?Z.sub_0_r; cbn [app md_addr md_pad md_own]; try assumption; try reflexivity.
    - pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
      split; [split; [exact I|]|]; unfold bytes_at, wr_at; cbn [cells_bytes cells_size length Z.of_nat].
      + split; [clear - SPB SLO2 HLS ACL ACP; lia|]. split; [clear - SPB SLO2 HLS ACL ACP; lia|]. intros i Hi. exfalso. clear - Hi. lia.
      + split; [clear - SPB SLO2 HLS ACL ACP; lia|]. split; [clear - SPB SLO2 HLS ACL ACP; lia|]. intros i Hi. exfalso. clear - Hi. lia.
    - apply mo_frame_refl.
    - apply mpd_out_refl. exact NST.
    - intros b Hb; left; exact Hb.
    - apply heap_presx_refl.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41924822481.3000008S2sp1a1C". (* [comment removed for export] *)
  Lemma cst_of_xj : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.PdAe,$35.PdBe,$35.Ptbp,$4.Ptbs,$4.Ptbn,$4.PzsB,(0.(2.&40.))PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)Phc,(33.$1<.VL,VHI,)PLBc,(0.$<.)Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$34.PdXc,$35.P,(4:.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(4<.$1<.VL,VHI,R16.R15.R14.R13.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(17.&40.(1>.(1?.&40.Vsp,)+70.))Vlo,=(19.$5.)(19.$<.)R6.R5.R4.R3.R2.)(36.(48.R11.R?.R<.R:.)R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros K J. pose proof K as [MI1 ST1 HH1 HT1 MF1 SOK1 MX1 HPX1 SUB NEW TMP FR1 JA BA JB_ BB TB TA DIS AG BG]. pose proof SPJU' as SPJU.
    pose proof J as [MIc STc FRc HHc HTc MFc SOKc MXc ADc PDc NSc OUTc FRSc HPXc XPc NMc]. cbn [app md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    rewrite ?SPJU, ?Z.sub_0_r in *. flat constr:(OUTc) 5%nat. intros _ _ O3 O4 O5.
    split; [exact MIc|]. split; [exact STc|]. split; [eapply mo_frame_trans; [exact MF1| exact MFc]|]. split; [rewrite HTc; exact HT1|]. split; [exact HHc|].
    split; [exact MXc|]. split; [exact ADc|]. split; [exact PDc|]. split; [exact NSc|]. split; [exact NMc|]. split; [exact SOKc|].
    split.
    { intros a Ha Hc Ho. flat constr:((HPX1 a Ha Hc Ho)) 2%nat. intros E1 W1.
      assert (Hc' : client_addr L LB1 (bv_unsigned sp - 112) a).
      { destruct Hc as [C|[C|([q k] & Hq & R)]]; [left; clear - C; lia| right; left; exact C| right; right; exists (q, k); split; [apply SUB; exact Hq| exact R]]. }
      flat constr:((HPXc a Ha Hc' Ho)) 2%nat. intros E2 W2. split; [rewrite E2; exact E1| intros Wm; exact (W2 (W1 Wm))]. }
    split. { intros b Hb. destruct (O3 b Hb) as [C|C]; [| right; left; exact C]. destruct (NEW b C) as [C'|C']; [left; exact C'| right; right; exact C']. }
    split. { intros b Hb NXb. apply O4; [apply SUB; exact Hb| exact NXb]. }
    split. { intros b Hb Hb'. exact (O5 b Hb Hb'). }
    split. { intros b Hb. destruct (FRSc b Hb) as [C|C]; [left; exact C| right; intros Hin; exact (C (SUB b Hin))]. }
    split. { intros b Hb. flat constr:((TMP b Hb)) 4%nat. intros N1 N2 N3 N4. split; [exact N1|]. split; [| split; [apply O4; [exact N3| exact N2]| exact N4]].
             intros Hx. destruct (FRSc b Hx) as [C|C]; [exact (N2 C)| exact (C N3)]. }
    exact XPc.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma mm_frame_size : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ptbp,$4.Ptbs,$4.Ptbn,$4.PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PpdA,(2.&40.)(10.$4.(4=.(46.(49.R8.R7.R6.R5.R4.R3.R2.R1.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,)))+70.)")
(* [comment removed for export] *).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_B : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.Ptbp,$4.Ptbs,$4.Ptbn,$4.PzsB,(0.(2.&40.))PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)PAa,$4.PsA,$4.PnA,$4.PpA,$4.Pys,(0.(2.&40.))PpadA,(2.&40.)PownA,$26.PBa,$4.PsB,$4.PnB,$4.PpB,$4.Pzs,(0.(2.&40.))PpadB,(2.&40.)PownB,$26.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(4:.R32.R31.R30.R2?.(2=.R24.R23.R22.R21.R20.R1?.R1>.)(2=.R1=.R1<.R1;.R1:.R19.R18.R17.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)(47.$1<.R30.(38.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(39.VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)Vlo,Vm,Vmo,)(3;.(3<.R14.(17.&40.(1>.(1?.&40.Vsp,)+70.))Vgp,Vtp,R17.R16.R15.(17.&40.VX,)(17.&40.R1>.)R13.R12.R11.R10.R?.R>.R=.R<.(17.&40.R25.)R;.R:.R9.R8.R7.R6.Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(17.&40.+20;:<.)Vfc,(3>.(2.&40.))R31.(3?.$1<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros K.
    flat constr:(XW) 3%nat. intros XCW _ _. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR0 DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS0.
    eapply (mm_AENTRY L HI HFREE HCALLOC IMGC sp gp tp s9 s10 s11 F fc m1 mo1 h1 LB1 lo MSF
              (mm_frame tbp tbs tbn pdB tap tas tan pdA ra s0 s1 s2 s3 s4 s5 s6 s7 s8)
              X sX nX pX xs0 padX ownX Aa sA nA pA ys padA ownA Ba sB nB pB zs padB ownB _
              MSFE CA TP SPA SLO2 ACL (mm_frame_size _ _ _ _ _ _ _ _) (lnk_JC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K) XS0 (l_JA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K) (l_JB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K));
      [| exact (lnk_XJ0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K)| exact (l_BA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K)| exact (l_BB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K)| exact (l_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K)| reflexivity| reflexivity].
    (* [comment removed for export] *)
    unfold KCL_stmt. intros until pc. intros J BA BB FRc HR HPC.
    eapply mm_CLEAN; [eapply cst_of_xj; [exact K| exact J]| exact FRc| | | exact (l_dis _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K)| exact HR| exact HPC].
    - destruct (l_TB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K) as [C|E]; [left; exact C| right]. rewrite E in BB. exact (opnd_heap_mpd _ _ _ _ (bj_at _ _ _ _ _ _ BB) eq_refl).
    - destruct (l_TA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K) as [C|E]; [left; exact C| right]. rewrite E in BA. exact (opnd_heap_mpd _ _ _ _ (bj_at _ _ _ _ _ _ BA) eq_refl).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma mm_B' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.Ptbp,$4.Ptbs,$4.Ptbn,$4.PzsB,(0.(2.&40.))PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)PdAe,$35.PdBe,$35.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(4:.R26.R25.R24.R23.R18.R17.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)(47.$1<.R24.(38.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(39.VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)Vlo,Vm,Vmo,)(3;.(3<.R14.(17.&40.(1>.(1?.&40.Vsp,)+70.))Vgp,Vtp,R17.R16.R15.(17.&40.VX,)(17.&40.(24.R18.))R13.R12.R11.R10.R?.R>.R=.R<.(17.&40.(24.R19.))R;.R:.R9.R8.R7.R6.Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(17.&40.+20;:<.)Vfc,(3>.(2.&40.))R25.(3?.$1<.)))")
(* [comment removed for export] *).
  Proof. intros until t6. intros K. destruct dAe, dBe. eapply mm_B. exact K. Qed.

  (* [comment removed for export] *)
  Record LNKA (h1 : HST usegs L HI) (LB1 : list blk) (m1 : mem) (mo1 : Model) (dAe : mpd)
      (pdB : word) (tap tas tan : Z) (ysA : list word) (pdA : word) : Prop := {
    a_mi : mem_inv usegs m1;
    a_stk : stk usegs m1 lo (bv_unsigned sp - 112);
    a_heap : HEAP usegs L HI h1 LB1 m1 mo1;
    a_top : heap_top usegs L HI h1 = heap_top usegs L HI h;
    a_mf : mo_frame mo mo1;
    a_sok : statics_ok usegs L m1;
    a_X : mpd_at usegs m1 LB1 dX;
    a_presx : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m1;
    a_sub : forall b, In b LB -> In b LB1;
    a_new : forall b, In b LB1 -> In b LB \/ In b (temps 0 0 tap tan);
    a_tmp : forall b, In b (temps 0 0 tap tan) -> ~ In b LB /\ ~ In b (mpd_blk dX) /\ In b LB1 /\ 0 < snd b;
    a_fr : rw_cells usegs m1 (bv_unsigned sp - 112) (mm_frame 0 1 0 pdB tap tas tan pdA ra s0 s1 s2 s3 s4 s5 s6 s7 s8);
    a_JA : JB usegs L LB1 m1 dX SPJ lo dAe;
    a_BA : BJ usegs SPJ dAe LB1 m1 dX;
    a_TA : tap = 0 \/ dAe = mkMPD (bv_unsigned sp - 96) tas tan tap ysA pdA LHeap;
    a_B : md_addr dB <> X -> JB usegs L LB1 m1 dX SPJ lo dB /\ BJ usegs SPJ dB LB1 m1 dX;
    a_BX : md_addr dB = X -> dB = dX;
    a_ATB : md_addr dAe + 16 <= bv_unsigned sp - 112 \/ bv_unsigned sp - 96 <= md_addr dAe;
    a_AG : genuine dAe
  }.

  Lemma lnka_lnk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.PdAe,$35.PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)P,(4>.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(?.(10.$4.(24.VdB,)VX,))P,(4?.VdB,)(4:.R>.R=.R<.R;.R:.VdB,=+1.=(19.(2.&40.))R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros until pdA. intros K NE BG. destruct K. flat constr:((a_B0 NE)) 2%nat. intros JB_ BB.
    constructor; try assumption. - left; reflexivity. - left; reflexivity.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11326729879.5 L13234202622.3 L21591057760.15L38232090713.5 L40132594475.6 L41261378637.7 L45315296503.1200000@00I00J00X00g00h00iS1L2HI2sp1h4HTOPS2sp2pX1CFS1L2sp2lo4SLO2S1L2HI2sp1h1a1CFF". (* [comment removed for export] *)
  Lemma lnka_JC : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.PdAe,$35.PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)P,(4>.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(4;.$1<.VL,VHI,R<.R;.R:.R9.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(17.&40.(1>.(1?.&40.Vsp,)+70.))Vlo,=(19.$5.))")
(* [comment removed for export] *).
  Proof.
    intros until pdA. intros K. destruct K. pose proof SPJU' as SPJU. flat constr:(XW) 3%nat. intros XCW XDW XP.
    constructor; rewrite ?SPJU; try assumption; try reflexivity; try (clear - SLO2 HLS; lia).
    - split; [| split; [exact XDW| exact XP]]. cbn [md_addr]. intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; rewrite a_top0; clear - C; lia| right; left; exact C| right; right].
      exists (q, k). split; [apply a_sub0; exact Hq| exact R].
    - cbn [md_own md_p md_n]. intros ON. destruct (XLS ON) as [C|C]; [left; exact C| right; clear - C; lia].
    - rewrite a_top0. clear - HTOP; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0?L11904838205.4 L15672447660.2 L18684593914.4 L22964727664.1 L26184891353.9 L26636580081.4 L28220768376.9 L28837322975.4 L29108390342.7 L30616158697.2 L3226164952.4  L35001535088.1 L36335323928.2 L37212616533.8 L3818602442.4  L38948636245.0 L41918453431.5 L41924822481.3 L41924822481.6 L46900375401.1 L50081116912.5 L51044204458.5 L51044662317.4 L52101785646.9 L52102064936.11L52108071704.3 L59314873579.8 L59314938599.8 L59315053158.6 L59656785403.9 L60701619344.6 L65502317357.2 L66114193000.1 L68177966866.6 L785248895.5   L8929162512.5  00000100900:00>00]00k01J01Y02102902:02>02F02b02c02d03303;03J03N03`04304404S05405<05S06006A06\06]06^06b07707I07\FS3tbp2R0FS2spS1L3HLS2sp2lo2nX2pX4SLO23ACL2R3S1L4IMGC3dAe1HS1L3HLS2sp2lo2nX2pX4SLO23ACL2R3S2sp3dAe6a_ATB0S1L3HLS2sp2lo1X4SLO23XS0S3dAe2N1FS2spS3tbn2N1S1L3HLS2sp2lo4SLO23ACL3dAe1HFSS2sp3dAe1D1a2HaS2sp1a1CS1L2HI2sp1h1a1CS2spS1L3HLS2sp2lo4SLO2S1L4DIMG3tbn3tbp2R4FS1L3HLS2sp2lo4SLO23ACL3DHI1a2C1S1L3HLS2sp2lo4SLO23ACL1a1q1k1R2R3S2sp1a1CS1L2lo3ACL3dAe1a2Ha1C1HS3tap3tbn3tbp2N11E1D3tan4APOSS2lo3dAe1D1a2Ha1CS1L2HI3HLS2sp1h2lo4SLO21a1CFSS2spS1L2lo3ACL3tbn3tbp2R3S1L3HLS2sp2lo4SLO2S3dAe2N12P04LEN'2KB". (* [comment removed for export] *)
  Lemma lnk_copyB : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.PdAe,$35.PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)Ph2,(33.$1<.VL,VHI,)PLB2,(0.$<.)Pm2,P,(2.&40.)(3.(2.&8.))Pmo2,$34.PdTB,$35.Pr,$4.P,(4>.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)P,(10.$4.(24.VdB,)VX,)ZdTB0,$35.(2=.(1>.(1?.&40.Vsp,)+70.)+1.==(19.(2.&40.))R>.$50.)P,(1;.$1<.R7.)P,(1=.$1<.R8.Vlo,(1>.(1?.&40.Vsp,)+70.))P,(20.R13.R8.)P,(10.$4.(21.$1<.VL,VHI,R<.)(21.$1<.VL,VHI,R17.))P,(22.$1<.VL,VHI,R=.R<.R;.R:.)P,(23.$1<.R<.R=.R:.)P,(51.R19.R7.R>.R;.)P,(2;.$1<.VL,R1:.(1>.(1?.&40.Vsp,)+70.)(2<.R8.)R19.R>.)P,(2:.$1<.VL,R?.)P,(52.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R:.R1<.R=.R>.)(4:.R13.R12.R11.R10.R1:.R?.(31.R?.)(53.R?.)(29.R?.)(54.R?.)R19.R18.R17.R16.R15.R14.)")
(* [comment removed for export] *).
  Proof.
    intros until r. intros K BX dTB0 MI2 ST2 MF2 HT2 HH2 MTB OUT2 HPX2 SOK2 CR. subst dTB0.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU' as SPJU.
    pose proof K as [MI1 ST1 HH1 HT1 MF1 SOK1 MX1 HPX1 SUB NEW TMP FR1 JA BA TA AB ABX a_ATB0 AG].
    flat constr:(XW) 3%nat. intros XCW XDW XPo. cbn [md_addr md_own md_p md_n] in XCW, XDW, XPo.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _. flat constr:((heap_blocks _ _ HI _ _ _ _ HH1)) 2%nat. intros HBR1 HAP1. flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2.
    pose proof (HND _ _ _ _ HH2) as ND2.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR0 DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS0.
    flat constr:(OUT2) 5%nat. intros ADT NST_ O3 O4 O5. cbn [md_addr md_own mpd_blk] in ADT, NST_, O3, O4, O5.
    flat constr:(CR) 4%nat. intros _ _ PDT FRT. cbn [md_pad mpd_blk md_own] in PDT, FRT.
    destruct dTB as [tba tbs tbn tbp zsB pdB' oB]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst tba pdB'.
    assert (SUB2 : forall b, In b LB1 -> In b LB2) by (intros b Hb; apply O4; [exact Hb| intros []]).
    flat constr:(MX) 2%nat. intros FLt9 SGX. flat constr:(FLt9) 6%nat. flclear FLt9. intros CX0 XAL X0 LENX NRX OWNX.
    (* [comment removed for export] *)
    assert (XC1 : client_range L LB1 (bv_unsigned sp - 112) X 16).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C; lia| right; left; exact C| right; right; exists (q, k); split; [apply SUB; exact Hq| exact R]]. }
    assert (XBLK : ownX = LHeap -> In (pX, 4 * nX) LB1 /\ 0 < pX /\ pX + 4 * nX <= alloc_ceiling).
    { intros EO. rewrite EO in OWNX. flat constr:(OWNX) 4%nat. flclear OWNX. intros N1 XIN _ _. flat constr:((proj1 (Forall_forall _ _) HBR0 _ XIN)) 5%nat. intros R0 _ _ R3 _. cbn in R0, R3.
      split; [apply SUB; exact XIN|]. split; [exact R0| exact R3]. }
    assert (MX2 : mpd_at usegs m2 LB2 dX).
    { eapply mpd_at_heap_presx; [exact MX1| exact HPX2| exact MI1| exact MI2| exact XC1| | | |]; cbn [md_addr md_own md_p md_n].
      - intros EO a Ha. right; right. exists (pX, 4 * nX). split; [exact (proj1 (XBLK EO))| cbn; exact Ha].
      - unfold mpd_ivs. cbn. split; [clear - XS0 SLO2 HLS; lia| exact I].
      - intros EO. unfold mpd_ivs. cbn. split; [| exact I]. flat constr:((XBLK EO)) 3%nat. intros _ _ R3. clear - R3 ACL SLO2 HLS. lia.
      - intros b Hb. apply SUB2. unfold mpd_blk in Hb. cbn [md_own md_p md_n] in Hb. destruct ownX; try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (XBLK eq_refl)). }
    (* [comment removed for export] *)
    assert (TBF : oB = LHeap -> ~ In (tbp, 4 * tbn) LB1 /\ In (tbp, 4 * tbn) LB2 /\ 1 <= tbn /\ 0 < tbp /\ tbp + 4 * tbn <= alloc_ceiling
                 /\ (tbp + 4 * tbn <= hl_data_lo L \/ hl_data_hi L <= tbp) /\ (forall B j, In (B, j) LB1 -> tbp + 4 * tbn <= B \/ B + j <= tbp)).
    { intros EO. flat constr:(MTB) 2%nat. intros FLt10 _. flat constr:(FLt10) 6%nat. flclear FLt10. intros _ _ _ _ _ OW. cbn [md_own md_p md_n md_limbs] in OW. rewrite EO in OW. flat constr:(OW) 4%nat. flclear OW. intros N1 BIN _ _.
      assert (NIN : ~ In (tbp, 4 * tbn) LB1) by (intros Hin; destruct (FRT _ ltac:(rewrite EO; left; reflexivity)) as [[]|C]; exact (C Hin)).
      flat constr:((proj1 (Forall_forall _ _) HBR2 _ BIN)) 5%nat. intros R0 _ _ R3 R4. cbn in R0, R3, R4.
      split; [exact NIN|]. split; [exact BIN|]. split; [exact N1|]. split; [exact R0|]. split; [exact R3|]. split; [clear - R4 DIMG; lia|].
      intros B j HB. destruct (blocks_apart_neq' _ _ _ HAP2 (SUB2 _ HB) BIN ltac:(intros EE; rewrite EE in HB; exact (NIN HB))) as [D|D]; cbn in D; [right| left]; exact D. }
    (* [comment removed for export] *)
    pose proof JA as [MA1 OA CRA CRAL SXA]. pose proof BA as [BA1 ASS ASL]. flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5.
    flat constr:((bj_facts _ _ _ _ _ _ _ _ _ _ _ _ (lnka_JC _ _ _ _ _ _ _ _ _ _ _ K) _ JA _ _ _ BA)) 8%nat. intros E0 E16 EAL LENE NRE ES OWNE0 OWNE1. rewrite ?SPJU in ES, OWNE1.
    assert (ELIM : md_own dAe <> LNull -> md_p dAe + 4 * md_n dAe <= alloc_ceiling).
    { intros EN. flat constr:((OWNE1 EN)) 6%nat. intros N1 P0 _ EBY _ EIN. flat constr:((AG _ _ _ MA1)) 2%nat. intros FLt11 _. flat constr:(FLt11) 6%nat. flclear FLt11. intros _ _ _ LEN' _ OW.
      destruct (md_own dAe) eqn:EO; [exfalso; exact (EN eq_refl)| |].
      - flat constr:((EIN eq_refl)) 2%nat. intros _ EIN1. flat constr:((proj1 (Forall_forall _ _) HBR1 _ EIN1)) 5%nat. intros _ _ _ R3 _. exact R3.
      - flat constr:(OW) 5%nat. flclear OW. intros _ _ _ _ RO. pose proof (RO (4 * md_n dAe - 1) ltac:(clear - N1; lia)) as RO1.
        pose proof (bytes_at_bound _ _ _ _ EBY) as KB. rewrite u32s_length in KB.
        pose proof (ROIMG _ RO1 ltac:(clear - KB P0 N1 LEN'; lia)). clear - H IMGC. lia. }
    assert (MA2 : mpd_at usegs m2 LB2 dAe).
    { eapply mpd_at_heap_presx; [exact (AG _ _ _ MA1)| exact HPX2| exact MI1| exact MI2| | | | |].
      - intros a Ha. destruct (CRA a Ha) as [C|[C|C]]; [| right; left; exact C| right; right; exact C]. destruct ES as [D|D]; [| left; clear - D Ha; lia].
        exfalso. clear - C D Ha. lia.
      - intros EO a Ha. destruct (CRAL EO a Ha) as [C|[C|C]]; [| right; left; exact C| right; right; exact C].
        pose proof (ELIM ltac:(rewrite EO; discriminate)). exfalso. clear - H Ha C ACL. lia.
      - unfold mpd_ivs. cbn. split; [clear - a_ATB0; pose proof a_ATB0; lia| exact I].
      - intros EO. unfold mpd_ivs. cbn. split; [| exact I]. pose proof (ELIM ltac:(rewrite EO; discriminate)). clear - H ACL SLO2 HLS. lia.
      - intros b Hb. apply SUB2. unfold mpd_blk in Hb. destruct (md_own dAe) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]].
        flat constr:((OWNE1 ltac:(discriminate))) 6%nat. intros _ _ _ _ _ EIN. exact (proj2 (EIN eq_refl)). }
    constructor; try assumption.
    - rewrite HT2. exact HT1.
    - eapply mo_frame_trans; [exact MF1| exact MF2].
    - (* [comment removed for export] *)
      intros a Ha Hc Ho. flat constr:((HPX1 a Ha Hc Ho)) 2%nat. intros E1 W1.
      assert (Hc' : client_addr L LB1 (bv_unsigned sp - 112) a /\ outside (mpd_ivs (mkMPD (bv_unsigned sp - 112) 1 0 0 [] pdB LNull)) a).
      { unfold mpd_ivs. cbn. destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]].
        - split; [left; clear - C; lia|]. split; [clear - C; lia| exact I].
        - split; [right; left; split; assumption|]. split; [clear - C1 DHI ACL SLO2 HLS; lia| exact I].
        - split; [right; right; exists (q, k); split; [apply SUB; exact Hq| exact R]|]. cbn in R.
          flat constr:((proj1 (Forall_forall _ _) HBR0 _ Hq)) 5%nat. intros _ _ _ R3 _. cbn in R3. split; [clear - R R3 ACL SLO2 HLS; lia| exact I]. }
      flat constr:(Hc') 2%nat. flclear Hc'. intros K1 K2. flat constr:((HPX2 a Ha K1 K2)) 2%nat. intros E2 W2. split; [rewrite E2; exact E1| intros Wm; exact (W2 (W1 Wm))].
    - intros b Hb. apply SUB2. apply SUB. exact Hb.
    - intros b Hb. destruct (O3 b Hb) as [C|C].
      + destruct (NEW b C) as [C'|C']; [left; exact C'| right]. unfold temps in C' |- *. cbn [Z.eqb app] in C'. apply in_or_app. right. exact C'.
      + right. unfold temps. apply in_or_app. left. destruct oB; try (destruct C; fail). destruct C as [<-|[]].
        flat constr:((TBF eq_refl)) 5%nat. intros _ _ _ R0 _. replace (tbp =? 0) with false by (symmetry; apply Z.eqb_neq; clear - R0; lia). left; reflexivity.
    - intros b Hb. unfold temps in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      + destruct (Z.eqb_spec tbp 0) as [T0|T0]; [destruct Hb|]. destruct Hb as [<-|[]].
        assert (EO : oB = LHeap).
        { flat constr:(MTB) 2%nat. intros FLt12 _. flat constr:(FLt12) 6%nat. flclear FLt12. intros _ _ _ _ _ OW. cbn [md_own md_p md_n] in OW. destruct oB; [(flat constr:(OW) 2%nat; flclear OW; intros P0 _); exfalso; exact (T0 P0)| reflexivity| exfalso; exact (NST_ eq_refl)]. }
        flat constr:((TBF EO)) 5%nat. intros NIN BIN N1 R0 _. split; [intros Hin; exact (NIN (SUB _ Hin))|].
        split; [| split; [exact BIN| cbn; clear - N1; lia]].
        unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX eqn:EOX; try (intros []; fail). intros [E|[]].
        flat constr:((XBLK eq_refl)) 2%nat. intros XIN1 _. rewrite E in XIN1. exact (NIN XIN1).
      + unfold temps in TMP. cbn [Z.eqb app] in TMP. flat constr:((TMP b Hb)) 4%nat. intros N1 N2 N3 N4. split; [exact N1|]. split; [exact N2|]. split; [apply SUB2; exact N3| exact N4].
    - (* [comment removed for export] *)
      unfold mm_frame in FR1 |- *. flat constr:(MTB) 2%nat. intros (CTB & _) _. cbn [md_addr md_sg md_n md_p md_pad] in CTB.
      apply rw_cells_app in FR1. flat constr:(FR1) 2%nat. flclear FR1. intros _ F3.
      lazymatch type of F3 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp - 96) in F3 by (cbn; clear; lia) end.
      apply rw_cells_app. split.
      + exact CTB.
      + lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (bv_unsigned sp - 96) by (cbn; clear; lia) end.
        eapply heap_presx_rw_cells; [exact HPX2| exact F3| cbn; apply client_range_stack; clear; lia| unfold mpd_ivs; cbn; split; [clear; lia| exact I]].
    - (* [comment removed for export] *) constructor; try assumption; try (apply opnd_at_mpd; exact MA2).
      + intros a Ha. destruct (CRA a Ha) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [apply SUB2; exact Hb| exact R]].
      + intros EO a Ha. destruct (CRAL EO a Ha) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [apply SUB2; exact Hb| exact R]].
    - (* [comment removed for export] *) constructor; [apply opnd_at_mpd; exact MA2| exact ASS| exact ASL].
    - (* [comment removed for export] *)
      constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + apply opnd_at_mpd. exact MTB.
      + unfold opnd_sep. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. rewrite SPJU.
        split. { intros BN. assert (EO : oB = LHeap) by (destruct oB; [exfalso; exact (BN eq_refl)| reflexivity| exfalso; exact (NST_ eq_refl)]).
                 flat constr:((TBF EO)) 7%nat. intros NIN BIN N1 R0 R3 R4 APA.
                 destruct (client_range_apart L LB1 lo X 16 tbp (4 * tbn)) as [D|D]; try (clear - N1; lia); try exact ACL; try exact R3; try exact R4; try exact APA; [| right; exact D| left; exact D].
                 intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C SLO2 HLS; lia| right; left; exact C| right; right; exists (q, k); split; [apply SUB; exact Hq| exact R]]. }
        split. { intros EOX. flat constr:((XBLK EOX)) 3%nat. intros _ _ R3. right. clear - R3 ACL SLO2 HLS. lia. }
        split. { destruct ownX eqn:EOX; [right; left; discriminate| | right; left; discriminate].
                 destruct oB eqn:EOB; [right; right; left; reflexivity| | exfalso; exact (NST_ eq_refl)].
                 flat constr:((TBF eq_refl)) 7%nat. intros NIN BIN N1 R0 R3 R4 APA. flat constr:((XBLK eq_refl)) 2%nat. intros XIN1 _.
                 right; right; right. destruct (APA _ _ XIN1) as [D|D]; [right; exact D| left; exact D]. }
        split; [right; clear; lia|].
        intros BN. assert (EO : oB = LHeap) by (destruct oB; [exfalso; exact (BN eq_refl)| reflexivity| exfalso; exact (NST_ eq_refl)]).
        flat constr:((TBF EO)) 6%nat. intros _ _ _ _ R3 _. left. clear - R3 ACL. lia.
      + apply client_range_stack. clear - SLO2 HLS; lia.
      + intros EO a Ha. flat constr:((TBF EO)) 3%nat. intros _ BIN _. right; right. exists (tbp, 4 * tbn). split; [exact BIN| cbn; exact Ha].
      + clear - XS0 SLO2 HLS. lia.
    - (* [comment removed for export] *)
      constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + apply opnd_at_mpd. exact MTB.
      + intros EOX. flat constr:((XBLK EOX)) 3%nat. intros _ _ R3. right. clear - R3 ACL SLO2 HLS. lia.
      + intros EOX BN. assert (EO : oB = LHeap) by (destruct oB; [exfalso; exact (BN eq_refl)| reflexivity| exfalso; exact (NST_ eq_refl)]).
        flat constr:((TBF EO)) 7%nat. intros NIN BIN N1 R0 R3 R4 APA. flat constr:((XBLK EOX)) 2%nat. intros XIN1 _.
        destruct (APA _ _ XIN1) as [D|D]; [right; exact D| left; exact D].
    - (* [comment removed for export] *)
      destruct oB; [| right; reflexivity| exfalso; exact (NST_ eq_refl)].
      left. flat constr:(MTB) 2%nat. intros FLt13 _. flat constr:(FLt13) 6%nat. flclear FLt13. intros _ _ _ _ _ OW. cbn [md_own md_p md_n] in OW. exact (proj1 OW).
    - (* [comment removed for export] *)
      destruct (Z.eq_dec tbp 0) as [T0|T0]; [left; exact T0|]. destruct (Z.eq_dec tap 0) as [T0'|T0']; [right; left; exact T0'|]. right; right.
      assert (EO : oB = LHeap).
      { flat constr:(MTB) 2%nat. intros FLt14 _. flat constr:(FLt14) 6%nat. flclear FLt14. intros _ _ _ _ _ OW. cbn [md_own md_p md_n] in OW. destruct oB; [(flat constr:(OW) 2%nat; flclear OW; intros P0 _); exfalso; exact (T0 P0)| reflexivity| exfalso; exact (NST_ eq_refl)]. }
      flat constr:((TBF EO)) 7%nat. intros NIN BIN N1 R0 R3 R4 APA.
      (* [comment removed for export] *)
      unfold temps in TMP. cbn [Z.eqb app] in TMP. replace (tap =? 0) with false in TMP by (symmetry; apply Z.eqb_neq; exact T0').
      destruct (TMP (tap, 4 * tan) ltac:(left; reflexivity)) as (_ & _ & AIN1 & APOS). cbn in APOS.
      intros E. destruct (APA _ _ AIN1) as [D|D]; clear - D E N1 APOS; lia.
    - (* [comment removed for export] *) exact (genuine_of _ _ _ MTB).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record ST0 (m0 : mem) (pdB pdA : word) : Prop := {
    z_mi : mem_inv usegs m0;
    z_stk : stk usegs m0 lo (bv_unsigned sp - 112);
    z_heap : HEAP usegs L HI h LB m0 mo;
    z_X : mpd_at usegs m0 LB dX;
    z_A : mpd_at usegs m0 LB dA;
    z_B : mpd_at usegs m0 LB dB;
    z_presx : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m0;
    z_sok : statics_ok usegs L m0;
    z_fr : rw_cells usegs m0 (bv_unsigned sp - 112) (mm_frame 0 1 0 pdB 0 1 0 pdA ra s0 s1 s2 s3 s4 s5 s6 s7 s8)
  }.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis SXB : mpd_sep dX dB.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis CRA : client_range L LB lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L LB lo (md_p dA) (4 * md_n dA).
  Hypothesis CRB : client_range L LB lo (md_addr dB) 16.
  Hypothesis CRBL : md_own dB = LHeap -> client_range L LB lo (md_p dB) (4 * md_n dB).
  Hypothesis MA00 : mpd_at usegs m LB dA.
  Hypothesis MB00 : mpd_at usegs m LB dB.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L31891488440.3L9956773826.4 00000800DS2sp1d1CS2sp2lo1d2O4". (* [comment removed for export] *)
  Lemma opnd_JB : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Pm0,P,(2.&40.)(3.(2.&8.))PLB0,(0.$<.)Pd,$35.P,(23.$1<.R3.R2.R1.)P,Pb,$<.P,(>.$<.R1.VLB,)(>.$<.R2.R5.)P,(55.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R3.)P,(56.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R4.Vlo,(1?.&40.Vsp,))P,(57.VL,VLB,Vlo,(24.R5.)+10.)P,P,(10.$26.(27.R6.)$30.)(57.VL,VLB,Vlo,(31.R7.)(32.+4.(29.R7.)))P,(?.(10.$4.(24.R7.)VX,))(1:.(58.$1<.VL,R9.R:.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(17.&40.(1>.(1?.&40.Vsp,)+70.))Vlo,R8.)(59.$1<.(17.&40.(1>.(1?.&40.Vsp,)+70.))R8.R9.R:.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))")
(* [comment removed for export] *).
  Proof.
    intros m0 LB0 d Md SUB SX OD CR CRL NE. pose proof SPJU' as SPJU. flat constr:(OD) 5%nat. intros O1 O2 O3 O4 O5.
    assert (D : X + 16 <= md_addr d \/ md_addr d + 16 <= X) by (destruct SX as [E|D]; [exfalso; apply NE; rewrite <- E; reflexivity| cbn [md_addr] in D; exact D]).
    split.
    - constructor; rewrite ?SPJU; [apply opnd_at_mpd; exact Md| | | | exact D].
      + split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [clear - O4; lia| intros ON; destruct (O5 ON) as [C|C]; [left; exact C| right; clear - C; lia]].
      + intros a Ha. destruct (CR a Ha) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [apply SUB; exact Hb| exact R]].
      + intros EO a Ha. destruct (CRL EO a Ha) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists b; split; [apply SUB; exact Hb| exact R]].
    - constructor; [apply opnd_at_mpd; exact Md| exact O2|]. intros EO ON. destruct O3 as [C|[C|[C|C]]]; [exfalso; apply NE; rewrite <- C; reflexivity| exfalso; exact (C EO)| exfalso; exact (ON C)| exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L46910384423.7L59314938599.400000I00SS1L3HLS2sp2lo2dA4SLO23OA4S1X2dB1E1D". (* [comment removed for export] *)
  Lemma lnka_noalias : forall m0 pdB pdA, ST0 m0 pdB pdA -> md_addr dA <> X ->
    LNKA h LB m0 mo dA pdB 0 1 0 [] pdA.
  Proof.
    intros m0 pdB pdA K NE. destruct K. flat constr:(OA) 5%nat. intros _ _ _ OA4 _.
    destruct (opnd_JB m0 LB dA z_A0 ltac:(intros b Hb; exact Hb) SXA OA CRA CRAL NE) as [JA BA].
    constructor; try assumption; try reflexivity.
    - apply mo_frame_refl.
    - intros b Hb; exact Hb.
    - intros b Hb; left; exact Hb.
    - intros b Hb. unfold temps in Hb. cbn in Hb. destruct Hb.
    - left; reflexivity.
    - intros NEB. exact (opnd_JB m0 LB dB z_B0 ltac:(intros b Hb; exact Hb) SXB OB CRB CRBL NEB).
    - intros E. destruct SXB as [E'|D]; [symmetry; exact E'| exfalso; cbn [md_addr] in D; clear - D E; lia].
    - clear - OA4 SLO2 HLS. lia.
    - exact (genuine_of _ _ _ z_A0).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0?L10415726953.1 L16188040568.9 L18488355526.7 L18630705146.4 L21111136530.6 L21270006093.8 L21667038736.1 L22964727664.1 L28209341501.4 L30616158697.2 L31674794713.9 L3226164952.4  L32656338056.4 L35001535088.1 L35692135273.1 L3818602442.4  L38948636245.0 L41918453431.5 L41924822481.3 L41924822481.6 L42346440344.2 L46329478570.5 L46329544237.4 L51165555193.2 L51811949356.2 L52101785646.9 L52102064936.11L52108071704.3 L55222140915.6 L56401928560.1 L59309005398.8 L59314938599.4 L59315053158.6 L59656785403.9 L62134836720.5 L65502317357.2 L66114193000.1 L67598260592.1 L785248895.5   L8929162512.5  L9669562934.7  00000400S00k00l01A01]01a01e01f01m02L02M02Z02^02b02c02d03203:03I03Q03d03e03l04404S05405<05=05A05X05b06206M06_06`06d06h07:07L07eS2spS1L3HLS2sp2lo2nX2pX4SLO23ACL2R3S1L3HLS2sp2lo1X4SLO23XS0FS1L2lo3ACL3tan3tap2R3S1L3HLS2sp2lo2dB4SLO23ACL2R3S2spS2spFS2dB2N1S1L3HLS2sp2lo2nX2pX4SLO23ACL2R3FS1L4IMGC2dB1HS2spS2spFSS2sp2dB1D1a2HaS2sp1a1CS1L2HI2sp1h1a1CS3tan2N1S1L4DIMG3tan3tap2R4FS2dB2N1S3tap2R0S1L3HLS2sp2lo4SLO23ACL3DHI1a2C1S1L3HLS2sp2lo4SLO23ACL1a1q1k1R2R3S2sp1a1CFS2spS1L2lo2dB3ACL1a2Ha1C2R3S1X2dB1E1DS2lo2dB1D1a2Ha1CS1L2HI3HLS2sp1h2lo4SLO21a1CS1L3HLS2sp2lo4SLO2SS2spS2spS1L3HLS2sp2lo4SLO2S2dB4LENB2N12P02KBS1L3HLS2sp2lo2dB4SLO23OB4". (* [comment removed for export] *)
  Lemma lnka_copyA : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Pm0,P,(2.&40.)(3.(2.&8.))PpdB,(2.&40.)PpdA,(2.&40.)Ph2,(33.$1<.VL,VHI,)PLB2,(0.$<.)Pm2,P,(2.&40.)(3.(2.&8.))Pmo2,$34.PdTA,$35.Pr,$4.P,(5:.R9.R8.R7.)P,(10.$4.(24.VdA,)VX,)ZdTA0,$35.(2=.(1>.(1?.&40.Vsp,)+60.)+1.==(19.(2.&40.))R9.$50.)P,(1;.$1<.R7.)P,(1=.$1<.R8.Vlo,(1>.(1?.&40.Vsp,)+70.))P,(20.Vmo,R8.)P,(10.$4.(21.$1<.VL,VHI,R<.)(21.$1<.VL,VHI,Vh,))P,(22.$1<.VL,VHI,R=.R<.R;.R:.)P,(23.$1<.R<.R=.R:.)P,(51.VLB,R7.R>.R;.)P,(2;.$1<.VL,VLB,(1>.(1?.&40.Vsp,)+70.)(2<.R8.)R13.R>.)P,(2:.$1<.VL,R?.)P,(52.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)R:.VLB,R=.R>.)(4>.R13.R12.R11.R10.R?.R15.(31.R?.)(53.R?.)(29.R?.)(54.R?.)R14.)")
(* [comment removed for export] *).
  Proof.
    intros until r. intros K AX dTA0 MI2 ST2 MF2 HT2 HH2 MTA OUT2 HPX2 SOK2 CR. subst dTA0.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU' as SPJU.
    pose proof K as [MI1 ST1 HH1 MX1 MA1 MB1 HPX1 SOK1 FR1].
    flat constr:(XW) 3%nat. intros XCW XDW XPo. cbn [md_addr md_own md_p md_n] in XCW, XDW, XPo.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 HAP0. flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2.
    pose proof (HND _ _ _ _ HH2) as ND2.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR0 DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS0.
    flat constr:(OUT2) 5%nat. intros ADT NST_ O3 O4 O5. cbn [md_addr md_own mpd_blk] in ADT, NST_, O3, O4, O5.
    flat constr:(CR) 4%nat. intros _ _ PDT FRT. cbn [md_pad mpd_blk md_own] in PDT, FRT.
    destruct dTA as [taa tas tan tap ysA pdA' oA]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst taa pdA'.
    assert (SUB2 : forall b, In b LB -> In b LB2) by (intros b Hb; apply O4; [exact Hb| intros []]).
    flat constr:(MX) 2%nat. intros FLt15 SGX. flat constr:(FLt15) 6%nat. flclear FLt15. intros CX0 XAL X0 LENX NRX OWNX.
    assert (XC1 : client_range L LB (bv_unsigned sp - 112) X 16).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C; lia| right; left; exact C| right; right; exists (q, k); split; [exact Hq| exact R]]. }
    assert (XBLK : ownX = LHeap -> In (pX, 4 * nX) LB /\ 0 < pX /\ pX + 4 * nX <= alloc_ceiling).
    { intros EO. rewrite EO in OWNX. flat constr:(OWNX) 4%nat. flclear OWNX. intros N1 XIN _ _. flat constr:((proj1 (Forall_forall _ _) HBR0 _ XIN)) 5%nat. intros R0 _ _ R3 _. cbn in R0, R3.
      split; [exact XIN|]. split; [exact R0| exact R3]. }
    assert (MX2 : mpd_at usegs m2 LB2 dX).
    { eapply mpd_at_heap_presx; [exact MX1| exact HPX2| exact MI1| exact MI2| exact XC1| | | |]; cbn [md_addr md_own md_p md_n].
      - intros EO a Ha. right; right. exists (pX, 4 * nX). split; [exact (proj1 (XBLK EO))| cbn; exact Ha].
      - unfold mpd_ivs. cbn. split; [clear - XS0 SLO2 HLS; lia| exact I].
      - intros EO. unfold mpd_ivs. cbn. split; [| exact I]. flat constr:((XBLK EO)) 3%nat. intros _ _ R3. clear - R3 ACL SLO2 HLS. lia.
      - intros b Hb. apply SUB2. unfold mpd_blk in Hb. cbn [md_own md_p md_n] in Hb. destruct ownX; try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (XBLK eq_refl)). }
    assert (TAF : oA = LHeap -> ~ In (tap, 4 * tan) LB /\ In (tap, 4 * tan) LB2 /\ 1 <= tan /\ 0 < tap /\ tap + 4 * tan <= alloc_ceiling
                 /\ (tap + 4 * tan <= hl_data_lo L \/ hl_data_hi L <= tap) /\ (forall B j, In (B, j) LB -> tap + 4 * tan <= B \/ B + j <= tap)).
    { intros EO. flat constr:(MTA) 2%nat. intros FLt16 _. flat constr:(FLt16) 6%nat. flclear FLt16. intros _ _ _ _ _ OW. cbn [md_own md_p md_n md_limbs] in OW. rewrite EO in OW. flat constr:(OW) 4%nat. flclear OW. intros N1 AIN _ _.
      assert (NIN : ~ In (tap, 4 * tan) LB) by (intros Hin; destruct (FRT _ ltac:(rewrite EO; left; reflexivity)) as [[]|C]; exact (C Hin)).
      flat constr:((proj1 (Forall_forall _ _) HBR2 _ AIN)) 5%nat. intros R0 _ _ R3 R4. cbn in R0, R3, R4.
      split; [exact NIN|]. split; [exact AIN|]. split; [exact N1|]. split; [exact R0|]. split; [exact R3|]. split; [clear - R4 DIMG; lia|].
      intros B j HB. destruct (blocks_apart_neq' _ _ _ HAP2 (SUB2 _ HB) AIN ltac:(intros EE; rewrite EE in HB; exact (NIN HB))) as [D|D]; cbn in D; [right| left]; exact D. }
    constructor; try assumption.
    - (* [comment removed for export] *)
      intros a Ha Hc Ho. flat constr:((HPX1 a Ha Hc Ho)) 2%nat. intros E1 W1.
      assert (Hc' : client_addr L LB (bv_unsigned sp - 112) a /\ outside (mpd_ivs (mkMPD (bv_unsigned sp - 96) 1 0 0 [] pdA LNull)) a).
      { unfold mpd_ivs. cbn. destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]].
        - split; [left; clear - C; lia|]. split; [clear - C; lia| exact I].
        - split; [right; left; split; assumption|]. split; [clear - C1 DHI ACL SLO2 HLS; lia| exact I].
        - split; [right; right; exists (q, k); split; [exact Hq| exact R]|]. cbn in R.
          flat constr:((proj1 (Forall_forall _ _) HBR0 _ Hq)) 5%nat. intros _ _ _ R3 _. cbn in R3. split; [clear - R R3 ACL SLO2 HLS; lia| exact I]. }
      flat constr:(Hc') 2%nat. flclear Hc'. intros K1 K2. flat constr:((HPX2 a Ha K1 K2)) 2%nat. intros E2 W2. split; [rewrite E2; exact E1| intros Wm; exact (W2 (W1 Wm))].
    - intros b Hb. destruct (O3 b Hb) as [C|C]; [left; exact C| right].
      unfold temps. cbn [Z.eqb app]. destruct oA; try (destruct C; fail). destruct C as [<-|[]].
      flat constr:((TAF eq_refl)) 5%nat. intros _ _ _ R0 _. replace (tap =? 0) with false by (symmetry; apply Z.eqb_neq; clear - R0; lia). left; reflexivity.
    - intros b Hb. unfold temps in Hb. cbn [Z.eqb app] in Hb.
      destruct (Z.eqb_spec tap 0) as [T0|T0]; [destruct Hb|]. destruct Hb as [<-|[]].
      assert (EO : oA = LHeap).
      { flat constr:(MTA) 2%nat. intros FLt17 _. flat constr:(FLt17) 6%nat. flclear FLt17. intros _ _ _ _ _ OW. cbn [md_own md_p md_n] in OW. destruct oA; [(flat constr:(OW) 2%nat; flclear OW; intros P0 _); exfalso; exact (T0 P0)| reflexivity| exfalso; exact (NST_ eq_refl)]. }
      flat constr:((TAF EO)) 5%nat. intros NIN AIN N1 R0 _. split; [exact NIN|].
      split; [| split; [exact AIN| cbn; clear - N1; lia]].
      unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX eqn:EOX; try (intros []; fail). intros [E|[]].
      flat constr:((XBLK eq_refl)) 2%nat. intros XIN1 _. rewrite E in XIN1. exact (NIN XIN1).
    - (* [comment removed for export] *)
      unfold mm_frame in FR1 |- *. flat constr:(MTA) 2%nat. intros (CTA & _) _. cbn [md_addr md_sg md_n md_p md_pad] in CTA.
      flat constr:((rw_cells_split3 usegs _ _ _ _ _ FR1)) 3%nat. intros F1 _ F3.
      lazymatch type of F3 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp - 80) in F3 by (cbn; clear; lia) end.
      apply rw_cells_join3.
      + eapply heap_presx_rw_cells; [exact HPX2| exact F1| cbn; apply client_range_stack; clear; lia| unfold mpd_ivs; cbn; split; [clear; lia| exact I]].
      + lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (bv_unsigned sp - 96) by (cbn; clear; lia) end. exact CTA.
      + lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (bv_unsigned sp - 80) by (cbn; clear; lia) end.
        eapply heap_presx_rw_cells; [exact HPX2| exact F3| cbn; apply client_range_stack; clear; lia| unfold mpd_ivs; cbn; split; [clear; lia| exact I]].
    - (* [comment removed for export] *)
      constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + apply opnd_at_mpd. exact MTA.
      + unfold opnd_sep. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. rewrite SPJU.
        split. { intros AN. assert (EO : oA = LHeap) by (destruct oA; [exfalso; exact (AN eq_refl)| reflexivity| exfalso; exact (NST_ eq_refl)]).
                 flat constr:((TAF EO)) 7%nat. intros NIN AIN N1 R0 R3 R4 APA.
                 destruct (client_range_apart L LB lo X 16 tap (4 * tan)) as [D|D]; try (clear - N1; lia); try exact ACL; try exact R3; try exact R4; try exact APA; [| right; exact D| left; exact D].
                 intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; clear - C SLO2 HLS; lia| right; left; exact C| right; right; exact C]. }
        split. { intros EOX. flat constr:((XBLK EOX)) 3%nat. intros _ _ R3. right. clear - R3 ACL SLO2 HLS. lia. }
        split. { destruct ownX eqn:EOX; [right; left; discriminate| | right; left; discriminate].
                 destruct oA eqn:EOB; [right; right; left; reflexivity| | exfalso; exact (NST_ eq_refl)].
                 flat constr:((TAF eq_refl)) 7%nat. intros NIN AIN N1 R0 R3 R4 APA. flat constr:((XBLK eq_refl)) 2%nat. intros XIN1 _.
                 right; right; right. destruct (APA _ _ XIN1) as [D|D]; [right; exact D| left; exact D]. }
        split; [right; clear; lia|].
        intros AN. assert (EO : oA = LHeap) by (destruct oA; [exfalso; exact (AN eq_refl)| reflexivity| exfalso; exact (NST_ eq_refl)]).
        flat constr:((TAF EO)) 6%nat. intros _ _ _ _ R3 _. left. clear - R3 ACL. lia.
      + apply client_range_stack. clear - SLO2 HLS; lia.
      + intros EO a Ha. flat constr:((TAF EO)) 3%nat. intros _ AIN _. right; right. exists (tap, 4 * tan). split; [exact AIN| cbn; exact Ha].
      + clear - XS0 SLO2 HLS. lia.
    - (* [comment removed for export] *)
      constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      + apply opnd_at_mpd. exact MTA.
      + intros EOX. flat constr:((XBLK EOX)) 3%nat. intros _ _ R3. right. clear - R3 ACL SLO2 HLS. lia.
      + intros EOX AN. assert (EO : oA = LHeap) by (destruct oA; [exfalso; exact (AN eq_refl)| reflexivity| exfalso; exact (NST_ eq_refl)]).
        flat constr:((TAF EO)) 7%nat. intros NIN AIN N1 R0 R3 R4 APA. flat constr:((XBLK EOX)) 2%nat. intros XIN1 _.
        destruct (APA _ _ XIN1) as [D|D]; [right; exact D| left; exact D].
    - (* [comment removed for export] *)
      destruct oA; [| right; reflexivity| exfalso; exact (NST_ eq_refl)].
      left. flat constr:(MTA) 2%nat. intros FLt18 _. flat constr:(FLt18) 6%nat. flclear FLt18. intros _ _ _ _ _ OW. cbn [md_own md_p md_n] in OW. exact (proj1 OW).
    - (* [comment removed for export] *)
      intros NEB. flat constr:(OB) 5%nat. intros OB1 OB2 OB3 OB4 OB5.
      assert (DB : X + 16 <= md_addr dB \/ md_addr dB + 16 <= X) by (destruct SXB as [E|D]; [exfalso; apply NEB; rewrite <- E; reflexivity| cbn [md_addr] in D; exact D]).
      flat constr:(MB1) 2%nat. intros FLt19 _. flat constr:(FLt19) 6%nat. flclear FLt19. intros _ _ _ LENB NRB OWB.
      assert (BLIM : md_own dB <> LNull -> 0 < md_p dB /\ md_p dB + 4 * md_n dB <= alloc_ceiling).
      { intros BN. destruct (md_own dB) eqn:EO; [exfalso; exact (BN eq_refl)| |].
        - flat constr:(OWB) 3%nat. flclear OWB. intros N1 BIN _. flat constr:((proj1 (Forall_forall _ _) HBR0 _ BIN)) 5%nat. intros R0 _ _ R3 _. cbn in R0, R3. split; [exact R0| exact R3].
        - flat constr:(OWB) 5%nat. flclear OWB. intros N1 _ P0 BBY RO. pose proof (RO 0 ltac:(clear - N1; lia)) as RO0. rewrite Z.add_0_r in RO0.
          pose proof (RO (4 * md_n dB - 1) ltac:(clear - N1; lia)) as RO1.
          pose proof (bytes_at_bound _ _ _ _ BBY) as KB. rewrite u32s_length in KB.
          pose proof (ROIMG _ RO1 ltac:(clear - KB P0 N1 LENB; lia)). split; [exact P0| clear - H IMGC; lia]. }
      assert (MB2 : mpd_at usegs m2 LB2 dB).
      { eapply mpd_at_heap_presx; [exact MB1| exact HPX2| exact MI1| exact MI2| | | | |].
        - intros a Ha. destruct (CRB a Ha) as [C|[C|C]]; [| right; left; exact C| right; right; exact C]. destruct OB4 as [D|D]; [| left; clear - D Ha; lia]. exfalso. clear - C D Ha. lia.
        - intros EO a Ha. destruct (CRBL EO a Ha) as [C|[C|C]]; [| right; left; exact C| right; right; exact C].
          pose proof (BLIM ltac:(rewrite EO; discriminate)) as [_ R3]. exfalso. clear - R3 Ha C ACL. lia.
        - unfold mpd_ivs. cbn. split; [clear - OB4 SLO2 HLS; lia| exact I].
        - intros EO. unfold mpd_ivs. cbn. split; [| exact I]. pose proof (BLIM ltac:(rewrite EO; discriminate)) as [_ R3]. clear - R3 ACL SLO2 HLS. lia.
        - intros b Hb. apply SUB2. unfold mpd_blk in Hb. destruct (md_own dB) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]].
          flat constr:(OWB) 3%nat. flclear OWB. intros _ BIN _. exact BIN. }
      exact (opnd_JB m2 LB2 dB MB2 SUB2 SXB OB CRB CRBL NEB).
    - intros E. destruct SXB as [E'|D]; [symmetry; exact E'| exfalso; cbn [md_addr] in D; clear - D E; lia].
    - cbn [md_addr]. right. clear; lia.
    - exact (genuine_of _ _ _ MTA).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_A2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)PdAe,$35.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Praj,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Px23,(2.&40.)Px24,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(4>.R21.R20.R1?.R1>.R17.R1=.R1<.R1;.R1:.R19.R18.)(47.$1<.R1?.(38.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(39.VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)Vlo,Vm,Vmo,)(3;.(3<.R14.(17.&40.(1>.(1?.&40.Vsp,)+70.))Vgp,Vtp,R17.R16.R15.(17.&40.VX,)(17.&40.(24.VdB,))R13.R12.R11.R10.R?.R>.R=.R<.(17.&40.(24.R18.))R;.R:.R9.R8.R7.R6.Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(17.&40.+20;:8.)Vfc,(3>.(2.&40.))R20.(3?.$1<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros K.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU' as SPJU.
    pose proof K as [MI1 ST1 HH1 HT1 MF1 SOK1 MX1 HPX1 SUB NEW TMP FR1 JA BA TA AB ABX ATB AG].
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
    flat constr:(XW) 3%nat. intros XCW XDW XPo. cbn [md_addr md_own md_p md_n] in XCW, XDW, XPo.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR0 DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS0.
    flat constr:(MX) 2%nat. intros FLt20 SGX. flat constr:(FLt20) 6%nat. flclear FLt20. intros CX0 XAL X0 LENX NRX OWNX. pose proof (rw_cells_bound _ _ _ _ CX0) as XBD. unfold mpi_cells in XBD. cbn [cells_size csize Nat.add md_addr] in XBD.
    flat constr:(MB00) 2%nat. intros (CB0 & _) _. pose proof (rw_cells_bound _ _ _ _ CB0) as BBD. unfold mpi_cells in BBD. cbn [cells_size csize Nat.add] in BBD.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. if_cases KXB; zify_cond KXB; rewrite ?Z.mod_small in KXB by (clear - XBD BBD; lia).
    2: { (* [comment removed for export] *)
         eapply mm_B'. eapply (lnka_lnk _ _ _ _ _ _ _ _ _ _ _ K); [| exact (genuine_of _ _ _ MB00)]. clear - KXB. intros E. apply KXB. rewrite E. reflexivity. }
    (* [comment removed for export] *)
    pose proof (ABX (eq_sym KXB)) as EDB.
    zstep. zstep. zstep.
    unfold mm_frame, mpi_cells in FR1. cbn [app] in FR1.
    pose proof HCOPY as SPc. unfold mpi_copy_stmt in SPc.
    eapply aevtM_cut.
    { eapply SPc with (dX := mkMPD (bv_unsigned sp - 112) 1 0 0 [] pdB LNull) (dY := dX) (lo := lo); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        rewrite ?SPJU; try reflexivity.
      - exact HH1.
      - (* [comment removed for export] *)
        split; [| left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        match type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
          destruct (proj1 (rw_cells_app usegs m1 (bv_unsigned sp - 112) [c0; c1; c2; c3] rest) FR1) as (CTB & _) end.
        split; [unfold mpi_cells; exact CTB|]. split; [clear - SPA; Z.div_mod_to_equations; lia|]. split; [clear - SPB SLO2 HLS ACL ACP; lia|].
        split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; clear; lia|]. split; reflexivity.
      - discriminate.
      - exact MX1.
      - right. cbn [md_addr]. clear - XS0 SLO2 HLS. lia.
      - unfold copy_sep. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split. { intros ON. destruct ownX eqn:EOX; [exfalso; exact (ON eq_refl)| | exfalso; exact (NST eq_refl)].
                 flat constr:(OWNX) 3%nat. flclear OWNX. intros _ XIN _. flat constr:((proj1 (Forall_forall _ _) HBR0 _ XIN)) 5%nat. intros _ _ _ R3 _. cbn in R3. right. clear - R3 ACL SLO2 HLS. lia. }
        split; [intros; discriminate|]. split; [right; left; discriminate|]. split; [clear - XS0 SLO2 HLS; lia|].
        split; [intros ON; destruct (XLS ON) as [C|C]; [left; exact C| right; clear - C; lia]|]. intros a Ha. clear - Ha XBD; lia.
      - intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C SLO2 HLS; lia| right; left; exact C| right; right; exists (q, k); split; [apply SUB; exact Hq| exact R]].
      - intros EOX a Ha. rewrite EOX in OWNX. flat constr:(OWNX) 3%nat. flclear OWNX. intros _ XIN _. right; right. exists (pX, 4 * nX). split; [apply SUB; exact XIN| cbn; exact Ha].
      - split; [| split; [| intros; discriminate]]; cbn [md_addr md_own md_p md_n].
        + intros a Ha. left. rewrite HT1. clear - Ha HTOP. lia.
        + intros a Ha Hd. exfalso. clear - Ha Hd DHI ACL SLO2 HLS. lia.
      - exact ST1.
      - clear - SLO2; lia.
      - exact ACL.
      - rewrite HT1. clear - HTOP; lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact DHI.
      - exact TP.
      - exact MI1.
      - exact SOK1.
      - exact CA.
      - rewrite KXB. reflexivity. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 LB2 dTB r E PO. injection E as -> ->.
    rewrite ?SPJU in PO.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MTB OUT2 HPX2 SOK2 CR.
    replace (ret_pc (Z_to_bv 64 134456)) with (Z_to_bv 64 134456) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (lnk_copyB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K (eq_sym KXB) MI2 ST2 MF2 HT2 HH2 MTB OUT2 HPX2 SOK2 CR) as K2.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    flat constr:(CR) 3%nat. intros CR1 ADT _. destruct dTB as [tba tbs tbn tbp zsB pdB' oB]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst tba.
    clear MU WM FR1. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep.
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      destruct dAe as [Aa sA nA pA ys padA ownA]. cbn [md_addr]. eapply mm_B. exact K2.
    - (* [comment removed for export] *)
      destruct CR1 as [(-> & _)|(-> & _ & EP & _)]; [exfalso; apply KR; reflexivity|]. cbn [md_p] in EP. subst tbp.
      zstep.
      eapply mm_CLEAN; [eapply cst_of_xj; [exact K2| exact (lnk_XJ0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K2)]| exact (l_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K2)| left; reflexivity| | exact (l_dis _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K2)| right; reflexivity| left; reflexivity].
      destruct (l_TA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K2) as [C|E]; [left; exact C| right]. rewrite <- E. exact (opnd_heap_mpd _ _ _ _ (bj_at _ _ _ _ _ _ (l_BA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K2)) ltac:(rewrite E; reflexivity)).
    Unshelve. all: exact [].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma cst_of_lnka : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Ph1,(33.$1<.VL,VHI,)PLB1,(0.$<.)Pm1,P,(2.&40.)(3.(2.&8.))Pmo1,$34.PdAe,$35.PpdB,(2.&40.)Ptap,$4.Ptas,$4.Ptan,$4.PysA,(0.(2.&40.))PpdA,(2.&40.)P,(4>.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(36.(48.==R6.R4.)R<.R;.R:.R9.(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))")
(* [comment removed for export] *).
  Proof.
    intros until pdA. intros K. destruct K. flat constr:(XW) 3%nat. intros _ _ XP. cbn [md_addr md_own md_p md_n] in XP.
    split; [exact a_mi0|]. split; [exact a_stk0|]. split; [exact a_mf0|]. split; [exact a_top0|]. split; [exact a_heap0|]. split; [exact a_X0|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact NST|]. split; [apply Z.le_refl|]. split; [exact a_sok0|]. split; [exact a_presx0|].
    split; [intros b Hb; destruct (a_new0 b Hb) as [C|C]; [left; exact C| right; right; exact C]|]. split; [intros b Hb _; exact (a_sub0 b Hb)|].
    split; [intros; reflexivity|]. split; [intros b Hb; left; exact Hb|].
    split; [| exact XP]. intros b Hb. flat constr:((a_tmp0 b Hb)) 4%nat. intros N1 N2 N3 N4. split; [exact N1|]. split; [exact N2|]. split; [exact N3| exact N4].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mm_MAIN : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(1=.$1<.Vm,Vlo,(1?.&40.Vsp,))(47.$1<.Vmo,(38.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(39.VLB,(2=.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)Vlo,Vm,Vmo,)(3;.(3<.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,(17.&40.VX,)(17.&40.(24.VdA,))(17.&40.(24.VdB,))R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(17.&40.+20;58.)Vfc,(3>.(2.&40.))Vm,(3?.$1<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros ST.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV. pose proof SPJU' as SPJU.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
    flat constr:(XW) 3%nat. intros XCW XDW XPo. cbn [md_addr md_own md_p md_n] in XCW, XDW, XPo.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(clear; lia) HBR0 DHI ACL ltac:(clear - SLO2 HLS; lia)) as XS0.
    flat constr:(MX) 2%nat. intros FLt21 SGX. flat constr:(FLt21) 6%nat. flclear FLt21. intros CX0 XAL X0 LENX NRX OWNX. pose proof (rw_cells_bound _ _ _ _ CX0) as XBD. unfold mpi_cells in XBD. cbn [cells_size csize Nat.add md_addr] in XBD.
    flat constr:(MA00) 2%nat. intros (CA0 & _) _. pose proof (rw_cells_bound _ _ _ _ CA0) as ABD. unfold mpi_cells in ABD. cbn [cells_size csize Nat.add] in ABD.
    flat constr:(OA) 5%nat. intros OA1 OA2 OA3 OA4 OA5. flat constr:(OB) 5%nat. intros OB1 OB2 OB3 OB4 OB5.
    pose proof MI0 as MI.
    carve_frame 112%nat ST.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    set (mI := m) in HH, MX, MA00, MB00, MI0, SOK0, CX0, CA0.
    do 11 zstep.
    replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) in * by (clear; lia).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    pose proof HH as HH'. pose proof SOK0 as SOK'. pose proof MX as MX'. pose proof MA00 as MA'. pose proof MB00 as MB'. unfold mI in HH', SOK', MX', MA', MB'.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (C8 _ :: C4 _ :: CB 4 ?jb :: C8 _ :: C4 _ :: CB 4 ?jc :: _) =>
      set (jB := jb) in FR; set (jA := jc) in FR end.
    pose proof (rw_cells_split_C4 usegs m0 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) _ FR) as FR2. cbn [app] in FR2.
    pose proof (rw_cells_CB4_C4 usegs m0 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16))] jB _ FR2) as FR3. cbn [app] in FR3.
    pose proof (rw_cells_split_C4 usegs m0 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16)); C4 (le_bytes_to_word jB); C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) _ FR3) as FR4. cbn [app] in FR4.
    pose proof (rw_cells_CB4_C4 usegs m0 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16)); C4 (le_bytes_to_word jB); C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16))] jA _ FR4) as FR5. cbn [app] in FR5.
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16)) with (Z_to_bv 64 0) in FR5 by (rewrite unsigned_lit by (clear; lia); reflexivity).
    clear FR FR2 FR3 FR4.
    assert (HH0 : HEAP usegs L HI h LB m0 mo).
    { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH'| exact MU| exact WM| exact ACL|]. intros a Ha NO. cbn in NO. left. clear - NO HTOP SLO2 HLS. lia. }
    assert (MX0 : mpd_at usegs m0 LB dX).
    { eapply mpd_at_munch_any; [exact MX'| exact MU| exact WM| cbn; split; [clear - XS0 SLO2 HLS; lia| exact I]|].
      cbn [md_own md_p md_n]. intros ON. cbn. split; [| exact I]. destruct (XLS ON); clear - H SLO2 HLS; lia. }
    assert (MA0' : mpd_at usegs m0 LB dA).
    { eapply mpd_at_munch_any; [exact MA'| exact MU| exact WM| cbn; split; [clear - OA4 SLO2 HLS; lia| exact I]|].
      intros ON. cbn. split; [| exact I]. destruct (OA5 ON); clear - H SLO2 HLS; lia. }
    assert (MB0' : mpd_at usegs m0 LB dB).
    { eapply mpd_at_munch_any; [exact MB'| exact MU| exact WM| cbn; split; [clear - OB4 SLO2 HLS; lia| exact I]|].
      intros ON. cbn. split; [| exact I]. destruct (OB5 ON); clear - H SLO2 HLS; lia. }
    assert (HPX0 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m0).
    { eapply heap_presx_frame; [exact MU| exact WM| exact HBR0| exact DHI| clear - ACL SLO2 HLS; lia]. }
    assert (SOKm0 : statics_ok usegs L m0).
    { eapply statics_ok_munch; [exact SOK'| exact MU|]. intros a Hd NW. cbn. split; [clear - Hd DHI ACL SLO2 HLS; lia| exact I]. }
    match goal with MIx : mem_inv usegs m0, STx : stk usegs m0 _ _ |- _ =>
      pose proof (Build_ST0 m0 (le_bytes_to_word jB) (le_bytes_to_word jA) MIx STx HH0 MX0 MA0' MB0' HPX0 SOKm0 FR5) as K0 end.
    clear MU WM HH' SOK' MX' MA' MB'. pose proof (munch_refl ([] : list ivl) m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    zstep. if_cases KXA; zify_cond KXA; rewrite ?Z.mod_small in KXA by (clear - XBD ABD; lia).
    2: { (* [comment removed for export] *) eapply (mm_A2 _ _ _ _ _ _ _ _ _ _ dA). eapply lnka_noalias; [exact K0|]. clear - KXA. intros E. apply KXA. rewrite E. reflexivity. }
    (* [comment removed for export] *)
    pose proof K0 as [MI1 ST1 HH1 MX1 MA1 MB1 HPX1 SOK1 FR1]. unfold mm_frame, mpi_cells in FR1. cbn [app] in FR1.
    zstep. zstep. zstep.
    pose proof HCOPY as SPc. unfold mpi_copy_stmt in SPc.
    eapply aevtM_cut.
    { eapply SPc with (dX := mkMPD (bv_unsigned sp - 96) 1 0 0 [] (le_bytes_to_word jA) LNull) (dY := dX) (lo := lo); cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own];
        rewrite ?SPJU; try reflexivity.
      - exact HH1.
      - split; [| left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        match type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
          destruct (rw_cells_split3 usegs m0 (bv_unsigned sp - 112) [c0; c1; c2; c3] [c4; c5; c6; c7] rest FR1) as (_ & CTA & _) end.
        lazymatch type of CTA with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp - 96) in CTA by (cbn; clear; lia) end.
        split; [unfold mpi_cells; exact CTA|]. split; [clear - SPA; Z.div_mod_to_equations; lia|]. split; [clear - SPB SLO2 HLS ACL ACP; lia|].
        split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; clear; lia|]. split; reflexivity.
      - discriminate.
      - exact MX1.
      - right. cbn [md_addr]. clear - XS0 SLO2 HLS. lia.
      - unfold copy_sep. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split. { intros ON. destruct ownX eqn:EOX; [exfalso; exact (ON eq_refl)| | exfalso; exact (NST eq_refl)].
                 flat constr:(OWNX) 3%nat. flclear OWNX. intros _ XIN _. flat constr:((proj1 (Forall_forall _ _) HBR0 _ XIN)) 5%nat. intros _ _ _ R3 _. cbn in R3. right. clear - R3 ACL SLO2 HLS. lia. }
        split; [intros; discriminate|]. split; [right; left; discriminate|]. split; [clear - XS0 SLO2 HLS; lia|].
        split; [intros ON; destruct (XLS ON) as [C|C]; [left; exact C| right; clear - C; lia]|]. intros a Ha. clear - Ha XBD; lia.
      - intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C SLO2 HLS; lia| right; left; exact C| right; right; exists (q, k); split; [exact Hq| exact R]].
      - intros EOX a Ha. rewrite EOX in OWNX. flat constr:(OWNX) 3%nat. flclear OWNX. intros _ XIN _. right; right. exists (pX, 4 * nX). split; [exact XIN| cbn; exact Ha].
      - split; [| split; [| intros; discriminate]]; cbn [md_addr md_own md_p md_n].
        + intros a Ha. left. clear - Ha HTOP. lia.
        + intros a Ha Hd. exfalso. clear - Ha Hd DHI ACL SLO2 HLS. lia.
      - exact ST1.
      - clear - SLO2; lia.
      - exact ACL.
      - clear - HTOP; lia.
      - clear - SPA. Z.div_mod_to_equations. lia.
      - exact DHI.
      - exact TP.
      - exact MI1.
      - exact SOK1.
      - exact CA.
      - f_equal. clear; lia.
      - rewrite KXA. reflexivity. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 LB2 dTA r E PO. injection E as -> ->.
    rewrite ?SPJU in PO.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MTA OUT2 HPX2 SOK2 CR.
    replace (ret_pc (Z_to_bv 64 134172)) with (Z_to_bv 64 134172) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (lnka_copyA _ _ _ _ _ _ _ _ _ K0 (eq_sym KXA) MI2 ST2 MF2 HT2 HH2 MTA OUT2 HPX2 SOK2 CR) as K2.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    flat constr:(CR) 3%nat. intros CR1 ADT _. destruct dTA as [taa tas tan tap ysA pdA' oA]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst taa.
    clear MU WM FR1 FR5. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. replace (bv_unsigned sp - 112 + 16) with (bv_unsigned sp - 96) by (clear; lia).
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      destruct CR1 as [(-> & _)|(-> & _ & EP & _)]; [exfalso; apply KR; reflexivity|]. cbn [md_p] in EP. subst tap.
      zstep.
      eapply mm_CLEAN with (zsB := []); [eapply cst_of_lnka; exact K2| exact (a_fr _ _ _ _ _ _ _ _ _ _ _ K2)| left; reflexivity| left; reflexivity| left; reflexivity| right; reflexivity| right; left; reflexivity].
    - (* [comment removed for export] *)
      zstep. eapply (mm_A2 _ _ _ _ _ _ _ _ _ _ (mkMPD (bv_unsigned sp - 96) tas tan tap ysA pdA' oA)). exact K2.
    Unshelve. all: try exact []; try exact (Z_to_bv 64 0); try exact 0.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Main.

(* [comment removed for export] *)
Section Spec.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.

  Theorem U_mpi_mul_mpi_spec' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_mul_mpi ()) "PMSF,$4.P,(10.$4.R1.$5;.)P,(5<.$1<.VL,VHI,$5=.R2.)(5>.$1<.VL,VHI,$5?.R3.)")
(* [comment removed for export] *).
  Proof.
    intros MSF MSFE HCOPY. unfold mpi_mul_mpi_stmt, mpi_binop_stmt, U_MPI_MUL_MPI. intros until lo.
    intros HH MX MA0 MB0 SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO2 ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    destruct dX as [X sX nX pX xs0 padX ownX]. cbn [md_addr md_own md_p md_n] in NST, XLS.
    eapply (mm_MAIN L HI HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB lo MSF X sX nX pX xs0 padX ownX dA dB);
      try eassumption.
  Qed.

  Theorem U_mpi_mul_mpi_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_mul_mpi_stmt usegs L HI U_MPI_MUL_MPI MSF.
  Proof.
    intros MSF ->. apply U_mpi_mul_mpi_spec'; [reflexivity|].
    apply U_mpi_copy_spec; try assumption. intros a H1 H2. exact (ROIMG a H2 H1).
  Qed.
End Spec.

