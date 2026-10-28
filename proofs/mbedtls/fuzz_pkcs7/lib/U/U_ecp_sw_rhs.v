(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts CrtFacts RepEcp EcpFacts EcpLoad. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_cmp U_ecp_red U_ecp_mul_mod.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
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
Ltac2 gd_tbl_P_ecp_sw_rhs () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_A"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_B"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.ext_opnd"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.ecp_mul_mod_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.mm_base"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.mm_inv"; "SR.sr_frame"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.opnd_sep"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "ECP_SW_RHS_STACK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"].


Definition ECP_SW_RHS_STACK : Z := 656.   (* [comment removed for export] *)

Definition ecp_sw_rhs_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ENTRY MSF MC STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.O8.O7.O6.)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Pcnt,(0.&40.)Plo,$8.P,(:.O8.O7.O6.R8.R7.R:.R9.)P,(;.O8.O5.R;.R8.R5.R4.)P,(<.$8.(=.R5.)+1.)P,(<.$8.(>.(?.R6.))+1.)P,(<.$8.(>.(10.R7.))+1.)P,(<.$8.(>.(11.R8.))+1.)P,(12.+1.(13.(?.R9.)))P,(14.O7.R>.R8.R;.+<0.)P,(15.(12.(16.R<.+<0.)R9.)(12.(17.&40.R32.)R<.))P,(15.(12.(16.(18.R?.)+10.)R=.)(12.(16.R=.+<0.)(18.R?.)))P,P,(<.$19.(1:.R10.)$1;.)(15.(12.(16.R?.+<0.)(1<.R11.))(12.(16.(1<.R11.)(1=.+4.(1>.R11.)))R?.))P,(1?.O8.R15.R12.R11.)P,(20.(<.$19.(1:.R12.)$21.))P,(22.O7.R14.(17.&40.R37.)(23.O8.O7.O6.R15.)R13.)P,P,(20.(<.$19.(1:.R14.)$24.))(15.(12.(16.(1<.R15.)(1=.+4.(1>.R15.)))R10.)(12.(17.&40.R39.)(1<.R15.)))P,(1?.O8.R19.R16.R14.)P,(25.O7.R17.R16.R15.O2.(17.&40.R3:.)R11.)P,(26.O8.R1;.O2.(27.$28.(29.R13.)(2:.$28.)))P,(12.(2;.O7.)O2.)P,(12.(16.O2.+8.)(2<.O7.))P,Pa,$8.P,(2=.(12.O2.R1.)(2>.R1.(16.O2.+8.)))(2=.(20.(2?.O7.R2.))(30.O7.R2.))P,(15.(12.(16.O2.+8.)(18.R1;.))(12.(16.(18.R1;.)+10.)O2.))P,(15.(12.(16.O2.+8.)R1:.)(12.(16.R1:.+<0.)O2.))P,(31.O8.R21.R18.(17.&40.R41.))P,(12.R19.(32.(32.(17.&40.R42.)O1.)(33.O7.)))P,(12.(34.O7.)R1:.)P,(12.(17.&40.R44.)(23.O8.O7.O6.R22.))P,(<.$8.(35.(17.&40.R45.)+10.)=)P,(12.(2<.O7.)(34.O7.))P,(<.(0.&40.)R45.(36.&40.(37.O7.)))P,(38.O8.R28.)P,(39.O8.O7.R29.)P,(3:.O7.O3.+8.)P,(<.(0.&40.)R43.(36.&40.R25.))P,(<.(0.&40.)R43.(36.&40.(18.R28.)))P,(<.(0.&40.)R43.(36.&40.(18.R28.)))(3;.O8.R2=.(3<.O8.O7.O6.O5.R4?.R4>.R4=.R4<.R48.R47.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R30.R2?.R2<.R2;.R2:.R28.R27.O2.R25.R2>.R2=.)(3=.(3>.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.)R30.(36.&40.O4.)R2?.(3?.(0.&40.))R2>.(40.O8.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma mpd_abs_nonneg : forall d, 0 <= mpd_abs d.
Proof. intros d. unfold mpd_abs. apply limbs_val_nonneg. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L35074859392.4L56810737828.400000300;S1dS1d1H2H0". (* [comment removed for export] *)
Lemma mpd_val_pos_abs : forall d, (md_sg d = 1 \/ md_sg d = -1) -> 0 < mpd_val d -> mpd_abs d = mpd_val d /\ md_sg d = 1.
Proof. intros d [S|S] H; unfold mpd_val, mpd_abs in *; rewrite S in *; pose proof (limbs_val_nonneg (md_limbs d)); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L42250180652.2000003S1d". (* [comment removed for export] *)
Lemma mpd_val_sg1 : forall d, md_sg d = 1 -> mpd_val d = mpd_abs d.
Proof. intros d S. unfold mpd_val, mpd_abs. rewrite S. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition U_ECP_SW_RHS : Z := 0x3a7a4.
Notation U_MUL_COUNT := 380840 (only parsing).

Section SR.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  Variable MT : list modp_ent.
  (* [comment removed for export] *)
  Hypothesis HMM : ecp_mul_mod_stmt usegs L HI MT 0x3a8f4 U_MEMSET_FUNC U_MUL_COUNT ECP_MUL_MOD_STACK.
  Hypothesis HADD : mpi_add_mpi_stmt usegs L HI 0x209fc U_MEMSET_FUNC.
  Hypothesis HSUBA : mpi_sub_abs_stmt usegs L HI 0x2078c U_MEMSET_FUNC.
  Hypothesis HSUBI : mpi_sub_int_stmt usegs L HI 0x20b0c U_MEMSET_FUNC.
  Hypothesis HCMP : mpi_cmp_mpi_stmt usegs 0x202a4.
  Hypothesis HCMPI : mpi_cmp_int_stmt usegs 0x2044c.

  Definition sr_frame (j8 : list byte) (s3e s2e s1e s0e rae : word) : list cell := [CB 8 j8; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L11542269846.103L13100768790.103L14471356349.106L43263663511.106L44109073686.103L49236136086.103L58132820783.107L8869413654.103 L940844358.106  00000;00F00Q00\00g01201E01P01[S3spv2j82J8S3spv2j82J8S3spv2j82J8S3spv2j82J8S3spv2j82J8S3spv2j82J8S3spv2lo2j82J84LOSPS3spv2j82J8S3spv2j82J8". (* [comment removed for export] *)
  #[using="Type"] Lemma sr_exit : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2e,(0.&40.)Ps3e,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0c,(0.&40.)Ps1c,(0.&40.)Ps2c,(0.&40.)Ps3c,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PG,$8.Pg,$9.Plo,$8.Ph1,(4.$41.VL,VHI,)PLB1,(5.$6.)PdX1,$7.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.Pr,$8.Pj8,(5.(0.&8.))P,(42.VL,R<.R;.R:.+5<?:8.(17.&40.R33.)+30.R8.(23.$41.VL,VHI,R=.)R9.)P,(1?.$41.R10.R=.R<.)P,(43.$41.VL,VHI,VMT,R?.R>.R=.R<.R;.+5<?:8.(17.&40.R35.)+30.R:.R11.R10.R9.R8.R7.R6.R5.)P,(26.$41.R7.(16.(17.&40.R36.)-30.)(44.R4.R30.R31.R32.R33.R37.))P,(<.$45.(46.(0.&8.)R5.)#8.)P,(2=.(2>.(47.(48.+2.+1?.))R7.)(12.R7.=))(3;.$41.R9.(3<.$41.VL,VHI,VMT,R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R17.R16.R13.R12.R11.R10.R?.+5<?:8.R>.R15.R14.)(3=.(3>.R2:.(36.&40.(16.(17.&40.R39.)-30.))R38.R37.R29.R28.R27.R26.R25.(36.&40.R8.)R22.R21.R20.R1?.R1>.R1=.R1<.R24.R23.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R1;.R1:.R19.R18.)R17.(36.&40.+3:7=4.)R16.(3?.(0.&40.))R:.(40.$41.)))")
(* [comment removed for export] *).
  Proof.
    intros until j8. intros BASE MA INV FR J8 Hr.
    pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    ddestruct INV as (HH1 & MA1 & OUT1 & FR1 & PAD1 & NLE1 & PX1 & SOK1 & MI1 & MF1 & HT1 & GR1 & [cnt1 CNT1] & ST1).
    replace (bv_unsigned spv - 48) with (bv_unsigned spv + -48) in ST1 by lia. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    unfold sr_frame in FR.
    zstep. zstep. zstep. zstep. zstep. release_frame FR ST1 (bv_unsigned spv). zstep.
    try (replace (bv_unsigned spv + -48 + 48) with (bv_unsigned spv) by lia; rewrite (Z_to_bv_bv_unsigned spv)). zstep.
    apply aevtM_done. unfold ecp_mul_mod_post.
    deexists 14. dexists m1, mo1, h1, LB1, dX1, r, cnt1.
    split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact MF1|]. split; [exact HT1|].
    split; [exact HH1|]. split; [exact MA1|]. split; [exact OUT1|]. split; [exact PX1|]. split; [exact SOK1|].
    split; [exact GR1|]. split; [exact CNT1|].
    unfold mul_mod_R, binop_keep. destruct OUT1 as (EA1 & _). exact (conj Hr (conj EA1 (conj PAD1 (conj FR1 NLE1)))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L47801051489.36L63381042064.36000001002SS". (* [comment removed for export] *)
  #[using="DIMG ROIMG IMGC"] Lemma sr_P_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PG,$8.Pg,$9.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph1,(4.$41.VL,VHI,)PLB1,(5.$6.)PdX1,$7.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.PSP,$8.P,(42.VL,R=.R<.R;.+5<?:8.R1.+30.R9.(23.$41.VL,VHI,R>.)R:.)P,(1?.$41.R9.R>.R=.)P,(<.$8.(=.R<.)+1.)P,(<.$8.(>.(?.R=.))+1.)P,(43.$41.VL,VHI,VMT,R12.R11.R10.R?.R>.+5<?:8.R5.+30.R=.R<.R;.R:.R9.R8.R7.R6.)(2=.(1?.$41.R8.R:.(?.R?.))(2=.(49.R9.(?.R?.))(2=.(4:.R9.(?.R?.)R>.(32.R6.+30.))(2=.(14.VL,R:.R>.(18.(?.R?.))+10.)(2=.P,(<.$19.(1:.(?.R?.))$1;.)(14.VL,R;.R?.(1<.(?.R10.))(1=.+4.(1>.(?.R10.))))(2=.(<.$8.(18.(?.R?.))(16.R10.+8.))(20.(<.$19.(1:.(?.R?.))$1;.))))))))")
(* [comment removed for export] *).
  Proof.
    intros h LB dX G g lo m mo h1 LB1 dX1 m1 mo1 SP BASE MA H1 GPS INV.
    dpose INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GR1 & _).
    dpose GR1 as (_ & _ & _ & EP & _ & _ & _ & MP & _).
    assert (POWN : md_own (g_P g) <> LHeap) by (apply (grp_static_own usegs MT m1 LB1 G g _ GR1 H1); cbn; auto).
    pose proof (mm_grp_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT SP 48 lo m mo h1 LB1 dX1 m1 mo1 (g_P g) 8 ROIMG IMGC BASE MA INV MP POWN (or_introl GPS) EP ltac:(lia) ltac:(lia)) as B.
    ddestruct B as (B1 & B2 & B3 & B4 & B5). exact (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj EP POWN)))))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L11710712414.158L15320267806.158L16075584458.121L21186064871.132L246904734.158  L29010566049.151L29962731771.161L34229555104.5  L45914717502.8  L48281031184.155L50284849680.76 L54315085739.127L59308628304.156L59353370052.159L61274419438.158L61274419565.128L63219124928.129L64626056980.132L818452692.5    00000F00G00H00g01=01>01_02302N02d05I05_06806\07207J07i08?08LS1n3spv3dX12j84MEAS2J8FFS1L1n3spv2lo3dX12j84MEAS2J83SLOS1n3spv3dX12j84MEAS2J8FS1L1n3spv2lo3dX12j84MEAS2J83SLO1rS3spv2dX2lo3SXS4LOSPS1n1g3dX14MEAS2PV2GE3dX22V2S1n3spv3dX12j84MEAS2J8S1L2HI2MT3rae3spv2gp2tp3s0e3s1e3s2e3s3e2s42s52s62s72s82s93s103s113ra02t02t12t23s2c2a02a12a22a32a42a52a62a72t32t42t52t61F2fc1m2mo1h2LB2dX1G1g2lo3dX12m13mo12j84MEAS2J8S1n3spv3dX12j84MEAS2J8S1n3spv3dX12j84MEAS2J82K1S1n3spv1g3dX12j84MEAS2PV2J83SPB2GE1rS1n3spv3dX12j84MEAS2J8S1n3spv1g3dX12j84MEAS2J8S1n3spv1g3dX12j84MEAS2J83SPB2K0S1n3spv3dX12j84MEAS2J8S3spv3SPA3SPB". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HSUBA HCMP"] Lemma sr_loop2 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Pn,$45.Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2e,(0.&40.)Ps3e,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps2c,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PG,$8.Pg,$9.Plo,$8.Ph1,(4.$41.VL,VHI,)PLB1,(5.$6.)PdX1,$7.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.Pj8,(5.(0.&8.))P,(4;.(4<.(13.R4.))R32.)P,(42.VL,R<.R;.R:.+5<?:8.(17.&40.R31.)+30.R8.(23.$41.VL,VHI,R=.)R9.)P,(1?.$41.R10.R=.R<.)P,(15.(12.(16.(18.R=.)+10.)R:.)(12.(17.&40.R33.)(18.R=.)))P,(<.$8.(=.R<.)+1.)P,(<.$8.(>.(?.R=.))+1.)P,(12.+1.(13.(?.R>.)))P,(43.$41.VL,VHI,VMT,R13.R12.R11.R10.R?.+5<?:8.(17.&40.R37.)+30.R>.R15.R14.R=.R<.R;.R:.R9.)P,(26.$41.R;.(16.(17.&40.R38.)-30.)(44.R9.R32.R33.R34.R35.R39.))P,(<.$45.(46.(0.&8.)R:.)#8.)P,(<.(0.&40.)R38.(36.&40.(37.VL,)))P,(3:.VL,$4=.+8.)P,(12.R13.(32.(32.(17.&40.R3<.)$4>.)(33.VL,)))P,(<.$8.(35.(17.&40.R3=.)+10.)=)(3;.$41.R10.(3<.$41.VL,VHI,VMT,R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R1>.R1=.R1:.R19.R18.R17.R16.+5<?:8.R15.R1<.R1;.)(3=.(3>.R2?.(36.&40.(16.(17.&40.R3>.)-30.))R3=.R3<.R2>.R2=.R2<.(36.&40.(18.R18.))(36.&40.(16.R17.+8.))R2:.R29.R28.R27.R26.R25.R24.R23.R2;.(36.&40.(16.R17.+8.))R37.R36.R35.R34.R33.R32.R31.R30.R22.R21.R20.R1?.)R1>.(36.&40.+3:8<0.)R1=.(3?.(0.&40.))R11.(40.$41.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until j8; intros MEAS BASE MA SXS GH1 GPS PV INV FR J8 TP CA SLO SPA; [lia|].
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB. unfold ECP_SW_RHS_STACK in SLO.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    destruct (sr_P_opnd h LB dX G g lo m mo h1 LB1 dX1 m1 mo1 _ BASE MA GH1 GPS INV) as (MP1 & SXP & OXP & CRP & CRPL & EP & POWN).
    dpose INV as (HH1 & MA1 & OUT1 & _). pose proof OUT1 as (EA1 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    pose proof MA1 as [_ SG1].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply (mm_call_cmp usegs L HI); [exact HCMP| exact INV| exact MP1| intros O; exfalso; exact (POWN O)| first [reflexivity| rewrite EA1; reflexivity]| rewrite EP; reflexivity|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'. replace (ret_pc (Z_to_bv 64 0x3a8cc)) with (Z_to_bv 64 0x3a8cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. zstep. eapply sr_exit; [exact BASE| exact MA| exact INV| exact FR| exact J8| lia].
    - (* [comment removed for export] *)
      assert (GE : mpd_val (g_P g) <= mpd_val dX1) by (pose proof (Z.sgn_spec (mpd_val dX1 - mpd_val (g_P g))); lia).
      clear K0. zstep. zstep. zstep. zstep.
      ddestruct (mm_self_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 48 lo m mo h1 LB1 dX1 m1 mo1 BASE MA INV) as (SXX & OXX & CRX & CRXL).
      eapply (mm_call_binop usegs L HI DIMG) with (FRC := sr_frame j8 s3e s2e s1e s0e rae);
        [exact HSUBA| intros ? ? ? ? ? ? [_ KP]; exact KP| exact BASE| exact MA| exact INV| reflexivity| exact FR| lia| cbn; clear - SXS LOSP; lia
        | exact MA1| exact MP1| exact SXX| exact SXP| exact SXP| exact OXX| exact OXP| exact CRX| exact CRXL| exact CRP| exact CRPL
        | lia| exact HLS| clear - SPA SPB LOSP; lia| exact TP| exact CA| first [reflexivity| rewrite EA1; reflexivity]| first [reflexivity| rewrite EA1; reflexivity]| rewrite EP; reflexivity|].
      intros m2 mo2 h2 LB2 dX2 r ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 FR2 RR _.
      replace (ret_pc (Z_to_bv 64 0x3a8e0)) with (Z_to_bv 64 0x3a8e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof INV2 as (HH2 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        ddestruct RR as [[(_ & V2 & S2)|[Er|[Er _]]] _]; [| exfalso; subst r; cbv in K1; lia| exfalso; subst r; cbv in K1; lia].
        destruct (mpd_val_pos_abs dX1 SG1 ltac:(lia)) as [AX1 _]. pose proof (mpd_val_sg1 _ GPS) as VP. rewrite AX1, <- VP in V2.
        eapply IH with (dX1 := dX2) (h1 := h2) (LB1 := LB2) (j8 := j8); [clear - MEAS V2 GE PV; lia| exact BASE| exact MA| exact SXS| exact GH1| exact GPS| exact PV| exact INV2| exact FR2| exact J8| exact TP| exact CA| unfold ECP_SW_RHS_STACK; lia| exact SPA].
      + (* [comment removed for export] *)
        zstep. eapply sr_exit; [exact BASE| exact MA| exact INV2| exact FR2| exact J8| first [lia| ddestruct RR as [[(Er & _)|[Er|[Er _]]] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia| ddestruct RR as [[(Er & _)|Er] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L41889544848.36L50127424097.36000001002SS". (* [comment removed for export] *)
  #[using="DIMG ROIMG IMGC"] Lemma sr_A_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PG,$8.Pg,$9.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph1,(4.$41.VL,VHI,)PLB1,(5.$6.)PdX1,$7.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.PSP,$8.P,(42.VL,R=.R<.R;.+5<?:8.R1.+30.R9.(23.$41.VL,VHI,R>.)R:.)P,(1?.$41.R9.R>.R=.)P,(<.$8.(=.R<.)+1.)P,(<.$8.(>.(10.R=.))+1.)P,(43.$41.VL,VHI,VMT,R12.R11.R10.R?.R>.+5<?:8.R5.+30.R=.R<.R;.R:.R9.R8.R7.R6.)(2=.(1?.$41.R8.R:.(10.R?.))(2=.(49.R9.(10.R?.))(2=.(4:.R9.(10.R?.)R>.(32.R6.+30.))(2=.(14.VL,R:.R>.(18.(10.R?.))+10.)(2=.P,(<.$19.(1:.(10.R?.))$1;.)(14.VL,R;.R?.(1<.(10.R10.))(1=.+4.(1>.(10.R10.))))(2=.(<.$8.(18.(10.R?.))(16.R10.+18.))(20.(<.$19.(1:.(10.R?.))$1;.))))))))")
(* [comment removed for export] *).
  Proof.
    intros h LB dX G g lo m mo h1 LB1 dX1 m1 mo1 SP BASE MA H1 GS1 INV.
    dpose INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GR1 & _).
    dpose GR1 as (_ & _ & _ & _ & EA & _ & _ & _ & MA' & _).
    assert (OWN : md_own (g_A g) <> LHeap) by (apply (grp_static_own usegs MT m1 LB1 G g _ GR1 H1); cbn; auto).
    pose proof (mm_grp_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT SP 48 lo m mo h1 LB1 dX1 m1 mo1 (g_A g) 24 ROIMG IMGC BASE MA INV MA' OWN (or_introl GS1) EA ltac:(lia) ltac:(lia)) as B.
    ddestruct B as (B1 & B2 & B3 & B4 & B5). exact (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj EA OWN)))))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L20408246672.36L68544409441.36000001002SS". (* [comment removed for export] *)
  #[using="DIMG ROIMG IMGC"] Lemma sr_B_opnd : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PG,$8.Pg,$9.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph1,(4.$41.VL,VHI,)PLB1,(5.$6.)PdX1,$7.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.PSP,$8.P,(42.VL,R=.R<.R;.+5<?:8.R1.+30.R9.(23.$41.VL,VHI,R>.)R:.)P,(1?.$41.R9.R>.R=.)P,(<.$8.(=.R<.)+1.)P,(<.$8.(>.(11.R=.))+1.)P,(43.$41.VL,VHI,VMT,R12.R11.R10.R?.R>.+5<?:8.R5.+30.R=.R<.R;.R:.R9.R8.R7.R6.)(2=.(1?.$41.R8.R:.(11.R?.))(2=.(49.R9.(11.R?.))(2=.(4:.R9.(11.R?.)R>.(32.R6.+30.))(2=.(14.VL,R:.R>.(18.(11.R?.))+10.)(2=.P,(<.$19.(1:.(11.R?.))$1;.)(14.VL,R;.R?.(1<.(11.R10.))(1=.+4.(1>.(11.R10.))))(2=.(<.$8.(18.(11.R?.))(16.R10.+28.))(20.(<.$19.(1:.(11.R?.))$1;.))))))))")
(* [comment removed for export] *).
  Proof.
    intros h LB dX G g lo m mo h1 LB1 dX1 m1 mo1 SP BASE MA H1 GS1 INV.
    dpose INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GR1 & _).
    dpose GR1 as (_ & _ & _ & _ & _ & EB & _ & _ & _ & MB & _).
    assert (OWN : md_own (g_B g) <> LHeap) by (apply (grp_static_own usegs MT m1 LB1 G g _ GR1 H1); cbn; auto).
    pose proof (mm_grp_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT SP 48 lo m mo h1 LB1 dX1 m1 mo1 (g_B g) 40 ROIMG IMGC BASE MA INV MB OWN (or_introl GS1) EB ltac:(lia) ltac:(lia)) as B.
    ddestruct B as (B1 & B2 & B3 & B4 & B5). exact (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj EB OWN)))))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L10472342405.176L246904734.182  L27632495159.179L29010565666.139L29962826072.182L34229555104.5  L36242967909.156L3659161738.156 L36610342185.182L37502206226.182L43602991207.115L61274419438.182L64626040726.156L64626053780.115L818452692.5    L8356415152.139 00000100>00K00L00e01901O01^02202302G02T02a02l03903DFS3spv2j82J81rS3spv2j82J81rFS1L3spv2lo2j82J83SLO1r2r3S3spv2dX2lo3SXS4LOSPS1L3spv2lo2j82J83SLO1rS3spv1G2j82J81rS3spv2j82J81r3dX32r3FS1L3spv2lo2j82J83SLOS3spv2j82J81rS3spv2j82J81rS3spv2j82J8S3spv3SPA3SPBS3spv2j82J8". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HMM HADD HSUBA HCMP"] Lemma sr_mid : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2e,(0.&40.)Ps3e,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Plo,$8.Ph1,(4.$41.VL,VHI,)PLB1,(5.$6.)PdX1,$7.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.Pj8,(5.(0.&8.))P,(42.VL,R<.R;.R9.+5<?:8.(17.&40.R30.)+30.R7.(23.$41.VL,VHI,R=.)R8.)P,(1?.$41.R10.R=.R<.)P,(15.(12.(16.(18.R=.)+10.)R9.)(12.(17.&40.R32.)(18.R=.)))P,(<.$8.(=.R;.)+1.)P,(<.$8.(>.(?.R<.))+1.)P,(<.$8.(>.(11.R=.))+1.)P,(12.+1.(13.(?.R>.)))P,(38.$41.R16.)P,(1?.$41.R17.R14.R12.)P,(25.VL,R15.R14.R13.+5<?:8.(17.&40.R39.)R10.)P,(43.$41.VL,VHI,VMT,R17.R16.R15.R13.R12.+5<?:8.(17.&40.R3:.)+30.R11.R19.R18.R10.R?.R>.R=.R<.)P,(26.$41.R>.(16.(17.&40.R3;.)-30.)(44.R<.R35.R36.R37.R38.R3<.))P,(<.$45.(46.(0.&8.)R=.)#8.)P,(<.(0.&40.)R3;.(36.&40.(37.VL,)))P,(3:.VL,$4=.+8.)P,(12.R16.(32.(32.(17.&40.R3?.)$4>.)(33.VL,)))P,(<.$8.(35.(17.&40.R40.)+10.)=)(3;.$41.R13.(3<.$41.VL,VHI,VMT,R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R22.R21.R1>.R1=.R1<.R1:.R19.+5<?:8.R18.R20.R1?.)(3=.(3>.R32.(36.&40.(16.(17.&40.R41.)-30.))R40.R3?.R31.R30.R2?.(36.&40.(18.R1<.))(36.&40.R1:.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.(36.&40.(18.R1;.))(36.&40.(16.R1:.+8.))R3:.R39.R38.R37.R36.R35.R34.R33.R26.R25.R24.R23.)R22.(36.&40.+3:890.)R21.(3?.(0.&40.))R14.(40.$41.)))")
(* [comment removed for export] *).
  Proof.
    intros until j8; intros BASE MA SXS GH1 GPS GBS PV MI0 MXA EXT INV FR J8 TP CA SLO SPA.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB. unfold ECP_SW_RHS_STACK in SLO.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    dpose INV as (HH1 & MA1 & OUT1 & _). pose proof OUT1 as (EA1 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    ddestruct (mm_self_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 48 lo m mo h1 LB1 dX1 m1 mo1 BASE MA INV) as (SXX & OXX & CRX & CRXL).
    ddestruct (mm_ext_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 48 lo m mo h1 LB1 dX1 m1 mo1 dA ROIMG BASE MA INV MI0 MXA EXT) as (MEA & SXA & OXA & CRA & CRAL).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    eapply (mm_call_mulmod usegs L HI DIMG) with (FRC := sr_frame j8 s3e s2e s1e s0e rae);
      [exact HMM| exact BASE| exact MA| exact GH1| exact GPS| exact INV| reflexivity| exact FR| lia| cbn; clear - SXS LOSP; lia
      | exact MA1| exact MEA| exact SXX| exact SXA| exact SXA| exact OXX| exact OXA| exact CRX| exact CRXL| exact CRA| exact CRAL
      | unfold ECP_MUL_MOD_STACK; lia| exact HLS| clear - SPA SPB LOSP; lia| exact TP| exact CA| reflexivity| first [reflexivity| rewrite EA1; reflexivity]| first [reflexivity| rewrite EA1; reflexivity]| reflexivity|].
    intros m2 mo2 h2 LB2 dX2 r ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 FR2 RR _ Hr2.
    replace (ret_pc (Z_to_bv 64 0x3a8a4)) with (Z_to_bv 64 0x3a8a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    dpose INV2 as (HH2 & MA2 & OUT2 & _). pose proof OUT2 as (EA2 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    zstep. if_cases K0; zify_cond K0; [eapply sr_exit; [exact BASE| exact MA| exact INV2| exact FR2| exact J8| exact Hr2]|].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    ddestruct (mm_self_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 48 lo m mo h2 LB2 dX2 m2 mo2 BASE MA INV2) as (SXX2 & OXX2 & CRX2 & CRXL2).
    destruct (sr_B_opnd h LB dX G g lo m mo h2 LB2 dX2 m2 mo2 _ BASE MA GH1 GBS INV2) as (MB2 & SXB & OXB & CRB & CRBL & EB & BOWN).
    eapply (mm_call_binop usegs L HI DIMG) with (FRC := sr_frame j8 s3e s2e s1e s0e rae);
      [exact HADD| intros ? ? ? ? ? ? [_ KP]; exact KP| exact BASE| exact MA| exact INV2| reflexivity| exact FR2| lia| cbn; clear - SXS LOSP; lia
      | exact MA2| exact MB2| exact SXX2| exact SXB| exact SXB| exact OXX2| exact OXB| exact CRX2| exact CRXL2| exact CRB| exact CRBL
      | lia| exact HLS| clear - SPA SPB LOSP; lia| exact TP| exact CA| first [reflexivity| rewrite EA2, EA1; reflexivity]| first [reflexivity| rewrite EA2; reflexivity]| rewrite EB; apply f_equal; lia|].
    intros m3 mo3 h3 LB3 dX3 r3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV3 FR3 RR3 _.
    replace (ret_pc (Z_to_bv 64 0x3a8b8)) with (Z_to_bv 64 0x3a8b8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof INV3 as (HH3 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    zstep. if_cases K1; zify_cond K1; [eapply sr_exit; [exact BASE| exact MA| exact INV3| exact FR3| exact J8| first [lia| ddestruct RR3 as [[(Er & _)|[Er|[Er _]]] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia| ddestruct RR3 as [[(Er & _)|Er] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia]]|].
    zstep.
    eapply (sr_loop2 (S (Z.to_nat (mpd_val dX3)))) with (dX1 := dX3); [lia| exact BASE| exact MA| exact SXS| exact GH1| exact GPS| exact PV| exact INV3| exact FR3| exact J8| exact TP| exact CA| unfold ECP_SW_RHS_STACK; lia| exact SPA].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L11710712414.163L13854151595.132L15320267806.163L16075584458.126L21186064871.137L246904734.163  L29010566049.156L34229555104.5  L45914717502.8  L59213849104.160L59308628304.161L59353370052.164L61274419438.163L63219124928.134L64626056980.137L659213063.80   L818452692.5    00000F00\00]00^01=01S01T01h02C02Y03203V03l04K04a07E07RS1n3spv3dX12j84MEAS2J8S1n3spv3dX12j84MEAS2J8FFS1L1n3spv2lo3dX12j84MEAS2J83SLOS1n3spv3dX12j84MEAS2J8FS3spv2dX2lo3SXS4LOSPS1n1g3dX14MEAS2PV2GE3dX22V2S1n3spv3dX12j84MEAS2J8S1n3spv3dX12j84MEAS2J82K1S1n3spv1g3dX12j84MEAS2PV2J83SPB2GE1rS1n3spv3dX12j84MEAS2J8S1n3spv1g3dX12j84MEAS2J83SPB2K0S1n3spv3dX12j84MEAS2J8S1L2HI2MT3rae3spv2gp2tp3s0e3s1e3s2e3s3e2s42s52s62s72s82s93s103s113ra02t02t12t22a02a12a22a32a42a52a62a72t32t42t52t61F2fc1m2mo1h2LB2dX2dA1G1g2lo3dX12m13mo12j84MEAS2J8S3spv3SPA3SPB". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HMM HADD HSUBA HCMP"] Lemma sr_loop1 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Pn,$45.Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2e,(0.&40.)Ps3e,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Plo,$8.Ph1,(4.$41.VL,VHI,)PLB1,(5.$6.)PdX1,$7.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.Pj8,(5.(0.&8.))P,(4;.(4<.(13.R4.))R32.)P,(42.VL,R=.R<.R:.+5<?:8.(17.&40.R31.)+30.R8.(23.$41.VL,VHI,R>.)R9.)P,(1?.$41.R11.R>.R=.)P,(15.(12.(16.(18.R>.)+10.)R:.)(12.(17.&40.R33.)(18.R>.)))P,(<.$8.(=.R<.)+1.)P,(<.$8.(>.(?.R=.))+1.)P,(<.$8.(>.(11.R>.))+1.)P,(12.+1.(13.(?.R?.)))P,(38.$41.R17.)P,(1?.$41.R18.R15.R13.)P,(25.VL,R16.R15.R14.+5<?:8.(17.&40.R3:.)R11.)P,(43.$41.VL,VHI,VMT,R18.R17.R16.R14.R13.+5<?:8.(17.&40.R3;.)+30.R12.R1:.R19.R11.R10.R?.R>.R=.)P,(26.$41.R?.(16.(17.&40.R3<.)-30.)(44.R=.R36.R37.R38.R39.R3=.))P,(<.$45.(46.(0.&8.)R>.)#8.)P,(<.(0.&40.)R3<.(36.&40.(37.VL,)))P,(3:.VL,$4=.+8.)P,(12.R17.(32.(32.(17.&40.R40.)$4>.)(33.VL,)))P,(<.$8.(35.(17.&40.R41.)+10.)=)(3;.$41.R14.(3<.$41.VL,VHI,VMT,R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R23.R22.R1?.R1>.R1=.R1;.R1:.+5<?:8.R19.R21.R20.)(3=.(3>.R33.(36.&40.(16.(17.&40.R42.)-30.))R41.R40.R32.R31.R30.(36.&40.(18.R1=.))(36.&40.R1;.)R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(36.&40.(18.R1<.))(36.&40.(16.R1;.+8.))R3;.R3:.R39.R38.R37.R36.R35.R34.R27.R26.R25.R24.)R23.(36.&40.+3:818.)R22.(3?.(0.&40.))R15.(40.$41.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until j8; intros MEAS BASE MA SXS GH1 GPS GBS PV MI0 MXA EXT INV FR J8 TP CA SLO SPA; [lia|].
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof SLO as SLO0. unfold ECP_SW_RHS_STACK in SLO.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    destruct (sr_P_opnd h LB dX G g lo m mo h1 LB1 dX1 m1 mo1 _ BASE MA GH1 GPS INV) as (MP1 & SXP & OXP & CRP & CRPL & EP & POWN).
    dpose INV as (HH1 & MA1 & OUT1 & _). pose proof OUT1 as (EA1 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    pose proof MA1 as [_ SG1].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply (mm_call_cmp usegs L HI); [exact HCMP| exact INV| exact MP1| intros O; exfalso; exact (POWN O)| first [reflexivity| rewrite EA1; reflexivity]| rewrite EP; reflexivity|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'. replace (ret_pc (Z_to_bv 64 0x3a824)) with (Z_to_bv 64 0x3a824) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      eapply sr_mid; [exact BASE| exact MA| exact SXS| exact GH1| exact GPS| exact GBS| exact PV| exact MI0| exact MXA| exact EXT| exact INV| exact FR| exact J8| exact TP| exact CA| exact SLO0| exact SPA].
    - assert (GE : mpd_val (g_P g) <= mpd_val dX1) by (pose proof (Z.sgn_spec (mpd_val dX1 - mpd_val (g_P g))); lia).
      clear K0. zstep. zstep. zstep. zstep.
      ddestruct (mm_self_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 48 lo m mo h1 LB1 dX1 m1 mo1 BASE MA INV) as (SXX & OXX & CRX & CRXL).
      eapply (mm_call_binop usegs L HI DIMG) with (FRC := sr_frame j8 s3e s2e s1e s0e rae);
        [exact HSUBA| intros ? ? ? ? ? ? [_ KP]; exact KP| exact BASE| exact MA| exact INV| reflexivity| exact FR| lia| cbn; clear - SXS LOSP; lia
        | exact MA1| exact MP1| exact SXX| exact SXP| exact SXP| exact OXX| exact OXP| exact CRX| exact CRXL| exact CRP| exact CRPL
        | lia| exact HLS| clear - SPA SPB LOSP; lia| exact TP| exact CA| first [reflexivity| rewrite EA1; reflexivity]| first [reflexivity| rewrite EA1; reflexivity]| rewrite EP; reflexivity|].
      intros m2 mo2 h2 LB2 dX2 r ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 FR2 RR _.
      replace (ret_pc (Z_to_bv 64 0x3a838)) with (Z_to_bv 64 0x3a838) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof INV2 as (HH2 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      zstep. if_cases K1; zify_cond K1.
      + ddestruct RR as [[(_ & V2 & S2)|[Er|[Er _]]] _]; [| exfalso; subst r; cbv in K1; lia| exfalso; subst r; cbv in K1; lia].
        destruct (mpd_val_pos_abs dX1 SG1 ltac:(lia)) as [AX1 _]. pose proof (mpd_val_sg1 _ GPS) as VP. rewrite AX1, <- VP in V2.
        eapply IH with (dX1 := dX2) (h1 := h2) (LB1 := LB2) (j8 := j8); [clear - MEAS V2 GE PV; lia| exact BASE| exact MA| exact SXS| exact GH1| exact GPS| exact GBS| exact PV| exact MI0| exact MXA| exact EXT| exact INV2| exact FR2| exact J8| exact TP| exact CA| exact SLO0| exact SPA].
      + zstep. eapply sr_exit; [exact BASE| exact MA| exact INV2| exact FR2| exact J8| first [lia| ddestruct RR as [[(Er & _)|[Er|[Er _]]] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia| ddestruct RR as [[(Er & _)|Er] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L10600775827.119L15320267935.178L16075584073.136L17276979114.119L17311541139.119L246904607.178  L27757627056.136L29010565920.172L31270539015.80 L34229555104.5  L36240853465.152L50052061159.144L58861535760.175L59308628179.1  L59308628433.176L61274419311.178L61482332611.119L62303761365.8  L64628153130.152L64636506271.119L818452692.5    00000F00G00H00o01E01[02102204V04j05I06f07<07@07Y07o08E08a09709M09ZS1n3spv3dX12j84MEAS2J8FFS1L3HLS1n3spv2lo3dX12j84MEAS2J83SLO3SPBS1n3spv3dX12j84MEAS2J8S1n3spv3dX12j84MEAS2J8S1n3spv3dX12j84MEAS2J8FS1L2HI2MT3rae3spv2gp2tp3s0e3s1e3s2e3s3e2s42s52s62s72s82s93s103s113ra02t02t12t22a02a12a22a32a42a52a62a72t32t42t52t61F2fc1m2mo1h2LB2dX2dA1G1g2lo3dX12m13mo12j84MEAS2J8S3spv2dX2lo3SXS4LOSPS1L1n3spv2lo3dX12j84MEAS2J83SLOS1L3HLS4DIMG4IMGC1n3spv2dX1G2lo3dX12j84MEAS3SXS2J83SLO3SPB2GX3MC23MCX3MCG3ACL3DHI2SX2GS2K12H0S1n3spv3dX12j84MEAS2J8S2K0S1n3spv3dX12j84MEAS2J82K2S1n3spv3dX12j84MEAS2J8S1n3spv3dX12j84MEAS2J8S1n1g3dX14MEAS2PV3NEG3dX32V3S1n3spv3dX12j84MEAS2J8S1n3spv3dX12j84MEAS2J8S3spv3SPA3SPB". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HMM HADD HSUBA HCMP HCMPI"] Lemma sr_loopS : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Pn,$45.Prae,(0.&40.)Pspv,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Ps0e,(0.&40.)Ps1e,(0.&40.)Ps2e,(0.&40.)Ps3e,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pra0,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PdA,$7.PG,$8.Pg,$9.Plo,$8.Ph1,(4.$41.VL,VHI,)PLB1,(5.$6.)PdX1,$7.Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3.Pj8,(5.(0.&8.))P,(4;.(4<.(47.(13.R4.)))R32.)P,(42.VL,R=.R<.R:.+5<?:8.(17.&40.R31.)+30.R8.(23.$41.VL,VHI,R>.)R9.)P,(1?.$41.R11.R>.R=.)P,(15.(12.(16.(18.R>.)+10.)R:.)(12.(17.&40.R33.)(18.R>.)))P,(<.$8.(=.R<.)+1.)P,(<.$8.(>.(?.R=.))+1.)P,(<.$8.(>.(11.R>.))+1.)P,(12.+1.(13.(?.R?.)))P,(38.$41.R17.)P,(1?.$41.R18.R15.R13.)P,(25.VL,R16.R15.R14.+5<?:8.(17.&40.R3:.)R11.)P,(43.$41.VL,VHI,VMT,R18.R17.R16.R14.R13.+5<?:8.(17.&40.R3;.)+30.R12.R1:.R19.R11.R10.R?.R>.R=.)P,(26.$41.R?.(16.(17.&40.R3<.)-30.)(44.R=.R36.R37.R38.R39.R3=.))P,(<.$45.(46.(0.&8.)R>.)#8.)P,(<.(0.&40.)R3<.(36.&40.(37.VL,)))P,(3:.VL,$4=.+8.)P,(12.R17.(32.(32.(17.&40.R40.)$4>.)(33.VL,)))P,(<.$8.(35.(17.&40.R41.)+10.)=)(3;.$41.R14.(3<.$41.VL,VHI,VMT,R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R23.R22.R1?.R1>.R1=.R1;.R1:.+5<?:8.R19.R21.R20.)(3=.(3>.R33.(36.&40.(16.(17.&40.R42.)-30.))R41.R40.R32.R31.R30.(36.&40.(18.R1=.))(36.&40.R1;.)R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(36.&40.(18.R1<.))(36.&40.(16.R1;.+8.))R3;.R3:.R39.R38.R37.R36.R35.R34.R27.R26.R25.R24.)R23.(36.&40.+3:860.)R22.(3?.(0.&40.))R15.(40.$41.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until j8; intros MEAS BASE MA SXS GH1 GPS GBS PV MI0 MXA EXT INV FR J8 TP CA SLO SPA; [lia|].
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 spv) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof SLO as SLO0. unfold ECP_SW_RHS_STACK in SLO.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    destruct (sr_P_opnd h LB dX G g lo m mo h1 LB1 dX1 m1 mo1 _ BASE MA GH1 GPS INV) as (MP1 & SXP & OXP & CRP & CRPL & EP & POWN).
    dpose INV as (HH1 & MA1 & OUT1 & _). pose proof OUT1 as (EA1 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    pose proof MA1 as [(CH1 & _) SG1]. rewrite EA1 in CH1. unfold mpi_cells in CH1.
    (* [comment removed for export] *)
    destruct SG1 as [E|E]; rewrite E in CH1.
    { zstep. rewrite (sx16_small 1) by lia. zstep. if_cases K0; zify_cond K0; [| exfalso; clear - K0; lia].
      eapply sr_mid; [exact BASE| exact MA| exact SXS| exact GH1| exact GPS| exact GBS| exact PV| exact MI0| exact MXA| exact EXT| exact INV| exact FR| exact J8| exact TP| exact CA| exact SLO0| exact SPA]. }
    zstep. rewrite (sx16_small (-1)) by lia. zstep. if_cases K0; zify_cond K0; [exfalso; clear - K0; lia|]. clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply (mm_call_cmpint usegs L HI DIMG) with (FRC := sr_frame j8 s3e s2e s1e s0e rae) (z := 0);
      [exact HCMPI| exact BASE| exact MA| exact INV| reflexivity| exact FR| lia| cbn; clear - SXS LOSP; lia| lia| lia| clear - SPA SPB LOSP; lia| first [reflexivity| rewrite EA1; reflexivity]| reflexivity|].
    intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 FR2.
    replace (ret_pc (Z_to_bv 64 0x3a874)) with (Z_to_bv 64 0x3a874) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    dpose INV2 as (HH2 & MA2 & OUT2 & _). pose proof OUT2 as (EA2 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *) eapply sr_mid; [exact BASE| exact MA| exact SXS| exact GH1| exact GPS| exact GBS| exact PV| exact MI0| exact MXA| exact EXT| exact INV2| exact FR2| exact J8| exact TP| exact CA| exact SLO0| exact SPA]. }
    assert (NEG : mpd_val dX1 < 0).
    { pose proof (Z.sgn_spec (mpd_val dX1 - 0)). unfold mpd_val in *. rewrite E in *. pose proof (limbs_val_nonneg (md_limbs dX1)). lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    ddestruct (mm_self_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned spv) 48 lo m mo h1 LB1 dX1 m2 mo1 BASE MA INV2) as (SXX & OXX & CRX & CRXL).
    destruct (sr_P_opnd h LB dX G g lo m mo h1 LB1 dX1 m2 mo1 _ BASE MA GH1 GPS INV2) as (MP2 & SXP2 & OXP2 & CRP2 & CRPL2 & _ & _).
    eapply (mm_call_binop usegs L HI DIMG) with (FRC := sr_frame j8 s3e s2e s1e s0e rae);
      [exact HADD| intros ? ? ? ? ? ? [_ KP]; exact KP| exact BASE| exact MA| exact INV2| reflexivity| exact FR2| lia| cbn; clear - SXS LOSP; lia
      | exact MA2| exact MP2| exact SXX| exact SXP2| exact SXP2| exact OXX| exact OXP2| exact CRX| exact CRXL| exact CRP2| exact CRPL2
      | lia| exact HLS| clear - SPA SPB LOSP; lia| exact TP| exact CA| first [reflexivity| rewrite EA1; reflexivity]| first [reflexivity| rewrite EA1; reflexivity]| rewrite EP; reflexivity|].
    intros m3 mo3 h3 LB3 dX3 r ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV3 FR3 RR _.
    replace (ret_pc (Z_to_bv 64 0x3a888)) with (Z_to_bv 64 0x3a888) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof INV3 as (HH3 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    zstep. if_cases K2; zify_cond K2.
    - ddestruct RR as [[(_ & V3)|Er] _]; [| exfalso; subst r; cbv in K2; lia].
      eapply IH with (dX1 := dX3) (h1 := h3) (LB1 := LB3) (j8 := j8); [clear - MEAS V3 NEG PV; lia| exact BASE| exact MA| exact SXS| exact GH1| exact GPS| exact GBS| exact PV| exact MI0| exact MXA| exact EXT| exact INV3| exact FR3| exact J8| exact TP| exact CA| exact SLO0| exact SPA].
    - zstep. eapply sr_exit; [exact BASE| exact MA| exact INV3| exact FR3| exact J8| first [lia| ddestruct RR as [[(Er & _)|[Er|[Er _]]] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia| ddestruct RR as [[(Er & _)|Er] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L22706553362.62L27823803230.60L30119711213.60L3126147364.60 L54391891673.63L61768502295.62L61770805803.65L61772695821.6000000U01[02?02U03i05105L06RS1L4DIMG4IMGC2lo2SP3FRM3ACL4LOSP1a2HaS1L4DIMG4IMGC2dX1G2lo2SP3FRM3SXS2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GSS1L4DIMG4IMGC2lo2SP3FRM3MC23ACL4LOSPS1L2lo2SP3FRM3ACL4LOSPS1L2HI4DIMG4IMGC1h2dX1G2lo2SP3FRM3SXS2GX3MC23MCX3MCG3ACL3FR04LOSP3SPT3DHI2SX2GS1a2NOS1L4DIMG4IMGC2dX1G2lo2SP3FRM3SXS2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS1HS1L2lo2SP3FRM3ACL4LOSP1d2D4S1L4DIMG4IMGC2dX1G2lo2SP3FRM3SXS2GX3MC23MCX3MCG3ACL3FR04LOSP3DHI2SX2GS". (* [comment removed for export] *)
  #[using="DIMG IMGC"] Lemma sr_inv0 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_sw_rhs ()) "Ph,(4.$41.VL,VHI,)PLB,(5.$6.)PdX,$7.PG,$8.Pg,$9.Plo,$8.Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Pm1,P,(0.&40.)(2.(0.&8.))PSP,$8.PFRM,$8.Pcnt,(0.&40.)P,(42.VL,R;.R:.R9.+5<?:8.R3.R2.R7.(23.$41.VL,VHI,R<.)R8.)P,(1?.$41.R7.R<.R;.)P,(:.$41.VL,VHI,R>.R=.R8.R7.)P,(;.$41.VMT,R9.R>.R<.R;.)P,(26.$41.R:.+5<?:8.(27.$28.(29.R5.)(2:.$28.)))P,(39.$41.VL,R;.)P,(38.$41.R<.)P,(38.$41.R;.)P,(4?.(27.(50.$8.$8.)(51.$8.$8.(32.R;.R:.)R;.)(2:.(50.$8.$8.)))R>.R<.)P,(52.$41.R?.R=.)P,(31.$41.R>.R11.(32.R=.R<.))P,P,(20.(<.$19.(1:.R15.)$24.))(15.(12.(16.(1<.R16.)(1=.+4.(1>.R16.)))R13.)(12.R?.(1<.R16.)))P,(15.(12.(16.(18.R16.)+10.)R13.)(12.R?.(18.R16.)))(43.$41.VL,VHI,VMT,R19.R18.R17.R16.R15.+5<?:8.R10.R?.R14.R13.R12.R19.R18.R17.R11.R12.)")
(* [comment removed for export] *).
  Proof.
    intros h LB dX G g lo m mo m1 SP FRM cnt BASE MA HH GR CNT SOK MI MI1 MU WM ST1 XSL SXS. pose proof alloc_ceiling_pos as ACP.
    dpose BASE as (XW & NST & XIN & GCR & GX & GXL & MC1 & MC2 & MCS & MCX & MCG & H1 & ACL & FR0 & LOSP & SPT & DHI & SX & GS & SPU).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    unfold mm_inv. refine (conj _ (conj _ (conj (mpd_out_refl LB dX NST) (conj (fun b Hb => or_introl Hb) (conj eq_refl (conj (Z.le_refl _) (conj _ (conj _ (conj MI1 (conj (mo_frame_refl mo) (conj eq_refl (conj _ (conj _ ST1))))))))))))).
    - apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia.
    - eapply mpd_at_munch; [exact MA| exact NST| exact MU| exact WM| cbn; lia| intros O; pose proof (XSL ltac:(rewrite O; discriminate)); cbn; lia].
    - eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia].
    - eapply statics_ok_munch; [exact SOK| exact MU| intros a Ha _; cbn; lia].
    - eapply ecp_group_at_munch; [exact GR| exact MU| exact WM| exact MI| exact MI1| cbn; lia| intros d Hd HO; ddestruct (H1 d Hd HO) as (INd & _ & _); pose proof (proj1 (Forall_forall _ _) HBR _ INd) as (_ & _ & _ & D4 & _); cbn in D4; cbn; lia].
    - exists cnt. eapply rw_cells_transport; [exact CNT| exact MU| exact WM| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@L10355920871.153L10472342276.173L10472342276.180L11741095640.105L16075584073.144L18280395119.178L19354909044.106L19427582228.109L19427582228.110L2224152947.144 L22536217100.99 L246904607.178  L246904607.185  L25382082548.106L25618547375.112L25618547375.113L26924648792.106L2776191840.113 L2776194784.153 L2776227426.160 L27989871199.99 L28692136132.96 L29010565666.138L31378308326.108L31378308326.110L31392867444.106L34241923368.7  L34297840176.137L34429374090.160L34590493239.176L36242918757.160L36610342312.185L37414286068.106L37502206355.178L37502206355.185L41644202024.99 L43055137673.106L43442376564.105L43602991207.113L43654564952.106L43781838460.99 L44622288685.112L44622288685.113L48519070263.183L49698585326.112L49698585326.113L52616107219.101L59499841752.106L61274419311.178L61274419311.185L62143930712.153L63599554304.99 L65502165646.96 L7510805464.106 L808409670.7    00000G00H00I00M00N00c00g01\02Z02h02l03:03F03J03`04?04C04M04[04g05<05Q05R05V05Z05^06506?06M06[07007C07G07H07I07J07_07c08608:08B0970:50:A0:[0;>0<F0<J0<X0<d0=20=?0=C0=G0=TS1L2sp1g2lo3SLO2j82J81rFFS2spFS2sp1g2j82J81r3dX32r3S2spS1L3HLS4DIMG4IMGC2ra2sp2lo3MC23SLO3ACL2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2sp2s02lo3MC23SLO3ACL2HB5Ha_st5Hl_st2s12s22s3S2sp1G2j82J81rS2spS2sp1g2j82J81rS2sp2j82J81rS2spS2ra2sp2HB5Ha_st5Hl_stS2sp2s02HB5Ha_st5Hl_st2s12s22s3S2spS2sp2j82J8S2sp1g2j82J81rS2sp2j82J81rS1L3HLS2sp2lo3SLO3SPBS1L3HLS2sp2lo3SLO3SPBFS2spS2spS2spS1L3HLS2sp2dX2lo3SLO2SXS2sp2j82J8S2sp1G2j82J81rS2sp1g2j82J81rS1L2sp2lo3SLO2j82J81rS2sp2j82J81r3dX32r3S2spFFFS1L3HLS2sp2lo3SLO3SPBS2spS1L2sp2lo3SLO2j82J8S2spS2sp3SPBS1L3HLS4DIMG4IMGC2ra2sp2lo3SLO3ACL3SPB2HB5Ha_st5Hl_stS1L3HLS4DIMG4IMGC2sp2s02lo3SLO3ACL3SPB2HB5Ha_st5Hl_st2s12s22s3S2sp2j82J81rS2ra2sp3SPB2HB5Ha_st5Hl_stS2sp2s03SPB2HB5Ha_st5Hl_st2s12s22s3S1L3HLS4DIMG4IMGC2sp2dX1G2lo2GS2GX3MC23MCX3MCG3SLO3ACL3DHI3SPB2SX1a2Ha1CS2spS2sp1g2j82J81rS2sp2j82J81rS2sp1g2j82J81rS2sp2dX2lo2SXS2spS2spS2sp4SPA03SPB". (* [comment removed for export] *)
  #[using="HLS DIMG ROIMG IMGC HMM HADD HSUBA HSUBI HCMP HCMPI"] Theorem U_ecp_sw_rhs_spec : ecp_sw_rhs_stmt usegs L HI MT U_ECP_SW_RHS U_MEMSET_FUNC U_MUL_COUNT ECP_SW_RHS_STACK.
  Proof.
    unfold ecp_sw_rhs_stmt, U_ECP_SW_RHS. intros until lo.
    intros HH GR H1 GPS GAS GBS PV GCR0 GS GX GXL MA NST XW XSL MXA EXT CNT MC1 MC2 MCS MCX MCG ST SLO ACL HTOP SPA0 DHI TP MI SOK CA -> -> ->.
    pose proof alloc_ceiling_pos as ACP. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof SLO as SLO0. unfold ECP_SW_RHS_STACK in SLO.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    dpose XW as (XCW & XD & XP).
    pose proof (client_wrange_where2 L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as SX.
    assert (XIN : forall b, In b (mpd_blk dX) -> In b LB).
    { intros b Hb. unfold mpd_blk in Hb. pose proof MA as [(_ & _ & _ & _ & _ & HO) _]. destruct (md_own dX); try (destruct Hb; fail).
      destruct Hb as [<-|[]]. ddestruct HO as (_ & IN & _). exact IN. }
    assert (GCR : client_range L LB (bv_unsigned sp) G 192).
    { intros a Ha. destruct (GCR0 a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
    assert (BASE : mm_base L LB dX G U_MUL_COUNT (bv_unsigned sp) 48 lo (heap_top usegs L HI h) g).
    { unfold mm_base. repeat match goal with |- _ /\ _ => split end; try assumption; try lia. eapply (grp_X_ok_h1 usegs); [exact GR| exact H1]. }
    (* [comment removed for export] *)
    pose proof (lock MI) as MI00.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. pose proof (conj GR I) as GR0'. pose proof (conj CNT I) as CNT0. pose proof (conj SOK I) as SOK0. clear HH.
    carve_frame 48%nat ST. set (JJ := junk) in FR. clearbody JJ.
    do 10 zstep.
    destruct HH0 as [HH _]. destruct GR0' as [GR' _]. destruct CNT0 as [CNT' _]. destruct SOK0 as [SOK' _].
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (INV1 : mm_inv usegs L HI MT h LB dX G g U_MUL_COUNT (bv_unsigned sp) 48 lo m mo h LB dX m1 mo).
    { eapply sr_inv0; [exact BASE| exact MA| exact HH| exact GR'| exact CNT'| exact SOK'| exact (unlock _ MI00)| assumption| | exact WM| | exact XSL| exact SX].
      - replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. exact MU.
      - replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. assumption. }
    assert (J8 : length (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 JJ))))) = 8%nat).
    { pose proof (proj1 (proj1 FR)) as WF. cbn in WF. destruct WF as [WF _]. exact WF. }
    change (rw_cells usegs m1 (bv_unsigned sp + -48) (sr_frame (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 JJ))))) s3 s2 s1 s0 ra)) in FR.
    set (j8 := firstn 8 _) in FR, J8. clearbody j8.
    clear MU WM MK GR' CNT' SOK'. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (mm_ext_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned sp) 48 lo m mo h LB dX m1 mo dA ROIMG BASE MA INV1 (unlock _ MI00) MXA EXT) as (MEA & SXA & OXA & CRA & CRAL).
    (* [comment removed for export] *)
    zstep.
    eapply (mm_call_mulmod usegs L HI DIMG) with (FRC := sr_frame j8 s3 s2 s1 s0 ra);
      [exact HMM| exact BASE| exact MA| exact H1| exact GPS| exact INV1| reflexivity| exact FR| lia| cbn; clear - SX SLO HLS; lia
      | exact MEA| exact MEA| exact SXA| exact SXA| left; reflexivity| exact OXA| exact OXA| exact CRA| exact CRAL| exact CRA| exact CRAL
      | unfold ECP_MUL_MOD_STACK; lia| exact HLS| clear - SPA0 SPB SLO HLS; lia| exact TP| exact CA| reflexivity| reflexivity| reflexivity| reflexivity|].
    intros m2 mo2 h2 LB2 dX2 r ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV2 FR2 RR _ Hr2.
    replace (ret_pc (Z_to_bv 64 0x3a7d0)) with (Z_to_bv 64 0x3a7d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    dpose INV2 as (HH2 & MA2 & OUT2 & _ & _ & _ & _ & _ & _ & _ & _ & GR2 & _). pose proof OUT2 as (EA2 & _). clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    zstep. if_cases K0; zify_cond K0; [| eapply sr_exit; [exact BASE| exact MA| exact INV2| exact FR2| exact J8| exact Hr2]].
    (* [comment removed for export] *)
    dpose GR2 as (_ & _ & _ & _ & EGA & _ & _ & _ & MGA & _). dpose MGA as (CHA & _ & _ & _ & AHN & _). rewrite EGA in CHA. unfold mpi_cells in CHA.
    dpose MGA as (_ & _ & _ & _ & _ & AHO).
    pose proof GR2 as (GHD2 & GAL2 & _). pose proof (rw_cells_bound _ _ _ _ GHD2) as GB2. cbn [cells_size csize Nat.add] in GB2.
    first [pose proof MA as [(XCH & XAL & _) _] | pose proof MA as (XCH & XAL & _)].
    pose proof (rw_cells_bound _ _ _ _ XCH) as XB. cbn [cells_size csize Nat.add mpi_cells] in XB.
    zstep. zstep. if_cases KG; zify_cond KG; [exfalso; rewrite ?unsigned_lit in KG by lia; rewrite ?land_7_mod in KG; lia|].
    zstep. zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      ddestruct (mm_self_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned sp) 48 lo m mo h2 LB2 dX2 m2 mo2 BASE MA INV2) as (SXX & OXX & CRX & CRXL).
      eapply (mm_call_intop usegs L HI DIMG) with (FRC := sr_frame j8 s3 s2 s1 s0 ra) (b := 3);
        [exact HSUBI| intros ? ? ? ? ? ? [_ KP]; exact KP| exact BASE| exact MA| exact INV2| reflexivity| exact FR2| lia| cbn; clear - SX SLO HLS; lia
        | exact MA2| exact SXX| exact OXX| exact CRX| exact CRXL| lia
        | lia| exact HLS| clear - SPA0 SPB SLO HLS; lia| exact TP| exact CA| first [reflexivity| rewrite EA2; reflexivity]| first [reflexivity| rewrite EA2; reflexivity]| reflexivity|].
      intros m3 mo3 h3 LB3 dX3 r3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV3 FR3 RR3 _.
      replace (ret_pc (Z_to_bv 64 0x3a850)) with (Z_to_bv 64 0x3a850) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof INV3 as (HH3 & _). clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
      zstep. if_cases K2; zify_cond K2; [eapply sr_exit; [exact BASE| exact MA| exact INV3| exact FR3| exact J8| first [lia| ddestruct RR3 as [[(Er & _)|[Er|[Er _]]] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia| ddestruct RR3 as [[(Er & _)|Er] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia]]|].
      zstep. zstep. if_cases KX; zify_cond KX; [exfalso; rewrite ?unsigned_lit in KX by lia; rewrite ?land_7_mod in KX; lia|].
      zstep.
      eapply (sr_loopS (S (Z.to_nat (- mpd_val dX3)))) with (dX1 := dX3); [lia| exact BASE| exact MA| exact SX| exact H1| exact GPS| exact GBS| exact PV| exact (unlock _ MI00)| exact MXA| exact EXT| exact INV3| exact FR3| exact J8| exact TP| exact CA| exact SLO0| exact SPA0].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      ddestruct (mm_self_opnd usegs L HI DIMG MT h LB dX G g U_MUL_COUNT (bv_unsigned sp) 48 lo m mo h2 LB2 dX2 m2 mo2 BASE MA INV2) as (SXX & OXX & CRX & CRXL).
      destruct (sr_A_opnd h LB dX G g lo m mo h2 LB2 dX2 m2 mo2 _ BASE MA H1 GAS INV2) as (MA2' & SXA2 & OXA2 & CRA2 & CRAL2 & EA' & AOWN).
      eapply (mm_call_binop usegs L HI DIMG) with (FRC := sr_frame j8 s3 s2 s1 s0 ra);
        [exact HADD| intros ? ? ? ? ? ? [_ KP]; exact KP| exact BASE| exact MA| exact INV2| reflexivity| exact FR2| lia| cbn; clear - SX SLO HLS; lia
        | exact MA2| exact MA2'| exact SXX| exact SXA2| exact SXA2| exact OXX| exact OXA2| exact CRX| exact CRXL| exact CRA2| exact CRAL2
        | lia| exact HLS| clear - SPA0 SPB SLO HLS; lia| exact TP| exact CA| first [reflexivity| rewrite EA2; reflexivity]| first [reflexivity| rewrite EA2; reflexivity]| rewrite EA'; apply f_equal; lia|].
      intros m3 mo3 h3 LB3 dX3 r3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? INV3 FR3 RR3 _.
      replace (ret_pc (Z_to_bv 64 0x3a810)) with (Z_to_bv 64 0x3a810) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof INV3 as (HH3 & _). clear MK. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
      zstep. if_cases K2; zify_cond K2; [eapply sr_exit; [exact BASE| exact MA| exact INV3| exact FR3| exact J8| first [lia| ddestruct RR3 as [[(Er & _)|[Er|[Er _]]] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia| ddestruct RR3 as [[(Er & _)|Er] _]; rewrite Er; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_MPI_NEGATIVE_VALUE; lia]]|].
      zstep.
      eapply (sr_loop1 (S (Z.to_nat (mpd_val dX3)))) with (dX1 := dX3); [lia| exact BASE| exact MA| exact SX| exact H1| exact GPS| exact GBS| exact PV| exact (unlock _ MI00)| exact MXA| exact EXT| exact INV3| exact FR3| exact J8| exact TP| exact CA| exact SLO0| exact SPA0].
  all: match goal with |- ?g => idtac "MAINLEFT" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SR.
