(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_ecp_group_init U_mpi_cmp U_mpi_bitlen U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_C U_pk_ecparams_D U_pk_ecparams_E.
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
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_pk_ecparams_F () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_E.LINV"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_E.LSTATE"].



Section EP.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis CA_RSA0 : const_at L U_RSA_INFO 4.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (mo0 : Model) (h0 : HST usegs L HI) (LB : list blk)
            (PKA info C lo PAR LEN P BUF : Z) (tg pd : word) (bs : list byte)
            (idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ : word).
  Notation K := (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ).
  Hypothesis HH0 : HEAP usegs L HI h0 LB m0 mo0.
  Hypothesis HPKA0 : rw_cells usegs m0 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)].
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis NZP : 0 < PKA.
  Hypothesis EI : In info U_EC_INFOS.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis CWP : client_wrange L LB lo (heap_top usegs L HI h0) PKA 16.
  Hypothesis DPC : PKA + 16 <= C \/ C + 256 <= PKA.
  Hypothesis PKD : PKA + 16 <= hl_data_lo L \/ hl_data_hi L <= PKA.
  Hypothesis KP0 : ecp_keypair_at usegs U_MT m0 LB C K.
  Hypothesis INC : In (C, 256) LB.
  Hypothesis CD : C + 256 <= hl_data_lo L \/ hl_data_hi L <= C.
  Hypothesis HPAR0 : rw_cells usegs m0 PAR (buf_cells tg pd LEN P).
  Hypothesis ALR : PAR mod 8 = 0.
  Hypothesis NZR : 0 < PAR.
  Hypothesis DSR : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis RD : PAR + 24 <= hl_data_lo L \/ hl_data_hi L <= PAR.
  Hypothesis RC : PAR + 24 <= C \/ C + 256 <= PAR.
  Hypothesis HBS0 : bytes_at usegs m0 BUF bs.
  Hypothesis INB : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis BP : BUF <= P.
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis PL : P + LEN <= BUF + Z.of_nat (length bs).
  Hypothesis B63 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis IDS0 : ecp_ids_state usegs U_ECP_IDS_DONE U_ECP_IDS m0.
  Hypothesis SOK0 : statics_ok usegs L m0.
  Hypothesis CA : const_at L U_MEMSET_FUNC 8.
  Hypothesis CAT : const_at L U_OID_EC_GRP_TBL 440.
  Hypothesis CA_EC0 : forall e, In e U_EC_INFOS -> const_at L e 4.
  Hypothesis SLO : lo <= bv_unsigned sp - 688 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h0.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv usegs m0.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis SPR : bv_unsigned sp < 2^64.
  Hypothesis IDL : ecp_ids_lok L U_ECP_IDS_DONE U_ECP_IDS.
  (* [comment removed for export] *)
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis CAC : C + 256 <= alloc_ceiling.
  Hypothesis C0 : 0 < C.
  Hypothesis C16 : C mod 16 = 0.
  Hypothesis CIM : C + 256 <= hl_img_lo L \/ hl_img_hi L <= C.
  Hypothesis BAC : BUF + Z.of_nat (length bs) <= alloc_ceiling.
  Hypothesis BIM : BUF + Z.of_nat (length bs) <= hl_img_lo L \/ hl_img_hi L <= BUF.

  Notation XS := [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)].
  Notation X0 := [(C, C + ECP_GROUP_SIZE); (U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)].
  Notation POST := (pk_use_ecparams_post usegs L HI U_MT U_CA U_ONE U_ECP_IDS_DONE U_ECP_IDS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PKA info C K lo m0 mo0).
  Notation FRS mm := (rw_cells usegs mm (bv_unsigned sp + -104)
                        [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_F ()) "(0.(1.+1000.(2.VL,))(0.(1.=VC,)(0.(3.$4.(5.VC,+10.)=)(0.(6.(7.VC,+100.)(2.VL,))(0.(8.(6.(7.VC,+100.)(9.VL,))(6.(:.VL,)VC,))(0.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(2.VL,))(8.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(9.VL,))(6.(:.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2647750340.6  L2726914452.6  L52616404933.1000000D00X016S1L3PKA3PKD2I12I22I3S1L3PKA3PKD2I12I22I3S1L2HI2sp2h03PKA2lo3DSP1a2Ha1Q". (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_F ()) "Pm,P,(=.&40.)(>.(=.&8.))P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R1.)(18.$10.R2.VPKA,(12.$19.(1:.(1;.&40.Vinfo,))(12.$19.(1:.(1;.&40.VC,))(17.$19.))))")
(* [comment removed for export] *).
  Proof.
    intros m PX. eapply heap_presx_rw_cells; [exact PX| exact HPKA0| |]; cbn [cells_size csize Nat.add disjoint_from].
    - intros a Ha. destruct (CWP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exact Q].
    - ddestruct IDL as (I1 & I2 & I3 & _). clear -PKD I1 I2 I3. split; [lia| split; [lia| exact I]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  #[using="IDL"] Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 IDL). Qed.
  #[using="L IDL"] Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 IDL)). Qed.
  #[using="IDL"] Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 IDL))). Qed.
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_F ()) "Pa,$4.P,(8.(0.(6.$15.R1.)(1.R1.(7.$15.+1.)))(0.(6.$16.R1.)(1.R1.(7.$16.+38.))))(0.(1<.VL,R2.)(1=.(1>.VL,R2.)))")
(* [comment removed for export] *).
  Proof. exact (proj2 (proj2 (proj2 IDL))). Qed.
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.

  Notation G := (bv_unsigned sp + -504).
  Notation REF := (bv_unsigned sp + -296).
  Notation CTX := (ctx_now L HI mo0 h0 LB).
  Notation DS7 dN dP dA dB dX dY dZ := ([dN; dP; dA; dB; dX; dY; dZ] : list mpd) (only parsing).


  Notation LSTATE := (LSTATE sp gp tp F fc PKA).
  Notation LINV := (LINV L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB lo).
  Notation ctx_munch' := (ctx_munch L HI ra sp m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP DHI IDL).
  Notation tail_from_linv' := (tail_from_linv L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation iter_head' := (iter_head L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).

  (* [comment removed for export] *)
  #[using="Type"] Lemma ref_mpd : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_F ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.Pg3,$23.Pidj,$4.PdN,$24.PdP,$24.PdA,$24.PdB,$24.PdX,$24.PdY,$24.PdZ,$24.Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Pmj,(20.(=.&8.))Pl1,(20.(=.&8.))Pl2,(20.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)P,(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R15.R14.R13.R12.R11.R10.=R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)Pd,$24.P,(26.$24.R1.(27.R13.))(0.(28.$10.R16.R17.R2.)P,(3.$29.(2:.R2.)$2;.)(1.=(2<.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros until nb. (intros dd_H; ddestruct dd_H as (CX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG & _ & GL & _); intros d Hd).
    destruct CX as (HH & _). destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    assert (MD : mpdr_at usegs m LBi d).
    { ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & _).
      unfold grp_mpds, pt_mpds in Hd. cbn [app In] in Hd. decompose [or] Hd; subst; try assumption; contradiction. }
    split; [split; [exact MD| left; exact (gl_signs _ _ _ _ _ _ GL d Hd)]|].
    intros O. destruct (mpdr_blk_facts usegs L _ _ _ MD O HBR) as (_ & _ & P0 & _). exact P0.
  Qed.

  #[using="Type"] Lemma tmp_mpd : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_F ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.Pg3,$23.Pidg,$4.Prg,$4.PdN,$24.PdP,$24.PdA,$24.PdB,$24.PdX,$24.PdY,$24.PdZ,$24.Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Pmj,(20.(=.&8.))Pl1,(20.(=.&8.))Pl2,(20.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)P,(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)Pd,$24.P,(26.$24.R1.(12.$24.R11.(12.$24.R10.(12.$24.R?.(12.$24.R>.(12.$24.R=.(12.$24.R<.(12.$24.R;.(17.$24.)))))))))(0.(28.$10.R17.R18.R2.)P,(3.$29.(2:.R2.)$2;.)(1.=(2<.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros until nb. (intros dd_H; ddestruct dd_H as (CX & _ & TOK & _); intros d Hd). destruct CX as (HH & _). destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK Hd) as MD. split; [exact MD|].
    intros O. destruct (mpdr_blk_facts usegs L _ _ _ (proj1 MD) O HBR) as (_ & _ & P0 & _). exact P0.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L11930903853.1 L1886511516.1  L22473720065.1 L27945360799.12L30977400476.1 L352225630.8   L35276053645.14L36121744865.8 L50033622428.1 L51256173200.1400000400800<00Q00U01001O01i01m02HS2spS2spS2spS2sp1u1v1a1k2Ha2Q12Q2S2spS1L2sp2lo1H3DHI3ACL3SLO3HLSS1L3HLS2sp2lo3SLO3ACL1u1v2Q12Q2S1L3HLS2sp2lo3SLO3ACL1d2P4S2spS1L3HLS2sp2lo3SLO1u1v2Q12Q2". (* [comment removed for export] *)
  #[using="HLS PKA C PAR bs SLO ACL HTOP DHI IDL"] Lemma linv_frame : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_F ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))Pmo,$22.Pg3,$23.Pidg,$4.Prg,$4.PdN,$24.PdP,$24.PdA,$24.PdB,$24.PdX,$24.PdY,$24.PdZ,$24.Pscj,(20.(=.&8.))Pscj',(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Pmj,(20.(=.&8.))Pl1,(20.(=.&8.))Pl2,(20.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)PW,(20.$2=.)P,(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R19.R18.R17.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R8.R7.R6.R5.R4.R3.R2.)P,(2>.R2.R18.R17.)P,(2?.$10.R19.R18.)P,(30.$10.R19.)P,(31.(13.$4.$4.)Liv,(13.$4.$4.)(0.(6.(7.(11.&40.Vsp,)-200.)(32.$4.$4.R1.))(6.(33.$4.$4.R1.)(7.(11.&40.Vsp,)-1?8.)))R5.)P,(18.$10.R1;.(7.(11.&40.Vsp,)-200.)(12.$19.(34.#8.R>.)(17.$19.)))P,(35.$10.R1<.Vlo,(7.(11.&40.Vsp,)-200.))(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R20.R1?.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R10.R?.R>.R=.R<.R;.R:.R9.)")
(* [comment removed for export] *).
  Proof.
    intros until W. (intros dd_H; ddestruct dd_H as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & RT & HG & AP & GL & HIDS & FR0 & FRH & FRT & FRM & FR & ST); intros MU WM MI' HW FR0' ST').
    destruct CX as (HH & REST). destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _]. pose proof (proj1 (proj2 (proj2 REST))) as MI.
    assert (DW : forall a k, (bv_unsigned sp + -504 <= a \/ a + k <= bv_unsigned sp + -512) -> disjoint_from W a k).
    { intros a k Ha. clear -HW Ha. induction W as [|[u v] W IH]; cbn; [exact I|]. inversion HW as [|? ? [Q1 Q2] Q3]; subst. cbn in Q1, Q2.
      split; [lia| apply IH; exact Q3]. }
    destruct (ctx_munch' _ _ _ _ _ _ _ (conj HH REST) PX MU WM MI' ltac:(clear -HW SLO HLS ACL; induction W as [|[u v] W IH]; [constructor|]; inversion HW as [|? ? [Q1 Q2] Q3]; subst; cbn in Q1, Q2; constructor; [cbn; lia| apply IH; exact Q3])) as [CX' PX'].
    split; [exact CX'|]. split; [exact PX'|].
    split. { eapply (tmp_ok_munch usegs L); [exact TOK| exact MU| exact WM| exact MI| exact MI'| | exact HBR].
             clear -HW SLO HLS ACL. induction W as [|[u v] W IH]; [constructor|]; inversion HW as [|? ? [Q1 Q2] Q3]; subst; cbn in Q1, Q2; constructor; [cbn; lia| apply IH; exact Q3]. }
    split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|]. split; [exact RT|].
    split. { eapply (ecp_group_at_munch usegs); [exact HG| exact MU| exact WM| exact MI| exact MI'| apply DW; clear; lia|].
             intros d Hd O. ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & _).
             assert (MD : mpdr_at usegs m LBi d) by (unfold grp_mpds, pt_mpds in Hd; cbn [app In] in Hd; decompose [or] Hd; subst; try assumption; contradiction).
             destruct (mpdr_blk_facts usegs L _ _ _ MD O HBR) as (_ & _ & _ & P4 & _). apply DW. right. clear -P4 ACL SLO HLS. lia. }
    split; [exact AP|]. split; [exact GL|].
    split. { eapply bytes_at_transport; [exact HIDS| exact MU|]. apply DW. right. rewrite <- ids_bytes_u32s. cbn. generalize IL3 DHI ACL SLO HLS; clear; intros; lia. }
    split; [exact FR0'|].
    split; [eapply rw_cells_transport; [exact FRH| exact MU| exact WM| apply DW; left; clear; lia]|].
    split; [eapply rw_cells_transport; [exact FRT| exact MU| exact WM| apply DW; left; clear; lia]|].
    split; [eapply rw_cells_transport; [exact FRM| exact MU| exact WM| apply DW; left; clear; lia]|].
    split; [eapply rw_cells_transport; [exact FR| exact MU| exact WM| apply DW; left; clear; lia]| exact ST'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00f0@D11805467289.300D21175008748.303D44622288685.302D49698585326.302D49705053714.300D54831671062.302D54842242026.300L10251975069.1  L10837299463.1  L14429712647.1  L15504965379.292L16077671799.204L16077671799.221L16077671799.238L16077671799.255L16077671799.272L16077671799.289L18313572791.313L1886511516.1   L21185490716.295L2397676628.0   L24507271431.1  L2463497117.1   L25937495349.305L27105925383.1  L27197623219.172L30718654727.1  L32027975233.0  L36400461110.297L38796395825.246L41632399652.173L41632399781.172L42138844316.1  L43467180248.173L46038090503.1  L46987149575.1  L47290142471.1  L49260410162.229L50600009991.1  L53254869767.1  L55358598067.292L55358598067.313L61663432603.313L63109977398.319L63267834119.1  L65505944887.280L66272636120.173L66867980551.1  L7251498288.263 L7454461363.172 L7665549575.1   L8719708423.1   L882378613.2    L9674728726.212 00000G00H01N02802S03903P03T03X03\04004104204304404504604X04\04]04^04b04f05:05>05R05V05W05k06?06@06A06E06\06`06d06h07<07@07D07X07l08N08b08f09:09Q09U09i0:=0:A0:E0:K0:_S2ra2sp3PKA1C3PAR2bs2HBFS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C02b12HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR2b12HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR2HBS2ra2sp3PKA1C3PAR2bs2b12HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs2HBS2spS2spS2spS2ra2sp3PKA1C3PAR2bsFFFFFFS2ra2sp3PKA1C3PAR2bs4x1282PC5POST4S2spFSS2spS2spS2ra2sp3PKA1C3PAR2bsS2spS2ra2sp3PKA1C3PAR2bsS2spSS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsFFS2spS2ra2sp3PKA1C3PAR2bs2g3S2spS2spS2spS2ra2sp3PKA1C3PAR2bsS2spS2spS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs2b14PC115POST5S2ra2sp3PKA1C3PAR2bsS2spS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs2g3S2spS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2spS2spS1i2IBS2ra2sp3PKA1C3PAR2bs". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma cmp_chain : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_F ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.Pg3,$23.Pidj,$4.PdN,$24.PdP,$24.PdA,$24.PdB,$24.PdX,$24.PdY,$24.PdZ,$24.Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Pmj,(20.(=.&8.))Pl1,(20.(=.&8.))Pl2,(20.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)Pi,$4.Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R26.R25.R24.R23.R22.R21.=R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(0.(6.=R12.)(6.R12.+<.))P,Pm',P,(=.&40.)(>.(=.&8.))Pscj',(20.(=.&8.))Py1,(=.&40.)Py5,(=.&40.)Py6,(=.&40.)Py7,(=.&40.)Py10,(=.&40.)Py11,(=.&40.)Py12,(=.&40.)Py13,(=.&40.)Py14,(=.&40.)Py15,(=.&40.)Py16,(=.&40.)Py17,(=.&40.)Py28,(=.&40.)Py29,(=.&40.)Py30,(=.&40.)Py31,(=.&40.)P,(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R3:.R39.R12.R37.R36.R35.=R34.R33.R32.R31.R30.R2?.R2>.R11.R2<.R2;.R2:.R29.R28.R27.R26.)(36.$10.R38.(37.$10.VL,VHI,$38.$39.$3:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(3;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(3<.Vsp,Vgp,Vtp,VF,Vfc,VPKA,+29;50.R13.R26.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.))(36.$10.R26.(37.$10.VL,VHI,$38.$39.$3:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(3;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(3<.Vsp,Vgp,Vtp,VF,Vfc,VPKA,+29:;4.R27.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros LI IB NEXT.
    dpose LI as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & RT & HG & AP & GL & HIDS & FR0 & FRH & FRT & FRM & FR & ST).
    ddestruct CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    (* [comment removed for export] *)
    pose proof HG as HGc. ddestruct HGc as (_ & _ & _ & EgP & EgA & EgB & EgN & _ & _ & _ & (EgX & EgY & EgZ & _ & _ & _) & _ & HGT & _).
    unfold grp_tail_cells in HGT. replace (REF + 120) with (bv_unsigned sp + -176) in HGT by (clear; lia).
    pose proof FRT as FRTw. replace (G + 120) with (bv_unsigned sp + -384) in FRTw by (clear; lia).
    unfold U_pk_ecparams_E.LSTATE.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *) eapply NEXT. exact LI. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    { eapply NEXT. exact LI. }
    clear K1 K2.
    pose proof (tmp_mpd h LBi m mo g3 idj 0 dN dP dA dB dX dY dZ scj hj tj mj l1 l2 pb nb LI) as TM.
    pose proof (ref_mpd h LBi m mo g3 idj dN dP dA dB dX dY dZ scj hj tj mj l1 l2 pb nb LI) as RM.
    pose proof U_mpi_cmp_mpi_spec as SPC. unfold mpi_cmp_mpi_stmt, mpi_cmp_post, U_MPI_CMP_MPI in SPC.
    Ltac inlist := cbn; repeat (first [ left; reflexivity | right ]).
    pose proof (TM dP ltac:(inlist)) as TMP. pose proof (TM dA ltac:(inlist)) as TMA. pose proof (TM dB ltac:(inlist)) as TMB.
    pose proof (TM dN ltac:(inlist)) as TMN. pose proof (TM dX ltac:(inlist)) as TMX. pose proof (TM dY ltac:(inlist)) as TMY.
    pose proof (TM dZ ltac:(inlist)) as TMZ.
    pose proof (RM (g_P g3) ltac:(inlist)) as RMP. pose proof (RM (g_A g3) ltac:(inlist)) as RMA. pose proof (RM (g_B g3) ltac:(inlist)) as RMB.
    pose proof (RM (g_N g3) ltac:(inlist)) as RMN. pose proof (RM (pt_X (g_G g3)) ltac:(inlist)) as RMX.
    pose proof (RM (pt_Y (g_G g3)) ltac:(inlist)) as RMY. pose proof (RM (pt_Z (g_G g3)) ltac:(inlist)) as RMZ.
    clear TM RM.
    Ltac cmp_one SPC MI LI NEXT dT dR ET ER TMd RMd :=
      zstep; zstep; zstep;
      acallp (eapply SPC with (dX := dT) (dY := dR);
              [ exact (proj1 TMd) | exact (proj1 RMd) | exact (proj2 TMd) | exact (proj2 RMd) | exact MI
              | rewrite ET; f_equal; clear; lia | rewrite ER; f_equal; clear; lia ]);
      zstep; let K := fresh "K" in if_cases K; zify_cond K; [ eapply NEXT; exact LI | clear K ].
    cmp_one SPC MI LI NEXT dP (g_P g3) EP EgP TMP RMP.
    cmp_one SPC MI LI NEXT dA (g_A g3) EA EgA TMA RMA.
    cmp_one SPC MI LI NEXT dB (g_B g3) EB EgB TMB RMB.
    cmp_one SPC MI LI NEXT dN (g_N g3) EN EgN TMN RMN.
    cmp_one SPC MI LI NEXT dX (pt_X (g_G g3)) EX EgX TMX RMX.
    cmp_one SPC MI LI NEXT dZ (pt_Z (g_G g3)) EZ EgZ TMZ RMZ.
    clear SPC TMP TMA TMB TMN TMX TMZ RMP RMA RMB RMN RMX RMZ.
    (* [comment removed for export] *)
    pose proof U_mpi_get_bit_spec as SPB. unfold mpi_get_bit_stmt, mpi_query_post, U_MPI_GET_BIT in SPB.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep.
    acallx (eapply SPB with (dX := dY) (pos := 0);
            [ exact (proj1 TMY) | exact (proj2 TMY) | exact MI | clear; lia | rewrite EY; f_equal; clear; lia | reflexivity ]).
    try clear PC PC1 PC3 PC5 PC7 PC9.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename b into b1 end.
    match goal with W : wmono usegs m m4 |- _ => rename W into WM4 end. rename MU into MU4.
    match goal with M : mem_inv usegs m4 |- _ => rename M into MI4 end.
    pose proof (linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI MU4 WM4 MI4 (Forall_nil _) FR0 ST) as LI4.
    clear MU4 WM4.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp + -512, bv_unsigned sp + -504)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with M : mem_inv usegs m5 |- _ => rename M into MI5 end.
    assert (FR0b : rw_cells usegs m5 (bv_unsigned sp + -512) [CB 8 (le8 (Z_to_bv 64 b1))]).
    { eapply rw_cells_reshape; [exact FR0| cbn; split; [reflexivity| exact I]| reflexivity]. }
    pose proof (linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI4 MU WM MI5
                  ltac:(repeat constructor; cbn; clear; lia) FR0b ST) as LI5.
    clear LI4 MU WM FR0b.
    (* [comment removed for export] *)
    pose proof (ref_mpd h LBi m5 mo g3 idj dN dP dA dB dX dY dZ _ hj tj mj l1 l2 pb nb LI5 (pt_Y (g_G g3)) ltac:(inlist)) as RMY5.
    pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    zstep. zstep. zstep.
    acallx (eapply SPB with (dX := pt_Y (g_G g3)) (pos := 0);
            [ exact (proj1 RMY5) | exact (proj2 RMY5) | exact MI5 | clear; lia | rewrite EgY; f_equal; clear; lia | reflexivity ]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with W : wmono usegs m5 m6 |- _ => rename W into WM6 end. rename MU into MU6.
    match goal with M : mem_inv usegs m6 |- _ => rename M into MI6 end.
    assert (FR0b : rw_cells usegs m6 (bv_unsigned sp + -512) [CB 8 (le8 (Z_to_bv 64 b1))]).
    { eapply rw_cells_reshape; [exact FR0| cbn; split; [reflexivity| exact I]| reflexivity]. }
    pose proof (linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LI5 MU6 WM6 MI6 (Forall_nil _) FR0b ST) as LI6.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K3; zify_cond K3.
    2:{ eapply NEXT. exact LI6. }
    (* [comment removed for export] *)
    zstep. zstep.
    eapply tail_from_linv'; [exact LI6| clear -IB; lia| clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EP.
