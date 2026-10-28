(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_ecp_group_init U_mpi_cmp U_mpi_bitlen U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_C U_pk_ecparams_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_ecparams_E () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_B.ctx_now"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_load.gl_result"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_D.IDWS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "EP.LINV"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "EP.LSTATE"].



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
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_E ()) "(0.(1.+1000.(2.VL,))(0.(1.=VC,)(0.(3.$4.(5.VC,+10.)=)(0.(6.(7.VC,+100.)(2.VL,))(0.(8.(6.(7.VC,+100.)(9.VL,))(6.(:.VL,)VC,))(0.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(2.VL,))(8.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(9.VL,))(6.(:.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_E ()) "Pm,P,(=.&40.)(>.(=.&8.))P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R1.)(18.$10.R2.VPKA,(12.$19.(1:.(1;.&40.Vinfo,))(12.$19.(1:.(1;.&40.VC,))(17.$19.))))")
(* [comment removed for export] *).
  Proof.
    intros m PX. eapply heap_presx_rw_cells; [exact PX| exact HPKA0| |]; cbn [cells_size csize Nat.add disjoint_from].
    - intros a Ha. destruct (CWP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exact Q].
    - ddestruct IDL as (I1 & I2 & I3 & _). clear -PKD I1 I2 I3. split; [lia| split; [lia| exact I]].
  Qed.


  (* [comment removed for export] *)
  #[using="IDL"] Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 IDL). Qed.
  #[using="L IDL"] Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 IDL)). Qed.
  #[using="IDL"] Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 IDL))). Qed.
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_E ()) "Pa,$4.P,(8.(0.(6.$15.R1.)(1.R1.(7.$15.+1.)))(0.(6.$16.R1.)(1.R1.(7.$16.+38.))))(0.(1<.VL,R2.)(1=.(1>.VL,R2.)))")
(* [comment removed for export] *).
  Proof. exact (proj2 (proj2 (proj2 IDL))). Qed.
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.

  Notation G := (bv_unsigned sp + -504).
  Notation REF := (bv_unsigned sp + -296).
  Notation CTX := (ctx_now L HI mo0 h0 LB).
  Notation DS7 dN dP dA dB dX dY dZ := ([dN; dP; dA; dB; dX; dY; dZ] : list mpd) (only parsing).

  (* [comment removed for export] *)
  Definition LSTATE (pc : Z) (m : mem) (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state := ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_E ()) "(1?.(20.O10.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,O?.O>.O=.(1;.&40.VPKA,)(1;.&40.(7.$16.(21.+4.O11.)))O<.O;.O:.O9.O8.O7.O6.O5.(1;.&40.(7.(11.&40.Vsp,)-1?0.))(1;.&40.(7.(11.&40.Vsp,)-120.))(1;.&40.(7.(11.&40.Vsp,)-1>0.))(1;.&40.(7.(11.&40.Vsp,)-110.))(1;.&40.(7.(11.&40.Vsp,)-1=0.))(1;.&40.(7.(11.&40.Vsp,)-100.))(1;.&40.(7.(11.&40.Vsp,)-190.))(1;.&40.(7.(11.&40.Vsp,)-<0.))(1;.&40.-4.)(1;.&40.(7.(11.&40.Vsp,)-?0.))O4.O3.O2.O1.)VF,(1;.&40.O13.)Vfc,(22.(=.&40.))O12.(23.$10.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition LINV (h : HST usegs L HI) (LBi : list blk) (m : mem) (mo : Model) (gref : ecp_grp) (idg rg : Z)
      (dN dP dA dB dX dY dZ : mpd) (scj hj tj mj l1 l2 : list byte) (pb nb : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_E ()) "(0.(24.VL,VHI,Vmo0,Vh0,VLB,O16.O15.(25.$26.(27.(12.$28.O?.(12.$28.O>.(12.$28.O=.(12.$28.O<.(12.$28.O;.(12.$28.O:.(12.$28.O9.(17.$28.)))))))))(29.O12.))O14.O13.)(0.(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,O14.)(0.(2:.$10.O14.O15.(7.(11.&40.Vsp,)-1?8.)+<0.(12.$28.O?.(12.$28.O>.(12.$28.O=.(12.$28.O<.(12.$28.O;.(12.$28.O:.(12.$28.O9.(17.$28.)))))))))(0.(3.$4.(2;.O?.)(7.(7.(11.&40.Vsp,)-1?8.)+68.))(0.(3.$4.(2;.O>.)(7.(7.(11.&40.Vsp,)-1?8.)+8.))(0.(3.$4.(2;.O=.)(7.(7.(11.&40.Vsp,)-1?8.)+18.))(0.(3.$4.(2;.O<.)(7.(7.(11.&40.Vsp,)-1?8.)+28.))(0.(3.$4.(2;.O;.)(7.(7.(11.&40.Vsp,)-1?8.)+38.))(0.(3.$4.(2;.O:.)(7.(7.(11.&40.Vsp,)-1?8.)+48.))(0.(3.$4.(2;.O9.)(7.(7.(11.&40.Vsp,)-1?8.)+58.))(0.Pb,$26.P,(2<.$26.R1.(29.O12.))(1=.(2<.$26.R2.(27.(12.$28.O?.(12.$28.O>.(12.$28.O=.(12.$28.O<.(12.$28.O;.(12.$28.O:.(12.$28.O9.(17.$28.)))))))))))(0.(2=.$10.$2>.O14.O15.(7.(11.&40.Vsp,)-128.)O12.)(0.(2?.(30.O12.))(0.(31.$32.$33.O11.(7.(11.&40.Vsp,)-128.)O10.O12.(29.O12.))(0.(34.$10.O14.$16.(35.$36.))(0.(18.$10.O14.(7.(11.&40.Vsp,)-200.)(12.$19.(37.#8.O8.)(17.$19.)))(0.(18.$10.O14.(7.(11.&40.Vsp,)-1?8.)(12.$19.(37.#8.O7.)(17.$19.)))(0.(18.$10.O14.(7.(7.(11.&40.Vsp,)-1?8.)+78.)(12.$19.(1:.O2.)(12.$19.(1:.O1.)(12.$19.(37.#38.O6.)(17.$19.)))))(0.(18.$10.O14.(7.(11.&40.Vsp,)-138.)(12.$19.(37.#8.O5.)(12.$19.(37.#4.O4.)(12.$19.(37.#4.O3.)(17.$19.)))))(0.(18.$10.O14.(7.(11.&40.Vsp,)-68.)(12.$19.(1:.Vs11,)(12.$19.(1:.Vs10,)(12.$19.(1:.Vs9,)(12.$19.(1:.Vs8,)(12.$19.(1:.Vs7,)(12.$19.(1:.Vs6,)(12.$19.(1:.Vs5,)(12.$19.(1:.Vs4,)(12.$19.(1:.Vs3,)(12.$19.(1:.Vs2,)(12.$19.(1:.Vs1,)(12.$19.(1:.Vs0,)(12.$19.(1:.Vra,)(17.$19.)))))))))))))))(38.$10.O14.Vlo,(7.(11.&40.Vsp,)-200.))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma tail_from_linv : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_E ()) "Ph,(39.$10.VL,VHI,)PLBi,(3:.$26.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$3;.Pgref,$3<.Pidg,$4.Prg,$4.PdN,$28.PdP,$28.PdA,$28.PdB,$28.PdX,$28.PdY,$28.PdZ,$28.Pscj,(3:.(=.&8.))Phj,(3:.(=.&8.))Ptj,(3:.(=.&8.))Pmj,(3:.(=.&8.))Pl1,(3:.(=.&8.))Pl2,(3:.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)Pj,$4.Pr1,$4.Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px19,(=.&40.)Px20,(=.&40.)Px21,(=.&40.)Px22,(=.&40.)Px23,(=.&40.)Px24,(=.&40.)Px25,(=.&40.)Px26,(=.&40.)Px27,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(3=.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(0.(6.=R1<.)(6.R1<.+=.))P,(0.(1.(3>.(3?.+2.+1?.))R1<.)(6.R1<.=))(40.$10.R31.(41.$10.VL,VHI,$2>.$32.$33.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(1?.(20.R1<.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,R1;.R1:.R19.(1;.&40.VPKA,)(1;.&40.(7.$16.(21.+4.R1>.)))R18.R17.R16.R15.R14.R13.R12.R11.(1;.&40.R1=.)R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)VF,(1;.&40.+29;7<.)Vfc,(22.(=.&40.))R32.(23.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. (intros dd_H; ddestruct dd_H as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & RT & HG & AP & GL & HIDS & FR0 & FRH & FRT & FRM & FR & ST); intros JB RR).
    eapply tail_walk with (PKA := PKA) (info := info) (C := C) (lo := lo) (PAR := PAR) (bs := bs); try eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma iter_head : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_E ()) "Ph,(39.$10.VL,VHI,)PLBi,(3:.$26.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$3;.Pgref,$3<.Pidg,$4.Prg,$4.PdN,$28.PdP,$28.PdA,$28.PdB,$28.PdX,$28.PdY,$28.PdZ,$28.Pscj,(3:.(=.&8.))Phj,(3:.(=.&8.))Ptj,(3:.(=.&8.))Pmj,(3:.(=.&8.))Pl1,(3:.(=.&8.))Pl2,(3:.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)Pi,$4.Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(3=.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)P,(0.(6.=R12.)(6.R12.+<.))P,Ph',(39.$10.VL,VHI,)PLB',(3:.$26.)Pm',P,(=.&40.)(>.(=.&8.))Pmo',$3;.Pg',$3<.Pidj,$4.Py1,(=.&40.)Py5,(=.&40.)Py6,(=.&40.)Py7,(=.&40.)Py10,(=.&40.)Py11,(=.&40.)Py12,(=.&40.)Py13,(=.&40.)Py14,(=.&40.)Py15,(=.&40.)Py16,(=.&40.)Py17,(=.&40.)Py28,(=.&40.)Py29,(=.&40.)Py30,(=.&40.)Py31,(=.&40.)P,(3=.R16.R15.R14.R13.R12.R11.=R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.)P,(3.(>.(=.&40.))(43.(=.&40.)$36.(44.R2:.))(45.(=.&40.)(1;.&40.R12.)))P,(0.(6.+1.R13.)(6.R13.+=.))(40.$10.R16.(41.$10.VL,VHI,$2>.$32.$33.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(46.+29:;4.R17.R2<.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.))(40.$10.R27.(41.$10.VL,VHI,$2>.$32.$33.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(42.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(46.+29:9<.R28.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. (intros dd_H; ddestruct dd_H as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & RT & HG & AP & GL & HIDS & FR0 & FRH & FRT & FRM & FR & ST); intros IB K).
    ddestruct CX as (HH & HT & MF & MI & SOK & EXT & IDS).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBRc HAPc]. pose proof (HND _ _ _ _ HH) as NDc.
    unfold LSTATE. zstep. zstep.
    (* [comment removed for export] *)
    pose proof (U_ecp_group_free_spec L HI HFREE HLS SW DIMG HND U_MT) as SGF. unfold ecp_group_free_stmt, ecp_group_free_post, U_ECP_GROUP_FREE in SGF.
    eapply aevtM_cut.
    { eapply SGF with (lo := lo) (h := h) (LB := LBi) (A := REF) (g := gref);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH | exact HG | exact AP | exact TP | exact CA | eassumption
              | rewrite HT; intros a Ha; left; clear -Ha SLO HLS HTOP ACL ACP; unfold ECP_GROUP_SIZE in Ha; lia
              | unfold ECP_GROUP_SIZE; clear -DHI ACL SLO HLS; lia
              | clear -SLO; lia | clear -HTOP HT; lia | clear -SPA SPR; lia
              | reflexivity | f_equal; clear; lia
              | match goal with |- ?g => idtac "GFLEFT" g end ]. }
    clear SGF.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & HG2 & FRR2 & PX2 & SOK2). unfold ECP_GROUP_SIZE in PX2.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HT2 with heap_top _ _ _ ?hh = _ => rename hh into h2 end.
    pose proof (gl_free_set _ _ _ _ _ _ _ LBi GL NDc ltac:(intros b Hb; apply (proj2 (proj1 EXT b)); left; apply in_app_iff; right; exact Hb)) as FS.
    set (LBf := grp_free_LB gref LBi) in *.
    assert (EXT2 : lb_ext LB (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ]) LBf).
    { destruct EXT as [E1 E2]. split.
      - intros b. rewrite (FS b), (E1 b), in_app_iff. split.
        + (intros dd_H; ddestruct dd_H as [[[HT'|HR]|HL] NR]); [left; exact HT'| exfalso; exact (NR HR)| right; exact HL].
        + intros [HT'|HL]; [split; [left; left; exact HT'| intros HR; exact (RT _ HR HT')]| split; [right; exact HL| intros HR; apply (E2 b); [apply in_app_iff; right; exact HR| exact HL]]].
      - intros b HT'. apply E2. apply in_app_iff. left. exact HT'. }
    assert (TOK2 : tmp_ok usegs m2 LBf G 192 [dN; dP; dA; dB; dX; dY; dZ]).
    { eapply (tmp_ok_presx usegs L); [exact TOK| exact PX2| exact MI| exact MI2| clear; lia| clear -ACL SLO HLS; lia| | | exact HBRc].
      - intros d Hd Od. apply (proj2 (FS _)). pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK Hd) as [MDd _].
        destruct (mpdr_blk_facts usegs L _ _ _ MDd Od HBRc) as (Id & _). split; [exact Id|].
        intros HR. apply (RT _ HR). apply in_tmp_blocks. exists d. split; [exact Hd|]. rewrite (mpd_blk_heap _ Od). left; reflexivity.
      - repeat constructor; cbn; clear -ACL SLO HLS ACP; lia. }
    assert (PXn : heap_presx usegs L LB (bv_unsigned sp) XS m0 m2).
    { eapply heap_presx_trans; [exact PX|].
      eapply (presx_caller usegs L LB LBf LBi); [exact PX2| intros b Hb; eapply lb_ext_sub; [exact EXT2| exact Hb]| clear; lia| clear -ACL SLO HLS; lia
        | exact HBRc| exact HAPc| exact NDc| intros b Hb; eapply lb_ext_sub; [exact EXT| exact Hb]| | exact DHI| exact DI1| exact DI2].
      intros iv [<-|[]]. left. cbn. clear -ACL SLO HLS. lia. }
    pose proof (ecp_ids_state_presx usegs L _ _ _ _ _ _ _ IDS PX2 IDL
                  ltac:(cbn; generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia) ltac:(cbn; generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia)) as IDS2.
    assert (HIDS2 : bytes_at usegs m2 U_ECP_IDS (u32s IDWS)).
    { eapply heap_presx_bytes_at; [exact PX2| exact HIDS| |]; rewrite <- ids_bytes_u32s; cbn [length ecp_ids_bytes].
      - intros a Ha. right; left. destruct (IL4 a ltac:(right; generalize IL1 IL2 IL3 Ha; clear; cbn; intros; lia)) as [_ NS]. split; [generalize IL1 IL2 IL3 Ha; clear; cbn; intros; lia| exact NS].
      - cbn. generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia. }
    repeat match goal with
    | Hc : rw_cells usegs m ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells usegs L _ _ _ m m2 a cs PX2) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; intros a' Ha'; left; clear -Ha'; lia
                  | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; split; [clear; lia| exact I] ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end.
    destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 HAP2]. pose proof (HND _ _ _ _ HH2) as ND2.
    clear HH MI SOK ST TOK PX IDS HIDS HG AP HBRc HAPc MK FS NDc.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    (* [comment removed for export] *)
    destruct (nth_error IDWS (Z.to_nat i)) as [w|] eqn:NJ; [| exfalso; apply nth_error_None in NJ; cbn in NJ; clear -NJ IB; lia].
    ddestruct (ids_nth i w NJ ltac:(clear -IB; lia)) as (idj & -> & IJB & IJZ & _).
    assert (IJ1 : 1 <= idj <= 13) by (clear -IJB IJZ IB; lia).
    pose proof (u32ro_read usegs m2 U_ECP_IDS IDWS i _ (wa (U_ECP_IDS + 4 * i)) HIDS2 NJ ltac:(clear -IB; lia) eq_refl) as RDJ.
    zstep. clear RDJ. rewrite (sx32_small idj) by (clear -IJB; lia).
    zstep. zstep.
    (* [comment removed for export] *)
    pose proof (U_ecp_group_load_spec L HI HFREE HCALLOC HLS SW DIMG HND) as SPL.
    unfold ecp_group_load_stmt, ecp_group_load_post, U_ECP_GROUP_LOAD in SPL.
    eapply aevtM_cut.
    { eapply SPL with (lo := lo) (LB := LBf) (h := h2) (id := idj) (A := REF) (g := grp_zero REF);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH2 | exact HG2 | exact TP | exact CA | eassumption
              | (* [comment removed for export] *)
                intros d1 d2 Q1 Q2 NE O1 O2; exfalso; revert Q1 O1; unfold grp_mpds, grp_zero;
                cbn [g_P g_A g_B g_G g_N pt_mpds pt_zero pt_X pt_Y pt_Z app In]; unfold mpd_zero;
                intros Q1 O1; decompose [or] Q1; subst; cbn in O1; try discriminate; contradiction
              | rewrite HT2, HT; intros a Ha; left; clear -Ha SLO HLS HTOP ACL ACP; unfold ECP_GROUP_SIZE in Ha; lia
              | unfold ECP_GROUP_SIZE; clear -DHI ACL SLO HLS; lia
              | clear -IJ1; lia
              | clear -SLO; lia | rewrite HT2; clear -HTOP HT; lia | clear -SPA SPR; lia
              | reflexivity | f_equal; clear; lia
              | match goal with |- ?g => idtac "GLLEFT" g end ]. }
    clear SPL.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI3 & ST3 & MF3 & HT3 & HH3 & LEQ & LNEW & HG3 & AP3 & GB3 & RES & PX3 & SOK3). unfold ECP_GROUP_SIZE in PX3.
    change (grp_free_LB (grp_zero REF) LBf) with LBf in LEQ, LNEW, PX3.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m3; rename mox into mo3 end.
    match type of HT3 with heap_top _ _ _ ?hh = _ => rename hh into h3 end.
    match type of HH3 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB3 end.
    lazymatch type of RES with gl_result _ _ _ _ ?r ?g ?nb => rename r into r3; rename g into g3; rename nb into NB3 end.
    subst NB3.
    assert (EXT3 : lb_ext LB (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ] ++ grp_blocks g3) LB3).
    { pose proof EXT2 as [E1 E2]. split.
      - intros b. rewrite (LEQ b), (E1 b), in_app_iff. clear. tauto.
      - intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (E2 b Hb)|].
        intros HL. apply (LNEW b Hb). eapply lb_ext_sub; [exact EXT2| exact HL]. }
    assert (RT3 : forall b, In b (grp_blocks g3) -> ~ In b (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ])).
    { intros b Hb HTb. apply (LNEW b Hb). apply (proj2 (proj1 EXT2 b)). left. exact HTb. }
    assert (TOK3 : tmp_ok usegs m3 LB3 G 192 [dN; dP; dA; dB; dX; dY; dZ]).
    { eapply tmp_ok_relist; [eapply (tmp_ok_presx usegs L); [exact TOK2| exact PX3| exact MI2| exact MI3| clear; lia| clear -ACL SLO HLS; lia| | | exact HBR2]|].
      - intros d Hd Od. pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK2 Hd) as [MDd _]. exact (proj1 (mpdr_blk_facts usegs L _ _ _ MDd Od HBR2)).
      - repeat constructor; cbn; clear -ACL SLO HLS ACP; lia.
      - intros d Hd Od. apply (proj2 (LEQ _)). right. pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK2 Hd) as [MDd _].
        exact (proj1 (mpdr_blk_facts usegs L _ _ _ MDd Od HBR2)). }
    assert (PXn3 : heap_presx usegs L LB (bv_unsigned sp) XS m0 m3).
    { eapply heap_presx_trans; [exact PXn|].
      eapply (presx_caller usegs L LB LBf LBf); [exact PX3| intros b Hb; eapply lb_ext_sub; [exact EXT2| exact Hb]| clear; lia| clear -ACL SLO HLS; lia
        | exact HBR2| exact HAP2| exact ND2| intros b Hb; eapply lb_ext_sub; [exact EXT2| exact Hb]| | exact DHI| exact DI1| exact DI2].
      intros iv [<-|[]]. left. cbn. clear -ACL SLO HLS. lia. }
    pose proof (ecp_ids_state_presx usegs L _ _ _ _ _ _ _ IDS2 PX3 IDL
                  ltac:(cbn; generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia) ltac:(cbn; generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia)) as IDS3.
    assert (HIDS3 : bytes_at usegs m3 U_ECP_IDS (u32s IDWS)).
    { eapply heap_presx_bytes_at; [exact PX3| exact HIDS2| |]; rewrite <- ids_bytes_u32s; cbn [length ecp_ids_bytes].
      - intros a Ha. right; left. destruct (IL4 a ltac:(right; generalize IL1 IL2 IL3 Ha; clear; cbn; intros; lia)) as [_ NS]. split; [generalize IL1 IL2 IL3 Ha; clear; cbn; intros; lia| exact NS].
      - cbn. generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia. }
    repeat match goal with
    | Hc : rw_cells usegs m2 ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells usegs L _ _ _ m2 m3 a cs PX3) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; intros a' Ha'; left; clear -Ha'; lia
                  | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; split; [clear; lia| exact I] ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end.
    assert (CX3 : CTX h3 LB3 (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ] ++ grp_blocks g3) m3 mo3).
    { split; [exact HH3|]. split; [rewrite HT3, HT2; exact HT|]. split; [eapply mo_frame_trans; [exact MF| eapply mo_frame_trans; [exact MF2| exact MF3]]|].
      split; [exact MI3|]. split; [exact SOK3|]. split; [exact EXT3| exact IDS3]. }
    assert (LI3 : LINV h3 LB3 m3 mo3 g3 idj r3 dN dP dA dB dX dY dZ scj hj tj mj l1 l2 pb nb).
    { split; [exact CX3|]. split; [exact PXn3|]. split; [exact TOK3|].
      split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact RT3|]. split; [exact HG3|]. split; [exact AP3|]. split; [exact RES|]. split; [exact HIDS3|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FRM|]. split; [exact FR| exact ST3]. }
    clear HH2 MI2 ST2 SOK2 TOK2 PXn IDS2 HIDS2 HG2 EXT2 LEQ LNEW PX3 HBR2 HAP2 ND2 MK2 CX3 EXT3 RT3 TOK3 PXn3 IDS3 HIDS3.
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      zstep.
      eapply tail_from_linv; [exact LI3| clear -IB; lia| exact (gl_result_range _ _ _ _ _ _ _ RES)].
    - (* [comment removed for export] *)
      assert (Z0 : r3 = 0).
      { pose proof (gl_result_range _ _ _ _ _ _ _ RES) as RR. clear -KR RR. apply Z.mod_divide in KR; [| lia]. destruct KR as [q Hq].
        assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
      subst r3. eapply K; [exact LI3| first [exact NJ| reflexivity]| exact IJ1].
  Qed.
End EP.

