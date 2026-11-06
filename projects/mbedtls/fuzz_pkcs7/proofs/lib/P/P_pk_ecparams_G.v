(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Arr MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepPk PkTmp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_platform_zeroize P_mpi_free P_mpi_addsub P_ecp_keypair_init P_ecp_group_free P_ecp_group_load
     P_ecp_group_load_main P_ecp_defs P_ecp_mul_mod P_ecp_grp_id_list P_ecp_point_free P_asn1_get_sequence_of_A P_pk_wrap_eckey P_pk_free P_pk_type
     P_pk_ecc_set_group P_ecp_sinv P_string P_oid P_oidv P_oid_ec_grp P_oid_ec_grp_v P_ecp_group_init P_mpi_cmp P_mpi_bitlen P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_C P_pk_ecparams_D P_pk_ecparams_E P_pk_ecparams_F.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_ecparams_G () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.P.PImg.psegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.P_ECP_IDS_DONE"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.P_ECP_IDS"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Lib.HeapIface.hl_static"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.RepEcp.ecp_grp"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.P.P_pk_ecparams_E.LINV"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_pk_ecparams_A.pk_use_ecparams_post"; "OSSVerify.KrLib.P.P_ecp_defs.P_MT"; "OSSVerify.KrLib.P.P_ecp_defs.P_CA"; "OSSVerify.KrLib.P.P_ecp_defs.P_ONE"; "OSSVerify.KrLib.P.P_ecp_keypair_init.kp_init"; "OSSVerify.KrLib.P.P_pk_ecparams_E.LSTATE"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.le"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.P.P_pk_ecparams_B.ctx_now"; "OSSVerify.KrLib.Spec.PkTmp.tmp_blocks"; "OSSVerify.KrLib.Spec.PkTmp.tmp_ok"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].



Section EP.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis CA_RSA0 : const_at L P_RSA_INFO 4.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (mo0 : Model) (h0 : HST psegs L HI) (LB : list blk)
            (PKA info C lo PAR LEN P BUF : Z) (tg pd : word) (bs : list byte)
            (idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ : word).
  Notation K := (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ).
  Hypothesis HH0 : HEAP psegs L HI h0 LB m0 mo0.
  Hypothesis HPKA0 : rw_cells psegs m0 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)].
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis NZP : 0 < PKA.
  Hypothesis EI : In info P_EC_INFOS.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis CWP : client_wrange L LB lo (heap_top psegs L HI h0) PKA 16.
  Hypothesis DPC : PKA + 16 <= C \/ C + 256 <= PKA.
  Hypothesis PKD : PKA + 16 <= hl_data_lo L \/ hl_data_hi L <= PKA.
  Hypothesis KP0 : ecp_keypair_at psegs P_MT m0 LB C K.
  Hypothesis INC : In (C, 256) LB.
  Hypothesis CD : C + 256 <= hl_data_lo L \/ hl_data_hi L <= C.
  Hypothesis HPAR0 : rw_cells psegs m0 PAR (buf_cells tg pd LEN P).
  Hypothesis ALR : PAR mod 8 = 0.
  Hypothesis NZR : 0 < PAR.
  Hypothesis DSR : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis RD : PAR + 24 <= hl_data_lo L \/ hl_data_hi L <= PAR.
  Hypothesis RC : PAR + 24 <= C \/ C + 256 <= PAR.
  Hypothesis HBS0 : bytes_at psegs m0 BUF bs.
  Hypothesis INB : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis BP : BUF <= P.
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis PL : P + LEN <= BUF + Z.of_nat (length bs).
  Hypothesis B63 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis IDS0 : ecp_ids_state psegs P_ECP_IDS_DONE P_ECP_IDS m0.
  Hypothesis SOK0 : statics_ok psegs L m0.
  Hypothesis CA : const_at L P_MEMSET_FUNC 8.
  Hypothesis CAT : const_at L P_OID_EC_GRP_TBL 440.
  Hypothesis CA_EC0 : forall e, In e P_EC_INFOS -> const_at L e 4.
  Hypothesis SLO : lo <= bv_unsigned sp - 688 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top psegs L HI h0.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv psegs m0.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis SPR : bv_unsigned sp < 2^64.
  Hypothesis IDL : ecp_ids_lok L P_ECP_IDS_DONE P_ECP_IDS.
  (* [comment removed for export] *)
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis CAC : C + 256 <= alloc_ceiling.
  Hypothesis C0 : 0 < C.
  Hypothesis C16 : C mod 16 = 0.
  Hypothesis CIM : C + 256 <= hl_img_lo L \/ hl_img_hi L <= C.
  Hypothesis BAC : BUF + Z.of_nat (length bs) <= alloc_ceiling.
  Hypothesis BIM : BUF + Z.of_nat (length bs) <= hl_img_lo L \/ hl_img_hi L <= BUF.

  Notation XS := [(P_ECP_IDS_DONE, P_ECP_IDS_DONE + 1); (P_ECP_IDS, P_ECP_IDS + 56)].
  Notation X0 := [(C, C + ECP_GROUP_SIZE); (P_ECP_IDS_DONE, P_ECP_IDS_DONE + 1); (P_ECP_IDS, P_ECP_IDS + 56)].
  Notation POST := (pk_use_ecparams_post psegs L HI P_MT P_CA P_ONE P_ECP_IDS_DONE P_ECP_IDS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PKA info C K lo m0 mo0).
  Notation FRS mm := (rw_cells psegs mm (bv_unsigned sp + -104)
                        [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_G ()) "(0.(1.+1000.(2.VL,))(0.(1.=VC,)(0.(3.$4.(5.VC,+10.)=)(0.(6.(7.VC,+100.)(2.VL,))(0.(8.(6.(7.VC,+100.)(9.VL,))(6.(:.VL,)VC,))(0.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(2.VL,))(8.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(9.VL,))(6.(:.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_G ()) "Pm,P,(=.&40.)(>.(=.&8.))P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R1.)(18.$10.R2.VPKA,(12.$19.(1:.(1;.&40.Vinfo,))(12.$19.(1:.(1;.&40.VC,))(17.$19.))))")
(* [comment removed for export] *).
  Proof.
    intros m PX. eapply heap_presx_rw_cells; [exact PX| exact HPKA0| |]; cbn [cells_size csize Nat.add disjoint_from].
    - intros a Ha. destruct (CWP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exact Q].
    - ddestruct IDL as (I1 & I2 & I3 & _). clear -PKD I1 I2 I3. split; [lia| split; [lia| exact I]].
  Qed.


  (* [comment removed for export] *)
  #[using="IDL"] Lemma IL1 : hl_data_lo L <= P_ECP_IDS_DONE. Proof. exact (proj1 IDL). Qed.
  #[using="L IDL"] Lemma IL2 : P_ECP_IDS_DONE + 1 <= P_ECP_IDS. Proof. exact (proj1 (proj2 IDL)). Qed.
  #[using="IDL"] Lemma IL3 : P_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 IDL))). Qed.
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_G ()) "Pa,$4.P,(8.(0.(6.$15.R1.)(1.R1.(7.$15.+1.)))(0.(6.$16.R1.)(1.R1.(7.$16.+38.))))(0.(1<.VL,R2.)(1=.(1>.VL,R2.)))")
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
  Notation cmp_chain' := (cmp_chain L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation linv_frame' := (linv_frame L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP SPA DHI IDL).


  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma loop_step : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_G ()) "Pi,$4.Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.Pgref,$23.Pidg,$4.Prg,$4.PdN,$24.PdP,$24.PdA,$24.PdB,$24.PdX,$24.PdY,$24.PdZ,$24.Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Pmj,(20.(=.&8.))Pl1,(20.(=.&8.))Pl2,(20.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)P,(0.(6.=R28.)(6.R28.+<.))P,P,(1.R29.+<.)Ph',(1?.$10.VL,VHI,)PLB',(20.$21.)Pm',P,(=.&40.)(>.(=.&8.))Pmo',$22.Pg',$23.Pidg',$4.Prg',$4.Pscj',(20.(=.&8.))Py1,(=.&40.)Py5,(=.&40.)Py6,(=.&40.)Py7,(=.&40.)Py10,(=.&40.)Py11,(=.&40.)Py12,(=.&40.)Py13,(=.&40.)Py14,(=.&40.)Py15,(=.&40.)Py16,(=.&40.)Py17,(=.&40.)Py28,(=.&40.)Py29,(=.&40.)Py30,(=.&40.)Py31,(=.&40.)P,(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R18.R17.R16.R15.R14.R13.R12.R3:.R39.R38.R37.R36.R35.R34.R11.R32.R31.R30.R2?.R2>.R2=.R2<.)(26.$10.R16.(27.$10.VL,VHI,$28.$29.$2:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(2<.Vsp,Vgp,Vtp,VF,Vfc,VPKA,+275:<.R17.(7.R43.+1.)R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.))(26.$10.R26.(27.$10.VL,VHI,$28.$29.$2:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(2<.Vsp,Vgp,Vtp,VF,Vfc,VPKA,+275:<.R27.R2:.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros LI IB REC.
    eapply iter_head'; [exact LI| exact IB|]. intros h' LB' m' mo' g' idj y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 LI' NJ IJ1.
    eapply cmp_chain'; [exact LI'| exact IB|]. intros m'' scj' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 LI''.
    (* [comment removed for export] *)
    dpose LI'' as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & RT & HG & AP & GL & HIDS & FR0 & FRH & FRT & FRM & FR & ST).
    ddestruct CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    unfold P_pk_ecparams_E.LSTATE.
    destruct (nth_error IDWS (Z.to_nat (i + 1))) as [w|] eqn:NJ1; [| exfalso; apply nth_error_None in NJ1; cbn in NJ1; clear -NJ1 IB; lia].
    ddestruct (ids_nth (i + 1) w NJ1 ltac:(clear -IB; lia)) as (idn & -> & INB1 & INZ & _).
    pose proof (u32ro_read psegs m'' P_ECP_IDS IDWS (i + 1) _ (wa (P_ECP_IDS + 4 * i + 4)) HIDS NJ1 ltac:(clear -IB; lia) ltac:(f_equal; clear; lia)) as RDJ.
    zstep. clear RDJ. rewrite (sx32_small idn) by (clear -INB1; lia).
    zstep. zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      assert (I12 : i = 12). { clear -KE INZ INB1 IB. rewrite ?Z.mod_small in KE by lia. lia. }
      zstep. zstep.
      replace (Z_to_bv 64 (P_ECP_IDS + 4 * i + 4)) with (Z_to_bv 64 (P_ECP_IDS + 4 * 13)) by (f_equal; clear -I12; lia).
      eapply tail_from_linv'; [exact LI''| clear; lia| clear; lia].
    - assert (I12 : i < 12). { clear -KE INZ INB1 IB. rewrite ?Z.mod_small in KE by lia. lia. }
      replace (Z_to_bv 64 (P_ECP_IDS + 4 * i + 4)) with (Z_to_bv 64 (P_ECP_IDS + 4 * (i + 1))) by (f_equal; clear; lia).
      eapply (REC I12). exact LI''.
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_G ()) "Pn,$2=.Pi,$4.Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.Pgref,$23.Pidg,$4.Prg,$4.PdN,$24.PdP,$24.PdA,$24.PdB,$24.PdX,$24.PdY,$24.PdZ,$24.Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Pmj,(20.(=.&8.))Pl1,(20.(=.&8.))Pl2,(20.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(2>.(2?.(30.+<.R27.))R28.)P,(0.(6.=R28.)(6.R28.+<.))P,(25.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)(26.$10.R26.(27.$10.VL,VHI,$28.$29.$2:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(2<.Vsp,Vgp,Vtp,VF,Vfc,VPKA,+275:<.R27.R2:.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until x31; intros HN IB LI.
    - eapply loop_step; [exact LI| exact IB|]. intros LT. exfalso. clear -HN IB LT. lia.
    - eapply loop_step; [exact LI| exact IB|]. intros LT. intros. eapply IH; [clear -HN IB LT; lia| clear -IB LT; lia| eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma idloop_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_G ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.PdN,$24.PdP,$24.PdA,$24.PdB,$24.PdX,$24.PdY,$24.PdZ,$24.Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Pmj,(20.(=.&8.))Pl1,(20.(=.&8.))Pl2,(20.(=.&8.))Prj,(20.(=.&8.))Ppb,(=.&40.)Pnb,(=.&40.)Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px9,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px18,(=.&40.)Px19,(=.&40.)Px20,(=.&40.)Px21,(=.&40.)Px22,(=.&40.)Px23,(=.&40.)Px24,(=.&40.)Px25,(=.&40.)Px26,(=.&40.)Px27,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(31.VL,VHI,Vmo0,Vh0,VLB,R2?.R2>.(32.(12.$24.R2;.(12.$24.R2:.(12.$24.R29.(12.$24.R28.(12.$24.R27.(12.$24.R26.(12.$24.R25.(17.$24.)))))))))R2=.R2<.)P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R2>.)P,(33.$10.R2?.R30.(7.(11.&40.Vsp,)-1?8.)+<0.(12.$24.R2=.(12.$24.R2<.(12.$24.R2;.(12.$24.R2:.(12.$24.R29.(12.$24.R28.(12.$24.R27.(17.$24.)))))))))P,(3.$4.(34.R2>.)(7.(7.(11.&40.Vsp,)-1?8.)+68.))P,(3.$4.(34.R2>.)(7.(7.(11.&40.Vsp,)-1?8.)+8.))P,(3.$4.(34.R2>.)(7.(7.(11.&40.Vsp,)-1?8.)+18.))P,(3.$4.(34.R2>.)(7.(7.(11.&40.Vsp,)-1?8.)+28.))P,(3.$4.(34.R2>.)(7.(7.(11.&40.Vsp,)-1?8.)+38.))P,(3.$4.(34.R2>.)(7.(7.(11.&40.Vsp,)-1?8.)+48.))P,(3.$4.(34.R2>.)(7.(7.(11.&40.Vsp,)-1?8.)+58.))P,(18.$10.R37.(7.(11.&40.Vsp,)-200.)(12.$19.(35.#8.R2>.)(17.$19.)))P,(18.$10.R38.(7.(11.&40.Vsp,)-1?8.)(12.$19.(35.#8.R2>.)(17.$19.)))P,(18.$10.R39.(7.(7.(11.&40.Vsp,)-1?8.)+78.)(12.$19.(1:.R29.)(12.$19.(1:.R28.)(12.$19.(35.#38.R2>.)(17.$19.)))))P,(18.$10.R3:.(7.(11.&40.Vsp,)-138.)(12.$19.(35.#8.R2>.)(12.$19.(35.#4.R2=.)(12.$19.(35.#4.R2<.)(17.$19.)))))P,(18.$10.R3;.(7.(11.&40.Vsp,)-128.)(12.$19.(35.#<0.R2<.)(17.$19.)))P,(18.$10.R3<.(7.(11.&40.Vsp,)-68.)(12.$19.(1:.Vs11,)(12.$19.(1:.Vs10,)(12.$19.(1:.Vs9,)(12.$19.(1:.Vs8,)(12.$19.(1:.Vs7,)(12.$19.(1:.Vs6,)(12.$19.(1:.Vs5,)(12.$19.(1:.Vs4,)(12.$19.(1:.Vs3,)(12.$19.(1:.Vs2,)(12.$19.(1:.Vs1,)(12.$19.(1:.Vs0,)(12.$19.(1:.Vra,)(17.$19.)))))))))))))))P,(36.$10.R3=.Vlo,(7.(11.&40.Vsp,)-200.))(26.$10.R3=.(27.$10.VL,VHI,$28.$29.$2:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(37.(38.R2<.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,R2;.R2:.R29.(1;.&40.VPKA,)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)VF,(1;.&40.+2755<.)Vfc,(39.(=.&40.))R3>.(3:.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX PX TOK EN EP EA EB EX EY EZ FR0 FRH FRT FRM FRR FR ST.
    dpose CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    (* [comment removed for export] *)
    pose proof (P_ecp_group_init_spec P_MT) as SGI. unfold ecp_group_init_stmt, ecp_group_init_post, P_ECP_GROUP_INIT, ECP_GROUP_SIZE in SGI.
    pose proof (munch_refl [(REF, REF + 192); (lo, bv_unsigned sp + -512)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. zstep.
    acallx_sp (bv_unsigned sp + -512) (eapply SGI with (A := REF) (LB := LBi) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
            [ exact FRR | clear -SPA SPR; lia | clear -SLO HLS ACL ACP; lia | exact ST | clear -SLO HLS; lia | clear -SPA SPR; lia
            | right; clear; lia | exact MI | reflexivity | reflexivity ]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with W : wmono psegs m m1 |- _ => rename W into WM1 end. rename MU into MU1.
    match goal with M : mem_inv psegs m1 |- _ => rename M into MI1 end.
    match goal with Hg : ecp_group_at psegs P_MT m1 LBi _ _ |- _ => rename Hg into HG1 end.
    destruct (ctx_munch' _ _ _ _ _ _ _ CX PX MU1 WM1 MI1 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX1 PX1].
    pose proof (tmp_ok_munch psegs L _ _ _ _ _ _ _ TOK MU1 WM1 (proj1 (proj2 (proj2 (proj2 CX)))) MI1 ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) HBR) as TOK1.
    clear MU1 WM1 CX PX TOK MK HH HT MF SOK IDS SGI.
    dpose CX1 as (HH & HT & MF & _ & SOK & _ & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    (* [comment removed for export] *)
    pose proof P_ecp_grp_id_list_spec as SIL. unfold ecp_grp_id_list_stmt, ecp_grp_id_list_post, P_ECP_GRP_ID_LIST in SIL.
    zstep.
    eapply aevtM_cut_evt; [exact MK| eapply SIL; [exact IDS| exact MI1| reflexivity]|].
    intros ms' PO. destruct_exs PO. ddestruct PO as (E & MU2 & WM2 & MI2 & HFLAG & FNZ & HIDSc). subst ms'.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (DST : forall a k, hl_data_hi L <= a -> disjoint_from [(P_ECP_IDS_DONE, P_ECP_IDS_DONE + 1); (P_ECP_IDS, P_ECP_IDS + 56)] a k).
    { intros a k Ha. cbn. generalize IL1 IL2 IL3 Ha; clear; intros. repeat split; lia. }
    assert (CX2 : CTX h LBi (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ]) m2 mo).
    { split. { apply (Asn1AuxA.HEAP_munch psegs L HI h LBi m1 m2 mo lo _ HH ACL MU2 WM2).
               intros a Ha NO. right; left. cbn in NO.
               assert (IN : P_ECP_IDS_DONE <= a < P_ECP_IDS_DONE + 1 \/ P_ECP_IDS <= a < P_ECP_IDS + 56) by (clear -NO; lia).
               destruct (IL4 a IN) as [_ NS]. split; [generalize IL1 IL2 IL3 IN; clear; intros; lia| exact NS]. }
      split; [exact HT|]. split; [exact MF|]. split; [exact MI2|].
      split. { eapply statics_ok_munch; [exact SOK| exact MU2|]. intros a Ha NW. cbn.
               split; [| split; [| exact I]]; intros IN; apply NW; apply (proj1 (IL4 a ltac:(clear -IN; lia))). }
      split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 CX1))))))|].
      eapply ecp_ids_state_done; [exact HFLAG| exact FNZ| exact HIDSc]. }
    assert (PX2 : heap_presx psegs L LB (bv_unsigned sp) XS m0 m2).
    { eapply heap_presx_trans; [exact PX1|]. eapply heap_presx_of_munch; [exact MU2| exact WM2|]. intros a _ _ Ho. exact Ho. }
    assert (TOK2 : tmp_ok psegs m2 LBi G 192 [dN; dP; dA; dB; dX; dY; dZ]).
    { eapply (tmp_ok_munch_data psegs L); [exact TOK1| exact MU2| exact WM2| exact MI1| exact MI2| | exact DHI| clear -ACL SLO HLS; lia| exact DI1| exact DI2| exact HBR].
      repeat constructor; cbn; generalize IL1 IL2 IL3; clear; intros; lia. }
    lazymatch type of HG1 with ecp_group_at _ _ _ _ _ ?g => assert (HG2 : ecp_group_at psegs P_MT m2 LBi REF g) end.
    { eapply (ecp_group_at_munch psegs); [exact HG1| exact MU2| exact WM2| exact MI1| exact MI2| apply DST; clear -DHI ACL SLO HLS; lia|].
      intros d Hd O. exfalso. revert Hd O. unfold grp_mpds, grp_init. cbn [g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]. unfold mpd_init.
      intros Hd O; decompose [or] Hd; subst; cbn in O; try discriminate; contradiction. }
    assert (HIDS2 : bytes_at psegs m2 P_ECP_IDS (u32s IDWS)).
    { rewrite <- ids_bytes_u32s. pose proof HIDSc as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB. }
    repeat match goal with
    | Hc : rw_cells psegs m1 ?a ?cs |- _ =>
        first [ eapply (rw_cells_transport psegs _ m1 m2 a cs) in Hc; [| exact MU2| exact WM2| apply DST; clear -DHI ACL SLO HLS; lia]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end.
    match goal with S : stk psegs m1 lo _ |- _ => eapply (stk_transport_disjoint psegs _ m1 m2) in S; [| exact MU2| exact WM2| apply DST; clear -DHI ACL SLO HLS; lia]; rename S into ST end.
    clear HG1 MU2 WM2 MI1 CX1 PX1 TOK1 HFLAG FNZ HIDSc SIL HH HT MF SOK IDS MK.
    dpose CX2 as (HH & HT & MF & _ & SOK & _ & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    (* [comment removed for export] *)
    zstep.
    pose proof (u32ro_read psegs m2 P_ECP_IDS IDWS 0 (Z_to_bv 64 5) (wa (P_ECP_IDS + 0)) HIDS2 eq_refl ltac:(clear; lia) ltac:(f_equal; clear; lia)) as RD0.
    zstep. clear RD0. rewrite (sx32_small 5) by (clear; lia).
    zstep. if_cases K5; zify_cond K5. { exfalso. clear -K5. rewrite ?unsigned_lit in K5 by lia. lia. }
    do 11 zstep.
    replace (Z_to_bv 64 P_ECP_IDS) with (Z_to_bv 64 (P_ECP_IDS + 4 * 0)) by (f_equal; clear; lia).
    lazymatch type of HG2 with ecp_group_at _ _ _ _ _ ?g =>
      eapply (loop_walk 12 0) with (gref := g) (idg := 0) (rg := MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE) end; [clear; cbn; lia| clear; lia|].
    split. { cbn [grp_blocks grp_mpds grp_init g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z flat_map app mpd_blk mpd_init md_own]. rewrite app_nil_r. exact CX2. }
    split; [exact PX2|]. split; [exact TOK2|].
    split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
    split. { cbn [grp_blocks grp_mpds grp_init g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z flat_map app mpd_blk mpd_init md_own]. intros b []. }
    split; [exact HG2|].
    split. { intros d1 d2 Q1 Q2 NE O1 O2. exfalso. revert Q1 O1. unfold grp_mpds, grp_init.
             cbn [g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]. unfold mpd_init.
             intros Q1 O1; decompose [or] Q1; subst; cbn in O1; try discriminate; contradiction. }
    split. { right. right. left. split; [reflexivity|]. split; [clear; lia|].
             split; [cbn [grp_blocks grp_mpds grp_init g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z flat_map app mpd_blk mpd_init md_own]; reflexivity|].
             deexists 9. split; [reflexivity| exact I]. }
    split; [exact HIDS2|]. split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FRM|]. split; [exact FR| exact ST].
  Qed.
End EP.
