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
     P_pk_ecc_set_group P_ecp_sinv P_string P_oid P_oidv P_oid_ec_grp P_oid_ec_grp_v P_ecp_group_init P_mpi_cmp P_mpi_bitlen P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_C P_pk_ecparams_D P_pk_ecparams_E P_pk_ecparams_F P_pk_ecparams_G P_asn1_get_tag P_asn1_get_int P_asn1_get_mpi P_mpi_read_binary P_mpi_read_binary_proof P_mpi_lset P_pk_ecparams_H P_pk_ecparams_I P_pk_ecparams_J P_pk_ecparams_K P_asn1_empty.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_ecparams_L () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.P.PImg.psegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.P_ECP_IDS_DONE"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.P_ECP_IDS"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Lib.HeapIface.hl_static"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.P.P_pk_ecparams_B.ctx_now"; "OSSVerify.KrLib.Spec.Rep.buf_cells"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_pk_ecparams_A.pk_use_ecparams_post"; "OSSVerify.KrLib.P.P_ecp_defs.P_MT"; "OSSVerify.KrLib.P.P_ecp_defs.P_CA"; "OSSVerify.KrLib.P.P_ecp_defs.P_ONE"; "OSSVerify.KrLib.P.P_ecp_keypair_init.kp_init"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].




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
  Hypothesis LEN0 : 0 <= LEN.
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
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_L ()) "(0.(1.+1000.(2.VL,))(0.(1.=VC,)(0.(3.$4.(5.VC,+10.)=)(0.(6.(7.VC,+100.)(2.VL,))(0.(8.(6.(7.VC,+100.)(9.VL,))(6.(:.VL,)VC,))(0.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(2.VL,))(8.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(9.VL,))(6.(:.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_L ()) "Pm,P,(=.&40.)(>.(=.&8.))P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R1.)(18.$10.R2.VPKA,(12.$19.(1:.(1;.&40.Vinfo,))(12.$19.(1:.(1;.&40.VC,))(17.$19.))))")
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
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_L ()) "Pa,$4.P,(8.(0.(6.$15.R1.)(1.R1.(7.$15.+1.)))(0.(6.$16.R1.)(1.R1.(7.$16.+38.))))(0.(1<.VL,R2.)(1=.(1>.VL,R2.)))")
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
  Notation idloop_walk' := (idloop_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation cleanup_walk' := (cleanup_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation linv_frame' := (linv_frame L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP SPA DHI IDL).



  Notation PEND := (P + LEN).
  Ltac inlist := cbn; repeat (first [ left; reflexivity | right ]).
  (* [comment removed for export] *)
  Ltac dj7 EN EP EA EB EX EY EZ :=
    let d := fresh "d" in let Hd := fresh "Hd" in
    intros d Hd; cbn in Hd; decompose [or] Hd; try contradiction; subst d; rewrite ?EN, ?EP, ?EA, ?EB, ?EX, ?EY, ?EZ; cbn;
    generalize SLO HLS ACL; clear; intros; repeat split; lia.

  Notation SPINV' := (SPINV L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB lo LEN P).
  Notation spinv_munch' := (spinv_munch L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB PKA C lo PAR LEN P bs ACL HTOP DHI IDL).
  Notation spinv_update' := (spinv_update L HI HLS DIMG HND sp m0 mo0 h0 LB lo SLO ACL DHI IDL).
  Notation ctx_bytes' := (ctx_bytes L DIMG sp m0 LB BUF bs HBS0 INB IDL BIM).
  Notation tmp_apart_LB' := (tmp_apart_LB L HI HLS ra sp LB PKA C lo PAR bs NZP DSP DPC NZR DSR RC SLO ACL ACP CAC C0).
  Notation tmp_upd7' := (tmp_upd7 sp).
  Notation tmp_writable' := (tmp_writable L HI sp h0 lo ACL HTOP DHI).
  Notation spec_err' := (spec_err L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation spec_erradd' := (spec_erradd L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).

(* [comment removed for export] *)
  Ltac tmp_post m1 m2 d Ed CX1 PX1 TOK1 HH1 HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2 CXo PXo TOKo :=
    let EAD := fresh "EAD" in let HBR1 := fresh "HBR1" in let MDd := fresh "MDd" in let NSd := fresh "NSd" in
    pose proof (proj1 OUT) as EAD;
    destruct (spinv_update' _ _ m1 _ _ _ m2 _ _ d _ _ CX1 PX1 TOK1 ltac:(inlist) HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2
                ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as (CXo & PXo & TOKo);
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _];
    pose proof (proj1 (tmp_ok_in psegs _ _ _ _ _ d TOK1 ltac:(inlist))) as MDd;
    pose proof (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK1)) d ltac:(inlist))) as NSd;
    rewrite (mpd_ivs_fp d NSd) in PX2;
    repeat match goal with
    | Hc : rw_cells psegs m1 ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells psegs L _ _ _ m1 m2 a cs PX2) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; let a' := fresh "a'" in let Ha' := fresh "Ha'" in intros a' Ha'; left; clear -Ha'; lia
                  | first [ (* [comment removed for export] *) eapply (fp_disjoint_stack psegs L d m1); [exact MDd| exact HBR1| clear -ACL SLO HLS; lia
                              | rewrite Ed; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia]
                          | split; [cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia
                                   | eapply (fp_disjoint_stack psegs L d m1); [exact MDd| exact HBR1| clear -ACL SLO HLS; lia
                                     | rewrite Ed; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia] ] ] ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end;
    clear HBR1 MDd NSd.


  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma spec0_null_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_L ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.Plnw,(=.&40.)Pvw,(=.&40.)Pscj,(20.(=.&8.))Ppj,(20.(=.&8.))Pgj,(20.(=.&8.))Prj,(20.(=.&8.))Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px9,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px18,(=.&40.)Px19,(=.&40.)Px20,(=.&40.)Px21,(=.&40.)Px22,(=.&40.)Px23,(=.&40.)Px24,(=.&40.)Px25,(=.&40.)Px26,(=.&40.)Px27,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(3.$4.VP,=)P,(3.$4.VLEN,=)P,(23.VL,VHI,Vmo0,Vh0,VLB,R26.R25.(17.$21.)R24.R23.)P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R25.)P,(18.$10.R26.VPAR,(24.Vtg,Vpd,VLEN,VP,))P,(18.$10.R27.(7.(11.&40.Vsp,)-200.)(12.$19.(25.#8.R23.)(17.$19.)))P,(18.$10.R28.(7.(11.&40.Vsp,)-1?8.)(12.$19.(25.#<0.R22.)(17.$19.)))P,(18.$10.R29.(7.(11.&40.Vsp,)-138.)(12.$19.(25.#4.R24.)(12.$19.(26.R26.)(17.$19.))))P,(18.$10.R2:.(7.(11.&40.Vsp,)-130.)(12.$19.(1:.R28.)(17.$19.)))P,(18.$10.R2;.(7.(11.&40.Vsp,)-128.)(12.$19.(25.#<0.R24.)(17.$19.)))P,(18.$10.R2<.(7.(11.&40.Vsp,)-68.)(12.$19.(1:.Vs11,)(12.$19.(1:.Vs10,)(12.$19.(1:.Vs9,)(12.$19.(1:.Vs8,)(12.$19.(1:.Vs7,)(12.$19.(1:.Vs6,)(12.$19.(1:.Vs5,)(12.$19.(1:.Vs4,)(12.$19.(1:.Vs3,)(12.$19.(1:.Vs2,)(12.$19.(1:.Vs1,)(12.$19.(1:.Vs0,)(12.$19.(1:.Vra,)(17.$19.)))))))))))))))P,(27.$10.R2=.Vlo,(7.(11.&40.Vsp,)-200.))(28.$10.R2=.(29.$10.VL,VHI,$2:.$2;.$2<.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2=.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(2>.(2?.R26.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,R25.R24.R23.(1;.&40.VPKA,)R22.(1;.&40.VPAR,)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)VF,(1;.&40.+27518.)Vfc,(30.(=.&40.))R2>.(31.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros P0 L0 CX PX HPAR FR0 FRG FRM FRL FRR FR ST.
    dpose CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    pose proof (rw_cells_bound _ _ _ _ HPAR) as PRB. cbn [cells_size csize Nat.add buf_cells] in PRB.
    (* [comment removed for export] *)
    pose proof (P_ecp_group_init_spec P_MT) as SGI. unfold ecp_group_init_stmt, ecp_group_init_post, P_ECP_GROUP_INIT, ECP_GROUP_SIZE in SGI.
    pose proof (munch_refl [(G, G + 192); (lo, bv_unsigned sp + -512)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. zstep. zstep.
    acallx_sp (bv_unsigned sp + -512) (eapply SGI with (A := G) (LB := LBi) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
            [ exact FRG | clear -SPA SPR; lia | clear -SLO HLS ACL ACP; lia | exact ST | clear -SLO HLS; lia | clear -SPA SPR; lia
            | right; clear; lia | exact MI | reflexivity | reflexivity ]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with W : wmono psegs m m1 |- _ => rename W into WM1 end. rename MU into MU1.
    match goal with M : mem_inv psegs m1 |- _ => rename M into MI1 end.
    match goal with Hg : ecp_group_at psegs P_MT m1 LBi _ _ |- _ => rename Hg into HG1 end.
    match goal with S : stk psegs m1 lo _ |- _ => rename S into ST1 end.
    destruct (ctx_munch' _ _ _ _ _ _ _ CX PX MU1 WM1 MI1 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX1 PX1].
    lazymatch type of HG1 with ecp_group_at _ _ _ _ _ (grp_init _ ?idpad' ?pP' ?pA' ?pB' ?pX' ?pY' ?pZ' ?pN' ?hpad') =>
      ddestruct (tmp_ok_init7 m1 LBi G idpad' pP' pA' pB' pX' pY' pZ' pN' hpad' HG1) as (TOK1 & FRH & FRT);
      set (dN := mpd_init (G + 104) pN') in TOK1; set (dP := mpd_init (G + 8) pP') in TOK1; set (dA := mpd_init (G + 24) pA') in TOK1;
      set (dB := mpd_init (G + 40) pB') in TOK1; set (dX := mpd_init (G + 56) pX') in TOK1; set (dY := mpd_init (G + 72) pY') in TOK1;
      set (dZ := mpd_init (G + 88) pZ') in TOK1
    end.
    clear MU1 WM1 CX PX MK HH HT MF SOK IDS SGI HG1 HBR. try clear MI. try clear ST.
    dpose CX1 as (HH & HT & MF & _ & SOK & _ & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    change ([] : list blk) with (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ]) in CX1.
    (* [comment removed for export] *)
    unfold buf_cells in HPAR.
    zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of FRR with rw_cells ?sg ?mx ?A [CB 192 ?j] =>
      change (rw_cells sg mx A [CB 192 j]) with (rw_cells sg mx A ([] ++ CB 192 j :: [])) in FRR;
      apply (rw_cells_split_CB sg mx A [] 192 j [] [8; 184]%nat) in FRR; [| reflexivity]; cbn [mk_CB_cells app] in FRR
    end.
    cb8_to_c8 FRR ([] : list cell).
    chunk_split FRR 1%nat FRP FRR'. rename FRR' into FRR.
    replace (REF + 8) with (bv_unsigned sp + -288) in FRR by (clear; lia).
    pose proof (munch_refl [(REF, REF + 8)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with W : wmono psegs m1 m2 |- _ => rename W into WM2 end. rename MU into MU2.
    match goal with M : mem_inv psegs m2 |- _ => rename M into MI2 end.
    destruct (ctx_munch' _ _ _ _ _ _ _ CX1 PX1 MU2 WM2 MI2 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX2 PX2].
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR1 _].
    pose proof (tmp_ok_munch_fine psegs L _ _ _ _ _ _ _ TOK1 MU2 WM2 (proj1 (proj2 (proj2 (proj2 CX1)))) MI2
                  ltac:(subst dN dP dA dB dX dY dZ; intros d Hd; cbn in Hd; decompose [or] Hd; try contradiction; subst d; cbn; clear; repeat split; lia)
                  ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) HBR1) as TOK2.
    clear MU2 WM2 CX1 PX1 TOK1 MK HH HT MF SOK IDS HBR1. try clear MI1.
    dpose CX2 as (HH & HT & MF & _ & SOK & _ & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    pose proof P_asn1_get_int_empty as SGN. unfold asn1_empty_stmt, asn1_empty_post, P_ASN1_GET_INT in SGN.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. zstep. zstep. zstep.
    acallx (eapply SGN with (PP := REF) (p := P);
       first [ exact FRP | exact MI2 | eassumption | reflexivity | rewrite P0; clear; lia | f_equal; rewrite L0; clear; lia
             | match goal with |- ?g => idtac "GNLEFT" g end ]).
    try clear PC. clear SGN.
    match goal with S : stk psegs m2 lo _ |- _ => rename S into ST3 end.
    lazymatch type of FRR with rw_cells _ _ _ [CB 184 ?j] => set (rj2 := j) in FRR; clearbody rj2 end.
    lazymatch type of FRH with rw_cells _ _ _ [CB 8 ?j] => set (hj := j) in FRH; clearbody hj end.
    lazymatch type of FRT with rw_cells _ _ _ [C8 ?a; C8 ?b; CB 56 ?j] => set (tj := j) in FRT; clearbody tj; set (pb := a) in FRT; clearbody pb end.
    assert (SI3 : SPINV' h LBi m2 mo dN dP dA dB dX dY dZ P lnw vw pb pb scj hj tj pj rj2).
    { split; [exact CX2|]. split; [exact PX2|]. split; [exact TOK2|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact FRP|]. split; [rewrite L0; clear; lia|]. split; [exact FRR|]. split; [exact FRL|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST3]. }
    zstep. if_cases K3; zify_cond K3.
    { exfalso. clear -K3. rewrite ?unsigned_lit in K3 by lia. cbv in K3. lia. }
    eapply spec_erradd'; [exact SI3| clear; lia| exact MK].
  Qed.
End EP.
