(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Bytes MpiCoreAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points U_asn1_get_mpi U_asn1_get_alg_A U_pk_ecparams U_ecp_statics U_ecp_check_pubkey U_ecp_point_read_binary U_pk_ecc_set_pubkey_proof U_pk_parse_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_pk_parse_C () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Stdlib.Lists.List.In"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "newb"; "OSSVerify.KrLib.Spec.RepEcp.modp_ent"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.RepEcp.ecp_kp"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.U.UImg.usegs"; "OSSVerify.KrLib.Spec.RepEcp.ecp_keypair_at"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.RepEcp.kp_mpds"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Spec.RepEcp.kp_blocks"; "OSSVerify.KrLib.USpec.RepPk.pk_rep_c"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "OSSVerify.KrLib.U.U_ecp_defs.U_MT"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "OSSVerify.KrLib.U.U_platform_zeroize.U_MEMSET_FUNC"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.U_BAD_POINTS"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "OSSVerify.KrLib.Spec.RepEcp.ecp_grp"; "OSSVerify.KrLib.Spec.RepEcp.mkKP"; "OSSVerify.KrLib.Spec.RepEcp.mpd_init"; "OSSVerify.KrLib.Spec.RepEcp.pt_init"; "OSSVerify.KrLib.Spec.RepEcp.grp_mpds"; "OSSVerify.KrLib.Spec.RepEcp.grp_blocks"; "OSSVerify.KrLib.U.U_pk_parse_A.pctx"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.U.U_pk_free.U_EC_INFOS"; "OSSVerify.KrLib.Spec.EcpFacts.mpds_apart"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.U.U_ecp_group_load.gl_result"; "OSSVerify.KrLib.U.U_ecp_defs.U_CA"; "OSSVerify.KrLib.U.U_ecp_defs.U_ONE"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "OSSVerify.KrLib.USpec.RepPk.PKC_inst"; "OSSVerify.KrLib.U.U_pk_free.U_RSA_INFO"; "OSSVerify.KrLib.U.U_pk_sinv.U_pk_sinv"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Mem.le4"; "OSSVerify.KrLib.Lib.Mem.le8"; "OSSVerify.KrLib.U.U_ecp_keypair_init.kp_init"].


(* [comment removed for export] *)
Definition blk_eq_dec : forall x y : blk, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Definition newb (LB LB' : list blk) : list blk := List.filter (fun b => if in_dec blk_eq_dec b LB then false else true) LB'.

Lemma newb_in : forall LB LB' b, In b (newb LB LB') <-> In b LB' /\ ~ In b LB.
Proof.
  intros LB LB' b. unfold newb. rewrite List.filter_In. destruct (in_dec blk_eq_dec b LB) as [I|N]; split.
  - intros [_ F]. discriminate F. - intros [_ N]. exfalso. exact (N I). - intros [H _]. exact (conj H N). - intros [H _]. split; [exact H| reflexivity].
Qed.

Lemma newb_perm : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "PLB,(0.(1.$2.$2.))PLB',(0.(1.$2.$2.))P,(3.$2.(4.(1.$2.$2.)$2.(5.$2.$2.)R1.))P,(3.$2.(4.(1.$2.$2.)$2.(5.$2.$2.)R3.))P,Pb,(1.$2.$2.)P,(6.(1.$2.$2.)R1.R5.)(6.(1.$2.$2.)R2.R5.)(7.(1.$2.$2.)R4.(8.$9.(:.R5.R4.)R5.))")
(* [comment removed for export] *).
Proof.
  intros LB LB' ND' ND SUB. apply perm_of_sets; [exact ND'| |].
  - apply (nodup_fst_of_sub _ LB' ND').
    + intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (proj1 (newb_in _ _ _) Hb))| apply SUB; exact Hb].
    + apply NoDup_app; [apply List.NoDup_filter; apply (NoDup_map_inv fst); exact ND'| apply (NoDup_map_inv fst); exact ND|].
      intros b Hb HbL. exact (proj2 (proj1 (newb_in _ _ _) Hb) HbL).
  - intros b. rewrite in_app_iff, newb_in. split.
    + intros Hb. destruct (in_dec blk_eq_dec b LB) as [I|N]; [right; exact I| left; exact (conj Hb N)].
    + intros [[Hb _]|Hb]; [exact Hb| apply SUB; exact Hb].
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L52919434315.2000005S1L1H". (* [comment removed for export] *)
Lemma alloc_ceiling_lt {L : heap_layout} : alloc_ceiling < 2^63.
Proof. pose proof (@alloc_ceiling_bounds L). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ec_rep_intro : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "PMT,(0.$;.)PRSAI,$2.PECIS,(0.$2.)Pm,P,(<.&40.)(=.(<.&8.))PLBx,(0.(1.$2.$2.))PPKA,$2.PC,$2.Pk,$>.Pinfo,$2.Powned,(0.(1.$2.$2.))P,(6.$2.R2.R8.)P,(?.(10.$2.R3.=))P,(11.$12.R9.)P,(3.$2.(4.(1.$2.$2.)$2.(5.$2.$2.)R9.))P,(13.$12.R>.R;.R:.R8.R7.)P,(6.(1.$2.$2.)(14.$2.$2.R9.+100.)R;.)P,Pd1,$15.Pd2,$15.P,(6.$15.R2.(16.R;.))P,(6.$15.R2.(16.R<.))P,(?.(10.$2.(17.R4.)(17.R3.)))P,(10.$18.(19.R5.)$1:.)P,(10.$18.(19.R5.)$1:.)(?.(10.(1.$2.$2.)(14.$2.$2.(1;.R7.)(1<.+4.(1=.R7.)))(14.$2.$2.(1;.R6.)(1<.+4.(1=.R6.)))))P,Pd,$15.P,(6.$15.R1.(16.R;.))P,(10.$18.(19.R2.)$1:.)(?.(10.(1.$2.$2.)(14.$2.$2.(1;.R3.)(1<.+4.(1=.R3.)))(14.$2.$2.R>.+100.)))P,(10.$2.(1>.R<.+10.)=)P,(1?.(20.R=.+100.)(21.+2.+40.))P,Pb,(1.$2.$2.)(22.(6.(1.$2.$2.)R1.R<.)(6.(1.$2.$2.)R1.(23.(1.$2.$2.)(14.$2.$2.R?.+100.)(24.R>.))))(25.$12.R14.R13.R15.R12.R11.R10.R=.R?.R<.)")
(* [comment removed for export] *).
Proof.
  intros MT RSAI ECIS m LBx PKA C k info owned EI NI MI ND KP CIN DIS NC AL C64 OWN.
  assert (BLK : forall d, In d (kp_mpds k) -> md_own d = LHeap -> In (md_p d, 4 * md_n d) LBx).
  { intros d Hd O. dpose (kp_mpds_mpdr usegs MT m LBx C k d KP Hd) as (_ & _ & _ & _ & _ & HO). rewrite O in HO. exact (proj1 (proj2 HO)). }
  right; right. split; [exact EI|]. split; [exact NI|]. split; [exact MI|]. exists k.
  split; [exact KP|]. split; [exact CIN|]. split.
  { intros d1 d2 H1 H2 NE O1 O2 E. apply (DIS d1 d2 H1 H2 NE O1 O2). rewrite E. f_equal.
    exact (nodup_fst_same LBx (md_p d2) (4 * md_n d1) (4 * md_n d2) ND ltac:(rewrite <- E; exact (BLK d1 H1 O1)) (BLK d2 H2 O2)). }
  split. { intros d Hd O E. apply (NC d Hd O). rewrite E. f_equal. exact (nodup_fst_same LBx C (4 * md_n d) 256 ND ltac:(rewrite <- E; exact (BLK d Hd O)) CIN). }
  split; [exact AL|]. split; [exact C64| exact OWN].
Qed.

Notation MT := U_MT (only parsing).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L17512215678.5L19337450167.5L2686763790.3 L35495549846.3L40825464044.5L66392575453.800000300900?00@00A00IS1uS1u2HuS1u2HuSSS1u1x2X4". (* [comment removed for export] *)
Lemma land_m5_9 : forall u, 0 <= u < 2^64 -> Z.land u 18446744073709551611 = 9 -> u = 9 \/ u = 13.
Proof.
  intros u Hu H.
  assert (E1 : Z.ldiff u 4 = 9).
  { rewrite Z.ldiff_land. change (Z.lnot 4) with (-5). rewrite <- (land_mod_pow2_r u (-5) 64) by lia. exact H. }
  pose proof (Z.lor_ldiff_and u 4) as E2. rewrite E1 in E2.
  set (x := Z.land u 4) in *.
  assert (X4 : 0 <= x <= 4). { subst x. split; [apply Z.land_nonneg; lia|]. rewrite Z.land_comm. apply MpiCoreAux.land_le_l; lia. }
  assert (XX : Z.land x 4 = x). { subst x. rewrite <- Z.land_assoc. rewrite (Z.land_diag 4). reflexivity. }
  assert (X04 : x = 0 \/ x = 4).
  { assert (C5 : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4) by lia.
    destruct C5 as [E|[E|[E|[E|E]]]]; rewrite E in XX |- *; cbn in XX; first [left; reflexivity| right; reflexivity| discriminate XX]. }
  clearbody x. destruct X04 as [-> | ->]; cbn in E2; [left| right]; symmetry; exact E2.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section PA.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis HL : ecp_ids_lok L U_ECP_IDS_DONE U_ECP_IDS.
  Hypothesis HMC : mc_lok L U_MUL_COUNT.
  (* [comment removed for export] *)
  Hypothesis HPERM : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "Ph,(26.$12.VL,VHI,)PLB,(0.$9.)PLB',(0.$9.)Pm,P,(<.&40.)(=.(<.&8.))Pmo,$27.P,(28.$12.VL,VHI,R5.R4.R2.R1.)P,(7.$9.R5.R4.)(29.(26.$12.VL,VHI,)Lh',(26.$12.VL,VHI,)(2:.(28.$12.VL,VHI,R1.R6.R5.R4.)(10.$2.(2;.$12.VL,VHI,R1.)(2;.$12.VL,VHI,R8.))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis CA_MSF : const_at L U_MEMSET_FUNC 8.
  Hypothesis CA_RSA0 : const_at L U_RSA_INFO 4.
  Hypothesis CA_RSA72 : const_at L (U_RSA_INFO + 72) 8.
  Hypothesis CA_RSA80 : const_at L (U_RSA_INFO + 80) 8.
  Hypothesis CA_EC0 : forall e, In e U_EC_INFOS -> const_at L e 4.
  Hypothesis CA_EC72 : forall e, In e U_EC_INFOS -> const_at L (e + 72) 8.
  Hypothesis CA_EC80 : forall e, In e U_EC_INFOS -> const_at L (e + 80) 8.
  Hypothesis CAT_ECGRP : const_at L U_OID_EC_GRP_TBL 440.
  Hypothesis CAT_PKALG : const_at L U_OID_PK_ALG_TBL 120.
  Hypothesis CAT_ECALGID : const_at L U_OID_EC_GRP_ALGID_TBL 80.
  Hypothesis CA_PKTBL : const_at L U_PK_INFO_TBL 32.
  Hypothesis CA_BP : const_at L U_BAD_POINTS 32.
  (* [comment removed for export] *)
  Hypothesis HPRB : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "(2<.$12.VL,VHI,$2=.$2>.$2?.+5<?:8.$30.)")
(* [comment removed for export] *).
  Hypothesis HCPK : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "(31.$12.VL,VHI,$2=.$32.$2?.+5<?:8.$33.$34.)")
(* [comment removed for export] *).

  Notation SI := (U_pk_sinv L HL HMC).
  Notation PK := (PKC_inst usegs U_RSA_INFO U_EC_INFOS MT).
  Notation XS := [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_MUL_COUNT, U_MUL_COUNT + 8); (U_ECP_IDS, U_ECP_IDS + 56)].

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (mo0 : Model) (h0 : HST usegs L HI) (LB : list blk) (PP P END BUF PKA lo : Z) (bs : list byte).
  Hypothesis HH0 : HEAP usegs L HI h0 LB m0 mo0.
  Hypothesis HPP0 : rw_cells usegs m0 PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALPP : PP mod 8 = 0.
  Hypothesis HBS0 : bytes_at usegs m0 BUF bs.
  Hypothesis INB : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis BP : BUF <= P.
  Hypothesis PE : P <= END.
  Hypothesis EB : END <= BUF + Z.of_nat (length bs).
  Hypothesis B63 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis HPKA0 : rw_cells usegs m0 PKA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis SPP : bv_unsigned sp <= PP.
  Hypothesis PPT : PP + 8 <= heap_top usegs L HI h0.
  Hypothesis SPK : bv_unsigned sp <= PKA.
  Hypothesis PKT : PKA + 16 <= heap_top usegs L HI h0.
  Hypothesis DPK : PP + 8 <= PKA \/ PKA + 16 <= PP.
  Hypothesis ST0 : stk usegs m0 lo (bv_unsigned sp).
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - PK_PARSE_STACK - hl_stack L.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis MI0 : mem_inv usegs m0.
  Hypothesis SOK0 : statics_ok usegs L m0.
  Hypothesis SIP0 : pk_sinv_P m0.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis DKB : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis DPB : PKA + 16 <= BUF \/ BUF + Z.of_nat (length bs) <= PKA.
  Hypothesis NZPP : 0 < PP.
  Hypothesis NZP : 0 < PKA.
  Hypothesis DSPP : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis DSB : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h0) PP 8.
  Hypothesis CWP : client_wrange L LB lo (heap_top usegs L HI h0) PKA 16.
  Hypothesis CRB : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis SPR : bv_unsigned sp < 2^64.

  Notation POST := (pk_parse_subpubkey_post usegs L HI PK SI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0).
  Notation FRS mm := (rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FP := ([(PP, PP + 8); (PKA, PKA + 16)] ++ XS).

Notation pa_basics' := (pa_basics L HI HLS sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI).
  Notation pctx' := (pctx L HI sp m0 mo0 h0 LB PP PKA).
  Notation pctx_munch' := (pctx_munch L HI HLS HL HMC sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO HTOP DHI CWPP CWP).
  Notation ret_walk' := (ret_walk L HI HLS HL HMC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 INB BP PE EB BUF0 SPP SPK DPK ACL SLO DHI DKB DPB NZPP NZP DSPP DSP DSB).
  Notation early_walk' := (early_walk L HI HLS HL HMC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 INB BP PE EB BUF0 SPP SPK DPK ACL SLO DHI DKB DPB NZPP NZP DSPP DSP DSB).
  Notation fail_free_walk' := (fail_free_walk L HI HFREE HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA80 CA_EC80 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 INB BP PE EB BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP SPR).
  Notation pctx_bytes' := (pctx_bytes L HI HLS DIMG HL HMC sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 HBS0 INB SPP SPK ACL SLO DHI DKB DPB CRB).
  Notation keep_frame' := (keep_frame L sp).
  Notation keep_pp' := (keep_pp L HI sp h0 LB PP lo DSPP CWPP).
  Notation keep_pka' := (keep_pka L HI sp h0 LB PKA lo DSP CWP).
  Notation fresh_not_client' := (fresh_not_client L HI HLS DIMG sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI).
  Notation fresh_apart_pp' := (fresh_apart_pp L HI HLS DIMG sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI CWPP).
  Notation fresh_apart_pka' := (fresh_apart_pka L HI HLS DIMG sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI CWP).
  Notation blk_apart_pp' := (blk_apart_pp L HI DIMG h0 LB PP lo ACL CWPP).
  Notation heap_presx_weak'' := (heap_presx_weak' L ra sp LB PP P END BUF PKA bs BP PE EB DPK DKB DPB NZPP NZP).
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.
  #[using="HL"] Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 HL). Qed.
  #[using="L HL"] Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 HL)). Qed.
  #[using="HL"] Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 HL))). Qed.
  #[using="HMC"] Lemma ML1 : hl_data_lo L <= U_MUL_COUNT. Proof. exact (proj1 HMC). Qed.
  #[using="HMC"] Lemma ML2 : U_MUL_COUNT + 8 <= hl_data_hi L. Proof. exact (proj1 (proj2 HMC)). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma kpi_heap_grp : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "PC,$2.Pg,$35.Ppd,(<.&40.)PqX,(<.&40.)PqY,(<.&40.)PqZ,(<.&40.)Pd,$15.P,(6.$15.R1.(16.(36.R6.(37.(20.R7.+<0.)R5.)(38.(20.R7.+=0.)R4.R3.R2.))))P,(10.$18.(19.R2.)$1:.)(6.$15.R3.(39.R8.))")
(* [comment removed for export] *).
  Proof.
    intros C g pd qX qY qZ d Hd O. unfold kp_mpds in Hd. cbn [kp_grp kp_d kp_Q] in Hd. apply in_app_or in Hd. destruct Hd as [Hd|Hd]; [exact Hd|].
    exfalso. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn in O; discriminate.
  Qed.
  #[using="Type"] Lemma kpi_blocks : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "PC,$2.Pg,$35.Ppd,(<.&40.)PqX,(<.&40.)PqY,(<.&40.)PqZ,(<.&40.)(10.(0.$9.)(24.(36.R5.(37.(20.R6.+<0.)R4.)(38.(20.R6.+=0.)R3.R2.R1.)))(3:.R5.))")
(* [comment removed for export] *).
  Proof. intros. unfold kp_blocks. cbn [kp_grp kp_d kp_Q]. unfold pt_blocks. cbn. rewrite app_nil_r. reflexivity. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma grp_blk_in : forall g d, In d (grp_mpds g) -> md_own d = LHeap -> In (md_p d, 4 * md_n d) (grp_blocks g).
  Proof. intros g d Hd O. unfold grp_blocks. apply in_flat_map. exists d. split; [exact Hd|]. rewrite (mpd_blk_heap d O). left; reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02L0@D34028600543.211D37216054521.209D37226362885.211D41355788639.211D47139703723.209D61281570664.211D61556549392.211D61571118060.209D63898547005.211D9797143268.212 L10003311324.3  L10015296529.7  L10472341635.213L1077460508.1   L11423978205.12 L11478878833.7  L11492060348.2  L11579565607.1  L11583641897.12 L11585737858.5  L11585737858.7  L11604501807.2  L11881533423.15 L11886305925.4  L11892015684.10 L11892015684.8  L12185525866.2  L14372944785.6  L15320336567.3  L15783951668.3  L17059565736.0  L1709264443.8   L1725003874.1   L17468603376.5  L17475029333.1  L17479087707.12 L17751513212.16 L17762329926.12 L17766491352.3  L18274053436.5  L18274053436.7  L18284535959.11 L18933043916.4  L1917911384.5   L19203646566.4  L19979836608.14 L20592880768.7  L20594975019.11 L20597072155.2  L22052548753.6  L23445226910.4  L23778900769.0  L2397676628.0   L24444476101.3  L24746614092.12 L24750662210.1  L24761290983.5  L24761290983.7  L25584779078.10 L25873462220.5  L25873462220.7  L25879643616.1  L25883950695.12 L27644520960.8  L29010571016.161L31161988459.170L32029494421.10 L33768578310.3  L34632187794.6  L34806988770.1  L35188131620.2  L3582028444.1   L36430635735.4  L37317392303.8  L37334681915.170L37339008021.213L37502268859.3  L38891255949.5  L38901698209.2  L39466114793.14 L39467843354.3  L39472115522.8  L39472403266.7  L39472403266.9  L39567207272.6  L4111208532.11  L4114706726.1   L41202929119.171L41202929119.200L4125892095.6   L41320204299.10 L41514427527.2  L43300649301.0  L44075892968.12 L44080302334.15 L44145255421.3  L45961560139.8  L46716081219.15 L49728944076.8  L51066652574.6  L51158950247.3  L53271535775.200L55216948638.7  L55227435061.12 L55229532165.3  L555939825.3    L56310033514.8  L56892130782.4  L56894227950.13 L56904714309.9  L57381299516.7  L57391786135.11 L57393883303.2  L57701871804.0  L5873661889.4   L5873892567.12  L5884166637.17  L59240035548.8  L59314873579.2  L59315137787.1  L59525066331.5  L60087886610.14 L60972063020.5  L60972566735.12 L61275282840.202L62586298816.3  L627073308.5    L62768742067.16 L62772933416.5  L62779016073.12 L62835326901.4  L629173431.12   L633476025.1    L64511515182.16 L64521924354.14 L65348482612.1  L65351391046.12 L65361585901.8  L65361877741.6  L65361877741.8  L65821241403.5  L65823338507.14 L65825439136.9  L66151418569.3  L66389975894.12 L66394053720.1  L66400464637.5  L66718479728.8  L7036479304.1   L7434295329.12  L7438346031.1   L7448974730.5   L7448974730.7   L8322245898.4   L9782466580.203 L9797143268.203 00000]01<01j02W03103203[04505H05I05J05K05L05P06506606706806906:06;06A06B06C06D06E06K06^06g06o07007H07L07M07N07O07P07Q07R07S07T07U07[07\07]07^07_07`07a08408508608708808908:08;08<08Q08R08j08k08l08m08n0:U0:c0:k0:l0;00;10;50;C0;a0=H0?20?=0?O0?P0?Q0?R0?`0?a0?b0?c0@=0@>0@U0@l0@m0AE0AF0AG0Ac0Ad0Al0BD0BE0BV0BW0Bc0C:0C;0C<0C=0CE0Ca0Cb0Cc0Cd0Ce0DA0DB0DC0DD0DE0DF0Dc0Dh0Dk0E;0E`0Ea0F:0Ff0G10G20GU0GV0GW0GX0GY0GZ0H;0H<0H=0H>0HF0HG0HH0HI0HJ0HK0HT0HU0HV0HW0HX0H\0H]0H^0H_0H`0I20JC0JDS2ra2sp2PP3PKA2bs3SPP1C2E23kbs2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs4NZPP1C3kbs2HBS2ra2sp2PP3PKA2bs4NZPP1C2E23kbs2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPP1C2E23kbs2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C3kbs2HBFS2ra2sp2PP3PKA2bs1C2E23kbs2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C3kbs2HBS1L3HLS2ra2sp2PP3PKA2lo2bs3SPP3ACL3DHI4NZPP3NZP1C2E23ACP4SLO'2C03kbs2HB5Ha_st5Hl_stFFFFS2spS1P3END3BUF2bs2BP2EB1p2E22PB3E2B1a2HaFFFFFFS2id1XFFFFS1d2N1S1P3END1p2E22PB3E2BS1r2RR2NZS2PP1d1QSS1L1C3CIM2I12I33E1'4E2''S2spFFFFFFFFFS1r2r3FFFFFFS1P3END1p2E22PB3E2BFSSFFFFFS1P3BUF2bs2BP1p2E22PBFS1L1C3CIM2M12M23E1'4E2''FFSFS1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22PB3E2B3ACP3BAC4SLO'2C03kbs4LENKS1P2bs1p2E22PBS2PP1C1QFS2spFS2spS1L1C3CAC4ACLTS1L3HLS2sp2lo3ACL3SPR3ACP4SLO'S1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22PB3E2B3ACP3BAC4SLO'2C03kbs4LENKS1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22PB3E2B3ACP3BAC4SLO'2C03kbs4LENK2KES2r33RR32NZS1L1C3CIM3E1'4E2''FFFS1L2sp2lo4SLO'FFFS1P3BUF2bs2BP4BUF01p2E22PBFS2ra2sp2PP3PKA2bs1C3kbsS2ra2sp2PP3PKA2bs1C3kbsFS3END3BUF2bs2EB1p2E23E2BFSS3END3BUF2bs2EB1C1p2E23E2B1QFS1C1a2HaS1L1C3CIM2I12I33E1'4E2''FS1L2HI2sp2h04HTOPFS2sp3PKA3SPKS2ra2sp2PP3PKA2bs1C3kbsFFFS2PP1C1QS1L3HLS2sp2lo3ACL1C4SLO'3CACFFFFS3END3BUF2bs2EB3B631p2E23E2BFFFFFS1L3HLS2sp2lo3ACL3DHI4SLO'2M2S1C1HS1XS1L2PP3PPD2M12M2S1L3END3BUF2lo2bs2EB3ACL1p2E23E2B3BACFS1P3BUF2bs2BP1C1p2E22PB1QS2ra2sp2PP3PKA2bs1C2E23kbs2HB5Ha_st5Hl_st2HDS2r33RR32HqFS1L3END3BUF2bs2EB1p2E23E2B1Q2M13E1'FFFFFS1L1P3BUF2bs2BP1p2E22PB1Q2M24E2''FFFS2sp3SPAFFFFFS1r2RR2HqFFFSS2spFFFFS1r2RR1q2Hq2r33RR3S1L3HLS2ra2sp2PP3PKA2lo2bs3SPP3NZP1C2E24SLO'2C03kbs2HB5Ha_st5Hl_st2HD3BUF3ACL3BACF". (* [comment removed for export] *)
  #[using="HFREE HLS SW DIMG HND HPERM CA_MSF CA_RSA80 CA_EC80 CA_BP HPRB HCPK BUF bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR"] Lemma ec_fin_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (LB2 : @Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (C : @Corelib.Numbers.BinNums.Z), forall (p :
    @Corelib.Numbers.BinNums.Z), forall (E2 : @Corelib.Numbers.BinNums.Z), forall (info : @Corelib.Numbers.BinNums.Z), forall (r : @Corelib.Numbers.BinNums.Z), forall (g :
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.ecp_grp), forall (NB : @Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (pd :
    @stdpp.bitvector.definitions.bv 64%N), forall (qX : @stdpp.bitvector.definitions.bv 64%N), forall (qY : @stdpp.bitvector.definitions.bv 64%N), forall (qZ :
    @stdpp.bitvector.definitions.bv 64%N), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 : @stdpp.bitvector.definitions.bv 64%N), forall
    (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x12 : @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x15 : @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 :
    @stdpp.bitvector.definitions.bv 64%N), forall (p0 : @Corelib.Numbers.BinNums.Z), forall (x20 : @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv
    64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 : @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N),
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0 mo0 h0 LB PP PKA h LB2 m mo -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.ecp_keypair_at
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m LB2 C (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.mkKP g
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.mpd_init (@Stdlib.ZArith.BinInt.Z.add C 192%Z) pd) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.pt_init
    (@Stdlib.ZArith.BinInt.Z.add C 208%Z) qX qY qZ)) -> @Stdlib.Lists.List.In (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB2 -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.block_range L C 256%Z ->
    (forall (B : @Corelib.Numbers.BinNums.Z), forall (k : @Corelib.Numbers.BinNums.Z), @Stdlib.Lists.List.In (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z)
    (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) B k) LB -> @Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le
    (@Stdlib.ZArith.BinInt.Z.add C 256%Z) B) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add B k) C)) -> @Stdlib.Lists.List.In (@Corelib.Numbers.BinNums.Z) info
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.EcpFacts.mpds_apart (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.grp_mpds
    g) -> @Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.grp_blocks g) NB
    -> (forall (b : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk), @Corelib.Init.Logic.iff (@Stdlib.Lists.List.In (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b LB2)
    (@Corelib.Init.Logic.or (@Stdlib.Lists.List.In (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b NB) (@Stdlib.Lists.List.In
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB)))) -> (forall (b : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk),
    @Stdlib.Lists.List.In (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b NB -> @Corelib.Init.Logic.not (@Stdlib.Lists.List.In
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB))) -> (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) r 0%Z ->
    @Corelib.Init.Logic.ex (@Corelib.Numbers.BinNums.Z) (fun (id : @Corelib.Numbers.BinNums.Z) => @Corelib.Init.Logic.and (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le 0%Z id)
    (@Stdlib.ZArith.BinInt.Z.lt id (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_group_load.gl_result
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_CA) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_ONE) id C 0%Z g NB))) -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.lt (@Stdlib.ZArith.BinInt.Z.opp (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.le r 0%Z) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p E2) -> @Stdlib.ZArith.BinInt.Z.le E2 END ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N info); @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N C)] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat lj] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-48)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le BUF p0) (@Stdlib.ZArith.BinInt.Z.le p0 END) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) (@stdpp.bitvector.definitions.Z_to_bv 64%N PP) (@stdpp.bitvector.definitions.Z_to_bv 64%N r) x11 x12 x13
    x14 x15 x16 x17 (@stdpp.bitvector.definitions.Z_to_bv 64%N E2) (@stdpp.bitvector.definitions.Z_to_bv 64%N p0) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x294c4%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros m mo h LB2 C p E2 info r g NB pd qX qY qZ lj x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 p0 x20 x28 x29 x30 x31
      w_ctx w_key w_cin w_brange w_apart w_info w_mpds w_nb w_split w_fresh w_load w_rr w_pcell w_prange w_end w_pk w_low w_saved w_stk w_p0.
    clear HCALLOC CA_RSA0 CA_RSA72 CA_EC0 CA_EC72 CAT_ECGRP CAT_PKALG CAT_ECALGID CA_PKTBL HPP0 ALPP HPKA0 PPT ST0 MI0 SOK0 SIP0 RA.
    pose proof w_ctx as (w_heap & w_top & w_mof & w_mi & w_sok & w_sinv & w_grow & w_keep).
    pose proof (heap_mok _ _ HI _ _ _ _ w_heap) as w_mok.
    pose proof (HND _ _ _ _ w_heap) as w_nd.
    pose proof w_brange as (w_c0 & w_c16 & _ & w_cac & w_cim).
    pose proof alloc_ceiling_lt as w_ceil.
    assert (w_info0 : info <> 0).
    { intros w_z. subst info. revert w_info. cbn. intuition discriminate. }
    assert (w_cnot : ~ In (C, 256) LB).
    { intros w_c. destruct (w_apart C 256 w_c) as [w_x|w_x]; clear -w_x; lia. }
    (* the blocks this function owns: those of LB2 that the caller did not pass in *)
    assert (w_own : forall b, In b (newb LB LB2) <-> In b ((C, 256) :: NB)).
    { intros b. rewrite newb_in. split.
      - intros [w_in2 w_out]. apply w_split in w_in2. destruct w_in2 as [w_n|[w_c|w_l]].
        + right. exact w_n.
        + left. exact w_c.
        + exfalso. exact (w_out w_l).
      - intros [w_c|w_n].
        + subst b. exact (conj w_cin w_cnot).
        + split; [apply w_split; left; exact w_n|].
          intros w_l. apply (w_fresh b w_n). right. exact w_l. }
    assert (w_rep : forall mx LBx, mem_inv usegs mx -> List.NoDup (map fst LBx) -> In (C, 256) LBx ->
              ecp_keypair_at usegs U_MT mx LBx C (mkKP g (mpd_init (C + 192) pd) (pt_init (C + 208) qX qY qZ)) ->
              pk_rep_c usegs U_RSA_INFO U_EC_INFOS U_MT mx LBx PKA info C (newb LB LB2)).
    { intros mx LBx w_mix w_ndx w_cx w_kx.
      apply (ec_rep_intro U_MT U_RSA_INFO U_EC_INFOS mx LBx PKA C _ info (newb LB LB2) w_info w_info0 w_mix w_ndx w_kx w_cx).
      - intros d1 d2 w_d1 w_d2 w_ne w_o1 w_o2 w_eq.
        apply (w_mpds d1 d2 (kpi_heap_grp _ _ _ _ _ _ d1 w_d1 w_o1) (kpi_heap_grp _ _ _ _ _ _ d2 w_d2 w_o2) w_ne w_o1 w_o2).
        injection w_eq as w_peq _. exact w_peq.
      - intros d w_d w_o w_eq.
        pose proof (grp_blk_in g d (kpi_heap_grp _ _ _ _ _ _ d w_d w_o) w_o) as w_gb.
        rewrite w_nb, w_eq in w_gb. apply (w_fresh _ w_gb). left. reflexivity.
      - exact w_c16.
      - clear -w_cac w_ceil. lia.
      - intros b. rewrite w_own, kpi_blocks, w_nb. reflexivity. }
    zstep.
    if_cases w_br; zify_cond w_br.
    { (* a nonzero code from the group load: free the context and return it *)
      eapply fail_free_walk' with (LBc := LB2) (owned := newb LB LB2) (info := info) (ctx := C) (p' := p);
        [ exact w_ctx | apply newb_perm; [exact w_nd| exact (HND _ _ _ _ HH0)| exact w_grow] | | exact w_pcell | clear -w_prange w_end; lia | exact w_pk
        | | exact w_low | exact w_saved | exact w_stk ].
      - clear -w_rr w_br. lia.
      - apply (pk_rep_c_frame _ _ _ _ m m LB2 _ _ _ _ _ (w_rep m LB2 w_mi w_nd w_cin w_key) w_mi).
        + intros b w_b. apply in_or_app. left. exact w_b.
        + intros a _. reflexivity. }
    assert (w_r0 : r = 0) by (clear -w_rr w_br; lia). subst r.
    destruct (w_load eq_refl) as (id & w_idr & w_gl).
    assert (w_id13 : 1 <= id <= 13).
    { destruct w_gl as [(_ & _ & w_x & _)|[(_ & [w_x|w_x] & _)|[(w_x & _)|(w_x & _)]]];
        [exact w_x| subst id; lia| subst id; lia| discriminate w_x| discriminate w_x]. }
    pose proof (pctx_bytes' h LB2 m mo w_ctx) as w_bytes.
    pose proof pa_basics' as (w_ac4096 & w_bufac & w_bufimg & w_ppdat & w_pkdat & w_room).
    pose proof DI1 as w_di1. pose proof DI2 as w_di2. pose proof ML1 as w_ml1. pose proof ML2 as w_ml2.
    assert (w_spu : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112).
    { apply unsigned_lit. clear -w_room ACL w_ac4096 HLS SPR. lia. }
    destruct (bytes_at_sub m BUF bs (p - BUF) (E2 - p) w_bytes) as [w_xs w_xsl];
      [clear -w_prange BP; lia| clear -w_prange; lia| clear -w_prange w_end EB; lia|].
    set (xs := firstn (Z.to_nat (E2 - p)) (skipn (Z.to_nat (p - BUF)) bs)) in w_xs, w_xsl.
    replace (BUF + (p - BUF)) with p in w_xs by (clear; lia).
    assert (w_xsz : Z.of_nat (length xs) = E2 - p) by (rewrite w_xsl; clear -w_prange; lia).
    clearbody xs. clear w_xsl.
    pose proof w_sinv as (w_ids & cnt & w_mc).
    pose proof (U_bad_points_ok L LB2 m w_sok CA_BP w_mi) as (w_bp1 & w_bp2).
    pose proof (U_pk_ecc_set_pubkey_spec L HI HLS DIMG U_MT HPRB HCPK) as w_spk.
    unfold pk_ecc_set_pubkey_stmt, U_PK_ECC_SET_PUBKEY in w_spk.
    zstep. zstep. zstep. zstep.
    eapply aevtM_cut.
    { eapply w_spk with (h := h) (LB := LB2) (PKA := PKA) (info := info) (C := C) (id := id) (lo := lo) (B := p) (bs := xs)
        (g := g) (pd := pd) (qX := qX) (qY := qY) (qZ := qZ) (cnt := cnt) (bp1 := U_bp1) (bp2 := U_bp2);
        rewrite ?w_spu;
      [ exact w_heap | exact w_pk | exact ALP | exact NZP
      | clear -DSP; lia
      | rewrite w_top; exact (client_wrange_mono L LB LB2 lo (heap_top usegs L HI h0) PKA 16 CWP w_grow)
      | exact (fresh_apart_pka' C 256 w_brange w_apart ltac:(lia))
      | exact w_pkdat
      | exact w_key
      | exact w_cin
      | unfold ECP_KEYPAIR_SIZE; clear -w_cim w_di1 w_di2; lia
      | rewrite w_nb; exact w_gl
      | exact (U_curve_statics m id w_mi w_id13)
      | exact w_xs
      | clear -w_prange BP BUF0; lia
      | rewrite w_xsz; clear -w_prange w_end EB B63; lia
      | rewrite w_xsz; apply (client_range_blk L LB2 lo BUF (Z.of_nat (length bs)) p (E2 - p) (w_grow _ INB)); clear -w_prange w_end EB BP; lia
      | rewrite w_xsz; clear -DSB w_prange w_end EB BP; lia
      | rewrite w_xsz; unfold ECP_KEYPAIR_SIZE; destruct (w_apart _ _ INB) as [w_q|w_q]; clear -w_q w_prange w_end EB BP; lia
      | rewrite w_xsz; clear -w_bufimg w_di1 w_di2 w_ml1 w_ml2 w_prange w_end EB BP; lia
      | exact w_mc
      | exact w_ml1
      | exact w_ml2
      | intros a w_a; destruct (proj2 (proj2 HMC) a w_a) as [w_w w_s]; exact (conj w_s w_w)
      | unfold ECP_KEYPAIR_SIZE; clear -w_cim w_di1 w_di2 w_ml1 w_ml2; lia
      | exact w_bp1
      | exact w_bp2
      | exact (proj1 CA_BP)
      | exact (proj1 (proj2 CA_BP))
      | intros a w_a w_st; exact (proj2 (proj2 CA_BP) a w_a (SW a w_st))
      | unfold U_BAD_POINTS; clear; lia
      | exact w_stk
      | clear -SLO HLS; unfold PK_PARSE_STACK in SLO; lia
      | exact ACL
      | rewrite w_top; clear -HTOP; lia
      | clear -SPA; lia
      | exact DHI
      | exact TP
      | exact w_mi
      | vm_compute; reflexivity
      | exact w_sok
      | exact CA_MSF
      | reflexivity
      | reflexivity
      | rewrite w_xsz; reflexivity ]. }
    intros ms1 mo1 w_post. unfold pk_ecc_set_pubkey_post in w_post.
    destruct w_post as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & mo1' & h1 & LB3 & Q1 & r1 & cnt1 &
      w_cfg & w_rr1 & w_mi1 & w_stk1 & w_mof1 & w_top1 & w_heap1 & w_key1 & w_qf & w_qsg & w_qdis & w_grow1 & w_back1 & w_newq & w_pk1 & w_px1 & w_sok1 & w_mc1).
    injection w_cfg as -> ->.
    rewrite w_spu in w_stk1, w_px1.
    rewrite (ret_pc_even 169176) by (first [lia | reflexivity]).
    pose proof (heap_mok _ _ HI _ _ _ _ w_heap1) as w_mok1.
    assert (w_ppfar : PP + 8 <= C ∨ C + 256 <= PP) by exact (fresh_apart_pp' C 256 w_brange w_apart ltac:(lia)).
    assert (w_pcell1 : rw_cells usegs m1 PP [C8 (Z_to_bv 64 p)]).
    { apply (keep_pp' LB2 (bv_unsigned sp + -112) _ m m1 _ w_px1 w_grow ltac:(lia) w_pcell eq_refl).
      cbn [disjoint_from]. split; [clear -w_ppfar; lia|]. split; [clear -w_ppdat w_ml1 w_ml2; lia| exact I]. }
    assert (w_xfar : Forall (fun iv : Z * Z => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C + 208, C + 256); (380840, 380840 + 8)]).
    { apply Forall_cons; [cbn [fst snd]; left; clear -w_cac ACL w_room HLS; lia|].
      apply Forall_cons; [cbn [fst snd]; left; clear -ACL w_room HLS w_ml2 DHI; lia|]. apply Forall_nil. }
    assert (w_low1 : rw_cells usegs m1 (bv_unsigned sp + -112) [CB 64 lj]).
    { apply (keep_frame' LB2 (bv_unsigned sp + -112) _ m m1 _ _ w_px1 ltac:(lia) w_low ltac:(lia)); [cbn; lia| exact w_xfar]. }
    assert (w_saved1 : FRS m1).
    { apply (keep_frame' LB2 (bv_unsigned sp + -112) _ m m1 _ _ w_px1 ltac:(lia) w_saved ltac:(lia)); [cbn; lia| exact w_xfar]. }
    clear w_pcell w_low w_saved w_pk.
    (* the static invariant survives the call: the id list is outside its footprint *)
    assert (w_ids1 : ecp_ids_state usegs U_ECP_IDS_DONE U_ECP_IDS m1).
    { destruct w_ids as (w_b & w_bsl & w_i1 & w_i2 & w_iv).
      pose proof HL as (w_l1 & w_l2 & w_l3 & w_l4).
      exists w_b, w_bsl. split; [| split; [| exact w_iv]].
      - apply (heap_presx_rw_cells _ _ _ _ _ m m1 _ _ w_px1 w_i1).
        + intros a w_a. right. left. cbn in w_a. destruct (w_l4 a ltac:(clear -w_a; lia)) as [_ w_ns].
          split; [clear -w_a w_l1 w_l2 w_l3; lia| exact w_ns].
        + cbn. unfold U_ECP_IDS_DONE in *. split; [clear -w_cim w_di1 w_di2 w_l1 w_l3 w_l2; lia|]. split; [clear; lia| exact I].
      - apply (heap_presx_rw_cells _ _ _ _ _ m m1 _ _ w_px1 w_i2).
        + intros a w_a. right. left. cbn in w_a. destruct (w_l4 a ltac:(clear -w_a; lia)) as [_ w_ns].
          split; [clear -w_a w_l1 w_l2 w_l3; lia| exact w_ns].
        + cbn. unfold U_ECP_IDS in *. split; [clear -w_cim w_di1 w_di2 w_l1 w_l3 w_l2; lia|]. split; [clear; lia| exact I]. }
    assert (w_grow13 : forall b, In b LB -> In b LB3) by (intros b w_b; exact (w_grow1 b (w_grow b w_b))).
    assert (w_ctx1 : pctx' h1 LB3 m1 mo1').
    { refine (conj w_heap1 (conj _ (conj (mo_frame_trans mo0 mo mo1' w_mof w_mof1) (conj w_mi1 (conj w_sok1 (conj _ (conj w_grow13 _))))))).
      - rewrite w_top1. exact w_top.
      - split; [exact w_ids1| exists cnt1; exact w_mc1].
      - apply (heap_presx_trans usegs L LB (bv_unsigned sp) FP m0 m m1 w_keep).
        apply (heap_presx_weak'' LB2 (bv_unsigned sp + -112) _ _ m m1 w_px1 w_grow ltac:(lia)).
        intros a w_ca w_out. cbn [outside app] in w_out |- *.
        destruct w_out as (_ & _ & _ & w_omc & _). split; [| split; [exact w_omc| exact I]].
        intros w_in. destruct w_ca as [w_up|[[w_dlo _]|((w_bb & w_bk) & w_bin & w_br2)]].
        + clear -w_up w_in w_cac ACL w_room HLS. lia.
        + clear -w_dlo w_in w_cim w_di1 w_di2. lia.
        + cbn [fst snd] in w_br2. destruct (w_apart w_bb w_bk w_bin) as [w_q|w_q]; clear -w_q w_br2 w_in; lia. }
    (* what the context owns now: the key block, the group limbs and the new point limbs *)
    assert (w_own1 : forall b, In b (newb LB LB3) <-> In b ((C, 256) :: kp_blocks {| kp_grp := g; kp_d := mpd_init (C + 192) pd; kp_Q := Q1 |})).
    { intros b. rewrite newb_in. unfold kp_blocks. cbn [kp_grp kp_d kp_Q mpd_blk mpd_init md_own app]. rewrite w_nb.
      split.
      - intros [w_in3 w_out]. destruct (w_back1 b w_in3) as [w_in2|w_inq].
        + apply w_split in w_in2. destruct w_in2 as [w_n|[w_c|w_l]].
          * right. apply in_or_app. left. exact w_n.
          * left. exact w_c.
          * exfalso. exact (w_out w_l).
        + right. apply in_or_app. right. exact w_inq.
      - intros [w_c|w_r]; [subst b; exact (conj (w_grow1 _ w_cin) w_cnot)|].
        apply in_app_or in w_r. destruct w_r as [w_n|w_q].
        + split; [apply w_grow1; apply w_split; left; exact w_n|].
          intros w_l. apply (w_fresh b w_n). right. exact w_l.
        + split.
          * apply (kp_blocks_in _ _ _ _ _ _ b w_key1). unfold kp_blocks. cbn [kp_grp kp_d kp_Q]. apply in_or_app. right. apply in_or_app. right. exact w_q.
          * intros w_l. exact (w_newq b w_q (w_grow b w_l)). }
    assert (w_blk1 : forall d, In d (kp_mpds {| kp_grp := g; kp_d := mpd_init (C + 192) pd; kp_Q := Q1 |}) -> md_own d = LHeap ->
              (In (md_p d, 4 * md_n d) NB /\ In d (grp_mpds g)) \/ (In (md_p d, 4 * md_n d) (pt_blocks Q1) /\ In d (pt_mpds Q1))).
    { intros d w_d w_o. unfold kp_mpds in w_d. cbn [kp_grp kp_d kp_Q] in w_d.
      apply in_app_or in w_d. destruct w_d as [w_d|[w_d|w_d]].
      - left. split; [rewrite <- w_nb; exact (grp_blk_in g d w_d w_o)| exact w_d].
      - exfalso. subst d. discriminate w_o.
      - right. split; [| exact w_d]. unfold pt_blocks. apply in_flat_map. exists d. split; [exact w_d|].
        rewrite (mpd_blk_heap d w_o). left. reflexivity. }
    assert (w_rep1 : pk_rep_c usegs U_RSA_INFO U_EC_INFOS U_MT m1 LB3 PKA info C (newb LB LB3)).
    { apply (ec_rep_intro U_MT U_RSA_INFO U_EC_INFOS m1 LB3 PKA C _ info (newb LB LB3) w_info w_info0 w_mi1 (HND _ _ _ _ w_heap1) w_key1 (w_grow1 _ w_cin)).
      - intros d1 d2 w_d1 w_d2 w_ne w_o1 w_o2.
        destruct (w_blk1 d1 w_d1 w_o1) as [(w_b1 & w_g1)|(w_b1 & w_q1)];
          destruct (w_blk1 d2 w_d2 w_o2) as [(w_b2 & w_g2)|(w_b2 & w_q2)].
        + intros w_eq. injection w_eq as w_peq _. exact (w_mpds d1 d2 w_g1 w_g2 w_ne w_o1 w_o2 w_peq).
        + intros w_eq. rewrite w_eq in w_b1. apply (w_newq _ w_b2). apply w_split. left. exact w_b1.
        + intros w_eq. rewrite <- w_eq in w_b2. apply (w_newq _ w_b1). apply w_split. left. exact w_b2.
        + destruct w_qdis as (w_xy & w_xz & w_yz). cbn [pt_mpds In] in w_q1, w_q2.
          destruct w_q1 as [<-|[<-|[<-|[]]]]; destruct w_q2 as [<-|[<-|[<-|[]]]];
            first [ exfalso; exact (w_ne eq_refl)
                  | exact (w_xy w_o1 w_o2) | exact (w_xz w_o1 w_o2) | exact (w_yz w_o1 w_o2)
                  | intros w_eq; symmetry in w_eq; revert w_eq; first [exact (w_xy w_o2 w_o1) | exact (w_xz w_o2 w_o1) | exact (w_yz w_o2 w_o1)] ].
      - intros d w_d w_o w_eq. destruct (w_blk1 d w_d w_o) as [(w_b & _)|(w_b & _)]; rewrite w_eq in w_b.
        + apply (w_fresh _ w_b). left. reflexivity.
        + exact (w_newq _ w_b w_cin).
      - exact w_c16.
      - clear -w_cac w_ceil. lia.
      - exact w_own1. }
    clear w_key1 w_ids1 w_own1 w_blk1 w_px1 w_ids w_mc w_heap1.
    zstep. zstep. zstep. zstep.
    if_cases w_t1; zify_cond w_t1.
    { exfalso. rewrite (proj2 (Z.ltb_ge p0 1)) in w_t1 by (clear -w_p0 BUF0; lia).
      rewrite (proj2 (Z.ltb_lt 0 p)) in w_t1 by (clear -w_prange BP BUF0; lia). discriminate w_t1. }
    zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases w_t2; zify_cond w_t2.
    { exfalso. rewrite pk_lxor_sb in w_t2 by (clear -w_prange w_end EB B63 BP BUF0; lia).
      rewrite (proj2 (Z.ltb_ge E2 p)) in w_t2 by (clear -w_prange; lia).
      rewrite (proj2 (Z.ltb_ge (E2 - p + 9223372036854775808) 9223372036854775808)) in w_t2 by (clear -w_prange; lia).
      vm_compute in w_t2. discriminate w_t2. }
    pose proof (munch_refl [(PP, PP + 8)] m1) as w_mu. pose proof (wmono_refl usegs m1) as w_wm.
    zstep. zstep.
    replace (p + (E2 - p)) with E2 in * by (clear; lia).
    assert (w_wpp : Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= bv_unsigned sp \/ iv = (PP, PP + 8) \/ iv = (PKA, PKA + 16)) [(PP, PP + 8)])
      by (apply Forall_cons; [right; left; reflexivity| apply Forall_nil]).
    pose proof (pctx_munch' h1 LB3 m1 m2 mo1' [(PP, PP + 8)] w_ctx1 w_mu w_wm w_mi1 w_wpp) as w_ctx2.
    pose proof w_ctx2 as (w_heap2 & w_topc & w_mofc & w_mic & w_sokc & w_sinvc & _ & w_keepc).
    assert (w_rep2 : pk_rep_c usegs U_RSA_INFO U_EC_INFOS U_MT m2 (newb LB LB3 ++ LB) PKA info C (newb LB LB3)).
    { apply (pk_rep_c_frame _ _ _ _ m1 m2 LB3 _ _ _ _ _ w_rep1 w_mi1).
      - intros b w_b. apply in_or_app. left. exact w_b.
      - intros a ((w_bb & w_bk) & w_bin & w_ba). cbn [fst snd] in w_ba. apply newb_in in w_bin. destruct w_bin as [w_b3 w_bl].
        pose proof (heap_blocks _ _ HI _ _ _ _ w_heap2) as [w_bf _].
        pose proof (proj1 (Forall_forall _ _) w_bf _ w_b3) as (w_bp & _ & _ & w_bac & _). cbn [fst snd] in w_bp, w_bac.
        apply w_mu. rewrite wa_unsigned by (clear -w_ba w_bp w_bac w_ceil; lia).
        cbn [outside]. split; [| exact I].
        destruct (blk_apart_pp' h1 LB3 m2 mo1' w_bb w_bk w_heap2 w_grow13 w_b3 w_bl ltac:(clear -w_ba; lia)) as [w_q|w_q];
          clear -w_q w_ba; lia. }
    clear w_rep1 w_ctx1 w_mu w_wm.
    zstep.
    if_cases w_t3; zify_cond w_t3.
    { (* the key parsed: return 0 *)
      assert (w_r10 : r1 = 0) by (clear -w_rr1 w_t3; lia). subst r1.
      zstep. if_true. zstep. zstep.
      destruct (HPERM h1 LB3 (newb LB LB3 ++ LB) m2 mo1' w_heap2 (newb_perm LB LB3 (HND _ _ _ _ w_heap2) (HND _ _ _ _ HH0) w_grow13))
        as (h2 & w_heap3 & w_top3).
      refine (ret_walk' m2 mo1' h2 (newb LB LB3 ++ LB) 0 E2 info C (newb LB LB3) lj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                w_heap3 _ w_mofc w_mic w_sokc w_sinvc w_keepc _ w_pcell1 _ w_pk1 w_rep2 _ eq_refl w_low1 w_saved1 w_stk1).
      - rewrite w_top3. exact w_topc.
      - clear. lia.
      - clear -w_prange w_end. lia.
      - intros w_n. exfalso. exact (w_n eq_refl). }
    (* the public key was refused: free the context and return the code *)
    eapply fail_free_walk' with (LBc := LB3) (owned := newb LB LB3) (info := info) (ctx := C) (p' := E2);
      [ exact w_ctx2 | exact (newb_perm LB LB3 (HND _ _ _ _ w_heap2) (HND _ _ _ _ HH0) w_grow13) | clear -w_rr1 w_t3; lia | exact w_pcell1
      | clear -w_prange w_end; lia | exact w_pk1 | exact w_rep2 | exact w_low1 | exact w_saved1 | exact w_stk1 ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L13345447015.109L24906321761.111L28232829219.4  L47071308384.112L55445551334.110L66152802788.11300000M00j01701T02102NS2ra2sp2PP3PKA2bs2j02oj2W02W5S2ra2sp2PP3PKA2bs2j02oj2W02W5S2j02oj2W02W5S2ra2sp2PP3PKA2bs2j02oj2W02W5S2ra2sp2PP3PKA2bs2j02oj2W02W5S2ra2sp2PP3PKA2bs2j02oj2W02W5". (* [comment removed for export] *)
  #[using="ra PP PKA bs"] Lemma low_frame_merge : forall (mm : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (j0 : @Corelib.Init.Datatypes.list
    (@stdpp.bitvector.definitions.bv 8%N)), forall (idw : @stdpp.bitvector.definitions.bv 64%N), forall (agw : @stdpp.bitvector.definitions.bv 64%N), forall (ptag :
    @stdpp.bitvector.definitions.bv 64%N), forall (ppad : @stdpp.bitvector.definitions.bv 64%N), forall (plen : @stdpp.bitvector.definitions.bv 64%N), forall (ppw :
    @stdpp.bitvector.definitions.bv 64%N), forall (lnw : @stdpp.bitvector.definitions.bv 64%N), forall (alen : @stdpp.bitvector.definitions.bv 64%N), forall (oj :
    @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat j0] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-104)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 idw] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-100)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 agw] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-96)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ptag; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ppad; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 plen;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ppw] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-72)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 lnw] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-64)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat oj; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 alen] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-112)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) j0 (@Corelib.Init.Datatypes.app
    (@stdpp.bitvector.definitions.bv 8%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le4 idw) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le4 agw) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le4 ptag)
    (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le4 ppad) (@Corelib.Init.Datatypes.app
    (@stdpp.bitvector.definitions.bv 8%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le8 plen) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le8 ppw) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le8 lnw)
    (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) oj (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le8 alen))))))))))]
(* [comment removed for export] *).
  Proof.
    intros until oj. intros F0 F1 F2 F3 F4 F5.
    dpose F0 as [[[W0 _] _] _]. dpose F5 as [[[W5 _] _] _]. cbn in W0, W5.
    chunk_join F0 F1 J1. chunk_join J1 F2 J2. chunk_join J2 F3 J3. chunk_join J3 F4 J4. chunk_join J4 F5 J5.
    eapply rw_cells_reshape; [exact J5| | cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity].
    cbn. rewrite ?app_length, ?length_le8, ?length_le4. cbn. rewrite ?app_length, ?length_le8, ?length_le4. cbn. split; [clear -W0 W5; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L36430635735.400000>S1L1C3CAC4ACLT". (* [comment removed for export] *)
  #[using="HFREE HLS SW DIMG HND HPERM CA_MSF CA_RSA80 CA_EC80 BUF bs HH0 INB BP PE EB BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP SPR"] Lemma init_fail_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (C : @Corelib.Numbers.BinNums.Z), forall (p : @Corelib.Numbers.BinNums.Z), forall (info : @Corelib.Numbers.BinNums.Z), forall (r : @Corelib.Numbers.BinNums.Z), forall (idpad
    : @stdpp.bitvector.definitions.bv 64%N), forall (pP : @stdpp.bitvector.definitions.bv 64%N), forall (pA : @stdpp.bitvector.definitions.bv 64%N), forall (pB :
    @stdpp.bitvector.definitions.bv 64%N), forall (pX : @stdpp.bitvector.definitions.bv 64%N), forall (pY : @stdpp.bitvector.definitions.bv 64%N), forall (pZ :
    @stdpp.bitvector.definitions.bv 64%N), forall (pN : @stdpp.bitvector.definitions.bv 64%N), forall (hpad : @stdpp.bitvector.definitions.bv 64%N), forall (pd :
    @stdpp.bitvector.definitions.bv 64%N), forall (qX : @stdpp.bitvector.definitions.bv 64%N), forall (qY : @stdpp.bitvector.definitions.bv 64%N), forall (qZ :
    @stdpp.bitvector.definitions.bv 64%N), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 : @stdpp.bitvector.definitions.bv 64%N), forall
    (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 : @stdpp.bitvector.definitions.bv 64%N), forall (x9 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x11 : @stdpp.bitvector.definitions.bv 64%N), forall (x12 : @stdpp.bitvector.definitions.bv 64%N), forall (x13 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x14 : @stdpp.bitvector.definitions.bv 64%N), forall (x15 : @stdpp.bitvector.definitions.bv 64%N), forall (x16 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x17 : @stdpp.bitvector.definitions.bv 64%N), forall (x18 : @stdpp.bitvector.definitions.bv 64%N), forall (x19 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x20 : @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x30 : @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N),
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0 mo0 h0 LB PP PKA h (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z)
    (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB) m mo ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.ecp_keypair_at (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m
    (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z)
    (@Corelib.Numbers.BinNums.Z) C 256%Z) LB) C (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_keypair_init.kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.block_range L C 256%Z -> (forall (B : @Corelib.Numbers.BinNums.Z), forall (k : @Corelib.Numbers.BinNums.Z), @Stdlib.Lists.List.In
    (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) B
    k) LB -> @Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add C 256%Z) B) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add B k) C)) ->
    @Stdlib.Lists.List.In (@Corelib.Numbers.BinNums.Z) info (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt
    (@Stdlib.ZArith.BinInt.Z.opp (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.lt r 0%Z) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p END) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA
    [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N info); @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N C)] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat lj] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-48)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) x9 (@stdpp.bitvector.definitions.Z_to_bv 64%N r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9
    s10 s11 x28 x29 x30 x31) F (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x2950c%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX KP BRC APC EI RR HPP PB HPKA FRL FR ST.
    dpose CX as (HH & HT & MF & MI & SOK & SIP & SUB & PX). dpose BRC as (C0 & C16 & _ & CAC & CIM). pose proof alloc_ceiling_lt as ACLT.
    pose proof (HND _ _ _ _ HH) as ND1.
    assert (NOH : forall d, In d (kp_mpds (kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ)) -> md_own d = LHeap -> False).
    { intros d Hd O. unfold kp_mpds, kp_init, grp_mpds, grp_init in Hd.
      cbn [kp_grp kp_d kp_Q g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In] in Hd. unfold mpd_init in Hd.
      decompose [or] Hd; try contradiction; subst d; cbn in O; discriminate. }
    eapply fail_free_walk' with (owned := [(C, 256)]) (info := info) (ctx := C);
      [ exact CX | apply Permutation_refl | exact RR | exact HPP | exact PB | exact HPKA | | exact FRL | exact FR | exact ST ].
    eapply ec_rep_intro; [exact EI| intros E0; rewrite E0 in EI; cbn in EI; clear -EI; intuition discriminate| exact MI| exact ND1| exact KP| left; reflexivity
      | intros d1 d2 H1 _ _ O1 _; exfalso; exact (NOH d1 H1 O1) | intros d Hd O; exfalso; exact (NOH d Hd O) | exact C16| clear -CAC ACLT; lia|].
    intros b. unfold kp_blocks, kp_init, grp_blocks, grp_mpds, grp_init, pt_blocks.
    cbn [kp_grp kp_d kp_Q g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z flat_map app mpd_blk md_own mpd_init]. split; intros Hx; exact Hx.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01[0@L1077460508.1   L11881722111.6  L11886305925.6  L11892015684.8  L11892194884.11 L11892194884.9  L1212367933.7   L1223650147.11  L12586315760.6  L12586472432.7  L12596958027.3  L1326225569.0   L14372944785.6  L14954029152.12 L14956411285.4  L14956411285.7  L14960416076.12 L15621588449.3  L15623165340.1  L1725003874.1   L17818708241.8  L18324370038.3  L18961486402.9  L18961722946.7  L1917911384.5   L19484473094.9  L19561826530.1  L20941750301.12 L20941929501.10 L20953764036.8  L21649695260.1  L22987083584.6  L23268210308.0  L23271682978.1  L23445226910.4  L2397676628.0   L24232655618.6  L24232937218.7  L24235034553.4  L2651746289.7   L28142564996.0  L29250350218.7  L29256378022.11 L29256669862.8  L29762660275.171L29956516996.0  L30556717977.4  L30567249333.6  L30567467445.8  L30738725165.5  L33333697059.3  L34741001406.7  L34806988770.1  L3582028444.1   L36879782785.6  L36886498503.10 L36886737095.8  L37263248962.7  L37263618626.7  L37278298873.5  L37317392303.8  L38891255949.5  L40147641242.5  L42810574465.170L42842486707.170L43300649301.0  L44145255421.3  L4728363746.1   L47292300636.8  L48932718241.0  L4966764130.1   L49728944076.8  L50922497238.11 L51158950247.3  L52253708504.172L52991974620.1  L55234206670.0  L57862176958.0  L5958257762.1   L59762707150.11 L59773239266.11 L59773498986.6  L59775870098.3  L60264566684.1  L60988478422.8  L60999331698.4  L61001957135.2  L61900301956.0  L62673510860.8  L64995164688.170L65351099990.3  L65361585901.9  L65361877741.6  L66291751964.1  L66558683739.2  L66568952032.6  L66569118944.8  L66569699239.4  L68335942726.9  L68342123114.2  L68342123114.4  L68346317162.8  L68447938666.8  L7036479304.1   L8530602861.6   L8532465622.3   L9683945296.6   00000400500600700800900:00;00<00V00W00X00k00l00m00n00o01301701;01X01`01n01o02002P02T02U02V02W02[02n02o03303403503603703803903:03;03<03=03P03Q03R03S03T03U03a04904=04A04B04C04D04E04S04T05205D05R05e06806906A06E06`06a06e07607W07c08608:08;08<08@08A08B08C08D08H08b08c08d08e09@09S09[0:90::0:>0:H0:I0:J0:K0:L0:M0:N0:j0;F0;J0;K0;S0;fS2spFFFFFFFFS1L3HLS2sp2lo3ACL3ACP4SLO'FSS1P3END1p2E22PB3E2BFFFFS2spS2spS2spS1L3HLS2sp2lo3ACL3DHI4SLO'2I3S2PP1C1QS1L2sp2lo4SLO'FFS1L3HLS2sp2lo3ACL3DHI4SLO'2I32I2S2spFFFS2spS1L2PP3PPD2I12I22I3SS2spFSFFFFSFFFS2ra2sp2PP3PKA2bs1CSFFFFS3idw1u4U913S1L1C3CIM2M12M23E1'4E2''S2spS2spFFFFS1L2sp2lo4SLO'FS1L3HLS2sp2lo3ACL3SPR3ACP4SLO'S1L1C3CIM3E1'4E2''S1L2M12M21a2HaS2ra2sp2PP3PKA2bs1CS2ra2sp2PP3PKA2bs1CSS1C1a2HaS2spS1L1C3CIM2I12I22I33E1'4E2''SS2spS1L2HI2sp2h04HTOPS3END3BUF2bs2EB2E24plen2pp2Q23E2BS2sp3PKA3SPKS2ra2sp2PP3PKA2bs1CS2spSSS2spFFFFS2spS1L3HLS2sp2lo3ACL3DHI4SLO'FFSS1L1C3CIM2I12I22I33E1'4E2''S2ra2sp2PP3PKA2bs1CS2sp3SPAS1L3HLS2sp2lo3ACL3SPA3ACP4SLO'FS2spS4plen3PLRFFFFFFS1L3HLS2sp2lo3ACL1C4SLO'3CACS1L3HLS2sp2lo3ACL1C4SLO'3CACS2spFS2sp3SPAS1L2PP3PPD2I12I22I3". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND HPERM CA_MSF CA_RSA0 CA_RSA80 CA_EC0 CA_EC80 CAT_ECGRP CA_BP HPRB HCPK bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR"] Lemma ec_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (C : @Corelib.Numbers.BinNums.Z), forall (p : @Corelib.Numbers.BinNums.Z), forall (E2 : @Corelib.Numbers.BinNums.Z), forall (info : @Corelib.Numbers.BinNums.Z), forall (ta :
    @stdpp.bitvector.definitions.bv 64%N), forall (x11 : @stdpp.bitvector.definitions.bv 64%N), forall (idpad : @stdpp.bitvector.definitions.bv 64%N), forall (pP :
    @stdpp.bitvector.definitions.bv 64%N), forall (pA : @stdpp.bitvector.definitions.bv 64%N), forall (pB : @stdpp.bitvector.definitions.bv 64%N), forall (pX :
    @stdpp.bitvector.definitions.bv 64%N), forall (pY : @stdpp.bitvector.definitions.bv 64%N), forall (pZ : @stdpp.bitvector.definitions.bv 64%N), forall (pN :
    @stdpp.bitvector.definitions.bv 64%N), forall (hpad : @stdpp.bitvector.definitions.bv 64%N), forall (pd : @stdpp.bitvector.definitions.bv 64%N), forall (qX :
    @stdpp.bitvector.definitions.bv 64%N), forall (qY : @stdpp.bitvector.definitions.bv 64%N), forall (qZ : @stdpp.bitvector.definitions.bv 64%N), forall (j0 :
    @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (oj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (idw :
    @stdpp.bitvector.definitions.bv 64%N), forall (agw : @stdpp.bitvector.definitions.bv 64%N), forall (ptag : @stdpp.bitvector.definitions.bv 64%N), forall (ppad :
    @stdpp.bitvector.definitions.bv 64%N), forall (plen : @stdpp.bitvector.definitions.bv 64%N), forall (alen : @stdpp.bitvector.definitions.bv 64%N), forall (lnw :
    @stdpp.bitvector.definitions.bv 64%N), forall (pp : @Corelib.Numbers.BinNums.Z), forall (x1 : @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv
    64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 : @stdpp.bitvector.definitions.bv 64%N), forall (x12 : @stdpp.bitvector.definitions.bv 64%N), forall (x13 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x14 : @stdpp.bitvector.definitions.bv 64%N), forall (x15 : @stdpp.bitvector.definitions.bv 64%N), forall (x16 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x17 : @stdpp.bitvector.definitions.bv 64%N), forall (p0 : @Corelib.Numbers.BinNums.Z), forall (x20 : @stdpp.bitvector.definitions.bv
    64%N), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 : @stdpp.bitvector.definitions.bv 64%N), forall (x31 :
    @stdpp.bitvector.definitions.bv 64%N), @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0 mo0 h0 LB PP PKA h (@Corelib.Init.Datatypes.cons
    (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C
    256%Z) LB) m mo -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.ecp_keypair_at (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB) C (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_keypair_init.kp_init C idpad pP
    pA pB pX pY pZ pN hpad pd qX qY qZ) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.block_range L C 256%Z -> (forall (B : @Corelib.Numbers.BinNums.Z), forall (k :
    @Corelib.Numbers.BinNums.Z), @Stdlib.Lists.List.In (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair
    (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) B k) LB -> @Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add C 256%Z) B)
    (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add B k) C)) -> @Stdlib.Lists.List.In (@Corelib.Numbers.BinNums.Z) info
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) -> @Corelib.Init.Logic.or (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) pp 0%Z)
    (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned 64%N plen) 0%Z) (@Corelib.Init.Logic.eq
    (@stdpp.bitvector.definitions.bv 64%N) ptag (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z)))) (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le BUF pp)
    (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add pp (@stdpp.bitvector.definitions.bv_unsigned 64%N plen)) E2)) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p E2) -> @Stdlib.ZArith.BinInt.Z.le E2 END -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N info);
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N C)] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z)
    [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat j0] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-104)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 idw] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-100)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 agw] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-96)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ptag;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ppad; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 plen; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N pp)] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-72)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 lnw] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-64)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat oj; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 alen] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-48)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le BUF p0) (@Stdlib.ZArith.BinInt.Z.le p0 END) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT))
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add
    (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) (@stdpp.bitvector.definitions.Z_to_bv 64%N PP) ta x11
    x12 x13 x14 x15 x16 x17 (@stdpp.bitvector.definitions.Z_to_bv 64%N E2) (@stdpp.bitvector.definitions.Z_to_bv 64%N p0) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x29440%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros m mo h C p E2 info ta x11 idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ j0 oj idw agw ptag ppad plen alen lnw pp
      x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 p0 x20 x28 x29 x30 x31
      v_ctx v_key v_brange v_apart v_info v_par v_pcell v_prange v_end v_pk v_j0 v_idw v_agw v_parc v_lnw v_oj v_saved v_stk v_p0.
    clear CA_RSA72 CA_EC72 CAT_PKALG CAT_ECALGID CA_PKTBL HPP0 ALPP HPKA0 PPT ST0 MI0 SOK0 SIP0 RA.
    pose proof v_ctx as (v_heap & v_top & v_mof & v_mi & v_sok & v_sinv & v_grow & v_keep).
    pose proof (heap_mok _ _ HI _ _ _ _ v_heap) as v_mok.
    pose proof (pctx_bytes' h ((C, 256) :: LB) m mo v_ctx) as v_bytes.
    pose proof pa_basics' as (v_ac4096 & v_bufac & v_bufimg & v_ppdat & v_pkdat & v_room).
    pose proof DI1 as v_di1. pose proof DI2 as v_di2. pose proof ML1 as v_ml1. pose proof ML2 as v_ml2.
    pose proof IL1 as v_il1. pose proof IL2 as v_il2. pose proof IL3 as v_il3.
    pose proof v_brange as (v_c0 & v_c16 & _ & v_cac & v_cim).
    pose proof (fresh_apart_pka' C 256 v_brange v_apart ltac:(lia)) as v_pkfar.
    pose proof (fresh_apart_pp' C 256 v_brange v_apart ltac:(lia)) as v_ppfar.
    assert (v_spu : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112).
    { apply unsigned_lit. clear -v_room ACL v_ac4096 HLS SPR. lia. }
    assert (v_lb1 : forall b, In b LB -> In b ((C, 256) :: LB)) by (intros b v_b; right; exact v_b).
    assert (v_cwp : client_wrange L ((C, 256) :: LB) lo (heap_top usegs L HI h) PKA 16).
    { rewrite v_top. exact (client_wrange_mono L LB _ lo (heap_top usegs L HI h0) PKA 16 CWP v_lb1). }
    (* the stack slots below the saved registers, viewed as one 64-byte local area *)
    pose proof (low_frame_merge m j0 idw agw ptag ppad plen (Z_to_bv 64 pp) lnw alen oj v_j0 v_idw v_agw v_parc v_lnw v_oj) as v_low.
    set (lj := j0 ++ le4 idw ++ le4 agw ++ le4 ptag ++ le4 ppad ++ le8 plen ++ le8 (Z_to_bv 64 pp) ++ le8 lnw ++ oj ++ le8 alen) in v_low.
    clearbody lj.
    zstep. zstep. zstep.
    if_cases v_t0; zify_cond v_t0.
    { (* neither EC key kind: unknown algorithm, free the fresh context *)
      zstep. zstep. zstep.
      eapply init_fail_walk with (r := -15488) (lj := lj);
        [ exact v_ctx | exact v_key | exact v_brange | exact v_apart | exact v_info | clear; lia | exact v_pcell
        | clear -v_prange v_end; lia | exact v_pk | exact v_low | exact v_saved | exact v_stk ]. }
    zstep. zstep. zstep. zstep.
    if_cases v_t1; zify_cond v_t1.
    { (* the curve comes from the algorithm parameters *)
      zstep. zstep. zstep.
      pose proof (U_pk_use_ecparams_spec L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 HL) as v_uep.
      unfold pk_use_ecparams_stmt, U_PK_USE_ECPARAMS in v_uep. lazy zeta in v_uep.
      pose proof v_sinv as (v_ids & cnt & v_mc).
      eapply aevtM_cut.
      { eapply v_uep with (h := h) (LB := (C, 256) :: LB) (PKA := PKA) (info := info) (C := C) (lo := lo)
          (PAR := bv_unsigned sp + -96) (LEN := bv_unsigned plen) (P := pp) (BUF := BUF) (tg := ptag) (pd := ppad) (bs := bs)
          (idpad := idpad) (pP := pP) (pA := pA) (pB := pB) (pX := pX) (pY := pY) (pZ := pZ) (pN := pN) (hpad := hpad)
          (qd := pd) (qX := qX) (qY := qY) (qZ := qZ);
          rewrite ?v_spu;
          [ exact v_heap | exact v_pk | exact ALP | exact NZP | exact v_info
          | clear -DSP; lia
          | exact v_cwp
          | unfold ECP_KEYPAIR_SIZE; exact v_pkfar
          | exact v_pkdat
          | exact v_key
          | left; reflexivity
          | unfold ECP_KEYPAIR_SIZE; clear -v_cim v_di1 v_di2; lia
          | unfold buf_cells; rewrite Z_to_bv_bv_unsigned; exact v_parc
          | clear -SPA; lia
          | clear -v_room HLS ACL v_ac4096; lia
          | right; clear; lia
          | right; clear -v_room HLS ACL DHI; lia
          | right; unfold ECP_KEYPAIR_SIZE; clear -v_room HLS ACL v_cac; lia
          | exact v_bytes
          | right; exact INB
          | destruct v_par as [v_q|v_q]; [left; exact v_q| right; clear -v_q v_end EB; lia]
          | apply bv_unsigned_in_range
          | exact B63
          | exact BUF0
          | exact v_ids
          | exact v_sok
          | exact CA_MSF
          | exact CAT_ECGRP
          | exact CA_EC0
          | exact v_stk
          | clear -SLO HLS; unfold PK_PARSE_STACK in SLO; lia
          | exact ACL
          | rewrite v_top; clear -HTOP; lia
          | clear -SPA; lia
          | exact DHI
          | exact TP
          | exact v_mi
          | vm_compute; reflexivity
          | reflexivity
          | reflexivity ]. }
      intros ms1 mo1 v_post. unfold pk_use_ecparams_post in v_post.
      destruct v_post as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & mo1' & h1 & r1 & g1 & NB1 & LB1 &
        v_cfg & v_mi1 & v_stk1 & v_mof1 & v_top1 & v_heap1 & v_split1 & v_fresh1 & v_key1 & v_mpds1 & v_nb1 & v_res1 & v_rr1 & v_pk1 & v_px1 & v_sok1 & v_ids1).
      injection v_cfg as -> ->.
      rewrite v_spu in v_stk1, v_px1.
      rewrite (ret_pc_even 169156) by (first [lia | reflexivity]).
      unfold ECP_GROUP_SIZE in v_px1.
      assert (v_xfar : Forall (fun iv : Z * Z => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv)
                         [(C, C + 192); (U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)]).
      { apply Forall_cons; [cbn [fst snd]; left; clear -v_cac ACL v_room HLS; lia|].
        apply Forall_cons; [cbn [fst snd]; left; clear -ACL v_room HLS v_il2 v_il3 DHI; lia|].
        apply Forall_cons; [cbn [fst snd]; left; clear -ACL v_room HLS v_il3 DHI; lia|]. apply Forall_nil. }
      assert (v_lb2 : forall b, In b LB -> In b LB1) by (intros b v_b; apply v_split1; right; right; exact v_b).
      assert (v_mc1 : rw_cells usegs m1 380840 [C8 cnt]).
      { apply (heap_presx_rw_cells _ _ _ _ _ m m1 _ _ v_px1 v_mc).
        - intros a v_a. right. left. cbn in v_a. destruct (proj2 (proj2 HMC) a ltac:(clear -v_a; lia)) as [_ v_ns].
          split; [clear -v_a v_ml1 v_ml2; lia| exact v_ns].
        - cbn. unfold U_ECP_IDS_DONE, U_ECP_IDS. split; [clear -v_cim v_di1 v_di2 v_ml1 v_ml2; lia|].
          split; [clear; lia|]. split; [clear; lia| exact I]. }
      assert (v_ctx1 : pctx' h1 LB1 m1 mo1').
      { refine (conj v_heap1 (conj _ (conj (mo_frame_trans mo0 mo mo1' v_mof v_mof1) (conj v_mi1 (conj v_sok1 (conj _ (conj v_lb2 _))))))).
        - rewrite v_top1. exact v_top.
        - split; [exact v_ids1| exists cnt; exact v_mc1].
        - apply (heap_presx_trans usegs L LB (bv_unsigned sp) FP m0 m m1 v_keep).
          apply (heap_presx_weak'' ((C, 256) :: LB) (bv_unsigned sp + -112) _ _ m m1 v_px1 v_lb1 ltac:(lia)).
          intros a v_ca v_out. cbn [outside app] in v_out |- *.
          destruct v_out as (_ & _ & v_odone & _ & v_oids & _). split; [| split; [exact v_odone| split; [exact v_oids| exact I]]].
          intros v_in. destruct v_ca as [v_up|[[v_dlo _]|((v_bb & v_bk) & v_bin & v_br)]].
          + clear -v_up v_in v_cac ACL v_room HLS. lia.
          + clear -v_dlo v_in v_cim v_di1 v_di2. lia.
          + cbn [fst snd] in v_br. destruct (v_apart v_bb v_bk v_bin) as [v_q|v_q]; clear -v_q v_br v_in; lia. }
      eapply ec_fin_walk with (h := h1) (LB2 := LB1) (C := C) (p := p) (info := info) (g := g1) (NB := NB1)
        (pd := pd) (qX := qX) (qY := qY) (qZ := qZ) (lj := lj);
        [ exact v_ctx1 | exact v_key1 | apply v_split1; right; left; reflexivity | exact v_brange | exact v_apart | exact v_info
        | exact v_mpds1 | exact v_nb1 | exact v_split1 | exact v_fresh1
        | intros v_r0; subst r1; destruct v_res1 as [(v_id & v_idr & v_gl)|(v_ne & _)];
            [exists v_id; exact (conj v_idr v_gl)| exfalso; exact (v_ne eq_refl)]
        | exact v_rr1
        | | clear -v_prange; lia | exact v_end | exact v_pk1 | | | exact v_stk1 | exact v_p0 ].
      + assert (v_sple : bv_unsigned sp + -112 <= bv_unsigned sp) by (clear; lia).
        apply (keep_pp' ((C, 256) :: LB) (bv_unsigned sp + -112) _ m m1 _ v_px1 v_lb1 v_sple v_pcell eq_refl).
        cbn [disjoint_from]. unfold U_ECP_IDS_DONE, U_ECP_IDS in *.
        split; [clear -v_ppfar; lia|]. split; [clear -v_ppdat v_il1 v_il2 v_il3; lia|]. split; [clear -v_ppdat v_il1 v_il2 v_il3; lia| exact I].
      + apply (keep_frame' ((C, 256) :: LB) (bv_unsigned sp + -112) _ m m1 _ _ v_px1 ltac:(lia) v_low ltac:(lia)); [cbn; lia| exact v_xfar].
      + apply (keep_frame' ((C, 256) :: LB) (bv_unsigned sp + -112) _ m m1 _ _ v_px1 ltac:(lia) v_saved ltac:(lia)); [cbn; lia| exact v_xfar]. }
    (* RFC 8410 curve: the parameters must be absent *)
    assert (v_ginit_apart : mpds_apart (grp_mpds (grp_init C idpad pP pA pB pX pY pZ pN hpad))).
    { intros d1 d2 v_d1 _ _ v_o1 _. exfalso. unfold grp_mpds in v_d1.
      cbn [grp_init g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app] in v_d1.
      repeat (destruct v_d1 as [v_e|v_d1]; [rewrite <- v_e in v_o1; cbn in v_o1; discriminate v_o1|]).
      destruct v_d1. }
    assert (v_ginit_blocks : grp_blocks (grp_init C idpad pP pA pB pX pY pZ pN hpad) = []) by (unfold grp_blocks, grp_mpds; cbn; reflexivity).
    assert (v_ginit_split : forall b, In b ((C, 256) :: LB) <-> In b [] \/ In b ((C, 256) :: LB)).
    { intros b. split; [intros v_b; right; exact v_b| intros [[]|v_b]; exact v_b]. }
    zstep. zstep. zstep. zstep. zstep.
    if_cases v_al; zify_cond v_al.
    { exfalso. apply v_al. replace 7 with (Z.ones 3) by reflexivity. rewrite Z.land_ones by (clear; lia).
      change (2 ^ 3) with 8. clear -SPA. lia. }
    zstep. zstep.
    if_cases v_tg; zify_cond v_tg.
    2: (zstep; zstep; if_cases v_ln; zify_cond v_ln).
    2: { (* tag and length both zero: load the named group into the fresh key *)
      zstep. zstep.
      lazymatch goal with v_c : Z.land (bv_unsigned ?w) 18446744073709551611 = 9 |- _ => set (wv := w) in * end.
      pose proof (bv_unsigned_in_range 64 wv) as v_wrng. change (bv_modulus 64) with (2 ^ 64) in v_wrng.
      pose proof (land_m5_9 (bv_unsigned wv) v_wrng v_t1) as v_w913.
      assert (v_wid : 0 <= bv_unsigned wv < 2 ^ 31) by (clear -v_w913; lia).
      pose proof (U_pk_ecc_set_group_spec L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0) as v_sgs.
      unfold pk_ecc_set_group_stmt, U_PK_ECC_SET_GROUP in v_sgs. lazy zeta in v_sgs.
      eapply aevtM_cut.
      { eapply v_sgs with (h := h) (LB := (C, 256) :: LB) (PKA := PKA) (info := info) (C := C) (id := bv_unsigned wv) (lo := lo)
          (idpad := idpad) (pP := pP) (pA := pA) (pB := pB) (pX := pX) (pY := pY) (pZ := pZ) (pN := pN) (hpad := hpad)
          (pd := pd) (qX := qX) (qY := qY) (qZ := qZ);
          rewrite ?v_spu;
          [ exact v_heap | exact v_pk | exact ALP | exact NZP | exact v_info
          | clear -DSP; lia
          | exact v_cwp
          | unfold ECP_KEYPAIR_SIZE; exact v_pkfar
          | exact v_key
          | left; reflexivity
          | unfold ECP_KEYPAIR_SIZE; clear -v_cim v_di1 v_di2; lia
          | exact v_wid
          | exact v_stk
          | clear -SLO HLS; unfold PK_PARSE_STACK in SLO; lia
          | exact ACL
          | rewrite v_top; clear -HTOP; lia
          | clear -SPA; lia
          | exact DHI
          | exact TP
          | exact v_mi
          | exact v_sok
          | exact CA_MSF
          | exact CA_EC0
          | vm_compute; reflexivity
          | reflexivity
          | symmetry; apply Z_to_bv_bv_unsigned ]. }
      intros ms1 mo1 v_post. unfold pk_ecc_set_group_post in v_post.
      destruct v_post as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & mo1' & h1 & r1 & g1 & NB1 & LB1 &
        v_cfg & v_mi1 & v_stk1 & v_mof1 & v_top1 & v_heap1 & v_split1 & v_fresh1 & v_key1 & v_mpds1 & v_nb1 & v_gl1 & v_pk1 & v_px1 & v_sok1).
      injection v_cfg as -> ->.
      rewrite v_spu in v_stk1, v_px1.
      rewrite (ret_pc_even 169064) by (first [lia | reflexivity]).
      unfold ECP_GROUP_SIZE in v_px1.
      pose proof (heap_mok _ _ HI _ _ _ _ v_heap1) as v_mok1.
      zstep.
      assert (v_xfar : Forall (fun iv : Z * Z => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C, C + 192)]).
      { apply Forall_cons; [cbn [fst snd]; left; clear -v_cac ACL v_room HLS; lia| apply Forall_nil]. }
      assert (v_lb2 : forall b, In b LB -> In b LB1) by (intros b v_b; apply v_split1; right; right; exact v_b).
      pose proof v_sinv as (v_ids & cnt & v_mc).
      assert (v_cl : forall a, hl_data_lo L <= a < hl_data_hi L -> ~ hl_static L a -> client_addr L ((C, 256) :: LB) (bv_unsigned sp + -112) a)
        by (intros a v_a v_ns; right; left; exact (conj v_a v_ns)).
      assert (v_cfar : forall a n, hl_data_lo L <= a -> a + n <= hl_data_hi L -> disjoint_from [(C, C + 192)] a n).
      { intros a n v_a v_n. cbn. split; [clear -v_a v_n v_cim v_di1 v_di2; lia| exact I]. }
      assert (v_sinv1 : pk_sinv_P m1).
      { pose proof HL as (v_l1 & v_l2 & v_l3 & v_l4).
        destruct v_ids as (v_b & v_bsl & v_i1 & v_i2 & v_iv). split.
        - exists v_b, v_bsl. split; [| split; [| exact v_iv]].
          + apply (heap_presx_rw_cells _ _ _ _ _ m m1 _ _ v_px1 v_i1); [| cbn; apply v_cfar; clear -v_l1 v_l2 v_l3; lia].
            intros a v_a. cbn in v_a. destruct (v_l4 a ltac:(clear -v_a; lia)) as [_ v_ns]. apply v_cl; [clear -v_a v_l1 v_l2 v_l3; lia| exact v_ns].
          + apply (heap_presx_rw_cells _ _ _ _ _ m m1 _ _ v_px1 v_i2); [| cbn; apply v_cfar; clear -v_l1 v_l2 v_l3; lia].
            intros a v_a. cbn in v_a. destruct (v_l4 a ltac:(clear -v_a; lia)) as [_ v_ns]. apply v_cl; [clear -v_a v_l1 v_l2 v_l3; lia| exact v_ns].
        - exists cnt. apply (heap_presx_rw_cells _ _ _ _ _ m m1 _ _ v_px1 v_mc); [| cbn; apply v_cfar; clear -v_ml1 v_ml2; lia].
          intros a v_a. cbn in v_a. destruct (proj2 (proj2 HMC) a ltac:(clear -v_a; lia)) as [_ v_ns].
          apply v_cl; [clear -v_a v_ml1 v_ml2; lia| exact v_ns]. }
      assert (v_ctx1 : pctx' h1 LB1 m1 mo1').
      { refine (conj v_heap1 (conj _ (conj (mo_frame_trans mo0 mo mo1' v_mof v_mof1) (conj v_mi1 (conj v_sok1 (conj v_sinv1 (conj v_lb2 _))))))).
        - rewrite v_top1. exact v_top.
        - apply (heap_presx_trans usegs L LB (bv_unsigned sp) FP m0 m m1 v_keep).
          apply (heap_presx_weak'' ((C, 256) :: LB) (bv_unsigned sp + -112) _ _ m m1 v_px1 v_lb1 ltac:(lia)).
          intros a v_ca _. cbn [outside]. split; [| exact I].
          intros v_in. destruct v_ca as [v_up|[[v_dlo _]|((v_bb & v_bk) & v_bin & v_br)]].
          + clear -v_up v_in v_cac ACL v_room HLS. lia.
          + clear -v_dlo v_in v_cim v_di1 v_di2. lia.
          + cbn [fst snd] in v_br. destruct (v_apart v_bb v_bk v_bin) as [v_q|v_q]; clear -v_q v_br v_in; lia. }
      assert (v_sple : bv_unsigned sp + -112 <= bv_unsigned sp) by (clear; lia).
      eapply ec_fin_walk with (h := h1) (LB2 := LB1) (C := C) (p := p) (info := info) (g := g1) (NB := NB1)
        (pd := pd) (qX := qX) (qY := qY) (qZ := qZ) (lj := lj);
        [ exact v_ctx1 | exact v_key1 | apply v_split1; right; left; reflexivity | exact v_brange | exact v_apart | exact v_info
        | exact v_mpds1 | exact v_nb1 | exact v_split1 | exact v_fresh1
        | intros v_r0; subst r1; exists (bv_unsigned wv); exact (conj v_wid v_gl1)
        | destruct v_gl1 as [(-> & _)|[(-> & _)|[(-> & _)|(-> & _)]]];
            unfold MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE, MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia
        | | clear -v_prange; lia | exact v_end | exact v_pk1 | | | exact v_stk1 | exact v_p0 ].
      + apply (keep_pp' ((C, 256) :: LB) (bv_unsigned sp + -112) _ m m1 _ v_px1 v_lb1 v_sple v_pcell eq_refl).
        cbn [disjoint_from]. split; [clear -v_ppfar; lia| exact I].
      + apply (keep_frame' ((C, 256) :: LB) (bv_unsigned sp + -112) _ m m1 _ _ v_px1 (Z.le_refl _) v_low ltac:(lia)); [cbn; lia| exact v_xfar].
      + apply (keep_frame' ((C, 256) :: LB) (bv_unsigned sp + -112) _ m m1 _ _ v_px1 (Z.le_refl _) v_saved ltac:(lia)); [cbn; lia| exact v_xfar]. }
    (* a tag or a length is present: the parameters are refused before any allocation *)
    all: zstep; zstep; zstep; zstep;
      eapply ec_fin_walk with (h := h) (LB2 := (C, 256) :: LB) (C := C) (p := p) (info := info)
        (g := grp_init C idpad pP pA pB pX pY pZ pN hpad) (NB := []) (pd := pd) (qX := qX) (qY := qY) (qZ := qZ) (lj := lj);
      [ exact v_ctx | exact v_key | left; reflexivity | exact v_brange | exact v_apart | exact v_info
      | exact v_ginit_apart | exact v_ginit_blocks | exact v_ginit_split | intros b [] | intros v_r0; discriminate v_r0 | clear; lia
      | exact v_pcell | clear -v_prange; lia | exact v_end | exact v_pk | exact v_low | exact v_saved | exact v_stk | exact v_p0 ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.
