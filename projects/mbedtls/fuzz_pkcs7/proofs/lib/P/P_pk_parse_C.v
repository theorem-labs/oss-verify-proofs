(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Bytes MpiCoreAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepPk RepCrt CrtStmts CrtParseStmts SInv PkTmp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_platform_zeroize P_mpi_free P_mpi_addsub P_asn1_sequence_free P_asn1_get_sequence_of_A P_ecp_defs P_ecp_group_load P_ecp_grp_id_list P_ecp_sinv P_pk_sinv P_ecp_keypair_init
     P_pk_wrap_rsa P_pk_wrap_eckey P_pk_free P_pk_type P_pk_setup P_pk_ecc_set_group P_pk_ecc_set_pubkey P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_D P_rsa_parse_pubkey
     P_oid P_oid_pk_alg P_oid_ec_grp P_oid_ec_grp_algid P_pk_info P_ecp_point_read_binary P_ecp_check_pubkey P_ecp_bad_points P_asn1_get_mpi P_asn1_get_alg_A P_pk_ecparams P_ecp_statics P_ecp_check_pubkey P_ecp_point_read_binary P_pk_ecc_set_pubkey_proof P_pk_parse_A.
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
Ltac2 gd_tbl_P_pk_parse_C () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Stdlib.Lists.List.In"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "newb"; "OSSVerify.KrLib.Spec.RepEcp.modp_ent"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.RepEcp.ecp_kp"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Spec.RepEcp.ecp_keypair_at"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.RepEcp.kp_mpds"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Spec.RepEcp.kp_blocks"; "OSSVerify.KrLib.Spec.RepPk.pk_rep_c"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.ecp_point_read_binary_stmt"; "OSSVerify.KrLib.P.P_ecp_defs.P_MT"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.P_ECP_POINT_READ_BINARY"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.ECP_POINT_READ_STACK"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.ecp_check_pubkey_stmt"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.P_ECP_CHECK_PUBKEY"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.P_BAD_POINTS"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "OSSVerify.KrLib.Spec.RepEcp.ecp_grp"; "OSSVerify.KrLib.Spec.RepEcp.mkKP"; "OSSVerify.KrLib.Spec.RepEcp.mpd_init"; "OSSVerify.KrLib.Spec.RepEcp.pt_init"; "OSSVerify.KrLib.Spec.RepEcp.grp_mpds"; "OSSVerify.KrLib.Spec.RepEcp.grp_blocks"; "OSSVerify.KrLib.P.P_pk_parse_A.pctx"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.P.P_pk_free.P_EC_INFOS"; "OSSVerify.KrLib.Spec.EcpFacts.mpds_apart"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.P.P_ecp_group_load.gl_result"; "OSSVerify.KrLib.P.P_ecp_defs.P_CA"; "OSSVerify.KrLib.P.P_ecp_defs.P_ONE"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "OSSVerify.KrLib.Spec.RepPk.PKC_inst"; "OSSVerify.KrLib.P.P_pk_free.P_RSA_INFO"; "OSSVerify.KrLib.P.P_pk_sinv.P_pk_sinv"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Mem.le4"; "OSSVerify.KrLib.Lib.Mem.le8"; "OSSVerify.KrLib.P.P_ecp_keypair_init.kp_init"].


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
  { intros d Hd O. dpose (kp_mpds_mpdr psegs MT m LBx C k d KP Hd) as (_ & _ & _ & _ & _ & HO). rewrite O in HO. exact (proj1 (proj2 HO)). }
  right; right. split; [exact EI|]. split; [exact NI|]. split; [exact MI|]. exists k.
  split; [exact KP|]. split; [exact CIN|]. split.
  { intros d1 d2 H1 H2 NE O1 O2 E. apply (DIS d1 d2 H1 H2 NE O1 O2). rewrite E. f_equal.
    exact (nodup_fst_same LBx (md_p d2) (4 * md_n d1) (4 * md_n d2) ND ltac:(rewrite <- E; exact (BLK d1 H1 O1)) (BLK d2 H2 O2)). }
  split. { intros d Hd O E. apply (NC d Hd O). rewrite E. f_equal. exact (nodup_fst_same LBx C (4 * md_n d) 256 ND ltac:(rewrite <- E; exact (BLK d Hd O)) CIN). }
  split; [exact AL|]. split; [exact C64| exact OWN].
Qed.

Notation MT := P_MT (only parsing).

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
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis HL : ecp_ids_lok L P_ECP_IDS_DONE P_ECP_IDS.
  Hypothesis HMC : mc_lok L P_MUL_COUNT.
  (* [comment removed for export] *)
  Hypothesis HPERM : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "Ph,(26.$12.VL,VHI,)PLB,(0.$9.)PLB',(0.$9.)Pm,P,(<.&40.)(=.(<.&8.))Pmo,$27.P,(28.$12.VL,VHI,R5.R4.R2.R1.)P,(7.$9.R5.R4.)(29.(26.$12.VL,VHI,)Lh',(26.$12.VL,VHI,)(2:.(28.$12.VL,VHI,R1.R6.R5.R4.)(10.$2.(2;.$12.VL,VHI,R1.)(2;.$12.VL,VHI,R8.))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis CA_MSF : const_at L P_MEMSET_FUNC 8.
  Hypothesis CA_RSA0 : const_at L P_RSA_INFO 4.
  Hypothesis CA_RSA72 : const_at L (P_RSA_INFO + 72) 8.
  Hypothesis CA_RSA80 : const_at L (P_RSA_INFO + 80) 8.
  Hypothesis CA_EC0 : forall e, In e P_EC_INFOS -> const_at L e 4.
  Hypothesis CA_EC72 : forall e, In e P_EC_INFOS -> const_at L (e + 72) 8.
  Hypothesis CA_EC80 : forall e, In e P_EC_INFOS -> const_at L (e + 80) 8.
  Hypothesis CAT_ECGRP : const_at L P_OID_EC_GRP_TBL 440.
  Hypothesis CAT_PKALG : const_at L P_OID_PK_ALG_TBL 120.
  Hypothesis CAT_ECALGID : const_at L P_OID_EC_GRP_ALGID_TBL 80.
  Hypothesis CA_PKTBL : const_at L P_PK_INFO_TBL 32.
  Hypothesis CA_BP : const_at L P_BAD_POINTS 32.
  (* [comment removed for export] *)
  Hypothesis HPRB : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "(2<.$12.VL,VHI,$2=.$2>.$2?.+598:8.$30.)")
(* [comment removed for export] *).
  Hypothesis HCPK : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "(31.$12.VL,VHI,$2=.$32.$2?.+598:8.$33.$34.)")
(* [comment removed for export] *).

  Notation SI := (P_pk_sinv L HL HMC).
  Notation PK := (PKC_inst psegs P_RSA_INFO P_EC_INFOS MT).
  Notation XS := [(P_ECP_IDS_DONE, P_ECP_IDS_DONE + 1); (P_MUL_COUNT, P_MUL_COUNT + 8); (P_ECP_IDS, P_ECP_IDS + 56)].

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (mo0 : Model) (h0 : HST psegs L HI) (LB : list blk) (PP P END BUF PKA lo : Z) (bs : list byte).
  Hypothesis HH0 : HEAP psegs L HI h0 LB m0 mo0.
  Hypothesis HPP0 : rw_cells psegs m0 PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALPP : PP mod 8 = 0.
  Hypothesis HBS0 : bytes_at psegs m0 BUF bs.
  Hypothesis INB : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis BP : BUF <= P.
  Hypothesis PE : P <= END.
  Hypothesis EB : END <= BUF + Z.of_nat (length bs).
  Hypothesis B63 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis HPKA0 : rw_cells psegs m0 PKA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis SPP : bv_unsigned sp <= PP.
  Hypothesis PPT : PP + 8 <= heap_top psegs L HI h0.
  Hypothesis SPK : bv_unsigned sp <= PKA.
  Hypothesis PKT : PKA + 16 <= heap_top psegs L HI h0.
  Hypothesis DPK : PP + 8 <= PKA \/ PKA + 16 <= PP.
  Hypothesis ST0 : stk psegs m0 lo (bv_unsigned sp).
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - PK_PARSE_STACK - hl_stack L.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis HTOP : bv_unsigned sp <= heap_top psegs L HI h0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis MI0 : mem_inv psegs m0.
  Hypothesis SOK0 : statics_ok psegs L m0.
  Hypothesis SIP0 : pk_sinv_P m0.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis DKB : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis DPB : PKA + 16 <= BUF \/ BUF + Z.of_nat (length bs) <= PKA.
  Hypothesis NZPP : 0 < PP.
  Hypothesis NZP : 0 < PKA.
  Hypothesis DSPP : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis DSB : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top psegs L HI h0) PP 8.
  Hypothesis CWP : client_wrange L LB lo (heap_top psegs L HI h0) PKA 16.
  Hypothesis CRB : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis SPR : bv_unsigned sp < 2^64.

  Notation POST := (pk_parse_subpubkey_post psegs L HI PK SI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0).
  Notation FRS mm := (rw_cells psegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
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
  #[using="HL"] Lemma IL1 : hl_data_lo L <= P_ECP_IDS_DONE. Proof. exact (proj1 HL). Qed.
  #[using="L HL"] Lemma IL2 : P_ECP_IDS_DONE + 1 <= P_ECP_IDS. Proof. exact (proj1 (proj2 HL)). Qed.
  #[using="HL"] Lemma IL3 : P_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 HL))). Qed.
  #[using="HMC"] Lemma ML1 : hl_data_lo L <= P_MUL_COUNT. Proof. exact (proj1 HMC). Qed.
  #[using="HMC"] Lemma ML2 : P_MUL_COUNT + 8 <= hl_data_hi L. Proof. exact (proj1 (proj2 HMC)). Qed.

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
  #[using="HFREE HLS SW DIMG HND HPERM CA_MSF CA_RSA80 CA_EC80 CA_BP HPRB HCPK BUF bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR"] Lemma ec_fin_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "Pm,P,(<.&40.)(=.(<.&8.))Pmo,$27.Ph,(26.$12.VL,VHI,)PLB2,(0.$9.)PC,$2.Pp,$2.PE2,$2.Pinfo,$2.Pr,$2.Pg,$35.PNB,(0.$9.)Ppd,(<.&40.)PqX,(<.&40.)PqY,(<.&40.)PqZ,(<.&40.)Plj,(0.(<.&8.))Px1,(<.&40.)Px5,(<.&40.)Px6,(<.&40.)Px7,(<.&40.)Px11,(<.&40.)Px12,(<.&40.)Px13,(<.&40.)Px14,(<.&40.)Px15,(<.&40.)Px16,(<.&40.)Px17,(<.&40.)Px19,(<.&40.)Px28,(<.&40.)Px29,(<.&40.)Px30,(<.&40.)Px31,(<.&40.)P,(3;.VL,VHI,Vsp,Vm0,Vmo0,Vh0,VLB,VPP,VPKA,R1>.R1=.R20.R1?.)P,(13.$12.$2=.R21.R1>.R1=.(36.R18.(37.(20.R1=.+<0.)R16.)(38.(20.R1=.+=0.)R15.R14.R13.)))P,(6.(1.$2.$2.)(14.$2.$2.R1>.+100.)R1?.)P,(3<.VL,R1?.+100.)P,PB,$2.Pk,$2.P,(6.(1.$2.$2.)(14.$2.$2.R2.R1.)VLB,)(3=.(1?.(20.R23.+100.)R3.)(1?.(20.R3.R2.)R23.))P,(6.$2.R1>.$3>.)P,(3?.(39.R1=.))P,(10.(0.$9.)(3:.R1>.)R1=.)P,Pb,$9.(22.(6.$9.R1.R26.)(3=.(6.$9.R1.R1?.)(6.$9.R1.(23.(1.$2.$2.)(14.$2.$2.R25.+100.)VLB,))))P,Pb,$9.P,(6.$9.R1.R20.)(?.(6.$9.R2.(23.(1.$2.$2.)(14.$2.$2.R27.+100.)VLB,)))P,P,(10.$2.R22.=)(29.$2.Lid,$2.(2:.(2:.(1?.=R1.)(40.R1.(21.+2.+1?.)))(41.$42.$43.R1.R28.=R23.R22.)))P,(2:.(40.(44.(21.+2.+1?.))R23.)(1?.R23.=))P,(45.$12.R2<.VPP,(23.$46.(47.(48.&40.R27.))(49.$46.)))P,(2:.(1?.VP,R28.)(1?.R28.R27.))P,(1?.R28.VEND,)P,(45.$12.R2?.VPKA,(23.$46.(47.(48.&40.R28.))(23.$46.(47.(48.&40.R2;.))(49.$46.))))P,(45.$12.R30.(20.(4:.&40.Vsp,)-70.)(23.$46.(4;.#48.R21.)(49.$46.)))P,(45.$12.R31.(20.(4:.&40.Vsp,)-28.)(23.$46.(47.Vs3,)(23.$46.(47.Vs2,)(23.$46.(47.Vs1,)(23.$46.(47.Vs0,)(23.$46.(47.Vra,)(49.$46.)))))))P,(4<.$12.R32.Vlo,(20.(4:.&40.Vsp,)-70.))(4=.$12.R32.(4>.$12.VL,VHI,(4?.$12.$50.$3>.$2=.)(51.VL,VHL,VHMC,)Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPP,VP,VEND,VPKA,Vlo,Vm0,Vmo0,)(52.(53.R23.(48.&40.(20.(4:.&40.Vsp,)-70.))Vgp,Vtp,R22.R21.R20.(48.&40.VPKA,)(48.&40.VPP,)(48.&40.R2;.)R1?.R1>.R1=.R1<.R1;.R1:.R19.(48.&40.R2=.)R18.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R17.R16.R15.R14.)VF,(48.&40.+27480.)Vfc,(54.(<.&40.))R33.(55.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX KP CIN BRC APC EI AP GB LEQ NEWNB RES RR HPP PB E2B HPKA FRL FR ST.
    dpose pa_basics' as (ACP & BAC & BIM & PPD & PKD & SLO').
    dpose CX as (HH & HT & MF & MI & SOK & SIP & SUB & PX). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    dpose BRC as (C0 & C16 & _ & CAC & CIM). pose proof alloc_ceiling_lt as ACLT.
    assert (NDL : List.NoDup (map fst LB)) by exact (HND _ _ _ _ HH0). pose proof (HND _ _ _ _ HH) as ND2.
    assert (NINC : ~ In (C, 256) LB) by (intros Hin; destruct (APC _ _ Hin); clear -H; lia).
    (* [comment removed for export] *)
    assert (REP2 : pk_rep_c psegs P_RSA_INFO P_EC_INFOS MT m LB2 PKA info C (newb LB LB2)).
    { eapply ec_rep_intro; [exact EI| intros E0; rewrite E0 in EI; cbn in EI; clear -EI; intuition discriminate| exact MI| exact ND2| exact KP| exact CIN| | | exact C16| clear -CAC ACLT; lia|].
      - intros d1 d2 H1 H2 NE O1 O2 E. apply (AP d1 d2 (kpi_heap_grp _ _ _ _ _ _ _ H1 O1) (kpi_heap_grp _ _ _ _ _ _ _ H2 O2) NE O1 O2). injection E as Ea Eb. exact Ea.
      - intros d Hd O E. apply (NEWNB (C, 256)); [| left; reflexivity]. rewrite <- E, <- GB. exact (grp_blk_in g d (kpi_heap_grp _ _ _ _ _ _ _ Hd O) O).
      - intros b. rewrite newb_in, kpi_blocks, GB. cbn [In]. rewrite LEQ. cbn [In]. split.
        + (intros dd_H; ddestruct dd_H as [[Hb|[Hb|Hb]] Hn]); [right; exact Hb| left; exact Hb| exfalso; exact (Hn Hb)].
        + intros [Hb|Hb]; [subst b| ]; [split; [right; left; reflexivity| exact NINC]| split; [left; exact Hb| intros HbL; exact (NEWNB b Hb ltac:(right; exact HbL))]]. }
    assert (PERM2 : Permutation LB2 (newb LB LB2 ++ LB)) by (apply newb_perm; [exact ND2| exact NDL| exact SUB]).
    (* [comment removed for export] *)
    assert (REPx : forall LBx, (forall b, In b (newb LB LB2) -> In b LBx) -> pk_rep_c psegs P_RSA_INFO P_EC_INFOS MT m LBx PKA info C (newb LB LB2)).
    { intros LBx Hs. eapply pk_rep_c_frame; [exact REP2| exact MI| exact Hs| intros a _; reflexivity]. }
    zstep. if_cases KZ; zify_cond KZ.
    { (* [comment removed for export] *)
      assert (NZ : r <> 0) by (intros ->; apply KZ; reflexivity).
      eapply fail_free_walk' with (owned := newb LB LB2) (info := info) (ctx := C);
        [ exact CX | exact PERM2 | clear -RR NZ; lia | exact HPP | clear -PB E2B; lia | exact HPKA | apply REPx; intros b Hb; apply in_or_app; left; exact Hb | exact FRL | exact FR | exact ST ]. }
    assert (Z0 : r = 0).
    { clear -KZ RR. apply Z.mod_divide in KZ; [| lia]. destruct KZ as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    subst r. clear KZ RR. ddestruct (RES eq_refl) as (id & IDB & GL). clear RES.
    assert (ID13 : 1 <= id <= 13).
    { destruct GL as [(_ & _ & X & _)|[(_ & X & _)|[(X & _)|(X & _)]]]; [exact X| clear -X; lia| exfalso; unfold MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE in X; clear -X; lia| exfalso; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in X; clear -X; lia]. }
    (* [comment removed for export] *)
    pose proof (pctx_bytes' _ _ _ _ CX) as HBS.
    set (kbs := firstn (Z.to_nat (E2 - p)) (skipn (Z.to_nat (p - BUF)) bs)).
    assert (LENK : Z.of_nat (length kbs) = E2 - p) by (subst kbs; apply P_asn1_get_mpi.bytes_at_sub_length; clear -PB E2B BP EB; lia).
    assert (HKB : bytes_at psegs m p kbs) by (subst kbs; eapply P_asn1_get_mpi.bytes_at_sub; [exact HBS| | |]; clear -PB E2B BP EB; lia).
    clearbody kbs.
    destruct SIP as [IDS [cnt CNT]].
    destruct (P_bad_points_ok L LB2 m SOK CA_BP MI) as [BP1 BP2].
    pose proof (P_pk_ecc_set_pubkey_spec L HI HLS DIMG P_MT HPRB HCPK) as SPK'. unfold pk_ecc_set_pubkey_stmt, pk_ecc_set_pubkey_post, P_PK_ECC_SET_PUBKEY in SPK'.
    zstep. zstep. zstep. zstep.
    eapply aevtM_cut.
    { eapply SPK' with (lo := lo) (h := h) (LB := LB2) (PKA := PKA) (info := info) (C := C) (id := id) (B := p) (bs := kbs) (g := g);
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by (clear -SLO' HLS ACL ACP SPR; lia); rewrite ?LENK, <- ?GB; unfold ECP_KEYPAIR_SIZE;
        first [ exact HH | exact HPKA | exact ALP | exact NZP | exact KP | exact CIN | exact EI | exact HKB | exact CNT | exact BP1 | exact BP2
              | exact TP | exact MI | exact RA | exact SOK | exact CA_MSF | exact ACL | exact DHI | exact ST | reflexivity
              | f_equal; clear; lia
              | (* [comment removed for export] *) right; clear -SPK; lia
              | (* [comment removed for export] *) intros a Ha; destruct (CWP a Ha) as [Q|[Q|(b & Hb & Hr)]]; [left; rewrite HT; exact Q| right; left; exact Q| right; right; exists b; split; [apply SUB; exact Hb| exact Hr]]
              | exact (fresh_apart_pka' C 256 BRC APC ltac:(clear; lia))
              | exact PKD
              | (* [comment removed for export] *) pose proof DI1 as E1'; pose proof DI2 as E2''; clear -CIM E1' E2''; lia
              | (* [comment removed for export] *) rewrite GB; exact GL
              | apply P_curve_statics; [exact MI| exact ID13]
              | clear -PB E2B BP EB BUF0; lia
              | clear -PB E2B BP EB B63; lia
              | (* [comment removed for export] *) intros a Ha; right; right; exists (BUF, Z.of_nat (length bs)); split; [apply SUB; exact INB| cbn; clear -Ha PB E2B BP EB; lia]
              | left; clear -PB E2B BP EB BAC ACL; lia
              | (* [comment removed for export] *) destruct (APC _ _ INB) as [Q|Q]; [right; clear -Q PB E2B BP EB; lia| left; clear -Q PB E2B BP EB; lia]
              | (* [comment removed for export] *) pose proof ML1 as M1; pose proof ML2 as M2; pose proof DI1 as E1'; pose proof DI2 as E2''; destruct BIM as [Q|Q]; [right| left]; clear -Q PB E2B BP EB M1 M2 E1' E2''; lia
              | exact ML1 | exact ML2 | intros a Ha; destruct (proj2 (proj2 HMC) a Ha) as [W NS]; exact (conj NS W)
              | (* [comment removed for export] *) pose proof ML1 as M1; pose proof ML2 as M2; pose proof DI1 as E1'; pose proof DI2 as E2''; clear -CIM M1 M2 E1' E2''; lia
              | exact (proj1 CA_BP) | exact (proj1 (proj2 CA_BP))
              | (* [comment removed for export] *) intros a Ha Hs; exact (proj2 (proj2 CA_BP) a Ha (SW a Hs))
              | (* [comment removed for export] *) unfold P_BAD_POINTS; clear; lia
              | rewrite HT; clear -HTOP SLO' HLS; lia
              | clear -SLO' HLS SPA SPR ACL; lia
              | match goal with |- ?gl => idtac "SPKLEFT" gl end ]. }
    clear SPK'.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2'. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by (clear -SLO' HLS ACL ACP SPR; lia).
    ddestruct PO as (RR3 & MI3 & ST3 & MF3 & HT3 & HH3 & KP3 & PF3 & SG3 & DIS3 & SUB3 & COV3 & NEW3 & HPKA3 & PX3 & SOK3 & CNT3).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m3; rename mox into mo3 end.
    match type of HH3 with HEAP _ _ _ ?hh ?lb _ _ => rename hh into h3; rename lb into LB3 end.
    match type of KP3 with ecp_keypair_at _ _ _ _ _ (mkKP _ _ ?q) => rename q into Q' end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r3 end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3. clear MK.
    (* [comment removed for export] *)
    assert (XF : Forall (fun iv => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C + 208, C + 256); (366760, 366760 + 8)]).
    { pose proof ML2 as M2. constructor; [cbn; left; clear -CAC ACL SLO' HLS; lia| constructor; [cbn; left; clear -M2 DHI ACL SLO' HLS; lia| constructor]]. }
    apply (keep_frame' _ _ _ m m3 _ _ PX3 ltac:(clear; lia)) in FRL; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m m3 _ _ PX3 ltac:(clear; lia)) in FR; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_pp' LB2 _ _ m m3 _ PX3 SUB ltac:(clear; lia)) in HPP;
      [| reflexivity| cbn; pose proof (fresh_apart_pp' C 256 BRC APC ltac:(clear; lia)) as Q; pose proof ML1 as M1; pose proof ML2 as M2; split; [clear -Q; lia| split; [clear -PPD M1 M2; lia| exact I]]].
    assert (CX3 : pctx' h3 LB3 m3 mo3).
    { split; [exact HH3|]. split; [rewrite HT3; exact HT|]. split; [eapply mo_frame_trans; [exact MF| exact MF3]|]. split; [exact MI3|]. split; [exact SOK3|].
      split. { pose proof IL1 as I1; pose proof IL2 as I2; pose proof IL3 as I3; pose proof ML1 as M1; pose proof ML2 as M2; pose proof DI1 as E1'; pose proof DI2 as E2''. split.
               - apply (ecp_ids_state_presx psegs L _ _ _ _ _ m m3 IDS PX3 HL); cbn; unfold P_ECP_IDS_DONE, P_ECP_IDS in *; clear -CIM I1 I2 I3 E1' E2''; (split; [lia| split; [lia| exact I]]).
               - eexists. exact CNT3. }
      split; [intros b Hb; apply SUB3; apply SUB; exact Hb|].
      eapply heap_presx_trans; [exact PX|]. eapply heap_presx_weak''; [exact PX3| exact SUB| clear; lia|].
      intros a Hc Ho. cbn. cbn in Ho. split; [| split; [clear -Ho; tauto| exact I]]. intros Ha. exact (fresh_not_client' C 256 a BRC APC ltac:(clear -Ha; lia) Hc). }
    clear CX HH HT MF SOK IDS CNT PX HBS HKB BP1 BP2.
    (* [comment removed for export] *)
    pose proof (conj MI3 (conj HH3 I)) as BOX3. clear HH3.
    pose proof (munch_refl [(PP, PP + 8)] m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with M : mem_inv psegs m4 |- _ => rename M into MI4 end. match goal with W : wmono psegs m3 m4 |- _ => rename W into WM4 end.
    pose proof (pctx_munch' _ _ _ _ _ _ CX3 MU WM4 MI4 ltac:(constructor; [cbn; right; left; reflexivity| constructor])) as CX4.
    dpose CX4 as (HH4 & HT4 & MF4 & _ & SOK4 & SIP4 & SUB4 & PX4).
    assert (KP4 : ecp_keypair_at psegs P_MT m4 LB3 C (mkKP g (mpd_init (C + 192) pd) Q')).
    { destruct (heap_blocks _ _ HI _ _ _ _ (proj1 (proj2 BOX3))) as [HBR3 _].
      eapply ecp_keypair_at_munch; [exact KP3| exact MU| exact WM4| exact (proj1 BOX3)| exact MI4| cbn [disjoint_from]; pose proof (fresh_apart_pp' C 256 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]|].
      intros d Hd HO. pose proof (kp_mpds_mpdr psegs P_MT m3 LB3 C _ d KP3 Hd) as MDd.
      destruct (mpdr_blk_facts psegs L _ _ _ MDd HO HBR3) as (HIn & N1 & _).
      cbn [disjoint_from]. split; [| exact I].
      (* [comment removed for export] *)
      assert (NOTIN : ~ In (md_p d, 4 * md_n d) LB).
      { intros HbL. unfold kp_mpds in Hd. cbn [kp_grp kp_d kp_Q] in Hd. apply in_app_or in Hd. destruct Hd as [Hd|[<-|Hd]].
        - apply (NEWNB _ ltac:(rewrite <- GB; exact (grp_blk_in g d Hd HO))). right. exact HbL.
        - cbn in HO. discriminate.
        - apply (NEW3 (md_p d, 4 * md_n d)); [| apply SUB; exact HbL]. unfold pt_blocks. apply in_flat_map. exists d. split; [exact Hd| rewrite (mpd_blk_heap d HO); left; reflexivity]. }
      pose proof (blk_apart_pp' h3 LB3 m3 mo3 _ _ (proj1 (proj2 BOX3)) ltac:(intros b Hb; apply SUB4; exact Hb) HIn NOTIN ltac:(clear -N1; lia)) as Q. clear -Q. lia. }
    dpose KP3 as (_ & _ & _ & _ & (EX3 & EY3 & EZ3 & _) & _). clear MU WM4 CX3 KP3.
    match goal with H : rw_cells psegs m4 PP _ |- _ => rename H into HPP4 end.
    (* [comment removed for export] *)
    assert (NDL' : List.NoDup (map fst LB)) by exact NDL. pose proof (HND _ _ _ _ HH4) as ND4.
    assert (CIN4 : In (C, 256) LB3) by (apply SUB3; exact CIN).
    assert (REP4 : pk_rep_c psegs P_RSA_INFO P_EC_INFOS MT m4 LB3 PKA info C (newb LB LB3)).
    { eapply ec_rep_intro; [exact EI| intros E0; rewrite E0 in EI; cbn in EI; clear -EI; intuition discriminate| exact MI4| exact ND4| exact KP4| exact CIN4| | | exact C16| clear -CAC ACLT; lia|].
      - (* [comment removed for export] *)
        intros d1 d2 H1 H2 NE O1 O2. unfold kp_mpds in H1, H2. cbn [kp_grp kp_d kp_Q] in H1, H2.
        assert (CASE : forall d, In d (grp_mpds g ++ mpd_init (C + 192) pd :: pt_mpds Q') -> md_own d = LHeap ->
                         (In d (grp_mpds g) /\ In (md_p d, 4 * md_n d) LB2) \/ (In d (pt_mpds Q') /\ ~ In (md_p d, 4 * md_n d) LB2)).
        { intros d Hd O. apply in_app_or in Hd. destruct Hd as [Hd|[<-|Hd]]; [left| cbn in O; discriminate| right].
          - split; [exact Hd|]. apply (proj2 (LEQ _)). left. rewrite <- GB. exact (grp_blk_in g d Hd O).
          - split; [exact Hd|]. apply NEW3. unfold pt_blocks. apply in_flat_map. exists d. split; [exact Hd| rewrite (mpd_blk_heap d O); left; reflexivity]. }
        destruct (CASE d1 H1 O1) as [[G1 I1]|[Q1 N1]]; destruct (CASE d2 H2 O2) as [[G2 I2]|[Q2 N2]].
        + intros E. apply (AP d1 d2 G1 G2 NE O1 O2). injection E as Ea Eb. exact Ea.
        + intros E. apply N2. rewrite <- E. exact I1.
        + intros E. apply N1. rewrite E. exact I2.
        + (* [comment removed for export] *)
          ddestruct DIS3 as (DXY & DXZ & DYZ).
          cbn in Q1, Q2. destruct Q1 as [<-|[<-|[<-|[]]]]; destruct Q2 as [<-|[<-|[<-|[]]]];
            first [ exfalso; apply NE; reflexivity | exact (DXY O1 O2) | exact (DXZ O1 O2) | exact (DYZ O1 O2)
                  | intros E; symmetry in E; revert E; first [exact (DXY O2 O1)| exact (DXZ O2 O1)| exact (DYZ O2 O1)] ].
      - (* [comment removed for export] *)
        intros d Hd O E. unfold kp_mpds in Hd. cbn [kp_grp kp_d kp_Q] in Hd. apply in_app_or in Hd. destruct Hd as [Hd|[<-|Hd]].
        + apply (NEWNB (C, 256)); [| left; reflexivity]. rewrite <- E, <- GB. exact (grp_blk_in g d Hd O).
        + cbn in O. discriminate.
        + apply (NEW3 (C, 256)); [| exact CIN]. rewrite <- E. unfold pt_blocks. apply in_flat_map. exists d. split; [exact Hd| rewrite (mpd_blk_heap d O); left; reflexivity].
      - (* [comment removed for export] *)
        intros b. rewrite newb_in. unfold kp_blocks. cbn [kp_grp kp_d kp_Q]. cbn [mpd_blk md_own mpd_init app]. rewrite GB. split.
        + intros [Hb Hn]. destruct (COV3 b Hb) as [Hb2|Hq].
          * apply (proj1 (LEQ b)) in Hb2. destruct Hb2 as [Hb2|[Hb2|Hb2]]; [right; apply in_or_app; left; exact Hb2| left; exact Hb2| exfalso; exact (Hn Hb2)].
          * right; apply in_or_app; right; exact Hq.
        + intros [<-|Hb].
          * split; [exact CIN4| exact NINC].
          * apply in_app_or in Hb. destruct Hb as [Hb|Hb].
            -- split; [apply SUB3; apply (proj2 (LEQ b)); left; exact Hb| intros HbL; exact (NEWNB b Hb ltac:(right; exact HbL))].
            -- split; [eapply kp_blocks_in; [exact KP4|]; unfold kp_blocks; cbn [kp_grp kp_d kp_Q]; apply in_or_app; right; apply in_or_app; right; exact Hb
                     | intros HbL; exact (NEW3 b Hb ltac:(apply SUB; exact HbL))]. }
    assert (PERM4 : Permutation LB3 (newb LB LB3 ++ LB)) by (apply newb_perm; [exact ND4| exact NDL'| exact SUB4]).
    assert (REPx4 : forall LBx, (forall b, In b (newb LB LB3) -> In b LBx) -> pk_rep_c psegs P_RSA_INFO P_EC_INFOS MT m4 LBx PKA info C (newb LB LB3)).
    { intros LBx Hs. eapply pk_rep_c_frame; [exact REP4| exact MI4| exact Hs| intros a _; reflexivity]. }
    clear BOX3.
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3.
    - (* [comment removed for export] *)
      assert (Z3 : r3 = 0).
      { clear -K3 RR3. apply Z.mod_divide in K3; [| lia]. destruct K3 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
      subst r3. zstep. if_cases KE; zify_cond KE. 2:{ exfalso. apply KE. reflexivity. }
      zstep. zstep.
      destruct (HPERM _ _ _ _ _ HH4 PERM4) as (h5 & HH5 & HT5).
      eapply ret_walk' with (owned := newb LB LB3) (info := info) (ctx := C) (h := h5) (p' := E2);
        [ exact HH5 | rewrite HT5; exact HT4 | exact MF4 | exact MI4 | exact SOK4 | exact SIP4 | exact PX4 | clear; lia | exact HPP4 | clear -PB E2B; lia
        | exact HPKA3 | apply REPx4; intros b Hb; apply in_or_app; left; exact Hb | intros NZ; exfalso; apply NZ; reflexivity | reflexivity | exact FRL | exact FR | exact ST3 ].
    - (* [comment removed for export] *)
      assert (NZ : r3 <> 0) by (intros ->; apply K3; reflexivity).
      eapply fail_free_walk' with (owned := newb LB LB3) (info := info) (ctx := C);
        [ exact CX4 | exact PERM4 | clear -RR3 NZ; lia | exact HPP4 | clear -PB E2B; lia | exact HPKA3 | apply REPx4; intros b Hb; apply in_or_app; left; exact Hb | exact FRL | exact FR | exact ST3 ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L13345447015.109L24906321761.111L28232829219.4  L47071308384.112L55445551334.110L66152802788.11300000M00j01701T02102NS2ra2sp2PP3PKA2bs2j02oj2W02W5S2ra2sp2PP3PKA2bs2j02oj2W02W5S2j02oj2W02W5S2ra2sp2PP3PKA2bs2j02oj2W02W5S2ra2sp2PP3PKA2bs2j02oj2W02W5S2ra2sp2PP3PKA2bs2j02oj2W02W5". (* [comment removed for export] *)
  #[using="ra PP PKA bs"] Lemma low_frame_merge : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "Pmm,P,(<.&40.)(=.(<.&8.))Pj0,(0.(<.&8.))Pidw,(<.&40.)Pagw,(<.&40.)Pptag,(<.&40.)Pppad,(<.&40.)Pplen,(<.&40.)Pppw,(<.&40.)Plnw,(<.&40.)Palen,(<.&40.)Papw,(<.&40.)Poj,(0.(<.&8.))P,(45.$12.R<.(20.(4:.&40.Vsp,)-70.)(23.$46.(4;.#8.R;.)(49.$46.)))P,(45.$12.R=.(20.(4:.&40.Vsp,)-68.)(23.$46.(56.R;.)(49.$46.)))P,(45.$12.R>.(20.(4:.&40.Vsp,)-64.)(23.$46.(56.R;.)(49.$46.)))P,(45.$12.R?.(20.(4:.&40.Vsp,)-60.)(23.$46.(56.R;.)(23.$46.(56.R:.)(23.$46.(47.R9.)(23.$46.(47.R8.)(49.$46.))))))P,(45.$12.R10.(20.(4:.&40.Vsp,)-48.)(23.$46.(47.R8.)(49.$46.)))P,(45.$12.R11.(20.(4:.&40.Vsp,)-40.)(23.$46.(4;.#8.R6.)(23.$46.(47.R8.)(23.$46.(47.R7.)(49.$46.)))))(45.$12.R12.(20.(4:.&40.Vsp,)-70.)(23.$46.(4;.#48.(8.(<.&8.)R11.(8.(<.&8.)(57.R10.)(8.(<.&8.)(57.R?.)(8.(<.&8.)(57.R>.)(8.(<.&8.)(57.R=.)(8.(<.&8.)(58.R<.)(8.(<.&8.)(58.R;.)(8.(<.&8.)(58.R:.)(8.(<.&8.)R7.(8.(<.&8.)(58.R9.)(58.R8.))))))))))))(49.$46.)))")
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
  #[using="HFREE HLS SW DIMG HND HPERM CA_MSF CA_RSA80 CA_EC80 BUF bs HH0 INB BP PE EB BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP SPR"] Lemma init_fail_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "Pm,P,(<.&40.)(=.(<.&8.))Pmo,$27.Ph,(26.$12.VL,VHI,)PC,$2.Pp,$2.Pinfo,$2.Pr,$2.Pidpad,(<.&40.)PpP,(<.&40.)PpA,(<.&40.)PpB,(<.&40.)PpX,(<.&40.)PpY,(<.&40.)PpZ,(<.&40.)PpN,(<.&40.)Phpad,(<.&40.)Ppd,(<.&40.)PqX,(<.&40.)PqY,(<.&40.)PqZ,(<.&40.)Plj,(0.(<.&8.))Px1,(<.&40.)Px5,(<.&40.)Px6,(<.&40.)Px7,(<.&40.)Px9,(<.&40.)Px11,(<.&40.)Px12,(<.&40.)Px13,(<.&40.)Px14,(<.&40.)Px15,(<.&40.)Px16,(<.&40.)Px17,(<.&40.)Px18,(<.&40.)Px19,(<.&40.)Px28,(<.&40.)Px29,(<.&40.)Px30,(<.&40.)Px31,(<.&40.)P,(3;.VL,VHI,Vsp,Vm0,Vmo0,Vh0,VLB,VPP,VPKA,R25.(23.(1.$2.$2.)(14.$2.$2.R24.+100.)VLB,)R27.R26.)P,(13.$12.$2=.R28.(23.(1.$2.$2.)(14.$2.$2.R25.+100.)VLB,)R25.(59.R25.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.))P,(3<.VL,R26.+100.)P,PB,$2.Pk,$2.P,(6.(1.$2.$2.)(14.$2.$2.R2.R1.)VLB,)(3=.(1?.(20.R2:.+100.)R3.)(1?.(20.R3.R2.)R2:.))P,(6.$2.R26.$3>.)P,(2:.(40.(44.(21.+2.+1?.))R26.)(40.R26.=))P,(45.$12.R2=.VPP,(23.$46.(47.(48.&40.R29.))(49.$46.)))P,(2:.(1?.VP,R2:.)(1?.R2:.VEND,))P,(45.$12.R2?.VPKA,(23.$46.(47.(48.&40.R2:.))(23.$46.(47.(48.&40.R2<.))(49.$46.))))P,(45.$12.R30.(20.(4:.&40.Vsp,)-70.)(23.$46.(4;.#48.R1<.)(49.$46.)))P,(45.$12.R31.(20.(4:.&40.Vsp,)-28.)(23.$46.(47.Vs3,)(23.$46.(47.Vs2,)(23.$46.(47.Vs1,)(23.$46.(47.Vs0,)(23.$46.(47.Vra,)(49.$46.)))))))P,(4<.$12.R32.Vlo,(20.(4:.&40.Vsp,)-70.))(4=.$12.R32.(4>.$12.VL,VHI,(4?.$12.$50.$3>.$2=.)(51.VL,VHL,VHMC,)Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPP,VP,VEND,VPKA,Vlo,Vm0,Vmo0,)(52.(53.R1>.(48.&40.(20.(4:.&40.Vsp,)-70.))Vgp,Vtp,R1=.R1<.R1;.(48.&40.VPKA,)R1:.(48.&40.R2=.)R19.R18.R17.R16.R15.R14.R13.R12.R11.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(48.&40.+2749<.)Vfc,(54.(<.&40.))R33.(55.$12.)))")
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
  #[using="HFREE HCALLOC HLS SW DIMG HND HPERM CA_MSF CA_RSA0 CA_RSA80 CA_EC0 CA_EC80 CAT_ECGRP CA_BP HPRB HCPK bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR"] Lemma ec_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_C ()) "Pm,P,(<.&40.)(=.(<.&8.))Pmo,$27.Ph,(26.$12.VL,VHI,)PC,$2.Pp,$2.PE2,$2.Pinfo,$2.Pta,(<.&40.)Px11,(<.&40.)Pidpad,(<.&40.)PpP,(<.&40.)PpA,(<.&40.)PpB,(<.&40.)PpX,(<.&40.)PpY,(<.&40.)PpZ,(<.&40.)PpN,(<.&40.)Phpad,(<.&40.)Ppd,(<.&40.)PqX,(<.&40.)PqY,(<.&40.)PqZ,(<.&40.)Pj0,(0.(<.&8.))Poj,(0.(<.&8.))Pidw,(<.&40.)Pagw,(<.&40.)Pptag,(<.&40.)Pppad,(<.&40.)Pplen,(<.&40.)Palen,(<.&40.)Papw,(<.&40.)Plnw,(<.&40.)Ppp,$2.Px1,(<.&40.)Px5,(<.&40.)Px6,(<.&40.)Px7,(<.&40.)Px12,(<.&40.)Px13,(<.&40.)Px14,(<.&40.)Px15,(<.&40.)Px16,(<.&40.)Px17,(<.&40.)Px19,(<.&40.)Px28,(<.&40.)Px29,(<.&40.)Px30,(<.&40.)Px31,(<.&40.)P,(3;.VL,VHI,Vsp,Vm0,Vmo0,Vh0,VLB,VPP,VPKA,R2>.(23.(1.$2.$2.)(14.$2.$2.R2=.+100.)VLB,)R30.R2?.)P,(13.$12.$2=.R31.(23.(1.$2.$2.)(14.$2.$2.R2>.+100.)VLB,)R2>.(59.R2>.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.))P,(3<.VL,R2?.+100.)P,PB,$2.Pk,$2.P,(6.(1.$2.$2.)(14.$2.$2.R2.R1.)VLB,)(3=.(1?.(20.R33.+100.)R3.)(1?.(20.R3.R2.)R33.))P,(6.$2.R2>.$3>.)P,(3=.(2:.(10.$2.R15.=)(2:.(10.$2.(4:.&40.R19.)=)(10.(<.&40.)R1;.(48.&40.=))))(2:.(1?.VBUF,R15.)(1?.(20.R15.(4:.&40.R19.))R30.)))P,(45.$12.R36.VPP,(23.$46.(47.(48.&40.R32.))(49.$46.)))P,(2:.(1?.VP,R33.)(1?.R33.R32.))P,(1?.R33.VEND,)P,(45.$12.R39.VPKA,(23.$46.(47.(48.&40.R33.))(23.$46.(47.(48.&40.R36.))(49.$46.))))P,(45.$12.R3:.(20.(4:.&40.Vsp,)-70.)(23.$46.(4;.#8.R24.)(49.$46.)))P,(45.$12.R3;.(20.(4:.&40.Vsp,)-68.)(23.$46.(56.R23.)(49.$46.)))P,(45.$12.R3<.(20.(4:.&40.Vsp,)-64.)(23.$46.(56.R23.)(49.$46.)))P,(45.$12.R3=.(20.(4:.&40.Vsp,)-60.)(23.$46.(56.R23.)(23.$46.(56.R22.)(23.$46.(47.R21.)(23.$46.(47.(48.&40.R1=.))(49.$46.))))))P,(45.$12.R3>.(20.(4:.&40.Vsp,)-48.)(23.$46.(47.R1?.)(49.$46.)))P,(45.$12.R3?.(20.(4:.&40.Vsp,)-40.)(23.$46.(4;.#8.R28.)(23.$46.(47.R22.)(23.$46.(47.R21.)(49.$46.)))))P,(45.$12.R40.(20.(4:.&40.Vsp,)-28.)(23.$46.(47.Vs3,)(23.$46.(47.Vs2,)(23.$46.(47.Vs1,)(23.$46.(47.Vs0,)(23.$46.(47.Vra,)(49.$46.)))))))P,(4<.$12.R41.Vlo,(20.(4:.&40.Vsp,)-70.))(4=.$12.R41.(4>.$12.VL,VHI,(4?.$12.$50.$3>.$2=.)(51.VL,VHL,VHMC,)Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPP,VP,VEND,VPKA,Vlo,Vm0,Vmo0,)(52.(53.R21.(48.&40.(20.(4:.&40.Vsp,)-70.))Vgp,Vtp,R20.R1?.R1>.(48.&40.VPKA,)(48.&40.VPP,)R3;.R3:.R1=.R1<.R1;.R1:.R19.R18.(48.&40.R3=.)R17.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R16.R15.R14.R13.)VF,(48.&40.+27414.)Vfc,(54.(<.&40.))R42.(55.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX KP BRC APC EI PARD HPP PB E2B HPKA F0 FID FALG FPAR FLEN FOID FR ST.
    dpose pa_basics' as (ACP & BAC & BIM & PPD & PKD & SLO').
    dpose CX as (HH & HT & MF & MI & SOK & SIP & SUB & PX). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    dpose BRC as (C0 & C16 & _ & CAC & CIM). pose proof alloc_ceiling_lt as ACLT.
    pose proof (bv_unsigned_in_range 64 plen) as PLR. change (bv_modulus 64) with (2^64) in PLR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KA; zify_cond KA.
    { (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply init_fail_walk; [exact CX| exact KP| exact BRC| exact APC| exact EI| clear; lia| exact HPP| clear -PB E2B; lia| exact HPKA
        | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR| exact ST]. }
    clear KA.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof (P_pk_use_ecparams_spec L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 HL) as SEP. unfold pk_use_ecparams_stmt, pk_use_ecparams_post, P_PK_USE_ECPARAMS in SEP.
      replace plen with (Z_to_bv 64 (bv_unsigned plen)) in FPAR by (apply definitions.Z_to_bv_bv_unsigned).
      destruct SIP as [IDS [cnt CNT]].
      eapply aevtM_cut.
      { eapply SEP with (lo := lo) (h := h) (LB := (C, 256) :: LB) (PKA := PKA) (info := info) (C := C) (PAR := bv_unsigned sp + -96) (LEN := bv_unsigned plen) (P := pp) (BUF := BUF) (bs := bs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by (clear -SLO' HLS ACL ACP SPR; lia); unfold ECP_KEYPAIR_SIZE;
          first [ exact HH | exact HPKA | exact ALP | exact NZP | exact EI | exact KP | exact FPAR | exact IDS | exact SOK | exact CA_MSF | exact CAT_ECGRP | exact CA_EC0
                | exact TP | exact MI | exact ACL | exact DHI | exact ST | exact B63 | exact BUF0 | exact PKD | reflexivity
                | right; clear -SPK; lia
                | (* [comment removed for export] *) intros a Ha; destruct (CWP a Ha) as [Q|[Q|(b & Hb & Hr)]]; [left; rewrite HT; exact Q| right; left; exact Q| right; right; exists b; split; [right; exact Hb| exact Hr]]
                | exact (fresh_apart_pka' C 256 BRC APC ltac:(clear; lia))
                | left; reflexivity
                | pose proof DI1 as E1'; pose proof DI2 as E2''; clear -CIM E1' E2''; lia
                | clear -SPA SPR; lia | clear -SLO' HLS ACL ACP; lia
                | right; clear; lia
                | (* [comment removed for export] *) right; pose proof DI2 as E2''; clear -DHI ACL SLO' HLS E2''; lia
                | right; clear -CAC ACL SLO' HLS; lia
                | eapply pctx_bytes'; exact CX
                | right; exact INB
                | (* [comment removed for export] *) destruct PARD as [(Q1 & Q2 & Q3)|(Q1 & Q2)]; [left; split; [exact Q1| split; [exact Q2| exact Q3]]| right; split; [exact Q1| clear -Q2 E2B EB PE; lia]]
                | clear -PLR; lia
                | rewrite HT; clear -HTOP SLO' HLS; lia
                | match goal with |- ?gl => idtac "EPLEFT" gl end ]. }
      clear SEP.
      intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2'. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by (clear -SLO' HLS ACL ACP SPR; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & LEQ & NEWNB & KP2 & AP2 & GB2 & RES & RR2 & HPKA2 & PX2 & SOK2 & IDS2).
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
      match type of HH2 with HEAP _ _ _ ?hh ?lb _ _ => rename hh into h2; rename lb into LB2 end.
      match type of GB2 with grp_blocks ?gg = ?nb => rename gg into g'; rename nb into NB end.
      cbn [kp_grp kp_d kp_Q kp_init] in KP2, RES.
      (* [comment removed for export] *)
      assert (XF : Forall (fun iv => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C, C + ECP_GROUP_SIZE); (P_ECP_IDS_DONE, P_ECP_IDS_DONE + 1); (P_ECP_IDS, P_ECP_IDS + 56)]).
      { pose proof IL3 as I3. pose proof IL2 as I2. unfold ECP_GROUP_SIZE. constructor; [cbn; left; clear -CAC ACL SLO' HLS; lia|].
        constructor; [cbn; left; clear -I2 I3 DHI ACL SLO' HLS; lia|]. constructor; [cbn; left; clear -I3 DHI ACL SLO' HLS; lia| constructor]. }
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in F0; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FID; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FALG; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FPAR; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FLEN; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FOID; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FR; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_pp' ((C, 256) :: LB) _ _ m m2 _ PX2 ltac:(intros b Hb; right; exact Hb) ltac:(clear; lia)) in HPP;
        [| reflexivity| cbn; unfold ECP_GROUP_SIZE; pose proof (fresh_apart_pp' C 256 BRC APC ltac:(clear; lia)) as Q; pose proof IL1 as I1; pose proof IL2 as I2; pose proof IL3 as I3;
           split; [clear -Q; lia| split; [clear -PPD I1 I2 I3; lia| split; [clear -PPD I1 I2 I3; lia| exact I]]]].
      assert (CX2 : pctx' h2 LB2 m2 mo2).
      { split; [exact HH2|]. split; [rewrite HT2; exact HT|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|]. split; [exact MI2|]. split; [exact SOK2|].
        split. { split; [exact IDS2|]. exists cnt. pose proof ML1 as M1; pose proof ML2 as M2; pose proof DI1 as E1'; pose proof DI2 as E2''.
                 eapply heap_presx_rw_cells; [exact PX2| exact CNT| |]; cbn [cells_size csize Nat.add disjoint_from].
                 - intros a Ha. right; left. split; [clear -Ha M1 M2; lia| exact (proj2 (proj2 (proj2 HMC) a Ha))].
                 - unfold ECP_GROUP_SIZE, P_ECP_IDS_DONE, P_ECP_IDS. split; [clear -CIM M1 M2 E1' E2''; lia| split; [clear; lia| split; [clear; lia| exact I]]]. }
        split; [intros b Hb; apply (proj2 (LEQ b)); right; right; exact Hb|].
        eapply heap_presx_trans; [exact PX|]. eapply heap_presx_weak''; [exact PX2| intros b Hb; right; exact Hb| clear; lia|].
        intros a Hc Ho. cbn in Ho |- *. unfold ECP_GROUP_SIZE. split; [| clear -Ho; tauto]. intros Ha. exact (fresh_not_client' C 256 a BRC APC ltac:(clear -Ha; lia) Hc). }
      eapply ec_fin_walk with (NB := NB) (g := g');
        [ exact CX2 | exact KP2 | apply (proj2 (LEQ _)); right; left; reflexivity | exact BRC | exact APC | exact EI | exact AP2 | exact GB2 | exact LEQ | exact NEWNB
        | intros Z0; destruct RES as [(id & IDB & GL)|(NZ & _)]; [exists id; subst; exact (conj IDB GL)| exfalso; exact (NZ Z0)]
        | exact RR2 | exact HPP | exact PB | exact E2B | exact HPKA2
        | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR | exact ST2 ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases KT; zify_cond KT.
      { eapply init_fail_walk; [exact CX| exact KP| exact BRC| exact APC| exact EI| clear; lia| exact HPP| clear -PB E2B; lia| exact HPKA
          | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR| exact ST]. }
      zstep. zstep. if_cases KL; zify_cond KL.
      { eapply init_fail_walk; [exact CX| exact KP| exact BRC| exact APC| exact EI| clear; lia| exact HPP| clear -PB E2B; lia| exact HPKA
          | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR| exact ST]. }
      (* [comment removed for export] *)
      pose proof (bv_unsigned_in_range 64 (sx32 idw)) as UR. change (bv_modulus 64) with (2^64) in UR.
      pose proof (land_m5_9 _ UR KR) as U913. set (u := bv_unsigned (sx32 idw)) in *.
      assert (IDB : 0 <= u < 2^31) by (clear -U913; lia).
      pose proof (P_pk_ecc_set_group_spec L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0) as SSG. unfold pk_ecc_set_group_stmt, pk_ecc_set_group_post, P_PK_ECC_SET_GROUP in SSG.
      destruct SIP as [IDS [cnt CNT]].
      zstep. zstep.
      eapply aevtM_cut.
      { eapply SSG with (lo := lo) (h := h) (LB := (C, 256) :: LB) (PKA := PKA) (info := info) (C := C) (id := u);
          rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by (clear -SLO' HLS ACL ACP SPR; lia); unfold ECP_KEYPAIR_SIZE;
          first [ exact HH | exact HPKA | exact ALP | exact NZP | exact EI | exact KP | exact IDB | exact SOK | exact CA_MSF | exact CA_EC0
                | exact TP | exact MI | exact ACL | exact DHI | exact ST | exact PKD | reflexivity
                | right; clear -SPK; lia
                | intros a Ha; destruct (CWP a Ha) as [Q|[Q|(b & Hb & Hr)]]; [left; rewrite HT; exact Q| right; left; exact Q| right; right; exists b; split; [right; exact Hb| exact Hr]]
                | exact (fresh_apart_pka' C 256 BRC APC ltac:(clear; lia))
                | left; reflexivity
                | pose proof DI1 as E1'; pose proof DI2 as E2''; clear -CIM E1' E2''; lia
                | clear -SLO' HLS ACL ACP SPA SPR; lia
                | rewrite HT; clear -HTOP SLO' HLS; lia
                | subst u; symmetry; apply definitions.Z_to_bv_bv_unsigned
                | match goal with |- ?gl => idtac "SGLEFT" gl end ]. }
      clear SSG.
      intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2'. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by (clear -SLO' HLS ACL ACP SPR; lia).
      ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & LEQ & NEWNB & KP2 & AP2 & GB2 & GL & HPKA2 & PX2 & SOK2).
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
      match type of HH2 with HEAP _ _ _ ?hh ?lb _ _ => rename hh into h2; rename lb into LB2 end.
      match type of GB2 with grp_blocks ?gg = ?nb => rename gg into g'; rename nb into NB end.
      match type of GL with gl_result _ _ _ _ ?rr _ _ => rename rr into r2 end.
      cbn [kp_grp kp_d kp_Q kp_init] in KP2. unfold ECP_GROUP_SIZE in PX2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      assert (RR2 : -2^31 < r2 <= 0).
      { destruct GL as [(X & _)|[(X & _)|[(X & _)|(X & _)]]]; rewrite X; unfold MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE, MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia. }
      (* [comment removed for export] *)
      assert (XF : Forall (fun iv => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C, C + 192)]).
      { constructor; [cbn; left; clear -CAC ACL SLO' HLS; lia| constructor]. }
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in F0; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FID; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FALG; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FPAR; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FLEN; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FOID; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_frame' _ _ _ m m2 _ _ PX2 ltac:(clear; lia)) in FR; [| clear; lia| cbn; clear; lia| exact XF].
      apply (keep_pp' ((C, 256) :: LB) _ _ m m2 _ PX2 ltac:(intros b Hb; right; exact Hb) ltac:(clear; lia)) in HPP;
        [| reflexivity| cbn; pose proof (fresh_apart_pp' C 256 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]].
      assert (CX2 : pctx' h2 LB2 m2 mo2).
      { split; [exact HH2|]. split; [rewrite HT2; exact HT|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|]. split; [exact MI2|]. split; [exact SOK2|].
        split. { pose proof IL1 as I1; pose proof IL2 as I2; pose proof IL3 as I3; pose proof ML1 as M1; pose proof ML2 as M2; pose proof DI1 as E1'; pose proof DI2 as E2''. split.
                 - apply (ecp_ids_state_presx psegs L _ _ _ _ _ m m2 IDS PX2 HL); cbn; clear -CIM I1 I2 I3 E1' E2''; (split; [lia| exact I]).
                 - exists cnt. eapply heap_presx_rw_cells; [exact PX2| exact CNT| |]; cbn [cells_size csize Nat.add disjoint_from].
                   + intros a Ha. right; left. split; [clear -Ha M1 M2; lia| exact (proj2 (proj2 (proj2 HMC) a Ha))].
                   + split; [clear -CIM M1 M2 E1' E2''; lia| exact I]. }
        split; [intros b Hb; apply (proj2 (LEQ b)); right; right; exact Hb|].
        eapply heap_presx_trans; [exact PX|]. eapply heap_presx_weak''; [exact PX2| intros b Hb; right; exact Hb| clear; lia|].
        intros a Hc Ho. cbn. split; [| exact I]. intros Ha. exact (fresh_not_client' C 256 a BRC APC ltac:(clear -Ha; lia) Hc). }
      zstep.
      eapply ec_fin_walk with (NB := NB) (g := g');
        [ exact CX2 | exact KP2 | apply (proj2 (LEQ _)); right; left; reflexivity | exact BRC | exact APC | exact EI | exact AP2 | exact GB2 | exact LEQ | exact NEWNB
        | intros Z0; exists u; rewrite Z0 in GL; exact (conj IDB GL)
        | exact RR2 | exact HPP | exact PB | exact E2B | exact HPKA2
        | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR | exact ST2 ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.
