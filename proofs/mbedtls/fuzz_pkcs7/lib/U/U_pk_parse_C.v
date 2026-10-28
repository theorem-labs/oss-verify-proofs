(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Bytes MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points U_asn1_get_mpi U_asn1_get_alg_A U_pk_ecparams U_ecp_statics U_ecp_check_pubkey U_ecp_point_read_binary U_pk_ecc_set_pubkey_proof U_pk_parse_A.
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
Ltac2 gd_tbl_P_pk_parse_C () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Stdlib.Lists.List.In"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "newb"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_kp"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_blocks"; "RocqVerifyHarness.AgentSubmission.USpec.RepPk.pk_rep_c"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.U.U_pk_parse_A.pctx"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_load.gl_result"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "RocqVerifyHarness.AgentSubmission.USpec.RepPk.PKC_inst"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_RSA_INFO"; "RocqVerifyHarness.AgentSubmission.U.U_pk_sinv.U_pk_sinv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"].


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
  Notation FRS mm := (rw_cells usegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
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
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (LB2 : @Corelib.Init.Datatypes.list (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (C : @Corelib.Numbers.BinNums.Z), forall (p :
    @Corelib.Numbers.BinNums.Z), forall (E2 : @Corelib.Numbers.BinNums.Z), forall (info : @Corelib.Numbers.BinNums.Z), forall (r : @Corelib.Numbers.BinNums.Z), forall (g :
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.ecp_grp), forall (NB : @Corelib.Init.Datatypes.list (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (pd :
    @stdpp.bitvector.definitions.bv 64%N), forall (qX : @stdpp.bitvector.definitions.bv 64%N), forall (qY : @stdpp.bitvector.definitions.bv 64%N), forall (qZ :
    @stdpp.bitvector.definitions.bv 64%N), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 : @stdpp.bitvector.definitions.bv 64%N), forall
    (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x12 : @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x15 : @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 :
    @stdpp.bitvector.definitions.bv 64%N), forall (p0 : @Corelib.Numbers.BinNums.Z), forall (x20 : @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv
    64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 : @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N),
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0 mo0 h0 LB PP PKA h LB2 m mo -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.ecp_keypair_at
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m LB2 C (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.mkKP g
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.mpd_init (@Stdlib.ZArith.BinInt.Z.add C 192%Z) pd) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.pt_init
    (@Stdlib.ZArith.BinInt.Z.add C 208%Z) qX qY qZ)) -> @Stdlib.Lists.List.In (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB2 -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.block_range L C 256%Z ->
    (forall (B : @Corelib.Numbers.BinNums.Z), forall (k : @Corelib.Numbers.BinNums.Z), @Stdlib.Lists.List.In (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z)
    (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) B k) LB -> @Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le
    (@Stdlib.ZArith.BinInt.Z.add C 256%Z) B) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add B k) C)) -> @Stdlib.Lists.List.In (@Corelib.Numbers.BinNums.Z) info
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.EcpFacts.mpds_apart (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.grp_mpds
    g) -> @Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.grp_blocks g) NB
    -> (forall (b : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk), @Corelib.Init.Logic.iff (@Stdlib.Lists.List.In (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b LB2)
    (@Corelib.Init.Logic.or (@Stdlib.Lists.List.In (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b NB) (@Stdlib.Lists.List.In
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB)))) -> (forall (b : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk),
    @Stdlib.Lists.List.In (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b NB -> @Corelib.Init.Logic.not (@Stdlib.Lists.List.In
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) b (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB))) -> (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) r 0%Z ->
    @Corelib.Init.Logic.ex (@Corelib.Numbers.BinNums.Z) (fun (id : @Corelib.Numbers.BinNums.Z) => @Corelib.Init.Logic.and (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le 0%Z id)
    (@Stdlib.ZArith.BinInt.Z.lt id (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z))) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_group_load.gl_result
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_CA) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_ONE) id C 0%Z g NB))) -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.lt (@Stdlib.ZArith.BinInt.Z.opp (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.le r 0%Z) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p E2) -> @Stdlib.ZArith.BinInt.Z.le E2 END ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N info); @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N C)] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat lj] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-48)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le BUF p0) (@Stdlib.ZArith.BinInt.Z.le p0 END) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) (@stdpp.bitvector.definitions.Z_to_bv 64%N PP) (@stdpp.bitvector.definitions.Z_to_bv 64%N r) x11 x12 x13
    x14 x15 x16 x17 (@stdpp.bitvector.definitions.Z_to_bv 64%N E2) (@stdpp.bitvector.definitions.Z_to_bv 64%N p0) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x294c4%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX KP CIN BRC APC EI AP GB LEQ NEWNB RES RR HPP PB E2B HPKA FRL FR ST P00.
    dpose pa_basics' as (ACP & BAC & BIM & PPD & PKD & SLO').
    dpose CX as (HH & HT & MF & MI & SOK & SIP & SUB & PX). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    dpose BRC as (C0 & C16 & _ & CAC & CIM). pose proof alloc_ceiling_lt as ACLT.
    assert (NDL : List.NoDup (map fst LB)) by exact (HND _ _ _ _ HH0). pose proof (HND _ _ _ _ HH) as ND2.
    assert (NINC : ~ In (C, 256) LB) by (intros Hin; destruct (APC _ _ Hin); clear -H; lia).
    (* [comment removed for export] *)
    assert (REP2 : pk_rep_c usegs U_RSA_INFO U_EC_INFOS MT m LB2 PKA info C (newb LB LB2)).
    { eapply ec_rep_intro; [exact EI| intros E0; rewrite E0 in EI; cbn in EI; clear -EI; intuition discriminate| exact MI| exact ND2| exact KP| exact CIN| | | exact C16| clear -CAC ACLT; lia|].
      - intros d1 d2 H1 H2 NE O1 O2 E. apply (AP d1 d2 (kpi_heap_grp _ _ _ _ _ _ _ H1 O1) (kpi_heap_grp _ _ _ _ _ _ _ H2 O2) NE O1 O2). injection E as Ea Eb. exact Ea.
      - intros d Hd O E. apply (NEWNB (C, 256)); [| left; reflexivity]. rewrite <- E, <- GB. exact (grp_blk_in g d (kpi_heap_grp _ _ _ _ _ _ _ Hd O) O).
      - intros b. rewrite newb_in, kpi_blocks, GB. cbn [In]. rewrite LEQ. cbn [In]. split.
        + (intros dd_H; ddestruct dd_H as [[Hb|[Hb|Hb]] Hn]); [right; exact Hb| left; exact Hb| exfalso; exact (Hn Hb)].
        + intros [Hb|Hb]; [subst b| ]; [split; [right; left; reflexivity| exact NINC]| split; [left; exact Hb| intros HbL; exact (NEWNB b Hb ltac:(right; exact HbL))]]. }
    assert (PERM2 : Permutation LB2 (newb LB LB2 ++ LB)) by (apply newb_perm; [exact ND2| exact NDL| exact SUB]).
    (* [comment removed for export] *)
    assert (REPx : forall LBx, (forall b, In b (newb LB LB2) -> In b LBx) -> pk_rep_c usegs U_RSA_INFO U_EC_INFOS MT m LBx PKA info C (newb LB LB2)).
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
    assert (LENK : Z.of_nat (length kbs) = E2 - p) by (subst kbs; apply U_asn1_get_mpi.bytes_at_sub_length; clear -PB E2B BP EB; lia).
    assert (HKB : bytes_at usegs m p kbs) by (subst kbs; eapply U_asn1_get_mpi.bytes_at_sub; [exact HBS| | |]; clear -PB E2B BP EB; lia).
    clearbody kbs.
    destruct SIP as [IDS [cnt CNT]].
    destruct (U_bad_points_ok L LB2 m SOK CA_BP MI) as [BP1 BP2].
    pose proof (U_pk_ecc_set_pubkey_spec L HI HLS DIMG U_MT HPRB HCPK) as SPK'. unfold pk_ecc_set_pubkey_stmt, pk_ecc_set_pubkey_post, U_PK_ECC_SET_PUBKEY in SPK'.
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
              | apply U_curve_statics; [exact MI| exact ID13]
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
              | (* [comment removed for export] *) unfold U_BAD_POINTS; clear; lia
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
    assert (XF : Forall (fun iv => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C + 208, C + 256); (380840, 380840 + 8)]).
    { pose proof ML2 as M2. constructor; [cbn; left; clear -CAC ACL SLO' HLS; lia| constructor; [cbn; left; clear -M2 DHI ACL SLO' HLS; lia| constructor]]. }
    apply (keep_frame' _ _ _ m m3 _ _ PX3 ltac:(clear; lia)) in FRL; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m m3 _ _ PX3 ltac:(clear; lia)) in FR; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_pp' LB2 _ _ m m3 _ PX3 SUB ltac:(clear; lia)) in HPP;
      [| reflexivity| cbn; pose proof (fresh_apart_pp' C 256 BRC APC ltac:(clear; lia)) as Q; pose proof ML1 as M1; pose proof ML2 as M2; split; [clear -Q; lia| split; [clear -PPD M1 M2; lia| exact I]]].
    assert (CX3 : pctx' h3 LB3 m3 mo3).
    { split; [exact HH3|]. split; [rewrite HT3; exact HT|]. split; [eapply mo_frame_trans; [exact MF| exact MF3]|]. split; [exact MI3|]. split; [exact SOK3|].
      split. { pose proof IL1 as I1; pose proof IL2 as I2; pose proof IL3 as I3; pose proof ML1 as M1; pose proof ML2 as M2; pose proof DI1 as E1'; pose proof DI2 as E2''. split.
               - apply (ecp_ids_state_presx usegs L _ _ _ _ _ m m3 IDS PX3 HL); cbn; unfold U_ECP_IDS_DONE, U_ECP_IDS in *; clear -CIM I1 I2 I3 E1' E2''; (split; [lia| split; [lia| exact I]]).
               - eexists. exact CNT3. }
      split; [intros b Hb; apply SUB3; apply SUB; exact Hb|].
      eapply heap_presx_trans; [exact PX|]. eapply heap_presx_weak''; [exact PX3| exact SUB| clear; lia|].
      intros a Hc Ho. cbn. cbn in Ho. split; [| split; [clear -Ho; tauto| exact I]]. intros Ha. exact (fresh_not_client' C 256 a BRC APC ltac:(clear -Ha; lia) Hc). }
    clear CX HH HT MF SOK IDS CNT PX HBS HKB BP1 BP2.
    (* [comment removed for export] *)
    pose proof (conj MI3 (conj HH3 I)) as BOX3. clear HH3.
    pose proof (munch_refl [(PP, PP + 8)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep. zstep. zstep. zstep. pk_ckb KN ltac:(clear -P00 PB E2B BP EB BUF0 B63; lia).
    zstep. zstep. zstep. zstep. zstep. zstep. pk_ckb KS ltac:(clear -P00 PB E2B BP EB BUF0 B63; lia).
    zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with M : mem_inv usegs m4 |- _ => rename M into MI4 end. match goal with W : wmono usegs m3 m4 |- _ => rename W into WM4 end.
    pose proof (pctx_munch' _ _ _ _ _ _ CX3 MU WM4 MI4 ltac:(constructor; [cbn; right; left; reflexivity| constructor])) as CX4.
    dpose CX4 as (HH4 & HT4 & MF4 & _ & SOK4 & SIP4 & SUB4 & PX4).
    assert (KP4 : ecp_keypair_at usegs U_MT m4 LB3 C (mkKP g (mpd_init (C + 192) pd) Q')).
    { destruct (heap_blocks _ _ HI _ _ _ _ (proj1 (proj2 BOX3))) as [HBR3 _].
      eapply ecp_keypair_at_munch; [exact KP3| exact MU| exact WM4| exact (proj1 BOX3)| exact MI4| cbn [disjoint_from]; pose proof (fresh_apart_pp' C 256 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]|].
      intros d Hd HO. pose proof (kp_mpds_mpdr usegs U_MT m3 LB3 C _ d KP3 Hd) as MDd.
      destruct (mpdr_blk_facts usegs L _ _ _ MDd HO HBR3) as (HIn & N1 & _).
      cbn [disjoint_from]. split; [| exact I].
      (* [comment removed for export] *)
      assert (NOTIN : ~ In (md_p d, 4 * md_n d) LB).
      { intros HbL. unfold kp_mpds in Hd. cbn [kp_grp kp_d kp_Q] in Hd. apply in_app_or in Hd. destruct Hd as [Hd|[<-|Hd]].
        - apply (NEWNB _ ltac:(rewrite <- GB; exact (grp_blk_in g d Hd HO))). right. exact HbL.
        - cbn in HO. discriminate.
        - apply (NEW3 (md_p d, 4 * md_n d)); [| apply SUB; exact HbL]. unfold pt_blocks. apply in_flat_map. exists d. split; [exact Hd| rewrite (mpd_blk_heap d HO); left; reflexivity]. }
      pose proof (blk_apart_pp' h3 LB3 m3 mo3 _ _ (proj1 (proj2 BOX3)) ltac:(intros b Hb; apply SUB4; exact Hb) HIn NOTIN ltac:(clear -N1; lia)) as Q. clear -Q. lia. }
    dpose KP3 as (_ & _ & _ & _ & (EX3 & EY3 & EZ3 & _) & _). clear MU WM4 CX3 KP3.
    match goal with H : rw_cells usegs m4 PP _ |- _ => rename H into HPP4 end.
    (* [comment removed for export] *)
    assert (NDL' : List.NoDup (map fst LB)) by exact NDL. pose proof (HND _ _ _ _ HH4) as ND4.
    assert (CIN4 : In (C, 256) LB3) by (apply SUB3; exact CIN).
    assert (REP4 : pk_rep_c usegs U_RSA_INFO U_EC_INFOS MT m4 LB3 PKA info C (newb LB LB3)).
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
    assert (REPx4 : forall LBx, (forall b, In b (newb LB LB3) -> In b LBx) -> pk_rep_c usegs U_RSA_INFO U_EC_INFOS MT m4 LBx PKA info C (newb LB LB3)).
    { intros LBx Hs. eapply pk_rep_c_frame; [exact REP4| exact MI4| exact Hs| intros a _; reflexivity]. }
    clear BOX3.
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3.
    - (* [comment removed for export] *)
      assert (Z3 : r3 = 0).
      { clear -K3 RR3. apply Z.mod_divide in K3; [| lia]. destruct K3 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
      subst r3. zstep. if_cases KE; zify_cond KE. 2:{ exfalso. first [ apply KE; reflexivity | clear -KE PB E2B BP EB B63 BUF0; rewrite ?unsigned_lit in KE by lia; lia ]. }
      zstep. zstep.
      destruct (HPERM _ _ _ _ _ HH4 PERM4) as (h5 & HH5 & HT5).
      eapply ret_walk' with (owned := newb LB LB3) (info := info) (ctx := C) (h := h5);
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
  #[using="ra PP PKA bs"] Lemma low_frame_merge : forall (mm : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (j0 : @Corelib.Init.Datatypes.list
    (@stdpp.bitvector.definitions.bv 8%N)), forall (idw : @stdpp.bitvector.definitions.bv 64%N), forall (agw : @stdpp.bitvector.definitions.bv 64%N), forall (ptag :
    @stdpp.bitvector.definitions.bv 64%N), forall (ppad : @stdpp.bitvector.definitions.bv 64%N), forall (plen : @stdpp.bitvector.definitions.bv 64%N), forall (ppw :
    @stdpp.bitvector.definitions.bv 64%N), forall (lnw : @stdpp.bitvector.definitions.bv 64%N), forall (alen : @stdpp.bitvector.definitions.bv 64%N), forall (oj :
    @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat j0] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-104)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 idw] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-100)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 agw] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-96)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ptag; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ppad; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 plen;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ppw] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-72)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 lnw] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-64)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat oj; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 alen] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mm (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-112)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) j0 (@Corelib.Init.Datatypes.app
    (@stdpp.bitvector.definitions.bv 8%N) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le4 idw) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le4 agw) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le4 ptag)
    (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le4 ppad) (@Corelib.Init.Datatypes.app
    (@stdpp.bitvector.definitions.bv 8%N) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le8 plen) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le8 ppw) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le8 lnw)
    (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) oj (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.le8 alen))))))))))]
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
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
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
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0 mo0 h0 LB PP PKA h (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z)
    (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB) m mo ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.ecp_keypair_at (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m
    (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z)
    (@Corelib.Numbers.BinNums.Z) C 256%Z) LB) C (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_keypair_init.kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.block_range L C 256%Z -> (forall (B : @Corelib.Numbers.BinNums.Z), forall (k : @Corelib.Numbers.BinNums.Z), @Stdlib.Lists.List.In
    (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) B
    k) LB -> @Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add C 256%Z) B) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add B k) C)) ->
    @Stdlib.Lists.List.In (@Corelib.Numbers.BinNums.Z) info (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt
    (@Stdlib.ZArith.BinInt.Z.opp (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.lt r 0%Z) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p END) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA
    [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N info); @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N C)] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat lj] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-48)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) x9 (@stdpp.bitvector.definitions.Z_to_bv 64%N r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9
    s10 s11 x28 x29 x30 x31) F (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x2950c%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
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
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
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
    @stdpp.bitvector.definitions.bv 64%N), @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0 mo0 h0 LB PP PKA h (@Corelib.Init.Datatypes.cons
    (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C
    256%Z) LB) m mo -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepEcp.ecp_keypair_at (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 256%Z) LB) C (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_keypair_init.kp_init C idpad pP
    pA pB pX pY pZ pN hpad pd qX qY qZ) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.block_range L C 256%Z -> (forall (B : @Corelib.Numbers.BinNums.Z), forall (k :
    @Corelib.Numbers.BinNums.Z), @Stdlib.Lists.List.In (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair
    (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) B k) LB -> @Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add C 256%Z) B)
    (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add B k) C)) -> @Stdlib.Lists.List.In (@Corelib.Numbers.BinNums.Z) info
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) -> @Corelib.Init.Logic.or (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) pp 0%Z)
    (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned 64%N plen) 0%Z) (@Corelib.Init.Logic.eq
    (@stdpp.bitvector.definitions.bv 64%N) ptag (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z)))) (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le BUF pp)
    (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add pp (@stdpp.bitvector.definitions.bv_unsigned 64%N plen)) E2)) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p E2) -> @Stdlib.ZArith.BinInt.Z.le E2 END -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N info);
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N C)] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z)
    [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat j0] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-104)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 idw] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-100)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 agw] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-96)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ptag;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ppad; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 plen; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N pp)] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-72)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 lnw] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-64)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat oj; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 alen] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-48)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le BUF p0) (@Stdlib.ZArith.BinInt.Z.le p0 END) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT))
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add
    (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) (@stdpp.bitvector.definitions.Z_to_bv 64%N PP) ta x11
    x12 x13 x14 x15 x16 x17 (@stdpp.bitvector.definitions.Z_to_bv 64%N E2) (@stdpp.bitvector.definitions.Z_to_bv 64%N p0) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x29440%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX KP BRC APC EI PARD HPP PB E2B HPKA F0 FID FALG FPAR FLEN FOID FR ST P00.
    dpose pa_basics' as (ACP & BAC & BIM & PPD & PKD & SLO').
    dpose CX as (HH & HT & MF & MI & SOK & SIP & SUB & PX). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    dpose BRC as (C0 & C16 & _ & CAC & CIM). pose proof alloc_ceiling_lt as ACLT.
    pose proof (bv_unsigned_in_range 64 plen) as PLR. change (bv_modulus 64) with (2^64) in PLR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KA; zify_cond KA.
    { (* [comment removed for export] *)
      zstep. zstep. zstep.
      eapply init_fail_walk; [exact CX| exact KP| exact BRC| exact APC| exact EI| clear; lia| exact HPP| clear -PB E2B; lia| exact HPKA
        | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR| exact ST]. }
    clear KA.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof (U_pk_use_ecparams_spec L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 HL) as SEP. unfold pk_use_ecparams_stmt, pk_use_ecparams_post, U_PK_USE_ECPARAMS in SEP.
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
      assert (XF : Forall (fun iv => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C, C + ECP_GROUP_SIZE); (U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)]).
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
                 - unfold ECP_GROUP_SIZE, U_ECP_IDS_DONE, U_ECP_IDS. split; [clear -CIM M1 M2 E1' E2''; lia| split; [clear; lia| split; [clear; lia| exact I]]]. }
        split; [intros b Hb; apply (proj2 (LEQ b)); right; right; exact Hb|].
        eapply heap_presx_trans; [exact PX|]. eapply heap_presx_weak''; [exact PX2| intros b Hb; right; exact Hb| clear; lia|].
        intros a Hc Ho. cbn in Ho |- *. unfold ECP_GROUP_SIZE. split; [| clear -Ho; tauto]. intros Ha. exact (fresh_not_client' C 256 a BRC APC ltac:(clear -Ha; lia) Hc). }
      eapply ec_fin_walk with (NB := NB) (g := g');
        [ exact CX2 | exact KP2 | apply (proj2 (LEQ _)); right; left; reflexivity | exact BRC | exact APC | exact EI | exact AP2 | exact GB2 | exact LEQ | exact NEWNB
        | intros Z0; destruct RES as [(id & IDB & GL)|(NZ & _)]; [exists id; subst; exact (conj IDB GL)| exfalso; exact (NZ Z0)]
        | exact RR2 | exact HPP | exact PB | exact E2B | exact HPKA2
        | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR | exact ST2 | exact P00 ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. zstep. if_cases KP8; zify_cond KP8.
      1-2: try (exfalso; clear -KP8 SPA SPR SLO' HLS ACL ACP; rewrite ?unsigned_lit in KP8 by lia; rewrite ?land_7_mod in KP8; lia).
      zstep. zstep. if_cases KT; zify_cond KT.
      { zstep. zstep. zstep. zstep. zstep. if_cases KZ1; zify_cond KZ1.
        2:{ exfalso. clear -KZ1. first [ discriminate | lia | (vm_compute in KZ1; discriminate) ]. }
        eapply init_fail_walk; [exact CX| exact KP| exact BRC| exact APC| exact EI| clear; lia| exact HPP| clear -PB E2B; lia| exact HPKA
          | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR| exact ST]. }
      zstep. zstep. if_cases KL; zify_cond KL.
      2:{ zstep. zstep. zstep. zstep. zstep. if_cases KZ2; zify_cond KZ2.
        2:{ exfalso. clear -KZ2. first [ discriminate | lia | (vm_compute in KZ2; discriminate) ]. }
        eapply init_fail_walk; [exact CX| exact KP| exact BRC| exact APC| exact EI| clear; lia| exact HPP| clear -PB E2B; lia| exact HPKA
          | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR| exact ST]. }
      (* [comment removed for export] *)
      pose proof (bv_unsigned_in_range 64 (sx32 idw)) as UR. change (bv_modulus 64) with (2^64) in UR.
      pose proof (land_m5_9 _ UR KR) as U913. set (u := bv_unsigned (sx32 idw)) in *.
      assert (IDB : 0 <= u < 2^31) by (clear -U913; lia).
      pose proof (U_pk_ecc_set_group_spec L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0) as SSG. unfold pk_ecc_set_group_stmt, pk_ecc_set_group_post, U_PK_ECC_SET_GROUP in SSG.
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
                 - apply (ecp_ids_state_presx usegs L _ _ _ _ _ m m2 IDS PX2 HL); cbn; clear -CIM I1 I2 I3 E1' E2''; (split; [lia| exact I]).
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
        | exact (low_frame_merge _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN FOID) | exact FR | exact ST2 | exact P00 ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.
