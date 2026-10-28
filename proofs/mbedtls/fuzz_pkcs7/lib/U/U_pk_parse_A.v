(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_parse_A () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.NoDup"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.U.U_pk_sinv.pk_sinv_P"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "PA.pctx"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.USpec.RepPk.pk_rep_c"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_RSA_INFO"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_EC_INFOS"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "RocqVerifyHarness.AgentSubmission.USpec.RepPk.PKC_inst"; "RocqVerifyHarness.AgentSubmission.U.U_pk_sinv.U_pk_sinv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Logic.iff"].


Definition U_PK_PARSE_SUBPUBKEY : Z := 0x292a8.
Definition MBEDTLS_ERR_PK_INVALID_PUBKEY : Z := -0x3B00.
Definition MBEDTLS_ERR_PK_INVALID_ALG : Z := -0x3A80.
Definition MBEDTLS_ERR_PK_UNKNOWN_PK_ALG : Z := -0x3C80.

(* [comment removed for export] *)
Lemma list_nil_of_empty {A} (l : list A) : (forall x, In x l -> False) -> l = [].
Proof. destruct l as [|x r]; [reflexivity|]. intros H. exfalso. apply (H x). left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nodup_fst_of_sub : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "Pl,(0.$1.)PLB2,(0.$1.)P,(2.$3.(4.(5.$3.$3.)$3.(6.$3.$3.)R1.))P,Pb,$1.P,(7.$1.R1.R4.)(7.$1.R2.R4.)P,(2.$1.R4.)(2.$3.(4.(5.$3.$3.)$3.(6.$3.$3.)R5.))")
(* [comment removed for export] *).
Proof.
  intros l LB2 ND SUB NDl. induction l as [|[a k] l IH]; [constructor|]. cbn. inversion NDl as [|? ? NI NDl']; subst. constructor.
  - intros Hin. apply in_map_iff in Hin. ddestruct Hin as ([a' k'] & E & Hin). cbn in E. subst a'.
    pose proof (nodup_fst_same LB2 a k k' ND (SUB _ ltac:(left; reflexivity)) (SUB _ ltac:(right; exact Hin))) as ->. exact (NI Hin).
  - apply IH; [intros b Hb; apply SUB; right; exact Hb| exact NDl'].
Qed.

Notation MT := U_MT (only parsing).

Lemma pk_lxor_sb : forall x, 0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 i) as [<-|]; [| apply andb_false_r].
  rewrite andb_true_r. rewrite <- (Z.mod_small x (2^63)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.
Ltac pk_ltb_fix H tac :=
  repeat match type of H with context [?x <? ?y] =>
    first [ replace (x <? y) with true in H by (symmetry; apply Z.ltb_lt; tac)
          | replace (x <? y) with false in H by (symmetry; apply Z.ltb_ge; tac) ] end.
Ltac pk_ckb K tac := if_cases K;
  [ exfalso; rewrite ?Z.lxor_0_l in K; try (rewrite pk_lxor_sb in K by tac); (pk_ltb_fix K tac); cbn [Z.b2z] in K; vm_compute in K; discriminate
  | clear K ].

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
  Hypothesis HPERM : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "Ph,(8.$9.VL,VHI,)PLB,(0.$1.)PLB',(0.$1.)Pm,P,(:.&40.)(;.(:.&8.))Pmo,$<.P,(=.$9.VL,VHI,R5.R4.R2.R1.)P,(>.$1.R5.R4.)(?.(8.$9.VL,VHI,)Lh',(8.$9.VL,VHI,)(10.(=.$9.VL,VHI,R1.R6.R5.R4.)(11.$3.(12.$9.VL,VHI,R1.)(12.$9.VL,VHI,R8.))))")
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
  Hypothesis HPRB : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "(13.$9.VL,VHI,$14.$15.$16.+5<?:8.$17.)")
(* [comment removed for export] *).
  Hypothesis HCPK : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "(18.$9.VL,VHI,$14.$19.$16.+5<?:8.$1:.$1;.)")
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

  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.
  #[using="HL"] Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 HL). Qed.
  #[using="L HL"] Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 HL)). Qed.
  #[using="HL"] Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 HL))). Qed.
  #[using="HMC"] Lemma ML1 : hl_data_lo L <= U_MUL_COUNT. Proof. exact (proj1 HMC). Qed.
  #[using="HMC"] Lemma ML2 : U_MUL_COUNT + 8 <= hl_data_hi L. Proof. exact (proj1 (proj2 HMC)). Qed.

  (* [comment removed for export] *)
  #[using="HI HLS m0 mo0 h0 LB HH0 INB SPP SPK ACL SLO DHI"] Lemma pa_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "(10.(1<.+1000.(1=.VL,))(10.(1>.(1?.VBUF,(20.(21.(:.&8.)Vbs,)))(1=.VL,))(10.(22.(1>.(1?.VBUF,(20.(21.(:.&8.)Vbs,)))(23.VL,))(1>.(24.VL,)VBUF,))(10.(22.(1>.(1?.VPP,+8.)(25.VL,))(1>.(26.VL,)VPP,))(10.(22.(1>.(1?.VPKA,+10.)(25.VL,))(1>.(26.VL,)VPKA,))(1>.(1?.(1?.Vlo,+7530.)(27.VL,))(28.&40.Vsp,)))))))")
(* [comment removed for export] *).
  Proof.
    pose proof alloc_ceiling_pos as ACP. destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC & BIM). cbn in BAC, BIM.
    pose proof SLO as SLO'. unfold PK_PARSE_STACK in SLO'.
    refine (conj ACP (conj BAC (conj BIM _))). clear -SPP SPK ACL SLO' HLS DHI. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition pctx (h : HST usegs L HI) (LBc : list blk) (m : mem) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "(10.(=.$9.VL,VHI,O4.O3.O2.O1.)(10.(11.$3.(12.$9.VL,VHI,O4.)(12.$9.VL,VHI,Vh0,))(10.(29.Vmo0,O1.)(10.(2:.$9.O2.)(10.(2;.$9.VL,O2.)(10.(2<.O2.)(10.Pb,$1.P,(7.$1.R1.VLB,)(7.$1.R2.O3.)(2=.$9.VL,VLB,(28.&40.Vsp,)(2>.(5.$3.$3.)(2?.(5.$3.$3.)(30.$3.$3.VPP,(1?.VPP,+8.))(2?.(5.$3.$3.)(30.$3.$3.VPKA,(1?.VPKA,+10.))(31.(5.$3.$3.))))(2?.(5.$3.$3.)(30.$3.$3.$32.(1?.$32.+1.))(2?.(5.$3.$3.)(30.$3.$3.+5<?:8.(1?.+5<?:8.+8.))(2?.(5.$3.$3.)(30.$3.$3.$33.(1?.$33.+38.))(31.(5.$3.$3.))))))Vm0,O2.))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="HLS HL HMC BUF bs HH0 INB SPP SPK ACL SLO HTOP DHI CWPP CWP"] Lemma pctx_munch : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "Ph,(8.$9.VL,VHI,)PLBc,(0.$1.)Pm,P,(:.&40.)(;.(:.&8.))Pm',P,(:.&40.)(;.(:.&8.))Pmo,$<.PW,(0.$34.)P,(35.R6.R5.R4.R2.)P,(36.R2.R5.R4.)P,(37.$9.R6.R5.)P,(2:.$9.R6.)P,(38.(5.$3.$3.)Liv,(5.$3.$3.)(22.(10.(1>.Vlo,(6.$3.$3.R1.))(1>.(39.$3.$3.R1.)(28.&40.Vsp,)))(22.(11.(5.$3.$3.)R1.(30.$3.$3.VPP,(1?.VPP,+8.)))(11.(5.$3.$3.)R1.(30.$3.$3.VPKA,(1?.VPKA,+10.)))))R5.)(35.R;.R:.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    (intros h LBc m m' mo W dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & IDS & SUB & PX); intros MU WM MI' HW).
    dpose pa_basics as (ACP & BAC & BIM & PPD & PKD & SLO').
    assert (HWa : forall a, ~ outside W a -> (lo <= a < bv_unsigned sp) \/ (PP <= a < PP + 8) \/ (PKA <= a < PKA + 16)).
    { clear -HW. intros a Ha. revert HW Ha. induction W as [|[u v] W IH]; intros HW Ha; [exfalso; apply Ha; exact I|].
      inversion HW as [|? ? Q1 Q2]; subst. cbn in Ha.
      destruct (Z_le_dec u a) as [GE|LT]; [destruct (Z_lt_dec a v) as [LT2|GE2]|].
      - cbn in Q1. destruct Q1 as [Q1|[Q1|Q1]]; [left; clear -Q1 GE LT2; lia| right; left| right; right];
          injection Q1; intros; subst; clear -GE LT2; lia.
      - apply IH; [exact Q2|]. intros Ho. apply Ha. split; [clear -GE2; lia| exact Ho].
      - apply IH; [exact Q2|]. intros Ho. apply Ha. split; [clear -LT; lia| exact Ho]. }
    assert (DJ : forall a n, hl_data_lo L <= a -> a + n <= hl_data_hi L -> disjoint_from W a n).
    { intros a n H1 H2. clear -HW PPD PKD DHI ACL H1 H2. induction W as [|[u v] W IH]; [exact I|]. inversion HW as [|? ? Q1 Q2]; subst. cbn. split; [| apply IH; exact Q2].
      cbn in Q1. destruct Q1 as [Q1|[Q1|Q1]]; [left; clear -Q1 H2 DHI ACL; lia| | ]; injection Q1; intros; subst; [clear -PPD H1 H2; lia| clear -PKD H1 H2; lia]. }
    split. { apply (Asn1AuxA.HEAP_munch usegs L HI h LBc m m' mo lo _ HH ACL MU WM).
             intros a Ha NO. destruct (HWa a NO) as [Q|[Q|Q]].
             - left. rewrite HT. clear -Q SLO' HLS HTOP. lia.
             - destruct (CWPP a ltac:(clear -Q; lia)) as [X|[X|X]]; [left; rewrite HT; exact X| right; left; exact X| right; right].
               ddestruct X as (b & Hb & Hr). exists b. split; [apply SUB; exact Hb| exact Hr].
             - destruct (CWP a ltac:(clear -Q; lia)) as [X|[X|X]]; [left; rewrite HT; exact X| right; left; exact X| right; right].
               ddestruct X as (b & Hb & Hr). exists b. split; [apply SUB; exact Hb| exact Hr]. }
    split; [exact HT|]. split; [exact MF|]. split; [exact MI'|].
    split. { eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW.
             destruct (outside_dec W a) as [Ho|No]; [exact Ho|]. exfalso. destruct (HWa a No) as [Q|[Q|Q]]; [clear -Q Ha DHI ACL; lia| clear -Q Ha PPD; lia| clear -Q Ha PKD; lia]. }
    split. { pose proof IL1 as I1. pose proof IL2 as I2. pose proof IL3 as I3. pose proof ML1 as M1. pose proof ML2 as M2. destruct IDS as [IDS [cnt RC]]. split.
             - eapply ecp_ids_state_munch; [exact IDS| exact MU| exact WM| |]; (apply DJ; clear -I1 I2 I3; lia).
             - exists cnt. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. apply DJ; clear -M1 M2; cbn; lia. }
    split; [exact SUB|].
    eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. destruct (outside_dec W a) as [Hw|Nw]; [exact Hw|]. exfalso. cbn in Ho.
    destruct (HWa a Nw) as [Q|[Q|Q]]; [| clear -Q Ho; lia| clear -Q Ho; lia].
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [clear -Hs Q; lia| clear -Hd1 Q DHI ACL; lia|].
    pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & Bc & _). destruct b as [Bb kk]; cbn in Hr, Bc. clear -Hr Bc Q ACL. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HLS BUF bs HH0 INB BP PE EB BUF0 SPP SPK DPK ACL SLO DHI DKB DPB NZPP NZP DSPP DSP DSB"] Lemma ret_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (LBc : @Corelib.Init.Datatypes.list (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (r : @Corelib.Numbers.BinNums.Z), forall (p' :
    @Corelib.Numbers.BinNums.Z), forall (info : @Corelib.Numbers.BinNums.Z), forall (ctx : @Corelib.Numbers.BinNums.Z), forall (owned : @Corelib.Init.Datatypes.list
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x8 : @stdpp.bitvector.definitions.bv 64%N), forall (x9 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x12 : @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x15 : @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x18 : @stdpp.bitvector.definitions.bv 64%N), forall (x19 : @stdpp.bitvector.definitions.bv 64%N), forall (x20 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N), @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HEAP
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI h (@Corelib.Init.Datatypes.app (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) m mo ->
    @Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.heap_top (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI h)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.heap_top (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI h0) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.mo_frame
    mo0 mo -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.mem_inv (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AStep.statics_ok
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L m -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.pk_sinv_P m -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Asn1Aux.heap_presx
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L LB (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (@Corelib.Init.Datatypes.app (@Corelib.Init.Datatypes.prod
    (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) [@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) PP (@Stdlib.ZArith.BinInt.Z.add
    PP 8%Z); @Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) PKA (@Stdlib.ZArith.BinInt.Z.add PKA 16%Z)] [@Corelib.Init.Datatypes.pair
    (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_grp_id_list.U_ECP_IDS_DONE) (@Stdlib.ZArith.BinInt.Z.add
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_grp_id_list.U_ECP_IDS_DONE) 1%Z); @Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) 380840%Z
    (@Stdlib.ZArith.BinInt.Z.add 380840%Z 8%Z); @Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_grp_id_list.U_ECP_IDS) (@Stdlib.ZArith.BinInt.Z.add (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_grp_id_list.U_ECP_IDS) 56%Z)]) m0 m ->
    @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt (@Stdlib.ZArith.BinInt.Z.opp (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.le r 0%Z) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N p')] -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le P p') (@Stdlib.ZArith.BinInt.Z.le p' END) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N info); @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N ctx)] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.pk_rep_c (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m (@Corelib.Init.Datatypes.app
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) PKA info ctx owned -> (@Corelib.Init.Logic.not (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) r 0%Z) ->
    @Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) info 0%Z) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) ctx 0%Z)
    (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)) owned []))) -> @Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)) LBc (@Corelib.Init.Datatypes.app (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat lj] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-48)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 x8 x9 (@stdpp.bitvector.definitions.Z_to_bv 64%N r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x29344%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros HH HT MF MI SOK IDS PX RR HPP PB HPKA REP RNZ -> FRL FR ST.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. dpose pa_basics as (ACP & BAC & BIM & PPD & PKD & SLO').
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FRL ST (bv_unsigned sp + -48). release_frame FR ST (bv_unsigned sp).
    zstep.
    apply aevtM_done. unfold pk_parse_subpubkey_post.
    deexists 15. dexists m, mo, h, r, p', info, ctx, owned.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [exact MI|]. split; [exact SOK|]. split; [exact IDS|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|].
    split; [exact HPP|]. split; [exact PB|]. split; [exact HPKA|]. split; [exact REP|]. split; [exact RNZ|]. split; [exact HH| exact PX].
  Qed.

  (* [comment removed for export] *)
  #[using="HLS BUF bs HH0 INB BP PE EB BUF0 SPP SPK DPK ACL SLO DHI DKB DPB NZPP NZP DSPP DSP DSB"] Lemma early_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (r : @Corelib.Numbers.BinNums.Z), forall (p' : @Corelib.Numbers.BinNums.Z), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x8 : @stdpp.bitvector.definitions.bv 64%N), forall (x9 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x12 : @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x15 : @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x18 : @stdpp.bitvector.definitions.bv 64%N), forall (x19 : @stdpp.bitvector.definitions.bv 64%N), forall (x20 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N), @PA.pctx h LB m mo -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt
    (@Stdlib.ZArith.BinInt.Z.opp (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.lt r 0%Z) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N p')] -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le P p') (@Stdlib.ZArith.BinInt.Z.le p' END) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    PKA [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z); @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z)] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
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
    (-112)%Z)) gp tp x5 x6 x7 x8 x9 (@stdpp.bitvector.definitions.Z_to_bv 64%N r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x29344%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros until x31. (intros dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & IDS & SUB & PX); intros RR HPP PB HPKA FRL FR ST).
    eapply ret_walk with (owned := []) (info := 0) (ctx := 0); try eassumption.
    - clear -RR. lia.
    - apply pk_rep_c_null.
    - intros _. repeat split; reflexivity.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="HFREE HLS SW DIMG HND HPERM CA_MSF CA_RSA80 CA_EC80 BUF bs HH0 INB BP PE EB BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP SPR"] Lemma fail_free_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (LBc : @Corelib.Init.Datatypes.list (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (r : @Corelib.Numbers.BinNums.Z), forall (p' :
    @Corelib.Numbers.BinNums.Z), forall (info : @Corelib.Numbers.BinNums.Z), forall (ctx : @Corelib.Numbers.BinNums.Z), forall (owned : @Corelib.Init.Datatypes.list
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x9 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 : @stdpp.bitvector.definitions.bv 64%N), forall (x12 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 : @stdpp.bitvector.definitions.bv 64%N), forall (x15 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 : @stdpp.bitvector.definitions.bv 64%N), forall (x18 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x19 : @stdpp.bitvector.definitions.bv 64%N), forall (x20 : @stdpp.bitvector.definitions.bv 64%N), forall (x28 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 : @stdpp.bitvector.definitions.bv 64%N), forall (x31 :
    @stdpp.bitvector.definitions.bv 64%N), @PA.pctx h LBc m mo -> @Stdlib.Sorting.Permutation.Permutation (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) LBc
    (@Corelib.Init.Datatypes.app (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt (@Stdlib.ZArith.BinInt.Z.opp
    (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.lt r 0%Z) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N p')] -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le P p') (@Stdlib.ZArith.BinInt.Z.le p' END) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    PKA [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N info); @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N ctx)] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.pk_rep_c (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m
    (@Corelib.Init.Datatypes.app (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) PKA info ctx owned -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z)
    [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat lj] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-48)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
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
    intros until x31. (intros dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & IDS & SUB & PX); intros PERM RR HPP PB HPKA REP FRL FR ST).
    dpose pa_basics as (ACP & BAC & BIM & PPD & PKD & SLO').
    destruct (HPERM _ _ _ _ _ HH PERM) as (h1 & HH1 & HT1).
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    zstep. zstep. zstep.
    pose proof (U_pk_free_spec L HI U_MT HFREE HLS SW DIMG HND CA_MSF CA_RSA80 CA_EC80) as SPF. unfold pk_free_c_stmt, pk_free_c_post, U_PK_FREE in SPF.
    eapply aevtM_cut.
    { eapply SPF with (lo := lo) (h := h1) (LBo := owned) (LB := LB) (owned := owned);
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by (clear -SLO' HLS ACL ACP SPR; lia);
        first [ exact HH1 | exact HPKA | exact REP | exact ALP | exact ST | exact MI | exact SOK | exact TP | exact ACL | exact DHI | reflexivity
              | intros b Hb; exact Hb
              | rewrite HT1, HT; clear -SPK PKT HTOP SLO' HLS; lia
              | clear -SPK SPA SPR SLO' HLS; lia
              | match goal with |- ?g => idtac "PFLEFT" g end ]. }
    clear SPF.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by (clear -SLO' HLS ACL ACP SPR; lia).
    ddestruct PO as (MI2 & SOK2 & ST2 & MF2 & HT2 & HH2 & SUBo & KEEP & HPKA2 & PX2 & NIN).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HH2 with HEAP _ _ _ ?hh (?lbo ++ _) _ _ => rename hh into h2; rename lbo into LBo' end.
    assert (E0 : LBo' = []).
    { apply list_nil_of_empty. intros b Hb. apply (NIN b Hb). apply in_map. exact (SUBo b Hb). }
    subst LBo'. cbn [app] in HH2, PX2.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. clear MK.
    (* [comment removed for export] *)
    assert (TR : forall A cs, rw_cells usegs m A cs -> bv_unsigned sp + -112 <= A -> A + Z.of_nat (cells_size cs) <= bv_unsigned sp -> rw_cells usegs m2 A cs).
    { intros A cs Hc B1 B2. eapply heap_presx_rw_cells; [exact PX2| exact Hc| intros a Ha; left; clear -Ha B1; lia| cbn; split; [clear -B2 SPK; lia| exact I]]. }
    apply TR in FRL; [| clear; lia| cbn; clear; lia]. apply TR in FR; [| clear; lia| cbn; clear; lia]. clear TR.
    assert (HPP2 : rw_cells usegs m2 PP [C8 (Z_to_bv 64 p')]).
    { eapply heap_presx_rw_cells; [exact PX2| exact HPP| |]; cbn [cells_size csize Nat.add disjoint_from].
      - intros a Ha. destruct (CWPP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSPP Ha; lia| right; left; exact Q| right; right; exact Q].
      - split; [clear -DPK; lia| exact I]. }
    zstep. zstep.
    eapply ret_walk with (owned := []) (info := 0) (ctx := 0) (h := h2); try eassumption.
    - rewrite HT2, HT1. exact HT.
    - eapply mo_frame_trans; [exact MF| exact MF2].
    - pose proof IL1 as I1; pose proof IL2 as I2; pose proof IL3 as I3. pose proof ML1 as M1; pose proof ML2 as M2. destruct IDS as [IDS [cnt RC]]. split.
      + apply (ecp_ids_state_presx usegs L _ _ _ _ _ m m2 IDS PX2 HL); cbn; clear -PKD I1 I2 I3; (split; [lia| exact I]).
      + exists cnt. eapply heap_presx_rw_cells; [exact PX2| exact RC| |]; cbn [cells_size csize Nat.add disjoint_from].
        * intros a Ha. right; left. split; [clear -Ha M1 M2; lia| exact (proj2 (proj2 (proj2 HMC) a Ha))].
        * split; [clear -PKD M1 M2; lia| exact I].
    - eapply heap_presx_trans; [exact PX|]. eapply heap_presx_weak; [exact PX2| intros b Hb; exact Hb| clear; lia|].
      intros a Ha. cbn [outside app] in Ha |- *. clear -Ha. tauto.
    - clear -RR. lia.
    - apply pk_rep_c_null.
    - intros _. repeat split; reflexivity.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="HLS DIMG HL HMC lo HH0 HBS0 INB SPP SPK ACL SLO DHI DKB DPB CRB"] Lemma pctx_bytes : forall h LBc m mo, pctx h LBc m mo -> bytes_at usegs m BUF bs.
  Proof.
    (intros h LBc m mo dd_H; ddestruct dd_H as (_ & _ & _ & _ & _ & _ & _ & PX)). dpose pa_basics as (ACP & BAC & BIM & PPD & PKD & SLO').
    eapply heap_presx_bytes_at; [exact PX| exact HBS0| |].
    - intros a Ha. destruct (CRB a Ha) as [Q|[Q|Q]]; [exfalso; clear -Q Ha BAC ACL; lia| right; left; exact Q| right; right; exact Q].
    - cbn. pose proof IL1 as I1. pose proof IL2 as I2. pose proof IL3 as I3. pose proof ML1 as M1. pose proof ML2 as M2. pose proof DI1 as E1. pose proof DI2 as E2.
      clear -DKB DPB BIM I1 I2 I3 M1 M2 E1 E2. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma keep_frame : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "PLB1,(0.$1.)PSP,$3.PX,(0.$34.)Pm,P,(:.&40.)(;.(:.&8.))Pm',P,(:.&40.)(;.(:.&8.))PA,$3.Pcs,(0.$3=.)P,(2=.$9.VL,R7.R6.R5.R4.R3.)P,(1>.R7.(1?.(28.&40.Vsp,)-70.))P,(3<.$9.R6.R4.R3.)P,(1>.(1?.(28.&40.Vsp,)-70.)R5.)P,(1>.(1?.R6.(20.(4>.R5.)))(28.&40.Vsp,))P,(38.(5.$3.$3.)Liv,(5.$3.$3.)(22.(1>.(39.$3.$3.R1.)(1?.(28.&40.Vsp,)-70.))(1>.(28.&40.Vsp,)(6.$3.$3.R1.)))R:.)(3<.$9.R9.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    intros LB1 SP X m m' A cs PX HSP Hc B1 B2 HX. eapply heap_presx_rw_cells; [exact PX| exact Hc| intros a Ha; left; clear -Ha B1 HSP; lia|].
    clear -HX B1 B2. induction X as [|[u v] X IH]; [exact I|]. inversion HX as [|? ? Q1 Q2]; subst. cbn in Q1 |- *. split; [lia| apply IH; exact Q2].
  Qed.
  #[using="HI h0 lo DSPP CWPP"] Lemma keep_pp : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "PLB1,(0.$1.)PSP,$3.PX,(0.$34.)Pm,P,(:.&40.)(;.(:.&8.))Pm',P,(:.&40.)(;.(:.&8.))Pcs,(0.$3=.)P,(2=.$9.VL,R6.R5.R4.R3.R2.)P,Pb,$1.P,(7.$1.R1.VLB,)(7.$1.R2.R9.)P,(1>.R7.(28.&40.Vsp,))P,(3<.$9.R6.VPP,R4.)P,(11.$4?.(4>.R5.)#8.)P,(50.R9.VPP,+8.)(3<.$9.R8.VPP,R7.)")
(* [comment removed for export] *).
  Proof.
    intros LB1 SP X m m' cs PX SUB HSP Hc SZ DX. eapply heap_presx_rw_cells; [exact PX| exact Hc| rewrite SZ| rewrite SZ; exact DX].
    intros a Ha. destruct (CWPP a Ha) as [Q|[Q|(b & Hb & Hr)]]; [left; clear -Q DSPP Ha HSP; lia| right; left; exact Q| right; right; exists b; split; [apply SUB; exact Hb| exact Hr]].
  Qed.
  #[using="HI h0 lo DSP CWP"] Lemma keep_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "PLB1,(0.$1.)PSP,$3.PX,(0.$34.)Pm,P,(:.&40.)(;.(:.&8.))Pm',P,(:.&40.)(;.(:.&8.))Pcs,(0.$3=.)P,(2=.$9.VL,R6.R5.R4.R3.R2.)P,Pb,$1.P,(7.$1.R1.VLB,)(7.$1.R2.R9.)P,(1>.R7.(28.&40.Vsp,))P,(3<.$9.R6.VPKA,R4.)P,(11.$4?.(4>.R5.)#10.)P,(50.R9.VPKA,+10.)(3<.$9.R8.VPKA,R7.)")
(* [comment removed for export] *).
  Proof.
    intros LB1 SP X m m' cs PX SUB HSP Hc SZ DX. eapply heap_presx_rw_cells; [exact PX| exact Hc| rewrite SZ| rewrite SZ; exact DX].
    intros a Ha. destruct (CWP a Ha) as [Q|[Q|(b & Hb & Hr)]]; [left; clear -Q DSP Ha HSP; lia| right; left; exact Q| right; right; exists b; split; [apply SUB; exact Hb| exact Hr]].
  Qed.

  (* [comment removed for export] *)
  #[using="HI HLS DIMG m0 mo0 h0 PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI"] Lemma fresh_not_client : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "PC,$3.Pn,$3.Pa,$3.P,(51.VL,R3.R2.)P,PB,$3.Pk,$3.P,(7.(5.$3.$3.)(30.$3.$3.R2.R1.)VLB,)(22.(1>.(1?.R7.R6.)R3.)(1>.(1?.R3.R2.)R7.))P,(10.(1>.R5.R3.)(1<.R3.(1?.R5.R4.)))(43.(52.VL,VLB,(28.&40.Vsp,)R4.))")
(* [comment removed for export] *).
  Proof.
    (intros C n a dd_H; ddestruct dd_H as (_ & _ & _ & CAC & CIM); intros AP Ha [Hs|[[Hd _]|((B & k) & Hb & Hr)]]).
    - dpose pa_basics as (_ & _ & _ & _ & _ & SLO'). clear -Hs Ha CAC ACL SLO' HLS. lia.
    - pose proof DI1 as E1. pose proof DI2 as E2. clear -Hd Ha CIM E1 E2. lia.
    - cbn in Hr. destruct (AP B k Hb); clear -Ha Hr H; lia.
  Qed.
  (* [comment removed for export] *)
  #[using="ra PP P END BUF PKA bs BP PE EB DPK DKB DPB NZPP NZP"] Lemma heap_presx_weak' : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "PL1,(0.$1.)PSP1,$3.PX1,(0.$34.)PX,(0.$34.)Pm,P,(:.&40.)(;.(:.&8.))Pm',P,(:.&40.)(;.(:.&8.))P,(2=.$9.VL,R6.R5.R4.R2.R1.)P,Pb,$1.P,(7.$1.R1.VLB,)(7.$1.R2.R9.)P,(1>.R7.(28.&40.Vsp,))P,Pa,$3.P,(52.VL,VLB,(28.&40.Vsp,)R1.)P,(53.R8.R2.)(53.R:.R3.)(2=.$9.VL,VLB,(28.&40.Vsp,)R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros L1 SP1 X1 X m m' HP HS HSP HX a Ha Hc Ho.
    apply HP; [exact Ha| | apply HX; [exact Hc| exact Ho]].
    destruct Hc as [Hs|[Hd|(b & Hb & Hr)]]; [left; lia| right; left; exact Hd| right; right; exists b; split; [apply HS; exact Hb| exact Hr]].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma perm_of_sets : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "Pl1,(0.$1.)Pl2,(0.$1.)P,(2.$3.(4.(5.$3.$3.)$3.(6.$3.$3.)R2.))P,(2.$3.(4.(5.$3.$3.)$3.(6.$3.$3.)R2.))P,Pb,$1.(54.(7.$1.R1.R5.)(7.$1.R1.R4.))(>.$1.R5.R4.)")
(* [comment removed for export] *).
  Proof. intros l1 l2 N1 N2 E. apply NoDup_Permutation; [apply (NoDup_map_inv fst); exact N1| apply (NoDup_map_inv fst); exact N2| exact E]. Qed.

  (* [comment removed for export] *)
  #[using="HI HLS DIMG sp m0 mo0 h0 BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI CWPP"] Lemma fresh_apart_pp : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "PC,$3.Pn,$3.P,(51.VL,R2.R1.)P,PB,$3.Pk,$3.P,(7.(5.$3.$3.)(30.$3.$3.R2.R1.)VLB,)(22.(1>.(1?.R6.R5.)R3.)(1>.(1?.R3.R2.)R6.))P,(1<.=R3.)(22.(1>.(1?.VPP,+8.)R5.)(1>.(1?.R5.R4.)VPP,))")
(* [comment removed for export] *).
  Proof.
    (intros C n dd_H; ddestruct dd_H as (_ & _ & _ & CAC & CIM); intros AP Hn). dpose pa_basics as (_ & _ & _ & _ & _ & SLO'). pose proof DI1 as E1. pose proof DI2 as E2.
    destruct (Z_le_dec (PP + 8) C) as [Y|N1]; [left; exact Y|]. destruct (Z_le_dec (C + n) PP) as [Y|N2]; [right; exact Y|]. exfalso.
    destruct (CWPP (Z.max PP C) ltac:(clear -N1 N2; lia)) as [Hs|[[Hd _]|((B & k) & Hb & Hr)]].
    - clear -Hs N1 N2 CAC ACL Hn. lia.
    - clear -Hd N1 N2 CIM E1 E2 Hn. lia.
    - cbn in Hr. destruct (AP B k Hb); clear -N1 N2 Hr H Hn; lia.
  Qed.
  #[using="HI HLS DIMG sp m0 mo0 h0 PP BUF lo bs HH0 INB SPP SPK ACL SLO DHI CWP"] Lemma fresh_apart_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "PC,$3.Pn,$3.P,(51.VL,R2.R1.)P,PB,$3.Pk,$3.P,(7.(5.$3.$3.)(30.$3.$3.R2.R1.)VLB,)(22.(1>.(1?.R6.R5.)R3.)(1>.(1?.R3.R2.)R6.))P,(1<.=R3.)(22.(1>.(1?.VPKA,+10.)R5.)(1>.(1?.R5.R4.)VPKA,))")
(* [comment removed for export] *).
  Proof.
    (intros C n dd_H; ddestruct dd_H as (_ & _ & _ & CAC & CIM); intros AP Hn). dpose pa_basics as (_ & _ & _ & _ & _ & SLO'). pose proof DI1 as E1. pose proof DI2 as E2.
    destruct (Z_le_dec (PKA + 16) C) as [Y|N1]; [left; exact Y|]. destruct (Z_le_dec (C + n) PKA) as [Y|N2]; [right; exact Y|]. exfalso.
    destruct (CWP (Z.max PKA C) ltac:(clear -N1 N2; lia)) as [Hs|[[Hd _]|((B & k) & Hb & Hr)]].
    - clear -Hs N1 N2 CAC ACL Hn. lia.
    - clear -Hd N1 N2 CIM E1 E2 Hn. lia.
    - cbn in Hr. destruct (AP B k Hb); clear -N1 N2 Hr H Hn; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="DIMG h0 lo ACL CWPP"] Lemma blk_apart_pp : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_A ()) "Phx,(8.$9.VL,VHI,)PLBx,(0.$1.)Pmx,P,(:.&40.)(;.(:.&8.))Pmox,$<.PB,$3.Pk,$3.P,(=.$9.VL,VHI,R6.R5.R4.R3.)P,Pb,$1.P,(7.$1.R1.VLB,)(7.$1.R2.R8.)P,(7.(5.$3.$3.)(30.$3.$3.R4.R3.)R7.)P,(43.(7.(5.$3.$3.)(30.$3.$3.R5.R4.)VLB,))P,(1<.=R5.)(22.(1>.(1?.VPP,+8.)R7.)(1>.(1?.R7.R6.)VPP,))")
(* [comment removed for export] *).
  Proof.
    intros hx LBx mx mox B k HH SUB IN NIN Hk. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (_ & _ & _ & CAC & CIM). cbn in CAC, CIM. pose proof DI1 as E1. pose proof DI2 as E2.
    destruct (Z_le_dec (PP + 8) B) as [Y|N1]; [left; exact Y|]. destruct (Z_le_dec (B + k) PP) as [Y|N2]; [right; exact Y|]. exfalso.
    destruct (CWPP (Z.max PP B) ltac:(clear -N1 N2 Hk; lia)) as [Hs|[[Hd _]|((B' & k') & Hb & Hr)]].
    - clear -Hs N1 N2 CAC ACL Hk. lia.
    - clear -Hd N1 N2 CIM E1 E2 Hk. lia.
    - cbn in Hr. assert (NE : (B', k') <> (B, k)) by (intros E; rewrite E in Hb; exact (NIN Hb)).
      pose proof (blocks_apart_neq LBx _ _ HAP (SUB _ Hb) IN NE ltac:(cbn; clear -Hr; lia) ltac:(cbn; exact Hk)) as AP. cbn [fst snd] in AP.
      clear -AP Hr N1 N2 Hk. lia.
  Qed.
End PA.
