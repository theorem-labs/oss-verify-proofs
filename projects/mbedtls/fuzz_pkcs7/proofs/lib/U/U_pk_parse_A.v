(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_parse_A () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Stdlib.Lists.List.NoDup"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.U.UImg.usegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "OSSVerify.KrLib.U.U_ecp_defs.U_MT"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "OSSVerify.KrLib.U.U_platform_zeroize.U_MEMSET_FUNC"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.U_BAD_POINTS"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.U.U_pk_sinv.pk_sinv_P"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "OSSVerify.KrLib.U.U_ecp_grp_id_list.U_ECP_IDS"; "OSSVerify.KrLib.Lib.Frame.ivl"; "PA.pctx"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.USpec.RepPk.pk_rep_c"; "OSSVerify.KrLib.U.U_pk_free.U_RSA_INFO"; "OSSVerify.KrLib.U.U_pk_free.U_EC_INFOS"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "OSSVerify.KrLib.USpec.RepPk.PKC_inst"; "OSSVerify.KrLib.U.U_pk_sinv.U_pk_sinv"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "OSSVerify.KrLib.Lib.HeapIface.client_addr"; "OSSVerify.KrLib.Lib.Frame.outside"; "Corelib.Init.Logic.iff"].


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
  intros x Rx.
  assert (Bit63 : Z.testbit x 63 = false).
  { apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity. }
  assert (NoOverlap : Z.land x 9223372036854775808 = 0).
  { apply Z.bits_inj'. intros k Kpos. rewrite Z.land_spec, Z.bits_0.
    change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 63 k) as [At63|Off63]; [subst k; rewrite Bit63; reflexivity| apply andb_false_r]. }
  symmetry. apply Z.add_nocarry_lxor. exact NoOverlap.
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
  Notation FRS mx := (rw_cells usegs mx (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
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
    intros h LBc m m' mo W Ctx Mu Wm MemOkNew Wfp.
    clear HFREE HCALLOC SW DIMG HND HPERM CA_MSF CA_RSA0 CA_RSA72 CA_RSA80 CA_EC0 CA_EC72 CA_EC80 CAT_ECGRP CAT_PKALG
      CAT_ECALGID CA_PKTBL CA_BP HPRB HCPK HPP0 ALPP HBS0 BP PE EB B63 BUF0 HPKA0 ALP PPT PKT DPK ST0 SPA MI0 SOK0 SIP0
      TP DKB DPB NZPP NZP DSPP DSP DSB CRB RA SPR.
    dpose pa_basics as (CeilBig & _ & _ & PPclear & PKAclear & Room).
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [BlkRange _].
    destruct Ctx as (Heap & TopEq & ModelFr & _ & StatOk & SinvOk & Grow & Kept).
    assert (Where : forall a, ~ outside W a ->
              (lo <= a < bv_unsigned sp) \/ (PP <= a < PP + 8) \/ (PKA <= a < PKA + 16)).
    { clear -Wfp. induction Wfp as [|[u v] W' Head Tail IH]; intros a Out; cbn [outside] in Out.
      - exfalso. exact (Out I).
      - destruct (Asn1AuxA.outside_dec W' a) as [Rest|Rest]; [|exact (IH a Rest)].
        assert (Inside : u <= a < v).
        { destruct (Z_le_gt_dec u a) as [Lo|Lo]; destruct (Z_lt_ge_dec a v) as [Hi|Hi];
            first [ lia | exfalso; apply Out; split; [lia| exact Rest] ]. }
        cbn [fst snd] in Head. destruct Head as [Stack|[E1|E2]].
        + left. lia.
        + injection E1 as -> ->. right. left. exact Inside.
        + injection E2 as -> ->. right. right. exact Inside. }
    assert (AboveCeil : forall a, ~ outside W a -> alloc_ceiling <= a).
    { intros a Out. destruct (Where a Out) as [Zone|[Zone|Zone]]; lia. }
    refine (conj _ (conj TopEq (conj ModelFr (conj MemOkNew (conj _ (conj _ (conj Grow _))))))).
    - apply (Asn1AuxA.HEAP_munch usegs L HI h LBc m m' mo lo W Heap ACL Mu Wm).
      pose proof (client_wrange_mono L LB LBc lo (heap_top usegs L HI h0) PP 8 CWPP Grow) as PPwr.
      pose proof (client_wrange_mono L LB LBc lo (heap_top usegs L HI h0) PKA 16 CWP Grow) as PKwr.
      intros a Ra Out. rewrite TopEq.
      destruct (Where a Out) as [Zone|[Zone|Zone]]; [left; lia| exact (PPwr a Zone)| exact (PKwr a Zone)].
    - apply (statics_ok_munch usegs L W m m' StatOk Mu).
      intros a [_ Dhi] _.
      destruct (Asn1AuxA.outside_dec W a) as [Fine|Hit]; [exact Fine|].
      pose proof (AboveCeil a Hit) as Up. exfalso. lia.
    - change (si_P (U_pk_sinv L HL HMC) m').
      apply (si_frame (U_pk_sinv L HL HMC) m m' SinvOk).
      intros a Ra Fp. destruct (si_data (U_pk_sinv L HL HMC) a Fp) as [[_ Dhi] _].
      apply Mu. rewrite (wa_unsigned a Ra).
      destruct (Asn1AuxA.outside_dec W a) as [Fine|Hit]; [exact Fine|].
      pose proof (AboveCeil a Hit) as Up. exfalso. lia.
    - apply (heap_presx_trans usegs L LB (bv_unsigned sp) FP m0 m m' Kept).
      apply (heap_presx_of_munch usegs L LB (bv_unsigned sp) FP W m m' Mu Wm).
      intros a Ra Ca Oa.
      destruct (Asn1AuxA.outside_dec W a) as [Fine|Hit]; [exact Fine|]. exfalso.
      cbn [outside app] in Oa. destruct Oa as (NotPP & NotPKA & _).
      destruct (Where a Hit) as [Zone|[Zone|Zone]]; [| exact (NotPP Zone)| exact (NotPKA Zone)].
      destruct Ca as [Up|[[[_ Dhi] _]|(b & Inb & Rb)]]; [lia| lia|].
      pose proof (proj1 (Forall_forall _ _) BlkRange b Inb) as (_ & _ & _ & BTop & _).
      lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HLS BUF bs HH0 INB BP PE EB BUF0 SPP SPK DPK ACL SLO DHI DKB DPB NZPP NZP DSPP DSP DSB"] Lemma ret_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (LBc : @Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (r : @Corelib.Numbers.BinNums.Z), forall (p' :
    @Corelib.Numbers.BinNums.Z), forall (info : @Corelib.Numbers.BinNums.Z), forall (ctx : @Corelib.Numbers.BinNums.Z), forall (owned : @Corelib.Init.Datatypes.list
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x8 : @stdpp.bitvector.definitions.bv 64%N), forall (x9 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x12 : @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x15 : @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x18 : @stdpp.bitvector.definitions.bv 64%N), forall (x19 : @stdpp.bitvector.definitions.bv 64%N), forall (x20 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N), @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HEAP
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI h (@Corelib.Init.Datatypes.app (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) m mo ->
    @Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.heap_top (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI h)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.heap_top (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI h0) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.mo_frame
    mo0 mo -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Mem.mem_inv (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AStep.statics_ok
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L m -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.pk_sinv_P m -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Asn1Aux.heap_presx
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L LB (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (@Corelib.Init.Datatypes.app (@Corelib.Init.Datatypes.prod
    (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) [@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) PP (@Stdlib.ZArith.BinInt.Z.add
    PP 8%Z); @Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) PKA (@Stdlib.ZArith.BinInt.Z.add PKA 16%Z)] [@Corelib.Init.Datatypes.pair
    (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_grp_id_list.U_ECP_IDS_DONE) (@Stdlib.ZArith.BinInt.Z.add
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_grp_id_list.U_ECP_IDS_DONE) 1%Z); @Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) 380840%Z
    (@Stdlib.ZArith.BinInt.Z.add 380840%Z 8%Z); @Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_grp_id_list.U_ECP_IDS) (@Stdlib.ZArith.BinInt.Z.add (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_grp_id_list.U_ECP_IDS) 56%Z)]) m0 m ->
    @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt (@Stdlib.ZArith.BinInt.Z.opp (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.le r 0%Z) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N p')] -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le P p') (@Stdlib.ZArith.BinInt.Z.le p' END) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N info); @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N ctx)] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.pk_rep_c (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m (@Corelib.Init.Datatypes.app
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) PKA info ctx owned -> (@Corelib.Init.Logic.not (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) r 0%Z) ->
    @Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) info 0%Z) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) ctx 0%Z)
    (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)) owned []))) -> @Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)) LBc (@Corelib.Init.Datatypes.app (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat lj] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-48)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 x8 x9 (@stdpp.bitvector.definitions.Z_to_bv 64%N r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x29344%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros m mo h LBc r p' info ctx owned lj x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
      Heap TopEq ModelFr MemOk StatOk SinvOk Kept RetRange PPCell PRange PKCell PkRep ErrZero LBcEq LocalBuf SavedRegs StackOk.
    assert (Room : lo + 30000 + hl_stack L <= bv_unsigned sp) by (unfold PK_PARSE_STACK in SLO; lia).
    assert (FrameStk : stk usegs m lo (bv_unsigned sp)).
    { pose proof (stk_release _ _ _ _ _ StackOk LocalBuf ltac:(lia)) as UpTo48.
      cbn [cells_size csize Nat.add] in UpTo48.
      replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in UpTo48 by lia.
      pose proof (stk_release _ _ _ _ _ UpTo48 SavedRegs ltac:(lia)) as Whole.
      cbn [cells_size csize Nat.add] in Whole.
      replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in Whole by lia.
      exact Whole. }
    pose proof (heap_mok _ _ HI _ _ _ _ Heap) as Mok.
    do 6 zstep. zstep. zstep.
    apply aevtM_done. unfold pk_parse_subpubkey_post.
    exists x5, x6, x7, (Z_to_bv 64 r), x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m, mo, h, r, p', info, ctx, owned.
    split; [reflexivity|].
    refine (conj eq_refl (conj RetRange (conj MemOk (conj StatOk (conj SinvOk (conj FrameStk (conj ModelFr (conj TopEq _)))))))).
    refine (conj PPCell (conj PRange (conj PKCell (conj PkRep (conj ErrZero (conj Heap Kept)))))).
  Qed.

  (* [comment removed for export] *)
  #[using="HLS BUF bs HH0 INB BP PE EB BUF0 SPP SPK DPK ACL SLO DHI DKB DPB NZPP NZP DSPP DSP DSB"] Lemma early_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (r : @Corelib.Numbers.BinNums.Z), forall (p' : @Corelib.Numbers.BinNums.Z), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x8 : @stdpp.bitvector.definitions.bv 64%N), forall (x9 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x12 : @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x15 : @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x18 : @stdpp.bitvector.definitions.bv 64%N), forall (x19 : @stdpp.bitvector.definitions.bv 64%N), forall (x20 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N), @PA.pctx h LB m mo -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt
    (@Stdlib.ZArith.BinInt.Z.opp (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.lt r 0%Z) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N p')] -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le P p') (@Stdlib.ZArith.BinInt.Z.le p' END) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    PKA [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z); @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z)] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
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
    (-112)%Z)) gp tp x5 x6 x7 x8 x9 (@stdpp.bitvector.definitions.Z_to_bv 64%N r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0x29344%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
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
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (LBc : @Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (r : @Corelib.Numbers.BinNums.Z), forall (p' :
    @Corelib.Numbers.BinNums.Z), forall (info : @Corelib.Numbers.BinNums.Z), forall (ctx : @Corelib.Numbers.BinNums.Z), forall (owned : @Corelib.Init.Datatypes.list
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk)), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x9 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 : @stdpp.bitvector.definitions.bv 64%N), forall (x12 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 : @stdpp.bitvector.definitions.bv 64%N), forall (x15 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 : @stdpp.bitvector.definitions.bv 64%N), forall (x18 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x19 : @stdpp.bitvector.definitions.bv 64%N), forall (x20 : @stdpp.bitvector.definitions.bv 64%N), forall (x28 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 : @stdpp.bitvector.definitions.bv 64%N), forall (x31 :
    @stdpp.bitvector.definitions.bv 64%N), @PA.pctx h LBc m mo -> @Stdlib.Sorting.Permutation.Permutation (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) LBc
    (@Corelib.Init.Datatypes.app (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.lt (@Stdlib.ZArith.BinInt.Z.opp
    (@Stdlib.ZArith.BinInt.Z.pow 2%Z 31%Z)) r) (@Stdlib.ZArith.BinInt.Z.lt r 0%Z) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N p')] -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le P p') (@Stdlib.ZArith.BinInt.Z.le p' END) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    PKA [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N info); @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N ctx)] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.pk_rep_c (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT) m
    (@Corelib.Init.Datatypes.app (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.blk) owned LB) PKA info ctx owned -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z)
    [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 64%nat lj] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-48)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
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
    intros m mo h LBc r p' info ctx owned lj x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
      Ctx Perm RetRange PPCell PRange PKCell PkRep LocalBuf SavedRegs StackOk.
    clear HCALLOC CA_RSA0 CA_RSA72 CA_EC0 CA_EC72 CAT_ECGRP CAT_PKALG CAT_ECALGID CA_PKTBL CA_BP HPRB HCPK HPP0 ALPP HBS0
      B63 HPKA0 PPT ST0 MI0 SOK0 SIP0 CWP CRB RA.
    destruct Ctx as (Heap & TopEq & ModelFr & MemOk & StatOk & SinvOk & Grow & Kept).
    assert (Room : lo + 30000 + hl_stack L <= bv_unsigned sp) by (unfold PK_PARSE_STACK in SLO; lia).
    pose proof alloc_ceiling_pos as CeilPos.
    assert (FrameLit : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112).
    { apply unsigned_lit. lia. }
    destruct (HPERM h LBc (owned ++ LB) m mo Heap Perm) as (hp & HeapP & TopP).
    pose proof (heap_mok _ _ HI _ _ _ _ HeapP) as Mok.
    zstep. zstep. zstep.
    pose proof (U_pk_free_spec L HI U_MT HFREE HLS SW DIMG HND CA_MSF CA_RSA80 CA_EC80) as FreeSpec.
    unfold pk_free_c_stmt, U_PK_FREE in FreeSpec.
    eapply aevtM_cut.
    { eapply FreeSpec with (LBo := owned) (LB := LB) (h := hp) (lo := lo) (info := info) (ctx := ctx) (owned := owned);
        rewrite ?FrameLit; try eassumption; try reflexivity;
        first [ intros b Owns; exact Owns | rewrite TopP, TopEq; lia | lia ]. }
    clear FreeSpec.
    intros ms' mo' Ret. unfold pk_free_c_post in Ret.
    ddestruct Ret as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & mo1 & h1 & LBo1 &
      Cfg & MemOk1 & StatOk1 & Stk1 & ModelFr1 & Top1 & Heap1 & Shrunk & _ & Zeroed & Presx1 & Gone).
    injection Cfg as -> ->.
    rewrite FrameLit in Stk1, Presx1.
    assert (NoneLeft : LBo1 = []).
    { apply list_nil_of_empty. intros b Inb. exact (Gone b Inb (in_map fst owned b (Shrunk b Inb))). }
    subst LBo1.
    rewrite (ret_pc_even 169240) by (first [lia | reflexivity]).
    assert (StackSide : forall A cs, rw_cells usegs m A cs -> bv_unsigned sp + -112 <= A ->
              disjoint_from [(PKA, PKA + 16)] A (Z.of_nat (cells_size cs)) -> rw_cells usegs m1 A cs).
    { intros A cs Cells Above Apart.
      apply (heap_presx_rw_cells usegs L ([] ++ LB) (bv_unsigned sp + -112) [(PKA, PKA + 16)] m m1 A cs Presx1 Cells);
        [| exact Apart].
      intros a Ra. left. lia. }
    assert (PPCell1 : rw_cells usegs m1 PP [C8 (Z_to_bv 64 p')]).
    { apply StackSide; [exact PPCell| lia|]. cbn [disjoint_from cells_size csize Nat.add]. split; [lia| exact I]. }
    assert (LocalBuf1 : rw_cells usegs m1 (bv_unsigned sp + -112) [CB 64 lj]).
    { apply StackSide; [exact LocalBuf| lia|]. cbn [disjoint_from cells_size csize Nat.add]. split; [lia| exact I]. }
    assert (SavedRegs1 : FRS m1).
    { apply StackSide; [exact SavedRegs| lia|]. cbn [disjoint_from cells_size csize Nat.add]. split; [lia| exact I]. }
    assert (SinvOk1 : pk_sinv_P m1).
    { change (si_P (U_pk_sinv L HL HMC) m1). apply (si_frame (U_pk_sinv L HL HMC) m m1 SinvOk).
      intros a Ra Fp. destruct (si_data (U_pk_sinv L HL HMC) a Fp) as [Drange [_ NotStatic]].
      refine (proj1 (Presx1 a Ra _ _)).
      - right. left. split; [exact Drange| exact NotStatic].
      - cbn [outside]. split; [lia| exact I]. }
    assert (Kept1 : heap_presx usegs L LB (bv_unsigned sp) FP m0 m1).
    { apply (heap_presx_trans usegs L LB (bv_unsigned sp) FP m0 m m1 Kept).
      intros a Ra Client Out. apply Presx1; [exact Ra| |].
      - destruct Client as [Up|[Dt|Blk]]; [left; lia| right; left; exact Dt| right; right; exact Blk].
      - cbn [outside app] in Out |- *. destruct Out as (_ & NotPKA & _). split; [exact NotPKA| exact I]. }
    pose proof (heap_mok _ _ HI _ _ _ _ Heap1) as Mok1.
    zstep. zstep.
    refine (ret_walk m1 mo1 h1 LB r p' 0 0 [] lj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              Heap1 _ _ MemOk1 StatOk1 SinvOk1 Kept1 _ PPCell1 PRange Zeroed _ _ _ LocalBuf1 SavedRegs1 Stk1).
    - rewrite Top1, TopP. exact TopEq.
    - exact (mo_frame_trans mo0 mo mo1 ModelFr ModelFr1).
    - lia.
    - apply pk_rep_c_null.
    - intros _. split; [reflexivity| split; reflexivity].
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
