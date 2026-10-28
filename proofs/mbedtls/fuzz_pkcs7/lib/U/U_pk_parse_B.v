(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points U_asn1_get_mpi U_pk_parse_A.
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
Ltac2 gd_tbl_P_pk_parse_B () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_pk_parse_A.pctx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_RSA_INFO"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "RocqVerifyHarness.AgentSubmission.USpec.RepPk.PKC_inst"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.U.U_pk_sinv.U_pk_sinv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Lemma swrap32_as_mod : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31). reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L10736246414.7 L13045237767.9 L14897237694.9 L19405846407.9 L19629527575.10L23421541755.9 L23421687016.9 L32532082058.9 L32532259865.9 L38715811453.4 L42464375761.3 L4539841608.9  L8929279494.9  L8929359765.9  00000=00K00R00Y00g01001901F01S01V01Y01i02302=S1u2Hu1v1q2VDS1u1v2VB1q3V13S1u1v1qS1u1v1qS1u1v2VB1q3V13S1u1v1H1qS1u1v1H1qS1u1v2VB1q2LTS1u1v2VB1q2GES1uS1uS1u2Hu1v2VB1q2VDS1u1v2VB1qS1u1v2VB1q". (* [comment removed for export] *)
Lemma rsa_err_map : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_B ()) "Pu,$0.P,(1.=R1.)P,(2.(3.(4.&20.(5.R2.+6<.))(6.+2.+40.))+=.)(7.(2.(8.(6.+2.+1?.))(4.&20.(5.R3.+????????????<500.)))(2.(4.&20.(5.R3.+????????????<500.))=))")
(* [comment removed for export] *).
Proof.
  intros u Hu H. rewrite !swrap32_as_mod in *.
  pose proof (Z.mod_pos_bound (u + 108) (2^32) ltac:(lia)) as VB.
  pose proof (Z.div_mod (u + 108) (2^32) ltac:(lia)) as VD.
  set (v := (u + 108) mod 2^32) in *. set (q := (u + 108) / 2^32) in *.
  assert (E1 : (u + 108 + 2^31) mod 2^32 = (v + 2^31) mod 2^32).
  { replace (u + 108 + 2^31) with (v + 2^31 + q * 2^32) by lia. apply Z_mod_plus_full. }
  rewrite E1 in H.
  assert (V13 : v < 13).
  { destruct (Z_lt_dec v (2^31)) as [LT|GE].
    - rewrite (Z.mod_small (v + 2^31) (2^32)) in H by lia. rewrite Z.mod_small in H by lia. lia.
    - replace (v + 2^31) with (v - 2^31 + 1 * 2^32) in H by lia. rewrite Z_mod_plus_full in H. rewrite (Z.mod_small (v - 2^31) (2^32)) in H by lia.
      replace (v - 2^31 - 2^31) with (v - 2^32 + 2^64 + (-1) * 2^64) in H by lia. rewrite Z_mod_plus_full in H. rewrite Z.mod_small in H by lia. lia. }
  assert (E2 : (u + 18446744073709536512 + 2^31) mod 2^32 = v + 2^31 - 15212).
  { replace (u + 18446744073709536512 + 2^31) with (v + 2^31 - 15212 + (q + 2^32) * 2^32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  rewrite E2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Notation MT := U_MT (only parsing).

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
  Hypothesis HPERM : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_B ()) "Ph,(9.$:.VL,VHI,)PLB,(;.$<.)PLB',(;.$<.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$?.P,(10.$:.VL,VHI,R5.R4.R2.R1.)P,(11.$<.R5.R4.)(12.(9.$:.VL,VHI,)Lh',(9.$:.VL,VHI,)(7.(10.$:.VL,VHI,R1.R6.R5.R4.)(13.$0.(14.$:.VL,VHI,R1.)(14.$:.VL,VHI,R8.))))")
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
  Hypothesis HPRB : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_B ()) "(15.$:.VL,VHI,$16.$17.$18.+5<?:8.$19.)")
(* [comment removed for export] *).
  Hypothesis HCPK : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_B ()) "(1:.$:.VL,VHI,$16.$1;.$18.+5<?:8.$1<.$1=.)")
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
  Notation heap_presx_weak'' := (heap_presx_weak' L ra sp LB PP P END BUF PKA bs BP PE EB DPK DKB DPB NZPP NZP).
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.
  #[using="HL"] Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 HL). Qed.
  #[using="L HL"] Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 HL)). Qed.
  #[using="HL"] Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 HL))). Qed.
  #[using="HMC"] Lemma ML1 : hl_data_lo L <= U_MUL_COUNT. Proof. exact (proj1 HMC). Qed.
  #[using="HMC"] Lemma ML2 : U_MUL_COUNT + 8 <= hl_data_hi L. Proof. exact (proj1 (proj2 HMC)). Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01Y0@D10463954377.159D10463954377.160D11805467289.157D11805467289.158D12223852868.159D12223852868.160D15457446739.158D15463825327.160D19120365881.159D34028600543.210D37216054521.208D37226362885.210D41355788639.210D43928033258.157D43934434070.159D44622288685.159D44622288685.160D47139703723.208D49698585326.159D49698585326.160D49705053714.157D49705053714.158D61281570664.210D61556549392.210D61571118060.208D63898547005.210D64111535230.159D64111535230.160D7377275490.160 L10356181826.21 L10360527642.3  L1077460508.1   L11423978205.12 L11886305925.4  L12283411672.144L12283411672.148L12634579262.7  L13345498453.205L14372944785.6  L14948329643.196L15068833967.3  L16824022294.158L1725003874.1   L22052548753.6  L2397676628.0   L24446230945.0  L25584779078.10 L25815444617.6  L26641309430.3  L28009021698.3  L28011049605.143L2831671631.12  L29010380273.147L30522440326.3  L31161809777.143L32029494421.10 L34317004597.2  L34806988770.1  L34994544387.147L3582028444.1   L36660877808.7  L36671363403.3  L37317392303.8  L37335025441.143L37339008021.196L37796632789.0  L40147641242.5  L40228640085.0  L4114706726.1   L41202929119.144L41202929119.198L4125729279.21  L41320204299.10 L41672612599.8  L43058782591.10 L44075892968.12 L4660549440.154 L4709231164.2   L4728363746.1   L47431073244.8  L49728944076.8  L5079168823.0   L51925114228.148L52071584789.143L52225222276.0  L53271535775.198L53506606353.143L56892130782.4  L56904954949.21 L57381525820.21 L57393883303.2  L59314873579.2  L60264566684.1  L61275282840.201L62503018828.8  L62835830358.13 L63455408106.8  L6443869654.3   L65348482612.1  L65361585901.21 L67158371251.147L67819175067.5  L68310574691.1  L7036479304.1   L9114374322.3   00001;02F02d03B04004^05<05f06j07e08R09N0:I0:g0;Q0<]0=i0>Q0??0?m0@O0A10A20Ai0BQ0D20D`0EN0FR0Fc0Fd0Fh0GM0GN0Gi0HD0H\0IA0IT0IU0IV0J10J50JH0JI0JJ0J_0J`0Jh0K20L30LL0Lg0Lo0NU0Nc0Nj0Nn0OI0OM0Og0Oh0PF0Ql0Sd0Se0T30T40T50TP0U50Uh0V@0V\0W>0WZ0X50X<0X@0X[0Xl0Xm0YH0YI0YJ0Yo0ZJ0ZK0[A0\60\70\<0\@0]:0]U0]V0^20^:0^;0^e0_@0_R0_S0_W0_`S1L2HI2ra2sp2h02PP3PKA2bs3SPP3PPT4NZPP3NZP1h1C2HT2C03PKB3PPB2HB5Ha_st5Hl_stS1L2HI2ra2sp2h02PP3PKA2bs3SPP3PPT4NZPP3NZP1h1C2HT2C03PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs3SPP1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPP1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs1C3PKB3PPB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP3PKA2lo2bs4NZPP3NZP1C4SLO'2C03PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPP1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs4NZPP1C2lj3PKB3PPB3kbs2WF2HBS2ra2sp2PP3PKA2bs4NZPP1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPP1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs1C3PKB3PPB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP3PKA2lo2bs3ACL3DHI4NZPP3NZP1C4SLO'2C03PKB3PPB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP3PKA2lo2bs3ACL3DHI4NZPP3NZP1C4SLO'2C03PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WF2HBS2ra2sp2PP3PKA2bs3SPR1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPR1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPR1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs3SPR1C3PKB3PPB2HBFS2ra2sp2PP3PKA2bs1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WF2HBS1L3HLS2ra2sp2PP3PKA2lo2bs3SPP3ACL3DHI4NZPP3NZP1C2E22lj3ACP4SLO'2C03PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPK1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPK1C3PKB3PPB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP3PKA2lo2bs4NZPP3NZP1C4SLO'2C03PKB3PPB2HB5Ha_st5Hl_stS1L2sp2lo2bs4SLO'FS2spS1P3END3BUF2bs2BP2EB1p2E22PB3E2B1a2HaFS2ra2sp2PP3PKA2bs1C3PKB3PPBS2ra2sp2PP3PKA2bs1C3PKB3PPBS1L1C3CIM2M12M23E1'4E2''S2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WFS1P3END1p2E22PB3E2BFFS2ra2sp2PP3PKA2bs1C3PKB3PPBS2spS1P3END1p2E22PB3E2BSSS1P3BUF2bs2BP1p2E22PBFS2PP1C1QS1C2C03C64S1L3HLS2ra2sp2PP3PKA2lo2bs3SPK3ACL4NZPP3NZP1C4SLO'2C03CAC3PKB3PPBS1P3BUF2bs2BP1C1p2E22PB1QS2ra2sp2PP3PKA2bs1C3PKB3PPBS2PP1C1QS1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22PB3E2B3ACP3BAC4SLO'2C03PKB3PPBS1P2bs1p2E22PBS2x42XRS2spS2ra2sp2PP3PKA2bs1C3PKB3PPBS2spS1L3HLS2sp2lo3ACL3ACP4SLO'FS1L3HLS2sp2lo3ACL3SPR3ACP4SLO'S1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22PB3E2B3ACP3BAC4SLO'2C03PKB3PPBS1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22lj2PB3E2B3ACP3BAC4SLO'2C03PKB3PPB3kbs4LENK2WF2KESS1L2M12M21a2HaSFS2ra2sp2PP3PKA2bs1C3PKB3PPBS2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WFS1L3HLS2sp1P3BUF2lo2bs2BP4BUF03ACL1p2E22PB3BAC4SLO'S3END3BUF2bs2EB1p2E23E2BS1L3HLS2sp2lo3ACL1C4SLO'3CACS1L3HLS2sp2PP2lo3SPP3ACL4SLO'1d2PcS3END3BUF2bs2EB1C1p2E23E2B1QS2ra2sp2PP3PKA2bs1C3PKB3PPBS2lj2WFS2spS1L1C3CIM2I12I22I33E1'4E2''S1L2HI2sp2h04HTOPSS2ra2sp2PP3PKA2bs1C3PKB3PPBFSS2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WFS2ra2sp2PP3PKA2bs1C3PKB3PPBFS1L3HLS2sp3END3BUF2lo2bs2EB4BUF03ACL1p2E23E2B3BAC4SLO'S1L3HLS2sp3END3BUF2lo2bs2EB3B633ACL1p2E23E2B3BAC4SLO'FS1C1HS2spS2ra2sp2PP3PKA2bs1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_st2HDS1L1C3CIM2I12I22I33E1'4E2''FS1L3HLS2sp2lo3ACL1C4SLO'3CACS2sp3SPAFS1L3HLS2sp3BUF2lo2bs4BUF03ACL3SPA3BAC4SLO'S2ra2sp2PP3PKA2bs1C3PKB3PPBS1L3HLS2sp2lo4SLO'FS2spS3PKA1C1Q". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND HPERM CA_MSF CA_RSA0 CA_RSA80 CA_EC0 CA_EC80 BUF bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP PPT SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR"] Lemma rsa_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (C : @Corelib.Numbers.BinNums.Z), forall (p : @Corelib.Numbers.BinNums.Z), forall (E2 : @Corelib.Numbers.BinNums.Z), forall (alen : @stdpp.bitvector.definitions.bv 64%N),
    forall (oj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x10 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 : @stdpp.bitvector.definitions.bv 64%N), forall (x12 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 : @stdpp.bitvector.definitions.bv 64%N), forall (x15 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 : @stdpp.bitvector.definitions.bv 64%N), forall (p0 :
    @Corelib.Numbers.BinNums.Z), forall (x20 : @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv
    64%N), forall (x30 : @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N), @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0
    mo0 h0 LB PP PKA h (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair
    (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 232%Z) LB) m mo -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepRsa.rsa_at
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 232%Z) LB) C (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepRsa.rsa_fresh C) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.block_range L C 232%Z -> (forall (B : @Corelib.Numbers.BinNums.Z), forall (k : @Corelib.Numbers.BinNums.Z), @Stdlib.Lists.List.In
    (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) B
    k) LB -> @Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add C 232%Z) B) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add B k) C)) ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p E2) -> @Stdlib.ZArith.BinInt.Z.le E2 END ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)); @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N C)] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 48%nat lj] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-64)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat oj; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 alen] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-48)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le BUF p0) (@Stdlib.ZArith.BinInt.Z.le p0 END) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) (@stdpp.bitvector.definitions.Z_to_bv 64%N PP) x10 x11 x12 x13 x14 x15 x16 x17
    (@stdpp.bitvector.definitions.Z_to_bv 64%N E2) (@stdpp.bitvector.definitions.Z_to_bv 64%N p0) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (@stdpp.bitvector.definitions.Z_to_bv
    64%N 0x293dc%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX RSA0 BRC APC HPP PB E2B HPKA FRL FRO FR ST P00.
    dpose pa_basics' as (ACP & BAC & BIM & PPD & PKD & SLO').
    dpose CX as (HH & HT & MF & MI & SOK & SIP & SUB & PX). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    dpose BRC as (C0 & C16 & _ & CAC & CIM).
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB.
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. cbn [cells_size csize Nat.add] in PPB.
    (* [comment removed for export] *)
    pose proof (conj MI I) as MIbox.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp + -48)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end. match goal with W : wmono usegs m m1 |- _ => rename W into WM1 end.
    pose proof (pctx_munch' _ _ _ _ _ _ CX MU WM1 MI1 ltac:(constructor; [cbn; left; clear -SLO' HLS; lia| constructor])) as CX1.
    assert (RSA1 : rsa_at usegs m1 ((C, 232) :: LB) C (rsa_fresh C)).
    { eapply rsa_at_munch; [exact RSA0| exact MU| exact WM1| exact (proj1 MIbox)| exact MI1| cbn [disjoint_from]; clear -CAC ACL SLO' HLS; lia|].
      cbn. intros d Hd HO. exfalso. decompose [or] Hd; try contradiction; subst d; cbn in HO; discriminate. }
    clear MU WM1 CX RSA0 MIbox. dpose CX1 as (HH1 & _ & _ & _ & SOK1 & _). clear HH HT MF SIP SUB PX. try clear SOK.
    (* [comment removed for export] *)
    match goal with H : rw_cells usegs m1 (bv_unsigned sp + -64) _ |- _ => rename H into FRO1 end.
    pose proof (U_pk_get_type_spec L CA_RSA0 CA_EC0) as SPT. unfold pk_get_type_stmt, pk_get_type_post, U_PK_GET_TYPE in SPT.
    zstep. zstep.
    rename FRO1 into FROa.
    acallp (eapply SPT with (A := bv_unsigned sp + -64) (info := U_RSA_INFO); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear -SLO' HLS SPR; lia);
           first [exact FROa| exact MI1| exact SOK1| reflexivity| right; left; reflexivity| clear -SPA SPR; lia| clear -SLO' HLS ACL ACP; lia
                 | match goal with |- ?g => idtac "PTLEFT" g end]).
    match goal with H : U_RSA_INFO = U_RSA_INFO -> ?t = 1 |- _ => pose proof (H eq_refl) as TY; clear H; subst t end.
    repeat match goal with H : _ -> _ = _ |- _ => clear H | H : _ -> _ <= _ <= _ |- _ => clear H end.
    rename FROa into FRO1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    dpose RSA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C64 & _). unfold RSA_CTX_SIZE in C64.
    (* [comment removed for export] *)
    pose proof (pctx_bytes' _ _ _ _ CX1) as HBS1.
    set (kbs := firstn (Z.to_nat (E2 - p)) (skipn (Z.to_nat (p - BUF)) bs)).
    assert (LENK : Z.of_nat (length kbs) = E2 - p) by (subst kbs; apply U_asn1_get_mpi.bytes_at_sub_length; clear -PB E2B BP EB; lia).
    assert (HKB : bytes_at usegs m1 p kbs) by (subst kbs; eapply U_asn1_get_mpi.bytes_at_sub; [exact HBS1| | |]; clear -PB E2B BP EB; lia).
    clearbody kbs.
    dpose CX1 as (_ & HT1 & MF1 & _ & _ & SIP1 & SUB1 & PX1).
    pose proof (U_rsa_parse_pubkey_spec L HI HFREE HCALLOC HLS SW DIMG HND _ eq_refl) as SRP. unfold rsa_parse_pubkey_stmt, rsa_parse_pubkey_post, U_RSA_PARSE_PUBKEY in SRP.
    zstep.
    eapply aevtM_cut.
    { eapply SRP with (lo := lo) (h := h) (LB := (C, 232) :: LB) (C := C) (KEY := p) (kbs := kbs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by (clear -SLO' HLS ACL ACP SPR; lia); rewrite ?LENK;
        first [ exact HH1 | exact RSA1 | exact HKB | exact TP | exact MI1 | exact SOK1 | exact CA_MSF | exact ACL | exact DHI | eassumption | reflexivity
              | f_equal; clear; lia
              | (* [comment removed for export] *) f_equal; lazymatch goal with |- Z.land ?msk C = C => replace msk with (Z.ones 64) by reflexivity end;
                rewrite Z.land_comm, Z.land_ones by (clear; lia); apply Z.mod_small; clear -C0 C64; lia
              | (* [comment removed for export] *) intros a Ha; right; right; exists (BUF, Z.of_nat (length bs)); split; [right; exact INB| cbn; clear -Ha PB E2B BP EB; lia]
              | (* [comment removed for export] *) unfold RSA_CTX_SIZE; destruct (APC _ _ INB) as [Q|Q]; [right; clear -Q PB E2B BP EB; lia| left; clear -Q PB E2B BP EB; lia]
              | rewrite HT1; clear -HTOP SLO' HLS; lia
              | clear -PB E2B BP EB B63 BUF0 BAC ACL SLO' HLS SPA SPR; lia
              | match goal with |- ?g => idtac "RPLEFT" g end ]. }
    clear SRP.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2'. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by (clear -SLO' HLS ACL ACP SPR; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & RSA2 & COV2 & SUB2 & NEW2 & PX2 & SOK2).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HH2 with HEAP _ _ _ ?hh ?lb _ _ => rename hh into h2; rename lb into LB2 end.
    match type of RSA2 with rsa_at _ _ _ _ ?rr => rename rr into r' end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. clear MK.
    unfold RSA_CTX_SIZE in PX2.
    (* [comment removed for export] *)
    assert (XF : Forall (fun iv => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C, C + 232)]) by (constructor; [cbn; left; clear -CAC ACL SLO' HLS; lia| constructor]).
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FRL; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FRO1; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FR; [| clear; lia| cbn; clear; lia| exact XF].
    match goal with H : rw_cells usegs m1 PP _ |- _ =>
      apply (keep_pp' ((C, 232) :: LB) _ _ m1 m2 _ PX2 ltac:(intros b Hb; right; exact Hb) ltac:(clear; lia)) in H; [| reflexivity| cbn; pose proof (fresh_apart_pp' C 232 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]]; rename H into HPP2 end.
    match goal with H : rw_cells usegs m1 PKA _ |- _ =>
      apply (keep_pka' ((C, 232) :: LB) _ _ m1 m2 _ PX2 ltac:(intros b Hb; right; exact Hb) ltac:(clear; lia)) in H; [| reflexivity| cbn; pose proof (fresh_apart_pka' C 232 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]]; rename H into HPKA2 end.
    (* [comment removed for export] *)
    assert (CX2 : pctx' h2 LB2 m2 mo2).
    { split; [exact HH2|]. split; [rewrite HT2; exact HT1|]. split; [eapply mo_frame_trans; [exact MF1| exact MF2]|]. split; [exact MI2|]. split; [exact SOK2|].
      split. { destruct SIP1 as [IDS1 [cnt RC1]]. pose proof IL1 as I1; pose proof IL2 as I2; pose proof IL3 as I3; pose proof ML1 as M1; pose proof ML2 as M2; pose proof DI1 as E1'; pose proof DI2 as E2''. split.
               - apply (ecp_ids_state_presx usegs L _ _ _ _ _ m1 m2 IDS1 PX2 HL); cbn; clear -CIM I1 I2 I3 E1' E2''; (split; [lia| exact I]).
               - exists cnt. eapply heap_presx_rw_cells; [exact PX2| exact RC1| |]; cbn [cells_size csize Nat.add disjoint_from].
                 + intros a Ha. right; left. split; [clear -Ha M1 M2; lia| exact (proj2 (proj2 (proj2 HMC) a Ha))].
                 + split; [clear -CIM M1 M2 E1' E2''; lia| exact I]. }
      split; [intros b Hb; apply SUB2; right; exact Hb|].
      eapply heap_presx_trans; [exact PX1|]. eapply heap_presx_weak''; [exact PX2| intros b Hb; right; exact Hb| clear; lia|].
      intros a Hc _. cbn. split; [| exact I]. intros Ha. exact (fresh_not_client' C 232 a BRC APC Ha Hc). }
    clear CX1 HH1 SOK1 HT1 MF1 SIP1 SUB1 PX1 MI1 HBS1 HKB.
    (* [comment removed for export] *)
    dpose CX2 as (_ & HT2' & MF2' & _ & _ & SIP2 & SUB2' & PX2').
    set (owned := (C, 232) :: rsa_limb_blocks r').
    assert (NDL : List.NoDup (map fst LB)) by exact (HND _ _ _ _ HH0).
    pose proof (HND _ _ _ _ HH2) as ND2.
    dpose RSA2 as (_ & _ & _ & _ & _ & _ & _ & ALL2 & _ & _ & _ & CIN2 & NC1 & NC2 & NNE).
    assert (LIMBS : forall b, In b (rsa_limb_blocks r') -> In b LB2) by (intros b Hb; eapply rsa_limb_blocks_in; [exact RSA2| exact Hb]).
    assert (PERM : Permutation LB2 (owned ++ LB)).
    { apply perm_of_sets; [exact ND2| |].
      - apply (nodup_fst_of_sub _ LB2 ND2).
        + subst owned. cbn [app]. intros b [E|Hb]; [subst b; exact CIN2|]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (LIMBS b Hb)| apply SUB2'; exact Hb].
        + subst owned. cbn [app]. constructor.
          * intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
            -- unfold rsa_limb_blocks in Hin. apply in_app_or in Hin.
               destruct Hin as [Hin|Hin]; apply mpd_blk_in in Hin; destruct Hin as [HO E]; injection E as Ea Eb; [exact (NC1 HO (eq_sym Ea))| exact (NC2 HO (eq_sym Ea))].
            -- destruct (APC _ _ Hin); clear -H; lia.
          * apply NoDup_app.
            -- unfold rsa_limb_blocks. destruct (mpd_blk_cases (r_N r')) as [EN|[ON EN]]; destruct (mpd_blk_cases (r_E r')) as [EE|[OE EE]]; rewrite EN, EE; cbn [app].
               ++ constructor.
               ++ constructor; [intros []| constructor].
               ++ constructor; [intros []| constructor].
               ++ constructor; [| constructor; [intros []| constructor]]. intros [E|[]]. injection E as Ea Eb. exact (NNE ON OE (eq_sym Ea)).
            -- apply (NoDup_map_inv fst). exact NDL.
            -- intros b Hb HbL. exact (NEW2 b Hb ltac:(right; exact HbL)).
      - intros b. subst owned. cbn [app]. split.
        + intros Hb. destruct (COV2 b Hb) as [Hb'|Hb'].
          * destruct Hb' as [E|Hb']; [left; exact E| right; apply in_or_app; right; exact Hb'].
          * right; apply in_or_app; left; exact Hb'.
        + intros [E|Hb]; [subst b; exact CIN2|]. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (LIMBS b Hb)| apply SUB2'; exact Hb]. }
    assert (INP : forall b, In b LB2 -> In b (owned ++ LB)) by (intros b Hb; eapply Permutation_in; [exact PERM| exact Hb]).
    (* [comment removed for export] *)
    assert (REPm : forall mx, mem_inv usegs mx -> rsa_at usegs mx LB2 C r' -> pk_rep_c usegs U_RSA_INFO U_EC_INFOS MT mx (owned ++ LB) PKA U_RSA_INFO C owned).
    { (intros mx MIx dd_H; ddestruct dd_H as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QALL & Q9 & Q10 & Q11 & QIN & Q13 & Q14 & Q15)).
      right; left. split; [reflexivity|]. split; [unfold U_RSA_INFO; clear; lia|]. split; [exact MIx|].
      exists r'. split; [| intros b'; subst owned; split; intros Hx; exact Hx].
      refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj _ (conj Q9 (conj Q10 (conj Q11 (conj (INP _ QIN) (conj Q13 (conj Q14 Q15)))))))))))))).
      apply Forall_forall. intros d Hd. eapply mpdr_at_LB_mono; [exact (proj1 (Forall_forall _ _) QALL d Hd)| exact INP]. }
    (* [comment removed for export] *)
    pose proof FRL as [[WF _] _]. cbn in WF.
    lazymatch type of FRO1 with rw_cells _ _ _ [C8 ?w1; C8 ?w2] => set (wi := w1) in FRO1; set (wc := w2) in FRO1; clearbody wi wc end.
    chunk_join FRL FRO1 FRJ.
    eapply rw_cells_reshape with (cs' := [CB 64 (lj ++ le8 wi ++ le8 wc)]) in FRJ;
      [| cbn; rewrite ?app_length, ?length_le8; cbn; split; [clear -WF; lia| exact I]| cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity].
    clearbody owned.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      pose proof (conj MI2 (conj HH2 I)) as BOX2. clear HH2.
      pose proof (munch_refl [(PP, PP + 8)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      zstep. zstep. zstep. zstep. pk_ckb KN ltac:(clear -P00 PB E2B BP EB BUF0 B63; lia).
      zstep. zstep. zstep. zstep. zstep. zstep. pk_ckb KS ltac:(clear -P00 PB E2B BP EB BUF0 B63; lia).
      zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with M : mem_inv usegs m3 |- _ => rename M into MI3 end. match goal with W : wmono usegs m2 m3 |- _ => rename W into WM3 end.
      pose proof (pctx_munch' _ _ _ _ _ _ CX2 MU WM3 MI3 ltac:(constructor; [cbn; right; left; reflexivity| constructor])) as CX3.
      assert (RSA3 : rsa_at usegs m3 LB2 C r').
      { eapply rsa_at_munch; [exact RSA2| exact MU| exact WM3| exact (proj1 BOX2)| exact MI3| cbn [disjoint_from]; pose proof (fresh_apart_pp' C 232 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]|].
        intros d Hd HO. destruct (heap_blocks _ _ HI _ _ _ _ (proj1 (proj2 BOX2))) as [HBR2 _].
        rewrite Forall_forall in ALL2. pose proof (ALL2 d Hd) as MDd.
        destruct (mpdr_blk_facts usegs L _ _ _ MDd HO HBR2) as (HIn & _ & _ & Pc & _).
        cbn. split; [| exact I]. clear -Pc ACL SLO' HLS SPP. left. lia. }
      clear MU WM3 CX2 RSA2 BOX2.
      zstep. if_cases KE; zify_cond KE. 2:{ exfalso. first [ apply KE; reflexivity | clear -KE PB E2B BP EB B63 BUF0; rewrite ?unsigned_lit in KE by lia; lia ]. }
      zstep. zstep.
      dpose CX3 as (HH3 & HT3 & MF3 & _ & SOK3 & SIP3 & SUB3 & PX3).
      destruct (HPERM _ _ _ _ _ HH3 PERM) as (h4 & HH4 & HT4).
      match goal with H : rw_cells usegs m3 PP _ |- _ => rename H into HPP3 end.
      eapply ret_walk' with (owned := owned) (info := U_RSA_INFO) (ctx := C) (h := h4);
        [ exact HH4 | rewrite HT4; exact HT3 | exact MF3 | exact MI3 | exact SOK3 | exact SIP3 | exact PX3 | clear; lia | exact HPP3 | clear -PB E2B; lia
        | exact HPKA2 | exact (REPm m3 MI3 RSA3) | intros NZ; exfalso; apply NZ; reflexivity | reflexivity | exact FRJ | exact FR | exact ST2 ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases KG; zify_cond KG.
      + (* [comment removed for export] *)
        eapply fail_free_walk' with (owned := owned) (info := U_RSA_INFO) (ctx := C);
          [ exact CX2 | exact PERM | clear; lia | exact HPP2 | clear -PB E2B; lia | exact HPKA2 | exact (REPm m2 MI2 RSA2) | exact FRJ | exact FR | exact ST2 ].
      + (* [comment removed for export] *)
        zstep. zstep.
        lazymatch type of KG with context [bv_swrap 32 (bv_unsigned ?xw + 108)] =>
          pose proof (bv_unsigned_in_range 64 xw) as XR;
          pose proof (rsa_err_map (bv_unsigned xw) ltac:(clear -XR; lia) KG) as RRm end.
        eapply fail_free_walk' with (owned := owned) (info := U_RSA_INFO) (ctx := C);
          [ exact CX2 | exact PERM | exact RRm | exact HPP2 | clear -PB E2B; lia | exact HPKA2 | exact (REPm m2 MI2 RSA2) | exact FRJ | exact FR | exact ST2 ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.
