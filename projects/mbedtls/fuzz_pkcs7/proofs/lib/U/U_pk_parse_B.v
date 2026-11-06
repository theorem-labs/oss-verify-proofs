(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points U_asn1_get_mpi U_pk_parse_A.
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
Ltac2 gd_tbl_P_pk_parse_B () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "OSSVerify.KrLib.U.U_ecp_defs.U_MT"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "OSSVerify.KrLib.U.U_platform_zeroize.U_MEMSET_FUNC"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.U_BAD_POINTS"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "OSSVerify.KrLib.U.U_pk_parse_A.pctx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.RepRsa.rsa_at"; "OSSVerify.KrLib.Spec.RepRsa.rsa_fresh"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.U.U_pk_free.U_RSA_INFO"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "OSSVerify.KrLib.USpec.RepPk.PKC_inst"; "OSSVerify.KrLib.U.U_pk_free.U_EC_INFOS"; "OSSVerify.KrLib.U.U_pk_sinv.U_pk_sinv"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].


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
  Notation XS := [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (380840, 380840 + 8); (U_ECP_IDS, U_ECP_IDS + 56)].

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
  Notation FRS mem_at := (rw_cells usegs mem_at (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
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
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (C : @Corelib.Numbers.BinNums.Z), forall (p : @Corelib.Numbers.BinNums.Z), forall (E2 : @Corelib.Numbers.BinNums.Z), forall (alen : @stdpp.bitvector.definitions.bv 64%N),
    forall (oj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (lj : @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x10 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 : @stdpp.bitvector.definitions.bv 64%N), forall (x12 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 : @stdpp.bitvector.definitions.bv 64%N), forall (x15 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 : @stdpp.bitvector.definitions.bv 64%N), forall (p0 :
    @Corelib.Numbers.BinNums.Z), forall (x20 : @stdpp.bitvector.definitions.bv 64%N), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv
    64%N), forall (x30 : @stdpp.bitvector.definitions.bv 64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N), @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0
    mo0 h0 LB PP PKA h (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair
    (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 232%Z) LB) m mo -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepRsa.rsa_at
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Corelib.Init.Datatypes.cons (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z))
    (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) C 232%Z) LB) C (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.RepRsa.rsa_fresh C) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.block_range L C 232%Z -> (forall (B : @Corelib.Numbers.BinNums.Z), forall (k : @Corelib.Numbers.BinNums.Z), @Stdlib.Lists.List.In
    (@Corelib.Init.Datatypes.prod (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z)) (@Corelib.Init.Datatypes.pair (@Corelib.Numbers.BinNums.Z) (@Corelib.Numbers.BinNums.Z) B
    k) LB -> @Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add C 232%Z) B) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add B k) C)) ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p E2) -> @Stdlib.ZArith.BinInt.Z.le E2 END ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)); @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N C)] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 48%nat lj] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-64)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat oj; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 alen] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-48)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-112)%Z) -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le BUF p0) (@Stdlib.ZArith.BinInt.Z.le p0 END) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) (@stdpp.bitvector.definitions.Z_to_bv 64%N PP) x10 x11 x12 x13 x14 x15 x16 x17
    (@stdpp.bitvector.definitions.Z_to_bv 64%N E2) (@stdpp.bitvector.definitions.Z_to_bv 64%N p0) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (@stdpp.bitvector.definitions.Z_to_bv
    64%N 0x293dc%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).

  Proof.
    intros m mo h C p E2 alen oj lj x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 p0 x20 x28 x29 x30 x31
      ctx_in rsa_in blk_c apart_c pp_in p_in e2_end pka_in lj_in oj_in regs_in stk_in p0_in.
    pose proof alloc_ceiling_pos as ceil_pos.
    pose proof ctx_in as (heap_in & _ & _ & mi_in & _).
    pose proof (heap_mok _ _ HI _ _ _ _ heap_in) as mok_in.
    clear heap_in.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp + -48)] m) as mu_1.
    pose proof (wmono_refl usegs m) as wm_1.
    do 6 zstep.
    rename m2 into m1.
    assert (ctx_1 : pctx' h ((C, 232) :: LB) m1 mo).
    { refine (pctx_munch' h ((C, 232) :: LB) m m1 mo _ ctx_in mu_1 wm_1 mi_in _).
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold PK_PARSE_STACK in SLO. lia. }
    pose proof ctx_1 as (_ & _ & _ & _ & sok_1 & _).
    pose proof (U_pk_get_type_spec L CA_RSA0 CA_EC0) as ty_spec.
    unfold pk_get_type_stmt, U_PK_GET_TYPE in ty_spec.
    eapply aevtM_cut_evt; [exact mok_in | eapply ty_spec with (A := bv_unsigned sp + -64) (info := U_RSA_INFO) (c := Z_to_bv 64 C);
      [ exact oj_in | unfold PK_PARSE_STACK in SLO; lia | unfold PK_PARSE_STACK in SLO; lia | right; left; reflexivity
      | exact mi_in | exact sok_1 | reflexivity | reflexivity ] | ].
    intros ms_t post_t.
    destruct post_t as (a1_t & ty & ms_t_eq & _ & ty_rsa & _ & _).
    subst ms_t. rewrite (ty_rsa eq_refl). clear ty_rsa ty_spec.
    rewrite (ret_pc_even 168948) by (first [lia | reflexivity]).
    do 8 zstep.
    pose proof pa_basics' as (_ & buf_ceil & _ & _ & _ & room).
    pose proof blk_c as (c_pos & c_al & _ & c_ceil & c_img).
    assert (fs_bound : 0 <= bv_unsigned sp + -112 < 2 ^ 64) by lia.
    assert (a0_c : Z.land ((Z.b2z (0 <? 0) + -1) mod 18446744073709551616) (C mod 18446744073709551616) = C).
    { change ((Z.b2z (0 <? 0) + -1) mod 18446744073709551616) with (Z.ones 64).
      rewrite Z.land_comm, Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
    rewrite a0_c. clear a0_c.
    pose proof (pctx_bytes' h ((C, 232) :: LB) m1 mo ctx_1) as bs_1.
    pose proof (bytes_at_sub usegs m1 BUF bs p (E2 - p) bs_1 ltac:(lia) ltac:(lia) ltac:(lia)) as key_1.
    pose proof (bytes_at_sub_length bs BUF p (E2 - p) ltac:(lia) ltac:(lia) ltac:(lia)) as key_len.
    set (key := firstn (Z.to_nat (E2 - p)) (skipn (Z.to_nat (p - BUF)) bs)) in key_1, key_len.
    assert (rsa_1 : rsa_at usegs m1 ((C, 232) :: LB) C (rsa_fresh C)).
    { pose proof ctx_in as (_ & _ & _ & mi_0 & _).
      refine (rsa_at_munch usegs m m1 _ C _ _ rsa_in mu_1 wm_1 mi_0 mi_in _ _).
      - cbn [disjoint_from]. split; [lia | exact I].
      - intros d d_in own_heap. cbn [rsa_mpds rsa_fresh r_N r_E rsa_zero_mpds rsa_zero_offs map] in d_in.
        repeat (destruct d_in as [d_eq | d_in]; [subst d; discriminate own_heap |]). destruct d_in. }
    pose proof (U_rsa_parse_pubkey_spec L HI HFREE HCALLOC HLS SW DIMG HND U_MEMSET_FUNC eq_refl) as rp_spec.
    unfold rsa_parse_pubkey_stmt, U_RSA_PARSE_PUBKEY in rp_spec.
    pose proof ctx_1 as (heap_1 & top_1 & _).
    rewrite <- (unsigned_lit (bv_unsigned sp + -112)) in stk_in by exact fs_bound.
    unfold RSA_CTX_SIZE, PK_PARSE_STACK in *.
    eapply aevtM_cut; [ eapply rp_spec with (h := h) (LB := (C, 232) :: LB) (C := C) (KEY := p) (kbs := key) (lo := lo);
      [ exact heap_1 | exact rsa_1 | exact key_1 | lia | lia
      | apply (client_range_blk L _ lo BUF (Z.of_nat (length bs))); [right; exact INB | lia | lia ]
      | destruct (apart_c BUF (Z.of_nat (length bs)) INB) as [c_under | c_over]; [right | left]; lia
      | rewrite unsigned_lit by exact fs_bound; lia
      | exact stk_in
      | rewrite unsigned_lit by exact fs_bound; lia
      | exact ACL
      | rewrite unsigned_lit, top_1 by exact fs_bound; lia
      | rewrite unsigned_lit by exact fs_bound; lia
      | exact DHI | exact TP | exact mi_in | exact sok_1 | exact CA_MSF | reflexivity | reflexivity | reflexivity
      | rewrite key_len; reflexivity ] | ].
    clear rp_spec.
    intros ms_2 mo2 post_2. unfold rsa_parse_pubkey_post in post_2.
    destruct post_2 as (t0r & t1r & t2r & a0r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r
      & m2 & mo2r & h2 & LB2 & r2 & cfg_2 & mi_2 & stk_2 & mof_2 & top_2 & heap_2 & rsa_2 & sub_2 & sup_2
      & new_2 & presx_2 & sok_2).
    injection cfg_2 as -> ->.
    rewrite (ret_pc_even 168980) by (first [lia | reflexivity]).
    unfold RSA_CTX_SIZE in presx_2.
    rewrite unsigned_lit in presx_2, stk_2 by exact fs_bound.
    pose proof (heap_mok _ _ HI _ _ _ _ heap_2) as mok_2.
    pose proof ctx_1 as (_ & _ & mof_1 & _ & _ & sinv_1 & _ & keep_1).
    pose proof (fresh_apart_pp' C 232 blk_c apart_c ltac:(lia)) as c_pp.
    pose proof (fresh_apart_pka' C 232 blk_c apart_c ltac:(lia)) as c_pka.
    assert (sub_c : forall b, In b LB -> In b ((C, 232) :: LB)) by (intros b b_in; right; exact b_in).
    assert (far_c : Forall (fun iv : Z * Z => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(C, C + 232)]).
    { apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia. }
    pose proof (keep_pp' _ _ _ _ _ _ presx_2 sub_c ltac:(lia) pp_in eq_refl ltac:(cbn [disjoint_from]; split; [lia | exact I])) as pp_2.
    pose proof (keep_pka' _ _ _ _ _ _ presx_2 sub_c ltac:(lia) pka_in eq_refl ltac:(cbn [disjoint_from]; split; [lia | exact I])) as pka_2.
    pose proof (keep_frame' _ _ _ _ _ _ _ presx_2 ltac:(lia) lj_in ltac:(lia) ltac:(cbn; lia) far_c) as lj_2.
    pose proof (keep_frame' _ _ _ _ _ _ _ presx_2 ltac:(lia) oj_in ltac:(lia) ltac:(cbn; lia) far_c) as oj_2.
    pose proof (keep_frame' _ _ _ _ _ _ _ presx_2 ltac:(lia) regs_in ltac:(lia) ltac:(cbn; lia) far_c) as regs_2.
    clear pp_in pka_in lj_in oj_in regs_in.
    assert (ctx_2 : pctx' h2 LB2 m2 mo2r).
    { refine (conj heap_2 (conj _ (conj (mo_frame_trans mo0 mo mo2r mof_1 mof_2) (conj mi_2 (conj sok_2 (conj _ (conj _ _))))))).
      - rewrite top_2. exact top_1.
      - change (si_P (U_pk_sinv L HL HMC) m2). apply (si_frame (U_pk_sinv L HL HMC) m1 m2 sinv_1).
        intros a a_rng a_fp. destruct (si_data (U_pk_sinv L HL HMC) a a_fp) as [a_data [_ a_ns]].
        refine (proj1 (presx_2 a a_rng _ _)).
        + right. left. split; [exact a_data | exact a_ns].
        + cbn [outside]. split; [| exact I]. pose proof DI1 as img_data_lo. pose proof DI2 as img_data_hi. lia.
      - intros b b_in. apply sup_2. right. exact b_in.
      - apply (heap_presx_trans usegs L LB (bv_unsigned sp) FP m0 m1 m2 keep_1).
        apply (heap_presx_weak'' ((C, 232) :: LB) (bv_unsigned sp + -112) [(C, C + 232)] FP m1 m2 presx_2 sub_c ltac:(lia)).
        intros a a_cl _. cbn [outside]. split; [| exact I].
        intros a_c. exact (fresh_not_client' C 232 a blk_c apart_c a_c a_cl). }
    pose proof (HND h2 LB2 m2 mo2r heap_2) as nd_2.
    pose proof (HND h ((C, 232) :: LB) m1 mo heap_1) as nd_1.
    pose proof (NoDup_map_inv fst LB (HND h0 LB m0 mo0 HH0)) as nd_lb.
    assert (c_not_lb : ~ In (C, 232) LB).
    { intros c_in. cbn [map] in nd_1. apply NoDup_cons_iff in nd_1 as [c_fresh _].
      apply c_fresh. exact (in_map fst LB (C, 232) c_in). }
    assert (blk_dec : forall x y : blk, {x = y} + {x <> y}) by (intros x y; decide equality; apply Z.eq_dec).
    set (owned := List.filter (fun b => if in_dec blk_dec b LB then false else true) LB2).
    assert (owned_spec : forall b, In b owned <-> In b LB2 /\ ~ In b LB).
    { intros b. unfold owned. rewrite filter_In.
      destruct (in_dec blk_dec b LB) as [b_lb | b_lb]; split; intros [b_l2 b_k]; try discriminate; tauto. }
    assert (owned_iff : forall b, In b owned <-> In b ((C, 232) :: rsa_limb_blocks r2)).
    { intros b. rewrite owned_spec. split.
      - intros [b_l2 b_nlb]. destruct (sub_2 b b_l2) as [[b_c | b_lb] | b_limb].
        + left. exact b_c.
        + contradiction.
        + right. exact b_limb.
      - intros [b_c | b_limb].
        + subst b. split; [apply sup_2; left; reflexivity | exact c_not_lb].
        + split; [exact (rsa_limb_blocks_in usegs m2 LB2 C r2 b rsa_2 b_limb) |].
          intros b_lb. exact (new_2 b b_limb (or_intror b_lb)). }
    assert (perm_2 : Permutation LB2 (owned ++ LB)).
    { apply perm_of_sets; [exact nd_2 | |].
      - apply (nodup_fst_of_sub (owned ++ LB) LB2 nd_2).
        + intros b b_in. apply in_app_or in b_in as [b_o | b_lb]; [apply owned_spec in b_o; tauto | apply sup_2; right; exact b_lb].
        + apply NoDup_app; [apply NoDup_filter; exact (NoDup_map_inv fst LB2 nd_2) | exact nd_lb |].
          intros b b_o. apply owned_spec in b_o. tauto.
      - intros b. rewrite in_app_iff, owned_spec. split.
        + intros b_l2. destruct (in_dec blk_dec b LB) as [b_lb | b_lb]; [right; exact b_lb | left; tauto].
        + intros [[b_l2 _] | b_lb]; [exact b_l2 | apply sup_2; right; exact b_lb]. }
    assert (rep_2 : pk_rep_c usegs U_RSA_INFO U_EC_INFOS U_MT m2 (owned ++ LB) PKA U_RSA_INFO C owned).
    { apply (pk_rep_c_frame usegs U_RSA_INFO U_EC_INFOS U_MT m2 m2 LB2 (owned ++ LB) PKA U_RSA_INFO C owned).
      - right. left. refine (conj eq_refl (conj _ (conj mi_2 (ex_intro _ r2 (conj rsa_2 owned_iff))))).
        unfold U_RSA_INFO. lia.
      - exact mi_2.
      - intros b b_in. apply in_or_app. left. exact b_in.
      - intros a _. reflexivity. }
    assert (frame_fold : forall mm, stk usegs mm lo (bv_unsigned sp + -112) ->
              rw_cells usegs mm (bv_unsigned sp + -112) [CB 48 lj] ->
              rw_cells usegs mm (bv_unsigned sp + -64) [C8 (Z_to_bv 64 U_RSA_INFO); C8 (Z_to_bv 64 C)] ->
              stk usegs mm lo (bv_unsigned sp + -112) /\ exists junk, rw_cells usegs mm (bv_unsigned sp + -112) [CB 64 junk]).
    { intros mm stk_m low_m high_m.
      pose proof (stk_release _ _ _ _ _ stk_m low_m ltac:(lia)) as upto_64. cbn [cells_size csize Nat.add] in upto_64.
      replace (bv_unsigned sp + -112 + Z.of_nat 48) with (bv_unsigned sp + -64) in upto_64 by lia.
      pose proof (stk_release _ _ _ _ _ upto_64 high_m ltac:(lia)) as upto_48. cbn [cells_size csize Nat.add] in upto_48.
      replace (bv_unsigned sp + -64 + Z.of_nat 16) with (bv_unsigned sp + -48) in upto_48 by lia.
      destruct (stk_carve _ _ _ _ 64 upto_48 ltac:(lia)) as [below whole].
      replace (bv_unsigned sp + -48 - Z.of_nat 64) with (bv_unsigned sp + -112) in below, whole by lia.
      exact (conj below whole). }
    zstep.
    if_cases ret_ok.
    - (* the parser accepted the key: consume the rest of the input *)
      do 4 zstep.
      replace (p0 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia).
      if_false.
      do 6 zstep.
      rewrite (pk_lxor_sb (E2 - p)) by lia.
      replace (E2 - p + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (E2 <? p) with false by (symmetry; apply Z.ltb_ge; lia).
      if_false.
      zstep.
      pose proof (munch_refl [(PP, PP + 8)] m2) as mu_3.
      pose proof (wmono_refl usegs m2) as wm_3.
      zstep.
      replace (p + (E2 - p)) with E2 in * by lia.
      zstep. if_true.
      do 2 zstep.
      assert (ctx_3 : pctx' h2 LB2 m3 mo2r).
      { refine (pctx_munch' h2 LB2 m2 m3 mo2r _ ctx_2 mu_3 wm_3 mi_2 _).
        apply Forall_cons; [| apply Forall_nil]. right. left. reflexivity. }
      pose proof ctx_3 as (heap_3 & top_3 & mof_3 & mi_3 & sok_3 & sinv_3 & _ & keep_3).
      destruct (HPERM h2 LB2 (owned ++ LB) m3 mo2r heap_3 perm_2) as (h3 & heap_h3 & top_h3).
      destruct (heap_blocks _ _ HI _ _ _ _ heap_2) as [ranges_2 _].
      assert (rep_3 : pk_rep_c usegs U_RSA_INFO U_EC_INFOS U_MT m3 (owned ++ LB) PKA U_RSA_INFO C owned).
      { apply (pk_rep_c_frame usegs U_RSA_INFO U_EC_INFOS U_MT m2 m3 (owned ++ LB) (owned ++ LB) PKA U_RSA_INFO C owned rep_2 mi_3).
        - intros b b_in. apply in_or_app. left. exact b_in.
        - intros a ([B k] & b_o & b_rng). cbn [fst snd] in b_rng.
          apply owned_spec in b_o as [b_l2 b_nlb].
          pose proof (proj1 (Forall_forall _ _) ranges_2 _ b_l2) as (b_pos & _ & _ & b_ceil & _). cbn [fst snd] in b_pos, b_ceil.
          pose proof (blk_apart_pp L HI DIMG h0 LB PP lo ACL CWPP h2 LB2 m3 mo2r B k heap_2 (fun b b_lb => sup_2 b (or_intror b_lb)) b_l2 b_nlb ltac:(lia)) as b_pp.
          apply mu_3. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
      destruct (frame_fold m3 stk_2 lj_2 oj_2) as [stk_3 [junk lbuf_3]].
      refine (ret_walk' m3 mo2r h3 (owned ++ LB) 0 E2 U_RSA_INFO C owned junk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                heap_h3 _ mof_3 mi_3 sok_3 sinv_3 keep_3 _ pp_2 _ pka_2 rep_3 _ eq_refl lbuf_3 regs_2 stk_3).
      + rewrite top_h3. exact top_3.
      + lia.
      + lia.
      + intros nonzero. exfalso. apply nonzero. reflexivity.
    - (* the parser failed: map its code and free the context *)
      destruct (frame_fold m2 stk_2 lj_2 oj_2) as [stk_x [junk lbuf_2]].
      do 6 zstep.
      if_cases asn1_err.
      + refine (fail_free_walk' m2 mo2r h2 LB2 _ p U_RSA_INFO C owned junk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  ctx_2 perm_2 _ pp_2 _ pka_2 rep_2 lbuf_2 regs_2 stk_x); lia.
      + zify_cond asn1_err.
        do 2 zstep.
        pose proof (rsa_err_map (bv_unsigned a0r) ltac:(pose proof (bv_unsigned_in_range 64 a0r) as a0r_rng; lia) asn1_err) as err_rng.
        refine (fail_free_walk' m2 mo2r h2 LB2 _ p U_RSA_INFO C owned junk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  ctx_2 perm_2 _ pp_2 _ pka_2 rep_2 lbuf_2 regs_2 stk_x); lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.
