(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepPk RepCrt CrtStmts CrtParseStmts SInv PkTmp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_platform_zeroize P_mpi_free P_mpi_addsub P_asn1_sequence_free P_asn1_get_sequence_of_A P_ecp_defs P_ecp_group_load P_ecp_grp_id_list P_ecp_sinv P_pk_sinv P_ecp_keypair_init
     P_pk_wrap_rsa P_pk_wrap_eckey P_pk_free P_pk_type P_pk_setup P_pk_ecc_set_group P_pk_ecc_set_pubkey P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_D P_rsa_parse_pubkey
     P_oid P_oid_pk_alg P_oid_ec_grp P_oid_ec_grp_algid P_pk_info P_ecp_point_read_binary P_ecp_check_pubkey P_ecp_bad_points P_asn1_get_mpi P_pk_parse_A.
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
Ltac2 gd_tbl_P_pk_parse_B () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.P.PImg.psegs"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.ecp_point_read_binary_stmt"; "OSSVerify.KrLib.P.P_ecp_defs.P_MT"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.P_ECP_POINT_READ_BINARY"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.ECP_POINT_READ_STACK"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.ecp_check_pubkey_stmt"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.P_ECP_CHECK_PUBKEY"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.P_BAD_POINTS"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "OSSVerify.KrLib.P.P_pk_parse_A.pctx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.RepRsa.rsa_at"; "OSSVerify.KrLib.Spec.RepRsa.rsa_fresh"; "OSSVerify.KrLib.Lib.HeapIface.block_range"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.P.P_pk_free.P_RSA_INFO"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "OSSVerify.KrLib.Spec.RepPk.PKC_inst"; "OSSVerify.KrLib.P.P_pk_free.P_EC_INFOS"; "OSSVerify.KrLib.P.P_pk_sinv.P_pk_sinv"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].


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

Notation MT := P_MT (only parsing).

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
  Hypothesis HPERM : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_B ()) "Ph,(9.$:.VL,VHI,)PLB,(;.$<.)PLB',(;.$<.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$?.P,(10.$:.VL,VHI,R5.R4.R2.R1.)P,(11.$<.R5.R4.)(12.(9.$:.VL,VHI,)Lh',(9.$:.VL,VHI,)(7.(10.$:.VL,VHI,R1.R6.R5.R4.)(13.$0.(14.$:.VL,VHI,R1.)(14.$:.VL,VHI,R8.))))")
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
  Hypothesis HPRB : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_B ()) "(15.$:.VL,VHI,$16.$17.$18.+598:8.$19.)")
(* [comment removed for export] *).
  Hypothesis HCPK : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_B ()) "(1:.$:.VL,VHI,$16.$1;.$18.+598:8.$1<.$1=.)")
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
  Notation heap_presx_weak'' := (heap_presx_weak' L ra sp LB PP P END BUF PKA bs BP PE EB DPK DKB DPB NZPP NZP).
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.
  #[using="HL"] Lemma IL1 : hl_data_lo L <= P_ECP_IDS_DONE. Proof. exact (proj1 HL). Qed.
  #[using="L HL"] Lemma IL2 : P_ECP_IDS_DONE + 1 <= P_ECP_IDS. Proof. exact (proj1 (proj2 HL)). Qed.
  #[using="HL"] Lemma IL3 : P_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 HL))). Qed.
  #[using="HMC"] Lemma ML1 : hl_data_lo L <= P_MUL_COUNT. Proof. exact (proj1 HMC). Qed.
  #[using="HMC"] Lemma ML2 : P_MUL_COUNT + 8 <= hl_data_hi L. Proof. exact (proj1 (proj2 HMC)). Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01Y0@D10463954377.159D10463954377.160D11805467289.157D11805467289.158D12223852868.159D12223852868.160D15457446739.158D15463825327.160D19120365881.159D34028600543.210D37216054521.208D37226362885.210D41355788639.210D43928033258.157D43934434070.159D44622288685.159D44622288685.160D47139703723.208D49698585326.159D49698585326.160D49705053714.157D49705053714.158D61281570664.210D61556549392.210D61571118060.208D63898547005.210D64111535230.159D64111535230.160D7377275490.160 L10356181826.21 L10360527642.3  L1077460508.1   L11423978205.12 L11886305925.4  L12283411672.144L12283411672.148L12634579262.7  L13345498453.205L14372944785.6  L14948329643.196L15068833967.3  L16824022294.158L1725003874.1   L22052548753.6  L2397676628.0   L24446230945.0  L25584779078.10 L25815444617.6  L26641309430.3  L28009021698.3  L28011049605.143L2831671631.12  L29010380273.147L30522440326.3  L31161809777.143L32029494421.10 L34317004597.2  L34806988770.1  L34994544387.147L3582028444.1   L36660877808.7  L36671363403.3  L37317392303.8  L37335025441.143L37339008021.196L37796632789.0  L40147641242.5  L40228640085.0  L4114706726.1   L41202929119.144L41202929119.198L4125729279.21  L41320204299.10 L41672612599.8  L43058782591.10 L44075892968.12 L4660549440.154 L4709231164.2   L4728363746.1   L47431073244.8  L49728944076.8  L5079168823.0   L51925114228.148L52071584789.143L52225222276.0  L53271535775.198L53506606353.143L56892130782.4  L56904954949.21 L57381525820.21 L57393883303.2  L59314873579.2  L60264566684.1  L61275282840.201L62503018828.8  L62835830358.13 L63455408106.8  L6443869654.3   L65348482612.1  L65361585901.21 L67158371251.147L67819175067.5  L68310574691.1  L7036479304.1   L9114374322.3   00001;02F02d03B04004^05<05f06j07e08R09N0:I0:g0;Q0<]0=i0>Q0??0?m0@O0A10A20Ai0BQ0D20D`0EN0FR0Fc0Fd0Fh0GM0GN0Gi0HD0H\0IA0IT0IU0IV0J10J50JH0JI0JJ0J_0J`0Jh0K20L30LL0Lg0Lo0NU0Nc0Nj0Nn0OI0OM0Og0Oh0PF0Ql0Sd0Se0T30T40T50TP0U50Uh0V@0V\0W>0WZ0X50X<0X@0X[0Xl0Xm0YH0YI0YJ0Yo0ZJ0ZK0[A0\60\70\<0\@0]:0]U0]V0^20^:0^;0^e0_@0_R0_S0_W0_`S1L2HI2ra2sp2h02PP3PKA2bs3SPP3PPT4NZPP3NZP1h1C2HT2C03PKB3PPB2HB5Ha_st5Hl_stS1L2HI2ra2sp2h02PP3PKA2bs3SPP3PPT4NZPP3NZP1h1C2HT2C03PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs3SPP1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPP1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs1C3PKB3PPB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP3PKA2lo2bs4NZPP3NZP1C4SLO'2C03PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPP1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs4NZPP1C2lj3PKB3PPB3kbs2WF2HBS2ra2sp2PP3PKA2bs4NZPP1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPP1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs1C3PKB3PPB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP3PKA2lo2bs3ACL3DHI4NZPP3NZP1C4SLO'2C03PKB3PPB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP3PKA2lo2bs3ACL3DHI4NZPP3NZP1C4SLO'2C03PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WF2HBS2ra2sp2PP3PKA2bs3SPR1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPR1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPR1C3PKB3PPB2HBS2ra2sp2PP3PKA2bs3SPR1C3PKB3PPB2HBFS2ra2sp2PP3PKA2bs1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WF2HBS1L3HLS2ra2sp2PP3PKA2lo2bs3SPP3ACL3DHI4NZPP3NZP1C2E22lj3ACP4SLO'2C03PKB3PPB3kbs2WF2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPK1C3PKB3PPB2HB5Ha_st5Hl_stS2ra2sp2PP3PKA2bs3SPK1C3PKB3PPB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2PP3PKA2lo2bs4NZPP3NZP1C4SLO'2C03PKB3PPB2HB5Ha_st5Hl_stS1L2sp2lo2bs4SLO'FS2spS1P3END3BUF2bs2BP2EB1p2E22PB3E2B1a2HaFS2ra2sp2PP3PKA2bs1C3PKB3PPBS2ra2sp2PP3PKA2bs1C3PKB3PPBS1L1C3CIM2M12M23E1'4E2''S2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WFS1P3END1p2E22PB3E2BFFS2ra2sp2PP3PKA2bs1C3PKB3PPBS2spS1P3END1p2E22PB3E2BSSS1P3BUF2bs2BP1p2E22PBFS2PP1C1QS1C2C03C64S1L3HLS2ra2sp2PP3PKA2lo2bs3SPK3ACL4NZPP3NZP1C4SLO'2C03CAC3PKB3PPBS1P3BUF2bs2BP1C1p2E22PB1QS2ra2sp2PP3PKA2bs1C3PKB3PPBS2PP1C1QS1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22PB3E2B3ACP3BAC4SLO'2C03PKB3PPBS1P2bs1p2E22PBS2x42XRS2spS2ra2sp2PP3PKA2bs1C3PKB3PPBS2spS1L3HLS2sp2lo3ACL3ACP4SLO'FS1L3HLS2sp2lo3ACL3SPR3ACP4SLO'S1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22PB3E2B3ACP3BAC4SLO'2C03PKB3PPBS1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1C1p2E22lj2PB3E2B3ACP3BAC4SLO'2C03PKB3PPB3kbs4LENK2WF2KESS1L2M12M21a2HaSFS2ra2sp2PP3PKA2bs1C3PKB3PPBS2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WFS1L3HLS2sp1P3BUF2lo2bs2BP4BUF03ACL1p2E22PB3BAC4SLO'S3END3BUF2bs2EB1p2E23E2BS1L3HLS2sp2lo3ACL1C4SLO'3CACS1L3HLS2sp2PP2lo3SPP3ACL4SLO'1d2PcS3END3BUF2bs2EB1C1p2E23E2B1QS2ra2sp2PP3PKA2bs1C3PKB3PPBS2lj2WFS2spS1L1C3CIM2I12I22I33E1'4E2''S1L2HI2sp2h04HTOPSS2ra2sp2PP3PKA2bs1C3PKB3PPBFSS2ra2sp2PP3PKA2bs1C2lj3PKB3PPB3kbs2WFS2ra2sp2PP3PKA2bs1C3PKB3PPBFS1L3HLS2sp3END3BUF2lo2bs2EB4BUF03ACL1p2E23E2B3BAC4SLO'S1L3HLS2sp3END3BUF2lo2bs2EB3B633ACL1p2E23E2B3BAC4SLO'FS1C1HS2spS2ra2sp2PP3PKA2bs1C2E22lj3PKB3PPB3kbs2WF2HB5Ha_st5Hl_st2HDS1L1C3CIM2I12I22I33E1'4E2''FS1L3HLS2sp2lo3ACL1C4SLO'3CACS2sp3SPAFS1L3HLS2sp3BUF2lo2bs4BUF03ACL3SPA3BAC4SLO'S2ra2sp2PP3PKA2bs1C3PKB3PPBS1L3HLS2sp2lo4SLO'FS2spS3PKA1C1Q". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND HPERM CA_MSF CA_RSA0 CA_RSA80 CA_EC0 CA_EC80 BUF bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP PPT SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR"] Lemma rsa_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_B ()) "Pm,P,(=.&40.)(>.(=.&8.))Pmo,$?.Ph,(9.$:.VL,VHI,)PC,$0.Pp,$0.PE2,$0.Papw,(=.&40.)Palen,(=.&40.)Poj,(;.(=.&8.))Plj,(;.(=.&8.))Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px19,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(1>.VL,VHI,Vsp,Vm0,Vmo0,Vh0,VLB,VPP,VPKA,R19.(1?.(20.$0.$0.)(21.$0.$0.R18.+>8.)VLB,)R1;.R1:.)P,(22.$:.R1<.(1?.(20.$0.$0.)(21.$0.$0.R19.+>8.)VLB,)R19.(23.R19.))P,(24.VL,R1:.+>8.)P,PB,$0.Pk,$0.P,(25.(20.$0.$0.)(21.$0.$0.R2.R1.)VLB,)(26.(1.(5.R1>.+>8.)R3.)(1.(5.R3.R2.)R1>.))P,(27.$:.R1?.VPP,(1?.$28.(29.(2:.&40.R1;.))(2;.$28.)))P,(7.(1.VP,R1<.)(1.R1<.R1;.))P,(1.R1<.VEND,)P,(27.$:.R22.VPKA,(1?.$28.(29.(2:.&40.$2<.))(1?.$28.(29.(2:.&40.R1?.))(2;.$28.))))P,(27.$:.R23.(5.(2=.&40.Vsp,)-70.)(1?.$28.(2>.#30.R1:.)(2;.$28.)))P,(27.$:.R24.(5.(2=.&40.Vsp,)-40.)(1?.$28.(2>.#8.R1<.)(1?.$28.(29.R1=.)(1?.$28.(29.R1>.)(2;.$28.)))))P,(27.$:.R25.(5.(2=.&40.Vsp,)-28.)(1?.$28.(29.Vs3,)(1?.$28.(29.Vs2,)(1?.$28.(29.Vs1,)(1?.$28.(29.Vs0,)(1?.$28.(29.Vra,)(2;.$28.)))))))P,(2?.$:.R26.Vlo,(5.(2=.&40.Vsp,)-70.))(30.$:.R26.(31.$:.VL,VHI,(32.$:.$2<.$33.$16.)(34.VL,VHL,VHMC,)Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPP,VP,VEND,VPKA,Vlo,Vm0,Vmo0,)(35.(36.R1=.(2:.&40.(5.(2=.&40.Vsp,)-70.))Vgp,Vtp,R1<.R1;.R1:.(2:.&40.VPKA,)(2:.&40.VPP,)R19.R18.R17.R16.R15.R14.R13.R12.(2:.&40.R22.)R11.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(2:.&40.+273;0.)Vfc,(37.(=.&40.))R27.(38.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX RSA0 BRC APC HPP PB E2B HPKA FRL FRO FR ST.
    dpose pa_basics' as (ACP & BAC & BIM & PPD & PKD & SLO').
    dpose CX as (HH & HT & MF & MI & SOK & SIP & SUB & PX). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    dpose BRC as (C0 & C16 & _ & CAC & CIM).
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB.
    pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. cbn [cells_size csize Nat.add] in PPB.
    (* [comment removed for export] *)
    pose proof (conj MI I) as MIbox.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp + -48)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with M : mem_inv psegs m1 |- _ => rename M into MI1 end. match goal with W : wmono psegs m m1 |- _ => rename W into WM1 end.
    pose proof (pctx_munch' _ _ _ _ _ _ CX MU WM1 MI1 ltac:(constructor; [cbn; left; clear -SLO' HLS; lia| constructor])) as CX1.
    assert (RSA1 : rsa_at psegs m1 ((C, 232) :: LB) C (rsa_fresh C)).
    { eapply rsa_at_munch; [exact RSA0| exact MU| exact WM1| exact (proj1 MIbox)| exact MI1| cbn [disjoint_from]; clear -CAC ACL SLO' HLS; lia|].
      cbn. intros d Hd HO. exfalso. decompose [or] Hd; try contradiction; subst d; cbn in HO; discriminate. }
    clear MU WM1 CX RSA0 MIbox. dpose CX1 as (HH1 & _ & _ & _ & SOK1 & _). clear HH HT MF SIP SUB PX. try clear SOK.
    (* [comment removed for export] *)
    match goal with H : rw_cells psegs m1 (bv_unsigned sp + -64) _ |- _ => rename H into FRO1 end.
    pose proof (P_pk_get_type_spec L CA_RSA0 CA_EC0) as SPT. unfold pk_get_type_stmt, pk_get_type_post, P_PK_GET_TYPE in SPT.
    zstep. zstep.
    chunk_split FRO1 2%nat FROa FROb.
    acallp (eapply SPT with (A := bv_unsigned sp + -64) (info := P_RSA_INFO); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by (clear -SLO' HLS SPR; lia);
           first [exact FROa| exact MI1| exact SOK1| reflexivity| right; left; reflexivity| clear -SPA SPR; lia| clear -SLO' HLS ACL ACP; lia
                 | match goal with |- ?g => idtac "PTLEFT" g end]).
    match goal with H : P_RSA_INFO = P_RSA_INFO -> ?t = 1 |- _ => pose proof (H eq_refl) as TY; clear H; subst t end.
    repeat match goal with H : _ -> _ = _ |- _ => clear H | H : _ -> _ <= _ <= _ |- _ => clear H end.
    chunk_join FROa FROb FRO1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    dpose RSA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C64 & _). unfold RSA_CTX_SIZE in C64.
    (* [comment removed for export] *)
    pose proof (pctx_bytes' _ _ _ _ CX1) as HBS1.
    set (kbs := firstn (Z.to_nat (E2 - p)) (skipn (Z.to_nat (p - BUF)) bs)).
    assert (LENK : Z.of_nat (length kbs) = E2 - p) by (subst kbs; apply P_asn1_get_mpi.bytes_at_sub_length; clear -PB E2B BP EB; lia).
    assert (HKB : bytes_at psegs m1 p kbs) by (subst kbs; eapply P_asn1_get_mpi.bytes_at_sub; [exact HBS1| | |]; clear -PB E2B BP EB; lia).
    clearbody kbs.
    dpose CX1 as (_ & HT1 & MF1 & _ & _ & SIP1 & SUB1 & PX1).
    pose proof (P_rsa_parse_pubkey_spec L HI HFREE HCALLOC HLS SW DIMG HND _ eq_refl) as SRP. unfold rsa_parse_pubkey_stmt, rsa_parse_pubkey_post, P_RSA_PARSE_PUBKEY in SRP.
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
    match goal with H : rw_cells psegs m1 PP _ |- _ =>
      apply (keep_pp' ((C, 232) :: LB) _ _ m1 m2 _ PX2 ltac:(intros b Hb; right; exact Hb) ltac:(clear; lia)) in H; [| reflexivity| cbn; pose proof (fresh_apart_pp' C 232 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]]; rename H into HPP2 end.
    match goal with H : rw_cells psegs m1 PKA _ |- _ =>
      apply (keep_pka' ((C, 232) :: LB) _ _ m1 m2 _ PX2 ltac:(intros b Hb; right; exact Hb) ltac:(clear; lia)) in H; [| reflexivity| cbn; pose proof (fresh_apart_pka' C 232 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]]; rename H into HPKA2 end.
    (* [comment removed for export] *)
    assert (CX2 : pctx' h2 LB2 m2 mo2).
    { split; [exact HH2|]. split; [rewrite HT2; exact HT1|]. split; [eapply mo_frame_trans; [exact MF1| exact MF2]|]. split; [exact MI2|]. split; [exact SOK2|].
      split. { destruct SIP1 as [IDS1 [cnt RC1]]. pose proof IL1 as I1; pose proof IL2 as I2; pose proof IL3 as I3; pose proof ML1 as M1; pose proof ML2 as M2; pose proof DI1 as E1'; pose proof DI2 as E2''. split.
               - apply (ecp_ids_state_presx psegs L _ _ _ _ _ m1 m2 IDS1 PX2 HL); cbn; clear -CIM I1 I2 I3 E1' E2''; (split; [lia| exact I]).
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
    assert (REPm : forall mx, mem_inv psegs mx -> rsa_at psegs mx LB2 C r' -> pk_rep_c psegs P_RSA_INFO P_EC_INFOS MT mx (owned ++ LB) PKA P_RSA_INFO C owned).
    { (intros mx MIx dd_H; ddestruct dd_H as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QALL & Q9 & Q10 & Q11 & QIN & Q13 & Q14 & Q15)).
      right; left. split; [reflexivity|]. split; [unfold P_RSA_INFO; clear; lia|]. split; [exact MIx|].
      exists r'. split; [| intros b'; subst owned; split; intros Hx; exact Hx].
      refine (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj _ (conj Q9 (conj Q10 (conj Q11 (conj (INP _ QIN) (conj Q13 (conj Q14 Q15)))))))))))))).
      apply Forall_forall. intros d Hd. eapply mpdr_at_LB_mono; [exact (proj1 (Forall_forall _ _) QALL d Hd)| exact INP]. }
    (* [comment removed for export] *)
    pose proof FRL as [[WF _] _]. cbn in WF.
    lazymatch type of FRO1 with rw_cells _ _ _ [C8 ?w1; C8 ?w2; C8 _] => set (wi := w1) in FRO1; set (wc := w2) in FRO1; clearbody wi wc end.
    chunk_join FRL FRO1 FRJ.
    eapply rw_cells_reshape with (cs' := [CB 72 (lj ++ le8 wi ++ le8 wc ++ le8 apw)]) in FRJ;
      [| cbn; rewrite ?app_length, ?length_le8; cbn; split; [clear -WF; lia| exact I]| cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity].
    clearbody owned.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      pose proof (conj MI2 (conj HH2 I)) as BOX2. clear HH2.
      pose proof (munch_refl [(PP, PP + 8)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with M : mem_inv psegs m3 |- _ => rename M into MI3 end. match goal with W : wmono psegs m2 m3 |- _ => rename W into WM3 end.
      pose proof (pctx_munch' _ _ _ _ _ _ CX2 MU WM3 MI3 ltac:(constructor; [cbn; right; left; reflexivity| constructor])) as CX3.
      assert (RSA3 : rsa_at psegs m3 LB2 C r').
      { eapply rsa_at_munch; [exact RSA2| exact MU| exact WM3| exact (proj1 BOX2)| exact MI3| cbn [disjoint_from]; pose proof (fresh_apart_pp' C 232 BRC APC ltac:(clear; lia)) as Q; split; [clear -Q; lia| exact I]|].
        intros d Hd HO. destruct (heap_blocks _ _ HI _ _ _ _ (proj1 (proj2 BOX2))) as [HBR2 _].
        rewrite Forall_forall in ALL2. pose proof (ALL2 d Hd) as MDd.
        destruct (mpdr_blk_facts psegs L _ _ _ MDd HO HBR2) as (HIn & _ & _ & Pc & _).
        cbn. split; [| exact I]. clear -Pc ACL SLO' HLS SPP. left. lia. }
      clear MU WM3 CX2 RSA2 BOX2.
      zstep. if_cases KE; zify_cond KE. 2:{ exfalso. apply KE. reflexivity. }
      zstep. zstep.
      dpose CX3 as (HH3 & HT3 & MF3 & _ & SOK3 & SIP3 & SUB3 & PX3).
      destruct (HPERM _ _ _ _ _ HH3 PERM) as (h4 & HH4 & HT4).
      match goal with H : rw_cells psegs m3 PP _ |- _ => rename H into HPP3 end.
      eapply ret_walk' with (owned := owned) (info := P_RSA_INFO) (ctx := C) (h := h4) (p' := E2);
        [ exact HH4 | rewrite HT4; exact HT3 | exact MF3 | exact MI3 | exact SOK3 | exact SIP3 | exact PX3 | clear; lia | exact HPP3 | clear -PB E2B; lia
        | exact HPKA2 | exact (REPm m3 MI3 RSA3) | intros NZ; exfalso; apply NZ; reflexivity | reflexivity | exact FRJ | exact FR | exact ST2 ].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases KG; zify_cond KG.
      + (* [comment removed for export] *)
        eapply fail_free_walk' with (owned := owned) (info := P_RSA_INFO) (ctx := C);
          [ exact CX2 | exact PERM | clear; lia | exact HPP2 | clear -PB E2B; lia | exact HPKA2 | exact (REPm m2 MI2 RSA2) | exact FRJ | exact FR | exact ST2 ].
      + (* [comment removed for export] *)
        zstep. zstep.
        lazymatch type of KG with context [bv_swrap 32 (bv_unsigned ?xw + 108)] =>
          pose proof (bv_unsigned_in_range 64 xw) as XR;
          pose proof (rsa_err_map (bv_unsigned xw) ltac:(clear -XR; lia) KG) as RRm end.
        eapply fail_free_walk' with (owned := owned) (info := P_RSA_INFO) (ctx := C);
          [ exact CX2 | exact PERM | exact RRm | exact HPP2 | clear -PB E2B; lia | exact HPKA2 | exact (REPm m2 MI2 RSA2) | exact FRJ | exact FR | exact ST2 ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.
