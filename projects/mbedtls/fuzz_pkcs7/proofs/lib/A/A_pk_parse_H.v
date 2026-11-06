(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface Arr Statics.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StreamSim StoreOk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepPk RepCrt CrtStmts SInv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_ecp_check_pubkey P_ecp_grp_id_list P_ecp_sinv P_pk_sinv P_ecp_bad_points.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_asn1_get_tag_stmt A_asn1_get_alg_A A_oid A_oid_pk_alg A_oid_ec_grp_algid
     A_asn1_get_bitstring_null A_pk_defs A_pk_info A_pk_type A_mpi_stmtA A_mpi_stmtA_sz A_mpi_read_binary_stmt A_ecp_stmtA A_ecp_defs A_ecp_grp_id_list A_ecp_grp_facts A_ecp_check_pubkey_c24
     A_crt_stmts A_crt_parse_stmts A_pk_setup A_rsa_parse_pubkey A_rsa_parse_pubkey_c24 A_pk_ecc_set_group A_pk_ecc_set_pubkey A_pk_ecparams_stmt A_pk_free A_pk_parse_stmt
     A_pk_parse_A A_pk_parse_B A_pk_parse_C A_pk_parse_D A_pk_parse_E A_pk_parse_F A_pk_parse_G0 A_pk_parse_G.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_pk_parse_H () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.BB.StreamSim.wseg_ok"; "OSSVerify.KrLib.A.AImg.asegs"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Statics.img_bytes_b"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.ecp_ids_state"; "OSSVerify.KrLib.A.A_ecp_grp_id_list.A_ECP_IDS_DONE"; "OSSVerify.KrLib.A.A_ecp_grp_id_list.A_ECP_IDS"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.A.A_ecp_stmtA.A_MUL_COUNT"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Spec.SInv.si_fp"; "Inst.A_pk_sinv"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.A.AImgRT.asan_rtc"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.bad_point_ok"; "OSSVerify.KrLib.A.A_ecp_check_pubkey_c24.A_BAD_POINTS"; "A_bp1"; "A_bp2"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mpd_imgA"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.Spec.RepEcp.modp_ent"; "OSSVerify.KrLib.P.P_ecp_sinv.ecp_ids_lok"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.P.P_pk_sinv.mc_lok"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.arl_uar_got"; "OSSVerify.KrLib.A.A_pk_parse_A.A_UAR_GOT_PK"; "OSSVerify.KrLib.LibA.ARt.arl_smalloc"; "OSSVerify.KrLib.A.A_pk_parse_A.A_SMALLOC_2_PK"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.A.A_pk_parse_C.A_AMEMSET_PK"; "OSSVerify.KrLib.LibA.ARt.arl_need_smalloc"; "OSSVerify.KrLib.LibA.ARt.arl_need_amem"; "OSSVerify.KrLib.LibA.ARt.arl_need_bcmp"; "OSSVerify.KrLib.LibA.ARt.arl_need_malloc"; "OSSVerify.KrLib.LibA.ARt.arl_rtc"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.LibA.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Stdlib.Sorting.Permutation.Permutation"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.A.A_asn1_get_tag_stmt.asn1_get_tag_stmtA"; "OSSVerify.KrLib.A.A_pk_parse_C.A_ASN1_GET_TAG_PK"; "OSSVerify.KrLib.A.A_asn1_get_alg_A.asn1_get_alg_stmtA"; "OSSVerify.KrLib.A.A_pk_parse_C.A_ASN1_GET_ALG_PK"; "OSSVerify.KrLib.A.A_oid.oid_lookup1_stmtA"; "OSSVerify.KrLib.A.A_oid_pk_alg.A_OID_GET_PK_ALG"; "OSSVerify.KrLib.A.A_oid_ec_grp_algid.A_OID_GET_EC_GRP_ALGID"; "OSSVerify.KrLib.A.A_asn1_get_bitstring_null.asn1_get_bitstring_null_stmtA"; "OSSVerify.KrLib.A.A_asn1_get_bitstring_null.A_ASN1_GET_BITSTRING_NULL"; "OSSVerify.KrLib.A.A_pk_setup.pk_setup_stmtA"; "OSSVerify.KrLib.A.A_pk_defs.A_RSA_INFO"; "OSSVerify.KrLib.A.A_pk_defs.A_EC_INFOS"; "OSSVerify.KrLib.A.A_pk_parse_D.A_PK_SETUP_PK"; "OSSVerify.KrLib.A.A_rsa_parse_pubkey_c24.rsa_parse_pubkey_stmtA_c"; "OSSVerify.KrLib.A.A_rsa_parse_pubkey.A_RSA_PARSE_PUBKEY"; "OSSVerify.KrLib.A.A_pk_ecparams_stmt.pk_use_ecparams_stmtA"; "OSSVerify.KrLib.A.A_ecp_defs.A_CA"; "OSSVerify.KrLib.A.A_ecp_defs.A_ONE"; "OSSVerify.KrLib.A.A_pk_ecparams_stmt.A_PK_USE_ECPARAMS"; "OSSVerify.KrLib.A.A_pk_ecc_set_group.pk_ecc_set_group_stmtA"; "OSSVerify.KrLib.A.A_pk_ecc_set_group.A_PK_ECC_SET_GROUP"; "OSSVerify.KrLib.A.A_pk_ecc_set_pubkey.pk_ecc_set_pubkey_stmtA"; "OSSVerify.KrLib.A.A_pk_ecc_set_pubkey.A_PK_ECC_SET_PUBKEY"; "OSSVerify.KrLib.A.A_crt_stmts.pk_free_stmtA"; "OSSVerify.KrLib.A.A_pk_free.PKA_inst"; "OSSVerify.KrLib.A.A_pk_free.PHIpk"; "OSSVerify.KrLib.A.A_pk_free.FFRpk"; "OSSVerify.KrLib.A.A_pk_free.STKpk"; "OSSVerify.KrLib.A.A_pk_free.A_PK_FREE"; "OSSVerify.KrLib.A.A_pk_parse_stmt.pk_parse_subpubkey_stmtA"; "A_pk_sinv"; "OSSVerify.KrLib.A.A_pk_parse_G0.PKP_PHI"; "OSSVerify.KrLib.A.A_pk_parse_G0.PKP_FFR"; "OSSVerify.KrLib.A.A_pk_parse_G0.PKP_CNT"; "OSSVerify.KrLib.A.A_pk_parse_G0.PKP_STK"; "OSSVerify.KrLib.A.A_pk_parse_G0.PKP_C24"; "OSSVerify.KrLib.A.A_pk_parse_A.A_PK_PARSE_SUBPUBKEY"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma A_wseg_638 : wseg_ok asegs (Z_to_bv 64 0x638300) 4096%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma A_wseg_ee : wseg_ok asegs (Z_to_bv 64 0xee300) 4096%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma A_page_rw_cells : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_H ()) "Ppage,$0.Pm,Px,(1.&40.)(2.(1.&8.))PA,$0.Pbs,(3.(1.&8.))P,(4.$5.(6.$7.(8.&40.R4.)#1000.)$9.)P,(:.=R5.)P,(:.(;.R6.+1000.)(<.+2.+40.))P,(4.$5.(=.$7.R5.R4.)$9.)P,(:.R8.R6.)P,(:.(;.R7.(>.(?.(1.&8.)R6.)))(;.R9.+1000.))P,Pa,$0.P,(10.(:.R9.R1.)(11.R1.(;.R9.(>.(?.(1.&8.)R8.)))))(4.(2.(1.&8.))A1.R;.(12.R2.)(13.(1.&8.)))(14.$7.R:.R9.(15.$16.(17.(?.(1.&8.)R8.)R8.)(18.$16.)))")
(* [comment removed for export] *).
Proof.
  intros page m A bs WS P0 P1 IB LO HI NONE.
  pose proof (pristine_cells asegs A (A + Z.of_nat (length bs)) (fun _ => False) m A bs
                ltac:(split; [lia|]; split; [lia|]; intros a Ha _; exact (NONE a Ha)) IB ltac:(lia) ltac:(lia) ltac:(intros a _ F; exact F)) as [WF BA].
  split; [exact (conj WF BA)|]. cbn [cells_size csize Nat.add].
  split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (store_ok_window asegs m (Z_to_bv 64 page) (Z_to_bv 64 A) 4096%nat (length bs) page (page + 4096)
                ltac:(rewrite unsigned_lit by lia; reflexivity) ltac:(lia) ltac:(lia) WS ltac:(rewrite unsigned_lit by lia; lia) ltac:(rewrite unsigned_lit by lia; lia)) as SOK.
  pose proof (store_ok_wview asegs m (Z_to_bv 64 A) (length bs) (Z.to_nat i) SOK ltac:(lia)) as W.
  rewrite unsigned_lit in W by lia. rewrite Z2Nat.id in W by lia. exact W.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_pk_sinv_P (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_H ()) "(10.(19.$7.$1:.$1;.O1.)(1<.(1.&40.)Lcnt,(1.&40.)(14.$7.O1.$1=.(15.$16.(1>.R1.)(18.$16.)))))")
(* [comment removed for export] *).

Section Inst.
  Variable L : heap_layout.
  Hypothesis HL : ecp_ids_lok L A_ECP_IDS_DONE A_ECP_IDS.
  Hypothesis HM : mc_lok L A_MUL_COUNT.

  Definition A_pk_sinv : sinv L.
  Proof.
    refine (mkSI L A_pk_sinv_P
                  [(A_ECP_IDS_DONE, A_ECP_IDS_DONE + 1); (A_ECP_IDS, A_ECP_IDS + 56); (A_MUL_COUNT, A_MUL_COUNT + 8)] _ _ _ _).
    - (* [comment removed for export] *)
      (intros m m' dd_H; ddestruct dd_H as [(b & bs & R1 & R2 & IMP) (cnt & RC)]; intros AG). split; [dexists b, bs; split; [| split; [| exact IMP]]| exists cnt].
      + eapply rw_cells_agree'; [exact R1|]. cbn [cells_size csize Nat.add]. intros a Ha. apply AG; [unfold A_ECP_IDS_DONE in Ha; lia|].
        cbn. intros [H _]. apply H. lia.
      + pose proof R2 as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
        eapply rw_cells_agree'; [exact R2|]. cbn [cells_size csize Nat.add]. intros a Ha. apply AG; [unfold A_ECP_IDS in Ha; lia|].
        cbn. (intros dd_H; ddestruct dd_H as (_ & H & _)). apply H. lia.
      + eapply rw_cells_agree'; [exact RC|]. cbn [cells_size csize Nat.add]. intros a Ha. apply AG; [unfold A_MUL_COUNT in Ha; lia|].
        cbn. (intros dd_H; ddestruct dd_H as (_ & _ & H & _)). apply H. lia.
    - (* [comment removed for export] *)
      intros m NONE. split; [dexists (Z_to_bv 8 0), (repeat (Z_to_bv 8 0) 56); split; [| split]| exists (Z_to_bv 64 0)].
      + apply (A_page_rw_cells 0x638300 m A_ECP_IDS_DONE [Z_to_bv 8 0] A_wseg_638); [clear; lia| clear; lia| vm_compute; reflexivity| unfold A_ECP_IDS_DONE; lia| unfold A_ECP_IDS_DONE; cbn; lia|].
        intros a Ha. apply NONE; [unfold A_ECP_IDS_DONE in Ha; cbn in Ha; lia|]. cbn. intros [H _]. apply H. cbn in Ha. lia.
      + apply (A_page_rw_cells 0x638300 m A_ECP_IDS (repeat (Z_to_bv 8 0) 56) A_wseg_638); [clear; lia| clear; lia| vm_compute; reflexivity| unfold A_ECP_IDS; lia| unfold A_ECP_IDS; cbn; lia|].
        intros a Ha. apply NONE; [unfold A_ECP_IDS in Ha; cbn in Ha; lia|]. cbn. (intros dd_H; ddestruct dd_H as (_ & H & _)). apply H. cbn in Ha. lia.
      + intros NZ. exfalso. apply NZ. reflexivity.
      + pose proof (A_page_rw_cells 0x638300 m A_MUL_COUNT (repeat (Z_to_bv 8 0) 8) A_wseg_638 ltac:(clear; lia) ltac:(clear; lia) ltac:(vm_compute; reflexivity)
                      ltac:(unfold A_MUL_COUNT; lia) ltac:(unfold A_MUL_COUNT; cbn; lia)
                      ltac:(intros a Ha; apply NONE; [unfold A_MUL_COUNT in Ha; cbn in Ha; lia|]; cbn; (intros dd_H; ddestruct dd_H as (_ & _ & H & _)); apply H; cbn in Ha; lia)) as RCx.
        cbn [length repeat] in RCx. cb8_to_c8 RCx ([] : list cell).
        replace (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with (Z_to_bv 64 0) in RCx by (vm_compute; reflexivity). exact RCx.
    - (* [comment removed for export] *)
      intros a NO. ddestruct HL as (D1 & D2 & D3 & D4). ddestruct HM as (M1 & M2 & M3). cbn in NO.
      assert (IN : (A_ECP_IDS_DONE <= a < A_ECP_IDS_DONE + 1 \/ A_ECP_IDS <= a < A_ECP_IDS + 56) \/ A_MUL_COUNT <= a < A_MUL_COUNT + 8)
        by (clear -NO; unfold A_ECP_IDS_DONE, A_ECP_IDS, A_MUL_COUNT in *; lia).
      destruct IN as [IN|IN]; [destruct (D4 a IN) as [W NS]| destruct (M3 a IN) as [W NS]]; (split; [unfold A_ECP_IDS_DONE, A_ECP_IDS, A_MUL_COUNT in *; lia| split; [exact W| exact NS]]).
    - (* [comment removed for export] *)
      repeat constructor; cbn; unfold A_ECP_IDS_DONE, A_ECP_IDS, A_MUL_COUNT; lia.
  Defined.

    #[using="Type"] Lemma A_pk_sinv_fp : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_H ()) "(4.(3.$1?.)(20.VL,$21.)(15.(22.$0.$0.)(23.$0.$0.$1:.(;.$1:.+1.))(15.(22.$0.$0.)(23.$0.$0.$1;.(;.$1;.+38.))(15.(22.$0.$0.)(23.$0.$0.$1=.(;.$1=.+8.))(18.(22.$0.$0.))))))")
(* [comment removed for export] *).
  Proof. reflexivity. Qed.
End Inst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_BAD1_LIMBS : Z := 0x26fe0.
Definition A_BAD2_LIMBS : Z := 0x27020.
Definition A_bp1 : mpd := smpd A_BAD_POINTS A_BAD1_LIMBS bad1_limbs (Z_to_bv 64 0).
Definition A_bp2 : mpd := smpd (A_BAD_POINTS + 32) A_BAD2_LIMBS bad2_limbs (Z_to_bv 64 0).

Lemma A_bad_points_ok : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_H ()) "PLB,(3.$24.)Pm,P,(1.&40.)(2.(1.&8.))P,(25.R1.)P,(26.$7.R2.)(10.(27.$7.R3.R4.$28.$29.)(10.(27.$7.R3.R4.(;.$28.+20.)$2:.)(10.(2;.$29.)(2;.$2:.))))")
(* [comment removed for export] *).
Proof.
  intros LB m [_ PR] MI. unfold A_bp1, A_bp2, A_BAD1_LIMBS, A_BAD2_LIMBS, A_BAD_POINTS in *.
  assert (S1 : static_limbs asegs m 0x26fe0 bad1_limbs) by (apply static_limbs_image; [exact MI| vm_compute; reflexivity| reflexivity| reflexivity| vm_compute; discriminate| cbn; lia]).
  assert (S2 : static_limbs asegs m 0x27020 bad2_limbs) by (apply static_limbs_image; [exact MI| vm_compute; reflexivity| reflexivity| reflexivity| vm_compute; discriminate| cbn; lia]).
  set (bs1 := map (Z_to_bv 8) [0xe0; 0x6f; 2; 0; 0; 0; 0; 0; 1; 0; 8; 0; 0; 0; 0; 0]).
  set (bs2 := map (Z_to_bv 8) [0x20; 0x70; 2; 0; 0; 0; 0; 0; 1; 0; 8; 0; 0; 0; 0; 0]).
  assert (NONE : forall a, 0xef080 <= a < 0xef080 + 48 -> m (wa a) = None).
  { intros a Ha. apply PR. unfold rtc_prist. eapply (in_ranges_b_sound rtc_pristine 0xef080 (0xef080 + 48)); [vm_compute; reflexivity| exact Ha]. }
  assert (C1 : rw_cells asegs m 0xef080 [CB 16 bs1]).
  { apply (A_page_rw_cells 0xee300 m 0xef080 bs1 A_wseg_ee); [clear; lia| clear; lia| vm_compute; reflexivity| clear; lia| cbn; clear; lia|]. intros a Ha. apply NONE. cbn in Ha. lia. }
  assert (C2 : rw_cells asegs m (0xef080 + 32) [CB 16 bs2]).
  { apply (A_page_rw_cells 0xee300 m (0xef080 + 32) bs2 A_wseg_ee); [clear; lia| clear; lia| vm_compute; reflexivity| clear; lia| cbn; clear; lia|]. intros a Ha. apply NONE. cbn in Ha. lia. }
  apply mpi_cells_of_bytes in C1. apply mpi_cells_of_bytes in C2.
  match type of C1 with rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' in C1 end.
  match type of C2 with rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' in C2 end.
  split; [| split; [| split]].
  - split; [| split; [reflexivity| split; reflexivity]]. split; [| left; reflexivity].
    apply smpd_at; [| reflexivity| reflexivity| exact S1].
    match goal with |- rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' end. exact C1.
  - split; [| split; [reflexivity| split; reflexivity]]. split; [| left; reflexivity].
    apply smpd_at; [| reflexivity| reflexivity| exact S2].
    match goal with |- rw_cells _ _ _ ?c => let c' := eval vm_compute in c in change c with c' end. exact C2.
  - intros _. vm_compute. reflexivity.
  - intros _. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fr_nonneg :=
  unfold check_pubkey_FRn, pk_set_pubkey_FR, point_read_FRn, derive_y_FRn, sw_rhs_FRn, mm_FRn, mul_mpi_FRn, red_FRn, mod_mpi_FRn, intop_FRn, addsub_FRn, exp_mod_FRn,
         pk_ecparams_FR, A_ecp_group_free.GF_FR, group_load_FRn, MPI_RB_FR, pk_set_group_FR;
  repeat first [ apply Z.add_nonneg_nonneg | apply Z.mul_nonneg_nonneg | apply calls_FR_nonneg ];
  first [ (unfold fr_charge; lia) | (vm_compute; intros K; discriminate K) ].

Lemma pkp_FRE0 : forall d, 0 <= d -> 0 <= pk_ecparams_FR (d + 1).
Proof. intros d Hd. fr_nonneg. Qed.
Lemma pkp_FRS0 : forall d, 0 <= d -> 0 <= pk_set_pubkey_FR ECP_MAX_N (d + 1).
Proof. intros d Hd. fr_nonneg. Qed.
Lemma pkp_CKF0 : forall d, 0 <= d -> 0 <= check_pubkey_FRn (ecp_dy_sz ECP_MAX_N) (d + 1).
Proof. intros d Hd. fr_nonneg. Qed.
Lemma pkp_CKP0 : 0 <= check_pubkey_PHIn (ecp_dy_sz ECP_MAX_N).
Proof. vm_compute. intros K. discriminate K. Qed.
Lemma pkp_DY0 : 0 <= derive_y_PHIn ECP_MAX_N.
Proof. vm_compute. intros K. discriminate K. Qed.
Lemma pkp_PHS0 : forall n, 0 <= n -> 0 <= pk_set_pubkey_PHI ECP_MAX_N n.
Proof.
  intros n Hn. pose proof pkp_CKP0. pose proof pkp_DY0.
  unfold pk_set_pubkey_PHI, point_read_PHIn, MPI_RB_PHI, grow_PHI, AVOL_CALL. lia.
Qed.
Lemma pkp_PHIM : forall a b, a <= b -> pk_set_pubkey_PHI ECP_MAX_N a <= pk_set_pubkey_PHI ECP_MAX_N b.
Proof. intros a b H. unfold pk_set_pubkey_PHI, point_read_PHIn, MPI_RB_PHI. lia. Qed.
Lemma pkp_PHE0 : forall n, 0 <= n -> 0 <= pk_ecparams_PHI n.
Proof.
  intros n Hn. unfold pk_ecparams_PHI, MPI_RB_PHI, grow_PHI, A_ecp_group_free.GF_PHI, group_load_PHI, pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL. lia.
Qed.
Lemma pkp_PHIME : forall a b, a <= b -> pk_ecparams_PHI a <= pk_ecparams_PHI b.
Proof. intros a b H. unfold pk_ecparams_PHI, MPI_RB_PHI. lia. Qed.

(* [comment removed for export] *)
Lemma PKP_PHI0 : forall a, 0 <= a -> 0 <= PKP_PHI a.
Proof.
  intros a Ha. pose proof (pkp_PHE0 a Ha). pose proof (pkp_PHS0 a Ha).
  unfold PKP_PHI, PK_SETUP_PHI, A_pk_wrap_alloc.ECKEY_ALLOC_WRAP_PHI, RSA_PP_PHI, MPI_RB_PHI, pk_set_group_PHI, group_load_PHI, grow_PHI, PHIpk, AVOL_CALL. lia.
Qed.
Lemma PKP_PHI_mono : forall a b, 0 <= a <= b -> PKP_PHI a <= PKP_PHI b.
Proof.
  intros a b H. pose proof (pkp_PHIME a b ltac:(lia)). pose proof (pkp_PHIM a b ltac:(lia)).
  unfold PKP_PHI, RSA_PP_PHI, MPI_RB_PHI. lia.
Qed.
Lemma PKP_FFR0 : forall a e, 0 <= a -> 0 <= PKP_FFR a e.
Proof. intros a e _. unfold PKP_FFR, RSA_PP_FR, MPI_RB_FR, pk_set_group_FR, group_load_FRn, calls_FR, FFRpk, fr_charge. lia. Qed.
Lemma PKP_FFR_mono : forall a b e, 0 <= a <= b -> PKP_FFR a e <= PKP_FFR b e.
Proof. intros a b e _. unfold PKP_FFR. lia. Qed.
Lemma PKP_CNT0 : 0 <= PKP_CNT. Proof. unfold PKP_CNT. lia. Qed.
Lemma PKP_C24_0 : 0 <= PKP_C24. Proof. vm_compute. intros K. discriminate K. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Thm.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.

#[using="Type"] Theorem A_pk_parse_subpubkey_spec : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_H ()) "PHIA,(2<.$7.VR,)PMT,(3.$2=.)PHL,(2>.(2?.VR,)$1:.$1;.)PHMC,(30.(2?.VR,)$1=.)P,(31.(32.VR,))P,(4.$0.(33.VR,)$34.)P,(4.$0.(35.VR,+2.)$36.)P,(4.$0.(37.VR,)$38.)P,(:.=(39.VR,))P,(:.=(3:.VR,))P,(:.=(3;.VR,))P,(:.=(3<.VR,))P,Pmx,P,(1.&40.)(2.(1.&8.))P,(3=.VR,R1.)(25.R2.)P,(10.(:.(3>.(2?.VR,))(3?.(2?.VR,)))(:.(40.(2?.VR,))(41.(2?.VR,))))P,Phx,(42.$7.VR,R>.)PLBx,(3.$24.)PLFx,(3.$24.)Pmx,P,(1.&40.)(2.(1.&8.))P,(43.$7.VR,R12.R4.R3.R2.R1.)(44.$0.(45.(22.$0.$0.)$0.(46.$0.$0.)R4.))P,Phx,(42.$7.VR,R?.)PLBx,(3.$24.)PLBx',(3.$24.)PLFx,(3.$24.)Pmx,P,(1.&40.)(2.(1.&8.))P,(43.$7.VR,R14.R5.R4.R2.R1.)P,(47.$24.R5.R4.)(1<.(42.$7.VR,R16.)Lh',(42.$7.VR,R16.)(10.(43.$7.VR,R17.R1.R6.R5.R4.)(10.(4.P,$0.Sp(48.$7.VR,R17.R1.)(48.$7.VR,R17.R8.))(10.(4.$0.(49.$7.VR,R17.R1.)(49.$7.VR,R17.R8.))(10.(4.$0.(4:.$7.VR,R17.R1.)(4:.$7.VR,R17.R8.))(10.(4.$0.(4;.$7.VR,R17.R1.)(4;.$7.VR,R17.R8.))(10.(4.$0.(4<.$7.VR,R17.R1.)(4<.$7.VR,R17.R8.))(10.(4.$0.(4=.$7.VR,R17.R1.)(4=.$7.VR,R17.R8.))Pmo,$4>.(4?.(50.$7.VR,R18.R2.R1.)(50.$7.VR,R18.R9.R1.))))))))))P,(51.$7.(32.VR,)$52.)P,(53.$7.VR,R11.$54.)P,(55.$7.VR,R12.$56.+20.)P,(55.$7.VR,R13.$57.+20.)P,(58.(2?.VR,)$7.(32.VR,)$59.)P,(5:.$7.VR,R15.R14.$5;.$5<.$5=.)P,(5>.$7.VR,R16.$5?.)P,(60.$7.VR,R17.R16.$61.$62.$5<.$1:.$1;.$63.)P,(64.$7.VR,R18.R17.$61.$62.$5<.$65.)P,(66.$7.VR,R19.R18.$67.$1=.$28.)P,(68.$7.VR,R1:.(69.R19.)$6:.$6;.(6<.VR,)$6=.)(6>.$7.VR,R1;.(69.R1:.)(6?.(2?.VR,)R19.R18.)$70.$71.$72.(73.VR,)$74.$75.)")
(* [comment removed for export] *).
Proof.
  intros HIA MT HL HMC IMG UARG SM2 AMS NS1 NA1 NB1 NM1 RTCL DIMG HND HMPERM GETTAG GETALG OIDPK OIDGA GETBSN PKSETUP RSAPP USEECP SETGRP SETPUB PKFREE.
  unfold pk_parse_subpubkey_stmtA. intros until bs.
  intros HH0 HK0 LFL HBS0 BIN BP PE EB B47 BUF0 BL30 HPP0 PPAL PP0 OPP0 CWP PPLO HPKA0 PKAL PK0 OPKA0 CWK PKLO DPK DPB DKB PPOD PKOD
         ST SSH0 SLO1 SLO2 SLO TOP SPA SPH MI0 TPV SIP0 NDL RAE BUD UW0 BUDF C24H -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP0) as PPB. cbn [cells_size csize Nat.add] in PPB. change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HPKA0) as PKB. cbn [cells_size csize Nat.add] in PKB. change (Z.of_nat 16) with 16 in PKB.
  pose proof (uwc_nonneg _ _ _ _ _ _ _ UW0) as D0.
  pose proof (arl_need_rt_malloc R) as NRM. pose proof (arl_need_rt_amem R) as NRA.
  assert (NE0 : 0 <= arl_need_ecp R) by (unfold arl_need_ecp; clear - NRM NM1; lia).
  assert (NEr : arl_need_rt R <= arl_need_ecp R /\ arl_need_smalloc R <= arl_need_ecp R) by (unfold arl_need_ecp; clear; lia).
  assert (STKV : PKP_STK R = 176 + 32 + 32 + 112 + 416 + 144 + (272 + (176 + ECP_GROUP_LOAD_STACK_A)) + 320 + 1280 + STKpk R
                             + arl_need_smalloc R + arl_need_amem R + arl_need_bcmp R + arl_need_malloc R + arl_need_rt R + arl_need_ecp R) by reflexivity.
  assert (GLS : 0 <= ECP_GROUP_LOAD_STACK_A) by (vm_compute; intros K; discriminate K).
  assert (SPK0 : STKpk R = 192 + arl_need_rt R) by reflexivity.
  destruct HL as (L1 & L2 & L3 & L4) eqn:EHL. destruct HMC as (M1 & M2 & M3) eqn:EHMC.
  destruct IMG as (IG1 & IG2 & IG3 & IG4) eqn:EIMG.
  assert (IDOK : ids_okA R A_ECP_IDS_DONE A_ECP_IDS).
  { split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [intros a Ha; exact (proj2 (L4 a Ha))|].
    rewrite IG2, IG3. unfold A_ECP_IDS_DONE, A_ECP_IDS. clear. lia. }
  assert (MCOK : mc_okA R A_MUL_COUNT).
  { split; [exact M1|]. split; [exact M2|]. split; [intros a Ha; exact (proj2 (M3 a Ha))|].
    rewrite IG2, IG3. unfold A_MUL_COUNT. clear. split; [lia| split; [lia| reflexivity]]. }
  eapply (A_pk_parse_G.pk_main R HIA) with (h := h) (lo := lo) (STKk := PKP_STK R) (P := P) (BUF := BUF) (bs := bs) (slo := slo) (d := d)
                                         (SI := A_pk_sinv (arl_L R) (conj L1 (conj L2 (conj L3 L4))) (conj M1 (conj M2 M3))) (MT := MT);
    first [ eassumption | reflexivity | exact (pkp_PHE0) | exact (pkp_PHS0) | exact (pkp_FRE0 d D0) | exact (pkp_FRS0 d D0) | exact (pkp_CKF0 d D0) | exact pkp_PHIM | exact pkp_PHIME
          | exact (conj IG1 (conj IG2 (conj IG3 IG4)))
          | lazymatch goal with
            | |- (length LF < 512)%nat => unfold LFMAX_CRT in LFL; clear - LFL; lia
            | |- (length LF + 1 + _ <= 512)%nat => unfold LFMAX_CRT in LFL; clear - LFL; lia
            | |- 0 <= END < 2 ^ 64 => clear - BUF0 BP PE EB B47; lia
            | |- forall mx, si_P _ mx <-> _ => intros mx; reflexivity
            | |- forall hx LBx LFx mx, HM _ _ _ hx LBx LFx mx -> mem_inv _ mx -> _ =>
                intros hx LBx LFx mx HHx MIx; dexists A_bp1, A_bp2; exact (A_bad_points_ok LBx mx (RTCL mx (hm_rtc asegs R HIA hx LBx LFx mx HHx)) MIx)
            | |- _ <= PKP_STK R => rewrite STKV, ?SPK0; clear - NS1 NA1 NB1 NM1 NRM NRA NE0 NEr GLS; lia
            | |- _ <= bv_unsigned sp - PKP_STK R => exact SLO
            | |- arl_stklo R <= lo => clear - SLO1 SLO2; lia
            end
          | match goal with |- ?g => idtac "THM-LEFT:" g end ].
Qed.
End Thm.

(* [comment removed for export] *)
