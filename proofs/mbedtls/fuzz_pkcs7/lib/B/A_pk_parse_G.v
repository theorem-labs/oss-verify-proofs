(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiClient RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepPk RepCrt CrtStmts SInv PkTmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pk_info P_rsa_parse_pubkey P_ecp_check_pubkey P_ecp_grp_id_list P_ecp_keypair_init P_ecp_group_load P_pk_ecparams_A P_pk_parse_A P_pk_parse_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_asn1_get_tag_stmt A_asn1_get_alg_A A_oid A_oid_pk_alg A_oid_ec_grp_algid
     A_asn1_get_bitstring_null A_pk_defs A_pk_info A_pk_type A_mpi_stmtA A_mpi_stmtA_sz A_mpi_read_binary_stmt A_ecp_stmtA A_ecp_defs A_ecp_grp_id_list A_ecp_grp_facts A_ecp_check_pubkey_c24
     A_crt_stmts A_crt_parse_stmts A_pk_setup A_rsa_parse_pubkey A_rsa_parse_pubkey_c24 A_pk_ecc_set_group A_pk_ecc_set_pubkey A_pk_ecparams_stmt A_pk_free A_pk_parse_stmt
     A_pk_parse_A A_pk_parse_B A_pk_parse_C A_pk_parse_D A_pk_parse_E A_pk_parse_F A_pk_parse_G0 BX_pk_get_pk_alg BX_pk_use_ecparams_rfc8410.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_pk_parse_G () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_P"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_grp_id_list.ecp_ids_state"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_grp_id_list.A_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_grp_id_list.A_ECP_IDS"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_MUL_COUNT"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.pk_rep"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.PKA_inst"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_B.EPIQ"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "WalkPKG.Call.FINQ"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_G0.PKP_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_G0.PKP_FFR"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_G0.PKP_CNT"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_stmt.pk_parse_subpubkey_postA"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_F.CQ"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.PHIpk"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.FFRpk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_check_pubkey.bad_point_ok"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_check_pubkey_c24.A_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.pk_set_pubkey_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_grp_facts.ECP_MAX_N"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.pk_set_pubkey_FR"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.check_pubkey_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_dy_sz"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.check_pubkey_FRn"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_init"; "RocqVerifyHarness.AgentSubmission.B.A_pk_defs.A_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.grp_factsA"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.P.P_pk_parse_C.newb"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_E.DINV2"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_F.SCQ"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_FR"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_use_ecparams_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.A_PK_USE_ECPARAMS"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_FR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_defs.A_RSA_INFO"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.RSA_PP_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.RSA_PP_FR"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.B.A_pk_setup.PK_SETUP_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_C.XE"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_parse_A.A_PK_PARSE_SUBPUBKEY"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section WalkPKG.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_PK.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2_PK.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP END PKA lo STKk : Z) (P BUF : Z) (bs : list byte).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis STK0 : 176 + arl_need_smalloc R <= STKk.
  Hypothesis SLO : lo <= bv_unsigned sp - STKk.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis PKB : 0 <= PKA /\ PKA + 16 <= 2^64.
  Hypothesis ENDB : 0 <= END < 2^64.

  Local Notation BLEN := (Z.of_nat (length bs)).
  Local Notation X00 := [(PP, PP + 8); (PKA, PKA + 16)].
  Hypothesis HBS0 : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, BLEN) LB.
  Hypothesis BP : BUF <= P. Hypothesis PE : P <= END. Hypothesis EB : END <= BUF + BLEN.
  Hypothesis B47 : BUF + BLEN < 2^47. Hypothesis BUF0 : 0 < BUF. Hypothesis BL30 : BLEN < 2^30.
  Hypothesis PPAL : PP mod 8 = 0. Hypothesis PP0 : 0 < PP. Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PKAL : PKA mod 8 = 0. Hypothesis PK0 : 0 < PKA. Hypothesis PKLO : PKA + 16 <= lo.
  Hypothesis CWK : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PKA 16.
  Hypothesis DPK : PP + 8 <= PKA \/ PKA + 16 <= PP.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + BLEN <= PP.
  Hypothesis DKB : PKA + 16 <= BUF \/ BUF + BLEN <= PKA.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_PK in UARG; unfold A_SMALLOC_2_PK in SM2;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation F1 := (C1 (Z_to_bv 8 241)). Local Notation F2 := (C1 (Z_to_bv 8 242)). Local Notation F3 := (C1 (Z_to_bv 8 243)).
  Local Notation F8 := (C1 (Z_to_bv 8 248)). Local Notation Z0 := (C1 (Z_to_bv 8 0)). Local Notation P4 := (C1 (Z_to_bv 8 4)).
  Local Notation FSH0 :=
    [F1; F1; F1; F1;  F8; F8; F2; F2;  Z0; F2; F2; F2;  Z0; Z0; Z0; F2;  F2; F2; F2; F2;  P4; F2; P4; F3;  Z0; Z0; Z0; Z0;  Z0; Z0; Z0; Z0].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


  (* [comment removed for export] *)
  Variables (slo d : Z) (mo0 : Model).
  Variable SI : sinv L.
  Variable MT : list modp_ent.
  Local Notation PK := (PKA_inst MT).
  Local Notation WXF := (X00 ++ si_fp SI).
  Local Notation WBP := [(PP, PP + 8)].
  Hypothesis HH0 : HM asegs R HIA h LB LF m.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis SIP0 : si_P SI m.
  Hypothesis NDL : List.NoDup (map fst LB).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis SSH0 : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLO1 : arl_stklo R <= slo. Hypothesis SLO2 : slo <= lo.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis UW0 : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis PPOD : PP + 8 <= hl_data_lo L \/ hl_data_hi L <= PP.
  Hypothesis PKOD : PKA + 16 <= hl_data_lo L \/ hl_data_hi L <= PKA.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis STK2 : 176 + 32 + arl_need_bcmp R <= STKk.
  Hypothesis RTCL : forall mx, arl_rtc R mx -> asan_rtc mx.
  (* [comment removed for export] *)
  Hypothesis HND : forall (hx : HST asegs R HIA) LBx LFx mx, HM asegs R HIA hx LBx LFx mx -> List.NoDup (map fst LBx).
  Hypothesis HMPERM : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phx,(0.$1.VR,VHIA,)PLBx,(2.$3.)PLBx',(2.$3.)PLFx,(2.$3.)Pmx,P,(4.&40.)(5.(4.&8.))P,(6.$1.VR,VHIA,R5.R4.R2.R1.)P,(7.$3.R5.R4.)(8.(0.$1.VR,VHIA,)Lh',(0.$1.VR,VHIA,)(9.(6.$1.VR,VHIA,R1.R6.R5.R4.)(9.(:.P,$;.Sp(<.$1.VR,VHIA,R1.)(<.$1.VR,VHIA,R8.))(9.(:.$;.(=.$1.VR,VHIA,R1.)(=.$1.VR,VHIA,R8.))(9.(:.$;.(>.$1.VR,VHIA,R1.)(>.$1.VR,VHIA,R8.))(9.(:.$;.(?.$1.VR,VHIA,R1.)(?.$1.VR,VHIA,R8.))(9.(:.$;.(10.$1.VR,VHIA,R1.)(10.$1.VR,VHIA,R8.))(9.(:.$;.(11.$1.VR,VHIA,R1.)(11.$1.VR,VHIA,R8.))Pmo,$12.(13.(14.$1.VR,VHIA,R2.R1.)(14.$1.VR,VHIA,R9.R1.))))))))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis SIP : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Pmx,P,(4.&40.)(5.(4.&8.))(13.(15.(16.VR,)VSI,R1.)(9.(17.$1.$18.$19.R1.)(8.(4.&40.)Lcnt,(4.&40.)(1:.$1.R2.$1;.(1<.$1=.(1>.R1.)(1?.$1=.))))))")
(* [comment removed for export] *).
  Hypothesis SIFP : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "(:.(2.$20.)(21.(16.VR,)VSI,)(1<.(22.$;.$;.)(23.$;.$;.$18.(24.$18.+1.))(1<.(22.$;.$;.)(23.$;.$;.$19.(24.$19.+38.))(1<.(22.$;.$;.)(23.$;.$;.$1;.(24.$1;.+8.))(1?.(22.$;.$;.))))))")
(* [comment removed for export] *).
  Local Notation PHIk := PKP_PHI.
  Local Notation FFRk := PKP_FFR.
  Local Notation CNTk := PKP_CNT.
  Hypothesis BUD : havol asegs R HIA h + PHIk (END - P) <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + FFRk (END - P) d <= FR_MAX.
  Hypothesis STK3 : 176 + STKpk R <= STKk.
  Hypothesis PKFREE : pk_free_stmtA asegs R HIA PK PHIpk FFRpk (STKpk R) A_PK_FREE.

  Local Notation EPIQ' := (A_pk_parse_B.EPIQ R HIA LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo).
  Local Notation DINV2' := (A_pk_parse_E.DINV2 R HIA LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP END PKA lo P BUF bs).
  Local Notation XF' := (A_pk_parse_F.XF R HIA LF sp PP END P).
  Local Notation CQ' := (A_pk_parse_F.CQ R HIA LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP END PKA lo P BUF bs).
  Local Notation POST := (pk_parse_subpubkey_postA asegs R HIA PK SI PHIk FFRk CNTk h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP P END PKA lo slo d m mo0).

  (* [comment removed for export] *)
  Definition FINQ (own : list blk) (a0v : word) (mm : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "(8.$;.Lr,$;.(8.$;.Lp',$;.(8.$;.Linfo,$;.(8.$;.Lctx,$;.(9.(:.(4.&40.)O2.(25.&40.R4.))(9.(9.(26.(27.(28.+2.+1?.))R4.)(29.R4.=))(9.(1:.$1.O1.VPP,(1<.$1=.(1>.(25.&40.R3.))(1?.$1=.)))(9.(9.(29.VP,R3.)(29.R3.VEND,))(9.(1:.$1.O1.VPKA,(1<.$1=.(1>.(25.&40.R2.))(1<.$1=.(1>.(25.&40.R1.))(1?.$1=.))))(9.(2:.$1.(2;.VMT,)O1.(2<.$3.O3.VLB,)VPKA,R2.R1.O3.)(9.P,(2=.(:.$;.R4.=))(9.(:.$;.R3.=)(9.(:.$;.R2.=)(:.(2.$3.)O3.(1?.$3.))))(9.(15.(16.VR,)VSI,O1.)(29.(2>.(2<.$3.O3.VLB,))(24.(2>.VLB,)(2?.(30.R3.VP,)+1701.)))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="Type"] Lemma epiq_mono : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Php,(0.$1.VR,VHIA,)PLBa,(2.$3.)PLBq,(2.$3.)Pm0,P,(4.&40.)(5.(4.&8.))PWA,(2.$20.)PFB,$;.Psp1,$;.Pa0v,(4.&40.)PXQ,P,P,(4.&40.)(5.(4.&8.))SpPXQ',P,P,(4.&40.)(5.(4.&8.))SpPms,$31.P,(32.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R1.)P,Pmm,P,(4.&40.)(5.(4.&8.))P,(6.$1.VR,VHIA,R>.R;.(1<.(22.$;.$;.)(23.$;.$;.R8.+100.)VLF,)R1.)P,(33.$1.R2.)P,(34.$1.VR,VHIA,R?.R>.VLF,(35.&40.Vsp,)(36.VR,)R;.R<.R3.)P,A1.R8.R4.A1.R8.R5.(32.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R>.R=.R<.R;.R:.R9.R8.R7.R6.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros hq hp LBa LBq m0 WA FB sp1 a0v XQ XQ' ms EQ HX. unfold A_pk_parse_B.EPIQ in *.
    destruct EQ as (mm & EQ). exists mm.
    repeat (lazymatch type of EQ with ex _ => let x := fresh "x" in destruct EQ as (x & EQ); exists x end).
    ddestruct EQ as (E0 & HHq & FHD & FSH & SAVE & ST1 & STb & MIq & PRESa & XQm).
    repeat (split; [assumption|]). apply HX; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hm_block_bounds : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phx,(0.$1.VR,VHIA,)PLBx,(2.$3.)PLFx,(2.$3.)Pmx,P,(4.&40.)(5.(4.&8.))PB,$;.Pj,$;.P,(6.$1.VR,VHIA,R6.R5.R4.R3.)P,(37.(22.$;.$;.)(23.$;.$;.R3.R2.)R6.)(9.(26.=R4.)(9.(29.=R3.)(9.(29.(24.R4.R3.)(38.(16.VR,)))(39.(29.(24.R4.R3.)(3:.(16.VR,)))(29.(3;.(16.VR,))R4.)))))")
(* [comment removed for export] *).
  Proof.
    intros hx LBx LFx mx B j HHx Hb. destruct (hm_apart asegs R HIA hx LBx LFx mx HHx) as [HBR _]. rewrite Forall_forall in HBR.
    ddestruct (HBR (B, j) ltac:(apply in_app_iff; left; exact Hb)) as (K1 & K2 & K3 & K4). cbn [fst snd] in K1, K2, K3, K4. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L38089602648.6L56763417752.800000?00US2PP1a1B1j2Hr1KS1R1a1B1j2Hr2B02BC3ACV". (* [comment removed for export] *)
  #[using="Type"] Lemma own_agree : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Pown,(2.$3.)PLFq,(2.$3.)Pm2x,P,(4.&40.)(5.(4.&8.))Pmm,P,(4.&40.)(5.(4.&8.))P,(34.$1.VR,VHIA,R5.(2<.$3.R4.VLB,)VLF,(35.&40.Vsp,)(36.VR,)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1?.(22.$;.$;.)))R2.R1.)P,(6.$1.VR,VHIA,R6.(2<.$3.R5.VLB,)R4.R2.)P,Pb,$3.P,(37.$3.R1.R7.)(39.(29.(24.VPP,+8.)(3<.$;.$;.R2.))(29.(24.(3<.$;.$;.R2.)(3=.$;.$;.R2.))VPP,))Pa,$;.P,(3>.R8.R1.)(:.(5.(4.&8.))A1.R6.(3?.R2.)A1.R7.(3?.R2.))")
(* [comment removed for export] *).
  Proof.
    (intros hq own LFq m2x mm PB HHq APO a dd_H; ddestruct dd_H as ([B j] & Hb & Hr)). cbn [fst snd] in Hr.
    destruct (hm_block_bounds hq _ _ _ B j HHq ltac:(apply in_app_iff; left; exact Hb)) as (B0 & J0 & BC & _).
    pose proof (alloc_ceiling_val R) as ACV.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PB)) as PX.
    apply (PX a ltac:(clear - Hr B0 BC ACV; lia)).
    - right; right. exists (B, j). split; [apply in_app_iff; left; apply in_app_iff; left; exact Hb| cbn [fst snd]; exact Hr].
    - cbn [outside]. split; [| exact I]. pose proof (APO _ Hb) as K. cbn [fst snd] in K. clear - K Hr. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="PPOD"] Lemma si_path : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)PLBq,(2.$3.)Pm2x,P,(4.&40.)(5.(4.&8.))Pmm,P,(4.&40.)(5.(4.&8.))P,(34.$1.VR,VHIA,R4.R3.VLF,(35.&40.Vsp,)(36.VR,)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1?.(22.$;.$;.)))R2.R1.)P,(15.(16.VR,)VSI,R3.)(15.(16.VR,)VSI,R3.)")
(* [comment removed for export] *).
  Proof.
    intros hq LBq m2x mm PB S2. eapply (si_heap_presx asegs L SI); [exact S2| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PB))|].
    intros a Ha. exact (si_outside1 L SI PP 8 a PPOD Ha).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L13748187931.9L26892418956.1L31023889811.6L40281191306.3L50790580594.8L56763417752.8L62018535662.1L62050552506.900000<00@00V00_01>01T01W01dS2PP2lo4PPLOS2spS1R3HIA1h2sp3TOP5HTOP0S1R3HIA1hS1R3NS12sp2lo4STKk3LOS4STK03SLOS1R1a1B1j2Hr2B02BC3ACVS1RS3PKA2lo4PKLO". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PPLO CWP PKLO CWK HH0 SSH0 SLO1 HND"] Lemma fin_exit : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Pown,(2.$3.)PWX,(2.$20.)PFB,$;.Psp1,$;.Pa0v,(4.&40.)Pms,$31.P,(32.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R7.R7.VLB,(2<.$3.R6.VLB,)Vm,R5.R4.R3.R2.(40.R6.R2.)R1.)P,Px,$;.P,(41.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1<.(22.$;.$;.)(23.$;.$;.VPKA,(24.VPKA,+10.))(1?.(22.$;.$;.))))(21.(16.VR,)VSI,))R1.)(41.R8.R2.)P,(9.(29.(30.(35.&40.Vsp,)+;0.)R5.)(29.R5.(30.(35.&40.Vsp,)+:0.)))P,(:.$;.(42.R6.+20.)=)P,(:.$;.(42.R8.+40.)=)P,(43.VR,VLB,VLF,R9.+100.)P,(43.VR,(2<.$3.R<.VLB,)VLF,R:.+100.)P,(44.(<.$1.VR,VHIA,Vh,)R;.+100.)P,PB,$;.Pj,$;.P,(37.(22.$;.$;.)(23.$;.$;.R2.R1.)VLF,)(39.(29.(24.R?.+100.)R3.)(29.(24.R3.R2.)R?.))P,Px,$;.P,(<.$1.VR,VHIA,Vh,R1.)(<.$1.VR,VHIA,R12.R2.)P,(:.$;.(=.$1.VR,VHIA,R11.)(=.$1.VR,VHIA,Vh,))P,(:.$;.(>.$1.VR,VHIA,R12.)(>.$1.VR,VHIA,Vh,))P,(:.$;.(?.$1.VR,VHIA,R13.)(?.$1.VR,VHIA,Vh,))P,(29.(10.$1.VR,VHIA,R14.)(24.(10.$1.VR,VHIA,Vh,)(45.(30.VEND,VP,))))P,(29.(11.$1.VR,VHIA,R15.)(24.(11.$1.VR,VHIA,Vh,)(46.(30.VEND,VP,)Vd,)))P,(29.(47.(48.$3.R15.))$49.)(4:.$1.(4;.$1.VR,VHIA,R17.Vmo0,)(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)R11.)")
(* [comment removed for export] *).
  Proof.
    intros hq own WX FB sp1 a0v ms EQ WSUB SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq CNTq.
    unfold A_pk_parse_B.EPIQ in EQ.
    ddestruct EQ as (mm & xra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & s4v & s5v & s6v & s7v & s8v & s9v & s10v & w0 & w1 & w2
                    & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & b14 & b15 & b16 & b17 & b18 & b19 & b20 & b21 & b22 & b23
                    & b24 & b25 & b26 & b27 & b28 & b29 & b30 & b31
                    & -> & HHq & FHD & FSH & SAVE & ST1 & STb & MIq & PRESa & FQ).
    ddestruct FQ as (r & p' & info & ctx & Ea0 & RR & HPPq & Hp' & HPKAq & REPq & RNZ & SIq & C24q).
    pose proof (presW_init_at R HIA hq _ _ (own ++ LB) LF mm (bv_unsigned sp) (arl_stklo R) [] hq HHq
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRES2.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply A_pk_parse_B.epi_walk with (h := h) (lo := lo) (STKk := STKk) (h3 := hq) (LBa := LB) (LBb := own ++ LB);
        first [ exact HHq | exact HCSq | exact ETq | exact ESq | exact PRESa | exact PRES2 | exact FRSH | exact FRSHq | exact CFB | exact AP
              | (intros b' Hb; apply in_app_iff; right; exact Hb)
              | eassumption | reflexivity | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    pose proof (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES9) as HPF. rewrite ESq in HPF.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES29)) as PX29.
    pose proof (hm_top asegs R HIA h LB LF m HH0) as HTOP0.
    assert (SUBf : forall b, In b (LB ++ fdata LF) -> In b ((own ++ LB) ++ fdata LF)).
    { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    assert (CRPP : client_range L ((own ++ LB) ++ fdata LF) (bv_unsigned sp) PP 8).
    { eapply client_range_wsep; [exact CWP| exact SUBf| left; clear - PPLO SLO STK0 NS1; lia]. }
    assert (CRPK : client_range L ((own ++ LB) ++ fdata LF) (bv_unsigned sp) PKA 16).
    { eapply client_range_wsep; [exact CWK| exact SUBf| left; clear - PKLO SLO STK0 NS1; lia]. }
    unfold pk_parse_subpubkey_postA.
    deexists 15. dexists m9, mo9, h4, r, p', info, ctx, own.
    split; [rewrite Ea0; reflexivity|]. split; [reflexivity|]. split; [exact RR|].
    split; [exact MI9|]. split; [exact ST9|].
    split; [eapply (presA_sshad asegs R _ _ _ _ _ _ m m9 _ _ HPF); [exact SSH0| exact SLO1| clear - TOP HTOP0; lia]|].
    split; [exact MF9|].
    split; [eapply presA_weaken; [exact HPF| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear - LOS SLO STK0 NS1; lia| clear; lia| exact WSUB]|].
    split; [rewrite E4top; exact ETq|]. split; [rewrite E4stk; exact ESq|]. split; [rewrite E4flag; exact EFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; exact EVq|]. split; [rewrite E4fr; exact EFRq|].
    split; [exact CNTq|]. split; [exact C24q|].
    split; [eapply heap_presx_rw_cells; [exact PX29| exact HPPq| exact CRPP| cbn; exact I]|]. split; [exact Hp'|].
    split; [eapply heap_presx_rw_cells; [exact PX29| exact HPKAq| exact CRPK| cbn; exact I]|].
    split.
    { eapply (pk_rep_frame asegs PK); [exact REPq| exact MI9| intros b Hb; apply in_app_iff; left; exact Hb|].
      (intros a dd_H; ddestruct dd_H as ([B j] & Hb & Hr)). cbn [fst snd] in Hr.
      destruct (hm_block_bounds hq _ _ _ B j HHq ltac:(apply in_app_iff; left; exact Hb)) as (B0 & J0 & BC & _).
      pose proof (alloc_ceiling_val R) as ACV.
      apply (PX29 a ltac:(clear - Hr B0 BC ACV; lia)); [| cbn; exact I].
      right; right. exists (B, j). split; [apply in_app_iff; left; apply in_app_iff; left; exact Hb| cbn [fst snd]; exact Hr]. }
    split; [exact RNZ|].
    split; [exact (HND _ _ _ _ HH4)|].
    split; [exact HH4|].
    eapply (si_heap_presx asegs L SI); [exact SIq| exact PX29| intros a _; cbn; exact I].
    all: match goal with |- ?g => idtac "FINEXIT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L14565458108.3 L1540877545.3  L19965341046.14L21014960645.7 L21014960772.14L28572447521.0 L32951620623.4 L33804787453.4 L3480690467.14 L3778745695.11 L38948636245.0 L39332637397.0 L43167789172.4 L43300649301.0 L51042627313.9 L51508673957.0 L5362633121.11 L55223687620.2 L58800644504.14L62018535662.1 L65146463766.10L67092310858.4 L67216882938.12L9356559676.13 L973128649.0   00000<00H00`01601i01j02802H02R03503603703803903:03;03_03f04E04H04h05405[06N06OS2PP3PKA3DPKS2sp3sp13SP1S1R3HIA1h2sp3TOP3sp13SP1S3PKA2FB3APK1A1n2H12H2S1R3NS12sp3PKA2lo4STKk4STK03SLO4PKLO3sp13SP11A1n2H1SS3END1P2p23HPxS3PKA3BUF2bs3DKBS3sp14SP1MS1R3HIA1h3END1P2hq2Vq3EVq2BV2h23HV2SSFSFSS1R3HIA1h3END1P1d4BUDF2hq2Fq4EFRq2BFS2rc2RCS1R2sp2lo4STKk3SLO4STK33sp13SP1S1RS1R3HIA1h3END1P3BUD2hq2Vq3EVq2BVS2LB1P2p22DPS1R3HIA1h3END1P1d2hq2Fq4EFRq2BF2h24HFR2S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP TPV LFB PPB PKB BIN BP PE EB PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB HH0 SSH0 SLO1 PPOD PKOD HND BUD BUDF STK3 PKFREE"] Lemma do_free : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Pown,(2.$3.)Pm2x,P,(4.&40.)(5.(4.&8.))PFB,$;.Psp1,$;.Pkv,(4.&40.)Pp2,$;.Pe1,$;.Prc,$;.Pinfo,$;.Pctx,$;.Pa1v,(4.&40.)Pa2v,(4.&40.)Ps6v,(4.&40.)PVq,$;.PFq,$;.Pms,$31.P,(4=.VR,VHIA,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,+;0720.+;1740.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1<.(22.$;.$;.)(23.$;.$;.VPKA,(24.VPKA,+10.))(1?.(22.$;.$;.))))(21.(16.VR,)VSI,))(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1?.(22.$;.$;.)))R>.R=.R11.(2<.$3.R10.VLB,)R?.R<.R;.R:.(25.&40.R8.)(25.&40.R7.)(25.&40.VPKA,)R6.R5.(25.&40.R9.)R4.R1.)P,(9.(26.(27.(28.+2.+1?.))R:.)(26.R:.=))P,(9.(29.(30.(35.&40.Vsp,)+;0.)R?.)(29.R?.(30.(35.&40.Vsp,)+:0.)))P,(:.$;.(42.R10.+20.)=)P,(:.$;.(42.R12.+40.)=)P,(43.VR,VLB,VLF,R13.+100.)P,(43.VR,(2<.$3.R16.VLB,)VLF,R14.+100.)P,(44.(<.$1.VR,VHIA,Vh,)R15.+100.)P,PB,$;.Pj,$;.P,(37.(22.$;.$;.)(23.$;.$;.R2.R1.)VLF,)(39.(29.(24.R19.+100.)R3.)(29.(24.R3.R2.)R19.))P,Px,$;.P,(<.$1.VR,VHIA,Vh,R1.)(<.$1.VR,VHIA,R1<.R2.)P,(:.$;.(=.$1.VR,VHIA,R1;.)(=.$1.VR,VHIA,Vh,))P,(:.$;.(>.$1.VR,VHIA,R1<.)(>.$1.VR,VHIA,Vh,))P,(:.$;.(?.$1.VR,VHIA,R1=.)(?.$1.VR,VHIA,Vh,))P,(29.(10.$1.VR,VHIA,R1>.)(24.(10.$1.VR,VHIA,Vh,)R10.))P,(29.(11.$1.VR,VHIA,R1?.)(24.(11.$1.VR,VHIA,Vh,)R10.))P,(29.(24.R12.(4>.=))(45.(30.VEND,VP,)))P,(29.(24.R12.(4?.=+1<.))(46.(30.VEND,VP,)Vd,))P,(29.=$49.)P,(2:.$1.(2;.VMT,)R21.(2<.$3.R22.VLB,)VPKA,R1:.R19.R22.)P,(15.(16.VR,)VSI,R22.)P,Pb,$3.P,(37.$3.R1.R25.)(39.(29.(24.VPP,+8.)(3<.$;.$;.R2.))(29.(24.(3<.$;.$;.R2.)(3=.$;.$;.R2.))VPP,))(4:.$1.(4;.$1.VR,VHIA,R26.Vmo0,)(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)R16.)")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros CQH RC SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq BV BF CNT0 REP2 SI2 APO.
    ddestruct CQH as (mm & c0 & c1 & c2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & -> & D & PRESB).
    pose proof D as D0.
    ddestruct D0 as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & p1v & ptag & ppad & plen
                   & HHq & FHD & LPKC & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MIq
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & Hp1v & Hp1v2 & PPC & PRES).
    rt_facts.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq. rewrite ETq, ESq in HTOPq.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    (* [comment removed for export] *)
    pose proof (own_agree hq own _ m2x mm PRESB HHq APO) as AGR.
    assert (REPm : pk_rep asegs PK mm (own ++ LB) PKA info ctx own).
    { eapply (pk_rep_frame asegs PK); [exact REP2| exact MIq| intros b Hb; apply in_app_iff; left; exact Hb| exact AGR]. }
    pose proof (si_path hq _ m2x mm PRESB SI2) as SIm.
    assert (PHI0 : PHIpk (Z.of_nat (length own)) = PHIpk 0) by reflexivity.
    assert (FFR0 : FFRpk (Z.of_nat (length own)) 28 = FFRpk 0 28) by reflexivity.
    pose proof PKFREE as PF'. unfold pk_free_stmtA, A_PK_FREE in PF'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply PF' with (h := hq) (LBo := own) (LB := LB) (LF := (FB, 256) :: LF) (PKA := PKA) (info := info) (ctx := ctx) (owned := own) (lo := lo) (d := 28);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?PHI0, ?FFR0; rewrite ?ETq;
        first [ exact HHq | exact HK1 | exact HPKA | exact PKAL | exact PK0 | exact REPm | exact OPKA | exact STbelow | exact LOS | exact MIq | exact TPV | reflexivity
              | lazymatch goal with
                | |- forall b, In b own -> In b own => intros b Hb; exact Hb
                | |- List.NoDup _ => exact (HND _ _ _ _ HHq)
                | |- client_wrange _ _ _ _ PKA 16 => eapply client_wrange_mono; [exact CWK| intros b Hb; apply fdata_cons_sub; exact Hb]
                | |- PKA + 16 <= lo \/ _ => left; exact PKLO
                | |- uw_obj _ _ _ _ => right; clear; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD EVq BV; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF EFRq BF; lia
                | |- _ => clear - SP1 SP1M SLO STK0 STK3 NS1 TOP; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "FREE-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & LBo'
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & SUBo & KEEPo & GONEo & ND2 & HPKA2).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xb0720)) with (Z_to_bv 64 0xb0720 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R. rewrite PHI0 in HV2. rewrite FFR0 in HFR2.
    assert (ELO : LBo' = []).
    { destruct LBo' as [|b0 L0]; [reflexivity|]. exfalso. apply (GONEo b0 ltac:(left; reflexivity)). apply in_map. apply SUBo. left. reflexivity. }
    subst LBo'. cbn [app] in HP2, HH2.
    assert (HCSh2 : forall x, CS x -> hcs asegs R HIA h2 x) by (intros x Hx; apply HCS2, HCSq, Hx).
    assert (HS2' : hstkhi asegs R HIA h2 = hstkhi asegs R HIA h) by (rewrite HS2; exact ESq).
    (* [comment removed for export] *)
    assert (PRESa2 : presW asegs R HIA h2 LB LF (bv_unsigned sp) (arl_stklo R) WXF m m2).
    { eapply A_pk_parse_E.presW_step with (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (FB := FB) (sp1 := sp1) (hq := hq) (LBq := LB) (W := [(PKA, PKA + 16)]) (mc := mm);
        first [ exact PRES | exact HP2 | exact HCS2 | (exact HS2) | eassumption | (clear - SP1; lia) | (intros b Hb; exact Hb)
              | lazymatch goal with |- forall x, client_addr _ _ _ x -> _ => idtac end
              | match goal with |- ?g => idtac "PWS-LEFT:" g end ].
      intros x _ Hx. apply (proj1 (outside_app _ _ x)) in Hx. destruct Hx as [Hx _]. cbn [outside] in Hx |- *. clear - Hx. tauto. }
    assert (D2 : DINV2' WXF FB sp1 h2 LB FSH0 kv p2 e1 (Z_to_bv 64 0) (Z_to_bv 64 0) m2).
    { eapply A_pk_parse_E.dinv2_presA with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (hq := hq) (LBq := own ++ LB) (LBp := LB) (W := [(PKA, PKA + 16)]) (mc := mm);
        first [ exact D | reflexivity | exact SP1 | exact F64 | exact FRSHq | exact ESq | exact HP2 | exact HH2 | exact HCS2 | exact ST2 | exact MI2 | exact HPKA2 | exact PRESa2
              | eassumption
              | lazymatch goal with
                | |- forall b, In b LB -> In b LB => intros b Hb; exact Hb
                | |- forall A n, FB <= A -> _ -> disjoint_from _ A n => intros A n H1 H2; cbn [disjoint_from]; split; [clear - H1 H2 APK; lia| exact I]
                | |- forall A n, sp1 <= A -> disjoint_from _ A n => intros A n H1; cbn [disjoint_from]; split; [clear - H1 PKLO SP1 SLO STK0 NS1; lia| exact I]
                | |- disjoint_from _ PP 8 => cbn [disjoint_from]; split; [clear - DPK; lia| exact I]
                | |- disjoint_from _ BUF _ => cbn [disjoint_from]; split; [clear - DKB; lia| exact I]
                end
              | match goal with |- ?g => idtac "FREE-DINV-LEFT:" g end ]. }
    pose proof (presW_init_at R HIA h2 _ _ LB LF m2 (bv_unsigned sp) (arl_stklo R) WBP h2 HH2
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb2.
    assert (SI2' : si_P SI m2).
    { eapply (si_heap_presx asegs L SI); [exact SIm| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)|].
      intros a Ha. exact (si_outside1 L SI PKA 16 a PKOD Ha). }
    assert (FRSH2 : fresh_apart R LB LF FB 256) by exact FRSH.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo0).
    { eapply A_pk_parse_F.seg_F with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (WB := WBP) (hq := h2) (LBq := LB) (m2x := m2) (s3v := Z_to_bv 64 rc);
        first [ exact D2 | exact PRESb2 | exact HCSh2 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact HS2'
              | (rewrite HT2; exact ETq) | (intros b Hb; exact Hb) | eassumption | match goal with |- ?g => idtac "SEGF-PRE-LEFT:" g end ]. }
    cbv beta. intros ms5 EQ.
    eapply (fin_exit h2 [] WXF FB sp1 (Z_to_bv 64 rc));
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact AP | exact HCSh2 | exact HS2' | (intros x Hx; exact Hx)
            | (rewrite HT2; exact ETq) | (rewrite HF2; exact EFq)
            | lazymatch goal with
              | |- havol _ _ _ _ <= _ => clear - HV2 EVq BV; lia
              | |- hfr _ _ _ _ <= _ => clear - HFR2 EFRq BF; lia
              | |- Z.of_nat (length []) <= _ => cbn [length Z.of_nat]; exact CNT0
              | |- context [FINQ] =>
                  eapply epiq_mono; [exact EQ|]; (intros mx HHx MIx PWx dd_H; ddestruct dd_H as (PBx & HPPx & HPx & HPKAx));
                  dexists rc, p2, 0, 0;
                  split; [reflexivity|]; split; [clear - RC; lia|]; split; [exact HPPx|]; split; [exact HPx|]; split; [exact HPKAx|];
                  split; [apply (pk_rep_null asegs PK)|]; split; [intros _; repeat split; reflexivity|];
                  split; [exact (si_path h2 _ m2 mx PBx SI2')|];
                  cbn [app]; pose proof (Z.div_pos (p2 - P) 5889 ltac:(clear - HPx; lia) ltac:(clear; lia)) as DP; clear - DP; lia
              end
            | match goal with |- ?g => idtac "FREE-FIN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis STK4 : 176 + 1536 + arl_need_ecp R <= STKk.
  Hypothesis NEEDE : 0 <= arl_need_ecp R.
  Hypothesis SETPUB : pk_ecc_set_pubkey_stmtA asegs R HIA MT A_PK_ECC_SET_PUBKEY A_MUL_COUNT A_BAD_POINTS.
  Hypothesis MCOK : mc_okA R A_MUL_COUNT.
  Hypothesis IDOK : ids_okA R A_ECP_IDS_DONE A_ECP_IDS.
  Hypothesis BPOK : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phx,(0.$1.VR,VHIA,)PLBx,(2.$3.)PLFx,(2.$3.)Pmx,P,(4.&40.)(5.(4.&8.))P,(6.$1.VR,VHIA,R4.R3.R2.R1.)P,(33.$1.R2.)(8.$50.Lbp1,$50.(8.$50.Lbp2,$50.(9.(51.$1.R5.R7.$52.R2.)(9.(51.$1.R5.R7.(24.$52.+20.)R1.)(9.(53.R2.)(53.R1.))))))")
(* [comment removed for export] *).
  Hypothesis LFN : (length LF + 1 + ECP_POINT_READ_NF <= 512)%nat.
  Hypothesis C24H : cnt24 LB + PKP_C24 <= C24MAX.

  Local Notation MC := A_MUL_COUNT.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L22805382621.2L35411708365.2L52792927696.600000600<00MS1a2HaS1a2HaS1R2I12I22I31a2Ha". (* [comment removed for export] *)
  #[using="IDOK"] Lemma ids_presA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "PLBx,(2.$3.)PLFx,(2.$3.)PSPx,$;.PSSPx,$;.PTOPx,$;.PW,(2.$20.)Pmx,P,(4.&40.)(5.(4.&8.))Pmy,P,(4.&40.)(5.(4.&8.))P,(17.$1.$18.$19.R2.)P,(54.$1.VR,R9.R8.R7.R6.R5.R4.R3.R2.)P,(55.R5.$18.+1.)P,(55.R6.$19.+38.)(17.$1.$18.$19.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros LBx LFx SPx SSPx TOPx W mx my dd_H; ddestruct dd_H as (b & bsx & R1 & R2 & IMP); intros HP D1 D2). ddestruct IDOK as (I1 & I2 & I3 & I4 & _).
    dexists b, bsx. split; [| split; [| exact IMP]].
    - eapply (presA_rw_cells asegs R); [exact HP| exact R1| | exact D1]. cbn [cells_size csize Nat.add]. intros a Ha. right; left.
      split; [clear - Ha I1 I2 I3; lia| apply I4; left; clear - Ha; lia].
    - eapply (presA_rw_cells asegs R); [exact HP| exact R2| | exact D2]. cbn [cells_size csize Nat.add]. intros a Ha. right; left.
      split; [clear - Ha I1 I2 I3; lia| apply I4; right; clear - Ha; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="HIA LOS"] Lemma fresh_apart_objA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "PN,$;.Pk,$;.PA,$;.Pn,$;.PTOPx,$;.P,(43.VR,VLB,VLF,R5.R4.)P,(56.(16.VR,)(2<.$3.VLB,(57.VLF,))Vlo,R2.R4.R3.)P,(26.=R4.)P,(26.=R7.)(39.(29.(24.R9.R8.)R7.)(29.(24.R7.R6.)R9.))")
(* [comment removed for export] *).
  Proof. intros N k A n TOPx FR CW Hn Hk. exact (frame_apart_obj R HIA LB LF lo TOPx A n N k FR CW Hn Hk LOS). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01?0?L11127637930.6 L11136097799.13L11307491108.5 L13551397331.2 L15008978136.3 L15318565559.3 L1540877545.3  L19025301323.13L19597524532.6 L19965341046.16L21538005540.6 L21538007604.5 L21540367912.7 L21566214438.6 L21884438016.3 L22720842886.6 L22722674826.4 L23606728283.7 L23606728410.16L23743014399.11L23755645416.13L2397676628.0  L24023021321.16L24299716137.7 L25281032412.5 L25757215576.0 L26083066514.2 L26866085392.16L26866085521.9 L26892418956.1 L27111942217.1 L27687752827.13L28248436663.3 L28364173308.10L29121023659.16L29195095995.9 L29362887695.8 L31023889811.6 L31868079865.6 L34190246353.4 L3480690467.16 L35194455852.3 L35716151075.5 L36432766960.4 L36811323463.5 L36873639411.4 L38087549238.13L38484132271.9 L38948636245.0 L39316637317.0 L39332637397.0 L40890272010.8 L42888598577.7 L43300649301.0 L48117736582.10L48132467214.9 L48285060136.0 L49799904432.3 L51042627313.10L51313452802.5 L51313454866.4 L51315286814.3 L51508673957.0 L53781488386.4 L54256493155.11L56658999053.1 L59308664168.1 L61686649508.6 L62018535662.1 L62037211595.9 L63867716001.0 L65500096437.3 L66151427842.16L66878085703.5 L68091150744.13L696052593.2   L9218375351.2  L9356559676.13 L9873114841.11 00000<00g01901@01L01V01b02L02a03903:03I03J03a03i03j04704L05D05h06S06T07307I07J07K07S08N08j08n09209a09h0:G0;>0;\0<50<K0<\0<k0=50=A0=U0=b0>30>?0>m0?I0?J0?K0?L0?^0@:0@;0@c0AF0AG0AS0AT0AU0AV0AW0AX0Af0BJ0BN0BR0Bg0Bj0CM0CN0CY0D<0DO0E:0EB0EI0F<0FhS2LB4C24H2K3S1R3END2lo3BUF2bs3LOS2EB2p52e13HeE3ALO4BUFCS1P3BUF2BP2p54Hp2aS1e3SZeS2p52e14Hp2eS1r2RR3RNZS2sp3sp13SP1S3END1P3BUF2bs2BP2EB2p52e11C4Hp2a3HeE4APCBS1R1C3CF23ID13ID23ID3S1R3HIA1h2sp3TOP3sp13SP1FS3END1P1d2Fq2BFFS1P3BUF2BP4BUF02p54Hp2aS2PP1b1KFS3END1P2Vq2BVS2FB1C4APCF1A1n2H12H2S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp11C3SP13ALO3CF11A1n2H1S1R3HIA1h3END1P1d4BUDF2hq2Fq4EFRq2BFS1R3HIA1h3END1P3BUD2hq2p52e12Vq3EVq2BV4MONOSS1R2sp2lo4STKk3SLO4STK43sp13SP1S3END1P2p52e14Hp2a3HeEFSS2LF3LFNS1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO4DLOW3MC21A1n2H1S1R2FB3FD23MC13MC21A1n2H12H2S2spS2PPS1R3HIA3NS11h2sp3PKA2lo4STKk4STK03SLO4PKLO1a2HaS1C1x1KS1R3HIA1h3END1P1d2Fq2BF2h34EFR3S1R3END1P3BUF2bs2BP2EB4DIMG2p52e14Hp2a3HeE4BUFI3MC13MC2S1R3HIA1h1d2hq2Fq4EFRq2h24HFR2S3END3BUF2bs2EB2p52e13HeES1R3HIA1h2sp3TOP5HTOP0S1R3HIA1h2sp1a2HaS3BUF2bs1C4APCBS3sp14SP1MS3PKA1C4APCKS1R3PKA4PKOD3MC13MC2S1R1C3ACV3CF1S1R1C3CF23MC13MC2S2LB1P2e12DPS1R3HIA3NS11h2sp2PP2lo4STKk4STK03SLO4PPLO1a2HaS1R3HIA1h3END1P2Vq2BV2h33EV3SSSS1g2Q'4own'1K1H2H0S1R3BUF2bs4DIMG4BUFI3MC13MC2SS1R3NS12sp2lo4STKk3LOS4STK03SLO3ALO4DLOWS1R3NS12sp2lo4STKk3LOS4STK03SLO3ALOSS2sp3sp13SP1FFFFSS3END1P2e13HPxS1R3END3BUF2bs2EB2p52e13HeE3ACV4BUFCS2spS2EIS1R1C3CF23ID13ID23ID3S1RS1R3NS12sp2lo4STKk3LOS4STK03SLO3SPRSS2PP1C4APCPS2sp2r03SPA1q1r1H2H02q02H43sp14SP1MS1R2PP4PPOD3MC13MC2S1R3HIA1h3END1P2hq2p52e12Vq3EVq2h23HV24MONOS2sp3SPRS1e3N1'S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS1R3NS12sp2lo4STKk4STK03SLO3slo4SLO23sp13SP1". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP SPA TPV LFB PPB PKB ENDB BIN BP PE EB BUF0 PPAL PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB HH0 NDL SSH0 SLO1 SLO2 UW0 PPOD PKOD DIMG NB1 STK2 HND HMPERM SIP SIFP BUD BUDF STK3 PKFREE STK4 SETPUB MCOK IDOK BPOK LFN C24H"] Lemma do_pubkey : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Pown,(2.$3.)Pm2x,P,(4.&40.)(5.(4.&8.))PFB,$;.Psp1,$;.Pkv,(4.&40.)Pp5,$;.Pe1,$;.Pinfo,$;.PC,$;.Pg,$58.Ppd,(4.&40.)PqX,(4.&40.)PqY,(4.&40.)PqZ,(4.&40.)PVq,$;.PFq,$;.Pms,$31.P,(4=.VR,VHIA,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,+;065<.+=:558.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1<.(22.$;.$;.)(23.$;.$;.VPKA,(24.VPKA,+10.))(1?.(22.$;.$;.))))(21.(16.VR,)VSI,))(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1?.(22.$;.$;.)))R?.R>.R12.(2<.$3.R11.VLB,)R10.R=.R<.R;.(25.&40.R:.)(25.&40.R9.)(25.&40.VPKA,)(25.&40.R<.)(25.&40.(30.R;.R<.))(25.&40.(24.(59.VPP,+3.)(5:.(5;.VR,))))(25.&40.-4000.)R1.)P,(9.(29.(30.(35.&40.Vsp,)+;0.)R?.)(29.R?.(30.(35.&40.Vsp,)+:0.)))P,(:.$;.(42.R10.+20.)=)P,(:.$;.(42.R12.+40.)=)P,(43.VR,VLB,VLF,R13.+100.)P,(43.VR,(2<.$3.R16.VLB,)VLF,R14.+100.)P,(44.(<.$1.VR,VHIA,Vh,)R15.+100.)P,PB,$;.Pj,$;.P,(37.(22.$;.$;.)(23.$;.$;.R2.R1.)VLF,)(39.(29.(24.R19.+100.)R3.)(29.(24.R3.R2.)R19.))P,Px,$;.P,(<.$1.VR,VHIA,Vh,R1.)(<.$1.VR,VHIA,R1<.R2.)P,(:.$;.(=.$1.VR,VHIA,R1;.)(=.$1.VR,VHIA,Vh,))P,(:.$;.(>.$1.VR,VHIA,R1<.)(>.$1.VR,VHIA,Vh,))P,(:.$;.(?.$1.VR,VHIA,R1=.)(?.$1.VR,VHIA,Vh,))P,(29.(10.$1.VR,VHIA,R1>.)(24.(10.$1.VR,VHIA,Vh,)R?.))P,(29.(11.$1.VR,VHIA,R1?.)(24.(11.$1.VR,VHIA,Vh,)R?.))P,(29.=R11.)P,(29.=R11.)P,(29.(24.(24.R13.(5<.$5=.(30.VEND,VP,)))(4>.=))(45.(30.VEND,VP,)))P,(29.(24.(24.R13.(5>.$5=.(24.Vd,+1.)))(4?.=+1<.))(46.(30.VEND,VP,)Vd,))P,(29.$49.$49.)P,(29.=(5?.(60.$5=.)))P,(29.=(61.(60.$5=.)(24.Vd,+1.)))P,Pa,$;.Pb,$;.P,(29.R2.R1.)(29.(5<.$5=.R3.)(5<.$5=.R2.))P,(33.$1.R26.)P,(15.(16.VR,)VSI,R27.)P,(62.$1.VMT,R28.(2<.$3.R29.VLB,)R21.(63.R20.(64.(24.R21.+<0.)R1?.)(65.(24.R21.+=0.)R1>.R1=.R1<.)))P,(37.$;.R23.$66.)P,(67.R22.$5=.)P,(68.(69.R23.))P,(:.$;.(42.R25.+10.)=)P,Pb,$3.(13.(37.$3.R1.R2?.)(39.(:.$3.R1.(23.$;.$;.R27.+100.))(37.$3.R1.(6:.R26.))))P,(2=.(37.(22.$;.$;.)(23.$;.$;.R27.+100.)(6:.R26.)))P,Pb,$3.P,(37.$3.R1.R31.)(9.(2=.(37.$3.R2.VLB,))(9.(43.VR,VLB,VLF,(3<.$;.$;.R2.)(3=.$;.$;.R2.))(26.=(3=.$;.$;.R2.))))P,(:.$;.(2>.R31.)=)(4:.$1.(4;.$1.VR,VHIA,R33.Vmo0,)(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)R22.)")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros CQH SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq V0 F0q BV BF CNTK CKP0 CKF0 PHIM MI2x SI2x KP2x EI GF APG C16 OWN GNC OWNF C24o.
    ddestruct CQH as (mm & c0 & c1 & c2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & -> & D & PRESB).
    pose proof D as D0.
    ddestruct D0 as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & p1v & ptag & ppad & plen
                   & HHq & FHD & LPKC & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MIq
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & Hp1v & Hp1v2 & PPC & PRES).
    rt_facts.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq. rewrite ETq, ESq in HTOPq.
    pose proof (hm_top asegs R HIA h LB LF m HH0) as HTOP0.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    pose proof (art_data_lo asegs R HIA) as DLOW.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    assert (CIN : In (C, 256) own) by (apply OWN; left; reflexivity).
    assert (CINq : In (C, 256) (own ++ LB)) by (apply in_app_iff; left; exact CIN).
    destruct (OWNF _ CIN) as (CNL & CFR & _). cbn [fst snd] in CFR.
    dpose CFR as (CF0 & CF1 & CF2 & CF3).
    assert (APO : forall b, In b own -> PP + 8 <= fst b \/ fst b + snd b <= PP).
    { intros b Hb. ddestruct (OWNF b Hb) as (_ & FRb & POSb). pose proof (fresh_apart_objA _ _ PP 8 _ FRb CWP ltac:(clear; lia) POSb) as K. clear - K. lia. }
    pose proof (fresh_apart_objA _ _ PP 8 _ CFR CWP ltac:(clear; lia) ltac:(clear; lia)) as APCP.
    pose proof (fresh_apart_objA _ _ PKA 16 _ CFR CWK ltac:(clear; lia) ltac:(clear; lia)) as APCK.
    assert (APCB : C + 256 <= BUF \/ BUF + BLEN <= C) by (apply CF3; apply in_app_iff; left; exact BIN).
    assert (APCF : FB + 256 <= C \/ C + 256 <= FB) by (ddestruct FRSHq as (_ & _ & _ & K); apply K; apply in_app_iff; left; exact CINq).
    destruct (hm_block_bounds hq _ _ _ BUF BLEN HHq ltac:(apply in_app_iff; right; exact BIN)) as (_ & _ & BUFC & BUFI).
    assert (GNEC : forall e, In e (grp_mpds g) -> md_own e = LHeap -> md_p e <> C).
    { intros e He O E. apply GNC. pose proof (grp_blk_inA g e He O) as Hb. rewrite E in Hb.
      assert (I1 : In (C, 4 * md_n e) (own ++ LB)) by (apply in_app_iff; left; apply OWN; right; exact Hb).
      rewrite (nodup_fst_same (own ++ LB) C 256 (4 * md_n e) (HND _ _ _ _ HHq) CINq I1). exact Hb. }
    ddestruct MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6). ddestruct IDOK as (ID1 & ID2 & ID3 & ID4 & ID5 & ID6).
    (* [comment removed for export] *)
    pose proof (own_agree hq own _ m2x mm PRESB HHq APO) as AGR.
    assert (KPm : ecp_keypair_at asegs MT mm (own ++ LB) C (mkKP g (mpd_init (C + 192) pd) (pt_init (C + 208) qX qY qZ))).
    { eapply (ecp_keypair_at_agree asegs MT m2x mm (own ++ LB) (own ++ LB) own); [exact KP2x| exact MI2x| exact MIq| intros b Hb; apply in_app_iff; left; exact Hb| exact AGR| exact CIN|].
      intros e He HO. apply OWN. right. apply grp_blk_inA; [exact (kpi_heap_grpA _ _ _ _ _ _ e He HO)| exact HO]. }
    pose proof (si_path hq _ m2x mm PRESB SI2x) as SIm.
    destruct (proj1 (SIP mm) SIm) as [IDSm [cnt MCm]].
    destruct (BPOK hq _ _ mm HHq MIq) as (bp1 & bp2 & BP1 & BP2 & BI1 & BI2).
    (* [comment removed for export] *)
    destruct (sub_input asegs mm BUF bs p5 (e1 - p5) HBS ltac:(clear - Hp2a BP; lia) ltac:(clear - Hp2e; lia) ltac:(clear - Hp2e HeE EB; lia)) as [HKB KLEN].
    set (kbs := firstn (Z.to_nat (e1 - p5)) (skipn (Z.to_nat (p5 - BUF)) bs)) in HKB, KLEN.
    assert (OKB : aobj asegs AL (hcs asegs R HIA hq) mm p5 (e1 - p5)) by (eapply aobj_sub; [exact OBUF| clear - Hp2a BP; lia| clear - Hp2e HeE EB; lia]).
    (* [comment removed for export] *)
    pose proof (presW_presA asegs R HIA hq LB LF _ _ _ _ _ PRES) as HPe. rewrite ESq in HPe.
    assert (UWm : uwc asegs mm (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs mm (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact HPe| exact UW0| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STK0; lia].
        intros a Ha. apply (proj2 (outside_app _ _ a)). split; [cbn; split; [clear - Ha PPLO SLO NS1 STK0; lia| split; [clear - Ha PKLO SLO NS1 STK0; lia| exact I]]|].
        eapply (disjoint_outside _ (bv_unsigned sp) (hstkhi asegs R HIA h - bv_unsigned sp)); [| clear - Ha; lia].
        apply (si_disjoint_off L SI). right. clear - DLOW ALO LOS SLO NS1 STK0; lia. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact (uwc_nonneg _ _ _ _ _ _ _ UW0)]. }
    assert (SSm : sshad asegs AL mm slo (bv_unsigned sp)) by (eapply (presA_sshad asegs R _ _ _ _ _ _ m mm _ _ HPe); [exact SSH0| exact SLO1| clear - TOP HTOP0; lia]).
    destruct (sshad_split asegs AL mm slo sp1 (bv_unsigned sp) SSm ltac:(clear - SP1 SLO SLO2 NS1 STK0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof SETPUB as SP'. unfold pk_ecc_set_pubkey_stmtA, A_PK_ECC_SET_PUBKEY in SP'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SP' with (h := hq) (LB := own ++ LB) (LF := (FB, 256) :: LF) (PKA := PKA) (info := info) (C := C) (B := p5) (bs := kbs) (g := g)
                      (pd := pd) (qX := qX) (qY := qY) (qZ := qZ) (cnt := cnt) (bp1 := bp1) (bp2 := bp2) (N := ECP_MAX_N) (lo := lo) (d := d + 1) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?KLEN; rewrite ?ETq, ?ESq; unfold ECP_KEYPAIR_SIZE;
        first [ exact HHq | exact HK1 | exact HPKA | exact PKAL | exact PK0 | exact OPKA | exact KPm | exact CINq | exact GF | exact HKB | exact MCm
              | exact BP1 | exact BP2 | exact BI1 | exact BI2 | exact STbelow | exact LOS | exact SSlo | exact SLO1 | exact SLO2 | exact MIq | exact TPV | exact UWm
              | exact CKP0 | exact CKF0 | reflexivity
              | lazymatch goal with
                | |- (length _ + _ <= 512)%nat => cbn [length]; clear - LFN; lia
                | |- client_range _ _ _ PKA 16 => eapply client_range_wsep; [exact CWK| | left; exact PKLO];
                       intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]
                | |- PKA + 16 <= lo \/ _ => left; exact PKLO
                | |- PKA + 16 <= C \/ _ => clear - APCK; lia
                | |- MC + 8 <= PKA \/ _ => clear - PKOD MC1 MC2; lia
                | |- mc_okA _ _ => exact (conj MC1 (conj MC2 (conj MC3 (conj MC4 (conj MC5 MC6)))))
                | |- 0 < p5 => clear - Hp2a BP BUF0; lia
                | |- p5 + _ + 8 <= 2 ^ 47 => clear - Hp2e HeE EB BUFC ACV; lia
                | |- client_range _ _ _ p5 _ => eapply client_range_block; [apply in_app_iff; left; apply in_app_iff; right; exact BIN| clear - Hp2a BP; lia| clear - Hp2e HeE EB; lia]
                | |- p5 + _ <= lo \/ _ => left; clear - Hp2e HeE EB BUFC ALO LOS; lia
                | |- p5 + _ <= C \/ _ => clear - APCB Hp2a Hp2e HeE BP EB; lia
                | |- MC + 8 <= p5 \/ _ => clear - BUFI DIMG MC1 MC2 Hp2a Hp2e HeE BP EB; lia
                | |- _ = 0 \/ aobj _ _ _ _ p5 _ => right; exact OKB
                | |- MC + 8 <= C \/ _ => clear - CF2 MC1 MC2; lia
                | |- img_norz _ _ = true => vm_compute; reflexivity
                | |- MC + 8 <= A_BAD_POINTS \/ _ => right; vm_compute; intros K; discriminate K
                | |- List.NoDup _ => exact (HND _ _ _ _ HHq)
                | |- havol _ _ _ _ + _ <= AVOL_MAX => pose proof (PHIM (e1 - p5) (END - P) ltac:(clear - Hp2a Hp2e HeE; lia)) as MONO; clear - BUD EVq BV MONO; unfold PHIpk, AVOL_CALL in *; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF EFRq BF; unfold FFRpk, fr_charge in *; lia
                | |- cnt24 _ + _ <= C24MAX => rewrite cnt24_app, C24o; ddestruct PKP_C24_facts as (K1 & K2 & K3 & K4); clear - C24H K1 K2 K3 K4; lia
                | |- forall e, In e (grp_mpds g) -> _ -> md_p e <> C => exact GNEC
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- _ => clear - SP1 SP1M SLO STK0 STK4 NS1 NEEDE TOP SPH; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "SPK-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & LB2 & Q' & r & cnt'
                    & E4 & RR & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & KP2 & SGQ & DISQ & SZQ & SUB2 & COV2 & NEW2 & HPKA2 & HMC2).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xb065c)) with (Z_to_bv 64 0xb065c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R. rewrite KLEN in HV2.
    (* [comment removed for export] *)
    set (own' := newb LB LB2).
    assert (SUBL : forall b, In b LB -> In b LB2) by (intros b Hb; apply SUB2; apply in_app_iff; right; exact Hb).
    pose proof (newb_perm LB LB2 (HND _ _ _ _ HH2) NDL SUBL) as PERM. fold own' in PERM.
    destruct (HMPERM _ _ _ _ _ HH2 PERM) as (h3 & HH3 & E3cs & E3top & E3stk & E3flag & E3vol & E3fr & HKI3).
    assert (OWN' : forall b, In b own' <-> b = (C, 256) \/ In b (grp_blocks g) \/ In b (pt_blocks Q')).
    { intros b. unfold own'. rewrite newb_in. split.
      - intros [Hb Hn]. destruct (COV2 b Hb) as [Hb1|Hq]; [| right; right; exact Hq].
        apply in_app_iff in Hb1. destruct Hb1 as [Hb1|Hb1]; [| exfalso; exact (Hn Hb1)].
        apply OWN in Hb1. destruct Hb1 as [E|Hg]; [left; exact E| right; left; exact Hg].
      - intros [E|[Hg|Hq]].
        + subst b. split; [apply SUB2; exact CINq| exact CNL].
        + assert (Ho : In b own) by (apply OWN; right; exact Hg). split; [apply SUB2; apply in_app_iff; left; exact Ho| exact (proj1 (OWNF b Ho))].
        + split; [eapply (kp_blocks_in asegs MT); [exact KP2|]; unfold kp_blocks; cbn [kp_grp kp_d kp_Q]; apply in_or_app; right; apply in_or_app; right; exact Hq|].
          intros HbL. exact (proj1 (NEW2 b Hq) ltac:(apply in_app_iff; right; exact HbL)). }
    assert (HCSq3 : forall x, hcs asegs R HIA hq x -> hcs asegs R HIA h3 x) by (intros x Hx; rewrite E3cs; exact (HCS2 x Hx)).
    assert (HCSh3 : forall x, CS x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCSq3, HCSq, Hx).
    assert (ES3 : hstkhi asegs R HIA h3 = hstkhi asegs R HIA h) by (rewrite E3stk, HS2; exact ESq).
    assert (ET3 : htop asegs R HIA h3 = htop asegs R HIA h) by (rewrite E3top, HT2; exact ETq).
    assert (EF3 : hflag asegs R HIA h3 = hflag asegs R HIA h) by (rewrite E3flag, HF2; exact EFq).
    pose proof (fresh_apart_relist_sg R HIA h3 (own ++ LB) (own' ++ LB) LF m2 FB 256 FRSHq HH3) as FRSH3.
    (* [comment removed for export] *)
    assert (REP2 : pk_rep asegs PK m2 (own' ++ LB) PKA info C own').
    { eapply (pk_rep_frame asegs PK) with (m := m2) (LB := LB2); [| exact MI2| intros b Hb; apply in_app_iff; left; exact Hb| intros a _; reflexivity].
      cbn [PKA_inst PKC_inst pk_rep].
      eapply (ec_rep_introA asegs); [exact EI| | exact MI2| exact (HND _ _ _ _ HH2)| exact KP2| apply SUB2; exact CINq| | | exact C16| clear - CF1 ACV; lia|].
      - intros E0. rewrite E0 in EI. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI. clear - EI. lia.
      - (* [comment removed for export] *)
        intros d1 d2 H1 H2 NE O1 O2. unfold kp_mpds in H1, H2. cbn [kp_grp kp_d kp_Q] in H1, H2.
        assert (CASE : forall e, In e (grp_mpds g ++ mpd_init (C + 192) pd :: pt_mpds Q') -> md_own e = LHeap ->
                         (In e (grp_mpds g) /\ In (md_p e, 4 * md_n e) (own ++ LB)) \/ (In e (pt_mpds Q') /\ ~ In (md_p e, 4 * md_n e) (own ++ LB))).
        { intros e He O. apply in_app_or in He. destruct He as [He|[<-|He]]; [left| cbn in O; discriminate| right].
          - split; [exact He|]. apply in_app_iff. left. apply OWN. right. exact (grp_blk_inA g e He O).
          - split; [exact He|]. exact (proj1 (NEW2 _ (pt_blk_inA Q' e He O))). }
        destruct (CASE d1 H1 O1) as [[G1 I1]|[Q1 N1]]; destruct (CASE d2 H2 O2) as [[G2 I2]|[Q2 N2]].
        + intros E. apply (APG d1 d2 G1 G2 NE O1 O2). injection E as Ea Eb. exact Ea.
        + intros E. apply N2. rewrite <- E. exact I1.
        + intros E. apply N1. rewrite E. exact I2.
        + ddestruct DISQ as (DXY & DXZ & DYZ).
          cbn in Q1, Q2. destruct Q1 as [<-|[<-|[<-|[]]]]; destruct Q2 as [<-|[<-|[<-|[]]]];
            first [ exfalso; apply NE; reflexivity | exact (DXY O1 O2) | exact (DXZ O1 O2) | exact (DYZ O1 O2)
                  | intros E; symmetry in E; revert E; first [exact (DXY O2 O1)| exact (DXZ O2 O1)| exact (DYZ O2 O1)] ].
      - (* [comment removed for export] *)
        intros e He O E. unfold kp_mpds in He. cbn [kp_grp kp_d kp_Q] in He. apply in_app_or in He. destruct He as [He|[<-|He]].
        + apply GNC. rewrite <- E. exact (grp_blk_inA g e He O).
        + cbn in O. discriminate.
        + apply (proj1 (NEW2 (C, 256) ltac:(rewrite <- E; exact (pt_blk_inA Q' e He O)))). exact CINq.
      - (* [comment removed for export] *)
        intros b. rewrite OWN'. unfold kp_blocks. cbn [kp_grp kp_d kp_Q]. cbn [mpd_blk md_own mpd_init app In]. rewrite in_app_iff.
        split; (intros [E|K]; [left; symmetry; exact E| right; exact K]). }
    assert (SI2' : si_P SI m2).
    { apply (proj2 (SIP m2)). split; [| exists cnt'; exact HMC2].
      eapply ids_presA; [exact IDSm| exact HP2| |]; cbn [disjoint_from]; (split; [clear - CF2 ID1 ID2 ID3; lia| split; [unfold A_MUL_COUNT, A_ECP_IDS_DONE, A_ECP_IDS; clear; lia| exact I]]). }
    (* [comment removed for export] *)
    assert (PRESa3 : presW asegs R HIA h3 LB LF (bv_unsigned sp) (arl_stklo R) WXF m m2).
    { eapply A_pk_parse_E.presW_step with (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (FB := FB) (sp1 := sp1) (hq := hq) (LBq := own ++ LB) (W := [(C + 208, C + 208 + 48); (MC, MC + 8)]) (mc := mm);
        first [ exact PRES | exact HP2 | exact HCSq3 | (rewrite E3stk; exact HS2) | eassumption | (clear - SP1; lia) | (intros b Hb; apply in_app_iff; right; exact Hb)
              | lazymatch goal with |- forall x, client_addr _ _ _ x -> _ => idtac end
              | match goal with |- ?g => idtac "PWS-LEFT:" g end ].
      intros x Hc Hx. cbn [outside]. split; [| split; [| exact I]].
      - intros K. apply (fresh_not_clientA R LB LF C 256 (bv_unsigned sp) x CFR ltac:(clear - ALO LOS SLO STK0 NS1; lia) Hc). clear - K. lia.
      - apply (proj1 (outside_app _ _ x)) in Hx. destruct Hx as [_ Hx]. rewrite SIFP in Hx. cbn [outside] in Hx. clear - Hx. tauto. }
    assert (D3 : DINV2' WXF FB sp1 h3 (own' ++ LB) FSH0 kv p5 e1 (Z_to_bv 64 info) (Z_to_bv 64 C) m2).
    { eapply A_pk_parse_E.dinv2_presA with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (hq := hq) (LBq := own ++ LB) (LBp := own ++ LB) (W := [(C + 208, C + 208 + 48); (MC, MC + 8)]) (mc := mm);
        first [ exact D | reflexivity | exact SP1 | exact F64 | exact FRSHq | exact ESq | exact HP2 | exact HH3 | exact HCSq3 | exact ST2 | exact MI2 | exact HPKA2 | exact PRESa3
              | eassumption
              | lazymatch goal with
                | |- forall b, In b LB -> In b (own ++ LB) => intros b Hb; apply in_app_iff; right; exact Hb
                | |- forall A n, FB <= A -> _ -> disjoint_from _ A n => intros A n H1 H2; ddestruct FRSH as (_ & _ & FD2 & _); cbn [disjoint_from]; split; [clear - H1 H2 APCF; lia| split; [clear - H1 H2 FD2 MC1 MC2; lia| exact I]]
                | |- forall A n, sp1 <= A -> disjoint_from _ A n => intros A n H1; cbn [disjoint_from]; split; [clear - H1 CF1 ALO LOS SP1 SLO STK0 NS1; lia| split; [clear - H1 MC2 DLOW ALO LOS SP1 SLO STK0 NS1; lia| exact I]]
                | |- disjoint_from _ PP 8 => cbn [disjoint_from]; split; [clear - APCP; lia| split; [clear - PPOD MC1 MC2; lia| exact I]]
                | |- disjoint_from _ BUF _ => cbn [disjoint_from]; split; [clear - APCB; lia| split; [clear - BUFI DIMG MC1 MC2; lia| exact I]]
                end
              | match goal with |- ?g => idtac "SPK-DINV-LEFT:" g end ]. }
    pose proof (presW_init_at R HIA h3 _ _ (own' ++ LB) LF m2 (bv_unsigned sp) (arl_stklo R) WBP h3 HH3
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb3.
    assert (OWNF' : forall b, In b own' -> ~ In b LB /\ fresh_apart R LB LF (fst b) (snd b) /\ 0 < snd b).
    { intros b Hb. apply OWN' in Hb. destruct Hb as [E|[Hg|Hq]].
      - subst b. exact (OWNF _ CIN).
      - apply OWNF. apply OWN. right. exact Hg.
      - destruct (NEW2 b Hq) as [N1 N2]. split; [intros HbL; apply N1; apply in_app_iff; right; exact HbL|]. split.
        + eapply fresh_apart_frames_mono_sg; [eapply (fresh_apart_blocks_mono R (own ++ LB) LB); [exact N2| intros b' Hb'; apply in_app_iff; right; exact Hb']|].
          intros b' Hb'. eapply fdata_incl; [| exact Hb']. intros fb Hfb. right. exact Hfb.
        + unfold pt_blocks in Hq. apply in_flat_map in Hq. ddestruct Hq as (e & He & Hbe). destruct (MpiClient.mpd_blk_heap e b Hbe) as [O ->]. cbn [snd].
          pose proof (kp_mpds_mpdr asegs MT _ _ _ _ e KP2 ltac:(unfold kp_mpds; cbn [kp_grp kp_d kp_Q]; apply in_or_app; right; right; exact He)) as (_ & _ & _ & _ & _ & HOW).
          rewrite O in HOW. destruct HOW as (N1' & _). clear - N1'. lia. }
    assert (APO' : forall b, In b own' -> PP + 8 <= fst b \/ fst b + snd b <= PP).
    { intros b Hb. ddestruct (OWNF' b Hb) as (_ & FRb & POSb). pose proof (fresh_apart_objA _ _ PP 8 _ FRb CWP ltac:(clear; lia) POSb) as K. clear - K. lia. }
    pose proof (PHIM (e1 - p5) (END - P) ltac:(clear - Hp2a Hp2e HeE; lia)) as MONO.
    assert (EV3 : havol asegs R HIA h3 <= havol asegs R HIA h + (Vq + pk_set_pubkey_PHI ECP_MAX_N (END - P))) by (rewrite E3vol; clear - HV2 EVq MONO; lia).
    assert (EFR3 : hfr asegs R HIA h3 <= hfr asegs R HIA h + (Fq + pk_set_pubkey_FR ECP_MAX_N (d + 1))) by (rewrite E3fr; clear - HFR2 EFRq; lia).
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj (proj2 (HKI3 mo2) HK2) (mo_frame_trans _ _ _ MF1 MF2))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { eapply A_pk_parse_F.seg_D with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (WB := WBP) (hq := h3) (LBq := own' ++ LB) (m2x := m2) (p5 := p5) (r := r);
        first [ exact D3 | exact PRESb3 | exact HCSh3 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact ES3 | exact ET3 | exact RR
              | (intros b Hb; apply in_app_iff; right; exact Hb)
              | (apply wcover_inside; cbn [inside app]; left; clear; lia)
              | eassumption | match goal with |- ?g => idtac "SEGD-PRE-LEFT:" g end ]. }
    cbv beta. intros ms5 [(a1v & a2v & RNZ & CQF)|(R0 & EQ)].
    - eapply (do_free h3 own' m2 FB sp1 kv e1 e1 r info C a1v a2v _ (Vq + pk_set_pubkey_PHI ECP_MAX_N (END - P)) (Fq + pk_set_pubkey_FR ECP_MAX_N (d + 1)));
        first [ exact CQF | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact CFB | exact AP | exact HCSh3 | exact ET3 | exact ES3 | exact EF3
              | exact EV3 | exact EFR3 | exact REP2 | exact SI2' | exact APO'
              | (clear - RR RNZ; lia) | (clear - BV; lia) | (clear - BF; lia) | (unfold PKP_CNT; clear; lia)
              | match goal with |- ?g => idtac "SPK-FREE-LEFT:" g end ].
    - subst r.
      assert (ND3 : List.NoDup own').
      { pose proof (NoDup_map_inv fst _ (HND _ _ _ _ HH3)) as K. exact (NoDup_app_remove_r _ _ K). }
      assert (LEN3 : Z.of_nat (length own') <= CNTk).
      { pose proof (nodup_incl_len own' ((C, 256) :: grp_blocks g ++ pt_blocks Q') ND3
                      ltac:(intros b Hb; apply OWN' in Hb; destruct Hb as [E|[Hg|Hq]]; [left; symmetry; exact E| right; apply in_or_app; left; exact Hg| right; apply in_or_app; right; exact Hq])) as K.
        cbn [length] in K. rewrite app_length in K. pose proof (grp_blocks_len g). pose proof (pt_blocks_len Q'). unfold PKP_CNT. clear - K H H0. lia. }
      assert (C24' : cnt24 own' = 0).
      { apply cnt24_all_out. intros b Hb. apply OWN' in Hb. destruct Hb as [E|[Hg|Hq]].
        - subst b. reflexivity.
        - apply (cnt24_zero_out own b C24o). apply OWN. right. exact Hg.
        - unfold pt_blocks in Hq. apply in_flat_map in Hq. ddestruct Hq as (e & He & Hbe). destruct (MpiClient.mpd_blk_heap e b Hbe) as [O ->]. cbn [snd].
          pose proof (proj1 (Forall_forall _ _) (SZQ eq_refl) e He) as SZe. cbn beta in SZe. unfold ecp_dy_sz, ecp_sz, ECP_MAX_N in SZe.
          unfold win24. apply andb_false_iff. left. apply Z.leb_gt. clear - SZe. lia. }
      eapply (fin_exit h3 own' WXF FB sp1 (Z_to_bv 64 0));
        first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact CFB | exact AP | exact HCSh3 | exact ET3 | exact ES3 | exact EF3 | exact LEN3
              | (intros x Hx; exact Hx)
              | lazymatch goal with
                | |- havol _ _ _ _ <= _ => clear - EV3 BV; unfold PHIpk, AVOL_CALL in BV; lia
                | |- hfr _ _ _ _ <= _ => clear - EFR3 BF; unfold FFRpk, fr_charge in BF; lia
                | |- context [FINQ] =>
                    eapply epiq_mono; [exact EQ|]; (intros mx HHx MIx PWx dd_H; ddestruct dd_H as (PBx & HPPx & HPx & HPKAx));
                    dexists 0, e1, info, C;
                    split; [reflexivity|]; split; [clear; lia|]; split; [exact HPPx|]; split; [exact HPx|]; split; [exact HPKAx|];
                    split; [eapply (pk_rep_frame asegs PK); [exact REP2| exact MIx| intros b Hb; apply in_app_iff; left; exact Hb| exact (own_agree h3 own' _ m2 mx PBx HHx APO')]|];
                    split; [intros K; exfalso; apply K; reflexivity|];
                    split; [exact (si_path h3 _ m2 mx PBx SI2')|];
                    rewrite cnt24_app, C24'; pose proof (Z.div_pos (e1 - P) 5889 ltac:(clear - HPx; lia) ltac:(clear; lia)) as DP; clear - DP; lia
                end
              | match goal with |- ?g => idtac "SPK-FIN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="NDL HND HMPERM"] Lemma relist : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Ph2,(0.$1.VR,VHIA,)PLB2,(2.$3.)PLFx,(2.$3.)Pm2,P,(4.&40.)(5.(4.&8.))P,(6.$1.VR,VHIA,R4.R3.R2.R1.)P,Pb,$3.P,(37.$3.R1.VLB,)(37.$3.R2.R6.)(8.(0.$1.VR,VHIA,)Lh3,(0.$1.VR,VHIA,)(9.(6.$1.VR,VHIA,R1.(2<.$3.(6;.VLB,R6.)VLB,)R5.R4.)(9.(7.$3.R6.(2<.$3.(6;.VLB,R6.)VLB,))(9.(:.P,$;.Sp(<.$1.VR,VHIA,R1.)(<.$1.VR,VHIA,R7.))(9.(:.$;.(=.$1.VR,VHIA,R1.)(=.$1.VR,VHIA,R7.))(9.(:.$;.(>.$1.VR,VHIA,R1.)(>.$1.VR,VHIA,R7.))(9.(:.$;.(?.$1.VR,VHIA,R1.)(?.$1.VR,VHIA,R7.))(9.(:.$;.(10.$1.VR,VHIA,R1.)(10.$1.VR,VHIA,R7.))(9.(:.$;.(11.$1.VR,VHIA,R1.)(11.$1.VR,VHIA,R7.))Pmo,$12.(13.(14.$1.VR,VHIA,R2.R1.)(14.$1.VR,VHIA,R8.R1.)))))))))))")
(* [comment removed for export] *).
  Proof.
    intros h2 LB2 LFx m2 HH2 SUBL. pose proof (newb_perm LB LB2 (HND _ _ _ _ HH2) NDL SUBL) as PERM.
    destruct (HMPERM _ _ _ _ _ HH2 PERM) as (h3 & HH3 & K). exists h3. split; [exact HH3|]. split; [exact PERM| exact K].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L26892418956.1L52806978339.3L62018535662.100000400>00AS2spS1R3HIA2hqS1R". (* [comment removed for export] *)
  #[using="Type"] Lemma dinv2_widen : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "PWX,(2.$20.)PWX',(2.$20.)PFB,$;.Psp1,$;.Phq,(0.$1.VR,VHIA,)PLBq,(2.$3.)Psh,(2.$1=.)Pkv,(4.&40.)Pp2,$;.Pe1,$;.Ppk0,(4.&40.)Ppk1,(4.&40.)Pmm,P,(4.&40.)(5.(4.&8.))P,(6<.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R=.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,Px,$;.P,(41.R>.R1.)(41.R10.R2.)(6<.VR,VHIA,VLB,VLF,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros WX WX' FB sp1 hq LBq sh kv p2 e1 pk0 pk1 mm D HW. unfold A_pk_parse_E.DINV2 in *.
    repeat (lazymatch type of D with ex _ => let x := fresh "x" in destruct D as (x & D); exists x end).
    repeat (lazymatch type of D with _ /\ _ => let K := fresh "K" in destruct D as (K & D); split; [exact K|] end).
    ddestruct D as (P0 & C1' & C2' & C3'). split; [| split; [exact C1'| split; [exact C2'| exact C3']]].
    eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| exact HW].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation SCQ' := (A_pk_parse_F.SCQ R HIA LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP END PKA lo P BUF bs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0>L15320665279.3L21884438016.3L29193539343.5L29195665965.6L30246851835.7L30248983001.7L30249276633.6L36432733781.4L39316637317.0L39332637397.0L51313192214.3L51315318836.5L51315486004.6L59308664168.100000:00B00S00T00U00V00i01601701801901:01;01?S1r3RNZ2RRS2PP1b1KS3END1P2Vq2BV3PH0FFFS3END1P1d2Fq2BF3FR0S1R1C3CF13ACVSSFFFS2EI". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP SPA TPV LFB PPB PKB ENDB BIN BP PE EB BUF0 PPAL PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB HH0 NDL SSH0 SLO1 SLO2 UW0 PPOD PKOD DIMG NB1 STK2 HND HMPERM SIP SIFP BUD BUDF STK3 PKFREE STK4 SETPUB MCOK IDOK BPOK LFN C24H"] Lemma ec_mid : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Pown,(2.$3.)Pm2x,P,(4.&40.)(5.(4.&8.))PFB,$;.Psp1,$;.Pkv,(4.&40.)Pp5,$;.Pe1,$;.Pr,$;.Pinfo,$;.PC,$;.Pg,$58.Ppd,(4.&40.)PqX,(4.&40.)PqY,(4.&40.)PqZ,(4.&40.)PVq,$;.PFq,$;.Pms,$31.P,(6=.VR,VHIA,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1<.(22.$;.$;.)(23.$;.$;.VPKA,(24.VPKA,+10.))(1?.(22.$;.$;.))))(21.(16.VR,)VSI,))(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1?.(22.$;.$;.)))R10.R?.R13.(2<.$3.R12.VLB,)R11.R>.R=.R<.R;.(25.&40.R:.)(25.&40.R9.)R1.)P,(9.(26.(27.(28.+2.+1?.))R<.)(29.R<.=))P,(9.(29.(30.(35.&40.Vsp,)+;0.)R11.)(29.R11.(30.(35.&40.Vsp,)+:0.)))P,(:.$;.(42.R12.+20.)=)P,(:.$;.(42.R14.+40.)=)P,(43.VR,VLB,VLF,R15.+100.)P,(43.VR,(2<.$3.R18.VLB,)VLF,R16.+100.)P,(44.(<.$1.VR,VHIA,Vh,)R17.+100.)P,PB,$;.Pj,$;.P,(37.(22.$;.$;.)(23.$;.$;.R2.R1.)VLF,)(39.(29.(24.R1;.+100.)R3.)(29.(24.R3.R2.)R1;.))P,Px,$;.P,(<.$1.VR,VHIA,Vh,R1.)(<.$1.VR,VHIA,R1>.R2.)P,(:.$;.(=.$1.VR,VHIA,R1=.)(=.$1.VR,VHIA,Vh,))P,(:.$;.(>.$1.VR,VHIA,R1>.)(>.$1.VR,VHIA,Vh,))P,(:.$;.(?.$1.VR,VHIA,R1?.)(?.$1.VR,VHIA,Vh,))P,(29.(10.$1.VR,VHIA,R20.)(24.(10.$1.VR,VHIA,Vh,)R10.))P,(29.(11.$1.VR,VHIA,R21.)(24.(11.$1.VR,VHIA,Vh,)R10.))P,(29.=R12.)P,(29.=R12.)P,(29.(24.(24.R14.(5<.$5=.(30.VEND,VP,)))(4>.=))(45.(30.VEND,VP,)))P,(29.(24.(24.R14.(5>.$5=.(24.Vd,+1.)))(4?.=+1<.))(46.(30.VEND,VP,)Vd,))P,(29.$49.$49.)P,(29.=(5<.$5=.(30.VEND,VP,)))P,(29.=(5>.$5=.(24.Vd,+1.)))P,(29.=(5?.(60.$5=.)))P,(29.=(61.(60.$5=.)(24.Vd,+1.)))P,Pa,$;.Pb,$;.P,(29.R2.R1.)(29.(5<.$5=.R3.)(5<.$5=.R2.))P,(33.$1.R2:.)P,(15.(16.VR,)VSI,R2;.)P,(62.$1.VMT,R2<.(2<.$3.R2=.VLB,)R24.(63.R23.(64.(24.R24.+<0.)R22.)(65.(24.R24.+=0.)R21.R20.R1?.)))P,(37.$;.R26.$66.)P,P,(:.$;.R28.=)(67.R26.$5=.)P,(68.(69.R26.))P,(:.$;.(42.R28.+10.)=)P,Pb,$3.(13.(37.$3.R1.R33.)(39.(:.$3.R1.(23.$;.$;.R2:.+100.))(37.$3.R1.(6:.R29.))))P,(2=.(37.(22.$;.$;.)(23.$;.$;.R2:.+100.)(6:.R29.)))P,Pb,$3.P,(37.$3.R1.R35.)(9.(2=.(37.$3.R2.VLB,))(9.(43.VR,VLB,VLF,(3<.$;.$;.R2.)(3=.$;.$;.R2.))(26.=(3=.$;.$;.R2.))))P,(:.$;.(2>.R35.)=)(4:.$1.(4;.$1.VR,VHIA,R37.Vmo0,)(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)R25.)")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros SC RR SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq V0 F0q BV BF CNTK PH0 FR0 CKP0 CKF0 PHIM MI2x SI2x KP2x EI GF APG C16 OWN GNC OWNF C24o.
    destruct SC as [(a1v & a2v & RNZ & CQF)|(R0 & CQS)].
    - (* [comment removed for export] *)
      pose proof CQF as CQF0. ddestruct CQF0 as (mm & c0 & c1 & c2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & _ & D0 & _).
      ddestruct D0 as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & p1v & ptag & ppad & plen & HHq & _).
      assert (CIN : In (C, 256) own) by (apply OWN; left; reflexivity).
      destruct (OWNF _ CIN) as (_ & (_ & CF1 & _) & _). cbn [fst snd] in CF1. pose proof (alloc_ceiling_val R) as ACV.
      assert (REP2 : pk_rep asegs PK m2x (own ++ LB) PKA info C own).
      { cbn [PKA_inst PKC_inst pk_rep].
        eapply (ec_rep_introA asegs); [exact EI| | exact MI2x| exact (HND _ _ _ _ HHq)| exact KP2x| apply in_app_iff; left; exact CIN| | | exact C16| clear - CF1 ACV; lia|].
        - intros E0. rewrite E0 in EI. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI. clear - EI. lia.
        - intros d1 d2 H1 H2 NE O1 O2 E. apply (APG d1 d2 (kpi_heap_grpA _ _ _ _ _ _ d1 H1 O1) (kpi_heap_grpA _ _ _ _ _ _ d2 H2 O2) NE O1 O2). injection E as Ea Eb. exact Ea.
        - intros e He O E. apply GNC. rewrite <- E. exact (grp_blk_inA g e (kpi_heap_grpA _ _ _ _ _ _ e He O) O).
        - intros b. rewrite OWN, kpi_blocksA. cbn [In]. split; intros [K|K]; first [left; symmetry; exact K| right; exact K]. }
      assert (APO : forall b, In b own -> PP + 8 <= fst b \/ fst b + snd b <= PP).
      { intros b Hb. ddestruct (OWNF b Hb) as (_ & FRb & POSb). pose proof (fresh_apart_objA _ _ PP 8 _ FRb CWP ltac:(clear; lia) POSb) as K. clear - K. lia. }
      eapply (do_free hq own m2x FB sp1 kv p5 e1 r info C a1v a2v _ Vq Fq);
        first [ exact CQF | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSHq | exact CFB | exact AP | exact HCSq | exact ETq | exact ESq | exact EFq
              | exact EVq | exact EFRq | exact REP2 | exact SI2x | exact APO
              | (clear - RR RNZ; lia) | (clear - BV PH0; lia) | (clear - BF FR0; lia) | (unfold PKP_CNT; clear; lia)
              | match goal with |- ?g => idtac "ECMID-FREE-LEFT:" g end ].
    - eapply (do_pubkey hq own m2x FB sp1 kv p5 e1 info C g pd qX qY qZ Vq Fq);
        first [ exact CQS | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSHq | exact CFB | exact AP | exact HCSq | exact ETq | exact ESq | exact EFq
              | exact EVq | exact EFRq | exact V0 | exact F0q | exact BV | exact BF | exact CNTK | exact CKP0 | exact CKF0 | exact PHIM | exact MI2x | exact SI2x | exact KP2x
              | exact EI | exact (GF R0) | exact APG | exact C16 | exact OWN | exact GNC | exact OWNF | exact C24o
              | match goal with |- ?g => idtac "ECMID-SPK-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis STK5 : 176 + (176 + ECP_GROUP_LOAD_STACK_A) + arl_need_ecp R <= STKk.
  Hypothesis USERFC : pk_use_ecparams_rfc8410_stmtA asegs R HIA MT A_CA A_ONE A_EC_INFOS A_PK_USE_ECPARAMS_RFC8410.

  (* [comment removed for export] *)
  Ltac ctx_block_facts :=
    lazymatch goal with CFR : fresh_apart R LB LF ?C ?SZ |- _ =>
      pose proof CFR as (CF0 & CF1 & CF2 & CF3);
      pose proof (fresh_apart_objA _ _ PP 8 _ CFR CWP ltac:(clear; lia) ltac:(clear; lia)) as APCP;
      pose proof (fresh_apart_objA _ _ PKA 16 _ CFR CWK ltac:(clear; lia) ltac:(clear; lia)) as APCK;
      assert (APCB : C + SZ <= BUF \/ BUF + BLEN <= C) by (apply CF3; apply in_app_iff; left; exact BIN)
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0?L10433001147.8 L11259844057.3 L11260008665.4 L1540877545.3  L16370432801.0 L17665920644.3 L18330401141.3 L19965341046.15L248989856.6   L25281032412.5 L28248436663.3 L30448823313.7 L30448823440.16L30832519840.6 L32586543723.0 L32955626683.8 L3480690467.15 L35194455852.3 L36021046677.2 L38948636245.0 L39332637397.0 L40887902202.11L40888062714.12L43300649301.0 L48132467214.9 L51042627313.10L5214639477.3  L52438553431.15L57218308313.3 L5754760513.4  L59308628433.2 L61276508112.6 L62018535662.1 L6249365241.6  L63948500217.0 L66078761348.5 L66078928004.6 L66081091227.4 L66564204126.6 L66564434782.7 L66566235201.6 L66566237265.5 L66567143876.2 L9218375351.2  L9356559676.13 L957827166.0   00000J00V00W00c00d00m01801P01Q01R01Y01n02f02g02h03D03N03Z03b03c03d04H05005105T05U05`06?06J06Y06_06`06c06o07007107207?07@07A07B07Q07Y07`08S08TS1R3HIA1h2hq2Vq3EVq2h23HV2S2Fq3F0q3FRGFS2sp3sp13SP1SS1R1C3CF2S2PP1C4APCPS1R3HIA1h2sp3TOP3sp13SP1SFS1C1x1KS2FB1C4APCF1A1n2H12H2S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp11C3SP13ALO3CF11A1n2H1SSS1R3HIA1h2hq2Fq4EFRq2h24HFR2S3sp14SP1MS3PKA1C4APCKS2LF3LFNSSS1R3HIA1h3END1P3BUD2hq2Vq3EVq2BV3PH0S1R3HIA1h3END1P1d4BUDF2hq2Fq4EFRq2BF3FR0SS1R3NS12sp2lo4STKk3LOS4STK03SLO3ALOFS2PP1C4APCPS1R2sp2lo4STKk3SLO4STK53sp13SP1S2Vq2V03PHGS3BUF2bs1C4APCBS1C2K2SS1RS2LB4C24H2K4SFFS3END1P2Vq2BVFFFS3END1P1d2Fq2BFS2id3IDVS1e3N1'S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP SPA TPV LFB PPB PKB ENDB BIN BP PE EB BUF0 PPAL PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB HH0 NDL SSH0 SLO1 SLO2 UW0 PPOD PKOD DIMG NB1 STK2 HND HMPERM SIP SIFP BUD BUDF STK3 PKFREE STK4 SETPUB MCOK IDOK BPOK LFN C24H STK5 USERFC"] Lemma do_group : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Pm2x,P,(4.&40.)(5.(4.&8.))PFB,$;.Psp1,$;.Pkv,(4.&40.)Pp5,$;.Pe1,$;.Pinfo,$;.PC,$;.Pid,$;.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)Ppd,(4.&40.)PqX,(4.&40.)PqY,(4.&40.)PqZ,(4.&40.)PVq,$;.PFq,$;.Pms,$31.P,(4=.VR,VHIA,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,+;0560.+;0:=4.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1<.(22.$;.$;.)(23.$;.$;.VPKA,(24.VPKA,+10.))(1?.(22.$;.$;.))))(21.(16.VR,)VSI,))(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1?.(22.$;.$;.)))R18.R17.R1:.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R12.+100.)(1?.(22.$;.$;.)))VLB,)R19.R16.R15.R14.(25.&40.R13.)(25.&40.R12.)(25.&40.(24.R18.+60.))(25.&40.R11.)(25.&40.VPKA,)(25.&40.(5:.(5;.VR,)))(25.&40.-4000.)R1.)P,(39.(:.$;.R12.+9.)(:.$;.R12.+=.))P,(9.(29.(30.(35.&40.Vsp,)+;0.)R19.)(29.R19.(30.(35.&40.Vsp,)+:0.)))P,(:.$;.(42.R1:.+20.)=)P,(:.$;.(42.R1<.+40.)=)P,(43.VR,VLB,VLF,R1=.+100.)P,(43.VR,(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R18.+100.)(1?.(22.$;.$;.)))VLB,)VLF,R1>.+100.)P,(44.(<.$1.VR,VHIA,Vh,)R1?.+100.)P,PB,$;.Pj,$;.P,(37.(22.$;.$;.)(23.$;.$;.R2.R1.)VLF,)(39.(29.(24.R23.+100.)R3.)(29.(24.R3.R2.)R23.))P,Px,$;.P,(<.$1.VR,VHIA,Vh,R1.)(<.$1.VR,VHIA,R25.R2.)P,(:.$;.(=.$1.VR,VHIA,R24.)(=.$1.VR,VHIA,Vh,))P,(:.$;.(>.$1.VR,VHIA,R25.)(>.$1.VR,VHIA,Vh,))P,(:.$;.(?.$1.VR,VHIA,R26.)(?.$1.VR,VHIA,Vh,))P,(29.(10.$1.VR,VHIA,R27.)(24.(10.$1.VR,VHIA,Vh,)R10.))P,(29.(11.$1.VR,VHIA,R28.)(24.(11.$1.VR,VHIA,Vh,)R10.))P,(29.=R12.)P,(29.=R12.)P,(29.(24.(24.(24.R14.$6>.)(5<.$5=.(30.VEND,VP,)))(4>.=))(45.(30.VEND,VP,)))P,(29.(24.(24.(24.R14.$6?.)(5>.$5=.(24.Vd,+1.)))(4?.=+1<.))(46.(30.VEND,VP,)Vd,))P,(29.$49.$49.)P,(29.=(5<.$5=.(30.VEND,VP,)))P,(29.=(5>.$5=.(24.Vd,+1.)))P,(29.=(5?.(60.$5=.)))P,(29.=(61.(60.$5=.)(24.Vd,+1.)))P,Pa,$;.Pb,$;.P,(29.R2.R1.)(29.(5<.$5=.R3.)(5<.$5=.R2.))P,(33.$1.R32.)P,(15.(16.VR,)VSI,R33.)P,(62.$1.VMT,R34.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R2=.+100.)(1?.(22.$;.$;.)))VLB,)R2=.(70.R2=.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.))P,(37.$;.R2?.$66.)P,(:.$;.(42.R2?.+10.)=)P,(43.VR,VLB,VLF,R30.+100.)(4:.$1.(4;.$1.VR,VHIA,R39.Vmo0,)(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)R20.)")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros CQH IDV SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq V0 F0q BV BF CNTK PH0 FR0 CKP0 CKF0 PHIM MI2x SI2x KP2x EI C16 CFR.
    ddestruct CQH as (mm & c0 & c1 & c2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & -> & D & PRESB).
    pose proof D as D0.
    ddestruct D0 as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & p1v & ptag & ppad & plen
                   & HHq & FHD & LPKC & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MIq
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & Hp1v & Hp1v2 & PPC & PRES).
    rt_facts.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq. rewrite ETq, ESq in HTOPq.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    pose proof (art_data_lo asegs R HIA) as DLOW.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    ctx_block_facts.
    assert (CINq : In (C, 256) ([(C, 256)] ++ LB)) by (left; reflexivity).
    assert (APCF : FB + 256 <= C \/ C + 256 <= FB) by (ddestruct FRSHq as (_ & _ & _ & K); apply K; apply in_app_iff; left; exact CINq).
    assert (CNL : ~ In (C, 256) LB) by (intros K; pose proof (CF3 C 256 ltac:(apply in_app_iff; left; exact K)) as K2; clear - K2; lia).
    assert (APO : forall b, In b [(C, 256)] -> PP + 8 <= fst b \/ fst b + snd b <= PP) by (intros b [<-|[]]; cbn [fst snd]; clear - APCP; lia).
    (* [comment removed for export] *)
    pose proof (own_agree hq [(C, 256)] _ m2x mm PRESB HHq APO) as AGR.
    assert (KPm : ecp_keypair_at asegs MT mm ([(C, 256)] ++ LB) C (kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ)).
    { eapply (ecp_keypair_at_agree asegs MT m2x mm _ _ [(C, 256)]); [exact KP2x| exact MI2x| exact MIq| intros b Hb; apply in_app_iff; left; exact Hb| exact AGR| left; reflexivity|].
      intros e He HO. exfalso. clear - He HO. unfold kp_mpds, kp_init, grp_mpds, grp_init, pt_mpds, pt_init in He. cbn in He.
      repeat (destruct He as [<-|He]; [cbn in HO; discriminate|]). destruct He. }
    pose proof (si_path hq _ m2x mm PRESB SI2x) as SIm.
    assert (PHG : 0 <= pk_set_group_PHI) by (unfold pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
    assert (FRG : 0 <= pk_set_group_FR) by (unfold pk_set_group_FR, group_load_FRn, calls_FR, fr_charge; clear; lia).
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq ([(C, 256)] ++ LB) LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBq & INF & INH & IND & APq & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    pose proof USERFC as SG'. unfold pk_use_ecparams_rfc8410_stmtA, A_PK_USE_ECPARAMS_RFC8410 in SG'.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    frame_aobj FSHX (FB + 96) 3%nat as OPAR.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply SG' with (h := hq) (LB := [(C, 256)] ++ LB) (LF := (FB, 256) :: LF) (PKA := PKA) (info := info) (C := C) (id := id) (lo := lo)
                      (idpad := idpad) (pP := pP) (pA := pA) (pB := pB) (pX := pX) (pY := pY) (pZ := pZ) (pN := pN) (hpad := hpad) (pd := pd) (qX := qX) (qY := qY) (qZ := qZ)
                      (PRM := FB + 96) (tag := ptag) (pad := ppad) (len := plen) (pv := Z_to_bv 64 pp);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?ETq, ?ESq; unfold ECP_KEYPAIR_SIZE;
        first [ exact HHq | exact HK1 | exact HPKA | exact PKAL | exact PK0 | exact EI | exact OPKA | exact KPm | exact CINq | exact STbelow | exact LOS | exact MIq | exact TPV | reflexivity
              | exact OPAR | exact (proj1 LPAR)
              | lazymatch goal with
                | |- (length _ < 512)%nat => cbn [length]; clear - LFN; lia
                | |- client_range _ _ _ PKA 16 => eapply client_range_wsep; [exact CWK| | left; exact PKLO];
                       intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]
                | |- PKA + 16 <= lo \/ _ => left; exact PKLO
                | |- PKA + 16 <= C \/ _ => clear - APCK; lia
                | |- 0 <= id < 2 ^ 31 => clear - IDV; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD EVq BV PH0; unfold PHIpk, AVOL_CALL in *; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF EFRq BF FR0; unfold FFRpk, fr_charge in *; lia
                | |- cnt24 _ + _ <= C24MAX => cbn [app]; rewrite cnt24_cons_small by (clear; lia); ddestruct PKP_C24_facts as (K1 & K2 & K3 & K4); clear - C24H K1 K2 K3 K4; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- (FB + 96) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                | |- 0 < FB + 96 => clear - F0; lia
                | |- FB + 96 + 24 <= lo \/ _ => left; clear - FBLO; lia
                | |- _ => clear - SP1 SP1M SLO STK0 STK5 NS1 NEEDE TOP; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "SG-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). cbv zeta in PO.
    destruct PO as [(TGL & PO)|(TG0 & LN0 & PO)].
    { ddestruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & E4 & HK2 & MF2 & A0E & MU2 & WM2 & MI2 & ST2 & HH2).
      injection E4 as Ems Emo. subst ms4 mo4 qa0.
      replace (ret_pc (Z_to_bv 64 0xb0560)) with (Z_to_bv 64 0xb0560 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      rewrite (unsigned_lit sp1) in ST2, MU2 by exact SP1R.
      assert (HP2 : presA asegs R ([(C, 256)] ++ LB) ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [] mm m2).
      { eapply (presA_drop_below asegs R HIA hq ([(C, 256)] ++ LB) ((FB, 256) :: LF) [] lo sp1 mm mm m2 sp1 HHq); [| clear; lia| exact LOS].
        eapply (presA_of_munch asegs R ([(C, 256)] ++ LB) ((FB, 256) :: LF) _ _ _ _ mm m2 (hcs asegs R HIA hq) (hcs_ok asegs R HIA hq)); [| | exact MU2| exact WM2].
        - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
          eapply crange_sub; [exact (hcs_stack asegs R HIA hq)| clear - LOS; lia| rewrite ESq; clear - HTOPq TOP SP1; lia].
        - intros cx Hc. eapply cshd_hcs; [exact HHq| apply Z.le_refl| exact Hc]. }
      assert (HPK2 : rw_cells asegs m2 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)]).
      { eapply (presA_rw_cells asegs R); [exact HP2| exact HPKA| | exact I].
        change (Z.of_nat (cells_size _)) with 16.
        eapply client_range_wsep; [exact CWK| | left; exact PKLO].
        intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]. }
      assert (PRESa2 : presW asegs R HIA hq LB LF (bv_unsigned sp) (arl_stklo R) WXF m m2).
      { eapply A_pk_parse_E.presW_step with (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (FB := FB) (sp1 := sp1) (hq := hq) (h2 := hq) (LBq := [(C, 256)] ++ LB) (W := []) (mc := mm) (m2 := m2);
          first [ exact PRES | exact HP2 | (clear - SP1; lia) | (intros b Hb; apply in_app_iff; right; exact Hb) | (intros x _ _; exact I) | (intros x Hx; exact Hx) | reflexivity
                | eassumption | match goal with |- ?g => idtac "RFCERR-PWS-LEFT:" g end ]. }
      assert (D2 : DINV2' WXF FB sp1 hq ([(C, 256)] ++ LB) FSH0 kv p5 e1 (Z_to_bv 64 info) (Z_to_bv 64 C) m2).
      { eapply A_pk_parse_E.dinv2_presA with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (hq := hq) (LBq := [(C, 256)] ++ LB)
            (LBp := [(C, 256)] ++ LB) (LB2 := [(C, 256)] ++ LB) (h2 := hq) (W := []) (mc := mm) (m2 := m2);
          first [ exact D | reflexivity | exact SP1 | exact F64 | exact FRSHq | exact ESq | exact HP2 | exact HH2 | exact ST2 | exact MI2 | exact HPK2 | exact PRESa2
                | (intros b Hb; apply in_app_iff; right; exact Hb) | (intros x Hx; exact Hx)
                | (intros A n _ _; exact I) | (intros A n _; exact I) | exact I
                | eassumption | match goal with |- ?g => idtac "RFCERR-DINV-LEFT:" g end ]. }
      pose proof (presW_init_at R HIA hq _ _ ([(C, 256)] ++ LB) LF m2 (bv_unsigned sp) (arl_stklo R) WBP hq HH2
                    ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb2.
      assert (SI2e : si_P SI m2).
      { eapply (si_heap_presx asegs L SI); [exact SIm| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)| intros a _; exact I]. }
      assert (GB0 : forall b, ~ In b (grp_blocks (grp_init C idpad pP pA pB pX pY pZ pN hpad))).
      { intros b Hb. unfold grp_blocks in Hb. apply in_flat_map in Hb. ddestruct Hb as (e & He & Hbe). destruct (MpiClient.mpd_blk_heap e b Hbe) as [O _].
        clear - He O. unfold grp_mpds, grp_init in He. cbn in He. repeat (destruct He as [<-|He]; [cbn in O; discriminate|]). destruct He. }
      assert (KP3 : ecp_keypair_at asegs MT m2 ([(C, 256)] ++ LB) C (kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ)).
      { eapply (ecp_keypair_at_agree asegs MT mm m2 _ _ [(C, 256)]); [exact KPm| exact MIq| exact MI2| intros b Hb; apply in_app_iff; left; exact Hb| | left; reflexivity|].
        - intros a (b & Hb & Ha). destruct Hb as [<-|[]]. cbn [fst snd] in Ha. apply (MU2 (wa a)). cbn [outside]. split; [| exact I].
          unfold wa. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; clear - Ha CF0 CF1 ACV; lia).
          clear - Ha CF1 ALO LOS; lia.
        - intros e He HO. exfalso. clear - He HO. unfold kp_mpds, kp_init, grp_mpds, grp_init, pt_mpds, pt_init in He. cbn in He.
          repeat (destruct He as [<-|He]; [cbn in HO; discriminate|]). destruct He. }
      assert (OWNe : forall b, In b [(C, 256)] <-> b = (C, 256) \/ In b (grp_blocks (grp_init C idpad pP pA pB pX pY pZ pN hpad))).
      { intros b. split; [intros [<-|[]]; left; reflexivity| intros [<-|Hg]; [left; reflexivity| exfalso; exact (GB0 b Hg)]]. }
      assert (OWNFe : forall b, In b [(C, 256)] -> ~ In b LB /\ fresh_apart R LB LF (fst b) (snd b) /\ 0 < snd b).
      { intros b [<-|[]]. cbn [fst snd]. split; [exact CNL|]. split; [exact CFR| clear; lia]. }
      assert (C24e : cnt24 [(C, 256)] = 0) by (apply cnt24_all_out; intros b [<-|[]]; reflexivity).
      assert (RRe : -2^31 < MBEDTLS_ERR_PK_KEY_INVALID_FORMAT <= 0) by (unfold MBEDTLS_ERR_PK_KEY_INVALID_FORMAT; clear; lia).
      assert (GFe : MBEDTLS_ERR_PK_KEY_INVALID_FORMAT = 0 -> grp_factsA (grp_init C idpad pP pA pB pX pY pZ pN hpad) ECP_MAX_N).
      { intros K. exfalso. unfold MBEDTLS_ERR_PK_KEY_INVALID_FORMAT in K. clear - K. lia. }
      assert (APGe : mpds_apart (grp_mpds (grp_init C idpad pP pA pB pX pY pZ pN hpad))).
      { intros d1 d2 H1 _ _ O1 _. exfalso. clear - H1 O1. unfold grp_mpds, grp_init in H1. cbn in H1.
        repeat (destruct H1 as [<-|H1]; [cbn in O1; discriminate|]). destruct H1. }
      assert (EV3e : havol asegs R HIA hq <= havol asegs R HIA h + (Vq + pk_set_group_PHI)) by (clear - EVq PHG; lia).
      assert (EFR3e : hfr asegs R HIA hq <= hfr asegs R HIA h + (Fq + pk_set_group_FR)) by (clear - EFRq FRG; lia).
      apply (aevtA_enter asegs (KF asegs R HIA hq mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
      { eapply A_pk_parse_F.seg_C with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (WB := WBP) (hq := hq) (LBq := [(C, 256)] ++ LB) (m2x := m2)
            (p5 := p5) (r := MBEDTLS_ERR_PK_KEY_INVALID_FORMAT);
          first [ exact D2 | exact PRESb2 | exact HCSq | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSHq | exact ESq | exact ETq | exact RRe
                | (intros b Hb; apply in_app_iff; right; exact Hb)
                | eassumption | match goal with |- ?g => idtac "RFCERR-SEGC-LEFT:" g end ]. }
      cbv beta. intros ms5 SC.
      eapply (ec_mid hq [(C, 256)] m2 FB sp1 kv p5 e1 MBEDTLS_ERR_PK_KEY_INVALID_FORMAT info C (grp_init C idpad pP pA pB pX pY pZ pN hpad) pd qX qY qZ (Vq + pk_set_group_PHI) (Fq + pk_set_group_FR));
        first [ exact SC | exact RRe | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSHq | exact CFB | exact AP | exact HCSq | exact ETq | exact ESq | exact EFq
              | exact EV3e | exact EFR3e | exact CNTK | exact PH0 | exact FR0 | exact CKP0 | exact CKF0 | exact PHIM | exact MI2 | exact SI2e | exact KP3
              | exact EI | exact GFe | exact APGe | exact C24e | exact C16 | exact OWNe | exact (GB0 (C, 256)) | exact OWNFe
              | (clear - V0 PHG; lia) | (clear - F0q FRG; lia) | (clear - BV; lia) | (clear - BF; lia)
              | match goal with |- ?g => idtac "RFCERR-MID-LEFT:" g end ]. }
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & r & g' & NB & LB2
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & LEQ & LNEW & KP2 & AP2 & GB2 & RES & HPKA2).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xb0560)) with (Z_to_bv 64 0xb0560 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R. unfold ECP_GROUP_SIZE in HP2. cbn [kp_d kp_Q kp_init] in KP2.
    assert (RR : -2^31 < r <= 0).
    { clear - RES. unfold gl_result, MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE, P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED in RES. destruct RES as [(K & _)|[(K & _)|[(K & _)|(K & _)]]]; rewrite K; lia. }
    (* [comment removed for export] *)
    assert (SUBL : forall b, In b LB -> In b LB2) by (intros b Hb; apply LEQ; right; apply in_app_iff; right; exact Hb).
    destruct (relist h2 LB2 _ m2 HH2 SUBL) as (h3 & HH3 & PERM & E3cs & E3top & E3stk & E3flag & E3vol & E3fr & HKI3).
    set (own' := newb LB LB2) in *.
    assert (OWN' : forall b, In b own' <-> b = (C, 256) \/ In b (grp_blocks g')).
    { intros b. unfold own'. rewrite newb_in, GB2. split.
      - intros [Hb Hn]. apply LEQ in Hb. destruct Hb as [Hb|Hb]; [right; exact Hb|]. destruct Hb as [E|Hb]; [left; symmetry; exact E| exfalso; exact (Hn Hb)].
      - intros [E|Hb]; [subst b; split; [apply LEQ; right; left; reflexivity| exact CNL]|].
        split; [apply LEQ; left; exact Hb| intros HbL; exact (proj1 (LNEW b Hb) ltac:(right; exact HbL))]. }
    assert (GNC : ~ In (C, 256) (grp_blocks g')) by (rewrite GB2; intros K; exact (proj1 (LNEW _ K) ltac:(left; reflexivity))).
    assert (HCSq3 : forall x, hcs asegs R HIA hq x -> hcs asegs R HIA h3 x) by (intros x Hx; rewrite E3cs; exact (HCS2 x Hx)).
    assert (HCSh3 : forall x, CS x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCSq3, HCSq, Hx).
    assert (ES3 : hstkhi asegs R HIA h3 = hstkhi asegs R HIA h) by (rewrite E3stk, HS2; exact ESq).
    assert (ET3 : htop asegs R HIA h3 = htop asegs R HIA h) by (rewrite E3top, HT2; exact ETq).
    assert (EF3 : hflag asegs R HIA h3 = hflag asegs R HIA h) by (rewrite E3flag, HF2; exact EFq).
    pose proof (fresh_apart_relist_sg R HIA h3 ([(C, 256)] ++ LB) (own' ++ LB) LF m2 FB 256 FRSHq HH3) as FRSH3.
    assert (KP3 : ecp_keypair_at asegs MT m2 (own' ++ LB) C (mkKP g' (mpd_init (C + 192) pd) (pt_init (C + 208) qX qY qZ))).
    { eapply ecp_keypair_at_LB_mono; [exact KP2| intros b Hb; exact (Permutation_in b PERM Hb)]. }
    assert (SI2' : si_P SI m2).
    { eapply (si_heap_presx asegs L SI); [exact SIm| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)|].
      intros a Ha. apply (si_outside1 L SI C 192 a); [clear - CF2; lia| exact Ha]. }
    assert (PRESa3 : presW asegs R HIA h3 LB LF (bv_unsigned sp) (arl_stklo R) WXF m m2).
    { eapply A_pk_parse_E.presW_step with (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (FB := FB) (sp1 := sp1) (hq := hq) (LBq := [(C, 256)] ++ LB) (W := [(C, C + 192)]) (mc := mm);
        first [ exact PRES | exact HP2 | exact HCSq3 | (rewrite E3stk; exact HS2) | eassumption | (clear - SP1; lia) | (intros b Hb; apply in_app_iff; right; exact Hb)
              | lazymatch goal with |- forall x, client_addr _ _ _ x -> _ => idtac end
              | match goal with |- ?g => idtac "PWS-LEFT:" g end ].
      intros x Hc _. cbn [outside]. split; [| exact I].
      intros K. apply (fresh_not_clientA R LB LF C 256 (bv_unsigned sp) x CFR ltac:(clear - ALO LOS SLO STK0 NS1; lia) Hc). clear - K. lia. }
    assert (D3 : DINV2' WXF FB sp1 h3 (own' ++ LB) FSH0 kv p5 e1 (Z_to_bv 64 info) (Z_to_bv 64 C) m2).
    { eapply A_pk_parse_E.dinv2_presA with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (hq := hq) (LBq := [(C, 256)] ++ LB) (LBp := [(C, 256)] ++ LB) (W := [(C, C + 192)]) (mc := mm);
        first [ exact D | reflexivity | exact SP1 | exact F64 | exact FRSHq | exact ESq | exact HP2 | exact HH3 | exact HCSq3 | exact ST2 | exact MI2 | exact HPKA2 | exact PRESa3
              | eassumption
              | lazymatch goal with
                | |- forall b, In b LB -> In b _ => intros b Hb; apply in_app_iff; right; exact Hb
                | |- forall A n, FB <= A -> _ -> disjoint_from _ A n => intros A n H1 H2; cbn [disjoint_from]; split; [clear - H1 H2 APCF; lia| exact I]
                | |- forall A n, sp1 <= A -> disjoint_from _ A n => intros A n H1; cbn [disjoint_from]; split; [clear - H1 CF1 ALO LOS SP1 SLO STK0 NS1; lia| exact I]
                | |- disjoint_from _ PP 8 => cbn [disjoint_from]; split; [clear - APCP; lia| exact I]
                | |- disjoint_from _ BUF _ => cbn [disjoint_from]; split; [clear - APCB; lia| exact I]
                end
              | match goal with |- ?g => idtac "SG-DINV-LEFT:" g end ]. }
    pose proof (presW_init_at R HIA h3 _ _ (own' ++ LB) LF m2 (bv_unsigned sp) (arl_stklo R) WBP h3 HH3
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb3.
    assert (OWNF' : forall b, In b own' -> ~ In b LB /\ fresh_apart R LB LF (fst b) (snd b) /\ 0 < snd b).
    { intros b Hb. apply OWN' in Hb. destruct Hb as [E|Hg].
      - subst b. cbn [fst snd]. split; [exact CNL|]. split; [exact CFR| clear; lia].
      - rewrite GB2 in Hg. destruct (LNEW b Hg) as [N1 N2]. split; [intros HbL; apply N1; right; exact HbL|]. split.
        + eapply fresh_apart_frames_mono_sg; [eapply (fresh_apart_blocks_mono R ([(C, 256)] ++ LB) LB); [exact N2| intros b' Hb'; apply in_app_iff; right; exact Hb']|].
          intros b' Hb'. eapply fdata_incl; [| exact Hb']. intros fb Hfb. right. exact Hfb.
        + rewrite <- GB2 in Hg. unfold grp_blocks in Hg. apply in_flat_map in Hg. ddestruct Hg as (e & He & Hbe). destruct (MpiClient.mpd_blk_heap e b Hbe) as [O ->]. cbn [snd].
          pose proof (kp_mpds_mpdr asegs MT _ _ _ _ e KP2 ltac:(unfold kp_mpds; cbn [kp_grp kp_d kp_Q]; apply in_or_app; left; exact He)) as (_ & _ & _ & _ & _ & HOW).
          rewrite O in HOW. destruct HOW as (N1' & _). clear - N1'. lia. }
    assert (C24' : cnt24 own' = 0).
    { apply cnt24_all_out. intros b Hb. apply OWN' in Hb. destruct Hb as [E|Hg]; [subst b; reflexivity|].
      rewrite GB2 in Hg. exact (cnt24_zero_out NB b (gl_cnt24A _ _ _ _ _ _ _ RES) Hg). }
    assert (GF3 : r = 0 -> grp_factsA g' ECP_MAX_N).
    { intros R0. rewrite R0 in RES. eapply (grp_factsA_of_gl_result_at R HIA h2 LB2 _ m2 MT id C g' NB HH2); [exact (proj1 KP2)| exact RES]. }
    assert (EV3 : havol asegs R HIA h3 <= havol asegs R HIA h + (Vq + pk_set_group_PHI)) by (rewrite E3vol; clear - HV2 EVq; lia).
    assert (EFR3 : hfr asegs R HIA h3 <= hfr asegs R HIA h + (Fq + pk_set_group_FR)) by (rewrite E3fr; clear - HFR2 EFRq; lia).
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj (proj2 (HKI3 mo2) HK2) (mo_frame_trans _ _ _ MF1 MF2))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { eapply A_pk_parse_F.seg_C with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (WB := WBP) (hq := h3) (LBq := own' ++ LB) (m2x := m2) (p5 := p5) (r := r);
        first [ exact D3 | exact PRESb3 | exact HCSh3 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact ES3 | exact ET3 | exact RR
              | (intros b Hb; apply in_app_iff; right; exact Hb)
              | eassumption | match goal with |- ?g => idtac "SEGC-PRE-LEFT:" g end ]. }
    cbv beta. intros ms5 SC.
    eapply (ec_mid h3 own' m2 FB sp1 kv p5 e1 r info C g' pd qX qY qZ (Vq + pk_set_group_PHI) (Fq + pk_set_group_FR));
      first [ exact SC | exact RR | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact CFB | exact AP | exact HCSh3 | exact ET3 | exact ES3 | exact EF3
            | exact EV3 | exact EFR3 | exact CNTK | exact PH0 | exact FR0 | exact CKP0 | exact CKF0 | exact PHIM | exact MI2 | exact SI2' | exact KP3
            | exact EI | exact GF3 | exact AP2 | exact C16 | exact OWN' | exact GNC | exact OWNF' | exact C24'
            | (clear - V0 PHG; lia) | (clear - F0q FRG; lia) | (clear - BV; lia) | (clear - BF; lia)
            | match goal with |- ?g => idtac "SG-MID-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis STK6 : 176 + (272 + (176 + ECP_GROUP_LOAD_STACK_A)) + arl_need_ecp R <= STKk.
  Hypothesis STK7 : 176 + 336 + arl_need_bcmp R <= STKk.
  Hypothesis USEECP : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "(71.$1.VR,VHIA,VMT,$72.$73.$66.$18.$19.$74.)")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01F0@L10837002389.2  L12654381620.1  L1540877545.3   L15795394494.0  L16136706699.289L18330401141.3  L18361960229.13 L18366302482.12 L18915258185.5  L19965341046.17 L22984996800.6  L25281032412.5  L26807410424.4  L26809621112.10 L26892418956.1  L27687752827.13 L28248436663.3  L28466672472.3  L29035697961.1  L29195095995.9  L29798657295.2  L30448823313.7  L30448823440.16 L31423882600.6  L31855359181.2  L31868079865.6  L31947621146.2  L33260198520.8  L3480690467.17  L35194455852.3  L3544842628.6   L38087549238.13 L38307157710.0  L38723285313.4  L38948636245.0  L39332637397.0  L43300649301.0  L44086382939.6  L45912147617.0  L46568163600.18 L46568163729.10 L48117736582.10 L48132467214.9  L48306838630.8  L4858179046.1   L48913550112.18 L48913550241.10 L49799904432.3  L50920171361.9  L51042627313.10 L5214639477.3   L52438553431.17 L52792927696.5  L56378894559.7  L56658999053.1  L5754760513.4   L59308586248.2  L59308628433.2  L60665797558.8  L62018535662.1  L62037211595.9  L6249365241.6   L62810577026.5  L63948500217.0  L64850595401.0  L65110448706.3  L66074878653.8  L66076829245.7  L66081091227.4  L66151427842.16 L66558683739.2  L66560190567.10 L66562108647.6  L66566235201.6  L66566237265.5  L66867922034.8  L68089138619.12 L68431700745.17 L696052593.2    L9218375351.2   L9356559676.13  L9681862608.6   Q19561319921.289Q26827028856.289Q51725606459.289Q9634096142.289 00000800=00I00J00o01:01i02Q02b03:03Q03R03a03b03f04U04\04g04k05I05P05e06]07207807I07Q08408>08J08^09L09M09\09]09^09_0:10:20:m0;M0<50<X0=80=<0>;0>[0>g0?H0?I0?T0@30@C0@]0@a0A00A60A<0A\0A_0BB0BN0Ba0Bb0Bc0Bm0Bn0Bo0C<0C]0Cg0Ch0Ci0Cj0D90DU0E@0E_0Eg0En0Fa0G80Gl0H>0HP0HeS3BUF2bsS3BUFS2sp3sp13SP1SS2LF2ra2sp2PP3PKA2bs3LFB3LFN2FB3sp11CS2PP1C4APCPS1R3HIA1h3END1P3BUD2hq2Vq3EVq2BV3PH04plen5MONOES1R3HIA1h3END1P1d4BUDF2hq2Fq4EFRq2BF3FR0S1R1C3CF23MC13MC2S1R3HIA1h2sp3TOP3sp13SP1S1R2PP4PPOD3ID13ID23ID3FS1d2Fq3F0q4FRE0FS2spS1R3HIA3NS11h2sp3PKA2lo4STKk4STK03SLO4PKLO1a2HaS1C1x1KS2FB1C4APCFS2FBS1R3HIA1h1d2hq2Fq4EFRq2h24HFR2S2FB2F0S2FB1C4APCF1A1n2H12H2S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp11C3SP13ALO3CF11A1n2H1S1R2lo3LOS2FB3ALO3F1'S1a2HaS1R3HIA1h2sp1a2HaS2LF3LFNS3END1P2Vq2V04PHE04plen5MONOE5MONO0S3sp14SP1MS3PKA1C4APCKS1R3PKA4PKOD3ID13ID3S1R3HIA3NS11h2sp2PP2lo4STKk4STK03SLO4PPLO1a2HaSS3BUF2bs1C4APCBSSSS1R2FB3F2'3ID13ID3SS1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO4DLOW3ID31A1n2H1S1R2FB3F2'3ID13ID23ID31A1n2H12H2S1R3NS12sp2lo4STKk3LOS4STK03SLO3ALO4DLOWS1R3NS12sp2lo4STKk3LOS4STK03SLO3ALOS1R3BUF2bs4DIMG4BUFI3ID13ID23ID3S2FBS1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO4DLOW3ID23ID31A1n2H1S1R2FB3F2'3ID13ID23ID31A1n2H12H2S2sp3sp13SP1S3END3BUF2bs2EB2e12pp4plen3HeE2K3FS2PP1C4APCPS1R2sp2lo4STKk3SLO4STK63sp13SP1S1R3MC13MC21a2HaS1R2lo3BUF2bs3LOS3ALO4BUFCS2spS3BUF2bs1C4APCBS1i2HiS1C2K2S1R3BUF2bs4DIMG4BUFI3ID13ID33ID2S1RS1R3NS12sp2lo4STKk3LOS4STK03SLO3SPRS2LB4C24H2K2S1R3BUF2bs3ACV4BUFCSSS3END1P2PEFFS3END1P2Vq2BVS2sp2r03SPA1q1r1H2H02q02H42FB3F64S4plen3PLRFFFS3END1P1d2Fq2BFS3END1P2e12pp4plen3HeE2K12K2S1R3HIA1h3END1P2hq2Vq3EVq4plen5MONOE2h23HV2S1R2sp2lo4STKk3SLO4STK73sp13SP1S2sp3SPRS1e3N1'S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS1R2PP4PPOD3ID13ID23ID3S2LF2ra2sp2PP3PKA2bs3LFB3LFN2FB3sp11C3SPR3CF02F03F8'S2LF2bs3LFB3LFN2FBS2LF2bs3LFB3LFN2FBS2LF2bs3LFB3LFN2FB2F0". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP SPA TPV LFB PPB PKB ENDB BIN BP PE EB BUF0 PPAL PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB HH0 NDL SSH0 SLO1 SLO2 UW0 PPOD PKOD DIMG NB1 STK2 HND HMPERM SIP SIFP BUD BUDF STK3 PKFREE STK4 SETPUB MCOK IDOK BPOK LFN C24H STK6 STK7 USEECP"] Lemma do_ecparams : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Pm2x,P,(4.&40.)(5.(4.&8.))PFB,$;.Psp1,$;.Pkv,(4.&40.)Pp5,$;.Pe1,$;.Pinfo,$;.PC,$;.Pa2v,(4.&40.)Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)Ppd,(4.&40.)PqX,(4.&40.)PqY,(4.&40.)PqZ,(4.&40.)PVq,$;.PFq,$;.Pms,$31.P,(4=.VR,VHIA,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,+;063<.+;0;5<.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1<.(22.$;.$;.)(23.$;.$;.VPKA,(24.VPKA,+10.))(1?.(22.$;.$;.))))(21.(16.VR,)VSI,))(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1?.(22.$;.$;.)))R18.R17.R1:.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R12.+100.)(1?.(22.$;.$;.)))VLB,)R19.R16.R15.R14.(25.&40.R13.)(25.&40.R12.)(25.&40.(24.R18.+60.))(25.&40.VPKA,)R11.(25.&40.(5:.(5;.VR,)))(25.&40.-4000.)R1.)P,(9.(29.(30.(35.&40.Vsp,)+;0.)R18.)(29.R18.(30.(35.&40.Vsp,)+:0.)))P,(:.$;.(42.R19.+20.)=)P,(:.$;.(42.R1;.+40.)=)P,(43.VR,VLB,VLF,R1<.+100.)P,(43.VR,(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R17.+100.)(1?.(22.$;.$;.)))VLB,)VLF,R1=.+100.)P,(44.(<.$1.VR,VHIA,Vh,)R1>.+100.)P,PB,$;.Pj,$;.P,(37.(22.$;.$;.)(23.$;.$;.R2.R1.)VLF,)(39.(29.(24.R22.+100.)R3.)(29.(24.R3.R2.)R22.))P,Px,$;.P,(<.$1.VR,VHIA,Vh,R1.)(<.$1.VR,VHIA,R24.R2.)P,(:.$;.(=.$1.VR,VHIA,R23.)(=.$1.VR,VHIA,Vh,))P,(:.$;.(>.$1.VR,VHIA,R24.)(>.$1.VR,VHIA,Vh,))P,(:.$;.(?.$1.VR,VHIA,R25.)(?.$1.VR,VHIA,Vh,))P,(29.(10.$1.VR,VHIA,R26.)(24.(10.$1.VR,VHIA,Vh,)R?.))P,(29.(11.$1.VR,VHIA,R27.)(24.(11.$1.VR,VHIA,Vh,)R?.))P,(29.=R11.)P,(29.=R11.)P,(29.(24.(24.(24.R13.(75.(30.VEND,VP,)))(5<.$5=.(30.VEND,VP,)))(4>.=))(45.(30.VEND,VP,)))P,(29.(24.(24.(24.R13.(76.(24.Vd,+1.)))(5>.$5=.(24.Vd,+1.)))(4?.=+1<.))(46.(30.VEND,VP,)Vd,))P,(29.$49.$49.)P,(29.=(5<.$5=.(30.VEND,VP,)))P,(29.=(5>.$5=.(24.Vd,+1.)))P,(29.=(75.=))P,(29.=(76.(24.Vd,+1.)))P,(29.=(5?.(60.$5=.)))P,(29.=(61.(60.$5=.)(24.Vd,+1.)))P,Pa,$;.Pb,$;.P,(29.R2.R1.)(29.(5<.$5=.R3.)(5<.$5=.R2.))P,Pa,$;.Pb,$;.P,(29.R2.R1.)(29.(75.R3.)(75.R2.))P,(33.$1.R34.)P,(15.(16.VR,)VSI,R35.)P,(62.$1.VMT,R36.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R2?.+100.)(1?.(22.$;.$;.)))VLB,)R2?.(70.R2?.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.))P,(37.$;.R31.$66.)P,(:.$;.(42.R31.+10.)=)P,(43.VR,VLB,VLF,R32.+100.)P,(26.=(47.(48.(4.&8.)Vbs,)))(4:.$1.(4;.$1.VR,VHIA,R3<.Vmo0,)(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)R23.)")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros CQH SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq V0 F0q BV BF CNTK PH0 FR0 PHE0 FRE0 CKP0 CKF0 PHIM PHIME MI2x SI2x KP2x EI C16 CFR BLEN0.
    ddestruct CQH as (mm & c0 & c1 & c2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & -> & D & PRESB).
    pose proof D as D0.
    ddestruct D0 as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & p1v & ptag & ppad & plen
                   & HHq & FHD & LPKC & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MIq
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & Hp1v & Hp1v2 & PPC & PRES).
    rt_facts.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq. rewrite ETq, ESq in HTOPq.
    pose proof (hm_top asegs R HIA h LB LF m HH0) as HTOP0.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    pose proof (art_data_lo asegs R HIA) as DLOW.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    ctx_block_facts.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hq) hq ([(C, 256)] ++ LB) LF mm FB 256 lo HHq eq_refl FRSHq F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBq & INF & INH & IND & APq & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
    assert (CINq : In (C, 256) ([(C, 256)] ++ LB)) by (left; reflexivity).
    assert (APCF : FB + 256 <= C \/ C + 256 <= FB) by (apply F3'; apply in_app_iff; left; exact CINq).
    assert (CNL : ~ In (C, 256) LB) by (intros K; pose proof (CF3 C 256 ltac:(apply in_app_iff; left; exact K)) as K2; clear - K2; lia).
    assert (APO : forall b, In b [(C, 256)] -> PP + 8 <= fst b \/ fst b + snd b <= PP) by (intros b [<-|[]]; cbn [fst snd]; clear - APCP; lia).
    destruct (hm_block_bounds hq _ _ _ BUF BLEN HHq ltac:(apply in_app_iff; right; exact BIN)) as (_ & _ & BUFC & BUFI).
    ddestruct MCOK as (MC1 & MC2 & MC3 & MC4 & MC5 & MC6). dpose IDOK as (ID1 & ID2 & ID3 & ID4 & ID5 & ID6).
    (* [comment removed for export] *)
    pose proof (own_agree hq [(C, 256)] _ m2x mm PRESB HHq APO) as AGR.
    assert (KPm : ecp_keypair_at asegs MT mm ([(C, 256)] ++ LB) C (kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ)).
    { eapply (ecp_keypair_at_agree asegs MT m2x mm _ _ [(C, 256)]); [exact KP2x| exact MI2x| exact MIq| intros b Hb; apply in_app_iff; left; exact Hb| exact AGR| left; reflexivity|].
      intros e He HO. exfalso. clear - He HO. unfold kp_mpds, kp_init, grp_mpds, grp_init, pt_mpds, pt_init in He. cbn in He.
      repeat (destruct He as [<-|He]; [cbn in HO; discriminate|]). destruct He. }
    pose proof (si_path hq _ m2x mm PRESB SI2x) as SIm.
    destruct (proj1 (SIP mm) SIm) as [IDSm [cnt MCm]].
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 plen) as PLR. unfold bv_modulus in PLR. cbn [Z.pow Z.of_N Pos.pow] in PLR.
    rewrite <- (Z_to_bv_bv_unsigned plen) in LPAR.
    change [C4 ptag; C4 ppad; C8 (Z_to_bv 64 (bv_unsigned plen)); C8 (Z_to_bv 64 pp)] with (buf_cells ptag ppad (bv_unsigned plen) pp) in LPAR.
    frame_aobj FSHX (FB + 96) 3%nat as OPAR.
    assert (LENB : bv_unsigned plen <= END - P) by (destruct PPC as [(_ & K & _)|(_ & K1 & K2)]; [rewrite K; clear - PE; lia| clear - K1 K2 HeE; lia]).
    (* [comment removed for export] *)
    pose proof (presW_presA asegs R HIA hq LB LF _ _ _ _ _ PRES) as HPe. rewrite ESq in HPe.
    assert (UWm : uwc asegs mm (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { assert (UWa : uwc asegs mm (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply (uwc_presA R); [exact HPe| exact UW0| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NS1 STK0; lia].
        intros a Ha. apply (proj2 (outside_app _ _ a)). split; [cbn; split; [clear - Ha PPLO SLO NS1 STK0; lia| split; [clear - Ha PKLO SLO NS1 STK0; lia| exact I]]|].
        eapply (disjoint_outside _ (bv_unsigned sp) (hstkhi asegs R HIA h - bv_unsigned sp)); [| clear - Ha; lia].
        apply (si_disjoint_off L SI). right. clear - DLOW ALO LOS SLO NS1 STK0; lia. }
      pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UWa| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact (uwc_nonneg _ _ _ _ _ _ _ UW0)]. }
    pose proof (PHIME (bv_unsigned plen) (END - P) LENB) as MONOE.
    pose proof (PHIME 0 (bv_unsigned plen) ltac:(clear - PLR; lia)) as MONO0.
    assert (SSm : sshad asegs AL mm slo (bv_unsigned sp)) by (eapply (presA_sshad asegs R _ _ _ _ _ _ m mm _ _ HPe); [exact SSH0| exact SLO1| clear - TOP HTOP0; lia]).
    destruct (sshad_split asegs AL mm slo sp1 (bv_unsigned sp) SSm ltac:(clear - SP1 SLO SLO2 NS1 STK0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof USEECP as UE'. unfold pk_use_ecparams_stmtA, A_PK_USE_ECPARAMS in UE'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply UE' with (h := hq) (LB := [(C, 256)] ++ LB) (LF := (FB, 256) :: LF) (PKA := PKA) (info := info) (C := C) (lo := lo) (d := d + 1) (slo := slo)
                      (PAR := FB + 96) (LEN := bv_unsigned plen) (P := pp) (BUF := BUF) (tg := ptag) (pd := ppad) (bs := bs)
                      (idpad := idpad) (pP := pP) (pA := pA) (pB := pB) (pX := pX) (pY := pY) (pZ := pZ) (pN := pN) (hpad := hpad) (qd := pd) (qX := qX) (qY := qY) (qZ := qZ);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?ETq, ?ESq; unfold ECP_KEYPAIR_SIZE;
        first [ exact HHq | exact HK1 | exact HPKA | exact PKAL | exact PK0 | exact EI | exact OPKA | exact KPm | exact CINq | exact LPAR | exact OPAR | exact HBS | exact BUF0
              | exact IDSm | exact IDOK | exact STbelow | exact LOS | exact MIq | exact TPV | exact UWm | exact BLEN0 | exact SSlo | exact SLO1 | exact SLO2 | reflexivity
              | lazymatch goal with
                | |- (length _ + 1 < 512)%nat => cbn [length]; clear - LFN; lia
                | |- client_range _ _ _ PKA 16 => eapply client_range_wsep; [exact CWK| | left; exact PKLO];
                       intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]
                | |- PKA + 16 <= lo \/ _ => left; exact PKLO
                | |- PKA + 16 <= C \/ _ => clear - APCK; lia
                | |- PKA + 16 <= A_ECP_IDS_DONE \/ _ => clear - PKOD ID1 ID2 ID3; lia
                | |- (FB + 96) mod 8 = 0 => clear - F64; Z.div_mod_to_equations; lia
                | |- 0 < FB + 96 => clear - F0; lia
                | |- client_range _ _ _ (FB + 96) 24 => eapply client_range_block; [exact IND| clear; lia| clear; lia]
                | |- FB + 96 + 24 <= lo \/ _ => left; clear - F1' ALO LOS; lia
                | |- FB + 96 + 24 <= C \/ _ => clear - APCF; lia
                | |- FB + 96 + 24 <= A_ECP_IDS_DONE \/ _ => clear - F2' ID1 ID2 ID3; lia
                | |- BUF + _ + 8 <= 2 ^ 47 => clear - BUFC ACV; lia
                | |- client_range _ _ _ BUF _ => eapply client_range_block; [apply in_app_iff; left; apply in_app_iff; right; exact BIN| clear; lia| clear; lia]
                | |- BUF + _ <= lo \/ _ => left; clear - BUFC ALO LOS; lia
                | |- BUF + _ <= C \/ _ => clear - APCB; lia
                | |- BUF + _ <= A_ECP_IDS_DONE \/ _ => clear - BUFI DIMG ID1 ID2 ID3; lia
                | |- _ = 0 \/ aobj _ _ _ _ BUF _ => right; exact OBUF
                | |- (pp = 0 /\ _) \/ _ => destruct PPC as [(K1 & K2 & K3)|(K1 & K2 & K3)]; [left; split; [exact K1| split; [exact K2| exact K3]]| right; split; [exact K1| clear - K3 HeE EB; lia]]
                | |- 0 <= bv_unsigned plen => clear - PLR; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD EVq BV PH0 MONOE; unfold PHIpk, AVOL_CALL in *; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF EFRq BF FR0; unfold FFRpk, fr_charge in *; lia
                | |- cnt24 _ + _ <= C24MAX => cbn [app]; rewrite cnt24_cons_small by (clear; lia); ddestruct PKP_C24_facts as (K1 & K2 & K3 & K4); clear - C24H K1 K2 K3 K4; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- _ => clear - SP1 SP1M SLO STK0 STK6 STK7 NS1 NB1 NEEDE TOP; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "UE-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). cbv zeta in PO.
    ddestruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & r & g' & NB & LB2
                    & E4 & RR & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & LEQ & LNEW & C24L & KP2 & AP2 & GB2 & ERES & GF2 & HPKA2 & IDS2).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xb063c)) with (Z_to_bv 64 0xb063c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R. unfold ECP_GROUP_SIZE in HP2. cbn [kp_d kp_Q kp_init] in KP2.
    (* [comment removed for export] *)
    assert (SUBL : forall b, In b LB -> In b LB2) by (intros b Hb; apply LEQ; right; apply in_app_iff; right; exact Hb).
    destruct (relist h2 LB2 _ m2 HH2 SUBL) as (h3 & HH3 & PERM & E3cs & E3top & E3stk & E3flag & E3vol & E3fr & HKI3).
    set (own' := newb LB LB2) in *.
    assert (OWN' : forall b, In b own' <-> b = (C, 256) \/ In b (grp_blocks g')).
    { intros b. unfold own'. rewrite newb_in, GB2. split.
      - intros [Hb Hn]. apply LEQ in Hb. destruct Hb as [Hb|Hb]; [right; exact Hb|]. destruct Hb as [E|Hb]; [left; symmetry; exact E| exfalso; exact (Hn Hb)].
      - intros [E|Hb]; [subst b; split; [apply LEQ; right; left; reflexivity| exact CNL]|].
        split; [apply LEQ; left; exact Hb| intros HbL; exact (proj1 (LNEW b Hb) ltac:(right; exact HbL))]. }
    assert (GNC : ~ In (C, 256) (grp_blocks g')) by (rewrite GB2; intros K; exact (proj1 (LNEW _ K) ltac:(left; reflexivity))).
    assert (HCSq3 : forall x, hcs asegs R HIA hq x -> hcs asegs R HIA h3 x) by (intros x Hx; rewrite E3cs; exact (HCS2 x Hx)).
    assert (HCSh3 : forall x, CS x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCSq3, HCSq, Hx).
    assert (ES3 : hstkhi asegs R HIA h3 = hstkhi asegs R HIA h) by (rewrite E3stk, HS2; exact ESq).
    assert (ET3 : htop asegs R HIA h3 = htop asegs R HIA h) by (rewrite E3top, HT2; exact ETq).
    assert (EF3 : hflag asegs R HIA h3 = hflag asegs R HIA h) by (rewrite E3flag, HF2; exact EFq).
    pose proof (fresh_apart_relist_sg R HIA h3 ([(C, 256)] ++ LB) (own' ++ LB) LF m2 FB 256 FRSHq HH3) as FRSH3.
    assert (KP3 : ecp_keypair_at asegs MT m2 (own' ++ LB) C (mkKP g' (mpd_init (C + 192) pd) (pt_init (C + 208) qX qY qZ))).
    { eapply ecp_keypair_at_LB_mono; [exact KP2| intros b Hb; exact (Permutation_in b PERM Hb)]. }
    assert (SI2' : si_P SI m2).
    { apply (proj2 (SIP m2)). split; [exact IDS2|]. exists cnt.
      eapply (presA_rw_cells asegs R _ _ _ _ _ _ mm m2 _ _ HP2); [exact MCm| |].
      - cbn [cells_size csize Nat.add]. intros a Ha. right; left. split; [clear - Ha MC1 MC2; lia| apply MC3; clear - Ha; lia].
      - cbn [cells_size csize Nat.add disjoint_from]. split; [clear - CF2 MC1 MC2; lia|]. unfold A_MUL_COUNT, A_ECP_IDS_DONE, A_ECP_IDS. split; [clear; lia| split; [clear; lia| exact I]]. }
    assert (PRESa3 : presW asegs R HIA h3 LB LF (bv_unsigned sp) (arl_stklo R) WXF m m2).
    { eapply A_pk_parse_E.presW_step with (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (FB := FB) (sp1 := sp1) (hq := hq) (LBq := [(C, 256)] ++ LB)
                                         (W := [(C, C + 192); (A_ECP_IDS_DONE, A_ECP_IDS_DONE + 1); (A_ECP_IDS, A_ECP_IDS + 56)]) (mc := mm);
        first [ exact PRES | exact HP2 | exact HCSq3 | (rewrite E3stk; exact HS2) | eassumption | (clear - SP1; lia) | (intros b Hb; apply in_app_iff; right; exact Hb)
              | lazymatch goal with |- forall x, client_addr _ _ _ x -> _ => idtac end
              | match goal with |- ?g => idtac "PWS-LEFT:" g end ].
      intros x Hc Hx. apply (proj1 (outside_app _ _ x)) in Hx. destruct Hx as [_ Hx]. rewrite SIFP in Hx. cbn [outside] in Hx |- *.
      split; [| clear - Hx; tauto].
      intros K. apply (fresh_not_clientA R LB LF C 256 (bv_unsigned sp) x CFR ltac:(clear - ALO LOS SLO STK0 NS1; lia) Hc). clear - K. lia. }
    assert (D3 : DINV2' WXF FB sp1 h3 (own' ++ LB) FSH0 kv p5 e1 (Z_to_bv 64 info) (Z_to_bv 64 C) m2).
    { eapply A_pk_parse_E.dinv2_presA with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (hq := hq) (LBq := [(C, 256)] ++ LB) (LBp := [(C, 256)] ++ LB)
                                          (W := [(C, C + 192); (A_ECP_IDS_DONE, A_ECP_IDS_DONE + 1); (A_ECP_IDS, A_ECP_IDS + 56)]) (mc := mm);
        first [ exact D | reflexivity | exact SP1 | exact F64 | exact FRSHq | exact ESq | exact HP2 | exact HH3 | exact HCSq3 | exact ST2 | exact MI2 | exact HPKA2 | exact PRESa3
              | eassumption
              | lazymatch goal with
                | |- forall b, In b LB -> In b _ => intros b Hb; apply in_app_iff; right; exact Hb
                | |- forall A n, FB <= A -> _ -> disjoint_from _ A n => intros A n H1 H2; cbn [disjoint_from]; split; [clear - H1 H2 APCF; lia| split; [clear - H1 H2 F2' ID1 ID2 ID3; lia| split; [clear - H1 H2 F2' ID1 ID2 ID3; lia| exact I]]]
                | |- forall A n, sp1 <= A -> disjoint_from _ A n => intros A n H1; cbn [disjoint_from];
                       split; [clear - H1 CF1 ALO LOS SP1 SLO STK0 NS1; lia| split; [clear - H1 ID1 ID2 ID3 DLOW ALO LOS SP1 SLO STK0 NS1; lia| split; [clear - H1 ID1 ID2 ID3 DLOW ALO LOS SP1 SLO STK0 NS1; lia| exact I]]]
                | |- disjoint_from _ PP 8 => cbn [disjoint_from]; split; [clear - APCP; lia| split; [clear - PPOD ID1 ID2 ID3; lia| split; [clear - PPOD ID1 ID2 ID3; lia| exact I]]]
                | |- disjoint_from _ BUF _ => cbn [disjoint_from]; split; [clear - APCB; lia| split; [clear - BUFI DIMG ID1 ID2 ID3; lia| split; [clear - BUFI DIMG ID1 ID2 ID3; lia| exact I]]]
                end
              | match goal with |- ?g => idtac "UE-DINV-LEFT:" g end ]. }
    pose proof (presW_init_at R HIA h3 _ _ (own' ++ LB) LF m2 (bv_unsigned sp) (arl_stklo R) WBP h3 HH3
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb3.
    assert (OWNF' : forall b, In b own' -> ~ In b LB /\ fresh_apart R LB LF (fst b) (snd b) /\ 0 < snd b).
    { intros b Hb. apply OWN' in Hb. destruct Hb as [E|Hg].
      - subst b. cbn [fst snd]. split; [exact CNL|]. split; [exact CFR| clear; lia].
      - rewrite GB2 in Hg. destruct (LNEW b Hg) as [N1 N2]. split; [intros HbL; apply N1; right; exact HbL|]. split.
        + eapply fresh_apart_frames_mono_sg; [eapply (fresh_apart_blocks_mono R ([(C, 256)] ++ LB) LB); [exact N2| intros b' Hb'; apply in_app_iff; right; exact Hb']|].
          intros b' Hb'. eapply fdata_incl; [| exact Hb']. intros fb Hfb. right. exact Hfb.
        + rewrite <- GB2 in Hg. unfold grp_blocks in Hg. apply in_flat_map in Hg. ddestruct Hg as (e & He & Hbe). destruct (MpiClient.mpd_blk_heap e b Hbe) as [O ->]. cbn [snd].
          pose proof (kp_mpds_mpdr asegs MT _ _ _ _ e KP2 ltac:(unfold kp_mpds; cbn [kp_grp kp_d kp_Q]; apply in_or_app; left; exact He)) as (_ & _ & _ & _ & _ & HOW).
          rewrite O in HOW. destruct HOW as (N1' & _). clear - N1'. lia. }
    assert (C24' : cnt24 own' = 0).
    { apply cnt24_all_out. intros b Hb. apply OWN' in Hb. destruct Hb as [E|Hg]; [subst b; reflexivity|].
      rewrite GB2 in Hg. destruct ERES as [(idx & _ & RES)|(_ & _ & ENB)]; [exact (cnt24_zero_out NB b (gl_cnt24A _ _ _ _ _ _ _ RES) Hg)| rewrite ENB in Hg; destruct Hg]. }
    assert (EV3 : havol asegs R HIA h3 <= havol asegs R HIA h + (Vq + pk_ecparams_PHI (END - P))) by (rewrite E3vol; clear - HV2 EVq MONOE; lia).
    assert (EFR3 : hfr asegs R HIA h3 <= hfr asegs R HIA h + (Fq + pk_ecparams_FR (d + 1))) by (rewrite E3fr; clear - HFR2 EFRq; lia).
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj (proj2 (HKI3 mo2) HK2) (mo_frame_trans _ _ _ MF1 MF2))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { eapply A_pk_parse_F.seg_C4 with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (WB := WBP) (hq := h3) (LBq := own' ++ LB) (m2x := m2) (p5 := p5) (r := r);
        first [ exact D3 | exact PRESb3 | exact HCSh3 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact ES3 | exact ET3 | exact RR
              | (intros b Hb; apply in_app_iff; right; exact Hb)
              | eassumption | match goal with |- ?g => idtac "SEGC4-PRE-LEFT:" g end ]. }
    cbv beta. intros ms5 SC.
    eapply (ec_mid h3 own' m2 FB sp1 kv p5 e1 r info C g' pd qX qY qZ (Vq + pk_ecparams_PHI (END - P)) (Fq + pk_ecparams_FR (d + 1)));
      first [ exact SC | exact RR | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact CFB | exact AP | exact HCSh3 | exact ET3 | exact ES3 | exact EF3
            | exact EV3 | exact EFR3 | exact CNTK | exact PH0 | exact FR0 | exact CKP0 | exact CKF0 | exact PHIM | exact MI2 | exact SI2' | exact KP3
            | exact EI | exact GF2 | exact AP2 | exact C16 | exact OWN' | exact GNC | exact OWNF' | exact C24'
            | (clear - V0 PHE0 MONOE MONO0; lia) | (clear - F0q FRE0; lia) | (clear - BV; lia) | (clear - BF; lia)
            | match goal with |- ?g => idtac "UE-MID-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis STK8 : 176 + 528 + arl_need_rt R <= STKk.
  Hypothesis STK9 : 176 + 448 + arl_need_smalloc R <= STKk.
  Hypothesis RSAPP : rsa_parse_pubkey_stmtA_c asegs R HIA A_RSA_PARSE_PUBKEY.

  Local Notation SEQ' := (A_pk_parse_F.SEQ R HIA LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP END PKA lo P BUF bs).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00k0@L11136097799.13 L11307491108.5  L11621993564.3  L13527420912.7  L13527535092.8  L14662949897.15 L15008978136.3  L1540877545.3   L17117663799.0  L17604312231.0  L18359863091.13 L18857395536.239L19380128016.16 L19380128145.7  L19965341046.15 L21566214438.6  L21884438016.3  L22722674826.4  L2397676628.0   L24299716137.7  L25281032412.5  L26631083509.3  L27111942217.1  L28046100089.0  L28364173308.10 L29362887695.8  L29936708385.0  L30532661637.3  L32955626683.8  L3480690467.15  L35812527258.4  L36021046677.2  L37796632789.0  L38484132271.9  L38948636245.0  L39316637317.0  L39332637397.0  L40888186162.6  L40890226892.11 L43300649301.0  L48132467214.9  L48172182542.2  L51042627313.10 L51313452802.5  L51313454866.4  L51508673957.0  L53330035200.6  L53330037264.5  L54256493155.11 L54378684516.240L55623974153.15 L58284014529.4  L59308628433.2  L61284830317.11 L62018535662.1  L6249365241.6   L68089138619.13 L9356559676.13  L9714622411.13  00000[00m01901T01m02L02X02d02e02f03Q05A06906N06f07=07E07R07S07i07j08508908:08Y09209309>09Z09d0:20::0:;0:W0:X0:Y0:Z0:g0;K0;L0;o0<70<80<90<:0<;0<<0<K0<o0>\0?;0?J0?P0?]0?`0?l0@W0AJ0B4S1R3END2lo3BUF2bs3LOS2EB2p52e13HeE3ALO4BUFCS1P3BUF2BP2p54Hp2aS3PKA1C4APCKS2LB2p52e13LB24C24L4own'2CIS2LB1P2p52e14own'4C24'2DMS1R2sp2lo4STKk3SLO4STK93sp13SP1S2p52e14Hp2eS2sp3sp13SP1SSS1R3HIA1h3END1P3BUD2hq2p52e12Vq3EVq2BV4MONOS2LF2ra2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2PE2EB3DPK3DPB3DKB3LFN2FB3sp12p52e14Hp2a3HeE3SPR4SP1R3kbs4KLEN1n2HnS1R3NS12sp2lo4STKk3LOS4STK03SLO3sp11C3SP13ALO3CF11A1n2H1S2FB1C4APCF1A1n2H12H2S1R3HIA1h2sp3TOP3sp13SP1S1P3BUF2BP4BUF02p54Hp2aS2PP1b1KS3END1P2Vq2BVSS3END1P2p52e14Hp2a3HeEFS2PP1C4APCPS2PPSS1R3HIA1h3END1P1d2Fq2BF2h34EFR3S3END3BUF2bs2EB2p52e13HeESS2PP1C4APCPS1R3HIA1h2hq2Fq4EFRq2h24HFR2S3sp14SP1MS1P2p52e14Hp2aS2LF3LFNSS1R3HIA1h3END1P2Vq2BV2h33EV3SSSS2r'4own'1K1HS1R3HIA1h3END1P1d4BUDF2hq2Fq4EFRq2BFSS1R3NS12sp2lo4STKk3LOS4STK03SLO3ALOS2r'3N1'FFFSFS3END1P1d2Fq2BFS1R3END3BUF2bs2EB2p52e13HeE3ACV4BUFCS2LF2ra2sp2PP3END3PKA1P3BUF2bs3LFB3PPB3PKB2BP2PE2EB3DPK3DPB3DKB3LFN2FB3sp12p52e14Hp2a3HeE3SPR4SP1R3kbs4KLEN1HS1R2sp2lo4STKk3SLO4STK83sp13SP1S3BUF2bs1C4APCBS1C2K2S3PKA2lo4PKLOS1RS2LB4C24H2K1S1R3HIA1h3END1P2hq2p52e12Vq3EVq4MONO2h23HV2S1R3NS12sp2lo4STKk3LOS4STK03SLO3sp13SP13ALO3ACV3SPRS3END1P3BUF2bs2BP2EB2p52e11C4Hp2a3HeE4APCB". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP TPV LFB PPB PKB ENDB BIN BP PE EB BUF0 PPAL PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB HH0 NDL SSH0 SLO1 PPOD PKOD NB1 STK2 HND HMPERM BUD BUDF STK3 PKFREE LFN C24H STK8 STK9 RSAPP SLO2"] Lemma do_rsa : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Phq,(0.$1.VR,VHIA,)Pm2x,P,(4.&40.)(5.(4.&8.))PFB,$;.Psp1,$;.Pkv,(4.&40.)Pp5,$;.Pe1,$;.PC,$;.PVq,$;.PFq,$;.Pms,$31.P,(4=.VR,VHIA,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,VPP,VEND,VPKA,Vlo,VP,VBUF,Vbs,+;05?8.+;28>4.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1<.(22.$;.$;.)(23.$;.$;.VPKA,(24.VPKA,+10.))(1?.(22.$;.$;.))))(21.(16.VR,)VSI,))(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1?.(22.$;.$;.)))R9.R8.R;.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R4.+>8.)(1?.(22.$;.$;.)))VLB,)R:.R7.R6.R5.(25.&40.$77.)(25.&40.R4.)(25.&40.R4.)(25.&40.R6.)(25.&40.(30.R5.R6.))(25.&40.(5:.(5;.VR,)))(25.&40.(24.R9.+20.))R1.)P,(9.(29.(30.(35.&40.Vsp,)+;0.)R9.)(29.R9.(30.(35.&40.Vsp,)+:0.)))P,(:.$;.(42.R:.+20.)=)P,(:.$;.(42.R<.+40.)=)P,(43.VR,VLB,VLF,R=.+100.)P,(43.VR,(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R9.+>8.)(1?.(22.$;.$;.)))VLB,)VLF,R>.+100.)P,(44.(<.$1.VR,VHIA,Vh,)R?.+100.)P,PB,$;.Pj,$;.P,(37.(22.$;.$;.)(23.$;.$;.R2.R1.)VLF,)(39.(29.(24.R13.+100.)R3.)(29.(24.R3.R2.)R13.))P,Px,$;.P,(<.$1.VR,VHIA,Vh,R1.)(<.$1.VR,VHIA,R15.R2.)P,(:.$;.(=.$1.VR,VHIA,R14.)(=.$1.VR,VHIA,Vh,))P,(:.$;.(>.$1.VR,VHIA,R15.)(>.$1.VR,VHIA,Vh,))P,(:.$;.(?.$1.VR,VHIA,R16.)(?.$1.VR,VHIA,Vh,))P,(29.(10.$1.VR,VHIA,R17.)(24.(10.$1.VR,VHIA,Vh,)R?.))P,(29.(11.$1.VR,VHIA,R18.)(24.(11.$1.VR,VHIA,Vh,)R?.))P,(29.=R11.)P,(29.=R11.)P,(29.(24.(24.R13.(78.(30.VEND,VP,)))(4>.=))(45.(30.VEND,VP,)))P,(29.(24.(24.R13.$79.)(4?.=+1<.))(46.(30.VEND,VP,)Vd,))P,(29.$49.$49.)P,(33.$1.R1=.)P,(15.(16.VR,)VSI,R1>.)P,(7:.$1.R1?.(2<.(22.$;.$;.)(1<.(22.$;.$;.)(23.$;.$;.R19.+>8.)(1?.(22.$;.$;.)))VLB,)R19.(7;.R19.))P,(43.VR,VLB,VLF,R1:.+>8.)(4:.$1.(4;.$1.VR,VHIA,R22.Vmo0,)(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)R18.)")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros CQH SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq V0 F0q BV BF CNTK MI2x SI2x RAT2x CFR.
    ddestruct CQH as (mm & c0 & c1 & c2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & -> & D & PRESB).
    pose proof D as D0.
    ddestruct D0 as (w0 & w1 & w2 & pc0 & pc1 & Lw & kpad & gv & gpad & pp & p1v & ptag & ppad & plen
                   & HHq & FHD & LPKC & LLEN & LPAR & LALGa & LALGb & LGIDa & LGIDb & FSHX & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MIq
                   & HPP & OPP & HPKA & OPKA & HBS & OBUF & Hp2a & Hp2e & HeE & Hp1v & Hp1v2 & PPC & PRES).
    rt_facts.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq. rewrite ETq, ESq in HTOPq.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    pose proof (art_data_lo asegs R HIA) as DLOW.
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    ctx_block_facts.
    assert (CINq : In (C, 232) ([(C, 232)] ++ LB)) by (left; reflexivity).
    assert (APCF : FB + 256 <= C \/ C + 232 <= FB) by (ddestruct FRSHq as (_ & _ & _ & K); apply K; apply in_app_iff; left; exact CINq).
    assert (CNL : ~ In (C, 232) LB) by (intros K; pose proof (CF3 C 232 ltac:(apply in_app_iff; left; exact K)) as K2; clear - K2; lia).
    destruct (hm_block_bounds hq _ _ _ BUF BLEN HHq ltac:(apply in_app_iff; right; exact BIN)) as (_ & _ & BUFC & BUFI).
    (* [comment removed for export] *)
    assert (RATm : rsa_at asegs mm ([(C, 232)] ++ LB) C (rsa_fresh C)).
    { eapply (rsa_at_presx asegs L m2x mm _ (([(C, 232)] ++ LB) ++ fdata LF) (bv_unsigned sp) WBP);
        [exact RAT2x| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ LF _ _ _ _ _ PRESB))| exact MI2x| exact MIq
        | apply in_app_iff; left; exact CINq| intros b Hb; cbn in Hb; destruct Hb| cbn [disjoint_from]; split; [clear - APCP; lia| exact I]| intros b Hb; cbn in Hb; destruct Hb]. }
    pose proof (si_path hq _ m2x mm PRESB SI2x) as SIm.
    (* [comment removed for export] *)
    destruct (sub_input asegs mm BUF bs p5 (e1 - p5) HBS ltac:(clear - Hp2a BP; lia) ltac:(clear - Hp2e; lia) ltac:(clear - Hp2e HeE EB; lia)) as [HKB KLEN].
    set (kbs := firstn (Z.to_nat (e1 - p5)) (skipn (Z.to_nat (p5 - BUF)) bs)) in HKB, KLEN.
    assert (OKB : aobj asegs AL (hcs asegs R HIA hq) mm p5 (e1 - p5)) by (eapply aobj_sub; [exact OBUF| clear - Hp2a BP; lia| clear - Hp2e HeE EB; lia]).
    assert (PHR : forall n, 0 <= n -> 0 <= RSA_PP_PHI n) by (intros n Hn; unfold RSA_PP_PHI, MPI_RB_PHI, AVOL_CALL; lia).
    assert (FRR : 0 <= RSA_PP_FR) by (unfold RSA_PP_FR, MPI_RB_FR, fr_charge; clear; lia).
    assert (MONO : RSA_PP_PHI (e1 - p5) <= RSA_PP_PHI (END - P)) by (unfold RSA_PP_PHI; pose proof (MPI_RB_PHI_mono (e1 - p5) (END - P) ltac:(clear - Hp2a Hp2e HeE; lia)); lia).
    pose proof (hm_top asegs R HIA h LB LF m HH0) as HTOP0.
    pose proof (presW_presA asegs R HIA hq LB LF _ _ _ _ _ PRES) as HPe. rewrite ESq in HPe.
    assert (SSm : sshad asegs AL mm slo (bv_unsigned sp)) by (eapply (presA_sshad asegs R _ _ _ _ _ _ m mm _ _ HPe); [exact SSH0| exact SLO1| clear - TOP HTOP0; lia]).
    destruct (sshad_split asegs AL mm slo sp1 (bv_unsigned sp) SSm ltac:(clear - SP1 SLO SLO2 NS1 STK0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    pose proof RSAPP as RP'. unfold rsa_parse_pubkey_stmtA_c, A_RSA_PARSE_PUBKEY in RP'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply RP' with (h := hq) (LB := [(C, 232)] ++ LB) (LF := (FB, 256) :: LF) (C := C) (KEY := p5) (kbs := kbs) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?KLEN; rewrite ?ETq, ?ESq; unfold RSA_CTX_SIZE;
        first [ exact HHq | exact HK1 | exact RATm | exact HKB | exact STbelow | exact LOS | exact MIq | exact TPV | exact OKB | exact SSlo | exact SLO1 | reflexivity
              | lazymatch goal with
                | |- (length _ < 511)%nat => cbn [length]; clear - LFN; lia
                | |- slo <= _ => clear - SP1 SLO SLO2 STK9 NS1; lia
                | |- 0 < p5 => clear - Hp2a BP BUF0; lia
                | |- p5 + _ + 8 <= 2 ^ 47 => clear - Hp2e HeE EB BUFC ACV; lia
                | |- client_range _ _ _ p5 _ => eapply client_range_block; [apply in_app_iff; left; apply in_app_iff; right; exact BIN| clear - Hp2a BP; lia| clear - Hp2e HeE EB; lia]
                | |- p5 + _ <= C \/ _ => clear - APCB Hp2a Hp2e HeE BP EB; lia
                | |- p5 + _ <= lo \/ _ => left; clear - Hp2e HeE EB BUFC ALO LOS; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD EVq BV MONO; unfold PHIpk, AVOL_CALL in *; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF EFRq BF; unfold FFRpk, fr_charge in *; lia
                | |- cnt24 _ + _ <= C24MAX => cbn [app]; rewrite cnt24_cons_small by (clear; lia); ddestruct PKP_C24_facts as (K1 & K2 & K3 & K4); clear - C24H K1 K2 K3 K4; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- _ => clear - SP1 SP1M SLO STK0 STK8 STK9 NS1 TOP; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "RSA-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & LB2 & r'
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & RAT2 & COV2 & SUB2 & NEWN & NEWF & C24L).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xb05f8)) with (Z_to_bv 64 0xb05f8 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R. unfold RSA_CTX_SIZE in HP2. rewrite KLEN in HV2, C24L.
    (* [comment removed for export] *)
    assert (SUBL : forall b, In b LB -> In b LB2) by (intros b Hb; apply SUB2; apply in_app_iff; right; exact Hb).
    destruct (relist h2 LB2 _ m2 HH2 SUBL) as (h3 & HH3 & PERM & E3cs & E3top & E3stk & E3flag & E3vol & E3fr & HKI3).
    set (own' := newb LB LB2) in *.
    assert (OWN' : forall b, In b own' <-> In b ((C, 232) :: rsa_limb_blocks r')).
    { intros b. unfold own'. rewrite newb_in. cbn [In]. split.
      - intros [Hb Hn]. destruct (COV2 b Hb) as [Hb1|Hq]; [| right; exact Hq]. destruct Hb1 as [E|Hb1]; [left; exact E| exfalso; exact (Hn Hb1)].
      - intros [E|Hq]; [subst b; split; [apply SUB2; left; reflexivity| exact CNL]|].
        split; [exact (rsa_limb_blocks_in asegs _ _ _ _ b RAT2 Hq)| intros HbL; exact (NEWN b Hq ltac:(right; exact HbL))]. }
    assert (HCSq3 : forall x, hcs asegs R HIA hq x -> hcs asegs R HIA h3 x) by (intros x Hx; rewrite E3cs; exact (HCS2 x Hx)).
    assert (HCSh3 : forall x, CS x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCSq3, HCSq, Hx).
    assert (ES3 : hstkhi asegs R HIA h3 = hstkhi asegs R HIA h) by (rewrite E3stk, HS2; exact ESq).
    assert (ET3 : htop asegs R HIA h3 = htop asegs R HIA h) by (rewrite E3top, HT2; exact ETq).
    assert (EF3 : hflag asegs R HIA h3 = hflag asegs R HIA h) by (rewrite E3flag, HF2; exact EFq).
    pose proof (fresh_apart_relist_sg R HIA h3 ([(C, 232)] ++ LB) (own' ++ LB) LF m2 FB 256 FRSHq HH3) as FRSH3.
    assert (REP2 : pk_rep asegs PK m2 (own' ++ LB) PKA A_RSA_INFO C own').
    { eapply (pk_rep_frame asegs PK) with (m := m2) (LB := LB2); [| exact MI2| intros b Hb; apply in_app_iff; left; exact Hb| intros a _; reflexivity].
      cbn [PKA_inst PKC_inst pk_rep]. eapply (rsa_rep_introA asegs); [unfold A_RSA_INFO; clear; lia| exact MI2| exact RAT2| exact OWN']. }
    assert (SI2' : si_P SI m2).
    { eapply (si_heap_presx asegs L SI); [exact SIm| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)|].
      intros a Ha. apply (si_outside1 L SI C 232 a); [exact CF2| exact Ha]. }
    assert (HPKA2 : rw_cells asegs m2 PKA [C8 (Z_to_bv 64 A_RSA_INFO); C8 (Z_to_bv 64 C)]).
    { eapply (presA_rw_cells asegs R _ _ _ _ _ _ mm m2 _ _ HP2); [exact HPKA| | cbn [cells_size csize Nat.add disjoint_from]; split; [clear - APCK; lia| exact I]].
      cbn [cells_size csize Nat.add]. eapply client_range_wsep; [exact CWK| | left; clear - PKLO SP1 SLO STK0 NS1; lia].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]. }
    assert (PRESa3 : presW asegs R HIA h3 LB LF (bv_unsigned sp) (arl_stklo R) WXF m m2).
    { eapply A_pk_parse_E.presW_step with (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (FB := FB) (sp1 := sp1) (hq := hq) (LBq := [(C, 232)] ++ LB) (W := [(C, C + 232)]) (mc := mm);
        first [ exact PRES | exact HP2 | exact HCSq3 | (rewrite E3stk; exact HS2) | eassumption | (clear - SP1; lia) | (intros b Hb; apply in_app_iff; right; exact Hb)
              | lazymatch goal with |- forall x, client_addr _ _ _ x -> _ => idtac end
              | match goal with |- ?g => idtac "PWS-LEFT:" g end ].
      intros x Hc _. cbn [outside]. split; [| exact I].
      intros K. exact (fresh_not_clientA R LB LF C 232 (bv_unsigned sp) x CFR ltac:(clear - ALO LOS SLO STK0 NS1; lia) Hc K). }
    assert (D3 : DINV2' WXF FB sp1 h3 (own' ++ LB) FSH0 kv p5 e1 (Z_to_bv 64 A_RSA_INFO) (Z_to_bv 64 C) m2).
    { eapply A_pk_parse_E.dinv2_presA with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (hq := hq) (LBq := [(C, 232)] ++ LB) (LBp := [(C, 232)] ++ LB) (W := [(C, C + 232)]) (mc := mm);
        first [ exact D | reflexivity | exact SP1 | exact F64 | exact FRSHq | exact ESq | exact HP2 | exact HH3 | exact HCSq3 | exact ST2 | exact MI2 | exact HPKA2 | exact PRESa3
              | eassumption
              | lazymatch goal with
                | |- forall b, In b LB -> In b _ => intros b Hb; apply in_app_iff; right; exact Hb
                | |- forall A n, FB <= A -> _ -> disjoint_from _ A n => intros A n H1 H2; cbn [disjoint_from]; split; [clear - H1 H2 APCF; lia| exact I]
                | |- forall A n, sp1 <= A -> disjoint_from _ A n => intros A n H1; cbn [disjoint_from]; split; [clear - H1 CF1 ALO LOS SP1 SLO STK0 NS1; lia| exact I]
                | |- disjoint_from _ PP 8 => cbn [disjoint_from]; split; [clear - APCP; lia| exact I]
                | |- disjoint_from _ BUF _ => cbn [disjoint_from]; split; [clear - APCB; lia| exact I]
                end
              | match goal with |- ?g => idtac "RSA-DINV-LEFT:" g end ]. }
    pose proof (presW_init_at R HIA h3 _ _ (own' ++ LB) LF m2 (bv_unsigned sp) (arl_stklo R) WBP h3 HH3
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb3.
    assert (APO' : forall b, In b own' -> PP + 8 <= fst b \/ fst b + snd b <= PP).
    { intros b Hb. apply OWN' in Hb. destruct Hb as [E|Hq]; [subst b; cbn [fst snd]; clear - APCP; lia|].
      pose proof (NEWF b Hq) as FRb.
      assert (FRb' : fresh_apart R LB LF (fst b) (snd b)).
      { eapply fresh_apart_frames_mono_sg; [eapply (fresh_apart_blocks_mono R ([(C, 232)] ++ LB) LB); [exact FRb| intros b' Hb'; apply in_app_iff; right; exact Hb']|].
        intros b' Hb'. eapply fdata_incl; [| exact Hb']. intros fb Hfb. right. exact Hfb. }
      assert (POSb : 0 < snd b).
      { unfold rsa_limb_blocks in Hq. dpose RAT2 as (_ & _ & _ & _ & _ & _ & _ & ALL2 & _). rewrite Forall_forall in ALL2.
        apply in_app_or in Hq. destruct Hq as [Hq|Hq]; destruct (MpiClient.mpd_blk_heap _ b Hq) as [O ->]; cbn [snd];
          [dpose (ALL2 (r_N r') ltac:(left; reflexivity)) as (_ & _ & _ & _ & _ & HOW)| dpose (ALL2 (r_E r') ltac:(right; left; reflexivity)) as (_ & _ & _ & _ & _ & HOW)];
          rewrite O in HOW; destruct HOW as (N1' & _); clear - N1'; lia. }
      pose proof (fresh_apart_objA _ _ PP 8 _ FRb' CWP ltac:(clear; lia) POSb) as K. clear - K. lia. }
    assert (ND3 : List.NoDup (own' ++ LB)) by exact (NoDup_map_inv fst _ (HND _ _ _ _ HH3)).
    assert (LEN3 : Z.of_nat (length own') <= CNTk).
    { pose proof (nodup_incl_len own' ((C, 232) :: rsa_limb_blocks r') (NoDup_app_remove_r _ _ ND3) ltac:(intros b Hb; apply OWN'; exact Hb)) as K.
      cbn [length] in K. pose proof (rsa_limb_blocks_len r'). unfold PKP_CNT. clear - K H. lia. }
    assert (C24' : cnt24 (own' ++ LB) <= cnt24 LB + (e1 - p5) / 5889).
    { pose proof (cnt24_incl (own' ++ LB) LB2 ND3 ltac:(intros b Hb; exact (Permutation_in b (Permutation_sym PERM) Hb))) as CI.
      cbn [app] in C24L. rewrite cnt24_cons_small in C24L by (clear; lia). clear - CI C24L. lia. }
    assert (EV3 : havol asegs R HIA h3 <= havol asegs R HIA h + (Vq + RSA_PP_PHI (END - P))) by (rewrite E3vol; clear - HV2 EVq MONO; lia).
    assert (EFR3 : hfr asegs R HIA h3 <= hfr asegs R HIA h + (Fq + RSA_PP_FR)) by (rewrite E3fr; clear - HFR2 EFRq; lia).
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj (proj2 (HKI3 mo2) HK2) (mo_frame_trans _ _ _ MF1 MF2))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { eapply A_pk_parse_F.seg_E with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (WB := WBP) (hq := h3) (LBq := own' ++ LB) (m2x := m2) (p5 := p5);
        first [ exact D3 | exact PRESb3 | exact HCSh3 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact ES3 | exact ET3
              | (intros b Hb; apply in_app_iff; right; exact Hb)
              | (apply wcover_inside; cbn [inside app]; left; clear; lia)
              | eassumption | match goal with |- ?g => idtac "SEGE-PRE-LEFT:" g end ]. }
    cbv beta. intros ms5 [(rc & a1v & a2v & RC & CQF)|EQ].
    - eapply (do_free h3 own' m2 FB sp1 kv p5 e1 rc A_RSA_INFO C a1v a2v _ (Vq + RSA_PP_PHI (END - P)) (Fq + RSA_PP_FR));
        first [ exact CQF | exact RC | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact CFB | exact AP | exact HCSh3 | exact ET3 | exact ES3 | exact EF3
              | exact EV3 | exact EFR3 | exact REP2 | exact SI2' | exact APO'
              | (clear - BV; lia) | (clear - BF; lia) | (unfold PKP_CNT; clear; lia)
              | match goal with |- ?g => idtac "RSA-FREE-LEFT:" g end ].
    - eapply (fin_exit h3 own' WXF FB sp1 (Z_to_bv 64 0));
        first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH3 | exact CFB | exact AP | exact HCSh3 | exact ET3 | exact ES3 | exact EF3 | exact LEN3
              | (intros x Hx; exact Hx)
              | lazymatch goal with
                | |- havol _ _ _ _ <= _ => clear - EV3 BV; unfold PHIpk, AVOL_CALL in BV; lia
                | |- hfr _ _ _ _ <= _ => clear - EFR3 BF; unfold FFRpk, fr_charge in BF; lia
                | |- context [FINQ] =>
                    eapply epiq_mono; [exact EQ|]; (intros mx HHx MIx PWx dd_H; ddestruct dd_H as (PBx & HPPx & HPx & HPKAx));
                    dexists 0, e1, A_RSA_INFO, C;
                    split; [reflexivity|]; split; [clear; lia|]; split; [exact HPPx|]; split; [exact HPx|]; split; [exact HPKAx|];
                    split; [eapply (pk_rep_frame asegs PK); [exact REP2| exact MIx| intros b Hb; apply in_app_iff; left; exact Hb| exact (own_agree h3 own' _ m2 mx PBx HHx APO')]|];
                    split; [intros K; exfalso; apply K; reflexivity|];
                    split; [exact (si_path h3 _ m2 mx PBx SI2')|];
                    pose proof (Z.div_le_mono (e1 - p5) (e1 - P) 5889 ltac:(clear; lia) ltac:(clear - Hp2a; lia)) as DM; clear - C24' DM; lia
                end
              | match goal with |- ?g => idtac "RSA-FIN-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis AMS : arl_amemset R = A_AMEMSET_PK.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis NM1 : 0 <= arl_need_malloc R.
  Hypothesis STK1 : 176 + ASN1_GET_ALG_STACK_A + arl_need_amem R <= STKk.
  Hypothesis STK10 : 176 + 128 + arl_need_malloc R + arl_need_amem R <= STKk.
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_PK.
  Hypothesis GETALG : asn1_get_alg_stmtA asegs R HIA A_ASN1_GET_ALG_PK.
  Hypothesis OIDPK : oid_lookup1_stmtA asegs R HIA A_OID_GET_PK_ALG OID_PK_ALG_STACK_A.
  Hypothesis OIDGA : oid_lookup1_stmtA asegs R HIA A_OID_GET_EC_GRP_ALGID OID_EC_GRP_ALGID_STACK_A.
  Hypothesis GETBSN : asn1_get_bitstring_null_stmtA asegs AL A_ASN1_GET_BITSTRING_NULL.
  Hypothesis PKSETUP : pk_setup_stmtA asegs R HIA MT A_RSA_INFO A_EC_INFOS A_PK_SETUP_PK.
  Hypothesis STK11 : 176 + PK_GET_PK_ALG_STACK_A <= STKk.
  Hypothesis STK12 : 176 + 320 + arl_need_amem R <= STKk.
  Hypothesis PKALG : pk_get_pk_alg_stmtA asegs R HIA A_PK_GET_PK_ALG.
  (* [comment removed for export] *)
  Hypothesis D0 : 0 <= d.
  Hypothesis PHE0 : forall n, 0 <= n -> 0 <= pk_ecparams_PHI n.
  Hypothesis PHS0 : forall n, 0 <= n -> 0 <= pk_set_pubkey_PHI ECP_MAX_N n.
  Hypothesis FRE0 : 0 <= pk_ecparams_FR (d + 1).
  Hypothesis FRS0 : 0 <= pk_set_pubkey_FR ECP_MAX_N (d + 1).
  Hypothesis CKP0 : 0 <= check_pubkey_PHIn (ecp_dy_sz ECP_MAX_N).
  Hypothesis CKF0 : 0 <= check_pubkey_FRn (ecp_dy_sz ECP_MAX_N) (d + 1).
  Hypothesis PHIM : forall a b, a <= b -> pk_set_pubkey_PHI ECP_MAX_N a <= pk_set_pubkey_PHI ECP_MAX_N b.
  Hypothesis PHIME : forall a b, a <= b -> pk_ecparams_PHI a <= pk_ecparams_PHI b.

  Local Notation XE' := (A_pk_parse_C.XE PP END PKA P).
  Local Notation SBQ' := (A_pk_parse_F.SBQ R HIA LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PP END PKA lo P BUF bs).

  #[using="Type"] Lemma aevtA_KF_equiv : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Ph1,(0.$1.VR,VHIA,)PQ,P,$7<.SpPms,$31.P,Pmo,$12.(13.(14.$1.VR,VHIA,R4.R1.)(14.$1.VR,VHIA,Vh,R1.))P,(4:.$1.(4;.$1.VR,VHIA,R4.Vmo0,)R3.R2.)(4:.$1.(4;.$1.VR,VHIA,Vh,Vmo0,)R4.R3.)")
(* [comment removed for export] *).
  Proof. intros h1 Q ms EQV H mo [HKx MFx]. apply H. split; [apply (proj2 (EQV mo)); exact HKx| exact MFx]. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L17604312231.0L18857372174.3L23565994354.0L28292264044.0L32586543723.0L38154991877.0L65110448706.3L957827166.0  00000100;00<00=00>00?00I00JSS3END1P2N0SSSSS3END1P2PES". (* [comment removed for export] *)
  #[using="PE PHE0 PHS0"] Lemma budget_facts : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "(9.(29.=$7=.)(9.(29.=(78.(30.VEND,VP,)))(9.(29.=(75.(30.VEND,VP,)))(9.(29.=$6>.)(9.(29.=(5<.$5=.(30.VEND,VP,)))(9.(29.=(4>.=))(9.(29.=$79.)(9.(29.=$6?.)(29.=(4?.=+1<.))))))))))")
(* [comment removed for export] *).
  Proof.
    assert (N0 : 0 <= END - P) by (clear - PE; lia).
    split; [unfold PK_SETUP_PHI, A_pk_wrap_alloc.ECKEY_ALLOC_WRAP_PHI, AVOL_CALL; clear; lia|].
    split; [unfold RSA_PP_PHI, MPI_RB_PHI, AVOL_CALL; clear - N0; lia|].
    split; [exact (PHE0 _ N0)|].
    split; [unfold pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL; clear; lia|].
    split; [exact (PHS0 _ N0)|].
    split; [unfold PHIpk, AVOL_CALL; clear; lia|].
    split; [unfold RSA_PP_FR, MPI_RB_FR, fr_charge; clear; lia|].
    split; [unfold pk_set_group_FR, group_load_FRn, calls_FR, fr_charge; clear; lia|].
    unfold FFRpk, fr_charge. clear. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L15320669407.2L4233398872.11L4233399509.9 L43423718831.0L51508673957.0L67092310858.4L9945892861.4 00000600W00k00l00m01901GS1r2RrS1R3HIA1h3END1P2B12B22B32B42B52B6S1R3HIA1h1d2B72B82B9SSS2LB1P2p'2DPS3END1P2p'3Hp'". (* [comment removed for export] *)
  #[using="IMG NS1 STKk LOS STK0 SLO TOP LFB PE PPLO CWP PKLO CWK HH0 SIP0 SSH0 SLO1 PPOD PKOD HND PHE0 PHS0"] Lemma early_exit : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Ph1,(0.$1.VR,VHIA,)PFB,$;.Psp1,$;.Pa0v,(4.&40.)Pms,$31.P,(32.VR,VHIA,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,R5.R5.VLB,VLB,Vm,(1<.(22.$;.$;.)(23.$;.$;.VPP,(24.VPP,+8.))(1<.(22.$;.$;.)(23.$;.$;.VPKA,(24.VPKA,+10.))(1?.(22.$;.$;.))))R4.R3.R2.(7>.VPP,VEND,VPKA,VP,R2.)R1.)P,(9.(29.(30.(35.&40.Vsp,)+;0.)R4.)(29.R4.(30.(35.&40.Vsp,)+:0.)))P,(:.$;.(42.R5.+20.)=)P,(:.$;.(42.R7.+40.)=)P,(43.VR,VLB,VLF,R8.+100.)P,(44.(<.$1.VR,VHIA,Vh,)R9.+100.)P,PB,$;.Pj,$;.P,(37.(22.$;.$;.)(23.$;.$;.R2.R1.)VLF,)(39.(29.(24.R=.+100.)R3.)(29.(24.R3.R2.)R=.))P,(:.P,$;.Sp(<.$1.VR,VHIA,R<.)(<.$1.VR,VHIA,Vh,))P,(:.$;.(=.$1.VR,VHIA,R=.)(=.$1.VR,VHIA,Vh,))P,(:.$;.(>.$1.VR,VHIA,R>.)(>.$1.VR,VHIA,Vh,))P,(:.$;.(?.$1.VR,VHIA,R?.)(?.$1.VR,VHIA,Vh,))P,(:.$;.(10.$1.VR,VHIA,R10.)(10.$1.VR,VHIA,Vh,))P,(:.$;.(11.$1.VR,VHIA,R11.)(11.$1.VR,VHIA,Vh,))(4:.$1.(4;.$1.VR,VHIA,R12.Vmo0,)(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)R>.)")
(* [comment removed for export] *).
  Proof.
    intros h1 FB sp1 a0v ms EQ SP1 SP1M F64 FRSH CFB AP Ehcs Ehtop Estk Eflag Evol Efr.
    ddestruct budget_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    eapply (fin_exit h1 [] X00 FB sp1 a0v);
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact AP | exact Ehtop | exact Estk | exact Eflag
            | (intros x Hx; rewrite Ehcs; exact Hx)
            | lazymatch goal with
              | |- forall x, outside _ x -> outside X00 x => intros x Hx; exact (proj1 (proj1 (outside_app _ _ x) Hx))
              | |- havol _ _ _ _ <= _ => rewrite Evol; unfold PKP_PHI; clear - B1 B2 B3 B4 B5 B6; lia
              | |- hfr _ _ _ _ <= _ => rewrite Efr; unfold PKP_FFR, fr_charge; clear - B7 B8 B9 FRE0 FRS0; lia
              | |- Z.of_nat (length []) <= _ => cbn [length Z.of_nat]; unfold PKP_CNT; clear; lia
              | |- context [FINQ] =>
                  eapply epiq_mono; [exact EQ|]; (intros mx HHx MIx PWx dd_H; ddestruct dd_H as (r & p' & Ea & Rr & HPPx & Hp' & HPKAx));
                  dexists r, p', 0, 0;
                  split; [exact Ea|]; split; [clear - Rr; lia|]; split; [exact HPPx|]; split; [exact Hp'|]; split; [exact HPKAx|];
                  split; [apply (pk_rep_null asegs PK)|]; split; [intros _; repeat split; reflexivity|];
                  split; [eapply (si_heap_presx asegs L SI); [exact SIP0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PWx))|];
                          intros a Ha; exact (si_outside2 L SI PP 8 PKA 16 a PPOD PKOD Ha)|];
                  cbn [app]; pose proof (Z.div_pos (p' - P) 5889 ltac:(clear - Hp'; lia) ltac:(clear; lia)) as DP; clear - DP; lia
              end
            | match goal with |- ?g => idtac "EARLY-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00l0?L10837002389.2 L12654381620.1 L13165066323.9 L13167710465.3 L13748187931.9 L14565458108.3 L15320419519.2 L1540877545.3  L17117663799.0 L19965341046.16L21014960645.7 L21014960772.14L2412282163.12 L26572233507.6 L29892191849.0 L33804787453.4 L34435497065.2 L3480690467.16 L36430639082.4 L37796632789.0 L38818802022.16L38948636245.0 L39316637317.0 L39332637397.0 L3961845025.6  L43167789172.4 L43300649301.0 L43423718831.0 L44920591204.6 L450113426.4   L48285541379.8 L48323742628.2 L50790580594.8 L51042627313.9 L51508673957.0 L51595685011.2 L52795256714.8 L52826239822.9 L52828953116.3 L58411082547.12L59308664168.1 L59309005011.3 L59309005011.4 L59309005011.5 L59309005011.6 L59309005011.7 L61522160417.0 L62018535662.1 L62050552506.9 L64011996548.13L64115649086.4 L64850595401.0 L66082958749.2 L66566231137.9 L66567912755.3 L66610540230.13L66616831174.11L67092310858.4 L9356559645.13 L9544301958.8  00000800=00>00?00K00W00]00i00j01B01X02K02d02m02n03>03?03I03W03X04804904:04;04A04B04C04D04M04X04k04l05K05L05M05Y05i05j05k06M06Q06Z06[06\06]06^06_06b06o07_07m07n07o08008108V09209>0:10:AS3BUF2bsS3BUFFFS2PP2lo4PPLOS2PP3PKA3DPKS1r2ERS2sp3sp13SP1SS1R3HIA1h2sp3TOP3sp13SP1S3PKA2FB3APK1A1n2H12H2S1R3NS12sp3PKA2lo4STKk4STK03SLO4PKLO3sp13SP11A1n2H1S1R3HIA1h1d4BUDF2B72B82B9S1d2B72B8SS3PKA3BUF2bs3DKBFS3sp14SP1MS1R1C3CF14ACV'SS1R2sp2lo4STKk3SLO5STK103sp13SP1SSSS1d2B8FSSS1d2B72B8S2PP1C2SZ1KS3END1P2B22B32B42B5FS1R3NS12sp2lo4STKk3LOS4STK03SLOFSS4info5INFO1S3END1P2B32B42B5FFS1R3HIA1h3END1P3BUD2B22B32B42B52B6S2EIS1r2ER2R0FFFFSS1RS3PKA2lo4PKLOS3END1P3BUF2bs2BP2EB2Lw2p12p24Hp1a4Hp124Hp2e3HeES3END1P2p53HPxSFFFS1R3HIA1h3END1P2B22B32B42B52B62h23EV2S1R3HIA1h1d2B72B82B92h24EFR2S2LB1P2p52DPS1R3NS12sp2lo4STKk3LOS4STK03SLO3ALO3ACV3SPR3sp13SP1S3END1P2B22B32B4". (* [comment removed for export] *)
  #[using="IMG UARG SM2 NS1 STKk BUF bs LOS STK0 SLO TOP SPA TPV LFB PPB PKB ENDB HBS0 BIN BP PE EB B47 BUF0 BL30 PPAL PP0 PPLO CWP PKAL PK0 PKLO CWK DPK DPB DKB HH0 MI0 SIP0 NDL SSH0 SLO1 SLO2 UW0 PPOD PKOD DIMG NB1 STK2 RTCL HND HMPERM SIP SIFP BUD BUDF STK3 PKFREE STK4 SETPUB MCOK IDOK BPOK LFN C24H STK5 USERFC STK6 STK7 USEECP STK8 STK9 RSAPP AMS NA1 STK1 STK10 GETTAG GETALG OIDPK OIDGA GETBSN PKSETUP PHE0 PHS0 FRE0 FRS0 CKF0 PHIM PHIME STK11 STK12 PKALG"] Lemma pk_main : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G ()) "Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(14.$1.VR,VHIA,Vh,Vmo0,)P,(7?.$1.Vm,Vlo,(35.&40.Vsp,))P,(1:.$1.Vm,VPP,(1<.$1=.(1>.(25.&40.VP,))(1?.$1=.)))P,(80.$1.(5;.VR,)(<.$1.VR,VHIA,Vh,)Vm,VPP,+8.)P,(1:.$1.Vm,VPKA,(1<.$1=.(1>.(25.&40.=))(1<.$1=.(1>.(25.&40.=))(1?.$1=.))))P,(80.$1.(5;.VR,)(<.$1.VR,VHIA,Vh,)Vm,VPKA,+10.)(81.$1.(4<.$1.VR,VHIA,(2;.VMT,)VSI,$45.$46.$49.Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VPKA,Vlo,Vslo,Vd,Vm,Vmo0,)(82.(83.(84.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(25.&40.VPP,)(25.&40.VEND,)(25.&40.VPKA,)R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.$85.)Vfc,(86.(4.&40.))Vm,(87.$1.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HK0 ST HPP0 OPP0 HPKA0 OPKA0.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH0) as HTOP.
    ddestruct budget_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply A_pk_parse_A.pro_walk with (lo := lo) (STKk := STKk) (PP := PP) (END := END) (PKA := PKA); eassumption. }
    intros ms1 P1.
    ddestruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & z0 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & w0 & w1 & w2
                   & pc0 & pc1 & lenj & kpad & gpad & w8 & w16 & w24 & jpar
                   & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & LPKC & LLEN & LPAR & LALG & LGID & FSHX
                   & SAVE & SLOTS & SLOT48 & STlo & STmid & SThi & STbelow & MI1 & PRES0).
    subst ms1.
    apply (aevtA_KF_equiv h1 _ _ HKI).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO STK0 NS1 LOS ALO ACV; lia).
    ddestruct (frame_factsA R HIA CS h1 LB LF m1 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1' & F2' & F3') & F8' & FBLO & SBND & APS).
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HP01) as HPX01.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros x Hx; eapply hcs_below_top; exact Hx).
    (* [comment removed for export] *)
    assert (CRPPs : client_range L (LB ++ fdata LF) (bv_unsigned sp) PP 8) by (eapply client_range_wsep; [exact CWP| intros b Hb; exact Hb| left; clear - PPLO SLO STK0 NS1; lia]).
    assert (CRPKs : client_range L (LB ++ fdata LF) (bv_unsigned sp) PKA 16) by (eapply client_range_wsep; [exact CWK| intros b Hb; exact Hb| left; clear - PKLO SLO STK0 NS1; lia]).
    assert (HPP1 : rw_cells asegs m1 PP [C8 (Z_to_bv 64 P)]) by (eapply heap_presx_rw_cells; [exact HPX01| exact HPP0| exact CRPPs| cbn; exact I]).
    assert (HPKA1 : rw_cells asegs m1 PKA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (eapply heap_presx_rw_cells; [exact HPX01| exact HPKA0| exact CRPKs| cbn; exact I]).
    assert (OPP1 : aobj asegs AL (hcs asegs R HIA h1) m1 PP 8).
    { rewrite Ehcs. eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OPP0| exact CRPPs| clear - LOS SLO STK0 NS1; lia| exact TOPCS]. }
    assert (OPKA1 : aobj asegs AL (hcs asegs R HIA h1) m1 PKA 16).
    { rewrite Ehcs. eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OPKA0| exact CRPKs| clear - LOS SLO STK0 NS1; lia| exact TOPCS]. }
    assert (HBS1 : bytes_at asegs m1 BUF bs).
    { eapply heap_presx_bytes_at; [exact HPX01| exact HBS0| eapply client_range_block; [apply in_app_iff; left; exact BIN| clear; lia| clear; lia]| cbn; exact I]. }
    assert (LFN1 : (length LF + 1 < 512)%nat) by (clear - LFN; lia).
    assert (STK3c : 176 + 128 + arl_need_smalloc R <= STKk) by (clear - STK9; lia).
    assert (STK4c : 176 + 176 + arl_need_bcmp R <= STKk) by (clear - STK7 NB1; lia).
    assert (STK5c : 176 + 144 + arl_need_smalloc R <= STKk) by (clear - STK9; lia).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo0).
    { eapply A_pk_parse_C.seg_A1 with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (h1 := h1);
        first [ eassumption | reflexivity | match goal with |- ?g => idtac "SEGA1-PRE-LEFT:" g end ]. }
    assert (KFC : forall hx hy Q ms, (forall mo, HK asegs R HIA hx mo <-> HK asegs R HIA hy mo) ->
                  aevtA asegs (KF asegs R HIA hx mo0) Q ms -> aevtA asegs (KF asegs R HIA hy mo0) Q ms).
    { intros hx hy Q ms EQV H mo [HKx MFx]. apply H. split; [apply (proj2 (EQV mo)); exact HKx| exact MFx]. }
    cbv beta. intros ms2 [(hq & a0v & HSQ & EQ)|(h2 & HS2 & MQ)].
    { destruct HSQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      apply (KFC hq h1 _ _ Q7).
      assert (EQ2 : EPIQ' hq hq LB LB m X00 FB sp1 a0v (XE' a0v) ms2).
      { unfold A_pk_parse_B.EPIQ in EQ |- *.
        repeat (let x := fresh "x" in destruct EQ as [x EQ]; exists x).
        decompose [and] EQ.
        repeat match goal with |- _ /\ _ => split end;
          first [ eassumption | eapply (presW_hmono R HIA h1 hq); [eassumption| rewrite Q1; intros y Hy; exact Hy| exact Q3] ]. }
      eapply (early_exit hq FB sp1 a0v);
        first [ exact EQ2 | exact (eq_trans Q1 Ehcs) | exact (eq_trans Q2 Ehtop) | exact (eq_trans Q3 Estk)
              | exact (eq_trans Q4 Eflag) | exact (eq_trans Q5 Evol) | exact (eq_trans Q6 Efr) | eassumption ]. }
    destruct HS2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    apply (KFC h2 h1 _ _ Q7).
    rewrite <- Q1 in Ehcs, HCS1, OPP1, OPKA1. rewrite <- Q2 in Ehtop. rewrite <- Q3 in Estk.
    rewrite <- Q4 in Eflag. rewrite <- Q5 in Evol. rewrite <- Q6 in Efr.
    pose proof (fun mo => iff_trans (Q7 mo) (HKI mo)) as HKI2.
    clear HKI HH1 Q1 Q2 Q3 Q4 Q5 Q6 Q7. rename HKI2 into HKI. rename h1 into h1o, h2 into h1.
    assert (BLEN0 : 0 < BLEN).
    { destruct MQ as (mq & qra & q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & v0 & v1 & v2 & vc0 & vc1 & Lw & vkv & vkpad & vgv & vgpad
                     & p1 & p2 & pp & ptag & ppad & plen
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                     & Hp1a & Hp12 & Hp2e & HeE & _).
      clear - Hp1a Hp12 Hp2e HeE BP EB; lia. }
    assert (STK5x : 176 + 64 <= STKk) by (clear - STK11; unfold PK_GET_PK_ALG_STACK_A in STK11; lia).
    eapply (aevtA_cut_evtA_KF asegs R HIA h1 mo0).
    { eapply A_pk_parse_D.seg_A2 with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (h1 := h1);
        first [ eassumption | reflexivity | match goal with |- ?g => idtac "SEGA2-PRE-LEFT:" g end ]. }
    cbv beta. intros ms3 [(a0v & EQ)|CQS].
    { eapply (early_exit h1 FB sp1 a0v); eassumption. }
    (* [comment removed for export] *)
    ddestruct CQS as (mc & c0 & c1 & c2 & ca2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & kv & p5 & e1 & info & Emc & DV & EINFO & INFO1).
    subst ms3.
    pose proof (A_pk_parse_E.dinv2_of_dinv R HIA LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP END PKA lo P BUF bs FB sp1 h1 _ kv p5 e1 mc DV) as D2.
    assert (SIc : si_P SI mc).
    { ddestruct D2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & D2'). 
      repeat (lazymatch type of D2' with _ /\ (_ /\ _) => destruct D2' as (_ & D2') end). destruct D2' as (_ & PRESx).
      eapply (si_heap_presx asegs L SI); [exact SIP0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ _ _ _ _ _ _ PRESx))|].
      intros a Ha. exact (si_outside2 L SI PP 8 PKA 16 a PPOD PKOD Ha). }
    pose proof (dinv2_widen X00 WXF _ _ _ _ _ _ _ _ _ _ _ D2 ltac:(intros x Hx; exact (proj1 (proj1 (outside_app _ _ x) Hx)))) as D. clear D2 DV.
    pose proof D as D0'.
    ddestruct D0' as (u0 & u1 & u2 & uc0 & uc1 & uLw & ukpad & gv & ugpad & upp & up1v & uptag & uppad & uplen
                   & HHc & FHDc & LPKCc & LLENc & LPARc & LALGac & LALGbc & LGIDac & LGIDbc & FSHXc & SAVEc & SLOTSc & SLOT48c & STloc & STmidc & SThic & STbelowc & MIc
                   & HPPc & OPPc & HPKAc & OPKAc & HBSc & OBUFc & Hp2a & Hp2e' & HeE' & Hp1v & Hp1v2 & PPCc & PRESc).
    pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
    pose proof (frame_apart_obj R HIA LB LF lo _ PKA 16 FB 256 FRSH CWK ltac:(clear; lia) ltac:(clear; lia) LOS) as APK.
    pose proof (art_data_lo asegs R HIA) as DLOW.
    pose proof PKSETUP as PS'. unfold pk_setup_stmtA, A_PK_SETUP_PK in PS'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply PS' with (h := h1) (LB := LB) (LF := (FB, 256) :: LF) (PKA := PKA) (info := info) (lo := lo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehtop, ?Evol, ?Efr;
        first [ exact HHc | exact HK1 | exact HPKAc | exact PKAL | exact PK0 | exact OPKAc | exact STbelowc | exact LOS | exact MIc | exact TPV | reflexivity
              | lazymatch goal with
                | |- info = A_RSA_INFO \/ _ => clear - INFO1; unfold A_PK_INFOS, A_EC_INFOS in *; cbn [In] in *;
                       destruct INFO1 as [E|[E|[E|[E|[]]]]]; [left; symmetry; exact E| right; left; exact E| right; right; left; exact E| right; right; right; left; exact E]
                | |- PKA + 16 <= lo \/ _ => left; exact PKLO
                | |- client_wrange _ _ _ _ PKA 16 => eapply client_wrange_mono; [exact CWK| intros b Hb; apply fdata_cons_sub; exact Hb]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - BUD B1 B2 B3 B4 B5 B6; unfold PKP_PHI in BUD; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - BUDF B7 B8 B9 FRE0 FRS0; unfold PKP_FFR in BUDF; unfold fr_charge in *; lia
                | |- _ => clear - SP1 SP1M SLO STK0 STK10 NS1 NA1 NM1 TOP; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "SETUP-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0' & q1' & q2' & qa1' & qa2' & qa3' & qa4' & qa5' & qa6' & qa7' & q3' & q4' & q5' & q6' & m2 & mo2 & h2 & r & C & SZ
                    & E4 & MI2 & ST2 & MF2 & WM2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & DISJ).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xb052c)) with (Z_to_bv 64 0xb052c : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R.
    rewrite Ehtop in HT2. rewrite Eflag in HF2. rewrite Evol in HV2. rewrite Efr in HFR2.
    assert (HS2' : hstkhi asegs R HIA h2 = hstkhi asegs R HIA h) by (rewrite HS2; exact Estk).
    assert (HCSh2 : forall x, CS x -> hcs asegs R HIA h2 x) by (intros x Hx; apply HCS2, HCS1, Hx).
    assert (SI2 : si_P SI m2).
    { eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)|].
      intros a Ha. exact (si_outside1 L SI PKA 16 a PKOD Ha). }
    assert (PRESa2 : presW asegs R HIA h2 LB LF (bv_unsigned sp) (arl_stklo R) WXF m m2).
    { eapply A_pk_parse_E.presW_step with (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (FB := FB) (sp1 := sp1) (hq := h1) (LBq := LB) (W := [(PKA, PKA + 16)]) (mc := mc);
        first [ exact PRESc | exact HP2 | exact HCS2 | (exact HS2) | eassumption | (clear - SP1; lia) | (intros b Hb; exact Hb)
              | lazymatch goal with |- forall x, client_addr _ _ _ x -> _ => idtac end
              | match goal with |- ?g => idtac "PWS-LEFT:" g end ].
      intros x _ Hx. apply (proj1 (outside_app _ _ x)) in Hx. destruct Hx as [Hx _]. cbn [outside] in Hx |- *. clear - Hx. tauto. }
    assert (DSTEP : forall LB2 (pk0' pk1' : word), HM asegs R HIA h2 LB2 ((FB, 256) :: LF) m2 -> rw_cells asegs m2 PKA [C8 pk0'; C8 pk1'] ->
                      DINV2' WXF FB sp1 h2 LB2 FSH0 kv p5 e1 pk0' pk1' m2).
    { intros LB2 pk0' pk1' HH2 HPKA2.
      eapply A_pk_parse_E.dinv2_presA with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (hq := h1) (LBq := LB) (LBp := LB) (W := [(PKA, PKA + 16)]) (mc := mc);
        first [ exact D | reflexivity | exact SP1 | exact F64 | exact FRSH | exact Estk | exact HP2 | exact HH2 | exact HCS2 | exact ST2 | exact MI2 | exact HPKA2 | exact PRESa2
              | eassumption
              | lazymatch goal with
                | |- forall b, In b LB -> In b LB => intros b Hb; exact Hb
                | |- forall A n, FB <= A -> _ -> disjoint_from _ A n => intros A n H1 H2; cbn [disjoint_from]; split; [clear - H1 H2 APK; lia| exact I]
                | |- forall A n, sp1 <= A -> disjoint_from _ A n => intros A n H1; cbn [disjoint_from]; split; [clear - H1 PKLO SP1 SLO STK0 NS1; lia| exact I]
                | |- disjoint_from _ PP 8 => cbn [disjoint_from]; split; [clear - DPK; lia| exact I]
                | |- disjoint_from _ BUF _ => cbn [disjoint_from]; split; [clear - DKB; lia| exact I]
                end
              | match goal with |- ?g => idtac "SETUP-DINV-LEFT:" g end ]. }
    assert (EV2 : havol asegs R HIA h2 <= havol asegs R HIA h + PK_SETUP_PHI) by exact HV2.
    assert (EFR2 : hfr asegs R HIA h2 <= hfr asegs R HIA h + fr_charge 0) by exact HFR2.
    destruct DISJ as [(ER & HH2 & HPKA2)|(ER & C16 & CFR' & CSTK & HH2 & HPKA2 & RSAC & ECC)].
    - (* [comment removed for export] *)
      pose proof (DSTEP LB _ _ HH2 HPKA2) as D3.
      pose proof (presW_init_at R HIA h2 _ _ LB LF m2 (bv_unsigned sp) (arl_stklo R) WBP h2 HH2
                    ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb2.
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo0).
      { eapply A_pk_parse_F.seg_B with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (WB := WBP) (hq := h2) (LBq := LB) (m2x := m2) (p5 := p5) (r := r) (info := 0);
          first [ exact D3 | exact PRESb2 | exact HCSh2 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact HS2' | exact HT2
                | (intros b Hb; exact Hb) | (right; exact ER) | (intros R0; exfalso; clear - ER R0; lia)
                | eassumption | match goal with |- ?g => idtac "SEGB1-PRE-LEFT:" g end ]. }
      cbv beta. intros ms5 SB.
      destruct SB as [(RNZ & EQ)|[(? & R0 & _)|[(? & R0 & _)|[(R0 & _)|(? & ? & ? & R0 & _)]]]]; try (exfalso; clear - ER R0; lia).
      eapply (fin_exit h2 [] WXF FB sp1 (Z_to_bv 64 r));
        first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact AP | exact HCSh2 | exact HT2 | exact HS2' | exact HF2
              | (intros x Hx; exact Hx)
              | lazymatch goal with
                | |- havol _ _ _ _ <= _ => unfold PKP_PHI; clear - EV2 B1 B2 B3 B4 B5 B6; lia
                | |- hfr _ _ _ _ <= _ => unfold PKP_FFR; clear - EFR2 B7 B8 B9 FRE0 FRS0; lia
                | |- Z.of_nat (length []) <= _ => cbn [length Z.of_nat]; unfold PKP_CNT; clear; lia
                | |- context [FINQ] =>
                    eapply epiq_mono; [exact EQ|]; (intros mx HHx MIx PWx dd_H; ddestruct dd_H as (PBx & HPPx & HPx & HPKAx));
                    dexists r, p5, 0, 0;
                    split; [reflexivity|]; split; [clear - ER; lia|]; split; [exact HPPx|]; split; [exact HPx|]; split; [exact HPKAx|];
                    split; [apply (pk_rep_null asegs PK)|]; split; [intros _; repeat split; reflexivity|];
                    split; [exact (si_path h2 _ m2 mx PBx SI2)|];
                    cbn [app]; pose proof (Z.div_pos (p5 - P) 5889 ltac:(clear - HPx; lia) ltac:(clear; lia)) as DP; clear - DP; lia
                end
              | match goal with |- ?g => idtac "SETUPFAIL-FIN-LEFT:" g end ].
    - (* [comment removed for export] *)
      change ((C, SZ) :: LB) with ([(C, SZ)] ++ LB) in HH2, RSAC, ECC.
      pose proof (DSTEP _ _ _ HH2 HPKA2) as D3.
      assert (CFR : fresh_apart R LB LF C SZ).
      { eapply fresh_apart_frames_mono_sg; [exact CFR'|]. intros b' Hb'. eapply fdata_incl; [| exact Hb']. intros fb Hfb. right. exact Hfb. }
      pose proof (fresh_apart_relist_sg R HIA h2 LB ([(C, SZ)] ++ LB) LF m2 FB 256 FRSH HH2) as FRSH2.
      pose proof (presW_init_at R HIA h2 _ _ ([(C, SZ)] ++ LB) LF m2 (bv_unsigned sp) (arl_stklo R) WBP h2 HH2
                    ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb2.
      assert (INFOC : info = A_RSA_INFO \/ (info <> A_RSA_INFO /\ In info A_EC_INFOS)).
      { clear - INFO1. unfold A_PK_INFOS, A_EC_INFOS, A_RSA_INFO, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in *. cbn [In] in *. lia. }
      assert (TVEC : A_pk_parse_D.TVAL kv = 2 \/ A_pk_parse_D.TVAL kv = 3 -> info <> A_RSA_INFO /\ In info A_EC_INFOS).
      { intros [E|E]; rewrite EINFO, E; (split; [vm_compute; intros K; discriminate K|]);
          first [left; vm_compute; reflexivity | right; left; vm_compute; reflexivity | right; right; left; vm_compute; reflexivity]. }
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo0).
      { eapply A_pk_parse_F.seg_B with (h := h) (lo := lo) (STKk := STKk) (m := m) (PP := PP) (END := END) (PKA := PKA) (P := P) (BUF := BUF) (bs := bs) (WX := WXF) (WB := WBP) (hq := h2) (LBq := [(C, SZ)] ++ LB) (m2x := m2) (p5 := p5) (r := r) (info := info);
          first [ exact D3 | exact PRESb2 | exact HCSh2 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH2 | exact HS2' | exact HT2
                | (intros b Hb; apply in_app_iff; right; exact Hb) | (left; exact ER) | (intros _; split; [exact EINFO| exact INFO1])
                | eassumption | match goal with |- ?g => idtac "SEGB2-PRE-LEFT:" g end ]. }
      cbv beta. intros ms5 SB.
      destruct SB as [(RNZ & _)|[(id & _ & IDV & TV & CQG)|[(a2v & _ & TV & CQE)|[(_ & TV & CQR)|(rc & a1v & a2v & _ & RC & CQF)]]]].
      + exfalso. exact (RNZ ER).
      + (* [comment removed for export] *)
        destruct (TVEC TV) as [NRSA EI]. ddestruct (ECC NRSA) as (ESZ & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & pd & qX & qY & qZ & KP2). subst SZ.
        eapply (do_group h2 m2 FB sp1 kv p5 e1 info C id idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ PK_SETUP_PHI (fr_charge 0));
          first [ exact CQG | exact IDV | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH2 | exact CFB | exact AP | exact HCSh2 | exact HT2 | exact HS2' | exact HF2
                | exact EV2 | exact EFR2 | exact B1 | exact B5 | exact FRS0 | exact CKP0 | exact CKF0 | exact PHIM | exact MI2 | exact SI2 | exact KP2 | exact EI | exact C16 | exact CFR
                | (unfold fr_charge; clear; lia) | (unfold PKP_CNT; clear; lia)
                | (unfold PKP_PHI; clear - B1 B2 B3 B4 B5 B6; lia) | (unfold PKP_FFR; clear - B7 B8 B9 FRE0 FRS0; lia)
                | match goal with |- ?g => idtac "MAIN-SG-LEFT:" g end ].
      + (* [comment removed for export] *)
        destruct (TVEC TV) as [NRSA EI]. ddestruct (ECC NRSA) as (ESZ & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & pd & qX & qY & qZ & KP2). subst SZ.
        eapply (do_ecparams h2 m2 FB sp1 kv p5 e1 info C a2v idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ PK_SETUP_PHI (fr_charge 0));
          first [ exact CQE | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH2 | exact CFB | exact AP | exact HCSh2 | exact HT2 | exact HS2' | exact HF2
                | exact EV2 | exact EFR2 | exact B1 | exact B5 | exact FRS0 | exact FRE0 | exact CKP0 | exact CKF0 | exact PHIM | exact PHIME | exact MI2 | exact SI2 | exact KP2
                | exact EI | exact C16 | exact CFR | exact BLEN0
                | (apply PHE0; clear; lia) | (unfold fr_charge; clear; lia) | (unfold PKP_CNT; clear; lia)
                | (unfold PKP_PHI; clear - B1 B2 B3 B4 B5 B6; lia) | (unfold PKP_FFR; clear - B7 B8 B9 FRE0 FRS0; lia)
                | match goal with |- ?g => idtac "MAIN-UE-LEFT:" g end ].
      + (* [comment removed for export] *)
        assert (EI : info = A_RSA_INFO) by (rewrite EINFO, TV; reflexivity).
        destruct (RSAC EI) as (ESZ & RAT2). subst SZ. rewrite EI in CQR.
        eapply (do_rsa h2 m2 FB sp1 kv p5 e1 C PK_SETUP_PHI (fr_charge 0));
          first [ exact CQR | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH2 | exact CFB | exact AP | exact HCSh2 | exact HT2 | exact HS2' | exact HF2
                | exact EV2 | exact EFR2 | exact B1 | exact MI2 | exact SI2 | exact RAT2 | exact CFR
                | (unfold fr_charge; clear; lia) | (unfold PKP_CNT; clear; lia)
                | (unfold PKP_PHI; clear - B1 B2 B3 B4 B5 B6; lia) | (unfold PKP_FFR; clear - B7 B8 B9 FRE0 FRS0; lia)
                | match goal with |- ?g => idtac "MAIN-RSA-LEFT:" g end ].
      + (* [comment removed for export] *)
        dpose CFR as (CF0 & CF1 & CF2 & CF3). pose proof (alloc_ceiling_val R) as ACV'.
        assert (REP2 : pk_rep asegs PK m2 ([(C, SZ)] ++ LB) PKA info C [(C, SZ)]).
        { cbn [PKA_inst PKC_inst pk_rep]. destruct INFOC as [EI|[NRSA EI]].
          - destruct (RSAC EI) as (ESZ & RAT2). subst SZ. rewrite EI.
            eapply (rsa_rep_introA asegs); [unfold A_RSA_INFO; clear; lia| exact MI2| exact RAT2| clear; intros b; cbn [In rsa_limb_blocks rsa_fresh r_N r_E mpd_blk mpd_z md_own app]; split; intros K; exact K].
          - ddestruct (ECC NRSA) as (ESZ & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & pd & qX & qY & qZ & KP2). subst SZ.
            assert (NOH : forall e, In e (kp_mpds (kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ)) -> md_own e = LHeap -> False).
            { intros e He O. unfold kp_mpds, kp_init, grp_mpds, grp_init in He.
              cbn [kp_grp kp_d kp_Q g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In] in He. unfold mpd_init in He.
              decompose [or] He; try contradiction; subst e; cbn in O; discriminate. }
            eapply (ec_rep_introA asegs); [exact EI| | exact MI2| exact (HND _ _ _ _ HH2)| exact KP2| left; reflexivity
              | intros d1 d2 H1 _ _ O1 _; exfalso; exact (NOH d1 H1 O1) | intros e He O; exfalso; exact (NOH e He O) | exact C16| clear - CF1 ACV'; lia|].
            + intros E0. rewrite E0 in EI. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI. clear - EI. lia.
            + intros b. unfold kp_blocks, kp_init, grp_blocks, grp_mpds, grp_init, pt_blocks.
              cbn [kp_grp kp_d kp_Q g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z flat_map app mpd_blk md_own mpd_init]. split; intros Hx; exact Hx. }
        assert (SZP : 0 < SZ) by (destruct INFOC as [EI|[NRSA _]]; [destruct (RSAC EI) as (-> & _)| destruct (ECC NRSA) as (-> & _)]; clear; lia).
        assert (APO : forall b, In b [(C, SZ)] -> PP + 8 <= fst b \/ fst b + snd b <= PP).
        { intros b [<-|[]]. cbn [fst snd]. pose proof (fresh_apart_objA _ _ PP 8 _ CFR CWP ltac:(clear; lia) SZP) as K. clear - K. lia. }
        eapply (do_free h2 [(C, SZ)] m2 FB sp1 kv p5 e1 rc info C a1v a2v _ PK_SETUP_PHI (fr_charge 0));
          first [ exact CQF | exact RC | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact FRSH2 | exact CFB | exact AP | exact HCSh2 | exact HT2 | exact HS2' | exact HF2
                | exact EV2 | exact EFR2 | exact REP2 | exact SI2 | exact APO
                | (unfold PKP_CNT; clear; lia)
                | (unfold PKP_PHI; clear - B1 B2 B3 B4 B5 B6; lia) | (unfold PKP_FFR; clear - B7 B8 B9 FRE0 FRS0; lia)
                | match goal with |- ?g => idtac "MAIN-FREE-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End WalkPKG.
