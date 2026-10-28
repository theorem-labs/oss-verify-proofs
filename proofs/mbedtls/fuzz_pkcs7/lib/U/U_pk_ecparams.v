(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Arr MpiCoreAux MpiWalkAux Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_ecp_group_init U_mpi_cmp U_mpi_bitlen U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_C U_pk_ecparams_D U_pk_ecparams_E U_pk_ecparams_F U_pk_ecparams_G U_asn1_get_tag U_asn1_get_int U_asn1_get_mpi U_mpi_read_binary U_mpi_read_binary_proof U_mpi_lset U_pk_ecparams_H U_pk_ecparams_I U_pk_ecparams_J U_pk_ecparams_K U_pk_ecparams_L U_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chunk_split H n H1 H2 ::=
  lazymatch type of H with
  | OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells ?sg ?mx ?A ?cs =>
      let pre := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.firstn n cs) in
      let post := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.skipn n cs) in
      change (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx A (Corelib.Init.Datatypes.app pre post)) in H;
      apply (proj1 (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.CellsX.rw_cells_app sg mx A pre post)) in H;
      destruct H as [H1 H2];
      let z := eval cbv in (Stdlib.ZArith.BinInt.Z.of_nat (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.cells_size pre)) in
      change (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx (Stdlib.ZArith.BinInt.Z.add A z) post) in H2
  end.
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_pk_ecparams () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.U_FREE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.U_CALLOC"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_RSA_INFO"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_sinv.ecp_ids_lok"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.U.U_oid_ec_grp.U_OID_EC_GRP_TBL"; "U_PK_USE_ECPARAMS"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"].


Definition U_PK_USE_ECPARAMS : Z := 0x2964c.

Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Theorem U_pk_use_ecparams_spec : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams ()) "PL,$0.PHI,(1.$2.R1.)P,(3.$4.(5.R2.)$6.)P,(3.$4.(7.R3.)$8.)P,(9.=(:.R4.))P,Pa,$4.P,(;.R6.R1.)(<.R7.R2.)P,(=.(9.(>.R6.)(?.R6.))(9.(10.R6.)(11.R6.)))P,Ph,(12.$2.R7.R6.)PLB,(13.$14.)Pm,P,(15.&40.)(16.(15.&8.))Pmo,$17.P,(18.$2.R;.R:.R4.R3.R2.R1.)(19.$4.(1:.(1;.$4.$4.)$4.(1<.$4.$4.)R4.))P,(1=.R8.$1>.+4.)P,(1?.R9.$20.$21.)(22.$2.R:.R9.$23.$24.$25.$26.$20.$21.$27.$28.$29.)")
(* [comment removed for export] *).
Proof.
  intros L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 IDL.
  unfold pk_use_ecparams_stmt, U_PK_USE_ECPARAMS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 mo0 h0 LB
         PKA info C lo PAR LEN P BUF tg pd bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ.
  lazy zeta.
  intros HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD HPAR0 ALR NZR DSR RD RC HBS0 INB HBD LEN0 B63 BUF0 IDS0 SOK0 CA CAT CA_EC0
         ST0 SLO ACL HTOP SPA DHI TP MI0 RA A0 A1.
  subst a0 a1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0. pose proof (proj2 SPR0) as SPR. clear SPR0.
  dpose (U_pk_ecparams_B.ep_basics L HI m0 mo0 h0 LB C BUF bs HH0 INC INB) as (ACP & C0 & C16 & CAC & CIM & BAC & BIM).
  pose proof DIMG as [DI1 DI2]. dpose IDL as (IL1 & IL2 & IL3 & IL4).
  pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK0.
  assert (CX0 : ctx_now L HI mo0 h0 LB h0 LB [] m0 mo0).
  { split; [exact HH0|]. split; [reflexivity|]. split; [apply mo_frame_refl|]. split; [exact MI0|]. split; [exact SOK0|]. split; [apply lb_ext_refl| exact IDS0]. }
  pose proof (heap_presx_refl usegs L LB (bv_unsigned sp) [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)] m0) as PX0.
  pose proof HPAR0 as HPAR. unfold buf_cells in HPAR.
  (* [comment removed for export] *)
  pose proof (conj HH0 (conj MI0 (conj HPKA0 (conj HBS0 (conj HPAR0 I))))) as BOX. clear HPKA0 HBS0 HPAR0.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl usegs m0) as WM.
  (* [comment removed for export] *)
  carve_frame 512%nat ST0.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. if_cases KA; zify_cond KA; [exfalso; change 7 with (Z.ones 3) in KA; rewrite Z.land_ones in KA by lia; clear -KA ALR; lia|].
  zstep. zstep. zstep.
  lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end. match goal with W : wmono usegs m0 m1 |- _ => rename W into WM1 end.
  match goal with S : stk usegs m1 lo _ |- _ => rename S into ST1 end.
  try clear HH0. try clear SOK0. ddestruct BOX as (HH0 & MI0 & HPKA0 & HBS0 & HPAR0 & _).
  destruct (U_pk_ecparams_D.ctx_munch L HI ra sp m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP DHI IDL _ _ _ _ _ _ _ CX0 PX0 MU WM1 MI1 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX1 PX1].
  lazymatch goal with FR : rw_cells usegs m1 (bv_unsigned sp + -512) (CB 408 ?j :: ?rest) |- _ =>
    set (JJ := j) in FR; clearbody JJ; rename FR into FRA end.
  zstep. if_cases KT; zify_cond KT.
  - (* [comment removed for export] *)
    lazymatch type of FRA with rw_cells ?sg ?mx ?A (CB 408 ?j :: ?rest) =>
      change (rw_cells sg mx A (CB 408 j :: rest)) with (rw_cells sg mx A ([] ++ CB 408 j :: rest)) in FRA;
      apply (rw_cells_split_CB sg mx A [] 408 j rest [8; 192; 4; 4; 8; 192]%nat) in FRA; [| reflexivity]; cbn [mk_CB_cells app] in FRA
    end.
    lazymatch type of FRA with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => cb4_to_c4 FRA [c0; c1; c2] end.
    lazymatch type of FRA with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 FRA [c0; c1; c2; c3] end.
    chunk_split FRA 1%nat FR0 FRA1. chunk_split FRA1 1%nat FRG FRA2. chunk_split FRA2 2%nat FRM FRA3. chunk_split FRA3 1%nat FRL FRA4. chunk_split FRA4 1%nat FRR FRS.
    replace (bv_unsigned sp + -512 + 8) with (bv_unsigned sp + -504) in FRG by (clear; lia).
    replace (bv_unsigned sp + -512 + 8 + 192) with (bv_unsigned sp + -312) in FRM by (clear; lia).
    replace (bv_unsigned sp + -512 + 8 + 192 + 8) with (bv_unsigned sp + -304) in FRL by (clear; lia).
    replace (bv_unsigned sp + -512 + 8 + 192 + 8 + 8) with (bv_unsigned sp + -296) in FRR by (clear; lia).
    replace (bv_unsigned sp + -512 + 8 + 192 + 8 + 8 + 192) with (bv_unsigned sp + -104) in FRS by (clear; lia).
    destruct HBD as [(P0 & L0 & _)|[BP PL]].
    + eapply (U_pk_ecparams_L.spec0_null_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF tg pd bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM);
        [exact P0| exact L0| exact CX1| exact PX1| exact HPAR| exact FR0| exact FRG| exact FRM| exact FRL| exact FRR| exact FRS| exact ST1].
    + eapply (U_pk_ecparams_K.spec0_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF tg pd bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP LEN0 PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM);
        [exact CX1| exact PX1| exact HPAR| exact FR0| exact FRG| exact FRM| exact FRL| exact FRR| exact FRS| exact ST1].
  - (* [comment removed for export] *)
    destruct HBD as [(_ & _ & TG0)|[BP PL]].
    { exfalso. subst tg. clear -KT. rewrite ?(sx32_small 0) in KT by lia. rewrite ?unsigned_lit in KT by lia. match type of KT with ?t => idtac "KT:" t end. lia. }
    lazymatch type of FRA with rw_cells ?sg ?mx ?A (CB 408 ?j :: ?rest) =>
      change (rw_cells sg mx A (CB 408 j :: rest)) with (rw_cells sg mx A ([] ++ CB 408 j :: rest)) in FRA;
      apply (rw_cells_split_CB sg mx A [] 408 j rest [208; 4; 4; 192]%nat) in FRA; [| reflexivity]; cbn [mk_CB_cells app] in FRA
    end.
    lazymatch type of FRA with rw_cells _ _ _ (?c0 :: _) => cb4_to_c4 FRA [c0] end.
    chunk_split FRA 1%nat FRa FRA1. chunk_split FRA1 1%nat FRE FRA2. chunk_split FRA2 1%nat FRb FRA3. chunk_split FRA3 1%nat FRc FRS.
    replace (bv_unsigned sp + -512 + 208) with (bv_unsigned sp + -304) in FRE by (clear; lia).
    replace (bv_unsigned sp + -512 + 208 + 4) with (bv_unsigned sp + -300) in FRb by (clear; lia).
    replace (bv_unsigned sp + -512 + 208 + 4 + 4) with (bv_unsigned sp + -296) in FRc by (clear; lia).
    replace (bv_unsigned sp + -512 + 208 + 4 + 4 + 192) with (bv_unsigned sp + -104) in FRS by (clear; lia).
    dpose CX1 as (HH1 & HT1 & MF1 & _ & SOK1 & EXT1 & IDS1). pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    pose proof (U_pk_ecparams_H.ctx_bytes L DIMG sp m0 LB BUF bs HBS0 INB IDL BIM m1 PX1) as HBS1.
    set (xs := firstn (Z.to_nat LEN) (skipn (Z.to_nat (P - BUF)) bs)).
    assert (LENX : Z.of_nat (length xs) = LEN) by (subst xs; apply bytes_at_sub_length; clear -BP LEN0 PL; lia).
    assert (HXS : bytes_at usegs m1 P xs) by (subst xs; eapply bytes_at_sub; [exact HBS1| | |]; clear -BP LEN0 PL; lia).
    clearbody xs.
    pose proof (U_oid_get_ec_grp_vspec L) as SOG. unfold oid_lookup1v_stmt, oid_lookup1v_post, U_OID_GET_EC_GRP in SOG.
    clear MU. pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep.
    acallx_sp (bv_unsigned sp + -512)
      (eapply SOG with (OID := PAR) (EXT := bv_unsigned sp + -304) (P := P) (LEN := LEN) (lo := lo) (xs := xs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
       first [ exact HPAR | exact HXS | exact LENX | exact FRE | exact MI1 | exact SOK1 | exact CAT | exact DHI | eassumption | reflexivity
             | clear -DSR SLO HLS ACL ACP; lia
             | clear -BP LEN0 PL BAC ACL SLO HLS; lia
             | clear -SPA SPR; lia | clear -BUF0 BP; lia
             | clear -DHI ACL SLO HLS; lia
             | f_equal; clear; lia
             | match goal with |- ?g => idtac "OGLEFT" g end ]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with M : mem_inv usegs m2 |- _ => rename M into MI2 end. match goal with W : wmono usegs m1 m2 |- _ => rename W into WM2 end.
    match goal with S : stk usegs m2 lo _ |- _ => rename S into ST2 end.
    match goal with H : rw_cells usegs m2 (bv_unsigned sp + -304) [C4 ?v] |- _ => rename H into FRE2; rename v into gv end.
    match goal with H : oid_vres ?r _ _ _ |- _ => rename H into VR; rename r into rg end.
    match goal with H : rg = 0 \/ rg = _ |- _ => rename H into RR end.
    destruct (U_pk_ecparams_D.ctx_munch L HI ra sp m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP DHI IDL _ _ _ _ _ _ _ CX1 PX1 MU WM2 MI2 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX2 PX2].
    clear MU WM2 SOG HXS LENX HBS1 CX1 PX1 MK1 HH1 HT1 MF1 SOK1 EXT1 IDS1.
    dpose CX2 as (HH2 & _ & _ & _ & _). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    match goal with H : ?x = Z_to_bv 64 rg |- _ => subst x end.
    zstep. if_cases KG; zify_cond KG.
    + (* [comment removed for export] *)
      assert (Z0 : rg = 0).
      { unfold MBEDTLS_ERR_OID_NOT_FOUND in RR. clear -KG RR. apply Z.mod_divide in KG; [| lia]. destruct KG as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
      destruct VR as [[NF _]|[_ INV]]; [exfalso; unfold MBEDTLS_ERR_OID_NOT_FOUND in NF; clear -NF Z0; lia|].
      assert (GVB : 0 <= bv_unsigned gv < 2^31) by (cbn in INV; clear -INV; lia).
      zstep. zstep.
      assert (SX : sx32 gv = Z_to_bv 64 (bv_unsigned gv)).
      { etransitivity; [| apply (sx32_small (bv_unsigned gv) GVB)]. f_equal. symmetry. apply definitions.Z_to_bv_bv_unsigned. }
      rewrite SX. clear SX.
      assert (STX : stk usegs m2 lo (bv_unsigned sp + -104)).
      { generalize FRa FRE2 FRb FRc ST2 SLO ACL ACP HLS SPR. clear. intros.
        release_frame FRa ST2 (bv_unsigned sp + -304). release_frame FRE2 ST2 (bv_unsigned sp + -300).
        release_frame FRb ST2 (bv_unsigned sp + -296). release_frame FRc ST2 (bv_unsigned sp + -104). exact ST2. }
      clear FRa FRE2 FRb FRc ST2.
      eapply (U_pk_ecparams_B.setgrp_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL)
        with (id := bv_unsigned gv); [exact CX2| exact PX2| exact GVB| exact FRS| exact STX].
    + (* [comment removed for export] *)
      zstep. zstep. zstep.
      assert (STX : stk usegs m2 lo (bv_unsigned sp + -104)).
      { generalize FRa FRE2 FRb FRc ST2 SLO ACL ACP HLS SPR. clear. intros.
        release_frame FRa ST2 (bv_unsigned sp + -304). release_frame FRE2 ST2 (bv_unsigned sp + -300).
        release_frame FRb ST2 (bv_unsigned sp + -296). release_frame FRc ST2 (bv_unsigned sp + -104). exact ST2. }
      clear FRa FRE2 FRb FRc ST2.
      eapply (U_pk_ecparams_B.exit_walk L HI HLS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ NZP DSP DPC NZR DSR RC SLO)
        with (g' := kp_grp (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ)) (NB := []);
        [exact CX2| | | reflexivity| | clear; lia| | | exact FRS| exact STX].
      * (* [comment removed for export] *) eapply U_pk_ecparams_B.kp_init_presx; [exact DIMG| exact KP0| exact PX2| exact MI0| exact MI2| exact INC|].
        cbn. generalize IL1 IL2 IL3 CIM DI1 DI2. clear. intros. repeat split; lia.
      * intros d1 d2 H1 H2 NE O1 O2. exfalso. revert H1 O1. unfold grp_mpds, kp_init, kp_grp, grp_init.
        cbn [g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]. unfold mpd_init.
        intros H1 O1; decompose [or] H1; subst; cbn in O1; try discriminate; contradiction.
      * right. split; [clear; lia| split; reflexivity].
      * eapply (U_pk_ecparams_B.ctx_pka L HI sp m0 mo0 h0 LB PKA info C lo BUF bs HH0 HPKA0 DSP CWP PKD INC INB IDL). exact PX2.
      * eapply heap_presx_weak; [exact PX2| intros b Hb; exact Hb| clear; lia| intros a Ha; exact (proj2 Ha)].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
