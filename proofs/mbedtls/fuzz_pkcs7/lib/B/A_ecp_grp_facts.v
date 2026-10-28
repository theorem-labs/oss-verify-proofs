(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad EcpPkGlue.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_ecp_group_load.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_free_seq A_ecp_defs A_ecp_statics
     A_pk_ecc_set_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_grp_facts () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_group_load.gl_result"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_h"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_G"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.grp_factsA"; "ECP_MAX_N"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"].


(* [comment removed for export] *)
Definition ECP_MAX_N : Z := 17.

(* [comment removed for export] *)
Lemma grp_factsA_of_gl_result : ltac2:(CDefT.buildp (gd_tbl_A_ecp_grp_facts ()) "Pid,$0.PC,$0.Pg,$1.PNB,(2.$3.)P,(4.$5.$6.R4.R3.=R2.R1.)P,P,(7.$0.(8.R3.)+2.)(9.(7.$0.(:.(;.(<.R4.)))=))(=.R4.$>.)")
(* [comment removed for export] *).
Proof.
  intros id C g NB GL NZ. unfold grp_factsA, ECP_MAX_N.
  destruct GL as [(_ & SW & IDB & _ & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & ->)
              |[(_ & ID913 & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & PA & PX & PZ & wA & wX & wZ & -> & _)
              |[(R0 & _)|(R0 & _)]]].
  - pose proof (A_grp_sw_imgA id C idpad pP pA pB pX pY pZ pN hpad IDB SW) as IMGG.
    pose proof (cP_val_pos id IDB) as VP.
    assert (Cid : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by (clear - IDB; lia).
    split; [reflexivity|]. split; [unfold grp_sw; cbn [g_A]; destruct (has_A id); reflexivity|]. split; [reflexivity|].
    split; [unfold mpd_val, grp_sw; cbn [g_P md_sg md_limbs smpd]; clear - VP; lia|].
    split. { clear - Cid. destruct Cid as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]; vm_compute; intros CC; discriminate CC. }
    split; [exact IMGG|].
    split. { unfold grp_nle. clear - Cid SW. destruct Cid as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]; try discriminate SW;
               vm_compute; repeat split; intros CC; discriminate CC. }
    split; [clear; lia|].
    left. split; [reflexivity|].
    clear - Cid SW. destruct Cid as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]; try discriminate SW;
      vm_compute; split; intros CC; discriminate CC.
  - pose proof (A_grp_mx_imgA id C idpad pP pA pB pX pY pZ pN hpad PA PX PZ wA wX wZ ID913) as IMGG.
    pose proof (cP_val_pos id ltac:(clear - ID913; lia)) as VP.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold mpd_val, grp_mx, grp_mxi; cbn [g_P md_sg md_limbs smpd]; clear - VP; lia|].
    split. { clear - ID913. destruct ID913 as [-> | ->]; vm_compute; intros CC; discriminate CC. }
    split; [exact IMGG|].
    split. { unfold grp_nle. clear - ID913. destruct ID913 as [-> | ->]; vm_compute; repeat split; intros CC; discriminate CC. }
    split; [clear; lia|].
    right. split; [reflexivity|]. split; [apply NZ; reflexivity| reflexivity].
  - exfalso. unfold MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE in R0. clear - R0. lia.
  - exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in R0. clear - R0. lia.
Qed.

(* [comment removed for export] *)
Lemma grp_GX_nz : ltac2:(CDefT.buildp (gd_tbl_A_ecp_grp_facts ()) "PR,$?.PHIA,(10.$11.R1.)Ph,(12.$11.R2.R1.)PLB,(2.$3.)PLF,(2.$3.)Pm,P,(13.&40.)(14.(13.&8.))PMT,(2.$15.)PC,$0.Pg,$1.P,(16.$11.R9.R8.R7.R6.R5.R4.)P,(17.$11.R4.R5.R7.R3.R2.)P,(7.$18.(19.(;.(<.R3.)))$1:.)(9.(7.$0.(:.(;.(<.R4.)))=))")
(* [comment removed for export] *).
Proof.
  intros R HIA h LB LF m MT C g HH G O.
  destruct (hm_apart asegs R HIA h LB LF m HH) as [HBR _]. change (blkfacts (arl_L R) (LB ++ LF)) in HBR.
  ddestruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & MX & _) & _).
  destruct (mpdr_blk_factsA asegs (arl_L R) m LB (LB ++ LF) _ MX O HBR ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as (_ & _ & P0 & _).
  clear - P0. lia.
Qed.

(* [comment removed for export] *)
Lemma grp_factsA_of_gl_result_at : ltac2:(CDefT.buildp (gd_tbl_A_ecp_grp_facts ()) "PR,$?.PHIA,(10.$11.R1.)Ph,(12.$11.R2.R1.)PLB,(2.$3.)PLF,(2.$3.)Pm,P,(13.&40.)(14.(13.&8.))PMT,(2.$15.)Pid,$0.PC,$0.Pg,$1.PNB,(2.$3.)P,(16.$11.R;.R:.R9.R8.R7.R6.)P,(17.$11.R6.R7.R9.R4.R3.)P,(4.$5.$6.R6.R5.=R4.R3.)(=.R5.$>.)")
(* [comment removed for export] *).
Proof.
  intros R HIA h LB LF m MT id C g NB HH G GL. eapply grp_factsA_of_gl_result; [exact GL|].
  intros H2. eapply grp_GX_nz; [exact HH| exact G|].
  destruct GL as [(_ & _ & _ & _ & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & ->)
              |[(_ & _ & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & PA & PX & PZ & wA & wX & wZ & -> & _)
              |[(R0 & _)|(R0 & _)]]]; [cbn in H2; discriminate H2| reflexivity| |].
  - exfalso. unfold MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE in R0. clear - R0. lia.
  - exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in R0. clear - R0. lia.
Qed.
