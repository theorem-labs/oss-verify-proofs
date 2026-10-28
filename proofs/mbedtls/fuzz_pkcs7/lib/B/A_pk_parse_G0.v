(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiClient RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepPk RepCrt PkTmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_ecp_group_load P_pk_parse_A P_pk_parse_C.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_read_binary_stmt A_ecp_stmtA A_ecp_grp_facts
     A_pk_setup A_rsa_parse_pubkey A_pk_ecc_set_group A_pk_ecc_set_pubkey A_pk_ecparams_stmt A_pk_free A_asn1_get_alg_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_pk_parse_G0 () : Init.string Init.list := ["Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.B.A_pk_setup.PK_SETUP_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.RSA_PP_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.pk_set_pubkey_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_grp_facts.ECP_MAX_N"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.PHIpk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.RSA_PP_FR"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.pk_ecparams_FR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.pk_set_group_FR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.pk_set_pubkey_FR"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.FFRpk"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.STKpk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_malloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.C24_RSA_PP"; "PKP_C24"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.C24_PK_USE_ECPARAMS"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.C24_PK_SET_PUBKEY"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.C24_ECP_GROUP_LOAD"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_kp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Logic.not"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.RepPk.pk_rep_c"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_limb_blocks"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Stdlib.ZArith.BinInt.Z.lt"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PKP_PHI (n : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "(0.(0.(0.(0.(0.$1.(2.O1.))(3.O1.))$4.)(5.$6.O1.))(7.=))")
(* [comment removed for export] *).
Definition PKP_FFR (n d : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "(0.(0.(0.(0.(0.(8.=)$9.)(:.=(;.(0.O1.+1.))))$<.)(:.=(=.$6.(0.O1.+1.))))(>.=+1<.))")
(* [comment removed for export] *).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PKP_CNT : Z := 11.
Definition PKP_C24 : Z := C24_RSA_PP + C24_PK_USE_ECPARAMS + C24_PK_SET_PUBKEY.
Definition PKP_STK (R : art_layout) : Z := 176 + 4224 + arl_need_ecp R + arl_need_bcmp R + arl_need_amem R
(* [comment removed for export] *).

Lemma PKP_C24_facts : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "(16.(17.$18.$19.)(16.(17.$1:.$19.)(16.(17.$1;.$19.)(17.$1<.$19.))))")
(* [comment removed for export] *).
Proof. vm_compute. repeat split; discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cnt24_all_out : forall (l : list blk), (forall b, In b l -> win24 (snd b) = false) -> cnt24 l = 0.
Proof.
  induction l as [|b l IH]; intros H; [reflexivity|]. rewrite cnt24_cons. rewrite (H b ltac:(left; reflexivity)).
  rewrite IH; [reflexivity|]. intros b' Hb. apply H. right. exact Hb.
Qed.
Lemma cnt24_zero_out : forall (l : list blk) b, cnt24 l = 0 -> In b l -> win24 (snd b) = false.
Proof.
  induction l as [|c l IH]; intros b H Hb; [destruct Hb|]. rewrite cnt24_cons in H. pose proof (cnt24_nonneg l) as N0.
  destruct Hb as [<-|Hb].
  - destruct (win24 (snd c)); [exfalso; lia| reflexivity].
  - apply IH; [| exact Hb]. destruct (win24 (snd c)); lia.
Qed.
Lemma gl_cnt24A : forall ca ONE id A r g NB, gl_result ca ONE id A r g NB -> cnt24 NB = 0.
Proof. intros ca ONE id A r g NB RES. unfold gl_result in RES. decompose [and or ex] RES; subst; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mpd_blk_len : forall d, (length (mpd_blk d) <= 1)%nat.
Proof. intros d. unfold mpd_blk. destruct (md_own d); cbn; lia. Qed.
Lemma grp_blocks_len : forall g, (length (grp_blocks g) <= 7)%nat.
Proof.
  intros g. unfold grp_blocks, grp_mpds, pt_mpds. cbn [app flat_map]. rewrite !app_length. cbn [length].
  pose proof (mpd_blk_len (g_P g)). pose proof (mpd_blk_len (g_A g)). pose proof (mpd_blk_len (g_B g)).
  pose proof (mpd_blk_len (pt_X (g_G g))). pose proof (mpd_blk_len (pt_Y (g_G g))). pose proof (mpd_blk_len (pt_Z (g_G g))). pose proof (mpd_blk_len (g_N g)). lia.
Qed.
Lemma pt_blocks_len : forall p, (length (pt_blocks p) <= 3)%nat.
Proof.
  intros p. unfold pt_blocks, pt_mpds. cbn [app flat_map]. rewrite !app_length. cbn [length].
  pose proof (mpd_blk_len (pt_X p)). pose proof (mpd_blk_len (pt_Y p)). pose proof (mpd_blk_len (pt_Z p)). lia.
Qed.
Lemma rsa_limb_blocks_len : forall r, (length (rsa_limb_blocks r) <= 2)%nat.
Proof. intros r. unfold rsa_limb_blocks. rewrite app_length. pose proof (mpd_blk_len (r_N r)). pose proof (mpd_blk_len (r_E r)). lia. Qed.
Lemma nodup_incl_len : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "Pl,(1=.$1>.)Pl',(1=.$1>.)P,(1?.$1>.R2.)P,Pb,$1>.P,(20.$1>.R1.R4.)(20.$1>.R2.R4.)(21.(22.$1>.R4.)(22.$1>.R3.))")
(* [comment removed for export] *).
Proof. intros l l' ND INC. apply NoDup_incl_length; [exact ND| exact INC]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma ecp_keypair_at_LB_mono : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "PMT,(1=.$23.)Pm,P,(24.&40.)(25.(24.&8.))PLB,(1=.$1>.)PLB',(1=.$1>.)PA,$26.Pk,$27.P,(28.Vsegs,R6.R5.R4.R2.R1.)P,Pb,$1>.P,(20.$1>.R1.R6.)(20.$1>.R2.R6.)(28.Vsegs,R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros MT m LB LB' A k dd_H; ddestruct dd_H as (HG & ED & MD & FD & (EX & EY & EZ & MX & MY & MZ) & FQ); intros SUB).
  split; [eapply ecp_group_at_LB_mono; [exact HG| exact SUB]|]. split; [exact ED|].
  split; [eapply mpdr_at_LB_mono; [exact MD| exact SUB]|]. split; [exact FD|]. split; [| exact FQ].
  split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
  split; [eapply mpdr_at_LB_mono; [exact MX| exact SUB]|]. split; [eapply mpdr_at_LB_mono; [exact MY| exact SUB]| eapply mpdr_at_LB_mono; [exact MZ| exact SUB]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ecp_keypair_at_agree : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "PMT,(1=.$23.)Pm,P,(24.&40.)(25.(24.&8.))Pm',P,(24.&40.)(25.(24.&8.))PLB,(1=.$1>.)PLB',(1=.$1>.)Powned,(1=.$1>.)PC,$26.Pk,$27.P,(28.Vsegs,R8.R7.R5.R2.R1.)P,(29.Vsegs,R8.)P,(29.Vsegs,R8.)P,Pb,$1>.P,(20.$1>.R1.R7.)(20.$1>.R2.R9.)P,Pa,$26.P,(2:.R8.R1.)(2;.(25.(24.&8.))A1.R<.(2<.R2.)A1.R=.(2<.R2.))P,(20.(2=.$26.$26.)(2>.$26.$26.R7.+100.)R8.)P,Pd,$2?.P,(20.$2?.R1.(30.R8.))P,(2;.$31.(32.R2.)$33.)(20.(2=.$26.$26.)(2>.$26.$26.(34.R3.)(35.+4.(36.R3.)))R<.)(28.Vsegs,R?.R=.R;.R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros MT m m' LB LB' owned C k KP MI MI' HS HA CIN HB.
  assert (AG : agree_on m m' C 256) by (eapply agree_of_blocks; [exact HA| exact CIN]).
  assert (MF : forall d, In d (kp_mpds k) -> mpdr_at segs m' LB' d).
  { intros d Hd. pose proof (kp_mpds_mpdr segs MT _ _ _ _ _ KP Hd) as MD.
    ddestruct KP as (HG & ED & _ & _ & (EX & EY & EZ & _) & _).
    ddestruct HG as (_ & _ & _ & EP & EA & EB & EN & _ & _ & _ & (GX & GY & GZ & _) & _).
    assert (HR : C <= md_addr d /\ md_addr d + 16 <= C + 256).
    { unfold kp_mpds, grp_mpds in Hd. cbn [app In pt_mpds] in Hd.
      destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; lia. }
    eapply mpdr_at_frame_in with (owned := owned) (C := C) (sz := 256);
      [exact MD| exact MI| exact MI'| exact HS| exact HA| exact CIN| lia| lia|].
    intros HO. exact (HB d Hd HO). }
  ddestruct KP as (HG & ED & MD & FD & (EX & EY & EZ & MX & MY & MZ) & FQ).
  split; [| split; [exact ED| split; [apply MF; unfold kp_mpds; apply in_or_app; right; left; reflexivity| split; [exact FD| split; [| exact FQ]]]]].
  + ddestruct HG as (HDc & AL & POS & EP & EA & EB & EN & MP & MA & MB & (GX & GY & GZ & PX & PY & PZ) & MN & HTc & REST).
    unfold ecp_group_at. repeat match goal with |- _ /\ _ => split end; try assumption;
      try (apply MF; unfold kp_mpds, grp_mpds; cbn [app In pt_mpds]; tauto).
    all: lazymatch goal with
         | |- rw_cells _ _ _ (grp_head_cells _) =>
             eapply rw_cells_agree; [exact HDc|]; cbn [cells_size csize Nat.add grp_head_cells]; eapply agree_on_sub; [exact AG| lia| cbn; lia]
         | |- rw_cells _ _ _ (grp_tail_cells _) =>
             eapply rw_cells_agree; [exact HTc|]; cbn [cells_size csize Nat.add grp_tail_cells]; eapply agree_on_sub; [exact AG| lia| cbn; lia]
         | |- ecp_point_at _ _ _ _ _ =>
             split; [exact GX|]; split; [exact GY|]; split; [exact GZ|];
             split; [| split]; apply MF; unfold kp_mpds, grp_mpds; cbn [app In pt_mpds]; tauto
         | |- _ => clear -REST; tauto
         end.
  + split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
    split; [| split]; apply MF; unfold kp_mpds; cbn [app In pt_mpds]; apply in_or_app; right; right; cbn; tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ec_rep_introA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "PMT,(1=.$23.)PRSAI,$26.PECIS,(1=.$26.)Pm,P,(24.&40.)(25.(24.&8.))PLBx,(1=.(2=.$26.$26.))PPKA,$26.PC,$26.Pk,$27.Pinfo,$26.Powned,(1=.(2=.$26.$26.))P,(20.$26.R2.R8.)P,(37.(2;.$26.R3.=))P,(29.Vsegs,R9.)P,(1?.$26.(38.(2=.$26.$26.)$26.(39.$26.$26.)R9.))P,(28.Vsegs,R>.R;.R:.R8.R7.)P,(20.(2=.$26.$26.)(2>.$26.$26.R9.+100.)R;.)P,Pd1,$2?.Pd2,$2?.P,(20.$2?.R2.(30.R;.))P,(20.$2?.R2.(30.R<.))P,(37.(2;.$26.(3:.R4.)(3:.R3.)))P,(2;.$31.(32.R5.)$33.)P,(2;.$31.(32.R5.)$33.)(37.(2;.(2=.$26.$26.)(2>.$26.$26.(34.R7.)(35.+4.(36.R7.)))(2>.$26.$26.(34.R6.)(35.+4.(36.R6.)))))P,Pd,$2?.P,(20.$2?.R1.(30.R;.))P,(2;.$31.(32.R2.)$33.)(37.(2;.(2=.$26.$26.)(2>.$26.$26.(34.R3.)(35.+4.(36.R3.)))(2>.$26.$26.R>.+100.)))P,(2;.$26.(3;.R<.+10.)=)P,(17.(0.R=.+100.)(3<.+2.+40.))P,Pb,(2=.$26.$26.)(3=.(20.(2=.$26.$26.)R1.R<.)(20.(2=.$26.$26.)R1.(3>.(2=.$26.$26.)(2>.$26.$26.R?.+100.)(3?.R>.))))(40.Vsegs,R14.R13.R15.R12.R11.R10.R=.R?.R<.)")
(* [comment removed for export] *).
Proof.
  intros MT RSAI ECIS m LBx PKA C k info owned EI NI MI ND KP CIN DIS NC AL C64 OWN.
  assert (BLK : forall d, In d (kp_mpds k) -> md_own d = LHeap -> In (md_p d, 4 * md_n d) LBx).
  { intros d Hd O. dpose (kp_mpds_mpdr segs MT m LBx C k d KP Hd) as (_ & _ & _ & _ & _ & HO). rewrite O in HO. exact (proj1 (proj2 HO)). }
  right; right. split; [exact EI|]. split; [exact NI|]. split; [exact MI|]. exists k.
  split; [exact KP|]. split; [exact CIN|]. split.
  { intros d1 d2 H1 H2 NE O1 O2 E. apply (DIS d1 d2 H1 H2 NE O1 O2). rewrite E. f_equal.
    exact (nodup_fst_same LBx (md_p d2) (4 * md_n d1) (4 * md_n d2) ND ltac:(rewrite <- E; exact (BLK d1 H1 O1)) (BLK d2 H2 O2)). }
  split. { intros d Hd O E. apply (NC d Hd O). rewrite E. f_equal. exact (nodup_fst_same LBx C (4 * md_n d) 256 ND ltac:(rewrite <- E; exact (BLK d Hd O)) CIN). }
  split; [exact AL|]. split; [exact C64| exact OWN].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kpi_heap_grpA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "PC,$26.Pg,$41.Ppd,(24.&40.)PqX,(24.&40.)PqY,(24.&40.)PqZ,(24.&40.)Pd,$2?.P,(20.$2?.R1.(30.(42.R6.(43.(0.R7.+<0.)R5.)(44.(0.R7.+=0.)R4.R3.R2.))))P,(2;.$31.(32.R2.)$33.)(20.$2?.R3.(45.R8.))")
(* [comment removed for export] *).
Proof.
  intros C g pd qX qY qZ d Hd O. unfold kp_mpds in Hd. cbn [kp_grp kp_d kp_Q] in Hd. apply in_app_or in Hd. destruct Hd as [Hd|Hd]; [exact Hd|].
  exfalso. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; cbn in O; discriminate.
Qed.
#[using="Type"] Lemma kpi_blocksA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "PC,$26.Pg,$41.Ppd,(24.&40.)PqX,(24.&40.)PqY,(24.&40.)PqZ,(24.&40.)(2;.(1=.$1>.)(3?.(42.R5.(43.(0.R6.+<0.)R4.)(44.(0.R6.+=0.)R3.R2.R1.)))(46.R5.))")
(* [comment removed for export] *).
Proof. intros. unfold kp_blocks. cbn [kp_grp kp_d kp_Q]. unfold pt_blocks. cbn. rewrite app_nil_r. reflexivity. Qed.
#[using="Type"] Lemma grp_blk_inA : forall g d, In d (grp_mpds g) -> md_own d = LHeap -> In (md_p d, 4 * md_n d) (grp_blocks g).
Proof. intros g d Hd O. unfold grp_blocks. apply in_flat_map. exists d. split; [exact Hd|]. apply MpiClient.mpd_blk_in. exact O. Qed.
#[using="Type"] Lemma pt_blk_inA : forall p d, In d (pt_mpds p) -> md_own d = LHeap -> In (md_p d, 4 * md_n d) (pt_blocks p).
Proof. intros p d Hd O. unfold pt_blocks. apply in_flat_map. exists d. split; [exact Hd|]. apply MpiClient.mpd_blk_in. exact O. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rsa_rep_introA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "PMT,(1=.$23.)PRSAI,$26.PECIS,(1=.$26.)Pm,P,(24.&40.)(25.(24.&8.))PLBx,(1=.$1>.)PPKA,$26.PC,$26.Pr,$47.Powned,(1=.(2=.$26.$26.))P,(37.(2;.$26.R8.=))P,(29.Vsegs,R7.)P,(48.Vsegs,R8.R7.R5.R4.)P,Pb,(2=.$26.$26.)(3=.(20.(2=.$26.$26.)R1.R5.)(20.(2=.$26.$26.)R1.(3>.(2=.$26.$26.)(2>.$26.$26.R7.+>8.)(49.R6.))))(40.Vsegs,R<.R;.R=.R:.R9.R8.R<.R7.R5.)")
(* [comment removed for export] *).
Proof.
  intros MT RSAI ECIS m LBx PKA C r owned NZ MI RA OWN. right; left. split; [reflexivity|]. split; [exact NZ|]. split; [exact MI|].
  exists r. split; [exact RA| exact OWN].
Qed.
End WithSegs.

(* [comment removed for export] *)
Lemma fresh_not_clientA : ltac2:(CDefT.buildp (gd_tbl_A_pk_parse_G0 ()) "PR,$4:.PLB,(1=.$1>.)PLF,(1=.$1>.)PN,$26.Pk,$26.PSP,$26.Px,$26.P,(4;.R7.R6.R5.R4.R3.)P,(17.(4<.(4=.R8.))R3.)P,(4>.(4=.R9.)(4?.$1>.R8.(50.R7.))R4.R3.)(37.(16.(17.R7.R4.)(51.R4.(0.R7.R6.))))")
(* [comment removed for export] *).
Proof.
  (intros R LB LF N k SP x dd_H; ddestruct dd_H as (F0 & F1 & F2 & F3); intros HSP HC Hx). destruct HC as [K|[[K _]|([B j] & Hb & Hr)]].
  - lia.
  - lia.
  - cbn [fst snd] in Hr. pose proof (F3 B j Hb). lia.
Qed.
