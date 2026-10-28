(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6FrmInv_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import FpBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6FpSites_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import CutVF CutVFX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecScanPure_u5 DecOkDefs_u5 DecOkSem_u5 DecKinds5_u5 DecfloatLems5_u5 DecfloatPre_u5 DecfloatAt_u5 Pm6Leaf_scalbnl_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import DecAssume.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_decfloat5_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK. Import DFO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFT.
Import DFA.
(* [comment removed for export] *)
Lemma tags_go_of : forall CPS TAGS NF, CC.tags_chk CPS TAGS NF = true -> CC.tags_chk_go CPS NF CPS TAGS = true.
Proof. intros CPS TAGS NF H. exact H. Qed.
Section Final.
Context {SCFG_P : ScfgP}.
Hypothesis FMODL : CVF.vf_contract RSEGS 0xbb134 192 IMGc.
Hypothesis SCX : PDC.scanexp_contract RSEGS PDC.src11.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem decfloat_ok : forall e2, PDC.decfloat_contract RSEGS PDC.src11 e2.
Proof.
  intros e2 fx R M model K SP F P Q CAN sv txt Hh Hl Hfp Hpre HK.
  pose proof (entry_at e2 R M SP F P Q CAN sv txt Hpre) as HAt. cbv zeta in HAt.
  set (N := Z.of_nat (length txt)) in *. set (c := entry_cp e2 N) in *. set (E0 := mkE0 Q CAN N sv (CC.cp_regs c) R) in *.
  destruct Hpre as (Rsp & Hal & Hfloor & Htop & RF & R23 & R18 & R22 & R24 & R9 & R20 & R4 & Hdef & Hwr & Hsaves & Hret & Hcan & Hguard & Hgap & Hfile & Hfs & Htext & Htap & Herrw & Himg & Hent).
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr). destruct Htap as (Ta1 & Ta2 & Ta3).
  fold N in Tn, TQ2, TQ3, Td, Ta1, Ta2, Ta3. unfold PDC.FRAME, PDC.SCR_D in *. cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi PDC.src11] in *.
  change (256 + 8416) with 8672 in *. change (905232 - 164) with ERRNO in *.
  assert (HN0 : 0 <= N) by (unfold N; lia).
  (* [comment removed for export] *)
  assert (E0_sp : bv_unsigned (ev E0 2) = SP) by exact Rsp.
  assert (E0_F : bv_unsigned (ev E0 21) = F) by exact RF.
  assert (E0_Q : bv_unsigned (ev E0 32) = Q) by (change (ev E0 32) with (Z_to_bv 64 Q); apply u64_of_Z; lia).
  change (DOS.N txt) with N in *.
  assert (E0_N : bv_unsigned (ev E0 47) = N) by (change (ev E0 47) with (Z_to_bv 64 N); apply u64_of_Z; lia).
  assert (R_SP : PDC.STK_FLOOR + 256 <= SP /\ SP + 8416 <= 2 ^ 47) by (split; assumption).
  assert (R_F : PDC.STK_FLOOR <= F /\ F + 256 <= 2 ^ 47) by (split; assumption).
  assert (R_Q : 4096 <= Q /\ Q + N < 2 ^ 47 /\ N < 2 ^ 26) by (repeat split; assumption).
  assert (R_ERR : 0 <= ERRNO /\ ERRNO + 4 <= PDC.STK_FLOOR) by (unfold ERRNO, PDC.STK_FLOOR; lia).
  assert (T_dig : exists c0 r, txt = c0 :: r /\ PD.is_dig c0 = true).
  { destruct e2.
    - destruct Hent as (_ & r0 & Et). exists 48, r0. split; [exact Et | reflexivity].
    - destruct Hent as (_ & c0 & r0 & Et & Hc0 & _). exists c0, r0. split; [exact Et|]. unfold PD.is_dig. apply andb_true_intro. split; apply Z.leb_le; lia. }
  assert (D_len : DOS.D txt = PD.dec_len txt).
  { destruct T_dig as (c0 & r0 & Et & Hd0). unfold DOS.D, DOS.txt'. rewrite Et. symmetry. apply PDS.dec_len_contD0. exact Hd0. }
  set (XIf := DOS.XI RSEGS CPS RETS DK5.DKINDS SCANEXP txt Q F).
  set (AMB := DOS.Amb RSEGS CPS RETS DK5.DKINDS SCANEXP ERRNO txt Q F E0 M model).
  assert (SUBF : forall i0 c0, nth_error CPS i0 = Some c0 -> CL.sub_F NF E0 (DOS.F0x ERRNO) c0 /\ (NF <= CC.cp_nx c0)%nat /\ cutc i0 c0 = true).
  { intros i0 c0 Hc0. pose proof (CC.cps_all_sound _ _ cuts_ok i0 c0 Hc0) as X. split; [|split; [|exact X]].
    - exact (DOS.sub_F_ok CPS RETS DK5.DKINDS SCANEXP ERRNO F SP E0 E0_sp E0_F R_SP R_F R_ERR i0 c0 X).
    - unfold cutc, DOS.cut_chk in X. do 2 (apply andb_prop in X as [X _]). apply Nat.leb_le. exact X. }
  (* [comment removed for export] *)
  assert (Hci : exists i0, nth_error CPS i0 = Some c /\ DOS.kind_of CPS RETS DK5.DKINDS SCANEXP i0 = KEnt /\ CC.cp_pc c = (if e2 then PDC.a_E2 PDC.src11 else PDC.a_E1 PDC.src11)).
  { unfold c, entry_cp. destruct e2; [destruct (N =? 1)|].
    - exists 1%nat. split; [reflexivity|]. split; vm_compute; reflexivity.
    - exists 2%nat. split; [reflexivity|]. split; vm_compute; reflexivity.
    - exists 0%nat. split; [reflexivity|]. split; vm_compute; reflexivity. }
  destruct Hci as (i0 & Hci & Hki & Hpc). rewrite <- Hpc.
  eapply (CC.cutcert_sound_tagged RSEGS CPS TAGS NF AMB K FrmInv.fp_ok
            (fun fx1 fx2 R1 pc1 M1 R2 pc2 M2 H => FrmInv.msteps_fp_ok RSEGS Pm6FrmInv.text_safe fx1 fx2 R1 _ M1 _ R2 _ M2 _ H) DecfloatLems5_u5.plans_ok tags_ok)
    with (i := i0) (c := c) (E := E0).
  - (* [comment removed for export] *)
    intros i E M1 m1 H. exact (CVX.ambx_model NF E0 M model (DOS.F0x ERRNO) XIf Hh Hl i E M1 m1 H).
  - (* [comment removed for export] *)
    intros i c1 tags k ps j s Hc1 Htags Hps Htag.
    destruct (CC.tags_chk_go_nth CPS NF CPS TAGS i c1 (tags_go_of CPS TAGS NF tags_ok) Hc1) as (tags' & Htags' & Hlv). rewrite Htags in Htags'. injection Htags' as <-.
    destruct (CC.leaves_chk_nth CPS NF c1 _ tags k ps Hlv Hps) as (t & Ht & Hg). rewrite Htag in Ht. injection Ht as <-. destruct Hg as (cj & Hcj & Hg).
    pose proof (CH2.leaves_all_nth CPS TAGS gchk gotos_ok i c1 tags k ps _ Hc1 Htags Hps Htag) as G2. unfold gchk in G2. rewrite Hcj in G2.
    destruct (SUBF i c1 Hc1) as (S1 & S2 & S3). destruct (SUBF j cj Hcj) as (_ & _ & S3j).
    apply CVX.ambx_goto; [exact S1 | exact S2 |].
    intros E R1 M1 m1 E' R' M' HAt1 [HAmb1 HX1] Hag HLF.
    exact (DOS.xi_goto RSEGS CPS RETS DK5.DKINDS SCANEXP ERRNO txt Q F SP E0 M model E0_sp E0_F E0_Q E0_N R_SP R_F R_Q R_ERR Tb Tn Tr T_dig Ta1 Ta2 Ta3 Hfs
             i c1 ps j cj s E R1 M1 m1 E' R' M' Hc1 Hcj S3 S3j Hg G2 HAt1 HAmb1 HX1 Hag HLF).
  - (* [comment removed for export] *)
    intros i c1 tags k ps id Hc1 Htags Hps Htag.
    pose proof (CC.others_all_sound _ _ _ others_ok i c1 tags k ps id Hc1 Htags Hps Htag) as X. unfold ochk, DOS.other_chk in X. rewrite Hc1 in X.
    destruct (SUBF i c1 Hc1) as (S1 & S2 & S3).
    apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|].
    + (* [comment removed for export] *)
      do 2 (apply andb_prop in X as [X ?Y]).
      intros fx' E R1 M1 m1 E' R' M' HAt1 HAmb1 HFP Hag HLF _.
      destruct (DOS.exit_facts RSEGS CPS RETS DK5.DKINDS SCANEXP ERRNO TPV txt Q F SP E0 M model E0_sp E0_F R_SP R_F R_Q R_ERR Hfs
                  i c1 ps E R1 M1 m1 E' R' M' Hc1 S3 Y Y0 HAt1 HAmb1 Hag HLF) as (-> & Hsv & Hsp' & Hgp' & Htp' & Hfr' & Hgr' & Hrp').
      assert (Hra : getr R' 1%bv = Z_to_bv 64 (sv 1%nat)).
      { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite (Hsv 1%nat 34%nat ltac:(unfold DOS.SAVE_VARS; cbn; tauto)). reflexivity. }
      (* [comment removed for export] *)
      assert (POST : forall R2 (M2 : word -> option byte), (forall x : reg, In (ridx x) CVF.CSAVED -> getr R2 x = getr R' x) ->
                (forall a : word, ~ (SP + 8416 - 112 <= bv_unsigned a < SP + 8416) -> M2 a = M' a) -> mem_grows M' M2 ->
                PDC.dec_post RSEGS PDC.src11 R M SP F Q sv txt R2 M2).
      { intros R2 M2 Hcs Hfr2 Hgr2. unfold PDC.dec_post, PDC.FRAME, PDC.SCR_D. cbn [PDC.a_TP PDC.src11]. change (905232 - 164) with ERRNO. change (905232 - 160) with (ERRNO + 4).
        split; [|split; [|split; [|split; [|split; [|split]]]]].
        - unfold PDC.rz, PDC.reg_of. rewrite (Hcs (Z_to_bv 5 (Z.of_nat 2))) by (cbn; tauto).
          replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact Hsp'.
        - intros r o Hin. destruct (Hsaves r o Hin) as [_ Rsv]. unfold PDC.rz, PDC.reg_of.
          assert (Hv : exists v, In (r, v) DOS.SAVE_VARS /\ ev E0 v = Z_to_bv 64 (sv r) /\ In r CVF.CSAVED).
          { unfold PDC.SAVES in Hin. cbn [In] in Hin.
            repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; eexists; split; [unfold DOS.SAVE_VARS; cbn [In]; tauto | split; [reflexivity | cbn; tauto]]|]). contradiction. }
          destruct Hv as (v & Hv1 & Hv2 & Hv3).
          rewrite Hcs by (unfold ridx; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; rewrite Z.mod_small by (unfold CVF.CSAVED in Hv3; cbn in Hv3; lia); rewrite Nat2Z.id; exact Hv3).
          rewrite (Hsv r v Hv1), Hv2. apply u64_of_Z. exact Rsv.
        - unfold PDC.reg_of. rewrite (Hcs (Z_to_bv 5 (Z.of_nat 3))) by (cbn; tauto). replace (Z_to_bv 5 (Z.of_nat 3)) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact Hgp'.
        - unfold PDC.reg_of. rewrite (Hcs (Z_to_bv 5 (Z.of_nat 4))) by (cbn; tauto). replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
          rewrite Htp'. symmetry. exact (rz_word R 4 _ R4).
        - intros a A1 A2 A3. rewrite Hfr2 by lia. apply Hfr'. unfold DOS.out3. lia.
        - eapply mem_grows_trans; [exact Hgr' | exact Hgr2].
        - rewrite <- D_len. unfold PDC.STK_FLOOR in *. apply (u64_at_same RSEGS M' M2 (F + 8) _ ltac:(lia) ltac:(lia)); [|exact Hrp'].
          intros x Hx. apply Hfr2. unfold PDC.apart in Hfs. lia. }
      apply orb_prop in X as [X|X]; apply Z.eqb_eq in X; rewrite X.
      * (* [comment removed for export] *)
        eapply CL.ret_cps; [exact ret_pc_ok | exact Hh | exact Hl | rewrite Hra; exact Hret |]. rewrite Hra.
        apply HK; [exact HFP|]. apply POST; [intros; reflexivity | intros; reflexivity | apply mem_grows_refl].
      * (* [comment removed for export] *)
        unfold PDC.STK_FLOOR in *.
        apply (Leaf_scalbnl_xsrc.ok fx' R' M' model K (SP + 8416) Hh Hl HFP).
        -- apply bv_eq. rewrite Hsp'. rewrite u64_of_Z by lia. reflexivity.
        -- rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
        -- unfold Leaf_scalbnl_xsrc.SCR. lia.
        -- unfold Leaf_scalbnl_xsrc.SCR. intros d Hd. apply Hgr'. replace (SP + 8416 - 112 + d) with (SP - 256 + (8560 + d)) by lia. apply Hdef. lia.
        -- unfold CVF.img_pre, CVF.img_pre_of, Leaf_scalbnl_xsrc.IMG. split; [lia|]. split; [lia|]. intros a Ha. rewrite Hfr'.
           ++ apply Himg. exact Ha.
           ++ unfold DOS.out3, ERRNO. rewrite u64_of_Z by lia. lia.
        -- rewrite Hra. exact Hret.
        -- intros fx2 R2 M2 HFP2 Hfr2 Hgr2 Hcs2. rewrite Hra. apply HK; [exact HFP2|]. apply POST; [exact Hcs2 | exact Hfr2 | exact Hgr2].
    + (* [comment removed for export] *)
      apply andb_prop in X as [Xpc Xs]. apply Z.eqb_eq in Xpc.
      exact (DOS.scx_leaf_ok RSEGS CPS RETS DK5.DKINDS SCANEXP ERRNO IMG_LO IMG_HI txt Q F SP E0 M model E0_sp E0_F E0_Q E0_N R_SP R_F R_Q R_ERR Tb Tn Tr Ta1 Ta2 Ta3 Hfs
               K PDC.src11 Hh Hl eq_refl eq_refl (conj eq_refl eq_refl) SCX Hal Hdef Hfw Td i c1 ps Hc1 S3 Xpc Xs).
    + (* [comment removed for export] *)
      apply existsb_exists in X as ([[[j i'] k'] pc] & _ & X). do 5 (apply andb_prop in X as [X ?Y]).
      apply Nat.eqb_eq in X. apply Z.eqb_eq in Y3, Y2. subst i' pc.
      destruct (nth_error CPS j) as [cj|] eqn:Hcj; [|discriminate Y].
      destruct (find (fun e : Z * (Z * list nat * option Z) => Z.eqb (fst e) id) INL) as [[pc' [[len hv] a0]]|] eqn:Hf.
      * apply find_some in Hf as [HinI Hpc']. cbn [fst] in Hpc'. apply Z.eqb_eq in Hpc'. subst pc'.
        destruct (inl_ok _ _ _ _ HinI) as [-> Hstep]. rewrite <- Y2 in Hstep.
        refine (CVX.inl_leaf_okX RSEGS CPS NF E0 M model (DOS.F0x ERRNO) K XIf Hh Hl Pm6FrmInv.text_safe i c1 ps j cj len hv Hcj Y S1 S2 _ Hstep).
        exact (DOS.xi_leaf_ok RSEGS CPS RETS DK5.DKINDS SCANEXP ERRNO txt Q F SP E0 E0_sp R_SP R_F R_ERR Hfs i j c1 Y0 S3).
      * destruct (find (fun e : Z * (Z * option (Z * Z)) => Z.eqb (fst e) id) CALLEES) as [[pc' [SCRc IMG']]|] eqn:Hg; [|discriminate Y].
        apply find_some in Hg as [HinC Hpc']. cbn [fst] in Hpc'. apply Z.eqb_eq in Hpc'. subst pc'.
        pose proof (callees_ok FMODL _ _ _ HinC) as Hct. rewrite <- Y2 in Hct. unfold PDC.STK_FLOOR in *.
        refine (CVX.call_leaf_okX RSEGS CPS NF E0 M model (DOS.F0x ERRNO) K XIf Hh Hl 256 SP _ i c1 ps j cj SCRc IMG' ltac:(unfold NF; lia) ltac:(lia) eq_refl E0_sp Hal ltac:(lia) _ Hcj Y Hct S1 S2 _).
        -- apply (L5.defined_sub M (SP - 256) 8672 (SP - 256) 256 Hdef); lia.
        -- exact (DOS.xi_call_ok RSEGS CPS RETS DK5.DKINDS SCANEXP ERRNO txt Q F SP E0 E0_sp R_SP R_F R_ERR Hfs i j c1 Y0 S3).
  - exact Hci.
  - exact HAt.
  - (* [comment removed for export] *)
    split; [split; [reflexivity | split; [apply CC.env_agree_refl | split; [reflexivity | apply mem_grows_refl]]]|].
    unfold DOS.XI. rewrite Hki. exact I.
  - exact Hfp.
Qed.
End Final.
End DFT.
