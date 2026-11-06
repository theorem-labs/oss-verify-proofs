(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape FPSteps
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutShA CutInlA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module GDK.
Definition mem := (word -> option byte).

Definition site_fld_chk (segs : list Segment) (pc : Z) : option (reg * reg * bv 12) :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (FLoad FMT_D rd rs imm, sz) => if Z.eqb sz 4 then Some (rd, rs, imm) else None
              | _ => None
              end
  | None => None
  end.
Theorem fld_step : forall segs pc rd rs imm, 0 <= pc -> pc + 4 < 2 ^ 64 -> site_fld_chk segs pc = Some (rd, rs, imm) ->
  forall (fx : FPState) R (M : mem) bs, rdn segs M (v_addi (getr R rs) (bv_signed imm)) 8%nat = Some bs ->
  exists fx2, msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx2 R (Z_to_bv 64 (pc + 4)) M (seg_rom segs)).
Proof.
  intros segs pc rd rs imm Hpc Hpc4 H fx R M bs Hr. unfold site_fld_chk in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|discriminate].
  destruct i; try discriminate. destruct fmt; try discriminate.
  lazymatch type of H with (if ?bb then _ else _) = _ => destruct bb eqn:Hb; [|discriminate] end.
  apply Z.eqb_eq in Hb. subst sz. injection H as <- <- <-.
  pose proof (fp_step_fld fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w rd0 rs1 imm0 _ bs Hf He Hd eq_refl Hr) as Hs.
  exists (mkFP (bvmap_set rd0 (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx)).
  rewrite <- (CSL.pc4 pc 4) by lia. eapply mst_step; [reflexivity | exact Hs | apply mst_refl].
Qed.

Lemma rdn_def : forall segs (M : mem) (n : nat) (a : Z), (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None) ->
  exists bs, rdn segs M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros segs M. induction n as [|n IH]; intros a H; [exists []; reflexivity|].
  destruct (IH (a + 1)) as (bs & Hr). { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply H. lia. }
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 a)) as [b|] eqn:Hb; [|contradiction].
  exists (b :: bs). cbn [rdn]. rewrite Hb. rewrite CH.bv_succ_Z, Hr. reflexivity.
Qed.

Section Leaf.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).

Theorem inlF_leaf : forall i c ps j cj len rd,
  nth_error CPS j = Some cj ->
  CIA.inl1_chk NF c ps cj len rd = true ->
  CIA.same_chk NF d c (nth i BLS []) (nth j BLS []) (nth i FFS []) (nth j FFS []) = true ->
  0 <= SR.ps_pc ps -> SR.ps_pc ps + len < 2 ^ 64 -> 0 <= len ->
  (forall fx fx2 R R2 (M M2 : mem) pc pc2, msteps (hl_segs L) (@mkst fx R pc M (seg_rom (hl_segs L))) (@mkst fx2 R2 pc2 M2 (seg_rom (hl_segs L))) -> FPI fx -> FPI fx2) ->
  (forall E E' R R' A M model M1 model1,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> forall fx,
     exists fx2 R2, msteps (hl_segs L) (@mkst fx R' (Z_to_bv 64 (SR.ps_pc ps)) (mrestrict (ahid A model1) M1) (seg_rom (hl_segs L)))
                                    (@mkst fx2 R2 (Z_to_bv 64 (SR.ps_pc ps + len)) (mrestrict (ahid A model1) M1) (seg_rom (hl_segs L)))
                  /\ (forall r : reg, r <> Z_to_bv 5 (Z.of_nat rd) -> getr R2 r = getr R' r)) ->
  (forall E E' R R' A M model M1 model1 E2,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> env_agree (CC.cp_nx c) E' E2 -> XI j E2 A M1 model1) ->
  (forall E E2 cr, Cred i E cr -> env_agree NF E E2 -> Cred j E2 cr) ->
  CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj len rd Hcj Hchk Hsame Hpc0 Hpc1 Hlen FPIS Hstep USER CRED fx' E R A M model E' R' M1 model1 HAt [HA HXI] HFP Hag HLF HIH.
  unfold CIA.inl1_chk in Hchk.
  apply andb_prop in Hchk as [Hchk Xnf]. apply andb_prop in Hchk as [Hchk Xrd32]. apply andb_prop in Hchk as [Hchk Xrd0]. apply andb_prop in Hchk as [Hchk Xmv].
  apply andb_prop in Hchk as [Hchk Xkv]. apply andb_prop in Hchk as [Hchk Xsv]. apply andb_prop in Hchk as [Hchk Xhas]. apply andb_prop in Hchk as [Hchk Xmeas].
  apply andb_prop in Hchk as [Hchk Xnx]. apply andb_prop in Hchk as [Hchk Xkn]. apply andb_prop in Hchk as [Hchk Xregs]. apply andb_prop in Hchk as [Xall Xpc].
  apply Nat.leb_le in Xnf. apply Nat.ltb_lt in Xrd32. apply Nat.ltb_lt in Xrd0. apply Z.eqb_eq in Xpc. apply CH2.regs_eqb_eq in Xregs. rewrite forallb_forall in Xkn.
  apply Nat.eqb_eq in Xnx. apply expr_eqb_eq in Xmeas.
  unfold CIA.same_chk in Hsame. apply andb_prop in Hsame as [Hsame Hfe]. apply andb_prop in Hsame as [Hfoot Hbe]. apply CH2.blocks_eqb_eq in Hbe. apply CHA.frames_eqb_eq in Hfe.
  set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  set (regs := CA.ps_reglist ps) in *.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
  pose proof (CIA.leaf_regs_ok L NF sp0 NF32 c ps E' R' _ _ Xall HLFv) as HR. fold regs in HR.
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1 Hfoot HAt HA Hag HLF) as HA1.
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M1 model1 HA1) as (Hh1 & HMI1 & HAwf & Hoff1).
  set (H1 := ahid A model1).
  destruct (Hstep E E' R R' A M model M1 model1 HAt HA HXI Hag HLF fx') as (fx2 & R2 & MS & HR2).
  set (rdr := (Z_to_bv 5 (Z.of_nat rd)) : reg) in *.
  eapply (L5LZ.cps_of_msteps_lazy (hl_segs L) H1 A fx' fx2 R' _ M1 R2 _ (mrestrict H1 M1) model1 K Hoff1 LY_nowrap (L5LZ.lazy_cover_ahid A model1) HAwf HMI1 Hh1 MS).
  intros model2 HMI2 HS12 _.
  replace (munrestrict H1 M1 (mrestrict H1 M1)) with M1
    by (apply FunctionalExtensionality.functional_extensionality; intros x; unfold munrestrict, mrestrict; destruct (H1 x); reflexivity).
  assert (HLF2 : CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model2).
  { constructor.
    - rewrite (CCA.vis_sbm A model1 model2 M1 HS12). exact HLFv.
    - exact (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (CCA.lfa_hid _ _ _ _ _ _ _ _ _ _ HLF).
    - exact (same_but_materialized_trans _ _ _ (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF) HS12).
    - exact HMI2. }
  rewrite <- Xpc.
  set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) [rd])).
  pose proof (APS.ext_list_agree E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) [rd]) : env_agree nx E' E2) as Hag2.
  assert (HagC : env_agree (CC.cp_nx c) E' E2) by (eapply CC.env_agree_le; [exact Hag2 | exact Hnxc]).
  assert (HagNF : env_agree NF E E2) by (eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact Xnf] | eapply CC.env_agree_le; [exact Hag2 | lia]]).
  assert (Hrdr : ridx rdr = rd) by (unfold rdr, ridx; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; rewrite Z.mod_small by lia; lia).
  apply (HIH j cj fx2 E2 R2 A M1 model2 Hcj).
  - split.
    + rewrite Xregs. apply CH.fresh_regs_ok; [| exact Xsv | constructor; [lia | constructor]].
      intros r Hn. rewrite HR2; [exact (HR r)|]. intros ->. apply Hn. left. symmetry. exact Hrdr.
    + rewrite (CCA.vis_sbm A model1 model2 M1 HS12). unfold know_ok. apply Forall_forall. intros Y HY. pose proof (CC.has_cell_In _ _ (Xkn Y HY)) as HY'.
      eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y Xkv HY') | exact (CC.lf_cells _ _ _ _ _ _ _ HLFv Y HY')].
  - split.
    + unfold CHA.foot_chk in Hfoot. pose proof Hfoot as Hfoot'. apply andb_prop in Hfoot' as [Hfoot' _]. apply andb_prop in Hfoot' as [Hfoot' Hfv]. apply andb_prop in Hfoot' as [_ Hbv].
      apply (CHA.amb_step L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 Wo_incl Wo_ok
               i j E E2 A M1 M1 model1 model2 HA1); [intros a _; reflexivity | apply mem_grows_refl | exact HS12 | exact HMI2 | exact HagNF | | | |].
      * rewrite Hbe. exact (CH2.den_agree _ E E2 _ (CC.env_agree_trans _ _ _ _ Hag HagC) Hbv).
      * rewrite Hfe. exact (CHA.denF_agree sp0 _ E E2 _ (CC.env_agree_trans _ _ _ _ Hag HagC) Hfv).
      * rewrite Hfe. reflexivity.
      * intros cr HC. exact (CRED E E2 cr HC HagNF).
    + exact (USER E E' R R' A M model M1 model2 E2 HAt HA HXI Hag HLF2 HagC).
  - exact (FPIS _ _ _ _ _ _ _ _ MS HFP).
  - unfold CC.meas. rewrite Xmeas. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ HagC Xmv). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag Xmv). }
    rewrite Em. unfold CA.has in Xhas. apply existsb_exists in Xhas as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
    pose proof (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HY) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag Xmv) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Leaf.
End GDK.
