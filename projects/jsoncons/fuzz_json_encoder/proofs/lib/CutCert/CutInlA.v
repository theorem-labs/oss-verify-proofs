(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape FPSteps
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutShA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CIA.
Definition mem := (word -> option byte).

Definition kn_eqb (a b : list kentry) : bool := (Nat.eqb (length a) (length b) && forallb (fun xy => APC.kentry_eqb (fst xy) (snd xy)) (combine a b))%bool.
Lemma kn_eqb_eq : forall a b, kn_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; unfold kn_eqb in H; cbn [length combine forallb fst snd] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hl H]. apply andb_prop in H as [Hx H]. apply APS.kentry_eqb_eq in Hx. subst y. f_equal. apply IH. unfold kn_eqb.
  apply Nat.eqb_eq in Hl. injection Hl as Hl. rewrite Hl, Nat.eqb_refl. exact H.
Qed.
Definition all_regs_chk (ps : SR.post_spec) : bool :=
  forallb (fun r => existsb (fun ie : nat * expr => Nat.eqb (fst ie) r) (SR.ps_regs ps)) (seq 1 31).

(* [comment removed for export] *)
Definition inl1_chk (NF : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (len : Z) (rd : nat) : bool :=
  let regs := CA.ps_reglist ps in
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  (all_regs_chk ps && Z.eqb (CC.cp_pc cj) (SR.ps_pc ps + len) && CA.regs_eqb (CC.cp_regs cj) (APC.sr_fresh regs [rd] nx)
   && forallb (CC.has_cell (SR.ps_cells ps)) (CC.cp_know cj) && Nat.eqb (CC.cp_nx cj) (nx + 1)
   && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1))
   && CA.has (SR.ps_cells ps) (KRange (CC.cp_meas c) 1 CC.MB)
   && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx (SR.ps_cells ps) && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
   && Nat.ltb 0 rd && Nat.ltb rd 32 && Nat.leb NF (CC.cp_nx c))%bool.
(* [comment removed for export] *)
Definition same_chk (NF : nat) (d : CH.hdecl) (c : CC.cutpoint) (BLi BLj : CA.blocks) (FLi FLj : list (expr * Z * Z)) : bool :=
  (CHA.foot_chk NF d c BLi FLi && CH2.blocks_eqb BLj BLi && CHA.frames_eqb FLj FLi)%bool.

(* [comment removed for export] *)
Definition inl1_step (segs : list Segment) (pc len : Z) (rd : nat) : Prop :=
  forall (fx : FPState) R (M : mem), exists v : word,
    msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx (regupd R (Z_to_bv 5 (Z.of_nat rd)) v) (Z_to_bv 64 (pc + len)) M (seg_rom segs)).

(* [comment removed for export] *)
Lemma fp_step_fclass : forall (fx : FPState) segs regs pc M rom w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass fmt rd rs1, 4%Z) ->
  exists v, RiscvSemantics.step segs (@mkst fx regs pc M rom) =
            MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) M rom).
Proof.
  intros fx segs regs pc M rom w fmt rd rs1 Hf He Hd.
  destruct fx as [fr cs]. eexists. fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.
Definition site_fclass_chk (segs : list Segment) (pc : Z) : option nat :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => if is_ecall w then None else
              match decode_any w with
              | Some (Fclass _ rd _, sz) => if (Z.eqb sz 4 && negb (bv_eqb rd 0))%bool then Some (ridx rd) else None
              | _ => None
              end
  | None => None
  end.
Theorem fclass_step : forall segs pc rd, 0 <= pc -> pc + 4 < 2 ^ 64 -> site_fclass_chk segs pc = Some rd -> inl1_step segs pc 4 rd.
Proof.
  intros segs pc rd0 Hpc Hpc4 H fx R M. unfold site_fclass_chk in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|discriminate].
  destruct i; try discriminate. lazymatch type of H with (if ?bb then _ else _) = _ => destruct bb eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hsz Hrd]. apply Z.eqb_eq in Hsz. subst sz. apply negb_true_iff in Hrd. injection H as <-.
  destruct (fp_step_fclass fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w fmt rd rs1 Hf He Hd) as (v & Hs).
  exists v. rewrite Hrd in Hs. rewrite (CC.reg_of_ridx rd). rewrite <- (CSL.pc4 pc 4) by lia. eapply mst_step; [reflexivity | exact Hs | apply mst_refl].
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

Lemma leaf_regs_ok : forall c ps E' R' M M', all_regs_chk ps = true -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
  regs_ok E' (CA.ps_reglist ps) R'.
Proof.
  intros c ps E' R' M M' H HLF r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
  - assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
    cbn [edenot]. replace (0%bv : bv 5) with (Z_to_bv 5 0) by (apply bv_eq; reflexivity). exact (CC.lf_x0 _ _ _ _ _ _ _ HLF).
  - assert (Hr : (1 <= ridx r < 32)%nat).
    { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
      unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
    unfold CA.ps_reglist. destruct (ridx r) as [|m] eqn:Em; [lia|]. cbn [nth].
    rewrite (nth_indep _ (ELit 0) (CA.ps_reg ps 0%nat)) by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (CA.ps_reg ps) (seq 1 31) 0%nat m). rewrite seq_nth by lia.
    unfold all_regs_chk in H. rewrite forallb_forall in H. specialize (H (1 + m)%nat ltac:(apply in_seq; lia)).
    unfold CA.ps_reg. destruct (find (fun ie : nat * expr => Nat.eqb (fst ie) (1 + m)) (SR.ps_regs ps)) as [[i e]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hi]. cbn [fst snd] in *. apply Nat.eqb_eq in Hi. subst i.
      destruct (CC.lf_regs _ _ _ _ _ _ _ HLF _ _ Hin) as [_ Hg]. rewrite <- Hg. f_equal. rewrite <- (CC.reg_of_ridx r). rewrite Em. reflexivity.
    + exfalso. apply existsb_exists in H as (ie & Hin & Hb). rewrite (find_none _ _ Hf ie Hin) in Hb. discriminate.
Qed.

Theorem inl1_leaf : forall i c ps j cj len rd,
  nth_error CPS j = Some cj ->
  inl1_chk NF c ps cj len rd = true ->
  same_chk NF d c (nth i BLS []) (nth j BLS []) (nth i FFS []) (nth j FFS []) = true ->
  0 <= SR.ps_pc ps -> SR.ps_pc ps + len < 2 ^ 64 -> 0 <= len ->
  inl1_step (hl_segs L) (SR.ps_pc ps) len rd ->
  (forall E E' R R' A M model M1 model1 E2,
     CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> XI i E A M model -> env_agree (CC.cp_nx c) E E' ->
     CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> env_agree (CC.cp_nx c) E' E2 -> XI j E2 A M1 model1) ->
  (forall E E2 cr, Cred i E cr -> env_agree NF E E2 -> Cred j E2 cr) ->
  CCA.leaf_ok (hl_segs L) CPS AMBX K FPI i c ps.
Proof.
  intros i c ps j cj len rd Hcj Hchk Hsame Hpc0 Hpc1 Hlen Hstep USER CRED fx' E R A M model E' R' M1 model1 HAt [HA HXI] HFP Hag HLF HIH.
  (* [comment removed for export] *)
  unfold inl1_chk in Hchk.
  apply andb_prop in Hchk as [Hchk Xnf]. apply andb_prop in Hchk as [Hchk Xrd32]. apply andb_prop in Hchk as [Hchk Xrd0]. apply andb_prop in Hchk as [Hchk Xmv].
  apply andb_prop in Hchk as [Hchk Xkv]. apply andb_prop in Hchk as [Hchk Xsv]. apply andb_prop in Hchk as [Hchk Xhas]. apply andb_prop in Hchk as [Hchk Xmeas].
  apply andb_prop in Hchk as [Hchk Xnx]. apply andb_prop in Hchk as [Hchk Xkn]. apply andb_prop in Hchk as [Hchk Xregs]. apply andb_prop in Hchk as [Xall Xpc].
  apply Nat.leb_le in Xnf. apply Nat.ltb_lt in Xrd32. apply Nat.ltb_lt in Xrd0. apply Z.eqb_eq in Xpc. apply CH2.regs_eqb_eq in Xregs. rewrite forallb_forall in Xkn.
  apply Nat.eqb_eq in Xnx. apply expr_eqb_eq in Xmeas.
  unfold same_chk in Hsame. apply andb_prop in Hsame as [Hsame Hfe]. apply andb_prop in Hsame as [Hfoot Hbe]. apply CH2.blocks_eqb_eq in Hbe. apply CHA.frames_eqb_eq in Hfe.
  set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  set (regs := CA.ps_reglist ps) in *.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
  pose proof (leaf_regs_ok c ps E' R' _ _ Xall HLFv) as HR. fold regs in HR.
  (* [comment removed for export] *)
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1 Hfoot HAt HA Hag HLF) as HA1.
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M1 model1 HA1) as (Hh1 & HMI1 & HAwf & Hoff1).
  set (H1 := ahid A model1).
  (* [comment removed for export] *)
  destruct (Hstep fx' R' (mrestrict H1 M1)) as (v & MS).
  set (rdr := (Z_to_bv 5 (Z.of_nat rd)) : reg) in *. set (R2 := regupd R' rdr v) in *.
  eapply (L5LZ.cps_of_msteps_lazy (hl_segs L) H1 A fx' fx' R' _ M1 R2 _ (mrestrict H1 M1) model1 K Hoff1 LY_nowrap (L5LZ.lazy_cover_ahid A model1) HAwf HMI1 Hh1 MS).
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
  apply (HIH j cj fx' E2 R2 A M1 model2 Hcj).
  - (* [comment removed for export] *)
    split.
    + rewrite Xregs. apply CH.fresh_regs_ok; [| exact Xsv | constructor; [lia | constructor]].
      intros r Hn. unfold R2. rewrite getr_other; [exact (HR r)|]. intros ->. apply Hn. left. symmetry. exact Hrdr.
    + rewrite (CCA.vis_sbm A model1 model2 M1 HS12). unfold know_ok. apply Forall_forall. intros Y HY. pose proof (CC.has_cell_In _ _ (Xkn Y HY)) as HY'.
      eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y Xkv HY') | exact (CC.lf_cells _ _ _ _ _ _ _ HLFv Y HY')].
  - (* [comment removed for export] *)
    split.
    + unfold CHA.foot_chk in Hfoot. pose proof Hfoot as Hfoot'. apply andb_prop in Hfoot' as [Hfoot' _]. apply andb_prop in Hfoot' as [Hfoot' Hfv]. apply andb_prop in Hfoot' as [_ Hbv].
      apply (CHA.amb_step L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 Wo_incl Wo_ok
               i j E E2 A M1 M1 model1 model2 HA1); [intros a _; reflexivity | apply mem_grows_refl | exact HS12 | exact HMI2 | exact HagNF | | | |].
      * rewrite Hbe. exact (CH2.den_agree _ E E2 _ (CC.env_agree_trans _ _ _ _ Hag HagC) Hbv).
      * rewrite Hfe. exact (CHA.denF_agree sp0 _ E E2 _ (CC.env_agree_trans _ _ _ _ Hag HagC) Hfv).
      * rewrite Hfe. reflexivity.
      * intros cr HC. exact (CRED E E2 cr HC HagNF).
    + exact (USER E E' R R' A M model M1 model2 E2 HAt HA HXI Hag HLF2 HagC).
  - exact HFP.
  - (* [comment removed for export] *)
    unfold CC.meas. rewrite Xmeas. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ HagC Xmv). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag Xmv). }
    rewrite Em. unfold CA.has in Xhas. apply existsb_exists in Xhas as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
    pose proof (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HY) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag Xmv) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Leaf.
End CIA.
