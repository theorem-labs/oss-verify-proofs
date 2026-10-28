(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg FPSteps
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridgesU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FXKU.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition inlF_chk (NF : nat) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (len : Z) (hv : list nat) : bool :=
  let regs := CA.ps_reglist ps in
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  (CH2.all_regs_chk ps && Z.eqb (CC.cp_pc cj) (SR.ps_pc ps + len) && CA.regs_eqb (CC.cp_regs cj) (APC.sr_fresh regs hv nx)
   && forallb (CC.has_cell (SR.ps_cells ps)) (CC.cp_know cj) && Nat.eqb (CC.cp_nx cj) (nx + length hv)
   && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1))
   && CA.has (SR.ps_cells ps) (KRange (CC.cp_meas c) 1 CC.MB)
   && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx (SR.ps_cells ps) && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
   && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32)%bool hv && Nat.leb NF (CC.cp_nx c)
   && Z.leb 0 (SR.ps_pc ps) && Z.ltb (SR.ps_pc ps + len) (2 ^ 64))%bool.

(* [comment removed for export] *)
Definition inlF_step (segs : list Segment) (FPI : FPState -> Prop) (pc len : Z) (hv : list nat) : Prop :=
  forall (fx : FPState) R (M : mem), FPI fx -> exists fx2 R2, FPI fx2 /\ (forall r : reg, ~ In (ridx r) hv -> getr R2 r = getr R r) /\
    msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 (pc + len)) M (seg_rom segs)).

(* [comment removed for export] *)
Definition fp_site (segs : list Segment) (pc : Z) : option (list nat) :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => if is_ecall w then None else
      match decode_any w with
      | Some (Fsgnj _ _ _ _ _, sz) => if Z.eqb sz 4 then Some [] else None
      | Some (Fmv FMV_F_X FMT_D _ _, sz) => if Z.eqb sz 4 then Some [] else None
      | Some (Fmv FMV_X_F FMT_D rd _, sz) => if (Z.eqb sz 4 && negb (bv_eqb rd 0))%bool then Some [ridx rd] else None
      | Some (Fcmp _ _ rd _ _, sz) => if (Z.eqb sz 4 && negb (bv_eqb rd 0))%bool then Some [ridx rd] else None
      | Some (Fclass _ rd _, sz) => if (Z.eqb sz 4 && negb (bv_eqb rd 0))%bool then Some [ridx rd] else None      (* [comment removed for export] *)
      | _ => None
      end
  | None => None
  end.
Lemma getr_upd_notin : forall (R : bvmap 5 word) (rd : reg) v (r : reg), ~ In (ridx r) [ridx rd] -> getr (regupd R rd v) r = getr R r.
Proof. intros R rd v r H. apply getr_other. intros ->. apply H. left. reflexivity. Qed.
Lemma pc4 : forall pc, 0 <= pc -> pc + 4 < 2 ^ 64 -> v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof.
  intros pc H0 H1. unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma fp_step_fclass : forall (fx : FPState) segs regs pc mem rom w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass fmt rd rs1, 4%Z) ->
  exists v : word,
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w fmt rd rs1 Hf He Hd. destruct fx as [fr cs].
  eexists. fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; reflexivity.
Qed.

Theorem fp_site_step : forall segs pc hv, 0 <= pc -> pc + 4 < 2 ^ 64 -> fp_site segs pc = Some hv -> inlF_step segs PML.fp_ok pc 4 hv.
Proof.
  intros segs pc hv Hpc Hpc4 H fx R M HFP. unfold fp_site in H.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|discriminate].
  rewrite <- (pc4 pc) by lia.
  destruct i; try discriminate.
  - (* [comment removed for export] *) lazymatch type of Hd with decode_any w = Some (Fsgnj ?o0 ?f0 ?r0 ?s1 ?s2, _) => rename o0 into op, f0 into fmt, r0 into rd, s1 into rs1, s2 into rs2 end.
    destruct (Z.eqb_spec sz 4) as [->|]; [|discriminate]. injection H as <-.
    destruct (fp_step_fsgnj fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w op fmt rd rs1 rs2 Hf He Hd) as (fr' & Hs).
    exists (mkFP fr' (@fp_csr fx)), R. split; [exact HFP|]. split; [intros r _; reflexivity|]. eapply mst_step; [reflexivity | exact Hs | apply mst_refl].
  - (* [comment removed for export] *) lazymatch type of Hd with decode_any w = Some (Fcmp ?o0 ?f0 ?r0 ?s1 ?s2, _) => rename o0 into op, f0 into fmt, r0 into rd, s1 into rs1, s2 into rs2 end.
    lazymatch type of H with (if ?bb then _ else _) = _ => destruct bb eqn:Hb; [|discriminate] end.
    apply andb_prop in Hb as [Hsz Hrd]. apply Z.eqb_eq in Hsz. subst sz. apply negb_true_iff in Hrd. injection H as <-.
    destruct (fp_step_fcmp fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w op fmt rd rs1 rs2 Hf He Hd HFP) as (b & cs' & Hz & Hs). rewrite Hrd in Hs.
    exists (mkFP (@fp_regs fx) cs'), (regupd R rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0)). split; [exact Hz|]. split; [intros r Hr; exact (getr_upd_notin R rd _ r Hr)|].
    eapply mst_step; [reflexivity | exact Hs | apply mst_refl].
  - (* [comment removed for export] *) lazymatch type of Hd with decode_any w = Some (Fmv ?d0 ?f0 ?r0 ?s0, _) => rename r0 into rd, s0 into rs1; destruct d0; destruct f0; try discriminate end.
    + (* [comment removed for export] *) lazymatch type of H with (if ?bb then _ else _) = _ => destruct bb eqn:Hb; [|discriminate] end.
      apply andb_prop in Hb as [Hsz Hrd]. apply Z.eqb_eq in Hsz. subst sz. apply negb_true_iff in Hrd. injection H as <-.
      pose proof (fp_step_fmv_x_d fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w rd rs1 Hf He Hd) as Hs. rewrite Hrd in Hs.
      exists fx, (regupd R rd (reg_get (@fp_regs fx) rs1)). split; [exact HFP|]. split; [intros r Hr; exact (getr_upd_notin R rd _ r Hr)|].
      eapply mst_step; [reflexivity | exact Hs | apply mst_refl].
    + (* [comment removed for export] *) destruct (Z.eqb_spec sz 4) as [->|]; [|discriminate]. injection H as <-.
      pose proof (fp_step_fmv_d_x fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w rd rs1 Hf He Hd) as Hs.
      exists (mkFP (bvmap_set rd (getr R rs1) (@fp_regs fx)) (@fp_csr fx)), R. split; [exact HFP|]. split; [intros r _; reflexivity|].
      eapply mst_step; [reflexivity | exact Hs | apply mst_refl].
  - (* [comment removed for export] *) lazymatch type of Hd with decode_any w = Some (Fclass ?f0 ?r0 ?s0, _) => rename f0 into fmt, r0 into rd, s0 into rs1 end.
    lazymatch type of H with (if ?bb then _ else _) = _ => destruct bb eqn:Hb; [|discriminate] end.
    apply andb_prop in Hb as [Hsz Hrd]. apply Z.eqb_eq in Hsz. subst sz. apply negb_true_iff in Hrd. injection H as <-.
    destruct (fp_step_fclass fx segs R (Z_to_bv 64 pc) M (seg_rom segs) w fmt rd rs1 Hf He Hd) as (v & Hs). rewrite Hrd in Hs.
    exists fx, (regupd R rd v). split; [exact HFP|]. split; [intros r Hr; exact (getr_upd_notin R rd _ r Hr)|].
    eapply mst_step; [reflexivity | exact Hs | apply mst_refl].
Qed.

Section V.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable LBo : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable G : Type.
Variable gB : G -> list (Z * Z).
Variable CredV : G -> nat -> env -> credit -> Prop.
Variable XIv : G -> nat -> env -> mem -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBo sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - CH.hd_scr d) (CH.hd_scr d).
Hypothesis HEAPCHK : CH2.heap_chk3 NF d BLS CPS TAGS = true.
Hypothesis CredV_iE : forall g i j E E' cr, CredV g i E cr -> CredV g j E' cr.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.

Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS G gB CredV).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS G gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Theorem inl_leaf_okV : forall i c k ps pc j cj len hv g M0c,
  OKV M0c -> is_leaf i c k ps (CC.TOther pc) -> nth_error CPS j = Some cj ->
  inlF_chk NF c ps cj len hv = true ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true -> CH2.blocks_vars_lt (CC.cp_nx c) (nth i BLS []) = true ->
  inlF_step (hl_segs L) PML.fp_ok (SR.ps_pc ps) len hv ->
  (forall E E' R R' (M M' : mem) model E2, CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' -> env_agree (CC.cp_nx c) E' E2 -> XIv g j E2 M') ->
  LEAFOKV g M0c i c ps.
Proof.
  intros i c k ps pc j cj len hv g M0c HOKV IL Hcj Hchk Hbe Hbv Hstep USER fx' E R M model E' R' M' HAt [HA HXI] HFP Hag HLF HIH.
  unfold inlF_chk in Hchk.
  apply andb_prop in Hchk as [Hchk Xpc1]. apply andb_prop in Hchk as [Hchk Xpc0]. apply Z.leb_le in Xpc0. apply Z.ltb_lt in Xpc1.
  apply andb_prop in Hchk as [Hchk Xnf]. apply andb_prop in Hchk as [Hchk Xhv]. apply andb_prop in Hchk as [Hchk Xmv].
  apply andb_prop in Hchk as [Hchk Xkv]. apply andb_prop in Hchk as [Hchk Xsv]. apply andb_prop in Hchk as [Hchk Xhas]. apply andb_prop in Hchk as [Hchk Xmeas].
  apply andb_prop in Hchk as [Hchk Xnx]. apply andb_prop in Hchk as [Hchk Xkn]. apply andb_prop in Hchk as [Hchk Xregs]. apply andb_prop in Hchk as [Xall Xpc].
  apply Nat.leb_le in Xnf. apply Z.eqb_eq in Xpc. apply CH2.regs_eqb_eq in Xregs. rewrite forallb_forall in Xkn.
  apply Nat.eqb_eq in Xnx. apply expr_eqb_eq in Xmeas. apply CH2.blocks_eqb_eq in Hbe.
  set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  set (regs := CA.ps_reglist ps) in *.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  pose proof (CH2.leaf_regs_ok L NF sp0 d STK SCR_pos NF32 c ps E' R' _ _ Xall HLF) as HR. fold regs in HR.
  (* [comment removed for export] *)
  pose proof (CH2.leaf_amb3 L HI HIok LYI LYE LYR NF E0 M0c model0 (CH2V.LBr LBo G gB g) sp0 d W BLS (CredV g) STK SCR_pos NF32 SP0 W_ok WRS_ok CPS TAGS HEAPCHK
                i c k ps pc IL E E' R R' M M' model HAt HA Hag HLF) as HA1.
  destruct (CH2.amb3_model L HI NF E0 M0c model0 (CH2V.LBr LBo G gB g) sp0 d W BLS (CredV g) (XIv g) i E M model (conj HA HXI)) as [Hh1 Hl1].
  (* [comment removed for export] *)
  destruct (Hstep fx' R' M' HFP) as (fx2 & R2 & HFP2 & HR2 & MS).
  eapply L5.cps_of_msteps; [exact Hh1 | exact Hl1 | exact MS |].
  rewrite <- Xpc.
  set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv)).
  pose proof (APS.ext_list_agree E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv) : env_agree nx E' E2) as Hag2.
  assert (HagC : env_agree (CC.cp_nx c) E' E2) by (eapply CC.env_agree_le; [exact Hag2 | exact Hnxc]).
  assert (HagNF : env_agree NF E E2) by (eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact Xnf] | eapply CC.env_agree_le; [exact Hag2 | lia]]).
  apply (HIH j cj fx2 E2 R2 M' model Hcj).
  - (* [comment removed for export] *)
    split.
    + rewrite Xregs. apply CH.fresh_regs_ok; [| exact Xsv |].
      * intros r Hn. rewrite (HR2 r Hn). exact (HR r).
      * apply Forall_forall. intros r Hr. rewrite forallb_forall in Xhv. specialize (Xhv r Hr). apply andb_prop in Xhv as [X1 X2]. apply Nat.ltb_lt in X1, X2. lia.
    + unfold know_ok. apply Forall_forall. intros Y HY. pose proof (CC.has_cell_In _ _ (Xkn Y HY)) as HY'.
      eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y Xkv HY') | exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY')].
  - (* [comment removed for export] *)
    apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS G gB CredV XIv g M0c j E2 M' model HOKV). split.
    + apply (CH2.amb_pure_step L HI HIok LYI LYE LYR NF E0 M0c model0 (CH2V.LBr LBo G gB g) sp0 d W BLS (CredV g) STK SCR_pos NF32 W_ok
               i j E E2 M' M' model HA1); [intros a _; reflexivity | apply mem_grows_refl | exact HagNF | | intros cr HC; exact (CredV_iE g i j E E2 cr HC)].
      rewrite Hbe. exact (CH2.den_agree _ E E2 _ (CC.env_agree_trans _ _ _ _ Hag HagC) Hbv).
    + exact (USER E E' R R' M M' model E2 HAt HA HXI Hag HLF HagC).
  - exact HFP2.
  - (* [comment removed for export] *)
    unfold CC.meas. rewrite Xmeas. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ HagC Xmv). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag Xmv). }
    rewrite Em. unfold CA.has in Xhas. apply existsb_exists in Xhas as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
    pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ HY) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag Xmv) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.
End V.

Section VS.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable LBo : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable GR : list (Z * Z).
Variable kx bx : Z.
Variable XIv : ESBU.sghost -> nat -> env -> mem -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBo sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - CH.hd_scr d) (CH.hd_scr d).
Variable S2 : Z.
Hypothesis S2OBJ : PML.obj_on_stack L sp0 S2 24.
Hypothesis W_S2 : In (S2, 24) W.
Variable OB : expr.
Variable OK : Z.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Hypothesis OADDR : estart E0 (SA OB OK) = S2.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Abbreviation gB := (ESBU.gB GR).
Abbreviation CredV := (ESBU.CredV L kx bx).
Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS ESBU.sghost gB CredV).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS ESBU.sghost gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Definition a0e (a0 : option Z) : option expr := match a0 with Some z => Some (ELit z) | None => None end.
(* [comment removed for export] *)
Definition strans_chkN (scr : Z) (a0 : option Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  if CH2.blocks_eqb BLj BLi then CH2.custom_chk NF d scr 0 BLi [(OB, OK, ELit 24)] [] (a0e a0) c ps cj BLi else None.

(* [comment removed for export] *)
Lemma strans_leaf_okN : forall (pc scr : Z) (PayP : Z -> Prop) (Ret : bvmap 5 word -> Z -> Prop) (a0 : option Z) i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  strans_chkN scr a0 c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall R2 pay, Ret R2 pay -> match a0 with Some z => PML.a0 R2 z /\ 0 <= z < 2 ^ 64 | None => True end) ->
  (forall E R (M : mem) model E' R' (M' : mem), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     ESBU.sink_inv M' S2 g) ->
  (forall E R (M : mem) model E' R' (M' : mem) cr (fx' : FPState), CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo ESBU.sghost gB g) sp0 d W BLS (CredV g) scr 0 c ps cj ci i E E' R' M' model ->
     ESBU.sink_inv M' S2 g ->
     hi_heap HI ((CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (ESBU.s_rep g)) cr M' (m_vmmaps model) -> PMES.screditU L cr (ESBU.s_rep g) kx bx ->
     PML.fp_ok fx' ->
     ((forall (fx2 : FPState) R2 (M2 : mem) model2 LB' cr' LBk Wc, PML.fp_ok fx2 ->
           (exists (rep' : PML.srep) (pay : Z), PayP pay /\ Ret R2 pay /\ PMES.sink_at M2 S2 rep' /\
              PMES.len (PML.srep_chars rep') = PMES.len (PML.srep_chars (ESBU.s_rep g)) + pay /\
              LB' = (CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks rep' /\ LBk = CH2.den E' (nth i BLS []) ++ LBo ++ GR /\ Wc = [(S2, 24)] /\
              PMES.screditU L cr' rep' kx bx) ->
           regs_preserved R' R2 -> L5C.hpres L LBk (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> model_but_vm model model2 -> hi_heap HI LB' cr' M2 (m_vmmaps model2) ->
           srealizes RSEGS SCFG (@PML.cfg fx2 R2 (CC.cp_pc cj) M2 model2) K) ->
        srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K)) ->
  (forall E R (M : mem) model E' R' (M' : mem) E2 (M2 : mem) g' pay, CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree NF E0 E' ->
     env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBo ++ GR) (sp0 + CH2.ci_csp ci) scr [(S2, 24)] M' M2 ->
     ESBU.sink_inv M2 S2 g' -> ESBU.s_len g' = ESBU.s_len g + pay -> PayP pay ->
     XIv g' j E2 M2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr PayP Ret a0 i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk RETA0 XILEAF CALL XIRET fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct HAmb as [HAmbH HXI0].
  unfold strans_chkN in Hchk.
  destruct (CH2.blocks_eqb (nth j BLS []) (nth i BLS [])) eqn:B3; [|discriminate]. apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *.
  destruct (CH2V.custom_retV L HI HIok LYI LYE LYR NF E0 M00 model0 LBo sp0 d W BLS ESBU.sghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok
              g M0c scr 0%nat BLi _ _ (a0e a0) i c ps j cj ci HOKV Hcj Hchk E R M model E' R' M' HAt HAmbH Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (BV : CH2.blocks_vars_lt (CH2.ci_nx ci) BLi = true).
  { unfold CH2.custom_chk in Hchk. destruct (CH2.common_chk_x NF d scr 0 c ps cj BLi) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof (XILEAF E R M model E' R' M' HAt HAmbH HXI0 Hag HLF) as HINV.
  set (own := CH2.den E' BLi) in *.
  unfold CH2.cur, CH2V.LBr in HH. fold BLi in HH, Hden. rewrite <- Hden in HH. fold own in HH.
  assert (Ho : estart E' (SA OB OK) = S2) by (rewrite (PB.estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct S2OBJ as (O3 & O4 & O5). pose proof STK as (S1 & S2' & S3 & S4 & S5).
  assert (PERM1 : Permutation (own ++ LBo ++ gB g) ((own ++ LBo ++ GR) ++ PML.srep_blocks (ESBU.s_rep g))).
  { unfold ESBU.gB. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH PERM1) as HH1.
  pose proof (CALL E R M model E' R' M' cr fx' HAt HAmbH HXI0 Hag HLF CF HINV HH1 HC HFP) as Hcall.
  rewrite Hpc. rewrite LS. apply Hcall.
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (rep' & pay & HPay & HRet & Hsink2 & Hlen' & -> & -> & -> & HSC') HRP HPRES Hbv2 HH2.
  pose proof (PmLayout.ly_kpm L LAY) as KPM.
  assert (Hlen2 : PMES.len (PML.srep_chars rep') = ESBU.s_len g + pay) by (destruct HINV as (_ & I4); lia).
  assert (PERM2 : Permutation ((own ++ LBo ++ GR) ++ PML.srep_blocks rep') (own ++ LBo ++ PML.srep_blocks rep' ++ GR)).
  { rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2 PERM2) as HH2'.
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  assert (HINV2 : ESBU.sink_inv M2 S2 (ESBU.g_upd g rep' pay)) by (split; [exact Hsink2 | exact Hlen2]).
  assert (HC' : CredV (ESBU.g_upd g rep' pay) j (CH2.retEx E' (CH2.ci_nx ci) [] R2) cr').
  { exact HSC'. }
  unfold PML.cfg. rewrite <- LS.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  eapply (RET fx2 R2 M2 model2 [] (own ++ LBo ++ GR) [(S2, 24)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) _ HPRES).
  - intros b Hb. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb].
  - intros w a Hw Hin. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  - intros X [].
  - fold E2.
    assert (Hcur : CH2.cur (CH2V.LBr LBo ESBU.sghost gB (ESBU.g_upd g rep' pay)) BLS j E2 = own ++ LBo ++ PML.srep_blocks rep' ++ GR).
    { unfold CH2.cur, CH2V.LBr, ESBU.gB, ESBU.g_upd. cbn [ESBU.s_rep]. rewrite B3. fold BLi. rewrite (CH2.den_agree (CH2.ci_nx ci) E' E2 BLi Hag2 BV). reflexivity. }
    destruct (CH2V.amb_callee_xV L HI LYI LYE NF E0 M00 model0 LBo sp0 d W BLS ESBU.sghost gB CredV STK SCR_pos NF32 DEF0 g (ESBU.g_upd g rep' pay) M0c scr 0%nat c ps cj ci i j E E' R' M' model
                E2 M2 model2 (own ++ LBo ++ GR) [(S2, 24)] cr' HOKV CF HPRES) as [OK2 HA2].
    + intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). destruct Hw as [<-|[]]. exact (Hout (S2, 24) W_S2 Hin).
    + exact Hbv2.
    + rewrite Hcur. exact HH2'.
    + exact Hag2.
    + exact HC'.
    + apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS ESBU.sghost gB CredV XIv (ESBU.g_upd g rep' pay) M2 j E2 M2 model2 OK2).
      split; [exact HA2|].
      apply (XIRET E R M model E' R' M' E2 M2 (ESBU.g_upd g rep' pay) pay HAt HAmbH HXI0 HagE' Hag HLF Hag2 V3 HPRES HINV2); [reflexivity | exact HPay].
  Unshelve. destruct a0 as [z|]; [|exact I]. cbv beta iota. destruct (RETA0 R2 pay HRet) as [Hz Hzr]. rewrite Hz. cbn [edenot]. reflexivity.
Qed.
End VS.
End FXKU.
