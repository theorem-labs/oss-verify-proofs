(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs L5Core FrmInv FpBridge.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CVF.

Definition kn_eqb (a b : list kentry) : bool :=
  (Nat.eqb (length a) (length b) && forallb (fun p : kentry * kentry => APC.kentry_eqb (fst p) (snd p)) (combine a b))%bool.
Lemma kn_eqb_eq : forall a b, kn_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; unfold kn_eqb in H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hl H]. apply andb_prop in H as [Hxy H].
  apply APS.kentry_eqb_eq in Hxy. subst y. f_equal. apply IH. unfold kn_eqb. rewrite Hl, H. reflexivity.
Qed.
Lemma regs_eqb_eq : forall a b, CA.regs_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hxy H]. apply AX2S.expr_eqb_eq in Hxy. subst y. f_equal. exact (IH _ H).
Qed.

Definition all_regs_chk (ps : SR.post_spec) : bool :=
  forallb (fun r => existsb (fun ie : nat * expr => Nat.eqb (fst ie) r) (SR.ps_regs ps)) (seq 1 31).

Definition inl_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (len : Z) (hv : list nat) (a0 : option Z) : bool :=
  let regs := CA.ps_reglist ps in
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  let regs1 := APC.sr_fresh regs hv nx in
  let regs2 := match a0 with Some z => sr_upd regs1 10 (ELit z) | None => regs1 end in
  (all_regs_chk ps && Z.eqb (CC.cp_pc cj) (SR.ps_pc ps + len) && CA.regs_eqb (CC.cp_regs cj) regs2
   && kn_eqb (CC.cp_know cj) (SR.ps_cells ps) && Nat.eqb (CC.cp_nx cj) (nx + length hv)
   && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1))
   && CA.has (SR.ps_cells ps) (KRange (CC.cp_meas c) 1 CC.MB)
   && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx (SR.ps_cells ps) && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
   && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) hv
   && match a0 with Some z => (Z.leb 0 z && Z.ltb z (2 ^ 64) && match hv with [] => true | _ => false end)%bool | None => true end)%bool.

Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable CPS : list CC.cutpoint.
Variable NF : nat.
Variable E0 : env.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variable F0 : list SGP.region.
Variable K : ShapeAlg.TSet.
Hypothesis Hhalt : m_halted model0 = None.
Hypothesis Hlazy : m_vm_lazy model0 = [].
Hypothesis SAFE : FrmInv.text_safe segs.

Abbreviation Amb := (CL.pure_amb NF E0 M0 model0 F0).
Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Lemma leaf_regs_ok : forall c ps E' R' M M', all_regs_chk ps = true -> CC.leaf_facts segs c ps E' R' M M' ->
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

(* [comment removed for export] *)
Lemma inl_common : forall i c ps j cj len hv a0,
  nth_error CPS j = Some cj -> inl_chk c ps cj len hv a0 = true -> CL.sub_F NF E0 F0 c -> (NF <= CC.cp_nx c)%nat ->
  forall (fx2 : FPState) E R M model E' R' R2 M',
    CC.At segs c E R M -> Amb i E M model -> FrmInv.fp_ok fx2 ->
    env_agree (CC.cp_nx c) E E' -> CC.leaf_facts segs c ps E' R' M M' ->
    CC.IH segs CPS Amb K FrmInv.fp_ok (CC.meas c E) ->
    (forall r : reg, ~ In (ridx r) hv -> getr R2 r = match a0 with Some z => if bv_eqb r 10 then Z_to_bv 64 z else getr R' r | None => getr R' r end) ->
    srealizes segs SCFG (mkCfg (mk fx2 R2 (SR.ps_pc ps + len) M') model) K.
Proof.
  intros i c ps j cj len hv a0 Hcj Hchk Hsub Hnf fx2 E R M model E' R' R2 M' HAt HAmb HFP Hag HLF HIH Hkeep.
  unfold inl_chk in Hchk. do 11 (apply andb_prop in Hchk as [Hchk ?X]).
  rename Hchk into Xall. apply Z.eqb_eq in X9. apply regs_eqb_eq in X8. apply kn_eqb_eq in X7. apply Nat.eqb_eq in X6. apply AX2S.expr_eqb_eq in X5.
  set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  set (regs := CA.ps_reglist ps) in *.
  pose proof (leaf_regs_ok c ps E' R' M M' Xall HLF) as HR. fold regs in HR.
  set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv)).
  pose proof (APS.ext_list_agree E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) hv) : env_agree nx E' E2) as Hag2.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  assert (HagNF : env_agree NF E' E2) by (eapply CC.env_agree_le; [exact Hag2 | lia]).
  assert (Hhv : Forall (fun r => (0 < r < 32)%nat) hv).
  { apply Forall_forall. intros r Hr. rewrite forallb_forall in X0. specialize (X0 r Hr). apply andb_prop in X0 as [A B].
    apply Nat.ltb_lt in A. apply Nat.ltb_lt in B. lia. }
  rewrite <- X9.
  apply (HIH j cj fx2 E2 R2 M' model Hcj).
  - (* [comment removed for export] *)
    split.
    + rewrite X8. destruct a0 as [z|].
      * (* [comment removed for export] *)
        apply andb_prop in X as [X Xhv]. apply andb_prop in X as [Xz0 Xz1]. apply Z.leb_le in Xz0. apply Z.ltb_lt in Xz1.
        destruct hv; [|discriminate]. cbn [APC.sr_fresh].
        intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er0.
        { assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0). cbn [edenot]. apply getr_zero. }
        rewrite nth_sr_upd. rewrite (Hkeep r (fun X => X)).
        destruct (bv_eqb r 10) eqn:Er10.
        { assert (r = 10%bv) as -> by (apply bv_eq; unfold bv_eqb in Er10; apply Z.eqb_eq in Er10; exact Er10).
          change (ridx 10%bv) with 10%nat. cbn [Nat.eqb edenot]. reflexivity. }
        assert (Hne : Nat.eqb (ridx r) 10 = false).
        { apply Nat.eqb_neq. intros Hx. unfold bv_eqb in Er10. apply Z.eqb_neq in Er10. apply Er10.
          unfold ridx in Hx. pose proof (bv_unsigned_in_range _ r). change (bv_unsigned (10%bv : bv 5)) with 10. lia. }
        rewrite Hne. rewrite (HR r). unfold sr_get. rewrite Er0.
        apply (SR.edenot_agree_AP nx); [exact Hag2 | apply CH.nth_vars_lt; exact X3].
      * apply CH.fresh_regs_ok; [| exact X3 | exact Hhv].
        intros r Hn. rewrite (Hkeep r Hn). exact (HR r).
    + rewrite X7. unfold know_ok. apply Forall_forall. intros Y HY.
      eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y X2 HY) | exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY)].
  - (* [comment removed for export] *)
    eapply CL.pure_amb_step; [exact Hsub | exact Hnf | exact HAmb | exact Hag | exact HLF | exact HagNF].
  - exact HFP.
  - (* [comment removed for export] *)
    unfold CC.meas. rewrite X5. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
    assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
    { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 Hnxc) X1). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag X1). }
    rewrite Em. unfold CA.has in X4. apply existsb_exists in X4 as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
    pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ HY) as HM. cbn [kentry_ok] in HM.
    rewrite <- (SR.edenot_agree_AP _ E E' _ Hag X1) in HM. unfold CC.MB in HM.
    rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.

Theorem inl_leaf_ok : forall i c ps j cj len hv,
  nth_error CPS j = Some cj -> inl_chk c ps cj len hv None = true -> CL.sub_F NF E0 F0 c -> (NF <= CC.cp_nx c)%nat ->
  FPB.inl_step segs (SR.ps_pc ps) len hv ->
  CC.leaf_ok segs CPS Amb K FrmInv.fp_ok i c ps.
Proof.
  intros i c ps j cj len hv Hcj Hchk Hsub Hnf Hstep fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct (Hstep fx' R' M' HFP) as (fx2 & R2 & Hms & Hkeep).
  pose proof HAmb as (-> & _).
  eapply L5.cps_of_msteps; [exact Hhalt | exact Hlazy | exact Hms |].
  eapply (inl_common i c ps j cj len hv None Hcj Hchk Hsub Hnf fx2 E R M model0 E' R' R2 M'); try eassumption.
  exact (FrmInv.msteps_fp_ok segs SAFE _ _ _ _ _ _ _ _ _ _ Hms HFP).
Qed.

Theorem inl_leaf_ok_a0 : forall i c ps j cj len z,
  nth_error CPS j = Some cj -> inl_chk c ps cj len [] (Some z) = true -> CL.sub_F NF E0 F0 c -> (NF <= CC.cp_nx c)%nat ->
  FPB.inl_step_a0 segs (SR.ps_pc ps) len z ->
  CC.leaf_ok segs CPS Amb K FrmInv.fp_ok i c ps.
Proof.
  intros i c ps j cj len z Hcj Hchk Hsub Hnf Hstep fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct (Hstep fx' R' M' HFP) as (fx2 & Hms).
  pose proof HAmb as (-> & _).
  eapply L5.cps_of_msteps; [exact Hhalt | exact Hlazy | exact Hms |].
  eapply (inl_common i c ps j cj len [] (Some z) Hcj Hchk Hsub Hnf fx2 E R M model0 E' R' _ M'); try eassumption.
  - exact (FrmInv.msteps_fp_ok segs SAFE _ _ _ _ _ _ _ _ _ _ Hms HFP).
  - intros r _. destruct (bv_eqb r 10) eqn:Er.
    + assert (r = 10%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er). apply getr_same. discriminate.
    + apply getr_other. intros ->. unfold bv_eqb in Er. rewrite Z.eqb_refl in Er. discriminate.
Qed.

End WithSegs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition img_pre_of (IMG : option (Z * Z)) (M : word -> option byte) : Prop :=
  match IMG with Some (lo, hi) => 0 <= lo /\ hi <= 2 ^ 64 /\ L5.img_clear M lo hi | None => True end.
Definition CSAVED : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.
(* [comment removed for export] *)
Definition vf_contract (segs : list Segment) {SCFG_P : ScfgP} (entry SCR : Z) (IMG : option (Z * Z)) : Prop :=
  forall (fx : FPState) R M model K sp,
  m_halted model = None -> m_vm_lazy model = [] -> FrmInv.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp -> sp mod 16 = 0 -> 140735332483072 + SCR <= sp <= 140737488355328 -> L5.defined M (sp - SCR) SCR -> img_pre_of IMG M ->
  Hoare.ret_ok (getr R 1%bv) ->
  (forall (fx' : FPState) R' M', FrmInv.fp_ok fx' ->
      (forall a : word, ~ (sp - SCR <= bv_unsigned a < sp) -> M' a = M a) -> mem_grows M M' ->
      (forall x : reg, In (ridx x) CSAVED -> getr R' x = getr R x) ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (getr R 1%bv) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 entry) M (seg_rom segs)) model) K.


(* [comment removed for export] *)
Lemma vf_contract_weaken : forall (segs : list Segment) {SCFG_P : ScfgP} entry SCR SCR' IMG IMG',
  0 <= SCR <= SCR' -> (IMG = None \/ IMG = IMG') -> vf_contract segs entry SCR IMG -> vf_contract segs entry SCR' IMG'.
Proof.
  intros segs SP entry SCR SCR' IMG IMG' Hs Hi H fx R M model K sp Hh Hl Hfx Hsp Hal Hr Hdef Himg Hret HK.
  apply (H fx R M model K sp Hh Hl Hfx Hsp Hal); try assumption; try lia.
  - intros k Hk. replace (sp - SCR + k) with (sp - SCR' + (SCR' - SCR + k)) by lia. apply Hdef. lia.
  - destruct Hi as [-> | ->]; [exact I | exact Himg].
  - intros fx' R' M' F1 F2 F3 F4. apply HK; try assumption. intros a Ha. apply F2. lia.
Qed.

Lemma csaved_partition : forall r : reg, r <> 0%bv -> ~ In (ridx r) APC.caller_saved -> In (ridx r) CSAVED.
Proof.
  intros r Hr Hn.
  assert (T : forallb (fun n => (Nat.eqb n 0 || existsb (Nat.eqb n) APC.caller_saved || existsb (Nat.eqb n) CSAVED)%bool) (seq 0 32) = true) by reflexivity.
  rewrite forallb_forall in T. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
  specialize (T (ridx r) ltac:(apply in_seq; unfold ridx; lia)).
  apply orb_prop in T as [T|T]; [apply orb_prop in T as [T|T]|].
  - exfalso. apply Hr. apply bv_eq. apply Nat.eqb_eq in T. unfold ridx in T. change (bv_unsigned (0%bv : bv 5)) with 0. lia.
  - exfalso. apply Hn. apply existsb_exists in T as (x & Hx & He). apply Nat.eqb_eq in He. subst x. exact Hx.
  - apply existsb_exists in T as (x & Hx & He). apply Nat.eqb_eq in He. subst x. exact Hx.
Qed.

Section Leaf.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable entry SCR : Z.
Variable ENDS : list Z.
Variable RETS : list (nat * nat * nat * Z).                  (* [comment removed for export] *)
Variable INL : list (Z * (Z * list nat * option Z)).         (* [comment removed for export] *)
Variable CALLEES : list (Z * (Z * option (Z * Z))).          (* [comment removed for export] *)
Variable IMG : option (Z * Z).                               (* [comment removed for export] *)

Definition NF : nat := 32.
Definition F0 : list SGP.region := if Z.eqb SCR 0 then [] else [(EVar 2, - SCR, ELit SCR)].
Definition KN0 : list kentry :=
  [KRange (EVar 2) (140735332483072 + SCR) 140737488355328; KAlign (EVar 2) 16]
  ++ (match IMG with Some (lo, hi) => [KImg lo hi] | None => [] end)
  ++ (if Z.eqb SCR 0 then [] else [KWr (SA (EVar 2) (- SCR)) (ELit SCR); KUnk (SA (EVar 2) (- SCR)) (ELit SCR)]).
Definition img_pre (M : word -> option byte) : Prop := img_pre_of IMG M.

Definition entry_chk : bool :=
  match CPS with
  | c0 :: _ => (Z.eqb (CC.cp_pc c0) entry && CA.regs_eqb (CC.cp_regs c0) sr_id && kn_eqb (CC.cp_know c0) KN0 && Nat.eqb (CC.cp_nx c0) 32)%bool
  | [] => false
  end.
Definition F_ok (c : CC.cutpoint) : bool :=
  match CC.cp_F c with
  | [] => true
  | [(b, o, n)] => (negb (Z.eqb SCR 0) && expr_eqb b (EVar 2) && Z.eqb o (- SCR) && expr_eqb n (ELit SCR))%bool
  | _ => false
  end.
Definition call_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (SCRc : Z) (IMGc : option (Z * Z)) : bool :=
  let regs := CA.ps_reglist ps in
  let nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps) in
  match nth 1 regs (ELit 1), split_lit (nth 2 regs (ELit 0)) with
  | ELit ra, (spb, spo) =>
      (all_regs_chk ps && Z.eqb (CC.cp_pc cj) ra && Z.leb 0 ra && Z.ltb ra (2 ^ 47) && Z.eqb (ra mod 2) 0
       && expr_eqb spb (EVar 2) && Z.leb (- SCR) (spo - SCRc) && Z.leb spo 0 && Z.eqb (spo mod 16) 0 && Z.ltb 0 SCRc
       && CA.regs_eqb (CC.cp_regs cj) (APC.sr_fresh regs APC.caller_saved nx)
       && kn_eqb (CC.cp_know cj) (KUnk (SA spb (spo - SCRc)) (ELit SCRc) :: APC.kn_havoc (SR.ps_cells ps) spb (spo - SCRc) (ELit SCRc))
       && Nat.eqb (CC.cp_nx cj) (nx + APC.NCS)
       && expr_eqb (CC.cp_meas cj) (APC.esub (CC.cp_meas c) (ELit 1))
       && CA.has (SR.ps_cells ps) (KRange (CC.cp_meas c) 1 CC.MB)
       && APC.sr_vars_lt nx regs && APC.kn_vars_lt nx (APC.kn_havoc (SR.ps_cells ps) spb (spo - SCRc) (ELit SCRc))
       && APC.expr_vars_lt (CC.cp_nx c) (CC.cp_meas c)
       && match IMGc with Some (lo, hi) => CA.has (SR.ps_cells ps) (KImg lo hi) | None => true end)%bool
  | _, _ => false
  end.
Definition cut_chk (i : nat) (c : CC.cutpoint) : bool := (Nat.leb NF (CC.cp_nx c) && F_ok c)%bool.
Definition leaf_chk (i : nat) (ps : SR.post_spec) (id : Z) : bool :=
  ((CL.ps_at ps ENDS && CL.ps_keeps ps CSAVED)
   || existsb (fun rt : nat * nat * nat * Z => let '(j, i', _, pc) := rt in
                 (Nat.eqb i' i && Z.eqb pc id && Z.eqb (SR.ps_pc ps) id &&
                  match nth_error CPS i, nth_error CPS j with
                  | Some c, Some cj =>
                      match find (fun e : Z * (Z * list nat * option Z) => Z.eqb (fst e) pc) INL with
                      | Some (_, (len, hv, a0)) => inl_chk c ps cj len hv a0
                      | None => match find (fun e : Z * (Z * option (Z * Z)) => Z.eqb (fst e) pc) CALLEES with
                                | Some (_, (SCRc, IMGc)) => call_chk c ps cj SCRc IMGc
                                | None => false
                                end
                      end
                  | _, _ => false
                  end)%bool) RETS)%bool.
Definition vf_chk : bool :=
  (entry_chk && CC.cps_all CPS cut_chk && CC.others_all CPS TAGS leaf_chk && Z.leb 0 SCR && Z.ltb SCR (2 ^ 32))%bool.

Lemma reglist_len : forall ps, length (CA.ps_reglist ps) = 32%nat.
Proof. intros ps. unfold CA.ps_reglist. cbn [length]. rewrite length_map, length_seq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma call_leaf_ok : forall (E0 : env) (M0 : word -> option byte) (model0 : Model) (K : ShapeAlg.TSet) (sp0 : Z) (F0x XF : list SGP.region)
                            i c ps j cj SCRc IMGc,
  (SCR <> 0 -> F0x = (EVar 2, - SCR, ELit SCR) :: XF) ->
  m_halted model0 = None -> m_vm_lazy model0 = [] ->
  bv_unsigned (ev E0 2) = sp0 -> sp0 mod 16 = 0 -> 140735332483072 + SCR <= sp0 <= 140737488355328 -> L5.defined M0 (sp0 - SCR) SCR ->
  nth_error CPS j = Some cj -> call_chk c ps cj SCRc IMGc = true -> vf_contract segs (SR.ps_pc ps) SCRc IMGc ->
  CL.sub_F NF E0 F0x c -> (NF <= CC.cp_nx c)%nat ->
  CC.leaf_ok segs CPS (CL.pure_amb NF E0 M0 model0 F0x) K FrmInv.fp_ok i c ps.
Proof.
  intros E0 M0 model0 K sp0 F0x XF i c ps j cj SCRc IMGc HF0 Hh Hl U2 Hal Hrange Hdef Hcj Hchk Hcallee Hsub Hnf
         fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  unfold call_chk in Hchk.
  set (regs := CA.ps_reglist ps) in *. set (nx := Nat.max (CC.cp_nx c) (CA.ps_bound ps)) in *.
  destruct (nth 1 regs (ELit 1)) as [ra| | | | | | |] eqn:Era; try discriminate.
  destruct (split_lit (nth 2 regs (ELit 0))) as [spb spo] eqn:Esp.
  do 18 (apply andb_prop in Hchk as [Hchk ?X]). rename Hchk into Xall.
  apply Z.eqb_eq in X16. apply Z.leb_le in X15. apply Z.ltb_lt in X14. apply Z.eqb_eq in X13. apply AX2S.expr_eqb_eq in X12. subst spb.
  apply Z.leb_le in X11. apply Z.leb_le in X10. apply Z.eqb_eq in X9. apply Z.ltb_lt in X8.
  apply regs_eqb_eq in X7. apply kn_eqb_eq in X6. apply Nat.eqb_eq in X5. apply AX2S.expr_eqb_eq in X4.
  assert (Hnxc : (CC.cp_nx c <= nx)%nat) by (unfold nx; lia).
  assert (EF0 : F0x = (EVar 2, - SCR, ELit SCR) :: XF) by (apply HF0; lia).
  pose proof (leaf_regs_ok segs c ps E' R' M M' Xall HLF) as HR. fold regs in HR.
  (* [comment removed for export] *)
  assert (HA' : CL.pure_amb NF E0 M0 model0 F0x 0%nat E' M' model).
  { eapply CL.pure_amb_step with (c := c); [exact Hsub | exact Hnf | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
  destruct HA' as (-> & HagE & Hfr & Hgr).
  assert (E2v : forall Ex, env_agree NF E0 Ex -> bv_unsigned (ev Ex 2) = sp0).
  { intros Ex [Hv _]. rewrite <- (Hv 2%nat) by (unfold NF; lia). exact U2. }
  set (spc := sp0 + spo).
  (* [comment removed for export] *)
  assert (Hra : getr R' 1%bv = Z_to_bv 64 ra).
  { rewrite (HR 1%bv). unfold sr_get. change (bv_eqb (1%bv : bv 5) 0) with false. cbv iota. change (ridx 1%bv) with 1%nat.
    rewrite (nth_indep regs (ELit 0) (ELit 1)) by (unfold regs; rewrite reglist_len; lia). rewrite Era. reflexivity. }
  assert (Hspv : getr R' 2%bv = Z_to_bv 64 spc).
  { rewrite (HR 2%bv). unfold sr_get. change (bv_eqb (2%bv : bv 5) 0) with false. cbv iota. change (ridx 2%bv) with 2%nat.
    rewrite (APS.split_lit_denot E' _ _ _ Esp). cbn [edenot]. rewrite (E2v E' HagE). reflexivity. }
  assert (DEF' : L5.defined M' (spc - SCRc) SCRc).
  { intros k Hk. apply Hgr. replace (spc - SCRc + k) with (sp0 - SCR + (spc - SCRc + k - (sp0 - SCR))) by lia. apply Hdef. unfold spc. lia. }
  (* [comment removed for export] *)
  eapply (Hcallee fx' R' M' model0 K spc Hh Hl HFP Hspv).
  - unfold spc. rewrite Z.add_mod by lia. rewrite Hal, X9. reflexivity.
  - unfold spc. lia.
  - exact DEF'.
  - unfold img_pre_of. destruct IMGc as [[lo hi]|]; [|exact I].
    unfold CA.has in X. apply existsb_exists in X as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
    exact (CC.lf_cells _ _ _ _ _ _ _ HLF _ HY).
  - rewrite Hra. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact X13.
  - intros fx2 R2 M2 HFP2 Hfr2 Hgr2 Hcs2.
    rewrite Hra, <- X16.
    set (E2 := APS.ext_list E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) APC.caller_saved)).
    pose proof (APS.ext_list_agree E' nx (map (fun r => getr R2 (Z_to_bv 5 (Z.of_nat r))) APC.caller_saved) : env_agree nx E' E2) as Hag2.
    assert (HagNF : env_agree NF E' E2) by (eapply CC.env_agree_le; [exact Hag2 | lia]).
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE | exact HagNF]).
    apply (HIH j cj fx2 E2 R2 M2 model0 Hcj).
    + (* [comment removed for export] *)
      split.
      * rewrite X7. apply CH.fresh_regs_ok; [| exact X2 | repeat constructor; lia].
        intros r Hn. destruct (bv_eqb r 0) eqn:Er0.
        { assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er0; apply Z.eqb_eq in Er0; exact Er0).
          unfold sr_get. change (bv_eqb (0%bv : bv 5) 0) with true. cbn [edenot]. apply getr_zero. }
        assert (Hr0 : r <> 0%bv) by (intros ->; unfold bv_eqb in Er0; rewrite Z.eqb_refl in Er0; discriminate).
        rewrite (Hcs2 r (csaved_partition r Hr0 Hn)). exact (HR r).
      * rewrite X6. unfold know_ok. apply Forall_cons.
        { cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite (E2v E2 HagE2). rewrite u64_of_Z by lia.
          split; [lia|]. intros k Hk. apply Hgr2. replace (sp0 + (spo - SCRc) + k) with (spc - SCRc + k) by (unfold spc; lia). apply DEF'. exact Hk. }
        assert (HK' : know_ok segs E' M' (SR.ps_cells ps)).
        { unfold know_ok. apply Forall_forall. intros Y HY. exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY). }
        assert (HKh : know_ok segs E' M2 (APC.kn_havoc (SR.ps_cells ps) (EVar 2) (spo - SCRc) (ELit SCRc))).
        { apply (APS.know_ok_havoc segs E' M' M2 _ _ _ _ HK'); [|exact Hgr2].
          intros x Hx. apply Hfr2. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite (E2v E' HagE) in Hx.
          rewrite u64_of_Z in Hx by lia. unfold spc. lia. }
        unfold know_ok in *. apply Forall_forall. intros Y HY.
        eapply SGP.kentry_ok_agree1; [exact Hag2 | exact (SGP.kn_vars_lt_In nx _ Y X1 HY) | exact (proj1 (Forall_forall _ _) HKh Y HY)].
    + (* [comment removed for export] *)
      split; [reflexivity|]. split; [exact HagE2|]. split.
      * intros a Ha. assert (Ha' : bv_unsigned a < sp0 - SCR \/ sp0 <= bv_unsigned a).
        { rewrite EF0 in Ha. apply Forall_inv in Ha. unfold estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U2 in Ha.
          rewrite u64_of_Z in Ha by lia. lia. }
        rewrite Hfr2 by (unfold spc; lia). apply Hfr. exact Ha.
      * eapply mem_grows_trans; [exact Hgr | exact Hgr2].
    + exact HFP2.
    + (* [comment removed for export] *)
      unfold CC.meas. rewrite X4. unfold APC.esub. rewrite mkAlu_denot, u_sub64. cbn [edenot].
      assert (Em : edenot E2 (CC.cp_meas c) = edenot E (CC.cp_meas c)).
      { rewrite <- (SR.edenot_agree_AP _ E' E2 _ (CC.env_agree_le _ _ _ _ Hag2 Hnxc) X0). symmetry. exact (SR.edenot_agree_AP _ E E' _ Hag X0). }
      rewrite Em. unfold CA.has in X3. apply existsb_exists in X3 as (Y & HY & Heq). apply APS.kentry_eqb_eq in Heq. subst Y.
      pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ HY) as HM. cbn [kentry_ok] in HM.
      rewrite <- (SR.edenot_agree_AP _ E E' _ Hag X0) in HM. unfold CC.MB in HM.
      rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition inl_sem (e : Z * (Z * list nat * option Z)) : Prop :=
  let '(pc, (len, hv, a0)) := e in
  match a0 with None => FPB.inl_step segs pc len hv | Some z => hv = [] /\ FPB.inl_step_a0 segs pc len z end.

Hypothesis SAFE : FrmInv.text_safe segs.
Hypothesis PLANS : forall i c, nth_error CPS i = Some c -> CC.plan_sound segs c.
Hypothesis TAGS_OK : CC.tags_chk CPS TAGS NF = true.
Hypothesis CHK : vf_chk = true.
Hypothesis RETS_OK : forall pc, In pc ENDS -> CL.is_ret_at segs pc.
Hypothesis INL_OK : forall e, In e INL -> inl_sem e.
Hypothesis CALLEES_OK : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> vf_contract segs pc SCRc IMGc.

Theorem vf_leaf_sound : forall (fx : FPState) R M model K sp,
  m_halted model = None -> m_vm_lazy model = [] -> FrmInv.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp -> sp mod 16 = 0 -> 140735332483072 + SCR <= sp <= 140737488355328 -> L5.defined M (sp - SCR) SCR -> img_pre M ->
  Hoare.ret_ok (getr R 1%bv) ->
  (forall (fx' : FPState) R' M', FrmInv.fp_ok fx' ->
      (forall a : word, ~ (sp - SCR <= bv_unsigned a < sp) -> M' a = M a) -> mem_grows M M' ->
      (forall x : reg, In (ridx x) CSAVED -> getr R' x = getr R x) ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (getr R 1%bv) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 entry) M (seg_rom segs)) model) K.
Proof.
  intros fx R M model K sp Hh Hl Hfx Hsp Hal Hrange Hdef Himg Hret HK.
  unfold vf_chk in CHK. do 4 (apply andb_prop in CHK as [CHK ?C]). rename CHK into Centry. apply Z.leb_le in C0. apply Z.ltb_lt in C.
  assert (HC0 : exists c0, nth_error CPS 0 = Some c0 /\ CC.cp_pc c0 = entry /\ CC.cp_regs c0 = sr_id /\ CC.cp_know c0 = KN0).
  { unfold entry_chk in Centry. destruct CPS as [|c0 CPSr]; [discriminate|]. exists c0.
    do 3 (apply andb_prop in Centry as [Centry ?D]).
    apply Z.eqb_eq in Centry. apply regs_eqb_eq in D1. apply kn_eqb_eq in D0. repeat split; assumption. }
  destruct HC0 as (c0 & ECPS & Centry' & D1 & D0). clear Centry. rename Centry' into Centry.
  set (E0 := EnvR R).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (apply (CL.EnvR_reg_u R 2%bv sp Hsp); lia).
  assert (F0v : forallb (SGP.region_vars_lt NF) F0 = true) by (unfold F0; destruct (Z.eqb SCR 0); reflexivity).
  set (Amb := CL.pure_amb NF E0 M model F0).
  assert (NFle : forall i c, nth_error CPS i = Some c -> (NF <= CC.cp_nx c)%nat).
  { intros i c Hc. pose proof (CC.cps_all_sound _ _ C2 i c Hc) as X. apply andb_prop in X as [X _]. apply Nat.leb_le. exact X. }
  assert (SUBF : forall i c, nth_error CPS i = Some c -> CL.sub_F NF E0 F0 c).
  { intros i c Hc. pose proof (CC.cps_all_sound _ _ C2 i c Hc) as X. apply andb_prop in X as [_ X]. unfold F_ok in X.
    destruct (CC.cp_F c) as [|[[b o] n] [|? ?]] eqn:EF; try discriminate.
    - apply CL.sub_F_nil. exact EF.
    - do 3 (apply andb_prop in X as [X ?Y]). apply negb_true_iff in X. apply AX2S.expr_eqb_eq in Y1, Y. apply Z.eqb_eq in Y0. subst b o n.
      assert (EF0 : F0 = [(EVar 2, - SCR, ELit SCR)]) by (unfold F0; rewrite X; reflexivity).
      intros E a Hag Ho. rewrite EF.
      pose proof (CL.outside_agree_F0 NF E0 F0 F0v E a Hag Ho) as Q. rewrite EF0 in Q. exact Q. }
  assert (FRAME : forall (M' : word -> option byte), (forall a : word, SGP.outside E0 F0 a -> M' a = M a) ->
                  forall a : word, ~ (sp - SCR <= bv_unsigned a < sp) -> M' a = M a).
  { intros M' Hfr a Ha. apply Hfr. unfold F0. destruct (Z.eqb SCR 0); [constructor|]. constructor; [|constructor].
    unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite u64_of_Z by lia. lia. }
  rewrite <- Centry.
  eapply (CC.cutcert_sound_tagged segs CPS TAGS NF Amb K FrmInv.fp_ok
            (fun fx1 fx2 R1 pc1 M1 R2 pc2 M2 H => FrmInv.msteps_fp_ok segs SAFE fx1 fx2 R1 _ M1 _ R2 _ M2 _ H) PLANS TAGS_OK)
    with (i := 0%nat) (c := c0) (E := E0).
  - intros i E M1 m1 H. eapply (CL.pure_amb_model NF E0 M model F0 i); eauto.
  - intros i c tags k ps j s Hc _ _ _. apply CL.pure_amb_goto; [exact (SUBF i c Hc) | exact (NFle i c Hc)].
  - intros i c tags k ps id Hc Htags Hps Htag.
    pose proof (CC.others_all_sound _ _ _ C1 i c tags k ps id Hc Htags Hps Htag) as X. unfold leaf_chk in X.
    apply orb_prop in X as [X|X].
    + (* [comment removed for export] *)
      apply andb_prop in X as [Xpc Xk].
      intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
      assert (HA' : Amb 0%nat E' M' m1).
      { eapply CL.pure_amb_step with (c := c); [exact (SUBF i c Hc) | exact (NFle i c Hc) | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl]. }
      destruct HA' as (-> & HagE & Hfr & Hgr).
      assert (Hcs : forall x : reg, In (ridx x) CSAVED -> getr R' x = getr R x).
      { intros x Hx. assert (Hx32 : (ridx x < 32)%nat) by (unfold CSAVED in Hx; cbn in Hx; intuition lia).
        rewrite (CL.ps_keeps_sound segs c ps E0 E' R' M1 M' CSAVED NF x HLF Xk HagE Hx Hx32).
        unfold E0. rewrite (EnvR_ev R (ridx x) Hx32). rewrite CC.reg_of_ridx. reflexivity. }
      assert (Hra : getr R' 1%bv = getr R 1%bv) by (apply Hcs; left; reflexivity).
      eapply CL.ret_cps; [exact (RETS_OK _ (CL.ps_at_sound _ _ Xpc)) | exact Hh | exact Hl | rewrite Hra; exact Hret |].
      rewrite Hra. apply HK; [exact HFP | exact (FRAME M' Hfr) | exact Hgr | exact Hcs].
    + (* [comment removed for export] *)
      apply existsb_exists in X as ([[[j i'] k'] pc] & Hin & X). do 3 (apply andb_prop in X as [X ?Y]).
      apply Nat.eqb_eq in X. apply Z.eqb_eq in Y1, Y0. subst i' pc. rewrite Hc in Y.
      destruct (nth_error CPS j) as [cj|] eqn:Hcj; [|discriminate].
      destruct (find (fun e : Z * (Z * list nat * option Z) => Z.eqb (fst e) id) INL) as [[pc' [[len hv] a0]]|] eqn:Hf.
      2:{ (* [comment removed for export] *)
          destruct (find (fun e : Z * (Z * option (Z * Z)) => Z.eqb (fst e) id) CALLEES) as [[pc' [SCRc IMGc]]|] eqn:Hg; [|discriminate].
          apply find_some in Hg as [HinC Hpc']. cbn [fst] in Hpc'. apply Z.eqb_eq in Hpc'. subst pc'.
          pose proof (CALLEES_OK _ _ _ HinC) as Hct. rewrite <- Y0 in Hct.
          refine (call_leaf_ok E0 M model K sp F0 [] i c ps j cj SCRc IMGc _ Hh Hl U2 Hal Hrange Hdef Hcj Y Hct (SUBF i c Hc) (NFle i c Hc)).
          intros NZ. unfold F0. destruct (Z.eqb_spec SCR 0); [contradiction | reflexivity]. }
      apply find_some in Hf as [HinI Hpc']. cbn [fst] in Hpc'. apply Z.eqb_eq in Hpc'. subst pc'.
      pose proof (INL_OK _ HinI) as Hsem. cbn in Hsem. rewrite <- Y0 in Hsem.
      destruct a0 as [z|].
      * destruct Hsem as [-> Hst].
        exact (inl_leaf_ok_a0 segs CPS NF E0 M model F0 K Hh Hl SAFE i c ps j cj len z Hcj Y (SUBF i c Hc) (NFle i c Hc) Hst).
      * exact (inl_leaf_ok segs CPS NF E0 M model F0 K Hh Hl SAFE i c ps j cj len hv Hcj Y (SUBF i c Hc) (NFle i c Hc) Hsem).
  - exact ECPS.
  - (* [comment removed for export] *)
    split; [rewrite D1; apply EnvR_regs_ok|]. rewrite D0. unfold KN0.
    assert (KR : kentry_ok segs E0 M (KRange (EVar 2) (140735332483072 + SCR) 140737488355328)) by (cbn [kentry_ok edenot]; rewrite U2; lia).
    assert (KA : kentry_ok segs E0 M (KAlign (EVar 2) 16)) by (cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact Hal]).
    unfold know_ok. apply Forall_cons; [exact KR|]. apply Forall_cons; [exact KA|].
    apply Forall_app. split.
    { unfold img_pre, img_pre_of in Himg. destruct IMG as [[lo hi]|]; [|constructor]. apply Forall_cons; [|constructor]. cbn [kentry_ok].
      destruct Himg as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|]. exact I3. }
    destruct (Z.eqb_spec SCR 0) as [Z0|NZ]; [constructor|].
    apply Forall_cons; [|apply Forall_cons; [|constructor]]; cbn [kentry_ok]; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite U2; rewrite u64_of_Z by lia.
    + split; [lia|]. intros d m Hd Hm. replace (sp + - SCR + d) with (sp - SCR + d) by lia.
      apply (L5C.writable_of_defined segs M (sp - SCR) SCR Hdef); lia.
    + split; [lia|]. intros i Hi. replace (sp + - SCR + i) with (sp - SCR + i) by lia. apply Hdef. exact Hi.
  - split; [reflexivity|]. split; [apply CC.env_agree_refl|]. split; [reflexivity | apply mem_grows_refl].
  - exact Hfx.
  Unshelve. all: exact 0%nat.
Qed.

(* [comment removed for export] *)
Theorem vf_leaf_sound_pre : forall (entry0 : Z) (hv : list nat),
  entry = entry0 + 4 -> FPB.inl_step segs entry0 4 hv -> (forall x, In x hv -> ~ In x CSAVED) ->
  forall (fx : FPState) R M model K sp,
  m_halted model = None -> m_vm_lazy model = [] -> FrmInv.fp_ok fx ->
  getr R 2%bv = Z_to_bv 64 sp -> sp mod 16 = 0 -> 140735332483072 + SCR <= sp <= 140737488355328 -> L5.defined M (sp - SCR) SCR -> img_pre M ->
  Hoare.ret_ok (getr R 1%bv) ->
  (forall (fx' : FPState) R' M', FrmInv.fp_ok fx' ->
      (forall a : word, ~ (sp - SCR <= bv_unsigned a < sp) -> M' a = M a) -> mem_grows M M' ->
      (forall x : reg, In (ridx x) CSAVED -> getr R' x = getr R x) ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (getr R 1%bv) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 entry0) M (seg_rom segs)) model) K.
Proof.
  intros entry0 hv He Hstep Hhv fx R M model K sp Hh Hl Hfx Hsp Hal Hrange Hdef Himg Hret HK.
  destruct (Hstep fx R M Hfx) as (fx1 & R1 & Hms & Hkeep).
  assert (KEEP : forall x : reg, In (ridx x) CSAVED -> getr R1 x = getr R x).
  { intros x Hx. apply Hkeep. intros X. exact (Hhv _ X Hx). }
  eapply L5.cps_of_msteps; [exact Hh | exact Hl | exact Hms |]. rewrite <- He.
  assert (R1ra : getr R1 1%bv = getr R 1%bv) by (apply KEEP; left; reflexivity).
  assert (R1sp : getr R1 2%bv = getr R 2%bv) by (apply KEEP; right; left; reflexivity).
  apply (vf_leaf_sound fx1 R1 M model K sp Hh Hl (FrmInv.msteps_fp_ok segs SAFE _ _ _ _ _ _ _ _ _ _ Hms Hfx)); try assumption.
  - rewrite R1sp. exact Hsp.
  - rewrite R1ra. exact Hret.
  - intros fx' R' M' F1 F2 F3 F4. rewrite R1ra. apply HK; [exact F1 | exact F2 | exact F3 |].
    intros x Hx. rewrite (F4 x Hx). exact (KEEP x Hx).
Qed.

End Leaf.
End CVF.
