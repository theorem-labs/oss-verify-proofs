From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjXform ObjUnbase.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6 Require Import S_pg S_pgB pgB_st.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import S_sc sc.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import PcJoin.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddrU.

Lemma check_pgB : check_cfg segsU FUEL_pgB cutpcs_pgB NF cuts_pgB exits_pgB = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_pgB_strict : existsb ss_lenient cuts_pgB = false.
Proof. vm_compute. reflexivity. Qed.

Ltac find_idx F l := lazymatch l with | F :: _ => constr:(O) | _ :: ?t => let i := find_idx F t in constr:(S i) end.
Ltac have_fact HF F H :=
  lazymatch type of HF with Forall _ ?l =>
    let l' := eval vm_compute in l in let F' := eval vm_compute in F in let i := find_idx F' l' in
    pose proof (Forall_pick _ _ i F HF ltac:(vm_compute; reflexivity)) as H end.

(* Computed side conditions. *)
Lemma X4_xf : apply_xforms E4 (sc_xf E4) = Some X4. Proof. vm_compute. reflexivity. Qed.
Lemma X3a_xf : apply_xforms E3a (sc_xf E3a) = Some X3a. Proof. vm_compute. reflexivity. Qed.
Lemma X3b_xf : apply_xforms E3b (sc_xf E3b) = Some X3b. Proof. vm_compute. reflexivity. Qed.
Lemma E5_xf : apply_xforms E5 r2_xf = Some E5s. Proof. vm_compute. reflexivity. Qed.
Lemma E5_ub : unbase_obj_at E5s 1 (-2288) = Some E5u. Proof. vm_compute. reflexivity. Qed.
Lemma X5_below : forallb (sprop_below (ss_next E5u)) (n5 :: ss_facts E5u) = true. Proof. vm_compute. reflexivity. Qed.
Lemma fr4 : entails_fr X4 Pre_sc_U s4 = Some R4. Proof. vm_compute. reflexivity. Qed.
Lemma fr3a : entails_fr X3a Pre_sc_U s3a = Some R3a. Proof. vm_compute. reflexivity. Qed.
Lemma fr3b : entails_fr X3b Pre_sc_U s3b = Some R3b. Proof. vm_compute. reflexivity. Qed.
Lemma fr5 : entails_fr X5 Pre_r2U s5 = Some R5. Proof. vm_compute. reflexivity. Qed.
Lemma chk4 : call_check X4 Pre_sc_U s4 R4 Posts_sc_U = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk3a : call_check X3a Pre_sc_U s3a R3a Posts_sc_U = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk3b : call_check X3b Pre_sc_U s3b R3b Posts_sc_U = true. Proof. vm_compute. reflexivity. Qed.
Lemma chk5 : call_check X5 Pre_r2U s5 R5 Posts_r2U = true. Proof. vm_compute. reflexivity. Qed.

(* What a summarised call needs of its call state, decided by computation. *)
Definition call_side (C : sstate) (s : wsub) (R : list sobj) (P : sstate) : bool :=
  Pos.leb NF (ss_next C) && forallb (sprop_below (ss_next C)) (ss_facts C) &&
  (let T := import_post s NF P (ss_next C) R in forallb (sprop_below (ss_next T)) (ss_facts T ++ ss_facts C)).
Lemma side4 : call_side X4 s4 R4 P_sc_U = true. Proof. vm_compute. reflexivity. Qed.
Lemma side3a : call_side X3a s3a R3a P_sc_U = true. Proof. vm_compute. reflexivity. Qed.
Lemma side3b : call_side X3b s3b R3b P_sc_U = true. Proof. vm_compute. reflexivity. Qed.
Lemma side5 : call_side X5 s5 R5 P_r2U = true. Proof. vm_compute. reflexivity. Qed.

Lemma call_side_split : forall C s R P, call_side C s R P = true ->
  Pos.le NF (ss_next C) /\ forallb (sprop_below (ss_next C)) (ss_facts C) = true /\
  (let T := import_post s NF P (ss_next C) R in forallb (sprop_below (ss_next T)) (ss_facts T ++ ss_facts C) = true).
Proof.
  intros C s R P H. unfold call_side in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [apply Pos.leb_le; exact H1|]. split; assumption.
Qed.

Lemma SP_lift : forall K rho S S' w,
  (forall w', smatch segsU rho S w' -> smatch segsU rho S' w') -> SP segsU K S rho w -> SP segsU K S' rho w.
Proof. intros K rho S S' w H [Hsm Hk]. split; [apply H; exact Hsm | exact Hk]. Qed.

Lemma facts_transport : forall n rho rho' F,
  agree_below n rho rho' -> forallb (sprop_below n) F = true -> Forall (holds rho) F -> Forall (holds rho') F.
Proof.
  intros n rho rho' F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n rho rho' p Hag (proj1 (forallb_forall _ _) Hb p Hp))).
  exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Lemma n5_holds : forall rho, Forall (holds rho) (ss_facts E5u) -> holds rho n5.
Proof.
  intros rho HF.
  have_fact HF (SPBranch BC_NE PGD.pN (SLit 3)) H1. have_fact HF (SPNot (SPBranch BC_EQ PGD.pN (SLit 4))) H2.
  have_fact HF (SPUle (SLit 3) PGD.pN) H3. clear HF. unfold n5 in *. zfacts; lia.
Qed.

Definition RT : list sstate := RT3 ++ RT4 ++ RT5.
Lemma RT_fin : forallb (fun S => match apply_xforms S (fin_xf S) with
                                  | Some F => entails F P_ok_U (infer_sub NF F P_ok_U) && wsub_id_below (infer_sub NF F P_ok_U) NF
                                  | None => false end) RT = true.
Proof. vm_compute. reflexivity. Qed.

Section Safe.
Variable ok : world -> Prop.
Variable K : list event -> Model -> Prop.
Variable rho0 : valuation.
Hypothesis Hok : ok_frame segsU ok K.
Let Gp : valuation -> Prop := fun r => agree_below NF rho0 r.
Let Qs : assn := fun w => SPfam segsU K Gp cuts_pgB w \/ LQ segsU K NF rho0 Posts_pg_U w.

Lemma call1_ok : forall Pre P C s R rho,
  (forall rho1, triple segsU ok (SP segsU K Pre rho1) (LQ segsU K (ss_next Pre) rho1 [mkLeaf P RsSymJump])) ->
  ss_next Pre = NF ->
  entails_fr C Pre s = Some R -> call_check C Pre s R [mkLeaf P RsSymJump] = true -> call_side C s R P = true ->
  In (post_cut C s R P) cuts_pgB -> Gp rho ->
  triple segsU ok (SP segsU K C rho) Qs.
Proof.
  intros Pre P C s R rho Hsum Hnx He Hchk Hside Hin Hg.
  destruct (call_side_split C s R P Hside) as (Hle & Hb & HbT).
  apply triple_facts. intros HF.
  apply (call_sound_P segsU (fun _ => True) ok K K C Pre s R [mkLeaf P RsSymJump] Qs rho He Hchk).
  - intros rho1 _. apply Hsum.
  - intros ms. exact I.
  - intros L rho' HinL Hag.
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hsp. left.
    pose proof (facts_transport _ _ _ _ Hag Hb HF) as HFC.
    assert (Hg' : Gp rho') by (unfold Gp; eapply agree_below_trans; [exact Hg | eapply agree_below_le; [exact Hle | exact Hag]]).
    destruct HinL as [<-|[]]; cbn [lf_state] in Hsp. rewrite Hnx in Hsp.
    exists (post_cut C s R P), rho'. split; [exact Hin|]. split; [exact Hg'|].
    unfold post_cut. apply SP_refacts; [exact Hsp | exact HbT |].
    intros HFT. apply Forall_app. split; [exact HFT | exact HFC].
Qed.

Lemma sc_ok : forall rho1, triple segsU ok (SP segsU K Pre_sc_U rho1) (LQ segsU K (ss_next Pre_sc_U) rho1 [mkLeaf P_sc_U RsSymJump]).
Proof. intros rho1. exact (scale2d_sum_U ok K rho1 Hok). Qed.
Lemma r2_ok : forall rho1, triple segsU ok (SP segsU K Pre_r2U rho1) (LQ segsU K (ss_next Pre_r2U) rho1 [mkLeaf P_r2U RsSymJump]).
Proof. intros rho1. exact (r2_sum ok K rho1 Hok). Qed.

Lemma exits_ok : forall E rho, In E exits_pgB -> Gp rho -> triple segsU ok (SP segsU K E rho) Qs.
Proof.
  intros E rho HE Hg. unfold exits_pgB in HE. rewrite in_app_iff in HE.
  destruct HE as [[<-|[<-|[<-|[<-|[]]]]]|HE].
  - apply (triple_xforms segsU ok K (sc_xf E4) rho E4 X4 Qs X4_xf).
    apply (call1_ok Pre_sc_U P_sc_U X4 s4 R4 rho sc_ok eq_refl fr4 chk4 side4); [in_nth 1 | exact Hg].
  - apply (triple_xforms segsU ok K (sc_xf E3a) rho E3a X3a Qs X3a_xf).
    apply (call1_ok Pre_sc_U P_sc_U X3a s3a R3a rho sc_ok eq_refl fr3a chk3a side3a); [in_nth 2 | exact Hg].
  - apply (triple_xforms segsU ok K (sc_xf E3b) rho E3b X3b Qs X3b_xf).
    apply (call1_ok Pre_sc_U P_sc_U X3b s3b R3b rho sc_ok eq_refl fr3b chk3b side3b); [in_nth 3 | exact Hg].
  - apply (triple_xforms segsU ok K r2_xf rho E5 E5s Qs E5_xf).
    eapply triple_conseq; [| intros w Hw; exact Hw |].
    { intros w Hw. revert Hw. apply SP_lift. intros w' Hsm. eapply smatch_unbase; [exact E5_ub | exact Hsm]. }
    apply triple_facts. intros HF.
    eapply triple_conseq; [| intros w Hw; exact Hw |].
    { intros w Hw. change X5 with (with_facts E5u (n5 :: ss_facts E5u)) in *.
      apply SP_refacts; [exact Hw | exact X5_below |]. intros HF'. constructor; [apply n5_holds; exact HF' | exact HF']. }
    apply (call1_ok Pre_r2U P_r2U X5 s5 R5 rho r2_ok eq_refl fr5 chk5 side5); [in_nth 4 | exact Hg].
  - pose proof (proj1 (forallb_forall _ _) RT_fin E HE) as H.
    revert H. case_eq (apply_xforms E (fin_xf E)); [intros F Hx H | intros _ H; discriminate].
    apply andb_prop in H as [He Hid].
    apply (triple_xforms segsU ok K (fin_xf E) rho E F Qs Hx).
    apply (triple_entails segsU ok K F P_ok_U _ rho Qs He).
    apply exit_post; [in_nth 1 |]. eapply agree_below_trans; [exact Hg | apply rho_sub_agree; exact Hid].
Qed.
End Safe.

Theorem pgB_sum_U : pgB_sum_stmt_U.
Proof.
  intros ok K rho0 rho Hok Hg.
  apply (cfg_sound segsU FUEL_pgB cutpcs_pgB NF cuts_pgB exits_pgB
           (fun rho' => agree_below NF rho0 rho') ok K (LQ segsU K NF rho0 Posts_pg_U) Hok).
  - rewrite cuts_pgB_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_pgB.
  - intros E rhoE HinE HagE. exact (exits_ok ok K rho0 Hok E rhoE HinE HagE).
  - left; reflexivity.
  - exact Hg.
Qed.

(* Existence: same graph, measured by rank alone; returns last. *)
Definition z0 : sv := SLit 0.
Definition vcuts_pgB : list vnode :=
  [mkVN B_U 250 z0; mkVN T4 230 z0; mkVN T3a 230 z0; mkVN T3b 230 z0; mkVN T5 230 z0; mkVN G3 245 z0;
   mkVN GA 220 z0; mkVN GB 220 z0; mkVN CA 210 z0; mkVN CB 210 z0].
Definition vexits_pgB : list vnode :=
  [mkVN E4 240 z0; mkVN E3a 240 z0; mkVN E3b 240 z0; mkVN E5 240 z0] ++ map (fun S => mkVN S 1 vTop) RT.

Lemma echeck_pgB : check_ecfgI segsU FUEL_pgB cutpcs_pgB NF vcuts_pgB vexits_pgB = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma vmeasI_z0 : forall S r rho, vmeasI (mkVN S r z0) rho = 2 ^ 64 * 256 + r.
Proof. intros. unfold vmeasI, z0. cbn [vn_var vn_rank eval]. rewrite lit_unsigned. rewrite Z.mod_0_l by lia. lia. Qed.

Lemma vmeasI_top : forall S r rho, vmeasI (mkVN S r vTop) rho = 256 + r.
Proof. intros. unfold vmeasI, vTop. cbn [vn_var vn_rank eval]. rewrite lit_unsigned. rewrite Z.mod_small by lia. lia. Qed.

Section Ex.
Variable K : list event -> Model -> Prop.
Variable rho0 : valuation.
Hypothesis R2X : r2_sum_ex_stmt_U.
Let Gp : valuation -> Prop := fun r => agree_below NF rho0 r.
Let Qe (b : Z) : world -> Prop :=
  fun w => SPfamE segsU K (map (to_enodeI Gp) vcuts_pgB) b w \/ LQ segsU K NF rho0 Posts_pg_U w.

Lemma call1_ex : forall Pre P C s R rho rT b,
  (forall rho1, etriple segsU (SP segsU K Pre rho1) (LQ segsU K (ss_next Pre) rho1 [mkLeaf P RsSymJump])) ->
  ss_next Pre = NF ->
  entails_fr C Pre s = Some R -> call_check C Pre s R [mkLeaf P RsSymJump] = true -> call_side C s R P = true ->
  In (mkVN (post_cut C s R P) rT z0) vcuts_pgB -> 0 <= rT -> 2 ^ 64 * 256 + rT < b -> Gp rho ->
  etriple segsU (SP segsU K C rho) (Qe b).
Proof.
  intros Pre P C s R rho rT b Hsum Hnx He Hchk Hside Hin Hr Hb' Hg.
  destruct (call_side_split C s R P Hside) as (Hle & Hb & HbT).
  apply etriple_facts. intros HF.
  apply (call_complete_P segsU (fun _ => True) K K C Pre s R [mkLeaf P RsSymJump] (Qe b) rho He Hchk).
  - intros rho1 _. apply Hsum.
  - intros ms. exact I.
  - intros L rho' HinL Hag w Hsp. exists w. split; [apply wsteps_refl|]. left.
    pose proof (facts_transport _ _ _ _ Hag Hb HF) as HFC.
    assert (Hg' : Gp rho') by (unfold Gp; eapply agree_below_trans; [exact Hg | eapply agree_below_le; [exact Hle | exact Hag]]).
    destruct HinL as [<-|[]]; cbn [lf_state] in Hsp. rewrite Hnx in Hsp.
    exists (to_enodeI Gp (mkVN (post_cut C s R P) rT z0)), rho'.
    split; [apply in_map; exact Hin|]. split; [exact Hg'|]. split.
    + change (SP segsU K (post_cut C s R P) rho' w).
      unfold post_cut. apply SP_refacts; [exact Hsp | exact HbT |].
      intros HFT. apply Forall_app. split; [exact HFT | exact HFC].
    + change (0 <= vmeasI (mkVN (post_cut C s R P) rT z0) rho' /\ vmeasI (mkVN (post_cut C s R P) rT z0) rho' < b).
      rewrite vmeasI_z0. lia.
Qed.

Lemma sc_ex : forall rho1, etriple segsU (SP segsU K Pre_sc_U rho1) (LQ segsU K (ss_next Pre_sc_U) rho1 [mkLeaf P_sc_U RsSymJump]).
Proof. intros rho1. exact (scale2d_sum_ex_U K rho1). Qed.
Lemma r2_ex : forall rho1, etriple segsU (SP segsU K Pre_r2U rho1) (LQ segsU K (ss_next Pre_r2U) rho1 [mkLeaf P_r2U RsSymJump]).
Proof. intros rho1. exact (R2X K rho1). Qed.

Lemma exits_ex : forall E rho, In E vexits_pgB -> Gp rho ->
  etriple segsU (SP segsU K (vn_state E) rho) (Qe (vmeasI E rho)).
Proof.
  intros E rho HE Hg. unfold vexits_pgB in HE. rewrite in_app_iff in HE.
  destruct HE as [[<-|[<-|[<-|[<-|[]]]]]|HE].
  - cbn [vn_state]. rewrite vmeasI_z0.
    apply (etriple_xforms segsU K (sc_xf E4) rho E4 X4 _ X4_xf).
    apply (call1_ex Pre_sc_U P_sc_U X4 s4 R4 rho 230 _ sc_ex eq_refl fr4 chk4 side4); [in_nth 1 | lia | lia | exact Hg].
  - cbn [vn_state]. rewrite vmeasI_z0.
    apply (etriple_xforms segsU K (sc_xf E3a) rho E3a X3a _ X3a_xf).
    apply (call1_ex Pre_sc_U P_sc_U X3a s3a R3a rho 230 _ sc_ex eq_refl fr3a chk3a side3a); [in_nth 2 | lia | lia | exact Hg].
  - cbn [vn_state]. rewrite vmeasI_z0.
    apply (etriple_xforms segsU K (sc_xf E3b) rho E3b X3b _ X3b_xf).
    apply (call1_ex Pre_sc_U P_sc_U X3b s3b R3b rho 230 _ sc_ex eq_refl fr3b chk3b side3b); [in_nth 3 | lia | lia | exact Hg].
  - cbn [vn_state]. rewrite vmeasI_z0.
    apply (etriple_xforms segsU K r2_xf rho E5 E5s _ E5_xf).
    eapply etriple_conseq; [| intros w Hw; exact Hw |].
    { intros w Hw. revert Hw. apply SP_lift. intros w' Hsm. eapply smatch_unbase; [exact E5_ub | exact Hsm]. }
    apply etriple_facts. intros HF.
    eapply etriple_conseq; [| intros w Hw; exact Hw |].
    { intros w Hw. change X5 with (with_facts E5u (n5 :: ss_facts E5u)) in *.
      apply SP_refacts; [exact Hw | exact X5_below |]. intros HF'. constructor; [apply n5_holds; exact HF' | exact HF']. }
    apply (call1_ex Pre_r2U P_r2U X5 s5 R5 rho 230 _ r2_ex eq_refl fr5 chk5 side5); [in_nth 4 | lia | lia | exact Hg].
  - apply in_map_iff in HE as (S & <- & HS). cbn [vn_state]. rewrite vmeasI_top.
    pose proof (proj1 (forallb_forall _ _) RT_fin S HS) as H.
    revert H. case_eq (apply_xforms S (fin_xf S)); [intros F Hx H | intros _ H; discriminate].
    apply andb_prop in H as [He Hid].
    apply (etriple_xforms segsU K (fin_xf S) rho S F _ Hx).
    apply (etriple_entails segsU K F P_ok_U _ rho _ He).
    pose proof (eexit_post_I0 segsU K NF rho0 vcuts_pgB Posts_pg_U (mkVN P_ok_U 1 vTop) ltac:(in_nth 1)
                  (rho_sub rho (infer_sub NF F P_ok_U))) as H.
    rewrite vmeasI_top in H. apply H.
    eapply agree_below_trans; [exact Hg | apply rho_sub_agree; exact Hid].
Qed.
End Ex.

Theorem pgB_sum_ex_U : r2_sum_ex_stmt_U -> pgB_sum_ex_stmt_U.
Proof.
  intros R2X K rho0 rho Hg.
  change B_U with (vn_state (mkVN B_U 250 z0)).
  apply (cfg_complete_autoI segsU FUEL_pgB cutpcs_pgB NF vcuts_pgB vexits_pgB
           (fun rho' => agree_below NF rho0 rho') K (LQ segsU K NF rho0 Posts_pg_U)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_pgB.
  - intros E rhoE HinE HgE. exact (exits_ex K rho0 R2X E rhoE HinE HgE).
  - left; reflexivity.
  - exact Hg.
Qed.
