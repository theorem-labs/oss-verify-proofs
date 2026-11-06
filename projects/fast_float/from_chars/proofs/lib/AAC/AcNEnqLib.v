(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChEnt FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_q3e.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require NqTail.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.AXG_gpf OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3.AXG_q1e OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_q3e OSSVerify.Proofs.fast_float.from_chars.lib.AAC.NqTail.AXG_qt.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcAst AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarveP AcMALlib AcPutN AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcOwnSet AcDenW AcConvA AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcNPopN AcNEnq.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarveP.AcStepsOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.AcRunApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPopN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNEnq.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import NqStepZ NqTail.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nq_front_wf_mono : forall S n n' rgs, (n <= n')%positive -> state_wf (nq_front S n rgs) = true -> state_wf (nq_front S n' rgs) = true.
Proof.
  intros S n n' rgs Hn H. unfold state_wf, nq_front in *. cbn [s_next s_regs s_rgs s_facts s_resv] in *.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  rewrite (regs_wf_n_mono n n' _ _ Hn H1). cbn [forallb rsv_wf]. rewrite !andb_true_r.
  apply forallb_forall. intros R HR. rewrite forallb_forall in H2. exact (rwf_mono n n' R Hn (H2 R HR)).
Qed.

(* [comment removed for export] *)
Definition qcell (pz : list Z) (x : Z) : Prop := z_ca pz - 128 <= x < z_ca pz - 96 \/ BQ pz <= x < BQ pz + 8192.
Definition qcell_b (pz : list Z) (x : Z) : bool :=
  ((Z.leb (z_ca pz - 128) x && Z.ltb x (z_ca pz - 96)) || (Z.leb (BQ pz) x && Z.ltb x (BQ pz + 8192)))%bool.
Lemma qcell_b_spec : forall pz x, qcell_b pz x = true <-> qcell pz x.
Proof. intros pz x. unfold qcell_b, qcell. rewrite orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt. tauto. Qed.

Lemma uE_ladd_z : forall E x y, 0 <= uE E x + uE E y < two64 -> uE E (ladd x y) = uE E x + uE E y.
Proof. intros E x y H. unfold uE in *. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. exact H. Qed.

(* [comment removed for export] *)
Lemma pden_qroom : forall E a szl, 0 <= z_qn (pden E a) + 1 < two64 -> 0 <= z_qb (pden E a) + uE E szl < two64 ->
  pden E (a_qstep a (q_step_room a szl)) = qz_room (pden E a) (uE E szl).
Proof.
  intros E a szl Hn Hb. unfold pden. cbn [a_qstep with_pri a_pri]. unfold q_step_room, qz_room. rewrite !map_set_nth. fold (pden E a).
  assert (En : uE E (p_qn a) = z_qn (pden E a)) by (symmetry; apply zn_pden).
  assert (Eb : uE E (p_qb a) = z_qb (pden E a)) by (symmetry; apply zn_pden).
  rewrite uE_laddc_z by (rewrite En; exact Hn). rewrite En. rewrite uE_ladd_z by (rewrite Eb; exact Hb). rewrite Eb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pden_qnew : forall E a szl, List.length (a_pri a) = PRI_LEN -> 0 <= z_j (pden E a) 24 + 1 < two64 -> 0 <= uE E szl + 8192 < two64 ->
  pden E (a_qstep a (q_step_new a szl)) = qz_new (pden E a) (uE E szl).
Proof.
  intros E a szl Hlen Hj Hs. unfold pden. cbn [a_qstep with_pri a_pri]. unfold q_step_new, qz_new, pri_step, pz_step, QCLS. rewrite !map_set_nth. fold (pden E a).
  assert (Ej : uE E (p_j a 24) = z_j (pden E a) 24) by (symmetry; apply zn_pden).
  rewrite (uE_laddc_z E szl 8192) by exact Hs. rewrite !uE_lc by lia. rewrite uE_laddc_z by (rewrite Ej; exact Hj). rewrite Ej. reflexivity.
Qed.

(* [comment removed for export] *)
Definition qncell (pz : list Z) (x : Z) : Prop :=
  ncell (z_ca pz) (z_sb pz) 24 32 x \/ z_ca pz - 128 <= x < z_ca pz - 96 \/ BN pz <= x < BN pz + 8192.
Definition qncell_b (pz : list Z) (x : Z) : bool :=
  (ncell_b (z_ca pz) (z_sb pz) 24 32 x || (Z.leb (z_ca pz - 128) x && Z.ltb x (z_ca pz - 96)) || (Z.leb (BN pz) x && Z.ltb x (BN pz + 8192)))%bool.
Lemma qncell_b_spec : forall pz x, qncell_b pz x = true <-> qncell pz x.
Proof. intros pz x. unfold qncell_b, qncell. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt, ncell_b_spec. tauto. Qed.

(* [comment removed for export] *)
Definition nq_room (S : sst) (a : ast) : bool := Z.leb 1 (fst (irange (s_facts S) (p_qn a))).
Definition nq_nodrain (S : sst) (a : ast) : bool :=
  Z.leb (Z.min (snd (irange (s_facts S) (p_qb a)) + snd (irange (s_facts S) (rget (s_regs S) (rk 14))) + (if nq_room S a then 0 else 8192))
               (snd (irange (s_facts S) (if nq_room S a then ladd (p_qb a) (rget (s_regs S) (rk 14)) else laddc (rget (s_regs S) (rk 14)) 8192))))
        (fst (irange (s_facts S) (rget (s_regs S) (rk 22)))).
Lemma forallb_l_and3 : forall {A} (p b : A -> bool) l, forallb_l (fun R => p R &&& b R &&& true) l = true -> forallb_l (fun R => p R &&& b R) l = true.
Proof. intros A p b l. induction l as [|x r IH]; [reflexivity|]. cbn [forallb_l]. destruct (p x); [|discriminate]. destruct (b x); [exact IH | discriminate]. Qed.

(* [comment removed for export] *)
Definition qdcell (pz : list Z) (x : Z) : Prop := qcell pz x \/ 924360 <= x < 924400 \/ (1 <= z_gn pz /\ BG pz <= x < BG pz + 8).
Definition qdcell_b (pz : list Z) (x : Z) : bool :=
  (qcell_b pz x || (Z.leb 924360 x && Z.ltb x 924400) || (Z.leb 1 (z_gn pz) && Z.leb (BG pz) x && Z.ltb x (BG pz + 8)))%bool.
Lemma qdcell_b_spec : forall pz x, qdcell_b pz x = true <-> qdcell pz x.
Proof. intros pz x. unfold qdcell_b, qdcell. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt, qcell_b_spec. tauto. Qed.
Lemma forallb_l_and3' : forall {A} (p b g : A -> bool) l, forallb_l (fun R => p R &&& b R &&& g R) l = true ->
  forallb_l (fun R => p R &&& b R) l = true /\ forallb_l (fun R => p R &&& g R) l = true.
Proof.
  intros A p b g l. induction l as [|x r IH]; [split; reflexivity|]. cbn [forallb_l]. destruct (p x); [|discriminate]. destruct (b x); [|discriminate].
  destruct (g x); [exact IH | discriminate].
Qed.
Lemma forallb_l_and1 : forall {A} (p b : A -> bool) l, forallb_l (fun R => p R &&& b R) l = true -> forallb_l p l = true.
Proof. intros A p b l. induction l as [|x r IH]; [reflexivity|]. cbn [forallb_l]. destruct (p x); [|discriminate]. destruct (b x); [exact IH | discriminate]. Qed.

(* [comment removed for export] *)
Lemma pden_qroom_drain : forall E a szl, List.length (a_pri a) = PRI_LEN -> 0 <= z_qn (pden E a) + 1 < two64 -> 0 <= z_qb (pden E a) + uE E szl < two64 ->
  0 <= z_gn (pden E a) + 1 < two64 -> 0 <= z_gb (pden E a) + (z_qb (pden E a) + uE E szl) < two64 ->
  pden E (a_qstep a (q_step_drain (q_step_room a szl) a (p_qj a) (ladd (p_qb a) szl))) = qz_drain (qz_room (pden E a) (uE E szl)).
Proof.
  intros E a szl Hlen Hn Hb Hg Hgb. pose proof (pden_qroom E a szl Hn Hb) as E0. unfold pden in E0 |- *. cbn [a_qstep with_pri a_pri] in E0 |- *.
  unfold q_step_drain. rewrite !map_set_nth. rewrite E0. fold (pden E a).
  assert (Hl : List.length (pden E a) = PRI_LEN) by (unfold pden; rewrite length_map; exact Hlen).
  unfold qz_drain. rewrite (qroom_gb _ _ Hl), (qroom_qb _ _ Hl), (qroom_qj _ _ Hl), (qroom_gn _ _ Hl).
  assert (En : uE E (p_gn a) = z_gn (pden E a)) by (symmetry; apply zn_pden).
  assert (Eg : uE E (p_gb a) = z_gb (pden E a)) by (symmetry; apply zn_pden).
  assert (Eb : uE E (p_qb a) = z_qb (pden E a)) by (symmetry; apply zn_pden).
  assert (Ej : uE E (p_qj a) = z_qj (pden E a)) by (symmetry; apply zn_pden).
  assert (Eq : uE E (ladd (p_qb a) szl) = z_qb (pden E a) + uE E szl) by (rewrite uE_ladd_z by (rewrite Eb; exact Hb); rewrite Eb; reflexivity).
  rewrite (uE_ladd_z E (p_gb a)) by (rewrite Eg, Eq; exact Hgb). rewrite Eg, Eq, Ej.
  rewrite uE_laddc_z by (rewrite En; exact Hg). rewrite En. rewrite !uE_lc by lia. reflexivity.
Qed.

Lemma kt2_cases : forall r, existsb (Pos.eqb (rkey r)) KT2k = true ->
  exists k : nat, In k [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat /\ r = Z_to_bv 5 (Z.of_nat k).
Proof.
  intros r Hr. apply existsb_exists in Hr as (key & Hkey & Hke). apply Pos.eqb_eq in Hke.
  unfold KT2k in Hkey. apply in_map_iff in Hkey as (z & Hz & Hin).
  assert (Hr : r = Z_to_bv 5 z) by (rewrite <- (rkey_reg r), Hke, <- Hz; exact (rkey_reg (Z_to_bv 5 z))).
  exists (Z.to_nat z). cbn [In] in Hin.
  repeat destruct Hin as [<-|Hin]; try destruct Hin; (split; [cbn [In]; repeat (first [left; reflexivity | right]) | exact Hr]).
Qed.

(* [comment removed for export] *)
Definition qndcell (pz : list Z) (x : Z) : Prop := qncell pz x \/ 924360 <= x < 924400 \/ (1 <= z_gn pz /\ BG pz <= x < BG pz + 8).
Definition qndcell_b (pz : list Z) (x : Z) : bool :=
  (qncell_b pz x || (Z.leb 924360 x && Z.ltb x 924400) || (Z.leb 1 (z_gn pz) && Z.leb (BG pz) x && Z.ltb x (BG pz + 8)))%bool.
Lemma qndcell_b_spec : forall pz x, qndcell_b pz x = true <-> qndcell pz x.
Proof. intros pz x. unfold qndcell_b, qndcell. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt, qncell_b_spec. tauto. Qed.

(* [comment removed for export] *)
Lemma pden_qnew_drain : forall E a szl, List.length (a_pri a) = PRI_LEN -> 0 <= z_j (pden E a) 24 + 1 < two64 -> 0 <= uE E szl + 8192 < two64 ->
  0 <= z_gn (pden E a) + 1 < two64 -> 0 <= z_gb (pden E a) + (uE E szl + 8192) < two64 ->
  pden E (a_qstep a (q_step_drain (q_step_new a szl) a (p_j a QCLS) (laddc szl 8192))) = qz_drain (qz_new (pden E a) (uE E szl)).
Proof.
  intros E a szl Hlen Hj Hs Hg Hgb. pose proof (pden_qnew E a szl Hlen Hj Hs) as E0. unfold pden in E0 |- *. cbn [a_qstep with_pri a_pri] in E0 |- *.
  unfold q_step_drain. rewrite !map_set_nth. rewrite E0. fold (pden E a).
  assert (Hl : List.length (pden E a) = PRI_LEN) by (unfold pden; rewrite length_map; exact Hlen).
  unfold qz_drain. rewrite (qnew_gb _ _ Hl), (qnew_qb _ _ Hl), (qnew_qj _ _ Hl), (qnew_gn _ _ Hl).
  assert (En : uE E (p_gn a) = z_gn (pden E a)) by (symmetry; apply zn_pden).
  assert (Eg : uE E (p_gb a) = z_gb (pden E a)) by (symmetry; apply zn_pden).
  assert (Ej : uE E (p_j a QCLS) = z_j (pden E a) 24) by (symmetry; apply zn_pden).
  assert (Eq : uE E (laddc szl 8192) = uE E szl + 8192) by (apply uE_laddc_z; exact Hs).
  rewrite (uE_ladd_z E (p_gb a)) by (rewrite Eg, Eq; exact Hgb). rewrite Eg, Eq, Ej.
  rewrite uE_laddc_z by (rewrite En; exact Hg). rewrite En. rewrite !uE_lc by lia. reflexivity.
Qed.
