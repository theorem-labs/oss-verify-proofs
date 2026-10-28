(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmFloatXSpecs_u5 PmFloatXTu_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncSinkBridges_u5 EncTail_u5 EncSinkBridgesU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_pr_xsrc_T_u5 Cut_pr_xsrc_u5.
Set Default Proof Mode "Classic".

Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PRXU.
Import PMES.
Module G := Cut_pr_xsrc_u5.
Module GT := Cut_pr_xsrc_T_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Definition RETPC : Z := 0x44b04.
Definition S2E : expr := EVar 32.
Definition F0W (w : Z) : list SGP.region := [(EVar 2, -w, ELit w)].
Definition F0 : list SGP.region := F0W 8592.

Lemma heap_ok3 : CH2.heap_chk3 GT.NF G.HDECL G.BLS G.CPS G.TAGS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition sink_j (f : CC.cutpoint -> SR.post_spec -> CC.cutpoint -> CA.blocks -> CA.blocks -> option CH2.cinfo) (i k j : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (match CH2.ret_of G.RETS i k with Some j' => Nat.eqb j' j | None => false end &&
   match nth_error G.CPS j with Some cj => isSome (f c ps cj (nth i G.BLS []) (nth j G.BLS [])) | None => false end)%bool.
Definition ret_cut (i k : nat) : nat :=
  match i, k with
  | 2%nat, _ => 14%nat
  | 3%nat, 0%nat => 15%nat
  | 3%nat, 1%nat => 16%nat
  | 3%nat, _ => 17%nat
  | 4%nat, 0%nat => 18%nat
  | 4%nat, _ => 19%nat
  | 5%nat, _ => 20%nat
  | 6%nat, _ => 21%nat
  | 7%nat, _ => 22%nat
  | 8%nat, _ => 23%nat
  | 9%nat, _ => 24%nat
  | 10%nat, _ => 25%nat
  | 11%nat, _ => 26%nat
  | 12%nat, _ => 27%nat
  | 13%nat, 0%nat => 28%nat
  | 13%nat, 1%nat => 29%nat
  | 13%nat, _ => 30%nat
  | 14%nat, _ => 31%nat
  | 15%nat, _ => 32%nat
  | 16%nat, _ => 33%nat
  | 17%nat, _ => 34%nat
  | 18%nat, _ => 35%nat
  | 19%nat, _ => 36%nat
  | 20%nat, _ => 37%nat
  | 21%nat, _ => 38%nat
  | 22%nat, _ => 39%nat
  | 26%nat, _ => 40%nat
  | 27%nat, _ => 41%nat
  | 30%nat, _ => 42%nat
  | 33%nat, _ => 43%nat
  | 35%nat, _ => 44%nat
  | 40%nat, _ => 45%nat
  | 41%nat, _ => 46%nat
  | _, _ => 0%nat
  end.
Definition is_tail (i : nat) : bool := match i with 28%nat | 29%nat | 37%nat | 38%nat | 42%nat => true | _ => false end.
Definition lo (i : nat) : Z :=
  match i with
  | 0%nat | 1%nat | 2%nat | 3%nat | 4%nat | 5%nat | 6%nat | 7%nat => 0
  | 8%nat | 14%nat | 15%nat | 16%nat | 17%nat | 18%nat | 19%nat | 20%nat | 21%nat | 22%nat | 37%nat | 38%nat | 39%nat => 1
  | 9%nat | 10%nat | 11%nat | 12%nat | 23%nat | 24%nat | 25%nat | 26%nat | 27%nat | 31%nat | 32%nat | 33%nat | 34%nat | 35%nat | 36%nat | 40%nat | 41%nat => 2
  | 13%nat | 43%nat | 44%nat | 45%nat | 46%nat => 3
  | 28%nat | 29%nat | 30%nat => 4
  | 42%nat => 5
  | _ => 1
  end.
Definition hi (i : nat) (n k kk r P : Z) : Z :=
  match i with
  | 5%nat => n - r
  | 6%nat => n + k - r
  | 7%nat => kk - r
  | 8%nat | 11%nat | 12%nat => n + 1 - r
  | 9%nat => 5 - r
  | 10%nat => 5 + n - r
  | 13%nat => P
  | 14%nat | 15%nat | 16%nat | 17%nat | 18%nat | 19%nat => 1
  | 20%nat => n - r + 1
  | 21%nat => n + k - r + 1
  | 22%nat => kk - r + 1
  | 23%nat | 26%nat | 27%nat => n + 2 - r
  | 24%nat => 6 - r
  | 25%nat => 6 + n - r
  | 28%nat | 29%nat | 30%nat => P + 1
  | 31%nat | 32%nat | 33%nat | 34%nat | 35%nat | 36%nat => 2
  | 37%nat | 38%nat => 25
  | 39%nat => kk + 1
  | 40%nat | 41%nat => n + 2
  | 42%nat => P + 2
  | 43%nat | 44%nat => 3
  | 45%nat | 46%nat => n + 3
  | _ => 0
  end.
Definition needs (i : nat) : nat :=
  match i with
  | 5%nat | 6%nat | 7%nat | 8%nat | 9%nat | 10%nat | 11%nat | 12%nat | 20%nat | 21%nat | 22%nat | 23%nat | 24%nat | 25%nat | 26%nat | 27%nat | 39%nat => 67%nat
  | 13%nat | 28%nat | 29%nat | 30%nat | 42%nat => 70%nat
  | _ => 0%nat
  end.
Definition facts_chk (i : nat) (cells : list kentry) : bool :=
  ((negb (Nat.eqb (needs i) 67) || APC.fact_ok cells (KRange (EVar 66) 1 400)) &&
   (negb (Nat.eqb (needs i) 70) || APC.fact_ok cells (KRange (EVar 69) 3 24)) &&
   (negb (Nat.eqb i 6 || Nat.eqb i 21) || (APC.fact_ok cells (KRange (APC.eadd (EVar 11) (EVar 12)) 1 17) && APC.fact_ok cells (KRange (EVar 12) 0 16))) &&
   (negb (Nat.eqb i 31) || APC.fact_ok cells (KRange (EVar 33) 0 3)) &&
   (negb (Nat.eqb i 7 || Nat.eqb i 22 || Nat.eqb i 39) || (APC.fact_ok cells (KRange (APC.esub (EVar 11) (EVar 33)) 1 20) && APC.fact_ok cells (KRange (EVar 33) 1 17))))%bool.
Definition g66 (s : CC.subst) (e : expr) : bool := expr_eqb (CC.slook s 66) e.
Definition g69 (s : CC.subst) (e : expr) : bool := expr_eqb (CC.slook s 69) e.
Definition RDEC : expr := APC.eaddz (EVar 66) (-1).
Definition goto_ok (i j : nat) (s : CC.subst) : bool :=
  match i, j with
  | 0%nat, 5%nat => g66 s (EVar 11)
  | 1%nat, 7%nat => g66 s (EVar 33)
  | 20%nat, 6%nat => g66 s (EVar 12)
  | 20%nat, 5%nat => g66 s RDEC
  | 21%nat, 6%nat => g66 s RDEC
  | 22%nat, 7%nat => g66 s RDEC
  | 23%nat, 8%nat => g66 s RDEC
  | 24%nat, 9%nat => g66 s RDEC
  | 25%nat, 10%nat => g66 s RDEC
  | 26%nat, 11%nat => g66 s RDEC
  | 27%nat, 12%nat => g66 s RDEC
  | 24%nat, 10%nat => g66 s (EVar 11)
  | 31%nat, 10%nat => g66 s (EVar 11)
  | 31%nat, 9%nat => g66 s (EVar 33)
  | 32%nat, 11%nat => g66 s (APC.eaddz (EVar 11) (-1))
  | 34%nat, 11%nat => g66 s (APC.eaddz (EVar 11) (-1))
  | 36%nat, 12%nat => g66 s (APC.eaddz (EVar 11) (-1))
  | 39%nat, 8%nat => g66 s (APC.esub (EVar 11) (EVar 33))
  | 43%nat, 13%nat => g69 s (ELit 3)
  | 44%nat, 13%nat => g69 s (ELit 3)
  | 45%nat, 13%nat => g69 s (APC.eaddz (EVar 11) 3)
  | 46%nat, 13%nat => g69 s (APC.eaddz (EVar 11) 3)
  | _, _ => false
  end.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  (SP.F_sub (CC.cp_F c) F0 && Nat.leb (needs i) (CC.cp_nx c) && facts_chk i cells) &&
  match t with
  | CC.TGoto j s => goto_ok i j s
  | CC.TOther pc =>
      if Z.eqb pc PML.PC_STR_PUSH_BACK then
        if is_tail i then
          (Z.eqb (SR.ps_pc ps) PML.PC_STR_PUSH_BACK && ETL.tail_base_chk GT.NF c ps && CL.ps_reg_is ps 10 (EVar 32) &&
           CL.ps_reg_is ps 11 (CA.ps_reg ps 11) && APC.fact_ok cells (KRange (CA.ps_reg ps 11) 0 255))%bool
        else
          (Z.eqb (SR.ps_pc ps) PML.PC_STR_PUSH_BACK && sink_j (ESBU.pushb_chk GT.NF G.HDECL S2E 0) i k (ret_cut i k) c ps &&
           Nat.leb (needs (ret_cut i k)) (needs i))%bool
      else (PB.exit_base_chk GT.NF RETPC c ps && match i with 23%nat | 25%nat => true | _ => false end)%bool
  end.

Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vm_compute. reflexivity. Qed.

Definition phase (i : nat) (E : env) (p : Z) : Prop :=
  lo i <= p <= hi i (uv E (EVar 11)) (uv E (EVar 12)) (uv E (EVar 33)) (uv E (EVar 66)) (uv E (EVar 69)).

Lemma uv_add_lit : forall E e z, uv E (EAlu Instr.ALU_ADD e (ELit z)) = (uv E e + z) mod 2 ^ 64.
Proof.
  intros. pose proof (PB.uv_eaddz E e z) as H. unfold APC.eaddz, PB.uv in H. rewrite AX2S.mkAlu_denot in H. unfold uv, PB.uv. cbn [edenot] in H |- *. exact H.
Qed.
Lemma uv_lit1 : forall E z, 0 <= z < 2 ^ 64 -> uv E (ELit z) = z.
Proof. intros. unfold uv, PB.uv. cbn [edenot]. apply u64_of_Z; lia. Qed.

Ltac ph_split n k :=
  lazymatch k with
  | O => idtac
  | S ?k' => destruct n as [|n]; [idtac | ph_split n k']
  end.
Lemma ph_kr : forall E (M : mem) cells e lo hi, know_ok RSEGS E M cells -> APC.fact_ok cells (KRange e lo hi) = true -> lo <= uv E e <= hi.
Proof. intros E M cells e lo hi HK HF. exact (PB.fact_ok' E M cells _ HK HF). Qed.
Lemma ph_uvr : forall E e, 0 <= uv E e < 2 ^ 64.
Proof. intros E e. exact (PB.uv_range E e). Qed.
Lemma ph_lit3 : forall E, PB.uv E (ELit 3) = 3.
Proof. intros E. exact (uv_lit1 E 3 ltac:(lia)). Qed.
Lemma ph_ag : forall b E E' v, env_agree b E E' -> (v < b)%nat -> uv E' (EVar v) = uv E (EVar v).
Proof. intros b E E' v H Hv. apply (PB.uv_agree b); [exact H |]. cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. exact Hv. Qed.
Lemma ph_o11 : forall s E, uv (CC.env_over GT.NF s E) (EVar 11) = uv E (EVar 11). Proof. reflexivity. Qed.
Lemma ph_o12 : forall s E, uv (CC.env_over GT.NF s E) (EVar 12) = uv E (EVar 12). Proof. reflexivity. Qed.
Lemma ph_o33 : forall s E, uv (CC.env_over GT.NF s E) (EVar 33) = uv E (EVar 33). Proof. reflexivity. Qed.
Lemma ph_o66 : forall s E, uv (CC.env_over GT.NF s E) (EVar 66) = uv E (CC.slook s 66). Proof. reflexivity. Qed.
Lemma ph_o69 : forall s E, uv (CC.env_over GT.NF s E) (EVar 69) = uv E (CC.slook s 69). Proof. reflexivity. Qed.
Ltac ph_facts HK :=
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end;
  repeat match goal with H : APC.fact_ok _ (KRange _ _ _) = true |- _ => apply (ph_kr _ _ _ _ _ _ HK) in H end.

Lemma goto_phase : forall i c kk ps j s E E' (M' : mem) p,
  CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j s) ->
  env_agree (CC.cp_nx c) E E' -> know_ok RSEGS E' M' (SR.ps_cells ps) -> 1 <= uv E (EVar 11) <= 21 ->
  phase i E p -> phase j (CC.env_over GT.NF s E') p.
Proof.
  intros i c kk ps j s E E' M' p IL Hag HK Hn Hph.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. cbn beta iota zeta in X.
  apply andb_prop in X as [XA XG]. apply andb_prop in XA as [XA XF]. apply andb_prop in XA as [_ XN]. apply Nat.leb_le in XN.
  destruct IL as (tags & Hc & _).
  assert (HNF : (48 <= CC.cp_nx c)%nat) by exact (G.NF_le i c Hc).
  pose proof (ph_ag _ _ _ 11 Hag ltac:(lia)) as U11. pose proof (ph_ag _ _ _ 12 Hag ltac:(lia)) as U12.
  pose proof (ph_ag _ _ _ 33 Hag ltac:(lia)) as U33.
  assert (A66 : (67 <= needs i)%nat -> uv E' (EVar 66) = uv E (EVar 66)) by (intros; apply ph_ag with (b := CC.cp_nx c); [exact Hag | lia]).
  assert (A69 : (70 <= needs i)%nat -> uv E' (EVar 69) = uv E (EVar 69)) by (intros; apply ph_ag with (b := CC.cp_nx c); [exact Hag | lia]).
  unfold phase in Hph |- *. rewrite ph_o11, ph_o12, ph_o33, ph_o66, ph_o69, U11, U12, U33.
  pose proof (ph_uvr E (EVar 11)). pose proof (ph_uvr E (EVar 12)). pose proof (ph_uvr E (EVar 33)).
  pose proof (ph_uvr E (EVar 66)). pose proof (ph_uvr E (EVar 69)).
  pose proof (ph_uvr E' (EVar 66)). pose proof (ph_uvr E' (EVar 69)).
  clear Hc tags XN HNF.
  ph_split i 47%nat; cbn [goto_ok] in XG; try discriminate XG.
  all: ph_split j 14%nat; cbn beta iota in XG; try discriminate XG.
  all: unfold g66, g69 in XG; apply expr_eqb_eq in XG; try rewrite XG.
  all: unfold facts_chk in XF; cbn [lo hi needs Nat.eqb negb orb andb] in Hph, XF, A66, A69 |- *.
  all: ph_facts HK.
  all: try specialize (A66 ltac:(lia)); try specialize (A69 ltac:(lia)).
  all: unfold RDEC, uv in *; rewrite ?PB.uv_eaddz, ?PB.uv_esub, ?PB.uv_eadd, ?ph_lit3 in *.
  all: rewrite ?U11, ?U12, ?U33 in *.
  all: repeat match goal with A : PB.uv ?x (EVar ?v) = PB.uv ?y (EVar ?v) |- _ => try rewrite A in *; clear A end.
  all: try change (2 ^ 64) with 18446744073709551616 in *.
  all: try lia.
  all: Z.div_mod_to_equations; lia.
Qed.

Lemma uv_eadd' : forall E a b, uv E (APC.eadd a b) = (uv E a + uv E b) mod 2 ^ 64.
Proof. exact PB.uv_eadd. Qed.

Ltac rm_close E' V F :=
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?]
  | H : APC.fact_ok _ (KRange _ _ _) = true |- _ => apply F in H
  end;
  repeat match goal with
  | H : context [uv E' (APC.eadd ?a ?b)] |- _ => rewrite (uv_eadd' E' a b) in H
  end;
  repeat match goal with
  | H : context [uv E' (EVar ?v)] |- _ => rewrite (V v ltac:(lia)) in H
  end;
  repeat match goal with
  | H : context [(?x + ?y) mod 2 ^ 64] |- _ => rewrite (Z.mod_small (x + y) (2 ^ 64)) in H by lia
  end.

Lemma rm_bound : forall i c kk ps t E E' (M' : mem) p,
  CH2.is_leaf G.CPS G.TAGS i c kk ps t ->
  env_agree (CC.cp_nx c) E E' -> know_ok RSEGS E' M' (SR.ps_cells ps) -> 1 <= uv E (EVar 11) <= 21 ->
  phase i E p -> lo i <= p <= 26.
Proof.
  intros i c kk ps t E E' M' p IL Hag HK N11 HP.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as Y0. unfold leaf_chk in Y0.
  apply andb_prop in Y0 as [YF _]. apply andb_prop in YF as [YF YC]. apply andb_prop in YF as [_ YN]. apply Nat.leb_le in YN.
  assert (NX : (48 <= CC.cp_nx c)%nat).
  { destruct IL as (? & Hc & _). pose proof (G.NF_le i c Hc) as HN. unfold GT.NF in HN. exact HN. }
  assert (V : forall v, (v < CC.cp_nx c)%nat -> uv E' (EVar v) = uv E (EVar v)).
  { intros v Hv. unfold uv. apply (PB.uv_agree (CC.cp_nx c) E E' (EVar v) Hag). cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. exact Hv. }
  assert (F : forall e a b, APC.fact_ok (SR.ps_cells ps) (KRange e a b) = true -> a <= uv E' e <= b).
  { intros e a b Hf. pose proof (PB.fact_ok' E' M' _ _ HK Hf) as H. cbn [kentry_ok] in H. fold (PB.uv E' e) in H. exact H. }
  pose proof (PB.uv_range E (EVar 12)) as R12. pose proof (PB.uv_range E (EVar 33)) as R33.
  pose proof (PB.uv_range E (EVar 66)) as R66. pose proof (PB.uv_range E (EVar 69)) as R69. fold uv in R12, R33, R66, R69.
  unfold phase in HP. unfold facts_chk in YC. clear IL.
  do 47 (destruct i as [|i]; [(cbn [lo hi needs Nat.eqb negb orb andb] in YC; cbn [lo hi needs] in YN; cbn [lo hi] in HP; cbn [lo]; rm_close E' V F; lia)|]).
  cbn [lo hi] in HP. lia.
Qed.

Lemma rm_lo_nonneg : forall i, 0 <= lo i.
Proof. intros i. do 47 (destruct i as [|i]; [(cbn; lia)|]). cbn. lia. Qed.

Lemma rm_lo_tail : forall i, is_tail i = true -> 1 <= lo i.
Proof. intros i H. do 43 (destruct i as [|i]; [(cbn in H; cbn; first [discriminate H | lia])|]). cbn in H. discriminate H. Qed.

Lemma ret_phase : forall i c kk ps E E' E2 (M' : mem) ci p,
  CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TOther PML.PC_STR_PUSH_BACK) -> is_tail i = false ->
  env_agree (CC.cp_nx c) E E' -> know_ok RSEGS E' M' (SR.ps_cells ps) ->
  env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat -> 1 <= uv E (EVar 11) <= 21 ->
  phase i E p -> phase (ret_cut i kk) E2 (p + 1).
Proof.
  intros i c kk ps E E' E2 M' ci p IL TL Hag HK Hag2 Hnx N11 HP.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as Y0. unfold leaf_chk in Y0.
  apply andb_prop in Y0 as [YF Y]. apply andb_prop in YF as [YF YC]. apply andb_prop in YF as [_ YN]. apply Nat.leb_le in YN.
  cbv beta iota zeta in Y. rewrite Z.eqb_refl, TL in Y. cbv beta iota in Y.
  apply andb_prop in Y as [Y _]. apply andb_prop in Y as [_ Y3]. unfold sink_j in Y3. apply andb_prop in Y3 as [Y3a _].
  assert (NX : (48 <= CC.cp_nx c)%nat).
  { destruct IL as (? & Hc & _). pose proof (G.NF_le i c Hc) as HN. unfold GT.NF in HN. exact HN. }
  assert (V : forall v, (v < CC.cp_nx c)%nat -> uv E' (EVar v) = uv E (EVar v)).
  { intros v Hv. unfold uv. apply (PB.uv_agree (CC.cp_nx c) E E' (EVar v) Hag). cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. exact Hv. }
  assert (V2 : forall v, (v < CC.cp_nx c)%nat -> uv E2 (EVar v) = uv E (EVar v)).
  { intros v Hv. unfold uv. rewrite (PB.uv_agree (CH2.ci_nx ci) E' E2 (EVar v) Hag2) by (cbn [APC.expr_vars_lt]; apply Nat.ltb_lt; lia).
    apply (PB.uv_agree (CC.cp_nx c) E E' (EVar v) Hag). cbn [APC.expr_vars_lt]. apply Nat.ltb_lt. exact Hv. }
  assert (F : forall e a b, APC.fact_ok (SR.ps_cells ps) (KRange e a b) = true -> a <= uv E' e <= b).
  { intros e a b Hf. pose proof (PB.fact_ok' E' M' _ _ HK Hf) as H. cbn [kentry_ok] in H. fold (PB.uv E' e) in H. exact H. }
  pose proof (PB.uv_range E (EVar 12)) as R12. pose proof (PB.uv_range E (EVar 33)) as R33.
  pose proof (PB.uv_range E (EVar 66)) as R66. pose proof (PB.uv_range E (EVar 69)) as R69. fold uv in R12, R33, R66, R69.
  unfold phase in HP |- *. unfold facts_chk in YC. clear IL TL.
  do 47 (destruct i as [|i]; [(destruct kk as [|[|kk]]; vm_compute in Y3a;
    first [ discriminate Y3a
          | (cbn [lo hi needs Nat.eqb negb orb andb] in YC; cbn [lo hi needs] in YN; cbn [lo hi] in HP; cbn [lo hi ret_cut];
             rm_close E' V F;
             repeat match goal with |- context [uv E2 (EVar ?v)] => rewrite (V2 v ltac:(lia)) end;
             lia) ])|]).
  vm_compute in Y3a. discriminate Y3a.
Qed.

Lemma push_room : forall i c kk ps E E' (M' : mem) p,
  CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TOther PML.PC_STR_PUSH_BACK) ->
  env_agree (CC.cp_nx c) E E' -> know_ok RSEGS E' M' (SR.ps_cells ps) -> 1 <= uv E (EVar 11) <= 21 ->
  phase i E p -> 0 <= p <= 26 /\ (is_tail i = true -> 1 <= p).
Proof.
  intros i c kk ps E E' M' p IL Hag HK N11 HP.
  destruct (rm_bound i c kk ps _ E E' M' p IL Hag HK N11 HP) as [HL HU].
  pose proof (rm_lo_nonneg i). split; [lia|]. intros HT. pose proof (rm_lo_tail i HT). lia.
Qed.

Lemma exit_pay : forall i c kk ps pc E E' (M' : mem) p,
  CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TOther pc) -> pc <> PML.PC_STR_PUSH_BACK ->
  env_agree (CC.cp_nx c) E E' -> know_ok RSEGS E' M' (SR.ps_cells ps) -> 1 <= uv E (EVar 11) <= 21 ->
  phase i E p -> 2 <= p <= 27.
Proof.
  intros i c kk ps pc E E' M' p IL Hne Hag HK N11 HP.
  destruct (rm_bound i c kk ps _ E E' M' p IL Hag HK N11 HP) as [HL HU].
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as Y0. unfold leaf_chk in Y0.
  apply andb_prop in Y0 as [_ Y]. cbv beta iota zeta in Y. rewrite (proj2 (Z.eqb_neq pc PML.PC_STR_PUSH_BACK) Hne) in Y. cbv beta iota in Y.
  apply andb_prop in Y as [_ Y]. clear IL.
  split; [|lia].
  do 26 (destruct i as [|i]; [(cbn in Y; cbn in HL; cbn; first [discriminate Y | lia])|]). cbn in Y. discriminate Y.
Qed.

Definition root_ok (i0 : nat) (n k X : Z) : Prop :=
  match i0 with
  | 0%nat => 0 <= k /\ n + k <= 17 /\ X = 0
  | 1%nat => k < 0 /\ 1 <= n + k <= 17 /\ X = n + k
  | 2%nat => -3 <= n + k <= 0 /\ X = - (n + k)
  | 3%nat => 18 <= n + k /\ X = n + k
  | 4%nat => n + k <= -4 /\ X = - (n + k)
  | _ => False
  end.

Lemma root_choice : forall n k, 1 <= n <= 21 -> -343 <= k <= 309 -> exists i0 X, root_ok i0 n k X.
Proof.
  intros n k Hn Hk.
  destruct (Z_lt_ge_dec (n + k) (-3)) as [A|A]; [exists 4%nat, (- (n + k)); cbn [root_ok]; lia|].
  destruct (Z_le_gt_dec (n + k) 0) as [B|B]; [exists 2%nat, (- (n + k)); cbn [root_ok]; lia|].
  destruct (Z_le_gt_dec 18 (n + k)) as [C|C]; [exists 3%nat, (n + k); cbn [root_ok]; lia|].
  destruct (Z_lt_ge_dec k 0) as [D|D]; [exists 1%nat, (n + k); cbn [root_ok]; lia|].
  exists 0%nat, 0. cbn [root_ok]. lia.
Qed.

Lemma root_lt : forall i0 n k X, root_ok i0 n k X -> (i0 < 5)%nat.
Proof. intros [|[|[|[|[|i]]]]] n k X H; cbn [root_ok] in H; try lia; destruct H. Qed.

Lemma roots_pc : forall i0, (i0 < 5)%nat -> nth_error G.CPS i0 = Some (nth i0 G.CPS G.cp0) /\ CC.cp_pc (nth i0 G.CPS G.cp0) = PMFX.PC_PRETTIFY.
Proof. intros [|[|[|[|[|i]]]]] H; try lia; split; vm_compute; reflexivity. Qed.

Lemma root_phase : forall i0 E, (i0 < 5)%nat -> phase i0 E 0.
Proof. intros [|[|[|[|[|i]]]]] E H; try lia; unfold phase; cbn [lo hi]; lia. Qed.

Lemma bls_nil : forall i, nth i G.BLS [] = [].
Proof. intros i. do 47 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.

Section PrettifyOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PUSHB_OK : str_push_back_x_specU L HI.

Lemma LS : hl_segs L = RSEGS.
Proof. exact (PmLayout.ly_segs L LAY). Qed.

Section Stretch.
Variables (E0 : env) (sp S2 : Z).
Variable WIN : Z.
Hypothesis U2 : bv_unsigned (ev E0 2) = sp.
Hypothesis WIN0 : 0 <= WIN.
Hypothesis SPR : hl_ceil L + WIN <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis S2OBJ : PML.obj_on_stack L sp S2 24.

Lemma out_F0 : forall (F : list SGP.region) E' a, SP.F_sub F (F0W WIN) = true -> env_agree GT.NF E0 E' -> 0 <= a < 2 ^ 64 ->
  ~ (sp - WIN <= a < sp) -> SGP.outside E' F (Z_to_bv 64 a).
Proof.
  intros F E' a HF Hag Ha N1. unfold SGP.outside. apply Forall_forall. intros [[rb rlo] rlen] Hin.
  pose proof (SP.F_sub_in _ _ _ HF Hin) as Hin0. rewrite L5.unsigned_lit by lia.
  destruct SPR as (P1 & P2 & P3).
  unfold F0W in Hin0. cbn [In] in Hin0. destruct Hin0 as [X|[]]; injection X as <- <- <-.
  rewrite (PB.estart_agree GT.NF E0 E' (EVar 2) (-WIN) Hag eq_refl). unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite U2. rewrite (u64_of_Z WIN) by lia. lia.
Qed.

Lemma sink_stretch : forall (F : list SGP.region) E' (M M' : mem) g, SP.F_sub F (F0W WIN) = true -> env_agree GT.NF E0 E' ->
  (forall a : word, SGP.outside E' F a -> M' a = M a) ->
  (forall b, In b (PML.srep_blocks (ESBU.s_rep g)) -> block_range L (fst b) (snd b)) ->
  ESBU.sink_inv M S2 g -> ESBU.sink_inv M' S2 g.
Proof.
  intros F E' M M' g HF Hag HFR HB (HS & HL).
  destruct S2OBJ as (O1 & O2 & O3). destruct SPR as (P1 & P2 & P3).
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - WIN \/ sp <= a) -> L5C.agree_on M M' a n).
  { intros a n H0 H1 H2 i Hi. apply HFR. apply (out_F0 F E' i HF Hag); lia. }
  split; [|exact HL].
  apply (EK.sink_at_agree M M' S2 (ESBU.s_rep g)); [lia | lia | apply AG; lia | | exact HS].
  destruct (ESBU.s_rep g) as [s|cap p s] eqn:Hrep; [exact I|].
  destruct (HB (p, cap) ltac:(left; reflexivity)) as (R0 & R1 & R2 & R3 & R4). cbn [fst snd] in *.
  split; [lia|]. split; [lia|]. apply AG; unfold hl_ceil in *; lia.
Qed.
End Stretch.

Section Comp.
Variables (buf n k : Z) (bs : list Z) (LBo : list (Z * Z)) (cr : credit) (sp r SK S2 kx bx : Z) (rep : PML.srep).
Variables (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet).
Hypothesis HH : hi_heap HI (LBo ++ PML.srep_blocks rep) cr M (m_vmmaps model).
Hypothesis Hmo : PML.model_ok model.
Hypothesis HKnil : K [].
Hypothesis Hfp : PML.fp_ok fx.
Hypothesis HPRE : PML.entry L R M sp r PMFXT.PR_SCR /\
  (PML.a0 R buf /\ PML.a1 R n /\ PML.a2 R k /\ PML.a3 R (2 ^ 64 - 4) /\ getr R 14%bv = Z_to_bv 64 17 /\ getr R 15%bv = Z_to_bv 64 SK /\
   1 <= n <= 21 /\ -343 <= k <= 309 /\ exists S2' : Z, PML.u64 M SK S2' /\ 0 <= S2' < 2 ^ 64 /\ PMFXT.rd_buf L M sp buf n S2' SK bs) /\
  PML.u64 M SK S2 /\ sp <= SK /\ SK + 8 <= hl_sptop L /\ PML.apart SK 8 S2 24 /\
  sink_at M S2 rep /\ PML.obj_on_stack L sp S2 24 /\ PML.img_ro M /\ screditU L cr rep kx bx /\ len (PML.srep_chars rep) + 27 <= CLU.
Hypothesis Hcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z))
  (W' : list L5.range), PML.fp_ok fx' ->
  (exists (rep' : PML.srep) (pay : Z), 2 <= pay <= 27 /\ True /\ sink_at M' S2 rep' /\ len (PML.srep_chars rep') = len (PML.srep_chars rep) + pay /\
     LB' = LBo ++ PML.srep_blocks rep' /\ LBk = LBo /\ W' = [(S2, 24)] /\ screditU L cr' rep' kx bx) ->
  regs_preserved R R' -> L5C.hpres L LBk sp PMFXT.PR_SCR W' M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.
Variables (i0 : nat) (X : Z).
Hypothesis HR0 : root_ok i0 n k X.

Ltac pre := pose proof HPRE as (Hentry & (Ha0 & Ha1 & Ha2 & Ha3 & Ha14 & Ha15 & Hn & Hk & (S2' & HskS2' & HS2' & Hrd)) & HskS2 & Hsk1 & Hsk2 & Hapsk & Hsink & Hobj & Himg & Hcred & Hroom);
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk); destruct Hstk as (S1 & S2s & S3 & S4 & S5);
  destruct Hrd as (Hbs & Hbdef & Hblen & Hb1 & Hb2 & Hb3 & Hb4); pose proof Hobj as (OS1 & OS2 & OS3);
  unfold PMFXT.PR_SCR, PMFXT.STRX_SCR, STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK, PML.apart in *.

Definition E0 : env := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [S2; X] 0))) (fun _ => []).
Definition len0 : Z := len (PML.srep_chars rep).
Definition W : list L5.range := [(S2, 24)].
Definition XIv (g1 : ESBU.sghost) (i : nat) (E : env) (M1 : mem) : Prop := ESBU.sink_inv M1 S2 g1 /\ phase i E (ESBU.s_len g1 - len0).
Definition CredV := ESBU.CredV L kx bx.
Definition gB := ESBU.gB [].

Lemma EV : forall x : reg, ev E0 (ridx x) = getr R x.
Proof. intros x. unfold E0. apply CL5.ev_reg. Qed.
Lemma U2 : bv_unsigned (ev E0 2) = sp.
Proof. pre. rewrite (EV 2%bv). rewrite Hsp. apply u64_of_Z. lia. Qed.
Lemma U10 : bv_unsigned (ev E0 10) = buf.
Proof. pre. rewrite (EV 10%bv). rewrite Ha0. apply u64_of_Z. lia. Qed.
Lemma U11 : bv_unsigned (ev E0 11) = n.
Proof. pre. rewrite (EV 11%bv). rewrite Ha1. apply u64_of_Z. lia. Qed.
Lemma U15 : bv_unsigned (ev E0 15) = SK.
Proof. pre. rewrite (EV 15%bv). rewrite Ha15. apply u64_of_Z. lia. Qed.
Lemma V32 : ev E0 32 = Z_to_bv 64 S2.
Proof. reflexivity. Qed.
Lemma U32 : bv_unsigned (ev E0 32) = S2.
Proof. pre. rewrite V32. apply u64_of_Z. lia. Qed.
Lemma TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Proof. pre. rewrite (EV 4%bv). rewrite Htp, (PmLayout.ly_tp L LAY). reflexivity. Qed.
Lemma SCRV : CH.hd_scr G.HDECL = 8592.
Proof. reflexivity. Qed.
Lemma STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof. pre. rewrite SCRV. unfold hl_ceil. repeat split; lia. Qed.
Lemma SPR0 : hl_ceil L + 8592 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof. pre. unfold hl_ceil. repeat split; lia. Qed.
Lemma SCRP : 0 <= CH.hd_scr G.HDECL.
Proof. rewrite SCRV. lia. Qed.
Lemma NF32 : (32 <= GT.NF)%nat.
Proof. unfold GT.NF. lia. Qed.
Lemma HOBJ : PML.obj_on_stack L sp S2 24.
Proof. pre. exact Hobj. Qed.
Lemma W_S2 : In (S2, 24) W.
Proof. left. reflexivity. Qed.
Lemma W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a.
Proof. pre. intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). Qed.
Lemma CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a).
Proof.
  pre. intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
  - rewrite U10, U11 in Ha. split; [lia | left; lia].
  - rewrite U15 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia].
Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a).
Proof.
  pre. intros rg [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
  rewrite U32 in Ha. rewrite u64_of_Z in Ha by lia. exists (S2, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.
Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Proof. intros rg a []. Qed.
Lemma DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL).
Proof. pre. rewrite SCRV. intros j Hj. apply S5. lia. Qed.
Lemma OADDR : estart E0 (SA S2E 0) = S2.
Proof. pre. unfold estart, S2E. cbn [a_base a_off edenot]. rewrite U32. lia. Qed.
Lemma ES2 : forall S2' : Z, PML.u64 M SK S2' -> 0 <= S2' < 2 ^ 64 -> S2' = S2.
Proof.
  pre. intros S2x HskS2x HS2x.
  unfold PML.u64, L5.u64_at, word_to_le_bytes in HskS2, HskS2x. rewrite HskS2 in HskS2x.
  pose proof (f_equal (fun o => match o with Some l => bytes_le_to_Z l | None => 0 end) HskS2x) as E. cbn beta iota in E. rewrite !u64_of_Z in E by lia. rewrite !bytes_le_to_Z_of_le_bytes in E by lia.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact (eq_sym E).
Qed.
Lemma GBL : forall g1, gB g1 = PML.srep_blocks (ESBU.s_rep g1).
Proof. intros g1. unfold gB, ESBU.gB. apply app_nil_r. Qed.
Lemma U11E : forall E, env_agree GT.NF E0 E -> uv E (EVar 11) = n.
Proof. intros E H. unfold uv. rewrite (PB.uv_agree GT.NF E0 E (EVar 11) H eq_refl). exact U11. Qed.
Lemma HKC : forall c ps E' R' (M1 M' : mem), CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> know_ok RSEGS E' M' (SR.ps_cells ps).
Proof. intros c ps E' R' M1 M' HLF. rewrite <- LS. unfold know_ok. apply Forall_forall. exact (CC.lf_cells _ _ _ _ _ _ _ HLF). Qed.
Lemma AGE : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E -> env_agree (CC.cp_nx c) E E' -> env_agree GT.NF E0 E'.
Proof. intros i c E E' Hc H1 H2. eapply CC.env_agree_trans; [exact H1 | eapply CC.env_agree_le; [exact H2 | exact (G.NF_le i c Hc)]]. Qed.
Lemma BRG : forall g1 M0c i E (M1 : mem) m1, CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 ->
  (forall b, In b (PML.srep_blocks (ESBU.s_rep g1)) -> block_range L (fst b) (snd b)) /\ env_agree GT.NF E0 E /\
  exists cr1, hi_heap HI (CH2.den E (nth i G.BLS []) ++ LBo ++ gB g1) cr1 M1 (m_vmmaps m1) /\ CredV g1 i E cr1.
Proof.
  intros g1 M0c i E M1 m1 (_ & _ & HagE & (cr1 & HH1 & HC1) & _). split; [|split; [exact HagE | exists cr1; split; [exact HH1 | exact HC1]]]. intros b Hb.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf & _). apply (Hwf b). unfold CH2.cur, CH2V.LBr. apply in_or_app. right. apply in_or_app. right. rewrite GBL. exact Hb.
Qed.
Lemma STRETCH : forall g1 M0c i c kk ps t E R1 (M1 : mem) m1 E' R' (M' : mem), CH2.is_leaf G.CPS G.TAGS i c kk ps t -> CC.At (hl_segs L) c E R1 M1 ->
  CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 ->
  env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' ->
  ESBU.sink_inv M' S2 g1 /\ env_agree GT.NF E0 E'.
Proof.
  intros g1 M0c i c kk ps t E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X0. unfold leaf_chk in X0.
  apply andb_prop in X0 as [XF _]. apply andb_prop in XF as [XF _]. apply andb_prop in XF as [XF _].
  destruct IL as (tags & Hc & _). destruct (BRG _ _ _ _ _ _ HA) as (HB & HagE & _). pose proof (AGE i c E E' Hc HagE Hag) as HagE'.
  split; [|exact HagE']. destruct HX as (HX1 & _).
  exact (sink_stretch E0 sp S2 8592 U2 ltac:(lia) SPR0 HOBJ (CC.cp_F c) E' M1 M' g1 XF HagE' (CC.lf_frame _ _ _ _ _ _ _ HLF) HB HX1).
Qed.

Lemma wd_regs_pw : forall E sr (R0 : bvmap 5 word), (forall q, (0 < q < 32)%nat -> getr R0 (Z_to_bv 5 (Z.of_nat q)) = edenot E (nth q sr (ELit 0))) -> regs_ok E sr R0.
Proof.
  intros E sr R0 H. apply APSX.regs_ok_pointwise. intros rg Hr0.
  pose proof (ridx_range rg) as Hq. rewrite <- (ridx_roundtrip rg) at 1. apply H. split; [|lia].
  destruct (ridx rg) eqn:Er; [|lia]. exfalso. apply Hr0. rewrite <- (ridx_roundtrip rg), Er. apply bv_eq. reflexivity.
Qed.
Lemma wd_reg_uv : forall E (R0 : bvmap 5 word) (q : nat) (rg : reg) e z, Z_to_bv 5 (Z.of_nat q) = rg -> getr R0 rg = Z_to_bv 64 z -> PB.uv E e = z mod 2 ^ 64 ->
  getr R0 (Z_to_bv 5 (Z.of_nat q)) = edenot E e.
Proof.
  intros E R0 q rg e z Hq Hr Hu. rewrite Hq, Hr. apply bv_eq. unfold PB.uv in Hu. rewrite Hu, Z_to_bv_unsigned. unfold bv_wrap. reflexivity.
Qed.
Lemma wd_krange_neg : forall E (M0 : mem) e lo hi v, lden E (lin_of e) = v -> - 2 ^ 64 <= v < 0 -> lo <= v + 2 ^ 64 <= hi -> kentry_ok RSEGS E M0 (KRange e lo hi).
Proof.
  intros E M0 e lo hi v H Hv Hr. cbn [kentry_ok].
  assert (U : bv_unsigned (edenot E e) = v + 2 ^ 64).
  { destruct (lin_of_sound E e) as [q Hq]. unfold uE in Hq. pose proof (u64_range (edenot E e)) as Hu.
    change (2 ^ 64) with two64 in *. unfold two64 in *. lia. }
  rewrite U. exact Hr.
Qed.
Lemma wd_uv_lin : forall E e v, lden E (lin_of e) = v -> PB.uv E e = v mod 2 ^ 64.
Proof.
  intros E e v H. destruct (lin_of_sound E e) as [q Hq]. unfold uE in Hq. pose proof (u64_range (edenot E e)) as Hu.
  unfold PB.uv. rewrite <- H, Hq, Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac wd_rq Ha2 Ha3 Ha14 :=
  cbn [CC.cp_regs G.cp0 G.cp1 G.cp2 G.cp3 G.cp4 nth];
  first [ reflexivity
        | eapply (wd_reg_uv _ R 13 13%bv); [apply bv_eq; reflexivity | exact Ha3 | unfold PB.uv; cbn [edenot]; reflexivity]
        | eapply (wd_reg_uv _ R 14 14%bv); [apply bv_eq; reflexivity | exact Ha14 | unfold PB.uv; cbn [edenot]; reflexivity]
        | eapply (wd_reg_uv _ R 12 12%bv); [apply bv_eq; reflexivity | exact Ha2 |
            first [ rewrite (wd_uv_lin E0 _ (X - n)) by (lin_eval; rw_atoms; lia); f_equal; lia
                  | rewrite (wd_uv_lin E0 _ (- (X + n))) by (lin_eval; rw_atoms; lia); f_equal; lia ] ] ].

Lemma entry_at : CC.At (hl_segs L) (nth i0 G.CPS G.cp0) E0 R M.
Proof.
  pre. pose proof (root_lt _ _ _ _ HR0) as Hlt. rewrite LS. pose proof (ES2 S2' HskS2' HS2') as ES. subst S2'.
  pose proof U2 as U2'. pose proof U10 as U10'. pose proof U11 as U11'. pose proof U15 as U15'. pose proof U32 as U32'.
  assert (Hds : L5.defined M (sp - 8592) 8592) by (intros j Hj; apply S5; lia).
  assert (U12 : 0 <= k -> bv_unsigned (ev E0 12) = k) by (intros Hk0; rewrite (EV 12%bv), Ha2; apply u64_of_Z; lia).
  assert (HX0 : 0 <= X <= 342) by (destruct i0 as [|[|[|[|[|j0]]]]]; cbn [root_ok] in HR0; lia).
  assert (UX : PB.uv E0 (EVar 33) = X) by (unfold PB.uv; cbn [edenot]; change (ev E0 33) with (Z_to_bv 64 X); apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = X) by exact UX.
  assert (UN : PB.uv E0 (EVar 11) = n) by exact U11'.
  destruct i0 as [|[|[|[|[|j0]]]]]; [ | | | | | lia]; cbn [root_ok] in HR0; cbn [nth G.CPS]; split.
  1, 3, 5, 7, 9: (apply wd_regs_pw; intros q Hq; do 32 (destruct q as [|q]; [first [lia | wd_rq Ha2 Ha3 Ha14] |]); lia).
  all: try (pose proof (U12 ltac:(lia)) as U12').
  all: unfold know_ok, G.cp0, G.cp1, G.cp2, G.cp3, G.cp4; cbn [CC.cp_know]; repeat (apply Forall_cons); [.. | apply Forall_nil].
  all: first [ eapply CL5.kword64_intro with (A := SK) (z := S2); [ev_start | lia | lia | exact V32 | exact HskS2]
             | e_range | e_align S1 | e_align OS3 | e_unk | e_wr | e_disj
             | eapply wd_krange_neg; [lin_eval; rw_atoms; reflexivity | lia | lia] ].
Qed.

Lemma goto_xi : forall g1 M0c, CH2V.okV L M LBo sp G.HDECL W M0c -> forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) ->
  forall E R1 E' R' (M1 M' : mem) m1, CC.At (hl_segs L) c E R1 M1 -> CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 ->
  env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> XIv g1 i E M1 -> XIv g1 j (CC.env_over GT.NF sg E') M'.
Proof.
  intros g1 M0c OKV i c kk ps j sg IL E R1 E' R' M1 M' m1 HAt HA Hag HLF HX.
  destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF) as [HINV _].
  destruct (BRG _ _ _ _ _ _ HA) as (_ & HagE & _).
  destruct HX as (_ & HP). split; [exact HINV|].
  pose proof (U11E E HagE) as N11. pose proof HPRE as (_ & (_ & _ & _ & _ & _ & _ & Hn & _) & _).
  exact (goto_phase i c kk ps j sg E E' M' _ IL Hag (HKC c ps E' R' M1 M' HLF) ltac:(lia) HP).
Qed.

Lemma tail_leaf_ok : forall i c kk ps, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TOther PML.PC_STR_PUSH_BACK) -> is_tail i = true ->
  forall g1 M0c, CH2V.okV L M LBo sp G.HDECL W M0c ->
  CH2V.leaf_okV L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv G.CPS K PML.fp_ok g1 M0c i c ps.
Proof.
  intros i c kk ps IL TL g1 M0c OKV. pre.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X0. unfold leaf_chk in X0. apply andb_prop in X0 as [_ X0].
  rewrite Z.eqb_refl, TL in X0.
  apply andb_prop in X0 as [X0 YR]. apply andb_prop in X0 as [X0 Y1]. apply andb_prop in X0 as [X0 Y10]. apply andb_prop in X0 as [X2 Y2]. apply Z.eqb_eq in X2.
  intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  assert (DEFC : L5.defined M0c (sp - 8592) 8592) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
  destruct (ETL.tail_leaf L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS
              (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) 8592 ltac:(rewrite SCRV; lia) ltac:(unfold hl_ceil; lia) DEFC R EV heap_ok3
              i c kk ps PML.PC_STR_PUSH_BACK IL Y2 E R1 M1 m1 E' R' M' HAt HAmb Hag HLF) as (HRP & KEEP & HP & HA' & HagE').
  destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HAmb HX Hag HLF) as [HINV _].
  destruct HX as [_ HPH].
  destruct (BRG _ _ _ _ _ _ HAmb) as (_ & HagE & _).
  destruct (BRG _ _ _ _ _ _ HA') as (HB & _ & cr1 & HH1 & HC1).
  rewrite bls_nil in HH1. cbn [CH2.den map app] in HH1. rewrite GBL in HH1.
  assert (HP2 : L5C.hpres L LBo sp 8592 W M M').
  { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
  destruct HA' as (Hmo1 & Hbv1 & _).
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 S2).
  { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 10 (EVar 32) HLF Y10) as G10.
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity). rewrite G10. cbn [edenot].
    destruct HagE' as [AG _]. rewrite <- AG by (unfold GT.NF; lia). exact V32. }
  set (ch := bv_unsigned (edenot E' (CA.ps_reg ps 11))).
  assert (Hch : 0 <= ch <= 255) by (pose proof (PB.fact_ok' E' M' _ _ (HKC c ps E' R' M1 M' HLF) YR) as KR; cbn [kentry_ok] in KR; exact KR).
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 ch).
  { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps E' R' M1 M' 11 (CA.ps_reg ps 11) HLF Y1) as G11.
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in G11 by (apply bv_eq; reflexivity). rewrite G11. unfold ch. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof HINV as [Hsink1 Hlen1].
  destruct (push_room i c kk ps E E' M' _ IL Hag (HKC c ps E' R' M1 M' HLF) ltac:(rewrite (U11E E HagE); lia) HPH) as [HPR1 HPR2].
  specialize (HPR2 TL).
  rewrite X2, LS.
  apply (PUSHB_OK (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) cr1 S2 ch sp r (ESBU.s_rep g1) fx' R' M' m1 K HH1 Hmo1 HKnil HFP).
  { split; [split; [rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra | split; [exact Hraok | split; [rewrite (KEEP 2%bv ltac:(right; left; reflexivity)); exact Hsp |
             split; [rewrite (KEEP 4%bv ltac:(right; right; right; left; reflexivity)); exact Htp|]]]]|].
    - unfold STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK. split; [exact S1|]. split; [unfold hl_ceil in *; lia|]. split; [lia|]. split; [lia|].
      intros j Hj. replace (sp - (256 + (16 + 8224)) + j) with (sp - 8592 + (j + 96)) by lia. apply (L5C.hpres_defined _ _ _ _ _ _ _ HP2). lia.
    - split; [exact Ga0|]. split; [exact Ga1|]. split; [lia|]. split; [exact Hsink1|].
      split; [destruct (ESBU.s_rep g1) as [s0|cap0 p0 s0]; cbn [rep_live PML.srep_blocks]; [exact I | apply in_or_app; right; left; reflexivity]|].
      split; [exact Hobj|]. intros HNF. apply (EK.grow_okU L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) cr1 (ESBU.s_rep g1) kx bx _ HC1 (EK.rep8_of_sink _ _ _ Hsink1));
        [unfold len0, PMES.len, PMFXT.len in *; lia | unfold len0, PMES.len, PMFXT.len in *; lia | exact HNF]. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (rep' & Hgrown & HWc) HRP2 HPc Hbv2 HH2. subst Wc.
  assert (Hrep8 : match ESBU.s_rep g1 with PML.SShort _ => True | PML.SLong cap _ _ => 8 <= cap /\ cap mod 8 = 0 end).
  { destruct Hsink1 as (Hs1 & _ & Hs3). destruct (ESBU.s_rep g1) as [s0|cap0 p0 s0]; [exact I|]. cbn [rep_ok PML.str_at] in *. destruct Hs1 as (_ & Hm & _). split; [lia | exact Hm]. }
  assert (Hcl : len (PML.srep_chars (ESBU.s_rep g1) ++ [ch]) <= CLU) by (unfold len0, PMES.len, PMFXT.len in *; rewrite length_app; cbn [length]; lia).
  pose proof (EK.grown_screditU L (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) _ _ _ _ _ _ _ _ _ _ kx bx Hgrown Hrep8 Hcl HC1) as HC'.
  assert (Hdrop : lb_drop (ESBU.s_rep g1) (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) = LBo).
  { pose proof (ESBU.den_app_nodup L HI HIok LBo [] [] (ESBU.s_rep g1) cr1 M' (m_vmmaps m1)) as D. cbn [app] in D. rewrite !app_nil_r in D. apply D. exact HH1. }
  assert (FACTS : sink_at M2 S2 rep' /\ len (PML.srep_chars rep') = ESBU.s_len g1 + 1 /\ LBk = LBo /\ Permutation LB' (LBo ++ PML.srep_blocks rep')).
  { destruct Hgrown as [(F & -> & Hs & -> & _ & ->)|(NFt & p' & Gx)].
    - split; [exact Hs|]. split; [destruct (ESBU.s_rep g1); cbn [same_rep PML.srep_chars] in *; unfold PMES.len, PMFXT.len in *; rewrite length_app; cbn [length]; lia|].
      split; [exact Hdrop|]. destruct (ESBU.s_rep g1); cbn [same_rep PML.srep_blocks]; apply Permutation_refl.
    - cbv zeta in Gx. destruct Gx as (-> & Hs & FB & -> & _ & ->). split; [exact Hs|].
      split; [cbn [PML.srep_chars]; unfold PMES.len, PMFXT.len in *; rewrite length_app; cbn [length]; lia|]. split; [exact Hdrop|].
      rewrite Hdrop. cbn [PML.srep_blocks]. apply Permutation_cons_append. }
  destruct FACTS as (Hsink2 & Hlen2 & -> & Hperm).
  apply (Hcont fx2 R2 M2 model2 (LBo ++ PML.srep_blocks rep') cr' LBo W HFP2); [| exact (L5.regs_preserved_trans _ _ _ HRP HRP2) | |
         exact (L5C.model_but_vm_trans _ _ _ Hbv1 Hbv2) | exact (CH2V.hi_heap_perm L HI HIok _ _ _ _ _ HH2 Hperm)].
  - exists rep', (ESBU.s_len g1 + 1 - len0).
    split; [lia|]. split; [exact I|]. split; [exact Hsink2|]. split; [unfold len0 in *; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exact HC'.
  - apply (ETL.hpres_comp L LBo sp 8592 (256 + (16 + 8224)) W M M' M2); [lia | unfold hl_ceil in *; lia | lia | rewrite LER; lia | lia | exact HP2 | exact HPc].
Qed.

Lemma den_nil : forall E i, CH2.den E (nth i G.BLS []) = [].
Proof. intros E i. rewrite bls_nil. reflexivity. Qed.
Lemma PRS : PMFXT.PR_SCR = 8592.
Proof. reflexivity. Qed.
Lemma N11_of : forall i c E E', nth_error G.CPS i = Some c -> env_agree GT.NF E0 E' -> env_agree (CC.cp_nx c) E E' -> 1 <= uv E (EVar 11) <= 21.
Proof.
  intros i c E E' Hc HagE' Hag. pose proof HPRE as (_ & (_ & _ & _ & _ & _ & _ & Hn & _) & _).
  assert (N : uv E (EVar 11) = n).
  { rewrite <- (U11E E' HagE'). unfold uv. symmetry. apply (PB.uv_agree (CC.cp_nx c) E E' (EVar 11) Hag). cbn [APC.expr_vars_lt]. apply Nat.ltb_lt.
    pose proof (G.NF_le i c Hc) as HN. unfold GT.NF in HN. lia. }
  rewrite N. exact Hn.
Qed.

Lemma push_leaf_ok : forall i c kk ps, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TOther PML.PC_STR_PUSH_BACK) -> is_tail i = false ->
  forall g1 M0c, CH2V.okV L M LBo sp G.HDECL W M0c ->
  CH2V.leaf_okV L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv G.CPS K PML.fp_ok g1 M0c i c ps.
Proof.
  intros i c kk ps IL TL g1 M0c OKV.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as Y0. unfold leaf_chk in Y0.
  apply andb_prop in Y0 as [_ Y]. cbv beta iota zeta in Y. rewrite Z.eqb_refl, TL in Y. cbv beta iota in Y.
  apply andb_prop in Y as [Y _]. apply andb_prop in Y as [Y2 Y3]. apply Z.eqb_eq in Y2.
  unfold sink_j in Y3. apply andb_prop in Y3 as [Y3a Y3b].
  destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. apply Nat.eqb_eq in Y3a.
  destruct (nth_error G.CPS (ret_cut i kk)) as [cj|] eqn:Hcj; [|discriminate].
  destruct (ESBU.pushb_chk GT.NF G.HDECL S2E 0 c ps cj (nth i G.BLS []) (nth (ret_cut i kk) G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
  subst j.
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (? & Hc & _); exact Hc).
  assert (XILEAF : forall E R1 (M1 : mem) m1 E' R' (M' : mem), CC.At (hl_segs L) c E R1 M1 ->
             CH2V.heap_ambV L HI GT.NF E0 model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV g1 M0c i E M1 m1 -> XIv g1 i E M1 -> env_agree (CC.cp_nx c) E E' ->
             CC.leaf_facts (hl_segs L) c ps E' R' M1 M' -> ESBU.sink_inv M' S2 g1 /\ ESBU.s_len g1 + 1 <= CLU).
  { intros E R1 M1 m1 E' R' M' HAt HA HX Hag HLF.
    destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HA HX Hag HLF) as [HINV HagE']. split; [exact HINV|].
    destruct HX as [_ HP].
    destruct (push_room i c kk ps E E' M' _ IL Hag (HKC c ps E' R' M1 M' HLF) (N11_of i c E E' Hc HagE' Hag) HP) as [HR1 _].
    pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hroom). unfold len0 in *. lia. }
  apply (ESBU.pushb_leaf_ok L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS [] kx bx XIv STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK IMG_OK G.CPS G.TAGS G.RETS K HKnil DEF0
           S2 HOBJ W_S2 S2E 0 eq_refl OADDR PUSHB_OK i c kk ps (ret_cut i kk) cj ci g1 M0c OKV IL Hret Hcj Y2 Hchk XILEAF).
  intros E E' R' M1 M' E2 M2 g' HX HagE' Hag HLF Hag2 Hnx HINV2 G1.
  split; [exact HINV2|]. destruct HX as [_ HP]. rewrite G1.
  replace (ESBU.s_len g1 + 1 - len0) with ((ESBU.s_len g1 - len0) + 1) by lia.
  exact (ret_phase i c kk ps E E' E2 M' ci _ IL TL Hag (HKC c ps E' R' M1 M' HLF) Hag2 Hnx (N11_of i c E E' Hc HagE' Hag) HP).
Qed.

Lemma exit_leaf_ok : forall i c kk ps pc, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TOther pc) -> pc <> PML.PC_STR_PUSH_BACK ->
  forall g1 M0c, CH2V.okV L M LBo sp G.HDECL W M0c ->
  CH2V.leaf_okV L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv G.CPS K PML.fp_ok g1 M0c i c ps.
Proof.
  intros i c kk ps pc IL Hne g1 M0c OKV.
  pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as Y0. unfold leaf_chk in Y0.
  apply andb_prop in Y0 as [_ Y]. cbv beta iota zeta in Y. rewrite (proj2 (Z.eqb_neq pc PML.PC_STR_PUSH_BACK) Hne) in Y. cbv beta iota in Y.
  apply andb_prop in Y as [Y1 _].
  assert (Hc : nth_error G.CPS i = Some c) by (destruct IL as (? & Hc & _); exact Hc).
  intros fx' E R1 M1 m1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  destruct (STRETCH g1 M0c i c kk ps _ E R1 M1 m1 E' R' M' IL HAt HAmb HX Hag HLF) as [HINV HagE'].
  pose proof HPRE as (Hentry & _). destruct Hentry as (Hra & Hraok & _).
  assert (DEFC : L5.defined M0c (sp - 8592) 8592) by (rewrite <- SCRV; exact (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)).
  apply (PB.exit_ret L HI HIok LAY GT.NF E0 M0c model (CH2V.LBr LBo ESBU.sghost gB g1) sp G.HDECL W G.BLS (CredV g1) STKF SCRP NF32 U2 W_OK WRS_OK G.CPS G.TAGS K (XIv g1)
           (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV) (fun _ => 0) (fun _ => 0)
           8592 ltac:(rewrite SCRV; lia) (proj1 SPR0) DEFC R EV r Hra Hraok heap_ok3 RETPC i c kk ps pc ret_at IL Y1 fx' E R1 M1 m1 E' R' M' HAt HAmb Hag HLF).
  intros HRP HP HA' _. destruct HA' as (Hmo1 & Hbv1 & _ & (cr1 & HH1 & HC1) & _ & _).
  destruct HX as [_ HPH].
  assert (HP2 : L5C.hpres L LBo sp 8592 W M M').
  { rewrite <- SCRV. apply (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W ESBU.sghost gB NF32 g1 M0c M' OKV). rewrite SCRV. exact HP. }
  pose proof (exit_pay i c kk ps pc E E' M' _ IL Hne Hag (HKC c ps E' R' M1 M' HLF) (N11_of i c E E' Hc HagE' Hag) HPH) as HPAY.
  apply (Hcont fx' R' M' m1 (LBo ++ PML.srep_blocks (ESBU.s_rep g1)) cr1 LBo W HFP); [| exact HRP | rewrite PRS; exact HP2 | exact Hbv1 |].
  - exists (ESBU.s_rep g1), (ESBU.s_len g1 - len0). destruct HINV as [Hs Hl].
    split; [lia|]. split; [exact I|]. split; [exact Hs|]. split; [unfold len0 in *; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exact HC1.
  - unfold CH2.cur, CH2V.LBr in HH1. rewrite GBL, den_nil in HH1. exact HH1.
Qed.

Lemma comp_ok : srealizes RSEGS SCFG (@PML.cfg fx R PMFX.PC_PRETTIFY M model) K.
Proof.
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & Hsink & _ & _ & Hcred & _).
  pose proof (root_lt i0 n k X HR0) as Hlt. destruct (roots_pc i0 Hlt) as [Hc0 Hpc0].
  unfold PML.cfg. rewrite <- Hpc0. rewrite <- LS.
  eapply (CH2V.cert_sound3V L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv STKF SCRP NF32 U2 W_OK WRS_OK
            G.CPS K PML.fp_ok G.TAGS) with (i := i0) (E := E0).
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok3.
  - intros g1 i c kk ps j sg IL E E' R' M1 M' cr1 _ _ _ HC. exact HC.
  - exact goto_xi.
  - intros i c kk ps pc IL g1 M0c OKV. destruct (Z.eq_dec pc PML.PC_STR_PUSH_BACK) as [->|Hne].
    + destruct (is_tail i) eqn:TL; [exact (tail_leaf_ok i c kk ps IL TL g1 M0c OKV) | exact (push_leaf_ok i c kk ps IL TL g1 M0c OKV)].
    + exact (exit_leaf_ok i c kk ps pc IL Hne g1 M0c OKV).
  - exact Hc0.
  - exact entry_at.
  - apply (CH2V.amb3V_intro L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS ESBU.sghost gB CredV XIv (ESBU.SG rep len0) M i0 E0 M model
             (CH2V.okV_refl L M LBo sp G.HDECL W DEF0)).
    split; [|split; [split; [exact Hsink | reflexivity] | cbn [ESBU.s_len]; replace (len0 - len0) with 0 by lia; exact (root_phase i0 E0 Hlt)]].
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [unfold CH2.cur, CH2V.LBr; rewrite bls_nil; cbn [CH2.den map app]; rewrite (GBL (ESBU.SG rep len0)); cbn [ESBU.s_rep]; exact HH|].
    exact Hcred.
  - exact Hfp.
Qed.
End Comp.

Theorem prettify_x_ok : PMFXT.prettify_x_specU L HI.
Proof.
  intros buf n k bs LBo cr sp r SK S2 kx bx rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp HPRE Hcont.
  pose proof HPRE as (_ & (_ & _ & _ & _ & _ & _ & Hn & Hk & _) & _).
  destruct (root_choice n k Hn Hk) as (i0 & X & HR0).
  eapply comp_ok; eassumption.
Qed.
End PrettifyOk.
End PRXU.
