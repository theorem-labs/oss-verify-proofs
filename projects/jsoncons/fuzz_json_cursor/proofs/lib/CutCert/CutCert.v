(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan L5Defs.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CC.

Definition subst : Type := list (nat * expr).
Fixpoint slook (s : subst) (n : nat) : expr :=
  match s with
  | [] => ELit 0
  | (m, e) :: r => if Nat.eqb m n then e else slook r n
  end.

Fixpoint esubstL (lo : nat) (s : subst) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => if Nat.ltb n lo then x else slook s n
  | EAlu op a b => mkAlu op (esubstL lo s a) (esubstL lo s b)
  | EAluw op a b => mkAluw op (esubstL lo s a) (esubstL lo s b)
  | EMd op a b => mkMd op (esubstL lo s a) (esubstL lo s b)
  | EMdw op a b => mkMdw op (esubstL lo s a) (esubstL lo s b)
  | EExt sx l n a => EExt sx l n (esubstL lo s a)
  | EBlob _ _ _ _ => x
  end.
Definition asubstL (lo : nat) (s : subst) (a : saddr) : saddr := SA (esubstL lo s (a_base a)) (a_off a).
Definition ksubstL (lo : nat) (s : subst) (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (asubstL lo s a) w (esubstL lo s v)
  | KZero a n => KZero (asubstL lo s a) (esubstL lo s n)
  | KBlob a n k => KBlob (asubstL lo s a) (esubstL lo s n) k
  | KImg _ _ => K
  | KAlign x m => KAlign (esubstL lo s x) m
  | KRange x l h => KRange (esubstL lo s x) l h
  | KWr a n => KWr (asubstL lo s a) (esubstL lo s n)
  | KDisj a1 n1 a2 n2 => KDisj (asubstL lo s a1) (esubstL lo s n1) (asubstL lo s a2) (esubstL lo s n2)
  | KFill a n c => KFill (asubstL lo s a) (esubstL lo s n) c
  | KUnk a n => KUnk (asubstL lo s a) (esubstL lo s n)
  end.

Definition env_over (lo : nat) (s : subst) (E : env) : env :=
  Env (fun n => if Nat.ltb n lo then ev E n else edenot E (slook s n)) (eb E).

Lemma esubstL_denot : forall lo s E x, edenot E (esubstL lo s x) = edenot (env_over lo s E) x.
Proof.
  intros lo s E x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx l n a IHa|sx k i n];
    cbn [esubstL edenot]; try reflexivity.
  - cbn [env_over ev]. destruct (Nat.ltb n lo); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.
Lemma estart_asubstL : forall lo s E a, estart E (asubstL lo s a) = estart (env_over lo s E) a.
Proof. intros lo s E [b o]. unfold asubstL, estart. cbn [a_base a_off]. rewrite esubstL_denot. reflexivity. Qed.
Lemma adenot_asubstL : forall lo s E a, adenot E (asubstL lo s a) = adenot (env_over lo s E) a.
Proof. intros lo s E [b o]. unfold asubstL, adenot. cbn [a_base a_off]. rewrite esubstL_denot. reflexivity. Qed.

Lemma kentry_ok_ksubstL : forall segs lo s E M K,
  kentry_ok segs E M (ksubstL lo s K) <-> kentry_ok segs (env_over lo s E) M K.
Proof.
  intros segs lo s E M K. set (E' := env_over lo s E).
  destruct K as [a w v|a n|a n k|l h|x m|x l h|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubstL kentry_ok];
    unfold flat, elenZ; rewrite ?estart_asubstL, ?adenot_asubstL, ?esubstL_denot; fold E'; try tauto.
Qed.

Lemma env_over_agree : forall lo s E, env_agree lo E (env_over lo s E).
Proof.
  intros lo s E. split; [|reflexivity]. intros n Hn. cbn [env_over ev].
  destruct (Nat.ltb_spec n lo); [reflexivity | lia].
Qed.

Lemma env_agree_trans : forall b E1 E2 E3, env_agree b E1 E2 -> env_agree b E2 E3 -> env_agree b E1 E3.
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite (A1 n Hn); apply A2; exact Hn | congruence]. Qed.
Lemma env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [A B] Hle. split; [intros n Hn; apply A; lia | exact B]. Qed.
Lemma env_agree_refl : forall b E, env_agree b E E.
Proof. intros; split; reflexivity. Qed.
Lemma env_agree_sym : forall b E E', env_agree b E E' -> env_agree b E' E.
Proof. intros b E E' [A B]. split; [intros n Hn; symmetry; apply A; exact Hn | congruence]. Qed.

Record cutpoint : Type := CP {
  cp_pc : Z;
  cp_regs : list expr;
  cp_know : list kentry;
  cp_nx : nat;
  cp_F : list SGP.region;
  cp_PSS : list SR.post_spec;
  cp_meas : expr
}.

Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.

Abbreviation mk fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

Definition At (c : cutpoint) (E : env) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  regs_ok E (cp_regs c) R /\ know_ok segs E M (cp_know c).
Definition meas (c : cutpoint) (E : env) : Z := bv_unsigned (edenot E (cp_meas c)).

Record leaf_facts (c : cutpoint) (ps : SR.post_spec) (E' : env) (R' : bvmap 5 word) (M M' : word -> option byte) : Prop := LF {
  lf_regs : forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e;
  lf_x0 : getr R' (Z_to_bv 5 0) = Z_to_bv 64 0;
  lf_flat : SGP.regions_ok E' (cp_F c);
  lf_frame : forall a : word, SGP.outside E' (cp_F c) a -> M' a = M a;
  lf_cells : forall K, In K (SR.ps_cells ps) -> kentry_ok segs E' M' K;
  lf_grows : mem_grows M M' }.

Definition plan_sound (c : cutpoint) : Prop :=
  forall (fx : FPState) E R M, regs_ok E (cp_regs c) R -> know_ok segs E M (cp_know c) ->
  exists (fx' : FPState) E' R' M' k ps,
       nth_error (cp_PSS c) k = Some ps
    /\ env_agree (cp_nx c) E E'
    /\ msteps segs (mk fx R (cp_pc c) M) (mk fx' R' (SR.ps_pc ps) M')
    /\ leaf_facts c ps E' R' M M'.

Section Cert.
Variable CPS : list cutpoint.

Variable Amb : nat -> env -> (word -> option byte) -> Model -> Prop.
Variable K : ShapeAlg.TSet.

Variable FPI : FPState -> Prop.
Hypothesis FPI_msteps : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps segs (mk fx R pc M) (mk fx' R' pc' M') -> FPI fx -> FPI fx'.

Definition IH (mu : Z) : Prop :=
  forall j cj (fx2 : FPState) E2 R2 M2 model2,
    nth_error CPS j = Some cj -> At cj E2 R2 M2 -> Amb j E2 M2 model2 -> FPI fx2 -> meas cj E2 < mu ->
    srealizes segs SCFG (mkCfg (mk fx2 R2 (cp_pc cj) M2) model2) K.

Definition leaf_ok (i : nat) (c : cutpoint) (ps : SR.post_spec) : Prop :=
  forall (fx' : FPState) E R M model E' R' M',
    At c E R M -> Amb i E M model -> FPI fx' ->
    env_agree (cp_nx c) E E' -> leaf_facts c ps E' R' M M' ->
    IH (meas c E) ->
    srealizes segs SCFG (mkCfg (mk fx' R' (SR.ps_pc ps) M') model) K.

Hypothesis PLANS : forall i c, nth_error CPS i = Some c -> plan_sound c.
Hypothesis LEAVES : forall i c k ps, nth_error CPS i = Some c -> nth_error (cp_PSS c) k = Some ps -> leaf_ok i c ps.
Hypothesis AMB_MODEL : forall i E M model, Amb i E M model -> m_halted model = None /\ m_vm_lazy model = [].

Theorem cutcert_sound :
  forall i c (fx : FPState) E R M model,
    nth_error CPS i = Some c -> At c E R M -> Amb i E M model -> FPI fx ->
    srealizes segs SCFG (mkCfg (mk fx R (cp_pc c) M) model) K.
Proof.
  assert (G : forall n : nat, forall i c (fx : FPState) E R M model,
             nth_error CPS i = Some c -> At c E R M -> Amb i E M model -> FPI fx -> (Z.to_nat (meas c E) < n)%nat ->
             srealizes segs SCFG (mkCfg (mk fx R (cp_pc c) M) model) K).
  { induction n as [|n IHn]; intros i c fx E R M model Hc HAt HAmb HFP Hn; [lia|].
    destruct HAt as [HR HK].
    destruct (PLANS i c Hc fx E R M HR HK) as (fx' & E' & R' & M' & k & ps & Hps & Hag & Hms & HLF).
    destruct (AMB_MODEL i E M model HAmb) as [Hh Hl].
    eapply L5.cps_of_msteps; [exact Hh | exact Hl | exact Hms |].
    eapply (LEAVES i c k ps Hc Hps fx' E R M model E' R' M'); [split; assumption | exact HAmb | exact (FPI_msteps _ _ _ _ _ _ _ _ Hms HFP) | exact Hag | exact HLF |].
    intros j cj fx2 E2 R2 M2 model2 Hcj HAt2 HAmb2 HFP2 Hlt.
    eapply IHn; [exact Hcj | exact HAt2 | exact HAmb2 | exact HFP2 |].
    unfold meas in *. pose proof (bv_unsigned_in_range _ (edenot E2 (cp_meas cj))) as B2.
    pose proof (bv_unsigned_in_range _ (edenot E (cp_meas c))) as B1. lia. }
  intros i c fx E R M model Hc HAt HAmb HFP. eapply (G (S (Z.to_nat (meas c E)))); eauto.
Qed.

Variable NF : nat.
Definition MB : Z := 4611686018427387904.

Definition has_cell (cells : list kentry) (X : kentry) : bool := existsb (APC.kentry_eqb X) cells.
Definition goto_chk (c : cutpoint) (ps : SR.post_spec) (cj : cutpoint) (s : subst) : bool :=
  (Z.eqb (SR.ps_pc ps) (cp_pc cj)
   && Nat.leb NF (cp_nx c)
   && forallb (fun r => existsb (fun ie : nat * expr => Nat.eqb (fst ie) r && expr_eqb (snd ie) (esubstL NF s (nth r (cp_regs cj) (ELit 0))))
                                (SR.ps_regs ps)) (seq 1 31)
   && forallb (fun X => has_cell (SR.ps_cells ps) (ksubstL NF s X)) (cp_know cj)
   && APC.expr_vars_lt (cp_nx c) (cp_meas c)
   && has_cell (SR.ps_cells ps) (KRange (APC.esub (cp_meas c) (esubstL NF s (cp_meas cj))) 1 MB)
   && has_cell (SR.ps_cells ps) (KRange (cp_meas c) 0 MB)
   && has_cell (SR.ps_cells ps) (KRange (esubstL NF s (cp_meas cj)) 0 MB))%bool.

Lemma has_cell_In : forall cells X, has_cell cells X = true -> In X cells.
Proof.
  intros cells X H. unfold has_cell in H. apply existsb_exists in H as (Y & HY & Heq).
  apply APS.kentry_eqb_eq in Heq. subst Y. exact HY.
Qed.

Lemma reg_of_ridx : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
  intros r. unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. rewrite Z2Nat.id by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact B.
Qed.

Lemma goto_chk_sound : forall c ps cj s E E' R' M M',
  goto_chk c ps cj s = true -> env_agree (cp_nx c) E E' -> leaf_facts c ps E' R' M M' ->
  SR.ps_pc ps = cp_pc cj /\ At cj (env_over NF s E') R' M' /\ meas cj (env_over NF s E') < meas c E
  /\ env_agree NF E (env_over NF s E').
Proof.
  intros c ps cj s E E' R' M M' H Hag HLF. unfold goto_chk in H.
  repeat (apply andb_prop in H as [H ?X]).
  apply Z.eqb_eq in H. apply Nat.leb_le in X5.
  apply has_cell_In in X, X0, X1.
  split; [exact H|]. split; [split|split].
  -
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Er.
    + assert (r = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Er; apply Z.eqb_eq in Er; exact Er).
      cbn [edenot]. replace (0%bv : bv 5) with (Z_to_bv 5 0) by (apply bv_eq; reflexivity). exact (lf_x0 _ _ _ _ _ _ HLF).
    + assert (Hr : (1 <= ridx r < 32)%nat).
      { unfold ridx. pose proof (bv_unsigned_in_range _ r) as B. change (bv_modulus 5) with 32 in B.
        unfold bv_eqb in Er. apply Z.eqb_neq in Er. change (bv_unsigned (0%bv : bv 5)) with 0 in Er. lia. }
      rewrite forallb_forall in X4. specialize (X4 (ridx r)).
      assert (Hin : In (ridx r) (seq 1 31)) by (apply in_seq; lia).
      apply X4 in Hin. apply existsb_exists in Hin as ([i e] & Hie & Hb). cbn [fst snd] in Hb.
      apply andb_prop in Hb as [Hi He]. apply Nat.eqb_eq in Hi. apply expr_eqb_eq in He. subst i.
      destruct (lf_regs _ _ _ _ _ _ HLF _ _ Hie) as [_ Hg]. rewrite reg_of_ridx in Hg. rewrite Hg, He.
      apply esubstL_denot.
  -
    unfold know_ok. apply Forall_forall. intros X' HX'. rewrite forallb_forall in X3. specialize (X3 X' HX').
    apply has_cell_In in X3. apply (kentry_ok_ksubstL segs NF s E' M' X'). exact (lf_cells _ _ _ _ _ _ HLF _ X3).
  -
    unfold meas. rewrite <- esubstL_denot.
    rewrite (edenot_agree (cp_nx c) E E' (cp_meas c) Hag X2).
    pose proof (lf_cells _ _ _ _ _ _ HLF _ X1) as F1. pose proof (lf_cells _ _ _ _ _ _ HLF _ X0) as F2.
    pose proof (lf_cells _ _ _ _ _ _ HLF _ X) as F3. cbn [kentry_ok] in F1, F2, F3.
    unfold APC.esub in F1. rewrite mkAlu_denot, u_sub64 in F1. unfold MB in *.
    set (a := bv_unsigned (edenot E' (cp_meas c))) in *. set (b := bv_unsigned (edenot E' (esubstL NF s (cp_meas cj)))) in *.
    destruct (Z_lt_le_dec b a) as [Hlt|Hge]; [exact Hlt|exfalso].
    destruct (Z.eq_dec a b) as [->|Hne].
    + rewrite Z.sub_diag, Z.mod_0_l in F1 by lia. lia.
    + assert (Hm : (a - b) mod 2 ^ 64 = a - b + 2 ^ 64).
      { rewrite <- (Z_mod_plus_full (a - b) 1 (2 ^ 64)). rewrite Z.mul_1_l. apply Z.mod_small.
        pose proof (bv_unsigned_in_range _ (edenot E' (cp_meas c))) as Ba.
        pose proof (bv_unsigned_in_range _ (edenot E' (esubstL NF s (cp_meas cj)))) as Bb.
        fold a in Ba. fold b in Bb. change (bv_modulus 64) with (2 ^ 64) in *. lia. }
      rewrite Hm in F1. lia.
  - eapply env_agree_trans; [eapply env_agree_le; [exact Hag | exact X5] | apply env_over_agree].
Qed.

Definition amb_goto (i : nat) (c : cutpoint) (ps : SR.post_spec) (j : nat) (s : subst) : Prop :=
  forall E R M model E' R' M',
    At c E R M -> Amb i E M model -> env_agree (cp_nx c) E E' -> leaf_facts c ps E' R' M M' ->
    Amb j (env_over NF s E') M' model.

Lemma leaf_goto : forall i c ps j cj s,
  nth_error CPS j = Some cj -> goto_chk c ps cj s = true -> amb_goto i c ps j s -> leaf_ok i c ps.
Proof.
  intros i c ps j cj s Hcj Hchk Hamb fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  destruct (goto_chk_sound c ps cj s E E' R' M M' Hchk Hag HLF) as (Hpc & HAt' & Hm & _).
  rewrite Hpc. eapply (HIH j cj); [exact Hcj | exact HAt' | | exact HFP | exact Hm].
  eapply Hamb; eassumption.
Qed.

End Cert.

Inductive tag : Type :=
| TGoto (j : nat) (s : subst)
| TOther (id : Z).

Section Tagged.
Variable CPS : list cutpoint.
Variable TAGS : list (list tag).
Variable NF : nat.
Variable Amb : nat -> env -> (word -> option byte) -> Model -> Prop.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.

Fixpoint leaves_chk (c : cutpoint) (pss : list SR.post_spec) (tags : list tag) : bool :=
  match pss, tags with
  | [], [] => true
  | ps :: pr, t :: tr =>
      (match t with
       | TGoto j s => match nth_error CPS j with Some cj => goto_chk NF c ps cj s | None => false end
       | TOther _ => true
       end && leaves_chk c pr tr)%bool
  | _, _ => false
  end.
Fixpoint tags_chk_go (cps : list cutpoint) (tgs : list (list tag)) : bool :=
  match cps, tgs with
  | [], [] => true
  | c :: cr, t :: tr => (leaves_chk c (cp_PSS c) t && tags_chk_go cr tr)%bool
  | _, _ => false
  end.
Definition tags_chk : bool := tags_chk_go CPS TAGS.

Lemma leaves_chk_nth : forall c pss tags k ps, leaves_chk c pss tags = true -> nth_error pss k = Some ps ->
  exists t, nth_error tags k = Some t
    /\ match t with
       | TGoto j s => exists cj, nth_error CPS j = Some cj /\ goto_chk NF c ps cj s = true
       | TOther _ => True
       end.
Proof.
  intros c pss. induction pss as [|p pr IHp]; intros tags k ps H Hk; [destruct k; discriminate|].
  destruct tags as [|t tr]; [discriminate|]. cbn [leaves_chk] in H. apply andb_prop in H as [H1 H2].
  destruct k as [|k]; cbn [nth_error] in *.
  - injection Hk as <-. exists t. split; [reflexivity|]. destruct t as [j s|id]; [|exact I].
    destruct (nth_error CPS j) as [cj|]; [|discriminate]. exists cj. split; [reflexivity | exact H1].
  - exact (IHp tr k ps H2 Hk).
Qed.
Lemma tags_chk_go_nth : forall cps tgs i c, tags_chk_go cps tgs = true -> nth_error cps i = Some c ->
  exists tags, nth_error tgs i = Some tags /\ leaves_chk c (cp_PSS c) tags = true.
Proof.
  intros cps. induction cps as [|c0 cr IHc]; intros tgs i c H Hi; [destruct i; discriminate|].
  destruct tgs as [|t tr]; [discriminate|]. cbn [tags_chk_go] in H. apply andb_prop in H as [H1 H2].
  destruct i as [|i]; cbn [nth_error] in *.
  - injection Hi as <-. exists t. split; [reflexivity | exact H1].
  - exact (IHc tr i c H2 Hi).
Qed.

Fixpoint others_leaves (P : SR.post_spec -> Z -> bool) (pss : list SR.post_spec) (tags : list tag) : bool :=
  match pss, tags with
  | ps :: pr, t :: tr => (match t with TOther id => P ps id | TGoto _ _ => true end && others_leaves P pr tr)%bool
  | _, _ => true
  end.
Fixpoint others_go (P : nat -> SR.post_spec -> Z -> bool) (i : nat) (cps : list cutpoint) (tgs : list (list tag)) : bool :=
  match cps, tgs with
  | c :: cr, t :: tr => (others_leaves (P i) (cp_PSS c) t && others_go P (S i) cr tr)%bool
  | _, _ => true
  end.
Definition others_all (P : nat -> SR.post_spec -> Z -> bool) : bool := others_go P 0 CPS TAGS.
Lemma others_leaves_sound : forall P pss tags k ps id, others_leaves P pss tags = true ->
  nth_error pss k = Some ps -> nth_error tags k = Some (TOther id) -> P ps id = true.
Proof.
  intros P pss. induction pss as [|p pr IHp]; intros tags k ps id H Hps Ht; [destruct k; discriminate|].
  destruct tags as [|t tr]; [destruct k; discriminate|]. cbn [others_leaves] in H. apply andb_prop in H as [H1 H2].
  destruct k as [|k]; cbn [nth_error] in *; [injection Hps as <-; injection Ht as ->; exact H1 | exact (IHp tr k ps id H2 Hps Ht)].
Qed.
Lemma others_go_sound : forall P cps tgs i0 i c tags k ps id, others_go P i0 cps tgs = true ->
  nth_error cps i = Some c -> nth_error tgs i = Some tags -> nth_error (cp_PSS c) k = Some ps -> nth_error tags k = Some (TOther id) ->
  P (i0 + i)%nat ps id = true.
Proof.
  intros P cps. induction cps as [|c0 cr IHc]; intros tgs i0 i c tags k ps id H Hc Htg Hps Ht; [destruct i; discriminate|].
  destruct tgs as [|t tr]; [destruct i; discriminate|]. cbn [others_go] in H. apply andb_prop in H as [H1 H2].
  destruct i as [|i]; cbn [nth_error] in *.
  - injection Hc as <-. injection Htg as <-. rewrite Nat.add_0_r. exact (others_leaves_sound _ _ _ _ _ _ H1 Hps Ht).
  - replace (i0 + S i)%nat with (S i0 + i)%nat by lia. exact (IHc tr (S i0) i c tags k ps id H2 Hc Htg Hps Ht).
Qed.
Lemma others_all_sound : forall P, others_all P = true ->
  forall i c tags k ps id, nth_error CPS i = Some c -> nth_error TAGS i = Some tags ->
    nth_error (cp_PSS c) k = Some ps -> nth_error tags k = Some (TOther id) -> P i ps id = true.
Proof. intros P H i c tags k ps id Hc Htg Hps Ht. exact (others_go_sound P CPS TAGS 0 i c tags k ps id H Hc Htg Hps Ht). Qed.

Fixpoint cps_go (Q : nat -> cutpoint -> bool) (i : nat) (cps : list cutpoint) : bool :=
  match cps with [] => true | c :: cr => (Q i c && cps_go Q (S i) cr)%bool end.
Definition cps_all (Q : nat -> cutpoint -> bool) : bool := cps_go Q 0 CPS.
Lemma cps_go_sound : forall Q cps i0 i c, cps_go Q i0 cps = true -> nth_error cps i = Some c -> Q (i0 + i)%nat c = true.
Proof.
  intros Q cps. induction cps as [|c0 cr IHc]; intros i0 i c H Hc; [destruct i; discriminate|].
  cbn [cps_go] in H. apply andb_prop in H as [H1 H2]. destruct i as [|i]; cbn [nth_error] in Hc.
  - injection Hc as <-. rewrite Nat.add_0_r. exact H1.
  - replace (i0 + S i)%nat with (S i0 + i)%nat by lia. exact (IHc (S i0) i c H2 Hc).
Qed.
Lemma cps_all_sound : forall Q, cps_all Q = true -> forall i c, nth_error CPS i = Some c -> Q i c = true.
Proof. intros Q H i c Hc. exact (cps_go_sound Q CPS 0 i c H Hc). Qed.

Theorem cutcert_sound_tagged :
  (forall (fx fx' : FPState) R pc M R' pc' M', msteps segs (mk fx R pc M) (mk fx' R' pc' M') -> FPI fx -> FPI fx') ->
  (forall i c, nth_error CPS i = Some c -> plan_sound c) ->
  tags_chk = true ->
  (forall i E M model, Amb i E M model -> m_halted model = None /\ m_vm_lazy model = []) ->
  (forall i c tags k ps j s, nth_error CPS i = Some c -> nth_error TAGS i = Some tags ->
       nth_error (cp_PSS c) k = Some ps -> nth_error tags k = Some (TGoto j s) -> amb_goto Amb NF i c ps j s) ->
  (forall i c tags k ps id, nth_error CPS i = Some c -> nth_error TAGS i = Some tags ->
       nth_error (cp_PSS c) k = Some ps -> nth_error tags k = Some (TOther id) -> leaf_ok CPS Amb K FPI i c ps) ->
  forall i c (fx : FPState) E R M model,
    nth_error CPS i = Some c -> At c E R M -> Amb i E M model -> FPI fx ->
    srealizes segs SCFG (mkCfg (mk fx R (cp_pc c) M) model) K.
Proof.
  intros FPM PLANS TCHK AMBM GOTOS OTHERS.
  apply (cutcert_sound CPS Amb K FPI FPM PLANS); [|exact AMBM].
  intros i c k ps Hc Hps.
  destruct (tags_chk_go_nth CPS TAGS i c TCHK Hc) as (tags & Htags & Hl).
  destruct (leaves_chk_nth c (cp_PSS c) tags k ps Hl Hps) as (t & Ht & Hm).
  destruct t as [j s|id].
  - destruct Hm as (cj & Hcj & Hg). eapply leaf_goto; [exact Hcj | exact Hg |]. eapply GOTOS; eassumption.
  - eapply OTHERS; eassumption.
Qed.
End Tagged.

End WithSegs.
End CC.
