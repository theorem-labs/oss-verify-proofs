(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxBatch HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop HUBatch HUFam.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Record leaf2 : Type := L2 { l2_F : list kentry; l2_pA1 : plan; l2_h : nat; l2_arms : list leafd }.
(* [comment removed for export] *)
Definition l2_view (L : leaf2) : leafd := LDX (l2_F L) (l2_pA1 L) [] [] PExit [] [].
(* [comment removed for export] *)
Definition ARM (s : sub) (fp : list kentry) (c : plan) (r : list sub) (x : list (nat * plan)) : leafd := LDX [] PExit s fp c r x.

Section Fam2.
  Variable sp : word.
  Variable STR0 : Z.
  Variable LIM : Z.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  Variables BF FUEL : nat.
  Variable rs : list (Z * nat).

  #[local] Notation CSOK PHI := (cs_ok HSEGS H0T LIM (SINVg PHI sp STR0) (argHt STR0) (bv_unsigned sp) fs).
  #[local] Notation CHECK NX HS := (CAP.check HSEGS (APC.mk_itab_ranges HSEGS rs) H0T NX LIM (g0_XN NX LIM) (g0_XE NX) g0_XB HS 0 true false false BF FUEL None).

  Variables N0 NA NB NC ND VSA VSB VSC VSD : nat.
  Variables S0 TA1 TB : acs.
  Variables TCs TDs : list acs.
  Variable a0s : list a0d.
  Variable leaves2 : list leaf2.
  Variable ops : list opd.
  Variable shapeB : shape.
  Variable sC2s : list shape.

  (* [comment removed for export] *)
  Definition arms : list leafd := flat_map l2_arms leaves2.
  Fixpoint tg_arms (i : nat) (l : list leafd) : list (nat * htgt) :=
    match l with [] => [] | a :: r => ((1000 * i)%nat, (TB, ld_sig a, ld_Fp a)) :: tg_arms (S i) r end.
  Definition tgA1c (L : leaf2) : list (nat * htgt) := tg_arms 0 (l2_arms L).
  Definition stA1c (L : leaf2) : acs := add_kn TA1 (l2_F L).
  Definition mkA1c (L : leaf2) : hjob := HJ NA (tgA1c L) (stA1c L) (l2_pA1 L) (SHole (l2_h L)).

  Hypothesis JA0 : allok LIM BF FUEL rs _ (mkA0 N0 S0 TA1) a0s.
  Hypothesis JA1 : allok LIM BF FUEL rs _ mkA1c leaves2.
  Hypothesis JB : allok LIM BF FUEL rs _ (mkB NB S0 TB TCs shapeB) ops.
  Hypothesis JC1 : allok LIM BF FUEL rs _ (mkC1 NC S0 TCs TDs) (list_prod arms (classes TCs)).
  Hypothesis JC2 : allok LIM BF FUEL rs _ (mkC2 ND S0 TDs sC2s) (flat_map od_holes ops).
  Hypothesis SIDE : side_ok N0 NA NB NC ND VSA VSB VSC VSD S0 TA1 TB TCs TDs a0s arms ops shapeB sC2s = true.

  #[local] Notation DEN0 := (DEN shapeB sC2s).

  Lemma tg_arms_in : forall l i h t, assoc h (tg_arms i l) = Some t -> exists a, In a l /\ t = (TB, ld_sig a, ld_Fp a).
  Proof.
    induction l as [|a r IH]; intros i h t H; cbn [tg_arms assoc] in H; [discriminate|].
    destruct (Nat.eqb (1000 * i) h).
    - injection H as <-. exists a. split; [left; reflexivity | reflexivity].
    - destruct (IH (S i) h t H) as [a' [Hin Heq]]. exists a'. split; [right; exact Hin | exact Heq].
  Qed.
  Lemma tg_arms_in' : forall l i h t, In (h, t) (tg_arms i l) -> exists a, In a l /\ t = (TB, ld_sig a, ld_Fp a).
  Proof.
    induction l as [|a r IH]; intros i h t Hi; cbn [tg_arms] in Hi; [destruct Hi|].
    destruct Hi as [Hi|Hi]; [injection Hi as _ <-; exists a; split; [left; reflexivity | reflexivity]|].
    destruct (IH (S i) h t Hi) as [a' [Ha' He]]. exists a'. split; [right; exact Ha' | exact He].
  Qed.

  Section Chain2.
    Variable v : a0d. Variable L : leaf2. Variable o : opd.
    Hypothesis Hv : In v a0s. Hypothesis HL : In L leaves2. Hypothesis Ho : In o ops.
    Variable PHI0 : env -> Prop.
    Hypothesis PHI0_agree : forall E E', env_agree N0 E E' -> PHI0 E -> PHI0 E'.
    Hypothesis PHI0_facts : forall E, PHI0 E -> Forall (pure_holds E) (a0_F v) /\ Forall (pure_holds E) (l2_F L) /\ Forall (pure_holds E) (od_F o).

    #[local] Notation PHI1c := (PHI1 v PHI0).

    Lemma arm_in : forall a, In a (l2_arms L) -> In a arms.
    Proof. intros a Ha. unfold arms. apply in_flat_map. exists L. split; assumption. Qed.

    (* [comment removed for export] *)
    Lemma side2 : (N0 <= NA)%nat /\ (NX0t <= NA)%nat /\ CAP.expr_vars_lt NA e_spw = true /\ (NA <= VSB)%nat
                  /\ (NX0t <= N0)%nat /\ CAP.expr_vars_lt N0 e_spw = true /\ (N0 <= VSA)%nat
                  /\ ht_ok VSA (TA1, a0_sig v, a0_Fx v) = true /\ lvl_ok (a0_sig v) (a0_Fx v) NA = true
                  /\ forall a, In a arms -> ht_ok VSB (TB, ld_sig a, ld_Fp a) = true.
    Proof.
      pose proof SIDE as X. unfold side_ok in X. do 21 (apply andb_prop in X; destruct X as [X ?]).
      repeat match goal with H : nx_ok _ = true |- _ => unfold nx_ok in H; apply andb_prop in H; destruct H as [? ?] end.
      repeat match goal with H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H end.
      match goal with H : forallb _ a0s = true |- _ => pose proof (proj1 (forallb_forall _ _) H v Hv) as Y end.
      do 4 (apply andb_prop in Y; destruct Y as [Y ?]).
      repeat split; try assumption.
      intros a Ha. match goal with H : forallb _ arms = true |- _ => pose proof (proj1 (forallb_forall _ _) H a Ha) as Z end.
      do 4 (apply andb_prop in Z; destruct Z as [Z ?]). exact Z.
    Qed.

    (* [comment removed for export] *)
    Lemma A1c_thm : forall E R FULL model, CSOK PHI1c E (stA1c L) R FULL model -> crz HSEGS (cfg_of HSEGS R (pc (stA1c L)) FULL model) (DEN0 E (m_fs model)).
    Proof.
      intros E R FULL model HC.
      destruct side2 as (N0A & NA_ge & NA_spw & NAB & _ & _ & _ & _ & HvA & Harm).
      assert (PA1 : forall E1 E2, env_agree NA E1 E2 -> PHI1c E1 -> PHI1c E2).
      { exact (PHI1_agree LIM N0 NA NB NC ND VSA VSB VSC VSD S0 TA1 TB TCs TDs a0s arms ops shapeB sC2s SIDE v PHI0 PHI0_agree NA (le_n _) HvA). }
      assert (HOK : forallb (fun p => ht_ok VSB (snd p)) (tgA1c L) = true).
      { apply forallb_forall. intros [h t] Hin. cbn [snd]. unfold tgA1c in Hin.
        destruct (tg_arms_in' _ _ _ _ Hin) as [a [Ha ->]]. exact (Harm a (arm_in a Ha)). }
      refine (hop_sound sp STR0 LIM fs Hsp Hstr Hstr8 BF FUEL NA VSB NA_ge NA_spw NAB PHI1c PA1 (tgA1c L) HOK
                (fun _ => DEN0) (fun _ => DEN_agree N0 NA NB NC ND VSA VSB VSC VSD S0 TA1 TB TCs TDs a0s arms ops shapeB sC2s SIDE NA N0A)
                (fun _ => DEN_nil shapeB sC2s) (fun _ _ _ => eq_refl) _
                rs (stA1c L) (l2_pA1 L) (SHole (l2_h L)) (JA1 L HL) E R FULL model HC).
      intros h0 t Ht E1 R1 FULL1 model1 HC1'. unfold tgA1c in Ht.
      destruct (tg_arms_in _ _ _ _ Ht) as [a [Ha ->]]. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      pose proof (arm_in a Ha) as Hain.
      change (PHI_ext PHI1c (ld_sig a) (ld_Fp a)) with (PHI2 v a PHI0) in HC1'.
      pose proof (add_facts sp STR0 LIM fs (PHI2 v a PHI0) (od_F o) TB E1 R1 FULL1 model1
                    ltac:(intros E0 ((HP0 & _) & _); exact (proj2 (proj2 (PHI0_facts E0 HP0)))) HC1') as HC2'.
      pose proof (B_thm sp STR0 LIM fs Hsp Hstr Hstr8 BF FUEL rs N0 NA NB NC ND VSA VSB VSC VSD S0 TA1 TB TCs TDs a0s arms ops shapeB sC2s
                    JB JC1 JC2 SIDE v a o Hv Hain Ho (PHI2 v a PHI0)
                    (PHI2_agree LIM N0 NA NB NC ND VSA VSB VSC VSD S0 TA1 TB TCs TDs a0s arms ops shapeB sC2s SIDE v a PHI0 PHI0_agree)
                    ltac:(intros E0 (_ & Hs0 & Hf0); split; assumption) E1 R1 FULL1 model1 HC2') as HR.
      unfold stB in HR. change (pc (add_kn TB (od_F o))) with (pc TB) in HR. exact HR.
    Qed.

    (* [comment removed for export] *)
    Theorem fam_sound2 : forall E R FULL model, CSOK PHI0 E (stA0 S0 v) R FULL model -> crz HSEGS (cfg_of HSEGS R (pc S0) FULL model) (DEN0 E (m_fs model)).
    Proof.
      intros E R FULL model HC.
      destruct side2 as (N0A & _ & _ & _ & N0_ge & N0_spw & N0V & HvOK & _ & _).
      assert (HOK : forallb (fun p => ht_ok VSA (snd p)) (tgA0 TA1 v) = true) by (unfold tgA0; cbn [forallb snd]; rewrite HvOK; reflexivity).
      change (pc S0) with (pc (stA0 S0 v)).
      refine (hop_sound sp STR0 LIM fs Hsp Hstr Hstr8 BF FUEL N0 VSA N0_ge N0_spw N0V PHI0 PHI0_agree (tgA0 TA1 v) HOK
                (fun _ => DEN0) (fun _ => DEN_agree N0 NA NB NC ND VSA VSB VSC VSD S0 TA1 TB TCs TDs a0s arms ops shapeB sC2s SIDE N0 (le_n _))
                (fun _ => DEN_nil shapeB sC2s) (fun _ _ _ => eq_refl) _
                rs (stA0 S0 v) (a0_plan v) (SHole 0) (JA0 v Hv) E R FULL model HC).
      intros h0 t Ht E1 R1 FULL1 model1 HC1'. unfold tgA0 in Ht. cbn [assoc] in Ht.
      destruct (Nat.eqb 0 h0); [|discriminate]. injection Ht as <-. unfold ht_T, ht_s, ht_F in *. cbn [fst snd] in *.
      change (PHI_ext PHI0 (a0_sig v) (a0_Fx v)) with PHI1c in HC1'.
      pose proof (add_facts sp STR0 LIM fs PHI1c (l2_F L) TA1 E1 R1 FULL1 model1
                    ltac:(intros E0 (HP0 & _); exact (proj1 (proj2 (PHI0_facts E0 HP0)))) HC1') as HC2'.
      pose proof (A1c_thm E1 R1 FULL1 model1 HC2') as HR.
      unfold stA1c in HR. change (pc (add_kn TA1 (l2_F L))) with (pc TA1) in HR. exact HR.
    Qed.
  End Chain2.

  (* [comment removed for export] *)
  Theorem fam_sound2_view : forall v l o, In v a0s -> In l (map l2_view leaves2) -> In o ops ->
    forall PHI0 : env -> Prop, (forall E E', env_agree N0 E E' -> PHI0 E -> PHI0 E') ->
      (forall E, PHI0 E -> Forall (pure_holds E) (a0_F v) /\ Forall (pure_holds E) (ld_F l) /\ Forall (pure_holds E) (od_F o)) ->
      forall E R FULL model, CSOK PHI0 E (stA0 S0 v) R FULL model -> crz HSEGS (cfg_of HSEGS R (pc S0) FULL model) (DEN0 E (m_fs model)).
  Proof.
    intros v l o Hv Hl Ho PHI0 PA PF. apply in_map_iff in Hl as [L [<- HL]].
    exact (fam_sound2 v L o Hv HL Ho PHI0 PA PF).
  Qed.
End Fam2.
