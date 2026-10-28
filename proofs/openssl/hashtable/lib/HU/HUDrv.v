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

(* [comment removed for export] *)
Record grpd : Type := GD { g_N0 : nat; g_S0 : acs; g_sub : sub; g_a0s : list a0d; g_leaves : list leafd; g_ops : list opd;
                           g_shapeB : shape; g_sC2s : list shape }.
Definition g_facts (v : a0d) (l : leafd) (o : opd) : list kentry := a0_F v ++ ld_F l ++ od_F o.

(* [comment removed for export] *)
Fixpoint cover_ok (tab : list (Z * Z)) (a b : Z) : bool :=
  match tab with
  | [] => Z.ltb b a
  | (lo, hi) :: r => (Z.leb lo a && (Z.leb b hi || cover_ok r (hi + 1) b))%bool
  end.
Lemma cover_ok_sound : forall tab a b, cover_ok tab a b = true -> forall n, a <= n <= b -> exists p, In p tab /\ fst p <= n <= snd p.
Proof.
  induction tab as [|[lo hi] r IH]; intros a b H n Hn; cbn [cover_ok] in H.
  - apply Z.ltb_lt in H. lia.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
    destruct (Z_le_gt_dec n hi) as [Hle|Hgt]; [exists (lo, hi); split; [left; reflexivity | cbn; lia]|].
    apply orb_prop in H2 as [H2|H2]; [apply Z.leb_le in H2; lia|].
    destruct (IH (hi + 1) b H2 n ltac:(lia)) as [p [Hp Hr]]. exists p. split; [right; exact Hp | exact Hr].
Qed.

Section Drv.
  Variable sp : word.
  Variable STR0 : Z.
  Variable LIM : Z.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  #[local] Notation CSOK PHI := (cs_ok HSEGS H0T LIM (SINVg PHI sp STR0) (argHt STR0) (bv_unsigned sp) fs).

  Variable S0 : acs.                       (* [comment removed for export] *)
  Hypothesis S0_log : s_log (a_ss S0) = [].

  (* [comment removed for export] *)
  Definition grp_stmt (G : grpd) : Prop :=
    forall v l o, In v (g_a0s G) -> In l (g_leaves G) -> In o (g_ops G) ->
    forall PHI0 : env -> Prop, (forall E E', env_agree (g_N0 G) E E' -> PHI0 E -> PHI0 E') ->
      (forall E, PHI0 E -> Forall (pure_holds E) (a0_F v) /\ Forall (pure_holds E) (ld_F l) /\ Forall (pure_holds E) (od_F o)) ->
      forall E R FULL model, CSOK PHI0 E (stA0 (g_S0 G) v) R FULL model ->
        crz HSEGS (cfg_of HSEGS R (pc (g_S0 G)) FULL model) (DEN (g_shapeB G) (g_sC2s G) E (m_fs model)).
  (* [comment removed for export] *)
  Definition grp_side (G : grpd) : bool :=
    (sig_vars_lt (g_N0 G) (g_sub G)
     && forallb (fun v => forallb (fun l => forallb (fun o => F_ok (g_N0 G) (g_facts v l o)) (g_ops G)) (g_leaves G)) (g_a0s G))%bool.

  Variable groups : list grpd.
  Hypothesis HG : forall G, In G groups -> grp_stmt G.
  Hypothesis HBASE : forall G, In G groups -> g_S0 G = inst_list S0 (g_sub G).
  Hypothesis HSIDE : forallb grp_side groups = true.

  Definition sel_ok (E : env) (G : grpd) (v : a0d) (l : leafd) (o : opd) : Prop :=
    In G groups /\ In v (g_a0s G) /\ In l (g_leaves G) /\ In o (g_ops G)
    /\ sig_holds E (g_sub G) /\ Forall (pure_holds E) (g_facts v l o).

  Theorem drive_sel : forall (PHIb : env -> Prop) E R FULL model G v l o,
    sel_ok E G v l o -> CSOK PHIb E S0 R FULL model ->
    crz HSEGS (cfg_of HSEGS R (pc S0) FULL model) (DEN (g_shapeB G) (g_sC2s G) E (m_fs model)).
  Proof.
    intros PHIb E R FULL model G v l o (HGin & Hv & Hl & Ho & Hsig & Hfacts) HC.
    pose proof (proj1 (forallb_forall _ _) HSIDE G HGin) as Hside. unfold grp_side in Hside. apply andb_prop in Hside as [Hsv Hfo].
    pose proof (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) Hfo v Hv) l Hl) o Ho) as HFok.
    set (PHI0 := fun E' : env => sig_holds E' (g_sub G) /\ Forall (pure_holds E') (g_facts v l o)).
    assert (PA : forall E1 E2, env_agree (g_N0 G) E1 E2 -> PHI0 E1 -> PHI0 E2).
    { intros E1 E2 Hag [H1 H2]. split; [exact (sig_holds_agree (g_N0 G) (g_sub G) E1 E2 Hag Hsv H1) | exact (pure_agree (g_N0 G) _ E1 E2 Hag HFok H2)]. }
    assert (PF : forall E1, PHI0 E1 -> Forall (pure_holds E1) (a0_F v) /\ Forall (pure_holds E1) (ld_F l) /\ Forall (pure_holds E1) (od_F o)).
    { intros E1 [_ H2]. unfold g_facts in H2. apply Forall_app in H2 as [A1 H2]. apply Forall_app in H2 as [A2 A3]. repeat split; assumption. }
    pose proof (csok_phi sp STR0 LIM fs PHIb PHI0 E S0 R FULL model ltac:(intros _; split; assumption) HC) as HC0.
    pose proof (spec_back sp STR0 LIM fs PHI0 (g_sub G) (a0_F v) S0 E R FULL model
                  ltac:(intros E0 HP; split; [exact (proj1 HP) | exact (proj1 (PF E0 HP))]) S0_log HC0) as HC1.
    pose proof (HG G HGin v l o Hv Hl Ho PHI0 PA PF E R FULL model) as HR.
    unfold stA0 in HR. rewrite (HBASE G HGin) in HR. specialize (HR HC1).
    rewrite pc_inst_list in HR. exact HR.
  Qed.

  (* [comment removed for export] *)
  Variable content : Type.
  Variable EOK : content -> env -> Prop.          (* [comment removed for export] *)
  Variable TARGET : content -> Fs.Fs -> TSet.     (* [comment removed for export] *)
  Hypothesis SELECT : forall c E, EOK c E -> exists G v l o, sel_ok E G v l o.
  Hypothesis DEN_TARGET : forall c E G v l o fs0, EOK c E -> sel_ok E G v l o ->
    ShapeAlg.t_eq (DEN (g_shapeB G) (g_sC2s G) E fs0) (TARGET c fs0).

  Theorem family_drive : forall (PHIb : env -> Prop) c E R FULL model,
    CSOK PHIb E S0 R FULL model -> EOK c E ->
    crz HSEGS (cfg_of HSEGS R (pc S0) FULL model) (TARGET c (m_fs model)).
  Proof.
    intros PHIb c E R FULL model HC HE.
    destruct (SELECT c E HE) as (G & v & l & o & Hsel).
    exact (crz_conseq HSEGS _ _ _ (drive_sel PHIb E R FULL model G v l o Hsel HC) (DEN_TARGET c E G v l o (m_fs model) HE Hsel)).
  Qed.
End Drv.
