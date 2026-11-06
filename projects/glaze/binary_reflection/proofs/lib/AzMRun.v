(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module MR.
Import AX2. Import AX2S. Import AX2B.

(* [comment removed for export] *)
Inductive msel : Type := SExpr (e : expr) | SReg (r : nat).
Definition sel_expr (s : msel) (sr : list expr) : expr :=
  match s with SExpr e => e | SReg r => nth r sr (ELit 0) end.

Inductive mplan : Type :=
| MRun (stops : list Z) (k : mplan)
| MCase (s : msel) (mid : Z) (k1 k2 : mplan)
| MJoin (s : msel) (mid : Z) (stops : list Z) (k : mplan)
| MDrop (b : expr) (lo hi : Z) (k : mplan)
| MSpin.

(* [comment removed for export] *)
Definition kaddr (K : kentry) : option saddr :=
  match K with
  | KWord a _ _ | KZero a _ | KBlob a _ _ | KFill a _ _ | KUnk a _ => Some a
  | _ => None
  end.
Definition keepf (b : expr) (lo hi : Z) (K : kentry) : bool :=
  match kaddr K with
  | Some (SA b' o) => negb (expr_eqb b b' && Z.leb lo o && Z.ltb o hi)
  | None => true
  end.

Section Chk.
Variable segs : list Segment.
Variable IT : itab.
Variable KC : nat.
Variable BF : nat.
Variable SPIN : Z.

Definition blockB (stops : list Z) (pc : Z) (sr : list expr) (kn : list kentry) (nx : nat) : sym_state :=
  sym_execTXBI segs (mkbc (facts_of kn)) (mk_kix kn) IT KC BF true stops (SS pc sr [] kn nx).

Fixpoint mcheck (p : mplan) (pc : Z) (sr : list expr) (kn : list kentry) (nx : nat) {struct p} : bool :=
  AzSymRun3.sr_vars_lt nx sr && AzSymRun3.kn_vars_lt nx kn &&
  match p with
  | MSpin => Z.eqb pc SPIN
  | MRun stops k =>
      let ss' := blockB stops pc sr kn nx in
      match carryK (mkbc (facts_of (s_know ss'))) (s_log ss') (s_know ss') [] with
      | (kn', [], _) => mcheck k (s_pc ss') (s_regs ss') kn' (s_next ss')
      | _ => false
      end
  | MCase s mid k1 k2 =>
      let e := sel_expr s sr in
      match APC.brange kn e with
      | Some (lo, hi) =>
          if (Z.leb lo mid && Z.ltb mid hi)%bool
          then mcheck k1 pc sr (KRange e lo mid :: kn) nx && mcheck k2 pc sr (KRange e (mid + 1) hi :: kn) nx
          else if Z.leb hi mid then mcheck k1 pc sr kn nx else mcheck k2 pc sr kn nx
      | None => false
      end
  | MJoin s mid stops k =>
      let e := sel_expr s sr in
      match APC.brange kn e with
      | Some (lo, hi) =>
          let kn1 := KRange e lo mid :: kn in
          let kn2 := KRange e (mid + 1) hi :: kn in
          let s1 := blockB stops pc sr kn1 nx in
          let s2 := blockB stops pc sr kn2 nx in
          AzSymRun3.kn_vars_lt nx kn1 &&
          match s_log s1, s_log s2 with
          | [], [] =>
              Z.eqb (s_pc s1) (s_pc s2) &&
              (let '(rj, nx') := regs_join 32 (s_regs s1) (s_regs s2) (Nat.max (s_next s1) (s_next s2)) in
               mcheck k (s_pc s1) rj kn nx')
          | _, _ => false
          end
      | None => false
      end
  | MDrop b lo hi k => mcheck k pc sr (List.filter (keepf b lo hi) kn) nx
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis IT_ok : itab_sound segs IT.

Lemma blockB_eq : forall stops pc sr kn nx,
  blockB stops pc sr kn nx = sym_execTX segs IT KC BF true stops (SS pc sr [] kn nx).
Proof. intros. unfold blockB. apply sym_execTXBI_eq. reflexivity. Qed.

Lemma mkst_regs_inj : forall fx fx' R R' pc pc' M M' rom rom',
  @mkst fx R pc M rom = @mkst fx' R' pc' M' rom' -> R = R'.
Proof. intros. apply (f_equal ms_regs) in H. exact H. Qed.

Lemma know_ok_filter : forall E M f kn, know_ok segs E M kn -> know_ok segs E M (List.filter f kn).
Proof.
  intros E M f kn H. unfold know_ok in *. rewrite Forall_forall in *. intros K HK. apply filter_In in HK. apply H. tauto.
Qed.


Theorem mcheck_sound : forall p pc sr kn nx,
  mcheck p pc sr kn nx = true ->
  forall E R M rom fx, regs_ok E sr R -> know_ok segs E M kn -> fx_ok fx ->
  exists fx' R' M', msteps segs (@mkst fx R (Z_to_bv 64 pc) M rom) (@mkst fx' R' (Z_to_bv 64 SPIN) M' rom).
Proof.
  induction p as [stops k IHk | s mid k1 IH1 k2 IH2 | s mid stops k IHk | b lo hi k IHk | ];
    intros pc sr kn nx Hc E R M rom fx HR HK HF; cbn [mcheck] in Hc;
    apply andb_prop in Hc as [Hv Hc]; apply andb_prop in Hv as [Hvs Hvk].
  - (* [comment removed for export] *)
    rewrite blockB_eq in Hc.
    pose proof (AzSymRun3.runTX_sound segs IT KC BF stops pc sr kn nx E M rom R fx IT_ok HR HK HF Hvs Hvk) as RUN.
    cbv zeta in RUN.
    set (ss' := sym_execTX segs IT KC BF true stops (SS pc sr [] kn nx)) in *.
    destruct RUN as (E' & R' & fx' & Ha & Hle & HF' & HR' & Hlf & HK' & Hms & _).
    rewrite carryK_eq in Hc.
    destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs'] eqn:Hcar.
    destruct scs as [|sc scs]; [|discriminate].
    assert (HK'' : know_ok segs E' (mem_denot E' M (s_log ss')) kn').
    { eapply AzSymRun3.carry_after; [exact Hcar | exact Hlf | exact HK' | constructor]. }
    destruct (IHk _ _ _ _ Hc E' R' (mem_denot E' M (s_log ss')) rom fx' HR' HK'' HF') as (fx2 & R2 & M2 & Hms2).
    exists fx2, R2, M2. eapply msteps_trans; [exact Hms | exact Hms2].
  - (* [comment removed for export] *)
    cbv zeta in Hc. set (e := sel_expr s sr) in *. clearbody e.
    destruct (APC.brange kn e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (APS.brange_sound segs E M kn e lo hi HK Hr) as Hb.
    destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
    + apply andb_prop in Hc as [Hc1 Hc2].
      destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
      * apply (IH1 _ _ _ _ Hc1 E R M rom fx HR); [|exact HF]. constructor; [cbn [kentry_ok]; lia | exact HK].
      * apply (IH2 _ _ _ _ Hc2 E R M rom fx HR); [|exact HF]. constructor; [cbn [kentry_ok]; lia | exact HK].
    + destruct (Z.leb hi mid); [exact (IH1 _ _ _ _ Hc E R M rom fx HR HK HF) | exact (IH2 _ _ _ _ Hc E R M rom fx HR HK HF)].
  - (* [comment removed for export] *)
    cbv zeta in Hc. set (e := sel_expr s sr) in *. clearbody e.
    destruct (APC.brange kn e) as [[lo hi]|] eqn:Hr; [|discriminate].
    pose proof (APS.brange_sound segs E M kn e lo hi HK Hr) as Hb.
    cbv zeta in Hc. rewrite !blockB_eq in Hc.
    apply andb_prop in Hc as [Hvk1 Hc].
    assert (Hvk2 : AzSymRun3.kn_vars_lt nx (KRange e (mid + 1) hi :: kn) = true).
    { cbn [AzSymRun3.kn_vars_lt AzSymRun3.kentry_vars_lt] in Hvk1 |- *. exact Hvk1. }
    set (kn1 := KRange e lo mid :: kn) in *. set (kn2 := KRange e (mid + 1) hi :: kn) in *.
    set (s1 := sym_execTX segs IT KC BF true stops (SS pc sr [] kn1 nx)) in *.
    set (s2 := sym_execTX segs IT KC BF true stops (SS pc sr [] kn2 nx)) in *.
    destruct (s_log s1) as [|? ?] eqn:Hl1; [|discriminate].
    destruct (s_log s2) as [|? ?] eqn:Hl2; [|discriminate].
    apply andb_prop in Hc as [Hpc Hc]. apply Z.eqb_eq in Hpc.
    destruct (regs_join 32 (s_regs s1) (s_regs s2) (Nat.max (s_next s1) (s_next s2))) as [rj nx'] eqn:Hj.
    (* [comment removed for export] *)
    assert (ARM : forall (sel : bool) (knA : list kentry),
              knA = (if sel then kn1 else kn2) ->
              know_ok segs E M knA -> AzSymRun3.kn_vars_lt nx knA = true ->
              exists fx' R' M', msteps segs (@mkst fx R (Z_to_bv 64 pc) M rom) (@mkst fx' R' (Z_to_bv 64 SPIN) M' rom)).
    { intros sel knA HknA HKA HvA.
      pose proof (AzSymRun3.runTX_sound segs IT KC BF stops pc sr knA nx E M rom R fx IT_ok HR HKA HF Hvs HvA) as RUN.
      cbv zeta in RUN.
      set (sA := sym_execTX segs IT KC BF true stops (SS pc sr [] knA nx)) in *.
      assert (HsA : sA = if sel then s1 else s2) by (unfold sA; rewrite HknA; destruct sel; reflexivity).
      destruct RUN as (E1 & R1 & fx1 & Ha & Hle & HF1 & HR1 & Hlf & HK1 & Hms & HALL).
      assert (HlA : s_log sA = []) by (rewrite HsA; destruct sel; assumption).
      assert (HpA : s_pc sA = s_pc s1) by (rewrite HsA; destruct sel; [reflexivity | symmetry; exact Hpc]).
      rewrite HlA in Hms, HALL. cbn [mem_denot] in Hms, HALL.
      assert (HnA : (s_next sA <= Nat.max (s_next s1) (s_next s2))%nat) by (rewrite HsA; destruct sel; lia).
      destruct (regs_join_regs_ok 31 (s_regs s1) (s_regs s2) (Nat.max (s_next s1) (s_next s2)) rj nx' E1 R1 sel eq_refl Hj)
        as (E2 & Ha2 & Hle2 & HR2).
      { intros E'' Ha''.
        assert (Hag : AzSymRun3.env_agree (s_next sA) E1 E'').
        { apply AzSymRun3.eagree_env_agree. eapply eagree_le; [exact Ha'' | exact HnA]. }
        destruct (HALL E'' Hag) as (r0 & f0 & Heq & _ & Hr0 & _).
        apply mkst_regs_inj in Heq. subst r0.
        replace (if sel then s_regs s1 else s_regs s2) with (s_regs sA) by (rewrite HsA; destruct sel; reflexivity).
        exact Hr0. }
      assert (HR2' : regs_ok E2 rj R1) by (apply HR2; apply eagree_refl).
      assert (HK2 : know_ok segs E2 M kn).
      { eapply (AzSymRun3.know_ok_agree segs nx E E2 M kn); [|exact Hvk|exact HK].
        apply AzSymRun3.eagree_env_agree.
        eapply eagree_trans; [apply AzSymRun3.eagree_env_agree; exact Ha|].
        eapply eagree_le; [exact Ha2 | lia]. }
      destruct (IHk _ _ _ _ Hc E2 R1 M rom fx1 HR2' HK2 HF1) as (fx3 & R3 & M3 & Hms3).
      exists fx3, R3, M3. eapply msteps_trans; [exact Hms|]. rewrite HpA. exact Hms3. }
    destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
    + apply (ARM true kn1 eq_refl); [|exact Hvk1]. constructor; [cbn [kentry_ok]; lia | exact HK].
    + apply (ARM false kn2 eq_refl); [|exact Hvk2]. constructor; [cbn [kentry_ok]; lia | exact HK].
  - (* [comment removed for export] *)
    apply (IHk _ _ _ _ Hc E R M rom fx HR); [apply know_ok_filter; exact HK | exact HF].
  - (* [comment removed for export] *)
    apply Z.eqb_eq in Hc. subst pc. exists fx, R, M. apply mst_refl.
Qed.

End Chk.
End MR.
