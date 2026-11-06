(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad MemImageType RiscvSemantics Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uaccess Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap Madvise.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common.BudgetBridge Require Import Relim LimArms LimVm LimMremap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arm_124 : LI (fun i => sched_yield_spec i).
Proof. arm_start. li. Qed.

Lemma spec_table_ARM : Forall (fun a => ARM (sa_no a) (sa_spec a)) spec_table.
Proof.
  unfold spec_table.
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_17)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_19)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_20)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_21)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_22)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_23)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_24)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_25)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_29)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_32)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_35)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_46)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_48)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_56)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_57)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_59)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_61)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_62)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_63)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_64)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_65)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_66)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_67)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_68)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_72)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_73)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_78)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_79)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_80)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_82)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_83)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_85)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_93)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_94)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_96)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_98)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_101)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_113)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_119)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_123)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_124)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_130)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_131)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_132)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_134)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_135)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_144)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_146)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_147)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_149)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_157)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_158)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_159)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_160)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_167)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_169)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_172)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_174)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_175)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_176)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_177)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_178)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_198)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_199)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_200)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_201)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_202)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_203)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_204)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_205)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_206)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_207)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_208)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_209)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_210)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_211)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_212)|].
  apply Forall_cons; [exact (arm_214)|].
  apply Forall_cons; [exact (ARM_of_LIV _ _ arm_215)|].
  apply Forall_cons; [exact (arm_216)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_220)|].
  apply Forall_cons; [exact (arm_222)|].
  apply Forall_cons; [exact (arm_226)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_233)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_242)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_260)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_261)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_278)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_435)|].
  apply Forall_cons; [exact (ARM_of_LI _ _ arm_439)|].
  apply Forall_nil.
Qed.

Lemma lookup_arm_In : forall t n a, lookup_arm t n = Some a -> In a t /\ sa_no a = n.
Proof.
  induction t as [|x t IH]; intros n a H; [discriminate H|]. cbn [lookup_arm] in H.
  destruct (Z.eqb (sa_no x) n) eqn:E.
  - injection H as <-. split; [left; reflexivity| apply Z.eqb_eq; exact E].
  - destruct (IH n a H) as [Hin Hno]. split; [right; exact Hin| exact Hno].
Qed.

Theorem syscall_spec_ARM : forall i m o l, syscall_spec i m o ->
  ofrV m o /\
  (INV m -> alloc_budget_refused_b i m = false -> alloc_budget_refused_b i (relim l m) = false ->
   syscall_spec i (relim l m) (relimo l o)).
Proof.
  intros i m o l H. unfold syscall_spec, dispatch in *.
  destruct (lookup_arm spec_table (bv_unsigned (in_sysno i))) as [a|] eqn:E.
  - destruct (lookup_arm_In _ _ _ E) as [Hin Hno].
    exact (proj1 (Forall_forall _ _) spec_table_ARM a Hin i m o l (eq_sym Hno) H).
  - unfold unmodeled in H. subst o. split; [exact I| intros; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leb_up x l L : (l <= L)%Z -> negb (x <=? l)%Z = false -> negb (x <=? L)%Z = false.
Proof. intros HL H. apply true_of_negb_false in H. apply Z.leb_le in H. rewrite (proj2 (Z.leb_le _ _)); [reflexivity| lia]. Qed.

Ltac unrelim2 :=
  unrelim;
  repeat match goal with
  | |- context [min_brk (m_vmmaps (relim ?l ?m))] => change (min_brk (m_vmmaps (relim l m))) with (min_brk (m_vmmaps m))
  | |- context [vm_brk (m_vmmaps (relim ?l ?m))] => change (vm_brk (m_vmmaps (relim l m))) with (vm_brk (m_vmmaps m))
  | |- context [vm_limit (m_vmmaps (relim ?l ?m))] => change (vm_limit (m_vmmaps (relim l m))) with l
  | |- context [vm_backing_used (relim ?l ?m)] => rewrite (vm_backing_used_relim l m)
  | |- context [mremap_source_b (m_vmmaps (relim ?l ?m))] => change (mremap_source_b (m_vmmaps (relim l m))) with (mremap_source_b (m_vmmaps m))
  | |- context [mremap_backing_uniform_b (relim ?l ?m)] => change (mremap_backing_uniform_b (relim l m)) with (mremap_backing_uniform_b m)
  | |- context [mremap_move_charge (relim ?l ?m)] => change (mremap_move_charge (relim l m)) with (mremap_move_charge m)
  | |- context [mremap_model_next (relim ?l ?m) ?a ?b ?c ?d] => rewrite (mremap_model_next_relim l m a b c d)
  | |- context [mprotect_model_next (relim ?l ?m) ?a ?b] => change (mprotect_model_next (relim l m) a b) with (relim l (mprotect_model_next m a b))
  | |- context [with_vmmaps ?h (relim ?l ?m)] => change (with_vmmaps h (relim l m)) with (relim l (with_vmmaps h m))
  | |- context [with_mmap_replacement ?f ?a ?n (relim ?l ?m)] => rewrite (with_mmap_replacement_relim f a n l m)
  | |- context [mmap_fixed_rw_next (m_vmmaps (relim ?l ?m)) ?a ?n] =>
      change (mmap_fixed_rw_next (m_vmmaps (relim l m)) a n) with (relim_maps l (mmap_fixed_rw_next (m_vmmaps m) a n))
  | |- context [mmap_fixed_rw_span_next (m_vmmaps (relim ?l ?m)) ?a ?n] =>
      change (mmap_fixed_rw_span_next (m_vmmaps (relim l m)) a n) with (relim_maps l (mmap_fixed_rw_span_next (m_vmmaps m) a n))
  | |- context [with_vmmaps (relim_maps ?l ?h) ?m] => change (with_vmmaps (relim_maps l h) m) with (relim l (with_vmmaps h m))
  end.

(* [comment removed for export] *)
Ltac anti_ifs :=
  repeat (match goal with |- context [if ?b then _ else _] => destruct b end; try reflexivity; try discriminate).

Lemma abr_up : forall i m l L, (l <= L)%Z ->
  alloc_budget_refused_b i (relim l m) = false -> alloc_budget_refused_b i (relim L m) = false.
Proof.
  intros i m l L HL. unfold alloc_budget_refused_b. cbv zeta.
  destruct (bv_unsigned (in_sysno i) =? 214)%Z.
  { unfold brk_budget_refused_b, brk_budget_ok. cbv zeta. unrelim2.
    destruct (negb _ && _ && _); cbn [andb]; [apply leb_up; exact HL| reflexivity]. }
  destruct (bv_unsigned (in_sysno i) =? 216)%Z.
  { unfold mremap_budget_refused_b, mremap_final_budget_b, mremap_move_budget_b, vm_backing_within_limit. cbv zeta. unrelim2.
    match goal with |- context [mmap_fixed_rw_next] => idtac | _ => idtac end.
    anti_ifs. intros H. apply true_of_negb_false in H. apply andb_true_iff in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.leb_le _ _)); [reflexivity| lia| ].
    revert H1. unrelim2. intros H1. lia. }
  destruct (bv_unsigned (in_sysno i) =? 222)%Z.
  { unfold mmap_budget_refused_b, mmap_noreserve_backed_ok, mmap_fixed_rw_budget_ok, mmap_fixed_rw_span_budget_ok,
      vm_backing_within_limit. cbv zeta. unrelim2.
    rewrite ?m_vmmaps_with_mmap_replacement. unrelim2.
    anti_ifs; apply leb_up; exact HL. }
  destruct (bv_unsigned (in_sysno i) =? 226)%Z.
  { unfold mprotect_budget_refused_b, mprotect_budget_ok, vm_backing_within_limit. cbv zeta. unrelim2.
    anti_ifs; apply leb_up; exact HL. }
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma materialize_relim : forall l m acc,
  materialize_model_accesses (relim l m) acc =
  match materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) l acc with
  | Some pages => Some (relim l (with_vm_backing (m_vm_lazy m) pages m))
  | None => None
  end.
Proof. intros. reflexivity. Qed.

Lemma materialize_accesses_mono : forall lz mt u l L acc p, (l <= L)%Z ->
  materialize_accesses lz mt u l acc = Some p -> materialize_accesses lz mt u L acc = Some p.
Proof.
  intros lz mt u l L acc p HL. unfold materialize_accesses. cbv zeta.
  destruct (newly_materialized_pages lz mt acc); [exact (fun H => H)|].
  destruct (u + _ * _ <=? l)%Z eqn:E; [| discriminate]. apply Z.leb_le in E.
  rewrite (proj2 (Z.leb_le _ _)); [exact (fun H => H)| lia].
Qed.

Lemma materialize_accesses_down : forall lz mt u l L acc p,
  materialize_accesses lz mt u L acc = Some p ->
  materialize_accesses lz mt u l acc = Some p \/ materialize_accesses lz mt u l acc = None.
Proof.
  intros lz mt u l L acc p. unfold materialize_accesses. cbv zeta.
  destruct (newly_materialized_pages lz mt acc); [intros H; left; exact H|].
  destruct (u + _ * _ <=? L)%Z; [| discriminate]. intros H. injection H as <-.
  destruct (u + _ * _ <=? l)%Z; [left| right]; reflexivity.
Qed.

Lemma materialize_up : forall l L m acc m2, (l <= L)%Z ->
  materialize_model_accesses (relim l m) acc = Some m2 ->
  materialize_model_accesses (relim L m) acc = Some (relim L m2).
Proof.
  intros l L m acc m2 HL. rewrite !materialize_relim.
  destruct (materialize_accesses _ _ _ l acc) as [p|] eqn:E; [| discriminate].
  rewrite (materialize_accesses_mono _ _ _ _ _ _ _ HL E). intros H. injection H as <-. reflexivity.
Qed.

Lemma materialize_down : forall l L m acc m2,
  materialize_model_accesses (relim L m) acc = Some m2 ->
  materialize_model_accesses (relim l m) acc = Some (relim l m2) \/ materialize_model_accesses (relim l m) acc = None.
Proof.
  intros l L m acc m2. rewrite !materialize_relim.
  destruct (materialize_accesses _ _ _ L acc) as [p|] eqn:E; [| discriminate].
  intros H. injection H as <-.
  destruct (materialize_accesses_down _ _ _ l _ _ _ E) as [-> | ->]; [left| right]; reflexivity.
Qed.

Lemma materialize_none_down : forall l L m acc, (l <= L)%Z ->
  materialize_model_accesses (relim L m) acc = None -> materialize_model_accesses (relim l m) acc = None.
Proof.
  intros l L m acc HL H. destruct (materialize_model_accesses (relim l m) acc) as [m2|] eqn:E; [| reflexivity].
  rewrite (materialize_up _ _ _ _ _ HL E) in H. discriminate H.
Qed.

Lemma materialize_frame : forall m acc m2, materialize_model_accesses m acc = Some m2 ->
  mlim m2 = mlim m /\ (INV m -> INV m2).
Proof.
  intros m acc m2 H. pose proof (materialize_model_accesses_frame _ _ _ H) as (_ & E & _).
  unfold mlim, INV. rewrite E. split; [reflexivity| exact (fun X => X)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition relim_cfg (l : Z) (c : config) : config := mkCfg (cfg_ms c) (relim l (cfg_model c)).

Definition relim_to (l : Z) (r : step_to) : step_to :=
  match r with SNext c => SNext (relim_cfg l c) | SError => SError end.

(* [comment removed for export] *)

(* [comment removed for export] *)

Section Step.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma marks_off : forall lo l' ms m x8,
  (lo <= l')%Z -> m_halted m = None -> ms_svc_pending ms = Some x8 ->
  ~ budget_refused_at segs (relim_cfg lo (mkCfg ms m)) ->
  alloc_budget_refused_b (sys_input segs ms x8) (relim l' m) = false.
Proof.
  intros lo l' ms m x8 HL Hh Hsvc NB. apply (abr_up _ _ _ _ HL).
  destruct (alloc_budget_refused_b (sys_input segs ms x8) (relim lo m)) eqn:E; [| reflexivity].
  exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. left. exact E.
Qed.

Theorem sstep_relim : forall lo l' c evs r,
  (lo <= l')%Z -> (lo <= mlim (cfg_model c))%Z -> INV (cfg_model c) ->
  ~ budget_refused_at segs (relim_cfg lo c) ->
  sstep segs c evs r ->
  sstep segs (relim_cfg l' c) evs (relim_to l' r)
  /\ (forall c2, r = SNext c2 -> mlim (cfg_model c2) = mlim (cfg_model c) /\ INV (cfg_model c2)).
Proof.
  intros lo l' c evs r HL Hlo HI NB ST.
  assert (Hid : forall m, relim (mlim m) m = m) by (intros; apply relim_id).
  destruct ST as [ms m ms' m' Hh Hsvc Hacc | ms m Hh Hsvc Hacc | ms m Hh Hsvc Hacc
    | ms m x8 eff m' m'' evs0 Hh Hsvc Hspec Hh' Hmat | ms m x8 eff m' evs0 Hh Hsvc Hspec Hh' Hmat
    | ms m x8 eff m' evs0 code Hh Hsvc Hspec Hh' Hk | ms m x8 eff m' evs0 sig Hh Hsvc Hspec Hk | ms m x8 Hh Hsvc Hspec];
    cbn [cfg_model cfg_ms] in *; unfold relim_cfg, relim_to; cbn [cfg_model cfg_ms].
  - (* [comment removed for export] *)
    unfold mi_account_step in Hacc.
    destruct (step_accesses segs ms) as [report| |] eqn:Hsa; [| discriminate| discriminate].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1|] eqn:Hmat; [| discriminate].
    injection Hacc as <- <-. split.
    + apply sstep_instr; [exact Hh| exact Hsvc|]. unfold mi_account_step. rewrite Hsa.
      rewrite <- (Hid m) in Hmat.
      destruct (materialize_down lo _ _ _ _ Hmat) as [Hlo'|Hnone].
      * rewrite (materialize_up _ _ _ _ _ HL Hlo'). rewrite relim_relim. reflexivity.
      * exfalso. apply NB. split; [exact Hh|]. left. split; [exact Hsvc|]. exists report. split; [exact Hsa| exact Hnone].
    + intros c2 E. injection E as <-. cbn [cfg_model]. destruct (materialize_frame _ _ _ Hmat) as [F1 F2]. split; [exact F1| exact (F2 HI)].
  - (* [comment removed for export] *)
    split; [| intros c2 E; discriminate E].
    apply sstep_instr_fault; [exact Hh| exact Hsvc|]. unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report| |] eqn:Hsa; [| reflexivity| discriminate].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1|] eqn:Hmat; [discriminate|].
    exfalso. apply NB. split; [exact Hh|]. left. split; [exact Hsvc|]. exists report. split; [exact Hsa|].
    cbn [cfg_model]. rewrite <- (Hid m) in Hmat. exact (materialize_none_down _ _ _ _ Hlo Hmat).
  - (* [comment removed for export] *)
    split; [| intros c2 E; discriminate E].
    apply sstep_instr_unmodeled; [exact Hh| exact Hsvc|]. unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report| |] eqn:Hsa; [| discriminate| reflexivity].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate.
  - (* [comment removed for export] *)
    pose proof (marks_off lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
    pose proof (marks_off lo lo ms m x8 (Z.le_refl lo) Hh Hsvc NB) as Mlo.
    pose proof (marks_off lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ l' Hspec) as [[Fl FI] S']. specialize (S' HI Mm Ml').
    destruct (syscall_spec_ARM _ _ _ lo Hspec) as [_ Slo]. specialize (Slo HI Mm Mlo). cbn [relimo] in *.
    split.
    + rewrite <- (Hid m') in Hmat. destruct (materialize_down lo _ _ _ _ Hmat) as [Hlo'|Hnone].
      * eapply sstep_syscall; [exact Hh| exact Hsvc| exact S'| exact Hh'|].
        rewrite (materialize_up _ _ _ _ _ HL Hlo'). rewrite relim_relim. reflexivity.
      * exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. right.
        exists eff, (relim lo m'), evs0. split; [exact Slo|]. split; [exact Hh'|]. exact Hnone.
    + intros c2 E. injection E as <-. cbn [cfg_model].
      destruct (materialize_frame _ _ _ Hmat) as [F2 I2]. split; [congruence| exact (I2 (FI HI))].
  - (* [comment removed for export] *)
    split; [| intros c2 E; discriminate E].
    pose proof (marks_off lo lo ms m x8 (Z.le_refl lo) Hh Hsvc NB) as Mlo.
    pose proof (marks_off lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ lo Hspec) as [[Fl _] Slo]. specialize (Slo HI Mm Mlo). cbn [relimo] in *.
    exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. right.
    exists eff, (relim lo m'), evs0. split; [exact Slo|]. split; [exact Hh'|].
    rewrite <- (Hid m'), Fl in Hmat. exact (materialize_none_down _ _ _ _ Hlo Hmat).
  - (* [comment removed for export] *)
    pose proof (marks_off lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
    pose proof (marks_off lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ l' Hspec) as [[Fl FI] S']. specialize (S' HI Mm Ml'). cbn [relimo] in *.
    split.
    + change (m_fs m') with (m_fs (relim l' m')). eapply sstep_exit; [exact Hh| exact Hsvc| exact S'| exact Hh'| exact Hk].
    + intros c2 E. injection E as <-. cbn [cfg_model]. split; [exact Fl| exact (FI HI)].
  - (* [comment removed for export] *)
    pose proof (marks_off lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
    pose proof (marks_off lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ l' Hspec) as [[Fl FI] S']. specialize (S' HI Mm Ml'). cbn [relimo] in *.
    split.
    + change (m_fs m') with (m_fs (relim l' m')). eapply sstep_killed; [exact Hh| exact Hsvc| exact S'| exact Hk].
    + intros c2 E. injection E as <-. cbn [cfg_model]. split; [exact Fl| exact (FI HI)].
  - (* [comment removed for export] *)
    split; [| intros c2 E; discriminate E].
    pose proof (marks_off lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
    pose proof (marks_off lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ l' Hspec) as [_ S']. specialize (S' HI Mm Ml'). cbn [relimo] in *.
    eapply sstep_syscall_unmodeled; [exact Hh| exact Hsvc| exact S'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem star_relim : forall lo l' c tr c',
  star segs c tr c' ->
  (lo <= l')%Z -> (lo <= mlim (cfg_model c))%Z -> INV (cfg_model c) ->
  ~ reaches_budget_refused segs (relim_cfg lo c) ->
  star segs (relim_cfg l' c) tr (relim_cfg l' c')
  /\ mlim (cfg_model c') = mlim (cfg_model c) /\ INV (cfg_model c')
  /\ ~ reaches_budget_refused segs (relim_cfg lo c').
Proof.
  intros lo l' c tr c' ST. induction ST as [c | c1 evs c2 tr c3 Hs ST IH]; intros HL Hlo HI NR.
  - split; [apply star_refl|]. split; [reflexivity|]. split; [exact HI| exact NR].
  - assert (NB : ~ budget_refused_at segs (relim_cfg lo c1)).
    { intros B. apply NR. apply reaches_budget_refused_intro. exact B. }
    destruct (sstep_relim lo l' c1 evs (SNext c2) HL Hlo HI NB Hs) as [S' F]. destruct (F c2 eq_refl) as [Fl FI].
    destruct (sstep_relim lo lo c1 evs (SNext c2) (Z.le_refl lo) Hlo HI NB Hs) as [Slo _].
    assert (NR2 : ~ reaches_budget_refused segs (relim_cfg lo c2)).
    { intros R. apply NR. eapply reaches_budget_refused_star; [apply star_one; exact Slo| exact R]. }
    destruct (IH HL ltac:(rewrite Fl; exact Hlo) FI NR2) as (ST' & Fl' & FI' & NR').
    split; [eapply star_step; [exact S'| exact ST']|]. split; [congruence|]. split; [exact FI'| exact NR'].
Qed.

Theorem obs_trace_relim : forall lo l' c tr,
  (lo <= l')%Z -> (lo <= mlim (cfg_model c))%Z -> INV (cfg_model c) ->
  ~ reaches_budget_refused segs (relim_cfg lo c) ->
  obs_trace segs c tr -> obs_trace segs (relim_cfg l' c) tr.
Proof.
  intros lo l' c tr HL Hlo HI NR (tr' & c' & ST & P).
  exists tr', (relim_cfg l' c'). split; [exact (proj1 (star_relim _ _ _ _ _ ST HL Hlo HI NR))| exact P].
Qed.

Theorem reaches_error_relim : forall lo l' c,
  (lo <= l')%Z -> (lo <= mlim (cfg_model c))%Z -> INV (cfg_model c) ->
  ~ reaches_budget_refused segs (relim_cfg lo c) ->
  reaches_error segs c -> reaches_error segs (relim_cfg l' c).
Proof.
  intros lo l' c HL Hlo HI NR (tr & c' & evs & ST & SE).
  destruct (star_relim _ _ _ _ _ ST HL Hlo HI NR) as (ST' & Fl & FI & NR').
  exists tr, (relim_cfg l' c'), evs. split; [exact ST'|].
  refine (proj1 (sstep_relim lo l' c' evs SError HL _ FI _ SE)); [rewrite Fl; exact Hlo|].
  intros B. apply NR'. apply reaches_budget_refused_intro. exact B.
Qed.

(* [comment removed for export] *)
End Step.

Section StepCfg.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma refusal_b_relim : forall i l m r, refusal_b i (relim l m) r = refusal_b i m r.
Proof. reflexivity. Qed.

Lemma spurious_relim : forall lo l' ms m x8 eff,
  (lo <= l')%Z -> (lo <= mlim m)%Z -> INV m -> m_halted m = None -> ms_svc_pending ms = Some x8 ->
  ~ budget_refused_at segs (relim_cfg lo (mkCfg ms m)) ->
  spurious_refusal_cfg cfg (sys_input segs ms x8) (relim l' m) eff ->
  spurious_refusal_cfg cfg (sys_input segs ms x8) m eff.
Proof.
  intros lo l' ms m x8 eff HL Hlo HI Hh Hsvc NB (Hoff & Hr & (eff' & m' & evs' & Hspec' & Hnr)).
  split; [exact Hoff|]. split; [rewrite <- (refusal_b_relim _ l'); exact Hr|].
  pose proof (marks_off segs lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
  pose proof (marks_off segs lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm.
  destruct (syscall_spec_ARM _ _ _ (mlim m) Hspec') as [_ S]. specialize (S HI Ml' Mm).
  rewrite relim_relim, relim_id in S. cbn [relimo] in S.
  exists eff', (relim (mlim m) m'), evs'. split; [exact S|]. rewrite <- (refusal_b_relim _ l'). exact Hnr.
Qed.

Theorem sstep_cfg_relim : forall lo l' c evs r,
  (lo <= l')%Z -> (lo <= mlim (cfg_model c))%Z -> INV (cfg_model c) ->
  ~ budget_refused_at segs (relim_cfg lo c) ->
  sstep_cfg segs cfg c evs r ->
  sstep_cfg segs cfg (relim_cfg l' c) evs (relim_to l' r)
  /\ (forall c2, r = SNext c2 -> mlim (cfg_model c2) = mlim (cfg_model c) /\ INV (cfg_model c2)).
Proof.
  intros lo l' c evs r HL Hlo HI NB ST.
  split; [| exact (proj2 (sstep_relim segs lo l' c evs r HL Hlo HI NB (sstep_cfg_sub segs cfg _ _ _ ST)))].
  assert (Hid : forall m, relim (mlim m) m = m) by (intros; apply relim_id).
  destruct ST as [ms m ms' m' Hh Hsvc Hacc | ms m Hh Hsvc Hacc | ms m Hh Hsvc Hacc
    | ms m x8 eff m' m'' evs0 Hh Hsvc Hspec Hns Hh' Hmat | ms m x8 eff m' evs0 Hh Hsvc Hspec Hns Hh' Hmat
    | ms m x8 eff m' evs0 code Hh Hsvc Hspec Hh' Hk | ms m x8 eff m' evs0 sig Hh Hsvc Hspec Hk | ms m x8 Hh Hsvc Hspec];
    cbn [cfg_model cfg_ms] in *; unfold relim_cfg, relim_to; cbn [cfg_model cfg_ms].
  - unfold mi_account_step in Hacc.
    destruct (step_accesses segs ms) as [report| |] eqn:Hsa; [| discriminate| discriminate].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1|] eqn:Hmat; [| discriminate].
    injection Hacc as <- <-.
    apply sstep_cfg_instr; [exact Hh| exact Hsvc|]. unfold mi_account_step. rewrite Hsa.
    rewrite <- (Hid m) in Hmat.
    destruct (materialize_down lo _ _ _ _ Hmat) as [Hlo'|Hnone].
    + rewrite (materialize_up _ _ _ _ _ HL Hlo'). rewrite relim_relim. reflexivity.
    + exfalso. apply NB. split; [exact Hh|]. left. split; [exact Hsvc|]. exists report. split; [exact Hsa| exact Hnone].
  - apply sstep_cfg_instr_fault; [exact Hh| exact Hsvc|]. unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report| |] eqn:Hsa; [| reflexivity| discriminate].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)) as [m1|] eqn:Hmat; [discriminate|].
    exfalso. apply NB. split; [exact Hh|]. left. split; [exact Hsvc|]. exists report. split; [exact Hsa|].
    cbn [cfg_model]. rewrite <- (Hid m) in Hmat. exact (materialize_none_down _ _ _ _ Hlo Hmat).
  - apply sstep_cfg_instr_unmodeled; [exact Hh| exact Hsvc|]. unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report| |] eqn:Hsa; [| discriminate| reflexivity].
    destruct (materialize_model_accesses m (@accessed_ranges _ report)); discriminate.
  - pose proof (marks_off segs lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
    pose proof (marks_off segs lo lo ms m x8 (Z.le_refl lo) Hh Hsvc NB) as Mlo.
    pose proof (marks_off segs lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ l' Hspec) as [_ S']. specialize (S' HI Mm Ml').
    destruct (syscall_spec_ARM _ _ _ lo Hspec) as [_ Slo]. specialize (Slo HI Mm Mlo). cbn [relimo] in *.
    rewrite <- (Hid m') in Hmat. destruct (materialize_down lo _ _ _ _ Hmat) as [Hlo'|Hnone].
    + eapply sstep_cfg_syscall; [exact Hh| exact Hsvc| exact S'| | exact Hh'|].
      * intros Sp. exact (Hns (spurious_relim lo l' ms m x8 eff HL Hlo HI Hh Hsvc NB Sp)).
      * rewrite (materialize_up _ _ _ _ _ HL Hlo'). rewrite relim_relim. reflexivity.
    + exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. right.
      exists eff, (relim lo m'), evs0. split; [exact Slo|]. split; [exact Hh'|]. exact Hnone.
  - pose proof (marks_off segs lo lo ms m x8 (Z.le_refl lo) Hh Hsvc NB) as Mlo.
    pose proof (marks_off segs lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ lo Hspec) as [[Fl _] Slo]. specialize (Slo HI Mm Mlo). cbn [relimo] in *.
    exfalso. apply NB. split; [exact Hh|]. right. exists x8. split; [exact Hsvc|]. right.
    exists eff, (relim lo m'), evs0. split; [exact Slo|]. split; [exact Hh'|].
    rewrite <- (Hid m'), Fl in Hmat. exact (materialize_none_down _ _ _ _ Hlo Hmat).
  - pose proof (marks_off segs lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
    pose proof (marks_off segs lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ l' Hspec) as [_ S']. specialize (S' HI Mm Ml'). cbn [relimo] in *.
    change (m_fs m') with (m_fs (relim l' m')). eapply sstep_cfg_exit; [exact Hh| exact Hsvc| exact S'| exact Hh'| exact Hk].
  - pose proof (marks_off segs lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
    pose proof (marks_off segs lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ l' Hspec) as [_ S']. specialize (S' HI Mm Ml'). cbn [relimo] in *.
    change (m_fs m') with (m_fs (relim l' m')). eapply sstep_cfg_killed; [exact Hh| exact Hsvc| exact S'| exact Hk].
  - pose proof (marks_off segs lo l' ms m x8 HL Hh Hsvc NB) as Ml'.
    pose proof (marks_off segs lo (mlim m) ms m x8 Hlo Hh Hsvc NB) as Mm. rewrite Hid in Mm.
    destruct (syscall_spec_ARM _ _ _ l' Hspec) as [_ S']. specialize (S' HI Mm Ml'). cbn [relimo] in *.
    eapply sstep_cfg_syscall_unmodeled; [exact Hh| exact Hsvc| exact S'].
Qed.

Theorem star_cfg_relim : forall lo l' c tr c',
  star_cfg segs cfg c tr c' ->
  (lo <= l')%Z -> (lo <= mlim (cfg_model c))%Z -> INV (cfg_model c) ->
  ~ reaches_budget_refused_cfg segs cfg (relim_cfg lo c) ->
  star_cfg segs cfg (relim_cfg l' c) tr (relim_cfg l' c')
  /\ mlim (cfg_model c') = mlim (cfg_model c) /\ INV (cfg_model c')
  /\ ~ reaches_budget_refused_cfg segs cfg (relim_cfg lo c').
Proof.
  intros lo l' c tr c' ST. induction ST as [c | c1 evs c2 tr c3 Hs ST IH]; intros HL Hlo HI NR.
  - split; [apply star_cfg_refl|]. split; [reflexivity|]. split; [exact HI| exact NR].
  - assert (NB : ~ budget_refused_at segs (relim_cfg lo c1)).
    { intros B. apply NR. exists [], (relim_cfg lo c1). split; [apply star_cfg_refl| exact B]. }
    destruct (sstep_cfg_relim lo l' c1 evs (SNext c2) HL Hlo HI NB Hs) as [S' F]. destruct (F c2 eq_refl) as [Fl FI].
    destruct (sstep_cfg_relim lo lo c1 evs (SNext c2) (Z.le_refl lo) Hlo HI NB Hs) as [Slo _].
    assert (NR2 : ~ reaches_budget_refused_cfg segs cfg (relim_cfg lo c2)).
    { intros (tr' & c' & ST' & B). apply NR. exists (evs ++ tr'), c'.
      split; [eapply star_cfg_step; [exact Slo| exact ST']| exact B]. }
    destruct (IH HL ltac:(rewrite Fl; exact Hlo) FI NR2) as (ST' & Fl' & FI' & NR').
    split; [eapply star_cfg_step; [exact S'| exact ST']|]. split; [congruence|]. split; [exact FI'| exact NR'].
Qed.

Theorem obs_trace_cfg_relim : forall lo l' c tr,
  (lo <= l')%Z -> (lo <= mlim (cfg_model c))%Z -> INV (cfg_model c) ->
  ~ reaches_budget_refused_cfg segs cfg (relim_cfg lo c) ->
  obs_trace_cfg segs cfg c tr -> obs_trace_cfg segs cfg (relim_cfg l' c) tr.
Proof.
  intros lo l' c tr HL Hlo HI NR (tr' & c' & ST & P).
  exists tr', (relim_cfg l' c'). split; [exact (proj1 (star_cfg_relim _ _ _ _ _ ST HL Hlo HI NR))| exact P].
Qed.

Theorem reaches_error_cfg_relim : forall lo l' c,
  (lo <= l')%Z -> (lo <= mlim (cfg_model c))%Z -> INV (cfg_model c) ->
  ~ reaches_budget_refused_cfg segs cfg (relim_cfg lo c) ->
  reaches_error_cfg segs cfg c -> reaches_error_cfg segs cfg (relim_cfg l' c).
Proof.
  intros lo l' c HL Hlo HI NR (tr & c' & evs & ST & SE).
  destruct (star_cfg_relim _ _ _ _ _ ST HL Hlo HI NR) as (ST' & Fl & FI & NR').
  exists tr, (relim_cfg l' c'), evs. split; [exact ST'|].
  refine (proj1 (sstep_cfg_relim lo l' c' evs SError HL _ FI _ SE)); [rewrite Fl; exact Hlo|].
  intros B. apply NR'. exists [], (relim_cfg lo c'). split; [apply star_cfg_refl| exact B].
Qed.

End StepCfg.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma init_config_relim : forall segs pc ph sp brk0 mbase rnd l L inp,
  init_config segs pc ph sp brk0 mbase rnd l inp = relim_cfg l (init_config segs pc ph sp brk0 mbase rnd L inp).
Proof. intros. reflexivity. Qed.

Lemma init_config_mlim : forall segs pc ph sp brk0 mbase rnd l inp,
  mlim (cfg_model (init_config segs pc ph sp brk0 mbase rnd l inp)) = l.
Proof. intros. reflexivity. Qed.

Lemma init_config_INV : forall segs pc ph sp brk0 mbase rnd l inp,
  INV (cfg_model (init_config segs pc ph sp brk0 mbase rnd l inp)).
Proof. intros. split; intros a sz []. Qed.

Section Run.
Variables (img : Image) (en : ExecEntry) (inp : ProcInput) (l L : Z).
Hypothesis HlL : (l <= L)%Z.
Hypothesis NB : ~ run_budget_refused img l en inp.

Theorem run_relimit_traces : forall tr,
  bh_traces (run img l en inp) tr <-> bh_traces (run img L en inp) tr.
Proof.
  intros tr. destruct img as [segs pc ph], en as [sp brk0 mbase rnd]. cbn [run bh_traces]. unfold run_budget_refused in NB.
  split; intros H.
  - rewrite (init_config_relim segs pc ph sp brk0 mbase rnd L l inp).
    apply (obs_trace_relim segs l); [exact HlL| rewrite init_config_mlim; lia| apply init_config_INV| | exact H].
    rewrite <- init_config_relim. exact NB.
  - rewrite (init_config_relim segs pc ph sp brk0 mbase rnd l L inp).
    apply (obs_trace_relim segs l); [lia| rewrite init_config_mlim; exact HlL| apply init_config_INV| | exact H].
    rewrite <- init_config_relim. exact NB.
Qed.

Theorem run_relimit_errors :
  bh_errors (run img l en inp) <-> bh_errors (run img L en inp).
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd]. cbn [run bh_errors]. unfold run_budget_refused in NB.
  split; intros H.
  - rewrite (init_config_relim segs pc ph sp brk0 mbase rnd L l inp).
    apply (reaches_error_relim segs l); [exact HlL| rewrite init_config_mlim; lia| apply init_config_INV| | exact H].
    rewrite <- init_config_relim. exact NB.
  - rewrite (init_config_relim segs pc ph sp brk0 mbase rnd l L inp).
    apply (reaches_error_relim segs l); [lia| rewrite init_config_mlim; exact HlL| apply init_config_INV| | exact H].
    rewrite <- init_config_relim. exact NB.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Corollary run_relimit_error_free :
  error_free (run img l en inp) <-> error_free (run img L en inp).
Proof. unfold error_free. pose proof run_relimit_errors. tauto. Qed.

(* [comment removed for export] *)
End Run.

Section RunCfg.
Variables (cfg : SpuriousCfg) (img : Image) (en : ExecEntry) (inp : ProcInput) (l L : Z).
Hypothesis HlL : (l <= L)%Z.
Hypothesis NB : ~ run_scfg_budget_refused cfg img l en inp.

Theorem run_scfg_relimit_traces : forall tr,
  bh_traces (run_scfg cfg img l en inp) tr <-> bh_traces (run_scfg cfg img L en inp) tr.
Proof.
  intros tr. destruct img as [segs pc ph], en as [sp brk0 mbase rnd]. cbn [run_scfg bh_traces].
  unfold run_scfg_budget_refused in NB.
  split; intros H.
  - rewrite (init_config_relim segs pc ph sp brk0 mbase rnd L l inp).
    apply (obs_trace_cfg_relim segs cfg l); [exact HlL| rewrite init_config_mlim; lia| apply init_config_INV| | exact H].
    rewrite <- init_config_relim. exact NB.
  - rewrite (init_config_relim segs pc ph sp brk0 mbase rnd l L inp).
    apply (obs_trace_cfg_relim segs cfg l); [lia| rewrite init_config_mlim; exact HlL| apply init_config_INV| | exact H].
    rewrite <- init_config_relim. exact NB.
Qed.

Theorem run_scfg_relimit_errors :
  bh_errors (run_scfg cfg img l en inp) <-> bh_errors (run_scfg cfg img L en inp).
Proof.
  destruct img as [segs pc ph], en as [sp brk0 mbase rnd]. cbn [run_scfg bh_errors].
  unfold run_scfg_budget_refused in NB.
  split; intros H.
  - rewrite (init_config_relim segs pc ph sp brk0 mbase rnd L l inp).
    apply (reaches_error_cfg_relim segs cfg l); [exact HlL| rewrite init_config_mlim; lia| apply init_config_INV| | exact H].
    rewrite <- init_config_relim. exact NB.
  - rewrite (init_config_relim segs pc ph sp brk0 mbase rnd l L inp).
    apply (reaches_error_cfg_relim segs cfg l); [lia| rewrite init_config_mlim; exact HlL| apply init_config_INV| | exact H].
    rewrite <- init_config_relim. exact NB.
Qed.

Corollary run_scfg_relimit_error_free :
  error_free (run_scfg cfg img l en inp) <-> error_free (run_scfg cfg img L en inp).
Proof. unfold error_free. pose proof run_scfg_relimit_errors. tauto. Qed.

End RunCfg.
