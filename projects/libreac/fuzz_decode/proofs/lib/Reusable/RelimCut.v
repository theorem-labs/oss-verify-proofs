(* A budget refusal at a larger memory limit is a budget refusal at a smaller one. So when the run at the smaller
   limit is never refused, the run at the larger limit never reaches a refused configuration: it is cut-free in the
   sense of lib/Reusable/YK15.v, whose [realizes] has a cut at a refused configuration. This is what lets the plain
   build's realization of SPECX at 2^34 (lib/AgreeTop.v) serve the ASan agreement, whose premise bounds the plain
   run at 2^31. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs RiscvSemantics MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK15 YQ00 YQ02 YQ03 YQ04 YQ05 YQ06.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Open Scope Z_scope.

Section r.
Variables L0 L : Z.
Hypothesis HLE : L <= L0.

Lemma materialize_none_relim : forall m acc, vm_limit (m_vmmaps m) = L0 ->
  materialize_model_accesses m acc = None -> materialize_model_accesses (relim L m) acc = None.
Proof.
  intros m acc HM H. destruct (materialize_model_accesses (relim L m) acc) as [m1|] eqn:E; [|reflexivity].
  assert (HL : L <= vm_limit (m_vmmaps m)) by (rewrite HM; exact HLE).
  destruct (materialize_relim_up L m acc m1 HL E) as (m0 & E0 & _). rewrite E0 in H. discriminate.
Qed.

(* Each allocation call's budget mark: refused at the larger limit implies refused at the smaller one. *)
Lemma brk_refused_relim : forall m req, vm_limit (m_vmmaps m) = L0 ->
  brk_budget_refused_b m req = true -> brk_budget_refused_b (relim L m) req = true.
Proof.
  intros m req HM H. unfold brk_budget_refused_b, min_brk in *. autorewrite with relim_rw.
  rewrite !andb_true_iff in H |- *. destruct H as (((H1 & H2) & H3) & H4).
  repeat split; try assumption.
  apply negb_true_iff in H4. apply negb_true_iff.
  destruct (brk_budget_ok (relim L m) req) eqn:E; [|reflexivity].
  assert (brk_budget_ok m req = true) by (eapply brk_budget_ok_mono; eauto). congruence.
Qed.

Lemma mprotect_refused_relim : forall a n p m, vm_limit (m_vmmaps m) = L0 ->
  mprotect_budget_refused_b a n p m = true -> mprotect_budget_refused_b a n p (relim L m) = true.
Proof.
  intros a n p m HM H. unfold mprotect_budget_refused_b in *. autorewrite with relim_rw.
  replace (m_vmmaps (relim L m)) with (relimV L (m_vmmaps m)) by reflexivity. cbn [relimV vm_noaccess vm_maps].
  repeat match goal with
         | H : context [if ?c then _ else _] |- _ => destruct c; try discriminate
         end.
  apply negb_true_iff in H. apply negb_true_iff.
  destruct (mprotect_budget_ok (relim L m) a (Z_to_bv 64 (page_round_up_Z (bv_unsigned n)))) eqn:E; [|reflexivity].
  assert (mprotect_budget_ok m a (Z_to_bv 64 (page_round_up_Z (bv_unsigned n))) = true)
    by (eapply mprotect_budget_ok_relim; eauto). congruence.
Qed.

Lemma mremap_refused_relim : forall o os ns f m, vm_limit (m_vmmaps m) = L0 ->
  mremap_budget_refused_b o os ns f m = true -> mremap_budget_refused_b o os ns f (relim L m) = true.
Proof.
  intros o os ns f m HM H. unfold mremap_budget_refused_b in *.
  replace (m_vmmaps (relim L m)) with (relimV L (m_vmmaps m)) by reflexivity.
  replace (mremap_source_b (relimV L (m_vmmaps m))) with (mremap_source_b (m_vmmaps m)) by reflexivity.
  replace (mremap_backing_uniform_b (relim L m)) with (mremap_backing_uniform_b m) by reflexivity.
  repeat match goal with
         | H : context [if ?c then _ else _] |- _ => destruct c; try discriminate
         end.
  apply negb_true_iff in H. apply negb_true_iff.
  apply andb_false_iff in H. apply andb_false_iff.
  destruct H as [H | H].
  - left. destruct (mremap_final_budget_b (relim L m) _ _ _ _) eqn:E; [|reflexivity].
    assert (mremap_final_budget_b m o (Z_to_bv 64 (page_round_up_Z (bv_unsigned os))) o
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned ns))) = true)
      by (eapply mremap_final_budget_b_mono; eauto). congruence.
  - right. unfold mremap_move_budget_b in H |- *. rewrite mremap_move_charge_relim, rr_m_vmmaps, rr_vm_limit.
    rewrite HM in H. apply Z.leb_gt in H. apply Z.leb_gt. lia.
Qed.

Lemma mmap_refused_relim : forall a n p f fd off m, vm_limit (m_vmmaps m) = L0 ->
  mmap_budget_refused_b a n p f fd off m = true -> mmap_budget_refused_b a n p f fd off (relim L m) = true.
Proof.
  intros a n p f fd off m HM H. unfold mmap_budget_refused_b in *.
  replace (m_vmmaps (relim L m)) with (relimV L (m_vmmaps m)) by reflexivity.
  cbn [relimV vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_mmap_base vm_init_sp] in *.
  try change (alloc_top (relimV L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
  repeat match goal with
         | H : context [if ?c then _ else _] |- _ =>
           lazymatch c with
           | context [relim] => fail
           | _ => destruct c; try discriminate
           end
         end;
  apply negb_true_iff in H; apply negb_true_iff;
  first
    [ destruct (mmap_noreserve_backed_ok _ (relim L m) _) eqn:E; [|reflexivity];
      assert (mmap_noreserve_backed_ok f m (page_round_up_Z (bv_unsigned n)) = true)
        by (eapply mmap_noreserve_backed_ok_mono; eauto); congruence
    | destruct (mmap_fixed_rw_budget_ok _ (relim L m) _ _) eqn:E; [|reflexivity];
      assert (mmap_fixed_rw_budget_ok f m a (Z_to_bv 64 (page_round_up_Z (bv_unsigned n))) = true)
        by (eapply mmap_fixed_rw_budget_ok_mono; eauto); congruence
    | destruct (mmap_fixed_rw_span_budget_ok _ (relim L m) _ _) eqn:E; [|reflexivity];
      assert (mmap_fixed_rw_span_budget_ok f m a (Z_to_bv 64 (page_round_up_Z (bv_unsigned n))) = true)
        by (eapply mmap_fixed_rw_span_budget_ok_mono; eauto); congruence ].
Qed.

Lemma alloc_refused_relim : forall i m, vm_limit (m_vmmaps m) = L0 ->
  alloc_budget_refused_b i m = true -> alloc_budget_refused_b i (relim L m) = true.
Proof.
  intros i m HM H. unfold alloc_budget_refused_b in *.
  destruct (bv_unsigned (in_sysno i) =? 214); [exact (brk_refused_relim _ _ HM H)|].
  destruct (bv_unsigned (in_sysno i) =? 216); [exact (mremap_refused_relim _ _ _ _ _ HM H)|].
  destruct (bv_unsigned (in_sysno i) =? 222); [exact (mmap_refused_relim _ _ _ _ _ _ _ HM H)|].
  destruct (bv_unsigned (in_sysno i) =? 226); [exact (mprotect_refused_relim _ _ _ _ HM H)|].
  discriminate.
Qed.

Lemma budget_refused_relim : forall segs ms m, MOK L0 m -> MV_OK m ->
  budget_refused_at segs (mkCfg ms m) -> budget_refused_at segs (mkCfg ms (relim L m)).
Proof.
  intros segs ms m HM MV (Hh & H). unfold MOK in HM. split; [cbn; rewrite relim_halted; exact Hh|].
  destruct H as [(Hp & report & Est & Emat) | (x8 & Hp & [Hr | (eff & m' & evs & Hsp & Hh' & Emat)])].
  - left. split; [exact Hp|]. exists report. split; [exact Est|]. exact (materialize_none_relim _ _ HM Emat).
  - right. exists x8. split; [exact Hp|]. left. exact (alloc_refused_relim _ _ HM Hr).
  - right. exists x8. split; [exact Hp|]. cbn [cfg_ms cfg_model] in *.
    destruct (alloc_budget_refused_b (sys_input segs ms x8) (relim L m)) eqn:G; [left; reflexivity|].
    right.
    destruct (syscall_spec_dir L0 L HLE false _ m HM G (fun _ => MV) _ Hsp) as ([e0 m0 ev0|] & Hsp0 & R);
      cbn in R; [|contradiction].
    destruct R as (-> & -> & -> & HM0).
    exists eff, (relim L m'), evs. split; [exact Hsp0|]. split; [rewrite relim_halted; exact Hh'|].
    exact (materialize_none_relim _ _ HM0 Emat).
Qed.
End r.

(* The plain run at the larger limit is cut-free when the run at the smaller limit is never refused. *)
Theorem cut_free_of_relim : forall s pc ph sp brk0 mbase rnd (Ls Lbig : Z) inp,
  Ls <= Lbig ->
  ~ run_scfg_budget_refused ACFG (mkImage s pc ph) Ls (mkEntry sp brk0 mbase rnd) inp ->
  cut_free s (init_config s pc ph sp brk0 mbase rnd Lbig inp).
Proof.
  intros s pc ph sp brk0 mbase rnd Ls Lbig inp HLE NB tr c' Hst Hb.
  pose proof (INV_init ACFG (mkImage s pc ph) Lbig Ls (mkEntry sp brk0 mbase rnd) inp NB) as HI. cbn in HI.
  destruct (star_down s ACFG Lbig Ls HLE _ tr c' Hst HI) as [_ (HM & HW & NR)].
  destruct c' as [ms m]. cbn [cfg_model] in HM, HW.
  apply (not_reaches_here s ACFG _ NR).
  exact (budget_refused_relim Lbig Ls HLE s ms m HM (MV_OK_wf m HW) Hb).
Qed.
