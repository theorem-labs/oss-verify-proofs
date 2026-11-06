(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  AsanCeil SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg ShapeNodes Nodes StoreOk AgentLib SpecConsts RefNodes PureModel AllocRefusal CfgStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Export VmLedger.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition t_ix (A : TSet) (P : word -> Prop) (B : word -> TSet) : TSet :=
  fun tr => A tr \/ exists a, P a /\ B a tr.

Lemma t_ix_const : forall A (P : word -> Prop) B,
  (exists a, P a) -> t_eq (t_ix A P (fun _ => B)) (t_alt2 A B).
Proof.
  intros A P B [a Ha] tr. unfold t_ix, t_alt2. split.
  - intros [H | (a' & _ & H)]; [left | right]; exact H.
  - intros [H | H]; [left; exact H | right; exists a; split; [exact Ha | exact H]].
Qed.

Lemma t_ix_empty : forall A (P : word -> Prop) B,
  (forall a, ~ P a) -> t_eq (t_ix A P B) A.
Proof.
  intros A P B Hn tr. unfold t_ix. split.
  - intros [H | (a & Ha & _)]; [exact H | exfalso; exact (Hn a Ha)].
  - intros H. left. exact H.
Qed.

(* [comment removed for export] *)
Definition t_ixc (c : Prop) (A : TSet) (P : word -> Prop) (B : word -> TSet) : TSet :=
  fun tr => (c /\ A tr) \/ exists a, P a /\ B a tr.

Lemma t_ixc_true : forall (c : Prop) A P B, c -> t_eq (t_ixc c A P B) (t_ix A P B).
Proof.
  intros c A P B Hc tr. unfold t_ixc, t_ix. split.
  - intros [[_ H] | H]; [left; exact H | right; exact H].
  - intros [H | H]; [left; split; [exact Hc | exact H] | right; exact H].
Qed.

(* [comment removed for export] *)
Lemma t_ixc_false : forall (c : Prop) A P B, ~ c -> t_eq (t_ixc c A P B) (fun tr => exists a, P a /\ B a tr).
Proof.
  intros c A P B Hc tr. unfold t_ixc. split.
  - intros [[H _] | H]; [exfalso; exact (Hc H) | exact H].
  - intros H. right. exact H.
Qed.

Lemma t_ixc_const : forall (c : Prop) A (P : word -> Prop) B,
  ~ c -> (exists a, P a) -> t_eq (t_ixc c A P (fun _ => B)) B.
Proof.
  intros c A P B Hc [a Ha] tr. unfold t_ixc. split.
  - intros [[H _] | (a' & _ & H)]; [exfalso; exact (Hc H) | exact H].
  - intros H. right. exists a. split; [exact Ha | exact H].
Qed.

Lemma t_ixc_empty : forall (c : Prop) A (P : word -> Prop) B,
  c -> (forall a, ~ P a) -> t_eq (t_ixc c A P B) A.
Proof.
  intros c A P B Hc Hn tr. unfold t_ixc. split.
  - intros [[_ H] | (a & Ha & _)]; [exact H | exfalso; exact (Hn a Ha)].
  - intros H. left. split; [exact Hc | exact H].
Qed.

Lemma word_of_unsigned : forall (x : word) z, bv_unsigned x = z -> x = Z_to_bv 64 z.
Proof. intros x z <-. symmetry. apply Z_to_bv_u_eq'. reflexivity. Qed.

Lemma nonzero_of_unsigned_pos : forall (x : word), (0 < bv_unsigned x)%Z -> x <> Z_to_bv 64 0.
Proof.
  intros x Hx E. rewrite E in Hx. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_I (ms : machine_state) (model : Model) : Type :=
  ({e : Z | In e (mmap_errnos_when
                    (mmap_refusable model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))))}   (* [comment removed for export] *)
   + {a : word | grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})%type.

(* [comment removed for export] *)
Lemma mmap_I_inhabited : forall ms model, inhabited (mmap_I ms model).
Proof.
  intros ms model. unfold mmap_I.
  destruct (mmap_refusable model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Er.
  - constructor. left. exists ENOMEM. apply ENOMEM_in_mmap_errnos.
  - apply (mmap_refusable_false_iff (ms_gpr ms 0)) in Er as [a Ha]. constructor. right. exists a. exact Ha.
Qed.

Definition mmap_nx (ms : machine_state) (model : Model) (i : mmap_I ms model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr (exist _ a _) =>
      mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
            (mmap_model a (page_round_up (ms_gpr ms 1)) model)
  end.

Lemma node_mmap : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  node_ok segs (mkCfg ms model) (mmap_I ms model) (fun _ => []) (mmap_nx ms model).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
  pose (nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1))).
  pose (nxu := fun i : {e : Z | In e mmap_errnos} + {a : word | grant_ok (ms_gpr ms 0) model a nZ = true} =>
    match i with
    | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
    | inr (exist _ a _) =>
        mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
              (mmap_model a (page_round_up (ms_gpr ms 1)) model)
    end).
  assert (Hu : node_ok_u segs (mkCfg ms model)
                 ({e : Z | In e mmap_errnos} + {a : word | grant_ok (ms_gpr ms 0) model a nZ = true})
                 (fun _ => []) nxu).
  { split.
    - intros [[e He] | [a Ha]]; unfold nxu; cbv beta iota.
      + rewrite <- (apply_effect_no_write ms (errno_ret e)).
        apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] []) model model []);
          [exact Hh | exact Hsvc | apply mmap_fail_ok_u; assumption | exact Hh
          | apply materialize_model_accesses_no_lazy; exact Hlazy].
      + apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
                 (mmap_model a (page_round_up (ms_gpr ms 1)) model)
                 (mmap_model a (page_round_up (ms_gpr ms 1)) model) []);
          [exact Hh | exact Hsvc | apply mmap_succ_ok; assumption
          | rewrite mmap_model_halted; exact Hh
          | apply materialize_model_accesses_no_lazy; exact (eq_trans (mmap_model_lazy _ _ _) Hlazy)].
    - intros e st Hss.
      destruct (sstep_mmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
        as [-> [(er & Her & ->) | (a & Ha & ->)]].
      + exists (inl (exist _ er Her)). split; reflexivity.
      + exists (inr (exist _ a Ha)). split; reflexivity. }
  pose proof (node_ok_refusable segs (mkCfg ms model) {e : Z | In e mmap_errnos}
                {a : word | grant_ok (ms_gpr ms 0) model a nZ = true}
                {e : Z | In e (mmap_errnos_when (mmap_refusable model nZ))}
                (fun r' => exist _ (proj1_sig r') (proj2 (proj1 (mmap_errnos_when_in _ _) (proj2_sig r'))))
                (fun _ => []) nxu Hu) as Hc.
  refine (node_ok_ext segs _ _ _ _ _ _ (Hc _ _ _ _ _ _ _) _ _).
  - exact (kit_pending_off_sysno segs ms model x8 222 Hsvc Hno eq_refl).
  - intros [e He]. unfold nxu; cbv beta iota.
    rewrite (child_refusal_b_set_gpr0 segs ms model x8 (errno_ret e) model Hsvc Hh).
    exact (refusal_b_mmap_errno (sys_input segs ms x8) model e Hno He).
  - intros [a Ha]. unfold nxu; cbv beta iota.
    rewrite (child_refusal_b_syscall segs ms model x8 _ _ Hsvc (eq_trans (mmap_model_halted _ _ _) Hh)).
    cbn [eff_ret]. exact (mmap_grant_not_refusal segs ms model x8 a Hno Ha).
  - intros [[e He] | [a Ha]]; unfold nxu; cbv beta iota; cbn [cfg_model]; [exact Hh | rewrite mmap_model_halted; exact Hh].
  - intros [e He] [a Ha]. apply mmap_errnos_when_in in He as [Hr _].
    pose proof (proj1 (mmap_refusable_iff (ms_gpr ms 0) model nZ) Hr a) as E. congruence.
  - intros HG [e He].
    assert (Hr : mmap_refusable model nZ = true).
    { apply (mmap_refusable_iff (ms_gpr ms 0)). intros a.
      destruct (grant_ok (ms_gpr ms 0) model a nZ) eqn:E; [exfalso; exact (HG (exist _ a E)) | reflexivity]. }
    exists (exist _ e (proj2 (mmap_errnos_when_in _ _) (conj Hr He))). split; reflexivity.
  - intros [[e He] | [a Ha]]; unfold nxu; cbv beta iota; cbn [cfg_limit cfg_model]; [reflexivity | apply vm_limit_mmap_model].
  - intros i. reflexivity.
  - intros [[e He] | [a Ha]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_ix : forall ms model x8 A (B : word -> TSet),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  let n := page_round_up (ms_gpr ms 1) in
  (mmap_refusable model nZ = true ->
   realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model) A) ->
  (forall a, grant_ok (ms_gpr ms 0) model a nZ = true ->
     realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, n)])))
                          (mmap_model a n model)) (B a)) ->
  realizes segs (mkCfg ms model)
           (t_ixc (mmap_refusable model nZ = true) A (fun a => grant_ok (ms_gpr ms 0) model a nZ = true) B).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs nZ n HA HB.
  destruct (mmap_I_inhabited ms model) as [i0].
  apply (rz_conseq segs _
           (t_alt (fun i : mmap_I ms model =>
                     t_emit [] (match i with inl _ => A | inr (exist _ a _) => B a end)))).
  - apply (rz_node segs (mkCfg ms model) (mmap_I ms model) (fun _ => []) (mmap_nx ms model)
             (fun i => match i with inl _ => A | inr (exist _ a _) => B a end) i0).
    + eapply node_mmap; eassumption.
    + intros [[e He] | [a Ha]]; cbn.
      * apply mmap_errnos_when_in in He as [Hr He]. destruct He as [<- | []]. exact (HA Hr).
      * apply HB. exact Ha.
  - intros tr. unfold t_alt, t_ixc. split.
    + intros [[[e He] | [a Ha]] Ht]; cbn in Ht.
      * left. apply mmap_errnos_when_in in He as [Hr He]. split; [exact Hr|].
        apply (t_emit_nil_eq A); [eapply realizes_nonempty; exact (HA Hr) | exact Ht].
      * right. exists a. split; [exact Ha|].
        apply (t_emit_nil_eq (B a)); [eapply realizes_nonempty; apply HB; exact Ha | exact Ht].
    + intros [[Hr Ht] | (a & Ha & Ht)].
      * exists (inl (exist _ ENOMEM (proj2 (mmap_errnos_when_in _ ENOMEM) (conj Hr ENOMEM_in_mmap_errnos)))). cbn.
        apply t_emit_nil_eq; [eapply realizes_nonempty; exact (HA Hr) | exact Ht].
      * exists (inr (exist _ a Ha)). cbn.
        apply t_emit_nil_eq; [eapply realizes_nonempty; apply HB; exact Ha | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_nogrant_ms : forall ms model x8 A,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_args_ok ms ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false) ->
  (forall e, In e mmap_errnos ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes segs (mkCfg ms model) A.
Proof.
  intros ms model x8 A Hh Hlazy Hsvc Hno Hargs Hng HA.
  eapply rz_conseq.
  - apply (rz_mmap_ix ms model x8 A (fun _ => A) Hh Hlazy Hsvc Hno Hargs).
    + intros _. apply HA. apply ENOMEM_in_mmap_errnos.
    + intros a Ha. rewrite Hng in Ha. discriminate.
  - apply t_ixc_empty.
    + apply (mmap_refusable_iff (ms_gpr ms 0)). exact Hng.
    + intros a Ha. rewrite Hng in Ha. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_brk_query_ms : forall ms model x8 T,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (vm_brk (m_vmmaps model)) [] [] [] [] [])))
                       model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno H0 Hc.
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  assert (Hnr : brk_refusal_b model (ms_gpr ms 0) (vm_brk (m_vmmaps model)) = false).
  { rewrite H0. unfold brk_refusal_b. cbv zeta. unfold w_is0. rewrite bv_eqb_refl. reflexivity. }
  pose (i0 := exist _ (vm_brk (m_vmmaps model)) (conj Hq (or_introl Hnr)) : brk_I model (ms_gpr ms 0)).
  apply (rz_conseq segs _ (t_alt (fun _ : brk_I model (ms_gpr ms 0) => T)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists i0; exact Ht]].
  eapply rz_cases; [exact i0 | eapply node_brk; [exact Hh | exact Hlazy | exact Hsvc | exact Hno] |].
  intros [r [Hr Hx]]. cbn [proj1_sig].
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rz_brk_grow_ms : forall ms model x8 (req : word) A B,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = req ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (0 < bv_unsigned b)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b < bv_unsigned req)%Z ->
  (Mmap.brk_grow_ok model req req = false ->
   realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffectU b [] [] [] [] []))) model) A) ->
  (Mmap.brk_grow_ok model req req = true ->
   realizes segs (mkCfg (advance_past_svc (apply_effect ms
                          (mkEffectU req [] (brk_zeros req req b) [] [] [])))
                       (brk_model req req model)) B) ->
  realizes segs (mkCfg ms model)
    (fun tr => (Mmap.brk_grow_ok model req req = false /\ A tr) \/ (Mmap.brk_grow_ok model req req = true /\ B tr)).
Proof.
  intros ms model x8 req A B Hh Hlazy Hsvc Hno H0 h b Hb0 Hs Hlt HA HB.
  pose proof (u64_range b) as Hbr. pose proof (u64_range req) as Hrr.
  assert (Hpos : (0 < bv_unsigned req)%Z) by lia.
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <->
                             (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; lia. }
  assert (Hneq : req <> b).
  { intros E. rewrite E in Hlt. lia. }
  assert (Hreq0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  assert (Hrb : brk_refusal_b model (ms_gpr ms 0) b = true).
  { rewrite H0. unfold brk_refusal_b. cbv zeta. fold h. fold b. unfold min_brk.
    rewrite Hreq0, (proj2 (Z.ltb_ge _ _) Hs), (bv_eqb_neq _ _ Hneq), bv_eqb_refl. reflexivity. }
  assert (Hrq : brk_refusal_b model (ms_gpr ms 0) req = false).
  { rewrite H0. unfold brk_refusal_b. cbv zeta. fold h. fold b.
    rewrite (bv_eqb_neq _ _ Hneq). apply andb_false_r. }
  pose (nxb := fun i : brk_I model (ms_gpr ms 0) =>
    mkCfg (advance_past_svc (apply_effect ms
             (mkEffectU (proj1_sig i) []
                (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
          (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
  assert (Hnode : node_ok segs (mkCfg ms model) (brk_I model (ms_gpr ms 0)) (fun _ => []) nxb)
    by (eapply node_brk; [exact Hh | exact Hlazy | exact Hsvc | exact Hno]).
  destruct (Mmap.brk_grow_ok model req req) eqn:Eg.
  - assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; auto).
    pose (i0 := exist _ req (conj Hgrow (or_introl Hrq)) : brk_I model (ms_gpr ms 0)).
    assert (HB' : forall i, realizes segs (nxb i) B).
    { intros [r [Hr Hx]].
      destruct (proj1 (Hcases r) Hr) as [-> | [-> _]].
      - exfalso. destruct Hx as [Hx | Hall].
        + congruence.
        + pose proof (Hall req Hgrow) as E. congruence.
      - unfold nxb; cbn [proj1_sig]. rewrite H0. fold h. fold b.
        rewrite (brk_unmaps_grow req b) by lia. apply HB. reflexivity. }
    assert (HB0 : B []) by (eapply realizes_nonempty; exact (HB' i0)).
    apply (rz_conseq segs _ (t_alt (fun _ : brk_I model (ms_gpr ms 0) => t_emit [] B))).
    + exact (rz_node segs (mkCfg ms model) (brk_I model (ms_gpr ms 0)) (fun _ => []) nxb
               (fun _ => B) i0 Hnode HB').
    + intros tr. split.
      * intros [_ Ht]. right. split; [reflexivity | exact (proj1 (t_emit_nil_eq B HB0 tr) Ht)].
      * intros [[E _] | [_ Ht]]; [discriminate E |].
        exists i0. exact (proj2 (t_emit_nil_eq B HB0 tr) Ht).
  - assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; left; reflexivity).
    assert (Hall : forall r', brk_resolution_ok model (ms_gpr ms 0) r' ->
                              brk_refusal_b model (ms_gpr ms 0) r' = true).
    { intros r' Hr'. destruct (proj1 (Hcases r') Hr') as [-> | [_ E]]; [exact Hrb | congruence]. }
    pose (i0 := exist _ b (conj Hkeep (or_intror Hall)) : brk_I model (ms_gpr ms 0)).
    assert (HA' : forall i, realizes segs (nxb i) A).
    { intros [r [Hr Hx]]. destruct (proj1 (Hcases r) Hr) as [-> | [_ E]]; [| congruence].
      unfold nxb; cbn [proj1_sig]. rewrite H0. fold h. fold b. rewrite brk_zeros_keep, brk_unmaps_keep.
      unfold b, h. rewrite brk_model_keep. apply HA. reflexivity. }
    assert (HA0 : A []) by (eapply realizes_nonempty; exact (HA' i0)).
    apply (rz_conseq segs _ (t_alt (fun _ : brk_I model (ms_gpr ms 0) => t_emit [] A))).
    + exact (rz_node segs (mkCfg ms model) (brk_I model (ms_gpr ms 0)) (fun _ => []) nxb
               (fun _ => A) i0 Hnode HA').
    + intros tr. split.
      * intros [_ Ht]. left. split; [reflexivity | exact (proj1 (t_emit_nil_eq A HA0 tr) Ht)].
      * intros [[_ Ht] | [E _]]; [| discriminate E].
        exists i0. exact (proj2 (t_emit_nil_eq A HA0 tr) Ht).
Qed.

(* [comment removed for export] *)
Lemma brk_grow_post_aligned : forall model (d : Z),
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  let req := Z_to_bv 64 (bv_unsigned b + d) in
  brk_zeros req req b = [(b, Z_to_bv 64 d)]
  /\ brk_model req req model
     = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                      (vm_noaccess h) (vm_start_brk h)
                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model.
Proof.
  intros model d h b Hbal Hdal Hd Hb0 Hnw req.
  pose proof (u64_range b) as Hbr.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  split.
  - rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt). unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia. reflexivity.
  - unfold req, b, h. apply (brk_model_grow_eq model d); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mmap_na_I (ms : machine_state) (model : Model) : Type :=
  ({e : Z | In e (mmap_errnos_when
                    (mmap_reserve_refusable model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))))}   (* [comment removed for export] *)
   + {a : word | grant_ok_na_pin model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})%type.

Lemma mmap_na_I_inhabited : forall ms model, inhabited (mmap_na_I ms model).
Proof.
  intros ms model. unfold mmap_na_I.
  destruct (mmap_reserve_refusable model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Er.
  - constructor. left. exists ENOMEM. apply ENOMEM_in_mmap_errnos.
  - rewrite mmap_reserve_refusable_vm in Er. apply mmap_na_refusable_vm_false_iff in Er as [a Ha].
    constructor. right. exists a. rewrite grant_ok_na_pin_vm. exact Ha.
Qed.

Definition mmap_na_eff (ms : machine_state) (model : Model) (i : mmap_na_I ms model) : SyscallEffect :=
  match i with
  | inl (exist _ e _) => mkEffectU (errno_ret e) [] [] [] [] []
  | inr (exist _ a _) => mkEffectU a [] [] [(a, page_round_up (ms_gpr ms 1))] [] []
  end.

Definition mmap_na_model (ms : machine_state) (model : Model) (i : mmap_na_I ms model) : Model :=
  match i with
  | inl _ => model
  | inr (exist _ a _) => noaccess_model a (page_round_up (ms_gpr ms 1)) model
  end.

Definition mmap_na_U (ms : machine_state) (model : Model) : Type :=
  ({e : Z | In e mmap_errnos}
   + {a : word | grant_ok_na_pin model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true})%type.

Definition mmap_na_effu (ms : machine_state) (model : Model) (i : mmap_na_U ms model) : SyscallEffect :=
  match i with
  | inl (exist _ e _) => mkEffectU (errno_ret e) [] [] [] [] []
  | inr (exist _ a _) => mkEffectU a [] [] [(a, page_round_up (ms_gpr ms 1))] [] []
  end.

Definition mmap_na_modu (ms : machine_state) (model : Model) (i : mmap_na_U ms model) : Model :=
  match i with
  | inl _ => model
  | inr (exist _ a _) => noaccess_model a (page_round_up (ms_gpr ms 1)) model
  end.

Lemma node_mmap_noaccess_u : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  node_ok_u segs (mkCfg ms model) (mmap_na_U ms model) (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mmap_na_effu ms model i))) (mmap_na_modu ms model i)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
  pose proof (fun eff => mmap_noaccess_check segs ms x8 model eff Hno Hargs) as Hchk.
  cbv zeta in Hchk.
  assert (HnZ : (0 <= page_round_up_Z (bv_unsigned (ms_gpr ms 1)))%Z).
  { pose proof (u64_range (ms_gpr ms 1)) as Hr1.
    pose proof (page_round_up_Z_bounds (bv_unsigned (ms_gpr ms 1)) (proj1 Hr1)). lia. }
  apply (node_chk segs ms model x8 (mmap_na_U ms model) (mmap_na_effu ms model) (mmap_na_modu ms model) Hh Hsvc).
  - intros [[e He] | [a Ha]]; cbn [mmap_na_effu mmap_na_modu]; rewrite Hchk.
    + rewrite (errno_ret_in_intro _ e He). reflexivity.
    + rewrite (grant_na_pin_not_errno model a _ HnZ Ha), Ha.
      unfold page_round_up. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:Herr.
    + destruct us; [|discriminate]. injection Hc as <- <-.
      apply errno_ret_in_true in Herr. destruct Herr as (e & He & ->).
      exists (inl (exist _ e He)). repeat split; reflexivity.
    + destruct (grant_ok_na_pin model r (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Hg; [|discriminate].
      destruct (listNN_eqb us [(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hus; [|discriminate].
      apply listNN_eqb_eq in Hus. subst us. injection Hc as <- <-.
      exists (inr (exist _ r Hg)). cbn [mmap_na_effu mmap_na_modu]. unfold page_round_up.
      repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
    destruct (grant_ok_na_pin model r _ && listNN_eqb us _); discriminate.
  - intros [[e He] | [a Ha]]; cbn [mmap_na_modu]; [exact Hh | unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
  - intros [[e He] | [a Ha]]; cbn [mmap_na_modu]; [exact Hlazy | unfold noaccess_model; rewrite with_vmmaps_lazy'; exact Hlazy].
Qed.

Lemma node_mmap_noaccess : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  node_ok segs (mkCfg ms model) (mmap_na_I ms model) (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mmap_na_eff ms model i))) (mmap_na_model ms model i)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
  assert (HnZ : (0 <= page_round_up_Z (bv_unsigned (ms_gpr ms 1)))%Z).
  { pose proof (u64_range (ms_gpr ms 1)) as Hr1.
    pose proof (page_round_up_Z_bounds (bv_unsigned (ms_gpr ms 1)) (proj1 Hr1)). lia. }
  pose proof (node_ok_refusable segs (mkCfg ms model) {e : Z | In e mmap_errnos}
                {a : word | grant_ok_na_pin model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true}
                {e : Z | In e (mmap_errnos_when
                                 (mmap_reserve_refusable model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))))}
                (fun r' => exist _ (proj1_sig r') (proj2 (proj1 (mmap_errnos_when_in _ _) (proj2_sig r'))))
                (fun _ => []) _ (node_mmap_noaccess_u ms model x8 Hh Hlazy Hsvc Hno Hargs)) as Hc.
  refine (node_ok_ext segs _ _ _ _ _ _ (Hc _ _ _ _ _ _ _) _ _).
  - exact (kit_pending_off_sysno segs ms model x8 222 Hsvc Hno eq_refl).
  - intros [e He]. cbn [mmap_na_effu mmap_na_modu].
    rewrite (child_refusal_b_syscall segs ms model x8 _ _ Hsvc Hh). cbn [eff_ret].
    exact (refusal_b_mmap_errno (sys_input segs ms x8) model e Hno He).
  - intros [a Ha]. cbn [mmap_na_effu mmap_na_modu].
    rewrite (child_refusal_b_syscall segs ms model x8 _ (noaccess_model a (page_round_up (ms_gpr ms 1)) model) Hsvc
               ltac:(unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh)).
    cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8) model a Hno).
    exact (grant_na_pin_not_errno model a _ HnZ Ha).
  - intros [[e He] | [a Ha]]; cbn [mmap_na_modu cfg_model];
      [exact Hh | unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
  - intros [e He] [a Ha]. apply mmap_errnos_when_in in He as [Hr _].
    rewrite mmap_reserve_refusable_vm in Hr.
    pose proof (proj1 (mmap_na_refusable_vm_iff _ _) Hr a) as E.
    rewrite <- grant_ok_na_pin_vm in E. congruence.
  - intros HG [e He].
    assert (Hr : mmap_reserve_refusable model (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true).
    { rewrite mmap_reserve_refusable_vm. apply mmap_na_refusable_vm_iff. intros a.
      rewrite <- grant_ok_na_pin_vm.
      destruct (grant_ok_na_pin model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:E;
        [exfalso; exact (HG (exist _ a E)) | reflexivity]. }
    exists (exist _ e (proj2 (mmap_errnos_when_in _ _) (conj Hr He))). split; reflexivity.
  - intros [[e He] | [a Ha]]; cbn [mmap_na_modu cfg_limit cfg_model]; reflexivity.
  - intros i. reflexivity.
  - intros [[e He] | [a Ha]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_noaccess_ix : forall ms model x8 A (B : word -> TSet),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_noaccess_args_ok ms ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  let n := page_round_up (ms_gpr ms 1) in
  (mmap_reserve_refusable model nZ = true ->
   realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (errno_ret ENOMEM) [] [] [] [] []))) model) A) ->
  (forall a, grant_ok_na_pin model a nZ = true ->
     realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffectU a [] [] [(a, n)] [] [])))
                          (noaccess_model a n model)) (B a)) ->
  realizes segs (mkCfg ms model)
           (t_ixc (mmap_reserve_refusable model nZ = true) A (fun a => grant_ok_na_pin model a nZ = true) B).
Proof.
  intros ms model x8 A B Hh Hlazy Hsvc Hno Hargs nZ n HA HB.
  destruct (mmap_na_I_inhabited ms model) as [i0].
  apply (rz_conseq segs _
           (t_alt (fun i : mmap_na_I ms model =>
                     t_emit [] (match i with inl _ => A | inr (exist _ a _) => B a end)))).
  - apply (rz_node segs (mkCfg ms model) (mmap_na_I ms model) (fun _ => []) _
             (fun i => match i with inl _ => A | inr (exist _ a _) => B a end)
             i0
             (node_mmap_noaccess ms model x8 Hh Hlazy Hsvc Hno Hargs)).
    intros [[e He] | [a Ha]]; cbn.
    + apply mmap_errnos_when_in in He as [Hr He]. destruct He as [<- | []]. exact (HA Hr).
    + apply HB. exact Ha.
  - intros tr. unfold t_alt, t_ixc. split.
    + intros [[[e He] | [a Ha]] Ht]; cbn in Ht.
      * left. apply mmap_errnos_when_in in He as [Hr He]. split; [exact Hr|].
        apply (t_emit_nil_eq A); [eapply realizes_nonempty; exact (HA Hr) | exact Ht].
      * right. exists a. split; [exact Ha|].
        apply (t_emit_nil_eq (B a)); [eapply realizes_nonempty; apply HB; exact Ha | exact Ht].
    + intros [[Hr Ht] | (a & Ha & Ht)].
      * exists (inl (exist _ ENOMEM (proj2 (mmap_errnos_when_in _ ENOMEM) (conj Hr ENOMEM_in_mmap_errnos)))). cbn.
        apply t_emit_nil_eq; [eapply realizes_nonempty; exact (HA Hr) | exact Ht].
      * exists (inr (exist _ a Ha)). cbn.
        apply t_emit_nil_eq; [eapply realizes_nonempty; apply HB; exact Ha | exact Ht].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mprot_I (model : Model) (addr n : word) : Type :=
  ({e : Z | In e (mprotect_errnos_when (mprotect_refusable model addr n))}   (* [comment removed for export] *)
   + {u : unit | mprotect_budget_ok model addr n = true})%type.

(* [comment removed for export] *)
Lemma mprot_I_inhabited : forall model addr n, inhabited (mprot_I model addr n).
Proof.
  intros model addr n. unfold mprot_I, mprotect_refusable.
  destruct (mprotect_budget_ok model addr n) eqn:Eb.
  - constructor. right. exists tt. reflexivity.
  - constructor. left. exists ENOMEM. apply ENOMEM_in_mprotect_errnos.
Qed.

Definition mprot_eff (model : Model) (addr n : word) (i : mprot_I model addr n) : SyscallEffect :=
  match i with
  | inl (exist _ e _) => mkEffectU (errno_ret e) [] [] [] [] []
  | inr _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []
  end.

Definition mprot_model (model : Model) (addr n : word) (i : mprot_I model addr n) : Model :=
  match i with
  | inl _ => model
  | inr _ => mprotect_model addr n model
  end.

Definition mprot_U (model : Model) (addr n : word) : Type :=
  ({e : Z | In e mprotect_errnos} + {u : unit | mprotect_budget_ok model addr n = true})%type.

Definition mprot_effu (model : Model) (addr n : word) (i : mprot_U model addr n) : SyscallEffect :=
  match i with
  | inl (exist _ e _) => mkEffectU (errno_ret e) [] [] [] [] []
  | inr _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []
  end.

Definition mprot_modu (model : Model) (addr n : word) (i : mprot_U model addr n) : Model :=
  match i with
  | inl _ => model
  | inr _ => mprotect_model addr n model
  end.

Lemma node_mprotect_u : forall ms model x8 (addr : word) (len : Z),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  node_ok_u segs (mkCfg ms model) (mprot_U model addr n) (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mprot_effu model addr n i))) (mprot_modu model addr n i)).
Proof.
  intros ms model x8 addr len Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  pose proof (fun eff => mprotect_check segs ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Hz : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by reflexivity.
  apply (node_chk segs ms model x8 (mprot_U model addr n) (mprot_effu model addr n) (mprot_modu model addr n) Hh Hsvc).
  - intros [[e He] | [[] Hb]]; cbn [mprot_effu mprot_modu]; rewrite Hchk.
    + rewrite (errno_ret_in_intro _ e He). reflexivity.
    + rewrite Hz, Hb. unfold w_is0. rewrite bv_eqb_refl. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate].
    destruct us; [|destruct (errno_ret_in mprotect_errnos r); discriminate].
    destruct cs; [|destruct (errno_ret_in mprotect_errnos r); discriminate].
    destruct ci; [|destruct (errno_ret_in mprotect_errnos r); discriminate].
    destruct (errno_ret_in mprotect_errnos r) eqn:Herr.
    + destruct zs; [|discriminate]. injection Hc as <- <-.
      apply errno_ret_in_true in Herr. destruct Herr as (e & He & ->).
      exists (inl (exist _ e He)). repeat split; reflexivity.
    + destruct (mprotect_budget_ok model addr n) eqn:Hb; [|discriminate].
      destruct (w_is0 r) eqn:Hr; [|discriminate]. unfold w_is0 in Hr. apply bv_eqb_eq in Hr. subst r.
      destruct (listNN_eqb zs [(addr, n)]) eqn:Hzs; [|discriminate].
      apply listNN_eqb_eq in Hzs. subst zs. injection Hc as <- <-.
      exists (inr (exist _ tt Hb)). repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate].
    destruct us; [|destruct (errno_ret_in mprotect_errnos r); discriminate].
    destruct cs; [|destruct (errno_ret_in mprotect_errnos r); discriminate].
    destruct ci; [|destruct (errno_ret_in mprotect_errnos r); discriminate].
    destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
    destruct (mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]); discriminate.
  - intros [[e He] | [u Hb]]; cbn [mprot_modu]; [exact Hh | unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh].
  - intros [[e He] | [u Hb]]; cbn [mprot_modu]; [exact Hlazy | unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hlazy].
Qed.

Lemma node_mprotect : forall ms model x8 (addr : word) (len : Z),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  node_ok segs (mkCfg ms model) (mprot_I model addr n) (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (mprot_eff model addr n i))) (mprot_model model addr n i)).
Proof.
  intros ms model x8 addr len Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  pose proof (node_ok_refusable segs (mkCfg ms model) {e : Z | In e mprotect_errnos}
                {u : unit | mprotect_budget_ok model addr n = true}
                {e : Z | In e (mprotect_errnos_when (mprotect_refusable model addr n))}
                (fun r' => exist _ (proj1_sig r') (proj2 (proj1 (mprotect_errnos_when_in _ _) (proj2_sig r'))))
                (fun _ => []) _
                (node_mprotect_u ms model x8 addr len Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 Hna Hma)) as Hc.
  refine (node_ok_ext segs _ _ _ _ _ _ (Hc _ _ _ _ _ _ _) _ _).
  - exact (kit_pending_off_sysno segs ms model x8 226 Hsvc Hno eq_refl).
  - intros [e He]. cbn [mprot_effu mprot_modu].
    rewrite (child_refusal_b_syscall segs ms model x8 _ _ Hsvc Hh). cbn [eff_ret].
    exact (refusal_b_mprotect_errno (sys_input segs ms x8) model e Hno He).
  - intros [u Hb]. cbn [mprot_effu mprot_modu].
    rewrite (child_refusal_b_syscall segs ms model x8 _ (mprotect_model addr n model) Hsvc
               ltac:(unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh)).
    cbn [eff_ret]. rewrite (refusal_b_mprotect (sys_input segs ms x8) model _ Hno). reflexivity.
  - intros [[e He] | [u Hb]]; cbn [mprot_modu cfg_model];
      [exact Hh | unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh].
  - intros [e He] [u Hb]. apply mprotect_errnos_when_in in He as [Hr _].
    unfold mprotect_refusable in Hr. rewrite Hb in Hr. discriminate Hr.
  - intros HG [e He].
    assert (Hr : mprotect_refusable model addr n = true).
    { unfold mprotect_refusable. apply negb_true_iff. apply Bool.not_true_is_false.
      intros E. exact (HG (exist _ tt E)). }
    exists (exist _ e (proj2 (mprotect_errnos_when_in _ _) (conj Hr He))). split; reflexivity.
  - intros [[e He] | [u Hb]]; cbn [mprot_modu cfg_limit cfg_model]; [reflexivity | reflexivity].
  - intros i. reflexivity.
  - intros [[e He] | [u Hb]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_mprotect_ix : forall ms model x8 (addr : word) (len : Z) A B,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (mprotect_budget_ok model addr n = false ->
   realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (errno_ret ENOMEM) [] [] [] [] []))) model) A) ->
  (mprotect_budget_ok model addr n = true ->
   realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
                        (mprotect_model addr n model)) B) ->
  realizes segs (mkCfg ms model)
           (fun tr => (mprotect_budget_ok model addr n = false /\ A tr) \/ (mprotect_budget_ok model addr n = true /\ B tr)).
Proof.
  intros ms model x8 addr len A B Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma HA HB.
  destruct (mprot_I_inhabited model addr n) as [i0].
  assert (Hrf : forall e, In e (mprotect_errnos_when (mprotect_refusable model addr n)) ->
                          mprotect_budget_ok model addr n = false /\ e = ENOMEM).
  { intros e He. apply mprotect_errnos_when_in in He as [Hr He]. unfold mprotect_refusable in Hr.
    apply negb_true_iff in Hr. split; [exact Hr|]. destruct He as [<- | []]. reflexivity. }
  apply (rz_conseq segs _
           (t_alt (fun i : mprot_I model addr n => t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node segs (mkCfg ms model) (mprot_I model addr n) (fun _ => []) _
             (fun i => match i with inl _ => A | inr _ => B end)
             i0
             (node_mprotect ms model x8 addr len Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 Hna Hma)).
    intros [[e He] | [u Hb]]; cbn.
    + destruct (Hrf e He) as [Hb ->]. exact (HA Hb).
    + apply HB. exact Hb.
  - intros tr. unfold t_alt. split.
    + intros [[[e He] | [u Hb]] Ht]; cbn in Ht.
      * left. destruct (Hrf e He) as [Hb _]. split; [exact Hb|].
        apply (t_emit_nil_eq A); [eapply realizes_nonempty; exact (HA Hb) | exact Ht].
      * right. split; [exact Hb|]. apply (t_emit_nil_eq B); [eapply realizes_nonempty; apply HB; exact Hb | exact Ht].
    + intros [[Hb Ht] | [Hb Ht]].
      * assert (He : In ENOMEM (mprotect_errnos_when (mprotect_refusable model addr n))).
        { apply mprotect_errnos_when_in. split; [unfold mprotect_refusable; rewrite Hb; reflexivity | apply ENOMEM_in_mprotect_errnos]. }
        exists (inl (exist _ ENOMEM He)). cbn. apply t_emit_nil_eq; [eapply realizes_nonempty; exact (HA Hb) | exact Ht].
      * exists (inr (exist _ tt Hb)). cbn. apply t_emit_nil_eq; [eapply realizes_nonempty; apply HB; exact Hb | exact Ht].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_fixed_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with
             | [] => CheckOk model []
             | _ => if listNN_eqb us [(addr, n)]
                    then CheckOk (with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps model) addr n) model) []
                    else CheckReject
             end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
        then CheckOk (fixed_noaccess_model addr n model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno (H1 & H2 & H3 & H4 & H5) H0 Hal Hpos H1' Hlen Htop n Hrf Hmc.
  pose proof (u64_range addr) as Har. alloc_top_bounds.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold two_pow_64, stack_max_size in *. lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1'; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, H0, Hu1.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 50)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
  replace (mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  cbn [negb]. cbv zeta.
  rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64, stack_max_size in *; lia).
  rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
  fold n. rewrite Hrf, Hmc. cbn [andb].
  destruct eff as [r ws zs us cs ci].
  unfold fixed_noaccess_model, with_mmap_replacement, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_mmap_fixed_noaccess : forall ms model x8 (addr : word) (len : Z),
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                    (fixed_noaccess_model addr n model)).
Proof.
  intros ms model x8 addr len Hh Hlazy Hsvc Hno Hargs H0 Hal Hpos H1 Hlen Htop n Hrf Hmc.
  pose proof (fun eff => mmap_fixed_check ms x8 model eff addr len Hno Hargs H0 Hal Hpos H1 Hlen Htop Hrf Hmc) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  assert (Hae : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds.
    pose proof (page_round_up_Z_bounds len ltac:(lia)). unfold two_pow_64 in *. lia. }
  apply (node_single_cfg segs ms model x8 (mkEffectU addr [] [] [(addr, n)] [] []) (fixed_noaccess_model addr n model) [] Hh Hsvc).
  - exact (kit_pending_off_sysno segs ms model x8 222 Hsvc Hno eq_refl).
  - rewrite Hchk. rewrite Hae, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
  - cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8) model addr Hno). exact Hae.
  - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:Herr.
    + right. apply errno_ret_in_true in Herr. destruct Herr as (e & He & ->). cbn [eff_ret].
      split; [exact (refusal_b_mmap_errno (sys_input segs ms x8) model e Hno He) |].
      destruct us as [|u us].
      * injection Hc as <- <-. exact Hh.
      * destruct (listNN_eqb (u :: us) [(addr, n)]); [|discriminate]. injection Hc as <- <-.
        unfold with_mmap_destroyed. rewrite vm_forget_range_halted, with_vmmaps_halted. exact Hh.
    + left. destruct (bv_eqb r addr) eqn:Hr; [|discriminate]. apply bv_eqb_eq in Hr. subst r.
      destruct (listNN_eqb us [(addr, n)]) eqn:Hus; [|discriminate].
      apply listNN_eqb_eq in Hus. subst us. injection Hc as <- <-. repeat split; reflexivity.
  - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
    destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r);
      [ destruct us as [|u us]; [discriminate | destruct (listNN_eqb (u :: us) [(addr, n)]); discriminate]
      | destruct (bv_eqb r addr && listNN_eqb us [(addr, n)]); discriminate ].
  - unfold fixed_noaccess_model. rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
  - unfold fixed_noaccess_model. apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy.
  - unfold fixed_noaccess_model, vm_forget_range. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_fixed_noaccess_ms : forall ms model x8 (addr : word) (len : Z) KB,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222%Z ->
  mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
                       (fixed_noaccess_model addr n model)) KB ->
  realizes segs (mkCfg ms model) KB.
Proof.
  intros ms model x8 addr len KB Hh Hlazy Hsvc Hno Hargs H0 Hal Hpos H1 Hlen Htop n Hrf Hmc HB.
  pose proof (node_mmap_fixed_noaccess ms model x8 addr len Hh Hlazy Hsvc Hno Hargs H0 Hal Hpos H1 Hlen Htop Hrf Hmc) as Hnode.
  cbv zeta in Hnode. fold n in Hnode.
  assert (HB0 : KB []) by (eapply realizes_nonempty; exact HB).
  apply (rz_conseq segs _ (t_alt (fun _ : unit => t_emit [] KB))).
  - apply (rz_node segs (mkCfg ms model) unit (fun _ => []) _ (fun _ => KB) tt Hnode).
    intros []. exact HB.
  - intros tr. unfold t_alt. split.
    + intros [[] Ht]. exact (proj1 (t_emit_nil_eq KB HB0 tr) Ht).
    + intros Ht. exists tt. apply t_emit_nil_eq; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_set_tid_ms : forall ms model x8 T,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms tid)) (with_tid tid model)) T) ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Htid Hk.
  apply (rz_conseq segs _ (t_alt (fun _ : tid_I => T)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply rz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid; [exact Hh | exact Hlazy | exact Hsvc | exact Hno | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig]. apply Hk. exact Ht.
Qed.

End Nodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes2.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma mprotect_rw_check : forall ms x8 model eff (addr len : word),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = len -> (0 < bv_unsigned len)%Z ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  map_contains (vm_noaccess (m_vmmaps model)) addr (page_round_up len) = false ->
  map_contains (vm_maps (m_vmmaps model)) addr (page_round_up len) = true ->
  region_free (vm_noaccess (m_vmmaps model)) addr (page_round_up len) = true ->
  check_syscall (sys_input segs ms x8) eff model = check_ret_only eff (Z_to_bv 64 0) model [].
Proof.
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma Hrf.
  rewrite (check_syscall_226 segs ms x8 eff model Hno). unfold check_mprotect.
  rewrite H0, H1, H2.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  assert (E1 : w_is0 len = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  cbv beta iota zeta. fold (page_round_up len). rewrite Hna, Hma, Hrf. cbn [andb].
  destruct eff as [r ws zs us cs ci]. unfold check_ret_only, w_is0. reflexivity.
Qed.

Lemma rz_mprotect_rw_ms : forall ms model x8 (addr len : word) T,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = len -> (0 < bv_unsigned len)%Z ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  map_contains (vm_noaccess (m_vmmaps model)) addr (page_round_up len) = false ->
  map_contains (vm_maps (m_vmmaps model)) addr (page_round_up len) = true ->
  region_free (vm_noaccess (m_vmmaps model)) addr (page_round_up len) = true ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] []))) model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 addr len T Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 Hna Hma Hrf Hc.
  apply (rz_ret_chk_silent segs ms model x8 (Z_to_bv 64 0) model T Hh Hsvc); [| exact Hh | exact Hlazy | reflexivity | exact Hc].
  intros eff. eapply mprotect_rw_check; eassumption.
Qed.

End Nodes2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section At.
Context {fx : FPState}.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma adv_uret_st : forall regs pc mem rom r,
  advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffectU r [] [] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. apply adv_ret_st. Qed.

Lemma adv_zeros_st : forall regs pc mem rom r a n,
  advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffectU r [] [(a, n)] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold ecall_st, apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_zlist_st : forall regs pc mem rom r zs,
  advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffectU r [] zs [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (apply_zeros mem zs) rom.
Proof.
  intros.
  unfold ecall_st, apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies apply_unmaps].
  unfold mkst, regupd. rewrite b_npc4. reflexivity.
Qed.

Lemma adv_unmap_st : forall regs pc mem rom r a n,
  advance_past_svc (apply_effect (ecall_st regs pc mem rom) (mkEffectU r [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold ecall_st, apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma minus_one_of_unsigned : forall (x : word),
  bv_unsigned x = (2 ^ 64 - 1)%Z -> x = Z_to_bv 64 (-1).
Proof. intros x H. apply bv_eq. rewrite H, Z_to_bv_unsigned. reflexivity. Qed.

Lemma nonzero_word : forall (x : word), (0 < bv_unsigned x)%Z -> x <> Z_to_bv 64 0.
Proof. intros x H E. rewrite E in H. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in H. lia. Qed.

(* [comment removed for export] *)

Lemma mmap_args_ok_of : forall regs pc mem rom (len : word),
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 3%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  mmap_args_ok (ecall_st regs pc mem rom).
Proof.
  intros regs pc mem rom len H11 Hlen H12 H13 H14 H15. unfold mmap_args_ok.
  rewrite ecall_st_gpr1, ecall_st_gpr2, ecall_st_gpr3, ecall_st_gpr4, ecall_st_gpr5, H11.
  split; [apply nonzero_word; exact Hlen|].
  split; [apply word_of_unsigned; exact H12|].
  split; [apply word_of_unsigned; exact H13|].
  split; [apply minus_one_of_unsigned; exact H14|].
  apply word_of_unsigned; exact H15.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_ix_at : forall regs (pc : word) mem rom model w (len : word) A (B : word -> TSet),
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 3%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  let h := m_vmmaps model in
  (mmap_refusable_vm h (page_round_up_Z (bv_unsigned len)) = true ->
   realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) A) ->
  (forall a, grant_ok_vm h a (page_round_up_Z (bv_unsigned len)) = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (page_round_up len) mem) rom)
                          (with_vmmaps (vm_mmap a (page_round_up len) h) model)) (B a)) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (fun tr => (mmap_refusable_vm h (page_round_up_Z (bv_unsigned len)) = true /\ A tr)
                      \/ exists a, grant_ok_vm h a (page_round_up_Z (bv_unsigned len)) = true /\ B a tr).
Proof.
  intros regs pc mem rom model w len A B Hp HF HE H17 H11 Hlen H12 H13 H14 H15 h HA HB.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (mmap_args_ok_of regs pc mem rom len H11 Hlen H12 H13 H14 H15) as Hargs.
  destruct (vm_budget_leaf h (page_round_up_Z (bv_unsigned len))) eqn:Hleaf.
  { (* [comment removed for export] *)
    destruct (vm_budget_leaf_true _ _ Hleaf) as [Hsmall Hover].
    apply (rz_refused_svc segs _ model (getr regs 17)); [exact Hh | apply ecall_st_svc | | exact Hsmall | |].
    - rewrite (mmap_budget_mark segs _ _ model H17 Hargs), ecall_st_gpr1, H11, (vm_backing_used_pure _ Hp).
      fold h. rewrite Hover. reflexivity.
    - destruct (Bool.bool_dec (mmap_refusable_vm h (page_round_up_Z (bv_unsigned len))) true) as [Hr | Hr].
      + left. split; [exact Hr | exact (realizes_nonempty segs _ _ (HA Hr))].
      + apply Bool.not_true_is_false in Hr.
        destruct (proj1 (mmap_refusable_vm_false_iff _ _) Hr) as [a0 Ha0].
        right. exists a0. split; [exact Ha0 | exact (realizes_nonempty segs _ _ (HB a0 Ha0))].
    - intros tr tr' [[Hr HAt] | (a & Ha & HBt)] Hpre.
      + left. split; [exact Hr | exact (realizes_pclosed segs _ _ (HA Hr) _ _ HAt Hpre)].
      + right. exists a. split; [exact Ha | exact (realizes_pclosed segs _ _ (HB a Ha) _ _ HBt Hpre)]. }
  eapply rz_conseq.
  - apply (rz_mmap_ix segs (ecall_st regs pc mem rom) model (getr regs 17) A B Hh Hlazy
             (ecall_st_svc _ _ _ _) H17 Hargs).
    + intros Hr. rewrite ecall_st_gpr1, H11, (mmap_refusable_pure _ _ Hp Hleaf) in Hr.
      rewrite adv_setgpr0_st. exact (HA Hr).
    + intros a Ha. rewrite ecall_st_gpr1, H11 in Ha |- *.
      rewrite (grant_ok_pure _ _ _ _ Hp Hleaf) in Ha.
      rewrite adv_grant_st. apply HB. exact Ha.
  - intros tr. unfold t_ixc. rewrite ecall_st_gpr1, H11, (mmap_refusable_pure _ _ Hp Hleaf). fold h.
    split; (intros [Ht | (a & Ha & Ht)]; [left; exact Ht | right; exists a; split; [| exact Ht]]);
      [rewrite (grant_ok_pure _ _ _ _ Hp Hleaf) in Ha | rewrite (grant_ok_pure _ _ _ _ Hp Hleaf)]; exact Ha.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_sure_ix_at : forall regs (pc : word) mem rom model w (len : word) (B : word -> TSet),
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 3%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  let h := m_vmmaps model in
  mmap_refusable_vm h (page_round_up_Z (bv_unsigned len)) = false ->
  (forall a, grant_ok_vm h a (page_round_up_Z (bv_unsigned len)) = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (page_round_up len) mem) rom)
                          (with_vmmaps (vm_mmap a (page_round_up len) h) model)) (B a)) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (fun tr => exists a, grant_ok_vm h a (page_round_up_Z (bv_unsigned len)) = true /\ B a tr).
Proof.
  intros regs pc mem rom model w len B Hp HF HE H17 H11 Hlen H12 H13 H14 H15 h Hnr HB.
  eapply rz_conseq.
  - apply (rz_mmap_ix_at regs pc mem rom model w len t_nil B Hp HF HE H17 H11 Hlen H12 H13 H14 H15).
    + intros Hr. fold h in Hr. rewrite Hnr in Hr. discriminate.
    + exact HB.
  - intros tr. cbv zeta. fold h. rewrite Hnr. split.
    + intros [[Hr _] | H]; [discriminate | exact H].
    + intros H. right. exact H.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_anon_at : forall regs (pc : word) mem rom model w (len : word) B,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 3%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  let h := m_vmmaps model in
  (forall a, grant_ok_vm h a (page_round_up_Z (bv_unsigned len)) = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (page_round_up len) mem) rom)
                          (with_vmmaps (vm_mmap a (page_round_up len) h) model)) B) ->
  (exists a, grant_ok_vm h a (page_round_up_Z (bv_unsigned len)) = true) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) B.
Proof.
  intros regs pc mem rom model w len B Hp HF HE H17 H11 Hlen H12 H13 H14 H15 h HB [a0 Ha0].
  eapply rz_conseq.
  - apply (rz_mmap_sure_ix_at regs pc mem rom model w len (fun _ => B) Hp HF HE H17 H11 Hlen H12 H13 H14 H15);
      [apply mmap_refusable_vm_false_iff; exists a0; exact Ha0 | exact HB].
  - intros tr. split.
    + intros (a & _ & Ht). exact Ht.
    + intros Ht. exists a0. split; [exact Ha0 | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_nogrant_at : forall regs (pc : word) mem rom model w (len : word) A,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 3%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  (forall a, grant_ok_vm (m_vmmaps model) a (page_round_up_Z (bv_unsigned len)) = false) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) A ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) A.
Proof.
  intros regs pc mem rom model w len A Hp HF HE H17 H11 Hlen H12 H13 H14 H15 Hng HA.
  eapply rz_conseq.
  - apply (rz_mmap_ix_at regs pc mem rom model w len A (fun _ => A) Hp HF HE H17 H11 Hlen H12 H13 H14 H15 (fun _ => HA)).
    intros a Ha. rewrite Hng in Ha. discriminate.
  - intros tr. split; [intros [[_ Ht] | (a & Ha & _)]; [exact Ht | rewrite Hng in Ha; discriminate] |].
    intros Ht. left. split; [apply mmap_refusable_vm_iff; exact Hng | exact Ht].
Qed.

(* [comment removed for export] *)

Lemma mmap_noaccess_args_ok_of : forall regs pc mem rom (len : word),
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 0%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  mmap_noaccess_args_ok (ecall_st regs pc mem rom).
Proof.
  intros regs pc mem rom len H11 Hlen H12 H13 H14 H15. unfold mmap_noaccess_args_ok.
  rewrite ecall_st_gpr1, ecall_st_gpr2, ecall_st_gpr3, ecall_st_gpr4, ecall_st_gpr5, H11.
  split; [apply nonzero_word; exact Hlen|].
  split; [apply word_of_unsigned; exact H12|].
  split; [apply word_of_unsigned; exact H13|].
  split; [apply minus_one_of_unsigned; exact H14|].
  apply word_of_unsigned; exact H15.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_noaccess_ix_at : forall regs (pc : word) mem rom model w (len : word) A (B : word -> TSet),
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 0%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  let h := m_vmmaps model in
  (mmap_na_refusable_vm h (page_round_up_Z (bv_unsigned len)) = true ->
   realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) A) ->
  (forall a, grant_ok_na_vm h a (page_round_up_Z (bv_unsigned len)) = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a (page_round_up len) mem) rom)
                          (with_vmmaps (vm_noacc a (page_round_up len) h) model)) (B a)) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (fun tr => (mmap_na_refusable_vm h (page_round_up_Z (bv_unsigned len)) = true /\ A tr)
                      \/ exists a, grant_ok_na_vm h a (page_round_up_Z (bv_unsigned len)) = true /\ B a tr).
Proof.
  intros regs pc mem rom model w len A B Hp HF HE H17 H11 Hlen H12 H13 H14 H15 h HA HB.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (mmap_noaccess_args_ok_of regs pc mem rom len H11 Hlen H12 H13 H14 H15) as Hargs.
  eapply rz_conseq.
  - apply (rz_mmap_noaccess_ix segs (ecall_st regs pc mem rom) model (getr regs 17) A B Hh Hlazy
             (ecall_st_svc _ _ _ _) H17 Hargs).
    + intros Hr. rewrite ecall_st_gpr1, H11, mmap_reserve_refusable_vm in Hr.
      rewrite adv_uret_st. exact (HA Hr).
    + intros a Ha. rewrite ecall_st_gpr1, H11 in Ha |- *.
      rewrite grant_ok_na_pin_vm in Ha.
      rewrite adv_unmap_st. apply HB. exact Ha.
  - intros tr. unfold t_ixc. rewrite ecall_st_gpr1, H11, mmap_reserve_refusable_vm. fold h.
    split; (intros [Ht | (a & Ha & Ht)]; [left; exact Ht | right; exists a; split; [| exact Ht]]);
      [rewrite grant_ok_na_pin_vm in Ha | rewrite grant_ok_na_pin_vm]; exact Ha.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_noaccess_sure_ix_at : forall regs (pc : word) mem rom model w (len : word) (B : word -> TSet),
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 0%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  let h := m_vmmaps model in
  mmap_na_refusable_vm h (page_round_up_Z (bv_unsigned len)) = false ->
  (forall a, grant_ok_na_vm h a (page_round_up_Z (bv_unsigned len)) = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a (page_round_up len) mem) rom)
                          (with_vmmaps (vm_noacc a (page_round_up len) h) model)) (B a)) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (fun tr => exists a, grant_ok_na_vm h a (page_round_up_Z (bv_unsigned len)) = true /\ B a tr).
Proof.
  intros regs pc mem rom model w len B Hp HF HE H17 H11 Hlen H12 H13 H14 H15 h Hnr HB.
  eapply rz_conseq.
  - apply (rz_mmap_noaccess_ix_at regs pc mem rom model w len t_nil B Hp HF HE H17 H11 Hlen H12 H13 H14 H15).
    + intros Hr. fold h in Hr. rewrite Hnr in Hr. discriminate.
    + exact HB.
  - intros tr. cbv zeta. fold h. rewrite Hnr. split.
    + intros [[Hr _] | H]; [discriminate | exact H].
    + intros H. right. exact H.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_noaccess_at : forall regs (pc : word) mem rom model w (len : word) B,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 0%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  let h := m_vmmaps model in
  (forall a, grant_ok_na_vm h a (page_round_up_Z (bv_unsigned len)) = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a (page_round_up len) mem) rom)
                          (with_vmmaps (vm_noacc a (page_round_up len) h) model)) B) ->
  (exists a, grant_ok_na_vm h a (page_round_up_Z (bv_unsigned len)) = true) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) B.
Proof.
  intros regs pc mem rom model w len B Hp HF HE H17 H11 Hlen H12 H13 H14 H15 h HB [a0 Ha0].
  eapply rz_conseq.
  - apply (rz_mmap_noaccess_sure_ix_at regs pc mem rom model w len (fun _ => B) Hp HF HE H17 H11 Hlen H12 H13 H14 H15);
      [apply mmap_na_refusable_vm_false_iff; exists a0; exact Ha0 | exact HB].
  - intros tr. split.
    + intros (a & _ & Ht). exact Ht.
    + intros Ht. exists a0. split; [exact Ha0 | exact Ht].
Qed.

Lemma rz_mmap_noaccess_nogrant_at : forall regs (pc : word) mem rom model w (len : word) A,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 0%Z -> bv_unsigned (getr regs 13) = 34%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  (forall a, grant_ok_na_vm (m_vmmaps model) a (page_round_up_Z (bv_unsigned len)) = false) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) A ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) A.
Proof.
  intros regs pc mem rom model w len A Hp HF HE H17 H11 Hlen H12 H13 H14 H15 Hng HA.
  eapply rz_conseq.
  - apply (rz_mmap_noaccess_ix_at regs pc mem rom model w len A (fun _ => A) Hp HF HE H17 H11 Hlen H12 H13 H14 H15 (fun _ => HA)).
    intros a Ha. rewrite Hng in Ha. discriminate.
  - intros tr. split; [intros [[_ Ht] | (a & Ha & _)]; [exact Ht | rewrite Hng in Ha; discriminate] |].
    intros Ht. left. split; [apply mmap_na_refusable_vm_iff; exact Hng | exact Ht].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_munmap_at : forall regs (pc : word) mem rom model w (addr len : word) T,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 215%Z ->
  getr regs 10 = addr -> getr regs 11 = len ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned len)%Z ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= TASK_SIZE)%Z ->
  map_has (vm_maps (m_vmmaps model)) addr (page_round_up len) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill addr (page_round_up len) mem) rom)
                       (with_vmmaps (vm_munmap addr (page_round_up len) (m_vmmaps model)) model)) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w addr len T Hp HF HE H17 H10 H11 Hal Hlen Hts Hhas Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  assert (Hargs : munmap_args_ok (ecall_st regs pc mem rom) model).
  { unfold munmap_args_ok. rewrite ecall_st_gpr0, ecall_st_gpr1, H10, H11.
    split; [exact Hal|]. split; [apply nonzero_word; exact Hlen|]. split; [exact Hts | exact Hhas]. }
  eapply (ShapeAlg.rz_munmap segs (ecall_st regs pc mem rom) model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | exact H17 | exact Hargs |].
  unfold munmap_eff. rewrite ecall_st_gpr0, ecall_st_gpr1, H10, H11, adv_unmap_st.
  rewrite (munmap_model_pure _ _ _ Hp). exact Hc.
Qed.

(* [comment removed for export] *)

Lemma rz_brk_query_at : forall regs (pc : word) mem rom model w T,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 214%Z ->
  bv_unsigned (getr regs 10) = 0%Z ->
  realizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hp HF HE H17 H10 Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (rz_brk_query_ms segs (ecall_st regs pc mem rom) model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | exact H17
    | rewrite ecall_st_gpr0; apply word_of_unsigned; exact H10 |].
  rewrite adv_uret_st. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rz_brk_grow_at : forall regs (pc : word) mem rom model w (req : word) A B,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 214%Z ->
  getr regs 10 = req ->
  let h := m_vmmaps model in
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) < bv_unsigned req)%Z ->
  (brk_grow_ok_vm h req req = false ->
   realizes segs (mkCfg (mkst (regupd regs 10 (vm_brk h)) (v_addi pc 4) mem rom) model) A) ->
  (brk_grow_ok_vm h req req = true ->
   realizes segs (mkCfg (mkst (regupd regs 10 req) (v_addi pc 4)
                              (apply_zeros mem (brk_zeros req req (vm_brk h))) rom)
                        (with_vmmaps (vm_brk_grow req h) model)) B) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (fun tr => (brk_grow_ok_vm h req req = false /\ A tr) \/ (brk_grow_ok_vm h req req = true /\ B tr)).
Proof.
  intros regs pc mem rom model w req A B Hp HF HE H17 H10 h Hb0 Hs Hlt HA HB.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_conseq.
  - apply (rz_brk_grow_ms segs (ecall_st regs pc mem rom) model (getr regs 17) req A B Hh Hlazy
             (ecall_st_svc _ _ _ _) H17 ltac:(rewrite ecall_st_gpr0; exact H10) Hb0 Hs Hlt).
    + intros Hg. rewrite adv_uret_st. apply HA.
      rewrite <- (brk_grow_ok_pure _ _ _ Hp). exact Hg.
    + intros Hg. rewrite adv_zlist_st. fold h.
      rewrite (brk_model_grow_vm model req Hb0 Hlt). apply HB.
      rewrite <- (brk_grow_ok_pure _ _ _ Hp). exact Hg.
  - intros tr. rewrite (brk_grow_ok_pure _ _ _ Hp). split; intros Ht; exact Ht.
Qed.

(* [comment removed for export] *)
Lemma rz_brk_grow_aligned_at : forall regs (pc : word) mem rom model w (d : Z) A B,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 214%Z ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  (brk_grow_ok_vm h (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false ->
   realizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) A) ->
  (brk_grow_ok_vm h (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h)
                                      (vm_init_sp h)) model)) B) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (fun tr => (brk_grow_ok_vm h (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false
                       /\ A tr)
                      \/ (brk_grow_ok_vm h (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true
                       /\ B tr)).
Proof.
  intros regs pc mem rom model w d A B Hp HF HE H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 HA HB.
  unfold b, h in *. clear b h.
  pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
  destruct (brk_grow_post_aligned model d Hbal Hdal Hd Hb0 Hnw) as [Hz Hm].
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d))
                  = (bv_unsigned (vm_brk (m_vmmaps model)) + d)%Z) by (apply u64_lit; lia).
  apply (rz_brk_grow_at regs pc mem rom model w _ A B Hp HF HE H17 H10 Hb0
           ltac:(rewrite Hureq; exact Hs) ltac:(rewrite Hureq; lia) HA).
  intros Hg. rewrite Hz, apply_zeros_one. change (zmem mem ?b ?d) with (zfill b d mem).
  rewrite <- (brk_model_grow_vm model _ Hb0 ltac:(rewrite Hureq; lia)). rewrite Hm.
  apply HB. exact Hg.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_mprotect_unprotect_at : forall regs (pc : word) mem rom model w (addr len : word) A B,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 226%Z ->
  getr regs 10 = addr -> getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 3%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < 2 ^ 64)%Z ->
  let h := m_vmmaps model in
  map_contains (vm_noaccess h) addr (page_round_up len) = true ->
  map_contains (vm_maps h) addr (page_round_up len) = true ->
  (mprot_ok_vm h addr (page_round_up len) = false ->
   realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) model) A) ->
  (mprot_ok_vm h addr (page_round_up len) = true ->
   realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                              (zfill addr (page_round_up len) mem) rom)
                        (with_vmmaps (vm_unprotect addr (page_round_up len) h) model)) B) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (fun tr => (mprot_ok_vm h addr (page_round_up len) = false /\ A tr)
                      \/ (mprot_ok_vm h addr (page_round_up len) = true /\ B tr)).
Proof.
  intros regs pc mem rom model w addr len A B Hp HF HE H17 H10 H11 Hlen H12 Hal Hnw h Hna Hma HA HB.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  assert (H1 : ms_gpr (ecall_st regs pc mem rom) 1 = Z_to_bv 64 (bv_unsigned len)).
  { rewrite ecall_st_gpr1, H11. symmetry. apply u64_roundtrip. }
  destruct (mprot_leaf (m_vmmaps model) addr (page_round_up len)) eqn:Hleaf.
  { (* [comment removed for export] *)
    destruct (mprot_leaf_true _ _ _ Hleaf) as [Hsmall Hover].
    assert (Hok : mprot_ok_vm h addr (page_round_up len) = true).
    { unfold mprot_ok_vm. apply orb_true_iff. right. apply Z.ltb_lt. exact Hsmall. }
    apply (rz_refused_svc segs _ model (getr regs 17)); [exact Hh | apply ecall_st_svc | | exact Hsmall | |].
    - rewrite (mprotect_budget_mark segs (ecall_st regs pc mem rom) (getr regs 17) model addr (bv_unsigned len) H17
                 ltac:(rewrite ecall_st_gpr0; exact H10) Hal H1 Hlen ltac:(unfold two_pow_64; exact Hnw)
                 ltac:(rewrite ecall_st_gpr2; apply word_of_unsigned; exact H12) Hna Hma).
      fold (page_round_up len). rewrite (mprotect_budget_ok_real _ _ _ Hp). rewrite Hover. reflexivity.
    - right. split; [exact Hok | exact (realizes_nonempty segs _ _ (HB Hok))].
    - intros tr tr' [[Hb HAt] | [Hb HBt]] Hpre.
      + rewrite Hok in Hb. discriminate Hb.
      + right. split; [exact Hb | exact (realizes_pclosed segs _ _ (HB Hb) _ _ HBt Hpre)]. }
  eapply rz_conseq.
  - apply (rz_mprotect_ix segs (ecall_st regs pc mem rom) model (getr regs 17) addr (bv_unsigned len) A B
             Hh Hlazy (ecall_st_svc _ _ _ _) H17
             ltac:(rewrite ecall_st_gpr0; exact H10) Hal H1 Hlen
             ltac:(unfold two_pow_64; exact Hnw)
             ltac:(rewrite ecall_st_gpr2; apply word_of_unsigned; exact H12) Hna Hma).
    + intros Hb. rewrite adv_uret_st. apply HA. fold (page_round_up len) in Hb.
      rewrite (mprotect_budget_ok_pure _ _ _ Hp Hleaf) in Hb. exact Hb.
    + intros Hb. rewrite adv_zeros_st. fold (page_round_up len) in Hb |- *. fold h.
      apply HB. rewrite (mprotect_budget_ok_pure _ _ _ Hp Hleaf) in Hb. exact Hb.
  - intros tr. fold (page_round_up len). rewrite (mprotect_budget_ok_pure _ _ _ Hp Hleaf). split; intros Ht; exact Ht.
Qed.

(* [comment removed for export] *)
Lemma rz_mprotect_unprotect_sure_at : forall regs (pc : word) mem rom model w (addr len : word) B,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 226%Z ->
  getr regs 10 = addr -> getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 3%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < 2 ^ 64)%Z ->
  let h := m_vmmaps model in
  map_contains (vm_noaccess h) addr (page_round_up len) = true ->
  map_contains (vm_maps h) addr (page_round_up len) = true ->
  mprot_ok_vm h addr (page_round_up len) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (zfill addr (page_round_up len) mem) rom)
                       (with_vmmaps (vm_unprotect addr (page_round_up len) h) model)) B ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) B.
Proof.
  intros regs pc mem rom model w addr len B Hp HF HE H17 H10 H11 Hlen H12 Hal Hnw h Hna Hma Hok HB.
  eapply rz_conseq.
  - apply (rz_mprotect_unprotect_at regs pc mem rom model w addr len t_nil B Hp HF HE H17 H10 H11 Hlen H12 Hal Hnw Hna Hma).
    + intros Hb. fold h in Hb. rewrite Hok in Hb. discriminate.
    + intros _. exact HB.
  - intros tr. cbv zeta. fold h. rewrite Hok. split.
    + intros [[Hb _] | [_ Ht]]; [discriminate | exact Ht].
    + intros Ht. right. split; [reflexivity | exact Ht].
Qed.

(* [comment removed for export] *)
Lemma rz_mprotect_already_rw_at : forall regs (pc : word) mem rom model w (addr len : word) T,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 226%Z ->
  getr regs 10 = addr -> getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 3%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) < 2 ^ 64)%Z ->
  let h := m_vmmaps model in
  map_contains (vm_noaccess h) addr (page_round_up len) = false ->
  map_contains (vm_maps h) addr (page_round_up len) = true ->
  region_free (vm_noaccess h) addr (page_round_up len) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w addr len T Hp HF HE H17 H10 H11 Hlen H12 Hal Hnw h Hna Hma Hrf Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (rz_mprotect_rw_ms segs (ecall_st regs pc mem rom) model (getr regs 17) addr len T Hh Hlazy
            (ecall_st_svc _ _ _ _) H17
            ltac:(rewrite ecall_st_gpr0; exact H10) Hal
            ltac:(rewrite ecall_st_gpr1; exact H11) Hlen
            ltac:(unfold two_pow_64; exact Hnw)
            ltac:(rewrite ecall_st_gpr2; apply word_of_unsigned; exact H12) Hna Hma Hrf).
  rewrite adv_ret_st. exact Hc.
Qed.

(* [comment removed for export] *)

Lemma mmap_fixed_args_ok_of : forall regs pc mem rom (len : word),
  getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 0%Z -> bv_unsigned (getr regs 13) = 50%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  mmap_fixed_args_ok (ecall_st regs pc mem rom).
Proof.
  intros regs pc mem rom len H11 Hlen H12 H13 H14 H15. unfold mmap_fixed_args_ok.
  rewrite ecall_st_gpr1, ecall_st_gpr2, ecall_st_gpr3, ecall_st_gpr4, ecall_st_gpr5, H11.
  split; [apply nonzero_word; exact Hlen|].
  split; [apply word_of_unsigned; exact H12|].
  split; [apply word_of_unsigned; exact H13|].
  split; [apply minus_one_of_unsigned; exact H14|].
  apply word_of_unsigned; exact H15.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_fixed_noaccess_at : forall regs (pc : word) mem rom model w (addr len : word) KB,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 222%Z ->
  getr regs 10 = addr -> getr regs 11 = len -> (0 < bv_unsigned len)%Z ->
  bv_unsigned (getr regs 12) = 0%Z -> bv_unsigned (getr regs 13) = 50%Z ->
  bv_unsigned (getr regs 14) = (2 ^ 64 - 1)%Z -> bv_unsigned (getr regs 15) = 0%Z ->
  let h := m_vmmaps model in
  (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top h)%Z ->
  region_free (vm_reserved h) addr (page_round_up len) = true ->
  map_contains (vm_maps h) addr (page_round_up len) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr (page_round_up len) mem) rom)
                       (with_vmmaps (vm_fixed_ok addr (page_round_up len) h) model)) KB ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w addr len KB Hp HF HE H17 H10 H11 Hlen H12 H13 H14 H15 h
         Hal Hpos Htop Hrf Hmc HB.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  pose proof (mmap_fixed_args_ok_of regs pc mem rom len H11 Hlen H12 H13 H14 H15) as Hargs.
  assert (H1 : ms_gpr (ecall_st regs pc mem rom) 1 = Z_to_bv 64 (bv_unsigned len)).
  { rewrite ecall_st_gpr1, H11. symmetry. apply u64_roundtrip. }
  apply (rz_mmap_fixed_noaccess_ms segs (ecall_st regs pc mem rom) model (getr regs 17) addr (bv_unsigned len)
             KB Hh Hlazy (ecall_st_svc _ _ _ _) H17 Hargs
             ltac:(rewrite ecall_st_gpr0; exact H10) Hal Hpos H1 Hlen Htop Hrf Hmc).
  rewrite adv_unmap_st. fold (page_round_up len). fold h.
  rewrite (fixed_noaccess_model_pure _ _ _ Hp). exact HB.
Qed.

(* [comment removed for export] *)
Lemma fixed_top_of_ceiling : forall h (addr : word) (nZ : Z),
  init_sp_ok h -> (bv_unsigned addr + nZ <= alloc_ceiling)%Z -> (bv_unsigned addr + nZ <= alloc_top h)%Z.
Proof. intros h addr nZ Hi Hc. apply alloc_top_ge_of_ceiling; assumption. Qed.

(* [comment removed for export] *)

Lemma rz_set_tid_at : forall regs (pc : word) mem rom model w T,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 96%Z ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) T) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros regs pc mem rom model w T Hp HF HE H17 Htid Hk.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply (rz_set_tid_ms segs (ecall_st regs pc mem rom) model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | exact H17 | exact Htid |].
  intros tid Ht. rewrite adv_setgpr0_st. apply Hk. exact Ht.
Qed.

Lemma md_pure_with_tid : forall t md, md_pure md -> md_pure (with_tid t md).
Proof. intros t md [H1 H2 H3]. constructor; [exact H1 | exact H2 | exact H3]. Qed.

End At.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section Pigeonhole.
Local Open Scope Z_scope.

Lemma grant_exists_na_vm_gen : forall (h : VmMaps) (N n C : Z),
  init_sp_ok h ->
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= C ->
  bottomup_floor + C * (2 * N) + N <= alloc_ceiling ->
  exists a, grant_ok_na_vm h a n = true.
Proof.
  intros h N n C Hsp HN HNal Hn Hsz Hcnt Hband.
  pose proof (alloc_ceiling_le_alloc_top h Hsp) as Htop.
  set (l := vm_reserved h ++ vm_maps h) in *.
  destruct (pick_candidate N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
    as (j & Hj & Hfree).
  apply in_seq in Hj.
  exists (Z_to_bv 64 (cand N j)).
  pose proof alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
  assert (Hc : bottomup_floor <= cand N j <= bottomup_floor + C * (2 * N)) by (unfold cand; nia).
  unfold grant_ok_na_vm. rewrite !u64_lit by lia.
  assert (E1 : cand N j mod page_size = 0).
  { unfold cand. rewrite Hfv. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal by lia.
    rewrite Z.mul_0_r. reflexivity. }
  rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  fold l. rewrite (region_free_of_noconflict l (cand N j) n) by (first [lia | exact Hfree]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_vm_gen : forall (h : VmMaps) (N n C : Z),
  init_sp_ok h ->
  0 < N -> N mod page_size = 0 -> 0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= C ->
  bottomup_floor + C * (2 * N) + N <= alloc_ceiling ->
  vm_backed_bytes h + n <= vm_limit h ->
  exists a, grant_ok_vm h a n = true.
Proof.
  intros h N n C Hsp HN HNal Hn Hsz Hcnt Hband Hlive.
  destruct (grant_exists_na_vm_gen h N n C Hsp HN HNal Hn Hsz Hcnt Hband) as [a Ha].
  exists a. unfold grant_ok_vm. unfold grant_ok_na_vm in Ha. rewrite Ha.
  rewrite (vm_budget_ok_real h n Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_vm : forall (h : VmMaps) (n : Z),
  init_sp_ok h ->
  0 <= n <= 2 ^ 30 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= 40000 ->
  vm_backed_bytes h + n <= vm_limit h ->
  exists a, grant_ok_vm h a n = true.
Proof.
  intros h n Hsp Hn Hsz Hcnt Hlive.
  apply (grant_exists_vm_gen h (2 ^ 30) n 40000); try assumption; try lia.
  - reflexivity.
  - rewrite alloc_ceiling_val, bottomup_floor_val. cbn. discriminate.
Qed.

Lemma grant_exists_na_vm : forall (h : VmMaps) (n : Z),
  init_sp_ok h ->
  0 <= n <= 2 ^ 30 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= 40000 ->
  exists a, grant_ok_na_vm h a n = true.
Proof.
  intros h n Hsp Hn Hsz Hcnt.
  apply (grant_exists_na_vm_gen h (2 ^ 30) n 40000); try assumption; try lia.
  - reflexivity.
  - rewrite alloc_ceiling_val, bottomup_floor_val. cbn. discriminate.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_vm_big : forall (h : VmMaps) (n : Z),
  init_sp_ok h ->
  0 <= n <= 2 ^ 35 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35) (vm_reserved h ++ vm_maps h) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= 1000 ->
  vm_backed_bytes h + n <= vm_limit h ->
  exists a, grant_ok_vm h a n = true.
Proof.
  intros h n Hsp Hn Hsz Hcnt Hlive.
  apply (grant_exists_vm_gen h (2 ^ 35) n 1000); try assumption; try lia.
  - reflexivity.
  - rewrite alloc_ceiling_val, bottomup_floor_val. cbn. discriminate.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_vm_over_budget : forall (h : VmMaps) (a : word) (n : Z),
  BUDGET_BIG <= vm_limit h ->   
  vm_limit h < vm_backed_bytes h + n ->
  grant_ok_vm h a n = false.
Proof.
  intros h a n Hbig H. unfold grant_ok_vm. rewrite (vm_budget_ok_big h n Hbig).
  rewrite (proj2 (Z.leb_gt _ _) H). rewrite andb_false_r. reflexivity.
Qed.

Lemma grant_exists : forall hint (m : Model) (n : Z),
  md_pure m -> init_sp_ok (m_vmmaps m) ->
  0 <= n <= 2 ^ 30 ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000 ->
  vm_backed_bytes (m_vmmaps m) + n <= vm_limit (m_vmmaps m) ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hp Hsp Hn Hsz Hcnt Hlive.
  destruct (grant_exists_vm (m_vmmaps m) n Hsp Hn Hsz Hcnt Hlive) as [a Ha].
  assert (Hleaf : vm_budget_leaf (m_vmmaps m) n = false).
  { unfold vm_budget_leaf. rewrite (proj2 (Z.leb_le _ _) Hlive). apply andb_false_r. }
  exists a. rewrite (grant_ok_pure hint m a n Hp Hleaf). exact Ha.
Qed.

Lemma grant_ok_over_budget : forall hint (m : Model) (a : word) (n : Z),
  md_pure m -> vm_limit (m_vmmaps m) < vm_backed_bytes (m_vmmaps m) + n ->
  grant_ok hint m a n = false.
Proof.
  intros hint m a n Hp H. unfold grant_ok. rewrite (vm_backing_used_pure _ Hp).
  rewrite (proj2 (Z.leb_gt _ _) H). rewrite andb_false_r. reflexivity.
Qed.

End Pigeonhole.
