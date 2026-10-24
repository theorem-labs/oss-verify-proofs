(** Generic budget definitions extracted from the pinned Varnish helper.
    Its unrelated concrete Varnish instruction certificates are omitted. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Acfg.
Import ListNotations.
Local Open Scope Z_scope.

Class BWorld : Type := mkBWorld {
  bw_on : bool;                      (* [comment removed for export] *)
  bw_lim : Z;                        (* [comment removed for export] *)
  bw_lim_ok : if bw_on then True else State.source_alloc_limit <= bw_lim
}.

(* [comment removed for export] *)
Definition bw_pinned : BWorld :=
  {| bw_on := false; bw_lim := State.source_alloc_limit; bw_lim_ok := Z.le_refl _ |}.
Definition bw_premise (lim : Z) : BWorld :=
  {| bw_on := true; bw_lim := lim; bw_lim_ok := I |}.

Section BW.
Context {BW : BWorld}.

(* [comment removed for export] *)
Definition bw_limit (L : Z) : Prop := if bw_on then True else State.source_alloc_limit <= L.

Lemma bw_limit_lim : bw_limit bw_lim.
Proof. unfold bw_limit. exact bw_lim_ok. Qed.

Lemma bw_limit_of_le : forall L, State.source_alloc_limit <= L -> bw_limit L.
Proof. intros L H. unfold bw_limit. destruct bw_on; [exact I | exact H]. Qed.

Lemma bw_limit_off : forall L, bw_on = false -> bw_limit L -> State.source_alloc_limit <= L.
Proof. intros L E H. unfold bw_limit in H. rewrite E in H. exact H. Qed.

(* [comment removed for export] *)
Definition bw_gate (i : SyscallInput) (m : Model) : Prop :=
  if bw_on then alloc_budget_refused_b i m = false else True.

Lemma bw_gate_off : forall i m, bw_on = false -> bw_gate i m.
Proof. intros i m E. unfold bw_gate. rewrite E. exact I. Qed.

Lemma bw_gate_on : forall i m, bw_on = true -> bw_gate i m -> alloc_budget_refused_b i m = false.
Proof. intros i m E H. unfold bw_gate in H. rewrite E in H. exact H. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition bw_excuse (c : config) : Prop :=
  if bw_on then budget_refused_at segs c else False.

(* [comment removed for export] *)
Definition never_excused (c0 : config) : Prop :=
  forall tr c, star_cfg segs ACFG c0 tr c -> ~ bw_excuse c.

Lemma never_excused_off : bw_on = false -> forall c0, never_excused c0.
Proof. intros E c0 tr c _ H. unfold bw_excuse in H. rewrite E in H. exact H. Qed.

Lemma never_excused_on : forall c0,
  ~ reaches_budget_refused_cfg segs ACFG c0 -> never_excused c0.
Proof.
  intros c0 Hn tr c Hstar Hex. unfold bw_excuse in Hex.
  destruct bw_on; [| exact Hex]. apply Hn. exists tr, c. split; assumption.
Qed.

Lemma never_excused_here : forall c, never_excused c -> ~ bw_excuse c.
Proof. intros c H. exact (H [] c (star_cfg_refl segs ACFG c)). Qed.

Lemma never_excused_star : forall c tr c',
  never_excused c -> star_cfg segs ACFG c tr c' -> never_excused c'.
Proof.
  intros c tr c' H Hstar tr' c'' Hstar'.
  exact (H (tr ++ tr') c'' (star_cfg_trans segs _ _ _ _ _ Hstar Hstar')).
Qed.

Lemma never_excused_step : forall c evs c',
  never_excused c -> sstep_cfg segs ACFG c evs (SNext c') -> never_excused c'.
Proof.
  intros c evs c' H Hss. eapply never_excused_star; [exact H | apply star_cfg_one; exact Hss].
Qed.

(* [comment removed for export] *)
Lemma bw_gate_of_not_excused : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff model' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
     m_vm_lazy model' = []) ->
  ~ bw_excuse (mkCfg ms model) ->
  bw_gate (sys_input segs ms x8) model.
Proof.
  intros ms model x8 Hh Hsvc Hlazy Hne. unfold bw_gate, bw_excuse in *.
  destruct bw_on; [| exact I].
  destruct (alloc_budget_refused_b (sys_input segs ms x8) model) eqn:E; [| reflexivity].
  exfalso. apply Hne.
  exact (proj2 (budget_refused_at_no_lazy_syscall segs ms model x8 Hh Hsvc Hlazy) E).
Qed.

Corollary bw_gate_of_never_excused : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff model' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
     m_vm_lazy model' = []) ->
  never_excused (mkCfg ms model) ->
  bw_gate (sys_input segs ms x8) model.
Proof.
  intros ms model x8 Hh Hsvc Hlazy Hne.
  apply bw_gate_of_not_excused; [exact Hh | exact Hsvc | exact Hlazy | apply never_excused_here; exact Hne].
Qed.

End WithSegs.
End BW.

(* [comment removed for export] *)
Lemma never_excused_of_premise : forall lim segs c0,
  ~ reaches_budget_refused_cfg segs ACFG c0 -> @never_excused (bw_premise lim) segs c0.
Proof. intros lim segs c0 H. apply never_excused_on. exact H. Qed.

Lemma never_excused_pinned : forall segs c0, @never_excused bw_pinned segs c0.
Proof. intros segs c0. apply never_excused_off. reflexivity. Qed.

(* [comment removed for export] *)
Lemma abr_brk : forall i m, in_sysno i = Z_to_bv 64 214 ->
  alloc_budget_refused_b i m = Sys.Mm.Mmap.brk_budget_refused_b m (in_arg i 0).
Proof. intros i m E. unfold alloc_budget_refused_b. rewrite E. reflexivity. Qed.

Lemma abr_mremap : forall i m, in_sysno i = Z_to_bv 64 216 ->
  alloc_budget_refused_b i m
  = Sys.Mm.Mremap.mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m.
Proof. intros i m E. unfold alloc_budget_refused_b. rewrite E. reflexivity. Qed.

Lemma abr_mmap : forall i m, in_sysno i = Z_to_bv 64 222 ->
  alloc_budget_refused_b i m
  = Sys.Mm.Mmap.mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m.
Proof. intros i m E. unfold alloc_budget_refused_b. rewrite E. reflexivity. Qed.

Lemma abr_mprotect : forall i m, in_sysno i = Z_to_bv 64 226 ->
  alloc_budget_refused_b i m
  = Sys.Mm.Mprotect.mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. intros i m E. unfold alloc_budget_refused_b. rewrite E. reflexivity. Qed.

Lemma abr_other : forall i m,
  bv_unsigned (in_sysno i) <> 214 -> bv_unsigned (in_sysno i) <> 216 ->
  bv_unsigned (in_sysno i) <> 222 -> bv_unsigned (in_sysno i) <> 226 ->
  alloc_budget_refused_b i m = false.
Proof.
  intros i m H1 H2 H3 H4. apply alloc_budget_refused_b_outside.
  cbn [alloc_mark_sysnos In]. intros [E|[E|[E|[E|[]]]]]; congruence.
Qed.
