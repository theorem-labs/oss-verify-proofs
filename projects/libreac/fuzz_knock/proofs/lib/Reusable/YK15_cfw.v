From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0i YK0n YK15 YM06 YO0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import Uniform.
Import ListNotations.
Open Scope bv_scope.
Section a. Context {fx : YK11.FPState}.
Section b.
Variable segs : list Segment.
Lemma cut_free_of_succ : forall c, ~ budget_refused_at segs c ->
(forall e c', sstep_cfg segs ACFG c e (SNext c') -> cut_free segs c') -> cut_free segs c.
Proof using.
intros c Hb H tr c' Hstar.
inversion Hstar as [c0 | c1 evs c2 tr' c3 Hs Hst]; subst; [exact Hb | exact (H evs c2 Hs tr' c' Hst)].
Qed.
Lemma cut_free_halted : forall c, m_halted (cfg_model c) <> None -> cut_free segs c.
Proof using.
intros c Hh tr c' Hstar.
inversion Hstar as [c0 | c1 evs c2 tr' c3 Hs Hst]; subst.
- intros (Hn & _). exact (Hh Hn).
- exfalso. exact (Hh (sstep_halted_none segs _ _ _ Hs)).
Qed.
Lemma cut_free_node : forall c (I : Type) evs nx,
node_ok segs c I evs nx -> ~ budget_refused_at segs c -> (forall i, cut_free segs (nx i)) -> cut_free segs c.
Proof using.
intros c I evs nx [_ Hc] Hb H. apply (cut_free_of_succ c Hb). intros e c' Hs.
destruct (Hc e (SNext c') Hs) as (i & _ & E). injection E as ->. apply H.
Qed.
Lemma alloc_refused_false : forall i m, ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
alloc_budget_refused_b i m = false.
Proof using.
intros i m Hn. unfold alloc_budget_refused_b.
destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 214) as [E|_]; [exfalso; apply Hn; rewrite E; vm_compute; auto|].
destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 216) as [E|_]; [exfalso; apply Hn; rewrite E; vm_compute; auto|].
destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 222) as [E|_]; [exfalso; apply Hn; rewrite E; vm_compute; auto|].
destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 226) as [E|_]; [exfalso; apply Hn; rewrite E; vm_compute; auto|].
reflexivity.
Qed.
Lemma nr_node_sys : forall ms model x8 (I : Type) evs nx,
node_ok segs (mkCfg ms model) I evs nx -> ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
~ budget_refused_at segs (mkCfg ms model).
Proof using.
intros ms model x8 I evs nx [_ Hc] Hsvc Hno (Hh & [(Hn & _) | (y8 & Hy8 & [Hb | (eff & m' & evs' & Hspec & Hh' & Hmat)])]);
cbn [cfg_ms cfg_model] in *.
- congruence.
- rewrite Hsvc in Hy8. injection Hy8 as <-.
rewrite (alloc_refused_false _ model ltac:(rewrite in_sysno_sys_input; exact (alloc_no_b_false _ Hno))) in Hb.
discriminate Hb.
- rewrite Hsvc in Hy8. injection Hy8 as <-.
assert (Hs : sstep_cfg segs ACFG (mkCfg ms model) [] SError).
{ eapply sstep_cfg_syscall_materialization_fault;
[exact Hh | exact Hsvc | exact Hspec | exact (acfg_nonspurious_no segs ms x8 _ model eff eq_refl Hno) | exact Hh' | exact Hmat]. }
destruct (Hc [] SError Hs) as (i & _ & E). discriminate E.
Qed.
Lemma not_refused_exit : forall ms model x8,
m_halted model = None -> ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
~ budget_refused_at segs (mkCfg ms model).
Proof using.
intros ms model x8 Hh Hsvc Hx8 (_ & [(Hn & _) | (y8 & Hy8 & [Hb | (eff & m' & evs & Hspec & Hh' & _)])]);
cbn [cfg_ms cfg_model] in *.
- congruence.
- rewrite Hsvc in Hy8. injection Hy8 as <-. unfold alloc_budget_refused_b in Hb.
rewrite in_sysno_sys_input in Hb. destruct Hx8 as [E|E]; rewrite E in Hb; discriminate Hb.
- rewrite Hsvc in Hy8. injection Hy8 as <-.
destruct (exit_dispatch_ok_inv _ _ _ _ _ ltac:(rewrite in_sysno_sys_input; exact Hx8) Hspec) as (_ & -> & _).
discriminate Hh'.
Qed.
Lemma uniform_node : forall c (I : Type) evs nx,
node_ok segs c I evs nx -> place_uniform segs c -> (forall i, uniform segs (nx i)) -> uniform segs c.
Proof using.
intros c I evs nx [_ Hc] Hp H. apply (uniform_intro segs c Hp). intros e c' Hs.
destruct (Hc e (SNext c') Hs) as (i & _ & E). injection E as ->. apply H.
Qed.
Lemma place_uniform_sys : forall ms model x8,
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false -> place_uniform segs (mkCfg ms model).
Proof using.
intros ms model x8 Hsvc Hno. apply place_uniform_nonplacement. intros y8 len.
exact (nonalloc_not_placement segs ms model x8 y8 len Hsvc Hno).
Qed.
End b.
Section c.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_conseq : forall c T T', crealizes B c T -> t_eq T T' -> crealizes B c T'.
Proof using.
intros c T T' H HT.
exact (crealizes_intro B c T' (rz_conseq segs c T T' (crealizes_realizes B c T H) HT)
  (crealizes_cut_free B c T H) (crealizes_uniform B c T H)).
Qed.
Lemma crealizes_emit_nil : forall c T, crealizes B c T -> crealizes B c (t_emit [] T).
Proof using.
intros c T H.
exact (crealizes_intro B c _ (realizes_emit_nil segs c T (crealizes_realizes B c T H))
  (crealizes_cut_free B c T H) (crealizes_uniform B c T H)).
Qed.
Lemma crz_step : forall ms model ms' T,
m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
crealizes B (mkCfg ms' model) T -> crealizes B (mkCfg ms model) T.
Proof using.
intros ms model ms' T Hh Hlz Hsvc Hst H. apply crealizes_intro.
- exact (rz_step segs ms model ms' T Hh Hlz Hsvc Hst (crealizes_realizes B _ T H)).
- exact (cut_free_instr B ms model ms' Hh Hlz Hsvc Hst (crealizes_cut_free B _ T H)).
- exact (uniform_instr B ms model ms' Hh Hlz Hsvc Hst (crealizes_uniform B _ T H)).
Qed.
Lemma crz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I evs nx -> ~ budget_refused_at segs c -> place_uniform segs c ->
(forall i, crealizes B (nx i) (T i)) -> crealizes B c (t_alt (fun i => t_emit (evs i) (T i))).
Proof using.
intros c I evs nx T i0 Hn Hb Hp H. apply crealizes_intro.
- exact (rz_node segs c I evs nx T i0 Hn (fun i => crealizes_realizes B _ _ (H i))).
- exact (cut_free_node segs c I evs nx Hn Hb (fun i => crealizes_cut_free B _ _ (H i))).
- exact (uniform_node segs c I evs nx Hn Hp (fun i => crealizes_uniform B _ _ (H i))).
Qed.
Lemma crz_silent : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I (fun _ => []) nx -> ~ budget_refused_at segs c -> place_uniform segs c ->
(forall i, crealizes B (nx i) (T i)) -> crealizes B c (t_alt T).
Proof using.
intros c I nx T i0 Hn Hb Hp H. apply crealizes_intro.
- exact (rz_silent segs c I nx T i0 Hn (fun i => crealizes_realizes B _ _ (H i))).
- exact (cut_free_node segs c I _ nx Hn Hb (fun i => crealizes_cut_free B _ _ (H i))).
- exact (uniform_node segs c I _ nx Hn Hp (fun i => crealizes_uniform B _ _ (H i))).
Qed.
Lemma crz_node_sys : forall ms model x8 (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) I evs nx ->
(forall i, crealizes B (nx i) (T i)) -> crealizes B (mkCfg ms model) (t_alt (fun i => t_emit (evs i) (T i))).
Proof using.
intros ms model x8 I evs nx T i0 Hsvc Hno Hn H.
exact (crz_node _ I evs nx T i0 Hn (nr_node_sys segs ms model x8 I evs nx Hn Hsvc Hno)
  (place_uniform_sys segs ms model x8 Hsvc Hno) H).
Qed.
Lemma crz_silent_sys : forall ms model x8 (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
(forall i, crealizes B (nx i) (T i)) -> crealizes B (mkCfg ms model) (t_alt T).
Proof using.
intros ms model x8 I nx T i0 Hsvc Hno Hn H.
exact (crz_silent _ I nx T i0 Hn (nr_node_sys segs ms model x8 I _ nx Hn Hsvc Hno)
  (place_uniform_sys segs ms model x8 Hsvc Hno) H).
Qed.
Lemma crz_halt : forall c, m_halted (cfg_model c) <> None -> crealizes B c t_nil.
Proof using.
intros c Hh. exact (crealizes_intro B c t_nil (rz_halt segs c Hh) (cut_free_halted segs c Hh) (uniform_halted segs c Hh)).
Qed.
Lemma crz_silent1 : forall c c' T,
node_ok segs c unit (fun _ => []) (fun _ => c') -> ~ budget_refused_at segs c -> place_uniform segs c ->
crealizes B c' T -> crealizes B c T.
Proof using.
intros c c' T Hn Hb Hp H. apply crealizes_intro.
- exact (rz_silent1 segs c c' T Hn (crealizes_realizes B _ _ H)).
- exact (cut_free_node segs c unit _ _ Hn Hb (fun _ => crealizes_cut_free B _ _ H)).
- exact (uniform_node segs c unit _ _ Hn Hp (fun _ => crealizes_uniform B _ _ H)).
Qed.
Lemma crz_emit1 : forall c c' e T,
node_ok segs c unit (fun _ => e) (fun _ => c') -> ~ budget_refused_at segs c -> place_uniform segs c ->
crealizes B c' T -> crealizes B c (t_emit e T).
Proof using.
intros c c' e T Hn Hb Hp H. apply crealizes_intro.
- exact (rz_emit1 segs c c' e T Hn (crealizes_realizes B _ _ H)).
- exact (cut_free_node segs c unit _ _ Hn Hb (fun _ => crealizes_cut_free B _ _ H)).
- exact (uniform_node segs c unit _ _ Hn Hp (fun _ => crealizes_uniform B _ _ H)).
Qed.
Lemma crz_silent1_sys : forall ms model x8 c' T,
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => c') ->
crealizes B c' T -> crealizes B (mkCfg ms model) T.
Proof using.
intros ms model x8 c' T Hsvc Hno Hn H.
exact (crz_silent1 _ c' T Hn (nr_node_sys segs ms model x8 unit _ _ Hn Hsvc Hno)
  (place_uniform_sys segs ms model x8 Hsvc Hno) H).
Qed.
Lemma crz_emit1_sys : forall ms model x8 c' e T,
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) unit (fun _ => e) (fun _ => c') ->
crealizes B c' T -> crealizes B (mkCfg ms model) (t_emit e T).
Proof using.
intros ms model x8 c' e T Hsvc Hno Hn H.
exact (crz_emit1 _ c' e T Hn (nr_node_sys segs ms model x8 unit _ _ Hn Hsvc Hno)
  (place_uniform_sys segs ms model x8 Hsvc Hno) H).
Qed.
Lemma crz_exit : forall ms model x8,
m_halted model = None -> ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
crealizes B (mkCfg ms model) (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof using.
intros ms model x8 Hh Hsvc Hx8.
assert (Hsucc : forall e c', sstep_cfg segs ACFG (mkCfg ms model) e (SNext c') -> m_halted (cfg_model c') <> None).
{ intros e c' Hs. destruct (sstep_exit_inv segs ms model x8 e (SNext c') Hh Hsvc Hx8 (sstep_of_cfg segs ACFG _ e _ Hs)) as [_ E].
  injection E as ->. cbn. discriminate. }
apply crealizes_intro.
- exact (rz_exit segs ms model x8 Hh Hsvc Hx8).
- apply (cut_free_of_succ segs _ (not_refused_exit segs ms model x8 Hh Hsvc Hx8)).
  intros e c' Hs. exact (cut_free_halted segs c' (Hsucc e c' Hs)).
- apply (uniform_intro segs _ (place_uniform_sys segs ms model x8 Hsvc
    ltac:(destruct Hx8 as [E|E]; rewrite E; vm_compute; reflexivity))).
  intros e c' Hs. exact (uniform_halted segs c' (Hsucc e c' Hs)).
Qed.
End c.
End a.
