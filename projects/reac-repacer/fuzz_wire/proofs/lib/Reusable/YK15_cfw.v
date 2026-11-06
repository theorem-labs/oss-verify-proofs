From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0i YK0n YK15 YM06 YM06_cf YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import SlotAgree AgreeLift.
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
End b.
Section c.
Variable B : malloc_syms.
Let segs := ms_segs B.
Lemma crz_conseq : forall c T T', crealizes B c T -> t_eq T T' -> crealizes B c T'.
Proof using. intros c T T' [H1 H2] HT. exact (conj (rz_conseq segs c T T' H1 HT) H2). Qed.
Lemma crealizes_emit_nil : forall c T, crealizes B c T -> crealizes B c (t_emit [] T).
Proof using. intros c T [H1 H2]. exact (conj (realizes_emit_nil segs c T H1) H2). Qed.
Lemma crz_step : forall ms model ms' T,
m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
crealizes B (mkCfg ms' model) T -> crealizes B (mkCfg ms model) T.
Proof using.
intros ms model ms' T Hh Hlz Hsvc Hst [H1 H2]. split.
- exact (rz_step segs ms model ms' T Hh Hlz Hsvc Hst H1).
- exact (cut_free_instr B ms model ms' Hh Hlz Hsvc Hst H2).
Qed.
Lemma crz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I evs nx -> ~ budget_refused_at segs c ->
(forall i, crealizes B (nx i) (T i)) -> crealizes B c (t_alt (fun i => t_emit (evs i) (T i))).
Proof using.
intros c I evs nx T i0 Hn Hb H. split.
- exact (rz_node segs c I evs nx T i0 Hn (fun i => proj1 (H i))).
- exact (cut_free_node segs c I evs nx Hn Hb (fun i => proj2 (H i))).
Qed.
Lemma crz_silent : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I (fun _ => []) nx -> ~ budget_refused_at segs c ->
(forall i, crealizes B (nx i) (T i)) -> crealizes B c (t_alt T).
Proof using.
intros c I nx T i0 Hn Hb H. split.
- exact (rz_silent segs c I nx T i0 Hn (fun i => proj1 (H i))).
- exact (cut_free_node segs c I _ nx Hn Hb (fun i => proj2 (H i))).
Qed.
Lemma crz_node_sys : forall ms model x8 (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) I evs nx ->
(forall i, crealizes B (nx i) (T i)) -> crealizes B (mkCfg ms model) (t_alt (fun i => t_emit (evs i) (T i))).
Proof using.
intros ms model x8 I evs nx T i0 Hsvc Hno Hn H.
exact (crz_node _ I evs nx T i0 Hn (nr_node_sys segs ms model x8 I evs nx Hn Hsvc Hno) H).
Qed.
Lemma crz_silent_sys : forall ms model x8 (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
(forall i, crealizes B (nx i) (T i)) -> crealizes B (mkCfg ms model) (t_alt T).
Proof using.
intros ms model x8 I nx T i0 Hsvc Hno Hn H.
exact (crz_silent _ I nx T i0 Hn (nr_node_sys segs ms model x8 I _ nx Hn Hsvc Hno) H).
Qed.
Lemma crz_halt : forall c, m_halted (cfg_model c) <> None -> crealizes B c t_nil.
Proof using. intros c Hh. exact (conj (rz_halt segs c Hh) (cut_free_halted segs c Hh)). Qed.
Lemma crz_silent1 : forall c c' T,
node_ok segs c unit (fun _ => []) (fun _ => c') -> ~ budget_refused_at segs c ->
crealizes B c' T -> crealizes B c T.
Proof using.
intros c c' T Hn Hb [H1 H2]. split.
- exact (rz_silent1 segs c c' T Hn H1).
- exact (cut_free_node segs c unit _ _ Hn Hb (fun _ => H2)).
Qed.
Lemma crz_emit1 : forall c c' e T,
node_ok segs c unit (fun _ => e) (fun _ => c') -> ~ budget_refused_at segs c ->
crealizes B c' T -> crealizes B c (t_emit e T).
Proof using.
intros c c' e T Hn Hb [H1 H2]. split.
- exact (rz_emit1 segs c c' e T Hn H1).
- exact (cut_free_node segs c unit _ _ Hn Hb (fun _ => H2)).
Qed.
Lemma crz_silent1_sys : forall ms model x8 c' T,
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => c') ->
crealizes B c' T -> crealizes B (mkCfg ms model) T.
Proof using.
intros ms model x8 c' T Hsvc Hno Hn H.
exact (crz_silent1 _ c' T Hn (nr_node_sys segs ms model x8 unit _ _ Hn Hsvc Hno) H).
Qed.
Lemma crz_emit1_sys : forall ms model x8 c' e T,
ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
node_ok segs (mkCfg ms model) unit (fun _ => e) (fun _ => c') ->
crealizes B c' T -> crealizes B (mkCfg ms model) (t_emit e T).
Proof using.
intros ms model x8 c' e T Hsvc Hno Hn H.
exact (crz_emit1 _ c' e T Hn (nr_node_sys segs ms model x8 unit _ _ Hn Hsvc Hno) H).
Qed.
Lemma crz_exit : forall ms model x8,
m_halted model = None -> ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
crealizes B (mkCfg ms model) (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof using.
intros ms model x8 Hh Hsvc Hx8. split.
- exact (rz_exit segs ms model x8 Hh Hsvc Hx8).
- apply (cut_free_of_succ segs _ (not_refused_exit segs ms model x8 Hh Hsvc Hx8)).
intros e c' Hs. destruct (sstep_exit_inv segs ms model x8 e (SNext c') Hh Hsvc Hx8 (sstep_of_cfg segs ACFG _ e _ Hs)) as [_ E].
injection E as ->. apply cut_free_halted. cbn. discriminate.
Qed.
Lemma crz_SR : forall c Q T, SR segs c Q -> avoid segs c Q ->
(forall c', Q c' -> crealizes B c' T) -> crealizes B c T.
Proof using. intros c Q T HS HA HK. exact (SR_cf_crealizes segs c Q T (conj HS HA) HK). Qed.
End c.
End a.
