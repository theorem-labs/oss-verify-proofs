(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from SpinAlg.v: the relation srealizes with a no-allocation-call check at each node (rzb), its soundness for the budget premise, and SpinAlg's node lemmas on the usage path restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: added a RomBase.sys_rob premise to the rzb node constructor and its derived lemmas, handled the vDSO budget-fault case in node_not_refused, added rzb_wrom, rzb_app_tail, rzb_run_segments, rzb_run_init, and dropped comments and indentation; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/SpinAlgB.v, 70 lines within its lines 16-378. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim LazyFrame SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common.Cfg Require RomBase SRomStable.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition nalloc_ok (c : config) : Prop :=
forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Lemma nalloc_ok_instr : forall ms model,
ms_svc_pending ms = None -> nalloc_ok (mkCfg ms model).
Proof. intros ms model H x8 Hx. cbn [cfg_ms] in Hx. congruence. Qed.
Lemma nalloc_ok_sysno : forall ms model x8,
ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
nalloc_ok (mkCfg ms model).
Proof.
intros ms model x8 Hsvc Hn y Hy. cbn [cfg_ms] in Hy.
rewrite Hsvc in Hy. injection Hy as <-. exact Hn.
Qed.
Lemma not_alloc_no : forall n,
negb (existsb (Z.eqb n) alloc_mark_sysnos) = true -> ~ In n alloc_mark_sysnos.
Proof.
intros n Hno Hin.
assert (E : existsb (Z.eqb n) alloc_mark_sysnos = true)
by (apply existsb_exists; exists n; split; [exact Hin | apply Z.eqb_refl]).
rewrite E in Hno. discriminate Hno.
Qed.
Lemma nalloc_ok_no : forall ms model x8 n,
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n ->
negb (existsb (Z.eqb n) alloc_mark_sysnos) = true ->
nalloc_ok (mkCfg ms model).
Proof.
intros ms model x8 n Hsvc Hn Hno. apply (nalloc_ok_sysno ms model x8 Hsvc).
rewrite Hn. exact (not_alloc_no n Hno).
Qed.
Lemma nalloc_ok_exit : forall ms model x8,
ms_svc_pending ms = Some x8 -> is_exit_no x8 -> nalloc_ok (mkCfg ms model).
Proof.
intros ms model x8 Hsvc Hx8.
destruct Hx8 as [E | E]; exact (nalloc_ok_no ms model x8 _ Hsvc E eq_refl).
Qed.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs scfg c I evs nx ->
RomBase.sys_rob segs c ->
nalloc_ok c ->
(forall i, rzb (nx i) (T i)) ->
rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
m_halted (cfg_model c) <> None ->
rzb c t_nil
| rzb_conseq : forall c T T',
rzb c T -> t_eq T T' -> rzb c T'.
Lemma rzb_nonempty : forall c T, rzb c T -> T [].
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
Qed.
Lemma rzb_silent1 : forall c c' T,
node_ok segs scfg c unit (fun _ => []) (fun _ => c') ->
RomBase.sys_rob segs c ->
nalloc_ok c ->
rzb c' T ->
rzb c T.
Proof.
intros c c' T Hnode Hrob Hb Hc.
apply (rzb_conseq c (t_alt (fun _ : unit => t_emit [] T))).
- apply (rzb_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.
Lemma rzb_emit1 : forall c c' e T,
node_ok segs scfg c unit (fun _ => e) (fun _ => c') ->
RomBase.sys_rob segs c ->
nalloc_ok c ->
rzb c' T ->
rzb c (t_emit e T).
Proof.
intros c c' e T Hnode Hrob Hb Hc.
apply (rzb_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (rzb_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
intros []; exact Hc.
- apply t_alt_unit.
Qed.
Lemma rzb_cases1 : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
node_ok segs scfg c I (fun _ => []) nx ->
RomBase.sys_rob segs c ->
nalloc_ok c ->
(forall i, rzb (nx i) T) ->
rzb c T.
Proof.
intros c I nx T i0 Hnode Hrob Hb Hc.
assert (HT0 : T []) by (eapply rzb_nonempty; apply (Hc i0)).
apply (rzb_conseq c (t_alt (fun _ : I => t_emit [] T))).
- apply (rzb_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob Hb). exact Hc.
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros Ht. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Ht).
Qed.
Lemma rzb_step : forall ms model ms' T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
rzb (mkCfg ms' model) T ->
rzb (mkCfg ms model) T.
Proof.
intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
eapply rzb_silent1;
[ apply node_instr; eassumption
| apply RomBase.sys_rob_instr; cbn [cfg_ms]; exact Hsvc
| apply nalloc_ok_instr; exact Hsvc | exact Hc].
Qed.
Lemma rzb_msteps : forall ms ms' model T,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
rzb (mkCfg ms' model) T ->
rzb (mkCfg ms model) T.
Proof.
intros ms ms' model T Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
intro Hc; [exact Hc|].
eapply rzb_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| apply IH; exact Hc].
Qed.
Lemma rzb_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
rzb (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros ms model x8 Hh Hsvc Hx8.
unfold t_exit.
eapply (rzb_emit1 (mkCfg ms model)
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
- apply (node_exit segs scfg ms model x8); assumption.
- apply (RomBase.sys_rob_exit segs ms model x8); [exact Hsvc|].
destruct Hx8 as [E | E]; [left | right]; exact E.
- exact (nalloc_ok_exit ms model x8 Hsvc Hx8).
- apply rzb_halt. cbn. discriminate.
Qed.
End WithSegs.
Section Sound.
Variable segs : list Segment.
Lemma rzb_sstep_lift : forall c e st,
sstep segs c e st -> sstep_cfg segs may_fail_cfg c e st.
Proof. intros c e st H. exact (proj1 (sstep_cfg_may_fail segs c e st) H). Qed.
Lemma star_cases : forall c tr c', star segs c tr c' ->
c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
- left. reflexivity.
- right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.
Lemma node_not_refused : forall c I evs nx,
node_ok segs may_fail_cfg c I evs nx -> nalloc_ok c -> ~ budget_refused_at segs c.
Proof.
intros [ms model] I evs nx [_ Hc] Hb [Hh Hr].
assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
{ intros Hs.
destruct (Hc [] SError (rzb_sstep_lift _ [] SError Hs)) as (i & _ & Hbad).
discriminate Hbad. }
cbn [cfg_ms cfg_model] in Hh, Hr.
destruct Hr as [(Hsvc & [ (report & Hstep & Hmat)
| (Hacct & fn & n & eff0 & model0 & evs0 & Hfn & Hsys & Hspec0 & Hret0 & Hh0 & Hmat0) ])
| (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
- exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
- exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff0 model0 evs0
Hh Hsvc Hacct Hfn Hsys Hspec0 Hret0 Hh0 Hmat0)).
- rewrite (alloc_budget_refused_b_outside (sys_input segs ms x8) model (Hb x8 Hx8)) in Hgr.
discriminate Hgr.
- exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.
Lemma rzb_star_not_refused : forall c T, rzb segs may_fail_cfg c T ->
forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq];
intros tr c' Hstar.
- destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
+ exact (node_not_refused c I evs nx Hnode Hb).
+ destruct (proj2 Hnode e (SNext c2) (rzb_sstep_lift c e (SNext c2) Hss))
as (i & _ & Heq2).
injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
- destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
+ intros [Hn _]. exact (Hh Hn).
+ exfalso. exact (Hh (sstep_halted_none segs may_fail_cfg c e _ (rzb_sstep_lift c e _ Hss))).
- exact (IH tr c' Hstar).
Qed.
Theorem rzb_never_refused : forall c T, rzb segs may_fail_cfg c T -> ~ reaches_budget_refused segs c.
Proof.
intros c T H (tr & c' & Hstar & Hb). exact (rzb_star_not_refused c T H tr c' Hstar Hb).
Qed.
Theorem rzb_never_refused_cfg : forall cfg c T, rzb segs may_fail_cfg c T ->
~ reaches_budget_refused_cfg segs cfg c.
Proof.
intros cfg c T H Hr. exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.
End Sound.
Lemma nalloc_ok_cwrom : forall c r, nalloc_ok c -> nalloc_ok (RomBase.cwrom c r).
Proof. intros c r H. exact H. Qed.
Section RzbWrom.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Hvi : vdso_image segs = None.
Theorem rzb_wrom : forall c T, rzb segs scfg c T ->
forall r, RomBase.rom_ext (ms_rom (cfg_ms c)) r -> rzb segs scfg (RomBase.cwrom c r) T.
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq];
intros r Hr.
- apply (rzb_node segs scfg (RomBase.cwrom c r) I evs (fun i => RomBase.cwrom (nx i) r) T i0).
+ eapply SRomStable.node_wrom; eassumption.
+ eapply SRomStable.sys_rob_wrom; eassumption.
+ apply nalloc_ok_cwrom; exact Hb.
+ intros i. apply IH.
match goal with |- RomBase.rom_ext ?x _ => replace x with (ms_rom (cfg_ms c)) end;
[exact Hr|].
symmetry. eapply SRomStable.node_rom; eassumption.
- apply rzb_halt. exact Hh.
- eapply rzb_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End RzbWrom.
Section RzbAppTail.
Variables segs tail : list Segment.
Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
Hypothesis Hvi : vdso_image segs = None.
Variable scfg : SpuriousCfg.
Theorem rzb_app_tail : forall c T, rzb segs scfg c T -> rzb (segs ++ tail) scfg c T.
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hn Hrob Hb Hc IH | c Hh | c T T' H IH Heq].
- apply (rzb_node (segs ++ tail) scfg c I evs nx T i0).
+ eapply SRomStable.node_ok_app_tail; eassumption.
+ eapply SRomStable.sys_rob_app_tail; eassumption.
+ exact Hb.
+ exact IH.
- apply rzb_halt. exact Hh.
- eapply rzb_conseq; [exact IH | exact Heq].
Qed.
End RzbAppTail.
Theorem rzb_run_segments : forall scfg segs inp (sp mb : word) c T,
vdso_image segs = None ->
rzb segs scfg c T -> rzb (run_segments segs inp sp mb) scfg c T.
Proof.
intros scfg segs inp sp mb c T Hvi H. unfold run_segments.
apply (rzb_app_tail segs _
(fun s Hs => SRomStable.vdso_segments_nx _ _ _ s Hs)
(fun s Hs => SRomStable.vdso_segments_nw _ _ _ s Hs) Hvi).
exact H.
Qed.
Theorem rzb_run_init : forall scfg segs inp (sp mb : word) pc ph brk rnd lim T,
vdso_image segs = None ->
rzb segs scfg (init_config segs pc ph sp brk mb rnd lim inp) T ->
rzb (run_segments segs inp sp mb) scfg
(init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
intros scfg segs inp sp mb pc ph brk rnd lim T Hvi H.
rewrite SRomStable.init_config_run_segments.
apply rzb_run_segments; [exact Hvi|].
apply (rzb_wrom segs scfg Hvi); [exact H|].
rewrite SRomStable.init_config_rom. apply SRomStable.rom_ext_run_segments.
Qed.
