(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: module paths changed to omx-clap-core fuzz_manifest (copied from cgif_file_fuzzer, no other change). *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YA05.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's munmap (errno arm, cut, allocation mark), with bnode_munmap at the munmap node and mmap_spec's named helpers unfolded, as libreac/fuzz_boxreg's BudgetWit/AW/YA05_w.v; the node obligation sys_rob and the new system calls; the budget obligation at the changed nodes). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require BudgetPremise SpuriousCfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p YK15.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK0y YK1b YK00 YK01 YK13 YK04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK08 YK0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK0c YK0e YK0f YK09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YA0c_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import RomBase.
Local Instance asanreflect_fx : YK11.FPState := YK11.fx0.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
(* Theorem Labs, 2026-11: no admitted outcome of brk, mmap or mprotect reads or writes guest
   memory ([syscall_effect_accesses] is empty), proved from the LPS specs by walking their
   [Monad] combinators.  [bnode_grant_noacc] and [bnode_brk_mark] use it for the effect clause
   of [YK18_w.bnode_ok]: at these calls materialization cannot fail. *)
Definition sys_noacc (s : Monad.Sys SyscallEffect) : Prop :=
forall i m eff m' evs, s i m (Ok eff m' evs) -> syscall_effect_accesses eff = [].
Lemma noacc_pure : forall r zs us cs, sys_noacc (Monad.pure (mkEffectU r [] zs us cs [])).
Proof.
intros r zs us cs i m eff m' evs H. unfold Monad.pure in H. cbv beta in H.
injection H as He _ _. rewrite He. reflexivity.
Qed.
Lemma noacc_bind : forall (A : Type) (c : Monad.Sys A) (k : A -> Monad.Sys SyscallEffect),
(forall x, sys_noacc (k x)) -> sys_noacc (Monad.bind c k).
Proof.
intros A c k Hk i m eff m' evs H. unfold Monad.bind in H. cbv beta iota in H.
destruct H as (x & m1 & evs1 & evs2 & _ & H & _). exact (Hk x i m1 eff m' evs2 H).
Qed.
Lemma noacc_alt : forall c1 c2 : Monad.Sys SyscallEffect,
sys_noacc c1 -> sys_noacc c2 -> sys_noacc (Monad.alt c1 c2).
Proof.
intros c1 c2 H1 H2 i m eff m' evs H. unfold Monad.alt in H. cbv beta in H.
destruct H as [H | H]; [exact (H1 i m eff m' evs H) | exact (H2 i m eff m' evs H)].
Qed.
Lemma noacc_unmodeled : sys_noacc Monad.unmodeled.
Proof. intros i m eff m' evs H. unfold Monad.unmodeled in H. cbv beta in H. discriminate H. Qed.
Lemma noacc_ret_only : forall r, sys_noacc (Syscall.ret_only r).
Proof. intros r. unfold Syscall.ret_only. apply noacc_pure. Qed.
Lemma noacc_err_ret : forall e, sys_noacc (Syscall.err_ret e).
Proof. intros e. unfold Syscall.err_ret. apply noacc_ret_only. Qed.
(* 727298f3: [mmap_spec] calls named helpers; a head constant the cases below do not take apart is
   unfolded. *)
Ltac noacc_head t := lazymatch t with ?f _ => noacc_head f | _ => t end.
Ltac noacc_tac :=
repeat (cbv beta zeta;
first
[ match goal with |- sys_noacc (match ?x with _ => _ end) => destruct x end
| apply noacc_unmodeled
| apply noacc_err_ret
| apply noacc_ret_only
| apply noacc_alt
| (apply noacc_bind; intro)
| apply noacc_pure
| match goal with |- sys_noacc ?s => let f := noacc_head s in progress unfold f end ]).
Lemma alloc_spec_noacc : forall i m eff m' evs,
In (bv_unsigned (in_sysno i)) [214; 222; 226]%Z ->
syscall_spec i m (Ok eff m' evs) -> syscall_effect_accesses eff = [].
Proof.
intros i m eff m' evs Hno Hs. destruct Hno as [E | [E | [E | []]]].
- apply (proj1 (BudgetPremise.brk_dispatch i m _ (eq_sym E))) in Hs.
enough (Hn : sys_noacc (brk_spec (in_arg i 0))) by exact (Hn i m eff m' evs Hs).
unfold brk_spec. noacc_tac.
- apply (proj1 (SpuriousCfg.mmap_dispatch i m _ (eq_sym E))) in Hs.
enough (Hn : sys_noacc (mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4)
(in_arg i 5))) by exact (Hn i m eff m' evs Hs).
unfold mmap_spec. noacc_tac.
- apply (proj1 (BudgetPremise.mprotect_dispatch i m _ (eq_sym E))) in Hs.
enough (Hn : sys_noacc (mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))) by exact (Hn i m eff m' evs Hs).
unfold mprotect_spec. noacc_tac.
Qed.
Lemma in214 : forall x8 : word, bv_unsigned x8 = 214%Z -> In (bv_unsigned x8) [214; 222; 226]%Z.
Proof. intros x8 E. rewrite E. left. reflexivity. Qed.
Lemma in222 : forall x8 : word, bv_unsigned x8 = 222%Z -> In (bv_unsigned x8) [214; 222; 226]%Z.
Proof. intros x8 E. rewrite E. right. left. reflexivity. Qed.
Lemma in226 : forall x8 : word, bv_unsigned x8 = 226%Z -> In (bv_unsigned x8) [214; 222; 226]%Z.
Proof. intros x8 E. rewrite E. right. right. left. reflexivity. Qed.
Section f.
Variable segs : list Segment.
Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, syscall_effect_accesses (effs i) = []) ->
(forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
sys_rob segs (mkCfg ms model) ->
node_ok segs (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hacc Hns Hrob. split; [| split; [| exact Hrob]].
- intros i. apply (sstep_cfg_syscall segs ACFG ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
+ apply check_syscall_ok_iff. apply Hok.
+ apply Hns.
+ apply Hh'.
+ rewrite (Hacc i). apply materialize_model_accesses_nil.
- intros e st Hss.
destruct (sstep_svc_inv segs ms model x8 e st Hsvc (sstep_of_cfg segs ACFG _ _ _ Hss))
as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
| (eff & Hc & -> & ->)].
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
rewrite (Hacc i), materialize_model_accesses_nil in Hmat.
injection Hmat as <-. exists i. split; reflexivity.
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
rewrite (Hacc i), materialize_model_accesses_nil in Hmat. discriminate.
+ destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
+ exfalso. exact (Hnu eff Hc).
Qed.
Lemma node_chk_cfg_noacc : forall ms model x8 (I : Type) (i0 : I)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, syscall_effect_accesses (effs i) = []) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
(exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
\/ (spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
(forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
sys_rob segs (mkCfg ms model) ->
node_ok segs (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I i0 effs ms' evs Hh Hsvc Hok Hh' Hacc Hinv Hns Hrob. split; [| split; [| exact Hrob]].
- intros i. apply (sstep_cfg_syscall segs ACFG ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
+ apply check_syscall_ok_iff. apply Hok.
+ apply Hns.
+ apply Hh'.
+ rewrite (Hacc i). apply materialize_model_accesses_nil.
- intros e st Hss. inversion Hss; subst; try congruence.
+
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H4 : ~ spurious_refusal_cfg _ _ _ _,
H5 : materialize_model_accesses ?model' _ = Some ?model'' |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply check_syscall_ok_iff in H3;
destruct (Hinv eff model' evs0 H3) as [(i & -> & -> & ->) | [Hsp _]]; [| exfalso; exact (H4 Hsp)];
rewrite (Hacc i), materialize_model_accesses_nil in H5;
injection H5 as <-;
exists i; split; reflexivity
end.
+
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H4 : ~ spurious_refusal_cfg _ _ _ _,
H5 : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply check_syscall_ok_iff in H3;
destruct (Hinv eff model' evs0 H3) as [(i & -> & -> & _) | [Hsp _]]; [| exact (H4 Hsp)];
rewrite (Hacc i), materialize_model_accesses_nil in H5; discriminate
end.
+
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply check_syscall_ok_iff in H3;
destruct (Hinv eff model' evs0 H3) as [(i & _ & Hm & _) | [_ Hm]];
[rewrite Hm, (Hh' i) in H6 | rewrite Hm in H6]; discriminate
end.
+
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply check_syscall_ok_iff in H3;
destruct (Hinv eff model' evs0 H3) as [(i & _ & Hm & _) | [_ Hm]];
[rewrite Hm, (m_killed_of_m_halted_none _ (Hh' i)) in H6 | rewrite (m_killed_of_m_halted_none _ Hm) in H6]; discriminate
end.
+
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply (check_syscall_complete_unmodeled _ _ (effs i0)) in H3;
rewrite (Hok i0) in H3; discriminate
end.
Qed.
Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, syscall_effect_accesses (effs i) = []) ->
(forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i)) ->
sys_rob segs (mkCfg ms model) ->
node_ok segs (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hacc Hns Hrob.
apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.
Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall eff m' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
(eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
m_halted m0 = None ->
syscall_effect_accesses eff0 = [] ->
sys_rob segs (mkCfg ms model) ->
node_ok segs (mkCfg ms model) unit (fun _ => evs0)
(fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hacc Hrob.
apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
- intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
- intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
- exact Hnu.
- intros []; exact Hh0.
- intros []; exact Hacc.
- intros []. apply nonspurious_of_unique. intros eff m' ev Hs.
apply check_syscall_ok_iff in Hs. apply Hchk in Hs as (-> & _ & _). reflexivity.
- exact Hrob.
Qed.
Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall eff m' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
(eff = eff0 /\ m' = m0 /\ evs = [])) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
m_halted m0 = None ->
syscall_effect_accesses eff0 = [] ->
sys_rob segs (mkCfg ms model) ->
bnode_ok segs (mkCfg ms model) ->
srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
srealizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hacc Hrob Hb Hc.
eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hb | exact Hc].
Qed.
Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I (fun _ => []) nx ->
bnode_ok segs c ->
(forall i, srealizes segs (nx i) (T i)) ->
srealizes segs c (t_alt T).
Proof.
intros c I nx T i0 Hnode Hb Hc.
apply (srz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
- apply (srz_node segs c I (fun _ => []) nx T i0 Hnode Hb Hc).
- intros tr. split.
+ intros [i Hi]. exists i.
exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
+ intros [i Hi]. exists i.
exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.
(* Theorem Labs, 2026-11: the budget obligation at an allocation node whose walk admits an
   outcome that is not a refusal (the mark is then false, LPS [Checks.BudgetPremise]); the
   effect clause holds because [alloc_spec_noacc] leaves nothing to materialize. *)
Lemma bnode_grant_noacc : forall ms model x8 eff model' evs,
ms_svc_pending ms = Some x8 -> In (bv_unsigned x8) [214; 222; 226]%Z ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
bnode_ok segs (mkCfg ms model).
Proof.
intros ms model x8 eff model' evs Hsvc Hin Hs Hnr.
apply (bnode_of_grant_outcome segs ms model x8 eff model' evs Hsvc Hin Hs Hnr).
intros eff1 model1 evs1 Hs1 _ Hm1. exfalso.
rewrite (alloc_spec_noacc (sys_input segs ms x8) model eff1 model1 evs1 Hin Hs1),
materialize_model_accesses_nil in Hm1. discriminate Hm1.
Qed.
(* Theorem Labs, 2026-11: the budget obligation at a brk node where brk's own budget mark is
   false, whatever the admitted outcomes are (the query, and a grow blocked off the budget). *)
Lemma bnode_brk_mark : forall ms model x8,
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
Mmap.brk_budget_refused_b model (ms_gpr ms 0) = false ->
bnode_ok segs (mkCfg ms model).
Proof.
intros ms model x8 Hsvc Hno Hm. split.
- intros y8 Hy. cbn [cfg_ms cfg_model] in Hy |- *. rewrite Hsvc in Hy. injection Hy as <-.
unfold alloc_budget_refused_b. cbv zeta.
change (in_sysno (sys_input segs ms x8)) with x8. rewrite Hno. exact Hm.
- apply err_filtered_of_effects. intros y8 eff1 model1 evs1 Hy Hs1 _ Hm1. exfalso.
rewrite Hsvc in Hy. injection Hy as <-.
rewrite (alloc_spec_noacc (sys_input segs ms x8) model eff1 model1 evs1 (in214 x8 Hno) Hs1),
materialize_model_accesses_nil in Hm1. discriminate Hm1.
Qed.
(* Theorem Labs, 2026-11: the budget obligation at a munmap node.  At LPS 727298f3 munmap (215)
   is one of [Run.alloc_mark_sysnos], so [bnode_no] no longer applies; its mark is the constant
   [false] ([Run.alloc_budget_refused_munmap]), and no admitted outcome of [munmap_spec] has an
   access to materialize. *)
Lemma bnode_munmap : forall ms model x8,
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215%Z ->
bnode_ok segs (mkCfg ms model).
Proof.
intros ms model x8 Hsvc Hno. split.
- intros y8 Hy. cbn [cfg_ms cfg_model] in Hy |- *. rewrite Hsvc in Hy. injection Hy as <-.
apply alloc_budget_refused_munmap. exact Hno.
- apply err_filtered_of_effects. intros y8 eff1 model1 evs1 Hy Hs1 _ Hm1. exfalso.
rewrite Hsvc in Hy. injection Hy as <-.
apply (proj1 (SpuriousCfg.munmap_dispatch (sys_input segs ms x8) model _ Hno)) in Hs1.
assert (Hn : sys_noacc (Mmap.munmap_spec (in_arg (sys_input segs ms x8) 0) (in_arg (sys_input segs ms x8) 1)))
by (unfold Mmap.munmap_spec; noacc_tac).
rewrite (Hn _ _ eff1 model1 evs1 Hs1), materialize_model_accesses_nil in Hm1. discriminate Hm1.
Qed.
Lemma forget_vm_ranges_halted : forall ranges m,
m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.
Lemma brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
intros. unfold brk_model, with_brk_next. cbv zeta.
rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
fetch_word segs pc = Some w -> is_ecall w = true ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
= MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
intros regs pc mem rom w Hfetch Hecall.
unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
rewrite Hfetch. cbv beta iota.
unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
reflexivity.
Qed.
Lemma node_instr_noacc : forall ms model ms',
m_halted model = None ->
ms_svc_pending ms = None ->
RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
intros ms model ms' Hh Hsvc Hstep.
assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
{ unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
rewrite materialize_model_accesses_nil. reflexivity. }
apply node_ok_of_pnode; [apply transparent_instr; exact Hsvc | apply sys_rob_instr; exact Hsvc |]. split.
- intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
- intros e st Hss. exists tt.
inversion Hss; subst;
match goal with
| H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
| H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
end.
Qed.
Lemma srz_sys_lazy : forall regs pc mem rom model w T,
m_halted model = None ->
fetch_word segs pc = Some w -> is_ecall w = true ->
srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model w T Hh HF HE Hc.
eapply srz_silent1; [| apply bnode_none; reflexivity | exact Hc].
apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.
Lemma srz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 215 ->
getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
(munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
{ unfold page_round_up. rewrite Hu1. reflexivity. }
assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hargs : munmap_args_ok ms model).
{ unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
(* The node proof excludes refused outcomes using the allocator policy. *)
eapply srz_silent1.
- eapply node_munmap_cfg.
  + exact Hh.
  + reflexivity.
  + exact Hno.
  + exact Hargs.
  + cbn [munmap_eff syscall_effect_accesses].
    apply materialize_model_accesses_nil.
- exact (bnode_munmap ms model (getr regs 17) eq_refl Hno).
- unfold munmap_eff. rewrite H0, Hpr.
  unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.
Definition brk_eff_lazy (ms : machine_state) (model : Model) (r : word) : SyscallEffect :=
mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [].
Definition brk_J_lazy (ms : machine_state) (x8 : word) (model : Model) : Type :=
{r : word | brk_resolution_ok model (ms_gpr ms 0) r /\
~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (brk_eff_lazy ms model r)}.
Lemma brk_resolution_ok_keep_lazy : forall model req,
brk_resolution_ok model req (vm_brk (m_vmmaps model)).
Proof.
intros model req. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (min_brk (m_vmmaps model))))%bool.
- apply bv_eqb_refl.
- destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps model)))).
+ rewrite bv_eqb_refl, orb_true_r. reflexivity.
+ rewrite bv_eqb_refl, orb_true_r, andb_true_l.
unfold Mmap.brk_grow_ok. now rewrite Z.ltb_irrefl, andb_false_r.
Qed.
Lemma brk_J_lazy_inh : forall ms model x8,
bv_unsigned x8 = 214%Z -> inhabited (brk_J_lazy ms x8 model).
Proof.
intros ms model x8 Hno.
destruct (exists_nonspurious ACFG (sys_input segs ms x8) model _ _ _
(brk_ok_intro segs ms x8 model _ Hno (brk_resolution_ok_keep_lazy model (ms_gpr ms 0))))
as (eff & m' & evs & Hs & Hns).
apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hs. destruct Hs as (Heff & _ & Hr & _).
constructor. exists (eff_ret eff). split; [exact Hr|]. unfold brk_eff_lazy. rewrite <- Heff. exact Hns.
Qed.
Lemma node_brk_lazy : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
node_ok segs (mkCfg ms model) (brk_J_lazy ms x8 model)
(fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (brk_eff_lazy ms model (proj1_sig i))))
(brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
intros ms model x8 Hh Hsvc Hno.
destruct (brk_J_lazy_inh ms model x8 Hno) as [i0].
apply (node_chk_cfg_noacc ms model x8 (brk_J_lazy ms x8 model) i0
(fun i => brk_eff_lazy ms model (proj1_sig i))
(fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) (fun _ => []) Hh Hsvc).
- intros [r [Hr Hns]]. cbn [proj1_sig]. apply check_syscall_ok_iff.
exact (brk_ok_intro segs ms x8 model r Hno Hr).
- intros [r Hr]. cbn [proj1_sig]. rewrite brk_model_halted. exact Hh.
- intros [r Hr]. reflexivity.
- intros eff m' evs Hc. apply check_syscall_ok_iff in Hc.
apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & Hok & ->).
destruct (classic (spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff)) as [Hsp | Hns].
+ right. split; [exact Hsp | rewrite brk_model_halted; exact Hh].
+ left.
assert (Hns' : ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (brk_eff_lazy ms model (eff_ret eff)))
by (unfold brk_eff_lazy; rewrite <- Heff; exact Hns).
exists (exist _ (eff_ret eff) (conj Hok Hns')). cbn [proj1_sig]. unfold brk_eff_lazy. rewrite <- Heff.
repeat split; reflexivity.
- intros [r [Hr Hns]]. exact Hns.
- exact (sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact memfree_214)).
Qed.
Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 214 ->
getr regs 10 = Z_to_bv 64 0 ->
srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
{ intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
destruct (brk_J_lazy_inh ms model (getr regs 17) Hno) as [i0].
apply (srz_conseq segs _ (t_alt (fun _ : brk_J_lazy ms (getr regs 17) model => K)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists i0; exact Ht]].
eapply srz_cases; [exact i0 | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno]
| apply (bnode_brk_mark ms model (getr regs 17) eq_refl Hno);
unfold Mmap.brk_budget_refused_b; rewrite H0; reflexivity |].
intros [r [Hr Hns]]. cbn [proj1_sig]. unfold brk_eff_lazy.
pose proof (proj1 (Hcases r) Hr) as Er. subst r.
rewrite H0, brk_zeros_query, brk_unmaps_keep.
rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.
Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 214 ->
let h := m_vmmaps model in
let b := vm_brk h in
(bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
(0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
(bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
(zfill b (Z_to_bv 64 d) mem) rom)
(with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h)
(Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
pose proof (u64_range b) as Hbr.
set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
{ intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
assert (Hneq : req <> b).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
assert (Hne : bv_eqb req (vm_brk (m_vmmaps model)) = false) by (apply bv_eqb_neq; exact Hneq).
assert (Harg : in_arg (sys_input segs ms (getr regs 17)) 0 = req) by exact H0.
assert (Hgnr : refusal_b (sys_input segs ms (getr regs 17)) model (eff_ret (brk_eff_lazy ms model req)) = false).
{ unfold brk_eff_lazy. cbn [eff_ret].
rewrite (refusal_b_214 (sys_input segs ms (getr regs 17)) model _ Hno), Harg. unfold brk_refusal_b. rewrite Hne. rewrite !andb_false_r. reflexivity. }
assert (Hgns : ~ spurious_refusal_cfg ACFG (sys_input segs ms (getr regs 17)) model (brk_eff_lazy ms model req))
by (apply spurious_refusal_not_refusal; exact Hgnr).
pose (ig := exist (fun r => brk_resolution_ok model (ms_gpr ms 0) r /\
~ spurious_refusal_cfg ACFG (sys_input segs ms (getr regs 17)) model (brk_eff_lazy ms model r))
req (conj Hgrow Hgns) : brk_J_lazy ms (getr regs 17) model).
apply (srz_conseq segs _ (t_alt (fun _ : brk_J_lazy ms (getr regs 17) model => KB)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists ig; exact Ht]].
eapply srz_cases; [exact ig | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno]
| exact (bnode_grant_noacc ms model (getr regs 17) _ _ _ eq_refl (in214 _ Hno)
(brk_ok_intro segs ms (getr regs 17) model req Hno Hgrow) Hgnr) |].
intros [r [Hr Hns]]. cbn [proj1_sig]. unfold brk_eff_lazy. fold h.
destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
- exfalso. apply Hns.
assert (Hreq0' : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
apply (refusal_spurious_of_grant ACFG _ model _ (brk_eff_lazy ms model req) (brk_model (ms_gpr ms 0) req model) []).
+ apply acfg_family_off_214. exact Hno.
+ unfold brk_eff_lazy. cbn [eff_ret]. rewrite (refusal_b_214 (sys_input segs ms (getr regs 17)) model _ Hno), Harg.
unfold brk_refusal_b, min_brk. rewrite Hne. rewrite !andb_true_iff. repeat split.
* apply negb_true_iff. unfold w_is0. apply bv_eqb_neq. exact Hreq0'.
* apply negb_true_iff. apply Z.ltb_ge. rewrite Hureq. exact Hs.
* apply bv_eqb_refl.
+ exact (brk_ok_intro segs ms (getr regs 17) model req Hno Hgrow).
+ exact Hgnr.
- assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
assert (Hreq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
unfold brk_page_range.
rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned req))
by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _) Hlt).
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.
Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 214 ->
let h := m_vmmaps model in
let b := vm_brk h in
getr regs 10 = req ->
(0 < bv_unsigned req)%Z ->
(bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
(bv_unsigned b <= bv_unsigned req)%Z ->
Mmap.brk_grow_ok model req req = false ->
Mmap.brk_budget_ok model req = true ->
srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk Hbud HA.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
{ intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
- intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
- intros ->. left. reflexivity. }
destruct (brk_J_lazy_inh ms model (getr regs 17) Hno) as [i0].
apply (srz_conseq segs _ (t_alt (fun _ : brk_J_lazy ms (getr regs 17) model => KA)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists i0; exact Ht]].
(* Theorem Labs, 2026-11: a blocked grow is not a budget refusal only when the budget would
   admit it ([Hbud]); every admitted outcome here is the refusal r = b. *)
eapply srz_cases; [exact i0 | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno]
| apply (bnode_brk_mark ms model (getr regs 17) eq_refl Hno);
unfold Mmap.brk_budget_refused_b; cbv zeta; rewrite H0, Hbud; cbn [negb]; apply andb_false_r |].
intros [r [Hr Hns]]. cbn [proj1_sig]. unfold brk_eff_lazy. fold h.
pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
unfold ms. rewrite adv_ret_epend. exact HA.
Qed.
Lemma node_set_tid_lazy : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
m_tid model = None ->
node_ok segs (mkCfg ms model) tid_I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
(with_tid (proj1_sig i) model)).
Proof.
intros ms model x8 Hh Hsvc Hno Htid.
assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
match eff with
| mkEffectU ret [] [] [] [] [] =>
if ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool
then CheckOk (with_tid ret model) [] else CheckReject
| _ => CheckReject end).
{ intros eff. rewrite (check_syscall_96 segs ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
apply (node_chk_noacc ms model x8 tid_I
(fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
(fun i => with_tid (proj1_sig i) model) Hh Hsvc).
- intros [t [Ht1 Ht2]]. cbn [proj1_sig]. rewrite Hchk.
rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
- intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool eqn:Eb; [|discriminate].
apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
- intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool; discriminate.
- intros [t Ht]. cbn [proj1_sig]. rewrite with_tid_halted. exact Hh.
- intros [t Ht]. reflexivity.
- exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- exact (sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact memfree_96)).
Qed.
Lemma srz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
srealizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
| eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid]
| apply (bnode_no segs _ model (getr regs 17) 96%Z); [reflexivity | rewrite H17; apply u64_lit; lia | reflexivity] |].
intros [t Ht]. cbn [proj1_sig].
change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.
Lemma srz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
(getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
getr regs 10 = code ->
srealizes segs (mkCfg (mkst regs pc mem rom) model)
(t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs pc mem rom model w code HF HE Hh H17 H10.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply srz_exit; [exact Hh | reflexivity |].
destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.
Lemma mmap_gates_core50 : forall flags prot,
mmap_flags_core flags = 50%Z ->
mmap_modeled_b prot flags (Z_to_bv 64 0) = false
/\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
/\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
/\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
/\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
rewrite Hc. repeat split; try (vm_compute; reflexivity).
all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.
Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
if Z.eqb prot 0
then mkVmMapsFull (vm_reserved h) (vm_maps h)
((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
else mmap_fixed_rw_next h addr n.
Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
mkVmMapsFull (vm_reserved h)
(maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.
Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].
Lemma with_mmap_replacement_halted' : forall flags a n m,
m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
destruct (mmap_noreserve_b flags); reflexivity.
Qed.
Lemma with_mmap_destroyed_halted' : forall a n h m,
m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros. reflexivity. Qed.
Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
bv_unsigned x8 = 222%Z ->
(prot = 0 \/ prot = 3)%Z ->
mmap_flags_core flags = 50%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs us [] [] =>
if errno_ret_in mmap_errnos r
then match zs with
| [] => match us with
| [] => CheckOk model []
| _ => if listNN_eqb us [(addr, n)]
then CheckOk (fixedin_destroyed_model addr n model) []
else CheckReject
end
| _ => CheckReject
end
else if (Z.eqb prot 0)
then match zs with
| [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (fixedin_ok_model prot flags addr n model) []
else CheckReject
| _ => CheckReject
end
else match us with
| [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
then CheckOk (fixedin_ok_model prot flags addr n model) []
else CheckReject
| _ => CheckReject
end
| _ => CheckReject
end.
Proof.
intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Hce n Hrf Hmc Hbud.
pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv.
assert (Hlen' : (len < 2 ^ 64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap, check_mmap_fixed_overflow.
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
rewrite E1, H2, H3, H5, H0, Hu1.
destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
pose proof (u64_range addr) as Har.
destruct Hprot as [-> | ->].
-
rewrite G3. cbv beta iota zeta.
rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
rewrite (proj2 (Z.leb_le _ _) Hce). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct (errno_ret_in mmap_errnos r); destruct zs; destruct us; destruct cs; destruct ci; reflexivity.
-
rewrite G4, G5. cbv beta iota zeta.
rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
rewrite (proj2 (Z.leb_le _ _) Hce). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct (errno_ret_in mmap_errnos r).
+ destruct zs; destruct us; destruct cs; destruct ci; reflexivity.
+ destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
destruct us; [|reflexivity]. rewrite (Hbud eq_refl), andb_true_r. reflexivity.
Qed.
Lemma node_mmap_fixedin : forall ms x8 model (prot : Z) (flags addr : word) (len : Z),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
(prot = 0 \/ prot = 3)%Z ->
mmap_flags_core flags = 50%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
node_ok segs (mkCfg ms model) unit (fun _ => [])
(fun _ => mkCfg (advance_past_svc (apply_effect ms (fixedin_ok_eff prot addr n)))
(fixedin_ok_model prot flags addr n model)).
Proof.
intros ms x8 model prot flags addr len Hh Hsvc Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Hce n Hrf Hmc Hbud.
pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv.
pose proof (fun eff => mmap_fixedin_check ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen
H2 H3 H4 H5 Hce Hrf Hmc Hbud) as Hchk.
cbv zeta in Hchk. fold n in Hchk.
assert (Hnot : errno_ret_in mmap_errnos addr = false).
{ apply errno_ret_in_below; [reflexivity|].
pose proof (page_round_up_Z_nonneg len ltac:(lia)). unfold two_pow_64. lia. }
assert (Hrb : forall r, refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r).
{ intros r. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno). reflexivity. }
assert (Hsucc : check_syscall (sys_input segs ms x8) (fixedin_ok_eff prot addr n) model
= CheckOk (fixedin_ok_model prot flags addr n model) []).
{ unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep;
rewrite Hchk, Hnot, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity. }
assert (Hret : eff_ret (fixedin_ok_eff prot addr n) = addr).
{ unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity. }
apply (node_chk_cfg_noacc ms model x8 unit tt (fun _ => fixedin_ok_eff prot addr n)
(fun _ => fixedin_ok_model prot flags addr n model) (fun _ => []) Hh Hsvc).
- intros []. exact Hsucc.
- intros []. unfold fixedin_ok_model. rewrite with_mmap_replacement_halted', with_vmmaps_halted. exact Hh.
- intros []. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
- intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Her.
+ right. split.
* apply (refusal_spurious_of_grant ACFG _ model _ (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) []).
-- apply acfg_family_off_222. exact Hno.
-- cbn [eff_ret]. rewrite Hrb. exact Her.
-- apply check_syscall_ok_iff. exact Hsucc.
-- rewrite Hret, Hrb. exact Hnot.
* destruct zs; [|discriminate]. destruct us as [|u us]; [injection Hc as <- <-; exact Hh|].
destruct (listNN_eqb (u :: us) [(addr, n)]); [|discriminate].
injection Hc as <- <-. unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. exact Hh.
+ left. destruct (Z.eqb prot 0) eqn:Ep.
* destruct zs; [|discriminate].
destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
exists tt. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
* destruct us; [|discriminate].
destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
exists tt. unfold fixedin_ok_eff. rewrite Ep. repeat split; reflexivity.
- intros []. apply spurious_refusal_not_refusal. rewrite Hret, Hrb. exact Hnot.
- exact (sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact memfree_222)).
Qed.
(* Theorem Labs, 2026-11: the budget obligation at [node_mmap_fixedin]'s node, from the
   node's own grant outcome [fixedin_ok_eff], which is not a refusal. *)
Lemma bnode_mmap_fixedin : forall ms x8 model (prot : Z) (flags addr : word) (len : Z),
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
(prot = 0 \/ prot = 3)%Z ->
mmap_flags_core flags = 50%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
bnode_ok segs (mkCfg ms model).
Proof.
intros ms x8 model prot flags addr len Hsvc Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Hce n Hrf Hmc Hbud.
pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv.
pose proof (fun eff => mmap_fixedin_check ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen
H2 H3 H4 H5 Hce Hrf Hmc Hbud) as Hchk.
cbv zeta in Hchk. fold n in Hchk.
assert (Hnot : errno_ret_in mmap_errnos addr = false).
{ apply errno_ret_in_below; [reflexivity|].
pose proof (page_round_up_Z_nonneg len ltac:(lia)). unfold two_pow_64. lia. }
assert (Hrb : forall r, refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r).
{ intros r. rewrite (refusal_b_222 (sys_input segs ms x8) model _ Hno). reflexivity. }
assert (Hsucc : check_syscall (sys_input segs ms x8) (fixedin_ok_eff prot addr n) model
= CheckOk (fixedin_ok_model prot flags addr n model) []).
{ unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep;
rewrite Hchk, Hnot, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity. }
assert (Hret : eff_ret (fixedin_ok_eff prot addr n) = addr).
{ unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity. }
apply (bnode_grant_noacc ms model x8 (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) []
Hsvc (in222 x8 Hno)).
- apply check_syscall_ok_iff. exact Hsucc.
- rewrite Hret, Hrb. exact Hnot.
Qed.
Lemma srz_mmap_fixedin_ok : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 222 ->
(prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
(if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
(fixedin_ok_model prot flags addr n model)) KB ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 n Hrf Hmc Hbud HB.
pose proof (alloc_top_room (m_vmmaps model)) as Hcv. unfold stack_max_size, two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
pose (effs := fun i : unit => fixedin_ok_eff prot addr n).
pose (ms' := fun i : unit => fixedin_ok_model prot flags addr n model).
apply (srz_conseq segs _ (t_alt (fun i : unit => t_emit [] KB))).
2: { eapply t_eq_trans; [ apply (t_alt_unit (fun _ : unit => t_emit [] KB)) | apply t_emit_nil_eq; eapply srealizes_nonempty; exact HB ]. }
apply (srz_node segs (mkCfg ms model) unit (fun _ => []) (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))
(fun _ => KB) tt).
- exact (node_mmap_fixedin ms (getr regs 17) model prot flags addr len Hh eq_refl Hno Hprot Hcore
ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
Hce Hrf Hmc Hbud).
- exact (bnode_mmap_fixedin ms (getr regs 17) model prot flags addr len eq_refl Hno Hprot Hcore
ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
Hce Hrf Hmc Hbud).
- intros []. cbv beta iota delta [effs ms']. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
+ rewrite adv_unmaps1_epend. exact HB.
+ rewrite adv_zeros1_epend. exact HB.
Qed.
End f.
Open Scope Z_scope.
Import AX2 AX2S APG APSG.
Lemma is_ecall_at_sound : forall SEGS cs,
is_ecall_at SEGS cs = true ->
0 <= pc cs /\ pc cs + 4 < two64 /\
exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true.
Proof.
intros SEGS cs H. unfold is_ecall_at in H.
apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
apply Z.leb_le in H0. apply Z.ltb_lt in H4.
destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
repeat split; try assumption. exists w. auto.
Qed.
Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
symmetry. apply u64_lit. unfold two64 in *.
pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.
Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.
Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < two64 ->
v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.
