(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YK0x.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YK0x.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed sstep_munmap_inv_lazy, node_munmap_lazy, srz_munmap_lazy; added materialize_syscall_effect_nil). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK16 YK0n YK11 YK0i YK0v YK15 YK0j YK0t YK1g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require YA05_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import RomBase RomWrite.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section d.
Context {fx : FPState}.
Lemma materialize_syscall_effect_nil :
forall (m : Model) (r : word) (zs us : list (word * word)),
materialize_model_accesses m
(syscall_effect_accesses (mkEffectU r [] zs us [] []))
= Some m.
Proof. intros m r zs us. exact (materialize_model_accesses_nil m). Qed.
Lemma materialize_munmap_eff_nil : forall (m : Model) (ms : machine_state),
materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms))
= Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.
Section f.
Variable segs : list Segment.
Lemma sstep_munmap_inv_lazy : forall ms model x8 evs st,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
sstep segs (mkCfg ms model) evs st ->
(* 08b1429: [YK0v.munmap_ok_inv] now answers with the REFUSAL/GRANT disjunction, because the
   spec's munmap may answer -ENOMEM; the raw [sstep] relation this inverts is not ACFG-filtered,
   so the inversion carries both outcomes.  (The ACFG fork that closes the refusal is applied at
   [node_munmap_lazy] below, not here.) *)
evs = [] /\
((exists e, In e munmap_errnos /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (Hevs & Hcase);
subst evs0
end.
split; [reflexivity|].
destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
+ left. exists e.
match goal with
| Hmat : materialize_model_accesses model _ = Some _ |- _ =>
rewrite materialize_syscall_effect_nil in Hmat;
inversion Hmat; subst
end.
split; [assumption |].
rewrite apply_effect_no_write. reflexivity.
+ right.
match goal with
| Hmat : materialize_model_accesses
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
rewrite materialize_munmap_eff_nil in Hmat;
inversion Hmat; subst
end.
reflexivity.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
[ rewrite materialize_syscall_effect_nil in Hmat
| rewrite materialize_munmap_eff_nil in Hmat ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
[ rewrite Hh in H6 | rewrite munmap_model_halted, Hh in H6 ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some _ |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
[ rewrite (m_killed_of_m_halted_none _ Hh) in H6
| rewrite m_killed_of_m_halted_none in H6;
[| rewrite munmap_model_halted; exact Hh] ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
end.
Qed.
Lemma node_munmap_lazy : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
node_ok segs (mkCfg ms model) unit (fun _ => [])
(fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
model)).
Proof.
intros ms model x8 Hh Hsvc Hno Hargs.
(* 08b1429: the ACFG fork filters munmap's refusal, so the node keeps its single
   success child and the index stays [unit] ([YK15.node_munmap_cfg], and this tree's
   own [YK18_w.v:359] applies it the same way). *)
exact (node_munmap_cfg segs ms model x8 _ Hh Hsvc Hno Hargs
(materialize_munmap_eff_nil _ ms)).
Qed.
Lemma srz_munmap_lazy : forall ms model x8 T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
srealizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 T Hh Hsvc Hno Hargs Hc.
eapply srz_silent1; [apply (node_munmap_lazy ms model x8); assumption | exact (YA05_w.bnode_munmap segs ms model x8 Hsvc Hno) | exact Hc].
Qed.
Inductive msteps_acc
: machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
ms_svc_pending ms = None ->
RiscvSemantics.step_accesses segs ms
= MachineOk (@mkAccessReport machine_state ms1 ranges) ->
msteps_acc ms1 ms2 accs ->
msteps_acc ms ms2 (ranges ++ accs).
End f.
End d.
Section g.
Context {fx : FPState}.
End g.
