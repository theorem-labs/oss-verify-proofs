(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import BudgetBridgeCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac headc t := lazymatch t with ?f _ => headc f | _ => t end.
Ltac innermost e :=
lazymatch e with
| (match ?x with _ => _ end) => innermost x
| _ => e
end.
Ltac disc_tac := fail.
Ltac pair_destruct l r :=
match r with
| context [match ?e2 with _ => _ end] =>
let x2 := innermost e2 in
match l with
| context [match ?e1 with _ => _ end] =>
let x1 := innermost e1 in
(tryif constr_eq x1 x2 then idtac
else (let E := fresh "E" in
assert (E : x1 = x2) by (first [ disc_tac | reflexivity ]);
rewrite E; clear E));
destruct x2 eqn:?
end
end.
Create Rewrite HintDb bb_lim_comm.
Ltac comm_tac :=
cbv beta iota zeta;
first
[ reflexivity
| progress (autorewrite with bb_lim_comm); comm_tac
| lazymatch goal with
| |- ?l = ?r => pair_destruct l r; comm_tac
end
| lazymatch goal with
| |- ?l = setlim _ ?r =>
let h := headc r in
progress (unfold h); comm_tac
end ].
Create HintDb bb_simdb.
Ltac sim_step :=
lazymatch goal with
| |- Sim _ _ (bind _ _) (bind _ _) =>
eapply sim_bind; [ | intros ?x; cbv beta ]
| |- Sim _ _ get_model get_model => apply sim_get
| |- Sim _ ?F (pure _) (pure _) =>
tryif is_evar F then (apply (sim_pure _ (fun x => x)); reflexivity)
else (apply sim_pure; reflexivity)
| |- Sim _ _ (modify _) (modify _) => apply sim_modify; intros ?m; comm_tac
| |- Sim _ _ (choose _) (choose _) => apply sim_choose; intros ?x; reflexivity
| |- Sim _ _ (alt _ _) (alt _ _) => apply sim_alt
| |- Sim _ _ unmodeled unmodeled => apply sim_unmodeled
| |- Sim _ _ (emit _) (emit _) => apply sim_emit; reflexivity
| |- Sim _ _ input input => apply sim_input
| |- Sim _ _ sysno sysno => apply sim_sysno
| |- Sim _ _ (arg _) (arg _) => apply sim_arg
| |- Sim _ _ get_fds get_fds => apply sim_get_fds
| |- Sim _ _ get_vmmaps get_vmmaps => apply sim_get_vmmaps
| |- Sim _ _ (let _ := _ in _) _ => cbv zeta
| |- Sim _ _ _ (let _ := _ in _) => cbv zeta
| |- Sim _ _ ?X ?Y =>
lazymatch Y with
| (match _ with _ => _ end) => pair_destruct X Y; cbv beta iota zeta
| _ => first [ solve [ eauto with bb_simdb ]
| let h := headc Y in progress (unfold h); cbv beta ]
end
end.
Ltac sim_auto := repeat sim_step.
Ltac gate_tac := fail.
Ltac sim1_out He :=
lazymatch type of He with
| get_model _ _ _ => cbv [get_model] in He; injection He; intros; subst
| input _ _ _ => cbv [input] in He; injection He; intros; subst
| pure _ _ _ _ => cbv [pure] in He; injection He; intros; subst
| modify _ _ _ _ => cbv [modify] in He; injection He; intros; subst
| choose _ _ _ _ =>
cbv [choose] in He;
let r := fresh "r" in let Hr := fresh "Hr" in
destruct He as (r & Hr & He); injection He; intros; subst
| _ => idtac
end.
Ltac sim1_step :=
lazymatch goal with
| |- Sim1 _ _ (bind _ _) (bind _ _) _ _ =>
eapply sim1_bind;
[ | let x := fresh "x" in let m' := fresh "m'" in let e := fresh "e" in
let He := fresh "He" in intros x m' e He; cbv beta; sim1_out He ]
| |- Sim1 _ _ get_model get_model _ _ => apply sim1_of_sim, sim_get
| |- Sim1 _ _ input input _ _ => apply sim1_of_sim, sim_input
| |- Sim1 _ _ (choose _) (choose _) _ _ =>
apply sim1_choose; intros ?x; cbv beta; first [ gate_tac | reflexivity ]
| |- Sim1 _ _ (alt _ _) (alt _ _) _ _ => apply sim1_alt
| |- Sim1 _ _ (let _ := _ in _) _ _ _ => cbv zeta
| |- Sim1 _ _ _ (let _ := _ in _) _ _ => cbv zeta
| |- Sim1 _ _ ?X ?Y _ _ =>
lazymatch Y with
| (match _ with _ => _ end) => pair_destruct X Y; cbv beta iota zeta in *
| _ => first [ apply sim1_of_sim; solve [ sim_auto ]
| let h := headc Y in progress (unfold h); cbv beta ]
end
end.
Ltac sim1_auto := repeat sim1_step.
