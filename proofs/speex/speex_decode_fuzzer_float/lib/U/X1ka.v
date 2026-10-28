(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qm X0px X0qn X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation rsegs := Ubsan.M.loaded_segments.

Fixpoint tleaf {R} (t : itree node R) (r : R) : Prop :=
match t with
| X1bs.Ret r' => r' = r
| X1bs.Vis n k => exists rsp, tleaf (k rsp) r
end.

Definition mleaf {A} (c : M PState A) (s : PState) (a : A) (s' : PState) : Prop := tleaf (c s) (Ok (a, s')).

Lemma impl_leaves : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms,
impl rsegs (at_node rsegs) t Q ms -> impl rsegs (at_node rsegs) t (fun r ms' => Q r ms' /\ tleaf t r) ms.
Proof.
induction t as [r|n k IH]; intros Q ms H; cbn in *.
- eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| reflexivity].
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp.
eapply impl_mono; [apply IH; apply Hk|]. intros r ms' [HQ HL]. split; [exact HQ|]. exists rsp. exact HL.
Qed.

Lemma implM_leaves : forall {A} (c : M PState A) s (Q : A -> PState -> machine_state -> Prop) ms,
implM rsegs c s Q ms -> implM rsegs c s (fun a s' ms' => Q a s' ms' /\ mleaf c s a s') ms.
Proof.
intros A c s Q ms H. unfold implM, mleaf in *. eapply impl_mono; [apply impl_leaves; exact H|].
intros [|[a s']] ms' [HQ HL]; cbn in *; [exact HQ|]. split; assumption.
Qed.

Definition rfree_keeps_ptr_stmt {RCEIL : RunCeiling} : Prop :=
forall (s s' : PState) (LB : list block) (m : mem) (p : bptr) (A n : Z) (b : block),
RHEAP s LB m -> In (p, A, n) LB -> mleaf (raw_free p) s tt s' ->
In b (lb_remove p LB) -> ptr_addr s' (blk_id b) = ptr_addr s (blk_id b).

Lemma tleaf_bind {A B} (t : itree node A) (f : A -> itree node B) r :
tleaf (X1bs.bind _ t f) r -> exists x, tleaf t x /\ tleaf (f x) r.
Proof.
induction t as [a|n k IH]; cbn; intros H.
- exists a. split; [reflexivity| exact H].
- destruct H as [rsp H]. destruct (IH rsp H) as (x & Hx & Hf). exists x. split; [exists rsp; exact Hx| exact Hf].
Qed.

Lemma tleaf_ebind {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) r :
tleaf (ebind t f) (Ok r) -> exists a, tleaf t (Ok a) /\ tleaf (f a) (Ok r).
Proof.
unfold ebind. intros H. destruct (tleaf_bind _ _ _ H) as (x & Hx & Hf).
destruct x as [|a]; [cbn in Hf; discriminate Hf|]. exists a. split; assumption.
Qed.

Lemma mleaf_bind {A B} (c : X1qx.M PState A) (f : A -> X1qx.M PState B) s b s' :
mleaf (mbind c f) s b s' -> exists a s1, mleaf c s a s1 /\ mleaf (f a) s1 b s'.
Proof.
unfold mleaf, mbind. intros H. destruct (tleaf_ebind _ _ _ H) as ([a s1] & H1 & H2). exists a, s1. split; assumption.
Qed.

Lemma mleaf_ret {A} (a : A) s b s' : mleaf (mret a) s b s' -> b = a /\ s' = s.
Proof. unfold mleaf, mret. cbn. intros H. inversion H. auto. Qed.

Lemma mleaf_msys {A} n (dec : resp -> option A) s a s' : mleaf (msys n dec) s a s' -> s' = s.
Proof.
unfold mleaf, msys, enode. cbn. intros [rsp H]. destruct (dec rsp); cbn in H; [| discriminate H]. inversion H. reflexivity.
Qed.

Lemma ev_step_leaf ceil e s z s1 : mleaf (ev_step ceil e) s z s1 ->
ps_m s1 = ps_m s /\ match e with EPeek _ _ _ | EUndef _ => False | _ => True end.
Proof.
destruct e as [rq|a len prot flags|a len|a len prot|p c h|w]; cbn [ev_step]; intros H.
- destruct (rq =? 0).
+ apply mleaf_bind in H as (r & s2 & H1 & H2). apply mleaf_msys in H1. subst s2.
apply mleaf_bind in H2 as (u & s3 & H2 & H3). unfold mleaf, mupd in H2. cbn in H2. inversion H2. subst.
apply mleaf_ret in H3 as [_ ->]. split; [reflexivity| exact I].
+ apply mleaf_bind in H as (s0 & s2 & H1 & H2). unfold mleaf, mget in H1. cbn in H1. inversion H1. subst.
apply mleaf_bind in H2 as (aa & s3 & H2 & H3). apply mleaf_msys in H2. subst s3.
destruct aa.
* apply mleaf_bind in H3 as (u & s4 & H3 & H4). unfold mleaf, mupd in H3. cbn in H3. inversion H3. subst.
apply mleaf_ret in H4 as [_ ->]. split; [reflexivity| exact I].
* apply mleaf_ret in H3 as [_ ->]. split; [reflexivity| exact I].
- destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [| destruct (prot =? 0)].
all: apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
- apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
- apply mleaf_bind in H as (aa & s2 & H1 & H2); apply mleaf_msys in H1; subst s2; apply mleaf_ret in H2 as [_ ->]; split; [reflexivity| exact I].
- unfold mleaf, munr in H. cbn in H. discriminate H.
- unfold mleaf, munr in H. cbn in H. discriminate H.
Qed.

Lemma membed_leaf {R} ceil (t : stree ev Z R) : forall s r s',
mleaf (membed ceil t) s r s' -> ps_m s' = ps_m s /\ exists ans, follow t ans = Some r.
Proof.
induction t as [r0|e k IH]; intros s r s' H; cbn [membed] in H.
- apply mleaf_ret in H as [-> ->]. split; [reflexivity|]. exists []. reflexivity.
- apply mleaf_bind in H as (z & s1 & H1 & H2). destruct (ev_step_leaf ceil e s z s1 H1) as [E1 NE].
destruct (IH z s1 r s' H2) as [E2 [ans Hf]]. split; [rewrite E2; exact E1|].
exists (z :: ans). destruct e; try exact Hf; destruct NE.
Qed.

Lemma raw_free_leaf p s s' : mleaf (raw_free p) s tt s' ->
exists ans, follow (cfree (ps_m s) (Some (fst p))) ans = Some (ps_m s').
Proof.
unfold raw_free. intros H.
apply mleaf_bind in H as (s0 & s1 & H1 & H2). unfold mleaf, mget in H1. cbn in H1. inversion H1. subst s0 s1.
apply mleaf_bind in H2 as (cs' & s2 & H2 & H3). destruct (membed_leaf _ _ _ _ _ H2) as [E [ans Hf]].
unfold mleaf, mupd in H3. cbn in H3. inversion H3. subst s'. exists ans. cbn. exact Hf.
Qed.

