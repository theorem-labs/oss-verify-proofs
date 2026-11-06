(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1o8 X1r3 X1rm X1r6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Fixpoint tall {R} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
match t with
| Ret Unr => True
| Ret (Ok r) => P r
| Vis _ k => forall rsp, tall P (k rsp)
end.

Lemma tall_mono : forall {R} (P P' : R -> Prop) t, tall P t -> (forall r, P r -> P' r) -> tall P' t.
Proof.
induction t as [[|r]|n k IH]; cbn; intros H HP.
- exact I.
- apply HP. exact H.
- intros rsp. eapply IH; [apply H| exact HP].
Qed.

Lemma tall_ebind : forall {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree node (exc A)) (f : A -> itree node (exc B)),
tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ebind t f).
Proof.
induction t as [[|a]|n k IH]; cbn; intros f H HF; [exact I| apply HF; exact H|].
intros rsp. apply IH; [apply H| exact HF].
Qed.

Lemma impl_tall : forall segs {R} (t : itree node (exc R)) (P : R -> Prop) (Q : R -> machine_state -> Prop) ms,
impl segs (at_node segs) t (epost Q) ms -> tall P t ->
impl segs (at_node segs) t (epost (fun r ms' => Q r ms' /\ P r)) ms.
Proof.
intros segs R t. induction t as [[|r]|n k IH]; cbn; intros P Q ms H HP.
- exact H.
- eapply evt_mono; [exact H|]. cbn. intros ms' HQ. split; [exact HQ| exact HP].
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH; [apply Hk| apply HP].
Qed.

Section Keeps.
Context {RCEIL : RunCeiling}.
Context {St B : Type} (f : St -> B).

Definition keeps {A} (c : M St A) : Prop := forall s, tall (fun p => f (snd p) = f s) (c s).

#[using="Type"] Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
Proof. intros A a s. reflexivity. Qed.
#[using="Type"] Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
Proof. intros A s. exact I. Qed.
#[using="Type"] Lemma keeps_get : keeps mget.
Proof. intros s. reflexivity. Qed.
#[using="Type"] Lemma keeps_upd : forall g, (forall s, f (g s) = f s) -> keeps (mupd g).
Proof. intros g Hg s. cbn. apply Hg. Qed.
#[using="Type"] Lemma keeps_put_bad : True. Proof. exact I. Qed.
#[using="Type"] Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
Proof. intros A n dec s. cbn. intros rsp. destruct (dec rsp); cbn; [reflexivity| exact I]. Qed.
#[using="Type"] Lemma keeps_bind : forall {A C} (m : M St A) (k : A -> M St C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
Proof.
intros A C m k Hm Hk s. unfold mbind. eapply tall_ebind; [apply Hm|]. cbn. intros [a s1] E. cbn in E.
eapply tall_mono; [apply Hk|]. cbn. intros [c s2] E2. cbn in E2 |- *. congruence.
Qed.

#[using="Type"] Lemma keeps_getk : forall {C} (k : St -> M St C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
Proof. intros C k Hk s. unfold mbind, mget. cbn. apply Hk. Qed.
#[using="Type"] Lemma keeps_loop : forall {X R} fuel (body : X -> M St (X + R)), (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
Proof.
induction fuel as [|fuel IH]; intros body HB x; cbn; [apply keeps_unr|].
apply keeps_bind; [apply HB|]. intros [x'|r]; [apply IH; exact HB| apply keeps_ret].
Qed.
#[using="Type"] Lemma keeps_if : forall {A} (b : bool) (m1 m2 : M St A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
#[using="Type"] Lemma keeps_when : forall (b : bool) (m1 : M St unit), keeps m1 -> keeps (mwhen b m1).
Proof. intros [|] m1 H1; [exact H1| apply keeps_ret]. Qed.
End Keeps.
Arguments keeps {St B} f {A} c.

Ltac keeps_step :=
first [ apply keeps_ret | apply keeps_unr | apply keeps_sys | apply keeps_get
| apply keeps_getk | apply keeps_bind | apply keeps_if | apply keeps_when
| apply keeps_upd; [intros; reflexivity] ].

Ltac keeps_tac :=
repeat (intros; cbn beta;
first [ solve [auto]
| keeps_step
| lazymatch goal with
| |- keeps _ (match ?x with _ => _ end) => destruct x
end ]).

Lemma ev_step_k : forall {B} (f : PState -> B) ceil e,
(forall v s, f (set_brk_ps v s) = f s) -> keeps f (ev_step ceil e).
Proof. intros B f ceil e Hb. destruct e; cbn; keeps_tac; apply keeps_upd; intros; apply Hb. Qed.

Lemma membed_k : forall {B} (f : PState -> B) {R} ceil (t : stree ev Z R),
(forall v s, f (set_brk_ps v s) = f s) -> keeps f (membed ceil t).
Proof. intros B f R ceil t Hb. induction t as [r|e k IH]; cbn; [apply keeps_ret|]. apply keeps_bind; [apply ev_step_k; exact Hb| exact IH]. Qed.

Lemma raw_malloc_so : forall n, keeps ps_so (raw_malloc n).
Proof. intros n. unfold raw_malloc. pose proof (fun R ceil t => @membed_k _ ps_so R ceil t (fun v s => eq_refl)). keeps_tac. Qed.

Lemma raw_free_so : forall p, keeps ps_so (raw_free p).
Proof. intros p. unfold raw_free. pose proof (fun R ceil t => @membed_k _ ps_so R ceil t (fun v s => eq_refl)). keeps_tac. Qed.

Section StdioKeeps.
Context {RCEIL : RunCeiling}.
Context {St B : Type} (f : St -> B).

#[using="Type"] Lemma stdio_wloop_keeps : forall fuel fd iovs, keeps f (stdio_wloop (St:=St) fuel fd iovs).
Proof. induction fuel as [|fuel IH]; intros fd iovs; cbn [stdio_wloop]; keeps_tac. Qed.

#[using="Type"] Lemma stdio_writev_keeps : forall fd buf s, keeps f (stdio_writev (St:=St) fd buf s).
Proof. intros fd buf s. unfold stdio_writev. pose proof stdio_wloop_keeps. keeps_tac. Qed.
End StdioKeeps.

Lemma stdout_fwritex_keeps : forall so0 p, keeps (fun s => set_so_ps so0 s) (stdout_fwritex ps_so set_so_ps p).
Proof.
intros so0 p. unfold stdout_fwritex, stdout_towrite, stdout_writefn, stdout_stdio_write, upd_so, rd_so.
pose proof (@stdio_writev_keeps PState _ (fun s => set_so_ps so0 s)).
keeps_tac.
Qed.

Lemma out_pieces_keeps : forall so0 ps, keeps (fun s => set_so_ps so0 s) (out_pieces ps_so set_so_ps ps).
Proof.
intros so0 ps. induction ps as [|p ps IH]; cbn [out_pieces]; [apply keeps_ret|].
apply keeps_bind; [apply stdout_fwritex_keeps| intros; exact IH].
Qed.

Lemma s_emit_keeps : forall so0 rc, keeps (fun s => set_so_ps so0 s) (s_emit ps_so set_so_ps rc).
Proof.
intros so0 rc. unfold s_emit, stdout_vprintf, stdout_towrite, upd_so.
pose proof (out_pieces_keeps so0). keeps_tac.
Qed.

Lemma io_emit_keeps : forall so0 rc, keeps (fun s => set_so_ps so0 s) (io_emit rc).
Proof. intros. unfold io_emit. apply s_emit_keeps. Qed.

Lemma implM_keepsf : forall segs {B A} (f : PState -> B) (c : M PState A) s Q ms,
implM segs c s Q ms -> keeps f c -> implM segs c s (fun r s' ms' => Q r s' ms' /\ f s' = f s) ms.
Proof.
intros segs B A0 f c s Q ms H K. unfold implM in *.
eapply impl_epost_mono; [eapply impl_tall; [exact H| apply K]|]. cbn. intros [a s'] ms' [HQ E]. split; [exact HQ| exact E].
Qed.

Lemma set_so_ps_eq : forall so0 s s', set_so_ps so0 s' = set_so_ps so0 s ->
ps_m s' = ps_m s /\ ps_brk s' = ps_brk s /\ ps_fa s' = ps_fa s /\ ps_hdr s' = ps_hdr s.
Proof.
intros so0 s s' E.
pose proof (f_equal ps_m E) as E1. pose proof (f_equal ps_brk E) as E2. pose proof (f_equal ps_fa E) as E3. pose proof (f_equal ps_hdr E) as E4.
cbn in E1, E2, E3, E4. auto.
Qed.
