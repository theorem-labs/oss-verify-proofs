(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit.
Import ListNotations.
Open Scope Z_scope.

Definition KI : Z := 2240.

Definition ictx (T p lox qx : Z) (m : mem) : Prop :=
  icpt_env m /\ accessible m T (p + 1) /\ sh_readable m T (p + 1) /\ accessible m lox (qx - lox) /\ sh_readable m lox (qx - lox).
Definition iwin (T p lox qx : Z) (tp : word) : Prop :=
  cwin T (p + 1) /\ T + p + 1 < 2^47 /\ p + 1 <= 2^43 /\ 0x10007fff8000 <= lox /\ lox <= qx /\ qx <= 2^47
  /\ 0x146000 + 164 <= bv_unsigned tp /\ bv_unsigned tp <= 0x7fff7000.

Definition cwinP (P : Z) : Prop := P + 4 <= 0x7fff7000 \/ 0x10007fff8000 <= P.

Definition shw_ok (W : list ivl) : Prop :=
  Forall (fun iv => snd iv <= 0xa9000 \/ (0x146000 <= fst iv /\ snd iv <= 0x7fff7000) \/ 0x10007fff8000 <= fst iv) W.

Lemma shw_outside : forall W s, shw_ok W -> 0x7fff7000 <= s < 0x10007fff8000 -> outside W s.
Proof.
  induction W as [|[a b] W IH]; intros s H Hs; cbn [outside]; [exact I|].
  inversion H as [|x l H1 H2]; subst. cbn [fst snd] in H1. split; [lia| apply IH; assumption].
Qed.
Lemma shw_band : forall W, shw_ok W -> env_band_safe W.
Proof.
  induction W as [|[a b] W IH]; intros H; [constructor|].
  inversion H as [|x l H1 H2]; subst. cbn [fst snd] in H1. constructor; [cbn [fst snd]; lia| apply IH; exact H2].
Qed.

Lemma ictx_frame : forall T p lox qx tp W m m', ictx T p lox qx m -> iwin T p lox qx tp -> munch W m m' -> wmono asegs m m' -> shw_ok W ->
  ictx T p lox qx m'.
Proof.
  intros T p lox qx tp W m m' (IE & A1 & R1 & A2 & R2) (CW & W2 & NS & KLO & LQ & QX & _) MU WM OK.
  assert (CW2 : cwin lox (qx - lox)) by (unfold cwin; lia).
  pose proof (shw_outside W) as HO.
  split; [eapply icpt_env_frame; [exact IE| exact MU| exact WM| apply shw_band; exact OK]|].
  split; [eapply accessible_munch; [exact A1| exact MU| exact CW| intros s Hs; apply HO; [exact OK| lia]]|].
  split; [eapply sh_readable_munch; [exact R1| exact MU| exact CW| intros s Hs; apply HO; [exact OK| lia]]|].
  split; [eapply accessible_munch; [exact A2| exact MU| exact CW2| intros s Hs; apply HO; [exact OK| lia]]|].
  eapply sh_readable_munch; [exact R2| exact MU| exact CW2| intros s Hs; apply HO; [exact OK| lia]].
Qed.

Lemma ictx_env : forall T p lox qx m, ictx T p lox qx m -> icpt_env m.
Proof. intros T p lox qx m H; apply H. Qed.
Lemma ictx_text : forall T p lox qx m A n, ictx T p lox qx m -> T <= A -> A + n <= T + p + 1 -> 0 <= n ->
  accessible m A n /\ sh_readable m A n.
Proof.
  intros T p lox qx m A n (_ & A1 & R1 & _) H1 H2 H3. split; [eapply accessible_sub; [exact A1| lia| lia]| eapply sh_readable_sub; [exact R1| lia| lia| lia]].
Qed.
Lemma ictx_stack : forall T p lox qx m A n, ictx T p lox qx m -> lox <= A -> A + n <= qx -> 0 <= n ->
  accessible m A n /\ sh_readable m A n.
Proof.
  intros T p lox qx m A n (_ & _ & _ & A2 & R2) H1 H2 H3. split; [eapply accessible_sub; [exact A2| lia| lia]| eapply sh_readable_sub; [exact R2| lia| lia| lia]].
Qed.
Lemma iwin_text : forall T p lox qx tp A n, iwin T p lox qx tp -> T <= A -> A + n <= T + p + 1 -> 0 <= n -> cwin A n /\ A + n < 2^47 /\ n <= 2^43.
Proof. intros T p lox qx tp A n ((Hn & CW) & W2 & NS & _) H1 H2 H3. unfold cwin. lia. Qed.
Lemma iwin_stack : forall T p lox qx tp A n, iwin T p lox qx tp -> lox <= A -> A + n <= qx -> 0 <= n -> cwin A n /\ A + n <= 2^47.
Proof. intros T p lox qx tp A n (_ & _ & _ & KLO & LQ & QX & _) H1 H2 H3. unfold cwin. lia. Qed.

Ltac shw_solve := unfold shw_ok; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.
