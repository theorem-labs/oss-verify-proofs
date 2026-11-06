(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import CAP. Import CXS.

Definition job : Type := (acs * plan * shape)%type.
Definition is_ok (r : cres) (s : shape) : bool := match r with COk s' => shape_eqb s' s | CErr _ _ _ => false end.
Lemma is_ok_eq : forall r s, is_ok r s = true -> r = COk s.
Proof. intros [s'|c p cs] s H; [|discriminate]. cbn in H. apply shape_eqb_eq in H. subst. reflexivity. Qed.

Definition batch_ok (run : acs -> plan -> cres) (jobs : list job) : bool :=
  forallb (fun j => is_ok (run (fst (fst j)) (snd (fst j))) (snd j)) jobs.
Lemma batch_sound : forall run jobs, batch_ok run jobs = true ->
  forall cs p s, In (cs, p, s) jobs -> run cs p = COk s.
Proof. intros run jobs H cs p s Hin. apply is_ok_eq. exact (proj1 (forallb_forall _ _) H (cs, p, s) Hin). Qed.
(* [comment removed for export] *)
Lemma batch_with : forall (T : Type) (mk : T) (run : T -> acs -> plan -> cres) jobs,
  (let it := mk in batch_ok (run it) jobs) = true -> forall cs p s, In (cs, p, s) jobs -> run mk cs p = COk s.
Proof. intros T mk run jobs H. exact (batch_sound (run mk) jobs H). Qed.
