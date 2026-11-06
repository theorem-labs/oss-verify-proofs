(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst FxEnt FxFrame FxCall FxGenA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive ckind : Type :=
| CKFn (rets : list Z)     (* [comment removed for export] *)
| CKKit.                   (* [comment removed for export] *)
Record m4con : Type := M4Con { mc_p0 : sst; mc_q : sst; mc_kind : ckind }.

Definition con_ok (segs : list Segment) (c : m4con) : Prop :=
  match mc_kind c with
  | CKFn rets => fn_ok segs (mc_p0 c) (mc_q c) rets
  | CKKit => kfn_ok segs (mc_p0 c) (mc_q c)
  end.

(* [comment removed for export] *)
Definition m4site : Type := (nat * list positive * list positive * list (vop * Z * rkind))%type.

Section P.
Variable segs : list Segment.
Variable cons : list m4con.
Hypothesis Hcons : Forall (con_ok segs) cons.
Context {MT : Type}.

Definition ppostM (p : m4site) (S : sst) (_ : MT) : option sst :=
  let '(j, keep, qk, specs) := p in
  match nth_error cons j with
  | Some c => call_cont S (mc_p0 c) (mc_q c) keep qk (List.map (fun '(v, _, _) => v) specs) (views_of specs S) (ret_of S)
  | None => None
  end.

(* [comment removed for export] *)
#[using="Hcons"] Theorem ppostM_ok : forall p S M K, ppostM p S M = Some K ->
  (forall E ms, sden segs E S ms ->
     exists ms'' E'', isteps segs ms ms'' /\ sden segs E'' K ms'' /\ agree (s_next S) E E'' /\
       (forall x, fr_pt E (s_rgs S) x -> ms_mem ms'' x = ms_mem ms x)) /\
  (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins (fun (Hcons : LiaFast.U) => LiaFast.u0).
  intros [[[j keep] qk] specs] S M K Hp. cbn [ppostM] in Hp.
  destruct (nth_error cons j) as [c|] eqn:Hj; [|discriminate].
  assert (Hc : con_ok segs c) by (rewrite Forall_forall in Hcons; exact (Hcons c (nth_error_In _ _ Hj))).
  destruct (call_cont_shape _ _ _ _ _ _ _ _ _ Hp) as (Hsh & Hnx & _).
  split; [|split; [lia | exact Hsh]].
  intros E ms Hd. unfold con_ok in Hc. destruct (mc_kind c) as [rets|].
  - exact (call_sound segs (mc_p0 c) (mc_q c) rets keep qk _ _ _ S K E ms Hc Hp Hd).
  - exact (call_sound_k segs (mc_p0 c) (mc_q c) keep qk _ _ _ S K E ms Hc Hp Hd).
Qed.
End P.
(* [comment removed for export] *)
