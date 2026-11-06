(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim SeqExec StoreOk AgentLib AxSymExec3 DepotInv.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2.
Open Scope Z_scope.
Unset Lia Cache.

Definition inv_den (segs : list Segment) (id : nat) (args : list expr) (E : env) (M : word -> option byte) : Prop :=
  match id, args with
  | O, [d; ss; k; b17; b18] =>
      DepotInv segs (bv_unsigned (edenot E d)) (bv_unsigned (edenot E ss)) (bv_unsigned (edenot E k))
               (bv_unsigned (edenot E b17)) (bv_unsigned (edenot E b18)) M
  | _, _ => False
  end.

(* [comment removed for export] *)
Definition in_foot (E : env) (id : nat) (args : list expr) (x : word) : Prop :=
  Exists (fun it => bv_unsigned (edenot E (a_base (fst it))) + a_off (fst it) <= bv_unsigned x
                    < bv_unsigned (edenot E (a_base (fst it))) + a_off (fst it) + bv_unsigned (edenot E (snd it))) (inv_foot id args).

Lemma inv_den_frame : forall segs id args E M M',
  (forall x : word, in_foot E id args x -> M' x = M x) ->
  inv_den segs id args E M -> inv_den segs id args E M'.
Proof.
  intros segs id args E M M' Hfr H.
  unfold inv_den in H |- *.
  destruct id as [|id']; [|exact H].
  destruct args as [|d args]; [exact H|]. destruct args as [|ss args]; [exact H|].
  destruct args as [|k args]; [exact H|].
  destruct args as [|b17 args]; [exact H|]. destruct args as [|b18 args]; [exact H|]. destruct args; [|exact H].
  apply (DepotInv_frame segs _ _ _ _ _ M M'); [|exact H].
  intros x Hx. apply Hfr. unfold in_foot, in_fp, depot_fp, TCAP in *. cbn [inv_foot].
  apply Exists_exists in Hx as (it & Hin & Hit).
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hit.
  - apply Exists_cons_hd. cbn [fst snd a_base a_off edenot]. rewrite !u64_lit by lia. lia.
  - apply Exists_cons_tl, Exists_cons_hd. cbn [fst snd a_base a_off edenot]. rewrite !u64_lit by lia. lia.
  - apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd a_base a_off edenot]. rewrite !u64_lit by lia. lia.
  - apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd a_base a_off edenot]. rewrite !u64_lit by lia. lia.
Qed.

Lemma inv_den_extends : forall segs id args E M M',
  mem_extends segs M M' -> inv_den segs id args E M -> inv_den segs id args E M'.
Proof.
  intros segs id args E M M' HX H.
  unfold inv_den in H |- *.
  destruct id as [|id']; [|exact H].
  destruct args as [|d args]; [exact H|]. destruct args as [|ss args]; [exact H|].
  destruct args as [|k args]; [exact H|].
  destruct args as [|b17 args]; [exact H|]. destruct args as [|b18 args]; [exact H|]. destruct args; [|exact H].
  exact (DepotInv_extends segs _ _ _ _ _ M M' HX H).
Qed.

(* [comment removed for export] *)
Lemma inv_den_agree : forall segs id args E E' M,
  (forall e, In e args -> edenot E e = edenot E' e) -> inv_den segs id args E M -> inv_den segs id args E' M.
Proof.
  intros segs id args E E' M Hag H.
  unfold inv_den in H |- *.
  destruct id as [|id']; [|exact H].
  destruct args as [|d args]; [exact H|]. destruct args as [|ss args]; [exact H|].
  destruct args as [|k args]; [exact H|].
  destruct args as [|b17 args]; [exact H|]. destruct args as [|b18 args]; [exact H|]. destruct args; [|exact H].
  rewrite <- (Hag d), <- (Hag ss), <- (Hag k), <- (Hag b17), <- (Hag b18) by (cbn; tauto). exact H.
Qed.

(* [comment removed for export] *)
Lemma inv_den_map : forall segs id args E E' M (f : expr -> expr),
  (forall e, In e args -> edenot E (f e) = edenot E' e) -> (inv_den segs id (map f args) E M <-> inv_den segs id args E' M).
Proof.
  intros segs id args E E' M f Hf. unfold inv_den.
  destruct id as [|id']; [|tauto].
  destruct args as [|d args]; [tauto|]. destruct args as [|ss args]; [tauto|].
  destruct args as [|k args]; [tauto|].
  destruct args as [|b17 args]; [tauto|]. destruct args as [|b18 args]; [tauto|]. destruct args; [|cbn [map]; tauto].
  cbn [map]. rewrite !Hf by (cbn; tauto). tauto.
Qed.
