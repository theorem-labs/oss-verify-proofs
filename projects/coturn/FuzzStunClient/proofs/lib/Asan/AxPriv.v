(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk AgentLib SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 DepotInvG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition pvE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).
Definition pstart (E : env) (a : saddr) : Z := pvE E (a_base a) + a_off a.

(* [comment removed for export] *)
Definition in_rs (E : env) (rs : list (saddr * expr)) (x : Z) : Prop :=
  Exists (fun r => pstart E (fst r) <= x < pstart E (fst r) + pvE E (snd r)) rs.

(* [comment removed for export] *)
Definition PRIV (segs : list Segment) (tag : nat) (rs : list (saddr * expr)) (args : list expr) (k : Z)
                (E : env) (M : word -> option byte) : Prop :=
  match tag, rs, args with
  | O, [r1; r2; r3; r4], [eB; eP; enc; efc; edp; esb; eih] =>
         pstart E (fst r1) = pvE E edp /\ pvE E (snd r1) = 4194328
      /\ pstart E (fst r2) = pvE E eB  /\ pvE E (snd r2) = 16 * pvE E enc
      /\ pstart E (fst r3) = pvE E esb /\ pvE E (snd r3) = 28
      /\ pstart E (fst r4) = pvE E eP  /\ pvE E (snd r4) = 8 * pvE E efc
      /\ depot_invG segs (pvE E edp) (pvE E esb) (pvE E eih) (pvE E eB) (pvE E eP) (pvE E enc) (pvE E efc) k M
  | _, _, _ => False
  end.

(* [comment removed for export] *)
Definition priv_exprs (rs : list (saddr * expr)) (args : list expr) : list expr :=
  map (fun r => a_base (fst r)) rs ++ map snd rs ++ args.

Lemma pvE_lit : forall E z, 0 <= z < 2 ^ 64 -> pvE E (ELit z) = z.
Proof. intros E z Hz. unfold pvE. cbn [edenot]. apply u64_lit. exact Hz. Qed.

(* [comment removed for export] *)
Lemma PRIV_frame_avail : forall segs tag rs args k E M M',
  (forall x : word, in_rs E rs (bv_unsigned x) -> avail segs M x -> M' x = M x) ->
  PRIV segs tag rs args k E M -> PRIV segs tag rs args k E M'.
Proof.
  intros segs tag rs args k E M M' AG HP.
  destruct tag; [|exact HP]. cbn [PRIV] in *.
  destruct rs as [|r1 [|r2 [|r3 [|r4 [|? ?]]]]]; try exact HP.
  destruct args as [|eB [|eP [|enc [|efc [|edp [|esb [|eih [|? ?]]]]]]]]; try exact HP.
  destruct HP as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & L4 & HI).
  repeat (split; [assumption|]).
  eapply depot_invG_agree; [exact HI |].
  intros x Hx Hav. apply AG; [|exact Hav]. unfold in_rs, depot_footG in *.
  destruct Hx as [Hx|[Hx|[Hx|Hx]]];
    [ apply Exists_cons_hd
    | apply Exists_cons_tl, Exists_cons_hd
    | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd
    | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd ]; lia.
Qed.

Lemma PRIV_frame : forall segs tag rs args k E M M',
  (forall x : word, in_rs E rs (bv_unsigned x) -> M' x = M x) ->
  PRIV segs tag rs args k E M -> PRIV segs tag rs args k E M'.
Proof. intros segs tag rs args k E M M' AG HP. eapply PRIV_frame_avail; [|exact HP]. intros x Hx _. apply AG, Hx. Qed.

(* [comment removed for export] *)
Lemma PRIV_agree : forall segs tag rs args k E E' M,
  (forall e, In e (priv_exprs rs args) -> edenot E' e = edenot E e) ->
  PRIV segs tag rs args k E M -> PRIV segs tag rs args k E' M.
Proof.
  intros segs tag rs args k E E' M AG HP.
  destruct tag; [|exact HP]. cbn [PRIV] in *.
  destruct rs as [|r1 [|r2 [|r3 [|r4 [|? ?]]]]]; try exact HP.
  destruct args as [|eB [|eP [|enc [|efc [|edp [|esb [|eih [|? ?]]]]]]]]; try exact HP.
  unfold priv_exprs in AG. cbn [map app] in AG.
  assert (R : forall e, In e [a_base (fst r1); a_base (fst r2); a_base (fst r3); a_base (fst r4); snd r1; snd r2; snd r3; snd r4;
                            eB; eP; enc; efc; edp; esb; eih] -> pvE E' e = pvE E e)
    by (intros e He; unfold pvE; rewrite (AG e He); reflexivity).
  unfold pstart in *.
  rewrite !R by (cbn; tauto). exact HP.
Qed.

Lemma PRIV_pos : forall segs tag rs args k E M, PRIV segs tag rs args k E M -> 0 <= k.
Proof.
  intros segs tag rs args k E M HP. destruct tag; [|destruct HP]. cbn [PRIV] in HP.
  destruct rs as [|r1 [|r2 [|r3 [|r4 [|? ?]]]]]; try contradiction.
  destruct args as [|eB [|eP [|enc [|efc [|edp [|esb [|eih [|? ?]]]]]]]]; try contradiction.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & HI). eapply depot_invG_pos. exact HI.
Qed.
