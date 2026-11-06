(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Ops OpsTwin OpsKeep GLib GPot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Import ListNotations.
Import W64 Val Mem St Step Plan ValP PlanS HeapOp UO UG UOK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PotDrop.

Definition drop_of (sc : option sv) (ws : list (sv * sv * sv)) : list (sv * sv * sv) :=
  match sc with Some lo => List.filter (fun x => negb (win3_eqb x (GPot.pwl lo))) ws | None => ws end.
Definition pot_drop (fs : list fact) (ws : list (sv * sv * sv)) : option (list (sv * sv * sv)) :=
  match GPot.pot_scan fs ws with
  | Some None => Some ws
  | Some (Some lo) => Some (List.filter (fun x => negb (win3_eqb x (GPot.pwl lo))) ws)
  | None => None
  end.

Definition pseudo (w : window) : Prop := w_kind w = K_STACK /\ w_len w = 0 /\ AW_BAND <= w_lo w.
Lemma pseudo_no_byte : forall w a, pseudo w -> ~ in_iv (w_iv w) a.
Proof. intros w a (_ & L0 & _). unfold in_iv, w_iv. cbn [fst snd]. lia. Qed.
Lemma pseudo_not_tied : forall w, pseudo w -> ~ aw_tied w.
Proof. intros w (K & _ & B) [[_ LO]|G]; [lia| unfold K_GHOST, K_STACK in *; lia]. Qed.
Lemma pseudo_not_heap : forall w, pseudo w -> ~ heap_kind w.
Proof. intros w (K & _ & _) HK. unfold heap_kind, K_BLOCK, K_STACK in *. lia. Qed.

Lemma pot_drop_spec : forall E fs ws ws0, facts_hold E fs -> pot_drop fs ws = Some ws0 ->
  (forall x, In x ws0 -> In x ws) /\ (forall x, In x ws -> In x ws0 \/ pseudo (wden E x)) /\ (length ws0 <= length ws)%nat.
Proof.
  intros E fs ws ws0 HF H. unfold pot_drop in H. destruct (GPot.pot_scan fs ws) as [[lo|]|] eqn:SC; [| | discriminate].
  - injection H as <-. pose proof (GPot.pot_scan_ok E fs ws (Some lo) HF SC) as (IN & B & _).
    split; [| split].
    + intros x Hx. apply filter_In in Hx. exact (proj1 Hx).
    + intros x Hx. destruct (win3_eqb x (GPot.pwl lo)) eqn:Q.
      * right. apply win3_eqb_eq in Q. subst x. rewrite GPot.pwl_den. unfold pseudo. cbn [w_kind w_len w_lo].
        split; [reflexivity|]. split; [reflexivity|]. unfold AW_BAND, POT_BASE in *. lia.
      * left. apply filter_In. split; [exact Hx|]. rewrite Q. reflexivity.
    + clear. induction ws as [|w ws IH]; cbn [List.filter length]; [lia|]. destruct (negb (win3_eqb w (GPot.pwl lo))); cbn [length]; lia.
  - injection H as <-. split; [auto| split; [auto| lia]].
Qed.

Lemma drop_of_spec : forall E fs ws sc, facts_hold E fs -> GPot.pot_scan fs ws = Some sc ->
  (forall x, In x (drop_of sc ws) -> In x ws) /\ (forall x, In x ws -> In x (drop_of sc ws) \/ pseudo (wden E x)) /\ (length (drop_of sc ws) <= length ws)%nat.
Proof.
  intros E fs ws sc HF SC. apply (pot_drop_spec E fs ws (drop_of sc ws) HF). unfold pot_drop. rewrite SC. destruct sc; reflexivity.
Qed.

Lemma drop_keep : forall E LB (ws ws0 : list (sv * sv * sv)),
  (forall x, In x ws0 -> In x ws) -> (forall x, In x ws -> In x ws0 \/ pseudo (wden E x)) ->
  wins_keep LB (map (wden E) ws) (map (wden E) ws0).
Proof.
  intros E LB ws ws0 SUB OLD. apply wins_keep_intro.
  - intros w Hw. left. apply in_map_iff in Hw as (x & <- & Hx). apply in_map. exact (SUB x Hx).
  - intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). destruct (OLD x Hx) as [H0|PS]; [left; apply in_map; exact H0| right].
    split; [exact (pseudo_not_tied _ PS)|]. intros HK _. exfalso. exact (pseudo_not_heap _ PS HK).
Qed.

End PotDrop.
