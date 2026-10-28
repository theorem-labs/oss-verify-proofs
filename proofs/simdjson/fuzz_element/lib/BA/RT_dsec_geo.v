(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_sec_defs R_flushshadow HandoffImage RT_state RT_rep RT_drain_defs RT_drain_led.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Lemma ds_rel : forall L (m : mem), consts_rep L m -> rel_cells m.
Proof.
  intros L m HC. pose proof HC as (_ & MG & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  repeat match type of IC with _ /\ ?R => let X := fresh "X" in destruct IC as [X IC] end.
  pose proof MG as (M1 & _ & M3 & _). unfold rel_cells, g_got_pagesize_cached, g_got_sealed, g_PageSizeCached.
  split; [exact M1|]. split; [match goal with H : rw_cells asegs m 0x16a270 _ |- _ => exact H end | exact M3].
Qed.

Lemma ds_upd_prefix : forall {X} (f : X -> word) (l : list X) (ws : list word) (k : nat) (lst : X),
  firstn (length l) ws = map f l -> (length l <= length ws)%nat -> (k < length l)%nat -> nth_error l (length l - 1) = Some lst ->
  firstn (length l - 1) (upd ws k (f lst)) = map f (swap_remove k l).
Proof.
  intros X f l ws k lst Hf Hlw Hk Hlst. apply nth_error_ext. intros j.
  rewrite nth_error_firstn, nth_error_map.
  pose proof (swap_remove_length k l Hk) as SL.
  destruct (Nat.ltb_spec j (length l - 1)) as [Hj|Hj].
  - destruct (nth_error (swap_remove k l) j) as [y|] eqn:Ey; [|apply nth_error_None in Ey; lia].
    destruct (swap_remove_nth k l j y Hk Ey) as (Ny & _). cbn [option_map].
    destruct (Nat.eqb_spec j k) as [->|Hne].
    + rewrite Hlst in Ny. injection Ny as <-. rewrite nth_error_upd_same by lia. reflexivity.
    + rewrite nth_error_upd_other by lia.
      assert (E : nth_error (firstn (length l) ws) j = nth_error (map f l) j) by (rewrite Hf; reflexivity).
      rewrite nth_error_firstn, nth_error_map, Ny in E. destruct (Nat.ltb_spec j (length l)) as [_|X']; [exact E | lia].
  - destruct (nth_error (swap_remove k l) j) as [y|] eqn:Ey; [pose proof (nth_error_lt _ _ _ Ey); lia | reflexivity].
Qed.

End GWIN.
