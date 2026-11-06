(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI.
Open Scope Z_scope.
Unset Lia Cache.

Module ItabOk.
Section WithSegs.
Variable segs : list Segment.

Lemma itab_ok_empty : itab_ok segs IMap.empty.
Proof. intros pc fi H. rewrite IMap.find_empty in H. discriminate. Qed.

Lemma build_itab_ok : forall pcs acc,
  IMap.bst acc -> itab_ok segs acc -> IMap.bst (build_itab segs pcs acc) /\ itab_ok segs (build_itab segs pcs acc).
Proof.
  induction pcs as [|pc pcs IH]; intros acc Hb Hok; cbn [build_itab].
  - split; assumption.
  - destruct (decode_at segs pc) as [fi|] eqn:Hd.
    + apply IH.
      * apply IMap.add_bst. exact Hb.
      * intros pc' fi' Hf.
        destruct (PrimInt63.eqb pc pc') eqn:He.
        -- apply eqb_correct in He. subst pc'. rewrite IMap.find_add_same in Hf by exact Hb. congruence.
        -- rewrite IMap.find_add_other_eqb in Hf by assumption. exact (Hok _ _ Hf).
    + apply IH; assumption.
Qed.

Lemma build_itab_ok_of_eq : forall pcs t, build_itab segs pcs IMap.empty = t -> itab_ok segs t.
Proof.
  intros pcs t <-. apply (proj2 (build_itab_ok pcs IMap.empty IMap.bst_empty itab_ok_empty)).
Qed.

Lemma build_itab_bst_of_eq : forall pcs t, build_itab segs pcs IMap.empty = t -> IMap.bst t.
Proof.
  intros pcs t <-. apply (proj1 (build_itab_ok pcs IMap.empty IMap.bst_empty itab_ok_empty)).
Qed.

End WithSegs.
End ItabOk.
