(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Seal.
Definition SBz : Z := 0x7fff8000.
Definition shadZ (a : Z) : Z := a / 8 + SBz.
Definition K_TWIN : Z := 9.

Definition seal_ok (ws : list window) (cs : list (Z * Z)) : Prop :=
  (forall w, In w ws -> w_kind w = K_TWIN -> forall c, In c cs -> w_lo w <> shadZ (fst c)) /\
  (forall c, In c cs -> snd c mod 8 = 0).

Lemma seal_ok_nil : forall ws, seal_ok ws [].
Proof. intros ws. split; intros; contradiction. Qed.

Lemma seal_ok_mono : forall ws cs ws' cs', seal_ok ws cs ->
  (forall w, In w ws' -> w_kind w = K_TWIN -> In w ws) -> (forall c, In c cs' -> In c cs) -> seal_ok ws' cs'.
Proof.
  intros ws cs ws' cs' [S1 S2] HW HC. split.
  - intros w Hw K c Hc. exact (S1 w (HW w Hw K) K c (HC c Hc)).
  - intros c Hc. exact (S2 c (HC c Hc)).
Qed.

Lemma seal_ok_ws : forall ws cs ws', seal_ok ws cs -> (forall w, In w ws' -> w_kind w = K_TWIN -> In w ws) -> seal_ok ws' cs.
Proof. intros ws cs ws' S HW. exact (seal_ok_mono ws cs ws' cs S HW (fun c H => H)). Qed.

Lemma seal_ok_app : forall ws cs new, seal_ok ws cs -> Forall (fun w => w_kind w <> K_TWIN) new -> seal_ok (ws ++ new) cs.
Proof.
  intros ws cs new S HN. apply (seal_ok_ws ws cs); [exact S|]. intros w Hw K. apply in_app_iff in Hw as [Hw|Hw]; [exact Hw|].
  exfalso. exact (proj1 (Forall_forall _ _) HN w Hw K).
Qed.

Lemma seal_ok_cons : forall ws cs c, seal_ok ws cs -> snd c mod 8 = 0 ->
  (forall w, In w ws -> w_kind w = K_TWIN -> w_lo w <> shadZ (fst c)) -> seal_ok ws (c :: cs).
Proof.
  intros ws cs c [S1 S2] H8 HW. split.
  - intros w Hw K c' [<-|Hc']; [exact (HW w Hw K)| exact (S1 w Hw K c' Hc')].
  - intros c' [<-|Hc']; [exact H8| exact (S2 c' Hc')].
Qed.
End Seal.
