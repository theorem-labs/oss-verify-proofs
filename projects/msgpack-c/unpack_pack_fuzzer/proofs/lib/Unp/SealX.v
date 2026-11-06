(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Module SealX.
Import Seal.

Lemma shadZ_inj8 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> shadZ a = shadZ b -> a = b.
Proof.
  intros a b Ha Hb E. unfold shadZ in E.
  rewrite (Z.div_mod a 8), (Z.div_mod b 8) by lia. rewrite Ha, Hb. lia.
Qed.
Lemma shadZ_neq8 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> a <> b -> shadZ a <> shadZ b.
Proof. intros a b Ha Hb N E. apply N. exact (shadZ_inj8 a b Ha Hb E). Qed.

Lemma seal_ok_no9 : forall ws cs, (forall w, In w ws -> w_kind w <> K_TWIN) -> (forall c, In c cs -> snd c mod 8 = 0) -> seal_ok ws cs.
Proof. intros ws cs N A. split; [intros w Hw K; exfalso; exact (N w Hw K)| exact A]. Qed.
Lemma seal_ok_cs : forall ws cs cs', seal_ok ws cs -> (forall c, In c cs' -> In c cs) -> seal_ok ws cs'.
Proof. intros ws cs cs' S HC. exact (seal_ok_mono ws cs ws cs' S (fun w H _ => H) HC). Qed.
Lemma seal_ok_tl : forall ws c cs, seal_ok ws (c :: cs) -> seal_ok ws cs.
Proof. intros ws c cs S. apply (seal_ok_cs ws (c :: cs) cs S). intros x Hx. right. exact Hx. Qed.
Lemma seal_ok_app_other : forall ws l cs, seal_ok ws cs -> (forall w, In w l -> w_kind w <> K_TWIN) -> seal_ok (ws ++ l) cs.
Proof. intros ws l cs S N. apply seal_ok_app; [exact S|]. apply Forall_forall. exact N. Qed.
Lemma seal_ok_cons_other : forall ws w0 cs, seal_ok ws cs -> w_kind w0 <> K_TWIN -> seal_ok (w0 :: ws) cs.
Proof.
  intros ws w0 cs S N. apply (seal_ok_ws ws cs (w0 :: ws) S). intros w [<-|Hw] K; [exfalso; exact (N K)| exact Hw].
Qed.

Lemma seal_ok_map : forall (A : Type) (f : A -> window) (l l' : list A) cs, seal_ok (map f l) cs ->
  (forall x, In x l' -> In x l \/ w_kind (f x) <> K_TWIN) -> seal_ok (map f l') cs.
Proof.
  intros A f l l' cs S H. apply (seal_ok_ws (map f l) cs (map f l') S). intros w Hw K.
  apply in_map_iff in Hw as (x & <- & Hx). destruct (H x Hx) as [Hx0|N]; [apply in_map; exact Hx0| exfalso; exact (N K)].
Qed.

Lemma seal_ok_twin_window : forall ws cs b n, seal_ok ws cs -> b mod 8 = 0 ->
  (forall c, In c cs -> fst c mod 8 = 0 /\ fst c <> b) -> seal_ok (ws ++ [Win (shadZ b) n K_TWIN]) cs.
Proof.
  intros ws cs b n [S1 S2] Hb HC. split; [| exact S2].
  intros w Hw K c Hc. apply in_app_or in Hw as [Hw|[<-|[]]]; [exact (S1 w Hw K c Hc)|].
  cbn [w_lo]. destruct (HC c Hc) as [A N]. apply shadZ_neq8; [exact Hb| exact A| intros E; apply N; symmetry; exact E].
Qed.
Lemma seal_ok_grow_twin : forall ws cs b n kb, seal_ok ws cs -> b mod 8 = 0 -> kb <> K_TWIN ->
  (forall c, In c cs -> fst c mod 8 = 0 /\ fst c <> b) ->
  seal_ok ((ws ++ [Win b n kb]) ++ [Win (shadZ b) ((n + 7) / 8) K_TWIN]) cs.
Proof.
  intros ws cs b n kb S Hb KB HC. apply seal_ok_twin_window; [| exact Hb| exact HC].
  apply seal_ok_app_other; [exact S|]. intros w [<-|[]]. exact KB.
Qed.

Lemma seal_ok_not_out : forall ws cs c n, seal_ok ws cs -> In c cs -> ~ In (Win (shadZ (fst c)) n K_TWIN) ws.
Proof. intros ws cs c n [S1 _] Hc Hw. exact (S1 _ Hw eq_refl c Hc eq_refl). Qed.
Lemma seal_ok_al8 : forall ws cs c, seal_ok ws cs -> In c cs -> snd c mod 8 = 0.
Proof. intros ws cs c [_ S2] Hc. exact (S2 c Hc). Qed.

End SealX.
