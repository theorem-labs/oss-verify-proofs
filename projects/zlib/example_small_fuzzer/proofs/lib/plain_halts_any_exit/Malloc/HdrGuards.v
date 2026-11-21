(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Local Open Scope Z_scope.

Section ORACLE.
Context {O : Type}.
Variable pans : O -> aptr -> Z -> Z -> Z.
Variable pupd : O -> ev -> Z -> O.

Lemma prun_guard_false : forall {R} (o : O) tag (k bail : M R) (x : O * R),
  prun pans pupd o (guard tag false k bail) <> SRet x.
Proof. intros R o tag k bail x. unfold guard, prun. cbn. discriminate. Qed.

Lemma free_hdr_guards : forall (o : O) (st : mstate) (p : aptr) (st1 : mstate) (g : aptr) (idx : Z) (b3 lo hi : Z) (gh : ghdr) (g0 : aptr),
  prun pans pupd o (free_hdr st p) = SRet (o, Some (st1, g, idx)) ->
  cell_read (get_shadow st (fst p)) (snd p + -4) = Known 0 ->
  cell_read (get_shadow st (fst p)) (snd p + -3) = Known b3 ->
  cell_read (get_shadow st (fst p)) (snd p + -2) = Known lo ->
  cell_read (get_shadow st (fst p)) (snd p + -2 + 1) = Known hi ->
  (s_groups st) !! (aadd p (- (UNIT * (lo + 256 * hi)) - UNIT)) = Some gh -> g_meta gh = Some g0 ->
  let off16 := lo + 256 * hi in
  let index := Z.land b3 31 in
  let mr := get_meta_rec st g0 in
  index <= m_last_idx mr
  /\ Z.testbit (m_avail mr) index = false /\ Z.testbit (m_freed mr) index = false
  /\ (exists ar, (s_areas st) !! (area_of g0) = Some ar /\ a_check ar = c_secret (ctx st))
  /\ (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * index <= off16 < size_class (m_sizeclass mr) * (index + 1))
  /\ (48 <= m_sizeclass mr -> m_sizeclass mr = 63)
  /\ (m_maplen mr <> 0 -> off16 <= m_maplen mr * 4096 / UNIT - 1).
Proof.
  intros o st p st1 g idx b3 lo hi gh g0 RUN C4 C3 C2 C1 Hgh Hg off16 index mr.
  unfold free_hdr, get_meta in RUN.
  destruct (snd p mod 16 =? 0) eqn:G10; [| exfalso; exact (prun_guard_false o _ _ _ _ RUN)].
  unfold guard at 1 in RUN.
  unfold rd16, rd8 in RUN. cbn [aadd fst snd] in RUN.
  rewrite C2, C1, C3, C4 in RUN. cbn [Z.eqb negb] in RUN.
  unfold get_group in RUN. rewrite Hgh, Hg in RUN. fold mr index off16 in RUN.
  repeat lazymatch type of RUN with
  | prun _ _ _ (guard _ ?c _ _) = _ =>
      let G := fresh "G" in destruct c eqn:G; [unfold guard at 1 in RUN; cbv iota in RUN | exfalso; exact (prun_guard_false o _ _ _ _ RUN)]
  end.
  clear RUN.
  apply Z.leb_le in G0. apply negb_true_iff in G1. apply negb_true_iff in G2.
  split; [exact G0|]. split; [exact G1|]. split; [exact G2|].
  split. { destruct ((s_areas st) !! (area_of g0)) as [ar|]; [| discriminate]. exists ar. split; [reflexivity|]. apply Z.eqb_eq. exact G3. }
  split. { intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G4. apply andb_true_iff in G4. destruct G4 as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia. }
  split. { intros Hsc. destruct (Z.ltb_spec (m_sizeclass mr) 48); [lia|]. apply Z.eqb_eq in G4. exact G4. }
  intros Hml. destruct (Z.eqb_spec (m_maplen mr) 0); [lia|]. cbn [negb] in G5. apply Z.leb_le in G5. exact G5.
Qed.
End ORACLE.
