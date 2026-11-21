(** * KeyRank — L3: the sort places each symbol at its same-length rank


    [places_prefix] (ItGTblSortWin) proves the LENGTH of what a window
    slot holds; this file proves the ORDER: symbol [sym] lands exactly
    at its window base plus the count of EARLIER same-length symbols —
    which, read declaratively ([zcount_zlens_firstn]), is
    [Huff.code_offset].  Proof mirrors [places_prefix]'s snoc induction;
    the different-window case reuses its disjointness block verbatim. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Huff Inftrees ItGTblRev ItGTblGeom ItGTblSortWin InftreesBridge.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** Symbol [sym]'s landing slot, at any sort prefix [n > sym]. *)
Lemma rank_prefix : forall lens codes cnt n (sym : nat),
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  cnt = sw_cnt lens codes ->
  (n <= Z.to_nat codes)%nat ->
  (sym < n)%nat ->
  lens (Z.of_nat sym) <> 0 ->
  snd (it_sort n 0 lens (sw_offs cnt) zzero)
      (sw_offs cnt (lens (Z.of_nat sym))
       + it_count sym 0 lens zzero (lens (Z.of_nat sym)))
  = Z.of_nat sym.
Proof.
  intros lens codes cnt n sym Hlens Hcnt Hn Hsn Hsym.
  assert (Hnn : forall i, 1 <= i <= 15 -> 0 <= cnt i)
    by (intros i _; rewrite Hcnt; apply sw_cnt_nonneg).
  assert (Hlr : 1 <= lens (Z.of_nat sym) <= 15).
  { specialize (Hlens (Z.of_nat sym) ltac:(lia)). lia. }
  revert Hn Hsn. induction n as [|k IH]; intros Hn Hsn; [lia|].
  assert (Hkr : 0 <= Z.of_nat k < codes) by lia.
  assert (Hoff : forall l', l' <> 0 ->
            fst (it_sort k 0 lens (sw_offs cnt) zzero) l'
            = sw_offs cnt l' + it_count k 0 lens zzero l')
    by (intros l' Hl'; apply sort_offs_advance0; exact Hl').
  destruct (Z.eq_dec (lens (Z.of_nat k)) 0) as [Hz|Hnz].
  - (* zero-length symbol k: skipped; sym <> k since lens sym <> 0 *)
    rewrite (sort_snd_snoc0_zero k lens (sw_offs cnt) zzero Hz).
    destruct (Nat.eq_dec sym k) as [->|Hne]; [congruence|].
    apply IH; lia.
  - rewrite (sort_snd_snoc0_nz k lens (sw_offs cnt) zzero Hnz).
    rewrite Hoff by exact Hnz.
    destruct (Nat.eq_dec sym k) as [->|Hne].
    + (* sym is the snoc'd write: exact slot *)
      rewrite zset_same. reflexivity.
    + (* an earlier symbol: the write must miss sym's slot *)
      assert (Hd : sw_offs cnt (lens (Z.of_nat sym))
                     + it_count sym 0 lens zzero (lens (Z.of_nat sym))
                   <> sw_offs cnt (lens (Z.of_nat k))
                     + it_count k 0 lens zzero (lens (Z.of_nat k))).
      { assert (Hl'r : 1 <= lens (Z.of_nat k) <= 15)
          by (specialize (Hlens (Z.of_nat k) Hkr); lia).
        assert (Hkc : it_count k 0 lens zzero (lens (Z.of_nat k))
                      < cnt (lens (Z.of_nat k))).
        { rewrite Hcnt. unfold sw_cnt.
          pose proof (count_mono (Z.to_nat codes) (S k) 0 lens zzero
                        (lens (Z.of_nat k)) Hn) as Hm.
          rewrite (count_hit0 k lens zzero) in Hm. lia. }
        assert (Hsc : it_count (S sym) 0 lens zzero (lens (Z.of_nat sym))
                      = it_count sym 0 lens zzero (lens (Z.of_nat sym)) + 1)
          by (apply (count_hit0 sym lens zzero)).
        assert (Hscnt : it_count (S sym) 0 lens zzero (lens (Z.of_nat sym))
                        <= cnt (lens (Z.of_nat sym))).
        { rewrite Hcnt. unfold sw_cnt. apply count_mono. lia. }
        pose proof (count_zzero_nonneg sym 0 lens (lens (Z.of_nat sym)))
          as Hnn0.
        pose proof (count_zzero_nonneg k 0 lens (lens (Z.of_nat k))) as Hnn1.
        destruct (Z.eq_dec (lens (Z.of_nat sym)) (lens (Z.of_nat k)))
          as [Heq|Hnel].
        - (* same window: sym's rank is strictly below k's *)
          rewrite <- Heq.
          pose proof (count_mono k (S sym) 0 lens zzero
                        (lens (Z.of_nat sym)) ltac:(lia)) as Hm2.
          lia.
        - (* different windows: the cumulative layout separates them *)
          destruct (Z.lt_ge_cases (lens (Z.of_nat sym)) (lens (Z.of_nat k)))
            as [Hlt2|Hge].
          + pose proof (sw_offs_mono cnt (lens (Z.of_nat sym) + 1)
                          (lens (Z.of_nat k)) Hnn ltac:(lia) ltac:(lia))
              as Hmono.
            rewrite sw_offs_step in Hmono by lia. lia.
          + pose proof (sw_offs_mono cnt (lens (Z.of_nat k) + 1)
                          (lens (Z.of_nat sym)) Hnn ltac:(lia) ltac:(lia))
              as Hmono.
            rewrite sw_offs_step in Hmono by lia. lia. }
      rewrite zset_other by exact Hd.
      apply IH; lia.
Qed.

(** Declarative reading of the rank: over a lens LIST, the prefix count
    at bucket [b] is [count_len (firstn sym L) b] — i.e. exactly
    [Huff.code_offset L sym b].  Cons induction in the
    [zcount_zlens_count_len] style. *)
Lemma zcount_zlens_firstn : forall (L : list nat) (sym : nat) (b : nat),
  (sym <= length L)%nat ->
  zcount sym 0 (zlens L) (Z.of_nat b)
  = Z.of_nat (count_len (firstn sym L) b).
Proof.
  induction L as [|x L IH]; intros sym b Hs.
  - cbn [length] in Hs. assert (sym = 0)%nat by lia. subst sym. reflexivity.
  - destruct sym as [|sym]; [reflexivity|].
    cbn [length] in Hs.
    cbn [zcount firstn].
    assert (Hz0 : zlens (x :: L) 0 = Z.of_nat x) by reflexivity.
    rewrite Hz0.
    rewrite (zcount_zlens_tail sym 0 x L (Z.of_nat b)) by lia.
    rewrite (IH sym b) by lia.
    rewrite count_len_cons.
    destruct (Nat.eq_dec x b) as [->|Hx].
    + rewrite Z.eqb_refl. lia.
    + replace (Z.of_nat x =? Z.of_nat b) with false
        by (symmetry; apply Z.eqb_neq; lia).
      lia.
Qed.

(** The tie to [Huff.code_offset], spelled at the definition. *)
Lemma zcount_code_offset : forall (L : list nat) (sym : nat) (b : nat),
  (sym <= length L)%nat ->
  zcount sym 0 (zlens L) (Z.of_nat b)
  = Z.of_nat (code_offset L sym b).
Proof.
  intros L sym b Hs. unfold code_offset.
  apply zcount_zlens_firstn. exact Hs.
Qed.
