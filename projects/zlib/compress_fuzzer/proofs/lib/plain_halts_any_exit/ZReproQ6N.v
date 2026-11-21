(** * ZReproQ6N — the MATCH arm: the overlapped back-reference copy IS
    [lz_copy] (LEN-chain layer 2b, match piece).

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).

    Under the one-shot facts (output anchor tie, whave = 0, sane <> 0 —
    the residue-v2 premises), one [inf_MATCH] trip is a FOUR-way case:
    output-starved leave; distance-too-far [M_BAD] (the window branch is
    unreachable except through the guard); a FULL direct copy landing at
    [M_LEN] whose slice extension IS [lz_copy]; or a PARTIAL copy that
    zeroes [o_left] (the next trip starves — the caller's EXIT arm).
    [cw3 = min(o_left, length)] has no window quantities, so the direct
    case needs no induction over trips — only over bytes, which is
    [zr_copyn_out]: byte [i] of the machine copy reads the entry buffer
    at [put - dist + (i mod dist)], the modular wrap of the overlapped
    [do { *put++ = *from++; }].

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6D.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The overlapped copy, pointwise.
   ========================================================================== *)

Lemma zr_copyn_out : forall n win o d,
  0 < d <= o_put o ->
  o_put (ob_copyn n win o (OSout (o_put o - d))) = o_put o + Z.of_nat n
  /\ o_left (ob_copyn n win o (OSout (o_put o - d)))
     = o_left o - Z.of_nat n
  /\ (forall j, j < o_put o ->
        o_buf (ob_copyn n win o (OSout (o_put o - d))) j = o_buf o j)
  /\ (forall i, (i < n)%nat ->
        o_buf (ob_copyn n win o (OSout (o_put o - d)))
              (o_put o + Z.of_nat i)
        = o_buf o (o_put o - d + (Z.of_nat i) mod d)).
Proof.
  induction n as [|k IH]; intros win o d Hd.
  - cbn [ob_copyn].
    split; [lia|]. split; [lia|].
    split; [intros j Hj; reflexivity|].
    intros i Hi. lia.
  - cbn [ob_copyn os_read os_bump].
    set (o1 := ob_write o (o_buf o (o_put o - d))) in *.
    assert (P1 : o_put o1 = o_put o + 1) by reflexivity.
    assert (L1 : o_left o1 = o_left o - 1) by reflexivity.
    assert (B1own : o_buf o1 (o_put o) = o_buf o (o_put o - d)).
    { unfold o1, ob_write. cbn [o_buf]. apply zset_same. }
    assert (B1low : forall j, j <> o_put o -> o_buf o1 j = o_buf o j).
    { intros j Hj. unfold o1, ob_write. cbn [o_buf]. unfold zset.
      rewrite (proj2 (Z.eqb_neq j (o_put o)) Hj). reflexivity. }
    replace (o_put o - d + 1) with (o_put o1 - d) by lia.
    destruct (IH win o1 d ltac:(lia)) as (IHput & IHleft & IHlow & IHhi).
    split. { rewrite IHput. lia. }
    split. { rewrite IHleft. lia. }
    split.
    { intros j Hj. rewrite IHlow by lia. apply B1low. lia. }
    intros i Hi.
    destruct i as [|i'].
    + (* byte 0: the first write, then below the tail's put *)
      rewrite IHlow by lia.
      change (Z.of_nat 0) with 0. rewrite Z.add_0_r, B1own.
      rewrite Z.mod_0_l by lia. f_equal. lia.
    + (* byte S i' = the tail's byte i' *)
      replace (o_put o + Z.of_nat (S i')) with (o_put o1 + Z.of_nat i')
        by lia.
      rewrite (IHhi i' ltac:(lia)).
      pose proof (Z.mod_pos_bound (Z.of_nat i') d ltac:(lia)) as Hr.
      set (r := Z.of_nat i' mod d) in *.
      assert (Hsucc : Z.of_nat (S i') mod d
                      = (if Z.eqb (r + 1) d then 0 else r + 1)).
      { replace (Z.of_nat (S i')) with (Z.of_nat i' + 1) by lia.
        rewrite <- Zplus_mod_idemp_l. fold r.
        destruct (Z.eqb_spec (r + 1) d) as [E|Nn].
        - rewrite E. apply Z.mod_same. lia.
        - apply Z.mod_small. lia. }
      rewrite Hsucc.
      destruct (Z.eqb_spec (r + 1) d) as [E|Nn].
      * (* wrap: the tail reads the byte the head just wrote *)
        replace (o_put o1 - d + r) with (o_put o) by lia.
        rewrite B1own. f_equal. lia.
      * (* no wrap: the tail reads an original byte *)
        rewrite B1low by lia. f_equal. lia.
Qed.

(* ==========================================================================
   2.  The slice form: the machine's direct copy IS [lz_copy].
   ========================================================================== *)

Lemma zr_nth_map_seq : forall (f : nat -> Z) (n j : nat) (dflt : Z),
  (j < n)%nat -> nth j (map f (seq 0 n)) dflt = f j.
Proof.
  intros f n j dflt Hj.
  rewrite (nth_indep _ dflt (f 0%nat))
    by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth. rewrite seq_nth by exact Hj. reflexivity.
Qed.

Lemma zr_copyn_lz : forall n win o d,
  0 < d <= o_put o ->
  ob_slice (ob_copyn n win o (OSout (o_put o - d))) 0
           (o_put o + Z.of_nat n)
  = ob_slice o 0 (o_put o)
    ++ lz_copy (ob_slice o 0 (o_put o)) n (Z.to_nat d).
Proof.
  intros n win o d Hd.
  destruct (zr_copyn_out n win o d Hd) as (_ & _ & Low & Hi).
  set (o' := ob_copyn n win o (OSout (o_put o - d))) in *.
  unfold ob_slice at 1.
  replace (Z.to_nat (o_put o + Z.of_nat n))
    with (Z.to_nat (o_put o) + n)%nat by lia.
  rewrite seq_app, map_app.
  f_equal.
  - (* the untouched prefix *)
    unfold ob_slice. apply map_ext_in.
    intros m Hm. apply in_seq in Hm.
    rewrite Z.add_0_l. apply Low. lia.
  - (* the copied bytes are the modular reads *)
    rewrite (zr_map_seq_shift _ _ (Z.to_nat (o_put o)) n).
    unfold lz_copy.
    apply map_ext_in.
    intros m Hm. apply in_seq in Hm. cbv beta.
    replace (0 + Z.of_nat (Z.to_nat (o_put o) + m)%nat)
      with (o_put o + Z.of_nat m) by lia.
    rewrite (Hi m ltac:(lia)).
    (* nth of the slice is the buffer read *)
    unfold ob_slice.
    rewrite length_map, length_seq.
    set (j := (Z.to_nat (o_put o) - Z.to_nat d + m mod Z.to_nat d)%nat).
    assert (Hj : (j < Z.to_nat (o_put o))%nat).
    { unfold j.
      pose proof (Nat.mod_upper_bound m (Z.to_nat d) ltac:(lia)). lia. }
    rewrite (zr_nth_map_seq (fun k => o_buf o (0 + Z.of_nat k))
               (Z.to_nat (o_put o)) j 0 Hj).
    cbv beta. rewrite Z.add_0_l.
    f_equal.
    unfold j.
    rewrite Nat2Z.inj_add, Nat2Z.inj_sub
      by (pose proof (Nat.mod_upper_bound m (Z.to_nat d) ltac:(lia)); lia).
    rewrite Nat2Z.inj_mod.
    rewrite !Z2Nat.id by lia.
    lia.
Qed.

(* ==========================================================================
   3.  One MATCH trip, four ways.
   ========================================================================== *)

Lemma zr_match_cases : forall q,
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  q_out q = o_put (q_ob q) + o_left (q_ob q) ->
  q_out q <= 4294967295 ->
  w_whave (s_win (q_st q)) = 0 ->
  t_sane (s_tab (q_st q)) <> 0 ->
  0 < u_offset (s_cur (q_st q)) < 4294967296 ->
  0 <= u_length (s_cur (q_st q)) < 2147483648 ->
  (* starved *)
  (o_left (q_ob q) = 0 /\ inf_MATCH q = InfLeave q)
  (* distance too far: BAD *)
  \/ (exists qb, inf_MATCH q = InfCont qb
        /\ h_mode (s_hdr (q_st qb)) = M_BAD)
  (* full direct copy: the block's LZ step *)
  \/ (exists q',
        inf_MATCH q = InfCont q'
        /\ u_offset (s_cur (q_st q)) <= o_put (q_ob q)
        /\ u_length (s_cur (q_st q)) <= o_left (q_ob q)
        /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
           = ob_slice (q_ob q) 0 (o_put (q_ob q))
             ++ lz_copy (ob_slice (q_ob q) 0 (o_put (q_ob q)))
                        (Z.to_nat (u_length (s_cur (q_st q))))
                        (Z.to_nat (u_offset (s_cur (q_st q))))
        /\ o_put (q_ob q') = o_put (q_ob q) + u_length (s_cur (q_st q))
        /\ o_put (q_ob q') + o_left (q_ob q')
           = o_put (q_ob q) + o_left (q_ob q)
        /\ h_mode (s_hdr (q_st q')) = M_LEN
        /\ q_br q' = q_br q
        /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
        /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
        (* amendment #10 (q7-decode carrier): flags frame-rides the
           full-copy arm; the repeat-split reflexivity closer covers it. *)
        /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
        (* amendment #11: h_check/h_total frame conjuncts — carrier
           q7-decode; g1 census; q6 pre-ruling;
           #10 shape *)
        /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
        /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
        /\ s_win (q_st q') = s_win (q_st q)
        /\ s_tab (q_st q') = s_tab (q_st q)
        /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q)
  (* partial copy: output exhausted, the next trip starves *)
  \/ (exists q',
        inf_MATCH q = InfCont q'
        /\ o_left (q_ob q') = 0
        /\ h_mode (s_hdr (q_st q')) = h_mode (s_hdr (q_st q))
        /\ q_ret q' = q_ret q).
Proof.
  intros q Hput Hleft Htie Hcap Hwh Hsn Hoff Hlen.
  unfold inf_MATCH. cbv zeta.
  destruct (Z.eqb_spec (o_left (q_ob q)) 0) as [E0|N0].
  { left. split; [exact E0 | reflexivity]. }
  assert (Houtd : u32 (q_out q - o_left (q_ob q)) = o_put (q_ob q)).
  { unfold u32. rewrite Htie.
    replace (o_put (q_ob q) + o_left (q_ob q) - o_left (q_ob q))
      with (o_put (q_ob q)) by lia.
    apply Z.mod_small. lia. }
  rewrite Houtd.
  destruct (Z.ltb_spec (o_put (q_ob q)) (u_offset (s_cur (q_st q))))
    as [Hfar|Hnear].
  - (* window branch: dead by whave = 0 /\ sane <> 0 *)
    right; left.
    assert (Hcw : u32 (u_offset (s_cur (q_st q)) - o_put (q_ob q))
                  = u_offset (s_cur (q_st q)) - o_put (q_ob q)).
    { unfold u32. apply Z.mod_small. lia. }
    rewrite Hcw, Hwh.
    rewrite (proj2 (Z.ltb_lt 0
               (u_offset (s_cur (q_st q)) - o_put (q_ob q))) ltac:(lia)).
    rewrite (proj2 (negb_true_iff _) (proj2 (Z.eqb_neq _ 0) Hsn)).
    cbn [andb].
    eexists. split; [reflexivity | reflexivity].
  - (* direct copy *)
    destruct (Z.ltb_spec (o_left (q_ob q)) (u_length (s_cur (q_st q))))
      as [Hpart|Hfull].
    + (* partial: copies o_left, zeroes it *)
      right; right; right.
      destruct (zr_copyn_out (Z.to_nat (o_left (q_ob q)))
                  (w_win (s_win (q_st q))) (q_ob q)
                  (u_offset (s_cur (q_st q))) ltac:(lia))
        as (_ & Lft & _ & _).
      rewrite Z2Nat.id in Lft by lia.
      destruct (Z.eqb_spec
                  (u_length (s_cur (q_st q)) - o_left (q_ob q)) 0)
        as [Ez|Nz]; [lia|].
      eexists. split; [reflexivity|].
      cbn [q_st q_ob qset_ob qset_st].
      split. { rewrite Lft. lia. }
      split; reflexivity.
    + (* full: the LZ step *)
      right; right; left.
      destruct (zr_copyn_out (Z.to_nat (u_length (s_cur (q_st q))))
                  (w_win (s_win (q_st q))) (q_ob q)
                  (u_offset (s_cur (q_st q))) ltac:(lia))
        as (Putn & Lftn & _ & _).
      rewrite Z2Nat.id in Putn, Lftn by lia.
      pose proof (zr_copyn_lz (Z.to_nat (u_length (s_cur (q_st q))))
                    (w_win (s_win (q_st q))) (q_ob q)
                    (u_offset (s_cur (q_st q))) ltac:(lia)) as Hlz.
      rewrite Z2Nat.id in Hlz by lia.
      rewrite Z.sub_diag.
      change (u32 0) with 0.
      rewrite (proj2 (Z.eqb_eq 0 0) eq_refl).
      eexists. split; [reflexivity|].
      cbn [q_st q_ob qset_ob qset_st qmode].
      split; [lia|].
      split; [lia|].
      split.
      { cbn [q_ob]. rewrite Putn. exact Hlz. }
      split. { exact Putn. }
      split. { rewrite Putn, Lftn. lia. }
      repeat split; try reflexivity.
Qed.

(** The trivial trip: no output room, immediate leave. *)
Lemma zr_match_left0 : forall q,
  o_left (q_ob q) = 0 -> inf_MATCH q = InfLeave q.
Proof.
  intros q H. unfold inf_MATCH. cbv zeta.
  rewrite (proj2 (Z.eqb_eq (o_left (q_ob q)) 0) H). reflexivity.
Qed.

Print Assumptions zr_copyn_lz.
Print Assumptions zr_match_cases.
