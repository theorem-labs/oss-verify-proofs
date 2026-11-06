(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzR2Theory BzR2D1 BzR2D BzR1a.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzR1a.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzR1d.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR1a.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

Ltac dsn := cbv beta iota delta [d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv s_in s_out s_avail_out s_tin s_tout c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail
    d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit d_set_base d_set_perm d_set_minLens d_set_sv out_byte c_write c_set_len c_set_k0 c_set_ch c_inc].
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma flush_run_S : forall n d s, flush_run (S n) d s =
  (if s_avail_out s =? 0 then (d, s, true)
   else if d_out_len d =? 0 then (d, s, false)
   else flush_run n (d_set_out_len (d_set_cbcrc d (crc_update (d_cbcrc d) (d_out_ch d))) (d_out_len d - 1)) (out_byte s (d_out_ch d))).
Proof. reflexivity. Qed.

Lemma unrle_plain_S : forall f d s, unrle_plain (S f) d s =
      (let '(d1, s1, ret) := flush_run (S (Z.to_nat (d_out_len d))) d s in
      if ret then (0, d1, s1) else
      let PP := sv_nblock (d_sv d1) + 1 in
      if d_nused d1 =? PP then (0, d1, s1)
      else if PP <? d_nused d1 then (1, d1, s1)
      else
        let d2 := d_set_out_ch (d_set_out_len d1 1) (d_k0 d1) in
        match get_sym d2 with
        | None => (1, d2, s1)
        | Some (k1, d3) =>
            let d3 := d_set_nused d3 (d_nused d3 + 1) in
            if d_nused d3 =? PP then unrle_plain f d3 s1
            else if negb (k1 =? d_k0 d3) then unrle_plain f (d_set_k0 d3 k1) s1
            else
              let d4 := d_set_out_len d3 2 in
              match get_sym d4 with
              | None => (1, d4, s1)
              | Some (k2, d5) =>
                  let d5 := d_set_nused d5 (d_nused d5 + 1) in
                  if d_nused d5 =? PP then unrle_plain f d5 s1
                  else if negb (k2 =? d_k0 d5) then unrle_plain f (d_set_k0 d5 k2) s1
                  else
                    let d6 := d_set_out_len d5 3 in
                    match get_sym d6 with
                    | None => (1, d6, s1)
                    | Some (k3, d7) =>
                        let d7 := d_set_nused d7 (d_nused d7 + 1) in
                        if d_nused d7 =? PP then unrle_plain f d7 s1
                        else if negb (k3 =? d_k0 d7) then unrle_plain f (d_set_k0 d7 k3) s1
                        else
                          match get_sym d7 with
                          | None => (1, d7, s1)
                          | Some (k4, d8) =>
                              let d8 := d_set_out_len (d_set_nused d8 (d_nused d8 + 1)) (k4 + 4) in
                              match get_sym d8 with
                              | None => (1, d8, s1)
                              | Some (k5, d9) => unrle_plain f (d_set_nused (d_set_k0 d9 k5) (d_nused d9 + 1)) s1
                              end
                          end
                    end
              end
        end).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nth_app_mid : forall (pre l post : list Z) i, (i < length l)%nat -> nth (length pre + i) (pre ++ l ++ post) 0 = nth i l 0.
Proof. intros. rewrite app_nth2_plus, app_nth1 by assumption. reflexivity. Qed.

Section UnRLE.
  (* [comment removed for export] *)
  Variables (n : nat) (t : list Z) (sm : bool) (pos sym : nat -> Z) (TV : dst -> Prop) (TVC : zarr -> Z -> Prop).
  Hypothesis Hn : length t = n.
  Hypothesis Hn1 : (1 <= n)%nat.
  Hypothesis sym_spec : forall m, (m < n)%nat -> sym m = nth m t 0.
  Hypothesis TV_small : forall d, TV d -> smallb d = sm.
  Hypothesis TV_rand : forall d, TV d -> d_rand d = 0.
  Hypothesis TV_frame : forall d d', TV d ->
    d_small d' = d_small d -> d_rand d' = d_rand d -> d_bs100k d' = d_bs100k d -> d_tt d' = d_tt d ->
    d_cftab d' = d_cftab d -> d_ll16 d' = d_ll16 d -> d_ll4 d' = d_ll4 d -> TV d'.
  Hypothesis get_sym_src : forall d m, TV d -> d_tPos d = pos m -> get_sym d = Some (sym m, d_set_tPos d (pos (S m))).
  Hypothesis c_get_src : sm = false -> forall tt cap c m, TVC tt cap -> c_tPos c = pos m ->
    c_get tt cap c = Some (sym m, CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c) (c_k0 c) (pos (S m)) (c_out c) (c_avail c)).

  (* [comment removed for export] *)
  Variables (q_state q_out_ch q_out_len q_rand q_rNToGo q_rTPos q_bsBuff q_bsLive q_bs100k q_small q_blockNo q_verb q_origPtr q_tPos q_k0 : Z)
            (q_unzftab : zarr) (q_nused : Z) (q_cftab q_cftabCopy q_tt q_ll16 q_ll4 : zarr) (q_tt_al q_ll_al : bool)
            (q_sbcrc q_sccrc q_cbcrc q_cccrc q_nInUse : Z) (q_inUse q_inUse16 q_s2u q_mtfa q_mtfbase q_sel q_selMtf q_len q_limit q_base q_perm q_minLens : zarr)
            (q_sv : dsv).
  Let d0 : dst := DST q_state q_out_ch q_out_len q_rand q_rNToGo q_rTPos q_bsBuff q_bsLive q_bs100k q_small q_blockNo q_verb q_origPtr q_tPos q_k0 q_unzftab q_nused q_cftab q_cftabCopy q_tt q_ll16 q_ll4 q_tt_al q_ll_al q_sbcrc q_sccrc q_cbcrc q_cccrc q_nInUse q_inUse q_inUse16 q_s2u q_mtfa q_mtfbase q_sel q_selMtf q_len q_limit q_base q_perm q_minLens q_sv.
  Hypothesis TV0 : TV d0.
  Hypothesis Hsv : sv_nblock q_sv = Z.of_nat n.
  (* [comment removed for export] *)
  Variables (q_in : list Z) (q_tin : Z).

  #[local] Notation "'DD' och olen crc nu k0 tp" := (DST q_state och olen q_rand q_rNToGo q_rTPos q_bsBuff q_bsLive q_bs100k q_small q_blockNo q_verb q_origPtr tp k0 q_unzftab nu q_cftab q_cftabCopy q_tt q_ll16 q_ll4 q_tt_al q_ll_al q_sbcrc q_sccrc crc q_cccrc q_nInUse q_inUse q_inUse16 q_s2u q_mtfa q_mtfbase q_sel q_selMtf q_len q_limit q_base q_perm q_minLens q_sv)
    (at level 10, och at level 9, olen at level 9, crc at level 9, nu at level 9, k0 at level 9, tp at level 9).
  #[local] Notation "'SS' sout avail tout" := (DSTRM q_in sout avail q_tin tout)
    (at level 10, sout at level 9, avail at level 9, tout at level 9).

  Lemma TV_DD : forall och olen crc nu k0 tp, TV (DD och olen crc nu k0 tp).
  Proof. intros. apply (TV_frame d0); [exact TV0| reflexivity..]. Qed.

  Lemma get_DD : forall och olen crc nu k0 m,
    get_sym (DD och olen crc nu k0 (pos m)) = Some (sym m, DD och olen crc nu k0 (pos (S m))).
  Proof. intros. rewrite (get_sym_src _ m); [reflexivity| apply TV_DD| reflexivity]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma flush_run_spec : forall k och crc nu k0 tp sout avail tout, Z.of_nat k <= avail ->
    flush_run (S k) (DD och (Z.of_nat k) crc nu k0 tp) (SS sout avail tout) =
    (DD och 0 (crc_list crc (repeat och k)) nu k0 tp, SS (repeat och k ++ sout) (avail - Z.of_nat k) (tout + Z.of_nat k), (avail =? Z.of_nat k)).
  Proof.
    induction k as [|k IH]; intros och crc nu k0 tp sout avail tout Hk; rewrite flush_run_S; dsn.
    - cbn [repeat app crc_list fold_left]. rewrite Z.sub_0_r, Z.add_0_r. destruct (Z.eqb_spec avail 0) as [->|NE]; [reflexivity|].
      change (Z.of_nat 0 =? 0) with true. cbv iota. replace (avail =? Z.of_nat 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - replace (avail =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.of_nat (S k) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia. rewrite IH by lia.
      cbn [repeat]. rewrite crc_list_cons, (repeat_cons k och), <- app_assoc. cbn [app].
      f_equal; [f_equal; f_equal; lia|]. destruct (Z.eqb_spec (avail - 1) (Z.of_nat k)), (Z.eqb_spec avail (Z.of_nat (S k))); try reflexivity; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma eqb_F : forall a b, a <> b -> (a =? b) = false. Proof. intros. apply Z.eqb_neq. assumption. Qed.
  Lemma eqb_T : forall a b, a = b -> (a =? b) = true. Proof. intros. apply Z.eqb_eq. assumption. Qed.
  Lemma ltb_F : forall a b, b <= a -> (a <? b) = false. Proof. intros. apply Z.ltb_ge. assumption. Qed.
  Lemma negb_T : forall a b, a <> b -> negb (a =? b) = true. Proof. intros. apply Bool.negb_true_iff. apply Z.eqb_neq. assumption. Qed.
  Lemma negb_F : forall a b, a = b -> negb (a =? b) = false. Proof. intros. apply Bool.negb_false_iff. apply Z.eqb_eq. assumption. Qed.
  Ltac ifF := match goal with |- context [if ?c then _ else _] =>
    let E := fresh in assert (E : c = false) by (first [apply eqb_F | apply ltb_F | apply negb_F]; lia); rewrite E; clear E; cbv beta iota zeta end.
  Ltac ifT := match goal with |- context [if ?c then _ else _] =>
    let E := fresh in assert (E : c = true) by (first [apply eqb_T | apply negb_T]; lia); rewrite E; clear E; cbv beta iota zeta end.

  (* [comment removed for export] *)
  Lemma t_at : forall pre l post i, t = pre ++ l ++ post -> (i < length l)%nat -> nth (length pre + i) t 0 = nth i l 0.
  Proof. intros pre l post i -> Hi. apply nth_app_mid. exact Hi. Qed.
  Lemma t_len : forall pre l post, t = pre ++ l ++ post -> (length pre + length l + length post = n)%nat.
  Proof. intros pre l post E. rewrite <- Hn, E, !length_app. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma plain_loop : forall rs f pre c k crc k0 sout avail tout,
    t = pre ++ rl_enc rs -> RWF rs -> (length rs < f)%nat ->
    Z.of_nat k + Z.of_nat (length (rl_dec rs)) <= avail ->
    let p := length pre in
    ((p < n)%nat -> k0 = nth p t 0) ->
    exists och' k0' tp',
      unrle_plain f (DD c (Z.of_nat k) crc (Z.of_nat p + 1) k0 (pos (S p))) (SS sout avail tout) =
      (0, DD och' 0 (crc_list crc (repeat c k ++ rl_dec rs)) (Z.of_nat n + 1) k0' tp',
          SS (rev (rl_dec rs) ++ repeat c k ++ sout) (avail - Z.of_nat k - Z.of_nat (length (rl_dec rs))) (tout + Z.of_nat k + Z.of_nat (length (rl_dec rs)))).
  Proof.
    induction rs as [|[c' L'] rs IH]; intros f pre c k crc k0 sout avail tout Ht W Hf Hav p Hk0.
    - (* [comment removed for export] *)
      cbn [rl_enc] in Ht. rewrite app_nil_r in Ht. assert (Hp : p = n) by (subst p; rewrite <- Hn, Ht; reflexivity).
      destruct f as [|f]; [lia|]. rewrite unrle_plain_S. dsn. rewrite Nat2Z.id. rewrite flush_run_spec by lia. cbv beta iota zeta. dsn.
      cbn [rl_dec length rev app]. rewrite app_nil_r, Z.add_0_r, Z.sub_0_r. rewrite Hsv, Hp.
      exists c, k0, (pos (S n)).
      destruct (avail =? Z.of_nat k); [reflexivity|]. rewrite Z.eqb_refl. reflexivity.
    - cbn [rl_enc] in Ht. cbn [RWF] in W. cps_destruct W as (Hc' & HL' & AD & W). cbn [length] in Hf. cbn [rl_dec] in Hav |- *.
      rewrite length_app, repeat_length in Hav |- *.
      pose proof (t_len pre (rcode c' L') (rl_enc rs) Ht) as TL.
      pose proof (rcode_length c' L' HL') as RL.
      destruct (rcode_hd c' L' ltac:(lia)) as [tl RC].
      assert (Hpn : (p < n)%nat) by (subst p; rewrite RC in TL; cbn [length] in TL; lia).
      specialize (Hk0 Hpn). subst p. rewrite <- (Nat.add_0_r (length pre)) in Hk0.
      rewrite (t_at pre (rcode c' L') (rl_enc rs) 0 Ht ltac:(rewrite RC; cbn; lia)), RC in Hk0. cbn [nth] in Hk0. subst k0.
      set (p := length pre) in *.
      destruct f as [|f]; [lia|]. rewrite unrle_plain_S. dsn. rewrite Nat2Z.id. rewrite flush_run_spec by lia. cbv beta iota zeta.
      ifF. dsn. rewrite Hsv. ifF. ifF. rewrite get_DD. cbv beta iota zeta. dsn.
      set (crc1 := crc_list crc (repeat c k)). set (sout1 := repeat c k ++ sout).
      (* [comment removed for export] *)
      assert (IHk : forall k0', ((p + length (rcode c' L') < n)%nat -> k0' = nth (p + length (rcode c' L')) t 0) ->
        exists och' k0'' tp',
          unrle_plain f (DD c' (Z.of_nat (Z.to_nat L')) crc1 (Z.of_nat (p + length (rcode c' L')) + 1) k0' (pos (S (p + length (rcode c' L')))))
                      (SS sout1 (avail - Z.of_nat k) (tout + Z.of_nat k)) =
          (0, DD och' 0 (crc_list crc1 (repeat c' (Z.to_nat L') ++ rl_dec rs)) (Z.of_nat n + 1) k0'' tp',
              SS (rev (rl_dec rs) ++ repeat c' (Z.to_nat L') ++ sout1) (avail - Z.of_nat k - Z.of_nat (Z.to_nat L') - Z.of_nat (length (rl_dec rs)))
                 (tout + Z.of_nat k + Z.of_nat (Z.to_nat L') + Z.of_nat (length (rl_dec rs))))).
      { intros k0' HK. pose proof (IH f (pre ++ rcode c' L') c' (Z.to_nat L') crc1 k0' sout1 (avail - Z.of_nat k) (tout + Z.of_nat k)) as X.
        rewrite length_app in X. apply X; [rewrite <- app_assoc; exact Ht| exact W| lia| lia| exact HK]. }
      (* [comment removed for export] *)
      assert (FIN : forall och' k0'' tp',
        (0, DD och' 0 (crc_list crc1 (repeat c' (Z.to_nat L') ++ rl_dec rs)) (Z.of_nat n + 1) k0'' tp',
            SS (rev (rl_dec rs) ++ repeat c' (Z.to_nat L') ++ sout1) (avail - Z.of_nat k - Z.of_nat (Z.to_nat L') - Z.of_nat (length (rl_dec rs)))
               (tout + Z.of_nat k + Z.of_nat (Z.to_nat L') + Z.of_nat (length (rl_dec rs))))
        = (0, DD och' 0 (crc_list crc (repeat c k ++ repeat c' (Z.to_nat L') ++ rl_dec rs)) (Z.of_nat n + 1) k0'' tp',
            SS (rev (repeat c' (Z.to_nat L') ++ rl_dec rs) ++ repeat c k ++ sout) (avail - Z.of_nat k - Z.of_nat (Z.to_nat L' + length (rl_dec rs)))
               (tout + Z.of_nat k + Z.of_nat (Z.to_nat L' + length (rl_dec rs))))).
      { intros. subst crc1 sout1. rewrite !crc_list_app, rev_app_distr, rev_repeat, <- !app_assoc. f_equal. f_equal; lia. }
      (* [comment removed for export] *)
      assert (SYM : forall i, (S i < length (rcode c' L'))%nat -> (S i < 4)%nat -> sym (S (p + i)) = c').
      { intros i Hi Hi4. rewrite sym_spec by lia. replace (S (p + i)) with (p + S i)%nat by lia. subst p. rewrite (t_at pre (rcode c' L') (rl_enc rs) (S i) Ht Hi).
        unfold rcode. destruct (Z.ltb_spec L' 4); [apply nth_repeat_lt; unfold rcode in Hi; rewrite (proj2 (Z.ltb_lt _ _)) in Hi by lia; rewrite repeat_length in Hi; lia|].
        unfold rcode in Hi. rewrite (proj2 (Z.ltb_ge _ _)) in Hi by lia. rewrite length_app, repeat_length in Hi. cbn [length] in Hi.
        rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat_lt. lia. }
      (* [comment removed for export] *)
      assert (NXT : (p + length (rcode c' L') < n)%nat -> sym (p + length (rcode c' L')) = hd_char rs /\ (L' < 4 -> hd_char rs <> c')).
      { intros Hlt. split; [| exact AD]. rewrite sym_spec by exact Hlt.
        destruct rs as [|[c2 L2] rs2]; [cbn [rl_enc length] in TL; rewrite app_nil_r in *; lia|].
        destruct (rl_enc_hd ((c2, L2) :: rs2) W ltac:(discriminate)) as [tl2 E2]. rewrite E2 in Ht.
        subst p. rewrite <- (Nat.add_0_r (length pre + length (rcode c' L'))%nat).
        replace (pre ++ rcode c' L' ++ hd_char ((c2, L2) :: rs2) :: tl2) with ((pre ++ rcode c' L') ++ [hd_char ((c2, L2) :: rs2)] ++ tl2) in Ht by (rewrite <- !app_assoc; reflexivity).
        rewrite <- length_app. rewrite (t_at (pre ++ rcode c' L') [hd_char ((c2, L2) :: rs2)] tl2 0 Ht ltac:(cbn; lia)). reflexivity. }
      destruct (Z.ltb_spec L' 4) as [LT|GE].
      + (* [comment removed for export] *)
        assert (RCE : rcode c' L' = repeat c' (Z.to_nat L')) by (unfold rcode; rewrite (proj2 (Z.ltb_lt _ _)) by exact LT; reflexivity).
        rewrite RCE, repeat_length in IHk, SYM, NXT, TL.
        assert (L' = 1 \/ L' = 2 \/ L' = 3) as [-> |[-> | ->]] by lia.
        * (* [comment removed for export] *) change (Z.to_nat 1) with 1%nat in *. change (Z.of_nat 1) with 1 in IHk.
          destruct (Nat.eq_dec (p + 1) n) as [END|NE].
          -- ifT. cps_destruct (IHk c' ltac:(lia)) as (o & kk & tp & E). exists o, kk, tp.
             replace (Z.of_nat p + 1 + 1) with (Z.of_nat (p + 1) + 1) by lia. replace (S (S p)) with (S (p + 1)) by lia.
             rewrite E. apply FIN.
          -- ifF. destruct (NXT ltac:(lia)) as [NX1 NX2]. replace (S p) with (p + 1)%nat by lia. rewrite NX1. ifT.
             cps_destruct (IHk (hd_char rs) ltac:(intros; rewrite <- sym_spec by lia; rewrite <- NX1; reflexivity)) as (o & kk & tp & E). exists o, kk, tp.
             replace (Z.of_nat p + 1 + 1) with (Z.of_nat (p + 1) + 1) by lia. replace (S (S p)) with (S (p + 1)) by lia.
             rewrite E. apply FIN.
        * (* [comment removed for export] *) change (Z.to_nat 2) with 2%nat in *. change (Z.of_nat 2) with 2 in IHk.
          pose proof (SYM 0%nat ltac:(lia) ltac:(lia)) as S0. rewrite Nat.add_0_r in S0. rewrite S0. ifF. ifF. rewrite get_DD. cbv beta iota zeta. dsn.
          destruct (Nat.eq_dec (p + 2) n) as [END|NE].
          -- ifT. cps_destruct (IHk c' ltac:(lia)) as (o & kk & tp & E). exists o, kk, tp.
             replace (Z.of_nat p + 1 + 1 + 1) with (Z.of_nat (p + 2) + 1) by lia. replace (S (S (S p))) with (S (p + 2)) by lia.
             rewrite E. apply FIN.
          -- ifF. destruct (NXT ltac:(lia)) as [NX1 NX2]. replace (S (S p)) with (p + 2)%nat by lia. rewrite NX1. ifT.
             cps_destruct (IHk (hd_char rs) ltac:(intros; rewrite <- sym_spec by lia; rewrite <- NX1; reflexivity)) as (o & kk & tp & E). exists o, kk, tp.
             replace (Z.of_nat p + 1 + 1 + 1) with (Z.of_nat (p + 2) + 1) by lia. replace (S (p + 2 + 1))%nat with (S (S (p + 2)))%nat by lia.
             replace (S (S (S p))) with (S (p + 2)) by lia.
             rewrite E. apply FIN.
        * (* [comment removed for export] *) change (Z.to_nat 3) with 3%nat in *. change (Z.of_nat 3) with 3 in IHk.
          pose proof (SYM 0%nat ltac:(lia) ltac:(lia)) as S0. rewrite Nat.add_0_r in S0. rewrite S0. ifF. ifF. rewrite get_DD. cbv beta iota zeta. dsn.
          replace (S (S p)) with (S (p + 1)) by lia. rewrite (SYM 1%nat) by lia. ifF. ifF. rewrite get_DD. cbv beta iota zeta. dsn.
          destruct (Nat.eq_dec (p + 3) n) as [END|NE].
          -- ifT. cps_destruct (IHk c' ltac:(lia)) as (o & kk & tp & E). exists o, kk, tp.
             replace (Z.of_nat p + 1 + 1 + 1 + 1) with (Z.of_nat (p + 3) + 1) by lia. replace (S (S (S (p + 1)))) with (S (p + 3)) by lia.
             rewrite E. apply FIN.
          -- ifF. destruct (NXT ltac:(lia)) as [NX1 NX2]. replace (S (S (p + 1))) with (p + 3)%nat by lia. rewrite NX1. ifT.
             cps_destruct (IHk (hd_char rs) ltac:(intros; rewrite <- sym_spec by lia; rewrite <- NX1; reflexivity)) as (o & kk & tp & E). exists o, kk, tp.
             replace (Z.of_nat p + 1 + 1 + 1 + 1) with (Z.of_nat (p + 3) + 1) by lia. replace (S (S (S (p + 1)))) with (S (p + 3)) by lia.
             rewrite E. apply FIN.
      + (* [comment removed for export] *)
        assert (RCE : rcode c' L' = repeat c' 4 ++ [L' - 4]) by (unfold rcode; rewrite (proj2 (Z.ltb_ge _ _)) by exact GE; reflexivity).
        assert (RLN : length (rcode c' L') = 5%nat) by (rewrite RCE; reflexivity).
        rewrite RLN in IHk, SYM, NXT, TL.
        pose proof (SYM 0%nat ltac:(lia) ltac:(lia)) as S0. rewrite Nat.add_0_r in S0. rewrite S0. ifF. ifF. rewrite get_DD. cbv beta iota zeta. dsn.
        replace (S (S p)) with (S (p + 1)) by lia. rewrite (SYM 1%nat) by lia. ifF. ifF. rewrite get_DD. cbv beta iota zeta. dsn.
        replace (S (S (p + 1))) with (S (p + 2)) by lia. rewrite (SYM 2%nat) by lia. ifF. ifF. rewrite get_DD. cbv beta iota zeta. dsn.
        (* [comment removed for export] *)
        assert (CNT : sym (S (p + 3)) = L' - 4).
        { rewrite sym_spec by lia. replace (S (p + 3)) with (p + 4)%nat by lia. subst p. rewrite (t_at pre (rcode c' L') (rl_enc rs) 4 Ht ltac:(rewrite RLN; lia)), RCE. reflexivity. }
        replace (S (S (p + 2))) with (S (p + 3)) by lia. rewrite CNT. rewrite get_DD. cbv beta iota zeta. dsn.
        replace (S (S (p + 3))) with (S (p + 4)) by lia.
        cps_destruct (IHk (sym (S (p + 4))) ltac:(intros; rewrite sym_spec by lia; f_equal; lia)) as (o & kk & tp & E). exists o, kk, tp.
        replace (L' - 4 + 4) with (Z.of_nat (Z.to_nat L')) by lia.
        replace (Z.of_nat p + 1 + 1 + 1 + 1 + 1 + 1) with (Z.of_nat (p + 5) + 1) by lia. replace (S (S (p + 4))) with (S (p + 5)) by lia.
        rewrite E. apply FIN.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma c_flush_S : forall n c, c_flush (S n) c =
    (if c_avail c =? 0 then (c, true) else if c_len c =? 1 then (c, false) else c_flush n (c_set_len (c_write c) (c_len c - 1))).
  Proof. reflexivity. Qed.
  Lemma unrle_creg_S : forall f eq1 tt cap PP c, unrle_creg (S f) eq1 tt cap PP c =
     (let '(c1, stop) :=
        if eq1 then
          (if c_avail c =? 0 then (c_set_len c 1, true) else (c_write c, false))
        else if 0 <? c_len c then
          let '(c', r) := c_flush (S (Z.to_nat (c_len c))) c in
          if r then (c', true)
          else if c_avail c' =? 0 then (c_set_len c' 1, true) else (c_write c', false)
        else (c, false) in
      if stop then (0, c1) else
      if PP <? c_nused c1 then (1, c1)
      else if c_nused c1 =? PP then (0, c_set_len c1 0)
      else
        let c2 := c_set_ch c1 (c_k0 c1) in
        match c_get tt cap c2 with
        | None => (1, c2)
        | Some (k1, c3) =>
            let c3 := c_inc c3 in
            if negb (k1 =? c_k0 c3) then unrle_creg f true tt cap PP (c_set_k0 c3 k1)
            else if c_nused c3 =? PP then unrle_creg f true tt cap PP c3
            else
              let c4 := c_set_len c3 2 in
              match c_get tt cap c4 with
              | None => (1, c4)
              | Some (k2, c5) =>
                  let c5 := c_inc c5 in
                  if c_nused c5 =? PP then unrle_creg f false tt cap PP c5
                  else if negb (k2 =? c_k0 c5) then unrle_creg f false tt cap PP (c_set_k0 c5 k2)
                  else
                    let c6 := c_set_len c5 3 in
                    match c_get tt cap c6 with
                    | None => (1, c6)
                    | Some (k3, c7) =>
                        let c7 := c_inc c7 in
                        if c_nused c7 =? PP then unrle_creg f false tt cap PP c7
                        else if negb (k3 =? c_k0 c7) then unrle_creg f false tt cap PP (c_set_k0 c7 k3)
                        else
                          match c_get tt cap c7 with
                          | None => (1, c7)
                          | Some (k4, c8) =>
                              let c8 := c_set_len (c_inc c8) (k4 + 4) in
                              match c_get tt cap c8 with
                              | None => (1, c8)
                              | Some (k5, c9) => unrle_creg f false tt cap PP (c_inc (c_set_k0 c9 k5))
                              end
                          end
                    end
              end
        end).
  Proof. reflexivity. Qed.

  Section Creg.
    Hypothesis SM0 : sm = false.
    Hypothesis TVC0 : TVC q_tt (blk_cap d0).
    Let cap : Z := blk_cap d0.

    Lemma cget : forall crc ch len nu k0 out avail m,
      c_get q_tt cap (CLOC crc ch len nu k0 (pos m) out avail) = Some (sym m, CLOC crc ch len nu k0 (pos (S m)) out avail).
    Proof. intros. rewrite (c_get_src SM0 q_tt cap (CLOC crc ch len nu k0 (pos m) out avail) m TVC0 eq_refl). reflexivity. Qed.

    Lemma c_flush_spec : forall k crc ch nu k0 tp out avail, Z.of_nat k + 1 <= avail ->
      c_flush (S (S k)) (CLOC crc ch (Z.of_nat k + 1) nu k0 tp out avail) =
      (CLOC (crc_list crc (repeat ch k)) ch 1 nu k0 tp (repeat ch k ++ out) (avail - Z.of_nat k), false).
    Proof.
      induction k as [|k IH]; intros crc ch nu k0 tp out avail Hav; rewrite c_flush_S; dsn.
      - replace (avail =? 0) with false by (symmetry; apply Z.eqb_neq; lia). change (Z.of_nat 0 + 1 =? 1) with true. cbv iota.
        cbn [repeat app crc_list fold_left]. rewrite Z.sub_0_r. reflexivity.
      - replace (avail =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (Z.of_nat (S k) + 1 =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (Z.of_nat (S k) + 1 - 1) with (Z.of_nat k + 1) by lia. rewrite IH by lia.
        cbn [repeat]. rewrite crc_list_cons, (repeat_cons k ch), <- app_assoc. cbn [app]. f_equal. f_equal. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma creg_head : forall f (eq1 : bool) (m : nat) crc ch len nu k0 tp out avail,
      (if eq1 return Prop then m = 1%nat else len = Z.of_nat m) -> Z.of_nat m <= avail ->
      unrle_creg (S f) eq1 q_tt cap (Z.of_nat n + 1) (CLOC crc ch len nu k0 tp out avail) =
      (let c1 := CLOC (crc_list crc (repeat ch m)) ch (if eq1 then len else Z.min len 1) nu k0 tp (repeat ch m ++ out) (avail - Z.of_nat m) in
       if Z.of_nat n + 1 <? nu then (1, c1)
       else if nu =? Z.of_nat n + 1 then (0, c_set_len c1 0)
       else
        let c2 := c_set_ch c1 (c_k0 c1) in
        match c_get q_tt cap c2 with
        | None => (1, c2)
        | Some (k1, c3) =>
            let c3 := c_inc c3 in
            if negb (k1 =? c_k0 c3) then unrle_creg f true q_tt cap (Z.of_nat n + 1) (c_set_k0 c3 k1)
            else if c_nused c3 =? Z.of_nat n + 1 then unrle_creg f true q_tt cap (Z.of_nat n + 1) c3
            else
              let c4 := c_set_len c3 2 in
              match c_get q_tt cap c4 with
              | None => (1, c4)
              | Some (k2, c5) =>
                  let c5 := c_inc c5 in
                  if c_nused c5 =? Z.of_nat n + 1 then unrle_creg f false q_tt cap (Z.of_nat n + 1) c5
                  else if negb (k2 =? c_k0 c5) then unrle_creg f false q_tt cap (Z.of_nat n + 1) (c_set_k0 c5 k2)
                  else
                    let c6 := c_set_len c5 3 in
                    match c_get q_tt cap c6 with
                    | None => (1, c6)
                    | Some (k3, c7) =>
                        let c7 := c_inc c7 in
                        if c_nused c7 =? Z.of_nat n + 1 then unrle_creg f false q_tt cap (Z.of_nat n + 1) c7
                        else if negb (k3 =? c_k0 c7) then unrle_creg f false q_tt cap (Z.of_nat n + 1) (c_set_k0 c7 k3)
                        else
                          match c_get q_tt cap c7 with
                          | None => (1, c7)
                          | Some (k4, c8) =>
                              let c8 := c_set_len (c_inc c8) (k4 + 4) in
                              match c_get q_tt cap c8 with
                              | None => (1, c8)
                              | Some (k5, c9) => unrle_creg f false q_tt cap (Z.of_nat n + 1) (c_inc (c_set_k0 c9 k5))
                              end
                          end
                    end
              end
        end).
    Proof.
      intros f eq1 m crc ch len nu k0 tp out avail Hm Hav. rewrite unrle_creg_S. destruct eq1.
      - subst m. dsn. replace (avail =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
        change (repeat ch 1) with [ch]. cbn [app crc_list fold_left]. replace (Z.of_nat 1) with 1 by reflexivity. reflexivity.
      - subst len. destruct m as [|m].
        + dsn. change (0 <? Z.of_nat 0) with false. cbv beta iota zeta. cbn [repeat app crc_list fold_left]. rewrite Z.sub_0_r.
          change (Z.min (Z.of_nat 0) 1) with 0. reflexivity.
        + dsn. replace (0 <? Z.of_nat (S m)) with true by (symmetry; apply Z.ltb_lt; lia).
          rewrite Nat2Z.id. replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia. rewrite c_flush_spec by lia. cbv beta iota zeta. dsn.
          replace (avail - Z.of_nat m =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
          replace (Z.min (Z.of_nat m + 1) 1) with 1 by lia.
          replace (crc_list crc (repeat ch (S m))) with (crc_update (crc_list crc (repeat ch m)) ch) by (cbn [repeat]; rewrite (repeat_cons m ch), crc_list_app; reflexivity).
          cbn [repeat app]. replace (avail - (Z.of_nat m + 1)) with (avail - Z.of_nat m - 1) by lia. reflexivity.
    Qed.

    Lemma creg_loop : forall rs f pre c (eq1 : bool) (m : nat) len crc k0 out avail,
      t = pre ++ rl_enc rs -> RWF rs -> (length rs < f)%nat ->
      (if eq1 return Prop then m = 1%nat else len = Z.of_nat m) ->
      Z.of_nat m + Z.of_nat (length (rl_dec rs)) <= avail ->
      let p := length pre in
      ((p < n)%nat -> k0 = nth p t 0) ->
      exists ch' k0' tp',
        unrle_creg f eq1 q_tt cap (Z.of_nat n + 1) (CLOC crc c len (Z.of_nat p + 1) k0 (pos (S p)) out avail) =
        (0, CLOC (crc_list crc (repeat c m ++ rl_dec rs)) ch' 0 (Z.of_nat n + 1) k0' tp'
                 (rev (rl_dec rs) ++ repeat c m ++ out) (avail - Z.of_nat m - Z.of_nat (length (rl_dec rs)))).
    Proof.
      induction rs as [|[c' L'] rs IH]; intros f pre c eq1 m len crc k0 out avail Ht W Hf Hm Hav p Hk0.
      - cbn [rl_enc] in Ht. rewrite app_nil_r in Ht. assert (Hp : p = n) by (subst p; rewrite <- Hn, Ht; reflexivity).
        destruct f as [|f]; [lia|]. cbn [rl_dec length] in Hav. rewrite (creg_head f eq1 m) by (try exact Hm; lia). cbv beta iota zeta. dsn.
        cbn [rl_dec length rev app]. rewrite app_nil_r, Z.sub_0_r. rewrite Hp. ifF. rewrite Z.eqb_refl.
        exists c, k0, (pos (S n)). reflexivity.
      - cbn [rl_enc] in Ht. cbn [RWF] in W. cps_destruct W as (Hc' & HL' & AD & W). cbn [length] in Hf. cbn [rl_dec] in Hav |- *.
        rewrite length_app, repeat_length in Hav |- *.
        pose proof (t_len pre (rcode c' L') (rl_enc rs) Ht) as TL.
        pose proof (rcode_length c' L' HL') as RL.
        destruct (rcode_hd c' L' ltac:(lia)) as [tl RC].
        assert (Hpn : (p < n)%nat) by (subst p; rewrite RC in TL; cbn [length] in TL; lia).
        specialize (Hk0 Hpn). subst p. rewrite <- (Nat.add_0_r (length pre)) in Hk0.
        rewrite (t_at pre (rcode c' L') (rl_enc rs) 0 Ht ltac:(rewrite RC; cbn; lia)), RC in Hk0. cbn [nth] in Hk0. subst k0.
        set (p := length pre) in *.
        destruct f as [|f]; [lia|]. rewrite (creg_head f eq1 m) by (try exact Hm; lia). cbv beta iota zeta. dsn.
        ifF. ifF. rewrite cget. cbv beta iota zeta. dsn.
        set (crc1 := crc_list crc (repeat c m)). set (out1 := repeat c m ++ out).
        assert (IHk : forall (eq1' : bool) len' k0', (if eq1' return Prop then Z.to_nat L' = 1%nat else len' = Z.of_nat (Z.to_nat L')) ->
          ((p + length (rcode c' L') < n)%nat -> k0' = nth (p + length (rcode c' L')) t 0) ->
          exists ch' k0'' tp',
            unrle_creg f eq1' q_tt cap (Z.of_nat n + 1) (CLOC crc1 c' len' (Z.of_nat (p + length (rcode c' L')) + 1) k0' (pos (S (p + length (rcode c' L')))) out1 (avail - Z.of_nat m)) =
            (0, CLOC (crc_list crc1 (repeat c' (Z.to_nat L') ++ rl_dec rs)) ch' 0 (Z.of_nat n + 1) k0'' tp'
                 (rev (rl_dec rs) ++ repeat c' (Z.to_nat L') ++ out1) (avail - Z.of_nat m - Z.of_nat (Z.to_nat L') - Z.of_nat (length (rl_dec rs))))).
        { intros eq1' len' k0' HM HK. pose proof (IH f (pre ++ rcode c' L') c' eq1' (Z.to_nat L') len' crc1 k0' out1 (avail - Z.of_nat m)) as X.
          rewrite length_app in X. apply X; [rewrite <- app_assoc; exact Ht| exact W| lia| exact HM| lia| exact HK]. }
        assert (FIN : forall ch' k0'' tp',
          (0, CLOC (crc_list crc1 (repeat c' (Z.to_nat L') ++ rl_dec rs)) ch' 0 (Z.of_nat n + 1) k0'' tp'
                 (rev (rl_dec rs) ++ repeat c' (Z.to_nat L') ++ out1) (avail - Z.of_nat m - Z.of_nat (Z.to_nat L') - Z.of_nat (length (rl_dec rs))))
          = (0, CLOC (crc_list crc (repeat c m ++ repeat c' (Z.to_nat L') ++ rl_dec rs)) ch' 0 (Z.of_nat n + 1) k0'' tp'
                 (rev (repeat c' (Z.to_nat L') ++ rl_dec rs) ++ repeat c m ++ out) (avail - Z.of_nat m - Z.of_nat (Z.to_nat L' + length (rl_dec rs))))).
        { intros. subst crc1 out1. rewrite !crc_list_app, rev_app_distr, rev_repeat, <- !app_assoc. f_equal. f_equal; lia. }
        assert (SYM : forall i, (S i < length (rcode c' L'))%nat -> (S i < 4)%nat -> sym (S (p + i)) = c').
        { intros i Hi Hi4. rewrite sym_spec by lia. replace (S (p + i)) with (p + S i)%nat by lia. subst p. rewrite (t_at pre (rcode c' L') (rl_enc rs) (S i) Ht Hi).
          unfold rcode. destruct (Z.ltb_spec L' 4); [apply nth_repeat_lt; unfold rcode in Hi; rewrite (proj2 (Z.ltb_lt _ _)) in Hi by lia; rewrite repeat_length in Hi; lia|].
          unfold rcode in Hi. rewrite (proj2 (Z.ltb_ge _ _)) in Hi by lia. rewrite length_app, repeat_length in Hi. cbn [length] in Hi.
          rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat_lt. lia. }
        assert (NXT : (p + length (rcode c' L') < n)%nat -> sym (p + length (rcode c' L')) = hd_char rs /\ (L' < 4 -> hd_char rs <> c')).
        { intros Hlt. split; [| exact AD]. rewrite sym_spec by exact Hlt.
          destruct rs as [|[c2 L2] rs2]; [cbn [rl_enc length] in TL; rewrite app_nil_r in *; lia|].
          destruct (rl_enc_hd ((c2, L2) :: rs2) W ltac:(discriminate)) as [tl2 E2]. rewrite E2 in Ht.
          subst p. rewrite <- (Nat.add_0_r (length pre + length (rcode c' L'))%nat).
          replace (pre ++ rcode c' L' ++ hd_char ((c2, L2) :: rs2) :: tl2) with ((pre ++ rcode c' L') ++ [hd_char ((c2, L2) :: rs2)] ++ tl2) in Ht by (rewrite <- !app_assoc; reflexivity).
          rewrite <- length_app. rewrite (t_at (pre ++ rcode c' L') [hd_char ((c2, L2) :: rs2)] tl2 0 Ht ltac:(cbn; lia)). reflexivity. }
        destruct (Z.ltb_spec L' 4) as [LT|GE].
        + assert (RCE : rcode c' L' = repeat c' (Z.to_nat L')) by (unfold rcode; rewrite (proj2 (Z.ltb_lt _ _)) by exact LT; reflexivity).
          rewrite RCE, repeat_length in IHk, SYM, NXT, TL.
          assert (L' = 1 \/ L' = 2 \/ L' = 3) as [-> |[-> | ->]] by lia.
          * (* [comment removed for export] *)
            change (Z.to_nat 1) with 1%nat in *.
            destruct (Nat.eq_dec (p + 1) n) as [END|NE].
            -- destruct (Z.eqb_spec (sym (S p)) c') as [EQ|NEQ]; cbn [negb]; [ifT|];
                 [cps_destruct (IHk true (if eq1 then len else Z.min len 1) c' eq_refl ltac:(lia)) as (o & kk & tp & E)
                 | cps_destruct (IHk true (if eq1 then len else Z.min len 1) (sym (S p)) eq_refl ltac:(lia)) as (o & kk & tp & E)];
                 exists o, kk, tp; replace (Z.of_nat p + 1 + 1) with (Z.of_nat (p + 1) + 1) by lia; replace (S (S p)) with (S (p + 1)) by lia;
                 rewrite E; apply FIN.
            -- destruct (NXT ltac:(lia)) as [NX1 NX2]. replace (S p) with (p + 1)%nat by lia. rewrite NX1. ifT.
               cps_destruct (IHk true (if eq1 then len else Z.min len 1) (hd_char rs) eq_refl ltac:(intros; rewrite <- sym_spec by lia; rewrite <- NX1; reflexivity)) as (o & kk & tp & E). exists o, kk, tp.
               replace (Z.of_nat p + 1 + 1) with (Z.of_nat (p + 1) + 1) by lia. replace (S (S p)) with (S (p + 1)) by lia.
               rewrite E. apply FIN.
          * change (Z.to_nat 2) with 2%nat in *. change (Z.of_nat 2) with 2 in IHk.
            pose proof (SYM 0%nat ltac:(lia) ltac:(lia)) as S0. rewrite Nat.add_0_r in S0. rewrite S0, Z.eqb_refl. cbn [negb]. ifF. rewrite cget. cbv beta iota zeta. dsn.
            destruct (Nat.eq_dec (p + 2) n) as [END|NE].
            -- ifT. cps_destruct (IHk false 2 c' eq_refl ltac:(lia)) as (o & kk & tp & E). exists o, kk, tp.
               replace (Z.of_nat p + 1 + 1 + 1) with (Z.of_nat (p + 2) + 1) by lia. replace (S (S (S p))) with (S (p + 2)) by lia.
               rewrite E. apply FIN.
            -- ifF. destruct (NXT ltac:(lia)) as [NX1 NX2]. replace (S (S p)) with (p + 2)%nat by lia. rewrite NX1. ifT.
               cps_destruct (IHk false 2 (hd_char rs) eq_refl ltac:(intros; rewrite <- sym_spec by lia; rewrite <- NX1; reflexivity)) as (o & kk & tp & E). exists o, kk, tp.
               replace (Z.of_nat p + 1 + 1 + 1) with (Z.of_nat (p + 2) + 1) by lia. replace (S (p + 2 + 1))%nat with (S (S (p + 2)))%nat by lia.
               replace (S (S (S p))) with (S (p + 2)) by lia.
               rewrite E. apply FIN.
          * change (Z.to_nat 3) with 3%nat in *. change (Z.of_nat 3) with 3 in IHk.
            pose proof (SYM 0%nat ltac:(lia) ltac:(lia)) as S0. rewrite Nat.add_0_r in S0. rewrite S0, Z.eqb_refl. cbn [negb]. ifF. rewrite cget. cbv beta iota zeta. dsn.
            replace (S (S p)) with (S (p + 1)) by lia. ifF. rewrite (SYM 1%nat) by lia. rewrite Z.eqb_refl. cbn [negb]. rewrite cget. cbv beta iota zeta. dsn.
            destruct (Nat.eq_dec (p + 3) n) as [END|NE].
            -- ifT. cps_destruct (IHk false 3 c' eq_refl ltac:(lia)) as (o & kk & tp & E). exists o, kk, tp.
               replace (Z.of_nat p + 1 + 1 + 1 + 1) with (Z.of_nat (p + 3) + 1) by lia. replace (S (S (S (p + 1)))) with (S (p + 3)) by lia.
               rewrite E. apply FIN.
            -- ifF. destruct (NXT ltac:(lia)) as [NX1 NX2]. replace (S (S (p + 1))) with (p + 3)%nat by lia. rewrite NX1. ifT.
               cps_destruct (IHk false 3 (hd_char rs) eq_refl ltac:(intros; rewrite <- sym_spec by lia; rewrite <- NX1; reflexivity)) as (o & kk & tp & E). exists o, kk, tp.
               replace (Z.of_nat p + 1 + 1 + 1 + 1) with (Z.of_nat (p + 3) + 1) by lia. replace (S (S (S (p + 1)))) with (S (p + 3)) by lia.
               rewrite E. apply FIN.
        + assert (RCE : rcode c' L' = repeat c' 4 ++ [L' - 4]) by (unfold rcode; rewrite (proj2 (Z.ltb_ge _ _)) by exact GE; reflexivity).
          assert (RLN : length (rcode c' L') = 5%nat) by (rewrite RCE; reflexivity).
          rewrite RLN in IHk, SYM, NXT, TL.
          pose proof (SYM 0%nat ltac:(lia) ltac:(lia)) as S0. rewrite Nat.add_0_r in S0. rewrite S0, Z.eqb_refl. cbn [negb]. ifF. rewrite cget. cbv beta iota zeta. dsn.
          replace (S (S p)) with (S (p + 1)) by lia. ifF. rewrite (SYM 1%nat) by lia. rewrite Z.eqb_refl. cbn [negb]. rewrite cget. cbv beta iota zeta. dsn.
          replace (S (S (p + 1))) with (S (p + 2)) by lia. ifF. rewrite (SYM 2%nat) by lia. rewrite Z.eqb_refl. cbn [negb]. rewrite cget. cbv beta iota zeta. dsn.
          assert (CNT : sym (S (p + 3)) = L' - 4).
          { rewrite sym_spec by lia. replace (S (p + 3)) with (p + 4)%nat by lia. subst p. rewrite (t_at pre (rcode c' L') (rl_enc rs) 4 Ht ltac:(rewrite RLN; lia)), RCE. reflexivity. }
          replace (S (S (p + 2))) with (S (p + 3)) by lia. rewrite CNT. rewrite cget. cbv beta iota zeta. dsn.
          replace (S (S (p + 3))) with (S (p + 4)) by lia.
          cps_destruct (IHk false (L' - 4 + 4) (sym (S (p + 4))) ltac:(cbv iota; lia) ltac:(intros; rewrite sym_spec by lia; f_equal; lia)) as (o & kk & tp & E). exists o, kk, tp.
          replace (Z.of_nat p + 1 + 1 + 1 + 1 + 1 + 1) with (Z.of_nat (p + 5) + 1) by lia. replace (S (S (p + 4))) with (S (p + 5)) by lia.
          rewrite E. apply FIN.
    Qed.

    Lemma creg_all : forall runs sout avail tout, RWF runs -> t = rl_enc runs -> Z.of_nat (length (rl_dec runs)) <= avail ->
      q_nused = 1 -> q_k0 = nth 0 t 0 -> q_tPos = pos 1 -> q_out_len = 0 ->
      exists och' k0' tp',
        unRLE d0 (SS sout avail tout) =
        (0, DD och' 0 (crc_list q_cbcrc (rl_dec runs)) (Z.of_nat n + 1) k0' tp',
            SS (rev (rl_dec runs) ++ sout) (avail - Z.of_nat (length (rl_dec runs))) (tout + Z.of_nat (length (rl_dec runs)))).
    Proof.
      intros runs sout avail tout W Ht Hav N1 K0 TP OL. unfold unRLE.
      rewrite (TV_small d0 TV0), (TV_rand d0 TV0), SM0. change (false || negb (0 =? 0))%bool with false. cbv iota. fold cap.
      unfold d0. dsn. rewrite Hsv.
      pose proof (rl_enc_length_ge runs W) as LR. rewrite <- Ht, Hn in LR.
      rewrite N1, TP, OL. replace (Z.to_nat (Z.of_nat n + 1 + 3 - 1)) with (S (S (S n))) by lia.
      cps_destruct (creg_loop runs (S (S (S n))) [] q_out_ch false 0 0 q_cbcrc q_k0 [] avail Ht W ltac:(cbn; lia) eq_refl ltac:(cbn; lia)
                  ltac:(cbn; intros; exact K0)) as (o & kk & tp & E).
      cbn [length Z.of_nat repeat app] in E. rewrite Z.add_0_l, Z.sub_0_r, app_nil_r in E. rewrite E. dsn. change (0 =? 0) with true. cbv iota.
      exists o, kk, tp. f_equal. f_equal. lia.
    Qed.
  End Creg.

  Lemma plain_all : forall runs sout avail tout, RWF runs -> t = rl_enc runs -> Z.of_nat (length (rl_dec runs)) <= avail ->
    q_nused = 1 -> q_k0 = nth 0 t 0 -> q_tPos = pos 1 -> q_out_len = 0 -> sm = true ->
    exists och' k0' tp',
      unRLE d0 (SS sout avail tout) =
      (0, DD och' 0 (crc_list q_cbcrc (rl_dec runs)) (Z.of_nat n + 1) k0' tp',
          SS (rev (rl_dec runs) ++ sout) (avail - Z.of_nat (length (rl_dec runs))) (tout + Z.of_nat (length (rl_dec runs)))).
  Proof.
    intros runs sout avail tout W Ht Hav N1 K0 TP OL SM. unfold unRLE.
    rewrite (TV_small d0 TV0), SM. cbv iota. unfold d0. dsn. rewrite Hsv.
    pose proof (rl_enc_length_ge runs W) as LR. rewrite <- Ht, Hn in LR.
    rewrite N1, TP, OL. replace (Z.to_nat (Z.of_nat n + 1 + 3 - 1)) with (S (S (S n))) by lia.
    cps_destruct (plain_loop runs (S (S (S n))) [] q_out_ch 0 q_cbcrc q_k0 sout avail tout Ht W ltac:(cbn; lia) ltac:(cbn; lia)
                ltac:(cbn; intros; exact K0)) as (o & kk & tp & E).
    cbn [length Z.of_nat repeat app] in E. rewrite Z.add_0_l, Z.add_0_r, Z.sub_0_r in E.
    exists o, kk, tp. exact E.
  Qed.

  (* [comment removed for export] *)
  Theorem unRLE_sec : forall data sout avail tout, rlcodes t data -> Z.of_nat (length data) <= avail ->
    q_nused = 1 -> q_k0 = nth 0 t 0 -> q_tPos = pos 1 -> q_out_len = 0 ->
    (sm = false -> TVC q_tt (blk_cap d0)) ->
    exists och' k0' tp',
      unRLE d0 (SS sout avail tout) =
      (0, DD och' 0 (crc_list q_cbcrc data) (Z.of_nat n + 1) k0' tp',
          SS (rev data ++ sout) (avail - Z.of_nat (length data)) (tout + Z.of_nat (length data))).
  Proof.
    (intros data sout avail tout; cps_intros (runs & W & Ht & ->); intros Hav N1 K0 TP OL TC).
    destruct (Bool.bool_dec sm true) as [SM|SM]; [| apply Bool.not_true_is_false in SM].
    - apply plain_all; auto.
    - apply (creg_all SM (TC SM)); auto.
  Qed.
End UnRLE.

(* [comment removed for export] *)
Theorem unRLE_rlcodes : forall (t : list Z) (sm : bool) (pos sym : nat -> Z) (TV : dst -> Prop) (TVC : zarr -> Z -> Prop),
  (1 <= length t)%nat ->
  (forall m, (m < length t)%nat -> sym m = nth m t 0) ->
  (forall d, TV d -> smallb d = sm) ->
  (forall d, TV d -> d_rand d = 0) ->
  (forall d d', TV d -> d_small d' = d_small d -> d_rand d' = d_rand d -> d_bs100k d' = d_bs100k d -> d_tt d' = d_tt d ->
     d_cftab d' = d_cftab d -> d_ll16 d' = d_ll16 d -> d_ll4 d' = d_ll4 d -> TV d') ->
  (forall d m, TV d -> d_tPos d = pos m -> get_sym d = Some (sym m, d_set_tPos d (pos (S m)))) ->
  (forall d, TV d -> sm = false -> TVC (d_tt d) (blk_cap d)) ->
  (sm = false -> forall tt cap c m, TVC tt cap -> c_tPos c = pos m ->
     c_get tt cap c = Some (sym m, CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c) (c_k0 c) (pos (S m)) (c_out c) (c_avail c))) ->
  forall d s data,
  TV d -> sv_nblock (d_sv d) = Z.of_nat (length t) -> d_nused d = 1 -> d_k0 d = nth 0 t 0 -> d_tPos d = pos 1%nat -> d_out_len d = 0 ->
  rlcodes t data -> Z.of_nat (length data) <= s_avail_out s ->
  exists d'',
    unRLE d s = (0, d'', DSTRM (s_in s) (rev data ++ s_out s) (s_avail_out s - Z.of_nat (length data)) (s_tin s) (s_tout s + Z.of_nat (length data))) /\
    d_nused d'' = sv_nblock (d_sv d) + 1 /\ d_out_len d'' = 0 /\ d_cbcrc d'' = crc_list (d_cbcrc d) data /\
    d_state d'' = d_state d /\
    d_rand d'' = d_rand d /\
    d_rNToGo d'' = d_rNToGo d /\
    d_rTPos d'' = d_rTPos d /\
    d_bsBuff d'' = d_bsBuff d /\
    d_bsLive d'' = d_bsLive d /\
    d_bs100k d'' = d_bs100k d /\
    d_small d'' = d_small d /\
    d_blockNo d'' = d_blockNo d /\
    d_verb d'' = d_verb d /\
    d_origPtr d'' = d_origPtr d /\
    d_unzftab d'' = d_unzftab d /\
    d_cftab d'' = d_cftab d /\
    d_cftabCopy d'' = d_cftabCopy d /\
    d_tt d'' = d_tt d /\
    d_ll16 d'' = d_ll16 d /\
    d_ll4 d'' = d_ll4 d /\
    d_tt_al d'' = d_tt_al d /\
    d_ll_al d'' = d_ll_al d /\
    d_sbcrc d'' = d_sbcrc d /\
    d_sccrc d'' = d_sccrc d /\
    d_cccrc d'' = d_cccrc d /\
    d_nInUse d'' = d_nInUse d /\
    d_inUse d'' = d_inUse d /\
    d_inUse16 d'' = d_inUse16 d /\
    d_s2u d'' = d_s2u d /\
    d_mtfa d'' = d_mtfa d /\
    d_mtfbase d'' = d_mtfbase d /\
    d_sel d'' = d_sel d /\
    d_selMtf d'' = d_selMtf d /\
    d_len d'' = d_len d /\
    d_limit d'' = d_limit d /\
    d_base d'' = d_base d /\
    d_perm d'' = d_perm d /\
    d_minLens d'' = d_minLens d /\
    d_sv d'' = d_sv d.
Proof.
  intros t sm pos sym TV TVC Hn1 SYS TS TR TF GS TT CG d s data TVd SV N1 K0 TP OL RC AV.
  destruct d as [q_state q_out_ch q_out_len q_rand q_rNToGo q_rTPos q_bsBuff q_bsLive q_bs100k q_small q_blockNo q_verb q_origPtr q_tPos q_k0 q_unzftab q_nused q_cftab q_cftabCopy q_tt q_ll16 q_ll4 q_tt_al q_ll_al q_sbcrc q_sccrc q_cbcrc q_cccrc q_nInUse q_inUse q_inUse16 q_s2u q_mtfa q_mtfbase q_sel q_selMtf q_len q_limit q_base q_perm q_minLens q_sv]. destruct s as [sin sout avail stin stout].
  cbn [d_sv d_nused d_k0 d_tPos d_out_len d_cbcrc s_in s_out s_avail_out s_tin s_tout] in *.
  cps_destruct (unRLE_sec (length t) t sm pos sym TV TVC eq_refl Hn1 SYS TS TR TF GS CG q_state q_out_ch q_out_len q_rand q_rNToGo q_rTPos q_bsBuff q_bsLive q_bs100k q_small q_blockNo q_verb q_origPtr q_tPos q_k0 q_unzftab q_nused q_cftab q_cftabCopy q_tt q_ll16 q_ll4 q_tt_al q_ll_al q_sbcrc q_sccrc q_cbcrc q_cccrc q_nInUse q_inUse q_inUse16 q_s2u q_mtfa q_mtfbase q_sel q_selMtf q_len q_limit q_base q_perm q_minLens q_sv TVd SV sin stin data sout avail stout RC AV N1 K0 TP OL
              ltac:(intros SM; exact (TT _ TVd SM))) as (o & kk & tp & E).
  rewrite E. eexists. split; [reflexivity|]. cbn. rewrite SV. repeat split; reflexivity.
Qed.
End BzR1d.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2Theory OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR2D OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR1a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR1b.BzR1d.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem unRLE_block : forall t pi rho, bwt t pi rho -> forall sm d s data,
  TV t pi rho sm d ->
  sv_nblock (d_sv d) = Z.of_nat (length t) -> d_nused d = 1 -> d_k0 d = sym t pi rho sm 0 -> d_tPos d = pos t pi rho sm 1 -> d_out_len d = 0 ->
  rlcodes t data -> Z.of_nat (length data) <= s_avail_out s ->
  exists d'',
    unRLE d s = (0, d'', DSTRM (s_in s) (rev data ++ s_out s) (s_avail_out s - Z.of_nat (length data)) (s_tin s) (s_tout s + Z.of_nat (length data))) /\
    d_nused d'' = sv_nblock (d_sv d) + 1 /\ d_out_len d'' = 0 /\ d_cbcrc d'' = crc_list (d_cbcrc d) data /\
    d_state d'' = d_state d /\ d_rand d'' = d_rand d /\ d_rNToGo d'' = d_rNToGo d /\ d_rTPos d'' = d_rTPos d /\
    d_bsBuff d'' = d_bsBuff d /\ d_bsLive d'' = d_bsLive d /\ d_bs100k d'' = d_bs100k d /\ d_small d'' = d_small d /\
    d_blockNo d'' = d_blockNo d /\ d_verb d'' = d_verb d /\ d_origPtr d'' = d_origPtr d /\ d_unzftab d'' = d_unzftab d /\
    d_cftab d'' = d_cftab d /\ d_cftabCopy d'' = d_cftabCopy d /\ d_tt d'' = d_tt d /\ d_ll16 d'' = d_ll16 d /\ d_ll4 d'' = d_ll4 d /\
    d_tt_al d'' = d_tt_al d /\ d_ll_al d'' = d_ll_al d /\ d_sbcrc d'' = d_sbcrc d /\ d_sccrc d'' = d_sccrc d /\ d_cccrc d'' = d_cccrc d /\
    d_nInUse d'' = d_nInUse d /\ d_inUse d'' = d_inUse d /\ d_inUse16 d'' = d_inUse16 d /\ d_s2u d'' = d_s2u d /\
    d_mtfa d'' = d_mtfa d /\ d_mtfbase d'' = d_mtfbase d /\ d_sel d'' = d_sel d /\ d_selMtf d'' = d_selMtf d /\ d_len d'' = d_len d /\
    d_limit d'' = d_limit d /\ d_base d'' = d_base d /\ d_perm d'' = d_perm d /\ d_minLens d'' = d_minLens d /\ d_sv d'' = d_sv d.
Proof.
  intros t pi rho HB sm d s data TVd SV N1 K0 TP OL RC AV.
  pose proof (bwt_n t pi rho HB) as Hn.
  apply (unRLE_rlcodes t sm (pos t pi rho sm) (sym t pi rho sm) (TV t pi rho sm) (TVC t pi)); try assumption.
  - intros m Hm. apply (sym_spec t pi rho HB). exact Hm.
  - intros d0 H. apply (TV_small t pi rho) in H. exact H.
  - intros d0 H. apply (TV_rand t pi rho) in H. exact H.
  - intros d0 d' H. apply (TV_frame t pi rho). exact H.
  - intros d0 m H E. apply (get_sym_src t pi rho HB); assumption.
  - intros d0 H E. subst sm. apply (TV_TVC t pi rho). exact H.
  - intros E tt cap c m H P. subst sm. apply (c_get_src t pi rho HB); assumption.
  - rewrite K0. apply (sym_spec t pi rho HB). lia.
Qed.
