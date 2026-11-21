(** * ZRStrictSupply — kraft facts at the three flush builds, and the
      strict-guard discharge (GAP7 strict supply, stage 2/W3).

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-21; strict-freeze
    round 3, pin Gap7Strict ).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    Per-kind instances of [ZRKraftEq.build_tree_kraft_eq] at the exact
    call shapes the dyn-arm chain builds — TK_L and TK_D via the
    [inst_L]/[inst_D] destruct pattern (heap bounded by [bt_sized]),
    TK_BL via the [bl_cl_pack] parked route (heap bounded by the census,
    which is what makes [4 (hlen-1) < 2^7] true).  The dead-tail facts
    ride along for the 19-vector extension. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes SendGo Kraft15 KraftTree KraftAdjust.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus2 BtCensus4 BtCensus5 BtPass1 BtPass2 BtItem6 BtItem6b
  BtBlSide BtClPack BtSized BtTerm BuildTree.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRKraftEq.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** TK_L: heap bounded by [bt_sized], overflow premise at 2^15 *)

Lemma kraft_L : forall s,
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  (kraft_sum (SendGo.tree_lens (ts_trees (build_tree TK_L s) TK_L)
       (ts_maxcode (build_tree TK_L s) TK_L)) 15
   = 32768)%nat
  /\ (forall len,
        In len (SendGo.tree_lens (ts_trees (build_tree TK_L s) TK_L)
                  (ts_maxcode (build_tree TK_L s) TK_L)) ->
        (len <= 15)%nat).
Proof.
  intros s Hblc.
  assert (HelL : 3 <= sd_elems TK_L <= L_CODES)
    by (change (sd_elems TK_L) with L_CODES; unfold L_CODES; lia).
  assert (HM : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_L)
              (ts_trees s TK_L) (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_force2 3%nat (sd_stree TK_L) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  assert (Hsz : 2 <= hlen1 <= L_CODES)
    by (eapply bt_sized; try eassumption; lia).
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems TK_L |}) as [stf|] eqn:Eloop.
  2:{ exfalso.
      eapply (bt_loop_terminates (Z.to_nat HEAP_SIZE)); [| | exact Eloop].
      - cbn [b_hlen]. lia.
      - cbn [b_hlen].
        rewrite Z2Nat.id by (unfold HEAP_SIZE, L_CODES; lia).
        unfold HEAP_SIZE, L_CODES in *. lia. }
  assert (HK : 4 * (hlen1 - 1) < 2 ^ sd_max_length TK_L)
    by (change (sd_max_length TK_L) with 15;
        change (2 ^ 15) with 32768;
        unfold L_CODES in Hsz; lia).
  destruct (build_tree_kraft_eq TK_L s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
              HelL HM HK Hblc E0 E2 Eloop)
    as (Emc & Hkr & Hub & _).
  rewrite Emc.
  change (Z.to_nat (sd_max_length TK_L)) with 15%nat in Hkr, Hub.
  change (2 ^ 15)%nat with 32768%nat in Hkr.
  split; [exact Hkr | exact Hub].
Qed.

(** ** TK_D: same route (D_CODES fits the same bounds) *)

Lemma kraft_D : forall s,
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  (kraft_sum (SendGo.tree_lens (ts_trees (build_tree TK_D s) TK_D)
       (ts_maxcode (build_tree TK_D s) TK_D)) 15
   = 32768)%nat
  /\ (forall len,
        In len (SendGo.tree_lens (ts_trees (build_tree TK_D s) TK_D)
                  (ts_maxcode (build_tree TK_D s) TK_D)) ->
        (len <= 15)%nat).
Proof.
  intros s Hblc.
  assert (HelL : 3 <= sd_elems TK_D <= L_CODES)
    by (change (sd_elems TK_D) with D_CODES; unfold D_CODES, L_CODES; lia).
  assert (HM : 1 <= sd_max_length TK_D <= 15)
    by (change (sd_max_length TK_D) with 15; lia).
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_D)
              (ts_trees s TK_D) (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_force2 3%nat (sd_stree TK_D) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  assert (Hsz : 2 <= hlen1 <= L_CODES)
    by (eapply bt_sized; try eassumption; lia).
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems TK_D |}) as [stf|] eqn:Eloop.
  2:{ exfalso.
      eapply (bt_loop_terminates (Z.to_nat HEAP_SIZE)); [| | exact Eloop].
      - cbn [b_hlen]. lia.
      - cbn [b_hlen].
        rewrite Z2Nat.id by (unfold HEAP_SIZE, L_CODES; lia).
        unfold HEAP_SIZE, L_CODES in *. lia. }
  assert (HK : 4 * (hlen1 - 1) < 2 ^ sd_max_length TK_D)
    by (change (sd_max_length TK_D) with 15;
        change (2 ^ 15) with 32768;
        unfold L_CODES in Hsz; lia).
  destruct (build_tree_kraft_eq TK_D s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
              HelL HM HK Hblc E0 E2 Eloop)
    as (Emc & Hkr & Hub & _).
  rewrite Emc.
  change (Z.to_nat (sd_max_length TK_D)) with 15%nat in Hkr, Hub.
  change (2 ^ 15)%nat with 32768%nat in Hkr.
  split; [exact Hkr | exact Hub].
Qed.

(** ** TK_BL: the parked route bounds the heap by the SMALL alphabet
    (mirrors [BtClPack.bl_cl_pack]'s opening), which is what makes the
    overflow premise true at [2^7].  The dead tail rides along for the
    19-vector extension. *)

Lemma kraft_BL : forall s,
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  (kraft_sum (SendGo.tree_lens (ts_trees (build_tree TK_BL s) TK_BL)
       (ts_maxcode (build_tree TK_BL s) TK_BL)) 7
   = 128)%nat
  /\ (forall len,
        In len (SendGo.tree_lens (ts_trees (build_tree TK_BL s) TK_BL)
                  (ts_maxcode (build_tree TK_BL s) TK_BL)) ->
        (len <= 7)%nat)
  /\ -1 <= ts_maxcode (build_tree TK_BL s) TK_BL <= 18
  /\ (forall i, ts_maxcode (build_tree TK_BL s) TK_BL < i <= 18 ->
      t_len (ts_trees (build_tree TK_BL s) TK_BL) i = 0).
Proof.
  intros s Hblc.
  assert (Hel : sd_elems TK_BL = 19) by reflexivity.
  assert (Hml : sd_max_length TK_BL = 7) by reflexivity.
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL)
              (ts_trees s TK_BL) (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems TK_BL |}) as [stf|] eqn:Eloop.
  2:{ exfalso.
      pose proof (bt_sized TK_BL s t0 hp0 dep0 hlen0 maxc0
                    t1 hp1 dep1 hlen1 maxc1 ol1 sl1
                    ltac:(rewrite Hel; lia) ltac:(rewrite Hel; unfold L_CODES; lia)
                    E0 E2) as Hsz.
      eapply (bt_loop_terminates (Z.to_nat HEAP_SIZE)); [| | exact Eloop].
      - cbn [b_hlen]. lia.
      - cbn [b_hlen].
        rewrite Z2Nat.id by (unfold HEAP_SIZE, L_CODES; lia).
        unfold HEAP_SIZE, L_CODES in *. lia. }
  destruct (build_tree_parked TK_BL s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf ltac:(rewrite Hel; unfold L_CODES; lia)
              E0 E2 eq_refl Eloop)
    as [Hpk [Hout1 [Hsz [Hcen Hfr0]]]].
  assert (Hh19 : hlen1 <= 19).
  { pose proof (io_total _ _ _ _ _ Hout1) as Ht.
    unfold live_total in Ht.
    pose proof (wsum_ind_ub (fun s' => live_b t1 maxc1 s') 0
                  (Z.to_nat (sd_elems TK_BL))) as HB.
    cbn beta in HB.
    rewrite Hel in Ht, HB.
    change (Z.of_nat (Z.to_nat 19)) with 19 in HB. lia. }
  assert (HK : 4 * (hlen1 - 1) < 2 ^ sd_max_length TK_BL)
    by (rewrite Hml; replace (2 ^ 7) with 128 by reflexivity; lia).
  assert (Hmax : -1 <= maxc1 < 19)
    by (pose proof (io_maxc _ _ _ _ _ Hout1) as H; rewrite Hel in H; lia).
  destruct (build_tree_kraft_eq TK_BL s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
              ltac:(rewrite Hel; unfold L_CODES; lia)
              ltac:(rewrite Hml; lia)
              HK Hblc E0 E2 Eloop)
    as (Emc & Hkr & Hub & _).
  destruct (build_tree_out TK_BL s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
              ltac:(rewrite Hel; unfold L_CODES; lia)
              ltac:(rewrite Hml; lia)
              HK Hblc E0 E2 Eloop)
    as (_ & _ & _ & _ & Gdead & Ggap & _).
  rewrite Hel in Gdead, Ggap.
  rewrite Emc.
  change (Z.to_nat (sd_max_length TK_BL)) with 7%nat in Hkr, Hub.
  change (2 ^ 7)%nat with 128%nat in Hkr.
  split; [exact Hkr|].
  split; [exact Hub|].
  split; [lia|].
  intros i Hi. apply Gdead; [lia|]. apply Ggap. lia.
Qed.

Print Assumptions kraft_L.
Print Assumptions kraft_D.
Print Assumptions kraft_BL.

(* ==========================================================================
   The strict-guard discharge at the flush state: given the frozen
   characterization statement (g1's proof pending, taken as premise) and
   the frozen ENOUGH residue, the five facts the amended
   [dyn_arm_dec_blk] asks for.
   ========================================================================== *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import G3DynA Gap7Strict.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(** local copy of G3DynB's [tree_lens_ext] (importing G3DynB here would
    couple the supply below the site it feeds) *)
Lemma tree_lens_ext_s : forall t t' maxc,
  (forall i, 0 <= i <= maxc -> t_len t' i = t_len t i) ->
  SendGo.tree_lens t' maxc = SendGo.tree_lens t maxc.
Proof.
  intros t t' maxc He.
  unfold SendGo.tree_lens.
  apply map_ext_in.
  intros a Ha. apply in_seq in Ha.
  rewrite He; [reflexivity|lia].
Qed.

Theorem dyn_strict_guards : forall ts0,
  build_accepts_of_kraft_STMT ->
  EnoughFits_STMT ->
  t_freq (ts_trees ts0 TK_L) END_BLOCK <> 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts0 b = 0) ->
  (forall i, 0 <= i < 19 -> t_freq (ts_trees ts0 TK_BL) i = 0) ->
  (forall i, 0 <= t_len (ts_trees ts0 TK_BL) i) ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (build_tree TK_L ts0) b = 0) ->
  (forall i, 0 <= t_len (ts_trees (build_tree TK_L ts0) TK_L) i) ->
  (forall b, b < 0 \/ 15 < b ->
   ts_blcount (build_tree TK_D (build_tree TK_L ts0)) b = 0) ->
  (forall i, 0 <= t_len
     (ts_trees (build_tree TK_D (build_tree TK_L ts0)) TK_D) i) ->
  1 <= ts_maxcode (build_tree TK_D (build_tree TK_L ts0)) TK_D ->
  (forall b, b < 0 \/ 15 < b ->
   ts_blcount
     (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0)))) b = 0) ->
  (forall i, 0 <= t_len
     (ts_trees (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0))))
        TK_BL) i) ->
  build_accepts_b CT_CODES
    (SendGo.tree_lens
       (ts_trees (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0))))
          TK_BL) 18) 7 = true
  /\ build_accepts_b CT_LENS
       (SendGo.tree_lens
          (ts_trees
             (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0))))
             TK_L)
          (ts_maxcode (build_tree TK_L ts0) TK_L)) 9 = true
  /\ build_accepts_b CT_DISTS
       (SendGo.tree_lens
          (ts_trees
             (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0))))
             TK_D)
          (ts_maxcode (build_tree TK_D (build_tree TK_L ts0)) TK_D)) 6 = true
  /\ ts_maxcode (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0))))
       TK_L + 1 <= 286
  /\ ts_maxcode (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts0))))
       TK_D + 1 <= 30.
Proof.
  intros ts0 HB EF Heob Hblc0 Hblf0 Hbln0 HR1L HR2L HR1D HR2D HR3D HR1B HR2B.
  set (s1L := build_tree TK_L ts0) in *.
  set (s1D := build_tree TK_D s1L) in *.
  set (s2 := snd (build_bl_tree s1D)) in *.
  (* ---- the L and D builds ---- *)
  destruct (inst_L ts0 Hblc0 Heob HR1L HR2L)
    as (LmcR & LVL & Lrng & Leob & Llive & Lcodes).
  cbv zeta in LmcR, LVL, Lrng, Leob, Llive, Lcodes.
  fold s1L in LmcR, LVL, Lrng, Leob, Llive, Lcodes.
  destruct (inst_D s1L HR1L HR1D HR2D HR3D)
    as (DmcR & DVL & Drng & Dlive & Dcodes).
  cbv zeta in DmcR, DVL, Drng, Dlive, Dcodes.
  fold s1D in DmcR, DVL, Drng, Dlive, Dcodes.
  (* frames *)
  assert (FL_D : ts_trees s1D TK_L = ts_trees s1L TK_L)
    by (apply build_tree_tree_other; unfold TK_L, TK_D; lia).
  assert (FLmc_D : ts_maxcode s1D TK_L = ts_maxcode s1L TK_L)
    by (apply build_tree_maxcode_other; unfold TK_L, TK_D; lia).
  assert (FBL_L : ts_trees s1L TK_BL = ts_trees ts0 TK_BL)
    by (apply build_tree_tree_other; unfold TK_L, TK_BL; lia).
  assert (FBL_D : ts_trees s1D TK_BL = ts_trees s1L TK_BL)
    by (apply build_tree_tree_other; unfold TK_D, TK_BL; lia).
  (* ---- the BL pipeline ---- *)
  destruct (inst_BL s1D HR1D
              ltac:(intros i Hi; rewrite FBL_D, FBL_L;
                    exact (Hblf0 i Hi))
              ltac:(intro i; rewrite FBL_D, FBL_L; apply Hbln0)
              ltac:(rewrite FLmc_D; exact LmcR)
              DmcR
              ltac:(intro i; rewrite FL_D; apply HR2L)
              HR2D
              ltac:(intros i Hi; rewrite FL_D; apply Lrng;
                    rewrite FLmc_D in Hi; exact Hi)
              ltac:(intros i Hi; apply Drng; exact Hi)
              ltac:(rewrite FL_D; exact Leob)
              HR1B HR2B)
    as (Bmbi & Bcllen & BV7 & Bfits & Btail & Bpack & BbitsL & BbitsD
        & BgL & BgD & BmL & BmD & BLnn & BLrng & BDnn & BDrng
        & BLcode & BLlen & BDcode & BDlen & Bsb & Bsn & Bbw).
  cbv zeta in Bmbi, Bcllen, BV7, Bfits, Btail, Bpack, BbitsL, BbitsD,
    BgL, BgD, BmL, BmD, BLnn, BLrng, BDnn, BDrng,
    BLcode, BLlen, BDcode, BDlen, Bsb, Bsn, Bbw.
  fold s2 in Bmbi, Bcllen, BV7, Bfits, Btail, Bpack, BbitsL, BbitsD,
    BgL, BgD, BmL, BmD, BLnn, BLrng, BDnn, BDrng,
    BLcode, BLlen, BDcode, BDlen, Bsb, Bsn, Bbw.
  (* the two maxcode caps *)
  assert (A4 : ts_maxcode s2 TK_L + 1 <= 286)
    by (rewrite BmL, FLmc_D; lia).
  assert (A5 : ts_maxcode s2 TK_D + 1 <= 30)
    by (rewrite BmD; lia).
  (* ---- A2: the L list ---- *)
  destruct (kraft_L ts0 Hblc0) as (KL & KLub).
  fold s1L in KL, KLub.
  assert (EllL : SendGo.tree_lens (ts_trees s2 TK_L) (ts_maxcode s1L TK_L)
                 = SendGo.tree_lens (ts_trees s1L TK_L)
                     (ts_maxcode s1L TK_L)).
  { apply tree_lens_ext_s.
    intros i Hi.
    rewrite BLlen by (rewrite FLmc_D; lia).
    rewrite FL_D. reflexivity. }
  assert (A2 : build_accepts_b CT_LENS
                 (SendGo.tree_lens (ts_trees s2 TK_L) (ts_maxcode s1L TK_L))
                 9 = true).
  { apply (HB CT_LENS
             (SendGo.tree_lens (ts_trees s2 TK_L) (ts_maxcode s1L TK_L)) 9).
    - right; left.
      split; [reflexivity|].
      split.
      { rewrite tree_lens_length. lia. }
      split; [reflexivity|].
      split.
      { left. rewrite EllL.
        change (2 ^ 15)%nat with 32768%nat. exact KL. }
      { intros len Hin. rewrite EllL in Hin. exact (KLub len Hin). }
    - intros c st Hpre n t.
      refine (EF CT_LENS _ 9 c st _ _ Hpre n t).
      + right; left.
        split; [reflexivity|].
        split; [rewrite tree_lens_length; lia | reflexivity].
      + (* lens_capped, from the kraft export's In-bound *)
        intros len Hin. rewrite EllL in Hin. exact (KLub len Hin). }
  (* ---- A3: the D list ---- *)
  destruct (kraft_D s1L HR1L) as (KD & KDub).
  fold s1D in KD, KDub.
  assert (EllD : SendGo.tree_lens (ts_trees s2 TK_D) (ts_maxcode s1D TK_D)
                 = SendGo.tree_lens (ts_trees s1D TK_D)
                     (ts_maxcode s1D TK_D)).
  { apply tree_lens_ext_s.
    intros i Hi.
    rewrite BDlen by lia. reflexivity. }
  assert (A3 : build_accepts_b CT_DISTS
                 (SendGo.tree_lens (ts_trees s2 TK_D) (ts_maxcode s1D TK_D))
                 6 = true).
  { apply (HB CT_DISTS
             (SendGo.tree_lens (ts_trees s2 TK_D) (ts_maxcode s1D TK_D)) 6).
    - right; right.
      split; [reflexivity|].
      split.
      { rewrite tree_lens_length. lia. }
      split; [reflexivity|].
      split.
      { left. rewrite EllD.
        change (2 ^ 15)%nat with 32768%nat. exact KD. }
      { intros len Hin. rewrite EllD in Hin. exact (KDub len Hin). }
    - intros c st Hpre n t.
      refine (EF CT_DISTS _ 6 c st _ _ Hpre n t).
      + right; right.
        split; [reflexivity|].
        split; [rewrite tree_lens_length; lia | reflexivity].
      + intros len Hin. rewrite EllD in Hin. exact (KDub len Hin). }
  (* ---- A1: the 19-slot CL list ---- *)
  (* name build_bl_tree's internal pipeline at s1D *)
  set (p1 := scan_tree (ts_trees s1D TK_L) (ts_maxcode s1D TK_L)
               (ts_trees s1D TK_BL)) in *.
  set (s1sc := set_tree TK_BL (snd p1) (set_tree TK_L (fst p1) s1D)) in *.
  set (p2 := scan_tree (ts_trees s1sc TK_D) (ts_maxcode s1sc TK_D)
               (ts_trees s1sc TK_BL)) in *.
  set (s2sc := set_tree TK_BL (snd p2) (set_tree TK_D (fst p2) s1sc)) in *.
  assert (Es3 : ts_trees s2 TK_BL
                = ts_trees (build_tree TK_BL s2sc) TK_BL).
  { unfold s2, s2sc, p2, s1sc, p1, build_bl_tree.
    cbv zeta.
    cbn [snd].
    unfold set_optlen.
    cbn [ts_trees].
    reflexivity. }
  assert (Hblsc : forall b, b < 0 \/ 15 < b -> ts_blcount s2sc b = 0).
  { intros b Hb. unfold s2sc, s1sc.
    rewrite !bc_settree. exact (HR1D b Hb). }
  destruct (kraft_BL s2sc Hblsc) as (Kbl & Kblub & Kmaxr & Kdead).
  set (bt := ts_trees (build_tree TK_BL s2sc) TK_BL) in *.
  set (mb := ts_maxcode (build_tree TK_BL s2sc) TK_BL) in *.
  assert (E19 : SendGo.tree_lens bt 18
                = SendGo.tree_lens bt mb
                  ++ map (fun i => Z.to_nat (t_len bt (Z.of_nat i)))
                       (seq (Z.to_nat (mb + 1))
                          (Z.to_nat (18 + 1) - Z.to_nat (mb + 1)))).
  { apply tree_lens_app. lia. }
  assert (Htail0 : forall x,
            In x (map (fun i => Z.to_nat (t_len bt (Z.of_nat i)))
                    (seq (Z.to_nat (mb + 1))
                       (Z.to_nat (18 + 1) - Z.to_nat (mb + 1)))) ->
            x = 0%nat).
  { intros x Hx.
    apply in_map_iff in Hx.
    destruct Hx as (i & <- & Hi).
    apply in_seq in Hi.
    rewrite Kdead; [reflexivity|].
    split; [lia|].
    destruct Hi as [Hlo Hhi]. lia. }
  assert (K19 : (kraft_sum (SendGo.tree_lens bt 18) 7 = 128)%nat).
  { rewrite E19, kraft_sum_app_zeros by exact Htail0. exact Kbl. }
  assert (K19ub : forall len, In len (SendGo.tree_lens bt 18) ->
                  (len <= 7)%nat).
  { intros len Hin.
    rewrite E19 in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin|Hin].
    - exact (Kblub len Hin).
    - rewrite (Htail0 len Hin). lia. }
  assert (A1 : build_accepts_b CT_CODES
                 (SendGo.tree_lens (ts_trees s2 TK_BL) 18) 7 = true).
  { rewrite Es3. fold bt.
    apply (HB CT_CODES (SendGo.tree_lens bt 18) 7).
    - left.
      split; [reflexivity|].
      split.
      { rewrite tree_lens_length. lia. }
      split; [reflexivity|].
      split.
      { change (2 ^ 7)%nat with 128%nat. exact K19. }
      { exact K19ub. }
    - intros c st Hpre n t.
      refine (EF CT_CODES _ 7 c st _ _ Hpre n t).
      + left.
        split; [reflexivity|].
        split; [rewrite tree_lens_length; lia | reflexivity].
      + (* lens_capped at 15, weakened from the CL bound at 7 *)
        intros len Hin.
        pose proof (K19ub len Hin). lia. }
  (* package *)
  refine (conj A1 (conj _ (conj _ (conj A4 A5)))).
  - exact A2.
  - exact A3.
Qed.

Print Assumptions dyn_strict_guards.
