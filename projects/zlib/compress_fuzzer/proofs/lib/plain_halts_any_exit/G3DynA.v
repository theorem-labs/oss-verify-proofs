(** * G3DynA — the three tree builds instantiated at the flush state.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G3 dynamic arm,
    part 1: per-build wrappers over an earlier development run's landed keystone, with the
    destructuring-equation plumbing done ONCE here so G3DynB reads
    build_tree facts as plain conclusions.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    Two facts are consumed as PREMISES pending an earlier development run's re-exports
    (requested through the lead; conversion to Qed is zero-restructuring):
      [Hblc']  — blcount support at the build output (R1);
      [Hnn']   — global length nonnegativity at the output (R2). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import BtFrame ZReproScanR.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream Huff DeflateSpec Trees CbEmit
  HuffGenCodes KraftDlNn ClStream SendItems SendGo SendGoLens HuffCover CoverChain ScanBase LdDynRT BuildTree BtSized BtTerm BtCensus4 BtCensus5
  BtItem6 BtItem6b BtClPack BtBlSide BtLive BtLiveR DynCodes.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.


(** The dynamic branch's writer, as one closed expression — the exact
    term [tr_flush_block] builds, so the seam hypothesis unifies.
    (Lives here rather than in G3Block so the dynamic-arm assembly can
    be staged without G3Block's stored-arm dependencies.) *)
Definition dyn_bw (last mbi : Z) (s2 : TSt) : BW :=
  compress_block (ts_symbuf s2) (ts_symnext s2) (ts_trees s2 TK_L)
    (ts_trees s2 TK_D)
    (send_all_trees (ts_maxcode s2 TK_L + 1) (ts_maxcode s2 TK_D + 1)
       (mbi + 1)
       (set_bw (bw_send_bits (Z.shiftl DYN_TREES 1 + last) 3 (ts_bw s2))
          s2)).

(** [LensOf] holds tautologically between a tree and its own length vector,
    provided the lengths are nonnegative (Z-to-nat round trip). *)
Lemma lensof_self : forall t maxc,
  (forall i, 0 <= t_len t i) ->
  LensOf t (tree_lens t maxc).
Proof.
  intros t maxc Hnn k Hk.
  rewrite BtClPack.tree_lens_length in Hk.
  rewrite (BtClPack.tree_lens_nth t maxc k Hk).
  rewrite Z2Nat.id by apply Hnn.
  reflexivity.
Qed.

(** Past the vector's end, [nth]'s default is 0 — [AbsentBeyond] is free. *)
Lemma absentbeyond_self : forall t maxc,
  AbsentBeyond (tree_lens t maxc) maxc.
Proof.
  intros t maxc k Hk.
  apply nth_overflow.
  rewrite BtClPack.tree_lens_length. lia.
Qed.

(** ** The TK_L build, at any state with a live END_BLOCK *)

Theorem inst_L : forall s,
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  t_freq (ts_trees s TK_L) END_BLOCK <> 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (build_tree TK_L s) b = 0) ->
  (forall i, 0 <= t_len (ts_trees (build_tree TK_L s) TK_L) i) ->
  let bt := build_tree TK_L s in
  let maxc := ts_maxcode bt TK_L in
  256 <= maxc <= 285
  /\ ValidLengths (tree_lens (ts_trees bt TK_L) maxc) 15%nat
  /\ (forall i, 0 <= i <= maxc -> 0 <= t_len (ts_trees bt TK_L) i <= 15)
  /\ 1 <= t_len (ts_trees bt TK_L) END_BLOCK <= 15
  /\ (forall v, 0 <= v < 286 -> t_freq (ts_trees s TK_L) v <> 0 ->
      1 <= t_len (ts_trees bt TK_L) v <= 15 /\ v <= maxc)
  /\ (forall n, tree_codes_upto (ts_trees bt TK_L)
        (tree_lens (ts_trees bt TK_L) maxc) n).
Proof.
  intros s Hblc Heob Hblc' Hnn'.
  assert (Hel : sd_elems TK_L = L_CODES) by reflexivity.
  assert (HelL : 3 <= sd_elems TK_L <= L_CODES)
    by (rewrite Hel; unfold L_CODES; lia).
  assert (HM : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  (* open the build's three internal calls *)
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
  destruct (build_tree_out TK_L s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
              HelL HM HK Hblc E0 E2 Eloop)
    as (Emc & HVL & HBlc & Hzk & Hdead & Hgap & Hrange).
  cbv zeta.
  rewrite Emc.
  (* END_BLOCK's live length *)
  assert (Heobl : 1 <= t_len (ts_trees (build_tree TK_L s) TK_L) END_BLOCK
                  <= 15).
  { pose proof (build_tree_live TK_L s t0 hp0 dep0 hlen0 maxc0
                  t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf END_BLOCK
                  HelL HM HK Hblc E0 E2 Eloop
                  ltac:(rewrite Hel; unfold END_BLOCK, L_CODES; lia) Heob)
      as H.
    change (sd_max_length TK_L) with 15 in H. exact H. }
  (* a live entry symbol sits at or below maxcode *)
  assert (Hlive : forall v, 0 <= v < 286 ->
            t_freq (ts_trees s TK_L) v <> 0 ->
            1 <= t_len (ts_trees (build_tree TK_L s) TK_L) v <= 15
            /\ v <= maxc1).
  { intros v Hv Hfv.
    assert (Hl : 1 <= t_len (ts_trees (build_tree TK_L s) TK_L) v <= 15).
    { pose proof (build_tree_live TK_L s t0 hp0 dep0 hlen0 maxc0
                    t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf v
                    HelL HM HK Hblc E0 E2 Eloop
                    ltac:(rewrite Hel; unfold L_CODES; lia) Hfv) as H.
      change (sd_max_length TK_L) with 15 in H. exact H. }
    split; [exact Hl|].
    destruct (Z_le_gt_dec v maxc1) as [Hle|Hgt]; [exact Hle|].
    exfalso.
    assert (Hf0 : t_freq t1 v = 0)
      by (apply Hgap; rewrite Hel in *; unfold L_CODES in *; lia).
    pose proof (Hdead v ltac:(rewrite Hel; unfold L_CODES; lia) Hf0).
    lia. }
  (* maxcode bounds: END_BLOCK live pins 256 from below; the gap +
     dead-zero pin 285 from above via any live symbol... the upper bound
     is maxc1 < elems, which the freq-gap gives through liveness at
     END_BLOCK only if 285 < maxc1 were possible — rule it out by the
     range conclusion's domain. *)
  assert (Hmc : 256 <= maxc1 <= 285).
  { split.
    - destruct (Hlive END_BLOCK ltac:(unfold END_BLOCK; lia) Heob)
        as [_ Hle]. unfold END_BLOCK in Hle. lia.
    - (* upper: 285 < maxc1 contradicts ValidLengths' vector width? No —
         use the parked census's maxcode range instead *)
      pose proof (build_tree_parked TK_L s t0 hp0 dep0 hlen0 maxc0
                    t1 hp1 dep1 hlen1 maxc1 ol1 sl1
                    (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                       (hlen1 / 2)) stf HelL E0 E2 eq_refl Eloop)
        as [Hpk _].
      pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as H.
      rewrite Hel in H. unfold L_CODES in H. lia. }
  split; [exact Hmc|].
  split; [exact HVL|].
  split; [intros i Hi; apply Hrange; rewrite Hel; unfold L_CODES; lia|].
  split; [exact Heobl|].
  split; [exact Hlive|].
  (* the codes: the output IS a gen_codes image *)
  intro n.
  assert (Eshape : exists tpre,
      ts_trees (build_tree TK_L s) TK_L
      = gen_codes tpre maxc1 (ts_blcount (build_tree TK_L s))
      /\ forall i, t_len tpre i
                  = t_len (ts_trees (build_tree TK_L s) TK_L) i).
  { unfold build_tree. cbv zeta.
    rewrite E0. cbv beta match.
    rewrite E2. cbv beta match.
    rewrite Eloop. cbv beta match.
    eexists. split.
    - rewrite set_tree_same. reflexivity.
    - intro i. rewrite set_tree_same, gen_codes_len. reflexivity. }
  destruct Eshape as (tpre & Etree & Elens).
  rewrite Etree at 1.
  apply gen_codes_tree_codes_upto.
  - intros k Hk.
    rewrite Elens.
    exact (lensof_self _ maxc1 Hnn' k Hk).
  - exact HBlc.
  - exact HVL.
  - apply absentbeyond_self.
  - lia.
Qed.


(** ** The TK_D build — no liveness assumed (bt_force2 manufactures
    distance codes 0/1 when the block has no matches).

    [Hmc0] is the maxcode lower bound (>= 1 always, by bt_force2's bumps
    against bt_init's census) — consumed as a premise pending an earlier development run's
    R3 re-export. *)

Theorem inst_D : forall s,
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (build_tree TK_D s) b = 0) ->
  (forall i, 0 <= t_len (ts_trees (build_tree TK_D s) TK_D) i) ->
  1 <= ts_maxcode (build_tree TK_D s) TK_D ->
  let bt := build_tree TK_D s in
  let maxc := ts_maxcode bt TK_D in
  1 <= maxc <= 29
  /\ ValidLengths (tree_lens (ts_trees bt TK_D) maxc) 15%nat
  /\ (forall i, 0 <= i <= maxc -> 0 <= t_len (ts_trees bt TK_D) i <= 15)
  /\ (forall v, 0 <= v < 30 -> t_freq (ts_trees s TK_D) v <> 0 ->
      1 <= t_len (ts_trees bt TK_D) v <= 15 /\ v <= maxc)
  /\ (forall n, tree_codes_upto (ts_trees bt TK_D)
        (tree_lens (ts_trees bt TK_D) maxc) n).
Proof.
  intros s Hblc Hblc' Hnn' Hmc0.
  assert (Hel : sd_elems TK_D = D_CODES) by reflexivity.
  assert (HelL : 3 <= sd_elems TK_D <= L_CODES)
    by (rewrite Hel; unfold D_CODES, L_CODES; lia).
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
  destruct (build_tree_out TK_D s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
              HelL HM HK Hblc E0 E2 Eloop)
    as (Emc & HVL & HBlc & Hzk & Hdead & Hgap & Hrange).
  cbv zeta.
  rewrite Emc.
  rewrite Emc in Hmc0.
  assert (Hlive : forall v, 0 <= v < 30 ->
            t_freq (ts_trees s TK_D) v <> 0 ->
            1 <= t_len (ts_trees (build_tree TK_D s) TK_D) v <= 15
            /\ v <= maxc1).
  { intros v Hv Hfv.
    assert (Hl : 1 <= t_len (ts_trees (build_tree TK_D s) TK_D) v <= 15).
    { pose proof (build_tree_live TK_D s t0 hp0 dep0 hlen0 maxc0
                    t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf v
                    HelL HM HK Hblc E0 E2 Eloop
                    ltac:(rewrite Hel; unfold D_CODES; lia) Hfv) as H.
      change (sd_max_length TK_D) with 15 in H. exact H. }
    split; [exact Hl|].
    destruct (Z_le_gt_dec v maxc1) as [Hle|Hgt]; [exact Hle|].
    exfalso.
    assert (Hf0 : t_freq t1 v = 0)
      by (apply Hgap; rewrite Hel in *; unfold D_CODES in *; lia).
    pose proof (Hdead v ltac:(rewrite Hel; unfold D_CODES; lia) Hf0).
    lia. }
  assert (Hmc : 1 <= maxc1 <= 29).
  { split; [exact Hmc0|].
    pose proof (build_tree_parked TK_D s t0 hp0 dep0 hlen0 maxc0
                  t1 hp1 dep1 hlen1 maxc1 ol1 sl1
                  (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                     (hlen1 / 2)) stf HelL E0 E2 eq_refl Eloop)
      as [Hpk _].
    pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as H.
    rewrite Hel in H. unfold D_CODES in H. lia. }
  split; [exact Hmc|].
  split; [exact HVL|].
  split; [intros i Hi; apply Hrange; rewrite Hel; unfold D_CODES; lia|].
  split; [exact Hlive|].
  intro n.
  assert (Eshape : exists tpre,
      ts_trees (build_tree TK_D s) TK_D
      = gen_codes tpre maxc1 (ts_blcount (build_tree TK_D s))
      /\ forall i, t_len tpre i
                  = t_len (ts_trees (build_tree TK_D s) TK_D) i).
  { unfold build_tree. cbv zeta.
    rewrite E0. cbv beta match.
    rewrite E2. cbv beta match.
    rewrite Eloop. cbv beta match.
    eexists. split.
    - rewrite set_tree_same. reflexivity.
    - intro i. rewrite set_tree_same, gen_codes_len. reflexivity. }
  destruct Eshape as (tpre & Etree & Elens).
  rewrite Etree at 1.
  apply gen_codes_tree_codes_upto.
  - intros k Hk.
    rewrite Elens.
    exact (lensof_self _ maxc1 Hnn' k Hk).
  - exact HBlc.
  - exact HVL.
  - apply absentbeyond_self.
  - lia.
Qed.


(** ** [scan_tree]'s second component only touches frequencies *)

Lemma scan_go_lens : forall fuel t maxc n prevlen nextlen count maxcnt
                            mincnt bl i,
  t_len (scan_go fuel t maxc n prevlen nextlen count maxcnt mincnt bl) i
  = t_len bl i.
Proof.
  induction fuel as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt bl i;
    cbn [scan_go].
  - reflexivity.
  - destruct (Z.ltb maxc n); [reflexivity|].
    cbv zeta.
    destruct ((count + 1 <? maxcnt) && (nextlen =? t_len t (n + 1)));
      [apply IH|].
    rewrite IH.
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b
    end;
    unfold t_setfreq, t_len; cbn [tr_dl]; reflexivity.
Qed.

Lemma scan_tree_snd_lens : forall t maxc bl i,
  t_len (snd (scan_tree t maxc bl)) i = t_len bl i.
Proof.
  intros t maxc bl i. unfold scan_tree. cbn [snd].
  apply scan_go_lens.
Qed.

(** The guard write never touches the code array. *)
Lemma scan_tree_fst_code : forall t maxc bl i,
  t_code (fst (scan_tree t maxc bl)) i = t_code t i.
Proof.
  intros t maxc bl i. unfold scan_tree. cbn [fst].
  unfold t_setlen, t_code. cbn [tr_fc]. reflexivity.
Qed.

(** ** [build_bl_tree], instantiated *)

Theorem inst_BL : forall s,
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  (forall i, 0 <= i < 19 -> t_freq (ts_trees s TK_BL) i = 0) ->
  (forall i, 0 <= t_len (ts_trees s TK_BL) i) ->
  256 <= ts_maxcode s TK_L <= 285 ->
  1 <= ts_maxcode s TK_D <= 29 ->
  (forall i, 0 <= t_len (ts_trees s TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees s TK_D) i) ->
  (forall i, 0 <= i <= ts_maxcode s TK_L ->
   0 <= t_len (ts_trees s TK_L) i <= 15) ->
  (forall i, 0 <= i <= ts_maxcode s TK_D ->
   0 <= t_len (ts_trees s TK_D) i <= 15) ->
  1 <= t_len (ts_trees s TK_L) END_BLOCK <= 15 ->
  (forall b, b < 0 \/ 15 < b ->
   ts_blcount (snd (build_bl_tree s)) b = 0) ->
  (forall i, 0 <= t_len (ts_trees (snd (build_bl_tree s)) TK_BL) i) ->
  let mbi := fst (build_bl_tree s) in
  let s' := snd (build_bl_tree s) in
  let blt := ts_trees s' TK_BL in
  let cl := tree_lens blt 18 in
  3 <= mbi <= 18
  /\ length cl = 19%nat
  /\ ValidLengths cl 7%nat
  /\ (forall r, 0 <= r <= 18 -> 0 <= t_len blt (bl_order r) < 8)
  /\ (forall j, mbi + 1 <= j <= 18 -> t_len blt (bl_order j) = 0)
  /\ (exists blt0 maxcbl blc,
        blt = gen_codes blt0 maxcbl blc
        /\ LensOf blt0 cl /\ BlcOf blc cl
        /\ AbsentBeyond cl maxcbl /\ -1 <= maxcbl <= 288)
  /\ (exists bitsL, cl_bits cl (send_tree_items (ts_trees s' TK_L)
        (ts_maxcode s TK_L)) = Some bitsL)
  /\ (exists bitsD, cl_bits cl (send_tree_items (ts_trees s' TK_D)
        (ts_maxcode s TK_D)) = Some bitsD)
  /\ t_len (ts_trees s' TK_L) (ts_maxcode s TK_L + 1) = 65535
  /\ t_len (ts_trees s' TK_D) (ts_maxcode s TK_D + 1) = 65535
  /\ ts_maxcode s' TK_L = ts_maxcode s TK_L
  /\ ts_maxcode s' TK_D = ts_maxcode s TK_D
  /\ (forall i, 0 <= t_len (ts_trees s' TK_L) i)
  /\ (forall i, 0 <= i <= ts_maxcode s TK_L ->
      0 <= t_len (ts_trees s' TK_L) i <= 15)
  /\ (forall i, 0 <= t_len (ts_trees s' TK_D) i)
  /\ (forall i, 0 <= i <= ts_maxcode s TK_D ->
      0 <= t_len (ts_trees s' TK_D) i <= 15)
  /\ (forall i, t_code (ts_trees s' TK_L) i = t_code (ts_trees s TK_L) i)
  /\ (forall i, i <> ts_maxcode s TK_L + 1 ->
      t_len (ts_trees s' TK_L) i = t_len (ts_trees s TK_L) i)
  /\ (forall i, t_code (ts_trees s' TK_D) i = t_code (ts_trees s TK_D) i)
  /\ (forall i, i <> ts_maxcode s TK_D + 1 ->
      t_len (ts_trees s' TK_D) i = t_len (ts_trees s TK_D) i)
  /\ ts_symbuf s' = ts_symbuf s
  /\ ts_symnext s' = ts_symnext s
  /\ ts_bw s' = ts_bw s.
Proof.
  intros s Hblc Hblf Hbln HmcL HmcD HnnL HnnD HrngL HrngD Heob Hblc' Hbln'.
  cbv zeta.
  (* name the pipeline's states *)
  set (p1 := scan_tree (ts_trees s TK_L) (ts_maxcode s TK_L)
               (ts_trees s TK_BL)).
  set (bl2 := snd p1).
  set (s1sc := set_tree TK_BL bl2 (set_tree TK_L (fst p1) s)).
  (* build_bl_tree's own p2 is stated over s1sc's fields *)
  assert (E1L : ts_trees s1sc TK_D = ts_trees s TK_D) by reflexivity.
  assert (E1mc : ts_maxcode s1sc TK_D = ts_maxcode s TK_D) by reflexivity.
  set (p2 := scan_tree (ts_trees s TK_D) (ts_maxcode s TK_D) bl2).
  set (bl3 := snd p2).
  set (s2sc := set_tree TK_BL bl3 (set_tree TK_D (fst p2) s1sc)).
  (* the BL build's internal equations, at the canonical spelling *)
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) bl3
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  assert (Hsz : 2 <= hlen1 <= L_CODES)
    by (eapply (bt_sized TK_BL s2sc); try exact E0; try exact E2;
        change (sd_elems TK_BL) with 19; unfold L_CODES; lia).
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems TK_BL |}) as [stf|] eqn:Eloop.
  2:{ exfalso.
      eapply (bt_loop_terminates (Z.to_nat HEAP_SIZE)); [| | exact Eloop].
      - cbn [b_hlen]. lia.
      - cbn [b_hlen].
        rewrite Z2Nat.id by (unfold HEAP_SIZE, L_CODES; lia).
        unfold HEAP_SIZE, L_CODES in *. lia. }
  (* items 1-3 at the built BL tree *)
  destruct (bl_cl_pack s2sc t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
              Hblc E0 E2 Eloop)
    as (Pmc & Pmcr & Plen & Plens & Pblc & PV7 & Pab & P8).
  (* mbi >= 3 *)
  assert (Hmbi3 : 3 <= fst (build_bl_tree s)).
  { eapply (build_bl_tree_mbi3_r s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf END_BLOCK);
      try eassumption.
    - unfold END_BLOCK; lia.
    - lia.
    - lia.
    - lia.
    - intros x Hx. rewrite (Hblf x Hx). lia. }
  (* the guards + maxcode frames *)
  pose proof (build_bl_tree_guards s) as (GgL & GgD & GmL & GmD).
  cbv zeta in GgL, GgD, GmL, GmD.
  (* the result state, pinned to the pipeline names *)
  assert (Ebbl : build_bl_tree s
                 = (bbl_scan (Z.to_nat BL_CODES + 1)
                      (ts_trees (build_tree TK_BL s2sc) TK_BL)
                      (BL_CODES - 1),
                    set_optlen
                      (u64 (ts_optlen (build_tree TK_BL s2sc)
                            + 3 * (bbl_scan (Z.to_nat BL_CODES + 1)
                                     (ts_trees (build_tree TK_BL s2sc) TK_BL)
                                     (BL_CODES - 1) + 1) + 5 + 5 + 4))
                      (build_tree TK_BL s2sc))).
  { unfold build_bl_tree. cbv zeta. reflexivity. }
  assert (EblT : ts_trees (snd (build_bl_tree s)) TK_BL
                 = ts_trees (build_tree TK_BL s2sc) TK_BL)
    by (rewrite Ebbl; reflexivity).
  assert (Embi : fst (build_bl_tree s)
                 = bbl_scan (Z.to_nat BL_CODES + 1)
                     (ts_trees (build_tree TK_BL s2sc) TK_BL)
                     (BL_CODES - 1))
    by (rewrite Ebbl; reflexivity).
  (* the bbl_scan spec at the built tree *)
  destruct (bbl_scan_spec (Z.to_nat BL_CODES + 1)
              (ts_trees (build_tree TK_BL s2sc) TK_BL) (BL_CODES - 1)
              ltac:(rewrite Nat2Z.inj_add, Z2Nat.id
                      by (unfold BL_CODES; lia);
                    unfold BL_CODES; cbn [Z.of_nat]; lia)
              ltac:(unfold BL_CODES; lia))
    as (Hsrange & Hszero & _).
  change (BL_CODES - 1) with 18 in Hsrange, Hszero, Embi, Ebbl.
  (* the coverage: both code-length streams encodable *)
  destruct (cover_both_streams_final_r s s2sc
              (tree_lens (ts_trees (build_tree TK_BL s2sc) TK_BL) 18)
              (ts_trees s TK_L) (ts_maxcode s TK_L)
              (ts_trees s TK_D) (ts_maxcode s TK_D)
              p1 p2 t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              ltac:(lia) ltac:(lia) HrngL HrngD Hblf eq_refl eq_refl
              eq_refl
              ltac:(unfold DlNn; intro i; unfold p2;
                    rewrite scan_tree_snd_lens;
                    unfold bl2, p1; rewrite scan_tree_snd_lens;
                    apply Hbln)
              E0 E2 Plens
              ltac:(rewrite BtClPack.tree_lens_length; cbn; lia))
    as (HbitsL & HbitsD).
  (* result-state projections in pipeline vocabulary *)
  assert (E'L : ts_trees (snd (build_bl_tree s)) TK_L = fst p1).
  { rewrite Ebbl. cbn [snd].
    change (ts_trees (set_optlen ?v ?x) TK_L) with (ts_trees x TK_L).
    rewrite (build_tree_tree_other TK_BL _ TK_L)
      by (unfold TK_L, TK_BL; lia).
    unfold s2sc, s1sc.
    rewrite (set_tree_other TK_BL _ _ TK_L) by (unfold TK_L, TK_BL; lia).
    rewrite (set_tree_other TK_D _ _ TK_L) by (unfold TK_L, TK_D; lia).
    rewrite (set_tree_other TK_BL _ _ TK_L) by (unfold TK_L, TK_BL; lia).
    apply set_tree_same. }
  assert (E'D : ts_trees (snd (build_bl_tree s)) TK_D = fst p2).
  { rewrite Ebbl. cbn [snd].
    change (ts_trees (set_optlen ?v ?x) TK_D) with (ts_trees x TK_D).
    rewrite (build_tree_tree_other TK_BL _ TK_D)
      by (unfold TK_D, TK_BL; lia).
    unfold s2sc.
    rewrite (set_tree_other TK_BL _ _ TK_D) by (unfold TK_D, TK_BL; lia).
    apply set_tree_same. }
  (* lens of the guarded trees *)
  assert (HL'nn : forall i, 0 <= t_len (ts_trees (snd (build_bl_tree s))
                              TK_L) i).
  { intro i. rewrite E'L.
    destruct (Z.eq_dec i (ts_maxcode s TK_L + 1)) as [->|Hne].
    - unfold p1. rewrite scan_tree_guard. lia.
    - unfold p1. rewrite scan_tree_len_other by exact Hne. apply HnnL. }
  assert (HL'rng : forall i, 0 <= i <= ts_maxcode s TK_L ->
            0 <= t_len (ts_trees (snd (build_bl_tree s)) TK_L) i <= 15).
  { intros i Hi. rewrite E'L.
    unfold p1. rewrite scan_tree_len_other by lia. apply HrngL. lia. }
  assert (HD'nn : forall i, 0 <= t_len (ts_trees (snd (build_bl_tree s))
                              TK_D) i).
  { intro i. rewrite E'D.
    destruct (Z.eq_dec i (ts_maxcode s TK_D + 1)) as [->|Hne].
    - unfold p2. rewrite scan_tree_guard. lia.
    - unfold p2. rewrite scan_tree_len_other by exact Hne. apply HnnD. }
  assert (HD'rng : forall i, 0 <= i <= ts_maxcode s TK_D ->
            0 <= t_len (ts_trees (snd (build_bl_tree s)) TK_D) i <= 15).
  { intros i Hi. rewrite E'D.
    unfold p2. rewrite scan_tree_len_other by lia. apply HrngD. lia. }
  split.
  { split; [exact Hmbi3|].
    rewrite Embi. lia. }
  split; [rewrite EblT; exact Plen|].
  split; [rewrite EblT; exact PV7|].
  split; [rewrite EblT; exact P8|].
  split.
  { rewrite EblT, Embi.
    intros j Hj. apply Hszero. lia. }
  split.
  { rewrite EblT.
    assert (Eshape : exists tpre,
        ts_trees (build_tree TK_BL s2sc) TK_BL
        = gen_codes tpre maxc1 (ts_blcount (build_tree TK_BL s2sc))
        /\ forall i, t_len tpre i
                    = t_len (ts_trees (build_tree TK_BL s2sc) TK_BL) i).
    { unfold build_tree. cbv zeta.
      change (ts_trees s2sc TK_BL) with bl3.
      change (ts_heap s2sc) with (ts_heap s).
      change (ts_depth s2sc) with (ts_depth s).
      change (ts_optlen s2sc) with (ts_optlen s).
      change (ts_statlen s2sc) with (ts_statlen s).
      rewrite E0. cbv beta match.
      rewrite E2. cbv beta match.
      rewrite Eloop. cbv beta match.
      eexists. split.
      - rewrite set_tree_same. reflexivity.
      - intro i. rewrite set_tree_same, gen_codes_len. reflexivity. }
    destruct Eshape as (tpre & Etree & Elens).
    exists tpre, maxc1, (ts_blcount (build_tree TK_BL s2sc)).
    split; [exact Etree|].
    split.
    { intros k Hk. rewrite Elens. exact (Plens k Hk). }
    split; [exact Pblc|].
    split; [exact Pab|].
    lia. }
  split; [rewrite E'L; exact HbitsL|].
  split; [rewrite E'D; exact HbitsD|].
  split; [exact GgL|].
  split; [exact GgD|].
  split; [exact GmL|].
  split; [exact GmD|].
  split; [exact HL'nn|].
  split; [exact HL'rng|].
  split; [exact HD'nn|].
  split; [exact HD'rng|].
  split.
  { intro i. rewrite E'L. unfold p1. apply scan_tree_fst_code. }
  split.
  { intros i Hne. rewrite E'L. unfold p1.
    apply scan_tree_len_other. exact Hne. }
  split.
  { intro i. rewrite E'D. unfold p2. apply scan_tree_fst_code. }
  split.
  { intros i Hne. rewrite E'D. unfold p2.
    apply scan_tree_len_other. exact Hne. }
  split.
  { rewrite Ebbl. cbn [snd].
    change (ts_symbuf (set_optlen ?v ?x)) with (ts_symbuf x).
    destruct (build_tree_frame TK_BL s2sc) as (F1 & _ & _ & _).
    rewrite F1. reflexivity. }
  split.
  { rewrite Ebbl. cbn [snd].
    change (ts_symnext (set_optlen ?v ?x)) with (ts_symnext x).
    destruct (build_tree_frame TK_BL s2sc) as (_ & F2 & _ & _).
    rewrite F2. reflexivity. }
  rewrite Ebbl. cbn [snd].
  change (ts_bw (set_optlen ?v ?x)) with (ts_bw x).
  destruct (build_tree_frame TK_BL s2sc) as (_ & _ & F3 & _).
  rewrite F3. reflexivity.
Qed.

Print Assumptions inst_L.
Print Assumptions inst_D.
Print Assumptions inst_BL.
