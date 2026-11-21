(** * ItGSubCover — SUB-TABLE coverage and root-entry classification for
      [inflate_table].

    OWNER: an earlier development run (zlib campaign, dynamic-table inhabitation lap,
    2026-08-19).  The confirmed-missing half of the coverage story: the
    landed [ItGTblCover.it_covers_root_pos] covers the ROOT region
    [[0, 2^root)] with a bits-range payload; the [DynTblOk] consumers
    (two-level, chain-fit, the wf-tbl clause set) additionally need
    (a) every root entry CLASSIFIED — a leaf shape or a sub-table pointer
        whose declared window sits inside [[2^root, used)], and
    (b) the whole sub-region [[2^root, used)] covered with LEVEL-2 leaf
        entries of width in [[1, 15 - root]].

    The geometry is the landed root walk one level down: within one root
    unit, codes of length [len] fill the open window [[next, next+2^curr)]
    at sub-indices given by the same bit-reversed position, at scale
    [15 - root] instead of 15.  Windows tile [[2^root, used)] contiguously
    ([next' = next + 2^curr], [used' = next' + 2^curr']), and global
    completeness makes every window exactly full when its root prefix is
    exhausted.  All reversal/mass/window bookkeeping is reused from the
    ported [ItGTblRev]/[ItGTblGeom]/[ItGTblSortWin]/[ItGTblCover]/
    [GtLenProv] layers (md5 pins in PORT-PINS-tbl.md5). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGTblRepl ItGTblLeafPos
  GtLenProv GtUsedBits.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(** ** 1.  The consumer-facing shapes *)

(** The low-nibble extra-bits budget: [inffast] masks [op & 15] and adds it
    to a 15-bit refill, so the walks need it bounded per table kind.  The
    CODES table never takes the base arm (its [match] is 20 and its work
    values are at most 18), so any bound is fine there. *)
Definition x15_bound (ty : Z) : Z := if Z.eqb ty CT_DISTS then 13 else 5.

(** What every LEAF the build writes looks like: a literal, a base entry
    (bit 4 set, bounded extra), or an end/invalid marker (bit 6 set) — in
    particular NEVER a sub-table pointer shape.  DISTS tables additionally
    have no literals ([x_match = 0] makes the literal arm unreachable). *)
Definition LeafShape (ty : Z) (e : Code) : Prop :=
  (c_op e = 0 \/ Z.land (c_op e) 16 <> 0 \/ Z.land (c_op e) 64 <> 0)
  /\ (ty = CT_DISTS -> c_op e <> 0)
  /\ 0 <= c_op e < 256
  /\ 0 <= c_val e < 65536
  /\ (Z.land (c_op e) 16 <> 0 -> Z.land (c_op e) 15 <= x15_bound ty)
  /\ (ty = CT_LENS -> Z.land (c_op e) 16 <> 0 ->
      3 <= c_val e
      /\ c_val e + Z.shiftl 1 (Z.land (c_op e) 15) - 1 <= 258)
  /\ (c_op e <> 0 -> Z.land (c_op e) 32 = 0 -> Z.land (c_op e) 64 = 0 ->
      1 <= c_val e).

(** A written sub-table (level-2) entry. *)
Definition SubEntry (ty root : Z) (e : Code) : Prop :=
  LeafShape ty e /\ 1 <= c_bits e <= 15 - root.

(** A written root-level leaf. *)
Definition RootLeaf (ty root : Z) (e : Code) : Prop :=
  LeafShape ty e /\ 1 <= c_bits e <= root.

(** A written sub-table pointer: [op] is the sub-table's width, [val] its
    offset, and the declared window sits inside the used extent. *)
Definition RootPtr (root used : Z) (e : Code) : Prop :=
  c_bits e = root
  /\ 1 <= c_op e <= 15 - root
  /\ 0 <= c_val e < 65536
  /\ 2 ^ root <= c_val e
  /\ c_val e + 2 ^ (c_op e) <= used.

Definition RootEntry (ty root used : Z) (e : Code) : Prop :=
  RootLeaf ty root e \/ RootPtr root used e.

(** ** 2.  The base/extra tables have the leaf shape — reflectively *)

Definition leaf_opb (ty : Z) (op : Z) : bool :=
  ((op =? 0) || negb (Z.land op 16 =? 0) || negb (Z.land op 64 =? 0))
  && (negb (ty =? CT_DISTS) || negb (op =? 0))
  && ((Z.land op 16 =? 0) || (Z.land op 15 <=? x15_bound ty))
  && (0 <=? op) && (op <? 256).

Definition len_valb (op val : Z) : bool :=
  (Z.land op 16 =? 0)
  || ((3 <=? val) && (val + Z.shiftl 1 (Z.land op 15) - 1 <=? 258)).

Lemma len_valb_sound : forall op val, len_valb op val = true ->
  Z.land op 16 <> 0 ->
  3 <= val /\ val + Z.shiftl 1 (Z.land op 15) - 1 <= 258.
Proof.
  intros op val H H16. unfold len_valb in H.
  apply orb_prop in H as [H|H].
  - apply Z.eqb_eq in H. contradiction.
  - apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption.
Qed.

Lemma lbase_lext_table :
  forallb (fun n => len_valb (lext (Z.of_nat n)) (lbase (Z.of_nat n)))
    (seq 0 31) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lbase_lext_ok : forall j, 0 <= j <= 30 ->
  len_valb (lext j) (lbase j) = true.
Proof.
  intros j Hj.
  pose proof (proj1 (forallb_forall _ _) lbase_lext_table (Z.to_nat j)) as H.
  cbn beta in H. rewrite Z2Nat.id in H by lia.
  apply H, in_seq. lia.
Qed.

Lemma lbase_range_table :
  forallb (fun n => (0 <=? lbase (Z.of_nat n)) && (lbase (Z.of_nat n) <? 65536))
    (seq 0 31) = true.
Proof. vm_compute. reflexivity. Qed.

(** live-shaped base entries carry positive values, on both tables *)
Definition live_valb (op val : Z) : bool :=
  (op =? 0) || negb (Z.land op 32 =? 0) || negb (Z.land op 64 =? 0)
  || (1 <=? val).

Lemma live_valb_sound : forall op val, live_valb op val = true ->
  op <> 0 -> Z.land op 32 = 0 -> Z.land op 64 = 0 -> 1 <= val.
Proof.
  intros op val H Hnz H32 H64. unfold live_valb in H.
  apply orb_prop in H as [H|H];
    [apply orb_prop in H as [H|H];
      [apply orb_prop in H as [H|H]|]|].
  - apply Z.eqb_eq in H. contradiction.
  - apply negb_true_iff, Z.eqb_neq in H. contradiction.
  - apply negb_true_iff, Z.eqb_neq in H. contradiction.
  - apply Z.leb_le in H. exact H.
Qed.

Lemma lbase_live_table :
  forallb (fun n => live_valb (lext (Z.of_nat n)) (lbase (Z.of_nat n)))
    (seq 0 31) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dbase_live_table :
  forallb (fun n => live_valb (dext (Z.of_nat n)) (dbase (Z.of_nat n)))
    (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dbase_range_table :
  forallb (fun n => (0 <=? dbase (Z.of_nat n)) && (dbase (Z.of_nat n) <? 65536))
    (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_fact : forall (f : nat -> bool) (m : nat) j,
  forallb f (seq 0 m) = true -> 0 <= j < Z.of_nat m -> f (Z.to_nat j) = true.
Proof.
  intros f m j Hall Hj.
  apply (proj1 (forallb_forall _ _) Hall).
  apply in_seq. lia.
Qed.

Lemma leaf_opb_sound : forall ty op, leaf_opb ty op = true ->
  (op = 0 \/ Z.land op 16 <> 0 \/ Z.land op 64 <> 0)
  /\ (ty = CT_DISTS -> op <> 0)
  /\ (Z.land op 16 <> 0 -> Z.land op 15 <= x15_bound ty)
  /\ 0 <= op < 256.
Proof.
  intros ty op H. unfold leaf_opb in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H4. apply Z.ltb_lt in H5.
  split; [|split; [|split; [|lia]]].
  - apply orb_prop in H1 as [H1|H1];
      [apply orb_prop in H1 as [H1|H1]|].
    + left. apply Z.eqb_eq in H1. exact H1.
    + right. left. apply negb_true_iff, Z.eqb_neq in H1. exact H1.
    + right. right. apply negb_true_iff, Z.eqb_neq in H1. exact H1.
  - intro Hd. subst ty.
    apply orb_prop in H2 as [H2|H2].
    + apply negb_true_iff, Z.eqb_neq in H2. exfalso. apply H2. reflexivity.
    + apply negb_true_iff, Z.eqb_neq in H2. exact H2.
  - intro H16. apply orb_prop in H3 as [H3|H3].
    + apply Z.eqb_eq in H3. contradiction.
    + apply Z.leb_le in H3. exact H3.
Qed.

Lemma lext_leaf_table :
  forallb (fun n => leaf_opb CT_LENS (lext (Z.of_nat n))) (seq 0 31) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dext_leaf_table :
  forallb (fun n => leaf_opb CT_DISTS (dext (Z.of_nat n))) (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lext_leaf : forall j, 0 <= j <= 30 -> leaf_opb CT_LENS (lext j) = true.
Proof.
  intros j Hj.
  pose proof (proj1 (forallb_forall _ _) lext_leaf_table (Z.to_nat j)) as H.
  cbn beta in H. rewrite Z2Nat.id in H by lia.
  apply H, in_seq. lia.
Qed.

Lemma dext_leaf : forall j, 0 <= j <= 31 -> leaf_opb CT_DISTS (dext j) = true.
Proof.
  intros j Hj.
  pose proof (proj1 (forallb_forall _ _) dext_leaf_table (Z.to_nat j)) as H.
  cbn beta in H. rewrite Z2Nat.id in H by lia.
  apply H, in_seq. lia.
Qed.

(** ** 3.  [mkCodeT] field ranges (unconditional, by the constructor masks) *)

Lemma op_mkCodeT_range : forall op b v, 0 <= c_op (mkCodeT op b v) < 256.
Proof.
  intros op b v. unfold mkCodeT. cbn [c_op]. unfold u8.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma val_mkCodeT_range : forall op b v, 0 <= c_val (mkCodeT op b v) < 65536.
Proof.
  intros op b v. unfold mkCodeT. cbn [c_val]. unfold u16.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma op_mkCodeT_id : forall op b v, 0 <= op < 256 -> c_op (mkCodeT op b v) = op.
Proof. intros op b v H. unfold mkCodeT. cbn [c_op]. apply u8_id. exact H. Qed.

Lemma val_mkCodeT_id : forall op b v, 0 <= v < 65536 -> c_val (mkCodeT op b v) = v.
Proof. intros op b v H. unfold mkCodeT. cbn [c_val]. apply u16_id. exact H. Qed.

(** ** 4.  Markers are leaves *)

(** The two markers the transcription writes are [32+64] ([it_here]'s
    invalid/EOB arm) and [64] ([it_pre]'s empty arm, [it_finish]'s fixup);
    both have bit 6 set and bit 4 clear. *)
Lemma marker_leafshape : forall ty op b v,
  0 <= op < 256 -> Z.land op 64 <> 0 -> Z.land op 16 = 0 ->
  LeafShape ty (mkCodeT op b v).
Proof.
  intros ty op b v Hr H64 H16. unfold LeafShape.
  rewrite op_mkCodeT_id by exact Hr.
  split; [right; right; exact H64|].
  split.
  { intros _ Hz. subst op. cbn in H64. apply H64. reflexivity. }
  split; [exact Hr|].
  split; [apply val_mkCodeT_range|].
  split; [intro Hc; contradiction|].
  split; [intros _ Hc; contradiction|].
  intros _ _ Hc. contradiction.
Qed.

(** ** 5.  [it_here] writes a leaf, whatever the arm — per table kind *)

Lemma here_leafshape_codes : forall c st,
  x_match c = 20 ->
  (forall s, 0 <= x_work c s <= 18) ->
  LeafShape CT_CODES (it_here c st).
Proof.
  intros c st Hm Hw. unfold it_here. rewrite Hm.
  pose proof (Hw (s_sym st)) as Hws.
  replace (Z.ltb (x_work c (s_sym st) + 1) 20) with true
    by (symmetry; apply Z.ltb_lt; lia).
  unfold LeafShape.
  rewrite op_mkCodeT_id by lia.
  split; [left; reflexivity|].
  split; [intro Hd; discriminate Hd|].
  split; [lia|].
  split; [apply val_mkCodeT_range|].
  split; [cbn; intro Hc; exfalso; apply Hc; reflexivity|].
  split; [cbn; intros _ Hc; exfalso; apply Hc; reflexivity|].
  intro Hc. exfalso. apply Hc. reflexivity.
Qed.

Lemma here_leafshape_lens : forall c st,
  x_match c = 257 -> x_base c = lbase -> x_extra c = lext ->
  (forall s, 0 <= x_work c s <= 287) ->
  LeafShape CT_LENS (it_here c st).
Proof.
  intros c st Hm Hb He Hw. unfold it_here. rewrite Hm, Hb, He.
  pose proof (Hw (s_sym st)) as Hws.
  destruct (Z.ltb (x_work c (s_sym st) + 1) 257) eqn:H1.
  - (* literal *)
    unfold LeafShape.
    rewrite op_mkCodeT_id by lia.
    split; [left; reflexivity|].
    split; [intro Hd; discriminate Hd|].
    split; [lia|].
    split; [apply val_mkCodeT_range|].
    split; [cbn; intro Hc; exfalso; apply Hc; reflexivity|].
    split; [cbn; intros _ Hc; exfalso; apply Hc; reflexivity|].
    intro Hc. exfalso. apply Hc. reflexivity.
  - apply Z.ltb_ge in H1.
    destruct (Z.leb 257 (x_work c (s_sym st))) eqn:H2.
    + (* length base *)
      apply Z.leb_le in H2.
      set (j := x_work c (s_sym st) - 257).
      assert (Hj : 0 <= j <= 30) by (unfold j; lia).
      destruct (leaf_opb_sound CT_LENS (lext j) (lext_leaf j Hj))
        as (Hop3 & _ & H15 & Hrng).
      assert (Hjv : len_valb (lext j) (lbase j) = true)
        by (apply lbase_lext_ok; exact Hj).
      assert (Hlb256 : 0 <= lbase j < 65536).
      { clear -Hj.
        pose proof (proj1 (forallb_forall _ _)
          lbase_range_table (Z.to_nat j)) as H.
        cbn beta in H. rewrite Z2Nat.id in H by lia.
        specialize (H ltac:(apply in_seq; lia)).
        apply andb_prop in H as [H1 H2].
        apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
      unfold LeafShape.
      rewrite op_mkCodeT_id by lia.
      rewrite val_mkCodeT_id by exact Hlb256.
      split; [exact Hop3|].
      split; [intro Hd; discriminate Hd|].
      split; [lia|].
      split; [exact Hlb256|].
      split; [exact H15|].
      split;
        [intros _ H16; exact (len_valb_sound (lext j) (lbase j) Hjv H16)|].
      apply live_valb_sound.
      pose proof (table_fact _ 31%nat j lbase_live_table ltac:(lia)) as Hlv.
      cbn beta in Hlv. rewrite Z2Nat.id in Hlv by lia. exact Hlv.
    + (* the end-of-block symbol 256: the 32+64 marker *)
      apply marker_leafshape; [lia | |].
      * vm_compute. discriminate.
      * vm_compute. reflexivity.
Qed.

Lemma here_leafshape_dists : forall c st,
  x_match c = 0 -> x_base c = dbase -> x_extra c = dext ->
  (forall s, 0 <= x_work c s <= 31) ->
  LeafShape CT_DISTS (it_here c st).
Proof.
  intros c st Hm Hb He Hw. unfold it_here. rewrite Hm, Hb, He.
  pose proof (Hw (s_sym st)) as Hws.
  replace (Z.ltb (x_work c (s_sym st) + 1) 0) with false
    by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.leb 0 (x_work c (s_sym st))) with true
    by (symmetry; apply Z.leb_le; lia).
  set (j := x_work c (s_sym st) - 0).
  assert (Hj : 0 <= j <= 31) by (unfold j; lia).
  destruct (leaf_opb_sound CT_DISTS (dext j) (dext_leaf j Hj))
    as (Hop3 & Hnz & H15 & Hrng).
  unfold LeafShape.
  rewrite op_mkCodeT_id by lia.
  split; [exact Hop3|].
  split; [exact Hnz|].
  split; [lia|].
  assert (Hdb256 : 0 <= dbase j < 65536).
  { pose proof (table_fact _ 32%nat j dbase_range_table ltac:(lia)) as Hr2.
    cbn beta in Hr2. rewrite Z2Nat.id in Hr2 by lia.
    apply andb_prop in Hr2 as [Hr2a Hr2b].
    apply Z.leb_le in Hr2a. apply Z.ltb_lt in Hr2b. lia. }
  rewrite val_mkCodeT_id by exact Hdb256.
  split; [lia|].
  split; [exact H15|].
  split; [intros Hd; exfalso; vm_compute in Hd; discriminate Hd|].
  apply live_valb_sound.
  pose proof (table_fact _ 32%nat j dbase_live_table ltac:(lia)) as Hlv.
  cbn beta in Hlv. rewrite Z2Nat.id in Hlv by lia. exact Hlv.
Qed.


(** ** 6.  Payload-generic coverage below a position

    [ItGTblCover.CovBelow] with three generalisations: an arbitrary payload
    [Q] (here: leaf/pointer classification instead of a bits range), an
    arbitrary window base (sub-tables live at [next], the root at 0), and an
    arbitrary position scale ([2 ^ (S - w)]; the root walk has [S = 15], a
    sub-table walk [S = 15 - root]).  The two step lemmas below are
    [cov_step_short]/[cov_step_long] re-proved at that generality; the
    geometry is the SAME [unit_cross_*], reached by scaling both position
    inequalities up by [2 ^ (15 - S)]. *)

Definition GenBelow (Q : Code -> Prop) (w S : Z) (t : ztbl) (base P : Z)
  : Prop :=
  forall k, 0 <= k < 2 ^ w ->
    (zrev (Z.to_nat w) k + 1) * 2 ^ (S - w) <= P ->
    Q (t (base + k)).

Lemma gen_le : forall Q w S t base P P',
  GenBelow Q w S t base P' -> P <= P' -> GenBelow Q w S t base P.
Proof. intros Q w S t base P P' H Hle k Hk Hu. apply H; [exact Hk | lia]. Qed.

(** A fill hands back either the written entry or the old one. *)
Lemma fill_pointwise : forall n t bi incr h j,
  0 < incr ->
  it_fill n t bi incr h j = h \/ it_fill n t bi incr h j = t j.
Proof.
  intros n t bi incr h j Hincr.
  rewrite (it_fill_get n t bi incr h j Hincr).
  destruct ((bi <=? j) && (j <? bi + Z.of_nat n * incr)
            && ((j - bi) mod incr =? 0)); [left | right]; reflexivity.
Qed.

Lemma gen_fill : forall Q w S n t bi incr h base P,
  0 < incr -> Q h ->
  GenBelow Q w S t base P ->
  GenBelow Q w S (it_fill n t bi incr h) base P.
Proof.
  intros Q w S n t bi incr h base P Hincr Hh Hcov k Hk Hu.
  destruct (fill_pointwise n t bi incr h (base + k) Hincr) as [-> | ->];
    [exact Hh | apply Hcov; assumption].
Qed.

Lemma gen_tset : forall Q w S t i e base P,
  Q e ->
  GenBelow Q w S t base P ->
  GenBelow Q w S (tset t i e) base P.
Proof.
  intros Q w S t i e base P He Hcov k Hk Hu.
  destruct (Z.eq_dec (base + k) i) as [->|Hne].
  - rewrite tset_same. exact He.
  - rewrite tset_other by exact Hne. apply Hcov; assumption.
Qed.

(** SHORT step: a code of [len <= w] bits fills its residue class across the
    window, and every unit its position newly completes lies in that class. *)
Lemma gen_step_short : forall (Q : Code -> Prop) w S len huff t base here,
  1 <= len <= w -> w <= S -> S <= 15 -> 0 <= huff < 2 ^ len ->
  Q here ->
  GenBelow Q w S t base (zrev (Z.to_nat len) huff * 2 ^ (S - len)) ->
  GenBelow Q w S
    (it_fill (Z.to_nat (2 ^ w / 2 ^ len)) t (base + huff) (2 ^ len) here)
    base
    (zrev (Z.to_nat len) huff * 2 ^ (S - len) + 2 ^ (S - len)).
Proof.
  intros Q w S len huff t base here Hlen HwS HS Hhuff Hhere Hcov k Hk Hu.
  set (P := zrev (Z.to_nat len) huff * 2 ^ (S - len)) in *.
  pose proof (pow2_pos_z len ltac:(lia)) as Hpl.
  pose proof (pow2_pos_z w ltac:(lia)) as Hpw.
  pose proof (pow2_pos_z (15 - S) ltac:(lia)) as HpS.
  assert (Hpow : 2 ^ (w - len) * 2 ^ len = 2 ^ w).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hpow' : 2 ^ len * 2 ^ (w - len) = 2 ^ w) by (rewrite <- Hpow; ring).
  destruct (Z_le_gt_dec ((zrev (Z.to_nat w) k + 1) * 2 ^ (S - w)) P)
    as [Hold|Hnew].
  - exact (gen_fill Q w S _ t (base + huff) (2 ^ len) here base P
             ltac:(lia) Hhere Hcov k Hk Hold).
  - (* newly completed: [k] is in the write class *)
    assert (Hsc1 : 2 ^ (S - len) * 2 ^ (15 - S) = 2 ^ (15 - len))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hsc2 : 2 ^ (S - w) * 2 ^ (15 - S) = 2 ^ (15 - w))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (Hmod : k mod 2 ^ len = huff).
    { pose proof (unit_cross_short (Z.to_nat w) (Z.to_nat len) huff k
                    ltac:(lia) ltac:(lia) ltac:(lia)) as Hx.
      rewrite !to_nat_pow in Hx by lia.
      rewrite !Z2Nat.id in Hx by lia.
      apply Hx.
      - lia.
      - lia.
      - (* scale the strict inequality up by [2 ^ (15 - S)] *)
        rewrite <- Hsc1, <- Hsc2.
        assert (P * 2 ^ (15 - S)
                < ((zrev (Z.to_nat w) k + 1) * 2 ^ (S - w)) * 2 ^ (15 - S))
          by (apply Z.mul_lt_mono_pos_r; lia).
        unfold P in *. nia.
      - rewrite <- Hsc1, <- Hsc2.
        assert (((zrev (Z.to_nat w) k + 1) * 2 ^ (S - w)) * 2 ^ (15 - S)
                <= (P + 2 ^ (S - len)) * 2 ^ (15 - S))
          by (apply Z.mul_le_mono_pos_r; lia).
        unfold P in *. nia. }
    assert (Hdiv : k = huff + (k / 2 ^ len) * 2 ^ len).
    { pose proof (Zdiv.Z_div_mod_eq_full k (2 ^ len)) as He.
      rewrite Hmod in He. lia. }
    assert (Hq : 0 <= k / 2 ^ len < 2 ^ (w - len)).
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; [lia|]. rewrite Hpow'. lia. }
    assert (Hn : Z.of_nat (Z.to_nat (2 ^ w / 2 ^ len)) = 2 ^ (w - len)).
    { rewrite Z2Nat.id.
      - rewrite <- Hpow, Z.div_mul by lia. reflexivity.
      - apply Z.div_pos; lia. }
    replace (base + k) with ((base + huff) + (k / 2 ^ len) * 2 ^ len) by lia.
    replace ((k / 2 ^ len) * 2 ^ len)
      with (Z.of_nat (Z.to_nat (k / 2 ^ len)) * 2 ^ len)
      by (rewrite Z2Nat.id by lia; reflexivity).
    rewrite it_fill_hit; [exact Hhere | lia | lia].
Qed.

(** LONG step (root level only): the fill lands outside the window, and the
    only unit the position can newly complete is the code's own prefix,
    which the caller certifies (it holds the sub-table pointer). *)
Lemma gen_step_long : forall (Q : Code -> Prop) w S len huff t base n bi incr here,
  1 <= w -> w < len -> len <= S -> S <= 15 -> 0 <= huff < 2 ^ len ->
  base + 2 ^ w <= bi -> 0 < incr ->
  GenBelow Q w S t base (zrev (Z.to_nat len) huff * 2 ^ (S - len)) ->
  Q (t (base + huff mod 2 ^ w)) ->
  GenBelow Q w S (it_fill n t bi incr here) base
    (zrev (Z.to_nat len) huff * 2 ^ (S - len) + 2 ^ (S - len)).
Proof.
  intros Q w S len huff t base n bi incr here Hw Hwl Hl HS Hhuff Hbi Hincr
         Hcov Hlow k Hk Hu.
  set (P := zrev (Z.to_nat len) huff * 2 ^ (S - len)) in *.
  assert (Hmiss : it_fill n t bi incr here (base + k) = t (base + k)).
  { rewrite (it_fill_get _ _ _ _ _ (base + k) Hincr).
    replace (Z.leb bi (base + k)) with false
      by (symmetry; apply Z.leb_gt; lia).
    reflexivity. }
  rewrite Hmiss.
  destruct (Z_le_gt_dec ((zrev (Z.to_nat w) k + 1) * 2 ^ (S - w)) P)
    as [Hold|Hnew]; [apply Hcov; assumption|].
  assert (Hsc1 : 2 ^ (S - len) * 2 ^ (15 - S) = 2 ^ (15 - len))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hsc2 : 2 ^ (S - w) * 2 ^ (15 - S) = 2 ^ (15 - w))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  pose proof (pow2_pos_z (15 - S) ltac:(lia)) as HpS.
  assert (Hkl : k = huff mod 2 ^ w).
  { pose proof (unit_cross_long (Z.to_nat w) (Z.to_nat len) huff k
                  ltac:(lia) ltac:(lia) ltac:(lia)) as Hx.
    rewrite !to_nat_pow in Hx by lia.
    rewrite !Z2Nat.id in Hx by lia.
    apply Hx.
    - lia.
    - lia.
    - rewrite <- Hsc1, <- Hsc2.
      assert (P * 2 ^ (15 - S)
              < ((zrev (Z.to_nat w) k + 1) * 2 ^ (S - w)) * 2 ^ (15 - S))
        by (apply Z.mul_lt_mono_pos_r; lia).
      unfold P in *. nia.
    - rewrite <- Hsc1, <- Hsc2.
      assert (((zrev (Z.to_nat w) k + 1) * 2 ^ (S - w)) * 2 ^ (15 - S)
              <= (P + 2 ^ (S - len)) * 2 ^ (15 - S))
        by (apply Z.mul_le_mono_pos_r; lia).
      unfold P in *. nia. }
  rewrite Hkl. exact Hlow.
Qed.


(** ** 7.  The weighted remaining mass, in position units

    [wmass n l cnt = sum_{j=l}^{l+n-1} cnt j * 2 ^ (15 - j)] — the same sum
    as [it_mass] but with n-independent weights, so prefixes and suffixes
    split cleanly.  The guard clause of the ledger uses it to say "the codes
    short enough for the open sub-table still cover the rest of the unit". *)

Fixpoint wmass (n : nat) (l : Z) (cnt : zarr) : Z :=
  match n with
  | O => 0
  | S k => cnt l * 2 ^ (15 - l) + wmass k (l + 1) cnt
  end.

Lemma wmass_it_mass : forall n l cnt,
  l + Z.of_nat n <= 16 ->
  wmass n l cnt = it_mass n l cnt * 2 ^ (16 - l - Z.of_nat n).
Proof.
  induction n as [|k IH]; intros l cnt Hl; cbn [wmass it_mass]; [ring|].
  rewrite Nat2Z.inj_succ in Hl.
  rewrite (IH (l + 1) cnt) by lia.
  replace (16 - (l + 1) - Z.of_nat k) with (16 - l - Z.of_nat (S k)) by lia.
  replace (15 - l) with (Z.of_nat k + (16 - l - Z.of_nat (S k))) by lia.
  rewrite Z.pow_add_r by lia.
  ring.
Qed.

Lemma wmass_ext : forall n l a b,
  (forall j, l <= j < l + Z.of_nat n -> a j = b j) ->
  wmass n l a = wmass n l b.
Proof.
  induction n as [|k IH]; intros l a b H; [reflexivity|].
  cbn [wmass]. rewrite (H l) by lia.
  f_equal. apply IH. intros j Hj. apply H. lia.
Qed.

Lemma wmass_zero_on : forall n l cnt,
  (forall j, l <= j < l + Z.of_nat n -> cnt j = 0) ->
  wmass n l cnt = 0.
Proof.
  induction n as [|k IH]; intros l cnt H; [reflexivity|].
  cbn [wmass]. rewrite (H l) by lia.
  rewrite (IH (l + 1) cnt) by (intros j Hj; apply H; lia). ring.
Qed.

Lemma wmass_nonneg : forall n l cnt,
  (forall j, l <= j < l + Z.of_nat n -> 0 <= cnt j) ->
  0 <= wmass n l cnt.
Proof.
  induction n as [|k IH]; intros l cnt H; cbn [wmass]; [lia|].
  assert (0 <= cnt l) by (apply H; lia).
  assert (0 <= wmass k (l + 1) cnt) by (apply IH; intros j Hj; apply H; lia).
  assert (0 < 2 ^ (15 - l) \/ 2 ^ (15 - l) = 0) as [Hp|Hp].
  { destruct (Z_le_gt_dec 0 (15 - l)) as [Hle|Hgt];
      [left; apply Z.pow_pos_nonneg; lia
      |right; apply Z.pow_neg_r; lia]. }
  - nia.
  - nia.
Qed.

Lemma wmass_split : forall a b l cnt,
  wmass (a + b)%nat l cnt = wmass a l cnt + wmass b (l + Z.of_nat a) cnt.
Proof.
  induction a as [|k IH]; intros b l cnt.
  - cbn [Nat.add wmass]. replace (l + Z.of_nat 0) with l by lia. ring.
  - cbn [Nat.add wmass]. rewrite (IH b (l + 1) cnt).
    replace (l + 1 + Z.of_nat k) with (l + Z.of_nat (S k)) by lia. ring.
Qed.

Lemma wmass_snoc : forall n l cnt,
  wmass (S n) l cnt = wmass n l cnt + cnt (l + Z.of_nat n) * 2 ^ (15 - (l + Z.of_nat n)).
Proof.
  intros n l cnt.
  replace (S n) with (n + 1)%nat by lia.
  rewrite wmass_split. cbn [wmass]. ring.
Qed.

Lemma wmass_dec : forall n l cnt j,
  l <= j < l + Z.of_nat n ->
  wmass n l (zset cnt j (cnt j - 1)) = wmass n l cnt - 2 ^ (15 - j).
Proof.
  induction n as [|k IH]; intros l cnt j Hj.
  - exfalso. cbn in Hj. lia.
  - destruct (Z.eq_dec j l) as [->|Hne].
    + cbn [wmass]. rewrite zset_same.
      rewrite (wmass_ext k (l + 1) (zset cnt l (cnt l - 1)) cnt)
        by (intros i Hi; apply zset_other; lia).
      ring.
    + cbn [wmass]. rewrite (zset_other cnt j (cnt j - 1) l) by lia.
      rewrite Nat2Z.inj_succ in Hj.
      rewrite (IH (l + 1) cnt j) by lia. ring.
Qed.

(** ** 8.  [it_subsz] sizes the window to the remaining short-enough mass

    The C's sizing loop stops either at the ceiling ([curr + drop = max]) or
    when the counted mass of lengths in [(drop, drop+curr]] fills the whole
    remaining unit ([left <= 0]) — which is what makes "a same-prefix code
    longer than the window" impossible under sortedness. *)

Lemma it_subsz_covers_go : forall fuel cnt drop mx curr left,
  0 <= drop -> 1 <= curr -> drop + curr <= 15 -> mx <= 15 ->
  mx - drop - curr <= Z.of_nat fuel ->
  left * 2 ^ (15 - drop - curr)
    = 2 ^ (15 - drop) - wmass (Z.to_nat (curr - 1)) (drop + 1) cnt ->
  (let r := it_subsz fuel cnt drop mx curr left in
   mx <= drop + r \/
   2 ^ (15 - drop) <= wmass (Z.to_nat r) (drop + 1) cnt).
Proof.
  induction fuel as [|f IH]; intros cnt drop mx curr left Hd Hc Hdc Hmx Hfu Hinv;
    cbv zeta; cbn [it_subsz].
  - left. cbn in Hfu. lia.
  - destruct (Z.ltb (curr + drop) mx) eqn:E1;
      [|left; apply Z.ltb_ge in E1; lia].
    apply Z.ltb_lt in E1.
    destruct (Z.leb (left - cnt (curr + drop)) 0) eqn:E2.
    + (* the window is full: the subtracted mass reached the unit *)
      right. apply Z.leb_le in E2.
      assert (Hsn : wmass (Z.to_nat curr) (drop + 1) cnt
                    = wmass (Z.to_nat (curr - 1)) (drop + 1) cnt
                      + cnt (curr + drop) * 2 ^ (15 - (curr + drop))).
      { replace (Z.to_nat curr) with (S (Z.to_nat (curr - 1))) by lia.
        rewrite wmass_snoc.
        replace (drop + 1 + Z.of_nat (Z.to_nat (curr - 1)))
          with (curr + drop) by lia.
        reflexivity. }
      rewrite Hsn.
      assert (Hscale : (left - cnt (curr + drop)) * 2 ^ (15 - drop - curr)
                       <= 0).
      { apply Z.mul_nonpos_nonneg; [lia|].
        apply Z.pow_nonneg. lia. }
      replace (15 - (curr + drop)) with (15 - drop - curr) by lia.
      nia.
    + apply Z.leb_gt in E2.
      rewrite Nat2Z.inj_succ in Hfu.
      apply (IH cnt drop mx (curr + 1) ((left - cnt (curr + drop)) * 2));
        [lia | lia | | lia | lia |].
      * (* drop + curr + 1 <= 15: from curr + drop < mx <= ... *)
        lia.
      * (* the scaled identity advances by one snoc *)
        replace (Z.to_nat (curr + 1 - 1)) with (S (Z.to_nat (curr - 1)))
          by lia.
        rewrite wmass_snoc.
        replace (drop + 1 + Z.of_nat (Z.to_nat (curr - 1)))
          with (curr + drop) by lia.
        replace (15 - drop - (curr + 1)) with (15 - drop - curr - 1) by lia.
        replace (15 - (curr + drop)) with (15 - drop - curr) by lia.
        assert (Hp : 2 ^ (15 - drop - curr) = 2 * 2 ^ (15 - drop - curr - 1)).
        { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
        nia.
Qed.

(** The call-site form: the result abstracted behind an equation, so an
    instantiation never materialises the [it_subsz] term in a goal. *)
Lemma it_subsz_covers : forall fuel cnt drop mx curr left r,
  r = it_subsz fuel cnt drop mx curr left ->
  0 <= drop -> 1 <= curr -> drop + curr <= 15 -> mx <= 15 ->
  mx - drop - curr <= Z.of_nat fuel ->
  left * 2 ^ (15 - drop - curr)
    = 2 ^ (15 - drop) - wmass (Z.to_nat (curr - 1)) (drop + 1) cnt ->
  mx <= drop + r \/
  2 ^ (15 - drop) <= wmass (Z.to_nat r) (drop + 1) cnt.
Proof.
  intros fuel cnt drop mx curr left r Hr Hd Hc Hdc Hmx Hfu Hinv.
  subst r.
  exact (it_subsz_covers_go fuel cnt drop mx curr left Hd Hc Hdc Hmx Hfu
           Hinv).
Qed.


(** ** 9.  Small bridges *)

Lemma root_entry_mono : forall ty root used used' e,
  used <= used' -> RootEntry ty root used e -> RootEntry ty root used' e.
Proof.
  intros ty root used used' e Hle [Hl | (Hb & Ho & Hv & Hlo & Hhi)];
    [left; exact Hl | right].
  split; [exact Hb|]. split; [exact Ho|]. split; [exact Hv|].
  split; [exact Hlo|]. lia.
Qed.

Lemma shiftr_range : forall h r len,
  0 <= r <= len -> 0 <= h < 2 ^ len ->
  0 <= Z.shiftr h r < 2 ^ (len - r).
Proof.
  intros h r len Hr Hh.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (pow2_pos_z r ltac:(lia)).
  pose proof (pow2_pos_z (len - r) ltac:(lia)).
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia.
    replace (r + (len - r)) with len by lia. lia.
Qed.

(** The bit-reversed position of a long code splits at the root: the unit
    index is the reversed prefix, the intra-unit index the reversed rest. *)
Lemma zrev_decomp : forall root len huff,
  1 <= root < len -> len <= 15 -> 0 <= huff < 2 ^ len ->
  zrev (Z.to_nat len) huff
  = zrev (Z.to_nat root) (huff mod 2 ^ root) * 2 ^ (len - root)
    + zrev (Z.to_nat (len - root)) (Z.shiftr huff root).
Proof.
  intros root len huff Hr Hl Hh.
  pose proof (pow2_pos_z root ltac:(lia)).
  assert (Hmodr : 0 <= huff mod 2 ^ root < 2 ^ root)
    by (apply Z.mod_pos_bound; lia).
  assert (Hto : (Z.to_nat len = Z.to_nat root + Z.to_nat (len - root))%nat)
    by lia.
  rewrite Hto.
  replace huff
    with (huff mod 2 ^ root
          + (huff / 2 ^ root) * 2 ^ Z.of_nat (Z.to_nat root)) at 1
    by (rewrite to_nat_pow by lia;
        pose proof (Z.div_mod huff (2 ^ root) ltac:(lia)); lia).
  rewrite zrev_split by (rewrite to_nat_pow by lia; exact Hmodr).
  rewrite to_nat_pow by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  reflexivity.
Qed.

(** ** 10.  The ledger

    Everything the endpoint needs, carried through the loop next to the
    landed [CovInv].  Phase 1 (no sub-table yet): the used extent is the
    root block.  Phase 2: the sub-region tiles as
    [[2^root, next) ++ [next, next + 2^curr)] with the closed part fully
    covered, the open window covered below its intra-unit position, the
    open window's pointer already classified, and the guard — the remaining
    mass short enough for this window still covers the rest of the unit —
    which is what makes an over-long same-prefix code impossible. *)

Definition UnitStart (root low : Z) : Z :=
  zrev (Z.to_nat root) low * 2 ^ (15 - root).

Definition SubLedger (ty : Z) (c : ItCtx) (cnt0 : zarr) (st : ItSt) : Prop :=
  GenBelow (RootEntry ty (x_root c) (s_used st)) (x_root c) 15 (s_tbl st) 0
           (Pos (it_mass 15%nat 1 cnt0) st)
  /\ ( (s_drop st = 0 /\ s_used st = 2 ^ x_root c /\ s_next st = 0)
       \/ (s_drop st = x_root c
           /\ 1 <= s_curr st <= 15 - x_root c
           /\ s_used st = s_next st + 2 ^ s_curr st
           /\ 2 ^ x_root c <= s_next st
           /\ s_used st <= 65535
           /\ (forall i, 2 ^ x_root c <= i < s_next st ->
                 SubEntry ty (x_root c) (s_tbl st i))
           /\ GenBelow (SubEntry ty (x_root c)) (s_curr st) (15 - x_root c)
                (s_tbl st) (s_next st)
                (Pos (it_mass 15%nat 1 cnt0) st
                 - UnitStart (x_root c) (s_low st))
           /\ RootEntry ty (x_root c) (s_used st) (s_tbl st (s_low st))
           /\ UnitStart (x_root c) (s_low st) + 2 ^ (15 - x_root c)
              <= Pos (it_mass 15%nat 1 cnt0) st
                 + wmass (Z.to_nat (x_root c + s_curr st)) 1 (s_count st)) ).

(** ** 11.  The ledger survives one fall-through trip *)

Lemma ledger_step_cont : forall ty c cnt0 st st',
  ty = x_type c ->
  (x_type c = CT_LENS \/ x_type c = CT_DISTS \/ x_max c <= x_root c) ->
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  LeafShape ty (it_here c st) ->
  it_step c st = ItCont st' ->
  SubLedger ty c cnt0 st'.
Proof.
  intros ty c cnt0 st st' Hcty Hty Hctx Hinv Hled Hherel Hstep.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof Hinv as Hinv2.
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).
  destruct Hled as (HrootB & Hledph).
  unfold it_step in Hstep. cbv zeta in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1)) in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  (* --- the counts after the trip --- *)
  assert (Hcnt1 : forall l, 1 <= l <= 15 ->
            cnt1 l = (if Z.ltb l (s_len st) then 0
                      else if Z.eqb l (s_len st)
                           then sw_offs cnt0 (s_len st) + cnt0 (s_len st)
                                - (s_sym st + 1)
                           else cnt0 l)).
  { intros l Hl. unfold cnt1, zset.
    destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
    - rewrite (Hcnt (s_len st) ltac:(lia)), Z.ltb_irrefl, Z.eqb_refl. lia.
    - rewrite (Hcnt l Hl).
      destruct (Z.ltb l (s_len st)); [reflexivity|].
      destruct (Z.eqb_spec l (s_len st)); [contradiction|reflexivity]. }
  assert (Hcnt1nn : forall l, 1 <= l <= 15 -> 0 <= cnt1 l).
  { intros l Hl. rewrite (Hcnt1 l Hl).
    destruct (Z.ltb l (s_len st)); [lia|].
    destruct (Z.eqb_spec l (s_len st)); [lia | apply Hnn; lia]. }
  (* --- the position advances by one code's worth --- *)
  assert (Hpos1 : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                  = Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)).
  { unfold cnt1. apply pos_advance. lia. }
  (* --- the reversed counter advanced --- *)
  assert (Hhuff' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
    by (rewrite (to_nat_pow (s_len st) ltac:(lia)); exact Hhuff).
  pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st)
                ltac:(lia) Hhuff') as Hinc.
  rewrite (Z2Nat.id (s_len st)) in Hinc by lia.
  assert (Hadv : 0 <= huff1 < 2 ^ s_len st
                 /\ zrev (Z.to_nat (s_len st)) huff1
                    = zrev (Z.to_nat (s_len st)) (s_huff st) + 1).
  { destruct Hinc as [[Hw Hz] | Hgood]; [exfalso | exact Hgood].
    assert (Hp15 : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1 = 2 ^ 15).
    { rewrite Hpos1, Hpos, Hz.
      replace ((2 ^ s_len st - 1) * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
        with (2 ^ s_len st * 2 ^ (15 - s_len st)) by ring.
      rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hmzero : it_mass 15%nat 1 cnt1 = 0).
    { assert (0 <= it_mass 15%nat 1 cnt1)
        by (apply it_mass_nonneg; intros j Hj; apply Hcnt1nn; cbn in Hj; lia).
      lia. }
    assert (Hallz : forall l, 1 <= l <= 15 -> cnt1 l = 0).
    { intros l Hl. apply (it_mass_zero_inv 15%nat 1 cnt1);
        [ intros j Hj; apply Hcnt1nn; cbn in Hj; lia
        | exact Hmzero | cbn; lia ]. }
    assert (Hcl : 0 < cnt0 (s_len st)) by lia.
    assert (Hmxlen : x_max c = s_len st).
    { destruct (Z_le_gt_dec (x_max c) (s_len st)) as [Hle|Hgt].
      - destruct (Z.eq_dec (x_max c) (s_len st)) as [->|Hne]; [reflexivity|].
        exfalso. rewrite (Hmxz (s_len st) ltac:(lia)) in Hcl. lia.
      - exfalso.
        assert (cnt1 (x_max c) = cnt0 (x_max c)).
        { rewrite (Hcnt1 (x_max c) ltac:(lia)).
          destruct (Z.ltb_spec (x_max c) (s_len st)); [lia|].
          destruct (Z.eqb_spec (x_max c) (s_len st)); [lia|reflexivity]. }
        rewrite (Hallz (x_max c) ltac:(lia)) in *. now apply Hmxnz. }
    assert (Hhit : Z.eqb (cnt1 (s_len st)) 0 = true)
      by (apply Z.eqb_eq, Hallz; lia).
    rewrite Hhit, Hmxlen, Z.eqb_refl in Hstep. cbn [andb] in Hstep.
    discriminate Hstep. }
  destruct Hadv as [Hhuff1 Hzadv].
  assert (Hposlink : forall len1, s_len st <= len1 -> len1 <= 15 ->
            it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
            = zrev (Z.to_nat len1) huff1 * 2 ^ (15 - len1)).
  { intros len1 Hge H15.
    rewrite (pos_link_widen (s_len st) len1 huff1 ltac:(lia) ltac:(lia)
               ltac:(lia)).
    rewrite Hpos1, Hpos, Hzadv. ring. }
  assert (Hlowmod : Z.land huff1 (x_mask c) = huff1 mod 2 ^ x_root c).
  { rewrite Hmask. apply land_ones_mod. lia. }
  assert (Hnotsent : Z.land huff1 (x_mask c) <> 4294967295).
  { rewrite Hlowmod.
    assert (Ha : 0 <= huff1 mod 2 ^ x_root c < 2 ^ x_root c)
      by (apply Z.mod_pos_bound, pow2_pos_z; lia).
    assert (Hb2 : 2 ^ x_root c <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    assert (H15c : (2:Z) ^ 15 = 32768) by reflexivity.
    lia. }
  assert (Hf0 : 0 <= Z.shiftl 1 (s_curr st))
    by (apply (proj2 (Z.shiftl_nonneg 1 (s_curr st))); lia).
  assert (Hlenmx : s_len st <= x_max c).
  { destruct (Z_le_gt_dec (s_len st) (x_max c)) as [?|Hgx];
      [assumption|exfalso].
    rewrite (Hmxz (s_len st) ltac:(lia)) in HwinU. lia. }
  (* --- guard-derived width bound, in the sub-table phase --- *)
  assert (Hlenfit : s_drop st = x_root c ->
            s_low st = s_huff st mod 2 ^ x_root c ->
            x_root c < s_len st ->
            s_len st <= x_root c + s_curr st).
  { intros Hd Hlow Hrl.
    destruct Hledph as [(Hd0 & _ & _) | (Hd2 & Hcb & Hue & Hnx2 & Hu16 & Hcl
                                         & Hopen & Hrp & Hguard)];
      [exfalso; lia|].
    destruct (Z_le_gt_dec (s_len st) (x_root c + s_curr st)) as [Hok|Hbad];
      [exact Hok | exfalso].
    (* all short-enough counts are zero, so the guard puts the position past
       the unit — but the current code still sits inside it *)
    assert (Hwz : wmass (Z.to_nat (x_root c + s_curr st)) 1 (s_count st) = 0).
    { apply wmass_zero_on. intros j Hj.
      rewrite (Hcnt j ltac:(lia)).
      replace (Z.ltb j (s_len st)) with true
        by (symmetry; apply Z.ltb_lt; lia).
      reflexivity. }
    rewrite Hwz in Hguard.
    (* the intra-unit position of the current code *)
    assert (Hdec := zrev_decomp (x_root c) (s_len st) (s_huff st)
                      ltac:(lia) ltac:(lia) Hhuff).
    assert (Hhi : 0 <= Z.shiftr (s_huff st) (x_root c)
                     < 2 ^ (s_len st - x_root c))
      by (apply shiftr_range; lia).
    assert (Hzr : zrev (Z.to_nat (s_len st - x_root c))
                    (Z.shiftr (s_huff st) (x_root c))
                  < 2 ^ (s_len st - x_root c)).
    { pose proof (zrev_lt (Z.to_nat (s_len st - x_root c))
                    (Z.shiftr (s_huff st) (x_root c))) as Hzl.
      rewrite to_nat_pow in Hzl by lia. exact Hzl. }
    assert (Hsplit2 : 2 ^ (s_len st - x_root c) * 2 ^ (15 - s_len st)
                      = 2 ^ (15 - x_root c))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    pose proof (pow2_pos_z (15 - s_len st) ltac:(lia)).
    (* Pos < UnitStart + 2^(15-root) *)
    unfold UnitStart in Hguard.
    rewrite Hlow in Hguard.
    rewrite Hpos, Hdec in Hguard. clear -Hguard Hzr Hsplit2 Hhi H; nia. }
  (* --- the fill, once, and its two phase shapes --- *)
  set (tblF := it_fill
                 (Z.to_nat (Z.shiftl 1 (s_curr st)
                            / Z.shiftl 1 (s_len st - s_drop st)))
                 (s_tbl st)
                 (s_next st + Z.shiftr (s_huff st) (s_drop st))
                 (Z.shiftl 1 (s_len st - s_drop st))
                 (it_here c st)) in *.
  assert (Hbits_here : c_bits (it_here c st) = s_len st - s_drop st).
  { apply bits_here_val.
    destruct Hphase as [(Hd & _) | (Hd & Hrl & _)]; rewrite Hd; lia. }
  (* the root-level payload carried by every root-region write *)
  assert (Hlow_rng : s_drop st = x_root c ->
            s_low st = s_huff st mod 2 ^ x_root c ->
            0 <= s_low st < 2 ^ x_root c).
  { intros _ Hlow. rewrite Hlow.
    apply Z.mod_pos_bound. apply pow2_pos_z. lia. }
  (* ------------------------------------------------------------------ *)
  destruct (Z.eqb (cnt1 (s_len st)) 0) eqn:Hhit.
  - (* current length exhausted: the next window's length takes over *)
    apply Z.eqb_eq in Hhit.
    destruct (Z.eqb (s_len st) (x_max c)) eqn:Hmxeq;
      cbn [andb] in Hstep; [discriminate Hstep|].
    apply Z.eqb_neq in Hmxeq.
    (* the next window: as in the landed walk *)
    assert (Hbook : exists l1, s_len st < l1 <= 15
              /\ sw_offs cnt0 l1 = s_sym st + 1
              /\ 0 < cnt0 l1
              /\ x_lens c (x_work c (s_sym st + 1)) = l1
              /\ (forall l, 1 <= l <= 15 ->
                    cnt1 l = (if Z.ltb l l1 then 0
                              else if Z.eqb l l1
                                   then sw_offs cnt0 l1 + cnt0 l1
                                        - (s_sym st + 1)
                                   else cnt0 l))).
    { rewrite (Hcnt1 (s_len st) ltac:(lia)), Z.ltb_irrefl, Z.eqb_refl in Hhit.
      assert (Hend : s_sym st + 1 = sw_offs cnt0 (s_len st) + cnt0 (s_len st))
        by lia.
      assert (Hlt : s_sym st + 1 < sw_offs cnt0 15 + cnt0 15).
      { destruct (Z_lt_le_dec (s_sym st + 1) (sw_offs cnt0 15 + cnt0 15))
          as [H|H]; [exact H | exfalso].
        destruct (cov_exhausted c cnt0 (s_len st) (s_sym st) Hctx2 ltac:(lia)
                    ltac:(lia) ltac:(lia)) as [_ Hmxl]. congruence. }
      destruct (cov_next_window c cnt0 (s_len st) (s_sym st) Hctx2 ltac:(lia)
                  ltac:(lia) Hend Hlt) as [l1 (Hl1 & Hstart & Hpos1' & Hlensym
                                              & Hgap)].
      exists l1. split; [lia|]. split; [exact Hstart|]. split; [lia|].
      split; [exact Hlensym|].
      intros l Hl. rewrite (Hcnt1 l Hl).
      destruct (Z.ltb_spec l l1) as [Hll|Hll].
      - destruct (Z.ltb_spec l (s_len st)) as [H1|H1]; [reflexivity|].
        destruct (Z.eqb_spec l (s_len st)) as [->|H2]; [lia|].
        rewrite (Hgap l ltac:(lia)). reflexivity.
      - destruct (Z.eqb_spec l l1) as [->|H2].
        + destruct (Z.ltb_spec l1 (s_len st)) as [H3|H3]; [lia|].
          destruct (Z.eqb_spec l1 (s_len st)) as [H4|H4]; [lia|]. clear -Hstart; lia.
        + destruct (Z.ltb_spec l (s_len st)) as [H3|H3]; [clear -Hl1 Hll H3; lia|].
          destruct (Z.eqb_spec l (s_len st)) as [H4|H4]; [clear -Hl1 Hll H4; lia|reflexivity]. }
    destruct Hbook as [l1 (Hl1 & Hstart & Hcl1 & Hlensym & Hcnt1')].
    rewrite Hlensym in Hstep.
    destruct (Z.ltb (x_root c) l1) eqn:Hgt.
    + apply Z.ltb_lt in Hgt.
      destruct (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) eqn:Hsame;
        cbn [andb negb] in Hstep.
      * (* SAME PREFIX: a sub-table fill *)
        apply Z.eqb_eq in Hsame.
        injection Hstep as Hst'. subst st'.
        destruct Hphase
          as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)];
          [exfalso; rewrite Hlow in Hsame; exact (Hnotsent Hsame)|].
        destruct Hledph
          as [(Hd0 & _) | (Hd2 & Hcb & Hue & Hnx2 & Hu16 & Hcl & Hopen
                           & Hrp & Hguard)];
          [exfalso; lia|].
        pose proof (Hlow_rng Hd Hlow) as Hlr2.
        assert (Hfit : s_len st <= x_root c + s_curr st)
          by (apply Hlenfit; assumption).
        set (hi := Z.shiftr (s_huff st) (x_root c)) in *.
        assert (Hhi : 0 <= hi < 2 ^ (s_len st - x_root c))
          by (unfold hi; apply shiftr_range; lia).
        assert (Hdec : zrev (Z.to_nat (s_len st)) (s_huff st)
                = zrev (Z.to_nat (x_root c)) (s_huff st mod 2 ^ x_root c)
                    * 2 ^ (s_len st - x_root c)
                  + zrev (Z.to_nat (s_len st - x_root c)) hi)
          by (unfold hi; apply zrev_decomp; [lia|lia|exact Hhuff]).
        assert (Hsc3 : 2 ^ (s_len st - x_root c) * 2 ^ (15 - s_len st)
                       = 2 ^ (15 - x_root c))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (HUS : Pos (it_mass 15%nat 1 cnt0) st
                        - UnitStart (x_root c) (s_low st)
                      = zrev (Z.to_nat (s_len st - x_root c)) hi
                          * 2 ^ (15 - s_len st)).
        { unfold UnitStart. rewrite Hlow, Hpos, Hdec. clear -Hsc3; nia. }
        assert (HF2 : tblF
                 = it_fill (Z.to_nat (2 ^ s_curr st
                                      / 2 ^ (s_len st - x_root c)))
                     (s_tbl st) (s_next st + hi)
                     (2 ^ (s_len st - x_root c)) (it_here c st)).
        { unfold tblF, hi. rewrite Hd, !shiftl1 by lia. reflexivity. }
        assert (Hmiss_low : forall j, j < s_next st -> tblF j = s_tbl st j).
        { intros j Hj. rewrite HF2.
           rewrite (it_fill_get _ _ _ _ _ j) by (apply pow2_pos_z; lia).
           replace (Z.leb (s_next st + hi) j) with false
             by (symmetry; apply Z.leb_gt; lia).
           reflexivity. }
        unfold SubLedger, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min
             s_count s_tbl].
        split.
        { replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
             with (zrev (Z.to_nat (s_len st)) (s_huff st)
                     * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
             by (unfold Pos in Hpos, Hpos1; clear -Hpos Hpos1; lia).
           rewrite HF2.
           apply gen_step_long;
             [lia | lia | lia | lia | exact Hhuff | lia
              | apply pow2_pos_z; lia | |].
           - unfold Pos in Hpos. rewrite <- Hpos. exact HrootB.
           - replace (0 + s_huff st mod 2 ^ x_root c) with (s_low st)
               by (rewrite Hlow; lia).
             exact Hrp. }
        right.
        split; [exact Hd|].
        split; [exact Hcb|].
        split; [exact Hue|].
        split; [exact Hnx2|].
        split; [exact Hu16|].
        split.
        { intros i Hi. rewrite Hmiss_low by lia. apply Hcl. exact Hi. }
        split.
        { replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                    - UnitStart (x_root c) (s_low st))
             with (zrev (Z.to_nat (s_len st - x_root c)) hi
                     * 2 ^ ((15 - x_root c) - (s_len st - x_root c))
                   + 2 ^ ((15 - x_root c) - (s_len st - x_root c)))
             by (replace ((15 - x_root c) - (s_len st - x_root c))
                   with (15 - s_len st) by lia;
                 unfold Pos in Hpos1, HUS; clear -Hpos1 HUS; lia).
           rewrite HF2.
           apply gen_step_short; [lia | lia | lia | exact Hhi | |].
           - split; [exact Hherel|]. rewrite Hbits_here, Hd. lia.
           - replace ((15 - x_root c) - (s_len st - x_root c))
               with (15 - s_len st) by lia.
             rewrite <- HUS. exact Hopen. }
        split.
        { rewrite Hmiss_low by lia. exact Hrp. }
        { assert (Hwd : wmass (Z.to_nat (x_root c + s_curr st)) 1 cnt1
                   = wmass (Z.to_nat (x_root c + s_curr st)) 1 (s_count st)
                     - 2 ^ (15 - s_len st)).
           { unfold cnt1. apply wmass_dec. lia. }
           rewrite Hwd.
           unfold Pos in Hguard, Hpos1. lia. }
      * (* NEW WINDOW *)
        apply Z.eqb_neq in Hsame.
        match type of Hstep with
        | (if it_enough _ (_ + Z.shiftl 1 ?cv) then _ else _) = _ =>
            remember cv as curr' eqn:Hcurr'
        end.
        match type of Hstep with
        | (if ?b then _ else _) = _ => remember b as en eqn:Hen; destruct en
        end; [discriminate Hstep|].
        injection Hstep as Hst'. subst st'.
        replace (if Z.eqb (s_drop st) 0 then x_root c else s_drop st)
          with (x_root c) in *
          by (destruct Hphase as [(Hd & _) | (Hd & _)]; rewrite Hd;
              [ rewrite Z.eqb_refl; reflexivity
              | replace (Z.eqb (x_root c) 0) with false
                  by (symmetry; apply Z.eqb_neq; lia); reflexivity ]).
        assert (HL1mx : l1 <= x_max c) by (destruct (Z_le_gt_dec l1 (x_max c)) as [?|Hgx2]; [assumption|exfalso]; rewrite (Hmxz l1 ltac:(lia)) in Hcl1; lia).
        assert (Hcb' : l1 - x_root c <= curr' /\ 1 <= curr' <= 15 - x_root c).
        { pose proof (it_subsz_bounds 16%nat cnt1 (x_root c) (x_max c)
                        (l1 - x_root c) (Z.shiftl 1 (l1 - x_root c))) as HB.
           rewrite <- Hcurr' in HB. clear -HB Hgt HL1mx Hmx; lia. }
        assert (Hcap : s_used st + Z.shiftl 1 curr' <= 852).
        { destruct Hty as [HtL|[HtD|Hcap3]];
            [ rewrite HtL in Hen | rewrite HtD in Hen
            | exfalso; clear -Hcap3 Hgt HL1mx; lia ];
            unfold it_enough in Hen; cbn in Hen;
            symmetry in Hen; rewrite ?orb_false_r in Hen;
            apply Z.ltb_ge in Hen;
            unfold ENOUGH_LENS, ENOUGH_DISTS in Hen; lia. }
        assert (Hcnt1z : forall l, 1 <= l < l1 -> cnt1 l = 0).
        { intros l Hll.
          rewrite (Hcnt1' l ltac:(clear -Hll Hl1; lia)).
          replace (Z.ltb l l1) with true
            by (symmetry; apply Z.ltb_lt; clear -Hll; lia).
          reflexivity. }
        assert (Hcnt1hi : forall l, x_max c < l <= 15 -> cnt1 l = 0).
        { intros l Hl. rewrite (Hcnt1 l ltac:(clear -Hl Hmx; lia)).
          replace (Z.ltb l (s_len st)) with false
            by (symmetry; apply Z.ltb_ge; clear -Hl Hlenmx; lia).
          replace (Z.eqb l (s_len st)) with false
            by (symmetry; apply Z.eqb_neq; clear -Hl Hlenmx; lia).
          apply Hmxz. clear -Hl Hmx. lia. }
        assert (Hgd : x_max c <= x_root c + curr'
                \/ 2 ^ (15 - x_root c)
                   <= wmass (Z.to_nat curr') (x_root c + 1) cnt1).
        { assert (Hinv0 : Z.shiftl 1 (l1 - x_root c)
                     * 2 ^ (15 - x_root c - (l1 - x_root c))
                   = 2 ^ (15 - x_root c)
                     - wmass (Z.to_nat (l1 - x_root c - 1))
                         (x_root c + 1) cnt1).
           { rewrite shiftl1 by (clear -Hgt; lia).
              rewrite (wmass_zero_on (Z.to_nat (l1 - x_root c - 1))
                        (x_root c + 1) cnt1)
                by (intros j Hj; apply Hcnt1z; clear -Hj Hroot Hgt; lia).
              rewrite Z.sub_0_r.
              rewrite <- Z.pow_add_r by (clear -Hgt HL1mx Hmx; lia).
              f_equal. clear -Hgt; lia. }
           exact (it_subsz_covers 16%nat cnt1 (x_root c) (x_max c)
                    (l1 - x_root c) (Z.shiftl 1 (l1 - x_root c)) curr'
                    Hcurr' ltac:(clear -Hroot; lia) ltac:(clear -Hgt; lia)
                    ltac:(clear -HL1mx Hmx; lia) ltac:(clear -Hmx; lia)
                    ltac:(clear -Hmx Hgt Hroot HL1mx; lia) Hinv0). }
        clear Hcurr' Hen.
        assert (Hsh1 : Z.shiftl 1 curr' = 2 ^ curr') by (apply shiftl1; lia).
        pose proof Hlowmod as Hlow'.
        assert (Hlr1 : 0 <= huff1 mod 2 ^ x_root c < 2 ^ x_root c)
          by (apply Z.mod_pos_bound, pow2_pos_z; lia).
        assert (Hh1L : 0 <= huff1 < 2 ^ l1).
        { assert (Hpm : 2 ^ s_len st <= 2 ^ l1) by (apply Z.pow_le_mono_r; lia).
           clear -Hhuff1 Hpm; lia. }
        set (hi1 := Z.shiftr huff1 (x_root c)) in *.
        assert (Hh1r : 0 <= hi1 < 2 ^ (l1 - x_root c))
          by (unfold hi1; apply shiftr_range; lia).
        assert (Hdec1 : zrev (Z.to_nat l1) huff1
                = zrev (Z.to_nat (x_root c)) (huff1 mod 2 ^ x_root c)
                    * 2 ^ (l1 - x_root c)
                  + zrev (Z.to_nat (l1 - x_root c)) hi1)
          by (unfold hi1; apply zrev_decomp; [lia|lia|exact Hh1L]).
        assert (Hzr1 : 0 <= zrev (Z.to_nat (l1 - x_root c)) hi1
                       < 2 ^ (l1 - x_root c)).
        { pose proof (zrev_lt (Z.to_nat (l1 - x_root c)) hi1) as Hz1.
           pose proof (zrev_nonneg (Z.to_nat (l1 - x_root c)) hi1) as Hz2.
           rewrite to_nat_pow in Hz1 by lia. lia. }
        assert (Hsc1' : 2 ^ (l1 - x_root c) * 2 ^ (15 - l1)
                        = 2 ^ (15 - x_root c))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (HsPos : 0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
        assert (HsPos2 : 0 < 2 ^ (15 - l1)) by (apply pow2_pos_z; lia).
        set (K1 := zrev (Z.to_nat (x_root c)) (huff1 mod 2 ^ x_root c)) in *.
        set (i1 := zrev (Z.to_nat (l1 - x_root c)) hi1 * 2 ^ (15 - l1))
          in *.
        assert (HK1nn : 0 <= K1) by (unfold K1; apply zrev_nonneg).
        assert (Hi1b : 0 <= i1 /\ i1 + 2 ^ (15 - l1) <= 2 ^ (15 - x_root c)).
        { unfold i1. split; [apply Z.mul_nonneg_nonneg; lia|].
          replace (zrev (Z.to_nat (l1 - x_root c)) hi1 * 2 ^ (15 - l1)
                   + 2 ^ (15 - l1))
            with ((zrev (Z.to_nat (l1 - x_root c)) hi1 + 1) * 2 ^ (15 - l1))
            by ring.
          rewrite <- Hsc1'. apply Z.mul_le_mono_pos_r; lia. }
        assert (HPn : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                      = K1 * 2 ^ (15 - x_root c) + i1).
        { unfold K1, i1.
           rewrite (Hposlink l1 ltac:(lia) ltac:(lia)), Hdec1.
           rewrite Z.mul_add_distr_r, <- Z.mul_assoc, Hsc1'. reflexivity. }
        destruct Hphase
          as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)].
        -- (* the FIRST window: phase 1 opens phase 2 *)
        destruct Hledph
          as [(Hd0 & Hu0 & Hn0) | (Hd2 & _)]; [| exfalso; clear -Hd Hd2 Hroot; lia].
        assert (Hsh2 : Z.shiftl 1 (s_curr st) = 2 ^ s_curr st)
          by (apply shiftl1; clear -Hc Hroot; lia).
        (* the position lands on a unit edge: everything is a multiple *)
        assert (HM : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                     = (zrev (Z.to_nat (s_len st)) (s_huff st)
                        * 2 ^ (x_root c - s_len st)
                        + 2 ^ (x_root c - s_len st)) * 2 ^ (15 - x_root c)).
        { assert (Hsp : 2 ^ (x_root c - s_len st) * 2 ^ (15 - x_root c)
                        = 2 ^ (15 - s_len st))
            by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
          rewrite Z.mul_add_distr_r, <- Z.mul_assoc, Hsp.
          unfold Pos in Hpos, Hpos1. clear - Hpos Hpos1. lia. }
        assert (Hi10 : i1 = 0 /\ it_mass 15%nat 1 cnt0
                               - it_mass 15%nat 1 cnt1
                               = K1 * 2 ^ (15 - x_root c)).
        { set (M := zrev (Z.to_nat (s_len st)) (s_huff st)
                    * 2 ^ (x_root c - s_len st) + 2 ^ (x_root c - s_len st))
            in *.
          assert (HMK : (M - K1) * 2 ^ (15 - x_root c) = i1).
          { replace ((M - K1) * 2 ^ (15 - x_root c))
              with (M * 2 ^ (15 - x_root c) - K1 * 2 ^ (15 - x_root c))
              by ring.
            clear -HM HPn. lia. }
          assert (H0le : 0 <= M - K1).
          { destruct (Z_le_gt_dec 0 (M - K1)) as [?|Hneg]; [assumption|].
            exfalso.
            assert (Hng : (M - K1) * 2 ^ (15 - x_root c)
                    <= (-1) * 2 ^ (15 - x_root c))
              by (apply Z.mul_le_mono_pos_r; clear -Hneg HsPos; lia).
            clear -Hng HMK Hi1b HsPos. lia. }
          assert (Hlt1 : M - K1 < 1).
          { apply (mul_lt_cancel_r (M - K1) 1 (2 ^ (15 - x_root c)) HsPos).
            replace (1 * 2 ^ (15 - x_root c)) with (2 ^ (15 - x_root c))
              by ring.
            clear -HMK Hi1b HsPos2. lia. }
          assert (HMeq : M = K1) by lia.
          rewrite HMeq in HMK.
          replace ((K1 - K1) * 2 ^ (15 - x_root c)) with 0 in HMK by ring.
          rewrite HMeq in HM.
          split; [clear -HMK; lia | clear -HM; lia]. }
        destruct Hi10 as [Hi10 HPnew].
        assert (HF1 : tblF = it_fill (Z.to_nat (2 ^ x_root c / 2 ^ s_len st))
                               (s_tbl st) (0 + s_huff st) (2 ^ s_len st)
                               (it_here c st)).
        { unfold tblF. rewrite Hd, Z.sub_0_r, Hn0, Hc, Z.shiftr_0_r.
          rewrite !shiftl1 by lia. reflexivity. }
        assert (Hptr : RootPtr (x_root c)
                         (s_used st + Z.shiftl 1 curr')
                         (mkCodeT curr' (x_root c)
                            (s_next st + Z.shiftl 1 (s_curr st)))).
        { unfold RootPtr.
          rewrite bits_mkCodeT by (clear -Hroot; lia).
          rewrite op_mkCodeT_id by (clear -Hcb' Hroot; lia).
          rewrite val_mkCodeT_id
            by (rewrite Hsh2, Hn0, Hc;
                pose proof (pow2_pos_z (x_root c) ltac:(clear -Hroot; lia))
                  as Q1;
                assert (Q2 : (2:Z) ^ x_root c <= 2 ^ 15)
                  by (apply Z.pow_le_mono_r; clear -Hroot; lia);
                assert (Q3 : (2:Z) ^ 15 = 32768) by reflexivity;
                clear -Q1 Q2 Q3; lia).
          rewrite Hsh1, Hsh2, Hn0, Hc.
          rewrite Hsh1 in Hcap.
          pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia)) as Q1.
          pose proof (pow2_pos_z (x_root c) ltac:(clear -Hroot; lia)) as Q2.
          assert (Q3 : (2:Z) ^ x_root c <= 2 ^ 15)
            by (apply Z.pow_le_mono_r; clear -Hroot; lia).
          assert (Q4 : (2:Z) ^ 15 = 32768) by reflexivity.
          clear -Q1 Q2 Q3 Q4 Hcb' Hcap Hroot Hu0. lia. }
        assert (HrootF : GenBelow (RootEntry ty (x_root c) (s_used st))
                  (x_root c) 15 tblF 0
                  (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)).
        { replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
            with (zrev (Z.to_nat (s_len st)) (s_huff st)
                    * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
            by (unfold Pos in Hpos, Hpos1; clear -Hpos Hpos1; lia).
          rewrite HF1.
          apply gen_step_short; [lia | lia | lia | exact Hhuff | |].
          - left. split; [exact Hherel|]. rewrite Hbits_here, Hd. lia.
          - unfold Pos in Hpos. rewrite <- Hpos. exact HrootB. }
        unfold SubLedger, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min
             s_count s_tbl].
        split.
        { apply gen_tset; [right; exact Hptr|].
          intros k Hk Hu.
          eapply root_entry_mono;
            [| exact (HrootF k Hk Hu)].
          rewrite Hsh1.
          pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia)) as Qm.
          clear -Qm. lia. }
        right.
        split; [reflexivity|].
        split; [clear -Hcb'; lia|].
        split; [rewrite Hsh1, Hsh2, Hn0, Hc, Hu0; clear -Hroot; lia|].
        split; [rewrite Hsh2, Hn0, Hc; clear -Hroot; lia|].
        split; [rewrite Hsh1; rewrite Hsh1 in Hcap; clear -Hcap; lia|].
        split.
        { intros i Hi. exfalso. rewrite Hsh2, Hn0, Hc in Hi.
          clear -Hi. lia. }
        split.
        { intros k Hk Hu. exfalso.
          unfold UnitStart in Hu. rewrite Hlow' in Hu. fold K1 in Hu.
          rewrite HPnew in Hu.
          pose proof (zrev_nonneg (Z.to_nat curr') k) as Qv1.
          pose proof (pow2_pos_z ((15 - x_root c) - curr')
                        ltac:(clear -Hcb'; lia)) as Qv2.
          assert (Qv3 : 0 < (zrev (Z.to_nat curr') k + 1)
                      * 2 ^ ((15 - x_root c) - curr'))
            by (apply Z.mul_pos_pos; clear -Qv1 Qv2; lia).
          clear -Qv3 Hu. lia. }
        split.
        { rewrite Hlow'. rewrite tset_same. right. exact Hptr. }
        { rewrite HPnew.
           unfold UnitStart. rewrite Hlow'. fold K1.
           replace (Z.to_nat (x_root c + curr'))
             with (Z.to_nat (x_root c) + Z.to_nat curr')%nat
             by (clear -Hroot Hcb'; lia).
           rewrite wmass_split.
           rewrite (wmass_zero_on (Z.to_nat (x_root c)) 1 cnt1)
             by (intros j Hj; apply Hcnt1z; clear -Hj Hgt Hroot; lia).
           replace (1 + Z.of_nat (Z.to_nat (x_root c))) with (x_root c + 1)
             by (clear -Hroot; lia).
           destruct Hgd as [Hgl | Hgr]; [| clear -Hgr; lia].
           (* ceiling case: the window swallows everything that remains *)
           assert (Hwtot : wmass (Z.to_nat curr') (x_root c + 1) cnt1
                           = it_mass 15%nat 1 cnt1).
           { assert (H15s : (15%nat
                     = Z.to_nat (x_root c)
                       + (Z.to_nat curr'
                          + Z.to_nat (15 - x_root c - curr')))%nat)
               by (clear -Hroot Hcb'; lia).
              assert (Hwm : wmass 15%nat 1 cnt1 = it_mass 15%nat 1 cnt1).
              { rewrite (wmass_it_mass 15%nat 1 cnt1)
                  by (clear -Hmx; lia).
                 replace (16 - 1 - Z.of_nat 15) with 0
                   by (clear -Hmx; lia).
                 rewrite Z.pow_0_r. ring. }
              rewrite <- Hwm. rewrite H15s.
              rewrite wmass_split.
              rewrite (wmass_zero_on (Z.to_nat (x_root c)) 1 cnt1)
                by (intros j Hj; apply Hcnt1z; clear -Hj Hgt Hroot; lia).
              replace (1 + Z.of_nat (Z.to_nat (x_root c)))
                with (x_root c + 1) by (clear -Hroot; lia).
              rewrite wmass_split.
              rewrite (wmass_zero_on (Z.to_nat (15 - x_root c - curr'))
                        (x_root c + 1 + Z.of_nat (Z.to_nat curr')) cnt1)
                by (intros j Hj; apply Hcnt1hi;
                    clear -Hj Hgl Hroot Hcb'; lia).
              ring. }
           rewrite Hwtot.
           destruct Hcase as [HM0 | (Hmx1 & _)];
             [| exfalso; clear -Hmx1 Hgt HL1mx Hroot; lia].
           assert (HK1lt : K1 < 2 ^ x_root c).
           { unfold K1.
              pose proof (zrev_lt (Z.to_nat (x_root c))
                            (huff1 mod 2 ^ x_root c)) as Hz.
              rewrite to_nat_pow in Hz by (clear -Hroot; lia). exact Hz. }
           assert (Hps : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
             by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
           assert (Hbnd : K1 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)
                          <= 2 ^ 15).
           { replace (K1 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c))
               with ((K1 + 1) * 2 ^ (15 - x_root c)) by ring.
             rewrite <- Hps.
             apply Z.mul_le_mono_pos_r; clear -HK1lt HsPos; lia. }
           assert (H2_15 : (2:Z) ^ 15 = 32768) by reflexivity.
           clear -Hbnd HM0 HPnew. lia. }
        -- (* a later window: the old one closes exactly full *)
        destruct Hledph
          as [(Hd0 & _) | (Hd2 & Hcb & Hue & Hnx2 & Hu16 & Hcl & Hopen
                           & Hrp & Hguard)];
          [exfalso; clear -Hd Hd0 Hroot; lia|].
        pose proof (Hlow_rng Hd Hlow) as Hlr2.
        assert (Hfit : s_len st <= x_root c + s_curr st)
          by (apply Hlenfit; assumption).
        assert (Hsh2 : Z.shiftl 1 (s_curr st) = 2 ^ s_curr st)
          by (apply shiftl1; clear -Hcb; lia).
        set (hiO := Z.shiftr (s_huff st) (x_root c)) in *.
        assert (HhiO : 0 <= hiO < 2 ^ (s_len st - x_root c))
          by (unfold hiO; apply shiftr_range; lia).
        assert (HdecO : zrev (Z.to_nat (s_len st)) (s_huff st)
                = zrev (Z.to_nat (x_root c)) (s_huff st mod 2 ^ x_root c)
                    * 2 ^ (s_len st - x_root c)
                  + zrev (Z.to_nat (s_len st - x_root c)) hiO)
          by (unfold hiO; apply zrev_decomp; [lia|lia|exact Hhuff]).
        assert (HzrO : 0 <= zrev (Z.to_nat (s_len st - x_root c)) hiO
                       < 2 ^ (s_len st - x_root c)).
        { pose proof (zrev_lt (Z.to_nat (s_len st - x_root c)) hiO) as Hz1.
          pose proof (zrev_nonneg (Z.to_nat (s_len st - x_root c)) hiO)
            as Hz2.
          rewrite to_nat_pow in Hz1 by lia. lia. }
        assert (HscO : 2 ^ (s_len st - x_root c) * 2 ^ (15 - s_len st)
                       = 2 ^ (15 - x_root c))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (HsPos3 : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
        set (K0 := zrev (Z.to_nat (x_root c)) (s_low st)) in *.
        set (iO := zrev (Z.to_nat (s_len st - x_root c)) hiO
                     * 2 ^ (15 - s_len st)) in *.
        assert (HK0nn : 0 <= K0) by (unfold K0; apply zrev_nonneg).
        assert (HiOb : 0 <= iO /\ iO + 2 ^ (15 - s_len st)
                               <= 2 ^ (15 - x_root c)).
        { unfold iO. split; [apply Z.mul_nonneg_nonneg; lia|].
          replace (zrev (Z.to_nat (s_len st - x_root c)) hiO
                     * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
            with ((zrev (Z.to_nat (s_len st - x_root c)) hiO + 1)
                    * 2 ^ (15 - s_len st)) by ring.
          rewrite <- HscO. apply Z.mul_le_mono_pos_r; lia. }
        assert (HPo : Pos (it_mass 15%nat 1 cnt0) st
                      = K0 * 2 ^ (15 - x_root c) + iO).
        { unfold K0, iO. rewrite Hlow, Hpos, HdecO.
          rewrite Z.mul_add_distr_r, <- Z.mul_assoc, HscO. reflexivity. }
        assert (HK01 : K0 <> K1).
        { unfold K0, K1. intro He. apply Hsame. rewrite Hlow'.
          symmetry.
          apply (zrev_inj (Z.to_nat (x_root c)));
            [ rewrite to_nat_pow by (clear -Hroot; lia); clear -Hlr2; lia
            | rewrite to_nat_pow by (clear -Hroot; lia); clear -Hlr1; lia
            | exact He ]. }
        assert (Hsq : K1 = K0 + 1
                      /\ i1 = 0
                      /\ iO + 2 ^ (15 - s_len st) = 2 ^ (15 - x_root c)).
        { assert (HE : K1 * 2 ^ (15 - x_root c) + i1
                       = K0 * 2 ^ (15 - x_root c) + iO + 2 ^ (15 - s_len st))
            by (unfold Pos in HPo, Hpos1; clear -HPo Hpos1 HPn; lia).
          assert (Hle1 : K1 <= K0 + 1).
          { apply (mul_le_cancel_r K1 (K0 + 1) (2 ^ (15 - x_root c)) HsPos).
            replace ((K0 + 1) * 2 ^ (15 - x_root c))
              with (K0 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)) by ring.
            clear -HE HiOb Hi1b HsPos3. lia. }
          assert (Hle0 : K0 < K1 + 1).
          { apply (mul_lt_cancel_r K0 (K1 + 1) (2 ^ (15 - x_root c)) HsPos).
            replace ((K1 + 1) * 2 ^ (15 - x_root c))
              with (K1 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)) by ring.
            clear -HE HiOb Hi1b HsPos2 HsPos3. lia. }
          assert (HK : K1 = K0 + 1) by lia.
          split; [exact HK|].
          rewrite HK in HE.
          replace ((K0 + 1) * 2 ^ (15 - x_root c))
            with (K0 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)) in HE
            by ring.
          clear -HE HiOb Hi1b HsPos2 HsPos3. lia. }
        destruct Hsq as (HK & Hi10 & Hfull).
        assert (HPnew : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                        = K1 * 2 ^ (15 - x_root c))
          by (clear -HPn Hi10; lia).
        assert (HF2 : tblF
                 = it_fill (Z.to_nat (2 ^ s_curr st
                                      / 2 ^ (s_len st - x_root c)))
                     (s_tbl st) (s_next st + hiO)
                     (2 ^ (s_len st - x_root c)) (it_here c st)).
        { unfold tblF, hiO. rewrite Hd, !shiftl1 by lia. reflexivity. }
        assert (Hmiss_low : forall j, j < s_next st -> tblF j = s_tbl st j).
        { intros j Hj. rewrite HF2.
          rewrite (it_fill_get _ _ _ _ _ j) by (apply pow2_pos_z; lia).
          replace (Z.leb (s_next st + hiO) j) with false
            by (symmetry; apply Z.leb_gt; clear -Hj HhiO; lia).
          reflexivity. }
        assert (Hoflfull : GenBelow (SubEntry ty (x_root c)) (s_curr st)
                  (15 - x_root c) tblF (s_next st) (2 ^ (15 - x_root c))).
        { replace (2 ^ (15 - x_root c))
            with (zrev (Z.to_nat (s_len st - x_root c)) hiO
                    * 2 ^ ((15 - x_root c) - (s_len st - x_root c))
                  + 2 ^ ((15 - x_root c) - (s_len st - x_root c)))
            by (replace ((15 - x_root c) - (s_len st - x_root c))
                  with (15 - s_len st) by (clear -Hroot; lia);
                unfold iO in Hfull; clear -Hfull; lia).
          rewrite HF2.
          apply gen_step_short; [lia | lia | lia | exact HhiO | |].
          - split; [exact Hherel|]. rewrite Hbits_here, Hd.
            clear -Hrl Hlen. lia.
          - replace ((15 - x_root c) - (s_len st - x_root c))
              with (15 - s_len st) by (clear -Hroot; lia).
            assert (HUSo : Pos (it_mass 15%nat 1 cnt0) st
                             - UnitStart (x_root c) (s_low st)
                           = zrev (Z.to_nat (s_len st - x_root c)) hiO
                               * 2 ^ (15 - s_len st))
              by (unfold UnitStart; fold K0; unfold iO in HPo;
                  clear -HPo; lia).
            rewrite <- HUSo. exact Hopen. }
        assert (Hsubfull : forall i,
                  s_next st <= i < s_next st + 2 ^ s_curr st ->
                  SubEntry ty (x_root c) (tblF i)).
        { intros i Hi.
          replace i with (s_next st + (i - s_next st)) by (clear -Hi; lia).
          apply Hoflfull; [clear -Hi Hcb; lia|].
          pose proof (zrev_lt (Z.to_nat (s_curr st)) (i - s_next st)) as Hzl.
          rewrite to_nat_pow in Hzl by (clear -Hcb; lia).
          pose proof (pow2_pos_z ((15 - x_root c) - s_curr st)
                        ltac:(clear -Hcb; lia)) as Hq2.
          pose proof (zrev_nonneg (Z.to_nat (s_curr st)) (i - s_next st))
            as Hq3.
          assert (Hpc : (zrev (Z.to_nat (s_curr st)) (i - s_next st) + 1)
                          * 2 ^ ((15 - x_root c) - s_curr st)
                        <= 2 ^ s_curr st
                          * 2 ^ ((15 - x_root c) - s_curr st))
            by (apply Z.mul_le_mono_pos_r; clear -Hzl Hq2; lia).
          rewrite <- Z.pow_add_r in Hpc by (clear -Hcb Hroot; lia).
          replace (s_curr st + ((15 - x_root c) - s_curr st))
            with (15 - x_root c) in Hpc by (clear -Hcb; lia).
          clear -Hpc Hq2 Hq3. lia. }
        assert (Hptr : RootPtr (x_root c)
                         (s_used st + Z.shiftl 1 curr')
                         (mkCodeT curr' (x_root c)
                            (s_next st + Z.shiftl 1 (s_curr st)))).
        { unfold RootPtr.
          rewrite bits_mkCodeT by (clear -Hroot; lia).
          rewrite op_mkCodeT_id by (clear -Hcb' Hroot; lia).
          rewrite val_mkCodeT_id
            by (rewrite Hsh2; rewrite Hsh1 in Hcap;
                pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia)) as Q1;
                pose proof (pow2_pos_z (s_curr st)
                              ltac:(clear -Hcb; lia)) as Q2;
                clear -Q1 Q2 Hcap Hnx2 Hue Hroot; lia).
          rewrite Hsh1, Hsh2.
          rewrite Hsh1 in Hcap.
          pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia)) as Q1.
          pose proof (pow2_pos_z (s_curr st) ltac:(clear -Hcb; lia)) as Q2.
          assert (Q3 : (2:Z) ^ x_root c <= 2 ^ 15)
            by (apply Z.pow_le_mono_r; clear -Hroot; lia).
          assert (Q4 : (2:Z) ^ 15 = 32768) by reflexivity.
          clear -Q1 Q2 Q3 Q4 Hcb' Hcap Hue Hnx2 Hroot. lia. }
        assert (HrootF : GenBelow (RootEntry ty (x_root c) (s_used st))
                  (x_root c) 15 tblF 0
                  (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)).
        { replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
            with (zrev (Z.to_nat (s_len st)) (s_huff st)
                    * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
            by (unfold Pos in Hpos, Hpos1; clear -Hpos Hpos1; lia).
          rewrite HF2.
          apply gen_step_long;
            [clear -Hroot; lia | clear -Hrl; lia | clear -Hlen; lia
             | clear -Hroot; lia | exact Hhuff | clear -Hnx HhiO; lia
             | apply pow2_pos_z; clear -Hrl; lia | |].
          - unfold Pos in Hpos. rewrite <- Hpos. exact HrootB.
          - replace (0 + s_huff st mod 2 ^ x_root c) with (s_low st)
              by (rewrite Hlow; lia).
            exact Hrp. }
        unfold SubLedger, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min
             s_count s_tbl].
        split.
        { apply gen_tset; [right; exact Hptr|].
          intros k Hk Hu.
          eapply root_entry_mono;
            [| exact (HrootF k Hk Hu)].
          rewrite Hsh1.
          pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia)) as Qm.
          clear -Qm. lia. }
        right.
        split; [reflexivity|].
        split; [clear -Hcb'; lia|].
        split; [rewrite Hsh1, Hsh2; clear -Hue; lia|].
        split; [rewrite Hsh2; clear -Hnx2 Hroot; lia|].
        split; [rewrite Hsh1; rewrite Hsh1 in Hcap; clear -Hcap; lia|].
        split.
        { intros i Hi. rewrite Hsh2 in Hi.
          rewrite tset_other
            by (pose proof (pow2_pos_z (s_curr st)
                              ltac:(clear -Hcb; lia)) as Qc;
                rewrite Hlow'; clear -Qc Hi Hlr1 Hnx2; lia).
          destruct (Z_lt_ge_dec i (s_next st)) as [Hi1'|Hi2'].
          - rewrite Hmiss_low by (clear -Hi1'; lia). apply Hcl.
            clear -Hi Hi1'. lia.
          - apply Hsubfull. clear -Hi Hi2'. lia. }
        split.
        { intros k Hk Hu. exfalso.
          unfold UnitStart in Hu. rewrite Hlow' in Hu. fold K1 in Hu.
          rewrite HPnew in Hu.
          pose proof (zrev_nonneg (Z.to_nat curr') k) as Qv1.
          pose proof (pow2_pos_z ((15 - x_root c) - curr')
                        ltac:(clear -Hcb'; lia)) as Qv2.
          assert (Qv3 : 0 < (zrev (Z.to_nat curr') k + 1)
                      * 2 ^ ((15 - x_root c) - curr'))
            by (apply Z.mul_pos_pos; clear -Qv1 Qv2; lia).
          clear -Qv3 Hu. lia. }
        split.
        { rewrite Hlow'. rewrite tset_same. right. exact Hptr. }
        { rewrite HPnew.
           unfold UnitStart. rewrite Hlow'. fold K1.
           replace (Z.to_nat (x_root c + curr'))
             with (Z.to_nat (x_root c) + Z.to_nat curr')%nat
             by (clear -Hroot Hcb'; lia).
           rewrite wmass_split.
           rewrite (wmass_zero_on (Z.to_nat (x_root c)) 1 cnt1)
             by (intros j Hj; apply Hcnt1z; clear -Hj Hgt Hroot; lia).
           replace (1 + Z.of_nat (Z.to_nat (x_root c))) with (x_root c + 1)
             by (clear -Hroot; lia).
           destruct Hgd as [Hgl | Hgr]; [| clear -Hgr; lia].
           (* ceiling case: the window swallows everything that remains *)
           assert (Hwtot : wmass (Z.to_nat curr') (x_root c + 1) cnt1
                           = it_mass 15%nat 1 cnt1).
           { assert (H15s : (15%nat
                     = Z.to_nat (x_root c)
                       + (Z.to_nat curr'
                          + Z.to_nat (15 - x_root c - curr')))%nat)
               by (clear -Hroot Hcb'; lia).
              assert (Hwm : wmass 15%nat 1 cnt1 = it_mass 15%nat 1 cnt1).
              { rewrite (wmass_it_mass 15%nat 1 cnt1)
                  by (clear -Hmx; lia).
                 replace (16 - 1 - Z.of_nat 15) with 0
                   by (clear -Hmx; lia).
                 rewrite Z.pow_0_r. ring. }
              rewrite <- Hwm. rewrite H15s.
              rewrite wmass_split.
              rewrite (wmass_zero_on (Z.to_nat (x_root c)) 1 cnt1)
                by (intros j Hj; apply Hcnt1z; clear -Hj Hgt Hroot; lia).
              replace (1 + Z.of_nat (Z.to_nat (x_root c)))
                with (x_root c + 1) by (clear -Hroot; lia).
              rewrite wmass_split.
              rewrite (wmass_zero_on (Z.to_nat (15 - x_root c - curr'))
                        (x_root c + 1 + Z.of_nat (Z.to_nat curr')) cnt1)
                by (intros j Hj; apply Hcnt1hi;
                    clear -Hj Hgl Hroot Hcb'; lia).
              ring. }
           rewrite Hwtot.
           destruct Hcase as [HM0 | (Hmx1 & _)];
             [| exfalso; clear -Hmx1 Hgt HL1mx Hroot; lia].
           assert (HK1lt : K1 < 2 ^ x_root c).
           { unfold K1.
              pose proof (zrev_lt (Z.to_nat (x_root c))
                            (huff1 mod 2 ^ x_root c)) as Hz.
              rewrite to_nat_pow in Hz by (clear -Hroot; lia). exact Hz. }
           assert (Hps : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
             by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
           assert (Hbnd : K1 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)
                          <= 2 ^ 15).
           { replace (K1 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c))
               with ((K1 + 1) * 2 ^ (15 - x_root c)) by ring.
             rewrite <- Hps.
             apply Z.mul_le_mono_pos_r; clear -HK1lt HsPos; lia. }
           assert (H2_15 : (2:Z) ^ 15 = 32768) by reflexivity.
           clear -Hbnd HM0 HPnew. lia. }
    + (* the next length still fits the root: phase 1 continues *)
      apply Z.ltb_ge in Hgt.
      cbn [andb] in Hstep.
      injection Hstep as Hst'. subst st'.
      destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & _)];
        [| exfalso; lia].
      destruct Hledph as [(Hd0 & Hu0 & Hn0) | (Hd2 & _)];
        [| exfalso; lia].
      unfold SubLedger, Pos.
      cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min
           s_count s_tbl].
      split; [| left; auto].
      (* the root region gains this code's residue class *)
      assert (HF1 : tblF = it_fill (Z.to_nat (2 ^ x_root c / 2 ^ s_len st))
                             (s_tbl st) (0 + s_huff st) (2 ^ s_len st)
                             (it_here c st)).
      { unfold tblF. rewrite Hd, Z.sub_0_r, Hnx, Hc, Z.shiftr_0_r.
        rewrite !shiftl1 by lia. reflexivity. }
      rewrite HF1.
      replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
        with (zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 - s_len st)
              + 2 ^ (15 - s_len st))
        by (unfold Pos in Hpos, Hpos1; clear -Hpos Hpos1; lia).
      apply gen_step_short; [lia | lia | lia | exact Hhuff | |].
      { left. split; [exact Hherel|].
        rewrite Hbits_here, Hd. lia. }
      { unfold Pos in Hpos. rewrite <- Hpos. exact HrootB. }
  - (* current length continues *)
    apply Z.eqb_neq in Hhit.
    cbn [andb] in Hstep.
    destruct (Z.ltb (x_root c) (s_len st)) eqn:Hgt.
    + apply Z.ltb_lt in Hgt.
      destruct (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) eqn:Hsame;
        cbn [andb negb] in Hstep.
      * (* SAME PREFIX *)
        apply Z.eqb_eq in Hsame.
        injection Hstep as Hst'. subst st'.
        destruct Hphase
          as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)];
          [exfalso; lia|].
        destruct Hledph
          as [(Hd0 & _) | (Hd2 & Hcb & Hue & Hnx2 & Hu16 & Hcl & Hopen
                           & Hrp & Hguard)];
          [exfalso; lia|].
        pose proof (Hlow_rng Hd Hlow) as Hlr2.
        assert (Hfit : s_len st <= x_root c + s_curr st)
          by (apply Hlenfit; assumption).
        set (hi := Z.shiftr (s_huff st) (x_root c)) in *.
        assert (Hhi : 0 <= hi < 2 ^ (s_len st - x_root c))
          by (unfold hi; apply shiftr_range; lia).
        assert (Hdec : zrev (Z.to_nat (s_len st)) (s_huff st)
                = zrev (Z.to_nat (x_root c)) (s_huff st mod 2 ^ x_root c)
                    * 2 ^ (s_len st - x_root c)
                  + zrev (Z.to_nat (s_len st - x_root c)) hi)
          by (unfold hi; apply zrev_decomp; [lia|lia|exact Hhuff]).
        assert (Hsc3 : 2 ^ (s_len st - x_root c) * 2 ^ (15 - s_len st)
                       = 2 ^ (15 - x_root c))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (HUS : Pos (it_mass 15%nat 1 cnt0) st
                        - UnitStart (x_root c) (s_low st)
                      = zrev (Z.to_nat (s_len st - x_root c)) hi
                          * 2 ^ (15 - s_len st)).
        { unfold UnitStart. rewrite Hlow, Hpos, Hdec. clear -Hsc3; nia. }
        assert (HF2 : tblF
                 = it_fill (Z.to_nat (2 ^ s_curr st
                                      / 2 ^ (s_len st - x_root c)))
                     (s_tbl st) (s_next st + hi)
                     (2 ^ (s_len st - x_root c)) (it_here c st)).
        { unfold tblF, hi. rewrite Hd, !shiftl1 by lia. reflexivity. }
        assert (Hmiss_low : forall j, j < s_next st -> tblF j = s_tbl st j).
        { intros j Hj. rewrite HF2.
           rewrite (it_fill_get _ _ _ _ _ j) by (apply pow2_pos_z; lia).
           replace (Z.leb (s_next st + hi) j) with false
             by (symmetry; apply Z.leb_gt; lia).
           reflexivity. }
        unfold SubLedger, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min
             s_count s_tbl].
        split.
        { replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
             with (zrev (Z.to_nat (s_len st)) (s_huff st)
                     * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
             by (unfold Pos in Hpos, Hpos1; clear -Hpos Hpos1; lia).
           rewrite HF2.
           apply gen_step_long;
             [lia | lia | lia | lia | exact Hhuff | lia
              | apply pow2_pos_z; lia | |].
           - unfold Pos in Hpos. rewrite <- Hpos. exact HrootB.
           - replace (0 + s_huff st mod 2 ^ x_root c) with (s_low st)
               by (rewrite Hlow; lia).
             exact Hrp. }
        right.
        split; [exact Hd|].
        split; [exact Hcb|].
        split; [exact Hue|].
        split; [exact Hnx2|].
        split; [exact Hu16|].
        split.
        { intros i Hi. rewrite Hmiss_low by lia. apply Hcl. exact Hi. }
        split.
        { replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                    - UnitStart (x_root c) (s_low st))
             with (zrev (Z.to_nat (s_len st - x_root c)) hi
                     * 2 ^ ((15 - x_root c) - (s_len st - x_root c))
                   + 2 ^ ((15 - x_root c) - (s_len st - x_root c)))
             by (replace ((15 - x_root c) - (s_len st - x_root c))
                   with (15 - s_len st) by lia;
                 unfold Pos in Hpos1, HUS; clear -Hpos1 HUS; lia).
           rewrite HF2.
           apply gen_step_short; [lia | lia | lia | exact Hhi | |].
           - split; [exact Hherel|]. rewrite Hbits_here, Hd. lia.
           - replace ((15 - x_root c) - (s_len st - x_root c))
               with (15 - s_len st) by lia.
             rewrite <- HUS. exact Hopen. }
        split.
        { rewrite Hmiss_low by lia. exact Hrp. }
        { assert (Hwd : wmass (Z.to_nat (x_root c + s_curr st)) 1 cnt1
                   = wmass (Z.to_nat (x_root c + s_curr st)) 1 (s_count st)
                     - 2 ^ (15 - s_len st)).
           { unfold cnt1. apply wmass_dec. lia. }
           rewrite Hwd.
           unfold Pos in Hguard, Hpos1. lia. }
      * (* NEW WINDOW *)
        apply Z.eqb_neq in Hsame.
        match type of Hstep with
        | (if it_enough _ (_ + Z.shiftl 1 ?cv) then _ else _) = _ =>
            remember cv as curr' eqn:Hcurr'
        end.
        match type of Hstep with
        | (if ?b then _ else _) = _ => remember b as en eqn:Hen; destruct en
        end; [discriminate Hstep|].
        injection Hstep as Hst'. subst st'.
        replace (if Z.eqb (s_drop st) 0 then x_root c else s_drop st)
          with (x_root c) in *
          by (destruct Hphase as [(Hd & _) | (Hd & _)]; rewrite Hd;
              [ rewrite Z.eqb_refl; reflexivity
              | replace (Z.eqb (x_root c) 0) with false
                  by (symmetry; apply Z.eqb_neq; lia); reflexivity ]).
        assert (HL1mx : (s_len st) <= x_max c) by (exact Hlenmx).
        assert (Hcb' : (s_len st) - x_root c <= curr' /\ 1 <= curr' <= 15 - x_root c).
        { pose proof (it_subsz_bounds 16%nat cnt1 (x_root c) (x_max c)
                        ((s_len st) - x_root c) (Z.shiftl 1 ((s_len st) - x_root c))) as HB.
           rewrite <- Hcurr' in HB. clear -HB Hgt Hlenmx Hmx; lia. }
        assert (Hcap : s_used st + Z.shiftl 1 curr' <= 852).
        { destruct Hty as [HtL|[HtD|Hcap3]];
            [ rewrite HtL in Hen | rewrite HtD in Hen
            | exfalso; clear -Hcap3 Hgt HL1mx; lia ];
            unfold it_enough in Hen; cbn in Hen;
            symmetry in Hen; rewrite ?orb_false_r in Hen;
            apply Z.ltb_ge in Hen;
            unfold ENOUGH_LENS, ENOUGH_DISTS in Hen; lia. }
        assert (Hsh1 : Z.shiftl 1 curr' = 2 ^ curr') by (apply shiftl1; lia).
        pose proof Hlowmod as Hlow'.
        assert (Hlr1 : 0 <= huff1 mod 2 ^ x_root c < 2 ^ x_root c)
          by (apply Z.mod_pos_bound, pow2_pos_z; lia).
        assert (Hh1L : 0 <= huff1 < 2 ^ (s_len st)).
        { assert (2 ^ s_len st <= 2 ^ (s_len st)) by (apply Z.pow_le_mono_r; lia).
           lia. }
        set (hi1 := Z.shiftr huff1 (x_root c)) in *.
        assert (Hh1r : 0 <= hi1 < 2 ^ ((s_len st) - x_root c))
          by (unfold hi1; apply shiftr_range; lia).
        assert (Hdec1 : zrev (Z.to_nat (s_len st)) huff1
                = zrev (Z.to_nat (x_root c)) (huff1 mod 2 ^ x_root c)
                    * 2 ^ ((s_len st) - x_root c)
                  + zrev (Z.to_nat ((s_len st) - x_root c)) hi1)
          by (unfold hi1; apply zrev_decomp; [lia|lia|exact Hh1L]).
        assert (Hzr1 : 0 <= zrev (Z.to_nat ((s_len st) - x_root c)) hi1
                       < 2 ^ ((s_len st) - x_root c)).
        { pose proof (zrev_lt (Z.to_nat ((s_len st) - x_root c)) hi1) as Hz1.
           pose proof (zrev_nonneg (Z.to_nat ((s_len st) - x_root c)) hi1) as Hz2.
           rewrite to_nat_pow in Hz1 by lia. lia. }
        assert (Hsc1' : 2 ^ ((s_len st) - x_root c) * 2 ^ (15 - (s_len st))
                        = 2 ^ (15 - x_root c))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (HsPos : 0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
        assert (HsPos2 : 0 < 2 ^ (15 - (s_len st))) by (apply pow2_pos_z; lia).
        set (K1 := zrev (Z.to_nat (x_root c)) (huff1 mod 2 ^ x_root c)) in *.
        set (i1 := zrev (Z.to_nat ((s_len st) - x_root c)) hi1 * 2 ^ (15 - (s_len st)))
          in *.
        assert (HK1nn : 0 <= K1) by (unfold K1; apply zrev_nonneg).
        assert (Hi1b : 0 <= i1 /\ i1 + 2 ^ (15 - (s_len st))
                              <= 2 ^ (15 - x_root c)).
        { unfold i1. split; [apply Z.mul_nonneg_nonneg; lia|].
          replace (zrev (Z.to_nat ((s_len st) - x_root c)) hi1
                     * 2 ^ (15 - (s_len st)) + 2 ^ (15 - (s_len st)))
            with ((zrev (Z.to_nat ((s_len st) - x_root c)) hi1 + 1)
                    * 2 ^ (15 - (s_len st))) by ring.
          rewrite <- Hsc1'. apply Z.mul_le_mono_pos_r; lia. }
        assert (HPn : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                      = K1 * 2 ^ (15 - x_root c) + i1).
        { unfold K1, i1.
           rewrite (Hposlink (s_len st) ltac:(lia) ltac:(lia)), Hdec1.
           rewrite Z.mul_add_distr_r, <- Z.mul_assoc, Hsc1'. reflexivity. }
        assert (Hcnt1z : forall l, 1 <= l < (s_len st) -> cnt1 l = 0).
        { intros l Hll.
          rewrite (Hcnt1 l ltac:(clear -Hll Hlen; lia)).
          replace (Z.ltb l (s_len st)) with true
            by (symmetry; apply Z.ltb_lt; clear -Hll; lia).
          reflexivity. }
        assert (Hcnt1hi : forall l, x_max c < l <= 15 -> cnt1 l = 0).
        { intros l Hl. rewrite (Hcnt1 l ltac:(clear -Hl Hmx; lia)).
          replace (Z.ltb l (s_len st)) with false
            by (symmetry; apply Z.ltb_ge; clear -Hl Hlenmx; lia).
          replace (Z.eqb l (s_len st)) with false
            by (symmetry; apply Z.eqb_neq; clear -Hl Hlenmx; lia).
          apply Hmxz. clear -Hl Hmx. lia. }
        assert (Hgd : x_max c <= x_root c + curr'
                \/ 2 ^ (15 - x_root c)
                   <= wmass (Z.to_nat curr') (x_root c + 1) cnt1).
        { assert (Hinv0 : Z.shiftl 1 ((s_len st) - x_root c)
                     * 2 ^ (15 - x_root c - ((s_len st) - x_root c))
                   = 2 ^ (15 - x_root c)
                     - wmass (Z.to_nat ((s_len st) - x_root c - 1))
                         (x_root c + 1) cnt1).
           { rewrite shiftl1 by (clear -Hgt; lia).
              rewrite (wmass_zero_on (Z.to_nat ((s_len st) - x_root c - 1))
                        (x_root c + 1) cnt1)
                by (intros j Hj; apply Hcnt1z; clear -Hj Hroot Hgt; lia).
              rewrite Z.sub_0_r.
              rewrite <- Z.pow_add_r by (clear -Hgt HL1mx Hmx; lia).
              f_equal. clear -Hgt; lia. }
           exact (it_subsz_covers 16%nat cnt1 (x_root c) (x_max c)
                    ((s_len st) - x_root c) (Z.shiftl 1 ((s_len st) - x_root c)) curr'
                    Hcurr' ltac:(clear -Hroot; lia) ltac:(clear -Hgt; lia)
                    ltac:(clear -HL1mx Hmx; lia) ltac:(clear -Hmx; lia)
                    ltac:(clear -Hmx Hgt Hroot HL1mx; lia) Hinv0). }
        clear Hcurr' Hen.
        destruct Hphase
          as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)];
          [exfalso; lia|].
        destruct Hledph
          as [(Hd0 & _) | (Hd2 & Hcb & Hue & Hnx2 & Hu16 & Hcl & Hopen
                           & Hrp & Hguard)];
          [exfalso; clear -Hd Hd0 Hroot; lia|].
        pose proof (Hlow_rng Hd Hlow) as Hlr2.
        assert (Hfit : s_len st <= x_root c + s_curr st)
          by (apply Hlenfit; assumption).
        assert (Hsh2 : Z.shiftl 1 (s_curr st) = 2 ^ s_curr st)
          by (apply shiftl1; clear -Hcb; lia).
        set (hiO := Z.shiftr (s_huff st) (x_root c)) in *.
        assert (HhiO : 0 <= hiO < 2 ^ (s_len st - x_root c))
          by (unfold hiO; apply shiftr_range; lia).
        assert (HdecO : zrev (Z.to_nat (s_len st)) (s_huff st)
                = zrev (Z.to_nat (x_root c)) (s_huff st mod 2 ^ x_root c)
                    * 2 ^ (s_len st - x_root c)
                  + zrev (Z.to_nat (s_len st - x_root c)) hiO)
          by (unfold hiO; apply zrev_decomp; [lia|lia|exact Hhuff]).
        assert (HzrO : 0 <= zrev (Z.to_nat (s_len st - x_root c)) hiO
                       < 2 ^ (s_len st - x_root c)).
        { pose proof (zrev_lt (Z.to_nat (s_len st - x_root c)) hiO) as Hz1.
          pose proof (zrev_nonneg (Z.to_nat (s_len st - x_root c)) hiO)
            as Hz2.
          rewrite to_nat_pow in Hz1 by lia. lia. }
        assert (HscO : 2 ^ (s_len st - x_root c) * 2 ^ (15 - s_len st)
                       = 2 ^ (15 - x_root c))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (HsPos3 : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
        set (K0 := zrev (Z.to_nat (x_root c)) (s_low st)) in *.
        set (iO := zrev (Z.to_nat (s_len st - x_root c)) hiO
                     * 2 ^ (15 - s_len st)) in *.
        assert (HK0nn : 0 <= K0) by (unfold K0; apply zrev_nonneg).
        assert (HiOb : 0 <= iO /\ iO + 2 ^ (15 - s_len st)
                               <= 2 ^ (15 - x_root c)).
        { unfold iO. split; [apply Z.mul_nonneg_nonneg; lia|].
          replace (zrev (Z.to_nat (s_len st - x_root c)) hiO
                     * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
            with ((zrev (Z.to_nat (s_len st - x_root c)) hiO + 1)
                    * 2 ^ (15 - s_len st)) by ring.
          rewrite <- HscO. apply Z.mul_le_mono_pos_r; lia. }
        assert (HPo : Pos (it_mass 15%nat 1 cnt0) st
                      = K0 * 2 ^ (15 - x_root c) + iO).
        { unfold K0, iO. rewrite Hlow, Hpos, HdecO.
          rewrite Z.mul_add_distr_r, <- Z.mul_assoc, HscO. reflexivity. }
        assert (HK01 : K0 <> K1).
        { unfold K0, K1. intro He. apply Hsame. rewrite Hlow'.
          symmetry.
          apply (zrev_inj (Z.to_nat (x_root c)));
            [ rewrite to_nat_pow by (clear -Hroot; lia); clear -Hlr2; lia
            | rewrite to_nat_pow by (clear -Hroot; lia); clear -Hlr1; lia
            | exact He ]. }
        assert (Hsq : K1 = K0 + 1
                      /\ i1 = 0
                      /\ iO + 2 ^ (15 - s_len st) = 2 ^ (15 - x_root c)).
        { assert (HE : K1 * 2 ^ (15 - x_root c) + i1
                       = K0 * 2 ^ (15 - x_root c) + iO + 2 ^ (15 - s_len st))
            by (unfold Pos in HPo, Hpos1; clear -HPo Hpos1 HPn; lia).
          assert (Hle1 : K1 <= K0 + 1).
          { apply (mul_le_cancel_r K1 (K0 + 1) (2 ^ (15 - x_root c)) HsPos).
            replace ((K0 + 1) * 2 ^ (15 - x_root c))
              with (K0 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)) by ring.
            clear -HE HiOb Hi1b HsPos3. lia. }
          assert (Hle0 : K0 < K1 + 1).
          { apply (mul_lt_cancel_r K0 (K1 + 1) (2 ^ (15 - x_root c)) HsPos).
            replace ((K1 + 1) * 2 ^ (15 - x_root c))
              with (K1 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)) by ring.
            clear -HE HiOb Hi1b HsPos2 HsPos3. lia. }
          assert (HK : K1 = K0 + 1) by lia.
          split; [exact HK|].
          rewrite HK in HE.
          replace ((K0 + 1) * 2 ^ (15 - x_root c))
            with (K0 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)) in HE
            by ring.
          clear -HE HiOb Hi1b HsPos2 HsPos3. lia. }
        destruct Hsq as (HK & Hi10 & Hfull).
        assert (HPnew : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                        = K1 * 2 ^ (15 - x_root c))
          by (clear -HPn Hi10; lia).
        assert (HF2 : tblF
                 = it_fill (Z.to_nat (2 ^ s_curr st
                                      / 2 ^ (s_len st - x_root c)))
                     (s_tbl st) (s_next st + hiO)
                     (2 ^ (s_len st - x_root c)) (it_here c st)).
        { unfold tblF, hiO. rewrite Hd, !shiftl1 by lia. reflexivity. }
        assert (Hmiss_low : forall j, j < s_next st -> tblF j = s_tbl st j).
        { intros j Hj. rewrite HF2.
          rewrite (it_fill_get _ _ _ _ _ j) by (apply pow2_pos_z; lia).
          replace (Z.leb (s_next st + hiO) j) with false
            by (symmetry; apply Z.leb_gt; clear -Hj HhiO; lia).
          reflexivity. }
        assert (Hoflfull : GenBelow (SubEntry ty (x_root c)) (s_curr st)
                  (15 - x_root c) tblF (s_next st) (2 ^ (15 - x_root c))).
        { replace (2 ^ (15 - x_root c))
            with (zrev (Z.to_nat (s_len st - x_root c)) hiO
                    * 2 ^ ((15 - x_root c) - (s_len st - x_root c))
                  + 2 ^ ((15 - x_root c) - (s_len st - x_root c)))
            by (replace ((15 - x_root c) - (s_len st - x_root c))
                  with (15 - s_len st) by (clear -Hroot; lia);
                unfold iO in Hfull; clear -Hfull; lia).
          rewrite HF2.
          apply gen_step_short; [lia | lia | lia | exact HhiO | |].
          - split; [exact Hherel|]. rewrite Hbits_here, Hd.
            clear -Hrl Hlen. lia.
          - replace ((15 - x_root c) - (s_len st - x_root c))
              with (15 - s_len st) by (clear -Hroot; lia).
            assert (HUSo : Pos (it_mass 15%nat 1 cnt0) st
                             - UnitStart (x_root c) (s_low st)
                           = zrev (Z.to_nat (s_len st - x_root c)) hiO
                               * 2 ^ (15 - s_len st))
              by (unfold UnitStart; fold K0; unfold iO in HPo;
                  clear -HPo; lia).
            rewrite <- HUSo. exact Hopen. }
        assert (Hsubfull : forall i,
                  s_next st <= i < s_next st + 2 ^ s_curr st ->
                  SubEntry ty (x_root c) (tblF i)).
        { intros i Hi.
          replace i with (s_next st + (i - s_next st)) by (clear -Hi; lia).
          apply Hoflfull; [clear -Hi Hcb; lia|].
          pose proof (zrev_lt (Z.to_nat (s_curr st)) (i - s_next st)) as Hzl.
          rewrite to_nat_pow in Hzl by (clear -Hcb; lia).
          pose proof (pow2_pos_z ((15 - x_root c) - s_curr st)
                        ltac:(clear -Hcb; lia)) as Hq2.
          pose proof (zrev_nonneg (Z.to_nat (s_curr st)) (i - s_next st))
            as Hq3.
          assert (Hpc : (zrev (Z.to_nat (s_curr st)) (i - s_next st) + 1)
                          * 2 ^ ((15 - x_root c) - s_curr st)
                        <= 2 ^ s_curr st
                          * 2 ^ ((15 - x_root c) - s_curr st))
            by (apply Z.mul_le_mono_pos_r; clear -Hzl Hq2; lia).
          rewrite <- Z.pow_add_r in Hpc by (clear -Hcb Hroot; lia).
          replace (s_curr st + ((15 - x_root c) - s_curr st))
            with (15 - x_root c) in Hpc by (clear -Hcb; lia).
          clear -Hpc Hq2 Hq3. lia. }
        assert (Hptr : RootPtr (x_root c)
                         (s_used st + Z.shiftl 1 curr')
                         (mkCodeT curr' (x_root c)
                            (s_next st + Z.shiftl 1 (s_curr st)))).
        { unfold RootPtr.
          rewrite bits_mkCodeT by (clear -Hroot; lia).
          rewrite op_mkCodeT_id by (clear -Hcb' Hroot; lia).
          rewrite val_mkCodeT_id
            by (rewrite Hsh2; rewrite Hsh1 in Hcap;
                pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia)) as Q1;
                pose proof (pow2_pos_z (s_curr st)
                              ltac:(clear -Hcb; lia)) as Q2;
                clear -Q1 Q2 Hcap Hnx2 Hue Hroot; lia).
          rewrite Hsh1, Hsh2.
          rewrite Hsh1 in Hcap.
          pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia)) as Q1.
          pose proof (pow2_pos_z (s_curr st) ltac:(clear -Hcb; lia)) as Q2.
          assert (Q3 : (2:Z) ^ x_root c <= 2 ^ 15)
            by (apply Z.pow_le_mono_r; clear -Hroot; lia).
          assert (Q4 : (2:Z) ^ 15 = 32768) by reflexivity.
          clear -Q1 Q2 Q3 Q4 Hcb' Hcap Hue Hnx2 Hroot. lia. }
        assert (HrootF : GenBelow (RootEntry ty (x_root c) (s_used st))
                  (x_root c) 15 tblF 0
                  (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)).
        { replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
            with (zrev (Z.to_nat (s_len st)) (s_huff st)
                    * 2 ^ (15 - s_len st) + 2 ^ (15 - s_len st))
            by (unfold Pos in Hpos, Hpos1; clear -Hpos Hpos1; lia).
          rewrite HF2.
          apply gen_step_long;
            [clear -Hroot; lia | clear -Hrl; lia | clear -Hlen; lia
             | clear -Hroot; lia | exact Hhuff | clear -Hnx HhiO; lia
             | apply pow2_pos_z; clear -Hrl; lia | |].
          - unfold Pos in Hpos. rewrite <- Hpos. exact HrootB.
          - replace (0 + s_huff st mod 2 ^ x_root c) with (s_low st)
              by (rewrite Hlow; lia).
            exact Hrp. }
        unfold SubLedger, Pos.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min
             s_count s_tbl].
        split.
        { apply gen_tset; [right; exact Hptr|].
          intros k Hk Hu.
          eapply root_entry_mono;
            [| exact (HrootF k Hk Hu)].
          rewrite Hsh1.
          pose proof (pow2_pos_z curr' ltac:(clear -Hcb'; lia)) as Qm.
          clear -Qm. lia. }
        right.
        split; [reflexivity|].
        split; [clear -Hcb'; lia|].
        split; [rewrite Hsh1, Hsh2; clear -Hue; lia|].
        split; [rewrite Hsh2; clear -Hnx2 Hroot; lia|].
        split; [rewrite Hsh1; rewrite Hsh1 in Hcap; clear -Hcap; lia|].
        split.
        { intros i Hi. rewrite Hsh2 in Hi.
          rewrite tset_other
            by (pose proof (pow2_pos_z (s_curr st)
                              ltac:(clear -Hcb; lia)) as Qc;
                rewrite Hlow'; clear -Qc Hi Hlr1 Hnx2; lia).
          destruct (Z_lt_ge_dec i (s_next st)) as [Hi1'|Hi2'].
          - rewrite Hmiss_low by (clear -Hi1'; lia). apply Hcl.
            clear -Hi Hi1'. lia.
          - apply Hsubfull. clear -Hi Hi2'. lia. }
        split.
        { intros k Hk Hu. exfalso.
          unfold UnitStart in Hu. rewrite Hlow' in Hu. fold K1 in Hu.
          rewrite HPnew in Hu.
          pose proof (zrev_nonneg (Z.to_nat curr') k) as Qv1.
          pose proof (pow2_pos_z ((15 - x_root c) - curr')
                        ltac:(clear -Hcb'; lia)) as Qv2.
          assert (Qv3 : 0 < (zrev (Z.to_nat curr') k + 1)
                      * 2 ^ ((15 - x_root c) - curr'))
            by (apply Z.mul_pos_pos; clear -Qv1 Qv2; lia).
          clear -Qv3 Hu. lia. }
        split.
        { rewrite Hlow'. rewrite tset_same. right. exact Hptr. }
        { rewrite HPnew.
           unfold UnitStart. rewrite Hlow'. fold K1.
           replace (Z.to_nat (x_root c + curr'))
             with (Z.to_nat (x_root c) + Z.to_nat curr')%nat
             by (clear -Hroot Hcb'; lia).
           rewrite wmass_split.
           rewrite (wmass_zero_on (Z.to_nat (x_root c)) 1 cnt1)
             by (intros j Hj; apply Hcnt1z; clear -Hj Hgt Hroot; lia).
           replace (1 + Z.of_nat (Z.to_nat (x_root c))) with (x_root c + 1)
             by (clear -Hroot; lia).
           destruct Hgd as [Hgl | Hgr]; [| clear -Hgr; lia].
           (* ceiling case: the window swallows everything that remains *)
           assert (Hwtot : wmass (Z.to_nat curr') (x_root c + 1) cnt1
                           = it_mass 15%nat 1 cnt1).
           { assert (H15s : (15%nat
                     = Z.to_nat (x_root c)
                       + (Z.to_nat curr'
                          + Z.to_nat (15 - x_root c - curr')))%nat)
               by (clear -Hroot Hcb'; lia).
              assert (Hwm : wmass 15%nat 1 cnt1 = it_mass 15%nat 1 cnt1).
              { rewrite (wmass_it_mass 15%nat 1 cnt1)
                  by (clear -Hmx; lia).
                 replace (16 - 1 - Z.of_nat 15) with 0
                   by (clear -Hmx; lia).
                 rewrite Z.pow_0_r. ring. }
              rewrite <- Hwm. rewrite H15s.
              rewrite wmass_split.
              rewrite (wmass_zero_on (Z.to_nat (x_root c)) 1 cnt1)
                by (intros j Hj; apply Hcnt1z; clear -Hj Hgt Hroot; lia).
              replace (1 + Z.of_nat (Z.to_nat (x_root c)))
                with (x_root c + 1) by (clear -Hroot; lia).
              rewrite wmass_split.
              rewrite (wmass_zero_on (Z.to_nat (15 - x_root c - curr'))
                        (x_root c + 1 + Z.of_nat (Z.to_nat curr')) cnt1)
                by (intros j Hj; apply Hcnt1hi;
                    clear -Hj Hgl Hroot Hcb'; lia).
              ring. }
           rewrite Hwtot.
           destruct Hcase as [HM0 | (Hmx1 & _)];
             [| exfalso; clear -Hmx1 Hgt HL1mx Hroot; lia].
           assert (HK1lt : K1 < 2 ^ x_root c).
           { unfold K1.
              pose proof (zrev_lt (Z.to_nat (x_root c))
                            (huff1 mod 2 ^ x_root c)) as Hz.
              rewrite to_nat_pow in Hz by (clear -Hroot; lia). exact Hz. }
           assert (Hps : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
             by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
           assert (Hbnd : K1 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)
                          <= 2 ^ 15).
           { replace (K1 * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c))
               with ((K1 + 1) * 2 ^ (15 - x_root c)) by ring.
             rewrite <- Hps.
             apply Z.mul_le_mono_pos_r; clear -HK1lt HsPos; lia. }
           assert (H2_15 : (2:Z) ^ 15 = 32768) by reflexivity.
           clear -Hbnd HM0 HPnew. lia. }
    + (* still fits the root *)
      apply Z.ltb_ge in Hgt.
      cbn [andb] in Hstep.
      injection Hstep as Hst'. subst st'.
      destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & _)];
        [| exfalso; lia].
      destruct Hledph as [(Hd0 & Hu0 & Hn0) | (Hd2 & _)];
        [| exfalso; lia].
      unfold SubLedger, Pos.
      cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min
           s_count s_tbl].
      split; [| left; auto].
      assert (HF1 : tblF = it_fill (Z.to_nat (2 ^ x_root c / 2 ^ s_len st))
                             (s_tbl st) (0 + s_huff st) (2 ^ s_len st)
                             (it_here c st)).
      { unfold tblF. rewrite Hd, Z.sub_0_r, Hnx, Hc, Z.shiftr_0_r.
        rewrite !shiftl1 by lia. reflexivity. }
      rewrite HF1.
      replace (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1)
        with (zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 - s_len st)
              + 2 ^ (15 - s_len st))
        by (unfold Pos in Hpos, Hpos1; clear -Hpos Hpos1; lia).
      apply gen_step_short; [lia | lia | lia | exact Hhuff | |].
      { left. split; [exact Hherel|].
        rewrite Hbits_here, Hd. lia. }
      { unfold Pos in Hpos. rewrite <- Hpos. exact HrootB. }
Qed.

Print Assumptions ledger_step_cont.

(** ** 12.  The ledger at the exit: the finished table, classified

    At the break every count is zero, so the position reached the whole
    Kraft mass.  COMPLETE codes ([mass = 2^15]): the counter wrapped to 0,
    [it_finish] writes nothing, every unit and the open window are full.
    The one accepted incomplete shape ([max = 1], half mass): root is 1,
    the loop covered entry 0, and the fix-up writes the marker at entry 1. *)

Lemma ledger_step_break : forall ty c cnt0 st st1,
  ty = x_type c ->
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  LeafShape ty (it_here c st) ->
  it_step c st = ItBreak st1 ->
  2 ^ x_root c <= s_used st1
  /\ (forall j, 0 <= j < 2 ^ x_root c ->
      RootEntry ty (x_root c) (s_used st1) (it_finish st1 j))
  /\ (forall i, 2 ^ x_root c <= i < s_used st1 ->
      SubEntry ty (x_root c) (it_finish st1 i)).
Proof.
  intros ty c cnt0 st st1 Hcty Hctx Hinv Hled Hherel Hstep.
  pose proof Hctx as Hctx2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof Hinv as Hinv2.
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).
  destruct Hled as (HrootB & Hledph).
  unfold it_step in Hstep. cbv zeta in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1)) in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  destruct (Z.eqb (cnt1 (s_len st)) 0) eqn:Hhit; cbn [andb] in Hstep;
    [| exfalso;
       repeat match type of Hstep with
              | (if ?b then _ else _) = _ => destruct b
              end;
       discriminate Hstep ].
  destruct (Z.eqb (s_len st) (x_max c)) eqn:Hmxeq; cbn [andb] in Hstep;
    [| exfalso;
       repeat match type of Hstep with
              | (if ?b then _ else _) = _ => destruct b
              end;
       discriminate Hstep ].
  apply Z.eqb_eq in Hhit. apply Z.eqb_eq in Hmxeq.
  assert (Hcnt1z : forall l, 1 <= l <= 15 -> cnt1 l = 0).
  { intros l Hl. unfold cnt1, zset.
    destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
    - unfold cnt1, zset in Hhit. rewrite Z.eqb_refl in Hhit. exact Hhit.
    - rewrite (Hcnt l Hl).
      destruct (Z.ltb_spec l (s_len st)) as [H1|H1]; [reflexivity|].
      destruct (Z.eqb_spec l (s_len st)) as [H2|H2]; [contradiction|].
      apply Hmxz. clear -Hl H1 H2 Hmxeq Hmx. lia. }
  assert (Hmass0 : it_mass 15%nat 1 cnt1 = 0)
    by (apply it_mass_zero_on; intros i Hi; apply Hcnt1z; cbn in Hi; lia).
  assert (Hposbrk : Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
                    = it_mass 15%nat 1 cnt0).
  { unfold Pos in *. rewrite <- (pos_advance (it_mass 15%nat 1 cnt0)
                                  (s_count st) (s_len st) ltac:(lia)).
    unfold cnt1 in Hmass0. rewrite Hmass0. ring. }
  assert (Hbits_here : c_bits (it_here c st) = s_len st - s_drop st).
  { apply bits_here_val.
    destruct Hphase as [(Hd & _) | (Hd & Hrl & _)]; rewrite Hd; lia. }
  injection Hstep as Hst1. subst st1.
  cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min
       s_count s_tbl] in *.
  set (tblF := it_fill
                 (Z.to_nat (Z.shiftl 1 (s_curr st)
                            / Z.shiftl 1 (s_len st - s_drop st)))
                 (s_tbl st)
                 (s_next st + Z.shiftr (s_huff st) (s_drop st))
                 (Z.shiftl 1 (s_len st - s_drop st))
                 (it_here c st)) in *.
  assert (Hhuff' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
    by (rewrite (to_nat_pow (s_len st) ltac:(lia)); exact Hhuff).
  pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st)
                ltac:(lia) Hhuff') as Hinc.
  rewrite (Z2Nat.id (s_len st)) in Hinc by lia.
  unfold it_finish.
  cbn [s_huff s_next s_len s_drop s_tbl s_used].
  destruct Hcase as [Hfull | [Hmx1 Hhalf]].
  - (* COMPLETE *)
    assert (Hh1z : huff1 = 0).
    { destruct Hinc as [[Hw _] | [Hr Ha]]; [exact Hw|].
      exfalso.
      (* the non-wrap case puts the NEXT code's reversed index at 2^len —
         but zrev is always below 2^len *)
      pose proof (zrev_lt (Z.to_nat (s_len st)) huff1) as Hzl1.
      rewrite to_nat_pow in Hzl1 by lia.
      assert (Hs15 : 2 ^ s_len st * 2 ^ (15 - s_len st) = 2 ^ 15)
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      pose proof (pow2_pos_z (15 - s_len st) ltac:(lia)) as Hsp.
      assert (He2 : (zrev (Z.to_nat (s_len st)) (s_huff st) + 1)
                      * 2 ^ (15 - s_len st)
                    = 2 ^ s_len st * 2 ^ (15 - s_len st)).
      { rewrite Z.mul_add_distr_r.
        unfold Pos in Hpos, Hposbrk.
        clear -Hpos Hposbrk Hfull Hs15. lia. }
      assert (He3 : zrev (Z.to_nat (s_len st)) (s_huff st) + 1
                    = 2 ^ s_len st).
      { clear -He2 Hsp.
        assert (Hle : zrev (Z.to_nat (s_len st)) (s_huff st) + 1
                      <= 2 ^ s_len st)
          by (apply (mul_le_cancel_r _ _ _ Hsp); lia).
        assert (Hge : 2 ^ s_len st
                      <= zrev (Z.to_nat (s_len st)) (s_huff st) + 1)
          by (apply (mul_le_cancel_r _ _ _ Hsp); lia).
        lia. }
      assert (Ha' : zrev (Z.to_nat (s_len st)) huff1
                    = zrev (Z.to_nat (s_len st)) (s_huff st) + 1)
        by exact Ha.
      rewrite Ha', He3 in Hzl1.
      clear -Hzl1. lia. }
    rewrite Hh1z.
    replace (Z.eqb 0 0) with true by reflexivity.
    destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                       | (Hd & Hrl & Hnx & Hlow & Hlb)].
    + (* phase 1: the whole table is the root block *)
      destruct Hledph as [(Hd0 & Hu0 & Hn0) | (Hd2 & _)];
        [| exfalso; clear -Hd Hd2 Hroot; lia].
      assert (HF1 : tblF = it_fill (Z.to_nat (2 ^ x_root c / 2 ^ s_len st))
                             (s_tbl st) (0 + s_huff st) (2 ^ s_len st)
                             (it_here c st)).
      { unfold tblF. rewrite Hd, Z.sub_0_r, Hn0, Hc, Z.shiftr_0_r.
        rewrite !shiftl1 by lia. reflexivity. }
      assert (HrootF : GenBelow (RootEntry ty (x_root c) (s_used st))
                (x_root c) 15 tblF 0 (2 ^ 15)).
      { replace (2 ^ 15)
          with (zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 - s_len st)
                + 2 ^ (15 - s_len st))
          by (unfold Pos in Hpos, Hposbrk; clear -Hpos Hposbrk Hfull; lia).
        rewrite HF1.
        apply gen_step_short; [lia | lia | lia | exact Hhuff | |].
        - left. split; [exact Hherel|]. rewrite Hbits_here, Hd.
          clear -Hlen Hlr Hd. lia.
        - unfold Pos in Hpos. rewrite <- Hpos. exact HrootB. }
      split; [rewrite Hu0; clear -Hroot; lia|].
      split.
      * intros j Hj. apply HrootF; [exact Hj|].
        pose proof (zrev_lt (Z.to_nat (x_root c)) j) as Hzl.
        rewrite to_nat_pow in Hzl by lia.
        assert (Hsp : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        pose proof (pow2_pos_z (15 - x_root c) ltac:(clear -Hroot; lia)).
        clear -Hzl Hsp H. nia.
      * intros i Hi. exfalso. rewrite Hu0 in Hi. clear -Hi. lia.
    + (* phase 2 *)
      destruct Hledph as [(Hd0 & _) | (Hd2 & Hcb & Hue & Hnx2 & Hu16 & Hcl
                                       & Hopen & Hrp & Hguard)];
        [exfalso; clear -Hd Hd0 Hroot; lia|].
      set (hiO := Z.shiftr (s_huff st) (x_root c)) in *.
      assert (HhiO : 0 <= hiO < 2 ^ (s_len st - x_root c))
        by (unfold hiO; apply shiftr_range; lia).
      assert (HdecO : zrev (Z.to_nat (s_len st)) (s_huff st)
              = zrev (Z.to_nat (x_root c)) (s_huff st mod 2 ^ x_root c)
                  * 2 ^ (s_len st - x_root c)
                + zrev (Z.to_nat (s_len st - x_root c)) hiO)
        by (unfold hiO; apply zrev_decomp; [lia|lia|exact Hhuff]).
      assert (HscO : 2 ^ (s_len st - x_root c) * 2 ^ (15 - s_len st)
                     = 2 ^ (15 - x_root c))
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (HF2 : tblF
               = it_fill (Z.to_nat (2 ^ s_curr st
                                    / 2 ^ (s_len st - x_root c)))
                   (s_tbl st) (s_next st + hiO)
                   (2 ^ (s_len st - x_root c)) (it_here c st)).
      { unfold tblF, hiO. rewrite Hd, !shiftl1 by lia. reflexivity. }
      assert (Hmiss_low : forall j, j < s_next st -> tblF j = s_tbl st j).
      { intros j Hj. rewrite HF2.
        rewrite (it_fill_get _ _ _ _ _ j) by (apply pow2_pos_z; lia).
        replace (Z.leb (s_next st + hiO) j) with false
          by (symmetry; apply Z.leb_gt; clear -Hj HhiO Hnx2; lia).
        reflexivity. }
      (* the intra-unit position, and the whole-unit fact at the break *)
      assert (HPos15 : UnitStart (x_root c) (s_low st)
                       + zrev (Z.to_nat (s_len st - x_root c)) hiO
                           * 2 ^ (15 - s_len st)
                       + 2 ^ (15 - s_len st) = 2 ^ 15).
      { unfold UnitStart. rewrite Hlow.
        rewrite Hpos in Hposbrk. rewrite HdecO in Hposbrk.
        rewrite Z.mul_add_distr_r, <- Z.mul_assoc, HscO in Hposbrk.
        clear -Hposbrk Hfull. lia. }
      assert (Hoflfull : GenBelow (SubEntry ty (x_root c)) (s_curr st)
                (15 - x_root c) tblF (s_next st)
                (zrev (Z.to_nat (s_len st - x_root c)) hiO
                   * 2 ^ ((15 - x_root c) - (s_len st - x_root c))
                 + 2 ^ ((15 - x_root c) - (s_len st - x_root c)))).
      { rewrite HF2.
        apply gen_step_short; [ | lia | lia | exact HhiO | |].
        - (* 1 <= len - root <= curr: the guard argument, as in the step *)
          split; [clear -Hrl; lia|].
          destruct (Z_le_gt_dec (s_len st - x_root c) (s_curr st)) as [Hok|Hbad];
            [exact Hok | exfalso].
          assert (Hwz : wmass (Z.to_nat (x_root c + s_curr st)) 1
                          (s_count st) = 0).
          { apply wmass_zero_on. intros j Hj.
            rewrite (Hcnt j ltac:(clear -Hj Hroot Hcb; lia)).
            replace (Z.ltb j (s_len st)) with true
              by (symmetry; apply Z.ltb_lt; clear -Hj Hbad Hroot Hcb; lia).
            reflexivity. }
          rewrite Hwz in Hguard.
          assert (HzrO : zrev (Z.to_nat (s_len st - x_root c)) hiO
                         < 2 ^ (s_len st - x_root c)).
          { pose proof (zrev_lt (Z.to_nat (s_len st - x_root c)) hiO) as Hz1.
            rewrite to_nat_pow in Hz1 by lia. exact Hz1. }
          pose proof (pow2_pos_z (15 - s_len st) ltac:(lia)).
          unfold UnitStart in Hguard. rewrite Hlow in Hguard.
          rewrite Hpos in Hguard. rewrite HdecO in Hguard.
          rewrite Z.mul_add_distr_r, <- Z.mul_assoc, HscO in Hguard.
          clear -Hguard HzrO HscO HhiO H. nia.
        - split; [exact Hherel|]. rewrite Hbits_here, Hd.
          clear -Hrl Hlen. lia.
        - replace ((15 - x_root c) - (s_len st - x_root c))
            with (15 - s_len st) by (clear -Hroot; lia).
          assert (HUSo : Pos (it_mass 15%nat 1 cnt0) st
                           - UnitStart (x_root c) (s_low st)
                         = zrev (Z.to_nat (s_len st - x_root c)) hiO
                             * 2 ^ (15 - s_len st)).
          { unfold UnitStart. rewrite Hlow, Hpos, HdecO.
            rewrite Z.mul_add_distr_r, <- Z.mul_assoc, HscO. ring. }
          rewrite <- HUSo. exact Hopen. }
      assert (Hsubfull : forall i,
                s_next st <= i < s_next st + 2 ^ s_curr st ->
                SubEntry ty (x_root c) (tblF i)).
      { intros i Hi.
        replace i with (s_next st + (i - s_next st)) by (clear -Hi; lia).
        apply Hoflfull; [clear -Hi Hcb; lia|].
        replace ((15 - x_root c) - (s_len st - x_root c))
          with (15 - s_len st) by (clear -Hroot; lia).
        (* the window position reached the unit's end *)
        assert (Hcap15 : UnitStart (x_root c) (s_low st)
                         <= 2 ^ 15 - 2 ^ (15 - x_root c)).
        { unfold UnitStart.
          pose proof (zrev_lt (Z.to_nat (x_root c)) (s_low st)) as Hzl.
          rewrite to_nat_pow in Hzl by lia.
          pose proof (zrev_nonneg (Z.to_nat (x_root c)) (s_low st)) as Hzn.
          assert (Hsp : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
            by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
          pose proof (pow2_pos_z (15 - x_root c) ltac:(clear -Hroot; lia)).
          clear -Hzl Hzn Hsp H. nia. }
        pose proof (zrev_lt (Z.to_nat (s_curr st)) (i - s_next st)) as Hzl.
        rewrite to_nat_pow in Hzl by (clear -Hcb; lia).
        pose proof (pow2_pos_z ((15 - x_root c) - s_curr st)
                      ltac:(clear -Hcb; lia)) as Hq2.
        pose proof (zrev_nonneg (Z.to_nat (s_curr st)) (i - s_next st))
          as Hq3.
        assert (Hpc : (zrev (Z.to_nat (s_curr st)) (i - s_next st) + 1)
                        * 2 ^ ((15 - x_root c) - s_curr st)
                      <= 2 ^ s_curr st
                        * 2 ^ ((15 - x_root c) - s_curr st))
          by (apply Z.mul_le_mono_pos_r; clear -Hzl Hq2; lia).
        rewrite <- Z.pow_add_r in Hpc by (clear -Hcb Hroot; lia).
        replace (s_curr st + ((15 - x_root c) - s_curr st))
          with (15 - x_root c) in Hpc by (clear -Hcb; lia).
        clear -Hpc Hq2 Hq3 HPos15 Hcap15. lia. }
      assert (HrootF : GenBelow (RootEntry ty (x_root c) (s_used st))
                (x_root c) 15 tblF 0 (2 ^ 15)).
      { replace (2 ^ 15)
          with (zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 - s_len st)
                + 2 ^ (15 - s_len st))
          by (unfold Pos in Hpos, Hposbrk; clear -Hpos Hposbrk Hfull; lia).
        rewrite HF2.
        apply gen_step_long;
          [lia | lia | lia | lia | exact Hhuff | clear -Hnx2 HhiO; lia
           | apply pow2_pos_z; lia | |].
        - unfold Pos in Hpos. rewrite <- Hpos. exact HrootB.
        - replace (0 + s_huff st mod 2 ^ x_root c) with (s_low st)
            by (rewrite Hlow; lia).
          exact Hrp. }
      split.
      { rewrite Hue.
        pose proof (pow2_pos_z (s_curr st) ltac:(clear -Hcb; lia)).
        clear -Hnx2 H. lia. }
      split.
      * intros j Hj. apply HrootF; [exact Hj|].
        pose proof (zrev_lt (Z.to_nat (x_root c)) j) as Hzl.
        rewrite to_nat_pow in Hzl by lia.
        assert (Hsp : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        pose proof (pow2_pos_z (15 - x_root c) ltac:(clear -Hroot; lia)).
        clear -Hzl Hsp H. nia.
      * intros i Hi. rewrite Hue in Hi.
        destruct (Z_lt_ge_dec i (s_next st)) as [Hi1'|Hi2'].
        -- rewrite Hmiss_low by (clear -Hi1'; lia). apply Hcl.
           clear -Hi Hi1'. lia.
        -- apply Hsubfull. clear -Hi Hi2'. lia.
  - (* INCOMPLETE-BUT-ACCEPTED: max = 1 *)
    assert (Hr1 : x_root c = 1) by (clear -Hrootmx Hmx1 Hroot; lia).
    assert (Hl1 : s_len st = 1) by (clear -Hmxeq Hmx1; lia).
    destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & _)];
      [| exfalso; clear -Hrl Hl1 Hr1; lia].
    destruct Hledph as [(Hd0 & Hu0 & Hn0) | (Hd2 & _)];
      [| exfalso; clear -Hd Hd2 Hroot; lia].
    assert (HF1 : tblF = it_fill (Z.to_nat (2 ^ x_root c / 2 ^ s_len st))
                           (s_tbl st) (0 + s_huff st) (2 ^ s_len st)
                           (it_here c st)).
    { unfold tblF. rewrite Hd, Z.sub_0_r, Hn0, Hc, Z.shiftr_0_r.
      rewrite !shiftl1 by lia. reflexivity. }
    assert (Hposzero : Pos (it_mass 15%nat 1 cnt0) st = 0).
    { replace (15 - s_len st) with 14 in Hposbrk by (clear -Hl1; lia).
      replace ((2:Z) ^ 14) with 16384 in Hposbrk, Hhalf by reflexivity.
      clear -Hposbrk Hhalf. lia. }
    assert (Hzh : zrev (Z.to_nat (s_len st)) (s_huff st) = 0).
    { rewrite Hpos in Hposzero.
      pose proof (pow2_pos_z (15 - s_len st) ltac:(lia)).
      pose proof (zrev_nonneg (Z.to_nat (s_len st)) (s_huff st)).
      clear -Hposzero H H0. nia. }
    assert (Hh1one : huff1 = 1).
    { destruct Hinc as [[Hw Hz1] | [Hr Ha]].
      - exfalso. rewrite Hzh in Hz1. rewrite Hl1 in Hz1.
        change ((2:Z) ^ 1) with 2 in Hz1. clear -Hz1. lia.
      - assert (Ha' : zrev (Z.to_nat (s_len st)) huff1
                      = zrev (Z.to_nat (s_len st)) (s_huff st) + 1)
          by exact Ha.
        assert (Hr' : 0 <= huff1 < 2 ^ s_len st) by exact Hr.
        apply (zrev_inj (Z.to_nat (s_len st))).
        + rewrite (to_nat_pow (s_len st) ltac:(lia)). lia.
        + rewrite (to_nat_pow (s_len st) ltac:(lia)), Hl1.
          change ((2:Z) ^ 1) with 2. clear; lia.
        + rewrite Ha', Hzh, Hl1. change (Z.to_nat 1) with 1%nat.
          rewrite (zrev_one 0). reflexivity. }
    assert (HrootF : GenBelow (RootEntry ty (x_root c) (s_used st))
              (x_root c) 15 tblF 0 (2 ^ 14)).
    { replace ((2:Z) ^ 14)
        with (zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 - s_len st)
              + 2 ^ (15 - s_len st))
        by (rewrite Hzh, Hl1;
            replace (15 - 1) with 14 by (clear; lia); ring).
      rewrite HF1.
      apply gen_step_short; [lia | lia | lia | exact Hhuff | |].
      - left. split; [exact Hherel|]. rewrite Hbits_here, Hd.
        clear -Hlen Hlr Hd. lia.
      - unfold Pos in Hpos. rewrite <- Hpos. exact HrootB. }
    rewrite Hh1one.
    replace (Z.eqb 1 0) with false by reflexivity.
    rewrite Hn0.
    replace (0 + 1) with 1 by (clear; lia).
    split; [rewrite Hu0; clear -Hroot; lia|].
    split.
    + intros j Hj.
      rewrite Hr1 in Hj. change ((2:Z) ^ 1) with 2 in Hj.
      destruct (Z.eq_dec j 1) as [->|Hne].
      * rewrite tset_same. left.
        split.
        -- apply marker_leafshape; [clear; lia | |].
           ++ vm_compute. discriminate.
           ++ vm_compute. reflexivity.
        -- rewrite bits_mkCodeT by (clear -Hlen Hd; lia).
           rewrite Hd, Hl1, Hr1. clear; lia.
      * assert (Hj0 : j = 0) by (clear -Hj Hne; lia). subst j.
        rewrite tset_other by (clear -Hne; lia).
        apply HrootF; [rewrite Hr1; change ((2:Z) ^ 1) with 2; clear; lia|].
        rewrite Hr1. change (Z.to_nat 1) with 1%nat.
        rewrite zrev_zero.
        replace (15 - 1) with 14 by (clear; lia).
        replace ((0 + 1) * 2 ^ 14) with (2 ^ 14) by ring.
        clear; lia.
    + intros i Hi. exfalso. rewrite Hu0, Hr1 in Hi.
      change ((2:Z) ^ 1) with 2 in Hi. clear -Hi. lia.
Qed.

(** ** 13.  Through the loop, and from the call *)

Lemma ledger_loop : forall n ty c cnt0 st st1,
  ty = x_type c ->
  (x_type c = CT_LENS \/ x_type c = CT_DISTS \/ x_max c <= x_root c) ->
  (forall st', LeafShape ty (it_here c st')) ->
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger ty c cnt0 st ->
  it_loop n c st = Some (ItBreak st1) ->
  2 ^ x_root c <= s_used st1
  /\ (forall j, 0 <= j < 2 ^ x_root c ->
      RootEntry ty (x_root c) (s_used st1) (it_finish st1 j))
  /\ (forall i, 2 ^ x_root c <= i < s_used st1 ->
      SubEntry ty (x_root c) (it_finish st1 i)).
Proof.
  induction n as [|n IH]; intros ty c cnt0 st st1 Hcty Hty Hhere Hctx Hinv
                                 Hled Hl;
    cbn [it_loop] in Hl; [discriminate Hl|].
  destruct (it_step c st) as [st'|st'|t'] eqn:Hs.
  - exact (IH ty c cnt0 st' st1 Hcty Hty Hhere Hctx
             (cov_step_cont c cnt0 st st' Hctx Hinv Hs)
             (ledger_step_cont ty c cnt0 st st' Hcty Hty Hctx Hinv Hled
                (Hhere st) Hs) Hl).
  - injection Hl as <-.
    exact (ledger_step_break ty c cnt0 st st' Hcty Hctx Hinv Hled
             (Hhere st) Hs).
  - discriminate Hl.
Qed.

(** The two [it_pre] projections the initial ledger needs. *)
Lemma it_pre_go_count : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  s_count st = sw_cnt lens codes.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  apply prego_inj_st in H. rewrite <- H. cbn [s_count]. reflexivity.
Qed.

Lemma it_pre_go_shape : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  s_drop st = 0 /\ s_next st = 0.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  apply prego_inj_st in H. rewrite <- H.
  cbn [s_drop s_next]. split; reflexivity.
Qed.


Lemma it_pre_go_type : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_type c = ty.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  injection H as Hc _. rewrite <- Hc. cbn [x_type]. reflexivity.
Qed.

Lemma it_pre_go_work : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_work c = sw_work lens codes.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  injection H as Hc _. rewrite <- Hc. cbn [x_work]. reflexivity.
Qed.

Lemma it_pre_go_lens_arrays : forall lens codes root0 t0 c st,
  it_pre CT_LENS lens codes root0 t0 = PreGo c st ->
  x_match c = 257 /\ x_base c = lbase /\ x_extra c = lext.
Proof.
  intros lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete CT_LENS lft _); [discriminate H|].
  destruct (it_enough CT_LENS _); [discriminate H|].
  injection H as Hc _. rewrite <- Hc. cbn [x_match x_base x_extra].
  vm_compute (Z.eqb CT_LENS CT_LENS).
  split; [reflexivity|]. split; reflexivity.
Qed.

Lemma sort_work_range : forall lens codes s,
  0 < codes -> 0 <= sw_work lens codes s < codes.
Proof.
  intros lens codes s Hc. unfold sw_work.
  apply sort_zzero_range. exact Hc.
Qed.

(** The ledger holds at the loop's entry: nothing is claimed at position 0,
    and the used extent is exactly the root block. *)
Lemma ledger_pre : forall ty lens codes root0 t0 c st,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_pre ty lens codes root0 t0 = PreGo c st ->
  SubLedger ty c (sw_cnt lens codes) st.
Proof.
  intros ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre.
  destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
    as [Hctx Hinv].
  destruct Hctx as (Hroot & _).
  destruct (it_pre_go_shape ty lens codes root0 t0 c st Hpre) as [Hd0 Hn0].
  pose proof (it_pre_go_count ty lens codes root0 t0 c st Hpre) as Hcnt.
  pose proof (pre_used_go ty lens codes root0 t0 c st Hpre) as Hused.
  split.
  - (* nothing is fully below position 0 *)
    intros k Hk Hu. exfalso.
    unfold Pos in Hu. rewrite Hcnt in Hu.
    pose proof (zrev_nonneg (Z.to_nat (x_root c)) k).
    pose proof (pow2_pos_z (15 - x_root c) ltac:(lia)).
    assert (0 < (zrev (Z.to_nat (x_root c)) k + 1) * 2 ^ (15 - x_root c))
      by (apply Z.mul_pos_pos; lia).
    clear -Hu H1. lia.
  - left. split; [exact Hd0|]. split; [|exact Hn0].
    rewrite Hused. apply shiftl1. lia.
Qed.

(** ** 14.  THE ENDPOINT: an accepted build's table, fully classified

    Type-restricted to the two ENOUGH-capped kinds: those are the ones
    whose sub-table pointers the decoder chases (the CODES table never
    opens a sub-table at its real call, and its consumer needs only the
    width/value bounds, available from the ported [GtTblWidth]). *)

Theorem it_covers_all : forall ty lens codes root0 t0 out,
  (ty = CT_LENS \/ ty = CT_DISTS) ->
  it_wf ty lens codes root0 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  2 ^ (o_bits out) <= o_used out
  /\ (forall j, 0 <= j < 2 ^ (o_bits out) ->
      RootEntry ty (o_bits out) (o_used out) (o_tbl out j))
  /\ (forall i, 2 ^ (o_bits out) <= i < o_used out ->
      SubEntry ty (o_bits out) (o_tbl out i)).
Proof.
  intros ty lens codes root0 t0 out Hty Hwf Hmodel Hret.
  destruct Hwf as (Hc0 & Hlens & Hroot0 & Hkinds).
  assert (Hcodes : 0 <= codes) by lia.
  unfold it_model in Hmodel.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hmodel as <-. cbn in Hret. lia.
  - (* PreEmpty: two markers, root 1, used 2 *)
    rewrite (it_pre_empty_shape ty lens codes root0 t0 temp Hpre) in Hmodel.
    injection Hmodel as <-. cbn [o_bits o_used o_tbl].
    split; [change ((2:Z) ^ 1) with 2; lia|].
    split.
    + intros j Hj. change ((2:Z) ^ 1) with 2 in Hj.
      assert (Hmk : RootEntry ty 1 2 (mkCodeT 64 1 0)).
      { left. split.
        - apply marker_leafshape; [lia | |].
          + vm_compute. discriminate.
          + vm_compute. reflexivity.
        - rewrite bits_mkCodeT by lia. lia. }
      destruct (Z.eq_dec j 1) as [->|Hne].
      * rewrite tset_same. exact Hmk.
      * assert (j = 0) by lia. subst j.
        rewrite tset_other by lia. rewrite tset_same. exact Hmk.
    + intros i Hi. exfalso. change ((2:Z) ^ 1) with 2 in Hi. lia.
  - injection Hmodel as <-. cbn in Hret. lia.
  - (* PreGo: the loop *)
    destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
      as [Hctx Hinv].
    pose proof (ledger_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0
                  Hpre) as Hled.
    assert (Hcty : ty = x_type c)
      by (symmetry; exact (it_pre_go_type ty lens codes root0 t0 c st Hpre)).
    assert (Htyc : x_type c = CT_LENS \/ x_type c = CT_DISTS
                   \/ x_max c <= x_root c)
      by (rewrite <- Hcty; destruct Hty as [?|?]; [left|right; left];
          assumption).
    assert (Hhere : forall st', LeafShape ty (it_here c st')).
    { intros st'.
      pose proof (it_pre_go_work ty lens codes root0 t0 c st Hpre) as Hwk.
      assert (Hwr : forall s, 0 <= x_work c s < codes)
        by (intros s; rewrite Hwk; apply sort_work_range; lia).
      destruct Hty as [HL|HD].
      - subst ty.
        destruct (it_pre_go_lens_arrays lens codes root0 t0 c st Hpre)
          as (Hm & Hb & He).
        apply (here_leafshape_lens c st' Hm Hb He).
        intros s. pose proof (Hwr s).
        destruct Hkinds as [(Hk & Hcap)|[(Hk & Hcap)|(Hk & Hcap)]];
          try (exfalso; vm_compute in Hk; discriminate Hk).
        lia.
      - subst ty.
        destruct (it_pre_go_dists lens codes root0 t0 c st Hpre)
          as (Hm & Hb & He).
        apply (here_leafshape_dists c st' Hm Hb He).
        intros s. pose proof (Hwr s).
        destruct Hkinds as [(Hk & Hcap)|[(Hk & Hcap)|(Hk & Hcap)]];
          try (exfalso; vm_compute in Hk; discriminate Hk).
        lia. }
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hloop;
      try discriminate Hmodel.
    + (* ItBreak: the accepted build *)
      injection Hmodel as <-. cbn [o_bits o_used o_tbl].
      exact (ledger_loop (S (Z.to_nat codes)) ty c (sw_cnt lens codes) st st'
               Hcty Htyc Hhere Hctx Hinv Hled Hloop).
    + (* ItOverflow: rejected *)
      injection Hmodel as <-. cbn in Hret. lia.
Qed.

Print Assumptions ledger_step_cont.
Print Assumptions ledger_step_break.
Print Assumptions it_covers_all.
