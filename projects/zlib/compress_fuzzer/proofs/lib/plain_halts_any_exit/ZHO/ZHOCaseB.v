(** * ZHOCaseB — the Case-B closure: the dynamic counter fits the budget.

    OWNER: huffman-opt (scope items 1+2+3+4 assembled).  THE consumer
    deliverable: under the ZRL1FastNone bed's premise context,

        ts_optlen (S2P ts) <= 8 * slen + 21

    which discharges zr_l1_min_fits's RIGHT disjunct unconditionally
    (l1-adversary wraps with [or_intror]).

    CHAIN:  ts_optlen (S2P ts)
      <= toks_cost(dyn) + EOB-len + desc + 6            [ZHOOl]
      =  sum count*cost_L(dyn) + sum count*cost_D(dyn)
         + EOB-len + desc + 6                           [toks_cost_regroup]
      =  sum f*len_L + sum f*xb + sum f*len_D + sum f*xd + desc + 6
                                                        [FreqInv count/freq tie]
      <= sum f*C_L + K + xb-terms + (sum f*C_D + K | D-corner) + desc + 6
                                                        [build_tree_cost_opt_main x2,
                                                         zho_d_corner when <=1 live dist]
      <= 8*slen + 21                                    [zho_bl_cap + zho_cert]

    The comparison family is RANK-adaptive (l1-adversary's LP: size-based
    families erode via the epsilon-support trick): the mass-dominant
    length code gets 2 bits, EOB 3, literals 9, other length codes 10
    (integer Kraft 29568 <= 2^15), distances flat 5.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees BtWin BtTerm CbEmit CbFold
  SendItems SendGo ScanCount ScanBase HuffCover ClStream
  BtBlSide BtCensus1 BtCensus2 BtSized BtPass1 BtPass2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  ZReproG6A ZReproG6C ZReproG6D ZReproG6E ZReproG6G ZReproG6N.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOStmt ZHOMain ZHOOl.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** The comparison family (rank-adaptive) *)

(** the mass-dominant length code of the ENTRY L tree (>= 257 always) *)
Definition zho_dom (t : Tree) : Z :=
  fold_left (fun best c => if t_freq t best <? t_freq t c then c else best)
            (map Z.of_nat (seq 258 28)) 257.

Definition zho_CL (t : Tree) (n : Z) : Z :=
  if Z.eqb n (zho_dom t) then 2
  else if Z.eqb n 256 then 3
  else if Z.ltb n 256 then 9 else 10.

Definition zho_CD (n : Z) : Z := 5.

Lemma zho_fold_dom_in : forall (t : Tree) (l : list Z) (acc : Z),
  In (fold_left (fun best c => if t_freq t best <? t_freq t c then c else best)
        l acc) (acc :: l).
Proof.
  intros t l. induction l as [|c l IH]; intro acc.
  - left. reflexivity.
  - cbn [fold_left].
    destruct (t_freq t acc <? t_freq t c).
    + destruct (IH c) as [E|Hin]; [right; left; exact E | right; right; exact Hin].
    + destruct (IH acc) as [E|Hin]; [left; exact E | right; right; exact Hin].
Qed.

Lemma zho_fold_dom_ge : forall (t : Tree) (l : list Z) (acc x : Z),
  In x (acc :: l) ->
  t_freq t x
  <= t_freq t (fold_left
        (fun best c => if t_freq t best <? t_freq t c then c else best) l acc).
Proof.
  intros t l. induction l as [|c l IH]; intros acc x Hin.
  - destruct Hin as [<-|[]]. cbn [fold_left]. lia.
  - cbn [fold_left].
    destruct (Z.ltb_spec (t_freq t acc) (t_freq t c)) as [Hlt|Hge].
    + destruct Hin as [<-|[<-|Hin]].
      * eapply Z.le_trans; [apply Z.lt_le_incl; exact Hlt|].
        apply (IH c c). left; reflexivity.
      * apply (IH c c). left; reflexivity.
      * apply (IH c x). right; exact Hin.
    + destruct Hin as [<-|[<-|Hin]].
      * apply (IH acc acc). left; reflexivity.
      * eapply Z.le_trans; [exact Hge|].
        apply (IH acc acc). left; reflexivity.
      * apply (IH acc x). right; exact Hin.
Qed.

Lemma zho_dom_range : forall t, 257 <= zho_dom t <= 285.
Proof.
  intro t. unfold zho_dom.
  pose proof (zho_fold_dom_in t (map Z.of_nat (seq 258 28)) 257) as Hin.
  destruct Hin as [E|Hin].
  - rewrite <- E. lia.
  - apply in_map_iff in Hin. destruct Hin as (m & Em & Hm).
    apply in_seq in Hm. rewrite <- Em. lia.
Qed.

Lemma zho_dom_max : forall t c, 257 <= c <= 285 ->
  t_freq t c <= t_freq t (zho_dom t).
Proof.
  intros t c Hc. unfold zho_dom.
  apply zho_fold_dom_ge.
  destruct (Z.eqb_spec c 257) as [->|Hne].
  - left; reflexivity.
  - right. apply in_map_iff. exists (Z.to_nat c).
    split; [lia|]. apply in_seq. lia.
Qed.

(** the SECOND-ranked length code: argmax excluding [zho_dom] (coarse2
    family; countersigned repair of the {3,4} dominance-boundary kink) *)
Definition zho_sec (t : Tree) : Z :=
  fold_left (fun best c =>
               if Z.eqb c (zho_dom t) then best
               else if t_freq t best <? t_freq t c then c else best)
            (map Z.of_nat (seq 258 28))
            (if Z.eqb (zho_dom t) 257 then 258 else 257).

Lemma zho_fold_sec_inv : forall (t : Tree) (d : Z) (l : list Z) (acc : Z),
  acc <> d ->
  In (fold_left (fun best c => if Z.eqb c d then best
                               else if t_freq t best <? t_freq t c then c
                               else best) l acc) (acc :: l)
  /\ fold_left (fun best c => if Z.eqb c d then best
                              else if t_freq t best <? t_freq t c then c
                              else best) l acc <> d
  /\ t_freq t acc
     <= t_freq t (fold_left (fun best c => if Z.eqb c d then best
                                           else if t_freq t best <? t_freq t c
                                                then c else best) l acc)
  /\ (forall x, In x l -> x <> d ->
      t_freq t x
      <= t_freq t (fold_left (fun best c => if Z.eqb c d then best
                                            else if t_freq t best <? t_freq t c
                                                 then c else best) l acc)).
Proof.
  intros t d l. induction l as [|c l IH]; intros acc Hacc.
  - cbn [fold_left]. repeat split.
    + left; reflexivity.
    + exact Hacc.
    + lia.
    + intros x [] _.
  - cbn [fold_left].
    destruct (Z.eqb_spec c d) as [->|Hcd].
    + destruct (IH acc Hacc) as (Hin & Hnd & Hge & Hall).
      repeat split.
      * destruct Hin as [E|Hin'];
          [left; exact E | right; right; exact Hin'].
      * exact Hnd.
      * exact Hge.
      * intros x [->|Hx] Hxd; [congruence | exact (Hall x Hx Hxd)].
    + destruct (Z.ltb_spec (t_freq t acc) (t_freq t c)) as [Hlt|Hge0].
      * destruct (IH c Hcd) as (Hin & Hnd & Hge & Hall).
        repeat split.
        -- destruct Hin as [E|Hin'];
             [right; left; exact E | right; right; exact Hin'].
        -- exact Hnd.
        -- eapply Z.le_trans; [apply Z.lt_le_incl; exact Hlt | exact Hge].
        -- intros x [->|Hx] Hxd; [exact Hge | exact (Hall x Hx Hxd)].
      * destruct (IH acc Hacc) as (Hin & Hnd & Hge & Hall).
        repeat split.
        -- destruct Hin as [E|Hin'];
             [left; exact E | right; right; exact Hin'].
        -- exact Hnd.
        -- exact Hge.
        -- intros x [->|Hx] Hxd;
             [eapply Z.le_trans; [exact Hge0 | exact Hge]
             | exact (Hall x Hx Hxd)].
Qed.

Lemma zho_sec_init_ne : forall t,
  (if Z.eqb (zho_dom t) 257 then 258 else 257) <> zho_dom t.
Proof.
  intro t. destruct (Z.eqb_spec (zho_dom t) 257) as [E|Hne]; lia.
Qed.

Lemma zho_sec_range : forall t, 257 <= zho_sec t <= 285.
Proof.
  intro t. unfold zho_sec.
  destruct (zho_fold_sec_inv t (zho_dom t) (map Z.of_nat (seq 258 28))
              (if Z.eqb (zho_dom t) 257 then 258 else 257)
              (zho_sec_init_ne t)) as (Hin & _ & _ & _).
  destruct Hin as [E|Hin'].
  - rewrite <- E. destruct (Z.eqb_spec (zho_dom t) 257); lia.
  - apply in_map_iff in Hin'. destruct Hin' as (m & Em & Hm).
    apply in_seq in Hm. rewrite <- Em. lia.
Qed.

Lemma zho_sec_ne_dom : forall t, zho_sec t <> zho_dom t.
Proof.
  intro t. unfold zho_sec.
  destruct (zho_fold_sec_inv t (zho_dom t) (map Z.of_nat (seq 258 28))
              (if Z.eqb (zho_dom t) 257 then 258 else 257)
              (zho_sec_init_ne t)) as (_ & Hnd & _ & _).
  exact Hnd.
Qed.

Lemma zho_sec_max : forall t c, 257 <= c <= 285 -> c <> zho_dom t ->
  t_freq t c <= t_freq t (zho_sec t).
Proof.
  intros t c Hc Hcd. unfold zho_sec.
  (* decide the init literal FIRST so the invariant's instantiation and the
     goal share one spelling (unifying mismatched inits converts two huge
     folds and hangs) *)
  destruct (Z.eqb_spec (zho_dom t) 257) as [Ed|Hnd].
  - (* dom = 257: init = 258, and c <> 257 *)
    change (if true then 258 else 257) with 258.
    rewrite Ed in Hcd.
    destruct (zho_fold_sec_inv t (zho_dom t) (map Z.of_nat (seq 258 28))
                258 ltac:(lia)) as (_ & _ & _ & Hall).
    apply Hall; [|rewrite Ed; exact Hcd].
    apply in_map_iff. exists (Z.to_nat c).
    split; [lia|]. apply in_seq. lia.
  - (* dom <> 257: init = 257 *)
    change (if false then 258 else 257) with 257.
    destruct (zho_fold_sec_inv t (zho_dom t) (map Z.of_nat (seq 258 28))
                257 ltac:(lia)) as (_ & _ & Hge & Hall).
    destruct (Z.eqb_spec c 257) as [->|Hne257].
    + exact Hge.
    + apply Hall; [|exact Hcd].
      apply in_map_iff. exists (Z.to_nat c).
      split; [lia|]. apply in_seq. lia.
Qed.

(** sum helpers *)
Lemma zho_wsum_le_pt : forall (f g : Z -> Z) lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> f i <= g i) ->
  wsum f lo n <= wsum g lo n.
Proof.
  intros f g lo n; revert lo; induction n as [|k IH]; intros lo Hpt;
    cbn [wsum]; [lia|].
  cbv beta.
  pose proof (Hpt lo ltac:(rewrite Nat2Z.inj_succ; lia)).
  pose proof (IH (lo + 1)
                ltac:(intros i Hi; apply Hpt; rewrite Nat2Z.inj_succ; lia)).
  lia.
Qed.

Lemma zho_ind_sum_le1 : forall (g : Z -> bool) lo n,
  (forall i j, lo <= i < lo + Z.of_nat n -> lo <= j < lo + Z.of_nat n ->
     i <> j -> g i = false \/ g j = false) ->
  wsum (fun i => ind (g i)) lo n <= 1.
Proof.
  intros g lo n; revert lo; induction n as [|k IH]; intros lo Hpw;
    cbn [wsum]; [lia|].
  cbv beta.
  destruct (g lo) eqn:Eg.
  - assert (Ht0 : wsum (fun i => ind (g i)) (lo + 1) k = 0).
    { apply g6_wsum_zero. intros p Hp.
      destruct (Hpw lo p ltac:(rewrite Nat2Z.inj_succ; lia)
                  ltac:(rewrite Nat2Z.inj_succ; lia) ltac:(lia)) as [E|E];
        [congruence | rewrite E; reflexivity]. }
    rewrite Ht0. cbn [ind]. lia.
  - cbn [ind].
    pose proof (IH (lo + 1)
                  ltac:(intros i j Hi Hj Hne;
                        apply Hpw; try (rewrite Nat2Z.inj_succ); lia)).
    lia.
Qed.

Lemma zho_ind_member_ge1 : forall (g : Z -> bool) lo n p,
  lo <= p < lo + Z.of_nat n -> g p = true ->
  1 <= wsum (fun i => ind (g i)) lo n.
Proof.
  intros g lo n; revert lo; induction n as [|k IH]; intros lo p Hp Hg.
  - cbn [Z.of_nat] in Hp. lia.
  - rewrite Nat2Z.inj_succ in Hp. cbn [wsum]. cbv beta.
    assert (Hnn : 0 <= wsum (fun i => ind (g i)) (lo + 1) k).
    { apply wsum_nonneg. intros i _. destruct (g i); cbn [ind]; lia. }
    destruct (Z.eq_dec p lo) as [->|Hne].
    + rewrite Hg. cbn [ind]. lia.
    + pose proof (IH (lo + 1) p ltac:(lia) Hg).
      destruct (g lo); cbn [ind]; lia.
Qed.

(** ** The tree-description cap *)

(** every send item carries exactly one code-length symbol *)
Lemma zho_items_syms_len : forall l,
  length (items_syms l) = length l.
Proof.
  induction l as [|it l IH]; [reflexivity|].
  unfold items_syms in *. cbn [flat_map].
  rewrite length_app, IH.
  destruct it; reflexivity.
Qed.

(** the per-symbol counts over [0,19) sum to at most the stream length *)
Lemma zho_hid_sum_le : forall (l : list Z),
  wsum (fun sy => hid_zcount sy l) 0 19 <= Z.of_nat (length l).
Proof.
  induction l as [|z l IH].
  - cbn [length]. cbn [Z.of_nat].
    rewrite (g6_wsum_zero (fun sy => hid_zcount sy []) 0 19); [lia|].
    intros p _. unfold hid_zcount. reflexivity.
  - cbn [length]. rewrite Nat2Z.inj_succ.
    rewrite (wsum_ext (fun sy => hid_zcount sy (z :: l))
               (fun sy => ind (Z.eqb z sy) + hid_zcount sy l) 0 19).
    2:{ intros p _. unfold hid_zcount.
        cbn [count_occ].
        destruct (Z.eq_dec z p) as [E|Hne];
          destruct (Z.eqb_spec z p) as [E'|Hne']; try congruence;
          cbn [ind]; lia. }
    rewrite wsum_plus.
    assert (Hle1 : wsum (fun sy => ind (Z.eqb z sy)) 0 19 <= 1).
    { apply zho_ind_sum_le1.
      intros i j _ _ Hne.
      destruct (Z.eqb_spec z i) as [->|Hzi]; [right|left].
      - destruct (Z.eqb_spec i j); [congruence | reflexivity].
      - destruct (Z.eqb_spec z i); [congruence | reflexivity]. }
    lia.
Qed.

(** the amortized item-count bound: at most one item per scanned slot *)
Lemma zho_send_items_len : forall fuel t maxc n prev next count mc mn,
  0 <= count -> 3 <= mn -> n <= maxc + 1 ->
  Z.of_nat (length (send_items fuel t maxc n prev next count mc mn))
  <= (maxc + 1 - n) + count + 1.
Proof.
  induction fuel as [|f IH]; intros t maxc n prev next count mc mn Hc Hmn Hn.
  - cbn [send_items length]. cbn [Z.of_nat]. lia.
  - cbn [send_items]. cbv zeta.
    destruct (Z.ltb_spec maxc n) as [Hlt|Hge].
    + cbn [length]. cbn [Z.of_nat]. lia.
    + destruct ((count + 1 <? mc) && (next =? t_len t (n + 1)))%bool eqn:Erun.
      * (* the run continues *)
        pose proof (IH t maxc (n + 1) prev (t_len t (n + 1)) (count + 1)
                      mc mn ltac:(lia) Hmn ltac:(lia)).
        lia.
      * (* a flush, then the tail *)
        rewrite length_app, Nat2Z.inj_add.
        set (mc' := if Z.eqb (t_len t (n + 1)) 0 then 138
                    else if Z.eqb next (t_len t (n + 1)) then 6 else 7) in *.
        set (mn' := if Z.eqb (t_len t (n + 1)) 0 then 3
                    else if Z.eqb next (t_len t (n + 1)) then 3 else 4) in *.
        assert (Hmn' : 3 <= mn').
        { unfold mn'.
          destruct (Z.eqb (t_len t (n + 1)) 0); [lia|].
          destruct (Z.eqb next (t_len t (n + 1))); lia. }
        pose proof (IH t maxc (n + 1) next (t_len t (n + 1)) 0
                      mc' mn' ltac:(lia) Hmn' ltac:(lia)) as Hrec.
        assert (Hit : Z.of_nat (length
                 (if count + 1 <? mn then
                    repeat (CLit (Z.to_nat next)) (Z.to_nat (count + 1))
                  else if negb (next =? 0) then
                    (if negb (next =? prev)
                     then [CLit (Z.to_nat next);
                           CRep (Z.to_nat next) (Z.to_nat (count + 1 - 1))]
                     else [CRep (Z.to_nat next) (Z.to_nat (count + 1))])
                  else if count + 1 <=? 10 then [CZ3 (Z.to_nat (count + 1))]
                  else [CZ11 (Z.to_nat (count + 1))]))
                <= count + 1).
        { destruct (Z.ltb_spec (count + 1) mn) as [Hsh|Hlong].
          - rewrite repeat_length. lia.
          - destruct (negb (next =? 0)).
            + destruct (negb (next =? prev)); cbn [length]; lia.
            + destruct (count + 1 <=? 10); cbn [length]; lia. }
        lia.
Qed.

Lemma zho_wsum_scale : forall (c : Z) (f : Z -> Z) lo n,
  wsum (fun i => c * f i) lo n = c * wsum f lo n.
Proof.
  intros c f lo n; revert lo; induction n as [|k IH]; intro lo;
    cbn [wsum]; [lia|].
  cbv beta. rewrite IH. lia.
Qed.

(** extra_blbits is at most 7 (the landed range says 16; sharpen) *)
Definition zho_eblb_at (c : Z) : bool :=
  (0 <=? extra_blbits c) && (extra_blbits c <=? 7).

Lemma zho_eblb_all : forallb zho_eblb_at (zseq 19 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma zho_extra_blbits_le7 : forall c, 0 <= c < 19 ->
  0 <= extra_blbits c <= 7.
Proof.
  intros c Hc.
  pose proof (forallb_zseq' zho_eblb_at 19 19 c
                ltac:(vm_compute; reflexivity) zho_eblb_all Hc) as H.
  unfold zho_eblb_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(** the generic per-tree description bound: nothing about T is needed *)
Lemma zho_bldesc_bound : forall (T : Tree) (maxc : Z) (blt : Tree),
  (forall sy, 0 <= sy < 19 -> 0 <= t_len blt sy <= 7) ->
  -1 <= maxc ->
  wsum (fun sy => hid_zcount sy (items_syms (send_tree_items T maxc))
                  * (t_len blt sy + extra_blbits sy)) 0 19
  <= 14 * (maxc + 2).
Proof.
  intros T maxc blt Hbl Hmc.
  eapply Z.le_trans.
  { apply (zho_wsum_le_pt
             (fun sy => hid_zcount sy (items_syms (send_tree_items T maxc))
                        * (t_len blt sy + extra_blbits sy))
             (fun sy => 14 * hid_zcount sy
                          (items_syms (send_tree_items T maxc)))
             0 19).
    intros sy Hsy.
    change (Z.of_nat 19) with 19 in Hsy.
    pose proof (hid_nonneg sy (items_syms (send_tree_items T maxc))).
    pose proof (Hbl sy ltac:(lia)).
    pose proof (zho_extra_blbits_le7 sy ltac:(lia)).
    nia. }
  rewrite zho_wsum_scale.
  eapply Z.le_trans.
  { apply Z.mul_le_mono_nonneg_l; [lia|].
    apply zho_hid_sum_le. }
  rewrite zho_items_syms_len.
  unfold send_tree_items.
  destruct (Z.eqb (t_len T 0) 0).
  - eapply Z.le_trans;
      [apply Z.mul_le_mono_nonneg_l;
        [lia | apply zho_send_items_len; lia] | lia].
  - eapply Z.le_trans;
      [apply Z.mul_le_mono_nonneg_l;
        [lia | apply zho_send_items_len; lia] | lia].
Qed.

Lemma zho_bl_cap : forall ts toks,
  ts_optlen ts = 0 -> ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts -> cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  (14 + 3 * (S2M ts + 1)) + zho_bldesc ts TK_L + zho_bldesc ts TK_D
  <= 4551.
Proof.
  intros ts toks Hol Hsl Hbl HFI Henc Hlen HblZ HnnL HnnD.
  destruct (dispatch_counters ts toks Hol Hsl Hbl HFI Henc Hlen HblZ HnnL HnnD)
    as (OL & SL & _ & _ & _ & _ & Hmbi & HmcL & HmcD285 & _).
  unfold zho_bldesc, S2P, S2M in *.
  set (BL' := build_tree TK_L ts) in *.
  set (BD' := build_tree TK_D BL') in *.
  (* blcount hygiene down the pipeline *)
  assert (HelL : 3 <= sd_elems TK_L <= 286)
    by (change (sd_elems TK_L) with 286; lia).
  assert (HML : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  assert (HKL : 4 * (sd_elems TK_L - 1) < 2 ^ sd_max_length TK_L)
    by (change (sd_elems TK_L) with 286;
        change (sd_max_length TK_L) with 15; lia).
  destruct (build_tree_shape TK_L ts HelL HML HKL Hbl) as (_ & _ & HblBL & _).
  assert (HelD : 3 <= sd_elems TK_D <= 286)
    by (change (sd_elems TK_D) with 30; lia).
  assert (HMD : 1 <= sd_max_length TK_D <= 15)
    by (change (sd_max_length TK_D) with 15; lia).
  assert (HKD : 4 * (sd_elems TK_D - 1) < 2 ^ sd_max_length TK_D)
    by (change (sd_elems TK_D) with 30;
        change (sd_max_length TK_D) with 15; lia).
  destruct (build_tree_shape TK_D BL' HelD HMD HKD HblBL)
    as (HmcD30 & _ & HblBD & _).
  fold BD' in HmcD30, HblBD.
  (* the build_bl_tree pipeline, destructured *)
  set (tL := ts_trees BD' TK_L) in *.
  set (mcL := ts_maxcode BD' TK_L) in *.
  set (bl0 := ts_trees BD' TK_BL) in *.
  set (p1 := scan_tree tL mcL bl0) in *.
  set (s1' := set_tree TK_BL (snd p1) (set_tree TK_L (fst p1) BD')) in *.
  set (tD := ts_trees s1' TK_D) in *.
  set (mcD := ts_maxcode s1' TK_D) in *.
  set (bl1 := ts_trees s1' TK_BL) in *.
  set (p2 := scan_tree tD mcD bl1) in *.
  set (s2' := set_tree TK_BL (snd p2) (set_tree TK_D (fst p2) s1')) in *.
  set (s3 := build_tree TK_BL s2') in *.
  set (mbi := bbl_scan (Z.to_nat BL_CODES + 1) (ts_trees s3 TK_BL)
                (BL_CODES - 1)) in *.
  assert (EP : build_bl_tree BD'
               = (mbi, set_optlen
                         (u64 (ts_optlen s3 + 3 * (mbi + 1) + 5 + 5 + 4))
                         s3)).
  { unfold build_bl_tree. cbv zeta. reflexivity. }
  (* the BL build's shape: lens in [0,7] *)
  assert (Hbls2 : forall b, b < 0 \/ 15 < b -> ts_blcount s2' b = 0).
  { intros b Hb. unfold s2', s1'.
    rewrite !g6_bc_settree. apply HblBD. exact Hb. }
  assert (HelB : 3 <= sd_elems TK_BL <= 286)
    by (change (sd_elems TK_BL) with 19; lia).
  assert (HMB : 1 <= sd_max_length TK_BL <= 15)
    by (change (sd_max_length TK_BL) with 7; lia).
  assert (HKB : 4 * (sd_elems TK_BL - 1) < 2 ^ sd_max_length TK_BL)
    by (change (sd_elems TK_BL) with 19;
        change (sd_max_length TK_BL) with 7; lia).
  destruct (build_tree_shape TK_BL s2' HelB HMB HKB Hbls2)
    as (_ & HlenBL7 & _ & _).
  fold s3 in HlenBL7.
  change (sd_elems TK_BL) with 19 in HlenBL7.
  change (sd_max_length TK_BL) with 7 in HlenBL7.
  (* frames onto the dispatch-state projections *)
  rewrite EP. cbn [fst snd].
  rewrite !g6_tr_setoptlen, !g6_mc_setoptlen.
  assert (EblT : ts_trees s3 TK_BL = ts_trees s3 TK_BL) by reflexivity.
  assert (EmcD : ts_maxcode s3 TK_D = ts_maxcode BD' TK_D).
  { unfold s3.
    rewrite (build_tree_maxcode_other TK_BL s2' TK_D)
      by (intro E; discriminate E).
    unfold s2', s1'. rewrite !g6_mc_settree. reflexivity. }
  rewrite EmcD.
  (* the two description bounds *)
  pose proof (zho_bldesc_bound (ts_trees s3 TK_L) (ts_maxcode s3 TK_L)
                (ts_trees s3 TK_BL) HlenBL7) as HB_L.
  pose proof (zho_bldesc_bound (ts_trees s3 TK_D) (ts_maxcode BD' TK_D)
                (ts_trees s3 TK_BL) HlenBL7) as HB_D.
  (* maxcode ranges: L from dispatch (frame its spelling), D sharp *)
  assert (HmcLs3 : 0 <= ts_maxcode s3 TK_L <= 285).
  { revert HmcL. fold BL' BD'. rewrite EP. cbn [snd].
    rewrite g6_mc_setoptlen. exact (fun H => H). }
  change (sd_elems TK_D) with 30 in HmcD30.
  eapply Z.le_trans.
  { apply Z.add_le_mono.
    - apply Z.add_le_mono.
      + (* header *) 
        assert (Hmbi' : 2 <= mbi <= 18).
        { revert Hmbi. fold BL' BD'. rewrite EP. cbn [fst].
          exact (fun H => H). }
        instantiate (1 := 14 + 3 * (18 + 1)). lia.
      + apply (Z.le_trans _ (14 * (ts_maxcode s3 TK_L + 2))).
        * apply HB_L. lia.
        * instantiate (1 := 14 * 287). lia.
    - apply (Z.le_trans _ (14 * (ts_maxcode BD' TK_D + 2))).
      + apply HB_D. lia.
      + instantiate (1 := 14 * 31). lia. }
  lia.
Qed.

(** ** The D-tree degenerate corner: at most one live distance code.
    The built tree then assigns the (possibly forced) live code length 1,
    so the distance data cost is at most the match count. *)

(** the corner, with the blcount-hygiene premise the pipeline machinery
    needs (see the defect note at [zho_d_corner] below) *)
Lemma zho_d_corner' : forall ts toks,
  FreqInv toks ts -> cEnc toks ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  (forall i j, 0 <= i < 30 -> 0 <= j < 30 -> i <> j ->
     t_freq (ts_trees ts TK_D) i = 0 \/ t_freq (ts_trees ts TK_D) j = 0) ->
  forall dynD,
  dynD = ts_trees (build_tree TK_D (build_tree TK_L ts)) TK_D ->
  wsum (fun n => t_freq (ts_trees ts TK_D) n * t_len dynD n)
       0 (Z.to_nat (sd_elems TK_D))
  <= wsum (fun n => t_freq (ts_trees ts TK_D) n) 0 (Z.to_nat (sd_elems TK_D)).
Proof.
  intros ts toks HFI Henc Hbl0ts Hlnn Hone dynD Edyn.
  set (BL' := build_tree TK_L ts) in *.
  set (f := t_freq (ts_trees ts TK_D)) in *.
  assert (NEQ_D_L : TK_D <> TK_L) by (intro E; discriminate E).
  assert (EtD : ts_trees BL' TK_D = ts_trees ts TK_D)
    by (unfold BL'; apply build_tree_tree_other; exact NEQ_D_L).
  assert (HelL : 3 <= sd_elems TK_L <= 286)
    by (change (sd_elems TK_L) with 286; lia).
  assert (HML : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  assert (HKL : 4 * (sd_elems TK_L - 1) < 2 ^ sd_max_length TK_L)
    by (change (sd_elems TK_L) with 286;
        change (sd_max_length TK_L) with 15; lia).
  destruct (build_tree_shape TK_L ts HelL HML HKL Hbl0ts)
    as (_ & _ & HblBL & _).
  destruct HFI as [_ HFD].
  assert (Hfnn : forall n, 0 <= n < 30 -> 0 <= f n).
  { intros n Hn. unfold f. rewrite (HFD n) by (unfold D_CODES; lia).
    apply count_D_nonneg. }
  assert (HelD : 3 <= sd_elems TK_D <= 286)
    by (change (sd_elems TK_D) with 30; lia).
  assert (HMD : 1 <= sd_max_length TK_D <= 15)
    by (change (sd_max_length TK_D) with 15; lia).
  (* any live? *)
  destruct (existsb (fun n => negb (f n =? 0)) (map Z.of_nat (seq 0 30)))
    eqn:Elive.
  2:{ (* all dead: both sums vanish pointwise *)
      assert (Hdead : forall n, 0 <= n < 30 -> f n = 0).
      { intros n Hn.
        destruct (Z.eqb_spec (f n) 0) as [E|Hnz]; [exact E|].
        exfalso.
        assert (Htrue : existsb (fun m => negb (f m =? 0))
                          (map Z.of_nat (seq 0 30)) = true).
        { apply existsb_exists. exists n. split.
          - apply in_map_iff. exists (Z.to_nat n).
            split; [lia|]. apply in_seq. lia.
          - apply negb_true_iff. apply Z.eqb_neq. exact Hnz. }
        congruence. }
      apply zho_wsum_le_pt.
      intros i Hi.
      change (Z.to_nat (sd_elems TK_D)) with 30%nat in Hi.
      rewrite Hdead by lia. lia. }
  (* a live distance code exists *)
  apply existsb_exists in Elive.
  destruct Elive as (i0 & Hin0 & Hnz0).
  apply in_map_iff in Hin0. destruct Hin0 as (m0 & Em0 & Hm0).
  apply in_seq in Hm0.
  apply negb_true_iff in Hnz0. apply Z.eqb_neq in Hnz0.
  assert (Hi0 : 0 <= i0 < 30) by lia.
  clear Em0 Hm0 m0.
  (* the D-build pipeline *)
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_D)
              (ts_trees BL' TK_D) (ts_heap BL') (ts_depth BL') 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_init_census_call (Z.to_nat L_CODES + 2) (sd_elems TK_D)
              (ts_trees BL' TK_D) (ts_heap BL') (ts_depth BL')
              t0 hp0 dep0 hlen0 maxc0 E0
              ltac:(change (Z.of_nat (Z.to_nat L_CODES + 2)) with 288; lia)
              ltac:(lia)) as [Hout0 Hfr0].
  assert (Efr0 : forall x, t_freq t0 x = f x)
    by (intro x; rewrite (Hfr0 x), EtD; reflexivity).
  assert (Hmc30 : -1 <= maxc0 < 30)
    by (pose proof (io_maxc _ _ _ _ _ Hout0) as Hm;
        change (sd_elems TK_D) with 30 in Hm; exact Hm).
  (* exactly one live: hlen0 = 1 *)
  assert (Hh01 : hlen0 = 1).
  { rewrite (io_total _ _ _ _ _ Hout0).
    unfold live_total.
    change (Z.to_nat (sd_elems TK_D)) with 30%nat.
    assert (Hle : wsum (fun s' => ind (live_b t0 maxc0 s')) 0 30 <= 1).
    { apply zho_ind_sum_le1.
      intros i j Hi Hj Hne.
      change (Z.of_nat 30) with 30 in Hi, Hj.
      destruct (Hone i j ltac:(lia) ltac:(lia) Hne) as [Hz|Hz];
        [left|right]; apply live_b_false_dead; rewrite Efr0; exact Hz. }
    assert (Hge : 1 <= wsum (fun s' => ind (live_b t0 maxc0 s')) 0 30).
    { apply (zho_ind_member_ge1 _ 0 30 i0);
        [change (Z.of_nat 30) with 30; lia|].
      apply live_b_true; [|rewrite Efr0; exact Hnz0].
      split; [lia|].
      destruct (Z.le_gt_cases i0 maxc0) as [|Hgt]; [assumption|].
      exfalso. apply Hnz0. rewrite <- Efr0.
      apply (io_gapz _ _ _ _ _ Hout0).
      change (sd_elems TK_D) with 30. lia. }
    lia. }
  subst hlen0.
  (* force2 *)
  destruct (bt_force2 3%nat (sd_stree TK_D) t0 hp0 dep0 1 maxc0
              (ts_optlen BL') (ts_statlen BL'))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  destruct (zho_force2_one (sd_stree TK_D) t0 hp0 dep0 maxc0
              (ts_optlen BL') (ts_statlen BL')
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 E2)
    as (nd & End & Et1 & Emc1 & Eol1 & Esl1).
  pose proof (bt_sized TK_D BL' t0 hp0 dep0 1 maxc0
                t1 hp1 dep1 hlen1 maxc1 ol1 sl1
                ltac:(change (sd_elems TK_D) with 30; lia)
                ltac:(change (sd_elems TK_D) with 30; unfold L_CODES; lia)
                E0 E2) as Hsz.
  assert (HK1 : 4 * (hlen1 - 1) < 2 ^ sd_max_length TK_D)
    by (change (sd_max_length TK_D) with 15;
        unfold L_CODES in Hsz; lia).
  (* the loop terminates *)
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems TK_D |}) as [stf|] eqn:Eloop.
  2:{ exfalso. revert Eloop. apply bt_loop_terminates.
      - cbn [b_hlen]. lia.
      - cbn [b_hlen].
        change (Z.of_nat (Z.to_nat HEAP_SIZE)) with 573.
        unfold L_CODES in Hsz. lia. }
  (* the unique live symbol is the heap's single entry *)
  set (w := hp0 1) in *.
  assert (Hlbw : live_b t0 maxc0 w = true).
  { pose proof (io_spec _ _ _ _ _ Hout0 w) as Hsp.
    unfold lcount, wcount in Hsp.
    change (Z.to_nat 1) with 1%nat in Hsp.
    cbn [wsum] in Hsp. cbv beta in Hsp.
    fold w in Hsp.
    rewrite Z.eqb_refl in Hsp. cbn [ind] in Hsp.
    destruct (live_b t0 maxc0 w); [reflexivity | cbn [ind] in Hsp; lia]. }
  assert (Hwr : 0 <= w <= maxc0 /\ f w <> 0).
  { unfold live_b in Hlbw.
    apply andb_true_iff in Hlbw. destruct Hlbw as [Hr Hnzb].
    apply andb_true_iff in Hr. destruct Hr as [H0w Hwm].
    apply Z.leb_le in H0w. apply Z.leb_le in Hwm.
    apply negb_true_iff in Hnzb. apply Z.eqb_neq in Hnzb.
    rewrite Efr0 in Hnzb. auto. }
  destruct Hwr as [[H0w Hwm0] Hfw].
  assert (Hwmc1 : w <= maxc1).
  { rewrite Emc1. destruct (Z.ltb_spec maxc0 2); lia. }
  (* witnesses for the two-coded-symbols cap *)
  assert (Hw2 : forall x, 0 <= x < sd_elems TK_D ->
                t_freq t1 x <> 0 -> x = w \/ x = nd).
  { intros x Hx Hnz.
    destruct (Z.eqb_spec x nd) as [->|Hne]; [right; reflexivity|].
    left.
    rewrite Et1 in Hnz.
    rewrite g6_t_freq_setfreq_other in Hnz by (intro E; exact (Hne E)).
    rewrite Efr0 in Hnz.
    change (sd_elems TK_D) with 30 in Hx.
    destruct (Z.eqb_spec x w) as [->|Hnew]; [reflexivity|].
    exfalso.
    destruct (Hone x w ltac:(lia) ltac:(lia) Hnew) as [Hz|Hz];
      [exact (Hnz Hz) | exact (Hfw Hz)]. }
  (* the length cap at the live symbol *)
  assert (Hlen1 : t_len (ts_trees (build_tree TK_D BL') TK_D) w <= 1).
  { apply (zho_len_le1 TK_D BL' t0 hp0 dep0 1 maxc0
             t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
             HelD HMD HK1 HblBL E0 E2 Eloop w nd Hw2).
    split; [exact H0w | exact Hwmc1]. }
  (* the pointwise bound *)
  subst dynD.
  apply zho_wsum_le_pt.
  intros i Hi.
  change (Z.to_nat (sd_elems TK_D)) with 30%nat in Hi.
  change (Z.of_nat 30%nat) with 30 in Hi.
  destruct (Z.eqb_spec (f i) 0) as [Ez|Hnz].
  - rewrite Ez. lia.
  - assert (Ei : i = w).
    { destruct (Z.eqb_spec i w) as [->|Hne]; [reflexivity|].
      exfalso.
      destruct (Hone i w ltac:(lia) ltac:(lia) Hne) as [Hz|Hz];
        [exact (Hnz Hz) | exact (Hfw Hz)]. }
    subst i.
    pose proof (Hfnn w ltac:(lia)) as Hnnw.
    fold BL'.
    eapply Z.le_trans; [apply Z.mul_le_mono_nonneg_l; [exact Hnnw | exact Hlen1]|].
    lia.
Qed.

Lemma zho_d_corner : forall ts toks,
  FreqInv toks ts -> cEnc toks ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  (* at most one live distance code *)
  (forall i j, 0 <= i < 30 -> 0 <= j < 30 -> i <> j ->
     t_freq (ts_trees ts TK_D) i = 0 \/ t_freq (ts_trees ts TK_D) j = 0) ->
  forall dynD,
  dynD = ts_trees (build_tree TK_D (build_tree TK_L ts)) TK_D ->
  wsum (fun n => t_freq (ts_trees ts TK_D) n * t_len dynD n)
       0 (Z.to_nat (sd_elems TK_D))
  <= wsum (fun n => t_freq (ts_trees ts TK_D) n) 0 (Z.to_nat (sd_elems TK_D)).
Proof.
  intros ts toks HFI Henc Hbl Hnn Hone dynD EdynD.
  exact (zho_d_corner' ts toks HFI Henc Hbl Hnn Hone dynD EdynD).
Qed.

(** ** The LP certificate: the family's cost fits the budget.
    Stated over token counts; the caller ties counts to freqs (FreqInv)
    and the span to the extents (toks_ext).  Constants: literals 9, EOB 3,
    dominant 2 / others 10 (+ length extras), distances 5 (+ extras
    <= 13), caps 4551 (desc) + 6 (ZHOOl slop) + K_L 8192 + K_D 2048. *)

(** table facts for the certificate, by reflection.
    NOTE: the model's base_length[28] is 0 (zlib's own table quirk for
    code 285, whose true base length is 258); the certificate needs the
    TRUE bases, so we use a patched table. *)
Definition zho_base (k : Z) : Z :=
  if Z.eqb k 28 then 258 else base_length k + 3.

Definition zho_t1_at (m : Z) : bool :=
  zho_base (length_code m) <=? m + 3.
Lemma zho_t1_all : forallb zho_t1_at (zseq 256 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma zho_base_le_len : forall len, 3 <= len <= 258 ->
  zho_base (length_code (len - 3)) <= len.
Proof.
  intros len Hl.
  pose proof (forallb_zseq' zho_t1_at 256 256 (len - 3)
                ltac:(vm_compute; reflexivity) zho_t1_all ltac:(lia)) as H.
  unfold zho_t1_at in H. apply Z.leb_le in H. lia.
Qed.

Definition zho_t2_at (m : Z) : bool :=
  (0 <=? length_code m) && (length_code m <? 29).
Lemma zho_t2_all : forallb zho_t2_at (zseq 256 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma zho_lc_range : forall len, 3 <= len <= 258 ->
  0 <= length_code (len - 3) < 29.
Proof.
  intros len Hl.
  pose proof (forallb_zseq' zho_t2_at 256 256 (len - 3)
                ltac:(vm_compute; reflexivity) zho_t2_all ltac:(lia)) as H.
  unfold zho_t2_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Definition zho_edb13_at (d : Z) : bool := extra_dbits d <=? 13.
Lemma zho_edb13_all : forallb zho_edb13_at (zseq 30 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma zho_extra_dbits_le13 : forall d, 0 <= d < 30 -> extra_dbits d <= 13.
Proof.
  intros d Hd.
  pose proof (forallb_zseq' zho_edb13_at 30 30 d
                ltac:(vm_compute; reflexivity) zho_edb13_all Hd) as H.
  unfold zho_edb13_at in H. apply Z.leb_le in H. lia.
Qed.

(** the summed certificate row (in c-257 coordinates):
    28 + xb <= 6*(base+3) + 3 + 7*[k=0] + [k=1] *)
Definition zho_row_at (k : Z) : bool :=
  28 + extra_lbits k
  <=? 6 * zho_base k + 3
      + (if k =? 0 then 7 else 0) + (if k =? 1 then 1 else 0).
Lemma zho_row_all : forallb zho_row_at (zseq 29 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma zho_row : forall k, 0 <= k < 29 ->
  28 + extra_lbits k
  <= 6 * zho_base k + 3
     + (if k =? 0 then 7 else 0) + (if k =? 1 then 1 else 0).
Proof.
  intros k Hk.
  pose proof (forallb_zseq' zho_row_at 29 29 k
                ltac:(vm_compute; reflexivity) zho_row_all Hk) as H.
  unfold zho_row_at in H. apply Z.leb_le in H. lia.
Qed.

(** the coarse2 summed certificate row, x2-scaled for integer multipliers
    (lambda1 = 11/2 etc.; rows verified numerically, const slack 5051):
    2*(28 + xb) <= 11*base + 7 + 16*[k=0] + 5*[k=1] *)
Definition zho_row2_at (k : Z) : bool :=
  2 * (28 + extra_lbits k)
  <=? 11 * zho_base k + 7
      + (if k =? 0 then 16 else 0) + (if k =? 1 then 5 else 0).
Lemma zho_row2_all : forallb zho_row2_at (zseq 29 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma zho_row2 : forall k, 0 <= k < 29 ->
  2 * (28 + extra_lbits k)
  <= 11 * zho_base k + 7
     + (if k =? 0 then 16 else 0) + (if k =? 1 then 5 else 0).
Proof.
  intros k Hk.
  pose proof (forallb_zseq' zho_row2_at 29 29 k
                ltac:(vm_compute; reflexivity) zho_row2_all Hk) as H.
  unfold zho_row2_at in H. apply Z.leb_le in H. lia.
Qed.

(** the LIVE comparison family (coarse2): dom -> 2, sec -> 3, EOB -> 4,
    literals -> 9, other length codes -> 10 *)
Definition zho_CL2 (t : Tree) (n : Z) : Z :=
  if Z.eqb n (zho_dom t) then 2
  else if Z.eqb n (zho_sec t) then 3
  else if Z.eqb n 256 then 4
  else if Z.ltb n 256 then 9 else 10.

Definition zho_CD2 (n : Z) : Z := 5.

(** ** Assembly support: counting, head tokens, window splits *)

Lemma zho_count256 : forall toks, cEnc toks -> count_L 256 toks = 0.
Proof.
  intros toks He. induction toks as [|t r IH].
  - reflexivity.
  - inversion He as [|? ? Ht Hr]; subst.
    destruct t as [b | len dist]; cbn [count_L].
    + destruct Ht as [Hb0 Hb1].
      replace (Z.eqb b 256) with false
        by (symmetry; apply Z.eqb_neq; lia).
      apply IH; exact Hr.
    + destruct Ht as [Hlen Hdist].
      pose proof (zho_lc_range len
                    ltac:(unfold MIN_MATCH, MAX_MATCH in Hlen; lia)).
      replace (Z.eqb (length_code (len - 3) + LITERALS + 1) 256) with false
        by (symmetry; apply Z.eqb_neq; unfold LITERALS; lia).
      apply IH; exact Hr.
Qed.

Lemma zho_toks_head : forall toks, cEnc toks -> 0 < toks_ext toks ->
  exists s, s <> 256 /\ 0 <= s < 286 /\ 1 <= count_L s toks.
Proof.
  intros toks He Hpos.
  destruct toks as [|t r]; [cbn [toks_ext] in Hpos; lia|].
  inversion He as [|? ? Ht Hr]; subst.
  destruct t as [b | len dist].
  - destruct Ht as [Hb0 Hb1].
    exists b. split; [lia|]. split; [lia|].
    cbn [count_L]. rewrite Z.eqb_refl.
    pose proof (count_L_nonneg b r). lia.
  - destruct Ht as [Hlen Hdist].
    set (c0 := length_code (len - 3) + LITERALS + 1).
    pose proof (zho_lc_range len
                  ltac:(unfold MIN_MATCH, MAX_MATCH in Hlen; lia)) as Hc0.
    exists c0. split; [unfold c0, LITERALS; lia|].
    split; [unfold c0, LITERALS; lia|].
    cbn [count_L]. fold c0. rewrite Z.eqb_refl.
    pose proof (count_L_nonneg c0 r). lia.
Qed.

(** two distinct true positions give an indicator sum of at least 2 *)
Lemma zho_ind_two_ge2 : forall (g : Z -> bool) lo n p q,
  lo <= p < lo + Z.of_nat n -> lo <= q < lo + Z.of_nat n -> p <> q ->
  g p = true -> g q = true ->
  2 <= wsum (fun i => ind (g i)) lo n.
Proof.
  intros g lo n; revert lo; induction n as [|k IH]; intros lo p q Hp Hq Hne Hgp Hgq.
  - cbn [Z.of_nat] in Hp. lia.
  - rewrite Nat2Z.inj_succ in Hp, Hq. cbn [wsum]. cbv beta.
    assert (Hnn : 0 <= wsum (fun i => ind (g i)) (lo + 1) k).
    { apply wsum_nonneg. intros i _. destruct (g i); cbn [ind]; lia. }
    destruct (Z.eq_dec p lo) as [->|Hpl].
    + rewrite Hgp. cbn [ind].
      pose proof (zho_ind_member_ge1 g (lo + 1) k q ltac:(lia) Hgq). lia.
    + destruct (Z.eq_dec q lo) as [->|Hql].
      * rewrite Hgq. cbn [ind].
        pose proof (zho_ind_member_ge1 g (lo + 1) k p ltac:(lia) Hgp). lia.
      * pose proof (IH (lo + 1) p q ltac:(lia) ltac:(lia) Hne Hgp Hgq).
        destruct (g lo); cbn [ind]; lia.
Qed.

(** an indicator sum of at least 2 yields two distinct true positions *)
Lemma zho_ind_two_inv : forall (g : Z -> bool) lo n,
  2 <= wsum (fun i => ind (g i)) lo n ->
  exists p q, lo <= p < lo + Z.of_nat n /\ lo <= q < lo + Z.of_nat n
              /\ p <> q /\ g p = true /\ g q = true.
Proof.
  intros g lo n; revert lo; induction n as [|k IH]; intros lo H2.
  - cbn [wsum] in H2. lia.
  - cbn [wsum] in H2. cbv beta in H2.
    rewrite Nat2Z.inj_succ.
    destruct (g lo) eqn:Eg.
    + cbn [ind] in H2.
      destruct (Z.le_gt_cases 2 (wsum (fun i => ind (g i)) (lo + 1) k))
        as [Hge2|Hlt2].
      * destruct (IH (lo + 1) Hge2) as (p & q & Hp & Hq & Hne & Hgp & Hgq).
        exists p, q. repeat split; try lia; assumption.
      * (* the tail holds at least one *)
        assert (H1 : 1 <= wsum (fun i => ind (g i)) (lo + 1) k) by lia.
        assert (Hex : exists p, lo + 1 <= p < lo + 1 + Z.of_nat k
                                /\ g p = true).
        { clear -H1. revert H1. generalize (lo + 1). clear lo.
          induction k as [|k IHk]; intros lo H1.
          - cbn [wsum] in H1. lia.
          - cbn [wsum] in H1. cbv beta in H1.
            rewrite Nat2Z.inj_succ.
            destruct (g lo) eqn:Eg.
            + exists lo. split; [lia | exact Eg].
            + cbn [ind] in H1.
              destruct (IHk (lo + 1) ltac:(lia)) as (p & Hp & Hgp).
              exists p. split; [lia | exact Hgp]. }
        destruct Hex as (p & Hp & Hgp).
        exists lo, p. repeat split; try lia; assumption.
    + cbn [ind] in H2.
      destruct (IH (lo + 1) ltac:(lia)) as (p & q & Hp & Hq & Hne & Hgp & Hgq).
      exists p, q. repeat split; try lia; assumption.
Qed.

(** a masked sum ignores a [t_setlen] at a dead or out-of-window index *)
Lemma zho_wsum_setlen_dead : forall (fr : Z -> Z) (t : Tree) (g v : Z) lo n,
  (lo <= g < lo + Z.of_nat n -> fr g = 0) ->
  wsum (fun i => fr i * t_len (t_setlen t g v) i) lo n
  = wsum (fun i => fr i * t_len t i) lo n.
Proof.
  intros fr t g v lo n Hdead.
  apply wsum_ext. intros i Hi.
  destruct (Z.eq_dec i g) as [->|Hne].
  - rewrite (Hdead Hi). ring.
  - unfold t_len, t_setlen. cbn [tr_dl].
    rewrite zset_other by exact Hne. reflexivity.
Qed.

(** span: literal count plus base-weighted match counts is at most the
    token extent *)
Lemma zho_span : forall toks, cEnc toks ->
  wsum (fun c => count_L c toks) 0 256
  + wsum (fun c => count_L c toks * zho_base (c - 257)) 257 29
  <= toks_ext toks.
Proof.
  intros toks He.
  induction toks as [|t r IH].
  - cbn [toks_ext].
    rewrite (g6_wsum_zero (fun c => count_L c []) 0 256)
      by (intros; reflexivity).
    rewrite (g6_wsum_zero (fun c => count_L c [] * zho_base (c - 257))
               257 29) by (intros; reflexivity).
    lia.
  - inversion He as [|? ? Ht Hr]; subst.
    specialize (IH Hr).
    destruct t as [b | len dist]; cbn [toks_ext tok_ext].
    + (* literal *)
      destruct Ht as [Hb0 Hb1].
      rewrite (wsum_ext (fun c => count_L c (TLit b :: r))
                 (fun c => (if Z.eqb b c then 1 else 0) * 1 + count_L c r)
                 0 256)
        by (intros p _; cbn [count_L]; ring).
      rewrite (wsum_ext (fun c => count_L c (TLit b :: r)
                                  * zho_base (c - 257))
                 (fun c => count_L c r * zho_base (c - 257))
                 257 29)
        by (intros p Hp; cbn [count_L];
            replace (Z.eqb b p) with false
              by (symmetry; apply Z.eqb_neq; lia);
            ring).
      rewrite wsum_plus.
      rewrite (wsum_delta (fun _ => 1) b 0 256)
        by (change (Z.of_nat 256) with 256; lia).
      lia.
    + (* match *)
      destruct Ht as [Hlen Hdist].
      set (c0 := length_code (len - 3) + LITERALS + 1) in *.
      assert (Hc0 : 257 <= c0 < 286).
      { unfold c0, LITERALS.
        pose proof (zho_lc_range len ltac:(unfold MIN_MATCH, MAX_MATCH in Hlen; lia)).
        lia. }
      rewrite (wsum_ext (fun c => count_L c (TMatch len dist :: r))
                 (fun c => count_L c r) 0 256)
        by (intros p Hp; cbn [count_L]; fold c0;
            replace (Z.eqb c0 p) with false
              by (symmetry; apply Z.eqb_neq;
                  change (Z.of_nat 256) with 256 in Hp; lia);
            ring).
      rewrite (wsum_ext (fun c => count_L c (TMatch len dist :: r)
                                  * zho_base (c - 257))
                 (fun c => (if Z.eqb c0 c then 1 else 0)
                             * zho_base (c - 257)
                           + count_L c r * zho_base (c - 257))
                 257 29)
        by (intros p _; cbn [count_L]; fold c0; ring).
      rewrite wsum_plus.
      rewrite (wsum_delta (fun c => zho_base (c - 257)) c0 257 29)
        by (change (Z.of_nat 29) with 29; lia).
      assert (Hb3 : zho_base (c0 - 257) <= len).
      { unfold c0, LITERALS.
        replace (length_code (len - 3) + 256 + 1 - 257)
          with (length_code (len - 3)) by ring.
        apply zho_base_le_len.
        unfold MIN_MATCH, MAX_MATCH in Hlen. lia. }
      lia.
Qed.

(** literal + match counts equal the token count *)
Lemma zho_lm_tot : forall toks, cEnc toks ->
  wsum (fun c => count_L c toks) 0 256
  + wsum (fun c => count_L c toks) 257 29
  = Z.of_nat (length toks).
Proof.
  intros toks He.
  induction toks as [|t r IH].
  - rewrite (g6_wsum_zero (fun c => count_L c []) 0 256)
      by (intros; reflexivity).
    rewrite (g6_wsum_zero (fun c => count_L c []) 257 29)
      by (intros; reflexivity).
    reflexivity.
  - inversion He as [|? ? Ht Hr]; subst.
    specialize (IH Hr).
    cbn [length]. rewrite Nat2Z.inj_succ.
    destruct t as [b | len dist].
    + destruct Ht as [Hb0 Hb1].
      rewrite (wsum_ext (fun c => count_L c (TLit b :: r))
                 (fun c => (if Z.eqb b c then 1 else 0) * 1 + count_L c r)
                 0 256)
        by (intros p _; cbn [count_L]; ring).
      rewrite (wsum_ext (fun c => count_L c (TLit b :: r))
                 (fun c => count_L c r) 257 29)
        by (intros p Hp; cbn [count_L];
            replace (Z.eqb b p) with false
              by (symmetry; apply Z.eqb_neq; lia);
            ring).
      rewrite wsum_plus.
      rewrite (wsum_delta (fun _ => 1) b 0 256)
        by (change (Z.of_nat 256) with 256; lia).
      lia.
    + destruct Ht as [Hlen Hdist].
      set (c0 := length_code (len - 3) + LITERALS + 1) in *.
      assert (Hc0 : 257 <= c0 < 286).
      { unfold c0, LITERALS.
        pose proof (zho_lc_range len ltac:(unfold MIN_MATCH, MAX_MATCH in Hlen; lia)).
        lia. }
      rewrite (wsum_ext (fun c => count_L c (TMatch len dist :: r))
                 (fun c => count_L c r) 0 256)
        by (intros p Hp; cbn [count_L]; fold c0;
            replace (Z.eqb c0 p) with false
              by (symmetry; apply Z.eqb_neq;
                  change (Z.of_nat 256) with 256 in Hp; lia);
            ring).
      rewrite (wsum_ext (fun c => count_L c (TMatch len dist :: r))
                 (fun c => (if Z.eqb c0 c then 1 else 0) * 1 + count_L c r)
                 257 29)
        by (intros p _; cbn [count_L]; fold c0; ring).
      rewrite wsum_plus.
      rewrite (wsum_delta (fun _ => 1) c0 257 29)
        by (change (Z.of_nat 29) with 29; lia).
      lia.
Qed.

(** the distance-count total is at most the match count *)
Lemma zho_countD_le : forall toks, cEnc toks ->
  wsum (fun d => count_D d toks) 0 30
  <= wsum (fun c => count_L c toks) 257 29.
Proof.
  intros toks He.
  induction toks as [|t r IH].
  - rewrite (g6_wsum_zero (fun d => count_D d []) 0 30)
      by (intros; reflexivity).
    rewrite (g6_wsum_zero (fun c => count_L c []) 257 29)
      by (intros; reflexivity).
    lia.
  - inversion He as [|? ? Ht Hr]; subst.
    specialize (IH Hr).
    destruct t as [b | len dist].
    + rewrite (wsum_ext (fun d => count_D d (TLit b :: r))
                 (fun d => count_D d r) 0 30)
        by (intros p _; reflexivity).
      rewrite (wsum_ext (fun c => count_L c (TLit b :: r))
                 (fun c => count_L c r) 257 29)
        by (intros p Hp; cbn [count_L];
            destruct Ht as [Hb0 Hb1];
            replace (Z.eqb b p) with false
              by (symmetry; apply Z.eqb_neq; lia);
            ring).
      lia.
    + destruct Ht as [Hlen Hdist].
      set (c0 := length_code (len - 3) + LITERALS + 1) in *.
      assert (Hc0 : 257 <= c0 < 286).
      { unfold c0, LITERALS.
        pose proof (zho_lc_range len ltac:(unfold MIN_MATCH, MAX_MATCH in Hlen; lia)).
        lia. }
      rewrite (wsum_ext (fun d => count_D d (TMatch len dist :: r))
                 (fun d => ind (Z.eqb (d_code (dist - 1)) d) + count_D d r)
                 0 30)
        by (intros p _; cbn [count_D];
            destruct (Z.eqb (d_code (dist - 1)) p); cbn [ind]; ring).
      rewrite (wsum_ext (fun c => count_L c (TMatch len dist :: r))
                 (fun c => (if Z.eqb c0 c then 1 else 0) * 1 + count_L c r)
                 257 29)
        by (intros p _; cbn [count_L]; fold c0; ring).
      rewrite !wsum_plus.
      rewrite (wsum_delta (fun _ => 1) c0 257 29)
        by (change (Z.of_nat 29) with 29; lia).
      assert (Hle1 : wsum (fun d => ind (Z.eqb (d_code (dist - 1)) d)) 0 30
                     <= 1).
      { apply zho_ind_sum_le1.
        intros i j _ _ Hne.
        destruct (Z.eqb_spec (d_code (dist - 1)) i) as [->|Hzi]; [right|left].
        - destruct (Z.eqb_spec i j); [congruence | reflexivity].
        - destruct (Z.eqb_spec (d_code (dist - 1)) i);
            [congruence | reflexivity]. }
      lia.
Qed.

(** SUPERSEDED (retained history): the coarse-1 certificate.  l1-adversary
    found the coarse family's binding case at the {3,4} dominance-boundary
    kink (margin only +1,086); the live certificate is the coarse2 form
    below (dom->2, sec->3, EOB->4, K_L=12288). *)
Lemma zho_cert_coarse1 : forall toks slen (dom : Z),
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  toks_ext toks = slen ->
  32506 < slen ->
  257 <= dom <= 285 ->
  (forall c, 257 <= c <= 285 -> count_L c toks <= count_L dom toks) ->
  9 * wsum (fun c => count_L c toks) 0 256
  + 3
  + wsum (fun c => count_L c toks
                   * ((if Z.eqb c dom then 2 else 10) + extra_lbits (c - 257)))
         257 29
  + wsum (fun d => count_D d toks * (5 + extra_dbits d)) 0 30
  + 4551 + 6 + 8192 + 2048   (* K_L + K_D: the SPLIT form — uniform 2*8192
     FAILS the certificate LP at L=9216, cnt257=5376, cnt258=1791 (margin
     -1471); the split passes at +4673 (certlp.py) *)
  <= 8 * slen + 21.
Proof.
  intros toks slen dom Henc Hlen Hext Hslen Hdom Hdomax.
  set (L := wsum (fun c => count_L c toks) 0 256) in *.
  set (M := wsum (fun c => count_L c toks) 257 29) in *.
  set (XB := wsum (fun c => count_L c toks * extra_lbits (c - 257)) 257 29)
    in *.
  set (BB := wsum (fun c => count_L c toks * zho_base (c - 257)) 257 29)
    in *.
  assert (HLnn : 0 <= L)
    by (apply wsum_nonneg; intros; apply count_L_nonneg).
  assert (HMnn : 0 <= M)
    by (apply wsum_nonneg; intros; apply count_L_nonneg).
  (* R1: the family cost as an equation *)
  assert (R1 : wsum (fun c => count_L c toks
                              * ((if Z.eqb c dom then 2 else 10)
                                 + extra_lbits (c - 257))) 257 29
               = 10 * M + XB - 8 * count_L dom toks).
  { rewrite (wsum_ext
               (fun c => count_L c toks
                         * ((if Z.eqb c dom then 2 else 10)
                            + extra_lbits (c - 257)))
               (fun c => (10 * count_L c toks
                          + count_L c toks * extra_lbits (c - 257))
                         + (if Z.eqb dom c then 1 else 0)
                           * (- 8 * count_L c toks))
               257 29).
    2:{ intros p _.
        destruct (Z.eqb_spec p dom) as [E1|Hne];
          destruct (Z.eqb_spec dom p) as [E2|Hne2].
        - subst dom. ring.
        - exfalso; apply Hne2; symmetry; exact E1.
        - exfalso; apply Hne; symmetry; exact E2.
        - ring. }
    rewrite wsum_plus.
    rewrite (wsum_delta (fun c => - 8 * count_L c toks) dom 257 29)
      by (change (Z.of_nat 29) with 29; lia).
    rewrite wsum_plus.
    rewrite (zho_wsum_scale 10 (fun c => count_L c toks) 257 29).
    fold M XB. lia. }
  (* R2: the summed certificate rows *)
  assert (R2 : wsum (fun c => count_L c toks * (28 + extra_lbits (c - 257)))
                 257 29
               <= 6 * BB + 3 * M + 7 * count_L 257 toks + count_L 258 toks).
  { eapply Z.le_trans.
    { apply (zho_wsum_le_pt
               (fun c => count_L c toks * (28 + extra_lbits (c - 257)))
               (fun c => count_L c toks * (6 * zho_base (c - 257) + 3)
                         + (if Z.eqb 257 c then 1 else 0)
                           * (7 * count_L c toks)
                         + (if Z.eqb 258 c then 1 else 0)
                           * (1 * count_L c toks))
               257 29).
      intros c Hc. change (Z.of_nat 29) with 29 in Hc.
      pose proof (zho_row (c - 257) ltac:(lia)) as HR.
      pose proof (count_L_nonneg c toks) as Hn.
      destruct (Z.eqb_spec 257 c) as [<-|Hne1].
      - replace (257 - 257 =? 0) with true in HR
          by (symmetry; apply Z.eqb_eq; lia).
        replace (257 - 257 =? 1) with false in HR
          by (symmetry; apply Z.eqb_neq; lia).
        destruct (Z.eqb_spec 258 257) as [E|_]; [lia|]. nia.
      - destruct (Z.eqb_spec 258 c) as [<-|Hne2].
        + replace (258 - 257 =? 0) with false in HR
            by (symmetry; apply Z.eqb_neq; lia).
          replace (258 - 257 =? 1) with true in HR
            by (symmetry; apply Z.eqb_eq; lia).
          nia.
        + replace (c - 257 =? 0) with false in HR
            by (symmetry; apply Z.eqb_neq; lia).
          replace (c - 257 =? 1) with false in HR
            by (symmetry; apply Z.eqb_neq; lia).
          nia. }
    rewrite !wsum_plus.
    rewrite (wsum_delta (fun c => 7 * count_L c toks) 257 257 29)
      by (change (Z.of_nat 29) with 29; lia).
    rewrite (wsum_delta (fun c => 1 * count_L c toks) 258 257 29)
      by (change (Z.of_nat 29) with 29; lia).
    rewrite (wsum_ext (fun c => count_L c toks * (6 * zho_base (c - 257) + 3))
               (fun c => 6 * (count_L c toks * zho_base (c - 257))
                         + 3 * count_L c toks)
               257 29) by (intros; ring).
    rewrite wsum_plus.
    rewrite (zho_wsum_scale 6
               (fun c => count_L c toks * zho_base (c - 257)) 257 29).
    rewrite (zho_wsum_scale 3 (fun c => count_L c toks) 257 29).
    fold BB M. lia. }
  (* the distance side *)
  assert (Hdist : wsum (fun d => count_D d toks * (5 + extra_dbits d)) 0 30
                  <= 18 * M).
  { eapply Z.le_trans.
    { apply (zho_wsum_le_pt
               (fun d => count_D d toks * (5 + extra_dbits d))
               (fun d => 18 * count_D d toks) 0 30).
      intros d Hd. change (Z.of_nat 30) with 30 in Hd.
      pose proof (count_D_nonneg d toks).
      pose proof (zho_extra_dbits_le13 d ltac:(lia)).
      pose proof (extra_dbits_range d ltac:(lia)).
      nia. }
    rewrite (zho_wsum_scale 18 (fun d => count_D d toks) 0 30).
    pose proof (zho_countD_le toks Henc) as HDL.
    fold M in HDL. lia. }
  (* span, token totals, dominance *)
  pose proof (zho_span toks Henc) as Hspan.
  fold L BB in Hspan. rewrite Hext in Hspan.
  pose proof (zho_lm_tot toks Henc) as Hlm.
  fold L M in Hlm.
  assert (HLM : L + M <= 16383) by lia.
  pose proof (Hdomax 257 ltac:(lia)) as Hd257.
  pose proof (Hdomax 258 ltac:(lia)) as Hd258.
  (* assemble *)
  rewrite R1.
  assert (HXB : 28 * M + XB
                <= 6 * BB + 3 * M + 7 * count_L 257 toks + count_L 258 toks).
  { eapply Z.le_trans; [|exact R2].
    apply Z.eq_le_incl. symmetry.
    rewrite (wsum_ext (fun c => count_L c toks * (28 + extra_lbits (c - 257)))
               (fun c => 28 * count_L c toks
                         + count_L c toks * extra_lbits (c - 257))
               257 29) by (intros; ring).
    rewrite wsum_plus.
    rewrite (zho_wsum_scale 28 (fun c => count_L c toks) 257 29).
    fold M XB. reflexivity. }
  pose proof (count_L_nonneg 257 toks).
  pose proof (count_L_nonneg 258 toks).
  pose proof (count_L_nonneg dom toks).
  lia.
Qed.

(** ** The LIVE certificate (coarse2): dom -> 2, sec -> 3, EOB -> 4,
    lits 9, rest 10; integer Kraft 8192+4096+2048+16384+864 = 31584
    <= 2^15; constants DESC 4551 + slop 6 + K_L 12288 + K_D 2048.
    Certificate: lambda1=11/2, lambda2=5/2, tau=7/2, nu257=4, sigma257=4,
    sigma258=5/2 (x2-scaled below); const slack 5051; kink-swept LP min
    margin +5157 (CERT-NOTES coarse2 section). *)
Lemma zho_cert : forall toks slen (dom sec : Z),
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  toks_ext toks = slen ->
  32506 < slen ->
  257 <= dom <= 285 ->
  257 <= sec <= 285 ->
  sec <> dom ->
  (forall c, 257 <= c <= 285 -> count_L c toks <= count_L dom toks) ->
  (forall c, 257 <= c <= 285 -> c <> dom ->
     count_L c toks <= count_L sec toks) ->
  9 * wsum (fun c => count_L c toks) 0 256
  + 4
  + wsum (fun c => count_L c toks
                   * ((if Z.eqb c dom then 2
                       else if Z.eqb c sec then 3 else 10)
                      + extra_lbits (c - 257)))
         257 29
  + wsum (fun d => count_D d toks * (5 + extra_dbits d)) 0 30
  + 4551 + 6 + 12288 + 2048
  <= 8 * slen + 21.
Proof.
  intros toks slen dom sec Henc Hlen Hext Hslen Hdom Hsec Hnds Hdomax Hsecmax.
  set (L := wsum (fun c => count_L c toks) 0 256) in *.
  set (M := wsum (fun c => count_L c toks) 257 29) in *.
  set (XB := wsum (fun c => count_L c toks * extra_lbits (c - 257)) 257 29)
    in *.
  set (BB := wsum (fun c => count_L c toks * zho_base (c - 257)) 257 29)
    in *.
  assert (HLnn : 0 <= L)
    by (apply wsum_nonneg; intros; apply count_L_nonneg).
  assert (HMnn : 0 <= M)
    by (apply wsum_nonneg; intros; apply count_L_nonneg).
  (* R1: the coarse2 family cost as an equation *)
  assert (R1 : wsum (fun c => count_L c toks
                              * ((if Z.eqb c dom then 2
                                  else if Z.eqb c sec then 3 else 10)
                                 + extra_lbits (c - 257))) 257 29
               = 10 * M + XB - 8 * count_L dom toks
                 - 7 * count_L sec toks).
  { rewrite (wsum_ext
               (fun c => count_L c toks
                         * ((if Z.eqb c dom then 2
                             else if Z.eqb c sec then 3 else 10)
                            + extra_lbits (c - 257)))
               (fun c => (10 * count_L c toks
                          + count_L c toks * extra_lbits (c - 257))
                         + ((if Z.eqb dom c then 1 else 0)
                              * (- 8 * count_L c toks)
                            + (if Z.eqb sec c then 1 else 0)
                              * (- 7 * count_L c toks)))
               257 29).
    2:{ intros p _.
        destruct (Z.eqb_spec p dom) as [E1|Hne1];
          destruct (Z.eqb_spec dom p) as [E2|Hne2];
          try (exfalso; congruence);
          destruct (Z.eqb_spec p sec) as [E3|Hne3];
          destruct (Z.eqb_spec sec p) as [E4|Hne4];
          try (exfalso; congruence).
        - ring.
        - ring.
        - ring. }
    rewrite (wsum_plus
               (fun c => 10 * count_L c toks
                         + count_L c toks * extra_lbits (c - 257))
               (fun c => (if Z.eqb dom c then 1 else 0)
                           * (- 8 * count_L c toks)
                         + (if Z.eqb sec c then 1 else 0)
                           * (- 7 * count_L c toks))
               257 29).
    rewrite (wsum_plus
               (fun c => (if Z.eqb dom c then 1 else 0)
                         * (- 8 * count_L c toks))
               (fun c => (if Z.eqb sec c then 1 else 0)
                         * (- 7 * count_L c toks))
               257 29).
    rewrite (wsum_delta (fun c => - 8 * count_L c toks) dom 257 29)
      by (change (Z.of_nat 29) with 29; lia).
    rewrite (wsum_delta (fun c => - 7 * count_L c toks) sec 257 29)
      by (change (Z.of_nat 29) with 29; lia).
    rewrite (wsum_plus (fun c => 10 * count_L c toks)
               (fun c => count_L c toks * extra_lbits (c - 257)) 257 29).
    rewrite (zho_wsum_scale 10 (fun c => count_L c toks) 257 29).
    fold M XB. lia. }
  (* the x2-scaled row-sum expansion *)
  assert (Hrow2L : wsum (fun c => count_L c toks
                                  * (56 + 2 * extra_lbits (c - 257))) 257 29
                   = 56 * M + 2 * XB).
  { rewrite (wsum_ext
               (fun c => count_L c toks * (56 + 2 * extra_lbits (c - 257)))
               (fun c => 56 * count_L c toks
                         + 2 * (count_L c toks * extra_lbits (c - 257)))
               257 29) by (intros; ring).
    rewrite (wsum_plus (fun c => 56 * count_L c toks)
               (fun c => 2 * (count_L c toks * extra_lbits (c - 257)))
               257 29).
    rewrite (zho_wsum_scale 56 (fun c => count_L c toks) 257 29).
    rewrite (zho_wsum_scale 2
               (fun c => count_L c toks * extra_lbits (c - 257)) 257 29).
    fold M XB. reflexivity. }
  (* R2: the x2-scaled summed certificate rows *)
  assert (R2 : wsum (fun c => count_L c toks
                              * (56 + 2 * extra_lbits (c - 257))) 257 29
               <= 11 * BB + 7 * M
                  + 16 * count_L 257 toks + 5 * count_L 258 toks).
  { eapply Z.le_trans.
    { apply (zho_wsum_le_pt
               (fun c => count_L c toks * (56 + 2 * extra_lbits (c - 257)))
               (fun c => count_L c toks * (11 * zho_base (c - 257) + 7)
                         + (if Z.eqb 257 c then 1 else 0)
                           * (16 * count_L c toks)
                         + (if Z.eqb 258 c then 1 else 0)
                           * (5 * count_L c toks))
               257 29).
      intros c Hc. change (Z.of_nat 29) with 29 in Hc.
      pose proof (zho_row2 (c - 257) ltac:(lia)) as HR.
      pose proof (count_L_nonneg c toks) as Hn.
      destruct (Z.eqb_spec 257 c) as [<-|Hne1].
      - replace (257 - 257 =? 0) with true in HR
          by (symmetry; apply Z.eqb_eq; lia).
        replace (257 - 257 =? 1) with false in HR
          by (symmetry; apply Z.eqb_neq; lia).
        destruct (Z.eqb_spec 258 257) as [E|_]; [lia|]. nia.
      - destruct (Z.eqb_spec 258 c) as [<-|Hne2].
        + replace (258 - 257 =? 0) with false in HR
            by (symmetry; apply Z.eqb_neq; lia).
          replace (258 - 257 =? 1) with true in HR
            by (symmetry; apply Z.eqb_eq; lia).
          nia.
        + replace (c - 257 =? 0) with false in HR
            by (symmetry; apply Z.eqb_neq; lia).
          replace (c - 257 =? 1) with false in HR
            by (symmetry; apply Z.eqb_neq; lia).
          nia. }
    rewrite !wsum_plus.
    rewrite (wsum_delta (fun c => 16 * count_L c toks) 257 257 29)
      by (change (Z.of_nat 29) with 29; lia).
    rewrite (wsum_delta (fun c => 5 * count_L c toks) 258 257 29)
      by (change (Z.of_nat 29) with 29; lia).
    rewrite (wsum_ext
               (fun c => count_L c toks * (11 * zho_base (c - 257) + 7))
               (fun c => 11 * (count_L c toks * zho_base (c - 257))
                         + 7 * count_L c toks)
               257 29) by (intros; ring).
    rewrite (wsum_plus
               (fun c => 11 * (count_L c toks * zho_base (c - 257)))
               (fun c => 7 * count_L c toks) 257 29).
    rewrite (zho_wsum_scale 11
               (fun c => count_L c toks * zho_base (c - 257)) 257 29).
    rewrite (zho_wsum_scale 7 (fun c => count_L c toks) 257 29).
    fold BB M. lia. }
  (* the scaled dominance payoff: 16 c257 + 5 c258 <= 16 cdom + 14 csec *)
  assert (Hdom2 : 16 * count_L 257 toks + 5 * count_L 258 toks
                  <= 16 * count_L dom toks + 14 * count_L sec toks).
  { pose proof (Hdomax 257 ltac:(lia)) as Hd257.
    pose proof (Hdomax 258 ltac:(lia)) as Hd258.
    pose proof (Hdomax sec Hsec) as Hdsec.
    pose proof (count_L_nonneg 257 toks).
    pose proof (count_L_nonneg 258 toks).
    pose proof (count_L_nonneg sec toks).
    pose proof (count_L_nonneg dom toks).
    destruct (Z.eqb_spec dom 257) as [->|Hnd257].
    - pose proof (Hsecmax 258 ltac:(lia) ltac:(lia)) as Hs258. lia.
    - destruct (Z.eqb_spec dom 258) as [->|Hnd258].
      + pose proof (Hsecmax 257 ltac:(lia) ltac:(lia)) as Hs257. lia.
      + pose proof (Hsecmax 257 ltac:(lia) ltac:(lia)) as Hs257.
        pose proof (Hsecmax 258 ltac:(lia) ltac:(lia)) as Hs258.
        lia. }
  (* the distance side *)
  assert (Hdist : wsum (fun d => count_D d toks * (5 + extra_dbits d)) 0 30
                  <= 18 * M).
  { eapply Z.le_trans.
    { apply (zho_wsum_le_pt
               (fun d => count_D d toks * (5 + extra_dbits d))
               (fun d => 18 * count_D d toks) 0 30).
      intros d Hd. change (Z.of_nat 30) with 30 in Hd.
      pose proof (count_D_nonneg d toks).
      pose proof (zho_extra_dbits_le13 d ltac:(lia)).
      pose proof (extra_dbits_range d ltac:(lia)).
      nia. }
    rewrite (zho_wsum_scale 18 (fun d => count_D d toks) 0 30).
    pose proof (zho_countD_le toks Henc) as HDL.
    fold M in HDL. lia. }
  (* span and token totals *)
  pose proof (zho_span toks Henc) as Hspan.
  fold L BB in Hspan. rewrite Hext in Hspan.
  pose proof (zho_lm_tot toks Henc) as Hlm.
  fold L M in Hlm.
  assert (HLM : L + M <= 16383) by lia.
  (* assemble *)
  rewrite R1.
  pose proof (count_L_nonneg 257 toks).
  pose proof (count_L_nonneg 258 toks).
  pose proof (count_L_nonneg dom toks).
  pose proof (count_L_nonneg sec toks).
  lia.
Qed.

(** ** Assembly support: pipeline frames, guard shapes, kraft bounds *)

Lemma zho_tr_settree_other : forall k t s j, j <> k ->
  ts_trees (set_tree k t s) j = ts_trees s j.
Proof.
  intros k t s j Hne. unfold set_tree, set_trees. cbn [ts_trees].
  destruct (Z.eqb_spec j k) as [E|_]; [congruence | reflexivity].
Qed.

Lemma zho_tr_settree_same : forall k t s, ts_trees (set_tree k t s) k = t.
Proof.
  intros k t s. unfold set_tree, set_trees. cbn [ts_trees].
  rewrite Z.eqb_refl. reflexivity.
Qed.

(** the S2P L tree is the scan-guarded built L tree *)
Lemma zho_s2p_ltree : forall ts,
  ts_trees (S2P ts) TK_L
  = t_setlen (ts_trees (build_tree TK_L ts) TK_L)
             (ts_maxcode (build_tree TK_L ts) TK_L + 1) 65535.
Proof.
  intro ts.
  unfold S2P, build_bl_tree. cbv zeta. cbn [snd].
  rewrite g6_tr_setoptlen.
  rewrite (build_tree_tree_other TK_BL _ TK_L)
    by (intro E; discriminate E).
  rewrite (zho_tr_settree_other TK_BL _ _ TK_L)
    by (intro E; discriminate E).
  rewrite (zho_tr_settree_other TK_D _ _ TK_L)
    by (intro E; discriminate E).
  rewrite (zho_tr_settree_other TK_BL _ _ TK_L)
    by (intro E; discriminate E).
  rewrite zho_tr_settree_same.
  unfold scan_tree. cbn [fst].
  rewrite (build_tree_tree_other TK_D _ TK_L)
    by (intro E; discriminate E).
  rewrite (build_tree_maxcode_other TK_D _ TK_L)
    by (intro E; discriminate E).
  reflexivity.
Qed.

(** the S2P D tree is the scan-guarded built D tree *)
Lemma zho_s2p_dtree : forall ts,
  ts_trees (S2P ts) TK_D
  = t_setlen (ts_trees (build_tree TK_D (build_tree TK_L ts)) TK_D)
             (ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D + 1)
             65535.
Proof.
  intro ts.
  unfold S2P, build_bl_tree. cbv zeta. cbn [snd].
  rewrite g6_tr_setoptlen.
  rewrite (build_tree_tree_other TK_BL _ TK_D)
    by (intro E; discriminate E).
  rewrite (zho_tr_settree_other TK_BL _ _ TK_D)
    by (intro E; discriminate E).
  rewrite zho_tr_settree_same.
  unfold scan_tree. cbn [fst].
  rewrite (zho_tr_settree_other TK_BL _ _ TK_D)
    by (intro E; discriminate E).
  rewrite (zho_tr_settree_other TK_L _ _ TK_D)
    by (intro E; discriminate E).
  rewrite !g6_mc_settree.
  reflexivity.
Qed.

(** clean three-way split of the L-symbol range *)
Lemma zho_wsum_split3 : forall (f : Z -> Z),
  wsum f 0 286 = wsum f 0 256 + f 256 + wsum f 257 29.
Proof.
  intro f.
  change 286%nat with (256 + (1 + 29))%nat.
  rewrite wsum_app. rewrite wsum_app.
  change (0 + Z.of_nat 256) with 256.
  change (256 + Z.of_nat 1) with 257.
  cbn [wsum]. cbv beta. lia.
Qed.

(** the family kraft bounds (unmasked totals; liveness only shrinks) *)
Lemma zho_kraft_CL2_bound : forall s,
  zho_kraft s TK_L (zho_CL2 (ts_trees s TK_L)) <= 2 ^ 15.
Proof.
  intro s. unfold zho_kraft.
  change (Z.to_nat (sd_elems TK_L)) with 286%nat.
  pose proof (zho_dom_range (ts_trees s TK_L)) as Hdr.
  pose proof (zho_sec_range (ts_trees s TK_L)) as Hsr.
  pose proof (zho_sec_ne_dom (ts_trees s TK_L)) as Hnd.
  eapply Z.le_trans.
  { apply (zho_wsum_le_pt
             (fun n => (if zho_live s TK_L n then 1 else 0)
                       * 2 ^ (15 - zho_CL2 (ts_trees s TK_L) n))
             (fun n => 2 ^ (15 - zho_CL2 (ts_trees s TK_L) n)) 0 286).
    intros n _.
    pose proof (Z.pow_nonneg 2 (15 - zho_CL2 (ts_trees s TK_L) n)
                  ltac:(lia)).
    destruct (zho_live s TK_L n); lia. }
  rewrite (zho_wsum_split3
             (fun n => 2 ^ (15 - zho_CL2 (ts_trees s TK_L) n))).
  (* literals: 9 bits -> 64 each *)
  rewrite (wsum_ext (fun n => 2 ^ (15 - zho_CL2 (ts_trees s TK_L) n))
             (fun _ => 64) 0 256).
  2:{ intros p Hp. change (Z.of_nat 256) with 256 in Hp.
      unfold zho_CL2.
      replace (Z.eqb p (zho_dom (ts_trees s TK_L))) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb p (zho_sec (ts_trees s TK_L))) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb p 256) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.ltb p 256) with true
        by (symmetry; apply Z.ltb_lt; lia).
      reflexivity. }
  rewrite (wsum_ext (fun _ : Z => 64) (fun _ : Z => 64 * 1) 0 256)
    by (intros; ring).
  rewrite (zho_wsum_scale 64 (fun _ => 1) 0 256).
  rewrite wsum_const1.
  (* EOB: 4 bits -> 2048 *)
  unfold zho_CL2 at 1.
  replace (Z.eqb 256 (zho_dom (ts_trees s TK_L))) with false
    by (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb 256 (zho_sec (ts_trees s TK_L))) with false
    by (symmetry; apply Z.eqb_neq; lia).
  rewrite Z.eqb_refl.
  (* match codes: 32 + dom bonus 8160 + sec bonus 4064 *)
  rewrite (wsum_ext (fun n => 2 ^ (15 - zho_CL2 (ts_trees s TK_L) n))
             (fun n => 32
                       + ((if Z.eqb (zho_dom (ts_trees s TK_L)) n
                           then 1 else 0) * 8160
                          + (if Z.eqb (zho_sec (ts_trees s TK_L)) n
                             then 1 else 0) * 4064))
             257 29).
  2:{ intros p Hp.
      change (Z.of_nat 29) with 29 in Hp.
      unfold zho_CL2.
      destruct (Z.eqb_spec p (zho_dom (ts_trees s TK_L))) as [E1|Hne1];
        destruct (Z.eqb_spec (zho_dom (ts_trees s TK_L)) p) as [E2|Hne2];
        try (exfalso; congruence).
      - (* p = dom *)
        replace (Z.eqb p (zho_sec (ts_trees s TK_L))) with false
          by (symmetry; apply Z.eqb_neq; lia).
        destruct (Z.eqb_spec (zho_sec (ts_trees s TK_L)) p) as [E3|Hne3];
          [exfalso; lia | reflexivity].
      - destruct (Z.eqb_spec p (zho_sec (ts_trees s TK_L))) as [E3|Hne3];
          destruct (Z.eqb_spec (zho_sec (ts_trees s TK_L)) p) as [E4|Hne4];
          try (exfalso; congruence).
        + (* p = sec *) reflexivity.
        + replace (Z.eqb p 256) with false
            by (symmetry; apply Z.eqb_neq; lia).
          replace (Z.ltb p 256) with false
            by (symmetry; apply Z.ltb_ge; lia).
          reflexivity. }
  rewrite (wsum_plus (fun _ : Z => 32)
             (fun n => (if Z.eqb (zho_dom (ts_trees s TK_L)) n
                        then 1 else 0) * 8160
                       + (if Z.eqb (zho_sec (ts_trees s TK_L)) n
                          then 1 else 0) * 4064) 257 29).
  rewrite (wsum_plus
             (fun n => (if Z.eqb (zho_dom (ts_trees s TK_L)) n
                        then 1 else 0) * 8160)
             (fun n => (if Z.eqb (zho_sec (ts_trees s TK_L)) n
                        then 1 else 0) * 4064) 257 29).
  rewrite (wsum_delta (fun _ => 8160) (zho_dom (ts_trees s TK_L)) 257 29)
    by (change (Z.of_nat 29) with 29; lia).
  rewrite (wsum_delta (fun _ => 4064) (zho_sec (ts_trees s TK_L)) 257 29)
    by (change (Z.of_nat 29) with 29; lia).
  rewrite (wsum_ext (fun _ : Z => 32) (fun _ : Z => 32 * 1) 257 29)
    by (intros; ring).
  rewrite (zho_wsum_scale 32 (fun _ => 1) 257 29).
  rewrite wsum_const1.
  change (Z.of_nat 29) with 29. change (Z.of_nat 256) with 256. lia.
Qed.

Lemma zho_kraft_CD2_bound : forall s',
  zho_kraft s' TK_D zho_CD2 <= 2 ^ 15.
Proof.
  intro s'. unfold zho_kraft.
  change (Z.to_nat (sd_elems TK_D)) with 30%nat.
  eapply Z.le_trans.
  { apply (zho_wsum_le_pt
             (fun n => (if zho_live s' TK_D n then 1 else 0)
                       * 2 ^ (15 - zho_CD2 n))
             (fun _ => 1024) 0 30).
    intros n _. unfold zho_CD2.
    destruct (zho_live s' TK_D n); cbn; lia. }
  rewrite (wsum_ext (fun _ : Z => 1024) (fun _ : Z => 1024 * 1) 0 30)
    by (intros; ring).
  rewrite (zho_wsum_scale 1024 (fun _ => 1) 0 30).
  rewrite wsum_const1. cbn. lia.
Qed.

(** ** THE DELIVERABLE: the dynamic counter fits the budget. *)

Lemma zq_dead : forall ts toks,
  cEnc toks ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  256 <= ts_maxcode (build_tree TK_L ts) TK_L
  /\ (0 <= ts_maxcode (build_tree TK_L ts) TK_L + 1 < 0 + Z.of_nat 286 ->
      count_L (ts_maxcode (build_tree TK_L ts) TK_L + 1) toks = 0)
  /\ (0 <= ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D + 1
        < 0 + Z.of_nat 30 ->
      count_D (ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D + 1)
        toks = 0).
Proof.
  intros ts toks Henc Hbl HFI.
  assert (HFL := proj1 HFI). assert (HFD := proj2 HFI).
  unfold END_BLOCK in HFL.
  (* --- entry frequency facts --- *)
  assert (Hc256 : count_L 256 toks = 0) by (apply zho_count256; exact Henc).
  assert (HfL256 : t_freq (ts_trees ts TK_L) 256 = 1).
  { rewrite (HFL 256) by (unfold L_CODES; lia).
    rewrite Z.eqb_refl, Hc256. reflexivity. }
  assert (HfLc : forall i, 0 <= i < 286 -> i <> 256 ->
                 t_freq (ts_trees ts TK_L) i = count_L i toks).
  { intros i Hi Hne. rewrite (HFL i) by (unfold L_CODES; lia).
    replace (Z.eqb i 256) with false
      by (symmetry; apply Z.eqb_neq; exact Hne). lia. }
  assert (HfDc : forall i, 0 <= i < 30 ->
                 t_freq (ts_trees ts TK_D) i = count_D i toks).
  { intros i Hi. apply HFD. unfold D_CODES. lia. }
  (* --- built-tree shapes and frames --- *)
  assert (HelL : 3 <= sd_elems TK_L <= 286)
    by (change (sd_elems TK_L) with 286; lia).
  assert (HML : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  assert (HKL : 4 * (sd_elems TK_L - 1) < 2 ^ sd_max_length TK_L)
    by (change (sd_elems TK_L) with 286;
        change (sd_max_length TK_L) with 15; lia).
  destruct (build_tree_shape TK_L ts HelL HML HKL Hbl)
    as (HmcL & HlenL15 & HblBL & HmaxL).
  change (sd_elems TK_L) with 286 in HmcL, HlenL15, HmaxL.
  change (sd_max_length TK_L) with 15 in HlenL15.
  assert (HelD : 3 <= sd_elems TK_D <= 286)
    by (change (sd_elems TK_D) with 30; lia).
  assert (HMD : 1 <= sd_max_length TK_D <= 15)
    by (change (sd_max_length TK_D) with 15; lia).
  assert (HKD : 4 * (sd_elems TK_D - 1) < 2 ^ sd_max_length TK_D)
    by (change (sd_elems TK_D) with 30;
        change (sd_max_length TK_D) with 15; lia).
  destruct (build_tree_shape TK_D (build_tree TK_L ts) HelD HMD HKD HblBL)
    as (HmcD & _ & HblBD & HmaxD).
  change (sd_elems TK_D) with 30 in HmcD, HmaxD.
  assert (NEQ_D_L : TK_D <> TK_L) by (intro E; discriminate E).
  assert (EtD : ts_trees (build_tree TK_L ts) TK_D = ts_trees ts TK_D)
    by (apply build_tree_tree_other; exact NEQ_D_L).
  rewrite EtD in HmaxD.
  (* --- guard indices are dead --- *)
  assert (H256mc : 256 <= ts_maxcode (build_tree TK_L ts) TK_L).
  { apply HmaxL; [lia|]. rewrite HfL256. lia. }
  assert (HdeadL : forall fr : Z -> Z,
            (forall i, 0 <= i < 286 -> i <> 256 ->
               fr i = count_L i toks) ->
            0 <= ts_maxcode (build_tree TK_L ts) TK_L + 1 < 0 + Z.of_nat 286 ->
            fr (ts_maxcode (build_tree TK_L ts) TK_L + 1) = 0).
  { intros fr Hfr Hg. change (Z.of_nat 286) with 286 in Hg.
    rewrite (Hfr (ts_maxcode (build_tree TK_L ts) TK_L + 1)
               ltac:(lia) ltac:(lia)).
    destruct (Z.eqb_spec (count_L (ts_maxcode (build_tree TK_L ts) TK_L + 1)
                            toks) 0) as [E|Hne]; [exact E|].
    exfalso.
    assert (Hle : ts_maxcode (build_tree TK_L ts) TK_L + 1
                  <= ts_maxcode (build_tree TK_L ts) TK_L).
    { apply HmaxL; [lia|].
      rewrite (HfLc (ts_maxcode (build_tree TK_L ts) TK_L + 1)
                 ltac:(lia) ltac:(lia)). exact Hne. }
    lia. }
  assert (HdeadD : 0 <= ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D
                        + 1 < 0 + Z.of_nat 30 ->
            count_D (ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D
                     + 1) toks = 0).
  { intros Hg. change (Z.of_nat 30) with 30 in Hg.
    destruct (Z.eqb_spec (count_D (ts_maxcode
                (build_tree TK_D (build_tree TK_L ts)) TK_D + 1) toks) 0)
      as [E|Hne]; [exact E|].
    exfalso.
    assert (Hle : ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D + 1
                  <= ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D).
    { apply HmaxD; [lia|].
      rewrite (HfDc (ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D
                       + 1) ltac:(lia)). exact Hne. }
    lia. }
  refine (conj H256mc (conj _ HdeadD)).
  intros Hg.
  exact (HdeadL (fun i => count_L i toks) (fun i Hi Hne => eq_refl) Hg).
Qed.

Lemma zq_mainL : forall ts toks slen,
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  toks_ext toks = slen ->
  32506 < slen ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  wsum (fun n => t_freq (ts_trees ts TK_L) n
        * t_len (ts_trees (build_tree TK_L ts) TK_L) n) 0 286
  <= wsum (fun n => t_freq (ts_trees ts TK_L) n
           * zho_CL2 (ts_trees ts TK_L) n) 0 286 + 12288.
Proof.
  intros ts toks slen Henc Hlen Hext Hslen Hbl HFI.
  assert (HFL := proj1 HFI). assert (HFD := proj2 HFI).
  unfold END_BLOCK in HFL.
  (* --- entry frequency facts --- *)
  assert (Hc256 : count_L 256 toks = 0) by (apply zho_count256; exact Henc).
  assert (HfL256 : t_freq (ts_trees ts TK_L) 256 = 1).
  { rewrite (HFL 256) by (unfold L_CODES; lia).
    rewrite Z.eqb_refl, Hc256. reflexivity. }
  assert (HfLc : forall i, 0 <= i < 286 -> i <> 256 ->
                 t_freq (ts_trees ts TK_L) i = count_L i toks).
  { intros i Hi Hne. rewrite (HFL i) by (unfold L_CODES; lia).
    replace (Z.eqb i 256) with false
      by (symmetry; apply Z.eqb_neq; exact Hne). lia. }
  assert (HfDc : forall i, 0 <= i < 30 ->
                 t_freq (ts_trees ts TK_D) i = count_D i toks).
  { intros i Hi. apply HFD. unfold D_CODES. lia. }
  (* --- built-tree shapes and frames --- *)
  assert (HelL : 3 <= sd_elems TK_L <= 286)
    by (change (sd_elems TK_L) with 286; lia).
  assert (HML : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  assert (HKL : 4 * (sd_elems TK_L - 1) < 2 ^ sd_max_length TK_L)
    by (change (sd_elems TK_L) with 286;
        change (sd_max_length TK_L) with 15; lia).
  destruct (build_tree_shape TK_L ts HelL HML HKL Hbl)
    as (HmcL & HlenL15 & HblBL & HmaxL).
  change (sd_elems TK_L) with 286 in HmcL, HlenL15, HmaxL.
  change (sd_max_length TK_L) with 15 in HlenL15.
  assert (HelD : 3 <= sd_elems TK_D <= 286)
    by (change (sd_elems TK_D) with 30; lia).
  assert (HMD : 1 <= sd_max_length TK_D <= 15)
    by (change (sd_max_length TK_D) with 15; lia).
  assert (HKD : 4 * (sd_elems TK_D - 1) < 2 ^ sd_max_length TK_D)
    by (change (sd_elems TK_D) with 30;
        change (sd_max_length TK_D) with 15; lia).
  destruct (build_tree_shape TK_D (build_tree TK_L ts) HelD HMD HKD HblBL)
    as (HmcD & _ & HblBD & HmaxD).
  change (sd_elems TK_D) with 30 in HmcD, HmaxD.
  assert (NEQ_D_L : TK_D <> TK_L) by (intro E; discriminate E).
  assert (EtD : ts_trees (build_tree TK_L ts) TK_D = ts_trees ts TK_D)
    by (apply build_tree_tree_other; exact NEQ_D_L).
  rewrite EtD in HmaxD.
  (* ================= L side: the main theorem at TK_L ============== *)
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_L)
              (ts_trees ts TK_L) (ts_heap ts) (ts_depth ts) 0 (-1))
    as [[[[t0L hp0L] dep0L] hlen0L] maxc0L] eqn:E0L.
  assert (HfuelL : sd_elems TK_L <= Z.of_nat (Z.to_nat L_CODES + 2)).
  { change (sd_elems TK_L) with 286.
    change (Z.to_nat L_CODES + 2)%nat with 288%nat.
    change (Z.of_nat 288) with 288. lia. }
  assert (HposL : 0 < sd_elems TK_L)
    by (change (sd_elems TK_L) with 286; lia).
  destruct (bt_init_census_call _ _ _ _ _ _ _ _ _ _ E0L HfuelL HposL)
    as [HoutL HfrL].
  assert (Hh0L : 2 <= hlen0L).
  { rewrite (io_total _ _ _ _ _ HoutL). unfold live_total.
    change (Z.to_nat (sd_elems TK_L)) with 286%nat.
    destruct (zho_toks_head toks Henc ltac:(rewrite Hext; lia))
      as (s0 & Hs0ne & Hs0r & Hs0c).
    assert (Hfs0 : t_freq (ts_trees ts TK_L) s0 <> 0)
      by (rewrite (HfLc s0 Hs0r Hs0ne); lia).
    assert (Hmc256 : 256 <= maxc0L).
    { destruct (Z.lt_ge_cases maxc0L 256) as [Hlt|]; [|assumption].
      exfalso.
      pose proof (io_gapz _ _ _ _ _ HoutL 256
                    ltac:(change (sd_elems TK_L) with 286; lia)) as Hg.
      rewrite HfrL, HfL256 in Hg. lia. }
    assert (Hmcs0 : s0 <= maxc0L).
    { destruct (Z.lt_ge_cases maxc0L s0) as [Hlt|]; [|lia].
      exfalso.
      pose proof (io_gapz _ _ _ _ _ HoutL s0
                    ltac:(change (sd_elems TK_L) with 286; lia)) as Hg.
      rewrite HfrL in Hg. exact (Hfs0 Hg). }
    apply (zho_ind_two_ge2 (live_b t0L maxc0L) 0 286 256 s0);
      [ change (Z.of_nat 286) with 286; lia
      | change (Z.of_nat 286) with 286; lia
      | lia
      | apply live_b_true; [lia|rewrite HfrL, HfL256; lia]
      | apply live_b_true; [lia|rewrite HfrL; exact Hfs0] ]. }
  assert (HhubL : hlen0L <= 286).
  { rewrite (io_total _ _ _ _ _ HoutL). unfold live_total.
    change (Z.to_nat (sd_elems TK_L)) with 286%nat.
    eapply Z.le_trans.
    - apply (wsum_le (fun s => ind (live_b t0L maxc0L s)) (fun _ => 1)).
      intros i _. pose proof (ind_0_1 (live_b t0L maxc0L i)). lia.
    - rewrite wsum_const1. change (Z.of_nat 286) with 286. lia. }
  destruct (bt_force2 3%nat (sd_stree TK_L) t0L hp0L dep0L hlen0L maxc0L
              (ts_optlen ts) (ts_statlen ts))
    as [[[[[[t1L hp1L] dep1L] hlen1L] maxc1L] ol1L] sl1L] eqn:E2L.
  assert (Ehl1L : hlen0L = hlen1L).
  { pose proof E2L as E2'.
    cbn [bt_force2] in E2'.
    rewrite (proj2 (Z.leb_le 2 hlen0L) Hh0L) in E2'.
    injection E2' as _ _ _ E _ _ _. exact E. }
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1L;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1L dep1L hp1L
                             hlen1L (hlen1L / 2);
                 b_dep := dep1L; b_hlen := hlen1L; b_hmax := HEAP_SIZE;
                 b_node := sd_elems TK_L |}) as [stfL|] eqn:EloopL.
  2:{ exfalso. revert EloopL. apply bt_loop_terminates; cbn [b_hlen].
      - lia.
      - change (Z.of_nat (Z.to_nat HEAP_SIZE)) with 573. lia. }
  assert (HfnnL : forall n, 0 <= n < sd_elems TK_L ->
                  0 <= t_freq (ts_trees ts TK_L) n).
  { intros n Hn. change (sd_elems TK_L) with 286 in Hn.
    rewrite (HFL n) by (unfold L_CODES; lia).
    pose proof (count_L_nonneg n toks).
    destruct (Z.eqb n 256); lia. }
  assert (HtotL : wsum (fun n => t_freq (ts_trees ts TK_L) n) 0
                    (Z.to_nat (sd_elems TK_L)) <= 16384).
  { change (Z.to_nat (sd_elems TK_L)) with 286%nat.
    rewrite (zho_wsum_split3 (fun n => t_freq (ts_trees ts TK_L) n)).
    rewrite (wsum_ext (fun n => t_freq (ts_trees ts TK_L) n)
               (fun c => count_L c toks) 0 256)
      by (intros p Hp; change (Z.of_nat 256) with 256 in Hp;
          apply (HfLc p ltac:(lia) ltac:(lia))).
    rewrite (wsum_ext (fun n => t_freq (ts_trees ts TK_L) n)
               (fun c => count_L c toks) 257 29)
      by (intros p Hp; change (Z.of_nat 29) with 29 in Hp;
          apply (HfLc p ltac:(lia) ltac:(lia))).
    rewrite HfL256.
    pose proof (zho_lm_tot toks Henc). lia. }
  assert (HrngL : forall n, 0 <= n < sd_elems TK_L ->
                  zho_live ts TK_L n = true ->
                  1 <= zho_CL2 (ts_trees ts TK_L) n <= 15).
  { intros n _ _. unfold zho_CL2.
    destruct (Z.eqb n (zho_dom (ts_trees ts TK_L))); [lia|].
    destruct (Z.eqb n (zho_sec (ts_trees ts TK_L))); [lia|].
    destruct (Z.eqb n 256); [lia|].
    destruct (Z.ltb n 256); lia. }
  pose proof (build_tree_cost_opt_main TK_L ts t0L hp0L dep0L hlen0L maxc0L
                t1L hp1L dep1L hlen1L maxc1L ol1L sl1L stfL
                (zho_CL2 (ts_trees ts TK_L))
                HelL ltac:(reflexivity) Hbl HfnnL HtotL E0L Hh0L E2L EloopL
                HrngL (zho_kraft_CL2_bound ts)) as HmainL.
  unfold zho_cost in HmainL.
  change (Z.to_nat (sd_elems TK_L)) with 286%nat in HmainL.
  change (ZHO_K TK_L) with 12288 in HmainL.
  cbv beta in HmainL.
  exact HmainL.
Qed.

Lemma zq_mainD : forall ts toks,
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  wsum (fun i => t_freq (ts_trees ts TK_D) i
        * t_len (ts_trees (build_tree TK_D (build_tree TK_L ts)) TK_D) i)
       0 30
  <= 5 * wsum (fun d => count_D d toks) 0 30 + 2048.
Proof.
  intros ts toks Henc Hlen Hbl HFI HnnD.
  assert (HFL := proj1 HFI). assert (HFD := proj2 HFI).
  unfold END_BLOCK in HFL.
  (* --- entry frequency facts --- *)
  assert (Hc256 : count_L 256 toks = 0) by (apply zho_count256; exact Henc).
  assert (HfL256 : t_freq (ts_trees ts TK_L) 256 = 1).
  { rewrite (HFL 256) by (unfold L_CODES; lia).
    rewrite Z.eqb_refl, Hc256. reflexivity. }
  assert (HfLc : forall i, 0 <= i < 286 -> i <> 256 ->
                 t_freq (ts_trees ts TK_L) i = count_L i toks).
  { intros i Hi Hne. rewrite (HFL i) by (unfold L_CODES; lia).
    replace (Z.eqb i 256) with false
      by (symmetry; apply Z.eqb_neq; exact Hne). lia. }
  assert (HfDc : forall i, 0 <= i < 30 ->
                 t_freq (ts_trees ts TK_D) i = count_D i toks).
  { intros i Hi. apply HFD. unfold D_CODES. lia. }
  (* --- built-tree shapes and frames --- *)
  assert (HelL : 3 <= sd_elems TK_L <= 286)
    by (change (sd_elems TK_L) with 286; lia).
  assert (HML : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  assert (HKL : 4 * (sd_elems TK_L - 1) < 2 ^ sd_max_length TK_L)
    by (change (sd_elems TK_L) with 286;
        change (sd_max_length TK_L) with 15; lia).
  destruct (build_tree_shape TK_L ts HelL HML HKL Hbl)
    as (HmcL & HlenL15 & HblBL & HmaxL).
  change (sd_elems TK_L) with 286 in HmcL, HlenL15, HmaxL.
  change (sd_max_length TK_L) with 15 in HlenL15.
  assert (HelD : 3 <= sd_elems TK_D <= 286)
    by (change (sd_elems TK_D) with 30; lia).
  assert (HMD : 1 <= sd_max_length TK_D <= 15)
    by (change (sd_max_length TK_D) with 15; lia).
  assert (HKD : 4 * (sd_elems TK_D - 1) < 2 ^ sd_max_length TK_D)
    by (change (sd_elems TK_D) with 30;
        change (sd_max_length TK_D) with 15; lia).
  destruct (build_tree_shape TK_D (build_tree TK_L ts) HelD HMD HKD HblBL)
    as (HmcD & _ & HblBD & HmaxD).
  change (sd_elems TK_D) with 30 in HmcD, HmaxD.
  assert (NEQ_D_L : TK_D <> TK_L) by (intro E; discriminate E).
  assert (EtD : ts_trees (build_tree TK_L ts) TK_D = ts_trees ts TK_D)
    by (apply build_tree_tree_other; exact NEQ_D_L).
  rewrite EtD in HmaxD.
  (* ================= D side: live-count split ======================= *)
  assert (HD : wsum (fun i => t_freq (ts_trees ts TK_D) i
                       * t_len (ts_trees (build_tree TK_D (build_tree TK_L ts))
                                  TK_D) i) 0 30
               <= 5 * wsum (fun d => count_D d toks) 0 30 + 2048).
  { destruct (Z.leb 2 (wsum (fun i => ind (negb (Z.eqb
                (t_freq (ts_trees ts TK_D) i) 0))) 0 30)) eqn:ELC.
    - (* >= 2 live distance codes: the theorem at TK_D *)
      apply Z.leb_le in ELC.
      destruct (zho_ind_two_inv
                  (fun i => negb (Z.eqb (t_freq (ts_trees ts TK_D) i) 0))
                  0 30 ELC) as (p & q & Hp & Hq & Hpq & Hgp & Hgq).
      change (Z.of_nat 30) with 30 in Hp, Hq.
      assert (Hfp : t_freq (ts_trees ts TK_D) p <> 0)
        by (apply (proj1 (Z.eqb_neq _ _)); apply negb_true_iff; exact Hgp).
      assert (Hfq : t_freq (ts_trees ts TK_D) q <> 0)
        by (apply (proj1 (Z.eqb_neq _ _)); apply negb_true_iff; exact Hgq).
      destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_D)
                  (ts_trees (build_tree TK_L ts) TK_D)
                  (ts_heap (build_tree TK_L ts))
                  (ts_depth (build_tree TK_L ts)) 0 (-1))
        as [[[[t0D hp0D] dep0D] hlen0D] maxc0D] eqn:E0D.
      assert (HfuelD : sd_elems TK_D <= Z.of_nat (Z.to_nat L_CODES + 2)).
      { change (sd_elems TK_D) with 30.
        change (Z.to_nat L_CODES + 2)%nat with 288%nat.
        change (Z.of_nat 288) with 288. lia. }
      assert (HposD : 0 < sd_elems TK_D)
        by (change (sd_elems TK_D) with 30; lia).
      destruct (bt_init_census_call _ _ _ _ _ _ _ _ _ _ E0D HfuelD HposD)
        as [HoutD HfrD].
      assert (HfrD' : forall i, t_freq t0D i = t_freq (ts_trees ts TK_D) i)
        by (intro i; rewrite HfrD, EtD; reflexivity).
      assert (Hmcp : p <= maxc0D).
      { destruct (Z.lt_ge_cases maxc0D p) as [Hlt|]; [|lia].
        exfalso.
        pose proof (io_gapz _ _ _ _ _ HoutD p
                      ltac:(change (sd_elems TK_D) with 30; lia)) as Hg.
        rewrite HfrD' in Hg. exact (Hfp Hg). }
      assert (Hmcq : q <= maxc0D).
      { destruct (Z.lt_ge_cases maxc0D q) as [Hlt|]; [|lia].
        exfalso.
        pose proof (io_gapz _ _ _ _ _ HoutD q
                      ltac:(change (sd_elems TK_D) with 30; lia)) as Hg.
        rewrite HfrD' in Hg. exact (Hfq Hg). }
      assert (Hh0D : 2 <= hlen0D).
      { rewrite (io_total _ _ _ _ _ HoutD). unfold live_total.
        change (Z.to_nat (sd_elems TK_D)) with 30%nat.
        apply (zho_ind_two_ge2 (live_b t0D maxc0D) 0 30 p q);
          [ change (Z.of_nat 30) with 30; lia
          | change (Z.of_nat 30) with 30; lia
          | exact Hpq
          | apply live_b_true; [lia|rewrite HfrD'; exact Hfp]
          | apply live_b_true; [lia|rewrite HfrD'; exact Hfq] ]. }
      assert (HhubD : hlen0D <= 30).
      { rewrite (io_total _ _ _ _ _ HoutD). unfold live_total.
        change (Z.to_nat (sd_elems TK_D)) with 30%nat.
        eapply Z.le_trans.
        - apply (wsum_le (fun s => ind (live_b t0D maxc0D s)) (fun _ => 1)).
          intros i _. pose proof (ind_0_1 (live_b t0D maxc0D i)). lia.
        - rewrite wsum_const1. change (Z.of_nat 30) with 30. lia. }
      destruct (bt_force2 3%nat (sd_stree TK_D) t0D hp0D dep0D hlen0D maxc0D
                  (ts_optlen (build_tree TK_L ts))
                  (ts_statlen (build_tree TK_L ts)))
        as [[[[[[t1D hp1D] dep1D] hlen1D] maxc1D] ol1D] sl1D] eqn:E2D.
      assert (Ehl1D : hlen0D = hlen1D).
      { pose proof E2D as E2'.
        cbn [bt_force2] in E2'.
        rewrite (proj2 (Z.leb_le 2 hlen0D) Hh0D) in E2'.
        injection E2' as _ _ _ E _ _ _. exact E. }
      destruct (bt_loop (Z.to_nat HEAP_SIZE)
                  {| b_tree := t1D;
                     b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1D dep1D hp1D
                                 hlen1D (hlen1D / 2);
                     b_dep := dep1D; b_hlen := hlen1D; b_hmax := HEAP_SIZE;
                     b_node := sd_elems TK_D |}) as [stfD|] eqn:EloopD.
      2:{ exfalso. revert EloopD. apply bt_loop_terminates; cbn [b_hlen].
          - lia.
          - change (Z.of_nat (Z.to_nat HEAP_SIZE)) with 573. lia. }
      assert (HfnnD : forall n, 0 <= n < sd_elems TK_D ->
                      0 <= t_freq (ts_trees (build_tree TK_L ts) TK_D) n).
      { intros n Hn. change (sd_elems TK_D) with 30 in Hn.
        rewrite EtD, (HfDc n Hn). apply count_D_nonneg. }
      assert (HtotD : wsum (fun n => t_freq (ts_trees (build_tree TK_L ts)
                              TK_D) n) 0 (Z.to_nat (sd_elems TK_D)) <= 16384).
      { change (Z.to_nat (sd_elems TK_D)) with 30%nat.
        rewrite (wsum_ext (fun n => t_freq (ts_trees (build_tree TK_L ts)
                             TK_D) n)
                   (fun d => count_D d toks) 0 30)
          by (intros p' Hp'; change (Z.of_nat 30) with 30 in Hp';
              rewrite EtD; apply (HfDc p' ltac:(lia))).
        pose proof (zho_countD_le toks Henc).
        pose proof (zho_lm_tot toks Henc).
        assert (0 <= wsum (fun c => count_L c toks) 0 256)
          by (apply wsum_nonneg; intros; apply count_L_nonneg).
        lia. }
      assert (HrngD : forall n, 0 <= n < sd_elems TK_D ->
                      zho_live (build_tree TK_L ts) TK_D n = true ->
                      1 <= zho_CD2 n <= 15)
        by (intros n _ _; unfold zho_CD2; lia).
      pose proof (build_tree_cost_opt_main TK_D (build_tree TK_L ts)
                    t0D hp0D dep0D hlen0D maxc0D
                    t1D hp1D dep1D hlen1D maxc1D ol1D sl1D stfD zho_CD2
                    HelD ltac:(reflexivity) HblBL HfnnD HtotD E0D Hh0D E2D
                    EloopD HrngD
                    (zho_kraft_CD2_bound (build_tree TK_L ts))) as HmainD.
      unfold zho_cost in HmainD.
      change (Z.to_nat (sd_elems TK_D)) with 30%nat in HmainD.
      change (ZHO_K TK_D) with 2048 in HmainD.
      unfold zho_CD2 in HmainD.
      cbv beta in HmainD.
      rewrite EtD in HmainD.
      assert (E5 : wsum (fun n => t_freq (ts_trees ts TK_D) n * 5) 0 30
                   = 5 * wsum (fun d => count_D d toks) 0 30).
      { rewrite (wsum_ext (fun n => t_freq (ts_trees ts TK_D) n * 5)
                   (fun d => 5 * count_D d toks) 0 30)
          by (intros p' Hp'; change (Z.of_nat 30) with 30 in Hp';
              rewrite (HfDc p' ltac:(lia)); ring).
        apply (zho_wsum_scale 5 (fun d => count_D d toks) 0 30). }
      lia.
    - (* <= 1 live distance code: the corner lemma *)
      apply Z.leb_gt in ELC.
      assert (Hone : forall i j, 0 <= i < 30 -> 0 <= j < 30 -> i <> j ->
                t_freq (ts_trees ts TK_D) i = 0
                \/ t_freq (ts_trees ts TK_D) j = 0).
      { intros i j Hi Hj Hij.
        destruct (Z.eqb_spec (t_freq (ts_trees ts TK_D) i) 0) as [Ei|Ei];
          [left; exact Ei|].
        destruct (Z.eqb_spec (t_freq (ts_trees ts TK_D) j) 0) as [Ej|Ej];
          [right; exact Ej|].
        exfalso.
        assert (H2 : 2 <= wsum (fun x => ind (negb (Z.eqb
                       (t_freq (ts_trees ts TK_D) x) 0))) 0 30).
        { apply (zho_ind_two_ge2 _ 0 30 i j);
            [ change (Z.of_nat 30) with 30; lia
            | change (Z.of_nat 30) with 30; lia
            | exact Hij
            | now rewrite (proj2 (Z.eqb_neq _ _) Ei)
            | now rewrite (proj2 (Z.eqb_neq _ _) Ej) ]. }
        lia. }
      pose proof (zho_d_corner' ts toks HFI Henc Hbl HnnD Hone
                    (ts_trees (build_tree TK_D (build_tree TK_L ts)) TK_D)
                    eq_refl) as Hcor.
      change (Z.to_nat (sd_elems TK_D)) with 30%nat in Hcor.
      assert (HSDnn : 0 <= wsum (fun d => count_D d toks) 0 30)
        by (apply wsum_nonneg; intros; apply count_D_nonneg).
      assert (ESD : wsum (fun n => t_freq (ts_trees ts TK_D) n) 0 30
                    = wsum (fun d => count_D d toks) 0 30).
      { apply wsum_ext. intros p Hp. change (Z.of_nat 30) with 30 in Hp.
        apply HfDc. lia. }
      rewrite ESD in Hcor. lia. }
  exact HD.
Qed.

Lemma zq_t8 : forall ts toks,
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  256 <= ts_maxcode (build_tree TK_L ts) TK_L ->
  (0 <= ts_maxcode (build_tree TK_L ts) TK_L + 1 < 0 + Z.of_nat 286 ->
     count_L (ts_maxcode (build_tree TK_L ts) TK_L + 1) toks = 0) ->
  (0 <= ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D + 1
      < 0 + Z.of_nat 30 ->
     count_D (ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D + 1)
       toks = 0) ->
  ts_optlen (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
  <= wsum (fun i => count_L i toks
            * t_len (ts_trees (build_tree TK_L ts) TK_L) i) 0 286
     + wsum (fun i => count_L i toks
              * (if Z.leb 257 i then extra_lbits (i - 257) else 0)) 0 286
     + wsum (fun i => t_freq (ts_trees ts TK_D) i
              * t_len (ts_trees (build_tree TK_D (build_tree TK_L ts))
                         TK_D) i) 0 30
     + wsum (fun i => count_D i toks * extra_dbits i) 0 30
     + t_len (ts_trees (build_tree TK_L ts) TK_L) 256
     + (14 + 3 * (S2M ts + 1))
     + zho_bldesc ts TK_L + zho_bldesc ts TK_D + 6.
Proof.
  intros ts toks Henc Hlen Hol Hsl Hbl HFI HblZ HnnL HnnD H256mc HdL HdD.
  assert (HFL := proj1 HFI). assert (HFD := proj2 HFI).
  unfold END_BLOCK in HFL.
  (* --- entry frequency facts --- *)
  assert (Hc256 : count_L 256 toks = 0) by (apply zho_count256; exact Henc).
  assert (HfL256 : t_freq (ts_trees ts TK_L) 256 = 1).
  { rewrite (HFL 256) by (unfold L_CODES; lia).
    rewrite Z.eqb_refl, Hc256. reflexivity. }
  assert (HfLc : forall i, 0 <= i < 286 -> i <> 256 ->
                 t_freq (ts_trees ts TK_L) i = count_L i toks).
  { intros i Hi Hne. rewrite (HFL i) by (unfold L_CODES; lia).
    replace (Z.eqb i 256) with false
      by (symmetry; apply Z.eqb_neq; exact Hne). lia. }
  assert (HfDc : forall i, 0 <= i < 30 ->
                 t_freq (ts_trees ts TK_D) i = count_D i toks).
  { intros i Hi. apply HFD. unfold D_CODES. lia. }
  pose proof (dispatch_ol_upper ts toks Hol Hsl Hbl HFI Henc Hlen HblZ
                HnnL HnnD) as Hup.
  pose proof (toks_cost_regroup (ts_trees (S2P ts) TK_L)
                (ts_trees (S2P ts) TK_D) toks Henc) as E1.
  assert (EL1 : wsum (fun c => count_L c toks
                   * cost_L (ts_trees (S2P ts) TK_L) c) 0 (Z.to_nat L_CODES)
              = wsum (fun c => count_L c toks
                   * t_len (ts_trees (S2P ts) TK_L) c) 0 286
                + wsum (fun c => count_L c toks
                   * (if Z.leb 257 c then extra_lbits (c - 257) else 0))
                    0 286).
  { change (Z.to_nat L_CODES) with 286%nat.
    etransitivity.
    - apply (wsum_ext
               (fun c => count_L c toks * cost_L (ts_trees (S2P ts) TK_L) c)
               (fun c => count_L c toks * t_len (ts_trees (S2P ts) TK_L) c
                  + count_L c toks
                    * (if Z.leb 257 c then extra_lbits (c - 257) else 0))
               0 286).
      intros p Hp. unfold cost_L. change (LITERALS + 1) with 257.
      apply Z.mul_add_distr_l.
    - apply (wsum_plus
               (fun c => count_L c toks * t_len (ts_trees (S2P ts) TK_L) c)
               (fun c => count_L c toks
                  * (if Z.leb 257 c then extra_lbits (c - 257) else 0))
               0 286). }
  assert (EL2 : wsum (fun c => count_L c toks
                   * t_len (ts_trees (S2P ts) TK_L) c) 0 286
              = wsum (fun i => count_L i toks
                   * t_len (ts_trees (build_tree TK_L ts) TK_L) i) 0 286).
  { etransitivity.
    - exact (f_equal
               (fun t : Tree => wsum (fun c => count_L c toks * t_len t c)
                                  0 286)
               (zho_s2p_ltree ts)).
    - exact (zho_wsum_setlen_dead (fun i => count_L i toks)
               (ts_trees (build_tree TK_L ts) TK_L)
               (ts_maxcode (build_tree TK_L ts) TK_L + 1) 65535 0 286 HdL). }
  assert (ED1 : wsum (fun c => count_D c toks
                   * cost_D (ts_trees (S2P ts) TK_D) c) 0 (Z.to_nat D_CODES)
              = wsum (fun c => count_D c toks
                   * t_len (ts_trees (S2P ts) TK_D) c) 0 30
                + wsum (fun i => count_D i toks * extra_dbits i) 0 30).
  { change (Z.to_nat D_CODES) with 30%nat.
    etransitivity.
    - apply (wsum_ext
               (fun c => count_D c toks * cost_D (ts_trees (S2P ts) TK_D) c)
               (fun c => count_D c toks * t_len (ts_trees (S2P ts) TK_D) c
                  + count_D c toks * extra_dbits c)
               0 30).
      intros p Hp. unfold cost_D.
      apply Z.mul_add_distr_l.
    - apply (wsum_plus
               (fun c => count_D c toks * t_len (ts_trees (S2P ts) TK_D) c)
               (fun c => count_D c toks * extra_dbits c) 0 30). }
  assert (ED2 : wsum (fun c => count_D c toks
                   * t_len (ts_trees (S2P ts) TK_D) c) 0 30
              = wsum (fun i => count_D i toks
                   * t_len (ts_trees (build_tree TK_D (build_tree TK_L ts))
                              TK_D) i) 0 30).
  { etransitivity.
    - exact (f_equal
               (fun t : Tree => wsum (fun c => count_D c toks * t_len t c)
                                  0 30)
               (zho_s2p_dtree ts)).
    - exact (zho_wsum_setlen_dead (fun i => count_D i toks)
               (ts_trees (build_tree TK_D (build_tree TK_L ts)) TK_D)
               (ts_maxcode (build_tree TK_D (build_tree TK_L ts)) TK_D + 1)
               65535 0 30 HdD). }
  assert (ED3 : wsum (fun i => count_D i toks
                   * t_len (ts_trees (build_tree TK_D (build_tree TK_L ts))
                              TK_D) i) 0 30
              = wsum (fun i => t_freq (ts_trees ts TK_D) i
                   * t_len (ts_trees (build_tree TK_D (build_tree TK_L ts))
                              TK_D) i) 0 30).
  { apply wsum_ext. intros p Hp.
    change (Z.of_nat 30) with 30 in Hp.
    rewrite (HfDc p Hp). reflexivity. }
  assert (Eeob : t_len (ts_trees (S2P ts) TK_L) END_BLOCK
               = t_len (ts_trees (build_tree TK_L ts) TK_L) 256).
  { unfold END_BLOCK.
    etransitivity.
    - exact (f_equal (fun t : Tree => t_len t 256) (zho_s2p_ltree ts)).
    - cbv beta. unfold t_len, t_setlen. cbn [tr_dl]. apply zset_other.
      lia. }
  assert (HLlen : wsum (fun i => count_L i toks
                          * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
                    0 286
                  + t_len (ts_trees (build_tree TK_L ts) TK_L) 256
                  = wsum (fun i => t_freq (ts_trees ts TK_L) i
                          * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
                      0 286).
  { rewrite (wsum_ext
               (fun i => t_freq (ts_trees ts TK_L) i
                         * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               (fun i => count_L i toks
                         * t_len (ts_trees (build_tree TK_L ts) TK_L) i
                         + (if Z.eqb 256 i then 1 else 0)
                           * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               0 286).
    2:{ intros p Hp. change (Z.of_nat 286) with 286 in Hp.
        destruct (Z.eqb_spec 256 p) as [<-|Hne].
        - rewrite HfL256, Hc256. ring.
        - rewrite (HfLc p Hp ltac:(lia)). ring. }
    rewrite (wsum_plus
               (fun i => count_L i toks
                         * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               (fun i => (if Z.eqb 256 i then 1 else 0)
                         * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               0 286).
    rewrite (wsum_delta
               (fun i => t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               256 0 286) by (change (Z.of_nat 286) with 286; lia).
    lia. }
  eapply Z.le_trans; [exact Hup|].
  lia.
Qed.

Theorem zr_l1_dyn_fits : forall ts toks slen,
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  toks_ext toks = slen ->
  32506 < slen ->
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  ts_optlen (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
  <= 8 * slen + 21.
Proof.
  intros ts toks slen Henc Hlen Hext Hslen Hol Hsl Hbl HFI HblZ HnnL HnnD.
  assert (HFL := proj1 HFI). assert (HFD := proj2 HFI).
  unfold END_BLOCK in HFL.
  (* --- entry frequency facts --- *)
  assert (Hc256 : count_L 256 toks = 0) by (apply zho_count256; exact Henc).
  assert (HfL256 : t_freq (ts_trees ts TK_L) 256 = 1).
  { rewrite (HFL 256) by (unfold L_CODES; lia).
    rewrite Z.eqb_refl, Hc256. reflexivity. }
  assert (HfLc : forall i, 0 <= i < 286 -> i <> 256 ->
                 t_freq (ts_trees ts TK_L) i = count_L i toks).
  { intros i Hi Hne. rewrite (HFL i) by (unfold L_CODES; lia).
    replace (Z.eqb i 256) with false
      by (symmetry; apply Z.eqb_neq; exact Hne). lia. }
  assert (HfDc : forall i, 0 <= i < 30 ->
                 t_freq (ts_trees ts TK_D) i = count_D i toks).
  { intros i Hi. apply HFD. unfold D_CODES. lia. }
  destruct (zq_dead ts toks Henc Hbl HFI) as (H256mc & HdL & HdD).
  eapply Z.le_trans;
    [exact (zq_t8 ts toks Henc Hlen Hol Hsl Hbl HFI HblZ HnnL HnnD
              H256mc HdL HdD)|].
  pose proof (zq_mainL ts toks slen Henc Hlen Hext Hslen Hbl HFI)
    as HmainL.
  pose proof (zq_mainD ts toks Henc Hlen Hbl HFI HnnD) as HD.
  assert (HLlen : wsum (fun i => count_L i toks
                          * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
                    0 286
                  + t_len (ts_trees (build_tree TK_L ts) TK_L) 256
                  = wsum (fun i => t_freq (ts_trees ts TK_L) i
                          * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
                      0 286).
  { rewrite (wsum_ext
               (fun i => t_freq (ts_trees ts TK_L) i
                         * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               (fun i => count_L i toks
                         * t_len (ts_trees (build_tree TK_L ts) TK_L) i
                         + (if Z.eqb 256 i then 1 else 0)
                           * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               0 286).
    2:{ intros p Hp. change (Z.of_nat 286) with 286 in Hp.
        destruct (Z.eqb_spec 256 p) as [<-|Hne].
        - rewrite HfL256, Hc256. ring.
        - rewrite (HfLc p Hp ltac:(lia)). ring. }
    rewrite (wsum_plus
               (fun i => count_L i toks
                         * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               (fun i => (if Z.eqb 256 i then 1 else 0)
                         * t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               0 286).
    rewrite (wsum_delta
               (fun i => t_len (ts_trees (build_tree TK_L ts) TK_L) i)
               256 0 286) by (change (Z.of_nat 286) with 286; lia).
    lia. }
  (* ================= descriptor cap and the certificate ============ *)
  pose proof (zho_bl_cap ts toks Hol Hsl Hbl HFI Henc Hlen HblZ HnnL HnnD)
    as Hcap.
  assert (Hdmax : forall c, 257 <= c <= 285 ->
            count_L c toks <= count_L (zho_dom (ts_trees ts TK_L)) toks).
  { intros c Hc.
    pose proof (zho_dom_max (ts_trees ts TK_L) c Hc) as H.
    pose proof (zho_dom_range (ts_trees ts TK_L)) as Hdr.
    rewrite (HfLc c ltac:(lia) ltac:(lia)) in H.
    rewrite (HfLc (zho_dom (ts_trees ts TK_L)) ltac:(lia) ltac:(lia)) in H.
    exact H. }
  assert (Hsmax : forall c, 257 <= c <= 285 ->
            c <> zho_dom (ts_trees ts TK_L) ->
            count_L c toks <= count_L (zho_sec (ts_trees ts TK_L)) toks).
  { intros c Hc Hcd.
    pose proof (zho_sec_max (ts_trees ts TK_L) c Hc Hcd) as H.
    pose proof (zho_sec_range (ts_trees ts TK_L)) as Hsr.
    rewrite (HfLc c ltac:(lia) ltac:(lia)) in H.
    rewrite (HfLc (zho_sec (ts_trees ts TK_L)) ltac:(lia) ltac:(lia)) in H.
    exact H. }
  pose proof (zho_cert toks slen (zho_dom (ts_trees ts TK_L))
                (zho_sec (ts_trees ts TK_L)) Henc Hlen Hext Hslen
                (zho_dom_range (ts_trees ts TK_L))
                (zho_sec_range (ts_trees ts TK_L))
                (zho_sec_ne_dom (ts_trees ts TK_L))
                Hdmax Hsmax) as Hcert.
  (* ================= bridges into the certificate vocabulary ======= *)
  assert (EcostC : wsum (fun n => t_freq (ts_trees ts TK_L) n
                          * zho_CL2 (ts_trees ts TK_L) n) 0 286
                   = 9 * wsum (fun c => count_L c toks) 0 256
                     + 4
                     + wsum (fun c => count_L c toks
                         * (if Z.eqb c (zho_dom (ts_trees ts TK_L)) then 2
                            else if Z.eqb c (zho_sec (ts_trees ts TK_L))
                                 then 3 else 10)) 257 29).
  { rewrite (zho_wsum_split3 (fun n => t_freq (ts_trees ts TK_L) n
                                * zho_CL2 (ts_trees ts TK_L) n)).
    pose proof (zho_dom_range (ts_trees ts TK_L)) as Hdr.
    pose proof (zho_sec_range (ts_trees ts TK_L)) as Hsr.
    rewrite (wsum_ext (fun n => t_freq (ts_trees ts TK_L) n
                         * zho_CL2 (ts_trees ts TK_L) n)
               (fun c => 9 * count_L c toks) 0 256).
    2:{ intros p Hp. change (Z.of_nat 256) with 256 in Hp.
        unfold zho_CL2.
        replace (Z.eqb p (zho_dom (ts_trees ts TK_L))) with false
          by (symmetry; apply Z.eqb_neq; lia).
        replace (Z.eqb p (zho_sec (ts_trees ts TK_L))) with false
          by (symmetry; apply Z.eqb_neq; lia).
        replace (Z.eqb p 256) with false
          by (symmetry; apply Z.eqb_neq; lia).
        replace (Z.ltb p 256) with true
          by (symmetry; apply Z.ltb_lt; lia).
        rewrite (HfLc p ltac:(lia) ltac:(lia)). ring. }
    rewrite (zho_wsum_scale 9 (fun c => count_L c toks) 0 256).
    rewrite (wsum_ext (fun n => t_freq (ts_trees ts TK_L) n
                         * zho_CL2 (ts_trees ts TK_L) n)
               (fun c => count_L c toks
                  * (if Z.eqb c (zho_dom (ts_trees ts TK_L)) then 2
                     else if Z.eqb c (zho_sec (ts_trees ts TK_L))
                          then 3 else 10)) 257 29).
    2:{ intros p Hp. change (Z.of_nat 29) with 29 in Hp.
        unfold zho_CL2.
        rewrite (HfLc p ltac:(lia) ltac:(lia)).
        destruct (Z.eqb p (zho_dom (ts_trees ts TK_L))); [ring|].
        destruct (Z.eqb p (zho_sec (ts_trees ts TK_L))); [ring|].
        replace (Z.eqb p 256) with false
          by (symmetry; apply Z.eqb_neq; lia).
        replace (Z.ltb p 256) with false
          by (symmetry; apply Z.ltb_ge; lia).
        ring. }
    unfold zho_CL2.
    replace (Z.eqb 256 (zho_dom (ts_trees ts TK_L))) with false
      by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb 256 (zho_sec (ts_trees ts TK_L))) with false
      by (symmetry; apply Z.eqb_neq; lia).
    rewrite Z.eqb_refl.
    rewrite HfL256. lia. }
  assert (Exb : wsum (fun i => count_L i toks
                        * (if Z.leb 257 i then extra_lbits (i - 257) else 0))
                  0 286
                = wsum (fun c => count_L c toks * extra_lbits (c - 257))
                    257 29).
  { rewrite (zho_wsum_split3 (fun i => count_L i toks
               * (if Z.leb 257 i then extra_lbits (i - 257) else 0))).
    rewrite (wsum_ext (fun i => count_L i toks
               * (if Z.leb 257 i then extra_lbits (i - 257) else 0))
               (fun _ : Z => 0) 0 256).
    2:{ intros p Hp. change (Z.of_nat 256) with 256 in Hp.
        replace (Z.leb 257 p) with false
          by (symmetry; apply Z.leb_gt; lia).
        ring. }
    rewrite (wsum_ext (fun i => count_L i toks
               * (if Z.leb 257 i then extra_lbits (i - 257) else 0))
               (fun c => count_L c toks * extra_lbits (c - 257)) 257 29).
    2:{ intros p Hp. change (Z.of_nat 29) with 29 in Hp.
        replace (Z.leb 257 p) with true
          by (symmetry; apply Z.leb_le; lia).
        reflexivity. }
    change (if Z.leb 257 256 then extra_lbits (256 - 257) else 0) with 0.
    rewrite (g6_wsum_zero (fun _ : Z => 0) 0 256) by (intros; reflexivity).
    lia. }
  assert (Ecomb : wsum (fun c => count_L c toks
                    * ((if Z.eqb c (zho_dom (ts_trees ts TK_L)) then 2
                        else if Z.eqb c (zho_sec (ts_trees ts TK_L))
                             then 3 else 10)
                       + extra_lbits (c - 257))) 257 29
                  = wsum (fun c => count_L c toks
                      * (if Z.eqb c (zho_dom (ts_trees ts TK_L)) then 2
                         else if Z.eqb c (zho_sec (ts_trees ts TK_L))
                              then 3 else 10)) 257 29
                    + wsum (fun c => count_L c toks * extra_lbits (c - 257))
                        257 29).
  { rewrite (wsum_ext (fun c => count_L c toks
               * ((if Z.eqb c (zho_dom (ts_trees ts TK_L)) then 2
                   else if Z.eqb c (zho_sec (ts_trees ts TK_L))
                        then 3 else 10)
                  + extra_lbits (c - 257)))
               (fun c => count_L c toks
                  * (if Z.eqb c (zho_dom (ts_trees ts TK_L)) then 2
                     else if Z.eqb c (zho_sec (ts_trees ts TK_L))
                          then 3 else 10)
                  + count_L c toks * extra_lbits (c - 257))
               257 29) by (intros; ring).
    apply (wsum_plus
             (fun c => count_L c toks
                * (if Z.eqb c (zho_dom (ts_trees ts TK_L)) then 2
                   else if Z.eqb c (zho_sec (ts_trees ts TK_L))
                        then 3 else 10))
             (fun c => count_L c toks * extra_lbits (c - 257)) 257 29). }
  assert (EcertD : wsum (fun d => count_D d toks * (5 + extra_dbits d)) 0 30
                   = 5 * wsum (fun d => count_D d toks) 0 30
                     + wsum (fun i => count_D i toks * extra_dbits i) 0 30).
  { rewrite (wsum_ext (fun d => count_D d toks * (5 + extra_dbits d))
               (fun d => 5 * count_D d toks + count_D d toks * extra_dbits d)
               0 30) by (intros; ring).
    rewrite (wsum_plus (fun d => 5 * count_D d toks)
               (fun d => count_D d toks * extra_dbits d) 0 30).
    rewrite (zho_wsum_scale 5 (fun d => count_D d toks) 0 30).
    reflexivity. }
  lia.
Qed.
