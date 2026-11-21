(** * W3Trip — the per-trip classification core (q7-decode, ZrLenFastLeg
      discharge W3, 2026-08-20, OFF-TREE SCRATCH).

    One [if_body] trip at an owned root read IS one [decode_lit_len]
    step, with the [resolve_lz] slice threading.  Consumes the W1
    content pack and the W2 stream view; mirrors ZReproQ6M's producing
    pattern at the fast reader (buffered case only — [if_refill15]
    keeps every code read inside [f_bits]). *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast
  InflateThy ZBitsBridge DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W1Content W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Local copies of the scratch interface definitions (re-point at
       landing).
   ========================================================================== *)

(** Copy of ZReproQ6M.zr_root_own (scratch; re-point at landing). *)
Definition w3_root_own (T : ztbl) (root : Z) (lens : list nat)
           (maxBits : nat) (ent : nat -> Code) : Prop :=
  forall i, 0 <= i < 2 ^ root ->
    exists sym cw,
      code_for lens maxBits sym = Some cw
      /\ Z.of_nat (length cw) <= root
      /\ T i = ent sym
      /\ c_bits (ent sym) = Z.of_nat (length cw)
      /\ firstn (length cw) (write_bits (Z.to_nat root) i) = cw.

(** Copy of ZReproQ6P.zr_len_ents (scratch), AMENDED with the negotiated
    pins: class 2 (+16=0, +64<>0), class 3 (+3<=b0, +joint 258 cap),
    class 4 (+16=0).  Re-point at landing. *)
Definition w3_len_ents (ll : list nat) (entl : nat -> Code) : Prop :=
  forall sym cw, code_for ll 15%nat sym = Some cw ->
    ((sym < 256)%nat /\ c_op (entl sym) = 0
       /\ c_val (entl sym) = Z.of_nat sym)
    \/ (sym = 256%nat /\ c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 <> 0
        /\ Z.land (c_op (entl sym)) 16 = 0
        /\ Z.land (c_op (entl sym)) 64 <> 0)
    \/ ((257 <= sym)%nat
        /\ exists b0 e0,
             nth_error length_base (sym - 257)%nat = Some b0
             /\ nth_error length_extra (sym - 257)%nat = Some e0
             /\ c_op (entl sym) = 16 + Z.of_nat e0
             /\ Z.land (c_op (entl sym)) 32 = 0
             /\ Z.land (c_op (entl sym)) 64 = 0
             /\ Z.land (c_op (entl sym)) 15 = Z.of_nat e0
             /\ c_val (entl sym) = Z.of_nat b0
             /\ (3 <= b0)%nat /\ (b0 <= 258)%nat /\ (e0 <= 5)%nat
             /\ (b0 + 2 ^ e0 - 1 <= 258)%nat)
    \/ (c_op (entl sym) <> 0
        /\ Z.land (c_op (entl sym)) 32 = 0
        /\ Z.land (c_op (entl sym)) 16 = 0
        /\ Z.land (c_op (entl sym)) 64 <> 0).

(** Copy of ZReproQ6P.zr_dist_ents (scratch), AMENDED: arm 2 (+16=0). *)
Definition w3_dist_ents (dl : list nat) (entd : nat -> Code) : Prop :=
  forall sym cw, code_for dl 15%nat sym = Some cw ->
    (exists b0 e0,
        nth_error dist_base sym = Some b0
        /\ nth_error dist_extra sym = Some e0
        /\ c_op (entd sym) = 16 + Z.of_nat e0
        /\ Z.land (c_op (entd sym)) 64 = 0
        /\ Z.land (c_op (entd sym)) 15 = Z.of_nat e0
        /\ c_val (entd sym) = Z.of_nat b0
        /\ 1 <= Z.of_nat b0 <= 32768 /\ (e0 <= 13)%nat)
    \/ (Z.land (c_op (entd sym)) 64 <> 0
        /\ Z.land (c_op (entd sym)) 16 = 0).

(* ==========================================================================
   2.  Small helpers.
   ========================================================================== *)

Lemma w3_u8_small : forall n, (n < 256)%nat -> u8 (Z.of_nat n) = Z.of_nat n.
Proof.
  intros n H. unfold u8. apply Z.mod_small. lia.
Qed.

(** [16 + x] for a nibble [x]: the dispatch masks. *)
Lemma w3_land16 : forall x, 0 <= x < 16 ->
  Z.land (16 + x) 16 = 16 /\ Z.land (16 + x) 15 = x
  /\ Z.land (16 + x) 64 = 0 /\ Z.land (16 + x) 32 = 0.
Proof.
  intros x H.
  assert (E : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6
              \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12
              \/ x = 13 \/ x = 14 \/ x = 15) by lia.
  repeat destruct E as [E|E]; subst; vm_compute;
    repeat split; congruence.
Qed.

Lemma w3_stream_put : forall c v s,
  if_stream c (if_put v s) = if_stream c s.
Proof. reflexivity. Qed.

Lemma w3_swf_put : forall v s, if_swf s -> if_swf (if_put v s).
Proof. intros v s H. exact H. Qed.

Lemma w3_haligned_put : forall c v s,
  if_haligned c s -> if_haligned c (if_put v s).
Proof. intros c v s H. exact H. Qed.

Lemma w3_drop_buf : forall n s, f_buf (if_drop n s) = f_buf s.
Proof. reflexivity. Qed.
Lemma w3_drop_out : forall n s, f_out (if_drop n s) = f_out s.
Proof. reflexivity. Qed.
Lemma w3_drop_in : forall n s, f_in (if_drop n s) = f_in s.
Proof. reflexivity. Qed.
Lemma w3_drop_bits : forall n s,
  0 <= f_bits s - n <= 4294967295 -> f_bits (if_drop n s) = f_bits s - n.
Proof.
  intros n s H. cbn [if_drop f_bits]. apply u32_id. lia.
Qed.

Lemma w3_stream_copyn : forall n c s r,
  if_stream c (fst (if_copyn n c s r)) = if_stream c s.
Proof.
  intros n c s r. unfold if_stream, if_bytes.
  rewrite (if_copyn_hold n c s r), (if_copyn_bits n c s r),
          (if_copyn_in n c s r).
  reflexivity.
Qed.

Lemma w3_swf_copyn : forall n c s r,
  if_swf s -> if_swf (fst (if_copyn n c s r)).
Proof.
  intros n c s r H. unfold if_swf in *.
  rewrite (if_copyn_hold n c s r), (if_copyn_bits n c s r). exact H.
Qed.

Lemma w3_haligned_copyn : forall n c s r,
  if_haligned c s -> if_haligned c (fst (if_copyn n c s r)).
Proof.
  intros n c s r H. unfold if_haligned in *.
  rewrite (if_copyn_hold n c s r), (if_copyn_bits n c s r),
          (if_copyn_in n c s r).
  exact H.
Qed.

(** Refill facts in case-explicit form for the load accounting. *)
Lemma w3_refill15_facts : forall c s,
  (f_bits s < 15 /\ f_in (if_refill15 c s) = f_in s + 2
     /\ f_bits (if_refill15 c s) = f_bits s + 16)
  \/ (15 <= f_bits s /\ if_refill15 c s = s).
Proof.
  intros c s. unfold if_refill15.
  destruct (Z.ltb_spec (f_bits s) 15) as [H|H].
  - left. cbn [if_load1 f_in f_bits]. repeat split; lia.
  - right. auto.
Qed.

(** Division atoms for the virtual-cursor accounting ([f_in - bits/8]
    is what [if_finish] returns to the input; W4 needs it monotone). *)
Lemma w3_div8_add : forall b k, (b + 8 * k) / 8 = b / 8 + k.
Proof.
  intros b k. rewrite Z.mul_comm, Z.div_add by lia. reflexivity.
Qed.

Lemma w3_div8_mono : forall a b, a <= b -> a / 8 <= b / 8.
Proof. intros a b H. apply Z.div_le_mono; lia. Qed.

(* ==========================================================================
   3.  The owned root read (Q6M's stop case; the pull loop does not
       arise — refill15 keeps the code buffered).
   ========================================================================== *)

Lemma w3_root_read :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code)
         (mask : Z) c s,
    ValidLengths lens 15%nat ->
    w3_root_own T root lens 15%nat ent ->
    0 < root <= 15 ->
    mask = Z.shiftl 1 root - 1 ->
    if_swf s -> root <= f_bits s ->
    exists sym cw,
      code_for lens 15%nat sym = Some cw
      /\ T (Z.land (f_hold s) mask) = ent sym
      /\ c_bits (ent sym) = Z.of_nat (length cw)
      /\ 1 <= Z.of_nat (length cw) <= root
      /\ hdecode (code_table lens 15%nat) (if_stream c s)
         = Some (sym, skipn (length cw) (if_stream c s)).
Proof.
  intros T root lens ent mask c s HV Hown Hroot Emask Hswf Hbits.
  pose proof Hswf as (Hb0 & Hh0 & Hh1).
  assert (Hrange : 0 <= Z.land (f_hold s) mask < 2 ^ root)
    by (rewrite Emask; apply land_ones_range; lia).
  destruct (Hown _ Hrange) as (sym & cw & Hcf & Hcwr & HTi & Hcb & Hpref).
  assert (Hlen1 : (1 <= length cw)%nat).
  { destruct (code_for_inv _ _ _ _ Hcf) as (len & _ & Hl1 & _ & Ecw).
    rewrite Ecw, code_bits_length. exact Hl1. }
  set (n := length cw) in *.
  exists sym, cw.
  split; [exact Hcf|].
  split; [exact HTi|].
  split; [exact Hcb|].
  split; [lia|].
  assert (Hlow : Z.land (f_hold s) mask = if_low root s)
    by (unfold if_low; rewrite Emask; reflexivity).
  assert (Hw : write_bits (Z.to_nat root) (Z.land (f_hold s) mask)
               = firstn (Z.to_nat root) (if_stream c s)).
  { rewrite Hlow. apply w2_low_spells_stream; [lia | exact Hh0]. }
  assert (Hfp : cw = firstn n (if_stream c s)).
  { rewrite <- Hpref, Hw.
    rewrite firstn_firstn.
    assert (Hmin : Nat.min n (Z.to_nat root) = n)
      by (apply Nat.min_l; lia).
    rewrite Hmin. reflexivity. }
  assert (Hsplit : if_stream c s = cw ++ skipn n (if_stream c s)).
  { rewrite Hfp. symmetry. apply firstn_skipn. }
  rewrite Hsplit at 1.
  exact (hdecode_complete nat Nat.eq_dec (code_table lens 15%nat) cw sym
           (skipn n (if_stream c s))
           (code_table_prefix_free lens 15%nat HV)
           (proj2 (code_table_In_iff lens 15%nat sym cw) Hcf)).
Qed.

(* ==========================================================================
   4.  The extra-bits blocks (equation-premise form).
   ========================================================================== *)

(** One conditional load ([if_dolen]'s length-extra shape), [0 < e <= 8]. *)
Lemma w3_extra1 :
  forall c s e sa,
    if_inb c -> if_swf s -> if_haligned c s ->
    0 < e <= 8 -> f_bits s <= 100 ->
    (f_bits s < e -> f_in s < f_last c + 5) ->
    sa = (if Z.ltb (f_bits s) e then if_load1 c s else s) ->
    read_bits (Z.to_nat e) (if_stream c s)
      = Some (if_low e sa, if_stream c (if_drop e sa))
    /\ if_stream c (if_drop e sa) = skipn (Z.to_nat e) (if_stream c s)
    /\ if_swf (if_drop e sa) /\ if_haligned c (if_drop e sa)
    /\ f_buf sa = f_buf s /\ f_out sa = f_out s
    /\ 0 <= if_low e sa < 2 ^ e
    /\ ((f_bits s < e /\ f_in (if_drop e sa) = f_in s + 1
          /\ f_bits (if_drop e sa) = f_bits s + 8 - e)
        \/ (e <= f_bits s /\ f_in (if_drop e sa) = f_in s
          /\ f_bits (if_drop e sa) = f_bits s - e)).
Proof.
  intros c s e sa Hin Hswf Hal He Hcap Hroom Esa.
  pose proof Hswf as (Hb0 & Hh0 & Hh1).
  assert (Hstep :
      if_stream c sa = if_stream c s /\ if_swf sa /\ if_haligned c sa
      /\ f_buf sa = f_buf s /\ f_out sa = f_out s
      /\ ((f_bits s < e /\ f_in sa = f_in s + 1 /\ f_bits sa = f_bits s + 8)
          \/ (e <= f_bits s /\ sa = s))).
  { rewrite Esa. destruct (Z.ltb_spec (f_bits s) e) as [H|H].
    - assert (Hr : f_in s < f_last c + 5) by (apply Hroom; lia).
      split; [apply w2_load1_stream; auto|].
      split; [apply w2_load1_swf; auto|].
      split; [apply w2_load1_haligned; auto|].
      split; [reflexivity|]. split; [reflexivity|].
      left. cbn [if_load1 f_in f_bits]. repeat split; lia.
    - repeat split; auto. }
  destruct Hstep as (Hstr & Hswa & Hala & Hbuf & Hout & Hcase).
  pose proof Hswa as (Hba0 & Hha0 & _).
  assert (Hea : e <= f_bits sa)
    by (destruct Hcase as [(?&?&E)|(?&E)]; [lia | rewrite E; lia]).
  assert (Hcapa : f_bits sa <= 4294967295)
    by (destruct Hcase as [(?&?&E)|(?&E)]; [lia | rewrite E; lia]).
  assert (Hlow : 0 <= if_low e sa < 2 ^ e).
  { unfold if_low. apply land_ones_range. lia. }
  assert (Hds : if_stream c (if_drop e sa)
                = skipn (Z.to_nat e) (if_stream c s)).
  { rewrite <- Hstr. apply w2_drop_stream; auto; lia. }
  split.
  { assert (Hw : write_bits (Z.to_nat e) (if_low e sa)
                 = firstn (Z.to_nat e) (if_stream c s)).
    { rewrite <- Hstr. apply w2_low_spells_stream; [lia | exact Hha0]. }
    rewrite <- (firstn_skipn (Z.to_nat e) (if_stream c s)) at 1.
    rewrite <- Hw, Hds.
    apply read_bits_write_bits.
    rewrite Z2Nat.id by lia. exact Hlow. }
  split; [exact Hds|].
  split; [apply w2_drop_swf; auto; lia|].
  split; [apply w2_drop_haligned; auto; lia|].
  split; [exact Hbuf|]. split; [exact Hout|].
  split; [exact Hlow|].
  destruct Hcase as [(H1&H2&H3)|(H1&E)].
  - left. split; [exact H1|].
    split; [rewrite w3_drop_in; exact H2|].
    rewrite w3_drop_bits by lia. lia.
  - right. split; [exact H1|].
    split; [rewrite w3_drop_in, E; reflexivity|].
    rewrite w3_drop_bits by (rewrite E; lia). rewrite E. lia.
Qed.

(** Two conditional loads ([if_dodist]'s dist-extra shape), [0 <= e <= 16]. *)
Lemma w3_extra2 :
  forall c s e sa,
    if_inb c -> if_swf s -> if_haligned c s ->
    0 <= e <= 16 -> f_bits s <= 100 ->
    (f_bits s < e -> f_in s < f_last c + 5) ->
    (f_bits s + 8 < e -> f_in s + 1 < f_last c + 5) ->
    sa = (if Z.ltb (f_bits s) e
          then (if Z.ltb (f_bits (if_load1 c s)) e
                then if_load1 c (if_load1 c s) else if_load1 c s)
          else s) ->
    read_bits (Z.to_nat e) (if_stream c s)
      = Some (if_low e sa, if_stream c (if_drop e sa))
    /\ if_stream c (if_drop e sa) = skipn (Z.to_nat e) (if_stream c s)
    /\ if_swf (if_drop e sa) /\ if_haligned c (if_drop e sa)
    /\ f_buf sa = f_buf s /\ f_out sa = f_out s
    /\ 0 <= if_low e sa < 2 ^ e
    /\ ((f_bits s < e /\ f_bits s + 8 < e
          /\ f_in (if_drop e sa) = f_in s + 2
          /\ f_bits (if_drop e sa) = f_bits s + 16 - e)
        \/ (f_bits s < e /\ e <= f_bits s + 8
          /\ f_in (if_drop e sa) = f_in s + 1
          /\ f_bits (if_drop e sa) = f_bits s + 8 - e)
        \/ (e <= f_bits s /\ f_in (if_drop e sa) = f_in s
          /\ f_bits (if_drop e sa) = f_bits s - e)).
Proof.
  intros c s e sa Hin Hswf Hal He Hcap Hroom1 Hroom2 Esa.
  pose proof Hswf as (Hb0 & Hh0 & Hh1).
  assert (Hb1 : f_bits (if_load1 c s) = f_bits s + 8) by reflexivity.
  assert (Hi1 : f_in (if_load1 c s) = f_in s + 1) by reflexivity.
  assert (Hstep :
      if_stream c sa = if_stream c s /\ if_swf sa /\ if_haligned c sa
      /\ f_buf sa = f_buf s /\ f_out sa = f_out s
      /\ ((f_bits s < e /\ f_bits s + 8 < e
            /\ f_in sa = f_in s + 2 /\ f_bits sa = f_bits s + 16)
          \/ (f_bits s < e /\ e <= f_bits s + 8
            /\ f_in sa = f_in s + 1 /\ f_bits sa = f_bits s + 8)
          \/ (e <= f_bits s /\ f_in sa = f_in s /\ f_bits sa = f_bits s))).
  { rewrite Esa. destruct (Z.ltb_spec (f_bits s) e) as [H|H].
    - assert (Hr : f_in s < f_last c + 5) by (apply Hroom1; lia).
      assert (Hs1 : if_swf (if_load1 c s)) by (apply w2_load1_swf; auto).
      assert (Ha1 : if_haligned c (if_load1 c s))
        by (apply w2_load1_haligned; auto).
      assert (Hst1 : if_stream c (if_load1 c s) = if_stream c s)
        by (apply w2_load1_stream; auto).
      destruct (Z.ltb_spec (f_bits (if_load1 c s)) e) as [H2|H2].
      + assert (Hr2 : f_in (if_load1 c s) < f_last c + 5)
          by (rewrite Hi1; apply Hroom2; lia).
        split.
        { rewrite (w2_load1_stream c (if_load1 c s) Hin Hs1 Hr2).
          exact Hst1. }
        split; [apply w2_load1_swf; auto|].
        split; [apply w2_load1_haligned; auto|].
        split; [reflexivity|]. split; [reflexivity|].
        left. cbn [if_load1 f_in f_bits].
        repeat split; lia.
      + split; [exact Hst1|]. split; [exact Hs1|]. split; [exact Ha1|].
        split; [reflexivity|]. split; [reflexivity|].
        right; left. repeat split; lia.
    - split; [reflexivity|]. split; [exact Hswf|]. split; [exact Hal|].
      split; [reflexivity|]. split; [reflexivity|].
      right; right. split; [lia|]. split; reflexivity. }
  destruct Hstep as (Hstr & Hswa & Hala & Hbuf & Hout & Hacc).
  pose proof Hswa as (Hba0 & Hha0 & _).
  assert (Hea : e <= f_bits sa)
    by (destruct Hacc as [(?&?&?&E)|[(?&?&?&E)|(?&?&E)]]; lia).
  assert (Hcapa : f_bits sa <= 4294967295)
    by (destruct Hacc as [(?&?&?&E)|[(?&?&?&E)|(?&?&E)]]; lia).
  assert (Hlow : 0 <= if_low e sa < 2 ^ e).
  { unfold if_low. apply land_ones_range. lia. }
  assert (Hds : if_stream c (if_drop e sa)
                = skipn (Z.to_nat e) (if_stream c s)).
  { rewrite <- Hstr. apply w2_drop_stream; auto; lia. }
  split.
  { assert (Hw : write_bits (Z.to_nat e) (if_low e sa)
                 = firstn (Z.to_nat e) (if_stream c s)).
    { rewrite <- Hstr. apply w2_low_spells_stream; [lia | exact Hha0]. }
    rewrite <- (firstn_skipn (Z.to_nat e) (if_stream c s)) at 1.
    rewrite <- Hw, Hds.
    apply read_bits_write_bits.
    rewrite Z2Nat.id by lia. exact Hlow. }
  split; [exact Hds|].
  split; [apply w2_drop_swf; auto; lia|].
  split; [apply w2_drop_haligned; auto; lia|].
  split; [exact Hbuf|]. split; [exact Hout|].
  split; [exact Hlow|].
  destruct Hacc as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]].
  - left. split; [exact A1|]. split; [exact A2|].
    split; [rewrite w3_drop_in; exact A3|].
    rewrite w3_drop_bits by lia. lia.
  - right; left. split; [exact A1|]. split; [exact A2|].
    split; [rewrite w3_drop_in; exact A3|].
    rewrite w3_drop_bits by lia. lia.
  - right; right. split; [exact A1|].
    split; [rewrite w3_drop_in; exact A2|].
    rewrite w3_drop_bits by lia. lia.
Qed.

(* ==========================================================================
   5.  One-step unfold equations (the goal-side discipline: the chain
       arm stays folded).
   ========================================================================== *)

Lemma if_dolen_S : forall k c s h,
  if_dolen (S k) c s h =
    (let s1 := if_drop (c_bits h) s in
     let op := c_op h in
     if Z.eqb op 0 then
       BodyOk (if_put (u8 (c_val h)) s1)
     else if negb (Z.eqb (Z.land op 16) 0) then
       let e := Z.land op 15 in
       let '(len, s2) :=
         if Z.eqb e 0 then (c_val h, s1)
         else let sa := if Z.ltb (f_bits s1) e then if_load1 c s1 else s1 in
              (c_val h + if_low e sa, if_drop e sa) in
       let s3 := if_refill15 c s2 in
       if_dodist tbl_fuel c len s3 (f_dcode c (Z.land (f_hold s3) (f_dmask c)))
     else if Z.eqb (Z.land op 64) 0 then
       if_dolen k c s1 (f_lcode c (c_val h + if_low op s1))
     else if negb (Z.eqb (Z.land op 32) 0) then
       BodyEob s1
     else
       BodyBad s1 MSG_LIT_LEN_CODE).
Proof. reflexivity. Qed.

Lemma if_dodist_S : forall k c len s h,
  if_dodist (S k) c len s h =
    (let s1 := if_drop (c_bits h) s in
     let op := c_op h in
     if negb (Z.eqb (Z.land op 16) 0) then
       let e := Z.land op 15 in
       let s2 := if Z.ltb (f_bits s1) e
                 then let sa := if_load1 c s1 in
                      if Z.ltb (f_bits sa) e then if_load1 c sa else sa
                 else s1 in
       let dist := c_val h + if_low e s2 in
       let s3 := if_drop e s2 in
       let od := u32 (f_out s3 - f_beg c) in
       if Z.ltb od dist then
         let ow := u32 (dist - od) in
         if Z.ltb (f_whave c) ow && negb (Z.eqb (f_sane c) 0) then
           BodyBad s3 MSG_DIST_FAR
         else
           let '(s4, r4, len4) := if_winphase c s3 dist ow len in
           match if_copy3w copy_fuel c s4 r4 len4 with
           | None => BodyFuel
           | Some (s5, r5, l5) => BodyOk (if_copytail c s5 r5 l5)
           end
       else
         match if_copydirect c s3 (SrcOut (f_out s3 - dist)) len with
         | None => BodyFuel
         | Some s5 => BodyOk s5
         end
     else if Z.eqb (Z.land op 64) 0 then
       if_dodist k c len s1 (f_dcode c (c_val h + if_low op s1))
     else
       BodyBad s1 MSG_DIST_CODE).
Proof. reflexivity. Qed.

(* ==========================================================================
   6.  The distance tail: refill + dist root read + dist extra + copy,
       classified against the spec's dist half.  [BodyEob] cannot arise.
   ========================================================================== *)

Lemma w3_dist_tail :
  forall c (s2 : IfSt) (rootD : Z) (dl : list nat) (entd : nat -> Code)
         (len : Z) (len_spec : nat) (k : nat),
    ValidLengths dl 15%nat ->
    w3_root_own (f_dcode c) rootD dl 15%nat entd ->
    w3_dist_ents dl entd ->
    0 < rootD <= 15 ->
    f_dmask c = Z.shiftl 1 rootD - 1 ->
    f_whave c = 0 -> f_sane c <> 0 -> if_inb c ->
    if_swf s2 -> if_haligned c s2 -> f_bits s2 <= 60 ->
    f_in s2 + 3 <= f_last c + 5 ->
    (f_bits s2 < 4 -> f_in s2 + 4 <= f_last c + 5) ->
    0 <= f_beg c <= f_out s2 -> f_out s2 <= 4294967295 ->
    len = Z.of_nat len_spec ->
    (3 <= len_spec)%nat -> (len_spec <= 258)%nat ->
    match if_dodist (S k) c len (if_refill15 c s2)
            (f_dcode c (Z.land (f_hold (if_refill15 c s2)) (f_dmask c)))
    with
    | BodyOk s' =>
        exists (dsym : nat) (dist_spec : nat) (r3 r4 : list bool),
          hdecode (code_table dl 15%nat) (if_stream c s2) = Some (dsym, r3)
          /\ read_extra dist_base dist_extra dsym r3 = Some (dist_spec, r4)
          /\ if_stream c s' = r4
          /\ (1 <= dist_spec)%nat
          /\ Z.of_nat dist_spec <= f_out s2
          /\ zslice (f_buf s') 0 (f_out s')
             = zslice (f_buf s2) 0 (f_out s2)
               ++ lz_copy (zslice (f_buf s2) 0 (f_out s2)) len_spec dist_spec
          /\ f_out s' = f_out s2 + len
          /\ if_swf s' /\ if_haligned c s' /\ f_bits s' <= 60
          /\ f_in s2 <= f_in s'
          /\ f_in s' <= f_last c + 5
          /\ f_in s2 - f_bits s2 / 8 <= f_in s' - f_bits s' / 8
    | BodyEob _ => False
    | BodyBad _ _ => True
    | BodyFuel => True
    end.
Proof.
  intros c s2 rootD dl entd len len_spec k HVd HownD Hde HrD EmD Hwh Hsn
         Hinb Hsw2 Hal2 Hcap2 Hrm3 Hrm4 Hbeg Hocap Elen Hl3 Hl258.
  pose proof Hsw2 as (Hb2 & Hh2 & _).
  set (s3 := if_refill15 c s2).
  assert (Hst3 : if_stream c s3 = if_stream c s2)
    by (apply w2_refill15_stream; auto; lia).
  assert (Hsw3 : if_swf s3) by (apply w2_refill15_swf; auto).
  pose proof Hsw3 as (Hb3 & Hh3 & _).
  assert (Hal3 : if_haligned c s3) by (apply w2_refill15_haligned; auto).
  assert (Hb15 : 15 <= f_bits s3) by (apply w2_refill15_bits; auto).
  assert (Hbuf3 : f_buf s3 = f_buf s2) by apply w2_refill15_buf.
  assert (Hout3 : f_out s3 = f_out s2) by apply w2_refill15_out.
  pose proof (w3_refill15_facts c s2) as Hrf2. fold s3 in Hrf2.
  assert (Hcap3 : f_bits s3 <= 60)
    by (destruct Hrf2 as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]).
  destruct (w3_root_read (f_dcode c) rootD dl entd (f_dmask c) c s3
              HVd HownD HrD EmD Hsw3 ltac:(lia))
    as (dsym & cwD & HcfD & HTD & HcbD & HlenD & HhdD).
  rewrite Hst3 in HhdD.
  rewrite if_dodist_S. cbv zeta.
  rewrite HTD, HcbD.
  set (s1' := if_drop (Z.of_nat (length cwD)) s3).
  assert (Hds1 : if_stream c s1' = skipn (length cwD) (if_stream c s2)).
  { unfold s1'.
    rewrite (w2_drop_stream (Z.of_nat (length cwD)) c s3)
      by (auto; lia).
    rewrite Hst3, Nat2Z.id. reflexivity. }
  assert (Hsw1' : if_swf s1')
    by (apply w2_drop_swf; auto; lia).
  pose proof Hsw1' as (Hb1' & Hh1' & _).
  assert (Hal1' : if_haligned c s1')
    by (apply w2_drop_haligned; auto; lia).
  assert (Hbuf1' : f_buf s1' = f_buf s2)
    by (unfold s1'; rewrite w3_drop_buf; exact Hbuf3).
  assert (Hout1' : f_out s1' = f_out s2)
    by (unfold s1'; rewrite w3_drop_out; exact Hout3).
  assert (Hin1' : f_in s1' = f_in s3) by apply w3_drop_in.
  assert (Hbits1' : f_bits s1' = f_bits s3 - Z.of_nat (length cwD))
    by (apply w3_drop_bits; lia).
  destruct (Hde _ _ HcfD) as
    [ (b0' & e0' & Hnb' & Hne' & Hop' & H64' & H15' & Hval' & Hb1d & He13')
    | (H64d & H16d) ].
  2:{ assert (E16 : (Z.land (c_op (entd dsym)) 16 =? 0) = true)
        by (apply Z.eqb_eq; exact H16d).
      rewrite E16. cbn [negb].
      assert (E64 : (Z.land (c_op (entd dsym)) 64 =? 0) = false)
        by (apply Z.eqb_neq; exact H64d).
      rewrite E64.
      cbv iota. exact I. }
  pose proof (w3_land16 (Z.of_nat e0') ltac:(lia)) as (L16' & _ & _ & _).
  assert (E16 : (Z.land (c_op (entd dsym)) 16 =? 0) = false)
    by (rewrite Hop', L16'; reflexivity).
  rewrite E16. cbn [negb].
  rewrite H15'.
  set (sa2 := if Z.ltb (f_bits s1') (Z.of_nat e0')
              then (if Z.ltb (f_bits (if_load1 c s1')) (Z.of_nat e0')
                    then if_load1 c (if_load1 c s1') else if_load1 c s1')
              else s1').
  assert (Hroom1 : f_bits s1' < Z.of_nat e0' -> f_in s1' < f_last c + 5).
  { intros _. rewrite Hin1'.
    destruct Hrf2 as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]. }
  assert (Hroom2 : f_bits s1' + 8 < Z.of_nat e0' ->
                   f_in s1' + 1 < f_last c + 5).
  { intros Hb. rewrite Hin1'.
    destruct Hrf2 as [(A&B&C)|(A&E)].
    - assert (f_bits s2 < 4) by lia.
      pose proof (Hrm4 ltac:(assumption)). lia.
    - rewrite E. lia. }
  destruct (w3_extra2 c s1' (Z.of_nat e0') sa2 Hinb Hsw1' Hal1'
              ltac:(lia) ltac:(lia) Hroom1 Hroom2 eq_refl)
    as (Hrb2 & Hds2 & Hsw3' & Hal3' & Hbufa2 & Houta2 & Hlow2 & Hacc2).
  set (s3' := if_drop (Z.of_nat e0') sa2).
  fold s3' in Hrb2, Hds2, Hsw3', Hal3', Hacc2.
  pose proof Hsw3' as (Hb3' & Hh3' & _).
  assert (Hbuf3' : f_buf s3' = f_buf s2)
    by (unfold s3'; rewrite w3_drop_buf; rewrite Hbufa2; exact Hbuf1').
  assert (Hout3' : f_out s3' = f_out s2)
    by (unfold s3'; rewrite w3_drop_out; rewrite Houta2; exact Hout1').
  assert (Hbits3' : f_bits s3' <= 60)
    by (destruct Hacc2 as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]]; lia).
  assert (Hin3' : f_in s2 <= f_in s3').
  { assert (f_in s2 <= f_in s1')
      by (rewrite Hin1';
          destruct Hrf2 as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]).
    destruct Hacc2 as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]]; lia. }
  set (v' := if_low (Z.of_nat e0') sa2) in *.
  assert (Hpow13 : 2 ^ Z.of_nat e0' <= 8192).
  { replace 8192 with (2 ^ 13) by reflexivity.
    apply Z.pow_le_mono_r; lia. }
  set (dist_spec := (b0' + Z.to_nat v')%nat).
  assert (Edist : c_val (entd dsym) + v' = Z.of_nat dist_spec).
  { unfold dist_spec. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    rewrite Hval'. reflexivity. }
  assert (Eod : u32 (f_out s3' - f_beg c) = f_out s2 - f_beg c)
    by (rewrite Hout3'; apply u32_id; lia).
  rewrite Eod.
  destruct (Z.ltb_spec (f_out s2 - f_beg c) (c_val (entd dsym) + v'))
    as [Hlt | Hge].
  - (* window arm: whave = 0 forces BAD before any window read *)
    rewrite Hwh.
    assert (Eow : (0 <? u32 (c_val (entd dsym) + v'
                             - (f_out s2 - f_beg c))) = true).
    { apply Z.ltb_lt. apply u32_pos. rewrite Hval'. lia. }
    rewrite Eow.
    assert (Esn : (f_sane c =? 0) = false) by (apply Z.eqb_neq; exact Hsn).
    rewrite Esn. cbn [negb andb].
    cbv iota. exact I.
  - (* direct copy *)
    rewrite if_copydirect_flat by lia.
    cbv iota.
    exists dsym, dist_spec, (skipn (length cwD) (if_stream c s2)),
           (if_stream c s3').
    split; [exact HhdD|].
    split.
    { unfold read_extra. rewrite Hnb', Hne'.
      rewrite Nat2Z.id in Hrb2.
      rewrite Hds1 in Hrb2.
      rewrite Hrb2. reflexivity. }
    split.
    { rewrite w3_stream_copyn. reflexivity. }
    split; [unfold dist_spec; lia|].
    split; [rewrite <- Edist, Hval'; lia|].
    split.
    { rewrite Edist.
      replace (Z.to_nat len) with len_spec by lia.
      rewrite <- Hbuf3', <- Hout3'.
      rewrite if_copyn_out.
      rewrite (if_copyn_lz len_spec dist_spec c s3')
        by (rewrite Hout3'; rewrite <- Edist, Hval'; lia).
      reflexivity. }
    split.
    { rewrite if_copyn_out, Hout3'. lia. }
    split; [apply w3_swf_copyn; exact Hsw3'|].
    split; [apply w3_haligned_copyn; exact Hal3'|].
    assert (HinA : f_in s3 = f_in s2 + 2 /\ f_bits s3 = f_bits s2 + 16
                   \/ f_in s3 = f_in s2 /\ f_bits s3 = f_bits s2).
    { destruct Hrf2 as [(B1&B2&B3)|(B1&B2)];
        [ left; auto
        | right; rewrite B2; auto ]. }
    split.
    { unfold if_swf in Hsw3'.
      rewrite (if_copyn_bits (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      exact Hbits3'. }
    split.
    { rewrite (if_copyn_in (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      exact Hin3'. }
    split.
    { (* the cursor stays inside the input window *)
      rewrite (if_copyn_in (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      destruct Hacc2 as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]];
        destruct HinA as [(C1&C2)|(C1&C2)];
        try lia;
        (* two loads fired AND the refill fired: bits s2 < 4 fires Hrm4 *)
        assert (Hb4 : f_bits s2 < 4) by lia;
        pose proof (Hrm4 Hb4); lia. }
    { (* the virtual byte cursor [f_in - bits/8] is monotone *)
      rewrite (if_copyn_in (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))),
              (if_copyn_bits (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      assert (HV23 : f_in s2 - f_bits s2 / 8 <= f_in s3 - f_bits s3 / 8).
      { destruct HinA as [(C1&C2)|(C1&C2)]; rewrite C1, C2;
          [ replace (f_bits s2 + 16) with (f_bits s2 + 8 * 2) by ring;
            rewrite w3_div8_add; lia
          | lia ]. }
      assert (HV31 : f_in s3 - f_bits s3 / 8 <= f_in s1' - f_bits s1' / 8).
      { rewrite Hin1', Hbits1'.
        pose proof (w3_div8_mono (f_bits s3 - Z.of_nat (length cwD))
                      (f_bits s3) ltac:(lia)).
        lia. }
      assert (HV13 : f_in s1' - f_bits s1' / 8 <= f_in s3' - f_bits s3' / 8).
      { destruct Hacc2 as [(A1&A2&A3&A4)|[(A1&A2&A3&A4)|(A1&A2&A3)]].
        - rewrite A3, A4.
          pose proof (w3_div8_mono (f_bits s1' + 16 - Z.of_nat e0')
                        (f_bits s1' + 16) ltac:(lia)) as M1.
          assert (E1 : (f_bits s1' + 16) / 8 = f_bits s1' / 8 + 2)
            by (replace (f_bits s1' + 16) with (f_bits s1' + 8 * 2) by ring;
                apply w3_div8_add).
          lia.
        - rewrite A3, A4.
          pose proof (w3_div8_mono (f_bits s1' + 8 - Z.of_nat e0')
                        (f_bits s1' + 8) ltac:(lia)) as M1.
          assert (E1 : (f_bits s1' + 8) / 8 = f_bits s1' / 8 + 1)
            by (replace (f_bits s1' + 8) with (f_bits s1' + 8 * 1) by ring;
                apply w3_div8_add).
          lia.
        - rewrite A2, A3.
          pose proof (w3_div8_mono (f_bits s1' - Z.of_nat e0')
                        (f_bits s1') ltac:(lia)) as M1.
          lia. }
      lia. }
Qed.

(* ==========================================================================
   7.  THE TRIP: one [if_body] at an owned root read IS one
       [decode_lit_len] step with the [resolve_lz] slice threading.
   ========================================================================== *)

Definition w3_post (c : IfCtx) (s s' : IfSt) : Prop :=
  if_swf s' /\ if_haligned c s' /\ f_bits s' <= 60
  /\ f_in s <= f_in s' /\ f_out s <= f_out s'
  /\ f_in s' <= f_last c + 5
  /\ f_in s - f_bits s / 8 <= f_in s' - f_bits s' / 8
  /\ f_out s' <= f_out s + 258.

Lemma w3_trip :
  forall c s (rootL rootD : Z) (ll dl : list nat) (entl entd : nat -> Code),
    ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
    w3_root_own (f_lcode c) rootL ll 15%nat entl ->
    w3_root_own (f_dcode c) rootD dl 15%nat entd ->
    w3_len_ents ll entl -> w3_dist_ents dl entd ->
    0 < rootL <= 15 -> 0 < rootD <= 15 ->
    f_lmask c = Z.shiftl 1 rootL - 1 ->
    f_dmask c = Z.shiftl 1 rootD - 1 ->
    f_whave c = 0 -> f_sane c <> 0 ->
    if_inb c -> if_swf s -> if_haligned c s ->
    f_bits s <= 60 ->
    f_in s + 6 <= f_last c + 5 ->
    0 <= f_beg c <= f_out s ->
    f_out s <= 4294967295 ->
    match if_body c s with
    | BodyOk s' =>
        exists sy rest,
          decode_lit_len ll dl (if_stream c s) = Some (sy, rest)
          /\ sy <> LzEnd
          /\ if_stream c s' = rest
          /\ resolve_lz [sy] (zslice (f_buf s) 0 (f_out s))
             = Some (zslice (f_buf s') 0 (f_out s'))
          /\ w3_post c s s'
    | BodyEob s' =>
        decode_lit_len ll dl (if_stream c s) = Some (LzEnd, if_stream c s')
        /\ f_out s' = f_out s /\ f_buf s' = f_buf s
        /\ w3_post c s s'
    | BodyBad s' m => True
    | BodyFuel => True
    end.
Proof.
  intros c s rootL rootD ll dl entl entd HVl HVd HownL HownD Hle Hde
         HrL HrD EmL EmD Hwh Hsn Hinb Hswf Hal Hcap Hroom Hbeg Hocap.
  pose proof Hswf as (Hb0s & Hh0s & _).
  unfold if_body. cbv zeta.
  set (s0 := if_refill15 c s).
  assert (Hst0 : if_stream c s0 = if_stream c s)
    by (apply w2_refill15_stream; auto; lia).
  assert (Hsw0 : if_swf s0) by (apply w2_refill15_swf; auto).
  pose proof Hsw0 as (Hb0 & Hh0 & _).
  assert (Hal0 : if_haligned c s0) by (apply w2_refill15_haligned; auto).
  assert (Hb15 : 15 <= f_bits s0) by (apply w2_refill15_bits; auto).
  assert (Hbuf0 : f_buf s0 = f_buf s) by apply w2_refill15_buf.
  assert (Hout0 : f_out s0 = f_out s) by apply w2_refill15_out.
  pose proof (w3_refill15_facts c s) as Hrf. fold s0 in Hrf.
  assert (Hcap0 : f_bits s0 <= 60)
    by (destruct Hrf as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]).
  assert (Hin0 : f_in s <= f_in s0 <= f_in s + 2)
    by (destruct Hrf as [(A&B&C)|(A&E)]; [lia | rewrite E; lia]).
  destruct (w3_root_read (f_lcode c) rootL ll entl (f_lmask c) c s0
              HVl HownL HrL EmL Hsw0 ltac:(lia))
    as (symL & cwL & HcfL & HTL & HcbL & HlenL & HhdL).
  rewrite Hst0 in HhdL.
  change tbl_fuel with (S 15).
  rewrite if_dolen_S. cbv zeta.
  rewrite HTL, HcbL.
  set (s1 := if_drop (Z.of_nat (length cwL)) s0).
  assert (Er1 : if_stream c s1 = skipn (length cwL) (if_stream c s)).
  { unfold s1.
    rewrite (w2_drop_stream (Z.of_nat (length cwL)) c s0) by (auto; lia).
    rewrite Hst0, Nat2Z.id. reflexivity. }
  assert (Hsw1 : if_swf s1) by (apply w2_drop_swf; auto; lia).
  pose proof Hsw1 as (Hb1 & Hh1 & _).
  assert (Hal1 : if_haligned c s1) by (apply w2_drop_haligned; auto; lia).
  assert (Hbuf1 : f_buf s1 = f_buf s)
    by (unfold s1; rewrite w3_drop_buf; exact Hbuf0).
  assert (Hout1 : f_out s1 = f_out s)
    by (unfold s1; rewrite w3_drop_out; exact Hout0).
  assert (Hin1 : f_in s1 = f_in s0) by apply w3_drop_in.
  assert (Hbits1 : f_bits s1 = f_bits s0 - Z.of_nat (length cwL))
    by (apply w3_drop_bits; lia).
  destruct (Hle _ _ HcfL) as
    [ (Hsym & Hop0 & Hval)
    | [ (Esym & Hopn & H32e & H16e & H64e)
    | [ (Hsym257 & b0 & e0 & Hnb & Hne & Hop3 & H32l & H64l & H15l & Hval
         & Hb3 & Hb258 & He5 & Hjoint)
    | (Hopn & H32i & H16i & H64i) ] ] ].
  - (* class 1: literal *)
    rewrite Hop0.
    change (0 =? 0) with true. cbv iota.
    exists (LzLit (Z.of_nat symL)), (skipn (length cwL) (if_stream c s)).
    split.
    { unfold decode_lit_len. rewrite HhdL.
      rewrite (proj2 (Nat.ltb_lt symL 256) Hsym).
      reflexivity. }
    split; [discriminate|].
    split.
    { rewrite w3_stream_put. exact Er1. }
    split.
    { assert (Ev : u8 (c_val (entl symL)) = Z.of_nat symL)
        by (rewrite Hval; apply w3_u8_small; exact Hsym).
      rewrite Ev.
      cbn [resolve_lz].
      rewrite if_put_out.
      rewrite if_put_slice by lia.
      rewrite Hbuf1, Hout1.
      reflexivity. }
    split; [apply w3_swf_put; exact Hsw1|].
    split; [apply w3_haligned_put; exact Hal1|].
    split.
    { cbn [if_put f_bits]. lia. }
    split.
    { cbn [if_put f_in]. lia. }
    split.
    { rewrite if_put_out, Hout1. lia. }
    split.
    { cbn [if_put f_in]. lia. }
    split.
    { cbn [if_put f_in f_bits].
      assert (HV0 : f_in s - f_bits s / 8 <= f_in s0 - f_bits s0 / 8).
      { destruct Hrf as [(B1&B2&B3)|(B1&B2)];
          [ rewrite B2, B3;
            replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
            rewrite w3_div8_add; lia
          | rewrite B2; lia ]. }
      assert (HV1 : f_in s0 - f_bits s0 / 8 <= f_in s1 - f_bits s1 / 8).
      { rewrite Hin1, Hbits1.
        pose proof (w3_div8_mono (f_bits s0 - Z.of_nat (length cwL))
                      (f_bits s0) ltac:(lia)).
        lia. }
      lia. }
    { rewrite if_put_out, Hout1. lia. }
  - (* class 2: end of block *)
    assert (E0 : (c_op (entl symL) =? 0) = false)
      by (apply Z.eqb_neq; exact Hopn).
    rewrite E0.
    assert (E16 : (Z.land (c_op (entl symL)) 16 =? 0) = true)
      by (apply Z.eqb_eq; exact H16e).
    rewrite E16. cbn [negb].
    assert (E64 : (Z.land (c_op (entl symL)) 64 =? 0) = false)
      by (apply Z.eqb_neq; exact H64e).
    rewrite E64.
    assert (E32 : (Z.land (c_op (entl symL)) 32 =? 0) = false)
      by (apply Z.eqb_neq; exact H32e).
    rewrite E32. cbn [negb]. cbv iota.
    split.
    { unfold decode_lit_len. rewrite HhdL.
      subst symL.
      change (256 <? 256)%nat with false.
      change (256 =? 256)%nat with true.
      rewrite Er1. reflexivity. }
    split; [exact Hout1|].
    split; [exact Hbuf1|].
    split; [exact Hsw1|].
    split; [exact Hal1|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split; [lia|].
    split.
    { assert (HV0 : f_in s - f_bits s / 8 <= f_in s0 - f_bits s0 / 8).
      { destruct Hrf as [(B1&B2&B3)|(B1&B2)];
          [ rewrite B2, B3;
            replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
            rewrite w3_div8_add; lia
          | rewrite B2; lia ]. }
      assert (HV1 : f_in s0 - f_bits s0 / 8 <= f_in s1 - f_bits s1 / 8).
      { rewrite Hin1, Hbits1.
        pose proof (w3_div8_mono (f_bits s0 - Z.of_nat (length cwL))
                      (f_bits s0) ltac:(lia)).
        lia. }
      lia. }
    lia.
  - (* class 3: length/distance pair *)
    rewrite Hop3.
    pose proof (w3_land16 (Z.of_nat e0) ltac:(lia)) as (L16 & L15 & L64 & L32).
    assert (E0 : (16 + Z.of_nat e0 =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite E0.
    assert (E16 : (Z.land (16 + Z.of_nat e0) 16 =? 0) = false)
      by (rewrite L16; reflexivity).
    rewrite E16. cbn [negb].
    rewrite L15.
    destruct (Z.eqb_spec (Z.of_nat e0) 0) as [Ee|Ee].
    + (* no extra bits *)
      cbv iota.
      assert (Ee0 : e0 = 0%nat) by lia.
      subst e0.
      set (len_spec := b0).
      assert (Hre : read_extra length_base length_extra (symL - 257)%nat
                      (skipn (length cwL) (if_stream c s))
                    = Some (len_spec, if_stream c s1)).
      { unfold read_extra. rewrite Hnb, Hne.
        cbn [read_bits].
        rewrite Er1.
        unfold len_spec. rewrite Nat.add_0_r. reflexivity. }
      assert (Elen : c_val (entl symL) = Z.of_nat len_spec)
        by (unfold len_spec; exact Hval).
      change tbl_fuel with (S 15).
      pose proof (w3_dist_tail c s1 rootD dl entd (c_val (entl symL))
                    len_spec 15 HVd HownD Hde HrD EmD Hwh Hsn Hinb
                    Hsw1 Hal1 ltac:(lia)
                    ltac:(lia) ltac:(intros _; lia)
                    ltac:(lia) ltac:(lia)
                    Elen ltac:(unfold len_spec; lia)
                    ltac:(unfold len_spec; lia)) as Htail.
      match goal with
      | |- match ?X with _ => _ end => destruct X as [s5|s5|s5 m|]
      end; [| destruct Htail | exact I | exact I].
      destruct Htail as (dsym & dist_spec & r3 & r4 & Hhd2 & Hre2 & Hstr5
                         & Hd1 & Hdle & Hslice & Hout5 & Hsw5 & Hal5
                         & Hbits5 & Hin5 & Hin5cap & Hv5).
      exists (LzRef len_spec dist_spec), r4.
      split.
      { unfold decode_lit_len. rewrite HhdL.
        rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
        rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
        rewrite Hre, Hhd2, Hre2. reflexivity. }
      split; [discriminate|].
      split; [exact Hstr5|].
      split.
      { cbn [resolve_lz].
        assert (Ez : (dist_spec =? 0)%nat = false)
          by (apply Nat.eqb_neq; lia).
        assert (El : (length (zslice (f_buf s) 0 (f_out s)) <? dist_spec)%nat
                     = false).
        { apply Nat.ltb_ge. rewrite zslice_length. lia. }
        rewrite Ez, El. cbn [orb].
        rewrite Hbuf1, Hout1 in Hslice.
        rewrite Hslice. reflexivity. }
      split; [exact Hsw5|].
      split; [exact Hal5|].
      split; [exact Hbits5|].
      split; [lia|].
      split.
      { rewrite Hout5, Hout1. unfold len_spec. lia. }
      split; [exact Hin5cap|].
      split.
      { assert (HV0 : f_in s - f_bits s / 8 <= f_in s0 - f_bits s0 / 8).
        { destruct Hrf as [(B1&B2&B3)|(B1&B2)];
            [ rewrite B2, B3;
              replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
              rewrite w3_div8_add; lia
            | rewrite B2; lia ]. }
        assert (HV1 : f_in s0 - f_bits s0 / 8 <= f_in s1 - f_bits s1 / 8).
        { rewrite Hin1, Hbits1.
          pose proof (w3_div8_mono (f_bits s0 - Z.of_nat (length cwL))
                        (f_bits s0) ltac:(lia)).
          lia. }
        lia. }
      rewrite Hout5, Hout1. unfold len_spec. lia.
    + (* extra bits *)
      cbv iota.
      set (sa := if Z.ltb (f_bits s1) (Z.of_nat e0)
                 then if_load1 c s1 else s1).
      destruct (w3_extra1 c s1 (Z.of_nat e0) sa Hinb Hsw1 Hal1
                  ltac:(lia) ltac:(lia) ltac:(intros _; lia) eq_refl)
        as (Hrb1 & Hds1 & Hsw2 & Hal2 & Hbufa & Houta & Hlow1 & Hacc1).
      set (s2 := if_drop (Z.of_nat e0) sa).
      fold s2 in Hrb1, Hds1, Hsw2, Hal2, Hacc1.
      assert (Hbuf2 : f_buf s2 = f_buf s)
        by (unfold s2; rewrite w3_drop_buf; rewrite Hbufa; exact Hbuf1).
      assert (Hout2 : f_out s2 = f_out s)
        by (unfold s2; rewrite w3_drop_out; rewrite Houta; exact Hout1).
      set (v := if_low (Z.of_nat e0) sa) in *.
      set (len_spec := (b0 + Z.to_nat v)%nat).
      assert (Hpow5 : 2 ^ Z.of_nat e0 <= 32).
      { replace 32 with (2 ^ 5) by reflexivity.
        apply Z.pow_le_mono_r; lia. }
      assert (Elen : c_val (entl symL) + v = Z.of_nat len_spec).
      { unfold len_spec. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
        rewrite Hval. reflexivity. }
      assert (Hjz : Z.of_nat b0 + 2 ^ Z.of_nat e0 - 1 <= 258).
      { replace (2 ^ Z.of_nat e0) with (Z.of_nat (2 ^ e0))
          by (rewrite Nat2Z.inj_pow; reflexivity).
        lia. }
      assert (Hre : read_extra length_base length_extra (symL - 257)%nat
                      (skipn (length cwL) (if_stream c s))
                    = Some (len_spec, if_stream c s2)).
      { unfold read_extra. rewrite Hnb, Hne.
        rewrite Nat2Z.id in Hrb1.
        rewrite Er1 in Hrb1.
        rewrite Hrb1. reflexivity. }
      assert (Hcap2 : f_bits s2 <= 60)
        by (destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)]; lia).
      assert (Hrm3 : f_in s2 + 3 <= f_last c + 5)
        by (destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)]; lia).
      assert (Hrm4 : f_bits s2 < 4 -> f_in s2 + 4 <= f_last c + 5).
      { intros Hb4.
        destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)];
          destruct Hrf as [(B1&B2&B3)|(B1&B2)];
          try lia.
        rewrite B2 in *. lia. }
      change tbl_fuel with (S 15).
      pose proof (w3_dist_tail c s2 rootD dl entd
                    (c_val (entl symL) + v) len_spec 15
                    HVd HownD Hde HrD EmD Hwh Hsn Hinb
                    Hsw2 Hal2 Hcap2 Hrm3 Hrm4
                    ltac:(lia) ltac:(lia)
                    Elen ltac:(unfold len_spec; lia)
                    ltac:(unfold len_spec; lia)) as Htail.
      match goal with
      | |- match ?X with _ => _ end => destruct X as [s5|s5|s5 m|]
      end; [| destruct Htail | exact I | exact I].
      destruct Htail as (dsym & dist_spec & r3 & r4 & Hhd2 & Hre2 & Hstr5
                         & Hd1 & Hdle & Hslice & Hout5 & Hsw5 & Hal5
                         & Hbits5 & Hin5 & Hin5cap & Hv5).
      exists (LzRef len_spec dist_spec), r4.
      split.
      { unfold decode_lit_len. rewrite HhdL.
        rewrite (proj2 (Nat.ltb_ge symL 256) ltac:(lia)).
        rewrite (proj2 (Nat.eqb_neq symL 256) ltac:(lia)).
        rewrite Hre, Hhd2, Hre2. reflexivity. }
      split; [discriminate|].
      split; [exact Hstr5|].
      split.
      { cbn [resolve_lz].
        assert (Ez : (dist_spec =? 0)%nat = false)
          by (apply Nat.eqb_neq; lia).
        assert (El : (length (zslice (f_buf s) 0 (f_out s)) <? dist_spec)%nat
                     = false).
        { apply Nat.ltb_ge. rewrite zslice_length. lia. }
        rewrite Ez, El. cbn [orb].
        rewrite Hbuf2, Hout2 in Hslice.
        rewrite Hslice. reflexivity. }
      split; [exact Hsw5|].
      split; [exact Hal5|].
      split; [exact Hbits5|].
      split.
      { destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)]; lia. }
      split.
      { rewrite Hout5, Hout2. unfold len_spec. lia. }
      split; [exact Hin5cap|].
      split.
      { assert (HV0 : f_in s - f_bits s / 8 <= f_in s0 - f_bits s0 / 8).
        { destruct Hrf as [(B1&B2&B3)|(B1&B2)];
            [ rewrite B2, B3;
              replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
              rewrite w3_div8_add; lia
            | rewrite B2; lia ]. }
        assert (HV1 : f_in s0 - f_bits s0 / 8 <= f_in s1 - f_bits s1 / 8).
        { rewrite Hin1, Hbits1.
          pose proof (w3_div8_mono (f_bits s0 - Z.of_nat (length cwL))
                        (f_bits s0) ltac:(lia)).
          lia. }
        assert (HV2 : f_in s1 - f_bits s1 / 8 <= f_in s2 - f_bits s2 / 8).
        { destruct Hacc1 as [(A1&A2&A3)|(A1&A2&A3)]; rewrite A2, A3.
          - pose proof (w3_div8_mono (f_bits s1 + 8 - Z.of_nat e0)
                          (f_bits s1 + 8) ltac:(lia)) as M1.
            assert (E1 : (f_bits s1 + 8) / 8 = f_bits s1 / 8 + 1)
              by (replace (f_bits s1 + 8) with (f_bits s1 + 8 * 1) by ring;
                  apply w3_div8_add).
            lia.
          - pose proof (w3_div8_mono (f_bits s1 - Z.of_nat e0)
                          (f_bits s1) ltac:(lia)) as M1.
            lia. }
        lia. }
      rewrite Hout5, Hout2. lia.
  - (* class 4: invalid *)
    assert (E0 : (c_op (entl symL) =? 0) = false)
      by (apply Z.eqb_neq; exact Hopn).
    rewrite E0.
    assert (E16 : (Z.land (c_op (entl symL)) 16 =? 0) = true)
      by (apply Z.eqb_eq; exact H16i).
    rewrite E16. cbn [negb].
    assert (E64 : (Z.land (c_op (entl symL)) 64 =? 0) = false)
      by (apply Z.eqb_neq; exact H64i).
    rewrite E64.
    assert (E32 : (Z.land (c_op (entl symL)) 32 =? 0) = true)
      by (apply Z.eqb_eq; exact H32i).
    rewrite E32. cbn [negb]. cbv iota.
    exact I.
Qed.

Print Assumptions w3_trip.
Print Assumptions w3_dist_tail.
Print Assumptions w3_root_read.
