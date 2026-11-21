(** * W3D — the per-trip classification at TWO-LEVEL tables (dyn round
      Leg A fast side, q7-decode, 2026-08-20, OFF-TREE SCRATCH).

    The dyn twin of the landed [W3Trip.w3_trip]: one [if_body] trip at a
    [zr_two_own_v3]-owned read IS one [decode_lit_len] step.  The read
    layer gains the chain case (root pointer -> one more [if_dolen] /
    [if_dodist] level at the child) and the marker case (BodyBad,
    absorbed); the four ent-class dispatch bodies are factored ONCE into
    [w3d_dispatch] / [w3d_dist_dispatch], parameterized by the bits
    already consumed ([d] = 0 at a root leaf, [d] = root at a child),
    so leaf and chain reuse one proof.  Everything else mirrors W3Trip
    verbatim.  Interface: A1StmtsV3 (working text v3, freeze v4). *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* ===== fast-shadow insert (fastshadow bed, W3D, batch JG6) =====
   Context-shed Zify pre-hook: revert every arithmetic hypothesis into the
   goal, then clear every remaining clearable hypothesis, so each [lia]/[nia]
   pays zify preprocessing only for the arithmetic facts instead of the full
   context.
   The hook is restored to the Zify default at the END of this file, so
   importers see no net redefinition. *)
Ltac w3d_fs_shed :=
  repeat match goal with
  | H : (_ <= _)%Z |- _ => revert H
  | H : (_ < _)%Z |- _ => revert H
  | H : (_ >= _)%Z |- _ => revert H
  | H : (_ > _)%Z |- _ => revert H
  | H : @eq Z _ _ |- _ => revert H
  | H : not _ |- _ => revert H
  | H : @eq bool _ _ |- _ => revert H
  | H : @eq nat _ _ |- _ => revert H
  | H : (_ <= _)%nat |- _ => revert H
  | H : (_ < _)%nat |- _ => revert H
  | H : (_ >= _)%nat |- _ => revert H
  | H : (_ > _)%nat |- _ => revert H
  | H : @eq N _ _ |- _ => revert H
  | H : (_ <= _)%N |- _ => revert H
  | H : (_ < _)%N |- _ => revert H
  | H : _ /\ _ |- _ => revert H
  | H : _ \/ _ |- _ => revert H
  | H : _ <-> _ |- _ => revert H
  end;
  repeat match goal with H : _ |- _ => clear H end.
Ltac Zify.zify_pre_hook ::= w3d_fs_shed.
(* ===== end fast-shadow insert ===== *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits BwStream ZBitsIn Huff DeflateSpec Inflate InflateFast
  InflateThy ZBitsBridge DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import W1Content W2Stream
  W3Trip.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6P.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1StmtsV3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require A1core GtDecHsel.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Helpers.
   ========================================================================== *)

Lemma w3d_firstn_add : forall (A : Type) (a b : nat) (l : list A),
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A a. induction a as [|a IH]; intros b l.
  - reflexivity.
  - destruct l as [|x l].
    + cbn [skipn]. now rewrite !firstn_nil.
    + cbn [Nat.add firstn skipn app]. f_equal. apply IH.
Qed.

(** Pointer ops are 240-clean: the fast dispatch's 16/64 tests both
    pass through to the chain arm. *)
Lemma w3d_ptr_masks : forall op, 1 <= op <= 14 ->
  Z.land op 16 = 0 /\ Z.land op 64 = 0.
Proof.
  intros op H.
  apply GtDecHsel.land240_sub.
  apply A1core.zrA_land240_small. lia.
Qed.

(* ==========================================================================
   2.  The owned root read, THREE-WAY (leaf / pointer / marker).
   ========================================================================== *)

Lemma w3d_root_read :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code)
         (mask : Z) c s,
    ValidLengths lens 15%nat ->
    zr_two_own_v3 T root lens ent ->
    0 < root <= 15 ->
    mask = Z.shiftl 1 root - 1 ->
    if_swf s -> root <= f_bits s ->
    (* LEAF: short code, hdecode fires *)
    (exists sym cw,
       code_for lens 15%nat sym = Some cw
       /\ T (Z.land (f_hold s) mask) = ent sym
       /\ c_bits (ent sym) = Z.of_nat (length cw)
       /\ 1 <= Z.of_nat (length cw) <= root
       /\ hdecode (code_table lens 15%nat) (if_stream c s)
          = Some (sym, skipn (length cw) (if_stream c s)))
    (* POINTER: fields + children + the root-window spelling *)
    \/ (c_bits (T (Z.land (f_hold s) mask)) = root
        /\ 1 <= c_op (T (Z.land (f_hold s) mask)) <= 15 - root
        /\ zr_ptr_children T root lens ent (Z.land (f_hold s) mask)
             (c_op (T (Z.land (f_hold s) mask)))
             (c_val (T (Z.land (f_hold s) mask)))
        /\ firstn (Z.to_nat root) (if_stream c s)
           = write_bits (Z.to_nat root) (Z.land (f_hold s) mask))
    (* MARKER *)
    \/ T (Z.land (f_hold s) mask) = mkCodeT 64 1 0.
Proof.
  intros T root lens ent mask c s HV Hown Hroot Emask Hswf Hbits.
  pose proof Hswf as (Hb0 & Hh0 & Hh1).
  assert (Hrange : 0 <= Z.land (f_hold s) mask < 2 ^ root)
    by (rewrite Emask; apply land_ones_range; lia).
  assert (Hw : write_bits (Z.to_nat root) (Z.land (f_hold s) mask)
               = firstn (Z.to_nat root) (if_stream c s)).
  { assert (Hlow : Z.land (f_hold s) mask = if_low root s)
      by (unfold if_low; rewrite Emask; reflexivity).
    rewrite Hlow. apply w2_low_spells_stream; [lia | exact Hh0]. }
  destruct (Hown _ Hrange)
    as [ (sym & cw & Hcf & Hcwr & HTi & Hcb & Hpref)
       | [ (Hcb & Hop & Hval & Hwc & Hch)
         | (Hrec & _ & _ & _) ] ].
  - left.
    assert (Hlen1 : (1 <= length cw)%nat).
    { destruct (code_for_inv _ _ _ _ Hcf) as (len & _ & Hl1 & _ & Ecw).
      rewrite Ecw, code_bits_length. exact Hl1. }
    set (n := length cw) in *.
    exists sym, cw.
    split; [exact Hcf|].
    split; [exact HTi|].
    split; [exact Hcb|].
    split; [lia|].
    assert (Hfp : cw = firstn n (if_stream c s)).
    { rewrite <- Hpref, Hw.
      rewrite firstn_firstn.
      assert (Hmin : Nat.min n (Z.to_nat root) = n)
        by (apply Nat.min_l; lia).
      rewrite Hmin. reflexivity. }
    assert (Hsplit : if_stream c s = cw ++ skipn n (if_stream c s)).
    { rewrite Hfp at 1.
      rewrite <- Hfp. rewrite Hfp at 1. apply eq_sym, firstn_skipn. }
    rewrite Hsplit at 1.
    exact (hdecode_complete nat Nat.eq_dec (code_table lens 15%nat) cw sym
             (skipn n (if_stream c s))
             (code_table_prefix_free lens 15%nat HV)
             (proj2 (code_table_In_iff lens 15%nat sym cw) Hcf)).
  - right; left.
    split; [exact Hcb|].
    split; [exact Hop|].
    split; [exact Hch|].
    symmetry. exact Hw.
  - right; right. exact Hrec.
Qed.

(* ==========================================================================
   3.  The child read at a pointer (all-coded; the two-slab spelling).
   ========================================================================== *)

Lemma w3d_child_read :
  forall (T : ztbl) (root : Z) (lens : list nat) (ent : nat -> Code)
         (i op val : Z) c (s1 : IfSt) (str : list bool),
    ValidLengths lens 15%nat ->
    0 < root <= 15 ->
    1 <= op <= 15 - root ->
    zr_ptr_children T root lens ent i op val ->
    if_swf s1 ->
    op <= f_bits s1 ->
    if_stream c s1 = skipn (Z.to_nat root) str ->
    firstn (Z.to_nat root) str = write_bits (Z.to_nat root) i ->
    exists sym cw,
      code_for lens 15%nat sym = Some cw
      /\ T (val + if_low op s1) = ent sym
      /\ c_bits (ent sym) = Z.of_nat (length cw) - root
      /\ root < Z.of_nat (length cw) <= root + op
      /\ hdecode (code_table lens 15%nat) str
         = Some (sym, skipn (length cw) str).
Proof.
  intros T root lens ent i op val c s1 str HV Hroot Hop Hch Hsw1 Hbits1
         Hstr1 Hpre.
  pose proof Hsw1 as (Hb1 & Hh1 & _).
  set (j := if_low op s1).
  assert (Hj : 0 <= j < 2 ^ op).
  { unfold j, if_low. apply land_ones_range. lia. }
  destruct (Hch j Hj) as (sym & cw & Hcf & Hrng & HTj & Hcbj & Hsp).
  exists sym, cw.
  split; [exact Hcf|].
  split; [exact HTj|].
  split; [exact Hcbj|].
  split; [exact Hrng|].
  assert (Hw2 : write_bits (Z.to_nat op) j
                = firstn (Z.to_nat op) (if_stream c s1)).
  { unfold j. apply w2_low_spells_stream; [lia | exact Hh1]. }
  assert (HrootLe : (Z.to_nat root <= length cw)%nat)
    by (apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia).
  set (m := (length cw - Z.to_nat root)%nat).
  assert (Hcwlen : (length cw = Z.to_nat root + m)%nat)
    by (unfold m; lia).
  assert (Hmop : (m <= Z.to_nat op)%nat).
  { unfold m. apply Nat2Z.inj_le.
    rewrite Nat2Z.inj_sub by exact HrootLe.
    rewrite Z2Nat.id by lia.
    rewrite Z2Nat.id by lia.
    lia. }
  assert (Hsp' : cw = write_bits (Z.to_nat root) i ++ write_bits m j).
  { rewrite <- Hsp at 1.
    rewrite Hcwlen, w3d_firstn_add.
    f_equal.
    - rewrite firstn_app, write_bits_length, Nat.sub_diag.
      cbn [firstn]. rewrite app_nil_r.
      apply firstn_all2. rewrite write_bits_length. lia.
    - rewrite skipn_app, write_bits_length, Nat.sub_diag.
      cbn [skipn].
      rewrite skipn_all2 by (rewrite write_bits_length; lia).
      cbn [app].
      apply firstn_write_bits. exact Hmop. }
  assert (Hfp : firstn (length cw) str = cw).
  { rewrite Hcwlen, w3d_firstn_add, Hpre.
    rewrite Hsp'. f_equal.
    rewrite <- Hstr1.
    transitivity (firstn m (firstn (Z.to_nat op) (if_stream c s1))).
    - rewrite firstn_firstn.
      rewrite Nat.min_l by exact Hmop. reflexivity.
    - rewrite <- Hw2. apply firstn_write_bits. exact Hmop. }
  assert (Hsplit : str = cw ++ skipn (length cw) str).
  { rewrite <- Hfp at 1. apply eq_sym, firstn_skipn. }
  rewrite Hsplit at 1.
  exact (hdecode_complete nat Nat.eq_dec (code_table lens 15%nat) cw sym
           (skipn (length cw) str)
           (code_table_prefix_free lens 15%nat HV)
           (proj2 (code_table_In_iff lens 15%nat sym cw) Hcf)).
Qed.

(* ==========================================================================
   4.  The DIST dispatch at a coded read, parameterized by the bits
       already consumed ([d] = 0 root leaf / [d] = rootD child).  The
       body is [W3Trip.w3_dist_tail]'s post-read text at that
       generality; the conclusion pack is verbatim w3_dist_tail's,
       relative to the tail's entry state [s2].
   ========================================================================== *)

Lemma w3d_dist_dispatch :
  forall (k : nat) c (s2 sPre : IfSt) (d : Z) (dsym : nat)
         (cwD : list bool) (dl : list nat) (entd : nat -> Code)
         (len : Z) (len_spec : nat),
    zr_dist_ents dl entd ->
    f_whave c = 0 -> f_sane c <> 0 -> if_inb c ->
    code_for dl 15%nat dsym = Some cwD ->
    hdecode (code_table dl 15%nat) (if_stream c s2)
      = Some (dsym, skipn (length cwD) (if_stream c s2)) ->
    c_bits (entd dsym) = Z.of_nat (length cwD) - d ->
    0 <= d < Z.of_nat (length cwD) ->
    Z.of_nat (length cwD) <= 15 ->
    if_swf sPre -> if_haligned c sPre ->
    if_stream c sPre = skipn (Z.to_nat d) (if_stream c s2) ->
    f_bits sPre <= 60 ->
    15 <= f_bits sPre + d ->
    f_buf sPre = f_buf s2 -> f_out sPre = f_out s2 ->
    ((f_in sPre = f_in s2 + 2 /\ f_bits sPre = f_bits s2 + 16 - d)
     \/ (f_in sPre = f_in s2 /\ f_bits sPre = f_bits s2 - d)) ->
    0 <= f_bits s2 ->
    f_in s2 + 3 <= f_last c + 5 ->
    (f_bits s2 < 4 -> f_in s2 + 4 <= f_last c + 5) ->
    0 <= f_beg c <= f_out s2 -> f_out s2 <= 4294967295 ->
    len = Z.of_nat len_spec ->
    (3 <= len_spec)%nat -> (len_spec <= 258)%nat ->
    match if_dodist (S k) c len sPre (entd dsym) with
    | BodyOk s' =>
        exists (dsym' : nat) (dist_spec : nat) (r3 r4 : list bool),
          hdecode (code_table dl 15%nat) (if_stream c s2) = Some (dsym', r3)
          /\ read_extra dist_base dist_extra dsym' r3 = Some (dist_spec, r4)
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
  intros k c s2 sPre d dsym cwD dl entd len len_spec Hde Hwh Hsn Hinb
         HcfD HhdD HcbD Hd Hcw15 HswP HalP HstrP HcapP Hb15d HbufP HoutP
         Hacc0 Hb2z Hrm3 Hrm4 Hbeg Hocap Elen Hl3 Hl258.
  pose proof HswP as (HbP & HhP & _).
  assert (HinS2 : f_in s2 <= f_in sPre)
    by (destruct Hacc0 as [(A&_)|(A&_)]; lia).
  rewrite if_dodist_S. cbv zeta.
  rewrite HcbD.
  set (wD := Z.of_nat (length cwD) - d).
  set (s1' := if_drop wD sPre).
  assert (HwD : 0 < wD <= f_bits sPre) by (unfold wD; lia).
  assert (Hds1 : if_stream c s1' = skipn (length cwD) (if_stream c s2)).
  { unfold s1'.
    rewrite (w2_drop_stream wD c sPre) by (auto; lia).
    rewrite HstrP, A1core.zrA_skipn_skipn.
    f_equal.
    rewrite <- Z2Nat.inj_add by lia.
    unfold wD.
    replace (d + (Z.of_nat (length cwD) - d))
      with (Z.of_nat (length cwD)) by ring.
    apply Nat2Z.id. }
  assert (Hsw1' : if_swf s1')
    by (apply w2_drop_swf; auto; lia).
  pose proof Hsw1' as (Hb1' & Hh1' & _).
  assert (Hal1' : if_haligned c s1')
    by (apply w2_drop_haligned; auto; lia).
  assert (Hbuf1' : f_buf s1' = f_buf s2)
    by (unfold s1'; rewrite w3_drop_buf; exact HbufP).
  assert (Hout1' : f_out s1' = f_out s2)
    by (unfold s1'; rewrite w3_drop_out; exact HoutP).
  assert (Hin1' : f_in s1' = f_in sPre) by apply w3_drop_in.
  assert (Hbits1' : f_bits s1' = f_bits sPre - wD)
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
  { intros _. rewrite Hin1'. lia. }
  assert (Hroom2 : f_bits s1' + 8 < Z.of_nat e0' ->
                   f_in s1' + 1 < f_last c + 5).
  { intros Hb. rewrite Hin1'.
    destruct Hacc0 as [(A1&A2)|(A1&A2)].
    - assert (Hb4 : f_bits s2 < 4) by lia.
      pose proof (Hrm4 Hb4). lia.
    - lia. }
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
  { assert (f_in s2 <= f_in s1') by lia.
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
        destruct Hacc0 as [(C1&C2)|(C1&C2)];
        try lia;
        (* two loads fired AND the +16 entry: bits s2 < 4 fires Hrm4 *)
        assert (Hb4 : f_bits s2 < 4) by lia;
        pose proof (Hrm4 Hb4); lia. }
    { (* the virtual byte cursor [f_in - bits/8] is monotone *)
      rewrite (if_copyn_in (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))),
              (if_copyn_bits (Z.to_nat len) c s3'
                 (SrcOut (f_out s3' - (c_val (entd dsym) + v')))).
      assert (HV23 : f_in s2 - f_bits s2 / 8 <= f_in sPre - f_bits sPre / 8).
      { destruct Hacc0 as [(C1&C2)|(C1&C2)]; rewrite C1, C2.
        - pose proof (w3_div8_mono (f_bits s2 + 16 - d) (f_bits s2 + 16)
                        ltac:(lia)) as M1.
          assert (E1 : (f_bits s2 + 16) / 8 = f_bits s2 / 8 + 2)
            by (replace (f_bits s2 + 16) with (f_bits s2 + 8 * 2) by ring;
                apply w3_div8_add).
          lia.
        - pose proof (w3_div8_mono (f_bits s2 - d) (f_bits s2)
                        ltac:(lia)) as M1.
          lia. }
      assert (HV31 : f_in sPre - f_bits sPre / 8
                     <= f_in s1' - f_bits s1' / 8).
      { rewrite Hin1', Hbits1'.
        pose proof (w3_div8_mono (f_bits sPre - wD) (f_bits sPre)
                      ltac:(lia)).
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
   5.  The DIST tail at two-level tables: refill + three-way read +
       (leaf dispatch | chain to the child dispatch | marker BAD).
   ========================================================================== *)

Lemma w3d_dist_tail :
  forall c (s2 : IfSt) (rootD : Z) (dl : list nat) (entd : nat -> Code)
         (len : Z) (len_spec : nat) (k : nat),
    ValidLengths dl 15%nat ->
    zr_two_own_v3 (f_dcode c) rootD dl entd ->
    zr_dist_ents dl entd ->
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
  destruct (w3d_root_read (f_dcode c) rootD dl entd (f_dmask c) c s3
              HVd HownD HrD EmD Hsw3 ltac:(lia))
    as [ (dsym & cwD & HcfD & HTD & HcbD & HlenD & HhdD)
       | [ (HcbP & HopP & HchP & HpreP)
         | Hrec ] ].
  - (* root LEAF *)
    rewrite Hst3 in HhdD.
    rewrite HTD.
    assert (HcbD0 : c_bits (entd dsym) = Z.of_nat (length cwD) - 0)
      by lia.
    assert (HdD : 0 <= 0 < Z.of_nat (length cwD)) by lia.
    assert (Hcw15D : Z.of_nat (length cwD) <= 15) by lia.
    assert (HstrD : if_stream c s3
                    = skipn (Z.to_nat 0) (if_stream c s2))
      by (cbn [Z.to_nat]; rewrite Hst3; reflexivity).
    assert (Hb15D : 15 <= f_bits s3 + 0) by lia.
    assert (HaccD : (f_in s3 = f_in s2 + 2 /\ f_bits s3 = f_bits s2 + 16 - 0)
                    \/ (f_in s3 = f_in s2 /\ f_bits s3 = f_bits s2 - 0))
      by (destruct Hrf2 as [(A&B&C)|(A&E)];
          [left; split; lia | right; rewrite E; split; lia]).
    assert (Hb2z : 0 <= f_bits s2) by lia.
    exact (w3d_dist_dispatch k c s2 s3 0 dsym cwD dl entd len len_spec
             Hde Hwh Hsn Hinb HcfD HhdD HcbD0 HdD Hcw15D
             Hsw3 Hal3 HstrD Hcap3 Hb15D Hbuf3 Hout3 HaccD
             Hb2z Hrm3 Hrm4 Hbeg Hocap Elen Hl3 Hl258).
  - (* root POINTER: chase the child *)
    rewrite if_dodist_S. cbv zeta.
    rewrite HcbP.
    set (s1' := if_drop rootD s3).
    assert (Hds1 : if_stream c s1'
                   = skipn (Z.to_nat rootD) (if_stream c s2)).
    { unfold s1'.
      rewrite (w2_drop_stream rootD c s3) by (auto; lia).
      rewrite Hst3. reflexivity. }
    assert (Hsw1' : if_swf s1') by (apply w2_drop_swf; auto; lia).
    pose proof Hsw1' as (Hb1' & Hh1' & _).
    assert (Hal1' : if_haligned c s1')
      by (apply w2_drop_haligned; auto; lia).
    assert (Hbuf1' : f_buf s1' = f_buf s2)
      by (unfold s1'; rewrite w3_drop_buf; exact Hbuf3).
    assert (Hout1' : f_out s1' = f_out s2)
      by (unfold s1'; rewrite w3_drop_out; exact Hout3).
    assert (Hin1' : f_in s1' = f_in s3) by apply w3_drop_in.
    assert (Hbits1' : f_bits s1' = f_bits s3 - rootD)
      by (apply w3_drop_bits; lia).
    pose proof (w3d_ptr_masks (c_op (f_dcode c
                  (Z.land (f_hold s3) (f_dmask c)))) ltac:(lia))
      as (M16 & M64).
    assert (E16 : (Z.land (c_op (f_dcode c
                    (Z.land (f_hold s3) (f_dmask c)))) 16 =? 0) = true)
      by (apply Z.eqb_eq; exact M16).
    rewrite E16. cbn [negb].
    assert (E64 : (Z.land (c_op (f_dcode c
                    (Z.land (f_hold s3) (f_dmask c)))) 64 =? 0) = true)
      by (apply Z.eqb_eq; exact M64).
    rewrite E64. cbv iota.
    destruct k as [|k'].
    + cbn [if_dodist]. exact I.
    + assert (HpreS2 : firstn (Z.to_nat rootD) (if_stream c s2)
                       = write_bits (Z.to_nat rootD)
                           (Z.land (f_hold s3) (f_dmask c)))
        by (rewrite <- Hst3; exact HpreP).
      destruct (w3d_child_read (f_dcode c) rootD dl entd
                  (Z.land (f_hold s3) (f_dmask c))
                  (c_op (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
                  (c_val (f_dcode c (Z.land (f_hold s3) (f_dmask c))))
                  c s1' (if_stream c s2)
                  HVd HrD HopP HchP Hsw1' ltac:(lia) Hds1 HpreS2)
        as (dsymC & cwC & HcfC & HTC & HcbC & HrngC & HhdC).
      rewrite HTC.
      assert (HdC : 0 <= rootD < Z.of_nat (length cwC)) by lia.
      assert (Hcw15C : Z.of_nat (length cwC) <= 15) by lia.
      assert (HcapC : f_bits s1' <= 60) by lia.
      assert (Hb15C : 15 <= f_bits s1' + rootD) by lia.
      assert (HaccC : (f_in s1' = f_in s2 + 2
                       /\ f_bits s1' = f_bits s2 + 16 - rootD)
                      \/ (f_in s1' = f_in s2
                          /\ f_bits s1' = f_bits s2 - rootD))
        by (destruct Hrf2 as [(A&B&C)|(A&E)];
            [ left; split; lia
            | right; split;
              [ rewrite Hin1', E; reflexivity
              | rewrite Hbits1', E; reflexivity ]]).
      assert (Hb2z : 0 <= f_bits s2) by lia.
      exact (w3d_dist_dispatch k' c s2 s1' rootD dsymC cwC dl entd
               len len_spec Hde Hwh Hsn Hinb HcfC HhdC HcbC
               HdC Hcw15C Hsw1' Hal1' Hds1 HcapC Hb15C Hbuf1' Hout1'
               HaccC Hb2z Hrm3 Hrm4 Hbeg Hocap Elen Hl3 Hl258).
  - (* root MARKER: BAD *)
    rewrite Hrec.
    rewrite if_dodist_S. cbv zeta.
    assert (Eo : c_op (mkCodeT 64 1 0) = 64) by reflexivity.
    rewrite Eo.
    assert (T2 : (Z.land 64 16 =? 0) = true) by reflexivity.
    rewrite T2. cbn [negb].
    assert (T3 : (Z.land 64 64 =? 0) = false) by reflexivity.
    rewrite T3. cbv iota. exact I.
Qed.

(* ==========================================================================
   6.  The LEN dispatch at a coded read, parameterized by [d].  The
       four-class body is [W3Trip.w3_trip]'s post-read text at that
       generality; the conclusion is the trip pack relative to [s].
   ========================================================================== *)

Lemma w3d_dispatch :
  forall (k : nat) c (s sPre : IfSt) (d : Z) (sym : nat) (cw : list bool)
         (rootD : Z) (ll dl : list nat) (entl entd : nat -> Code),
    ValidLengths dl 15%nat ->
    zr_two_own_v3 (f_dcode c) rootD dl entd ->
    zr_len_ents ll entl ->
    zr_dist_ents dl entd ->
    0 < rootD <= 15 ->
    f_dmask c = Z.shiftl 1 rootD - 1 ->
    f_whave c = 0 -> f_sane c <> 0 -> if_inb c ->
    code_for ll 15%nat sym = Some cw ->
    hdecode (code_table ll 15%nat) (if_stream c s)
      = Some (sym, skipn (length cw) (if_stream c s)) ->
    c_bits (entl sym) = Z.of_nat (length cw) - d ->
    0 <= d < Z.of_nat (length cw) ->
    Z.of_nat (length cw) <= 15 ->
    if_swf sPre -> if_haligned c sPre ->
    if_stream c sPre = skipn (Z.to_nat d) (if_stream c s) ->
    f_bits sPre <= 60 ->
    15 <= f_bits sPre + d ->
    f_buf sPre = f_buf s -> f_out sPre = f_out s ->
    ((f_in sPre = f_in s + 2 /\ f_bits sPre = f_bits s + 16 - d)
     \/ (f_in sPre = f_in s /\ f_bits sPre = f_bits s - d)) ->
    0 <= f_bits s ->
    f_in s + 6 <= f_last c + 5 ->
    0 <= f_beg c <= f_out s ->
    f_out s <= 4294967295 ->
    match if_dolen (S k) c sPre (entl sym) with
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
  intros k c s sPre d sym cw rootD ll dl entl entd HVd HownD Hle Hde HrD
         EmD Hwh Hsn Hinb HcfL HhdL Hcbw Hd Hcw15 HswP HalP HstrP HcapP
         Hb15d HbufP HoutP Hacc0 Hb0s HroomS Hbeg Hocap.
  pose proof HswP as (HbP & HhP & _).
  assert (HinS : f_in s <= f_in sPre)
    by (destruct Hacc0 as [(A&_)|(A&_)]; lia).
  assert (HinP2 : f_in sPre <= f_in s + 2)
    by (destruct Hacc0 as [(A&_)|(A&_)]; lia).
  (* the shared s -> sPre virtual-cursor step *)
  assert (HV0 : f_in s - f_bits s / 8 <= f_in sPre - f_bits sPre / 8).
  { destruct Hacc0 as [(A1&A2)|(A1&A2)]; rewrite A1, A2.
    - pose proof (w3_div8_mono (f_bits s + 16 - d) (f_bits s + 16)
                    ltac:(lia)) as M1.
      assert (E1 : (f_bits s + 16) / 8 = f_bits s / 8 + 2)
        by (replace (f_bits s + 16) with (f_bits s + 8 * 2) by ring;
            apply w3_div8_add).
      lia.
    - pose proof (w3_div8_mono (f_bits s - d) (f_bits s) ltac:(lia)) as M1.
      lia. }
  rewrite if_dolen_S. cbv zeta.
  rewrite Hcbw.
  set (wL := Z.of_nat (length cw) - d).
  set (s1 := if_drop wL sPre).
  assert (HwL : 0 < wL <= f_bits sPre) by (unfold wL; lia).
  assert (Er1 : if_stream c s1 = skipn (length cw) (if_stream c s)).
  { unfold s1.
    rewrite (w2_drop_stream wL c sPre) by (auto; lia).
    rewrite HstrP, A1core.zrA_skipn_skipn.
    f_equal.
    rewrite <- Z2Nat.inj_add by lia.
    unfold wL.
    replace (d + (Z.of_nat (length cw) - d))
      with (Z.of_nat (length cw)) by ring.
    apply Nat2Z.id. }
  assert (Hsw1 : if_swf s1) by (apply w2_drop_swf; auto; lia).
  pose proof Hsw1 as (Hb1 & Hh1 & _).
  assert (Hal1 : if_haligned c s1) by (apply w2_drop_haligned; auto; lia).
  assert (Hbuf1 : f_buf s1 = f_buf s)
    by (unfold s1; rewrite w3_drop_buf; exact HbufP).
  assert (Hout1 : f_out s1 = f_out s)
    by (unfold s1; rewrite w3_drop_out; exact HoutP).
  assert (Hin1 : f_in s1 = f_in sPre) by apply w3_drop_in.
  assert (Hbits1 : f_bits s1 = f_bits sPre - wL)
    by (apply w3_drop_bits; lia).
  assert (HV1 : f_in sPre - f_bits sPre / 8 <= f_in s1 - f_bits s1 / 8).
  { rewrite Hin1, Hbits1.
    pose proof (w3_div8_mono (f_bits sPre - wL) (f_bits sPre) ltac:(lia)).
    lia. }
  destruct (Hle _ _ HcfL) as
    [ (Hsym & Hop0 & Hval)
    | [ (Esym & Hopn & H32e & H16e & H64e)
    | [ (Hsym257 & b0 & e0 & Hnb & Hne & Hop3 & H32l & H64l & H15l & Hval
         & Hb3 & Hb258 & He5 & Hjoint)
    | (Hopn & H32i & H16i & H64i) ] ] ].
  - (* class 1: literal *)
    rewrite Hop0.
    change (0 =? 0) with true. cbv iota.
    exists (LzLit (Z.of_nat sym)), (skipn (length cw) (if_stream c s)).
    split.
    { unfold decode_lit_len. rewrite HhdL.
      rewrite (proj2 (Nat.ltb_lt sym 256) Hsym).
      reflexivity. }
    split; [discriminate|].
    split.
    { rewrite w3_stream_put. exact Er1. }
    split.
    { assert (Ev : u8 (c_val (entl sym)) = Z.of_nat sym)
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
    { cbn [if_put f_in f_bits]. lia. }
    { rewrite if_put_out, Hout1. lia. }
  - (* class 2: end of block *)
    assert (E0 : (c_op (entl sym) =? 0) = false)
      by (apply Z.eqb_neq; exact Hopn).
    rewrite E0.
    assert (E16 : (Z.land (c_op (entl sym)) 16 =? 0) = true)
      by (apply Z.eqb_eq; exact H16e).
    rewrite E16. cbn [negb].
    assert (E64 : (Z.land (c_op (entl sym)) 64 =? 0) = false)
      by (apply Z.eqb_neq; exact H64e).
    rewrite E64.
    assert (E32 : (Z.land (c_op (entl sym)) 32 =? 0) = false)
      by (apply Z.eqb_neq; exact H32e).
    rewrite E32. cbn [negb]. cbv iota.
    split.
    { unfold decode_lit_len. rewrite HhdL.
      subst sym.
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
    split; [lia|].
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
      assert (Hre : read_extra length_base length_extra (sym - 257)%nat
                      (skipn (length cw) (if_stream c s))
                    = Some (len_spec, if_stream c s1)).
      { unfold read_extra. rewrite Hnb, Hne.
        cbn [read_bits].
        rewrite Er1.
        unfold len_spec. rewrite Nat.add_0_r. reflexivity. }
      assert (Elen : c_val (entl sym) = Z.of_nat len_spec)
        by (unfold len_spec; exact Hval).
      change tbl_fuel with (S 15).
      pose proof (w3d_dist_tail c s1 rootD dl entd (c_val (entl sym))
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
        rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)).
        rewrite (proj2 (Nat.eqb_neq sym 256) ltac:(lia)).
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
      { lia. }
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
      assert (Elen : c_val (entl sym) + v = Z.of_nat len_spec).
      { unfold len_spec. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
        rewrite Hval. reflexivity. }
      assert (Hjz : Z.of_nat b0 + 2 ^ Z.of_nat e0 - 1 <= 258).
      { replace (2 ^ Z.of_nat e0) with (Z.of_nat (2 ^ e0))
          by (rewrite Nat2Z.inj_pow; reflexivity).
        lia. }
      assert (Hre : read_extra length_base length_extra (sym - 257)%nat
                      (skipn (length cw) (if_stream c s))
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
          destruct Hacc0 as [(B1&B2)|(B1&B2)];
          try lia. }
      change tbl_fuel with (S 15).
      pose proof (w3d_dist_tail c s2 rootD dl entd
                    (c_val (entl sym) + v) len_spec 15
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
        rewrite (proj2 (Nat.ltb_ge sym 256) ltac:(lia)).
        rewrite (proj2 (Nat.eqb_neq sym 256) ltac:(lia)).
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
      { assert (HV2 : f_in s1 - f_bits s1 / 8 <= f_in s2 - f_bits s2 / 8).
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
    assert (E0 : (c_op (entl sym) =? 0) = false)
      by (apply Z.eqb_neq; exact Hopn).
    rewrite E0.
    assert (E16 : (Z.land (c_op (entl sym)) 16 =? 0) = true)
      by (apply Z.eqb_eq; exact H16i).
    rewrite E16. cbn [negb].
    assert (E64 : (Z.land (c_op (entl sym)) 64 =? 0) = false)
      by (apply Z.eqb_neq; exact H64i).
    rewrite E64.
    assert (E32 : (Z.land (c_op (entl sym)) 32 =? 0) = true)
      by (apply Z.eqb_eq; exact H32i).
    rewrite E32. cbn [negb]. cbv iota.
    exact I.
Qed.

(* ==========================================================================
   7.  THE TRIP at two-level tables.
   ========================================================================== *)

Lemma w3d_trip :
  forall c s (rootL rootD : Z) (ll dl : list nat) (entl entd : nat -> Code),
    ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
    zr_two_own_v3 (f_lcode c) rootL ll entl ->
    zr_two_own_v3 (f_dcode c) rootD dl entd ->
    zr_len_ents ll entl -> zr_dist_ents dl entd ->
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
  destruct (w3d_root_read (f_lcode c) rootL ll entl (f_lmask c) c s0
              HVl HownL HrL EmL Hsw0 ltac:(lia))
    as [ (symL & cwL & HcfL & HTL & HcbL & HlenL & HhdL)
       | [ (HcbP & HopP & HchP & HpreP)
         | Hrec ] ].
  - (* root LEAF: dispatch at d = 0 *)
    rewrite Hst0 in HhdL.
    change tbl_fuel with (S 15).
    rewrite HTL.
    assert (HcbL0 : c_bits (entl symL) = Z.of_nat (length cwL) - 0)
      by lia.
    assert (HdL : 0 <= 0 < Z.of_nat (length cwL)) by lia.
    assert (Hcw15L : Z.of_nat (length cwL) <= 15) by lia.
    assert (HstrL : if_stream c s0
                    = skipn (Z.to_nat 0) (if_stream c s))
      by (cbn [Z.to_nat]; rewrite Hst0; reflexivity).
    assert (Hb15L : 15 <= f_bits s0 + 0) by lia.
    assert (HaccL : (f_in s0 = f_in s + 2 /\ f_bits s0 = f_bits s + 16 - 0)
                    \/ (f_in s0 = f_in s /\ f_bits s0 = f_bits s - 0))
      by (destruct Hrf as [(A&B&C)|(A&E)];
          [left; split; lia | right; rewrite E; split; lia]).
    exact (w3d_dispatch 15 c s s0 0 symL cwL rootD ll dl entl entd
             HVd HownD Hle Hde HrD EmD Hwh Hsn Hinb HcfL HhdL
             HcbL0 HdL Hcw15L Hsw0 Hal0 HstrL Hcap0 Hb15L Hbuf0 Hout0
             HaccL ltac:(lia) Hroom Hbeg Hocap).
  - (* root POINTER: one chain hop, dispatch at d = rootL *)
    change tbl_fuel with (S 15).
    rewrite if_dolen_S. cbv zeta.
    rewrite HcbP.
    set (s1 := if_drop rootL s0).
    assert (Hds1 : if_stream c s1
                   = skipn (Z.to_nat rootL) (if_stream c s)).
    { unfold s1.
      rewrite (w2_drop_stream rootL c s0) by (auto; lia).
      rewrite Hst0. reflexivity. }
    assert (Hsw1 : if_swf s1) by (apply w2_drop_swf; auto; lia).
    pose proof Hsw1 as (Hb1 & Hh1 & _).
    assert (Hal1 : if_haligned c s1)
      by (apply w2_drop_haligned; auto; lia).
    assert (Hbuf1 : f_buf s1 = f_buf s)
      by (unfold s1; rewrite w3_drop_buf; exact Hbuf0).
    assert (Hout1 : f_out s1 = f_out s)
      by (unfold s1; rewrite w3_drop_out; exact Hout0).
    assert (Hin1 : f_in s1 = f_in s0) by apply w3_drop_in.
    assert (Hbits1 : f_bits s1 = f_bits s0 - rootL)
      by (apply w3_drop_bits; lia).
    pose proof (w3d_ptr_masks (c_op (f_lcode c
                  (Z.land (f_hold s0) (f_lmask c)))) ltac:(lia))
      as (M16 & M64).
    assert (E0 : (c_op (f_lcode c
                    (Z.land (f_hold s0) (f_lmask c))) =? 0) = false)
      by (apply Z.eqb_neq; lia).
    rewrite E0.
    assert (E16 : (Z.land (c_op (f_lcode c
                    (Z.land (f_hold s0) (f_lmask c)))) 16 =? 0) = true)
      by (apply Z.eqb_eq; exact M16).
    rewrite E16. cbn [negb].
    assert (E64 : (Z.land (c_op (f_lcode c
                    (Z.land (f_hold s0) (f_lmask c)))) 64 =? 0) = true)
      by (apply Z.eqb_eq; exact M64).
    rewrite E64. cbv iota.
    assert (HpreS : firstn (Z.to_nat rootL) (if_stream c s)
                    = write_bits (Z.to_nat rootL)
                        (Z.land (f_hold s0) (f_lmask c)))
      by (rewrite <- Hst0; exact HpreP).
    destruct (w3d_child_read (f_lcode c) rootL ll entl
                (Z.land (f_hold s0) (f_lmask c))
                (c_op (f_lcode c (Z.land (f_hold s0) (f_lmask c))))
                (c_val (f_lcode c (Z.land (f_hold s0) (f_lmask c))))
                c s1 (if_stream c s)
                HVl HrL HopP HchP Hsw1 ltac:(lia) Hds1 HpreS)
      as (symC & cwC & HcfC & HTC & HcbC & HrngC & HhdC).
    rewrite HTC.
    assert (HdC : 0 <= rootL < Z.of_nat (length cwC)) by lia.
    assert (Hcw15C : Z.of_nat (length cwC) <= 15) by lia.
    assert (HcapC : f_bits s1 <= 60) by lia.
    assert (Hb15C : 15 <= f_bits s1 + rootL) by lia.
    assert (HaccC : (f_in s1 = f_in s + 2
                     /\ f_bits s1 = f_bits s + 16 - rootL)
                    \/ (f_in s1 = f_in s /\ f_bits s1 = f_bits s - rootL))
      by (destruct Hrf as [(A&B&C)|(A&E)];
          [ left; split; lia
          | right; split;
            [ rewrite Hin1, E; reflexivity
            | rewrite Hbits1, E; reflexivity ]]).
    exact (w3d_dispatch 14 c s s1 rootL symC cwC rootD ll dl entl entd
             HVd HownD Hle Hde HrD EmD Hwh Hsn Hinb HcfC HhdC HcbC
             HdC Hcw15C Hsw1 Hal1 Hds1 HcapC Hb15C Hbuf1 Hout1
             HaccC ltac:(lia) Hroom Hbeg Hocap).
  - (* root MARKER: BodyBad, absorbed *)
    change tbl_fuel with (S 15).
    rewrite Hrec.
    rewrite if_dolen_S. cbv zeta.
    assert (Eo : c_op (mkCodeT 64 1 0) = 64) by reflexivity.
    rewrite Eo.
    assert (T1 : (64 =? 0) = false) by reflexivity.
    rewrite T1.
    assert (T2 : (Z.land 64 16 =? 0) = true) by reflexivity.
    rewrite T2. cbn [negb].
    assert (T3 : (Z.land 64 64 =? 0) = false) by reflexivity.
    rewrite T3.
    assert (T4 : (Z.land 64 32 =? 0) = true) by reflexivity.
    rewrite T4. cbn [negb]. cbv iota.
    exact I.
Qed.

Print Assumptions w3d_trip.
Print Assumptions w3d_dist_tail.
Print Assumptions w3d_root_read.
Print Assumptions w3d_child_read.

(* fast-shadow restore: importers of this file see the Zify default hook. *)
Ltac Zify.zify_pre_hook ::= idtac.
