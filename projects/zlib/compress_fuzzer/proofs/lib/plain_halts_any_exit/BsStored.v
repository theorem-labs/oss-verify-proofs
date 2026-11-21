(** * BsStored — the stored block, GOOD-ONLY (an earlier development run bodyasm fork).

    The landed zr_stored_sound / zr_copy_loop / zr_stored_trip expose
    bare starve/BAD/absorbed arms (unrefutable post-hoc — the round's
    finding), so this file RE-RUNS them with the kills at their sites:
    the header NEEDBITS(32) starve dies by K1 against decode_stored's
    own read successes; the complement-check BAD dies by decode_stored's
    own guard; the copy-zero leave dies by input availability
    (read_bytes' bit accounting) + output room.  Proof bodies mirror
    ZReproQ6D.zr_stored_sound / ZReproQ6W.{zr_copy_loop, zr_stored_trip}
    verbatim modulo the declared kill deltas.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff InflateFast Inflate DeflateSpec
  StoredRt.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6B ZReproQ6D ZReproQ6I ZReproQ6W ZReproL0E W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill LkNb.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import BsSupport.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The copy-zero leave inversion.                                      *)

Lemma bs_min2_zero : forall a b c,
  0 <= c -> c <> 0 ->
  (if a <? (if b <? c then b else c) then a
   else (if b <? c then b else c)) = 0 ->
  a <= 0 \/ b <= 0.
Proof.
  intros a b c Hc Nc.
  destruct (Z.ltb_spec b c) as [L1|L1]; intros H.
  - destruct (Z.ltb_spec a b) as [L2|L2]; lia.
  - destruct (Z.ltb_spec a c) as [L2|L2]; lia.
Qed.

Lemma bs_copy_leave_inv : forall q q2,
  0 <= u_length (s_cur (q_st q)) ->
  inf_COPY q = InfLeave q2 ->
  u_length (s_cur (q_st q)) <> 0
  /\ (o_left (q_ob q) <= 0 \/ br_have (q_br q) <= 0).
Proof.
  intros q q2 Hlen H.
  unfold inf_COPY in H. cbv zeta in H.
  destruct (Z.eqb_spec (u_length (s_cur (q_st q))) 0) as [E0|N0];
    [discriminate H|].
  split; [exact N0|].
  lazymatch type of H with
  | (if ?b then _ else _) = _ => destruct b eqn:Ez; [|discriminate H]
  end.
  apply Z.eqb_eq in Ez.
  exact (bs_min2_zero _ _ _ Hlen N0 Ez).
Qed.

(* ------------------------------------------------------------------ *)
(* The copy loop, good-only.                                           *)

Definition bs_copy_pack (c : InfCtx) (q : InfSt) : Prop :=
  exists k q',
     inf_iter k c q = Some q'
     /\ br_bytes (q_br q)
        = (map (fun m => br_in (q_br q) (br_next (q_br q) + Z.of_nat m))
               (seq 0 (Z.to_nat (u_length (s_cur (q_st q))))))
          ++ br_bytes (q_br q')
     /\ br_hold (q_br q') = br_hold (q_br q)
     /\ br_bits (q_br q') = br_bits (q_br q)
     /\ br_wf (q_br q')
     /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
        = ob_slice (q_ob q) 0 (o_put (q_ob q))
          ++ map (fun m => br_in (q_br q) (br_next (q_br q) + Z.of_nat m))
                 (seq 0 (Z.to_nat (u_length (s_cur (q_st q)))))
     /\ o_put (q_ob q') = o_put (q_ob q) + u_length (s_cur (q_st q))
     /\ o_put (q_ob q') + o_left (q_ob q')
        = o_put (q_ob q) + o_left (q_ob q)
     /\ 0 <= o_left (q_ob q')
     /\ h_mode (s_hdr (q_st q')) = M_TYPE
     /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
     /\ q_ret q' = q_ret q
     /\ q_in q' = q_in q /\ q_out q' = q_out q
     /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
     /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q))
     /\ w_whave (s_win (q_st q')) = w_whave (s_win (q_st q))
     /\ t_sane (s_tab (q_st q')) = t_sane (s_tab (q_st q))
     /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
     /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
     /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q)).

Lemma bs_copy_len0 : forall c q,
  br_wf (q_br q) ->
  0 <= o_left (q_ob q) ->
  h_mode (s_hdr (q_st q)) = M_COPY ->
  u_length (s_cur (q_st q)) = 0 ->
  inf_COPY q = InfCont (qmode q M_TYPE) ->
  bs_copy_pack c q.
Proof.
  intros c q Hwf Hleft Hm E0 EC.
  exists 1%nat, (qmode q M_TYPE).
  split. { apply inf_iter_one. rewrite (zr_step_at_copy c q Hm). exact EC. }
  rewrite E0. change (Z.to_nat 0) with 0%nat. cbn [seq map].
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { exact Hwf. }
  split. { now rewrite app_nil_r. }
  split. { change (q_ob (qmode q M_TYPE)) with (q_ob q). lia. }
  split. { reflexivity. }
  split. { exact Hleft. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  split. { reflexivity. }
  reflexivity.
Qed.

Lemma bs_copy_loop_good : forall n c q,
  (Z.to_nat (u_length (s_cur (q_st q))) <= n)%nat ->
  zr_copy_entry q ->
  u_length (s_cur (q_st q)) <= br_have (q_br q) ->
  u_length (s_cur (q_st q)) <= o_left (q_ob q) ->
  bs_copy_pack c q.
Proof.
  induction n as [|n IH]; intros c q Hn Hentry Hhave Hroom;
  pose proof Hentry as (Hwf & Hput & Hleft & Hlen & Hm);
  destruct (zr_copy_step q Hwf Hleft Hput Hlen)
    as [[E0 EC] | [EL | (c2 & q' & Hc2 & Hc2h & Hc2o & EC & HLen'
                         & HMode & HHold & HBits & HBytes & HWf'
                         & HPut' & HLeft' & HSlice)]].
  - exact (bs_copy_len0 c q Hwf Hleft Hm E0 EC).
  - exfalso.
    destruct (bs_copy_leave_inv q q ltac:(lia) EL) as (N0 & [HL|HH]); lia.
  - exfalso.
    pose proof (Z2Nat.id (u_length (s_cur (q_st q))) ltac:(lia)) as HID.
    assert (HZ : Z.to_nat (u_length (s_cur (q_st q))) = 0%nat) by lia.
    rewrite HZ in HID. cbn in HID. lia.
  - exact (bs_copy_len0 c q Hwf Hleft Hm E0 EC).
  - exfalso.
    destruct (bs_copy_leave_inv q q ltac:(lia) EL) as (N0 & [HL|HH]); lia.
  - (* transfer: recurse and compose (walk's block, absorbed arm gone) *)
    destruct (zr_copy_frame q) as [HF _].
    destruct (HF q' EC)
      as (HRet & HIn & HOut & HLast & HWrap & HWsz & HWh & HSn & HFl
          & HCk & HTo).
    assert (Hentry' : zr_copy_entry q').
    { unfold zr_copy_entry.
      split; [exact HWf'|].
      split; [rewrite HPut'; lia|].
      split; [rewrite HLeft'; lia|].
      split; [rewrite HLen'; lia|].
      rewrite HMode; exact Hm. }
    assert (Hn' : (Z.to_nat (u_length (s_cur (q_st q'))) <= n)%nat)
      by (rewrite HLen'; lia).
    (* availability re-established: have' = have - c2 *)
    assert (Hhave' : u_length (s_cur (q_st q')) <= br_have (q_br q')).
    { pose proof (br_bytes_length (q_br q)) as BLq.
      pose proof (br_bytes_length (q_br q')) as BLq'.
      assert (HLL : length (br_bytes (q_br q))
                    = (Z.to_nat c2 + length (br_bytes (q_br q')))%nat)
        by (rewrite HBytes, length_app, zr_mapseq_len; reflexivity).
      destruct Hwf as (_ & _ & Hh0 & _).
      destruct HWf' as (_ & _ & Hh' & _).
      rewrite BLq, BLq' in HLL.
      rewrite HLen'. lia. }
    assert (Hroom' : u_length (s_cur (q_st q')) <= o_left (q_ob q')).
    { rewrite HLen', HLeft'. lia. }
    destruct (IH c q' Hn' Hentry' Hhave' Hroom')
      as (k & q'' & HI & HBt2 & HH2 & HB2 & HW2 & HS2 & HP2
          & HSum2 & HOl2 & HM2 & HL2 & HR2 & HIn2 & HOut2
          & HWr2 & HWs2 & HWh2 & HSn2 & HFl2 & HCk2 & HTo2).
    set (lenq := u_length (s_cur (q_st q))) in *.
    set (A := map (fun m => br_in (q_br q) (br_next (q_br q) + Z.of_nat m))
                  (seq 0 (Z.to_nat c2))) in *.
    set (B := map (fun m => br_in (q_br q') (br_next (q_br q') + Z.of_nat m))
                  (seq 0 (Z.to_nat (u_length (s_cur (q_st q')))))) in *.
    set (P := map (fun m => br_in (q_br q) (br_next (q_br q) + Z.of_nat m))
                  (seq 0 (Z.to_nat lenq))) in *.
    assert (HAB : br_bytes (q_br q) = (A ++ B) ++ br_bytes (q_br q''))
      by (rewrite HBytes, HBt2; now rewrite app_assoc).
    assert (HlenAB : length (A ++ B) = Z.to_nat lenq).
    { rewrite length_app. unfold A, B.
      rewrite !zr_mapseq_len, HLen'. unfold lenq. lia. }
    assert (Hlenhave : lenq <= br_have (q_br q)).
    { pose proof (br_bytes_length (q_br q)) as HhaveN.
      assert (HLL : length (br_bytes (q_br q))
              = (length (A ++ B) + length (br_bytes (q_br q'')))%nat)
        by (rewrite HAB; apply length_app).
      rewrite HhaveN, HlenAB in HLL. unfold lenq in *. lia. }
    assert (HP : br_bytes (q_br q)
                 = P ++ map (fun m => br_in (q_br q)
                              (br_next (q_br q) + lenq + Z.of_nat m))
                        (seq 0 (Z.to_nat (br_have (q_br q) - lenq)))).
    { unfold br_bytes at 1. unfold P.
      apply (zr_bytes_split (br_in (q_br q)) (br_have (q_br q))
               (br_next (q_br q)) lenq).
      unfold lenq in *. lia. }
    assert (HABP : A ++ B = P).
    { destruct (zr_app_inj (A ++ B) P
                  (br_bytes (q_br q''))
                  (map (fun m => br_in (q_br q)
                         (br_next (q_br q) + lenq + Z.of_nat m))
                       (seq 0 (Z.to_nat (br_have (q_br q) - lenq))))
                  ltac:(rewrite HlenAB; unfold P;
                        now rewrite zr_mapseq_len)
                  ltac:(rewrite <- HAB; exact HP)) as [HH _].
      exact HH. }
    exists (1 + k)%nat, q''.
    split.
    { rewrite (inf_iter_add 1 k c q q'); [ exact HI |].
      apply inf_iter_one. rewrite (zr_step_at_copy c q Hm). exact EC. }
    split.
    { rewrite HAB, HABP. reflexivity. }
    split. { now rewrite HH2, HHold. }
    split. { now rewrite HB2, HBits. }
    split. { exact HW2. }
    split.
    { rewrite HS2, HSlice, <- app_assoc, HABP. reflexivity. }
    split. { rewrite HP2, HPut', HLen'. unfold lenq. lia. }
    split. { rewrite HSum2, HPut', HLeft'. lia. }
    split. { exact HOl2. }
    split. { exact HM2. }
    split. { now rewrite HL2, HLast. }
    split. { now rewrite HR2, HRet. }
    split. { now rewrite HIn2, HIn. }
    split. { now rewrite HOut2, HOut. }
    split. { now rewrite HWr2, HWrap. }
    split. { now rewrite HWs2, HWsz. }
    split. { now rewrite HWh2, HWh. }
    split. { now rewrite HSn2, HSn. }
    split. { now rewrite HFl2, HFl. }
    split. { now rewrite HCk2, HCk. }
    { now rewrite HTo2, HTo. }
Qed.

(* ------------------------------------------------------------------ *)
(* The stored header, good-only: the NEEDBITS(32) starve dies by K1
   against decode_stored's own reads; the complement-check BAD dies by
   decode_stored's own guard.                                          *)

Lemma bs_stored_sound_good : forall c q payload rem1,
  n_flush c <> Z_TREES ->
  br_wf (q_br q) ->
  decode_stored (br_stream (q_br q)) = Some (payload, rem1) ->
  exists b len,
    0 <= len < 65536
    /\ br_wf (br_initbits b)
    /\ br_bits (br_initbits b) = 0
    /\ read_bytes (Z.to_nat len) (br_stream (br_initbits b))
       = Some (payload, rem1)
    /\ inf_STORED c q
       = inf_COPY_ (qmode (qset_br (qset_st q (set_length (q_st q) len))
                            (br_initbits b)) M_COPY_).
Proof.
  intros c q payload rem1 HF Hwf HD.
  assert (Hwfa : br_wf (br_bytebits (q_br q))).
  { unfold br_bytebits. apply br_wf_dropbits; [exact Hwf|].
    destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    destruct (Z.leb_spec 8 (br_bits (q_br q)));
      [ lia | rewrite Z.mod_small by lia; lia ]. }
  unfold decode_stored in HD.
  destruct (read_bits 16%nat (align_byte (br_stream (q_br q))))
    as [[len0 r1d]|] eqn:D1; [|discriminate].
  destruct (read_bits 16%nat r1d) as [[nlen0 r2d]|] eqn:D2; [|discriminate].
  destruct (inf_nb 32 (br_bytebits (q_br q))) as [b|b] eqn:EN.
  2:{ exfalso.
      destruct (k1_nb_starve_short 32 (br_bytebits (q_br q)) b Hwfa
                  ltac:(lia) EN) as (HS & _ & _).
      change (Z.to_nat 32) with 32%nat in HS.
      pose proof (read_bits_length _ _ _ _ D1) as L1.
      pose proof (read_bits_length _ _ _ _ D2) as L2.
      rewrite (zr_bytebits_align (q_br q) Hwf) in HS. lia. }
  destruct (inf_nb_ok 32 (br_bytebits (q_br q)) b Hwfa ltac:(lia) EN)
    as (ES & Hwfb & Hb32).
  assert (Hb0m : (br_bits (br_bytebits (q_br q))) mod 8 = 0).
  { unfold br_bytebits, br_dropbits. cbn [br_bits].
    destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    rewrite Zminus_mod, Z.mod_mod by lia.
    rewrite Z.sub_diag. reflexivity. }
  assert (Hbeq : br_bits b = 32).
  { pose proof (Z.div_mod (br_bits (br_bytebits (q_br q))) 8
                  ltac:(lia)) as HDm.
    rewrite Hb0m, Z.add_0_r in HDm.
    destruct (zr_nb_bits 32 (br_bytebits (q_br q)) b EN)
      as [HE | (Hlt & k & Hk)];
      destruct Hwfa as (HbA & _); destruct Hwfb as (HbB & _); lia. }
  pose proof (br_read_agree 16 b Hwfb ltac:(lia)) as R1.
  change (Z.to_nat 16) with 16%nat in R1.
  assert (Hwfd : br_wf (br_dropbits 16 b))
    by (apply br_wf_dropbits; [exact Hwfb | lia]).
  pose proof (br_read_agree 16 (br_dropbits 16 b) Hwfd
                ltac:(rewrite br_dropbits_bits; lia)) as R2.
  change (Z.to_nat 16) with 16%nat in R2.
  set (len := br_bits_of 16 b) in *.
  assert (Hlen : 0 <= len < 65536).
  { unfold len, br_bits_of.
    replace (Z.shiftl 1 16 - 1) with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    apply Z.mod_pos_bound. lia. }
  assert (Hland : Z.land (br_hold b) 65535 = len).
  { unfold len, br_bits_of. f_equal. }
  assert (HS16 : br_bits_of 16 (br_dropbits 16 b)
                 = Z.shiftr (br_hold b) 16).
  { unfold br_bits_of, br_dropbits. cbn [br_hold].
    replace (Z.shiftl 1 16 - 1) with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    destruct Hwfb as (_ & Hh & _).
    rewrite Z.shiftl_1_l, Hbeq in Hh.
    change (2 ^ 32) with 4294967296 in Hh.
    rewrite Z.mod_small; [reflexivity|].
    rewrite Z.shiftr_div_pow2 by lia.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (EQA : align_byte (br_stream (q_br q)) = br_stream b).
  { rewrite <- (zr_bytebits_align (q_br q) Hwf). exact (eq_sym ES). }
  rewrite EQA in D1. rewrite R1 in D1.
  injection D1 as E1a E1b. subst len0 r1d.
  rewrite R2 in D2. injection D2 as E2a E2b. subst nlen0 r2d.
  rewrite HS16 in HD.
  destruct (Z.eqb_spec (Z.lxor len (Z.shiftr (br_hold b) 16)) 65535)
    as [G|G]; [|discriminate HD].
  assert (HSval : Z.shiftr (br_hold b) 16 = Z.lxor len 65535).
  { rewrite <- G.
    now rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. }
  assert (ECHK : negb (Z.land (br_hold b) 65535
                   =? Z.lxor (Z.shiftr (br_hold b) 16) 65535) = false).
  { rewrite HSval, Hland.
    rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r, Z.eqb_refl.
    reflexivity. }
  assert (HSdrop : br_stream (br_dropbits 16 (br_dropbits 16 b))
                   = br_stream (br_initbits b)).
  { unfold br_stream, br_dropbits, br_initbits; cbn [br_bits br_hold].
    rewrite Hbeq.
    destruct Hwfb as (_ & Hh & _).
    rewrite Z.shiftl_1_l, Hbeq in Hh.
    change (2 ^ 32) with 4294967296 in Hh.
    replace (32 - 16 - 16) with 0 by lia.
    replace (Z.shiftr (Z.shiftr (br_hold b) 16) 16) with 0.
    { reflexivity. }
    rewrite Z.shiftr_shiftr by lia.
    change (16 + 16) with 32.
    rewrite Z.shiftr_div_pow2 by lia.
    symmetry. apply Z.div_small. lia. }
  rewrite HSdrop in HD.
  exists b, len.
  split. { exact Hlen. }
  split.
  { destruct Hwfb as (_ & _ & Hv & Hr).
    unfold br_initbits, br_wf; cbn [br_bits br_hold br_have br_in].
    rewrite Z.shiftl_1_l.
    repeat split; try lia;
      try (match goal with |- context [br_in b ?k] =>
             specialize (Hr k); lia end). }
  split. { reflexivity. }
  split. { exact HD. }
  unfold inf_STORED. cbv zeta.
  rewrite EN. cbv beta iota.
  rewrite ECHK. cbv beta iota.
  rewrite (proj2 (Z.eqb_neq (n_flush c) Z_TREES) HF). cbv beta iota.
  destruct Hwfb as (_ & Hh & _).
  rewrite Z.shiftl_1_l, Hbeq in Hh.
  change (2 ^ 32) with 4294967296 in Hh.
  unfold u32. rewrite Z.mod_small by lia.
  rewrite Hland. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The stored trip, good-only.                                         *)

Lemma bs_stored_trip_good : forall c q payload rem1,
  zr_cflush_ok c ->
  br_wf (q_br q) ->
  0 <= o_put (q_ob q) ->
  0 <= o_left (q_ob q) ->
  h_mode (s_hdr (q_st q)) = M_STORED ->
  decode_stored (br_stream (q_br q)) = Some (payload, rem1) ->
  zlen payload <= o_left (q_ob q) ->
  exists k q',
    inf_iter k c q = Some q'
    /\ br_stream (q_br q') = rem1
    /\ br_wf (q_br q')
    /\ ob_slice (q_ob q') 0 (o_put (q_ob q'))
       = ob_slice (q_ob q) 0 (o_put (q_ob q)) ++ payload
    /\ o_put (q_ob q') + o_left (q_ob q')
       = o_put (q_ob q) + o_left (q_ob q)
    /\ 0 <= o_put (q_ob q')
    /\ 0 <= o_left (q_ob q')
    /\ h_mode (s_hdr (q_st q')) = M_TYPE
    /\ h_last (s_hdr (q_st q')) = h_last (s_hdr (q_st q))
    /\ q_ret q' = q_ret q /\ q_in q' = q_in q /\ q_out q' = q_out q
    /\ h_wrap (s_hdr (q_st q')) = h_wrap (s_hdr (q_st q))
    /\ w_wsize (s_win (q_st q')) = w_wsize (s_win (q_st q))
    /\ w_whave (s_win (q_st q')) = w_whave (s_win (q_st q))
    /\ t_sane (s_tab (q_st q')) = t_sane (s_tab (q_st q))
    /\ h_flags (s_hdr (q_st q')) = h_flags (s_hdr (q_st q))
    /\ h_check (s_hdr (q_st q')) = h_check (s_hdr (q_st q))
    /\ h_total (s_hdr (q_st q')) = h_total (s_hdr (q_st q))
    /\ W2Stream.br_haligned (q_br q').
Proof.
  intros c q payload rem1 Hc Hwf Hput Hleft Hm HD Hroom.
  assert (HF : n_flush c <> Z_TREES) by (destruct Hc as [_ HT]; exact HT).
  destruct (bs_stored_sound_good c q payload rem1 HF Hwf HD)
    as (b & len & Hlen & Hwfb & Hb0 & HRB & EARM).
  set (q1 := qmode (qset_br (qset_st q (set_length (q_st q) len))
                      (br_initbits b)) M_COPY_) in *.
  set (q2 := qmode q1 M_COPY).
  assert (Hm2 : h_mode (s_hdr (q_st q2)) = M_COPY) by reflexivity.
  assert (HSTEP : inf_step c q = inf_step c q2).
  { rewrite (zr_step_at_stored c q Hm), EARM, (zr_step_at_copy c q2 Hm2).
    unfold inf_COPY_. reflexivity. }
  assert (HS1 : br_stream (br_initbits b) = bytes_bits (br_bytes (q_br q2))).
  { unfold br_stream. rewrite Hb0, zwrite_0. reflexivity. }
  assert (Hhave2 : u_length (s_cur (q_st q2)) <= br_have (q_br q2)).
  { pose proof (bs_read_bytes_bits _ _ _ _ HRB) as LB.
    rewrite HS1, bytes_bits_length in LB.
    pose proof (br_bytes_length (q_br q2)) as BL.
    rewrite BL in LB.
    change (u_length (s_cur (q_st q2))) with len.
    change (br_have (q_br q2)) with (br_have (br_initbits b)) in *.
    destruct Hwfb as (_ & _ & Hh2 & _).
    assert (HN : (Z.to_nat len <= Z.to_nat (br_have (br_initbits b)))%nat)
      by lia.
    exact (proj2 (Z2Nat.inj_le len (br_have (br_initbits b))
                    (proj1 Hlen) Hh2) HN). }
  assert (Hroom2 : u_length (s_cur (q_st q2)) <= o_left (q_ob q2)).
  { change (u_length (s_cur (q_st q2))) with len.
    change (o_left (q_ob q2)) with (o_left (q_ob q)).
    pose proof (read_bytes_length _ _ _ _ HRB) as PL.
    unfold zlen in Hroom. rewrite PL in Hroom.
    rewrite Z2Nat.id in Hroom by lia. exact Hroom. }
  assert (Hentry2 : zr_copy_entry q2).
  { unfold zr_copy_entry.
    split; [exact Hwfb|].
    split; [exact Hput|].
    split; [exact Hleft|].
    split; [exact Hlen|].
    exact Hm2. }
  destruct (bs_copy_loop_good (Z.to_nat (u_length (s_cur (q_st q2)))) c q2
              (Nat.le_refl _) Hentry2 Hhave2 Hroom2)
    as (k & q3 & HI & HBytes & HHold & HBits & HWf3 & HSlice
        & HPut3 & HSum3 & HOl3 & HM3 & HL3 & HR3 & HIn3
        & HOut3 & HWr3 & HWs3 & HWh3 & HSn3 & HFl3c & HCk3c & HTo3c).
  destruct k as [|k'].
  { exfalso. cbn [inf_iter] in HI. injection HI as <-.
    rewrite Hm2 in HM3. discriminate. }
  assert (HB3 : br_bits (q_br q3) = 0) by (rewrite HBits; exact Hb0).
  assert (HS3 : br_stream (q_br q3) = bytes_bits (br_bytes (q_br q3))).
  { unfold br_stream. rewrite HB3, zwrite_0. reflexivity. }
  assert (HRB2 : read_bytes (Z.to_nat len) (br_stream (br_initbits b))
                 = Some (map (fun m => br_in (q_br q2)
                                (br_next (q_br q2) + Z.of_nat m))
                             (seq 0 (Z.to_nat (u_length (s_cur (q_st q2))))),
                         br_stream (q_br q3))).
  { rewrite HS1, HS3, HBytes, bytes_bits_app.
    set (MAP := map (fun m => br_in (q_br q2)
                       (br_next (q_br q2) + Z.of_nat m))
                    (seq 0 (Z.to_nat (u_length (s_cur (q_st q2)))))).
    replace (Z.to_nat len) with (length MAP)
      by (unfold MAP; rewrite zr_mapseq_len; reflexivity).
    rewrite read_bytes_bytes_bits.
    rewrite stored_map_u8_id; [reflexivity|].
    apply Forall_forall. intros y Hy.
    apply in_map_iff in Hy. destruct Hy as (m & Hme & _).
    rewrite <- Hme.
    destruct Hwfb as (_ & _ & _ & Hr4). exact (Hr4 _). }
  rewrite HRB in HRB2.
  injection HRB2 as HMAP HREM.
  exists (S k'), q3.
  split. { exact (inf_iter_alias_S c q q2 k' q3 HSTEP HI). }
  split. { exact (eq_sym HREM). }
  split. { exact HWf3. }
  split. { rewrite HMAP. exact HSlice. }
  split. { exact HSum3. }
  split. { rewrite HPut3.
           change (o_put (q_ob q2)) with (o_put (q_ob q)).
           change (u_length (s_cur (q_st q2))) with len. lia. }
  split. { exact HOl3. }
  split. { exact HM3. }
  split. { exact HL3. }
  split. { exact HR3. }
  split. { exact HIn3. }
  split. { exact HOut3. }
  split. { exact HWr3. }
  split. { exact HWs3. }
  split. { exact HWh3. }
  split. { exact HSn3. }
  split. { exact HFl3c. }
  split. { exact HCk3c. }
  split. { exact HTo3c. }
  apply zr_haligned0. exact HB3.
Qed.
