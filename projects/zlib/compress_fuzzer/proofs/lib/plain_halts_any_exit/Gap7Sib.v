(** * Gap7Sib — sibling strengthenings for the ZrBodySelect proof.

    OWNER: an earlier development run (GAP7 Route B: all-additive; the landed lemmas are
    NOT touched).  Two disjunction-strengthened siblings whose BAD arms
    carry the DECLARATIVE failure directly (the A1 marker-arm pattern),
    so the selection loop kills them by congruence against dec-success:

    - [zr_typedo_sound_plus]: the btype=3 BAD arm additionally exports
      [forall acc, dec_blk (br_stream (q_br q)) acc = None] — dec_blk's
      trailing [else None] at the same two reads the machine made.
    - [zr_stored_sound_plus]: the LEN/NLEN qbad arm additionally exports
      [decode_stored (br_stream (q_br q)) = None] — the complement check
      fails on the same 32 bits.

    Proof bodies replicated from ZReproQ6C.zr_typedo_sound /
    ZReproQ6D.zr_stored_sound (landed) with the read plumbing hoisted
    above the failing-arm case splits; good arms verbatim.

    PA-EXPORTS: zr_typedo_sound_plus, zr_stored_sound_plus.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn InflateFast Inflate DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6B ZReproQ6C ZReproQ6D.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** btype has two bits. *)
Lemma bits_of_2_range : forall b, 0 <= br_bits_of 2 b < 4.
Proof.
  intro b. unfold br_bits_of.
  replace (Z.shiftl 1 2 - 1) with (Z.ones 2) by reflexivity.
  rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma zr_typedo_sound_plus : forall c q q',
  n_flush c <> Z_TREES ->
  h_last (s_hdr (q_st q)) = 0 ->
  br_wf (q_br q) ->
  inf_TYPEDO c q = InfCont q' ->
  (h_mode (s_hdr (q_st q')) = M_BAD
   /\ forall acc, dec_blk (br_stream (q_br q)) acc = None)
  \/ (exists lastb ty r1,
        read_bits 1%nat (br_stream (q_br q)) = Some (lastb, r1)
        /\ read_bits 2%nat r1 = Some (ty, br_stream (q_br q'))
        /\ h_last (s_hdr (q_st q')) = lastb
        /\ br_wf (q_br q')
        /\ zr_q6_frame q q'
        /\ ( (ty = 0 /\ h_mode (s_hdr (q_st q')) = M_STORED)
          \/ (ty = 1 /\ h_mode (s_hdr (q_st q')) = M_LEN_
              /\ t_lencode (s_tab (q_st q')) = TRlenfix
              /\ t_lenbits (s_tab (q_st q')) = 9
              /\ t_distcode (s_tab (q_st q')) = TRdistfix
              /\ t_distbits (s_tab (q_st q')) = 5)
          \/ (ty = 2 /\ h_mode (s_hdr (q_st q')) = M_TABLE))).
Proof.
  intros c q q' HF Hlast Hwf H.
  unfold inf_TYPEDO in H. cbv zeta in H.
  rewrite Hlast in H.
  change (negb (0 =? 0)) with false in H.
  destruct (inf_nb 3 (q_br q)) as [b|b] eqn:EN;
    cbv beta iota in H; [| discriminate].
  destruct (inf_nb_ok 3 (q_br q) b Hwf ltac:(lia) EN)
    as (ES & Hwf1 & Hb3).
  pose proof (br_read_agree 1 b Hwf1 ltac:(lia)) as R1.
  change (Z.to_nat 1) with 1%nat in R1.
  assert (Hwfd1 : br_wf (br_dropbits 1 b))
    by (apply br_wf_dropbits; [exact Hwf1 | lia]).
  assert (Hbd1 : br_bits (br_dropbits 1 b) = br_bits b - 1)
    by apply br_dropbits_bits.
  pose proof (br_read_agree 2 (br_dropbits 1 b) Hwfd1 ltac:(lia)) as R2.
  change (Z.to_nat 2) with 2%nat in R2.
  assert (Hwfd2 : br_wf (br_dropbits 2 (br_dropbits 1 b)))
    by (apply br_wf_dropbits; [exact Hwfd1 | lia]).
  destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 0) as [E0|N0].
  { injection H as <-. right.
    exists (br_bits_of 1 b), 0, (br_stream (br_dropbits 1 b)).
    rewrite <- ES.
    rewrite E0 in R2.
    split; [exact R1|].
    split; [exact R2|].
    split; [reflexivity|].
    split; [exact Hwfd2|].
    split; [repeat split; reflexivity|].
    left. split; reflexivity. }
  destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 1) as [E1|N1].
  { rewrite (proj2 (Z.eqb_neq (n_flush c) Z_TREES) HF) in H.
    cbv beta iota in H.
    injection H as <-. right.
    exists (br_bits_of 1 b), 1, (br_stream (br_dropbits 1 b)).
    rewrite <- ES.
    rewrite E1 in R2.
    split; [exact R1|].
    split; [exact R2|].
    split; [reflexivity|].
    split; [exact Hwfd2|].
    split; [repeat split; reflexivity|].
    right; left. repeat split; reflexivity. }
  destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 2) as [E2|N2].
  { injection H as <-. right.
    exists (br_bits_of 1 b), 2, (br_stream (br_dropbits 1 b)).
    rewrite <- ES.
    rewrite E2 in R2.
    split; [exact R1|].
    split; [exact R2|].
    split; [reflexivity|].
    split; [exact Hwfd2|].
    split; [repeat split; reflexivity|].
    right; right. split; reflexivity. }
  (* btype = 3: the machine BADs and the SPEC has no block either *)
  injection H as <-. left. split; [reflexivity|].
  intro acc. unfold dec_blk.
  rewrite <- ES.
  rewrite R1. cbv beta iota.
  rewrite R2. cbv beta iota.
  rewrite (proj2 (Z.eqb_neq _ _) N0).
  rewrite (proj2 (Z.eqb_neq _ _) N1).
  rewrite (proj2 (Z.eqb_neq _ _) N2).
  reflexivity.
Qed.

Lemma zr_stored_sound_plus : forall c q,
  n_flush c <> Z_TREES ->
  br_wf (q_br q) ->
  (exists b, inf_STORED c q = InfLeave (qset_br q b))
  \/ ((exists b, inf_STORED c q
                 = InfCont (qbad (qset_br q b) MSG_STORED_LEN))
      /\ decode_stored (br_stream (q_br q)) = None)
  \/ (exists b len r1,
        read_bits 16%nat (align_byte (br_stream (q_br q))) = Some (len, r1)
        /\ read_bits 16%nat r1
           = Some (Z.lxor len 65535, br_stream (br_initbits b))
        /\ 0 <= len < 65536
        /\ br_wf (br_initbits b)
        /\ br_bits (br_initbits b) = 0
        /\ inf_STORED c q
           = inf_COPY_ (qmode (qset_br
                (qset_st q (set_length (q_st q) len))
                (br_initbits b)) M_COPY_)).
Proof.
  intros c q HF Hwf.
  unfold inf_STORED. cbv zeta.
  assert (Hwfa : br_wf (br_bytebits (q_br q))).
  { unfold br_bytebits. apply br_wf_dropbits; [exact Hwf|].
    destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (br_bits (q_br q)) 8 ltac:(lia)).
    destruct (Z.leb_spec 8 (br_bits (q_br q)));
      [ lia | rewrite Z.mod_small by lia; lia ]. }
  destruct (inf_nb 32 (br_bytebits (q_br q))) as [b|b] eqn:EN;
    [| left; eexists; reflexivity].
  destruct (inf_nb_ok 32 (br_bytebits (q_br q)) b Hwfa ltac:(lia) EN)
    as (ES & Hwfb & Hb32).
  (* the read plumbing, HOISTED above the complement check so the qbad
     arm can spell the declarative reads too *)
  assert (Hb0 : (br_bits (br_bytebits (q_br q))) mod 8 = 0).
  { unfold br_bytebits, br_dropbits. cbn [br_bits].
    destruct Hwf as (Hb & _).
    replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    rewrite Zminus_mod, Z.mod_mod by lia.
    rewrite Z.sub_diag. reflexivity. }
  assert (Hbeq : br_bits b = 32).
  { pose proof (Z.div_mod (br_bits (br_bytebits (q_br q))) 8
                  ltac:(lia)) as HD.
    rewrite Hb0, Z.add_0_r in HD.
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
  set (len := br_bits_of 16 b).
  assert (Hlen : 0 <= len < 65536).
  { unfold len, br_bits_of.
    replace (Z.shiftl 1 16 - 1) with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    apply Z.mod_pos_bound. lia. }
  assert (Hland : Z.land (br_hold b) 65535 = len).
  { unfold len, br_bits_of. f_equal. }
  (* the second read's VALUE, check-independent: the top 16 of a 32-bit
     wf hold *)
  assert (Hnlenv : br_bits_of 16 (br_dropbits 16 b)
                   = Z.shiftr (br_hold b) 16).
  { unfold br_bits_of, br_dropbits. cbn [br_hold].
    replace (Z.shiftl 1 16 - 1) with (Z.ones 16) by reflexivity.
    rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    destruct Hwfb as (_ & Hh & _).
    rewrite Z.shiftl_1_l, Hbeq in Hh.
    change (2 ^ 32) with 4294967296 in Hh.
    apply Z.mod_small.
    rewrite Z.shiftr_div_pow2 by lia.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  destruct (negb (Z.land (br_hold b) 65535
                  =? Z.lxor (Z.shiftr (br_hold b) 16) 65535)) eqn:ECHK.
  { (* qbad arm: the machine rejects AND the spec's complement check
       fails on the same two 16-bit fields *)
    right; left. split; [eexists; reflexivity|].
    apply negb_true_iff, Z.eqb_neq in ECHK.
    unfold decode_stored.
    rewrite <- (zr_bytebits_align (q_br q) Hwf), <- ES.
    rewrite R1. cbv beta iota.
    rewrite R2. cbv beta iota.
    fold len.
    destruct (Z.eqb_spec
                (Z.lxor len (br_bits_of 16 (br_dropbits 16 b))) 65535)
      as [Econtra|]; [exfalso | reflexivity].
    apply ECHK.
    rewrite Hland.
    rewrite Hnlenv in Econtra.
    (* len XOR top = 65535  =>  top = len XOR 65535  =>
       top XOR 65535 = len *)
    rewrite <- Econtra.
    rewrite (Z.lxor_comm len (Z.shiftr (br_hold b) 16)).
    now rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l.
  }
  right; right.
  apply negb_false_iff, Z.eqb_eq in ECHK.
  assert (Hnlen : br_bits_of 16 (br_dropbits 16 b) = Z.lxor len 65535).
  { rewrite Hnlenv. rewrite Hland in ECHK. rewrite ECHK.
    now rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. }
  exists b, len, (br_stream (br_dropbits 16 b)).
  split; [| split; [| split; [exact Hlen | split; [| split]]]].
  - rewrite <- (zr_bytebits_align (q_br q) Hwf), <- ES.
    rewrite R1. now fold len.
  - rewrite R2. rewrite Hnlen. do 2 f_equal.
    unfold br_stream, br_dropbits, br_initbits;
      cbn [br_bits br_hold].
    rewrite Hbeq.
    destruct Hwfb as (_ & Hh & _).
    rewrite Z.shiftl_1_l, Hbeq in Hh.
    replace (32 - 32) with 0 by lia.
    replace (Z.shiftr (br_hold b) 32) with 0
      by (rewrite Z.shiftr_div_pow2 by lia; symmetry;
          apply Z.div_small; lia).
    reflexivity.
  - destruct Hwfb as (_ & _ & Hv & Hr).
    unfold br_initbits, br_wf; cbn [br_bits br_hold br_have br_in].
    rewrite Z.shiftl_1_l.
    repeat split; try lia;
      try (match goal with |- context [br_in b ?k] =>
             specialize (Hr k); lia end).
  - reflexivity.
  - rewrite (proj2 (Z.eqb_neq (n_flush c) Z_TREES) HF).
    cbv beta iota.
    destruct Hwfb as (_ & Hh & _).
    rewrite Z.shiftl_1_l, Hbeq in Hh.
    change (2 ^ 32) with 4294967296 in Hh.
    unfold u32. rewrite Z.mod_small by lia.
    rewrite Hland. reflexivity.
Qed.

Set Printing Width 2000.
Print Assumptions zr_typedo_sound_plus.
Print Assumptions zr_stored_sound_plus.
