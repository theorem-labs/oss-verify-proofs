(** * G3Block — ONE [tr_flush_block] emits ONE decodable block.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G3 dispatcher.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The three [trees.c:1045-1072] branches, each closed by its arm file —
    STORED by G3Stored, STATIC by G3Static, DYNAMIC by the [dyn_arm]
    hypothesis this theorem takes (the kraft/ld-seams composition's
    deliverable; its statement here is the consumption-shaped interface).
    [build_tree]/[build_bl_tree] disappear through BtFrame: the branch
    bodies read the SAME [sym_buf]/[bw] the premises talk about.

    The conclusion's trichotomy is what the stream assembly chains on:
      * [BitsBlk0]  — a mid-stream Huffman block: position-independent;
      * [BitsBlk0A] — a mid-stream STORED block: needs the suffix at byte
        parity 0, and leaves the writer byte-aligned;
      * [BitsBlk1]  — the final block ([bi_windup] pads): byte-aligned
        after, decodes with a remainder it does not constrain. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Trees CbEmit CbFold
  StoredRt.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  BtFrame G3Stored G3Static G3DynA Gap7Strict.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.


(** After a windup the stream is whole bytes. *)
Lemma bw_windup_aligned : forall b,
  (length (bw_stream (bw_windup b)) mod 8 = 0)%nat.
Proof.
  intro b. unfold bw_stream.
  destruct (bw_windup_empty b) as [_ Hv].
  rewrite Hv, zwrite_0, app_nil_r, bytes_bits_length, Nat.mul_comm.
  apply Nat.Div0.mod_mul.
Qed.

(** The windup pad is strictly sub-byte: [bw_pad]'s three branches under
    [bw_wf]'s [0 <= valid <= Buf_size]. *)
Lemma bw_pad_lt8 : forall b, bw_wf b -> (Z.to_nat (bw_pad b) < 8)%nat.
Proof.
  intros b [[Hv0 Hv16] _].
  assert (HB : Buf_size = 16) by reflexivity.
  unfold bw_pad.
  destruct (Z.ltb_spec 8 (bw_valid b)); [lia|].
  destruct (Z.ltb_spec 0 (bw_valid b)); lia.
Qed.

Theorem tr_flush_block_bits :
  forall buf stored_len last level strat dtype ts toks acc out,
  0 < level ->
  bw_wf (ts_bw ts) ->
  last = 0 \/ last = 1 ->
  BufToks (ts_symbuf ts) 0 (ts_symnext ts) toks ->
  cEnc toks ->
  resolve acc toks = Some out ->
  (forall dat, buf = Some dat ->
     Z.leb (stored_len + 4)
       (if (Z.leb (u64 (ts_statlen (snd (build_bl_tree (build_tree TK_D
                     (build_tree TK_L ts)))) + 3 + 7) / 8)
              (u64 (ts_optlen (snd (build_bl_tree (build_tree TK_D
                     (build_tree TK_L ts)))) + 3 + 7) / 8))
           || (Z.eqb strat Z_FIXED)
        then u64 (ts_statlen (snd (build_bl_tree (build_tree TK_D
               (build_tree TK_L ts)))) + 3 + 7) / 8
        else u64 (ts_optlen (snd (build_bl_tree (build_tree TK_D
               (build_tree TK_L ts)))) + 3 + 7) / 8) = true ->
     stored_len = zlen dat /\ 0 <= stored_len < 65536
     /\ Forall (fun b => 0 <= b < 256) dat /\ acc ++ dat = out) ->
  (forall mbi s2,
     (mbi, s2) = build_bl_tree (build_tree TK_D (build_tree TK_L ts)) ->
     exists delta,
       bw_stream (dyn_bw last mbi s2) = bw_stream (ts_bw ts) ++ delta
       /\ bw_wf (dyn_bw last mbi s2)
       /\ (forall suffix,
            dec_blk (delta ++ suffix) acc
            = Some (Z.eqb last 1, out, suffix))
       /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
           forall suffix,
            dec_blk_strict (delta ++ suffix) acc
            = Some (Z.eqb last 1, out, suffix))) ->
  exists delta,
    bw_stream (ts_bw (snd (tr_flush_block buf stored_len last level strat
                             dtype ts)))
      = bw_stream (ts_bw ts) ++ delta
    /\ bw_wf (ts_bw (snd (tr_flush_block buf stored_len last level strat
                            dtype ts)))
    /\ ( (last = 0
          /\ (forall suffix,
               dec_blk (delta ++ suffix) acc = Some (false, out, suffix))
          /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
              forall suffix,
               dec_blk_strict (delta ++ suffix) acc
               = Some (false, out, suffix)))
       \/ (last = 0
          /\ (length (bw_stream (ts_bw (snd (tr_flush_block buf stored_len
                        last level strat dtype ts)))) mod 8 = 0)%nat
          /\ (forall suffix, (length suffix mod 8 = 0)%nat ->
               dec_blk (delta ++ suffix) acc = Some (false, out, suffix))
          /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
              forall suffix, (length suffix mod 8 = 0)%nat ->
               dec_blk_strict (delta ++ suffix) acc
               = Some (false, out, suffix)))
       \/ (last = 1
          /\ (length (bw_stream (ts_bw (snd (tr_flush_block buf stored_len
                        last level strat dtype ts)))) mod 8 = 0)%nat
          /\ exists pad, (length pad < 8)%nat
             /\ (forall suffix, (length suffix mod 8 = 0)%nat ->
                  dec_blk (delta ++ suffix) acc
                  = Some (true, out, pad ++ suffix))
             /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
                 forall suffix, (length suffix mod 8 = 0)%nat ->
                  dec_blk_strict (delta ++ suffix) acc
                  = Some (true, out, pad ++ suffix))) ).
Proof.
  intros buf stored_len last level strat dtype ts toks acc out
         Hlevel Hwf Hl Hbuf Henc Hres Hstored Hdyn.
  unfold tr_flush_block. cbv zeta.
  rewrite (proj2 (Z.ltb_lt 0 level) Hlevel).
  cbv iota.
  destruct (build_bl_tree (build_tree TK_D (build_tree TK_L ts)))
    as [mbi s2] eqn:EP.
  cbn [fst snd].
  (* the builders' frame: same buffer, same writer *)
  assert (HF : TFrame s2 ts).
  { assert (Es2 : s2 = snd (build_bl_tree (build_tree TK_D
                             (build_tree TK_L ts))))
      by (rewrite EP; reflexivity).
    rewrite Es2.
    eapply tframe_trans; [apply build_bl_tree_frame|].
    eapply tframe_trans; apply build_tree_frame. }
  destruct HF as (Fsb & Fsn & Fbw & Fm).
  (* the shared post-processing: [init_block] keeps the writer *)
  assert (Einit : forall X, ts_bw (init_block X) = ts_bw X)
    by (intro X; reflexivity).
  destruct buf as [dat|].
  - (* buf present: the stored TEST runs *)
    destruct (Z.leb (stored_len + 4)
                (if (Z.leb (u64 (ts_statlen s2 + 3 + 7) / 8)
                       (u64 (ts_optlen s2 + 3 + 7) / 8))
                    || (Z.eqb strat Z_FIXED)
                 then u64 (ts_statlen s2 + 3 + 7) / 8
                 else u64 (ts_optlen s2 + 3 + 7) / 8)) eqn:Eguard.
    + (* ---- STORED ---- *)
      cbv iota.
      assert (Hstored' := Hstored dat eq_refl).
      try rewrite EP in Hstored'. cbn [snd] in Hstored'.
      destruct (Hstored' Eguard) as (Hlen & Hrange & Hbytes & Hout).
      clear Hstored'.
      destruct (tr_stored_block_dec_blk dat stored_len last s2
                  ltac:(rewrite Fbw; exact Hwf) Hl Hlen Hrange Hbytes)
        as (delta & Hs & Hw & Hval0 & Hmod & Hdec & Hdecs).
      set (s4 := tr_stored_block dat stored_len last s2) in *.
      destruct Hl; subst last.
      * (* last = 0: no windup *)
        cbn [Z.eqb]. cbv iota.
        exists delta.
        rewrite Einit.
        split; [rewrite Hs, ?Fbw; reflexivity|].
        split; [exact Hw|].
        right. left.
        split; [reflexivity|].
        split; [exact Hmod|].
        split.
        { intros suffix Hsuf.
          rewrite (Hdec suffix acc Hsuf), Hout. reflexivity. }
        { intros _ _ suffix Hsuf.
          rewrite (Hdecs suffix acc Hsuf), Hout. reflexivity. }
      * (* last = 1: windup is a no-op on the aligned writer *)
        cbn [Z.eqb]. cbv iota.
        cbn [ts_bw set_bw].
        rewrite Einit.
        assert (Epad : bw_pad (ts_bw s4) = 0)
          by (unfold bw_pad; rewrite Hval0; reflexivity).
        pose proof (bw_windup_stream (ts_bw s4) Hw) as Swind.
        rewrite Epad in Swind. cbn [Z.to_nat repeat] in Swind.
        rewrite app_nil_r in Swind.
        exists delta.
        split; [rewrite Swind, Hs, ?Fbw; reflexivity|].
        split; [apply bw_windup_wf|].
        right. right.
        split; [reflexivity|].
        split; [apply bw_windup_aligned|].
        exists (@nil bool).
        split; [cbn; lia|].
        split.
        { intros suffix Hsuf.
          cbn [app].
          rewrite (Hdec suffix acc Hsuf), Hout. reflexivity. }
        { intros _ _ suffix Hsuf.
          cbn [app].
          rewrite (Hdecs suffix acc Hsuf), Hout. reflexivity. }
    + (* stored not taken: fall through to the Huffman choice *)
      cbv iota.
      destruct (Z.eqb (u64 (ts_statlen s2 + 3 + 7) / 8)
                  (if (Z.leb (u64 (ts_statlen s2 + 3 + 7) / 8)
                         (u64 (ts_optlen s2 + 3 + 7) / 8))
                      || (Z.eqb strat Z_FIXED)
                   then u64 (ts_statlen s2 + 3 + 7) / 8
                   else u64 (ts_optlen s2 + 3 + 7) / 8)).
      * (* ---- STATIC ---- *)
        cbv iota.
        destruct (static_arm_dec_blk (ts_symbuf s2) (ts_symnext s2) toks
                    (ts_bw s2) last acc out
                    ltac:(rewrite Fbw; exact Hwf) Hl
                    ltac:(rewrite Fsb, Fsn; exact Hbuf) Henc Hres)
          as (delta & Hs & Hw & Hdec & Hdecs).
          set (b4 := compress_block (ts_symbuf s2) (ts_symnext s2)
                     static_ltree static_dtree
                     (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3
                        (ts_bw s2))) in *.
        destruct Hl; subst last.
        -- cbn [Z.eqb]. cbv iota.
           cbn [ts_bw set_bw]. rewrite Einit. cbn [ts_bw set_bw].
           exists delta.
           split; [rewrite Hs, ?Fbw; reflexivity|].
           split; [exact Hw|].
           left.
           split; [reflexivity|].
           split.
           { intro suffix. exact (Hdec suffix). }
           { intros _ _ suffix. exact (Hdecs suffix). }
        -- cbn [Z.eqb]. cbv iota.
           cbn [ts_bw set_bw]. rewrite Einit. cbn [ts_bw set_bw].
           pose proof (bw_windup_stream b4 Hw) as Swind.
           exists (delta ++ repeat false (Z.to_nat (bw_pad b4))).
           split; [rewrite Swind, Hs, ?Fbw, app_assoc; reflexivity|].
           split; [apply bw_windup_wf|].
           right. right.
           split; [reflexivity|].
           split; [apply bw_windup_aligned|].
           exists (repeat false (Z.to_nat (bw_pad b4))).
           split; [rewrite repeat_length; exact (bw_pad_lt8 _ Hw)|].
           split.
           { intros suffix Hsuf.
             rewrite <- app_assoc.
             exact (Hdec (repeat false (Z.to_nat (bw_pad b4)) ++ suffix)). }
           { intros _ _ suffix Hsuf.
             rewrite <- app_assoc.
             exact (Hdecs (repeat false (Z.to_nat (bw_pad b4)) ++ suffix)). }
      * (* ---- DYNAMIC ---- *)
        cbv iota.
        destruct (Hdyn mbi s2 ltac:(try rewrite EP; reflexivity))
          as (delta & Hs & Hw & Hdec & Hdecs).
          change (compress_block (ts_symbuf s2) (ts_symnext s2)
                  (ts_trees s2 TK_L) (ts_trees s2 TK_D)
                  (send_all_trees (ts_maxcode s2 TK_L + 1)
                     (ts_maxcode s2 TK_D + 1) (mbi + 1)
                     (set_bw (bw_send_bits (Z.shiftl DYN_TREES 1 + last) 3
                        (ts_bw s2)) s2)))
          with (dyn_bw last mbi s2).
        destruct Hl; subst last.
        -- cbn [Z.eqb]. cbv iota.
           cbn [ts_bw set_bw]. rewrite Einit. cbn [ts_bw set_bw].
           exists delta.
           split; [rewrite Hs, ?Fbw; reflexivity|].
           split; [exact Hw|].
           left.
           split; [reflexivity|].
           split.
           { intro suffix. exact (Hdec suffix). }
           { intros HBK EFR suffix. exact (Hdecs HBK EFR suffix). }
        -- cbn [Z.eqb]. cbv iota.
           cbn [ts_bw set_bw]. rewrite Einit. cbn [ts_bw set_bw].
           pose proof (bw_windup_stream (dyn_bw 1 mbi s2) Hw) as Swind.
           exists (delta ++ repeat false (Z.to_nat (bw_pad (dyn_bw 1 mbi s2)))).
           split; [rewrite Swind, Hs, ?Fbw, app_assoc; reflexivity|].
           split; [apply bw_windup_wf|].
           right. right.
           split; [reflexivity|].
           split; [apply bw_windup_aligned|].
           exists (repeat false (Z.to_nat (bw_pad (dyn_bw 1 mbi s2)))).
           split; [rewrite repeat_length; exact (bw_pad_lt8 _ Hw)|].
           split.
           { intros suffix Hsuf.
             rewrite <- app_assoc.
             exact (Hdec (repeat false (Z.to_nat (bw_pad (dyn_bw 1 mbi s2)))
                            ++ suffix)). }
           { intros HBK EFR suffix Hsuf.
             rewrite <- app_assoc.
             exact (Hdecs HBK EFR
                      (repeat false (Z.to_nat (bw_pad (dyn_bw 1 mbi s2)))
                         ++ suffix)). }
  - (* no buf: straight to the Huffman choice *)
    cbv iota.
    destruct (Z.eqb (u64 (ts_statlen s2 + 3 + 7) / 8)
                (if (Z.leb (u64 (ts_statlen s2 + 3 + 7) / 8)
                       (u64 (ts_optlen s2 + 3 + 7) / 8))
                    || (Z.eqb strat Z_FIXED)
                 then u64 (ts_statlen s2 + 3 + 7) / 8
                 else u64 (ts_optlen s2 + 3 + 7) / 8)).
    + (* STATIC *)
      cbv iota.
      destruct (static_arm_dec_blk (ts_symbuf s2) (ts_symnext s2) toks
                  (ts_bw s2) last acc out
                  ltac:(rewrite Fbw; exact Hwf) Hl
                  ltac:(rewrite Fsb, Fsn; exact Hbuf) Henc Hres)
        as (delta & Hs & Hw & Hdec & Hdecs).
      set (b4 := compress_block (ts_symbuf s2) (ts_symnext s2)
                   static_ltree static_dtree
                   (bw_send_bits (Z.shiftl STATIC_TREES 1 + last) 3
                      (ts_bw s2))) in *.
      destruct Hl; subst last.
      * cbn [Z.eqb]. cbv iota.
        cbn [ts_bw set_bw]. rewrite Einit. cbn [ts_bw set_bw].
        exists delta.
        split; [rewrite Hs, ?Fbw; reflexivity|].
        split; [exact Hw|].
        left. split; [reflexivity|].
        split.
        { intro suffix. exact (Hdec suffix). }
        { intros _ _ suffix. exact (Hdecs suffix). }
      * cbn [Z.eqb]. cbv iota.
        cbn [ts_bw set_bw]. rewrite Einit. cbn [ts_bw set_bw].
        pose proof (bw_windup_stream b4 Hw) as Swind.
        exists (delta ++ repeat false (Z.to_nat (bw_pad b4))).
        split; [rewrite Swind, Hs, ?Fbw, app_assoc; reflexivity|].
        split; [apply bw_windup_wf|].
        right. right.
        split; [reflexivity|].
        split; [apply bw_windup_aligned|].
        exists (repeat false (Z.to_nat (bw_pad b4))).
        split; [rewrite repeat_length; exact (bw_pad_lt8 _ Hw)|].
        split.
        { intros suffix Hsuf.
          rewrite <- app_assoc.
          exact (Hdec (repeat false (Z.to_nat (bw_pad b4)) ++ suffix)). }
        { intros _ _ suffix Hsuf.
          rewrite <- app_assoc.
          exact (Hdecs (repeat false (Z.to_nat (bw_pad b4)) ++ suffix)). }
    + (* DYNAMIC *)
      cbv iota.
      destruct (Hdyn mbi s2 ltac:(try rewrite EP; reflexivity))
        as (delta & Hs & Hw & Hdec & Hdecs).
      change (compress_block (ts_symbuf s2) (ts_symnext s2)
                (ts_trees s2 TK_L) (ts_trees s2 TK_D)
                (send_all_trees (ts_maxcode s2 TK_L + 1)
                   (ts_maxcode s2 TK_D + 1) (mbi + 1)
                   (set_bw (bw_send_bits (Z.shiftl DYN_TREES 1 + last) 3
                      (ts_bw s2)) s2)))
        with (dyn_bw last mbi s2).
      destruct Hl; subst last.
      * cbn [Z.eqb]. cbv iota.
        cbn [ts_bw set_bw]. rewrite Einit. cbn [ts_bw set_bw].
        exists delta.
        split; [rewrite Hs, ?Fbw; reflexivity|].
        split; [exact Hw|].
        left. split; [reflexivity|].
        split.
        { intro suffix. exact (Hdec suffix). }
        { intros HBK EFR suffix. exact (Hdecs HBK EFR suffix). }
      * cbn [Z.eqb]. cbv iota.
        cbn [ts_bw set_bw]. rewrite Einit. cbn [ts_bw set_bw].
        pose proof (bw_windup_stream (dyn_bw 1 mbi s2) Hw) as Swind.
        exists (delta ++ repeat false (Z.to_nat (bw_pad (dyn_bw 1 mbi s2)))).
        split; [rewrite Swind, Hs, ?Fbw, app_assoc; reflexivity|].
        split; [apply bw_windup_wf|].
        right. right.
        split; [reflexivity|].
        split; [apply bw_windup_aligned|].
        exists (repeat false (Z.to_nat (bw_pad (dyn_bw 1 mbi s2)))).
        split; [rewrite repeat_length; exact (bw_pad_lt8 _ Hw)|].
        split.
        { intros suffix Hsuf.
          rewrite <- app_assoc.
          exact (Hdec (repeat false (Z.to_nat (bw_pad (dyn_bw 1 mbi s2)))
                         ++ suffix)). }
        { intros HBK EFR suffix Hsuf.
          rewrite <- app_assoc.
          exact (Hdecs HBK EFR
                   (repeat false (Z.to_nat (bw_pad (dyn_bw 1 mbi s2)))
                      ++ suffix)). }
Qed.

Print Assumptions tr_flush_block_bits.
