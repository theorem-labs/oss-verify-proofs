(** * G3Event — one walk event is one decodable block on the wire.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G3 capstone.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The walk's [EvOk] snapshot carries everything [tr_flush_block_bits]
    asks: the token buffer, its resolution over the consumed input, and
    (for the stored branch) the window slice AS the input slice.  This
    file supplies the [flush_block_only] plumbing on top: the [win_take]
    buffer, the [flush_pending] drain (a [dst_stream] no-op), and the
    accumulated-stream statement the per-stream fold consumes.

    The decoder accumulator is pinned to [firstn fe_start done] and the
    output to [firstn fe_end done] — with EvTile these snap together
    across blocks. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream DeflateSpec Deflate Trees CbEmit
  CbFold StoredRt StreamPos.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  BtFrame G3Stored G3Static G3DynA G3Block SwEv Gap7Strict.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac dsimp :=
  cbn [d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm
       zs_in zs_done zs_out zs_availout zs_totalin zs_totalout zs_adler
       zs_datatype
       setZ_in setZ_done setZ_out setZ_availout setZ_totalin setZ_totalout
       setZ_adler setZ_datatype
       ls_blockstart ls_strstart ls_window setL_blockstart
       fst snd].

Lemma forall_firstn_b : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros P n l H; revert n; induction H as [|a l Ha Hl IH]; intro n;
    destruct n; simpl; auto.
Qed.

Lemma forall_skipn_b : forall (P : Z -> Prop) n (l : list Z),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros P n l H; revert n; induction H as [|a l Ha Hl IH]; intro n;
    destruct n; simpl; auto.
Qed.

Lemma firstn_split : forall (l : list Z) (a b : nat),
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  induction l as [|x l IH]; intros a b.
  - now rewrite !firstn_nil, skipn_nil, firstn_nil.
  - destruct a as [|a]; [reflexivity|].
    cbn [Nat.add firstn skipn].
    now rewrite IH.
Qed.

Lemma win_take_zlen : forall w base n,
  0 <= n -> zlen (win_take w base n) = n.
Proof.
  intros w base n Hn.
  unfold win_take, zlen.
  rewrite length_map, length_seq. lia.
Qed.

Theorem flush_block_only_bits : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g ->
  (0 <= ls_blockstart (d_ls (fe_s ev)) ->
   Z.leb (ls_strstart (d_ls (fe_s ev)) - ls_blockstart (d_ls (fe_s ev)) + 4)
     (if (Z.leb (u64 (ts_statlen (snd (build_bl_tree (build_tree TK_D
                   (build_tree TK_L (d_ts (fe_s ev)))))) + 3 + 7) / 8)
            (u64 (ts_optlen (snd (build_bl_tree (build_tree TK_D
                   (build_tree TK_L (d_ts (fe_s ev)))))) + 3 + 7) / 8))
         || (Z.eqb (dg_strategy (d_cfg (fe_s ev))) Z_FIXED)
      then u64 (ts_statlen (snd (build_bl_tree (build_tree TK_D
             (build_tree TK_L (d_ts (fe_s ev)))))) + 3 + 7) / 8
      else u64 (ts_optlen (snd (build_bl_tree (build_tree TK_D
             (build_tree TK_L (d_ts (fe_s ev)))))) + 3 + 7) / 8)
     = true ->
   fe_end ev - fe_start ev < 65536) ->
  Forall (fun b => 0 <= b < 256) done ->
  bw_wf (ts_bw (d_ts (fe_s ev))) ->
  (forall mbi s2,
     (mbi, s2) = build_bl_tree (build_tree TK_D
                    (build_tree TK_L (d_ts (fe_s ev)))) ->
     exists delta,
       bw_stream (dyn_bw (fe_last ev) mbi s2)
         = bw_stream (ts_bw (d_ts (fe_s ev))) ++ delta
       /\ bw_wf (dyn_bw (fe_last ev) mbi s2)
       /\ (forall suffix,
            dec_blk (delta ++ suffix)
              (firstn (Z.to_nat (fe_start ev)) done)
            = Some (Z.eqb (fe_last ev) 1,
                    firstn (Z.to_nat (fe_end ev)) done, suffix))
       /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
           forall suffix,
            dec_blk_strict (delta ++ suffix)
              (firstn (Z.to_nat (fe_start ev)) done)
            = Some (Z.eqb (fe_last ev) 1,
                    firstn (Z.to_nat (fe_end ev)) done, suffix))) ->
  exists delta,
    dst_stream (flush_block_only (fe_last ev) (fe_s ev))
      = dst_stream (fe_s ev) ++ delta
    /\ bw_wf (ts_bw (d_ts (flush_block_only (fe_last ev) (fe_s ev))))
    /\ ( (fe_last ev = 0
          /\ (forall suffix,
               dec_blk (delta ++ suffix)
                 (firstn (Z.to_nat (fe_start ev)) done)
               = Some (false, firstn (Z.to_nat (fe_end ev)) done, suffix))
          /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
              forall suffix,
               dec_blk_strict (delta ++ suffix)
                 (firstn (Z.to_nat (fe_start ev)) done)
               = Some (false, firstn (Z.to_nat (fe_end ev)) done, suffix)))
       \/ (fe_last ev = 0
          /\ (length (dst_stream (flush_block_only (fe_last ev) (fe_s ev)))
              mod 8 = 0)%nat
          /\ (forall suffix, (length suffix mod 8 = 0)%nat ->
               dec_blk (delta ++ suffix)
                 (firstn (Z.to_nat (fe_start ev)) done)
               = Some (false, firstn (Z.to_nat (fe_end ev)) done, suffix))
          /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
              forall suffix, (length suffix mod 8 = 0)%nat ->
               dec_blk_strict (delta ++ suffix)
                 (firstn (Z.to_nat (fe_start ev)) done)
               = Some (false, firstn (Z.to_nat (fe_end ev)) done, suffix)))
       \/ (fe_last ev = 1
          /\ (length (dst_stream (flush_block_only (fe_last ev) (fe_s ev)))
              mod 8 = 0)%nat
          /\ exists pad, (length pad < 8)%nat
             /\ (forall suffix, (length suffix mod 8 = 0)%nat ->
                  dec_blk (delta ++ suffix)
                    (firstn (Z.to_nat (fe_start ev)) done)
                  = Some (true, firstn (Z.to_nat (fe_end ev)) done,
                          pad ++ suffix))
             /\ (build_accepts_of_kraft_STMT -> EnoughFits_STMT ->
                 forall suffix, (length suffix mod 8 = 0)%nat ->
                  dec_blk_strict (delta ++ suffix)
                    (firstn (Z.to_nat (fe_start ev)) done)
                  = Some (true, firstn (Z.to_nat (fe_end ev)) done,
                          pad ++ suffix))) ).
Proof.
  intros g wrap done ev HE Hlevel Hspan Hbytes Hwf Hdyn.
  destruct HE as (Ecfg & Ewrap & Hbuf & Hfreq & Henc & Hsn & Hse & Hend
                  & Hres & Hspan_eq & Hwin & Hlast01).
  set (s := fe_s ev) in *.
  set (bs := ls_blockstart (d_ls s)) in *.
  set (slen := ls_strstart (d_ls s) - bs) in *.
  assert (Hl : fe_last ev = 0 \/ fe_last ev = 1) by lia.
  assert (Hslen : slen = fe_end ev - fe_start ev) by lia.
  assert (Hslen0 : 0 <= slen) by lia.
  (* acc ++ slice = out *)
  assert (Hsplit : firstn (Z.to_nat (fe_start ev)) done
                     ++ firstn (Z.to_nat (fe_end ev - fe_start ev))
                          (skipn (Z.to_nat (fe_start ev)) done)
                   = firstn (Z.to_nat (fe_end ev)) done).
  { rewrite <- firstn_split.
    f_equal. lia. }
  (* the stored-arm data facts: only demanded when the buffer EXISTS
     ([block_start >= 0]; it goes negative after a slide) AND the stored
     branch actually WINS its size test — the span bound is false
     otherwise (a long-match block can span megabytes) *)
  assert (HstoredF : forall dat,
            (if Z.leb 0 bs
             then Some (win_take (ls_window (d_ls s)) bs slen) else None)
            = Some dat ->
            Z.leb (slen + 4)
              (if (Z.leb (u64 (ts_statlen (snd (build_bl_tree
                            (build_tree TK_D (build_tree TK_L (d_ts s)))))
                          + 3 + 7) / 8)
                     (u64 (ts_optlen (snd (build_bl_tree
                            (build_tree TK_D (build_tree TK_L (d_ts s)))))
                          + 3 + 7) / 8))
                  || (Z.eqb (dg_strategy (d_cfg s)) Z_FIXED)
               then u64 (ts_statlen (snd (build_bl_tree
                      (build_tree TK_D (build_tree TK_L (d_ts s)))))
                    + 3 + 7) / 8
               else u64 (ts_optlen (snd (build_bl_tree
                      (build_tree TK_D (build_tree TK_L (d_ts s)))))
                    + 3 + 7) / 8) = true ->
            slen = zlen dat /\ 0 <= slen < 65536
            /\ Forall (fun b => 0 <= b < 256) dat
            /\ firstn (Z.to_nat (fe_start ev)) done ++ dat
               = firstn (Z.to_nat (fe_end ev)) done).
  { intros dat Edat Hguard.
    destruct (Z.leb_spec 0 bs) as [Hbs0|Hbs0]; [|discriminate].
    injection Edat as Edat. subst dat.
    pose proof (Hwin Hbs0) as Hdat.
    pose proof (Hspan Hbs0 Hguard) as Hspan'.
    split; [symmetry; apply win_take_zlen; exact Hslen0|].
    split; [lia|].
    split.
    - rewrite Hdat.
      apply forall_firstn_b, forall_skipn_b. exact Hbytes.
    - rewrite Hdat. exact Hsplit. }
  (* ---- the block dispatcher, at [d_ts s] ---- *)
  destruct (tr_flush_block_bits
              (if Z.leb 0 bs
               then Some (win_take (ls_window (d_ls s)) bs slen) else None)
              slen (fe_last ev) (dg_level (d_cfg s)) (dg_strategy (d_cfg s))
              (zs_datatype (d_strm s)) (d_ts s) (fe_toks ev)
              (firstn (Z.to_nat (fe_start ev)) done)
              (firstn (Z.to_nat (fe_end ev)) done)
              ltac:(rewrite Ecfg; exact Hlevel)
              Hwf Hl Hbuf Henc Hres HstoredF Hdyn)
    as (delta & Hs & Hw & Htri).
  (* ---- the [flush_block_only] plumbing ---- *)
  unfold flush_block_only. cbv zeta.
  fold s bs slen.
  set (r := tr_flush_block
              (if Z.leb 0 bs
               then Some (win_take (ls_window (d_ls s)) bs slen) else None)
              slen (fe_last ev) (dg_level (d_cfg s)) (dg_strategy (d_cfg s))
              (zs_datatype (d_strm s)) (d_ts s)) in *.
  set (s2d := setD_ls (setL_blockstart (ls_strstart (d_ls s)) (d_ls s))
                (setD_ts (snd r)
                   (setD_strm (setZ_datatype (fst r) (d_strm s)) s))).
  assert (E2ts : d_ts s2d = snd r) by reflexivity.
  assert (E2out : zs_out (d_strm s2d) = zs_out (d_strm s)) by reflexivity.
  assert (Hw2 : bw_wf (ts_bw (d_ts s2d))) by (rewrite E2ts; exact Hw).
  destruct (flush_pending_stream s2d Hw2) as [Sfp Wfp].
  exists delta.
  assert (Hdst : dst_stream (flush_pending s2d) = dst_stream s ++ delta).
  { rewrite Sfp. unfold dst_stream.
    rewrite E2ts, E2out, Hs, app_assoc. reflexivity. }
  split; [exact Hdst|].
  split; [exact Wfp|].
  (* the trichotomy, with the mod-8 clauses transported to [dst_stream] *)
  assert (Hmod8 : (length (bw_stream (ts_bw (snd r))) mod 8 = 0)%nat ->
                  (length (dst_stream (flush_pending s2d)) mod 8 = 0)%nat).
  { intro Hm.
    rewrite Sfp. unfold dst_stream.
    rewrite E2ts, E2out, length_app, bytes_bits_length.
    rewrite Nat.Div0.add_mod, Nat.mul_comm, Nat.Div0.mod_mul, Hm.
    reflexivity. }
  destruct Htri as [(Ez & Hd)|[(Ez & Hm & Hd)|(Ez & Hm & Hd)]].
  - left. split; [exact Ez|]. exact Hd.
  - right. left. split; [exact Ez|].
    split; [apply Hmod8; exact Hm|]. exact Hd.
  - right. right. split; [exact Ez|].
    split; [apply Hmod8; exact Hm|]. exact Hd.
Qed.

Print Assumptions flush_block_only_bits.
