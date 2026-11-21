(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateInitLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI5b.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac krefl := lazymatch goal with |- ?a = _ => exact_no_check (@eq_refl _ a) end.

Section Shape.
  Context {St : Type}.
  Variable H : zhooks St.

  Definition dinit_tail (ml lv st me : Z) (s : deflate_state) : SM St (option deflate_state * ZRet) :=
    do rw <- zalloc H (ds_w_size s) 2 ;
    let s := s_win s rw in
    do rp <- zalloc H (ds_w_size s) 2 ;
    let s := s_prv s rp in
    do rh <- zalloc H (ds_hash_size s) 2 ;
    let s := s_hd s rh in
    let s := s_lbs s ml in
    do rb <- zalloc H (ds_lit_bufsize s) LIT_BUFS ;
    let s := s_pb s rb in
    match ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s with
    | Some _, Some _, Some _, Some _ =>
        let '(s, rc) := deflateReset (s_fin s lv st me) in
        sret (Some s, zret_of_cs (ds_strm s) rc)
    | _, _, _, _ =>
        let s := s_fail s in
        do _ <- deflateEnd_core H s ;
        sret (None, zret_of_cs (ds_strm s) Z_MEM_ERROR)
    end.

  Definition dinit_prog (zc : ZCall) (level method windowBits memLevel strategy : Z)
    : SM St (option deflate_state * ZRet) :=
    let cs := cset_msg (cstrm_of_call zc) MSG_NULL in
    let level := if Z.eqb level Z_DEFAULT_COMPRESSION then 6 else level in
    let '(wrap, windowBits, bad) :=
      if Z.ltb windowBits 0 then (0, - windowBits, Z.ltb windowBits (-15))
      else if Z.ltb 15 windowBits then (2, windowBits - 16, false)
      else (1, windowBits, false) in
    if bad then sret (None, zret_of_cs cs Z_STREAM_ERROR)
    else if (memLevel <? 1) || (MAX_MEM_LEVEL <? memLevel) || negb (method =? Z_DEFLATED)
            || (windowBits <? 8) || (15 <? windowBits) || (level <? 0) || (9 <? level)
            || (strategy <? 0) || (Z_FIXED <? strategy) || ((windowBits =? 8) && negb (wrap =? 1))
    then sret (None, zret_of_cs cs Z_STREAM_ERROR)
    else
      let windowBits := if Z.eqb windowBits 8 then 9 else windowBits in
      do r0 <- zalloc H 1 SIZEOF_deflate_state ;
      match r0 with
      | None => sret (None, zret_of_cs cs Z_MEM_ERROR)
      | Some (b0, g0) => dinit_tail memLevel level strategy method (s_setup g0 b0 cs wrap windowBits memLevel)
      end.

End Shape.

Lemma dFg_strm b0 bw bp bh bb g0 gw gp gh gb cs wrap wb9 meml lv strat method :
  ds_strm (dFg b0 bw bp bh bb g0 gw gp gh gb cs wrap wb9 meml lv strat method)
  = cset_adler (cset_data_type (cset_msg (cset_total_out (cset_total_in cs 0) 0) MSG_NULL) Z_UNKNOWN)
               (if wrap =? 2 then crc32_init else adler32_init).
Proof. reflexivity. Qed.

Definition IRAW (cs : cstrm) (wrap wb9 ml lv st me : Z) (s1 s2 : deflate_state) : Prop :=
  exists b0 bw bp bh bb g0 gw gp gh gb g0' gw' gp' gh' gb',
    s1 = dFg b0 bw bp bh bb g0 gw gp gh gb cs wrap wb9 ml lv st me
    /\ s2 = dFg b0 bw bp bh bb g0' gw' gp' gh' gb' cs wrap wb9 ml lv st me.

Definition init_cs (cs : cstrm) (wrap : Z) : cstrm :=
  cset_adler (cset_data_type (cset_msg (cset_total_out (cset_total_in cs 0) 0) MSG_NULL) Z_UNKNOWN)
             (if wrap =? 2 then crc32_init else adler32_init).

Definition IQ (OK : Prop) (cs : cstrm) (wrap wb9 ml lv st me : Z) (p1 p2 : option deflate_state * ZRet) : Prop :=
  snd p1 = snd p2
  /\ match fst p1, fst p2 with
     | Some s1, Some s2 => OK /\ IRAW cs wrap wb9 ml lv st me s1 s2 /\ snd p1 = zret_of_cs (init_cs cs wrap) Z_OK
     | None, None => True
     | _, _ => False
     end.

Section TwoHooks.
  Context {St : Type}.
  Variable H1 : zhooks St.
Variable H2 : zhooks St.
  Hypothesis HZ : forall a b, srel (fun r1 r2 => option_map fst r1 = option_map fst r2) (zalloc H1 a b) (zalloc H2 a b).
  Hypothesis HF : forall b, srel eq (zfree H1 b) (zfree H2 b).

End TwoHooks.

Section ZcHooks.
  Context {MM : MallocModel}.
End ZcHooks.

Lemma dFg_dreach zc level method wb meml strategy b0 bw bp bh bb g0 gw gp gh gb :
  di_bad level method wb meml strategy = false -> 5 <= meml ->
  dreach (dFg b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method).
Proof.
  intros Hbad HML5.
  apply (DR_init zc level method wb meml strategy [Some (b0, g0); Some (bw, gw); Some (bp, gp); Some (bh, gh); Some (bb, gb)] _
           (zret_of_cs (ds_strm (dFg b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method)) Z_OK)); [exact HML5|].
  rewrite (dinit_run zc level method wb meml strategy _ Hbad). cbn [ohd otl].
  pose proof (S5og_proj b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (Some (bw, gw)) (Some (bp, gp)) (Some (bh, gh)) (Some (bb, gb))) as PJ.
  cbv zeta in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
  unfold dinit_body, all_some. rewrite Ew, Ep, Eh, Eb. cbn [option_map fst].
  change (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (Some (bw, gw)) (Some (bp, gp)) (Some (bh, gh)) (Some (bb, gb)))
    with (S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml).
  rewrite (reset_S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method (proj1 (di_wrap_range wb))).
  reflexivity.
Qed.

Section Facts.
  Variable b0 : blk.
Variable bw : blk.
Variable bp : blk.
Variable bh : blk.
Variable bb : blk.
Variable cs : cstrm.
Variable lv : Z.
  Hypothesis Hlv : 0 <= lv <= 9.
  Hypothesis Hain : 0 <= cs_avail_in cs.
  Hypothesis Haout : 0 <= cs_avail_out cs.

  Section One.
    Variable g0 : Z -> Z.
Variable gw : Z -> Z.
Variable gp : Z -> Z.
Variable gh : Z -> Z.
Variable gb : Z -> Z.
    Let F := dFg b0 bw bp bh bb g0 gw gp gh gb cs 1 15 8 lv 0 8.

    Lemma dFg_lens :
      arr_len (ds_window F) = 65536 /\ arr_len (ds_prev F) = 32768 /\ arr_len (ds_head F) = 32768 /\ arr_len (ds_pending_buf F) = 65536
      /\ arr_len (ds_dyn_ltree_fc F) = 573 /\ arr_len (ds_dyn_dtree_fc F) = 61 /\ arr_len (ds_bl_tree_fc F) = 39.
    Proof.
      unfold F, dFg. cbn [ds_window ds_prev ds_head ds_pending_buf ds_dyn_ltree_fc ds_dyn_dtree_fc ds_bl_tree_fc].
      unfold blk_bytes, blk_ush, arr_u16_of. rewrite ?arr_len_fill, ?arr_len_set, ?arr_len_fill, !arr_len_init. repeat split; reflexivity.
    Qed.

    Lemma dFg_head0' h : 0 <= h < 32768 -> arr_get (ds_head F) h = 0.
    Proof.
      intros Hh. unfold F, dFg. cbn [ds_head]. apply (cleared_get (blk_ush gh (Z.shiftl 1 (8 + 7)))); [| exact Hh].
      unfold blk_ush. rewrite arr_len_init. reflexivity.
    Qed.

    Lemma dFg_INV : INV F.
    Proof.
      pose proof dFg_lens as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
      pose proof (dFg_dwf b0 bw bp bh bb g0 gw gp gh gb cs 1 15 8 lv 0 8 ltac:(lia) ltac:(lia) Hlv ltac:(lia) ltac:(lia) eq_refl) as D.
      pose proof (df_tl _ D) as TL. clear D. revert L1 L2 L3 L4 L5 L6 L7 TL.

      unfold F, dFg, tree_lens.
      cbn [ds_w_size ds_w_mask ds_w_bits ds_window_size ds_hash_size ds_hash_mask ds_hash_bits ds_hash_shift ds_lit_bufsize
           ds_pending_buf_size ds_sym_end ds_window ds_prev ds_head ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc
           ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth ds_strstart ds_lookahead ds_insert ds_high_water
           ds_strm ds_opt_len ds_static_len ds_match_length ds_prev_length ds_strategy ds_pending ds_pending_out
           cs_avail_in cs_avail_out cset_adler cset_data_type cset_msg cset_total_out cset_total_in].
      intros L1 L2 L3 L4 L5 L6 L7 TL.
      constructor;
        [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | reflexivity | reflexivity
        | exact L1 | exact L2 | exact L3 | exact L4 | exact TL
        | cbn [ds_strstart]; lia | cbn [ds_lookahead]; lia | cbn [ds_insert ds_strstart]; lia | cbn [ds_strstart ds_lookahead]; lia
        | cbn [ds_high_water]; lia
        | cbn [ds_strm cs_avail_in cset_adler cset_data_type cset_msg cset_total_out cset_total_in]; destruct cs; cbn in Hain |- *; exact Hain
        | cbn [ds_opt_len]; lia | cbn [ds_static_len]; lia
        | cbn [ds_match_length]; unfold MIN_MATCH; lia | cbn [ds_prev_length]; unfold MIN_MATCH; lia
        | reflexivity | cbn [ds_pending]; lia | cbn [ds_pending ds_pending_out]; intros _; reflexivity
        | cbn [ds_strm cs_avail_out cset_adler cset_data_type cset_msg cset_total_out cset_total_in]; destruct cs; cbn in Haout |- *; exact Haout ].
    Qed.
  End One.

  Local Ltac proj_cbn :=
    cbn [ds_status ds_pending_buf ds_pending_buf_size ds_pending_out ds_pending ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush
         ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift
         ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length
         ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_dyn_ltree_fc ds_dyn_ltree_dl
         ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_l_max_code ds_d_max_code ds_bl_max_code ds_bl_count ds_heap
         ds_heap_len ds_heap_max ds_depth ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf
         ds_bi_valid ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm].

  Lemma dFg_REL g0 gw gp gh gb g0' gw' gp' gh' gb' :
    REL (fun i => i < 0) (fun _ => False) (fun _ => False) 0 false false
        (dFg b0 bw bp bh bb g0 gw gp gh gb cs 1 15 8 lv 0 8) (dFg b0 bw bp bh bb g0' gw' gp' gh' gb' cs 1 15 8 lv 0 8).
  Proof.
    pose proof (dFg_lens g0 gw gp gh gb) as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
    pose proof (dFg_lens g0' gw' gp' gh' gb') as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    pose proof (dFg_head0' g0 gw gp gh gb) as Z1. pose proof (dFg_head0' g0' gw' gp' gh' gb') as Z2.
    revert L1 L2 L3 L4 L5 L6 L7 M1 M2 M3 M4 M5 M6 M7 Z1 Z2.
    unfold dFg. proj_cbn. intros L1 L2 L3 L4 L5 L6 L7 M1 M2 M3 M4 M5 M6 M7 Z1 Z2.
    constructor; proj_cbn.
    - unfold clean. proj_cbn. reflexivity.
    - split; [rewrite L1, M1; reflexivity | intros i Hi Hlt; exfalso; lia].
    - split; [rewrite L3, M3; reflexivity | intros i Hi _]. rewrite L3 in Hi. rewrite Z1, Z2 by exact Hi. reflexivity.
    - split; [rewrite L2, M2; reflexivity | intros i _ Hf; destruct Hf].
    - split; [| intros p Hf; destruct Hf]. intros h Hh. unfold cv. proj_cbn. rewrite Z1 by exact Hh. split; [lia | left; reflexivity].
    - split; [rewrite L4, M4; reflexivity | intros i _ Hf; destruct Hf].
    - split; [rewrite L5, M5; reflexivity | intros i Hi Hlt]. rewrite L5 in Hi.
      rewrite !arr_get_set, !arr_get_fill. unfold arr_inb. rewrite !arr_len_fill. unfold arr_u16_of. rewrite !arr_len_init.
      unfold L_CODES, END_BLOCK in *.
      destruct (Z.eqb_spec 256 i); cbn [andb].
      + replace ((0 <=? 256) && (256 <? 573)) with true by reflexivity. reflexivity.
      + replace ((0 <=? i) && (i <? 0 + Z.max 0 286) && ((0 <=? i) && (i <? 573))) with true
          by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - split; [rewrite L6, M6; reflexivity | intros i Hi Hlt]. rewrite L6 in Hi.
      rewrite !arr_get_fill. unfold arr_inb. unfold arr_u16_of. rewrite !arr_len_init. unfold D_CODES in *.
      replace ((0 <=? i) && (i <? 0 + Z.max 0 30) && ((0 <=? i) && (i <? 61))) with true
        by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - split; [rewrite L7, M7; reflexivity | intros i Hi Hlt]. rewrite L7 in Hi.
      rewrite !arr_get_fill. unfold arr_inb. unfold arr_u16_of. rewrite !arr_len_init. unfold BL_CODES in *.
      replace ((0 <=? i) && (i <? 0 + Z.max 0 19) && ((0 <=? i) && (i <? 39))) with true
        by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - intros E; discriminate E.
    - intros E; discriminate E.
    - unfold MIN_MATCH. intros; exfalso; lia.
    - unfold MIN_MATCH. intros; exfalso; lia.
    - intros E; discriminate E.
  Qed.

  Lemma dFg_DQ g0 gw gp gh gb g0' gw' gp' gh' gb' :
    DQ (dFg b0 bw bp bh bb g0 gw gp gh gb cs 1 15 8 lv 0 8) (dFg b0 bw bp bh bb g0' gw' gp' gh' gb' cs 1 15 8 lv 0 8).
  Proof.
    exists (fun i => i < 0), (fun _ => False), (fun _ => False), 0, false, false.
    split; [apply dFg_REL|]. unfold WHI, SYMB, HWI, dFg. proj_cbn.
    split; [intros i Hi; lia|]. split; [intros _; lia|]. split; [intros; lia|]. split; [intros; lia | apply HWI4_look0].
  Qed.
End Facts.

Definition ISTRM (z : zstrm) : Prop := zstrm_okP z /\ zs_total_out z = 0 /\ zs_total_in z = 0.
