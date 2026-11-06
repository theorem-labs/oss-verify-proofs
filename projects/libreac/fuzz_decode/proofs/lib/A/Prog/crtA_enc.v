(* crtA_enc: the image-A part of the braid/encoder math of check_round_trip: the lemmas over rsegs and over
   lib/A/Prog/check_braid_c.v's braid_off and braid_map. The image-free part is lib/Lib/CrtEnc.v.

   PORT of a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:1-355.
   Lemma names, statements and proofs are the record's; each block below cites its source lines.
   Changes, all in the imports: lib/A/AsanCells.v in place of the record's old-lane runtime-cells file (built on
   the toolchain-N pin; not on this branch and not Required here); lib/Lib/CrtEnc.v in place of StrFun and
   crt_convert (this file used only s24, byte_range and memcmp_model from them; CrtEnc.v holds memcmp_model and
   re-exports lib/Lib/CrtS24.v, which holds s24 and byte_range, all with the record's text).
   Kept here and not generalised over the segment list: crt_rd, crt_rd_some, crt_list, crt_list_len and
   crt_list_bytes. Generalising them adds the segment list as an argument and changes the record's call forms
   (crt_rd m pcm i, crt_list_bytes m m' base A n ...) that the downstream walk uses. braid_off_at is here
   because braid_off is image A's (lib/A/Prog/check_braid_c.v). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import FloatExact RcBraid RcBraidLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import CrtEnc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_braid_c.
Import ListNotations.
Open Scope Z_scope.

(* braid_off_at: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:223-228. *)
Lemma braid_off_at : forall N s ch j, 0 <= ch -> 0 <= j < 3 ->
  3 * (s * N + 2 * (ch / 2)) + braid_off ch j = rb_at N s ch j.
Proof.
  intros N s ch j Hch Hj. rewrite rb_at_eq by lia. unfold braid_off, rb_off. rewrite (Zmod_even ch).
  destruct (Z.even ch); destruct (j =? 0); destruct (j =? 1); lia.
Qed.

(* crt_rd: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:268-269. *)
Definition crt_rd (m : word -> option byte) (base i : Z) : byte :=
  match mrd rsegs m (wa (base + i)) with Some b => b | None => Z_to_bv 8 0 end.

(* crt_rd_some, crt_pcm_ok, crt_audio_hit, crt_audio_ok, crt_out: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:274-333. *)
Lemma crt_rd_some : forall m base i b, mrd rsegs m (wa (base + i)) = Some b -> crt_rd m base i = b.
Proof. intros m base i b H. unfold crt_rd. rewrite H. reflexivity. Qed.

Lemma crt_pcm_ok : forall m audio pcm nch ns, 1 <= nch -> 1 <= ns -> braid_map m audio pcm nch ns ->
  forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m (wa (pcm + i)) = Some (crt_rd m pcm i).
Proof.
  intros m audio pcm nch ns HN HS BR i Hi.
  set (ch := i / (3 * ns)). set (r := i mod (3 * ns)).
  assert (D1 : i = 3 * ns * ch + r) by (apply Z.div_mod; lia).
  assert (R1 : 0 <= r < 3 * ns) by (apply Z.mod_pos_bound; lia).
  assert (Rc : 0 <= ch < nch) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  set (s := r / 3). set (j := r mod 3).
  assert (D2 : r = 3 * s + j) by (apply Z.div_mod; lia).
  assert (Rj : 0 <= j < 3) by (apply Z.mod_pos_bound; lia).
  assert (Rs : 0 <= s < ns) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (BR ch s j Rc Rs Rj) as (b & H1 & _).
  assert (E : pcm + 3 * (ch * ns + s) + j = pcm + i) by lia.
  rewrite E in H1. rewrite H1. rewrite (crt_rd_some m pcm i b H1). reflexivity.
Qed.

Lemma crt_audio_hit : forall m audio pcm nch ns, 2 <= nch -> nch mod 2 = 0 -> 1 <= ns -> braid_map m audio pcm nch ns ->
  forall i, 0 <= i < 3 * nch * ns -> exists s ch j, 0 <= s < ns /\ 0 <= ch < nch /\ 0 <= j < 3 /\
    i = rb_at nch s ch j /\
    mrd rsegs m (wa (audio + i)) = Some (crt_rd m pcm (3 * (ch * ns + s) + j)) /\
    mrd rsegs m (wa (pcm + (3 * (ch * ns + s) + j))) = Some (crt_rd m pcm (3 * (ch * ns + s) + j)).
Proof.
  intros m audio pcm nch ns HN HE HS BR i Hi.
  destruct (rb_cover nch ns i HN HE HS Hi) as (s & ch & j & Hs & Hch & Hj & Ei).
  destruct (BR ch s j Hch Hs Hj) as (b & H1 & H2).
  assert (EP : pcm + 3 * (ch * ns + s) + j = pcm + (3 * (ch * ns + s) + j)) by lia.
  rewrite EP in H1.
  assert (EA : audio + 3 * (s * nch + 2 * (ch / 2)) + braid_off ch j = audio + i).
  { rewrite Ei, <- (braid_off_at nch s ch j) by lia. lia. }
  rewrite EA in H2.
  exists s, ch, j. rewrite (crt_rd_some m pcm _ b H1).
  split; [exact Hs|]. split; [exact Hch|]. split; [exact Hj|]. split; [exact Ei|].
  split; [exact H2 | exact H1].
Qed.

Lemma crt_audio_ok : forall m audio pcm nch ns, 2 <= nch -> nch mod 2 = 0 -> 1 <= ns -> braid_map m audio pcm nch ns ->
  forall i, 0 <= i < 3 * nch * ns -> mrd rsegs m (wa (audio + i)) = Some (crt_rd m audio i).
Proof.
  intros m audio pcm nch ns HN HE HS BR i Hi.
  destruct (crt_audio_hit m audio pcm nch ns HN HE HS BR i Hi) as (s & ch & j & _ & _ & _ & _ & H & _).
  rewrite H. rewrite (crt_rd_some m audio i _ H). reflexivity.
Qed.

Lemma crt_out : forall m mm O audio pcm nch ns, 2 <= nch -> nch mod 2 = 0 -> 1 <= ns ->
  0 <= O -> O + 3 * nch * ns <= 2^64 -> braid_map m audio pcm nch ns ->
  forall i, 0 <= i < 3 * nch * ns ->
    rb_enc mm (rb_rows O nch (crt_K (crt_rd m pcm) ns) (Z.to_nat ns)) (wa (O + i)) = Some (crt_rd m audio i).
Proof.
  intros m mm O audio pcm nch ns HN HE HS H0 H1 BR i Hi.
  destruct (crt_audio_hit m audio pcm nch ns HN HE HS BR i Hi) as (s & ch & j & Hs & Hch & Hj & Ei & HA & _).
  rewrite (crt_rd_some m audio i _ HA).
  rewrite Ei. rewrite rb_rows_at; try lia.
  unfold crt_K. rewrite s24_byte by exact Hj. f_equal.
  assert (C : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct C as [-> | [-> | ->]]; cbn [Z.eqb]; f_equal; lia.
Qed.

(* crt_list, crt_list_len: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:335-339. *)
Definition crt_list (m : word -> option byte) (base n : Z) : list byte :=
  map (fun k => crt_rd m base (Z.of_nat k)) (seq 0 (Z.to_nat n)).

Lemma crt_list_len : forall m base n, length (crt_list m base n) = Z.to_nat n.
Proof. intros. unfold crt_list. rewrite length_map, length_seq. reflexivity. Qed.

(* crt_list_bytes: verbatim from a working branch dc455613c81:proofs/libreac/fuzz_decode/lib/A/Prog/crt_enc.v:347-355. *)
Lemma crt_list_bytes : forall m m' base A n, 0 <= A -> 0 <= n -> A + n <= 2^64 ->
  (forall i, 0 <= i < n -> mrd rsegs m' (wa (A + i)) = Some (crt_rd m base i)) ->
  bytes_at rsegs m' A (crt_list m base n).
Proof.
  intros m m' base A n H0 Hn H1 H. split; [exact H0|]. rewrite crt_list_len. split; [lia|].
  intros i Hi. unfold crt_list.
  rewrite nth_error_map, nth_seq0 by exact Hi. cbn [option_map].
  apply H. lia.
Qed.
