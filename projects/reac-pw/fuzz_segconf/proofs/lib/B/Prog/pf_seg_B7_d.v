(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 127 of its 152 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the vocabulary segment B7 of
   reac_segconf_parse_file's walk shares between its call sites and its runs. The B7 segment lane of the image-B G3 walk owner,
   2026-10-30. ADAPTED from the image-A G3 walk owner's image-A A7 segment lane lib/A/Prog/pf_a7_d.v (commit
   ebe0b30cca65): the same text over image B's lib/B/Prog/pf_pieces.v (a7_ -> b7_). Every fact here is about the
   cut predicates of pf_pieces.v (pf_base, pf_fsh, pf_shb, PF_SC_LINE) and the class-5 frame F, which image B lays
   at A's offsets (buf at F + 0x40, 512 bytes; the 144 shadow cells of pf_shb, plan section 1.3), so no number of
   image A is carried.

     b7_st  the part of a cut of B7 (pf_base) that no instruction of B7 changes: the journal from parse_file's
            entry with the class-5 frame (5, pos) owned and 0 events, the layout, the live blocks, the caller's
            objects and the frame's 144 shadow cells with buf IN scope.
     b7_buf  the address of buf (F + 0x40).
     b7_addr_buf / b7_fframe_buf  a range of buf is addressable with its shadow mapped (the inline checks B#8,
            B#12, B#20, B#21 and the interceptors' range checks), and lies in a LIVE side-stack frame
            (refuse_va_locs, trim's sa_dst).

   No instruction is walked here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c trim_c reac_segconf_parse_file_c SegInstB pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the class-5 frame is 64 << 5 bytes; its first 144 shadow cells are the ones pf_shb gives *)
Lemma b7_fb5 : fs_frame_bytes 5 = 2048.
Proof. reflexivity. Qed.

(* buf's shadow cells (8 .. 71) are 0 while buf is in scope *)
Lemma b7_shb_line : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof.
  intros i Hi. unfold pf_shb.
  destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 6) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 8) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 72) as [_|H]; [reflexivity|lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* buf: the 512-byte line buffer of parse_file's class-5 frame *)
Definition b7_buf (v : pfv) (pos : Z) : Z := pf_F v pos + PF_O_BUF.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* What a cut of A7 gives at every state of the segment that no call has left behind: the journal with the
   class-5 frame owned, the layout and blocks of the entry, the caller's objects, and the frame's shadow with
   buf in scope. Its fields are exactly the conjuncts of pf_pieces.v's pf_base that A7's call sites read. *)
Record b7_st (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) : Prop := mkA7St {
  b7_cx : pf_cx B v;
  b7_j : ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
           (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0;
  b7_lyc : lyc = p_ly v;
  b7_perm : Permutation (ablocks B lyc Sc) (ablocks B (p_ly v) (p_S v));
  b7_obj : pf_obj B v lyc Sc (rdW Wc memc);
  b7_fsh_line : pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC_LINE
}.

(* the allocator invariant at the cut's own state *)
Lemma b7_AR : forall v pos lyc Sc Wc memc mdc, b7_st v pos lyc Sc Wc memc mdc ->
  AR SEGS B lyc Sc Wc memc mdc.
Proof. intros v pos lyc Sc Wc memc mdc H. exact (proj1 (b7_j _ _ _ _ _ _ _ H)). Qed.

(* the class-5 frame is live at that state *)
Lemma b7_fin : forall v pos lyc Sc Wc memc mdc, b7_st v pos lyc Sc Wc memc mdc ->
  In (5, pos) (frames Sc).
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  pose proof (b7_j _ _ _ _ _ _ _ H) as (_ & _ & _ & _ & _ & Hfr & _).
  rewrite Hfr. left. reflexivity.
Qed.

(* where the frame lies *)
Lemma b7_frame_rng : forall v pos lyc Sc Wc memc mdc, b7_st v pos lyc Sc Wc memc mdc ->
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ in_app (pf_F v pos) 2048 /\
  pf_F v pos mod 32 = 0.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  pose proof (b7_AR v pos lyc Sc Wc memc mdc H) as HAR.
  pose proof (b7_fin v pos lyc Sc Wc memc mdc H) as Hfin.
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (H1 & H2 & H3).
  destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (H4 & _ & _ & _).
  pose proof (b7_lyc _ _ _ _ _ _ _ H) as Ely.
  rewrite b7_fb5 in H2, H3. unfold pf_F. rewrite <- Ely.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

(* buf's shadow cell for an address of buf *)
Lemma b7_sh_at : forall v pos lyc Sc Wc memc mdc x, b7_st v pos lyc Sc Wc memc mdc ->
  b7_buf v pos <= x < b7_buf v pos + 512 ->
  rdW Wc memc (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
  intros v pos lyc Sc Wc memc mdc x H Hx.
  destruct (b7_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & H2 & _ & H4).
  unfold b7_buf, PF_O_BUF in Hx.
  assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
  change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
  rewrite (b7_fsh_line _ _ _ _ _ _ _ H ((x - pf_F v pos) / 8)).
  - f_equal. apply b7_shb_line.
    split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
  - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* every byte of the frame's first 1152 bytes has a mapped shadow cell *)
Lemma b7_sh_some : forall v pos lyc Sc Wc memc mdc s, b7_st v pos lyc Sc Wc memc mdc ->
  pf_SH v pos <= s < pf_SH v pos + 144 -> rdW Wc memc s <> None.
Proof.
  intros v pos lyc Sc Wc memc mdc s H Hs.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (b7_fsh_line _ _ _ _ _ _ _ H (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.

(* a range of buf is addressable, with its shadow mapped: what every inline check of A7 and every range
   check of trim / strchr / strncasecmp / strlen / refuse asks *)
Lemma b7_addr_buf : forall v pos lyc Sc Wc memc mdc q n, b7_st v pos lyc Sc Wc memc mdc ->
  b7_buf v pos <= q -> 0 <= n -> q + n <= b7_buf v pos + 512 ->
  sa_addr (rdW Wc memc) q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  destruct (b7_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & H2 & H3 & H4).
  pose proof alloc_ceiling_lt as HC.
  unfold b7_buf, PF_O_BUF in Hq, Hqn.
  assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  split; [lia|]. split; [lia|].
  split.
  { apply amem_range_high; [lia| |lia].
    destruct H3 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia]. }
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    apply (b7_sh_at v pos lyc Sc Wc memc mdc x H). unfold b7_buf, PF_O_BUF. lia.
  - intros Hn0 s Hs.
    (* the 8-byte hull of [q, q + n) stays inside the frame's 144 shadow cells *)
    assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8).
    { unfold shadow_addr. replace q with (pf_F v pos + (q - pf_F v pos)) at 1 by lia.
      change (SHADOW_OFF + (pf_F v pos + (q - pf_F v pos)) / 8)
        with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q - pf_F v pos))).
      rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q - pf_F v pos) HF8). reflexivity. }
    assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8).
    { unfold shadow_addr. replace (q + n - 1) with (pf_F v pos + (q + n - 1 - pf_F v pos)) at 1 by lia.
      change (SHADOW_OFF + (pf_F v pos + (q + n - 1 - pf_F v pos)) / 8)
        with (shadow_of_addr SHADOW_OFF (pf_F v pos + (q + n - 1 - pf_F v pos))).
      rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (q + n - 1 - pf_F v pos) HF8). reflexivity. }
    assert (B1 : 8 <= (q - pf_F v pos) / 8)
      by (apply Z.div_le_lower_bound; lia).
    assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 72)
      by (apply Z.div_lt_upper_bound; lia).
    rewrite E1, E2 in Hs.
    apply (b7_sh_some v pos lyc Sc Wc memc mdc s H).
    pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
    lia.
Qed.

(* a range of buf lies in a live side-stack frame *)
Lemma b7_fframe_buf : forall v pos lyc Sc Wc memc mdc q n, b7_st v pos lyc Sc Wc memc mdc ->
  b7_buf v pos <= q -> 0 <= n -> q + n <= b7_buf v pos + 512 ->
  sa_fframe lyc Sc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  exists 5, pos. split; [exact (b7_fin v pos lyc Sc Wc memc mdc H)|].
  split; [lia|].
  pose proof (b7_lyc _ _ _ _ _ _ _ H) as Ely.
  unfold b7_buf, PF_O_BUF, pf_F in Hq, Hqn. rewrite <- Ely in Hq, Hqn.
  rewrite b7_fb5. lia.

Qed.

End e.
End f.
End d.
