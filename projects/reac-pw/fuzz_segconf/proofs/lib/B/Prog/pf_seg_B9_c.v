(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 590 of its 615 lines of code are new or changed and 493 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the vocabulary
   segment B9 of reac_segconf_parse_file's walk shares between its call sites and its runs, and what its three
   INTERCEPTOR calls ask (a B9 sub-lane of the image-B G3 walk owner, 2026-10-30). proves no function (kind: segment
   lemma of reac_segconf_parse_file's walk: call-site premises of segment B9, image B). No instruction is walked.
   ADAPTED from the image-A G3 walk owner's image-A files lib/A/Prog/pf_a7_d.v + lib/A/Prog/pf_a7_r.v (commit
   a78dafc7ecfa, the image-A A7 segment lane): the same lemmas with a7_ renamed b9_, over image B's pf_pieces.v (the realigned base
   pf_s1 = (sp0 - 0x160) & -32, STK_reac_segconf_parse_file = 12832, SegInstB's values), and the call sites
   replaced by B9's; plus the cur_name facts B9's shared key refusal KREF needs.

   B9 is the key branch: KEY 0x883f8 -> ROLE 0x88630, MODEL 0x886d4, IGN 0x887e0, REF3 0x882b4 (no '='), HREF
   0x885ec (cur = NULL) or KREF 0x889a0 -> TAIL. Its calls (image-B excerpt
   reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     strchr      0x88400  `li a1,61` 0x883f8, `mv a0,s7` 0x883fc   RtSeg.astrchr_realizes      window 2 * ESTACK
     trim        0x88424 (a0 = s7 = the line), 0x88434 (a0 = eq + 1)                  (pf_seg_B9_cs.v)
     strlen      0x8843c  a0 = s3 = vp0 (0x88438)                  RtString.astrlen_realizes   window ESTACK
     strcasecmp  0x88584 / 0x88598 / 0x885ac / 0x885c0, a0 = s7 = the key, a1 = "role" 0x21760 / "model"
                 0x21800 / "ignore" 0x218e0 / "knock" 0x21960      RtSeg.astrcasecmp_realizes  window 2 * ESTACK
     refuse      KREF 0x889a0 (a3 = slot 0x40 = cur_name, a4 = val or key)               (pf_seg_B9_cs.v)
   Every string B9 hands to a callee lies in parse_file's buf[512] (F + 0x40, the class-5 frame F = pf_F v pos),
   except refuse's cur_name (F + 0x20, 16 bytes) and the four .rodata literals. What the calls need of those is the
   same at every site, so it is derived once here:

     b9_st  the part of a cut of B9 (pf_pieces.v's pf_base at PF_SC_LINE) that no instruction of B9 changes: pf_cx,
            the journal from parse_file's entry with the class-5 frame (5, pos) owned and 0 events, the layout, the
            live blocks, the caller's objects (pf_obj) and the frame's 144 shadow cells with cur_name and buf IN
            scope (pf_fsh .. PF_SC_LINE). b9_st_of_base takes it out of pf_base.
     b9_addr_buf / b9_addr_cn, b9_fframe_buf / b9_fframe_cn  a range of buf / cur_name is addressable with its
            shadow mapped (pf_shb cells 8..71 / 4..5 are 0 under PF_SC_LINE) and lies in a LIVE side-stack frame.
     b9_astr_of_sa, b9_read_ok_of_addr, b9_rom_st, b9_stk, b9_win, b9_frame_some, b9_read_ok_buf / b9_read_ok_cn,
            b9_amem_frame, b9_tail_vis_buf / b9_tail_vis_cn, b9_ecall_pre_buf, b9_lit_read: the parts of RtDefs.v's
            premises (aread_ok, astr_at, amem_range, atail_vis, ecall_pre_stk, rt_rom_view), as pf_a7_r.v's.
            b9_stk: sp0 - 368 <= s1 <= sp0 - 352 (image A: 336 .. 320); b9_win: a call at s1 with a window
            stk <= 3 * ESTACK fits STK 12832 = 352 + 16 + 12464 (SegInstB.STK_values).
     b9_nm_str_st  pf_nm (cur_name holds nm, seg_spec.cstr_enc 16) gives sa_str at F + 0x20 and length nm < 16.
     b9_strchr_pre_88400 / b9_strlen_pre_8843c / b9_strcasecmp_pre  each call's premise list, in the order its
            _realizes text states it (lib/B/Rt/RtSeg.v rows 6 and 10, lib/B/Rt/RtString.v astrlen_realizes).
     b9_obj_low, b9_keep_art  after an art_post call (aj_art_at / aj_art_atF) b9_st holds again at the call's
            new memory, from the journal step and the keep clause outside the window.

   POSITIONAL NAMES carried from the A files, checked against image B: PF_O_BUF = 0x40 and PF_O_CN = 0x20 (B's
   pf_pieces.v, from B's frame description string 0x11b81: the same offsets as A's); pf_shb's cells 4..5 (cur_name)
   and 8..71 (buf) (B's pf_pieces.v, plan section 1.3); STK_values' fourth conjunct is STK_reac_segconf_parse_file
   in B's SegInstB.v as in A's SegInstA.v; RLO_A / RHI_A = SEG_RLO / SEG_RHI = 0xa1c60 / 0xa3f08 (B's SegGlob.v). No
   region letter, listing object number or STK row of an A table is used.

   No Section hypothesis: the file is closed over the listing instance PI and the symbols B. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase
  reac_segconf_parse_file_c SegInstB pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaArt reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the class-5 frame is 64 << 5 bytes; its first 144 shadow cells are the ones pf_shb gives *)
Lemma b9_fb5 : fs_frame_bytes 5 = 2048.
Proof. reflexivity. Qed.

(* buf's shadow cells (8 .. 71) are 0 while buf is in scope *)
Lemma b9_shb_line : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof.
  intros i Hi. unfold pf_shb.
  destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 6) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 8) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 72) as [_|H]; [reflexivity|lia].
Qed.

(* cur_name's shadow cells (4 .. 5) are 0 while cur_name is in scope (sc_cn PF_SC_LINE = true) *)
Lemma b9_shb_cn : forall i, 4 <= i < 6 -> pf_shb PF_SC_LINE i = 0.
Proof.
  intros i Hi. unfold pf_shb.
  destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
  destruct (Z.ltb_spec i 6) as [_|H]; [reflexivity|lia].
Qed.

(* the 8-byte shadow hull of a sub-range lies inside the hull of the range *)
Lemma b9_hull_sub : forall (rd : reader) q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' ->
  q' + n' <= q + n -> shadow_hull_vis rd q' n'.
Proof.
  intros rd q n q' n' H Hq Hn Hle s Hs. apply H.
  pose proof (shadow_mono q q' Hq) as M1.
  pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
  assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
    by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* sa_addr of a sub-range *)
Lemma b9_sa_addr_sub : forall (rd : reader) q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' ->
  q' + n' <= q + n -> sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (A0 & A1 & A2 & A3 & A4) Hq Hn Hle.
  split; [lia|]. split; [lia|].
  split; [unfold amem_range in *; destruct A2 as [A2|A2]; [left; lia | right; lia]|].
  split; [eapply range_addressable_sub; [exact A3 | lia | lia]|].
  intros Hn'. exact (b9_hull_sub rd q n q' n' (A4 ltac:(lia)) Hq Hn' Hle).
Qed.

(* every byte of a C string and its NUL is mapped *)
Lemma b9_str_some : forall (rd : reader) p s a, sa_str rd p s -> p <= a <= p + Z.of_nat (length s) ->
  rd a <> None.
Proof.
  intros rd p s a [[Hz _] _] Ha.
  assert (Hi : (Z.to_nat (a - p) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (Hz _ Hi) as E. rewrite Z2Nat.id in E by lia.
  replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
Qed.

(* the i-th value of a byte list (sa_bytes reads nth i bs ZB0, seg_spec.zs its values with default 0) *)
Lemma b9_nth_zs : forall (f : list byte) i, (i < length f)%nat ->
  nth i (seg_spec.zs f) 0 = bv_unsigned (nth i f ZB0).
Proof.
  unfold seg_spec.zs. induction f as [|b f IH]; intros [|i] Hi; cbn [length map nth] in Hi |- *;
    [lia | lia | reflexivity | apply IH; lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* buf: the 512-byte line buffer of parse_file's class-5 frame; cur_name: its 16-byte name buffer *)
Definition b9_bufp (v : pfv) (pos : Z) : Z := pf_F v pos + PF_O_BUF.
Definition b9_cnp (v : pfv) (pos : Z) : Z := pf_F v pos + PF_O_CN.

(** ** The text bridge: sa_str (list Z) to astr_at / astr_atR (list byte) *)
Lemma b9_astr_of_sa : forall (W : world SEGS) mem q l,
  sa_str (rdW W mem) q l ->
  astr_at SEGS W mem q (seg_spec.zb l) /\ astr_atR (rdW W mem) q (seg_spec.zb l) /\
  astr_len (seg_spec.zb l) = Z.of_nat (length l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  atail_vis SEGS W mem (q + astr_len (seg_spec.zb l)).
Proof.
  intros W mem q l [Hz Ht].
  destruct (sa_strz_bytes SEGS (w_H W) mem q l Hz) as (Hb & Hn & Hzs).
  assert (HR : astr_atR (rdW W mem) q (seg_spec.zb l)) by (split; [exact Hb | exact Hn]).
  assert (HL : astr_len (seg_spec.zb l) = Z.of_nat (length l))
    by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
  split; [apply astr_atR_view; exact HR|].
  split; [exact HR|]. split; [exact HL|]. split; [exact Hzs|].
  rewrite HL. exact Ht.
Qed.

(** ** A range parse_file's memory holds, as aread_ok *)
Lemma b9_read_ok_of_addr : forall (W : world SEGS) regs mem stk q n,
  sa_addr (rdW W mem) q n -> 0 <= n < 2 ^ 32 ->
  (forall a, q <= a < q + n -> rdW W mem a <> None) -> q + n <= spZ regs - stk ->
  aread_ok SEGS stk W regs mem q n.
Proof.
  intros W regs mem stk q n (A0 & A1 & A2 & A3 & A4) Hn Hm Hw.
  split; [exact A0|]. split; [exact A1|]. split; [exact Hn|].
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  intros a Ha. split; [exact (Hm a Ha)|]. unfold ascratch_stk. lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** 1. The state every site of B9 shares *)
(* What a cut of B9 gives at every state of the segment that no call has left behind: the entry facts, the journal
   with the class-5 frame owned, the layout and blocks of the entry, the caller's objects, and the frame's shadow
   with cur_name and buf in scope. Its fields are exactly the conjuncts of pf_pieces.v's pf_base that B9's call
   sites read. *)
Record b9_st (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) : Prop := mkB9St {
  b9_cx : pf_cx B v;
  b9_j : ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
           (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0;
  b9_lyc : lyc = p_ly v;
  b9_perm : Permutation (ablocks B lyc Sc) (ablocks B (p_ly v) (p_S v));
  b9_obj : pf_obj B v lyc Sc (rdW Wc memc);
  b9_fsh_line : pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC_LINE
}.

(* the part of a cut of B9 that b9_st names, out of pf_base (B's pf_fi: journal, lyc, set_fs, Permutation, ...) *)
Lemma b9_st_of_base : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> b9_st v pos lyc Sc Wc memc mdc.
Proof.
  intros v pos lyc Sc Wc rX memc mdc (HCX & (HJ & Hly & _ & Hperm & _) & HOBJ & _ & HFSH).
  constructor; [exact HCX | exact HJ | exact Hly | exact Hperm | exact HOBJ | exact HFSH].
Qed.

(* the allocator invariant at the cut's own state *)
Lemma b9_AR : forall v pos lyc Sc Wc memc mdc, b9_st v pos lyc Sc Wc memc mdc ->
  AR SEGS B lyc Sc Wc memc mdc.
Proof. intros v pos lyc Sc Wc memc mdc H. exact (proj1 (b9_j _ _ _ _ _ _ _ H)). Qed.

(* the class-5 frame is live at that state *)
Lemma b9_fin : forall v pos lyc Sc Wc memc mdc, b9_st v pos lyc Sc Wc memc mdc ->
  In (5, pos) (frames Sc).
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  pose proof (b9_j _ _ _ _ _ _ _ H) as (_ & _ & _ & _ & _ & Hfr & _).
  rewrite Hfr. left. reflexivity.
Qed.

(* where the frame lies *)
Lemma b9_frame_rng : forall v pos lyc Sc Wc memc mdc, b9_st v pos lyc Sc Wc memc mdc ->
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ in_app (pf_F v pos) 2048 /\
  pf_F v pos mod 32 = 0.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  pose proof (b9_AR v pos lyc Sc Wc memc mdc H) as HAR.
  pose proof (b9_fin v pos lyc Sc Wc memc mdc H) as Hfin.
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (H1 & H2 & H3).
  destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (H4 & _ & _ & _).
  pose proof (b9_lyc _ _ _ _ _ _ _ H) as Ely.
  rewrite b9_fb5 in H2, H3. unfold pf_F. rewrite <- Ely.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

(* the frame's shadow base is a multiple of 4 (F mod 32 = 0, SHADOW_OFF = 0x7fff8000) *)
Lemma b9_SH4 : forall v pos lyc Sc Wc memc mdc, b9_st v pos lyc Sc Wc memc mdc ->
  exists m, pf_SH v pos = 4 * m.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (_ & _ & _ & H4).
  exists (0x1fffe000 + pf_F v pos / 32).
  unfold pf_SH, shadow_addr.
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D. rewrite H4, Z.add_0_r in D.
  rewrite D at 1.
  replace (32 * (pf_F v pos / 32)) with ((pf_F v pos / 32 * 4) * 8) by ring.
  rewrite Z.div_mul by lia. unfold SHADOW_OFF. lia.
Qed.

(* the shadow cell of an address of the frame whose cell index i (lo <= i < hi) is 0 under PF_SC_LINE *)
Lemma b9_sh_cells : forall v pos lyc Sc Wc memc mdc lo hi x, b9_st v pos lyc Sc Wc memc mdc ->
  0 <= lo -> hi <= 144 -> (forall i, lo <= i < hi -> pf_shb PF_SC_LINE i = 0) ->
  pf_F v pos + 8 * lo <= x < pf_F v pos + 8 * hi ->
  rdW Wc memc (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
  intros v pos lyc Sc Wc memc mdc lo hi x H Hlo Hhi Hz Hx.
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & H2 & _ & H4).
  assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  replace x with (pf_F v pos + (x - pf_F v pos)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8).
  change (shadow_of_addr SHADOW_OFF (pf_F v pos)) with (pf_SH v pos).
  rewrite (b9_fsh_line _ _ _ _ _ _ _ H ((x - pf_F v pos) / 8)).
  - f_equal. apply Hz.
    split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
  - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* buf's shadow cell for an address of buf *)
Lemma b9_sh_at : forall v pos lyc Sc Wc memc mdc x, b9_st v pos lyc Sc Wc memc mdc ->
  b9_bufp v pos <= x < b9_bufp v pos + 512 ->
  rdW Wc memc (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
  intros v pos lyc Sc Wc memc mdc x H Hx.
  apply (b9_sh_cells v pos lyc Sc Wc memc mdc 8 72 x H ltac:(lia) ltac:(lia) b9_shb_line).
  unfold b9_bufp, PF_O_BUF in Hx. lia.
Qed.

(* cur_name's shadow cell for an address of cur_name *)
Lemma b9_sh_at_cn : forall v pos lyc Sc Wc memc mdc x, b9_st v pos lyc Sc Wc memc mdc ->
  b9_cnp v pos <= x < b9_cnp v pos + 16 ->
  rdW Wc memc (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
  intros v pos lyc Sc Wc memc mdc x H Hx.
  apply (b9_sh_cells v pos lyc Sc Wc memc mdc 4 6 x H ltac:(lia) ltac:(lia) b9_shb_cn).
  unfold b9_cnp, PF_O_CN in Hx. lia.
Qed.

(* every byte of the frame's first 1152 bytes has a mapped shadow cell *)
Lemma b9_sh_some : forall v pos lyc Sc Wc memc mdc s, b9_st v pos lyc Sc Wc memc mdc ->
  pf_SH v pos <= s < pf_SH v pos + 144 -> rdW Wc memc s <> None.
Proof.
  intros v pos lyc Sc Wc memc mdc s H Hs.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (b9_fsh_line _ _ _ _ _ _ _ H (s - pf_SH v pos) ltac:(lia)). discriminate.
Qed.

(* a range of the frame whose shadow cells lo .. hi - 1 (4 <= lo, hi <= 136) are 0 is addressable, with its
   8-byte shadow hull inside the frame's 144 cells (SH is a multiple of 4, so the hull's first word starts at or
   after SH when lo >= 4) *)
Lemma b9_addr_cells : forall v pos lyc Sc Wc memc mdc lo hi q n, b9_st v pos lyc Sc Wc memc mdc ->
  4 <= lo -> hi <= 136 -> (forall i, lo <= i < hi -> pf_shb PF_SC_LINE i = 0) ->
  pf_F v pos + 8 * lo <= q -> 0 <= n -> q + n <= pf_F v pos + 8 * hi ->
  sa_addr (rdW Wc memc) q n.
Proof.
  intros v pos lyc Sc Wc memc mdc lo hi q n H Hlo Hhi Hz Hq Hn Hqn.
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & H2 & H3 & H4).
  destruct (b9_SH4 v pos lyc Sc Wc memc mdc H) as [m Hm].
  pose proof alloc_ceiling_lt as HC.
  assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
  split; [lia|]. split; [lia|].
  split.
  { apply amem_range_high; [lia| |lia].
    destruct H3 as [_ [Hl | [Hh1 Hh2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia]. }
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    apply (b9_sh_cells v pos lyc Sc Wc memc mdc lo hi x H ltac:(lia) ltac:(lia) Hz). lia.
  - intros Hn0 s Hs.
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
    assert (B1 : lo <= (q - pf_F v pos) / 8)
      by (apply Z.div_le_lower_bound; lia).
    assert (B2 : (q + n - 1 - pf_F v pos) / 8 < hi)
      by (apply Z.div_lt_upper_bound; lia).
    rewrite E1, E2 in Hs.
    apply (b9_sh_some v pos lyc Sc Wc memc mdc s H).
    pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
    lia.
Qed.

(* a range of buf is addressable, with its shadow mapped: what every inline check of B9 and every range check of
   trim / strchr / strcasecmp / strlen / refuse asks *)
Lemma b9_addr_buf : forall v pos lyc Sc Wc memc mdc q n, b9_st v pos lyc Sc Wc memc mdc ->
  b9_bufp v pos <= q -> 0 <= n -> q + n <= b9_bufp v pos + 512 ->
  sa_addr (rdW Wc memc) q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  unfold b9_bufp, PF_O_BUF in Hq, Hqn.
  apply (b9_addr_cells v pos lyc Sc Wc memc mdc 8 72 q n H ltac:(lia) ltac:(lia) b9_shb_line); lia.
Qed.

(* a range of cur_name ([F + 0x20, F + 0x30)) is addressable, with its shadow mapped: refuse's %s check of the
   name at KREF *)
Lemma b9_addr_cn : forall v pos lyc Sc Wc memc mdc q n, b9_st v pos lyc Sc Wc memc mdc ->
  b9_cnp v pos <= q -> 0 <= n -> q + n <= b9_cnp v pos + 16 ->
  sa_addr (rdW Wc memc) q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  unfold b9_cnp, PF_O_CN in Hq, Hqn.
  apply (b9_addr_cells v pos lyc Sc Wc memc mdc 4 6 q n H ltac:(lia) ltac:(lia) b9_shb_cn); lia.
Qed.

(* a range of the class-5 frame lies in a live side-stack frame *)
Lemma b9_fframe_frame : forall v pos lyc Sc Wc memc mdc q n, b9_st v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 ->
  sa_fframe lyc Sc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  exists 5, pos. split; [exact (b9_fin v pos lyc Sc Wc memc mdc H)|].
  split; [lia|].
  pose proof (b9_lyc _ _ _ _ _ _ _ H) as Ely.
  unfold pf_F in Hq, Hqn. rewrite <- Ely in Hq, Hqn.
  rewrite b9_fb5. lia.
Qed.

(* a range of buf lies in a live side-stack frame *)
Lemma b9_fframe_buf : forall v pos lyc Sc Wc memc mdc q n, b9_st v pos lyc Sc Wc memc mdc ->
  b9_bufp v pos <= q -> 0 <= n -> q + n <= b9_bufp v pos + 512 ->
  sa_fframe lyc Sc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  unfold b9_bufp, PF_O_BUF in Hq, Hqn.
  apply (b9_fframe_frame v pos lyc Sc Wc memc mdc q n H); lia.
Qed.

(* a range of cur_name lies in a live side-stack frame *)
Lemma b9_fframe_cn : forall v pos lyc Sc Wc memc mdc q n, b9_st v pos lyc Sc Wc memc mdc ->
  b9_cnp v pos <= q -> 0 <= n -> q + n <= b9_cnp v pos + 16 ->
  sa_fframe lyc Sc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  unfold b9_cnp, PF_O_CN in Hq, Hqn.
  apply (b9_fframe_frame v pos lyc Sc Wc memc mdc q n H); lia.
Qed.

(** ** 2. The read-only view at the cut's reader *)
(* rt_rom_view (RtDefs.v) is arodata_okP's read-only-segment arm: in_rom is in_roP's first disjunct, and the two
   exclusions are the same (as pf_a7_r.v a7_rom, from b9_obj). *)
Lemma b9_rom_st : forall v pos lyc Sc Wc memc mdc, b9_st v pos lyc Sc Wc memc mdc ->
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc [_ _ _ _ Hobj _].
  destruct Hobj as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
  intros a (sg & Hsg & Hw & Hr) Ho He.
  exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.

(** ** 3. The stack at a cut of B9: sp0, s1 = pf_s1 = (sp0 - 0x160) & -32, the windows of the calls made at s1 *)
Lemma b9_stk : forall v pos lyc Sc Wc memc mdc, b9_st v pos lyc Sc Wc memc mdc ->
  pf_sp0 v mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo lyc /\
  ly_stk_lo lyc + STK_reac_segconf_parse_file <= pf_sp0 v /\
  pf_s1 v mod 32 = 0 /\ pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ (pf_s1 v - pf_sp0 v) mod 16 = 0.
Proof.
  intros v pos lyc Sc Wc memc mdc [_ Hj Ely _ _ _].
  pose proof Hj as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & _ & Hceil & Hslo & _).
  subst lyc.
  pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D0.
  pose proof (Z.div_mod (pf_sp0 v - 0x160) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_sp0 v - 0x160) 32 ltac:(lia)) as M1.
  assert (E1 : pf_s1 v = 32 * ((pf_sp0 v - 0x160) / 32)) by (unfold pf_s1; lia).
  pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_s1 v) 32 ltac:(lia)) as M2.
  pose proof (Z.div_mod (pf_s1 v - pf_sp0 v) 16 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (pf_s1 v - pf_sp0 v) 16 ltac:(lia)) as M3.
  split; [exact Hal16|]. split; [exact Hceil|]. split; [exact Hslo|].
  split; [lia|]. split; [lia|]. lia.
Qed.

(* a call made at s1 with a window stk <= 3 * ESTACK: the window lies above alloc_ceiling, fits the layout's stack,
   and fits parse_file's STK (12832 = 352 + 16 + 12464, SegInstB.STK_values; 3 * 4096 + 368 = 12656) *)
Lemma b9_win : forall v pos lyc Sc Wc memc mdc stk, b9_st v pos lyc Sc Wc memc mdc ->
  0 <= stk <= 3 * ESTACK ->
  ly_stk_lo lyc + stk <= pf_s1 v /\ alloc_ceiling <= pf_s1 v - stk /\
  stk - (pf_s1 v - pf_sp0 v) <= STK_reac_segconf_parse_file.
Proof.
  intros v pos lyc Sc Wc memc mdc stk H Hs.
  destruct (b9_stk v pos lyc Sc Wc memc mdc H) as (_ & Hc & Hlo & _ & Hs1 & _).
  pose proof STK_values as (_ & _ & _ & E & _). unfold ESTACK in Hs.
  rewrite E in Hlo |- *. lia.
Qed.

(* every byte of the class-5 frame is mapped (AR_laws' al_frames: a live frame's bytes are present) *)
Lemma b9_frame_some : forall v pos lyc Sc Wc memc mdc a, b9_st v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= a < pf_F v pos + 2048 -> rdW Wc memc a <> None.
Proof.
  intros v pos lyc Sc Wc memc mdc a H Ha.
  pose proof (b9_AR v pos lyc Sc Wc memc mdc H) as HAR.
  pose proof (b9_fin v pos lyc Sc Wc memc mdc H) as Hfin.
  destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hfin) as (_ & _ & Hpres & _).
  destruct H as [_ _ Ely _ _ _]. subst lyc.
  apply (aview_some_of_apresent SEGS). apply (Hpres a).
  unfold pf_F in Ha. rewrite b9_fb5. exact Ha.
Qed.

(* cur_name holds the C string nm (pf_nm, seg_spec.cstr_enc 16): sa_str at F + 0x20 (its bytes, its NUL and the
   bytes after it up to the next 8-byte boundary, all inside cur_name and so inside the live frame), and the name
   is at most 15 bytes *)
Lemma b9_nm_str_st : forall v pos lyc Sc Wc memc mdc nm, b9_st v pos lyc Sc Wc memc mdc ->
  pf_nm (rdW Wc memc) (b9_cnp v pos) nm ->
  sa_str (rdW Wc memc) (b9_cnp v pos) nm /\ (length nm < 16)%nat.
Proof.
  intros v pos lyc Sc Wc memc mdc nm H (f & Hb & Hlf & Hln & Hn0 & Hfz).
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & F4).
  split; [|exact Hln].
  split.
  - split; [|exact Hn0].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    assert (Hif : (i < length f)%nat) by lia.
    assert (E : nth i (seg_spec.zs f) 0 = nth i (nm ++ [0]) 0).
    { rewrite <- Hfz. rewrite <- (firstn_skipn (S (length nm)) (seg_spec.zs f)) at 1.
      apply app_nth1. rewrite length_firstn. unfold seg_spec.zs. rewrite length_map. lia. }
    pose proof (b9_nth_zs f i Hif) as E2.
    rewrite (Hb i Hif), <- E2, E; reflexivity.
  - intros x Hx.
    apply (b9_frame_some v pos lyc Sc Wc memc mdc x H).
    unfold b9_cnp, PF_O_CN in Hx.
    pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D0.
    pose proof (Z.div_mod (pf_F v pos + 0x20 + Z.of_nat (length nm)) 8 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (pf_F v pos + 0x20 + Z.of_nat (length nm)) 8 ltac:(lia)) as M1.
    lia.
Qed.

(** ** 4. aread_ok of a range of buf / cur_name at a call made at s1 *)
Lemma b9_read_ok_buf : forall v pos lyc Sc Wc memc mdc regsc stk q n, b9_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> 0 <= stk <= 3 * ESTACK ->
  b9_bufp v pos <= q -> 0 <= n -> q + n <= b9_bufp v pos + 512 ->
  aread_ok SEGS stk Wc regsc memc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk q n H Hsp Hs Hq Hn Hqn.
  pose proof (b9_addr_buf v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn) as HA.
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (_ & F2 & _ & _).
  destruct (b9_win v pos lyc Sc Wc memc mdc stk H Hs) as (_ & W2 & _).
  unfold b9_bufp, PF_O_BUF in Hq, Hqn.
  apply b9_read_ok_of_addr; [exact HA | lia | | rewrite Hsp; lia].
  intros a Ha. apply (b9_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

Lemma b9_read_ok_cn : forall v pos lyc Sc Wc memc mdc regsc stk q n, b9_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> 0 <= stk <= 3 * ESTACK ->
  b9_cnp v pos <= q -> 0 <= n -> q + n <= b9_cnp v pos + 16 ->
  aread_ok SEGS stk Wc regsc memc q n.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk q n H Hsp Hs Hq Hn Hqn.
  pose proof (b9_addr_cn v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn) as HA.
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (_ & F2 & _ & _).
  destruct (b9_win v pos lyc Sc Wc memc mdc stk H Hs) as (_ & W2 & _).
  unfold b9_cnp, PF_O_CN in Hq, Hqn.
  apply b9_read_ok_of_addr; [exact HA | lia | | rewrite Hsp; lia].
  intros a Ha. apply (b9_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

(** ** 5. amem_range of a range of the class-5 frame *)
Lemma b9_amem_frame : forall v pos lyc Sc Wc memc mdc q n, b9_st v pos lyc Sc Wc memc mdc ->
  pf_F v pos <= q -> 0 <= n -> q + n <= pf_F v pos + 2048 -> amem_range q n.
Proof.
  intros v pos lyc Sc Wc memc mdc q n H Hq Hn Hqn.
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & H2 & H3 & _).
  apply amem_range_high; [lia| |lia].
  destruct H3 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
    [left; lia | right; lia].
Qed.

(** ** 6. atail_vis at a NUL inside buf / cur_name (both 8-aligned, so the word's end stays inside) *)
Lemma b9_tail_vis_buf : forall v pos lyc Sc Wc memc mdc e, b9_st v pos lyc Sc Wc memc mdc ->
  b9_bufp v pos <= e < b9_bufp v pos + 512 -> atail_vis SEGS Wc memc e.
Proof.
  intros v pos lyc Sc Wc memc mdc e H He a Ha.
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & _ & _ & H4).
  unfold b9_bufp, PF_O_BUF in He.
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D0.
  pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M1.
  apply (b9_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

Lemma b9_tail_vis_cn : forall v pos lyc Sc Wc memc mdc e, b9_st v pos lyc Sc Wc memc mdc ->
  b9_cnp v pos <= e < b9_cnp v pos + 16 -> atail_vis SEGS Wc memc e.
Proof.
  intros v pos lyc Sc Wc memc mdc e H He a Ha.
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (H1 & _ & _ & H4).
  unfold b9_cnp, PF_O_CN in He.
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D0.
  pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M1.
  apply (b9_frame_some v pos lyc Sc Wc memc mdc a H). lia.
Qed.

(** ** 7. The runtime-call pre-state at a call of B9 (o = pf_s1 - sp0 in [-368, -352], a multiple of 16) *)
Lemma b9_ecall_pre_buf : forall v pos lyc Sc Wc memc mdc regsc stk, b9_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> ESTACK <= stk <= 3 * ESTACK ->
  YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  ecall_pre_stk SEGS B stk lyc Sc Wc regsc memc mdc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk H Hsp Hs Hra Hgp Htp.
  destruct (b9_stk v pos lyc Sc Wc memc mdc H) as (_ & _ & _ & _ & Hs1 & Hal).
  destruct (b9_win v pos lyc Sc Wc memc mdc stk H ltac:(unfold ESTACK in *; lia)) as (_ & _ & Hbud).
  destruct H as [_ Hj _ _ _ _].
  apply (PaArt.ecall_pre_stk_at SEGS B stk STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 regsc (pf_s1 v - pf_sp0 v) Hj);
    [lia | exact Hal | lia | exact (proj1 Hs) | exact Hbud | exact Hra | exact Hgp | exact Htp].
Qed.

(** ** 8. A literal of PARSE_FILE_LITS at a call made at s1 (sa_lit of b9_obj: sa_pinned, sa_img, the bytes) *)
Lemma b9_lit_read : forall v pos lyc Sc Wc memc mdc regsc stk s m, b9_st v pos lyc Sc Wc memc mdc ->
  In s PARSE_FILE_LITS -> spZ regsc = pf_s1 v -> 0 <= stk <= 3 * ESTACK ->
  0 <= m <= Z.of_nat (length s) + 1 ->
  0 < seg_litA_rc s /\
  astr_at SEGS Wc memc (seg_litA_rc s) (seg_spec.zb s) /\ astr_len (seg_spec.zb s) = Z.of_nat (length s) /\
  aread_ok SEGS stk Wc regsc memc (seg_litA_rc s) m /\
  amem_range (seg_litA_rc s) (Z.of_nat (length s) + 8) /\
  atail_vis SEGS Wc memc (seg_litA_rc s + Z.of_nat (length s)).
Proof.
  intros v pos lyc Sc Wc memc mdc regsc stk s m H Hin Hsp Hs Hm.
  pose proof (b9_AR v pos lyc Sc Wc memc mdc H) as HAR.
  destruct (b9_win v pos lyc Sc Wc memc mdc stk H Hs) as (_ & W2 & _).
  destruct H as [_ _ _ _ Hobj _].
  destruct Hobj as (_ & _ & _ & _ & _ & _ & HL & _).
  destruct (HL s Hin) as (Ha & Hstr & Hp & _ & Hi).
  destruct (b9_astr_of_sa Wc memc _ s Hstr) as (HA & _ & HLn & _ & HT).
  pose proof (Hp lyc Sc Wc memc mdc HAR) as HP.
  pose proof (proj1 (Hi (seg_litA_rc s + Z.of_nat (length s)) ltac:(lia))) as Himg.
  pose proof (pa_img_range _ Himg) as Hrg.
  pose proof asan_consts as (C1 & _ & _ & _ & C5). unfold kImgEnd in Hrg.
  split; [exact Ha|]. split; [exact HA|]. split; [exact HLn|].
  split; [|split].
  - apply b9_read_ok_of_addr.
    + apply (b9_sa_addr_sub _ _ _ _ _ HP); lia.
    + lia.
    + intros a Ha'. apply (b9_str_some _ _ _ a Hstr). lia.
    + rewrite Hsp. lia.
  - unfold amem_range. left. rewrite C5. lia.
  - rewrite HLn in HT. exact HT.
Qed.

(** ** 9. The premise lists of the three interceptor calls *)
(* strchr(line, '=') at 0x88400 (0x883f8 `li a1,61`, 0x883fc `mv a0,s7`): RtSeg.astrchr_realizes's premises in its
   order, for the C string l at x in buf (at KEY, x = lp and l = the trimmed line) *)
Lemma b9_strchr_pre_88400 : forall v pos lyc Sc Wc memc mdc regsc x l,
  b9_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x -> getr regsc 11 = w64 61 ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ getr regsc 11 = w64 61 /\ 0 < 61 < 256 /\ 0 < x /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc x (astr_len (seg_spec.zb l) + 1) /\
  amem_range x (astr_len (seg_spec.zb l) + 8) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 H11 Hs [Hb Hl].
  destruct (b9_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (b9_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [exact H11|]. split; [lia|]. split; [lia|].
  split; [exact HA|].
  split; [rewrite HLn; apply (b9_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold b9_bufp, PF_O_BUF; lia | lia
          | unfold b9_bufp, PF_O_BUF; lia]|].
  split; [rewrite HLn; apply (b9_amem_frame v pos lyc Sc Wc memc mdc); [exact H | lia | lia | lia]|].
  split; [exact HT|].
  exact (b9_rom_st v pos lyc Sc Wc memc mdc H).
Qed.

(* strlen(vp0) at 0x8843c (0x88438 `mv s3,a0`: a0 is still trim's result vp0): RtString.astrlen_realizes's premises
   in its order, for the C string l at x in buf (the trimmed value) *)
Lemma b9_strlen_pre_8843c : forall v pos lyc Sc Wc memc mdc regsc x l,
  b9_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 10 = w64 x ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B ESTACK lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ 0 < x /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\
  aread_ok SEGS ESTACK Wc regsc memc x (astr_len (seg_spec.zb l) + 1) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l H Hsp Hra Hgp Htp H10 Hs [Hb Hl].
  destruct (b9_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (b9_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc ESTACK H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [lia|].
  split; [exact HA|].
  split; [rewrite HLn; apply (b9_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold b9_bufp, PF_O_BUF; lia | lia
          | unfold b9_bufp, PF_O_BUF; lia]|].
  split; [exact HT|].
  exact (b9_rom_st v pos lyc Sc Wc memc mdc H).
Qed.

(* the four keys B9 compares with: "role" (.str.14 0x21760), "model" (.str.16 0x21800), "ignore" (0x218e0),
   "knock" (0x21960), each a text of PARSE_FILE_LITS (reac_segconf_parse_file_c.v:128-130) *)
Lemma b9_keys_lits : forall w, In w [S_role; S_model; S_ignore; S_knock] -> In w PARSE_FILE_LITS.
Proof.
  intros w Hw. unfold PARSE_FILE_LITS. apply in_or_app. left.
  destruct Hw as [<- | [<- | [<- | [<- | []]]]]; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* strcasecmp(key, w) at 0x88584 / 0x88598 / 0x885ac / 0x885c0 (a0 = s7 = the key, a1 = w's literal, auipc / addi
   before each call): RtSeg.astrcasecmp_realizes's premises in its order, for the C string l at x in buf (the
   trimmed key) and w one of the four keys; the literal's facts from b9_obj's sa_lit *)
Lemma b9_strcasecmp_pre : forall v pos lyc Sc Wc memc mdc regsc x l w,
  b9_st v pos lyc Sc Wc memc mdc ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  In w [S_role; S_model; S_ignore; S_knock] ->
  getr regsc 10 = w64 x -> getr regsc 11 = w64 (seg_litA_rc w) ->
  sa_str (rdW Wc memc) x l -> pf_inb (pf_F v pos + PF_O_BUF) x l ->
  ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc /\
  getr regsc 10 = w64 x /\ getr regsc 11 = w64 (seg_litA_rc w) /\ 0 < x /\ 0 < seg_litA_rc w /\
  astr_at SEGS Wc memc x (seg_spec.zb l) /\ astr_at SEGS Wc memc (seg_litA_rc w) (seg_spec.zb w) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc x (astr_len (seg_spec.zb l) + 1) /\
  amem_range x (astr_len (seg_spec.zb l) + 8) /\
  aread_ok SEGS (2 * ESTACK) Wc regsc memc (seg_litA_rc w) (astr_len (seg_spec.zb w) + 1) /\
  amem_range (seg_litA_rc w) (astr_len (seg_spec.zb w) + 8) /\
  atail_vis SEGS Wc memc (x + astr_len (seg_spec.zb l)) /\
  atail_vis SEGS Wc memc (seg_litA_rc w + astr_len (seg_spec.zb w)) /\
  rt_rom_view SEGS B Wc memc.
Proof.
  intros v pos lyc Sc Wc memc mdc regsc x l w H Hsp Hra Hgp Htp Hw H10 H11 Hs [Hb Hl].
  assert (HIN : In w PARSE_FILE_LITS) by exact (b9_keys_lits w Hw).
  assert (HLw : astr_len (seg_spec.zb w) = Z.of_nat (length w))
    by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
  destruct (b9_lit_read v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) w (astr_len (seg_spec.zb w) + 1)
    H HIN Hsp ltac:(unfold ESTACK; lia) ltac:(rewrite HLw; lia)) as (Ly0 & LyA & LyL & LyR & LyM & LyT).
  destruct (b9_astr_of_sa Wc memc x l Hs) as (HA & _ & HLn & _ & HT).
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  unfold PF_O_BUF in Hb, Hl.
  split; [exact (b9_ecall_pre_buf v pos lyc Sc Wc memc mdc regsc (2 * ESTACK) H Hsp
                   ltac:(unfold ESTACK; lia) Hra Hgp Htp)|].
  split; [exact H10|]. split; [exact H11|]. split; [lia|].
  split; [exact Ly0|]. split; [exact HA|]. split; [exact LyA|].
  split; [rewrite HLn; apply (b9_read_ok_buf v pos lyc Sc Wc memc mdc regsc);
          [exact H | exact Hsp | unfold ESTACK; lia | unfold b9_bufp, PF_O_BUF; lia | lia
          | unfold b9_bufp, PF_O_BUF; lia]|].
  split; [rewrite HLn; apply (b9_amem_frame v pos lyc Sc Wc memc mdc); [exact H | lia | lia | lia]|].
  split; [exact LyR|].
  split; [rewrite LyL; exact LyM|].
  split; [exact HT|].
  split; [rewrite LyL; exact LyT|].
  exact (b9_rom_st v pos lyc Sc Wc memc mdc H).
Qed.

(** ** 10. After an art_post call: b9_st again at the call's new memory *)
(* the caller's objects carry over to a reader that agrees below alloc_ceiling, at a state with AR: the text's and
   the block's bytes and shadow (sa_addr re-derived from the live blocks, reac_segconf_parse.v sa_addr_of_heap),
   the catalogue, the literals, the read-only window, the stack-protector cells *)
Lemma b9_obj_low : forall v lyc Sc (Wc : world SEGS) memc memc' mdc',
  AR SEGS B lyc Sc Wc memc' mdc' -> pf_obj B v lyc Sc (rdW Wc memc) ->
  (forall a, 0 <= a < alloc_ceiling -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_obj B v lyc Sc (rdW Wc memc').
Proof.
  intros v lyc Sc Wc memc memc' mdc' HAR' (Ht & At & Ht2 & Ac & Hc & CAT & LITS & ROD & SSP) LK.
  assert (Ht0 : 0 <= p_t v) by (destruct At; lia).
  assert (Hc0 : 0 <= p_c v) by (destruct Ac; lia).
  destruct (reac_segconf_parse.sa_addr_of_heap B lyc Sc Wc memc' mdc' (p_t v) (pf_len v) HAR' Ht2 Ht0
    ltac:(unfold pf_len; lia)) as [At' Hte].
  destruct (reac_segconf_parse.sa_addr_of_heap B lyc Sc Wc memc' mdc' (p_c v) seg_spec.SEG_C_SIZE HAR' Hc Hc0
    ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [Ac' _].
  split; [apply (reac_segconf_parse.sa_str_low _ _ _ _ Ht); [exact Ht0 | unfold pf_len in Hte; lia | exact LK]|].
  split; [exact At'|]. split; [exact Ht2|]. split; [exact Ac'|]. split; [exact Hc|].
  split; [exact (reac_segconf_parse.sa_cat_low B _ _ CAT LK)|].
  split; [intros x Hx; exact (reac_segconf_parse.sa_lit_low B _ _ _ _ (LITS x Hx) LK)|].
  split; [|exact (reac_segconf_parse.sa_ssp_low _ _ SSP LK)].
  intros a Hro Ho He.
  assert (Ha : 0 <= a < alloc_ceiling).
  { pose proof asan_consts as (C1 & _).
    destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
    - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
      pose proof (pa_img_range a Hi) as Hrg. unfold kImgEnd in Hrg. lia.
    - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia. }
  rewrite (LK a Ha). exact (ROD a Hro Ho He).
Qed.

(* What aj_art_at (PaArt.v) / aj_art_atF (PaFx.v) return after a call made at sp0 + o with window stk and no written
   cells (Eb = fun _ => False): the journal at the new memory memc' and the keep clause outside
   [sp0 + o - stk, sp0 + o). Every fact of b9_st other than the journal is about bytes below alloc_ceiling (the heap
   text and block, image literals and cells, the frame's shadow), which the journal's astk_ok puts below
   sp0 - STK <= sp0 + o - stk, so the keep clause keeps them all. *)
Lemma b9_keep_art : forall v pos lyc Sc Wc memc mdc memc' mdc' o stk,
  b9_st v pos lyc Sc Wc memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  stk - o <= STK_reac_segconf_parse_file ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_sp0 v + o - stk <= a < pf_sp0 v + o) -> ~ (fun _ : Z => False) a ->
     rdW Wc memc' a = rdW Wc memc a) ->
  b9_st v pos lyc Sc Wc memc' mdc'.
Proof.
  intros v pos lyc Sc Wc memc mdc memc' mdc' o stk H HJ' Hbud HK.
  destruct (b9_stk v pos lyc Sc Wc memc mdc H) as (_ & Hceil & Hslo & _).
  destruct (b9_frame_rng v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
  pose proof asan_consts as (C1 & C2 & _ & C4 & C5).
  assert (LK : forall a, 0 <= a < alloc_ceiling -> rdW Wc memc' a = rdW Wc memc a).
  { intros a Ha. apply HK; [lia | lia | intros Hf; exact Hf]. }
  pose proof (proj1 HJ') as HAR'.
  pose proof (shadow_addr_bounds (pf_F v pos) ltac:(rewrite C4; lia)) as HSB.
  rewrite C2, C5 in HSB.
  destruct H as [Hcx _ Ely Hperm Hobj Hfsh].
  constructor.
  - exact Hcx.
  - exact HJ'.
  - exact Ely.
  - exact Hperm.
  - exact (b9_obj_low v lyc Sc Wc memc memc' mdc' HAR' Hobj LK).
  - intros i Hi.
    assert (HS : 0 <= pf_SH v pos + i < alloc_ceiling) by (unfold pf_SH; lia).
    rewrite (LK _ HS). exact (Hfsh i Hi).
Qed.

End e.
End f.
End d.
