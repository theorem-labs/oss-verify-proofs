(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 558 of its 606 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a5_k.v, with its module paths and module names changed; 433 of its 539 lines of code are new or changed and 500 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the memory kit of segment B8a of
   reac_segconf_parse_file's walk (lib/B/Prog/pf_pieces.v S_B8a). The B8a segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: frame lemmas, no instruction walked).
   ADAPTED from the image-A G3 walk owner's image-A kits lib/A/Prog/pf_a5_k.v (the geometry a5_geo and the keep lemmas of a step,
   a5_move: commit 61a728170142) and lib/A/Prog/pf_a7_d.v / pf_a7_r.v (buf's range facts and
   the interceptor premises: commit ebe0b30cca65), re-derived for image B: B's realigned
   locals base s1 = (sp0 - 0x160) & -32 (0x87e38, 0x87e78), B's slots (PF_SL from 0x00), and B8a's write set
     b8_W v ov a : the callee windows below s1 (strcmp, 2 * ESTACK, called at s1), the slots s1 + 0x60 .. 0x78
                   (0x88cbc sd a3,96(s1); 0x88cd0 sd a2,104(s1); 0x88ce0 sd a0,112(s1)), the slot s1 + 0xc0
                   (0x88cc0 sd s7,192(s1)) and, on the bound path only (ov = true), the four bytes of
                   c->overflow (0x88d54 sw a1,0(a0)).
   A state that agrees with a cut state off b8_W keeps the cut's pf_base (b8_move) and, off c->overflow, the
   block c (b8_keep_rconf), cur_name and the name in buf (b8_keep_bytes_frame); the strcmp call's premises on a
   name in buf (b8_buf_str_pre) and on c->seg[i].name (b8_seg_str_pre) come from pf_base at the call's state. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YP03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B8a_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaArt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Lemma b8_fb5 : fs_frame_bytes 5 = 2048.
Proof. reflexivity. Qed.
(* a C string's span holds its bytes and NUL *)
Lemma b8_span_ge : forall t (s : list Z), Z.of_nat (length s) + 1 <= seg_spec.cstr_span t s.
Proof.
intros t s. unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
Qed.
(* the 8-byte word of the byte e ends at e's string span (seg_spec.cstr_span's slack) *)
Lemma b8_span_tail : forall t (s : list Z) x, t + Z.of_nat (length s) < x <
  t + Z.of_nat (length s) - (t + Z.of_nat (length s)) mod 8 + 8 -> x < t + seg_spec.cstr_span t s.
Proof.
intros t s x Hx. unfold seg_spec.cstr_span. set (e := t + Z.of_nat (length s)) in *.
pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as M2.
fold e in D2, M2. lia.
Qed.
(* buf's shadow cells (8 .. 71) are 0 while buf is in scope *)
Lemma b8_shb_line : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. unfold pf_shb.
destruct (Z.ltb_spec i 4) as [H|_]; [lia|].
destruct (Z.ltb_spec i 6) as [H|_]; [lia|].
destruct (Z.ltb_spec i 8) as [H|_]; [lia|].
destruct (Z.ltb_spec i 72) as [_|H]; [reflexivity|lia].
Qed.
(* the 8-byte shadow hull of a sub-range lies inside the hull of the range *)
Lemma b8_hull_sub : forall (rd : reader) q n q' n', shadow_hull_vis rd q n -> q <= q' -> 0 < n' ->
  q' + n' <= q + n -> shadow_hull_vis rd q' n'.
Proof.
intros rd q n q' n' H Hq Hn Hle s Hs. apply H.
pose proof (shadow_mono q q' Hq) as M1.
pose proof (shadow_mono (q' + n' - 1) (q + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u w, u <= w -> u / 8 * 8 <= w / 8 * 8)
  by (intros u w Huw; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The bytes B8a writes, and what agrees off them *)
Definition b8_W (v : pfv) (ov : bool) (a : Z) : Prop :=
  (alloc_ceiling <= a < pf_s1 v) \/ (pf_s1 v + 0x60 <= a < pf_s1 v + 0x78) \/
  (pf_s1 v + 0xc0 <= a < pf_s1 v + 0xc8) \/
  (ov = true /\ p_c v + seg_spec.RC_OVERFLOW <= a < p_c v + seg_spec.RC_OVERFLOW + 4).
Definition b8_keep (v : pfv) (ov : bool) (rd rd' : reader) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ b8_W v ov a -> rd' a = rd a.
Lemma b8_keep_refl : forall v ov rd, b8_keep v ov rd rd.
Proof. intros v ov rd a _ _. reflexivity. Qed.
Lemma b8_keep_trans : forall v ov rd1 rd2 rd3, b8_keep v ov rd1 rd2 -> b8_keep v ov rd2 rd3 -> b8_keep v ov rd1 rd3.
Proof. intros v ov rd1 rd2 rd3 H12 H23 a Ha Hn. rewrite (H23 a Ha Hn). exact (H12 a Ha Hn). Qed.
Lemma b8_keep_mono : forall v rd rd', b8_keep v false rd rd' -> b8_keep v true rd rd'.
Proof.
intros v rd rd' H a Ha Hn. apply H; [exact Ha|]. intros Hw. apply Hn.
destruct Hw as [W1 | [W2 | [W3 | (W4 & _)]]]; [left | right; left | right; right; left | discriminate W4]; assumption.
Qed.
(* a step that writes only a window W' inside b8_W *)
Lemma b8_keep_step : forall v ov rd1 rd2 rd3 (W' : Z -> Prop), b8_keep v ov rd1 rd2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W' a -> rd3 a = rd2 a) -> (forall a, W' a -> b8_W v ov a) ->
  b8_keep v ov rd1 rd3.
Proof.
intros v ov rd1 rd2 rd3 W' H12 H23 Hsub a Ha Hn. rewrite (H23 a Ha) by (intros Hw; exact (Hn (Hsub a Hw))).
exact (H12 a Ha Hn).
Qed.

(** ** The numbers of a cut state *)
Definition b8_G (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + STK_reac_segconf_parse_file <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 0x170 <= pf_s1 v <= pf_sp0 v - 0x160 /\ pf_s1 v mod 32 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  in_app (pf_F v pos) 2048 /\ pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\
  kLowMemEnd <= pf_SH v pos /\ pf_SH v pos + 256 <= kHighShadowEnd.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma b8_geo : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  AR SEGS B lyc Sc Wc memc mdc /\ lyc = p_ly v /\ In (5, pos) (frames Sc) /\ b8_G v pos.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & HFI & _).
destruct HFI as (HJ & Hly & _).
destruct HCX as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
subst lyc.
destruct (al_frames _ _ LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
rewrite b8_fb5 in *. change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & SPF & _).
change (spZ (p_regs v)) with (pf_sp0 v) in *. rewrite SPF in *.
split; [exact HAR|]. split; [reflexivity|]. split; [exact Hin|].
unfold b8_G. rewrite SPF.
assert (Hs1 : pf_s1 v = pf_sp0 v - 0x160 - (pf_sp0 v - 0x160) mod 32) by reflexivity.
assert (ESH : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8) by reflexivity.
pose proof (Z.mod_pos_bound (pf_sp0 v - 0x160) 32 ltac:(lia)) as M1.
pose proof (Z.div_mod (pf_sp0 v - 0x160) 32 ltac:(lia)) as D1.
pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D0.
assert (M16 : (pf_sp0 v - 0x160) mod 32 = 0 \/ (pf_sp0 v - 0x160) mod 32 = 16).
{ assert (E16 : (pf_sp0 v - 0x160) mod 16 = 0).
  { replace (pf_sp0 v - 0x160) with (pf_sp0 v + (-22) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
  pose proof (Z.div_mod (pf_sp0 v - 0x160) 16 ltac:(lia)) as D16. lia. }
pose proof Happ as Happ0.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
assert (Hq0 : 0 <= pf_F v pos / 8) by (apply Z.div_pos; lia).
assert (Hq3 : (pf_F v pos + 2048) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (Hq2 : (pf_F v pos + 2048) / 8 = pf_F v pos / 8 + 256).
{ replace (pf_F v pos + 2048) with (pf_F v pos + 256 * 8) by lia. apply Z.div_add. lia. }
assert (Hq4 : alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in Hq4.
rewrite ESH. unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [rewrite Hs1; lia|].
split; [rewrite Hs1; replace (pf_sp0 v - 0x160 - (pf_sp0 v - 0x160) mod 32) with (32 * ((pf_sp0 v - 0x160) / 32)) by lia;
  rewrite Z.mul_comm; apply Z_mod_mult|].
split; [lia|]. split; [lia|]. split; [exact H32|].
split; [exact Happ0|]. split; [reflexivity|]. split; lia.
Qed.

(* where the blocks of c and of the text lie *)
Lemma b8_blk : forall v pos lyc Sc Wc rX memc mdc sc q n, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  sa_heap B lyc Sc q n -> 0 < n ->
  exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= q /\ q + n <= b + req_size m /\ 4096 <= b /\
    b + req_size m <= alloc_ceiling /\ in_app b (req_size m) /\ off_img b (req_size m) /\
    (b + req_size m <= pf_F v pos \/ pf_F v pos + 2048 <= b).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc q n HB (b & m & Hb & H1 & H2) Hn.
destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof (blk_off_imgP B lyc Sc Wc memc mdc b m HAR Hb) as Hoff.
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite b8_fb5 in Hd. subst lyc.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
exists b, m. split; [exact Hb|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Happ|]. split; [exact Hoff|]. lia.
Qed.

(* c and the text are heap blocks apart from each other's spans (reader_pre, pf_cx) *)
Lemma b8_cx : forall v, pf_cx B v ->
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE /\ p_c v mod 16 = 0.
Proof.
intros v (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
destruct HPF as (HRP & _). destruct HRP as (_ & C16 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD & _).
split; [exact HD | exact C16].
Qed.

(** ** What a state that agrees off b8_W keeps *)
Section k.
Variables (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (rX : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (sc : pf_scope) (ov : bool) (memc' : word -> option byte).
#[local] Notation rd := (rdW Wc memc).
#[local] Notation rd' := (rdW Wc memc').
Hypothesis HB : pf_base B v pos lyc Sc Wc rX memc mdc sc.
Hypothesis HK : b8_keep v ov rd rd'.

Lemma b8_c_blk : exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= p_c v /\
  p_c v + seg_spec.SEG_C_SIZE <= b + req_size m /\ 4096 <= b /\
  b + req_size m <= alloc_ceiling /\ in_app b (req_size m) /\ off_img b (req_size m) /\
  (b + req_size m <= pf_F v pos \/ pf_F v pos + 2048 <= b).
Proof using HB.
pose proof HB as (_ & _ & (_ & _ & _ & _ & HC & _) & _).
apply (b8_blk v pos lyc Sc Wc rX memc mdc sc _ _ HB HC). unfold seg_spec.SEG_C_SIZE. lia.
Qed.

(* every byte below alloc_ceiling but c->overflow's is kept *)
Lemma b8_low : forall a, 0 <= a < alloc_ceiling ->
  (a < p_c v + seg_spec.RC_OVERFLOW \/ p_c v + seg_spec.RC_OVERFLOW + 4 <= a) -> rd' a = rd a.
Proof using HB HK.
intros a Ha Hc. destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G).
pose proof G as (G1 & G2 & G3 & G4 & _).
pose proof asan_consts as (C1 & _). pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & SPF & _).
rewrite SPF in G1.
apply HK; [lia|]. intros [W1 | [W2 | [W3 | (_ & W4)]]]; lia.
Qed.
(* a byte off the block c below alloc_ceiling *)
Lemma b8_low_offc : forall a, 0 <= a < alloc_ceiling ->
  (a < p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= a) -> rd' a = rd a.
Proof using HB HK.
intros a Ha Hc. apply b8_low; [exact Ha|]. unfold seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* a shadow byte of the application range below alloc_ceiling *)
Lemma b8_low_sh : forall s, SHADOW_OFF <= s < SHADOW_OFF + alloc_ceiling / 8 -> rd' s = rd s.
Proof using HB HK.
intros s Hs. destruct b8_c_blk as (b & m & _ & Hb & Hm & H4096 & Hc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (P2 : alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in P2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
apply b8_low_offc; unfold SHADOW_OFF, seg_spec.SEG_C_SIZE in *; lia.
Qed.
Lemma b8_ac8 : alloc_ceiling mod 8 = 0 /\ (alloc_ceiling / 8) mod 8 = 0.
Proof.
pose proof ASAN_CEIL_range as (_ & AC). unfold ASAN_CEIL in AC.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as D.
split.
- rewrite D, AC, Z.add_0_r. replace (4096 * (alloc_ceiling / 4096)) with ((512 * (alloc_ceiling / 4096)) * 8) by lia.
  apply Z_mod_mult.
- rewrite D, AC, Z.add_0_r. replace (4096 * (alloc_ceiling / 4096)) with ((512 * (alloc_ceiling / 4096)) * 8) by lia.
  rewrite Z.div_mul by lia. replace (512 * (alloc_ceiling / 4096)) with ((64 * (alloc_ceiling / 4096)) * 8) by lia.
  apply Z_mod_mult.
Qed.
(* an image byte *)
Lemma b8_low_img : forall a, 0x10000 <= a < kImgEnd -> rd' a = rd a.
Proof using HB HK.
intros a Ha. destruct b8_c_blk as (b & m & _ & Hb & Hm & H4096 & Hc & _ & Hoff & _).
pose proof asan_consts as (C1 & _). unfold off_img, kImgEnd in *.
apply b8_low_offc; unfold seg_spec.SEG_C_SIZE in *; lia.
Qed.
(* a byte of the class-5 frame, or of its shadow cells *)
Lemma b8_low_frame : forall a, pf_F v pos <= a < pf_F v pos + 2048 -> rd' a = rd a.
Proof using HB HK.
intros a Ha. destruct b8_c_blk as (b & m & _ & Hb & Hm & H4096 & Hc & _ & _ & Hf).
destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G).
pose proof G as (_ & _ & _ & _ & _ & G6 & G7 & _).
apply b8_low_offc; unfold seg_spec.SEG_C_SIZE in *; lia.
Qed.

Lemma b8_keep_addr_low : forall q n, 0 <= q -> q + n <= alloc_ceiling -> sa_addr rd q n -> sa_addr rd' q n.
Proof using HB HK.
intros q n Hq Hqn (A0 & A1 & A2 & A3 & A4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof b8_ac8 as (AC8 & AC64).
pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)) as DA. pose proof (Z.div_mod (alloc_ceiling / 8) 8 ltac:(lia)) as DA8.
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  rewrite b8_low_sh; [exact Hs | lia].
- intros Hn s Hs. pose proof (A4 Hn s Hs) as A4s.
  unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
  rewrite b8_low_sh; [exact A4s | unfold SHADOW_OFF; lia].
Qed.

Lemma b8_keep_bytes_low : forall a l, 0 <= a -> a + Z.of_nat (length l) <= alloc_ceiling ->
  (a + Z.of_nat (length l) <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= a) -> sa_bytes rd a l -> sa_bytes rd' a l.
Proof using HB HK. intros a l Ha Hl Hc H i Hi. rewrite b8_low_offc by lia. exact (H i Hi). Qed.

(* the text (and its slack to the next word), apart from c by reader_pre's sa_disj *)
Lemma b8_keep_text : sa_str rd (p_t v) (p_s v) -> sa_str rd' (p_t v) (p_s v).
Proof using HB HK.
intros ((Hz & Hn) & Ht).
pose proof HB as (HCX & _ & (_ & _ & HTH & _) & _).
destruct (b8_cx v HCX) as (HD & _).
destruct (b8_blk v pos lyc Sc Wc rX memc mdc sc _ _ HB HTH ltac:(unfold pf_len; lia))
  as (b & m & _ & Hb & Hm & H4096 & Hc & _).
unfold pf_len, sa_disj, seg_spec.SEG_C_SIZE in *.
pose proof (b8_span_ge (p_t v) (p_s v)) as Hsp.
split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  assert (E : rd' (p_t v + Z.of_nat i) = rd (p_t v + Z.of_nat i)).
  { apply b8_low_offc; [split; lia|]. unfold seg_spec.SEG_C_SIZE. destruct HD as [HD|HD]; [left|right]; lia. }
  rewrite E. apply Hz. rewrite length_app. cbn [length]. lia.
- intros x Hx. pose proof (b8_span_tail (p_t v) (p_s v) x Hx) as Hx'.
  pose proof ASAN_CEIL_range as (_ & AC). unfold ASAN_CEIL in AC.
  assert (He0 : 0 <= p_t v + Z.of_nat (length (p_s v)) < alloc_ceiling) by lia.
  pose proof (PaArt.tail_below (p_t v + Z.of_nat (length (p_s v))) alloc_ceiling He0 AC) as Hx2.
  assert (E : rd' x = rd x).
  { apply b8_low_offc; [split; lia|]. unfold seg_spec.SEG_C_SIZE. destruct HD as [HD|HD]; [left|right]; lia. }
  rewrite E. exact (Ht x Hx).
Qed.
Lemma b8_keep_rdword_img : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword rd' a = rdword rd a.
Proof using HB HK. intros a H0 H1. apply rdword_ext. intros k Hk. apply b8_low_img. lia. Qed.
Lemma b8_keep_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof using HB HK.
intros a s (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _ & _).
pose proof (pa_img_range _ Himg) as Hrg.
rewrite (b8_low_img (a + Z.of_nat i) Hrg). exact (Hz i Hi').
Qed.
Lemma b8_keep_cat : sa_cat SEGS B rd catA -> sa_cat SEGS B rd' catA.
Proof using HB HK.
intros (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b8_keep_lit tp _ Hl)].
assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd rd' (pin_spec.row_addr catA i)); [exact Htp|].
intros k Hk. apply b8_low_img.
refine (pa_img_range _ (proj1 (Hi (pin_spec.row_addr catA i + k) _))).
unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b8_keep_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof using HB HK.
intros H a Hro Ho He. rewrite (b8_low_img a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma b8_keep_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof using HB HK.
intros (G1 & g & G2).
split; [rewrite (b8_keep_rdword_img gotwA); [exact G1 | unfold gotwA; lia | unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (b8_keep_rdword_img guardA); [exact G2 | unfold guardA; lia | unfold guardA, kImgEnd; lia].
Qed.
(* a heap range other than the text, apart from c *)
Lemma b8_keep_obj : pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof using HB HK.
intros (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
destruct (b8_blk v pos lyc Sc Wc rX memc mdc sc _ _ HB T3 ltac:(unfold pf_len; lia)) as (bt & mt & _ & Ht1 & Ht2 & Ht4 & Ht3 & _).
destruct b8_c_blk as (bc & mc & _ & Hc1 & Hc2 & Hc4 & Hc3 & _).
unfold pf_len, seg_spec.SEG_C_SIZE in *.
split; [exact (b8_keep_text T1)|].
split; [apply (b8_keep_addr_low (p_t v) (Z.of_nat (length (p_s v)) + 1)); [lia | lia | exact T2]|]. split; [exact T3|].
split; [apply (b8_keep_addr_low (p_c v) 16616); [lia | lia | exact C1]|]. split; [exact C2|].
split; [exact (b8_keep_cat CA)|].
split; [intros x Hx; exact (b8_keep_lit _ _ (LI x Hx))|].
split; [exact (b8_keep_rod RO) | exact (b8_keep_ssp SS)].
Qed.
(* words above s1 that B8a does not write: PF_SL's, slot 0xc8, the saved registers *)
Lemma b8_keep_word_hi : forall a, pf_s1 v <= a -> a + 8 <= 2 ^ 64 ->
  (a + 8 <= pf_s1 v + 0x60 \/ (pf_s1 v + 0x78 <= a /\ a + 8 <= pf_s1 v + 0xc0) \/ pf_s1 v + 0xc8 <= a) ->
  rdword rd' a = rdword rd a.
Proof using HB HK.
intros a H0 H1 H2. destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G).
pose proof G as (G1 & G2 & G3 & G4 & _).
pose proof asan_consts as (C1 & _). pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & SPF & _).
rewrite SPF in G1. destruct b8_c_blk as (bc & mc & _ & Hc1 & Hc2 & _ & Hc3 & _).
unfold seg_spec.SEG_C_SIZE in *.
apply rdword_ext. intros k Hk. apply HK; [lia|].
intros [W1 | [W2 | [W3 | (_ & W4)]]]; unfold seg_spec.RC_OVERFLOW in *; lia.
Qed.
Lemma b8_keep_sl : pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof using HB HK.
intros H. destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G). pose proof G as (G1 & G2 & G3 & G4 & _).
unfold pf_sl in *. rewrite Forall_forall in *. intros [off val] Hov. specialize (H _ Hov). cbn [fst snd] in *.
assert (Hoff : (0 <= off <= 0x58 \/ (0x78 <= off <= 0xb8) \/ 0xd0 <= off <= 0xd8)).
{ unfold PF_SL in Hov. cbn [In] in Hov.
  repeat (let Hq := fresh "Hq" in destruct Hov as [Hq | Hov]; [injection Hq as <- _; lia |]). destruct Hov. }
rewrite b8_keep_word_hi; [exact H | lia | lia | lia].
Qed.
Lemma b8_keep_c8 : pf_sl rd (pf_s1 v) [(0xc8, p_c v)] -> pf_sl rd' (pf_s1 v) [(0xc8, p_c v)].
Proof using HB HK.
intros H. destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G). pose proof G as (G1 & G2 & G3 & G4 & _).
unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in H. cbn [fst snd] in *.
rewrite b8_keep_word_hi; [exact H | lia | lia | lia].
Qed.
Lemma b8_keep_saved : forall regs, pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof using HB HK.
intros regs H j r Hj. destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G). pose proof G as (G1 & G2 & G3 & G4 & _).
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
rewrite b8_keep_word_hi; [exact (H j r Hj) | lia | lia | lia].
Qed.
Lemma b8_keep_flag : forall x, rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof using HB HK.
intros x H. rewrite b8_fb5 in *. rewrite (rdword_ext rd rd'); [exact H|]. intros k Hk. apply b8_low_frame. lia.
Qed.
Lemma b8_keep_fsh : forall sc', pf_fsh rd (pf_SH v pos) sc' -> pf_fsh rd' (pf_SH v pos) sc'.
Proof using HB HK.
intros sc' H i Hi. destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G).
pose proof G as (_ & _ & _ & _ & _ & G6 & G7 & G8 & G9 & G10 & G11 & G12).
assert (P2 : (pf_F v pos + 2048) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (P3 : (pf_F v pos + 2048) / 8 = pf_F v pos / 8 + 256).
{ replace (pf_F v pos + 2048) with (pf_F v pos + 256 * 8) by lia. apply Z.div_add. lia. }
rewrite b8_low_sh; [exact (H i Hi) | unfold kLowMemEnd, SHADOW_OFF in *; lia].
Qed.
(* the block c, when c->overflow is not written *)
Lemma b8_keep_rconf : forall cf, ov = false -> sa_rconf rd (p_c v) cf -> sa_rconf rd' (p_c v) cf.
Proof using HB HK.
intros cf Hov (bs & Hb & He). exists bs. split; [|exact He]. intros i Hi.
destruct He as [L _]. unfold seg_spec.SEG_C_SIZE in L.
destruct b8_c_blk as (bc & mc & _ & Hc1 & Hc2 & H4 & Hc3 & _). unfold seg_spec.SEG_C_SIZE in *.
pose proof asan_consts as (AC1 & _).
rewrite (HK (p_c v + Z.of_nat i)); [exact (Hb i Hi) | lia |].
destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G). pose proof G as (G1 & G2 & G3 & G4 & _).
pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & SPF & _). rewrite SPF in G1.
intros [W1 | [W2 | [W3 | (W4 & _)]]]; [lia | lia | lia | rewrite Hov in W4; discriminate W4].
Qed.
(* bytes of the class-5 frame: cur_name, the name in buf *)
Lemma b8_keep_bytes_frame : forall a l, pf_F v pos <= a -> a + Z.of_nat (length l) <= pf_F v pos + 2048 ->
  sa_bytes rd a l -> sa_bytes rd' a l.
Proof using HB HK. intros a l H0 H1 H i Hi. rewrite b8_low_frame by lia. exact (H i Hi). Qed.
Lemma b8_keep_nm : forall nm, pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof using HB HK.
intros nm (f & Hf & Hfe). exists f. split; [|exact Hfe]. destruct Hfe as (Lf & _).
apply b8_keep_bytes_frame; [unfold PF_O_CN; lia | rewrite Lf; unfold PF_O_CN; lia | exact Hf].
Qed.
Lemma b8_keep_buf_str : forall np name, pf_inb (pf_F v pos + PF_O_BUF) np name -> sa_str rd np name -> sa_str rd' np name.
Proof using HB HK.
intros np name [Hi1 Hi2] ((Hz & Hn) & Ht). unfold PF_O_BUF in *.
destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G).
pose proof G as (_ & _ & _ & _ & _ & G6 & G7 & G8 & _).
pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as DF.
split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite b8_low_frame by lia.
  apply Hz. rewrite length_app. cbn [length]. lia.
- intros x Hx. pose proof (Z.div_mod (np + Z.of_nat (length name)) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (np + Z.of_nat (length name)) 8 ltac:(lia)) as M1.
  rewrite b8_low_frame by lia. exact (Ht x Hx).
Qed.
End k.

(** ** pf_base after a stretch of B8a: a state at the same layout and frame state whose journal goes on from
    the entry, whose memory agrees with the cut's off b8_W, and whose registers hold pf_fi's list *)
Definition b8_FI (v : pfv) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
Lemma b8_move : forall v pos lyc Sc Wc rX memc mdc sc ov rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  b8_keep v ov (rdW Wc memc) (rdW Wc memc') -> pf_rg rX' (b8_FI v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc ov rX' memc' mdc' HB HJ' HK HRG.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct HFI as (_ & Hly & HS0 & HP0 & HSV & HFL & HFRM & HTF & HC8 & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HS0|]. split; [exact HP0|].
  split; [exact (b8_keep_saved v pos lyc Sc Wc rX memc mdc sc ov memc' HB HK _ HSV)|].
  split; [exact (b8_keep_flag v pos lyc Sc Wc rX memc mdc sc ov memc' HB HK _ HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [exact (b8_keep_c8 v pos lyc Sc Wc rX memc mdc sc ov memc' HB HK HC8) | exact HRG]. }
split; [exact (b8_keep_obj v pos lyc Sc Wc rX memc mdc sc ov memc' HB HK HOBJ)|].
split; [exact (b8_keep_sl v pos lyc Sc Wc rX memc mdc sc ov memc' HB HK HSL)|].
exact (b8_keep_fsh v pos lyc Sc Wc rX memc mdc sc ov memc' HB HK _ HFSH).
Qed.
(** ** The premises of the strcmp call (0x88d04), at a state that holds pf_base *)
(* every byte of the class-5 frame is mapped *)
Lemma b8_frame_some : forall v pos lyc Sc Wc rX memc mdc sc a, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  pf_F v pos <= a < pf_F v pos + 2048 -> rdW Wc memc a <> None.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc a HB Ha.
destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & _).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (_ & _ & Hpres & _).
apply (aview_some_of_apresent SEGS). apply (Hpres a). subst lyc. unfold pf_F in Ha. rewrite b8_fb5. exact Ha.
Qed.
(* a range of buf is addressable with its shadow mapped while buf is in scope (pf_a7_d.v a7_addr_buf) *)
Lemma b8_buf_addr : forall v pos lyc Sc Wc rX memc mdc q n, pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  pf_F v pos + PF_O_BUF <= q -> 0 <= n -> q + n <= pf_F v pos + PF_O_BUF + 512 -> sa_addr (rdW Wc memc) q n.
Proof.
intros v pos lyc Sc Wc rX memc mdc q n HB Hq Hn Hqn.
destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G).
pose proof G as (_ & _ & _ & _ & _ & H1 & H2 & H4 & H3 & ESH & SH1 & SH2).
pose proof HB as (_ & _ & _ & _ & HFSH).
pose proof asan_consts as (C1 & _).
unfold PF_O_BUF in Hq, Hqn.
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
assert (SHA : forall x, pf_F v pos <= x -> shadow_of_addr SHADOW_OFF x = pf_SH v pos + (x - pf_F v pos) / 8).
{ intros x Hx. replace x with (pf_F v pos + (x - pf_F v pos)) at 1 by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (x - pf_F v pos) HF8). reflexivity. }
split; [lia|]. split; [lia|].
split.
{ apply amem_range_high; [lia| |lia].
  destruct H3 as [_ [Hlo | [Hhi1 Hhi2]]]; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; [left; lia | right; lia]. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  rewrite (SHA x ltac:(lia)). rewrite (HFSH ((x - pf_F v pos) / 8)).
  + f_equal. apply b8_shb_line. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
  + split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
- intros Hn0 s Hs.
  assert (E1 : shadow_addr q = pf_SH v pos + (q - pf_F v pos) / 8) by exact (SHA q ltac:(lia)).
  assert (E2 : shadow_addr (q + n - 1) = pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) by exact (SHA (q + n - 1) ltac:(lia)).
  assert (B1 : 8 <= (q - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (B2 : (q + n - 1 - pf_F v pos) / 8 < 72) by (apply Z.div_lt_upper_bound; lia).
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q - pf_F v pos) / 8) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (pf_SH v pos + (q + n - 1 - pf_F v pos) / 8) 8 ltac:(lia)) as M2.
  replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
  rewrite (HFSH (s - pf_SH v pos)) by lia. discriminate.
Qed.
Lemma b8_rom : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  rt_rom_view SEGS B Wc memc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (_ & _ & HOBJ & _). destruct HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
intros a (sg & Hsg & Hw & Hr) Ho He. exact (HROD a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.
(* strcmp(&c->seg[i], np) at a state of B8a's loop: RtString.astrcmp_realizes's premises in its order *)
Lemma b8_strcmp_pre : forall v pos lyc Sc Wc rX memc mdc regsc cf np name i,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> (i < length (rc_seg cf))%nat ->
  sa_str (rdW Wc memc) np name -> pf_inb (pf_F v pos + PF_O_BUF) np name ->
  spZ regsc = pf_s1 v -> YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) ->
  getr regsc 4 = w64 (as_tp B) ->
  exists sx,
    seg_spec.zs sx = rs_name (nth i (rc_seg cf) rseg_d) /\ ~ In seg_spec.ZERO sx /\
    ecall_pre_stk SEGS B (2 * ESTACK) lyc Sc Wc regsc memc mdc /\
    0 < p_c v + 356 * Z.of_nat i /\ 0 < np /\
    astr_at SEGS Wc memc (p_c v + 356 * Z.of_nat i) sx /\ astr_at SEGS Wc memc np (seg_spec.zb name) /\
    aread_ok SEGS (2 * ESTACK) Wc regsc memc (p_c v + 356 * Z.of_nat i) (astr_len sx + 1) /\
    aread_ok SEGS (2 * ESTACK) Wc regsc memc np (astr_len (seg_spec.zb name) + 1) /\
    atail_vis SEGS Wc memc (p_c v + 356 * Z.of_nat i + astr_len sx) /\
    atail_vis SEGS Wc memc (np + astr_len (seg_spec.zb name)) /\
    rt_rom_view SEGS B Wc memc.
Proof.
intros v pos lyc Sc Wc rX memc mdc regsc cf np name i HB HRC Hi HS [Hb1 Hb2] Hsp Hra Hgp Htp.
destruct (b8_geo _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof asan_consts as (C1 & _). pose proof pf_B_values as (_ & _ & _ & _ & _ & _ & _ & SPF & _).
rewrite SPF in G1.
pose proof HB as (_ & HFI & HOBJ & _).
destruct HFI as (HJ & _).
destruct HOBJ as (_ & _ & _ & _ & (bc & mc & Hbc & Hc1 & Hc2) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hbc) as (_ & Hbc4 & Hbcc & _ & _ & _ & Hm).
pose proof (req_size_pos mc (proj1 Hm)) as [_ Hreq].
destruct (b8_rname _ _ _ i HRC Hi) as (sx & Hsx & Nx & Zx & Lx).
destruct (sa_strz_bytes SEGS (w_H Wc) memc np name (proj1 HS)) as (Hnb & Nn & Zn).
pose proof (proj1 (b8_rconf_n _ _ _ HRC)) as _. pose proof (proj2 (b8_rconf_n _ _ _ HRC)) as L32.
unfold PF_O_BUF in *. unfold seg_spec.SEG_C_SIZE in *.
assert (Lzb : astr_len (seg_spec.zb name) = Z.of_nat (length name))
  by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
assert (Lsx : astr_len sx = Z.of_nat (length sx)) by reflexivity.
assert (HF8 : pf_F v pos mod 8 = 0) by (pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)); lia).
assert (HC16 : p_c v mod 16 = 0) by (pose proof HB as (HCX & _); exact (proj2 (b8_cx v HCX))).
exists sx. split; [exact Zx|]. split; [exact Nx|].
split.
{ apply (PaArt.ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 regsc (pf_s1 v - pf_sp0 v) HJ);
    [lia | | lia | unfold ESTACK; lia | rewrite SPF; unfold ESTACK; lia | exact Hra | exact Hgp | exact Htp].
  pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)). pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)).
  pose proof (Z.div_mod (pf_s1 v - pf_sp0 v) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_s1 v - pf_sp0 v) 16 ltac:(lia)).
  lia. }
split; [lia|]. split; [lia|].
split; [split; [exact Hsx | exact Nx]|].
split; [split; [exact Hnb | exact Nn]|].
split.
{ apply (PaArt.aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc regsc memc mdc bc mc); [exact HAR | exact Hbc | lia | | lia | ].
  - rewrite Lsx. lia.
  - rewrite Hsp. unfold ESTACK. lia. }
split.
{ rewrite Lzb.
  destruct (b8_buf_addr v pos lyc Sc Wc rX memc mdc np (Z.of_nat (length name) + 1) HB) as (A0 & A1 & A2 & A3 & A4);
    [unfold PF_O_BUF; lia | lia | unfold PF_O_BUF; lia|].
  split; [exact A0|]. split; [exact A1|]. split; [lia|].
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  intros a Ha. split; [apply (b8_frame_some v pos lyc Sc Wc rX memc mdc PF_SC_LINE a HB); lia|].
  unfold ascratch_stk. rewrite Hsp. unfold ESTACK. lia. }
split.
{ rewrite Lsx. intros a Ha. pose proof (Z.mod_pos_bound (p_c v + 356 * Z.of_nat i + Z.of_nat (length sx)) 8 ltac:(lia)).
  apply (b8_rconf_some _ _ cf a HRC). unfold seg_spec.SEG_C_SIZE. lia. }
split.
{ rewrite Lzb. intros a Ha. pose proof (Z.div_mod (np + Z.of_nat (length name)) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (np + Z.of_nat (length name)) 8 ltac:(lia)).
  pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)).
  apply (b8_frame_some v pos lyc Sc Wc rX memc mdc PF_SC_LINE a HB). lia. }
exact (b8_rom v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB).
Qed.
End e.
End f.
End d.
