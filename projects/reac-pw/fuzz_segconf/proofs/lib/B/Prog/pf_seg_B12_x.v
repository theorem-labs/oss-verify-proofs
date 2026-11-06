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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 348 of its 395 lines of code are new or changed and 406 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the keep family of the two exit pieces
   of segment B12 of reac_segconf_parse_file's walk (BAD 0x888a4 -> KREF, pf_seg_B12_b.v; STORE 0x88df8 -> PROV2,
   pf_seg_B12_s.v; the kit is pf_seg_B12_k.v). A B12 sub-lane of the image-B G3 walk owner, 2026-10-30. proves no function
   (kind: segment helper of reac_segconf_parse_file's walk, pieces BAD and STORE of segment B12).
    ADAPTED from the B10b segment lane's keep family (lib/B/Prog/pf_seg_B10b_j.v at commit 961c19ce3f65:
   b10j_k_* / b10j_keep_*, itself from a working branch's lib/A/Prog/pf_a10b_j.v) with its kept relation
   (every byte but the frame's 144 shadow cells) replaced by agreement outside X = [s1 - 2 ESTACK, s1) union
   [w, w + 8): the strcasecmp windows (b12_mid's kept_out) and STORE's two `sw` at cur + 24, cur + 28 (BAD writes
   nothing: there w = s1 - 8 lies inside the window, b12x_wok's second case).
   Every object a pf_pieces cut reads is outside X (b12x_geo): the text and c are heap blocks below alloc_ceiling
   (the text apart from c by reader_pre's sa_disj over its read span); shadow bytes lie in the shadow band, which no
   application block meets (AR_blocks_law's in_app), below alloc_ceiling; image bytes lie below kImgEnd and c's block
   is off_img (SegPaLib.blk_off_imgP); the class-5 frame (cur_name, buf, the flag word) is apart from c's block
   (YCbq sep_block_frame); the slots and the saved registers lie at or above s1.
     [b12x_geo]                   the geometry the keep lemmas need, from the entry bundle and the mid state.
     [b12x_k_*]                   one byte / one object class read alike at the two readers.
     [b12x_keep_obj / _saved / _flag / _slot / _sl / _fsh / _nm / _rconf / _vstr / _st]  the cut's facts carried.
     [b12x_base]                  pf_base at PF_SC_LINE at a later memory of the same frame state.
     [b12x_regs]                  pf_fi's and PF_RL / PF_RM's registers from the registers B12_KEPT kept. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B12_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- arithmetic: a C string's read span (seg_spec.cstr_span: its bytes, its NUL, the slack to the next
   8-byte boundary) ---------- *)
(* the span's end is where sa_tail's slack ends *)
Lemma b12x_span : forall p (s : list Z),
  p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 = p + seg_spec.cstr_span p s.
Proof.
intros p s. unfold seg_spec.cstr_span.
remember (p + Z.of_nat (length s)) as e eqn:He.
replace (- (p + Z.of_nat (length s) + 1)) with (- (e + 1)) by lia.
pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (- (e + 1)) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (- (e + 1)) 8 ltac:(lia)) as M2.
lia.
Qed.
Lemma b12x_span_ge : forall p (s : list Z), Z.of_nat (length s) + 1 <= seg_spec.cstr_span p s.
Proof.
intros p s. unfold seg_spec.cstr_span.
pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
Qed.
(* the span ends at or below an 8-aligned bound past the NUL *)
Lemma b12x_round : forall p (s : list Z) M, M mod 8 = 0 -> p + Z.of_nat (length s) + 1 <= M ->
  p + seg_spec.cstr_span p s <= M.
Proof.
intros p s M HM H. rewrite <- b12x_span. remember (p + Z.of_nat (length s)) as e eqn:He.
pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as M1.
pose proof (Z.div_mod M 8 ltac:(lia)) as D2. rewrite HM in D2.
lia.
Qed.

(* ---------- readers that agree on a range ---------- *)
Lemma b12x_str_same : forall (rd rd' : reader) p s,
  (forall x, p <= x < p + seg_spec.cstr_span p s -> rd' x = rd x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s Ho [[Hz Hn] Ht].
pose proof (b12x_span_ge p s) as Hsp. pose proof (b12x_span p s) as Hse.
split; [split; [|exact Hn]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite Ho by lia.
  exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx. rewrite Ho by lia. exact (Ht x Hx).
Qed.
Lemma b12x_bytes_same : forall (rd rd' : reader) p l,
  (forall i, (i < length l)%nat -> rd' (p + Z.of_nat i) = rd (p + Z.of_nat i)) -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros rd rd' p l Ho H i Hi. rewrite Ho by exact Hi. exact (H i Hi). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma b12x_PF_SL_offs : forall (v : pfv (PI := PI)) pos ov, In ov (PF_SL v pos) -> 0x00 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(** ** The kept relation and where the written range w lies *)
(* rd' agrees with rd on every byte outside the strcasecmp windows and outside [w, w + 8) *)
Definition b12x_kept (v : pfv (PI := PI)) (w : Z) (rd rd' : reader) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> ~ (w <= a < w + 8) -> rd' a = rd a.
(* STORE: w = cur + 24 inside the block c; BAD: w inside the windows (nothing written outside them) *)
Definition b12x_wok (v : pfv (PI := PI)) (w : Z) : Prop :=
  (p_c v <= w /\ w + 8 <= p_c v + seg_spec.SEG_C_SIZE) \/ (pf_s1 v - 2 * ESTACK <= w /\ w + 8 <= pf_s1 v).
(* the geometry: s1 above the allocator's ceiling and its windows, the frame, c and the text below it, and every
   shadow, image, frame and text byte apart from [w, w + 8) *)
Definition b12x_geoP (v : pfv (PI := PI)) (pos w : Z) : Prop :=
  alloc_ceiling + 2 * ESTACK <= pf_s1 v /\ pf_s1 v + 0x160 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 64 = 0 /\
  4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  0 <= p_t v /\ p_t v + seg_spec.cstr_span (p_t v) (p_s v) <= alloc_ceiling /\
  b12x_wok v w /\
  (forall x, SHADOW_OFF <= x < kHighMemBeg -> ~ (w <= x < w + 8)) /\
  (forall x, 0x10000 <= x < kImgEnd -> ~ (w <= x < w + 8)) /\
  (forall x, pf_F v pos <= x < pf_F v pos + 2048 -> ~ (w <= x < w + 8)) /\
  (forall x, p_t v <= x < p_t v + seg_spec.cstr_span (p_t v) (p_s v) -> ~ (w <= x < w + 8)).

Lemma b12x_wok_win : forall v, b12x_wok v (pf_s1 v - 8).
Proof. intros v. right. assert (ESTACK = 4096) by reflexivity. lia. Qed.

(* b12_mid's kept_out: the mid memory agrees with IGN's outside the windows (w = s1 - 8) *)
Lemma b12x_kept_mid : forall e regs1 memc1 mdc1, b12_mid B e regs1 memc1 mdc1 ->
  b12x_kept (e_v e) (pf_s1 (e_v e) - 8) (rdW (e_W e) (e_mem e)) (rdW (e_W e) memc1).
Proof. intros e regs1 memc1 mdc1 (_ & HK & _) a Ha Hw _. exact (HK a Ha Hw). Qed.

(* a run that writes only [w, w + 8) after the mid state *)
Lemma b12x_kept_step : forall v w (rd0 rd1 rd2 : reader),
  b12x_kept v (pf_s1 v - 8) rd0 rd1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (w <= a < w + 8) -> rd2 a = rd1 a) ->
  b12x_kept v w rd0 rd2.
Proof.
intros v w rd0 rd1 rd2 H1 H2 a Ha Hwin Hw. assert (ESTACK = 4096) by reflexivity.
rewrite (H2 a Ha Hw). apply H1; [exact Ha | exact Hwin | lia].
Qed.

Lemma b12x_geo : forall e regs1 memc1 mdc1 w, b12_ent B e -> b12_mid B e regs1 memc1 mdc1 -> b12x_wok (e_v e) w ->
  b12x_geoP (e_v e) (e_pos e) w.
Proof.
intros e regs1 memc1 mdc1 w HE HM HW.
pose proof (b12_geo B e regs1 memc1 mdc1 HE HM) as G.
destruct G as (Hin & EF & Hly & HF1 & HF2 & HF64 & HFa & Hc1 & Hc2 & Hc16 & Hheap & Hgi32 & Hgi & Hs1a & Hs1b
  & Hsp47 & Hs1m & Hsp16 & Hv1 & Hv2 & HAR & Hs1c).
pose proof HE as (HI & _).
destruct HI as ((HCX & HFI & HOBJ & HSL & HSH) & _).
pose proof HOBJ as (_ & _ & Hth & _).
pose proof HCX as (_ & _ & _ & _ & _ & Ht64 & _ & _ & (fe & HPRE) & _).
destruct HPRE as (HRP & _).
pose proof HRP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdisj & _).
destruct Hheap as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbc & Happ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
pose proof (blk_off_imgP B _ _ _ _ _ b m HAR Hb) as Hoff.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 5 (e_pos e) HAR Hb Hin) as Hsep.
destruct Hth as (b' & m' & Hb' & Ht1 & Ht2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b' m' HAR Hb') as (_ & _ & Hbc' & _ & _ & _ & Hm').
pose proof (req_size_pos m' ltac:(lia)) as [_ Hrq'].
pose proof asan_consts as (C1 & _).
pose proof ASAN_CEIL_range as (_ & Hac4096). unfold ASAN_CEIL in Hac4096.
assert (Hac8 : alloc_ceiling mod 8 = 0).
{ apply Z.mod_divide in Hac4096 as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with ((q * 512) * 8) by lia.
  apply Z_mod_mult. }
assert (ES : ESTACK = 4096) by reflexivity.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EF in Hsep. change (fs_frame_bytes 5) with 2048 in Hsep.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold off_img in Hoff. unfold pf_len in Ht2. unfold sa_disj in Hdisj.
assert (Htsp : p_t (e_v e) + seg_spec.cstr_span (p_t (e_v e)) (p_s (e_v e)) <= alloc_ceiling)
  by (apply b12x_round; [exact Hac8 | lia]).
unfold b12x_geoP.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HF64|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Htsp|]. split; [exact HW|].
split; [intros x Hx; unfold SHADOW_OFF, kHighMemBeg in Hx; destruct HW as [[Hw1 Hw2]|[Hw1 Hw2]]; lia|].
split; [intros x Hx; unfold kImgEnd in Hx; destruct HW as [[Hw1 Hw2]|[Hw1 Hw2]]; lia|].
split; [intros x Hx; destruct HW as [[Hw1 Hw2]|[Hw1 Hw2]]; lia|].
intros x Hx. destruct HW as [[Hw1 Hw2]|[Hw1 Hw2]]; lia.
Qed.

(** ** One byte, one object class *)
Lemma b12x_k_low : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall x, 0 <= x < alloc_ceiling -> ~ (w <= x < w + 8) -> rd' x = rd x.
Proof.
intros v pos w rd rd' G K x Hx Hw. pose proof G as (S1 & _). pose proof asan_consts as (C1 & _).
assert (ES : ESTACK = 4096) by reflexivity.
apply K; [lia | lia | exact Hw].
Qed.
Lemma b12x_k_hi : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall x, pf_s1 v <= x < 2 ^ 64 -> rd' x = rd x.
Proof.
intros v pos w rd rd' G K x Hx. pose proof G as (S1 & S2 & S3 & F1 & F2 & F3 & Cc1 & Cc2 & T1 & T2 & HW & _).
pose proof asan_consts as (C1 & _). assert (ES : ESTACK = 4096) by reflexivity.
apply K; [lia | lia |]. destruct HW as [[Hw1 Hw2]|[Hw1 Hw2]]; lia.
Qed.
Lemma b12x_k_shadow : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall x, SHADOW_OFF <= x < kHighMemBeg -> rd' x = rd x.
Proof.
intros v pos w rd rd' G K x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS & _).
pose proof asan_consts as (C1 & _).
apply (b12x_k_low v pos w rd rd' G K); [unfold SHADOW_OFF, kHighMemBeg in *; lia | exact (GS x Hx)].
Qed.
Lemma b12x_k_img : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall x, 0x10000 <= x < kImgEnd -> rd' x = rd x.
Proof.
intros v pos w rd rd' G K x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GI & _).
pose proof asan_consts as (C1 & _).
apply (b12x_k_low v pos w rd rd' G K); [unfold kImgEnd in *; lia | exact (GI x Hx)].
Qed.
Lemma b12x_k_frame : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall x, pf_F v pos <= x < pf_F v pos + 2048 -> rd' x = rd x.
Proof.
intros v pos w rd rd' G K x Hx. pose proof G as (_ & _ & _ & F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & GF & _).
apply (b12x_k_low v pos w rd rd' G K); [lia | exact (GF x Hx)].
Qed.
Lemma b12x_k_text : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall x, p_t v <= x < p_t v + seg_spec.cstr_span (p_t v) (p_s v) -> rd' x = rd x.
Proof.
intros v pos w rd rd' G K x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & _ & _ & _ & _ & GT).
apply (b12x_k_low v pos w rd rd' G K); [lia | exact (GT x Hx)].
Qed.
(* an object below alloc_ceiling: its shadow bytes and its shadow hull lie in the shadow band *)
Lemma b12x_k_addr : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall q n, 0 <= q -> q + n <= alloc_ceiling -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros v pos w rd rd' G K q n Hq Hqn (H0 & H1 & H2 & H3 & H4). pose proof asan_consts as (C1 & _).
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
- intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite (b12x_k_shadow v pos w rd rd' G K); [exact Hs|].
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le x 8 ltac:(lia)).
  unfold SHADOW_OFF, kHighMemBeg. lia.
- intros Hn s Hs. pose proof (H4 Hn s Hs) as Hv. rewrite (b12x_k_shadow v pos w rd rd' G K); [exact Hv|].
  unfold shadow_addr in Hs.
  pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)) as Q0.
  pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)) as Q1.
  pose proof (Z.div_mod (SHADOW_OFF + q / 8) 8 ltac:(lia)) as DA.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + q / 8) 8 ltac:(lia)) as MA.
  pose proof (Z.mul_div_le (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia)) as MB.
  unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
Lemma b12x_k_lit : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros v pos w rd rd' G K a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (b12x_str_same rd rd' a s); [|exact Hs].
destruct (Hi a ltac:(lia)) as (H0 & _). pose proof (pa_img_range _ H0) as R0.
destruct (Hi (a + Z.of_nat (length s)) ltac:(lia)) as (H1 & _). pose proof (pa_img_range _ H1) as R1.
assert (HE : a + seg_spec.cstr_span a s <= kImgEnd) by (apply b12x_round; [unfold kImgEnd; reflexivity | lia]).
intros x Hx. apply (b12x_k_img v pos w rd rd' G K). lia.
Qed.
Lemma b12x_k_cat : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros v pos w rd rd' G K cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp.
split; [|exact (b12x_k_lit v pos w rd rd' G K tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd rd'); [exact Htp|].
intros k Hk. apply (b12x_k_img v pos w rd rd' G K).
destruct (Hi (pin_spec.row_addr cat i + k)
  ltac:(unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES; lia)) as (H1 & _).
exact (pa_img_range _ H1).
Qed.
Lemma b12x_k_rod : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros v pos w rd rd' G K H a Hro Ho He. rewrite (b12x_k_img v pos w rd rd' G K a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- exact (pa_img_range a (ex_intro _ sg (conj Hsg Hr))).
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma b12x_k_ssp : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros v pos w rd rd' G K (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k))
  by (intros a Ha k Hk; apply (b12x_k_img v pos w rd rd' G K); lia).
split; [rewrite (rdword_ext rd rd' gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (rdword_ext rd rd' guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.

(** ** The cut's facts, carried *)
Lemma b12x_keep_obj : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall lyc Sc, pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos w rd rd' G K lyc Sc (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
pose proof G as (_ & _ & _ & _ & _ & _ & Cc1 & Cc2 & T1 & T2 & _).
pose proof (b12x_span_ge (p_t v) (p_s v)) as Hsp.
split; [exact (b12x_str_same rd rd' _ _ (b12x_k_text v pos w rd rd' G K) H1)|].
split; [apply (b12x_k_addr v pos w rd rd' G K); [lia | unfold pf_len; lia | exact H2]|]. split; [exact H3|].
split; [apply (b12x_k_addr v pos w rd rd' G K); [lia | lia | exact H4]|]. split; [exact H5|].
split; [exact (b12x_k_cat v pos w rd rd' G K _ H6)|].
split; [intros x Hx; exact (b12x_k_lit v pos w rd rd' G K _ _ (H7 x Hx))|].
split; [exact (b12x_k_rod v pos w rd rd' G K H8) | exact (b12x_k_ssp v pos w rd rd' G K H9)].
Qed.
Lemma b12x_keep_saved : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall regs, pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos w rd rd' G K regs H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
pose proof G as (S1 & S2 & S3 & _).
intros k Hk. apply (b12x_k_hi v pos w rd rd' G K). lia.
Qed.
Lemma b12x_keep_flag : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros v pos w rd rd' G K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. apply (b12x_k_frame v pos w rd rd' G K). lia.
Qed.
Lemma b12x_keep_slot : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall off x, 0 <= off <= 0x158 -> rdword rd (pf_s1 v + off) = Some x -> rdword rd' (pf_s1 v + off) = Some x.
Proof.
intros v pos w rd rd' G K off x Ho H. rewrite (rdword_ext rd rd'); [exact H|].
pose proof G as (S1 & S2 & S3 & _). intros k Hk. apply (b12x_k_hi v pos w rd rd' G K). lia.
Qed.
Lemma b12x_keep_sl : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall L, (forall ov, In ov L -> 0 <= fst ov <= 0xd8) -> pf_sl rd (pf_s1 v) L -> pf_sl rd' (pf_s1 v) L.
Proof.
intros v pos w rd rd' G K L HL H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
exact (b12x_keep_slot v pos w rd rd' G K (fst ov) (snd ov) ltac:(pose proof (HL ov Hov); lia) (H ov Hov)).
Qed.
Lemma b12x_keep_fsh : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall sc, pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos w rd rd' G K sc H i Hi. rewrite (b12x_k_shadow v pos w rd rd' G K); [exact (H i Hi)|].
pose proof G as (_ & _ & _ & F1 & F2 & _). pose proof asan_consts as (C1 & _).
unfold pf_SH, shadow_addr. pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (pf_F v pos) 8 ltac:(lia)). unfold SHADOW_OFF, kHighMemBeg. lia.
Qed.
Lemma b12x_keep_nm : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall nm, pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos w rd rd' G K nm (f & Hb & Henc). exists f. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi.
rewrite (b12x_k_frame v pos w rd rd' G K) by (unfold PF_O_CN; lia). exact (Hb i ltac:(lia)).
Qed.
(* c's bytes, when nothing was written inside c (BAD) *)
Lemma b12x_keep_rconf : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  (w + 8 <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= w) ->
  forall cf, sa_rconf rd (p_c v) cf -> sa_rconf rd' (p_c v) cf.
Proof.
intros v pos w rd rd' G K Hw cf (bs & Hb & Henc). exists bs. split; [|exact Henc].
apply (b12x_bytes_same rd rd'); [|exact Hb].
intros i Hi. destruct Henc as [Hl _].
pose proof G as (_ & _ & _ & _ & _ & _ & Cc1 & Cc2 & _).
apply (b12x_k_low v pos w rd rd' G K); lia.
Qed.
(* a C string in buf (val) *)
Lemma b12x_keep_vstr : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  forall vp val, pf_inb (pf_F v pos + PF_O_BUF) vp val -> sa_str rd vp val -> sa_str rd' vp val.
Proof.
intros v pos w rd rd' G K vp val (H1 & H2) H. pose proof G as (_ & _ & _ & F1 & F2 & F3 & _).
assert (HB8 : (pf_F v pos + 0x240) mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 64 + 0x240) with ((8 * q + 72) * 8) by lia.
  apply Z_mod_mult. }
assert (HE : vp + seg_spec.cstr_span vp val <= pf_F v pos + 0x240)
  by (apply b12x_round; [exact HB8 | unfold PF_O_BUF in H2; lia]).
apply (b12x_str_same rd rd' vp val); [|exact H].
intros x Hx. apply (b12x_k_frame v pos w rd rd' G K). unfold PF_O_BUF in H1. lia.
Qed.
(* the spine's state, when nothing was written inside c (BAD) *)
Lemma b12x_st : forall v pos w rd rd', b12x_geoP v pos w -> b12x_kept v w rd rd' ->
  (w + 8 <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= w) ->
  forall cf cur nm k, pf_st v pos rd cf cur nm k -> pf_st v pos rd' cf cur nm k.
Proof.
intros v pos w rd rd' G K Hw cf cur nm k (HRC & HCUR & HNM & HCNT & HC0).
split; [exact (b12x_keep_rconf v pos w rd rd' G K Hw cf HRC)|].
split; [exact HCUR|]. split; [exact (b12x_keep_nm v pos w rd rd' G K nm HNM)|]. split; [exact HCNT|].
exact (b12x_keep_slot v pos w rd rd' G K 0xc0 _ ltac:(lia) HC0).
Qed.

(** ** The registers and the cut's base at a later memory *)
Lemma b12x_regs : forall e (rX' : bvmap 5 word), b12_ent B e ->
  (forall r, In r B12_KEPT -> getr rX' (Z_to_bv 5 r) = getr (e_rX e) (Z_to_bv 5 r)) ->
  pf_rg rX' [(2, pf_s1 (e_v e)); (3, as_gp B); (4, as_tp B); (8, pf_sp0 (e_v e)); (9, pf_s1 (e_v e));
             (20, SHADOW_OFF)] /\
  pf_rg rX' (PF_RL (e_v e) (e_pos e) ++ PF_RM (e_v e) (e_o e) (e_ln e)).
Proof.
intros e rX' HE HR. pose proof HE as (HI & _).
destruct HI as ((_ & HFI & _) & _ & _ & _ & _ & HRG).
destruct HFI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
split.
- unfold pf_rg. rewrite Forall_forall. intros [r x] Hin. cbn [fst snd].
  rewrite HR; [exact (b12_rg _ _ _ _ HRG0 Hin)|].
  cbn [In] in Hin. unfold B12_KEPT. cbn [In].
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia |]). destruct Hin.
- unfold pf_rg. rewrite Forall_forall. intros [r x] Hin. cbn [fst snd].
  rewrite HR; [exact (b12_rg _ _ _ _ HRG Hin)|].
  unfold PF_RL, PF_RM in Hin. cbn [In app] in Hin. unfold B12_KEPT. cbn [In].
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia |]). destruct Hin.
Qed.

(* pf_base at PF_SC_LINE at a memory memc' of the same frame state: its journal, its bytes as IGN's outside X, the
   registers B12_KEPT as IGN's *)
Lemma b12x_base : forall e regs1 memc1 mdc1 w (rX' : bvmap 5 word) memc' mdc',
  b12_ent B e -> b12_mid B e regs1 memc1 mdc1 -> b12x_wok (e_v e) w ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (e_v e)) (seg_spec.RC_PARSE_W (p_c (e_v e)))
    (p_ly (e_v e)) (p_S (e_v e)) (p_W (e_v e)) (p_mem (e_v e)) (p_md (e_v e)) [(5, e_pos e)]
    (e_ly e) (e_S e) (e_W e) memc' mdc' 0 ->
  b12x_kept (e_v e) w (rdW (e_W e) (e_mem e)) (rdW (e_W e) memc') ->
  (forall r, In r B12_KEPT -> getr rX' (Z_to_bv 5 r) = getr (e_rX e) (Z_to_bv 5 r)) ->
  pf_base B (e_v e) (e_pos e) (e_ly e) (e_S e) (e_W e) rX' memc' mdc' PF_SC_LINE.
Proof.
intros e regs1 memc1 mdc1 w rX' memc' mdc' HE HM HW HJ' HK HR.
pose proof (b12x_geo e regs1 memc1 mdc1 w HE HM HW) as G.
destruct (b12x_regs e rX' HE HR) as (HRG0' & _).
pose proof HE as (HI & _).
destruct HI as ((HCX & HFI & HOBJ & HSL & HSH) & _).
destruct HFI as (HJ0 & Hly & HSc & HPm & HSAV & HFL & HFRM & HTF & HSLc & HRG0).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPm|].
  split; [exact (b12x_keep_saved _ _ _ _ _ G HK _ HSAV)|].
  split; [exact (b12x_keep_flag _ _ _ _ _ G HK HFL)|].
  split; [exact HFRM|]. split; [exact HTF|].
  split; [|exact HRG0'].
  exact (b12x_keep_sl _ _ _ _ _ G HK [(0xc8, p_c (e_v e))]
    ltac:(intros ov Hov; cbn [In] in Hov; destruct Hov as [<- | []]; cbn [fst]; lia) HSLc). }
split; [exact (b12x_keep_obj _ _ _ _ _ G HK _ _ HOBJ)|].
split; [exact (b12x_keep_sl _ _ _ _ _ G HK _ (b12x_PF_SL_offs (e_v e) (e_pos e)) HSL)|].
exact (b12x_keep_fsh _ _ _ _ _ G HK _ HSH).
Qed.

(* val, from the key split at IGN, at a later memory *)
Lemma b12x_val : forall e regs1 memc1 mdc1 w (memc' : word -> option byte),
  b12_ent B e -> b12_mid B e regs1 memc1 mdc1 -> b12x_wok (e_v e) w ->
  b12x_kept (e_v e) w (rdW (e_W e) (e_mem e)) (rdW (e_W e) memc') ->
  sa_str (rdW (e_W e) memc') (e_vp e) (e_val e) /\
  pf_inb (pf_F (e_v e) (e_pos e) + PF_O_BUF) (e_vp e) (e_val e).
Proof.
intros e regs1 memc1 mdc1 w memc' HE HM HW HK.
pose proof (b12x_geo e regs1 memc1 mdc1 w HE HM HW) as G.
pose proof HE as (HI & _). destruct HI as (_ & _ & _ & HKV & _).
destruct HKV as (_ & _ & _ & HVS & HVB).
split; [exact (b12x_keep_vstr _ _ _ _ _ G HK _ _ HVB HVS) | exact HVB].
Qed.

End e.
End f.
End d.
