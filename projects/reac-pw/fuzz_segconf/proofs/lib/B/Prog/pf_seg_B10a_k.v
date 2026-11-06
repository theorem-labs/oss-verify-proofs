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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 526 of its 575 lines of code are new or changed and 404 lines of the source are left out. *)
(* reac_segconf_parse_file (image B, fuzz_segconf.asan-ubsan, 0x87e38), segment B10a (ROLE 0x88630 -> INTENT 0x888e4,
   61 instructions: 0x88630-0x886d4, 0x888bc-0x888e4 and the slow arms 0x88fb4-0x88fcc, 0x8923c-0x89244,
   0x89280-0x89288; checks B#16, B#17, B#25; UBSan trap branches T17 0x8869c, T20 0x888c4; no call;
   lib/B/Prog/pf_pieces.v S_B10a): the kit of the segment's walk. The B10a segment lane of the image-B G3 walk owner, 2026-10-30.
   ADAPTED from the image-A G3 walk owner's image-A kit lib/A/Prog/pf_a10a_k.v (commit 73bafa8e5cd9, an
   image-A segment lane): its pure facts of the role fold, the bytes the segment may change (b10_D: low[64] at F + 0x280 and its
   eight shadow cells SH + 0x50 .. SH + 0x57), the frame facts the journal gives, the transfer of the cut's reader
   facts to a reader that agrees off b10_D, and the mid-segment state. Re-derived on image B's cut predicates
   (pf_fi with the trap facts pf_tf, slot 0xc8 and s4 = SHADOW_OFF; pf_st with slot 0xc0; INV_KV with val in slot
   0x70; INV_INTENT with s7 = low) and B's code: the registers B10a writes are a0-a6 and s7 (0x888c8), so the
   kept list is B10_KZ below (A's A10_KZ named s3, which A writes; B leaves s3 alone and writes s7). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob SegInstB
  refuse_c reac_segconf_parse_file_c pf_pieces.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the pure facts of the role branch (A kit's, unchanged: the C text R:234-238 is the same) ---- *)
(* R:236-238's fold, on a NUL-free value: the first cap - 1 - li bytes, folded *)
Lemma b10_r_low_map : forall v li cap, ~ In 0 v -> r_low v li cap = map lower (firstn (cap - S li) v).
Proof.
induction v as [|q r IH]; intros li cap H; cbn [r_low].
- destruct (cap - S li)%nat; reflexivity.
- assert (Hq : q <> 0) by (intros E; apply H; left; exact E).
  assert (Hr : ~ In 0 r) by (intros E; apply H; right; exact E).
  destruct (Z.eqb_spec q 0) as [E|_]; [contradiction|].
  destruct (Nat.ltb_spec (li + 1) cap) as [Hl|Hl].
  + replace (cap - S li)%nat with (S (cap - S (S li))) by lia. cbn [firstn map]. f_equal. apply IH. exact Hr.
  + replace (cap - S li)%nat with 0%nat by lia. reflexivity.
Qed.
Lemma b10_r_low64 : forall v, ~ In 0 v -> r_low v 0 64 = map lower (firstn 63 v).
Proof. intros v H. rewrite b10_r_low_map by exact H. reflexivity. Qed.
Lemma b10_r_low64_len : forall v, ~ In 0 v -> length (r_low v 0 64) = Nat.min (length v) 63.
Proof. intros v H. rewrite b10_r_low64, length_map, length_firstn by exact H. lia. Qed.
Lemma b10_lower_range : forall c, 0 <= c < 256 -> 0 <= lower c < 256.
Proof. intros c Hc. unfold lower. destruct ((65 <=? c) && (c <=? 90)) eqn:E; [|lia]. apply andb_prop in E as [E1 E2]. lia. Qed.
(* the key line's role step (R:228-246): r_key on a split line whose key is "role" is pf_role_step *)
Lemma b10_r_key_role : forall cf gi nm ln line key val,
  (exists ei : nat, strchr line EQ = Some ei /\ key = r_trim (firstn ei line) /\
                    val = r_unquote (r_trim (skipn (S ei) line))) ->
  strcasecmp key S_role = 0 ->
  r_key cf (Some gi) nm ln line = pf_role_step cf gi nm ln val.
Proof.
intros cf gi nm ln line key val (ei & Hs & Hk & Hv) Hr. unfold r_key. rewrite Hs. cbv beta iota zeta.
rewrite <- Hk, <- Hv, Hr. reflexivity.
Qed.
(* the fold of one byte (0x88688-0x88694: c - 'A' <u 26, shifted by 5 and added; `sb` keeps the low byte) *)
Lemma b10_fold_arith : forall c,
  0 <= c < 256 ->
  ((c + Z.shiftl (if (c + -65) mod 2 ^ 64 <? 26 then 1 else 0) 5) mod 2 ^ 64) mod 256 = lower c.
Proof.
intros c Hc. unfold lower.
destruct (Z.ltb_spec ((c + -65) mod 2 ^ 64) 26) as [Hlt|Hge].
- assert (Hu : (65 <=? c) && (c <=? 90) = true).
  { destruct (Z.leb_spec 65 c) as [H1|H1]; cbn [andb].
    - destruct (Z.leb_spec c 90) as [H2|H2]; [reflexivity|].
      rewrite Z.mod_small in Hlt by lia. lia.
    - assert (Hm : (c + -65) mod 2 ^ 64 = c + -65 + 1 * 2 ^ 64).
      { rewrite <- (Z_mod_plus_full (c + -65) 1 (2 ^ 64)). apply Z.mod_small. lia. }
      rewrite Hm in Hlt. lia. }
  rewrite Hu. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
  apply andb_prop in Hu as [Hu1 Hu2]. apply Z.leb_le in Hu1. apply Z.leb_le in Hu2.
  rewrite Z.mod_small by lia. rewrite Z.mod_small; lia.
- assert (Hu : (65 <=? c) && (c <=? 90) = false).
  { destruct (Z.leb_spec 65 c) as [H1|H1]; cbn [andb]; [|reflexivity].
    destruct (Z.leb_spec c 90) as [H2|H2]; [|reflexivity].
    rewrite Z.mod_small in Hge by lia. lia. }
  rewrite Hu. cbn [Z.shiftl]. rewrite Z.add_0_r, !Z.mod_small by lia. reflexivity.
Qed.
(* the length the fold leaves: a NUL-free val, k <= 63 bytes folded, the loop stops at k = 63 or at val's NUL *)
Lemma b10_len_63 : forall v, ~ In 0 v -> (63 <= length v)%nat -> length (r_low v 0 64) = 63%nat.
Proof. intros v H Hl. rewrite b10_r_low64_len by exact H. lia. Qed.
Lemma b10_len_end : forall v, ~ In 0 v -> (length v <= 63)%nat -> length (r_low v 0 64) = length v.
Proof. intros v H Hl. rewrite b10_r_low64_len by exact H. lia. Qed.

(* ---- readers that agree off a set ---- *)
Section t.
Variables (rd rd' : reader) (Fz : Z -> Prop).
Hypothesis K : forall a, Fz a -> rd' a = rd a.
Hypothesis G : forall a, rd a <> None -> rd' a <> None.
Lemma b10t_zs : forall p l, sa_zs rd p l -> (forall i, (i < length l)%nat -> Fz (p + Z.of_nat i)) -> sa_zs rd' p l.
Proof. intros p l H HF i Hi. rewrite K by (apply HF; exact Hi). exact (H i Hi). Qed.
Lemma b10t_bytes : forall p l, sa_bytes rd p l -> (forall i, (i < length l)%nat -> Fz (p + Z.of_nat i)) ->
  sa_bytes rd' p l.
Proof. intros p l H HF i Hi. rewrite K by (apply HF; exact Hi). exact (H i Hi). Qed.
Lemma b10t_tail : forall e, sa_tail rd e -> sa_tail rd' e.
Proof. intros e H x Hx. apply G, H, Hx. Qed.
Lemma b10t_str : forall p s, sa_str rd p s -> (forall i, 0 <= i <= Z.of_nat (length s) -> Fz (p + i)) ->
  sa_str rd' p s.
Proof.
intros p s ((Hz & Hn) & Ht) HF. split; [split; [|exact Hn] | exact (b10t_tail _ Ht)].
apply (b10t_zs _ _ Hz). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply HF. lia.
Qed.
Lemma b10t_word : forall a w, rdword rd a = w -> (forall k, 0 <= k < 8 -> Fz (a + k)) -> rdword rd' a = w.
Proof. intros a w H HF. rewrite (rdword_ext rd rd'); [exact H | intros k Hk; apply K, HF, Hk]. Qed.
Lemma b10t_ra : forall q n, range_addressable rd SHADOW_OFF q n ->
  (forall x, q <= x < q + n -> Fz (shadow_of_addr SHADOW_OFF x)) -> range_addressable rd' SHADOW_OFF q n.
Proof. intros q n H HF. apply (range_addressable_agree rd rd'); [intros x Hx; apply K, HF, Hx | exact H]. Qed.
Lemma b10t_hull : forall x n, shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros x n H s Hs. apply G, H, Hs. Qed.
Lemma b10t_addr : forall q n, sa_addr rd q n ->
  (forall x, q <= x < q + n -> Fz (shadow_of_addr SHADOW_OFF x)) -> sa_addr rd' q n.
Proof.
intros q n (H1 & H2 & H3 & H4 & H5) HF. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [exact (b10t_ra _ _ H4 HF)|]. intros Hn. exact (b10t_hull _ _ (H5 Hn)).
Qed.
End t.

(* ---- register lists ---- *)
(* the registers B10a never writes that the cuts name (pf_fi's 2, 3, 4, 8, 9, 20; PF_RL's 18, 21, 26; PF_RM's 25,
   22): its own writes are a0-a6 (x10-x16) and s7 (x23, 0x888c8) *)
Definition B10_KZ : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26].
Lemma b10_rg_in : forall (rX : bvmap 5 word) L r z, pf_rg rX L -> In (r, z) L -> getr rX (Z_to_bv 5 r) = w64 z.
Proof. intros rX L r z H Hin. exact (proj1 (Forall_forall _ _) H (r, z) Hin). Qed.
Lemma b10_rg_kept : forall (rX0 regs1 : bvmap 5 word) L,
  pf_rg rX0 L -> (forall r, In r B10_KZ -> getr regs1 (Z_to_bv 5 r) = getr rX0 (Z_to_bv 5 r)) ->
  Forall (fun rv => In (fst rv) B10_KZ) L -> pf_rg regs1 L.
Proof.
intros rX0 regs1 L H HK HL. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hrv.
rewrite HK by (apply HL; exact Hrv). apply H. exact Hrv.
Qed.
Ltac b10_inZ := cbn [In B10_KZ fst]; repeat (first [left; reflexivity | right]).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the bytes B10a writes: low[64] (F + 0x280; the fold's store 0x88698 and the NUL 0x888e0) and its eight shadow
   cells (0x88630-0x8864c, `sb zero, 0x50..0x57(s5)`) *)
Definition b10_D (v : pfv) (pos a : Z) : Prop :=
  (pf_F v pos + PF_O_LOW <= a < pf_F v pos + PF_O_LOW + 64) \/ (pf_SH v pos + 80 <= a < pf_SH v pos + 88).
(* the addresses off b10_D *)
Definition b10_far (v : pfv) (pos a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ b10_D v pos a.

Lemma b10_F8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
intros F H. rewrite (Z.div_mod F 32) by lia. rewrite H, Z.add_0_r.
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring. apply Z_mod_mult.
Qed.

(* the four kinds of address that are off b10_D: an image byte, an application byte outside the frame, the
   shadow cell of such a byte, a byte at or above alloc_ceiling (the real stack) *)
Lemma b10_nD : forall v pos a,
  pf_F v pos mod 32 = 0 -> in_app (pf_F v pos) 2048 -> off_img (pf_F v pos) 2048 ->
  pf_F v pos + 2048 <= alloc_ceiling ->
  ((0x10000 <= a < kImgEnd) \/
   ((a < pf_F v pos \/ pf_F v pos + 2048 <= a) /\ (a < kLowShadowBeg \/ kHighShadowEnd <= a)) \/
   (exists x, a = shadow_of_addr SHADOW_OFF x /\ 0 <= x < 2 ^ 47 /\ (x < pf_F v pos \/ pf_F v pos + 2048 <= x)) \/
   alloc_ceiling <= a) ->
  ~ b10_D v pos a.
Proof.
intros v pos a F32 Fapp Foff Fc Ha HD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (b10_F8 _ F32) as F8.
unfold b10_D, pf_SH, shadow_addr, PF_O_LOW in HD.
set (F := pf_F v pos) in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite F8, Z.add_0_r in DF.
unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, kImgEnd, kHighShadowEnd, SHADOW_OFF, ASAN_CEIL in *.
destruct Ha as [Ha | [Ha | [(x & -> & Hx & Hxo) | Ha]]].
- lia.
- lia.
- unfold shadow_of_addr in HD. pose proof (Z.div_mod x 8 ltac:(lia)) as DX.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MX. lia.
- lia.
Qed.
(* the frame's own bytes outside low, and its shadow cells outside low's eight *)
Lemma b10_nD_in : forall v pos a,
  pf_F v pos mod 32 = 0 -> in_app (pf_F v pos) 2048 -> pf_F v pos + 2048 <= alloc_ceiling ->
  ((pf_F v pos <= a < pf_F v pos + 2048 /\ (a < pf_F v pos + PF_O_LOW \/ pf_F v pos + PF_O_LOW + 64 <= a)) \/
   (exists i, a = pf_SH v pos + i /\ 0 <= i < 256 /\ (i < 80 \/ 88 <= i))) ->
  ~ b10_D v pos a.
Proof.
intros v pos a F32 Fapp Fc Ha HD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold b10_D, pf_SH, shadow_addr, PF_O_LOW in *.
set (F := pf_F v pos) in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *.
destruct Ha as [Ha | (i & -> & Hi & Hio)]; lia.
Qed.
(* a reader reads an address through its 64-bit word *)
Lemma b10_aview_wrap : forall H mem a, aview SEGS H mem a = aview SEGS H mem (a mod 2 ^ 64).
Proof.
intros H mem a. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod.
reflexivity.
Qed.
(* the fold's view of the frame's shadow at INTENT: low in scope, the rest as inside a line *)
Lemma b10_shb_low : forall i, pf_shb PF_SC_LOW i = if (80 <=? i) && (i <? 88) then 0 else pf_shb PF_SC_LINE i.
Proof.
intros i. unfold pf_shb, PF_SC_LOW, PF_SC_LINE. cbn [sc_cn sc_buf sc_low sc_l146 sc_known pf_io].
destruct (Z.leb_spec 80 i); destruct (Z.ltb_spec i 88); cbn [andb];
repeat match goal with |- context [i <? ?x] => destruct (Z.ltb_spec i x) end; try reflexivity; lia.
Qed.
(* buf's 64 cells are 0 inside a line *)
Lemma b10_shb_buf : forall i, 8 <= i < 72 -> pf_shb PF_SC_LINE i = 0.
Proof.
intros i Hi. unfold pf_shb, PF_SC_LINE. cbn [sc_cn sc_buf sc_low sc_l146 sc_known pf_io].
repeat match goal with |- context [i <? ?x] => destruct (Z.ltb_spec i x) end; try reflexivity; lia.
Qed.
(* n present bytes at a are the bytes of a list *)
Lemma b10_bytes_of : forall (rd : reader) a n,
  (forall i, (i < n)%nat -> exists z, rd (a + Z.of_nat i) = Some z /\ 0 <= z < 256) ->
  exists LB, length LB = n /\ sa_bytes rd a LB.
Proof.
intros rd a n H.
set (f := fun i : nat => Z_to_bv 8 (match rd (a + Z.of_nat i) with Some z => z | None => 0 end)).
exists (map f (seq 0 n)). split; [rewrite length_map, length_seq; reflexivity|].
intros i Hi. rewrite length_map, length_seq in Hi. destruct (H i Hi) as (z & Hz & Hr).
rewrite (nth_indep _ ZB0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
rewrite map_nth, seq_nth by exact Hi. cbn [Nat.add]. unfold f. rewrite Hz.
rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(* a byte of the frame and a cell of its shadow are different addresses *)
Lemma b10_lowsh_ne : forall v pos i j,
  pf_F v pos mod 32 = 0 -> in_app (pf_F v pos) 2048 -> pf_F v pos + 2048 <= alloc_ceiling ->
  0 <= i < 2048 -> 0 <= j < 256 -> pf_F v pos + i <> pf_SH v pos + j.
Proof.
intros v pos i j F32 Fapp Fc Hi Hj.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold pf_SH, shadow_addr, SHADOW_OFF.
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)) as MF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp.
lia.
Qed.

(* the shadow cell of a byte of the frame *)
Lemma b10_sh_of : forall v pos x,
  pf_F v pos mod 32 = 0 -> pf_F v pos <= x ->
  shadow_of_addr SHADOW_OFF x = pf_SH v pos + (x - pf_F v pos) / 8.
Proof.
intros v pos x F32 Hx. pose proof (b10_F8 _ F32) as F8.
unfold shadow_of_addr, pf_SH, shadow_addr.
replace x with (pf_F v pos + (x - pf_F v pos)) at 1 by lia.
rewrite (Z.div_mod (pf_F v pos) 8) at 1 by lia. rewrite F8, Z.add_0_r.
replace (8 * (pf_F v pos / 8) + (x - pf_F v pos)) with ((x - pf_F v pos) + (pf_F v pos / 8) * 8) by lia.
rewrite Z_div_plus by lia. lia.
Qed.

(* a range of frame bytes whose shadow cells read 0 is addressable *)
Lemma b10_frame_ra : forall (rd : reader) v pos q n,
  pf_F v pos mod 32 = 0 -> pf_F v pos <= q -> 0 <= n ->
  (forall x, q <= x < q + n -> rd (pf_SH v pos + (x - pf_F v pos) / 8) = Some 0) ->
  range_addressable rd SHADOW_OFF q n.
Proof.
intros rd v pos q n F32 Hq Hn H x Hx. exists 0. split; [|left; reflexivity].
rewrite (b10_sh_of v pos x F32) by lia. exact (H x Hx).
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* what the journal of a cut gives about the class-5 frame F = pf_F v pos *)
Lemma b10_frame : forall v pos lyc Sc Wc memc mdc,
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 ->
  lyc = p_ly v ->
  In (5, pos) (frames Sc) /\ AR SEGS B lyc Sc Wc memc mdc /\
  pf_F v pos mod 32 = 0 /\ in_app (pf_F v pos) 2048 /\ off_img (pf_F v pos) 2048 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> apresent (w_H Wc) memc a) /\
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)) /\
  (forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m ->
     (a < pf_F v pos \/ pf_F v pos + 2048 <= a) /\ in_app b (req_size m)).
Proof.
intros v pos lyc Sc Wc memc mdc HJ Hly.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfr; left; reflexivity).
assert (FB : fs_frame_bytes 5 = 2048) by reflexivity.
assert (FB8 : fs_frame_bytes 5 / 8 = 256) by reflexivity.
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (F32 & Fapp & Fp & Fsh).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Fb1 & Fb2 & _).
pose proof (frm_off_imgP B lyc Sc Wc memc mdc 5 pos HAR Hin) as Foff.
rewrite FB8 in Fsh. rewrite FB in Fapp, Fp, Fb2, Foff.
unfold pf_SH, pf_F. rewrite <- Hly.
split; [exact Hin|]. split; [exact HAR|]. split; [exact F32|]. split; [exact Fapp|]. split; [exact Foff|].
split; [lia|]. split; [lia|].
split; [intros a Ha; exact (proj1 (Fp a Ha))|].
split; [intros i Hi; exact (proj1 (Fsh i Hi))|].
intros b m a Hb Ha.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & Bapp & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite FB in Hsep.
split; [lia | exact Bapp].
Qed.

(* ---- the image's objects through a reader that agrees on the image ---- *)
Section i.
Variables (rd rd' : reader) (Fz : Z -> Prop).
Hypothesis K : forall a, Fz a -> rd' a = rd a.
Hypothesis G : forall a, rd a <> None -> rd' a <> None.
Hypothesis HI : forall a, 0x10000 <= a < kImgEnd -> Fz a.
Lemma b10t_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (H0 & Hs & Hp & Hr & Hi). split; [exact H0|]. split; [|split; [exact Hp | split; [exact Hr | exact Hi]]].
apply (b10t_str rd rd' Fz K G a s Hs). intros i Hi'. apply HI.
destruct (Hi (a + i) ltac:(lia)) as (Himg & _). exact (pa_img_range _ Himg).
Qed.
Lemma b10t_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hr i Hn) as (tp & Hw & Hl). exists tp. split; [|exact (b10t_lit _ _ Hl)].
apply (b10t_word rd rd' Fz K _ _ Hw). intros k Hk. apply HI.
unfold pin_spec.CAT_N in Hn. unfold pin_spec.row_addr, pin_spec.CAT_ROW.
destruct (Hi (pin_spec.row_addr cat i + k)) as (Himg & _);
  [unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES; lia|].
exact (pa_img_range _ Himg).
Qed.
Lemma b10t_ro : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Ha H1 H2. rewrite K; [exact (H a Ha H1 H2)|]. apply HI.
destruct Ha as [(s & Hs & _ & Hr) | Hr].
- apply pa_img_range. exists s. split; [exact Hs | exact Hr].
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma b10t_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (H1 & g & H2). split.
- apply (b10t_word rd rd' Fz K _ _ H1). intros k Hk. apply HI. unfold gotwA, kImgEnd. lia.
- exists g. apply (b10t_word rd rd' Fz K _ _ H2). intros k Hk. apply HI. unfold guardA, kImgEnd. lia.
Qed.
End i.

(* a byte of a live heap block, and its shadow cell, are off b10_D *)
Lemma b10_heap_far : forall v pos lyc Sc,
  pf_F v pos mod 32 = 0 -> in_app (pf_F v pos) 2048 -> off_img (pf_F v pos) 2048 ->
  pf_F v pos + 2048 <= alloc_ceiling ->
  (forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m ->
     (a < pf_F v pos \/ pf_F v pos + 2048 <= a) /\ in_app b (req_size m)) ->
  forall q n, sa_heap B lyc Sc q n -> forall x, q <= x < q + n ->
  b10_far v pos x /\ b10_far v pos (shadow_of_addr SHADOW_OFF x).
Proof.
intros v pos lyc Sc F32 Fapp Foff Fc HBLK q n (b & m & Hb & Hq1 & Hq2) x Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (HBLK b m x Hb ltac:(lia)) as (Hxo & Bapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp.
split.
- split; [lia|]. apply (b10_nD v pos x F32 Fapp Foff Fc). right; left. split; [exact Hxo|].
  unfold kLowShadowBeg, kHighShadowEnd. lia.
- split; [unfold shadow_of_addr, SHADOW_OFF; pose proof (Z.div_mod x 8 ltac:(lia));
          pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia|].
  apply (b10_nD v pos _ F32 Fapp Foff Fc). right; right; left. exists x. split; [reflexivity|]. split; [lia | exact Hxo].
Qed.

(* the caller's objects (pf_obj) survive a change of b10_D's bytes that keeps every present byte present *)
Lemma b10_obj_keep : forall v pos lyc Sc rd rd',
  pf_F v pos mod 32 = 0 -> in_app (pf_F v pos) 2048 -> off_img (pf_F v pos) 2048 ->
  pf_F v pos + 2048 <= alloc_ceiling ->
  (forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m ->
     (a < pf_F v pos \/ pf_F v pos + 2048 <= a) /\ in_app b (req_size m)) ->
  (forall a, b10_far v pos a -> rd' a = rd a) ->
  (forall a, rd a <> None -> rd' a <> None) ->
  pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc rd rd' F32 Fapp Foff Fc HBLK K G
  (Hs & Ha & Hh & Hca & Hch & Hcat & Hlit & Hro & Hssp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HI : forall a, 0x10000 <= a < kImgEnd -> b10_far v pos a).
{ intros a Hai. split; [unfold kImgEnd in Hai; lia|]. apply (b10_nD v pos a F32 Fapp Foff Fc). left. exact Hai. }
pose proof (b10_heap_far v pos lyc Sc F32 Fapp Foff Fc HBLK) as HH.
split.
{ apply (b10t_str rd rd' (b10_far v pos) K G _ _ Hs). intros i Hi. apply (HH _ _ Hh). unfold pf_len. lia. }
split.
{ apply (b10t_addr rd rd' (b10_far v pos) K G _ _ Ha). intros x Hx. apply (HH _ _ Hh x Hx). }
split; [exact Hh|].
split.
{ apply (b10t_addr rd rd' (b10_far v pos) K G _ _ Hca). intros x Hx. apply (HH _ _ Hch x Hx). }
split; [exact Hch|].
split; [exact (b10t_cat rd rd' (b10_far v pos) K G HI _ Hcat)|].
split; [intros x Hx; exact (b10t_lit rd rd' (b10_far v pos) K G HI _ _ (Hlit x Hx))|].
split; [exact (b10t_ro rd rd' (b10_far v pos) K HI Hro)|].
exact (b10t_ssp rd rd' (b10_far v pos) K HI Hssp).
Qed.

(* the numbers of the frame and the stack at ROLE (afn_pre's astk_ok, the journal's class-5 frame) *)
Lemma b10_geo : forall n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val,
  INV_KV B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val ->
  alloc_ceiling + STK_reac_segconf_parse_file <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\
  pf_sp0 v - 0x160 - 32 < pf_s1 v <= pf_sp0 v - 0x160 /\ pf_s1 v mod 32 = 0 /\
  pf_F v pos mod 32 = 0 /\ in_app (pf_F v pos) 2048 /\ off_img (pf_F v pos) 2048 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos + 2048 <= 2 ^ 47.
Proof.
intros n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val HKV.
destruct HKV as ((HCX & HFI & _) & _).
pose proof HFI as (HJ0 & Hly & _ & _ & _ & _ & _ & HTF & _).
pose proof HCX as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (b10_frame v pos lyc Sc Wc memc0 mdc0 HJ0 Hly) as (_ & _ & F32 & Fapp & Foff & F4096 & Fc & _).
pose proof HTF as (_ & _ & _ & HF47 & _). change (fs_frame_bytes 5) with 2048 in HF47.
assert (HSTK : STK_reac_segconf_parse_file = 12832) by reflexivity.
unfold pf_s1, pf_sp0 in *. pose proof (Z.mod_pos_bound (spZ (p_regs v) - 0x160) 32 ltac:(lia)) as M.
pose proof (Z.div_mod (spZ (p_regs v) - 0x160) 32 ltac:(lia)) as D.
split; [lia|]. split; [lia|]. split; [lia|].
split; [replace (spZ (p_regs v) - 352 - (spZ (p_regs v) - 352) mod 32) with ((spZ (p_regs v) - 352) / 32 * 32) by lia;
        apply Z_mod_mult|].
split; [exact F32|]. split; [exact Fapp|]. split; [exact Foff|]. split; [exact F4096|]. split; [exact Fc|]. lia.
Qed.

(* ---- the state inside B10a ---- *)
(* at a point of B10a: the ROLE cut's facts at its registers rX0 and memory memc0, and at the current registers
   regs1 and memory memc: the journal, every byte off b10_D as at ROLE, low's eight shadow cells 0 (in scope),
   low[0 .. k) the folded bytes of val, the registers of B10_KZ as at ROLE *)
Definition b10_mid (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX0 : bvmap 5 word) (memc0 : word -> option byte) (mdc0 : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (gi : nat) (kp vp : Z) (key val : list Z)
  (regs1 : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (k : nat) : Prop :=
  INV_KV B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val /\
  strcasecmp key S_role = 0 /\
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 /\
  (forall a, b10_far v pos a -> rdW Wc memc a = rdW Wc memc0 a) /\
  (forall i, 0 <= i < 8 -> rdW Wc memc (pf_SH v pos + 80 + i) = Some 0) /\
  (forall i, (i < k)%nat -> rdW Wc memc (pf_F v pos + PF_O_LOW + Z.of_nat i) = Some (lower (nth i val 0))) /\
  (k <= length val)%nat /\ (k <= 63)%nat /\
  (forall r, In r B10_KZ -> getr regs1 (Z_to_bv 5 r) = getr rX0 (Z_to_bv 5 r)).

(* every byte present at ROLE is present: off b10_D it is the same byte, low's bytes are the frame's, low's shadow
   cells hold 0 *)
Lemma b10_grow : forall v pos lyc Sc Wc memc0 memc mdc,
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 ->
  lyc = p_ly v ->
  (forall a, b10_far v pos a -> rdW Wc memc a = rdW Wc memc0 a) ->
  (forall i, 0 <= i < 8 -> rdW Wc memc (pf_SH v pos + 80 + i) = Some 0) ->
  forall a, rdW Wc memc0 a <> None -> rdW Wc memc a <> None.
Proof.
intros v pos lyc Sc Wc memc0 memc mdc HJ Hly KM Z0 a Ha.
destruct (b10_frame v pos lyc Sc Wc memc mdc HJ Hly) as (_ & _ & _ & _ & _ & _ & _ & Fp & _ & _).
rewrite (b10_aview_wrap _ memc a). rewrite (b10_aview_wrap _ memc0 a) in Ha.
assert (Ha' : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (a' := a mod 2 ^ 64) in *.
assert (HDd : b10_D v pos a' \/ ~ b10_D v pos a') by (unfold b10_D; lia).
destruct HDd as [[HD|HD]|HD].
- apply (aview_some_of_apresent SEGS). apply Fp. unfold PF_O_LOW in HD. lia.
- replace a' with (pf_SH v pos + 80 + (a' - pf_SH v pos - 80)) by lia. rewrite Z0 by lia. discriminate.
- rewrite KM by (split; [exact Ha' | exact HD]). exact Ha.
Qed.

(* b10_mid survives a step that writes at most low[k] *)
Lemma b10_mid_step : forall n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k
                            regs1' memc' mdc' k',
  b10_mid n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> pf_F v pos + PF_O_LOW + Z.of_nat k ->
     rdW Wc memc' a = rdW Wc memc a) ->
  (k' = k \/ (k' = S k /\
     rdW Wc memc' (pf_F v pos + PF_O_LOW + Z.of_nat k) = Some (lower (nth k val 0)))) ->
  (k' <= length val)%nat -> (k' <= 63)%nat ->
  (forall r, In r B10_KZ -> getr regs1' (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  b10_mid n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1' memc' mdc' k'.
Proof.
intros n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc k
  regs1' memc' mdc' k' (HKV & Hrole & HJ & KM & Z0 & LW & Hkl & Hk63 & HK) HJ' KS Hk' Hk'l Hk'63 HK'.
pose proof HKV as ((_ & HFI & _) & _). pose proof HFI as (HJ0 & Hly & _).
destruct (b10_frame v pos lyc Sc Wc memc mdc HJ Hly) as (_ & _ & F32 & Fapp & _ & F4096 & Fc & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLO : 0 <= pf_F v pos + PF_O_LOW + Z.of_nat k < 2 ^ 64) by (unfold PF_O_LOW; lia).
split; [exact HKV|]. split; [exact Hrole|]. split; [exact HJ'|].
split.
{ intros a Ha. rewrite KS; [exact (KM a Ha)|exact (proj1 Ha)|].
  intros ->. apply (proj2 Ha). left. unfold PF_O_LOW. lia. }
split.
{ intros i Hi. rewrite KS; [exact (Z0 i Hi)| unfold pf_SH, shadow_addr, SHADOW_OFF; lia |].
  replace (pf_SH v pos + 80 + i) with (pf_SH v pos + (80 + i)) by lia.
  replace (pf_F v pos + PF_O_LOW + Z.of_nat k) with (pf_F v pos + (PF_O_LOW + Z.of_nat k)) by lia.
  apply not_eq_sym.
  apply (b10_lowsh_ne v pos (PF_O_LOW + Z.of_nat k) (80 + i) F32 Fapp Fc); unfold PF_O_LOW; lia. }
split.
{ intros i Hi. destruct Hk' as [-> | (-> & HW)].
  - rewrite KS; [exact (LW i Hi) | unfold PF_O_LOW; lia |]. intros E'. lia.
  - destruct (Nat.eq_dec i k) as [->|Hne]; [exact HW|].
    rewrite KS; [apply LW; lia | unfold PF_O_LOW; lia |]. intros E'. lia. }
split; [exact Hk'l|]. split; [exact Hk'63|].
intros r Hr; rewrite HK' by exact Hr; exact (HK r Hr).
Qed.

(* INTENT (pf_pieces.v INV_INTENT) at the end of the fold: low[0 .. k) folded and low[k] = 0 with
   k = |r_low val 0 64|, s7 = low (0x888c8) *)
Lemma b10_intent : forall n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc,
  b10_mid n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc
    (length (r_low val 0 64)) ->
  rdW Wc memc (pf_F v pos + PF_O_LOW + Z.of_nat (length (r_low val 0 64))) = Some 0 ->
  getr regs1 (Z_to_bv 5 23) = w64 (pf_F v pos + PF_O_LOW) ->
  INV_INTENT B n v pos lyc Sc Wc regs1 memc mdc cf nm o ln d gi vp val.
Proof.
intros n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc
  (HKV & Hrole & HJ & KM & Z0 & LW & Hkl & Hk63 & HK) HN R23.
pose proof (b10_geo n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val HKV)
  as (Gsp & Gsp47 & Gs1 & Gs32 & _).
destruct HKV as ((HCX & HFI & HOBJ & HSL & HFSH) & HMID & HST & HKVS & HSLB & HRG).
pose proof HFI as (HJ0 & Hly & HSc & Hperm & HSV & HFL & HFRM & HTF & HC8 & HRG0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_reac_segconf_parse_file = 12832) by reflexivity. rewrite HSTK in Gsp.
destruct (b10_frame v pos lyc Sc Wc memc0 mdc0 HJ0 Hly)
  as (Hin & HAR0 & F32 & Fapp & Foff & F4096 & Fc & Fp0 & Fsh0 & HBLK).
destruct (b10_frame v pos lyc Sc Wc memc mdc HJ Hly) as (_ & _ & _ & _ & _ & _ & _ & Fp & _ & _).
pose proof (b10_grow v pos lyc Sc Wc memc0 memc mdc HJ Hly KM Z0) as G.
pose proof (b10_heap_far v pos lyc Sc F32 Fapp Foff Fc HBLK) as HH.
assert (FS : forall a, alloc_ceiling <= a < 2 ^ 64 -> b10_far v pos a).
{ intros a Ha. split; [lia|]. apply (b10_nD v pos a F32 Fapp Foff Fc). right; right; right. lia. }
assert (FIN : forall a, pf_F v pos <= a < pf_F v pos + 2048 ->
  (a < pf_F v pos + PF_O_LOW \/ pf_F v pos + PF_O_LOW + 64 <= a) -> b10_far v pos a).
{ intros a Ha Ho. split; [lia|]. apply (b10_nD_in v pos a F32 Fapp Fc). left. split; [exact Ha | exact Ho]. }
assert (HSHr : 0 <= pf_SH v pos /\ pf_SH v pos + 256 < 2 ^ 64).
{ unfold pf_SH, shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)). lia. }
assert (SLK : forall off, 0 <= off <= 0xd8 -> forall kk, 0 <= kk < 8 -> b10_far v pos (pf_s1 v + off + kk)).
{ intros off Hoff kk Hkk. apply FS. lia. }
destruct HKVS as (Hsplit & Hks & Hkb & Hvs & Hvb).
pose proof Hvs as ((HVZ & NZ) & _).
assert (VR : forall i, (i < length val)%nat -> 0 <= nth i val 0 < 256).
{ intros i Hi. pose proof (HVZ i ltac:(rewrite length_app; cbn [length]; lia)) as E.
  rewrite app_nth1 in E by exact Hi. destruct (aview_byte SEGS _ _ _ _ E) as (_ & _ & _ & Hr). exact Hr. }
pose proof (b10_r_low64_len val NZ) as RLL.
unfold INV_INTENT.
set (k := length (r_low val 0 64)) in *.
assert (Hk : length (r_low val 0 64) = k) by reflexivity. clearbody k.
split.
{ (* pf_base, low in scope *)
  split; [exact HCX|]. split.
  { (* pf_fi *)
    split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact Hperm|].
    split.
    { intros j r Hj. pose proof (HSV j r Hj) as Hw.
      assert (Hj13 : (j < length PF_SAVED)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
      cbn [length PF_SAVED] in Hj13.
      apply (b10t_word _ _ (b10_far v pos) KM _ _ Hw). intros kk Hkk. apply FS. unfold pf_sp0 in *. lia. }
    split.
    { apply (b10t_word _ _ (b10_far v pos) KM _ _ HFL). intros kk Hkk. apply FIN;
        change (fs_frame_bytes 5) with 2048; unfold PF_O_LOW; lia. }
    split; [exact HFRM|]. split; [exact HTF|].
    split.
    { unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
      apply (b10t_word _ _ (b10_far v pos) KM _ _ (HC8 ov Hov)). intros kk Hkk.
      cbn [In] in Hov. destruct Hov as [<-|[]]. cbn [fst]. apply SLK; lia. }
    apply (b10_rg_kept rX0 regs1 _ HRG0 HK).
    repeat (apply Forall_cons; [b10_inZ|]); apply Forall_nil. }
  split; [exact (b10_obj_keep v pos lyc Sc _ _ F32 Fapp Foff Fc HBLK KM G HOBJ)|].
  split.
  { unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
    apply (b10t_word _ _ (b10_far v pos) KM _ _ (HSL ov Hov)). intros kk Hkk.
    assert (Hov8 : 0 <= fst ov <= 0xd8).
    { unfold PF_SL in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<-|Hov]; [cbn [fst]; lia|]). destruct Hov. }
    apply SLK; lia. }
  intros i Hi. rewrite b10_shb_low.
  destruct (Z.leb_spec 80 i); destruct (Z.ltb_spec i 88); cbn [andb].
  - replace (pf_SH v pos + i) with (pf_SH v pos + 80 + (i - 80)) by lia. apply Z0. lia.
  - rewrite KM; [exact (HFSH i Hi)|]. split; [lia|]. apply (b10_nD_in v pos _ F32 Fapp Fc). right.
    exists i. split; [reflexivity|]. lia.
  - rewrite KM; [exact (HFSH i Hi)|]. split; [lia|]. apply (b10_nD_in v pos _ F32 Fapp Fc). right.
    exists i. split; [reflexivity|]. lia.
  - rewrite KM; [exact (HFSH i Hi)|]. split; [lia|]. apply (b10_nD_in v pos _ F32 Fapp Fc). right.
    exists i. split; [reflexivity|]. lia. }
split; [exact HMID|].
split.
{ (* the spine's state: c's bytes (heap), cur_name's bytes (the frame, below low), slot 0xc0 *)
  destruct HST as (HRC & HCO & HNM & HCNT & HC0).
  split; [|split; [exact HCO | split; [|split; [exact HCNT|]]]].
  - destruct HRC as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
    pose proof HOBJ as (_ & _ & _ & _ & Hch & _). destruct Henc as (Hlen & _).
    apply (b10t_bytes _ _ (b10_far v pos) KM _ _ Hbs). intros i Hi.
    destruct (HH _ _ Hch (p_c v + Z.of_nat i) ltac:(lia)) as [Hf _]. exact Hf.
  - destruct HNM as (f & Hf & Henc16). exists f. split; [|exact Henc16].
    destruct Henc16 as (Hl16 & _).
    apply (b10t_bytes _ _ (b10_far v pos) KM _ _ Hf). intros i Hi. apply FIN; unfold PF_O_CN, PF_O_LOW; lia.
  - apply (b10t_word _ _ (b10_far v pos) KM _ _ HC0). intros kk Hkk. apply SLK; lia. }
split.
{ apply (b10t_str _ _ (b10_far v pos) KM G _ _ Hvs). intros i Hi. unfold pf_inb, PF_O_BUF in Hvb.
  apply FIN; unfold PF_O_LOW; lia. }
split; [exact Hvb|].
split.
{ (* low's 64 bytes: the fold, its NUL, then the bytes the frame held *)
  destruct (b10_bytes_of (rdW Wc memc) (pf_F v pos + PF_O_LOW) 64) as (LB & HLB & HB).
  { intros i Hi. destruct (Nat.lt_ge_cases i k) as [Hlt|Hge].
    - exists (lower (nth i val 0)). split; [exact (LW i Hlt)|]. apply b10_lower_range, VR. lia.
    - destruct (Nat.eq_dec i k) as [->|Hne]; [exists 0; split; [exact HN | lia]|].
      destruct (rdW Wc memc (pf_F v pos + PF_O_LOW + Z.of_nat i)) as [z|] eqn:E.
      + exists z. split; [reflexivity|]. destruct (aview_byte SEGS _ _ _ _ E) as (_ & _ & _ & Hr). exact Hr.
      + exfalso. apply (aview_some_of_apresent SEGS _ _ _
          (Fp (pf_F v pos + PF_O_LOW + Z.of_nat i) ltac:(unfold PF_O_LOW; lia)) E). }
  exists LB. split; [exact HLB|]. split; [exact HB|].
  apply nth_ext with (d := 0) (d' := 0).
  { rewrite length_firstn, length_app. unfold seg_spec.zs. rewrite length_map, HLB. cbn [length]. lia. }
  intros i Hi. rewrite length_firstn in Hi. unfold seg_spec.zs in *. rewrite length_map, HLB in Hi.
  rewrite nth_firstn. destruct (Nat.ltb_spec i (S k)) as [_|]; [|lia].
  rewrite (nth_indep _ 0 (bv_unsigned ZB0)) by (rewrite length_map; lia). rewrite map_nth.
  pose proof (HB i ltac:(lia)) as Ei.
  destruct (Nat.lt_ge_cases i k) as [Hlt|Hge].
  - rewrite app_nth1 by lia. rewrite (LW i Hlt) in Ei. injection Ei as Ei. rewrite <- Ei.
    rewrite (b10_r_low64 val NZ).
    rewrite (nth_indep (map lower (firstn 63 val)) 0 (lower 0)) by (rewrite length_map, length_firstn; lia).
    rewrite map_nth, nth_firstn. destruct (Nat.ltb_spec i 63); [reflexivity | lia].
  - assert (i = k) as -> by lia. rewrite app_nth2 by lia.
    replace (k - length (r_low val 0 64))%nat with 0%nat by lia. cbn [nth].
    rewrite HN in Ei. injection Ei as Ei. exact (eq_sym Ei). }
split.
{ unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
  apply (b10t_word _ _ (b10_far v pos) KM _ _ (HSLB ov Hov)). intros kk Hkk.
  cbn [In] in Hov. destruct Hov as [<-|[]]. cbn [fst]. apply SLK; lia. }
unfold pf_rg. rewrite !Forall_app. split; [|split].
- apply (b10_rg_kept rX0 regs1 _ (proj1 (proj1 (Forall_app _ _ _) HRG)) HK).
  unfold PF_RL. repeat (apply Forall_cons; [b10_inZ|]); apply Forall_nil.
- apply (b10_rg_kept rX0 regs1 _ (proj2 (proj1 (Forall_app _ _ _) HRG)) HK).
  unfold PF_RM. repeat (apply Forall_cons; [b10_inZ|]); apply Forall_nil.
- apply Forall_cons; [exact R23 | apply Forall_nil].
Qed.
End e.
End f.
End d.
