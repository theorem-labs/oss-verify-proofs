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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 530 of its 580 lines of code are new or changed and 403 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a11b_m1.v, with its module names changed; 325 of its 418 lines of code are new or changed and 487 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the STORE exit of segment A12 of reac_segconf_parse_file's
   walk (the ignore key, reac_segconf.c:271-280; lib/A/Prog/pf_pieces.v S_A12), as one closed lemma:
     [a12_store_blk] from 0x888bc (BASE + A12_ST) with s7 = b and the mid-walk invariant a12_I of
     lib/A/Prog/pf_a12_k.v, the walk reaches the cut PROV2 (0x889f0), whose continuation HA_PROV2 ends it.
   The code (the unit's internal record, commit dfb49d6ad789,
   path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s,
   0x888bc .. 0x88908, 20 instructions):
     check #33 (store4 at cur + 0x18; slow block 0x88af4, error arm 0x88d60), `sw s7, 0x18(s4)` (cur->ignore = b),
     check #34 (store4 at cur + 0x1c; slow block 0x88b04, error arm 0x88d64) with `ld s3, 0x98(s1)` (s3 = SH + 8),
     `sw` of 1 at 0x1c(s4) (cur->ignore_set = 1), a0 = s4 + 0x100 (&cur->ignore_file), a1 = 0x60,
     a2 = "%s" (auipc/addi, 0x21340 = listing object 35), a3 = ld 0x58(s1) (c + RC_READING), `j 0x889f0`.
   The walk: pf_a12_k.v's seed a12_seed_I at A12_ST (cur's ignore / ignore_set words writable); one token run to
   PF_PROV2 (both checks decided from the SH entry a12st_SH on s4 = atom 20; no obligation, no token left); the
   run writes only [cur + 24, cur + 32) (frame_of), whose two chunks give the stored words (a12st_w4_chunk), so
   pf_a12_store.v's a12_rconf_store gives c's new state pf_prov_mid (PIgn b) cf gi; pf_base is carried across
   the write by this file's own keep lemmas (a12st_kit .. a12st_move: every byte pf_base reads lies outside the
   block c - the stack above alloc_ceiling, the class-5 frame (sep_block_frame), the shadow band (the block is
   in the application range), the image range (SegPaLib.v's blk_off_imgP), the text (reader_pre's sa_disj));
   the image facts (literals, catalogue, read-only view, stack-protector cells) are image-range bytes, so
   neither VRO nor SSPX is needed.
   a12st_hull_rng is lib/A/Prog/pf_a11b_m1.v's pfm_hull_rng (commit 921b452016cc), copied.

   Section hypothesis (one):
     OBJ  SegObj.seg_val_objs (the auipc / addi pair's object atom A_OBJ 35 is seg_litA_rc F_s, the "%s" that
          INV_PROV2 names in a2); forced by a12st_lit only.
   Part of segment A12's proof (the store exit), by the G3 walk owner, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
pf_pieces pf_a5_k pf_a12_pure pf_a12_k pf_a12_keep pf_a12_store.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the int value of a bool that a store of parse_bool's answer writes (seg_spec.v) *)
#[local] Notation b2z := seg_spec.b2z.

(** The SH list of the store block: cur's ignore / ignore_set words on s4 = atom 20 (checks #33, #34). *)
Definition a12st_SH : list shent := [mkSHE 20 seg_spec.RS_IGNORE (seg_spec.RS_IGNORE_SET + 4)].

(* membership of a register in a list of bv literals: equal bit vectors by their values (the literal's
   well-formedness proof and Z_to_bv's differ) *)
Local Ltac a12st_in := solve [cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]].

(** ** Readers: what a write outside an object keeps of it *)
(* the text: its bytes and NUL apart from the block c (reader_pre's sa_disj), its slack mapped (kept presence) *)
Lemma a12st_keep_str : forall (rd rd' : reader) t s c,
  sa_str rd t s -> 0 <= t -> t + Z.of_nat (length s) + 1 <= 2 ^ 63 ->
  sa_disj t (seg_spec.cstr_span t s) c seg_spec.SEG_C_SIZE ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + seg_spec.SEG_C_SIZE) -> rd' a = rd a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None) ->
  sa_str rd' t s.
Proof.
intros rd rd' t s c ((Hz & Hn) & Ht) H0 H1 HD HK HV.
unfold sa_disj, seg_spec.cstr_span in HD.
pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as M.
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite HK; [exact (Hz i Hi) | lia | lia].
- intros x Hx. pose proof (Z.mod_pos_bound (t + Z.of_nat (length s)) 8 ltac:(lia)) as M2.
  apply HV; [lia | exact (Ht x Hx)].
Qed.

(* lib/A/Prog/pf_a11b_m1.v's pfm_hull_rng (commit 921b452016cc), copied: the shadow hull of a range
   below 2 ^ 63 lies in [0, 2 ^ 64) *)
Lemma a12st_hull_rng : forall q n s, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 64.
Proof.
intros q n s H0 H1 Hn Hs. unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.

(* an addressable range: it reads only shadow bytes (kept) and the presence of its hull (kept) *)
Lemma a12st_keep_addr : forall (rd rd' : reader) q n,
  sa_addr rd q n ->
  (forall a, kLowMemEnd <= a < kHighShadowEnd -> rd' a = rd a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None) ->
  sa_addr rd' q n.
Proof.
intros rd rd' q n (Hq & Hn & Hm & Hra & Hhv) K HV.
assert (Hq47 : q + n <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm; lia).
refine (conj Hq (conj Hn (conj Hm (conj _ _)))).
- intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  assert (E : shadow_of_addr SHADOW_OFF x = shadow_addr x) by reflexivity.
  rewrite E in Hs |- *. rewrite K; [exact Hs|].
  pose proof (a12_sh_rng x ltac:(lia)). unfold kLowMemEnd, kHighShadowEnd. lia.
- intros Hn0 s Hs. apply HV; [exact (a12st_hull_rng q n s Hq Hn Hn0 Hs) | exact (Hhv Hn0 s Hs)].
Qed.

(* the registers of a list whose values are kept *)
Lemma a12st_rg_kept : forall (r1 r2 : bvmap 5 word) (l : list (bv 5)) L,
  (forall r, In r l -> getr r2 r = getr r1 r) -> Forall (fun rv => In (Z_to_bv 5 (fst rv)) l) L ->
  pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 l L HK HL H. unfold pf_rg in *. rewrite Forall_forall in H, HL |- *. intros rv Hin.
rewrite (HK _ (HL rv Hin)). exact (H rv Hin).
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** A 4-byte value chunk of a region, as the reader shows its bytes (the form pf_a12_store.v's a12_w4 takes). *)
Lemma a12st_w4_chunk : forall E1 (H : word -> bool) mem base off (e : sv) z,
  YP09.chunk_ok SEGS E1 (mrestrict H mem) base (YP09.mkChunk off (CVal 4 e)) ->
  sv_denot E1 e = Z_to_bv 64 z -> 0 <= z < 2 ^ 32 ->
  a12_w4 (aview SEGS H mem) (base + off) z.
Proof.
intros E1 H mem base off e z HC He Hz k Hk.
destruct (HC (Z.of_nat k) ltac:(cbn; lia)) as (bt & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm.
injection Hb as <-.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold byte_of_word. rewrite He. rewrite Z_to_bv_unsigned. rewrite unsigned_lit_small by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte.
change (8 * Z.of_nat 4) with 32.
rewrite (Z.mod_small z (2 ^ 32)) by exact Hz. reflexivity.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the listing's object atoms over the walk's abstract instance (SegObj.v): a2's "%s" is object 35 *)
Hypothesis OBJ : seg_val_objs (PI := PI).

(* the literal a2 holds at PROV2: listing object 35 is "%s", F_s's text (SegInstA.v's map; pf_a7_u.v's a7u_lit) *)
Lemma a12st_lit : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 35) = w64 (seg_litA_rc F_s).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 35) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section s.
Context {fx : YK11.FPState}.
Let RUNTO := paj_run_to B LAWS.

(** *** A register after the run, from the executor's term for it *)
Lemma a12st_reg : forall E1 ss1 ms1 (H : word -> bool) (r : bv 5) k c x,
  st_ok_pi SEGS VAL E1 ss1 (restrict H ms1) -> sr_get (ss_regs ss1) r = SOff k c ->
  ew E1 k = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> getr (ms_regs ms1) r = Z_to_bv 64 (x + c).
Proof.
intros E1 ss1 ms1 H r k c x HS Hr Hk Hx.
rewrite (st_ok_pi_restrict_reg H E1 ss1 ms1 r HS), Hr. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by lia.
reflexivity.
Qed.

Lemma a12st_reg_lit : forall E1 ss1 ms1 (H : word -> bool) (r : bv 5) z,
  st_ok_pi SEGS VAL E1 ss1 (restrict H ms1) -> sr_get (ss_regs ss1) r = SLit z ->
  getr (ms_regs ms1) r = Z_to_bv 64 z.
Proof.
intros E1 ss1 ms1 H r z HS Hr. rewrite (st_ok_pi_restrict_reg H E1 ss1 ms1 r HS), Hr. reflexivity.
Qed.

(** *** What a write inside the block c keeps: every byte outside c, so the stack above alloc_ceiling, the
    class-5 frame, the shadow band and the image range *)
Lemma a12st_kit : forall v pos lyc Sc (Wc : world SEGS) memc mdc memc',
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> rdW Wc memc' a = rdW Wc memc a) /\
  (forall a, kLowMemEnd <= a < kHighShadowEnd -> rdW Wc memc' a = rdW Wc memc a) /\
  (forall a, 0x10000 <= a < kImgEnd -> rdW Wc memc' a = rdW Wc memc a).
Proof.
intros v pos lyc Sc Wc memc mdc memc' G HAR Hin Hly (bq & mq & Hbq & H1 & H2) HK.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bq mq HAR Hbq) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos mq (proj1 Hm)) as [_ Hreq].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bq mq 5 pos HAR Hbq Hin) as Hd.
pose proof (blk_off_imgP B lyc Sc Wc memc mdc bq mq HAR Hbq) as Hoff.
subst lyc. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
unfold off_img in Hoff.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold seg_spec.SEG_C_SIZE in *.
split; [|split; [|split]]; intros a Ha; apply HK; unfold kImgEnd in *; lia.
Qed.

(** *** The image facts of pf_obj: image-range bytes *)
Lemma a12st_keep_lit : forall (Wc : world SEGS) memc memc' a s,
  (forall x, 0x10000 <= x < kImgEnd -> rdW Wc memc' x = rdW Wc memc x) ->
  sa_lit SEGS B (rdW Wc memc) a s -> sa_lit SEGS B (rdW Wc memc') a s.
Proof.
intros Wc memc memc' a s K4 (Ha & ((Hz & Hn) & Ht) & Hp & Hr & Hi).
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn] | exact (sa_tail_of_romtail SEGS _ _ _ Hr)].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Himg & _ & _).
pose proof (pa_img_range _ Himg) as Hrg.
rewrite K4; [exact (Hz i Hi') | exact Hrg].
Qed.

Lemma a12st_keep_cat : forall (Wc : world SEGS) memc memc',
  (forall x, 0x10000 <= x < kImgEnd -> rdW Wc memc' x = rdW Wc memc x) ->
  sa_cat SEGS B (rdW Wc memc) catA -> sa_cat SEGS B (rdW Wc memc') catA.
Proof.
intros Wc memc memc' K4 (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp.
split; [|exact (a12st_keep_lit Wc memc memc' tp _ K4 Hl)].
rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact Htp|].
intros k Hk. assert (Hn' : Z.of_nat i < 11) by (unfold pin_spec.CAT_N in Hn; lia).
apply K4. refine (pa_img_range _ (proj1 (Hi (pin_spec.row_addr catA i + k) _))).
unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.

Lemma a12st_keep_rod : forall (Wc : world SEGS) memc memc',
  (forall x, 0x10000 <= x < kImgEnd -> rdW Wc memc' x = rdW Wc memc x) ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) -> arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc').
Proof.
intros Wc memc memc' K4 HR a Hro Ho He.
assert (Hlow : 0x10000 <= a < kImgEnd).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  - assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
    exact (pa_img_range _ Hi).
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia. }
rewrite (K4 a Hlow). exact (HR a Hro Ho He).
Qed.

Lemma a12st_keep_ssp : forall (Wc : world SEGS) memc memc',
  (forall x, 0x10000 <= x < kImgEnd -> rdW Wc memc' x = rdW Wc memc x) ->
  sa_ssp (rdW Wc memc) gotwA guardA -> sa_ssp (rdW Wc memc') gotwA guardA.
Proof.
intros Wc memc memc' K4 (S1 & g & S2).
assert (E : gotwA = 0xa36d8 /\ guardA = 0x5ff078) by (split; reflexivity). destruct E as [E1 E2].
assert (KW : forall a, 0x10000 <= a -> a + 8 <= kImgEnd -> rdword (rdW Wc memc') a = rdword (rdW Wc memc) a).
{ intros a Ha1 Ha2. apply rdword_ext. intros k Hk. apply K4. lia. }
split; [rewrite KW; [exact S1 | lia | unfold kImgEnd; lia]|].
exists g. rewrite KW; [exact S2 | lia | unfold kImgEnd; lia].
Qed.

(** *** pf_base after a step that writes only inside the block c (same world, same layout and state) *)
Lemma a12st_move : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc sc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  pf_rg rX' (a5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' HB HJ' HK HV HRG.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct HFI as (_ & Hly' & HFS & HP0 & HSV & HFL & HFRM & _).
pose proof HOBJ as (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
destruct (a12st_kit v pos lyc Sc Wc memc mdc memc' G HAR Hin Hly C2 HK) as (K1 & K2 & K3 & K4).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HPF) & _).
destruct HPF as (HRP & _).
pose proof HRP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDJ & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
rewrite SPF in G1.
split; [exact HCX|].
split.
{ refine (conj HJ' (conj Hly' (conj HFS (conj HP0 (conj _ (conj _ (conj HFRM HRG))))))).
  - intros j r Hj.
    assert (Hj13 : (j < 13)%nat)
      by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
    rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact (HSV j r Hj)|].
    intros k Hk. apply K1. lia.
  - rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact HFL|].
    intros k Hk. apply K2. change (fs_frame_bytes 5) with 2048. lia. }
split.
{ pose proof T2 as (Ht0 & Ht1 & _). unfold pf_len in Ht1.
  refine (conj _ (conj _ (conj T3 (conj _ (conj C2 (conj _ (conj _ (conj _ _)))))))).
  - exact (a12st_keep_str _ _ _ _ _ T1 Ht0 ltac:(lia) HDJ HK HV).
  - exact (a12st_keep_addr _ _ _ _ T2 K3 HV).
  - exact (a12st_keep_addr _ _ _ _ C1 K3 HV).
  - exact (a12st_keep_cat Wc memc memc' K4 CA).
  - intros x Hx. exact (a12st_keep_lit Wc memc memc' _ _ K4 (LI x Hx)).
  - exact (a12st_keep_rod Wc memc memc' K4 RO).
  - exact (a12st_keep_ssp Wc memc memc' K4 SS). }
split.
{ unfold pf_sl in HSL |- *. rewrite Forall_forall in HSL |- *. intros [off x] Hov.
  specialize (HSL _ Hov). cbn [fst snd] in *.
  assert (Hoff : 0x20 <= off <= 0xb8).
  { unfold PF_SL in Hov. cbn [In] in Hov.
    repeat (let Hq := fresh "Hq" in destruct Hov as [Hq | Hov]; [injection Hq as <- _; lia |]). destruct Hov. }
  rewrite (rdword_ext (rdW Wc memc) (rdW Wc memc')); [exact HSL|].
  intros k Hk. apply K1. lia. }
{ intros i Hi. rewrite K3; [exact (HFSH i Hi) | lia]. }
Qed.

(** *** The store block: 0x888bc .. 0x88908, then PROV2 *)
Lemma a12_store_blk : forall (b : bool) n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3,
  a12_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  getr rX 23 = w64 (b2z b) ->
  HA_PROV2 B n ->
  SRr SEGS Wc (mkCfg (mkst rX (Z_to_bv 64 (BASE + A12_ST)) memc (seg_rom SEGS)) mdc)
    (pf_postm B v (pf_prov_fin (PIgn b) cf gi, Some gi, nm) o ln).
Proof.
intros b n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 HI H23 HPROV2.
pose proof HI as (HB & HMID & HST & _ & _ & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof HB as (HCX & (HJ & _) & HOBJ & _ & _).
pose proof HOBJ as (_ & _ & _ & HCA & HCH & _).
pose proof HST as (HRC & HOKcur & HNM & HCNT).
pose proof HMID as (Ho & _ & _).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof STK_values as (_ & _ & _ & SPF & _).
assert (Hgl : (gi < length (rc_seg cf))%nat) by exact HOKcur.
assert (Hgi32 : (gi < 32)%nat) by (destruct HRC as (bs & _ & (_ & Hn32 & _)); lia).
(* the block that holds c *)
pose proof HCH as (bq & mq & Hbq & Hq1 & Hq2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bq mq HAR Hbq) as (_ & Hq4096 & Hqceil & Hqapp & _ & _ & Hqm).
pose proof (req_size_pos mq (proj1 Hqm)) as [_ Hreq].
unfold seg_spec.SEG_C_SIZE in Hq2.
(* the registers of the cut *)
pose proof (a5_rg_get rX _ 18 0x23 HRG ltac:(cbn [PF_RM app In]; tauto)) as R18.
pose proof (a5_rg_get rX _ 24 (p_c v) HRG ltac:(cbn [PF_RM app In]; tauto)) as R24.
pose proof (a5_rg_get rX _ 27 (pf_SH v pos) HRG ltac:(cbn [PF_RM app In]; tauto)) as R27.
pose proof (a5_rg_get rX _ 21 (p_t v + Z.of_nat (pf_next (p_s v) o)) HRG ltac:(cbn [PF_RM app In]; tauto)) as R21.
pose proof (a5_rg_get rX _ 26 (ln + 1) HRG ltac:(cbn [PF_RM app In]; tauto)) as R26.
pose proof (a5_rg_get rX _ 20 (seg_spec.rseg_addr (p_c v) gi) HRG ltac:(cbn [PF_RM app In]; tauto)) as R20.
pose proof (a5_rg_get rX _ 22 SHADOW_OFF HFI ltac:(cbn [a5_FI In]; tauto)) as R22.
assert (R20' : getr rX 20 = w64 (p_c v + 356 * Z.of_nat gi)) by exact R20.
(* the environment of the seed *)
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (a12_E rX v pos val) k = getr rX r)
  by (intros k r Hk; unfold a12_E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HEI : img_env VAL A_LIM (a12_E rX v pos val)) by (unfold a12_E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX (a12_extra v pos val)) (a12_E rX v pos val)).
{ unfold a12_E. split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
assert (U20 : bv_unsigned (ew (a12_E rX v pos val) 20) = p_c v + 356 * Z.of_nat gi).
{ rewrite (ER 20%nat 20%bv eq_refl), R20'. unfold w64. apply unsigned_lit_small. lia. }
assert (U20s : U (a12_E rX v pos val) (SOff 20 0) = p_c v + 356 * Z.of_nat gi).
{ apply U_atom; [rewrite (ER 20%nat 20%bv eq_refl); exact R20' | lia]. }
assert (U22 : U (a12_E rX v pos val) a12_Bx = SHADOW_OFF).
{ unfold a12_Bx. apply U_atom; [rewrite (ER 22%nat 22%bv eq_refl); exact R22 | unfold SHADOW_OFF; lia]. }
(* checks #33 and #34: cur's 8 bytes [cur + 24, cur + 32) are addressable heap bytes *)
assert (SHOK : sh_ok SEGS a12_Bx a12st_SH (a12_E rX v pos val) (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, a12st_SH. apply Forall_cons; [|apply Forall_nil].
  apply (a12_shent (a12_E rX v pos val) Wc memc 20%nat (p_c v + 356 * Z.of_nat gi) seg_spec.RS_IGNORE
    (seg_spec.RS_IGNORE_SET + 4) U22 U20s ltac:(unfold seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET; lia)).
  - pose proof HCA as (_ & _ & _ & HRA & _).
    apply (range_addressable_sub _ _ (p_c v) seg_spec.SEG_C_SIZE); [exact HRA | |];
      unfold seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET, seg_spec.SEG_C_SIZE; lia.
  - apply (in_app_sub bq (req_size mq)); [exact Hqapp | ..];
      unfold seg_spec.RS_IGNORE, seg_spec.RS_IGNORE_SET; lia. }
(* the seed at 0x888bc, cur's two words writable *)
pose proof (a12_seed_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 A12_ST HI) as HS.
(* 0x888bc .. 0x88908: the two checks, the two stores, s3 reloaded, a0 .. a3, j PROV2 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_PROV2.
{ (* the run writes only cur's two words, inside the block c and inside parse_file's footprint *)
  lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 20%nat) (b := p_c v + 356 * Z.of_nat gi);
    [reflexivity | exact U20 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte. right. left. split.
  - unfold inFP. exists (p_c v, p_c v + seg_spec.RC_N + 4). unfold seg_spec.RC_PARSE_W.
    split; [left; reflexivity|]. cbn [fst snd]. unfold seg_spec.RC_N. lia.
  - exists bq, mq. split; [exact Hbq | lia]. }
(* at PROV2 *)
try (set (mdv := with_vm_backing _ _ _) in *; clearbody mdv).
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
  assert (HAx : env_agree 32 (Ereg rX (a12_extra v pos val)) E1) by (env_agree_chain HA0);
  assert (HEI1 : img_env VAL A_LIM E1) by assumption;
  set (E2 := E1) in HS, HAx, HEI1; clearbody E2
end.
assert (EW : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E2 k = getr rX r).
{ intros k r Hk Hr. rewrite (proj1 HAx k Hk), <- (proj1 HA0 k Hk). apply ER. exact Hr. }
pmkst HS.
(* the memory: every byte off [cur + 24, cur + 32) is the cut's *)
assert (KM : forall a, 0 <= a < 2 ^ 64 ->
  ~ (p_c v + 356 * Z.of_nat gi + 24 <= a < p_c v + 356 * Z.of_nat gi + 32) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := SEGS) _ _ _ _ _
    (fun a => p_c v + 356 * Z.of_nat gi + 24 <= a < p_c v + 356 * Z.of_nat gi + 32) HFr); [|exact Ha | exact Hn].
  intros bb wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbv beta; first [lia | rewrite U20 in Hrr; lia] |]).
  destruct Hin. }
(* the two stored words *)
assert (EW20 : bv_unsigned (ew E2 20) = p_c v + 356 * Z.of_nat gi).
{ rewrite (EW 20%nat 20%bv ltac:(lia) eq_refl), R20'. unfold w64. apply unsigned_lit_small. lia. }
pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS eq_refl) as HR2.
hnf in HR2. destruct HR2 as (_ & _ & _ & HC2).
cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in HC2.
rewrite EW20 in HC2.
pose proof (Forall_inv HC2) as HC28. pose proof (Forall_inv (Forall_inv_tail HC2)) as HC24.
assert (W28 : a12_w4 (rdW Wc (ms_mem ms)) (p_c v + 356 * Z.of_nat gi + 28) 1)
  by exact (a12st_w4_chunk E2 (w_H Wc) (ms_mem ms) _ 28 (SLit 1) 1 HC28 eq_refl ltac:(lia)).
assert (D23 : sv_denot E2 (SOff 23 0) = Z_to_bv 64 (b2z b)).
{ cbn [sv_denot]. rewrite (EW 23%nat 23%bv ltac:(lia) eq_refl), H23. unfold w64.
  rewrite unsigned_lit_small by (destruct b; cbn; lia). rewrite Z.add_0_r. reflexivity. }
assert (W24 : a12_w4 (rdW Wc (ms_mem ms)) (p_c v + 356 * Z.of_nat gi + 24) (b2z b))
  by exact (a12st_w4_chunk E2 (w_H Wc) (ms_mem ms) _ 24 (SOff 23 0) (b2z b) HC24 D23
              ltac:(destruct b; cbn; lia)).
(* every byte outside c is kept; every present byte stays present *)
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply KM; [exact Ha|]. intros Hw. apply Hn. unfold seg_spec.SEG_C_SIZE. lia. }
assert (KV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None).
{ intros a Ha Hp.
  destruct (Z_lt_le_dec a (p_c v + 356 * Z.of_nat gi + 24)) as [L1|L1]; [rewrite KM by lia; exact Hp|].
  destruct (Z_lt_le_dec a (p_c v + 356 * Z.of_nat gi + 28)) as [L2|L2].
  { replace a with (p_c v + 356 * Z.of_nat gi + 24 + Z.of_nat (Z.to_nat (a - (p_c v + 356 * Z.of_nat gi + 24))))
      by lia.
    rewrite (W24 (Z.to_nat (a - (p_c v + 356 * Z.of_nat gi + 24))) ltac:(lia)). discriminate. }
  destruct (Z_lt_le_dec a (p_c v + 356 * Z.of_nat gi + 32)) as [L3|L3].
  { replace a with (p_c v + 356 * Z.of_nat gi + 28 + Z.of_nat (Z.to_nat (a - (p_c v + 356 * Z.of_nat gi + 28))))
      by lia.
    rewrite (W28 (Z.to_nat (a - (p_c v + 356 * Z.of_nat gi + 28))) ltac:(lia)). discriminate. }
  rewrite KM by lia. exact Hp. }
pose proof (a12st_kit v pos lyc Sc Wc memc mdc (ms_mem ms) G HAR Hfin Hly HCH KC) as (_ & K2 & _ & _).
(* the registers at PROV2 *)
pose proof (regs_kept_of_st_ok_pi _ _ _ rX (a12_extra v pos val) [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 26; 27]%bv
  HS HAx ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (HFI' : pf_rg (ms_regs ms) (a5_FI B v)).
{ apply (a12st_rg_kept rX (ms_regs ms) _ _ HK); [|exact HFI].
  unfold a5_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; a12st_in. }
assert (EW27 : ew E2 27 = Z_to_bv 64 (pf_SH v pos)) by (rewrite (EW 27%nat 27%bv ltac:(lia) eq_refl); exact R27).
assert (EW20b : ew E2 20 = Z_to_bv 64 (p_c v + 356 * Z.of_nat gi))
  by (rewrite (EW 20%nat 20%bv ltac:(lia) eq_refl); exact R20').
assert (EW24 : ew E2 24 = Z_to_bv 64 (p_c v)) by (rewrite (EW 24%nat 24%bv ltac:(lia) eq_refl); exact R24).
assert (C19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (pf_SH v pos + 8)).
{ rewrite (a12st_reg _ _ _ _ (Z_to_bv 5 19) 27 8 _ HS ltac:(vm_compute; reflexivity) EW27
    ltac:(unfold kLowMemEnd, kHighShadowEnd in *; lia)). reflexivity. }
assert (C10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_IGNORE_FILE)).
{ rewrite (a12st_reg _ _ _ _ (Z_to_bv 5 10) 20 256 _ HS ltac:(vm_compute; reflexivity) EW20b ltac:(lia)).
  unfold w64, seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_IGNORE_FILE. reflexivity. }
assert (C11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 0x60).
{ rewrite (a12st_reg_lit _ _ _ _ (Z_to_bv 5 11) 96 HS ltac:(vm_compute; reflexivity)). reflexivity. }
assert (C12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (seg_litA_rc F_s)).
{ rewrite (a12st_reg _ _ _ _ (Z_to_bv 5 12) 276 0 _ HS ltac:(vm_compute; reflexivity) (a12st_lit E2 HEI1)
    ltac:(rewrite a12_lit_s; lia)).
  rewrite Z.add_0_r. reflexivity. }
assert (C13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (p_c v + seg_spec.RC_READING)).
{ rewrite (a12st_reg _ _ _ _ (Z_to_bv 5 13) 24 16512 _ HS ltac:(vm_compute; reflexivity) EW24 ltac:(lia)).
  unfold w64, seg_spec.RC_READING. reflexivity. }
(* the cut PROV2 *)
assert (HINV : INV_PROV2 (fx := fx) B n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d b gi).
{ split; [exact (a12st_move v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) mdv HB HJ KC KV HFI')|].
  split; [exact HMID|].
  split.
  - split; [|split; [|split]].
    + apply (a12_rconf_store (rdW Wc memc) (rdW Wc (ms_mem ms)) (p_c v) cf gi b HRC Hgl ltac:(lia));
        [|exact W24 | exact W28].
      intros a Ha Hn. apply KM; [unfold seg_spec.SEG_C_SIZE in Ha; lia | exact Hn].
    + cbn [pf_cur_ok]. unfold pf_prov_mid, r_upd, r_set_segs. cbn [rc_seg]. rewrite a12_len_upd. exact Hgl.
    + destruct HNM as (f & Hf & Hfe). exists f. split; [|exact Hfe].
      pose proof Hfe as (Hlen & _). intros i Hi. rewrite K2 by (unfold PF_O_CN; lia). exact (Hf i Hi).
    + apply (pf_cnt_mono (pf_prov_mid (PIgn b) cf gi) (length (skipn o (p_s v)))); [|exact HCNT].
      exact (Nat.lt_le_incl _ _ (pf_next_skipn_lt (p_s v) o Ho)).
  - unfold pf_rg, PF_RL, PF_RM. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    all: first [assumption | (rewrite HK by a12st_in; assumption)]. }
exact (HPROV2 fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d b gi HINV).
Qed.

End s.
End e.
End f.
End d.
