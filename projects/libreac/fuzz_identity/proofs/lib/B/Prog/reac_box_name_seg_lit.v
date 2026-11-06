(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_stem.v, with its module paths and module names changed; 1047 of its 1087 lines of code are new or changed and 233 lines of the source are left out. *)
(* reac_box_name (fuzz_identity.asan-ubsan 0x82d74, AF_reac_box_name = 0x2600): the segment C9 -> C10 of the
   program walk, 0x832dc (+0x568) .. 0x833e0 (+0x66c). The cut-point states are rbn_C9 / rbn_C10 of
   lib/B/Prog/reac_box_name_inv.v; lib/B/Prog/reac_box_name.v chains rbn_seg_c9_c10 into the walk.
   The span appends to db (s1 + 88, buffer DP = F + 192, cap 48) the literal " (" (object 23, loop 0x832ec ..
   0x83310), sb_dec(db, in, 1) (0x83334), " in / " (object 24, 0x83348 .. 0x8336c), sb_dec(db, out, 1) (0x83390)
   and " out)" (object 25, 0x833a4 .. 0x833c8); each character is read after an instrumented check and pushed by
   sb_ch(db) (0x83308 / 0x83364 / 0x833c0). The counts are literal, so the walk is unrolled: 13 sb_ch calls and
   2 sb_dec calls cut it into 16 runs of the token engine (lit_run_ch / lit_run_dec / lit_run_end), each started
   from a fresh symbolic state (lit_entry, the form of cgif lib/A/AC8b.v tcbb_loopX) and each stopping at the next
   call, whose contract (tsb_ch_spec / tsb_dec_spec) the call lemmas apply (rbn_lit_call_ch / rbn_lit_call_dec).
   The instrumented checks at 0x83318 / 0x83374 / 0x833d0 compare the loop index (slli/srai), not `andi addr, 7`,
   so the token engine's slow-path pattern (lib/Reusable/YCbn.v slow_block) does not apply. The symbolic state
   holds the literal's shadow byte instead (region lit_rS, through the alias of (lit + j) >> 3): at each read it is
   re-derived from the current AR by IdentRo.v ro_read_ok_glob (GM, IV and rbn_img's rbn_glob), and it is 0 or
   lies in (len, 8), so every check passes (lit_shadow). The literal's bytes are rbn_img's at the entry memory,
   carried to the current memory by the journal's image clause (rbn_fixed, lit_chars). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YI08 YI09 YI0s YI0t YI0m YI0n YP0g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBProgSig IdentBCJ IdentBFrame YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import reac_box_name_sbm reac_box_name_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c sb_dec_c box_name_lemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Section walk.
Context {RO : ro_below_ofl SEGS (@pa_relro_lo _ identb_listing PI) (@pa_relro_hi _ identb_listing PI)}.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis PSIG : identb_prog_sig_ok.
Hypothesis HSC : tsb_ch_spec B.
Hypothesis HSB : tsb_dec_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ---- Memory facts carried to a memory that kept the bytes of their footprint ---- *)
Lemma rlc_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) q l,
  (forall a, q <= a < q + Z.of_nat (length l) -> aview SEGS H m' a = aview SEGS H m a) ->
  garr8 SEGS (mrestrict H m) q l -> garr8 SEGS (mrestrict H m') q l.
Proof.
intros H m m' q l K Gq. apply (garr8_frame SEGS _ _ q l Gq). intros a Ha. apply (mbyte_of_aview SEGS). exact (K a Ha).
Qed.
Lemma rlc_val_mem_kept : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v K Hv. eapply val_mem_kept; [|exact Hv]. intros k Hk. apply K. lia.
Qed.
Lemma rlc_rdword_kept : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, a <= x < a + 8 -> aview SEGS H m' x = aview SEGS H m x) ->
  rdword (aview SEGS H m') a = rdword (aview SEGS H m) a.
Proof. intros H m m' a K. apply rdword_ext. intros k Hk. apply K. lia. Qed.
(* ---- Where things lie in a cut state ---- *)
Lemma rlc_lay : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  AR SEGS B lyc Sc (x_W c) memc mdc /\
  x_s1 c mod 32 = 0 /\ x_sp0 c - 351 <= x_s1 c <= x_sp0 c - 320 /\ x_sp0 c mod 16 = 0 /\
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + (336 + 2 * ESTACK) <= x_sp0 c /\ x_sp0 c <= ly_stk_hi lyc /\
  ly_stk_hi lyc <= 2 ^ 47 /\
  In (3, x_fpos c) (frames Sc) /\ frame_addr lyc 3 (x_fpos c) = x_F c /\
  4096 <= x_F c /\ x_F c + 512 <= alloc_ceiling /\ x_F c mod 32 = 0 /\ in_app (x_F c) 512 /\
  x_FS c = SHADOW_OFF + x_F c / 8 /\ x_F c = 8 * (x_F c / 8) /\
  (forall a, x_sp0 c - (336 + 2 * ESTACK) <= a < x_sp0 c -> apresent (w_H (x_W c)) memc a) /\
  (forall cid pos, frame_addr lyc cid pos = frame_addr (x_ly c) cid pos) /\
  (forall cid pos, In (cid, pos) (frames (x_S c)) -> In (cid, pos) (frames Sc)).
Proof.
intros c lyc Sc memc mdc regs (Hpre & HJ & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EF : forall cid pos, frame_addr lyc cid pos = frame_addr (x_ly c) cid pos).
{ intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E6 & _). rewrite E6. reflexivity. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
assert (Hin : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos c) HAR Hin) as (Hal & Happ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 (x_fpos c) HAR Hin) as (Hf0 & Hfc & _).
change (fs_frame_bytes 3) with 512 in *.
assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; apply EF).
rewrite HF in Hal, Happ, Hf0, Hfc.
unfold x_s1.
pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)) as D2.
pose proof (Z.div_mod (x_F c) 32 ltac:(lia)) as D3. pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as D5.
split; [exact HAR|].
split; [rewrite Z.mul_comm; apply Z_mod_mult|].
split; [lia|]. split; [exact Hal16|].
split; [rewrite Eslo; lia|]. split; [rewrite Eslo; lia|]. split; [rewrite Eshi; lia|]. split; [rewrite Eshi; lia|].
split; [exact Hin|]. split; [exact HF|].
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [exact Happ|].
split; [reflexivity|]. split; [lia|].
split; [exact Hpres|]. split; [exact EF|].
intros cid pos H. rewrite Hfrs. right. exact H.
Qed.
(* ---- What a call that writes only db's n / over and dp's bytes from n on keeps (IdentBCJ.v tcj_kept) ---- *)
Lemma rlc_K : forall c lyc Sc memc mdc regs mem2 STK' (E : Z -> Prop) n,
  rbn_core B G c lyc Sc memc mdc regs ->
  tcj_kept B STK' lyc Sc (x_W c) memc (x_W c) mem2 (x_s1 c) E ->
  0 <= n ->
  (forall a, E a -> (x_db c + 16 <= a < x_db c + 28) \/ (x_DP c + n <= a < x_DP c + 48)) ->
  (forall a, x_s1 c <= a < x_sp0 c -> ~ (x_db c + 16 <= a < x_db c + 28) ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a) /\
  (forall a, x_F c <= a < x_F c + 512 -> ~ (x_DP c + n <= a < x_DP c + 48) ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a) /\
  (forall a, x_FS c <= a < x_FS c + 64 ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a) /\
  (forall a, inFP (x_FP c) a -> (exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= a < q + N) ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a).
Proof.
intros c lyc Sc memc mdc regs mem2 STK' E n Hc (A1 & A2 & A3 & A4 & _) Hn HE.
destruct (rlc_lay c lyc Sc memc mdc regs Hc)
  as (HAR & Hs32 & Hs1 & Hsp16 & Hceil & Hlo & Hhi & H47 & HinF & HF & HF0 & HFc & HF32 & Happ & HFS & HF8 & _ & _ & _).
pose proof Hc as (_ & _ & Hperm & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold x_db, x_DP in *.
split; [|split; [|split]].
- intros a Ha Hb. apply A1; [lia | lia |]. intros He. destruct (HE a He) as [X|X]; lia.
- intros a Ha Hd. apply (A4 3 (x_fpos c) a HinF).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 3) with 512. lia.
  + intros He. destruct (HE a He) as [X|X]; lia.
- intros a Ha. apply (A4 3 (x_fpos c) a HinF).
  + right. unfold in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 3 / 8) with 64. unfold shadow_addr. lia.
  + intros He. destruct (HE a He) as [X|X];
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *; lia.
- intros a Hfp (q & N & Hin & Hq).
  pose proof (Permutation_in _ (Permutation_sym Hperm) Hin) as Hin2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR Hin2) as (_ & H4096 & Hce & _ & _ & _ & HN).
  pose proof (req_size_pos N ltac:(lia)) as RS.
  replace a with (q + (a - q)) by lia. apply (A2 q N (a - q) Hin2); [lia|].
  replace (q + (a - q)) with a by lia. intros He. destruct (HE a He) as [X|X]; [lia|].
  apply (block_not_frame_zone SEGS B LAWS lyc Sc (x_W c) memc mdc q N (a - q) 3 (x_fpos c) HAR Hin2 HinF); [lia|].
  left. replace (q + (a - q)) with a by lia. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF.
  change (fs_frame_bytes 3) with 512. lia.
Qed.

(* ---- The premises the sb_ch / sb_dec contracts ask at a cut, from rbn_core ---- *)
Lemma rlc_sp : forall c lyc Sc memc mdc regs, rbn_core B G c lyc Sc memc mdc regs -> spZ regs = x_s1 c.
Proof.
intros c lyc Sc memc mdc regs Hc.
destruct (rlc_lay c lyc Sc memc mdc regs Hc) as (_ & _ & Hs1 & _ & Hceil & Hlo & Hhi & H47 & _).
pose proof Hc as (_ & _ & _ & R2 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold spZ. rewrite R2. apply unsigned_lit_small. lia.
Qed.
Lemma rlc_mod4096_mod8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (4096 * (x / 4096)) with (512 * (x / 4096) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma rlc_sub_mod8 : forall x y, x mod 8 = 0 -> y mod 8 = 0 -> (x - y) mod 8 = 0.
Proof.
intros x y Hx Hy. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
rewrite Hx, Z.add_0_r in Dx. rewrite Hy, Z.add_0_r in Dy. rewrite Dx, Dy.
replace (8 * (x / 8) - 8 * (y / 8)) with ((x / 8 - y / 8) * 8) by lia. apply Z.mod_mul. lia.
Qed.
(* db's 28 bytes: the machine stack, whose shadow is 0 (AR_zshadow_law; lib/B/Prog/reac_box_catalogue.v:164). *)
Lemma rlc_db_ra : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  range_addressable (aview SEGS (w_H (x_W c)) memc) SHADOW_OFF (x_db c) 28.
Proof.
intros c lyc Sc memc mdc regs Hc.
destruct (rlc_lay c lyc Sc memc mdc regs Hc) as (HAR & Hs32 & Hs1 & _ & _ & Hlo & Hhi & _).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
pose proof (al_zshadow _ _ LAWS lyc Sc (x_W c) memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
unfold page_aligned in Hpal, Hpah.
apply (range_addressable_sub _ _ (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc));
  [apply zero_shadow_range;
   [exact (rlc_mod4096_mod8 _ Hpal) | exact (rlc_sub_mod8 _ _ (rlc_mod4096_mod8 _ Hpah) (rlc_mod4096_mod8 _ Hpal)) | exact Hz] | unfold x_db; lia | unfold x_db; lia].
Qed.
(* db's n / over: bytes of the caller's stack window (awr_byte case 1), present, not the runtime's. *)
Lemma rlc_db_twr : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  twr_ok B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) lyc Sc [(3, x_fpos c)] (x_W c) memc
    (x_s1 c) (x_db c + 16) 12.
Proof.
intros c lyc Sc memc mdc regs Hc.
destruct (rlc_lay c lyc Sc memc mdc regs Hc)
  as (HAR & Hs32 & Hs1 & Hsp16 & Hceil & Hlo & Hhi & H47 & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _ & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold x_db. intros a Ha.
split; [left; lia|]. split; [apply Hpres; lia|].
split; [apply (al_stack _ _ LAWS lyc Sc (x_W c) memc mdc a HAR); lia | lia].
Qed.
(* dp's bytes DP + k .. DP + k + l: the frame (3, fpos) (awr_byte case 4), shadow 0 by rbn_scope. *)
Lemma rlc_dp : forall c lyc Sc memc mdc regs k l,
  rbn_core B G c lyc Sc memc mdc regs -> rbn_scope c memc 5 0 0 0 ->
  0 <= k -> 0 <= l -> k + l <= 48 ->
  tdst_ok B lyc Sc (x_DP c + k) l /\
  range_addressable (aview SEGS (w_H (x_W c)) memc) SHADOW_OFF (x_DP c + k) l /\
  twr_ok B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) lyc Sc [(3, x_fpos c)] (x_W c) memc
    (x_s1 c) (x_DP c + k) l.
Proof.
intros c lyc Sc memc mdc regs k l Hc Hsc Hk Hl Hkl.
destruct (rlc_lay c lyc Sc memc mdc regs Hc)
  as (HAR & Hs32 & Hs1 & Hsp16 & Hceil & Hlo & Hhi & H47 & HinF & HF & HF0 & HFc & HF32 & Happ & HFS & HF8 & _ & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos c) HAR HinF) as (_ & _ & Hfb & _).
rewrite HF in Hfb. change (fs_frame_bytes 3) with 512 in Hfb.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct Hsc as (_ & _ & _ & S24).
unfold x_DP.
split; [|split].
- intros a Ha. right. exists 3, (x_fpos c). split; [exact HinF|].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 3) with 512. lia.
- intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Hd : x / 8 = (x - x_F c) / 8 + x_F c / 8).
  { replace x with ((x - x_F c) + (x_F c / 8) * 8) at 1 by lia. apply Z.div_add. lia. }
  replace (shadow_of_addr SHADOW_OFF x) with (x_FS c + (x - x_F c) / 8) by (unfold shadow_of_addr; rewrite HFS, Hd; lia).
  apply S24. pose proof (Z.div_mod (x - x_F c) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x - x_F c) 8 ltac:(lia)). lia.
- intros a Ha. destruct (Hfb a ltac:(lia)) as (Hp & Ho).
  split; [right; right; right; exists 3, (x_fpos c); split; [left; reflexivity|];
          left; unfold in_zr; cbn [fst snd]; rewrite HF; change (fs_frame_bytes 3) with 512; lia|].
  split; [exact Hp|]. split; [exact Ho|]. lia.
Qed.
(* sb_dec's budget premises: frames Sc = (3, fpos) :: frames S, the journal's event count, the blocks a
   Permutation of the entry's (blocks_bytes_bsum, bsum_perm). *)
Lemma rlc_budget : forall c lyc Sc memc mdc regs, rbn_core B G c lyc Sc memc mdc regs ->
  Z.of_nat (length (frames Sc)) <= 8 /\ st_nev Sc <= EV_MAX /\ blocks_bytes Sc <= LIVE_MAX.
Proof.
intros c lyc Sc memc mdc regs (Hpre & HJ & Hperm & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hfr7 & Hnev & Hbb).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev2 & _).
split; [rewrite Hfrs; cbn [app length]; lia|]. split; [lia|].
rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ Hperm), <- (blocks_bytes_bsum B (x_ly c) (x_S c)). exact Hbb.
Qed.
(* in / out: 0 .. 40 (bn_ok), so sb_dec's digits are bytes. *)
Lemma rlc_v : forall c v,
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true -> (v = x_i c \/ v = x_o c) ->
  0 <= v <= 40 /\ Forall (fun x => 0 <= x < 256) (sb_dec_c.sb_dec_D v 1).
Proof.
intros c v Hok Hv.
destruct (reac_box_name.args_ok_split _ _ _ _ _ _ _ _ Hok) as (_ & _ & _ & _ & _ & _ & Hi & Ho & _).
assert (Hbv : bn_ok v = true) by (destruct Hv as [-> | ->]; assumption).
destruct (reac_box_name.bn_ok_dec v Hbv) as (Hr & _ & _ & _ & HD & _ & HF).
split; [exact Hr|]. rewrite HD. eapply Forall_impl; [|exact HF]. intros x Hx. cbv beta in Hx. lia.
Qed.

(* ---- The segment's resume state: rbn_C9 / rbn_C10's shape with db holding st ---- *)
Definition rbn_lit (c : rbx) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) (st : list Z * Z) : Prop :=
  rbn_live B G c lyc Sc memc mdc regs /\ rbn_w4done c memc regs /\ rbn_nmdone c memc regs /\
  rbn_tkdone c memc regs /\ rbn_scope c memc 5 0 0 0 /\
  rbn_sb c memc (x_db c) (x_DP c) 48 (fst st) (snd st).

Lemma rlc_sb_tr : forall c m m' b q cap cs ov,
  rbn_sb c m b q cap cs ov ->
  (forall a, b <= a < b + 28 \/ q <= a < q + Z.of_nat (length cs) ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_sb c m' b q cap cs ov.
Proof.
intros c m m' b q cap cs ov (Vp & Vc & Vn & Vo & Ho & Hl & Hr & Gq) K. unfold rbn_sb, x_mem_at in *. cbv zeta in *.
split; [eapply rlc_val_mem_kept; [|exact Vp]; intros x Hx; apply K; left; cbn in Hx; lia|].
split; [eapply rlc_val_mem_kept; [|exact Vc]; intros x Hx; apply K; left; cbn in Hx; lia|].
split; [eapply rlc_val_mem_kept; [|exact Vn]; intros x Hx; apply K; left; cbn in Hx; lia|].
split; [eapply rlc_val_mem_kept; [|exact Vo]; intros x Hx; apply K; left; cbn in Hx; lia|].
split; [exact Ho|]. split; [exact Hl|]. split; [exact Hr|].
eapply rlc_garr8_kept; [|exact Gq]. intros a Ha. apply K. right. exact Ha.
Qed.
(* One callee-saved register of the cut, carried by aregs_preserved. *)
Local Ltac rlc_rr HP r R := refine (eq_trans (HP r ltac:(unfold acallee_saved; lia)) R).
(* rbn_lit at the return state of a call that kept every byte of its footprint but db's n / over and dp's bytes
   from length (fst st) on, with a new journal, the same blocks and the callee-saved registers. *)
Lemma rlc_kept : forall c lyc Sc memc mdc regs st lyc2 Sc2 mem2 md2 regs2 st2,
  rbn_lit c lyc Sc memc mdc regs st ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc2 Sc2 (x_W c) mem2 md2 0 ->
  Permutation (ablocks B lyc2 Sc2) (ablocks B lyc Sc) ->
  aregs_preserved regs regs2 ->
  (forall a, x_s1 c <= a < x_sp0 c -> ~ (x_db c + 16 <= a < x_db c + 28) ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a) ->
  (forall a, x_F c <= a < x_F c + 512 -> ~ (x_DP c + Z.of_nat (length (fst st)) <= a < x_DP c + 48) ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a) ->
  (forall a, x_FS c <= a < x_FS c + 64 ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a) ->
  (forall a, inFP (x_FP c) a -> (exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= a < q + N) ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a) ->
  rbn_sb c mem2 (x_db c) (x_DP c) 48 (fst st2) (snd st2) ->
  rbn_lit c lyc2 Sc2 mem2 md2 regs2 st2.
Proof.
intros c lyc Sc memc mdc regs st lyc2 Sc2 mem2 md2 regs2 st2 (Hlive & Hw4 & Hnm & Htk & Hsc & Hsb) HJ2 Hp2 HP
  KW KF KS KB Hsb2.
pose proof Hlive as (Hcore & Hok & Hbk & Hsl & R22).
pose proof Hcore as (Hpre & HJ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsv & Hfl).
destruct (rlc_lay c lyc Sc memc mdc regs Hcore)
  as (_ & Hs32 & Hs1 & Hsp16 & _ & _ & _ & _ & _ & _ & HF0 & HFc & _ & _ & _ & _ & _ & _ & _).
pose proof Hsb as (_ & _ & _ & _ & _ & Hn47 & _).
assert (Hn0 : 0 <= Z.of_nat (length (fst st))) by lia.
unfold rbn_lit.
split; [|split; [|split; [|split; [|split]]]].
- split; [|split; [exact Hok|split; [|split]]].
  + split; [exact Hpre|]. split; [exact HJ2|]. split; [exact (Permutation_trans Hp2 Hperm)|].
    split; [rlc_rr HP 2 R2|]. split; [rlc_rr HP 3 R3|]. split; [rlc_rr HP 4 R4|]. split; [rlc_rr HP 8 R8|].
    split; [rlc_rr HP 9 R9|]. split; [rlc_rr HP 18 R18|]. split; [rlc_rr HP 19 R19|]. split; [rlc_rr HP 23 R23|].
    split.
    * unfold rbn_saved in *. rewrite Forall_forall in *. intros p Hp. specialize (Hsv p Hp).
      assert (Hoff : 8 <= fst p <= 104)
        by (unfold rbn_saved_regs in Hp; cbn [In] in Hp; repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia|]); destruct Hp).
      unfold x_mem_at in *. eapply rlc_val_mem_kept; [|exact Hsv]. intros x Hx. apply KW; unfold x_db; lia.
    * rewrite (rlc_rdword_kept _ memc mem2); [exact Hfl|]. intros x Hx. apply KF; unfold x_DP; lia.
  + intros a Ha Hb. rewrite (KB a Ha Hb). exact (Hbk a Ha Hb).
  + unfold rbn_slots, x_mem_at in *. cbv zeta in *.
    destruct Hsl as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V80).
    repeat split; (eapply rlc_val_mem_kept; [|eassumption]); intros x Hx; apply KW; unfold x_db; lia.
  + rlc_rr HP 22 R22.
- destruct Hw4 as (Hsbw & Gw & R27). pose proof Hsbw as (_ & _ & _ & _ & _ & Hlw & _).
  split; [apply (rlc_sb_tr c memc); [exact Hsbw|]|split; [|rlc_rr HP 27 R27]].
  + intros a Ha. unfold x_wb, x_W4 in Ha. destruct Ha as [Ha|Ha]; [apply KW; unfold x_db; lia | apply KF; unfold x_DP; lia].
  + unfold x_mem_at in *. eapply rlc_garr8_kept; [|exact Gw]. intros a Ha.
    rewrite length_app in Ha. cbn [length] in Ha. unfold x_W4 in Ha. apply KF; unfold x_DP; lia.
- destruct Hnm as (Hsbn & Gn & R25). pose proof Hsbn as (_ & _ & _ & _ & _ & Hln & _).
  split; [apply (rlc_sb_tr c memc); [exact Hsbn|]|split; [|rlc_rr HP 25 R25]].
  + intros a Ha. unfold x_nb, x_NM in Ha. destruct Ha as [Ha|Ha]; [apply KW; unfold x_db; lia | apply KF; unfold x_DP; lia].
  + unfold x_mem_at in *. eapply rlc_garr8_kept; [|exact Gn]. intros a Ha.
    rewrite length_app in Ha. cbn [length] in Ha. unfold x_NM in Ha. apply KF; unfold x_DP; lia.
- destruct Htk as (Hsbt & Gt & R26). pose proof Hsbt as (_ & _ & _ & _ & _ & Hlt & _).
  split; [apply (rlc_sb_tr c memc); [exact Hsbt|]|split; [|rlc_rr HP 26 R26]].
  + intros a Ha. unfold x_tb, x_TK in Ha. destruct Ha as [Ha|Ha]; [apply KW; unfold x_db; lia | apply KF; unfold x_DP; lia].
  + unfold x_mem_at in *. eapply rlc_garr8_kept; [|exact Gt]. intros a Ha.
    rewrite length_app in Ha. cbn [length] in Ha. unfold x_TK in Ha. apply KF; unfold x_DP; lia.
- destruct Hsc as (S4 & S8 & S16 & S24). unfold rbn_scope. cbv zeta.
  split; [rewrite KS by lia; exact S4|].
  split; [intros j Hj; rewrite KS by lia; exact (S8 j Hj)|].
  split; [intros j Hj; rewrite KS by lia; exact (S16 j Hj)|].
  intros j Hj; rewrite KS by lia; exact (S24 j Hj).
- exact Hsb2.
Qed.

Lemma rbn_lit_call_ch : forall c lyc Sc memc mdc regs st ch retk Q,
  rbn_lit c lyc Sc memc mdc regs st ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs 10 = w64 (x_db c) -> getr regs 11 = w64 ch -> 0 <= ch < 256 ->
  (forall lyc2 Sc2 regs2 mem2 md2,
     aregs_preserved regs regs2 ->
     rbn_lit c lyc2 Sc2 mem2 md2 regs2 (sbm_ch 48 st ch) ->
     SRr SEGS (x_W c) (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_sb_ch) regs memc mdc) Q.
Proof.
intros c lyc Sc memc mdc regs st ch retk Q Hlit Rra Hrk Hrk2 R10 R11 Hch HK.
pose proof Hlit as (Hlive & _ & _ & _ & Hsc & Hsb).
pose proof Hlive as (Hcore & Hok & _ & _ & _).
pose proof Hcore as (Hpre & HJ & Hperm & R2 & R3 & R4 & _).
destruct (rlc_lay c lyc Sc memc mdc regs Hcore)
  as (HAR & Hs32 & Hs1 & Hsp16 & Hceil & Hlo & Hhi & H47 & HinF & HF & HF0 & HFc & HF32 & Happ & HFS & HF8 & _ & _ & _).
pose proof (rlc_sp c lyc Sc memc mdc regs Hcore) as Hsp.
pose proof (rlc_db_ra c lyc Sc memc mdc regs Hcore) as HRA.
pose proof (rlc_db_twr c lyc Sc memc mdc regs Hcore) as HWR.
destruct st as [cs ov].
pose proof Hsb as (Vp & Vc & Vn & Vo & Hov & Hn47 & Hcs & Gcs).
cbn [fst snd] in Vp, Vc, Vn, Vo, Hov, Hn47, Hcs, Gcs.
unfold x_mem_at in Vp, Vc, Vn, Vo, Gcs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HCS : SB_CH_STK = 4112) by reflexivity.
assert (Hs16 : x_s1 c mod 16 = 0).
{ pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs32, Z.add_0_r in D. rewrite D.
  replace (32 * (x_s1 c / 32)) with (2 * (x_s1 c / 32) * 16) by lia. apply Z.mod_mul. lia. }
assert (Hb8 : x_db c mod 8 = 0).
{ unfold x_db. pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs32, Z.add_0_r in D. rewrite D.
  replace (32 * (x_s1 c / 32) + 88) with ((4 * (x_s1 c / 32) + 11) * 8) by lia. apply Z.mod_mul. lia. }
eapply SRr_bind;
  [apply (HSC (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
            lyc Sc (x_W c) memc mdc 0 regs (x_db c) ch (x_DP c) 48 (Z.of_nat (length cs)) ov HJ) |].
- rewrite Rra. apply ret_ok_codeptr_v; lia.
- unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
- exact R3.
- exact R4.
- rewrite Hsp. exact Hs16.
- rewrite Hsp, HCS. lia.
- rewrite Hsp. lia.
- exact R10.
- exact R11.
- exact Hch.
- exact Hb8.
- unfold x_db. lia.
- unfold x_db. lia.
- left. rewrite Hsp. unfold x_db. lia.
- right. unfold x_db. lia.
- exact Vp.
- exact Vc.
- exact Vn.
- exact Vo.
- unfold x_DP. lia.
- lia.
- lia.
- lia.
- lia.
- exact HRA.
- rewrite Hsp. exact HWR.
- intros Hroom.
  destruct (rlc_dp c lyc Sc memc mdc regs (Z.of_nat (length cs)) 1 Hcore Hsc ltac:(lia) ltac:(lia) ltac:(lia))
    as (D1 & D2 & D3).
  split; [unfold x_DP; lia|]. split; [unfold x_DP; lia|].
  split; [exact D1|]. split; [exact D2|]. split; [rewrite Hsp; exact D3|].
  split; [left; unfold x_DP, x_db; lia|]. left. rewrite Hsp, HCS. unfold x_DP. lia.
- intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HT & Vp2 & Vc2 & HIF).
  change (0 + EV_SB_CH) with 0 in HJ2. rewrite Hsp in HT.
  rewrite Rra. apply (HK lyc Sc regs2 mem2 md2 HP).
  destruct (rlc_K c lyc Sc memc mdc regs mem2 SB_CH_STK (tsb_ch_wr (x_db c) (x_DP c) (Z.of_nat (length cs)) 48)
    (Z.of_nat (length cs)) Hcore HT ltac:(lia)) as (KW & KF & KS & KB).
  { intros a [Ha | (_ & Ha)]; [left; exact Ha | right; lia]. }
  apply (rlc_kept c lyc Sc memc mdc regs (cs, ov) lyc Sc mem2 md2 regs2 _ Hlit HJ2 (Permutation_refl _) HP
    KW KF KS KB).
  assert (Gk : garr8 SEGS (mrestrict (w_H (x_W c)) mem2) (x_DP c) cs).
  { eapply rlc_garr8_kept; [|exact Gcs]. intros a Ha. apply KF; unfold x_DP in *; lia. }
  unfold sbm_ch. cbn [fst snd].
  unfold rbn_sb, x_mem_at. cbv zeta.
  destruct (Z.of_nat (length cs) + 1 <? 48) eqn:Er; cbn [fst snd].
  + destruct HIF as (Vn2 & Vo2 & Gch). apply Z.ltb_lt in Er.
    split; [exact Vp2|]. split; [exact Vc2|].
    split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact Vn2|].
    split; [exact Vo2|]. split; [exact Hov|].
    split; [rewrite length_app; cbn [length]; lia|].
    split; [apply Forall_app; split; [exact Hcs | constructor; [lia | constructor]]|].
    apply garr8_app. split; [exact Gk | exact Gch].
  + destruct HIF as (Vn2 & Vo2).
    split; [exact Vp2|]. split; [exact Vc2|]. split; [exact Vn2|]. split; [exact Vo2|].
    split; [right; reflexivity|]. split; [exact Hn47|]. split; [exact Hcs|]. exact Gk.
Qed.

Lemma rbn_lit_call_dec : forall c lyc Sc memc mdc regs st v retk Q,
  rbn_lit c lyc Sc memc mdc regs st ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs 10 = w64 (x_db c) -> getr regs 11 = w64 v -> getr regs 12 = w64 1 ->
  (v = x_i c \/ v = x_o c) ->
  (forall lyc2 Sc2 regs2 mem2 md2,
     aregs_preserved regs regs2 ->
     rbn_lit c lyc2 Sc2 mem2 md2 regs2 (sbm_str 48 st (sb_dec_c.sb_dec_D v 1)) ->
     SRr SEGS (x_W c) (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_sb_dec) regs memc mdc) Q.
Proof.
intros c lyc Sc memc mdc regs st v retk Q Hlit Rra Hrk Hrk2 R10 R11 R12 Hv HK.
pose proof Hlit as (Hlive & _ & _ & _ & Hsc & Hsb).
pose proof Hlive as (Hcore & Hok & _ & _ & _).
pose proof Hcore as (Hpre & HJ & Hperm & R2 & R3 & R4 & _).
destruct (rlc_lay c lyc Sc memc mdc regs Hcore)
  as (HAR & Hs32 & Hs1 & Hsp16 & Hceil & Hlo & Hhi & H47 & HinF & HF & HF0 & HFc & HF32 & Happ & HFS & HF8 & _ & _ & _).
pose proof (rlc_sp c lyc Sc memc mdc regs Hcore) as Hsp.
pose proof (rlc_db_twr c lyc Sc memc mdc regs Hcore) as HWR.
destruct (rlc_budget c lyc Sc memc mdc regs Hcore) as (Hfr8 & Hnev & Hbb).
destruct (rlc_v c v Hok Hv) as (Hv40 & HDc).
destruct st as [cs ov].
pose proof Hsb as (Vp & Vc & Vn & Vo & Hov & Hn47 & Hcs & Gcs).
cbn [fst snd] in Vp, Vc, Vn, Vo, Hov, Hn47, Hcs, Gcs.
unfold x_mem_at in Vp, Vc, Vn, Vo, Gcs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HDS : SB_DEC_STK = 4256) by reflexivity.
assert (Hs16 : x_s1 c mod 16 = 0).
{ pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs32, Z.add_0_r in D. rewrite D.
  replace (32 * (x_s1 c / 32)) with (2 * (x_s1 c / 32) * 16) by lia. apply Z.mod_mul. lia. }
assert (Hb8 : x_db c mod 8 = 0).
{ unfold x_db. pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs32, Z.add_0_r in D. rewrite D.
  replace (32 * (x_s1 c / 32) + 88) with ((4 * (x_s1 c / 32) + 11) * 8) by lia. apply Z.mod_mul. lia. }
set (n := Z.of_nat (length cs)) in *.
set (D := sb_dec_c.sb_dec_D v 1) in *.
assert (Hroom : sb_dec_c.sb_dec_room 48 n = 47 - n).
{ unfold sb_dec_c.sb_dec_room. rewrite (proj2 (Z.leb_le (n + 1) 48)) by lia. reflexivity. }
assert (Hacc : 0 <= sb_dec_c.sb_dec_acc v 1 48 n <= 47 - n /\ sb_dec_c.sb_dec_acc v 1 48 n <= Z.of_nat (length D)).
{ unfold sb_dec_c.sb_dec_acc. fold D. rewrite Hroom. lia. }
set (acc := sb_dec_c.sb_dec_acc v 1 48 n) in *.
eapply SRr_bind;
  [apply (HSB (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
            lyc Sc (x_W c) memc mdc 0 regs (x_db c) v 1 (x_DP c) 48 n ov HJ) |].
- rewrite Rra. apply ret_ok_codeptr_v; lia.
- unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
- exact R3.
- exact R4.
- rewrite Hsp. exact Hs16.
- rewrite Hsp, HDS. lia.
- rewrite Hsp. lia.
- exact R10.
- exact R11.
- exact R12.
- lia.
- left. reflexivity.
- exact Hb8.
- unfold x_db. lia.
- unfold x_db. lia.
- left. rewrite Hsp. unfold x_db. lia.
- unfold tsb_dec_rec_at, x_db. lia.
- exact Vp.
- exact Vc.
- exact Vn.
- exact Vo.
- unfold x_DP. lia.
- lia.
- lia.
- lia.
- lia.
- rewrite Hsp. exact HWR.
- intros _.
  destruct (rlc_dp c lyc Sc memc mdc regs n acc Hcore Hsc ltac:(lia) ltac:(lia) ltac:(lia)) as (D1 & D2 & D3).
  split; [unfold x_DP; lia|]. split; [unfold x_DP; lia|].
  split; [exact D1|]. split; [exact D2|]. split; [rewrite Hsp; exact D3|].
  split; [left; unfold x_DP, x_db; lia|]. left. rewrite Hsp, HDS. unfold x_DP. lia.
- exact Hfr8.
- unfold EV_SB_DEC. lia.
- unfold LIVE_SB_DEC. lia.
- intros W2 c2 _ (-> & ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hfr2 & Hp2 & HT & Vp2 & Vc2 & Vn2 & Vo2 & G2).
  change (0 + EV_SB_DEC) with 0 in HJ2. rewrite Hsp in HT.
  rewrite Rra. apply (HK ly2 S2 regs2 mem2 md2 HP).
  destruct (rlc_K c lyc Sc memc mdc regs mem2 SB_DEC_STK (tsb_dec_wr (x_db c) (x_DP c) n acc) n Hcore HT ltac:(lia))
    as (KW & KF & KS & KB).
  { intros a [Ha | Ha]; [left; exact Ha | right; lia]. }
  apply (rlc_kept c lyc Sc memc mdc regs (cs, ov) ly2 S2 mem2 md2 regs2 _ Hlit HJ2 Hp2 HP KW KF KS KB).
  assert (Gk : garr8 SEGS (mrestrict (w_H (x_W c)) mem2) (x_DP c) cs).
  { eapply rlc_garr8_kept; [|exact Gcs]. intros a Ha. apply KF; unfold x_DP in *; lia. }
  pose proof (sbm_dec_post 48 cs ov v 1 n eq_refl ltac:(lia)) as ESB.
  change (sb_dec_c.sb_dec_D v 1) with D in ESB. change (sb_dec_c.sb_dec_acc v 1 48 n) with acc in ESB.
  rewrite ESB. cbn [fst snd].
  assert (HL : length (firstn (Z.to_nat acc) D) = Z.to_nat acc) by (apply firstn_length_le; lia).
  unfold rbn_sb, x_mem_at. cbv zeta.
  split; [exact Vp2|]. split; [exact Vc2|].
  split; [rewrite length_app, HL, Nat2Z.inj_add, Z2Nat.id by lia; exact Vn2|].
  split; [exact Vo2|].
  split; [destruct (sb_dec_c.sb_dec_room 48 n <? Z.of_nat (length D)); [right; reflexivity | exact Hov]|].
  split; [rewrite length_app, HL; lia|].
  split; [apply Forall_app; split; [exact Hcs | apply Forall_firstn_h; exact HDc]|].
  apply garr8_app. split; [exact Gk | exact G2].
Qed.


(* ---- The three literals the segment appends (rbn_img: objects 23, 24, 25) ---- *)
Definition lit_s (k : nat) : list Z :=
  match k with O => [32; 40] | S O => [32; 105; 110; 32; 47; 32] | _ => [32; 111; 117; 116; 41] end.
Definition lit_O (k : nat) : nat := A_OBJ (23 + k).
Definition lit_n (k : nat) : Z := Z.of_nat (length (lit_s k)).

Ltac lit_split H := repeat match type of H with _ /\ _ => let H1 := fresh "H" in destruct H as [H1 H] end.

Lemma lit_img : forall c lyc Sc memc mdc regs st k, rbn_lit c lyc Sc memc mdc regs st -> (k < 3)%nat ->
  VAL (lit_O k) mod 8 = 0 /\ rbn_imgstr B G (x_W c) (x_mem c) (VAL (lit_O k)) (lit_s k).
Proof.
intros c lyc Sc memc mdc regs st k HL Hk.
destruct HL as (((Hpre & _) & _) & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
destruct Himg as (_ & _ & _ & _ & _ & _ & _ & A23 & I23 & A24 & I24 & A25 & I25).
destruct k as [|[|[|k]]]; [split; assumption | split; assumption | split; assumption | lia].
Qed.

Lemma lit_n_cases : forall k, (k < 3)%nat -> (k = 0%nat /\ lit_n k = 2) \/ (k = 1%nat /\ lit_n k = 6) \/ (k = 2%nat /\ lit_n k = 5).
Proof. intros k Hk. destruct k as [|[|[|k]]]; [left | right; left | right; right | lia]; split; reflexivity. Qed.

Lemma lit_shadow : forall c lyc Sc memc mdc regs st k, rbn_lit c lyc Sc memc mdc regs st -> (k < 3)%nat ->
  exists sh, aview SEGS (w_H (x_W c)) memc (SHADOW_OFF + VAL (lit_O k) / 8) = Some sh /\
    (sh = 0 \/ lit_n k < sh < 8).
Proof.
intros c lyc Sc memc mdc regs st k HL Hk.
destruct (lit_img c lyc Sc memc mdc regs st k HL Hk) as (Hal & Hlo & Hhi & _ & _ & (q & z & Hin & Hq1 & Hq2) & _).
destruct HL as (((_ & HJ & _) & _) & _). pose proof (proj1 HJ) as HAR.
fold (lit_n k) in Hhi, Hq2.
assert (Hn : 2 <= lit_n k <= 6) by (destruct (lit_n_cases k Hk) as [(_ & ->) | [(_ & ->) | (_ & ->)]]; lia).
destruct (ro_read_ok_glob SEGS B G lyc Sc (x_W c) memc mdc q z (VAL (lit_O k)) (lit_n k + 1) GM Hin IV HAR
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [RA _].
destruct (RA (VAL (lit_O k) + lit_n k) ltac:(lia)) as (s & Hs & Hok).
exists s. split.
- rewrite shadow_of_addr_aligned_off in Hs by exact Hal.
  unfold shadow_of_addr in Hs. rewrite (Z.div_small (lit_n k) 8) in Hs by lia. rewrite Z.add_0_r in Hs. exact Hs.
- unfold saddr_ok in Hok. rewrite Z.add_mod, Hal, Z.add_0_l, Z.mod_mod, (Z.mod_small (lit_n k)) in Hok by lia. lia.
Qed.

Lemma lit_mbyte_of_aview : forall H m1 m2 x, aview SEGS H m2 x = aview SEGS H m1 x ->
  mbyte SEGS (mrestrict H m2) x = mbyte SEGS (mrestrict H m1) x.
Proof.
intros H m1 m2 x E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m2) x) as [b2|], (mbyte SEGS (mrestrict H m1) x) as [b1|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma lit_garr8_kept : forall H m1 m2 a l, garr8 SEGS (mrestrict H m1) a l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H m2 (a + j) = aview SEGS H m1 (a + j)) ->
  garr8 SEGS (mrestrict H m2) a l.
Proof.
intros H m1 m2 a l Hg K j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite lit_mbyte_of_aview with (m1 := m1) by (replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j) by lia; apply K; lia).
exact (Hv 0%nat Hk).
Qed.

(* FP holds no range at address 0 (reac_box_name_inv.v rbn_fp_closed: the three pointers are not negative). *)
Lemma lit_fp_closed : forall c lyc Sc memc mdc regs st, rbn_lit c lyc Sc memc mdc regs st ->
  ~ YI16.sink_open_fp (x_FP c).
Proof.
intros c lyc Sc memc mdc regs st HL.
destruct HL as (((Hpre & _) & _) & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rn & _ & _ & _ & Rt & _ & _ & _ & _ & Rd & _).
unfold x_FP. apply rbn_fp_closed; lia.
Qed.

Lemma lit_chars : forall c lyc Sc memc mdc regs st k, rbn_lit c lyc Sc memc mdc regs st -> (k < 3)%nat ->
  garr8 SEGS (mrestrict (w_H (x_W c)) memc) (VAL (lit_O k)) (lit_s k ++ [0]).
Proof.
intros c lyc Sc memc mdc regs st k HL Hk.
pose proof (lit_fp_closed c lyc Sc memc mdc regs st HL) as Hcl.
destruct (lit_img c lyc Sc memc mdc regs st k HL Hk) as (_ & _ & _ & _ & Hg & _ & Hfix & _).
destruct HL as (((_ & HJ & _) & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J11 & _).
apply (lit_garr8_kept _ (x_mem c)); [exact Hg|].
intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Hfix (VAL (lit_O k) + j) ltac:(lia)) as (Hi & Ho & He).
apply J11; [exact Hi | exact Ho | exact He | apply fp_spares_closed; exact Hcl].
Qed.

Lemma lit_stack : forall c lyc Sc memc mdc regs st, rbn_lit c lyc Sc memc mdc regs st ->
  x_sp0 c mod 16 = 0 /\ alloc_ceiling + 8528 <= x_sp0 c /\ x_sp0 c <= 2 ^ 47 /\
  x_sp0 c - 352 < x_s1 c /\ x_s1 c + 320 <= x_sp0 c /\ x_s1 c mod 32 = 0 /\ 140735332483072 <= alloc_ceiling.
Proof.
intros c lyc Sc memc mdc regs st HL.
destruct HL as (((Hpre & _) & _) & _).
destruct Hpre as ((_ & _ & _ & _ & _ & Hstk & _) & _).
destruct Hstk as (H16 & _ & Hce & Hlo & Hhi & H47 & _).
pose proof asan_consts as (C1 & _).
fold (x_sp0 c) in H16, Hlo, Hhi. unfold ESTACK in Hlo.
unfold x_s1. pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)) as Mb.
split; [exact H16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|lia].
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Definition lit_rS (z : bool) : YP09.region :=
  YP09.mkRegion (Some 32%nat) SHADOW_OFF (SHADOW_OFF + 1) 0 0
    [YP09.mkChunk SHADOW_OFF (CVal 1 (if z then SLit 0 else SOff 33 0))].
Definition lit_rC (o : nat) (j ch : Z) : YP09.region :=
  YP09.mkRegion (Some o) j (j + 1) 0 0 [YP09.mkChunk j (CVal 1 (SLit ch))].
Definition lit_rW : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 56 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 0))].
Definition lit_pin (pin : option (Z * nat * Z)) : list sv :=
  match pin with
  | None => sr_set sr_atoms 22%bv (SLit SHADOW_OFF)
  | Some (j4, o, n8) =>
      sr_set (sr_set (sr_set (sr_set sr_atoms 22%bv (SLit SHADOW_OFF)) 20%bv (SLit j4)) 21%bv (SOff o 0)) 24%bv (SLit n8)
  end.
Definition lit_ss (pc : Z) (pin : option (Z * nat * Z)) (o : nat) (j ch : Z) (z : bool) (slo shi : Z) : sstate :=
  mkSS pc (lit_pin pin) [lit_rS z; lit_rC o j ch; lit_rW] None
    (mkFacts [(33%nat, mkAF slo shi 0)] [] [(SAlu ALU_SRL (SOff o j) (SLit 3), SOff 32 0)]).
Definition lit_E (regs : bvmap 5 word) (o : nat) (sh xi xo : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [VAL o / 8; sh; xi; xo])).

Lemma lit_val_mem1 : forall H m a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v /\ 0 <= v < 256.
Proof.
intros H m a v E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; cbn [option_map] in E; [|discriminate].
injection E as <-. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|lia]. intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.

Lemma lit_rC_wf : forall o j ch, YP09.region_wf (lit_rC o j ch) = true.
Proof.
intros o j ch. unfold YP09.region_wf, lit_rC, YP09.chunk_inside.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb YP09.c_off YP09.c_len YP09.c_val YP09.cv_len].
repeat (match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end); cbn; first [reflexivity | lia].
Qed.

Lemma lit_nth_app0 : forall (s : list Z) j, (j <= length s)%nat -> nth j (s ++ [0]) 0 = nth j s 0.
Proof.
intros s j Hj. destruct (Nat.eq_dec j (length s)) as [->|Hne].
- rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
- apply app_nth1. lia.
Qed.

Lemma lit_entry : forall c lyc Sc memc mdc regs st (k : nat) j pin pc sh (z : bool) slo shi,
  rbn_lit c lyc Sc memc mdc regs st -> (k < 3)%nat -> 0 <= j <= lit_n k ->
  aview SEGS (w_H (x_W c)) memc (SHADOW_OFF + VAL (lit_O k) / 8) = Some sh -> slo <= sh <= shi ->
  (z = true -> sh = 0) ->
  match pin with
  | Some (j4, o, n8) => o = lit_O k /\ getr regs 20 = w64 j4 /\ getr regs 21 = w64 (VAL o) /\ getr regs 24 = w64 n8
  | None => True
  end ->
  st_ok_pi SEGS VAL (lit_E regs (lit_O k) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64))
    (lit_ss pc pin (lit_O k) j (nth (Z.to_nat j) (lit_s k) 0) z slo shi)
    (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros c lyc Sc memc mdc regs st k j pin pc sh z slo shi HL Hk Hj Hsh Hr Hz Hpin.
pose proof (lit_stack c lyc Sc memc mdc regs st HL) as (S16 & Sce & S47 & Sa & Sb & S32 & C0).
destruct (lit_img c lyc Sc memc mdc regs st k HL Hk) as (Hal & Hlo & Hhi & _).
pose proof (lit_chars c lyc Sc memc mdc regs st k HL Hk) as Hch.
destruct (lit_val_mem1 _ _ _ _ Hsh) as (Vsh & Rsh).
assert (Hn : 2 <= lit_n k <= 6) by (destruct (lit_n_cases k Hk) as [(_ & ->) | [(_ & ->) | (_ & ->)]]; lia).
fold (lit_n k) in Hhi.
pose proof HL as (((_ & _ & _ & _ & _ & _ & _ & R9 & _) & _ & _ & Hslots & R22) & _).
destruct Hslots as (_ & _ & _ & _ & _ & Vi & Vo & _).
assert (HOk : (A_TEXT <= lit_O k < A_LIM)%nat) by (unfold lit_O, A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (lit_O k)) as VO.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (lit_E regs (lit_O k) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64)) n =
  ew (Ereg regs (map (Z_to_bv 64) [VAL (lit_O k) / 8; sh; x_i c mod 2 ^ 64; x_o c mod 2 ^ 64])) n)
  by (intros n Hn0; unfold lit_E; apply Eimg_low; exact Hn0).
set (E := lit_E regs (lit_O k) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64)) in *.
assert (U9 : bv_unsigned (ew E 9) = x_s1 c).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. lia. }
assert (U32 : bv_unsigned (ew E 32) = VAL (lit_O k) / 8).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs _ 0). cbn [map nth]. apply unsigned_lit_small.
  split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ (VAL (lit_O k))); [apply Z.div_le_upper_bound; lia | lia]]. }
assert (E33 : ew E 33 = Z_to_bv 64 sh) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (x_i c mod 2 ^ 64)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (x_o c mod 2 ^ 64)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EO : ew E (lit_O k) = Z_to_bv 64 (VAL (lit_O k))) by (subst E; unfold lit_E; apply Eimg_img; exact HOk).
assert (UO : bv_unsigned (ew E (lit_O k)) = VAL (lit_O k)) by (rewrite EO; apply unsigned_lit_small; exact VO).
rewrite restrict_mkst_fx. unfold lit_ss. apply pa_entry_st_ok_full.
- assert (L22 : getr regs 22 = sv_denot E (SLit SHADOW_OFF)) by (cbn [sv_denot]; exact R22).
  destruct pin as [[[j4 o] n8]|]; cbn [lit_pin].
  + destruct Hpin as (-> & P20 & P21 & P24).
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [subst E; unfold lit_E; apply regs_ok_Eimg_Ereg | discriminate | exact L22] | discriminate | cbn [sv_denot]; exact P20] | discriminate | ] | discriminate | cbn [sv_denot]; exact P24].
    cbn [sv_denot]. rewrite UO, Z.add_0_r. exact P21.
  + apply regs_ok_pin; [subst E; unfold lit_E; apply regs_ok_Eimg_Ereg | discriminate | exact L22].
- cbn [YP09.regions_wf]. rewrite lit_rC_wf. destruct z; vm_compute; reflexivity.
- assert (HO8 : 0 <= VAL (lit_O k) / 8 <= VAL (lit_O k)) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hjn : (Z.to_nat j <= length (lit_s k))%nat) by (unfold lit_n in Hj; lia).
  destruct (Hch (Z.to_nat j) ltac:(rewrite length_app; cbn [length]; lia)) as (Vc & Rc).
  rewrite lit_nth_app0 in Vc, Rc by exact Hjn. rewrite Z2Nat.id in Vc by lia.
  constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold YP09.region_ok, lit_rS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U32. unfold SHADOW_OFF at 1 2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (lit_O k) / 8) SHADOW_OFF 1 (if z then SLit 0 else SOff 33 0) sh);
      [destruct z; [rewrite (Hz eq_refl); reflexivity | cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity] | cbn; lia | lia |].
    rewrite Z.add_comm. exact Vsh.
  + unfold YP09.region_ok, lit_rC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite UO. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (lit_O k)) j 1 (SLit (nth (Z.to_nat j) (lit_s k) 0)) (nth (Z.to_nat j) (lit_s k) 0)); [cbn [sv_denot]; reflexivity | cbn; lia | lia | exact Vc].
  + unfold YP09.region_ok, lit_rW. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold x_mem_at in Vi, Vo.
    pose proof (Z.mod_pos_bound (x_i c) (2 ^ 64) ltac:(lia)) as Mi. pose proof (Z.mod_pos_bound (x_o c) (2 ^ 64) ltac:(lia)) as Mo.
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 40 8 (SOff 34 0) (x_i c mod 2 ^ 64));
        [cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | lia | exact Vi].
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 48 8 (SOff 35 0) (x_o c mod 2 ^ 64));
        [cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | lia | exact Vo].
- assert (HO8 : 0 <= VAL (lit_O k) / 8 <= VAL (lit_O k)) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val lit_rS lit_rC lit_rW].
  rewrite U32, UO, U9. unfold SHADOW_OFF.
  repeat split; first [left; lia | right; lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I|split; [|exact I]]].
  + split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia.
  + apply U_inj. rewrite U_SAlu, !U_SOff. assert (U3 : U E (SLit 3) = 3) by (unfold U; cbn [sv_denot]; apply unsigned_lit_small; lia).
    rewrite UO, U32, U3. cbn [zalu_raw]. change (Z.land 3 63) with 3. unfold zcanon, M64.
    rewrite (Z.mod_small (VAL (lit_O k) + j)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.add_0_r. f_equal.
    rewrite (Z.div_mod (VAL (lit_O k)) 8) at 1 by lia. rewrite Hal, Z.add_0_r.
    replace (8 * (VAL (lit_O k) / 8) + j) with (j + VAL (lit_O k) / 8 * 8) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.


(* ---- Moving rbn_lit to a memory equal at every address and registers equal where it reads them ---- *)
Lemma lit_mb_ext : forall H (m m' : word -> option byte) a, (forall x, m' x = m x) ->
  mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros H m m' a E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma lit_av_ext : forall H (m m' : word -> option byte) a, (forall x, m' x = m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview. rewrite (lit_mb_ext H m m' a E). reflexivity. Qed.
Lemma lit_vm_ext : forall H (m m' : word -> option byte) a n v, (forall x, m' x = m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros H m m' a n v E V k Hk. rewrite (lit_mb_ext H m m' _ E). exact (V k Hk). Qed.
Lemma lit_ga_ext : forall H (m m' : word -> option byte) a l, (forall x, m' x = m x) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof. intros H m m' a l E V j Hj. destruct (V j Hj) as [V1 V2]. split; [exact (lit_vm_ext H m m' _ _ _ E V1) | exact V2]. Qed.
Lemma lit_rd_ext : forall H (m m' : word -> option byte) a, (forall x, m' x = m x) ->
  rdword (aview SEGS H m') a = rdword (aview SEGS H m) a.
Proof. intros H m m' a E. unfold rdword. rewrite !(lit_av_ext H m m' _ E). reflexivity. Qed.
Lemma lit_sb_ext : forall c (m m' : word -> option byte) b q cap cs ov, (forall x, m' x = m x) ->
  rbn_sb c m b q cap cs ov -> rbn_sb c m' b q cap cs ov.
Proof.
intros c m m' b q cap cs ov E (V1 & V2 & V3 & V4 & H5 & H6 & H7 & G8). unfold x_mem_at in *.
split; [exact (lit_vm_ext _ m m' _ _ _ E V1)|]. split; [exact (lit_vm_ext _ m m' _ _ _ E V2)|].
split; [exact (lit_vm_ext _ m m' _ _ _ E V3)|]. split; [exact (lit_vm_ext _ m m' _ _ _ E V4)|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. exact (lit_ga_ext _ m m' _ _ E G8).
Qed.

Definition lit_keep : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 22%bv; 23%bv; 25%bv; 26%bv; 27%bv].

Lemma rbn_lit_move : forall c lyc Sc memc mdc regs st memc' mdc' regs',
  rbn_lit c lyc Sc memc mdc regs st -> (forall x, memc' x = memc x) ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) memc' mdc' 0 ->
  (forall r, In r lit_keep -> getr regs' r = getr regs r) ->
  rbn_lit c lyc Sc memc' mdc' regs' st.
Proof.
intros c lyc Sc memc mdc regs st memc' mdc' regs' HL E HJ' HR.
destruct HL as ((Hcore & Hargs & Hbk & Hsl & R22) & (W1 & W2 & W3) & (N1 & N2 & N3) & (T1 & T2 & T3) & Hsc & Hdb).
destruct Hcore as (Hpre & _ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsaved & Hflag).
assert (Gk : forall r, In r lit_keep -> forall v, getr regs r = v -> getr regs' r = v) by (intros r Hr v Hv; rewrite HR by exact Hr; exact Hv).
unfold rbn_lit, rbn_live, rbn_core, rbn_w4done, rbn_nmdone, rbn_tkdone.
split; [split; [|split; [exact Hargs|split; [|split; [|]]]]|split; [split; [|split; [|]]|split; [split; [|split; [|]]|split; [split; [|split; [|]]|split; [|]]]]].
- split; [exact Hpre|]. split; [exact HJ'|]. split; [exact Hperm|].
  split; [apply Gk; [cbn; tauto | exact R2]|]. split; [apply Gk; [cbn; tauto | exact R3]|].
  split; [apply Gk; [cbn; tauto | exact R4]|]. split; [apply Gk; [cbn; tauto | exact R8]|].
  split; [apply Gk; [cbn; tauto | exact R9]|]. split; [apply Gk; [cbn; tauto | exact R18]|].
  split; [apply Gk; [cbn; tauto | exact R19]|]. split; [apply Gk; [cbn; tauto | exact R23]|].
  split.
  + unfold rbn_saved in *. eapply Forall_impl; [|exact Hsaved]. intros p Hp. unfold x_mem_at in *. exact (lit_vm_ext _ memc memc' _ _ _ E Hp).
  + rewrite (lit_rd_ext _ memc memc' _ E). exact Hflag.
- intros a Ha Hb. rewrite (lit_av_ext _ memc memc' _ E). exact (Hbk a Ha Hb).
- unfold rbn_slots, x_mem_at in *. destruct Hsl as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  repeat split; eapply lit_vm_ext; eassumption.
- apply Gk; [cbn; tauto | exact R22].
- exact (lit_sb_ext c memc memc' _ _ _ _ _ E W1).
- unfold x_mem_at in *. exact (lit_ga_ext _ memc memc' _ _ E W2).
- apply Gk; [cbn; tauto | exact W3].
- exact (lit_sb_ext c memc memc' _ _ _ _ _ E N1).
- unfold x_mem_at in *. exact (lit_ga_ext _ memc memc' _ _ E N2).
- apply Gk; [cbn; tauto | exact N3].
- exact (lit_sb_ext c memc memc' _ _ _ _ _ E T1).
- unfold x_mem_at in *. exact (lit_ga_ext _ memc memc' _ _ E T2).
- apply Gk; [cbn; tauto | exact T3].
- unfold rbn_scope in *. destruct Hsc as (C1 & C2 & C3 & C4).
  split; [rewrite (lit_av_ext _ memc memc' _ E); exact C1|].
  split; [intros jj Hjj; rewrite (lit_av_ext _ memc memc' _ E); exact (C2 jj Hjj)|].
  split; [intros jj Hjj; rewrite (lit_av_ext _ memc memc' _ E); exact (C3 jj Hjj)|].
  intros jj Hjj; rewrite (lit_av_ext _ memc memc' _ E); exact (C4 jj Hjj).
- exact (lit_sb_ext c memc memc' _ _ _ _ _ E Hdb).
Qed.

Lemma lit_frame_nowin : forall E pc pin o j ch z slo shi (m m' : word -> option byte),
  frame_of E (ss_mem (lit_ss pc pin o j ch z slo shi)) m m' -> forall x, m' x = m x.
Proof.
intros E pc pin o j ch z slo shi m m' HF x. apply HF. intros (r & Hin & Hr).
cbn [lit_ss ss_mem In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_wlo YP09.r_whi lit_rS lit_rC lit_rW] in Hr; lia.
Qed.

Lemma lit_E_reg : forall regs o sh xi xo (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (lit_E regs o sh xi xo) n = getr regs r.
Proof.
intros regs o sh xi xo n r Hn. unfold lit_E. rewrite Eimg_low.
- apply ew_Ereg_nat. exact Hn.
- pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold A_TEXT. lia.
Qed.

Lemma lit_E_img : forall regs o sh xi xo (n : nat), (A_TEXT <= n < A_LIM)%nat ->
  ew (lit_E regs o sh xi xo) n = Z_to_bv 64 (VAL n).
Proof. intros regs o sh xi xo n Hn. unfold lit_E. apply Eimg_img. exact Hn. Qed.
Lemma lit_E_agree : forall regs o sh xi xo,
  env_agree 32 (Ereg regs (map (Z_to_bv 64) [VAL o / 8; sh; xi; xo])) (lit_E regs o sh xi xo).
Proof. intros. split; [intros n Hn; unfold lit_E; rewrite Eimg_low; [reflexivity | unfold A_TEXT; lia] | reflexivity]. Qed.
Lemma lit_reg_soff : forall regs o sh xi xo (n : nat) (r : bv 5) v z, Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (ew (lit_E regs o sh xi xo) n) + z) = w64 (v + z).
Proof. intros regs o sh xi xo n r v z Hn Hr Hv. rewrite (lit_E_reg regs o sh xi xo n r Hn), Hr. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma lit_reg_img : forall regs o sh xi xo (n : nat) z, (A_TEXT <= n < A_LIM)%nat ->
  Z_to_bv 64 (bv_unsigned (ew (lit_E regs o sh xi xo) n) + z) = w64 (VAL n + z).
Proof. intros regs o sh xi xo n z Hn. rewrite lit_E_img by exact Hn. unfold w64. rewrite unsigned_lit_small by apply pa_val_range. reflexivity. Qed.

Definition lit_setup (k : nat) : Z := match k with O => 0x568 | S O => 0x5c4 | _ => 0x620 end.
Definition lit_ret (k : nat) : Z := match k with O => 0x598 | S O => 0x5f4 | _ => 0x650 end.
Definition lit_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma lit_shadow_cases : forall c lyc Sc memc mdc regs st k, rbn_lit c lyc Sc memc mdc regs st -> (k < 3)%nat ->
  exists sh z slo shi, aview SEGS (w_H (x_W c)) memc (SHADOW_OFF + VAL (lit_O k) / 8) = Some sh /\ slo <= sh <= shi /\
    (z = true -> sh = 0) /\ ((z = true /\ slo = 0 /\ shi = 0) \/ (z = false /\ slo = lit_n k + 1 /\ shi = 7)).
Proof.
intros c lyc Sc memc mdc regs st k HL Hk.
destruct (lit_shadow c lyc Sc memc mdc regs st k HL Hk) as (sh & Hsh & [-> | Hr]).
- exists 0, true, 0, 0. split; [exact Hsh | split; [lia | split; [reflexivity | left; repeat split]]].
- exists sh, false, (lit_n k + 1), 7. split; [exact Hsh | split; [lia | split; [discriminate | right; repeat split]]].
Qed.


Definition lit_start (k : nat) (j : Z) : Z := if j =? 0 then lit_setup k else lit_ret k.
Definition lit_pinv (k : nat) (j : Z) : option (Z * nat * Z) := if j =? 0 then None else Some (j - 1, lit_O k, lit_n k).
Lemma lit_pinv_ok : forall k j (regs : bvmap 5 word), 0 <= j ->
  (0 < j -> getr regs 20 = w64 (j - 1) /\ getr regs 21 = w64 (VAL (lit_O k)) /\ getr regs 24 = w64 (lit_n k)) ->
  match lit_pinv k j with
  | Some (j4, o, n8) => o = lit_O k /\ getr regs 20 = w64 j4 /\ getr regs 21 = w64 (VAL o) /\ getr regs 24 = w64 n8
  | None => True
  end.
Proof.
intros k j regs Hj H. unfold lit_pinv. destruct (Z.eqb_spec j 0) as [_|Hn]; [exact I|].
destruct (H ltac:(lia)) as (A & B' & C'). split; [reflexivity | split; [exact A | split; [exact B' | exact C']]].
Qed.

Ltac lit_after_run_call HS HF HM HKR :=
  lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awr_ok_tac | _ =>
  pmkst HS;
  lazymatch type of HS with st_ok _ ?E _ _ => pose proof (lit_frame_nowin E _ _ _ _ _ _ _ _ _ _ HF) as HM end;
  lazymatch type of HS with st_ok _ (lit_E ?rg ?o ?sh ?xi ?xo) _ _ =>
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rg _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 23%bv; 25%bv; 26%bv; 27%bv] HS
      (lit_E_agree rg o sh xi xo) ltac:(vm_compute; reflexivity)) as HKR end;
  cbn [ms_regs restrict] in HKR
  end.

Lemma lit_run_ch : forall (k : nat) j c lyc Sc memc mdc regs st Q,
  (k < 3)%nat -> 0 <= j < lit_n k ->
  rbn_lit c lyc Sc memc mdc regs st ->
  (0 < j -> getr regs 20 = w64 (j - 1) /\ getr regs 21 = w64 (VAL (lit_O k)) /\ getr regs 24 = w64 (lit_n k)) ->
  (forall regs1 memc1 mdc1,
     rbn_lit c lyc Sc memc1 mdc1 regs1 st ->
     getr regs1 1 = Z_to_bv 64 (BASE + (AF_reac_box_name + lit_ret k)) ->
     getr regs1 10 = w64 (x_db c) -> getr regs1 11 = w64 (nth (Z.to_nat j) (lit_s k) 0) ->
     getr regs1 20 = w64 j -> getr regs1 21 = w64 (VAL (lit_O k)) -> getr regs1 24 = w64 (lit_n k) ->
     SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_sb_ch) regs1 memc1 mdc1) Q) ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + lit_start k j))) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros k j c lyc Sc memc mdc regs st Q Hk Hj HL Hpin HK.
pose proof (lit_pinv_ok k j regs ltac:(lia) Hpin) as Hpv. clear Hpin.
pose proof HL as ((_ & _ & _ & _ & R22) & _).
pose proof (lit_stack c lyc Sc memc mdc regs st HL) as (_ & Sce & S47 & Sa & Sb & _ & C0).
pose proof HL as (((_ & _ & _ & _ & _ & _ & _ & R9 & _) & _) & _).
pose proof HL as (((_ & HJ & _) & _) & _).
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + lit_start k j))) memc (seg_rom SEGS))) in HJ.
destruct (lit_shadow_cases c lyc Sc memc mdc regs st k HL Hk) as (sh & z & slo & shi & Hsh & Hr & Hz & HZ).
pose proof (lit_entry c lyc Sc memc mdc regs st k j (lit_pinv k j) (AF_reac_box_name + lit_start k j) sh z slo shi
  HL Hk ltac:(lia) Hsh Hr Hz Hpv) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (lit_E regs (lit_O k) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64))
  (mrestrict (w_H (x_W c)) memc)) by constructor.
pose proof (Eimg_env (Ereg regs (map (Z_to_bv 64) [VAL (lit_O k) / 8; sh; x_i c mod 2 ^ 64; x_o c mod 2 ^ 64]))) as HEI.
fold (lit_E regs (lit_O k) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64)) in HEI.
clear Hpv Hr Hz Hsh.
destruct (lit_n_cases k Hk) as [(-> & En) | [(-> & En) | (-> & En)]]; rewrite En in Hj;
  [assert (Jc : j = 0 \/ j = 1) by lia
  | assert (Jc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia
  | assert (Jc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia];
  repeat (destruct Jc as [-> | Jc]; [|]); try (subst j);
  destruct HZ as [(-> & -> & ->) | (-> & -> & ->)].
all: paj_run_to_tok RUNTO HS HJ SHOK lit_Bspan (AF_reac_box_name + 0x66c).
all: lit_after_run_call HS HF HM HKR.
all: lazymatch goal with |- SRr _ _ _ _ =>
  rewrite (PSIG IB_sb_ch AF_sb_ch eq_refl);
  prreg HS (1%bv : bv 5) Rra; prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (20%bv : bv 5) R20';
  prreg HS (21%bv : bv 5) R21'; prreg HS (22%bv : bv 5) R22'; prreg HS (24%bv : bv 5) R24';
  apply HK; [ eapply rbn_lit_move; [exact HL | exact HM | exact HJ |];
      let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; unfold lit_keep in Hr;
      repeat (destruct Hr as [<- | Hr]; [first [apply HKR; cbn; tauto | rewrite R22', R22; reflexivity] |]); destruct Hr
  | rewrite Rra; reflexivity
  | rewrite Ra0, (lit_reg_soff _ _ _ _ _ 9 9%bv (x_s1 c) 88 eq_refl R9 ltac:(lia)); reflexivity
  | rewrite Ra1; reflexivity
  | rewrite R20'; reflexivity
  | rewrite R21', lit_E_img by (cbv; lia); reflexivity
  | rewrite R24'; reflexivity ] end.
Qed.

Definition lit_dret (d : nat) : Z := match d with O => 0x5c4 | _ => 0x620 end.
Definition lit_v (c : rbx) (d : nat) : Z := match d with O => x_i c | _ => x_o c end.
Lemma lit_mod64 : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zmod_mod. Qed.
Lemma lit_E_extra : forall regs o sh xi xo,
  ew (lit_E regs o sh xi xo) 34 = Z_to_bv 64 xi /\ ew (lit_E regs o sh xi xo) 35 = Z_to_bv 64 xo.
Proof.
intros. unfold lit_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs _ 2) | exact (ew_Ereg_extra regs _ 3)].
Qed.

Lemma lit_run_dec : forall (d : nat) c lyc Sc memc mdc regs st Q,
  (d < 2)%nat -> rbn_lit c lyc Sc memc mdc regs st ->
  getr regs 20 = w64 (lit_n d - 1) -> getr regs 21 = w64 (VAL (lit_O d)) -> getr regs 24 = w64 (lit_n d) ->
  (forall regs1 memc1 mdc1,
     rbn_lit c lyc Sc memc1 mdc1 regs1 st ->
     getr regs1 1 = Z_to_bv 64 (BASE + (AF_reac_box_name + lit_dret d)) ->
     getr regs1 10 = w64 (x_db c) -> getr regs1 11 = w64 (lit_v c d) -> getr regs1 12 = w64 1 ->
     SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_sb_dec) regs1 memc1 mdc1) Q) ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + lit_ret d))) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros d c lyc Sc memc mdc regs st Q Hd HL P20 P21 P24 HK.
assert (Hk : (d < 3)%nat) by lia.
assert (Hpv : match lit_pinv d (lit_n d) with
  | Some (j4, o, n8) => o = lit_O d /\ getr regs 20 = w64 j4 /\ getr regs 21 = w64 (VAL o) /\ getr regs 24 = w64 n8
  | None => True end).
{ apply lit_pinv_ok; [destruct (lit_n_cases d Hk) as [(_ & ->) | [(_ & ->) | (_ & ->)]]; lia|].
  intros _. split; [exact P20 | split; [exact P21 | exact P24]]. }
pose proof HL as ((_ & _ & _ & _ & R22) & _).
pose proof (lit_stack c lyc Sc memc mdc regs st HL) as (_ & Sce & S47 & Sa & Sb & _ & C0).
pose proof HL as (((_ & _ & _ & _ & _ & _ & _ & R9 & _) & _) & _).
pose proof HL as (((_ & HJ & _) & _) & _).
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + lit_ret d))) memc (seg_rom SEGS))) in HJ.
destruct (lit_shadow_cases c lyc Sc memc mdc regs st d HL Hk) as (sh & z & slo & shi & Hsh & Hr & Hz & HZ).
pose proof (lit_entry c lyc Sc memc mdc regs st d (lit_n d) (lit_pinv d (lit_n d)) (AF_reac_box_name + lit_ret d) sh z slo shi
  HL Hk ltac:(destruct (lit_n_cases d Hk) as [(_ & ->) | [(_ & ->) | (_ & ->)]]; lia) Hsh Hr Hz Hpv) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (lit_E regs (lit_O d) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64))
  (mrestrict (w_H (x_W c)) memc)) by constructor.
pose proof (Eimg_env (Ereg regs (map (Z_to_bv 64) [VAL (lit_O d) / 8; sh; x_i c mod 2 ^ 64; x_o c mod 2 ^ 64]))) as HEI.
fold (lit_E regs (lit_O d) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64)) in HEI.
clear Hpv Hr Hz Hsh.
destruct d as [|[|d]]; [| |lia];
  destruct HZ as [(-> & -> & ->) | (-> & -> & ->)].
all: paj_run_to_tok RUNTO HS HJ SHOK lit_Bspan (AF_reac_box_name + 0x66c).
all: lit_after_run_call HS HF HM HKR.
all: lazymatch goal with |- SRr _ _ _ _ =>
  rewrite (PSIG IB_sb_dec AF_sb_dec eq_refl);
  prreg HS (1%bv : bv 5) Rra; prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
  prreg HS (22%bv : bv 5) R22';
  apply HK; [ eapply rbn_lit_move; [exact HL | exact HM | exact HJ |];
      let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; unfold lit_keep in Hr;
      repeat (destruct Hr as [<- | Hr]; [first [apply HKR; cbn; tauto | rewrite R22', R22; reflexivity] |]); destruct Hr
  | rewrite Rra; reflexivity
  | rewrite Ra0, (lit_reg_soff _ _ _ _ _ 9 9%bv (x_s1 c) 88 eq_refl R9 ltac:(lia)); reflexivity
  | rewrite Ra1; rewrite ?Z.add_0_r, ?(proj1 (lit_E_extra _ _ _ _ _)), ?(proj2 (lit_E_extra _ _ _ _ _)), ?Z_to_bv_bv_unsigned; apply lit_mod64
  | rewrite Ra2; reflexivity ] end.
Qed.

Lemma lit_run_end : forall c lyc Sc memc mdc regs st Q,
  rbn_lit c lyc Sc memc mdc regs st ->
  getr regs 20 = w64 4 -> getr regs 21 = w64 (VAL (lit_O 2)) -> getr regs 24 = w64 5 ->
  (forall regs1 memc1 mdc1, rbn_lit c lyc Sc memc1 mdc1 regs1 st ->
     SRr SEGS (x_W c) (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x66c))) memc1 (seg_rom SEGS)) mdc1) Q) ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + lit_ret 2))) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros c lyc Sc memc mdc regs st Q HL P20 P21 P24 HK.
assert (Hk : (2 < 3)%nat) by lia.
assert (Hpv : match lit_pinv 2 (lit_n 2) with
  | Some (j4, o, n8) => o = lit_O 2 /\ getr regs 20 = w64 j4 /\ getr regs 21 = w64 (VAL o) /\ getr regs 24 = w64 n8
  | None => True end).
{ apply lit_pinv_ok; [change (lit_n 2) with 5; lia|]. intros _. split; [exact P20 | split; [exact P21 | exact P24]]. }
pose proof HL as ((_ & _ & _ & _ & R22) & _).
pose proof HL as (((_ & HJ & _) & _) & _).
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + lit_ret 2))) memc (seg_rom SEGS))) in HJ.
destruct (lit_shadow_cases c lyc Sc memc mdc regs st 2 HL Hk) as (sh & z & slo & shi & Hsh & Hr & Hz & HZ).
pose proof (lit_entry c lyc Sc memc mdc regs st 2 (lit_n 2) (lit_pinv 2 (lit_n 2)) (AF_reac_box_name + lit_ret 2) sh z slo shi
  HL Hk ltac:(change (lit_n 2) with 5; lia) Hsh Hr Hz Hpv) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (lit_E regs (lit_O 2) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64))
  (mrestrict (w_H (x_W c)) memc)) by constructor.
pose proof (Eimg_env (Ereg regs (map (Z_to_bv 64) [VAL (lit_O 2) / 8; sh; x_i c mod 2 ^ 64; x_o c mod 2 ^ 64]))) as HEI.
fold (lit_E regs (lit_O 2) sh (x_i c mod 2 ^ 64) (x_o c mod 2 ^ 64)) in HEI.
clear Hpv Hr Hz Hsh.
destruct HZ as [(-> & -> & ->) | (-> & -> & ->)].
all: paj_run_to_tok RUNTO HS HJ SHOK lit_Bspan (AF_reac_box_name + 0x66c).
all: lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awr_ok_tac | _ => idtac end.
all: pmkst HS.
all: lazymatch type of HS with st_ok_pi _ _ ?E _ _ => pose proof (lit_frame_nowin E _ _ _ _ _ _ _ _ _ _ HF) as HM end.
all: lazymatch type of HS with st_ok_pi _ _ (lit_E ?rg ?o ?sh ?xi ?xo) _ _ =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ rg _ [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 23%bv; 25%bv; 26%bv; 27%bv] HS
      (lit_E_agree rg o sh xi xo) ltac:(vm_compute; reflexivity)) as HKR end.
all: cbn [ms_regs restrict] in HKR.
all: prreg HS (22%bv : bv 5) R22'.
all: apply HK; eapply rbn_lit_move; [exact HL | exact HM | exact HJ |];
      let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; unfold lit_keep in Hr;
      repeat (destruct Hr as [<- | Hr]; [first [apply HKR; cbn; tauto | rewrite R22', R22; reflexivity] |]); destruct Hr.
Qed.

Lemma lit_s_range : forall k j, 0 <= nth j (lit_s k) 0 < 256.
Proof.
intros k j. destruct k as [|[|k]]; (destruct j as [|[|[|[|[|[|j]]]]]]; cbn [lit_s nth]; [lia..| destruct j; lia]).
Qed.
Lemma lit_ret_ok : forall k, 0 <= AF_reac_box_name + lit_ret k < 2 ^ 40 /\ (AF_reac_box_name + lit_ret k) mod 2 = 0.
Proof. intros k. destruct k as [|[|k]]; cbn [lit_ret]; unfold AF_reac_box_name; split; [lia | reflexivity | lia | reflexivity | lia | reflexivity]. Qed.
Lemma lit_dret_ok : forall d, 0 <= AF_reac_box_name + lit_dret d < 2 ^ 40 /\ (AF_reac_box_name + lit_dret d) mod 2 = 0.
Proof. intros d. destruct d as [|d]; cbn [lit_dret]; unfold AF_reac_box_name; split; [lia | reflexivity | lia | reflexivity]. Qed.
Lemma lit_pres : forall (regs regs2 : bvmap 5 word) (r : bv 5) v, aregs_preserved regs regs2 ->
  acallee_saved (bv_unsigned r) -> getr regs r = v -> getr regs2 r = v.
Proof. intros regs regs2 r v HP Hr Hv. rewrite <- Hv. pose proof (HP _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.

Lemma lit_cs : forall (r : bv 5), r = 20%bv \/ r = 21%bv \/ r = 24%bv -> acallee_saved (bv_unsigned r).
Proof.
intros r [-> | [-> | ->]]; unfold acallee_saved;
  [change (bv_unsigned (20%bv : bv 5)) with 20 | change (bv_unsigned (21%bv : bv 5)) with 21 | change (bv_unsigned (24%bv : bv 5)) with 24]; lia.
Qed.


Lemma rbn_seg_c9_c10 : forall c lyc Sc memc mdc regs,
  rbn_C9 B G c lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x568)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x66c)) mem' (seg_rom SEGS)) md' /\
       rbn_C10 B G c lyc' Sc' mem' md' regs').
Proof.
intros c lyc Sc memc mdc regs HC9.
assert (HLc : rbn_lit c lyc Sc memc mdc regs (sbm_str 48 ([], 0) (x_nmc c))) by exact HC9.
clear HC9. rewrite <- Z.add_assoc.
eapply (lit_run_ch 0 0); [lia | change (lit_n 0) with 2; lia | exact HLc | intros Hc; lia | intros rg0 mm0 md0 HLr0 Rra0 Ra00 Ra10 R200 R210 R240].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 0)); [exact HLr0 | exact Rra0 | apply lit_ret_ok | apply lit_ret_ok | exact Ra00 | exact Ra10 | apply lit_s_range | ].
intros ly0 S0 rg0' mm0' md0' Hp0 HL0.
eapply (lit_run_ch 0 1); [lia | change (lit_n 0) with 2; lia | exact HL0 | intros _; split; [|split]; eapply lit_pres; [exact Hp0 | apply lit_cs; auto | exact R200 | exact Hp0 | apply lit_cs; auto | exact R210 | exact Hp0 | apply lit_cs; auto | exact R240] | intros rg1 mm1 md1 HLr1 Rra1 Ra01 Ra11 R201 R211 R241].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 0)); [exact HLr1 | exact Rra1 | apply lit_ret_ok | apply lit_ret_ok | exact Ra01 | exact Ra11 | apply lit_s_range | ].
intros ly1 S1 rg1' mm1' md1' Hp1 HL1.
eapply (lit_run_dec 0); [lia | exact HL1 | eapply lit_pres; [exact Hp1 | apply lit_cs; auto | exact R201] | eapply lit_pres; [exact Hp1 | apply lit_cs; auto | exact R211] | eapply lit_pres; [exact Hp1 | apply lit_cs; auto | exact R241] | intros rg2 mm2 md2 HLr2 Rra2 Ra02 Ra12 Ra22].
eapply (rbn_lit_call_dec c _ _ _ _ _ _ _ (AF_reac_box_name + lit_dret 0)); [exact HLr2 | exact Rra2 | apply lit_dret_ok | apply lit_dret_ok | exact Ra02 | exact Ra12 | exact Ra22 | left; reflexivity | ].
intros ly2 S2 rg2' mm2' md2' Hp2 HL2.
eapply (lit_run_ch 1 0); [lia | change (lit_n 1) with 6; lia | exact HL2 | intros Hc; lia | intros rg3 mm3 md3 HLr3 Rra3 Ra03 Ra13 R203 R213 R243].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 1)); [exact HLr3 | exact Rra3 | apply lit_ret_ok | apply lit_ret_ok | exact Ra03 | exact Ra13 | apply lit_s_range | ].
intros ly3 S3 rg3' mm3' md3' Hp3 HL3.
eapply (lit_run_ch 1 1); [lia | change (lit_n 1) with 6; lia | exact HL3 | intros _; split; [|split]; eapply lit_pres; [exact Hp3 | apply lit_cs; auto | exact R203 | exact Hp3 | apply lit_cs; auto | exact R213 | exact Hp3 | apply lit_cs; auto | exact R243] | intros rg4 mm4 md4 HLr4 Rra4 Ra04 Ra14 R204 R214 R244].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 1)); [exact HLr4 | exact Rra4 | apply lit_ret_ok | apply lit_ret_ok | exact Ra04 | exact Ra14 | apply lit_s_range | ].
intros ly4 S4 rg4' mm4' md4' Hp4 HL4.
eapply (lit_run_ch 1 2); [lia | change (lit_n 1) with 6; lia | exact HL4 | intros _; split; [|split]; eapply lit_pres; [exact Hp4 | apply lit_cs; auto | exact R204 | exact Hp4 | apply lit_cs; auto | exact R214 | exact Hp4 | apply lit_cs; auto | exact R244] | intros rg5 mm5 md5 HLr5 Rra5 Ra05 Ra15 R205 R215 R245].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 1)); [exact HLr5 | exact Rra5 | apply lit_ret_ok | apply lit_ret_ok | exact Ra05 | exact Ra15 | apply lit_s_range | ].
intros ly5 S5 rg5' mm5' md5' Hp5 HL5.
eapply (lit_run_ch 1 3); [lia | change (lit_n 1) with 6; lia | exact HL5 | intros _; split; [|split]; eapply lit_pres; [exact Hp5 | apply lit_cs; auto | exact R205 | exact Hp5 | apply lit_cs; auto | exact R215 | exact Hp5 | apply lit_cs; auto | exact R245] | intros rg6 mm6 md6 HLr6 Rra6 Ra06 Ra16 R206 R216 R246].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 1)); [exact HLr6 | exact Rra6 | apply lit_ret_ok | apply lit_ret_ok | exact Ra06 | exact Ra16 | apply lit_s_range | ].
intros ly6 S6 rg6' mm6' md6' Hp6 HL6.
eapply (lit_run_ch 1 4); [lia | change (lit_n 1) with 6; lia | exact HL6 | intros _; split; [|split]; eapply lit_pres; [exact Hp6 | apply lit_cs; auto | exact R206 | exact Hp6 | apply lit_cs; auto | exact R216 | exact Hp6 | apply lit_cs; auto | exact R246] | intros rg7 mm7 md7 HLr7 Rra7 Ra07 Ra17 R207 R217 R247].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 1)); [exact HLr7 | exact Rra7 | apply lit_ret_ok | apply lit_ret_ok | exact Ra07 | exact Ra17 | apply lit_s_range | ].
intros ly7 S7 rg7' mm7' md7' Hp7 HL7.
eapply (lit_run_ch 1 5); [lia | change (lit_n 1) with 6; lia | exact HL7 | intros _; split; [|split]; eapply lit_pres; [exact Hp7 | apply lit_cs; auto | exact R207 | exact Hp7 | apply lit_cs; auto | exact R217 | exact Hp7 | apply lit_cs; auto | exact R247] | intros rg8 mm8 md8 HLr8 Rra8 Ra08 Ra18 R208 R218 R248].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 1)); [exact HLr8 | exact Rra8 | apply lit_ret_ok | apply lit_ret_ok | exact Ra08 | exact Ra18 | apply lit_s_range | ].
intros ly8 S8 rg8' mm8' md8' Hp8 HL8.
eapply (lit_run_dec 1); [lia | exact HL8 | eapply lit_pres; [exact Hp8 | apply lit_cs; auto | exact R208] | eapply lit_pres; [exact Hp8 | apply lit_cs; auto | exact R218] | eapply lit_pres; [exact Hp8 | apply lit_cs; auto | exact R248] | intros rg9 mm9 md9 HLr9 Rra9 Ra09 Ra19 Ra29].
eapply (rbn_lit_call_dec c _ _ _ _ _ _ _ (AF_reac_box_name + lit_dret 1)); [exact HLr9 | exact Rra9 | apply lit_dret_ok | apply lit_dret_ok | exact Ra09 | exact Ra19 | exact Ra29 | right; reflexivity | ].
intros ly9 S9 rg9' mm9' md9' Hp9 HL9.
eapply (lit_run_ch 2 0); [lia | change (lit_n 2) with 5; lia | exact HL9 | intros Hc; lia | intros rg10 mm10 md10 HLr10 Rra10 Ra010 Ra110 R2010 R2110 R2410].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 2)); [exact HLr10 | exact Rra10 | apply lit_ret_ok | apply lit_ret_ok | exact Ra010 | exact Ra110 | apply lit_s_range | ].
intros ly10 S10 rg10' mm10' md10' Hp10 HL10.
eapply (lit_run_ch 2 1); [lia | change (lit_n 2) with 5; lia | exact HL10 | intros _; split; [|split]; eapply lit_pres; [exact Hp10 | apply lit_cs; auto | exact R2010 | exact Hp10 | apply lit_cs; auto | exact R2110 | exact Hp10 | apply lit_cs; auto | exact R2410] | intros rg11 mm11 md11 HLr11 Rra11 Ra011 Ra111 R2011 R2111 R2411].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 2)); [exact HLr11 | exact Rra11 | apply lit_ret_ok | apply lit_ret_ok | exact Ra011 | exact Ra111 | apply lit_s_range | ].
intros ly11 S11 rg11' mm11' md11' Hp11 HL11.
eapply (lit_run_ch 2 2); [lia | change (lit_n 2) with 5; lia | exact HL11 | intros _; split; [|split]; eapply lit_pres; [exact Hp11 | apply lit_cs; auto | exact R2011 | exact Hp11 | apply lit_cs; auto | exact R2111 | exact Hp11 | apply lit_cs; auto | exact R2411] | intros rg12 mm12 md12 HLr12 Rra12 Ra012 Ra112 R2012 R2112 R2412].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 2)); [exact HLr12 | exact Rra12 | apply lit_ret_ok | apply lit_ret_ok | exact Ra012 | exact Ra112 | apply lit_s_range | ].
intros ly12 S12 rg12' mm12' md12' Hp12 HL12.
eapply (lit_run_ch 2 3); [lia | change (lit_n 2) with 5; lia | exact HL12 | intros _; split; [|split]; eapply lit_pres; [exact Hp12 | apply lit_cs; auto | exact R2012 | exact Hp12 | apply lit_cs; auto | exact R2112 | exact Hp12 | apply lit_cs; auto | exact R2412] | intros rg13 mm13 md13 HLr13 Rra13 Ra013 Ra113 R2013 R2113 R2413].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 2)); [exact HLr13 | exact Rra13 | apply lit_ret_ok | apply lit_ret_ok | exact Ra013 | exact Ra113 | apply lit_s_range | ].
intros ly13 S13 rg13' mm13' md13' Hp13 HL13.
eapply (lit_run_ch 2 4); [lia | change (lit_n 2) with 5; lia | exact HL13 | intros _; split; [|split]; eapply lit_pres; [exact Hp13 | apply lit_cs; auto | exact R2013 | exact Hp13 | apply lit_cs; auto | exact R2113 | exact Hp13 | apply lit_cs; auto | exact R2413] | intros rg14 mm14 md14 HLr14 Rra14 Ra014 Ra114 R2014 R2114 R2414].
eapply (rbn_lit_call_ch c _ _ _ _ _ _ _ (AF_reac_box_name + lit_ret 2)); [exact HLr14 | exact Rra14 | apply lit_ret_ok | apply lit_ret_ok | exact Ra014 | exact Ra114 | apply lit_s_range | ].
intros ly14 S14 rg14' mm14' md14' Hp14 HL14.
eapply lit_run_end; [exact HL14 | eapply lit_pres; [exact Hp14 | apply lit_cs; auto | exact R2014]
  | eapply lit_pres; [exact Hp14 | apply lit_cs; auto | exact R2114] | eapply lit_pres; [exact Hp14 | apply lit_cs; auto | exact R2414] | ].
intros rgF mmF mdF HLF.
apply SRr_ret. split; [reflexivity|]. eexists _, _, rgF, mmF, mdF. split; [rewrite <- Z.add_assoc; reflexivity|].
exact HLF.
Qed.

End walk.
End h.
End f.
End d.
