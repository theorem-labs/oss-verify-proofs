(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, image B's (fuzz_reply.asan-ubsan) block `reset` of SEG_EXIT:
   0x84fe8 (`ld a0,208(s1); jal check_shape_done`) through the loop set-up 0x84ff0..0x85000 (g_s = 0x5d8e60 in s3,
   g_s + 384 in s2, s4 = F+80 = FF, s8 = F+96 = SB + FF/8) and the four trips of `mv a0,s3; jal source_reset;
   addi s3,s3,96; bne s3,s2` (0x85004..0x85010) to 0x85014; lib/B/W_bx_defs.v lx_reset_S.  Ported from the image-A
   donor b86949b953d lib/A/W_LLVMFuzzerTestOneInput_exit.v:5898-7419 (xr_* kit, xr_at_entry,
   xr_entry0, the loop, xr_set_entry, lx_reset).  B vs A: the frame is bx_frame (no F+152) on both sides; the set-up
   loads no s7 (A's `ld s7,88(s1)`), so the loop invariant and the post carry x20 and x24 only; source_reset's spec
   takes `HA mod 8 = 0`; gx_rt's shadow cell is A_OBJ 30; ablocks_sep's footprint clause is over req_size; g_s's image
   atom, the return offsets and the image range [0x10000, 0x5fc000) are B's (the objdump of fuzz_reply.asan-ubsan,
   sha256 10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c, lib/B/W_rep.v fr_globals_b,
   lib/B/W_kit.v pa_img_range). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_shadow_pin W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_bx_defs.
(* RelocB's sink-instance guard, after every Import of YE2k: no sink class is a hint after it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section lx.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.
(* the hypotheses this block uses, each verbatim from lib/B/W_LLVMFuzzerTestOneInput_exit.v Section lx ... *)
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Hypothesis MLM : ameter_laws MT.
Hypothesis ERR : errno_law B.
Hypothesis AZS_s : azs B (rg_s fr_RG) (4 * ASRC).
Hypothesis CSD : csd_spec B (BASE + AF_fr_check_shape_done).
Hypothesis SR : sr_spec_g B MT (BASE + AF_fr_source_reset).
Hypothesis XRF_ROM_OUT : rom_out segs B G_fr.
Hypothesis XR_HGM : forall a, inG xr_GM a -> inG G_fr a.
Hypothesis XR_GSHV : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> rg_s fr_RG <= x < rg_s fr_RG + 4 * ASRC) ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
(* ... and the derived fact (the spine proves it from XR_HGM and XRF_ERRNO) *)
Hypothesis XR_ERRNO : forall a, inG xr_GM a -> ~ (as_errno B <= a < as_errno B + 4).

(* the symbolic-run scaffolding (the cut's) *)
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* ------------------------------------------------------------------ what a callee's journal keeps, byte by byte *)
Lemma xr_rom_img : forall a, in_rom segs a -> in_img segs a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.
(* a present byte is writable *)
Lemma xr_pres_wr : forall H (m : word -> option byte) a, apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
(* a writable byte off the image is present, so a reader sees it *)
Lemma xr_view_of_wr : forall H (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  writable_at segs (mrestrict H m) a -> aview segs H m a <> None.
Proof.
  intros H m a Ha Hni Hw. unfold aview, mbyte.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
  exfalso. unfold writable_at, wview in Hw. rewrite Em in Hw.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [sg|] eqn:Ef.
  - destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
    apply Hni. exists sg. split; [exact Hin | lia].
  - apply Hw. reflexivity.
Qed.
(* W_gestures_end.v gse_writable_view: a byte a reader sees, off the read-only segments, is writable *)
Lemma xr_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
  aview segs H m a = Some v -> ~ in_rom segs a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
  unfold seg_rom, memory_read in Hv.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
  change (Z.of_N 1) with 1 in Ef. rewrite Ef.
  destruct (seg_readable sg); [|discriminate].
  destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
  destruct (seg_writable sg) eqn:Ew.
  - destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
    exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
  - exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
(* a byte off the image whose view is the same is kept *)
Lemma xr_abyte_off : forall (W W' : world segs) m m' a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') m' a = aview segs (w_H W) m a -> abyte_kept W m W' m' a.
Proof.
  intros W W' m m' a Ha Hni He. split; [exact He|]. intros Hw. unfold arm in *.
  pose proof (xr_view_of_wr (w_H W) m a Ha Hni Hw) as Hv.
  destruct (aview segs (w_H W) m a) as [v|] eqn:Ev; [|exfalso; exact (Hv eq_refl)].
  exact (xr_writable_view (w_H W') m' a v Ha He (fun Hr => Hni (xr_rom_img a Hr))).
Qed.
(* W_cnl_step_scratch.v nls_awr_kept: a byte stays writable when it stays present *)
Lemma xr_awr_kept : forall (Wa Wb : world segs) (ma mb : word -> option byte) a,
  (apresent (w_H Wa) ma a -> apresent (w_H Wb) mb a) ->
  writable_at segs (arm Wa ma) a -> writable_at segs (arm Wb mb) a.
Proof.
  intros Wa Wb ma mb a Hp Hw. unfold writable_at, wview, arm, mrestrict in Hw |- *.
  destruct (w_H Wb (Z_to_bv 64 a)) eqn:EHb.
  - destruct (w_H Wa (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
    destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
    destruct (Hp (conj EHa (ex_intro _ b Ema))) as [Hh _]. rewrite EHb in Hh. discriminate.
  - destruct (mb (Z_to_bv 64 a)) as [b2|] eqn:Emb; [discriminate|].
    destruct (w_H Wa (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
    destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
    destruct (Hp (conj EHa (ex_intro _ b Ema))) as [_ [b3 Hb3]]. rewrite Emb in Hb3. discriminate.
Qed.
Lemma xr_abyte_img : forall (W W' : world segs) m m' a,
  aview segs (w_H W') m' a = aview segs (w_H W) m a ->
  (apresent (w_H W) m a -> apresent (w_H W') m' a) -> abyte_kept W m W' m' a.
Proof. intros W W' m m' a He Hp. split; [exact He | exact (xr_awr_kept W W' m m' a Hp)]. Qed.
Lemma xr_abyte_trans : forall (W1 W2 W3 : world segs) m1 m2 m3 a,
  abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof. intros W1 W2 W3 m1 m2 m3 a [E1 H1] [E2 H2]. split; [rewrite E2; exact E1 | intros Hw; exact (H2 (H1 Hw))]. Qed.

(* the journal's clauses, read through its start-memory overlay (W_gestures_end.v gse_keep_img / _high / _blk) *)
Lemma xr_jkeep_img : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx segs B Gc 0 [] STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  fp_spares FP a -> ~ inG Gc a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _) a Hi Ho He Hf Hg.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He Hf).
  pose proof (pa_segs_low a Hi) as HL.
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false.
  rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma xr_jkeep_high : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k,
  gx_ok segs B Gc -> ajournal_gx segs B Gc 0 [] STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _) a Ha Hno.
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
  pose proof asan_consts as (C1 & _).
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
  pose proof (inG_low segs B pa_segs_low Gc a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma xr_jkeep_blk : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i,
  gx_ok segs B Gc -> ajournal_gx segs B Gc 0 [] STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
  aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i).
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _) H1 H2 Hi Hf.
  pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
  apply (aview_gagree segs Gc _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
  destruct (al_blocks _ _ LAWS ly' S' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
  pose proof asan_consts as (C1 & _).
  rewrite unsigned_lit_small in HGa by lia.
  destruct (HGx _ HGa) as [Hi' _].
  pose proof (blk_off_imgP B ly' S' W' mem' md' p n HAR0 H2) as Hoff.
  (* B: lib/B/W_kit.v pa_img_range, [0x10000, 0x5fc000); blk_off_imgP's off_img is lib/B/YCbq.v's *)
  pose proof (pa_img_range _ Hi') as HR. red in Hoff. lia.
Qed.
Lemma xr_jkeep_frame : forall Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a,
  gx_ok segs B Gc -> ajournal_gx segs B Gc 0 [] STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros Gc STK sp FP ly S W mem md own ly' S' W' mem' md' k cid pos a HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
    Hin Hr Hf Ha Hni.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _). rewrite (F4 cid pos a Hin Hr Hf).
  apply (aview_gagree segs Gc _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia.
  intros HGa. exact (Hni (proj1 (HGx a HGa))).
Qed.
Lemma xr_blk_present : forall ly S (W : world segs) mem md p n a, AR segs B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> apresent (w_H W) mem a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & Hp & _). exact (proj1 (Hp a Ha)).
Qed.

(* ---- lists of blocks ---- *)
Lemma xr_pw_map : forall {X Y : Type} (f : X -> Y) (R : Y -> Y -> Prop), (forall a b, R a b -> R b a) ->
  forall l x y, pairwise R (map f l) -> In x l -> In y l -> x <> y -> R (f x) (f y).
Proof.
  intros X Y f R Hs l. induction l as [|z t IH]; intros x y Hp Hx Hy Hne; [destruct Hx|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. rewrite Forall_forall in Hf.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso; apply Hne; reflexivity.
  - apply Hf. apply in_map. exact Hy.
  - apply Hs. apply Hf. apply in_map. exact Hx.
  - exact (IH x y Hp Hx Hy Hne).
Qed.
Lemma xr_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y, pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1 l2 x y. induction l1 as [|z t IH]; intros Hp Hx Hy; [destruct Hx|].
  cbn [app pairwise] in Hp. destruct Hp as [Hf Hp]. rewrite Forall_forall in Hf.
  destruct Hx as [<-|Hx]; [apply Hf; apply in_or_app; right; exact Hy | exact (IH Hp Hx Hy)].
Qed.
Lemma xr_zd_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.
(* two different live blocks are apart *)
Lemma xr_blk_apart : forall ly S (W : world segs) mem md b1 b2, AR segs B ly S W mem md ->
  In b1 (ablocks B ly S) -> In b2 (ablocks B ly S) -> b1 <> b2 ->
  fst b1 + req_size (snd b1) <= fst b2 \/ fst b2 + req_size (snd b2) <= fst b1.
Proof.
  intros ly S W mem md b1 b2 HAR H1 H2 Hne.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  exact (xr_pw_map (fun b => (fst b, req_size (snd b))) zdisjoint xr_zd_sym _ b1 b2 Hp H1 H2 Hne).
Qed.
(* a live block and a fake frame are apart *)
Lemma xr_blk_frame_apart : forall ly S (W : world segs) mem md b cid pos, AR segs B ly S W mem md ->
  In b (ablocks B ly S) -> In (cid, pos) (frames S) ->
  fst b + req_size (snd b) <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= fst b.
Proof.
  intros ly S W mem md b cid pos HAR H1 H2.
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
  exact (xr_pw_app zdisjoint _ _ _ _ Hp (in_map (fun b => (fst b, req_size (snd b))) _ _ H1)
    (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ H2)).
Qed.
(* W_gestures_end.v gse_nodup *)
Lemma xr_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
  induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
  apply List.NoDup_cons; [|exact (IH Hp Hl)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
Lemma xr_nodup_app : forall {X : Type} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros X l1 l2 x. induction l1 as [|z t IH]; intros Hnd Hx; [destruct Hx|].
  inversion Hnd as [|? ? Hnz Hnd']; subst. destruct Hx as [<-|Hx].
  - intros Hy. apply Hnz. apply in_or_app. right. exact Hy.
  - exact (IH Hnd' Hx).
Qed.

(* ------------------------------------------------------------------ the model's footprints lie in its globals and blocks *)
Lemma xr_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma xr_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma xr_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, xr_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma xr_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.
(* the range r lies in one of the blocks BL *)
Definition xr_inblk (BL : list (Z * Z)) (r : Z * Z) : Prop :=
  exists b, In b BL /\ fst b <= fst r /\ snd r <= fst b + req_size (snd b).
(* split `In x (if t =? 0 then [] else [y])`: the empty case closes, the other leaves Ec : (t =? 0) = false *)
Ltac xr_ifz t H Ec := revert H; destruct (t =? 0) eqn:Ec; intros H; [destruct H|].
Lemma xr_alist_cov : forall ly S (W : world segs) mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall r, In r (alist_fp LA l) -> r = (LA, LA + 16) \/ xr_inblk (alist_blks l) r.
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) r Hr.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; reflexivity | right].
  apply in_app_or in Hr as [Hr | Hr].
  - xr_ifz (hl_cap l) Hr Ec. pose proof (proj1 (Z.eqb_neq _ _) Ec) as Hc. destruct Hr as [<- | []].
    exists (hl_v l, AREC * hl_cap l). split.
    + unfold alist_blks. rewrite Ec. apply in_or_app. left. left. reflexivity.
    + unfold gfp. cbn [fst snd].
      destruct H6 as [(Hc0 & _) | (Hc1 & _ & Hj & _)]; [lia|].
      rewrite xr_bzs_len, length_app, Nat2Z.inj_add, xr_concat_len.
      pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as [_ Hq].
      unfold hl_n, AREC in *. lia.
  - apply in_map_iff in Hr as (r0 & <- & Hr0). exists (fst r0, Z.of_nat (length (snd r0)) + 1). split.
    + unfold alist_blks. apply in_or_app. right.
      apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hr0.
    + unfold gfp. cbn [fst snd]. rewrite xr_bzs_len, length_app. cbn [length].
      pose proof (req_size_pos (Z.of_nat (length (snd r0)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xr_alist_live : forall ly S (W : world segs) mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - xr_ifz (hl_cap l) Hb Ec. pose proof (proj1 (Z.eqb_neq _ _) Ec) as Hc. destruct Hb as [<- | []].
    destruct H6 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in H9. exact (proj1 (H9 r Hr)).
Qed.
Lemma xr_asrc_cov : forall ly S (W : world segs) mem HA h, asrc_at B ly S W mem HA h ->
  forall r, In r (asrc_fp HA h) -> (HA <= fst r /\ snd r <= HA + ASRC) \/ xr_inblk (asrc_blks h) r.
Proof.
  intros ly S W mem HA h
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
     H21 & H22 & H23 & H24) r Hr.
  unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  - left. cbn [fst snd]. lia.
  - right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|]. unfold gfp. cbn [fst snd].
    rewrite xr_bzs_len. pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as [_ Hq]. lia.
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + destruct (xr_alist_cov _ _ _ _ _ _ _ H10 r Hr) as [-> | (b & Hb & Hlo & Hhi)];
        [left; cbn [fst snd]; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; left; exact Hb | lia].
    + destruct (xr_alist_cov _ _ _ _ _ _ _ H22 r Hr) as [-> | (b & Hb & Hlo & Hhi)];
        [left; cbn [fst snd]; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; right; apply in_or_app; left; exact Hb | lia].
    + destruct (xr_alist_cov _ _ _ _ _ _ _ H23 r Hr) as [-> | (b & Hb & Hlo & Hhi)];
        [left; cbn [fst snd]; unfold ASRC; lia|].
      right. exists b. split; [right; apply in_or_app; right; apply in_or_app; right; exact Hb | lia].
Qed.
Lemma xr_asrc_live : forall ly S (W : world segs) mem HA h, asrc_at B ly S W mem HA h ->
  forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
     H21 & H22 & H23 & H24) b Hb.
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xr_alist_live _ _ _ _ _ _ _ H10 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xr_alist_live _ _ _ _ _ _ _ H22 b Hb)|].
  exact (xr_alist_live _ _ _ _ _ _ _ H23 b Hb).
Qed.
Lemma xr_aentry_cov : forall ly S (W : world segs) mem e, aentry_ok B ly S W mem e ->
  forall r, In r (aentry_fp e) -> snd r <= fst r \/ xr_inblk (aentry_blks e) r.
Proof.
  intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | [<- | Hr]].
  - xr_ifz (re_cap e) Hr Ec. pose proof (proj1 (Z.eqb_neq _ _) Ec) as Hc. destruct Hr as [<- | []]. right.
    exists (re_buf e, re_cap e). split.
    + unfold aentry_blks. rewrite Ec. apply in_or_app. left. left. reflexivity.
    + unfold gfp. cbn [fst snd]. rewrite xr_bzs_len, length_app, Nat2Z.inj_add.
      destruct H10 as [(Hc0 & _) | (_ & _ & Hj & _)]; [lia|].
      pose proof (req_size_pos (re_cap e) ltac:(lia)) as [_ Hq]. lia.
  - destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    + left. unfold gfp. cbn [fst snd]. rewrite Hk. cbn. lia.
    + right. exists (re_hp e, re_kh e). split.
      * unfold aentry_blks. apply in_or_app. right. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) Hz). apply in_or_app. left.
        left. reflexivity.
      * unfold gfp. cbn [fst snd]. rewrite xr_bzs_len, xr_key_ptrs_len. unfold re_nheld in Hk1.
        pose proof (req_size_pos (re_kh e) ltac:(lia)) as [_ Hq]. lia.
  - apply in_map_iff in Hr as (kk & <- & Hk). right.
    exists (gestures_end_b_c.key_addr kk, Z.of_nat (length (gestures_end_b_c.key_text kk)) + 1). split.
    + unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (gestures_end_b_c.key_addr k, Z.of_nat (length (gestures_end_b_c.key_text k)) + 1))).
      exact Hk.
    + unfold gfp. cbn [fst snd]. rewrite xr_bzs_len, length_app. cbn [length].
      pose proof (req_size_pos (Z.of_nat (length (gestures_end_b_c.key_text kk)) + 1) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xr_aentry_live : forall ly S (W : world segs) mem e, aentry_ok B ly S W mem e ->
  forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
  - xr_ifz (re_cap e) Hb Ec. pose proof (proj1 (Z.eqb_neq _ _) Ec) as Hc. destruct Hb as [<- | []].
    destruct H10 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  - xr_ifz (re_hp e) Hb Ez. pose proof (proj1 (Z.eqb_neq _ _) Ez) as Hz. destruct Hb as [<- | []].
    destruct H12 as [(Hz0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  - apply in_map_iff in Hb as (kk & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 kk Hk)).
Qed.
Lemma xr_arelay_cov : forall ly S (W : world segs) mem G es, arelay_at B fr_RG ly S W mem G es ->
  forall r, In r (arelay_fp fr_RG G es) ->
    r = (rg_src fr_RG, rg_src fr_RG + 8) \/ r = (rg_nsrc fr_RG, rg_nsrc fr_RG + 4) \/
    r = (rg_capsrc fr_RG, rg_capsrc fr_RG + 4) \/ snd r <= fst r \/ xr_inblk (arelay_blks G es) r.
Proof.
  intros ly S W mem G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) r Hr.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]];
    [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | |].
  - right; right; right; right. exists (G, ATABLE). split; [left; reflexivity|]. cbn [fst snd].
    pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [_ Hq]. lia.
  - apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
    rewrite Forall_forall in H10.
    destruct (xr_aentry_cov ly S W mem e (H10 e He) r Hr) as [Hemp | (b & Hb & Hlo & Hhi)];
      [right; right; right; left; exact Hemp|].
    right; right; right; right. exists b. split; [|lia].
    right. apply in_concat. exists (aentry_blks e). split; [apply in_map; exact He | exact Hb].
Qed.
Lemma xr_arelay_live : forall ly S (W : world segs) mem G es, arelay_at B fr_RG ly S W mem G es ->
  forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem G es (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) b Hb.
  unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (bl & Hbl & Hb). apply in_map_iff in Hbl as (e & <- & He).
  rewrite Forall_forall in H10. exact (xr_aentry_live ly S W mem e (H10 e He) b Hb).
Qed.

(* ------------------------------------------------------------------ the bytes one call keeps
   Gc: the callee's globals; BLx: the blocks it frees; [lo, hi): the caller's frame above the callee's window;
   FF: the fake frame (128 bytes) and its 16 shadow bytes. *)
Definition xr_kb (Gc BLx : list (Z * Z)) (FF lo hi : Z) (ly1 : alayout) (S1 : astate) (W1 : world segs)
    (m1 : word -> option byte) (ly2 : alayout) (S2 : astate) (W2 : world segs) (m2 : word -> option byte) : Prop :=
  (forall a, inG xr_GM a -> ~ inG Gc a -> abyte_kept W1 m1 W2 m2 a) /\
  (forall b, In b (ablocks B ly1 S1) -> ~ In b BLx ->
     In b (ablocks B ly2 S2) /\ forall a, fst b <= a < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 a) /\
  (forall a, lo <= a < hi -> abyte_kept W1 m1 W2 m2 a) /\
  (forall a, FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W1 m1 W2 m2 a).
Lemma xr_akept_cov : forall Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 (BL fp : list (Z * Z)) (P : Z -> Prop),
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  (forall b, In b BL -> In b (ablocks B ly1 S1) /\ ~ In b BLx) ->
  (forall a, P a -> inG xr_GM a /\ ~ inG Gc a) ->
  (forall r, In r fp -> (forall a, fst r <= a < snd r -> P a) \/ snd r <= fst r \/ xr_inblk BL r) ->
  akept W1 m1 W2 m2 fp.
Proof.
  intros Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 BL fp P (K1 & K2 & _ & _) HBL HP Hcov r Hr a Ha.
  destruct (Hcov r Hr) as [HPr | [He | (b & Hb & Hlo & Hhi)]].
  - destruct (HP a (HPr a Ha)) as [Hg Hn]. exact (K1 a Hg Hn).
  - lia.
  - destruct (HBL b Hb) as [Hin Hn]. exact (proj2 (K2 b Hin Hn) a ltac:(lia)).
Qed.

(* concrete addresses of fuzz_reply.asan-ubsan's globals (lib/B/W_rep.v fr_globals_b, the cut's AG_NFD etc.) *)
Ltac xr_num := unfold AG_NFD, AG_THREAD_UP, AG_LISTEN, ASRC, fr_RG in *;
  cbn [fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *.
Ltac xr_inGM := unfold xr_GM;
  repeat (apply (proj2 (inG_cons _ _ _)); first [left; unfold in_zr; cbn [fst snd]; xr_num; lia | right]).
Lemma xr_gs_GM : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG xr_GM a.
Proof. intros a Ha. unfold xr_GM. apply (proj2 (inG_cons _ _ _)). left. unfold in_zr. cbn [fst snd]. lia. Qed.

(* W_gestures_end.v gse_fp_spares *)
Lemma xr_fp_spares : forall bl a, (forall b, In b bl -> 4096 <= fst b) -> fp_spares (ablocks_fp bl) a.
Proof.
  intros bl a Hb Ho. exfalso. destruct Ho as (r & Hr & H0).
  unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hin). cbn [fst snd] in H0. pose proof (Hb b Hin). lia.
Qed.
(* a callee at sp = F with globals Gc that frees the blocks BLx keeps the bundle: its journal (W2's image, block, high
   and frame clauses), the blocks it leaves, and the image bytes it leaves present *)
Lemma xr_kb_of_j : forall Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB,
  gx_ok segs B Gc ->
  ajournal_gx segs B Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk ->
  AR segs B ly1 S1 W1 m1 md1 ->
  Permutation (ablocks B ly1 S1) (BLx ++ restB) -> Permutation (ablocks B ly2 S2) restB ->
  apres_kept B W1 m1 W2 m2 ->
  0 <= STK -> alloc_ceiling <= F - STK -> F <= hi <= 2 ^ 64 ->
  In (1, fpos) (frames S1) -> FF = frame_addr ly1 1 fpos ->
  xr_kb Gc BLx FF F hi ly1 S1 W1 m1 ly2 S2 W2 m2.
Proof.
  intros Gc BLx STK F hi FF fpos ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 kk restB HGc HJ HAR1 HP1 HP2 HPRES HSTK HFlo HFhi
    Hfr HFF.
  pose proof (ajournal_gx_AR segs B Gc 0 [] STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HJ) as HAR2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HBL1 : forall b, In b BLx -> In b (ablocks B ly1 S1))
    by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HP1 | apply in_or_app; left; exact Hb]).
  assert (HFP : forall a, inFP (ablocks_fp BLx) a -> exists b, In b BLx /\ fst b <= a < fst b + req_size (snd b)).
  { intros a (r & Hr & Ha). unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb).
    exists b. split; [exact Hb|]. cbn [fst snd] in Ha. exact Ha. }
  split; [|split; [|split]].
  - intros a Hg Hn. pose proof (XR_HGM a Hg) as HgF. destruct (HG a HgF) as (Hi & Ho & _).
    pose proof (XR_ERRNO a Hg) as He.
    apply xr_abyte_img.
    + apply (xr_jkeep_img Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HJ a Hi Ho He); [|exact Hn].
      apply xr_fp_spares. intros [p n] Hb.
      destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p n HAR1 (HBL1 _ Hb)) as (_ & H4 & _). exact H4.
    + intros Hp. exact (HPRES a Hi Ho He Hp).
  - intros b Hb Hnb.
    assert (Hb2 : In b (ablocks B ly2 S2)).
    { eapply Permutation_in; [apply Permutation_sym; exact HP2|].
      pose proof (Permutation_in _ HP1 Hb) as H. apply in_app_or in H as [H|H]; [contradiction | exact H]. }
    split; [exact Hb2|]. intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
    split.
    + replace a with (p + (a - p)) by lia.
      apply (xr_jkeep_blk Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk p n (a - p) HGc HJ Hb Hb2);
        [lia|].
      replace (p + (a - p)) with a by lia. intros HF. destruct (HFP a HF) as (b' & Hb' & Ha').
      assert (Hne : (p, n) <> b') by (intros <-; exact (Hnb Hb')).
      destruct (xr_blk_apart ly1 S1 W1 m1 md1 (p, n) b' HAR1 Hb (HBL1 b' Hb') Hne) as [H|H]; cbn [fst snd] in H; lia.
    + intros _. unfold arm. apply xr_pres_wr. exact (xr_blk_present ly2 S2 W2 m2 md2 p n a HAR2 Hb2 Ha).
  - intros a Ha. apply xr_abyte_off; [lia | intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia |].
    apply (xr_jkeep_high Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk HGc HJ a); lia.
  - destruct (frames_bounds segs B LAWS ly1 S1 W1 m1 md1 1 fpos HAR1 Hfr) as (HF0 & HF1 & HFapp).
    replace (fs_frame_bytes 1) with 128 in HF1, HFapp by reflexivity. rewrite <- HFF in HF0, HF1, HFapp.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
    intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold SB in Ha; lia).
    assert (Hni : ~ in_img segs a).
    { intros Hi. destruct Ha as [Ha | Ha].
      - destruct (al_client_img _ _ LAWS ly1 S1 W1 m1 md1 a HAR1) as [_ Hn]; [|exact (Hn Hi)].
        right; left. exists 1, fpos. split; [exact Hfr|]. rewrite <- HFF. replace (fs_frame_bytes 1) with 128 by reflexivity.
        lia.
      - pose proof (pa_segs_low a Hi). unfold SB, kLowMemEnd in *. lia. }
    apply xr_abyte_off; [exact Ha64 | exact Hni |].
    apply (xr_jkeep_frame Gc STK F (ablocks_fp BLx) ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 kk 1 fpos a HGc HJ Hfr);
      [| | exact Ha64 | exact Hni].
    + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- HFF.
      * replace (fs_frame_bytes 1) with 128 by reflexivity. lia.
      * replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. unfold SB in Ha. lia.
    + intros HF. destruct (HFP a HF) as (b' & Hb' & Ha'). destruct Ha as [Ha | Ha].
      * destruct (xr_blk_frame_apart ly1 S1 W1 m1 md1 b' 1 fpos HAR1 (HBL1 b' Hb') Hfr) as [H|H];
          rewrite <- HFF in H; replace (fs_frame_bytes 1) with 128 in H by reflexivity; lia.
      * destruct b' as [p' n']. cbn [fst snd] in Ha'.
        destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p' n' HAR1 (HBL1 _ Hb')) as (_ & _ & _ & Happ & _).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.

(* ------------------------------------------------------------------ source_reset's globals: a slot of g_s *)
Definition xr_HA (j : nat) : Z := rg_s fr_RG + ASRC * Z.of_nat j.
Definition xr_segromb (a : Z) : bool := match seg_rom segs (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition xr_segwb (a : Z) : bool := match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Lemma xr_gs_rom : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> seg_rom segs (Z_to_bv 64 a) <> None.
Proof.
  intros a Ha.
  assert (Hb : forallb (fun o => xr_segromb (rg_s fr_RG + Z.of_nat o)) (seq 0 384) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat (a - rg_s fr_RG)) ltac:(apply in_seq; unfold ASRC in Ha; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (rg_s fr_RG + (a - rg_s fr_RG)) with a in Hb by lia.
  unfold xr_segromb in Hb. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate Hb].
Qed.
Lemma xr_gs_wr : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> forall m, writable_at segs m a.
Proof.
  intros a Ha m.
  assert (Hb : forallb (fun o => xr_segwb (rg_s fr_RG + Z.of_nat o)) (seq 0 384) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat (a - rg_s fr_RG)) ltac:(apply in_seq; unfold ASRC in Ha; lia)).
  rewrite Z2Nat.id in Hb by lia. replace (rg_s fr_RG + (a - rg_s fr_RG)) with a in Hb by lia.
  unfold xr_segwb in Hb.
  assert (Hw : wview segs (fun _ => None) (Z_to_bv 64 a) <> None)
    by (destruct (wview segs (fun _ => None) (Z_to_bv 64 a)); [discriminate | discriminate Hb]).
  unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate | exact Hw].
Qed.
Lemma xr_slot_gs : forall i a, (i < 4)%nat -> inG [(xr_HA i, ASRC)] a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC.
Proof.
  intros i a Hi Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr, xr_HA in Ha. cbn [fst snd] in Ha. unfold ASRC in *. lia.
Qed.
(* source_reset's own G: W_contract.v gx_prog at the slot, its image facts by vm_compute at PB_fr; B's gx_rt names
   the GOT slot A_OBJ 0 and the shadow cell A_OBJ 30 (lib/B/W_contract.v A_got_shadow / A_shadow_cell) *)
Lemma xr_gxp : forall i, (i < 4)%nat -> gx_prog B [(xr_HA i, ASRC)].
Proof.
  intros i Hi.
  assert (Hsub : forall a, inG [(xr_HA i, ASRC)] a -> inG G_fr a)
    by (intros a Ha; apply XR_HGM; apply xr_gs_GM; exact (xr_slot_gs i a Hi Ha)).
  assert (H0 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 0)) || (VAL (A_OBJ 0) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  assert (H1 : ((rg_s fr_RG + 4 * ASRC <=? VAL (A_OBJ 30)) || (VAL (A_OBJ 30) + 8 <=? rg_s fr_RG))%bool = true)
    by (vm_compute; reflexivity).
  apply orb_prop in H0, H1.
  split; [exact (gx_ok_sub segs B _ G_fr Hsub HG)|].
  split.
  { intros a Ha. pose proof (xr_slot_gs i a Hi Ha) as Hg.
    split; [exact (XR_ERRNO a (xr_gs_GM a Hg))|].
    destruct H0 as [H0|H0]; destruct H1 as [H1|H1]; apply Z.leb_le in H0; apply Z.leb_le in H1; split; lia. }
  split.
  { intros a Ha. destruct (XRF_ROM_OUT a Ha) as (Hn & Ho & He & Hk).
    split; [intros Hin; exact (Hn (Hsub a Hin)) | exact (conj Ho (conj He Hk))]. }
  split; [intros a Ha; exact (xr_gs_rom a (xr_slot_gs i a Hi Ha))|].
  split; [intros a Ha; exact (xr_gs_wr a (xr_slot_gs i a Hi Ha))|].
  intros ly S W mem md a n HAR Hn Hx. apply (XR_GSHV ly S W mem md a n HAR Hn).
  intros x Hx'. exact (xr_slot_gs i x Hi (Hx x Hx')).
Qed.

(* ------------------------------------------------------------------ the symbolic run scaffolding *)
Definition XRspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition XRbx : sv := SOff 33 0.
(* entry 0x84fe8: the only memory the run touches before `jal check_shape_done` is the `at` cell F+208 (-> a0). *)
Definition xr_at_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 208 216 208 208 [YP09.mkChunk 208 (CVal 8 (SOff 32 0))].
Definition xr_at_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (2^46) (2^47) 5);
            (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_xr_at : sstate := mkSS AX_done sr_atoms [xr_at_region] None xr_at_facts.
Definition xr_at_extra (A : Z) : list word := map (Z_to_bv 64) [A; SB].
Lemma xr_at_entry : forall (W : world segs) regs mem (F A : Z),
  2 ^ 46 <= F -> F + 320 <= 2 ^ 47 -> F mod 32 = 0 ->
  getr regs 2 = w64 F -> getr regs 9 = w64 F ->
  val_mem segs (arm W mem) (F + AX_AT) 8 A -> 0 <= A < 2 ^ 64 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (xr_at_extra A))) ss_xr_at
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_done)) mem (seg_rom segs)))
  /\ sh_ok segs XRbx [] (Eimg (Ereg regs (xr_at_extra A))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F A HFlo HFhi HF32 R2 R9 Mat HA.
  pose proof pa_B_ok as HBASE. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF16 : F mod 16 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32)) with ((2 * (F / 32)) * 16) by ring. apply Z_mod_mult. }
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (xr_at_extra A))).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 A) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  split.
  - unfold ss_xr_at. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold xr_at_region.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ F 208 8 (SOff 32 0) A);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      unfold AX_AT in Mat. exact Mat.
    + apply pairwise_disjoint_of_extents.
      unfold xr_at_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [xr_at_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U9, E32, E33, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end;
        try (unfold SB; lia); try exact HF32; try exact HF16.
  - unfold sh_ok, XRbx. constructor.
Qed.

(* ------------------------------------------------------------------ the model between the resets
   At the loop head of trip i the slots below i are closed, the others as they were; errno (ct_ev) is free. *)
Definition xr_hs (i : nat) (hs : list (option hsrc)) : list (option hsrc) := repeat None i ++ skipn i hs.
Definition xr_mid (m : lmod) (i : nat) (ev : Z) : lmod :=
  LM (lm_k m) (xr_hs i (lm_hs m)) (lm_G m) (lm_es m) (lx_ctl_ev (lm_c m) ev) (lm_O m)
     (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Fixpoint xr_cost (hs : list (option hsrc)) : Z :=
  match hs with [] => 0 | o :: hs' => sr_cost MT o + xr_cost hs' end.
Ltac xr_hs4 hs := destruct hs as [|o0 [|o1 [|o2 [|o3 [|o4 hs]]]]]; cbn [length] in *; try lia.
Lemma xr_hs_len : forall i hs, (i <= 4)%nat -> length hs = 4%nat -> length (xr_hs i hs) = 4%nat.
Proof. intros i hs Hi Hl. xr_hs4 hs. destruct i as [|[|[|[|[|i]]]]]; try lia; reflexivity. Qed.
Lemma xr_nth_hs : forall i j hs, (i <= 4)%nat -> length hs = 4%nat -> (j < 4)%nat ->
  nth j (xr_hs i hs) None = if (j <? i)%nat then None else nth j hs None.
Proof.
  intros i j hs Hi Hl Hj. xr_hs4 hs.
  destruct i as [|[|[|[|[|i]]]]]; try lia; destruct j as [|[|[|[|j]]]]; try lia; reflexivity.
Qed.
Lemma xr_concat_hs : forall i hs, (i < 4)%nat -> length hs = 4%nat ->
  concat (map slot_blks (xr_hs i hs)) = slot_blks (nth i hs None) ++ concat (map slot_blks (xr_hs (S i) hs)).
Proof.
  intros i hs Hi Hl. xr_hs4 hs.
  destruct i as [|[|[|[|i]]]]; try lia; unfold xr_hs; cbn [repeat skipn app map concat nth slot_blks]; reflexivity.
Qed.
Lemma xr_slot_in : forall k hs j b, (k <= 4)%nat -> length hs = 4%nat -> (j < 4)%nat -> (k <= j)%nat ->
  In b (slot_blks (nth j hs None)) -> In b (concat (map slot_blks (xr_hs k hs))).
Proof.
  intros k hs j b Hk Hl Hj Hkj Hb. apply in_concat. exists (slot_blks (nth j hs None)). split; [|exact Hb].
  apply in_map_iff. exists (nth j hs None). split; [reflexivity|].
  assert (E : nth j (xr_hs k hs) None = nth j hs None)
    by (rewrite xr_nth_hs by lia; destruct (Nat.ltb_spec j k); [lia | reflexivity]).
  rewrite <- E. apply nth_In. rewrite xr_hs_len by lia. lia.
Qed.
Lemma xr_cost_skip : forall i hs, (i < 4)%nat -> length hs = 4%nat ->
  xr_cost (skipn i hs) = sr_cost MT (nth i hs None) + xr_cost (skipn (S i) hs).
Proof. intros i hs Hi Hl. xr_hs4 hs. destruct i as [|[|[|[|i]]]]; try lia; reflexivity. Qed.
Lemma xr_cost_first : forall i hs, (i < 4)%nat -> length hs = 4%nat ->
  xr_cost (firstn (S i) hs) = xr_cost (firstn i hs) + sr_cost MT (nth i hs None).
Proof. intros i hs Hi Hl. xr_hs4 hs. destruct i as [|[|[|[|i]]]]; try lia; cbn [firstn xr_cost nth]; ring. Qed.
Lemma xr_perm_mid : forall (A X C : list (Z * Z)), Permutation (A ++ X ++ C) (X ++ A ++ C).
Proof. intros A X C. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. Qed.
Ltac xr_lnorm := rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc;
  reflexivity.
Lemma xr_perm_shape : forall (I E s R O rest : list (Z * Z)) (t : Z * Z),
  Permutation (I ++ (t :: E ++ (s ++ R) ++ O) ++ rest) (s ++ I ++ (t :: E ++ R ++ O) ++ rest).
Proof.
  intros I E s R O rest t.
  replace (I ++ (t :: E ++ (s ++ R) ++ O) ++ rest) with ((I ++ t :: E) ++ s ++ (R ++ O ++ rest)) by xr_lnorm.
  replace (s ++ I ++ (t :: E ++ R ++ O) ++ rest) with (s ++ (I ++ t :: E) ++ (R ++ O ++ rest)) by xr_lnorm.
  apply xr_perm_mid.
Qed.
Lemma xr_mb_perm : forall cx m i ev ev' rest, (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  Permutation (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest)
    (slot_blks (nth i (lm_hs m) None) ++ input_blks cx ++ model_blks (xr_mid m (S i) ev') ++ rest).
Proof.
  intros cx m i ev ev' rest Hi Hl. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
  rewrite (xr_concat_hs i (lm_hs m) Hi Hl). apply xr_perm_shape.
Qed.

(* ---- one call keeps the model: everything but the slots it is handed, and errno, by the keep bundle ---- *)
Ltac xr_kg KG := intros ? ?; apply KG; [xr_inGM | xr_num; lia].
Lemma xr_aout_kept : forall c O mx no cap out ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2,
  aout_at B fr_RG ly1 S1 W1 m1 c O mx no cap out ->
  (forall a, inG Gc a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC) ->
  (forall b, In b (aout_blks cap out) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  aout_at B fr_RG ly2 S2 W2 m2 (lx_ctl_ev c ev2) O mx no cap out.
Proof.
  intros c O mx no cap out ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HGc HBL (K1 & K2 & _ & _) Hev Hevw Hevr.
  assert (KG : forall a, inG xr_GM a -> ~ (rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC) -> abyte_kept W1 m1 W2 m2 a)
    by (intros a Hg Hn; apply K1; [exact Hg | intros Hc; exact (Hn (HGc a Hc))]).
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H1]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H2]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H3]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H4]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H5]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H6]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H7]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H8]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H9]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H10]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H11]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H12]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H13]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H14]|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact H15]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact H16]|].
  split; [exact Hev|]. split; [exact Hevw|]. split; [exact Hevr|].
  split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25|].
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26 | right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hb : In (out, cap) (aout_blks cap out)) by (unfold aout_blks; rewrite Ec; left; reflexivity).
  destruct (K2 (out, cap) Hin (HBL _ Hb)) as [Hin2 Kb].
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin2|]. exists junk. split; [exact Hj|].
  apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. apply Kb. cbn [fst snd].
  rewrite xr_bzs_len, length_app, Nat2Z.inj_add in Hx. pose proof (req_size_pos cap ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma xr_rest_kept : forall (mm : lmod) hs' ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2,
  amodel_at B ly1 S1 W1 m1 mm ->
  (forall a, inG Gc a -> rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC) ->
  (forall b, In b (arelay_blks (lm_G mm) (lm_es mm) ++ aout_blks (lm_cap mm) (lm_out mm)) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  length hs' = 4%nat -> (forall j, (j < 4)%nat -> aslot B ly2 S2 W2 m2 j (nth j hs' None)) ->
  amodel_at B ly2 S2 W2 m2 (LM (lm_k mm) hs' (lm_G mm) (lm_es mm) (lx_ctl_ev (lm_c mm) ev2) (lm_O mm)
     (lm_mx mm) (lm_cap mm) (lm_out mm) (lm_gn mm) (lm_nfd mm)).
Proof.
  intros mm hs' ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 HMOD HGc HBL HK Hev Hevw Hevr Hlen Hsl.
  pose proof HK as (K1 & K2 & _ & _).
  destruct HMOD as (_ & _ & Hrel & Hout & Hgn & Hlk & Hwk & Hnfd & Hnfdw & Hnfdr & Htu & (lst & Hls) & Hlsw).
  assert (KG : forall a, inG xr_GM a -> ~ (rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC) -> abyte_kept W1 m1 W2 m2 a)
    by (intros a Hg Hn; apply K1; [exact Hg | intros Hc; exact (Hn (HGc a Hc))]).
  unfold amodel_at. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [exact Hlen|]. split; [exact Hsl|].
  split.
  { apply (arelay_at_kept B fr_RG ly1 S1 W1 m1); [exact Hrel | |].
    - apply (xr_akept_cov Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 (arelay_blks (lm_G mm) (lm_es mm)) _
        (fun a => rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
                  rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4) HK).
      + intros b Hb. split; [exact (xr_arelay_live _ _ _ _ _ _ Hrel b Hb)|]. apply HBL. apply in_or_app. left. exact Hb.
      + intros a Ha. split.
        * destruct Ha as [Ha | [Ha | Ha]]; xr_inGM.
        * intros Hc. pose proof (HGc a Hc). destruct Ha as [Ha | [Ha | Ha]]; xr_num; lia.
      + intros r Hr. destruct (xr_arelay_cov _ _ _ _ _ _ Hrel r Hr) as [-> | [-> | [-> | [He | Hb]]]].
        * left. intros a Ha. cbn [fst snd] in Ha. left. exact Ha.
        * left. intros a Ha. cbn [fst snd] in Ha. right. left. exact Ha.
        * left. intros a Ha. cbn [fst snd] in Ha. right. right. exact Ha.
        * right. left. exact He.
        * right. right. exact Hb.
    - intros b Hb. apply (proj1 (K2 b (xr_arelay_live _ _ _ _ _ _ Hrel b Hb)
        (HBL b ltac:(apply in_or_app; left; exact Hb)))). }
  split.
  { apply (xr_aout_kept _ _ _ _ _ _ ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 Hout HGc); [|exact HK | exact Hev
      | exact Hevw | exact Hevr].
    intros b Hb. apply HBL. apply in_or_app. right. exact Hb. }
  split.
  { apply (agone_at_kept fr_RG W1 m1 W2 m2 _ Hgn). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply KG; [xr_inGM | xr_num; lia]. }
  split.
  { apply (alock_at_kept fr_RG W1 m1 W2 m2 _ Hlk). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply KG; [xr_inGM | xr_num; lia]. }
  split.
  { apply (awake_at_kept fr_RG W1 m1 W2 m2 Hwk). intros r [<- | []] x Hx. cbn [fst snd] in Hx.
    apply KG; [xr_inGM | xr_num; lia]. }
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact Hnfd]|].
  split; [apply (akept_awr W1 m1); [xr_kg KG | exact Hnfdw]|].
  split; [exact Hnfdr|].
  split; [apply (akept_vm W1 m1); [xr_kg KG | exact Htu]|].
  split; [exists lst; apply (akept_vm W1 m1); [xr_kg KG | exact Hls]|].
  apply (akept_awr W1 m1); [xr_kg KG | exact Hlsw].
Qed.
Lemma xr_slot_kept : forall Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j o,
  AR segs B ly1 S1 W1 m1 md1 -> (j < 4)%nat ->
  aslot B ly1 S1 W1 m1 j o ->
  (forall a, inG Gc a -> ~ (xr_HA j <= a < xr_HA j + ASRC)) ->
  (forall b, In b (slot_blks o) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  aslot B ly2 S2 W2 m2 j o.
Proof.
  intros Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j o HAR Hj Hs HGc HBL HK. pose proof HK as (K1 & K2 & _ & _).
  assert (Hgs : forall a, xr_HA j <= a < xr_HA j + ASRC -> inG xr_GM a)
    by (intros a Ha; apply xr_gs_GM; unfold xr_HA, ASRC in *; lia).
  assert (KS : forall a, xr_HA j <= a < xr_HA j + ASRC -> abyte_kept W1 m1 W2 m2 a)
    by (intros a Ha; apply K1; [exact (Hgs a Ha) | intros Hc; exact (HGc a Hc Ha)]).
  destruct o as [h|]; unfold aslot in *.
  - apply (asrc_at_kept B ly1 S1 W1 m1); [exact Hs | |].
    + apply (xr_akept_cov Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 (asrc_blks h) _
        (fun a => xr_HA j <= a < xr_HA j + ASRC) HK).
      * intros b Hb. split; [exact (xr_asrc_live _ _ _ _ _ _ Hs b Hb) | exact (HBL b Hb)].
      * intros a Ha. split; [exact (Hgs a Ha) | intros Hc; exact (HGc a Hc Ha)].
      * intros r Hr. destruct (xr_asrc_cov _ _ _ _ _ _ Hs r Hr) as [Hin | Hbl];
          [left; intros a Ha; unfold xr_HA in *; lia | right; right; exact Hbl].
    + intros b Hb. exact (proj1 (K2 b (xr_asrc_live _ _ _ _ _ _ Hs b Hb) (HBL b Hb))).
  - destruct Hs as [Hg Hw]. split.
    + apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. rewrite repeat_length in Hx.
      apply KS. unfold xr_HA, ASRC in *. lia.
    + apply (akept_awr W1 m1); [|exact Hw]. intros x Hx. apply KS. unfold xr_HA in *. lia.
Qed.
Lemma xr_model_step : forall cx (m : lmod) i ev ev2 Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 rest0,
  (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  AR segs B ly1 S1 W1 m1 md1 ->
  amodel_at B ly1 S1 W1 m1 (xr_mid m i ev) ->
  Permutation (ablocks B ly1 S1) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest0) ->
  (forall a, inG Gc a -> xr_HA i <= a < xr_HA i + ASRC) ->
  (forall b, In b BLx -> In b (slot_blks (nth i (lm_hs m) None))) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  asrc_closed W2 m2 (xr_HA i) ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  amodel_at B ly2 S2 W2 m2 (xr_mid m (S i) ev2).
Proof.
  intros cx m i ev ev2 Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 rest0 Hi Hlen HAR1 HMOD HP HGc HBLx HK Hcl
    Hev Hevw Hevr.
  pose proof (Permutation_NoDup HP (xr_nodup ly1 S1 W1 m1 md1 HAR1)) as HND.
  pose proof (Permutation_NoDup (xr_mb_perm cx m i ev ev2 rest0 Hi Hlen) HND) as HND2.
  assert (HY : forall b, In b (input_blks cx ++ model_blks (xr_mid m (S i) ev2) ++ rest0) -> ~ In b BLx)
    by (intros b Hb Hx; exact (xr_nodup_app _ _ b HND2 (HBLx b Hx) Hb)).
  assert (HYm : forall b, In b (model_blks (xr_mid m (S i) ev2)) -> ~ In b BLx)
    by (intros b Hb; apply HY; apply in_or_app; right; apply in_or_app; left; exact Hb).
  pose proof HMOD as (_ & Hsl & _).
  apply (xr_rest_kept (xr_mid m i ev) (xr_hs (S i) (lm_hs m)) ev2 Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 HMOD).
  - intros a Ha. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
  - intros b Hb. apply HYm. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    apply in_app_or in Hb as [Hb | Hb].
    + unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [left; reflexivity|].
      right. apply in_or_app. left. exact Hb.
    + right. apply in_or_app. right. apply in_or_app. right. exact Hb.
  - exact HK.
  - exact Hev.
  - exact Hevw.
  - exact Hevr.
  - apply xr_hs_len; lia.
  - intros j Hj. rewrite xr_nth_hs by lia.
    pose proof (Hsl j Hj) as Hs. cbn [lm_hs xr_mid] in Hs. rewrite xr_nth_hs in Hs by lia.
    destruct (Nat.ltb_spec j (S i)).
    + destruct (Nat.eq_dec j i) as [-> | Hne]; [exact Hcl|].
      destruct (Nat.ltb_spec j i); [|lia].
      apply (xr_slot_kept Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j None HAR1 Hj Hs); [| intros b [] | exact HK].
      intros a Ha Hr. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
    + destruct (Nat.ltb_spec j i); [lia|].
      apply (xr_slot_kept Gc BLx FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j (nth j (lm_hs m) None) HAR1 Hj Hs);
        [| | exact HK].
      * intros a Ha Hr. pose proof (HGc a Ha). unfold xr_HA, ASRC in *. lia.
      * intros b Hb. apply HYm. unfold model_blks, xr_mid. cbn [lm_G lm_es lm_hs lm_cap lm_out].
        right. apply in_or_app. right. apply in_or_app. left.
        apply (xr_slot_in (S i) (lm_hs m) j b); [lia | exact Hlen | exact Hj | lia | exact Hb].
Qed.
Lemma xr_model_keep : forall (m : lmod) i ev ev2 FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2,
  (i <= 4)%nat -> length (lm_hs m) = 4%nat -> AR segs B ly1 S1 W1 m1 md1 ->
  amodel_at B ly1 S1 W1 m1 (xr_mid m i ev) ->
  xr_kb [] [] FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  val_mem segs (arm W2 m2) (as_errno B) 4 ev2 -> awr W2 m2 (as_errno B) 4 -> 0 <= ev2 < 2 ^ 32 ->
  amodel_at B ly2 S2 W2 m2 (xr_mid m i ev2).
Proof.
  intros m i ev ev2 FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 Hi Hlen HAR1 HMOD HK Hev Hevw Hevr.
  pose proof HMOD as (_ & Hsl & _).
  apply (xr_rest_kept (xr_mid m i ev) (xr_hs i (lm_hs m)) ev2 [] [] FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 HMOD);
    [intros a Ha; exfalso; exact (inG_nil a Ha) | intros b _ [] | exact HK | exact Hev | exact Hevw | exact Hevr
    | apply xr_hs_len; lia |].
  intros j Hj. apply (xr_slot_kept [] [] FF lo hi ly1 S1 W1 m1 md1 ly2 S2 W2 m2 j _ HAR1 Hj (Hsl j Hj));
    [intros a Ha; exfalso; exact (inG_nil a Ha) | intros b _ [] | exact HK].
Qed.
Lemma xr_ainput_kept : forall cx Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2,
  ainput_at B cx ly1 S1 W1 m1 -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall b, In b (input_blks cx) -> ~ In b BLx) ->
  xr_kb Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  ainput_at B cx ly2 S2 W2 m2.
Proof.
  intros cx Gc BLx FF lo hi ly1 S1 W1 m1 ly2 S2 W2 m2 [[(Hn & Hp) | (Hn & Hin)] Hg] Hlen HBL (_ & K2 & _ & _).
  - split; [left; exact (conj Hn Hp)|].
    apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. rewrite length_map in Hx. lia.
  - assert (Hb : In (c_p cx, c_n cx) (input_blks cx))
      by (unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); left; reflexivity).
    destruct (K2 _ Hin (HBL _ Hb)) as [Hin2 Kb].
    split; [right; exact (conj Hn Hin2)|].
    apply (akept_garr8 W1 m1); [|exact Hg]. intros x Hx. apply Kb. cbn [fst snd]. rewrite length_map in Hx.
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
Qed.
(* the frame and the fake frame, by the bundle (W_LLVMFuzzerTestOneInput_latch.v lt_aframe_kept's shape) *)
Lemma xr_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* B: bx_frame (lib/B/W_bx_defs.v), the cut's aframe_at without its F+152 clause: thirteen frame cells
   F+32 .. F+184, all inside [F, F + 320), and the fake frame's three cells, its 128 bytes and its 16 shadow bytes *)
Lemma xr_bxframe_kept : forall cx FF Gc BLx ly1 S1 W1 m1 ly2 S2 W2 m2,
  bx_frame cx FF W1 m1 ->
  xr_kb Gc BLx FF (lf_F cx) (spZ (c_regs cx)) ly1 S1 W1 m1 ly2 S2 W2 m2 ->
  lf_F cx + 320 <= spZ (c_regs cx) ->
  bx_frame cx FF W2 m2.
Proof.
  intros cx FF Gc BLx ly1 S1 W1 m1 ly2 S2 W2 m2
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20)
    (_ & _ & KH & KF) HF1.
  split.
  { intros o r Hin. apply (xr_sv8_kept W1 W2 m1 m2); [|exact (A1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  split.
  { apply (akept_awr W1 m1); [|exact A2]. intros x Hx. apply KH. lia. }
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A3]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A4]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A5]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A6]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A7]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A8]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A9]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A10]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A11]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A12]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A13]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A14]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KH; lia | exact A15]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KF; lia | exact A16]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KF; lia | exact A17]|].
  split; [apply (xr_sv8_kept W1 W2 m1 m2); [intros x Hx; apply KF; lia | exact A18]|].
  split; [apply (akept_awr W1 m1); [intros x Hx; apply KF; lia | exact A19]|].
  split.
  { apply (akept_garr8 W1 m1); [|exact (proj1 A20)]. intros x Hx.
    unfold fake_shadow in Hx. cbn [length] in Hx. apply KF. lia. }
  apply (akept_awr W1 m1); [intros x Hx; apply KF; lia | exact (proj2 A20)].
Qed.
(* the callee's rom_out, from G_fr's *)
Lemma xr_rom_out_sub : forall Gc, (forall a, inG Gc a -> inG G_fr a) -> rom_out segs B Gc.
Proof.
  intros Gc Hs a Ha. destruct (XRF_ROM_OUT a Ha) as (Hn & Ho & He & Hk).
  split; [intros Hin; exact (Hn (Hs a Hin)) | exact (conj Ho (conj He Hk))].
Qed.
(* a callee's journal keeps the layout's frame addresses and, owning nothing, the frames *)
Lemma xr_fa_kept : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0,
  ajournal_gx segs B G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k ->
  AR segs B ly1 S1 W0 m0 md0 -> forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 own ly2 S2 W2 m2 md2 k W0 m0 md0 (_ & _ & (memS & HJi & _) & _) HAR.
  pose proof HJi as (_ & Hly & _).
  exact (proj1 (proj2 (al_layout _ _ LAWS ly1 S1 W0 m0 md0 ly2 HAR Hly))).
Qed.
Lemma xr_frames_kept : forall G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k,
  ajournal_gx segs B G XO OUT STK sp FP ly1 S1 W1 m1 md1 [] ly2 S2 W2 m2 md2 k -> frames S2 = frames S1.
Proof.
  intros G XO OUT STK sp FP ly1 S1 W1 m1 md1 ly2 S2 W2 m2 md2 k (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.
(* ------------------------------------------------------------------ the frame's numbers *)
Lemma xr_F_bounds : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  alloc_ceiling + LLVMF_STK - 352 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  lf_F cx mod 32 = 0 /\ 2 ^ 46 <= lf_F cx /\ spZ (c_regs cx) <= lf_F cx + 352.
Proof.
  intros cx (_ & HPRE). pose proof (proj1 HPRE) as HAFN.
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold lf_F. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  split; [unfold LLVMF_STK in *; lia|]. split; [lia|]. split; [lia|]. split.
  - rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
  - split; [unfold LLVMF_STK in *; lia | lia].
Qed.
Lemma xr_cost_nonneg : forall hs, 0 <= xr_cost hs.
Proof.
  pose proof (mo_free_nonneg MT MLM) as Hf.
  induction hs as [|o hs IH]; cbn [xr_cost]; [lia|].
  assert (Ho : 0 <= sr_cost MT o).
  { destruct o as [h|]; cbn [sr_cost]; [|lia]. unfold lf_cost, hl_n. nia. }
  lia.
Qed.
Lemma xr_sr_slot : forall o, Permutation (slot_blks o) (sr_blks o).
Proof.
  intros [h|]; [|apply Permutation_refl]. cbn [slot_blks sr_blks]. unfold asrc_blks, hs_blks. cbn [app].
  apply Permutation_middle.
Qed.
(* W_source_reset.v azs_sub *)
Lemma xr_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. repeat split; lia. Qed.

(* ------------------------------------------------------------------ the reset loop (0x85004, four trips) *)
Definition xr_facts0 : facts := mkFacts [ (32%nat, mkAF SB SB 0) ] [] [].
Definition xr_extra0 : list word := map (Z_to_bv 64) [SB].
Definition XRbx0 : sv := SOff 32 0.
(* a state that names no memory: the loop head and the return from source_reset *)
Lemma xr_entry0 : forall pc (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (Ereg regs xr_extra0)) (mkSS pc sr_atoms [] None xr_facts0)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs XRbx0 [] (Eimg (Ereg regs xr_extra0)) (mrestrict (w_H W) mem).
Proof.
  intros pc W regs mem. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs xr_extra0)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [xr_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* every register but ra and a0 *)
Definition xr_kept0 : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* every register but s3, which `addi s3,s3,96` sets *)
Definition xr_kept19 : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* every register but a0, s2, s3, s4, s8, which the loop's set-up 0x84ff0..0x85000 sets (B loads no s7) *)
Definition xr_kept_set : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%bv.
Ltac xr_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac xr_in := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma xr_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

(* the loop head 0x85004 of trip i (i = 4: the fall-through 0x85014) *)
Definition xr_inv (cx : lfcx) (m : lmod) (fpos : Z) (ly3 : alayout) (S3 : astate) (i : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S k ev,
    c = cfg_at segs (BASE + (if (i <? 4)%nat then AX_reset_loop else AX_ffexit)) regs mem md /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k /\
    frame_addr ly 1 fpos = frame_addr ly3 1 fpos /\
    bx_frame cx (frame_addr ly3 1 fpos) W mem /\
    sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
    getr regs 2 = w64 (lf_F cx) /\ getr regs 9 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
    getr regs 19 = w64 (xr_HA i) /\ getr regs 18 = w64 (xr_HA 4) /\
    getr regs 20 = w64 (frame_addr ly3 1 fpos) /\
    getr regs 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\
    amodel_at B ly S W mem (xr_mid m i ev) /\
    (forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest)) /\
    ainput_at B cx ly S W mem /\
    rom_view segs W mem /\
    mo_le MT S3 S (xr_cost (firstn i (lm_hs m))) /\
    mo_ok MT S (xr_cost (skipn i (lm_hs m))).
(* a slot's blocks are not empty (so req_size is their size) *)
Lemma xr_alist_pos : forall ly S (W : world segs) mem LA l lines, alist_at B ly S W mem LA l lines ->
  forall b, In b (alist_blks l) -> 0 < snd b.
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - xr_ifz (hl_cap l) Hb Ec. destruct Hb as [<- | []]. cbn [snd].
    destruct H6 as [(Hc0 & _) | (Hc1 & _)]; [apply Z.eqb_neq in Ec; lia | unfold AREC; lia].
  - apply in_map_iff in Hb as (r & <- & Hr). cbn [snd]. lia.
Qed.
Lemma xr_asrc_pos : forall ly S (W : world segs) mem HA h, asrc_at B ly S W mem HA h ->
  forall b, In b (asrc_blks h) -> 0 < snd b.
Proof.
  intros ly S W mem HA h
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
     H21 & H22 & H23 & H24) b Hb.
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [cbn [snd]; unfold APARTIAL; lia|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xr_alist_pos _ _ _ _ _ _ _ H10 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (xr_alist_pos _ _ _ _ _ _ _ H22 b Hb)|].
  exact (xr_alist_pos _ _ _ _ _ _ _ H23 b Hb).
Qed.

Lemma xr_iter : forall cx m fpos ly3 S3 i (W : world segs) c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> (i < 4)%nat -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv cx m fpos ly3 S3 i W c ->
  SRr segs W c (xr_inv cx m fpos ly3 S3 (S i)).
Proof.
  intros cx m fpos ly3 S3 i W c HB Hi Hlen (rest0 & HP0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (xr_F_bounds cx HB) as (HFlo & HFsp & Hsp47 & HF32 & HF46 & HFsp2).
  set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  set (hs := lm_hs m) in *.
  replace (if (i <? 4)%nat then AX_reset_loop else AX_ffexit) with AX_reset_loop
    by (destruct (Nat.ltb_spec i 4); [reflexivity | lia]).
  destruct (xr_entry0 AX_reset_loop W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs xr_extra0)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs xr_extra0) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E19 : ew E 19 = getr regs 19)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
  clear HE.
  unfold cfg_at. change (w64 (BASE + AX_reset_loop)) with (Z_to_bv 64 (BASE + AX_reset_loop)).
  paj_run_to_tok RUNTO HS HJ SHOK XRspan AF_fr_source_reset.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Emeq end.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs xr_extra0 xr_kept0 HS HAE ltac:(vm_compute; reflexivity))
    as KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  rewrite Emeq in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  (* the input's length: fr_lib_pre_cf's sixth clause (a positional destruct: tauto would touch every arrow-typed
     Section variable and make the lemma take them) *)
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & (_ & _ & _ & _ & _ & HN & _)); exact HN).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(unfold xr_kept0; xr_in)), R2; apply unsigned_lit_small; unfold LLVMF_STK in *;
        lia).
  assert (HFR' : bx_frame cx (frame_addr ly 1 fpos) W mem) by (rewrite HFA; exact HFR).
  destruct (lx_afn_pre_at B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG cx ly S fpos k W mem mdc (ms_regs ms) SR_STK
    HB HJ HFR' Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(unfold xr_kept0; xr_in)). exact R3. }
  { rewrite (KR 4%bv ltac:(unfold xr_kept0; xr_in)). exact R4. }
  { rewrite (KR 8%bv ltac:(unfold xr_kept0; xr_in)). exact R8. }
  { unfold SR_STK, LF_STK, ASTACK. lia. }
  { unfold SR_STK, LF_STK, ASTACK, LLVMF_STK. lia. }
  (* source_reset's premises: the slot, its zero shadow, the meter *)
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, fpos) (frames S)) by (rewrite Hfrs; left; reflexivity).
  pose proof HMOD as (_ & Hsl & _).
  set (o := nth i hs None) in *.
  assert (Hslot : match o with Some h => asrc_at B ly S W mem (xr_HA i) h | None => asrc_closed W mem (xr_HA i) end).
  { pose proof (Hsl i Hi) as Hs. cbn [lm_hs xr_mid] in Hs. fold hs in Hs.
    rewrite xr_nth_hs in Hs by lia. destruct (Nat.ltb_spec i i); [lia|]. exact Hs. }
  assert (Hazs : azs B (xr_HA i) ASRC) by (apply (xr_azs_sub _ _ _ _ AZS_s); unfold xr_HA, ASRC; lia).
  (* B's sr_spec takes the slot's alignment: g_s = 0x5d8e60 = 8 * 766412, ASRC = 96 *)
  assert (HHA8 : xr_HA i mod 8 = 0).
  { unfold xr_HA, ASRC, fr_RG. cbn [fr_globals_b rg_s]. apply (proj2 (Z.mod_divide _ 8 ltac:(lia))).
    exists (766412 + 12 * Z.of_nat i). lia. }
  assert (HMOKs : mo_ok MT S (sr_cost MT o)).
  { apply (mo_ok_le MT MLM S _ (xr_cost (skipn i hs))); [exact HMOK|].
    rewrite (xr_cost_skip i hs Hi Hlen). pose proof (xr_cost_nonneg (skipn (Datatypes.S i) hs)). fold o. lia. }
  eapply SRr_bind.
  { exact (SR [(xr_HA i, ASRC)] (xr_gxp i Hi) W ly S (ms_regs ms) mem mdc ch (xr_HA i) o HPREc
      ltac:(rewrite Q10, E19; exact R19) HHA8 Hslot
      ltac:(intros a Ha; apply (proj2 (inG_cons _ _ _)); left; unfold in_zr; cbn [fst snd]; exact Ha) Hazs HROM HMOKs). }
  intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & kk & -> & HJc & HP2 & Hcl & HBP & HPRES & HFRM & HMLE2).
  rewrite Hsp1 in HJc.
  (* the slot's blocks: live, in the model, not empty *)
  assert (HoS : forall b, In b (sr_blks o) -> In b (slot_blks o))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym (xr_sr_slot o)) Hb)).
  assert (HoL : forall b, In b (slot_blks o) -> In b (ablocks B ly S) /\ 0 < snd b).
  { intros b Hb. destruct o as [h|]; [|destruct Hb]. cbn [slot_blks] in Hb.
    exact (conj (xr_asrc_live _ _ _ _ _ _ Hslot b Hb) (xr_asrc_pos _ _ _ _ _ _ Hslot b Hb)). }
  assert (HoM : forall b, In b (slot_blks o) -> In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
    pose proof (xr_slot_in 0 hs i b ltac:(lia) Hlen Hi ltac:(lia) Hb) as H. exact H. }
  (* source_reset's journal inside this function's *)
  assert (HGsub : forall a, inG [(xr_HA i, ASRC)] a -> inG G_fr a)
    by (intros a Ha; apply XR_HGM; apply xr_gs_GM; exact (xr_slot_gs i a Hi Ha)).
  pose proof (ajournal_gx_G_mono segs B _ G_fr 0 [] SR_STK F _ ly S W mem mdc [] ly2 S2 W2 mem2 md2 kk HGsub HJc)
    as HJc'.
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem mdc k
     SR_STK F 0 [] _ [] ly2 S2 W2 mem2 md2 kk HJ HJc'
     ltac:(unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG) as HJ2.
  assert (HJ2' : ajournal_gx segs B G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 W2 mem2 md2 (k + kk)).
  { apply HJ2. intros a (r & Hr & Ha). unfold blk_FP in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
    destruct (HoL b (HoS b Hb)) as [HbL Hb0].
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnew].
    - destruct (HSEP2 b (HoM b (HoS b Hb))) as [Hn | Hcov]; [contradiction|].
      left. split; [apply Hcov; lia|]. exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact HbL | exact Ha].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact HbL|]. split; [exact Hnew | exact Ha]. }
  clear HJ2. cbn [app] in HJ2'.
  clear HS SHOK HF HFr HG0.
  (* what the call kept *)
  set (restB := input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev) ++ rest0).
  assert (HPa : Permutation (ablocks B ly S) (input_blks cx ++ model_blks (xr_mid m i ev) ++ rest0))
    by exact (HPRM rest0 HP0).
  assert (HPb : Permutation (ablocks B ly S) (sr_blks o ++ restB)).
  { eapply Permutation_trans; [exact HPa|]. eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev rest0 Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HK : xr_kb [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2).
  { apply (xr_kb_of_j [(xr_HA i, ASRC)] (sr_blks o) SR_STK F sp0 FF fpos ly S W mem mdc ly2 S2 W2 mem2 md2 kk restB
      (gx_ok_sub segs B _ G_fr HGsub HG) HJc HAR HPb (HBP restB HPb) HPRES);
      [unfold SR_STK, LF_STK, ASTACK; lia | unfold SR_STK, LF_STK, ASTACK, LLVMF_STK in *; lia | lia | exact Hin1
      | symmetry; exact HFA]. }
  pose proof (ajournal_gx_AR segs B _ 0 [] SR_STK F _ ly S W mem mdc [] ly2 S2 W2 mem2 md2 kk HJc) as HAR2.
  destruct (ERR ly2 S2 W2 mem2 md2 HAR2) as ((ev2 & Hev & Hevr) & Hevw).
  assert (HMOD2 : amodel_at B ly2 S2 W2 mem2 (xr_mid m (Datatypes.S i) ev2)).
  { apply (xr_model_step cx m i ev ev2 [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem mdc ly2 S2 W2 mem2 rest0
      Hi Hlen HAR HMOD HPa); [| exact HoS | exact HK | exact Hcl | exact Hev | exact Hevw | exact Hevr].
    intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; exact Ha|].
    exfalso. exact (inG_nil a Ha). }
  assert (HPRM2 : forall rest, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
       Permutation (ablocks B ly2 S2) (input_blks cx ++ model_blks (xr_mid m (Datatypes.S i) ev2) ++ rest)).
  { intros rest Hr. apply HBP. eapply Permutation_trans; [exact (HPRM rest Hr)|].
    eapply Permutation_trans; [exact (xr_mb_perm cx m i ev ev2 rest Hi Hlen)|].
    apply Permutation_app_tail. exact (xr_sr_slot o). }
  assert (HND : List.NoDup (sr_blks o ++ restB)) by exact (Permutation_NoDup HPb (xr_nodup ly S W mem mdc HAR)).
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { apply (xr_ainput_kept cx [(xr_HA i, ASRC)] (sr_blks o) FF F sp0 ly S W mem ly2 S2 W2 mem2 HIN (eq_sym HlenP));
      [|exact HK].
    intros b Hb Hx. exact (xr_nodup_app _ _ b HND Hx ltac:(unfold restB; apply in_or_app; left; exact Hb)). }
  assert (HFR2 : bx_frame cx FF W2 mem2)
    by exact (xr_bxframe_kept cx FF [(xr_HA i, ASRC)] (sr_blks o) ly S W mem ly2 S2 W2 mem2 HFR HK HFsp).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM2 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view;
      first [exact HJc | exact (xr_rom_out_sub _ HGsub) | exact HROM | exact LAWS | exact pa_segs_low]. }
  assert (HFA2 : frame_addr ly2 1 fpos = FF).
  { rewrite (xr_fa_kept _ _ _ _ _ _ ly S W mem mdc _ ly2 S2 W2 mem2 md2 kk W mem mdc HJc HAR). exact HFA. }
  assert (HMLE3 : mo_le MT S3 S2 (xr_cost (firstn (Datatypes.S i) hs))).
  { rewrite (xr_cost_first i hs Hi Hlen). exact (mo_le_trans MT MLM _ _ _ _ _ HMLE (proj2 HMLE2)). }
  assert (HMOK3 : mo_ok MT S2 (xr_cost (skipn (Datatypes.S i) hs))).
  { rewrite (xr_cost_skip i hs Hi Hlen) in HMOK. exact (mo_ok_step MT MLM _ _ _ _ HMOK (proj2 HMLE2)). }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* back at 0x8500c (AX_reset_loop + 8 = 0x2cc8 = 11464 from BASE): addi s3,s3,96; bne s3,s2 *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 11464)) with (Z_to_bv 64 (BASE + (AX_reset_loop + 8))).
  destruct (xr_entry0 (AX_reset_loop + 8) W2 regs2 mem2) as [HSb SHOKb].
  remember (Eimg (Ereg regs2 xr_extra0)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 xr_extra0) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb19 : ew Eb 19 = w64 (xr_HA i)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl).
    rewrite (RR 19%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)). exact R19. }
  assert (Eb18 : ew Eb 18 = w64 (xr_HA 4)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl).
    rewrite (RR 18%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)). exact R18. }
  clear HEb.
  paj_run_tok RUN HSb HJ2' SHOKb XRspan.
  { apply awr_ok_x_nil. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  clear HF HFr.
  assert (FIN : forall rf mdf, (forall r, In r xr_kept19 -> getr rf r = getr regs2 r) ->
      getr rf 19 = w64 (xr_HA (Datatypes.S i)) ->
      ajournal_gx segs B G_fr 0 [] LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly2 S2 W2 mem2 mdf (k + kk) ->
      forall c, c = cfg_at segs (BASE + (if (Datatypes.S i <? 4)%nat then AX_reset_loop else AX_ffexit)) rf mem2 mdf ->
      xr_inv cx m fpos ly3 S3 (Datatypes.S i) W2 c).
  { intros rf mdf KX R19' HJf c ->. exists rf, mem2, mdf, ly2, S2, (k + kk), ev2.
    split; [reflexivity|]. split; [exact HJf|]. split; [exact HFA2|]. split; [exact HFR2|]. split; [exact HFL2|].
    assert (KY : forall r : bv 5, In r xr_kept19 -> acallee_saved (bv_unsigned r) -> In r xr_kept0 ->
        getr rf r = getr regs r) by (intros r H1 H2 H3; rewrite (KX r H1); exact (RR r H2 H3)).
    split; [rewrite (KY 2%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R2|].
    split; [rewrite (KY 9%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R9|].
    split; [rewrite (KY 8%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R8|].
    split; [rewrite (KY 3%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R3|].
    split; [rewrite (KY 4%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R4|].
    split; [exact R19'|].
    split; [rewrite (KY 18%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R18|].
    split; [rewrite (KY 20%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R20|].
    split; [rewrite (KY 24%bv ltac:(unfold xr_kept19; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R24|].
    split; [exact HMOD2|]. split; [exact HPRM2|]. split; [exact HIN2|]. split; [exact HROM2|].
    split; [exact HMLE3 | exact HMOK3]. }
  assert (HU19 : U Eb (SOff 19 96) = xr_HA i + 96)
    by (apply (U_atom_off Eb 19 (xr_HA i) 96 Eb19); unfold xr_HA; xr_num; lia).
  assert (HU18 : U Eb (SOff 18 0) = xr_HA 4) by (apply (U_atom Eb 18 (xr_HA 4) Eb18); unfold xr_HA; xr_num; lia).
  psrr_branch_tok RUN BR HSb SHOKb XRspan.
  - assert (Hi3 : (i < 3)%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. unfold xr_HA, ASRC in Hc.
      lia. }
    paj_run_to_tok RUNTO HSb HJ2' SHOKb XRspan AX_reset_loop.
    { apply awr_ok_x_nil. }
    lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
      pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em3 end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 xr_extra0 xr_kept19 HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    prreg HSb (19%bv : bv 5) Q19.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply SRr_ret.
    lazymatch goal with |- xr_inv _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + rewrite (proj2 (Nat.ltb_lt (Datatypes.S i) 4) ltac:(lia)). reflexivity.
  - assert (Hi3 : i = 3%nat).
    { rewrite branch_ne_U, HU19, HU18 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold xr_HA, ASRC in Hc. lia. }
    paj_run_to_tok RUNTO HSb HJ2' SHOKb XRspan AX_ffexit.
    { apply awr_ok_x_nil. }
    lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
      pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em3 end.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 xr_extra0 xr_kept19 HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    prreg HSb (19%bv : bv 5) Q19.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply SRr_ret.
    lazymatch goal with |- xr_inv _ _ _ _ _ _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} =>
      apply (FIN r d KR2) end.
    + rewrite Q19, Eb19. unfold w64. rewrite unsigned_lit_small by (unfold xr_HA; xr_num; lia). f_equal.
      unfold xr_HA, ASRC. lia.
    + exact HJ2'.
    + subst i. reflexivity.
Qed.
(* the four trips *)
Lemma xr_loop : forall cx m fpos ly3 S3,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  forall n i (W : world segs) c, (i + n = 4)%nat -> xr_inv cx m fpos ly3 S3 i W c ->
  SRr segs W c (xr_inv cx m fpos ly3 S3 4).
Proof.
  intros cx m fpos ly3 S3 HB Hlen Hrest HSEP2 n. induction n as [|n IH]; intros i W c Hn Hinv.
  - replace i with 4%nat in Hinv by lia. apply SRr_ret. exact Hinv.
  - eapply SRr_bind; [exact (xr_iter cx m fpos ly3 S3 i W c HB ltac:(lia) Hlen Hrest HSEP2 Hinv)|].
    intros W' c' _ Hinv'. exact (IH (Datatypes.S i) W' c' ltac:(lia) Hinv').
Qed.
(* the model at the first and after the last trip *)
Lemma xr_mid0 : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m ->
  amodel_at B ly S W mem (xr_mid m 0 (ct_ev (lm_c m))).
Proof.
  intros ly S W mem m H. destruct m as [mk mhs mG mes mc mO mmx mcap mout mgn mnfd]. destruct mc. exact H.
Qed.
Lemma xr_mid4 : forall m ev, length (lm_hs m) = 4%nat -> xr_mid m 4 ev = lx_reset_model m ev.
Proof.
  intros m ev Hl. destruct m as [mk mhs mG mes mc mO mmx mcap mout mgn mnfd]. cbn [lm_hs] in Hl.
  xr_hs4 mhs. reflexivity.
Qed.
Lemma xr_cost_all : forall hs, length hs = 4%nat ->
  xr_cost (skipn 0 hs) = sr_cost MT (nth 0 hs None) + sr_cost MT (nth 1 hs None)
                        + sr_cost MT (nth 2 hs None) + sr_cost MT (nth 3 hs None) /\
  xr_cost (firstn 4 hs) = sr_cost MT (nth 0 hs None) + sr_cost MT (nth 1 hs None)
                        + sr_cost MT (nth 2 hs None) + sr_cost MT (nth 3 hs None).
Proof. intros hs Hl. xr_hs4 hs. cbn [skipn firstn xr_cost nth]. split; ring. Qed.
(* the loop's exit is the block's post *)
Lemma xr_post : forall cx m fpos ly3 S3 (W : world segs) c,
  length (lm_hs m) = 4%nat ->
  (exists rest0, Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest0)) ->
  (forall b, In b (model_blks m) ->
     ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
     (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a)) ->
  xr_inv cx m fpos ly3 S3 4 W c -> lx_reset_post B MT G_fr fr_FP cx m fpos ly3 S3 W c.
Proof.
  intros cx m fpos ly3 S3 W c Hlen (rest0 & HP0) HSEP2
    (regs & mem & md & ly & S & k & ev & -> & HJ & HFA & HFR & HFL & R2 & R9 & R8 & R3 & R4 & R19 & R18 & R20 & R24 &
     HMOD & HPRM & HIN & HROM & HMLE & HMOK).
  rewrite (xr_mid4 m ev Hlen) in HMOD, HPRM.
  destruct (xr_cost_all (lm_hs m) Hlen) as [_ Hc4]. rewrite Hc4 in HMLE.
  exists ly, S, regs, mem, md, k, ev.
  split; [reflexivity|]. split; [exact HJ|].
  split; [exact R2|]. split; [exact R9|]. split; [exact R8|]. split; [exact R20|].
  split; [exact R24|]. split; [exact R3|]. split; [exact R4|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split.
  { split; [exists rest0; exact (HPRM rest0 HP0)|].
    intros b Hb. apply HSEP2. unfold model_blks, lx_reset_model in *. cbn [lm_G lm_es lm_hs lm_cap lm_out] in Hb.
    destruct Hb as [<- | Hb]; [left; reflexivity|]. right.
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|].
    apply in_or_app; right. apply in_or_app; right. exact Hb. }
  split; [exact HIN|]. split; [exact HPRM|]. split; [exact HROM|]. split; [exact HFA | exact HMLE].
Qed.

(* ------------------------------------------------------------------ 0x84ff0, back from check_shape_done: the loop's set-up
   (`auipc a0,0x554; addi s3,a0,-400; addi s2,s3,384; ld s4,80(s1); ld s8,96(s1)`) reads the two frame slots F+80 (FF)
   and F+96 (shadow of FF); B has no `ld s7,88(s1)` *)
Definition xr_set_region : YP09.region :=
  YP09.mkRegion (Some 9%nat) 80 104 80 80
    [YP09.mkChunk 80 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 33 0))].
Definition xr_set_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (2^46) (2^47) 5);
            (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF SB SB 0) ] [] [].
Definition ss_xr_set : sstate := mkSS AX_resets sr_atoms [xr_set_region] None xr_set_facts.
Definition xr_set_extra (FF : Z) : list word := map (Z_to_bv 64) [FF; SB + FF / 8; SB].
Definition XRbx2 : sv := SOff 34 0.
Lemma xr_set_entry : forall (W : world segs) regs mem (F FF : Z),
  2 ^ 46 <= F -> F + 320 <= 2 ^ 47 -> F mod 32 = 0 ->
  getr regs 2 = w64 F -> getr regs 9 = w64 F ->
  sv8 W mem (F + 80) FF -> sv8 W mem (F + 96) (SB + FF / 8) ->
  0 <= FF < 2 ^ 64 -> 0 <= SB + FF / 8 < 2 ^ 64 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (xr_set_extra FF))) ss_xr_set
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AX_resets)) mem (seg_rom segs)))
  /\ sh_ok segs XRbx2 [] (Eimg (Ereg regs (xr_set_extra FF))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F FF HFlo HFhi HF32 R2 R9 M80 M96 HFF HSF.
  pose proof pa_B_ok as HBASE. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF16 : F mod 16 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32)) with ((2 * (F / 32)) * 16) by ring. apply Z_mod_mult. }
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (xr_set_extra FF))).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 FF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9, R9; apply unsigned_lit_small; lia).
  split.
  - unfold ss_xr_set. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold xr_set_region.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val segs E _ F 80 8 (SOff 32 0) FF);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M80].
      * apply (chunk_ok_val segs E _ F 96 8 (SOff 33 0) (SB + FF / 8));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M96].
    + apply pairwise_disjoint_of_extents.
      unfold xr_set_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U9. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [xr_set_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U9, E32, E33, E34, !unsigned_lit_small by (unfold SB in *; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end;
        try (unfold SB in *; lia); try exact HF32; try exact HF16.
  - unfold sh_ok, XRbx2. constructor.
Qed.

Lemma lx_reset : lx_reset_S B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP.
Proof.
  unfold lx_reset_S.
  intros cx m A fpos ly3 S3 W regs mem md k HB R2 R9 R8 R3 R4 HJ HFR HFL HMOD HSEP HIN HMOK Mat HA Mgnout HROM.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (F := lf_F cx) in *.
  assert (HFb : 2 ^ 46 <= F /\ F + 320 <= 2 ^ 47 /\ F mod 32 = 0).
  { destruct HB as (_ & HPRE). pose proof (proj1 HPRE) as HAFN.
    pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
    pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
    unfold F, lf_F. set (sp0 := spZ (c_regs cx)) in *.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    split; [| split].
    - revert Hceil Hslo Hshi H47 Hmb C1 C2 C3 C4 C5. unfold LLVMF_STK. clear. intros. lia.
    - revert Hslo Hshi H47 Hmb. unfold LLVMF_STK. clear. intros. lia.
    - rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  destruct HFb as (HFlo & HFhi & HF32).
  destruct (xr_at_entry W regs mem F A HFlo HFhi HF32 R2 R9 Mat HA) as [HS SHOK].
  remember (Eimg (Ereg regs (xr_at_extra A))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 A) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (HAE : env_agree 32 (Ereg regs (xr_at_extra A)) E)
    by (rewrite HE; split; [intros mm Hmm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Usp : bv_unsigned (ew E 2) = F) by (rewrite E2, R2; apply unsigned_lit_small; lia).
  clear HE.
  unfold cfg_at. change (w64 (BASE + AX_done)) with (Z_to_bv 64 (BASE + AX_done)).
  paj_run_to_tok RUNTO HS HJ SHOK XRspan AF_fr_check_shape_done.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Emeq end.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs (xr_at_extra A) xr_kept0 HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  rewrite Emeq in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  destruct (xr_F_bounds cx HB) as (HFlo' & HFsp & Hsp47 & _ & _ & HFsp2).
  change (lf_F cx) with F in HFlo', HFsp, HFsp2.
  set (sp0 := spZ (c_regs cx)) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hlen : length (lm_hs m) = 4%nat) by (destruct HMOD as (Hl & _); exact Hl).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (destruct HB as (_ & (_ & _ & _ & _ & _ & HN & _)); exact HN).
  assert (Hsp1 : spZ (ms_regs ms) = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(unfold xr_kept0; xr_in)), R2; apply unsigned_lit_small; lia).
  destruct (lx_afn_pre_at B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP HG cx ly3 S3 fpos k W mem mdc (ms_regs ms) CSD_STK
    HB HJ HFR Hsp1) as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(unfold xr_kept0; xr_in)). exact R3. }
  { rewrite (KR 4%bv ltac:(unfold xr_kept0; xr_in)). exact R4. }
  { rewrite (KR 8%bv ltac:(unfold xr_kept0; xr_in)). exact R8. }
  { unfold CSD_STK. lia. }
  { unfold CSD_STK, LLVMF_STK. lia. }
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof (proj1 HJi) as HAR.
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  (* check_shape_done(at) *)
  eapply SRr_bind.
  { exact (CSD W ly3 S3 (ms_regs ms) mem mdc ch A HPREc ltac:(rewrite Q10, E32; reflexivity) HA Mgnout). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HA0 & HPRES2).
  rewrite Hsp1 in HJc.
  clear HS SHOK HF HFr HG0.
  assert (HJc0 : ajournal_gx segs B [] 0 [] CSD_STK F [] ly3 S3 W mem mdc [] ly3 S3 W2 mem2 md2 0)
    by (apply ajournal_gx_nil; exact HJc).
  pose proof (ajournal_gx_G_mono segs B [] G_fr 0 [] CSD_STK F [] ly3 S3 W mem mdc [] ly3 S3 W2 mem2 md2 0
    (fun a Ha => False_ind _ (inG_nil a Ha)) HJc0) as HJc'.
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc k
     CSD_STK F 0 [] [] [] ly3 S3 W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CSD_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (HK : xr_kb [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2).
  { apply (xr_kb_of_j [] [] CSD_STK F sp0 FF fpos ly3 S3 W mem mdc ly3 S3 W2 mem2 md2 0 (ablocks B ly3 S3)
      (gx_ok_nil segs B) HJc0 HAR (Permutation_refl _) (Permutation_refl _)
      (* the kit's csd_spec post (fb28b53a2b8 lib/B/W_contract.v) pairs the presence clause with an
         errno-view clause, so the presence half is its first projection *)
      (fun a _ _ _ Hp => proj1 HPRES2 a Hp));
      [unfold CSD_STK; lia | unfold CSD_STK, LLVMF_STK in *; lia | lia | exact Hin1 | reflexivity]. }
  pose proof (ajournal_gx_AR segs B [] 0 [] CSD_STK F [] ly3 S3 W mem mdc [] ly3 S3 W2 mem2 md2 0 HJc0) as HAR2.
  destruct (ERR ly3 S3 W2 mem2 md2 HAR2) as ((ev0 & Hev & Hevr) & Hevw).
  assert (HMOD1 : amodel_at B ly3 S3 W2 mem2 (xr_mid m 0 ev0))
    by exact (xr_model_keep m 0 (ct_ev (lm_c m)) ev0 FF F sp0 ly3 S3 W mem mdc ly3 S3 W2 mem2 ltac:(lia) Hlen HAR
                (xr_mid0 _ _ _ _ _ HMOD) HK Hev Hevw Hevr).
  assert (HIN1 : ainput_at B cx ly3 S3 W2 mem2)
    by exact (xr_ainput_kept cx [] [] FF F sp0 ly3 S3 W mem ly3 S3 W2 mem2 HIN (eq_sym HlenP) (fun b _ H => H) HK).
  assert (HFR1 : bx_frame cx FF W2 mem2)
    by exact (xr_bxframe_kept cx FF [] [] ly3 S3 W mem ly3 S3 W2 mem2 HFR HK HFsp).
  assert (HFL1 : sv8 W2 mem2 (FF + 120) (flag_addr ly3 1 fpos)).
  { pose proof HK as (_ & _ & _ & KF). apply (xr_sv8_kept W W2 mem mem2); [|exact HFL].
    intros x Hx. apply KF. left. lia. }
  assert (HROM1 : rom_view segs W2 mem2).
  { eapply ajournal_gx_rom_view;
      first [exact HJc0 | exact (xr_rom_out_sub [] (fun a Ha => False_ind _ (inG_nil a Ha))) | exact HROM | exact LAWS
            | exact pa_segs_low]. }
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r xr_kept0 -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (xr_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  (* 0x84ff0: the loop's set-up (g_s, g_s + 384, the fake frame's two slots) *)
  pose proof HFR1 as (_ & _ & _ & _ & _ & _ & _ & _ & M80 & M96 & _).
  destruct (frames_bounds segs B LAWS ly3 S3 W mem mdc 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  replace (fs_frame_bytes 1) with 128 in HFF1 by reflexivity. fold FF in HFF0, HFF1.
  pose proof (Z.div_mod FF 8 ltac:(lia)) as HD8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HM8.
  (* the return from check_shape_done: AX_resets = 0x2cac = 11436 from BASE (0x84ff0) *)
  rewrite Q1. change (Z_to_bv 64 (BASE + 11436)) with (Z_to_bv 64 (BASE + AX_resets)).
  assert (R2' : getr regs2 2 = w64 F) by (rewrite (RR 2%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R2).
  assert (R9' : getr regs2 9 = w64 F) by (rewrite (RR 9%bv ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R9).
  destruct (xr_set_entry W2 regs2 mem2 F FF HFlo HFhi HF32 R2' R9' M80 M96 ltac:(lia) ltac:(unfold SB; lia))
    as [HSb SHOKb].
  remember (Eimg (Ereg regs2 (xr_set_extra FF))) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 (xr_set_extra FF)) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb32 : ew Eb 32 = Z_to_bv 64 FF)
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (Eb33 : ew Eb 33 = Z_to_bv 64 (SB + FF / 8))
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  clear HEb.
  paj_run_to_tok RUNTO HSb HJ2 SHOKb XRspan AX_reset_loop.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lazymatch type of HF with frame_of ?E0 ?rs ?m ?m' =>
    pose proof (frame_of_read_only E0 rs m m' ltac:(vm_compute; reflexivity) HF) as Em2 end.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (xr_set_extra FF) xr_kept_set HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  prreg HSb (18%bv : bv 5) Q18. prreg HSb (19%bv : bv 5) Q19. prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (24%bv : bv 5) Q24.
  pmkst HSb.
  rewrite Em2 in *.
  (* the loop head of the first trip; g_s is image atom 260 = A_OBJ 19 (lib/B/W_bx_defs.v AX_g_s, 0x5d8e60) *)
  assert (U260 : bv_unsigned (ew Eb 260) = rg_s fr_RG).
  { rewrite (HEIb 260%nat ltac:(split; [apply Nat.leb_le | apply Nat.ltb_lt]; vm_compute; reflexivity)).
    vm_compute. reflexivity. }
  assert (KS : forall r : bv 5, In r xr_kept_set -> acallee_saved (bv_unsigned r) -> In r xr_kept0 ->
      getr (ms_regs ms0) r = getr regs r) by (intros r H1 H2 H3; rewrite (KR2 r H1); exact (RR r H2 H3)).
  destruct HSEP as [(rest0 & HP0) HSEP2].
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
    assert (Hinv0 : xr_inv cx m fpos ly3 S3 0 W2 (cfg_at segs (BASE + AX_reset_loop) r mem2 d)) end.
  { do 3 eexists. exists ly3, S3, k, ev0.
    split; [reflexivity|]. split; [exact HJ2|]. split; [reflexivity|]. split; [exact HFR1|]. split; [exact HFL1|].
    split; [rewrite (KR2 2%bv ltac:(unfold xr_kept_set; xr_in)); exact R2'|].
    split; [rewrite (KR2 9%bv ltac:(unfold xr_kept_set; xr_in)); exact R9'|].
    split; [rewrite (KS 8%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R8|].
    split; [rewrite (KS 3%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R3|].
    split; [rewrite (KS 4%bv ltac:(unfold xr_kept_set; xr_in) ltac:(xr_cs) ltac:(unfold xr_kept0; xr_in)); exact R4|].
    split.
    { rewrite Q19, <- (Z_to_bv_bv_unsigned _ (ew Eb 260)), U260. unfold w64, xr_HA. f_equal. all: lia. }
    split.
    { rewrite Q18, U260. unfold w64, xr_HA, ASRC. f_equal. all: lia. }
    split; [rewrite Q20, Eb32; reflexivity|].
    split; [rewrite Q24, Eb33; reflexivity|].
    split; [exact HMOD1|]. split; [intros rest Hr; exact Hr|]. split; [exact HIN1|]. split; [exact HROM1|].
    split; [exact (mo_le_refl MT MLM S3)|].
    destruct (xr_cost_all (lm_hs m) Hlen) as [Hc0 _]. rewrite Hc0. exact HMOK. }
  (* the four trips, and the block's post at 0x85014 *)
  eapply SRr_bind; [exact (xr_loop cx m fpos ly3 S3 HB Hlen (ex_intro _ rest0 HP0) HSEP2 4 0 W2 _ eq_refl Hinv0)|].
  intros W' c' _ Hinv4. apply SRr_ret. exact (xr_post cx m fpos ly3 S3 W' c' Hlen (ex_intro _ rest0 HP0) HSEP2 Hinv4).
Qed.
End lx.
