(* Reader walk kit: the reader statements' data premises (FSH_Fn_reader.v rnode / pobj / rd_blocks_ok, FSH_Gen.v
   fs_rblock) carried across a memory change that keeps every byte below alloc_ceiling (same_below m m' alloc_ceiling,
   FSW_K.v), e.g. from a function's entry to a program call after a prologue that writes only its frame, or from a
   call's return to the final ret. Every heap block lies below alloc_ceiling by AR's blocks law (Reusable/YG0d.v:422-428)
   and every fake frame by the frames bounds (Reusable/YCbq.v frames_bounds), so the AR premise of each lemma is at ANY
   memory of the same layout and state (the blocks and frames do not depend on memory). The shadow bytes of an object
   below alloc_ceiling lie below it too (SHADOW_OFF + a / 8 < alloc_ceiling). The same premises are also carried across a
   PROGRAM call whose post is a journal (YCbq.v ajournal, own = []): pobj_kept_call, rnode_kept_call, rtree_kept_call,
   rd_blocks_ok_kept_call, fs_rblock_kept_call, cstr_ok_kept_call, over the byte lemmas fsw_journal_kept_byte / fsw_journal_kept_shadow;
   the objects lie off fs's image and off the shadow (fsw_*_off_img / fsw_*_off_shadow).
   Owner: a Theorem Labs lane (reader lane), per the walk-kit layout (FSH_Fn_FORM.md); imports FSW_K and FSH_Fn_reader, copies
   none of their lemmas. The released lib/Prog PjStruct is Required, never Imported (shadowed-name rule); so are AF0x,
   ALLOC's string kit FSW_strkit and Reusable/YG0s (fsw_afobj_hull's frame alignment).
   A kit: no function's contract is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* a restricted byte below alloc_ceiling is kept by same_below *)
Lemma fsw_mrestrict_belowZ : forall (H : word -> bool) m m' a, same_below m m' alloc_ceiling -> 0 <= a < alloc_ceiling ->
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof. intros H m m' a Hs Ha. unfold mrestrict. rewrite (Hs a Ha). reflexivity. Qed.
Lemma fsw_mrestrict_below : forall (H : word -> bool) m m' (x : word), same_below m m' alloc_ceiling ->
  bv_unsigned x < alloc_ceiling -> mrestrict H m' x = mrestrict H m x.
Proof.
intros H m m' x Hs Hx. pose proof (u64_range x) as Hr.
assert (E : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite E. apply fsw_mrestrict_belowZ; [exact Hs | lia].
Qed.
(* an address below alloc_ceiling has its shadow byte below it *)
Lemma fsw_shadow_below : forall a, 0 <= a < alloc_ceiling -> 0 <= shadow_of_addr SHADOW_OFF a < alloc_ceiling.
Proof.
intros a Ha. pose proof asan_consts as (C1 & _). unfold shadow_of_addr, SHADOW_OFF in *.
Z.div_mod_to_equations. lia.
Qed.
Lemma fsw_range_addressable_below : forall (H : word -> bool) m m' p n, same_below m m' alloc_ceiling ->
  0 <= p -> p + n <= alloc_ceiling ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF p n -> range_addressable (aview tfibsegs H m') SHADOW_OFF p n.
Proof.
intros H m m' p n Hs Hp Hn Hr x Hx. destruct (Hr x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
rewrite (aview_below H m m' alloc_ceiling _ Hs (fsw_shadow_below x ltac:(lia))). exact Es.
Qed.
Lemma fsw_writable_below : forall (H : word -> bool) m m' a, same_below m m' alloc_ceiling -> 0 <= a < alloc_ceiling ->
  writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m') a.
Proof.
intros H m m' a Hs Ha Hw. apply (writable_at_eq tfibsegs (mrestrict H m) (mrestrict H m') a); [|exact Hw].
apply fsw_mrestrict_belowZ; assumption.
Qed.

(* where the reader's objects lie: heap blocks and fake frames, all below alloc_ceiling (AR at any memory) *)
Lemma fsw_ablock_low : forall B ly S (W : world tfibsegs) mx md p n, AR tfibsegs B ly S W mx md ->
  In (p, n) (ablocks B ly S) -> 4096 <= p /\ p + req_size n <= alloc_ceiling /\ n <= req_size n.
Proof.
intros B ly S W mx md p n HAR Hin.
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md p n HAR Hin) as (_ & H4096 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as (_ & Hr). auto.
Qed.
Lemma fsw_rblock_low : forall B ly S (W : world tfibsegs) mx md m p n, AR tfibsegs B ly S W mx md ->
  fs_rblock tfibsegs B ly S W m p n -> 4096 + HEAD <= p /\ p + n <= alloc_ceiling.
Proof.
intros B ly S W mx md m p n HAR (Hin & _ & Hn & _).
destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (H1 & H2 & H3). unfold HEAD in *. lia.
Qed.
Lemma fsw_pobj_low : forall B ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof.
intros B ly S W mx md m v HAR ([((cid & pos & Hin & Hc & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)] & _).
- destruct (frames_bounds tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md cid pos HAR Hin) as (F1 & F2 & _). lia.
- destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3). unfold HEAD in *. lia.
Qed.
(* the shadow hull of an object of n bytes at o inside a LIVE FAKE FRAME of frames S is visible: the frame arm of the
   hull premise the ASan memset / memcpy intrinsics take (Reusable/YG0d.v:309-310 shadow_hull_vis, whose first cell is
   shadow_addr o rounded DOWN to a multiple of 8, and whose last ends the cell of shadow_addr (o + n - 1)). The heap
   arm is Reusable/YCbq.v:1981 shadow_hull_vis_of_block and this mirrors its shape. The rounding reaches no cell below
   the frame's own shadow: a frame is 64-aligned and a whole number of 64-byte units (Reusable/YG0s.v:442 frame_facts;
   al_frames gives only mod 32, under which shadow_addr (frame_addr ly cid pos) could sit 4 bytes above a cell
   boundary), so shadow_addr (frame_addr ly cid pos) is 8-aligned and every cell of the hull is a shadow byte of the
   frame, present by al_frames. Port of ACem.v:192-226 (frame_al64 and shadow_hull_vis_of_frame), inlined at tfibsegs.
   Users: the __asan_memset of a pobj in a fake frame (pj_parse 0x82ee8, pj_object 0x83cc4, pj_string 0x83c14,
   pj_set 0x8394c), whose placement premise FSH_Fn_reader.fs_afobj gives In (cid, pos) (frames S) with these bounds *)
Lemma fsw_afobj_hull : forall B ly S (W : world tfibsegs) mem md cid pos o n, AR tfibsegs B ly S W mem md ->
  In (cid, pos) (frames S) -> frame_addr ly cid pos <= o -> o + n <= frame_addr ly cid pos + fs_frame_bytes cid ->
  0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) o n.
Proof.
intros B ly S W mem md cid pos o n HAR Hin Hfo Hon Hn s Hs.
assert (A64 : frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid).
{ pose proof HAR as HARm. destruct HARm as [M _].
  destruct (YG0s.frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
  unfold frame_addr, page_aligned in *. split; [|split; [exact Hb | exact H64]].
  rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
  replace (ly_F ly) with (64 * (ly_F ly / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
  rewrite Z.mul_comm. apply Z_mod_mult. }
destruct A64 as (Hal & Hbal & Hb64).
destruct (al_frames tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md cid pos HAR Hin) as (_ & _ & _ & Hsh).
set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1;
  replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1;
  replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (Hsf : shadow_addr f = 8 * (268431360 + f / 64)) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (L1 : shadow_addr f <= shadow_addr o / 8 * 8).
{ pose proof (shadow_mono f o Hfo) as M1. rewrite Hsf. rewrite Hsf in M1.
  assert (268431360 + f / 64 <= shadow_addr o / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (L2 : shadow_addr (o + n - 1) / 8 * 8 + 8 <= shadow_addr f + bs / 8).
{ assert (M2 : shadow_addr (o + n - 1) < shadow_addr f + bs / 8).
  { unfold shadow_addr in *. assert ((o + n - 1) / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
  rewrite Hsf, E8b in M2. rewrite Hsf, E8b.
  assert (shadow_addr (o + n - 1) / 8 < 268431360 + f / 64 + bs / 64) by (apply Z.div_lt_upper_bound; lia). lia. }
specialize (Hsh (s - shadow_addr f) ltac:(lia)). replace (shadow_addr f + (s - shadow_addr f)) with s in Hsh by lia.
apply (aview_some_of_apresent tfibsegs). exact (proj1 Hsh).
Qed.
(* the reader's objects lie off fs's image [0x10000, FS_IMG_END): the layout's image zone covers [0x10000, FS_IMG_END)
   (AF0x.v img_cover_of_ledger: it holds fs's first and last PT_LOAD) and no client byte lies in it (AR_client_img_law);
   the donor's blk_off_img / frm_off_img (ACeh.v) say the same but ACeh does not build (ACej.v:30). They lie off the
   shadow [SHADOW_OFF, SHADOW_OFF + 2^44) = [0x7fff8000, kHighMemBeg) too: in_app puts each block / frame below
   kLowShadowBeg or at kHighMemBeg and above *)
Lemma fsw_client_off_img : forall B ly S (W : world tfibsegs) mx md lo len, AR tfibsegs B ly S W mx md -> 0 < len ->
  (forall a, lo <= a < lo + len -> ~ in_zr a (ly_img ly)) -> lo + len <= 0x10000 \/ FS_IMG_END <= lo.
Proof.
intros B ly S W mx md lo len (M & L & _) Hl Hc.
pose proof (AF0x.img_cover_of_ledger ly S md L) as [C1 C2]. unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END in C1, C2.
destruct (Z_le_gt_dec (lo + len) 0x10000) as [|H1]; [left; lia|].
destruct (Z_le_gt_dec FS_IMG_END lo) as [|H2]; [right; lia|]. exfalso.
apply (Hc (Z.max lo 0x10000)); [lia|]. unfold in_zr, FS_IMG_END in *. lia.
Qed.
Lemma fsw_ablock_off_img : forall B ly S (W : world tfibsegs) mx md p n, AR tfibsegs B ly S W mx md -> In (p, n) (ablocks B ly S) -> p + req_size n <= 0x10000 \/ FS_IMG_END <= p.
Proof.
intros B ly S W mx md p n HAR Hin.
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as (Hr & _).
apply (fsw_client_off_img B ly S W mx md p (req_size n) HAR ltac:(lia)).
intros a Ha. refine (proj1 (al_client_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md a HAR _)).
left. exists p, n. split; [exact Hin | exact Ha].
Qed.
Lemma fsw_ablock_off_shadow : forall B ly S (W : world tfibsegs) mx md p n, AR tfibsegs B ly S W mx md -> In (p, n) (ablocks B ly S) -> forall a, p <= a < p + req_size n -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros B ly S W mx md p n HAR Hin a Ha.
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md p n HAR Hin) as (_ & _ & _ & Happ & _).
pose proof (in_app_addr p (req_size n) a Happ Ha) as Hx. unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma fsw_pobj_off_img : forall B ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m v -> v + 56 <= 0x10000 \/ FS_IMG_END <= v.
Proof.
intros B ly S W mx md m v HAR HP.
apply (fsw_client_off_img B ly S W mx md v 56 HAR ltac:(lia)).
intros a Ha. refine (proj1 (al_client_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md a HAR _)).
destruct HP as [[((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)] _].
- right. left. exists cid, pos. split; [exact Hin | lia].
- left. exists b, n. split; [exact Hin | unfold HEAD in H1; lia].
Qed.
Lemma fsw_pobj_off_shadow : forall B ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m v -> forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros B ly S W mx md m v HAR ([((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)] & _) a Ha.
- destruct (frames_bounds tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md cid pos HAR Hin) as (_ & _ & Happ).
  pose proof (in_app_addr _ _ a Happ ltac:(lia)) as Hx. unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- apply (fsw_ablock_off_shadow B ly S W mx md b n HAR Hin a). unfold HEAD in H1. lia.
Qed.

(* ---- the data premises across same_below m m' alloc_ceiling ---- *)
Lemma fs_rblock_below : forall B ly S (W : world tfibsegs) mx md m m' p n, AR tfibsegs B ly S W mx md ->
  same_below m m' alloc_ceiling -> fs_rblock tfibsegs B ly S W m p n -> fs_rblock tfibsegs B ly S W m' p n.
Proof.
intros B ly S W mx md m m' p n HAR Hs Hb. pose proof Hb as (Hin & Hal & Hn & Hv).
destruct (fsw_ablock_low B ly S W mx md _ _ HAR Hin) as (A1 & A2 & A3).
split; [exact Hin|]. split; [exact Hal|]. split; [exact Hn|].
apply (val_mem_below (w_H W) m m' alloc_ceiling (p - HEAD) 8 n Hs); [unfold HEAD in *; lia | | exact Hv].
change (Z.of_nat 8) with 8. unfold HEAD in *. lia.
Qed.
Lemma rd_blocks_ok_below : forall B ly S (W : world tfibsegs) mx md m m' UL, AR tfibsegs B ly S W mx md ->
  same_below m m' alloc_ceiling -> rd_blocks_ok tfibsegs B ly S W m UL -> rd_blocks_ok tfibsegs B ly S W m' UL.
Proof.
intros B ly S W mx md m m' UL HAR Hs H a k Hak. exact (fs_rblock_below B ly S W mx md m m' a k HAR Hs (H a k Hak)).
Qed.
Lemma rnode_below : forall B ly S (W : world tfibsegs) mx md m m' UL v t D, AR tfibsegs B ly S W mx md ->
  same_below m m' alloc_ceiling -> 0 <= v -> v + 56 <= alloc_ceiling ->
  rnode tfibsegs B ly S W m UL v t D -> rnode tfibsegs B ly S W m' UL v t D.
Proof.
intros B ly S W mx md m m' UL v t D HAR Hs Hv0 Hv1 (HN & HB & HI).
split; [|split; [exact (rd_blocks_ok_below B ly S W mx md m m' UL HAR Hs HB) | exact HI]].
apply (PjStruct.pj_node_frame tfibsegs t (mrestrict (w_H W) m) (fun a k => In (a, k) UL)
  (mrestrict (w_H W) m') (fun a k => In (a, k) UL) v D HN); [intros a k Hak; exact (HI _ Hak)|].
intros x Hx. apply (fsw_mrestrict_below (w_H W) m m' x Hs).
destruct Hx as [Hx|((a & k) & Hb & Hx)]; [lia|].
destruct (fsw_rblock_low B ly S W mx md m a k HAR (HB a k (HI _ Hb))) as (R1 & R2).
unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx. lia.
Qed.
Lemma pobj_below : forall B ly S (W : world tfibsegs) mx md m m' v, AR tfibsegs B ly S W mx md ->
  same_below m m' alloc_ceiling -> pobj tfibsegs B ly S W m v -> pobj tfibsegs B ly S W m' v.
Proof.
intros B ly S W mx md m m' v HAR Hs HP.
destruct (fsw_pobj_low B ly S W mx md m v HAR HP) as (L1 & L2).
destruct HP as [Hpl Hw]. split.
- destruct Hpl as [(Hf & Ha & Hr)|(Hb & Ha & Hr)]; [left | right].
  + split; [exact Hf|]. split; [exact Ha|].
    exact (fsw_range_addressable_below (w_H W) m m' v 56 Hs ltac:(lia) L2 Hr).
  + split; [exact Hb|]. split; [exact Ha|].
    exact (fsw_range_addressable_below (w_H W) m m' v 56 Hs ltac:(lia) L2 Hr).
- intros i Hi. apply (fsw_writable_below (w_H W) m m' (v + i) Hs ltac:(lia)). exact (Hw i Hi).
Qed.

(* ---- the data premises across a PROGRAM call: the callee's post is the journal ajournal (YCbq.v:349-371) from the caller's
   (lyc, Sc, W, unpoison Uc memc) to (ly', S', W', unpoison U' mem') with own = []. The journal keeps the bytes (not the
   shadow bytes) of a block live at both ends, and the bytes and shadow bytes of a fake frame live before, each byte off
   FP1; a block it frees lies in FP1 (so a block with one byte off FP1 survives). The predicates read the RAW memories:
   a block / frame byte is no shadow byte, so unpoison leaves it (ARU at both ends; ARU after is the journal's AR with
   upoison_ok / upoisoned after). ---- *)
Lemma fsw_journal_block_live : forall B STK1 sp1 FP1 lyc Sc (W : world tfibsegs) mc mdc ly' S' W' m' md' kc p n a,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W mc mdc [] ly' S' W' m' md' kc ->
  In (p, n) (ablocks B lyc Sc) -> p <= a < p + req_size n -> ~ inFP FP1 a -> In (p, n) (ablocks B ly' S').
Proof.
intros B STK1 sp1 FP1 lyc Sc W mc mdc ly' S' W' m' md' kc p n a HJ Hin Ha Hf.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfree & _).
assert (Dec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (in_dec Dec (p, n) (ablocks B ly' S')) as [H|H]; [exact H|]. exfalso.
apply Hf. replace a with (p + (a - p)) by lia. apply (Hfree p n (a - p) Hin H). lia.
Qed.
(* an application byte is no user-poisoned shadow byte (FSupoison.v ARU_mem_low below the shadow, FSW_K.v
   fsw_unpoison_high above it) *)
Lemma fsw_unpoison_app : forall B ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) -> unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros B ly S U W mem md a H Ha Hn. destruct (Z_lt_le_dec a SHADOW_OFF) as [Hl|Hg].
- apply (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 a) H). rewrite (wz a Ha). exact Hl.
- apply (fsw_unpoison_high B ly S U W mem md a H). unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
(* off the image a byte's view fixes the byte (AD25.v restrict_of_aview states it too; AD25 loads AE2k, so not used) *)
Lemma fsw_restrict_of_aview : forall (H H' : word -> bool) m m' a, 0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  aview tfibsegs H' m' a = aview tfibsegs H m a -> mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn X. pose proof (YCbq.mbyte_of_aview tfibsegs H H' m m' a X) as E. unfold mbyte in E.
rewrite (YCbq.seg_rom_none tfibsegs a Ha Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 a)), (mrestrict H m (Z_to_bv 64 a)); congruence.
Qed.
(* (a) a byte of a block live before or of a fake frame live before, off FP1, is kept: in the unpoisoned memories (the
   journal's own form) and in the raw ones (it is no shadow byte, below alloc_ceiling and off the callee's window) *)
Lemma fsw_journal_kept_byte : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc x,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  ((exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= x < p + req_size n) \/
   (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
  ~ inFP FP1 x ->
  aview tfibsegs (w_H W') (unpoison U' mem') x = aview tfibsegs (w_H W) (unpoison Uc memc) x /\
  mrestrict (w_H W') mem' (Z_to_bv 64 x) = mrestrict (w_H W) memc (Z_to_bv 64 x).
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' Hx Hf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & Hblk & _ & Hfrm & _).
pose proof HU as (HARc & _ & _).
assert (HU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR'|]; split; [exact HO' | exact HP']).
assert (E1 : aview tfibsegs (w_H W') (unpoison U' mem') x = aview tfibsegs (w_H W) (unpoison Uc memc) x).
{ destruct Hx as [(p & n & Hin & Hr)|(cid & pos & Hin & Hr)].
  - pose proof (fsw_journal_block_live B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc
      p n x HJ Hin Hr Hf) as Hin'.
    replace x with (p + (x - p)) by lia. apply (Hblk p n (x - p) Hin Hin'); [lia|]. replace (p + (x - p)) with x by lia. exact Hf.
  - apply (Hfrm cid pos x Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hf]. }
split; [exact E1|].
assert (CL : ~ in_zr x (ly_img lyc) /\ ~ in_img tfibsegs x).
{ apply (al_client_img tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc x HARc).
  destruct Hx as [(p & n & Hin & Hr)|(cid & pos & Hin & Hr)]; [left; exists p, n; auto | right; left; exists cid, pos; auto]. }
assert (AP : app_addr x).
{ destruct Hx as [(p & n & Hin & Hr)|(cid & pos & Hin & Hr)].
  - destruct (al_blocks tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc p n HARc Hin) as (_ & _ & _ & Happ & _).
    exact (in_app_addr _ _ x Happ Hr).
  - destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc cid pos HARc Hin) as (_ & _ & Happ).
    exact (in_app_addr _ _ x Happ Hr). }
pose proof (app_addr_below_ceil x AP) as AC. pose proof ASAN_CEIL_range as [CR _].
assert (NS : ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) by (unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in AP |- *; lia).
apply (fsw_restrict_of_aview (w_H W) (w_H W') memc mem' x ltac:(lia) (proj2 CL)).
rewrite (aview_at tfibsegs (w_H W') mem' (unpoison U' mem') x (eq_sym (fsw_unpoison_app B ly' S' U' W' mem' md' x HU' ltac:(lia) NS))).
rewrite (aview_at tfibsegs (w_H W) memc (unpoison Uc memc) x (eq_sym (fsw_unpoison_app B lyc Sc Uc W memc mdc x HU ltac:(lia) NS))).
exact E1.
Qed.
(* the shadow byte of x is in no U range when every range is a 16-byte head (q, 16), q 8-aligned, not holding x *)
Lemma fsw_head_ush_out : forall (U : list (Z * Z)) x, 0 <= x ->
  (forall r, In r U -> snd r = 16 /\ fst r mod 8 = 0 /\ ~ (fst r <= x < fst r + 16)) ->
  in_ush U (shadow_of_addr SHADOW_OFF x) = false.
Proof.
intros U x Hx HU. destruct (in_ush U (shadow_of_addr SHADOW_OFF x)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hs). destruct (HU r Hr) as (E16 & Q8 & Nx).
rewrite E16 in Hs. unfold shadow_addr, shadow_of_addr in Hs.
apply Z.mod_divide in Q8 as [k Hk]; [|lia]. rewrite Hk in Hs, Nx.
Z.div_mod_to_equations. lia.
Qed.
(* the body of a live block past its 16-byte head is addressable on the MACHINE's memory: AR (over the unpoisoned memory)
   makes its granules addressable (YCbq.range_addressable_of_block), and no head of U covers them, because each head is
   the start of a live block (FSupoisonU.fs_heads) and live blocks are pairwise disjoint (AR_blocks_law). Moved here
   from the pj_get_str walk (a working branch 145a2f0cc88 FSW_pj_get_str.v pgs_body_addressable), same statement *)
Lemma fsw_block_body_addressable : forall B ly S U (W : world tfibsegs) mem md P n z len,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (P, n) (ablocks B ly S) -> P + 16 <= z -> 0 <= len -> z + len <= P + req_size n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF z len.
Proof.
intros B ly S U W mem md P n z len HARU FH Hin Hz Hl Hn.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (YCbq.range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P n z len HAR Hin ltac:(lia) Hn)
  as HRA.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P n HAR Hin) as (HP16 & HP4096 & HPc & _ & _ & PW & _).
pose proof asan_consts as (C1 & _).
intros x Hx. destruct (HRA x Hx) as (s & Es & Hok). exists s. split; [|exact Hok].
assert (NI : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
{ rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply fsw_head_ush_out; [lia|]. intros (h & q) Hr. cbn [fst snd].
  destruct (FH (h, q) Hr) as (E16 & m & Hm & M16). cbn [fst snd] in E16, Hm. subst q.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m HAR Hm) as (Hh16 & _).
  split; [reflexivity|].
  split; [apply Z.mod_divide in Hh16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((k * 2) * 8) by lia; apply Z_mod_mult|].
  destruct (Z.eq_dec h P) as [->|NE]; [lia|].
  assert (I1 : In (h, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
    by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (h, m)); exact Hm).
  assert (I2 : In (P, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
    by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (P, n)); exact Hin).
  destruct (FSupoisonU.pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E; injection E; intros _ E'; exact (NE E')))
    as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ NI). exact Es.
Qed.
(* the raw shadow byte of x is kept, x past the head of a block live before and off FP1, or in a fake frame live before:
   the frame's shadow byte by the journal (it is off FP1: FP1 holds no shadow byte), the block's by AR's shadow law at both
   ends (same block, same value); raw = unpoisoned since U' holds heads only (fs_heads) and x's shadow byte is not Uc's *)
Lemma fsw_journal_kept_shadow : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc x,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) -> FSupoisonU.fs_heads B ly' S' U' ->
  ((exists b n, In (b, n) (ablocks B lyc Sc) /\ b + HEAD <= x < b + req_size n /\ ~ inFP FP1 x) \/
   (exists cid pos, In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid)) ->
  in_ush Uc (shadow_of_addr SHADOW_OFF x) = false ->
  aview tfibsegs (w_H W') mem' (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x).
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' HFsh HH Hx HUc.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (HAR' & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & Hfrm & _).
pose proof HU as (HARc & _ & _).
pose proof asan_consts as (C1 & _).
destruct (al_layout tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc ly' HARc Hly) as (_ & HFA & _).
assert (XB : 4096 <= x < alloc_ceiling).
{ destruct Hx as [(b & n & Hin & Hr & _)|(cid & pos & Hin & Hr)].
  - destruct (fsw_ablock_low B lyc Sc W (unpoison Uc memc) mdc b n HARc Hin) as (A1 & A2 & _). unfold HEAD in Hr. lia.
  - destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc cid pos HARc Hin) as (F1 & F2 & _). lia. }
assert (SR : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44)
  by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
assert (S64 : 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64) by (unfold SHADOW_OFF in SR |- *; lia).
(* after: U' holds heads only, none on x *)
assert (HU'out : in_ush U' (shadow_of_addr SHADOW_OFF x) = false).
{ apply fsw_head_ush_out; [lia|]. intros r Hr. destruct (HH r Hr) as (E16 & m & Hm & M16).
  destruct (al_blocks tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' (fst r) m HAR' Hm) as (Q16 & _ & _ & _ & _ & PW & _).
  split; [exact E16|].
  split; [apply Z.mod_divide in Q16 as [k Hk]; [|lia]; rewrite Hk; replace (k * 16) with ((k * 2) * 8) by lia; apply Z_mod_mult|].
  destruct Hx as [(b & n & Hin & Hr' & Hf)|(cid & pos & Hin & Hr')].
  - pose proof (fsw_journal_block_live B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc
      b n x HJ Hin ltac:(unfold HEAD in Hr'; lia) Hf) as Hin'.
    destruct (Z.eq_dec (fst r) b) as [Eq|Hne]; [rewrite Eq; unfold HEAD in Hr'; lia|].
    assert (I1 : In (fst r, req_size m) (map (fun b0 => (fst b0, req_size (snd b0))) (ablocks B ly' S')))
      by exact (in_map (fun b0 => (fst b0, req_size (snd b0))) _ (fst r, m) Hm).
    assert (I2 : In (b, req_size n) (map (fun b0 => (fst b0, req_size (snd b0))) (ablocks B ly' S')))
      by exact (in_map (fun b0 => (fst b0, req_size (snd b0))) _ (b, n) Hin').
    destruct (FSupoisonU.pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E; injection E; intros _ E'; exact (Hne E')))
      as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; unfold HEAD in Hr'; lia.
  - assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfr; exact Hin).
    destruct (al_sep tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' HAR') as (PS & _).
    destruct (YG0s.pairwise_app_inv zdisjoint _ _ PS) as (_ & _ & PX).
    pose proof (PX (fst r, req_size m) (frame_addr ly' cid pos, fs_frame_bytes cid)
      (in_map (fun b0 => (fst b0, req_size (snd b0))) _ (fst r, m) Hm)
      (in_map (fun f => (frame_addr ly' (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos) Hin')) as D.
    rewrite HFA in D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
(* the unpoisoned shadow byte is kept *)
assert (E1 : aview tfibsegs (w_H W') (unpoison U' mem') (shadow_of_addr SHADOW_OFF x) =
             aview tfibsegs (w_H W) (unpoison Uc memc) (shadow_of_addr SHADOW_OFF x)).
{ destruct Hx as [(b & n & Hin & Hr' & Hf)|(cid & pos & Hin & Hr')].
  - pose proof (fsw_journal_block_live B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc
      b n x HJ Hin ltac:(unfold HEAD in Hr'; lia) Hf) as Hin'.
    destruct (al_shadow tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc b n HARc Hin) as [(P8 & _ & BSc) _].
    destruct (al_shadow tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' b n HAR' Hin') as [(_ & _ & BS') _].
    assert (Es : shadow_of_addr SHADOW_OFF x = shadow_of_addr SHADOW_OFF b + (x - b) / 8).
    { unfold shadow_of_addr. apply Z.mod_divide in P8 as [k Hk]; [|lia]. rewrite Hk.
      replace (x - k * 8) with (x + (- k) * 8) by lia. rewrite Z.div_add, Z.div_mul by lia. lia. }
    assert (Hi : 0 <= (x - b) / 8 < (req_size n + 7) / 8) by (unfold HEAD in Hr'; Z.div_mod_to_equations; lia).
    rewrite Es, (BS' _ Hi), (BSc _ Hi). reflexivity.
  - destruct (al_frames tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc cid pos HARc Hin) as (F32 & _).
    pose proof (YG0s.frame_facts B lyc Sc _ cid pos (proj1 HARc) Hin) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B64 & _).
    apply (Hfrm cid pos _ Hin); [right | intros Hin2; exact (HFsh _ Hin2 SR)].
    unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
    apply Z.mod_divide in F32 as [a8 Ha8]; [|lia]. apply Z.mod_divide in B64 as [b8 Hb8]; [|lia].
    rewrite Ha8, Hb8 in Hr' |- *. Z.div_mod_to_equations. lia. }
rewrite <- (aview_unpoison_out tfibsegs (w_H W') U' mem' (shadow_of_addr SHADOW_OFF x)) by (rewrite (wz _ S64); exact HU'out).
rewrite <- (aview_unpoison_out tfibsegs (w_H W) Uc memc (shadow_of_addr SHADOW_OFF x)) by (rewrite (wz _ S64); exact HUc).
exact E1.
Qed.

(* (b) the reader's data premises across the call *)
Lemma fs_rblock_kept_call : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc p k,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall x, p - HEAD <= x < p + k -> ~ inFP FP1 x) ->
  fs_rblock tfibsegs B lyc Sc W memc p k -> fs_rblock tfibsegs B ly' S' W' mem' p k.
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc p k HJ HU HO' HP' HF (Hin & Hal & Hk & Hv).
pose proof (req_size_pos (k + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
split; [|split; [exact Hal | split; [exact Hk|]]].
- apply (fsw_journal_block_live B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc
    (p - HEAD) (k + HEAD) (p - HEAD) HJ Hin); [unfold HEAD in *; lia | apply HF; unfold HEAD; lia].
- intros j Hj.
  assert (E : mrestrict (w_H W') mem' (Z_to_bv 64 (p - HEAD + Z.of_nat j)) = mrestrict (w_H W) memc (Z_to_bv 64 (p - HEAD + Z.of_nat j))).
  { refine (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc _ HJ HU HO' HP' _ _)).
    - left. exists (p - HEAD), (k + HEAD). split; [exact Hin | unfold HEAD in *; lia].
    - apply HF. unfold HEAD. lia. }
  unfold mbyte. rewrite E. exact (Hv j Hj).
Qed.
Lemma rd_blocks_ok_kept_call : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc UL,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a k x, In (a, k) UL -> a - HEAD <= x < a + k -> ~ inFP FP1 x) ->
  rd_blocks_ok tfibsegs B lyc Sc W memc UL -> rd_blocks_ok tfibsegs B ly' S' W' mem' UL.
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc UL HJ HU HO' HP' HF HB a k Hak.
exact (fs_rblock_kept_call B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc a k HJ HU HO' HP' (fun x => HF a k x Hak) (HB a k Hak)).
Qed.
Lemma pobj_kept_call : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc v,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  (* frame shadow: the journal keeps a frame byte's shadow byte only off FP1 (YCbq.v:363-365) *)
  (forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (* upoison_ok's granule freedom: a U' range may sit on any whole live-block granule; fs_heads pins them to block heads *)
  FSupoisonU.fs_heads B ly' S' U' ->
  pobj tfibsegs B lyc Sc W memc v -> pobj tfibsegs B ly' S' W' mem' v.
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc v HJ HU HO' HP' HFv HFsh HH HPc.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (HAR' & Hly & _ & _ & _ & Hfr & _).
pose proof HU as (HARc & _ & HPUc).
destruct (al_layout tfibsegs B LAWS lyc Sc W (unpoison Uc memc) mdc ly' HARc Hly) as (_ & HFA & _).
destruct HPc as [Hpl Hw].
assert (KB : forall x, v <= x < v + 56 -> mrestrict (w_H W') mem' (Z_to_bv 64 x) = mrestrict (w_H W) memc (Z_to_bv 64 x)).
{ intros x Hx. refine (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' _ (HFv x Hx))).
  destruct Hpl as [((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)].
  - right. exists cid, pos. split; [exact Hin | lia].
  - left. exists b, n. split; [exact Hin | unfold HEAD in H1; lia]. }
assert (RA : range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF v 56 ->
             range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF v 56).
{ intros Hra x Hx. destruct (Hra x Hx) as (sv & Esv & Hok). exists sv. split; [|exact Hok].
  rewrite <- Esv. apply (fsw_journal_kept_shadow B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' HFsh HH).
  - destruct Hpl as [((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)].
    + right. exists cid, pos. split; [exact Hin | lia].
    + left. exists b, n. split; [exact Hin|]. split; [lia | exact (HFv x Hx)].
  - destruct (in_ush Uc (shadow_of_addr SHADOW_OFF x)) eqn:E; [|reflexivity]. exfalso.
    pose proof (HPUc _ E) as E247. rewrite Esv in E247. injection E247 as ->. unfold saddr_ok in Hok. lia. }
split.
- destruct Hpl as [(Hf & Ha & Hr)|(Hb & Ha & Hr)]; [left | right].
  + destruct Hf as (cid & pos & Hin & Hc & H8 & H1 & H2).
    split; [|split; [exact Ha | exact (RA Hr)]].
    exists cid, pos. rewrite (HFA cid pos). split; [rewrite Hfr; exact Hin|]. split; [exact Hc|]. split; [exact H8|]. lia.
  + destruct Hb as (b & n & Hin & H1 & H2).
    split; [|split; [exact Ha | exact (RA Hr)]].
    exists b, n. split; [|lia].
    apply (fsw_journal_block_live B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc b n v HJ Hin);
      [unfold HEAD in H1; lia | apply HFv; lia].
- intros i Hi. apply (writable_at_eq tfibsegs (mrestrict (w_H W) memc) (mrestrict (w_H W') mem') (v + i));
    [exact (KB (v + i) ltac:(lia)) | exact (Hw i Hi)].
Qed.
Lemma rnode_kept_call : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc UL v t D,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall x, v <= x < v + 56 -> ~ inFP FP1 x) ->
  (* rd_blocks_ok's head reads: it reads each UL block's head [a - HEAD, a - 8), and the UL blocks outside D *)
  (forall a k x, In (a, k) UL -> a - HEAD <= x < a + k -> ~ inFP FP1 x) ->
  (* rnode's placelessness: rnode does not say where v lies, pobj does (the journal keeps live block / frame bytes) *)
  pobj tfibsegs B lyc Sc W memc v ->
  rnode tfibsegs B lyc Sc W memc UL v t D -> rnode tfibsegs B ly' S' W' mem' UL v t D.
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc UL v t D HJ HU HO' HP' HFv HFul HPc (HN & HB & HI).
split; [|split; [exact (rd_blocks_ok_kept_call B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc UL HJ HU HO' HP' HFul HB)
                | exact HI]].
apply (PjStruct.pj_node_frame tfibsegs t (mrestrict (w_H W) memc) (fun a k => In (a, k) UL)
  (mrestrict (w_H W') mem') (fun a k => In (a, k) UL) v D HN); [intros a k Hak; exact (HI _ Hak)|].
intros x Hx.
assert (Ex : x = Z_to_bv 64 (bv_unsigned x)) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite Ex.
refine (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc (bv_unsigned x) HJ HU HO' HP' _ _)).
- destruct Hx as [Hx|((a & k) & Hb & Hx)].
  + destruct HPc as [[((cid & pos & Hin & _ & _ & H1 & H2) & _)|((b & n & Hin & H1 & H2) & _)] _].
    * right. exists cid, pos. split; [exact Hin | lia].
    * left. exists b, n. split; [exact Hin | unfold HEAD in H1; lia].
  + destruct (HB a k (HI _ Hb)) as (Hin & _ & Hk & _). unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx.
    pose proof (req_size_pos (k + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hr).
    left. exists (a - HEAD), (k + HEAD). split; [exact Hin | unfold HEAD in *; lia].
- destruct Hx as [Hx|((a & k) & Hb & Hx)]; [exact (HFv _ Hx)|].
  unfold PjStruct.pj_holds in Hx. cbn [fst snd] in Hx. apply (HFul a k _ (HI _ Hb)). unfold HEAD. lia.
Qed.
Lemma rtree_kept_call : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc v t D,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall x, v <= x < v + 56 -> ~ inFP FP1 x) ->
  (forall a k x, In (a, k) D -> a - HEAD <= x < a + k -> ~ inFP FP1 x) ->
  pobj tfibsegs B lyc Sc W memc v ->
  rtree tfibsegs B lyc Sc W memc v t D -> rtree tfibsegs B ly' S' W' mem' v t D.
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc v t D HJ HU HO' HP' HFv HFd HPc HT.
exact (rnode_kept_call B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc D v t D HJ HU HO' HP' HFv HFd HPc HT).
Qed.
(* a C string the caller keeps (FSH_Rt.cstr_kept) across the call: the block arm by ALLOC's FSW_strkit.cstr_ok_kept_blkU
   (the block survives: fsw_journal_block_live), the table arms by FSW_strkit.cstr_ok_kept_tbl at the new state *)
Lemma cstr_ok_kept_call : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc p l,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (* the string and its tail word off the footprint: the journal keeps those block bytes, and the block survives *)
  (forall a, p <= a < p + Z.of_nat (length l) + 8 -> ~ inFP FP1 a) ->
  (* block arm: nothing stops the callee's U' from gaining a head over a string at the start of a headless block *)
  (forall r, In r U' -> In r Uc \/ fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r) ->
  (* table arms: no journal clause keeps an image object's shadow bytes; fs_img_facts gives cstr_ok at any AR state *)
  fs_img_facts tfibsegs B ->
  (* table arms: fs_img_facts needs the read-only view at the new state (not from the journal: fp_spares FP1 may spare
     the sink head) *)
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') ->
  cstr_kept B lyc Sc Uc p l -> cstr_ok tfibsegs W memc p l ->
  cstr_ok tfibsegs W' mem' p l /\ cstr_kept B ly' S' U' p l.
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc p l HJ HU HO' HP' HF HU' IMG HRO' Hk Hc.
pose proof HJ as (HAR' & _).
destruct Hk as [(b & m & Hin & Hb & Hbm & HD) | Htbl].
- assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  pose proof (fsw_journal_block_live B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc ly' S' W' (unpoison U' mem') md' kc
    b m p HJ Hin ltac:(rewrite Hrq; lia) (HF p ltac:(lia))) as Hin'.
  split.
  + apply (FSW_strkit.cstr_ok_kept_blkU B STK1 sp1 FP1 lyc Sc Uc W memc mdc [] ly' S' U' W' mem' md' kc p l b m
      HU HJ HO' HP' Hin Hin' Hb Hbm); [intros a Ha; apply HF; lia | exact HU' | exact Hc].
  + left. exists b, m. split; [exact Hin'|]. split; [exact Hb|]. split; [exact Hbm|].
    intros r Hr. destruct (HU' r Hr) as [HrU | [Hd | Hd]]; [exact (HD r HrU) | right; exact Hd | left; exact Hd].
- split; [|right; exact Htbl].
  exact (FSW_strkit.cstr_ok_kept_tbl B ly' S' U' W' mem' md' p l IMG (conj HAR' (conj HO' HP')) HRO' Htbl).
Qed.
(* fs's read-only bytes (its read-only segments and the relro range [FS_RLO, FS_RHI)) are image bytes (port of a Theorem Labs lane's
   FMW_K.v roP_img on a working branch, at fs's relro) *)
Lemma fsw_roP_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FS_RLO) && (FS_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
(* the read-only view across the call (port of a Theorem Labs lane's FMW_K.v arodata_kept over fs's FP-keyed image clause, YCbq.v:362):
   a read-only byte is an image byte off FP1, which the journal keeps while the sink is closed (fp_spares_closed); it lies
   below the shadow, so unpoison leaves it at both ends (ARU before; ARU after from the journal's AR).
   arodata_kept_own: any own list of the journal (a caller holding a live fake frame at the call, e.g. CNO's own =
   [(1, pos)]; the image clause does not look at own; a Theorem Labs lane's local cno_ff_arodata,
   a working branch lib/A/FSW_check_no_overread_ffree.v:95). arodata_kept: own = [], its corollary. *)
Lemma arodata_kept_own : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc own ly' S' U' W' mem' md' kc,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc own ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (* the image clause spares the sink head only while the callee's sink is closed (fp_spares, generic SK) *)
  ~ YI16.sink_open_fp FP1 ->
  (* the image clause keeps only bytes off FP1 *)
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP1 a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc own ly' S' U' W' mem' md' kc HJ HU HO' HP' Hcl Hro HR a Ha Ho He.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR'|]; split; [exact HO' | exact HP']).
pose proof (fsw_roP_img a Ha) as Hi. pose proof (fs_segs_img a Hi) as Hl.
assert (NS : ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) by (unfold FS_IMG_END, SHADOW_OFF in *; lia).
assert (A64 : 0 <= a < 2 ^ 64) by (unfold FS_IMG_END in Hl; lia).
rewrite <- (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' a (fsw_unpoison_app B ly' S' U' W' mem' md' a HU' A64 NS)).
rewrite (F3 a Hi Ho He (Hro a Ha) (fp_spares_closed FP1 a Hcl)).
rewrite (aview_at tfibsegs (w_H W) (unpoison Uc memc) memc a (fsw_unpoison_app B lyc Sc Uc W memc mdc a HU A64 NS)).
exact (HR a Ha Ho He).
Qed.
Lemma arodata_kept : forall B STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc,
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (* the image clause spares the sink head only while the callee's sink is closed (fp_spares, generic SK) *)
  ~ YI16.sink_open_fp FP1 ->
  (* the image clause keeps only bytes off FP1 *)
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP1 a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc.
exact (arodata_kept_own B STK1 sp1 FP1 lyc Sc Uc W memc mdc [] ly' S' U' W' mem' md' kc).
Qed.
End e.
