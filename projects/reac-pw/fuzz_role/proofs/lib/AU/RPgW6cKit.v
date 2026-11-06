(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v at 021dba8dbbd; hd_intrin_at renamed cb_intrin_at and stated over image B's segments (lib/AU/Img0U.v rsegs, lib/AU/HPgSteps.v img_segs_low, AR_laws from YG0q.AR_laws_ok), hd_memset_at / hd_memcpy_at renamed cb_memset_at / cb_memcpy_at with the entry pc made a parameter (image B's entries CB_ASAN_MEMSET 0x52228 and CB_ASAN_MEMCPY 0x51d8c stated as constants). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 80bf14ccf11 (PART 1, a segment's start facts at a cut); rs_ -> cb_, restated over lib/AU/HPgSeg.v (hsu_pre, hsu_core, hsu_E1, hsu_in, hsu_fsh_at) at image B's record headamp_himg_B: the frame for locals of class 4 (1024 bytes, 128 shadow bytes), the 116-byte prologue pattern in place of role's 52, R + 0x220 in place of 0x1a0, image B's three write ranges of hi_w1, the image fact segs_low taken from lib/AU/HPgSteps.v img_segs_low instead of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 80bf14ccf11 (w6_ctx, w6_caller_saved and Section seq only; w6_in as cb_in); w6_ -> cb_, the frame (4, pos) and R + 0x220 of image B, R's cells [R, R + 0x198), and the block post w6_post replaced by the shared layer's hdu_blk_postE (lib/AU/HPgSteps.v), rl_blk_post by hdu_blk_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf11 (its generic helpers only: the list tactics, the register and location-list lemmas, the geometry of a cut, the image's first write range, the suffix and cursor lemmas, pp's image length, the cut's geometry and context, the core step, the input kept, the block step and the side tactics); w6_ -> cb_, over lib/AU/HPgSeg.v at image B: w6_geo with image B's frame (1024 / 128 bytes, R + 0x220) and the conjuncts F mod 32 = 0 and in_app pp, its head- and tail-specific cell lemmas replaced by write-set-free disjointness lemmas, w6_in_kept and the side tactics generalised over the write set, cb_blkE_step added for a block that writes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 80bf14ccf11 (w6h_div, w6h_sh_e, w6h_e_mod8, w6h_bounds, w6h_callee, w6h_val_kept, w6h_chunk0, w6h_region_nth, w6h_chunks); w6h_ -> cb_, the shadow and alignment lemmas generalised over the offset, the bounds at class 4 (1024 bytes, 128 shadow bytes) and e62's 104 bytes at F + 0x210. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at f3898085bda (w7_post,
   w7_post_of_run), RPgW7bKit.v at f3898085bda (w7_kept, w7_hull, w7_ra_kept, w7_hull_kept, w7_strok, w7_strz and
   their lemmas), RPgCfgChanges.v at f3898085bda (kept_run), RPgW6aTail.v at f3898085bda (tl_byte, tl_val_of_chunk,
   tl_val_at), RPgW6aC2h.v at f3898085bda (c2_all256, c2_envz, c2_nz, c2_notin, c2_kio) and RPgW7bIter.v at
   f3898085bda (w7_cs_bv, w7_cs_out, w7_reg_eq), by way of lib/AU/HPgW6bC1k.v's and
   HPgW6bC1.v's hb1_* copies for reac-pw/fuzz_headamp's image B: moved here and renamed cb_* by the dedup, one copy
   kept for the equal helpers of 17 lib/AU files (HPgE0Base, HPgW7bBase, HPgW7bIter, HPgW6aTail, HPgW6aC2 and
   others); cb_val_at_rng is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths and module names changed; 694 of its 806 lines of code are new or changed and 977 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6c.v at cb9cdc023f20; for the same unit's
   image B (fuzz_rate.asan-ubsan): RtPgSegB's cuts D and J, image B's registers (cursor s2, left s6, kind byte's address
   s10, t1, a6) and real-frame cells (R+0x150, R+0x130, R+0x0, and R+0x158 = &pp->len, which the tails read back into
   s2), the pod e62 at F + 0x210, the class-4 frame for locals (1024 bytes, 128 shadow bytes, 88-byte pattern), the
   real frame 0x220, image B's first write ranges hi_w1; the heads and tails are lib/AU/RtPgW6cBaseB.v's statements,
   Section hypotheses until the end, where lib/AU/RtPgW6c6B.v, RtPgW6c7B.v, RtPgW6c8B.v and RtPgW6cTailB.v discharge
   them; A's unused helpers w6c_getrZ, w6c_fsub and w6c_present_hdr are dropped and RtPgW6cTail's w6c_val_kept is
   restated here. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6cB.v, with its module paths and module names changed; 42 of its 230 lines of code are new or changed and 618 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6c.v at cb9cdc023f20; for the same unit's
   image B (fuzz_rate.asan-ubsan): RtPgSegB's cuts D and J, image B's registers (cursor s2, left s6, kind byte's address
   s10, t1, a6) and real-frame cells (R+0x150, R+0x130, R+0x0, and R+0x158 = &pp->len, which the tails read back into
   s2), the pod e62 at F + 0x210, the class-4 frame for locals (1024 bytes, 128 shadow bytes, 88-byte pattern), the
   real frame 0x220, image B's first write ranges hi_w1; the heads and tails are lib/AU/RtPgW6cBaseB.v's statements,
   Section hypotheses until the end, where lib/AU/RtPgW6c6B.v, RtPgW6c7B.v, RtPgW6c8B.v and RtPgW6cTailB.v discharge
   them; A's unused helpers w6c_getrZ, w6c_fsub and w6c_present_hdr are dropped and RtPgW6cTail's w6c_val_kept is
   restated here. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6cB.v at 05426fac6916 for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): its cut-free helpers only (registers, values, the memcpy's
   source after a head, e62's bytes after a head, the model of cases 6, 7, 8, suffixes); module paths changed
   (lib/AU/Img0.rsegs, lib/A/RPgBase, lib/AU/RPgMem rm_, RPgSeg rs_); the statements are lib/AU/RPgW6cBase.v's, whose
   input premise w6cb_in names role B's five first write ranges; the register w6cb_keep_of_clob ties lib/AU/
   RPgW6bBase.v's w6bb_clob to w6cb_keep. The cut bridges move to lib/AU/RPgW6cGlue.v. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the kit of the walk piece
   "ent_build C" of LLVMFuzzerTestOneInput (0x80020): ent_build's cases 6, 7 and 8 (pod.h:340-366), from their
   switch entries 0x811d8 / 0x81050 / 0x8122c to the join J 0x818d8. Proves no function (kind: segment lemma).

   What lib/AU/RPgW6cGlue.v needs between a head (lib/AU/RPgW6c6.v, RPgW6c7.v, RPgW6c8.v) and its tail
   (lib/AU/RPgW6cTail.v) and at the join: the registers the three blocks keep; the memcpy's source after a head (the
   input's bytes after the first j, which a head never writes: it writes only e62's header); e62's 104 bytes after a
   head (type, size, the dispatch's 96 zeros); the pod Model.ent_build makes for kind % 10 = 6, 7, 8 and what it
   leaves of the input; and the memory a head and its tail keep together. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgMem RPgSteps RPgSeg RPgW6bBase RPgW6cBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== registers ======================================== *)
Lemma w6cb_regZ : forall (regs : bvmap 5 word) (q : bv 5) r, bv_unsigned q = r -> getr regs (Z_to_bv 5 r) = getr regs q.
Proof. intros regs q r <-. rewrite (Z_to_bv_bv_unsigned 5 q). reflexivity. Qed.
Lemma w6cb_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l H Hin. induction l as [|c l IH]; [exact Hin|]. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)]. unfold bv_eqb in H1. rewrite Z.eqb_refl in H1. discriminate H1.
Qed.
Lemma w6cb_nz : forall r : bv 5, (bv_unsigned r =? 0) = false -> bv_unsigned r <> 0.
Proof. intros r H. apply Z.eqb_neq. exact H. Qed.
(* a register a block keeps (outside clob) *)
Ltac w6cb_kept HK := rewrite HK; [| apply w6cb_nz; reflexivity | apply w6cb_notin; reflexivity].

(* the registers J keeps are outside both heads' clobber lists *)
Lemma w6cb_keep_clob : forall q, In q w6cb_keep -> bv_unsigned q <> 0 /\ ~ In q w6cb_clob67 /\ ~ In q w6cb_clob8.
Proof.
intros q Hq. cbv [w6cb_keep In] in Hq.
repeat (destruct Hq as [<-|Hq];
  [split; [apply w6cb_nz; reflexivity | split; apply w6cb_notin; reflexivity] |]).
destruct Hq.
Qed.
(* every register outside lib/AU/RPgW6bBase.v's w6bb_clob (and not x0) is one of w6cb_keep *)
Lemma w6cb_keep_of_clob : forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg w6bb_clob -> In rg w6cb_keep.
Proof.
intros rg H0 Hn. pose proof (in_nz_regs rg H0) as Hin. cbv [nz_regs In] in Hin.
repeat (destruct Hin as [<- | Hin];
  [ first
    [ solve [cbv [w6cb_keep In]; repeat (first [left; apply bv_eq; reflexivity | right])]
    | solve [exfalso; apply Hn; cbv [w6bb_clob In]; repeat (first [left; apply bv_eq; reflexivity | right])] ]
  | ]).
destruct Hin.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ======================================== values ======================================== *)
Lemma w6cb_val_mod : forall m a v, val_mem rsegs m a 8 (v mod 2 ^ 64) <-> val_mem rsegs m a 8 v.
Proof.
intros m a v. unfold val_mem.
assert (E : forall k, YO0f.le_byte (v mod 2 ^ 64) 8 k = YO0f.le_byte v 8 k).
{ intros k. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
split; intros H k Hk; specialize (H k Hk); [rewrite <- E | rewrite E]; exact H.
Qed.
(* an n-byte value whose bytes are kept *)
Lemma w6cb_val_kept : forall H m H' m' a n v, val_mem rsegs (mrestrict H m) a n v ->
(forall i, 0 <= i < Z.of_nat n -> aview rsegs H' m' (a + i) = aview rsegs H m (a + i)) ->
val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H m H' m' a n v V K k Hk. rewrite (mbyte_of_aview rsegs H H' m m' (a + Z.of_nat k)) by (apply K; lia).
exact (V k Hk).
Qed.

(* ======================================== the input and its shadow ======================================== *)
Lemma w6cb_hull_sub : forall (rd : reader) x n x' n', shadow_hull_vis rd x n -> 0 <= x -> x <= x' -> x' + n' <= x + n ->
0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H Hx0 H1 H2 H3 s Hs. apply H.
assert (M : forall a b, 0 <= a -> a <= b -> shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8).
{ intros a b Ha Hab. unfold shadow_addr.
  assert (a / 8 <= b / 8) by (apply Z.div_le_mono; lia).
  assert ((SHADOW_OFF + a / 8) / 8 <= (SHADOW_OFF + b / 8) / 8) by (apply Z.div_le_mono; lia). lia. }
pose proof (M x x' Hx0 H1). pose proof (M (x' + n' - 1) (x + n - 1) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma w6cb_src_bytes : forall H mem a (r : list byte) j m,
rm_bytes rsegs H mem a r -> rm_bytes rsegs H mem (a + Z.of_nat (Nat.min j (length r))) (firstn m (skipn j r)).
Proof.
intros H mem a r j m Hb.
pose proof (proj1 (rm_bytes_app rsegs H mem a (firstn j r) (skipn j r))) as Happ. rewrite firstn_skipn in Happ.
destruct (Happ Hb) as [_ H2]. rewrite length_firstn in H2.
pose proof (proj1 (rm_bytes_app rsegs H mem (a + Z.of_nat (Nat.min j (length r))) (firstn m (skipn j r)) (skipn m (skipn j r)))) as Happ2.
rewrite firstn_skipn in Happ2. destruct (Happ2 H2) as [H3 _]. exact H3.
Qed.

(* the memcpy's source after a head: the m bytes after the first j of the input, kept by the head, which writes only
   e62's header [F + 0x210, F + 0x218) *)
Lemma w6cb_src_ok : forall (W : world rsegs) memD memT R F c (r : list byte) (j m : nat),
w6cb_in W memD R F c r -> in_app F 1024 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memD a) ->
rm_bytes rsegs (w_H W) memT (c + Z.of_nat (Nat.min j (length r))) (firstn m (skipn j r)) /\
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF (c + Z.of_nat (Nat.min j (length r)))
  (Z.of_nat (length (firstn m (skipn j r)))) /\
(0 < Z.of_nat (length (firstn m (skipn j r))) ->
 shadow_hull_vis (aview rsegs (w_H W) memT) (c + Z.of_nat (Nat.min j (length r))) (Z.of_nat (length (firstn m (skipn j r))))) /\
amem_range (c + Z.of_nat (Nat.min j (length r))) (Z.of_nat (length (firstn m (skipn j r)))) /\
0 <= c + Z.of_nat (Nat.min j (length r)) /\
c + Z.of_nat (Nat.min j (length r)) + Z.of_nat (length (firstn m (skipn j r))) <= 2 ^ 63 /\
(forall a, c + Z.of_nat (Nat.min j (length r)) <= a < c + Z.of_nat (Nat.min j (length r)) + Z.of_nat (length (firstn m (skipn j r))) ->
 ~ (R - ESTACK <= a < R) /\ ~ (F + 0x210 <= a < F + 0x278)).
Proof.
intros W memD memT R F c r j m (HgI & HraI & HhI & Hc1 & Hctop & HamI & HdisI) HFapp HmT.
assert (Hlen : (Nat.min j (length r) + length (firstn m (skipn j r)) <= length r)%nat).
{ rewrite length_firstn, length_skipn. lia. }
set (x0 := c + Z.of_nat (Nat.min j (length r))) in *.
set (n0 := Z.of_nat (length (firstn m (skipn j r)))) in *.
assert (Hin : forall x, x0 <= x < x0 + n0 -> c <= x < c + Z.of_nat (length r)) by (intros x Hx; subst x0 n0; lia).
assert (Hx64 : forall x, c <= x < c + Z.of_nat (length r) -> 0 <= x < kHighMemEnd)
  by (intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (HkeepI : forall x, c <= x < c + Z.of_nat (length r) -> aview rsegs (w_H W) memT x = aview rsegs (w_H W) memD x).
{ intros x Hx. pose proof (Hx64 x Hx) as Hb. apply HmT; [unfold kHighMemEnd in Hb; lia |].
  unfold w6cb_hdr_wr. destruct (HdisI x Hx) as (_ & _ & _ & _ & D5). lia. }
assert (HkeepS : forall x, c <= x < c + Z.of_nat (length r) ->
  aview rsegs (w_H W) memT (shadow_of_addr SHADOW_OFF x) = aview rsegs (w_H W) memD (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (Hx64 x Hx) as Hb. pose proof (rm_shadow_band x Hb) as Hsb. apply HmT.
  - unfold kLowMemEnd, kHighMemBeg in Hsb. lia.
  - unfold w6cb_hdr_wr. pose proof (rm_shadow_not_app x F 1024 Hb HFapp). lia. }
split.
{ apply (rm_bytes_kept rsegs (w_H W) memD (w_H W) memT); [exact (w6cb_src_bytes _ _ _ _ _ _ HgI)|].
  intros x Hx. apply HkeepI. apply Hin. exact Hx. }
split.
{ intros x Hx. destruct (HraI x ltac:(pose proof (Hin x Hx); lia)) as (s & Hs & Ho). exists s.
  split; [rewrite (HkeepS x (Hin x Hx)); exact Hs | exact Ho]. }
split.
{ intros Hn. apply (rm_hull_kept rsegs (w_H W) memD (w_H W) memT).
  - apply (w6cb_hull_sub _ c (Z.of_nat (length r))); [apply HhI; lia | lia | lia | lia | lia].
  - intros s Hs Hnone.
    assert (Hsb : SHADOW_OFF <= s < kHighMemBeg).
    { pose proof (Hx64 x0 ltac:(pose proof (Hin x0); lia)). pose proof (Hx64 (x0 + n0 - 1) ltac:(pose proof (Hin (x0 + n0 - 1)); lia)).
      unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
      pose proof (Z.div_pos x0 8 ltac:(lia) ltac:(lia)).
      assert (2147450880 <= (2147450880 + x0 / 8) / 8 * 8).
      { assert (268431360 <= (2147450880 + x0 / 8) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
      assert ((x0 + n0 - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
      assert ((2147450880 + (x0 + n0 - 1) / 8) / 8 < 2199291686912) by (apply Z.div_lt_upper_bound; lia).
      lia. }
    rewrite HmT; [exact Hnone | unfold SHADOW_OFF, kHighMemBeg in Hsb; lia |].
    unfold w6cb_hdr_wr. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
split; [unfold amem_range in *; subst x0 n0; lia|].
split; [subst x0; lia|].
split; [subst x0 n0; lia|].
intros a Ha. destruct (HdisI a (Hin a Ha)) as (D1 & _ & _ & _ & D5).
split; [unfold ESTACK, T_SEG_STK, ASTACK in *; lia | lia].
Qed.

(* e62's 104 bytes after the head: type and size, then the 96 zeros of the dispatch's memset *)
Lemma w6cb_hdr_bytes : forall H mem H' mem' F ty sz,
rm_bytes rsegs H mem (F + 0x210) (zeros 104) ->
val_mem rsegs (mrestrict H' mem') (F + 0x210) 4 ty -> val_mem rsegs (mrestrict H' mem') (F + 0x214) 4 sz ->
(forall a, F + 0x218 <= a < F + 0x278 -> aview rsegs H' mem' a = aview rsegs H mem a) ->
rm_bytes rsegs H' mem' (F + 0x210) (le32 ty ++ le32 sz ++ zeros 96).
Proof.
intros H mem H' mem' F ty sz HZ Vt Vs K.
apply rm_bytes_app. split; [unfold le32; apply rm_bytes_of_val; exact Vt|].
rewrite length_le32. apply rm_bytes_app. split.
{ replace (F + 0x210 + Z.of_nat 4) with (F + 0x214) by lia. unfold le32. apply rm_bytes_of_val. exact Vs. }
rewrite length_le32.
pose proof (rm_bytes_slice rsegs _ _ _ (zeros 104) 8 96 HZ ltac:(rewrite length_zeros; lia)) as HZ1.
change (rm_slice (zeros 104) 8 96) with (zeros 96) in HZ1.
replace (F + 0x210 + Z.of_nat 4 + Z.of_nat 4) with (F + 0x210 + Z.of_nat 8) by lia.
apply (rm_bytes_kept rsegs _ _ _ _ _ _ HZ1).
intros x Hx. rewrite length_zeros in Hx. apply K. lia.
Qed.

(* the memory a head keeps, then the one its tail keeps *)
Lemma w6cb_mem_chain : forall (W : world rsegs) memD memT memJ R F,
(forall a, 0 <= a < 2 ^ 64 -> ~ w6cb_hdr_wr F a -> aview rsegs (w_H W) memT a = aview rsegs (w_H W) memD a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x210 <= a < F + 0x278) ->
 aview rsegs (w_H W) memJ a = aview rsegs (w_H W) memT a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (R - ESTACK <= a < R) -> ~ (F + 0x210 <= a < F + 0x278) ->
aview rsegs (w_H W) memJ a = aview rsegs (w_H W) memD a.
Proof.
intros W memD memT memJ R F HmT HmJ a Ha H1 H2. rewrite (HmJ a Ha H1 H2). apply HmT; [exact Ha|].
unfold w6cb_hdr_wr. lia.
Qed.
End b.

(* ======================================== the model ======================================== *)
Lemma w6cb_ent6 : forall (b : byte) r, bv_unsigned b mod 10 = 6 ->
ent_build (b :: r) =
(Ent (w6cb_ty6 (fst (fuzz_u8 r))) (w6cb_sz6 (w6cb_ty6 (fst (fuzz_u8 r))))
  (firstn (Z.to_nat (w6cb_sz6 (w6cb_ty6 (fst (fuzz_u8 r))))) (snd (fuzz_u8 r)) ++
   zeros (Z.to_nat (w6cb_sz6 (w6cb_ty6 (fst (fuzz_u8 r)))) -
          length (firstn (Z.to_nat (w6cb_sz6 (w6cb_ty6 (fst (fuzz_u8 r))))) (snd (fuzz_u8 r))))),
 skipn (Z.to_nat (w6cb_sz6 (w6cb_ty6 (fst (fuzz_u8 r))))) (snd (fuzz_u8 r))).
Proof.
intros b r H. unfold ent_build. change (fuzz_u8 (b :: r)) with (bv_unsigned b, r). cbv beta iota zeta.
rewrite H. change (Z.to_nat 6) with 6%nat. cbv beta iota zeta.
destruct (fuzz_u8 r) as [t r1]. reflexivity.
Qed.
Lemma w6cb_ent7 : forall (b : byte) r, bv_unsigned b mod 10 = 7 ->
ent_build (b :: r) =
(Ent (fst (fuzz_u8 r) mod 21) (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12)
  (firstn (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12)) (snd (fuzz_u8 (snd (fuzz_u8 r)))) ++
   zeros (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12) -
          length (firstn (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12)) (snd (fuzz_u8 (snd (fuzz_u8 r))))))),
 skipn (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 r))) mod 12)) (snd (fuzz_u8 (snd (fuzz_u8 r))))).
Proof.
intros b r H. unfold ent_build. change (fuzz_u8 (b :: r)) with (bv_unsigned b, r). cbv beta iota zeta.
rewrite H. change (Z.to_nat 7) with 7%nat. cbv beta iota zeta.
destruct (fuzz_u8 r) as [t r1]. cbn [fst snd]. destruct (fuzz_u8 r1) as [s r2]. reflexivity.
Qed.
Lemma w6cb_ent8 : forall (b : byte) r, bv_unsigned b mod 10 = 8 ->
ent_build (b :: r) =
(Ent (w6cb_ty8 (fst (fuzz_u8 r))) (fst (w6cb_sz8 (w6cb_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r))))
  (zeros (Z.to_nat (fst (w6cb_sz8 (w6cb_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r)))))),
 snd (w6cb_sz8 (w6cb_ty8 (fst (fuzz_u8 r))) (snd (fuzz_u8 r)))).
Proof.
intros b r H. unfold ent_build. change (fuzz_u8 (b :: r)) with (bv_unsigned b, r). cbv beta iota zeta.
rewrite H. change (Z.to_nat 8) with 8%nat. cbv beta iota zeta.
destruct (fuzz_u8 r) as [t r1]. cbn [fst snd]. unfold w6cb_sz8, w6cb_ty8.
destruct (nth (Z.to_nat (t mod 4)) Tables.t8 0 =? POD_STRING) eqn:E.
- apply Z.eqb_eq in E. cbn [fst snd]. rewrite E. reflexivity.
- destruct (fuzz_u8 r1) as [s r2]. reflexivity.
Qed.
Lemma w6cb_sz6_rng : forall ty, 0 <= w6cb_sz6 ty <= 8.
Proof. intros ty. unfold w6cb_sz6. destruct (ty =? POD_NONE); [lia|]. destruct (ty =? POD_ID); lia. Qed.
Lemma w6cb_sz8_rng : forall ty r1, 0 <= fst (w6cb_sz8 ty r1) < 4.
Proof. intros ty r1. unfold w6cb_sz8. destruct (ty =? POD_STRING); cbn [fst]; [lia|]. apply Z.mod_pos_bound. lia. Qed.

(* ======================================== the suffix ======================================== *)
Lemma w6cb_suffix_skip : forall rest r n, rs_suffix rest r -> rs_suffix rest (skipn n r).
Proof.
intros rest r n (j & Hj & ->). rewrite skipn_skipn.
destruct (Nat.le_gt_cases (n + j) (length rest)) as [Hle|Hgt].
- exists (n + j)%nat. split; [exact Hle | reflexivity].
- exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.
Lemma w6cb_u8_rest : forall r, snd (fuzz_u8 r) = skipn 1 r.
Proof. intros [|b r]; reflexivity. Qed.
Lemma w6cb_sz8_len : forall ty r1, (length (snd (w6cb_sz8 ty r1)) <= length r1)%nat.
Proof.
intros ty r1. unfold w6cb_sz8. destruct (ty =? POD_STRING); cbn [snd]; [lia|].
rewrite w6cb_u8_rest, length_skipn. lia.
Qed.
