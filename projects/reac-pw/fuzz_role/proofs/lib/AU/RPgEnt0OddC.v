(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v, with its module paths and module names changed; 147 of its 199 lines of code are new or changed and 909 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddC.v at 111d25b4415f for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; RPgBase / RPgMem / RPgSeg / RPgImgA are lib/A/RtPgBase.v (rt_cstr, rt_fsh, rt_inw and the rt_renv fields), RtPgMem.v (the rtm_ lemmas), RtPgSeg.v and RtPgImgA.v (rate_himg_A); the segment's write set is rate's hi_w1 (F + 0x20 .. F + 0x158, 39 of F's 56 shadow bytes, four runs of real-frame cells below R + 0x178) and the frame's shadow has 56 bytes; the prologue's shadow comes from rs_start_M01 (rate's rt_seg_pre holds none); AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0OddC.v at 21da95a5fcd3; image B (images.AsanUbsan): lib/AU/RtPgMemB.v, RtPgSegB.v and RtPgImgB.v (rate_himg_B) for the A files; the frame for locals is a side-stack frame of class 4 (1024 bytes) whose prologue writes 88 shadow bytes; the segment's write set is image B's hi_w1 (F + 0x20 .. F + 0x278, 75 of F's 88 shadow bytes, four runs of real-frame cells below R + 0x1b8); the table is RtPgEnt0OddBB.v's (0x9be40); names o_ -> ob_, oc_ -> ocb_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0OddCB.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; lib/AU/RPgMem.v, RPgSeg.v and RPgImgA.v (role_himg_B) for the rate files; the segment's write set is role B's hi_w1 (F + 0x20 .. F + 0x278, 75 of F's 88 shadow bytes, three runs of real-frame cells below R + 0x198); the prologue's shadow comes from RPgCSpec.rl_seg_pre; the table is lib/AU/RPgEnt0OddB.v's (0x9a820). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the start facts the ODD block
   of ent_build's case 0 (0x815e0 -> 0x80dc8, pod.h:247-248, `memcpy(ch, odd_ch[c % 14], strlen(...) + 1)`) reads,
   carried from the build segment's start memory to the memory of a cut inside it. Proves no function (kind: segment
   lemma, a memory transport).

   ob_at_cut: at a cut of the build (lib/AU/RPgSeg.v rs_core with the write set rs_E1) whose frame for locals
   holds the shadow bytes rs_PG, the read-only data is still the image's (rom_view), and for each m < 14 the table
   cell odd_ch[m] (0x9a820 + 8 m) is addressable, holds ob_ptr m, and the string at ob_ptr m is still RPgBase.rl_cstr
   of ob_str m.

   HOW. Every byte outside the callees' stack [R - T_SEG_STK, R) and outside rs_E1 (inside F + 0x20 .. F + 0x278,
   the 88 shadow bytes of F, R .. R + 0x198, the block pp) is as at the start. An image byte lies below kLowMemEnd
   and in neither F's frame nor pp (YCbq.v frm_img / blk_img), so it avoids that set (ocb_img_not_wr). The shadow
   byte of an address below kHighMemEnd lies in the low shadow band [kLowMemEnd, kHighMemBeg) (RPgMem.v
   rm_shadow_band), which no application range (F's frame, pp) and no part of the real frame or the callees' stack
   meets (ocb_band_not_wr); for an address addressable at the start it is not one of F's 88 shadow bytes either
   (RPgMem.v rm_ra_not_fsh: the prologue's pattern is all >= 8). A byte of a string's shadow hull lies in the band
   too: it is as at the start, or it is one of F's shadow bytes, which rs_PG makes present at the cut. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YO09 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgMem RPgSeg RPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgEnt0OddB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- address facts ---- *)
Lemma ocb_dec_in : forall lo n t, (lo <= t < lo + n) \/ ~ (lo <= t < lo + n).
Proof. intros lo n t. lia. Qed.

(* a byte of the shadow hull of a range below kLowMemEnd lies in the low shadow band *)
Lemma ocb_hull_band : forall a n t, 0 <= a -> 0 < n -> a + n <= kLowMemEnd ->
shadow_addr a / 8 * 8 <= t < shadow_addr (a + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= t < kHighMemBeg.
Proof.
intros a n t H0 Hn Hl Ht. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *.
Z.div_mod_to_equations. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the segment's write set rs_E1, range by range (RPgImgA: hi_w1 = [(XF, 0x20, 0x258); (XShF, 4, 75);
   (XR, 0x10, 0x30); (XR, 0x48, 0x118); (XR, 0x178, 0x20)]) *)
Lemma ocb_E1 : forall cx a, rs_E1 rsegs cx a ->
(e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x278) \/
(shadow_addr (e_F (x_e cx)) <= a < shadow_addr (e_F (x_e cx)) + 88) \/
(e_R (x_e cx) <= a < e_R (x_e cx) + 0x198) \/
(e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE).
Proof.
intros cx a [H|H]; [|right; right; right; exact H].
unfold rl_inw in H. cbn [hi_w1 role_himg_B] in H.
repeat rewrite Exists_cons in H. rewrite Exists_nil in H. cbn [rl_xv fst snd] in H.
destruct H as [H|[H|[H|[H|[H|[]]]]]];
  [left | right; left | right; right; left | right; right; left | right; right; left]; lia.
Qed.

(* an image byte avoids the write set and the callees' stack *)
Lemma ocb_img_not_wr : forall R F pp a,
alloc_ceiling <= R - T_SEG_STK -> 0 <= F ->
(forall x, F <= x < F + 1024 -> ~ in_img rsegs x) ->
(forall x, pp <= x < pp + Layout.PP_SIZE -> ~ in_img rsegs x) ->
in_img rsegs a ->
0 <= a < 2 ^ 64 /\ ~ (R - T_SEG_STK <= a < R) /\
~ ((F + 0x20 <= a < F + 0x278) \/ (shadow_addr F <= a < shadow_addr F + 88) \/ (R <= a < R + 0x198) \/
   (pp <= a < pp + Layout.PP_SIZE)).
Proof.
intros R F pp a HR HF0 HF Hp Ha. pose proof (rl_segs_low a Ha) as Hl. pose proof asan_consts as (C1 & _).
unfold kLowMemEnd in Hl. unfold T_SEG_STK, ASTACK in *.
split; [lia|]. split; [lia|].
intros [X|[X|[X|X]]].
- exact (HF a ltac:(lia) Ha).
- unfold shadow_addr, SHADOW_OFF in X. assert (0 <= F / 8) by (apply Z.div_pos; lia). lia.
- lia.
- exact (Hp a X Ha).
Qed.

(* a byte of the low shadow band outside F's 88 shadow bytes avoids the write set and the callees' stack *)
Lemma ocb_band_not_wr : forall R F pp s,
alloc_ceiling <= R - T_SEG_STK -> in_app F 1024 -> in_app pp Layout.PP_SIZE ->
kLowMemEnd <= s < kHighMemBeg -> ~ (shadow_addr F <= s < shadow_addr F + 88) ->
0 <= s < 2 ^ 64 /\ ~ (R - T_SEG_STK <= s < R) /\
~ ((F + 0x20 <= s < F + 0x278) \/ (shadow_addr F <= s < shadow_addr F + 88) \/ (R <= s < R + 0x198) \/
   (pp <= s < pp + Layout.PP_SIZE)).
Proof.
intros R F pp s HR HF Hp Hs Hsh. pose proof asan_consts as (C1 & _).
unfold in_app in HF, Hp.
unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, T_SEG_STK, ASTACK, Layout.PP_SIZE in *.
split; [lia|]. split; [lia|].
intros [X|[X|[X|X]]]; [lia | exact (Hsh X) | lia | lia].
Qed.

(* a string fact carried to another memory: its bytes (image bytes), the shadow bytes of its len + 1 bytes and
   its shadow hull *)
Lemma ocb_cstr_kept : forall H mem H' mem' a s,
rl_cstr rsegs H mem a s ->
(forall x, in_img rsegs x -> aview rsegs H' mem' x = aview rsegs H mem x) ->
(forall p n, range_addressable (aview rsegs H mem) SHADOW_OFF p n -> 0 <= p -> p + n <= kHighMemEnd ->
 forall x, p <= x < p + n ->
 aview rsegs H' mem' (shadow_of_addr SHADOW_OFF x) = aview rsegs H mem (shadow_of_addr SHADOW_OFF x)) ->
(forall t, kLowMemEnd <= t < kHighMemBeg -> aview rsegs H mem t <> None -> aview rsegs H' mem' t <> None) ->
rl_cstr rsegs H' mem' a s.
Proof.
intros H mem H' mem' a s (Hb & Hn & Hr & Ha0 & Ha63 & Himg & Ham & Hra & Hhull) Ki Ks Kh.
assert (Hlow : 0 <= a + Z.of_nat (length s) < kLowMemEnd) by (apply rl_segs_low, Himg; lia).
unfold rl_cstr.
split; [intros i Hi; rewrite Ki by (apply Himg; lia); exact (Hb i Hi)|].
split; [rewrite Ki by (apply Himg; lia); exact Hn|].
do 5 (split; [assumption|]).
split.
- apply (rm_ra_kept rsegs H mem); [exact Hra|]. apply (Ks _ _ Hra); unfold kHighMemEnd, kLowMemEnd in *; lia.
- apply (rm_hull_kept rsegs H mem); [exact Hhull|]. intros t Ht Hv. apply Kh; [|exact Hv].
  apply (ocb_hull_band a (Z.of_nat (length s) + 1) t); lia.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma ob_at_cut : forall cx rest ly2 S2 W2 regs2 mem2 md2,
rs_start_M01 rsegs B cx rest ->
rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rs_fsh_at rsegs cx W2 mem2 rs_PG ->
rom_view rsegs W2 mem2 /\
(forall m, 0 <= m < 14 ->
 range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (OB_TBL + 8 * m) 8 /\
 val_mem rsegs (mrestrict (w_H W2) mem2) (OB_TBL + 8 * m) 8 (ob_ptr m) /\
 rl_cstr rsegs (w_H W2) mem2 (ob_ptr m) (map (fun b : byte => bv_unsigned b) (ob_str m))).
Proof.
intros cx rest ly2 S2 W2 regs2 mem2 md2 Hst Hcore Hfsh2.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct Hst as (Hpre & _).
unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJ & _ & H2 & _ & _ & HS & _ & HRs & HRstk & Hown & HF & Hfsh & _ & Hpp & _ & _ & HG & _ & HSt & HC
  & Hrom & _).
cbn [hi_cid hi_rsz hi_shA hi_globs hi_strs hi_cells role_himg_B] in HRs, Hown, HF, Hfsh, HG, HSt, HC.
unfold rl_ro_cells in HC.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
(* R: the real frame, above the callees' stack, above alloc_ceiling *)
assert (HRlo : alloc_ceiling <= e_R (x_e cx) - T_SEG_STK) by (clear - Hceil Hslo HRstk; lia).
assert (HRhi : e_R (x_e cx) < 2 ^ 64) by (clear - HRs HS Hshi H47; lia).
assert (HR0 : 0 <= e_R (x_e cx)).
{ pose proof asan_consts as (C1 & _). clear - HRlo C1. unfold T_SEG_STK, ASTACK in HRlo. lia. }
assert (HspZ : spZ (x_regs cx) = e_R (x_e cx)).
{ unfold spZ. rewrite H2. exact (unsigned_lit_small _ (conj HR0 HRhi)). }
(* F: the frame for locals, a side-stack frame of class 4 the harness holds *)
assert (Hin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hin) as (F1 & _ & F3).
rewrite <- HF in F1, F3. change (fs_frame_bytes 4) with 1024 in F3.
assert (Fimg : forall a, e_F (x_e cx) <= a < e_F (x_e cx) + 1024 -> ~ in_img rsegs a).
{ intros a Ha. apply (frm_img rsegs B LAWS _ _ _ _ _ 4 (x_pos cx) a HAR Hin). rewrite <- HF. exact Ha. }
(* pp: the first block *)
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & _ & _ & Papp & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Papp.
assert (Pimg : forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE -> ~ in_img rsegs a).
{ intros a Ha. apply (blk_img rsegs B LAWS _ _ _ _ _ _ _ a HAR Hpp). rewrite Hrq. exact Ha. }
(* the kept clause of the cut *)
unfold rs_core, rs_mid in Hcore. destruct Hcore as (_ & _ & _ & _ & _ & _ & Hm).
rewrite HspZ in Hm.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) ->
  ~ ((e_F (x_e cx) + 0x20 <= a < e_F (x_e cx) + 0x278) \/
     (shadow_addr (e_F (x_e cx)) <= a < shadow_addr (e_F (x_e cx)) + 88) \/
     (e_R (x_e cx) <= a < e_R (x_e cx) + 0x198) \/ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE)) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a H1 H3 H4. apply Hm; [exact H1 | exact H3 |]. intros HE. exact (H4 (ocb_E1 cx a HE)). }
(* 1. image bytes *)
assert (Kimg : forall a, in_img rsegs a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha. assert (F0 : 0 <= e_F (x_e cx)) by (clear - F1; lia).
  destruct (ocb_img_not_wr _ _ _ a HRlo F0 Fimg Pimg Ha) as (X1 & X2 & X3).
  exact (K a X1 X2 X3). }
(* 2. the shadow bytes of a range addressable at the start, below kHighMemEnd *)
assert (Ksh : forall p n, range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF p n -> 0 <= p ->
  p + n <= kHighMemEnd -> forall x, p <= x < p + n ->
  aview rsegs (w_H W2) mem2 (shadow_of_addr SHADOW_OFF x) =
  aview rsegs (w_H (x_W cx)) (x_memc cx) (shadow_of_addr SHADOW_OFF x)).
{ intros p n Hra Hp Hn x Hx.
  pose proof (rm_shadow_band x ltac:(clear - Hp Hn Hx; lia)) as Hb.
  pose proof (rm_ra_not_fsh rsegs _ _ _ _ _ _ Hra Hfsh rm_sh_P0_big x Hx) as Hnf.
  change (Z.of_nat (length role_B_shA)) with 88 in Hnf.
  destruct (ocb_band_not_wr _ _ _ _ HRlo F3 Papp Hb Hnf) as (X1 & X2 & X3). exact (K _ X1 X2 X3). }
(* 3. a byte of the low shadow band present at the start is present at the cut *)
assert (Khull : forall t, kLowMemEnd <= t < kHighMemBeg ->
  aview rsegs (w_H (x_W cx)) (x_memc cx) t <> None -> aview rsegs (w_H W2) mem2 t <> None).
{ intros t Ht Hv. unfold rs_fsh_at, rl_fsh in Hfsh2.
  destruct (ocb_dec_in (shadow_addr (e_F (x_e cx))) 88 t) as [Hi|Hi].
  - replace t with (shadow_addr (e_F (x_e cx)) + (t - shadow_addr (e_F (x_e cx)))) by lia.
    rewrite (Hfsh2 (t - shadow_addr (e_F (x_e cx)))) by (change (Z.of_nat (length rs_PG)) with 88; lia).
    discriminate.
  - destruct (ocb_band_not_wr _ _ _ _ HRlo F3 Papp Ht Hi) as (X1 & X2 & X3). rewrite (K t X1 X2 X3). exact Hv. }
split.
- apply (rm_rom_kept rsegs (x_W cx) W2 (x_memc cx) mem2 Hrom). intros a (sg & Hsg & _ & Hb).
  apply Kimg. exists sg. split; [exact Hsg | exact Hb].
- intros m Hm14.
  pose proof (proj1 (Forall_forall _ _) HG _ ob_glob) as HGt. cbn [fst snd] in HGt.
  assert (HRA : range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF (OB_TBL + 8 * m) 8).
  { eapply range_addressable_sub; [exact HGt | lia | lia]. }
  split; [|split].
  + apply (rm_ra_kept rsegs (w_H (x_W cx)) (x_memc cx)); [exact HRA|].
    apply (Ksh _ _ HRA); unfold OB_TBL, kHighMemEnd; lia.
  + pose proof (proj1 (Forall_forall _ _) HC _ (ob_cell m Hm14)) as Hc. cbn [fst snd] in Hc.
    eapply val_mem_kept; [|exact Hc]. intros k Hk. apply Kimg. apply ob_tbl_img. cbn in Hk. lia.
  + pose proof (proj1 (Forall_forall _ _) HSt _ (ob_strin m Hm14)) as Hs. cbn [fst snd] in Hs.
    exact (ocb_cstr_kept _ _ _ _ _ _ Hs Kimg Ksh Khull).
Qed.
End d.
End b.

Print Assumptions ob_at_cut.
