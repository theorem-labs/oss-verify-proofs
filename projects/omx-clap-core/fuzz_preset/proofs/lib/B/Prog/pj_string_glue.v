(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the GLUE facts of pj_string's image-B walk (fuzz_preset asan-ubsan; the cuts of
   lib/B/Prog/pj_string_defs.v): what the entry premises pjs_pre say of v's 56 bytes (their place - a harness block's
   user bytes, a non-harness allocator block or a fake frame of the entry state: the caller-window case is excluded by
   the text's v < alloc_ceiling -, their bounds, apart from the image, the program statics and every harness head).
   The node bytes pjs_bytes and the tree predicates the post asks of them are lib/A/Prog/PjStringCommon.v's (the one
   copy for both images).
   proves no function (kind: glue lemma). Section hypothesis: AR_laws_x SEGS B ARx cf_head (the kit's laws).
   Numerals: 56 (LENGTH: node). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_string_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* where v's 56 bytes lie at the entry state *)
Definition pjs_place (en : PjsEnt) (ly : alayout) (S : astate) : Prop :=
  let v := js_v en in let Lam := js_Lam en in
  (exists a k, In (a, k) Lam /\ a <= v /\ v + 56 <= a + k) \/
  (exists b m, In (b, m) (ablocks B ly S) /\ ~ In (b + cf_head, m - cf_head) Lam /\ b <= v /\ v + 56 <= b + m) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid).

(* the facts of v the entry premises give *)
Lemma pjs_pre_v : forall CTX0 en, pjs_pre B ARx CTX0 en ->
  pjs_place en (js_ly en) (js_S en) /\
  4096 <= js_v en /\ js_v en + 56 <= YM05.alloc_ceiling /\ js_v en mod 8 = 0 /\ amem_range (js_v en) 56 /\
  (forall a, js_v en <= a < js_v en + 56 -> ~ in_img SEGS a) /\
  (forall a, Exists (in_zr a) prh_pst -> ~ (js_v en <= a < js_v en + 56)) /\
  (forall a k i, In (a, k) (js_Lam en) -> 0 <= i < 8 -> ~ (js_v en + 16 <= a - cf_head + i < js_v en + 24)).
Proof.
intros CTX0 en HPRE.
destruct en as [ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own rpsm rpx rpos rpi rpH0 rphist].
unfold pjs_pre in HPRE. cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak
  js_cnt js_fail js_ran js_most js_own] in HPRE |- *.
destruct HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HSLOT & HCEIL & _ & _ & _ & HLED & _).
destruct HFPRE as ((HAR & _ & _ & _ & _ & Hstk & _) & _ & _).
destruct Hstk as (_ & Hstk0 & Hcl & Hslo & _).
destruct HSLOT as (H4096 & Hat & (Hal8 & _) & Hamr & _).
pose proof cf_head_nonneg as Hh0.
(* the place: prhReader_at without its caller-window case (v < alloc_ceiling <= the entry sp) *)
assert (HPL : pjs_place (MkPjsEnt ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own rpsm rpx rpos rpi rpH0 rphist)
  ly S).
{ unfold pjs_place. cbn [js_v js_Lam].
  destruct Hat as [Hl | [Hb | [Hf | (Hw1 & _)]]]; [left; exact Hl | right; left; exact Hb | right; right; exact Hf|].
  exfalso. lia. }
pose proof HPL as HPL0. unfold pjs_place in HPL0. cbn [js_v js_Lam] in HPL0.
(* the allocator block holding a harness block *)
assert (HB : forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) /\ 0 <= k).
{ intros a k Hin. destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as (Hk & Hab & _).
  split; [exact Hab | exact Hk]. }
assert (Rq : forall k, 0 <= k -> k + cf_head <= req_size (k + cf_head))
  by (intros k Hk; unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
(* v's block or frame bounds *)
assert (Hbnd : v + 56 <= YM05.alloc_ceiling /\ forall a, v <= a < v + 56 -> ~ in_img SEGS a).
{ destruct HPL0 as [(a & k & Hin & Ha & Hk) | [(b & m & Hin & _ & Hb & Hm) | (cid & pos & Hin & Hf & Hfm)]].
  - destruct (HB a k Hin) as [Hab Hk0]. pose proof (Rq k Hk0) as R.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & Hc & _).
    split; [lia|]. intros x Hx.
    apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hab). lia.
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & Hc & _).
    pose proof (req_size_pos m) as Rm. assert (Hm0 : 0 <= m) by lia. specialize (Rm Hm0).
    split; [lia|]. intros x Hx. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m x HAR Hin). lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hc & _).
    split; [lia|]. intros x Hx. apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HAR Hin). lia. }
destruct Hbnd as (Hv56 & Hnimg).
split; [exact HPL|]. split; [exact H4096|]. split; [exact Hv56|]. split; [exact Hal8|]. split; [exact Hamr|].
split; [exact Hnimg|].
split.
{ intros a Ha Hv. exact (Hnimg a Hv (pst_in_img_B a Ha)). }
(* the head words of the harness blocks miss the str field: a head word is 8 bytes at the 16-aligned base of its
   block, and v's place is that block's user range, another 16-aligned block or a 32-aligned frame *)
intros a k i Hin Hi Hx.
destruct (HB a k Hin) as [Hab Hk0].
assert (R : 1 <= req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head)) by (apply req_size_pos; lia).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (HA16 & _).
destruct HPL0 as [(a0 & k0 & Hin0 & Ha0 & Hk0') | [(b & m & Hin1 & Hnl & Hb & Hm) | (cid & pos & Hin2 & Hf & Hfm)]].
- destruct (Z.eq_dec a a0) as [-> | Hne]; [lia|].
  destruct (HB a0 k0 Hin0) as [Hab0 Hkk0].
  assert (R0 : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head)) by (apply req_size_pos; lia).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab0) as (HA016 & _).
  assert (Hne' : (a - cf_head, k + cf_head) <> (a0 - cf_head, k0 + cf_head)) by (intros E; injection E as E1 _; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab0 Hne') as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (Hne' : (a - cf_head, k + cf_head) <> (b, m)).
  { intros E. injection E as E1 E2. apply Hnl. rewrite <- E1, <- E2.
    replace (a - cf_head + cf_head) with a by lia. replace (k + cf_head - cf_head) with k by lia. exact Hin. }
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin1) as (Hb16 & _).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin1 Hne') as Hd.
  pose proof (req_size_pos m) as Rm. assert (Hm0 : 0 <= m) by lia. specialize (Rm Hm0).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin2) as (Hf32 & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hab Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
End g.
