(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value: the SHADOW of EXB's text, scratch and Lam tree nodes at ANY
   allocator state, re-derived from the allocator laws (EXV_HYP's eh_laws, YCbqG's AR_laws_x at hl = cf_head) and the
   ledger. Every segment that makes a program call needs it: ajournal_x keeps no shadow byte of a heap block (the
   shadow is the runtime's), so EXB's range_addressable / shadow_hull_vis facts at the post-call state come from here.
   - exv_sh_blk: a range inside a live allocator block, past its hidden head when the block's base is in Hp
     (prhex_inblk), is addressable and its shadow hull visible: a harness block (base in Hp) by field 14
     alx_hshadow; any other block by alx_shadow, whose side condition (no Hp element inside the block) follows from the
     ledger (Hp is the bases of the Lam blocks, each a live block, and live blocks are disjoint: sep_blocks_x).
   - exv_sh_lam: a range inside a Lam block (a harness block's user range) is the case b - cf_head of exv_sh_blk.
   Rule 24: proves no function (kind: segment lemma helper). No numeral but 0 (LENGTH). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* the hull is closed under sub-ranges (YGcfHeadSh.v:93 shadow_hull_vis_sub_cf, restated: that file is the cf layer) *)
Lemma exv_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.

Section s. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

(* no base of the ledger's harness blocks lies inside a live block whose own base is not in Hp *)
Lemma exv_hp_apart : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In b Hp ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR (_ & _ & HB & HP) Hin Hbn h Hh Hr.
pose proof (eh_laws B ARx SK HYP) as LAWS.
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hak). cbn [fst] in Eh.
rewrite Forall_forall in HB. destruct (HB (a, k) Hak) as (Hk0 & Hblk & Hinp & _ & _). cbn [fst snd] in *.
rewrite Eh in Hblk, Hinp.
assert (Hne : (b, m) <> (h, k + cf_head)) by (intros E; injection E as -> _; exact (Hbn Hinp)).
pose proof (sep_blocks_x rsegs B ARx LAWS ly S Hp W mem md b m h (k + cf_head) HAR Hin Hblk Hne) as Hd.
pose proof (@cf_head_nonneg cp) as CH0.
assert (Hk1 : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0) as [Hz|Hz]; lia).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hr Hk1. lia.
Qed.

(* a range inside a live block (past the hidden head of a harness block) is addressable with a visible hull *)
Lemma exv_sh_blk : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own a n,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_inblk B ly S Hp a n -> 0 < n ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview rsegs (w_H W) mem) a n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a n HAR HLED (b & m & Hin & Hba & Ham & Hhd) Hn.
pose proof (eh_laws B ARx SK HYP) as LAWS.
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (in_dec Z.eq_dec b Hp) as [Hbh | Hbn].
- specialize (Hhd Hbh).
  destruct (alx_hshadow rsegs B ARx LAWS ly S Hp W mem md b m HAR Hin Hbh) as (BS & HV).
  split.
  + apply (block_shadow_range _ _ (b + cf_head) (req_size m - cf_head) a n BS); lia.
  + apply (exv_hull_sub _ (b + cf_head) (req_size m - cf_head)); [apply HV; lia | lia | lia].
- destruct (alx_shadow rsegs B ARx LAWS ly S Hp W mem md b m HAR Hin
    (exv_hp_apart ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin Hbn)) as (BS & HV).
  split.
  + apply (block_shadow_range _ _ b (req_size m) a n BS); lia.
  + apply (exv_hull_sub _ b (req_size m)); [exact HV | lia | lia].
Qed.

(* a range inside a Lam block (a harness block's user range) *)
Lemma exv_sh_lam : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own b k p m,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, k) Lam -> b <= p -> p + m <= b + k -> 0 < m ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF p m /\ shadow_hull_vis (aview rsegs (w_H W) mem) p m.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b k p m HAR HLED Hin Hbp Hpk Hm.
pose proof HLED as (_ & _ & HB & _). rewrite Forall_forall in HB.
destruct (HB (b, k) Hin) as (Hk0 & Hblk & Hinp & _ & _). cbn [fst snd] in *.
apply (exv_sh_blk ly S Hp W mem md Lam peak cnt fail ran most own p m HAR HLED); [|exact Hm].
exists (b - cf_head), (k + cf_head). split; [exact Hblk|]. pose proof (@cf_head_nonneg cp) as CH0.
split; [lia|]. split; [lia|]. intros _. lia.
Qed.
End s.

Print Assumptions exv_sh_blk.
Print Assumptions exv_sh_lam.
