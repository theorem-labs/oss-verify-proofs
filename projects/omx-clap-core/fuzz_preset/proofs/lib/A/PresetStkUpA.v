(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetStkUpA.v, with its module paths changed; 34 of its 97 lines of code are new or changed and 1 line of the source is left out. *)
(* Theorem Labs, 2026-10-30: omx-clap-core/fuzz_preset (asan image A), THE LIVE REAL STACK ABOVE THE ENTRY sp, the
   driver walk's invariant from main's entry to each harness call (#102; the slot pre's last conjunct,
   YGcallStackUp.astack_up_x at the call's sp, the interface's header item (13)). Rule 24: no function is proved here
   (driver layer of a port: transport lemmas).
   THE INVARIANT is YGcallStackUp.astack_up_x tfibsegs ly W usp mem, usp the start draw (bv_unsigned sp): every byte of
   [usp, ly_top ly) is present (apresent: not hidden, mapped). No driver step writes a byte at or above usp:
   - a symbolic run's frame (frame_of over its start state's regions) is outside the driver windows (drv_win_ok:
     [usp - 64 KiB, usp) and DRV_IVS below the image top, lib/A/AD1y.v), so the bytes above usp are unchanged
     (stk_up_frame);
   - an allocator call's post (acall_post_cf) keeps every byte off the image, off both owned sets (below
     alloc_ceiling), off errno and off its exception set (below alloc_ceiling) (stk_up_acall, through a Theorem Labs lane's
     YGcfPres.acall_post_cf_presence);
   - a site whose post keeps presence (memcpy, read check, printf) keeps it (stk_up_keep);
   - a harness call's journal keeps it (YGcallStackUp.astack_up_journal_xw, used in the loop's proof).
   At a call, the invariant and the window [usp - 64 KiB, usp) of the symbolic state give astack_up_x at the call's sp
   (stk_up_at). At main the invariant is the driver walk's named premise (lib/A/PresetD1pA.v H_stackup_main_A). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK15 YK18 YP0n YK0s YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i YA0n YA0e YG00 YG01 YG0f YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB12 AF0m AD2j AD2i AD1t AD20 AD1v AD1y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfPres YGcallStackUp YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section s.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Notation SU := (YGcallStackUp.astack_up_x tfibsegs) (only parsing).

(* a symbolic run: its frame is outside the driver windows, which lie below usp *)
Lemma stk_up_frame : forall (E : YP0m.env) rs ly (W : world tfibsegs) (mem mem' : word -> option byte) usp,
  forallb drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> top_ok usp ly ->
  frame_of E rs mem mem' -> SU ly W usp mem -> SU ly W usp mem'.
Proof.
intros E rs ly W mem mem' usp Hok E0 U HTOP HF HU a Ha.
destruct (HU a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
destruct HTOP as ((_ & T2) & _). unfold sp_window_lo, sp_window_hi in U.
rewrite HF; [exact Hb|]. intros Hw. rewrite u64_lit in Hw by lia.
destruct (in_wrange_drv E rs a Hok Hw) as [X|X]; [lia|].
pose proof (DRVW_rw a X). lia.
Qed.

(* an allocator call: its post keeps every byte above the ceiling that is off the image and errno *)
Lemma stk_up_acall : forall (B : asyms) stk ly S Hp (W : world tfibsegs) regs mem md (Eb : Z -> Prop)
  ly' S' W' regs' mem' md' usp,
  TfibSyms B -> AR_laws_cf tfibsegs B ->
  acall_post_cf tfibsegs B stk ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' ->
  ARcf tfibsegs B ly S Hp W mem md -> (forall a, Eb a -> a < alloc_ceiling) ->
  sp_window_lo <= usp <= sp_window_hi -> top_ok usp ly ->
  SU ly W usp mem -> SU ly' W' usp mem'.
Proof.
intros B stk ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' usp HB ARL HP HAR HEb U HTOP HU a Ha.
pose proof HP as (HAR' & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). rewrite Etop in Ha.
pose proof (YM05.ceil_le_top _ (top_ok_ceil _ _ HTOP)) as CLE. unfold stack_max_size in CLE.
destruct HTOP as ((_ & T2) & _). unfold sp_window_lo, sp_window_hi in U.
apply (YGcfPres.acall_post_cf_presence tfibsegs B stk ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' HP a).
- lia.
- apply not_in_img_high. lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ a HAR X). lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ a HAR' X). lia.
- rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
- intros X. pose proof (HEb a X). lia.
- apply HU. lia.
Qed.

(* the same after a free under the re-hide (YGcfRehidePost.acall_post_cf_rh): its view frame excepts the set the call
   may hide, which lies below kHighMemBeg (dead_shadow_new_high), so no byte at or above usp; the proof is
   YGcfPres.acall_post_cf_presence's, at that frame *)
Lemma stk_up_acall_rh : forall (B : asyms) stk ly S Hp (W : world tfibsegs) regs mem md (Eb : Z -> Prop)
  ly' S' W' regs' mem' md' usp,
  TfibSyms B -> AR_laws_cf tfibsegs B ->
  YGcfRehidePost.acall_post_cf_rh tfibsegs B stk ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' ->
  ARcf tfibsegs B ly S Hp W mem md -> (forall a, Eb a -> a < alloc_ceiling) ->
  sp_window_lo <= usp <= sp_window_hi -> top_ok usp ly ->
  SU ly W usp mem -> SU ly' W' usp mem'.
Proof.
intros B stk ly S Hp W regs mem md Eb ly' S' W' regs' mem' md' usp HB ARL HP HAR HEb U HTOP HU a Ha.
pose proof HP as (HAR' & Hly & _ & _ & _ & FR & STK).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). rewrite Etop in Ha.
pose proof (YM05.ceil_le_top _ (top_ok_ceil _ _ HTOP)) as CLE. unfold stack_max_size in CLE.
destruct HTOP as ((_ & T2) & _). unfold sp_window_lo, sp_window_hi in U.
assert (Ha0 : 0 <= a < 2 ^ 64) by lia.
assert (C : (spZ regs - stk <= a < spZ regs) \/ ~ ascratch B stk regs a).
{ destruct (Z_le_gt_dec (spZ regs - stk) a); destruct (Z_lt_ge_dec a (spZ regs)); try (left; lia);
  right; intros [X|X]; first [lia | (rewrite (ts_errno B HB) in X; unfold TFIB_ERRNO in X; lia)]. }
destruct C as [C|NS]; [exact (STK a C)|].
apply YGcfPres.cfp_present_of_view with (segs := tfibsegs); [apply YGcfPres.cfp_seg_rom_none; [exact Ha0 | apply not_in_img_high; lia]|].
rewrite (FR a Ha0).
- exact (YGcfPres.cfp_view_of_present tfibsegs _ _ a (HU a Ha)).
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ a HAR X). lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ a HAR' X). lia.
- exact NS.
- intros X. pose proof (HEb a X). lia.
- apply YGcfRehidePost.dead_shadow_new_high. unfold kHighMemBeg. lia.
Qed.

(* a site whose post keeps presence, at the same layout top *)
Lemma stk_up_keep : forall ly ly' (W W' : world tfibsegs) (mem mem' : word -> option byte) usp,
  ly_top ly' = ly_top ly ->
  (forall a, usp <= a < ly_top ly -> apresent (w_H W) mem a -> apresent (w_H W') mem' a) ->
  SU ly W usp mem -> SU ly' W' usp mem'.
Proof. intros ly ly' W W' mem mem' usp Et Hk HU a Ha. rewrite Et in Ha. exact (Hk a Ha (HU a Ha)). Qed.

(* at a call: the window below usp and the invariant above give the slot pre's conjunct at the call's sp *)
Lemma stk_up_at : forall ly (W : world tfibsegs) (mem : word -> option byte) usp spv,
  usp - 65536 <= spv ->
  (forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
  SU ly W usp mem -> SU ly W spv mem.
Proof.
intros ly W mem usp spv Hs Hwin HU a Ha.
destruct (Z_lt_le_dec a usp) as [C|C]; [apply Hwin; lia | apply HU; lia].
Qed.

(* a wider world (wle W W': W' hides a subset of W's bytes, e.g. a Theorem Labs lane's ARcf_nil_init exposing class 1's band
   at main) keeps it *)
Lemma stk_up_wle : forall ly (W W' : world tfibsegs) (mem : word -> option byte) usp,
  wle W W' -> SU ly W usp mem -> SU ly W' usp mem.
Proof.
intros ly W W' mem usp Hs HU a Ha. destruct (HU a Ha) as [Hh Hb]. split; [|exact Hb].
destruct (w_H W' (Z_to_bv 64 a)) eqn:X; [|reflexivity]. rewrite (Hs _ X) in Hh. discriminate Hh.
Qed.
End s.
