(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Image B (asan-ubsan), lane CwPinvB: this file is port/a2b.py's output (sha256 d27cabd1f8478083d9f07152def1d5f8ec74dd77cd91cd60f67a2f0ef4d5b5a2)
   of lib/A/PresetPinvA.v at a working branch 093605f124c5, code unchanged; the comment below is the A
   file's, with names mapped by the translator. *)
(* Modified by Theorem Labs, 2026-10: made from the FINV-stating lemmas of proofs/cgif/cgif_file_fuzzer/lib/YD1u.v,
   YD1v.v:31-71, YD1w.v:181-197 and YD2k.v:113-174 for fuzz_preset's ASan image. Line numbers cite this unit's copies
   lib/A/AD*.v (core relocation of the donor files).
   STATEMENTS of the PINV toolkit (closed-walk lane CwPinvA): each result is a closed `Definition <donor name>_pinv_B :
   Prop`; the proofs are `Theorem <name>_holds` in PresetPinvBPf.v. Nothing here proves a function (rule 24:
   composition / driver layer of a port).
   The change from the donor (plan section 2b; parent's decisions of 2026-10-28):
   (1) cgif's cross-call invariant FINV (YD1u.v:61-64: the sink's metadata ameta_inv, the musl stdio cells, ofl_head)
       is replaced by PINV of lib/AU/PresetCfnB.v: the alloc.c ledger at rest and the musl stdio cells. Before the first
       harness call nothing writes the ledger, so the driver's leaves carry it EXACTLY at the start-up values,
       `PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0` where the donor has `FINV ly (w_H W) (ms_mem ms)`
       (cnt = g_count = 0, ran = g_ran_out = 0); section 2 is that start-up fact. The frame lemmas take any cnt ran.
   (2) PINV reads only fixed image cells and needs no layout, so the lemmas cgif stated over AR only to place the sink's
       metadata block (ly_extra) are stated WITHOUT any allocator invariant. The four that need the allocator's laws
       (a call's frame clause, the client blocks) are over preset's second instance ARcf (a Theorem Labs lane's
       lib/Reusable/YG0ncf.v, YG0dcf.v): from the start-up onward every driver allocator site is over ARcf.
   (3) DROPPED with the sink (parent's decision: preset's driver writes no file): the sink laws tfib_AIL (YD1u.v:35-60,
       with the A_PATH / A_WB / A_RWA / A_TRAILER cells at :46-49), ameta_inv and its block (YD1u.v:62, 66, 131-136,
       209-214), FINV_IVS's sink cells (YD1u.v:67-69) and their cases (YD1u.v:74-76), the image strings of the
       file name / mode / rwa / trailer (YD2k.v:31, 166-169), the FF_meta_ptr exception of the owned-static check
       (YD1u.v:102-114), and finv_lyle (YD1u.v:145-150: no layout in PINV, and no user in the driver).
   Class arguments are universally quantified in each statement, never left to a #[global] instance. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB12 YB1h YB01 YB1n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2i YD1t.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD1y YD1v YD1w YD2f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetCfnB.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.

Local Notation segs := tfibsegs.

(* ---------------------------------------------------------------------- *)
(* 1. The frame lemmas of PINV (donor YD1u.v, YD1v.v:31-71, YD1w.v:181-197). PresetCfnB.v already proves the
      interval form (pinv_img_ivs, pinv_ivs_avoid_sound / _sub = the donor's finv_img_ivs, ivs_avoid_sound / _sub) and
      pinv_frame_view (the donor's finv_frame without ly_extra); they are cited, not restated. *)

(* YD1u.v:94-99 (with FINV_IVS_img, :92): every PINV cell is in the image hull. *)
Definition finv_img_range_pinv_B : Prop :=
forall a, pinv_img a -> YImgTop.IMG_LO_B <= a < YImgTop.IMG_TOP_B.

(* YD1u.v:100-101 *)
Definition finv_img_img_pinv_B : Prop :=
forall a, pinv_img a -> YG0d.in_img segs a.

(* YD1u.v:102-114: no PINV cell is an owned static of the unit (cgif's FF_meta_ptr exception is gone with the sink). *)
Definition finv_img_not_owned_pinv_B : Prop :=
forall B, TfibSyms B -> forall a, pinv_img a -> ~ Exists (in_zr a) (as_owned_static B).

(* YD1u.v:115-121 *)
Definition finv_img_not_drvw_pinv_B : Prop :=
forall a, pinv_img a -> YD1y.DRVW a = true -> False.

(* YD1u.v:122-125 *)
Definition finv_img_not_errno_pinv_B : Prop :=
forall B, TfibSyms B -> forall a, pinv_img a -> ~ (as_errno B <= a < as_errno B + 4).

(* YD1u.v:126-139 *)
Definition finv_frame_pinv_B : Prop :=
forall (H H' : word -> bool) (mem mem' : word -> option byte) cnt ran,
(forall a, pinv_img a -> mbyte segs (mrestrict H' mem') a = mbyte segs (mrestrict H mem) a) ->
PINV (aview segs H mem) cnt ran -> PINV (aview segs H' mem') cnt ran.

(* YD1u.v:140-143 *)
Definition finv_aview_pinv_B : Prop :=
forall (H H' : word -> bool) (mem mem' : word -> option byte) cnt ran,
(forall a, pinv_img a -> aview segs H' mem' a = aview segs H mem a) ->
PINV (aview segs H mem) cnt ran -> PINV (aview segs H' mem') cnt ran.

(* YD1u.v:156-174 (AR and the layout bounds dropped: they only placed the sink's metadata block). *)
Definition finv_stretch_pinv_B : Prop :=
forall (H : word -> bool) E rs (m m' : word -> option byte) usp cnt ran,
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb YD1y.drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp ->
sp_window_lo <= usp ->
PINV (aview segs H m) cnt ran -> PINV (aview segs H m') cnt ran.

(* YD1u.v:175-219, over ARcf: a call's frame clause (acall_post_cf, YG0dcf.v:70) and the owned-static / client-block
   laws (AR_laws_cf, YG0dcf.v:358). The ghost set Hp is any. The call's exception set E may also hold bytes off the
   image (the third disjunct: malloc_leaf_cf's E holds the errbuf extent). *)
Definition finv_acall_post_pinv_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
TfibSyms B -> AR_laws_cf segs B ->
forall stk ly S Hp W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' cnt ran,
ARcf segs B ly S Hp W mem md ->
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n) \/ ~ YG0d.in_img segs a) ->
ly_stk_lo ly <= spZ regs - stk -> spZ regs <= ly_stk_hi ly -> 2 ^ 24 <= spZ regs - stk ->
PINV (aview segs (w_H W) mem) cnt ran -> PINV (aview segs (w_H W') mem') cnt ran.

(* YD1u.v:220-231 (AR dropped). *)
Definition finv_off_pinv_B : Prop :=
forall (H : word -> bool) (mem mem' : word -> option byte) (X1 X2 : Z -> Prop) cnt ran,
(forall a, 0 <= a < 2 ^ 64 -> ~ X1 a -> ~ X2 a -> aview segs H mem' a = aview segs H mem a) ->
(forall a, pinv_img a -> ~ X1 a /\ ~ X2 a) ->
PINV (aview segs H mem) cnt ran -> PINV (aview segs H mem') cnt ran.

(* YD1u.v:232-239, over ARcf (the client-block law). *)
Definition finv_avoids_block_pinv_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
AR_laws_cf segs B -> forall ly S Hp W mem md p n a,
ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
pinv_img a -> ~ (p <= a < p + req_size n).

(* YD1u.v:240-247 (AR and the layout bounds dropped). *)
Definition finv_avoids_stack_pinv_B : Prop :=
forall lo hi a, 2 ^ 24 <= lo -> pinv_img a -> ~ (lo <= a < hi).

(* YD1u.v:248-255 (AR and the in-image premise dropped). *)
Definition finv_avoids_img_pinv_B : Prop :=
forall lo hi a, pinv_ivs_avoid lo hi = true -> pinv_img a -> ~ (lo <= a < hi).

(* YD1u.v:256-262 *)
Definition finv_fp_u64_pinv_B : Prop :=
forall a, pinv_img a -> 0 <= a < 2 ^ 64.

(* YD1u.v:263-273 (AR and the in-image premise dropped). *)
Definition finv_img_write_pinv_B : Prop :=
forall (H : word -> bool) (m m' : word -> option byte) lo hi cnt ran,
(forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> m' x = m x) ->
pinv_ivs_avoid lo hi = true ->
PINV (aview segs H m) cnt ran -> PINV (aview segs H m') cnt ran.

(* YD1v.v:31-40 (AR, the layout and top_ok dropped: the driver's windows and its stack avoid the cells). *)
Definition finv_run_pinv_B : Prop :=
forall (H : word -> bool) E rs (m m' : word -> option byte) usp cnt ran,
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb YD1y.drv_win_ok rs = true ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp ->
PINV (aview segs H m) cnt ran -> PINV (aview segs H m') cnt ran.

(* YD1v.v:41-54, over ARcf (the donor's other premises). *)
Definition finv_site_pinv_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
TfibSyms B -> AR_laws_cf segs B ->
forall stk ly S Hp (W : world segs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp cnt ran,
ARcf segs B ly S Hp W mem md -> acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n) \/ ~ YG0d.in_img segs a) ->
YD1v.top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
PINV (aview segs (w_H W) mem) cnt ran -> PINV (aview segs (w_H W') mem') cnt ran.

(* the same after a free under the re-hide: the call post YGcfRehidePost.acall_post_cf_rh, whose view frame also
   excepts the set the call may hide (dead_shadow_new, in the shadow of the application ranges, so off the image) *)
Definition finv_site_pinv_rh_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
TfibSyms B -> AR_laws_cf segs B ->
forall stk ly S Hp (W : world segs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp cnt ran,
ARcf segs B ly S Hp W mem md ->
YGcfRehidePost.acall_post_cf_rh segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n) \/ ~ YG0d.in_img segs a) ->
YD1v.top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
PINV (aview segs (w_H W) mem) cnt ran -> PINV (aview segs (w_H W') mem') cnt ran.

(* YD1v.v:55-71, over ARcf (the donor's other premises). *)
Definition finv_icpt_pinv_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
TfibSyms B -> AR_laws_cf segs B ->
forall ly S Hp (W : world segs) mem md (mem' : word -> option byte) (P : Z -> Prop) lo hi usp cnt ran,
ARcf segs B ly S Hp W mem md -> YD1v.top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> ~ (lo <= a < hi) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
usp - 65536 <= lo -> hi <= usp ->
(forall a, P a -> exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
PINV (aview segs (w_H W) mem) cnt ran -> PINV (aview segs (w_H W) mem') cnt ran.

(* YD1w.v:181-197 (AR, the layout and top_ok dropped). *)
Definition finv_printf_pinv_B : Prop :=
forall (H : word -> bool) (mem mem' : word -> option byte) usp splo cnt ran,
sp_window_lo <= usp -> usp - 4096 <= splo <= usp ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (splo - PF_STK <= a < splo) -> ~ STDOUT_MUT a -> aview segs H mem' a = aview segs H mem a) ->
PINV (aview segs H mem) cnt ran -> PINV (aview segs H mem') cnt ran.

(* ---------------------------------------------------------------------- *)
(* 2. The start-up certificate gives PINV at the image values (donor YD2k.v:113-174, tfib_finv_handoff): the four .bss
      ledger cells g_ran_out = g_live = g_peak = g_count = 0, g_fail_at = SIZE_MAX (its 8 .data image bytes are ff), the
      stdio cells threaded = need_locks = ofl_lock = 0 and ofl_head = NULL; so cnt = ran = 0. Quantifiers: YD2k.v's
      Section e; the world is the driver's start-up world W1 (lib/Reusable/YD2i.v:768). #102 / W8 core (int102
      preset-tree-at-2026-10-29T21-08-23Z.tsv (sha256 7ae478810979; internal record)): W1 takes the proof of its section hypothesis H1_8 (YD2i.v:507, the world field w_H8); the
      statement holds at every such proof (PINV reads w_H W1 = YD2i.H1 only), so the proof is a binder H8 here and
      the driver passes PWorldH8.H1_H8 (lib/AU/PWorldH8.v:370), as YD1d.v:232 / YD1f.v:99 do. *)
Definition tfib_finv_handoff_pinv_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil)
(sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
(Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)) (h : nat)
(ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
(H8 : forall a : Z, YG0f.in_band_rw a ->
  YD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a) = YD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8))),
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
PINV (aview segs (w_H (YD2i.W1 sp rdraw inp Hsp Hva ch E model H8)) FULL) 0 0.

