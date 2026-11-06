(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the FINV-stating lemmas of proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v,
   AD1v.v:31-71, AD1w.v:181-197 and AD2k.v:113-174 for fuzz_preset's ASan image. Line numbers cite this unit's copies
   lib/A/AD*.v (core relocation of the donor files).
   STATEMENTS of the PINV toolkit (closed-walk lane CwPinvA): each result is a closed `Definition <donor name>_pinv_A :
   Prop`; the proofs are `Theorem <name>_holds` in PresetPinvAPf.v. Nothing here proves a function (rule 24:
   composition / driver layer of a port).
   The change from the donor (plan section 2b; parent's decisions of 2026-10-28):
   (1) cgif's cross-call invariant FINV (AD1u.v:61-64: the sink's metadata ameta_inv, the musl stdio cells, ofl_head)
       is replaced by PINV of lib/A/PresetCfnA.v: the alloc.c ledger at rest and the musl stdio cells. Before the first
       harness call nothing writes the ledger, so the driver's leaves carry it EXACTLY at the start-up values,
       `PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0` where the donor has `FINV ly (w_H W) (ms_mem ms)`
       (cnt = g_count = 0, ran = g_ran_out = 0); section 2 is that start-up fact. The frame lemmas take any cnt ran.
   (2) PINV reads only fixed image cells and needs no layout, so the lemmas cgif stated over AR only to place the sink's
       metadata block (ly_extra) are stated WITHOUT any allocator invariant. The four that need the allocator's laws
       (a call's frame clause, the client blocks) are over preset's second instance ARcf (h-mani-a8's
       lib/Reusable/YG0ncf.v, YG0dcf.v): from the start-up onward every driver allocator site is over ARcf.
   (3) DROPPED with the sink (parent's decision: preset's driver writes no file): the sink laws tfib_AIL (AD1u.v:35-60,
       with the A_PATH / A_WB / A_RWA / A_TRAILER cells at :46-49), ameta_inv and its block (AD1u.v:62, 66, 131-136,
       209-214), FINV_IVS's sink cells (AD1u.v:67-69) and their cases (AD1u.v:74-76), the image strings of the
       file name / mode / rwa / trailer (AD2k.v:31, 166-169), the FF_meta_ptr exception of the owned-static check
       (AD1u.v:102-114), and finv_lyle (AD1u.v:145-150: no layout in PINV, and no user in the driver).
   Class arguments are universally quantified in each statement, never left to a #[global] instance. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetPinvA.v, with its module paths changed; 20 of its 148 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: made from the FINV-stating lemmas of proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v,
   AD1v.v:31-71, AD1w.v:181-197 and AD2k.v:113-174 for fuzz_preset's ASan image. Line numbers cite this unit's copies
   lib/A/AD*.v (core relocation of the donor files).
   STATEMENTS of the PINV toolkit (closed-walk lane CwPinvA): each result is a closed `Definition <donor name>_pinv_A :
   Prop`; the proofs are `Theorem <name>_holds` in PresetPinvAPf.v. Nothing here proves a function (rule 24:
   composition / driver layer of a port).
   The change from the donor (plan section 2b; parent's decisions of 2026-10-28):
   (1) cgif's cross-call invariant FINV (AD1u.v:61-64: the sink's metadata ameta_inv, the musl stdio cells, ofl_head)
       is replaced by PINV of lib/A/PresetCfnA.v: the alloc.c ledger at rest and the musl stdio cells. Before the first
       harness call nothing writes the ledger, so the driver's leaves carry it EXACTLY at the start-up values,
       `PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0` where the donor has `FINV ly (w_H W) (ms_mem ms)`
       (cnt = g_count = 0, ran = g_ran_out = 0); section 2 is that start-up fact. The frame lemmas take any cnt ran.
   (2) PINV reads only fixed image cells and needs no layout, so the lemmas cgif stated over AR only to place the sink's
       metadata block (ly_extra) are stated WITHOUT any allocator invariant. The four that need the allocator's laws
       (a call's frame clause, the client blocks) are over preset's second instance ARcf (a Theorem Labs lane's
       lib/Reusable/YG0ncf.v, YG0dcf.v): from the start-up onward every driver allocator site is over ARcf.
   (3) DROPPED with the sink (parent's decision: preset's driver writes no file): the sink laws tfib_AIL (AD1u.v:35-60,
       with the A_PATH / A_WB / A_RWA / A_TRAILER cells at :46-49), ameta_inv and its block (AD1u.v:62, 66, 131-136,
       209-214), FINV_IVS's sink cells (AD1u.v:67-69) and their cases (AD1u.v:74-76), the image strings of the
       file name / mode / rwa / trailer (AD2k.v:31, 166-169), the FF_meta_ptr exception of the owned-static check
       (AD1u.v:102-114), and finv_lyle (AD1u.v:145-150: no layout in PINV, and no user in the driver).
   Class arguments are universally quantified in each statement, never left to a #[global] instance. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB01 AB1n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YG00 YG01 YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP09 YP0l YP08 YP03 YN3q YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD2i AD1t.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD1y AD1v AD1w AD2f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetCfnA.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.

Local Notation segs := tfibsegs.

(* ---------------------------------------------------------------------- *)
(* 1. The frame lemmas of PINV (donor AD1u.v, AD1v.v:31-71, AD1w.v:181-197). PresetCfnA.v already proves the
      interval form (pinv_img_ivs, pinv_ivs_avoid_sound / _sub = the donor's finv_img_ivs, ivs_avoid_sound / _sub) and
      pinv_frame_view (the donor's finv_frame without ly_extra); they are cited, not restated. *)

(* AD1u.v:94-99 (with FINV_IVS_img, :92): every PINV cell is in the image hull. *)
Definition finv_img_range_pinv_A : Prop :=
forall a, pinv_img a -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP.

(* AD1u.v:100-101 *)
Definition finv_img_img_pinv_A : Prop :=
forall a, pinv_img a -> YG0d.in_img segs a.

(* AD1u.v:102-114: no PINV cell is an owned static of the unit (cgif's FF_meta_ptr exception is gone with the sink). *)
Definition finv_img_not_owned_pinv_A : Prop :=
forall B, TfibSyms B -> forall a, pinv_img a -> ~ Exists (in_zr a) (as_owned_static B).

(* AD1u.v:115-121 *)
Definition finv_img_not_drvw_pinv_A : Prop :=
forall a, pinv_img a -> AD1y.DRVW a = true -> False.

(* AD1u.v:122-125 *)
Definition finv_img_not_errno_pinv_A : Prop :=
forall B, TfibSyms B -> forall a, pinv_img a -> ~ (as_errno B <= a < as_errno B + 4).

(* AD1u.v:126-139 *)
Definition finv_frame_pinv_A : Prop :=
forall (H H' : word -> bool) (mem mem' : word -> option byte) cnt ran,
(forall a, pinv_img a -> mbyte segs (mrestrict H' mem') a = mbyte segs (mrestrict H mem) a) ->
PINV (aview segs H mem) cnt ran -> PINV (aview segs H' mem') cnt ran.

(* AD1u.v:140-143 *)
Definition finv_aview_pinv_A : Prop :=
forall (H H' : word -> bool) (mem mem' : word -> option byte) cnt ran,
(forall a, pinv_img a -> aview segs H' mem' a = aview segs H mem a) ->
PINV (aview segs H mem) cnt ran -> PINV (aview segs H' mem') cnt ran.

(* AD1u.v:156-174 (AR and the layout bounds dropped: they only placed the sink's metadata block). *)
Definition finv_stretch_pinv_A : Prop :=
forall (H : word -> bool) E rs (m m' : word -> option byte) usp cnt ran,
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb AD1y.drv_win_ok rs = true -> bv_unsigned (ew E 0) = usp ->
sp_window_lo <= usp ->
PINV (aview segs H m) cnt ran -> PINV (aview segs H m') cnt ran.

(* AD1u.v:175-219, over ARcf: a call's frame clause (acall_post_cf, YG0dcf.v:70) and the owned-static / client-block
   laws (AR_laws_cf, YG0dcf.v:358). The ghost set Hp is any. The call's exception set E may also hold bytes off the
   image (the third disjunct: malloc_leaf_cf's E holds the errbuf extent). *)
Definition finv_acall_post_pinv_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
TfibSyms B -> AR_laws_cf segs B ->
forall stk ly S Hp W regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' cnt ran,
ARcf segs B ly S Hp W mem md ->
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n) \/ ~ YG0d.in_img segs a) ->
ly_stk_lo ly <= spZ regs - stk -> spZ regs <= ly_stk_hi ly -> 2 ^ 24 <= spZ regs - stk ->
PINV (aview segs (w_H W) mem) cnt ran -> PINV (aview segs (w_H W') mem') cnt ran.

(* AD1u.v:220-231 (AR dropped). *)
Definition finv_off_pinv_A : Prop :=
forall (H : word -> bool) (mem mem' : word -> option byte) (X1 X2 : Z -> Prop) cnt ran,
(forall a, 0 <= a < 2 ^ 64 -> ~ X1 a -> ~ X2 a -> aview segs H mem' a = aview segs H mem a) ->
(forall a, pinv_img a -> ~ X1 a /\ ~ X2 a) ->
PINV (aview segs H mem) cnt ran -> PINV (aview segs H mem') cnt ran.

(* AD1u.v:232-239, over ARcf (the client-block law). *)
Definition finv_avoids_block_pinv_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
AR_laws_cf segs B -> forall ly S Hp W mem md p n a,
ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
pinv_img a -> ~ (p <= a < p + req_size n).

(* AD1u.v:240-247 (AR and the layout bounds dropped). *)
Definition finv_avoids_stack_pinv_A : Prop :=
forall lo hi a, 2 ^ 24 <= lo -> pinv_img a -> ~ (lo <= a < hi).

(* AD1u.v:248-255 (AR and the in-image premise dropped). *)
Definition finv_avoids_img_pinv_A : Prop :=
forall lo hi a, pinv_ivs_avoid lo hi = true -> pinv_img a -> ~ (lo <= a < hi).

(* AD1u.v:256-262 *)
Definition finv_fp_u64_pinv_A : Prop :=
forall a, pinv_img a -> 0 <= a < 2 ^ 64.

(* AD1u.v:263-273 (AR and the in-image premise dropped). *)
Definition finv_img_write_pinv_A : Prop :=
forall (H : word -> bool) (m m' : word -> option byte) lo hi cnt ran,
(forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> m' x = m x) ->
pinv_ivs_avoid lo hi = true ->
PINV (aview segs H m) cnt ran -> PINV (aview segs H m') cnt ran.

(* AD1v.v:31-40 (AR, the layout and top_ok dropped: the driver's windows and its stack avoid the cells). *)
Definition finv_run_pinv_A : Prop :=
forall (H : word -> bool) E rs (m m' : word -> option byte) usp cnt ran,
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb AD1y.drv_win_ok rs = true ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp ->
PINV (aview segs H m) cnt ran -> PINV (aview segs H m') cnt ran.

(* AD1v.v:41-54, over ARcf (the donor's other premises). *)
Definition finv_site_pinv_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
TfibSyms B -> AR_laws_cf segs B ->
forall stk ly S Hp (W : world segs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp cnt ran,
ARcf segs B ly S Hp W mem md -> acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n) \/ ~ YG0d.in_img segs a) ->
AD1v.top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
PINV (aview segs (w_H W) mem) cnt ran -> PINV (aview segs (w_H W') mem') cnt ran.

(* the same after a free under the re-hide: the call post YGcfRehidePost.acall_post_cf_rh, whose view frame also
   excepts the set the call may hide (dead_shadow_new, in the shadow of the application ranges, so off the image) *)
Definition finv_site_pinv_rh_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
TfibSyms B -> AR_laws_cf segs B ->
forall stk ly S Hp (W : world segs) regs mem md (E : Z -> Prop) ly' S' W' regs' mem' md' usp cnt ran,
ARcf segs B ly S Hp W mem md ->
YGcfRehidePost.acall_post_cf_rh segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
(forall a, E a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(exists p n, In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n) \/ ~ YG0d.in_img segs a) ->
AD1v.top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi -> usp - 4096 <= spZ regs <= usp -> 0 <= stk <= 65536 ->
PINV (aview segs (w_H W) mem) cnt ran -> PINV (aview segs (w_H W') mem') cnt ran.

(* AD1v.v:55-71, over ARcf (the donor's other premises). *)
Definition finv_icpt_pinv_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) B,
TfibSyms B -> AR_laws_cf segs B ->
forall ly S Hp (W : world segs) mem md (mem' : word -> option byte) (P : Z -> Prop) lo hi usp cnt ran,
ARcf segs B ly S Hp W mem md -> AD1v.top_ok usp ly -> sp_window_lo <= usp -> usp <= sp_window_hi ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P a -> ~ (lo <= a < hi) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
usp - 65536 <= lo -> hi <= usp ->
(forall a, P a -> exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
PINV (aview segs (w_H W) mem) cnt ran -> PINV (aview segs (w_H W) mem') cnt ran.

(* AD1w.v:181-197 (AR, the layout and top_ok dropped). *)
Definition finv_printf_pinv_A : Prop :=
forall (H : word -> bool) (mem mem' : word -> option byte) usp splo cnt ran,
sp_window_lo <= usp -> usp - 4096 <= splo <= usp ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (splo - PF_STK <= a < splo) -> ~ STDOUT_MUT a -> aview segs H mem' a = aview segs H mem a) ->
PINV (aview segs H mem) cnt ran -> PINV (aview segs H mem') cnt ran.

(* ---------------------------------------------------------------------- *)
(* 2. The start-up certificate gives PINV at the image values (donor AD2k.v:113-174, tfib_finv_handoff): the four .bss
      ledger cells g_ran_out = g_live = g_peak = g_count = 0, g_fail_at = SIZE_MAX (its 8 .data image bytes are ff), the
      stdio cells threaded = need_locks = ofl_lock = 0 and ofl_head = NULL; so cnt = ran = 0. Quantifiers: AD2k.v's
      Section e; the world is the driver's start-up world W1 (lib/A/AD2i.v:768). #102 / W8 core (int102
      preset-tree-at-2026-10-29T21-08-23Z.tsv (sha256 7ae478810979; internal record)): W1 takes the proof of its section hypothesis H1_8 (AD2i.v:507, the world field w_H8); the
      statement holds at every such proof (PINV reads w_H W1 = AD2i.H1 only), so the proof is a binder H8 here and
      the driver passes PWorldH8.H1_H8 (lib/A/PWorldH8.v), as AD1d.v / AD1f.v:98 do. *)
Definition tfib_finv_handoff_pinv_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil)
(sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
(Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)) (h : nat)
(ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
(H8 : forall a : Z, YG0f.in_band_rw a ->
  AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a) = AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8))),
HS_tfib h = Some ch ->
cs_ok TSEGS TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 TSEGS TPH sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
PINV (aview segs (w_H (AD2i.W1 sp rdraw inp Hsp Hva ch E model H8)) FULL) 0 0.

