(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 452 of its 508 lines of code are new or changed and 648 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeam.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan: module paths changed; 25 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); re-pointed Requires: FMupoison -> lib.A.Rt, FMsnprintfPf -> lib.A.Rt, FMsnprintfShared -> lib.A.Rt, FMsnprintfSx -> lib.A.Rt, FMgxaSeamNorm / FMgxaSeamReady and the FMgxaSeam* kit -> lib.A.Rt; name TfibSyms -> BoxregSyms (1x; boxreg's lib/A/AF0m.v record); GXA symbol keys 0x22e18 / 0x34288 / 0x1029e kept (keys of boxreg lib/A/RT_IImgA.v A_exact :70 / :72, not fm addresses). fm's 7e395de08f5 -> 3e35620c52e change of this file applied (git diff of lib/A/FMgxaSeam.v: GXA (5) in READY, then READY at the per-call store FMgxaSeamNorm.cjnormv ly R over the carve-out list NM.seam_R with FMgxaSeamReady's stack_hull / prefix_hull; the one address numeral in the change is the kept key 0x1029e, port_addr_check 0767e70e074a predict UNRESOLVED-SOURCE). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Rt/FMgxaSeam.v, with its module paths and module names changed; 975 of its 1040 lines of code are new or changed and 443 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeamReady.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan: module paths changed; 12 address numerals relocated (port_addr_check 0767e70e074a predict mode, symbol + offset), 2 of them by hand where predict gave no value (:759 / :763 0x20d00 -> 0x20cc0, the end of the image's first zero-shadow range = ZERO+0x0 of boxreg's lib/A/AF0m.v, as lib/A/Rt/FMgxaSeamShadow.v relocated the same numeral; the third 0x20d00, in the comment above them, with them); GXA symbol keys 0x1029e / 0x22e18 kept (keys of boxreg lib/A/RT_IImgA.v A_exact, not fm addresses); name TfibSyms -> BoxregSyms (boxreg's lib/A/AF0m.v record); re-pointed Requires: FMupoison, FMgxaSeamBase, FMgxaSeamShadow, FMgxaSeamNorm, FMgxaSeamNormG, FMgxaSeamGuard -> lib.A.Rt; FMgxa_mem -> lib.A.RT_gxa_calls_mem; RT_gxa_strnlen -> lib.A.RT_gxa_calls. New file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Rt/FMgxaSeamReady.v, with its module paths and addresses changed; 30 of its 170 lines of code are new or changed and 900 lines of the source are left out. *)
(* READINESS OF THE THREE INTERCEPTORS, THE AR HALF: the facts about the harness's state that the GXA seam's assembly
   (PSnpSeam.v: stack_hull, prefix_hull) and the clauses (PSnpSeamReady.v) read, split out of port-fm's
   FMgxaSeamReady.v so that PSnpSeam.v needs no interceptor contract.  From FMgxaSeamReady.v's header, items 1-3 and 5:
   the hull lemmas over any reader (hull_sub, hull_prefix, hull_in_shadow, hull_kept), a visible hull over any stack
   range (stack_view0, stack_hull, stack_rng) and the musl prefix's hull (prefix_hull: the zero shadow of the image's
   first range), and the shadow band's word arithmetic (band_word, shadow_band). *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's restatement for fuzz_preset image A (L3-V2, the GXA seam over ARx;
   parent c-libc-stdio 14:3xZ) of part of proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamReady.v at
   origin/cold/port-fm-rtprintf-param 3e35620c52e (its :152-318 without the FMgxa_bzcj / FMgxaSeamNorm lemmas,
   :669-775 and :1044-1057), over the engine's ARx with the ghost head list Hp passed through unchanged instead of
   Poison's ARU over U (FMupoison.v is not ported): the stack's zero shadow from AR_laws_x's alx_zshadow_byte (in place
   of am_zshadow at the stack range, ARU_view_out, ARU_shadow_out_block and ARU_stack_not_block: ARx is over mem itself,
   no user poison), the layout from alx_layout_ok (in place of am_layout), the prefix's zero shadow from alx_zshadow (in
   place of am_zshadow and the in_ush / ARU_poisoned split); module paths fuzz_manifest -> fuzz_preset, lib/A/Bz ->
   lib/A/PSnpBz, RT_IImgA.A_img -> CJ.RL.I.IImgA.N_img_asan; preset A's numbers: musl's prefix at sym 0x1029e = 0x10b74 in
   the first zero-shadow range (0x10000, 0x20f40 - 0x10000) (AF0m.v Tfib_zero_shadow; PSnpSeamShadow.v
   sym_musl_prefix / zsh_rodata_of_tfib). *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpSeamReadyAR.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YG0q YI04 YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
AB1v AF0m AF0x PSnpSeamBase PSnpSeamShadow.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import
IImgA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.MemNorm.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_printf_core_common.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Common.PropExec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.Shadow.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Spec.StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module CJM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Mem.
Module GAF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.AsanFacts.
Module BSh := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.Shadow.
Module BQ := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_qck.
(* this file does not Import RStep, where the image's symbol map `sym` lives *)
Module RSt := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc.RStep.

#[local] Existing Instance N_img_asan.

(* ===================================================================================== *)
(* 1. the generic lemmas, over any CJ store                                                *)
(* ===================================================================================== *)

(* the reader of a CJ store, the way the harness's aview reads cjstore (FMgxaSeamBase.aview_mrd) *)
Definition sview (m : word -> option byte) : Z -> option Z :=
  fun a => option_map (fun b : byte => bv_unsigned b) (CJM.mrd tfibsegs m (CJM.wa a)).

(* the quick check's aligned word is the hull's bound: al8 (shad a) = shadow_addr a / 8 * 8 *)
Lemma al8_shad_hull : forall a, BQ.al8 (BSh.shad a) = shadow_addr a / 8 * 8.
Proof.
intros a. unfold BQ.al8, BSh.shad, BSh.SHB, shadow_addr, SHADOW_OFF.
replace (a / 8 + 2147450880) with (2147450880 + a / 8) by lia. lia.
Qed.

Lemma hull_lo_le_hi : forall x n, 0 < n -> shadow_addr x / 8 * 8 <= shadow_addr (x + n - 1) / 8 * 8.
Proof.
intros x n Hn. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
Qed.

(* the hull of a sub-range lies in the hull of the range *)
Lemma hull_sub : forall (rd : Z -> option Z) p n p' k,
  shadow_hull_vis rd p n -> p <= p' -> 0 < k -> p' + k <= p + n -> shadow_hull_vis rd p' k.
Proof.
intros rd p n p' k HV H1 H2 H3 s Hs. apply HV.
assert (L : shadow_addr p / 8 * 8 <= shadow_addr p' / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (U : shadow_addr (p' + k - 1) / 8 * 8 <= shadow_addr (p + n - 1) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

Lemma hull_prefix : forall (rd : Z -> option Z) p n k,
  shadow_hull_vis rd p n -> 0 < k <= n -> shadow_hull_vis rd p k.
Proof. intros rd p n k HV Hk. exact (hull_sub rd p n p k HV ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* ---- over the harness's store: the two readers are the same reader ---- *)
Section V. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma aview_sview : forall H mem, aview tfibsegs H mem = sview (cjstore H mem).
Proof. reflexivity. Qed.

End V.

(* ===================================================================================== *)
(* 3. a hull carries to every store that keeps the shadow                                 *)
(* ===================================================================================== *)

(* the hull of a range of application memory lies in ASan's shadow *)
Lemma hull_in_shadow : forall p n s, 0 < n -> GAF.app_ivl p (p + n) ->
  shadow_addr p / 8 * 8 <= s < shadow_addr (p + n - 1) / 8 * 8 + 8 -> GAF.in_shadow s.
Proof.
intros p n s Hn HA Hs.
pose proof (HA p ltac:(lia)) as A0. pose proof (HA (p + n - 1) ltac:(lia)) as A1.
unfold GAF.app_mem in A0, A1.
assert (C : p + n - 1 < GAF.LOWMEM_END \/ GAF.HIGHMEM_BEG <= p).
{ destruct (Z_lt_le_dec (p + n - 1) GAF.LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct A0 as [A0|A0]; [|lia].
  exfalso. pose proof (HA GAF.LOWMEM_END ltac:(lia)) as X.
  unfold GAF.app_mem, GAF.LOWMEM_END, GAF.HIGHMEM_BEG, GAF.APPMEM_END in X. lia. }
unfold GAF.in_shadow. unfold shadow_addr, SHADOW_OFF in Hs.
unfold GAF.LOWMEM_END, GAF.LOWSHADOW_END, GAF.HIGHSHADOW_BEG, GAF.HIGHMEM_BEG, GAF.APPMEM_END in *.
clear HA.
destruct C as [C|C]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

Lemma hull_kept : forall (m m' : word -> option byte) p n, GAF.meta_kept m m' ->
  0 < n -> GAF.app_ivl p (p + n) ->
  shadow_hull_vis (sview m) p n -> shadow_hull_vis (sview m') p n.
Proof.
intros m m' p n MK Hn HA HV s Hs.
pose proof (MK s (hull_in_shadow p n s Hn HA Hs)) as E. pose proof (HV s Hs) as V.
unfold sview in *.
destruct (CJM.mrd tfibsegs m (CJM.wa s)) as [b|] eqn:Em; [|exfalso; apply V; reflexivity].
assert (E' : CJM.mrd tfibsegs m' (CJM.wa s) = Some b) by (etransitivity; [exact E | exact Em]).
rewrite E'. discriminate.
Qed.

Lemma pf_rng_app : forall (m : word -> option byte) p n, GAF.pf_rng m p n -> GAF.app_ivl p (p + n).
Proof. intros m p n (_ & AD & _). exact (GAF.addressable_app m p n AD). Qed.

(* ---- the stack and musl's prefix, over ARx ---- *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
(* the AR_laws_x fields this file uses (YCbqG.v), each under its field's name *)
Hypothesis alx_zshadow : ARx_zshadow_law tfibsegs B ARx.
Hypothesis alx_zshadow_byte : ARx_zshadow_byte_law tfibsegs ARx.
Hypothesis alx_layout_ok : ARx_layout_ok_law tfibsegs ARx.

(* the stack: AR_laws_x's zero shadow byte over [ly_stk_lo, ly_stk_hi) (alx_zshadow_byte) *)
Lemma stack_view0 : forall ly S Hp (W : world tfibsegs) mem md a, ARx ly S Hp W mem md ->
  ly_stk_lo ly <= a < ly_stk_hi ly -> aview tfibsegs (w_H W) mem (shadow_addr a) = Some 0.
Proof.
intros ly S Hp W mem md a HAR Ha.
replace (shadow_addr a) with (SHADOW_OFF + a / 8) by (unfold shadow_addr; reflexivity).
exact (alx_zshadow_byte ly S Hp W mem md a HAR Ha).
Qed.

(* the hull of a stack range is visible: every byte of it is a shadow byte of the stack, whose ends layout_ok
   page-aligns (lo_top) *)
Lemma stack_hull : forall ly S Hp (W : world tfibsegs) mem md x n, ARx ly S Hp W mem md ->
  ly_stk_lo ly <= x -> 0 < n -> x + n <= ly_stk_hi ly ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros ly S Hp W mem md x n HAR Hx Hn Hxn.
pose proof (alx_layout_ok ly S Hp W mem md HAR) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
unfold page_aligned in T5, T6.
intros s Hs.
assert (Ea : shadow_addr (8 * (s - SHADOW_OFF)) = s)
  by (unfold shadow_addr; Z.div_mod_to_equations; lia).
assert (Ha : ly_stk_lo ly <= 8 * (s - SHADOW_OFF) < ly_stk_hi ly).
{ unfold shadow_addr, SHADOW_OFF in Hs. unfold SHADOW_OFF. clear - Hs Hx Hn Hxn T5 T6.
  Z.div_mod_to_equations. lia. }
rewrite <- Ea, (stack_view0 ly S Hp W mem md _ HAR Ha). discriminate.
Qed.

(* a stack range is addressable for GXA and its hull is visible *)
Lemma stack_rng : forall ly S Hp (W : world tfibsegs) mem md x n, ARx ly S Hp W mem md ->
  ly_stk_lo ly <= x -> 0 <= n -> x + n + 9 <= ly_stk_hi ly ->
  GAF.pf_rng (cjstore (w_H W) mem) x n /\ (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n).
Proof.
intros ly S Hp W mem md x n HAR Hx Hn Hxn.
pose proof (alx_layout_ok ly S Hp W mem md HAR) as LO.
pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (lo_stk_ceil ly LO) as SC. pose proof ASAN_CEIL_range as [CR _].
unfold page_aligned in T5, T6.
split.
- apply pf_rng_of_view.
  + unfold kHighMemBeg in T7. lia.
  + exact Hn.
  + unfold kHighMemEnd in T4. lia.
  + right. split; lia.
  + intros y Hy. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF y) with (shadow_addr y) by (unfold shadow_of_addr, shadow_addr; lia).
    apply (stack_view0 ly S Hp W mem md y HAR). lia.
- intros Hn0. exact (stack_hull ly S Hp W mem md x n HAR Hx Hn0 ltac:(lia)).
Qed.

(* the musl prefix's hull: the nine bytes at sym 0x1029e = 0x10b74 have their hull in the shadow of the image's first
   zero-shadow range [0x10000, 0x20f40), which AR_laws_x's alx_zshadow fills with 0 *)
Lemma prefix_hull : forall ly S Hp (W : world tfibsegs) mem md,
  TfibSyms B -> ARx ly S Hp W mem md ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) (@RSt.sym N_img_asan 0x1029e) 9.
Proof.
intros ly S Hp W mem md HTB HAR.
pose proof (alx_zshadow ly S Hp W mem md (0x10000, 0x20f60 - 0x10000) HAR
              ltac:(unfold zero_shadow_ranges; right; exact (zsh_rodata_of_tfib B HTB))) as HZ0.
cbn [fst snd] in HZ0. unfold zero_shadow in HZ0.
rewrite sym_musl_prefix. intros s Hs.
assert (Hr : 0x10000 <= 8 * (s - SHADOW_OFF) < 0x20f60).
{ unfold shadow_addr, SHADOW_OFF in Hs. unfold SHADOW_OFF. clear - Hs. Z.div_mod_to_equations. lia. }
assert (E : shadow_of_addr SHADOW_OFF 0x10000 + (s - SHADOW_OFF - 0x10000 / 8) = s)
  by (unfold shadow_of_addr; clear - Hr; Z.div_mod_to_equations; lia).
assert (Hv : aview tfibsegs (w_H W) mem s = Some 0)
  by (rewrite <- E; apply HZ0; clear - Hr; Z.div_mod_to_equations; lia).
rewrite Hv. discriminate.
Qed.

End C.

(* the band's four ends are multiples of 8: an 8-aligned word with a byte in the band lies in it *)
Lemma band_word : forall s0 s, in_band_rw s0 -> s / 8 = s0 / 8 -> in_band_rw s.
Proof.
intros s0 s Hb E. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *.
Z.div_mod_to_equations. lia.
Qed.

(* the shadow byte of a byte of application memory is in the band *)
Lemma shadow_band : forall x, GAF.app_mem x -> in_band_rw (shadow_addr x).
Proof.
intros x Hx. unfold GAF.app_mem, GAF.LOWMEM_END, GAF.HIGHMEM_BEG, GAF.APPMEM_END in Hx.
unfold in_band_rw, shadow_addr, SHADOW_OFF, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd.
Z.div_mod_to_equations. lia.
Qed.

