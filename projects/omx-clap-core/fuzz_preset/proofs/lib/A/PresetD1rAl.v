(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan image A), the three LINK statements of the per-call loop's
   proof (lib/A/PresetD1rAPf.v), in a file of their own so that any consumer needs no driver file. STATEMENTS ONLY;
   nothing here proves a function (rule 24). The program interface lib/A/PresetCfnA.v (since 3f83c075b61f) makes
   ablocks_cf, afn_pre_cf and ajournal_cf constants, abbreviations of lib/Reusable/YCbqG.v's journal layer at
   ARx := ARcf; each link states exactly the content the loop uses, and lib/A/PresetD1rAlPf.v proves all three at
   those constants by unfolding:
   - ablocks_link_A: ablocks_cf is cgif's ablocks (YG0dcf.v's AR_blocks_law_cf is stated over ablocks);
   - afn_pre_link_A: YCbqG.v's afn_pre_x at ARx := ARcf tfibsegs B, as a sufficient condition;
   - ajournal_link_A: YCbqG.v's ajournal_x at ARx := ARcf tfibsegs B, at the interface's empty footprint and empty
     own list, the conjuncts the loop uses; its image clause's `~ Exists (in_zr a) PST` is read as
     `~ PCA.ledger_img a` (PST = prh_pst, alloc.c's six statics and fuzz_preset.c's g_own_ran_out, whose bytes are ledger_img's), and its
     `fp_spares [] a` holds at the empty footprint.
   The allocator instance's parameters are preset's: CfParams_preset (lib/A/CfParamsPreset.v), the only CfParams
   instance here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section s.
Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Variable B : asyms.
Variable ablocks_cf : forall (segs : list Segment) (B : asyms) (ly : alayout) (S : astate), list (Z * Z).
Variable afn_pre_cf : forall (segs : list Segment) (B : asyms) (STK : Z) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)), Prop.
Variable ajournal_cf : forall (segs : list Segment) (B : asyms) (STK sp0 : Z) (FP : list (Z * Z))
  (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
  (own : list (Z * Z))
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte)
  (md' : Model) (k : Z), Prop.

Definition ablocks_link_A : Prop := forall ly S, ablocks_cf tfibsegs B ly S = ablocks B ly S.

Definition afn_pre_link_A : Prop :=
forall STK ly S Hp (W : world tfibsegs) regs mem md ch,
ARcf tfibsegs B ly S Hp W mem md ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
astk_ok STK ly (spZ regs) ->
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) ->
achain ly (aview tfibsegs (w_H W) mem) (spZ regs) (s0Z regs) ch ->
qtight S ->
afn_pre_cf tfibsegs B STK ly S Hp W regs mem md ch.

Definition ajournal_link_A : Prop :=
forall STK sp0 ly S Hp (W : world tfibsegs) mem md ly' S' Hp' W' mem' md' k,
ajournal_cf tfibsegs B STK sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k ->
ARcf tfibsegs B ly' S' Hp' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\
frames S' = frames S /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ PCA.ledger_img a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
qtight S'.
End s.
