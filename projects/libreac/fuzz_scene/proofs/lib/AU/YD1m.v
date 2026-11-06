(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD1m.v (donor image sha256 1c29845fe605), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: LIBC is libreac/fuzz_scene's statement of record, scene_tfib_lib_contract_x
   (AU/P_LLVMFuzzerTestOneInput_ctx.v), at the sink head tfib_sink_head, tfibsegs and the closed sink's cells
   SINK_OWNED_tfa, in place of AU/YCfn.v's tfib_lib_contract_x. Its pre states no meta invariant and its post's journal
   footprint is []: tfib_lib_site_x keeps lib_site_x's statement and rebuilds FINV after the call from FINV before it
   and the journal (AU/YE01.v ameta_inv_kept, astdio_env_kept), and weakens the journal to [sink_token]
   (AU/YCbq.v ajournal_init, ajournal_sub). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YM02 YP0m YP09 YI00 YI16 YK04 YA0i YA0n
YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v YF0m YCeg YD1t YD20 YD1v YD2h YD2f YD1w.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YE01 YE2k YC5d YCfn YD1u. From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require P_LLVMFuzzerTestOneInput_ctx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* The closed sink's cells of the asan-ubsan image, as the glue passes them (AU/G_Top.v:136 g_SINK_OWNED; a Theorem Labs lane's
   AU/P_LLVMFuzzerTestOneInput.v:154 SCENE_SINK_OWNED): __libc.threaded, ofl_lock and ofl_head (AU/YE2k.v:25-27). *)
Definition SINK_OWNED_tfa : list (Z * Z) := [(0x5f6d29, 1); (0x5f7188, 4); (0x5f7190, 8)].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBC : @P_LLVMFuzzerTestOneInput_ctx.scene_tfib_lib_contract_x fx rc YE2k.tfib_sink_head LS tfibsegs SINK_OWNED_tfa
  YCfn.A_LLVMF YCfn.RA_LLVMF YCfn.EV_LIB YCfn.LIVE_LIB YCfn.LLVMF_STK YCfn.A_EMPTY B MT XM_LIB XN_LIB RLO RHI.
Lemma layout_of_AR' : forall ly S W mem md, AR tfibsegs B ly S W mem md -> layout_ok ly.
Proof. intros ly S W mem md H. exact (am_layout _ _ _ _ (proj1 H)). Qed.
Theorem tfib_lib_site_x : lib_site_x B.
Proof.
intros ly S W regs mem md p n pl K HPRE R10 R11 Hpn Hlen Hpl Hfr Hev Hlive Hro HFI Hfree Hnames Hsorted HAI CONT.
pose proof HPRE as (HAR & Hret & Hra & Hgp & Htp & Hal & [Wlo Whi] & [Tlo Thi] & Elo & Ehi & Hpres & Hs0 & Hqt).
pose proof (layout_of_AR' _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
destruct HFI as ((M & HAM) & Henv & Hhead).
assert (HAFN : afn_pre tfibsegs B YCfn.LLVMF_STK ly S W regs mem md []).
{ split; [exact HAR|]. split; [exact Hret|]. split; [rewrite Hra; cbv; discriminate|]. split; [exact Hgp|]. split; [exact Htp|].
split.
- unfold astk_ok. rewrite Ehi. unfold ly_bot, kHighMemEnd, LLVMF_STK, ASTACK, kStackSpan in *. repeat split; lia.
- split; [exact Hpres|]. split; [| exact Hqt]. apply achain_low. exact Hs0. }
apply (LIBC ly S W regs mem md p n pl K HAI).
-
split; [exact HAFN|].
split; [exact Hra|]. split; [exact R10|]. split; [exact R11|]. split; [exact Hpn|].
split; [exact Hlen|]. split; [exact Hpl|]. split; [exact Hfr|]. split; [exact Hev|]. split; [exact Hlive|].
split.
{ intros a Ha Hno Hne. apply Hro; [| exact Hno | exact Hne]. destruct Ha as [Ha | Ha]; [left; exact Ha | exact (RO_IN a Ha)]. }
split.
{ (* the closed sink: threaded and ofl_lock from astdio_env, ofl_head from FINV, the path from Hnames *)
destruct Henv as (Hth & _ & Hlk & _). split; [| exact Hnames]. unfold SINK_OWNED_tfa.
apply Forall_cons; [exact Hth|]. apply Forall_cons; [exact Hlk|]. apply Forall_cons; [exact Hhead | apply Forall_nil]. }
split; [exact Hfree|]. split; [exact Hsorted | apply MT_FREE].
-
intros l W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Hc' & HJ0 & Hk & HP & Ha0 & HPERM & Hfdl & Hmfs & Hret' & Hout & Hsorted' & (Hzero & Hnames') & _ & Hplk).
apply (CONT l W' c' Hwle HAI'). exists ly', S', regs', mem', md', k.
split; [exact Hc'|].
split.
{ (* the contract's journal has footprint []; lib_site_x states [sink_token], which [] implies *)
pose proof (ajournal_init tfibsegs B YCfn.LLVMF_STK [YI16.sink_token] ly S W regs mem md [] HAFN) as HJi.
exact (ajournal_sub tfibsegs B ARL tfib_segs_low YCfn.LLVMF_STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly S W mem md 0
  YCfn.LLVMF_STK (spZ regs) [] [] ly' S' W' mem' md' k HJi HJ0 ltac:(lia) ltac:(lia) ltac:(intros a (rg & [] & _))). }
split; [exact Hk|]. split; [exact HP|]. split; [exact Ha0|]. split; [exact HPERM|].
split; [exact Hfdl|]. split; [exact Hmfs|]. split; [exact Hret'|]. split; [exact Hout|]. split; [exact Hsorted'|]. split; [exact Hnames'|].
split; [| exact Hplk]. split; [| split].
+ (* FINV after the call: the meta invariant and the stdio cells are kept by the journal, ofl_head is the third cell *)
exists M. exact (ameta_inv_kept tfibsegs B tfib_K (tfib_AIL B HB) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M HJ0 HAM).
+ exact (astdio_env_kept tfibsegs B tfib_K (tfib_AIL B HB) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 Henv).
+ exact (proj1 (Forall_forall _ _) Hzero (0x5f7190, 8) ltac:(unfold SINK_OWNED_tfa; cbn [In]; right; right; left; reflexivity)).
Qed.
End c.
End b.
