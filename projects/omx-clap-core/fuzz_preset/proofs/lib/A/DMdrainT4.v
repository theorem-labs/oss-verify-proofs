(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT4.v (commit 67deba317dfb, blob 18c6823e7ca3) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK0h YK14 YK1b YK1a YK15 YK18 YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP03 YP02 YP0k YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainK DMdrainT3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable ly : alayout.
Variable iw : chunk -> Z.
Variable H : word -> bool.

Lemma lcn_app_split : forall m l1 l2 z, lcn ly iw m (l1 ++ l2) z -> lcn ly iw m l1 (fa ly l2 z) /\ lcn ly iw m l2 z.
Proof.
intros m l1. induction l1 as [|b t IH]; intros l2 z HL; [split; [exact I | exact HL]|].
cbn [app lcn] in HL. destruct HL as [Hb Ht]. destruct (IH l2 z Ht) as [H1 H2].
split; [|exact H2]. cbn [lcn]. split; [|exact H1].
rewrite (fa_app_k ly t l2 z) in Hb. exact Hb.
Qed.

Lemma bcell_relink : forall (Win : Z -> Prop) (mem mem' : word -> option byte) b nx z',
(forall x : word, ~ Win (bv_unsigned x) -> mem' x = mem x) ->
0 <= addrb ly b -> addrb ly b + 24 + 8 * zl (b_items b) <= 2 ^ 64 ->
(forall a, addrb ly b + 8 <= a < addrb ly b + 24 + 8 * zl (b_items b) -> ~ Win a) ->
val_mem tfibsegs (mrestrict H mem') (addrb ly b) 8 z' ->
bcell ly iw (mrestrict H mem) b nx -> bcell ly iw (mrestrict H mem') b z'.
Proof.
intros Win mem mem' b nx z' HM A1 A2 HA HZ (V0 & V8 & V16 & VS).
assert (HZl : 0 <= zl (b_items b)) by (unfold zl; lia).
unfold bcell. splits.
- exact HZ.
- apply (val_mem_frame H mem mem' _ 8 _); [|exact V8].
  intros k Hk. apply HM. rewrite unsigned_lit_small by lia. apply HA. lia.
- apply (val_mem_frame H mem mem' _ 8 _); [|exact V16].
  intros k Hk. apply HM. rewrite unsigned_lit_small by lia. apply HA. lia.
- intros j k Hj. pose proof (proj1 (nth_error_Some (b_items b) j) ltac:(rewrite Hj; discriminate)) as LT.
  apply (val_mem_frame H mem mem' _ 8 _); [|exact (VS j k Hj)].
  intros i Hi. apply HM. rewrite unsigned_lit_small by (unfold zl in *; lia).
  apply HA. unfold zl in *. lia.
Qed.

Lemma lcn_snoc : forall m init lastb z',
lcn ly iw m init (addrb ly lastb) -> bcell ly iw m lastb z' -> lcn ly iw m (init ++ [lastb]) z'.
Proof.
intros m init lastb z' HI HB. apply (lcn_app_link ly iw m init [lastb] z').
- cbn [fa addrb]. exact HI.
- cbn [lcn fa]. split; [exact HB | exact I].
Qed.
End e.
End c.
