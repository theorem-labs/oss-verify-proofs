(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainK.v (commit 67deba317dfb, blob af17606a9001) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFeu AFey AFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable B : asyms.
Variable ly : alayout.

Definition iwB (k : chunk) : Z := aeval B ly (sptr_exp (ck_hdr k)).

Lemma fa_firstaddr_hf : forall t, fa ly t 0 = AFhf.firstaddr ly t.
Proof. intros [|b t]; reflexivity. Qed.

Lemma lcn_of_cells : forall (H : word -> bool) (mem : word -> option byte) (l : list batch),
Forall (cell_holds B ly (aview tfibsegs H mem)) (batch_cells l) ->
lcn ly iwB (mrestrict H mem) l 0.
Proof.
intros H mem l. induction l as [|b t IH]; intros HC; [exact I|].
cbn [lcn]. split.
- pose proof (AFhf.batch_head_cells B ly H mem b t HC) as (V0 & V8 & V16 & VS). cbv zeta in V0, V8, V16, VS.
  unfold bcell, addrb, zl. rewrite fa_firstaddr_hf. split; [exact V0|]. split; [exact V8|]. split; [exact V16|].
  intros j k Hj. exact (VS j k Hj).
- apply IH. exact (AFhf.batch_cells_tail B ly _ b t HC).
Qed.

Lemma fa_app_k : forall l1 l2 z, fa ly (l1 ++ l2) z = fa ly l1 (fa ly l2 z).
Proof. intros [|b l1] l2 z; reflexivity. Qed.

Lemma lcn_app_link : forall iw m l1 l2 z, lcn ly iw m l1 (fa ly l2 z) -> lcn ly iw m l2 z -> lcn ly iw m (l1 ++ l2) z.
Proof.
intros iw m l1. induction l1 as [|b t IH]; intros l2 z H1 H2; [exact H2|].
cbn [app lcn] in *. destruct H1 as [Hb Ht]. split.
- rewrite fa_app_k. exact Hb.
- exact (IH l2 z Ht H2).
Qed.
End d.
End c.
