(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU2.v (commit 67deba317dfb, blob bf725c438f4b) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMdrainK DMdrainQ DMdrainG1 DMdrainG3 DMdrainG4 DMdrainT1 DMdrainTA DMdrainN.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMsegDA DMdeq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma zrange_dec : forall lo a hi, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof.
intros lo a hi. destruct (Z_le_gt_dec lo a) as [H1|H1].
- destruct (Z_lt_ge_dec a hi) as [H2|H2]; [left; split; assumption | right; intros [? ?]; lia].
- right; intros [? ?]; lia.
Qed.

Lemma win_dec : forall ly (regs0 : bvmap 5 word) gq a,
{AFgj.WIN ly regs0 gq a} + {~ AFgj.WIN ly regs0 gq a}.
Proof.
intros ly regs0 gq a. unfold AFgj.WIN, AFgj.WINF, AFgj.WINA.
destruct (zrange_dec (bv_unsigned (getr regs0 2) - 80) a (bv_unsigned (getr regs0 2))) as [A1|A1];
[left; tauto|].
destruct (zrange_dec (A_QUAR + 152) a (A_QUAR + 156)) as [A2|A2]; [left; tauto|].
destruct (zrange_dec (A_QUAR + 160) a (A_QUAR + 192)) as [A3|A3]; [left; tauto|].
destruct (zrange_dec (ly_T ly + t_qc) a (ly_T ly + t_qc + 32)) as [A4|A4]; [left; tauto|].
destruct (zrange_dec (AFgj.GLv ly gq) a (AFgj.GLv ly gq + 8)) as [A5|A5].
- destruct (qc_list gq) as [|b t] eqn:EG.
  + right. intros [H|[H|[H _]]]; [tauto | tauto | exact (H eq_refl)].
  + left. right. right. split; [discriminate | exact A5].
- right. intros [H|[H|[_ H]]]; tauto.
Qed.

Lemma lsz_len : forall gq tq, AFgj.LSZv gq tq = Z.of_nat (length (qc_list gq ++ qc_list tq)).
Proof.
intros gq tq. unfold AFgj.LSZv, AFgj.GSZv, AFgj.TSZv. rewrite length_app, Nat2Z.inj_add. reflexivity.
Qed.

Lemma lf_fa : forall ly gq tq, AFgj.LFv ly gq tq = fa ly (qc_list gq ++ qc_list tq) 0.
Proof.
intros ly gq tq. unfold AFgj.LFv, AFgj.GFv, AFgj.TFv, fa, addrb.
destruct (qc_list gq) as [|b t]; [destruct (qc_list tq) as [|b2 t2]; reflexivity | reflexivity].
Qed.

Lemma tl_la : forall ly gq tq, qc_list tq <> [] -> AFgj.TLv ly tq = la ly (qc_list gq ++ qc_list tq).
Proof.
intros ly gq tq HT. unfold AFgj.TLv, la, addrb. rewrite rev_app_distr.
destruct (rev (qc_list tq)) as [|b r] eqn:ER; [|reflexivity].
exfalso. apply HT. rewrite <- (rev_involutive (qc_list tq)), ER. reflexivity.
Qed.

Lemma lb_sum : forall gq tq, qc_bytes gq = sum_bytes (qc_list gq) -> qc_bytes tq = sum_bytes (qc_list tq) ->
AFgj.LBv gq tq = sum_bytes (qc_list gq ++ qc_list tq).
Proof.
intros gq tq HG HT. unfold AFgj.LBv, AFgj.GBv, AFgj.TBv.
rewrite DMdrainQ.sum_bytes_app_q, HG, HT. reflexivity.
Qed.

End f.
