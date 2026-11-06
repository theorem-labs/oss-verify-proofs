(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainU2.v (commit ce1a656b52b7, file sha256 f2b3a3c6d447) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 2 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainU2.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 958083de6f65) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainU2.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (2 numerals; per-numeral report). *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the NO-MERGE arm's first half - from Quarantine::Drain's entry at
   0x342b8 to Recycle's call of DoRecycle at 0x345c8, on the arm where the quarantine is over kQuarantineMax but
   Recycle's merge test fails, so the drain goes straight to the dequeue loop (YFgj.at_L0, YFgj.v:309-327, the
   third outcome of DMsegD.postDm).
   Chain: DMdrainG4.entry_free_hyps -> DMdrainT1.drain_entry_run -> at_L0 -> DMdrainN.deq_pre_nomerge (the loop's
   premise, with the joined list from DMdrainTA.GT_lcn) -> DMdeq.tfib_deq_ok (the released dequeue loop) ->
   DMdeq.ATDR at DoRecycle's call.
   The arm's theorem itself, nomerge_to_call, is in DMdrainV0.v (DMdrainU4 imports these helpers, so the theorem,
   which uses DMdrainU4, lives one file later).
   - [win_dec]: YFgj.WIN is decidable, which is how the loop frame's presence is split between the walk's own
     presence clause (inside the window) and the frame (outside it); no apartness of the layout is needed.
   - [lsz_len] / [lf_fa] / [tl_la] / [lb_sum]: the four head values of the transferred quarantine, in the
     dequeue loop's list vocabulary.
   rule 24: no function proved (kind: composition of segments already walked - DMdrainT1's entry walk and
   DMdeq.tfib_deq_ok; the lane's reuse search is the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches
   Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMdrainK DMdrainQ DMdrainG1 DMdrainG3 DMdrainG4 DMdrainT1 DMdrainTA DMdrainN.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMsegD DMdeq.
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

(* The drain's window is decidable: each disjunct is an address range, and the one side condition is a list
   emptiness test. *)
Lemma win_dec : forall ly (regs0 : bvmap 5 word) gq a,
{YFgj.WIN ly regs0 gq a} + {~ YFgj.WIN ly regs0 gq a}.
Proof.
intros ly regs0 gq a. unfold YFgj.WIN, YFgj.WINF, YFgj.WINA.
destruct (zrange_dec (bv_unsigned (getr regs0 2) - 80) a (bv_unsigned (getr regs0 2))) as [A1|A1];
[left; tauto|].
destruct (zrange_dec (A_QUAR + 152) a (A_QUAR + 156)) as [A2|A2]; [left; tauto|].
destruct (zrange_dec (A_QUAR + 160) a (A_QUAR + 192)) as [A3|A3]; [left; tauto|].
destruct (zrange_dec (ly_T ly + t_qc) a (ly_T ly + t_qc + 32)) as [A4|A4]; [left; tauto|].
destruct (zrange_dec (YFgj.GLv ly gq) a (YFgj.GLv ly gq + 8)) as [A5|A5].
- destruct (qc_list gq) as [|b t] eqn:EG.
  + right. intros [H|[H|[H _]]]; [tauto | tauto | exact (H eq_refl)].
  + left. right. right. split; [discriminate | exact A5].
- right. intros [H|[H|[_ H]]]; tauto.
Qed.

(* The four head values of the transferred quarantine, in the dequeue loop's vocabulary. *)
Lemma lsz_len : forall gq tq, YFgj.LSZv gq tq = Z.of_nat (length (qc_list gq ++ qc_list tq)).
Proof.
intros gq tq. unfold YFgj.LSZv, YFgj.GSZv, YFgj.TSZv. rewrite length_app, Nat2Z.inj_add. reflexivity.
Qed.

Lemma lf_fa : forall ly gq tq, YFgj.LFv ly gq tq = fa ly (qc_list gq ++ qc_list tq) 0.
Proof.
intros ly gq tq. unfold YFgj.LFv, YFgj.GFv, YFgj.TFv, fa, addrb.
destruct (qc_list gq) as [|b t]; [destruct (qc_list tq) as [|b2 t2]; reflexivity | reflexivity].
Qed.

Lemma tl_la : forall ly gq tq, qc_list tq <> [] -> YFgj.TLv ly tq = la ly (qc_list gq ++ qc_list tq).
Proof.
intros ly gq tq HT. unfold YFgj.TLv, la, addrb. rewrite rev_app_distr.
destruct (rev (qc_list tq)) as [|b r] eqn:ER; [|reflexivity].
exfalso. apply HT. rewrite <- (rev_involutive (qc_list tq)), ER. reflexivity.
Qed.

Lemma lb_sum : forall gq tq, qc_bytes gq = sum_bytes (qc_list gq) -> qc_bytes tq = sum_bytes (qc_list tq) ->
YFgj.LBv gq tq = sum_bytes (qc_list gq ++ qc_list tq).
Proof.
intros gq tq HG HT. unfold YFgj.LBv, YFgj.GBv, YFgj.TBv.
rewrite DMdrainQ.sum_bytes_app_q, HG, HT. reflexivity.
Qed.

End f.
