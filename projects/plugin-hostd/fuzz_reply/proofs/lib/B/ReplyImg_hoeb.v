(* Theorem Labs, 2026-10-30 (CfInstMiss, row img-hoeb-B of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for the cf layer at
   plugin-hostd/fuzz_reply; the B twin of lib/A/ReplyImg_hoeb.v, same stem).
   rule 24: no function proved (kind: image row; two symbol-table facts at reply's image B).

   HOEB is the cf layer's unit premise `Hypothesis HOEB : ~ (cf_errbuf_obj <= as_oom_byte B < cf_errbuf_obj + 56)`
   (YGcfInstMiss.v Section b, a working branch aa87040fb59), taken under `Hypothesis TS : im_syms B`. hoeb_B states
   that text at reply's image class instance AImg_reply (B/AGif2reply.v) and CfImg_B (B/CfImgB.v:34, cf_errbuf_obj :=
   0xa5ea8, __asan::error_message_buffer), with TS as its premise; a consumer closes HOEB with `exact (hoeb_B B TS)`. The
   discharge is cgif's (YGcfInstMisscgif.HOEB_cgif): reply B's TfibSyms field ts_oom (B/YF0m.v:874) with TFIB_OOM =
   0x1288a0 (B/YF0m.v:19). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply CfImgB.
Open Scope Z_scope.

(* HOEB at image B: the out-of-memory byte (0x1288a0) is not in the errbuf object [0xa5ea8, 0xa5ee0). *)
Lemma hoeb_B : forall B, @im_syms AImg_reply B ->
  ~ (@cf_errbuf_obj CfImg_B <= as_oom_byte B < @cf_errbuf_obj CfImg_B + 56).
Proof. intros B TS. rewrite (ts_oom B TS). cbn [cf_errbuf_obj CfImg_B]. unfold TFIB_OOM. lia. Qed.
