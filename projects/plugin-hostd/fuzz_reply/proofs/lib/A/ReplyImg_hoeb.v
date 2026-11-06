(* Theorem Labs, 2026-10-30 (CfInstMiss, row img-hoeb-A of a Theorem Labs lane's REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), for the cf layer at
   plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image row; two symbol-table facts at reply's image A, fuzz_reply.asan, pin
   42c58610e125).

   HOEB is the cf layer's unit premise `Hypothesis HOEB : ~ (cf_errbuf_obj <= as_oom_byte B < cf_errbuf_obj + 56)`
   (YGcfInstMiss.v Section b, a working branch aa87040fb59: the out-of-memory tail writes the OOM byte, and ARmcf's
   errbuf cells survive it because the byte is not in the errbuf object), taken under `Hypothesis TS : im_syms B`. hoeb_A
   states that text at reply's image class instance AImg_reply (A/AGif2reply.v, im_syms := TfibSyms) and CfImg_A
   (A/CfImgA.v:34, cf_errbuf_obj := 0xa5928, __asan::error_message_buffer), with TS as its premise; a consumer closes HOEB
   with `exact (hoeb_A B TS)`. The discharge is cgif's (YGcfInstMisscgif.HOEB_cgif: cf_errbuf_obj_cgif + ts_oom, one lia):
   reply A's TfibSyms field ts_oom (A/AF0m.v:875) with TFIB_OOM = 0x128320 (A/AF0m.v:20). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply CfImgA.
Open Scope Z_scope.

(* HOEB at image A: the out-of-memory byte (0x128320) is not in the errbuf object [0xa5928, 0xa5960). *)
Lemma hoeb_A : forall B, @im_syms AImg_reply B ->
  ~ (@cf_errbuf_obj CfImg_A <= as_oom_byte B < @cf_errbuf_obj CfImg_A + 56).
Proof. intros B TS. rewrite (ts_oom B TS). cbn [cf_errbuf_obj CfImg_A]. unfold TFIB_OOM. lia. Qed.
