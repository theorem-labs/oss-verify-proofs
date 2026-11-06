(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/YGcfInstF1WA.v, with its module paths changed; 7 of its 29 lines of code are new or changed and 173 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (lane F1 of the generic cf instance layer; integrator ReallocPrimary): reply's twin, at
   image A (fuzz_reply.asan), of the two depot-contract rows of CfF1's cgif witness
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstF1Wcgif.v (depot_spec_a_cgif / depot_spec_d_cgif): the released
   StackDepotPut contract A/AFem.tfib_depot_ok (over A/AFl0.tfib_depot_spec, the P'' admits form) stated as the
   generic CLdepot.depot_spec_x at Allocate's and Deallocate's call sites.  Its one premise is the image's dhash row
   (forall t, as_dhash B t = tfib_dhash t), the witness premise of tfib_depot_ok, as at cgif.
   rule 24: no function proved (kind: instance discharge of the depot contract at reply's image A). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseAG ImgBaseDG DGif0reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CLdepot AFem.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* At Allocate's StackDepotPut call (cgif: YGcfInstF1Wcgif.depot_spec_a_cgif). *)
Theorem depot_spec_a_reply : (forall t, as_dhash B t = tfib_dhash t) ->
CLdepot.depot_spec_x im_segs ag_depot_put im_tp im_img_cover B.
Proof. intros HDH. exact (AFem.tfib_depot_ok B TS HDH). Qed.

(* At Deallocate's (cgif: YGcfInstF1Wcgif.depot_spec_d_cgif). *)
Theorem depot_spec_d_reply : (forall t, as_dhash B t = tfib_dhash t) ->
CLdepot.depot_spec_x im_segs dg_depot im_tp im_img_cover B.
Proof. intros HDH. exact (AFem.tfib_depot_ok B TS HDH). Qed.
End b.
End a.
