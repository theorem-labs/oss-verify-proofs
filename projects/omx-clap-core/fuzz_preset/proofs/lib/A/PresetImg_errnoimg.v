(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_errnoimg.v (commit eb934de95d13, blob 6aa4ad058eeb) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA AGImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ErrnoApartpreset.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem errno_img_cf_A :
  errno_in_img (IM := AImg_A) /\
  errno_unhidden (IM := AImg_A) /\
  errno_apart_dzone_ag (IM := AImg_A) (AG := AGImg_A) /\
  errno_apart_shadow_ag (IM := AImg_A) (AG := AGImg_A) /\
  errno_apart_inst_ag (IM := AImg_A) (AG := AGImg_A) /\
  errno_apart_dzone_d (IM := AImg_A) (DI := DImg_A) /\
  errno_apart_izone (IM := AImg_A) (DI := DImg_A) /\
  errno_apart_zone3_d (IM := AImg_A) (DI := DImg_A) /\
  errno_apart_inst_d (IM := AImg_A) (DI := DImg_A).
Proof.
split; [exact ErrnoApartpreset.errno_in_img_preset|].
split; [exact ErrnoApartpreset.errno_unhidden_preset|].
split; [exact ErrnoApartpreset.errno_apart_dzone_ag_preset|].
split; [exact ErrnoApartpreset.errno_apart_shadow_ag_preset|].
split; [exact ErrnoApartpreset.errno_apart_inst_ag_preset|].
split; [exact ErrnoApartpreset.errno_apart_dzone_d_preset|].
split; [exact ErrnoApartpreset.errno_apart_izone_preset|].
split; [exact ErrnoApartpreset.errno_apart_zone3_d_preset|].
exact ErrnoApartpreset.errno_apart_inst_d_preset.
Qed.

End a.
