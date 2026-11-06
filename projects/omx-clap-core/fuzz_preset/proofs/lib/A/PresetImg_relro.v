(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_relro.v (commit eb934de95d13, blob 7e6e2b593f6d) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 3 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YK1b YK07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YO0f YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB13.
Open Scope Z_scope.

Definition C_SILENT_A : Z := 0xa2bd8.

Lemma silent_in_relro_A : 0xa19f0 <= C_SILENT_A /\ C_SILENT_A + 8 <= 0xa3000.
Proof. unfold C_SILENT_A. lia. Qed.

Lemma silent_rom_A : forall k, (k < 8)%nat ->
  seg_rom tfibsegs (Z_to_bv 64 (C_SILENT_A + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte 1 8 k)).
Proof.
intros k Hk. unfold C_SILENT_A.
rewrite tfib_rom2 by lia.
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma silent_val_A : forall mem : word -> option byte,
  (forall k, (k < 8)%nat -> mem (Z_to_bv 64 (C_SILENT_A + Z.of_nat k)) = None) ->
  val_mem tfibsegs mem C_SILENT_A 8 1.
Proof.
intros mem Hn k Hk. unfold mbyte. rewrite (Hn k Hk). apply silent_rom_A. exact Hk.
Qed.

Lemma silent_img_A : val_mem tfibsegs (fun _ => None) C_SILENT_A 8 1.
Proof. apply silent_val_A. intros k _. reflexivity. Qed.

Print Assumptions silent_rom_A.
Print Assumptions silent_val_A.
Print Assumptions silent_img_A.
Print Assumptions silent_in_relro_A.
