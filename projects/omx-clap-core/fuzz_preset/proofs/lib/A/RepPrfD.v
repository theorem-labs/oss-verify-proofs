(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepPrfD.v (commit eb934de95d13, blob e0cb8b1cd1a8) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 7 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition reptbl_build : ctable :=
  build_table tfibsegs 0x68440 88%nat (build_table tfibsegs 0x6196c 14%nat (build_table tfibsegs 0x64c0c 7%nat
  (build_table tfibsegs 0x6753c 4%nat (build_table tfibsegs 0x60e40 40%nat (build_table tfibsegs 0x6df78 6%nat
  (build_table tfibsegs 0x66b08 26%nat tfibtbl_rtD)))))).
Definition reptbl : ctable := Eval vm_compute in reptbl_build.
Lemma reptbl_eq : reptbl = reptbl_build.
Proof. vm_cast_no_check (@eq_refl ctable reptbl). Qed.
Lemma reptbl_ok : table_ok tfibsegs reptbl.
Proof. rewrite reptbl_eq. unfold reptbl_build. do 7 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtD_ok. Qed.
