(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: moved from proofs/cgif/cgif_file_fuzzer/lib/AGhy.v (file sha256 378d6b206c74: its text at 63b73430c18 and at a working branch 84ee52cd012) onto omx-clap-core/fuzz_preset's asan image A' (#102 pin fuzz_preset.asan 1be0f53d96cb; symbols from its unstripped twin bff8519bbe3e); module paths changed. No image numeral is relocated here: Allocate's entry and the malloc call site's alignment and alloc_type are FCimg.v's generated names (gen_fcimg 434a011a6139 at A', as re-emitted by the host-path sweep bedf6e890875; file sha256 70888fce61f2); can_fill stays the atom x15 in {0, 1}, as in the source; the start-up cells (TAIL0G) are REGENERATED from this unit's own seed AFhy.REG0 (A', file sha256 023bef010412) by the transformation a Theorem Labs lane applied to cgif's YFhy.REG0 (drop the stack region, base the two allocator-instance regions at aINST): the literal is generated from AFhy.v's text by the internal file gen_tail0g.py, and TAIL0G_derived checks it equal to that derivation. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AGhy.v, with its module paths and module names changed; 19 of its 42 lines of code are new or changed and 63 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGbase.v (a working branch 84ee52cd012, file sha256 4c38edb43c0d) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 3 image addresses moved by code-verified function pairs (3 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at d1f93c50c87) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc 0474699fc83547e0 (a working branch 83209f9d9cd8), --assume-source, --resolve the internal file resolve-102.txt (0 lines name this file); 3 numerals changed. *)
(* The definitions shared by the seeds of the frame-generic Deallocate walk (DGgi, DGgm, DGgn): Deallocate's entry
   pc and stack need, the frame atoms of the virtual register file regs0 (aINST = this, aBP = the trace buffer,
   aSO = the BufferedStackTrace object; atom 10 = the pointer, atom 2 = the entry sp, atom 1 = the return pc), the
   registers at the entry and the frame regions. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DeallocG.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition A_Deallocate : Z := 0x322a4.
(* Deallocate's stack need below its entry sp (DeallocG.DFSTACK_G). *)
Definition DFSTACK : Z := 8192.
Lemma DFSTACK_G_eq : DFSTACK = DeallocG.DFSTACK_G. Proof. reflexivity. Qed.
Definition aINST : nat := 11.  Definition aBP : nat := 12.  Definition aSO : nat := 13.
(* The instance-relative regions (the instance object spans [inst, inst + 0xe60)). *)
Definition ilit8 (o v : Z) : YP09.region := YP09.mkRegion (Some aINST) o (o + 8) 0 0 [YP09.mkChunk o (CVal 8 (SLit v))].
Definition R_soG : YP09.region :=
YP09.mkRegion (Some aSO) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff aBP 0)); YP09.mkChunk 8 (CVal 8 (SOff aLEN 0))].
Definition R_scrG : YP09.region := YP09.mkRegion (Some 2%nat) (- DFSTACK) 0 (- DFSTACK) 0 [].
Definition R_slotG : YP09.region := YP09.mkRegion (Some 2%nat) 0 0 0 0 [].
(* The registers at Deallocate's entry: a0 = this, a1 = p (atom 10), a2 = a3 = 0, a4 = the stack object,
   a5 = FROM_MALLOC; REGS_GN is the same with a1 = 0 (the NULL arm). *)
Definition REGS_G : list sv :=
[SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SLit TFIB_TP; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
SOff aINST 0; SOff 10 0; SLit 0; SLit 0; SOff aSO 0; SLit 1; SOff 16 0; SOff 17 0;
SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition REGS_GN : list sv :=
[SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SLit TFIB_TP; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
SOff aINST 0; SLit 0; SLit 0; SLit 0; SOff aSO 0; SLit 1; SOff 16 0; SOff 17 0;
SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* The entry sp's bound at DFSTACK, and the frame atoms (the instance range is AGif0cgif.inst_ok's). *)
Definition frame_facts : list (nat * afact) :=
[ (2%nat, mkAF (kHighMemBeg + DFSTACK) kHighMemEnd 4);
(aINST, mkAF 0xa3e98 (0xa86e0 - 0xe60) 3);
(aSO, mkAF kHighMemBeg kHighMemEnd 3);
(aBP, mkAF kHighMemBeg kHighMemEnd 3) ].
