(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGhy.v (a working branch 30a1993588f, c5 + memnorm; file sha256 378d6b206c74) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 40 image addresses moved by code-verified function pairs (40 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 1 hand maps (agreloc-resolve-R.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* The seeds of the frame-generic walk of Allocator::Allocate (the AG* files, generalized from YFhy-YFjg).

   The walk starts at Allocate's first instruction (A_Allocate) with the caller's frame abstract.  Over the
   virtual register file regs0 of the walk's environment (Ereg regs0 XW):
     atom 1 = the return pc, atom 2 = the entry sp, atom 10 = the size n, atom aINST = the allocator instance
     (this), atom aSO = the BufferedStackTrace object, atom aBP = its trace buffer, atoms 3, 8, 9, 18-27 = the
     caller's gp and callee-saved registers.
   REGS_G is the register file at the entry over those atoms (a0 = this, a1 = n, a2 = 8, a3 = the stack object,
   a4 = FROM_MALLOC, a5 = can_fill).  The regions are: the stack object (aSO), the scratch window of AFSTACK
   bytes below the entry sp, an empty slot (so that the region indices of YFhz's states are kept), and the
   regions of YFhy.REG0 / YFi1.REG0K with the allocator instance's fields based at aINST. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFhy AFi1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition A_Allocate : Z := 0x31bd8.
(* Allocate's stack need below its entry sp: its own frame (0x80) and its callees' (the depot 512, the refill
   1024 below a 176-byte frame, the memset), with room to spare.  Every caller has at least this below the
   sp at its call. *)
Definition AFSTACK : Z := 4096.
Definition aINST : nat := 11.  Definition aBP : nat := 12.  Definition aSO : nat := 13.
(* The instance-relative regions: the instance object spans [inst, inst + 0xe60) (the next symbol, asan's
   flags, is at TFIB_INST + 0xe60). *)
Definition ilit8 (o v : Z) : YP09.region := YP09.mkRegion (Some aINST) o (o + 8) 0 0 [YP09.mkChunk o (CVal 8 (SLit v))].
Definition iatom8 (o : Z) (k : nat) : YP09.region := YP09.mkRegion (Some aINST) o (o + 8) 0 0 [YP09.mkChunk o (CVal 8 (SOff k 0))].
Definition ilits8 (o : Z) (vs : list Z) : YP09.region :=
YP09.mkRegion (Some aINST) o (o + 8 * Z.of_nat (length vs)) 0 0
(map (fun iv => YP09.mkChunk (o + 8 * Z.of_nat (fst iv)) (CVal 8 (SLit (snd iv)))) (combine (seq 0 (length vs)) vs)).
Definition R_soG : YP09.region :=
YP09.mkRegion (Some aSO) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff aBP 0)); YP09.mkChunk 8 (CVal 8 (SOff aLEN 0))].
Definition R_scrG : YP09.region := YP09.mkRegion (Some 2%nat) (- AFSTACK) 0 (- AFSTACK) 0 [].
Definition R_slotG : YP09.region := YP09.mkRegion (Some 2%nat) 0 0 0 0 [].
Definition REGS_G : list sv :=
[SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SLit TFIB_TP; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
SOff aINST 0; SOff 10 0; SLit 8; SOff aSO 0; SLit 1; SOff 15 0; SOff 16 0; SOff 17 0;
SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* YFhy.REG0 without its stack region, the instance fields (TFIB_INST + 0x20, + 0xe20) based at aINST. *)
Definition TAIL0G : smem :=
[
lit1 0xa6d98 1; lit4 0xa6dbc 30; lit8 0x9d9c0 0x137be8; lit8 0x137c08 0x1e00010000;
lit1 0x128322 0; lit1 0xa5920 1; lit4 0xa5924 0; lit1 0xa591c 1;
iatom8 0x20 aSB; ilits8 0xe20 [0x10000000000; 0x108000010];
lit8 0x103b0 0x218a392cd3d5dbf; lits8 0x10420 CTZ_TABLE; lits8 0x10520 CTZ_TABLE; lit8 0x10328 0xcc6e96b9cc6e96b9;
lit8 0x9d9c8 0xa38b8; lit8 0x9d9d0 0xa60b8; lit8 0x9d9d8 0xa6da8; lit8 0x9d9e0 0xa6db0; lit8 0x9d9e8 0xa6da0;
lit8 0x9d9f0 0x9f870; lit8 0x9d9b0 0x135b60; lit8 0x135b60 4096; lit8 0x137c60 0xffffffffffffffff;
atom8 0xa60b8 aSHB; lit8 0xa6da0 0x7fffffffffff; lit8 0xa6da8 0; lit8 0xa6db0 0; lit8 0x9f870 0x96900;
lits8 0xa38e0 [0x100000000000; 0xbe00000000]; lits8 0xa3900 [0x1000100000000; 0x101010101000001];
lit8 0x9e628 0x10; lit4 0x5d9480 0  ; lit8 0x137b80 0;
lit8 (TFIB_TP - 88) TFIB_TSD; atom8 TFIB_TSD aC;
YP09.mkRegion (Some aC) 0 160 0 0 [YP09.mkChunk 8 (CVal 4 (SLit 0)); YP09.mkChunk 152 (CVal 8 (SOff aT 0))];
YP09.mkRegion (Some aT) 0 208 0 0 [YP09.mkChunk 0 (CVal 8 (SOff aC 0)); YP09.mkChunk 8 (CVal 8 (SOff aTOP 0));
YP09.mkChunk 16 (CVal 8 (SOff aTOP (- kStackSpan))); YP09.mkChunk 40 (CVal 1 (SLit 0))];
YP09.mkRegion (Some aT) 2768 2800 2768 2800 [YP09.mkChunk 2784 (CVal 8 (SOff aJ0 0))];
YP09.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1) [YP09.mkChunk t_unwinding (CVal 1 (SLit 0))];
YP09.mkRegion (Some aT) 2800 2824 2800 2824 [YP09.mkChunk 2800 (CVal 8 (SOff aJ1 0)); YP09.mkChunk 2808 (CVal 8 (SOff aJ2 0));
YP09.mkChunk 2816 (CVal 8 (SOff aJ3 0))];
YP09.mkRegion (Some aSSLOT) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff aJ4 0))];
YP09.mkRegion (Some aP) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff aCNT 0))];
YP09.mkRegion (Some aP) 4 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff aCSZ 0))];
YP09.mkRegion (Some aPV) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff aV 0))];
YP09.mkRegion (Some aK) 0 16 0 16 [];
YP09.mkRegion (Some aU) (- 16) 0 (- 16) 0 [YP09.mkChunk (- 15) (CVal 1 (SOff aJB 0))];
YP09.mkRegion (Some aSK) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 250))] ].
(* The same for YFi1.REG0K: its aK region holds the header byte and it has no aU region. *)
Definition TAIL0KG : smem :=
firstn 44 TAIL0G ++
[YP09.mkRegion (Some aK) 0 16 0 16 [YP09.mkChunk 1 (CVal 1 (SOff aJB 0))];
YP09.mkRegion (Some aSK) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 250))] ].
(* The facts: YFhy.FG / YFi1.FK with the entry sp's bound at AFSTACK, and the frame atoms. *)
Definition frame_facts : list (nat * afact) :=
[ (2%nat, mkAF (kHighMemBeg + AFSTACK) kHighMemEnd 4);
(aINST, mkAF TFIB_IMG_LO TFIB_IMG_END 3);
(aSO, mkAF kHighMemBeg kHighMemEnd 3);
(aBP, mkAF kHighMemBeg kHighMemEnd 3);
(15%nat, mkAF 0 1 0) ].
Definition FGG : facts := mkFacts (frame_facts ++ tl (f_atoms FG)) (f_conds FG) (f_alias FG).
Definition FKG : facts := mkFacts (frame_facts ++ tl (f_atoms FK)) (f_conds FK) (f_alias FK).
Definition REG0G : smem := R_soG :: R_scrG :: R_slotG :: TAIL0G.
Definition REG0KG : smem := R_soG :: R_scrG :: R_slotG :: TAIL0KG.
Definition SSG : sstate := mkSS A_Allocate REGS_G REG0G None FGG.
Definition SSGK : sstate := mkSS A_Allocate REGS_G REG0KG None FKG.
