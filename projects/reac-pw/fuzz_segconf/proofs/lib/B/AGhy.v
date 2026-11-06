(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGhy.v (cold/c-frame-alloc-dgraw-frozen ced28ed2383, file sha256 378d6b206c74) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 41 image addresses moved by code-verified function pairs (43 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AGhy.v (donor image sha256 64b53ff86172), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AGhy.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFhy YFi1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition A_Allocate : Z := 0x331a4.
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
lit1 0xad498 1; lit4 0xad4bc 30; lit8 0xa3200 0x13e2e8; lit8 0x13e308 0x1e00010000;
lit1 0x12ea22 0; lit1 0xac020 1; lit4 0xac024 0; lit1 0xac01c 1;
iatom8 0x20 aSB; ilits8 0xe20 [0x10000000000; 0x108000010];
lit8 0x103b0 0x218a392cd3d5dbf; lits8 0x10428 CTZ_TABLE; lits8 0x10528 CTZ_TABLE; lit8 0x10328 0xcc6e96b9cc6e96b9;
lit8 0xa3208 0xa9fb8; lit8 0xa3210 0xac7b8; lit8 0xa3218 0xad4a8; lit8 0xa3220 0xad4b0; lit8 0xa3228 0xad4a0;
lit8 0xa3230 0xa50a8; lit8 0xa31f0 0x13c260; lit8 0x13c260 4096; lit8 0x13e360 0xffffffffffffffff;
atom8 0xac7b8 aSHB; lit8 0xad4a0 0x7fffffffffff; lit8 0xad4a8 0; lit8 0xad4b0 0; lit8 0xa50a8 0x9afd4;
lits8 0xa9fe0 [0x100000000000; 0xbe00000000]; lits8 0xaa000 [0x1000100000000; 0x101010101000001];
lit8 0xa3e68 0x10; lit4 0x5df808 0  ; lit8 0x13e280 0;
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
Definition FG_AG : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4);
(10%nat, mkAF 49 64512 0);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)         ;
(aSB, mkAF kHighMemBeg CEIL_MAX 16)         ;
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aJ0, mkAF 0 (2 ^ 64 - 1) 0);
(aR8, mkAF 56 64512 3);
(aCL, mkAF 1 31 0);
(aP, mkAF 4096 CEIL_MAX 4)                  ;
(aCNT, mkAF 1 16 0);
(aV, mkAF 0 (2 ^ 28 - 1) 0);
(aCSZ, mkAF 0 (2 ^ 64 - 1) 0);
(aPV, mkAF 4096 CEIL_MAX 2)                 ;
(aK, mkAF kHighMemBeg CEIL_MAX 5)            ;
(aJB, mkAF 0 255 0);
(aSHB, mkAF 0x7fff8000 0x7fff8000 12);
(aSK, mkAF 0x2008fff7000 0x10007fff7fff 2);
(aJ1, mkAF 0 (2 ^ 64 - 1) 0); (aJ2, mkAF 0 (2 ^ 64 - 1) 0); (aJ3, mkAF 0 (2 ^ 64 - 1) 0);
(aSSLOT, mkAF 4096 CEIL_MAX 3)              ;
(aJ4, mkAF 0 (2 ^ 64 - 1) 0);
(aPB, mkAF 0x2008fff7000 0x10007fff7fff 0);
(aN8D, mkAF 48 64512 3);
(aCNT8, mkAF 6 8064 0);
(aKL, mkAF 1 6 0);
(aRZ, mkAF 32 1024 5);
(aH, mkAF kHighMemBeg CEIL_MAX 4);
(aU, mkAF kHighMemBeg CEIL_MAX 5);
(aSU, mkAF 0x2008fff7000 0x10007fff7fff 2);
(aFIL, mkAF 49 4096 0);
(aND, mkAF 88 65536 3) ] [] [].
Definition FK_AG : facts := mkFacts
[ (2%nat, mkAF (kHighMemBeg + ASTACK) kHighMemEnd 4);
(10%nat, mkAF 0 48 0);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)         ;
(aSB, mkAF kHighMemBeg CEIL_MAX 16)         ;
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aJ0, mkAF 0 (2 ^ 64 - 1) 0);
(aR8, mkAF 8 48 3);
(aCL, mkAF 1 2 0);
(aP, mkAF 4096 CEIL_MAX 4)                  ;
(aCNT, mkAF 1 16 0);
(aV, mkAF 0 (2 ^ 28 - 1) 0);
(aCSZ, mkAF 0 (2 ^ 64 - 1) 0);
(aPV, mkAF 4096 CEIL_MAX 2)                 ;
(aK, mkAF kHighMemBeg CEIL_MAX 5)            ;
(aJB, mkAF 0 255 0);
(aSHB, mkAF 0x7fff8000 0x7fff8000 12);
(aSK, mkAF 0x2008fff7000 0x10007fff7fff 2);
(aJ1, mkAF 0 (2 ^ 64 - 1) 0); (aJ2, mkAF 0 (2 ^ 64 - 1) 0); (aJ3, mkAF 0 (2 ^ 64 - 1) 0);
(aSSLOT, mkAF 4096 CEIL_MAX 3)              ;
(aJ4, mkAF 0 (2 ^ 64 - 1) 0);
(aPB, mkAF 0x2008fff7000 0x10007fff7fff 0);
(aN8D, mkAF 0 48 3);
(aCNT8, mkAF 0 6 0);
(aNP, mkAF 1 48 0);
(aND, mkAF 24 64 3) ] [] [].
(* The facts: YFhy.FG / YFi1.FK with the entry sp's bound at AFSTACK, and the frame atoms. *)
Definition frame_facts : list (nat * afact) :=
[ (2%nat, mkAF (kHighMemBeg + AFSTACK) kHighMemEnd 4);
(aINST, mkAF TFIB_IMG_LO TFIB_IMG_END 3);
(aSO, mkAF kHighMemBeg kHighMemEnd 3);
(aBP, mkAF kHighMemBeg kHighMemEnd 3);
(15%nat, mkAF 0 1 0) ].
Definition FGG : facts := mkFacts (frame_facts ++ tl (f_atoms FG_AG)) (f_conds FG_AG) (f_alias FG_AG).
Definition FKG : facts := mkFacts (frame_facts ++ tl (f_atoms FK_AG)) (f_conds FK_AG) (f_alias FK_AG).
Definition REG0G : smem := R_soG :: R_scrG :: R_slotG :: TAIL0G.
Definition REG0KG : smem := R_soG :: R_scrG :: R_slotG :: TAIL0KG.
Definition SSG : sstate := mkSS A_Allocate REGS_G REG0G None FGG.
Definition SSGK : sstate := mkSS A_Allocate REGS_G REG0KG None FKG.
