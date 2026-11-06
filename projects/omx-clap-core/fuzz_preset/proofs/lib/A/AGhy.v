(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: moved from proofs/cgif/cgif_file_fuzzer/lib/AGhy.v (file sha256 378d6b206c74: its text at 63b73430c18 and at a working branch 84ee52cd012) onto omx-clap-core/fuzz_preset's asan image A' (#102 pin fuzz_preset.asan 1be0f53d96cb; symbols from its unstripped twin bff8519bbe3e); module paths changed. No image numeral is relocated here: Allocate's entry and the malloc call site's alignment and alloc_type are FCimg.v's generated names (gen_fcimg 434a011a6139 at A', as re-emitted by the host-path sweep bedf6e890875; file sha256 70888fce61f2); can_fill stays the atom x15 in {0, 1}, as in the source; the start-up cells (TAIL0G) are REGENERATED from this unit's own seed AFhy.REG0 (A', file sha256 023bef010412) by the transformation a Theorem Labs lane applied to cgif's YFhy.REG0 (drop the stack region, base the two allocator-instance regions at aINST): the literal is generated from AFhy.v's text by the internal file gen_tail0g.py, and TAIL0G_derived checks it equal to that derivation. *)
(* The seeds of the frame-generic walk of Allocator::Allocate (the AG* files, generalized from the released AFhy-AFjy; this series renames 26 to AG* files (14 of AFhy-AFjg, 12 of AFji-AFjy) and deletes 30 of AFhy-AFjg, AFjg.v among them).

   The walk starts at Allocate's first instruction (A_Allocate) with the caller's frame abstract.  Over the
   virtual register file regs0 of the walk's environment (Ereg regs0 XW):
     atom 1 = the return pc, atom 2 = the entry sp, atom 10 = the size n, atom aINST = the allocator instance
     (this), atom aSO = the BufferedStackTrace object, atom aBP = its trace buffer, atoms 3, 8, 9, 18-27 = the
     caller's gp and callee-saved registers.
   REGS_G is the register file at the entry over those atoms (a0 = this, a1 = n, a2 = the alignment, a3 = the stack
   object, a4 = the alloc_type, a5 = can_fill; a2 / a4 are the malloc call site's, FCimg.ALLOC_AL_MALLOC /
   ALLOC_ATP_MALLOC; a5 is the atom 15, with the fact 0 <= x15 <= 1, so both can_fill values are covered).
   The regions are: the stack object (aSO), the scratch window of AFSTACK bytes below the entry sp, an empty slot
   (so that the region indices of AFhz's states are kept), and the regions of AFhy.REG0 / AFi1.REG0K with the
   allocator instance's fields based at aINST. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFhy AFi1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require FCimg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition A_Allocate : Z := FCimg.ALLOC_ENTRY.
(* Allocate's stack need below its entry sp: its own frame (0x80) and its callees' (the depot 512, the refill
   1024 below a 176-byte frame, the memset), with room to spare.  Every caller has at least this below the
   sp at its call. *)
Definition AFSTACK : Z := 4096.
Definition aINST : nat := 11.  Definition aBP : nat := 12.  Definition aSO : nat := 13.
(* The instance-relative regions. *)
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
SOff aINST 0; SOff 10 0; SLit FCimg.ALLOC_AL_MALLOC; SOff aSO 0; SLit FCimg.ALLOC_ATP_MALLOC; SOff 15 0; SOff 16 0; SOff 17 0;
SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* An absolute region inside the allocator instance, re-based at aINST (atom8 / lits8 -> iatom8 / ilits8). *)
Definition rebase_inst (r : YP09.region) : YP09.region :=
YP09.mkRegion (Some aINST) (YP09.r_lo r - TFIB_INST) (YP09.r_hi r - TFIB_INST) (YP09.r_wlo r) (YP09.r_whi r)
(map (fun c => YP09.mkChunk (YP09.c_off c - TFIB_INST) (YP09.c_val c)) (YP09.r_chunks r)).
(* AFhy.REG0 without its stack region, the instance fields (entries 8 and 9 of the tail) based at aINST.  The literal is
   GENERATED from AFhy.v's REG0 text by the internal file gen_tail0g.py (a Theorem Labs lane's literal form, AFhy's symbolic
   forms such as `lit8 (TFIB_TP - 88) TFIB_TSD` kept, which the walk files rewrite); TAIL0G_derived checks that it is
   exactly the derivation from the seed. *)
Definition TAIL0G : smem :=
[
lit1 0xabb98 1; lit4 0xabbbc 30; lit8 0xa2000 0x13c9e8; lit8 0x13ca08 0x1e00010000; lit1 0x12d122 0; lit1 0xaa720 1;
lit4 0xaa724 0; lit1 0xaa71c 1; iatom8 0x20 aSB; ilits8 0xe20 [0x10000000000; 0x108000010];
lit8 0x103c8 0x218a392cd3d5dbf; lits8 0x10438 CTZ_TABLE; lits8 0x10538 CTZ_TABLE; lit8 0x10328 0xcc6e96b9cc6e96b9;
lit8 0xa2008 0xa86b8; lit8 0xa2010 0xaaeb8; lit8 0xa2018 0xabba8; lit8 0xa2020 0xabbb0; lit8 0xa2028 0xabba0;
lit8 0xa2030 0xa3e90; lit8 0xa1ff0 0x13a960; lit8 0x13a960 4096; lit8 0x13ca60 0xffffffffffffffff;
atom8 0xaaeb8 aSHB; lit8 0xabba0 0x7fffffffffff; lit8 0xabba8 0; lit8 0xabbb0 0; lit8 0xa3e90 0x9b6b8;
lits8 0xa86e0 [0x100000000000; 0xbe00000000]; lits8 0xa8700 [0x1000100000000; 0x101010101000001];
lit8 0xa2c68 0x10; lit4 0x5ddf00 0; lit8 0x13c980 0; lit8 (TFIB_TP - 88) TFIB_TSD; atom8 TFIB_TSD aC;
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
(* The two re-based entries are the instance's fields at +0x20 and +0xe20 (struct offsets, the same code in both
   images): this pins the position of the instance regions in AFhy.REG0. *)
Lemma TAIL0G_derived :
TAIL0G = firstn 8 (tl AFhy.REG0) ++ map rebase_inst (firstn 2 (skipn 8 (tl AFhy.REG0))) ++ skipn 10 (tl AFhy.REG0).
Proof. vm_compute. reflexivity. Qed.
Lemma TAIL0G_inst_fields :
map (fun r => (YP09.r_base r, YP09.r_lo r)) (firstn 2 (skipn 8 TAIL0G)) = [(Some aINST, 0x20); (Some aINST, 0xe20)].
Proof. vm_compute. reflexivity. Qed.
(* The same for AFi1.REG0K: its aK region holds the header byte and it has no aU region. *)
Definition TAIL0KG : smem :=
firstn 44 TAIL0G ++
[YP09.mkRegion (Some aK) 0 16 0 16 [YP09.mkChunk 1 (CVal 1 (SOff aJB 0))];
YP09.mkRegion (Some aSK) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 250))] ].
(* The facts: AFhy.FG / AFi1.FK with the entry sp's bound at AFSTACK, and the frame atoms. *)
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
