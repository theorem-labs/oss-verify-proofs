(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: REGENERATED (not relocated) from proofs/cgif/cgif_file_fuzzer/lib/AGhy.v
   (cold/c-asan-realloc-primary 63b73430c18, file sha256 378d6b206c74) for omx-clap-core/fuzz_preset's asan-ubsan
   image (unstripped fuzz_preset.asan-ubsan, sha256 3b5e1a099b53), method
   h-mani-a8's agreloc-method.md section 3.  No numeral of the cgif seed is carried
   over: A_Allocate and the two constant call-site arguments are the generated names of AU/FCimgB.v, and the
   start-up cells TAIL0G are derived from this unit's OWN seed (Reusable/YFhy.v REG0), so they follow that file's
   image.  B deviates from the note in one point: REGS_G's a5 is kept as the generic can_fill atom [SOff 15 0]
   (fact (15%nat, mkAF 0 1 0)), as in the cgif seed, because AGhz / AGi0 / AGi2 / AGi4 and AllocG's contract are
   generic in cf; FCimgB.ALLOC_CF_MALLOC = 1 is the value of the malloc call site only, an instantiation. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFhy YFi1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FCimgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition A_Allocate : Z := FCimgB.ALLOC_ENTRY.
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
SOff aINST 0; SOff 10 0; SLit FCimgB.ALLOC_AL_MALLOC; SOff aSO 0; SLit FCimgB.ALLOC_ATP_MALLOC; SOff 15 0;
SOff 16 0; SOff 17 0;
SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
(* The start-up cells, derived from this unit's own seed: YFhy.REG0 without its stack region, with the two
   allocator-instance regions (the atom8 at TFIB_INST + 0x20 and the lits8 at TFIB_INST + 0xe20, entries 8 and 9
   of [tl YFhy.REG0]) re-based on the instance atom aINST.  This is the transformation c-asan applied to cgif's
   YFhy.REG0 by hand; written this way it carries no image numeral of its own. *)
Definition rebase_inst (r : YP09.region) : YP09.region :=
YP09.mkRegion (Some aINST) (YP09.r_lo r - TFIB_INST) (YP09.r_hi r - TFIB_INST) (YP09.r_wlo r) (YP09.r_whi r)
(map (fun c => YP09.mkChunk (YP09.c_off c - TFIB_INST) (YP09.c_val c)) (YP09.r_chunks r)).
Definition TAIL0G : smem :=
firstn 8 (tl YFhy.REG0) ++ map rebase_inst (firstn 2 (skipn 8 (tl YFhy.REG0))) ++ skipn 10 (tl YFhy.REG0).
Lemma TAIL0G_inst_fields :
map (fun r => (YP09.r_base r, YP09.r_lo r)) (firstn 2 (skipn 8 TAIL0G)) = [(Some aINST, 0x20); (Some aINST, 0xe20)].
Proof. vm_compute. reflexivity. Qed.
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
