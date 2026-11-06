(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGi9.v (a working branch 84ee52cd012, file sha256 0d55a85ac293) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 6 image addresses moved by code-verified function pairs (18 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py; 1 the tool cannot place or places wrongly, read out of the fuzz_state image itself); no other numeral changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFhy AGhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 6. Set Printing Width 250.
Definition aQ : nat := 39.    Definition aRES : nat := 40.  Definition aNCH : nat := 41.
Definition aMS : nat := 42.   Definition aMAP : nat := 45.
Definition aEND : nat := 46.  Definition aTL : nat := 48.   Definition aQS : nat := 52.   Definition aBSL : nat := 55.
Definition aJ5 : nat := 43.   Definition aJ6 : nat := 44.   Definition aJ7 : nat := 54.   Definition aJ8 : nat := 56.
Definition aJ9 : nat := 57.   Definition aI1 : nat := 58.   Definition aI2 : nat := 59.   Definition aI3 : nat := 60.
Definition aSM : nat := 61.   Definition aUE : nat := 62.   Definition aRL : nat := 64.   Definition aN8DS : nat := 65.  Definition aPBS : nat := 66.
Definition sHAV : nat := 80.
Definition sL1 : nat := 96.
Definition sM1 : nat := 104.
Definition sL2 : nat := 110.
Definition sM2 : nat := 118.
Definition sMX : nat := 128.
Definition sD1 : nat := 129.
Definition sGA : nat := 145.
Definition sL3 : nat := 146.
Definition sM3 : nat := 154.
Definition sL4 : nat := 160.
Definition sM4 : nat := 168.
Definition sL5 : nat := 174.
(* An 8-byte writable field of the allocator instance, holding an atom. *)
Definition iatom8w (o : Z) (k : nat) : YP09.region := YP09.mkRegion (Some aINST) o (o + 8) o (o + 8) [YP09.mkChunk o (CVal 8 (SOff k 0))].
(* The largest request size (exclusive) the secondary walk covers.  The walk asks the kernel for a map of
   MSv < n + 12296 bytes; the size an instance may ask for is its own bound NOBW (AGif4.ifs_grant_w), and this
   constant is only how far the walk's own arithmetic is proved: the clz sweep of AGi8, AGjm.LGv_range and
   AGjm.BSLv_range, AGjp.shadow_marks.  cgif's MALLOC_MAX (2 ^ 28) and the shared reply instance's
   cf_malloc_max (2 ^ 29 + 2 ^ 20) are both below it; Allocate itself rejects only sizes of 2 ^ 40 and more. *)
Definition SEC_NMAX : Z := 2 ^ 30 - 4 * 4096.
Lemma nrange_sec : forall n, 64513 <= n < MALLOC_MAX -> 64513 <= n < SEC_NMAX.
Proof. intros n H. unfold MALLOC_MAX, SEC_NMAX in *. lia. Qed.
(* The secondary path's facts: AGhy's frame facts (the entry sp, the instance, the stack object and its buffer),
   then YFi9.FS without its entry-sp fact. *)
Definition FS_atoms : list (nat * afact) :=
frame_facts ++
[ (10%nat, mkAF 64513 (SEC_NMAX - 1) 0);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)       ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)         ;
(aSB, mkAF kHighMemBeg CEIL_MAX 16)         ;
(aTOP, mkAF kHighMemBeg kHighMemEnd 12);
(aLEN, mkAF 1 30 0);
(aJ0, mkAF 0 (2 ^ 64 - 1) 0);
(aR8, mkAF 64520 SEC_NMAX 3);
(aQ, mkAF 4096 CEIL_MAX 12)                ;
(aRES, mkAF 0 1048576 14);
(aNCH, mkAF 0 1048575 0);
(aMS, mkAF 73728 (SEC_NMAX + 2 * 4096) 12);
(aJ5, mkAF 0 (2 ^ 64 - 1) 0); (aJ6, mkAF 0 (2 ^ 64 - 1) 0);
(aSHB, mkAF 0x7fff8000 0x7fff8000 12);
(aJ1, mkAF 0 (2 ^ 64 - 1) 0); (aJ2, mkAF 0 (2 ^ 64 - 1) 0); (aJ3, mkAF 0 (2 ^ 64 - 1) 0);
(aJ4, mkAF 0 (2 ^ 64 - 1) 0); (aJ7, mkAF 0 (2 ^ 64 - 1) 0); (aJ8, mkAF 0 (2 ^ 64 - 1) 0); (aJ9, mkAF 0 (2 ^ 64 - 1) 0);
(aI1, mkAF 0 (2 ^ 64 - 1) 0); (aI2, mkAF 0 (2 ^ 64 - 1) 0); (aI3, mkAF 0 (2 ^ 64 - 1) 0);
(aND, mkAF (64520 + 4096) (SEC_NMAX + 4096) 3) ].
Definition FS : facts := mkFacts FS_atoms [] [].
Definition FS2_atoms : list (nat * afact) :=
FS_atoms ++
[ (aMAP, mkAF TFIB_IMG_END (CEIL_MAX - 73728) 12)    ;
(aEND, mkAF (TFIB_IMG_END + 4096) CEIL_MAX 3);
(aTL, mkAF 0 4088 3);
(aQS, mkAF 4096 CEIL_MAX 3)                 ;
(aBSL, mkAF TFIB_IMG_LO TFIB_IMG_END 3);
(aSM, mkAF (kLowShadowBeg + TFIB_IMG_END / 8) kHighShadowEnd 9)    ;
(aUE, mkAF (TFIB_IMG_END + 4096) CEIL_MAX 3);
(aRL, mkAF 2048 (2048 + 2 * 4096) 3);
(aN8DS, mkAF 64512 SEC_NMAX 3);
(aPBS, mkAF (kLowShadowBeg + TFIB_IMG_END / 8) kHighShadowEnd 0)     ].
Definition FS2 : facts := mkFacts FS2_atoms [] [].
(* LargeMmapAllocator's stats.by_size_log[lg] cell (at the instance + 168 + 8 * lg). *)
Definition R_bsl : YP09.region := YP09.mkRegion (Some aBSL) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff aJ8 0))].
(* YFi9.SREG0 over AGhy.REG0G: the regions of AGhy.SSG up to the thread's 2800 window, then the secondary
   allocator's regions, with the instance fields (o_sec*, 80, 88, o_comb_stats) based at aINST. *)
Definition SREG0 : smem :=
R_soG :: R_scrG :: R_slotG :: firstn 40 TAIL0G ++
[ YP09.mkRegion (Some aT) 2872 2888 2872 2888 [YP09.mkChunk 2872 (CVal 8 (SOff aJ4 0)); YP09.mkChunk 2880 (CVal 8 (SOff aJ5 0))];
YP09.mkRegion (Some aT) 2904 2912 2904 2912 [YP09.mkChunk 2904 (CVal 8 (SOff aJ9 0))];
ilit8 o_sec 4096;
iatom8 o_sec_chunks aQ; iatom8 80 aQ; ilit8 88 kPtrArrayResv;
iatom8w o_sec_reserved aRES; iatom8w o_sec_n aNCH;
YP09.mkRegion (Some aINST) o_sec_sorted (o_sec_sorted + 1) o_sec_sorted (o_sec_sorted + 1) [];
YP09.mkRegion (Some aINST) o_sec_stats (o_sec_stats + 32) o_sec_stats (o_sec_stats + 32)
[YP09.mkChunk o_sec_stats (CVal 8 (SOff aI1 0)); YP09.mkChunk (o_sec_stats + 16) (CVal 8 (SOff aI2 0));
YP09.mkChunk (o_sec_stats + 24) (CVal 8 (SOff aI3 0))];
YP09.mkRegion (Some aINST) o_sec_mutex (o_sec_mutex + 4) o_sec_mutex (o_sec_mutex + 4)
[YP09.mkChunk o_sec_mutex (CVal 4 (SLit 0))];
YP09.mkRegion (Some aINST) o_comb_stats (o_comb_stats + 40) o_comb_stats (o_comb_stats + 40)
[YP09.mkChunk (o_comb_stats + 16) (CVal 8 (SOff aJ6 0)); YP09.mkChunk (o_comb_stats + 24) (CVal 8 (SOff aJ7 0))];
lit8 0x9f6d8 0xa15a8; lit8 0xa15a8 0x1931d; lit8 0x139b68 0x1010101; lit8 0x139af8 0; R_bsl ].
Lemma SREG0_len : length SREG0 = 60%nat. Proof. reflexivity. Qed.
(* The secondary seed at Allocate's entry (AGhy.SSG's registers). *)
Definition S0 : sstate := mkSS A_Allocate REGS_G SREG0 None FS.
Definition runtoC (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL pc ss).
