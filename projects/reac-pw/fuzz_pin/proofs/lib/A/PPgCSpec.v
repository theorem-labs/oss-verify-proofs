(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are
   restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin image A from
   proofs/libreac/fuzz_knock/lib/A/APgCSpec.v (the Section form of its lines 32-164) and
   proofs/libreac/fuzz_knock/lib/A/ACfn.v (lines 27-73, the harness contract) at origin/ossv/recipes
   6ebe35ba632, with their module paths changed, in the shape reac-pw/fuzz_qdisc's lib/A/QPgCSpec.v uses
   (origin/cold/h-small-a3-qdisca-a4 752182a65173). rule 24 (reuse): no function is proved here; this file
   states the ASan-level contracts only.

   IMAGE-INDEPENDENT: this file Requires no image module. segs, the symbol record B, the meter MT, the sink K,
   the entry addresses, the table address, the table's pointers and the harness constants are all Section
   variables or parameters, so image B (fuzz_pin.asan-ubsan) instantiates the same texts.

   THE PIN CHANGES against knock's texts, and the measurement behind each. Measured with capstone 5.0.7 and
   pyelftools 0.33 over the pinned images fuzz_pin.asan (sha256
   3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16) and fuzz_pin.asan-ubsan (sha256
   d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f), with the symbol names of their
   unstripped twins (435309a6b12c4d3e09a8484ec253b5fab600e4f00c28694ac28db2fc7a4475ab,
   635d02c7e8fa2e1653012207b6ddd2f2c5dd3b8e578ee9607cdc35b94e5260bb).
   - knock has three callees; pin has six, and one of them (reac_box_pin_parse) allocates a frame on the side
     stack for frames, calls four wrappers and writes two cells of the CALLER's frame. So the contracts come
     in two shapes: pin_post_simple (one memory clause: every byte outside the callee's own stack window and
     outside the named cells is unchanged) for the five callees that take no frame, and pin_post_parse
     (knock's four memory clauses) for reac_box_pin_parse, whose own frame on the side stack is taken and
     given back inside the call, so a caller cannot name it.
   - the table fuzz_catalogue is at 0x97ee0 in image A and 0x98000 in image B, so its address is the
     parameter `cat`. Its 11 rows hold a token pointer at +0 and a display pointer at +8; the 22 pointers are
     EQUAL in the two images (0x20dc0 .. 0x211a0, .rodata), but a shared text may carry no unit-dependent
     literal, so they are the parameters TP and DP with the premise pin_cat_ok, which each image discharges
     from its own read-only-data fact and its own start-up shadow cells.
   - the ':' set string strcspn reads is at 0x20d80 in both images; it is the parameter `colonp` with the
     premise pin_ro_str.
   - the stack windows: check_known / check_row / check_label / reac_box_catalogue take 16 bytes
     (`addi sp,sp,-0x10`, `sd ra,8(sp)`); fuzz_catalogue_row takes 64 (`addi sp,sp,-0x40`) and calls the
     strlen and bcmp wrappers, each of which uses up to 2 * ESTACK below ITS sp; reac_box_pin_parse takes
     160 bytes in image A (`addi sp,sp,-0xa0` 0x80b44) and 192 in image B (`addi sp,sp,-0xc0` 0x80ba4), then
     rounds sp down to a multiple of 32 (`andi sp,sp,-0x20`), which takes at most 16 bytes more, and calls
     the strcspn, strlen and strncmp wrappers. ONE bound per contract covers both images: T_leaf_STK 16,
     T_row_STK 64 + 2 * ESTACK, T_parse_STK 208 + 2 * ESTACK. A larger bound is a weaker claim, and the one
     caller (LLVMFuzzerTestOneInput, 128-byte frame rounded down to 32) stays inside LLVMF_STK 32768.
   - the results: fuzz_catalogue_row returns pin_spec.row_ptr cat sb (the FIRST row whose token is the probe,
     else 0) and reac_box_pin_parse returns 0 or -1 and, when it returns 0, stores the row address and the
     label address. Both are pin_spec's own functions (lib/Prog/pin_spec.v), the text h-small-q1's plain and
     UBSan contracts use, so the two builds state one result.
   - check_row and check_label are the same code (`bne a0,a1` to an abort that the premise makes dead), so
     one definition tpin_eq_leaf_specX carries both; check_known differs (`seqz` of both arguments).
   - image B holds an extra trap instruction (`unimp`) on each of its error paths, and UBSan checks on LIVE
     paths that today's premises discharge, so a later edit must not drop any of these premises:
     reac_box_pin_parse checks cat <> 0, cat mod 8 = 0 and that cat + 0x128 i does not wrap (from
     pin_cat_ok, with i < 11 because reac_box_catalogue stores the count 11, CA1.6, which also rules out an
     overflow of i * 0x128), that spec + toklen does not wrap and is not 0 or -1 (from pin_spec_str's bound
     sa + len + 1 <= 2 ^ 63), and mo mod 8 = 0 and lb mod 8 = 0 (from CP1.3); the harness checks want mod 8 = 0
     (row_addr cat i with cat mod 8 = 0) and SEVEN pointer-overflow checks of the cursor and the copy
     (data + 1, rest + k, spec + k and the scan's spec + i; from the heap block facts, and, for an empty
     input, from A_EMPTY <> 0: LIB1.2's n = 0 case hands the image's empty-input object, whose address is not
     0); reac_box_catalogue checks c mod 8 = 0 (CA1.1). The contract text names no error path, so the two
     builds share it.

   WHAT THE WRAPPERS ASK FOR, OBJECT BY OBJECT (the audit behind the amem_range clauses). Every wrapper a
   walk calls asks, besides the bytes and the shadow, that the range it reads lies in the application
   memory range: astrlen_realizes `amem_range x (k + 1)` (lib/A/Rt/StrlenDef.v), abcmp_realizes
   `amem_range x n` (lib/Reusable/YG0d.v:372), amemchr_realizes `amem_range x n`, and lib/A/PPgWrap.v's
   awrap_str for the strcspn and strncmp wrappers. So:
   - the 11 tokens and the ':' set string: pin_ro_str carries `amem_range x (len + 8)`, the strncmp
     wrapper's form (it implies the strlen and strcspn wrappers' `len + 1` by pin_amem_range_le). Without it
     a token in the high shadow band meets every other clause, and no wrapper call goes through.
   - the table fuzz_catalogue: pin_cat_ok carries `amem_range cat CAT_BYTES`. No wrapper reads the table,
     but the same gap would let the table sit in a band the program's own loads cannot reach.
   - the spec string: pin_spec_str carries `amem_range sa (len + 1)`; the strncmp wrapper's `len + 8` comes
     from the string's heap block (al_blocks gives `in_app b (req_size m)`, and in_app leaves at least 4096
     bytes below kLowMemEnd in the low band and up to the ceiling in the high band, lib/Reusable/YG0f.v:358).
   - the probe bytes of fuzz_catalogue_row: tpin_row_specX carries `amem_range sa n` (the bcmp wrapper).
   - the two out-cells of reac_box_pin_parse: NO premise, and none is needed. No wrapper touches them; the
     program stores 8 bytes with an instrumented check, which afobj's shadow clause covers, and the caller
     gets the band from the allocator relation's frame law (lib/Reusable/YG0d.v:457-465 al_frames gives
     `in_app (frame_addr ly cid pos) (fs_frame_bytes cid)`).
   - the harness's heap block and the input block: NO premise, and none is needed. Both are blocks of the
     allocator state, and al_blocks (lib/Reusable/YG0d.v:433-439) gives `in_app p (req_size n)` for every
     block, from which the walk derives the band at each wrapper call.

   ===================================================================================================
   THE ENGLISH CLAIM TREES (one claim per line; an id that never changes; the ids each claim uses).
   The builds a premise applies to: [A] = fuzz_pin.asan, [B] = fuzz_pin.asan-ubsan, [AB] = both.
   Size arithmetic: every length, index and address below is integer arithmetic with no wrap, unless the
   line says "64-bit", which means the value is read or written as a 64-bit word modulo 2 ^ 64.
   ===================================================================================================

   PIN-KIT (the premise block every claim below starts from; pin_pre_kit). [AB]
   PIN-KIT.1 The run is at the entry of the function. The register ra holds a return address of a call, and
     that address is at least 4096.
   PIN-KIT.2 gp and tp hold the image's values (as_gp B, as_tp B).
   PIN-KIT.3 sp is a multiple of 16, the stack below sp down to the function's own window is inside the
     caller's budget, and sp is not above the caller's start sp.
   PIN-KIT.4 The run so far is a journal from the harness's start state to the state at this call
     (ajournal), and the frame chain from sp is the list ch.
   PIN-KIT.5 The event count of the start state plus the journal's events plus this call's events is at most
     EV_MAX. The five callees spend no event; reac_box_pin_parse spends none (the side stack for frames does
     not tick the event count).

   --------------------------------------------------------------------------------------------------
   CK1 (contract: check_known at address a; tpin_check_known_specX). Uses PIN-KIT.
     Start state: PIN-KIT with the window T_leaf_STK = 16.
     CK1.1 Premise: a0 = 0 if and only if a1 <> 0 (64-bit words).
     Then every run from the start state returns to the address in ra. On the way it makes no fault and no
     system call, and the run does not reach the abort.
     CK1.2 At the return: every byte outside [sp - 16, sp) is unchanged, the callee-saved registers, gp, tp
       and sp have their start values, the heap blocks and the frames are the start ones, and the allocator
       state's meter did not grow.

   CR1 (contract: check_row and check_label at address a; tpin_eq_leaf_specX, with the two names
     tpin_check_row_specX and tpin_check_label_specX). Uses PIN-KIT.
     Start state: PIN-KIT with the window T_leaf_STK = 16.
     CR1.1 Premise: a0 and a1 hold the same 64-bit word.
     Then every run returns to the address in ra, makes no fault and no system call, and does not reach the
     abort; CK1.2 holds of the memory, the registers and the allocator state.

   CA1 (contract: reac_box_catalogue at address a, over a table at cat; tpin_catalogue_specX).
     Uses PIN-KIT, CA2.
     Start state: PIN-KIT with the window T_leaf_STK = 16, and:
     CA1.1 a0 = c (64-bit), c is not 0 and c is a multiple of 8.
     CA1.2 c and the 8 bytes from c are inside one frame (cid, pos) that the caller owns, and that frame is
       in the journal's own list. [AB; the only caller is reac_box_pin_parse, whose count cell is in its own
       frame on the side stack]
     CA1.3 The 8 bytes from c are marked usable in the shadow map (afobj).
     CA1.4 The 8 bytes from c are outside [sp - 16, sp).
     Then every run returns to the address in ra, and at the return:
     CA1.5 a0 = cat (64-bit).
     CA1.6 The 8 bytes at c hold 11 (the row count; integer, no wrap).
     CA1.7 Every byte outside [sp - 16, sp) and outside [c, c + 8) is unchanged; the rest of CK1.2 holds.
   CA2 (shared fact: the instrumented check before the 8-byte store at c passes because of CA1.3.) [AB]

   CT1 (contract: fuzz_catalogue_row at address a, over a table at cat with pointers TP and DP;
     tpin_row_specX). Uses PIN-KIT, CT2, CT3, F-CAT, F-RO.
     Start state: PIN-KIT with the window T_row_STK = 64 + 2 * ESTACK, and:
     CT1.1 a0 = sa and a1 = n (64-bit), n is the length of the byte list sb, and n < 2 ^ 32.
     CT1.2 The n bytes at sa are sb; sa is not 0 and sa + n is at most 2 ^ 63.
     CT1.3 The n bytes at sa are marked usable in the shadow map, their shadow bytes are readable, and they
       are outside [sp - T_row_STK, sp).
     CT1.4 F-CAT holds of the table at cat with the pointers TP and DP: every one of its bytes and
       every token's bytes and NUL are there, are marked usable, and lie in the application memory range
       (amem_range), which the strlen and bcmp wrappers ask for.
     CT1.5 F-RO holds: the image's read-only bytes read as the image.
     CT1.6 The table and the 11 tokens are outside [sp - T_row_STK, sp).
     Then every run returns to the address in ra, and at the return:
     CT1.7 a0 = pin_spec.row_ptr cat sb: the address of the FIRST row whose token is sb, else 0 (64-bit).
     CT1.8 Every byte outside [sp - T_row_STK, sp) is unchanged; the rest of CK1.2 holds.
   CT2 (callee offer: the strlen wrapper, lib/A/Rt/StrlenDef.v astrlen_realizes, at the trampoline
     0x41908 [AB]): with the token's bytes and its NUL marked usable, it returns the token's length and
     writes only its own stack.
   CT3 (callee offer: the bcmp wrapper, lib/Reusable/YG0d.v abcmp_realizes, at the trampoline 0x41924
     [AB]): with both ranges marked usable, it returns 0 exactly when the n bytes are equal.

   CP1 (contract: reac_box_pin_parse at address a, over a table at cat with pointers TP and DP and the ':'
     set at colonp; tpin_parse_specX). Uses PIN-KIT, CT2, CP2, CP3, CP4, CA1, F-CAT, F-SET, F-RO, F-FS,
     F-RO-LAW.
     Start state: PIN-KIT with the window T_parse_STK = 208 + 2 * ESTACK, and:
     CP1.1 a0 = sa, a1 = mo, a2 = lb (64-bit), each below 2 ^ 64.
     CP1.2 If sa <> 0: the bytes at sa are the byte list s and then one NUL byte; s holds no NUL; the s + 1
       bytes are marked usable, their shadow bytes are readable, the bytes between the NUL and the end of
       the NUL's 8-byte word are readable (the wrappers read whole words), they lie in the application
       memory range, and all of them are outside [sp - T_parse_STK, sp). AND the s + 1 bytes are inside one
       heap block (b, m) of the caller's allocator state. [AB; the harness's string is its malloc block,
       so lib/A/Prog/PinBlkTail.v's blk_tail_present gives the tail clause] The heap-block clause is what
       keeps the string across the function's first call: __asan_stack_malloc_0 (0x80bb8) keeps only the
       bytes the runtime does not own; a heap block's bytes are not owned (AR_blocks_law,
       lib/Reusable/YG0d.v:437), and its shadow, which is the runtime's own, is given again in every state
       of the allocator relation (AR_shadow_law, YG0d.v:440-444). Without it, a string inside the free class-0
       frame that call returns meets every other premise and breaks the check at 0x80c58.
     CP1.3 If the call is live (sa, mo and lb are all not 0): mo and lb are 8-aligned, each is in a frame the
       caller owns and in the journal's own list, the 8 bytes of each are marked usable, the two cells do not
       overlap, and neither is inside [sp - T_parse_STK, sp) or inside the string.
     CP1.4 F-CAT holds of the table at cat with TP and DP; the ':' set string at colonp holds ':' and a NUL
       and is marked usable (F-SET).
     CP1.5 F-RO holds.
     CP1.6 The table, the 11 tokens and the ':' set are outside [sp - T_parse_STK, sp).
     CP1.7 F-FS: one frame of class 0 is free on the side stack for frames, so the frame the function takes
       is a real frame. [AB: `li a0,0x40` + `jal __asan_stack_malloc_0` at 0x80bb4 / 0x80c14]
     CP1.12 F-RO-LAW: in EVERY state of the allocator relation whose read-only bytes read as the image,
       the table with its 22 pointers and 11 tokens and the ':' set string meet F-CAT and F-SET
       (pin_ro_law). The entry-memory facts of CP1.4 do not survive the function's first call
       (__asan_stack_malloc_0 keeps only bytes the runtime does not own, and the image's shadow is the
       runtime's own); this fact does. [AB; each image discharges it at its own segs and B]
     Then every run returns to the address in ra, and at the return:
     CP1.8 a0 = 0 when the pin is accepted, else -1 as a 64-bit word (2 ^ 64 - 1).
     CP1.9 When the pin is accepted: the 8 bytes at mo hold the address of the row the token names, and the
       8 bytes at lb hold the address of the label: the byte after the first ':' of the string when a byte
       follows it, else the row's display pointer DP i. This is pin_parse_res: pin_spec's parse_out with
       the plain image's display pointer (pin_spec.v:97-98) replaced by DP i.
     CP1.10 Every byte of the caller's stack above the window, every byte of every heap block, every byte of
       every frame the caller owns and its shadow bytes, and every read-only byte of the image, are unchanged
       except the two out-cells.
     CP1.11 The frames and the heap blocks at the return are the start ones (the frame the function takes is
       given back), and the allocator state's meter did not grow.
   CP2 (callee offer: the strcspn wrapper, lib/A/PPgWrap.v astrcspn_realizes, at the trampoline 0x4191c
     [AB]): for a set of exactly one byte, with the string and the set (each with its NUL) marked usable
     and in the application memory range, it returns the length of the longest first part of the string
     that holds no byte of the set, and writes only its own stack.
   CP3 (callee offer: the strncmp wrapper, lib/A/PPgWrap.v astrncmp_realizes, at the trampoline 0x41914
     [AB]): with both whole strings and their NULs marked usable, and each string's length + 8 bytes in the
     application memory range, it returns 0 exactly when the first n bytes are equal and hold no NUL before
     a difference.
   CP4 (callee offer: the side stack for frames, lib/A/Rt/StackMalloc0.v stack_malloc0_contract, class 0 at
     0x3c8e4 [AB]): it gives a 64-byte frame whose shadow bytes are 0 and whose last word holds the flag
     address, or 0 when every frame of the class is in use (CP1.7 makes that case dead).

   LIB1 (the top claim: LLVMFuzzerTestOneInput; pin_lib_contract_x). Uses CK1, CR1, CT1, CP1, F-ALLOC,
     F-CPY, F-MCHR, CT2, F-CAT, F-RO, F-FS, F-RO-LAW, and the class-1 frame offer F-FS1.
     Start state (this is the start state every claim above draws its premises from):
     LIB1.1 pc is the entry of LLVMFuzzerTestOneInput, ra = RA_LLVMF, a0 = p, a1 = n. [AB]
     LIB1.2 Either n = 0 and p is the image's empty-input object, or 0 < n < 2 ^ 26 and (p, n) is a heap
       block. The n bytes at p are the input pl. [AB]
     LIB1.3 The allocator relation AR holds, no frame is in use, the event count leaves EV_LIB events, and
       the live bytes leave LIVE_LIB bytes. [AB]
     LIB1.4 F-RO: every read-only byte of the image that the runtime does not own reads as the image
       (arodata_okP over RLO .. RHI, pin's .data.rel.ro start .. .got end: image A 0x97b00 .. 0x99d48,
       image B 0x97c20 .. 0x99e68). From it the walk derives F-CAT's byte half (the table and the tokens are
       read-only bytes) and the read-only premise of every wrapper (aro_unowned). [AB]
     LIB1.5 F-CAT (shadow half): the table's 3256 bytes and each token's bytes and NUL are marked usable
       and lie in the application memory range.
       The walk derives this from AR's zero-shadow ranges and const cells at the image's own symbol record
       (the 24 ASan globals of pin: 23 strings in .rodata and fuzz_catalogue in .data.rel.ro, registered by
       asan.module_ctor), not from a new premise of this contract. [AB]
     LIB1.6 F-FS: no frame of class 0 or class 1 is in use, so the two stack_malloc calls give real frames.
       From LIB1.3 (frames S = []). [AB]
     LIB1.7 The sink is closed, the file system is sorted, and the runtime's metadata invariant holds. [AB]
     LIB1.8 The meter MT admits the call (mo_ok MT S (XM_LIB n)). The consumer fixes MT := ameter_triv
       (lib/A/PPgLib.v pin_lib_x_all, as knock's lib/A/APgLib.v:305 does and lib/A/AD2o.v:39-41 consumes).
     Then every run from the start state reaches RA_LLVMF with a0 = 0; it makes no fault, no abort and no
     system call outside the sink; it writes no file; the input block's bytes are unchanged; the heap blocks
     at the return are a permutation of the start ones (the one block the harness takes is given back); and
     the journal's events are at most EV_LIB.
   F-ALLOC (callee offer: malloc and free, lib/Reusable/YG0d.v amalloc_realizes / afree_realizes, taken as
     Section hypotheses at the call sites of the walk and discharged in the close, the released form of
     libreac/fuzz_grant lib/A/Prog/GrantACjr.v:167-168 and lib/A/Prog/GrantLibXClosed.v:62-65). The harness
     asks malloc for n + 1 bytes with n at most 2 ^ 26 - 2, so the call takes both allocator paths (the size
     class path and the large mmap path); the contract's size premise is 0 <= n + 1 < MALLOC_MAX (2 ^ 28)
     and blocks_bytes S + n + 1 <= LIVE_MAX (2 ^ 34), which LIB1.2 and LIB1.3 give. What the walk needs of
     the result: the block (p1, n + 1) is in the heap blocks, its n + 1 bytes are usable and present, and
     the bytes between its last byte and the end of that byte's 8-byte word are present (the guard bytes
     after it, lib/A/Prog/PinBlkTail.v blk_tail_present). Each call spends one event, so the harness's
     journal ends at k = 2 (PIN_EV_LIB). [AB]
   F-CPY (callee offer: __asan_memcpy at 0x51a40, aintrin_realizes OCpy [AB]).
   F-MCHR (callee offer: the memchr wrapper at the trampoline 0x41928, lib/A/Rt/MemchrDef.v
     amemchr_realizes [AB]).
   F-SET (shared fact: the ':' set string at colonp holds ':' and a NUL, is marked usable, lies in the
     application memory range, and is outside the callee's stack window). [AB]
   F-FS1 (callee offer: the side stack for frames, class 1 at 0x3ca58, lib/A/AF0s.v stack_malloc1_contract
     [AB]): the harness's 96-byte frame, as CP4 for class 0.
   F-RO-LAW in the harness. LIB1's text is ACfn's and takes no new premise (the adapter to the core's
     contract must stay conversion), so the harness walk takes pin_ro_law at the image's own segs, B, RLO,
     RHI, table and pointers as a Section hypothesis, and the close discharges it ONCE at the real B: the
     bytes from the image (arodata_okP gives the image's bytes of every read-only address that B does not
     own), the shadow from the allocator relation's zero-shadow ranges and const cells at B (the start-up
     shadow cells listed in lib/A/PPgSat.v's header). The same fact gives the harness the entry premises
     of fuzz_catalogue_row (CT1.4) and of reac_box_pin_parse (CP1.4, CP1.12) at its two call sites, which
     both come after __asan_stack_malloc_1 (0x80724) and malloc (0x80824). fuzz_catalogue_row itself needs
     no durable fact: it makes no call that changes owned memory (its two wrappers keep every byte outside
     their stack window), so its entry-memory premises stay true to its return.

   Agreement record: see the commit message (accepted-by / refused-by lines).
   =================================================================================================== *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The stack each function uses below its caller's sp, one bound for both images (see the header). *)
Definition T_leaf_STK : Z := 16.
Definition T_row_STK : Z := 64 + 2 * ESTACK.
Definition T_parse_STK : Z := 208 + 2 * ESTACK.
(* No callee of the harness makes an allocator call, so none spends an event. *)
Definition EV_leaf : Z := 0.
Definition EV_row : Z := 0.
Definition EV_parse : Z := 0.
(* The ':' set string strcspn reads: one byte and its NUL. *)
Definition pin_colon_bytes : list byte := [Z_to_bv 8 COLON].
Definition pin_zbytes (l : list byte) : list Z := map (fun b : byte => bv_unsigned b) l.
Definition pin_tokn (i : nat) : Z := Z.of_nat (length (tok_bytes i)).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.

(* The bytes between x and the end of x's 8-byte word are readable: what musl's word loops read past a NUL
   (the form lib/A/Rt/StrlenDef.v:46 asks for). *)
Definition pin_str_tail (rd : reader) (x : Z) : Prop :=
forall a, x < a < x - x mod 8 + 8 -> rd a <> None.

(* A read-only C string at x whose bytes are l: its bytes and NUL are there and marked usable, and its
   length + 8 bytes lie in the application memory range (the strncmp wrapper asks for len + 8, the strlen
   and strcspn wrappers for len + 1, which pin_amem_range_le derives). *)
Definition pin_ro_str (m : word -> option byte) (rd : reader) (x : Z) (l : list byte) : Prop :=
0 < x /\ x + Z.of_nat (length l) + 1 <= 2 ^ 63 /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\
amem_range x (Z.of_nat (length l) + 8) /\
garr8 segs m x (pin_zbytes l ++ [0]) /\
range_addressable rd SHADOW_OFF x (Z.of_nat (length l) + 1) /\
shadow_hull_vis rd x (Z.of_nat (length l) + 1) /\
pin_str_tail rd (x + Z.of_nat (length l)).

(* amem_range is monotone in the length: the larger range gives every shorter one. *)
Lemma pin_amem_range_le : forall p n m, n <= m -> amem_range p m -> amem_range p n.
Proof. intros p n m Hnm [H|[H1 H2]]; [left; lia | right; split; [exact H1 | lia]]. Qed.

(* F-CAT: the box-model table at cat holds, in row i, the token pointer TP i and the display pointer DP i;
   each token is the read-only string pin_spec.tok_bytes i; the table's own bytes are marked usable. *)
Definition pin_cat_ok (m : word -> option byte) (rd : reader) (cat : Z) (TP DP : nat -> Z) : Prop :=
0 < cat /\ cat mod 8 = 0 /\ cat + CAT_BYTES <= 2 ^ 63 /\ amem_range cat CAT_BYTES /\
range_addressable rd SHADOW_OFF cat CAT_BYTES /\
(forall i, (i < CAT_N)%nat ->
 val_mem segs m (row_addr cat i) 8%nat (TP i) /\ val_mem segs m (row_addr cat i + 8) 8%nat (DP i) /\
 0 <= TP i < 2 ^ 64 /\ 0 <= DP i < 2 ^ 64 /\ pin_ro_str m rd (TP i) (tok_bytes i)).

(* The table and the tokens are not inside the window the callee writes. *)
Definition pin_cat_off_stack (cat : Z) (TP : nat -> Z) (regs : bvmap 5 word) (STK_f : Z) : Prop :=
(forall x, cat <= x < cat + CAT_BYTES -> ~ (spZ regs - STK_f <= x < spZ regs)) /\
(forall i x, (i < CAT_N)%nat -> TP i <= x <= TP i + pin_tokn i -> ~ (spZ regs - STK_f <= x < spZ regs)).

(* The spec string the caller hands reac_box_pin_parse: the bytes s, then a NUL, in a heap block. *)
Definition pin_spec_str (m : word -> option byte) (rd : reader) (regs : bvmap 5 word) (STK_f sa : Z)
(s : list byte) : Prop :=
~ In NUL s /\ 0 < sa /\ sa + Z.of_nat (length s) + 1 <= 2 ^ 63 /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
garr8 segs m sa (pin_zbytes s ++ [0]) /\
range_addressable rd SHADOW_OFF sa (Z.of_nat (length s) + 1) /\
shadow_hull_vis rd sa (Z.of_nat (length s) + 1) /\
pin_str_tail rd (sa + Z.of_nat (length s)) /\
amem_range sa (Z.of_nat (length s) + 1) /\
(forall x, sa <= x <= sa + Z.of_nat (length s) -> ~ (spZ regs - STK_f <= x < spZ regs)).

(* reac_box_pin_parse's result (pin_spec.parse_out at the display pointers DP): the first row whose token is
   the text before the first ':' of s, and the label just past that ':' when a byte follows it, else the
   row's display pointer. *)
Definition pin_label_at (DP : nat -> Z) (sa : Z) (s : list byte) (i : nat) : Z :=
match pin_label_off s with Some k => sa + Z.of_nat k | None => DP i end.
Definition pin_parse_live (sa mo lb : Z) : bool :=
negb (sa =? 0) && negb (mo =? 0) && negb (lb =? 0).
Definition pin_parse_res (cat : Z) (DP : nat -> Z) (sa mo lb : Z) (s : list byte) : option (Z * Z) :=
if pin_parse_live sa mo lb
then match pin_row s with Some i => Some (row_addr cat i, pin_label_at DP sa s i) | None => None end
else None.
(* The two out-cells of a live call. *)
Definition pin_out_cell (mo lb : Z) (a : Z) : Prop := mo <= a < mo + 8 \/ lb <= a < lb + 8.

(* The end of the 8-byte word that holds byte x: the musl word loops read up to it. *)
Definition pin_word_end (x : Z) : Z := x - x mod 8 + 8.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI : Z.

(* F-RO-LAW: the ONE fact about the image's read-only objects that every walk carries across a call that
   changes the runtime's own memory. In EVERY state of the allocator relation whose read-only bytes read as
   the image (arodata_okP), the table, its 22 pointers, its 11 tokens and the ':' set string are there,
   marked usable, and in range (pin_cat_ok, pin_ro_str). The entry-memory forms are not enough: the first
   call of reac_box_pin_parse, __asan_stack_malloc_0 (0x80bb8), keeps only the bytes the runtime does not
   own (lib/Reusable/YG0d.v:308-309), and the image's shadow is itself the runtime's own (aowned's lm_zone
   shadow, lib/Reusable/YG0n.v:427-433), so no call keeps the shadow facts; the harness reads the same
   objects after __asan_stack_malloc_1 (0x80724) and malloc (0x80824). What keeps them is the allocator
   relation at the image's own symbol record B (its zero-shadow ranges and const cells hold the start-up's
   shadow of the registered globals) together with the image's bytes. Each image discharges this ONE fact at
   its own segs and B (image A: P5, at tfibsegs and TfibB); reac_box_pin_parse takes it as a premise, and
   the harness walk, whose text is ACfn's and takes no new premise, takes it as a Section hypothesis. *)
Definition pin_ro_law (cat : Z) (TP DP : nat -> Z) (colonp : Z) : Prop :=
forall ly' S' (W' : world segs) mem' md', AR segs B ly' S' W' mem' md' ->
arodata_okP segs RLO RHI B (aview segs (w_H W') mem') ->
pin_cat_ok (mrestrict (w_H W') mem') (aview segs (w_H W') mem') cat TP DP /\
pin_ro_str (mrestrict (w_H W') mem') (aview segs (w_H W') mem') colonp pin_colon_bytes.

(* PIN-KIT: the premise block of every callee contract. *)
Definition pin_pre_kit (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(ch : list (Z * Z * Z)) (STK_f EV : Z) : Prop :=
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch /\
spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - STK_f /\ spZ regs <= sp0 /\
st_nev S + k + EV <= EV_MAX.

(* The post of a callee that takes no frame on the side stack: one memory clause, with the named cells E
   left out, and the result R. *)
Definition pin_post_simple (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(STK_f EV : Z) (E : Z -> Prop)
(R : bvmap 5 word -> (word -> option byte) -> world segs -> Prop)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
: world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_f <= a < spZ regs) -> ~ E a ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
R regs2 mem2 W2.

(* ================================ check_known (CK1) ================================ *)
Definition tpin_check_known_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch,
pin_pre_kit STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch T_leaf_STK EV_leaf ->
(getr regs 10 = w64 0 <-> getr regs 11 <> w64 0) ->
SRr segs W (cfg_at segs a regs memc mdc)
(pin_post_simple STK sp0 FP ly S W0 mem0 md0 own k regs T_leaf_STK EV_leaf
 (fun _ => False) (fun _ _ _ => True) lyc Sc W memc mdc).

(* ========================= check_row and check_label (CR1) ========================= *)
Definition tpin_eq_leaf_specX (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch,
pin_pre_kit STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch T_leaf_STK EV_leaf ->
getr regs 10 = getr regs 11 ->
SRr segs W (cfg_at segs a regs memc mdc)
(pin_post_simple STK sp0 FP ly S W0 mem0 md0 own k regs T_leaf_STK EV_leaf
 (fun _ => False) (fun _ _ _ => True) lyc Sc W memc mdc).
Definition tpin_check_row_specX (a : Z) : Prop := tpin_eq_leaf_specX a.
Definition tpin_check_label_specX (a : Z) : Prop := tpin_eq_leaf_specX a.

(* ============================== reac_box_catalogue (CA1) ============================== *)
Definition tpin_catalogue_specX (a cat : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch (c : Z) (cid pos : Z),
pin_pre_kit STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch T_leaf_STK EV_leaf ->
getr regs 10 = w64 c -> c <> 0 -> c mod 8 = 0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= c -> c + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
(spZ regs <= c \/ c + 8 <= spZ regs - T_leaf_STK) ->
afobj segs B lyc Sc W memc c 8 ->
SRr segs W (cfg_at segs a regs memc mdc)
(pin_post_simple STK sp0 FP ly S W0 mem0 md0 own k regs T_leaf_STK EV_leaf
 (fun x => c <= x < c + 8)
 (fun regs2 mem2 W2 => getr regs2 10 = w64 cat /\ val_mem segs (mrestrict (w_H W2) mem2) c 8%nat 11)
 lyc Sc W memc mdc).

(* ============================== fuzz_catalogue_row (CT1) ============================== *)
Definition tpin_row_specX (a cat : Z) (TP DP : nat -> Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
(sa n : Z) (sb : list byte),
pin_pre_kit STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch T_row_STK EV_row ->
getr regs 10 = w64 sa -> getr regs 11 = w64 n ->
n = Z.of_nat (length sb) -> 0 <= n < 2 ^ 32 -> 0 < sa -> sa + n <= 2 ^ 63 ->
garr8 segs (mrestrict (w_H W) memc) sa (pin_zbytes sb) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF sa n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memc) sa n) ->
amem_range sa n ->
(forall x, sa <= x < sa + n -> ~ (spZ regs - T_row_STK <= x < spZ regs)) ->
pin_cat_ok (mrestrict (w_H W) memc) (aview segs (w_H W) memc) cat TP DP ->
pin_cat_off_stack cat TP regs T_row_STK ->
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) ->
SRr segs W (cfg_at segs a regs memc mdc)
(pin_post_simple STK sp0 FP ly S W0 mem0 md0 own k regs T_row_STK EV_row
 (fun _ => False) (fun regs2 _ _ => getr regs2 10 = w64 (row_ptr cat sb)) lyc Sc W memc mdc).

(* ============================== reac_box_pin_parse (CP1) ==============================
   The post has knock's four memory clauses, because the function takes a frame of class 0 on the side
   stack for frames and gives it back inside the call: a caller cannot name that frame, so the one-clause
   form of the five other contracts would be false of its shadow bytes and its flag byte. *)
Definition pin_post_parse (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(cat : Z) (DP : nat -> Z) (sa mo lb : Z) (s : list byte)
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
: world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_parse) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
 ~ (spZ regs - T_parse_STK <= a < spZ regs) -> ~ pin_out_cell mo lb a ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
 aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
 (in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
 ~ pin_out_cell mo lb a ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
 ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
getr regs2 10 = w64 (parse_rc (pin_parse_res cat DP sa mo lb s)) /\
(forall row lab, pin_parse_res cat DP sa mo lb s = Some (row, lab) ->
 val_mem segs (mrestrict (w_H W2) mem2) mo 8%nat row /\ val_mem segs (mrestrict (w_H W2) mem2) lb 8%nat lab).

Definition tpin_parse_specX (a cat colonp : Z) (TP DP : nat -> Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
(sa mo lb : Z) (s : list byte) (cidm posm cidl posl : Z),
pin_pre_kit STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch T_parse_STK EV_parse ->
getr regs 10 = w64 sa -> getr regs 11 = w64 mo -> getr regs 12 = w64 lb ->
0 <= sa < 2 ^ 64 -> 0 <= mo < 2 ^ 64 -> 0 <= lb < 2 ^ 64 ->
(sa <> 0 -> pin_spec_str (mrestrict (w_H W) memc) (aview segs (w_H W) memc) regs T_parse_STK sa s /\
 exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= sa /\ sa + Z.of_nat (length s) + 1 <= b + req_size m) ->
(pin_parse_live sa mo lb = true ->
 mo mod 8 = 0 /\ lb mod 8 = 0 /\ (mo + 8 <= lb \/ lb + 8 <= mo) /\
 In (cidm, posm) own /\ 0 <= cidm /\ frame_addr lyc cidm posm mod 8 = 0 /\
 frame_addr lyc cidm posm <= mo /\ mo + 8 <= frame_addr lyc cidm posm + fs_frame_bytes cidm /\
 In (cidl, posl) own /\ 0 <= cidl /\ frame_addr lyc cidl posl mod 8 = 0 /\
 frame_addr lyc cidl posl <= lb /\ lb + 8 <= frame_addr lyc cidl posl + fs_frame_bytes cidl /\
 afobj segs B lyc Sc W memc mo 8 /\ afobj segs B lyc Sc W memc lb 8 /\
 (forall x, pin_out_cell mo lb x -> ~ (spZ regs - T_parse_STK <= x < spZ regs)) /\
 (forall x, pin_out_cell mo lb x -> ~ (sa <= x <= sa + Z.of_nat (length s)))) ->
pin_ro_str (mrestrict (w_H W) memc) (aview segs (w_H W) memc) colonp pin_colon_bytes ->
(forall x, colonp <= x <= colonp + 1 -> ~ (spZ regs - T_parse_STK <= x < spZ regs)) ->
pin_cat_ok (mrestrict (w_H W) memc) (aview segs (w_H W) memc) cat TP DP ->
pin_cat_off_stack cat TP regs T_parse_STK ->
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) ->
pin_ro_law cat TP DP colonp ->
count_cid 0 (frames Sc) < fs_frames 0 ->
SRr segs W (cfg_at segs a regs memc mdc)
(pin_post_parse STK sp0 FP ly S W0 mem0 md0 own k regs cat DP sa mo lb s lyc Sc W memc mdc).
(* How a walk consumes F-RO-LAW at a state its journal reaches: the journal's first conjunct is the
   allocator relation at that state. *)
Lemma pin_ro_law_at : forall cat TP DP colonp STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
pin_ro_law cat TP DP colonp ->
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) ->
pin_cat_ok (mrestrict (w_H W) memc) (aview segs (w_H W) memc) cat TP DP /\
pin_ro_str (mrestrict (w_H W) memc) (aview segs (w_H W) memc) colonp pin_colon_bytes.
Proof.
intros cat TP DP colonp STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HL HJ HR.
pose proof HJ as (HAR & _). exact (HL lyc Sc W memc mdc HAR HR).
Qed.
End d.

(* ============================== LLVMFuzzerTestOneInput (LIB1) ==============================
   ACfn's text (knock's lib/A/ACfn.v:27-73 at 6ebe35ba632) over abstract segs, sink and constants, as
   reac-pw/fuzz_qdisc's lib/A/QPgCSpec.v Section e states it. lib/A/PPgLib.v instantiates it at image A's
   constants; image B's twin instantiates it at its own. *)
Section e. Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Definition pin_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs)
(mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) /\
asink_none segs K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n).
Definition pin_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs)
(mem : word -> option byte) (md : Model) (p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte)
(md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs K (rd W' mem') md' /\
ameta_inv segs K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition pin_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (Kl : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
pin_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
pin_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (Kl l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) Kl).
End e.
End c.
End b.

(* The top claim is monotone in its event budget: pin's harness spends 2 events (one malloc and one free,
   lib/Reusable/YG01.v:452 and :460), and the core's donor text lib/A/ACfn.v carries a larger budget, so
   lib/A/PPgLib.v bridges the two with this lemma. A larger budget makes the start state's event clause
   stronger and the journal's clause weaker, so the contract at the smaller budget gives the larger one. *)
Lemma pin_lib_contract_x_ev_mono :
forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}
 (segs : list Segment) (B : asyms) (MT : ameter_ops) (K : asink_syms) (XM_LIB XN_LIB : Z -> Z)
 (RLO RHI A_LLVMF RA_LLVMF A_EMPTY EV EV' LIVE_LIB LLVMF_STK : Z),
EV <= EV' ->
pin_lib_contract_x segs B MT K XM_LIB XN_LIB RLO RHI A_LLVMF RA_LLVMF A_EMPTY EV LIVE_LIB LLVMF_STK ->
pin_lib_contract_x segs B MT K XM_LIB XN_LIB RLO RHI A_LLVMF RA_LLVMF A_EMPTY EV' LIVE_LIB LLVMF_STK.
Proof.
intros fx rc SK LS segs B MT K XM XN RLO RHI AL RA AE EV EV' LIVE STK Hle HX.
unfold pin_lib_contract_x in *.
intros ly S W regs mem md p n pl M Kl HAI HPRE HK.
apply (HX ly S W regs mem md p n pl M Kl HAI).
- unfold pin_lib_pre_x in *.
  destruct HPRE as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
  split; [exact P5|]. split; [exact P6|]. split; [exact P7|]. split; [exact P8|].
  split; [lia|]. split; [exact P10|]. split; [exact P11|]. split; [exact P12|].
  split; [exact P13|]. split; [exact P14|]. split; [exact P15 | exact P16].
- intros l W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Hc & HPOST).
  apply (HK l W' c' Hwle HAI').
  exists ly', S', regs', mem', md', k. split; [exact Hc|].
  unfold pin_lib_post_x in *.
  destruct HPOST as (Q1 & Q2 & Qrest).
  split; [exact Q1|]. split; [lia | exact Qrest].
Qed.
