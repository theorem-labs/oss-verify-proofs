(* libreac/fuzz_decode: the image-independent half of lib/A/DecodeCalloc.v, lib/A/DecodeCallocRt.v and
   lib/A/DecodeCallocTbl.v, moved verbatim (owner ruling a Theorem Labs lane 01:47Z).  The three source headers follow; the image
   tables they describe stay in lib/A/DecodeCalloc{,Rt,Tbl}.v (image A) and lib/B/DecodeCalloc{,Rt,Tbl}.v (image B).
   The global Remove Hints of lib/A/DecodeCalloc.v is not here: it stays in lib/A/DecodeCalloc.v and is repeated in
   lib/B/DecodeCalloc.v, so that it reaches the same files as before the move (owner a Theorem Labs lane 02:24Z). *)
(* The header of lib/A/DecodeCalloc.v: *)
(* libreac/fuzz_decode's ASan calloc runtime contract: the unit-generic kit of lib/Reusable/YGCalloc.v at the
   addresses measured in this unit's two ASan images.  fuzz_decode is the only unit of the 14 whose ASYMS has
   as_calloc = Some 0x51f68: check_round_trip calls calloc, so its TFIB_T walk needs this contract where
   cgif_file_fuzzer's needs only malloc and free.

   Addresses (ORIGINAL binaries, FACTS f0e6eb38667, read with capstone from
   fuzz_decode.{asan,asan-ubsan};
   the twins' loaded PROGBITS equal the published, stripped pins of harness.yaml):

   |                                   | image A (.asan) | image B (.asan-ubsan) |
   |---|---|---|
   | __wrap_calloc / __interceptor_trampoline_calloc (4 bytes, `j`) | 0x51f68 | 0x51fb4 |
   | ___interceptor_calloc (368 bytes, 92 insns)                    | 0x52364 | 0x523b0 |
   | __asan::asan_calloc (224 bytes, 56 insns)                      | 0x31bd4 | 0x31c20 |
   | __asan::Allocator::Allocate (the callee calloc shares with malloc) | 0x3124c | 0x31298 |
   | pc the allocation's stack trace records (ra of GetCurrentPc, interceptor + 0xd4) | 0x52438 | 0x52484 |
   | __sanitizer::allocator_may_return_null (1 byte, .bss)          | 0x123021 | 0x1235a1 |
   | __sanitizer::allocator_out_of_memory (1 byte, .bss; the Allocate statement's oomb) | 0x123020 | 0x1235a0 |
   | __asan::instance (3632 bytes, a0 of Allocate)                  | 0x9d758 | 0x9dcd8 |
   | loaded image (PT_LOAD) lo .. end                               | 0x10000 .. 0x5f5638 | 0x10000 .. 0x5f5bb8 |

   Image B's calloc chain is image A's, moved by +0x4c: the trampoline, the interceptor and the entry have the
   same sizes and the same bytes word for word except three lo12 immediates that name data, which the two images
   place differently (A 0x5243c the flags pointer load, A 0x31c08 the `addi` that forms &instance, A 0x31c44 the
   `real_memset` GOT load; B's are at +0x4c).  The two tables above were read out of each binary separately.

   The contract is stated here over an [asyms] record [B] of the image, as the unit's TFIB_T walk will take it:
   the kit's predicates are the allocator model's (lib/Reusable/YG0d.v), the image's segments are
   lib/A/AB1v.v's [tfibsegs] / [decodesegsB0], and the Allocate contract the walk consumes is
   M1 (lib/Reusable/YGAlloc.v, the by-path copy of AllocG.v) at this image's Allocate pc, allocator instance and
   out-of-memory byte, with the call site's a2 = 8, a4 = 1 and a5 = 0.  The call
   rule is instantiated at this unit's own walk layer: YCbq.v:349 ajournal and YCbq.v:823 acall_kept, with the
   meter YC5d.v:17-20 ameter_ops left as the parameter [MT] that cgif's own rule carries (cgif instantiates it at
   ameter_triv, YCbp.v:17).

   THE CALL SITE.  The whole image calls the trampoline 0x51f68 once: check_round_trip (0x80bc8) at 0x80c4c
   `jal 0x51f68`, with
     a1 (sz) = 1       : 0x80c48 `addi a1, zero, 1`, a constant;
     a0 (nm) = s4      : 0x80c3c `mv a0, s4`, where 0x80c18 `mul s7, a3, a2`, 0x80c1c `slli s4, s7, 1`,
                         0x80c20 `add s4, s4, s7`, so nm = 3 * (a3 * a2); or nm = 1 when s7 = 0
                         (0x80c40 `bnez s7, 0x80c48`, 0x80c44 `addi a0, zero, 1`).
   (The two calls just before it, 0x80c28 and 0x80c34, go to the malloc trampoline 0x51f64.)  In image B the one
   call site is 0x80de4, inside check_round_trip 0x80d54.

   The seven runtime addresses of the table above were checked pair by pair with a Theorem Labs lane's port_addr_check.py
   (A against B): 8 SAME-SYMBOL, and one DIFFERENT-SYMBOL on the call site
   alone (check_round_trip + 0x84 against + 0x90), which is the harness-code difference just named, not a port
   error.

   NO OVERFLOW ARM FOR THIS UNIT.  The kit's [acalloc_overflow_realizesP] returns NULL with errno = ENOMEM only
   under the premise that the runtime's allocator_may_return_null byte is not zero at the call
   (A 0x5df50 `auipc` + 0x5df54 `lb a0, 0xd1(a0)` + 0x5df58 `snez a0, a0`, the byte 0x123021).  That byte is
   .bss: it is 0 in the image and start-up writes it from the harness's __asan_default_options (A 0x7fbb8
   returns the string at 0x1dcdf, "allocator_may_return_null=1"), so its value at the call is a START-UP fact,
   which this unit's start-up certificate does not yet carry.  It is therefore NOT provably 1 here, and this file
   instantiates no overflow arm: it does not need one, because the single call site above passes the constant
   sz = 1, so nm * sz = nm < 2 ^ 64 refutes the arm's premise outright.  The same holds for Allocate's
   allocation-size-too-big path (inside Allocate, A 0x31458 `slli a0, a1, 0x28` = 2 ^ 40, A 0x31460 / 0x31464,
   A 0x31470): nm = 3 * a3 * a2 is bounded by the program's constants, far below both 2 ^ 28 (the in-range arm's
   room premise) and 2 ^ 40.

   HOW THE WALK DISCHARGES REFUSAL.  As cgif discharges malloc's (A/AD1n.v:24-34 tfib_malloc_site): the room
   premises 0 <= n < MALLOC_MAX and blocks_bytes S + n <= LIVE_MAX at n = nm * sz = 3 * a3 * a2 feed
   YG0d.v:526-527 ml_malloc_ns (fst r = PNull -> ns = false), whose ns is forced true by the granted flag of
   YG0d.v:184 amreal_SRr04 (YG0d.v:173 last_flag_true, :175 atok_apath_flag); a kernel answer of 0 ends the path
   as a refusal, not as a NULL return.  [decode_acalloc04_A] is that in call-rule form, with 4096 <= res. *)
(* The header of lib/A/DecodeCallocRt.v: *)
(* libreac/fuzz_decode: the runtime-entry contracts the calloc walk consumes, at the addresses measured in this
   unit's two ASan images.  The walk of the calloc chain (the trampoline, ___interceptor_calloc and asan_calloc,
   lib/A/DecodeCallocTbl.v) steps through those three functions only; every function they call is taken as a
   contract.  Allocate's is a Theorem Labs lane's (lib/Reusable/YGAlloc.v).  This file states the other five, in the SRr leaf
   form cgif_file_fuzzer states its runtime entries (A/AFl0.v:22-56 tfib_unwind_spec, A/AFeq.v:141-161
   tfib_ialloc_spec), so that the walk takes them as hypotheses and another lane proves them:

     [unwind_specP]     __sanitizer::BufferedStackTrace::UnwindImpl  (the interceptor's A 0x52490 `jal 0x59e44`)
     [zero_fill_specP]  musl memset, reached through __interception::real_memset (asan_calloc A 0x31c58 `jalr a3`)
     [try_init_specP]   __asan::TryAsanInitFromRtl                   (the interceptor's A 0x5239c `jal 0x590ac`)
     [mcs_specP]        __asan::GetMallocContextSize                 (the interceptor's A 0x52448 `jal 0x59e34`)
     [getpc_specP]      __sanitizer::StackTrace::GetCurrentPc        (the interceptor's A 0x52434 `jal 0x72a08`)

   Only facts this file can close are proved here: what the image's own bytes hold at the four 8-byte data cells
   the contracts and the walk read through ([dec_A_*_val], [dec_B_*_val], [vm_compute] against the image modules).
   Every other cell the contracts name is in .bss: it is 0 in the image and start-up code writes it, so its value at
   the call is a premise of the contract, which the walk discharges from the allocator relation or the start-up
   certificate.  No Axiom, Parameter or Admitted; the five contracts are Definitions of Props.

   ===============================================================================================================
   HOW EACH ADDRESS WAS MEASURED.  The ORIGINAL unstripped twins
   fuzz_decode.{asan,asan-ubsan}
   (image A = .asan, image B = .asan-ubsan; their loaded PROGBITS are the published pins, lib/A/DecodeCalloc.v):
   - "sym": the .symtab entry of that name, read with pyelftools;
   - "code": the address the named instruction pair forms (auipc + addi/ld/lw/lb), decoded from the image's words
     with capstone, which agrees with "sym" in every row where both are given;
   - "image": the 8 little-endian bytes the loaded segment holds there, read with pyelftools and proved below with
     [vm_compute] against the image module ([dec_A_*_val] / [dec_B_*_val]).
   cgif's column is cgif_file_fuzzer's image A (the image of A/AFl0.v, tfibsegs = A/AB1v.v Asan.M.loaded_segments),
   named by symbol from cgif_file_fuzzer.asan.recovered-syms.txt.

   | name (symbol)                                         | decode A  | decode B  | how       | cgif A    |
   |---|---|---|---|---|
   | BufferedStackTrace::UnwindImpl (336 bytes, 84 insns)  | 0x59e44   | 0x59e90   | sym       | 0x5a384 (AFl0.v:19 A_UnwindImpl) |
   | __asan::TryAsanInitFromRtl (160 bytes, 40 insns)      | 0x590ac   | 0x590f8   | sym       | 0x595ec   |
   | __asan::GetMallocContextSize (16 bytes, 4 insns)      | 0x59e34   | 0x59e80   | sym       | 0x5a374 (AB1w.v:221) |
   | StackTrace::GetCurrentPc (8 bytes, 2 insns)           | 0x72a08   | 0x72a54   | sym       | 0x72e34 (AB1w.v:411) |
   | musl memset (248 bytes, 62 insns)                     | 0x92474   | 0x92a1c   | sym, image (the slot's content) | 0x97698 |
   | __asan::asan_inited (1 byte, .bss)                    | 0xa1a98   | 0xa2018   | sym; code AsanInited+0x0/+0x4, TryAsanInitFromRtl+0xc/+0x10 | 0xa6cd8 |
   | __asan::tsd_key_inited (1 byte, .bss)                 | 0xa0620   | 0xa0ba0   | sym; code AsanTSDGet+0x0/+0x4 | 0xa5860 |
   | __asan::tsd_key (4 bytes, .bss)                       | 0xa0624   | 0xa0ba4   | sym; code AsanTSDGet+0x10 `lw a0, 4(a0)` | 0xa5864 |
   | GOT slot holding &PageSizeCached (.got)               | 0x98d20   | 0x992c8   | code UnwindFast+0x38/+0x3c; image | 0x9df78 |
   | __sanitizer::PageSizeCached (8 bytes, .bss)           | 0x130860  | 0x130de0  | sym; image (the GOT slot's content) | 0x135aa0 |
   | __asan::malloc_context_size (4 bytes, .bss)           | 0xa1abc   | 0xa203c   | sym; code GetMallocContextSize+0x0/+0x4 | 0xa6cfc (AB1w.v:587) |
   | GOT slot holding &real_memset (.got)                  | 0x98d60   | 0x99308   | code asan_calloc+0x6c/+0x70; image | 0x9dfb8 (AE37.v:30-31) |
   | __interception::real_memset (8 bytes, .data)          | 0x9abc0   | 0x9b168   | sym; image (the GOT slot's content) | 0x9fe28 (AE37.v:33) |
   | GOT slot holding &common_flags_dont_use (.got)        | 0x98d30   | 0x992d8   | code ___interceptor_calloc+0xd4/+0xd8; image | 0x9df88 (AB1w.v:568) |
   | __sanitizer::common_flags_dont_use (288 bytes, .bss)  | 0x1328e8  | 0x132e68  | sym; image (the GOT slot's content) | 0x137b28 |
   | builtin_tls (musl, 131280 bytes, .bss)                | 0x5d3c90  | 0x5d4210  | sym; code static_init_tls+0x1a0/+0x1b4 | 0x5d8ec8 |
   | thread pointer tp of the main thread                  | 0x5d3d58  | 0x5d42d8  | builtin_tls + 200, below | 0x5d8f90 (AF0m.v:12 TFIB_TP) |
   | __pthread_tsd_main (musl, 1024 bytes, .bss)           | 0x5f5100  | 0x5f5680  | sym; code __pthread_key_create+0x2c/+0x30, + 0x40 | 0x5fa338 (AF0m.v:12 TFIB_TSD) |

   THE THREAD POINTER.  tp is not a cell: start-up code computes it and puts it in register 4.  musl's
   static_init_tls (A 0x88234) takes mem = builtin_tls (A 0x883d4 `auipc a3, 0x54c` + 0x883e8 `addi a0, a3,
   -0x744` = 0x5d3c90; when the TLS size does not fit, A 0x883a0 .. 0x883c8 writes a message and halts, so there is
   no other arm), forms
   the thread descriptor td = mem + ((tls_align - 1) & (-200 - mem)) (A 0x883e0 .. 0x883f8, with 0x883e4 `addi a5,
   zero, -0xc8`), and sets tp = td + 200 (A 0x88408 `addi s0, s2, 0xc8`, A 0x88464 `jal 0x94698 <__set_thread_area>`,
   whose first instruction is A 0x94698 `mv tp, a0`).  tls_align = max (PT_TLS p_align, 8) (A 0x88374 / 0x88378 make
   it 8 when it is below 8); PT_TLS p_align is 8 in both images, and builtin_tls is a multiple of 8 in both, so
   td = builtin_tls and tp = builtin_tls + 200.  The same rule gives cgif's TFIB_TP: 0x5d8ec8 + 200 = 0x5d8f90.
   tp - 88 is td->tsd: musl's __pthread_getspecific (A 0x93d18 `mv a1, tp`, 0x93d1c `ld a1, -0x58(a1)`) reads it and
   __pthread_key_create stores __pthread_tsd_main there when it is 0 (A 0x940e4 .. 0x940e8, 0x94184 `addi a1, s4,
   0x40`, 0x94188 `sd a1, -0x58(a0)`, s4 = 0x5f50c0 from A 0x940ec / 0x940f0).

   NO DECODE CELL WITHOUT A CGIF COUNTERPART, AND THE REVERSE.  Each of cgif's per-image cells in tfib_unwind_spec
   (0xa6cd8, 0xa5860, 0xa5864, TFIB_TP, TFIB_TSD, 0x9df78, 0x135aa0) has the decode counterpart of the same symbol
   in the table; the offsets inside the thread objects (C + 152, T + 8, T + 16, T + 40, T + t_unwinding = T + 0xc60)
   and BufferedStackTrace's layout are the same in decode, read from decode's own code (below).

   The brief named 0x9abc0 as "the real_memset GOT slot".  It is the variable __interception::real_memset itself
   (.data, sym), whose image content is musl memset 0x92474.  asan_calloc reaches it in two loads: A 0x31c40 `auipc
   a1, 0x67` + 0x31c44 `ld a1, 0x120(a1)` read the GOT slot 0x98d60 (content 0x9abc0), and 0x31c48 `ld a3, 0(a1)`
   reads 0x9abc0 (content 0x92474); 0x31c58 `jalr a3`.  lib/Reusable/YGCalloc.v's table row for the memset calls
   0x9abc0 the GOT slot; the row should name 0x98d60 as the slot and 0x9abc0 as the variable.  A scan of image A's
   whole .text for every auipc pair that forms 0x98d60 or 0x9abc0 found 33 sites, each followed by loads only
   (no store through the loaded pointer within the next seven instructions), so no code in the image writes
   real_memset; its value at the call is the image's unless start-up code outside .text writes it, which the walk's
   premise on the cell covers either way.

   STACK BYTES.  UNW_STK = 144 is decode's own: UnwindImpl takes 0x50 (A 0x59e44 `addi sp, sp, -0x50`) and calls
   BufferedStackTrace::Unwind (A 0x59f5c `jal 0x7306c`), which takes 0x40 (A 0x7306c) and on the fast arm pops it
   and tail-jumps to UnwindFast (A 0x73180 `j 0x72a10`), which takes 0x40 (A 0x72a10): 0x50 + 0x40 = 144.  The other
   callees take less: GetCurrentThread 0x10 (A 0x5b8ac) with AsanTSDGet tail-jumping to __pthread_getspecific
   (A 0x541bc `j 0x93d18`), which takes none; AsanInited, stack_top and stack_bottom take none on the arm the
   premises select (A 0x5ba78 / 0x5bad0 `beqz a1` when T + 40 is 0).  BST_SIZE = 2064 is decode's own: the trace
   buffer starts at this + 0x10 (UnwindFast A 0x72a64 `sd a1, 0x10(a0)`) and top_frame_bp is at this + 0x808 =
   2056 (Unwind A 0x73094 `addi t0, a0, 0x7ff` + 0x730a4 `sd t1, 9(t0)`), so 2056 + 8 = 2064.  Image B's UnwindImpl,
   GetCurrentThread, stack_top, stack_bottom, Unwind and GetCurrentPc are image A's bytes word for word at +0x4c;
   UnwindFast, AsanTSDGet, AsanInited, TryAsanInitFromRtl and GetMallocContextSize differ only in the words that
   form data addresses, and AsanTSDGet also in its tail jump to __pthread_getspecific (A 0x541bc), whose target
   moves with musl's code; memset and __pthread_getspecific are the same bytes at +0x5a8.  Checked with
   measure_rt2.py (output rt/meas_rt2.txt beside it). *)
(* The header of lib/A/DecodeCallocTbl.v: *)
(* The decoded instruction table of libreac/fuzz_decode's calloc chain, for the walk of
   lib/A/DecodeCallocWalk.v: the trampoline, ___interceptor_calloc and __asan::asan_calloc of each ASan image.
   The words are read out of the image itself ([build_table] over the unit's loaded segments, [Eval vm_compute]),
   so no instruction word is written here; [table_ok] says every entry is the image's word at that pc.

   Ranges (start, instruction count), measured with capstone on the ORIGINAL unstripped binaries
   (fuzz_decode.asan and fuzz_decode.asan-ubsan), and matched to the symbol
   table (lib/A/DecodeCalloc.v's address table):
     image A: 0x51f68 (1), 0x52364 (92), 0x31bd4 (56)
     image B: 0x51fb4 (1), 0x523b0 (92), 0x31c20 (56)
   The callees the walk does not step through (TryAsanInitFromRtl, GetMallocContextSize, GetCurrentPc,
   UnwindImpl, Allocate, real_memset, SetErrnoToENOMEM) are not in the table: the walk uses their contracts. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YM05 YA0n YG00 YG0f YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq YC5d.
Import ListNotations.
Open Scope Z_scope.

(* The size bound of this unit's calloc calls, the [cmax] of the kit's contract (which needs cmax <= PRIM_MAX =
   64512, so that every covered request is a primary one).  reac-pw/fuzz_link image A calls calloc twice, both in
   LLVMFuzzerTestOneInput with constant arguments: 0x82c74 `jal 0x540d0` with a0 = 1 (0x82c70) and a1 = 0x2298 = 8856
   (0x82c68 `lui s4, 2`, 0x82c6c `addiw a1, s4, 0x298`), and 0x82c84 `jal 0x540d0` with a0 = 1 (0x82c7c) and
   a1 = 0x204 = 516 (0x82c80).  The larger request, 8856, is the bound stated. *)
Definition DEC_CALLOC_MAX : Z := 8856.
(* The call depth of the chain, the kit's [cdepth]: the wrapper's frame (0x52364 `addi sp, sp, -0x7f0` and
   0x5238c `addi sp, sp, -0x70`, 2144 bytes; image B 0x523b0 / 0x523d8 the same) plus asan_calloc's
   (0x31bd4 `addi sp, sp, -0x30`, 48 bytes; image B 0x31c20 the same) = 2192, the distance from the wrapper's
   entry sp to Allocate's entry sp. *)
Definition DEC_CALLOC_DEPTH : Z := 2192.
Lemma DEC_CALLOC_MAX_prim : DEC_CALLOC_MAX <= PRIM_MAX.
Proof. unfold DEC_CALLOC_MAX, PRIM_MAX. lia. Qed.

(* The image-independent half of lib/A/DecodeCallocRt.v, under that file's own Requires (re-imported here so that
   its names resolve as they did there). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YM05 YK04 YI04 YO0d YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop YCbq.
Import ListNotations.
Open Scope Z_scope.

(* The size of musl's struct pthread on riscv64: static_init_tls A 0x883e4 `addi a5, zero, -0xc8` and A 0x88408
   `addi s0, s2, 0xc8` (also __copy_tls A 0x88180 / 0x881bc). *)
Definition PTHREAD_SIZE : Z := 200.
(* tp - TSD_OFF holds the thread's tsd array: __pthread_getspecific A 0x93d1c `ld a1, -0x58(a1)`. *)
Definition TSD_OFF : Z := 88.
(* The stack bytes below sp each contract may write (see the header). *)
Definition UNW_STK : Z := 144.
Definition BST_SIZE : Z := 2064.
(* TryAsanInitFromRtl: A 0x590ac `addi sp, sp, -0x10`, A 0x590b0 `sd ra, 8(sp)`, A 0x590b4 `sd s0, 0(sp)`. *)
Definition TAI_STK : Z := 16.
(* The byte of common_flags_dont_use the interceptor passes as UnwindImpl's request_fast (fast_unwind_on_malloc):
   ___interceptor_calloc A 0x52440 `lbu s4, 0x22(a1)`, A 0x5248c `mv a4, s4`. *)
Definition CF_FAST_UNWIND_ON_MALLOC : Z := 0x22.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* cgif's A/AF0x.v:53 img_cover at this unit's own image bounds (lib/Reusable/YImgTop.v, computed from both ASan
   images' loaded segments). *)
Definition dec_img_cover (ly : alayout) : Prop :=
fst (ly_img ly) <= YImgTop.IMG_LO /\ YImgTop.IMG_TOP <= fst (ly_img ly) + snd (ly_img ly).

(* ============================================================================================================
   1. THE UNWINDER.  cgif's A/AFl0.v:22-56 tfib_unwind_spec, premise for premise and conjunct for conjunct, with its
   seven per-image cells as parameters: [tp] (cgif TFIB_TP), [tsd] (TFIB_TSD), [c_inited] (0xa6cd8), [c_tki]
   (0xa5860), [c_tk] (0xa5864), [got_ps] (0x9df78), [c_ps] (0x135aa0); and its entry [pcU] (A_UnwindImpl).  cgif
   proves its instance (A/AFl4.v:1206 tfib_unwind_ok); that proof is the released text a decode proof ports.

   What decode's code reads and writes, for each premise and conjunct (image A; B is the same code at +0x4c):
   | premise / conjunct | decode's instructions |
   |---|---|
   | a0 = this, a1 = pc0, a2 = bp, a3 = 0, a4 = 1, a5 = 30 | the interceptor's call A 0x52478 .. 0x52490: a0 = s0 - 0x858, a1 = s3 (GetCurrentPc's a0), a2 = s0, a3 = 0, a4 = the fast_unwind_on_malloc byte, a5 = GetMallocContextSize's a0 |
   | asan_inited = 1 | A 0x59e8c `jal 0x5819c <AsanInited>`: A 0x5819c / 0x581a0 `lb a0, -0x704(a0)` = 0xa1a98, 0x581a8 / 0x581ac a0 = (byte = 1); A 0x59e90 `beqz a0` |
   | tsd_key_inited = 1, tsd_key = 0 | GetCurrentThread A 0x5b8b4 `jal 0x541a8 <AsanTSDGet>`: A 0x541a8 / 0x541ac a0 = 0xa0620, 0x541b0 `lbu a1, 0(a0)`, 0x541b4 `beqz a1` (the CHECK arm), 0x541b8 `lw a0, 4(a0)` (0xa0624), 0x541bc `j 0x93d18 <__pthread_getspecific>` |
   | tp, tp - 88 = tsd, tsd[0] = C | __pthread_getspecific A 0x93d18 `mv a1, tp`, 0x93d1c `ld a1, -0x58(a1)`, 0x93d20 .. 0x93d2c `ld a0, 8 * key(a1)` |
   | C + 152 = T | GetCurrentThread A 0x5b8bc `ld a0, 0x98(a0)` |
   | T + t_unwinding = 0, present, restored | A 0x59e9c `addi s8, a0, 0x7ff`, 0x59ea0 `lbu a1, 0x461(s8)` (0x7ff + 0x461 = 0xc60 = t_unwinding), 0x59ea8 `sb a2(=1), 0x461(s8)`, 0x59eac `bnez a1`; A 0x59f60 `sb zero, 0x461(s8)` |
   | T + 40 = 0, T + 8 = top, T + 16 = bot | stack_top A 0x5ba70 `lb a1, 0x28(a0)`, 0x5ba78 `beqz a1`, 0x5bab0 `ld a1, 8(a0)`, 0x5bab4 `ld a0, 0x10(a0)`; stack_bottom A 0x5bac8 .. 0x5bb1c the same cells |
   | got_ps holds c_ps, c_ps = 4096 | UnwindFast A 0x72a48 `auipc a3, 0x26` + 0x72a4c `ld s2, 0x2d8(a3)` (= the GOT slot 0x98d20), 0x72a50 `ld a3, 0(s2)` (PageSizeCached), 0x72a54 `beqz a3` (the GetPageSize arm, which would store at 0x72a98) |
   | the frame: [sp - 144, sp), this + 8 .. 12, this + 16 .. 16 + 8 * 30, this + 2056 .. 2064 | UnwindImpl A 0x59e88 `sw zero, 8(a0)`; Unwind A 0x730a4 `sd t1, 9(t0)` (this + 2056 = bp when max_depth <> 0); UnwindFast A 0x72a60 `sw a5, 8(a0)`, 0x72a64 `sd a1, 0x10(a0)`, 0x72aec `sw a5, 8(a0)`, 0x72af0 `sd a6, 0(a7)` (a7 = this + 0x10 + 8 * k, k < max_depth = 30); the stack stores of the three frames |
   | the trace: unwind_of_chain over the frame-pointer chain | UnwindFast A 0x72ad0 .. 0x72b08: the loop reads [bp - 8] (ra) and [bp - 16] (the next bp), skips ra = pc0 (A 0x72adc `beq a6, a1`), stops at max_depth, at a misaligned or out-of-range next bp, or at ra below the page size (A 0x72ad8 `bltu a6, a3`) |
   | callee-saved registers kept | the three frames restore ra, s0 .. s8 (A 0x59f64 .. 0x59f8c, 0x730c0 .. 0x730dc, 0x72b0c .. 0x72b28) | *)
Section u.
Variable segs : list Segment.
Variables (pcU tp tsd c_inited c_tki c_tk got_ps c_ps : Z).
Definition unwind_specP : Prop :=
forall (W : world segs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(this pc0 bp ra0 nfp0 : Z) (ch : list (Z * Z * Z)),
let H := w_H W in let m := mrestrict H mem in
let sp := bv_unsigned (YK11.getr regs 2) in let T := ly_T ly in
YG0f.layout_ok ly -> dec_img_cover ly ->
YK11.getr regs 10 = Z_to_bv 64 this -> YK11.getr regs 11 = Z_to_bv 64 pc0 -> YK11.getr regs 12 = Z_to_bv 64 bp ->
YK11.getr regs 13 = Z_to_bv 64 0 -> YK11.getr regs 14 = Z_to_bv 64 1 -> YK11.getr regs 15 = Z_to_bv 64 30 ->
YK11.getr regs 4 = Z_to_bv 64 tp -> YK0s.ret_ok (YK11.getr regs 1) -> 0 <= pc0 < 2 ^ 64 ->
val_mem segs m c_inited 1 1 -> val_mem segs m c_tki 1 1 -> val_mem segs m c_tk 4 0 ->
val_mem segs m (tp - TSD_OFF) 8 tsd -> val_mem segs m tsd 8 (ly_C ly) ->
val_mem segs m (ly_C ly + 152) 8 T -> val_mem segs m (T + 40) 1 0 ->
val_mem segs m (T + 8) 8 (ly_top ly) -> val_mem segs m (T + 16) 8 (ly_bot ly) ->
val_mem segs m (T + t_unwinding) 1 0 -> apresent H mem (T + t_unwinding) ->
val_mem segs m got_ps 8 c_ps -> val_mem segs m c_ps 8 4096 ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - UNW_STK -> (forall a, sp - UNW_STK <= a < sp -> apresent H mem a) ->
this mod 8 = 0 -> ly_stk_lo ly <= this -> this + BST_SIZE <= sp - UNW_STK \/ sp <= this ->
(forall a, this <= a < this + BST_SIZE -> apresent H mem a) ->
this + BST_SIZE <= bp - 16 -> sp <= bp - 16 -> ly_bot ly < bp -> bp <= ly_stk_hi ly -> bp mod 8 = 0 ->
rdword (aview segs H mem) (bp - 8) = Some ra0 -> rdword (aview segs H mem) (bp - 16) = Some nfp0 -> 4096 <= ra0 ->
(if bp + 16 <? ly_top ly
then (if bad_next bp (ly_top ly) nfp0 then ch = []
else bp + 16 <= nfp0 /\ fpchain (rdword (aview segs H mem)) nfp0 (ly_top ly) ch)
else ch = []) ->
SRr segs W (mkCfg (YK11.mkst regs (Z_to_bv 64 pcU) mem (YK11.seg_rom segs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
YO0d.regs_preserved regs regs' /\
(forall x : word, ~ (sp - UNW_STK <= bv_unsigned x < sp) -> ~ (this + 8 <= bv_unsigned x < this + 12) ->
~ (this + 16 <= bv_unsigned x < this + 16 + 8 * 30) -> ~ (this + 2056 <= bv_unsigned x < this + BST_SIZE) ->
mem' x = mem x) /\
(forall a, apresent H mem a -> apresent H mem' a) /\
let tr := if bp + 16 <? ly_top ly then unwind_of_chain pc0 ((bp, ra0, nfp0) :: ch) else [pc0] in
val_mem segs (mrestrict H mem') (this + 8) 4 (Z.of_nat (length tr)) /\
(forall i, (i < length tr)%nat -> val_mem segs (mrestrict H mem') (this + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
val_mem segs (mrestrict H mem') (this + 2056) 8 bp).
End u.

(* ============================================================================================================
   2. THE ZERO FILL.  The call asan_calloc makes through __interception::real_memset (A 0x31c40 .. 0x31c58: a0 = the
   block, a1 = 0, a2 = n = nm * sz, `jalr a3` with a3 = the slot's content) reaches musl memset, the slot's image
   content ([dec_A_real_memset_val]).  The contract is YG0d.v:318-336 [aintrin_realizes] at op = OSet, with its
   three shadow premises (amem_range, range_addressable, shadow_hull_vis) removed: those are what the checking entry
   __asan_memset needs, and musl memset reads no shadow byte.  Read in full (A 0x92474 .. 0x92568, 62 instructions):
   - it calls nothing and never touches sp (no instruction names sp);
   - it writes only [d, d + n): the byte stores 0x92478 .. 0x924ac at d + 0 .. 3 and d + n - 4 .. n - 1, the word
     stores 0x924dc .. 0x92530 and the 8-byte loop 0x9254c .. 0x92564 at addresses in [d, d + n) (the head and the
     tail are aligned inward, 0x924b4 .. 0x924d4);
   - every stored byte is a1 mod 256: the byte stores store a1's low byte; A 0x924b8 .. 0x924d8 form the word value as
     the high half of (a1 << 56) * 0x101010100, which is (a1 mod 256) * 0x01010101, and A 0x92538 .. 0x92544 widen
     it to 8 bytes;
   - a0 is never written, so it returns d; it returns with `ret` (A 0x92568) to the caller's ra, a1 .. a6 clobbered,
     every callee-saved register kept.
   The allocation leaf's block is not owned by the allocator ([aowned] excludes client bytes, YG0n.v:236-242), so
   [dest_ok] holds of it and the post keeps [AR]. *)
Section z.
Variable segs : list Segment.
Variable B : asyms.
Definition zero_fill_specP (pc : Z) : Prop :=
forall ly S W regs mem md d x n,
ecall_pre segs B ly S W regs mem md ->
YK11.getr regs 10 = w64 d -> YK11.getr regs 11 = w64 x -> YK11.getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d ->
d + n <= 2 ^ 63 ->
dest_ok segs B ly S W regs mem d n ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
YK11.getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End z.

(* ============================================================================================================
   3. THE THREE SMALL ENTRIES the interceptor calls before the allocator, in the leaf form of A/AFeq.v:141-161
   (SRr from the entry pc to the caller's ra, the world unchanged, callee-saved registers kept, a0 stated, memory
   framed). *)
Section s.
Variable segs : list Segment.

(* TryAsanInitFromRtl, at [pc], with the memory-checking runtime already initialized (the asan_inited byte
   [c_inited] is 1).  Instructions read (image A):
     0x590ac `addi sp, sp, -0x10`; 0x590b0 `sd ra, 8(sp)`; 0x590b4 `sd s0, 0(sp)`   (the only stores: [sp - 16, sp))
     0x590b8 `auipc a0, 0x49`; 0x590bc `addi s0, a0, -0x620`                          (s0 = 0xa1a98, asan_inited)
     0x590c0 `lb a1, 0(s0)`; 0x590c4 `addi a0, zero, 1`; 0x590c8 `fence r, rw`
     0x590cc `bne a1, a0, 0x590e0`                                                    (not taken when the byte is 1)
     0x590d0 `ld ra, 8(sp)`; 0x590d4 `ld s0, 0(sp)`; 0x590d8 `addi sp, sp, 0x10`; 0x590dc `ret`
   so it returns a0 = 1 (the interceptor's A 0x523a0 `beqz a0` then skips the DlsymAlloc arm), with s0 and sp
   restored.  The window premise keeps the two stores off the byte it reads. *)
Definition try_init_specP (pc c_inited : Z) : Prop :=
forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (YK11.getr regs 2) in
YK0s.ret_ok (YK11.getr regs 1) ->
sp mod 16 = 0 -> YImgTop.IMG_TOP <= sp - TAI_STK -> (forall a, sp - TAI_STK <= a < sp -> apresent H mem a) ->
val_mem segs m c_inited 1 1 ->
SRr segs W (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom segs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
YO0d.regs_preserved regs regs' /\ YK11.getr regs' 10 = Z_to_bv 64 1 /\
(forall x : word, ~ (sp - TAI_STK <= bv_unsigned x < sp) -> mem' x = mem x) /\
(forall a, apresent H mem a -> apresent H mem' a)).

(* GetMallocContextSize, at [pc], reading the 4-byte cell [c_mcs] (__asan::malloc_context_size).  Instructions read
   (image A):
     0x59e34 `auipc a0, 0x48`; 0x59e38 `lw a0, -0x378(a0)`   (a0 = the sign-extended word at 0xa1abc)
     0x59e3c `fence r, rw`; 0x59e40 `ret`
   No stack, no store, only a0 written.  With 0 <= v < 2 ^ 31 the sign extension is v. *)
Definition mcs_specP (pc c_mcs : Z) : Prop :=
forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (v : Z),
let H := w_H W in let m := mrestrict H mem in
YK0s.ret_ok (YK11.getr regs 1) ->
val_mem segs m c_mcs 4 v -> 0 <= v < 2 ^ 31 ->
SRr segs W (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom segs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
YO0d.regs_preserved regs regs' /\ YK11.getr regs' 10 = Z_to_bv 64 v /\
(forall x : word, mem' x = mem x)).

(* StackTrace::GetCurrentPc, at [pc].  Instructions read (image A):
     0x72a08 `mv a0, ra`; 0x72a0c `ret`
   so a0 = the caller's return address (at the interceptor's A 0x52434 `jal 0x72a08` that is A 0x52438, the pc the
   allocation's trace records, lib/A/DecodeCalloc.v DEC_A_calloc_ra0).  No stack, no store. *)
Definition getpc_specP (pc : Z) : Prop :=
forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
YK0s.ret_ok (YK11.getr regs 1) ->
SRr segs W (mkCfg (YK11.mkst regs (Z_to_bv 64 pc) mem (YK11.seg_rom segs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
YO0d.regs_preserved regs regs' /\ YK11.getr regs' 10 = YK11.getr regs 1 /\
(forall x : word, mem' x = mem x)).
End s.

(* ============================================================================================================
   The facts the image settles.  [img_cell segs a n v]: the image's own bytes at [a, a + n) are v, little-endian
   ([mbyte] of the empty memory is [seg_rom], the loaded segment's byte).  Each is decided by [vm_compute] against the
   image module, through YCbq.v:2452 val_mem_of_rdword.  The four cells are the static ones the contracts and the
   walk read through: the GOT slot UnwindFast loads PageSizeCached's address from (premise [got_ps] of
   [unwind_specP]), the GOT slot and the variable asan_calloc loads the fill's target from (the pc of
   [zero_fill_specP]), and the GOT slot the interceptor loads common_flags_dont_use's address from (the byte at
   + CF_FAST_UNWIND_ON_MALLOC is [unwind_specP]'s a4).  The cells they point at are .bss, written by start-up code. *)
Definition img_cell (segs : list Segment) (a : Z) (n : nat) (v : Z) : Prop :=
val_mem segs (fun _ : word => @None byte) a n v.

Lemma img_cell_of_rdword : forall segs a v,
rdword (aview segs (fun _ : word => false) (fun _ : word => @None byte)) a = Some v -> img_cell segs a 8 v.
Proof.
intros segs a v Hw. exact (YCbq.val_mem_of_rdword segs (fun _ : word => false) (fun _ : word => @None byte) a v Hw).
Qed.

End d.

(* The image-independent half of lib/A/DecodeCallocTbl.v, under that file's own Requires (re-imported here so that
   its names resolve as they did there). *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP02.
Import ListNotations.
Open Scope Z_scope.

Fixpoint build_ranges (segs : list Segment) (rs : list (Z * nat)) (t : ctable) : ctable :=
match rs with [] => t | (lo, n) :: rest => build_ranges segs rest (build_table segs lo n t) end.
Lemma build_ranges_ok : forall segs rs t,
Forall (fun r => 0 <= fst r) rs -> table_ok segs t -> table_ok segs (build_ranges segs rs t).
Proof.
induction rs as [|[lo n] rest IH]; intros t Hrs Ht; cbn; [exact Ht|].
inversion Hrs; subst. apply IH; [assumption|]. apply build_table_ok; [cbn in *; assumption | exact Ht].
Qed.
