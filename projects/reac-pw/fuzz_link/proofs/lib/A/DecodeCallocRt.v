(* libreac/fuzz_decode: the runtime-entry contracts the calloc walk consumes, at the addresses measured in this
   unit's two ASan images.  The walk of the calloc chain (the trampoline, ___interceptor_calloc and asan_calloc,
   lib/A/DecodeCallocTbl.v) steps through those three functions only; every function they call is taken as a
   contract.  Allocate's is a Theorem Labs lane's (lib/Reusable/YGAlloc.v).  This file states the other five, in the SRr leaf
   form cgif_file_fuzzer states its runtime entries (A/AFl0.v:22-56 tfib_unwind_spec, A/AFeq.v:141-161
   tfib_ialloc_spec), so that the walk takes them as hypotheses and another lane proves them:

     [unwind_specP]     __sanitizer::BufferedStackTrace::UnwindImpl  (the interceptor's A 0x545f8 `jal 0x5bfac`)
     [zero_fill_specP]  musl memset, reached through __interception::real_memset (asan_calloc A 0x32ebc `jalr a3`)
     [try_init_specP]   __asan::TryAsanInitFromRtl                   (the interceptor's A 0x54504 `jal 0x5b214`)
     [mcs_specP]        __asan::GetMallocContextSize                 (the interceptor's A 0x545b0 `jal 0x5bf9c`)
     [getpc_specP]      __sanitizer::StackTrace::GetCurrentPc        (the interceptor's A 0x5459c `jal 0x74b70`)

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
   | BufferedStackTrace::UnwindImpl (336 bytes, 84 insns)  | 0x5bfac   | 0x5bff8   | sym       | 0x5c4ec (AFl0.v:19 A_UnwindImpl) |
   | __asan::TryAsanInitFromRtl (160 bytes, 40 insns)      | 0x5b214   | 0x5b260   | sym       | 0x5b754   |
   | __asan::GetMallocContextSize (16 bytes, 4 insns)      | 0x5bf9c   | 0x5bfe8   | sym       | 0x5c4dc (AB1w.v:221) |
   | StackTrace::GetCurrentPc (8 bytes, 2 insns)           | 0x74b70   | 0x74bbc   | sym       | 0x74f9c (AB1w.v:411) |
   | musl memset (248 bytes, 62 insns)                     | 0x9afa8   | 0x9b5b0   | sym, image (the slot's content) | 0xa022c |
   | __asan::asan_inited (1 byte, .bss)                    | 0xab118   | 0xab698   | sym; code AsanInited+0x0/+0x4, TryAsanInitFromRtl+0xc/+0x10 | 0xb0358 |
   | __asan::tsd_key_inited (1 byte, .bss)                 | 0xa9ca0   | 0xaa220   | sym; code AsanTSDGet+0x0/+0x4 | 0xaeee0 |
   | __asan::tsd_key (4 bytes, .bss)                       | 0xa9ca4   | 0xaa224   | sym; code AsanTSDGet+0x10 `lw a0, 4(a0)` | 0xaeee4 |
   | GOT slot holding &PageSizeCached (.got)               | 0xa19b0   | 0xa1f58   | code UnwindFast+0x38/+0x3c; image | 0xa75f8 |
   | __sanitizer::PageSizeCached (8 bytes, .bss)           | 0x139ee0  | 0x13a460  | sym; image (the GOT slot's content) | 0x13f120 |
   | __asan::malloc_context_size (4 bytes, .bss)           | 0xab13c   | 0xab6bc   | sym; code GetMallocContextSize+0x0/+0x4 | 0xb037c (AB1w.v:587) |
   | GOT slot holding &real_memset (.got)                  | 0xa19f0   | 0xa1f98   | code asan_calloc+0x6c/+0x70; image | 0xa7638 (AE37.v:30-31) |
   | __interception::real_memset (8 bytes, .data)          | 0xa3850   | 0xa3df8   | sym; image (the GOT slot's content) | 0xa94a8 (AE37.v:33) |
   | GOT slot holding &common_flags_dont_use (.got)        | 0xa19c0   | 0xa1f68   | code ___interceptor_calloc+0xd4/+0xd8; image | 0xa7608 (AB1w.v:568) |
   | __sanitizer::common_flags_dont_use (288 bytes, .bss)  | 0x13bf68  | 0x13c4e8  | sym; image (the GOT slot's content) | 0x1411a8 |
   | builtin_tls (musl, 131280 bytes, .bss)                | 0x631b48  | 0x6320c8  | sym; code static_init_tls+0x1a0/+0x1b4 | 0x636d80 |
   | thread pointer tp of the main thread                  | 0x631c10  | 0x632190  | builtin_tls + 200, below | 0x636e48 (AF0m.v:12 TFIB_TP) |
   | __pthread_tsd_main (musl, 1024 bytes, .bss)           | 0x652fb8  | 0x5f5680  | sym; code __pthread_key_create+0x2c/+0x30, + 0x40 | 0x5fa338 (AF0m.v:12 TFIB_TSD) |

   THE THREAD POINTER.  tp is not a cell: start-up code computes it and puts it in register 4.  musl's
   static_init_tls (A 0x90764) takes mem = builtin_tls (A 0x883d4 `auipc a3, 0x54c` + 0x883e8 `addi a0, a3,
   -0x744` = 0x631b48; when the TLS size does not fit, A 0x883a0 .. 0x883c8 writes a message and halts, so there is
   no other arm), forms
   the thread descriptor td = mem + ((tls_align - 1) & (-200 - mem)) (A 0x883e0 .. 0x883f8, with 0x883e4 `addi a5,
   zero, -0xc8`), and sets tp = td + 200 (A 0x88408 `addi s0, s2, 0xc8`, A 0x88464 `jal 0x9d22c <__set_thread_area>`,
   whose first instruction is A 0x9d22c `mv tp, a0`).  tls_align = max (PT_TLS p_align, 8) (A 0x88374 / 0x88378 make
   it 8 when it is below 8); PT_TLS p_align is 8 in both images, and builtin_tls is a multiple of 8 in both, so
   td = builtin_tls and tp = builtin_tls + 200.  The same rule gives cgif's TFIB_TP: 0x636d80 + 200 = 0x636e48.
   tp - 88 is td->tsd: musl's __pthread_getspecific (A 0x9c8ac `mv a1, tp`, 0x9c8b0 `ld a1, -0x58(a1)`) reads it and
   __pthread_key_create stores __pthread_tsd_main there when it is 0 (A 0x9cc78 .. 0x9cc7c, 0x9cd18 `addi a1, s4,
   0x40`, 0x9cd1c `sd a1, -0x58(a0)`, s4 = 0x652f78 from A 0x9cc80 / 0x9cc84).

   NO DECODE CELL WITHOUT A CGIF COUNTERPART, AND THE REVERSE.  Each of cgif's per-image cells in tfib_unwind_spec
   (0xb0358, 0xaeee0, 0xaeee4, TFIB_TP, TFIB_TSD, 0xa75f8, 0x13f120) has the decode counterpart of the same symbol
   in the table; the offsets inside the thread objects (C + 152, T + 8, T + 16, T + 40, T + t_unwinding = T + 0xc60)
   and BufferedStackTrace's layout are the same in decode, read from decode's own code (below).

   The brief named 0xa3850 as "the real_memset GOT slot".  It is the variable __interception::real_memset itself
   (.data, sym), whose image content is musl memset 0x9afa8.  asan_calloc reaches it in two loads: A 0x32ea4 `auipc
   a1, 0x67` + 0x32ea8 `ld a1, 0x120(a1)` read the GOT slot 0xa19f0 (content 0xa3850), and 0x32eac `ld a3, 0(a1)`
   reads 0xa3850 (content 0x9afa8); 0x32ebc `jalr a3`.  lib/Reusable/YGCalloc.v's table row for the memset calls
   0xa3850 the GOT slot; the row should name 0xa19f0 as the slot and 0xa3850 as the variable.  A scan of image A's
   whole .text for every auipc pair that forms 0xa19f0 or 0xa3850 found 33 sites, each followed by loads only
   (no store through the loaded pointer within the next seven instructions), so no code in the image writes
   real_memset; its value at the call is the image's unless start-up code outside .text writes it, which the walk's
   premise on the cell covers either way.

   STACK BYTES.  UNW_STK = 144 is decode's own: UnwindImpl takes 0x50 (A 0x5bfac `addi sp, sp, -0x50`) and calls
   BufferedStackTrace::Unwind (A 0x5c0c4 `jal 0x751d4`), which takes 0x40 (A 0x751d4) and on the fast arm pops it
   and tail-jumps to UnwindFast (A 0x752e8 `j 0x74b78`), which takes 0x40 (A 0x74b78): 0x50 + 0x40 = 144.  The other
   callees take less: GetCurrentThread 0x10 (A 0x5da14) with AsanTSDGet tail-jumping to __pthread_getspecific
   (A 0x56324 `j 0x9c8ac`), which takes none; AsanInited, stack_top and stack_bottom take none on the arm the
   premises select (A 0x5dbe0 / 0x5dc38 `beqz a1` when T + 40 is 0).  BST_SIZE = 2064 is decode's own: the trace
   buffer starts at this + 0x10 (UnwindFast A 0x74bcc `sd a1, 0x10(a0)`) and top_frame_bp is at this + 0x808 =
   2056 (Unwind A 0x751fc `addi t0, a0, 0x7ff` + 0x7520c `sd t1, 9(t0)`), so 2056 + 8 = 2064.  Image B's UnwindImpl,
   GetCurrentThread, stack_top, stack_bottom, Unwind and GetCurrentPc are image A's bytes word for word at +0x4c;
   UnwindFast, AsanTSDGet, AsanInited, TryAsanInitFromRtl and GetMallocContextSize differ only in the words that
   form data addresses, and AsanTSDGet also in its tail jump to __pthread_getspecific (A 0x56324), whose target
   moves with musl's code; memset and __pthread_getspecific are the same bytes at +0x5a8.  Checked with
   measure_rt2.py (output rt/meas_rt2.txt beside it). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YM05 YK04 YI04 YO0d YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import DecodeCallocKit.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------
   Image A (fuzz_decode.asan). *)
Definition DEC_A_UnwindImpl : Z := 0x5bfac.
Definition DEC_A_TryAsanInitFromRtl : Z := 0x5b214.
Definition DEC_A_GetMallocContextSize : Z := 0x5bf9c.
Definition DEC_A_GetCurrentPc : Z := 0x74b70.
Definition DEC_A_memset : Z := 0x9afa8.
Definition DEC_A_asan_inited : Z := 0xab118.
Definition DEC_A_tsd_key_inited : Z := 0xa9ca0.
Definition DEC_A_tsd_key : Z := 0xa9ca4.
Definition DEC_A_got_page_size : Z := 0xa19b0.
Definition DEC_A_page_size_cached : Z := 0x139ee0.
Definition DEC_A_malloc_context_size : Z := 0xab13c.
Definition DEC_A_got_real_memset : Z := 0xa19f0.
Definition DEC_A_real_memset : Z := 0xa3850.
Definition DEC_A_got_common_flags : Z := 0xa19c0.
Definition DEC_A_common_flags : Z := 0x13bf68.
Definition DEC_A_builtin_tls : Z := 0x631b48.
Definition DEC_A_TP : Z := DEC_A_builtin_tls + PTHREAD_SIZE.
Definition DEC_A_TSD : Z := 0x652fb8.

Lemma DEC_A_TP_val : DEC_A_TP = 0x631c10. Proof. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ============================================================================================================
   The instances at the two images. *)
Definition decode_unwind_spec_A : Prop :=
unwind_specP tfibsegs DEC_A_UnwindImpl DEC_A_TP DEC_A_TSD DEC_A_asan_inited DEC_A_tsd_key_inited DEC_A_tsd_key
DEC_A_got_page_size DEC_A_page_size_cached.
Definition decode_zero_fill_spec_A (B : asyms) : Prop := zero_fill_specP tfibsegs B DEC_A_memset.
Definition decode_try_init_spec_A : Prop := try_init_specP tfibsegs DEC_A_TryAsanInitFromRtl DEC_A_asan_inited.
Definition decode_mcs_spec_A : Prop := mcs_specP tfibsegs DEC_A_GetMallocContextSize DEC_A_malloc_context_size.
Definition decode_getpc_spec_A : Prop := getpc_specP tfibsegs DEC_A_GetCurrentPc.

(* ============================================================================================================
   The facts the image settles.  [img_cell segs a n v]: the image's own bytes at [a, a + n) are v, little-endian
   ([mbyte] of the empty memory is [seg_rom], the loaded segment's byte).  Each is decided by [vm_compute] against the
   image module, through YCbq.v:2452 val_mem_of_rdword.  The four cells are the static ones the contracts and the
   walk read through: the GOT slot UnwindFast loads PageSizeCached's address from (premise [got_ps] of
   [unwind_specP]), the GOT slot and the variable asan_calloc loads the fill's target from (the pc of
   [zero_fill_specP]), and the GOT slot the interceptor loads common_flags_dont_use's address from (the byte at
   + CF_FAST_UNWIND_ON_MALLOC is [unwind_specP]'s a4).  The cells they point at are .bss, written by start-up code. *)
Lemma dec_A_got_page_size_val : img_cell tfibsegs DEC_A_got_page_size 8 DEC_A_page_size_cached.
Proof. apply img_cell_of_rdword. vm_compute. reflexivity. Qed.
Lemma dec_A_got_real_memset_val : img_cell tfibsegs DEC_A_got_real_memset 8 DEC_A_real_memset.
Proof. apply img_cell_of_rdword. vm_compute. reflexivity. Qed.
Lemma dec_A_real_memset_val : img_cell tfibsegs DEC_A_real_memset 8 DEC_A_memset.
Proof. apply img_cell_of_rdword. vm_compute. reflexivity. Qed.
Lemma dec_A_got_common_flags_val : img_cell tfibsegs DEC_A_got_common_flags 8 DEC_A_common_flags.
Proof. apply img_cell_of_rdword. vm_compute. reflexivity. Qed.
End d.
