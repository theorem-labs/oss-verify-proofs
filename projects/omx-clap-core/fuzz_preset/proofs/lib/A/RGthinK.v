(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinK.v (hub 66a127cb11e, blob b4a97a8df297) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025), module paths and every image numeral moved by symbol + offset; record, the internal file A5.md. *)
(* fuzz_preset.asan image A (pinned sha256 d83eb25dbf0df6d5...): the addresses of the realloc chain that the thin realloc
   segments run through, and the decode table of that code.

   Measured with capstone on the pinned image and the symbols of its unstripped twin (sha256 f0d2e8d40c7e3ed0...):
   - __wrap_realloc 0x5373c (`j 0x53b38`), ___interceptor_realloc 0x53b38 (118 instructions);
   - __asan::asan_realloc 0x32f40 (43 instructions), __asan::Allocator::Reallocate 0x32fec (88 instructions);
   - Allocator::Allocate 0x325b8, Allocator::Deallocate 0x322a4;
   - REAL(memcpy): the RELRO slot 0xa2038 holds 0xa3e88 (__interception::real_memcpy), whose word is 0x9b2b4
     (musl memcpy);
   - __sanitizer::SetErrnoToENOMEM 0x6d398 (8 instructions), __errno_location 0x8efd8 (3 instructions).
   The return pcs: Reallocate after Allocate 0x33058, after memcpy 0x330d0, after Deallocate 0x330ec;
   asan_realloc after Reallocate 0x32fdc, after its NULL-input Allocate 0x32fb8; the interceptor after asan_realloc
   0x53ce4.  The trace pc (the interceptor's second GetCurrentPc call, 0x53c70, on the long-unwind branch)
   returns to 0x53c74.

   ported from proofs/cgif/cgif_rgb_fuzzer/lib (cgif_rgb's released realloc family: YF6s-YF6u prefix (YF6s.v:449
   pa_arm), YF78.v:553 composition, memcpy step YF67.v:156 c1_copy over YF63.v:33 tfx_memcpy, the NULL-return arm
   YF68.v:104 c_null, the call bridges YF6o / YF6p) relocated to fuzz_reply's image; template msgpack-c
   AsanW/ARealloc_x.v:205.  cgif_rgb's asan-ubsan bodies of the interceptor, asan_realloc and Reallocate are
   instruction-for-instruction these, modulo pc-relative fields (cmpfunc, the internal file REALLOC-THIN-SEGMENTS.md). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
Open Scope Z_scope.

Definition RT_PCR : Z := 0x5373c.
Definition RT_ICPT : Z := 0x53b38.
Definition RT_PC0 : Z := 0x53c74.
Definition RT_AREALLOC : Z := 0x32f40.
Definition RT_REALLOCATE : Z := 0x32fec.
Definition RT_PCA : Z := 0x325b8.
Definition RT_PCD : Z := 0x322a4.
Definition RT_PCM : Z := 0x9b2b4.
Definition RT_RA_A : Z := 0x33058.
Definition RT_RA_M : Z := 0x330d0.
Definition RT_RA_D : Z := 0x330ec.
Definition RT_RA_R : Z := 0x32fdc.
Definition RT_RA_NA : Z := 0x32fb8.
Definition RT_RA_I : Z := 0x53ce4.
Definition RT_GOT_M : Z := 0xa2038.
Definition RT_REAL_M : Z := 0xa3e88.
Definition RT_INST : Z := 0xa7858.
Definition RT_OOM : Z := 0x12d120.
Definition RT_TP : Z := 0x5ddef0.
Definition RT_ERRNO : Z := 0x5dde4c.

(* The stack frames below realloc's entry sp, as offsets from it: the interceptor's (2032 bytes, then 112 more), the
   BufferedStackTrace object at -2136, asan_realloc's (16 bytes, its ra at -2152) and Reallocate's (48 bytes, its ra
   at -2168, s0..s4 at -2176..-2208).  Allocate and Deallocate are entered from Reallocate at sp - 2208; the
   NULL-input Allocate from asan_realloc at sp - 2160. *)
Definition RT_SO : Z := -2136.
Definition RT_SPR : Z := -2208.
Definition RT_SPN : Z := -2160.

Definition rt_tbl_build : ctable :=
build_table tfibsegs 0x32f40 131%nat (build_table tfibsegs 0x53b38 118%nat
(build_table tfibsegs 0x6d398 8%nat (build_table tfibsegs 0x8efd8 3%nat TEmpty))).
Definition rt_tbl : ctable := Eval vm_compute in rt_tbl_build.
Lemma rt_tbl_eq : rt_tbl = rt_tbl_build.
Proof. vm_cast_no_check (@eq_refl ctable rt_tbl). Qed.
Lemma rt_tbl_ok : table_ok tfibsegs rt_tbl.
Proof.
rewrite rt_tbl_eq. unfold rt_tbl_build.
do 3 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate.
Qed.
