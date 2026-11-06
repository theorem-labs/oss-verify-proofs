(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinK.v (commit 66a127cb11e, sha256 84c6a42dadb9; internal record, reply A text, no relocation); no other change. *)
(* fuzz_reply.asan (pinned sha256 42c58610e125e0b4...): the addresses of the realloc chain that the thin realloc
   segments run through, and the decode table of that code.

   Measured with capstone on the pinned image and the symbols of its unstripped twin (sha256 d751b179ea493ead...):
   - __wrap_realloc 0x53df0 (`j 0x541ec`), ___interceptor_realloc 0x541ec (118 instructions);
   - __asan::asan_realloc 0x32560 (43 instructions), __asan::Allocator::Reallocate 0x3260c (88 instructions);
   - Allocator::Allocate 0x31bd8, Allocator::Deallocate 0x318c4;
   - REAL(memcpy): the RELRO slot 0x9d9f8 holds 0x9f868 (__interception::real_memcpy), whose word is 0x964cc
     (musl memcpy);
   - __sanitizer::SetErrnoToENOMEM 0x6e0a4 (8 instructions), __errno_location 0x8c9a8 (3 instructions).
   The return pcs: Reallocate after Allocate 0x32678, after memcpy 0x326f0, after Deallocate 0x3270c;
   asan_realloc after Reallocate 0x325fc, after its NULL-input Allocate 0x325d8; the interceptor after asan_realloc
   0x54398.  The trace pc (the interceptor's second GetCurrentPc call, 0x54324, on the long-unwind branch)
   returns to 0x54328.

   ported from proofs/cgif/cgif_rgb_fuzzer/lib (cgif_rgb's released realloc family: YF6s-YF6u prefix (YF6s.v:449
   pa_arm), YF78.v:553 composition, memcpy step YF67.v:156 c1_copy over YF63.v:33 tfx_memcpy, the NULL-return arm
   YF68.v:104 c_null, the call bridges YF6o / YF6p) relocated to fuzz_reply's image; template msgpack-c
   AsanW/ARealloc_x.v:205.  cgif_rgb's asan-ubsan bodies of the interceptor, asan_realloc and Reallocate are
   instruction-for-instruction these, modulo pc-relative fields (cmpfunc, REALLOC-THIN-SEGMENTS.md (sha256 d8933f501ed8; internal record)). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
Open Scope Z_scope.

Definition RT_PCR : Z := 0x53df0.
Definition RT_ICPT : Z := 0x541ec.
Definition RT_PC0 : Z := 0x54328.
Definition RT_AREALLOC : Z := 0x32560.
Definition RT_REALLOCATE : Z := 0x3260c.
Definition RT_PCA : Z := 0x31bd8.
Definition RT_PCD : Z := 0x318c4.
Definition RT_PCM : Z := 0x964cc.
Definition RT_RA_A : Z := 0x32678.
Definition RT_RA_M : Z := 0x326f0.
Definition RT_RA_D : Z := 0x3270c.
Definition RT_RA_R : Z := 0x325fc.
Definition RT_RA_NA : Z := 0x325d8.
Definition RT_RA_I : Z := 0x54398.
Definition RT_GOT_M : Z := 0x9d9f8.
Definition RT_REAL_M : Z := 0x9f868.
Definition RT_INST : Z := 0xa2a58.
Definition RT_OOM : Z := 0x128320.
Definition RT_TP : Z := 0x5d9470.
Definition RT_ERRNO : Z := 0x5d93cc.

(* The stack frames below realloc's entry sp, as offsets from it: the interceptor's (2032 bytes, then 112 more), the
   BufferedStackTrace object at -2136, asan_realloc's (16 bytes, its ra at -2152) and Reallocate's (48 bytes, its ra
   at -2168, s0..s4 at -2176..-2208).  Allocate and Deallocate are entered from Reallocate at sp - 2208; the
   NULL-input Allocate from asan_realloc at sp - 2160. *)
Definition RT_SO : Z := -2136.
Definition RT_SPR : Z := -2208.
Definition RT_SPN : Z := -2160.

Definition rt_tbl_build : ctable :=
build_table tfibsegs 0x32560 131%nat (build_table tfibsegs 0x541ec 118%nat
(build_table tfibsegs 0x6e0a4 8%nat (build_table tfibsegs 0x8c9a8 3%nat TEmpty))).
Definition rt_tbl : ctable := Eval vm_compute in rt_tbl_build.
Lemma rt_tbl_eq : rt_tbl = rt_tbl_build.
Proof. vm_cast_no_check (@eq_refl ctable rt_tbl). Qed.
Lemma rt_tbl_ok : table_ok tfibsegs rt_tbl.
Proof.
rewrite rt_tbl_eq. unfold rt_tbl_build.
do 3 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate.
Qed.
