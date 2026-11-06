(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinK.v at commit 6ea216c338f as lib/B/RGthinK.v, with its module paths changed (lib.A to lib.B, except the image-free ADIfaceImgA and the one params file CfParamsReply; the image twins A<r> to Y<r>, CfImgA / CfImg_A to CfImgB / CfImg_B, WrapAKit / WrapFreeA<x> to WrapBKit / WrapFreeB<x>, AFf0cfR to YFf0cfR, RGcfWalkA to RGcfWalkB with its three exported names wrap_realloc_walk_cf_A, wrap_realloc_null_walk_cf_A, wrap_realloc_walk_cf_rh_A to _B), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan by alreloc 6e5d1356c317 (44 numerals; per-numeral report). *)
(* Modified by a Theorem Labs lane (ReallocPrimary.RealSegA), 2026-10-30: from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinK.v (commit 66a127cb11e, sha256 84c6a42dadb9; internal record, reply A text, no relocation); no other change. *)
(* Image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a): every address in the next comment is image B's; an image it names is the image its text came from. *)
(* fuzz_reply.asan (pinned sha256 42c58610e125e0b4...): the addresses of the realloc chain that the thin realloc
   segments run through, and the decode table of that code.

   Measured with capstone on the pinned image and the symbols of its unstripped twin (sha256 d751b179ea493ead...):
   - __wrap_realloc 0x53e48 (`j 0x54244`), ___interceptor_realloc 0x54244 (118 instructions);
   - __asan::asan_realloc 0x325b8 (43 instructions), __asan::Allocator::Reallocate 0x32664 (88 instructions);
   - Allocator::Allocate 0x31c30, Allocator::Deallocate 0x3191c;
   - REAL(memcpy): the RELRO slot 0x9df78 holds 0x9fde8 (__interception::real_memcpy), whose word is 0x96a4c
     (musl memcpy);
   - __sanitizer::SetErrnoToENOMEM 0x6e0fc (8 instructions), __errno_location 0x8cf28 (3 instructions).
   The return pcs: Reallocate after Allocate 0x326d0, after memcpy 0x32748, after Deallocate 0x32764;
   asan_realloc after Reallocate 0x32654, after its NULL-input Allocate 0x32630; the interceptor after asan_realloc
   0x543f0.  The trace pc (the interceptor's second GetCurrentPc call, 0x5437c, on the long-unwind branch)
   returns to 0x54380.

   ported from proofs/cgif/cgif_rgb_fuzzer/lib (cgif_rgb's released realloc family: YF6s-YF6u prefix (YF6s.v:449
   pa_arm), YF78.v:553 composition, memcpy step YF67.v:156 c1_copy over YF63.v:33 tfx_memcpy, the NULL-return arm
   YF68.v:104 c_null, the call bridges YF6o / YF6p) relocated to fuzz_reply's image; template msgpack-c
   AsanW/ARealloc_x.v:205.  cgif_rgb's asan-ubsan bodies of the interceptor, asan_realloc and Reallocate are
   instruction-for-instruction these, modulo pc-relative fields (cmpfunc, REALLOC-THIN-SEGMENTS.md (sha256 d8933f501ed8; internal record)). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
Open Scope Z_scope.

Definition RT_PCR : Z := 0x53e48.
Definition RT_ICPT : Z := 0x54244.
Definition RT_PC0 : Z := 0x54380.
Definition RT_AREALLOC : Z := 0x325b8.
Definition RT_REALLOCATE : Z := 0x32664.
Definition RT_PCA : Z := 0x31c30.
Definition RT_PCD : Z := 0x3191c.
Definition RT_PCM : Z := 0x96a4c.
Definition RT_RA_A : Z := 0x326d0.
Definition RT_RA_M : Z := 0x32748.
Definition RT_RA_D : Z := 0x32764.
Definition RT_RA_R : Z := 0x32654.
Definition RT_RA_NA : Z := 0x32630.
Definition RT_RA_I : Z := 0x543f0.
Definition RT_GOT_M : Z := 0x9df78.
Definition RT_REAL_M : Z := 0x9fde8.
Definition RT_INST : Z := 0xa2fd8.
Definition RT_OOM : Z := 0x1288a0.
Definition RT_TP : Z := 0x5d99f0.
Definition RT_ERRNO : Z := 0x5d994c.

(* The stack frames below realloc's entry sp, as offsets from it: the interceptor's (2032 bytes, then 112 more), the
   BufferedStackTrace object at -2136, asan_realloc's (16 bytes, its ra at -2152) and Reallocate's (48 bytes, its ra
   at -2168, s0..s4 at -2176..-2208).  Allocate and Deallocate are entered from Reallocate at sp - 2208; the
   NULL-input Allocate from asan_realloc at sp - 2160. *)
Definition RT_SO : Z := -2136.
Definition RT_SPR : Z := -2208.
Definition RT_SPN : Z := -2160.

Definition rt_tbl_build : ctable :=
build_table tfibsegs 0x325b8 131%nat (build_table tfibsegs 0x54244 118%nat
(build_table tfibsegs 0x6e0fc 8%nat (build_table tfibsegs 0x8cf28 3%nat TEmpty))).
Definition rt_tbl : ctable := Eval vm_compute in rt_tbl_build.
Lemma rt_tbl_eq : rt_tbl = rt_tbl_build.
Proof. vm_cast_no_check (@eq_refl ctable rt_tbl). Qed.
Lemma rt_tbl_ok : table_ok tfibsegs rt_tbl.
Proof.
rewrite rt_tbl_eq. unfold rt_tbl_build.
do 3 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate.
Qed.
