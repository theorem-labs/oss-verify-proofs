(* Modified by Theorem Labs, 2026-10: from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_S1_tbl.v (commit ddc081c1a03, fuzz_state's realloc segment S1; file sha256 242ff2b140b9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair_fs.py; 0 code pcs the tool read as sizes, by funcpair_fs.py), and 12 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/FSRealloc_S1_tbl.v at commit 6ea216c338f as lib/B/FSRealloc_S1_tbl.v, with its module paths changed (lib.A to lib.B, except the image-free ADIfaceImgA and the one params file CfParamsReply; the image twins A<r> to Y<r>, CfImgA / CfImg_A to CfImgB / CfImg_B, WrapAKit / WrapFreeA<x> to WrapBKit / WrapFreeB<x>, AFf0cfR to YFf0cfR, RGcfWalkA to RGcfWalkB with its three exported names wrap_realloc_walk_cf_A, wrap_realloc_null_walk_cf_A, wrap_realloc_walk_cf_rh_A to _B), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan by alreloc 6e5d1356c317 (13 numerals; per-numeral report). *)
(* Provenance: in the header prose, 1 instruction immediate quoted in the prose (jal / auipc / lw) restated from fuzz_reply.asan's own instruction words. *)
(* Image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a): every address in the next comment is image B's; an image it names is the image its text came from. *)
(* fuzz_state image A, realloc segment S1 (RtS1, 2026-10-29): WORK IN PROGRESS, NOT YET COMPILED.
   The decode table of the realloc prefix's code, port of cgif_rgb_fuzzer lib/YF77.v (tfxtbl_rr) at fs.asan's addresses
   (capstone over fs.asan sha256 64b53ff86172bb07..., RV64, no compressed instructions):
   - 0x54244, 118 instructions: __interceptor_realloc, 0x54244 `addi sp, sp, -0x7f0` .. 0x54418 `ret`;
   - 0x325b8, 131 instructions: asan_realloc 0x325b8 `addi sp, sp, -0x10` .. 0x32660 `ret`, then Allocator::Reallocate
     0x32664 `addi sp, sp, -0x30` .. 0x32784 `ret` and its CHECK tails to 0x327c0 `jal 0x3ad64`;
   over tfibtbl_rtA (A/AB1q.v), whose last range 0x31bd4 (633 instructions) ends at 0x325b8. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rr_build : ctable := build_table tfibsegs 0x54244 118%nat (build_table tfibsegs 0x325b8 131%nat tfibtbl_rtA).
Definition tfibtbl_rr : ctable := Eval vm_compute in tfibtbl_rr_build.
Lemma tfibtbl_rr_eq : tfibtbl_rr = tfibtbl_rr_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rr). Qed.
Lemma tfibtbl_rr_ok : table_ok tfibsegs tfibtbl_rr.
Proof. rewrite tfibtbl_rr_eq. unfold tfibtbl_rr_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
