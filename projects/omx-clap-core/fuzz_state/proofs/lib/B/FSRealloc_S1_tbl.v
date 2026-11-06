(* fuzz_state image B, realloc segment S1 (a Theorem Labs lane, 2026-10-29).
   The decode table of the realloc prefix's code: the B twin of lib/A/FSRealloc_S1_tbl.v (a working branch
   ce07ca45bca; port of cgif_rgb_fuzzer lib/YF77.v tfxtbl_rr) at fuzz_state.asan-ubsan's addresses (capstone over sha256
   5ac5ce0954f87e2d..., RV64, no compressed instructions; A's address in []):
   - 0x534e4 [0x53474], 118 instructions: __interceptor_realloc, 0x534e4 `addi sp, sp, -0x7f0` .. 0x536b8 `ret`;
   - 0x328ec [0x3287c], 131 instructions: asan_realloc 0x328ec `addi sp, sp, -0x10` .. 0x32994 `ret`, then
     Allocator::Reallocate 0x32998 `addi sp, sp, -0x30` .. 0x32ab8 `ret` and its CHECK tails to 0x32af4 `jal 0x39678`;
   over tfibtbl_rtA (B/YB1q.v), whose last range 0x31f08 [0x31e98] (633 instructions) ends at 0x328ec.
   The two bodies are A's word for word except the pc-relative lo12 fields (capstone diff: interceptor 1 word, asan_realloc
   / Reallocate 9 words).  Two of them lie on S1's path: 0x53624 `ld a1, 0x5e0(a1)` (after 0x53620 `auipc a1, 0x4c`) reads
   the GOT slot 0x9fc00, which REG0 seeds; 0x32978 `addi a0, a0, 0x464` (after 0x32974 `auipc a0, 0x72`) forms
   inst = 0xa4dd8 = TFIB_INST, which PAREGS checks.  The other eight (0x3290c, 0x3291c, 0x32950, 0x32a48, 0x32ac4, 0x32ac8,
   0x32ae4, 0x32ae8) lie on branches the walk decides untaken or after Allocate's call. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.
Definition tfibtbl_rr_build : ctable := build_table tfibsegs 0x534e4 118%nat (build_table tfibsegs 0x328ec 131%nat tfibtbl_rtA).
Definition tfibtbl_rr : ctable := Eval vm_compute in tfibtbl_rr_build.
Lemma tfibtbl_rr_eq : tfibtbl_rr = tfibtbl_rr_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rr). Qed.
Lemma tfibtbl_rr_ok : table_ok tfibsegs tfibtbl_rr.
Proof. rewrite tfibtbl_rr_eq. unfold tfibtbl_rr_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
