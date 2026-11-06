(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: generated for omx-clap-core/fuzz_preset's ASan image (ELF sha256 c90d4fa54d43160b) by startb/gen/gen_fetch.py (sha256 1904fdb1e4b3093e) from proofs/cgif/cgif_file_fuzzer/lib/YB1s.v: every address moved by the containing function of the donor's recovered symbol table to that function in the target, and every `fetch_word` fact checked against the word the target image holds at the moved address (all equal: these bodies are identical in the two images); module paths changed. *)
(* Modified by Theorem Labs, 2026-10-29: image B' of the harness fix #102 (oss-verify 5f067f673c44, facts 8f3e7e1a07f1). Read from the unstripped twin bound-fix/9e1283d1/unstripped/fuzz_preset/fuzz_preset.asan-ubsan sha256 c90d4fa54d43160baf62e5aa387211a798dddbad13d2619d85acbf37aee0c175; pin of record bound-fix/a3b65bd4/bin/fuzz_preset/fuzz_preset.asan-ubsan sha256 d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994. Every `fetch_word` fact below was re-read against BOTH that twin and that pin: 5 facts, 0 mismatches. CONTROL: the same generator on the OLD-pin twin 3b5e1a099b535acf reproduces lib/Reusable/YB1s.v of origin/cold/h-mani-a4-preset-relocB BYTE FOR BYTE. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_509d4 : bv 32 := 0x000b2583.
Lemma F_509d4 : fetch_word AsanUbsan.M.loaded_segments (0x353b4 : word) = Some W_509d4.
Proof. vm_refl. Qed.
Lemma D_509d4 : decode_any W_509d4 = Some (Load SZ4 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_509d8 : bv 32 := 0x004b0b13.
Lemma F_509d8 : fetch_word AsanUbsan.M.loaded_segments (0x353b8 : word) = Some W_509d8.
Proof. vm_refl. Qed.
Lemma D_509d8 : decode_any W_509d8 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_509dc : bv 32 := 0x00bca023.
Lemma F_509dc : fetch_word AsanUbsan.M.loaded_segments (0x353bc : word) = Some W_509dc.
Proof. vm_refl. Qed.
Lemma D_509dc : decode_any W_509dc = Some (Store SZ4 25 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_509e0 : bv 32 := 0x004c8c93.
Lemma F_509e0 : fetch_word AsanUbsan.M.loaded_segments (0x353c0 : word) = Some W_509e0.
Proof. vm_refl. Qed.
Lemma D_509e0 : decode_any W_509e0 = Some (OpImm ALU_ADD 25 25 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_509e4 : bv 32 := 0xfeab18e3.
Lemma F_509e4 : fetch_word AsanUbsan.M.loaded_segments (0x353c4 : word) = Some W_509e4.
Proof. vm_refl. Qed.
Lemma D_509e4 : decode_any W_509e4 = Some (Branch BC_NE 22 10 8176, 4%Z).
Proof. vm_refl. Qed.
