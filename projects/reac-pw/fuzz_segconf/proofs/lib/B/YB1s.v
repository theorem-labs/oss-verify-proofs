(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1s.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AB1s.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AB1s.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_509d4 : bv 32 := 0x000b2583.
Lemma F_509d4 : fetch_word AsanUbsan.M.loaded_segments (0x35d88 : word) = Some W_509d4.
Proof. vm_refl. Qed.
Lemma D_509d4 : decode_any W_509d4 = Some (Load SZ4 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_509d8 : bv 32 := 0x004b0b13.
Lemma F_509d8 : fetch_word AsanUbsan.M.loaded_segments (0x35d8c : word) = Some W_509d8.
Proof. vm_refl. Qed.
Lemma D_509d8 : decode_any W_509d8 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_509dc : bv 32 := 0x00bca023.
Lemma F_509dc : fetch_word AsanUbsan.M.loaded_segments (0x35d90 : word) = Some W_509dc.
Proof. vm_refl. Qed.
Lemma D_509dc : decode_any W_509dc = Some (Store SZ4 25 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_509e0 : bv 32 := 0x004c8c93.
Lemma F_509e0 : fetch_word AsanUbsan.M.loaded_segments (0x35d94 : word) = Some W_509e0.
Proof. vm_refl. Qed.
Lemma D_509e0 : decode_any W_509e0 = Some (OpImm ALU_ADD 25 25 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_509e4 : bv 32 := 0xfeab18e3.
Lemma F_509e4 : fetch_word AsanUbsan.M.loaded_segments (0x35d98 : word) = Some W_509e4.
Proof. vm_refl. Qed.
Lemma D_509e4 : decode_any W_509e4 = Some (Branch BC_NE 22 10 8176, 4%Z).
Proof. vm_refl. Qed.
