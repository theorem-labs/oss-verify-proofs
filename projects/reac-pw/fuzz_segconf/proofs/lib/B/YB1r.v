(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1r.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AB1r.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AB1r.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
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
Definition W_52d28 : bv 32 := 0x000a2603.
Lemma F_52d28 : fetch_word AsanUbsan.M.loaded_segments (0x380dc : word) = Some W_52d28.
Proof. vm_refl. Qed.
Lemma D_52d28 : decode_any W_52d28 = Some (Load SZ4 true 12 20 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d2c : bv 32 := 0x00c6a023.
Lemma F_52d2c : fetch_word AsanUbsan.M.loaded_segments (0x380e0 : word) = Some W_52d2c.
Proof. vm_refl. Qed.
Lemma D_52d2c : decode_any W_52d2c = Some (Store SZ4 13 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d30 : bv 32 := 0x00468693.
Lemma F_52d30 : fetch_word AsanUbsan.M.loaded_segments (0x380e4 : word) = Some W_52d30.
Proof. vm_refl. Qed.
Lemma D_52d30 : decode_any W_52d30 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d34 : bv 32 := 0x004a0a13.
Lemma F_52d34 : fetch_word AsanUbsan.M.loaded_segments (0x380e8 : word) = Some W_52d34.
Proof. vm_refl. Qed.
Lemma D_52d34 : decode_any W_52d34 = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d38 : bv 32 := 0xfeb698e3.
Lemma F_52d38 : fetch_word AsanUbsan.M.loaded_segments (0x380ec : word) = Some W_52d38.
Proof. vm_refl. Qed.
Lemma D_52d38 : decode_any W_52d38 = Some (Branch BC_NE 13 11 8176, 4%Z).
Proof. vm_refl. Qed.
