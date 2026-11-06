(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1r.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1r.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1r.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_qdisc's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1r.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.reac_pw.fuzz_qdisc.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_52d28 : bv 32 := 0x000a2603.
Lemma F_52d28 : fetch_word AsanUbsan.M.loaded_segments (0x35a88 : word) = Some W_52d28.
Proof. vm_refl. Qed.
Lemma D_52d28 : decode_any W_52d28 = Some (Load SZ4 true 12 20 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d2c : bv 32 := 0x00c6a023.
Lemma F_52d2c : fetch_word AsanUbsan.M.loaded_segments (0x35a8c : word) = Some W_52d2c.
Proof. vm_refl. Qed.
Lemma D_52d2c : decode_any W_52d2c = Some (Store SZ4 13 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d30 : bv 32 := 0x00468693.
Lemma F_52d30 : fetch_word AsanUbsan.M.loaded_segments (0x35a90 : word) = Some W_52d30.
Proof. vm_refl. Qed.
Lemma D_52d30 : decode_any W_52d30 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d34 : bv 32 := 0x004a0a13.
Lemma F_52d34 : fetch_word AsanUbsan.M.loaded_segments (0x35a94 : word) = Some W_52d34.
Proof. vm_refl. Qed.
Lemma D_52d34 : decode_any W_52d34 = Some (OpImm ALU_ADD 20 20 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_52d38 : bv 32 := 0xfeb698e3.
Lemma F_52d38 : fetch_word AsanUbsan.M.loaded_segments (0x35a98 : word) = Some W_52d38.
Proof. vm_refl. Qed.
Lemma D_52d38 : decode_any W_52d38 = Some (Branch BC_NE 13 11 8176, 4%Z).
Proof. vm_refl. Qed.
