(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_73ec8 : bv 32 := 0xfe010113.
Lemma F_73ec8 : fetch_word AsanUbsan.M.loaded_segments (0x73f10 : word) = Some W_73ec8.
Proof. vm_refl. Qed.
Lemma D_73ec8 : decode_any W_73ec8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ecc : bv 32 := 0x00113c23.
Lemma F_73ecc : fetch_word AsanUbsan.M.loaded_segments (0x73f14 : word) = Some W_73ecc.
Proof. vm_refl. Qed.
Lemma D_73ecc : decode_any W_73ecc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ed0 : bv 32 := 0x00813823.
Lemma F_73ed0 : fetch_word AsanUbsan.M.loaded_segments (0x73f18 : word) = Some W_73ed0.
Proof. vm_refl. Qed.
Lemma D_73ed0 : decode_any W_73ed0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ed4 : bv 32 := 0x00913423.
Lemma F_73ed4 : fetch_word AsanUbsan.M.loaded_segments (0x73f1c : word) = Some W_73ed4.
Proof. vm_refl. Qed.
Lemma D_73ed4 : decode_any W_73ed4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ed8 : bv 32 := 0x01213023.
Lemma F_73ed8 : fetch_word AsanUbsan.M.loaded_segments (0x73f20 : word) = Some W_73ed8.
Proof. vm_refl. Qed.
Lemma D_73ed8 : decode_any W_73ed8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73edc : bv 32 := 0x00050413.
Lemma F_73edc : fetch_word AsanUbsan.M.loaded_segments (0x73f24 : word) = Some W_73edc.
Proof. vm_refl. Qed.
Lemma D_73edc : decode_any W_73edc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ee0 : bv 32 := 0x038160ef.
Lemma F_73ee0 : fetch_word AsanUbsan.M.loaded_segments (0x73f28 : word) = Some W_73ee0.
Proof. vm_refl. Qed.
Lemma D_73ee0 : decode_any W_73ee0 = Some (Jal 1 90168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ee4 : bv 32 := 0x000f2597.
Lemma F_73ee4 : fetch_word AsanUbsan.M.loaded_segments (0x73f2c : word) = Some W_73ee4.
Proof. vm_refl. Qed.
Lemma D_73ee4 : decode_any W_73ee4 = Some (Auipc 11 242, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ee8 : bv 32 := 0x5145b583.
Lemma F_73ee8 : fetch_word AsanUbsan.M.loaded_segments (0x73f30 : word) = Some W_73ee8.
Proof. vm_refl. Qed.
Lemma D_73ee8 : decode_any W_73ee8 = Some (Load SZ8 true 11 11 1300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73eec : bv 32 := 0x00050913.
Lemma F_73eec : fetch_word AsanUbsan.M.loaded_segments (0x73f34 : word) = Some W_73eec.
Proof. vm_refl. Qed.
Lemma D_73eec : decode_any W_73eec = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ef0 : bv 32 := 0x00040513.
Lemma F_73ef0 : fetch_word AsanUbsan.M.loaded_segments (0x73f38 : word) = Some W_73ef0.
Proof. vm_refl. Qed.
Lemma D_73ef0 : decode_any W_73ef0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ef4 : bv 32 := 0x000580e7.
Lemma F_73ef4 : fetch_word AsanUbsan.M.loaded_segments (0x73f3c : word) = Some W_73ef4.
Proof. vm_refl. Qed.
Lemma D_73ef4 : decode_any W_73ef4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ef8 : bv 32 := 0x00050493.
Lemma F_73ef8 : fetch_word AsanUbsan.M.loaded_segments (0x73f40 : word) = Some W_73ef8.
Proof. vm_refl. Qed.
Lemma D_73ef8 : decode_any W_73ef8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73efc : bv 32 := 0x02090663.
Lemma F_73efc : fetch_word AsanUbsan.M.loaded_segments (0x73f44 : word) = Some W_73efc.
Proof. vm_refl. Qed.
Lemma D_73efc : decode_any W_73efc = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f00 : bv 32 := 0x019180ef.
Lemma F_73f00 : fetch_word AsanUbsan.M.loaded_segments (0x73f48 : word) = Some W_73f00.
Proof. vm_refl. Qed.
Lemma D_73f00 : decode_any W_73f00 = Some (Jal 1 100376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f04 : bv 32 := 0x00050863.
Lemma F_73f04 : fetch_word AsanUbsan.M.loaded_segments (0x73f4c : word) = Some W_73f04.
Proof. vm_refl. Qed.
Lemma D_73f04 : decode_any W_73f04 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f08 : bv 32 := 0x03053603.
Lemma F_73f08 : fetch_word AsanUbsan.M.loaded_segments (0x73f50 : word) = Some W_73f08.
Proof. vm_refl. Qed.
Lemma D_73f08 : decode_any W_73f08 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f0c : bv 32 := 0x03853683.
Lemma F_73f0c : fetch_word AsanUbsan.M.loaded_segments (0x73f54 : word) = Some W_73f0c.
Proof. vm_refl. Qed.
Lemma D_73f0c : decode_any W_73f0c = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f10 : bv 32 := 0x00c0006f.
Lemma F_73f10 : fetch_word AsanUbsan.M.loaded_segments (0x73f58 : word) = Some W_73f10.
Proof. vm_refl. Qed.
Lemma D_73f10 : decode_any W_73f10 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f1c : bv 32 := 0x00040513.
Lemma F_73f1c : fetch_word AsanUbsan.M.loaded_segments (0x73f64 : word) = Some W_73f1c.
Proof. vm_refl. Qed.
Lemma D_73f1c : decode_any W_73f1c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f20 : bv 32 := 0x00048593.
Lemma F_73f20 : fetch_word AsanUbsan.M.loaded_segments (0x73f68 : word) = Some W_73f20.
Proof. vm_refl. Qed.
Lemma D_73f20 : decode_any W_73f20 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f24 : bv 32 := 0x725250ef.
Lemma F_73f24 : fetch_word AsanUbsan.M.loaded_segments (0x73f6c : word) = Some W_73f24.
Proof. vm_refl. Qed.
Lemma D_73f24 : decode_any W_73f24 = Some (Jal 1 155428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f28 : bv 32 := 0x00048513.
Lemma F_73f28 : fetch_word AsanUbsan.M.loaded_segments (0x73f70 : word) = Some W_73f28.
Proof. vm_refl. Qed.
Lemma D_73f28 : decode_any W_73f28 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f2c : bv 32 := 0x01813083.
Lemma F_73f2c : fetch_word AsanUbsan.M.loaded_segments (0x73f74 : word) = Some W_73f2c.
Proof. vm_refl. Qed.
Lemma D_73f2c : decode_any W_73f2c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f30 : bv 32 := 0x01013403.
Lemma F_73f30 : fetch_word AsanUbsan.M.loaded_segments (0x73f78 : word) = Some W_73f30.
Proof. vm_refl. Qed.
Lemma D_73f30 : decode_any W_73f30 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f34 : bv 32 := 0x00813483.
Lemma F_73f34 : fetch_word AsanUbsan.M.loaded_segments (0x73f7c : word) = Some W_73f34.
Proof. vm_refl. Qed.
Lemma D_73f34 : decode_any W_73f34 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f38 : bv 32 := 0x00013903.
Lemma F_73f38 : fetch_word AsanUbsan.M.loaded_segments (0x73f80 : word) = Some W_73f38.
Proof. vm_refl. Qed.
Lemma D_73f38 : decode_any W_73f38 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f3c : bv 32 := 0x02010113.
Lemma F_73f3c : fetch_word AsanUbsan.M.loaded_segments (0x73f84 : word) = Some W_73f3c.
Proof. vm_refl. Qed.
Lemma D_73f3c : decode_any W_73f3c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73f40 : bv 32 := 0x00008067.
Lemma F_73f40 : fetch_word AsanUbsan.M.loaded_segments (0x73f88 : word) = Some W_73f40.
Proof. vm_refl. Qed.
Lemma D_73f40 : decode_any W_73f40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

