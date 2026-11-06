(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_86fd0 : bv 32 := 0x00141517.
Lemma F_86fd0 : fetch_word AsanUbsan.M.loaded_segments (0x87020 : word) = Some W_86fd0.
Proof. vm_refl. Qed.
Lemma D_86fd0 : decode_any W_86fd0 = Some (Auipc 10 321, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fd4 : bv 32 := 0x34150503.
Lemma F_86fd4 : fetch_word AsanUbsan.M.loaded_segments (0x87024 : word) = Some W_86fd4.
Proof. vm_refl. Qed.
Lemma D_86fd4 : decode_any W_86fd4 = Some (Load SZ1 true 10 10 833, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fd8 : bv 32 := 0x00a03533.
Lemma F_86fd8 : fetch_word AsanUbsan.M.loaded_segments (0x87028 : word) = Some W_86fd8.
Proof. vm_refl. Qed.
Lemma D_86fd8 : decode_any W_86fd8 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_86fdc : bv 32 := 0x00008067.
Lemma F_86fdc : fetch_word AsanUbsan.M.loaded_segments (0x8702c : word) = Some W_86fdc.
Proof. vm_refl. Qed.
Lemma D_86fdc : decode_any W_86fdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ff8 : bv 32 := 0x00141517.
Lemma F_86ff8 : fetch_word AsanUbsan.M.loaded_segments (0x87048 : word) = Some W_86ff8.
Proof. vm_refl. Qed.
Lemma D_86ff8 : decode_any W_86ff8 = Some (Auipc 10 321, 4%Z).
Proof. vm_refl. Qed.

Definition W_86ffc : bv 32 := 0x31a50503.
Lemma F_86ffc : fetch_word AsanUbsan.M.loaded_segments (0x8704c : word) = Some W_86ffc.
Proof. vm_refl. Qed.
Lemma D_86ffc : decode_any W_86ffc = Some (Load SZ1 true 10 10 794, 4%Z).
Proof. vm_refl. Qed.

Definition W_87000 : bv 32 := 0x00a03533.
Lemma F_87000 : fetch_word AsanUbsan.M.loaded_segments (0x87050 : word) = Some W_87000.
Proof. vm_refl. Qed.
Lemma D_87000 : decode_any W_87000 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_87004 : bv 32 := 0x00008067.
Lemma F_87004 : fetch_word AsanUbsan.M.loaded_segments (0x87054 : word) = Some W_87004.
Proof. vm_refl. Qed.
Lemma D_87004 : decode_any W_87004 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
