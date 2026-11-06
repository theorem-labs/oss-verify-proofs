(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_dc460 : bv 32 := 0x00567597.
Lemma F_dc460 : fetch_word asegs (0xdc43c : word) = Some W_dc460.
Proof. vm_refl. Qed.
Lemma D_dc460 : decode_any W_dc460 = Some (Auipc 11 1383, 4%Z).
Proof. vm_refl. Qed.

Definition W_dc464 : bv 32 := 0xcb758683.
Lemma F_dc464 : fetch_word asegs (0xdc440 : word) = Some W_dc464.
Proof. vm_refl. Qed.
Lemma D_dc464 : decode_any W_dc464 = Some (Load SZ1 true 13 11 3255, 4%Z).
Proof. vm_refl. Qed.

Definition W_dc468 : bv 32 := 0x1e068863.
Lemma F_dc468 : fetch_word asegs (0xdc444 : word) = Some W_dc468.
Proof. vm_refl. Qed.
Lemma D_dc468 : decode_any W_dc468 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_dc658 : bv 32 := 0x00008067.
Lemma F_dc658 : fetch_word asegs (0xdc634 : word) = Some W_dc658.
Proof. vm_refl. Qed.
Lemma D_dc658 : decode_any W_dc658 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
