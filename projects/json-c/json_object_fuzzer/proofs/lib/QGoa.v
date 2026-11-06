(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_deb4c : bv 32 := 0x00567597.
Lemma F_deb4c : fetch_word asegs (0xdeb00 : word) = Some W_deb4c.
Proof. vm_refl. Qed.
Lemma D_deb4c : decode_any W_deb4c = Some (Auipc 11 1383, 4%Z).
Proof. vm_refl. Qed.

Definition W_deb50 : bv 32 := 0xcb358683.
Lemma F_deb50 : fetch_word asegs (0xdeb04 : word) = Some W_deb50.
Proof. vm_refl. Qed.
Lemma D_deb50 : decode_any W_deb50 = Some (Load SZ1 true 13 11 3251, 4%Z).
Proof. vm_refl. Qed.

Definition W_deb54 : bv 32 := 0x1e068863.
Lemma F_deb54 : fetch_word asegs (0xdeb08 : word) = Some W_deb54.
Proof. vm_refl. Qed.
Lemma D_deb54 : decode_any W_deb54 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_ded44 : bv 32 := 0x00008067.
Lemma F_ded44 : fetch_word asegs (0xdecf8 : word) = Some W_ded44.
Proof. vm_refl. Qed.
Lemma D_ded44 : decode_any W_ded44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
