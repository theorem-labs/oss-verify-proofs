(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_53538 : bv 32 := 0x40c006b3.
Lemma F_53538 : fetch_word Ubsan.M.loaded_segments (0x55314 : word) = Some W_53538.
Proof. vm_refl. Qed.
Lemma D_53538 : decode_any W_53538 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5353c : bv 32 := 0x00b6f6b3.
Lemma F_5353c : fetch_word Ubsan.M.loaded_segments (0x55318 : word) = Some W_5353c.
Proof. vm_refl. Qed.
Lemma D_5353c : decode_any W_5353c = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_53540 : bv 32 := 0x40d506b3.
Lemma F_53540 : fetch_word Ubsan.M.loaded_segments (0x5531c : word) = Some W_53540.
Proof. vm_refl. Qed.
Lemma D_53540 : decode_any W_53540 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_53544 : bv 32 := 0x00d70733.
Lemma F_53544 : fetch_word Ubsan.M.loaded_segments (0x55320 : word) = Some W_53544.
Proof. vm_refl. Qed.
Lemma D_53544 : decode_any W_53544 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_53548 : bv 32 := 0x00ea3023.
Lemma F_53548 : fetch_word Ubsan.M.loaded_segments (0x55324 : word) = Some W_53548.
Proof. vm_refl. Qed.
Lemma D_53548 : decode_any W_53548 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5354c : bv 32 := 0xf8a5fce3.
Lemma F_5354c : fetch_word Ubsan.M.loaded_segments (0x55328 : word) = Some W_5354c.
Proof. vm_refl. Qed.
Lemma D_5354c : decode_any W_5354c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_53550 : bv 32 := 0x01800713.
Lemma F_53550 : fetch_word Ubsan.M.loaded_segments (0x5532c : word) = Some W_53550.
Proof. vm_refl. Qed.
Lemma D_53550 : decode_any W_53550 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_53554 : bv 32 := 0xf95ff06f.
Lemma F_53554 : fetch_word Ubsan.M.loaded_segments (0x55330 : word) = Some W_53554.
Proof. vm_refl. Qed.
Lemma D_53554 : decode_any W_53554 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
