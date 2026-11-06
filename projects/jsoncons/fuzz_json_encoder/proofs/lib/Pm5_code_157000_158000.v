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
Definition W_15713c : bv 32 := 0x0056b597.
Lemma F_15713c : fetch_word AsanUbsan.M.loaded_segments (0x157178 : word) = Some W_15713c.
Proof. vm_refl. Qed.
Lemma D_15713c : decode_any W_15713c = Some (Auipc 11 1387, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157140 : bv 32 := 0x9ab58683.
Lemma F_157140 : fetch_word AsanUbsan.M.loaded_segments (0x15717c : word) = Some W_157140.
Proof. vm_refl. Qed.
Lemma D_157140 : decode_any W_157140 = Some (Load SZ1 true 13 11 2475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157144 : bv 32 := 0x1e068863.
Lemma F_157144 : fetch_word AsanUbsan.M.loaded_segments (0x157180 : word) = Some W_157144.
Proof. vm_refl. Qed.
Lemma D_157144 : decode_any W_157144 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157334 : bv 32 := 0x00008067.
Lemma F_157334 : fetch_word AsanUbsan.M.loaded_segments (0x157370 : word) = Some W_157334.
Proof. vm_refl. Qed.
Lemma D_157334 : decode_any W_157334 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1573c4 : bv 32 := 0x00052583.
Lemma F_1573c4 : fetch_word AsanUbsan.M.loaded_segments (0x157400 : word) = Some W_1573c4.
Proof. vm_refl. Qed.
Lemma D_1573c4 : decode_any W_1573c4 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1573c8 : bv 32 := 0x0005c463.
Lemma F_1573c8 : fetch_word AsanUbsan.M.loaded_segments (0x157404 : word) = Some W_1573c8.
Proof. vm_refl. Qed.
Lemma D_1573c8 : decode_any W_1573c8 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1573cc : bv 32 := 0x00008067.
Lemma F_1573cc : fetch_word AsanUbsan.M.loaded_segments (0x157408 : word) = Some W_1573cc.
Proof. vm_refl. Qed.
Lemma D_1573cc : decode_any W_1573cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157438 : bv 32 := 0x00050893.
Lemma F_157438 : fetch_word AsanUbsan.M.loaded_segments (0x157474 : word) = Some W_157438.
Proof. vm_refl. Qed.
Lemma D_157438 : decode_any W_157438 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15743c : bv 32 := 0x00058513.
Lemma F_15743c : fetch_word AsanUbsan.M.loaded_segments (0x157478 : word) = Some W_15743c.
Proof. vm_refl. Qed.
Lemma D_15743c : decode_any W_15743c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157440 : bv 32 := 0x00060593.
Lemma F_157440 : fetch_word AsanUbsan.M.loaded_segments (0x15747c : word) = Some W_157440.
Proof. vm_refl. Qed.
Lemma D_157440 : decode_any W_157440 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157444 : bv 32 := 0x00068613.
Lemma F_157444 : fetch_word AsanUbsan.M.loaded_segments (0x157480 : word) = Some W_157444.
Proof. vm_refl. Qed.
Lemma D_157444 : decode_any W_157444 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157448 : bv 32 := 0x00070693.
Lemma F_157448 : fetch_word AsanUbsan.M.loaded_segments (0x157484 : word) = Some W_157448.
Proof. vm_refl. Qed.
Lemma D_157448 : decode_any W_157448 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15744c : bv 32 := 0x00078713.
Lemma F_15744c : fetch_word AsanUbsan.M.loaded_segments (0x157488 : word) = Some W_15744c.
Proof. vm_refl. Qed.
Lemma D_15744c : decode_any W_15744c = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157450 : bv 32 := 0x00080793.
Lemma F_157450 : fetch_word AsanUbsan.M.loaded_segments (0x15748c : word) = Some W_157450.
Proof. vm_refl. Qed.
Lemma D_157450 : decode_any W_157450 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157458 : bv 32 := 0x00008067.
Lemma F_157458 : fetch_word AsanUbsan.M.loaded_segments (0x157494 : word) = Some W_157458.
Proof. vm_refl. Qed.
Lemma D_157458 : decode_any W_157458 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15745c : bv 32 := 0xfddff06f.
Lemma F_15745c : fetch_word AsanUbsan.M.loaded_segments (0x157498 : word) = Some W_15745c.
Proof. vm_refl. Qed.
Lemma D_15745c : decode_any W_15745c = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157460 : bv 32 := 0x00020593.
Lemma F_157460 : fetch_word AsanUbsan.M.loaded_segments (0x15749c : word) = Some W_157460.
Proof. vm_refl. Qed.
Lemma D_157460 : decode_any W_157460 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157464 : bv 32 := 0x00053603.
Lemma F_157464 : fetch_word AsanUbsan.M.loaded_segments (0x1574a0 : word) = Some W_157464.
Proof. vm_refl. Qed.
Lemma D_157464 : decode_any W_157464 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157468 : bv 32 := 0xff85b583.
Lemma F_157468 : fetch_word AsanUbsan.M.loaded_segments (0x1574a4 : word) = Some W_157468.
Proof. vm_refl. Qed.
Lemma D_157468 : decode_any W_157468 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15746c : bv 32 := 0x00853503.
Lemma F_15746c : fetch_word AsanUbsan.M.loaded_segments (0x1574a8 : word) = Some W_15746c.
Proof. vm_refl. Qed.
Lemma D_15746c : decode_any W_15746c = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157470 : bv 32 := 0x00361613.
Lemma F_157470 : fetch_word AsanUbsan.M.loaded_segments (0x1574ac : word) = Some W_157470.
Proof. vm_refl. Qed.
Lemma D_157470 : decode_any W_157470 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157474 : bv 32 := 0x00c585b3.
Lemma F_157474 : fetch_word AsanUbsan.M.loaded_segments (0x1574b0 : word) = Some W_157474.
Proof. vm_refl. Qed.
Lemma D_157474 : decode_any W_157474 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157478 : bv 32 := 0x0005b583.
Lemma F_157478 : fetch_word AsanUbsan.M.loaded_segments (0x1574b4 : word) = Some W_157478.
Proof. vm_refl. Qed.
Lemma D_157478 : decode_any W_157478 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15747c : bv 32 := 0x00b50533.
Lemma F_15747c : fetch_word AsanUbsan.M.loaded_segments (0x1574b8 : word) = Some W_15747c.
Proof. vm_refl. Qed.
Lemma D_15747c : decode_any W_15747c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157480 : bv 32 := 0x00008067.
Lemma F_157480 : fetch_word AsanUbsan.M.loaded_segments (0x1574bc : word) = Some W_157480.
Proof. vm_refl. Qed.
Lemma D_157480 : decode_any W_157480 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

