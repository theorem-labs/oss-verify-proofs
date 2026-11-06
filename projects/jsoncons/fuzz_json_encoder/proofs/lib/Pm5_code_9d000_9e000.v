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
Definition W_9deb0 : bv 32 := 0xfe010113.
Lemma F_9deb0 : fetch_word AsanUbsan.M.loaded_segments (0x9def8 : word) = Some W_9deb0.
Proof. vm_refl. Qed.
Lemma D_9deb0 : decode_any W_9deb0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deb4 : bv 32 := 0x00113c23.
Lemma F_9deb4 : fetch_word AsanUbsan.M.loaded_segments (0x9defc : word) = Some W_9deb4.
Proof. vm_refl. Qed.
Lemma D_9deb4 : decode_any W_9deb4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deb8 : bv 32 := 0x00813823.
Lemma F_9deb8 : fetch_word AsanUbsan.M.loaded_segments (0x9df00 : word) = Some W_9deb8.
Proof. vm_refl. Qed.
Lemma D_9deb8 : decode_any W_9deb8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9debc : bv 32 := 0x00913423.
Lemma F_9debc : fetch_word AsanUbsan.M.loaded_segments (0x9df04 : word) = Some W_9debc.
Proof. vm_refl. Qed.
Lemma D_9debc : decode_any W_9debc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec0 : bv 32 := 0x01213023.
Lemma F_9dec0 : fetch_word AsanUbsan.M.loaded_segments (0x9df08 : word) = Some W_9dec0.
Proof. vm_refl. Qed.
Lemma D_9dec0 : decode_any W_9dec0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec4 : bv 32 := 0x00058413.
Lemma F_9dec4 : fetch_word AsanUbsan.M.loaded_segments (0x9df0c : word) = Some W_9dec4.
Proof. vm_refl. Qed.
Lemma D_9dec4 : decode_any W_9dec4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec8 : bv 32 := 0x000c6597.
Lemma F_9dec8 : fetch_word AsanUbsan.M.loaded_segments (0x9df10 : word) = Some W_9dec8.
Proof. vm_refl. Qed.
Lemma D_9dec8 : decode_any W_9dec8 = Some (Auipc 11 198, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9decc : bv 32 := 0x5e85b903.
Lemma F_9decc : fetch_word AsanUbsan.M.loaded_segments (0x9df14 : word) = Some W_9decc.
Proof. vm_refl. Qed.
Lemma D_9decc : decode_any W_9decc = Some (Load SZ8 true 18 11 1512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded0 : bv 32 := 0x00093583.
Lemma F_9ded0 : fetch_word AsanUbsan.M.loaded_segments (0x9df18 : word) = Some W_9ded0.
Proof. vm_refl. Qed.
Lemma D_9ded0 : decode_any W_9ded0 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded4 : bv 32 := 0x00050493.
Lemma F_9ded4 : fetch_word AsanUbsan.M.loaded_segments (0x9df1c : word) = Some W_9ded4.
Proof. vm_refl. Qed.
Lemma D_9ded4 : decode_any W_9ded4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded8 : bv 32 := 0x00059863.
Lemma F_9ded8 : fetch_word AsanUbsan.M.loaded_segments (0x9df20 : word) = Some W_9ded8.
Proof. vm_refl. Qed.
Lemma D_9ded8 : decode_any W_9ded8 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dee8 : bv 32 := 0xfff58513.
Lemma F_9dee8 : fetch_word AsanUbsan.M.loaded_segments (0x9df30 : word) = Some W_9dee8.
Proof. vm_refl. Qed.
Lemma D_9dee8 : decode_any W_9dee8 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deec : bv 32 := 0x00a5f533.
Lemma F_9deec : fetch_word AsanUbsan.M.loaded_segments (0x9df34 : word) = Some W_9deec.
Proof. vm_refl. Qed.
Lemma D_9deec : decode_any W_9deec = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def0 : bv 32 := 0x04051a63.
Lemma F_9def0 : fetch_word AsanUbsan.M.loaded_segments (0x9df38 : word) = Some W_9def0.
Proof. vm_refl. Qed.
Lemma D_9def0 : decode_any W_9def0 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def4 : bv 32 := 0x00b484b3.
Lemma F_9def4 : fetch_word AsanUbsan.M.loaded_segments (0x9df3c : word) = Some W_9def4.
Proof. vm_refl. Qed.
Lemma D_9def4 : decode_any W_9def4 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def8 : bv 32 := 0x40b005b3.
Lemma F_9def8 : fetch_word AsanUbsan.M.loaded_segments (0x9df40 : word) = Some W_9def8.
Proof. vm_refl. Qed.
Lemma D_9def8 : decode_any W_9def8 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9defc : bv 32 := 0xfff48513.
Lemma F_9defc : fetch_word AsanUbsan.M.loaded_segments (0x9df44 : word) = Some W_9defc.
Proof. vm_refl. Qed.
Lemma D_9defc : decode_any W_9defc = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df00 : bv 32 := 0x00b57533.
Lemma F_9df00 : fetch_word AsanUbsan.M.loaded_segments (0x9df48 : word) = Some W_9df00.
Proof. vm_refl. Qed.
Lemma D_9df00 : decode_any W_9df00 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df04 : bv 32 := 0x00b475b3.
Lemma F_9df04 : fetch_word AsanUbsan.M.loaded_segments (0x9df4c : word) = Some W_9df04.
Proof. vm_refl. Qed.
Lemma D_9df04 : decode_any W_9df04 = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df08 : bv 32 := 0x02b57263.
Lemma F_9df08 : fetch_word AsanUbsan.M.loaded_segments (0x9df50 : word) = Some W_9df08.
Proof. vm_refl. Qed.
Lemma D_9df08 : decode_any W_9df08 = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df0c : bv 32 := 0x40a585b3.
Lemma F_9df0c : fetch_word AsanUbsan.M.loaded_segments (0x9df54 : word) = Some W_9df0c.
Proof. vm_refl. Qed.
Lemma D_9df0c : decode_any W_9df0c = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df10 : bv 32 := 0x00400613.
Lemma F_9df10 : fetch_word AsanUbsan.M.loaded_segments (0x9df58 : word) = Some W_9df10.
Proof. vm_refl. Qed.
Lemma D_9df10 : decode_any W_9df10 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df14 : bv 32 := 0x01813083.
Lemma F_9df14 : fetch_word AsanUbsan.M.loaded_segments (0x9df5c : word) = Some W_9df14.
Proof. vm_refl. Qed.
Lemma D_9df14 : decode_any W_9df14 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df18 : bv 32 := 0x01013403.
Lemma F_9df18 : fetch_word AsanUbsan.M.loaded_segments (0x9df60 : word) = Some W_9df18.
Proof. vm_refl. Qed.
Lemma D_9df18 : decode_any W_9df18 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df1c : bv 32 := 0x00813483.
Lemma F_9df1c : fetch_word AsanUbsan.M.loaded_segments (0x9df64 : word) = Some W_9df1c.
Proof. vm_refl. Qed.
Lemma D_9df1c : decode_any W_9df1c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df20 : bv 32 := 0x00013903.
Lemma F_9df20 : fetch_word AsanUbsan.M.loaded_segments (0x9df68 : word) = Some W_9df20.
Proof. vm_refl. Qed.
Lemma D_9df20 : decode_any W_9df20 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df24 : bv 32 := 0x02010113.
Lemma F_9df24 : fetch_word AsanUbsan.M.loaded_segments (0x9df6c : word) = Some W_9df24.
Proof. vm_refl. Qed.
Lemma D_9df24 : decode_any W_9df24 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df28 : bv 32 := 0xbb1f606f.
Lemma F_9df28 : fetch_word AsanUbsan.M.loaded_segments (0x9df70 : word) = Some W_9df28.
Proof. vm_refl. Qed.
Lemma D_9df28 : decode_any W_9df28 = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df2c : bv 32 := 0x01813083.
Lemma F_9df2c : fetch_word AsanUbsan.M.loaded_segments (0x9df74 : word) = Some W_9df2c.
Proof. vm_refl. Qed.
Lemma D_9df2c : decode_any W_9df2c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df30 : bv 32 := 0x01013403.
Lemma F_9df30 : fetch_word AsanUbsan.M.loaded_segments (0x9df78 : word) = Some W_9df30.
Proof. vm_refl. Qed.
Lemma D_9df30 : decode_any W_9df30 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df34 : bv 32 := 0x00813483.
Lemma F_9df34 : fetch_word AsanUbsan.M.loaded_segments (0x9df7c : word) = Some W_9df34.
Proof. vm_refl. Qed.
Lemma D_9df34 : decode_any W_9df34 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df38 : bv 32 := 0x00013903.
Lemma F_9df38 : fetch_word AsanUbsan.M.loaded_segments (0x9df80 : word) = Some W_9df38.
Proof. vm_refl. Qed.
Lemma D_9df38 : decode_any W_9df38 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df3c : bv 32 := 0x02010113.
Lemma F_9df3c : fetch_word AsanUbsan.M.loaded_segments (0x9df84 : word) = Some W_9df3c.
Proof. vm_refl. Qed.
Lemma D_9df3c : decode_any W_9df3c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df40 : bv 32 := 0x00008067.
Lemma F_9df40 : fetch_word AsanUbsan.M.loaded_segments (0x9df88 : word) = Some W_9df40.
Proof. vm_refl. Qed.
Lemma D_9df40 : decode_any W_9df40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

