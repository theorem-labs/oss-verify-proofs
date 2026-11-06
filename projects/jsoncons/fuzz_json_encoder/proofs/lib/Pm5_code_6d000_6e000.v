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
Definition W_6deb4 : bv 32 := 0x060a0063.
Lemma F_6deb4 : fetch_word AsanUbsan.M.loaded_segments (0x6defc : word) = Some W_6deb4.
Proof. vm_refl. Qed.
Lemma D_6deb4 : decode_any W_6deb4 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6deb8 : bv 32 := 0x0a051c63.
Lemma F_6deb8 : fetch_word AsanUbsan.M.loaded_segments (0x6df00 : word) = Some W_6deb8.
Proof. vm_refl. Qed.
Lemma D_6deb8 : decode_any W_6deb8 = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6decc : bv 32 := 0xfbf48593.
Lemma F_6decc : fetch_word AsanUbsan.M.loaded_segments (0x6df14 : word) = Some W_6decc.
Proof. vm_refl. Qed.
Lemma D_6decc : decode_any W_6decc = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ded0 : bv 32 := 0xfbf00613.
Lemma F_6ded0 : fetch_word AsanUbsan.M.loaded_segments (0x6df18 : word) = Some W_6ded0.
Proof. vm_refl. Qed.
Lemma D_6ded0 : decode_any W_6ded0 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ded4 : bv 32 := 0x12b67663.
Lemma F_6ded4 : fetch_word AsanUbsan.M.loaded_segments (0x6df1c : word) = Some W_6ded4.
Proof. vm_refl. Qed.
Lemma D_6ded4 : decode_any W_6ded4 = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ded8 : bv 32 := 0x000f6597.
Lemma F_6ded8 : fetch_word AsanUbsan.M.loaded_segments (0x6df20 : word) = Some W_6ded8.
Proof. vm_refl. Qed.
Lemma D_6ded8 : decode_any W_6ded8 = Some (Auipc 11 246, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dedc : bv 32 := 0x5f85b583.
Lemma F_6dedc : fetch_word AsanUbsan.M.loaded_segments (0x6df24 : word) = Some W_6dedc.
Proof. vm_refl. Qed.
Lemma D_6dedc : decode_any W_6dedc = Some (Load SZ8 true 11 11 1528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dee0 : bv 32 := 0x009906b3.
Lemma F_6dee0 : fetch_word AsanUbsan.M.loaded_segments (0x6df28 : word) = Some W_6dee0.
Proof. vm_refl. Qed.
Lemma D_6dee0 : decode_any W_6dee0 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dee4 : bv 32 := 0x0005b603.
Lemma F_6dee4 : fetch_word AsanUbsan.M.loaded_segments (0x6df2c : word) = Some W_6dee4.
Proof. vm_refl. Qed.
Lemma D_6dee4 : decode_any W_6dee4 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dee8 : bv 32 := 0x00395593.
Lemma F_6dee8 : fetch_word AsanUbsan.M.loaded_segments (0x6df30 : word) = Some W_6dee8.
Proof. vm_refl. Qed.
Lemma D_6dee8 : decode_any W_6dee8 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6deec : bv 32 := 0xfff68693.
Lemma F_6deec : fetch_word AsanUbsan.M.loaded_segments (0x6df34 : word) = Some W_6deec.
Proof. vm_refl. Qed.
Lemma D_6deec : decode_any W_6deec = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6def0 : bv 32 := 0x0036d713.
Lemma F_6def0 : fetch_word AsanUbsan.M.loaded_segments (0x6df38 : word) = Some W_6def0.
Proof. vm_refl. Qed.
Lemma D_6def0 : decode_any W_6def0 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6def4 : bv 32 := 0x00b605b3.
Lemma F_6def4 : fetch_word AsanUbsan.M.loaded_segments (0x6df3c : word) = Some W_6def4.
Proof. vm_refl. Qed.
Lemma D_6def4 : decode_any W_6def4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6def8 : bv 32 := 0x00e60633.
Lemma F_6def8 : fetch_word AsanUbsan.M.loaded_segments (0x6df40 : word) = Some W_6def8.
Proof. vm_refl. Qed.
Lemma D_6def8 : decode_any W_6def8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6defc : bv 32 := 0xff85f713.
Lemma F_6defc : fetch_word AsanUbsan.M.loaded_segments (0x6df44 : word) = Some W_6defc.
Proof. vm_refl. Qed.
Lemma D_6defc : decode_any W_6defc = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df00 : bv 32 := 0xff867793.
Lemma F_6df00 : fetch_word AsanUbsan.M.loaded_segments (0x6df48 : word) = Some W_6df00.
Proof. vm_refl. Qed.
Lemma D_6df00 : decode_any W_6df00 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df04 : bv 32 := 0x00073703.
Lemma F_6df04 : fetch_word AsanUbsan.M.loaded_segments (0x6df4c : word) = Some W_6df04.
Proof. vm_refl. Qed.
Lemma D_6df04 : decode_any W_6df04 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df08 : bv 32 := 0x0007b783.
Lemma F_6df08 : fetch_word AsanUbsan.M.loaded_segments (0x6df50 : word) = Some W_6df08.
Proof. vm_refl. Qed.
Lemma D_6df08 : decode_any W_6df08 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df0c : bv 32 := 0x00e7e733.
Lemma F_6df0c : fetch_word AsanUbsan.M.loaded_segments (0x6df54 : word) = Some W_6df0c.
Proof. vm_refl. Qed.
Lemma D_6df0c : decode_any W_6df0c = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df10 : bv 32 := 0x0e071c63.
Lemma F_6df10 : fetch_word AsanUbsan.M.loaded_segments (0x6df58 : word) = Some W_6df10.
Proof. vm_refl. Qed.
Lemma D_6df10 : decode_any W_6df10 = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df70 : bv 32 := 0x412504b3.
Lemma F_6df70 : fetch_word AsanUbsan.M.loaded_segments (0x6dfb8 : word) = Some W_6df70.
Proof. vm_refl. Qed.
Lemma D_6df70 : decode_any W_6df70 = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df74 : bv 32 := 0x00148493.
Lemma F_6df74 : fetch_word AsanUbsan.M.loaded_segments (0x6dfbc : word) = Some W_6df74.
Proof. vm_refl. Qed.
Lemma D_6df74 : decode_any W_6df74 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df78 : bv 32 := 0xfff94593.
Lemma F_6df78 : fetch_word AsanUbsan.M.loaded_segments (0x6dfc0 : word) = Some W_6df78.
Proof. vm_refl. Qed.
Lemma D_6df78 : decode_any W_6df78 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df7c : bv 32 := 0x80040a13.
Lemma F_6df7c : fetch_word AsanUbsan.M.loaded_segments (0x6dfc4 : word) = Some W_6df7c.
Proof. vm_refl. Qed.
Lemma D_6df7c : decode_any W_6df7c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df80 : bv 32 := 0xfb0a0a13.
Lemma F_6df80 : fetch_word AsanUbsan.M.loaded_segments (0x6dfc8 : word) = Some W_6df80.
Proof. vm_refl. Qed.
Lemma D_6df80 : decode_any W_6df80 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df84 : bv 32 := 0xf495f4e3.
Lemma F_6df84 : fetch_word AsanUbsan.M.loaded_segments (0x6dfcc : word) = Some W_6df84.
Proof. vm_refl. Qed.
Lemma D_6df84 : decode_any W_6df84 = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

