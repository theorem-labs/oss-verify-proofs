(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5ded0 : bv 32 := 0xff010113.
Lemma F_5ded0 : fetch_word AsanUbsan.M.loaded_segments (0x5e2e8 : word) = Some W_5ded0.
Proof. vm_refl. Qed.
Lemma D_5ded0 : decode_any W_5ded0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ded4 : bv 32 := 0x00113423.
Lemma F_5ded4 : fetch_word AsanUbsan.M.loaded_segments (0x5e2ec : word) = Some W_5ded4.
Proof. vm_refl. Qed.
Lemma D_5ded4 : decode_any W_5ded4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ded8 : bv 32 := 0x00813023.
Lemma F_5ded8 : fetch_word AsanUbsan.M.loaded_segments (0x5e2f0 : word) = Some W_5ded8.
Proof. vm_refl. Qed.
Lemma D_5ded8 : decode_any W_5ded8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dedc : bv 32 := 0x7f853583.
Lemma F_5dedc : fetch_word AsanUbsan.M.loaded_segments (0x5e2f4 : word) = Some W_5dedc.
Proof. vm_refl. Qed.
Lemma D_5dedc : decode_any W_5dedc = Some (Load SZ8 true 11 10 2040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dee0 : bv 32 := 0x00000413.
Lemma F_5dee0 : fetch_word AsanUbsan.M.loaded_segments (0x5e2f8 : word) = Some W_5dee0.
Proof. vm_refl. Qed.
Lemma D_5dee0 : decode_any W_5dee0 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dee4 : bv 32 := 0x00058023.
Lemma F_5dee4 : fetch_word AsanUbsan.M.loaded_segments (0x5e2fc : word) = Some W_5dee4.
Proof. vm_refl. Qed.
Lemma D_5dee4 : decode_any W_5dee4 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5dee8 : bv 32 := 0x09c000ef.
Lemma F_5dee8 : fetch_word AsanUbsan.M.loaded_segments (0x5e300 : word) = Some W_5dee8.
Proof. vm_refl. Qed.
Lemma D_5dee8 : decode_any W_5dee8 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5deec : bv 32 := 0xfffb2597.
Lemma F_5deec : fetch_word AsanUbsan.M.loaded_segments (0x5e304 : word) = Some W_5deec.
Proof. vm_refl. Qed.
Lemma D_5deec : decode_any W_5deec = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5def0 : bv 32 := 0x07c5b583.
Lemma F_5def0 : fetch_word AsanUbsan.M.loaded_segments (0x5e308 : word) = Some W_5def0.
Proof. vm_refl. Qed.
Lemma D_5def0 : decode_any W_5def0 = Some (Load SZ8 true 11 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5def4 : bv 32 := 0x00b53023.
Lemma F_5def4 : fetch_word AsanUbsan.M.loaded_segments (0x5e30c : word) = Some W_5def4.
Proof. vm_refl. Qed.
Lemma D_5def4 : decode_any W_5def4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5def8 : bv 32 := 0x00b53423.
Lemma F_5def8 : fetch_word AsanUbsan.M.loaded_segments (0x5e310 : word) = Some W_5def8.
Proof. vm_refl. Qed.
Lemma D_5def8 : decode_any W_5def8 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5defc : bv 32 := 0x00b53823.
Lemma F_5defc : fetch_word AsanUbsan.M.loaded_segments (0x5e314 : word) = Some W_5defc.
Proof. vm_refl. Qed.
Lemma D_5defc : decode_any W_5defc = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df00 : bv 32 := 0x00b53c23.
Lemma F_5df00 : fetch_word AsanUbsan.M.loaded_segments (0x5e318 : word) = Some W_5df00.
Proof. vm_refl. Qed.
Lemma D_5df00 : decode_any W_5df00 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df04 : bv 32 := 0x02b53023.
Lemma F_5df04 : fetch_word AsanUbsan.M.loaded_segments (0x5e31c : word) = Some W_5df04.
Proof. vm_refl. Qed.
Lemma D_5df04 : decode_any W_5df04 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df08 : bv 32 := 0x02b53423.
Lemma F_5df08 : fetch_word AsanUbsan.M.loaded_segments (0x5e320 : word) = Some W_5df08.
Proof. vm_refl. Qed.
Lemma D_5df08 : decode_any W_5df08 = Some (Store SZ8 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df0c : bv 32 := 0x02b53823.
Lemma F_5df0c : fetch_word AsanUbsan.M.loaded_segments (0x5e324 : word) = Some W_5df0c.
Proof. vm_refl. Qed.
Lemma D_5df0c : decode_any W_5df0c = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df10 : bv 32 := 0x02b53c23.
Lemma F_5df10 : fetch_word AsanUbsan.M.loaded_segments (0x5e328 : word) = Some W_5df10.
Proof. vm_refl. Qed.
Lemma D_5df10 : decode_any W_5df10 = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df14 : bv 32 := 0x04b53023.
Lemma F_5df14 : fetch_word AsanUbsan.M.loaded_segments (0x5e32c : word) = Some W_5df14.
Proof. vm_refl. Qed.
Lemma D_5df14 : decode_any W_5df14 = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df18 : bv 32 := 0x04b53423.
Lemma F_5df18 : fetch_word AsanUbsan.M.loaded_segments (0x5e330 : word) = Some W_5df18.
Proof. vm_refl. Qed.
Lemma D_5df18 : decode_any W_5df18 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df1c : bv 32 := 0x04b53823.
Lemma F_5df1c : fetch_word AsanUbsan.M.loaded_segments (0x5e334 : word) = Some W_5df1c.
Proof. vm_refl. Qed.
Lemma D_5df1c : decode_any W_5df1c = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df20 : bv 32 := 0x04b53c23.
Lemma F_5df20 : fetch_word AsanUbsan.M.loaded_segments (0x5e338 : word) = Some W_5df20.
Proof. vm_refl. Qed.
Lemma D_5df20 : decode_any W_5df20 = Some (Store SZ8 10 11 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df24 : bv 32 := 0x06b53023.
Lemma F_5df24 : fetch_word AsanUbsan.M.loaded_segments (0x5e33c : word) = Some W_5df24.
Proof. vm_refl. Qed.
Lemma D_5df24 : decode_any W_5df24 = Some (Store SZ8 10 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df28 : bv 32 := 0x06b53423.
Lemma F_5df28 : fetch_word AsanUbsan.M.loaded_segments (0x5e340 : word) = Some W_5df28.
Proof. vm_refl. Qed.
Lemma D_5df28 : decode_any W_5df28 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df2c : bv 32 := 0x06b53823.
Lemma F_5df2c : fetch_word AsanUbsan.M.loaded_segments (0x5e344 : word) = Some W_5df2c.
Proof. vm_refl. Qed.
Lemma D_5df2c : decode_any W_5df2c = Some (Store SZ8 10 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df30 : bv 32 := 0x06b53c23.
Lemma F_5df30 : fetch_word AsanUbsan.M.loaded_segments (0x5e348 : word) = Some W_5df30.
Proof. vm_refl. Qed.
Lemma D_5df30 : decode_any W_5df30 = Some (Store SZ8 10 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df34 : bv 32 := 0x08b53023.
Lemma F_5df34 : fetch_word AsanUbsan.M.loaded_segments (0x5e34c : word) = Some W_5df34.
Proof. vm_refl. Qed.
Lemma D_5df34 : decode_any W_5df34 = Some (Store SZ8 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df38 : bv 32 := 0x08b53423.
Lemma F_5df38 : fetch_word AsanUbsan.M.loaded_segments (0x5e350 : word) = Some W_5df38.
Proof. vm_refl. Qed.
Lemma D_5df38 : decode_any W_5df38 = Some (Store SZ8 10 11 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df3c : bv 32 := 0x08b53823.
Lemma F_5df3c : fetch_word AsanUbsan.M.loaded_segments (0x5e354 : word) = Some W_5df3c.
Proof. vm_refl. Qed.
Lemma D_5df3c : decode_any W_5df3c = Some (Store SZ8 10 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df40 : bv 32 := 0x08b53c23.
Lemma F_5df40 : fetch_word AsanUbsan.M.loaded_segments (0x5e358 : word) = Some W_5df40.
Proof. vm_refl. Qed.
Lemma D_5df40 : decode_any W_5df40 = Some (Store SZ8 10 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df44 : bv 32 := 0x0ab53023.
Lemma F_5df44 : fetch_word AsanUbsan.M.loaded_segments (0x5e35c : word) = Some W_5df44.
Proof. vm_refl. Qed.
Lemma D_5df44 : decode_any W_5df44 = Some (Store SZ8 10 11 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df48 : bv 32 := 0x0ab53423.
Lemma F_5df48 : fetch_word AsanUbsan.M.loaded_segments (0x5e360 : word) = Some W_5df48.
Proof. vm_refl. Qed.
Lemma D_5df48 : decode_any W_5df48 = Some (Store SZ8 10 11 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df4c : bv 32 := 0x0ab53823.
Lemma F_5df4c : fetch_word AsanUbsan.M.loaded_segments (0x5e364 : word) = Some W_5df4c.
Proof. vm_refl. Qed.
Lemma D_5df4c : decode_any W_5df4c = Some (Store SZ8 10 11 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df50 : bv 32 := 0x0ab53c23.
Lemma F_5df50 : fetch_word AsanUbsan.M.loaded_segments (0x5e368 : word) = Some W_5df50.
Proof. vm_refl. Qed.
Lemma D_5df50 : decode_any W_5df50 = Some (Store SZ8 10 11 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df54 : bv 32 := 0x0cb53023.
Lemma F_5df54 : fetch_word AsanUbsan.M.loaded_segments (0x5e36c : word) = Some W_5df54.
Proof. vm_refl. Qed.
Lemma D_5df54 : decode_any W_5df54 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df58 : bv 32 := 0x0cb53423.
Lemma F_5df58 : fetch_word AsanUbsan.M.loaded_segments (0x5e370 : word) = Some W_5df58.
Proof. vm_refl. Qed.
Lemma D_5df58 : decode_any W_5df58 = Some (Store SZ8 10 11 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df5c : bv 32 := 0x0cb53823.
Lemma F_5df5c : fetch_word AsanUbsan.M.loaded_segments (0x5e374 : word) = Some W_5df5c.
Proof. vm_refl. Qed.
Lemma D_5df5c : decode_any W_5df5c = Some (Store SZ8 10 11 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df60 : bv 32 := 0x0cb53c23.
Lemma F_5df60 : fetch_word AsanUbsan.M.loaded_segments (0x5e378 : word) = Some W_5df60.
Proof. vm_refl. Qed.
Lemma D_5df60 : decode_any W_5df60 = Some (Store SZ8 10 11 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df64 : bv 32 := 0x0eb53023.
Lemma F_5df64 : fetch_word AsanUbsan.M.loaded_segments (0x5e37c : word) = Some W_5df64.
Proof. vm_refl. Qed.
Lemma D_5df64 : decode_any W_5df64 = Some (Store SZ8 10 11 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df68 : bv 32 := 0x0eb53423.
Lemma F_5df68 : fetch_word AsanUbsan.M.loaded_segments (0x5e380 : word) = Some W_5df68.
Proof. vm_refl. Qed.
Lemma D_5df68 : decode_any W_5df68 = Some (Store SZ8 10 11 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df6c : bv 32 := 0x0eb53823.
Lemma F_5df6c : fetch_word AsanUbsan.M.loaded_segments (0x5e384 : word) = Some W_5df6c.
Proof. vm_refl. Qed.
Lemma D_5df6c : decode_any W_5df6c = Some (Store SZ8 10 11 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df70 : bv 32 := 0x0eb53c23.
Lemma F_5df70 : fetch_word AsanUbsan.M.loaded_segments (0x5e388 : word) = Some W_5df70.
Proof. vm_refl. Qed.
Lemma D_5df70 : decode_any W_5df70 = Some (Store SZ8 10 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df74 : bv 32 := 0x00813083.
Lemma F_5df74 : fetch_word AsanUbsan.M.loaded_segments (0x5e38c : word) = Some W_5df74.
Proof. vm_refl. Qed.
Lemma D_5df74 : decode_any W_5df74 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df78 : bv 32 := 0x00013403.
Lemma F_5df78 : fetch_word AsanUbsan.M.loaded_segments (0x5e390 : word) = Some W_5df78.
Proof. vm_refl. Qed.
Lemma D_5df78 : decode_any W_5df78 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df7c : bv 32 := 0x01010113.
Lemma F_5df7c : fetch_word AsanUbsan.M.loaded_segments (0x5e394 : word) = Some W_5df7c.
Proof. vm_refl. Qed.
Lemma D_5df7c : decode_any W_5df7c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5df80 : bv 32 := 0x00008067.
Lemma F_5df80 : fetch_word AsanUbsan.M.loaded_segments (0x5e398 : word) = Some W_5df80.
Proof. vm_refl. Qed.
Lemma D_5df80 : decode_any W_5df80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
