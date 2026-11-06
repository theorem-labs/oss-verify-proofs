(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6dea4 : bv 32 := 0x06050863.
Lemma F_6dea4 : fetch_word Plain.M.loaded_segments (0x6defc : word) = Some W_6dea4.
Proof. vm_refl. Qed.
Lemma D_6dea4 : decode_any W_6dea4 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dea8 : bv 32 := 0xf00007d3.
Lemma F_6dea8 : fetch_word Plain.M.loaded_segments (0x6df00 : word) = Some W_6dea8.
Proof. vm_refl. Qed.
Lemma D_6dea8 : decode_any W_6dea8 = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6deac : bv 32 := 0xa0f505d3.
Lemma F_6deac : fetch_word Plain.M.loaded_segments (0x6df04 : word) = Some W_6deac.
Proof. vm_refl. Qed.
Lemma D_6deac : decode_any W_6deac = Some (Fcmp F_LE FMT_S 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6deb0 : bv 32 := 0x08059863.
Lemma F_6deb0 : fetch_word Plain.M.loaded_segments (0x6df08 : word) = Some W_6deb0.
Proof. vm_refl. Qed.
Lemma D_6deb0 : decode_any W_6deb0 = Some (Branch BC_NE 11 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6deb4 : bv 32 := 0xa0f585d3.
Lemma F_6deb4 : fetch_word Plain.M.loaded_segments (0x6df0c : word) = Some W_6deb4.
Proof. vm_refl. Qed.
Lemma D_6deb4 : decode_any W_6deb4 = Some (Fcmp F_LE FMT_S 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6deb8 : bv 32 := 0x08059463.
Lemma F_6deb8 : fetch_word Plain.M.loaded_segments (0x6df10 : word) = Some W_6deb8.
Proof. vm_refl. Qed.
Lemma D_6deb8 : decode_any W_6deb8 = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6debc : bv 32 := 0x420507d3.
Lemma F_6debc : fetch_word Plain.M.loaded_segments (0x6df14 : word) = Some W_6debc.
Proof. vm_refl. Qed.
Lemma D_6debc : decode_any W_6debc = Some (Fcvt FC_D FC_S 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dec0 : bv 32 := 0xfffb1617.
Lemma F_6dec0 : fetch_word Plain.M.loaded_segments (0x6df18 : word) = Some W_6dec0.
Proof. vm_refl. Qed.
Lemma D_6dec0 : decode_any W_6dec0 = Some (Auipc 12 1048497, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dec4 : bv 32 := 0x42058753.
Lemma F_6dec4 : fetch_word Plain.M.loaded_segments (0x6df1c : word) = Some W_6dec4.
Proof. vm_refl. Qed.
Lemma D_6dec4 : decode_any W_6dec4 = Some (Fcvt FC_D FC_S 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dec8 : bv 32 := 0xdf063687.
Lemma F_6dec8 : fetch_word Plain.M.loaded_segments (0x6df20 : word) = Some W_6dec8.
Proof. vm_refl. Qed.
Lemma D_6dec8 : decode_any W_6dec8 = Some (FLoad FMT_D 13 12 3568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6decc : bv 32 := 0x01852603.
Lemma F_6decc : fetch_word Plain.M.loaded_segments (0x6df24 : word) = Some W_6decc.
Proof. vm_refl. Qed.
Lemma D_6decc : decode_any W_6decc = Some (Load SZ4 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ded0 : bv 32 := 0xfffb1697.
Lemma F_6ded0 : fetch_word Plain.M.loaded_segments (0x6df28 : word) = Some W_6ded0.
Proof. vm_refl. Qed.
Lemma D_6ded0 : decode_any W_6ded0 = Some (Auipc 13 1048497, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ded4 : bv 32 := 0xbc06b607.
Lemma F_6ded4 : fetch_word Plain.M.loaded_segments (0x6df2c : word) = Some W_6ded4.
Proof. vm_refl. Qed.
Lemma D_6ded4 : decode_any W_6ded4 = Some (FLoad FMT_D 12 13 3008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ded8 : bv 32 := 0x01c52683.
Lemma F_6ded8 : fetch_word Plain.M.loaded_segments (0x6df30 : word) = Some W_6ded8.
Proof. vm_refl. Qed.
Lemma D_6ded8 : decode_any W_6ded8 = Some (Load SZ4 true 13 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dedc : bv 32 := 0xd00675d3.
Lemma F_6dedc : fetch_word Plain.M.loaded_segments (0x6df34 : word) = Some W_6dedc.
Proof. vm_refl. Qed.
Lemma D_6dedc : decode_any W_6dedc = Some (Fcvt FC_S FC_W 11 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dee0 : bv 32 := 0x420585d3.
Lemma F_6dee0 : fetch_word Plain.M.loaded_segments (0x6df38 : word) = Some W_6dee0.
Proof. vm_refl. Qed.
Lemma D_6dee0 : decode_any W_6dee0 = Some (Fcvt FC_D FC_S 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dee4 : bv 32 := 0x6ab7f7c3.
Lemma F_6dee4 : fetch_word Plain.M.loaded_segments (0x6df3c : word) = Some W_6dee4.
Proof. vm_refl. Qed.
Lemma D_6dee4 : decode_any W_6dee4 = Some (Fma F_MADD FMT_D 15 15 11 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6dee8 : bv 32 := 0xd006f5d3.
Lemma F_6dee8 : fetch_word Plain.M.loaded_segments (0x6df40 : word) = Some W_6dee8.
Proof. vm_refl. Qed.
Lemma D_6dee8 : decode_any W_6dee8 = Some (Fcvt FC_S FC_W 11 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6deec : bv 32 := 0x420585d3.
Lemma F_6deec : fetch_word Plain.M.loaded_segments (0x6df44 : word) = Some W_6deec.
Proof. vm_refl. Qed.
Lemma D_6deec : decode_any W_6deec = Some (Fcvt FC_D FC_S 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6def0 : bv 32 := 0x6ab77743.
Lemma F_6def0 : fetch_word Plain.M.loaded_segments (0x6df48 : word) = Some W_6def0.
Proof. vm_refl. Qed.
Lemma D_6def0 : decode_any W_6def0 = Some (Fma F_MADD FMT_D 14 14 11 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6def4 : bv 32 := 0x2ac787d3.
Lemma F_6def4 : fetch_word Plain.M.loaded_segments (0x6df4c : word) = Some W_6def4.
Proof. vm_refl. Qed.
Lemma D_6def4 : decode_any W_6def4 = Some (Fminmax F_MIN FMT_D 15 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6def8 : bv 32 := 0x2ac70753.
Lemma F_6def8 : fetch_word Plain.M.loaded_segments (0x6df50 : word) = Some W_6def8.
Proof. vm_refl. Qed.
Lemma D_6def8 : decode_any W_6def8 = Some (Fminmax F_MIN FMT_D 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6defc : bv 32 := 0xc2179653.
Lemma F_6defc : fetch_word Plain.M.loaded_segments (0x6df54 : word) = Some W_6defc.
Proof. vm_refl. Qed.
Lemma D_6defc : decode_any W_6defc = Some (Fcvt FC_WU FC_D 12 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df00 : bv 32 := 0xc21716d3.
Lemma F_6df00 : fetch_word Plain.M.loaded_segments (0x6df58 : word) = Some W_6df00.
Proof. vm_refl. Qed.
Lemma D_6df00 : decode_any W_6df00 = Some (Fcvt FC_WU FC_D 13 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df04 : bv 32 := 0x00c52c23.
Lemma F_6df04 : fetch_word Plain.M.loaded_segments (0x6df5c : word) = Some W_6df04.
Proof. vm_refl. Qed.
Lemma D_6df04 : decode_any W_6df04 = Some (Store SZ4 10 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df08 : bv 32 := 0x00d52e23.
Lemma F_6df08 : fetch_word Plain.M.loaded_segments (0x6df60 : word) = Some W_6df08.
Proof. vm_refl. Qed.
Lemma D_6df08 : decode_any W_6df08 = Some (Store SZ4 10 13 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df0c : bv 32 := 0x00058513.
Lemma F_6df0c : fetch_word Plain.M.loaded_segments (0x6df64 : word) = Some W_6df0c.
Proof. vm_refl. Qed.
Lemma D_6df0c : decode_any W_6df0c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6df10 : bv 32 := 0x00008067.
Lemma F_6df10 : fetch_word Plain.M.loaded_segments (0x6df68 : word) = Some W_6df10.
Proof. vm_refl. Qed.
Lemma D_6df10 : decode_any W_6df10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

