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
Definition Wx_84638 : bv 32 := 0x00058613.
Lemma Fx_84638 : fetch_word AsanUbsan.M.loaded_segments (0x84680 : word) = Some Wx_84638.
Proof. vm_refl. Qed.
Lemma Dx_84638 : decode_any Wx_84638 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8463c : bv 32 := 0x000e0597.
Lemma Fx_8463c : fetch_word AsanUbsan.M.loaded_segments (0x84684 : word) = Some Wx_8463c.
Proof. vm_refl. Qed.
Lemma Dx_8463c : decode_any Wx_8463c = Some (Auipc 11 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84640 : bv 32 := 0xeb45b583.
Lemma Fx_84640 : fetch_word AsanUbsan.M.loaded_segments (0x84688 : word) = Some Wx_84640.
Proof. vm_refl. Qed.
Lemma Dx_84640 : decode_any Wx_84640 = Some (Load SZ8 true 11 11 3764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84644 : bv 32 := 0x0005b303.
Lemma Fx_84644 : fetch_word AsanUbsan.M.loaded_segments (0x8468c : word) = Some Wx_84644.
Proof. vm_refl. Qed.
Lemma Dx_84644 : decode_any Wx_84644 = Some (Load SZ8 true 6 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84648 : bv 32 := 0x00000593.
Lemma Fx_84648 : fetch_word AsanUbsan.M.loaded_segments (0x84690 : word) = Some Wx_84648.
Proof. vm_refl. Qed.
Lemma Dx_84648 : decode_any Wx_84648 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8464c : bv 32 := 0x00030067.
Lemma Fx_8464c : fetch_word AsanUbsan.M.loaded_segments (0x84694 : word) = Some Wx_8464c.
Proof. vm_refl. Qed.
Lemma Dx_8464c : decode_any Wx_8464c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84740 : bv 32 := 0x000e0617.
Lemma Fx_84740 : fetch_word AsanUbsan.M.loaded_segments (0x84788 : word) = Some Wx_84740.
Proof. vm_refl. Qed.
Lemma Dx_84740 : decode_any Wx_84740 = Some (Auipc 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84744 : bv 32 := 0xdb063603.
Lemma Fx_84744 : fetch_word AsanUbsan.M.loaded_segments (0x8478c : word) = Some Wx_84744.
Proof. vm_refl. Qed.
Lemma Dx_84744 : decode_any Wx_84744 = Some (Load SZ8 true 12 12 3504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84748 : bv 32 := 0x00063303.
Lemma Fx_84748 : fetch_word AsanUbsan.M.loaded_segments (0x84790 : word) = Some Wx_84748.
Proof. vm_refl. Qed.
Lemma Dx_84748 : decode_any Wx_84748 = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8474c : bv 32 := 0x00058613.
Lemma Fx_8474c : fetch_word AsanUbsan.M.loaded_segments (0x84794 : word) = Some Wx_8474c.
Proof. vm_refl. Qed.
Lemma Dx_8474c : decode_any Wx_8474c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84750 : bv 32 := 0x0f500593.
Lemma Fx_84750 : fetch_word AsanUbsan.M.loaded_segments (0x84798 : word) = Some Wx_84750.
Proof. vm_refl. Qed.
Lemma Dx_84750 : decode_any Wx_84750 = Some (OpImm ALU_ADD 11 0 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84754 : bv 32 := 0x00030067.
Lemma Fx_84754 : fetch_word AsanUbsan.M.loaded_segments (0x8479c : word) = Some Wx_84754.
Proof. vm_refl. Qed.
Lemma Dx_84754 : decode_any Wx_84754 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84758 : bv 32 := 0x000e0617.
Lemma Fx_84758 : fetch_word AsanUbsan.M.loaded_segments (0x847a0 : word) = Some Wx_84758.
Proof. vm_refl. Qed.
Lemma Dx_84758 : decode_any Wx_84758 = Some (Auipc 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8475c : bv 32 := 0xd9863603.
Lemma Fx_8475c : fetch_word AsanUbsan.M.loaded_segments (0x847a4 : word) = Some Wx_8475c.
Proof. vm_refl. Qed.
Lemma Dx_8475c : decode_any Wx_8475c = Some (Load SZ8 true 12 12 3480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84760 : bv 32 := 0x00063303.
Lemma Fx_84760 : fetch_word AsanUbsan.M.loaded_segments (0x847a8 : word) = Some Wx_84760.
Proof. vm_refl. Qed.
Lemma Dx_84760 : decode_any Wx_84760 = Some (Load SZ8 true 6 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84764 : bv 32 := 0x00058613.
Lemma Fx_84764 : fetch_word AsanUbsan.M.loaded_segments (0x847ac : word) = Some Wx_84764.
Proof. vm_refl. Qed.
Lemma Dx_84764 : decode_any Wx_84764 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84768 : bv 32 := 0x0f800593.
Lemma Fx_84768 : fetch_word AsanUbsan.M.loaded_segments (0x847b0 : word) = Some Wx_84768.
Proof. vm_refl. Qed.
Lemma Dx_84768 : decode_any Wx_84768 = Some (OpImm ALU_ADD 11 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8476c : bv 32 := 0x00030067.
Lemma Fx_8476c : fetch_word AsanUbsan.M.loaded_segments (0x847b4 : word) = Some Wx_8476c.
Proof. vm_refl. Qed.
Lemma Dx_8476c : decode_any Wx_8476c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

