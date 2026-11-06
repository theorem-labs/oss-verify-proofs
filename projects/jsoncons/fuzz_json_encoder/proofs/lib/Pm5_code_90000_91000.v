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
Definition W_90978 : bv 32 := 0x000d4597.
Lemma F_90978 : fetch_word AsanUbsan.M.loaded_segments (0x909c0 : word) = Some W_90978.
Proof. vm_refl. Qed.
Lemma D_90978 : decode_any W_90978 = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9097c : bv 32 := 0xb485b583.
Lemma F_9097c : fetch_word AsanUbsan.M.loaded_segments (0x909c4 : word) = Some W_9097c.
Proof. vm_refl. Qed.
Lemma D_9097c : decode_any W_9097c = Some (Load SZ8 true 11 11 2888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90980 : bv 32 := 0x0905b583.
Lemma F_90980 : fetch_word AsanUbsan.M.loaded_segments (0x909c8 : word) = Some W_90980.
Proof. vm_refl. Qed.
Lemma D_90980 : decode_any W_90980 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90984 : bv 32 := 0x00058e63.
Lemma F_90984 : fetch_word AsanUbsan.M.loaded_segments (0x909cc : word) = Some W_90984.
Proof. vm_refl. Qed.
Lemma D_90984 : decode_any W_90984 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_909a0 : bv 32 := 0x00008067.
Lemma F_909a0 : fetch_word AsanUbsan.M.loaded_segments (0x909e8 : word) = Some W_909a0.
Proof. vm_refl. Qed.
Lemma D_909a0 : decode_any W_909a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_909bc : bv 32 := 0x000d4597.
Lemma F_909bc : fetch_word AsanUbsan.M.loaded_segments (0x90a04 : word) = Some W_909bc.
Proof. vm_refl. Qed.
Lemma D_909bc : decode_any W_909bc = Some (Auipc 11 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_909c0 : bv 32 := 0xb045b583.
Lemma F_909c0 : fetch_word AsanUbsan.M.loaded_segments (0x90a08 : word) = Some W_909c0.
Proof. vm_refl. Qed.
Lemma D_909c0 : decode_any W_909c0 = Some (Load SZ8 true 11 11 2820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_909c4 : bv 32 := 0x0905b583.
Lemma F_909c4 : fetch_word AsanUbsan.M.loaded_segments (0x90a0c : word) = Some W_909c4.
Proof. vm_refl. Qed.
Lemma D_909c4 : decode_any W_909c4 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_909c8 : bv 32 := 0x00058a63.
Lemma F_909c8 : fetch_word AsanUbsan.M.loaded_segments (0x90a10 : word) = Some W_909c8.
Proof. vm_refl. Qed.
Lemma D_909c8 : decode_any W_909c8 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_909dc : bv 32 := 0x00008067.
Lemma F_909dc : fetch_word AsanUbsan.M.loaded_segments (0x90a24 : word) = Some W_909dc.
Proof. vm_refl. Qed.
Lemma D_909dc : decode_any W_909dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90eec : bv 32 := 0xfe010113.
Lemma F_90eec : fetch_word AsanUbsan.M.loaded_segments (0x90f34 : word) = Some W_90eec.
Proof. vm_refl. Qed.
Lemma D_90eec : decode_any W_90eec = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90ef0 : bv 32 := 0x00113c23.
Lemma F_90ef0 : fetch_word AsanUbsan.M.loaded_segments (0x90f38 : word) = Some W_90ef0.
Proof. vm_refl. Qed.
Lemma D_90ef0 : decode_any W_90ef0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90ef4 : bv 32 := 0x00813823.
Lemma F_90ef4 : fetch_word AsanUbsan.M.loaded_segments (0x90f3c : word) = Some W_90ef4.
Proof. vm_refl. Qed.
Lemma D_90ef4 : decode_any W_90ef4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90ef8 : bv 32 := 0x00913423.
Lemma F_90ef8 : fetch_word AsanUbsan.M.loaded_segments (0x90f40 : word) = Some W_90ef8.
Proof. vm_refl. Qed.
Lemma D_90ef8 : decode_any W_90ef8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90efc : bv 32 := 0x01213023.
Lemma F_90efc : fetch_word AsanUbsan.M.loaded_segments (0x90f44 : word) = Some W_90efc.
Proof. vm_refl. Qed.
Lemma D_90efc : decode_any W_90efc = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f00 : bv 32 := 0x00058413.
Lemma F_90f00 : fetch_word AsanUbsan.M.loaded_segments (0x90f48 : word) = Some W_90f00.
Proof. vm_refl. Qed.
Lemma D_90f00 : decode_any W_90f00 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f04 : bv 32 := 0x00050493.
Lemma F_90f04 : fetch_word AsanUbsan.M.loaded_segments (0x90f4c : word) = Some W_90f04.
Proof. vm_refl. Qed.
Lemma D_90f04 : decode_any W_90f04 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f08 : bv 32 := 0x09c000ef.
Lemma F_90f08 : fetch_word AsanUbsan.M.loaded_segments (0x90f50 : word) = Some W_90f08.
Proof. vm_refl. Qed.
Lemma D_90f08 : decode_any W_90f08 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f0c : bv 32 := 0x0016e517.
Lemma F_90f0c : fetch_word AsanUbsan.M.loaded_segments (0x90f54 : word) = Some W_90f0c.
Proof. vm_refl. Qed.
Lemma D_90f0c : decode_any W_90f0c = Some (Auipc 10 366, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f10 : bv 32 := 0x32c50913.
Lemma F_90f10 : fetch_word AsanUbsan.M.loaded_segments (0x90f58 : word) = Some W_90f10.
Proof. vm_refl. Qed.
Lemma D_90f10 : decode_any W_90f10 = Some (OpImm ALU_ADD 18 10 812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f14 : bv 32 := 0x00093603.
Lemma F_90f14 : fetch_word AsanUbsan.M.loaded_segments (0x90f5c : word) = Some W_90f14.
Proof. vm_refl. Qed.
Lemma D_90f14 : decode_any W_90f14 = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f18 : bv 32 := 0x06060a63.
Lemma F_90f18 : fetch_word AsanUbsan.M.loaded_segments (0x90f60 : word) = Some W_90f18.
Proof. vm_refl. Qed.
Lemma D_90f18 : decode_any W_90f18 = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f8c : bv 32 := 0x01813083.
Lemma F_90f8c : fetch_word AsanUbsan.M.loaded_segments (0x90fd4 : word) = Some W_90f8c.
Proof. vm_refl. Qed.
Lemma D_90f8c : decode_any W_90f8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f90 : bv 32 := 0x01013403.
Lemma F_90f90 : fetch_word AsanUbsan.M.loaded_segments (0x90fd8 : word) = Some W_90f90.
Proof. vm_refl. Qed.
Lemma D_90f90 : decode_any W_90f90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f94 : bv 32 := 0x00813483.
Lemma F_90f94 : fetch_word AsanUbsan.M.loaded_segments (0x90fdc : word) = Some W_90f94.
Proof. vm_refl. Qed.
Lemma D_90f94 : decode_any W_90f94 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f98 : bv 32 := 0x00013903.
Lemma F_90f98 : fetch_word AsanUbsan.M.loaded_segments (0x90fe0 : word) = Some W_90f98.
Proof. vm_refl. Qed.
Lemma D_90f98 : decode_any W_90f98 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90f9c : bv 32 := 0x02010113.
Lemma F_90f9c : fetch_word AsanUbsan.M.loaded_segments (0x90fe4 : word) = Some W_90f9c.
Proof. vm_refl. Qed.
Lemma D_90f9c : decode_any W_90f9c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fa0 : bv 32 := 0x00008067.
Lemma F_90fa0 : fetch_word AsanUbsan.M.loaded_segments (0x90fe8 : word) = Some W_90fa0.
Proof. vm_refl. Qed.
Lemma D_90fa0 : decode_any W_90fa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fa4 : bv 32 := 0x00008067.
Lemma F_90fa4 : fetch_word AsanUbsan.M.loaded_segments (0x90fec : word) = Some W_90fa4.
Proof. vm_refl. Qed.
Lemma D_90fa4 : decode_any W_90fa4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fa8 : bv 32 := 0xfe010113.
Lemma F_90fa8 : fetch_word AsanUbsan.M.loaded_segments (0x90ff0 : word) = Some W_90fa8.
Proof. vm_refl. Qed.
Lemma D_90fa8 : decode_any W_90fa8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fac : bv 32 := 0x00113c23.
Lemma F_90fac : fetch_word AsanUbsan.M.loaded_segments (0x90ff4 : word) = Some W_90fac.
Proof. vm_refl. Qed.
Lemma D_90fac : decode_any W_90fac = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fb0 : bv 32 := 0x00813823.
Lemma F_90fb0 : fetch_word AsanUbsan.M.loaded_segments (0x90ff8 : word) = Some W_90fb0.
Proof. vm_refl. Qed.
Lemma D_90fb0 : decode_any W_90fb0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fb4 : bv 32 := 0x00913423.
Lemma F_90fb4 : fetch_word AsanUbsan.M.loaded_segments (0x90ffc : word) = Some W_90fb4.
Proof. vm_refl. Qed.
Lemma D_90fb4 : decode_any W_90fb4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fb8 : bv 32 := 0x00050413.
Lemma F_90fb8 : fetch_word AsanUbsan.M.loaded_segments (0x91000 : word) = Some W_90fb8.
Proof. vm_refl. Qed.
Lemma D_90fb8 : decode_any W_90fb8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fbc : bv 32 := 0x098000ef.
Lemma F_90fbc : fetch_word AsanUbsan.M.loaded_segments (0x91004 : word) = Some W_90fbc.
Proof. vm_refl. Qed.
Lemma D_90fbc : decode_any W_90fbc = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fc0 : bv 32 := 0x00050e63.
Lemma F_90fc0 : fetch_word AsanUbsan.M.loaded_segments (0x91008 : word) = Some W_90fc0.
Proof. vm_refl. Qed.
Lemma D_90fc0 : decode_any W_90fc0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fdc : bv 32 := 0x00040513.
Lemma F_90fdc : fetch_word AsanUbsan.M.loaded_segments (0x91024 : word) = Some W_90fdc.
Proof. vm_refl. Qed.
Lemma D_90fdc : decode_any W_90fdc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fe0 : bv 32 := 0x07c000ef.
Lemma F_90fe0 : fetch_word AsanUbsan.M.loaded_segments (0x91028 : word) = Some W_90fe0.
Proof. vm_refl. Qed.
Lemma D_90fe0 : decode_any W_90fe0 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fe4 : bv 32 := 0x0016e517.
Lemma F_90fe4 : fetch_word AsanUbsan.M.loaded_segments (0x9102c : word) = Some W_90fe4.
Proof. vm_refl. Qed.
Lemma D_90fe4 : decode_any W_90fe4 = Some (Auipc 10 366, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fe8 : bv 32 := 0x25450493.
Lemma F_90fe8 : fetch_word AsanUbsan.M.loaded_segments (0x91030 : word) = Some W_90fe8.
Proof. vm_refl. Qed.
Lemma D_90fe8 : decode_any W_90fe8 = Some (OpImm ALU_ADD 9 10 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90fec : bv 32 := 0x0084b583.
Lemma F_90fec : fetch_word AsanUbsan.M.loaded_segments (0x91034 : word) = Some W_90fec.
Proof. vm_refl. Qed.
Lemma D_90fec : decode_any W_90fec = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90ff0 : bv 32 := 0x04058663.
Lemma F_90ff0 : fetch_word AsanUbsan.M.loaded_segments (0x91038 : word) = Some W_90ff0.
Proof. vm_refl. Qed.
Lemma D_90ff0 : decode_any W_90ff0 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

