(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7cbd8 : bv 32 := 0x81010113.
Lemma F_7cbd8 : fetch_word AsanUbsan.M.loaded_segments (0x7cc28 : word) = Some W_7cbd8.
Proof. vm_refl. Qed.
Lemma D_7cbd8 : decode_any W_7cbd8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbdc : bv 32 := 0x7e113423.
Lemma F_7cbdc : fetch_word AsanUbsan.M.loaded_segments (0x7cc2c : word) = Some W_7cbdc.
Proof. vm_refl. Qed.
Lemma D_7cbdc : decode_any W_7cbdc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbe0 : bv 32 := 0x7e813023.
Lemma F_7cbe0 : fetch_word AsanUbsan.M.loaded_segments (0x7cc30 : word) = Some W_7cbe0.
Proof. vm_refl. Qed.
Lemma D_7cbe0 : decode_any W_7cbe0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbe4 : bv 32 := 0x7c913c23.
Lemma F_7cbe4 : fetch_word AsanUbsan.M.loaded_segments (0x7cc34 : word) = Some W_7cbe4.
Proof. vm_refl. Qed.
Lemma D_7cbe4 : decode_any W_7cbe4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbe8 : bv 32 := 0x7d213823.
Lemma F_7cbe8 : fetch_word AsanUbsan.M.loaded_segments (0x7cc38 : word) = Some W_7cbe8.
Proof. vm_refl. Qed.
Lemma D_7cbe8 : decode_any W_7cbe8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbec : bv 32 := 0x7d313423.
Lemma F_7cbec : fetch_word AsanUbsan.M.loaded_segments (0x7cc3c : word) = Some W_7cbec.
Proof. vm_refl. Qed.
Lemma D_7cbec : decode_any W_7cbec = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbf0 : bv 32 := 0x7d413023.
Lemma F_7cbf0 : fetch_word AsanUbsan.M.loaded_segments (0x7cc40 : word) = Some W_7cbf0.
Proof. vm_refl. Qed.
Lemma D_7cbf0 : decode_any W_7cbf0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbf4 : bv 32 := 0x7b513c23.
Lemma F_7cbf4 : fetch_word AsanUbsan.M.loaded_segments (0x7cc44 : word) = Some W_7cbf4.
Proof. vm_refl. Qed.
Lemma D_7cbf4 : decode_any W_7cbf4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbf8 : bv 32 := 0x7f010413.
Lemma F_7cbf8 : fetch_word AsanUbsan.M.loaded_segments (0x7cc48 : word) = Some W_7cbf8.
Proof. vm_refl. Qed.
Lemma D_7cbf8 : decode_any W_7cbf8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cbfc : bv 32 := 0xfa010113.
Lemma F_7cbfc : fetch_word AsanUbsan.M.loaded_segments (0x7cc4c : word) = Some W_7cbfc.
Proof. vm_refl. Qed.
Lemma D_7cbfc : decode_any W_7cbfc = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc00 : bv 32 := 0x00058a13.
Lemma F_7cc00 : fetch_word AsanUbsan.M.loaded_segments (0x7cc50 : word) = Some W_7cc00.
Proof. vm_refl. Qed.
Lemma D_7cc00 : decode_any W_7cc00 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc04 : bv 32 := 0x000c1597.
Lemma F_7cc04 : fetch_word AsanUbsan.M.loaded_segments (0x7cc54 : word) = Some W_7cc04.
Proof. vm_refl. Qed.
Lemma D_7cc04 : decode_any W_7cc04 = Some (Auipc 11 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc08 : bv 32 := 0xc6c5b583.
Lemma F_7cc08 : fetch_word AsanUbsan.M.loaded_segments (0x7cc58 : word) = Some W_7cc08.
Proof. vm_refl. Qed.
Lemma D_7cc08 : decode_any W_7cc08 = Some (Load SZ8 true 11 11 3180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc0c : bv 32 := 0x0605c583.
Lemma F_7cc0c : fetch_word AsanUbsan.M.loaded_segments (0x7cc5c : word) = Some W_7cc0c.
Proof. vm_refl. Qed.
Lemma D_7cc0c : decode_any W_7cc0c = Some (Load SZ1 false 11 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc10 : bv 32 := 0x22058863.
Lemma F_7cc10 : fetch_word AsanUbsan.M.loaded_segments (0x7cc60 : word) = Some W_7cc10.
Proof. vm_refl. Qed.
Lemma D_7cc10 : decode_any W_7cc10 = Some (Branch BC_EQ 11 0 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc14 : bv 32 := 0x00068913.
Lemma F_7cc14 : fetch_word AsanUbsan.M.loaded_segments (0x7cc64 : word) = Some W_7cc14.
Proof. vm_refl. Qed.
Lemma D_7cc14 : decode_any W_7cc14 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc18 : bv 32 := 0x00060993.
Lemma F_7cc18 : fetch_word AsanUbsan.M.loaded_segments (0x7cc68 : word) = Some W_7cc18.
Proof. vm_refl. Qed.
Lemma D_7cc18 : decode_any W_7cc18 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc1c : bv 32 := 0x00050493.
Lemma F_7cc1c : fetch_word AsanUbsan.M.loaded_segments (0x7cc6c : word) = Some W_7cc1c.
Proof. vm_refl. Qed.
Lemma D_7cc1c : decode_any W_7cc1c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc20 : bv 32 := 0x000c1517.
Lemma F_7cc20 : fetch_word AsanUbsan.M.loaded_segments (0x7cc70 : word) = Some W_7cc20.
Proof. vm_refl. Qed.
Lemma D_7cc20 : decode_any W_7cc20 = Some (Auipc 10 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc24 : bv 32 := 0xca853503.
Lemma F_7cc24 : fetch_word AsanUbsan.M.loaded_segments (0x7cc74 : word) = Some W_7cc24.
Proof. vm_refl. Qed.
Lemma D_7cc24 : decode_any W_7cc24 = Some (Load SZ8 true 10 10 3240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc28 : bv 32 := 0x00052503.
Lemma F_7cc28 : fetch_word AsanUbsan.M.loaded_segments (0x7cc78 : word) = Some W_7cc28.
Proof. vm_refl. Qed.
Lemma D_7cc28 : decode_any W_7cc28 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc2c : bv 32 := 0x00300593.
Lemma F_7cc2c : fetch_word AsanUbsan.M.loaded_segments (0x7cc7c : word) = Some W_7cc2c.
Proof. vm_refl. Qed.
Lemma D_7cc2c : decode_any W_7cc2c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc30 : bv 32 := 0x08b57063.
Lemma F_7cc30 : fetch_word AsanUbsan.M.loaded_segments (0x7cc80 : word) = Some W_7cc30.
Proof. vm_refl. Qed.
Lemma D_7cc30 : decode_any W_7cc30 = Some (Branch BC_GEU 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc34 : bv 32 := 0x0899fe63.
Lemma F_7cc34 : fetch_word AsanUbsan.M.loaded_segments (0x7cc84 : word) = Some W_7cc34.
Proof. vm_refl. Qed.
Lemma D_7cc34 : decode_any W_7cc34 = Some (Branch BC_GEU 19 9 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc38 : bv 32 := 0x80040513.
Lemma F_7cc38 : fetch_word AsanUbsan.M.loaded_segments (0x7cc88 : word) = Some W_7cc38.
Proof. vm_refl. Qed.
Lemma D_7cc38 : decode_any W_7cc38 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc3c : bv 32 := 0xfb050513.
Lemma F_7cc3c : fetch_word AsanUbsan.M.loaded_segments (0x7cc8c : word) = Some W_7cc3c.
Proof. vm_refl. Qed.
Lemma D_7cc3c : decode_any W_7cc3c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc40 : bv 32 := 0x80040593.
Lemma F_7cc40 : fetch_word AsanUbsan.M.loaded_segments (0x7cc90 : word) = Some W_7cc40.
Proof. vm_refl. Qed.
Lemma D_7cc40 : decode_any W_7cc40 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc44 : bv 32 := 0xfc058593.
Lemma F_7cc44 : fetch_word AsanUbsan.M.loaded_segments (0x7cc94 : word) = Some W_7cc44.
Proof. vm_refl. Qed.
Lemma D_7cc44 : decode_any W_7cc44 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc48 : bv 32 := 0x80040613.
Lemma F_7cc48 : fetch_word AsanUbsan.M.loaded_segments (0x7cc98 : word) = Some W_7cc48.
Proof. vm_refl. Qed.
Lemma D_7cc48 : decode_any W_7cc48 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc4c : bv 32 := 0xfb060613.
Lemma F_7cc4c : fetch_word AsanUbsan.M.loaded_segments (0x7cc9c : word) = Some W_7cc4c.
Proof. vm_refl. Qed.
Lemma D_7cc4c : decode_any W_7cc4c = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc50 : bv 32 := 0x7ff60a93.
Lemma F_7cc50 : fetch_word AsanUbsan.M.loaded_segments (0x7cca0 : word) = Some W_7cc50.
Proof. vm_refl. Qed.
Lemma D_7cc50 : decode_any W_7cc50 = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc54 : bv 32 := 0x000ab4a3.
Lemma F_7cc54 : fetch_word AsanUbsan.M.loaded_segments (0x7cca4 : word) = Some W_7cc54.
Proof. vm_refl. Qed.
Lemma D_7cc54 : decode_any W_7cc54 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc58 : bv 32 := 0x00b53023.
Lemma F_7cc58 : fetch_word AsanUbsan.M.loaded_segments (0x7cca8 : word) = Some W_7cc58.
Proof. vm_refl. Qed.
Lemma D_7cc58 : decode_any W_7cc58 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc5c : bv 32 := 0x00053423.
Lemma F_7cc5c : fetch_word AsanUbsan.M.loaded_segments (0x7ccac : word) = Some W_7cc5c.
Proof. vm_refl. Qed.
Lemma D_7cc5c : decode_any W_7cc5c = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc60 : bv 32 := 0x6451e0ef.
Lemma F_7cc60 : fetch_word AsanUbsan.M.loaded_segments (0x7ccb0 : word) = Some W_7cc60.
Proof. vm_refl. Qed.
Lemma D_7cc60 : decode_any W_7cc60 = Some (Jal 1 126532, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc64 : bv 32 := 0x00050593.
Lemma F_7cc64 : fetch_word AsanUbsan.M.loaded_segments (0x7ccb4 : word) = Some W_7cc64.
Proof. vm_refl. Qed.
Lemma D_7cc64 : decode_any W_7cc64 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc68 : bv 32 := 0x000c1517.
Lemma F_7cc68 : fetch_word AsanUbsan.M.loaded_segments (0x7ccb8 : word) = Some W_7cc68.
Proof. vm_refl. Qed.
Lemma D_7cc68 : decode_any W_7cc68 = Some (Auipc 10 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc6c : bv 32 := 0xc0053503.
Lemma F_7cc6c : fetch_word AsanUbsan.M.loaded_segments (0x7ccbc : word) = Some W_7cc6c.
Proof. vm_refl. Qed.
Lemma D_7cc6c : decode_any W_7cc6c = Some (Load SZ8 true 10 10 3072, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc70 : bv 32 := 0x02154703.
Lemma F_7cc70 : fetch_word AsanUbsan.M.loaded_segments (0x7ccc0 : word) = Some W_7cc70.
Proof. vm_refl. Qed.
Lemma D_7cc70 : decode_any W_7cc70 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc74 : bv 32 := 0x008ab4a3.
Lemma F_7cc74 : fetch_word AsanUbsan.M.loaded_segments (0x7ccc4 : word) = Some W_7cc74.
Proof. vm_refl. Qed.
Lemma D_7cc74 : decode_any W_7cc74 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc78 : bv 32 := 0x80040513.
Lemma F_7cc78 : fetch_word AsanUbsan.M.loaded_segments (0x7ccc8 : word) = Some W_7cc78.
Proof. vm_refl. Qed.
Lemma D_7cc78 : decode_any W_7cc78 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc7c : bv 32 := 0xfb050513.
Lemma F_7cc7c : fetch_word AsanUbsan.M.loaded_segments (0x7cccc : word) = Some W_7cc7c.
Proof. vm_refl. Qed.
Lemma D_7cc7c : decode_any W_7cc7c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc80 : bv 32 := 0x0ff00793.
Lemma F_7cc80 : fetch_word AsanUbsan.M.loaded_segments (0x7ccd0 : word) = Some W_7cc80.
Proof. vm_refl. Qed.
Lemma D_7cc80 : decode_any W_7cc80 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc84 : bv 32 := 0x00040613.
Lemma F_7cc84 : fetch_word AsanUbsan.M.loaded_segments (0x7ccd4 : word) = Some W_7cc84.
Proof. vm_refl. Qed.
Lemma D_7cc84 : decode_any W_7cc84 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc88 : bv 32 := 0x00000693.
Lemma F_7cc88 : fetch_word AsanUbsan.M.loaded_segments (0x7ccd8 : word) = Some W_7cc88.
Proof. vm_refl. Qed.
Lemma D_7cc88 : decode_any W_7cc88 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc8c : bv 32 := 0x34c060ef.
Lemma F_7cc8c : fetch_word AsanUbsan.M.loaded_segments (0x7ccdc : word) = Some W_7cc8c.
Proof. vm_refl. Qed.
Lemma D_7cc8c : decode_any W_7cc8c = Some (Jal 1 25420, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc90 : bv 32 := 0x80040713.
Lemma F_7cc90 : fetch_word AsanUbsan.M.loaded_segments (0x7cce0 : word) = Some W_7cc90.
Proof. vm_refl. Qed.
Lemma D_7cc90 : decode_any W_7cc90 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc94 : bv 32 := 0xfb070713.
Lemma F_7cc94 : fetch_word AsanUbsan.M.loaded_segments (0x7cce4 : word) = Some W_7cc94.
Proof. vm_refl. Qed.
Lemma D_7cc94 : decode_any W_7cc94 = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc98 : bv 32 := 0x00048513.
Lemma F_7cc98 : fetch_word AsanUbsan.M.loaded_segments (0x7cce8 : word) = Some W_7cc98.
Proof. vm_refl. Qed.
Lemma D_7cc98 : decode_any W_7cc98 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cc9c : bv 32 := 0x000a0593.
Lemma F_7cc9c : fetch_word AsanUbsan.M.loaded_segments (0x7ccec : word) = Some W_7cc9c.
Proof. vm_refl. Qed.
Lemma D_7cc9c : decode_any W_7cc9c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cca0 : bv 32 := 0x00098613.
Lemma F_7cca0 : fetch_word AsanUbsan.M.loaded_segments (0x7ccf0 : word) = Some W_7cca0.
Proof. vm_refl. Qed.
Lemma D_7cca0 : decode_any W_7cca0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cca4 : bv 32 := 0x00090693.
Lemma F_7cca4 : fetch_word AsanUbsan.M.loaded_segments (0x7ccf4 : word) = Some W_7cca4.
Proof. vm_refl. Qed.
Lemma D_7cca4 : decode_any W_7cca4 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cca8 : bv 32 := 0x0e0030ef.
Lemma F_7cca8 : fetch_word AsanUbsan.M.loaded_segments (0x7ccf8 : word) = Some W_7cca8.
Proof. vm_refl. Qed.
Lemma D_7cca8 : decode_any W_7cca8 = Some (Jal 1 12512, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccac : bv 32 := 0x0300006f.
Lemma F_7ccac : fetch_word AsanUbsan.M.loaded_segments (0x7ccfc : word) = Some W_7ccac.
Proof. vm_refl. Qed.
Lemma D_7ccac : decode_any W_7ccac = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccb0 : bv 32 := 0xfff9c517.
Lemma F_7ccb0 : fetch_word AsanUbsan.M.loaded_segments (0x7cd00 : word) = Some W_7ccb0.
Proof. vm_refl. Qed.
Lemma D_7ccb0 : decode_any W_7ccb0 = Some (Auipc 10 1048476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccb4 : bv 32 := 0x7b950513.
Lemma F_7ccb4 : fetch_word AsanUbsan.M.loaded_segments (0x7cd04 : word) = Some W_7ccb4.
Proof. vm_refl. Qed.
Lemma D_7ccb4 : decode_any W_7ccb4 = Some (OpImm ALU_ADD 10 10 1977, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccb8 : bv 32 := 0x00048593.
Lemma F_7ccb8 : fetch_word AsanUbsan.M.loaded_segments (0x7cd08 : word) = Some W_7ccb8.
Proof. vm_refl. Qed.
Lemma D_7ccb8 : decode_any W_7ccb8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccbc : bv 32 := 0x000a0613.
Lemma F_7ccbc : fetch_word AsanUbsan.M.loaded_segments (0x7cd0c : word) = Some W_7ccbc.
Proof. vm_refl. Qed.
Lemma D_7ccbc : decode_any W_7ccbc = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccc0 : bv 32 := 0x00098693.
Lemma F_7ccc0 : fetch_word AsanUbsan.M.loaded_segments (0x7cd10 : word) = Some W_7ccc0.
Proof. vm_refl. Qed.
Lemma D_7ccc0 : decode_any W_7ccc0 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccc4 : bv 32 := 0x00090713.
Lemma F_7ccc4 : fetch_word AsanUbsan.M.loaded_segments (0x7cd14 : word) = Some W_7ccc4.
Proof. vm_refl. Qed.
Lemma D_7ccc4 : decode_any W_7ccc4 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccc8 : bv 32 := 0x491120ef.
Lemma F_7ccc8 : fetch_word AsanUbsan.M.loaded_segments (0x7cd18 : word) = Some W_7ccc8.
Proof. vm_refl. Qed.
Lemma D_7ccc8 : decode_any W_7ccc8 = Some (Jal 1 76944, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cccc : bv 32 := 0xf699e6e3.
Lemma F_7cccc : fetch_word AsanUbsan.M.loaded_segments (0x7cd1c : word) = Some W_7cccc.
Proof. vm_refl. Qed.
Lemma D_7cccc : decode_any W_7cccc = Some (Branch BC_LTU 19 9 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccd0 : bv 32 := 0xf72a64e3.
Lemma F_7ccd0 : fetch_word AsanUbsan.M.loaded_segments (0x7cd20 : word) = Some W_7ccd0.
Proof. vm_refl. Qed.
Lemma D_7ccd0 : decode_any W_7ccd0 = Some (Branch BC_LTU 20 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccd4 : bv 32 := 0xf73a62e3.
Lemma F_7ccd4 : fetch_word AsanUbsan.M.loaded_segments (0x7cd24 : word) = Some W_7ccd4.
Proof. vm_refl. Qed.
Lemma D_7ccd4 : decode_any W_7ccd4 = Some (Branch BC_LTU 20 19 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccd8 : bv 32 := 0xf69960e3.
Lemma F_7ccd8 : fetch_word AsanUbsan.M.loaded_segments (0x7cd28 : word) = Some W_7ccd8.
Proof. vm_refl. Qed.
Lemma D_7ccd8 : decode_any W_7ccd8 = Some (Branch BC_LTU 18 9 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccdc : bv 32 := 0x409a06b3.
Lemma F_7ccdc : fetch_word AsanUbsan.M.loaded_segments (0x7cd2c : word) = Some W_7ccdc.
Proof. vm_refl. Qed.
Lemma D_7ccdc : decode_any W_7ccdc = Some (Op ALU_SUB 13 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cce0 : bv 32 := 0x00100713.
Lemma F_7cce0 : fetch_word AsanUbsan.M.loaded_segments (0x7cd30 : word) = Some W_7cce0.
Proof. vm_refl. Qed.
Lemma D_7cce0 : decode_any W_7cce0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cce4 : bv 32 := 0x02871713.
Lemma F_7cce4 : fetch_word AsanUbsan.M.loaded_segments (0x7cd34 : word) = Some W_7cce4.
Proof. vm_refl. Qed.
Lemma D_7cce4 : decode_any W_7cce4 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cce8 : bv 32 := 0x00170513.
Lemma F_7cce8 : fetch_word AsanUbsan.M.loaded_segments (0x7cd38 : word) = Some W_7cce8.
Proof. vm_refl. Qed.
Lemma D_7cce8 : decode_any W_7cce8 = Some (OpImm ALU_ADD 10 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccec : bv 32 := 0x04a6fa63.
Lemma F_7ccec : fetch_word AsanUbsan.M.loaded_segments (0x7cd3c : word) = Some W_7ccec.
Proof. vm_refl. Qed.
Lemma D_7ccec : decode_any W_7ccec = Some (Branch BC_GEU 13 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccf0 : bv 32 := 0x15298863.
Lemma F_7ccf0 : fetch_word AsanUbsan.M.loaded_segments (0x7cd40 : word) = Some W_7ccf0.
Proof. vm_refl. Qed.
Lemma D_7ccf0 : decode_any W_7ccf0 = Some (Branch BC_EQ 19 18 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccf4 : bv 32 := 0x007a7513.
Lemma F_7ccf4 : fetch_word AsanUbsan.M.loaded_segments (0x7cd44 : word) = Some W_7ccf4.
Proof. vm_refl. Qed.
Lemma D_7ccf4 : decode_any W_7ccf4 = Some (OpImm ALU_AND 10 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccf8 : bv 32 := 0x06051063.
Lemma F_7ccf8 : fetch_word AsanUbsan.M.loaded_segments (0x7cd48 : word) = Some W_7ccf8.
Proof. vm_refl. Qed.
Lemma D_7ccf8 : decode_any W_7ccf8 = Some (Branch BC_NE 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ccfc : bv 32 := 0x00098a13.
Lemma F_7ccfc : fetch_word AsanUbsan.M.loaded_segments (0x7cd4c : word) = Some W_7ccfc.
Proof. vm_refl. Qed.
Lemma D_7ccfc : decode_any W_7ccfc = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd00 : bv 32 := 0x00090a93.
Lemma F_7cd00 : fetch_word AsanUbsan.M.loaded_segments (0x7cd50 : word) = Some W_7cd00.
Proof. vm_refl. Qed.
Lemma D_7cd00 : decode_any W_7cd00 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd04 : bv 32 := 0x00048513.
Lemma F_7cd04 : fetch_word AsanUbsan.M.loaded_segments (0x7cd54 : word) = Some W_7cd04.
Proof. vm_refl. Qed.
Lemma D_7cd04 : decode_any W_7cd04 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd08 : bv 32 := 0x0074f993.
Lemma F_7cd08 : fetch_word AsanUbsan.M.loaded_segments (0x7cd58 : word) = Some W_7cd08.
Proof. vm_refl. Qed.
Lemma D_7cd08 : decode_any W_7cd08 = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd0c : bv 32 := 0x08099e63.
Lemma F_7cd0c : fetch_word AsanUbsan.M.loaded_segments (0x7cd5c : word) = Some W_7cd0c.
Proof. vm_refl. Qed.
Lemma D_7cd0c : decode_any W_7cd0c = Some (Branch BC_NE 19 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd10 : bv 32 := 0x000a0593.
Lemma F_7cd10 : fetch_word AsanUbsan.M.loaded_segments (0x7cd60 : word) = Some W_7cd10.
Proof. vm_refl. Qed.
Lemma D_7cd10 : decode_any W_7cd10 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd14 : bv 32 := 0x000a0513.
Lemma F_7cd14 : fetch_word AsanUbsan.M.loaded_segments (0x7cd64 : word) = Some W_7cd14.
Proof. vm_refl. Qed.
Lemma D_7cd14 : decode_any W_7cd14 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd18 : bv 32 := 0x0d5a6863.
Lemma F_7cd18 : fetch_word AsanUbsan.M.loaded_segments (0x7cd68 : word) = Some W_7cd18.
Proof. vm_refl. Qed.
Lemma D_7cd18 : decode_any W_7cd18 = Some (Branch BC_LTU 20 21 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd1c : bv 32 := 0xff8af513.
Lemma F_7cd1c : fetch_word AsanUbsan.M.loaded_segments (0x7cd6c : word) = Some W_7cd1c.
Proof. vm_refl. Qed.
Lemma D_7cd1c : decode_any W_7cd1c = Some (OpImm ALU_AND 10 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd20 : bv 32 := 0x0cbaf863.
Lemma F_7cd20 : fetch_word AsanUbsan.M.loaded_segments (0x7cd70 : word) = Some W_7cd20.
Proof. vm_refl. Qed.
Lemma D_7cd20 : decode_any W_7cd20 = Some (Branch BC_GEU 21 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd24 : bv 32 := 0xff8af493.
Lemma F_7cd24 : fetch_word AsanUbsan.M.loaded_segments (0x7cd74 : word) = Some W_7cd24.
Proof. vm_refl. Qed.
Lemma D_7cd24 : decode_any W_7cd24 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd28 : bv 32 := 0x007a8613.
Lemma F_7cd28 : fetch_word AsanUbsan.M.loaded_segments (0x7cd78 : word) = Some W_7cd28.
Proof. vm_refl. Qed.
Lemma D_7cd28 : decode_any W_7cd28 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd2c : bv 32 := 0xff867913.
Lemma F_7cd2c : fetch_word AsanUbsan.M.loaded_segments (0x7cd7c : word) = Some W_7cd2c.
Proof. vm_refl. Qed.
Lemma D_7cd2c : decode_any W_7cd2c = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd30 : bv 32 := 0x0c957a63.
Lemma F_7cd30 : fetch_word AsanUbsan.M.loaded_segments (0x7cd80 : word) = Some W_7cd30.
Proof. vm_refl. Qed.
Lemma D_7cd30 : decode_any W_7cd30 = Some (Branch BC_GEU 10 9 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd34 : bv 32 := 0x40a485b3.
Lemma F_7cd34 : fetch_word AsanUbsan.M.loaded_segments (0x7cd84 : word) = Some W_7cd34.
Proof. vm_refl. Qed.
Lemma D_7cd34 : decode_any W_7cd34 = Some (Op ALU_SUB 11 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd38 : bv 32 := 0x00000613.
Lemma F_7cd38 : fetch_word AsanUbsan.M.loaded_segments (0x7cd88 : word) = Some W_7cd38.
Proof. vm_refl. Qed.
Lemma D_7cd38 : decode_any W_7cd38 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd3c : bv 32 := 0x0e00006f.
Lemma F_7cd3c : fetch_word AsanUbsan.M.loaded_segments (0x7cd8c : word) = Some W_7cd3c.
Proof. vm_refl. Qed.
Lemma D_7cd3c : decode_any W_7cd3c = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd40 : bv 32 := 0xfffa4517.
Lemma F_7cd40 : fetch_word AsanUbsan.M.loaded_segments (0x7cd90 : word) = Some W_7cd40.
Proof. vm_refl. Qed.
Lemma D_7cd40 : decode_any W_7cd40 = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd44 : bv 32 := 0xfffa5597.
Lemma F_7cd44 : fetch_word AsanUbsan.M.loaded_segments (0x7cd94 : word) = Some W_7cd44.
Proof. vm_refl. Qed.
Lemma D_7cd44 : decode_any W_7cd44 = Some (Auipc 11 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd48 : bv 32 := 0x66550513.
Lemma F_7cd48 : fetch_word AsanUbsan.M.loaded_segments (0x7cd98 : word) = Some W_7cd48.
Proof. vm_refl. Qed.
Lemma D_7cd48 : decode_any W_7cd48 = Some (OpImm ALU_ADD 10 10 1637, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd4c : bv 32 := 0x75858613.
Lemma F_7cd4c : fetch_word AsanUbsan.M.loaded_segments (0x7cd9c : word) = Some W_7cd4c.
Proof. vm_refl. Qed.
Lemma D_7cd4c : decode_any W_7cd4c = Some (OpImm ALU_ADD 12 11 1880, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd50 : bv 32 := 0x1b600593.
Lemma F_7cd50 : fetch_word AsanUbsan.M.loaded_segments (0x7cda0 : word) = Some W_7cd50.
Proof. vm_refl. Qed.
Lemma D_7cd50 : decode_any W_7cd50 = Some (OpImm ALU_ADD 11 0 438, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd54 : bv 32 := 0x58c170ef.
Lemma F_7cd54 : fetch_word AsanUbsan.M.loaded_segments (0x7cda4 : word) = Some W_7cd54.
Proof. vm_refl. Qed.
Lemma D_7cd54 : decode_any W_7cd54 = Some (Jal 1 95628, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd58 : bv 32 := 0xff8a7a93.
Lemma F_7cd58 : fetch_word AsanUbsan.M.loaded_segments (0x7cda8 : word) = Some W_7cd58.
Proof. vm_refl. Qed.
Lemma D_7cd58 : decode_any W_7cd58 = Some (OpImm ALU_AND 21 20 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd5c : bv 32 := 0x00098593.
Lemma F_7cd5c : fetch_word AsanUbsan.M.loaded_segments (0x7cdac : word) = Some W_7cd5c.
Proof. vm_refl. Qed.
Lemma D_7cd5c : decode_any W_7cd5c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd60 : bv 32 := 0x01396463.
Lemma F_7cd60 : fetch_word AsanUbsan.M.loaded_segments (0x7cdb0 : word) = Some W_7cd60.
Proof. vm_refl. Qed.
Lemma D_7cd60 : decode_any W_7cd60 = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd64 : bv 32 := 0x00090593.
Lemma F_7cd64 : fetch_word AsanUbsan.M.loaded_segments (0x7cdb4 : word) = Some W_7cd64.
Proof. vm_refl. Qed.
Lemma D_7cd64 : decode_any W_7cd64 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd68 : bv 32 := 0xf8bafae3.
Lemma F_7cd68 : fetch_word AsanUbsan.M.loaded_segments (0x7cdb8 : word) = Some W_7cd68.
Proof. vm_refl. Qed.
Lemma D_7cd68 : decode_any W_7cd68 = Some (Branch BC_GEU 21 11 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd6c : bv 32 := 0x000c1597.
Lemma F_7cd6c : fetch_word AsanUbsan.M.loaded_segments (0x7cdbc : word) = Some W_7cd6c.
Proof. vm_refl. Qed.
Lemma D_7cd6c : decode_any W_7cd6c = Some (Auipc 11 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd70 : bv 32 := 0xb0c5b583.
Lemma F_7cd70 : fetch_word AsanUbsan.M.loaded_segments (0x7cdc0 : word) = Some W_7cd70.
Proof. vm_refl. Qed.
Lemma D_7cd70 : decode_any W_7cd70 = Some (Load SZ8 true 11 11 2828, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd74 : bv 32 := 0x0005b583.
Lemma F_7cd74 : fetch_word AsanUbsan.M.loaded_segments (0x7cdc4 : word) = Some W_7cd74.
Proof. vm_refl. Qed.
Lemma D_7cd74 : decode_any W_7cd74 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd78 : bv 32 := 0x003a5613.
Lemma F_7cd78 : fetch_word AsanUbsan.M.loaded_segments (0x7cdc8 : word) = Some W_7cd78.
Proof. vm_refl. Qed.
Lemma D_7cd78 : decode_any W_7cd78 = Some (ShiftImm ALU_SRL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd7c : bv 32 := 0x00c585b3.
Lemma F_7cd7c : fetch_word AsanUbsan.M.loaded_segments (0x7cdcc : word) = Some W_7cd7c.
Proof. vm_refl. Qed.
Lemma D_7cd7c : decode_any W_7cd7c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd80 : bv 32 := 0x00058583.
Lemma F_7cd80 : fetch_word AsanUbsan.M.loaded_segments (0x7cdd0 : word) = Some W_7cd80.
Proof. vm_refl. Qed.
Lemma D_7cd80 : decode_any W_7cd80 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd84 : bv 32 := 0x00058463.
Lemma F_7cd84 : fetch_word AsanUbsan.M.loaded_segments (0x7cdd4 : word) = Some W_7cd84.
Proof. vm_refl. Qed.
Lemma D_7cd84 : decode_any W_7cd84 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd88 : bv 32 := 0xf6b55ae3.
Lemma F_7cd88 : fetch_word AsanUbsan.M.loaded_segments (0x7cdd8 : word) = Some W_7cd88.
Proof. vm_refl. Qed.
Lemma D_7cd88 : decode_any W_7cd88 = Some (Branch BC_GE 10 11 8052, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd8c : bv 32 := 0x000a8513.
Lemma F_7cd8c : fetch_word AsanUbsan.M.loaded_segments (0x7cddc : word) = Some W_7cd8c.
Proof. vm_refl. Qed.
Lemma D_7cd8c : decode_any W_7cd8c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd90 : bv 32 := 0x0e9aea63.
Lemma F_7cd90 : fetch_word AsanUbsan.M.loaded_segments (0x7cde0 : word) = Some W_7cd90.
Proof. vm_refl. Qed.
Lemma D_7cd90 : decode_any W_7cd90 = Some (Branch BC_LTU 21 9 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd94 : bv 32 := 0x00048513.
Lemma F_7cd94 : fetch_word AsanUbsan.M.loaded_segments (0x7cde4 : word) = Some W_7cd94.
Proof. vm_refl. Qed.
Lemma D_7cd94 : decode_any W_7cd94 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd98 : bv 32 := 0x000a8a13.
Lemma F_7cd98 : fetch_word AsanUbsan.M.loaded_segments (0x7cde8 : word) = Some W_7cd98.
Proof. vm_refl. Qed.
Lemma D_7cd98 : decode_any W_7cd98 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cd9c : bv 32 := 0x0f3af863.
Lemma F_7cd9c : fetch_word AsanUbsan.M.loaded_segments (0x7cdec : word) = Some W_7cd9c.
Proof. vm_refl. Qed.
Lemma D_7cd9c : decode_any W_7cd9c = Some (Branch BC_GEU 21 19 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cda0 : bv 32 := 0xf72ae4e3.
Lemma F_7cda0 : fetch_word AsanUbsan.M.loaded_segments (0x7cdf0 : word) = Some W_7cda0.
Proof. vm_refl. Qed.
Lemma D_7cda0 : decode_any W_7cda0 = Some (Branch BC_LTU 21 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cda4 : bv 32 := 0x0f00006f.
Lemma F_7cda4 : fetch_word AsanUbsan.M.loaded_segments (0x7cdf4 : word) = Some W_7cda4.
Proof. vm_refl. Qed.
Lemma D_7cda4 : decode_any W_7cda4 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cda8 : bv 32 := 0xf74504e3.
Lemma F_7cda8 : fetch_word AsanUbsan.M.loaded_segments (0x7cdf8 : word) = Some W_7cda8.
Proof. vm_refl. Qed.
Lemma D_7cda8 : decode_any W_7cda8 = Some (Branch BC_EQ 10 20 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdac : bv 32 := 0xf75512e3.
Lemma F_7cdac : fetch_word AsanUbsan.M.loaded_segments (0x7cdfc : word) = Some W_7cdac.
Proof. vm_refl. Qed.
Lemma D_7cdac : decode_any W_7cdac = Some (Branch BC_NE 10 21 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdb0 : bv 32 := 0x00748593.
Lemma F_7cdb0 : fetch_word AsanUbsan.M.loaded_segments (0x7ce00 : word) = Some W_7cdb0.
Proof. vm_refl. Qed.
Lemma D_7cdb0 : decode_any W_7cdb0 = Some (OpImm ALU_ADD 11 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdb4 : bv 32 := 0xff85f913.
Lemma F_7cdb4 : fetch_word AsanUbsan.M.loaded_segments (0x7ce04 : word) = Some W_7cdb4.
Proof. vm_refl. Qed.
Lemma D_7cdb4 : decode_any W_7cdb4 = Some (OpImm ALU_AND 18 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdb8 : bv 32 := 0xf5257ce3.
Lemma F_7cdb8 : fetch_word AsanUbsan.M.loaded_segments (0x7ce08 : word) = Some W_7cdb8.
Proof. vm_refl. Qed.
Lemma D_7cdb8 : decode_any W_7cdb8 = Some (Branch BC_GEU 10 18 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdbc : bv 32 := 0xff84f513.
Lemma F_7cdbc : fetch_word AsanUbsan.M.loaded_segments (0x7ce0c : word) = Some W_7cdbc.
Proof. vm_refl. Qed.
Lemma D_7cdbc : decode_any W_7cdbc = Some (OpImm ALU_AND 10 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdc0 : bv 32 := 0xbd0ff0ef.
Lemma F_7cdc0 : fetch_word AsanUbsan.M.loaded_segments (0x7ce10 : word) = Some W_7cdc0.
Proof. vm_refl. Qed.
Lemma D_7cdc0 : decode_any W_7cdc0 = Some (Jal 1 2094032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdc4 : bv 32 := 0x01350023.
Lemma F_7cdc4 : fetch_word AsanUbsan.M.loaded_segments (0x7ce14 : word) = Some W_7cdc4.
Proof. vm_refl. Qed.
Lemma D_7cdc4 : decode_any W_7cdc4 = Some (Store SZ1 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdc8 : bv 32 := 0x00090593.
Lemma F_7cdc8 : fetch_word AsanUbsan.M.loaded_segments (0x7ce18 : word) = Some W_7cdc8.
Proof. vm_refl. Qed.
Lemma D_7cdc8 : decode_any W_7cdc8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdcc : bv 32 := 0x012a6463.
Lemma F_7cdcc : fetch_word AsanUbsan.M.loaded_segments (0x7ce1c : word) = Some W_7cdcc.
Proof. vm_refl. Qed.
Lemma D_7cdcc : decode_any W_7cdcc = Some (Branch BC_LTU 20 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdd0 : bv 32 := 0x000a0593.
Lemma F_7cdd0 : fetch_word AsanUbsan.M.loaded_segments (0x7ce20 : word) = Some W_7cdd0.
Proof. vm_refl. Qed.
Lemma D_7cdd0 : decode_any W_7cdd0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdd4 : bv 32 := 0x012ae463.
Lemma F_7cdd4 : fetch_word AsanUbsan.M.loaded_segments (0x7ce24 : word) = Some W_7cdd4.
Proof. vm_refl. Qed.
Lemma D_7cdd4 : decode_any W_7cdd4 = Some (Branch BC_LTU 21 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdd8 : bv 32 := 0x000a8913.
Lemma F_7cdd8 : fetch_word AsanUbsan.M.loaded_segments (0x7ce28 : word) = Some W_7cdd8.
Proof. vm_refl. Qed.
Lemma D_7cdd8 : decode_any W_7cdd8 = Some (OpImm ALU_ADD 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cddc : bv 32 := 0x00090a93.
Lemma F_7cddc : fetch_word AsanUbsan.M.loaded_segments (0x7ce2c : word) = Some W_7cddc.
Proof. vm_refl. Qed.
Lemma D_7cddc : decode_any W_7cddc = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cde0 : bv 32 := 0x00058513.
Lemma F_7cde0 : fetch_word AsanUbsan.M.loaded_segments (0x7ce30 : word) = Some W_7cde0.
Proof. vm_refl. Qed.
Lemma D_7cde0 : decode_any W_7cde0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cde4 : bv 32 := 0xf325fce3.
Lemma F_7cde4 : fetch_word AsanUbsan.M.loaded_segments (0x7ce34 : word) = Some W_7cde4.
Proof. vm_refl. Qed.
Lemma D_7cde4 : decode_any W_7cde4 = Some (Branch BC_GEU 11 18 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cde8 : bv 32 := 0xff857513.
Lemma F_7cde8 : fetch_word AsanUbsan.M.loaded_segments (0x7ce38 : word) = Some W_7cde8.
Proof. vm_refl. Qed.
Lemma D_7cde8 : decode_any W_7cde8 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdec : bv 32 := 0xf2baece3.
Lemma F_7cdec : fetch_word AsanUbsan.M.loaded_segments (0x7ce3c : word) = Some W_7cdec.
Proof. vm_refl. Qed.
Lemma D_7cdec : decode_any W_7cdec = Some (Branch BC_LTU 21 11 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdf0 : bv 32 := 0x000a8593.
Lemma F_7cdf0 : fetch_word AsanUbsan.M.loaded_segments (0x7ce40 : word) = Some W_7cdf0.
Proof. vm_refl. Qed.
Lemma D_7cdf0 : decode_any W_7cdf0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdf4 : bv 32 := 0xff8af493.
Lemma F_7cdf4 : fetch_word AsanUbsan.M.loaded_segments (0x7ce44 : word) = Some W_7cdf4.
Proof. vm_refl. Qed.
Lemma D_7cdf4 : decode_any W_7cdf4 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdf8 : bv 32 := 0x007a8613.
Lemma F_7cdf8 : fetch_word AsanUbsan.M.loaded_segments (0x7ce48 : word) = Some W_7cdf8.
Proof. vm_refl. Qed.
Lemma D_7cdf8 : decode_any W_7cdf8 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7cdfc : bv 32 := 0xff867913.
Lemma F_7cdfc : fetch_word AsanUbsan.M.loaded_segments (0x7ce4c : word) = Some W_7cdfc.
Proof. vm_refl. Qed.
Lemma D_7cdfc : decode_any W_7cdfc = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce00 : bv 32 := 0xf2956ae3.
Lemma F_7ce00 : fetch_word AsanUbsan.M.loaded_segments (0x7ce50 : word) = Some W_7ce00.
Proof. vm_refl. Qed.
Lemma D_7ce00 : decode_any W_7ce00 = Some (Branch BC_LTU 10 9 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce04 : bv 32 := 0x00758513.
Lemma F_7ce04 : fetch_word AsanUbsan.M.loaded_segments (0x7ce54 : word) = Some W_7ce04.
Proof. vm_refl. Qed.
Lemma D_7ce04 : decode_any W_7ce04 = Some (OpImm ALU_ADD 10 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce08 : bv 32 := 0xff857513.
Lemma F_7ce08 : fetch_word AsanUbsan.M.loaded_segments (0x7ce58 : word) = Some W_7ce08.
Proof. vm_refl. Qed.
Lemma D_7ce08 : decode_any W_7ce08 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce0c : bv 32 := 0x00a97a63.
Lemma F_7ce0c : fetch_word AsanUbsan.M.loaded_segments (0x7ce5c : word) = Some W_7ce0c.
Proof. vm_refl. Qed.
Lemma D_7ce0c : decode_any W_7ce0c = Some (Branch BC_GEU 18 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce10 : bv 32 := 0x412505b3.
Lemma F_7ce10 : fetch_word AsanUbsan.M.loaded_segments (0x7ce60 : word) = Some W_7ce10.
Proof. vm_refl. Qed.
Lemma D_7ce10 : decode_any W_7ce10 = Some (Op ALU_SUB 11 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce14 : bv 32 := 0x0fc00613.
Lemma F_7ce14 : fetch_word AsanUbsan.M.loaded_segments (0x7ce64 : word) = Some W_7ce14.
Proof. vm_refl. Qed.
Lemma D_7ce14 : decode_any W_7ce14 = Some (OpImm ALU_ADD 12 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce18 : bv 32 := 0x00090513.
Lemma F_7ce18 : fetch_word AsanUbsan.M.loaded_segments (0x7ce68 : word) = Some W_7ce18.
Proof. vm_refl. Qed.
Lemma D_7ce18 : decode_any W_7ce18 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce1c : bv 32 := 0xe79fe0ef.
Lemma F_7ce1c : fetch_word AsanUbsan.M.loaded_segments (0x7ce6c : word) = Some W_7ce1c.
Proof. vm_refl. Qed.
Lemma D_7ce1c : decode_any W_7ce1c = Some (Jal 1 2092664, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce20 : bv 32 := 0x02990063.
Lemma F_7ce20 : fetch_word AsanUbsan.M.loaded_segments (0x7ce70 : word) = Some W_7ce20.
Proof. vm_refl. Qed.
Lemma D_7ce20 : decode_any W_7ce20 = Some (Branch BC_EQ 18 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce24 : bv 32 := 0x409906b3.
Lemma F_7ce24 : fetch_word AsanUbsan.M.loaded_segments (0x7ce74 : word) = Some W_7ce24.
Proof. vm_refl. Qed.
Lemma D_7ce24 : decode_any W_7ce24 = Some (Op ALU_SUB 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce28 : bv 32 := 0x00800513.
Lemma F_7ce28 : fetch_word AsanUbsan.M.loaded_segments (0x7ce78 : word) = Some W_7ce28.
Proof. vm_refl. Qed.
Lemma D_7ce28 : decode_any W_7ce28 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce2c : bv 32 := 0x02a69e63.
Lemma F_7ce2c : fetch_word AsanUbsan.M.loaded_segments (0x7ce7c : word) = Some W_7ce2c.
Proof. vm_refl. Qed.
Lemma D_7ce2c : decode_any W_7ce2c = Some (Branch BC_NE 13 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce30 : bv 32 := 0x007af913.
Lemma F_7ce30 : fetch_word AsanUbsan.M.loaded_segments (0x7ce80 : word) = Some W_7ce30.
Proof. vm_refl. Qed.
Lemma D_7ce30 : decode_any W_7ce30 = Some (OpImm ALU_AND 18 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce34 : bv 32 := 0x00048513.
Lemma F_7ce34 : fetch_word AsanUbsan.M.loaded_segments (0x7ce84 : word) = Some W_7ce34.
Proof. vm_refl. Qed.
Lemma D_7ce34 : decode_any W_7ce34 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce38 : bv 32 := 0xb58ff0ef.
Lemma F_7ce38 : fetch_word AsanUbsan.M.loaded_segments (0x7ce88 : word) = Some W_7ce38.
Proof. vm_refl. Qed.
Lemma D_7ce38 : decode_any W_7ce38 = Some (Jal 1 2093912, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce3c : bv 32 := 0x01250023.
Lemma F_7ce3c : fetch_word AsanUbsan.M.loaded_segments (0x7ce8c : word) = Some W_7ce3c.
Proof. vm_refl. Qed.
Lemma D_7ce3c : decode_any W_7ce3c = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce40 : bv 32 := 0x06010113.
Lemma F_7ce40 : fetch_word AsanUbsan.M.loaded_segments (0x7ce90 : word) = Some W_7ce40.
Proof. vm_refl. Qed.
Lemma D_7ce40 : decode_any W_7ce40 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce44 : bv 32 := 0x7e813083.
Lemma F_7ce44 : fetch_word AsanUbsan.M.loaded_segments (0x7ce94 : word) = Some W_7ce44.
Proof. vm_refl. Qed.
Lemma D_7ce44 : decode_any W_7ce44 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce48 : bv 32 := 0x7e013403.
Lemma F_7ce48 : fetch_word AsanUbsan.M.loaded_segments (0x7ce98 : word) = Some W_7ce48.
Proof. vm_refl. Qed.
Lemma D_7ce48 : decode_any W_7ce48 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce4c : bv 32 := 0x7d813483.
Lemma F_7ce4c : fetch_word AsanUbsan.M.loaded_segments (0x7ce9c : word) = Some W_7ce4c.
Proof. vm_refl. Qed.
Lemma D_7ce4c : decode_any W_7ce4c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce50 : bv 32 := 0x7d013903.
Lemma F_7ce50 : fetch_word AsanUbsan.M.loaded_segments (0x7cea0 : word) = Some W_7ce50.
Proof. vm_refl. Qed.
Lemma D_7ce50 : decode_any W_7ce50 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce54 : bv 32 := 0x7c813983.
Lemma F_7ce54 : fetch_word AsanUbsan.M.loaded_segments (0x7cea4 : word) = Some W_7ce54.
Proof. vm_refl. Qed.
Lemma D_7ce54 : decode_any W_7ce54 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce58 : bv 32 := 0x7c013a03.
Lemma F_7ce58 : fetch_word AsanUbsan.M.loaded_segments (0x7cea8 : word) = Some W_7ce58.
Proof. vm_refl. Qed.
Lemma D_7ce58 : decode_any W_7ce58 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce5c : bv 32 := 0x7b813a83.
Lemma F_7ce5c : fetch_word AsanUbsan.M.loaded_segments (0x7ceac : word) = Some W_7ce5c.
Proof. vm_refl. Qed.
Lemma D_7ce5c : decode_any W_7ce5c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce60 : bv 32 := 0x7f010113.
Lemma F_7ce60 : fetch_word AsanUbsan.M.loaded_segments (0x7ceb0 : word) = Some W_7ce60.
Proof. vm_refl. Qed.
Lemma D_7ce60 : decode_any W_7ce60 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce64 : bv 32 := 0x00008067.
Lemma F_7ce64 : fetch_word AsanUbsan.M.loaded_segments (0x7ceb4 : word) = Some W_7ce64.
Proof. vm_refl. Qed.
Lemma D_7ce64 : decode_any W_7ce64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce68 : bv 32 := 0xfffa4517.
Lemma F_7ce68 : fetch_word AsanUbsan.M.loaded_segments (0x7ceb8 : word) = Some W_7ce68.
Proof. vm_refl. Qed.
Lemma D_7ce68 : decode_any W_7ce68 = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce6c : bv 32 := 0xfff9c617.
Lemma F_7ce6c : fetch_word AsanUbsan.M.loaded_segments (0x7cebc : word) = Some W_7ce6c.
Proof. vm_refl. Qed.
Lemma D_7ce6c : decode_any W_7ce6c = Some (Auipc 12 1048476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce70 : bv 32 := 0x1dc00593.
Lemma F_7ce70 : fetch_word AsanUbsan.M.loaded_segments (0x7cec0 : word) = Some W_7ce70.
Proof. vm_refl. Qed.
Lemma D_7ce70 : decode_any W_7ce70 = Some (OpImm ALU_ADD 11 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce74 : bv 32 := 0x53d50513.
Lemma F_7ce74 : fetch_word AsanUbsan.M.loaded_segments (0x7cec4 : word) = Some W_7ce74.
Proof. vm_refl. Qed.
Lemma D_7ce74 : decode_any W_7ce74 = Some (OpImm ALU_ADD 10 10 1341, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce78 : bv 32 := 0xbe360613.
Lemma F_7ce78 : fetch_word AsanUbsan.M.loaded_segments (0x7cec8 : word) = Some W_7ce78.
Proof. vm_refl. Qed.
Lemma D_7ce78 : decode_any W_7ce78 = Some (OpImm ALU_ADD 12 12 3043, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce7c : bv 32 := 0x00800713.
Lemma F_7ce7c : fetch_word AsanUbsan.M.loaded_segments (0x7cecc : word) = Some W_7ce7c.
Proof. vm_refl. Qed.
Lemma D_7ce7c : decode_any W_7ce7c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce80 : bv 32 := 0x460170ef.
Lemma F_7ce80 : fetch_word AsanUbsan.M.loaded_segments (0x7ced0 : word) = Some W_7ce80.
Proof. vm_refl. Qed.
Lemma D_7ce80 : decode_any W_7ce80 = Some (Jal 1 95328, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce84 : bv 32 := 0x000a8a13.
Lemma F_7ce84 : fetch_word AsanUbsan.M.loaded_segments (0x7ced4 : word) = Some W_7ce84.
Proof. vm_refl. Qed.
Lemma D_7ce84 : decode_any W_7ce84 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce88 : bv 32 := 0xf13aece3.
Lemma F_7ce88 : fetch_word AsanUbsan.M.loaded_segments (0x7ced8 : word) = Some W_7ce88.
Proof. vm_refl. Qed.
Lemma D_7ce88 : decode_any W_7ce88 = Some (Branch BC_LTU 21 19 7960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce8c : bv 32 := 0x00098a13.
Lemma F_7ce8c : fetch_word AsanUbsan.M.loaded_segments (0x7cedc : word) = Some W_7ce8c.
Proof. vm_refl. Qed.
Lemma D_7ce8c : decode_any W_7ce8c = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce90 : bv 32 := 0xe72aece3.
Lemma F_7ce90 : fetch_word AsanUbsan.M.loaded_segments (0x7cee0 : word) = Some W_7ce90.
Proof. vm_refl. Qed.
Lemma D_7ce90 : decode_any W_7ce90 = Some (Branch BC_LTU 21 18 7800, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce94 : bv 32 := 0x00090a93.
Lemma F_7ce94 : fetch_word AsanUbsan.M.loaded_segments (0x7cee4 : word) = Some W_7ce94.
Proof. vm_refl. Qed.
Lemma D_7ce94 : decode_any W_7ce94 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ce98 : bv 32 := 0xe71ff06f.
Lemma F_7ce98 : fetch_word AsanUbsan.M.loaded_segments (0x7cee8 : word) = Some W_7ce98.
Proof. vm_refl. Qed.
Lemma D_7ce98 : decode_any W_7ce98 = Some (Jal 0 2096752, 4%Z).
Proof. vm_refl. Qed.
