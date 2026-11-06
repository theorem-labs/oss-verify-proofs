(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_348a8 : bv 32 := 0xfffdc197.
Lemma F_348a8 : fetch_word Ubsan.M.loaded_segments (0x34900 : word) = Some W_348a8.
Proof. vm_refl. Qed.
Lemma D_348a8 : decode_any W_348a8 = Some (Auipc 3 1048540, 4%Z).
Proof. vm_refl. Qed.

Definition W_348ac : bv 32 := 0xf0018193.
Lemma F_348ac : fetch_word Ubsan.M.loaded_segments (0x34904 : word) = Some W_348ac.
Proof. vm_refl. Qed.
Lemma D_348ac : decode_any W_348ac = Some (OpImm ALU_ADD 3 3 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_348b0 : bv 32 := 0x00010513.
Lemma F_348b0 : fetch_word Ubsan.M.loaded_segments (0x34908 : word) = Some W_348b0.
Proof. vm_refl. Qed.
Lemma D_348b0 : decode_any W_348b0 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_348b4 : bv 32 := 0xfffcb597.
Lemma F_348b4 : fetch_word Ubsan.M.loaded_segments (0x3490c : word) = Some W_348b4.
Proof. vm_refl. Qed.
Lemma D_348b4 : decode_any W_348b4 = Some (Auipc 11 1048523, 4%Z).
Proof. vm_refl. Qed.

Definition W_348b8 : bv 32 := 0x6f458593.
Lemma F_348b8 : fetch_word Ubsan.M.loaded_segments (0x34910 : word) = Some W_348b8.
Proof. vm_refl. Qed.
Lemma D_348b8 : decode_any W_348b8 = Some (OpImm ALU_ADD 11 11 1780, 4%Z).
Proof. vm_refl. Qed.

Definition W_348bc : bv 32 := 0xff017113.
Lemma F_348bc : fetch_word Ubsan.M.loaded_segments (0x34914 : word) = Some W_348bc.
Proof. vm_refl. Qed.
Lemma D_348bc : decode_any W_348bc = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_348c0 : bv 32 := 0x0040006f.
Lemma F_348c0 : fetch_word Ubsan.M.loaded_segments (0x34918 : word) = Some W_348c0.
Proof. vm_refl. Qed.
Lemma D_348c0 : decode_any W_348c0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_348c4 : bv 32 := 0x00052583.
Lemma F_348c4 : fetch_word Ubsan.M.loaded_segments (0x3491c : word) = Some W_348c4.
Proof. vm_refl. Qed.
Lemma D_348c4 : decode_any W_348c4 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_348c8 : bv 32 := 0x00085617.
Lemma F_348c8 : fetch_word Ubsan.M.loaded_segments (0x34920 : word) = Some W_348c8.
Proof. vm_refl. Qed.
Lemma D_348c8 : decode_any W_348c8 = Some (Auipc 12 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_348cc : bv 32 := 0x00085697.
Lemma F_348cc : fetch_word Ubsan.M.loaded_segments (0x34924 : word) = Some W_348cc.
Proof. vm_refl. Qed.
Lemma D_348cc : decode_any W_348cc = Some (Auipc 13 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_348d0 : bv 32 := 0x00085717.
Lemma F_348d0 : fetch_word Ubsan.M.loaded_segments (0x34928 : word) = Some W_348d0.
Proof. vm_refl. Qed.
Lemma D_348d0 : decode_any W_348d0 = Some (Auipc 14 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_348d4 : bv 32 := 0x37863783.
Lemma F_348d4 : fetch_word Ubsan.M.loaded_segments (0x3492c : word) = Some W_348d4.
Proof. vm_refl. Qed.
Lemma D_348d4 : decode_any W_348d4 = Some (Load SZ8 true 15 12 888, 4%Z).
Proof. vm_refl. Qed.

Definition W_348d8 : bv 32 := 0x37c6b683.
Lemma F_348d8 : fetch_word Ubsan.M.loaded_segments (0x34930 : word) = Some W_348d8.
Proof. vm_refl. Qed.
Lemma D_348d8 : decode_any W_348d8 = Some (Load SZ8 true 13 13 892, 4%Z).
Proof. vm_refl. Qed.

Definition W_348dc : bv 32 := 0x38073703.
Lemma F_348dc : fetch_word Ubsan.M.loaded_segments (0x34934 : word) = Some W_348dc.
Proof. vm_refl. Qed.
Lemma D_348dc : decode_any W_348dc = Some (Load SZ8 true 14 14 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_348e0 : bv 32 := 0x00850613.
Lemma F_348e0 : fetch_word Ubsan.M.loaded_segments (0x34938 : word) = Some W_348e0.
Proof. vm_refl. Qed.
Lemma D_348e0 : decode_any W_348e0 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_348e4 : bv 32 := 0x00078513.
Lemma F_348e4 : fetch_word Ubsan.M.loaded_segments (0x3493c : word) = Some W_348e4.
Proof. vm_refl. Qed.
Lemma D_348e4 : decode_any W_348e4 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_348e8 : bv 32 := 0x00000793.
Lemma F_348e8 : fetch_word Ubsan.M.loaded_segments (0x34940 : word) = Some W_348e8.
Proof. vm_refl. Qed.
Lemma D_348e8 : decode_any W_348e8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_348ec : bv 32 := 0x1416806f.
Lemma F_348ec : fetch_word Ubsan.M.loaded_segments (0x34944 : word) = Some W_348ec.
Proof. vm_refl. Qed.
Lemma D_348ec : decode_any W_348ec = Some (Jal 0 428352, 4%Z).
Proof. vm_refl. Qed.

Definition W_348f0 : bv 32 := 0xff010113.
Lemma F_348f0 : fetch_word Ubsan.M.loaded_segments (0x34948 : word) = Some W_348f0.
Proof. vm_refl. Qed.
Lemma D_348f0 : decode_any W_348f0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_348f4 : bv 32 := 0x00113423.
Lemma F_348f4 : fetch_word Ubsan.M.loaded_segments (0x3494c : word) = Some W_348f4.
Proof. vm_refl. Qed.
Lemma D_348f4 : decode_any W_348f4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_348f8 : bv 32 := 0x00813023.
Lemma F_348f8 : fetch_word Ubsan.M.loaded_segments (0x34950 : word) = Some W_348f8.
Proof. vm_refl. Qed.
Lemma D_348f8 : decode_any W_348f8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_348fc : bv 32 := 0x01010413.
Lemma F_348fc : fetch_word Ubsan.M.loaded_segments (0x34954 : word) = Some W_348fc.
Proof. vm_refl. Qed.
Lemma D_348fc : decode_any W_348fc = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_34900 : bv 32 := 0x00086517.
Lemma F_34900 : fetch_word Ubsan.M.loaded_segments (0x34958 : word) = Some W_34900.
Proof. vm_refl. Qed.
Lemma D_34900 : decode_any W_34900 = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_34904 : bv 32 := 0x7e850513.
Lemma F_34904 : fetch_word Ubsan.M.loaded_segments (0x3495c : word) = Some W_34904.
Proof. vm_refl. Qed.
Lemma D_34904 : decode_any W_34904 = Some (OpImm ALU_ADD 10 10 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_34908 : bv 32 := 0x00054503.
Lemma F_34908 : fetch_word Ubsan.M.loaded_segments (0x34960 : word) = Some W_34908.
Proof. vm_refl. Qed.
Lemma D_34908 : decode_any W_34908 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3490c : bv 32 := 0x00157513.
Lemma F_3490c : fetch_word Ubsan.M.loaded_segments (0x34964 : word) = Some W_3490c.
Proof. vm_refl. Qed.
Lemma D_3490c : decode_any W_3490c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_34910 : bv 32 := 0x00050663.
Lemma F_34910 : fetch_word Ubsan.M.loaded_segments (0x34968 : word) = Some W_34910.
Proof. vm_refl. Qed.
Lemma D_34910 : decode_any W_34910 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3491c : bv 32 := 0x00086517.
Lemma F_3491c : fetch_word Ubsan.M.loaded_segments (0x34974 : word) = Some W_3491c.
Proof. vm_refl. Qed.
Lemma D_3491c : decode_any W_3491c = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_34920 : bv 32 := 0x7cc50593.
Lemma F_34920 : fetch_word Ubsan.M.loaded_segments (0x34978 : word) = Some W_34920.
Proof. vm_refl. Qed.
Lemma D_34920 : decode_any W_34920 = Some (OpImm ALU_ADD 11 10 1996, 4%Z).
Proof. vm_refl. Qed.

Definition W_34924 : bv 32 := 0x00100513.
Lemma F_34924 : fetch_word Ubsan.M.loaded_segments (0x3497c : word) = Some W_34924.
Proof. vm_refl. Qed.
Lemma D_34924 : decode_any W_34924 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_34928 : bv 32 := 0x00a58023.
Lemma F_34928 : fetch_word Ubsan.M.loaded_segments (0x34980 : word) = Some W_34928.
Proof. vm_refl. Qed.
Lemma D_34928 : decode_any W_34928 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3492c : bv 32 := 0x00085517.
Lemma F_3492c : fetch_word Ubsan.M.loaded_segments (0x34984 : word) = Some W_3492c.
Proof. vm_refl. Qed.
Lemma D_3492c : decode_any W_3492c = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_34930 : bv 32 := 0x32c53503.
Lemma F_34930 : fetch_word Ubsan.M.loaded_segments (0x34988 : word) = Some W_34930.
Proof. vm_refl. Qed.
Lemma D_34930 : decode_any W_34930 = Some (Load SZ8 true 10 10 812, 4%Z).
Proof. vm_refl. Qed.

Definition W_34934 : bv 32 := 0x02050063.
Lemma F_34934 : fetch_word Ubsan.M.loaded_segments (0x3498c : word) = Some W_34934.
Proof. vm_refl. Qed.
Lemma D_34934 : decode_any W_34934 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_34954 : bv 32 := 0x00813083.
Lemma F_34954 : fetch_word Ubsan.M.loaded_segments (0x349ac : word) = Some W_34954.
Proof. vm_refl. Qed.
Lemma D_34954 : decode_any W_34954 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_34958 : bv 32 := 0x00013403.
Lemma F_34958 : fetch_word Ubsan.M.loaded_segments (0x349b0 : word) = Some W_34958.
Proof. vm_refl. Qed.
Lemma D_34958 : decode_any W_34958 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3495c : bv 32 := 0x01010113.
Lemma F_3495c : fetch_word Ubsan.M.loaded_segments (0x349b4 : word) = Some W_3495c.
Proof. vm_refl. Qed.
Lemma D_3495c : decode_any W_3495c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_34960 : bv 32 := 0x00008067.
Lemma F_34960 : fetch_word Ubsan.M.loaded_segments (0x349b8 : word) = Some W_34960.
Proof. vm_refl. Qed.
Lemma D_34960 : decode_any W_34960 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34964 : bv 32 := 0xff010113.
Lemma F_34964 : fetch_word Ubsan.M.loaded_segments (0x349bc : word) = Some W_34964.
Proof. vm_refl. Qed.
Lemma D_34964 : decode_any W_34964 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_34968 : bv 32 := 0x00113423.
Lemma F_34968 : fetch_word Ubsan.M.loaded_segments (0x349c0 : word) = Some W_34968.
Proof. vm_refl. Qed.
Lemma D_34968 : decode_any W_34968 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3496c : bv 32 := 0x00813023.
Lemma F_3496c : fetch_word Ubsan.M.loaded_segments (0x349c4 : word) = Some W_3496c.
Proof. vm_refl. Qed.
Lemma D_3496c : decode_any W_3496c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34970 : bv 32 := 0x01010413.
Lemma F_34970 : fetch_word Ubsan.M.loaded_segments (0x349c8 : word) = Some W_34970.
Proof. vm_refl. Qed.
Lemma D_34970 : decode_any W_34970 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_34974 : bv 32 := 0x00086517.
Lemma F_34974 : fetch_word Ubsan.M.loaded_segments (0x349cc : word) = Some W_34974.
Proof. vm_refl. Qed.
Lemma D_34974 : decode_any W_34974 = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_34978 : bv 32 := 0x7bc50513.
Lemma F_34978 : fetch_word Ubsan.M.loaded_segments (0x349d0 : word) = Some W_34978.
Proof. vm_refl. Qed.
Lemma D_34978 : decode_any W_34978 = Some (OpImm ALU_ADD 10 10 1980, 4%Z).
Proof. vm_refl. Qed.

Definition W_3497c : bv 32 := 0x00054503.
Lemma F_3497c : fetch_word Ubsan.M.loaded_segments (0x349d4 : word) = Some W_3497c.
Proof. vm_refl. Qed.
Lemma D_3497c : decode_any W_3497c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34980 : bv 32 := 0x00157513.
Lemma F_34980 : fetch_word Ubsan.M.loaded_segments (0x349d8 : word) = Some W_34980.
Proof. vm_refl. Qed.
Lemma D_34980 : decode_any W_34980 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_34984 : bv 32 := 0x00050663.
Lemma F_34984 : fetch_word Ubsan.M.loaded_segments (0x349dc : word) = Some W_34984.
Proof. vm_refl. Qed.
Lemma D_34984 : decode_any W_34984 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_34990 : bv 32 := 0x00086517.
Lemma F_34990 : fetch_word Ubsan.M.loaded_segments (0x349e8 : word) = Some W_34990.
Proof. vm_refl. Qed.
Lemma D_34990 : decode_any W_34990 = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_34994 : bv 32 := 0x7a050593.
Lemma F_34994 : fetch_word Ubsan.M.loaded_segments (0x349ec : word) = Some W_34994.
Proof. vm_refl. Qed.
Lemma D_34994 : decode_any W_34994 = Some (OpImm ALU_ADD 11 10 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_34998 : bv 32 := 0x00100513.
Lemma F_34998 : fetch_word Ubsan.M.loaded_segments (0x349f0 : word) = Some W_34998.
Proof. vm_refl. Qed.
Lemma D_34998 : decode_any W_34998 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3499c : bv 32 := 0x00a58023.
Lemma F_3499c : fetch_word Ubsan.M.loaded_segments (0x349f4 : word) = Some W_3499c.
Proof. vm_refl. Qed.
Lemma D_3499c : decode_any W_3499c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_349a0 : bv 32 := 0x00085517.
Lemma F_349a0 : fetch_word Ubsan.M.loaded_segments (0x349f8 : word) = Some W_349a0.
Proof. vm_refl. Qed.
Lemma D_349a0 : decode_any W_349a0 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_349a4 : bv 32 := 0x2c053503.
Lemma F_349a4 : fetch_word Ubsan.M.loaded_segments (0x349fc : word) = Some W_349a4.
Proof. vm_refl. Qed.
Lemma D_349a4 : decode_any W_349a4 = Some (Load SZ8 true 10 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_349a8 : bv 32 := 0x00050e63.
Lemma F_349a8 : fetch_word Ubsan.M.loaded_segments (0x34a00 : word) = Some W_349a8.
Proof. vm_refl. Qed.
Lemma D_349a8 : decode_any W_349a8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_349c4 : bv 32 := 0x00085517.
Lemma F_349c4 : fetch_word Ubsan.M.loaded_segments (0x34a1c : word) = Some W_349c4.
Proof. vm_refl. Qed.
Lemma D_349c4 : decode_any W_349c4 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_349c8 : bv 32 := 0x2a453503.
Lemma F_349c8 : fetch_word Ubsan.M.loaded_segments (0x34a20 : word) = Some W_349c8.
Proof. vm_refl. Qed.
Lemma D_349c8 : decode_any W_349c8 = Some (Load SZ8 true 10 10 676, 4%Z).
Proof. vm_refl. Qed.

Definition W_349cc : bv 32 := 0x00050c63.
Lemma F_349cc : fetch_word Ubsan.M.loaded_segments (0x34a24 : word) = Some W_349cc.
Proof. vm_refl. Qed.
Lemma D_349cc : decode_any W_349cc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_349e4 : bv 32 := 0x00813083.
Lemma F_349e4 : fetch_word Ubsan.M.loaded_segments (0x34a3c : word) = Some W_349e4.
Proof. vm_refl. Qed.
Lemma D_349e4 : decode_any W_349e4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_349e8 : bv 32 := 0x00013403.
Lemma F_349e8 : fetch_word Ubsan.M.loaded_segments (0x34a40 : word) = Some W_349e8.
Proof. vm_refl. Qed.
Lemma D_349e8 : decode_any W_349e8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_349ec : bv 32 := 0x01010113.
Lemma F_349ec : fetch_word Ubsan.M.loaded_segments (0x34a44 : word) = Some W_349ec.
Proof. vm_refl. Qed.
Lemma D_349ec : decode_any W_349ec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_349f0 : bv 32 := 0x00008067.
Lemma F_349f0 : fetch_word Ubsan.M.loaded_segments (0x34a48 : word) = Some W_349f0.
Proof. vm_refl. Qed.
Lemma D_349f0 : decode_any W_349f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34a48 : bv 32 := 0x24050a63.
Lemma F_34a48 : fetch_word Ubsan.M.loaded_segments (0x34aa0 : word) = Some W_34a48.
Proof. vm_refl. Qed.
Lemma D_34a48 : decode_any W_34a48 = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_34a88 : bv 32 := 0x01a9d513.
Lemma F_34a88 : fetch_word Ubsan.M.loaded_segments (0x34ae0 : word) = Some W_34a88.
Proof. vm_refl. Qed.
Lemma D_34a88 : decode_any W_34a88 = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_34a8c : bv 32 := 0x1a051863.
Lemma F_34a8c : fetch_word Ubsan.M.loaded_segments (0x34ae4 : word) = Some W_34a8c.
Proof. vm_refl. Qed.
Lemma D_34a8c : decode_any W_34a8c = Some (Branch BC_NE 10 0 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_34a90 : bv 32 := 0x00199a93.
Lemma F_34a90 : fetch_word Ubsan.M.loaded_segments (0x34ae8 : word) = Some W_34a90.
Proof. vm_refl. Qed.
Lemma D_34a90 : decode_any W_34a90 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_34a94 : bv 32 := 0x000a8513.
Lemma F_34a94 : fetch_word Ubsan.M.loaded_segments (0x34aec : word) = Some W_34a94.
Proof. vm_refl. Qed.
Lemma D_34a94 : decode_any W_34a94 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34a98 : bv 32 := 0x6696a0ef.
Lemma F_34a98 : fetch_word Ubsan.M.loaded_segments (0x34af0 : word) = Some W_34a98.
Proof. vm_refl. Qed.
Lemma D_34a98 : decode_any W_34a98 = Some (Jal 1 437864, 4%Z).
Proof. vm_refl. Qed.

Definition W_34a9c : bv 32 := 0x1c050063.
Lemma F_34a9c : fetch_word Ubsan.M.loaded_segments (0x34af4 : word) = Some W_34a9c.
Proof. vm_refl. Qed.
Lemma D_34a9c : decode_any W_34a9c = Some (Branch BC_EQ 10 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_34aa0 : bv 32 := 0x00050493.
Lemma F_34aa0 : fetch_word Ubsan.M.loaded_segments (0x34af8 : word) = Some W_34aa0.
Proof. vm_refl. Qed.
Lemma D_34aa0 : decode_any W_34aa0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34aa4 : bv 32 := 0x00098a63.
Lemma F_34aa4 : fetch_word Ubsan.M.loaded_segments (0x34afc : word) = Some W_34aa4.
Proof. vm_refl. Qed.
Lemma D_34aa4 : decode_any W_34aa4 = Some (Branch BC_EQ 19 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_34aa8 : bv 32 := 0x00048513.
Lemma F_34aa8 : fetch_word Ubsan.M.loaded_segments (0x34b00 : word) = Some W_34aa8.
Proof. vm_refl. Qed.
Lemma D_34aa8 : decode_any W_34aa8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34aac : bv 32 := 0x000b8593.
Lemma F_34aac : fetch_word Ubsan.M.loaded_segments (0x34b04 : word) = Some W_34aac.
Proof. vm_refl. Qed.
Lemma D_34aac : decode_any W_34aac = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34ab0 : bv 32 := 0x00098613.
Lemma F_34ab0 : fetch_word Ubsan.M.loaded_segments (0x34b08 : word) = Some W_34ab0.
Proof. vm_refl. Qed.
Lemma D_34ab0 : decode_any W_34ab0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34ab4 : bv 32 := 0x4fc790ef.
Lemma F_34ab4 : fetch_word Ubsan.M.loaded_segments (0x34b0c : word) = Some W_34ab4.
Proof. vm_refl. Qed.
Lemma D_34ab4 : decode_any W_34ab4 = Some (Jal 1 496892, 4%Z).
Proof. vm_refl. Qed.

Definition W_34ae8 : bv 32 := 0x000a0513.
Lemma F_34ae8 : fetch_word Ubsan.M.loaded_segments (0x34b40 : word) = Some W_34ae8.
Proof. vm_refl. Qed.
Lemma D_34ae8 : decode_any W_34ae8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34aec : bv 32 := 0x3687e0ef.
Lemma F_34aec : fetch_word Ubsan.M.loaded_segments (0x34b44 : word) = Some W_34aec.
Proof. vm_refl. Qed.
Lemma D_34aec : decode_any W_34aec = Some (Jal 1 516968, 4%Z).
Proof. vm_refl. Qed.

Definition W_34b68 : bv 32 := 0x000ac663.
Lemma F_34b68 : fetch_word Ubsan.M.loaded_segments (0x34bc0 : word) = Some W_34b68.
Proof. vm_refl. Qed.
Lemma D_34b68 : decode_any W_34b68 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_34b6c : bv 32 := 0x00050413.
Lemma F_34b6c : fetch_word Ubsan.M.loaded_segments (0x34bc4 : word) = Some W_34b6c.
Proof. vm_refl. Qed.
Lemma D_34b6c : decode_any W_34b6c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34b70 : bv 32 := 0x0780006f.
Lemma F_34b70 : fetch_word Ubsan.M.loaded_segments (0x34bc8 : word) = Some W_34b70.
Proof. vm_refl. Qed.
Lemma D_34b70 : decode_any W_34b70 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_34b74 : bv 32 := 0x148000ef.
Lemma F_34b74 : fetch_word Ubsan.M.loaded_segments (0x34bcc : word) = Some W_34b74.
Proof. vm_refl. Qed.
Lemma D_34b74 : decode_any W_34b74 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_34b78 : bv 32 := 0x0fb00593.
Lemma F_34b78 : fetch_word Ubsan.M.loaded_segments (0x34bd0 : word) = Some W_34b78.
Proof. vm_refl. Qed.
Lemma D_34b78 : decode_any W_34b78 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_34b7c : bv 32 := 0x00050413.
Lemma F_34b7c : fetch_word Ubsan.M.loaded_segments (0x34bd4 : word) = Some W_34b7c.
Proof. vm_refl. Qed.
Lemma D_34b7c : decode_any W_34b7c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34b80 : bv 32 := 0x06b56463.
Lemma F_34b80 : fetch_word Ubsan.M.loaded_segments (0x34bd8 : word) = Some W_34b80.
Proof. vm_refl. Qed.
Lemma D_34b80 : decode_any W_34b80 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_34cbc : bv 32 := 0x00000513.
Lemma F_34cbc : fetch_word Ubsan.M.loaded_segments (0x34d14 : word) = Some W_34cbc.
Proof. vm_refl. Qed.
Lemma D_34cbc : decode_any W_34cbc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34cc0 : bv 32 := 0x00008067.
Lemma F_34cc0 : fetch_word Ubsan.M.loaded_segments (0x34d18 : word) = Some W_34cc0.
Proof. vm_refl. Qed.
Lemma D_34cc0 : decode_any W_34cc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
