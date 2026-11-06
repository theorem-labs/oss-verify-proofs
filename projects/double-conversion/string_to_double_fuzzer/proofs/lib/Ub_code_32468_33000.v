(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation USEGS := ImgU.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_324e8 : bv 32 := 0xfffde197.
Lemma F_324e8 : fetch_word USEGS (0x324e8 : word) = Some W_324e8.
Proof. vm_refl. Qed.
Lemma D_324e8 : decode_any W_324e8 = Some (Auipc 3 1048542, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_324ec : bv 32 := 0x31818193.
Lemma F_324ec : fetch_word USEGS (0x324ec : word) = Some W_324ec.
Proof. vm_refl. Qed.
Lemma D_324ec : decode_any W_324ec = Some (OpImm ALU_ADD 3 3 792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_324f0 : bv 32 := 0x00010513.
Lemma F_324f0 : fetch_word USEGS (0x324f0 : word) = Some W_324f0.
Proof. vm_refl. Qed.
Lemma D_324f0 : decode_any W_324f0 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_324f4 : bv 32 := 0xfffce597.
Lemma F_324f4 : fetch_word USEGS (0x324f4 : word) = Some W_324f4.
Proof. vm_refl. Qed.
Lemma D_324f4 : decode_any W_324f4 = Some (Auipc 11 1048526, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_324f8 : bv 32 := 0xb0c58593.
Lemma F_324f8 : fetch_word USEGS (0x324f8 : word) = Some W_324f8.
Proof. vm_refl. Qed.
Lemma D_324f8 : decode_any W_324f8 = Some (OpImm ALU_ADD 11 11 2828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_324fc : bv 32 := 0xff017113.
Lemma F_324fc : fetch_word USEGS (0x324fc : word) = Some W_324fc.
Proof. vm_refl. Qed.
Lemma D_324fc : decode_any W_324fc = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32500 : bv 32 := 0x0040006f.
Lemma F_32500 : fetch_word USEGS (0x32500 : word) = Some W_32500.
Proof. vm_refl. Qed.
Lemma D_32500 : decode_any W_32500 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32504 : bv 32 := 0x00052583.
Lemma F_32504 : fetch_word USEGS (0x32504 : word) = Some W_32504.
Proof. vm_refl. Qed.
Lemma D_32504 : decode_any W_32504 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32508 : bv 32 := 0x00080617.
Lemma F_32508 : fetch_word USEGS (0x32508 : word) = Some W_32508.
Proof. vm_refl. Qed.
Lemma D_32508 : decode_any W_32508 = Some (Auipc 12 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3250c : bv 32 := 0x00080697.
Lemma F_3250c : fetch_word USEGS (0x3250c : word) = Some W_3250c.
Proof. vm_refl. Qed.
Lemma D_3250c : decode_any W_3250c = Some (Auipc 13 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32510 : bv 32 := 0x00080717.
Lemma F_32510 : fetch_word USEGS (0x32510 : word) = Some W_32510.
Proof. vm_refl. Qed.
Lemma D_32510 : decode_any W_32510 = Some (Auipc 14 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32514 : bv 32 := 0xc4063783.
Lemma F_32514 : fetch_word USEGS (0x32514 : word) = Some W_32514.
Proof. vm_refl. Qed.
Lemma D_32514 : decode_any W_32514 = Some (Load SZ8 true 15 12 3136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32518 : bv 32 := 0xc446b683.
Lemma F_32518 : fetch_word USEGS (0x32518 : word) = Some W_32518.
Proof. vm_refl. Qed.
Lemma D_32518 : decode_any W_32518 = Some (Load SZ8 true 13 13 3140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3251c : bv 32 := 0xc4873703.
Lemma F_3251c : fetch_word USEGS (0x3251c : word) = Some W_3251c.
Proof. vm_refl. Qed.
Lemma D_3251c : decode_any W_3251c = Some (Load SZ8 true 14 14 3144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32520 : bv 32 := 0x00850613.
Lemma F_32520 : fetch_word USEGS (0x32520 : word) = Some W_32520.
Proof. vm_refl. Qed.
Lemma D_32520 : decode_any W_32520 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32524 : bv 32 := 0x00078513.
Lemma F_32524 : fetch_word USEGS (0x32524 : word) = Some W_32524.
Proof. vm_refl. Qed.
Lemma D_32524 : decode_any W_32524 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32528 : bv 32 := 0x00000793.
Lemma F_32528 : fetch_word USEGS (0x32528 : word) = Some W_32528.
Proof. vm_refl. Qed.
Lemma D_32528 : decode_any W_32528 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3252c : bv 32 := 0x3716306f.
Lemma F_3252c : fetch_word USEGS (0x3252c : word) = Some W_3252c.
Proof. vm_refl. Qed.
Lemma D_3252c : decode_any W_3252c = Some (Jal 0 408432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32530 : bv 32 := 0xff010113.
Lemma F_32530 : fetch_word USEGS (0x32530 : word) = Some W_32530.
Proof. vm_refl. Qed.
Lemma D_32530 : decode_any W_32530 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32534 : bv 32 := 0x00113423.
Lemma F_32534 : fetch_word USEGS (0x32534 : word) = Some W_32534.
Proof. vm_refl. Qed.
Lemma D_32534 : decode_any W_32534 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32538 : bv 32 := 0x00813023.
Lemma F_32538 : fetch_word USEGS (0x32538 : word) = Some W_32538.
Proof. vm_refl. Qed.
Lemma D_32538 : decode_any W_32538 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3253c : bv 32 := 0x01010413.
Lemma F_3253c : fetch_word USEGS (0x3253c : word) = Some W_3253c.
Proof. vm_refl. Qed.
Lemma D_3253c : decode_any W_3253c = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32540 : bv 32 := 0x00081517.
Lemma F_32540 : fetch_word USEGS (0x32540 : word) = Some W_32540.
Proof. vm_refl. Qed.
Lemma D_32540 : decode_any W_32540 = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32544 : bv 32 := 0x06050513.
Lemma F_32544 : fetch_word USEGS (0x32544 : word) = Some W_32544.
Proof. vm_refl. Qed.
Lemma D_32544 : decode_any W_32544 = Some (OpImm ALU_ADD 10 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32548 : bv 32 := 0x00054503.
Lemma F_32548 : fetch_word USEGS (0x32548 : word) = Some W_32548.
Proof. vm_refl. Qed.
Lemma D_32548 : decode_any W_32548 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3254c : bv 32 := 0x00157513.
Lemma F_3254c : fetch_word USEGS (0x3254c : word) = Some W_3254c.
Proof. vm_refl. Qed.
Lemma D_3254c : decode_any W_3254c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32550 : bv 32 := 0x00050663.
Lemma F_32550 : fetch_word USEGS (0x32550 : word) = Some W_32550.
Proof. vm_refl. Qed.
Lemma D_32550 : decode_any W_32550 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3255c : bv 32 := 0x00081517.
Lemma F_3255c : fetch_word USEGS (0x3255c : word) = Some W_3255c.
Proof. vm_refl. Qed.
Lemma D_3255c : decode_any W_3255c = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32560 : bv 32 := 0x04450593.
Lemma F_32560 : fetch_word USEGS (0x32560 : word) = Some W_32560.
Proof. vm_refl. Qed.
Lemma D_32560 : decode_any W_32560 = Some (OpImm ALU_ADD 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32564 : bv 32 := 0x00100513.
Lemma F_32564 : fetch_word USEGS (0x32564 : word) = Some W_32564.
Proof. vm_refl. Qed.
Lemma D_32564 : decode_any W_32564 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32568 : bv 32 := 0x00a58023.
Lemma F_32568 : fetch_word USEGS (0x32568 : word) = Some W_32568.
Proof. vm_refl. Qed.
Lemma D_32568 : decode_any W_32568 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3256c : bv 32 := 0x00080517.
Lemma F_3256c : fetch_word USEGS (0x3256c : word) = Some W_3256c.
Proof. vm_refl. Qed.
Lemma D_3256c : decode_any W_3256c = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32570 : bv 32 := 0xbf453503.
Lemma F_32570 : fetch_word USEGS (0x32570 : word) = Some W_32570.
Proof. vm_refl. Qed.
Lemma D_32570 : decode_any W_32570 = Some (Load SZ8 true 10 10 3060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32574 : bv 32 := 0x02050063.
Lemma F_32574 : fetch_word USEGS (0x32574 : word) = Some W_32574.
Proof. vm_refl. Qed.
Lemma D_32574 : decode_any W_32574 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32594 : bv 32 := 0x00813083.
Lemma F_32594 : fetch_word USEGS (0x32594 : word) = Some W_32594.
Proof. vm_refl. Qed.
Lemma D_32594 : decode_any W_32594 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32598 : bv 32 := 0x00013403.
Lemma F_32598 : fetch_word USEGS (0x32598 : word) = Some W_32598.
Proof. vm_refl. Qed.
Lemma D_32598 : decode_any W_32598 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3259c : bv 32 := 0x01010113.
Lemma F_3259c : fetch_word USEGS (0x3259c : word) = Some W_3259c.
Proof. vm_refl. Qed.
Lemma D_3259c : decode_any W_3259c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325a0 : bv 32 := 0x00008067.
Lemma F_325a0 : fetch_word USEGS (0x325a0 : word) = Some W_325a0.
Proof. vm_refl. Qed.
Lemma D_325a0 : decode_any W_325a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325a4 : bv 32 := 0xff010113.
Lemma F_325a4 : fetch_word USEGS (0x325a4 : word) = Some W_325a4.
Proof. vm_refl. Qed.
Lemma D_325a4 : decode_any W_325a4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325a8 : bv 32 := 0x00113423.
Lemma F_325a8 : fetch_word USEGS (0x325a8 : word) = Some W_325a8.
Proof. vm_refl. Qed.
Lemma D_325a8 : decode_any W_325a8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325ac : bv 32 := 0x00813023.
Lemma F_325ac : fetch_word USEGS (0x325ac : word) = Some W_325ac.
Proof. vm_refl. Qed.
Lemma D_325ac : decode_any W_325ac = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325b0 : bv 32 := 0x01010413.
Lemma F_325b0 : fetch_word USEGS (0x325b0 : word) = Some W_325b0.
Proof. vm_refl. Qed.
Lemma D_325b0 : decode_any W_325b0 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325b4 : bv 32 := 0x00081517.
Lemma F_325b4 : fetch_word USEGS (0x325b4 : word) = Some W_325b4.
Proof. vm_refl. Qed.
Lemma D_325b4 : decode_any W_325b4 = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325b8 : bv 32 := 0x03450513.
Lemma F_325b8 : fetch_word USEGS (0x325b8 : word) = Some W_325b8.
Proof. vm_refl. Qed.
Lemma D_325b8 : decode_any W_325b8 = Some (OpImm ALU_ADD 10 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325bc : bv 32 := 0x00054503.
Lemma F_325bc : fetch_word USEGS (0x325bc : word) = Some W_325bc.
Proof. vm_refl. Qed.
Lemma D_325bc : decode_any W_325bc = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325c0 : bv 32 := 0x00157513.
Lemma F_325c0 : fetch_word USEGS (0x325c0 : word) = Some W_325c0.
Proof. vm_refl. Qed.
Lemma D_325c0 : decode_any W_325c0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325c4 : bv 32 := 0x00050663.
Lemma F_325c4 : fetch_word USEGS (0x325c4 : word) = Some W_325c4.
Proof. vm_refl. Qed.
Lemma D_325c4 : decode_any W_325c4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325c8 : bv 32 := 0x0040006f.
Lemma F_325c8 : fetch_word USEGS (0x325c8 : word) = Some W_325c8.
Proof. vm_refl. Qed.
Lemma D_325c8 : decode_any W_325c8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325cc : bv 32 := 0x0580006f.
Lemma F_325cc : fetch_word USEGS (0x325cc : word) = Some W_325cc.
Proof. vm_refl. Qed.
Lemma D_325cc : decode_any W_325cc = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325d0 : bv 32 := 0x00081517.
Lemma F_325d0 : fetch_word USEGS (0x325d0 : word) = Some W_325d0.
Proof. vm_refl. Qed.
Lemma D_325d0 : decode_any W_325d0 = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325d4 : bv 32 := 0x01850593.
Lemma F_325d4 : fetch_word USEGS (0x325d4 : word) = Some W_325d4.
Proof. vm_refl. Qed.
Lemma D_325d4 : decode_any W_325d4 = Some (OpImm ALU_ADD 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325d8 : bv 32 := 0x00100513.
Lemma F_325d8 : fetch_word USEGS (0x325d8 : word) = Some W_325d8.
Proof. vm_refl. Qed.
Lemma D_325d8 : decode_any W_325d8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325dc : bv 32 := 0x00a58023.
Lemma F_325dc : fetch_word USEGS (0x325dc : word) = Some W_325dc.
Proof. vm_refl. Qed.
Lemma D_325dc : decode_any W_325dc = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325e0 : bv 32 := 0x00080517.
Lemma F_325e0 : fetch_word USEGS (0x325e0 : word) = Some W_325e0.
Proof. vm_refl. Qed.
Lemma D_325e0 : decode_any W_325e0 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325e4 : bv 32 := 0xb8853503.
Lemma F_325e4 : fetch_word USEGS (0x325e4 : word) = Some W_325e4.
Proof. vm_refl. Qed.
Lemma D_325e4 : decode_any W_325e4 = Some (Load SZ8 true 10 10 2952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325e8 : bv 32 := 0x00050e63.
Lemma F_325e8 : fetch_word USEGS (0x325e8 : word) = Some W_325e8.
Proof. vm_refl. Qed.
Lemma D_325e8 : decode_any W_325e8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325ec : bv 32 := 0x0040006f.
Lemma F_325ec : fetch_word USEGS (0x325ec : word) = Some W_325ec.
Proof. vm_refl. Qed.
Lemma D_325ec : decode_any W_325ec = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325f0 : bv 32 := 0x00081517.
Lemma F_325f0 : fetch_word USEGS (0x325f0 : word) = Some W_325f0.
Proof. vm_refl. Qed.
Lemma D_325f0 : decode_any W_325f0 = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325f4 : bv 32 := 0xce850513.
Lemma F_325f4 : fetch_word USEGS (0x325f4 : word) = Some W_325f4.
Proof. vm_refl. Qed.
Lemma D_325f4 : decode_any W_325f4 = Some (OpImm ALU_ADD 10 10 3304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325f8 : bv 32 := 0x00053503.
Lemma F_325f8 : fetch_word USEGS (0x325f8 : word) = Some W_325f8.
Proof. vm_refl. Qed.
Lemma D_325f8 : decode_any W_325f8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_325fc : bv 32 := 0x7ad630ef.
Lemma F_325fc : fetch_word USEGS (0x325fc : word) = Some W_325fc.
Proof. vm_refl. Qed.
Lemma D_325fc : decode_any W_325fc = Some (Jal 1 409516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32600 : bv 32 := 0x0040006f.
Lemma F_32600 : fetch_word USEGS (0x32600 : word) = Some W_32600.
Proof. vm_refl. Qed.
Lemma D_32600 : decode_any W_32600 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32604 : bv 32 := 0x00080517.
Lemma F_32604 : fetch_word USEGS (0x32604 : word) = Some W_32604.
Proof. vm_refl. Qed.
Lemma D_32604 : decode_any W_32604 = Some (Auipc 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32608 : bv 32 := 0xb6c53503.
Lemma F_32608 : fetch_word USEGS (0x32608 : word) = Some W_32608.
Proof. vm_refl. Qed.
Lemma D_32608 : decode_any W_32608 = Some (Load SZ8 true 10 10 2924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3260c : bv 32 := 0x00050c63.
Lemma F_3260c : fetch_word USEGS (0x3260c : word) = Some W_3260c.
Proof. vm_refl. Qed.
Lemma D_3260c : decode_any W_3260c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32624 : bv 32 := 0x00813083.
Lemma F_32624 : fetch_word USEGS (0x32624 : word) = Some W_32624.
Proof. vm_refl. Qed.
Lemma D_32624 : decode_any W_32624 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32628 : bv 32 := 0x00013403.
Lemma F_32628 : fetch_word USEGS (0x32628 : word) = Some W_32628.
Proof. vm_refl. Qed.
Lemma D_32628 : decode_any W_32628 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3262c : bv 32 := 0x01010113.
Lemma F_3262c : fetch_word USEGS (0x3262c : word) = Some W_3262c.
Proof. vm_refl. Qed.
Lemma D_3262c : decode_any W_3262c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32630 : bv 32 := 0x00008067.
Lemma F_32630 : fetch_word USEGS (0x32630 : word) = Some W_32630.
Proof. vm_refl. Qed.
Lemma D_32630 : decode_any W_32630 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32640 : bv 32 := 0x02913c23.
Lemma F_32640 : fetch_word USEGS (0x32640 : word) = Some W_32640.
Proof. vm_refl. Qed.
Lemma D_32640 : decode_any W_32640 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32644 : bv 32 := 0x03213823.
Lemma F_32644 : fetch_word USEGS (0x32644 : word) = Some W_32644.
Proof. vm_refl. Qed.
Lemma D_32644 : decode_any W_32644 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32648 : bv 32 := 0x03313423.
Lemma F_32648 : fetch_word USEGS (0x32648 : word) = Some W_32648.
Proof. vm_refl. Qed.
Lemma D_32648 : decode_any W_32648 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3264c : bv 32 := 0x03413023.
Lemma F_3264c : fetch_word USEGS (0x3264c : word) = Some W_3264c.
Proof. vm_refl. Qed.
Lemma D_3264c : decode_any W_3264c = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32650 : bv 32 := 0x01513c23.
Lemma F_32650 : fetch_word USEGS (0x32650 : word) = Some W_32650.
Proof. vm_refl. Qed.
Lemma D_32650 : decode_any W_32650 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32654 : bv 32 := 0x01613823.
Lemma F_32654 : fetch_word USEGS (0x32654 : word) = Some W_32654.
Proof. vm_refl. Qed.
Lemma D_32654 : decode_any W_32654 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32658 : bv 32 := 0x01713423.
Lemma F_32658 : fetch_word USEGS (0x32658 : word) = Some W_32658.
Proof. vm_refl. Qed.
Lemma D_32658 : decode_any W_32658 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3265c : bv 32 := 0x00200413.
Lemma F_3265c : fetch_word USEGS (0x3265c : word) = Some W_3265c.
Proof. vm_refl. Qed.
Lemma D_3265c : decode_any W_3265c = Some (OpImm ALU_ADD 8 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32660 : bv 32 := 0x16851663.
Lemma F_32660 : fetch_word USEGS (0x32660 : word) = Some W_32660.
Proof. vm_refl. Qed.
Lemma D_32660 : decode_any W_32660 = Some (Branch BC_NE 10 8 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32664 : bv 32 := 0x0085b903.
Lemma F_32664 : fetch_word USEGS (0x32664 : word) = Some W_32664.
Proof. vm_refl. Qed.
Lemma D_32664 : decode_any W_32664 = Some (Load SZ8 true 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32668 : bv 32 := 0x00090513.
Lemma F_32668 : fetch_word USEGS (0x32668 : word) = Some W_32668.
Proof. vm_refl. Qed.
Lemma D_32668 : decode_any W_32668 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3266c : bv 32 := 0x00000593.
Lemma F_3266c : fetch_word USEGS (0x3266c : word) = Some W_3266c.
Proof. vm_refl. Qed.
Lemma D_3266c : decode_any W_3266c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32688 : bv 32 := 0x24050a63.
Lemma F_32688 : fetch_word USEGS (0x32688 : word) = Some W_32688.
Proof. vm_refl. Qed.
Lemma D_32688 : decode_any W_32688 = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3268c : bv 32 := 0x00050b93.
Lemma F_3268c : fetch_word USEGS (0x3268c : word) = Some W_3268c.
Proof. vm_refl. Qed.
Lemma D_3268c : decode_any W_3268c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32690 : bv 32 := 0x00000993.
Lemma F_32690 : fetch_word USEGS (0x32690 : word) = Some W_32690.
Proof. vm_refl. Qed.
Lemma D_32690 : decode_any W_32690 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32694 : bv 32 := 0x00081517.
Lemma F_32694 : fetch_word USEGS (0x32694 : word) = Some W_32694.
Proof. vm_refl. Qed.
Lemma D_32694 : decode_any W_32694 = Some (Auipc 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32698 : bv 32 := 0xf5550b13.
Lemma F_32698 : fetch_word USEGS (0x32698 : word) = Some W_32698.
Proof. vm_refl. Qed.
Lemma D_32698 : decode_any W_32698 = Some (OpImm ALU_ADD 22 10 3925, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3269c : bv 32 := 0x03501263.
Lemma F_3269c : fetch_word USEGS (0x3269c : word) = Some W_3269c.
Proof. vm_refl. Qed.
Lemma D_3269c : decode_any W_3269c = Some (Branch BC_NE 0 21 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326a4 : bv 32 := 0x01348533.
Lemma F_326a4 : fetch_word USEGS (0x326a4 : word) = Some W_326a4.
Proof. vm_refl. Qed.
Lemma D_326a4 : decode_any W_326a4 = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326a8 : bv 32 := 0x000b0593.
Lemma F_326a8 : fetch_word USEGS (0x326a8 : word) = Some W_326a8.
Proof. vm_refl. Qed.
Lemma D_326a8 : decode_any W_326a8 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326ac : bv 32 := 0x000b8613.
Lemma F_326ac : fetch_word USEGS (0x326ac : word) = Some W_326ac.
Proof. vm_refl. Qed.
Lemma D_326ac : decode_any W_326ac = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326b0 : bv 32 := 0x770740ef.
Lemma F_326b0 : fetch_word USEGS (0x326b0 : word) = Some W_326b0.
Proof. vm_refl. Qed.
Lemma D_326b0 : decode_any W_326b0 = Some (Jal 1 477040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326b4 : bv 32 := 0x013b89b3.
Lemma F_326b4 : fetch_word USEGS (0x326b4 : word) = Some W_326b4.
Proof. vm_refl. Qed.
Lemma D_326b4 : decode_any W_326b4 = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326b8 : bv 32 := 0x00048b93.
Lemma F_326b8 : fetch_word USEGS (0x326b8 : word) = Some W_326b8.
Proof. vm_refl. Qed.
Lemma D_326b8 : decode_any W_326b8 = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326bc : bv 32 := 0x01598663.
Lemma F_326bc : fetch_word USEGS (0x326bc : word) = Some W_326bc.
Proof. vm_refl. Qed.
Lemma D_326bc : decode_any W_326bc = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326c0 : bv 32 := 0x000b8493.
Lemma F_326c0 : fetch_word USEGS (0x326c0 : word) = Some W_326c0.
Proof. vm_refl. Qed.
Lemma D_326c0 : decode_any W_326c0 = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326c4 : bv 32 := 0x03c0006f.
Lemma F_326c4 : fetch_word USEGS (0x326c4 : word) = Some W_326c4.
Proof. vm_refl. Qed.
Lemma D_326c4 : decode_any W_326c4 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326e8 : bv 32 := 0x00048513.
Lemma F_326e8 : fetch_word USEGS (0x326e8 : word) = Some W_326e8.
Proof. vm_refl. Qed.
Lemma D_326e8 : decode_any W_326e8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326ec : bv 32 := 0x000b8593.
Lemma F_326ec : fetch_word USEGS (0x326ec : word) = Some W_326ec.
Proof. vm_refl. Qed.
Lemma D_326ec : decode_any W_326ec = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326f0 : bv 32 := 0x00098613.
Lemma F_326f0 : fetch_word USEGS (0x326f0 : word) = Some W_326f0.
Proof. vm_refl. Qed.
Lemma D_326f0 : decode_any W_326f0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326f4 : bv 32 := 0x72c740ef.
Lemma F_326f4 : fetch_word USEGS (0x326f4 : word) = Some W_326f4.
Proof. vm_refl. Qed.
Lemma D_326f4 : decode_any W_326f4 = Some (Jal 1 476972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326f8 : bv 32 := 0x000b8513.
Lemma F_326f8 : fetch_word USEGS (0x326f8 : word) = Some W_326f8.
Proof. vm_refl. Qed.
Lemma D_326f8 : decode_any W_326f8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_326fc : bv 32 := 0x735650ef.
Lemma F_326fc : fetch_word USEGS (0x326fc : word) = Some W_326fc.
Proof. vm_refl. Qed.
Lemma D_326fc : decode_any W_326fc = Some (Jal 1 417588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32700 : bv 32 := 0x413a8633.
Lemma F_32700 : fetch_word USEGS (0x32700 : word) = Some W_32700.
Proof. vm_refl. Qed.
Lemma D_32700 : decode_any W_32700 = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32704 : bv 32 := 0x00010537.
Lemma F_32704 : fetch_word USEGS (0x32704 : word) = Some W_32704.
Proof. vm_refl. Qed.
Lemma D_32704 : decode_any W_32704 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32708 : bv 32 := 0x00a66463.
Lemma F_32708 : fetch_word USEGS (0x32708 : word) = Some W_32708.
Proof. vm_refl. Qed.
Lemma D_32708 : decode_any W_32708 = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3270c : bv 32 := 0x00010637.
Lemma F_3270c : fetch_word USEGS (0x3270c : word) = Some W_3270c.
Proof. vm_refl. Qed.
Lemma D_3270c : decode_any W_3270c = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32710 : bv 32 := 0x000a0513.
Lemma F_32710 : fetch_word USEGS (0x32710 : word) = Some W_32710.
Proof. vm_refl. Qed.
Lemma D_32710 : decode_any W_32710 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32714 : bv 32 := 0x000b0593.
Lemma F_32714 : fetch_word USEGS (0x32714 : word) = Some W_32714.
Proof. vm_refl. Qed.
Lemma D_32714 : decode_any W_32714 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32718 : bv 32 := 0x574790ef.
Lemma F_32718 : fetch_word USEGS (0x32718 : word) = Some W_32718.
Proof. vm_refl. Qed.
Lemma D_32718 : decode_any W_32718 = Some (Jal 1 497012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3271c : bv 32 := 0x14054263.
Lemma F_3271c : fetch_word USEGS (0x3271c : word) = Some W_3271c.
Proof. vm_refl. Qed.
Lemma D_3271c : decode_any W_3271c = Some (Branch BC_LT 10 0 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32720 : bv 32 := 0x00050b93.
Lemma F_32720 : fetch_word USEGS (0x32720 : word) = Some W_32720.
Proof. vm_refl. Qed.
Lemma D_32720 : decode_any W_32720 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32724 : bv 32 := 0xf80510e3.
Lemma F_32724 : fetch_word USEGS (0x32724 : word) = Some W_32724.
Proof. vm_refl. Qed.
Lemma D_32724 : decode_any W_32724 = Some (Branch BC_NE 10 0 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32728 : bv 32 := 0x000a0513.
Lemma F_32728 : fetch_word USEGS (0x32728 : word) = Some W_32728.
Proof. vm_refl. Qed.
Lemma D_32728 : decode_any W_32728 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3272c : bv 32 := 0x500790ef.
Lemma F_3272c : fetch_word USEGS (0x3272c : word) = Some W_3272c.
Proof. vm_refl. Qed.
Lemma D_3272c : decode_any W_3272c = Some (Jal 1 496896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_327a8 : bv 32 := 0x000ac663.
Lemma F_327a8 : fetch_word USEGS (0x327a8 : word) = Some W_327a8.
Proof. vm_refl. Qed.
Lemma D_327a8 : decode_any W_327a8 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_327ac : bv 32 := 0x00050413.
Lemma F_327ac : fetch_word USEGS (0x327ac : word) = Some W_327ac.
Proof. vm_refl. Qed.
Lemma D_327ac : decode_any W_327ac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_327b0 : bv 32 := 0x0780006f.
Lemma F_327b0 : fetch_word USEGS (0x327b0 : word) = Some W_327b0.
Proof. vm_refl. Qed.
Lemma D_327b0 : decode_any W_327b0 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_327b4 : bv 32 := 0x148000ef.
Lemma F_327b4 : fetch_word USEGS (0x327b4 : word) = Some W_327b4.
Proof. vm_refl. Qed.
Lemma D_327b4 : decode_any W_327b4 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_327b8 : bv 32 := 0x0fb00593.
Lemma F_327b8 : fetch_word USEGS (0x327b8 : word) = Some W_327b8.
Proof. vm_refl. Qed.
Lemma D_327b8 : decode_any W_327b8 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_327bc : bv 32 := 0x00050413.
Lemma F_327bc : fetch_word USEGS (0x327bc : word) = Some W_327bc.
Proof. vm_refl. Qed.
Lemma D_327bc : decode_any W_327bc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_327c0 : bv 32 := 0x06b56463.
Lemma F_327c0 : fetch_word USEGS (0x327c0 : word) = Some W_327c0.
Proof. vm_refl. Qed.
Lemma D_327c0 : decode_any W_327c0 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3283c : bv 32 := 0x03813483.
Lemma F_3283c : fetch_word USEGS (0x3283c : word) = Some W_3283c.
Proof. vm_refl. Qed.
Lemma D_3283c : decode_any W_3283c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32840 : bv 32 := 0x03013903.
Lemma F_32840 : fetch_word USEGS (0x32840 : word) = Some W_32840.
Proof. vm_refl. Qed.
Lemma D_32840 : decode_any W_32840 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_328fc : bv 32 := 0x00000513.
Lemma F_328fc : fetch_word USEGS (0x328fc : word) = Some W_328fc.
Proof. vm_refl. Qed.
Lemma D_328fc : decode_any W_328fc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32900 : bv 32 := 0x00008067.
Lemma F_32900 : fetch_word USEGS (0x32900 : word) = Some W_32900.
Proof. vm_refl. Qed.
Lemma D_32900 : decode_any W_32900 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

