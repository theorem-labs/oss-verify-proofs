(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_dd71c : bv 32 := 0xfff33197.
Lemma F_dd71c : fetch_word Plain.M.loaded_segments (0xdd764 : word) = Some W_dd71c.
Proof. vm_refl. Qed.
Lemma D_dd71c : decode_any W_dd71c = Some (Auipc 3 1048371, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd720 : bv 32 := 0x09c18193.
Lemma F_dd720 : fetch_word Plain.M.loaded_segments (0xdd768 : word) = Some W_dd720.
Proof. vm_refl. Qed.
Lemma D_dd720 : decode_any W_dd720 = Some (OpImm ALU_ADD 3 3 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd724 : bv 32 := 0x00010513.
Lemma F_dd724 : fetch_word Plain.M.loaded_segments (0xdd76c : word) = Some W_dd724.
Proof. vm_refl. Qed.
Lemma D_dd724 : decode_any W_dd724 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd728 : bv 32 := 0xfff23597.
Lemma F_dd728 : fetch_word Plain.M.loaded_segments (0xdd770 : word) = Some W_dd728.
Proof. vm_refl. Qed.
Lemma D_dd728 : decode_any W_dd728 = Some (Auipc 11 1048355, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd72c : bv 32 := 0x89058593.
Lemma F_dd72c : fetch_word Plain.M.loaded_segments (0xdd774 : word) = Some W_dd72c.
Proof. vm_refl. Qed.
Lemma D_dd72c : decode_any W_dd72c = Some (OpImm ALU_ADD 11 11 2192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd730 : bv 32 := 0xff017113.
Lemma F_dd730 : fetch_word Plain.M.loaded_segments (0xdd778 : word) = Some W_dd730.
Proof. vm_refl. Qed.
Lemma D_dd730 : decode_any W_dd730 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd734 : bv 32 := 0x0040006f.
Lemma F_dd734 : fetch_word Plain.M.loaded_segments (0xdd77c : word) = Some W_dd734.
Proof. vm_refl. Qed.
Lemma D_dd734 : decode_any W_dd734 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd738 : bv 32 := 0x00052583.
Lemma F_dd738 : fetch_word Plain.M.loaded_segments (0xdd780 : word) = Some W_dd738.
Proof. vm_refl. Qed.
Lemma D_dd738 : decode_any W_dd738 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd73c : bv 32 := 0x001fd617.
Lemma F_dd73c : fetch_word Plain.M.loaded_segments (0xdd784 : word) = Some W_dd73c.
Proof. vm_refl. Qed.
Lemma D_dd73c : decode_any W_dd73c = Some (Auipc 12 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd740 : bv 32 := 0x001fd697.
Lemma F_dd740 : fetch_word Plain.M.loaded_segments (0xdd788 : word) = Some W_dd740.
Proof. vm_refl. Qed.
Lemma D_dd740 : decode_any W_dd740 = Some (Auipc 13 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd744 : bv 32 := 0x001fd717.
Lemma F_dd744 : fetch_word Plain.M.loaded_segments (0xdd78c : word) = Some W_dd744.
Proof. vm_refl. Qed.
Lemma D_dd744 : decode_any W_dd744 = Some (Auipc 14 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd748 : bv 32 := 0x3ac63783.
Lemma F_dd748 : fetch_word Plain.M.loaded_segments (0xdd790 : word) = Some W_dd748.
Proof. vm_refl. Qed.
Lemma D_dd748 : decode_any W_dd748 = Some (Load SZ8 true 15 12 940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd74c : bv 32 := 0x3b06b683.
Lemma F_dd74c : fetch_word Plain.M.loaded_segments (0xdd794 : word) = Some W_dd74c.
Proof. vm_refl. Qed.
Lemma D_dd74c : decode_any W_dd74c = Some (Load SZ8 true 13 13 944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd750 : bv 32 := 0x3b473703.
Lemma F_dd750 : fetch_word Plain.M.loaded_segments (0xdd798 : word) = Some W_dd750.
Proof. vm_refl. Qed.
Lemma D_dd750 : decode_any W_dd750 = Some (Load SZ8 true 14 14 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd754 : bv 32 := 0x00850613.
Lemma F_dd754 : fetch_word Plain.M.loaded_segments (0xdd79c : word) = Some W_dd754.
Proof. vm_refl. Qed.
Lemma D_dd754 : decode_any W_dd754 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd758 : bv 32 := 0x00078513.
Lemma F_dd758 : fetch_word Plain.M.loaded_segments (0xdd7a0 : word) = Some W_dd758.
Proof. vm_refl. Qed.
Lemma D_dd758 : decode_any W_dd758 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd75c : bv 32 := 0x00000793.
Lemma F_dd75c : fetch_word Plain.M.loaded_segments (0xdd7a4 : word) = Some W_dd75c.
Proof. vm_refl. Qed.
Lemma D_dd75c : decode_any W_dd75c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd760 : bv 32 := 0x00191317.
Lemma F_dd760 : fetch_word Plain.M.loaded_segments (0xdd7a8 : word) = Some W_dd760.
Proof. vm_refl. Qed.
Lemma D_dd760 : decode_any W_dd760 = Some (Auipc 6 401, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd764 : bv 32 := 0x1a430067.
Lemma F_dd764 : fetch_word Plain.M.loaded_segments (0xdd7ac : word) = Some W_dd764.
Proof. vm_refl. Qed.
Lemma D_dd764 : decode_any W_dd764 = Some (Jalr 0 6 420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd768 : bv 32 := 0xff010113.
Lemma F_dd768 : fetch_word Plain.M.loaded_segments (0xdd7b0 : word) = Some W_dd768.
Proof. vm_refl. Qed.
Lemma D_dd768 : decode_any W_dd768 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd76c : bv 32 := 0x00113423.
Lemma F_dd76c : fetch_word Plain.M.loaded_segments (0xdd7b4 : word) = Some W_dd76c.
Proof. vm_refl. Qed.
Lemma D_dd76c : decode_any W_dd76c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd770 : bv 32 := 0x00813023.
Lemma F_dd770 : fetch_word Plain.M.loaded_segments (0xdd7b8 : word) = Some W_dd770.
Proof. vm_refl. Qed.
Lemma D_dd770 : decode_any W_dd770 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd774 : bv 32 := 0x01010413.
Lemma F_dd774 : fetch_word Plain.M.loaded_segments (0xdd7bc : word) = Some W_dd774.
Proof. vm_refl. Qed.
Lemma D_dd774 : decode_any W_dd774 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd778 : bv 32 := 0x001ff517.
Lemma F_dd778 : fetch_word Plain.M.loaded_segments (0xdd7c0 : word) = Some W_dd778.
Proof. vm_refl. Qed.
Lemma D_dd778 : decode_any W_dd778 = Some (Auipc 10 511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd77c : bv 32 := 0x0f050513.
Lemma F_dd77c : fetch_word Plain.M.loaded_segments (0xdd7c4 : word) = Some W_dd77c.
Proof. vm_refl. Qed.
Lemma D_dd77c : decode_any W_dd77c = Some (OpImm ALU_ADD 10 10 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd780 : bv 32 := 0x00054503.
Lemma F_dd780 : fetch_word Plain.M.loaded_segments (0xdd7c8 : word) = Some W_dd780.
Proof. vm_refl. Qed.
Lemma D_dd780 : decode_any W_dd780 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd784 : bv 32 := 0x00157513.
Lemma F_dd784 : fetch_word Plain.M.loaded_segments (0xdd7cc : word) = Some W_dd784.
Proof. vm_refl. Qed.
Lemma D_dd784 : decode_any W_dd784 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd788 : bv 32 := 0x00050663.
Lemma F_dd788 : fetch_word Plain.M.loaded_segments (0xdd7d0 : word) = Some W_dd788.
Proof. vm_refl. Qed.
Lemma D_dd788 : decode_any W_dd788 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd78c : bv 32 := 0x0040006f.
Lemma F_dd78c : fetch_word Plain.M.loaded_segments (0xdd7d4 : word) = Some W_dd78c.
Proof. vm_refl. Qed.
Lemma D_dd78c : decode_any W_dd78c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd790 : bv 32 := 0x03c0006f.
Lemma F_dd790 : fetch_word Plain.M.loaded_segments (0xdd7d8 : word) = Some W_dd790.
Proof. vm_refl. Qed.
Lemma D_dd790 : decode_any W_dd790 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd794 : bv 32 := 0x001ff517.
Lemma F_dd794 : fetch_word Plain.M.loaded_segments (0xdd7dc : word) = Some W_dd794.
Proof. vm_refl. Qed.
Lemma D_dd794 : decode_any W_dd794 = Some (Auipc 10 511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd798 : bv 32 := 0x0d450593.
Lemma F_dd798 : fetch_word Plain.M.loaded_segments (0xdd7e0 : word) = Some W_dd798.
Proof. vm_refl. Qed.
Lemma D_dd798 : decode_any W_dd798 = Some (OpImm ALU_ADD 11 10 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd79c : bv 32 := 0x00100513.
Lemma F_dd79c : fetch_word Plain.M.loaded_segments (0xdd7e4 : word) = Some W_dd79c.
Proof. vm_refl. Qed.
Lemma D_dd79c : decode_any W_dd79c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7a0 : bv 32 := 0x00a58023.
Lemma F_dd7a0 : fetch_word Plain.M.loaded_segments (0xdd7e8 : word) = Some W_dd7a0.
Proof. vm_refl. Qed.
Lemma D_dd7a0 : decode_any W_dd7a0 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7a4 : bv 32 := 0x001fd517.
Lemma F_dd7a4 : fetch_word Plain.M.loaded_segments (0xdd7ec : word) = Some W_dd7a4.
Proof. vm_refl. Qed.
Lemma D_dd7a4 : decode_any W_dd7a4 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7a8 : bv 32 := 0x35c53503.
Lemma F_dd7a8 : fetch_word Plain.M.loaded_segments (0xdd7f0 : word) = Some W_dd7a8.
Proof. vm_refl. Qed.
Lemma D_dd7a8 : decode_any W_dd7a8 = Some (Load SZ8 true 10 10 860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7ac : bv 32 := 0x02050063.
Lemma F_dd7ac : fetch_word Plain.M.loaded_segments (0xdd7f4 : word) = Some W_dd7ac.
Proof. vm_refl. Qed.
Lemma D_dd7ac : decode_any W_dd7ac = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7b0 : bv 32 := 0x0040006f.
Lemma F_dd7b0 : fetch_word Plain.M.loaded_segments (0xdd7f8 : word) = Some W_dd7b0.
Proof. vm_refl. Qed.
Lemma D_dd7b0 : decode_any W_dd7b0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7b4 : bv 32 := 0xfffa4517.
Lemma F_dd7b4 : fetch_word Plain.M.loaded_segments (0xdd7fc : word) = Some W_dd7b4.
Proof. vm_refl. Qed.
Lemma D_dd7b4 : decode_any W_dd7b4 = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7b8 : bv 32 := 0xe7450513.
Lemma F_dd7b8 : fetch_word Plain.M.loaded_segments (0xdd800 : word) = Some W_dd7b8.
Proof. vm_refl. Qed.
Lemma D_dd7b8 : decode_any W_dd7b8 = Some (OpImm ALU_ADD 10 10 3700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7bc : bv 32 := 0x001ff597.
Lemma F_dd7bc : fetch_word Plain.M.loaded_segments (0xdd804 : word) = Some W_dd7bc.
Proof. vm_refl. Qed.
Lemma D_dd7bc : decode_any W_dd7bc = Some (Auipc 11 511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7c0 : bv 32 := 0x0b458593.
Lemma F_dd7c0 : fetch_word Plain.M.loaded_segments (0xdd808 : word) = Some W_dd7c0.
Proof. vm_refl. Qed.
Lemma D_dd7c0 : decode_any W_dd7c0 = Some (OpImm ALU_ADD 11 11 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7c4 : bv 32 := 0x000000ef.
Lemma F_dd7c4 : fetch_word Plain.M.loaded_segments (0xdd80c : word) = Some W_dd7c4.
Proof. vm_refl. Qed.
Lemma D_dd7c4 : decode_any W_dd7c4 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7c8 : bv 32 := 0x0040006f.
Lemma F_dd7c8 : fetch_word Plain.M.loaded_segments (0xdd810 : word) = Some W_dd7c8.
Proof. vm_refl. Qed.
Lemma D_dd7c8 : decode_any W_dd7c8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7cc : bv 32 := 0x00813083.
Lemma F_dd7cc : fetch_word Plain.M.loaded_segments (0xdd814 : word) = Some W_dd7cc.
Proof. vm_refl. Qed.
Lemma D_dd7cc : decode_any W_dd7cc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7d0 : bv 32 := 0x00013403.
Lemma F_dd7d0 : fetch_word Plain.M.loaded_segments (0xdd818 : word) = Some W_dd7d0.
Proof. vm_refl. Qed.
Lemma D_dd7d0 : decode_any W_dd7d0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7d4 : bv 32 := 0x01010113.
Lemma F_dd7d4 : fetch_word Plain.M.loaded_segments (0xdd81c : word) = Some W_dd7d4.
Proof. vm_refl. Qed.
Lemma D_dd7d4 : decode_any W_dd7d4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7d8 : bv 32 := 0x00008067.
Lemma F_dd7d8 : fetch_word Plain.M.loaded_segments (0xdd820 : word) = Some W_dd7d8.
Proof. vm_refl. Qed.
Lemma D_dd7d8 : decode_any W_dd7d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7dc : bv 32 := 0xff010113.
Lemma F_dd7dc : fetch_word Plain.M.loaded_segments (0xdd824 : word) = Some W_dd7dc.
Proof. vm_refl. Qed.
Lemma D_dd7dc : decode_any W_dd7dc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7e0 : bv 32 := 0x00113423.
Lemma F_dd7e0 : fetch_word Plain.M.loaded_segments (0xdd828 : word) = Some W_dd7e0.
Proof. vm_refl. Qed.
Lemma D_dd7e0 : decode_any W_dd7e0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7e4 : bv 32 := 0x00813023.
Lemma F_dd7e4 : fetch_word Plain.M.loaded_segments (0xdd82c : word) = Some W_dd7e4.
Proof. vm_refl. Qed.
Lemma D_dd7e4 : decode_any W_dd7e4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7e8 : bv 32 := 0x01010413.
Lemma F_dd7e8 : fetch_word Plain.M.loaded_segments (0xdd830 : word) = Some W_dd7e8.
Proof. vm_refl. Qed.
Lemma D_dd7e8 : decode_any W_dd7e8 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7ec : bv 32 := 0x001ff517.
Lemma F_dd7ec : fetch_word Plain.M.loaded_segments (0xdd834 : word) = Some W_dd7ec.
Proof. vm_refl. Qed.
Lemma D_dd7ec : decode_any W_dd7ec = Some (Auipc 10 511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7f0 : bv 32 := 0x0c450513.
Lemma F_dd7f0 : fetch_word Plain.M.loaded_segments (0xdd838 : word) = Some W_dd7f0.
Proof. vm_refl. Qed.
Lemma D_dd7f0 : decode_any W_dd7f0 = Some (OpImm ALU_ADD 10 10 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7f4 : bv 32 := 0x00054503.
Lemma F_dd7f4 : fetch_word Plain.M.loaded_segments (0xdd83c : word) = Some W_dd7f4.
Proof. vm_refl. Qed.
Lemma D_dd7f4 : decode_any W_dd7f4 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7f8 : bv 32 := 0x00157513.
Lemma F_dd7f8 : fetch_word Plain.M.loaded_segments (0xdd840 : word) = Some W_dd7f8.
Proof. vm_refl. Qed.
Lemma D_dd7f8 : decode_any W_dd7f8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd7fc : bv 32 := 0x00050663.
Lemma F_dd7fc : fetch_word Plain.M.loaded_segments (0xdd844 : word) = Some W_dd7fc.
Proof. vm_refl. Qed.
Lemma D_dd7fc : decode_any W_dd7fc = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd800 : bv 32 := 0x0040006f.
Lemma F_dd800 : fetch_word Plain.M.loaded_segments (0xdd848 : word) = Some W_dd800.
Proof. vm_refl. Qed.
Lemma D_dd800 : decode_any W_dd800 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd804 : bv 32 := 0x05c0006f.
Lemma F_dd804 : fetch_word Plain.M.loaded_segments (0xdd84c : word) = Some W_dd804.
Proof. vm_refl. Qed.
Lemma D_dd804 : decode_any W_dd804 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd808 : bv 32 := 0x001ff517.
Lemma F_dd808 : fetch_word Plain.M.loaded_segments (0xdd850 : word) = Some W_dd808.
Proof. vm_refl. Qed.
Lemma D_dd808 : decode_any W_dd808 = Some (Auipc 10 511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd80c : bv 32 := 0x0a850593.
Lemma F_dd80c : fetch_word Plain.M.loaded_segments (0xdd854 : word) = Some W_dd80c.
Proof. vm_refl. Qed.
Lemma D_dd80c : decode_any W_dd80c = Some (OpImm ALU_ADD 11 10 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd810 : bv 32 := 0x00100513.
Lemma F_dd810 : fetch_word Plain.M.loaded_segments (0xdd858 : word) = Some W_dd810.
Proof. vm_refl. Qed.
Lemma D_dd810 : decode_any W_dd810 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd814 : bv 32 := 0x00a58023.
Lemma F_dd814 : fetch_word Plain.M.loaded_segments (0xdd85c : word) = Some W_dd814.
Proof. vm_refl. Qed.
Lemma D_dd814 : decode_any W_dd814 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd818 : bv 32 := 0x001fd517.
Lemma F_dd818 : fetch_word Plain.M.loaded_segments (0xdd860 : word) = Some W_dd818.
Proof. vm_refl. Qed.
Lemma D_dd818 : decode_any W_dd818 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd81c : bv 32 := 0x2f053503.
Lemma F_dd81c : fetch_word Plain.M.loaded_segments (0xdd864 : word) = Some W_dd81c.
Proof. vm_refl. Qed.
Lemma D_dd81c : decode_any W_dd81c = Some (Load SZ8 true 10 10 752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd820 : bv 32 := 0x02050063.
Lemma F_dd820 : fetch_word Plain.M.loaded_segments (0xdd868 : word) = Some W_dd820.
Proof. vm_refl. Qed.
Lemma D_dd820 : decode_any W_dd820 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd824 : bv 32 := 0x0040006f.
Lemma F_dd824 : fetch_word Plain.M.loaded_segments (0xdd86c : word) = Some W_dd824.
Proof. vm_refl. Qed.
Lemma D_dd824 : decode_any W_dd824 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd828 : bv 32 := 0x001ff517.
Lemma F_dd828 : fetch_word Plain.M.loaded_segments (0xdd870 : word) = Some W_dd828.
Proof. vm_refl. Qed.
Lemma D_dd828 : decode_any W_dd828 = Some (Auipc 10 511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd82c : bv 32 := 0x8f050513.
Lemma F_dd82c : fetch_word Plain.M.loaded_segments (0xdd874 : word) = Some W_dd82c.
Proof. vm_refl. Qed.
Lemma D_dd82c : decode_any W_dd82c = Some (OpImm ALU_ADD 10 10 2288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd830 : bv 32 := 0x00053503.
Lemma F_dd830 : fetch_word Plain.M.loaded_segments (0xdd878 : word) = Some W_dd830.
Proof. vm_refl. Qed.
Lemma D_dd830 : decode_any W_dd830 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd834 : bv 32 := 0x00191097.
Lemma F_dd834 : fetch_word Plain.M.loaded_segments (0xdd87c : word) = Some W_dd834.
Proof. vm_refl. Qed.
Lemma D_dd834 : decode_any W_dd834 = Some (Auipc 1 401, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd838 : bv 32 := 0x6ec080e7.
Lemma F_dd838 : fetch_word Plain.M.loaded_segments (0xdd880 : word) = Some W_dd838.
Proof. vm_refl. Qed.
Lemma D_dd838 : decode_any W_dd838 = Some (Jalr 1 1 1772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd83c : bv 32 := 0x0040006f.
Lemma F_dd83c : fetch_word Plain.M.loaded_segments (0xdd884 : word) = Some W_dd83c.
Proof. vm_refl. Qed.
Lemma D_dd83c : decode_any W_dd83c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd840 : bv 32 := 0x001fd517.
Lemma F_dd840 : fetch_word Plain.M.loaded_segments (0xdd888 : word) = Some W_dd840.
Proof. vm_refl. Qed.
Lemma D_dd840 : decode_any W_dd840 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd844 : bv 32 := 0x2d053503.
Lemma F_dd844 : fetch_word Plain.M.loaded_segments (0xdd88c : word) = Some W_dd844.
Proof. vm_refl. Qed.
Lemma D_dd844 : decode_any W_dd844 = Some (Load SZ8 true 10 10 720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd848 : bv 32 := 0x00050c63.
Lemma F_dd848 : fetch_word Plain.M.loaded_segments (0xdd890 : word) = Some W_dd848.
Proof. vm_refl. Qed.
Lemma D_dd848 : decode_any W_dd848 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd84c : bv 32 := 0x0040006f.
Lemma F_dd84c : fetch_word Plain.M.loaded_segments (0xdd894 : word) = Some W_dd84c.
Proof. vm_refl. Qed.
Lemma D_dd84c : decode_any W_dd84c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd850 : bv 32 := 0xfffa4517.
Lemma F_dd850 : fetch_word Plain.M.loaded_segments (0xdd898 : word) = Some W_dd850.
Proof. vm_refl. Qed.
Lemma D_dd850 : decode_any W_dd850 = Some (Auipc 10 1048484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd854 : bv 32 := 0xdd850513.
Lemma F_dd854 : fetch_word Plain.M.loaded_segments (0xdd89c : word) = Some W_dd854.
Proof. vm_refl. Qed.
Lemma D_dd854 : decode_any W_dd854 = Some (OpImm ALU_ADD 10 10 3544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd858 : bv 32 := 0x000000ef.
Lemma F_dd858 : fetch_word Plain.M.loaded_segments (0xdd8a0 : word) = Some W_dd858.
Proof. vm_refl. Qed.
Lemma D_dd858 : decode_any W_dd858 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd85c : bv 32 := 0x0040006f.
Lemma F_dd85c : fetch_word Plain.M.loaded_segments (0xdd8a4 : word) = Some W_dd85c.
Proof. vm_refl. Qed.
Lemma D_dd85c : decode_any W_dd85c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd860 : bv 32 := 0x00813083.
Lemma F_dd860 : fetch_word Plain.M.loaded_segments (0xdd8a8 : word) = Some W_dd860.
Proof. vm_refl. Qed.
Lemma D_dd860 : decode_any W_dd860 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd864 : bv 32 := 0x00013403.
Lemma F_dd864 : fetch_word Plain.M.loaded_segments (0xdd8ac : word) = Some W_dd864.
Proof. vm_refl. Qed.
Lemma D_dd864 : decode_any W_dd864 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd868 : bv 32 := 0x01010113.
Lemma F_dd868 : fetch_word Plain.M.loaded_segments (0xdd8b0 : word) = Some W_dd868.
Proof. vm_refl. Qed.
Lemma D_dd868 : decode_any W_dd868 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd86c : bv 32 := 0x00008067.
Lemma F_dd86c : fetch_word Plain.M.loaded_segments (0xdd8b4 : word) = Some W_dd86c.
Proof. vm_refl. Qed.
Lemma D_dd86c : decode_any W_dd86c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd870 : bv 32 := 0xfb010113.
Lemma F_dd870 : fetch_word Plain.M.loaded_segments (0xdd8b8 : word) = Some W_dd870.
Proof. vm_refl. Qed.
Lemma D_dd870 : decode_any W_dd870 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd874 : bv 32 := 0x04113423.
Lemma F_dd874 : fetch_word Plain.M.loaded_segments (0xdd8bc : word) = Some W_dd874.
Proof. vm_refl. Qed.
Lemma D_dd874 : decode_any W_dd874 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd878 : bv 32 := 0x04813023.
Lemma F_dd878 : fetch_word Plain.M.loaded_segments (0xdd8c0 : word) = Some W_dd878.
Proof. vm_refl. Qed.
Lemma D_dd878 : decode_any W_dd878 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd87c : bv 32 := 0x02913c23.
Lemma F_dd87c : fetch_word Plain.M.loaded_segments (0xdd8c4 : word) = Some W_dd87c.
Proof. vm_refl. Qed.
Lemma D_dd87c : decode_any W_dd87c = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd880 : bv 32 := 0x03213823.
Lemma F_dd880 : fetch_word Plain.M.loaded_segments (0xdd8c8 : word) = Some W_dd880.
Proof. vm_refl. Qed.
Lemma D_dd880 : decode_any W_dd880 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd884 : bv 32 := 0x03313423.
Lemma F_dd884 : fetch_word Plain.M.loaded_segments (0xdd8cc : word) = Some W_dd884.
Proof. vm_refl. Qed.
Lemma D_dd884 : decode_any W_dd884 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd888 : bv 32 := 0x03413023.
Lemma F_dd888 : fetch_word Plain.M.loaded_segments (0xdd8d0 : word) = Some W_dd888.
Proof. vm_refl. Qed.
Lemma D_dd888 : decode_any W_dd888 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd88c : bv 32 := 0x01513c23.
Lemma F_dd88c : fetch_word Plain.M.loaded_segments (0xdd8d4 : word) = Some W_dd88c.
Proof. vm_refl. Qed.
Lemma D_dd88c : decode_any W_dd88c = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd890 : bv 32 := 0x01613823.
Lemma F_dd890 : fetch_word Plain.M.loaded_segments (0xdd8d8 : word) = Some W_dd890.
Proof. vm_refl. Qed.
Lemma D_dd890 : decode_any W_dd890 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd894 : bv 32 := 0x01713423.
Lemma F_dd894 : fetch_word Plain.M.loaded_segments (0xdd8dc : word) = Some W_dd894.
Proof. vm_refl. Qed.
Lemma D_dd894 : decode_any W_dd894 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd898 : bv 32 := 0x00200413.
Lemma F_dd898 : fetch_word Plain.M.loaded_segments (0xdd8e0 : word) = Some W_dd898.
Proof. vm_refl. Qed.
Lemma D_dd898 : decode_any W_dd898 = Some (OpImm ALU_ADD 8 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd89c : bv 32 := 0x18851663.
Lemma F_dd89c : fetch_word Plain.M.loaded_segments (0xdd8e4 : word) = Some W_dd89c.
Proof. vm_refl. Qed.
Lemma D_dd89c : decode_any W_dd89c = Some (Branch BC_NE 10 8 396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8a0 : bv 32 := 0x0085b903.
Lemma F_dd8a0 : fetch_word Plain.M.loaded_segments (0xdd8e8 : word) = Some W_dd8a0.
Proof. vm_refl. Qed.
Lemma D_dd8a0 : decode_any W_dd8a0 = Some (Load SZ8 true 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8a4 : bv 32 := 0x00090513.
Lemma F_dd8a4 : fetch_word Plain.M.loaded_segments (0xdd8ec : word) = Some W_dd8a4.
Proof. vm_refl. Qed.
Lemma D_dd8a4 : decode_any W_dd8a4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8a8 : bv 32 := 0x00000593.
Lemma F_dd8a8 : fetch_word Plain.M.loaded_segments (0xdd8f0 : word) = Some W_dd8a8.
Proof. vm_refl. Qed.
Lemma D_dd8a8 : decode_any W_dd8a8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8ac : bv 32 := 0x00192097.
Lemma F_dd8ac : fetch_word Plain.M.loaded_segments (0xdd8f4 : word) = Some W_dd8ac.
Proof. vm_refl. Qed.
Lemma D_dd8ac : decode_any W_dd8ac = Some (Auipc 1 402, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8b0 : bv 32 := 0x804080e7.
Lemma F_dd8b0 : fetch_word Plain.M.loaded_segments (0xdd8f8 : word) = Some W_dd8b0.
Proof. vm_refl. Qed.
Lemma D_dd8b0 : decode_any W_dd8b0 = Some (Jalr 1 1 2052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8b4 : bv 32 := 0x28054263.
Lemma F_dd8b4 : fetch_word Plain.M.loaded_segments (0xdd8fc : word) = Some W_dd8b4.
Proof. vm_refl. Qed.
Lemma D_dd8b4 : decode_any W_dd8b4 = Some (Branch BC_LT 10 0 644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8b8 : bv 32 := 0x00050a13.
Lemma F_dd8b8 : fetch_word Plain.M.loaded_segments (0xdd900 : word) = Some W_dd8b8.
Proof. vm_refl. Qed.
Lemma D_dd8b8 : decode_any W_dd8b8 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8bc : bv 32 := 0x00010537.
Lemma F_dd8bc : fetch_word Plain.M.loaded_segments (0xdd904 : word) = Some W_dd8bc.
Proof. vm_refl. Qed.
Lemma D_dd8bc : decode_any W_dd8bc = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8c0 : bv 32 := 0x00010ab7.
Lemma F_dd8c0 : fetch_word Plain.M.loaded_segments (0xdd908 : word) = Some W_dd8c0.
Proof. vm_refl. Qed.
Lemma D_dd8c0 : decode_any W_dd8c0 = Some (Lui 21 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8c4 : bv 32 := 0x00192097.
Lemma F_dd8c4 : fetch_word Plain.M.loaded_segments (0xdd90c : word) = Some W_dd8c4.
Proof. vm_refl. Qed.
Lemma D_dd8c4 : decode_any W_dd8c4 = Some (Auipc 1 402, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8c8 : bv 32 := 0xbdc080e7.
Lemma F_dd8c8 : fetch_word Plain.M.loaded_segments (0xdd910 : word) = Some W_dd8c8.
Proof. vm_refl. Qed.
Lemma D_dd8c8 : decode_any W_dd8c8 = Some (Jalr 1 1 3036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8cc : bv 32 := 0x28050263.
Lemma F_dd8cc : fetch_word Plain.M.loaded_segments (0xdd914 : word) = Some W_dd8cc.
Proof. vm_refl. Qed.
Lemma D_dd8cc : decode_any W_dd8cc = Some (Branch BC_EQ 10 0 644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8d0 : bv 32 := 0x00050b93.
Lemma F_dd8d0 : fetch_word Plain.M.loaded_segments (0xdd918 : word) = Some W_dd8d0.
Proof. vm_refl. Qed.
Lemma D_dd8d0 : decode_any W_dd8d0 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8d4 : bv 32 := 0x00000993.
Lemma F_dd8d4 : fetch_word Plain.M.loaded_segments (0xdd91c : word) = Some W_dd8d4.
Proof. vm_refl. Qed.
Lemma D_dd8d4 : decode_any W_dd8d4 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8d8 : bv 32 := 0x001ff517.
Lemma F_dd8d8 : fetch_word Plain.M.loaded_segments (0xdd920 : word) = Some W_dd8d8.
Proof. vm_refl. Qed.
Lemma D_dd8d8 : decode_any W_dd8d8 = Some (Auipc 10 511, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8dc : bv 32 := 0xfd950b13.
Lemma F_dd8dc : fetch_word Plain.M.loaded_segments (0xdd924 : word) = Some W_dd8dc.
Proof. vm_refl. Qed.
Lemma D_dd8dc : decode_any W_dd8dc = Some (OpImm ALU_ADD 22 10 4057, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8e0 : bv 32 := 0x03501463.
Lemma F_dd8e0 : fetch_word Plain.M.loaded_segments (0xdd928 : word) = Some W_dd8e0.
Proof. vm_refl. Qed.
Lemma D_dd8e0 : decode_any W_dd8e0 = Some (Branch BC_NE 0 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8e4 : bv 32 := 0x02c0006f.
Lemma F_dd8e4 : fetch_word Plain.M.loaded_segments (0xdd92c : word) = Some W_dd8e4.
Proof. vm_refl. Qed.
Lemma D_dd8e4 : decode_any W_dd8e4 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8e8 : bv 32 := 0x01348533.
Lemma F_dd8e8 : fetch_word Plain.M.loaded_segments (0xdd930 : word) = Some W_dd8e8.
Proof. vm_refl. Qed.
Lemma D_dd8e8 : decode_any W_dd8e8 = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8ec : bv 32 := 0x000b0593.
Lemma F_dd8ec : fetch_word Plain.M.loaded_segments (0xdd934 : word) = Some W_dd8ec.
Proof. vm_refl. Qed.
Lemma D_dd8ec : decode_any W_dd8ec = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8f0 : bv 32 := 0x000b8613.
Lemma F_dd8f0 : fetch_word Plain.M.loaded_segments (0xdd938 : word) = Some W_dd8f0.
Proof. vm_refl. Qed.
Lemma D_dd8f0 : decode_any W_dd8f0 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8f4 : bv 32 := 0x0019c097.
Lemma F_dd8f4 : fetch_word Plain.M.loaded_segments (0xdd93c : word) = Some W_dd8f4.
Proof. vm_refl. Qed.
Lemma D_dd8f4 : decode_any W_dd8f4 = Some (Auipc 1 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8f8 : bv 32 := 0xf80080e7.
Lemma F_dd8f8 : fetch_word Plain.M.loaded_segments (0xdd940 : word) = Some W_dd8f8.
Proof. vm_refl. Qed.
Lemma D_dd8f8 : decode_any W_dd8f8 = Some (Jalr 1 1 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd8fc : bv 32 := 0x013b89b3.
Lemma F_dd8fc : fetch_word Plain.M.loaded_segments (0xdd944 : word) = Some W_dd8fc.
Proof. vm_refl. Qed.
Lemma D_dd8fc : decode_any W_dd8fc = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd900 : bv 32 := 0x00048b93.
Lemma F_dd900 : fetch_word Plain.M.loaded_segments (0xdd948 : word) = Some W_dd900.
Proof. vm_refl. Qed.
Lemma D_dd900 : decode_any W_dd900 = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd904 : bv 32 := 0x01598663.
Lemma F_dd904 : fetch_word Plain.M.loaded_segments (0xdd94c : word) = Some W_dd904.
Proof. vm_refl. Qed.
Lemma D_dd904 : decode_any W_dd904 = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd908 : bv 32 := 0x000b8493.
Lemma F_dd908 : fetch_word Plain.M.loaded_segments (0xdd950 : word) = Some W_dd908.
Proof. vm_refl. Qed.
Lemma D_dd908 : decode_any W_dd908 = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd90c : bv 32 := 0x0480006f.
Lemma F_dd90c : fetch_word Plain.M.loaded_segments (0xdd954 : word) = Some W_dd90c.
Proof. vm_refl. Qed.
Lemma D_dd90c : decode_any W_dd90c = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd910 : bv 32 := 0x01a9d513.
Lemma F_dd910 : fetch_word Plain.M.loaded_segments (0xdd958 : word) = Some W_dd910.
Proof. vm_refl. Qed.
Lemma D_dd910 : decode_any W_dd910 = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd914 : bv 32 := 0x1c051863.
Lemma F_dd914 : fetch_word Plain.M.loaded_segments (0xdd95c : word) = Some W_dd914.
Proof. vm_refl. Qed.
Lemma D_dd914 : decode_any W_dd914 = Some (Branch BC_NE 10 0 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd918 : bv 32 := 0x00199a93.
Lemma F_dd918 : fetch_word Plain.M.loaded_segments (0xdd960 : word) = Some W_dd918.
Proof. vm_refl. Qed.
Lemma D_dd918 : decode_any W_dd918 = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd91c : bv 32 := 0x000a8513.
Lemma F_dd91c : fetch_word Plain.M.loaded_segments (0xdd964 : word) = Some W_dd91c.
Proof. vm_refl. Qed.
Lemma D_dd91c : decode_any W_dd91c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd920 : bv 32 := 0x00192097.
Lemma F_dd920 : fetch_word Plain.M.loaded_segments (0xdd968 : word) = Some W_dd920.
Proof. vm_refl. Qed.
Lemma D_dd920 : decode_any W_dd920 = Some (Auipc 1 402, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd924 : bv 32 := 0xb80080e7.
Lemma F_dd924 : fetch_word Plain.M.loaded_segments (0xdd96c : word) = Some W_dd924.
Proof. vm_refl. Qed.
Lemma D_dd924 : decode_any W_dd924 = Some (Jalr 1 1 2944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd928 : bv 32 := 0x1e050063.
Lemma F_dd928 : fetch_word Plain.M.loaded_segments (0xdd970 : word) = Some W_dd928.
Proof. vm_refl. Qed.
Lemma D_dd928 : decode_any W_dd928 = Some (Branch BC_EQ 10 0 480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd92c : bv 32 := 0x00050493.
Lemma F_dd92c : fetch_word Plain.M.loaded_segments (0xdd974 : word) = Some W_dd92c.
Proof. vm_refl. Qed.
Lemma D_dd92c : decode_any W_dd92c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd930 : bv 32 := 0x00098c63.
Lemma F_dd930 : fetch_word Plain.M.loaded_segments (0xdd978 : word) = Some W_dd930.
Proof. vm_refl. Qed.
Lemma D_dd930 : decode_any W_dd930 = Some (Branch BC_EQ 19 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd934 : bv 32 := 0x00048513.
Lemma F_dd934 : fetch_word Plain.M.loaded_segments (0xdd97c : word) = Some W_dd934.
Proof. vm_refl. Qed.
Lemma D_dd934 : decode_any W_dd934 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd938 : bv 32 := 0x000b8593.
Lemma F_dd938 : fetch_word Plain.M.loaded_segments (0xdd980 : word) = Some W_dd938.
Proof. vm_refl. Qed.
Lemma D_dd938 : decode_any W_dd938 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd93c : bv 32 := 0x00098613.
Lemma F_dd93c : fetch_word Plain.M.loaded_segments (0xdd984 : word) = Some W_dd93c.
Proof. vm_refl. Qed.
Lemma D_dd93c : decode_any W_dd93c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd940 : bv 32 := 0x0019c097.
Lemma F_dd940 : fetch_word Plain.M.loaded_segments (0xdd988 : word) = Some W_dd940.
Proof. vm_refl. Qed.
Lemma D_dd940 : decode_any W_dd940 = Some (Auipc 1 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd944 : bv 32 := 0xf34080e7.
Lemma F_dd944 : fetch_word Plain.M.loaded_segments (0xdd98c : word) = Some W_dd944.
Proof. vm_refl. Qed.
Lemma D_dd944 : decode_any W_dd944 = Some (Jalr 1 1 3892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd948 : bv 32 := 0x000b8513.
Lemma F_dd948 : fetch_word Plain.M.loaded_segments (0xdd990 : word) = Some W_dd948.
Proof. vm_refl. Qed.
Lemma D_dd948 : decode_any W_dd948 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd94c : bv 32 := 0x00192097.
Lemma F_dd94c : fetch_word Plain.M.loaded_segments (0xdd994 : word) = Some W_dd94c.
Proof. vm_refl. Qed.
Lemma D_dd94c : decode_any W_dd94c = Some (Auipc 1 402, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd950 : bv 32 := 0xa14080e7.
Lemma F_dd950 : fetch_word Plain.M.loaded_segments (0xdd998 : word) = Some W_dd950.
Proof. vm_refl. Qed.
Lemma D_dd950 : decode_any W_dd950 = Some (Jalr 1 1 2580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd954 : bv 32 := 0x413a8633.
Lemma F_dd954 : fetch_word Plain.M.loaded_segments (0xdd99c : word) = Some W_dd954.
Proof. vm_refl. Qed.
Lemma D_dd954 : decode_any W_dd954 = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd958 : bv 32 := 0x00010537.
Lemma F_dd958 : fetch_word Plain.M.loaded_segments (0xdd9a0 : word) = Some W_dd958.
Proof. vm_refl. Qed.
Lemma D_dd958 : decode_any W_dd958 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd95c : bv 32 := 0x00a66463.
Lemma F_dd95c : fetch_word Plain.M.loaded_segments (0xdd9a4 : word) = Some W_dd95c.
Proof. vm_refl. Qed.
Lemma D_dd95c : decode_any W_dd95c = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd960 : bv 32 := 0x00010637.
Lemma F_dd960 : fetch_word Plain.M.loaded_segments (0xdd9a8 : word) = Some W_dd960.
Proof. vm_refl. Qed.
Lemma D_dd960 : decode_any W_dd960 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd964 : bv 32 := 0x000a0513.
Lemma F_dd964 : fetch_word Plain.M.loaded_segments (0xdd9ac : word) = Some W_dd964.
Proof. vm_refl. Qed.
Lemma D_dd964 : decode_any W_dd964 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd968 : bv 32 := 0x000b0593.
Lemma F_dd968 : fetch_word Plain.M.loaded_segments (0xdd9b0 : word) = Some W_dd968.
Proof. vm_refl. Qed.
Lemma D_dd968 : decode_any W_dd968 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd96c : bv 32 := 0x001a0097.
Lemma F_dd96c : fetch_word Plain.M.loaded_segments (0xdd9b4 : word) = Some W_dd96c.
Proof. vm_refl. Qed.
Lemma D_dd96c : decode_any W_dd96c = Some (Auipc 1 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd970 : bv 32 := 0x5d8080e7.
Lemma F_dd970 : fetch_word Plain.M.loaded_segments (0xdd9b8 : word) = Some W_dd970.
Proof. vm_refl. Qed.
Lemma D_dd970 : decode_any W_dd970 = Some (Jalr 1 1 1496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd974 : bv 32 := 0x14054a63.
Lemma F_dd974 : fetch_word Plain.M.loaded_segments (0xdd9bc : word) = Some W_dd974.
Proof. vm_refl. Qed.
Lemma D_dd974 : decode_any W_dd974 = Some (Branch BC_LT 10 0 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd978 : bv 32 := 0x00050b93.
Lemma F_dd978 : fetch_word Plain.M.loaded_segments (0xdd9c0 : word) = Some W_dd978.
Proof. vm_refl. Qed.
Lemma D_dd978 : decode_any W_dd978 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd97c : bv 32 := 0xf60516e3.
Lemma F_dd97c : fetch_word Plain.M.loaded_segments (0xdd9c4 : word) = Some W_dd97c.
Proof. vm_refl. Qed.
Lemma D_dd97c : decode_any W_dd97c = Some (Branch BC_NE 10 0 8044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd980 : bv 32 := 0x000a0513.
Lemma F_dd980 : fetch_word Plain.M.loaded_segments (0xdd9c8 : word) = Some W_dd980.
Proof. vm_refl. Qed.
Lemma D_dd980 : decode_any W_dd980 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd984 : bv 32 := 0x001a0097.
Lemma F_dd984 : fetch_word Plain.M.loaded_segments (0xdd9cc : word) = Some W_dd984.
Proof. vm_refl. Qed.
Lemma D_dd984 : decode_any W_dd984 = Some (Auipc 1 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd988 : bv 32 := 0x520080e7.
Lemma F_dd988 : fetch_word Plain.M.loaded_segments (0xdd9d0 : word) = Some W_dd988.
Proof. vm_refl. Qed.
Lemma D_dd988 : decode_any W_dd988 = Some (Jalr 1 1 1312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd98c : bv 32 := 0x00500513.
Lemma F_dd98c : fetch_word Plain.M.loaded_segments (0xdd9d4 : word) = Some W_dd98c.
Proof. vm_refl. Qed.
Lemma D_dd98c : decode_any W_dd98c = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd990 : bv 32 := 0x0b357e63.
Lemma F_dd990 : fetch_word Plain.M.loaded_segments (0xdd9d8 : word) = Some W_dd990.
Proof. vm_refl. Qed.
Lemma D_dd990 : decode_any W_dd990 = Some (Branch BC_GEU 10 19 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd994 : bv 32 := 0x00148a83.
Lemma F_dd994 : fetch_word Plain.M.loaded_segments (0xdd9dc : word) = Some W_dd994.
Proof. vm_refl. Qed.
Lemma D_dd994 : decode_any W_dd994 = Some (Load SZ1 true 21 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd998 : bv 32 := 0x0004c503.
Lemma F_dd998 : fetch_word Plain.M.loaded_segments (0xdd9e0 : word) = Some W_dd998.
Proof. vm_refl. Qed.
Lemma D_dd998 : decode_any W_dd998 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd99c : bv 32 := 0x039a9593.
Lemma F_dd99c : fetch_word Plain.M.loaded_segments (0xdd9e4 : word) = Some W_dd99c.
Proof. vm_refl. Qed.
Lemma D_dd99c : decode_any W_dd99c = Some (ShiftImm ALU_SLL 11 21 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9a0 : bv 32 := 0x0315d593.
Lemma F_dd9a0 : fetch_word Plain.M.loaded_segments (0xdd9e8 : word) = Some W_dd9a0.
Proof. vm_refl. Qed.
Lemma D_dd9a0 : decode_any W_dd9a0 = Some (ShiftImm ALU_SRL 11 11 49, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9a4 : bv 32 := 0x00a5e933.
Lemma F_dd9a4 : fetch_word Plain.M.loaded_segments (0xdd9ec : word) = Some W_dd9a4.
Proof. vm_refl. Qed.
Lemma D_dd9a4 : decode_any W_dd9a4 = Some (Op ALU_OR 18 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9a8 : bv 32 := 0x00690513.
Lemma F_dd9a8 : fetch_word Plain.M.loaded_segments (0xdd9f0 : word) = Some W_dd9a8.
Proof. vm_refl. Qed.
Lemma D_dd9a8 : decode_any W_dd9a8 = Some (OpImm ALU_ADD 10 18 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9ac : bv 32 := 0x0aa9ee63.
Lemma F_dd9ac : fetch_word Plain.M.loaded_segments (0xdd9f4 : word) = Some W_dd9ac.
Proof. vm_refl. Qed.
Lemma D_dd9ac : decode_any W_dd9ac = Some (Branch BC_LTU 19 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9b0 : bv 32 := 0x00248413.
Lemma F_dd9b0 : fetch_word Plain.M.loaded_segments (0xdd9f8 : word) = Some W_dd9b0.
Proof. vm_refl. Qed.
Lemma D_dd9b0 : decode_any W_dd9b0 = Some (OpImm ALU_ADD 8 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9b4 : bv 32 := 0x01240533.
Lemma F_dd9b4 : fetch_word Plain.M.loaded_segments (0xdd9fc : word) = Some W_dd9b4.
Proof. vm_refl. Qed.
Lemma D_dd9b4 : decode_any W_dd9b4 = Some (Op ALU_ADD 10 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9b8 : bv 32 := 0x00154583.
Lemma F_dd9b8 : fetch_word Plain.M.loaded_segments (0xdda00 : word) = Some W_dd9b8.
Proof. vm_refl. Qed.
Lemma D_dd9b8 : decode_any W_dd9b8 = Some (Load SZ1 false 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9bc : bv 32 := 0x00054603.
Lemma F_dd9bc : fetch_word Plain.M.loaded_segments (0xdda04 : word) = Some W_dd9bc.
Proof. vm_refl. Qed.
Lemma D_dd9bc : decode_any W_dd9bc = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9c0 : bv 32 := 0x00254683.
Lemma F_dd9c0 : fetch_word Plain.M.loaded_segments (0xdda08 : word) = Some W_dd9c0.
Proof. vm_refl. Qed.
Lemma D_dd9c0 : decode_any W_dd9c0 = Some (Load SZ1 false 13 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9c4 : bv 32 := 0x00354703.
Lemma F_dd9c4 : fetch_word Plain.M.loaded_segments (0xdda0c : word) = Some W_dd9c4.
Proof. vm_refl. Qed.
Lemma D_dd9c4 : decode_any W_dd9c4 = Some (Load SZ1 false 14 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9c8 : bv 32 := 0x00859593.
Lemma F_dd9c8 : fetch_word Plain.M.loaded_segments (0xdda10 : word) = Some W_dd9c8.
Proof. vm_refl. Qed.
Lemma D_dd9c8 : decode_any W_dd9c8 = Some (ShiftImm ALU_SLL 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9cc : bv 32 := 0x00c5e5b3.
Lemma F_dd9cc : fetch_word Plain.M.loaded_segments (0xdda14 : word) = Some W_dd9cc.
Proof. vm_refl. Qed.
Lemma D_dd9cc : decode_any W_dd9cc = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9d0 : bv 32 := 0x41298a33.
Lemma F_dd9d0 : fetch_word Plain.M.loaded_segments (0xdda18 : word) = Some W_dd9d0.
Proof. vm_refl. Qed.
Lemma D_dd9d0 : decode_any W_dd9d0 = Some (Op ALU_SUB 20 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9d4 : bv 32 := 0x00450993.
Lemma F_dd9d4 : fetch_word Plain.M.loaded_segments (0xdda1c : word) = Some W_dd9d4.
Proof. vm_refl. Qed.
Lemma D_dd9d4 : decode_any W_dd9d4 = Some (OpImm ALU_ADD 19 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9d8 : bv 32 := 0x01069693.
Lemma F_dd9d8 : fetch_word Plain.M.loaded_segments (0xdda20 : word) = Some W_dd9d8.
Proof. vm_refl. Qed.
Lemma D_dd9d8 : decode_any W_dd9d8 = Some (ShiftImm ALU_SLL 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9dc : bv 32 := 0x0187151b.
Lemma F_dd9dc : fetch_word Plain.M.loaded_segments (0xdda24 : word) = Some W_dd9dc.
Proof. vm_refl. Qed.
Lemma D_dd9dc : decode_any W_dd9dc = Some (ShiftImm32 ALU_SLL 10 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9e0 : bv 32 := 0x00a6e533.
Lemma F_dd9e0 : fetch_word Plain.M.loaded_segments (0xdda28 : word) = Some W_dd9e0.
Proof. vm_refl. Qed.
Lemma D_dd9e0 : decode_any W_dd9e0 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9e4 : bv 32 := 0x00a5e533.
Lemma F_dd9e4 : fetch_word Plain.M.loaded_segments (0xdda2c : word) = Some W_dd9e4.
Proof. vm_refl. Qed.
Lemma D_dd9e4 : decode_any W_dd9e4 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9e8 : bv 32 := 0xffaa0a13.
Lemma F_dd9e8 : fetch_word Plain.M.loaded_segments (0xdda30 : word) = Some W_dd9e8.
Proof. vm_refl. Qed.
Lemma D_dd9e8 : decode_any W_dd9e8 = Some (OpImm ALU_ADD 20 20 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9ec : bv 32 := 0x180000ef.
Lemma F_dd9ec : fetch_word Plain.M.loaded_segments (0xdda34 : word) = Some W_dd9ec.
Proof. vm_refl. Qed.
Lemma D_dd9ec : decode_any W_dd9ec = Some (Jal 1 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9f0 : bv 32 := 0x00040513.
Lemma F_dd9f0 : fetch_word Plain.M.loaded_segments (0xdda38 : word) = Some W_dd9f0.
Proof. vm_refl. Qed.
Lemma D_dd9f0 : decode_any W_dd9f0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9f4 : bv 32 := 0x00090593.
Lemma F_dd9f4 : fetch_word Plain.M.loaded_segments (0xdda3c : word) = Some W_dd9f4.
Proof. vm_refl. Qed.
Lemma D_dd9f4 : decode_any W_dd9f4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9f8 : bv 32 := 0x00098613.
Lemma F_dd9f8 : fetch_word Plain.M.loaded_segments (0xdda40 : word) = Some W_dd9f8.
Proof. vm_refl. Qed.
Lemma D_dd9f8 : decode_any W_dd9f8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd9fc : bv 32 := 0x000a0693.
Lemma F_dd9fc : fetch_word Plain.M.loaded_segments (0xdda44 : word) = Some W_dd9fc.
Proof. vm_refl. Qed.
Lemma D_dd9fc : decode_any W_dd9fc = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda00 : bv 32 := 0x178000ef.
Lemma F_dda00 : fetch_word Plain.M.loaded_segments (0xdda48 : word) = Some W_dda00.
Proof. vm_refl. Qed.
Lemma D_dda00 : decode_any W_dda00 = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda04 : bv 32 := 0x000ac663.
Lemma F_dda04 : fetch_word Plain.M.loaded_segments (0xdda4c : word) = Some W_dda04.
Proof. vm_refl. Qed.
Lemma D_dda04 : decode_any W_dda04 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda08 : bv 32 := 0x00050413.
Lemma F_dda08 : fetch_word Plain.M.loaded_segments (0xdda50 : word) = Some W_dda08.
Proof. vm_refl. Qed.
Lemma D_dda08 : decode_any W_dda08 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda0c : bv 32 := 0x0800006f.
Lemma F_dda0c : fetch_word Plain.M.loaded_segments (0xdda54 : word) = Some W_dda0c.
Proof. vm_refl. Qed.
Lemma D_dda0c : decode_any W_dda0c = Some (Jal 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda10 : bv 32 := 0x160000ef.
Lemma F_dda10 : fetch_word Plain.M.loaded_segments (0xdda58 : word) = Some W_dda10.
Proof. vm_refl. Qed.
Lemma D_dda10 : decode_any W_dda10 = Some (Jal 1 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda14 : bv 32 := 0x0fb00593.
Lemma F_dda14 : fetch_word Plain.M.loaded_segments (0xdda5c : word) = Some W_dda14.
Proof. vm_refl. Qed.
Lemma D_dda14 : decode_any W_dda14 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda18 : bv 32 := 0x00050413.
Lemma F_dda18 : fetch_word Plain.M.loaded_segments (0xdda60 : word) = Some W_dda18.
Proof. vm_refl. Qed.
Lemma D_dda18 : decode_any W_dda18 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda1c : bv 32 := 0x06b56863.
Lemma F_dda1c : fetch_word Plain.M.loaded_segments (0xdda64 : word) = Some W_dda1c.
Proof. vm_refl. Qed.
Lemma D_dda1c : decode_any W_dda1c = Some (Branch BC_LTU 10 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda20 : bv 32 := 0x0fb00413.
Lemma F_dda20 : fetch_word Plain.M.loaded_segments (0xdda68 : word) = Some W_dda20.
Proof. vm_refl. Qed.
Lemma D_dda20 : decode_any W_dda20 = Some (OpImm ALU_ADD 8 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda24 : bv 32 := 0x0680006f.
Lemma F_dda24 : fetch_word Plain.M.loaded_segments (0xdda6c : word) = Some W_dda24.
Proof. vm_refl. Qed.
Lemma D_dda24 : decode_any W_dda24 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda28 : bv 32 := 0x001fd517.
Lemma F_dda28 : fetch_word Plain.M.loaded_segments (0xdda70 : word) = Some W_dda28.
Proof. vm_refl. Qed.
Lemma D_dda28 : decode_any W_dda28 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda2c : bv 32 := 0x0f053503.
Lemma F_dda2c : fetch_word Plain.M.loaded_segments (0xdda74 : word) = Some W_dda2c.
Proof. vm_refl. Qed.
Lemma D_dda2c : decode_any W_dda2c = Some (Load SZ8 true 10 10 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda30 : bv 32 := 0x00053503.
Lemma F_dda30 : fetch_word Plain.M.loaded_segments (0xdda78 : word) = Some W_dda30.
Proof. vm_refl. Qed.
Lemma D_dda30 : decode_any W_dda30 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda34 : bv 32 := 0x0005b603.
Lemma F_dda34 : fetch_word Plain.M.loaded_segments (0xdda7c : word) = Some W_dda34.
Proof. vm_refl. Qed.
Lemma D_dda34 : decode_any W_dda34 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda38 : bv 32 := 0xfff3e597.
Lemma F_dda38 : fetch_word Plain.M.loaded_segments (0xdda80 : word) = Some W_dda38.
Proof. vm_refl. Qed.
Lemma D_dda38 : decode_any W_dda38 = Some (Auipc 11 1048382, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda3c : bv 32 := 0x25a58593.
Lemma F_dda3c : fetch_word Plain.M.loaded_segments (0xdda84 : word) = Some W_dda3c.
Proof. vm_refl. Qed.
Lemma D_dda3c : decode_any W_dda3c = Some (OpImm ALU_ADD 11 11 602, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda40 : bv 32 := 0x00195097.
Lemma F_dda40 : fetch_word Plain.M.loaded_segments (0xdda88 : word) = Some W_dda40.
Proof. vm_refl. Qed.
Lemma D_dda40 : decode_any W_dda40 = Some (Auipc 1 405, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda44 : bv 32 := 0x54c080e7.
Lemma F_dda44 : fetch_word Plain.M.loaded_segments (0xdda8c : word) = Some W_dda44.
Proof. vm_refl. Qed.
Lemma D_dda44 : decode_any W_dda44 = Some (Jalr 1 1 1356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda48 : bv 32 := 0x0500006f.
Lemma F_dda48 : fetch_word Plain.M.loaded_segments (0xdda90 : word) = Some W_dda48.
Proof. vm_refl. Qed.
Lemma D_dda48 : decode_any W_dda48 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda4c : bv 32 := 0x001fd517.
Lemma F_dda4c : fetch_word Plain.M.loaded_segments (0xdda94 : word) = Some W_dda4c.
Proof. vm_refl. Qed.
Lemma D_dda4c : decode_any W_dda4c = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda50 : bv 32 := 0x0cc53503.
Lemma F_dda50 : fetch_word Plain.M.loaded_segments (0xdda98 : word) = Some W_dda50.
Proof. vm_refl. Qed.
Lemma D_dda50 : decode_any W_dda50 = Some (Load SZ8 true 10 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda54 : bv 32 := 0x00053683.
Lemma F_dda54 : fetch_word Plain.M.loaded_segments (0xdda9c : word) = Some W_dda54.
Proof. vm_refl. Qed.
Lemma D_dda54 : decode_any W_dda54 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda58 : bv 32 := 0xfff59517.
Lemma F_dda58 : fetch_word Plain.M.loaded_segments (0xddaa0 : word) = Some W_dda58.
Proof. vm_refl. Qed.
Lemma D_dda58 : decode_any W_dda58 = Some (Auipc 10 1048409, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda5c : bv 32 := 0x01f00593.
Lemma F_dda5c : fetch_word Plain.M.loaded_segments (0xddaa4 : word) = Some W_dda5c.
Proof. vm_refl. Qed.
Lemma D_dda5c : decode_any W_dda5c = Some (OpImm ALU_ADD 11 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda60 : bv 32 := 0xa4f50513.
Lemma F_dda60 : fetch_word Plain.M.loaded_segments (0xddaa8 : word) = Some W_dda60.
Proof. vm_refl. Qed.
Lemma D_dda60 : decode_any W_dda60 = Some (OpImm ALU_ADD 10 10 2639, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda64 : bv 32 := 0x01c0006f.
Lemma F_dda64 : fetch_word Plain.M.loaded_segments (0xddaac : word) = Some W_dda64.
Proof. vm_refl. Qed.
Lemma D_dda64 : decode_any W_dda64 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda68 : bv 32 := 0x001fd517.
Lemma F_dda68 : fetch_word Plain.M.loaded_segments (0xddab0 : word) = Some W_dda68.
Proof. vm_refl. Qed.
Lemma D_dda68 : decode_any W_dda68 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda6c : bv 32 := 0x0b053503.
Lemma F_dda6c : fetch_word Plain.M.loaded_segments (0xddab4 : word) = Some W_dda6c.
Proof. vm_refl. Qed.
Lemma D_dda6c : decode_any W_dda6c = Some (Load SZ8 true 10 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda70 : bv 32 := 0x00053683.
Lemma F_dda70 : fetch_word Plain.M.loaded_segments (0xddab8 : word) = Some W_dda70.
Proof. vm_refl. Qed.
Lemma D_dda70 : decode_any W_dda70 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda74 : bv 32 := 0xfff3e517.
Lemma F_dda74 : fetch_word Plain.M.loaded_segments (0xddabc : word) = Some W_dda74.
Proof. vm_refl. Qed.
Lemma D_dda74 : decode_any W_dda74 = Some (Auipc 10 1048382, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda78 : bv 32 := 0x01f00593.
Lemma F_dda78 : fetch_word Plain.M.loaded_segments (0xddac0 : word) = Some W_dda78.
Proof. vm_refl. Qed.
Lemma D_dda78 : decode_any W_dda78 = Some (OpImm ALU_ADD 11 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda7c : bv 32 := 0x22f50513.
Lemma F_dda7c : fetch_word Plain.M.loaded_segments (0xddac4 : word) = Some W_dda7c.
Proof. vm_refl. Qed.
Lemma D_dda7c : decode_any W_dda7c = Some (OpImm ALU_ADD 10 10 559, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda80 : bv 32 := 0x00100613.
Lemma F_dda80 : fetch_word Plain.M.loaded_segments (0xddac8 : word) = Some W_dda80.
Proof. vm_refl. Qed.
Lemma D_dda80 : decode_any W_dda80 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda84 : bv 32 := 0x00196097.
Lemma F_dda84 : fetch_word Plain.M.loaded_segments (0xddacc : word) = Some W_dda84.
Proof. vm_refl. Qed.
Lemma D_dda84 : decode_any W_dda84 = Some (Auipc 1 406, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda88 : bv 32 := 0xc94080e7.
Lemma F_dda88 : fetch_word Plain.M.loaded_segments (0xddad0 : word) = Some W_dda88.
Proof. vm_refl. Qed.
Lemma D_dda88 : decode_any W_dda88 = Some (Jalr 1 1 3220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda8c : bv 32 := 0x00048513.
Lemma F_dda8c : fetch_word Plain.M.loaded_segments (0xddad4 : word) = Some W_dda8c.
Proof. vm_refl. Qed.
Lemma D_dda8c : decode_any W_dda8c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda90 : bv 32 := 0x00192097.
Lemma F_dda90 : fetch_word Plain.M.loaded_segments (0xddad8 : word) = Some W_dda90.
Proof. vm_refl. Qed.
Lemma D_dda90 : decode_any W_dda90 = Some (Auipc 1 402, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda94 : bv 32 := 0x8d0080e7.
Lemma F_dda94 : fetch_word Plain.M.loaded_segments (0xddadc : word) = Some W_dda94.
Proof. vm_refl. Qed.
Lemma D_dda94 : decode_any W_dda94 = Some (Jalr 1 1 2256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda98 : bv 32 := 0x00040513.
Lemma F_dda98 : fetch_word Plain.M.loaded_segments (0xddae0 : word) = Some W_dda98.
Proof. vm_refl. Qed.
Lemma D_dda98 : decode_any W_dda98 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dda9c : bv 32 := 0x04813083.
Lemma F_dda9c : fetch_word Plain.M.loaded_segments (0xddae4 : word) = Some W_dda9c.
Proof. vm_refl. Qed.
Lemma D_dda9c : decode_any W_dda9c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddaa0 : bv 32 := 0x04013403.
Lemma F_ddaa0 : fetch_word Plain.M.loaded_segments (0xddae8 : word) = Some W_ddaa0.
Proof. vm_refl. Qed.
Lemma D_ddaa0 : decode_any W_ddaa0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddaa4 : bv 32 := 0x03813483.
Lemma F_ddaa4 : fetch_word Plain.M.loaded_segments (0xddaec : word) = Some W_ddaa4.
Proof. vm_refl. Qed.
Lemma D_ddaa4 : decode_any W_ddaa4 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddaa8 : bv 32 := 0x03013903.
Lemma F_ddaa8 : fetch_word Plain.M.loaded_segments (0xddaf0 : word) = Some W_ddaa8.
Proof. vm_refl. Qed.
Lemma D_ddaa8 : decode_any W_ddaa8 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddaac : bv 32 := 0x02813983.
Lemma F_ddaac : fetch_word Plain.M.loaded_segments (0xddaf4 : word) = Some W_ddaac.
Proof. vm_refl. Qed.
Lemma D_ddaac : decode_any W_ddaac = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddab0 : bv 32 := 0x02013a03.
Lemma F_ddab0 : fetch_word Plain.M.loaded_segments (0xddaf8 : word) = Some W_ddab0.
Proof. vm_refl. Qed.
Lemma D_ddab0 : decode_any W_ddab0 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddab4 : bv 32 := 0x01813a83.
Lemma F_ddab4 : fetch_word Plain.M.loaded_segments (0xddafc : word) = Some W_ddab4.
Proof. vm_refl. Qed.
Lemma D_ddab4 : decode_any W_ddab4 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddab8 : bv 32 := 0x01013b03.
Lemma F_ddab8 : fetch_word Plain.M.loaded_segments (0xddb00 : word) = Some W_ddab8.
Proof. vm_refl. Qed.
Lemma D_ddab8 : decode_any W_ddab8 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddabc : bv 32 := 0x00813b83.
Lemma F_ddabc : fetch_word Plain.M.loaded_segments (0xddb04 : word) = Some W_ddabc.
Proof. vm_refl. Qed.
Lemma D_ddabc : decode_any W_ddabc = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddac0 : bv 32 := 0x05010113.
Lemma F_ddac0 : fetch_word Plain.M.loaded_segments (0xddb08 : word) = Some W_ddac0.
Proof. vm_refl. Qed.
Lemma D_ddac0 : decode_any W_ddac0 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddac4 : bv 32 := 0x00008067.
Lemma F_ddac4 : fetch_word Plain.M.loaded_segments (0xddb0c : word) = Some W_ddac4.
Proof. vm_refl. Qed.
Lemma D_ddac4 : decode_any W_ddac4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddac8 : bv 32 := 0x001fd517.
Lemma F_ddac8 : fetch_word Plain.M.loaded_segments (0xddb10 : word) = Some W_ddac8.
Proof. vm_refl. Qed.
Lemma D_ddac8 : decode_any W_ddac8 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddacc : bv 32 := 0x05053503.
Lemma F_ddacc : fetch_word Plain.M.loaded_segments (0xddb14 : word) = Some W_ddacc.
Proof. vm_refl. Qed.
Lemma D_ddacc : decode_any W_ddacc = Some (Load SZ8 true 10 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddad0 : bv 32 := 0x00053503.
Lemma F_ddad0 : fetch_word Plain.M.loaded_segments (0xddb18 : word) = Some W_ddad0.
Proof. vm_refl. Qed.
Lemma D_ddad0 : decode_any W_ddad0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddad4 : bv 32 := 0xfff53597.
Lemma F_ddad4 : fetch_word Plain.M.loaded_segments (0xddb1c : word) = Some W_ddad4.
Proof. vm_refl. Qed.
Lemma D_ddad4 : decode_any W_ddad4 = Some (Auipc 11 1048403, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddad8 : bv 32 := 0x36358593.
Lemma F_ddad8 : fetch_word Plain.M.loaded_segments (0xddb20 : word) = Some W_ddad8.
Proof. vm_refl. Qed.
Lemma D_ddad8 : decode_any W_ddad8 = Some (OpImm ALU_ADD 11 11 867, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddadc : bv 32 := 0x00090613.
Lemma F_ddadc : fetch_word Plain.M.loaded_segments (0xddb24 : word) = Some W_ddadc.
Proof. vm_refl. Qed.
Lemma D_ddadc : decode_any W_ddadc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddae0 : bv 32 := 0x01c0006f.
Lemma F_ddae0 : fetch_word Plain.M.loaded_segments (0xddb28 : word) = Some W_ddae0.
Proof. vm_refl. Qed.
Lemma D_ddae0 : decode_any W_ddae0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddae4 : bv 32 := 0x001fd517.
Lemma F_ddae4 : fetch_word Plain.M.loaded_segments (0xddb2c : word) = Some W_ddae4.
Proof. vm_refl. Qed.
Lemma D_ddae4 : decode_any W_ddae4 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddae8 : bv 32 := 0x03453503.
Lemma F_ddae8 : fetch_word Plain.M.loaded_segments (0xddb30 : word) = Some W_ddae8.
Proof. vm_refl. Qed.
Lemma D_ddae8 : decode_any W_ddae8 = Some (Load SZ8 true 10 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddaec : bv 32 := 0x00053503.
Lemma F_ddaec : fetch_word Plain.M.loaded_segments (0xddb34 : word) = Some W_ddaec.
Proof. vm_refl. Qed.
Lemma D_ddaec : decode_any W_ddaec = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddaf0 : bv 32 := 0xfff49597.
Lemma F_ddaf0 : fetch_word Plain.M.loaded_segments (0xddb38 : word) = Some W_ddaf0.
Proof. vm_refl. Qed.
Lemma D_ddaf0 : decode_any W_ddaf0 = Some (Auipc 11 1048393, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddaf4 : bv 32 := 0x92f58593.
Lemma F_ddaf4 : fetch_word Plain.M.loaded_segments (0xddb3c : word) = Some W_ddaf4.
Proof. vm_refl. Qed.
Lemma D_ddaf4 : decode_any W_ddaf4 = Some (OpImm ALU_ADD 11 11 2351, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddaf8 : bv 32 := 0x04000637.
Lemma F_ddaf8 : fetch_word Plain.M.loaded_segments (0xddb40 : word) = Some W_ddaf8.
Proof. vm_refl. Qed.
Lemma D_ddaf8 : decode_any W_ddaf8 = Some (Lui 12 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddafc : bv 32 := 0x00195097.
Lemma F_ddafc : fetch_word Plain.M.loaded_segments (0xddb44 : word) = Some W_ddafc.
Proof. vm_refl. Qed.
Lemma D_ddafc : decode_any W_ddafc = Some (Auipc 1 405, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb00 : bv 32 := 0x490080e7.
Lemma F_ddb00 : fetch_word Plain.M.loaded_segments (0xddb48 : word) = Some W_ddb00.
Proof. vm_refl. Qed.
Lemma D_ddb00 : decode_any W_ddb00 = Some (Jalr 1 1 1168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb04 : bv 32 := 0x0280006f.
Lemma F_ddb04 : fetch_word Plain.M.loaded_segments (0xddb4c : word) = Some W_ddb04.
Proof. vm_refl. Qed.
Lemma D_ddb04 : decode_any W_ddb04 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb08 : bv 32 := 0x001fd517.
Lemma F_ddb08 : fetch_word Plain.M.loaded_segments (0xddb50 : word) = Some W_ddb08.
Proof. vm_refl. Qed.
Lemma D_ddb08 : decode_any W_ddb08 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb0c : bv 32 := 0x01053503.
Lemma F_ddb0c : fetch_word Plain.M.loaded_segments (0xddb54 : word) = Some W_ddb0c.
Proof. vm_refl. Qed.
Lemma D_ddb0c : decode_any W_ddb0c = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb10 : bv 32 := 0x00053683.
Lemma F_ddb10 : fetch_word Plain.M.loaded_segments (0xddb58 : word) = Some W_ddb10.
Proof. vm_refl. Qed.
Lemma D_ddb10 : decode_any W_ddb10 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb14 : bv 32 := 0xfff3c517.
Lemma F_ddb14 : fetch_word Plain.M.loaded_segments (0xddb5c : word) = Some W_ddb14.
Proof. vm_refl. Qed.
Lemma D_ddb14 : decode_any W_ddb14 = Some (Auipc 10 1048380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb18 : bv 32 := 0x01300593.
Lemma F_ddb18 : fetch_word Plain.M.loaded_segments (0xddb60 : word) = Some W_ddb18.
Proof. vm_refl. Qed.
Lemma D_ddb18 : decode_any W_ddb18 = Some (OpImm ALU_ADD 11 0 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb1c : bv 32 := 0xa1e50513.
Lemma F_ddb1c : fetch_word Plain.M.loaded_segments (0xddb64 : word) = Some W_ddb1c.
Proof. vm_refl. Qed.
Lemma D_ddb1c : decode_any W_ddb1c = Some (OpImm ALU_ADD 10 10 2590, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb20 : bv 32 := 0x00100613.
Lemma F_ddb20 : fetch_word Plain.M.loaded_segments (0xddb68 : word) = Some W_ddb20.
Proof. vm_refl. Qed.
Lemma D_ddb20 : decode_any W_ddb20 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb24 : bv 32 := 0x00196097.
Lemma F_ddb24 : fetch_word Plain.M.loaded_segments (0xddb6c : word) = Some W_ddb24.
Proof. vm_refl. Qed.
Lemma D_ddb24 : decode_any W_ddb24 = Some (Auipc 1 406, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb28 : bv 32 := 0xbf4080e7.
Lemma F_ddb28 : fetch_word Plain.M.loaded_segments (0xddb70 : word) = Some W_ddb28.
Proof. vm_refl. Qed.
Lemma D_ddb28 : decode_any W_ddb28 = Some (Jalr 1 1 3060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb2c : bv 32 := 0x00200513.
Lemma F_ddb2c : fetch_word Plain.M.loaded_segments (0xddb74 : word) = Some W_ddb2c.
Proof. vm_refl. Qed.
Lemma D_ddb2c : decode_any W_ddb2c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb30 : bv 32 := 0x00191097.
Lemma F_ddb30 : fetch_word Plain.M.loaded_segments (0xddb78 : word) = Some W_ddb30.
Proof. vm_refl. Qed.
Lemma D_ddb30 : decode_any W_ddb30 = Some (Auipc 1 401, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb34 : bv 32 := 0x50c080e7.
Lemma F_ddb34 : fetch_word Plain.M.loaded_segments (0xddb7c : word) = Some W_ddb34.
Proof. vm_refl. Qed.
Lemma D_ddb34 : decode_any W_ddb34 = Some (Jalr 1 1 1292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb38 : bv 32 := 0x001fd517.
Lemma F_ddb38 : fetch_word Plain.M.loaded_segments (0xddb80 : word) = Some W_ddb38.
Proof. vm_refl. Qed.
Lemma D_ddb38 : decode_any W_ddb38 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb3c : bv 32 := 0xfe053503.
Lemma F_ddb3c : fetch_word Plain.M.loaded_segments (0xddb84 : word) = Some W_ddb3c.
Proof. vm_refl. Qed.
Lemma D_ddb3c : decode_any W_ddb3c = Some (Load SZ8 true 10 10 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb40 : bv 32 := 0x00053503.
Lemma F_ddb40 : fetch_word Plain.M.loaded_segments (0xddb88 : word) = Some W_ddb40.
Proof. vm_refl. Qed.
Lemma D_ddb40 : decode_any W_ddb40 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb44 : bv 32 := 0xfff53597.
Lemma F_ddb44 : fetch_word Plain.M.loaded_segments (0xddb8c : word) = Some W_ddb44.
Proof. vm_refl. Qed.
Lemma D_ddb44 : decode_any W_ddb44 = Some (Auipc 11 1048403, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb48 : bv 32 := 0x2de58593.
Lemma F_ddb48 : fetch_word Plain.M.loaded_segments (0xddb90 : word) = Some W_ddb48.
Proof. vm_refl. Qed.
Lemma D_ddb48 : decode_any W_ddb48 = Some (OpImm ALU_ADD 11 11 734, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb4c : bv 32 := 0xf91ff06f.
Lemma F_ddb4c : fetch_word Plain.M.loaded_segments (0xddb94 : word) = Some W_ddb4c.
Proof. vm_refl. Qed.
Lemma D_ddb4c : decode_any W_ddb4c = Some (Jal 0 2097040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb50 : bv 32 := 0x001fd517.
Lemma F_ddb50 : fetch_word Plain.M.loaded_segments (0xddb98 : word) = Some W_ddb50.
Proof. vm_refl. Qed.
Lemma D_ddb50 : decode_any W_ddb50 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb54 : bv 32 := 0xfc853503.
Lemma F_ddb54 : fetch_word Plain.M.loaded_segments (0xddb9c : word) = Some W_ddb54.
Proof. vm_refl. Qed.
Lemma D_ddb54 : decode_any W_ddb54 = Some (Load SZ8 true 10 10 4040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb58 : bv 32 := 0x00053683.
Lemma F_ddb58 : fetch_word Plain.M.loaded_segments (0xddba0 : word) = Some W_ddb58.
Proof. vm_refl. Qed.
Lemma D_ddb58 : decode_any W_ddb58 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb5c : bv 32 := 0xfff3c517.
Lemma F_ddb5c : fetch_word Plain.M.loaded_segments (0xddba4 : word) = Some W_ddb5c.
Proof. vm_refl. Qed.
Lemma D_ddb5c : decode_any W_ddb5c = Some (Auipc 10 1048380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb60 : bv 32 := 0x01300593.
Lemma F_ddb60 : fetch_word Plain.M.loaded_segments (0xddba8 : word) = Some W_ddb60.
Proof. vm_refl. Qed.
Lemma D_ddb60 : decode_any W_ddb60 = Some (OpImm ALU_ADD 11 0 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb64 : bv 32 := 0x9d650513.
Lemma F_ddb64 : fetch_word Plain.M.loaded_segments (0xddbac : word) = Some W_ddb64.
Proof. vm_refl. Qed.
Lemma D_ddb64 : decode_any W_ddb64 = Some (OpImm ALU_ADD 10 10 2518, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb68 : bv 32 := 0xfb9ff06f.
Lemma F_ddb68 : fetch_word Plain.M.loaded_segments (0xddbb0 : word) = Some W_ddb68.
Proof. vm_refl. Qed.
Lemma D_ddb68 : decode_any W_ddb68 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb6c : bv 32 := 0x00008067.
Lemma F_ddb6c : fetch_word Plain.M.loaded_segments (0xddbb4 : word) = Some W_ddb6c.
Proof. vm_refl. Qed.
Lemma D_ddb6c : decode_any W_ddb6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb70 : bv 32 := 0x00000513.
Lemma F_ddb70 : fetch_word Plain.M.loaded_segments (0xddbb8 : word) = Some W_ddb70.
Proof. vm_refl. Qed.
Lemma D_ddb70 : decode_any W_ddb70 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb74 : bv 32 := 0x00008067.
Lemma F_ddb74 : fetch_word Plain.M.loaded_segments (0xddbbc : word) = Some W_ddb74.
Proof. vm_refl. Qed.
Lemma D_ddb74 : decode_any W_ddb74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb78 : bv 32 := 0xfb010113.
Lemma F_ddb78 : fetch_word Plain.M.loaded_segments (0xddbc0 : word) = Some W_ddb78.
Proof. vm_refl. Qed.
Lemma D_ddb78 : decode_any W_ddb78 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb7c : bv 32 := 0x04113423.
Lemma F_ddb7c : fetch_word Plain.M.loaded_segments (0xddbc4 : word) = Some W_ddb7c.
Proof. vm_refl. Qed.
Lemma D_ddb7c : decode_any W_ddb7c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb80 : bv 32 := 0x04813023.
Lemma F_ddb80 : fetch_word Plain.M.loaded_segments (0xddbc8 : word) = Some W_ddb80.
Proof. vm_refl. Qed.
Lemma D_ddb80 : decode_any W_ddb80 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb84 : bv 32 := 0x02913c23.
Lemma F_ddb84 : fetch_word Plain.M.loaded_segments (0xddbcc : word) = Some W_ddb84.
Proof. vm_refl. Qed.
Lemma D_ddb84 : decode_any W_ddb84 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb88 : bv 32 := 0x03213823.
Lemma F_ddb88 : fetch_word Plain.M.loaded_segments (0xddbd0 : word) = Some W_ddb88.
Proof. vm_refl. Qed.
Lemma D_ddb88 : decode_any W_ddb88 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb8c : bv 32 := 0x03313423.
Lemma F_ddb8c : fetch_word Plain.M.loaded_segments (0xddbd4 : word) = Some W_ddb8c.
Proof. vm_refl. Qed.
Lemma D_ddb8c : decode_any W_ddb8c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb90 : bv 32 := 0x03413023.
Lemma F_ddb90 : fetch_word Plain.M.loaded_segments (0xddbd8 : word) = Some W_ddb90.
Proof. vm_refl. Qed.
Lemma D_ddb90 : decode_any W_ddb90 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb94 : bv 32 := 0x01513c23.
Lemma F_ddb94 : fetch_word Plain.M.loaded_segments (0xddbdc : word) = Some W_ddb94.
Proof. vm_refl. Qed.
Lemma D_ddb94 : decode_any W_ddb94 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb98 : bv 32 := 0x01613823.
Lemma F_ddb98 : fetch_word Plain.M.loaded_segments (0xddbe0 : word) = Some W_ddb98.
Proof. vm_refl. Qed.
Lemma D_ddb98 : decode_any W_ddb98 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddb9c : bv 32 := 0x01713423.
Lemma F_ddb9c : fetch_word Plain.M.loaded_segments (0xddbe4 : word) = Some W_ddb9c.
Proof. vm_refl. Qed.
Lemma D_ddb9c : decode_any W_ddb9c = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddba0 : bv 32 := 0x00068413.
Lemma F_ddba0 : fetch_word Plain.M.loaded_segments (0xddbe8 : word) = Some W_ddba0.
Proof. vm_refl. Qed.
Lemma D_ddba0 : decode_any W_ddba0 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddba4 : bv 32 := 0x00060493.
Lemma F_ddba4 : fetch_word Plain.M.loaded_segments (0xddbec : word) = Some W_ddba4.
Proof. vm_refl. Qed.
Lemma D_ddba4 : decode_any W_ddba4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddba8 : bv 32 := 0x00058913.
Lemma F_ddba8 : fetch_word Plain.M.loaded_segments (0xddbf0 : word) = Some W_ddba8.
Proof. vm_refl. Qed.
Lemma D_ddba8 : decode_any W_ddba8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbac : bv 32 := 0x0020f597.
Lemma F_ddbac : fetch_word Plain.M.loaded_segments (0xddbf4 : word) = Some W_ddbac.
Proof. vm_refl. Qed.
Lemma D_ddbac : decode_any W_ddbac = Some (Auipc 11 527, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbb0 : bv 32 := 0xd0c58a13.
Lemma F_ddbb0 : fetch_word Plain.M.loaded_segments (0xddbf8 : word) = Some W_ddbb0.
Proof. vm_refl. Qed.
Lemma D_ddbb0 : decode_any W_ddbb0 = Some (OpImm ALU_ADD 20 11 3340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbb4 : bv 32 := 0x000a4583.
Lemma F_ddbb4 : fetch_word Plain.M.loaded_segments (0xddbfc : word) = Some W_ddbb4.
Proof. vm_refl. Qed.
Lemma D_ddbb4 : decode_any W_ddbb4 = Some (Load SZ1 false 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbb8 : bv 32 := 0x00050993.
Lemma F_ddbb8 : fetch_word Plain.M.loaded_segments (0xddc00 : word) = Some W_ddbb8.
Proof. vm_refl. Qed.
Lemma D_ddbb8 : decode_any W_ddbb8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbbc : bv 32 := 0x04058263.
Lemma F_ddbbc : fetch_word Plain.M.loaded_segments (0xddc04 : word) = Some W_ddbbc.
Proof. vm_refl. Qed.
Lemma D_ddbbc : decode_any W_ddbbc = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbc0 : bv 32 := 0x06090263.
Lemma F_ddbc0 : fetch_word Plain.M.loaded_segments (0xddc08 : word) = Some W_ddbc0.
Proof. vm_refl. Qed.
Lemma D_ddbc0 : decode_any W_ddbc0 = Some (Branch BC_EQ 18 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbc4 : bv 32 := 0x0009c503.
Lemma F_ddbc4 : fetch_word Plain.M.loaded_segments (0xddc0c : word) = Some W_ddbc4.
Proof. vm_refl. Qed.
Lemma D_ddbc4 : decode_any W_ddbc4 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbc8 : bv 32 := 0x00357513.
Lemma F_ddbc8 : fetch_word Plain.M.loaded_segments (0xddc10 : word) = Some W_ddbc8.
Proof. vm_refl. Qed.
Lemma D_ddbc8 : decode_any W_ddbc8 = Some (OpImm ALU_AND 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbcc : bv 32 := 0x00150a93.
Lemma F_ddbcc : fetch_word Plain.M.loaded_segments (0xddc14 : word) = Some W_ddbcc.
Proof. vm_refl. Qed.
Lemma D_ddbcc : decode_any W_ddbcc = Some (OpImm ALU_ADD 21 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbd0 : bv 32 := 0x04040e63.
Lemma F_ddbd0 : fetch_word Plain.M.loaded_segments (0xddc18 : word) = Some W_ddbd0.
Proof. vm_refl. Qed.
Lemma D_ddbd0 : decode_any W_ddbd0 = Some (Branch BC_EQ 8 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbd4 : bv 32 := 0x00040513.
Lemma F_ddbd4 : fetch_word Plain.M.loaded_segments (0xddc1c : word) = Some W_ddbd4.
Proof. vm_refl. Qed.
Lemma D_ddbd4 : decode_any W_ddbd4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbd8 : bv 32 := 0x00192097.
Lemma F_ddbd8 : fetch_word Plain.M.loaded_segments (0xddc20 : word) = Some W_ddbd8.
Proof. vm_refl. Qed.
Lemma D_ddbd8 : decode_any W_ddbd8 = Some (Auipc 1 402, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbdc : bv 32 := 0x8c8080e7.
Lemma F_ddbdc : fetch_word Plain.M.loaded_segments (0xddc24 : word) = Some W_ddbdc.
Proof. vm_refl. Qed.
Lemma D_ddbdc : decode_any W_ddbdc = Some (Jalr 1 1 2248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbe0 : bv 32 := 0x02050e63.
Lemma F_ddbe0 : fetch_word Plain.M.loaded_segments (0xddc28 : word) = Some W_ddbe0.
Proof. vm_refl. Qed.
Lemma D_ddbe0 : decode_any W_ddbe0 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbe4 : bv 32 := 0x00050913.
Lemma F_ddbe4 : fetch_word Plain.M.loaded_segments (0xddc2c : word) = Some W_ddbe4.
Proof. vm_refl. Qed.
Lemma D_ddbe4 : decode_any W_ddbe4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbe8 : bv 32 := 0x00048593.
Lemma F_ddbe8 : fetch_word Plain.M.loaded_segments (0xddc30 : word) = Some W_ddbe8.
Proof. vm_refl. Qed.
Lemma D_ddbe8 : decode_any W_ddbe8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbec : bv 32 := 0x00040613.
Lemma F_ddbec : fetch_word Plain.M.loaded_segments (0xddc34 : word) = Some W_ddbec.
Proof. vm_refl. Qed.
Lemma D_ddbec : decode_any W_ddbec = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbf0 : bv 32 := 0x0019c097.
Lemma F_ddbf0 : fetch_word Plain.M.loaded_segments (0xddc38 : word) = Some W_ddbf0.
Proof. vm_refl. Qed.
Lemma D_ddbf0 : decode_any W_ddbf0 = Some (Auipc 1 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbf4 : bv 32 := 0xc84080e7.
Lemma F_ddbf4 : fetch_word Plain.M.loaded_segments (0xddc3c : word) = Some W_ddbf4.
Proof. vm_refl. Qed.
Lemma D_ddbf4 : decode_any W_ddbf4 = Some (Jalr 1 1 3204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbf8 : bv 32 := 0x00090493.
Lemma F_ddbf8 : fetch_word Plain.M.loaded_segments (0xddc40 : word) = Some W_ddbf8.
Proof. vm_refl. Qed.
Lemma D_ddbf8 : decode_any W_ddbf8 = Some (OpImm ALU_ADD 9 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbfc : bv 32 := 0x0380006f.
Lemma F_ddbfc : fetch_word Plain.M.loaded_segments (0xddc44 : word) = Some W_ddbfc.
Proof. vm_refl. Qed.
Lemma D_ddbfc : decode_any W_ddbfc = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc00 : bv 32 := 0x00100513.
Lemma F_ddc00 : fetch_word Plain.M.loaded_segments (0xddc48 : word) = Some W_ddc00.
Proof. vm_refl. Qed.
Lemma D_ddc00 : decode_any W_ddc00 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc04 : bv 32 := 0x00aa0023.
Lemma F_ddc04 : fetch_word Plain.M.loaded_segments (0xddc4c : word) = Some W_ddc04.
Proof. vm_refl. Qed.
Lemma D_ddc04 : decode_any W_ddc04 = Some (Store SZ1 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc08 : bv 32 := 0x00000517.
Lemma F_ddc08 : fetch_word Plain.M.loaded_segments (0xddc50 : word) = Some W_ddc08.
Proof. vm_refl. Qed.
Lemma D_ddc08 : decode_any W_ddc08 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc0c : bv 32 := 0x0d850513.
Lemma F_ddc0c : fetch_word Plain.M.loaded_segments (0xddc54 : word) = Some W_ddc0c.
Proof. vm_refl. Qed.
Lemma D_ddc0c : decode_any W_ddc0c = Some (OpImm ALU_ADD 10 10 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc10 : bv 32 := 0x00191097.
Lemma F_ddc10 : fetch_word Plain.M.loaded_segments (0xddc58 : word) = Some W_ddc10.
Proof. vm_refl. Qed.
Lemma D_ddc10 : decode_any W_ddc10 = Some (Auipc 1 401, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc14 : bv 32 := 0x314080e7.
Lemma F_ddc14 : fetch_word Plain.M.loaded_segments (0xddc5c : word) = Some W_ddc14.
Proof. vm_refl. Qed.
Lemma D_ddc14 : decode_any W_ddc14 = Some (Jalr 1 1 788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc18 : bv 32 := 0x0a050063.
Lemma F_ddc18 : fetch_word Plain.M.loaded_segments (0xddc60 : word) = Some W_ddc18.
Proof. vm_refl. Qed.
Lemma D_ddc18 : decode_any W_ddc18 = Some (Branch BC_EQ 10 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc1c : bv 32 := 0x00200513.
Lemma F_ddc1c : fetch_word Plain.M.loaded_segments (0xddc64 : word) = Some W_ddc1c.
Proof. vm_refl. Qed.
Lemma D_ddc1c : decode_any W_ddc1c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc20 : bv 32 := 0x06c0006f.
Lemma F_ddc20 : fetch_word Plain.M.loaded_segments (0xddc68 : word) = Some W_ddc20.
Proof. vm_refl. Qed.
Lemma D_ddc20 : decode_any W_ddc20 = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc24 : bv 32 := 0x00100a93.
Lemma F_ddc24 : fetch_word Plain.M.loaded_segments (0xddc6c : word) = Some W_ddc24.
Proof. vm_refl. Qed.
Lemma D_ddc24 : decode_any W_ddc24 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc28 : bv 32 := 0xfa0416e3.
Lemma F_ddc28 : fetch_word Plain.M.loaded_segments (0xddc70 : word) = Some W_ddc28.
Proof. vm_refl. Qed.
Lemma D_ddc28 : decode_any W_ddc28 = Some (Branch BC_NE 8 0 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc2c : bv 32 := 0x00000913.
Lemma F_ddc2c : fetch_word Plain.M.loaded_segments (0xddc74 : word) = Some W_ddc2c.
Proof. vm_refl. Qed.
Lemma D_ddc2c : decode_any W_ddc2c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc30 : bv 32 := 0x010a0493.
Lemma F_ddc30 : fetch_word Plain.M.loaded_segments (0xddc78 : word) = Some W_ddc30.
Proof. vm_refl. Qed.
Lemma D_ddc30 : decode_any W_ddc30 = Some (OpImm ALU_ADD 9 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc34 : bv 32 := 0x00000b13.
Lemma F_ddc34 : fetch_word Plain.M.loaded_segments (0xddc7c : word) = Some W_ddc34.
Proof. vm_refl. Qed.
Lemma D_ddc34 : decode_any W_ddc34 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc38 : bv 32 := 0xffe00b93.
Lemma F_ddc38 : fetch_word Plain.M.loaded_segments (0xddc80 : word) = Some W_ddc38.
Proof. vm_refl. Qed.
Lemma D_ddc38 : decode_any W_ddc38 = Some (OpImm ALU_ADD 23 0 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc3c : bv 32 := 0x00100513.
Lemma F_ddc3c : fetch_word Plain.M.loaded_segments (0xddc84 : word) = Some W_ddc3c.
Proof. vm_refl. Qed.
Lemma D_ddc3c : decode_any W_ddc3c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc40 : bv 32 := 0x00aa0223.
Lemma F_ddc40 : fetch_word Plain.M.loaded_segments (0xddc88 : word) = Some W_ddc40.
Proof. vm_refl. Qed.
Lemma D_ddc40 : decode_any W_ddc40 = Some (Store SZ1 20 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc44 : bv 32 := 0x00048513.
Lemma F_ddc44 : fetch_word Plain.M.loaded_segments (0xddc8c : word) = Some W_ddc44.
Proof. vm_refl. Qed.
Lemma D_ddc44 : decode_any W_ddc44 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc48 : bv 32 := 0x00040593.
Lemma F_ddc48 : fetch_word Plain.M.loaded_segments (0xddc90 : word) = Some W_ddc48.
Proof. vm_refl. Qed.
Lemma D_ddc48 : decode_any W_ddc48 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc4c : bv 32 := 0x11c000ef.
Lemma F_ddc4c : fetch_word Plain.M.loaded_segments (0xddc94 : word) = Some W_ddc4c.
Proof. vm_refl. Qed.
Lemma D_ddc4c : decode_any W_ddc4c = Some (Jal 1 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc50 : bv 32 := 0x00050993.
Lemma F_ddc50 : fetch_word Plain.M.loaded_segments (0xddc98 : word) = Some W_ddc50.
Proof. vm_refl. Qed.
Lemma D_ddc50 : decode_any W_ddc50 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc54 : bv 32 := 0x000a0223.
Lemma F_ddc54 : fetch_word Plain.M.loaded_segments (0xddc9c : word) = Some W_ddc54.
Proof. vm_refl. Qed.
Lemma D_ddc54 : decode_any W_ddc54 = Some (Store SZ1 20 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc58 : bv 32 := 0x00050593.
Lemma F_ddc58 : fetch_word Plain.M.loaded_segments (0xddca0 : word) = Some W_ddc58.
Proof. vm_refl. Qed.
Lemma D_ddc58 : decode_any W_ddc58 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc5c : bv 32 := 0x0bc000ef.
Lemma F_ddc5c : fetch_word Plain.M.loaded_segments (0xddca4 : word) = Some W_ddc5c.
Proof. vm_refl. Qed.
Lemma D_ddc5c : decode_any W_ddc5c = Some (Jal 1 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc60 : bv 32 := 0xfff9899b.
Lemma F_ddc60 : fetch_word Plain.M.loaded_segments (0xddca8 : word) = Some W_ddc60.
Proof. vm_refl. Qed.
Lemma D_ddc60 : decode_any W_ddc60 = Some (OpImm32 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc64 : bv 32 := 0x0179f463.
Lemma F_ddc64 : fetch_word Plain.M.loaded_segments (0xddcac : word) = Some W_ddc64.
Proof. vm_refl. Qed.
Lemma D_ddc64 : decode_any W_ddc64 = Some (Branch BC_GEU 19 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc68 : bv 32 := 0x00100b13.
Lemma F_ddc68 : fetch_word Plain.M.loaded_segments (0xddcb0 : word) = Some W_ddc68.
Proof. vm_refl. Qed.
Lemma D_ddc68 : decode_any W_ddc68 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc6c : bv 32 := 0xfffa8a9b.
Lemma F_ddc6c : fetch_word Plain.M.loaded_segments (0xddcb4 : word) = Some W_ddc6c.
Proof. vm_refl. Qed.
Lemma D_ddc6c : decode_any W_ddc6c = Some (OpImm32 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc70 : bv 32 := 0xfc0a96e3.
Lemma F_ddc70 : fetch_word Plain.M.loaded_segments (0xddcb8 : word) = Some W_ddc70.
Proof. vm_refl. Qed.
Lemma D_ddc70 : decode_any W_ddc70 = Some (Branch BC_NE 21 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc74 : bv 32 := 0x00090513.
Lemma F_ddc74 : fetch_word Plain.M.loaded_segments (0xddcbc : word) = Some W_ddc74.
Proof. vm_refl. Qed.
Lemma D_ddc74 : decode_any W_ddc74 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc78 : bv 32 := 0x00191097.
Lemma F_ddc78 : fetch_word Plain.M.loaded_segments (0xddcc0 : word) = Some W_ddc78.
Proof. vm_refl. Qed.
Lemma D_ddc78 : decode_any W_ddc78 = Some (Auipc 1 401, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc7c : bv 32 := 0x6e8080e7.
Lemma F_ddc7c : fetch_word Plain.M.loaded_segments (0xddcc4 : word) = Some W_ddc7c.
Proof. vm_refl. Qed.
Lemma D_ddc7c : decode_any W_ddc7c = Some (Jalr 1 1 1768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc80 : bv 32 := 0x001b3513.
Lemma F_ddc80 : fetch_word Plain.M.loaded_segments (0xddcc8 : word) = Some W_ddc80.
Proof. vm_refl. Qed.
Lemma D_ddc80 : decode_any W_ddc80 = Some (OpImm ALU_SLTU 10 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc84 : bv 32 := 0xfff50513.
Lemma F_ddc84 : fetch_word Plain.M.loaded_segments (0xddccc : word) = Some W_ddc84.
Proof. vm_refl. Qed.
Lemma D_ddc84 : decode_any W_ddc84 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc88 : bv 32 := 0x04e57513.
Lemma F_ddc88 : fetch_word Plain.M.loaded_segments (0xddcd0 : word) = Some W_ddc88.
Proof. vm_refl. Qed.
Lemma D_ddc88 : decode_any W_ddc88 = Some (OpImm ALU_AND 10 10 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc8c : bv 32 := 0x04813083.
Lemma F_ddc8c : fetch_word Plain.M.loaded_segments (0xddcd4 : word) = Some W_ddc8c.
Proof. vm_refl. Qed.
Lemma D_ddc8c : decode_any W_ddc8c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc90 : bv 32 := 0x04013403.
Lemma F_ddc90 : fetch_word Plain.M.loaded_segments (0xddcd8 : word) = Some W_ddc90.
Proof. vm_refl. Qed.
Lemma D_ddc90 : decode_any W_ddc90 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc94 : bv 32 := 0x03813483.
Lemma F_ddc94 : fetch_word Plain.M.loaded_segments (0xddcdc : word) = Some W_ddc94.
Proof. vm_refl. Qed.
Lemma D_ddc94 : decode_any W_ddc94 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc98 : bv 32 := 0x03013903.
Lemma F_ddc98 : fetch_word Plain.M.loaded_segments (0xddce0 : word) = Some W_ddc98.
Proof. vm_refl. Qed.
Lemma D_ddc98 : decode_any W_ddc98 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddc9c : bv 32 := 0x02813983.
Lemma F_ddc9c : fetch_word Plain.M.loaded_segments (0xddce4 : word) = Some W_ddc9c.
Proof. vm_refl. Qed.
Lemma D_ddc9c : decode_any W_ddc9c = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddca0 : bv 32 := 0x02013a03.
Lemma F_ddca0 : fetch_word Plain.M.loaded_segments (0xddce8 : word) = Some W_ddca0.
Proof. vm_refl. Qed.
Lemma D_ddca0 : decode_any W_ddca0 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddca4 : bv 32 := 0x01813a83.
Lemma F_ddca4 : fetch_word Plain.M.loaded_segments (0xddcec : word) = Some W_ddca4.
Proof. vm_refl. Qed.
Lemma D_ddca4 : decode_any W_ddca4 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddca8 : bv 32 := 0x01013b03.
Lemma F_ddca8 : fetch_word Plain.M.loaded_segments (0xddcf0 : word) = Some W_ddca8.
Proof. vm_refl. Qed.
Lemma D_ddca8 : decode_any W_ddca8 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcac : bv 32 := 0x00813b83.
Lemma F_ddcac : fetch_word Plain.M.loaded_segments (0xddcf4 : word) = Some W_ddcac.
Proof. vm_refl. Qed.
Lemma D_ddcac : decode_any W_ddcac = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcb0 : bv 32 := 0x05010113.
Lemma F_ddcb0 : fetch_word Plain.M.loaded_segments (0xddcf8 : word) = Some W_ddcb0.
Proof. vm_refl. Qed.
Lemma D_ddcb0 : decode_any W_ddcb0 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcb4 : bv 32 := 0x00008067.
Lemma F_ddcb4 : fetch_word Plain.M.loaded_segments (0xddcfc : word) = Some W_ddcb4.
Proof. vm_refl. Qed.
Lemma D_ddcb4 : decode_any W_ddcb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcb8 : bv 32 := 0x001fd517.
Lemma F_ddcb8 : fetch_word Plain.M.loaded_segments (0xddd00 : word) = Some W_ddcb8.
Proof. vm_refl. Qed.
Lemma D_ddcb8 : decode_any W_ddcb8 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcbc : bv 32 := 0xe6853503.
Lemma F_ddcbc : fetch_word Plain.M.loaded_segments (0xddd04 : word) = Some W_ddcbc.
Proof. vm_refl. Qed.
Lemma D_ddcbc : decode_any W_ddcbc = Some (Load SZ8 true 10 10 3688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcc0 : bv 32 := 0xf00500e3.
Lemma F_ddcc0 : fetch_word Plain.M.loaded_segments (0xddd08 : word) = Some W_ddcc0.
Proof. vm_refl. Qed.
Lemma D_ddcc0 : decode_any W_ddcc0 = Some (Branch BC_EQ 10 0 7936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcc4 : bv 32 := 0x001fe517.
Lemma F_ddcc4 : fetch_word Plain.M.loaded_segments (0xddd0c : word) = Some W_ddcc4.
Proof. vm_refl. Qed.
Lemma D_ddcc4 : decode_any W_ddcc4 = Some (Auipc 10 510, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcc8 : bv 32 := 0x46450513.
Lemma F_ddcc8 : fetch_word Plain.M.loaded_segments (0xddd10 : word) = Some W_ddcc8.
Proof. vm_refl. Qed.
Lemma D_ddcc8 : decode_any W_ddcc8 = Some (OpImm ALU_ADD 10 10 1124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddccc : bv 32 := 0x00850593.
Lemma F_ddccc : fetch_word Plain.M.loaded_segments (0xddd14 : word) = Some W_ddccc.
Proof. vm_refl. Qed.
Lemma D_ddccc : decode_any W_ddccc = Some (OpImm ALU_ADD 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcd0 : bv 32 := 0x00b13023.
Lemma F_ddcd0 : fetch_word Plain.M.loaded_segments (0xddd18 : word) = Some W_ddcd0.
Proof. vm_refl. Qed.
Lemma D_ddcd0 : decode_any W_ddcd0 = Some (Store SZ8 2 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcd4 : bv 32 := 0x00010593.
Lemma F_ddcd4 : fetch_word Plain.M.loaded_segments (0xddd1c : word) = Some W_ddcd4.
Proof. vm_refl. Qed.
Lemma D_ddcd4 : decode_any W_ddcd4 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcd8 : bv 32 := 0x08c000ef.
Lemma F_ddcd8 : fetch_word Plain.M.loaded_segments (0xddd20 : word) = Some W_ddcd8.
Proof. vm_refl. Qed.
Lemma D_ddcd8 : decode_any W_ddcd8 = Some (Jal 1 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcdc : bv 32 := 0xee5ff06f.
Lemma F_ddcdc : fetch_word Plain.M.loaded_segments (0xddd24 : word) = Some W_ddcdc.
Proof. vm_refl. Qed.
Lemma D_ddcdc : decode_any W_ddcdc = Some (Jal 0 2096868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddce0 : bv 32 := 0x0020f517.
Lemma F_ddce0 : fetch_word Plain.M.loaded_segments (0xddd28 : word) = Some W_ddce0.
Proof. vm_refl. Qed.
Lemma D_ddce0 : decode_any W_ddce0 = Some (Auipc 10 527, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddce4 : bv 32 := 0xbdc54503.
Lemma F_ddce4 : fetch_word Plain.M.loaded_segments (0xddd2c : word) = Some W_ddce4.
Proof. vm_refl. Qed.
Lemma D_ddce4 : decode_any W_ddce4 = Some (Load SZ1 false 10 10 3036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddce8 : bv 32 := 0x00051463.
Lemma F_ddce8 : fetch_word Plain.M.loaded_segments (0xddd30 : word) = Some W_ddce8.
Proof. vm_refl. Qed.
Lemma D_ddce8 : decode_any W_ddce8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcec : bv 32 := 0x00008067.
Lemma F_ddcec : fetch_word Plain.M.loaded_segments (0xddd34 : word) = Some W_ddcec.
Proof. vm_refl. Qed.
Lemma D_ddcec : decode_any W_ddcec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcf0 : bv 32 := 0xff010113.
Lemma F_ddcf0 : fetch_word Plain.M.loaded_segments (0xddd38 : word) = Some W_ddcf0.
Proof. vm_refl. Qed.
Lemma D_ddcf0 : decode_any W_ddcf0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcf4 : bv 32 := 0x00113423.
Lemma F_ddcf4 : fetch_word Plain.M.loaded_segments (0xddd3c : word) = Some W_ddcf4.
Proof. vm_refl. Qed.
Lemma D_ddcf4 : decode_any W_ddcf4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcf8 : bv 32 := 0x001fd517.
Lemma F_ddcf8 : fetch_word Plain.M.loaded_segments (0xddd40 : word) = Some W_ddcf8.
Proof. vm_refl. Qed.
Lemma D_ddcf8 : decode_any W_ddcf8 = Some (Auipc 10 509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddcfc : bv 32 := 0xe3053503.
Lemma F_ddcfc : fetch_word Plain.M.loaded_segments (0xddd44 : word) = Some W_ddcfc.
Proof. vm_refl. Qed.
Lemma D_ddcfc : decode_any W_ddcfc = Some (Load SZ8 true 10 10 3632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd00 : bv 32 := 0x00053503.
Lemma F_ddd00 : fetch_word Plain.M.loaded_segments (0xddd48 : word) = Some W_ddd00.
Proof. vm_refl. Qed.
Lemma D_ddd00 : decode_any W_ddd00 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd04 : bv 32 := 0x00194097.
Lemma F_ddd04 : fetch_word Plain.M.loaded_segments (0xddd4c : word) = Some W_ddd04.
Proof. vm_refl. Qed.
Lemma D_ddd04 : decode_any W_ddd04 = Some (Auipc 1 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd08 : bv 32 := 0x734080e7.
Lemma F_ddd08 : fetch_word Plain.M.loaded_segments (0xddd50 : word) = Some W_ddd08.
Proof. vm_refl. Qed.
Lemma D_ddd08 : decode_any W_ddd08 = Some (Jalr 1 1 1844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd0c : bv 32 := 0x04d00513.
Lemma F_ddd0c : fetch_word Plain.M.loaded_segments (0xddd54 : word) = Some W_ddd0c.
Proof. vm_refl. Qed.
Lemma D_ddd0c : decode_any W_ddd0c = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd10 : bv 32 := 0x001a0097.
Lemma F_ddd10 : fetch_word Plain.M.loaded_segments (0xddd58 : word) = Some W_ddd10.
Proof. vm_refl. Qed.
Lemma D_ddd10 : decode_any W_ddd10 = Some (Auipc 1 416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd14 : bv 32 := 0x188080e7.
Lemma F_ddd14 : fetch_word Plain.M.loaded_segments (0xddd5c : word) = Some W_ddd14.
Proof. vm_refl. Qed.
Lemma D_ddd14 : decode_any W_ddd14 = Some (Jalr 1 1 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd18 : bv 32 := 0xfb010113.
Lemma F_ddd18 : fetch_word Plain.M.loaded_segments (0xddd60 : word) = Some W_ddd18.
Proof. vm_refl. Qed.
Lemma D_ddd18 : decode_any W_ddd18 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd1c : bv 32 := 0x00113423.
Lemma F_ddd1c : fetch_word Plain.M.loaded_segments (0xddd64 : word) = Some W_ddd1c.
Proof. vm_refl. Qed.
Lemma D_ddd1c : decode_any W_ddd1c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd20 : bv 32 := 0x02f13c23.
Lemma F_ddd20 : fetch_word Plain.M.loaded_segments (0xddd68 : word) = Some W_ddd20.
Proof. vm_refl. Qed.
Lemma D_ddd20 : decode_any W_ddd20 = Some (Store SZ8 2 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd24 : bv 32 := 0x05013023.
Lemma F_ddd24 : fetch_word Plain.M.loaded_segments (0xddd6c : word) = Some W_ddd24.
Proof. vm_refl. Qed.
Lemma D_ddd24 : decode_any W_ddd24 = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd28 : bv 32 := 0x05113423.
Lemma F_ddd28 : fetch_word Plain.M.loaded_segments (0xddd70 : word) = Some W_ddd28.
Proof. vm_refl. Qed.
Lemma D_ddd28 : decode_any W_ddd28 = Some (Store SZ8 2 17 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd2c : bv 32 := 0x00b13c23.
Lemma F_ddd2c : fetch_word Plain.M.loaded_segments (0xddd74 : word) = Some W_ddd2c.
Proof. vm_refl. Qed.
Lemma D_ddd2c : decode_any W_ddd2c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd30 : bv 32 := 0x02c13023.
Lemma F_ddd30 : fetch_word Plain.M.loaded_segments (0xddd78 : word) = Some W_ddd30.
Proof. vm_refl. Qed.
Lemma D_ddd30 : decode_any W_ddd30 = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd34 : bv 32 := 0x02d13423.
Lemma F_ddd34 : fetch_word Plain.M.loaded_segments (0xddd7c : word) = Some W_ddd34.
Proof. vm_refl. Qed.
Lemma D_ddd34 : decode_any W_ddd34 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd38 : bv 32 := 0x02e13823.
Lemma F_ddd38 : fetch_word Plain.M.loaded_segments (0xddd80 : word) = Some W_ddd38.
Proof. vm_refl. Qed.
Lemma D_ddd38 : decode_any W_ddd38 = Some (Store SZ8 2 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd3c : bv 32 := 0x01810513.
Lemma F_ddd3c : fetch_word Plain.M.loaded_segments (0xddd84 : word) = Some W_ddd3c.
Proof. vm_refl. Qed.
Lemma D_ddd3c : decode_any W_ddd3c = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd40 : bv 32 := 0x00a13023.
Lemma F_ddd40 : fetch_word Plain.M.loaded_segments (0xddd88 : word) = Some W_ddd40.
Proof. vm_refl. Qed.
Lemma D_ddd40 : decode_any W_ddd40 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd44 : bv 32 := 0xfff3c517.
Lemma F_ddd44 : fetch_word Plain.M.loaded_segments (0xddd8c : word) = Some W_ddd44.
Proof. vm_refl. Qed.
Lemma D_ddd44 : decode_any W_ddd44 = Some (Auipc 10 1048380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd48 : bv 32 := 0x80250513.
Lemma F_ddd48 : fetch_word Plain.M.loaded_segments (0xddd90 : word) = Some W_ddd48.
Proof. vm_refl. Qed.
Lemma D_ddd48 : decode_any W_ddd48 = Some (OpImm ALU_ADD 10 10 2050, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd4c : bv 32 := 0x01810593.
Lemma F_ddd4c : fetch_word Plain.M.loaded_segments (0xddd94 : word) = Some W_ddd4c.
Proof. vm_refl. Qed.
Lemma D_ddd4c : decode_any W_ddd4c = Some (OpImm ALU_ADD 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd50 : bv 32 := 0x0019a097.
Lemma F_ddd50 : fetch_word Plain.M.loaded_segments (0xddd98 : word) = Some W_ddd50.
Proof. vm_refl. Qed.
Lemma D_ddd50 : decode_any W_ddd50 = Some (Auipc 1 410, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd54 : bv 32 := 0x598080e7.
Lemma F_ddd54 : fetch_word Plain.M.loaded_segments (0xddd9c : word) = Some W_ddd54.
Proof. vm_refl. Qed.
Lemma D_ddd54 : decode_any W_ddd54 = Some (Jalr 1 1 1432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd58 : bv 32 := 0x00813083.
Lemma F_ddd58 : fetch_word Plain.M.loaded_segments (0xddda0 : word) = Some W_ddd58.
Proof. vm_refl. Qed.
Lemma D_ddd58 : decode_any W_ddd58 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd5c : bv 32 := 0x05010113.
Lemma F_ddd5c : fetch_word Plain.M.loaded_segments (0xddda4 : word) = Some W_ddd5c.
Proof. vm_refl. Qed.
Lemma D_ddd5c : decode_any W_ddd5c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd60 : bv 32 := 0x00008067.
Lemma F_ddd60 : fetch_word Plain.M.loaded_segments (0xddda8 : word) = Some W_ddd60.
Proof. vm_refl. Qed.
Lemma D_ddd60 : decode_any W_ddd60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd64 : bv 32 := 0x0080006f.
Lemma F_ddd64 : fetch_word Plain.M.loaded_segments (0xdddac : word) = Some W_ddd64.
Proof. vm_refl. Qed.
Lemma D_ddd64 : decode_any W_ddd64 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd68 : bv 32 := 0x00c0006f.
Lemma F_ddd68 : fetch_word Plain.M.loaded_segments (0xdddb0 : word) = Some W_ddd68.
Proof. vm_refl. Qed.
Lemma D_ddd68 : decode_any W_ddd68 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd6c : bv 32 := 0x00100513.
Lemma F_ddd6c : fetch_word Plain.M.loaded_segments (0xdddb4 : word) = Some W_ddd6c.
Proof. vm_refl. Qed.
Lemma D_ddd6c : decode_any W_ddd6c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddd70 : bv 32 := 0x00008067.
Lemma F_ddd70 : fetch_word Plain.M.loaded_segments (0xdddb8 : word) = Some W_ddd70.
Proof. vm_refl. Qed.
Lemma D_ddd70 : decode_any W_ddd70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
