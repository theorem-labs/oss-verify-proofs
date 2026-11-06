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
Definition W_ea6c8 : bv 32 := 0xfe010113.
Lemma F_ea6c8 : fetch_word Plain.M.loaded_segments (0xea710 : word) = Some W_ea6c8.
Proof. vm_refl. Qed.
Lemma D_ea6c8 : decode_any W_ea6c8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6cc : bv 32 := 0x00113c23.
Lemma F_ea6cc : fetch_word Plain.M.loaded_segments (0xea714 : word) = Some W_ea6cc.
Proof. vm_refl. Qed.
Lemma D_ea6cc : decode_any W_ea6cc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6d0 : bv 32 := 0x00813823.
Lemma F_ea6d0 : fetch_word Plain.M.loaded_segments (0xea718 : word) = Some W_ea6d0.
Proof. vm_refl. Qed.
Lemma D_ea6d0 : decode_any W_ea6d0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6d4 : bv 32 := 0x00913423.
Lemma F_ea6d4 : fetch_word Plain.M.loaded_segments (0xea71c : word) = Some W_ea6d4.
Proof. vm_refl. Qed.
Lemma D_ea6d4 : decode_any W_ea6d4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6d8 : bv 32 := 0x02010413.
Lemma F_ea6d8 : fetch_word Plain.M.loaded_segments (0xea720 : word) = Some W_ea6d8.
Proof. vm_refl. Qed.
Lemma D_ea6d8 : decode_any W_ea6d8 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6dc : bv 32 := 0x00202517.
Lemma F_ea6dc : fetch_word Plain.M.loaded_segments (0xea724 : word) = Some W_ea6dc.
Proof. vm_refl. Qed.
Lemma D_ea6dc : decode_any W_ea6dc = Some (Auipc 10 514, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6e0 : bv 32 := 0x41450493.
Lemma F_ea6e0 : fetch_word Plain.M.loaded_segments (0xea728 : word) = Some W_ea6e0.
Proof. vm_refl. Qed.
Lemma D_ea6e0 : decode_any W_ea6e0 = Some (OpImm ALU_ADD 9 10 1044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6e4 : bv 32 := 0x0004c503.
Lemma F_ea6e4 : fetch_word Plain.M.loaded_segments (0xea72c : word) = Some W_ea6e4.
Proof. vm_refl. Qed.
Lemma D_ea6e4 : decode_any W_ea6e4 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6e8 : bv 32 := 0x0a050063.
Lemma F_ea6e8 : fetch_word Plain.M.loaded_segments (0xea730 : word) = Some W_ea6e8.
Proof. vm_refl. Qed.
Lemma D_ea6e8 : decode_any W_ea6e8 = Some (Branch BC_EQ 10 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6ec : bv 32 := 0x0044c503.
Lemma F_ea6ec : fetch_word Plain.M.loaded_segments (0xea734 : word) = Some W_ea6ec.
Proof. vm_refl. Qed.
Lemma D_ea6ec : decode_any W_ea6ec = Some (Load SZ1 false 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6f0 : bv 32 := 0x00157513.
Lemma F_ea6f0 : fetch_word Plain.M.loaded_segments (0xea738 : word) = Some W_ea6f0.
Proof. vm_refl. Qed.
Lemma D_ea6f0 : decode_any W_ea6f0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6f4 : bv 32 := 0x08050a63.
Lemma F_ea6f4 : fetch_word Plain.M.loaded_segments (0xea73c : word) = Some W_ea6f4.
Proof. vm_refl. Qed.
Lemma D_ea6f4 : decode_any W_ea6f4 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6f8 : bv 32 := 0x0084c503.
Lemma F_ea6f8 : fetch_word Plain.M.loaded_segments (0xea740 : word) = Some W_ea6f8.
Proof. vm_refl. Qed.
Lemma D_ea6f8 : decode_any W_ea6f8 = Some (Load SZ1 false 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea6fc : bv 32 := 0x00157513.
Lemma F_ea6fc : fetch_word Plain.M.loaded_segments (0xea744 : word) = Some W_ea6fc.
Proof. vm_refl. Qed.
Lemma D_ea6fc : decode_any W_ea6fc = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea700 : bv 32 := 0x08051463.
Lemma F_ea700 : fetch_word Plain.M.loaded_segments (0xea748 : word) = Some W_ea700.
Proof. vm_refl. Qed.
Lemma D_ea700 : decode_any W_ea700 = Some (Branch BC_NE 10 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea704 : bv 32 := 0x00100513.
Lemma F_ea704 : fetch_word Plain.M.loaded_segments (0xea74c : word) = Some W_ea704.
Proof. vm_refl. Qed.
Lemma D_ea704 : decode_any W_ea704 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea708 : bv 32 := 0x00a48423.
Lemma F_ea708 : fetch_word Plain.M.loaded_segments (0xea750 : word) = Some W_ea708.
Proof. vm_refl. Qed.
Lemma D_ea708 : decode_any W_ea708 = Some (Store SZ1 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea70c : bv 32 := 0x82cf80ef.
Lemma F_ea70c : fetch_word Plain.M.loaded_segments (0xea754 : word) = Some W_ea70c.
Proof. vm_refl. Qed.
Lemma D_ea70c : decode_any W_ea70c = Some (Jal 1 2064428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea710 : bv 32 := 0x0504b503.
Lemma F_ea710 : fetch_word Plain.M.loaded_segments (0xea758 : word) = Some W_ea710.
Proof. vm_refl. Qed.
Lemma D_ea710 : decode_any W_ea710 = Some (Load SZ8 true 10 9 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea714 : bv 32 := 0xab1f60ef.
Lemma F_ea714 : fetch_word Plain.M.loaded_segments (0xea75c : word) = Some W_ea714.
Proof. vm_refl. Qed.
Lemma D_ea714 : decode_any W_ea714 = Some (Jal 1 2058928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea718 : bv 32 := 0x0584b503.
Lemma F_ea718 : fetch_word Plain.M.loaded_segments (0xea760 : word) = Some W_ea718.
Proof. vm_refl. Qed.
Lemma D_ea718 : decode_any W_ea718 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea71c : bv 32 := 0x0404b823.
Lemma F_ea71c : fetch_word Plain.M.loaded_segments (0xea764 : word) = Some W_ea71c.
Proof. vm_refl. Qed.
Lemma D_ea71c : decode_any W_ea71c = Some (Store SZ8 9 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea720 : bv 32 := 0xaa5f60ef.
Lemma F_ea720 : fetch_word Plain.M.loaded_segments (0xea768 : word) = Some W_ea720.
Proof. vm_refl. Qed.
Lemma D_ea720 : decode_any W_ea720 = Some (Jal 1 2058916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea724 : bv 32 := 0x0404bc23.
Lemma F_ea724 : fetch_word Plain.M.loaded_segments (0xea76c : word) = Some W_ea724.
Proof. vm_refl. Qed.
Lemma D_ea724 : decode_any W_ea724 = Some (Store SZ8 9 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea728 : bv 32 := 0x01c48513.
Lemma F_ea728 : fetch_word Plain.M.loaded_segments (0xea770 : word) = Some W_ea728.
Proof. vm_refl. Qed.
Lemma D_ea728 : decode_any W_ea728 = Some (OpImm ALU_ADD 10 9 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea72c : bv 32 := 0xb95f60ef.
Lemma F_ea72c : fetch_word Plain.M.loaded_segments (0xea774 : word) = Some W_ea72c.
Proof. vm_refl. Qed.
Lemma D_ea72c : decode_any W_ea72c = Some (Jal 1 2059156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea730 : bv 32 := 0x734000ef.
Lemma F_ea730 : fetch_word Plain.M.loaded_segments (0xea778 : word) = Some W_ea730.
Proof. vm_refl. Qed.
Lemma D_ea730 : decode_any W_ea730 = Some (Jal 1 1844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea734 : bv 32 := 0x750000ef.
Lemma F_ea734 : fetch_word Plain.M.loaded_segments (0xea77c : word) = Some W_ea734.
Proof. vm_refl. Qed.
Lemma D_ea734 : decode_any W_ea734 = Some (Jal 1 1872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea738 : bv 32 := 0x76c000ef.
Lemma F_ea738 : fetch_word Plain.M.loaded_segments (0xea780 : word) = Some W_ea738.
Proof. vm_refl. Qed.
Lemma D_ea738 : decode_any W_ea738 = Some (Jal 1 1900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea73c : bv 32 := 0x00c4c503.
Lemma F_ea73c : fetch_word Plain.M.loaded_segments (0xea784 : word) = Some W_ea73c.
Proof. vm_refl. Qed.
Lemma D_ea73c : decode_any W_ea73c = Some (Load SZ1 false 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea740 : bv 32 := 0x00050463.
Lemma F_ea740 : fetch_word Plain.M.loaded_segments (0xea788 : word) = Some W_ea740.
Proof. vm_refl. Qed.
Lemma D_ea740 : decode_any W_ea740 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea744 : bv 32 := 0x7a4000ef.
Lemma F_ea744 : fetch_word Plain.M.loaded_segments (0xea78c : word) = Some W_ea744.
Proof. vm_refl. Qed.
Lemma D_ea744 : decode_any W_ea744 = Some (Jal 1 1956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea748 : bv 32 := 0x7c0000ef.
Lemma F_ea748 : fetch_word Plain.M.loaded_segments (0xea790 : word) = Some W_ea748.
Proof. vm_refl. Qed.
Lemma D_ea748 : decode_any W_ea748 = Some (Jal 1 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea74c : bv 32 := 0x5a99f0ef.
Lemma F_ea74c : fetch_word Plain.M.loaded_segments (0xea794 : word) = Some W_ea74c.
Proof. vm_refl. Qed.
Lemma D_ea74c : decode_any W_ea74c = Some (Jal 1 654760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea750 : bv 32 := 0x0017e097.
Lemma F_ea750 : fetch_word Plain.M.loaded_segments (0xea798 : word) = Some W_ea750.
Proof. vm_refl. Qed.
Lemma D_ea750 : decode_any W_ea750 = Some (Auipc 1 382, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea754 : bv 32 := 0xffc080e7.
Lemma F_ea754 : fetch_word Plain.M.loaded_segments (0xea79c : word) = Some W_ea754.
Proof. vm_refl. Qed.
Lemma D_ea754 : decode_any W_ea754 = Some (Jalr 1 1 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea758 : bv 32 := 0xa7cf70ef.
Lemma F_ea758 : fetch_word Plain.M.loaded_segments (0xea7a0 : word) = Some W_ea758.
Proof. vm_refl. Qed.
Lemma D_ea758 : decode_any W_ea758 = Some (Jal 1 2060924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea75c : bv 32 := 0xd99f70ef.
Lemma F_ea75c : fetch_word Plain.M.loaded_segments (0xea7a4 : word) = Some W_ea75c.
Proof. vm_refl. Qed.
Lemma D_ea75c : decode_any W_ea75c = Some (Jal 1 2063768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea760 : bv 32 := 0x72d150ef.
Lemma F_ea760 : fetch_word Plain.M.loaded_segments (0xea7a8 : word) = Some W_ea760.
Proof. vm_refl. Qed.
Lemma D_ea760 : decode_any W_ea760 = Some (Jal 1 89900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea764 : bv 32 := 0x581970ef.
Lemma F_ea764 : fetch_word Plain.M.loaded_segments (0xea7ac : word) = Some W_ea764.
Proof. vm_refl. Qed.
Lemma D_ea764 : decode_any W_ea764 = Some (Jal 1 621952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea768 : bv 32 := 0x714070ef.
Lemma F_ea768 : fetch_word Plain.M.loaded_segments (0xea7b0 : word) = Some W_ea768.
Proof. vm_refl. Qed.
Lemma D_ea768 : decode_any W_ea768 = Some (Jal 1 30484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea76c : bv 32 := 0xd11f40ef.
Lemma F_ea76c : fetch_word Plain.M.loaded_segments (0xea7b4 : word) = Some W_ea76c.
Proof. vm_refl. Qed.
Lemma D_ea76c : decode_any W_ea76c = Some (Jal 1 2051344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea770 : bv 32 := 0x895f90ef.
Lemma F_ea770 : fetch_word Plain.M.loaded_segments (0xea7b8 : word) = Some W_ea770.
Proof. vm_refl. Qed.
Lemma D_ea770 : decode_any W_ea770 = Some (Jal 1 2070676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea774 : bv 32 := 0x0017e097.
Lemma F_ea774 : fetch_word Plain.M.loaded_segments (0xea7bc : word) = Some W_ea774.
Proof. vm_refl. Qed.
Lemma D_ea774 : decode_any W_ea774 = Some (Auipc 1 382, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea778 : bv 32 := 0x048080e7.
Lemma F_ea778 : fetch_word Plain.M.loaded_segments (0xea7c0 : word) = Some W_ea778.
Proof. vm_refl. Qed.
Lemma D_ea778 : decode_any W_ea778 = Some (Jalr 1 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea77c : bv 32 := 0x0017e097.
Lemma F_ea77c : fetch_word Plain.M.loaded_segments (0xea7c4 : word) = Some W_ea77c.
Proof. vm_refl. Qed.
Lemma D_ea77c : decode_any W_ea77c = Some (Auipc 1 382, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea780 : bv 32 := 0x068080e7.
Lemma F_ea780 : fetch_word Plain.M.loaded_segments (0xea7c8 : word) = Some W_ea780.
Proof. vm_refl. Qed.
Lemma D_ea780 : decode_any W_ea780 = Some (Jalr 1 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea784 : bv 32 := 0x00048023.
Lemma F_ea784 : fetch_word Plain.M.loaded_segments (0xea7cc : word) = Some W_ea784.
Proof. vm_refl. Qed.
Lemma D_ea784 : decode_any W_ea784 = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea788 : bv 32 := 0x01813083.
Lemma F_ea788 : fetch_word Plain.M.loaded_segments (0xea7d0 : word) = Some W_ea788.
Proof. vm_refl. Qed.
Lemma D_ea788 : decode_any W_ea788 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea78c : bv 32 := 0x01013403.
Lemma F_ea78c : fetch_word Plain.M.loaded_segments (0xea7d4 : word) = Some W_ea78c.
Proof. vm_refl. Qed.
Lemma D_ea78c : decode_any W_ea78c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea790 : bv 32 := 0x00813483.
Lemma F_ea790 : fetch_word Plain.M.loaded_segments (0xea7d8 : word) = Some W_ea790.
Proof. vm_refl. Qed.
Lemma D_ea790 : decode_any W_ea790 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea794 : bv 32 := 0x02010113.
Lemma F_ea794 : fetch_word Plain.M.loaded_segments (0xea7dc : word) = Some W_ea794.
Proof. vm_refl. Qed.
Lemma D_ea794 : decode_any W_ea794 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ea798 : bv 32 := 0x00008067.
Lemma F_ea798 : fetch_word Plain.M.loaded_segments (0xea7e0 : word) = Some W_ea798.
Proof. vm_refl. Qed.
Lemma D_ea798 : decode_any W_ea798 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
