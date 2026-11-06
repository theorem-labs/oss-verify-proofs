(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_fe890 : bv 32 := 0xe8010113.
Lemma F_fe890 : fetch_word Asan.M.loaded_segments (0xfe890 : word) = Some W_fe890.
Proof. vm_refl. Qed.
Lemma D_fe890 : decode_any W_fe890 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe894 : bv 32 := 0x16113c23.
Lemma F_fe894 : fetch_word Asan.M.loaded_segments (0xfe894 : word) = Some W_fe894.
Proof. vm_refl. Qed.
Lemma D_fe894 : decode_any W_fe894 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe898 : bv 32 := 0x16813823.
Lemma F_fe898 : fetch_word Asan.M.loaded_segments (0xfe898 : word) = Some W_fe898.
Proof. vm_refl. Qed.
Lemma D_fe898 : decode_any W_fe898 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe89c : bv 32 := 0x16913423.
Lemma F_fe89c : fetch_word Asan.M.loaded_segments (0xfe89c : word) = Some W_fe89c.
Proof. vm_refl. Qed.
Lemma D_fe89c : decode_any W_fe89c = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8a0 : bv 32 := 0x17213023.
Lemma F_fe8a0 : fetch_word Asan.M.loaded_segments (0xfe8a0 : word) = Some W_fe8a0.
Proof. vm_refl. Qed.
Lemma D_fe8a0 : decode_any W_fe8a0 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8a4 : bv 32 := 0x00058413.
Lemma F_fe8a4 : fetch_word Asan.M.loaded_segments (0xfe8a4 : word) = Some W_fe8a4.
Proof. vm_refl. Qed.
Lemma D_fe8a4 : decode_any W_fe8a4 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8a8 : bv 32 := 0x00050493.
Lemma F_fe8a8 : fetch_word Asan.M.loaded_segments (0xfe8a8 : word) = Some W_fe8a8.
Proof. vm_refl. Qed.
Lemma D_fe8a8 : decode_any W_fe8a8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8ac : bv 32 := 0x03010513.
Lemma F_fe8ac : fetch_word Asan.M.loaded_segments (0xfe8ac : word) = Some W_fe8ac.
Proof. vm_refl. Qed.
Lemma D_fe8ac : decode_any W_fe8ac = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8b0 : bv 32 := 0x13000613.
Lemma F_fe8b0 : fetch_word Asan.M.loaded_segments (0xfe8b0 : word) = Some W_fe8b0.
Proof. vm_refl. Qed.
Lemma D_fe8b0 : decode_any W_fe8b0 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8b4 : bv 32 := 0x00000593.
Lemma F_fe8b4 : fetch_word Asan.M.loaded_segments (0xfe8b4 : word) = Some W_fe8b4.
Proof. vm_refl. Qed.
Lemma D_fe8b4 : decode_any W_fe8b4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8b8 : bv 32 := 0xe31720ef.
Lemma F_fe8b8 : fetch_word Asan.M.loaded_segments (0xfe8b8 : word) = Some W_fe8b8.
Proof. vm_refl. Qed.
Lemma D_fe8b8 : decode_any W_fe8b8 = Some (Jal 1 1519152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8bc : bv 32 := 0x0001e517.
Lemma F_fe8bc : fetch_word Asan.M.loaded_segments (0xfe8bc : word) = Some W_fe8bc.
Proof. vm_refl. Qed.
Lemma D_fe8bc : decode_any W_fe8bc = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8c0 : bv 32 := 0x87c53503.
Lemma F_fe8c0 : fetch_word Asan.M.loaded_segments (0xfe8c0 : word) = Some W_fe8c0.
Proof. vm_refl. Qed.
Lemma D_fe8c0 : decode_any W_fe8c0 = Some (Load SZ8 true 10 10 2172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8c4 : bv 32 := 0x00953023.
Lemma F_fe8c4 : fetch_word Asan.M.loaded_segments (0xfe8c4 : word) = Some W_fe8c4.
Proof. vm_refl. Qed.
Lemma D_fe8c4 : decode_any W_fe8c4 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8c8 : bv 32 := 0x0004b503.
Lemma F_fe8c8 : fetch_word Asan.M.loaded_segments (0xfe8c8 : word) = Some W_fe8c8.
Proof. vm_refl. Qed.
Lemma D_fe8c8 : decode_any W_fe8c8 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8cc : bv 32 := 0x00848493.
Lemma F_fe8cc : fetch_word Asan.M.loaded_segments (0xfe8cc : word) = Some W_fe8cc.
Proof. vm_refl. Qed.
Lemma D_fe8cc : decode_any W_fe8cc = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8d0 : bv 32 := 0xfe051ce3.
Lemma F_fe8d0 : fetch_word Asan.M.loaded_segments (0xfe8d0 : word) = Some W_fe8d0.
Proof. vm_refl. Qed.
Lemma D_fe8d0 : decode_any W_fe8d0 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8d4 : bv 32 := 0x0057f517.
Lemma F_fe8d4 : fetch_word Asan.M.loaded_segments (0xfe8d4 : word) = Some W_fe8d4.
Proof. vm_refl. Qed.
Lemma D_fe8d4 : decode_any W_fe8d4 = Some (Auipc 10 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8d8 : bv 32 := 0xe6c50913.
Lemma F_fe8d8 : fetch_word Asan.M.loaded_segments (0xfe8d8 : word) = Some W_fe8d8.
Proof. vm_refl. Qed.
Lemma D_fe8d8 : decode_any W_fe8d8 = Some (OpImm ALU_ADD 18 10 3692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8dc : bv 32 := 0x00993423.
Lemma F_fe8dc : fetch_word Asan.M.loaded_segments (0xfe8dc : word) = Some W_fe8dc.
Proof. vm_refl. Qed.
Lemma D_fe8dc : decode_any W_fe8dc = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8e0 : bv 32 := 0x0004b583.
Lemma F_fe8e0 : fetch_word Asan.M.loaded_segments (0xfe8e0 : word) = Some W_fe8e0.
Proof. vm_refl. Qed.
Lemma D_fe8e0 : decode_any W_fe8e0 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8e4 : bv 32 := 0x04058c63.
Lemma F_fe8e4 : fetch_word Asan.M.loaded_segments (0xfe8e4 : word) = Some W_fe8e4.
Proof. vm_refl. Qed.
Lemma D_fe8e4 : decode_any W_fe8e4 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8e8 : bv 32 := 0x01048493.
Lemma F_fe8e8 : fetch_word Asan.M.loaded_segments (0xfe8e8 : word) = Some W_fe8e8.
Proof. vm_refl. Qed.
Lemma D_fe8e8 : decode_any W_fe8e8 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8ec : bv 32 := 0x02500513.
Lemma F_fe8ec : fetch_word Asan.M.loaded_segments (0xfe8ec : word) = Some W_fe8ec.
Proof. vm_refl. Qed.
Lemma D_fe8ec : decode_any W_fe8ec = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8f0 : bv 32 := 0x03010613.
Lemma F_fe8f0 : fetch_word Asan.M.loaded_segments (0xfe8f0 : word) = Some W_fe8f0.
Proof. vm_refl. Qed.
Lemma D_fe8f0 : decode_any W_fe8f0 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8f4 : bv 32 := 0x0100006f.
Lemma F_fe8f4 : fetch_word Asan.M.loaded_segments (0xfe8f4 : word) = Some W_fe8f4.
Proof. vm_refl. Qed.
Lemma D_fe8f4 : decode_any W_fe8f4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8f8 : bv 32 := 0x0004b583.
Lemma F_fe8f8 : fetch_word Asan.M.loaded_segments (0xfe8f8 : word) = Some W_fe8f8.
Proof. vm_refl. Qed.
Lemma D_fe8f8 : decode_any W_fe8f8 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe8fc : bv 32 := 0x01048493.
Lemma F_fe8fc : fetch_word Asan.M.loaded_segments (0xfe8fc : word) = Some W_fe8fc.
Proof. vm_refl. Qed.
Lemma D_fe8fc : decode_any W_fe8fc = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe900 : bv 32 := 0x00058e63.
Lemma F_fe900 : fetch_word Asan.M.loaded_segments (0xfe900 : word) = Some W_fe900.
Proof. vm_refl. Qed.
Lemma D_fe900 : decode_any W_fe900 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe904 : bv 32 := 0xfeb56ae3.
Lemma F_fe904 : fetch_word Asan.M.loaded_segments (0xfe904 : word) = Some W_fe904.
Proof. vm_refl. Qed.
Lemma D_fe904 : decode_any W_fe904 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe908 : bv 32 := 0xff84b683.
Lemma F_fe908 : fetch_word Asan.M.loaded_segments (0xfe908 : word) = Some W_fe908.
Proof. vm_refl. Qed.
Lemma D_fe908 : decode_any W_fe908 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe90c : bv 32 := 0x00359593.
Lemma F_fe90c : fetch_word Asan.M.loaded_segments (0xfe90c : word) = Some W_fe90c.
Proof. vm_refl. Qed.
Lemma D_fe90c : decode_any W_fe90c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe910 : bv 32 := 0x00b605b3.
Lemma F_fe910 : fetch_word Asan.M.loaded_segments (0xfe910 : word) = Some W_fe910.
Proof. vm_refl. Qed.
Lemma D_fe910 : decode_any W_fe910 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe914 : bv 32 := 0x00d5b023.
Lemma F_fe914 : fetch_word Asan.M.loaded_segments (0xfe914 : word) = Some W_fe914.
Proof. vm_refl. Qed.
Lemma D_fe914 : decode_any W_fe914 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe918 : bv 32 := 0xfe1ff06f.
Lemma F_fe918 : fetch_word Asan.M.loaded_segments (0xfe918 : word) = Some W_fe918.
Proof. vm_refl. Qed.
Lemma D_fe918 : decode_any W_fe918 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe91c : bv 32 := 0x0b013583.
Lemma F_fe91c : fetch_word Asan.M.loaded_segments (0xfe91c : word) = Some W_fe91c.
Proof. vm_refl. Qed.
Lemma D_fe91c : decode_any W_fe91c = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe920 : bv 32 := 0x13013503.
Lemma F_fe920 : fetch_word Asan.M.loaded_segments (0xfe920 : word) = Some W_fe920.
Proof. vm_refl. Qed.
Lemma D_fe920 : decode_any W_fe920 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe924 : bv 32 := 0x0057f617.
Lemma F_fe924 : fetch_word Asan.M.loaded_segments (0xfe924 : word) = Some W_fe924.
Proof. vm_refl. Qed.
Lemma D_fe924 : decode_any W_fe924 = Some (Auipc 12 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe928 : bv 32 := 0xe8b63223.
Lemma F_fe928 : fetch_word Asan.M.loaded_segments (0xfe928 : word) = Some W_fe928.
Proof. vm_refl. Qed.
Lemma D_fe928 : decode_any W_fe928 = Some (Store SZ8 12 11 3716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe92c : bv 32 := 0x00050c63.
Lemma F_fe92c : fetch_word Asan.M.loaded_segments (0xfe92c : word) = Some W_fe92c.
Proof. vm_refl. Qed.
Lemma D_fe92c : decode_any W_fe92c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe930 : bv 32 := 0x0057f597.
Lemma F_fe930 : fetch_word Asan.M.loaded_segments (0xfe930 : word) = Some W_fe930.
Proof. vm_refl. Qed.
Lemma D_fe930 : decode_any W_fe930 = Some (Auipc 11 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe934 : bv 32 := 0xdea5bc23.
Lemma F_fe934 : fetch_word Asan.M.loaded_segments (0xfe934 : word) = Some W_fe934.
Proof. vm_refl. Qed.
Lemma D_fe934 : decode_any W_fe934 = Some (Store SZ8 11 10 3576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe938 : bv 32 := 0x00c0006f.
Lemma F_fe938 : fetch_word Asan.M.loaded_segments (0xfe938 : word) = Some W_fe938.
Proof. vm_refl. Qed.
Lemma D_fe938 : decode_any W_fe938 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe93c : bv 32 := 0x0057f517.
Lemma F_fe93c : fetch_word Asan.M.loaded_segments (0xfe93c : word) = Some W_fe93c.
Proof. vm_refl. Qed.
Lemma D_fe93c : decode_any W_fe93c = Some (Auipc 10 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe940 : bv 32 := 0xe6053623.
Lemma F_fe940 : fetch_word Asan.M.loaded_segments (0xfe940 : word) = Some W_fe940.
Proof. vm_refl. Qed.
Lemma D_fe940 : decode_any W_fe940 = Some (Store SZ8 10 0 3692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe944 : bv 32 := 0x06013503.
Lemma F_fe944 : fetch_word Asan.M.loaded_segments (0xfe944 : word) = Some W_fe944.
Proof. vm_refl. Qed.
Lemma D_fe944 : decode_any W_fe944 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe948 : bv 32 := 0x02a93823.
Lemma F_fe948 : fetch_word Asan.M.loaded_segments (0xfe948 : word) = Some W_fe948.
Proof. vm_refl. Qed.
Lemma D_fe948 : decode_any W_fe948 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe94c : bv 32 := 0x00041463.
Lemma F_fe94c : fetch_word Asan.M.loaded_segments (0xfe94c : word) = Some W_fe94c.
Proof. vm_refl. Qed.
Lemma D_fe94c : decode_any W_fe94c = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe950 : bv 32 := 0x12813403.
Lemma F_fe950 : fetch_word Asan.M.loaded_segments (0xfe950 : word) = Some W_fe950.
Proof. vm_refl. Qed.
Lemma D_fe950 : decode_any W_fe950 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe954 : bv 32 := 0x00041663.
Lemma F_fe954 : fetch_word Asan.M.loaded_segments (0xfe954 : word) = Some W_fe954.
Proof. vm_refl. Qed.
Lemma D_fe954 : decode_any W_fe954 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe958 : bv 32 := 0xfff16517.
Lemma F_fe958 : fetch_word Asan.M.loaded_segments (0xfe958 : word) = Some W_fe958.
Proof. vm_refl. Qed.
Lemma D_fe958 : decode_any W_fe958 = Some (Auipc 10 1048342, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe95c : bv 32 := 0x00b50413.
Lemma F_fe95c : fetch_word Asan.M.loaded_segments (0xfe95c : word) = Some W_fe95c.
Proof. vm_refl. Qed.
Lemma D_fe95c : decode_any W_fe95c = Some (OpImm ALU_ADD 8 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe960 : bv 32 := 0x0001d517.
Lemma F_fe960 : fetch_word Asan.M.loaded_segments (0xfe960 : word) = Some W_fe960.
Proof. vm_refl. Qed.
Lemma D_fe960 : decode_any W_fe960 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe964 : bv 32 := 0x7e053583.
Lemma F_fe964 : fetch_word Asan.M.loaded_segments (0xfe964 : word) = Some W_fe964.
Proof. vm_refl. Qed.
Lemma D_fe964 : decode_any W_fe964 = Some (Load SZ8 true 11 10 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe968 : bv 32 := 0x0001d517.
Lemma F_fe968 : fetch_word Asan.M.loaded_segments (0xfe968 : word) = Some W_fe968.
Proof. vm_refl. Qed.
Lemma D_fe968 : decode_any W_fe968 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe96c : bv 32 := 0x7e053503.
Lemma F_fe96c : fetch_word Asan.M.loaded_segments (0xfe96c : word) = Some W_fe96c.
Proof. vm_refl. Qed.
Lemma D_fe96c : decode_any W_fe96c = Some (Load SZ8 true 10 10 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe970 : bv 32 := 0x0085b023.
Lemma F_fe970 : fetch_word Asan.M.loaded_segments (0xfe970 : word) = Some W_fe970.
Proof. vm_refl. Qed.
Lemma D_fe970 : decode_any W_fe970 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe974 : bv 32 := 0x00140593.
Lemma F_fe974 : fetch_word Asan.M.loaded_segments (0xfe974 : word) = Some W_fe974.
Proof. vm_refl. Qed.
Lemma D_fe974 : decode_any W_fe974 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe978 : bv 32 := 0x00853023.
Lemma F_fe978 : fetch_word Asan.M.loaded_segments (0xfe978 : word) = Some W_fe978.
Proof. vm_refl. Qed.
Lemma D_fe978 : decode_any W_fe978 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe97c : bv 32 := 0x02f00613.
Lemma F_fe97c : fetch_word Asan.M.loaded_segments (0xfe97c : word) = Some W_fe97c.
Proof. vm_refl. Qed.
Lemma D_fe97c : decode_any W_fe97c = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe980 : bv 32 := 0x00c0006f.
Lemma F_fe980 : fetch_word Asan.M.loaded_segments (0xfe980 : word) = Some W_fe980.
Proof. vm_refl. Qed.
Lemma D_fe980 : decode_any W_fe980 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe984 : bv 32 := 0x00b53023.
Lemma F_fe984 : fetch_word Asan.M.loaded_segments (0xfe984 : word) = Some W_fe984.
Proof. vm_refl. Qed.
Lemma D_fe984 : decode_any W_fe984 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe988 : bv 32 := 0x00158593.
Lemma F_fe988 : fetch_word Asan.M.loaded_segments (0xfe988 : word) = Some W_fe988.
Proof. vm_refl. Qed.
Lemma D_fe988 : decode_any W_fe988 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe98c : bv 32 := 0xfff5c683.
Lemma F_fe98c : fetch_word Asan.M.loaded_segments (0xfe98c : word) = Some W_fe98c.
Proof. vm_refl. Qed.
Lemma D_fe98c : decode_any W_fe98c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe990 : bv 32 := 0xfec68ae3.
Lemma F_fe990 : fetch_word Asan.M.loaded_segments (0xfe990 : word) = Some W_fe990.
Proof. vm_refl. Qed.
Lemma D_fe990 : decode_any W_fe990 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe994 : bv 32 := 0xfe069ae3.
Lemma F_fe994 : fetch_word Asan.M.loaded_segments (0xfe994 : word) = Some W_fe994.
Proof. vm_refl. Qed.
Lemma D_fe994 : decode_any W_fe994 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe998 : bv 32 := 0x03010513.
Lemma F_fe998 : fetch_word Asan.M.loaded_segments (0xfe998 : word) = Some W_fe998.
Proof. vm_refl. Qed.
Lemma D_fe998 : decode_any W_fe998 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe99c : bv 32 := 0x2ec000ef.
Lemma F_fe99c : fetch_word Asan.M.loaded_segments (0xfe99c : word) = Some W_fe99c.
Proof. vm_refl. Qed.
Lemma D_fe99c : decode_any W_fe99c = Some (Jal 1 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9a0 : bv 32 := 0x0f813503.
Lemma F_fe9a0 : fetch_word Asan.M.loaded_segments (0xfe9a0 : word) = Some W_fe9a0.
Proof. vm_refl. Qed.
Lemma D_fe9a0 : decode_any W_fe9a0 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9a4 : bv 32 := 0x594000ef.
Lemma F_fe9a4 : fetch_word Asan.M.loaded_segments (0xfe9a4 : word) = Some W_fe9a4.
Proof. vm_refl. Qed.
Lemma D_fe9a4 : decode_any W_fe9a4 = Some (Jal 1 1428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9a8 : bv 32 := 0x08813503.
Lemma F_fe9a8 : fetch_word Asan.M.loaded_segments (0xfe9a8 : word) = Some W_fe9a8.
Proof. vm_refl. Qed.
Lemma D_fe9a8 : decode_any W_fe9a8 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9ac : bv 32 := 0x09013583.
Lemma F_fe9ac : fetch_word Asan.M.loaded_segments (0xfe9ac : word) = Some W_fe9ac.
Proof. vm_refl. Qed.
Lemma D_fe9ac : decode_any W_fe9ac = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9b0 : bv 32 := 0x00b51c63.
Lemma F_fe9b0 : fetch_word Asan.M.loaded_segments (0xfe9b0 : word) = Some W_fe9b0.
Proof. vm_refl. Qed.
Lemma D_fe9b0 : decode_any W_fe9b0 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9b4 : bv 32 := 0x09813503.
Lemma F_fe9b4 : fetch_word Asan.M.loaded_segments (0xfe9b4 : word) = Some W_fe9b4.
Proof. vm_refl. Qed.
Lemma D_fe9b4 : decode_any W_fe9b4 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9b8 : bv 32 := 0x0a013583.
Lemma F_fe9b8 : fetch_word Asan.M.loaded_segments (0xfe9b8 : word) = Some W_fe9b8.
Proof. vm_refl. Qed.
Lemma D_fe9b8 : decode_any W_fe9b8 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9bc : bv 32 := 0x00b51663.
Lemma F_fe9bc : fetch_word Asan.M.loaded_segments (0xfe9bc : word) = Some W_fe9bc.
Proof. vm_refl. Qed.
Lemma D_fe9bc : decode_any W_fe9bc = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9c0 : bv 32 := 0x0e813503.
Lemma F_fe9c0 : fetch_word Asan.M.loaded_segments (0xfe9c0 : word) = Some W_fe9c0.
Proof. vm_refl. Qed.
Lemma D_fe9c0 : decode_any W_fe9c0 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9c4 : bv 32 := 0x0e050063.
Lemma F_fe9c4 : fetch_word Asan.M.loaded_segments (0xfe9c4 : word) = Some W_fe9c4.
Proof. vm_refl. Qed.
Lemma D_fe9c4 : decode_any W_fe9c4 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9c8 : bv 32 := 0x00200693.
Lemma F_fe9c8 : fetch_word Asan.M.loaded_segments (0xfe9c8 : word) = Some W_fe9c8.
Proof. vm_refl. Qed.
Lemma D_fe9c8 : decode_any W_fe9c8 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9cc : bv 32 := 0x00100793.
Lemma F_fe9cc : fetch_word Asan.M.loaded_segments (0xfe9cc : word) = Some W_fe9cc.
Proof. vm_refl. Qed.
Lemma D_fe9cc : decode_any W_fe9cc = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9d0 : bv 32 := 0x00013423.
Lemma F_fe9d0 : fetch_word Asan.M.loaded_segments (0xfe9d0 : word) = Some W_fe9d0.
Proof. vm_refl. Qed.
Lemma D_fe9d0 : decode_any W_fe9d0 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9d4 : bv 32 := 0x00013823.
Lemma F_fe9d4 : fetch_word Asan.M.loaded_segments (0xfe9d4 : word) = Some W_fe9d4.
Proof. vm_refl. Qed.
Lemma D_fe9d4 : decode_any W_fe9d4 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9d8 : bv 32 := 0x04900893.
Lemma F_fe9d8 : fetch_word Asan.M.loaded_segments (0xfe9d8 : word) = Some W_fe9d8.
Proof. vm_refl. Qed.
Lemma D_fe9d8 : decode_any W_fe9d8 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9dc : bv 32 := 0x01810513.
Lemma F_fe9dc : fetch_word Asan.M.loaded_segments (0xfe9dc : word) = Some W_fe9dc.
Proof. vm_refl. Qed.
Lemma D_fe9dc : decode_any W_fe9dc = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9e0 : bv 32 := 0x00300593.
Lemma F_fe9e0 : fetch_word Asan.M.loaded_segments (0xfe9e0 : word) = Some W_fe9e0.
Proof. vm_refl. Qed.
Lemma D_fe9e0 : decode_any W_fe9e0 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9e4 : bv 32 := 0x00810613.
Lemma F_fe9e4 : fetch_word Asan.M.loaded_segments (0xfe9e4 : word) = Some W_fe9e4.
Proof. vm_refl. Qed.
Lemma D_fe9e4 : decode_any W_fe9e4 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9e8 : bv 32 := 0x00800713.
Lemma F_fe9e8 : fetch_word Asan.M.loaded_segments (0xfe9e8 : word) = Some W_fe9e8.
Proof. vm_refl. Qed.
Lemma D_fe9e8 : decode_any W_fe9e8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9ec : bv 32 := 0x00013c23.
Lemma F_fe9ec : fetch_word Asan.M.loaded_segments (0xfe9ec : word) = Some W_fe9ec.
Proof. vm_refl. Qed.
Lemma D_fe9ec : decode_any W_fe9ec = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9f0 : bv 32 := 0x02f13023.
Lemma F_fe9f0 : fetch_word Asan.M.loaded_segments (0xfe9f0 : word) = Some W_fe9f0.
Proof. vm_refl. Qed.
Lemma D_fe9f0 : decode_any W_fe9f0 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9f4 : bv 32 := 0x02d13423.
Lemma F_fe9f4 : fetch_word Asan.M.loaded_segments (0xfe9f4 : word) = Some W_fe9f4.
Proof. vm_refl. Qed.
Lemma D_fe9f4 : decode_any W_fe9f4 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9f8 : bv 32 := 0x00000693.
Lemma F_fe9f8 : fetch_word Asan.M.loaded_segments (0xfe9f8 : word) = Some W_fe9f8.
Proof. vm_refl. Qed.
Lemma D_fe9f8 : decode_any W_fe9f8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fe9fc : bv 32 := 0x00000073.
Lemma F_fe9fc : fetch_word Asan.M.loaded_segments (0xfe9fc : word) = Some W_fe9fc.
Proof. vm_refl. Qed.
Lemma D_fe9fc : decode_any W_fe9fc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_fe9fc : is_ecall W_fe9fc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_fea00 : bv 32 := 0x02051513.
Lemma F_fea00 : fetch_word Asan.M.loaded_segments (0xfea00 : word) = Some W_fea00.
Proof. vm_refl. Qed.
Lemma D_fea00 : decode_any W_fea00 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea04 : bv 32 := 0x00055463.
Lemma F_fea04 : fetch_word Asan.M.loaded_segments (0xfea04 : word) = Some W_fea04.
Proof. vm_refl. Qed.
Lemma D_fea04 : decode_any W_fea04 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea08 : bv 32 := 0x00000023.
Lemma F_fea08 : fetch_word Asan.M.loaded_segments (0xfea08 : word) = Some W_fea08.
Proof. vm_refl. Qed.
Lemma D_fea08 : decode_any W_fea08 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea0c : bv 32 := 0x01e15503.
Lemma F_fea0c : fetch_word Asan.M.loaded_segments (0xfea0c : word) = Some W_fea0c.
Proof. vm_refl. Qed.
Lemma D_fea0c : decode_any W_fea0c = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea10 : bv 32 := 0x02057513.
Lemma F_fea10 : fetch_word Asan.M.loaded_segments (0xfea10 : word) = Some W_fea10.
Proof. vm_refl. Qed.
Lemma D_fea10 : decode_any W_fea10 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea14 : bv 32 := 0x02050463.
Lemma F_fea14 : fetch_word Asan.M.loaded_segments (0xfea14 : word) = Some W_fea14.
Proof. vm_refl. Qed.
Lemma D_fea14 : decode_any W_fea14 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea18 : bv 32 := 0xfff25517.
Lemma F_fea18 : fetch_word Asan.M.loaded_segments (0xfea18 : word) = Some W_fea18.
Proof. vm_refl. Qed.
Lemma D_fea18 : decode_any W_fea18 = Some (Auipc 10 1048357, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea1c : bv 32 := 0x00008637.
Lemma F_fea1c : fetch_word Asan.M.loaded_segments (0xfea1c : word) = Some W_fea1c.
Proof. vm_refl. Qed.
Lemma D_fea1c : decode_any W_fea1c = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea20 : bv 32 := 0x03800893.
Lemma F_fea20 : fetch_word Asan.M.loaded_segments (0xfea20 : word) = Some W_fea20.
Proof. vm_refl. Qed.
Lemma D_fea20 : decode_any W_fea20 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea24 : bv 32 := 0x7e550593.
Lemma F_fea24 : fetch_word Asan.M.loaded_segments (0xfea24 : word) = Some W_fea24.
Proof. vm_refl. Qed.
Lemma D_fea24 : decode_any W_fea24 = Some (OpImm ALU_ADD 11 10 2021, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea28 : bv 32 := 0x0026061b.
Lemma F_fea28 : fetch_word Asan.M.loaded_segments (0xfea28 : word) = Some W_fea28.
Proof. vm_refl. Qed.
Lemma D_fea28 : decode_any W_fea28 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea2c : bv 32 := 0xf9c00513.
Lemma F_fea2c : fetch_word Asan.M.loaded_segments (0xfea2c : word) = Some W_fea2c.
Proof. vm_refl. Qed.
Lemma D_fea2c : decode_any W_fea2c = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea30 : bv 32 := 0x00000073.
Lemma F_fea30 : fetch_word Asan.M.loaded_segments (0xfea30 : word) = Some W_fea30.
Proof. vm_refl. Qed.
Lemma D_fea30 : decode_any W_fea30 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_fea30 : is_ecall W_fea30 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_fea34 : bv 32 := 0x00055463.
Lemma F_fea34 : fetch_word Asan.M.loaded_segments (0xfea34 : word) = Some W_fea34.
Proof. vm_refl. Qed.
Lemma D_fea34 : decode_any W_fea34 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea38 : bv 32 := 0x00000023.
Lemma F_fea38 : fetch_word Asan.M.loaded_segments (0xfea38 : word) = Some W_fea38.
Proof. vm_refl. Qed.
Lemma D_fea38 : decode_any W_fea38 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea3c : bv 32 := 0x02615503.
Lemma F_fea3c : fetch_word Asan.M.loaded_segments (0xfea3c : word) = Some W_fea3c.
Proof. vm_refl. Qed.
Lemma D_fea3c : decode_any W_fea3c = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea40 : bv 32 := 0x02057513.
Lemma F_fea40 : fetch_word Asan.M.loaded_segments (0xfea40 : word) = Some W_fea40.
Proof. vm_refl. Qed.
Lemma D_fea40 : decode_any W_fea40 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea44 : bv 32 := 0x02050463.
Lemma F_fea44 : fetch_word Asan.M.loaded_segments (0xfea44 : word) = Some W_fea44.
Proof. vm_refl. Qed.
Lemma D_fea44 : decode_any W_fea44 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea48 : bv 32 := 0xfff25517.
Lemma F_fea48 : fetch_word Asan.M.loaded_segments (0xfea48 : word) = Some W_fea48.
Proof. vm_refl. Qed.
Lemma D_fea48 : decode_any W_fea48 = Some (Auipc 10 1048357, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea4c : bv 32 := 0x00008637.
Lemma F_fea4c : fetch_word Asan.M.loaded_segments (0xfea4c : word) = Some W_fea4c.
Proof. vm_refl. Qed.
Lemma D_fea4c : decode_any W_fea4c = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea50 : bv 32 := 0x03800893.
Lemma F_fea50 : fetch_word Asan.M.loaded_segments (0xfea50 : word) = Some W_fea50.
Proof. vm_refl. Qed.
Lemma D_fea50 : decode_any W_fea50 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea54 : bv 32 := 0x7b550593.
Lemma F_fea54 : fetch_word Asan.M.loaded_segments (0xfea54 : word) = Some W_fea54.
Proof. vm_refl. Qed.
Lemma D_fea54 : decode_any W_fea54 = Some (OpImm ALU_ADD 11 10 1973, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea58 : bv 32 := 0x0026061b.
Lemma F_fea58 : fetch_word Asan.M.loaded_segments (0xfea58 : word) = Some W_fea58.
Proof. vm_refl. Qed.
Lemma D_fea58 : decode_any W_fea58 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea5c : bv 32 := 0xf9c00513.
Lemma F_fea5c : fetch_word Asan.M.loaded_segments (0xfea5c : word) = Some W_fea5c.
Proof. vm_refl. Qed.
Lemma D_fea5c : decode_any W_fea5c = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea60 : bv 32 := 0x00000073.
Lemma F_fea60 : fetch_word Asan.M.loaded_segments (0xfea60 : word) = Some W_fea60.
Proof. vm_refl. Qed.
Lemma D_fea60 : decode_any W_fea60 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_fea60 : is_ecall W_fea60 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_fea64 : bv 32 := 0x00055463.
Lemma F_fea64 : fetch_word Asan.M.loaded_segments (0xfea64 : word) = Some W_fea64.
Proof. vm_refl. Qed.
Lemma D_fea64 : decode_any W_fea64 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea68 : bv 32 := 0x00000023.
Lemma F_fea68 : fetch_word Asan.M.loaded_segments (0xfea68 : word) = Some W_fea68.
Proof. vm_refl. Qed.
Lemma D_fea68 : decode_any W_fea68 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea6c : bv 32 := 0x02e15503.
Lemma F_fea6c : fetch_word Asan.M.loaded_segments (0xfea6c : word) = Some W_fea6c.
Proof. vm_refl. Qed.
Lemma D_fea6c : decode_any W_fea6c = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea70 : bv 32 := 0x02057513.
Lemma F_fea70 : fetch_word Asan.M.loaded_segments (0xfea70 : word) = Some W_fea70.
Proof. vm_refl. Qed.
Lemma D_fea70 : decode_any W_fea70 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea74 : bv 32 := 0x02050463.
Lemma F_fea74 : fetch_word Asan.M.loaded_segments (0xfea74 : word) = Some W_fea74.
Proof. vm_refl. Qed.
Lemma D_fea74 : decode_any W_fea74 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea78 : bv 32 := 0xfff25517.
Lemma F_fea78 : fetch_word Asan.M.loaded_segments (0xfea78 : word) = Some W_fea78.
Proof. vm_refl. Qed.
Lemma D_fea78 : decode_any W_fea78 = Some (Auipc 10 1048357, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea7c : bv 32 := 0x00008637.
Lemma F_fea7c : fetch_word Asan.M.loaded_segments (0xfea7c : word) = Some W_fea7c.
Proof. vm_refl. Qed.
Lemma D_fea7c : decode_any W_fea7c = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea80 : bv 32 := 0x03800893.
Lemma F_fea80 : fetch_word Asan.M.loaded_segments (0xfea80 : word) = Some W_fea80.
Proof. vm_refl. Qed.
Lemma D_fea80 : decode_any W_fea80 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea84 : bv 32 := 0x78550593.
Lemma F_fea84 : fetch_word Asan.M.loaded_segments (0xfea84 : word) = Some W_fea84.
Proof. vm_refl. Qed.
Lemma D_fea84 : decode_any W_fea84 = Some (OpImm ALU_ADD 11 10 1925, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea88 : bv 32 := 0x0026061b.
Lemma F_fea88 : fetch_word Asan.M.loaded_segments (0xfea88 : word) = Some W_fea88.
Proof. vm_refl. Qed.
Lemma D_fea88 : decode_any W_fea88 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea8c : bv 32 := 0xf9c00513.
Lemma F_fea8c : fetch_word Asan.M.loaded_segments (0xfea8c : word) = Some W_fea8c.
Proof. vm_refl. Qed.
Lemma D_fea8c : decode_any W_fea8c = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea90 : bv 32 := 0x00000073.
Lemma F_fea90 : fetch_word Asan.M.loaded_segments (0xfea90 : word) = Some W_fea90.
Proof. vm_refl. Qed.
Lemma D_fea90 : decode_any W_fea90 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_fea90 : is_ecall W_fea90 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_fea94 : bv 32 := 0x00055463.
Lemma F_fea94 : fetch_word Asan.M.loaded_segments (0xfea94 : word) = Some W_fea94.
Proof. vm_refl. Qed.
Lemma D_fea94 : decode_any W_fea94 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea98 : bv 32 := 0x00000023.
Lemma F_fea98 : fetch_word Asan.M.loaded_segments (0xfea98 : word) = Some W_fea98.
Proof. vm_refl. Qed.
Lemma D_fea98 : decode_any W_fea98 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fea9c : bv 32 := 0x00100513.
Lemma F_fea9c : fetch_word Asan.M.loaded_segments (0xfea9c : word) = Some W_fea9c.
Proof. vm_refl. Qed.
Lemma D_fea9c : decode_any W_fea9c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feaa0 : bv 32 := 0x00a90123.
Lemma F_feaa0 : fetch_word Asan.M.loaded_segments (0xfeaa0 : word) = Some W_feaa0.
Proof. vm_refl. Qed.
Lemma D_feaa0 : decode_any W_feaa0 = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feaa4 : bv 32 := 0x17813083.
Lemma F_feaa4 : fetch_word Asan.M.loaded_segments (0xfeaa4 : word) = Some W_feaa4.
Proof. vm_refl. Qed.
Lemma D_feaa4 : decode_any W_feaa4 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feaa8 : bv 32 := 0x17013403.
Lemma F_feaa8 : fetch_word Asan.M.loaded_segments (0xfeaa8 : word) = Some W_feaa8.
Proof. vm_refl. Qed.
Lemma D_feaa8 : decode_any W_feaa8 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feaac : bv 32 := 0x16813483.
Lemma F_feaac : fetch_word Asan.M.loaded_segments (0xfeaac : word) = Some W_feaac.
Proof. vm_refl. Qed.
Lemma D_feaac : decode_any W_feaac = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feab0 : bv 32 := 0x16013903.
Lemma F_feab0 : fetch_word Asan.M.loaded_segments (0xfeab0 : word) = Some W_feab0.
Proof. vm_refl. Qed.
Lemma D_feab0 : decode_any W_feab0 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feab4 : bv 32 := 0x18010113.
Lemma F_feab4 : fetch_word Asan.M.loaded_segments (0xfeab4 : word) = Some W_feab4.
Proof. vm_refl. Qed.
Lemma D_feab4 : decode_any W_feab4 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feab8 : bv 32 := 0x00008067.
Lemma F_feab8 : fetch_word Asan.M.loaded_segments (0xfeab8 : word) = Some W_feab8.
Proof. vm_refl. Qed.
Lemma D_feab8 : decode_any W_feab8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
