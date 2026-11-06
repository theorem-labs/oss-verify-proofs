(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_82014 : bv 32 := 0x691200ef.
Lemma F_82014 : fetch_word Asan.M.loaded_segments (0x82064 : word) = Some W_82014.
Proof. vm_refl. Qed.
Lemma D_82014 : decode_any W_82014 = Some (Jal 1 134800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82018 : bv 32 := 0x000df597.
Lemma F_82018 : fetch_word Asan.M.loaded_segments (0x82068 : word) = Some W_82018.
Proof. vm_refl. Qed.
Lemma D_82018 : decode_any W_82018 = Some (Auipc 11 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8201c : bv 32 := 0xba05b583.
Lemma F_8201c : fetch_word Asan.M.loaded_segments (0x8206c : word) = Some W_8201c.
Proof. vm_refl. Qed.
Lemma D_8201c : decode_any W_8201c = Some (Load SZ8 true 11 11 2976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82020 : bv 32 := 0x0225c983.
Lemma F_82020 : fetch_word Asan.M.loaded_segments (0x82070 : word) = Some W_82020.
Proof. vm_refl. Qed.
Lemma D_82020 : decode_any W_82020 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82024 : bv 32 := 0x00050913.
Lemma F_82024 : fetch_word Asan.M.loaded_segments (0x82074 : word) = Some W_82024.
Proof. vm_refl. Qed.
Lemma D_82024 : decode_any W_82024 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82028 : bv 32 := 0x3a0080ef.
Lemma F_82028 : fetch_word Asan.M.loaded_segments (0x82078 : word) = Some W_82028.
Proof. vm_refl. Qed.
Lemma D_82028 : decode_any W_82028 = Some (Jal 1 33696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8202c : bv 32 := 0x00050793.
Lemma F_8202c : fetch_word Asan.M.loaded_segments (0x8207c : word) = Some W_8202c.
Proof. vm_refl. Qed.
Lemma D_8202c : decode_any W_8202c = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82030 : bv 32 := 0x00153513.
Lemma F_82030 : fetch_word Asan.M.loaded_segments (0x82080 : word) = Some W_82030.
Proof. vm_refl. Qed.
Lemma D_82030 : decode_any W_82030 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82034 : bv 32 := 0xfff50513.
Lemma F_82034 : fetch_word Asan.M.loaded_segments (0x82084 : word) = Some W_82034.
Proof. vm_refl. Qed.
Lemma D_82034 : decode_any W_82034 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82038 : bv 32 := 0x008575b3.
Lemma F_82038 : fetch_word Asan.M.loaded_segments (0x82088 : word) = Some W_82038.
Proof. vm_refl. Qed.
Lemma D_82038 : decode_any W_82038 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8203c : bv 32 := 0x00100513.
Lemma F_8203c : fetch_word Asan.M.loaded_segments (0x8208c : word) = Some W_8203c.
Proof. vm_refl. Qed.
Lemma D_8203c : decode_any W_8203c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82040 : bv 32 := 0x00bab4a3.
Lemma F_82040 : fetch_word Asan.M.loaded_segments (0x82090 : word) = Some W_82040.
Proof. vm_refl. Qed.
Lemma D_82040 : decode_any W_82040 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82044 : bv 32 := 0x00f56a63.
Lemma F_82044 : fetch_word Asan.M.loaded_segments (0x82094 : word) = Some W_82044.
Proof. vm_refl. Qed.
Lemma D_82044 : decode_any W_82044 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82058 : bv 32 := 0x80040513.
Lemma F_82058 : fetch_word Asan.M.loaded_segments (0x820a8 : word) = Some W_82058.
Proof. vm_refl. Qed.
Lemma D_82058 : decode_any W_82058 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8205c : bv 32 := 0xfb050513.
Lemma F_8205c : fetch_word Asan.M.loaded_segments (0x820ac : word) = Some W_8205c.
Proof. vm_refl. Qed.
Lemma D_8205c : decode_any W_8205c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82060 : bv 32 := 0x00090593.
Lemma F_82060 : fetch_word Asan.M.loaded_segments (0x820b0 : word) = Some W_82060.
Proof. vm_refl. Qed.
Lemma D_82060 : decode_any W_82060 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82064 : bv 32 := 0x00040613.
Lemma F_82064 : fetch_word Asan.M.loaded_segments (0x820b4 : word) = Some W_82064.
Proof. vm_refl. Qed.
Lemma D_82064 : decode_any W_82064 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82068 : bv 32 := 0x00000693.
Lemma F_82068 : fetch_word Asan.M.loaded_segments (0x820b8 : word) = Some W_82068.
Proof. vm_refl. Qed.
Lemma D_82068 : decode_any W_82068 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8206c : bv 32 := 0x00098713.
Lemma F_8206c : fetch_word Asan.M.loaded_segments (0x820bc : word) = Some W_8206c.
Proof. vm_refl. Qed.
Lemma D_8206c : decode_any W_8206c = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82070 : bv 32 := 0x368080ef.
Lemma F_82070 : fetch_word Asan.M.loaded_segments (0x820c0 : word) = Some W_82070.
Proof. vm_refl. Qed.
Lemma D_82070 : decode_any W_82070 = Some (Jal 1 33640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82074 : bv 32 := 0x80040593.
Lemma F_82074 : fetch_word Asan.M.loaded_segments (0x820c4 : word) = Some W_82074.
Proof. vm_refl. Qed.
Lemma D_82074 : decode_any W_82074 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82078 : bv 32 := 0xfb058593.
Lemma F_82078 : fetch_word Asan.M.loaded_segments (0x820c8 : word) = Some W_82078.
Proof. vm_refl. Qed.
Lemma D_82078 : decode_any W_82078 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8207c : bv 32 := 0x00048513.
Lemma F_8207c : fetch_word Asan.M.loaded_segments (0x820cc : word) = Some W_8207c.
Proof. vm_refl. Qed.
Lemma D_8207c : decode_any W_8207c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82080 : bv 32 := 0xefcd80ef.
Lemma F_82080 : fetch_word Asan.M.loaded_segments (0x820d0 : word) = Some W_82080.
Proof. vm_refl. Qed.
Lemma D_82080 : decode_any W_82080 = Some (Jal 1 1935100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82084 : bv 32 := 0x06010113.
Lemma F_82084 : fetch_word Asan.M.loaded_segments (0x820d4 : word) = Some W_82084.
Proof. vm_refl. Qed.
Lemma D_82084 : decode_any W_82084 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82088 : bv 32 := 0x7e813083.
Lemma F_82088 : fetch_word Asan.M.loaded_segments (0x820d8 : word) = Some W_82088.
Proof. vm_refl. Qed.
Lemma D_82088 : decode_any W_82088 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8208c : bv 32 := 0x7e013403.
Lemma F_8208c : fetch_word Asan.M.loaded_segments (0x820dc : word) = Some W_8208c.
Proof. vm_refl. Qed.
Lemma D_8208c : decode_any W_8208c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82090 : bv 32 := 0x7d813483.
Lemma F_82090 : fetch_word Asan.M.loaded_segments (0x820e0 : word) = Some W_82090.
Proof. vm_refl. Qed.
Lemma D_82090 : decode_any W_82090 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82094 : bv 32 := 0x7d013903.
Lemma F_82094 : fetch_word Asan.M.loaded_segments (0x820e4 : word) = Some W_82094.
Proof. vm_refl. Qed.
Lemma D_82094 : decode_any W_82094 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82098 : bv 32 := 0x7c813983.
Lemma F_82098 : fetch_word Asan.M.loaded_segments (0x820e8 : word) = Some W_82098.
Proof. vm_refl. Qed.
Lemma D_82098 : decode_any W_82098 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8209c : bv 32 := 0x7c013a03.
Lemma F_8209c : fetch_word Asan.M.loaded_segments (0x820ec : word) = Some W_8209c.
Proof. vm_refl. Qed.
Lemma D_8209c : decode_any W_8209c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820a0 : bv 32 := 0x7b813a83.
Lemma F_820a0 : fetch_word Asan.M.loaded_segments (0x820f0 : word) = Some W_820a0.
Proof. vm_refl. Qed.
Lemma D_820a0 : decode_any W_820a0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820a4 : bv 32 := 0x7f010113.
Lemma F_820a4 : fetch_word Asan.M.loaded_segments (0x820f4 : word) = Some W_820a4.
Proof. vm_refl. Qed.
Lemma D_820a4 : decode_any W_820a4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_820a8 : bv 32 := 0x00008067.
Lemma F_820a8 : fetch_word Asan.M.loaded_segments (0x820f8 : word) = Some W_820a8.
Proof. vm_refl. Qed.
Lemma D_820a8 : decode_any W_820a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824bc : bv 32 := 0x81010113.
Lemma F_824bc : fetch_word Asan.M.loaded_segments (0x8250c : word) = Some W_824bc.
Proof. vm_refl. Qed.
Lemma D_824bc : decode_any W_824bc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824c0 : bv 32 := 0x7e113423.
Lemma F_824c0 : fetch_word Asan.M.loaded_segments (0x82510 : word) = Some W_824c0.
Proof. vm_refl. Qed.
Lemma D_824c0 : decode_any W_824c0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824c4 : bv 32 := 0x7e813023.
Lemma F_824c4 : fetch_word Asan.M.loaded_segments (0x82514 : word) = Some W_824c4.
Proof. vm_refl. Qed.
Lemma D_824c4 : decode_any W_824c4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824c8 : bv 32 := 0x7c913c23.
Lemma F_824c8 : fetch_word Asan.M.loaded_segments (0x82518 : word) = Some W_824c8.
Proof. vm_refl. Qed.
Lemma D_824c8 : decode_any W_824c8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824cc : bv 32 := 0x7d213823.
Lemma F_824cc : fetch_word Asan.M.loaded_segments (0x8251c : word) = Some W_824cc.
Proof. vm_refl. Qed.
Lemma D_824cc : decode_any W_824cc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824d0 : bv 32 := 0x7d313423.
Lemma F_824d0 : fetch_word Asan.M.loaded_segments (0x82520 : word) = Some W_824d0.
Proof. vm_refl. Qed.
Lemma D_824d0 : decode_any W_824d0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824d4 : bv 32 := 0x7d413023.
Lemma F_824d4 : fetch_word Asan.M.loaded_segments (0x82524 : word) = Some W_824d4.
Proof. vm_refl. Qed.
Lemma D_824d4 : decode_any W_824d4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824d8 : bv 32 := 0x7b513c23.
Lemma F_824d8 : fetch_word Asan.M.loaded_segments (0x82528 : word) = Some W_824d8.
Proof. vm_refl. Qed.
Lemma D_824d8 : decode_any W_824d8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824dc : bv 32 := 0x7b613823.
Lemma F_824dc : fetch_word Asan.M.loaded_segments (0x8252c : word) = Some W_824dc.
Proof. vm_refl. Qed.
Lemma D_824dc : decode_any W_824dc = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e0 : bv 32 := 0x7f010413.
Lemma F_824e0 : fetch_word Asan.M.loaded_segments (0x82530 : word) = Some W_824e0.
Proof. vm_refl. Qed.
Lemma D_824e0 : decode_any W_824e0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e4 : bv 32 := 0xf9010113.
Lemma F_824e4 : fetch_word Asan.M.loaded_segments (0x82534 : word) = Some W_824e4.
Proof. vm_refl. Qed.
Lemma D_824e4 : decode_any W_824e4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e8 : bv 32 := 0x00008993.
Lemma F_824e8 : fetch_word Asan.M.loaded_segments (0x82538 : word) = Some W_824e8.
Proof. vm_refl. Qed.
Lemma D_824e8 : decode_any W_824e8 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824ec : bv 32 := 0x00058493.
Lemma F_824ec : fetch_word Asan.M.loaded_segments (0x8253c : word) = Some W_824ec.
Proof. vm_refl. Qed.
Lemma D_824ec : decode_any W_824ec = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f0 : bv 32 := 0x00050913.
Lemma F_824f0 : fetch_word Asan.M.loaded_segments (0x82540 : word) = Some W_824f0.
Proof. vm_refl. Qed.
Lemma D_824f0 : decode_any W_824f0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f4 : bv 32 := 0x80040a93.
Lemma F_824f4 : fetch_word Asan.M.loaded_segments (0x82544 : word) = Some W_824f4.
Proof. vm_refl. Qed.
Lemma D_824f4 : decode_any W_824f4 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f8 : bv 32 := 0xfa8a8a93.
Lemma F_824f8 : fetch_word Asan.M.loaded_segments (0x82548 : word) = Some W_824f8.
Proof. vm_refl. Qed.
Lemma D_824f8 : decode_any W_824f8 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824fc : bv 32 := 0x80040513.
Lemma F_824fc : fetch_word Asan.M.loaded_segments (0x8254c : word) = Some W_824fc.
Proof. vm_refl. Qed.
Lemma D_824fc : decode_any W_824fc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82500 : bv 32 := 0xfb850513.
Lemma F_82500 : fetch_word Asan.M.loaded_segments (0x82550 : word) = Some W_82500.
Proof. vm_refl. Qed.
Lemma D_82500 : decode_any W_82500 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82504 : bv 32 := 0x7ffa8b13.
Lemma F_82504 : fetch_word Asan.M.loaded_segments (0x82554 : word) = Some W_82504.
Proof. vm_refl. Qed.
Lemma D_82504 : decode_any W_82504 = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82508 : bv 32 := 0x000b34a3.
Lemma F_82508 : fetch_word Asan.M.loaded_segments (0x82558 : word) = Some W_82508.
Proof. vm_refl. Qed.
Lemma D_82508 : decode_any W_82508 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8250c : bv 32 := 0x00aab023.
Lemma F_8250c : fetch_word Asan.M.loaded_segments (0x8255c : word) = Some W_8250c.
Proof. vm_refl. Qed.
Lemma D_8250c : decode_any W_8250c = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82510 : bv 32 := 0x000ab423.
Lemma F_82510 : fetch_word Asan.M.loaded_segments (0x82560 : word) = Some W_82510.
Proof. vm_refl. Qed.
Lemma D_82510 : decode_any W_82510 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82514 : bv 32 := 0x6b5070ef.
Lemma F_82514 : fetch_word Asan.M.loaded_segments (0x82564 : word) = Some W_82514.
Proof. vm_refl. Qed.
Lemma D_82514 : decode_any W_82514 = Some (Jal 1 32436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82518 : bv 32 := 0x00200593.
Lemma F_82518 : fetch_word Asan.M.loaded_segments (0x82568 : word) = Some W_82518.
Proof. vm_refl. Qed.
Lemma D_82518 : decode_any W_82518 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8251c : bv 32 := 0x02a5ea63.
Lemma F_8251c : fetch_word Asan.M.loaded_segments (0x8256c : word) = Some W_8251c.
Proof. vm_refl. Qed.
Lemma D_8251c : decode_any W_8251c = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82550 : bv 32 := 0x155200ef.
Lemma F_82550 : fetch_word Asan.M.loaded_segments (0x825a0 : word) = Some W_82550.
Proof. vm_refl. Qed.
Lemma D_82550 : decode_any W_82550 = Some (Jal 1 133460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82554 : bv 32 := 0x000de597.
Lemma F_82554 : fetch_word Asan.M.loaded_segments (0x825a4 : word) = Some W_82554.
Proof. vm_refl. Qed.
Lemma D_82554 : decode_any W_82554 = Some (Auipc 11 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82558 : bv 32 := 0x6645b583.
Lemma F_82558 : fetch_word Asan.M.loaded_segments (0x825a8 : word) = Some W_82558.
Proof. vm_refl. Qed.
Lemma D_82558 : decode_any W_82558 = Some (Load SZ8 true 11 11 1636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8255c : bv 32 := 0x0225ca03.
Lemma F_8255c : fetch_word Asan.M.loaded_segments (0x825ac : word) = Some W_8255c.
Proof. vm_refl. Qed.
Lemma D_8255c : decode_any W_8255c = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82560 : bv 32 := 0x00050993.
Lemma F_82560 : fetch_word Asan.M.loaded_segments (0x825b0 : word) = Some W_82560.
Proof. vm_refl. Qed.
Lemma D_82560 : decode_any W_82560 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82564 : bv 32 := 0x665070ef.
Lemma F_82564 : fetch_word Asan.M.loaded_segments (0x825b4 : word) = Some W_82564.
Proof. vm_refl. Qed.
Lemma D_82564 : decode_any W_82564 = Some (Jal 1 32356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82568 : bv 32 := 0x00050793.
Lemma F_82568 : fetch_word Asan.M.loaded_segments (0x825b8 : word) = Some W_82568.
Proof. vm_refl. Qed.
Lemma D_82568 : decode_any W_82568 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8256c : bv 32 := 0x00153513.
Lemma F_8256c : fetch_word Asan.M.loaded_segments (0x825bc : word) = Some W_8256c.
Proof. vm_refl. Qed.
Lemma D_8256c : decode_any W_8256c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82570 : bv 32 := 0xfff50513.
Lemma F_82570 : fetch_word Asan.M.loaded_segments (0x825c0 : word) = Some W_82570.
Proof. vm_refl. Qed.
Lemma D_82570 : decode_any W_82570 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82574 : bv 32 := 0x008575b3.
Lemma F_82574 : fetch_word Asan.M.loaded_segments (0x825c4 : word) = Some W_82574.
Proof. vm_refl. Qed.
Lemma D_82574 : decode_any W_82574 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82578 : bv 32 := 0x00100513.
Lemma F_82578 : fetch_word Asan.M.loaded_segments (0x825c8 : word) = Some W_82578.
Proof. vm_refl. Qed.
Lemma D_82578 : decode_any W_82578 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8257c : bv 32 := 0x00bb34a3.
Lemma F_8257c : fetch_word Asan.M.loaded_segments (0x825cc : word) = Some W_8257c.
Proof. vm_refl. Qed.
Lemma D_8257c : decode_any W_8257c = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82580 : bv 32 := 0x00f56a63.
Lemma F_82580 : fetch_word Asan.M.loaded_segments (0x825d0 : word) = Some W_82580.
Proof. vm_refl. Qed.
Lemma D_82580 : decode_any W_82580 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82594 : bv 32 := 0x80040513.
Lemma F_82594 : fetch_word Asan.M.loaded_segments (0x825e4 : word) = Some W_82594.
Proof. vm_refl. Qed.
Lemma D_82594 : decode_any W_82594 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82598 : bv 32 := 0xfa850513.
Lemma F_82598 : fetch_word Asan.M.loaded_segments (0x825e8 : word) = Some W_82598.
Proof. vm_refl. Qed.
Lemma D_82598 : decode_any W_82598 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8259c : bv 32 := 0x00098593.
Lemma F_8259c : fetch_word Asan.M.loaded_segments (0x825ec : word) = Some W_8259c.
Proof. vm_refl. Qed.
Lemma D_8259c : decode_any W_8259c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825a0 : bv 32 := 0x00040613.
Lemma F_825a0 : fetch_word Asan.M.loaded_segments (0x825f0 : word) = Some W_825a0.
Proof. vm_refl. Qed.
Lemma D_825a0 : decode_any W_825a0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825a4 : bv 32 := 0x00000693.
Lemma F_825a4 : fetch_word Asan.M.loaded_segments (0x825f4 : word) = Some W_825a4.
Proof. vm_refl. Qed.
Lemma D_825a4 : decode_any W_825a4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825a8 : bv 32 := 0x000a0713.
Lemma F_825a8 : fetch_word Asan.M.loaded_segments (0x825f8 : word) = Some W_825a8.
Proof. vm_refl. Qed.
Lemma D_825a8 : decode_any W_825a8 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825ac : bv 32 := 0x62d070ef.
Lemma F_825ac : fetch_word Asan.M.loaded_segments (0x825fc : word) = Some W_825ac.
Proof. vm_refl. Qed.
Lemma D_825ac : decode_any W_825ac = Some (Jal 1 32300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825b0 : bv 32 := 0x80040613.
Lemma F_825b0 : fetch_word Asan.M.loaded_segments (0x82600 : word) = Some W_825b0.
Proof. vm_refl. Qed.
Lemma D_825b0 : decode_any W_825b0 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825b4 : bv 32 := 0xfa860613.
Lemma F_825b4 : fetch_word Asan.M.loaded_segments (0x82604 : word) = Some W_825b4.
Proof. vm_refl. Qed.
Lemma D_825b4 : decode_any W_825b4 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825b8 : bv 32 := 0x00090513.
Lemma F_825b8 : fetch_word Asan.M.loaded_segments (0x82608 : word) = Some W_825b8.
Proof. vm_refl. Qed.
Lemma D_825b8 : decode_any W_825b8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825bc : bv 32 := 0x00048593.
Lemma F_825bc : fetch_word Asan.M.loaded_segments (0x8260c : word) = Some W_825bc.
Proof. vm_refl. Qed.
Lemma D_825bc : decode_any W_825bc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825c0 : bv 32 := 0xdadd80ef.
Lemma F_825c0 : fetch_word Asan.M.loaded_segments (0x82610 : word) = Some W_825c0.
Proof. vm_refl. Qed.
Lemma D_825c0 : decode_any W_825c0 = Some (Jal 1 1936812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825c4 : bv 32 := 0x07010113.
Lemma F_825c4 : fetch_word Asan.M.loaded_segments (0x82614 : word) = Some W_825c4.
Proof. vm_refl. Qed.
Lemma D_825c4 : decode_any W_825c4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825c8 : bv 32 := 0x7e813083.
Lemma F_825c8 : fetch_word Asan.M.loaded_segments (0x82618 : word) = Some W_825c8.
Proof. vm_refl. Qed.
Lemma D_825c8 : decode_any W_825c8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825cc : bv 32 := 0x7e013403.
Lemma F_825cc : fetch_word Asan.M.loaded_segments (0x8261c : word) = Some W_825cc.
Proof. vm_refl. Qed.
Lemma D_825cc : decode_any W_825cc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825d0 : bv 32 := 0x7d813483.
Lemma F_825d0 : fetch_word Asan.M.loaded_segments (0x82620 : word) = Some W_825d0.
Proof. vm_refl. Qed.
Lemma D_825d0 : decode_any W_825d0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825d4 : bv 32 := 0x7d013903.
Lemma F_825d4 : fetch_word Asan.M.loaded_segments (0x82624 : word) = Some W_825d4.
Proof. vm_refl. Qed.
Lemma D_825d4 : decode_any W_825d4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825d8 : bv 32 := 0x7c813983.
Lemma F_825d8 : fetch_word Asan.M.loaded_segments (0x82628 : word) = Some W_825d8.
Proof. vm_refl. Qed.
Lemma D_825d8 : decode_any W_825d8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825dc : bv 32 := 0x7c013a03.
Lemma F_825dc : fetch_word Asan.M.loaded_segments (0x8262c : word) = Some W_825dc.
Proof. vm_refl. Qed.
Lemma D_825dc : decode_any W_825dc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825e0 : bv 32 := 0x7b813a83.
Lemma F_825e0 : fetch_word Asan.M.loaded_segments (0x82630 : word) = Some W_825e0.
Proof. vm_refl. Qed.
Lemma D_825e0 : decode_any W_825e0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825e4 : bv 32 := 0x7b013b03.
Lemma F_825e4 : fetch_word Asan.M.loaded_segments (0x82634 : word) = Some W_825e4.
Proof. vm_refl. Qed.
Lemma D_825e4 : decode_any W_825e4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825e8 : bv 32 := 0x7f010113.
Lemma F_825e8 : fetch_word Asan.M.loaded_segments (0x82638 : word) = Some W_825e8.
Proof. vm_refl. Qed.
Lemma D_825e8 : decode_any W_825e8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_825ec : bv 32 := 0x00008067.
Lemma F_825ec : fetch_word Asan.M.loaded_segments (0x8263c : word) = Some W_825ec.
Proof. vm_refl. Qed.
Lemma D_825ec : decode_any W_825ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

