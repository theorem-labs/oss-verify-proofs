(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_81010 : bv 32 := 0x691200ef.
Lemma F_81010 : fetch_word AsanUbsan.M.loaded_segments (0x81058 : word) = Some W_81010.
Proof. vm_refl. Qed.
Lemma D_81010 : decode_any W_81010 = Some (Jal 1 134800, 4%Z).
Proof. vm_refl. Qed.

Definition W_81014 : bv 32 := 0x000d3597.
Lemma F_81014 : fetch_word AsanUbsan.M.loaded_segments (0x8105c : word) = Some W_81014.
Proof. vm_refl. Qed.
Lemma D_81014 : decode_any W_81014 = Some (Auipc 11 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_81018 : bv 32 := 0x4945b583.
Lemma F_81018 : fetch_word AsanUbsan.M.loaded_segments (0x81060 : word) = Some W_81018.
Proof. vm_refl. Qed.
Lemma D_81018 : decode_any W_81018 = Some (Load SZ8 true 11 11 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_8101c : bv 32 := 0x0225c983.
Lemma F_8101c : fetch_word AsanUbsan.M.loaded_segments (0x81064 : word) = Some W_8101c.
Proof. vm_refl. Qed.
Lemma D_8101c : decode_any W_8101c = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_81020 : bv 32 := 0x00050913.
Lemma F_81020 : fetch_word AsanUbsan.M.loaded_segments (0x81068 : word) = Some W_81020.
Proof. vm_refl. Qed.
Lemma D_81020 : decode_any W_81020 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81024 : bv 32 := 0x3a0080ef.
Lemma F_81024 : fetch_word AsanUbsan.M.loaded_segments (0x8106c : word) = Some W_81024.
Proof. vm_refl. Qed.
Lemma D_81024 : decode_any W_81024 = Some (Jal 1 33696, 4%Z).
Proof. vm_refl. Qed.

Definition W_81028 : bv 32 := 0x00050793.
Lemma F_81028 : fetch_word AsanUbsan.M.loaded_segments (0x81070 : word) = Some W_81028.
Proof. vm_refl. Qed.
Lemma D_81028 : decode_any W_81028 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8102c : bv 32 := 0x00153513.
Lemma F_8102c : fetch_word AsanUbsan.M.loaded_segments (0x81074 : word) = Some W_8102c.
Proof. vm_refl. Qed.
Lemma D_8102c : decode_any W_8102c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81030 : bv 32 := 0xfff50513.
Lemma F_81030 : fetch_word AsanUbsan.M.loaded_segments (0x81078 : word) = Some W_81030.
Proof. vm_refl. Qed.
Lemma D_81030 : decode_any W_81030 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81034 : bv 32 := 0x008575b3.
Lemma F_81034 : fetch_word AsanUbsan.M.loaded_segments (0x8107c : word) = Some W_81034.
Proof. vm_refl. Qed.
Lemma D_81034 : decode_any W_81034 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81038 : bv 32 := 0x00100513.
Lemma F_81038 : fetch_word AsanUbsan.M.loaded_segments (0x81080 : word) = Some W_81038.
Proof. vm_refl. Qed.
Lemma D_81038 : decode_any W_81038 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8103c : bv 32 := 0x00bab4a3.
Lemma F_8103c : fetch_word AsanUbsan.M.loaded_segments (0x81084 : word) = Some W_8103c.
Proof. vm_refl. Qed.
Lemma D_8103c : decode_any W_8103c = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81040 : bv 32 := 0x00f56a63.
Lemma F_81040 : fetch_word AsanUbsan.M.loaded_segments (0x81088 : word) = Some W_81040.
Proof. vm_refl. Qed.
Lemma D_81040 : decode_any W_81040 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_81054 : bv 32 := 0x80040513.
Lemma F_81054 : fetch_word AsanUbsan.M.loaded_segments (0x8109c : word) = Some W_81054.
Proof. vm_refl. Qed.
Lemma D_81054 : decode_any W_81054 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_81058 : bv 32 := 0xfb050513.
Lemma F_81058 : fetch_word AsanUbsan.M.loaded_segments (0x810a0 : word) = Some W_81058.
Proof. vm_refl. Qed.
Lemma D_81058 : decode_any W_81058 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8105c : bv 32 := 0x00090593.
Lemma F_8105c : fetch_word AsanUbsan.M.loaded_segments (0x810a4 : word) = Some W_8105c.
Proof. vm_refl. Qed.
Lemma D_8105c : decode_any W_8105c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81060 : bv 32 := 0x00040613.
Lemma F_81060 : fetch_word AsanUbsan.M.loaded_segments (0x810a8 : word) = Some W_81060.
Proof. vm_refl. Qed.
Lemma D_81060 : decode_any W_81060 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81064 : bv 32 := 0x00000693.
Lemma F_81064 : fetch_word AsanUbsan.M.loaded_segments (0x810ac : word) = Some W_81064.
Proof. vm_refl. Qed.
Lemma D_81064 : decode_any W_81064 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81068 : bv 32 := 0x00098713.
Lemma F_81068 : fetch_word AsanUbsan.M.loaded_segments (0x810b0 : word) = Some W_81068.
Proof. vm_refl. Qed.
Lemma D_81068 : decode_any W_81068 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8106c : bv 32 := 0x368080ef.
Lemma F_8106c : fetch_word AsanUbsan.M.loaded_segments (0x810b4 : word) = Some W_8106c.
Proof. vm_refl. Qed.
Lemma D_8106c : decode_any W_8106c = Some (Jal 1 33640, 4%Z).
Proof. vm_refl. Qed.

Definition W_81070 : bv 32 := 0x80040593.
Lemma F_81070 : fetch_word AsanUbsan.M.loaded_segments (0x810b8 : word) = Some W_81070.
Proof. vm_refl. Qed.
Lemma D_81070 : decode_any W_81070 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_81074 : bv 32 := 0xfb058593.
Lemma F_81074 : fetch_word AsanUbsan.M.loaded_segments (0x810bc : word) = Some W_81074.
Proof. vm_refl. Qed.
Lemma D_81074 : decode_any W_81074 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_81078 : bv 32 := 0x00048513.
Lemma F_81078 : fetch_word AsanUbsan.M.loaded_segments (0x810c0 : word) = Some W_81078.
Proof. vm_refl. Qed.
Lemma D_81078 : decode_any W_81078 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8107c : bv 32 := 0xefcd80ef.
Lemma F_8107c : fetch_word AsanUbsan.M.loaded_segments (0x810c4 : word) = Some W_8107c.
Proof. vm_refl. Qed.
Lemma D_8107c : decode_any W_8107c = Some (Jal 1 1935100, 4%Z).
Proof. vm_refl. Qed.

Definition W_81080 : bv 32 := 0x06010113.
Lemma F_81080 : fetch_word AsanUbsan.M.loaded_segments (0x810c8 : word) = Some W_81080.
Proof. vm_refl. Qed.
Lemma D_81080 : decode_any W_81080 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_81084 : bv 32 := 0x7e813083.
Lemma F_81084 : fetch_word AsanUbsan.M.loaded_segments (0x810cc : word) = Some W_81084.
Proof. vm_refl. Qed.
Lemma D_81084 : decode_any W_81084 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_81088 : bv 32 := 0x7e013403.
Lemma F_81088 : fetch_word AsanUbsan.M.loaded_segments (0x810d0 : word) = Some W_81088.
Proof. vm_refl. Qed.
Lemma D_81088 : decode_any W_81088 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8108c : bv 32 := 0x7d813483.
Lemma F_8108c : fetch_word AsanUbsan.M.loaded_segments (0x810d4 : word) = Some W_8108c.
Proof. vm_refl. Qed.
Lemma D_8108c : decode_any W_8108c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_81090 : bv 32 := 0x7d013903.
Lemma F_81090 : fetch_word AsanUbsan.M.loaded_segments (0x810d8 : word) = Some W_81090.
Proof. vm_refl. Qed.
Lemma D_81090 : decode_any W_81090 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_81094 : bv 32 := 0x7c813983.
Lemma F_81094 : fetch_word AsanUbsan.M.loaded_segments (0x810dc : word) = Some W_81094.
Proof. vm_refl. Qed.
Lemma D_81094 : decode_any W_81094 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_81098 : bv 32 := 0x7c013a03.
Lemma F_81098 : fetch_word AsanUbsan.M.loaded_segments (0x810e0 : word) = Some W_81098.
Proof. vm_refl. Qed.
Lemma D_81098 : decode_any W_81098 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_8109c : bv 32 := 0x7b813a83.
Lemma F_8109c : fetch_word AsanUbsan.M.loaded_segments (0x810e4 : word) = Some W_8109c.
Proof. vm_refl. Qed.
Lemma D_8109c : decode_any W_8109c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_810a0 : bv 32 := 0x7f010113.
Lemma F_810a0 : fetch_word AsanUbsan.M.loaded_segments (0x810e8 : word) = Some W_810a0.
Proof. vm_refl. Qed.
Lemma D_810a0 : decode_any W_810a0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_810a4 : bv 32 := 0x00008067.
Lemma F_810a4 : fetch_word AsanUbsan.M.loaded_segments (0x810ec : word) = Some W_810a4.
Proof. vm_refl. Qed.
Lemma D_810a4 : decode_any W_810a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_814b8 : bv 32 := 0x81010113.
Lemma F_814b8 : fetch_word AsanUbsan.M.loaded_segments (0x81500 : word) = Some W_814b8.
Proof. vm_refl. Qed.
Lemma D_814b8 : decode_any W_814b8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_814bc : bv 32 := 0x7e113423.
Lemma F_814bc : fetch_word AsanUbsan.M.loaded_segments (0x81504 : word) = Some W_814bc.
Proof. vm_refl. Qed.
Lemma D_814bc : decode_any W_814bc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_814c0 : bv 32 := 0x7e813023.
Lemma F_814c0 : fetch_word AsanUbsan.M.loaded_segments (0x81508 : word) = Some W_814c0.
Proof. vm_refl. Qed.
Lemma D_814c0 : decode_any W_814c0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_814c4 : bv 32 := 0x7c913c23.
Lemma F_814c4 : fetch_word AsanUbsan.M.loaded_segments (0x8150c : word) = Some W_814c4.
Proof. vm_refl. Qed.
Lemma D_814c4 : decode_any W_814c4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_814c8 : bv 32 := 0x7d213823.
Lemma F_814c8 : fetch_word AsanUbsan.M.loaded_segments (0x81510 : word) = Some W_814c8.
Proof. vm_refl. Qed.
Lemma D_814c8 : decode_any W_814c8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_814cc : bv 32 := 0x7d313423.
Lemma F_814cc : fetch_word AsanUbsan.M.loaded_segments (0x81514 : word) = Some W_814cc.
Proof. vm_refl. Qed.
Lemma D_814cc : decode_any W_814cc = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_814d0 : bv 32 := 0x7d413023.
Lemma F_814d0 : fetch_word AsanUbsan.M.loaded_segments (0x81518 : word) = Some W_814d0.
Proof. vm_refl. Qed.
Lemma D_814d0 : decode_any W_814d0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_814d4 : bv 32 := 0x7b513c23.
Lemma F_814d4 : fetch_word AsanUbsan.M.loaded_segments (0x8151c : word) = Some W_814d4.
Proof. vm_refl. Qed.
Lemma D_814d4 : decode_any W_814d4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_814d8 : bv 32 := 0x7b613823.
Lemma F_814d8 : fetch_word AsanUbsan.M.loaded_segments (0x81520 : word) = Some W_814d8.
Proof. vm_refl. Qed.
Lemma D_814d8 : decode_any W_814d8 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_814dc : bv 32 := 0x7f010413.
Lemma F_814dc : fetch_word AsanUbsan.M.loaded_segments (0x81524 : word) = Some W_814dc.
Proof. vm_refl. Qed.
Lemma D_814dc : decode_any W_814dc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_814e0 : bv 32 := 0xf9010113.
Lemma F_814e0 : fetch_word AsanUbsan.M.loaded_segments (0x81528 : word) = Some W_814e0.
Proof. vm_refl. Qed.
Lemma D_814e0 : decode_any W_814e0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_814e4 : bv 32 := 0x00008993.
Lemma F_814e4 : fetch_word AsanUbsan.M.loaded_segments (0x8152c : word) = Some W_814e4.
Proof. vm_refl. Qed.
Lemma D_814e4 : decode_any W_814e4 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_814e8 : bv 32 := 0x00058493.
Lemma F_814e8 : fetch_word AsanUbsan.M.loaded_segments (0x81530 : word) = Some W_814e8.
Proof. vm_refl. Qed.
Lemma D_814e8 : decode_any W_814e8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_814ec : bv 32 := 0x00050913.
Lemma F_814ec : fetch_word AsanUbsan.M.loaded_segments (0x81534 : word) = Some W_814ec.
Proof. vm_refl. Qed.
Lemma D_814ec : decode_any W_814ec = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_814f0 : bv 32 := 0x80040a93.
Lemma F_814f0 : fetch_word AsanUbsan.M.loaded_segments (0x81538 : word) = Some W_814f0.
Proof. vm_refl. Qed.
Lemma D_814f0 : decode_any W_814f0 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_814f4 : bv 32 := 0xfa8a8a93.
Lemma F_814f4 : fetch_word AsanUbsan.M.loaded_segments (0x8153c : word) = Some W_814f4.
Proof. vm_refl. Qed.
Lemma D_814f4 : decode_any W_814f4 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_814f8 : bv 32 := 0x80040513.
Lemma F_814f8 : fetch_word AsanUbsan.M.loaded_segments (0x81540 : word) = Some W_814f8.
Proof. vm_refl. Qed.
Lemma D_814f8 : decode_any W_814f8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_814fc : bv 32 := 0xfb850513.
Lemma F_814fc : fetch_word AsanUbsan.M.loaded_segments (0x81544 : word) = Some W_814fc.
Proof. vm_refl. Qed.
Lemma D_814fc : decode_any W_814fc = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_81500 : bv 32 := 0x7ffa8b13.
Lemma F_81500 : fetch_word AsanUbsan.M.loaded_segments (0x81548 : word) = Some W_81500.
Proof. vm_refl. Qed.
Lemma D_81500 : decode_any W_81500 = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_81504 : bv 32 := 0x000b34a3.
Lemma F_81504 : fetch_word AsanUbsan.M.loaded_segments (0x8154c : word) = Some W_81504.
Proof. vm_refl. Qed.
Lemma D_81504 : decode_any W_81504 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_81508 : bv 32 := 0x00aab023.
Lemma F_81508 : fetch_word AsanUbsan.M.loaded_segments (0x81550 : word) = Some W_81508.
Proof. vm_refl. Qed.
Lemma D_81508 : decode_any W_81508 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8150c : bv 32 := 0x000ab423.
Lemma F_8150c : fetch_word AsanUbsan.M.loaded_segments (0x81554 : word) = Some W_8150c.
Proof. vm_refl. Qed.
Lemma D_8150c : decode_any W_8150c = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81510 : bv 32 := 0x6b5070ef.
Lemma F_81510 : fetch_word AsanUbsan.M.loaded_segments (0x81558 : word) = Some W_81510.
Proof. vm_refl. Qed.
Lemma D_81510 : decode_any W_81510 = Some (Jal 1 32436, 4%Z).
Proof. vm_refl. Qed.

Definition W_81514 : bv 32 := 0x00200593.
Lemma F_81514 : fetch_word AsanUbsan.M.loaded_segments (0x8155c : word) = Some W_81514.
Proof. vm_refl. Qed.
Lemma D_81514 : decode_any W_81514 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_81518 : bv 32 := 0x02a5ea63.
Lemma F_81518 : fetch_word AsanUbsan.M.loaded_segments (0x81560 : word) = Some W_81518.
Proof. vm_refl. Qed.
Lemma D_81518 : decode_any W_81518 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_8154c : bv 32 := 0x155200ef.
Lemma F_8154c : fetch_word AsanUbsan.M.loaded_segments (0x81594 : word) = Some W_8154c.
Proof. vm_refl. Qed.
Lemma D_8154c : decode_any W_8154c = Some (Jal 1 133460, 4%Z).
Proof. vm_refl. Qed.

Definition W_81550 : bv 32 := 0x000d3597.
Lemma F_81550 : fetch_word AsanUbsan.M.loaded_segments (0x81598 : word) = Some W_81550.
Proof. vm_refl. Qed.
Lemma D_81550 : decode_any W_81550 = Some (Auipc 11 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_81554 : bv 32 := 0xf585b583.
Lemma F_81554 : fetch_word AsanUbsan.M.loaded_segments (0x8159c : word) = Some W_81554.
Proof. vm_refl. Qed.
Lemma D_81554 : decode_any W_81554 = Some (Load SZ8 true 11 11 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_81558 : bv 32 := 0x0225ca03.
Lemma F_81558 : fetch_word AsanUbsan.M.loaded_segments (0x815a0 : word) = Some W_81558.
Proof. vm_refl. Qed.
Lemma D_81558 : decode_any W_81558 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_8155c : bv 32 := 0x00050993.
Lemma F_8155c : fetch_word AsanUbsan.M.loaded_segments (0x815a4 : word) = Some W_8155c.
Proof. vm_refl. Qed.
Lemma D_8155c : decode_any W_8155c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81560 : bv 32 := 0x665070ef.
Lemma F_81560 : fetch_word AsanUbsan.M.loaded_segments (0x815a8 : word) = Some W_81560.
Proof. vm_refl. Qed.
Lemma D_81560 : decode_any W_81560 = Some (Jal 1 32356, 4%Z).
Proof. vm_refl. Qed.

Definition W_81564 : bv 32 := 0x00050793.
Lemma F_81564 : fetch_word AsanUbsan.M.loaded_segments (0x815ac : word) = Some W_81564.
Proof. vm_refl. Qed.
Lemma D_81564 : decode_any W_81564 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81568 : bv 32 := 0x00153513.
Lemma F_81568 : fetch_word AsanUbsan.M.loaded_segments (0x815b0 : word) = Some W_81568.
Proof. vm_refl. Qed.
Lemma D_81568 : decode_any W_81568 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8156c : bv 32 := 0xfff50513.
Lemma F_8156c : fetch_word AsanUbsan.M.loaded_segments (0x815b4 : word) = Some W_8156c.
Proof. vm_refl. Qed.
Lemma D_8156c : decode_any W_8156c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_81570 : bv 32 := 0x008575b3.
Lemma F_81570 : fetch_word AsanUbsan.M.loaded_segments (0x815b8 : word) = Some W_81570.
Proof. vm_refl. Qed.
Lemma D_81570 : decode_any W_81570 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81574 : bv 32 := 0x00100513.
Lemma F_81574 : fetch_word AsanUbsan.M.loaded_segments (0x815bc : word) = Some W_81574.
Proof. vm_refl. Qed.
Lemma D_81574 : decode_any W_81574 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81578 : bv 32 := 0x00bb34a3.
Lemma F_81578 : fetch_word AsanUbsan.M.loaded_segments (0x815c0 : word) = Some W_81578.
Proof. vm_refl. Qed.
Lemma D_81578 : decode_any W_81578 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_8157c : bv 32 := 0x00f56a63.
Lemma F_8157c : fetch_word AsanUbsan.M.loaded_segments (0x815c4 : word) = Some W_8157c.
Proof. vm_refl. Qed.
Lemma D_8157c : decode_any W_8157c = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_81590 : bv 32 := 0x80040513.
Lemma F_81590 : fetch_word AsanUbsan.M.loaded_segments (0x815d8 : word) = Some W_81590.
Proof. vm_refl. Qed.
Lemma D_81590 : decode_any W_81590 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_81594 : bv 32 := 0xfa850513.
Lemma F_81594 : fetch_word AsanUbsan.M.loaded_segments (0x815dc : word) = Some W_81594.
Proof. vm_refl. Qed.
Lemma D_81594 : decode_any W_81594 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_81598 : bv 32 := 0x00098593.
Lemma F_81598 : fetch_word AsanUbsan.M.loaded_segments (0x815e0 : word) = Some W_81598.
Proof. vm_refl. Qed.
Lemma D_81598 : decode_any W_81598 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8159c : bv 32 := 0x00040613.
Lemma F_8159c : fetch_word AsanUbsan.M.loaded_segments (0x815e4 : word) = Some W_8159c.
Proof. vm_refl. Qed.
Lemma D_8159c : decode_any W_8159c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_815a0 : bv 32 := 0x00000693.
Lemma F_815a0 : fetch_word AsanUbsan.M.loaded_segments (0x815e8 : word) = Some W_815a0.
Proof. vm_refl. Qed.
Lemma D_815a0 : decode_any W_815a0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_815a4 : bv 32 := 0x000a0713.
Lemma F_815a4 : fetch_word AsanUbsan.M.loaded_segments (0x815ec : word) = Some W_815a4.
Proof. vm_refl. Qed.
Lemma D_815a4 : decode_any W_815a4 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_815a8 : bv 32 := 0x62d070ef.
Lemma F_815a8 : fetch_word AsanUbsan.M.loaded_segments (0x815f0 : word) = Some W_815a8.
Proof. vm_refl. Qed.
Lemma D_815a8 : decode_any W_815a8 = Some (Jal 1 32300, 4%Z).
Proof. vm_refl. Qed.

Definition W_815ac : bv 32 := 0x80040613.
Lemma F_815ac : fetch_word AsanUbsan.M.loaded_segments (0x815f4 : word) = Some W_815ac.
Proof. vm_refl. Qed.
Lemma D_815ac : decode_any W_815ac = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_815b0 : bv 32 := 0xfa860613.
Lemma F_815b0 : fetch_word AsanUbsan.M.loaded_segments (0x815f8 : word) = Some W_815b0.
Proof. vm_refl. Qed.
Lemma D_815b0 : decode_any W_815b0 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_815b4 : bv 32 := 0x00090513.
Lemma F_815b4 : fetch_word AsanUbsan.M.loaded_segments (0x815fc : word) = Some W_815b4.
Proof. vm_refl. Qed.
Lemma D_815b4 : decode_any W_815b4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_815b8 : bv 32 := 0x00048593.
Lemma F_815b8 : fetch_word AsanUbsan.M.loaded_segments (0x81600 : word) = Some W_815b8.
Proof. vm_refl. Qed.
Lemma D_815b8 : decode_any W_815b8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_815bc : bv 32 := 0xdadd80ef.
Lemma F_815bc : fetch_word AsanUbsan.M.loaded_segments (0x81604 : word) = Some W_815bc.
Proof. vm_refl. Qed.
Lemma D_815bc : decode_any W_815bc = Some (Jal 1 1936812, 4%Z).
Proof. vm_refl. Qed.

Definition W_815c0 : bv 32 := 0x07010113.
Lemma F_815c0 : fetch_word AsanUbsan.M.loaded_segments (0x81608 : word) = Some W_815c0.
Proof. vm_refl. Qed.
Lemma D_815c0 : decode_any W_815c0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_815c4 : bv 32 := 0x7e813083.
Lemma F_815c4 : fetch_word AsanUbsan.M.loaded_segments (0x8160c : word) = Some W_815c4.
Proof. vm_refl. Qed.
Lemma D_815c4 : decode_any W_815c4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_815c8 : bv 32 := 0x7e013403.
Lemma F_815c8 : fetch_word AsanUbsan.M.loaded_segments (0x81610 : word) = Some W_815c8.
Proof. vm_refl. Qed.
Lemma D_815c8 : decode_any W_815c8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_815cc : bv 32 := 0x7d813483.
Lemma F_815cc : fetch_word AsanUbsan.M.loaded_segments (0x81614 : word) = Some W_815cc.
Proof. vm_refl. Qed.
Lemma D_815cc : decode_any W_815cc = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_815d0 : bv 32 := 0x7d013903.
Lemma F_815d0 : fetch_word AsanUbsan.M.loaded_segments (0x81618 : word) = Some W_815d0.
Proof. vm_refl. Qed.
Lemma D_815d0 : decode_any W_815d0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_815d4 : bv 32 := 0x7c813983.
Lemma F_815d4 : fetch_word AsanUbsan.M.loaded_segments (0x8161c : word) = Some W_815d4.
Proof. vm_refl. Qed.
Lemma D_815d4 : decode_any W_815d4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_815d8 : bv 32 := 0x7c013a03.
Lemma F_815d8 : fetch_word AsanUbsan.M.loaded_segments (0x81620 : word) = Some W_815d8.
Proof. vm_refl. Qed.
Lemma D_815d8 : decode_any W_815d8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_815dc : bv 32 := 0x7b813a83.
Lemma F_815dc : fetch_word AsanUbsan.M.loaded_segments (0x81624 : word) = Some W_815dc.
Proof. vm_refl. Qed.
Lemma D_815dc : decode_any W_815dc = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_815e0 : bv 32 := 0x7b013b03.
Lemma F_815e0 : fetch_word AsanUbsan.M.loaded_segments (0x81628 : word) = Some W_815e0.
Proof. vm_refl. Qed.
Lemma D_815e0 : decode_any W_815e0 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_815e4 : bv 32 := 0x7f010113.
Lemma F_815e4 : fetch_word AsanUbsan.M.loaded_segments (0x8162c : word) = Some W_815e4.
Proof. vm_refl. Qed.
Lemma D_815e4 : decode_any W_815e4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_815e8 : bv 32 := 0x00008067.
Lemma F_815e8 : fetch_word AsanUbsan.M.loaded_segments (0x81630 : word) = Some W_815e8.
Proof. vm_refl. Qed.
Lemma D_815e8 : decode_any W_815e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

