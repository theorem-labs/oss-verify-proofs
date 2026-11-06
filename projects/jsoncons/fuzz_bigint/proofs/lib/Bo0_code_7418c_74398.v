(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7418c : bv 32 := 0xef010113.
Lemma F_7418c : fetch_word AsanUbsan.M.loaded_segments (0x7418c : word) = Some W_7418c.
Proof. vm_refl. Qed.
Lemma D_7418c : decode_any W_7418c = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_74190 : bv 32 := 0x10113423.
Lemma F_74190 : fetch_word AsanUbsan.M.loaded_segments (0x74190 : word) = Some W_74190.
Proof. vm_refl. Qed.
Lemma D_74190 : decode_any W_74190 = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_74194 : bv 32 := 0x10813023.
Lemma F_74194 : fetch_word AsanUbsan.M.loaded_segments (0x74194 : word) = Some W_74194.
Proof. vm_refl. Qed.
Lemma D_74194 : decode_any W_74194 = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_74198 : bv 32 := 0x0e913c23.
Lemma F_74198 : fetch_word AsanUbsan.M.loaded_segments (0x74198 : word) = Some W_74198.
Proof. vm_refl. Qed.
Lemma D_74198 : decode_any W_74198 = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_7419c : bv 32 := 0x0f213823.
Lemma F_7419c : fetch_word AsanUbsan.M.loaded_segments (0x7419c : word) = Some W_7419c.
Proof. vm_refl. Qed.
Lemma D_7419c : decode_any W_7419c = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_741a0 : bv 32 := 0x0f313423.
Lemma F_741a0 : fetch_word AsanUbsan.M.loaded_segments (0x741a0 : word) = Some W_741a0.
Proof. vm_refl. Qed.
Lemma D_741a0 : decode_any W_741a0 = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_741a4 : bv 32 := 0x0f413023.
Lemma F_741a4 : fetch_word AsanUbsan.M.loaded_segments (0x741a4 : word) = Some W_741a4.
Proof. vm_refl. Qed.
Lemma D_741a4 : decode_any W_741a4 = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_741a8 : bv 32 := 0x0d513c23.
Lemma F_741a8 : fetch_word AsanUbsan.M.loaded_segments (0x741a8 : word) = Some W_741a8.
Proof. vm_refl. Qed.
Lemma D_741a8 : decode_any W_741a8 = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_741ac : bv 32 := 0x00050913.
Lemma F_741ac : fetch_word AsanUbsan.M.loaded_segments (0x741ac : word) = Some W_741ac.
Proof. vm_refl. Qed.
Lemma D_741ac : decode_any W_741ac = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_741b0 : bv 32 := 0xfff00513.
Lemma F_741b0 : fetch_word AsanUbsan.M.loaded_segments (0x741b0 : word) = Some W_741b0.
Proof. vm_refl. Qed.
Lemma D_741b0 : decode_any W_741b0 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_741b4 : bv 32 := 0x12090463.
Lemma F_741b4 : fetch_word AsanUbsan.M.loaded_segments (0x741b4 : word) = Some W_741b4.
Proof. vm_refl. Qed.
Lemma D_741b4 : decode_any W_741b4 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_741b8 : bv 32 := 0x00060413.
Lemma F_741b8 : fetch_word AsanUbsan.M.loaded_segments (0x741b8 : word) = Some W_741b8.
Proof. vm_refl. Qed.
Lemma D_741b8 : decode_any W_741b8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_741bc : bv 32 := 0x00062617.
Lemma F_741bc : fetch_word AsanUbsan.M.loaded_segments (0x741bc : word) = Some W_741bc.
Proof. vm_refl. Qed.
Lemma D_741bc : decode_any W_741bc = Some (Auipc 12 98, 4%Z).
Proof. vm_refl. Qed.

Definition W_741c0 : bv 32 := 0x2fc63603.
Lemma F_741c0 : fetch_word AsanUbsan.M.loaded_segments (0x741c0 : word) = Some W_741c0.
Proof. vm_refl. Qed.
Lemma D_741c0 : decode_any W_741c0 = Some (Load SZ8 true 12 12 764, 4%Z).
Proof. vm_refl. Qed.

Definition W_741c4 : bv 32 := 0x10464603.
Lemma F_741c4 : fetch_word AsanUbsan.M.loaded_segments (0x741c4 : word) = Some W_741c4.
Proof. vm_refl. Qed.
Lemma D_741c4 : decode_any W_741c4 = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_741c8 : bv 32 := 0x00167613.
Lemma F_741c8 : fetch_word AsanUbsan.M.loaded_segments (0x741c8 : word) = Some W_741c8.
Proof. vm_refl. Qed.
Lemma D_741c8 : decode_any W_741c8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_741cc : bv 32 := 0x10060863.
Lemma F_741cc : fetch_word AsanUbsan.M.loaded_segments (0x741cc : word) = Some W_741cc.
Proof. vm_refl. Qed.
Lemma D_741cc : decode_any W_741cc = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_741d0 : bv 32 := 0x00058493.
Lemma F_741d0 : fetch_word AsanUbsan.M.loaded_segments (0x741d0 : word) = Some W_741d0.
Proof. vm_refl. Qed.
Lemma D_741d0 : decode_any W_741d0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_741d4 : bv 32 := 0x00d10513.
Lemma F_741d4 : fetch_word AsanUbsan.M.loaded_segments (0x741d4 : word) = Some W_741d4.
Proof. vm_refl. Qed.
Lemma D_741d4 : decode_any W_741d4 = Some (OpImm ALU_ADD 10 2 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_741d8 : bv 32 := 0x0aa00593.
Lemma F_741d8 : fetch_word AsanUbsan.M.loaded_segments (0x741d8 : word) = Some W_741d8.
Proof. vm_refl. Qed.
Lemma D_741d8 : decode_any W_741d8 = Some (OpImm ALU_ADD 11 0 170, 4%Z).
Proof. vm_refl. Qed.

Definition W_741dc : bv 32 := 0x0c800613.
Lemma F_741dc : fetch_word AsanUbsan.M.loaded_segments (0x741dc : word) = Some W_741dc.
Proof. vm_refl. Qed.
Lemma D_741dc : decode_any W_741dc = Some (OpImm ALU_ADD 12 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_741e0 : bv 32 := 0xc00fd0ef.
Lemma F_741e0 : fetch_word AsanUbsan.M.loaded_segments (0x741e0 : word) = Some W_741e0.
Proof. vm_refl. Qed.
Lemma D_741e0 : decode_any W_741e0 = Some (Jal 1 2085888, 4%Z).
Proof. vm_refl. Qed.

Definition W_741e4 : bv 32 := 0x00090513.
Lemma F_741e4 : fetch_word AsanUbsan.M.loaded_segments (0x741e4 : word) = Some W_741e4.
Proof. vm_refl. Qed.
Lemma D_741e4 : decode_any W_741e4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_741e8 : bv 32 := 0xd4cfd0ef.
Lemma F_741e8 : fetch_word AsanUbsan.M.loaded_segments (0x741e8 : word) = Some W_741e8.
Proof. vm_refl. Qed.
Lemma D_741e8 : decode_any W_741e8 = Some (Jal 1 2086220, 4%Z).
Proof. vm_refl. Qed.

Definition W_741ec : bv 32 := 0x0be00593.
Lemma F_741ec : fetch_word AsanUbsan.M.loaded_segments (0x741ec : word) = Some W_741ec.
Proof. vm_refl. Qed.
Lemma D_741ec : decode_any W_741ec = Some (OpImm ALU_ADD 11 0 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_741f0 : bv 32 := 0x14b57463.
Lemma F_741f0 : fetch_word AsanUbsan.M.loaded_segments (0x741f0 : word) = Some W_741f0.
Proof. vm_refl. Qed.
Lemma D_741f0 : decode_any W_741f0 = Some (Branch BC_GEU 10 11 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_741f4 : bv 32 := 0x94cfe0ef.
Lemma F_741f4 : fetch_word AsanUbsan.M.loaded_segments (0x741f4 : word) = Some W_741f4.
Proof. vm_refl. Qed.
Lemma D_741f4 : decode_any W_741f4 = Some (Jal 1 2089292, 4%Z).
Proof. vm_refl. Qed.

Definition W_741f8 : bv 32 := 0x00050693.
Lemma F_741f8 : fetch_word AsanUbsan.M.loaded_segments (0x741f8 : word) = Some W_741f8.
Proof. vm_refl. Qed.
Lemma D_741f8 : decode_any W_741f8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_741fc : bv 32 := 0xfffae597.
Lemma F_741fc : fetch_word AsanUbsan.M.loaded_segments (0x741fc : word) = Some W_741fc.
Proof. vm_refl. Qed.
Lemma D_741fc : decode_any W_741fc = Some (Auipc 11 1048494, 4%Z).
Proof. vm_refl. Qed.

Definition W_74200 : bv 32 := 0x00d10513.
Lemma F_74200 : fetch_word AsanUbsan.M.loaded_segments (0x74200 : word) = Some W_74200.
Proof. vm_refl. Qed.
Lemma D_74200 : decode_any W_74200 = Some (OpImm ALU_ADD 10 2 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_74204 : bv 32 := 0xc0c58613.
Lemma F_74204 : fetch_word AsanUbsan.M.loaded_segments (0x74204 : word) = Some W_74204.
Proof. vm_refl. Qed.
Lemma D_74204 : decode_any W_74204 = Some (OpImm ALU_ADD 12 11 3084, 4%Z).
Proof. vm_refl. Qed.

Definition W_74208 : bv 32 := 0x0c800593.
Lemma F_74208 : fetch_word AsanUbsan.M.loaded_segments (0x74208 : word) = Some W_74208.
Proof. vm_refl. Qed.
Lemma D_74208 : decode_any W_74208 = Some (OpImm ALU_ADD 11 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7420c : bv 32 := 0x00090713.
Lemma F_7420c : fetch_word AsanUbsan.M.loaded_segments (0x7420c : word) = Some W_7420c.
Proof. vm_refl. Qed.
Lemma D_7420c : decode_any W_7420c = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74210 : bv 32 := 0x045000ef.
Lemma F_74210 : fetch_word AsanUbsan.M.loaded_segments (0x74210 : word) = Some W_74210.
Proof. vm_refl. Qed.
Lemma D_74210 : decode_any W_74210 = Some (Jal 1 2116, 4%Z).
Proof. vm_refl. Qed.

Definition W_74214 : bv 32 := 0x000805b7.
Lemma F_74214 : fetch_word AsanUbsan.M.loaded_segments (0x74214 : word) = Some W_74214.
Proof. vm_refl. Qed.
Lemma D_74214 : decode_any W_74214 = Some (Lui 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_74218 : bv 32 := 0x00d10513.
Lemma F_74218 : fetch_word AsanUbsan.M.loaded_segments (0x74218 : word) = Some W_74218.
Proof. vm_refl. Qed.
Lemma D_74218 : decode_any W_74218 = Some (OpImm ALU_ADD 10 2 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7421c : bv 32 := 0x2425859b.
Lemma F_7421c : fetch_word AsanUbsan.M.loaded_segments (0x7421c : word) = Some W_7421c.
Proof. vm_refl. Qed.
Lemma D_7421c : decode_any W_7421c = Some (OpImm32 11 11 578, 4%Z).
Proof. vm_refl. Qed.

Definition W_74220 : bv 32 := 0x1c000613.
Lemma F_74220 : fetch_word AsanUbsan.M.loaded_segments (0x74220 : word) = Some W_74220.
Proof. vm_refl. Qed.
Lemma D_74220 : decode_any W_74220 = Some (OpImm ALU_ADD 12 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_74224 : bv 32 := 0xc1dfd0ef.
Lemma F_74224 : fetch_word AsanUbsan.M.loaded_segments (0x74224 : word) = Some W_74224.
Proof. vm_refl. Qed.
Lemma D_74224 : decode_any W_74224 = Some (Jal 1 2087964, 4%Z).
Proof. vm_refl. Qed.

Definition W_74228 : bv 32 := 0x00050913.
Lemma F_74228 : fetch_word AsanUbsan.M.loaded_segments (0x74228 : word) = Some W_74228.
Proof. vm_refl. Qed.
Lemma D_74228 : decode_any W_74228 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7422c : bv 32 := 0x0005051b.
Lemma F_7422c : fetch_word AsanUbsan.M.loaded_segments (0x7422c : word) = Some W_7422c.
Proof. vm_refl. Qed.
Lemma D_7422c : decode_any W_7422c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74230 : bv 32 := 0x00200593.
Lemma F_74230 : fetch_word AsanUbsan.M.loaded_segments (0x74230 : word) = Some W_74230.
Proof. vm_refl. Qed.
Lemma D_74230 : decode_any W_74230 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_74234 : bv 32 := 0x06a5c863.
Lemma F_74234 : fetch_word AsanUbsan.M.loaded_segments (0x74234 : word) = Some W_74234.
Proof. vm_refl. Qed.
Lemma D_74234 : decode_any W_74234 = Some (Branch BC_LT 11 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_74238 : bv 32 := 0x0aa00513.
Lemma F_74238 : fetch_word AsanUbsan.M.loaded_segments (0x74238 : word) = Some W_74238.
Proof. vm_refl. Qed.
Lemma D_74238 : decode_any W_74238 = Some (OpImm ALU_ADD 10 0 170, 4%Z).
Proof. vm_refl. Qed.

Definition W_7423c : bv 32 := 0x0ca10aa3.
Lemma F_7423c : fetch_word AsanUbsan.M.loaded_segments (0x7423c : word) = Some W_7423c.
Proof. vm_refl. Qed.
Lemma D_7423c : decode_any W_7423c = Some (Store SZ1 2 10 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_74240 : bv 32 := 0x0ca10b23.
Lemma F_74240 : fetch_word AsanUbsan.M.loaded_segments (0x74240 : word) = Some W_74240.
Proof. vm_refl. Qed.
Lemma D_74240 : decode_any W_74240 = Some (Store SZ1 2 10 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_74244 : bv 32 := 0x0ca10ba3.
Lemma F_74244 : fetch_word AsanUbsan.M.loaded_segments (0x74244 : word) = Some W_74244.
Proof. vm_refl. Qed.
Lemma D_74244 : decode_any W_74244 = Some (Store SZ1 2 10 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_74248 : bv 32 := 0x0d510993.
Lemma F_74248 : fetch_word AsanUbsan.M.loaded_segments (0x74248 : word) = Some W_74248.
Proof. vm_refl. Qed.
Lemma D_74248 : decode_any W_74248 = Some (OpImm ALU_ADD 19 2 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_7424c : bv 32 := 0x0d510513.
Lemma F_7424c : fetch_word AsanUbsan.M.loaded_segments (0x7424c : word) = Some W_7424c.
Proof. vm_refl. Qed.
Lemma D_7424c : decode_any W_7424c = Some (OpImm ALU_ADD 10 2 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_74250 : bv 32 := 0x00300613.
Lemma F_74250 : fetch_word AsanUbsan.M.loaded_segments (0x74250 : word) = Some W_74250.
Proof. vm_refl. Qed.
Lemma D_74250 : decode_any W_74250 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_74254 : bv 32 := 0x00300a13.
Lemma F_74254 : fetch_word AsanUbsan.M.loaded_segments (0x74254 : word) = Some W_74254.
Proof. vm_refl. Qed.
Lemma D_74254 : decode_any W_74254 = Some (OpImm ALU_ADD 20 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_74258 : bv 32 := 0x00000593.
Lemma F_74258 : fetch_word AsanUbsan.M.loaded_segments (0x74258 : word) = Some W_74258.
Proof. vm_refl. Qed.
Lemma D_74258 : decode_any W_74258 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7425c : bv 32 := 0xb84fd0ef.
Lemma F_7425c : fetch_word AsanUbsan.M.loaded_segments (0x7425c : word) = Some W_7425c.
Proof. vm_refl. Qed.
Lemma D_7425c : decode_any W_7425c = Some (Jal 1 2085764, 4%Z).
Proof. vm_refl. Qed.

Definition W_74260 : bv 32 := 0x00100a93.
Lemma F_74260 : fetch_word AsanUbsan.M.loaded_segments (0x74260 : word) = Some W_74260.
Proof. vm_refl. Qed.
Lemma D_74260 : decode_any W_74260 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_74264 : bv 32 := 0x0009051b.
Lemma F_74264 : fetch_word AsanUbsan.M.loaded_segments (0x74264 : word) = Some W_74264.
Proof. vm_refl. Qed.
Lemma D_74264 : decode_any W_74264 = Some (OpImm32 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74268 : bv 32 := 0x00a985b3.
Lemma F_74268 : fetch_word AsanUbsan.M.loaded_segments (0x74268 : word) = Some W_74268.
Proof. vm_refl. Qed.
Lemma D_74268 : decode_any W_74268 = Some (Op ALU_ADD 11 19 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7426c : bv 32 := 0x01558023.
Lemma F_7426c : fetch_word AsanUbsan.M.loaded_segments (0x7426c : word) = Some W_7426c.
Proof. vm_refl. Qed.
Lemma D_7426c : decode_any W_7426c = Some (Store SZ1 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74270 : bv 32 := 0xc9dfd0ef.
Lemma F_74270 : fetch_word AsanUbsan.M.loaded_segments (0x74270 : word) = Some W_74270.
Proof. vm_refl. Qed.
Lemma D_74270 : decode_any W_74270 = Some (Jal 1 2088092, 4%Z).
Proof. vm_refl. Qed.

Definition W_74274 : bv 32 := 0x0005091b.
Lemma F_74274 : fetch_word AsanUbsan.M.loaded_segments (0x74274 : word) = Some W_74274.
Proof. vm_refl. Qed.
Lemma D_74274 : decode_any W_74274 = Some (OpImm32 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74278 : bv 32 := 0xff4946e3.
Lemma F_74278 : fetch_word AsanUbsan.M.loaded_segments (0x74278 : word) = Some W_74278.
Proof. vm_refl. Qed.
Lemma D_74278 : decode_any W_74278 = Some (Branch BC_LT 18 20 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_7427c : bv 32 := 0x0d514583.
Lemma F_7427c : fetch_word AsanUbsan.M.loaded_segments (0x7427c : word) = Some W_7427c.
Proof. vm_refl. Qed.
Lemma D_7427c : decode_any W_7427c = Some (Load SZ1 false 11 2 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_74280 : bv 32 := 0x08059263.
Lemma F_74280 : fetch_word AsanUbsan.M.loaded_segments (0x74280 : word) = Some W_74280.
Proof. vm_refl. Qed.
Lemma D_74280 : decode_any W_74280 = Some (Branch BC_NE 11 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_74284 : bv 32 := 0x0d614583.
Lemma F_74284 : fetch_word AsanUbsan.M.loaded_segments (0x74284 : word) = Some W_74284.
Proof. vm_refl. Qed.
Lemma D_74284 : decode_any W_74284 = Some (Load SZ1 false 11 2 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_74288 : bv 32 := 0x08059a63.
Lemma F_74288 : fetch_word AsanUbsan.M.loaded_segments (0x74288 : word) = Some W_74288.
Proof. vm_refl. Qed.
Lemma D_74288 : decode_any W_74288 = Some (Branch BC_NE 11 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7428c : bv 32 := 0x0d714583.
Lemma F_7428c : fetch_word AsanUbsan.M.loaded_segments (0x7428c : word) = Some W_7428c.
Proof. vm_refl. Qed.
Lemma D_7428c : decode_any W_7428c = Some (Load SZ1 false 11 2 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_74290 : bv 32 := 0x00058a63.
Lemma F_74290 : fetch_word AsanUbsan.M.loaded_segments (0x74290 : word) = Some W_74290.
Proof. vm_refl. Qed.
Lemma D_74290 : decode_any W_74290 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_74294 : bv 32 := 0x00050913.
Lemma F_74294 : fetch_word AsanUbsan.M.loaded_segments (0x74294 : word) = Some W_74294.
Proof. vm_refl. Qed.
Lemma D_74294 : decode_any W_74294 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74298 : bv 32 := 0x00200513.
Lemma F_74298 : fetch_word AsanUbsan.M.loaded_segments (0x74298 : word) = Some W_74298.
Proof. vm_refl. Qed.
Lemma D_74298 : decode_any W_74298 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7429c : bv 32 := 0xb99fd0ef.
Lemma F_7429c : fetch_word AsanUbsan.M.loaded_segments (0x7429c : word) = Some W_7429c.
Proof. vm_refl. Qed.
Lemma D_7429c : decode_any W_7429c = Some (Jal 1 2087832, 4%Z).
Proof. vm_refl. Qed.

Definition W_742a0 : bv 32 := 0x00090513.
Lemma F_742a0 : fetch_word AsanUbsan.M.loaded_segments (0x742a0 : word) = Some W_742a0.
Proof. vm_refl. Qed.
Lemma D_742a0 : decode_any W_742a0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_742a4 : bv 32 := 0x00050913.
Lemma F_742a4 : fetch_word AsanUbsan.M.loaded_segments (0x742a4 : word) = Some W_742a4.
Proof. vm_refl. Qed.
Lemma D_742a4 : decode_any W_742a4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_742a8 : bv 32 := 0x0005051b.
Lemma F_742a8 : fetch_word AsanUbsan.M.loaded_segments (0x742a8 : word) = Some W_742a8.
Proof. vm_refl. Qed.
Lemma D_742a8 : decode_any W_742a8 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_742ac : bv 32 := 0x00048593.
Lemma F_742ac : fetch_word AsanUbsan.M.loaded_segments (0x742ac : word) = Some W_742ac.
Proof. vm_refl. Qed.
Lemma D_742ac : decode_any W_742ac = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_742b0 : bv 32 := 0xc25fd0ef.
Lemma F_742b0 : fetch_word AsanUbsan.M.loaded_segments (0x742b0 : word) = Some W_742b0.
Proof. vm_refl. Qed.
Lemma D_742b0 : decode_any W_742b0 = Some (Jal 1 2087972, 4%Z).
Proof. vm_refl. Qed.

Definition W_742b4 : bv 32 := 0x02051513.
Lemma F_742b4 : fetch_word AsanUbsan.M.loaded_segments (0x742b4 : word) = Some W_742b4.
Proof. vm_refl. Qed.
Lemma D_742b4 : decode_any W_742b4 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_742b8 : bv 32 := 0x0a051063.
Lemma F_742b8 : fetch_word AsanUbsan.M.loaded_segments (0x742b8 : word) = Some W_742b8.
Proof. vm_refl. Qed.
Lemma D_742b8 : decode_any W_742b8 = Some (Branch BC_NE 10 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_742bc : bv 32 := 0x00d10513.
Lemma F_742bc : fetch_word AsanUbsan.M.loaded_segments (0x742bc : word) = Some W_742bc.
Proof. vm_refl. Qed.
Lemma D_742bc : decode_any W_742bc = Some (OpImm ALU_ADD 10 2 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_742c0 : bv 32 := 0xc69fd0ef.
Lemma F_742c0 : fetch_word AsanUbsan.M.loaded_segments (0x742c0 : word) = Some W_742c0.
Proof. vm_refl. Qed.
Lemma D_742c0 : decode_any W_742c0 = Some (Jal 1 2088040, 4%Z).
Proof. vm_refl. Qed.

Definition W_742c4 : bv 32 := 0x02051513.
Lemma F_742c4 : fetch_word AsanUbsan.M.loaded_segments (0x742c4 : word) = Some W_742c4.
Proof. vm_refl. Qed.
Lemma D_742c4 : decode_any W_742c4 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_742c8 : bv 32 := 0x0a051863.
Lemma F_742c8 : fetch_word AsanUbsan.M.loaded_segments (0x742c8 : word) = Some W_742c8.
Proof. vm_refl. Qed.
Lemma D_742c8 : decode_any W_742c8 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_742cc : bv 32 := 0x00046503.
Lemma F_742cc : fetch_word AsanUbsan.M.loaded_segments (0x742cc : word) = Some W_742cc.
Proof. vm_refl. Qed.
Lemma D_742cc : decode_any W_742cc = Some (Load SZ4 false 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_742d0 : bv 32 := 0xfdf57513.
Lemma F_742d0 : fetch_word AsanUbsan.M.loaded_segments (0x742d0 : word) = Some W_742d0.
Proof. vm_refl. Qed.
Lemma D_742d0 : decode_any W_742d0 = Some (OpImm ALU_AND 10 10 4063, 4%Z).
Proof. vm_refl. Qed.

Definition W_742d4 : bv 32 := 0x00a42023.
Lemma F_742d4 : fetch_word AsanUbsan.M.loaded_segments (0x742d4 : word) = Some W_742d4.
Proof. vm_refl. Qed.
Lemma D_742d4 : decode_any W_742d4 = Some (Store SZ4 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_742d8 : bv 32 := 0x00090513.
Lemma F_742d8 : fetch_word AsanUbsan.M.loaded_segments (0x742d8 : word) = Some W_742d8.
Proof. vm_refl. Qed.
Lemma D_742d8 : decode_any W_742d8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_742dc : bv 32 := 0x0005051b.
Lemma F_742dc : fetch_word AsanUbsan.M.loaded_segments (0x742dc : word) = Some W_742dc.
Proof. vm_refl. Qed.
Lemma D_742dc : decode_any W_742dc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_742e0 : bv 32 := 0x10813083.
Lemma F_742e0 : fetch_word AsanUbsan.M.loaded_segments (0x742e0 : word) = Some W_742e0.
Proof. vm_refl. Qed.
Lemma D_742e0 : decode_any W_742e0 = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_742e4 : bv 32 := 0x10013403.
Lemma F_742e4 : fetch_word AsanUbsan.M.loaded_segments (0x742e4 : word) = Some W_742e4.
Proof. vm_refl. Qed.
Lemma D_742e4 : decode_any W_742e4 = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_742e8 : bv 32 := 0x0f813483.
Lemma F_742e8 : fetch_word AsanUbsan.M.loaded_segments (0x742e8 : word) = Some W_742e8.
Proof. vm_refl. Qed.
Lemma D_742e8 : decode_any W_742e8 = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_742ec : bv 32 := 0x0f013903.
Lemma F_742ec : fetch_word AsanUbsan.M.loaded_segments (0x742ec : word) = Some W_742ec.
Proof. vm_refl. Qed.
Lemma D_742ec : decode_any W_742ec = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_742f0 : bv 32 := 0x0e813983.
Lemma F_742f0 : fetch_word AsanUbsan.M.loaded_segments (0x742f0 : word) = Some W_742f0.
Proof. vm_refl. Qed.
Lemma D_742f0 : decode_any W_742f0 = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_742f4 : bv 32 := 0x0e013a03.
Lemma F_742f4 : fetch_word AsanUbsan.M.loaded_segments (0x742f4 : word) = Some W_742f4.
Proof. vm_refl. Qed.
Lemma D_742f4 : decode_any W_742f4 = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_742f8 : bv 32 := 0x0d813a83.
Lemma F_742f8 : fetch_word AsanUbsan.M.loaded_segments (0x742f8 : word) = Some W_742f8.
Proof. vm_refl. Qed.
Lemma D_742f8 : decode_any W_742f8 = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_742fc : bv 32 := 0x11010113.
Lemma F_742fc : fetch_word AsanUbsan.M.loaded_segments (0x742fc : word) = Some W_742fc.
Proof. vm_refl. Qed.
Lemma D_742fc : decode_any W_742fc = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_74300 : bv 32 := 0x00008067.
Lemma F_74300 : fetch_word AsanUbsan.M.loaded_segments (0x74300 : word) = Some W_74300.
Proof. vm_refl. Qed.
Lemma D_74300 : decode_any W_74300 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74304 : bv 32 := 0x00050913.
Lemma F_74304 : fetch_word AsanUbsan.M.loaded_segments (0x74304 : word) = Some W_74304.
Proof. vm_refl. Qed.
Lemma D_74304 : decode_any W_74304 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74308 : bv 32 := 0x00000513.
Lemma F_74308 : fetch_word AsanUbsan.M.loaded_segments (0x74308 : word) = Some W_74308.
Proof. vm_refl. Qed.
Lemma D_74308 : decode_any W_74308 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7430c : bv 32 := 0xb29fd0ef.
Lemma F_7430c : fetch_word AsanUbsan.M.loaded_segments (0x7430c : word) = Some W_7430c.
Proof. vm_refl. Qed.
Lemma D_7430c : decode_any W_7430c = Some (Jal 1 2087720, 4%Z).
Proof. vm_refl. Qed.

Definition W_74310 : bv 32 := 0x00090513.
Lemma F_74310 : fetch_word AsanUbsan.M.loaded_segments (0x74310 : word) = Some W_74310.
Proof. vm_refl. Qed.
Lemma D_74310 : decode_any W_74310 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74314 : bv 32 := 0x0d614583.
Lemma F_74314 : fetch_word AsanUbsan.M.loaded_segments (0x74314 : word) = Some W_74314.
Proof. vm_refl. Qed.
Lemma D_74314 : decode_any W_74314 = Some (Load SZ1 false 11 2 214, 4%Z).
Proof. vm_refl. Qed.

Definition W_74318 : bv 32 := 0xf6058ae3.
Lemma F_74318 : fetch_word AsanUbsan.M.loaded_segments (0x74318 : word) = Some W_74318.
Proof. vm_refl. Qed.
Lemma D_74318 : decode_any W_74318 = Some (Branch BC_EQ 11 0 8052, 4%Z).
Proof. vm_refl. Qed.

Definition W_7431c : bv 32 := 0x00050913.
Lemma F_7431c : fetch_word AsanUbsan.M.loaded_segments (0x7431c : word) = Some W_7431c.
Proof. vm_refl. Qed.
Lemma D_7431c : decode_any W_7431c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74320 : bv 32 := 0x00100513.
Lemma F_74320 : fetch_word AsanUbsan.M.loaded_segments (0x74320 : word) = Some W_74320.
Proof. vm_refl. Qed.
Lemma D_74320 : decode_any W_74320 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_74324 : bv 32 := 0xb11fd0ef.
Lemma F_74324 : fetch_word AsanUbsan.M.loaded_segments (0x74324 : word) = Some W_74324.
Proof. vm_refl. Qed.
Lemma D_74324 : decode_any W_74324 = Some (Jal 1 2087696, 4%Z).
Proof. vm_refl. Qed.

Definition W_74328 : bv 32 := 0x00090513.
Lemma F_74328 : fetch_word AsanUbsan.M.loaded_segments (0x74328 : word) = Some W_74328.
Proof. vm_refl. Qed.
Lemma D_74328 : decode_any W_74328 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7432c : bv 32 := 0x0d714583.
Lemma F_7432c : fetch_word AsanUbsan.M.loaded_segments (0x7432c : word) = Some W_7432c.
Proof. vm_refl. Qed.
Lemma D_7432c : decode_any W_7432c = Some (Load SZ1 false 11 2 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_74330 : bv 32 := 0xf60592e3.
Lemma F_74330 : fetch_word AsanUbsan.M.loaded_segments (0x74330 : word) = Some W_74330.
Proof. vm_refl. Qed.
Lemma D_74330 : decode_any W_74330 = Some (Branch BC_NE 11 0 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_74334 : bv 32 := 0xf71ff06f.
Lemma F_74334 : fetch_word AsanUbsan.M.loaded_segments (0x74334 : word) = Some W_74334.
Proof. vm_refl. Qed.
Lemma D_74334 : decode_any W_74334 = Some (Jal 0 2097008, 4%Z).
Proof. vm_refl. Qed.

Definition W_74338 : bv 32 := 0xfffa7517.
Lemma F_74338 : fetch_word AsanUbsan.M.loaded_segments (0x74338 : word) = Some W_74338.
Proof. vm_refl. Qed.
Lemma D_74338 : decode_any W_74338 = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_7433c : bv 32 := 0xfffa4597.
Lemma F_7433c : fetch_word AsanUbsan.M.loaded_segments (0x7433c : word) = Some W_7433c.
Proof. vm_refl. Qed.
Lemma D_7433c : decode_any W_7433c = Some (Auipc 11 1048484, 4%Z).
Proof. vm_refl. Qed.

Definition W_74340 : bv 32 := 0x8a950513.
Lemma F_74340 : fetch_word AsanUbsan.M.loaded_segments (0x74340 : word) = Some W_74340.
Proof. vm_refl. Qed.
Lemma D_74340 : decode_any W_74340 = Some (OpImm ALU_ADD 10 10 2217, 4%Z).
Proof. vm_refl. Qed.

Definition W_74344 : bv 32 := 0x36058613.
Lemma F_74344 : fetch_word AsanUbsan.M.loaded_segments (0x74344 : word) = Some W_74344.
Proof. vm_refl. Qed.
Lemma D_74344 : decode_any W_74344 = Some (OpImm ALU_ADD 12 11 864, 4%Z).
Proof. vm_refl. Qed.

Definition W_74348 : bv 32 := 0x18500593.
Lemma F_74348 : fetch_word AsanUbsan.M.loaded_segments (0x74348 : word) = Some W_74348.
Proof. vm_refl. Qed.
Lemma D_74348 : decode_any W_74348 = Some (OpImm ALU_ADD 11 0 389, 4%Z).
Proof. vm_refl. Qed.

Definition W_7434c : bv 32 := 0x00000693.
Lemma F_7434c : fetch_word AsanUbsan.M.loaded_segments (0x7434c : word) = Some W_7434c.
Proof. vm_refl. Qed.
Lemma D_7434c : decode_any W_7434c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74350 : bv 32 := 0x00000713.
Lemma F_74350 : fetch_word AsanUbsan.M.loaded_segments (0x74350 : word) = Some W_74350.
Proof. vm_refl. Qed.
Lemma D_74350 : decode_any W_74350 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74354 : bv 32 := 0x795040ef.
Lemma F_74354 : fetch_word AsanUbsan.M.loaded_segments (0x74354 : word) = Some W_74354.
Proof. vm_refl. Qed.
Lemma D_74354 : decode_any W_74354 = Some (Jal 1 20372, 4%Z).
Proof. vm_refl. Qed.

Definition W_74358 : bv 32 := 0x42055713.
Lemma F_74358 : fetch_word AsanUbsan.M.loaded_segments (0x74358 : word) = Some W_74358.
Proof. vm_refl. Qed.
Lemma D_74358 : decode_any W_74358 = Some (ShiftImm ALU_SRA 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7435c : bv 32 := 0xfffa7517.
Lemma F_7435c : fetch_word AsanUbsan.M.loaded_segments (0x7435c : word) = Some W_7435c.
Proof. vm_refl. Qed.
Lemma D_7435c : decode_any W_7435c = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_74360 : bv 32 := 0xfffaa597.
Lemma F_74360 : fetch_word AsanUbsan.M.loaded_segments (0x74360 : word) = Some W_74360.
Proof. vm_refl. Qed.
Lemma D_74360 : decode_any W_74360 = Some (Auipc 11 1048490, 4%Z).
Proof. vm_refl. Qed.

Definition W_74364 : bv 32 := 0x88550513.
Lemma F_74364 : fetch_word AsanUbsan.M.loaded_segments (0x74364 : word) = Some W_74364.
Proof. vm_refl. Qed.
Lemma D_74364 : decode_any W_74364 = Some (OpImm ALU_ADD 10 10 2181, 4%Z).
Proof. vm_refl. Qed.

Definition W_74368 : bv 32 := 0x67a58613.
Lemma F_74368 : fetch_word AsanUbsan.M.loaded_segments (0x74368 : word) = Some W_74368.
Proof. vm_refl. Qed.
Lemma D_74368 : decode_any W_74368 = Some (OpImm ALU_ADD 12 11 1658, 4%Z).
Proof. vm_refl. Qed.

Definition W_7436c : bv 32 := 0x19400593.
Lemma F_7436c : fetch_word AsanUbsan.M.loaded_segments (0x7436c : word) = Some W_7436c.
Proof. vm_refl. Qed.
Lemma D_7436c : decode_any W_7436c = Some (OpImm ALU_ADD 11 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_74370 : bv 32 := 0x00000693.
Lemma F_74370 : fetch_word AsanUbsan.M.loaded_segments (0x74370 : word) = Some W_74370.
Proof. vm_refl. Qed.
Lemma D_74370 : decode_any W_74370 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74374 : bv 32 := 0x775040ef.
Lemma F_74374 : fetch_word AsanUbsan.M.loaded_segments (0x74374 : word) = Some W_74374.
Proof. vm_refl. Qed.
Lemma D_74374 : decode_any W_74374 = Some (Jal 1 20340, 4%Z).
Proof. vm_refl. Qed.

Definition W_74378 : bv 32 := 0x42055713.
Lemma F_74378 : fetch_word AsanUbsan.M.loaded_segments (0x74378 : word) = Some W_74378.
Proof. vm_refl. Qed.
Lemma D_74378 : decode_any W_74378 = Some (ShiftImm ALU_SRA 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7437c : bv 32 := 0xfffa7517.
Lemma F_7437c : fetch_word AsanUbsan.M.loaded_segments (0x7437c : word) = Some W_7437c.
Proof. vm_refl. Qed.
Lemma D_7437c : decode_any W_7437c = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_74380 : bv 32 := 0xfffaa597.
Lemma F_74380 : fetch_word AsanUbsan.M.loaded_segments (0x74380 : word) = Some W_74380.
Proof. vm_refl. Qed.
Lemma D_74380 : decode_any W_74380 = Some (Auipc 11 1048490, 4%Z).
Proof. vm_refl. Qed.

Definition W_74384 : bv 32 := 0x86550513.
Lemma F_74384 : fetch_word AsanUbsan.M.loaded_segments (0x74384 : word) = Some W_74384.
Proof. vm_refl. Qed.
Lemma D_74384 : decode_any W_74384 = Some (OpImm ALU_ADD 10 10 2149, 4%Z).
Proof. vm_refl. Qed.

Definition W_74388 : bv 32 := 0x65a58613.
Lemma F_74388 : fetch_word AsanUbsan.M.loaded_segments (0x74388 : word) = Some W_74388.
Proof. vm_refl. Qed.
Lemma D_74388 : decode_any W_74388 = Some (OpImm ALU_ADD 12 11 1626, 4%Z).
Proof. vm_refl. Qed.

Definition W_7438c : bv 32 := 0x19600593.
Lemma F_7438c : fetch_word AsanUbsan.M.loaded_segments (0x7438c : word) = Some W_7438c.
Proof. vm_refl. Qed.
Lemma D_7438c : decode_any W_7438c = Some (OpImm ALU_ADD 11 0 406, 4%Z).
Proof. vm_refl. Qed.

Definition W_74390 : bv 32 := 0x00000693.
Lemma F_74390 : fetch_word AsanUbsan.M.loaded_segments (0x74390 : word) = Some W_74390.
Proof. vm_refl. Qed.
Lemma D_74390 : decode_any W_74390 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_74394 : bv 32 := 0x755040ef.
Lemma F_74394 : fetch_word AsanUbsan.M.loaded_segments (0x74394 : word) = Some W_74394.
Proof. vm_refl. Qed.
Lemma D_74394 : decode_any W_74394 = Some (Jal 1 20308, 4%Z).
Proof. vm_refl. Qed.
