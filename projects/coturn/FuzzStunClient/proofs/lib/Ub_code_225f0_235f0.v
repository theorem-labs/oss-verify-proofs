(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_23260 : bv 32 := 0x00853683.
Lemma F_23260 : fetch_word Ubsan.M.loaded_segments (0x23260 : word) = Some W_23260.
Proof. vm_refl. Qed.
Lemma D_23260 : decode_any W_23260 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23264 : bv 32 := 0x01053603.
Lemma F_23264 : fetch_word Ubsan.M.loaded_segments (0x23264 : word) = Some W_23264.
Proof. vm_refl. Qed.
Lemma D_23264 : decode_any W_23264 = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23268 : bv 32 := 0x05853703.
Lemma F_23268 : fetch_word Ubsan.M.loaded_segments (0x23268 : word) = Some W_23268.
Proof. vm_refl. Qed.
Lemma D_23268 : decode_any W_23268 = Some (Load SZ8 true 14 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2326c : bv 32 := 0x00b037b3.
Lemma F_2326c : fetch_word Ubsan.M.loaded_segments (0x2326c : word) = Some W_2326c.
Proof. vm_refl. Qed.
Lemma D_2326c : decode_any W_2326c = Some (Op ALU_SLTU 15 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23270 : bv 32 := 0x40d60833.
Lemma F_23270 : fetch_word Ubsan.M.loaded_segments (0x23270 : word) = Some W_23270.
Proof. vm_refl. Qed.
Lemma D_23270 : decode_any W_23270 = Some (Op ALU_SUB 16 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23274 : bv 32 := 0x0105a833.
Lemma F_23274 : fetch_word Ubsan.M.loaded_segments (0x23274 : word) = Some W_23274.
Proof. vm_refl. Qed.
Lemma D_23274 : decode_any W_23274 = Some (Op ALU_SLT 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23278 : bv 32 := 0x0107f7b3.
Lemma F_23278 : fetch_word Ubsan.M.loaded_segments (0x23278 : word) = Some W_23278.
Proof. vm_refl. Qed.
Lemma D_23278 : decode_any W_23278 = Some (Op ALU_AND 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2327c : bv 32 := 0x40d70733.
Lemma F_2327c : fetch_word Ubsan.M.loaded_segments (0x2327c : word) = Some W_2327c.
Proof. vm_refl. Qed.
Lemma D_2327c : decode_any W_2327c = Some (Op ALU_SUB 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23280 : bv 32 := 0x0cb53023.
Lemma F_23280 : fetch_word Ubsan.M.loaded_segments (0x23280 : word) = Some W_23280.
Proof. vm_refl. Qed.
Lemma D_23280 : decode_any W_23280 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23284 : bv 32 := 0x0ce53423.
Lemma F_23284 : fetch_word Ubsan.M.loaded_segments (0x23284 : word) = Some W_23284.
Proof. vm_refl. Qed.
Lemma D_23284 : decode_any W_23284 = Some (Store SZ8 10 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23288 : bv 32 := 0x00078463.
Lemma F_23288 : fetch_word Ubsan.M.loaded_segments (0x23288 : word) = Some W_23288.
Proof. vm_refl. Qed.
Lemma D_23288 : decode_any W_23288 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23290 : bv 32 := 0x0ac53c23.
Lemma F_23290 : fetch_word Ubsan.M.loaded_segments (0x23290 : word) = Some W_23290.
Proof. vm_refl. Qed.
Lemma D_23290 : decode_any W_23290 = Some (Store SZ8 10 12 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23294 : bv 32 := 0x00008067.
Lemma F_23294 : fetch_word Ubsan.M.loaded_segments (0x23294 : word) = Some W_23294.
Proof. vm_refl. Qed.
Lemma D_23294 : decode_any W_23294 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23360 : bv 32 := 0xfb010113.
Lemma F_23360 : fetch_word Ubsan.M.loaded_segments (0x23360 : word) = Some W_23360.
Proof. vm_refl. Qed.
Lemma D_23360 : decode_any W_23360 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23364 : bv 32 := 0x04113423.
Lemma F_23364 : fetch_word Ubsan.M.loaded_segments (0x23364 : word) = Some W_23364.
Proof. vm_refl. Qed.
Lemma D_23364 : decode_any W_23364 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23368 : bv 32 := 0x04813023.
Lemma F_23368 : fetch_word Ubsan.M.loaded_segments (0x23368 : word) = Some W_23368.
Proof. vm_refl. Qed.
Lemma D_23368 : decode_any W_23368 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2336c : bv 32 := 0x02913c23.
Lemma F_2336c : fetch_word Ubsan.M.loaded_segments (0x2336c : word) = Some W_2336c.
Proof. vm_refl. Qed.
Lemma D_2336c : decode_any W_2336c = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23370 : bv 32 := 0x03213823.
Lemma F_23370 : fetch_word Ubsan.M.loaded_segments (0x23370 : word) = Some W_23370.
Proof. vm_refl. Qed.
Lemma D_23370 : decode_any W_23370 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23374 : bv 32 := 0x03313423.
Lemma F_23374 : fetch_word Ubsan.M.loaded_segments (0x23374 : word) = Some W_23374.
Proof. vm_refl. Qed.
Lemma D_23374 : decode_any W_23374 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23378 : bv 32 := 0x03413023.
Lemma F_23378 : fetch_word Ubsan.M.loaded_segments (0x23378 : word) = Some W_23378.
Proof. vm_refl. Qed.
Lemma D_23378 : decode_any W_23378 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2337c : bv 32 := 0x01513c23.
Lemma F_2337c : fetch_word Ubsan.M.loaded_segments (0x2337c : word) = Some W_2337c.
Proof. vm_refl. Qed.
Lemma D_2337c : decode_any W_2337c = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23380 : bv 32 := 0x01613823.
Lemma F_23380 : fetch_word Ubsan.M.loaded_segments (0x23380 : word) = Some W_23380.
Proof. vm_refl. Qed.
Lemma D_23380 : decode_any W_23380 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23384 : bv 32 := 0x01713423.
Lemma F_23384 : fetch_word Ubsan.M.loaded_segments (0x23384 : word) = Some W_23384.
Proof. vm_refl. Qed.
Lemma D_23384 : decode_any W_23384 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23388 : bv 32 := 0x01813023.
Lemma F_23388 : fetch_word Ubsan.M.loaded_segments (0x23388 : word) = Some W_23388.
Proof. vm_refl. Qed.
Lemma D_23388 : decode_any W_23388 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2338c : bv 32 := 0x00058913.
Lemma F_2338c : fetch_word Ubsan.M.loaded_segments (0x2338c : word) = Some W_2338c.
Proof. vm_refl. Qed.
Lemma D_2338c : decode_any W_2338c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23390 : bv 32 := 0x02400593.
Lemma F_23390 : fetch_word Ubsan.M.loaded_segments (0x23390 : word) = Some W_23390.
Proof. vm_refl. Qed.
Lemma D_23390 : decode_any W_23390 = Some (OpImm ALU_ADD 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23394 : bv 32 := 0x1325ee63.
Lemma F_23394 : fetch_word Ubsan.M.loaded_segments (0x23394 : word) = Some W_23394.
Proof. vm_refl. Qed.
Lemma D_23394 : decode_any W_23394 = Some (Branch BC_LTU 11 18 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23398 : bv 32 := 0x00050493.
Lemma F_23398 : fetch_word Ubsan.M.loaded_segments (0x23398 : word) = Some W_23398.
Proof. vm_refl. Qed.
Lemma D_23398 : decode_any W_23398 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2339c : bv 32 := 0x00100513.
Lemma F_2339c : fetch_word Ubsan.M.loaded_segments (0x2339c : word) = Some W_2339c.
Proof. vm_refl. Qed.
Lemma D_2339c : decode_any W_2339c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233a0 : bv 32 := 0x12a90863.
Lemma F_233a0 : fetch_word Ubsan.M.loaded_segments (0x233a0 : word) = Some W_233a0.
Proof. vm_refl. Qed.
Lemma D_233a0 : decode_any W_233a0 = Some (Branch BC_EQ 18 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233a4 : bv 32 := 0x00068413.
Lemma F_233a4 : fetch_word Ubsan.M.loaded_segments (0x233a4 : word) = Some W_233a4.
Proof. vm_refl. Qed.
Lemma D_233a4 : decode_any W_233a4 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233a8 : bv 32 := 0x00060993.
Lemma F_233a8 : fetch_word Ubsan.M.loaded_segments (0x233a8 : word) = Some W_233a8.
Proof. vm_refl. Qed.
Lemma D_233a8 : decode_any W_233a8 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233ac : bv 32 := 0x00500a13.
Lemma F_233ac : fetch_word Ubsan.M.loaded_segments (0x233ac : word) = Some W_233ac.
Proof. vm_refl. Qed.
Lemma D_233ac : decode_any W_233ac = Some (OpImm ALU_ADD 20 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233b0 : bv 32 := 0x02000a93.
Lemma F_233b0 : fetch_word Ubsan.M.loaded_segments (0x233b0 : word) = Some W_233b0.
Proof. vm_refl. Qed.
Lemma D_233b0 : decode_any W_233b0 = Some (OpImm ALU_ADD 21 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233b4 : bv 32 := 0x0140006f.
Lemma F_233b4 : fetch_word Ubsan.M.loaded_segments (0x233b4 : word) = Some W_233b4.
Proof. vm_refl. Qed.
Lemma D_233b4 : decode_any W_233b4 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233c8 : bv 32 := 0x0084b503.
Lemma F_233c8 : fetch_word Ubsan.M.loaded_segments (0x233c8 : word) = Some W_233c8.
Proof. vm_refl. Qed.
Lemma D_233c8 : decode_any W_233c8 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233cc : bv 32 := 0x0b84b583.
Lemma F_233cc : fetch_word Ubsan.M.loaded_segments (0x233cc : word) = Some W_233cc.
Proof. vm_refl. Qed.
Lemma D_233cc : decode_any W_233cc = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233d0 : bv 32 := 0xfeb504e3.
Lemma F_233d0 : fetch_word Ubsan.M.loaded_segments (0x233d0 : word) = Some W_233d0.
Proof. vm_refl. Qed.
Lemma D_233d0 : decode_any W_233d0 = Some (Branch BC_EQ 10 11 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233d4 : bv 32 := 0x00150593.
Lemma F_233d4 : fetch_word Ubsan.M.loaded_segments (0x233d4 : word) = Some W_233d4.
Proof. vm_refl. Qed.
Lemma D_233d4 : decode_any W_233d4 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233d8 : bv 32 := 0x00b4b423.
Lemma F_233d8 : fetch_word Ubsan.M.loaded_segments (0x233d8 : word) = Some W_233d8.
Proof. vm_refl. Qed.
Lemma D_233d8 : decode_any W_233d8 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233dc : bv 32 := 0x00054503.
Lemma F_233dc : fetch_word Ubsan.M.loaded_segments (0x233dc : word) = Some W_233dc.
Proof. vm_refl. Qed.
Lemma D_233dc : decode_any W_233dc = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233e0 : bv 32 := 0xff750593.
Lemma F_233e0 : fetch_word Ubsan.M.loaded_segments (0x233e0 : word) = Some W_233e0.
Proof. vm_refl. Qed.
Lemma D_233e0 : decode_any W_233e0 = Some (OpImm ALU_ADD 11 10 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233e4 : bv 32 := 0xff45e2e3.
Lemma F_233e4 : fetch_word Ubsan.M.loaded_segments (0x233e4 : word) = Some W_233e4.
Proof. vm_refl. Qed.
Lemma D_233e4 : decode_any W_233e4 = Some (Branch BC_LTU 11 20 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233e8 : bv 32 := 0xff5500e3.
Lemma F_233e8 : fetch_word Ubsan.M.loaded_segments (0x233e8 : word) = Some W_233e8.
Proof. vm_refl. Qed.
Lemma D_233e8 : decode_any W_233e8 = Some (Branch BC_EQ 10 21 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233ec : bv 32 := 0x02d00593.
Lemma F_233ec : fetch_word Ubsan.M.loaded_segments (0x233ec : word) = Some W_233ec.
Proof. vm_refl. Qed.
Lemma D_233ec : decode_any W_233ec = Some (OpImm ALU_ADD 11 0 45, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f0 : bv 32 := 0x00b50663.
Lemma F_233f0 : fetch_word Ubsan.M.loaded_segments (0x233f0 : word) = Some W_233f0.
Proof. vm_refl. Qed.
Lemma D_233f0 : decode_any W_233f0 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f4 : bv 32 := 0x02b00593.
Lemma F_233f4 : fetch_word Ubsan.M.loaded_segments (0x233f4 : word) = Some W_233f4.
Proof. vm_refl. Qed.
Lemma D_233f4 : decode_any W_233f4 = Some (OpImm ALU_ADD 11 0 43, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233f8 : bv 32 := 0x02b51a63.
Lemma F_233f8 : fetch_word Ubsan.M.loaded_segments (0x233f8 : word) = Some W_233f8.
Proof. vm_refl. Qed.
Lemma D_233f8 : decode_any W_233f8 = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_233fc : bv 32 := 0x0084b583.
Lemma F_233fc : fetch_word Ubsan.M.loaded_segments (0x233fc : word) = Some W_233fc.
Proof. vm_refl. Qed.
Lemma D_233fc : decode_any W_233fc = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23400 : bv 32 := 0x0b84b603.
Lemma F_23400 : fetch_word Ubsan.M.loaded_segments (0x23400 : word) = Some W_23400.
Proof. vm_refl. Qed.
Lemma D_23400 : decode_any W_23400 = Some (Load SZ8 true 12 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23404 : bv 32 := 0xfd350513.
Lemma F_23404 : fetch_word Ubsan.M.loaded_segments (0x23404 : word) = Some W_23404.
Proof. vm_refl. Qed.
Lemma D_23404 : decode_any W_23404 = Some (OpImm ALU_ADD 10 10 4051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23408 : bv 32 := 0x00a03a33.
Lemma F_23408 : fetch_word Ubsan.M.loaded_segments (0x23408 : word) = Some W_23408.
Proof. vm_refl. Qed.
Lemma D_23408 : decode_any W_23408 = Some (Op ALU_SLTU 20 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2340c : bv 32 := 0xfffa0a1b.
Lemma F_2340c : fetch_word Ubsan.M.loaded_segments (0x2340c : word) = Some W_2340c.
Proof. vm_refl. Qed.
Lemma D_2340c : decode_any W_2340c = Some (OpImm32 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23410 : bv 32 := 0x02c58663.
Lemma F_23410 : fetch_word Ubsan.M.loaded_segments (0x23410 : word) = Some W_23410.
Proof. vm_refl. Qed.
Lemma D_23410 : decode_any W_23410 = Some (Branch BC_EQ 11 12 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23414 : bv 32 := 0x00158513.
Lemma F_23414 : fetch_word Ubsan.M.loaded_segments (0x23414 : word) = Some W_23414.
Proof. vm_refl. Qed.
Lemma D_23414 : decode_any W_23414 = Some (OpImm ALU_ADD 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23418 : bv 32 := 0x00a4b423.
Lemma F_23418 : fetch_word Ubsan.M.loaded_segments (0x23418 : word) = Some W_23418.
Proof. vm_refl. Qed.
Lemma D_23418 : decode_any W_23418 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2341c : bv 32 := 0x0005c503.
Lemma F_2341c : fetch_word Ubsan.M.loaded_segments (0x2341c : word) = Some W_2341c.
Proof. vm_refl. Qed.
Lemma D_2341c : decode_any W_2341c = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23420 : bv 32 := 0xfef97593.
Lemma F_23420 : fetch_word Ubsan.M.loaded_segments (0x23420 : word) = Some W_23420.
Proof. vm_refl. Qed.
Lemma D_23420 : decode_any W_23420 = Some (OpImm ALU_AND 11 18 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23424 : bv 32 := 0x02058463.
Lemma F_23424 : fetch_word Ubsan.M.loaded_segments (0x23424 : word) = Some W_23424.
Proof. vm_refl. Qed.
Lemma D_23424 : decode_any W_23424 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23428 : bv 32 := 0x06c0006f.
Lemma F_23428 : fetch_word Ubsan.M.loaded_segments (0x23428 : word) = Some W_23428.
Proof. vm_refl. Qed.
Lemma D_23428 : decode_any W_23428 = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2342c : bv 32 := 0x00000a13.
Lemma F_2342c : fetch_word Ubsan.M.loaded_segments (0x2342c : word) = Some W_2342c.
Proof. vm_refl. Qed.
Lemma D_2342c : decode_any W_2342c = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23430 : bv 32 := 0xfef97593.
Lemma F_23430 : fetch_word Ubsan.M.loaded_segments (0x23430 : word) = Some W_23430.
Proof. vm_refl. Qed.
Lemma D_23430 : decode_any W_23430 = Some (OpImm ALU_AND 11 18 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23434 : bv 32 := 0x00058c63.
Lemma F_23434 : fetch_word Ubsan.M.loaded_segments (0x23434 : word) = Some W_23434.
Proof. vm_refl. Qed.
Lemma D_23434 : decode_any W_23434 = Some (Branch BC_EQ 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23438 : bv 32 := 0x05c0006f.
Lemma F_23438 : fetch_word Ubsan.M.loaded_segments (0x23438 : word) = Some W_23438.
Proof. vm_refl. Qed.
Lemma D_23438 : decode_any W_23438 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23494 : bv 32 := 0x00091463.
Lemma F_23494 : fetch_word Ubsan.M.loaded_segments (0x23494 : word) = Some W_23494.
Proof. vm_refl. Qed.
Lemma D_23494 : decode_any W_23494 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2349c : bv 32 := 0xfffee597.
Lemma F_2349c : fetch_word Ubsan.M.loaded_segments (0x2349c : word) = Some W_2349c.
Proof. vm_refl. Qed.
Lemma D_2349c : decode_any W_2349c = Some (Auipc 11 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234a0 : bv 32 := 0xfd058593.
Lemma F_234a0 : fetch_word Ubsan.M.loaded_segments (0x234a0 : word) = Some W_234a0.
Proof. vm_refl. Qed.
Lemma D_234a0 : decode_any W_234a0 = Some (OpImm ALU_ADD 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234a4 : bv 32 := 0x00a585b3.
Lemma F_234a4 : fetch_word Ubsan.M.loaded_segments (0x234a4 : word) = Some W_234a4.
Proof. vm_refl. Qed.
Lemma D_234a4 : decode_any W_234a4 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234a8 : bv 32 := 0x0015c583.
Lemma F_234a8 : fetch_word Ubsan.M.loaded_segments (0x234a8 : word) = Some W_234a8.
Proof. vm_refl. Qed.
Lemma D_234a8 : decode_any W_234a8 = Some (Load SZ1 false 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234ac : bv 32 := 0x0525e863.
Lemma F_234ac : fetch_word Ubsan.M.loaded_segments (0x234ac : word) = Some W_234ac.
Proof. vm_refl. Qed.
Lemma D_234ac : decode_any W_234ac = Some (Branch BC_LTU 11 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234b0 : bv 32 := 0x0c04b503.
Lemma F_234b0 : fetch_word Ubsan.M.loaded_segments (0x234b0 : word) = Some W_234b0.
Proof. vm_refl. Qed.
Lemma D_234b0 : decode_any W_234b0 = Some (Load SZ8 true 10 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234b4 : bv 32 := 0x00054863.
Lemma F_234b4 : fetch_word Ubsan.M.loaded_segments (0x234b4 : word) = Some W_234b4.
Proof. vm_refl. Qed.
Lemma D_234b4 : decode_any W_234b4 = Some (Branch BC_LT 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234b8 : bv 32 := 0x0084b503.
Lemma F_234b8 : fetch_word Ubsan.M.loaded_segments (0x234b8 : word) = Some W_234b8.
Proof. vm_refl. Qed.
Lemma D_234b8 : decode_any W_234b8 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234bc : bv 32 := 0xfff50513.
Lemma F_234bc : fetch_word Ubsan.M.loaded_segments (0x234bc : word) = Some W_234bc.
Proof. vm_refl. Qed.
Lemma D_234bc : decode_any W_234bc = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234c0 : bv 32 := 0x00a4b423.
Lemma F_234c0 : fetch_word Ubsan.M.loaded_segments (0x234c0 : word) = Some W_234c0.
Proof. vm_refl. Qed.
Lemma D_234c0 : decode_any W_234c0 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234c4 : bv 32 := 0x00048513.
Lemma F_234c4 : fetch_word Ubsan.M.loaded_segments (0x234c4 : word) = Some W_234c4.
Proof. vm_refl. Qed.
Lemma D_234c4 : decode_any W_234c4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234c8 : bv 32 := 0x00000593.
Lemma F_234c8 : fetch_word Ubsan.M.loaded_segments (0x234c8 : word) = Some W_234c8.
Proof. vm_refl. Qed.
Lemma D_234c8 : decode_any W_234c8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234cc : bv 32 := 0xd95ff0ef.
Lemma F_234cc : fetch_word Ubsan.M.loaded_segments (0x234cc : word) = Some W_234cc.
Proof. vm_refl. Qed.
Lemma D_234cc : decode_any W_234cc = Some (Jal 1 2096532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234d0 : bv 32 := 0x889f80ef.
Lemma F_234d0 : fetch_word Ubsan.M.loaded_segments (0x234d0 : word) = Some W_234d0.
Proof. vm_refl. Qed.
Lemma D_234d0 : decode_any W_234d0 = Some (Jal 1 2066568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234d4 : bv 32 := 0x00000413.
Lemma F_234d4 : fetch_word Ubsan.M.loaded_segments (0x234d4 : word) = Some W_234d4.
Proof. vm_refl. Qed.
Lemma D_234d4 : decode_any W_234d4 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234d8 : bv 32 := 0x01600593.
Lemma F_234d8 : fetch_word Ubsan.M.loaded_segments (0x234d8 : word) = Some W_234d8.
Proof. vm_refl. Qed.
Lemma D_234d8 : decode_any W_234d8 = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234dc : bv 32 := 0x00b52023.
Lemma F_234dc : fetch_word Ubsan.M.loaded_segments (0x234dc : word) = Some W_234dc.
Proof. vm_refl. Qed.
Lemma D_234dc : decode_any W_234dc = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234e0 : bv 32 := 0x4240006f.
Lemma F_234e0 : fetch_word Ubsan.M.loaded_segments (0x234e0 : word) = Some W_234e0.
Proof. vm_refl. Qed.
Lemma D_234e0 : decode_any W_234e0 = Some (Jal 0 1060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_234fc : bv 32 := 0x00a00593.
Lemma F_234fc : fetch_word Ubsan.M.loaded_segments (0x234fc : word) = Some W_234fc.
Proof. vm_refl. Qed.
Lemma D_234fc : decode_any W_234fc = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23500 : bv 32 := 0x12b91463.
Lemma F_23500 : fetch_word Ubsan.M.loaded_segments (0x23500 : word) = Some W_23500.
Proof. vm_refl. Qed.
Lemma D_23500 : decode_any W_23500 = Some (Branch BC_NE 18 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23504 : bv 32 := 0xfd050a9b.
Lemma F_23504 : fetch_word Ubsan.M.loaded_segments (0x23504 : word) = Some W_23504.
Proof. vm_refl. Qed.
Lemma D_23504 : decode_any W_23504 = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23508 : bv 32 := 0x00000993.
Lemma F_23508 : fetch_word Ubsan.M.loaded_segments (0x23508 : word) = Some W_23508.
Proof. vm_refl. Qed.
Lemma D_23508 : decode_any W_23508 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2350c : bv 32 := 0x00900913.
Lemma F_2350c : fetch_word Ubsan.M.loaded_segments (0x2350c : word) = Some W_2350c.
Proof. vm_refl. Qed.
Lemma D_2350c : decode_any W_2350c = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23510 : bv 32 := 0x07596063.
Lemma F_23510 : fetch_word Ubsan.M.loaded_segments (0x23510 : word) = Some W_23510.
Proof. vm_refl. Qed.
Lemma D_23510 : decode_any W_23510 = Some (Branch BC_LTU 18 21 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23514 : bv 32 := 0x00a00b13.
Lemma F_23514 : fetch_word Ubsan.M.loaded_segments (0x23514 : word) = Some W_23514.
Proof. vm_refl. Qed.
Lemma D_23514 : decode_any W_23514 = Some (OpImm ALU_ADD 22 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23518 : bv 32 := 0x1999a537.
Lemma F_23518 : fetch_word Ubsan.M.loaded_segments (0x23518 : word) = Some W_23518.
Proof. vm_refl. Qed.
Lemma D_23518 : decode_any W_23518 = Some (Lui 10 104858, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2351c : bv 32 := 0x99950b9b.
Lemma F_2351c : fetch_word Ubsan.M.loaded_segments (0x2351c : word) = Some W_2351c.
Proof. vm_refl. Qed.
Lemma D_2351c : decode_any W_2351c = Some (OpImm32 23 10 2457, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23520 : bv 32 := 0x0200006f.
Lemma F_23520 : fetch_word Ubsan.M.loaded_segments (0x23520 : word) = Some W_23520.
Proof. vm_refl. Qed.
Lemma D_23520 : decode_any W_23520 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2353c : bv 32 := 0x0379f663.
Lemma F_2353c : fetch_word Ubsan.M.loaded_segments (0x2353c : word) = Some W_2353c.
Proof. vm_refl. Qed.
Lemma D_2353c : decode_any W_2353c = Some (Branch BC_GEU 19 23 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23540 : bv 32 := 0x0084b503.
Lemma F_23540 : fetch_word Ubsan.M.loaded_segments (0x23540 : word) = Some W_23540.
Proof. vm_refl. Qed.
Lemma D_23540 : decode_any W_23540 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23544 : bv 32 := 0x0b84b583.
Lemma F_23544 : fetch_word Ubsan.M.loaded_segments (0x23544 : word) = Some W_23544.
Proof. vm_refl. Qed.
Lemma D_23544 : decode_any W_23544 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23548 : bv 32 := 0xfcb50ee3.
Lemma F_23548 : fetch_word Ubsan.M.loaded_segments (0x23548 : word) = Some W_23548.
Proof. vm_refl. Qed.
Lemma D_23548 : decode_any W_23548 = Some (Branch BC_EQ 10 11 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2354c : bv 32 := 0x00150593.
Lemma F_2354c : fetch_word Ubsan.M.loaded_segments (0x2354c : word) = Some W_2354c.
Proof. vm_refl. Qed.
Lemma D_2354c : decode_any W_2354c = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23550 : bv 32 := 0x00b4b423.
Lemma F_23550 : fetch_word Ubsan.M.loaded_segments (0x23550 : word) = Some W_23550.
Proof. vm_refl. Qed.
Lemma D_23550 : decode_any W_23550 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23554 : bv 32 := 0x00054503.
Lemma F_23554 : fetch_word Ubsan.M.loaded_segments (0x23554 : word) = Some W_23554.
Proof. vm_refl. Qed.
Lemma D_23554 : decode_any W_23554 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23558 : bv 32 := 0x036985b3.
Lemma F_23558 : fetch_word Ubsan.M.loaded_segments (0x23558 : word) = Some W_23558.
Proof. vm_refl. Qed.
Lemma D_23558 : decode_any W_23558 = Some (Mul M_MUL 11 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2355c : bv 32 := 0x015589bb.
Lemma F_2355c : fetch_word Ubsan.M.loaded_segments (0x2355c : word) = Some W_2355c.
Proof. vm_refl. Qed.
Lemma D_2355c : decode_any W_2355c = Some (Op32 ALU_ADD 19 11 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23560 : bv 32 := 0xfd050a9b.
Lemma F_23560 : fetch_word Ubsan.M.loaded_segments (0x23560 : word) = Some W_23560.
Proof. vm_refl. Qed.
Lemma D_23560 : decode_any W_23560 = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23564 : bv 32 := 0xfd597ce3.
Lemma F_23564 : fetch_word Ubsan.M.loaded_segments (0x23564 : word) = Some W_23564.
Proof. vm_refl. Qed.
Lemma D_23564 : decode_any W_23564 = Some (Branch BC_GEU 18 21 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23568 : bv 32 := 0x02099993.
Lemma F_23568 : fetch_word Ubsan.M.loaded_segments (0x23568 : word) = Some W_23568.
Proof. vm_refl. Qed.
Lemma D_23568 : decode_any W_23568 = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2356c : bv 32 := 0x0209d993.
Lemma F_2356c : fetch_word Ubsan.M.loaded_segments (0x2356c : word) = Some W_2356c.
Proof. vm_refl. Qed.
Lemma D_2356c : decode_any W_2356c = Some (ShiftImm ALU_SRL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23570 : bv 32 := 0x2d596463.
Lemma F_23570 : fetch_word Ubsan.M.loaded_segments (0x23570 : word) = Some W_23570.
Proof. vm_refl. Qed.
Lemma D_23570 : decode_any W_23570 = Some (Branch BC_LTU 18 21 712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23574 : bv 32 := 0xfffed517.
Lemma F_23574 : fetch_word Ubsan.M.loaded_segments (0x23574 : word) = Some W_23574.
Proof. vm_refl. Qed.
Lemma D_23574 : decode_any W_23574 = Some (Auipc 10 1048557, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23578 : bv 32 := 0xffc53b03.
Lemma F_23578 : fetch_word Ubsan.M.loaded_segments (0x23578 : word) = Some W_23578.
Proof. vm_refl. Qed.
Lemma D_23578 : decode_any W_23578 = Some (Load SZ8 true 22 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2357c : bv 32 := 0x00a00513.
Lemma F_2357c : fetch_word Ubsan.M.loaded_segments (0x2357c : word) = Some W_2357c.
Proof. vm_refl. Qed.
Lemma D_2357c : decode_any W_2357c = Some (OpImm ALU_ADD 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23580 : bv 32 := 0x02a98c33.
Lemma F_23580 : fetch_word Ubsan.M.loaded_segments (0x23580 : word) = Some W_23580.
Proof. vm_refl. Qed.
Lemma D_23580 : decode_any W_23580 = Some (Mul M_MUL 24 19 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23584 : bv 32 := 0x00900b93.
Lemma F_23584 : fetch_word Ubsan.M.loaded_segments (0x23584 : word) = Some W_23584.
Proof. vm_refl. Qed.
Lemma D_23584 : decode_any W_23584 = Some (OpImm ALU_ADD 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23588 : bv 32 := 0x0084b503.
Lemma F_23588 : fetch_word Ubsan.M.loaded_segments (0x23588 : word) = Some W_23588.
Proof. vm_refl. Qed.
Lemma D_23588 : decode_any W_23588 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2358c : bv 32 := 0x0b84b583.
Lemma F_2358c : fetch_word Ubsan.M.loaded_segments (0x2358c : word) = Some W_2358c.
Proof. vm_refl. Qed.
Lemma D_2358c : decode_any W_2358c = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23590 : bv 32 := 0x02b50063.
Lemma F_23590 : fetch_word Ubsan.M.loaded_segments (0x23590 : word) = Some W_23590.
Proof. vm_refl. Qed.
Lemma D_23590 : decode_any W_23590 = Some (Branch BC_EQ 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23594 : bv 32 := 0x00150593.
Lemma F_23594 : fetch_word Ubsan.M.loaded_segments (0x23594 : word) = Some W_23594.
Proof. vm_refl. Qed.
Lemma D_23594 : decode_any W_23594 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23598 : bv 32 := 0x00b4b423.
Lemma F_23598 : fetch_word Ubsan.M.loaded_segments (0x23598 : word) = Some W_23598.
Proof. vm_refl. Qed.
Lemma D_23598 : decode_any W_23598 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2359c : bv 32 := 0x00054503.
Lemma F_2359c : fetch_word Ubsan.M.loaded_segments (0x2359c : word) = Some W_2359c.
Proof. vm_refl. Qed.
Lemma D_2359c : decode_any W_2359c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235a0 : bv 32 := 0x015c09b3.
Lemma F_235a0 : fetch_word Ubsan.M.loaded_segments (0x235a0 : word) = Some W_235a0.
Proof. vm_refl. Qed.
Lemma D_235a0 : decode_any W_235a0 = Some (Op ALU_ADD 19 24 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235a4 : bv 32 := 0xfd050a9b.
Lemma F_235a4 : fetch_word Ubsan.M.loaded_segments (0x235a4 : word) = Some W_235a4.
Proof. vm_refl. Qed.
Lemma D_235a4 : decode_any W_235a4 = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235a8 : bv 32 := 0x015bfe63.
Lemma F_235a8 : fetch_word Ubsan.M.loaded_segments (0x235a8 : word) = Some W_235a8.
Proof. vm_refl. Qed.
Lemma D_235a8 : decode_any W_235a8 = Some (Branch BC_GEU 23 21 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235ac : bv 32 := 0x26c0006f.
Lemma F_235ac : fetch_word Ubsan.M.loaded_segments (0x235ac : word) = Some W_235ac.
Proof. vm_refl. Qed.
Lemma D_235ac : decode_any W_235ac = Some (Jal 0 620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235c4 : bv 32 := 0x2569fa63.
Lemma F_235c4 : fetch_word Ubsan.M.loaded_segments (0x235c4 : word) = Some W_235c4.
Proof. vm_refl. Qed.
Lemma D_235c4 : decode_any W_235c4 = Some (Branch BC_GEU 19 22 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235c8 : bv 32 := 0x00a00913.
Lemma F_235c8 : fetch_word Ubsan.M.loaded_segments (0x235c8 : word) = Some W_235c8.
Proof. vm_refl. Qed.
Lemma D_235c8 : decode_any W_235c8 = Some (OpImm ALU_ADD 18 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235cc : bv 32 := 0x03298c33.
Lemma F_235cc : fetch_word Ubsan.M.loaded_segments (0x235cc : word) = Some W_235cc.
Proof. vm_refl. Qed.
Lemma D_235cc : decode_any W_235cc = Some (Mul M_MUL 24 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235d0 : bv 32 := 0xfffac593.
Lemma F_235d0 : fetch_word Ubsan.M.loaded_segments (0x235d0 : word) = Some W_235d0.
Proof. vm_refl. Qed.
Lemma D_235d0 : decode_any W_235d0 = Some (OpImm ALU_XOR 11 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235d4 : bv 32 := 0xfb85fae3.
Lemma F_235d4 : fetch_word Ubsan.M.loaded_segments (0x235d4 : word) = Some W_235d4.
Proof. vm_refl. Qed.
Lemma D_235d4 : decode_any W_235d4 = Some (Branch BC_GEU 11 24 8116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_235d8 : bv 32 := 0x24c0006f.
Lemma F_235d8 : fetch_word Ubsan.M.loaded_segments (0x235d8 : word) = Some W_235d8.
Proof. vm_refl. Qed.
Lemma D_235d8 : decode_any W_235d8 = Some (Jal 0 588, 4%Z).
Proof. vm_refl. Qed.
