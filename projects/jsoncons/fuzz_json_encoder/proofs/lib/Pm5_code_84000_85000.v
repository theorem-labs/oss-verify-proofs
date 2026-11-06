(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_842f4 : bv 32 := 0xfc010113.
Lemma F_842f4 : fetch_word AsanUbsan.M.loaded_segments (0x8433c : word) = Some W_842f4.
Proof. vm_refl. Qed.
Lemma D_842f4 : decode_any W_842f4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_842f8 : bv 32 := 0x02113c23.
Lemma F_842f8 : fetch_word AsanUbsan.M.loaded_segments (0x84340 : word) = Some W_842f8.
Proof. vm_refl. Qed.
Lemma D_842f8 : decode_any W_842f8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_842fc : bv 32 := 0x02813823.
Lemma F_842fc : fetch_word AsanUbsan.M.loaded_segments (0x84344 : word) = Some W_842fc.
Proof. vm_refl. Qed.
Lemma D_842fc : decode_any W_842fc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84300 : bv 32 := 0x02913423.
Lemma F_84300 : fetch_word AsanUbsan.M.loaded_segments (0x84348 : word) = Some W_84300.
Proof. vm_refl. Qed.
Lemma D_84300 : decode_any W_84300 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84304 : bv 32 := 0x03213023.
Lemma F_84304 : fetch_word AsanUbsan.M.loaded_segments (0x8434c : word) = Some W_84304.
Proof. vm_refl. Qed.
Lemma D_84304 : decode_any W_84304 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84308 : bv 32 := 0x01313c23.
Lemma F_84308 : fetch_word AsanUbsan.M.loaded_segments (0x84350 : word) = Some W_84308.
Proof. vm_refl. Qed.
Lemma D_84308 : decode_any W_84308 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8430c : bv 32 := 0x01413823.
Lemma F_8430c : fetch_word AsanUbsan.M.loaded_segments (0x84354 : word) = Some W_8430c.
Proof. vm_refl. Qed.
Lemma D_8430c : decode_any W_8430c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84310 : bv 32 := 0x01513423.
Lemma F_84310 : fetch_word AsanUbsan.M.loaded_segments (0x84358 : word) = Some W_84310.
Proof. vm_refl. Qed.
Lemma D_84310 : decode_any W_84310 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84314 : bv 32 := 0x14058c63.
Lemma F_84314 : fetch_word AsanUbsan.M.loaded_segments (0x8435c : word) = Some W_84314.
Proof. vm_refl. Qed.
Lemma D_84314 : decode_any W_84314 = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84318 : bv 32 := 0x00058493.
Lemma F_84318 : fetch_word AsanUbsan.M.loaded_segments (0x84360 : word) = Some W_84318.
Proof. vm_refl. Qed.
Lemma D_84318 : decode_any W_84318 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8431c : bv 32 := 0x00050413.
Lemma F_8431c : fetch_word AsanUbsan.M.loaded_segments (0x84364 : word) = Some W_8431c.
Proof. vm_refl. Qed.
Lemma D_8431c : decode_any W_8431c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84320 : bv 32 := 0x000e0517.
Lemma F_84320 : fetch_word AsanUbsan.M.loaded_segments (0x84368 : word) = Some W_84320.
Proof. vm_refl. Qed.
Lemma D_84320 : decode_any W_84320 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84324 : bv 32 := 0x1b053a83.
Lemma F_84324 : fetch_word AsanUbsan.M.loaded_segments (0x8436c : word) = Some W_84324.
Proof. vm_refl. Qed.
Lemma D_84324 : decode_any W_84324 = Some (Load SZ8 true 21 10 432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84328 : bv 32 := 0x000ab583.
Lemma F_84328 : fetch_word AsanUbsan.M.loaded_segments (0x84370 : word) = Some W_84328.
Proof. vm_refl. Qed.
Lemma D_84328 : decode_any W_84328 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8432c : bv 32 := 0xfff58513.
Lemma F_8432c : fetch_word AsanUbsan.M.loaded_segments (0x84374 : word) = Some W_8432c.
Proof. vm_refl. Qed.
Lemma D_8432c : decode_any W_8432c = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84330 : bv 32 := 0x00a5b633.
Lemma F_84330 : fetch_word AsanUbsan.M.loaded_segments (0x84378 : word) = Some W_84330.
Proof. vm_refl. Qed.
Lemma D_84330 : decode_any W_84330 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84334 : bv 32 := 0xfff60613.
Lemma F_84334 : fetch_word AsanUbsan.M.loaded_segments (0x8437c : word) = Some W_84334.
Proof. vm_refl. Qed.
Lemma D_84334 : decode_any W_84334 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84338 : bv 32 := 0x00a67633.
Lemma F_84338 : fetch_word AsanUbsan.M.loaded_segments (0x84380 : word) = Some W_84338.
Proof. vm_refl. Qed.
Lemma D_84338 : decode_any W_84338 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8433c : bv 32 := 0x04867263.
Lemma F_8433c : fetch_word AsanUbsan.M.loaded_segments (0x84384 : word) = Some W_8433c.
Proof. vm_refl. Qed.
Lemma D_8433c : decode_any W_8433c = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84340 : bv 32 := 0x000e0697.
Lemma F_84340 : fetch_word AsanUbsan.M.loaded_segments (0x84388 : word) = Some W_84340.
Proof. vm_refl. Qed.
Lemma D_84340 : decode_any W_84340 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84344 : bv 32 := 0x1986b683.
Lemma F_84344 : fetch_word AsanUbsan.M.loaded_segments (0x8438c : word) = Some W_84344.
Proof. vm_refl. Qed.
Lemma D_84344 : decode_any W_84344 = Some (Load SZ8 true 13 13 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84348 : bv 32 := 0x000e0717.
Lemma F_84348 : fetch_word AsanUbsan.M.loaded_segments (0x84390 : word) = Some W_84348.
Proof. vm_refl. Qed.
Lemma D_84348 : decode_any W_84348 = Some (Auipc 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8434c : bv 32 := 0x19873703.
Lemma F_8434c : fetch_word AsanUbsan.M.loaded_segments (0x84394 : word) = Some W_8434c.
Proof. vm_refl. Qed.
Lemma D_8434c : decode_any W_8434c = Some (Load SZ8 true 14 14 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84350 : bv 32 := 0x0006b803.
Lemma F_84350 : fetch_word AsanUbsan.M.loaded_segments (0x84398 : word) = Some W_84350.
Proof. vm_refl. Qed.
Lemma D_84350 : decode_any W_84350 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84354 : bv 32 := 0x00073683.
Lemma F_84354 : fetch_word AsanUbsan.M.loaded_segments (0x8439c : word) = Some W_84354.
Proof. vm_refl. Qed.
Lemma D_84354 : decode_any W_84354 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84358 : bv 32 := 0xfff80793.
Lemma F_84358 : fetch_word AsanUbsan.M.loaded_segments (0x843a0 : word) = Some W_84358.
Proof. vm_refl. Qed.
Lemma D_84358 : decode_any W_84358 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8435c : bv 32 := 0x0087f463.
Lemma F_8435c : fetch_word AsanUbsan.M.loaded_segments (0x843a4 : word) = Some W_8435c.
Proof. vm_refl. Qed.
Lemma D_8435c : decode_any W_8435c = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84364 : bv 32 := 0x000e0717.
Lemma F_84364 : fetch_word AsanUbsan.M.loaded_segments (0x843ac : word) = Some W_84364.
Proof. vm_refl. Qed.
Lemma D_84364 : decode_any W_84364 = Some (Auipc 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84368 : bv 32 := 0x18473703.
Lemma F_84368 : fetch_word AsanUbsan.M.loaded_segments (0x843b0 : word) = Some W_84368.
Proof. vm_refl. Qed.
Lemma D_84368 : decode_any W_84368 = Some (Load SZ8 true 14 14 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8436c : bv 32 := 0x00073283.
Lemma F_8436c : fetch_word AsanUbsan.M.loaded_segments (0x843b4 : word) = Some W_8436c.
Proof. vm_refl. Qed.
Lemma D_8436c : decode_any W_8436c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84370 : bv 32 := 0x0032d713.
Lemma F_84370 : fetch_word AsanUbsan.M.loaded_segments (0x843b8 : word) = Some W_84370.
Proof. vm_refl. Qed.
Lemma D_84370 : decode_any W_84370 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84374 : bv 32 := 0x00b708b3.
Lemma F_84374 : fetch_word AsanUbsan.M.loaded_segments (0x843bc : word) = Some W_84374.
Proof. vm_refl. Qed.
Lemma D_84374 : decode_any W_84374 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84378 : bv 32 := 0x1282e063.
Lemma F_84378 : fetch_word AsanUbsan.M.loaded_segments (0x843c0 : word) = Some W_84378.
Proof. vm_refl. Qed.
Lemma D_84378 : decode_any W_84378 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8437c : bv 32 := 0x1088fe63.
Lemma F_8437c : fetch_word AsanUbsan.M.loaded_segments (0x843c4 : word) = Some W_8437c.
Proof. vm_refl. Qed.
Lemma D_8437c : decode_any W_8437c = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84380 : bv 32 := 0x00848933.
Lemma F_84380 : fetch_word AsanUbsan.M.loaded_segments (0x843c8 : word) = Some W_84380.
Proof. vm_refl. Qed.
Lemma D_84380 : decode_any W_84380 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84384 : bv 32 := 0x05267263.
Lemma F_84384 : fetch_word AsanUbsan.M.loaded_segments (0x843cc : word) = Some W_84384.
Proof. vm_refl. Qed.
Lemma D_84384 : decode_any W_84384 = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84388 : bv 32 := 0x000e0617.
Lemma F_84388 : fetch_word AsanUbsan.M.loaded_segments (0x843d0 : word) = Some W_84388.
Proof. vm_refl. Qed.
Lemma D_84388 : decode_any W_84388 = Some (Auipc 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8438c : bv 32 := 0x15063603.
Lemma F_8438c : fetch_word AsanUbsan.M.loaded_segments (0x843d4 : word) = Some W_8438c.
Proof. vm_refl. Qed.
Lemma D_8438c : decode_any W_8438c = Some (Load SZ8 true 12 12 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84390 : bv 32 := 0x000e0697.
Lemma F_84390 : fetch_word AsanUbsan.M.loaded_segments (0x843d8 : word) = Some W_84390.
Proof. vm_refl. Qed.
Lemma D_84390 : decode_any W_84390 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84394 : bv 32 := 0x1506b683.
Lemma F_84394 : fetch_word AsanUbsan.M.loaded_segments (0x843dc : word) = Some W_84394.
Proof. vm_refl. Qed.
Lemma D_84394 : decode_any W_84394 = Some (Load SZ8 true 13 13 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84398 : bv 32 := 0x00063783.
Lemma F_84398 : fetch_word AsanUbsan.M.loaded_segments (0x843e0 : word) = Some W_84398.
Proof. vm_refl. Qed.
Lemma D_84398 : decode_any W_84398 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8439c : bv 32 := 0x0006b603.
Lemma F_8439c : fetch_word AsanUbsan.M.loaded_segments (0x843e4 : word) = Some W_8439c.
Proof. vm_refl. Qed.
Lemma D_8439c : decode_any W_8439c = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843a0 : bv 32 := 0xfff78713.
Lemma F_843a0 : fetch_word AsanUbsan.M.loaded_segments (0x843e8 : word) = Some W_843a0.
Proof. vm_refl. Qed.
Lemma D_843a0 : decode_any W_843a0 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843a4 : bv 32 := 0x01277463.
Lemma F_843a4 : fetch_word AsanUbsan.M.loaded_segments (0x843ec : word) = Some W_843a4.
Proof. vm_refl. Qed.
Lemma D_843a4 : decode_any W_843a4 = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843ac : bv 32 := 0x000e0697.
Lemma F_843ac : fetch_word AsanUbsan.M.loaded_segments (0x843f4 : word) = Some W_843ac.
Proof. vm_refl. Qed.
Lemma D_843ac : decode_any W_843ac = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843b0 : bv 32 := 0x13c6b683.
Lemma F_843b0 : fetch_word AsanUbsan.M.loaded_segments (0x843f8 : word) = Some W_843b0.
Proof. vm_refl. Qed.
Lemma D_843b0 : decode_any W_843b0 = Some (Load SZ8 true 13 13 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843b4 : bv 32 := 0x0006b883.
Lemma F_843b4 : fetch_word AsanUbsan.M.loaded_segments (0x843fc : word) = Some W_843b4.
Proof. vm_refl. Qed.
Lemma D_843b4 : decode_any W_843b4 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843b8 : bv 32 := 0x0038d693.
Lemma F_843b8 : fetch_word AsanUbsan.M.loaded_segments (0x84400 : word) = Some W_843b8.
Proof. vm_refl. Qed.
Lemma D_843b8 : decode_any W_843b8 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843bc : bv 32 := 0x00b68833.
Lemma F_843bc : fetch_word AsanUbsan.M.loaded_segments (0x84404 : word) = Some W_843bc.
Proof. vm_refl. Qed.
Lemma D_843bc : decode_any W_843bc = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843c0 : bv 32 := 0x1328e463.
Lemma F_843c0 : fetch_word AsanUbsan.M.loaded_segments (0x84408 : word) = Some W_843c0.
Proof. vm_refl. Qed.
Lemma D_843c0 : decode_any W_843c0 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843c4 : bv 32 := 0x13287263.
Lemma F_843c4 : fetch_word AsanUbsan.M.loaded_segments (0x8440c : word) = Some W_843c4.
Proof. vm_refl. Qed.
Lemma D_843c4 : decode_any W_843c4 = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843c8 : bv 32 := 0x23247863.
Lemma F_843c8 : fetch_word AsanUbsan.M.loaded_segments (0x84410 : word) = Some W_843c8.
Proof. vm_refl. Qed.
Lemma D_843c8 : decode_any W_843c8 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843cc : bv 32 := 0x00740513.
Lemma F_843cc : fetch_word AsanUbsan.M.loaded_segments (0x84414 : word) = Some W_843cc.
Proof. vm_refl. Qed.
Lemma D_843cc : decode_any W_843cc = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843d0 : bv 32 := 0xff857513.
Lemma F_843d0 : fetch_word AsanUbsan.M.loaded_segments (0x84418 : word) = Some W_843d0.
Proof. vm_refl. Qed.
Lemma D_843d0 : decode_any W_843d0 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843d4 : bv 32 := 0xff897a13.
Lemma F_843d4 : fetch_word AsanUbsan.M.loaded_segments (0x8441c : word) = Some W_843d4.
Proof. vm_refl. Qed.
Lemma D_843d4 : decode_any W_843d4 = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843d8 : bv 32 := 0xa91ff0ef.
Lemma F_843d8 : fetch_word AsanUbsan.M.loaded_segments (0x84420 : word) = Some W_843d8.
Proof. vm_refl. Qed.
Lemma D_843d8 : decode_any W_843d8 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843dc : bv 32 := 0x00050993.
Lemma F_843dc : fetch_word AsanUbsan.M.loaded_segments (0x84424 : word) = Some W_843dc.
Proof. vm_refl. Qed.
Lemma D_843dc : decode_any W_843dc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843e0 : bv 32 := 0x000a0513.
Lemma F_843e0 : fetch_word AsanUbsan.M.loaded_segments (0x84428 : word) = Some W_843e0.
Proof. vm_refl. Qed.
Lemma D_843e0 : decode_any W_843e0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843e4 : bv 32 := 0xa85ff0ef.
Lemma F_843e4 : fetch_word AsanUbsan.M.loaded_segments (0x8442c : word) = Some W_843e4.
Proof. vm_refl. Qed.
Lemma D_843e4 : decode_any W_843e4 = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843e8 : bv 32 := 0x000ab583.
Lemma F_843e8 : fetch_word AsanUbsan.M.loaded_segments (0x84430 : word) = Some W_843e8.
Proof. vm_refl. Qed.
Lemma D_843e8 : decode_any W_843e8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843ec : bv 32 := 0x00345613.
Lemma F_843ec : fetch_word AsanUbsan.M.loaded_segments (0x84434 : word) = Some W_843ec.
Proof. vm_refl. Qed.
Lemma D_843ec : decode_any W_843ec = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843f0 : bv 32 := 0x00c58633.
Lemma F_843f0 : fetch_word AsanUbsan.M.loaded_segments (0x84438 : word) = Some W_843f0.
Proof. vm_refl. Qed.
Lemma D_843f0 : decode_any W_843f0 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843f4 : bv 32 := 0x00060603.
Lemma F_843f4 : fetch_word AsanUbsan.M.loaded_segments (0x8443c : word) = Some W_843f4.
Proof. vm_refl. Qed.
Lemma D_843f4 : decode_any W_843f4 = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843f8 : bv 32 := 0x00060663.
Lemma F_843f8 : fetch_word AsanUbsan.M.loaded_segments (0x84440 : word) = Some W_843f8.
Proof. vm_refl. Qed.
Lemma D_843f8 : decode_any W_843f8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_843fc : bv 32 := 0x00747693.
Lemma F_843fc : fetch_word AsanUbsan.M.loaded_segments (0x84444 : word) = Some W_843fc.
Proof. vm_refl. Qed.
Lemma D_843fc : decode_any W_843fc = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84400 : bv 32 := 0x02c6d063.
Lemma F_84400 : fetch_word AsanUbsan.M.loaded_segments (0x84448 : word) = Some W_84400.
Proof. vm_refl. Qed.
Lemma D_84400 : decode_any W_84400 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84404 : bv 32 := 0xfff90913.
Lemma F_84404 : fetch_word AsanUbsan.M.loaded_segments (0x8444c : word) = Some W_84404.
Proof. vm_refl. Qed.
Lemma D_84404 : decode_any W_84404 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84408 : bv 32 := 0x00395613.
Lemma F_84408 : fetch_word AsanUbsan.M.loaded_segments (0x84450 : word) = Some W_84408.
Proof. vm_refl. Qed.
Lemma D_84408 : decode_any W_84408 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8440c : bv 32 := 0x00c585b3.
Lemma F_8440c : fetch_word AsanUbsan.M.loaded_segments (0x84454 : word) = Some W_8440c.
Proof. vm_refl. Qed.
Lemma D_8440c : decode_any W_8440c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84410 : bv 32 := 0x00058583.
Lemma F_84410 : fetch_word AsanUbsan.M.loaded_segments (0x84458 : word) = Some W_84410.
Proof. vm_refl. Qed.
Lemma D_84410 : decode_any W_84410 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84414 : bv 32 := 0x04058263.
Lemma F_84414 : fetch_word AsanUbsan.M.loaded_segments (0x8445c : word) = Some W_84414.
Proof. vm_refl. Qed.
Lemma D_84414 : decode_any W_84414 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84418 : bv 32 := 0x00797613.
Lemma F_84418 : fetch_word AsanUbsan.M.loaded_segments (0x84460 : word) = Some W_84418.
Proof. vm_refl. Qed.
Lemma D_84418 : decode_any W_84418 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8441c : bv 32 := 0x02b64e63.
Lemma F_8441c : fetch_word AsanUbsan.M.loaded_segments (0x84464 : word) = Some W_8441c.
Proof. vm_refl. Qed.
Lemma D_8441c : decode_any W_8441c = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84458 : bv 32 := 0x00a9fa63.
Lemma F_84458 : fetch_word AsanUbsan.M.loaded_segments (0x844a0 : word) = Some W_84458.
Proof. vm_refl. Qed.
Lemma D_84458 : decode_any W_84458 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8445c : bv 32 := 0x413505b3.
Lemma F_8445c : fetch_word AsanUbsan.M.loaded_segments (0x844a4 : word) = Some W_8445c.
Proof. vm_refl. Qed.
Lemma D_8445c : decode_any W_8445c = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84460 : bv 32 := 0x00098513.
Lemma F_84460 : fetch_word AsanUbsan.M.loaded_segments (0x844a8 : word) = Some W_84460.
Proof. vm_refl. Qed.
Lemma D_84460 : decode_any W_84460 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84464 : bv 32 := 0x37c100ef.
Lemma F_84464 : fetch_word AsanUbsan.M.loaded_segments (0x844ac : word) = Some W_84464.
Proof. vm_refl. Qed.
Lemma D_84464 : decode_any W_84464 = Some (Jal 1 66428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84468 : bv 32 := 0xfa050ce3.
Lemma F_84468 : fetch_word AsanUbsan.M.loaded_segments (0x844b0 : word) = Some W_84468.
Proof. vm_refl. Qed.
Lemma D_84468 : decode_any W_84468 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8446c : bv 32 := 0x00000413.
Lemma F_8446c : fetch_word AsanUbsan.M.loaded_segments (0x844b4 : word) = Some W_8446c.
Proof. vm_refl. Qed.
Lemma D_8446c : decode_any W_8446c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84470 : bv 32 := 0x00040513.
Lemma F_84470 : fetch_word AsanUbsan.M.loaded_segments (0x844b8 : word) = Some W_84470.
Proof. vm_refl. Qed.
Lemma D_84470 : decode_any W_84470 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84474 : bv 32 := 0x03813083.
Lemma F_84474 : fetch_word AsanUbsan.M.loaded_segments (0x844bc : word) = Some W_84474.
Proof. vm_refl. Qed.
Lemma D_84474 : decode_any W_84474 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84478 : bv 32 := 0x03013403.
Lemma F_84478 : fetch_word AsanUbsan.M.loaded_segments (0x844c0 : word) = Some W_84478.
Proof. vm_refl. Qed.
Lemma D_84478 : decode_any W_84478 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8447c : bv 32 := 0x02813483.
Lemma F_8447c : fetch_word AsanUbsan.M.loaded_segments (0x844c4 : word) = Some W_8447c.
Proof. vm_refl. Qed.
Lemma D_8447c : decode_any W_8447c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84480 : bv 32 := 0x02013903.
Lemma F_84480 : fetch_word AsanUbsan.M.loaded_segments (0x844c8 : word) = Some W_84480.
Proof. vm_refl. Qed.
Lemma D_84480 : decode_any W_84480 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84484 : bv 32 := 0x01813983.
Lemma F_84484 : fetch_word AsanUbsan.M.loaded_segments (0x844cc : word) = Some W_84484.
Proof. vm_refl. Qed.
Lemma D_84484 : decode_any W_84484 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84488 : bv 32 := 0x01013a03.
Lemma F_84488 : fetch_word AsanUbsan.M.loaded_segments (0x844d0 : word) = Some W_84488.
Proof. vm_refl. Qed.
Lemma D_84488 : decode_any W_84488 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8448c : bv 32 := 0x00813a83.
Lemma F_8448c : fetch_word AsanUbsan.M.loaded_segments (0x844d4 : word) = Some W_8448c.
Proof. vm_refl. Qed.
Lemma D_8448c : decode_any W_8448c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84490 : bv 32 := 0x04010113.
Lemma F_84490 : fetch_word AsanUbsan.M.loaded_segments (0x844d8 : word) = Some W_84490.
Proof. vm_refl. Qed.
Lemma D_84490 : decode_any W_84490 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84494 : bv 32 := 0x00008067.
Lemma F_84494 : fetch_word AsanUbsan.M.loaded_segments (0x844dc : word) = Some W_84494.
Proof. vm_refl. Qed.
Lemma D_84494 : decode_any W_84494 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84c2c : bv 32 := 0xfb010113.
Lemma F_84c2c : fetch_word AsanUbsan.M.loaded_segments (0x84c74 : word) = Some W_84c2c.
Proof. vm_refl. Qed.
Lemma D_84c2c : decode_any W_84c2c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84c30 : bv 32 := 0x04113423.
Lemma F_84c30 : fetch_word AsanUbsan.M.loaded_segments (0x84c78 : word) = Some W_84c30.
Proof. vm_refl. Qed.
Lemma D_84c30 : decode_any W_84c30 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84c34 : bv 32 := 0x04813023.
Lemma F_84c34 : fetch_word AsanUbsan.M.loaded_segments (0x84c7c : word) = Some W_84c34.
Proof. vm_refl. Qed.
Lemma D_84c34 : decode_any W_84c34 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84c38 : bv 32 := 0x000e0517.
Lemma F_84c38 : fetch_word AsanUbsan.M.loaded_segments (0x84c80 : word) = Some W_84c38.
Proof. vm_refl. Qed.
Lemma D_84c38 : decode_any W_84c38 = Some (Auipc 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84c3c : bv 32 := 0x8d853503.
Lemma F_84c3c : fetch_word AsanUbsan.M.loaded_segments (0x84c84 : word) = Some W_84c3c.
Proof. vm_refl. Qed.
Lemma D_84c3c : decode_any W_84c3c = Some (Load SZ8 true 10 10 2264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84c40 : bv 32 := 0x0a051463.
Lemma F_84c40 : fetch_word AsanUbsan.M.loaded_segments (0x84c88 : word) = Some W_84c40.
Proof. vm_refl. Qed.
Lemma D_84c40 : decode_any W_84c40 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84ce8 : bv 32 := 0x00000513.
Lemma F_84ce8 : fetch_word AsanUbsan.M.loaded_segments (0x84d30 : word) = Some W_84ce8.
Proof. vm_refl. Qed.
Lemma D_84ce8 : decode_any W_84ce8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84cec : bv 32 := 0x04813083.
Lemma F_84cec : fetch_word AsanUbsan.M.loaded_segments (0x84d34 : word) = Some W_84cec.
Proof. vm_refl. Qed.
Lemma D_84cec : decode_any W_84cec = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84cf0 : bv 32 := 0x04013403.
Lemma F_84cf0 : fetch_word AsanUbsan.M.loaded_segments (0x84d38 : word) = Some W_84cf0.
Proof. vm_refl. Qed.
Lemma D_84cf0 : decode_any W_84cf0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84cf4 : bv 32 := 0x05010113.
Lemma F_84cf4 : fetch_word AsanUbsan.M.loaded_segments (0x84d3c : word) = Some W_84cf4.
Proof. vm_refl. Qed.
Lemma D_84cf4 : decode_any W_84cf4 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84cf8 : bv 32 := 0x00008067.
Lemma F_84cf8 : fetch_word AsanUbsan.M.loaded_segments (0x84d40 : word) = Some W_84cf8.
Proof. vm_refl. Qed.
Lemma D_84cf8 : decode_any W_84cf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84d98 : bv 32 := 0x000e8517.
Lemma F_84d98 : fetch_word AsanUbsan.M.loaded_segments (0x84de0 : word) = Some W_84d98.
Proof. vm_refl. Qed.
Lemma D_84d98 : decode_any W_84d98 = Some (Auipc 10 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84d9c : bv 32 := 0x24050513.
Lemma F_84d9c : fetch_word AsanUbsan.M.loaded_segments (0x84de4 : word) = Some W_84d9c.
Proof. vm_refl. Qed.
Lemma D_84d9c : decode_any W_84d9c = Some (OpImm ALU_ADD 10 10 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84da0 : bv 32 := 0x00054583.
Lemma F_84da0 : fetch_word AsanUbsan.M.loaded_segments (0x84de8 : word) = Some W_84da0.
Proof. vm_refl. Qed.
Lemma D_84da0 : decode_any W_84da0 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84da4 : bv 32 := 0x00058663.
Lemma F_84da4 : fetch_word AsanUbsan.M.loaded_segments (0x84dec : word) = Some W_84da4.
Proof. vm_refl. Qed.
Lemma D_84da4 : decode_any W_84da4 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84da8 : bv 32 := 0x00452503.
Lemma F_84da8 : fetch_word AsanUbsan.M.loaded_segments (0x84df0 : word) = Some W_84da8.
Proof. vm_refl. Qed.
Lemma D_84da8 : decode_any W_84da8 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84dac : bv 32 := 0x2f0d406f.
Lemma F_84dac : fetch_word AsanUbsan.M.loaded_segments (0x84df4 : word) = Some W_84dac.
Proof. vm_refl. Qed.
Lemma D_84dac : decode_any W_84dac = Some (Jal 0 869104, 4%Z).
Proof. vm_refl. Qed.

