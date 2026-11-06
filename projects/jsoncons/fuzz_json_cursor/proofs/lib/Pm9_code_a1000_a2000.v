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

Definition W_a1234 : bv 32 := 0xfe010113.
Lemma F_a1234 : fetch_word AsanUbsan.M.loaded_segments (0xa127c : word) = Some W_a1234.
Proof. vm_refl. Qed.
Lemma D_a1234 : decode_any W_a1234 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1238 : bv 32 := 0x00113c23.
Lemma F_a1238 : fetch_word AsanUbsan.M.loaded_segments (0xa1280 : word) = Some W_a1238.
Proof. vm_refl. Qed.
Lemma D_a1238 : decode_any W_a1238 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a123c : bv 32 := 0x00813823.
Lemma F_a123c : fetch_word AsanUbsan.M.loaded_segments (0xa1284 : word) = Some W_a123c.
Proof. vm_refl. Qed.
Lemma D_a123c : decode_any W_a123c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1240 : bv 32 := 0x00060593.
Lemma F_a1240 : fetch_word AsanUbsan.M.loaded_segments (0xa1288 : word) = Some W_a1240.
Proof. vm_refl. Qed.
Lemma D_a1240 : decode_any W_a1240 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1244 : bv 32 := 0x00050413.
Lemma F_a1244 : fetch_word AsanUbsan.M.loaded_segments (0xa128c : word) = Some W_a1244.
Proof. vm_refl. Qed.
Lemma D_a1244 : decode_any W_a1244 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1248 : bv 32 := 0x00d53023.
Lemma F_a1248 : fetch_word AsanUbsan.M.loaded_segments (0xa1290 : word) = Some W_a1248.
Proof. vm_refl. Qed.
Lemma D_a1248 : decode_any W_a1248 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a124c : bv 32 := 0x00013423.
Lemma F_a124c : fetch_word AsanUbsan.M.loaded_segments (0xa1294 : word) = Some W_a124c.
Proof. vm_refl. Qed.
Lemma D_a124c : decode_any W_a124c = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1250 : bv 32 := 0x0018f517.
Lemma F_a1250 : fetch_word AsanUbsan.M.loaded_segments (0xa1298 : word) = Some W_a1250.
Proof. vm_refl. Qed.
Lemma D_a1250 : decode_any W_a1250 = Some (Auipc 10 399, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1254 : bv 32 := 0x93050513.
Lemma F_a1254 : fetch_word AsanUbsan.M.loaded_segments (0xa129c : word) = Some W_a1254.
Proof. vm_refl. Qed.
Lemma D_a1254 : decode_any W_a1254 = Some (OpImm ALU_ADD 10 10 2352, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1258 : bv 32 := 0x00810613.
Lemma F_a1258 : fetch_word AsanUbsan.M.loaded_segments (0xa12a0 : word) = Some W_a1258.
Proof. vm_refl. Qed.
Lemma D_a1258 : decode_any W_a1258 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a125c : bv 32 := 0xcc5fd0ef.
Lemma F_a125c : fetch_word AsanUbsan.M.loaded_segments (0xa12a4 : word) = Some W_a125c.
Proof. vm_refl. Qed.
Lemma D_a125c : decode_any W_a125c = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1260 : bv 32 := 0x00813583.
Lemma F_a1260 : fetch_word AsanUbsan.M.loaded_segments (0xa12a8 : word) = Some W_a1260.
Proof. vm_refl. Qed.
Lemma D_a1260 : decode_any W_a1260 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1264 : bv 32 := 0x00a42623.
Lemma F_a1264 : fetch_word AsanUbsan.M.loaded_segments (0xa12ac : word) = Some W_a1264.
Proof. vm_refl. Qed.
Lemma D_a1264 : decode_any W_a1264 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1268 : bv 32 := 0x00059a63.
Lemma F_a1268 : fetch_word AsanUbsan.M.loaded_segments (0xa12b0 : word) = Some W_a1268.
Proof. vm_refl. Qed.
Lemma D_a1268 : decode_any W_a1268 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a126c : bv 32 := 0x01813083.
Lemma F_a126c : fetch_word AsanUbsan.M.loaded_segments (0xa12b4 : word) = Some W_a126c.
Proof. vm_refl. Qed.
Lemma D_a126c : decode_any W_a126c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1270 : bv 32 := 0x01013403.
Lemma F_a1270 : fetch_word AsanUbsan.M.loaded_segments (0xa12b8 : word) = Some W_a1270.
Proof. vm_refl. Qed.
Lemma D_a1270 : decode_any W_a1270 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1274 : bv 32 := 0x02010113.
Lemma F_a1274 : fetch_word AsanUbsan.M.loaded_segments (0xa12bc : word) = Some W_a1274.
Proof. vm_refl. Qed.
Lemma D_a1274 : decode_any W_a1274 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1278 : bv 32 := 0x00008067.
Lemma F_a1278 : fetch_word AsanUbsan.M.loaded_segments (0xa12c0 : word) = Some W_a1278.
Proof. vm_refl. Qed.
Lemma D_a1278 : decode_any W_a1278 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a151c : bv 32 := 0x00058613.
Lemma F_a151c : fetch_word AsanUbsan.M.loaded_segments (0xa1564 : word) = Some W_a151c.
Proof. vm_refl. Qed.
Lemma D_a151c : decode_any W_a151c = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1520 : bv 32 := 0x0019e597.
Lemma F_a1520 : fetch_word AsanUbsan.M.loaded_segments (0xa1568 : word) = Some W_a1520.
Proof. vm_refl. Qed.
Lemma D_a1520 : decode_any W_a1520 = Some (Auipc 11 414, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1524 : bv 32 := 0x67058593.
Lemma F_a1524 : fetch_word AsanUbsan.M.loaded_segments (0xa156c : word) = Some W_a1524.
Proof. vm_refl. Qed.
Lemma D_a1524 : decode_any W_a1524 = Some (OpImm ALU_ADD 11 11 1648, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1528 : bv 32 := 0x00050693.
Lemma F_a1528 : fetch_word AsanUbsan.M.loaded_segments (0xa1570 : word) = Some W_a1528.
Proof. vm_refl. Qed.
Lemma D_a1528 : decode_any W_a1528 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a152c : bv 32 := 0x00058513.
Lemma F_a152c : fetch_word AsanUbsan.M.loaded_segments (0xa1574 : word) = Some W_a152c.
Proof. vm_refl. Qed.
Lemma D_a152c : decode_any W_a152c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1530 : bv 32 := 0x00068593.
Lemma F_a1530 : fetch_word AsanUbsan.M.loaded_segments (0xa1578 : word) = Some W_a1530.
Proof. vm_refl. Qed.
Lemma D_a1530 : decode_any W_a1530 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1534 : bv 32 := 0x00000693.
Lemma F_a1534 : fetch_word AsanUbsan.M.loaded_segments (0xa157c : word) = Some W_a1534.
Proof. vm_refl. Qed.
Lemma D_a1534 : decode_any W_a1534 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1538 : bv 32 := 0x0040006f.
Lemma F_a1538 : fetch_word AsanUbsan.M.loaded_segments (0xa1580 : word) = Some W_a1538.
Proof. vm_refl. Qed.
Lemma D_a1538 : decode_any W_a1538 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a153c : bv 32 := 0xf9010113.
Lemma F_a153c : fetch_word AsanUbsan.M.loaded_segments (0xa1584 : word) = Some W_a153c.
Proof. vm_refl. Qed.
Lemma D_a153c : decode_any W_a153c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1540 : bv 32 := 0x06113423.
Lemma F_a1540 : fetch_word AsanUbsan.M.loaded_segments (0xa1588 : word) = Some W_a1540.
Proof. vm_refl. Qed.
Lemma D_a1540 : decode_any W_a1540 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1544 : bv 32 := 0x06813023.
Lemma F_a1544 : fetch_word AsanUbsan.M.loaded_segments (0xa158c : word) = Some W_a1544.
Proof. vm_refl. Qed.
Lemma D_a1544 : decode_any W_a1544 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1548 : bv 32 := 0x04913c23.
Lemma F_a1548 : fetch_word AsanUbsan.M.loaded_segments (0xa1590 : word) = Some W_a1548.
Proof. vm_refl. Qed.
Lemma D_a1548 : decode_any W_a1548 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a154c : bv 32 := 0x05213823.
Lemma F_a154c : fetch_word AsanUbsan.M.loaded_segments (0xa1594 : word) = Some W_a154c.
Proof. vm_refl. Qed.
Lemma D_a154c : decode_any W_a154c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1550 : bv 32 := 0x05313423.
Lemma F_a1550 : fetch_word AsanUbsan.M.loaded_segments (0xa1598 : word) = Some W_a1550.
Proof. vm_refl. Qed.
Lemma D_a1550 : decode_any W_a1550 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1554 : bv 32 := 0x05413023.
Lemma F_a1554 : fetch_word AsanUbsan.M.loaded_segments (0xa159c : word) = Some W_a1554.
Proof. vm_refl. Qed.
Lemma D_a1554 : decode_any W_a1554 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1558 : bv 32 := 0x03513c23.
Lemma F_a1558 : fetch_word AsanUbsan.M.loaded_segments (0xa15a0 : word) = Some W_a1558.
Proof. vm_refl. Qed.
Lemma D_a1558 : decode_any W_a1558 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a155c : bv 32 := 0x03613823.
Lemma F_a155c : fetch_word AsanUbsan.M.loaded_segments (0xa15a4 : word) = Some W_a155c.
Proof. vm_refl. Qed.
Lemma D_a155c : decode_any W_a155c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1560 : bv 32 := 0x03713423.
Lemma F_a1560 : fetch_word AsanUbsan.M.loaded_segments (0xa15a8 : word) = Some W_a1560.
Proof. vm_refl. Qed.
Lemma D_a1560 : decode_any W_a1560 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1564 : bv 32 := 0x03813023.
Lemma F_a1564 : fetch_word AsanUbsan.M.loaded_segments (0xa15ac : word) = Some W_a1564.
Proof. vm_refl. Qed.
Lemma D_a1564 : decode_any W_a1564 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1568 : bv 32 := 0x01913c23.
Lemma F_a1568 : fetch_word AsanUbsan.M.loaded_segments (0xa15b0 : word) = Some W_a1568.
Proof. vm_refl. Qed.
Lemma D_a1568 : decode_any W_a1568 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a156c : bv 32 := 0x00068413.
Lemma F_a156c : fetch_word AsanUbsan.M.loaded_segments (0xa15b4 : word) = Some W_a156c.
Proof. vm_refl. Qed.
Lemma D_a156c : decode_any W_a156c = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1570 : bv 32 := 0x00050493.
Lemma F_a1570 : fetch_word AsanUbsan.M.loaded_segments (0xa15b8 : word) = Some W_a1570.
Proof. vm_refl. Qed.
Lemma D_a1570 : decode_any W_a1570 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1574 : bv 32 := 0x00b13423.
Lemma F_a1574 : fetch_word AsanUbsan.M.loaded_segments (0xa15bc : word) = Some W_a1574.
Proof. vm_refl. Qed.
Lemma D_a1574 : decode_any W_a1574 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1578 : bv 32 := 0x00c13823.
Lemma F_a1578 : fetch_word AsanUbsan.M.loaded_segments (0xa15c0 : word) = Some W_a1578.
Proof. vm_refl. Qed.
Lemma D_a1578 : decode_any W_a1578 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a157c : bv 32 := 0x00068463.
Lemma F_a157c : fetch_word AsanUbsan.M.loaded_segments (0xa15c4 : word) = Some W_a157c.
Proof. vm_refl. Qed.
Lemma D_a157c : decode_any W_a157c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1584 : bv 32 := 0x0006069b.
Lemma F_a1584 : fetch_word AsanUbsan.M.loaded_segments (0xa15cc : word) = Some W_a1584.
Proof. vm_refl. Qed.
Lemma D_a1584 : decode_any W_a1584 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1588 : bv 32 := 0x00000513.
Lemma F_a1588 : fetch_word AsanUbsan.M.loaded_segments (0xa15d0 : word) = Some W_a1588.
Proof. vm_refl. Qed.
Lemma D_a1588 : decode_any W_a1588 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a158c : bv 32 := 0x1c068a63.
Lemma F_a158c : fetch_word AsanUbsan.M.loaded_segments (0xa15d4 : word) = Some W_a158c.
Proof. vm_refl. Qed.
Lemma D_a158c : decode_any W_a158c = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1590 : bv 32 := 0x1c058863.
Lemma F_a1590 : fetch_word AsanUbsan.M.loaded_segments (0xa15d8 : word) = Some W_a1590.
Proof. vm_refl. Qed.
Lemma D_a1590 : decode_any W_a1590 = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1594 : bv 32 := 0x02065693.
Lemma F_a1594 : fetch_word AsanUbsan.M.loaded_segments (0xa15dc : word) = Some W_a1594.
Proof. vm_refl. Qed.
Lemma D_a1594 : decode_any W_a1594 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1598 : bv 32 := 0xfff00513.
Lemma F_a1598 : fetch_word AsanUbsan.M.loaded_segments (0xa15e0 : word) = Some W_a1598.
Proof. vm_refl. Qed.
Lemma D_a1598 : decode_any W_a1598 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a159c : bv 32 := 0xfff6f717.
Lemma F_a159c : fetch_word AsanUbsan.M.loaded_segments (0xa15e4 : word) = Some W_a159c.
Proof. vm_refl. Qed.
Lemma D_a159c : decode_any W_a159c = Some (Auipc 14 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15a0 : bv 32 := 0xfff6f797.
Lemma F_a15a0 : fetch_word AsanUbsan.M.loaded_segments (0xa15e8 : word) = Some W_a15a0.
Proof. vm_refl. Qed.
Lemma D_a15a0 : decode_any W_a15a0 = Some (Auipc 15 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15a4 : bv 32 := 0x02055513.
Lemma F_a15a4 : fetch_word AsanUbsan.M.loaded_segments (0xa15ec : word) = Some W_a15a4.
Proof. vm_refl. Qed.
Lemma D_a15a4 : decode_any W_a15a4 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15a8 : bv 32 := 0xd407b783.
Lemma F_a15a8 : fetch_word AsanUbsan.M.loaded_segments (0xa15f0 : word) = Some W_a15a8.
Proof. vm_refl. Qed.
Lemma D_a15a8 : decode_any W_a15a8 = Some (Load SZ8 true 15 15 3392, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15ac : bv 32 := 0x00a67633.
Lemma F_a15ac : fetch_word AsanUbsan.M.loaded_segments (0xa15f4 : word) = Some W_a15ac.
Proof. vm_refl. Qed.
Lemma D_a15ac : decode_any W_a15ac = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15b0 : bv 32 := 0xfff6f517.
Lemma F_a15b0 : fetch_word AsanUbsan.M.loaded_segments (0xa15f8 : word) = Some W_a15b0.
Proof. vm_refl. Qed.
Lemma D_a15b0 : decode_any W_a15b0 = Some (Auipc 10 1048431, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15b4 : bv 32 := 0xe5853803.
Lemma F_a15b4 : fetch_word AsanUbsan.M.loaded_segments (0xa15fc : word) = Some W_a15b4.
Proof. vm_refl. Qed.
Lemma D_a15b4 : decode_any W_a15b4 = Some (Load SZ8 true 16 10 3672, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15b8 : bv 32 := 0xd0473503.
Lemma F_a15b8 : fetch_word AsanUbsan.M.loaded_segments (0xa1600 : word) = Some W_a15b8.
Proof. vm_refl. Qed.
Lemma D_a15b8 : decode_any W_a15b8 = Some (Load SZ8 true 10 14 3332, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15bc : bv 32 := 0x02f60733.
Lemma F_a15bc : fetch_word AsanUbsan.M.loaded_segments (0xa1604 : word) = Some W_a15bc.
Proof. vm_refl. Qed.
Lemma D_a15bc : decode_any W_a15bc = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15c0 : bv 32 := 0x00361793.
Lemma F_a15c0 : fetch_word AsanUbsan.M.loaded_segments (0xa1608 : word) = Some W_a15c0.
Proof. vm_refl. Qed.
Lemma D_a15c0 : decode_any W_a15c0 = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15c4 : bv 32 := 0x01074633.
Lemma F_a15c4 : fetch_word AsanUbsan.M.loaded_segments (0xa160c : word) = Some W_a15c4.
Proof. vm_refl. Qed.
Lemma D_a15c4 : decode_any W_a15c4 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15c8 : bv 32 := 0x00f58733.
Lemma F_a15c8 : fetch_word AsanUbsan.M.loaded_segments (0xa1610 : word) = Some W_a15c8.
Proof. vm_refl. Qed.
Lemma D_a15c8 : decode_any W_a15c8 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15cc : bv 32 := 0x0005b783.
Lemma F_a15cc : fetch_word AsanUbsan.M.loaded_segments (0xa1614 : word) = Some W_a15cc.
Proof. vm_refl. Qed.
Lemma D_a15cc : decode_any W_a15cc = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15d0 : bv 32 := 0x00858593.
Lemma F_a15d0 : fetch_word AsanUbsan.M.loaded_segments (0xa1618 : word) = Some W_a15d0.
Proof. vm_refl. Qed.
Lemma D_a15d0 : decode_any W_a15d0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15d4 : bv 32 := 0x02a787b3.
Lemma F_a15d4 : fetch_word AsanUbsan.M.loaded_segments (0xa161c : word) = Some W_a15d4.
Proof. vm_refl. Qed.
Lemma D_a15d4 : decode_any W_a15d4 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15d8 : bv 32 := 0x02f7d813.
Lemma F_a15d8 : fetch_word AsanUbsan.M.loaded_segments (0xa1620 : word) = Some W_a15d8.
Proof. vm_refl. Qed.
Lemma D_a15d8 : decode_any W_a15d8 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15dc : bv 32 := 0x00f847b3.
Lemma F_a15dc : fetch_word AsanUbsan.M.loaded_segments (0xa1624 : word) = Some W_a15dc.
Proof. vm_refl. Qed.
Lemma D_a15dc : decode_any W_a15dc = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15e0 : bv 32 := 0x02a787b3.
Lemma F_a15e0 : fetch_word AsanUbsan.M.loaded_segments (0xa1628 : word) = Some W_a15e0.
Proof. vm_refl. Qed.
Lemma D_a15e0 : decode_any W_a15e0 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15e4 : bv 32 := 0x00c7c633.
Lemma F_a15e4 : fetch_word AsanUbsan.M.loaded_segments (0xa162c : word) = Some W_a15e4.
Proof. vm_refl. Qed.
Lemma D_a15e4 : decode_any W_a15e4 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15e8 : bv 32 := 0x02a60633.
Lemma F_a15e8 : fetch_word AsanUbsan.M.loaded_segments (0xa1630 : word) = Some W_a15e8.
Proof. vm_refl. Qed.
Lemma D_a15e8 : decode_any W_a15e8 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15ec : bv 32 := 0xfee590e3.
Lemma F_a15ec : fetch_word AsanUbsan.M.loaded_segments (0xa1634 : word) = Some W_a15ec.
Proof. vm_refl. Qed.
Lemma D_a15ec : decode_any W_a15ec = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15f0 : bv 32 := 0x00010b37.
Lemma F_a15f0 : fetch_word AsanUbsan.M.loaded_segments (0xa1638 : word) = Some W_a15f0.
Proof. vm_refl. Qed.
Lemma D_a15f0 : decode_any W_a15f0 = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15f4 : bv 32 := 0x80000bb7.
Lemma F_a15f4 : fetch_word AsanUbsan.M.loaded_segments (0xa163c : word) = Some W_a15f4.
Proof. vm_refl. Qed.
Lemma D_a15f4 : decode_any W_a15f4 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15f8 : bv 32 := 0x02a685b3.
Lemma F_a15f8 : fetch_word AsanUbsan.M.loaded_segments (0xa1640 : word) = Some W_a15f8.
Proof. vm_refl. Qed.
Lemma D_a15f8 : decode_any W_a15f8 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15fc : bv 32 := 0x004006b7.
Lemma F_a15fc : fetch_word AsanUbsan.M.loaded_segments (0xa1644 : word) = Some W_a15fc.
Proof. vm_refl. Qed.
Lemma D_a15fc : decode_any W_a15fc = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1600 : bv 32 := 0xfffb0b1b.
Lemma F_a1600 : fetch_word AsanUbsan.M.loaded_segments (0xa1648 : word) = Some W_a1600.
Proof. vm_refl. Qed.
Lemma D_a1600 : decode_any W_a1600 = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1604 : bv 32 := 0xfffb8b9b.
Lemma F_a1604 : fetch_word AsanUbsan.M.loaded_segments (0xa164c : word) = Some W_a1604.
Proof. vm_refl. Qed.
Lemma D_a1604 : decode_any W_a1604 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1608 : bv 32 := 0x02f5d713.
Lemma F_a1608 : fetch_word AsanUbsan.M.loaded_segments (0xa1650 : word) = Some W_a1608.
Proof. vm_refl. Qed.
Lemma D_a1608 : decode_any W_a1608 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a160c : bv 32 := 0x00b745b3.
Lemma F_a160c : fetch_word AsanUbsan.M.loaded_segments (0xa1654 : word) = Some W_a160c.
Proof. vm_refl. Qed.
Lemma D_a160c : decode_any W_a160c = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1610 : bv 32 := 0x02a585b3.
Lemma F_a1610 : fetch_word AsanUbsan.M.loaded_segments (0xa1658 : word) = Some W_a1610.
Proof. vm_refl. Qed.
Lemma D_a1610 : decode_any W_a1610 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1614 : bv 32 := 0x00c5c5b3.
Lemma F_a1614 : fetch_word AsanUbsan.M.loaded_segments (0xa165c : word) = Some W_a1614.
Proof. vm_refl. Qed.
Lemma D_a1614 : decode_any W_a1614 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1618 : bv 32 := 0x02a585b3.
Lemma F_a1618 : fetch_word AsanUbsan.M.loaded_segments (0xa1660 : word) = Some W_a1618.
Proof. vm_refl. Qed.
Lemma D_a1618 : decode_any W_a1618 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a161c : bv 32 := 0x02f5d613.
Lemma F_a161c : fetch_word AsanUbsan.M.loaded_segments (0xa1664 : word) = Some W_a161c.
Proof. vm_refl. Qed.
Lemma D_a161c : decode_any W_a161c = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1620 : bv 32 := 0x00b645b3.
Lemma F_a1620 : fetch_word AsanUbsan.M.loaded_segments (0xa1668 : word) = Some W_a1620.
Proof. vm_refl. Qed.
Lemma D_a1620 : decode_any W_a1620 = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1624 : bv 32 := 0x02a58533.
Lemma F_a1624 : fetch_word AsanUbsan.M.loaded_segments (0xa166c : word) = Some W_a1624.
Proof. vm_refl. Qed.
Lemma D_a1624 : decode_any W_a1624 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1628 : bv 32 := 0x02f55593.
Lemma F_a1628 : fetch_word AsanUbsan.M.loaded_segments (0xa1670 : word) = Some W_a1628.
Proof. vm_refl. Qed.
Lemma D_a1628 : decode_any W_a1628 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a162c : bv 32 := 0x00a5c9b3.
Lemma F_a162c : fetch_word AsanUbsan.M.loaded_segments (0xa1674 : word) = Some W_a162c.
Proof. vm_refl. Qed.
Lemma D_a162c : decode_any W_a162c = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1630 : bv 32 := 0x02c99513.
Lemma F_a1630 : fetch_word AsanUbsan.M.loaded_segments (0xa1678 : word) = Some W_a1630.
Proof. vm_refl. Qed.
Lemma D_a1630 : decode_any W_a1630 = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1634 : bv 32 := 0x02a55513.
Lemma F_a1634 : fetch_word AsanUbsan.M.loaded_segments (0xa167c : word) = Some W_a1634.
Proof. vm_refl. Qed.
Lemma D_a1634 : decode_any W_a1634 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1638 : bv 32 := 0x00a48933.
Lemma F_a1638 : fetch_word AsanUbsan.M.loaded_segments (0xa1680 : word) = Some W_a1638.
Proof. vm_refl. Qed.
Lemma D_a1638 : decode_any W_a1638 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a163c : bv 32 := 0x00092503.
Lemma F_a163c : fetch_word AsanUbsan.M.loaded_segments (0xa1684 : word) = Some W_a163c.
Proof. vm_refl. Qed.
Lemma D_a163c : decode_any W_a163c = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1640 : bv 32 := 0x01068c1b.
Lemma F_a1640 : fetch_word AsanUbsan.M.loaded_segments (0xa1688 : word) = Some W_a1640.
Proof. vm_refl. Qed.
Lemma D_a1640 : decode_any W_a1640 = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1644 : bv 32 := 0x01848c33.
Lemma F_a1644 : fetch_word AsanUbsan.M.loaded_segments (0xa168c : word) = Some W_a1644.
Proof. vm_refl. Qed.
Lemma D_a1644 : decode_any W_a1644 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1648 : bv 32 := 0x0230000f.
Lemma F_a1648 : fetch_word AsanUbsan.M.loaded_segments (0xa1690 : word) = Some W_a1648.
Proof. vm_refl. Qed.
Lemma D_a1648 : decode_any W_a1648 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a164c : bv 32 := 0x01757cb3.
Lemma F_a164c : fetch_word AsanUbsan.M.loaded_segments (0xa1694 : word) = Some W_a164c.
Proof. vm_refl. Qed.
Lemma D_a164c : decode_any W_a164c = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1650 : bv 32 := 0x0086869b.
Lemma F_a1650 : fetch_word AsanUbsan.M.loaded_segments (0xa1698 : word) = Some W_a1650.
Proof. vm_refl. Qed.
Lemma D_a1650 : decode_any W_a1650 = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1654 : bv 32 := 0x00d48a33.
Lemma F_a1654 : fetch_word AsanUbsan.M.loaded_segments (0xa169c : word) = Some W_a1654.
Proof. vm_refl. Qed.
Lemma D_a1654 : decode_any W_a1654 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1658 : bv 32 := 0x000c8593.
Lemma F_a1658 : fetch_word AsanUbsan.M.loaded_segments (0xa16a0 : word) = Some W_a1658.
Proof. vm_refl. Qed.
Lemma D_a1658 : decode_any W_a1658 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a165c : bv 32 := 0x04058c63.
Lemma F_a165c : fetch_word AsanUbsan.M.loaded_segments (0xa16a4 : word) = Some W_a165c.
Proof. vm_refl. Qed.
Lemma D_a165c : decode_any W_a165c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1660 : bv 32 := 0x00058513.
Lemma F_a1660 : fetch_word AsanUbsan.M.loaded_segments (0xa16a8 : word) = Some W_a1660.
Proof. vm_refl. Qed.
Lemma D_a1660 : decode_any W_a1660 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1664 : bv 32 := 0x0105d59b.
Lemma F_a1664 : fetch_word AsanUbsan.M.loaded_segments (0xa16ac : word) = Some W_a1664.
Proof. vm_refl. Qed.
Lemma D_a1664 : decode_any W_a1664 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1668 : bv 32 := 0x00359613.
Lemma F_a1668 : fetch_word AsanUbsan.M.loaded_segments (0xa16b0 : word) = Some W_a1668.
Proof. vm_refl. Qed.
Lemma D_a1668 : decode_any W_a1668 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a166c : bv 32 := 0x00cc0633.
Lemma F_a166c : fetch_word AsanUbsan.M.loaded_segments (0xa16b4 : word) = Some W_a166c.
Proof. vm_refl. Qed.
Lemma D_a166c : decode_any W_a166c = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1670 : bv 32 := 0x00063603.
Lemma F_a1670 : fetch_word AsanUbsan.M.loaded_segments (0xa16b8 : word) = Some W_a1670.
Proof. vm_refl. Qed.
Lemma D_a1670 : decode_any W_a1670 = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1674 : bv 32 := 0x02060463.
Lemma F_a1674 : fetch_word AsanUbsan.M.loaded_segments (0xa16bc : word) = Some W_a1674.
Proof. vm_refl. Qed.
Lemma D_a1674 : decode_any W_a1674 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1678 : bv 32 := 0x02051593.
Lemma F_a1678 : fetch_word AsanUbsan.M.loaded_segments (0xa16c0 : word) = Some W_a1678.
Proof. vm_refl. Qed.
Lemma D_a1678 : decode_any W_a1678 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a167c : bv 32 := 0x0205d593.
Lemma F_a167c : fetch_word AsanUbsan.M.loaded_segments (0xa16c4 : word) = Some W_a167c.
Proof. vm_refl. Qed.
Lemma D_a167c : decode_any W_a167c = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1680 : bv 32 := 0x0165f5b3.
Lemma F_a1680 : fetch_word AsanUbsan.M.loaded_segments (0xa16c8 : word) = Some W_a1680.
Proof. vm_refl. Qed.
Lemma D_a1680 : decode_any W_a1680 = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1684 : bv 32 := 0x00459593.
Lemma F_a1684 : fetch_word AsanUbsan.M.loaded_segments (0xa16cc : word) = Some W_a1684.
Proof. vm_refl. Qed.
Lemma D_a1684 : decode_any W_a1684 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1688 : bv 32 := 0x00b605b3.
Lemma F_a1688 : fetch_word AsanUbsan.M.loaded_segments (0xa16d0 : word) = Some W_a1688.
Proof. vm_refl. Qed.
Lemma D_a1688 : decode_any W_a1688 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a168c : bv 32 := 0x0005b603.
Lemma F_a168c : fetch_word AsanUbsan.M.loaded_segments (0xa16d4 : word) = Some W_a168c.
Proof. vm_refl. Qed.
Lemma D_a168c : decode_any W_a168c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1690 : bv 32 := 0x0085a583.
Lemma F_a1690 : fetch_word AsanUbsan.M.loaded_segments (0xa16d8 : word) = Some W_a1690.
Proof. vm_refl. Qed.
Lemma D_a1690 : decode_any W_a1690 = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1694 : bv 32 := 0xfcc994e3.
Lemma F_a1694 : fetch_word AsanUbsan.M.loaded_segments (0xa16dc : word) = Some W_a1694.
Proof. vm_refl. Qed.
Lemma D_a1694 : decode_any W_a1694 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1698 : bv 32 := 0x0c80006f.
Lemma F_a1698 : fetch_word AsanUbsan.M.loaded_segments (0xa16e0 : word) = Some W_a1698.
Proof. vm_refl. Qed.
Lemma D_a1698 : decode_any W_a1698 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16b4 : bv 32 := 0x00090513.
Lemma F_a16b4 : fetch_word AsanUbsan.M.loaded_segments (0xa16fc : word) = Some W_a16b4.
Proof. vm_refl. Qed.
Lemma D_a16b4 : decode_any W_a16b4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16b8 : bv 32 := 0x5f8000ef.
Lemma F_a16b8 : fetch_word AsanUbsan.M.loaded_segments (0xa1700 : word) = Some W_a16b8.
Proof. vm_refl. Qed.
Lemma D_a16b8 : decode_any W_a16b8 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16bc : bv 32 := 0x00050a93.
Lemma F_a16bc : fetch_word AsanUbsan.M.loaded_segments (0xa1704 : word) = Some W_a16bc.
Proof. vm_refl. Qed.
Lemma D_a16bc : decode_any W_a16bc = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16c0 : bv 32 := 0x03950663.
Lemma F_a16c0 : fetch_word AsanUbsan.M.loaded_segments (0xa1708 : word) = Some W_a16c0.
Proof. vm_refl. Qed.
Lemma D_a16c0 : decode_any W_a16c0 = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16ec : bv 32 := 0x00400537.
Lemma F_a16ec : fetch_word AsanUbsan.M.loaded_segments (0xa1734 : word) = Some W_a16ec.
Proof. vm_refl. Qed.
Lemma D_a16ec : decode_any W_a16ec = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16f0 : bv 32 := 0x00a48533.
Lemma F_a16f0 : fetch_word AsanUbsan.M.loaded_segments (0xa1738 : word) = Some W_a16f0.
Proof. vm_refl. Qed.
Lemma D_a16f0 : decode_any W_a16f0 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16f4 : bv 32 := 0x00100593.
Lemma F_a16f4 : fetch_word AsanUbsan.M.loaded_segments (0xa173c : word) = Some W_a16f4.
Proof. vm_refl. Qed.
Lemma D_a16f4 : decode_any W_a16f4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16f8 : bv 32 := 0x00b5252f.
Lemma F_a16f8 : fetch_word AsanUbsan.M.loaded_segments (0xa1740 : word) = Some W_a16f8.
Proof. vm_refl. Qed.
Lemma D_a16f8 : decode_any W_a16f8 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16fc : bv 32 := 0x0015051b.
Lemma F_a16fc : fetch_word AsanUbsan.M.loaded_segments (0xa1744 : word) = Some W_a16fc.
Proof. vm_refl. Qed.
Lemma D_a16fc : decode_any W_a16fc = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1700 : bv 32 := 0x02051493.
Lemma F_a1700 : fetch_word AsanUbsan.M.loaded_segments (0xa1748 : word) = Some W_a1700.
Proof. vm_refl. Qed.
Lemma D_a1700 : decode_any W_a1700 = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1704 : bv 32 := 0x0204d493.
Lemma F_a1704 : fetch_word AsanUbsan.M.loaded_segments (0xa174c : word) = Some W_a1704.
Proof. vm_refl. Qed.
Lemma D_a1704 : decode_any W_a1704 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1708 : bv 32 := 0x08054663.
Lemma F_a1708 : fetch_word AsanUbsan.M.loaded_segments (0xa1750 : word) = Some W_a1708.
Proof. vm_refl. Qed.
Lemma D_a1708 : decode_any W_a1708 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_a170c : bv 32 := 0x00050b93.
Lemma F_a170c : fetch_word AsanUbsan.M.loaded_segments (0xa1754 : word) = Some W_a170c.
Proof. vm_refl. Qed.
Lemma D_a170c : decode_any W_a170c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1710 : bv 32 := 0x0104d593.
Lemma F_a1710 : fetch_word AsanUbsan.M.loaded_segments (0xa1758 : word) = Some W_a1710.
Proof. vm_refl. Qed.
Lemma D_a1710 : decode_any W_a1710 = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1714 : bv 32 := 0x00359513.
Lemma F_a1714 : fetch_word AsanUbsan.M.loaded_segments (0xa175c : word) = Some W_a1714.
Proof. vm_refl. Qed.
Lemma D_a1714 : decode_any W_a1714 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1718 : bv 32 := 0x00ac0533.
Lemma F_a1718 : fetch_word AsanUbsan.M.loaded_segments (0xa1760 : word) = Some W_a1718.
Proof. vm_refl. Qed.
Lemma D_a1718 : decode_any W_a1718 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a171c : bv 32 := 0x00053503.
Lemma F_a171c : fetch_word AsanUbsan.M.loaded_segments (0xa1764 : word) = Some W_a171c.
Proof. vm_refl. Qed.
Lemma D_a171c : decode_any W_a171c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1720 : bv 32 := 0x08050a63.
Lemma F_a1720 : fetch_word AsanUbsan.M.loaded_segments (0xa1768 : word) = Some W_a1720.
Proof. vm_refl. Qed.
Lemma D_a1720 : decode_any W_a1720 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1724 : bv 32 := 0x0164f5b3.
Lemma F_a1724 : fetch_word AsanUbsan.M.loaded_segments (0xa176c : word) = Some W_a1724.
Proof. vm_refl. Qed.
Lemma D_a1724 : decode_any W_a1724 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1728 : bv 32 := 0x00459593.
Lemma F_a1728 : fetch_word AsanUbsan.M.loaded_segments (0xa1770 : word) = Some W_a1728.
Proof. vm_refl. Qed.
Lemma D_a1728 : decode_any W_a1728 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a172c : bv 32 := 0x00b504b3.
Lemma F_a172c : fetch_word AsanUbsan.M.loaded_segments (0xa1774 : word) = Some W_a172c.
Proof. vm_refl. Qed.
Lemma D_a172c : decode_any W_a172c = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1730 : bv 32 := 0x00810613.
Lemma F_a1730 : fetch_word AsanUbsan.M.loaded_segments (0xa1778 : word) = Some W_a1730.
Proof. vm_refl. Qed.
Lemma D_a1730 : decode_any W_a1730 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1734 : bv 32 := 0x00048513.
Lemma F_a1734 : fetch_word AsanUbsan.M.loaded_segments (0xa177c : word) = Some W_a1734.
Proof. vm_refl. Qed.
Lemma D_a1734 : decode_any W_a1734 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1738 : bv 32 := 0x00000593.
Lemma F_a1738 : fetch_word AsanUbsan.M.loaded_segments (0xa1780 : word) = Some W_a1738.
Proof. vm_refl. Qed.
Lemma D_a1738 : decode_any W_a1738 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a173c : bv 32 := 0x00098693.
Lemma F_a173c : fetch_word AsanUbsan.M.loaded_segments (0xa1784 : word) = Some W_a173c.
Proof. vm_refl. Qed.
Lemma D_a173c : decode_any W_a173c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1740 : bv 32 := 0xaf5ff0ef.
Lemma F_a1740 : fetch_word AsanUbsan.M.loaded_segments (0xa1788 : word) = Some W_a1740.
Proof. vm_refl. Qed.
Lemma D_a1740 : decode_any W_a1740 = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1744 : bv 32 := 0x0154a423.
Lemma F_a1744 : fetch_word AsanUbsan.M.loaded_segments (0xa178c : word) = Some W_a1744.
Proof. vm_refl. Qed.
Lemma D_a1744 : decode_any W_a1744 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1748 : bv 32 := 0x0310000f.
Lemma F_a1748 : fetch_word AsanUbsan.M.loaded_segments (0xa1790 : word) = Some W_a1748.
Proof. vm_refl. Qed.
Lemma D_a1748 : decode_any W_a1748 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a174c : bv 32 := 0x000b8513.
Lemma F_a174c : fetch_word AsanUbsan.M.loaded_segments (0xa1794 : word) = Some W_a174c.
Proof. vm_refl. Qed.
Lemma D_a174c : decode_any W_a174c = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1750 : bv 32 := 0x01792023.
Lemma F_a1750 : fetch_word AsanUbsan.M.loaded_segments (0xa1798 : word) = Some W_a1750.
Proof. vm_refl. Qed.
Lemma D_a1750 : decode_any W_a1750 = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1754 : bv 32 := 0x00040663.
Lemma F_a1754 : fetch_word AsanUbsan.M.loaded_segments (0xa179c : word) = Some W_a1754.
Proof. vm_refl. Qed.
Lemma D_a1754 : decode_any W_a1754 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1760 : bv 32 := 0x06813083.
Lemma F_a1760 : fetch_word AsanUbsan.M.loaded_segments (0xa17a8 : word) = Some W_a1760.
Proof. vm_refl. Qed.
Lemma D_a1760 : decode_any W_a1760 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1764 : bv 32 := 0x06013403.
Lemma F_a1764 : fetch_word AsanUbsan.M.loaded_segments (0xa17ac : word) = Some W_a1764.
Proof. vm_refl. Qed.
Lemma D_a1764 : decode_any W_a1764 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1768 : bv 32 := 0x05813483.
Lemma F_a1768 : fetch_word AsanUbsan.M.loaded_segments (0xa17b0 : word) = Some W_a1768.
Proof. vm_refl. Qed.
Lemma D_a1768 : decode_any W_a1768 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a176c : bv 32 := 0x05013903.
Lemma F_a176c : fetch_word AsanUbsan.M.loaded_segments (0xa17b4 : word) = Some W_a176c.
Proof. vm_refl. Qed.
Lemma D_a176c : decode_any W_a176c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1770 : bv 32 := 0x04813983.
Lemma F_a1770 : fetch_word AsanUbsan.M.loaded_segments (0xa17b8 : word) = Some W_a1770.
Proof. vm_refl. Qed.
Lemma D_a1770 : decode_any W_a1770 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1774 : bv 32 := 0x04013a03.
Lemma F_a1774 : fetch_word AsanUbsan.M.loaded_segments (0xa17bc : word) = Some W_a1774.
Proof. vm_refl. Qed.
Lemma D_a1774 : decode_any W_a1774 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1778 : bv 32 := 0x03813a83.
Lemma F_a1778 : fetch_word AsanUbsan.M.loaded_segments (0xa17c0 : word) = Some W_a1778.
Proof. vm_refl. Qed.
Lemma D_a1778 : decode_any W_a1778 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a177c : bv 32 := 0x03013b03.
Lemma F_a177c : fetch_word AsanUbsan.M.loaded_segments (0xa17c4 : word) = Some W_a177c.
Proof. vm_refl. Qed.
Lemma D_a177c : decode_any W_a177c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1780 : bv 32 := 0x02813b83.
Lemma F_a1780 : fetch_word AsanUbsan.M.loaded_segments (0xa17c8 : word) = Some W_a1780.
Proof. vm_refl. Qed.
Lemma D_a1780 : decode_any W_a1780 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1784 : bv 32 := 0x02013c03.
Lemma F_a1784 : fetch_word AsanUbsan.M.loaded_segments (0xa17cc : word) = Some W_a1784.
Proof. vm_refl. Qed.
Lemma D_a1784 : decode_any W_a1784 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1788 : bv 32 := 0x01813c83.
Lemma F_a1788 : fetch_word AsanUbsan.M.loaded_segments (0xa17d0 : word) = Some W_a1788.
Proof. vm_refl. Qed.
Lemma D_a1788 : decode_any W_a1788 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a178c : bv 32 := 0x07010113.
Lemma F_a178c : fetch_word AsanUbsan.M.loaded_segments (0xa17d4 : word) = Some W_a178c.
Proof. vm_refl. Qed.
Lemma D_a178c : decode_any W_a178c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1790 : bv 32 := 0x00008067.
Lemma F_a1790 : fetch_word AsanUbsan.M.loaded_segments (0xa17d8 : word) = Some W_a1790.
Proof. vm_refl. Qed.
Lemma D_a1790 : decode_any W_a1790 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cb0 : bv 32 := 0xfd010113.
Lemma F_a1cb0 : fetch_word AsanUbsan.M.loaded_segments (0xa1cf8 : word) = Some W_a1cb0.
Proof. vm_refl. Qed.
Lemma D_a1cb0 : decode_any W_a1cb0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cb4 : bv 32 := 0x02113423.
Lemma F_a1cb4 : fetch_word AsanUbsan.M.loaded_segments (0xa1cfc : word) = Some W_a1cb4.
Proof. vm_refl. Qed.
Lemma D_a1cb4 : decode_any W_a1cb4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cb8 : bv 32 := 0x02813023.
Lemma F_a1cb8 : fetch_word AsanUbsan.M.loaded_segments (0xa1d00 : word) = Some W_a1cb8.
Proof. vm_refl. Qed.
Lemma D_a1cb8 : decode_any W_a1cb8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cbc : bv 32 := 0x00913c23.
Lemma F_a1cbc : fetch_word AsanUbsan.M.loaded_segments (0xa1d04 : word) = Some W_a1cbc.
Proof. vm_refl. Qed.
Lemma D_a1cbc : decode_any W_a1cbc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cc0 : bv 32 := 0x01213823.
Lemma F_a1cc0 : fetch_word AsanUbsan.M.loaded_segments (0xa1d08 : word) = Some W_a1cc0.
Proof. vm_refl. Qed.
Lemma D_a1cc0 : decode_any W_a1cc0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cc4 : bv 32 := 0x01313423.
Lemma F_a1cc4 : fetch_word AsanUbsan.M.loaded_segments (0xa1d0c : word) = Some W_a1cc4.
Proof. vm_refl. Qed.
Lemma D_a1cc4 : decode_any W_a1cc4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cc8 : bv 32 := 0x00050413.
Lemma F_a1cc8 : fetch_word AsanUbsan.M.loaded_segments (0xa1d10 : word) = Some W_a1cc8.
Proof. vm_refl. Qed.
Lemma D_a1cc8 : decode_any W_a1cc8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ccc : bv 32 := 0x00000593.
Lemma F_a1ccc : fetch_word AsanUbsan.M.loaded_segments (0xa1d14 : word) = Some W_a1ccc.
Proof. vm_refl. Qed.
Lemma D_a1ccc : decode_any W_a1ccc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cd0 : bv 32 := 0x800004b7.
Lemma F_a1cd0 : fetch_word AsanUbsan.M.loaded_segments (0xa1d18 : word) = Some W_a1cd0.
Proof. vm_refl. Qed.
Lemma D_a1cd0 : decode_any W_a1cd0 = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cd4 : bv 32 := 0x00900913.
Lemma F_a1cd4 : fetch_word AsanUbsan.M.loaded_segments (0xa1d1c : word) = Some W_a1cd4.
Proof. vm_refl. Qed.
Lemma D_a1cd4 : decode_any W_a1cd4 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cd8 : bv 32 := 0x00052503.
Lemma F_a1cd8 : fetch_word AsanUbsan.M.loaded_segments (0xa1d20 : word) = Some W_a1cd8.
Proof. vm_refl. Qed.
Lemma D_a1cd8 : decode_any W_a1cd8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cdc : bv 32 := 0x00055a63.
Lemma F_a1cdc : fetch_word AsanUbsan.M.loaded_segments (0xa1d24 : word) = Some W_a1cdc.
Proof. vm_refl. Qed.
Lemma D_a1cdc : decode_any W_a1cdc = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cf0 : bv 32 := 0x00956633.
Lemma F_a1cf0 : fetch_word AsanUbsan.M.loaded_segments (0xa1d38 : word) = Some W_a1cf0.
Proof. vm_refl. Qed.
Lemma D_a1cf0 : decode_any W_a1cf0 = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cf4 : bv 32 := 0x160426af.
Lemma F_a1cf4 : fetch_word AsanUbsan.M.loaded_segments (0xa1d3c : word) = Some W_a1cf4.
Proof. vm_refl. Qed.
Lemma D_a1cf4 : decode_any W_a1cf4 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cf8 : bv 32 := 0x00a69663.
Lemma F_a1cf8 : fetch_word AsanUbsan.M.loaded_segments (0xa1d40 : word) = Some W_a1cf8.
Proof. vm_refl. Qed.
Lemma D_a1cf8 : decode_any W_a1cf8 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cfc : bv 32 := 0x1ac4272f.
Lemma F_a1cfc : fetch_word AsanUbsan.M.loaded_segments (0xa1d44 : word) = Some W_a1cfc.
Proof. vm_refl. Qed.
Lemma D_a1cfc : decode_any W_a1cfc = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d00 : bv 32 := 0xfe071ae3.
Lemma F_a1d00 : fetch_word AsanUbsan.M.loaded_segments (0xa1d48 : word) = Some W_a1d00.
Proof. vm_refl. Qed.
Lemma D_a1d00 : decode_any W_a1d00 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d04 : bv 32 := 0x02a68063.
Lemma F_a1d04 : fetch_word AsanUbsan.M.loaded_segments (0xa1d4c : word) = Some W_a1d04.
Proof. vm_refl. Qed.
Lemma D_a1d04 : decode_any W_a1d04 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d24 : bv 32 := 0x02813083.
Lemma F_a1d24 : fetch_word AsanUbsan.M.loaded_segments (0xa1d6c : word) = Some W_a1d24.
Proof. vm_refl. Qed.
Lemma D_a1d24 : decode_any W_a1d24 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d28 : bv 32 := 0x02013403.
Lemma F_a1d28 : fetch_word AsanUbsan.M.loaded_segments (0xa1d70 : word) = Some W_a1d28.
Proof. vm_refl. Qed.
Lemma D_a1d28 : decode_any W_a1d28 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d2c : bv 32 := 0x01813483.
Lemma F_a1d2c : fetch_word AsanUbsan.M.loaded_segments (0xa1d74 : word) = Some W_a1d2c.
Proof. vm_refl. Qed.
Lemma D_a1d2c : decode_any W_a1d2c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d30 : bv 32 := 0x01013903.
Lemma F_a1d30 : fetch_word AsanUbsan.M.loaded_segments (0xa1d78 : word) = Some W_a1d30.
Proof. vm_refl. Qed.
Lemma D_a1d30 : decode_any W_a1d30 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d34 : bv 32 := 0x00813983.
Lemma F_a1d34 : fetch_word AsanUbsan.M.loaded_segments (0xa1d7c : word) = Some W_a1d34.
Proof. vm_refl. Qed.
Lemma D_a1d34 : decode_any W_a1d34 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d38 : bv 32 := 0x03010113.
Lemma F_a1d38 : fetch_word AsanUbsan.M.loaded_segments (0xa1d80 : word) = Some W_a1d38.
Proof. vm_refl. Qed.
Lemma D_a1d38 : decode_any W_a1d38 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d3c : bv 32 := 0x00008067.
Lemma F_a1d3c : fetch_word AsanUbsan.M.loaded_segments (0xa1d84 : word) = Some W_a1d3c.
Proof. vm_refl. Qed.
Lemma D_a1d3c : decode_any W_a1d3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ea0 : bv 32 := 0x00008513.
Lemma F_a1ea0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ee8 : word) = Some W_a1ea0.
Proof. vm_refl. Qed.
Lemma D_a1ea0 : decode_any W_a1ea0 = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ea4 : bv 32 := 0x00008067.
Lemma F_a1ea4 : fetch_word AsanUbsan.M.loaded_segments (0xa1eec : word) = Some W_a1ea4.
Proof. vm_refl. Qed.
Lemma D_a1ea4 : decode_any W_a1ea4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ea8 : bv 32 := 0xfc010113.
Lemma F_a1ea8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ef0 : word) = Some W_a1ea8.
Proof. vm_refl. Qed.
Lemma D_a1ea8 : decode_any W_a1ea8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eac : bv 32 := 0x02113c23.
Lemma F_a1eac : fetch_word AsanUbsan.M.loaded_segments (0xa1ef4 : word) = Some W_a1eac.
Proof. vm_refl. Qed.
Lemma D_a1eac : decode_any W_a1eac = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eb0 : bv 32 := 0x02813823.
Lemma F_a1eb0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ef8 : word) = Some W_a1eb0.
Proof. vm_refl. Qed.
Lemma D_a1eb0 : decode_any W_a1eb0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eb4 : bv 32 := 0x02913423.
Lemma F_a1eb4 : fetch_word AsanUbsan.M.loaded_segments (0xa1efc : word) = Some W_a1eb4.
Proof. vm_refl. Qed.
Lemma D_a1eb4 : decode_any W_a1eb4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eb8 : bv 32 := 0x03213023.
Lemma F_a1eb8 : fetch_word AsanUbsan.M.loaded_segments (0xa1f00 : word) = Some W_a1eb8.
Proof. vm_refl. Qed.
Lemma D_a1eb8 : decode_any W_a1eb8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ebc : bv 32 := 0x01313c23.
Lemma F_a1ebc : fetch_word AsanUbsan.M.loaded_segments (0xa1f04 : word) = Some W_a1ebc.
Proof. vm_refl. Qed.
Lemma D_a1ebc : decode_any W_a1ebc = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ec0 : bv 32 := 0x01413823.
Lemma F_a1ec0 : fetch_word AsanUbsan.M.loaded_segments (0xa1f08 : word) = Some W_a1ec0.
Proof. vm_refl. Qed.
Lemma D_a1ec0 : decode_any W_a1ec0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ec4 : bv 32 := 0x01513423.
Lemma F_a1ec4 : fetch_word AsanUbsan.M.loaded_segments (0xa1f0c : word) = Some W_a1ec4.
Proof. vm_refl. Qed.
Lemma D_a1ec4 : decode_any W_a1ec4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ec8 : bv 32 := 0x01613023.
Lemma F_a1ec8 : fetch_word AsanUbsan.M.loaded_segments (0xa1f10 : word) = Some W_a1ec8.
Proof. vm_refl. Qed.
Lemma D_a1ec8 : decode_any W_a1ec8 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ecc : bv 32 := 0x00068493.
Lemma F_a1ecc : fetch_word AsanUbsan.M.loaded_segments (0xa1f14 : word) = Some W_a1ecc.
Proof. vm_refl. Qed.
Lemma D_a1ecc : decode_any W_a1ecc = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ed0 : bv 32 := 0x02079413.
Lemma F_a1ed0 : fetch_word AsanUbsan.M.loaded_segments (0xa1f18 : word) = Some W_a1ed0.
Proof. vm_refl. Qed.
Lemma D_a1ed0 : decode_any W_a1ed0 = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ed4 : bv 32 := 0x00100693.
Lemma F_a1ed4 : fetch_word AsanUbsan.M.loaded_segments (0xa1f1c : word) = Some W_a1ed4.
Proof. vm_refl. Qed.
Lemma D_a1ed4 : decode_any W_a1ed4 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ed8 : bv 32 := 0x02045413.
Lemma F_a1ed8 : fetch_word AsanUbsan.M.loaded_segments (0xa1f20 : word) = Some W_a1ed8.
Proof. vm_refl. Qed.
Lemma D_a1ed8 : decode_any W_a1ed8 = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1edc : bv 32 := 0x0ef6f863.
Lemma F_a1edc : fetch_word AsanUbsan.M.loaded_segments (0xa1f24 : word) = Some W_a1edc.
Proof. vm_refl. Qed.
Lemma D_a1edc : decode_any W_a1edc = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ee0 : bv 32 := 0x000b2697.
Lemma F_a1ee0 : fetch_word AsanUbsan.M.loaded_segments (0xa1f28 : word) = Some W_a1ee0.
Proof. vm_refl. Qed.
Lemma D_a1ee0 : decode_any W_a1ee0 = Some (Auipc 13 178, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ee4 : bv 32 := 0x5b86b903.
Lemma F_a1ee4 : fetch_word AsanUbsan.M.loaded_segments (0xa1f2c : word) = Some W_a1ee4.
Proof. vm_refl. Qed.
Lemma D_a1ee4 : decode_any W_a1ee4 = Some (Load SZ8 true 18 13 1464, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ee8 : bv 32 := 0x00093683.
Lemma F_a1ee8 : fetch_word AsanUbsan.M.loaded_segments (0xa1f30 : word) = Some W_a1ee8.
Proof. vm_refl. Qed.
Lemma D_a1ee8 : decode_any W_a1ee8 = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1eec : bv 32 := 0x00068e63.
Lemma F_a1eec : fetch_word AsanUbsan.M.loaded_segments (0xa1f34 : word) = Some W_a1eec.
Proof. vm_refl. Qed.
Lemma D_a1eec : decode_any W_a1eec = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ef0 : bv 32 := 0x00100793.
Lemma F_a1ef0 : fetch_word AsanUbsan.M.loaded_segments (0xa1f38 : word) = Some W_a1ef0.
Proof. vm_refl. Qed.
Lemma D_a1ef0 : decode_any W_a1ef0 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ef4 : bv 32 := 0x00c4d813.
Lemma F_a1ef4 : fetch_word AsanUbsan.M.loaded_segments (0xa1f3c : word) = Some W_a1ef4.
Proof. vm_refl. Qed.
Lemma D_a1ef4 : decode_any W_a1ef4 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ef8 : bv 32 := 0x00f52423.
Lemma F_a1ef8 : fetch_word AsanUbsan.M.loaded_segments (0xa1f40 : word) = Some W_a1ef8.
Proof. vm_refl. Qed.
Lemma D_a1ef8 : decode_any W_a1ef8 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1efc : bv 32 := 0x00b53823.
Lemma F_a1efc : fetch_word AsanUbsan.M.loaded_segments (0xa1f44 : word) = Some W_a1efc.
Proof. vm_refl. Qed.
Lemma D_a1efc : decode_any W_a1efc = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f00 : bv 32 := 0x04081463.
Lemma F_a1f00 : fetch_word AsanUbsan.M.loaded_segments (0xa1f48 : word) = Some W_a1f00.
Proof. vm_refl. Qed.
Lemma D_a1f00 : decode_any W_a1f00 = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f48 : bv 32 := 0x0a977263.
Lemma F_a1f48 : fetch_word AsanUbsan.M.loaded_segments (0xa1f90 : word) = Some W_a1f48.
Proof. vm_refl. Qed.
Lemma D_a1f48 : decode_any W_a1f48 = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f4c : bv 32 := 0x04c77c63.
Lemma F_a1f4c : fetch_word AsanUbsan.M.loaded_segments (0xa1f94 : word) = Some W_a1f4c.
Proof. vm_refl. Qed.
Lemma D_a1f4c : decode_any W_a1f4c = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f50 : bv 32 := 0xff048493.
Lemma F_a1f50 : fetch_word AsanUbsan.M.loaded_segments (0xa1f98 : word) = Some W_a1f50.
Proof. vm_refl. Qed.
Lemma D_a1f50 : decode_any W_a1f50 = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f54 : bv 32 := 0x04967863.
Lemma F_a1f54 : fetch_word AsanUbsan.M.loaded_segments (0xa1f9c : word) = Some W_a1f54.
Proof. vm_refl. Qed.
Lemma D_a1f54 : decode_any W_a1f54 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f58 : bv 32 := 0x00767713.
Lemma F_a1f58 : fetch_word AsanUbsan.M.loaded_segments (0xa1fa0 : word) = Some W_a1f58.
Proof. vm_refl. Qed.
Lemma D_a1f58 : decode_any W_a1f58 = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f5c : bv 32 := 0x04071463.
Lemma F_a1f5c : fetch_word AsanUbsan.M.loaded_segments (0xa1fa4 : word) = Some W_a1f5c.
Proof. vm_refl. Qed.
Lemma D_a1f5c : decode_any W_a1f5c = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f60 : bv 32 := 0x01050713.
Lemma F_a1f60 : fetch_word AsanUbsan.M.loaded_segments (0xa1fa8 : word) = Some W_a1f60.
Proof. vm_refl. Qed.
Lemma D_a1f60 : decode_any W_a1f60 = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f64 : bv 32 := 0x00100793.
Lemma F_a1f64 : fetch_word AsanUbsan.M.loaded_segments (0xa1fac : word) = Some W_a1f64.
Proof. vm_refl. Qed.
Lemma D_a1f64 : decode_any W_a1f64 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f68 : bv 32 := 0x0287fe63.
Lemma F_a1f68 : fetch_word AsanUbsan.M.loaded_segments (0xa1fb0 : word) = Some W_a1f68.
Proof. vm_refl. Qed.
Lemma D_a1f68 : decode_any W_a1f68 = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f6c : bv 32 := 0xff863803.
Lemma F_a1f6c : fetch_word AsanUbsan.M.loaded_segments (0xa1fb4 : word) = Some W_a1f6c.
Proof. vm_refl. Qed.
Lemma D_a1f6c : decode_any W_a1f6c = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f70 : bv 32 := 0x02d86a63.
Lemma F_a1f70 : fetch_word AsanUbsan.M.loaded_segments (0xa1fb8 : word) = Some W_a1f70.
Proof. vm_refl. Qed.
Lemma D_a1f70 : decode_any W_a1f70 = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f74 : bv 32 := 0x00b80c63.
Lemma F_a1f74 : fetch_word AsanUbsan.M.loaded_segments (0xa1fbc : word) = Some W_a1f74.
Proof. vm_refl. Qed.
Lemma D_a1f74 : decode_any W_a1f74 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f78 : bv 32 := 0x00379893.
Lemma F_a1f78 : fetch_word AsanUbsan.M.loaded_segments (0xa1fc0 : word) = Some W_a1f78.
Proof. vm_refl. Qed.
Lemma D_a1f78 : decode_any W_a1f78 = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f7c : bv 32 := 0x00178793.
Lemma F_a1f7c : fetch_word AsanUbsan.M.loaded_segments (0xa1fc4 : word) = Some W_a1f7c.
Proof. vm_refl. Qed.
Lemma D_a1f7c : decode_any W_a1f7c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f80 : bv 32 := 0x011708b3.
Lemma F_a1f80 : fetch_word AsanUbsan.M.loaded_segments (0xa1fc8 : word) = Some W_a1f80.
Proof. vm_refl. Qed.
Lemma D_a1f80 : decode_any W_a1f80 = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f84 : bv 32 := 0x00f52423.
Lemma F_a1f84 : fetch_word AsanUbsan.M.loaded_segments (0xa1fcc : word) = Some W_a1f84.
Proof. vm_refl. Qed.
Lemma D_a1f84 : decode_any W_a1f84 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f88 : bv 32 := 0x0108b023.
Lemma F_a1f88 : fetch_word AsanUbsan.M.loaded_segments (0xa1fd0 : word) = Some W_a1f88.
Proof. vm_refl. Qed.
Lemma D_a1f88 : decode_any W_a1f88 = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f8c : bv 32 := 0xff063803.
Lemma F_a1f8c : fetch_word AsanUbsan.M.loaded_segments (0xa1fd4 : word) = Some W_a1f8c.
Proof. vm_refl. Qed.
Lemma D_a1f8c : decode_any W_a1f8c = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f90 : bv 32 := 0x01067a63.
Lemma F_a1f90 : fetch_word AsanUbsan.M.loaded_segments (0xa1fd8 : word) = Some W_a1f90.
Proof. vm_refl. Qed.
Lemma D_a1f90 : decode_any W_a1f90 = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f94 : bv 32 := 0x00987863.
Lemma F_a1f94 : fetch_word AsanUbsan.M.loaded_segments (0xa1fdc : word) = Some W_a1f94.
Proof. vm_refl. Qed.
Lemma D_a1f94 : decode_any W_a1f94 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f98 : bv 32 := 0x00787893.
Lemma F_a1f98 : fetch_word AsanUbsan.M.loaded_segments (0xa1fe0 : word) = Some W_a1f98.
Proof. vm_refl. Qed.
Lemma D_a1f98 : decode_any W_a1f98 = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1f9c : bv 32 := 0x00080613.
Lemma F_a1f9c : fetch_word AsanUbsan.M.loaded_segments (0xa1fe4 : word) = Some W_a1f9c.
Proof. vm_refl. Qed.
Lemma D_a1f9c : decode_any W_a1f9c = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fa0 : bv 32 := 0xfc0884e3.
Lemma F_a1fa0 : fetch_word AsanUbsan.M.loaded_segments (0xa1fe8 : word) = Some W_a1fa0.
Proof. vm_refl. Qed.
Lemma D_a1fa0 : decode_any W_a1fa0 = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fa4 : bv 32 := 0x03813083.
Lemma F_a1fa4 : fetch_word AsanUbsan.M.loaded_segments (0xa1fec : word) = Some W_a1fa4.
Proof. vm_refl. Qed.
Lemma D_a1fa4 : decode_any W_a1fa4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fa8 : bv 32 := 0x03013403.
Lemma F_a1fa8 : fetch_word AsanUbsan.M.loaded_segments (0xa1ff0 : word) = Some W_a1fa8.
Proof. vm_refl. Qed.
Lemma D_a1fa8 : decode_any W_a1fa8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fac : bv 32 := 0x02813483.
Lemma F_a1fac : fetch_word AsanUbsan.M.loaded_segments (0xa1ff4 : word) = Some W_a1fac.
Proof. vm_refl. Qed.
Lemma D_a1fac : decode_any W_a1fac = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fb0 : bv 32 := 0x02013903.
Lemma F_a1fb0 : fetch_word AsanUbsan.M.loaded_segments (0xa1ff8 : word) = Some W_a1fb0.
Proof. vm_refl. Qed.
Lemma D_a1fb0 : decode_any W_a1fb0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fb4 : bv 32 := 0x01813983.
Lemma F_a1fb4 : fetch_word AsanUbsan.M.loaded_segments (0xa1ffc : word) = Some W_a1fb4.
Proof. vm_refl. Qed.
Lemma D_a1fb4 : decode_any W_a1fb4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fb8 : bv 32 := 0x01013a03.
Lemma F_a1fb8 : fetch_word AsanUbsan.M.loaded_segments (0xa2000 : word) = Some W_a1fb8.
Proof. vm_refl. Qed.
Lemma D_a1fb8 : decode_any W_a1fb8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fbc : bv 32 := 0x00813a83.
Lemma F_a1fbc : fetch_word AsanUbsan.M.loaded_segments (0xa2004 : word) = Some W_a1fbc.
Proof. vm_refl. Qed.
Lemma D_a1fbc : decode_any W_a1fbc = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fc0 : bv 32 := 0x00013b03.
Lemma F_a1fc0 : fetch_word AsanUbsan.M.loaded_segments (0xa2008 : word) = Some W_a1fc0.
Proof. vm_refl. Qed.
Lemma D_a1fc0 : decode_any W_a1fc0 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fc4 : bv 32 := 0x04010113.
Lemma F_a1fc4 : fetch_word AsanUbsan.M.loaded_segments (0xa200c : word) = Some W_a1fc4.
Proof. vm_refl. Qed.
Lemma D_a1fc4 : decode_any W_a1fc4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1fc8 : bv 32 := 0x00008067.
Lemma F_a1fc8 : fetch_word AsanUbsan.M.loaded_segments (0xa2010 : word) = Some W_a1fc8.
Proof. vm_refl. Qed.
Lemma D_a1fc8 : decode_any W_a1fc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

