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
Definition W_83080 : bv 32 := 0x000e6517.
Lemma F_83080 : fetch_word Asan.M.loaded_segments (0x830d0 : word) = Some W_83080.
Proof. vm_refl. Qed.
Lemma D_83080 : decode_any W_83080 = Some (Auipc 10 230, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83084 : bv 32 := 0x68c50503.
Lemma F_83084 : fetch_word Asan.M.loaded_segments (0x830d4 : word) = Some W_83084.
Proof. vm_refl. Qed.
Lemma D_83084 : decode_any W_83084 = Some (Load SZ1 true 10 10 1676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83088 : bv 32 := 0x0230000f.
Lemma F_83088 : fetch_word Asan.M.loaded_segments (0x830d8 : word) = Some W_83088.
Proof. vm_refl. Qed.
Lemma D_83088 : decode_any W_83088 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8308c : bv 32 := 0x00a03533.
Lemma F_8308c : fetch_word Asan.M.loaded_segments (0x830dc : word) = Some W_8308c.
Proof. vm_refl. Qed.
Lemma D_8308c : decode_any W_8308c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83090 : bv 32 := 0x00008067.
Lemma F_83090 : fetch_word Asan.M.loaded_segments (0x830e0 : word) = Some W_83090.
Proof. vm_refl. Qed.
Lemma D_83090 : decode_any W_83090 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83094 : bv 32 := 0xfc010113.
Lemma F_83094 : fetch_word Asan.M.loaded_segments (0x830e4 : word) = Some W_83094.
Proof. vm_refl. Qed.
Lemma D_83094 : decode_any W_83094 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83098 : bv 32 := 0x02113c23.
Lemma F_83098 : fetch_word Asan.M.loaded_segments (0x830e8 : word) = Some W_83098.
Proof. vm_refl. Qed.
Lemma D_83098 : decode_any W_83098 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8309c : bv 32 := 0x02813823.
Lemma F_8309c : fetch_word Asan.M.loaded_segments (0x830ec : word) = Some W_8309c.
Proof. vm_refl. Qed.
Lemma D_8309c : decode_any W_8309c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830a0 : bv 32 := 0x02913423.
Lemma F_830a0 : fetch_word Asan.M.loaded_segments (0x830f0 : word) = Some W_830a0.
Proof. vm_refl. Qed.
Lemma D_830a0 : decode_any W_830a0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830a4 : bv 32 := 0x03213023.
Lemma F_830a4 : fetch_word Asan.M.loaded_segments (0x830f4 : word) = Some W_830a4.
Proof. vm_refl. Qed.
Lemma D_830a4 : decode_any W_830a4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830a8 : bv 32 := 0x01313c23.
Lemma F_830a8 : fetch_word Asan.M.loaded_segments (0x830f8 : word) = Some W_830a8.
Proof. vm_refl. Qed.
Lemma D_830a8 : decode_any W_830a8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830ac : bv 32 := 0x01413823.
Lemma F_830ac : fetch_word Asan.M.loaded_segments (0x830fc : word) = Some W_830ac.
Proof. vm_refl. Qed.
Lemma D_830ac : decode_any W_830ac = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830b0 : bv 32 := 0x01513423.
Lemma F_830b0 : fetch_word Asan.M.loaded_segments (0x83100 : word) = Some W_830b0.
Proof. vm_refl. Qed.
Lemma D_830b0 : decode_any W_830b0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830b4 : bv 32 := 0x00060a63.
Lemma F_830b4 : fetch_word Asan.M.loaded_segments (0x83104 : word) = Some W_830b4.
Proof. vm_refl. Qed.
Lemma D_830b4 : decode_any W_830b4 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830b8 : bv 32 := 0x000e6697.
Lemma F_830b8 : fetch_word Asan.M.loaded_segments (0x83108 : word) = Some W_830b8.
Proof. vm_refl. Qed.
Lemma D_830b8 : decode_any W_830b8 = Some (Auipc 13 230, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830bc : bv 32 := 0x65468683.
Lemma F_830bc : fetch_word Asan.M.loaded_segments (0x8310c : word) = Some W_830bc.
Proof. vm_refl. Qed.
Lemma D_830bc : decode_any W_830bc = Some (Load SZ1 true 13 13 1620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830c0 : bv 32 := 0x0230000f.
Lemma F_830c0 : fetch_word Asan.M.loaded_segments (0x83110 : word) = Some W_830c0.
Proof. vm_refl. Qed.
Lemma D_830c0 : decode_any W_830c0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830c4 : bv 32 := 0x0a068a63.
Lemma F_830c4 : fetch_word Asan.M.loaded_segments (0x83114 : word) = Some W_830c4.
Proof. vm_refl. Qed.
Lemma D_830c4 : decode_any W_830c4 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830c8 : bv 32 := 0x00757693.
Lemma F_830c8 : fetch_word Asan.M.loaded_segments (0x83118 : word) = Some W_830c8.
Proof. vm_refl. Qed.
Lemma D_830c8 : decode_any W_830c8 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830cc : bv 32 := 0x42069863.
Lemma F_830cc : fetch_word Asan.M.loaded_segments (0x8311c : word) = Some W_830cc.
Proof. vm_refl. Qed.
Lemma D_830cc : decode_any W_830cc = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830d0 : bv 32 := 0x000de697.
Lemma F_830d0 : fetch_word Asan.M.loaded_segments (0x83120 : word) = Some W_830d0.
Proof. vm_refl. Qed.
Lemma D_830d0 : decode_any W_830d0 = Some (Auipc 13 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830d4 : bv 32 := 0xaf86b683.
Lemma F_830d4 : fetch_word Asan.M.loaded_segments (0x83124 : word) = Some W_830d4.
Proof. vm_refl. Qed.
Lemma D_830d4 : decode_any W_830d4 = Some (Load SZ8 true 13 13 2808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830d8 : bv 32 := 0x0006b483.
Lemma F_830d8 : fetch_word Asan.M.loaded_segments (0x83128 : word) = Some W_830d8.
Proof. vm_refl. Qed.
Lemma D_830d8 : decode_any W_830d8 = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830dc : bv 32 := 0xfff48693.
Lemma F_830dc : fetch_word Asan.M.loaded_segments (0x8312c : word) = Some W_830dc.
Proof. vm_refl. Qed.
Lemma D_830dc : decode_any W_830dc = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830e0 : bv 32 := 0x00d4b733.
Lemma F_830e0 : fetch_word Asan.M.loaded_segments (0x83130 : word) = Some W_830e0.
Proof. vm_refl. Qed.
Lemma D_830e0 : decode_any W_830e0 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830e4 : bv 32 := 0xfff70713.
Lemma F_830e4 : fetch_word Asan.M.loaded_segments (0x83134 : word) = Some W_830e4.
Proof. vm_refl. Qed.
Lemma D_830e4 : decode_any W_830e4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830e8 : bv 32 := 0x00d77733.
Lemma F_830e8 : fetch_word Asan.M.loaded_segments (0x83138 : word) = Some W_830e8.
Proof. vm_refl. Qed.
Lemma D_830e8 : decode_any W_830e8 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830ec : bv 32 := 0x1ca77c63.
Lemma F_830ec : fetch_word Asan.M.loaded_segments (0x8313c : word) = Some W_830ec.
Proof. vm_refl. Qed.
Lemma D_830ec : decode_any W_830ec = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830f0 : bv 32 := 0x000de797.
Lemma F_830f0 : fetch_word Asan.M.loaded_segments (0x83140 : word) = Some W_830f0.
Proof. vm_refl. Qed.
Lemma D_830f0 : decode_any W_830f0 = Some (Auipc 15 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830f4 : bv 32 := 0xae07b783.
Lemma F_830f4 : fetch_word Asan.M.loaded_segments (0x83144 : word) = Some W_830f4.
Proof. vm_refl. Qed.
Lemma D_830f4 : decode_any W_830f4 = Some (Load SZ8 true 15 15 2784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830f8 : bv 32 := 0x000de817.
Lemma F_830f8 : fetch_word Asan.M.loaded_segments (0x83148 : word) = Some W_830f8.
Proof. vm_refl. Qed.
Lemma D_830f8 : decode_any W_830f8 = Some (Auipc 16 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_830fc : bv 32 := 0xae083803.
Lemma F_830fc : fetch_word Asan.M.loaded_segments (0x8314c : word) = Some W_830fc.
Proof. vm_refl. Qed.
Lemma D_830fc : decode_any W_830fc = Some (Load SZ8 true 16 16 2784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83100 : bv 32 := 0x0007b883.
Lemma F_83100 : fetch_word Asan.M.loaded_segments (0x83150 : word) = Some W_83100.
Proof. vm_refl. Qed.
Lemma D_83100 : decode_any W_83100 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83104 : bv 32 := 0x00083783.
Lemma F_83104 : fetch_word Asan.M.loaded_segments (0x83154 : word) = Some W_83104.
Proof. vm_refl. Qed.
Lemma D_83104 : decode_any W_83104 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83108 : bv 32 := 0xfff88813.
Lemma F_83108 : fetch_word Asan.M.loaded_segments (0x83158 : word) = Some W_83108.
Proof. vm_refl. Qed.
Lemma D_83108 : decode_any W_83108 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8310c : bv 32 := 0x00a87463.
Lemma F_8310c : fetch_word Asan.M.loaded_segments (0x8315c : word) = Some W_8310c.
Proof. vm_refl. Qed.
Lemma D_8310c : decode_any W_8310c = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83114 : bv 32 := 0x000de297.
Lemma F_83114 : fetch_word Asan.M.loaded_segments (0x83164 : word) = Some W_83114.
Proof. vm_refl. Qed.
Lemma D_83114 : decode_any W_83114 = Some (Auipc 5 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83118 : bv 32 := 0xacc2b283.
Lemma F_83118 : fetch_word Asan.M.loaded_segments (0x83168 : word) = Some W_83118.
Proof. vm_refl. Qed.
Lemma D_83118 : decode_any W_83118 = Some (Load SZ8 true 5 5 2764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8311c : bv 32 := 0x0002be03.
Lemma F_8311c : fetch_word Asan.M.loaded_segments (0x8316c : word) = Some W_8311c.
Proof. vm_refl. Qed.
Lemma D_8311c : decode_any W_8311c = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83120 : bv 32 := 0x003e5313.
Lemma F_83120 : fetch_word Asan.M.loaded_segments (0x83170 : word) = Some W_83120.
Proof. vm_refl. Qed.
Lemma D_83120 : decode_any W_83120 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83124 : bv 32 := 0x009303b3.
Lemma F_83124 : fetch_word Asan.M.loaded_segments (0x83174 : word) = Some W_83124.
Proof. vm_refl. Qed.
Lemma D_83124 : decode_any W_83124 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83128 : bv 32 := 0x00ae6463.
Lemma F_83128 : fetch_word Asan.M.loaded_segments (0x83178 : word) = Some W_83128.
Proof. vm_refl. Qed.
Lemma D_83128 : decode_any W_83128 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8312c : bv 32 := 0x0ca3e463.
Lemma F_8312c : fetch_word Asan.M.loaded_segments (0x8317c : word) = Some W_8312c.
Proof. vm_refl. Qed.
Lemma D_8312c : decode_any W_8312c = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_831f4 : bv 32 := 0x0002b383.
Lemma F_831f4 : fetch_word Asan.M.loaded_segments (0x83244 : word) = Some W_831f4.
Proof. vm_refl. Qed.
Lemma D_831f4 : decode_any W_831f4 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_831f8 : bv 32 := 0x0033d293.
Lemma F_831f8 : fetch_word Asan.M.loaded_segments (0x83248 : word) = Some W_831f8.
Proof. vm_refl. Qed.
Lemma D_831f8 : decode_any W_831f8 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_831fc : bv 32 := 0x00928333.
Lemma F_831fc : fetch_word Asan.M.loaded_segments (0x8324c : word) = Some W_831fc.
Proof. vm_refl. Qed.
Lemma D_831fc : decode_any W_831fc = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83200 : bv 32 := 0x00a3e463.
Lemma F_83200 : fetch_word Asan.M.loaded_segments (0x83250 : word) = Some W_83200.
Proof. vm_refl. Qed.
Lemma D_83200 : decode_any W_83200 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83204 : bv 32 := 0x0ca36063.
Lemma F_83204 : fetch_word Asan.M.loaded_segments (0x83254 : word) = Some W_83204.
Proof. vm_refl. Qed.
Lemma D_83204 : decode_any W_83204 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832c4 : bv 32 := 0x0075f793.
Lemma F_832c4 : fetch_word Asan.M.loaded_segments (0x83314 : word) = Some W_832c4.
Proof. vm_refl. Qed.
Lemma D_832c4 : decode_any W_832c4 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832c8 : bv 32 := 0x26079a63.
Lemma F_832c8 : fetch_word Asan.M.loaded_segments (0x83318 : word) = Some W_832c8.
Proof. vm_refl. Qed.
Lemma D_832c8 : decode_any W_832c8 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832cc : bv 32 := 0x00b505b3.
Lemma F_832cc : fetch_word Asan.M.loaded_segments (0x8331c : word) = Some W_832cc.
Proof. vm_refl. Qed.
Lemma D_832cc : decode_any W_832cc = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832d0 : bv 32 := 0xff858593.
Lemma F_832d0 : fetch_word Asan.M.loaded_segments (0x83320 : word) = Some W_832d0.
Proof. vm_refl. Qed.
Lemma D_832d0 : decode_any W_832d0 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832d4 : bv 32 := 0x04b77263.
Lemma F_832d4 : fetch_word Asan.M.loaded_segments (0x83324 : word) = Some W_832d4.
Proof. vm_refl. Qed.
Lemma D_832d4 : decode_any W_832d4 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832d8 : bv 32 := 0x000de717.
Lemma F_832d8 : fetch_word Asan.M.loaded_segments (0x83328 : word) = Some W_832d8.
Proof. vm_refl. Qed.
Lemma D_832d8 : decode_any W_832d8 = Some (Auipc 14 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832dc : bv 32 := 0x8f873703.
Lemma F_832dc : fetch_word Asan.M.loaded_segments (0x8332c : word) = Some W_832dc.
Proof. vm_refl. Qed.
Lemma D_832dc : decode_any W_832dc = Some (Load SZ8 true 14 14 2296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832e0 : bv 32 := 0x000de797.
Lemma F_832e0 : fetch_word Asan.M.loaded_segments (0x83330 : word) = Some W_832e0.
Proof. vm_refl. Qed.
Lemma D_832e0 : decode_any W_832e0 = Some (Auipc 15 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832e4 : bv 32 := 0x8f87b783.
Lemma F_832e4 : fetch_word Asan.M.loaded_segments (0x83334 : word) = Some W_832e4.
Proof. vm_refl. Qed.
Lemma D_832e4 : decode_any W_832e4 = Some (Load SZ8 true 15 15 2296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832e8 : bv 32 := 0x00073883.
Lemma F_832e8 : fetch_word Asan.M.loaded_segments (0x83338 : word) = Some W_832e8.
Proof. vm_refl. Qed.
Lemma D_832e8 : decode_any W_832e8 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832ec : bv 32 := 0x0007b703.
Lemma F_832ec : fetch_word Asan.M.loaded_segments (0x8333c : word) = Some W_832ec.
Proof. vm_refl. Qed.
Lemma D_832ec : decode_any W_832ec = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832f0 : bv 32 := 0xfff88813.
Lemma F_832f0 : fetch_word Asan.M.loaded_segments (0x83340 : word) = Some W_832f0.
Proof. vm_refl. Qed.
Lemma D_832f0 : decode_any W_832f0 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832f4 : bv 32 := 0x00b87463.
Lemma F_832f4 : fetch_word Asan.M.loaded_segments (0x83344 : word) = Some W_832f4.
Proof. vm_refl. Qed.
Lemma D_832f4 : decode_any W_832f4 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_832fc : bv 32 := 0x000de797.
Lemma F_832fc : fetch_word Asan.M.loaded_segments (0x8334c : word) = Some W_832fc.
Proof. vm_refl. Qed.
Lemma D_832fc : decode_any W_832fc = Some (Auipc 15 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83300 : bv 32 := 0x8e47b783.
Lemma F_83300 : fetch_word Asan.M.loaded_segments (0x83350 : word) = Some W_83300.
Proof. vm_refl. Qed.
Lemma D_83300 : decode_any W_83300 = Some (Load SZ8 true 15 15 2276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83304 : bv 32 := 0x0007b303.
Lemma F_83304 : fetch_word Asan.M.loaded_segments (0x83354 : word) = Some W_83304.
Proof. vm_refl. Qed.
Lemma D_83304 : decode_any W_83304 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83308 : bv 32 := 0x00335793.
Lemma F_83308 : fetch_word Asan.M.loaded_segments (0x83358 : word) = Some W_83308.
Proof. vm_refl. Qed.
Lemma D_83308 : decode_any W_83308 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8330c : bv 32 := 0x009782b3.
Lemma F_8330c : fetch_word Asan.M.loaded_segments (0x8335c : word) = Some W_8330c.
Proof. vm_refl. Qed.
Lemma D_8330c : decode_any W_8330c = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83310 : bv 32 := 0x12b36263.
Lemma F_83310 : fetch_word Asan.M.loaded_segments (0x83360 : word) = Some W_83310.
Proof. vm_refl. Qed.
Lemma D_83310 : decode_any W_83310 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83314 : bv 32 := 0x12b2f063.
Lemma F_83314 : fetch_word Asan.M.loaded_segments (0x83364 : word) = Some W_83314.
Proof. vm_refl. Qed.
Lemma D_83314 : decode_any W_83314 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83318 : bv 32 := 0x000de697.
Lemma F_83318 : fetch_word Asan.M.loaded_segments (0x83368 : word) = Some W_83318.
Proof. vm_refl. Qed.
Lemma D_83318 : decode_any W_83318 = Some (Auipc 13 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8331c : bv 32 := 0x8d06b983.
Lemma F_8331c : fetch_word Asan.M.loaded_segments (0x8336c : word) = Some W_8331c.
Proof. vm_refl. Qed.
Lemma D_8331c : decode_any W_8331c = Some (Load SZ8 true 19 13 2256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83320 : bv 32 := 0x0009b303.
Lemma F_83320 : fetch_word Asan.M.loaded_segments (0x83370 : word) = Some W_83320.
Proof. vm_refl. Qed.
Lemma D_83320 : decode_any W_83320 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83324 : bv 32 := 0x22030c63.
Lemma F_83324 : fetch_word Asan.M.loaded_segments (0x83374 : word) = Some W_83324.
Proof. vm_refl. Qed.
Lemma D_83324 : decode_any W_83324 = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83328 : bv 32 := 0x00355693.
Lemma F_83328 : fetch_word Asan.M.loaded_segments (0x83378 : word) = Some W_83328.
Proof. vm_refl. Qed.
Lemma D_83328 : decode_any W_83328 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8332c : bv 32 := 0x0035d593.
Lemma F_8332c : fetch_word Asan.M.loaded_segments (0x8337c : word) = Some W_8332c.
Proof. vm_refl. Qed.
Lemma D_8332c : decode_any W_8332c = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83330 : bv 32 := 0x00d48533.
Lemma F_83330 : fetch_word Asan.M.loaded_segments (0x83380 : word) = Some W_83330.
Proof. vm_refl. Qed.
Lemma D_83330 : decode_any W_83330 = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83334 : bv 32 := 0x00158913.
Lemma F_83334 : fetch_word Asan.M.loaded_segments (0x83384 : word) = Some W_83334.
Proof. vm_refl. Qed.
Lemma D_83334 : decode_any W_83334 = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83338 : bv 32 := 0x40d90433.
Lemma F_83338 : fetch_word Asan.M.loaded_segments (0x83388 : word) = Some W_83338.
Proof. vm_refl. Qed.
Lemma D_83338 : decode_any W_83338 = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8333c : bv 32 := 0x0c061063.
Lemma F_8333c : fetch_word Asan.M.loaded_segments (0x8338c : word) = Some W_8333c.
Proof. vm_refl. Qed.
Lemma D_8333c : decode_any W_8333c = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83340 : bv 32 := 0x000de597.
Lemma F_83340 : fetch_word Asan.M.loaded_segments (0x83390 : word) = Some W_83340.
Proof. vm_refl. Qed.
Lemma D_83340 : decode_any W_83340 = Some (Auipc 11 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83344 : bv 32 := 0x8785b583.
Lemma F_83344 : fetch_word Asan.M.loaded_segments (0x83394 : word) = Some W_83344.
Proof. vm_refl. Qed.
Lemma D_83344 : decode_any W_83344 = Some (Load SZ8 true 11 11 2168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83348 : bv 32 := 0x0785b583.
Lemma F_83348 : fetch_word Asan.M.loaded_segments (0x83398 : word) = Some W_83348.
Proof. vm_refl. Qed.
Lemma D_83348 : decode_any W_83348 = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8334c : bv 32 := 0x0ab46863.
Lemma F_8334c : fetch_word Asan.M.loaded_segments (0x8339c : word) = Some W_8334c.
Proof. vm_refl. Qed.
Lemma D_8334c : decode_any W_8334c = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_833fc : bv 32 := 0x00060593.
Lemma F_833fc : fetch_word Asan.M.loaded_segments (0x8344c : word) = Some W_833fc.
Proof. vm_refl. Qed.
Lemma D_833fc : decode_any W_833fc = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83400 : bv 32 := 0x00c0006f.
Lemma F_83400 : fetch_word Asan.M.loaded_segments (0x83450 : word) = Some W_83400.
Proof. vm_refl. Qed.
Lemma D_83400 : decode_any W_83400 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8340c : bv 32 := 0x00040613.
Lemma F_8340c : fetch_word Asan.M.loaded_segments (0x8345c : word) = Some W_8340c.
Proof. vm_refl. Qed.
Lemma D_8340c : decode_any W_8340c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83410 : bv 32 := 0x03813083.
Lemma F_83410 : fetch_word Asan.M.loaded_segments (0x83460 : word) = Some W_83410.
Proof. vm_refl. Qed.
Lemma D_83410 : decode_any W_83410 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83414 : bv 32 := 0x03013403.
Lemma F_83414 : fetch_word Asan.M.loaded_segments (0x83464 : word) = Some W_83414.
Proof. vm_refl. Qed.
Lemma D_83414 : decode_any W_83414 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83418 : bv 32 := 0x02813483.
Lemma F_83418 : fetch_word Asan.M.loaded_segments (0x83468 : word) = Some W_83418.
Proof. vm_refl. Qed.
Lemma D_83418 : decode_any W_83418 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8341c : bv 32 := 0x02013903.
Lemma F_8341c : fetch_word Asan.M.loaded_segments (0x8346c : word) = Some W_8341c.
Proof. vm_refl. Qed.
Lemma D_8341c : decode_any W_8341c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83420 : bv 32 := 0x01813983.
Lemma F_83420 : fetch_word Asan.M.loaded_segments (0x83470 : word) = Some W_83420.
Proof. vm_refl. Qed.
Lemma D_83420 : decode_any W_83420 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83424 : bv 32 := 0x01013a03.
Lemma F_83424 : fetch_word Asan.M.loaded_segments (0x83474 : word) = Some W_83424.
Proof. vm_refl. Qed.
Lemma D_83424 : decode_any W_83424 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83428 : bv 32 := 0x00813a83.
Lemma F_83428 : fetch_word Asan.M.loaded_segments (0x83478 : word) = Some W_83428.
Proof. vm_refl. Qed.
Lemma D_83428 : decode_any W_83428 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8342c : bv 32 := 0x04010113.
Lemma F_8342c : fetch_word Asan.M.loaded_segments (0x8347c : word) = Some W_8342c.
Proof. vm_refl. Qed.
Lemma D_8342c : decode_any W_8342c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83430 : bv 32 := 0x00030067.
Lemma F_83430 : fetch_word Asan.M.loaded_segments (0x83480 : word) = Some W_83430.
Proof. vm_refl. Qed.
Lemma D_83430 : decode_any W_83430 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83590 : bv 32 := 0x000dd597.
Lemma F_83590 : fetch_word Asan.M.loaded_segments (0x835e0 : word) = Some W_83590.
Proof. vm_refl. Qed.
Lemma D_83590 : decode_any W_83590 = Some (Auipc 11 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83594 : bv 32 := 0x6385b583.
Lemma F_83594 : fetch_word Asan.M.loaded_segments (0x835e4 : word) = Some W_83594.
Proof. vm_refl. Qed.
Lemma D_83594 : decode_any W_83594 = Some (Load SZ8 true 11 11 1592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83598 : bv 32 := 0x0005b583.
Lemma F_83598 : fetch_word Asan.M.loaded_segments (0x835e8 : word) = Some W_83598.
Proof. vm_refl. Qed.
Lemma D_83598 : decode_any W_83598 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8359c : bv 32 := 0xfff58613.
Lemma F_8359c : fetch_word Asan.M.loaded_segments (0x835ec : word) = Some W_8359c.
Proof. vm_refl. Qed.
Lemma D_8359c : decode_any W_8359c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835a0 : bv 32 := 0x00c5b6b3.
Lemma F_835a0 : fetch_word Asan.M.loaded_segments (0x835f0 : word) = Some W_835a0.
Proof. vm_refl. Qed.
Lemma D_835a0 : decode_any W_835a0 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835a4 : bv 32 := 0xfff68693.
Lemma F_835a4 : fetch_word Asan.M.loaded_segments (0x835f4 : word) = Some W_835a4.
Proof. vm_refl. Qed.
Lemma D_835a4 : decode_any W_835a4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835a8 : bv 32 := 0x00c6f6b3.
Lemma F_835a8 : fetch_word Asan.M.loaded_segments (0x835f8 : word) = Some W_835a8.
Proof. vm_refl. Qed.
Lemma D_835a8 : decode_any W_835a8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835ac : bv 32 := 0x04a6f263.
Lemma F_835ac : fetch_word Asan.M.loaded_segments (0x835fc : word) = Some W_835ac.
Proof. vm_refl. Qed.
Lemma D_835ac : decode_any W_835ac = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835b0 : bv 32 := 0x000dd697.
Lemma F_835b0 : fetch_word Asan.M.loaded_segments (0x83600 : word) = Some W_835b0.
Proof. vm_refl. Qed.
Lemma D_835b0 : decode_any W_835b0 = Some (Auipc 13 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835b4 : bv 32 := 0x6206b683.
Lemma F_835b4 : fetch_word Asan.M.loaded_segments (0x83604 : word) = Some W_835b4.
Proof. vm_refl. Qed.
Lemma D_835b4 : decode_any W_835b4 = Some (Load SZ8 true 13 13 1568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835b8 : bv 32 := 0x000dd717.
Lemma F_835b8 : fetch_word Asan.M.loaded_segments (0x83608 : word) = Some W_835b8.
Proof. vm_refl. Qed.
Lemma D_835b8 : decode_any W_835b8 = Some (Auipc 14 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835bc : bv 32 := 0x62073703.
Lemma F_835bc : fetch_word Asan.M.loaded_segments (0x8360c : word) = Some W_835bc.
Proof. vm_refl. Qed.
Lemma D_835bc : decode_any W_835bc = Some (Load SZ8 true 14 14 1568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835c0 : bv 32 := 0x0006b803.
Lemma F_835c0 : fetch_word Asan.M.loaded_segments (0x83610 : word) = Some W_835c0.
Proof. vm_refl. Qed.
Lemma D_835c0 : decode_any W_835c0 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835c4 : bv 32 := 0x00073683.
Lemma F_835c4 : fetch_word Asan.M.loaded_segments (0x83614 : word) = Some W_835c4.
Proof. vm_refl. Qed.
Lemma D_835c4 : decode_any W_835c4 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835c8 : bv 32 := 0xfff80793.
Lemma F_835c8 : fetch_word Asan.M.loaded_segments (0x83618 : word) = Some W_835c8.
Proof. vm_refl. Qed.
Lemma D_835c8 : decode_any W_835c8 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835cc : bv 32 := 0x00a7f463.
Lemma F_835cc : fetch_word Asan.M.loaded_segments (0x8361c : word) = Some W_835cc.
Proof. vm_refl. Qed.
Lemma D_835cc : decode_any W_835cc = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835d4 : bv 32 := 0x000dd717.
Lemma F_835d4 : fetch_word Asan.M.loaded_segments (0x83624 : word) = Some W_835d4.
Proof. vm_refl. Qed.
Lemma D_835d4 : decode_any W_835d4 = Some (Auipc 14 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835d8 : bv 32 := 0x60c73703.
Lemma F_835d8 : fetch_word Asan.M.loaded_segments (0x83628 : word) = Some W_835d8.
Proof. vm_refl. Qed.
Lemma D_835d8 : decode_any W_835d8 = Some (Load SZ8 true 14 14 1548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835dc : bv 32 := 0x00073283.
Lemma F_835dc : fetch_word Asan.M.loaded_segments (0x8362c : word) = Some W_835dc.
Proof. vm_refl. Qed.
Lemma D_835dc : decode_any W_835dc = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835e0 : bv 32 := 0x0032d713.
Lemma F_835e0 : fetch_word Asan.M.loaded_segments (0x83630 : word) = Some W_835e0.
Proof. vm_refl. Qed.
Lemma D_835e0 : decode_any W_835e0 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835e4 : bv 32 := 0x00b708b3.
Lemma F_835e4 : fetch_word Asan.M.loaded_segments (0x83634 : word) = Some W_835e4.
Proof. vm_refl. Qed.
Lemma D_835e4 : decode_any W_835e4 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835e8 : bv 32 := 0x00a2ea63.
Lemma F_835e8 : fetch_word Asan.M.loaded_segments (0x83638 : word) = Some W_835e8.
Proof. vm_refl. Qed.
Lemma D_835e8 : decode_any W_835e8 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835ec : bv 32 := 0x00a8f863.
Lemma F_835ec : fetch_word Asan.M.loaded_segments (0x8363c : word) = Some W_835ec.
Proof. vm_refl. Qed.
Lemma D_835ec : decode_any W_835ec = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835f0 : bv 32 := 0x00355513.
Lemma F_835f0 : fetch_word Asan.M.loaded_segments (0x83640 : word) = Some W_835f0.
Proof. vm_refl. Qed.
Lemma D_835f0 : decode_any W_835f0 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835f4 : bv 32 := 0x00a58533.
Lemma F_835f4 : fetch_word Asan.M.loaded_segments (0x83644 : word) = Some W_835f4.
Proof. vm_refl. Qed.
Lemma D_835f4 : decode_any W_835f4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_835f8 : bv 32 := 0x00008067.
Lemma F_835f8 : fetch_word Asan.M.loaded_segments (0x83648 : word) = Some W_835f8.
Proof. vm_refl. Qed.
Lemma D_835f8 : decode_any W_835f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a1c : bv 32 := 0xfc010113.
Lemma F_83a1c : fetch_word Asan.M.loaded_segments (0x83a6c : word) = Some W_83a1c.
Proof. vm_refl. Qed.
Lemma D_83a1c : decode_any W_83a1c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a20 : bv 32 := 0x02113c23.
Lemma F_83a20 : fetch_word Asan.M.loaded_segments (0x83a70 : word) = Some W_83a20.
Proof. vm_refl. Qed.
Lemma D_83a20 : decode_any W_83a20 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a24 : bv 32 := 0x02813823.
Lemma F_83a24 : fetch_word Asan.M.loaded_segments (0x83a74 : word) = Some W_83a24.
Proof. vm_refl. Qed.
Lemma D_83a24 : decode_any W_83a24 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a28 : bv 32 := 0x02913423.
Lemma F_83a28 : fetch_word Asan.M.loaded_segments (0x83a78 : word) = Some W_83a28.
Proof. vm_refl. Qed.
Lemma D_83a28 : decode_any W_83a28 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a2c : bv 32 := 0x03213023.
Lemma F_83a2c : fetch_word Asan.M.loaded_segments (0x83a7c : word) = Some W_83a2c.
Proof. vm_refl. Qed.
Lemma D_83a2c : decode_any W_83a2c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a30 : bv 32 := 0x01313c23.
Lemma F_83a30 : fetch_word Asan.M.loaded_segments (0x83a80 : word) = Some W_83a30.
Proof. vm_refl. Qed.
Lemma D_83a30 : decode_any W_83a30 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a34 : bv 32 := 0x01413823.
Lemma F_83a34 : fetch_word Asan.M.loaded_segments (0x83a84 : word) = Some W_83a34.
Proof. vm_refl. Qed.
Lemma D_83a34 : decode_any W_83a34 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a38 : bv 32 := 0x01513423.
Lemma F_83a38 : fetch_word Asan.M.loaded_segments (0x83a88 : word) = Some W_83a38.
Proof. vm_refl. Qed.
Lemma D_83a38 : decode_any W_83a38 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a3c : bv 32 := 0x14058c63.
Lemma F_83a3c : fetch_word Asan.M.loaded_segments (0x83a8c : word) = Some W_83a3c.
Proof. vm_refl. Qed.
Lemma D_83a3c : decode_any W_83a3c = Some (Branch BC_EQ 11 0 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a40 : bv 32 := 0x00058493.
Lemma F_83a40 : fetch_word Asan.M.loaded_segments (0x83a90 : word) = Some W_83a40.
Proof. vm_refl. Qed.
Lemma D_83a40 : decode_any W_83a40 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a44 : bv 32 := 0x00050413.
Lemma F_83a44 : fetch_word Asan.M.loaded_segments (0x83a94 : word) = Some W_83a44.
Proof. vm_refl. Qed.
Lemma D_83a44 : decode_any W_83a44 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a48 : bv 32 := 0x000dd517.
Lemma F_83a48 : fetch_word Asan.M.loaded_segments (0x83a98 : word) = Some W_83a48.
Proof. vm_refl. Qed.
Lemma D_83a48 : decode_any W_83a48 = Some (Auipc 10 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a4c : bv 32 := 0x18053a83.
Lemma F_83a4c : fetch_word Asan.M.loaded_segments (0x83a9c : word) = Some W_83a4c.
Proof. vm_refl. Qed.
Lemma D_83a4c : decode_any W_83a4c = Some (Load SZ8 true 21 10 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a50 : bv 32 := 0x000ab583.
Lemma F_83a50 : fetch_word Asan.M.loaded_segments (0x83aa0 : word) = Some W_83a50.
Proof. vm_refl. Qed.
Lemma D_83a50 : decode_any W_83a50 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a54 : bv 32 := 0xfff58513.
Lemma F_83a54 : fetch_word Asan.M.loaded_segments (0x83aa4 : word) = Some W_83a54.
Proof. vm_refl. Qed.
Lemma D_83a54 : decode_any W_83a54 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a58 : bv 32 := 0x00a5b633.
Lemma F_83a58 : fetch_word Asan.M.loaded_segments (0x83aa8 : word) = Some W_83a58.
Proof. vm_refl. Qed.
Lemma D_83a58 : decode_any W_83a58 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a5c : bv 32 := 0xfff60613.
Lemma F_83a5c : fetch_word Asan.M.loaded_segments (0x83aac : word) = Some W_83a5c.
Proof. vm_refl. Qed.
Lemma D_83a5c : decode_any W_83a5c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a60 : bv 32 := 0x00a67633.
Lemma F_83a60 : fetch_word Asan.M.loaded_segments (0x83ab0 : word) = Some W_83a60.
Proof. vm_refl. Qed.
Lemma D_83a60 : decode_any W_83a60 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a64 : bv 32 := 0x04867263.
Lemma F_83a64 : fetch_word Asan.M.loaded_segments (0x83ab4 : word) = Some W_83a64.
Proof. vm_refl. Qed.
Lemma D_83a64 : decode_any W_83a64 = Some (Branch BC_GEU 12 8 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a68 : bv 32 := 0x000dd697.
Lemma F_83a68 : fetch_word Asan.M.loaded_segments (0x83ab8 : word) = Some W_83a68.
Proof. vm_refl. Qed.
Lemma D_83a68 : decode_any W_83a68 = Some (Auipc 13 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a6c : bv 32 := 0x1686b683.
Lemma F_83a6c : fetch_word Asan.M.loaded_segments (0x83abc : word) = Some W_83a6c.
Proof. vm_refl. Qed.
Lemma D_83a6c : decode_any W_83a6c = Some (Load SZ8 true 13 13 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a70 : bv 32 := 0x000dd717.
Lemma F_83a70 : fetch_word Asan.M.loaded_segments (0x83ac0 : word) = Some W_83a70.
Proof. vm_refl. Qed.
Lemma D_83a70 : decode_any W_83a70 = Some (Auipc 14 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a74 : bv 32 := 0x16873703.
Lemma F_83a74 : fetch_word Asan.M.loaded_segments (0x83ac4 : word) = Some W_83a74.
Proof. vm_refl. Qed.
Lemma D_83a74 : decode_any W_83a74 = Some (Load SZ8 true 14 14 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a78 : bv 32 := 0x0006b803.
Lemma F_83a78 : fetch_word Asan.M.loaded_segments (0x83ac8 : word) = Some W_83a78.
Proof. vm_refl. Qed.
Lemma D_83a78 : decode_any W_83a78 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a7c : bv 32 := 0x00073683.
Lemma F_83a7c : fetch_word Asan.M.loaded_segments (0x83acc : word) = Some W_83a7c.
Proof. vm_refl. Qed.
Lemma D_83a7c : decode_any W_83a7c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a80 : bv 32 := 0xfff80793.
Lemma F_83a80 : fetch_word Asan.M.loaded_segments (0x83ad0 : word) = Some W_83a80.
Proof. vm_refl. Qed.
Lemma D_83a80 : decode_any W_83a80 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a84 : bv 32 := 0x0087f463.
Lemma F_83a84 : fetch_word Asan.M.loaded_segments (0x83ad4 : word) = Some W_83a84.
Proof. vm_refl. Qed.
Lemma D_83a84 : decode_any W_83a84 = Some (Branch BC_GEU 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a8c : bv 32 := 0x000dd717.
Lemma F_83a8c : fetch_word Asan.M.loaded_segments (0x83adc : word) = Some W_83a8c.
Proof. vm_refl. Qed.
Lemma D_83a8c : decode_any W_83a8c = Some (Auipc 14 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a90 : bv 32 := 0x15473703.
Lemma F_83a90 : fetch_word Asan.M.loaded_segments (0x83ae0 : word) = Some W_83a90.
Proof. vm_refl. Qed.
Lemma D_83a90 : decode_any W_83a90 = Some (Load SZ8 true 14 14 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a94 : bv 32 := 0x00073283.
Lemma F_83a94 : fetch_word Asan.M.loaded_segments (0x83ae4 : word) = Some W_83a94.
Proof. vm_refl. Qed.
Lemma D_83a94 : decode_any W_83a94 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a98 : bv 32 := 0x0032d713.
Lemma F_83a98 : fetch_word Asan.M.loaded_segments (0x83ae8 : word) = Some W_83a98.
Proof. vm_refl. Qed.
Lemma D_83a98 : decode_any W_83a98 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83a9c : bv 32 := 0x00b708b3.
Lemma F_83a9c : fetch_word Asan.M.loaded_segments (0x83aec : word) = Some W_83a9c.
Proof. vm_refl. Qed.
Lemma D_83a9c : decode_any W_83a9c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83aa0 : bv 32 := 0x1282e063.
Lemma F_83aa0 : fetch_word Asan.M.loaded_segments (0x83af0 : word) = Some W_83aa0.
Proof. vm_refl. Qed.
Lemma D_83aa0 : decode_any W_83aa0 = Some (Branch BC_LTU 5 8 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83aa4 : bv 32 := 0x1088fe63.
Lemma F_83aa4 : fetch_word Asan.M.loaded_segments (0x83af4 : word) = Some W_83aa4.
Proof. vm_refl. Qed.
Lemma D_83aa4 : decode_any W_83aa4 = Some (Branch BC_GEU 17 8 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83aa8 : bv 32 := 0x00848933.
Lemma F_83aa8 : fetch_word Asan.M.loaded_segments (0x83af8 : word) = Some W_83aa8.
Proof. vm_refl. Qed.
Lemma D_83aa8 : decode_any W_83aa8 = Some (Op ALU_ADD 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83aac : bv 32 := 0x05267263.
Lemma F_83aac : fetch_word Asan.M.loaded_segments (0x83afc : word) = Some W_83aac.
Proof. vm_refl. Qed.
Lemma D_83aac : decode_any W_83aac = Some (Branch BC_GEU 12 18 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ab0 : bv 32 := 0x000dd617.
Lemma F_83ab0 : fetch_word Asan.M.loaded_segments (0x83b00 : word) = Some W_83ab0.
Proof. vm_refl. Qed.
Lemma D_83ab0 : decode_any W_83ab0 = Some (Auipc 12 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ab4 : bv 32 := 0x12063603.
Lemma F_83ab4 : fetch_word Asan.M.loaded_segments (0x83b04 : word) = Some W_83ab4.
Proof. vm_refl. Qed.
Lemma D_83ab4 : decode_any W_83ab4 = Some (Load SZ8 true 12 12 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ab8 : bv 32 := 0x000dd697.
Lemma F_83ab8 : fetch_word Asan.M.loaded_segments (0x83b08 : word) = Some W_83ab8.
Proof. vm_refl. Qed.
Lemma D_83ab8 : decode_any W_83ab8 = Some (Auipc 13 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83abc : bv 32 := 0x1206b683.
Lemma F_83abc : fetch_word Asan.M.loaded_segments (0x83b0c : word) = Some W_83abc.
Proof. vm_refl. Qed.
Lemma D_83abc : decode_any W_83abc = Some (Load SZ8 true 13 13 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ac0 : bv 32 := 0x00063783.
Lemma F_83ac0 : fetch_word Asan.M.loaded_segments (0x83b10 : word) = Some W_83ac0.
Proof. vm_refl. Qed.
Lemma D_83ac0 : decode_any W_83ac0 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ac4 : bv 32 := 0x0006b603.
Lemma F_83ac4 : fetch_word Asan.M.loaded_segments (0x83b14 : word) = Some W_83ac4.
Proof. vm_refl. Qed.
Lemma D_83ac4 : decode_any W_83ac4 = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ac8 : bv 32 := 0xfff78713.
Lemma F_83ac8 : fetch_word Asan.M.loaded_segments (0x83b18 : word) = Some W_83ac8.
Proof. vm_refl. Qed.
Lemma D_83ac8 : decode_any W_83ac8 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83acc : bv 32 := 0x01277463.
Lemma F_83acc : fetch_word Asan.M.loaded_segments (0x83b1c : word) = Some W_83acc.
Proof. vm_refl. Qed.
Lemma D_83acc : decode_any W_83acc = Some (Branch BC_GEU 14 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ad4 : bv 32 := 0x000dd697.
Lemma F_83ad4 : fetch_word Asan.M.loaded_segments (0x83b24 : word) = Some W_83ad4.
Proof. vm_refl. Qed.
Lemma D_83ad4 : decode_any W_83ad4 = Some (Auipc 13 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ad8 : bv 32 := 0x10c6b683.
Lemma F_83ad8 : fetch_word Asan.M.loaded_segments (0x83b28 : word) = Some W_83ad8.
Proof. vm_refl. Qed.
Lemma D_83ad8 : decode_any W_83ad8 = Some (Load SZ8 true 13 13 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83adc : bv 32 := 0x0006b883.
Lemma F_83adc : fetch_word Asan.M.loaded_segments (0x83b2c : word) = Some W_83adc.
Proof. vm_refl. Qed.
Lemma D_83adc : decode_any W_83adc = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ae0 : bv 32 := 0x0038d693.
Lemma F_83ae0 : fetch_word Asan.M.loaded_segments (0x83b30 : word) = Some W_83ae0.
Proof. vm_refl. Qed.
Lemma D_83ae0 : decode_any W_83ae0 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ae4 : bv 32 := 0x00b68833.
Lemma F_83ae4 : fetch_word Asan.M.loaded_segments (0x83b34 : word) = Some W_83ae4.
Proof. vm_refl. Qed.
Lemma D_83ae4 : decode_any W_83ae4 = Some (Op ALU_ADD 16 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ae8 : bv 32 := 0x1328e463.
Lemma F_83ae8 : fetch_word Asan.M.loaded_segments (0x83b38 : word) = Some W_83ae8.
Proof. vm_refl. Qed.
Lemma D_83ae8 : decode_any W_83ae8 = Some (Branch BC_LTU 17 18 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83aec : bv 32 := 0x13287263.
Lemma F_83aec : fetch_word Asan.M.loaded_segments (0x83b3c : word) = Some W_83aec.
Proof. vm_refl. Qed.
Lemma D_83aec : decode_any W_83aec = Some (Branch BC_GEU 16 18 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83af0 : bv 32 := 0x23247863.
Lemma F_83af0 : fetch_word Asan.M.loaded_segments (0x83b40 : word) = Some W_83af0.
Proof. vm_refl. Qed.
Lemma D_83af0 : decode_any W_83af0 = Some (Branch BC_GEU 8 18 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83af4 : bv 32 := 0x00740513.
Lemma F_83af4 : fetch_word Asan.M.loaded_segments (0x83b44 : word) = Some W_83af4.
Proof. vm_refl. Qed.
Lemma D_83af4 : decode_any W_83af4 = Some (OpImm ALU_ADD 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83af8 : bv 32 := 0xff857513.
Lemma F_83af8 : fetch_word Asan.M.loaded_segments (0x83b48 : word) = Some W_83af8.
Proof. vm_refl. Qed.
Lemma D_83af8 : decode_any W_83af8 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83afc : bv 32 := 0xff897a13.
Lemma F_83afc : fetch_word Asan.M.loaded_segments (0x83b4c : word) = Some W_83afc.
Proof. vm_refl. Qed.
Lemma D_83afc : decode_any W_83afc = Some (OpImm ALU_AND 20 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b00 : bv 32 := 0xa91ff0ef.
Lemma F_83b00 : fetch_word Asan.M.loaded_segments (0x83b50 : word) = Some W_83b00.
Proof. vm_refl. Qed.
Lemma D_83b00 : decode_any W_83b00 = Some (Jal 1 2095760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b04 : bv 32 := 0x00050993.
Lemma F_83b04 : fetch_word Asan.M.loaded_segments (0x83b54 : word) = Some W_83b04.
Proof. vm_refl. Qed.
Lemma D_83b04 : decode_any W_83b04 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b08 : bv 32 := 0x000a0513.
Lemma F_83b08 : fetch_word Asan.M.loaded_segments (0x83b58 : word) = Some W_83b08.
Proof. vm_refl. Qed.
Lemma D_83b08 : decode_any W_83b08 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b0c : bv 32 := 0xa85ff0ef.
Lemma F_83b0c : fetch_word Asan.M.loaded_segments (0x83b5c : word) = Some W_83b0c.
Proof. vm_refl. Qed.
Lemma D_83b0c : decode_any W_83b0c = Some (Jal 1 2095748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b10 : bv 32 := 0x000ab583.
Lemma F_83b10 : fetch_word Asan.M.loaded_segments (0x83b60 : word) = Some W_83b10.
Proof. vm_refl. Qed.
Lemma D_83b10 : decode_any W_83b10 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b14 : bv 32 := 0x00345613.
Lemma F_83b14 : fetch_word Asan.M.loaded_segments (0x83b64 : word) = Some W_83b14.
Proof. vm_refl. Qed.
Lemma D_83b14 : decode_any W_83b14 = Some (ShiftImm ALU_SRL 12 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b18 : bv 32 := 0x00c58633.
Lemma F_83b18 : fetch_word Asan.M.loaded_segments (0x83b68 : word) = Some W_83b18.
Proof. vm_refl. Qed.
Lemma D_83b18 : decode_any W_83b18 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b1c : bv 32 := 0x00060603.
Lemma F_83b1c : fetch_word Asan.M.loaded_segments (0x83b6c : word) = Some W_83b1c.
Proof. vm_refl. Qed.
Lemma D_83b1c : decode_any W_83b1c = Some (Load SZ1 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b20 : bv 32 := 0x00060663.
Lemma F_83b20 : fetch_word Asan.M.loaded_segments (0x83b70 : word) = Some W_83b20.
Proof. vm_refl. Qed.
Lemma D_83b20 : decode_any W_83b20 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b24 : bv 32 := 0x00747693.
Lemma F_83b24 : fetch_word Asan.M.loaded_segments (0x83b74 : word) = Some W_83b24.
Proof. vm_refl. Qed.
Lemma D_83b24 : decode_any W_83b24 = Some (OpImm ALU_AND 13 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b28 : bv 32 := 0x02c6d063.
Lemma F_83b28 : fetch_word Asan.M.loaded_segments (0x83b78 : word) = Some W_83b28.
Proof. vm_refl. Qed.
Lemma D_83b28 : decode_any W_83b28 = Some (Branch BC_GE 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b2c : bv 32 := 0xfff90913.
Lemma F_83b2c : fetch_word Asan.M.loaded_segments (0x83b7c : word) = Some W_83b2c.
Proof. vm_refl. Qed.
Lemma D_83b2c : decode_any W_83b2c = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b30 : bv 32 := 0x00395613.
Lemma F_83b30 : fetch_word Asan.M.loaded_segments (0x83b80 : word) = Some W_83b30.
Proof. vm_refl. Qed.
Lemma D_83b30 : decode_any W_83b30 = Some (ShiftImm ALU_SRL 12 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b34 : bv 32 := 0x00c585b3.
Lemma F_83b34 : fetch_word Asan.M.loaded_segments (0x83b84 : word) = Some W_83b34.
Proof. vm_refl. Qed.
Lemma D_83b34 : decode_any W_83b34 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b38 : bv 32 := 0x00058583.
Lemma F_83b38 : fetch_word Asan.M.loaded_segments (0x83b88 : word) = Some W_83b38.
Proof. vm_refl. Qed.
Lemma D_83b38 : decode_any W_83b38 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b3c : bv 32 := 0x04058263.
Lemma F_83b3c : fetch_word Asan.M.loaded_segments (0x83b8c : word) = Some W_83b3c.
Proof. vm_refl. Qed.
Lemma D_83b3c : decode_any W_83b3c = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b40 : bv 32 := 0x00797613.
Lemma F_83b40 : fetch_word Asan.M.loaded_segments (0x83b90 : word) = Some W_83b40.
Proof. vm_refl. Qed.
Lemma D_83b40 : decode_any W_83b40 = Some (OpImm ALU_AND 12 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b44 : bv 32 := 0x02b64e63.
Lemma F_83b44 : fetch_word Asan.M.loaded_segments (0x83b94 : word) = Some W_83b44.
Proof. vm_refl. Qed.
Lemma D_83b44 : decode_any W_83b44 = Some (Branch BC_LT 12 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b80 : bv 32 := 0x00a9fa63.
Lemma F_83b80 : fetch_word Asan.M.loaded_segments (0x83bd0 : word) = Some W_83b80.
Proof. vm_refl. Qed.
Lemma D_83b80 : decode_any W_83b80 = Some (Branch BC_GEU 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b84 : bv 32 := 0x413505b3.
Lemma F_83b84 : fetch_word Asan.M.loaded_segments (0x83bd4 : word) = Some W_83b84.
Proof. vm_refl. Qed.
Lemma D_83b84 : decode_any W_83b84 = Some (Op ALU_SUB 11 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b88 : bv 32 := 0x00098513.
Lemma F_83b88 : fetch_word Asan.M.loaded_segments (0x83bd8 : word) = Some W_83b88.
Proof. vm_refl. Qed.
Lemma D_83b88 : decode_any W_83b88 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b8c : bv 32 := 0x37c100ef.
Lemma F_83b8c : fetch_word Asan.M.loaded_segments (0x83bdc : word) = Some W_83b8c.
Proof. vm_refl. Qed.
Lemma D_83b8c : decode_any W_83b8c = Some (Jal 1 66428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b90 : bv 32 := 0xfa050ce3.
Lemma F_83b90 : fetch_word Asan.M.loaded_segments (0x83be0 : word) = Some W_83b90.
Proof. vm_refl. Qed.
Lemma D_83b90 : decode_any W_83b90 = Some (Branch BC_EQ 10 0 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b94 : bv 32 := 0x00000413.
Lemma F_83b94 : fetch_word Asan.M.loaded_segments (0x83be4 : word) = Some W_83b94.
Proof. vm_refl. Qed.
Lemma D_83b94 : decode_any W_83b94 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b98 : bv 32 := 0x00040513.
Lemma F_83b98 : fetch_word Asan.M.loaded_segments (0x83be8 : word) = Some W_83b98.
Proof. vm_refl. Qed.
Lemma D_83b98 : decode_any W_83b98 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83b9c : bv 32 := 0x03813083.
Lemma F_83b9c : fetch_word Asan.M.loaded_segments (0x83bec : word) = Some W_83b9c.
Proof. vm_refl. Qed.
Lemma D_83b9c : decode_any W_83b9c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ba0 : bv 32 := 0x03013403.
Lemma F_83ba0 : fetch_word Asan.M.loaded_segments (0x83bf0 : word) = Some W_83ba0.
Proof. vm_refl. Qed.
Lemma D_83ba0 : decode_any W_83ba0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ba4 : bv 32 := 0x02813483.
Lemma F_83ba4 : fetch_word Asan.M.loaded_segments (0x83bf4 : word) = Some W_83ba4.
Proof. vm_refl. Qed.
Lemma D_83ba4 : decode_any W_83ba4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83ba8 : bv 32 := 0x02013903.
Lemma F_83ba8 : fetch_word Asan.M.loaded_segments (0x83bf8 : word) = Some W_83ba8.
Proof. vm_refl. Qed.
Lemma D_83ba8 : decode_any W_83ba8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bac : bv 32 := 0x01813983.
Lemma F_83bac : fetch_word Asan.M.loaded_segments (0x83bfc : word) = Some W_83bac.
Proof. vm_refl. Qed.
Lemma D_83bac : decode_any W_83bac = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bb0 : bv 32 := 0x01013a03.
Lemma F_83bb0 : fetch_word Asan.M.loaded_segments (0x83c00 : word) = Some W_83bb0.
Proof. vm_refl. Qed.
Lemma D_83bb0 : decode_any W_83bb0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bb4 : bv 32 := 0x00813a83.
Lemma F_83bb4 : fetch_word Asan.M.loaded_segments (0x83c04 : word) = Some W_83bb4.
Proof. vm_refl. Qed.
Lemma D_83bb4 : decode_any W_83bb4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bb8 : bv 32 := 0x04010113.
Lemma F_83bb8 : fetch_word Asan.M.loaded_segments (0x83c08 : word) = Some W_83bb8.
Proof. vm_refl. Qed.
Lemma D_83bb8 : decode_any W_83bb8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_83bbc : bv 32 := 0x00008067.
Lemma F_83bbc : fetch_word Asan.M.loaded_segments (0x83c0c : word) = Some W_83bbc.
Proof. vm_refl. Qed.
Lemma D_83bbc : decode_any W_83bbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

