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
Definition W_6701c : bv 32 := 0x00160613.
Lemma F_6701c : fetch_word AsanUbsan.M.loaded_segments (0x67064 : word) = Some W_6701c.
Proof. vm_refl. Qed.
Lemma D_6701c : decode_any W_6701c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67020 : bv 32 := 0x00100513.
Lemma F_67020 : fetch_word AsanUbsan.M.loaded_segments (0x67068 : word) = Some W_67020.
Proof. vm_refl. Qed.
Lemma D_67020 : decode_any W_67020 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67024 : bv 32 := 0xffb90693.
Lemma F_67024 : fetch_word AsanUbsan.M.loaded_segments (0x6706c : word) = Some W_67024.
Proof. vm_refl. Qed.
Lemma D_67024 : decode_any W_67024 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67028 : bv 32 := 0x02c4b423.
Lemma F_67028 : fetch_word AsanUbsan.M.loaded_segments (0x67070 : word) = Some W_67028.
Proof. vm_refl. Qed.
Lemma D_67028 : decode_any W_67028 = Some (Store SZ8 9 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6702c : bv 32 := 0x00a78023.
Lemma F_6702c : fetch_word AsanUbsan.M.loaded_segments (0x67074 : word) = Some W_6702c.
Proof. vm_refl. Qed.
Lemma D_6702c : decode_any W_6702c = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67030 : bv 32 := 0x00d51533.
Lemma F_67030 : fetch_word AsanUbsan.M.loaded_segments (0x67078 : word) = Some W_67030.
Proof. vm_refl. Qed.
Lemma D_67030 : decode_any W_67030 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67034 : bv 32 := 0x00500613.
Lemma F_67034 : fetch_word AsanUbsan.M.loaded_segments (0x6707c : word) = Some W_67034.
Proof. vm_refl. Qed.
Lemma D_67034 : decode_any W_67034 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67038 : bv 32 := 0x00b89893.
Lemma F_67038 : fetch_word AsanUbsan.M.loaded_segments (0x67080 : word) = Some W_67038.
Proof. vm_refl. Qed.
Lemma D_67038 : decode_any W_67038 = Some (ShiftImm ALU_SLL 17 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6703c : bv 32 := 0x01261633.
Lemma F_6703c : fetch_word AsanUbsan.M.loaded_segments (0x67084 : word) = Some W_6703c.
Proof. vm_refl. Qed.
Lemma D_6703c : decode_any W_6703c = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67040 : bv 32 := 0x00a58533.
Lemma F_67040 : fetch_word AsanUbsan.M.loaded_segments (0x67088 : word) = Some W_67040.
Proof. vm_refl. Qed.
Lemma D_67040 : decode_any W_67040 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67044 : bv 32 := 0x01160633.
Lemma F_67044 : fetch_word AsanUbsan.M.loaded_segments (0x6708c : word) = Some W_67044.
Proof. vm_refl. Qed.
Lemma D_67044 : decode_any W_67044 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67048 : bv 32 := 0x00c504b3.
Lemma F_67048 : fetch_word AsanUbsan.M.loaded_segments (0x67090 : word) = Some W_67048.
Proof. vm_refl. Qed.
Lemma D_67048 : decode_any W_67048 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6704c : bv 32 := 0x0084bc23.
Lemma F_6704c : fetch_word AsanUbsan.M.loaded_segments (0x67094 : word) = Some W_6704c.
Proof. vm_refl. Qed.
Lemma D_6704c : decode_any W_6704c = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67050 : bv 32 := 0x7ef4bc23.
Lemma F_67050 : fetch_word AsanUbsan.M.loaded_segments (0x67098 : word) = Some W_67050.
Proof. vm_refl. Qed.
Lemma D_67050 : decode_any W_67050 = Some (Store SZ8 9 15 2040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67054 : bv 32 := 0x00048513.
Lemma F_67054 : fetch_word AsanUbsan.M.loaded_segments (0x6709c : word) = Some W_67054.
Proof. vm_refl. Qed.
Lemma D_67054 : decode_any W_67054 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67058 : bv 32 := 0x178000ef.
Lemma F_67058 : fetch_word AsanUbsan.M.loaded_segments (0x670a0 : word) = Some W_67058.
Proof. vm_refl. Qed.
Lemma D_67058 : decode_any W_67058 = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6705c : bv 32 := 0x00050593.
Lemma F_6705c : fetch_word AsanUbsan.M.loaded_segments (0x670a4 : word) = Some W_6705c.
Proof. vm_refl. Qed.
Lemma D_6705c : decode_any W_6705c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67060 : bv 32 := 0x00048513.
Lemma F_67060 : fetch_word AsanUbsan.M.loaded_segments (0x670a8 : word) = Some W_67060.
Proof. vm_refl. Qed.
Lemma D_67060 : decode_any W_67060 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67064 : bv 32 := 0x00000613.
Lemma F_67064 : fetch_word AsanUbsan.M.loaded_segments (0x670ac : word) = Some W_67064.
Proof. vm_refl. Qed.
Lemma D_67064 : decode_any W_67064 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67068 : bv 32 := 0x0005b023.
Lemma F_67068 : fetch_word AsanUbsan.M.loaded_segments (0x670b0 : word) = Some W_67068.
Proof. vm_refl. Qed.
Lemma D_67068 : decode_any W_67068 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6706c : bv 32 := 0x0005b423.
Lemma F_6706c : fetch_word AsanUbsan.M.loaded_segments (0x670b4 : word) = Some W_6706c.
Proof. vm_refl. Qed.
Lemma D_6706c : decode_any W_6706c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67070 : bv 32 := 0x0005b823.
Lemma F_67070 : fetch_word AsanUbsan.M.loaded_segments (0x670b8 : word) = Some W_67070.
Proof. vm_refl. Qed.
Lemma D_67070 : decode_any W_67070 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67074 : bv 32 := 0x0005bc23.
Lemma F_67074 : fetch_word AsanUbsan.M.loaded_segments (0x670bc : word) = Some W_67074.
Proof. vm_refl. Qed.
Lemma D_67074 : decode_any W_67074 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67078 : bv 32 := 0x0205b023.
Lemma F_67078 : fetch_word AsanUbsan.M.loaded_segments (0x670c0 : word) = Some W_67078.
Proof. vm_refl. Qed.
Lemma D_67078 : decode_any W_67078 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6707c : bv 32 := 0x0205b423.
Lemma F_6707c : fetch_word AsanUbsan.M.loaded_segments (0x670c4 : word) = Some W_6707c.
Proof. vm_refl. Qed.
Lemma D_6707c : decode_any W_6707c = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67080 : bv 32 := 0x0205b823.
Lemma F_67080 : fetch_word AsanUbsan.M.loaded_segments (0x670c8 : word) = Some W_67080.
Proof. vm_refl. Qed.
Lemma D_67080 : decode_any W_67080 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67084 : bv 32 := 0x0205bc23.
Lemma F_67084 : fetch_word AsanUbsan.M.loaded_segments (0x670cc : word) = Some W_67084.
Proof. vm_refl. Qed.
Lemma D_67084 : decode_any W_67084 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67088 : bv 32 := 0x0405b023.
Lemma F_67088 : fetch_word AsanUbsan.M.loaded_segments (0x670d0 : word) = Some W_67088.
Proof. vm_refl. Qed.
Lemma D_67088 : decode_any W_67088 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6708c : bv 32 := 0x0405b423.
Lemma F_6708c : fetch_word AsanUbsan.M.loaded_segments (0x670d4 : word) = Some W_6708c.
Proof. vm_refl. Qed.
Lemma D_6708c : decode_any W_6708c = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67090 : bv 32 := 0x0405b823.
Lemma F_67090 : fetch_word AsanUbsan.M.loaded_segments (0x670d8 : word) = Some W_67090.
Proof. vm_refl. Qed.
Lemma D_67090 : decode_any W_67090 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67094 : bv 32 := 0x0405bc23.
Lemma F_67094 : fetch_word AsanUbsan.M.loaded_segments (0x670dc : word) = Some W_67094.
Proof. vm_refl. Qed.
Lemma D_67094 : decode_any W_67094 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67098 : bv 32 := 0x0605b023.
Lemma F_67098 : fetch_word AsanUbsan.M.loaded_segments (0x670e0 : word) = Some W_67098.
Proof. vm_refl. Qed.
Lemma D_67098 : decode_any W_67098 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6709c : bv 32 := 0x0605b423.
Lemma F_6709c : fetch_word AsanUbsan.M.loaded_segments (0x670e4 : word) = Some W_6709c.
Proof. vm_refl. Qed.
Lemma D_6709c : decode_any W_6709c = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a0 : bv 32 := 0x0605b823.
Lemma F_670a0 : fetch_word AsanUbsan.M.loaded_segments (0x670e8 : word) = Some W_670a0.
Proof. vm_refl. Qed.
Lemma D_670a0 : decode_any W_670a0 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a4 : bv 32 := 0x0605bc23.
Lemma F_670a4 : fetch_word AsanUbsan.M.loaded_segments (0x670ec : word) = Some W_670a4.
Proof. vm_refl. Qed.
Lemma D_670a4 : decode_any W_670a4 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670a8 : bv 32 := 0x0805b023.
Lemma F_670a8 : fetch_word AsanUbsan.M.loaded_segments (0x670f0 : word) = Some W_670a8.
Proof. vm_refl. Qed.
Lemma D_670a8 : decode_any W_670a8 = Some (Store SZ8 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670ac : bv 32 := 0x0805b423.
Lemma F_670ac : fetch_word AsanUbsan.M.loaded_segments (0x670f4 : word) = Some W_670ac.
Proof. vm_refl. Qed.
Lemma D_670ac : decode_any W_670ac = Some (Store SZ8 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b0 : bv 32 := 0x0805b823.
Lemma F_670b0 : fetch_word AsanUbsan.M.loaded_segments (0x670f8 : word) = Some W_670b0.
Proof. vm_refl. Qed.
Lemma D_670b0 : decode_any W_670b0 = Some (Store SZ8 11 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b4 : bv 32 := 0x0805bc23.
Lemma F_670b4 : fetch_word AsanUbsan.M.loaded_segments (0x670fc : word) = Some W_670b4.
Proof. vm_refl. Qed.
Lemma D_670b4 : decode_any W_670b4 = Some (Store SZ8 11 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670b8 : bv 32 := 0x0a05b023.
Lemma F_670b8 : fetch_word AsanUbsan.M.loaded_segments (0x67100 : word) = Some W_670b8.
Proof. vm_refl. Qed.
Lemma D_670b8 : decode_any W_670b8 = Some (Store SZ8 11 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670bc : bv 32 := 0x0a05b423.
Lemma F_670bc : fetch_word AsanUbsan.M.loaded_segments (0x67104 : word) = Some W_670bc.
Proof. vm_refl. Qed.
Lemma D_670bc : decode_any W_670bc = Some (Store SZ8 11 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c0 : bv 32 := 0x0a05b823.
Lemma F_670c0 : fetch_word AsanUbsan.M.loaded_segments (0x67108 : word) = Some W_670c0.
Proof. vm_refl. Qed.
Lemma D_670c0 : decode_any W_670c0 = Some (Store SZ8 11 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c4 : bv 32 := 0x0a05bc23.
Lemma F_670c4 : fetch_word AsanUbsan.M.loaded_segments (0x6710c : word) = Some W_670c4.
Proof. vm_refl. Qed.
Lemma D_670c4 : decode_any W_670c4 = Some (Store SZ8 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670c8 : bv 32 := 0x0c05b023.
Lemma F_670c8 : fetch_word AsanUbsan.M.loaded_segments (0x67110 : word) = Some W_670c8.
Proof. vm_refl. Qed.
Lemma D_670c8 : decode_any W_670c8 = Some (Store SZ8 11 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670cc : bv 32 := 0x0c05b423.
Lemma F_670cc : fetch_word AsanUbsan.M.loaded_segments (0x67114 : word) = Some W_670cc.
Proof. vm_refl. Qed.
Lemma D_670cc : decode_any W_670cc = Some (Store SZ8 11 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d0 : bv 32 := 0x0c05b823.
Lemma F_670d0 : fetch_word AsanUbsan.M.loaded_segments (0x67118 : word) = Some W_670d0.
Proof. vm_refl. Qed.
Lemma D_670d0 : decode_any W_670d0 = Some (Store SZ8 11 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d4 : bv 32 := 0x0c05bc23.
Lemma F_670d4 : fetch_word AsanUbsan.M.loaded_segments (0x6711c : word) = Some W_670d4.
Proof. vm_refl. Qed.
Lemma D_670d4 : decode_any W_670d4 = Some (Store SZ8 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670d8 : bv 32 := 0x0e05b023.
Lemma F_670d8 : fetch_word AsanUbsan.M.loaded_segments (0x67120 : word) = Some W_670d8.
Proof. vm_refl. Qed.
Lemma D_670d8 : decode_any W_670d8 = Some (Store SZ8 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670dc : bv 32 := 0x0e05b423.
Lemma F_670dc : fetch_word AsanUbsan.M.loaded_segments (0x67124 : word) = Some W_670dc.
Proof. vm_refl. Qed.
Lemma D_670dc : decode_any W_670dc = Some (Store SZ8 11 0 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e0 : bv 32 := 0x0e05b823.
Lemma F_670e0 : fetch_word AsanUbsan.M.loaded_segments (0x67128 : word) = Some W_670e0.
Proof. vm_refl. Qed.
Lemma D_670e0 : decode_any W_670e0 = Some (Store SZ8 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e4 : bv 32 := 0x0e05bc23.
Lemma F_670e4 : fetch_word AsanUbsan.M.loaded_segments (0x6712c : word) = Some W_670e4.
Proof. vm_refl. Qed.
Lemma D_670e4 : decode_any W_670e4 = Some (Store SZ8 11 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670e8 : bv 32 := 0x01813083.
Lemma F_670e8 : fetch_word AsanUbsan.M.loaded_segments (0x67130 : word) = Some W_670e8.
Proof. vm_refl. Qed.
Lemma D_670e8 : decode_any W_670e8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670ec : bv 32 := 0x01013403.
Lemma F_670ec : fetch_word AsanUbsan.M.loaded_segments (0x67134 : word) = Some W_670ec.
Proof. vm_refl. Qed.
Lemma D_670ec : decode_any W_670ec = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670f0 : bv 32 := 0x00813483.
Lemma F_670f0 : fetch_word AsanUbsan.M.loaded_segments (0x67138 : word) = Some W_670f0.
Proof. vm_refl. Qed.
Lemma D_670f0 : decode_any W_670f0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670f4 : bv 32 := 0x00013903.
Lemma F_670f4 : fetch_word AsanUbsan.M.loaded_segments (0x6713c : word) = Some W_670f4.
Proof. vm_refl. Qed.
Lemma D_670f4 : decode_any W_670f4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670f8 : bv 32 := 0x02010113.
Lemma F_670f8 : fetch_word AsanUbsan.M.loaded_segments (0x67140 : word) = Some W_670f8.
Proof. vm_refl. Qed.
Lemma D_670f8 : decode_any W_670f8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_670fc : bv 32 := 0x00008067.
Lemma F_670fc : fetch_word AsanUbsan.M.loaded_segments (0x67144 : word) = Some W_670fc.
Proof. vm_refl. Qed.
Lemma D_670fc : decode_any W_670fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6711c : bv 32 := 0xff010113.
Lemma F_6711c : fetch_word AsanUbsan.M.loaded_segments (0x67164 : word) = Some W_6711c.
Proof. vm_refl. Qed.
Lemma D_6711c : decode_any W_6711c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67120 : bv 32 := 0x00113423.
Lemma F_67120 : fetch_word AsanUbsan.M.loaded_segments (0x67168 : word) = Some W_67120.
Proof. vm_refl. Qed.
Lemma D_67120 : decode_any W_67120 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67124 : bv 32 := 0x00813023.
Lemma F_67124 : fetch_word AsanUbsan.M.loaded_segments (0x6716c : word) = Some W_67124.
Proof. vm_refl. Qed.
Lemma D_67124 : decode_any W_67124 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67128 : bv 32 := 0x7f853583.
Lemma F_67128 : fetch_word AsanUbsan.M.loaded_segments (0x67170 : word) = Some W_67128.
Proof. vm_refl. Qed.
Lemma D_67128 : decode_any W_67128 = Some (Load SZ8 true 11 10 2040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6712c : bv 32 := 0x00000413.
Lemma F_6712c : fetch_word AsanUbsan.M.loaded_segments (0x67174 : word) = Some W_6712c.
Proof. vm_refl. Qed.
Lemma D_6712c : decode_any W_6712c = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67130 : bv 32 := 0x00058023.
Lemma F_67130 : fetch_word AsanUbsan.M.loaded_segments (0x67178 : word) = Some W_67130.
Proof. vm_refl. Qed.
Lemma D_67130 : decode_any W_67130 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67134 : bv 32 := 0x09c000ef.
Lemma F_67134 : fetch_word AsanUbsan.M.loaded_segments (0x6717c : word) = Some W_67134.
Proof. vm_refl. Qed.
Lemma D_67134 : decode_any W_67134 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67138 : bv 32 := 0xfffa9597.
Lemma F_67138 : fetch_word AsanUbsan.M.loaded_segments (0x67180 : word) = Some W_67138.
Proof. vm_refl. Qed.
Lemma D_67138 : decode_any W_67138 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6713c : bv 32 := 0x2285b583.
Lemma F_6713c : fetch_word AsanUbsan.M.loaded_segments (0x67184 : word) = Some W_6713c.
Proof. vm_refl. Qed.
Lemma D_6713c : decode_any W_6713c = Some (Load SZ8 true 11 11 552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67140 : bv 32 := 0x00b53023.
Lemma F_67140 : fetch_word AsanUbsan.M.loaded_segments (0x67188 : word) = Some W_67140.
Proof. vm_refl. Qed.
Lemma D_67140 : decode_any W_67140 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67144 : bv 32 := 0x00b53423.
Lemma F_67144 : fetch_word AsanUbsan.M.loaded_segments (0x6718c : word) = Some W_67144.
Proof. vm_refl. Qed.
Lemma D_67144 : decode_any W_67144 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67148 : bv 32 := 0x00b53823.
Lemma F_67148 : fetch_word AsanUbsan.M.loaded_segments (0x67190 : word) = Some W_67148.
Proof. vm_refl. Qed.
Lemma D_67148 : decode_any W_67148 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6714c : bv 32 := 0x00b53c23.
Lemma F_6714c : fetch_word AsanUbsan.M.loaded_segments (0x67194 : word) = Some W_6714c.
Proof. vm_refl. Qed.
Lemma D_6714c : decode_any W_6714c = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67150 : bv 32 := 0x02b53023.
Lemma F_67150 : fetch_word AsanUbsan.M.loaded_segments (0x67198 : word) = Some W_67150.
Proof. vm_refl. Qed.
Lemma D_67150 : decode_any W_67150 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67154 : bv 32 := 0x02b53423.
Lemma F_67154 : fetch_word AsanUbsan.M.loaded_segments (0x6719c : word) = Some W_67154.
Proof. vm_refl. Qed.
Lemma D_67154 : decode_any W_67154 = Some (Store SZ8 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67158 : bv 32 := 0x02b53823.
Lemma F_67158 : fetch_word AsanUbsan.M.loaded_segments (0x671a0 : word) = Some W_67158.
Proof. vm_refl. Qed.
Lemma D_67158 : decode_any W_67158 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6715c : bv 32 := 0x02b53c23.
Lemma F_6715c : fetch_word AsanUbsan.M.loaded_segments (0x671a4 : word) = Some W_6715c.
Proof. vm_refl. Qed.
Lemma D_6715c : decode_any W_6715c = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67160 : bv 32 := 0x04b53023.
Lemma F_67160 : fetch_word AsanUbsan.M.loaded_segments (0x671a8 : word) = Some W_67160.
Proof. vm_refl. Qed.
Lemma D_67160 : decode_any W_67160 = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67164 : bv 32 := 0x04b53423.
Lemma F_67164 : fetch_word AsanUbsan.M.loaded_segments (0x671ac : word) = Some W_67164.
Proof. vm_refl. Qed.
Lemma D_67164 : decode_any W_67164 = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67168 : bv 32 := 0x04b53823.
Lemma F_67168 : fetch_word AsanUbsan.M.loaded_segments (0x671b0 : word) = Some W_67168.
Proof. vm_refl. Qed.
Lemma D_67168 : decode_any W_67168 = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6716c : bv 32 := 0x04b53c23.
Lemma F_6716c : fetch_word AsanUbsan.M.loaded_segments (0x671b4 : word) = Some W_6716c.
Proof. vm_refl. Qed.
Lemma D_6716c : decode_any W_6716c = Some (Store SZ8 10 11 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67170 : bv 32 := 0x06b53023.
Lemma F_67170 : fetch_word AsanUbsan.M.loaded_segments (0x671b8 : word) = Some W_67170.
Proof. vm_refl. Qed.
Lemma D_67170 : decode_any W_67170 = Some (Store SZ8 10 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67174 : bv 32 := 0x06b53423.
Lemma F_67174 : fetch_word AsanUbsan.M.loaded_segments (0x671bc : word) = Some W_67174.
Proof. vm_refl. Qed.
Lemma D_67174 : decode_any W_67174 = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67178 : bv 32 := 0x06b53823.
Lemma F_67178 : fetch_word AsanUbsan.M.loaded_segments (0x671c0 : word) = Some W_67178.
Proof. vm_refl. Qed.
Lemma D_67178 : decode_any W_67178 = Some (Store SZ8 10 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6717c : bv 32 := 0x06b53c23.
Lemma F_6717c : fetch_word AsanUbsan.M.loaded_segments (0x671c4 : word) = Some W_6717c.
Proof. vm_refl. Qed.
Lemma D_6717c : decode_any W_6717c = Some (Store SZ8 10 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67180 : bv 32 := 0x08b53023.
Lemma F_67180 : fetch_word AsanUbsan.M.loaded_segments (0x671c8 : word) = Some W_67180.
Proof. vm_refl. Qed.
Lemma D_67180 : decode_any W_67180 = Some (Store SZ8 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67184 : bv 32 := 0x08b53423.
Lemma F_67184 : fetch_word AsanUbsan.M.loaded_segments (0x671cc : word) = Some W_67184.
Proof. vm_refl. Qed.
Lemma D_67184 : decode_any W_67184 = Some (Store SZ8 10 11 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67188 : bv 32 := 0x08b53823.
Lemma F_67188 : fetch_word AsanUbsan.M.loaded_segments (0x671d0 : word) = Some W_67188.
Proof. vm_refl. Qed.
Lemma D_67188 : decode_any W_67188 = Some (Store SZ8 10 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6718c : bv 32 := 0x08b53c23.
Lemma F_6718c : fetch_word AsanUbsan.M.loaded_segments (0x671d4 : word) = Some W_6718c.
Proof. vm_refl. Qed.
Lemma D_6718c : decode_any W_6718c = Some (Store SZ8 10 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67190 : bv 32 := 0x0ab53023.
Lemma F_67190 : fetch_word AsanUbsan.M.loaded_segments (0x671d8 : word) = Some W_67190.
Proof. vm_refl. Qed.
Lemma D_67190 : decode_any W_67190 = Some (Store SZ8 10 11 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67194 : bv 32 := 0x0ab53423.
Lemma F_67194 : fetch_word AsanUbsan.M.loaded_segments (0x671dc : word) = Some W_67194.
Proof. vm_refl. Qed.
Lemma D_67194 : decode_any W_67194 = Some (Store SZ8 10 11 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67198 : bv 32 := 0x0ab53823.
Lemma F_67198 : fetch_word AsanUbsan.M.loaded_segments (0x671e0 : word) = Some W_67198.
Proof. vm_refl. Qed.
Lemma D_67198 : decode_any W_67198 = Some (Store SZ8 10 11 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6719c : bv 32 := 0x0ab53c23.
Lemma F_6719c : fetch_word AsanUbsan.M.loaded_segments (0x671e4 : word) = Some W_6719c.
Proof. vm_refl. Qed.
Lemma D_6719c : decode_any W_6719c = Some (Store SZ8 10 11 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671a0 : bv 32 := 0x0cb53023.
Lemma F_671a0 : fetch_word AsanUbsan.M.loaded_segments (0x671e8 : word) = Some W_671a0.
Proof. vm_refl. Qed.
Lemma D_671a0 : decode_any W_671a0 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671a4 : bv 32 := 0x0cb53423.
Lemma F_671a4 : fetch_word AsanUbsan.M.loaded_segments (0x671ec : word) = Some W_671a4.
Proof. vm_refl. Qed.
Lemma D_671a4 : decode_any W_671a4 = Some (Store SZ8 10 11 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671a8 : bv 32 := 0x0cb53823.
Lemma F_671a8 : fetch_word AsanUbsan.M.loaded_segments (0x671f0 : word) = Some W_671a8.
Proof. vm_refl. Qed.
Lemma D_671a8 : decode_any W_671a8 = Some (Store SZ8 10 11 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671ac : bv 32 := 0x0cb53c23.
Lemma F_671ac : fetch_word AsanUbsan.M.loaded_segments (0x671f4 : word) = Some W_671ac.
Proof. vm_refl. Qed.
Lemma D_671ac : decode_any W_671ac = Some (Store SZ8 10 11 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671b0 : bv 32 := 0x0eb53023.
Lemma F_671b0 : fetch_word AsanUbsan.M.loaded_segments (0x671f8 : word) = Some W_671b0.
Proof. vm_refl. Qed.
Lemma D_671b0 : decode_any W_671b0 = Some (Store SZ8 10 11 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671b4 : bv 32 := 0x0eb53423.
Lemma F_671b4 : fetch_word AsanUbsan.M.loaded_segments (0x671fc : word) = Some W_671b4.
Proof. vm_refl. Qed.
Lemma D_671b4 : decode_any W_671b4 = Some (Store SZ8 10 11 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671b8 : bv 32 := 0x0eb53823.
Lemma F_671b8 : fetch_word AsanUbsan.M.loaded_segments (0x67200 : word) = Some W_671b8.
Proof. vm_refl. Qed.
Lemma D_671b8 : decode_any W_671b8 = Some (Store SZ8 10 11 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671bc : bv 32 := 0x0eb53c23.
Lemma F_671bc : fetch_word AsanUbsan.M.loaded_segments (0x67204 : word) = Some W_671bc.
Proof. vm_refl. Qed.
Lemma D_671bc : decode_any W_671bc = Some (Store SZ8 10 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671c0 : bv 32 := 0x00813083.
Lemma F_671c0 : fetch_word AsanUbsan.M.loaded_segments (0x67208 : word) = Some W_671c0.
Proof. vm_refl. Qed.
Lemma D_671c0 : decode_any W_671c0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671c4 : bv 32 := 0x00013403.
Lemma F_671c4 : fetch_word AsanUbsan.M.loaded_segments (0x6720c : word) = Some W_671c4.
Proof. vm_refl. Qed.
Lemma D_671c4 : decode_any W_671c4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671c8 : bv 32 := 0x01010113.
Lemma F_671c8 : fetch_word AsanUbsan.M.loaded_segments (0x67210 : word) = Some W_671c8.
Proof. vm_refl. Qed.
Lemma D_671c8 : decode_any W_671c8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671cc : bv 32 := 0x00008067.
Lemma F_671cc : fetch_word AsanUbsan.M.loaded_segments (0x67214 : word) = Some W_671cc.
Proof. vm_refl. Qed.
Lemma D_671cc : decode_any W_671cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671d0 : bv 32 := 0x000fd597.
Lemma F_671d0 : fetch_word AsanUbsan.M.loaded_segments (0x67218 : word) = Some W_671d0.
Proof. vm_refl. Qed.
Lemma D_671d0 : decode_any W_671d0 = Some (Auipc 11 253, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671d4 : bv 32 := 0x3005b583.
Lemma F_671d4 : fetch_word AsanUbsan.M.loaded_segments (0x6721c : word) = Some W_671d4.
Proof. vm_refl. Qed.
Lemma D_671d4 : decode_any W_671d4 = Some (Load SZ8 true 11 11 768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671d8 : bv 32 := 0x0005b583.
Lemma F_671d8 : fetch_word AsanUbsan.M.loaded_segments (0x67220 : word) = Some W_671d8.
Proof. vm_refl. Qed.
Lemma D_671d8 : decode_any W_671d8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671dc : bv 32 := 0xfff58613.
Lemma F_671dc : fetch_word AsanUbsan.M.loaded_segments (0x67224 : word) = Some W_671dc.
Proof. vm_refl. Qed.
Lemma D_671dc : decode_any W_671dc = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671e0 : bv 32 := 0x00c5b6b3.
Lemma F_671e0 : fetch_word AsanUbsan.M.loaded_segments (0x67228 : word) = Some W_671e0.
Proof. vm_refl. Qed.
Lemma D_671e0 : decode_any W_671e0 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671e4 : bv 32 := 0xfff68693.
Lemma F_671e4 : fetch_word AsanUbsan.M.loaded_segments (0x6722c : word) = Some W_671e4.
Proof. vm_refl. Qed.
Lemma D_671e4 : decode_any W_671e4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671e8 : bv 32 := 0x00c6f6b3.
Lemma F_671e8 : fetch_word AsanUbsan.M.loaded_segments (0x67230 : word) = Some W_671e8.
Proof. vm_refl. Qed.
Lemma D_671e8 : decode_any W_671e8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671ec : bv 32 := 0x04a6f263.
Lemma F_671ec : fetch_word AsanUbsan.M.loaded_segments (0x67234 : word) = Some W_671ec.
Proof. vm_refl. Qed.
Lemma D_671ec : decode_any W_671ec = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671f0 : bv 32 := 0x000fd697.
Lemma F_671f0 : fetch_word AsanUbsan.M.loaded_segments (0x67238 : word) = Some W_671f0.
Proof. vm_refl. Qed.
Lemma D_671f0 : decode_any W_671f0 = Some (Auipc 13 253, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671f4 : bv 32 := 0x2e86b683.
Lemma F_671f4 : fetch_word AsanUbsan.M.loaded_segments (0x6723c : word) = Some W_671f4.
Proof. vm_refl. Qed.
Lemma D_671f4 : decode_any W_671f4 = Some (Load SZ8 true 13 13 744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671f8 : bv 32 := 0x000fd717.
Lemma F_671f8 : fetch_word AsanUbsan.M.loaded_segments (0x67240 : word) = Some W_671f8.
Proof. vm_refl. Qed.
Lemma D_671f8 : decode_any W_671f8 = Some (Auipc 14 253, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671fc : bv 32 := 0x2e873703.
Lemma F_671fc : fetch_word AsanUbsan.M.loaded_segments (0x67244 : word) = Some W_671fc.
Proof. vm_refl. Qed.
Lemma D_671fc : decode_any W_671fc = Some (Load SZ8 true 14 14 744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67200 : bv 32 := 0x0006b803.
Lemma F_67200 : fetch_word AsanUbsan.M.loaded_segments (0x67248 : word) = Some W_67200.
Proof. vm_refl. Qed.
Lemma D_67200 : decode_any W_67200 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67204 : bv 32 := 0x00073683.
Lemma F_67204 : fetch_word AsanUbsan.M.loaded_segments (0x6724c : word) = Some W_67204.
Proof. vm_refl. Qed.
Lemma D_67204 : decode_any W_67204 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67208 : bv 32 := 0xfff80793.
Lemma F_67208 : fetch_word AsanUbsan.M.loaded_segments (0x67250 : word) = Some W_67208.
Proof. vm_refl. Qed.
Lemma D_67208 : decode_any W_67208 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6720c : bv 32 := 0x00a7f463.
Lemma F_6720c : fetch_word AsanUbsan.M.loaded_segments (0x67254 : word) = Some W_6720c.
Proof. vm_refl. Qed.
Lemma D_6720c : decode_any W_6720c = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67214 : bv 32 := 0x000fd717.
Lemma F_67214 : fetch_word AsanUbsan.M.loaded_segments (0x6725c : word) = Some W_67214.
Proof. vm_refl. Qed.
Lemma D_67214 : decode_any W_67214 = Some (Auipc 14 253, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67218 : bv 32 := 0x2d473703.
Lemma F_67218 : fetch_word AsanUbsan.M.loaded_segments (0x67260 : word) = Some W_67218.
Proof. vm_refl. Qed.
Lemma D_67218 : decode_any W_67218 = Some (Load SZ8 true 14 14 724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6721c : bv 32 := 0x00073283.
Lemma F_6721c : fetch_word AsanUbsan.M.loaded_segments (0x67264 : word) = Some W_6721c.
Proof. vm_refl. Qed.
Lemma D_6721c : decode_any W_6721c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67220 : bv 32 := 0x0032d713.
Lemma F_67220 : fetch_word AsanUbsan.M.loaded_segments (0x67268 : word) = Some W_67220.
Proof. vm_refl. Qed.
Lemma D_67220 : decode_any W_67220 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67224 : bv 32 := 0x00b708b3.
Lemma F_67224 : fetch_word AsanUbsan.M.loaded_segments (0x6726c : word) = Some W_67224.
Proof. vm_refl. Qed.
Lemma D_67224 : decode_any W_67224 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67228 : bv 32 := 0x00a2ea63.
Lemma F_67228 : fetch_word AsanUbsan.M.loaded_segments (0x67270 : word) = Some W_67228.
Proof. vm_refl. Qed.
Lemma D_67228 : decode_any W_67228 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6722c : bv 32 := 0x00a8f863.
Lemma F_6722c : fetch_word AsanUbsan.M.loaded_segments (0x67274 : word) = Some W_6722c.
Proof. vm_refl. Qed.
Lemma D_6722c : decode_any W_6722c = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67230 : bv 32 := 0x00355513.
Lemma F_67230 : fetch_word AsanUbsan.M.loaded_segments (0x67278 : word) = Some W_67230.
Proof. vm_refl. Qed.
Lemma D_67230 : decode_any W_67230 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67234 : bv 32 := 0x00a58533.
Lemma F_67234 : fetch_word AsanUbsan.M.loaded_segments (0x6727c : word) = Some W_67234.
Proof. vm_refl. Qed.
Lemma D_67234 : decode_any W_67234 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67238 : bv 32 := 0x00008067.
Lemma F_67238 : fetch_word AsanUbsan.M.loaded_segments (0x67280 : word) = Some W_67238.
Proof. vm_refl. Qed.
Lemma D_67238 : decode_any W_67238 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

