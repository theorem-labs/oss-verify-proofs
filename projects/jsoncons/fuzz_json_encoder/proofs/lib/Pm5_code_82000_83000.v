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
Definition W_82020 : bv 32 := 0x02061e63.
Lemma F_82020 : fetch_word AsanUbsan.M.loaded_segments (0x82068 : word) = Some W_82020.
Proof. vm_refl. Qed.
Lemma D_82020 : decode_any W_82020 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82024 : bv 32 := 0xd4dff06f.
Lemma F_82024 : fetch_word AsanUbsan.M.loaded_segments (0x8206c : word) = Some W_82024.
Proof. vm_refl. Qed.
Lemma D_82024 : decode_any W_82024 = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82028 : bv 32 := 0x00070783.
Lemma F_82028 : fetch_word AsanUbsan.M.loaded_segments (0x82070 : word) = Some W_82028.
Proof. vm_refl. Qed.
Lemma D_82028 : decode_any W_82028 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8202c : bv 32 := 0x0079f813.
Lemma F_8202c : fetch_word AsanUbsan.M.loaded_segments (0x82074 : word) = Some W_8202c.
Proof. vm_refl. Qed.
Lemma D_8202c : decode_any W_8202c = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82030 : bv 32 := 0x00f038b3.
Lemma F_82030 : fetch_word AsanUbsan.M.loaded_segments (0x82078 : word) = Some W_82030.
Proof. vm_refl. Qed.
Lemma D_82030 : decode_any W_82030 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82034 : bv 32 := 0x00f827b3.
Lemma F_82034 : fetch_word AsanUbsan.M.loaded_segments (0x8207c : word) = Some W_82034.
Proof. vm_refl. Qed.
Lemma D_82034 : decode_any W_82034 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82038 : bv 32 := 0x0017c793.
Lemma F_82038 : fetch_word AsanUbsan.M.loaded_segments (0x82080 : word) = Some W_82038.
Proof. vm_refl. Qed.
Lemma D_82038 : decode_any W_82038 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8203c : bv 32 := 0x00f8f7b3.
Lemma F_8203c : fetch_word AsanUbsan.M.loaded_segments (0x82084 : word) = Some W_8203c.
Proof. vm_refl. Qed.
Lemma D_8203c : decode_any W_8203c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82040 : bv 32 := 0x00e6fa63.
Lemma F_82040 : fetch_word AsanUbsan.M.loaded_segments (0x82088 : word) = Some W_82040.
Proof. vm_refl. Qed.
Lemma D_82040 : decode_any W_82040 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82044 : bv 32 := 0x0006c803.
Lemma F_82044 : fetch_word AsanUbsan.M.loaded_segments (0x8208c : word) = Some W_82044.
Proof. vm_refl. Qed.
Lemma D_82044 : decode_any W_82044 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82048 : bv 32 := 0x00168693.
Lemma F_82048 : fetch_word AsanUbsan.M.loaded_segments (0x82090 : word) = Some W_82048.
Proof. vm_refl. Qed.
Lemma D_82048 : decode_any W_82048 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8204c : bv 32 := 0x00f867b3.
Lemma F_8204c : fetch_word AsanUbsan.M.loaded_segments (0x82094 : word) = Some W_8204c.
Proof. vm_refl. Qed.
Lemma D_8204c : decode_any W_8204c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82050 : bv 32 := 0xfee69ae3.
Lemma F_82050 : fetch_word AsanUbsan.M.loaded_segments (0x82098 : word) = Some W_82050.
Proof. vm_refl. Qed.
Lemma D_82050 : decode_any W_82050 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82054 : bv 32 := 0x0ff7f693.
Lemma F_82054 : fetch_word AsanUbsan.M.loaded_segments (0x8209c : word) = Some W_82054.
Proof. vm_refl. Qed.
Lemma D_82054 : decode_any W_82054 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82058 : bv 32 := 0xd0068ce3.
Lemma F_82058 : fetch_word AsanUbsan.M.loaded_segments (0x820a0 : word) = Some W_82058.
Proof. vm_refl. Qed.
Lemma D_82058 : decode_any W_82058 = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8205c : bv 32 := 0x00050b93.
Lemma F_8205c : fetch_word AsanUbsan.M.loaded_segments (0x820a4 : word) = Some W_8205c.
Proof. vm_refl. Qed.
Lemma D_8205c : decode_any W_8205c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82060 : bv 32 := 0x00058513.
Lemma F_82060 : fetch_word AsanUbsan.M.loaded_segments (0x820a8 : word) = Some W_82060.
Proof. vm_refl. Qed.
Lemma D_82060 : decode_any W_82060 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82064 : bv 32 := 0x00058c13.
Lemma F_82064 : fetch_word AsanUbsan.M.loaded_segments (0x820ac : word) = Some W_82064.
Proof. vm_refl. Qed.
Lemma D_82064 : decode_any W_82064 = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82068 : bv 32 := 0x00060593.
Lemma F_82068 : fetch_word AsanUbsan.M.loaded_segments (0x820b0 : word) = Some W_82068.
Proof. vm_refl. Qed.
Lemma D_82068 : decode_any W_82068 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8206c : bv 32 := 0x00060493.
Lemma F_8206c : fetch_word AsanUbsan.M.loaded_segments (0x820b4 : word) = Some W_8206c.
Proof. vm_refl. Qed.
Lemma D_8206c : decode_any W_8206c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82070 : bv 32 := 0x284020ef.
Lemma F_82070 : fetch_word AsanUbsan.M.loaded_segments (0x820b8 : word) = Some W_82070.
Proof. vm_refl. Qed.
Lemma D_82070 : decode_any W_82070 = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82074 : bv 32 := 0x000c0593.
Lemma F_82074 : fetch_word AsanUbsan.M.loaded_segments (0x820bc : word) = Some W_82074.
Proof. vm_refl. Qed.
Lemma D_82074 : decode_any W_82074 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82078 : bv 32 := 0x00048613.
Lemma F_82078 : fetch_word AsanUbsan.M.loaded_segments (0x820c0 : word) = Some W_82078.
Proof. vm_refl. Qed.
Lemma D_82078 : decode_any W_82078 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8207c : bv 32 := 0x00050913.
Lemma F_8207c : fetch_word AsanUbsan.M.loaded_segments (0x820c4 : word) = Some W_8207c.
Proof. vm_refl. Qed.
Lemma D_8207c : decode_any W_8207c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82080 : bv 32 := 0x000b8513.
Lemma F_82080 : fetch_word AsanUbsan.M.loaded_segments (0x820c8 : word) = Some W_82080.
Proof. vm_refl. Qed.
Lemma D_82080 : decode_any W_82080 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82084 : bv 32 := 0xce0906e3.
Lemma F_82084 : fetch_word AsanUbsan.M.loaded_segments (0x820cc : word) = Some W_82084.
Proof. vm_refl. Qed.
Lemma D_82084 : decode_any W_82084 = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82128 : bv 32 := 0x00070783.
Lemma F_82128 : fetch_word AsanUbsan.M.loaded_segments (0x82170 : word) = Some W_82128.
Proof. vm_refl. Qed.
Lemma D_82128 : decode_any W_82128 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8212c : bv 32 := 0x007a7813.
Lemma F_8212c : fetch_word AsanUbsan.M.loaded_segments (0x82174 : word) = Some W_8212c.
Proof. vm_refl. Qed.
Lemma D_8212c : decode_any W_8212c = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82130 : bv 32 := 0x00f038b3.
Lemma F_82130 : fetch_word AsanUbsan.M.loaded_segments (0x82178 : word) = Some W_82130.
Proof. vm_refl. Qed.
Lemma D_82130 : decode_any W_82130 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82134 : bv 32 := 0x00f827b3.
Lemma F_82134 : fetch_word AsanUbsan.M.loaded_segments (0x8217c : word) = Some W_82134.
Proof. vm_refl. Qed.
Lemma D_82134 : decode_any W_82134 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82138 : bv 32 := 0x0017c793.
Lemma F_82138 : fetch_word AsanUbsan.M.loaded_segments (0x82180 : word) = Some W_82138.
Proof. vm_refl. Qed.
Lemma D_82138 : decode_any W_82138 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8213c : bv 32 := 0x00f8f7b3.
Lemma F_8213c : fetch_word AsanUbsan.M.loaded_segments (0x82184 : word) = Some W_8213c.
Proof. vm_refl. Qed.
Lemma D_8213c : decode_any W_8213c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82140 : bv 32 := 0x00e6fa63.
Lemma F_82140 : fetch_word AsanUbsan.M.loaded_segments (0x82188 : word) = Some W_82140.
Proof. vm_refl. Qed.
Lemma D_82140 : decode_any W_82140 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82144 : bv 32 := 0x0006c803.
Lemma F_82144 : fetch_word AsanUbsan.M.loaded_segments (0x8218c : word) = Some W_82144.
Proof. vm_refl. Qed.
Lemma D_82144 : decode_any W_82144 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82148 : bv 32 := 0x00168693.
Lemma F_82148 : fetch_word AsanUbsan.M.loaded_segments (0x82190 : word) = Some W_82148.
Proof. vm_refl. Qed.
Lemma D_82148 : decode_any W_82148 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8214c : bv 32 := 0x00f867b3.
Lemma F_8214c : fetch_word AsanUbsan.M.loaded_segments (0x82194 : word) = Some W_8214c.
Proof. vm_refl. Qed.
Lemma D_8214c : decode_any W_8214c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82150 : bv 32 := 0xfee69ae3.
Lemma F_82150 : fetch_word AsanUbsan.M.loaded_segments (0x82198 : word) = Some W_82150.
Proof. vm_refl. Qed.
Lemma D_82150 : decode_any W_82150 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82154 : bv 32 := 0x0ff7f693.
Lemma F_82154 : fetch_word AsanUbsan.M.loaded_segments (0x8219c : word) = Some W_82154.
Proof. vm_refl. Qed.
Lemma D_82154 : decode_any W_82154 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82158 : bv 32 := 0xc60680e3.
Lemma F_82158 : fetch_word AsanUbsan.M.loaded_segments (0x821a0 : word) = Some W_82158.
Proof. vm_refl. Qed.
Lemma D_82158 : decode_any W_82158 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8215c : bv 32 := 0x00050493.
Lemma F_8215c : fetch_word AsanUbsan.M.loaded_segments (0x821a4 : word) = Some W_8215c.
Proof. vm_refl. Qed.
Lemma D_8215c : decode_any W_8215c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82160 : bv 32 := 0x00058b13.
Lemma F_82160 : fetch_word AsanUbsan.M.loaded_segments (0x821a8 : word) = Some W_82160.
Proof. vm_refl. Qed.
Lemma D_82160 : decode_any W_82160 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82164 : bv 32 := 0x00060593.
Lemma F_82164 : fetch_word AsanUbsan.M.loaded_segments (0x821ac : word) = Some W_82164.
Proof. vm_refl. Qed.
Lemma D_82164 : decode_any W_82164 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82168 : bv 32 := 0x00060913.
Lemma F_82168 : fetch_word AsanUbsan.M.loaded_segments (0x821b0 : word) = Some W_82168.
Proof. vm_refl. Qed.
Lemma D_82168 : decode_any W_82168 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8216c : bv 32 := 0x188020ef.
Lemma F_8216c : fetch_word AsanUbsan.M.loaded_segments (0x821b4 : word) = Some W_8216c.
Proof. vm_refl. Qed.
Lemma D_8216c : decode_any W_8216c = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82170 : bv 32 := 0x000b0593.
Lemma F_82170 : fetch_word AsanUbsan.M.loaded_segments (0x821b8 : word) = Some W_82170.
Proof. vm_refl. Qed.
Lemma D_82170 : decode_any W_82170 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82174 : bv 32 := 0x00090613.
Lemma F_82174 : fetch_word AsanUbsan.M.loaded_segments (0x821bc : word) = Some W_82174.
Proof. vm_refl. Qed.
Lemma D_82174 : decode_any W_82174 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82178 : bv 32 := 0x00050993.
Lemma F_82178 : fetch_word AsanUbsan.M.loaded_segments (0x821c0 : word) = Some W_82178.
Proof. vm_refl. Qed.
Lemma D_82178 : decode_any W_82178 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8217c : bv 32 := 0x00048513.
Lemma F_8217c : fetch_word AsanUbsan.M.loaded_segments (0x821c4 : word) = Some W_8217c.
Proof. vm_refl. Qed.
Lemma D_8217c : decode_any W_8217c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82180 : bv 32 := 0xc2098ce3.
Lemma F_82180 : fetch_word AsanUbsan.M.loaded_segments (0x821c8 : word) = Some W_82180.
Proof. vm_refl. Qed.
Lemma D_82180 : decode_any W_82180 = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82354 : bv 32 := 0xfe010113.
Lemma F_82354 : fetch_word AsanUbsan.M.loaded_segments (0x8239c : word) = Some W_82354.
Proof. vm_refl. Qed.
Lemma D_82354 : decode_any W_82354 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82358 : bv 32 := 0x00113c23.
Lemma F_82358 : fetch_word AsanUbsan.M.loaded_segments (0x823a0 : word) = Some W_82358.
Proof. vm_refl. Qed.
Lemma D_82358 : decode_any W_82358 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8235c : bv 32 := 0x00813823.
Lemma F_8235c : fetch_word AsanUbsan.M.loaded_segments (0x823a4 : word) = Some W_8235c.
Proof. vm_refl. Qed.
Lemma D_8235c : decode_any W_8235c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82360 : bv 32 := 0x00913423.
Lemma F_82360 : fetch_word AsanUbsan.M.loaded_segments (0x823a8 : word) = Some W_82360.
Proof. vm_refl. Qed.
Lemma D_82360 : decode_any W_82360 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82364 : bv 32 := 0x01213023.
Lemma F_82364 : fetch_word AsanUbsan.M.loaded_segments (0x823ac : word) = Some W_82364.
Proof. vm_refl. Qed.
Lemma D_82364 : decode_any W_82364 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82368 : bv 32 := 0x00058413.
Lemma F_82368 : fetch_word AsanUbsan.M.loaded_segments (0x823b0 : word) = Some W_82368.
Proof. vm_refl. Qed.
Lemma D_82368 : decode_any W_82368 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8236c : bv 32 := 0x00050493.
Lemma F_8236c : fetch_word AsanUbsan.M.loaded_segments (0x823b4 : word) = Some W_8236c.
Proof. vm_refl. Qed.
Lemma D_8236c : decode_any W_8236c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82370 : bv 32 := 0x030000ef.
Lemma F_82370 : fetch_word AsanUbsan.M.loaded_segments (0x823b8 : word) = Some W_82370.
Proof. vm_refl. Qed.
Lemma D_82370 : decode_any W_82370 = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82374 : bv 32 := 0x00050913.
Lemma F_82374 : fetch_word AsanUbsan.M.loaded_segments (0x823bc : word) = Some W_82374.
Proof. vm_refl. Qed.
Lemma D_82374 : decode_any W_82374 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82378 : bv 32 := 0x00940533.
Lemma F_82378 : fetch_word AsanUbsan.M.loaded_segments (0x823c0 : word) = Some W_82378.
Proof. vm_refl. Qed.
Lemma D_82378 : decode_any W_82378 = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8237c : bv 32 := 0x024000ef.
Lemma F_8237c : fetch_word AsanUbsan.M.loaded_segments (0x823c4 : word) = Some W_8237c.
Proof. vm_refl. Qed.
Lemma D_8237c : decode_any W_8237c = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82380 : bv 32 := 0x00050593.
Lemma F_82380 : fetch_word AsanUbsan.M.loaded_segments (0x823c8 : word) = Some W_82380.
Proof. vm_refl. Qed.
Lemma D_82380 : decode_any W_82380 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82384 : bv 32 := 0x00090513.
Lemma F_82384 : fetch_word AsanUbsan.M.loaded_segments (0x823cc : word) = Some W_82384.
Proof. vm_refl. Qed.
Lemma D_82384 : decode_any W_82384 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82388 : bv 32 := 0x01813083.
Lemma F_82388 : fetch_word AsanUbsan.M.loaded_segments (0x823d0 : word) = Some W_82388.
Proof. vm_refl. Qed.
Lemma D_82388 : decode_any W_82388 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8238c : bv 32 := 0x01013403.
Lemma F_8238c : fetch_word AsanUbsan.M.loaded_segments (0x823d4 : word) = Some W_8238c.
Proof. vm_refl. Qed.
Lemma D_8238c : decode_any W_8238c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82390 : bv 32 := 0x00813483.
Lemma F_82390 : fetch_word AsanUbsan.M.loaded_segments (0x823d8 : word) = Some W_82390.
Proof. vm_refl. Qed.
Lemma D_82390 : decode_any W_82390 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82394 : bv 32 := 0x00013903.
Lemma F_82394 : fetch_word AsanUbsan.M.loaded_segments (0x823dc : word) = Some W_82394.
Proof. vm_refl. Qed.
Lemma D_82394 : decode_any W_82394 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82398 : bv 32 := 0x02010113.
Lemma F_82398 : fetch_word AsanUbsan.M.loaded_segments (0x823e0 : word) = Some W_82398.
Proof. vm_refl. Qed.
Lemma D_82398 : decode_any W_82398 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8239c : bv 32 := 0x3151b06f.
Lemma F_8239c : fetch_word AsanUbsan.M.loaded_segments (0x823e4 : word) = Some W_8239c.
Proof. vm_refl. Qed.
Lemma D_8239c : decode_any W_8239c = Some (Jal 0 113428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823a0 : bv 32 := 0x000e2597.
Lemma F_823a0 : fetch_word AsanUbsan.M.loaded_segments (0x823e8 : word) = Some W_823a0.
Proof. vm_refl. Qed.
Lemma D_823a0 : decode_any W_823a0 = Some (Auipc 11 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823a4 : bv 32 := 0x1305b583.
Lemma F_823a4 : fetch_word AsanUbsan.M.loaded_segments (0x823ec : word) = Some W_823a4.
Proof. vm_refl. Qed.
Lemma D_823a4 : decode_any W_823a4 = Some (Load SZ8 true 11 11 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823a8 : bv 32 := 0x0005b583.
Lemma F_823a8 : fetch_word AsanUbsan.M.loaded_segments (0x823f0 : word) = Some W_823a8.
Proof. vm_refl. Qed.
Lemma D_823a8 : decode_any W_823a8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823ac : bv 32 := 0xfff58613.
Lemma F_823ac : fetch_word AsanUbsan.M.loaded_segments (0x823f4 : word) = Some W_823ac.
Proof. vm_refl. Qed.
Lemma D_823ac : decode_any W_823ac = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b0 : bv 32 := 0x00c5b6b3.
Lemma F_823b0 : fetch_word AsanUbsan.M.loaded_segments (0x823f8 : word) = Some W_823b0.
Proof. vm_refl. Qed.
Lemma D_823b0 : decode_any W_823b0 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b4 : bv 32 := 0xfff68693.
Lemma F_823b4 : fetch_word AsanUbsan.M.loaded_segments (0x823fc : word) = Some W_823b4.
Proof. vm_refl. Qed.
Lemma D_823b4 : decode_any W_823b4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b8 : bv 32 := 0x00c6f6b3.
Lemma F_823b8 : fetch_word AsanUbsan.M.loaded_segments (0x82400 : word) = Some W_823b8.
Proof. vm_refl. Qed.
Lemma D_823b8 : decode_any W_823b8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823bc : bv 32 := 0x04a6f263.
Lemma F_823bc : fetch_word AsanUbsan.M.loaded_segments (0x82404 : word) = Some W_823bc.
Proof. vm_refl. Qed.
Lemma D_823bc : decode_any W_823bc = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c0 : bv 32 := 0x000e2697.
Lemma F_823c0 : fetch_word AsanUbsan.M.loaded_segments (0x82408 : word) = Some W_823c0.
Proof. vm_refl. Qed.
Lemma D_823c0 : decode_any W_823c0 = Some (Auipc 13 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c4 : bv 32 := 0x1186b683.
Lemma F_823c4 : fetch_word AsanUbsan.M.loaded_segments (0x8240c : word) = Some W_823c4.
Proof. vm_refl. Qed.
Lemma D_823c4 : decode_any W_823c4 = Some (Load SZ8 true 13 13 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c8 : bv 32 := 0x000e2717.
Lemma F_823c8 : fetch_word AsanUbsan.M.loaded_segments (0x82410 : word) = Some W_823c8.
Proof. vm_refl. Qed.
Lemma D_823c8 : decode_any W_823c8 = Some (Auipc 14 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823cc : bv 32 := 0x11873703.
Lemma F_823cc : fetch_word AsanUbsan.M.loaded_segments (0x82414 : word) = Some W_823cc.
Proof. vm_refl. Qed.
Lemma D_823cc : decode_any W_823cc = Some (Load SZ8 true 14 14 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d0 : bv 32 := 0x0006b803.
Lemma F_823d0 : fetch_word AsanUbsan.M.loaded_segments (0x82418 : word) = Some W_823d0.
Proof. vm_refl. Qed.
Lemma D_823d0 : decode_any W_823d0 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d4 : bv 32 := 0x00073683.
Lemma F_823d4 : fetch_word AsanUbsan.M.loaded_segments (0x8241c : word) = Some W_823d4.
Proof. vm_refl. Qed.
Lemma D_823d4 : decode_any W_823d4 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d8 : bv 32 := 0xfff80793.
Lemma F_823d8 : fetch_word AsanUbsan.M.loaded_segments (0x82420 : word) = Some W_823d8.
Proof. vm_refl. Qed.
Lemma D_823d8 : decode_any W_823d8 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823dc : bv 32 := 0x00a7f463.
Lemma F_823dc : fetch_word AsanUbsan.M.loaded_segments (0x82424 : word) = Some W_823dc.
Proof. vm_refl. Qed.
Lemma D_823dc : decode_any W_823dc = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823e4 : bv 32 := 0x000e2717.
Lemma F_823e4 : fetch_word AsanUbsan.M.loaded_segments (0x8242c : word) = Some W_823e4.
Proof. vm_refl. Qed.
Lemma D_823e4 : decode_any W_823e4 = Some (Auipc 14 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823e8 : bv 32 := 0x10473703.
Lemma F_823e8 : fetch_word AsanUbsan.M.loaded_segments (0x82430 : word) = Some W_823e8.
Proof. vm_refl. Qed.
Lemma D_823e8 : decode_any W_823e8 = Some (Load SZ8 true 14 14 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823ec : bv 32 := 0x00073283.
Lemma F_823ec : fetch_word AsanUbsan.M.loaded_segments (0x82434 : word) = Some W_823ec.
Proof. vm_refl. Qed.
Lemma D_823ec : decode_any W_823ec = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f0 : bv 32 := 0x0032d713.
Lemma F_823f0 : fetch_word AsanUbsan.M.loaded_segments (0x82438 : word) = Some W_823f0.
Proof. vm_refl. Qed.
Lemma D_823f0 : decode_any W_823f0 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f4 : bv 32 := 0x00b708b3.
Lemma F_823f4 : fetch_word AsanUbsan.M.loaded_segments (0x8243c : word) = Some W_823f4.
Proof. vm_refl. Qed.
Lemma D_823f4 : decode_any W_823f4 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f8 : bv 32 := 0x00a2ea63.
Lemma F_823f8 : fetch_word AsanUbsan.M.loaded_segments (0x82440 : word) = Some W_823f8.
Proof. vm_refl. Qed.
Lemma D_823f8 : decode_any W_823f8 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823fc : bv 32 := 0x00a8f863.
Lemma F_823fc : fetch_word AsanUbsan.M.loaded_segments (0x82444 : word) = Some W_823fc.
Proof. vm_refl. Qed.
Lemma D_823fc : decode_any W_823fc = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82400 : bv 32 := 0x00355513.
Lemma F_82400 : fetch_word AsanUbsan.M.loaded_segments (0x82448 : word) = Some W_82400.
Proof. vm_refl. Qed.
Lemma D_82400 : decode_any W_82400 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82404 : bv 32 := 0x00a58533.
Lemma F_82404 : fetch_word AsanUbsan.M.loaded_segments (0x8244c : word) = Some W_82404.
Proof. vm_refl. Qed.
Lemma D_82404 : decode_any W_82404 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82408 : bv 32 := 0x00008067.
Lemma F_82408 : fetch_word AsanUbsan.M.loaded_segments (0x82450 : word) = Some W_82408.
Proof. vm_refl. Qed.
Lemma D_82408 : decode_any W_82408 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82648 : bv 32 := 0x0100006f.
Lemma F_82648 : fetch_word AsanUbsan.M.loaded_segments (0x82690 : word) = Some W_82648.
Proof. vm_refl. Qed.
Lemma D_82648 : decode_any W_82648 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8264c : bv 32 := 0x1dc0006f.
Lemma F_8264c : fetch_word AsanUbsan.M.loaded_segments (0x82694 : word) = Some W_8264c.
Proof. vm_refl. Qed.
Lemma D_8264c : decode_any W_8264c = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82654 : bv 32 := 0x7400006f.
Lemma F_82654 : fetch_word AsanUbsan.M.loaded_segments (0x8269c : word) = Some W_82654.
Proof. vm_refl. Qed.
Lemma D_82654 : decode_any W_82654 = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82658 : bv 32 := 0x81010113.
Lemma F_82658 : fetch_word AsanUbsan.M.loaded_segments (0x826a0 : word) = Some W_82658.
Proof. vm_refl. Qed.
Lemma D_82658 : decode_any W_82658 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8265c : bv 32 := 0x7e113423.
Lemma F_8265c : fetch_word AsanUbsan.M.loaded_segments (0x826a4 : word) = Some W_8265c.
Proof. vm_refl. Qed.
Lemma D_8265c : decode_any W_8265c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82660 : bv 32 := 0x7e813023.
Lemma F_82660 : fetch_word AsanUbsan.M.loaded_segments (0x826a8 : word) = Some W_82660.
Proof. vm_refl. Qed.
Lemma D_82660 : decode_any W_82660 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82664 : bv 32 := 0x7c913c23.
Lemma F_82664 : fetch_word AsanUbsan.M.loaded_segments (0x826ac : word) = Some W_82664.
Proof. vm_refl. Qed.
Lemma D_82664 : decode_any W_82664 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82668 : bv 32 := 0x7d213823.
Lemma F_82668 : fetch_word AsanUbsan.M.loaded_segments (0x826b0 : word) = Some W_82668.
Proof. vm_refl. Qed.
Lemma D_82668 : decode_any W_82668 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8266c : bv 32 := 0x7d313423.
Lemma F_8266c : fetch_word AsanUbsan.M.loaded_segments (0x826b4 : word) = Some W_8266c.
Proof. vm_refl. Qed.
Lemma D_8266c : decode_any W_8266c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82670 : bv 32 := 0x7d413023.
Lemma F_82670 : fetch_word AsanUbsan.M.loaded_segments (0x826b8 : word) = Some W_82670.
Proof. vm_refl. Qed.
Lemma D_82670 : decode_any W_82670 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82674 : bv 32 := 0x7b513c23.
Lemma F_82674 : fetch_word AsanUbsan.M.loaded_segments (0x826bc : word) = Some W_82674.
Proof. vm_refl. Qed.
Lemma D_82674 : decode_any W_82674 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82678 : bv 32 := 0x7f010413.
Lemma F_82678 : fetch_word AsanUbsan.M.loaded_segments (0x826c0 : word) = Some W_82678.
Proof. vm_refl. Qed.
Lemma D_82678 : decode_any W_82678 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8267c : bv 32 := 0xfa010113.
Lemma F_8267c : fetch_word AsanUbsan.M.loaded_segments (0x826c4 : word) = Some W_8267c.
Proof. vm_refl. Qed.
Lemma D_8267c : decode_any W_8267c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82680 : bv 32 := 0x00008913.
Lemma F_82680 : fetch_word AsanUbsan.M.loaded_segments (0x826c8 : word) = Some W_82680.
Proof. vm_refl. Qed.
Lemma D_82680 : decode_any W_82680 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82684 : bv 32 := 0x00050493.
Lemma F_82684 : fetch_word AsanUbsan.M.loaded_segments (0x826cc : word) = Some W_82684.
Proof. vm_refl. Qed.
Lemma D_82684 : decode_any W_82684 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82688 : bv 32 := 0x10c0c0ef.
Lemma F_82688 : fetch_word AsanUbsan.M.loaded_segments (0x826d0 : word) = Some W_82688.
Proof. vm_refl. Qed.
Lemma D_82688 : decode_any W_82688 = Some (Jal 1 49420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8268c : bv 32 := 0x02f4d593.
Lemma F_8268c : fetch_word AsanUbsan.M.loaded_segments (0x826d4 : word) = Some W_8268c.
Proof. vm_refl. Qed.
Lemma D_8268c : decode_any W_8268c = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82690 : bv 32 := 0x0a059063.
Lemma F_82690 : fetch_word AsanUbsan.M.loaded_segments (0x826d8 : word) = Some W_82690.
Proof. vm_refl. Qed.
Lemma D_82690 : decode_any W_82690 = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82694 : bv 32 := 0x0204d593.
Lemma F_82694 : fetch_word AsanUbsan.M.loaded_segments (0x826dc : word) = Some W_82694.
Proof. vm_refl. Qed.
Lemma D_82694 : decode_any W_82694 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82698 : bv 32 := 0x00359613.
Lemma F_82698 : fetch_word AsanUbsan.M.loaded_segments (0x826e0 : word) = Some W_82698.
Proof. vm_refl. Qed.
Lemma D_82698 : decode_any W_82698 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8269c : bv 32 := 0x00c50633.
Lemma F_8269c : fetch_word AsanUbsan.M.loaded_segments (0x826e4 : word) = Some W_8269c.
Proof. vm_refl. Qed.
Lemma D_8269c : decode_any W_8269c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a0 : bv 32 := 0x00863683.
Lemma F_826a0 : fetch_word AsanUbsan.M.loaded_segments (0x826e8 : word) = Some W_826a0.
Proof. vm_refl. Qed.
Lemma D_826a0 : decode_any W_826a0 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a4 : bv 32 := 0x0230000f.
Lemma F_826a4 : fetch_word AsanUbsan.M.loaded_segments (0x826ec : word) = Some W_826a4.
Proof. vm_refl. Qed.
Lemma D_826a4 : decode_any W_826a4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a8 : bv 32 := 0x08068463.
Lemma F_826a8 : fetch_word AsanUbsan.M.loaded_segments (0x826f0 : word) = Some W_826a8.
Proof. vm_refl. Qed.
Lemma D_826a8 : decode_any W_826a8 = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82730 : bv 32 := 0x80040a13.
Lemma F_82730 : fetch_word AsanUbsan.M.loaded_segments (0x82778 : word) = Some W_82730.
Proof. vm_refl. Qed.
Lemma D_82730 : decode_any W_82730 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82734 : bv 32 := 0xfb0a0a13.
Lemma F_82734 : fetch_word AsanUbsan.M.loaded_segments (0x8277c : word) = Some W_82734.
Proof. vm_refl. Qed.
Lemma D_82734 : decode_any W_82734 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82738 : bv 32 := 0x80040513.
Lemma F_82738 : fetch_word AsanUbsan.M.loaded_segments (0x82780 : word) = Some W_82738.
Proof. vm_refl. Qed.
Lemma D_82738 : decode_any W_82738 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8273c : bv 32 := 0xfc050513.
Lemma F_8273c : fetch_word AsanUbsan.M.loaded_segments (0x82784 : word) = Some W_8273c.
Proof. vm_refl. Qed.
Lemma D_8273c : decode_any W_8273c = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82740 : bv 32 := 0x7ffa0a93.
Lemma F_82740 : fetch_word AsanUbsan.M.loaded_segments (0x82788 : word) = Some W_82740.
Proof. vm_refl. Qed.
Lemma D_82740 : decode_any W_82740 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82744 : bv 32 := 0x000ab4a3.
Lemma F_82744 : fetch_word AsanUbsan.M.loaded_segments (0x8278c : word) = Some W_82744.
Proof. vm_refl. Qed.
Lemma D_82744 : decode_any W_82744 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82748 : bv 32 := 0x00aa3023.
Lemma F_82748 : fetch_word AsanUbsan.M.loaded_segments (0x82790 : word) = Some W_82748.
Proof. vm_refl. Qed.
Lemma D_82748 : decode_any W_82748 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8274c : bv 32 := 0x000a3423.
Lemma F_8274c : fetch_word AsanUbsan.M.loaded_segments (0x82794 : word) = Some W_8274c.
Proof. vm_refl. Qed.
Lemma D_8274c : decode_any W_8274c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82750 : bv 32 := 0x550080ef.
Lemma F_82750 : fetch_word AsanUbsan.M.loaded_segments (0x82798 : word) = Some W_82750.
Proof. vm_refl. Qed.
Lemma D_82750 : decode_any W_82750 = Some (Jal 1 34128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82754 : bv 32 := 0x00200593.
Lemma F_82754 : fetch_word AsanUbsan.M.loaded_segments (0x8279c : word) = Some W_82754.
Proof. vm_refl. Qed.
Lemma D_82754 : decode_any W_82754 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82758 : bv 32 := 0x02a5ea63.
Lemma F_82758 : fetch_word AsanUbsan.M.loaded_segments (0x827a0 : word) = Some W_82758.
Proof. vm_refl. Qed.
Lemma D_82758 : decode_any W_82758 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8278c : bv 32 := 0x7f1200ef.
Lemma F_8278c : fetch_word AsanUbsan.M.loaded_segments (0x827d4 : word) = Some W_8278c.
Proof. vm_refl. Qed.
Lemma D_8278c : decode_any W_8278c = Some (Jal 1 135152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82790 : bv 32 := 0x000e2597.
Lemma F_82790 : fetch_word AsanUbsan.M.loaded_segments (0x827d8 : word) = Some W_82790.
Proof. vm_refl. Qed.
Lemma D_82790 : decode_any W_82790 = Some (Auipc 11 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82794 : bv 32 := 0xd305b583.
Lemma F_82794 : fetch_word AsanUbsan.M.loaded_segments (0x827dc : word) = Some W_82794.
Proof. vm_refl. Qed.
Lemma D_82794 : decode_any W_82794 = Some (Load SZ8 true 11 11 3376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82798 : bv 32 := 0x0225c983.
Lemma F_82798 : fetch_word AsanUbsan.M.loaded_segments (0x827e0 : word) = Some W_82798.
Proof. vm_refl. Qed.
Lemma D_82798 : decode_any W_82798 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8279c : bv 32 := 0x00050913.
Lemma F_8279c : fetch_word AsanUbsan.M.loaded_segments (0x827e4 : word) = Some W_8279c.
Proof. vm_refl. Qed.
Lemma D_8279c : decode_any W_8279c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827a0 : bv 32 := 0x500080ef.
Lemma F_827a0 : fetch_word AsanUbsan.M.loaded_segments (0x827e8 : word) = Some W_827a0.
Proof. vm_refl. Qed.
Lemma D_827a0 : decode_any W_827a0 = Some (Jal 1 34048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827a4 : bv 32 := 0x00050793.
Lemma F_827a4 : fetch_word AsanUbsan.M.loaded_segments (0x827ec : word) = Some W_827a4.
Proof. vm_refl. Qed.
Lemma D_827a4 : decode_any W_827a4 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827a8 : bv 32 := 0x00153513.
Lemma F_827a8 : fetch_word AsanUbsan.M.loaded_segments (0x827f0 : word) = Some W_827a8.
Proof. vm_refl. Qed.
Lemma D_827a8 : decode_any W_827a8 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827ac : bv 32 := 0xfff50513.
Lemma F_827ac : fetch_word AsanUbsan.M.loaded_segments (0x827f4 : word) = Some W_827ac.
Proof. vm_refl. Qed.
Lemma D_827ac : decode_any W_827ac = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827b0 : bv 32 := 0x008575b3.
Lemma F_827b0 : fetch_word AsanUbsan.M.loaded_segments (0x827f8 : word) = Some W_827b0.
Proof. vm_refl. Qed.
Lemma D_827b0 : decode_any W_827b0 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827b4 : bv 32 := 0x00100513.
Lemma F_827b4 : fetch_word AsanUbsan.M.loaded_segments (0x827fc : word) = Some W_827b4.
Proof. vm_refl. Qed.
Lemma D_827b4 : decode_any W_827b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827b8 : bv 32 := 0x00bab4a3.
Lemma F_827b8 : fetch_word AsanUbsan.M.loaded_segments (0x82800 : word) = Some W_827b8.
Proof. vm_refl. Qed.
Lemma D_827b8 : decode_any W_827b8 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827bc : bv 32 := 0x00f56a63.
Lemma F_827bc : fetch_word AsanUbsan.M.loaded_segments (0x82804 : word) = Some W_827bc.
Proof. vm_refl. Qed.
Lemma D_827bc : decode_any W_827bc = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827d0 : bv 32 := 0x80040513.
Lemma F_827d0 : fetch_word AsanUbsan.M.loaded_segments (0x82818 : word) = Some W_827d0.
Proof. vm_refl. Qed.
Lemma D_827d0 : decode_any W_827d0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827d4 : bv 32 := 0xfb050513.
Lemma F_827d4 : fetch_word AsanUbsan.M.loaded_segments (0x8281c : word) = Some W_827d4.
Proof. vm_refl. Qed.
Lemma D_827d4 : decode_any W_827d4 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827d8 : bv 32 := 0x00090593.
Lemma F_827d8 : fetch_word AsanUbsan.M.loaded_segments (0x82820 : word) = Some W_827d8.
Proof. vm_refl. Qed.
Lemma D_827d8 : decode_any W_827d8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827dc : bv 32 := 0x00040613.
Lemma F_827dc : fetch_word AsanUbsan.M.loaded_segments (0x82824 : word) = Some W_827dc.
Proof. vm_refl. Qed.
Lemma D_827dc : decode_any W_827dc = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827e0 : bv 32 := 0x00000693.
Lemma F_827e0 : fetch_word AsanUbsan.M.loaded_segments (0x82828 : word) = Some W_827e0.
Proof. vm_refl. Qed.
Lemma D_827e0 : decode_any W_827e0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827e4 : bv 32 := 0x00098713.
Lemma F_827e4 : fetch_word AsanUbsan.M.loaded_segments (0x8282c : word) = Some W_827e4.
Proof. vm_refl. Qed.
Lemma D_827e4 : decode_any W_827e4 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827e8 : bv 32 := 0x4c8080ef.
Lemma F_827e8 : fetch_word AsanUbsan.M.loaded_segments (0x82830 : word) = Some W_827e8.
Proof. vm_refl. Qed.
Lemma D_827e8 : decode_any W_827e8 = Some (Jal 1 33992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827ec : bv 32 := 0x80040593.
Lemma F_827ec : fetch_word AsanUbsan.M.loaded_segments (0x82834 : word) = Some W_827ec.
Proof. vm_refl. Qed.
Lemma D_827ec : decode_any W_827ec = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827f0 : bv 32 := 0xfb058593.
Lemma F_827f0 : fetch_word AsanUbsan.M.loaded_segments (0x82838 : word) = Some W_827f0.
Proof. vm_refl. Qed.
Lemma D_827f0 : decode_any W_827f0 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827f4 : bv 32 := 0x00100613.
Lemma F_827f4 : fetch_word AsanUbsan.M.loaded_segments (0x8283c : word) = Some W_827f4.
Proof. vm_refl. Qed.
Lemma D_827f4 : decode_any W_827f4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827f8 : bv 32 := 0x00048513.
Lemma F_827f8 : fetch_word AsanUbsan.M.loaded_segments (0x82840 : word) = Some W_827f8.
Proof. vm_refl. Qed.
Lemma D_827f8 : decode_any W_827f8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_827fc : bv 32 := 0xd78d80ef.
Lemma F_827fc : fetch_word AsanUbsan.M.loaded_segments (0x82844 : word) = Some W_827fc.
Proof. vm_refl. Qed.
Lemma D_827fc : decode_any W_827fc = Some (Jal 1 1934712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82800 : bv 32 := 0x06010113.
Lemma F_82800 : fetch_word AsanUbsan.M.loaded_segments (0x82848 : word) = Some W_82800.
Proof. vm_refl. Qed.
Lemma D_82800 : decode_any W_82800 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82804 : bv 32 := 0x7e813083.
Lemma F_82804 : fetch_word AsanUbsan.M.loaded_segments (0x8284c : word) = Some W_82804.
Proof. vm_refl. Qed.
Lemma D_82804 : decode_any W_82804 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82808 : bv 32 := 0x7e013403.
Lemma F_82808 : fetch_word AsanUbsan.M.loaded_segments (0x82850 : word) = Some W_82808.
Proof. vm_refl. Qed.
Lemma D_82808 : decode_any W_82808 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8280c : bv 32 := 0x7d813483.
Lemma F_8280c : fetch_word AsanUbsan.M.loaded_segments (0x82854 : word) = Some W_8280c.
Proof. vm_refl. Qed.
Lemma D_8280c : decode_any W_8280c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82810 : bv 32 := 0x7d013903.
Lemma F_82810 : fetch_word AsanUbsan.M.loaded_segments (0x82858 : word) = Some W_82810.
Proof. vm_refl. Qed.
Lemma D_82810 : decode_any W_82810 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82814 : bv 32 := 0x7c813983.
Lemma F_82814 : fetch_word AsanUbsan.M.loaded_segments (0x8285c : word) = Some W_82814.
Proof. vm_refl. Qed.
Lemma D_82814 : decode_any W_82814 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82818 : bv 32 := 0x7c013a03.
Lemma F_82818 : fetch_word AsanUbsan.M.loaded_segments (0x82860 : word) = Some W_82818.
Proof. vm_refl. Qed.
Lemma D_82818 : decode_any W_82818 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8281c : bv 32 := 0x7b813a83.
Lemma F_8281c : fetch_word AsanUbsan.M.loaded_segments (0x82864 : word) = Some W_8281c.
Proof. vm_refl. Qed.
Lemma D_8281c : decode_any W_8281c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82820 : bv 32 := 0x7f010113.
Lemma F_82820 : fetch_word AsanUbsan.M.loaded_segments (0x82868 : word) = Some W_82820.
Proof. vm_refl. Qed.
Lemma D_82820 : decode_any W_82820 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82824 : bv 32 := 0x00008067.
Lemma F_82824 : fetch_word AsanUbsan.M.loaded_segments (0x8286c : word) = Some W_82824.
Proof. vm_refl. Qed.
Lemma D_82824 : decode_any W_82824 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82828 : bv 32 := 0x81010113.
Lemma F_82828 : fetch_word AsanUbsan.M.loaded_segments (0x82870 : word) = Some W_82828.
Proof. vm_refl. Qed.
Lemma D_82828 : decode_any W_82828 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8282c : bv 32 := 0x7e113423.
Lemma F_8282c : fetch_word AsanUbsan.M.loaded_segments (0x82874 : word) = Some W_8282c.
Proof. vm_refl. Qed.
Lemma D_8282c : decode_any W_8282c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82830 : bv 32 := 0x7e813023.
Lemma F_82830 : fetch_word AsanUbsan.M.loaded_segments (0x82878 : word) = Some W_82830.
Proof. vm_refl. Qed.
Lemma D_82830 : decode_any W_82830 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82834 : bv 32 := 0x7c913c23.
Lemma F_82834 : fetch_word AsanUbsan.M.loaded_segments (0x8287c : word) = Some W_82834.
Proof. vm_refl. Qed.
Lemma D_82834 : decode_any W_82834 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82838 : bv 32 := 0x7d213823.
Lemma F_82838 : fetch_word AsanUbsan.M.loaded_segments (0x82880 : word) = Some W_82838.
Proof. vm_refl. Qed.
Lemma D_82838 : decode_any W_82838 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8283c : bv 32 := 0x7d313423.
Lemma F_8283c : fetch_word AsanUbsan.M.loaded_segments (0x82884 : word) = Some W_8283c.
Proof. vm_refl. Qed.
Lemma D_8283c : decode_any W_8283c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82840 : bv 32 := 0x7d413023.
Lemma F_82840 : fetch_word AsanUbsan.M.loaded_segments (0x82888 : word) = Some W_82840.
Proof. vm_refl. Qed.
Lemma D_82840 : decode_any W_82840 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82844 : bv 32 := 0x7b513c23.
Lemma F_82844 : fetch_word AsanUbsan.M.loaded_segments (0x8288c : word) = Some W_82844.
Proof. vm_refl. Qed.
Lemma D_82844 : decode_any W_82844 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82848 : bv 32 := 0x7f010413.
Lemma F_82848 : fetch_word AsanUbsan.M.loaded_segments (0x82890 : word) = Some W_82848.
Proof. vm_refl. Qed.
Lemma D_82848 : decode_any W_82848 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8284c : bv 32 := 0xfa010113.
Lemma F_8284c : fetch_word AsanUbsan.M.loaded_segments (0x82894 : word) = Some W_8284c.
Proof. vm_refl. Qed.
Lemma D_8284c : decode_any W_8284c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82850 : bv 32 := 0x00008913.
Lemma F_82850 : fetch_word AsanUbsan.M.loaded_segments (0x82898 : word) = Some W_82850.
Proof. vm_refl. Qed.
Lemma D_82850 : decode_any W_82850 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82854 : bv 32 := 0x00050493.
Lemma F_82854 : fetch_word AsanUbsan.M.loaded_segments (0x8289c : word) = Some W_82854.
Proof. vm_refl. Qed.
Lemma D_82854 : decode_any W_82854 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82858 : bv 32 := 0x6c0070ef.
Lemma F_82858 : fetch_word AsanUbsan.M.loaded_segments (0x828a0 : word) = Some W_82858.
Proof. vm_refl. Qed.
Lemma D_82858 : decode_any W_82858 = Some (Jal 1 30400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8285c : bv 32 := 0x06050063.
Lemma F_8285c : fetch_word AsanUbsan.M.loaded_segments (0x828a4 : word) = Some W_8285c.
Proof. vm_refl. Qed.
Lemma D_8285c : decode_any W_8285c = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82860 : bv 32 := 0x80040a13.
Lemma F_82860 : fetch_word AsanUbsan.M.loaded_segments (0x828a8 : word) = Some W_82860.
Proof. vm_refl. Qed.
Lemma D_82860 : decode_any W_82860 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82864 : bv 32 := 0xfb0a0a13.
Lemma F_82864 : fetch_word AsanUbsan.M.loaded_segments (0x828ac : word) = Some W_82864.
Proof. vm_refl. Qed.
Lemma D_82864 : decode_any W_82864 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82868 : bv 32 := 0x80040513.
Lemma F_82868 : fetch_word AsanUbsan.M.loaded_segments (0x828b0 : word) = Some W_82868.
Proof. vm_refl. Qed.
Lemma D_82868 : decode_any W_82868 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8286c : bv 32 := 0xfc050513.
Lemma F_8286c : fetch_word AsanUbsan.M.loaded_segments (0x828b4 : word) = Some W_8286c.
Proof. vm_refl. Qed.
Lemma D_8286c : decode_any W_8286c = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82870 : bv 32 := 0x7ffa0a93.
Lemma F_82870 : fetch_word AsanUbsan.M.loaded_segments (0x828b8 : word) = Some W_82870.
Proof. vm_refl. Qed.
Lemma D_82870 : decode_any W_82870 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82874 : bv 32 := 0x000ab4a3.
Lemma F_82874 : fetch_word AsanUbsan.M.loaded_segments (0x828bc : word) = Some W_82874.
Proof. vm_refl. Qed.
Lemma D_82874 : decode_any W_82874 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82878 : bv 32 := 0x00aa3023.
Lemma F_82878 : fetch_word AsanUbsan.M.loaded_segments (0x828c0 : word) = Some W_82878.
Proof. vm_refl. Qed.
Lemma D_82878 : decode_any W_82878 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8287c : bv 32 := 0x000a3423.
Lemma F_8287c : fetch_word AsanUbsan.M.loaded_segments (0x828c4 : word) = Some W_8287c.
Proof. vm_refl. Qed.
Lemma D_8287c : decode_any W_8287c = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82880 : bv 32 := 0x420080ef.
Lemma F_82880 : fetch_word AsanUbsan.M.loaded_segments (0x828c8 : word) = Some W_82880.
Proof. vm_refl. Qed.
Lemma D_82880 : decode_any W_82880 = Some (Jal 1 33824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82884 : bv 32 := 0x00200593.
Lemma F_82884 : fetch_word AsanUbsan.M.loaded_segments (0x828cc : word) = Some W_82884.
Proof. vm_refl. Qed.
Lemma D_82884 : decode_any W_82884 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82888 : bv 32 := 0x06a5e263.
Lemma F_82888 : fetch_word AsanUbsan.M.loaded_segments (0x828d0 : word) = Some W_82888.
Proof. vm_refl. Qed.
Lemma D_82888 : decode_any W_82888 = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828ec : bv 32 := 0x691200ef.
Lemma F_828ec : fetch_word AsanUbsan.M.loaded_segments (0x82934 : word) = Some W_828ec.
Proof. vm_refl. Qed.
Lemma D_828ec : decode_any W_828ec = Some (Jal 1 134800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f0 : bv 32 := 0x000e2597.
Lemma F_828f0 : fetch_word AsanUbsan.M.loaded_segments (0x82938 : word) = Some W_828f0.
Proof. vm_refl. Qed.
Lemma D_828f0 : decode_any W_828f0 = Some (Auipc 11 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f4 : bv 32 := 0xbd05b583.
Lemma F_828f4 : fetch_word AsanUbsan.M.loaded_segments (0x8293c : word) = Some W_828f4.
Proof. vm_refl. Qed.
Lemma D_828f4 : decode_any W_828f4 = Some (Load SZ8 true 11 11 3024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828f8 : bv 32 := 0x0225c983.
Lemma F_828f8 : fetch_word AsanUbsan.M.loaded_segments (0x82940 : word) = Some W_828f8.
Proof. vm_refl. Qed.
Lemma D_828f8 : decode_any W_828f8 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_828fc : bv 32 := 0x00050913.
Lemma F_828fc : fetch_word AsanUbsan.M.loaded_segments (0x82944 : word) = Some W_828fc.
Proof. vm_refl. Qed.
Lemma D_828fc : decode_any W_828fc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82900 : bv 32 := 0x3a0080ef.
Lemma F_82900 : fetch_word AsanUbsan.M.loaded_segments (0x82948 : word) = Some W_82900.
Proof. vm_refl. Qed.
Lemma D_82900 : decode_any W_82900 = Some (Jal 1 33696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82904 : bv 32 := 0x00050793.
Lemma F_82904 : fetch_word AsanUbsan.M.loaded_segments (0x8294c : word) = Some W_82904.
Proof. vm_refl. Qed.
Lemma D_82904 : decode_any W_82904 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82908 : bv 32 := 0x00153513.
Lemma F_82908 : fetch_word AsanUbsan.M.loaded_segments (0x82950 : word) = Some W_82908.
Proof. vm_refl. Qed.
Lemma D_82908 : decode_any W_82908 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8290c : bv 32 := 0xfff50513.
Lemma F_8290c : fetch_word AsanUbsan.M.loaded_segments (0x82954 : word) = Some W_8290c.
Proof. vm_refl. Qed.
Lemma D_8290c : decode_any W_8290c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82910 : bv 32 := 0x008575b3.
Lemma F_82910 : fetch_word AsanUbsan.M.loaded_segments (0x82958 : word) = Some W_82910.
Proof. vm_refl. Qed.
Lemma D_82910 : decode_any W_82910 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82914 : bv 32 := 0x00100513.
Lemma F_82914 : fetch_word AsanUbsan.M.loaded_segments (0x8295c : word) = Some W_82914.
Proof. vm_refl. Qed.
Lemma D_82914 : decode_any W_82914 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82918 : bv 32 := 0x00bab4a3.
Lemma F_82918 : fetch_word AsanUbsan.M.loaded_segments (0x82960 : word) = Some W_82918.
Proof. vm_refl. Qed.
Lemma D_82918 : decode_any W_82918 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8291c : bv 32 := 0x00f56a63.
Lemma F_8291c : fetch_word AsanUbsan.M.loaded_segments (0x82964 : word) = Some W_8291c.
Proof. vm_refl. Qed.
Lemma D_8291c : decode_any W_8291c = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82930 : bv 32 := 0x80040513.
Lemma F_82930 : fetch_word AsanUbsan.M.loaded_segments (0x82978 : word) = Some W_82930.
Proof. vm_refl. Qed.
Lemma D_82930 : decode_any W_82930 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82934 : bv 32 := 0xfb050513.
Lemma F_82934 : fetch_word AsanUbsan.M.loaded_segments (0x8297c : word) = Some W_82934.
Proof. vm_refl. Qed.
Lemma D_82934 : decode_any W_82934 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82938 : bv 32 := 0x00090593.
Lemma F_82938 : fetch_word AsanUbsan.M.loaded_segments (0x82980 : word) = Some W_82938.
Proof. vm_refl. Qed.
Lemma D_82938 : decode_any W_82938 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8293c : bv 32 := 0x00040613.
Lemma F_8293c : fetch_word AsanUbsan.M.loaded_segments (0x82984 : word) = Some W_8293c.
Proof. vm_refl. Qed.
Lemma D_8293c : decode_any W_8293c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82940 : bv 32 := 0x00000693.
Lemma F_82940 : fetch_word AsanUbsan.M.loaded_segments (0x82988 : word) = Some W_82940.
Proof. vm_refl. Qed.
Lemma D_82940 : decode_any W_82940 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82944 : bv 32 := 0x00098713.
Lemma F_82944 : fetch_word AsanUbsan.M.loaded_segments (0x8298c : word) = Some W_82944.
Proof. vm_refl. Qed.
Lemma D_82944 : decode_any W_82944 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82948 : bv 32 := 0x368080ef.
Lemma F_82948 : fetch_word AsanUbsan.M.loaded_segments (0x82990 : word) = Some W_82948.
Proof. vm_refl. Qed.
Lemma D_82948 : decode_any W_82948 = Some (Jal 1 33640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8294c : bv 32 := 0x80040593.
Lemma F_8294c : fetch_word AsanUbsan.M.loaded_segments (0x82994 : word) = Some W_8294c.
Proof. vm_refl. Qed.
Lemma D_8294c : decode_any W_8294c = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82950 : bv 32 := 0xfb058593.
Lemma F_82950 : fetch_word AsanUbsan.M.loaded_segments (0x82998 : word) = Some W_82950.
Proof. vm_refl. Qed.
Lemma D_82950 : decode_any W_82950 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82954 : bv 32 := 0x00048513.
Lemma F_82954 : fetch_word AsanUbsan.M.loaded_segments (0x8299c : word) = Some W_82954.
Proof. vm_refl. Qed.
Lemma D_82954 : decode_any W_82954 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82958 : bv 32 := 0xefcd80ef.
Lemma F_82958 : fetch_word AsanUbsan.M.loaded_segments (0x829a0 : word) = Some W_82958.
Proof. vm_refl. Qed.
Lemma D_82958 : decode_any W_82958 = Some (Jal 1 1935100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8295c : bv 32 := 0x06010113.
Lemma F_8295c : fetch_word AsanUbsan.M.loaded_segments (0x829a4 : word) = Some W_8295c.
Proof. vm_refl. Qed.
Lemma D_8295c : decode_any W_8295c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82960 : bv 32 := 0x7e813083.
Lemma F_82960 : fetch_word AsanUbsan.M.loaded_segments (0x829a8 : word) = Some W_82960.
Proof. vm_refl. Qed.
Lemma D_82960 : decode_any W_82960 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82964 : bv 32 := 0x7e013403.
Lemma F_82964 : fetch_word AsanUbsan.M.loaded_segments (0x829ac : word) = Some W_82964.
Proof. vm_refl. Qed.
Lemma D_82964 : decode_any W_82964 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82968 : bv 32 := 0x7d813483.
Lemma F_82968 : fetch_word AsanUbsan.M.loaded_segments (0x829b0 : word) = Some W_82968.
Proof. vm_refl. Qed.
Lemma D_82968 : decode_any W_82968 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8296c : bv 32 := 0x7d013903.
Lemma F_8296c : fetch_word AsanUbsan.M.loaded_segments (0x829b4 : word) = Some W_8296c.
Proof. vm_refl. Qed.
Lemma D_8296c : decode_any W_8296c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82970 : bv 32 := 0x7c813983.
Lemma F_82970 : fetch_word AsanUbsan.M.loaded_segments (0x829b8 : word) = Some W_82970.
Proof. vm_refl. Qed.
Lemma D_82970 : decode_any W_82970 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82974 : bv 32 := 0x7c013a03.
Lemma F_82974 : fetch_word AsanUbsan.M.loaded_segments (0x829bc : word) = Some W_82974.
Proof. vm_refl. Qed.
Lemma D_82974 : decode_any W_82974 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82978 : bv 32 := 0x7b813a83.
Lemma F_82978 : fetch_word AsanUbsan.M.loaded_segments (0x829c0 : word) = Some W_82978.
Proof. vm_refl. Qed.
Lemma D_82978 : decode_any W_82978 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8297c : bv 32 := 0x7f010113.
Lemma F_8297c : fetch_word AsanUbsan.M.loaded_segments (0x829c4 : word) = Some W_8297c.
Proof. vm_refl. Qed.
Lemma D_8297c : decode_any W_8297c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82980 : bv 32 := 0x00008067.
Lemma F_82980 : fetch_word AsanUbsan.M.loaded_segments (0x829c8 : word) = Some W_82980.
Proof. vm_refl. Qed.
Lemma D_82980 : decode_any W_82980 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d94 : bv 32 := 0x81010113.
Lemma F_82d94 : fetch_word AsanUbsan.M.loaded_segments (0x82ddc : word) = Some W_82d94.
Proof. vm_refl. Qed.
Lemma D_82d94 : decode_any W_82d94 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d98 : bv 32 := 0x7e113423.
Lemma F_82d98 : fetch_word AsanUbsan.M.loaded_segments (0x82de0 : word) = Some W_82d98.
Proof. vm_refl. Qed.
Lemma D_82d98 : decode_any W_82d98 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82d9c : bv 32 := 0x7e813023.
Lemma F_82d9c : fetch_word AsanUbsan.M.loaded_segments (0x82de4 : word) = Some W_82d9c.
Proof. vm_refl. Qed.
Lemma D_82d9c : decode_any W_82d9c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82da0 : bv 32 := 0x7c913c23.
Lemma F_82da0 : fetch_word AsanUbsan.M.loaded_segments (0x82de8 : word) = Some W_82da0.
Proof. vm_refl. Qed.
Lemma D_82da0 : decode_any W_82da0 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82da4 : bv 32 := 0x7d213823.
Lemma F_82da4 : fetch_word AsanUbsan.M.loaded_segments (0x82dec : word) = Some W_82da4.
Proof. vm_refl. Qed.
Lemma D_82da4 : decode_any W_82da4 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82da8 : bv 32 := 0x7d313423.
Lemma F_82da8 : fetch_word AsanUbsan.M.loaded_segments (0x82df0 : word) = Some W_82da8.
Proof. vm_refl. Qed.
Lemma D_82da8 : decode_any W_82da8 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dac : bv 32 := 0x7d413023.
Lemma F_82dac : fetch_word AsanUbsan.M.loaded_segments (0x82df4 : word) = Some W_82dac.
Proof. vm_refl. Qed.
Lemma D_82dac : decode_any W_82dac = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82db0 : bv 32 := 0x7b513c23.
Lemma F_82db0 : fetch_word AsanUbsan.M.loaded_segments (0x82df8 : word) = Some W_82db0.
Proof. vm_refl. Qed.
Lemma D_82db0 : decode_any W_82db0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82db4 : bv 32 := 0x7b613823.
Lemma F_82db4 : fetch_word AsanUbsan.M.loaded_segments (0x82dfc : word) = Some W_82db4.
Proof. vm_refl. Qed.
Lemma D_82db4 : decode_any W_82db4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82db8 : bv 32 := 0x7f010413.
Lemma F_82db8 : fetch_word AsanUbsan.M.loaded_segments (0x82e00 : word) = Some W_82db8.
Proof. vm_refl. Qed.
Lemma D_82db8 : decode_any W_82db8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dbc : bv 32 := 0xf9010113.
Lemma F_82dbc : fetch_word AsanUbsan.M.loaded_segments (0x82e04 : word) = Some W_82dbc.
Proof. vm_refl. Qed.
Lemma D_82dbc : decode_any W_82dbc = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc0 : bv 32 := 0x00008993.
Lemma F_82dc0 : fetch_word AsanUbsan.M.loaded_segments (0x82e08 : word) = Some W_82dc0.
Proof. vm_refl. Qed.
Lemma D_82dc0 : decode_any W_82dc0 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc4 : bv 32 := 0x00058493.
Lemma F_82dc4 : fetch_word AsanUbsan.M.loaded_segments (0x82e0c : word) = Some W_82dc4.
Proof. vm_refl. Qed.
Lemma D_82dc4 : decode_any W_82dc4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dc8 : bv 32 := 0x00050913.
Lemma F_82dc8 : fetch_word AsanUbsan.M.loaded_segments (0x82e10 : word) = Some W_82dc8.
Proof. vm_refl. Qed.
Lemma D_82dc8 : decode_any W_82dc8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dcc : bv 32 := 0x80040a93.
Lemma F_82dcc : fetch_word AsanUbsan.M.loaded_segments (0x82e14 : word) = Some W_82dcc.
Proof. vm_refl. Qed.
Lemma D_82dcc : decode_any W_82dcc = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd0 : bv 32 := 0xfa8a8a93.
Lemma F_82dd0 : fetch_word AsanUbsan.M.loaded_segments (0x82e18 : word) = Some W_82dd0.
Proof. vm_refl. Qed.
Lemma D_82dd0 : decode_any W_82dd0 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd4 : bv 32 := 0x80040513.
Lemma F_82dd4 : fetch_word AsanUbsan.M.loaded_segments (0x82e1c : word) = Some W_82dd4.
Proof. vm_refl. Qed.
Lemma D_82dd4 : decode_any W_82dd4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dd8 : bv 32 := 0xfb850513.
Lemma F_82dd8 : fetch_word AsanUbsan.M.loaded_segments (0x82e20 : word) = Some W_82dd8.
Proof. vm_refl. Qed.
Lemma D_82dd8 : decode_any W_82dd8 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ddc : bv 32 := 0x7ffa8b13.
Lemma F_82ddc : fetch_word AsanUbsan.M.loaded_segments (0x82e24 : word) = Some W_82ddc.
Proof. vm_refl. Qed.
Lemma D_82ddc : decode_any W_82ddc = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82de0 : bv 32 := 0x000b34a3.
Lemma F_82de0 : fetch_word AsanUbsan.M.loaded_segments (0x82e28 : word) = Some W_82de0.
Proof. vm_refl. Qed.
Lemma D_82de0 : decode_any W_82de0 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82de4 : bv 32 := 0x00aab023.
Lemma F_82de4 : fetch_word AsanUbsan.M.loaded_segments (0x82e2c : word) = Some W_82de4.
Proof. vm_refl. Qed.
Lemma D_82de4 : decode_any W_82de4 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82de8 : bv 32 := 0x000ab423.
Lemma F_82de8 : fetch_word AsanUbsan.M.loaded_segments (0x82e30 : word) = Some W_82de8.
Proof. vm_refl. Qed.
Lemma D_82de8 : decode_any W_82de8 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82dec : bv 32 := 0x6b5070ef.
Lemma F_82dec : fetch_word AsanUbsan.M.loaded_segments (0x82e34 : word) = Some W_82dec.
Proof. vm_refl. Qed.
Lemma D_82dec : decode_any W_82dec = Some (Jal 1 32436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82df0 : bv 32 := 0x00200593.
Lemma F_82df0 : fetch_word AsanUbsan.M.loaded_segments (0x82e38 : word) = Some W_82df0.
Proof. vm_refl. Qed.
Lemma D_82df0 : decode_any W_82df0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82df4 : bv 32 := 0x02a5ea63.
Lemma F_82df4 : fetch_word AsanUbsan.M.loaded_segments (0x82e3c : word) = Some W_82df4.
Proof. vm_refl. Qed.
Lemma D_82df4 : decode_any W_82df4 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e28 : bv 32 := 0x155200ef.
Lemma F_82e28 : fetch_word AsanUbsan.M.loaded_segments (0x82e70 : word) = Some W_82e28.
Proof. vm_refl. Qed.
Lemma D_82e28 : decode_any W_82e28 = Some (Jal 1 133460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e2c : bv 32 := 0x000e1597.
Lemma F_82e2c : fetch_word AsanUbsan.M.loaded_segments (0x82e74 : word) = Some W_82e2c.
Proof. vm_refl. Qed.
Lemma D_82e2c : decode_any W_82e2c = Some (Auipc 11 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e30 : bv 32 := 0x6945b583.
Lemma F_82e30 : fetch_word AsanUbsan.M.loaded_segments (0x82e78 : word) = Some W_82e30.
Proof. vm_refl. Qed.
Lemma D_82e30 : decode_any W_82e30 = Some (Load SZ8 true 11 11 1684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e34 : bv 32 := 0x0225ca03.
Lemma F_82e34 : fetch_word AsanUbsan.M.loaded_segments (0x82e7c : word) = Some W_82e34.
Proof. vm_refl. Qed.
Lemma D_82e34 : decode_any W_82e34 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e38 : bv 32 := 0x00050993.
Lemma F_82e38 : fetch_word AsanUbsan.M.loaded_segments (0x82e80 : word) = Some W_82e38.
Proof. vm_refl. Qed.
Lemma D_82e38 : decode_any W_82e38 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e3c : bv 32 := 0x665070ef.
Lemma F_82e3c : fetch_word AsanUbsan.M.loaded_segments (0x82e84 : word) = Some W_82e3c.
Proof. vm_refl. Qed.
Lemma D_82e3c : decode_any W_82e3c = Some (Jal 1 32356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e40 : bv 32 := 0x00050793.
Lemma F_82e40 : fetch_word AsanUbsan.M.loaded_segments (0x82e88 : word) = Some W_82e40.
Proof. vm_refl. Qed.
Lemma D_82e40 : decode_any W_82e40 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e44 : bv 32 := 0x00153513.
Lemma F_82e44 : fetch_word AsanUbsan.M.loaded_segments (0x82e8c : word) = Some W_82e44.
Proof. vm_refl. Qed.
Lemma D_82e44 : decode_any W_82e44 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e48 : bv 32 := 0xfff50513.
Lemma F_82e48 : fetch_word AsanUbsan.M.loaded_segments (0x82e90 : word) = Some W_82e48.
Proof. vm_refl. Qed.
Lemma D_82e48 : decode_any W_82e48 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e4c : bv 32 := 0x008575b3.
Lemma F_82e4c : fetch_word AsanUbsan.M.loaded_segments (0x82e94 : word) = Some W_82e4c.
Proof. vm_refl. Qed.
Lemma D_82e4c : decode_any W_82e4c = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e50 : bv 32 := 0x00100513.
Lemma F_82e50 : fetch_word AsanUbsan.M.loaded_segments (0x82e98 : word) = Some W_82e50.
Proof. vm_refl. Qed.
Lemma D_82e50 : decode_any W_82e50 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e54 : bv 32 := 0x00bb34a3.
Lemma F_82e54 : fetch_word AsanUbsan.M.loaded_segments (0x82e9c : word) = Some W_82e54.
Proof. vm_refl. Qed.
Lemma D_82e54 : decode_any W_82e54 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e58 : bv 32 := 0x00f56a63.
Lemma F_82e58 : fetch_word AsanUbsan.M.loaded_segments (0x82ea0 : word) = Some W_82e58.
Proof. vm_refl. Qed.
Lemma D_82e58 : decode_any W_82e58 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e6c : bv 32 := 0x80040513.
Lemma F_82e6c : fetch_word AsanUbsan.M.loaded_segments (0x82eb4 : word) = Some W_82e6c.
Proof. vm_refl. Qed.
Lemma D_82e6c : decode_any W_82e6c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e70 : bv 32 := 0xfa850513.
Lemma F_82e70 : fetch_word AsanUbsan.M.loaded_segments (0x82eb8 : word) = Some W_82e70.
Proof. vm_refl. Qed.
Lemma D_82e70 : decode_any W_82e70 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e74 : bv 32 := 0x00098593.
Lemma F_82e74 : fetch_word AsanUbsan.M.loaded_segments (0x82ebc : word) = Some W_82e74.
Proof. vm_refl. Qed.
Lemma D_82e74 : decode_any W_82e74 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e78 : bv 32 := 0x00040613.
Lemma F_82e78 : fetch_word AsanUbsan.M.loaded_segments (0x82ec0 : word) = Some W_82e78.
Proof. vm_refl. Qed.
Lemma D_82e78 : decode_any W_82e78 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e7c : bv 32 := 0x00000693.
Lemma F_82e7c : fetch_word AsanUbsan.M.loaded_segments (0x82ec4 : word) = Some W_82e7c.
Proof. vm_refl. Qed.
Lemma D_82e7c : decode_any W_82e7c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e80 : bv 32 := 0x000a0713.
Lemma F_82e80 : fetch_word AsanUbsan.M.loaded_segments (0x82ec8 : word) = Some W_82e80.
Proof. vm_refl. Qed.
Lemma D_82e80 : decode_any W_82e80 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e84 : bv 32 := 0x62d070ef.
Lemma F_82e84 : fetch_word AsanUbsan.M.loaded_segments (0x82ecc : word) = Some W_82e84.
Proof. vm_refl. Qed.
Lemma D_82e84 : decode_any W_82e84 = Some (Jal 1 32300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e88 : bv 32 := 0x80040613.
Lemma F_82e88 : fetch_word AsanUbsan.M.loaded_segments (0x82ed0 : word) = Some W_82e88.
Proof. vm_refl. Qed.
Lemma D_82e88 : decode_any W_82e88 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e8c : bv 32 := 0xfa860613.
Lemma F_82e8c : fetch_word AsanUbsan.M.loaded_segments (0x82ed4 : word) = Some W_82e8c.
Proof. vm_refl. Qed.
Lemma D_82e8c : decode_any W_82e8c = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e90 : bv 32 := 0x00090513.
Lemma F_82e90 : fetch_word AsanUbsan.M.loaded_segments (0x82ed8 : word) = Some W_82e90.
Proof. vm_refl. Qed.
Lemma D_82e90 : decode_any W_82e90 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e94 : bv 32 := 0x00048593.
Lemma F_82e94 : fetch_word AsanUbsan.M.loaded_segments (0x82edc : word) = Some W_82e94.
Proof. vm_refl. Qed.
Lemma D_82e94 : decode_any W_82e94 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e98 : bv 32 := 0xdadd80ef.
Lemma F_82e98 : fetch_word AsanUbsan.M.loaded_segments (0x82ee0 : word) = Some W_82e98.
Proof. vm_refl. Qed.
Lemma D_82e98 : decode_any W_82e98 = Some (Jal 1 1936812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82e9c : bv 32 := 0x07010113.
Lemma F_82e9c : fetch_word AsanUbsan.M.loaded_segments (0x82ee4 : word) = Some W_82e9c.
Proof. vm_refl. Qed.
Lemma D_82e9c : decode_any W_82e9c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea0 : bv 32 := 0x7e813083.
Lemma F_82ea0 : fetch_word AsanUbsan.M.loaded_segments (0x82ee8 : word) = Some W_82ea0.
Proof. vm_refl. Qed.
Lemma D_82ea0 : decode_any W_82ea0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea4 : bv 32 := 0x7e013403.
Lemma F_82ea4 : fetch_word AsanUbsan.M.loaded_segments (0x82eec : word) = Some W_82ea4.
Proof. vm_refl. Qed.
Lemma D_82ea4 : decode_any W_82ea4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ea8 : bv 32 := 0x7d813483.
Lemma F_82ea8 : fetch_word AsanUbsan.M.loaded_segments (0x82ef0 : word) = Some W_82ea8.
Proof. vm_refl. Qed.
Lemma D_82ea8 : decode_any W_82ea8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eac : bv 32 := 0x7d013903.
Lemma F_82eac : fetch_word AsanUbsan.M.loaded_segments (0x82ef4 : word) = Some W_82eac.
Proof. vm_refl. Qed.
Lemma D_82eac : decode_any W_82eac = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb0 : bv 32 := 0x7c813983.
Lemma F_82eb0 : fetch_word AsanUbsan.M.loaded_segments (0x82ef8 : word) = Some W_82eb0.
Proof. vm_refl. Qed.
Lemma D_82eb0 : decode_any W_82eb0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb4 : bv 32 := 0x7c013a03.
Lemma F_82eb4 : fetch_word AsanUbsan.M.loaded_segments (0x82efc : word) = Some W_82eb4.
Proof. vm_refl. Qed.
Lemma D_82eb4 : decode_any W_82eb4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82eb8 : bv 32 := 0x7b813a83.
Lemma F_82eb8 : fetch_word AsanUbsan.M.loaded_segments (0x82f00 : word) = Some W_82eb8.
Proof. vm_refl. Qed.
Lemma D_82eb8 : decode_any W_82eb8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ebc : bv 32 := 0x7b013b03.
Lemma F_82ebc : fetch_word AsanUbsan.M.loaded_segments (0x82f04 : word) = Some W_82ebc.
Proof. vm_refl. Qed.
Lemma D_82ebc : decode_any W_82ebc = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ec0 : bv 32 := 0x7f010113.
Lemma F_82ec0 : fetch_word AsanUbsan.M.loaded_segments (0x82f08 : word) = Some W_82ec0.
Proof. vm_refl. Qed.
Lemma D_82ec0 : decode_any W_82ec0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82ec4 : bv 32 := 0x00008067.
Lemma F_82ec4 : fetch_word AsanUbsan.M.loaded_segments (0x82f0c : word) = Some W_82ec4.
Proof. vm_refl. Qed.
Lemma D_82ec4 : decode_any W_82ec4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

