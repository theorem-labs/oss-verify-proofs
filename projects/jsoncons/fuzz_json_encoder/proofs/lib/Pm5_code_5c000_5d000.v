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
Definition W_5cd7c : bv 32 := 0xfd010113.
Lemma F_5cd7c : fetch_word AsanUbsan.M.loaded_segments (0x5cdc4 : word) = Some W_5cd7c.
Proof. vm_refl. Qed.
Lemma D_5cd7c : decode_any W_5cd7c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd80 : bv 32 := 0x02113423.
Lemma F_5cd80 : fetch_word AsanUbsan.M.loaded_segments (0x5cdc8 : word) = Some W_5cd80.
Proof. vm_refl. Qed.
Lemma D_5cd80 : decode_any W_5cd80 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd84 : bv 32 := 0x02813023.
Lemma F_5cd84 : fetch_word AsanUbsan.M.loaded_segments (0x5cdcc : word) = Some W_5cd84.
Proof. vm_refl. Qed.
Lemma D_5cd84 : decode_any W_5cd84 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd88 : bv 32 := 0x00913c23.
Lemma F_5cd88 : fetch_word AsanUbsan.M.loaded_segments (0x5cdd0 : word) = Some W_5cd88.
Proof. vm_refl. Qed.
Lemma D_5cd88 : decode_any W_5cd88 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd8c : bv 32 := 0x01213823.
Lemma F_5cd8c : fetch_word AsanUbsan.M.loaded_segments (0x5cdd4 : word) = Some W_5cd8c.
Proof. vm_refl. Qed.
Lemma D_5cd8c : decode_any W_5cd8c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd90 : bv 32 := 0x01313423.
Lemma F_5cd90 : fetch_word AsanUbsan.M.loaded_segments (0x5cdd8 : word) = Some W_5cd90.
Proof. vm_refl. Qed.
Lemma D_5cd90 : decode_any W_5cd90 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd94 : bv 32 := 0x09850713.
Lemma F_5cd94 : fetch_word AsanUbsan.M.loaded_segments (0x5cddc : word) = Some W_5cd94.
Proof. vm_refl. Qed.
Lemma D_5cd94 : decode_any W_5cd94 = Some (OpImm ALU_ADD 14 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd98 : bv 32 := 0x0ff00793.
Lemma F_5cd98 : fetch_word AsanUbsan.M.loaded_segments (0x5cde0 : word) = Some W_5cd98.
Proof. vm_refl. Qed.
Lemma D_5cd98 : decode_any W_5cd98 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd9c : bv 32 := 0xffc77813.
Lemma F_5cd9c : fetch_word AsanUbsan.M.loaded_segments (0x5cde4 : word) = Some W_5cd9c.
Proof. vm_refl. Qed.
Lemma D_5cd9c : decode_any W_5cd9c = Some (OpImm ALU_AND 16 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cda0 : bv 32 := 0x00100893.
Lemma F_5cda0 : fetch_word AsanUbsan.M.loaded_segments (0x5cde8 : word) = Some W_5cda0.
Proof. vm_refl. Qed.
Lemma D_5cda0 : decode_any W_5cda0 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cda4 : bv 32 := 0x140822af.
Lemma F_5cda4 : fetch_word AsanUbsan.M.loaded_segments (0x5cdec : word) = Some W_5cda4.
Proof. vm_refl. Qed.
Lemma D_5cda4 : decode_any W_5cda4 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cda8 : bv 32 := 0x00088313.
Lemma F_5cda8 : fetch_word AsanUbsan.M.loaded_segments (0x5cdf0 : word) = Some W_5cda8.
Proof. vm_refl. Qed.
Lemma D_5cda8 : decode_any W_5cda8 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdac : bv 32 := 0x0062c333.
Lemma F_5cdac : fetch_word AsanUbsan.M.loaded_segments (0x5cdf4 : word) = Some W_5cdac.
Proof. vm_refl. Qed.
Lemma D_5cdac : decode_any W_5cdac = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdb0 : bv 32 := 0x00f37333.
Lemma F_5cdb0 : fetch_word AsanUbsan.M.loaded_segments (0x5cdf8 : word) = Some W_5cdb0.
Proof. vm_refl. Qed.
Lemma D_5cdb0 : decode_any W_5cdb0 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdb4 : bv 32 := 0x0062c333.
Lemma F_5cdb4 : fetch_word AsanUbsan.M.loaded_segments (0x5cdfc : word) = Some W_5cdb4.
Proof. vm_refl. Qed.
Lemma D_5cdb4 : decode_any W_5cdb4 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdb8 : bv 32 := 0x1868232f.
Lemma F_5cdb8 : fetch_word AsanUbsan.M.loaded_segments (0x5ce00 : word) = Some W_5cdb8.
Proof. vm_refl. Qed.
Lemma D_5cdb8 : decode_any W_5cdb8 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdbc : bv 32 := 0xfe0314e3.
Lemma F_5cdbc : fetch_word AsanUbsan.M.loaded_segments (0x5ce04 : word) = Some W_5cdbc.
Proof. vm_refl. Qed.
Lemma D_5cdbc : decode_any W_5cdbc = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdc0 : bv 32 := 0x0ff2f793.
Lemma F_5cdc0 : fetch_word AsanUbsan.M.loaded_segments (0x5ce08 : word) = Some W_5cdc0.
Proof. vm_refl. Qed.
Lemma D_5cdc0 : decode_any W_5cdc0 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdc4 : bv 32 := 0x10079663.
Lemma F_5cdc4 : fetch_word AsanUbsan.M.loaded_segments (0x5ce0c : word) = Some W_5cdc4.
Proof. vm_refl. Qed.
Lemma D_5cdc4 : decode_any W_5cdc4 = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdc8 : bv 32 := 0x0a050713.
Lemma F_5cdc8 : fetch_word AsanUbsan.M.loaded_segments (0x5ce10 : word) = Some W_5cdc8.
Proof. vm_refl. Qed.
Lemma D_5cdc8 : decode_any W_5cdc8 = Some (OpImm ALU_ADD 14 10 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdcc : bv 32 := 0x12b70a63.
Lemma F_5cdcc : fetch_word AsanUbsan.M.loaded_segments (0x5ce14 : word) = Some W_5cdcc.
Proof. vm_refl. Qed.
Lemma D_5cdcc : decode_any W_5cdcc = Some (Branch BC_EQ 14 11 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdd0 : bv 32 := 0x0005b783.
Lemma F_5cdd0 : fetch_word AsanUbsan.M.loaded_segments (0x5ce18 : word) = Some W_5cdd0.
Proof. vm_refl. Qed.
Lemma D_5cdd0 : decode_any W_5cdd0 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdd4 : bv 32 := 0x04078863.
Lemma F_5cdd4 : fetch_word AsanUbsan.M.loaded_segments (0x5ce1c : word) = Some W_5cdd4.
Proof. vm_refl. Qed.
Lemma D_5cdd4 : decode_any W_5cdd4 = Some (Branch BC_EQ 15 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdd8 : bv 32 := 0x00073803.
Lemma F_5cdd8 : fetch_word AsanUbsan.M.loaded_segments (0x5ce20 : word) = Some W_5cdd8.
Proof. vm_refl. Qed.
Lemma D_5cdd8 : decode_any W_5cdd8 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cddc : bv 32 := 0x02080263.
Lemma F_5cddc : fetch_word AsanUbsan.M.loaded_segments (0x5ce24 : word) = Some W_5cddc.
Proof. vm_refl. Qed.
Lemma D_5cddc : decode_any W_5cddc = Some (Branch BC_EQ 16 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cde0 : bv 32 := 0x0b053703.
Lemma F_5cde0 : fetch_word AsanUbsan.M.loaded_segments (0x5ce28 : word) = Some W_5cde0.
Proof. vm_refl. Qed.
Lemma D_5cde0 : decode_any W_5cde0 = Some (Load SZ8 true 14 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cde4 : bv 32 := 0x0085b883.
Lemma F_5cde4 : fetch_word AsanUbsan.M.loaded_segments (0x5ce2c : word) = Some W_5cde4.
Proof. vm_refl. Qed.
Lemma D_5cde4 : decode_any W_5cde4 = Some (Load SZ8 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cde8 : bv 32 := 0x0105b283.
Lemma F_5cde8 : fetch_word AsanUbsan.M.loaded_segments (0x5ce30 : word) = Some W_5cde8.
Proof. vm_refl. Qed.
Lemma D_5cde8 : decode_any W_5cde8 = Some (Load SZ8 true 5 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdec : bv 32 := 0x00f807b3.
Lemma F_5cdec : fetch_word AsanUbsan.M.loaded_segments (0x5ce34 : word) = Some W_5cdec.
Proof. vm_refl. Qed.
Lemma D_5cdec : decode_any W_5cdec = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdf0 : bv 32 := 0x01173023.
Lemma F_5cdf0 : fetch_word AsanUbsan.M.loaded_segments (0x5ce38 : word) = Some W_5cdf0.
Proof. vm_refl. Qed.
Lemma D_5cdf0 : decode_any W_5cdf0 = Some (Store SZ8 14 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdf4 : bv 32 := 0x0af53023.
Lemma F_5cdf4 : fetch_word AsanUbsan.M.loaded_segments (0x5ce3c : word) = Some W_5cdf4.
Proof. vm_refl. Qed.
Lemma D_5cdf4 : decode_any W_5cdf4 = Some (Store SZ8 10 15 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdf8 : bv 32 := 0x0a553823.
Lemma F_5cdf8 : fetch_word AsanUbsan.M.loaded_segments (0x5ce40 : word) = Some W_5cdf8.
Proof. vm_refl. Qed.
Lemma D_5cdf8 : decode_any W_5cdf8 = Some (Store SZ8 10 5 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cdfc : bv 32 := 0x01c0006f.
Lemma F_5cdfc : fetch_word AsanUbsan.M.loaded_segments (0x5ce44 : word) = Some W_5cdfc.
Proof. vm_refl. Qed.
Lemma D_5cdfc : decode_any W_5cdfc = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce00 : bv 32 := 0x0105b783.
Lemma F_5ce00 : fetch_word AsanUbsan.M.loaded_segments (0x5ce48 : word) = Some W_5ce00.
Proof. vm_refl. Qed.
Lemma D_5ce00 : decode_any W_5ce00 = Some (Load SZ8 true 15 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce04 : bv 32 := 0x00f73823.
Lemma F_5ce04 : fetch_word AsanUbsan.M.loaded_segments (0x5ce4c : word) = Some W_5ce04.
Proof. vm_refl. Qed.
Lemma D_5ce04 : decode_any W_5ce04 = Some (Store SZ8 14 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce08 : bv 32 := 0x0085b783.
Lemma F_5ce08 : fetch_word AsanUbsan.M.loaded_segments (0x5ce50 : word) = Some W_5ce08.
Proof. vm_refl. Qed.
Lemma D_5ce08 : decode_any W_5ce08 = Some (Load SZ8 true 15 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce0c : bv 32 := 0x00f73423.
Lemma F_5ce0c : fetch_word AsanUbsan.M.loaded_segments (0x5ce54 : word) = Some W_5ce0c.
Proof. vm_refl. Qed.
Lemma D_5ce0c : decode_any W_5ce0c = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce10 : bv 32 := 0x0005b783.
Lemma F_5ce10 : fetch_word AsanUbsan.M.loaded_segments (0x5ce58 : word) = Some W_5ce10.
Proof. vm_refl. Qed.
Lemma D_5ce10 : decode_any W_5ce10 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce14 : bv 32 := 0x00f73023.
Lemma F_5ce14 : fetch_word AsanUbsan.M.loaded_segments (0x5ce5c : word) = Some W_5ce14.
Proof. vm_refl. Qed.
Lemma D_5ce14 : decode_any W_5ce14 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce18 : bv 32 := 0x0005b023.
Lemma F_5ce18 : fetch_word AsanUbsan.M.loaded_segments (0x5ce60 : word) = Some W_5ce18.
Proof. vm_refl. Qed.
Lemma D_5ce18 : decode_any W_5ce18 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce1c : bv 32 := 0x0005b423.
Lemma F_5ce1c : fetch_word AsanUbsan.M.loaded_segments (0x5ce64 : word) = Some W_5ce1c.
Proof. vm_refl. Qed.
Lemma D_5ce1c : decode_any W_5ce1c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce20 : bv 32 := 0x0005b823.
Lemma F_5ce20 : fetch_word AsanUbsan.M.loaded_segments (0x5ce68 : word) = Some W_5ce20.
Proof. vm_refl. Qed.
Lemma D_5ce20 : decode_any W_5ce20 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce24 : bv 32 := 0x0185b703.
Lemma F_5ce24 : fetch_word AsanUbsan.M.loaded_segments (0x5ce6c : word) = Some W_5ce24.
Proof. vm_refl. Qed.
Lemma D_5ce24 : decode_any W_5ce24 = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce28 : bv 32 := 0x0b853783.
Lemma F_5ce28 : fetch_word AsanUbsan.M.loaded_segments (0x5ce70 : word) = Some W_5ce28.
Proof. vm_refl. Qed.
Lemma D_5ce28 : decode_any W_5ce28 = Some (Load SZ8 true 15 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce2c : bv 32 := 0x00e78733.
Lemma F_5ce2c : fetch_word AsanUbsan.M.loaded_segments (0x5ce74 : word) = Some W_5ce2c.
Proof. vm_refl. Qed.
Lemma D_5ce2c : decode_any W_5ce2c = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce30 : bv 32 := 0x0ae53c23.
Lemma F_5ce30 : fetch_word AsanUbsan.M.loaded_segments (0x5ce78 : word) = Some W_5ce30.
Proof. vm_refl. Qed.
Lemma D_5ce30 : decode_any W_5ce30 = Some (Store SZ8 10 14 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce34 : bv 32 := 0x0005bc23.
Lemma F_5ce34 : fetch_word AsanUbsan.M.loaded_segments (0x5ce7c : word) = Some W_5ce34.
Proof. vm_refl. Qed.
Lemma D_5ce34 : decode_any W_5ce34 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce38 : bv 32 := 0x0310000f.
Lemma F_5ce38 : fetch_word AsanUbsan.M.loaded_segments (0x5ce80 : word) = Some W_5ce38.
Proof. vm_refl. Qed.
Lemma D_5ce38 : decode_any W_5ce38 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce3c : bv 32 := 0x08050c23.
Lemma F_5ce3c : fetch_word AsanUbsan.M.loaded_segments (0x5ce84 : word) = Some W_5ce3c.
Proof. vm_refl. Qed.
Lemma D_5ce3c : decode_any W_5ce3c = Some (Store SZ1 10 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce40 : bv 32 := 0x0b853583.
Lemma F_5ce40 : fetch_word AsanUbsan.M.loaded_segments (0x5ce88 : word) = Some W_5ce40.
Proof. vm_refl. Qed.
Lemma D_5ce40 : decode_any W_5ce40 = Some (Load SZ8 true 11 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce44 : bv 32 := 0x04053703.
Lemma F_5ce44 : fetch_word AsanUbsan.M.loaded_segments (0x5ce8c : word) = Some W_5ce44.
Proof. vm_refl. Qed.
Lemma D_5ce44 : decode_any W_5ce44 = Some (Load SZ8 true 14 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce48 : bv 32 := 0x04b77663.
Lemma F_5ce48 : fetch_word AsanUbsan.M.loaded_segments (0x5ce90 : word) = Some W_5ce48.
Proof. vm_refl. Qed.
Lemma D_5ce48 : decode_any W_5ce48 = Some (Branch BC_GEU 14 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce4c : bv 32 := 0x09950593.
Lemma F_5ce4c : fetch_word AsanUbsan.M.loaded_segments (0x5ce94 : word) = Some W_5ce4c.
Proof. vm_refl. Qed.
Lemma D_5ce4c : decode_any W_5ce4c = Some (OpImm ALU_ADD 11 10 153, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce50 : bv 32 := 0x0ff00713.
Lemma F_5ce50 : fetch_word AsanUbsan.M.loaded_segments (0x5ce98 : word) = Some W_5ce50.
Proof. vm_refl. Qed.
Lemma D_5ce50 : decode_any W_5ce50 = Some (OpImm ALU_ADD 14 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce54 : bv 32 := 0x00100793.
Lemma F_5ce54 : fetch_word AsanUbsan.M.loaded_segments (0x5ce9c : word) = Some W_5ce54.
Proof. vm_refl. Qed.
Lemma D_5ce54 : decode_any W_5ce54 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce58 : bv 32 := 0xffc5f813.
Lemma F_5ce58 : fetch_word AsanUbsan.M.loaded_segments (0x5cea0 : word) = Some W_5ce58.
Proof. vm_refl. Qed.
Lemma D_5ce58 : decode_any W_5ce58 = Some (OpImm ALU_AND 16 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce5c : bv 32 := 0x0035f593.
Lemma F_5ce5c : fetch_word AsanUbsan.M.loaded_segments (0x5cea4 : word) = Some W_5ce5c.
Proof. vm_refl. Qed.
Lemma D_5ce5c : decode_any W_5ce5c = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce60 : bv 32 := 0x00359593.
Lemma F_5ce60 : fetch_word AsanUbsan.M.loaded_segments (0x5cea8 : word) = Some W_5ce60.
Proof. vm_refl. Qed.
Lemma D_5ce60 : decode_any W_5ce60 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce64 : bv 32 := 0x00b7173b.
Lemma F_5ce64 : fetch_word AsanUbsan.M.loaded_segments (0x5ceac : word) = Some W_5ce64.
Proof. vm_refl. Qed.
Lemma D_5ce64 : decode_any W_5ce64 = Some (Op32 ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce68 : bv 32 := 0x00b797bb.
Lemma F_5ce68 : fetch_word AsanUbsan.M.loaded_segments (0x5ceb0 : word) = Some W_5ce68.
Proof. vm_refl. Qed.
Lemma D_5ce68 : decode_any W_5ce68 = Some (Op32 ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce6c : bv 32 := 0x140828af.
Lemma F_5ce6c : fetch_word AsanUbsan.M.loaded_segments (0x5ceb4 : word) = Some W_5ce6c.
Proof. vm_refl. Qed.
Lemma D_5ce6c : decode_any W_5ce6c = Some (Lr AW true false 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce70 : bv 32 := 0x00078293.
Lemma F_5ce70 : fetch_word AsanUbsan.M.loaded_segments (0x5ceb8 : word) = Some W_5ce70.
Proof. vm_refl. Qed.
Lemma D_5ce70 : decode_any W_5ce70 = Some (OpImm ALU_ADD 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce74 : bv 32 := 0x0058c2b3.
Lemma F_5ce74 : fetch_word AsanUbsan.M.loaded_segments (0x5cebc : word) = Some W_5ce74.
Proof. vm_refl. Qed.
Lemma D_5ce74 : decode_any W_5ce74 = Some (Op ALU_XOR 5 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce78 : bv 32 := 0x00e2f2b3.
Lemma F_5ce78 : fetch_word AsanUbsan.M.loaded_segments (0x5cec0 : word) = Some W_5ce78.
Proof. vm_refl. Qed.
Lemma D_5ce78 : decode_any W_5ce78 = Some (Op ALU_AND 5 5 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce7c : bv 32 := 0x0058c2b3.
Lemma F_5ce7c : fetch_word AsanUbsan.M.loaded_segments (0x5cec4 : word) = Some W_5ce7c.
Proof. vm_refl. Qed.
Lemma D_5ce7c : decode_any W_5ce7c = Some (Op ALU_XOR 5 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce80 : bv 32 := 0x185822af.
Lemma F_5ce80 : fetch_word AsanUbsan.M.loaded_segments (0x5cec8 : word) = Some W_5ce80.
Proof. vm_refl. Qed.
Lemma D_5ce80 : decode_any W_5ce80 = Some (Sc AW false false 5 16 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce84 : bv 32 := 0xfe0294e3.
Lemma F_5ce84 : fetch_word AsanUbsan.M.loaded_segments (0x5cecc : word) = Some W_5ce84.
Proof. vm_refl. Qed.
Lemma D_5ce84 : decode_any W_5ce84 = Some (Branch BC_NE 5 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce88 : bv 32 := 0x00b8d5bb.
Lemma F_5ce88 : fetch_word AsanUbsan.M.loaded_segments (0x5ced0 : word) = Some W_5ce88.
Proof. vm_refl. Qed.
Lemma D_5ce88 : decode_any W_5ce88 = Some (Op32 ALU_SRL 11 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce8c : bv 32 := 0x0ff5f593.
Lemma F_5ce8c : fetch_word AsanUbsan.M.loaded_segments (0x5ced4 : word) = Some W_5ce8c.
Proof. vm_refl. Qed.
Lemma D_5ce8c : decode_any W_5ce8c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce90 : bv 32 := 0x02058063.
Lemma F_5ce90 : fetch_word AsanUbsan.M.loaded_segments (0x5ced8 : word) = Some W_5ce90.
Proof. vm_refl. Qed.
Lemma D_5ce90 : decode_any W_5ce90 = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce94 : bv 32 := 0x02813083.
Lemma F_5ce94 : fetch_word AsanUbsan.M.loaded_segments (0x5cedc : word) = Some W_5ce94.
Proof. vm_refl. Qed.
Lemma D_5ce94 : decode_any W_5ce94 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce98 : bv 32 := 0x02013403.
Lemma F_5ce98 : fetch_word AsanUbsan.M.loaded_segments (0x5cee0 : word) = Some W_5ce98.
Proof. vm_refl. Qed.
Lemma D_5ce98 : decode_any W_5ce98 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ce9c : bv 32 := 0x01813483.
Lemma F_5ce9c : fetch_word AsanUbsan.M.loaded_segments (0x5cee4 : word) = Some W_5ce9c.
Proof. vm_refl. Qed.
Lemma D_5ce9c : decode_any W_5ce9c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cea0 : bv 32 := 0x01013903.
Lemma F_5cea0 : fetch_word AsanUbsan.M.loaded_segments (0x5cee8 : word) = Some W_5cea0.
Proof. vm_refl. Qed.
Lemma D_5cea0 : decode_any W_5cea0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cea4 : bv 32 := 0x00813983.
Lemma F_5cea4 : fetch_word AsanUbsan.M.loaded_segments (0x5ceec : word) = Some W_5cea4.
Proof. vm_refl. Qed.
Lemma D_5cea4 : decode_any W_5cea4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cea8 : bv 32 := 0x03010113.
Lemma F_5cea8 : fetch_word AsanUbsan.M.loaded_segments (0x5cef0 : word) = Some W_5cea8.
Proof. vm_refl. Qed.
Lemma D_5cea8 : decode_any W_5cea8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ceac : bv 32 := 0x00008067.
Lemma F_5ceac : fetch_word AsanUbsan.M.loaded_segments (0x5cef4 : word) = Some W_5ceac.
Proof. vm_refl. Qed.
Lemma D_5ceac : decode_any W_5ceac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ceb0 : bv 32 := 0x04853583.
Lemma F_5ceb0 : fetch_word AsanUbsan.M.loaded_segments (0x5cef8 : word) = Some W_5ceb0.
Proof. vm_refl. Qed.
Lemma D_5ceb0 : decode_any W_5ceb0 = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ceb4 : bv 32 := 0x02813083.
Lemma F_5ceb4 : fetch_word AsanUbsan.M.loaded_segments (0x5cefc : word) = Some W_5ceb4.
Proof. vm_refl. Qed.
Lemma D_5ceb4 : decode_any W_5ceb4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ceb8 : bv 32 := 0x02013403.
Lemma F_5ceb8 : fetch_word AsanUbsan.M.loaded_segments (0x5cf00 : word) = Some W_5ceb8.
Proof. vm_refl. Qed.
Lemma D_5ceb8 : decode_any W_5ceb8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cebc : bv 32 := 0x01813483.
Lemma F_5cebc : fetch_word AsanUbsan.M.loaded_segments (0x5cf04 : word) = Some W_5cebc.
Proof. vm_refl. Qed.
Lemma D_5cebc : decode_any W_5cebc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cec0 : bv 32 := 0x01013903.
Lemma F_5cec0 : fetch_word AsanUbsan.M.loaded_segments (0x5cf08 : word) = Some W_5cec0.
Proof. vm_refl. Qed.
Lemma D_5cec0 : decode_any W_5cec0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cec4 : bv 32 := 0x00813983.
Lemma F_5cec4 : fetch_word AsanUbsan.M.loaded_segments (0x5cf0c : word) = Some W_5cec4.
Proof. vm_refl. Qed.
Lemma D_5cec4 : decode_any W_5cec4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cec8 : bv 32 := 0x03010113.
Lemma F_5cec8 : fetch_word AsanUbsan.M.loaded_segments (0x5cf10 : word) = Some W_5cec8.
Proof. vm_refl. Qed.
Lemma D_5cec8 : decode_any W_5cec8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cecc : bv 32 := 0x0540006f.
Lemma F_5cecc : fetch_word AsanUbsan.M.loaded_segments (0x5cf14 : word) = Some W_5cecc.
Proof. vm_refl. Qed.
Lemma D_5cecc : decode_any W_5cecc = Some (Jal 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf20 : bv 32 := 0xfb010113.
Lemma F_5cf20 : fetch_word AsanUbsan.M.loaded_segments (0x5cf68 : word) = Some W_5cf20.
Proof. vm_refl. Qed.
Lemma D_5cf20 : decode_any W_5cf20 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf24 : bv 32 := 0x04113423.
Lemma F_5cf24 : fetch_word AsanUbsan.M.loaded_segments (0x5cf6c : word) = Some W_5cf24.
Proof. vm_refl. Qed.
Lemma D_5cf24 : decode_any W_5cf24 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf28 : bv 32 := 0x04813023.
Lemma F_5cf28 : fetch_word AsanUbsan.M.loaded_segments (0x5cf70 : word) = Some W_5cf28.
Proof. vm_refl. Qed.
Lemma D_5cf28 : decode_any W_5cf28 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf2c : bv 32 := 0x02913c23.
Lemma F_5cf2c : fetch_word AsanUbsan.M.loaded_segments (0x5cf74 : word) = Some W_5cf2c.
Proof. vm_refl. Qed.
Lemma D_5cf2c : decode_any W_5cf2c = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf30 : bv 32 := 0x03213823.
Lemma F_5cf30 : fetch_word AsanUbsan.M.loaded_segments (0x5cf78 : word) = Some W_5cf30.
Proof. vm_refl. Qed.
Lemma D_5cf30 : decode_any W_5cf30 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf34 : bv 32 := 0x03313423.
Lemma F_5cf34 : fetch_word AsanUbsan.M.loaded_segments (0x5cf7c : word) = Some W_5cf34.
Proof. vm_refl. Qed.
Lemma D_5cf34 : decode_any W_5cf34 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf38 : bv 32 := 0x03413023.
Lemma F_5cf38 : fetch_word AsanUbsan.M.loaded_segments (0x5cf80 : word) = Some W_5cf38.
Proof. vm_refl. Qed.
Lemma D_5cf38 : decode_any W_5cf38 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf3c : bv 32 := 0x00013023.
Lemma F_5cf3c : fetch_word AsanUbsan.M.loaded_segments (0x5cf84 : word) = Some W_5cf3c.
Proof. vm_refl. Qed.
Lemma D_5cf3c : decode_any W_5cf3c = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf40 : bv 32 := 0x00013423.
Lemma F_5cf40 : fetch_word AsanUbsan.M.loaded_segments (0x5cf88 : word) = Some W_5cf40.
Proof. vm_refl. Qed.
Lemma D_5cf40 : decode_any W_5cf40 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf44 : bv 32 := 0x00013823.
Lemma F_5cf44 : fetch_word AsanUbsan.M.loaded_segments (0x5cf8c : word) = Some W_5cf44.
Proof. vm_refl. Qed.
Lemma D_5cf44 : decode_any W_5cf44 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf48 : bv 32 := 0x00013c23.
Lemma F_5cf48 : fetch_word AsanUbsan.M.loaded_segments (0x5cf90 : word) = Some W_5cf48.
Proof. vm_refl. Qed.
Lemma D_5cf48 : decode_any W_5cf48 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf4c : bv 32 := 0x09850713.
Lemma F_5cf4c : fetch_word AsanUbsan.M.loaded_segments (0x5cf94 : word) = Some W_5cf4c.
Proof. vm_refl. Qed.
Lemma D_5cf4c : decode_any W_5cf4c = Some (OpImm ALU_ADD 14 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf50 : bv 32 := 0x0ff00793.
Lemma F_5cf50 : fetch_word AsanUbsan.M.loaded_segments (0x5cf98 : word) = Some W_5cf50.
Proof. vm_refl. Qed.
Lemma D_5cf50 : decode_any W_5cf50 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf54 : bv 32 := 0xffc77813.
Lemma F_5cf54 : fetch_word AsanUbsan.M.loaded_segments (0x5cf9c : word) = Some W_5cf54.
Proof. vm_refl. Qed.
Lemma D_5cf54 : decode_any W_5cf54 = Some (OpImm ALU_AND 16 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf58 : bv 32 := 0x00100893.
Lemma F_5cf58 : fetch_word AsanUbsan.M.loaded_segments (0x5cfa0 : word) = Some W_5cf58.
Proof. vm_refl. Qed.
Lemma D_5cf58 : decode_any W_5cf58 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf5c : bv 32 := 0x140822af.
Lemma F_5cf5c : fetch_word AsanUbsan.M.loaded_segments (0x5cfa4 : word) = Some W_5cf5c.
Proof. vm_refl. Qed.
Lemma D_5cf5c : decode_any W_5cf5c = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf60 : bv 32 := 0x00088313.
Lemma F_5cf60 : fetch_word AsanUbsan.M.loaded_segments (0x5cfa8 : word) = Some W_5cf60.
Proof. vm_refl. Qed.
Lemma D_5cf60 : decode_any W_5cf60 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf64 : bv 32 := 0x0062c333.
Lemma F_5cf64 : fetch_word AsanUbsan.M.loaded_segments (0x5cfac : word) = Some W_5cf64.
Proof. vm_refl. Qed.
Lemma D_5cf64 : decode_any W_5cf64 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf68 : bv 32 := 0x00f37333.
Lemma F_5cf68 : fetch_word AsanUbsan.M.loaded_segments (0x5cfb0 : word) = Some W_5cf68.
Proof. vm_refl. Qed.
Lemma D_5cf68 : decode_any W_5cf68 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf6c : bv 32 := 0x0062c333.
Lemma F_5cf6c : fetch_word AsanUbsan.M.loaded_segments (0x5cfb4 : word) = Some W_5cf6c.
Proof. vm_refl. Qed.
Lemma D_5cf6c : decode_any W_5cf6c = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf70 : bv 32 := 0x1868232f.
Lemma F_5cf70 : fetch_word AsanUbsan.M.loaded_segments (0x5cfb8 : word) = Some W_5cf70.
Proof. vm_refl. Qed.
Lemma D_5cf70 : decode_any W_5cf70 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf74 : bv 32 := 0xfe0314e3.
Lemma F_5cf74 : fetch_word AsanUbsan.M.loaded_segments (0x5cfbc : word) = Some W_5cf74.
Proof. vm_refl. Qed.
Lemma D_5cf74 : decode_any W_5cf74 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf78 : bv 32 := 0x0ff2f793.
Lemma F_5cf78 : fetch_word AsanUbsan.M.loaded_segments (0x5cfc0 : word) = Some W_5cf78.
Proof. vm_refl. Qed.
Lemma D_5cf78 : decode_any W_5cf78 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf7c : bv 32 := 0x12079a63.
Lemma F_5cf7c : fetch_word AsanUbsan.M.loaded_segments (0x5cfc4 : word) = Some W_5cf7c.
Proof. vm_refl. Qed.
Lemma D_5cf7c : decode_any W_5cf7c = Some (Branch BC_NE 15 0 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf80 : bv 32 := 0x0b853783.
Lemma F_5cf80 : fetch_word AsanUbsan.M.loaded_segments (0x5cfc8 : word) = Some W_5cf80.
Proof. vm_refl. Qed.
Lemma D_5cf80 : decode_any W_5cf80 = Some (Load SZ8 true 15 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf84 : bv 32 := 0x0a053803.
Lemma F_5cf84 : fetch_word AsanUbsan.M.loaded_segments (0x5cfcc : word) = Some W_5cf84.
Proof. vm_refl. Qed.
Lemma D_5cf84 : decode_any W_5cf84 = Some (Load SZ8 true 16 10 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf88 : bv 32 := 0x00d81713.
Lemma F_5cf88 : fetch_word AsanUbsan.M.loaded_segments (0x5cfd0 : word) = Some W_5cf88.
Proof. vm_refl. Qed.
Lemma D_5cf88 : decode_any W_5cf88 = Some (ShiftImm ALU_SLL 14 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf8c : bv 32 := 0x14e7ee63.
Lemma F_5cf8c : fetch_word AsanUbsan.M.loaded_segments (0x5cfd4 : word) = Some W_5cf8c.
Proof. vm_refl. Qed.
Lemma D_5cf8c : decode_any W_5cf8c = Some (Branch BC_LTU 15 14 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf90 : bv 32 := 0x04f77663.
Lemma F_5cf90 : fetch_word AsanUbsan.M.loaded_segments (0x5cfd8 : word) = Some W_5cf90.
Proof. vm_refl. Qed.
Lemma D_5cf90 : decode_any W_5cf90 = Some (Branch BC_GEU 14 15 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf94 : bv 32 := 0x00190737.
Lemma F_5cf94 : fetch_word AsanUbsan.M.loaded_segments (0x5cfdc : word) = Some W_5cf94.
Proof. vm_refl. Qed.
Lemma D_5cf94 : decode_any W_5cf94 = Some (Lui 14 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf98 : bv 32 := 0x06400893.
Lemma F_5cf98 : fetch_word AsanUbsan.M.loaded_segments (0x5cfe0 : word) = Some W_5cf98.
Proof. vm_refl. Qed.
Lemma D_5cf98 : decode_any W_5cf98 = Some (OpImm ALU_ADD 17 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf9c : bv 32 := 0x02e80733.
Lemma F_5cf9c : fetch_word AsanUbsan.M.loaded_segments (0x5cfe4 : word) = Some W_5cf9c.
Proof. vm_refl. Qed.
Lemma D_5cf9c : decode_any W_5cf9c = Some (Mul M_MUL 14 16 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cfa0 : bv 32 := 0x031787b3.
Lemma F_5cfa0 : fetch_word AsanUbsan.M.loaded_segments (0x5cfe8 : word) = Some W_5cfa0.
Proof. vm_refl. Qed.
Lemma D_5cfa0 : decode_any W_5cfa0 = Some (Mul M_MUL 15 15 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cfa4 : bv 32 := 0x02e7fc63.
Lemma F_5cfa4 : fetch_word AsanUbsan.M.loaded_segments (0x5cfec : word) = Some W_5cfa4.
Proof. vm_refl. Qed.
Lemma D_5cfa4 : decode_any W_5cfa4 = Some (Branch BC_GEU 15 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cfdc : bv 32 := 0x00013703.
Lemma F_5cfdc : fetch_word AsanUbsan.M.loaded_segments (0x5d024 : word) = Some W_5cfdc.
Proof. vm_refl. Qed.
Lemma D_5cfdc : decode_any W_5cfdc = Some (Load SZ8 true 14 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cfe0 : bv 32 := 0x01013783.
Lemma F_5cfe0 : fetch_word AsanUbsan.M.loaded_segments (0x5d028 : word) = Some W_5cfe0.
Proof. vm_refl. Qed.
Lemma D_5cfe0 : decode_any W_5cfe0 = Some (Load SZ8 true 15 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cfe4 : bv 32 := 0x0b853883.
Lemma F_5cfe4 : fetch_word AsanUbsan.M.loaded_segments (0x5d02c : word) = Some W_5cfe4.
Proof. vm_refl. Qed.
Lemma D_5cfe4 : decode_any W_5cfe4 = Some (Load SZ8 true 17 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cfe8 : bv 32 := 0x0915f863.
Lemma F_5cfe8 : fetch_word AsanUbsan.M.loaded_segments (0x5d030 : word) = Some W_5cfe8.
Proof. vm_refl. Qed.
Lemma D_5cfe8 : decode_any W_5cfe8 = Some (Branch BC_GEU 11 17 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cfec : bv 32 := 0x0a853283.
Lemma F_5cfec : fetch_word AsanUbsan.M.loaded_segments (0x5d034 : word) = Some W_5cfec.
Proof. vm_refl. Qed.
Lemma D_5cfec : decode_any W_5cfec = Some (Load SZ8 true 5 10 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cff0 : bv 32 := 0x02c0006f.
Lemma F_5cff0 : fetch_word AsanUbsan.M.loaded_segments (0x5d038 : word) = Some W_5cff0.
Proof. vm_refl. Qed.
Lemma D_5cff0 : decode_any W_5cff0 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cff4 : bv 32 := 0x0067b023.
Lemma F_5cff4 : fetch_word AsanUbsan.M.loaded_segments (0x5d03c : word) = Some W_5cff4.
Proof. vm_refl. Qed.
Lemma D_5cff4 : decode_any W_5cff4 = Some (Store SZ8 15 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cff8 : bv 32 := 0x00833783.
Lemma F_5cff8 : fetch_word AsanUbsan.M.loaded_segments (0x5d040 : word) = Some W_5cff8.
Proof. vm_refl. Qed.
Lemma D_5cff8 : decode_any W_5cff8 = Some (Load SZ8 true 15 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cffc : bv 32 := 0x01813283.
Lemma F_5cffc : fetch_word AsanUbsan.M.loaded_segments (0x5d044 : word) = Some W_5cffc.
Proof. vm_refl. Qed.
Lemma D_5cffc : decode_any W_5cffc = Some (Load SZ8 true 5 2 24, 4%Z).
Proof. vm_refl. Qed.

