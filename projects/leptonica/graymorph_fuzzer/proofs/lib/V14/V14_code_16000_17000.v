(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushU14.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_1612c : bv 32 := 0xfd010113.
Lemma F_1612c : fetch_word Ubsan.M.loaded_segments (0x16228 : word) = Some W_1612c.
Proof. vm_refl. Qed.
Lemma D_1612c : decode_any W_1612c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16130 : bv 32 := 0x02113423.
Lemma F_16130 : fetch_word Ubsan.M.loaded_segments (0x1622c : word) = Some W_16130.
Proof. vm_refl. Qed.
Lemma D_16130 : decode_any W_16130 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16134 : bv 32 := 0x02813023.
Lemma F_16134 : fetch_word Ubsan.M.loaded_segments (0x16230 : word) = Some W_16134.
Proof. vm_refl. Qed.
Lemma D_16134 : decode_any W_16134 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16138 : bv 32 := 0x00913c23.
Lemma F_16138 : fetch_word Ubsan.M.loaded_segments (0x16234 : word) = Some W_16138.
Proof. vm_refl. Qed.
Lemma D_16138 : decode_any W_16138 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1613c : bv 32 := 0x0e058863.
Lemma F_1613c : fetch_word Ubsan.M.loaded_segments (0x16238 : word) = Some W_1613c.
Proof. vm_refl. Qed.
Lemma D_1613c : decode_any W_1613c = Some (Branch BC_EQ 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16140 : bv 32 := 0x10050a63.
Lemma F_16140 : fetch_word Ubsan.M.loaded_segments (0x1623c : word) = Some W_16140.
Proof. vm_refl. Qed.
Lemma D_16140 : decode_any W_16140 = Some (Branch BC_EQ 10 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16144 : bv 32 := 0x0ea58063.
Lemma F_16144 : fetch_word Ubsan.M.loaded_segments (0x16240 : word) = Some W_16144.
Proof. vm_refl. Qed.
Lemma D_16144 : decode_any W_16144 = Some (Branch BC_EQ 11 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16148 : bv 32 := 0x0075f613.
Lemma F_16148 : fetch_word Ubsan.M.loaded_segments (0x16244 : word) = Some W_16148.
Proof. vm_refl. Qed.
Lemma D_16148 : decode_any W_16148 = Some (OpImm ALU_AND 12 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1614c : bv 32 := 0x1c061e63.
Lemma F_1614c : fetch_word Ubsan.M.loaded_segments (0x16248 : word) = Some W_1614c.
Proof. vm_refl. Qed.
Lemma D_1614c : decode_any W_1614c = Some (Branch BC_NE 12 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16150 : bv 32 := 0x00757613.
Lemma F_16150 : fetch_word Ubsan.M.loaded_segments (0x1624c : word) = Some W_16150.
Proof. vm_refl. Qed.
Lemma D_16150 : decode_any W_16150 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16154 : bv 32 := 0x1c061a63.
Lemma F_16154 : fetch_word Ubsan.M.loaded_segments (0x16250 : word) = Some W_16154.
Proof. vm_refl. Qed.
Lemma D_16154 : decode_any W_16154 = Some (Branch BC_NE 12 0 468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16158 : bv 32 := 0x0085a603.
Lemma F_16158 : fetch_word Ubsan.M.loaded_segments (0x16254 : word) = Some W_16158.
Proof. vm_refl. Qed.
Lemma D_16158 : decode_any W_16158 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1615c : bv 32 := 0x00852683.
Lemma F_1615c : fetch_word Ubsan.M.loaded_segments (0x16258 : word) = Some W_1615c.
Proof. vm_refl. Qed.
Lemma D_1615c : decode_any W_1615c = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16160 : bv 32 := 0x10d61e63.
Lemma F_16160 : fetch_word Ubsan.M.loaded_segments (0x1625c : word) = Some W_16160.
Proof. vm_refl. Qed.
Lemma D_16160 : decode_any W_16160 = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16164 : bv 32 := 0x03053603.
Lemma F_16164 : fetch_word Ubsan.M.loaded_segments (0x16260 : word) = Some W_16164.
Proof. vm_refl. Qed.
Lemma D_16164 : decode_any W_16164 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16168 : bv 32 := 0x00c13823.
Lemma F_16168 : fetch_word Ubsan.M.loaded_segments (0x16264 : word) = Some W_16168.
Proof. vm_refl. Qed.
Lemma D_16168 : decode_any W_16168 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1616c : bv 32 := 0x02060063.
Lemma F_1616c : fetch_word Ubsan.M.loaded_segments (0x16268 : word) = Some W_1616c.
Proof. vm_refl. Qed.
Lemma D_1616c : decode_any W_1616c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1618c : bv 32 := 0x0305b403.
Lemma F_1618c : fetch_word Ubsan.M.loaded_segments (0x16288 : word) = Some W_1618c.
Proof. vm_refl. Qed.
Lemma D_1618c : decode_any W_1618c = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16190 : bv 32 := 0x08040a63.
Lemma F_16190 : fetch_word Ubsan.M.loaded_segments (0x1628c : word) = Some W_16190.
Proof. vm_refl. Qed.
Lemma D_16190 : decode_any W_16190 = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16194 : bv 32 := 0x00050493.
Lemma F_16194 : fetch_word Ubsan.M.loaded_segments (0x16290 : word) = Some W_16194.
Proof. vm_refl. Qed.
Lemma D_16194 : decode_any W_16194 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16198 : bv 32 := 0x00c10613.
Lemma F_16198 : fetch_word Ubsan.M.loaded_segments (0x16294 : word) = Some W_16198.
Proof. vm_refl. Qed.
Lemma D_16198 : decode_any W_16198 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1619c : bv 32 := 0x00040513.
Lemma F_1619c : fetch_word Ubsan.M.loaded_segments (0x16298 : word) = Some W_1619c.
Proof. vm_refl. Qed.
Lemma D_1619c : decode_any W_1619c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a0 : bv 32 := 0x00000593.
Lemma F_161a0 : fetch_word Ubsan.M.loaded_segments (0x1629c : word) = Some W_161a0.
Proof. vm_refl. Qed.
Lemma D_161a0 : decode_any W_161a0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a4 : bv 32 := 0x6ac030ef.
Lemma F_161a4 : fetch_word Ubsan.M.loaded_segments (0x162a0 : word) = Some W_161a4.
Proof. vm_refl. Qed.
Lemma D_161a4 : decode_any W_161a4 = Some (Jal 1 13996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161a8 : bv 32 := 0x00c12503.
Lemma F_161a8 : fetch_word Ubsan.M.loaded_segments (0x162a4 : word) = Some W_161a8.
Proof. vm_refl. Qed.
Lemma D_161a8 : decode_any W_161a8 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161ac : bv 32 := 0x10050663.
Lemma F_161ac : fetch_word Ubsan.M.loaded_segments (0x162a8 : word) = Some W_161ac.
Proof. vm_refl. Qed.
Lemma D_161ac : decode_any W_161ac = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b0 : bv 32 := 0x00040513.
Lemma F_161b0 : fetch_word Ubsan.M.loaded_segments (0x162ac : word) = Some W_161b0.
Proof. vm_refl. Qed.
Lemma D_161b0 : decode_any W_161b0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b4 : bv 32 := 0x584030ef.
Lemma F_161b4 : fetch_word Ubsan.M.loaded_segments (0x162b0 : word) = Some W_161b4.
Proof. vm_refl. Qed.
Lemma D_161b4 : decode_any W_161b4 = Some (Jal 1 13700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161b8 : bv 32 := 0x12050463.
Lemma F_161b8 : fetch_word Ubsan.M.loaded_segments (0x162b4 : word) = Some W_161b8.
Proof. vm_refl. Qed.
Lemma D_161b8 : decode_any W_161b8 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161bc : bv 32 := 0x00048593.
Lemma F_161bc : fetch_word Ubsan.M.loaded_segments (0x162b8 : word) = Some W_161bc.
Proof. vm_refl. Qed.
Lemma D_161bc : decode_any W_161bc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161c0 : bv 32 := 0x0304b603.
Lemma F_161c0 : fetch_word Ubsan.M.loaded_segments (0x162bc : word) = Some W_161c0.
Proof. vm_refl. Qed.
Lemma D_161c0 : decode_any W_161c0 = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161c4 : bv 32 := 0x00c13823.
Lemma F_161c4 : fetch_word Ubsan.M.loaded_segments (0x162c0 : word) = Some W_161c4.
Proof. vm_refl. Qed.
Lemma D_161c4 : decode_any W_161c4 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161c8 : bv 32 := 0x00060c63.
Lemma F_161c8 : fetch_word Ubsan.M.loaded_segments (0x162c4 : word) = Some W_161c8.
Proof. vm_refl. Qed.
Lemma D_161c8 : decode_any W_161c8 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161e0 : bv 32 := 0x02a5b823.
Lemma F_161e0 : fetch_word Ubsan.M.loaded_segments (0x162dc : word) = Some W_161e0.
Proof. vm_refl. Qed.
Lemma D_161e0 : decode_any W_161e0 = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161e4 : bv 32 := 0x01010613.
Lemma F_161e4 : fetch_word Ubsan.M.loaded_segments (0x162e0 : word) = Some W_161e4.
Proof. vm_refl. Qed.
Lemma D_161e4 : decode_any W_161e4 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161e8 : bv 32 := 0x00000593.
Lemma F_161e8 : fetch_word Ubsan.M.loaded_segments (0x162e4 : word) = Some W_161e8.
Proof. vm_refl. Qed.
Lemma D_161e8 : decode_any W_161e8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161ec : bv 32 := 0x664030ef.
Lemma F_161ec : fetch_word Ubsan.M.loaded_segments (0x162e8 : word) = Some W_161ec.
Proof. vm_refl. Qed.
Lemma D_161ec : decode_any W_161ec = Some (Jal 1 13924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161f0 : bv 32 := 0x01012503.
Lemma F_161f0 : fetch_word Ubsan.M.loaded_segments (0x162ec : word) = Some W_161f0.
Proof. vm_refl. Qed.
Lemma D_161f0 : decode_any W_161f0 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_161f4 : bv 32 := 0x02051863.
Lemma F_161f4 : fetch_word Ubsan.M.loaded_segments (0x162f0 : word) = Some W_161f4.
Proof. vm_refl. Qed.
Lemma D_161f4 : decode_any W_161f4 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16224 : bv 32 := 0x00000513.
Lemma F_16224 : fetch_word Ubsan.M.loaded_segments (0x16320 : word) = Some W_16224.
Proof. vm_refl. Qed.
Lemma D_16224 : decode_any W_16224 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16228 : bv 32 := 0x0ec0006f.
Lemma F_16228 : fetch_word Ubsan.M.loaded_segments (0x16324 : word) = Some W_16228.
Proof. vm_refl. Qed.
Lemma D_16228 : decode_any W_16228 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_162e0 : bv 32 := 0x0001d517.
Lemma F_162e0 : fetch_word Ubsan.M.loaded_segments (0x163dc : word) = Some W_162e0.
Proof. vm_refl. Qed.
Lemma D_162e0 : decode_any W_162e0 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_162e4 : bv 32 := 0x99453503.
Lemma F_162e4 : fetch_word Ubsan.M.loaded_segments (0x163e0 : word) = Some W_162e4.
Proof. vm_refl. Qed.
Lemma D_162e4 : decode_any W_162e4 = Some (Load SZ8 true 10 10 2452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_162e8 : bv 32 := 0x00052503.
Lemma F_162e8 : fetch_word Ubsan.M.loaded_segments (0x163e4 : word) = Some W_162e8.
Proof. vm_refl. Qed.
Lemma D_162e8 : decode_any W_162e8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_162ec : bv 32 := 0x00500593.
Lemma F_162ec : fetch_word Ubsan.M.loaded_segments (0x163e8 : word) = Some W_162ec.
Proof. vm_refl. Qed.
Lemma D_162ec : decode_any W_162ec = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_162f0 : bv 32 := 0x02a5c063.
Lemma F_162f0 : fetch_word Ubsan.M.loaded_segments (0x163ec : word) = Some W_162f0.
Proof. vm_refl. Qed.
Lemma D_162f0 : decode_any W_162f0 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_162f4 : bv 32 := 0xffffa517.
Lemma F_162f4 : fetch_word Ubsan.M.loaded_segments (0x163f0 : word) = Some W_162f4.
Proof. vm_refl. Qed.
Lemma D_162f4 : decode_any W_162f4 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_162f8 : bv 32 := 0xffffa597.
Lemma F_162f8 : fetch_word Ubsan.M.loaded_segments (0x163f4 : word) = Some W_162f8.
Proof. vm_refl. Qed.
Lemma D_162f8 : decode_any W_162f8 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_162fc : bv 32 := 0x0db50513.
Lemma F_162fc : fetch_word Ubsan.M.loaded_segments (0x163f8 : word) = Some W_162fc.
Proof. vm_refl. Qed.
Lemma D_162fc : decode_any W_162fc = Some (OpImm ALU_ADD 10 10 219, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16300 : bv 32 := 0x19958593.
Lemma F_16300 : fetch_word Ubsan.M.loaded_segments (0x163fc : word) = Some W_16300.
Proof. vm_refl. Qed.
Lemma D_16300 : decode_any W_16300 = Some (OpImm ALU_ADD 11 11 409, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16304 : bv 32 := 0x00100613.
Lemma F_16304 : fetch_word Ubsan.M.loaded_segments (0x16400 : word) = Some W_16304.
Proof. vm_refl. Qed.
Lemma D_16304 : decode_any W_16304 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16308 : bv 32 := 0x878ff0ef.
Lemma F_16308 : fetch_word Ubsan.M.loaded_segments (0x16404 : word) = Some W_16308.
Proof. vm_refl. Qed.
Lemma D_16308 : decode_any W_16308 = Some (Jal 1 2093176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1630c : bv 32 := 0x0080006f.
Lemma F_1630c : fetch_word Ubsan.M.loaded_segments (0x16408 : word) = Some W_1630c.
Proof. vm_refl. Qed.
Lemma D_1630c : decode_any W_1630c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16314 : bv 32 := 0x02813083.
Lemma F_16314 : fetch_word Ubsan.M.loaded_segments (0x16410 : word) = Some W_16314.
Proof. vm_refl. Qed.
Lemma D_16314 : decode_any W_16314 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16318 : bv 32 := 0x02013403.
Lemma F_16318 : fetch_word Ubsan.M.loaded_segments (0x16414 : word) = Some W_16318.
Proof. vm_refl. Qed.
Lemma D_16318 : decode_any W_16318 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1631c : bv 32 := 0x01813483.
Lemma F_1631c : fetch_word Ubsan.M.loaded_segments (0x16418 : word) = Some W_1631c.
Proof. vm_refl. Qed.
Lemma D_1631c : decode_any W_1631c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16320 : bv 32 := 0x03010113.
Lemma F_16320 : fetch_word Ubsan.M.loaded_segments (0x1641c : word) = Some W_16320.
Proof. vm_refl. Qed.
Lemma D_16320 : decode_any W_16320 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16324 : bv 32 := 0x00008067.
Lemma F_16324 : fetch_word Ubsan.M.loaded_segments (0x16420 : word) = Some W_16324.
Proof. vm_refl. Qed.
Lemma D_16324 : decode_any W_16324 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164ac : bv 32 := 0x00050e63.
Lemma F_164ac : fetch_word Ubsan.M.loaded_segments (0x165a8 : word) = Some W_164ac.
Proof. vm_refl. Qed.
Lemma D_164ac : decode_any W_164ac = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164b0 : bv 32 := 0x00757613.
Lemma F_164b0 : fetch_word Ubsan.M.loaded_segments (0x165ac : word) = Some W_164b0.
Proof. vm_refl. Qed.
Lemma D_164b0 : decode_any W_164b0 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164b4 : bv 32 := 0x0405c063.
Lemma F_164b4 : fetch_word Ubsan.M.loaded_segments (0x165b0 : word) = Some W_164b4.
Proof. vm_refl. Qed.
Lemma D_164b4 : decode_any W_164b4 = Some (Branch BC_LT 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164b8 : bv 32 := 0x06061c63.
Lemma F_164b8 : fetch_word Ubsan.M.loaded_segments (0x165b4 : word) = Some W_164b8.
Proof. vm_refl. Qed.
Lemma D_164b8 : decode_any W_164b8 = Some (Branch BC_NE 12 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164bc : bv 32 := 0x00b52023.
Lemma F_164bc : fetch_word Ubsan.M.loaded_segments (0x165b8 : word) = Some W_164bc.
Proof. vm_refl. Qed.
Lemma D_164bc : decode_any W_164bc = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164c0 : bv 32 := 0x00060513.
Lemma F_164c0 : fetch_word Ubsan.M.loaded_segments (0x165bc : word) = Some W_164c0.
Proof. vm_refl. Qed.
Lemma D_164c0 : decode_any W_164c0 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_164c4 : bv 32 := 0x00008067.
Lemma F_164c4 : fetch_word Ubsan.M.loaded_segments (0x165c0 : word) = Some W_164c4.
Proof. vm_refl. Qed.
Lemma D_164c4 : decode_any W_164c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16534 : bv 32 := 0x00050e63.
Lemma F_16534 : fetch_word Ubsan.M.loaded_segments (0x16630 : word) = Some W_16534.
Proof. vm_refl. Qed.
Lemma D_16534 : decode_any W_16534 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16538 : bv 32 := 0x00757613.
Lemma F_16538 : fetch_word Ubsan.M.loaded_segments (0x16634 : word) = Some W_16538.
Proof. vm_refl. Qed.
Lemma D_16538 : decode_any W_16538 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1653c : bv 32 := 0x0405c063.
Lemma F_1653c : fetch_word Ubsan.M.loaded_segments (0x16638 : word) = Some W_1653c.
Proof. vm_refl. Qed.
Lemma D_1653c : decode_any W_1653c = Some (Branch BC_LT 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16540 : bv 32 := 0x06061c63.
Lemma F_16540 : fetch_word Ubsan.M.loaded_segments (0x1663c : word) = Some W_16540.
Proof. vm_refl. Qed.
Lemma D_16540 : decode_any W_16540 = Some (Branch BC_NE 12 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16544 : bv 32 := 0x00b52223.
Lemma F_16544 : fetch_word Ubsan.M.loaded_segments (0x16640 : word) = Some W_16544.
Proof. vm_refl. Qed.
Lemma D_16544 : decode_any W_16544 = Some (Store SZ4 10 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16548 : bv 32 := 0x00060513.
Lemma F_16548 : fetch_word Ubsan.M.loaded_segments (0x16644 : word) = Some W_16548.
Proof. vm_refl. Qed.
Lemma D_16548 : decode_any W_16548 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1654c : bv 32 := 0x00008067.
Lemma F_1654c : fetch_word Ubsan.M.loaded_segments (0x16648 : word) = Some W_1654c.
Proof. vm_refl. Qed.
Lemma D_1654c : decode_any W_1654c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165bc : bv 32 := 0x00050e63.
Lemma F_165bc : fetch_word Ubsan.M.loaded_segments (0x166b8 : word) = Some W_165bc.
Proof. vm_refl. Qed.
Lemma D_165bc : decode_any W_165bc = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165c0 : bv 32 := 0x04b05263.
Lemma F_165c0 : fetch_word Ubsan.M.loaded_segments (0x166bc : word) = Some W_165c0.
Proof. vm_refl. Qed.
Lemma D_165c0 : decode_any W_165c0 = Some (Branch BC_GE 0 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165c4 : bv 32 := 0x00757613.
Lemma F_165c4 : fetch_word Ubsan.M.loaded_segments (0x166c0 : word) = Some W_165c4.
Proof. vm_refl. Qed.
Lemma D_165c4 : decode_any W_165c4 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165c8 : bv 32 := 0x06061863.
Lemma F_165c8 : fetch_word Ubsan.M.loaded_segments (0x166c4 : word) = Some W_165c8.
Proof. vm_refl. Qed.
Lemma D_165c8 : decode_any W_165c8 = Some (Branch BC_NE 12 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165cc : bv 32 := 0x00b52423.
Lemma F_165cc : fetch_word Ubsan.M.loaded_segments (0x166c8 : word) = Some W_165cc.
Proof. vm_refl. Qed.
Lemma D_165cc : decode_any W_165cc = Some (Store SZ4 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165d0 : bv 32 := 0x00060513.
Lemma F_165d0 : fetch_word Ubsan.M.loaded_segments (0x166cc : word) = Some W_165d0.
Proof. vm_refl. Qed.
Lemma D_165d0 : decode_any W_165d0 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165d4 : bv 32 := 0x00008067.
Lemma F_165d4 : fetch_word Ubsan.M.loaded_segments (0x166d0 : word) = Some W_165d4.
Proof. vm_refl. Qed.
Lemma D_165d4 : decode_any W_165d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16710 : bv 32 := 0xfd010113.
Lemma F_16710 : fetch_word Ubsan.M.loaded_segments (0x1680c : word) = Some W_16710.
Proof. vm_refl. Qed.
Lemma D_16710 : decode_any W_16710 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16714 : bv 32 := 0x02113423.
Lemma F_16714 : fetch_word Ubsan.M.loaded_segments (0x16810 : word) = Some W_16714.
Proof. vm_refl. Qed.
Lemma D_16714 : decode_any W_16714 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16718 : bv 32 := 0x02813023.
Lemma F_16718 : fetch_word Ubsan.M.loaded_segments (0x16814 : word) = Some W_16718.
Proof. vm_refl. Qed.
Lemma D_16718 : decode_any W_16718 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1671c : bv 32 := 0x00913c23.
Lemma F_1671c : fetch_word Ubsan.M.loaded_segments (0x16818 : word) = Some W_1671c.
Proof. vm_refl. Qed.
Lemma D_1671c : decode_any W_1671c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16720 : bv 32 := 0x01213823.
Lemma F_16720 : fetch_word Ubsan.M.loaded_segments (0x1681c : word) = Some W_16720.
Proof. vm_refl. Qed.
Lemma D_16720 : decode_any W_16720 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16724 : bv 32 := 0x01313423.
Lemma F_16724 : fetch_word Ubsan.M.loaded_segments (0x16820 : word) = Some W_16724.
Proof. vm_refl. Qed.
Lemma D_16724 : decode_any W_16724 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16728 : bv 32 := 0x00050413.
Lemma F_16728 : fetch_word Ubsan.M.loaded_segments (0x16824 : word) = Some W_16728.
Proof. vm_refl. Qed.
Lemma D_16728 : decode_any W_16728 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1672c : bv 32 := 0x08058063.
Lemma F_1672c : fetch_word Ubsan.M.loaded_segments (0x16828 : word) = Some W_1672c.
Proof. vm_refl. Qed.
Lemma D_1672c : decode_any W_1672c = Some (Branch BC_EQ 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16730 : bv 32 := 0x00058493.
Lemma F_16730 : fetch_word Ubsan.M.loaded_segments (0x1682c : word) = Some W_16730.
Proof. vm_refl. Qed.
Lemma D_16730 : decode_any W_16730 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16734 : bv 32 := 0x1e858e63.
Lemma F_16734 : fetch_word Ubsan.M.loaded_segments (0x16830 : word) = Some W_16734.
Proof. vm_refl. Qed.
Lemma D_16734 : decode_any W_16734 = Some (Branch BC_EQ 11 8 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16738 : bv 32 := 0x0074f513.
Lemma F_16738 : fetch_word Ubsan.M.loaded_segments (0x16834 : word) = Some W_16738.
Proof. vm_refl. Qed.
Lemma D_16738 : decode_any W_16738 = Some (OpImm ALU_AND 10 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1673c : bv 32 := 0x20051a63.
Lemma F_1673c : fetch_word Ubsan.M.loaded_segments (0x16838 : word) = Some W_1673c.
Proof. vm_refl. Qed.
Lemma D_1673c : decode_any W_1673c = Some (Branch BC_NE 10 0 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16740 : bv 32 := 0x0104a503.
Lemma F_16740 : fetch_word Ubsan.M.loaded_segments (0x1683c : word) = Some W_16740.
Proof. vm_refl. Qed.
Lemma D_16740 : decode_any W_16740 = Some (Load SZ4 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16744 : bv 32 := 0x200005b7.
Lemma F_16744 : fetch_word Ubsan.M.loaded_segments (0x16840 : word) = Some W_16744.
Proof. vm_refl. Qed.
Lemma D_16744 : decode_any W_16744 = Some (Lui 11 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16748 : bv 32 := 0x00b505b3.
Lemma F_16748 : fetch_word Ubsan.M.loaded_segments (0x16844 : word) = Some W_16748.
Proof. vm_refl. Qed.
Lemma D_16748 : decode_any W_16748 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1674c : bv 32 := 0x01e5d59b.
Lemma F_1674c : fetch_word Ubsan.M.loaded_segments (0x16848 : word) = Some W_1674c.
Proof. vm_refl. Qed.
Lemma D_1674c : decode_any W_1674c = Some (ShiftImm32 ALU_SRL 11 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16750 : bv 32 := 0x20059063.
Lemma F_16750 : fetch_word Ubsan.M.loaded_segments (0x1684c : word) = Some W_16750.
Proof. vm_refl. Qed.
Lemma D_16750 : decode_any W_16750 = Some (Branch BC_NE 11 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16754 : bv 32 := 0x0044a583.
Lemma F_16754 : fetch_word Ubsan.M.loaded_segments (0x16850 : word) = Some W_16754.
Proof. vm_refl. Qed.
Lemma D_16754 : decode_any W_16754 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16758 : bv 32 := 0x0025151b.
Lemma F_16758 : fetch_word Ubsan.M.loaded_segments (0x16854 : word) = Some W_16758.
Proof. vm_refl. Qed.
Lemma D_16758 : decode_any W_16758 = Some (ShiftImm32 ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1675c : bv 32 := 0x02b50933.
Lemma F_1675c : fetch_word Ubsan.M.loaded_segments (0x16858 : word) = Some W_1675c.
Proof. vm_refl. Qed.
Lemma D_1675c : decode_any W_1675c = Some (Mul M_MUL 18 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16760 : bv 32 := 0x02b5053b.
Lemma F_16760 : fetch_word Ubsan.M.loaded_segments (0x1685c : word) = Some W_16760.
Proof. vm_refl. Qed.
Lemma D_16760 : decode_any W_16760 = Some (Mul32 M_MUL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16764 : bv 32 := 0x1f251663.
Lemma F_16764 : fetch_word Ubsan.M.loaded_segments (0x16860 : word) = Some W_16764.
Proof. vm_refl. Qed.
Lemma D_16764 : decode_any W_16764 = Some (Branch BC_NE 10 18 492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16768 : bv 32 := 0x08040463.
Lemma F_16768 : fetch_word Ubsan.M.loaded_segments (0x16864 : word) = Some W_16768.
Proof. vm_refl. Qed.
Lemma D_16768 : decode_any W_16768 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167a4 : bv 32 := 0x00000613.
Lemma F_167a4 : fetch_word Ubsan.M.loaded_segments (0x168a0 : word) = Some W_167a4.
Proof. vm_refl. Qed.
Lemma D_167a4 : decode_any W_167a4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167a8 : bv 32 := 0x02c0006f.
Lemma F_167a8 : fetch_word Ubsan.M.loaded_segments (0x168a4 : word) = Some W_167a8.
Proof. vm_refl. Qed.
Lemma D_167a8 : decode_any W_167a8 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167d4 : bv 32 := 0x02813083.
Lemma F_167d4 : fetch_word Ubsan.M.loaded_segments (0x168d0 : word) = Some W_167d4.
Proof. vm_refl. Qed.
Lemma D_167d4 : decode_any W_167d4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167d8 : bv 32 := 0x02013403.
Lemma F_167d8 : fetch_word Ubsan.M.loaded_segments (0x168d4 : word) = Some W_167d8.
Proof. vm_refl. Qed.
Lemma D_167d8 : decode_any W_167d8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167dc : bv 32 := 0x01813483.
Lemma F_167dc : fetch_word Ubsan.M.loaded_segments (0x168d8 : word) = Some W_167dc.
Proof. vm_refl. Qed.
Lemma D_167dc : decode_any W_167dc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167e0 : bv 32 := 0x01013903.
Lemma F_167e0 : fetch_word Ubsan.M.loaded_segments (0x168dc : word) = Some W_167e0.
Proof. vm_refl. Qed.
Lemma D_167e0 : decode_any W_167e0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167e4 : bv 32 := 0x00813983.
Lemma F_167e4 : fetch_word Ubsan.M.loaded_segments (0x168e0 : word) = Some W_167e4.
Proof. vm_refl. Qed.
Lemma D_167e4 : decode_any W_167e4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167e8 : bv 32 := 0x03010113.
Lemma F_167e8 : fetch_word Ubsan.M.loaded_segments (0x168e4 : word) = Some W_167e8.
Proof. vm_refl. Qed.
Lemma D_167e8 : decode_any W_167e8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167ec : bv 32 := 0xc65fe06f.
Lemma F_167ec : fetch_word Ubsan.M.loaded_segments (0x168e8 : word) = Some W_167ec.
Proof. vm_refl. Qed.
Lemma D_167ec : decode_any W_167ec = Some (Jal 0 2092132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167f0 : bv 32 := 0x00048513.
Lemma F_167f0 : fetch_word Ubsan.M.loaded_segments (0x168ec : word) = Some W_167f0.
Proof. vm_refl. Qed.
Lemma D_167f0 : decode_any W_167f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167f4 : bv 32 := 0xdb4ff0ef.
Lemma F_167f4 : fetch_word Ubsan.M.loaded_segments (0x168f0 : word) = Some W_167f4.
Proof. vm_refl. Qed.
Lemma D_167f4 : decode_any W_167f4 = Some (Jal 1 2094516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167f8 : bv 32 := 0x06050463.
Lemma F_167f8 : fetch_word Ubsan.M.loaded_segments (0x168f4 : word) = Some W_167f8.
Proof. vm_refl. Qed.
Lemma D_167f8 : decode_any W_167f8 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167fc : bv 32 := 0x00050413.
Lemma F_167fc : fetch_word Ubsan.M.loaded_segments (0x168f8 : word) = Some W_167fc.
Proof. vm_refl. Qed.
Lemma D_167fc : decode_any W_167fc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16800 : bv 32 := 0x00757513.
Lemma F_16800 : fetch_word Ubsan.M.loaded_segments (0x168fc : word) = Some W_16800.
Proof. vm_refl. Qed.
Lemma D_16800 : decode_any W_16800 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16804 : bv 32 := 0x14051663.
Lemma F_16804 : fetch_word Ubsan.M.loaded_segments (0x16900 : word) = Some W_16804.
Proof. vm_refl. Qed.
Lemma D_16804 : decode_any W_16804 = Some (Branch BC_NE 10 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16808 : bv 32 := 0x01046503.
Lemma F_16808 : fetch_word Ubsan.M.loaded_segments (0x16904 : word) = Some W_16808.
Proof. vm_refl. Qed.
Lemma D_16808 : decode_any W_16808 = Some (Load SZ4 false 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1680c : bv 32 := 0x00446583.
Lemma F_1680c : fetch_word Ubsan.M.loaded_segments (0x16908 : word) = Some W_1680c.
Proof. vm_refl. Qed.
Lemma D_1680c : decode_any W_1680c = Some (Load SZ4 false 11 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16810 : bv 32 := 0x00251513.
Lemma F_16810 : fetch_word Ubsan.M.loaded_segments (0x1690c : word) = Some W_16810.
Proof. vm_refl. Qed.
Lemma D_16810 : decode_any W_16810 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16814 : bv 32 := 0x02b516b3.
Lemma F_16814 : fetch_word Ubsan.M.loaded_segments (0x16910 : word) = Some W_16814.
Proof. vm_refl. Qed.
Lemma D_16814 : decode_any W_16814 = Some (Mul M_MULH 13 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16818 : bv 32 := 0x02b50633.
Lemma F_16818 : fetch_word Ubsan.M.loaded_segments (0x16914 : word) = Some W_16818.
Proof. vm_refl. Qed.
Lemma D_16818 : decode_any W_16818 = Some (Mul M_MUL 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1681c : bv 32 := 0x43f65513.
Lemma F_1681c : fetch_word Ubsan.M.loaded_segments (0x16918 : word) = Some W_1681c.
Proof. vm_refl. Qed.
Lemma D_1681c : decode_any W_1681c = Some (ShiftImm ALU_SRA 10 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16820 : bv 32 := 0x12a69863.
Lemma F_16820 : fetch_word Ubsan.M.loaded_segments (0x1691c : word) = Some W_16820.
Proof. vm_refl. Qed.
Lemma D_16820 : decode_any W_16820 = Some (Branch BC_NE 13 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16824 : bv 32 := 0x03843503.
Lemma F_16824 : fetch_word Ubsan.M.loaded_segments (0x16920 : word) = Some W_16824.
Proof. vm_refl. Qed.
Lemma D_16824 : decode_any W_16824 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16828 : bv 32 := 0x00000593.
Lemma F_16828 : fetch_word Ubsan.M.loaded_segments (0x16924 : word) = Some W_16828.
Proof. vm_refl. Qed.
Lemma D_16828 : decode_any W_16828 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1682c : bv 32 := 0x6311a0ef.
Lemma F_1682c : fetch_word Ubsan.M.loaded_segments (0x16928 : word) = Some W_1682c.
Proof. vm_refl. Qed.
Lemma D_1682c : decode_any W_1682c = Some (Jal 1 110128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16830 : bv 32 := 0x00747513.
Lemma F_16830 : fetch_word Ubsan.M.loaded_segments (0x1692c : word) = Some W_16830.
Proof. vm_refl. Qed.
Lemma D_16830 : decode_any W_16830 = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16834 : bv 32 := 0x0a050c63.
Lemma F_16834 : fetch_word Ubsan.M.loaded_segments (0x16930 : word) = Some W_16834.
Proof. vm_refl. Qed.
Lemma D_16834 : decode_any W_16834 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16860 : bv 32 := 0x0001c517.
Lemma F_16860 : fetch_word Ubsan.M.loaded_segments (0x1695c : word) = Some W_16860.
Proof. vm_refl. Qed.
Lemma D_16860 : decode_any W_16860 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16864 : bv 32 := 0x41453983.
Lemma F_16864 : fetch_word Ubsan.M.loaded_segments (0x16960 : word) = Some W_16864.
Proof. vm_refl. Qed.
Lemma D_16864 : decode_any W_16864 = Some (Load SZ8 true 19 10 1044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16868 : bv 32 := 0x0009a503.
Lemma F_16868 : fetch_word Ubsan.M.loaded_segments (0x16964 : word) = Some W_16868.
Proof. vm_refl. Qed.
Lemma D_16868 : decode_any W_16868 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1686c : bv 32 := 0x00600593.
Lemma F_1686c : fetch_word Ubsan.M.loaded_segments (0x16968 : word) = Some W_1686c.
Proof. vm_refl. Qed.
Lemma D_1686c : decode_any W_1686c = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16870 : bv 32 := 0x0ab55e63.
Lemma F_16870 : fetch_word Ubsan.M.loaded_segments (0x1696c : word) = Some W_16870.
Proof. vm_refl. Qed.
Lemma D_16870 : decode_any W_16870 = Some (Branch BC_GE 10 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16874 : bv 32 := 0xffffa517.
Lemma F_16874 : fetch_word Ubsan.M.loaded_segments (0x16970 : word) = Some W_16874.
Proof. vm_refl. Qed.
Lemma D_16874 : decode_any W_16874 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16878 : bv 32 := 0xffffa597.
Lemma F_16878 : fetch_word Ubsan.M.loaded_segments (0x16974 : word) = Some W_16878.
Proof. vm_refl. Qed.
Lemma D_16878 : decode_any W_16878 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1687c : bv 32 := 0xb4d50513.
Lemma F_1687c : fetch_word Ubsan.M.loaded_segments (0x16978 : word) = Some W_1687c.
Proof. vm_refl. Qed.
Lemma D_1687c : decode_any W_1687c = Some (OpImm ALU_ADD 10 10 2893, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16880 : bv 32 := 0x43058593.
Lemma F_16880 : fetch_word Ubsan.M.loaded_segments (0x1697c : word) = Some W_16880.
Proof. vm_refl. Qed.
Lemma D_16880 : decode_any W_16880 = Some (OpImm ALU_ADD 11 11 1072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16884 : bv 32 := 0x00000613.
Lemma F_16884 : fetch_word Ubsan.M.loaded_segments (0x16980 : word) = Some W_16884.
Proof. vm_refl. Qed.
Lemma D_16884 : decode_any W_16884 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16888 : bv 32 := 0xbc9fe0ef.
Lemma F_16888 : fetch_word Ubsan.M.loaded_segments (0x16984 : word) = Some W_16888.
Proof. vm_refl. Qed.
Lemma D_16888 : decode_any W_16888 = Some (Jal 1 2091976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1688c : bv 32 := 0x08050063.
Lemma F_1688c : fetch_word Ubsan.M.loaded_segments (0x16988 : word) = Some W_1688c.
Proof. vm_refl. Qed.
Lemma D_1688c : decode_any W_1688c = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168ec : bv 32 := 0x03843503.
Lemma F_168ec : fetch_word Ubsan.M.loaded_segments (0x169e8 : word) = Some W_168ec.
Proof. vm_refl. Qed.
Lemma D_168ec : decode_any W_168ec = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168f0 : bv 32 := 0x0384b583.
Lemma F_168f0 : fetch_word Ubsan.M.loaded_segments (0x169ec : word) = Some W_168f0.
Proof. vm_refl. Qed.
Lemma D_168f0 : decode_any W_168f0 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168f4 : bv 32 := 0x00b56633.
Lemma F_168f4 : fetch_word Ubsan.M.loaded_segments (0x169f0 : word) = Some W_168f4.
Proof. vm_refl. Qed.
Lemma D_168f4 : decode_any W_168f4 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168f8 : bv 32 := 0x00367613.
Lemma F_168f8 : fetch_word Ubsan.M.loaded_segments (0x169f4 : word) = Some W_168f8.
Proof. vm_refl. Qed.
Lemma D_168f8 : decode_any W_168f8 = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_168fc : bv 32 := 0x04061a63.
Lemma F_168fc : fetch_word Ubsan.M.loaded_segments (0x169f8 : word) = Some W_168fc.
Proof. vm_refl. Qed.
Lemma D_168fc : decode_any W_168fc = Some (Branch BC_NE 12 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16900 : bv 32 := 0x0009061b.
Lemma F_16900 : fetch_word Ubsan.M.loaded_segments (0x169fc : word) = Some W_16900.
Proof. vm_refl. Qed.
Lemma D_16900 : decode_any W_16900 = Some (OpImm32 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16904 : bv 32 := 0x1551a0ef.
Lemma F_16904 : fetch_word Ubsan.M.loaded_segments (0x16a00 : word) = Some W_16904.
Proof. vm_refl. Qed.
Lemma D_16904 : decode_any W_16904 = Some (Jal 1 108884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16908 : bv 32 := 0x0280006f.
Lemma F_16908 : fetch_word Ubsan.M.loaded_segments (0x16a04 : word) = Some W_16908.
Proof. vm_refl. Qed.
Lemma D_16908 : decode_any W_16908 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1690c : bv 32 := 0x0009a503.
Lemma F_1690c : fetch_word Ubsan.M.loaded_segments (0x16a08 : word) = Some W_1690c.
Proof. vm_refl. Qed.
Lemma D_1690c : decode_any W_1690c = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16910 : bv 32 := 0x00500593.
Lemma F_16910 : fetch_word Ubsan.M.loaded_segments (0x16a0c : word) = Some W_16910.
Proof. vm_refl. Qed.
Lemma D_16910 : decode_any W_16910 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16914 : bv 32 := 0x00a5cc63.
Lemma F_16914 : fetch_word Ubsan.M.loaded_segments (0x16a10 : word) = Some W_16914.
Proof. vm_refl. Qed.
Lemma D_16914 : decode_any W_16914 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16918 : bv 32 := 0xffffa517.
Lemma F_16918 : fetch_word Ubsan.M.loaded_segments (0x16a14 : word) = Some W_16918.
Proof. vm_refl. Qed.
Lemma D_16918 : decode_any W_16918 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1691c : bv 32 := 0xffffa597.
Lemma F_1691c : fetch_word Ubsan.M.loaded_segments (0x16a18 : word) = Some W_1691c.
Proof. vm_refl. Qed.
Lemma D_1691c : decode_any W_1691c = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16920 : bv 32 := 0xaa950513.
Lemma F_16920 : fetch_word Ubsan.M.loaded_segments (0x16a1c : word) = Some W_16920.
Proof. vm_refl. Qed.
Lemma D_16920 : decode_any W_16920 = Some (OpImm ALU_ADD 10 10 2729, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16924 : bv 32 := 0x34958593.
Lemma F_16924 : fetch_word Ubsan.M.loaded_segments (0x16a20 : word) = Some W_16924.
Proof. vm_refl. Qed.
Lemma D_16924 : decode_any W_16924 = Some (OpImm ALU_ADD 11 11 841, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16928 : bv 32 := 0xe7dff06f.
Lemma F_16928 : fetch_word Ubsan.M.loaded_segments (0x16a24 : word) = Some W_16928.
Proof. vm_refl. Qed.
Lemma D_16928 : decode_any W_16928 = Some (Jal 0 2096764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16930 : bv 32 := 0x00040513.
Lemma F_16930 : fetch_word Ubsan.M.loaded_segments (0x16a2c : word) = Some W_16930.
Proof. vm_refl. Qed.
Lemma D_16930 : decode_any W_16930 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16934 : bv 32 := 0x02813083.
Lemma F_16934 : fetch_word Ubsan.M.loaded_segments (0x16a30 : word) = Some W_16934.
Proof. vm_refl. Qed.
Lemma D_16934 : decode_any W_16934 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16938 : bv 32 := 0x02013403.
Lemma F_16938 : fetch_word Ubsan.M.loaded_segments (0x16a34 : word) = Some W_16938.
Proof. vm_refl. Qed.
Lemma D_16938 : decode_any W_16938 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1693c : bv 32 := 0x01813483.
Lemma F_1693c : fetch_word Ubsan.M.loaded_segments (0x16a38 : word) = Some W_1693c.
Proof. vm_refl. Qed.
Lemma D_1693c : decode_any W_1693c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16940 : bv 32 := 0x01013903.
Lemma F_16940 : fetch_word Ubsan.M.loaded_segments (0x16a3c : word) = Some W_16940.
Proof. vm_refl. Qed.
Lemma D_16940 : decode_any W_16940 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16944 : bv 32 := 0x00813983.
Lemma F_16944 : fetch_word Ubsan.M.loaded_segments (0x16a40 : word) = Some W_16944.
Proof. vm_refl. Qed.
Lemma D_16944 : decode_any W_16944 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16948 : bv 32 := 0x03010113.
Lemma F_16948 : fetch_word Ubsan.M.loaded_segments (0x16a44 : word) = Some W_16948.
Proof. vm_refl. Qed.
Lemma D_16948 : decode_any W_16948 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1694c : bv 32 := 0x00008067.
Lemma F_1694c : fetch_word Ubsan.M.loaded_segments (0x16a48 : word) = Some W_1694c.
Proof. vm_refl. Qed.
Lemma D_1694c : decode_any W_1694c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d18 : bv 32 := 0x00050a63.
Lemma F_16d18 : fetch_word Ubsan.M.loaded_segments (0x16e14 : word) = Some W_16d18.
Proof. vm_refl. Qed.
Lemma D_16d18 : decode_any W_16d18 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d1c : bv 32 := 0x00757593.
Lemma F_16d1c : fetch_word Ubsan.M.loaded_segments (0x16e18 : word) = Some W_16d1c.
Proof. vm_refl. Qed.
Lemma D_16d1c : decode_any W_16d1c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d20 : bv 32 := 0x04059063.
Lemma F_16d20 : fetch_word Ubsan.M.loaded_segments (0x16e1c : word) = Some W_16d20.
Proof. vm_refl. Qed.
Lemma D_16d20 : decode_any W_16d20 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d24 : bv 32 := 0x03853503.
Lemma F_16d24 : fetch_word Ubsan.M.loaded_segments (0x16e20 : word) = Some W_16d24.
Proof. vm_refl. Qed.
Lemma D_16d24 : decode_any W_16d24 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d28 : bv 32 := 0x00008067.
Lemma F_16d28 : fetch_word Ubsan.M.loaded_segments (0x16e24 : word) = Some W_16d28.
Proof. vm_refl. Qed.
Lemma D_16d28 : decode_any W_16d28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
