(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9713c : bv 32 := 0xf4010113.
Lemma F_9713c : fetch_word Ubsan.M.loaded_segments (0x9713c : word) = Some W_9713c.
Proof. vm_refl. Qed.
Lemma D_9713c : decode_any W_9713c = Some (OpImm ALU_ADD 2 2 3904, 4%Z).
Proof. vm_refl. Qed.

Definition W_97140 : bv 32 := 0x0a113c23.
Lemma F_97140 : fetch_word Ubsan.M.loaded_segments (0x97140 : word) = Some W_97140.
Proof. vm_refl. Qed.
Lemma D_97140 : decode_any W_97140 = Some (Store SZ8 2 1 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_97144 : bv 32 := 0x0a813823.
Lemma F_97144 : fetch_word Ubsan.M.loaded_segments (0x97144 : word) = Some W_97144.
Proof. vm_refl. Qed.
Lemma D_97144 : decode_any W_97144 = Some (Store SZ8 2 8 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_97148 : bv 32 := 0x0a913423.
Lemma F_97148 : fetch_word Ubsan.M.loaded_segments (0x97148 : word) = Some W_97148.
Proof. vm_refl. Qed.
Lemma D_97148 : decode_any W_97148 = Some (Store SZ8 2 9 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_9714c : bv 32 := 0x0b213023.
Lemma F_9714c : fetch_word Ubsan.M.loaded_segments (0x9714c : word) = Some W_9714c.
Proof. vm_refl. Qed.
Lemma D_9714c : decode_any W_9714c = Some (Store SZ8 2 18 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_97150 : bv 32 := 0x09313c23.
Lemma F_97150 : fetch_word Ubsan.M.loaded_segments (0x97150 : word) = Some W_97150.
Proof. vm_refl. Qed.
Lemma D_97150 : decode_any W_97150 = Some (Store SZ8 2 19 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_97154 : bv 32 := 0x09413823.
Lemma F_97154 : fetch_word Ubsan.M.loaded_segments (0x97154 : word) = Some W_97154.
Proof. vm_refl. Qed.
Lemma D_97154 : decode_any W_97154 = Some (Store SZ8 2 20 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_97158 : bv 32 := 0x09513423.
Lemma F_97158 : fetch_word Ubsan.M.loaded_segments (0x97158 : word) = Some W_97158.
Proof. vm_refl. Qed.
Lemma D_97158 : decode_any W_97158 = Some (Store SZ8 2 21 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9715c : bv 32 := 0x09613023.
Lemma F_9715c : fetch_word Ubsan.M.loaded_segments (0x9715c : word) = Some W_9715c.
Proof. vm_refl. Qed.
Lemma D_9715c : decode_any W_9715c = Some (Store SZ8 2 22 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_97160 : bv 32 := 0x07713c23.
Lemma F_97160 : fetch_word Ubsan.M.loaded_segments (0x97160 : word) = Some W_97160.
Proof. vm_refl. Qed.
Lemma D_97160 : decode_any W_97160 = Some (Store SZ8 2 23 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_97164 : bv 32 := 0x07813823.
Lemma F_97164 : fetch_word Ubsan.M.loaded_segments (0x97164 : word) = Some W_97164.
Proof. vm_refl. Qed.
Lemma D_97164 : decode_any W_97164 = Some (Store SZ8 2 24 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_97168 : bv 32 := 0x07913423.
Lemma F_97168 : fetch_word Ubsan.M.loaded_segments (0x97168 : word) = Some W_97168.
Proof. vm_refl. Qed.
Lemma D_97168 : decode_any W_97168 = Some (Store SZ8 2 25 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_9716c : bv 32 := 0x07a13023.
Lemma F_9716c : fetch_word Ubsan.M.loaded_segments (0x9716c : word) = Some W_9716c.
Proof. vm_refl. Qed.
Lemma D_9716c : decode_any W_9716c = Some (Store SZ8 2 26 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_97170 : bv 32 := 0x05b13c23.
Lemma F_97170 : fetch_word Ubsan.M.loaded_segments (0x97170 : word) = Some W_97170.
Proof. vm_refl. Qed.
Lemma D_97170 : decode_any W_97170 = Some (Store SZ8 2 27 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_97174 : bv 32 := 0x14050863.
Lemma F_97174 : fetch_word Ubsan.M.loaded_segments (0x97174 : word) = Some W_97174.
Proof. vm_refl. Qed.
Lemma D_97174 : decode_any W_97174 = Some (Branch BC_EQ 10 0 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_97178 : bv 32 := 0x00058993.
Lemma F_97178 : fetch_word Ubsan.M.loaded_segments (0x97178 : word) = Some W_97178.
Proof. vm_refl. Qed.
Lemma D_97178 : decode_any W_97178 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9717c : bv 32 := 0x05010593.
Lemma F_9717c : fetch_word Ubsan.M.loaded_segments (0x9717c : word) = Some W_9717c.
Proof. vm_refl. Qed.
Lemma D_9717c : decode_any W_9717c = Some (OpImm ALU_ADD 11 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_97180 : bv 32 := 0x05410613.
Lemma F_97180 : fetch_word Ubsan.M.loaded_segments (0x97180 : word) = Some W_97180.
Proof. vm_refl. Qed.
Lemma D_97180 : decode_any W_97180 = Some (OpImm ALU_ADD 12 2 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_97184 : bv 32 := 0x04c10693.
Lemma F_97184 : fetch_word Ubsan.M.loaded_segments (0x97184 : word) = Some W_97184.
Proof. vm_refl. Qed.
Lemma D_97184 : decode_any W_97184 = Some (OpImm ALU_ADD 13 2 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_97188 : bv 32 := 0x00050493.
Lemma F_97188 : fetch_word Ubsan.M.loaded_segments (0x97188 : word) = Some W_97188.
Proof. vm_refl. Qed.
Lemma D_97188 : decode_any W_97188 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9718c : bv 32 := 0x918d70ef.
Lemma F_9718c : fetch_word Ubsan.M.loaded_segments (0x9718c : word) = Some W_9718c.
Proof. vm_refl. Qed.
Lemma D_9718c : decode_any W_9718c = Some (Jal 1 1929496, 4%Z).
Proof. vm_refl. Qed.

Definition W_97190 : bv 32 := 0x04c12603.
Lemma F_97190 : fetch_word Ubsan.M.loaded_segments (0x97190 : word) = Some W_97190.
Proof. vm_refl. Qed.
Lemma D_97190 : decode_any W_97190 = Some (Load SZ4 true 12 2 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_97194 : bv 32 := 0x02000513.
Lemma F_97194 : fetch_word Ubsan.M.loaded_segments (0x97194 : word) = Some W_97194.
Proof. vm_refl. Qed.
Lemma D_97194 : decode_any W_97194 = Some (OpImm ALU_ADD 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_97198 : bv 32 := 0x08c566e3.
Lemma F_97198 : fetch_word Ubsan.M.loaded_segments (0x97198 : word) = Some W_97198.
Proof. vm_refl. Qed.
Lemma D_97198 : decode_any W_97198 = Some (Branch BC_LTU 10 12 2188, 4%Z).
Proof. vm_refl. Qed.

Definition W_9719c : bv 32 := 0x10001537.
Lemma F_9719c : fetch_word Ubsan.M.loaded_segments (0x9719c : word) = Some W_9719c.
Proof. vm_refl. Qed.
Lemma D_9719c : decode_any W_9719c = Some (Lui 10 65537, 4%Z).
Proof. vm_refl. Qed.

Definition W_971a0 : bv 32 := 0x00451513.
Lemma F_971a0 : fetch_word Ubsan.M.loaded_segments (0x971a0 : word) = Some W_971a0.
Proof. vm_refl. Qed.
Lemma D_971a0 : decode_any W_971a0 = Some (ShiftImm ALU_SLL 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_971a4 : bv 32 := 0x11650513.
Lemma F_971a4 : fetch_word Ubsan.M.loaded_segments (0x971a4 : word) = Some W_971a4.
Proof. vm_refl. Qed.
Lemma D_971a4 : decode_any W_971a4 = Some (OpImm ALU_ADD 10 10 278, 4%Z).
Proof. vm_refl. Qed.

Definition W_971a8 : bv 32 := 0x00c55533.
Lemma F_971a8 : fetch_word Ubsan.M.loaded_segments (0x971a8 : word) = Some W_971a8.
Proof. vm_refl. Qed.
Lemma D_971a8 : decode_any W_971a8 = Some (Op ALU_SRL 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_971ac : bv 32 := 0x00157513.
Lemma F_971ac : fetch_word Ubsan.M.loaded_segments (0x971ac : word) = Some W_971ac.
Proof. vm_refl. Qed.
Lemma D_971ac : decode_any W_971ac = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_971b0 : bv 32 := 0x06050ae3.
Lemma F_971b0 : fetch_word Ubsan.M.loaded_segments (0x971b0 : word) = Some W_971b0.
Proof. vm_refl. Qed.
Lemma D_971b0 : decode_any W_971b0 = Some (Branch BC_EQ 10 0 2164, 4%Z).
Proof. vm_refl. Qed.

Definition W_971b4 : bv 32 := 0xfff00513.
Lemma F_971b4 : fetch_word Ubsan.M.loaded_segments (0x971b4 : word) = Some W_971b4.
Proof. vm_refl. Qed.
Lemma D_971b4 : decode_any W_971b4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_971b8 : bv 32 := 0x00a98663.
Lemma F_971b8 : fetch_word Ubsan.M.loaded_segments (0x971b8 : word) = Some W_971b8.
Proof. vm_refl. Qed.
Lemma D_971b8 : decode_any W_971b8 = Some (Branch BC_EQ 19 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_971bc : bv 32 := 0x00100513.
Lemma F_971bc : fetch_word Ubsan.M.loaded_segments (0x971bc : word) = Some W_971bc.
Proof. vm_refl. Qed.
Lemma D_971bc : decode_any W_971bc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_971c0 : bv 32 := 0x40a99c63.
Lemma F_971c0 : fetch_word Ubsan.M.loaded_segments (0x971c0 : word) = Some W_971c0.
Proof. vm_refl. Qed.
Lemma D_971c0 : decode_any W_971c0 = Some (Branch BC_NE 19 10 1048, 4%Z).
Proof. vm_refl. Qed.

Definition W_971c4 : bv 32 := 0x05412503.
Lemma F_971c4 : fetch_word Ubsan.M.loaded_segments (0x971c4 : word) = Some W_971c4.
Proof. vm_refl. Qed.
Lemma D_971c4 : decode_any W_971c4 = Some (Load SZ4 true 10 2 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_971c8 : bv 32 := 0x05012583.
Lemma F_971c8 : fetch_word Ubsan.M.loaded_segments (0x971c8 : word) = Some W_971c8.
Proof. vm_refl. Qed.
Lemma D_971c8 : decode_any W_971c8 = Some (Load SZ4 true 11 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_971cc : bv 32 := 0x871d60ef.
Lemma F_971cc : fetch_word Ubsan.M.loaded_segments (0x971cc : word) = Some W_971cc.
Proof. vm_refl. Qed.
Lemma D_971cc : decode_any W_971cc = Some (Jal 1 1927280, 4%Z).
Proof. vm_refl. Qed.

Definition W_971d0 : bv 32 := 0x04a13023.
Lemma F_971d0 : fetch_word Ubsan.M.loaded_segments (0x971d0 : word) = Some W_971d0.
Proof. vm_refl. Qed.
Lemma D_971d0 : decode_any W_971d0 = Some (Store SZ8 2 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_971d4 : bv 32 := 0x42050663.
Lemma F_971d4 : fetch_word Ubsan.M.loaded_segments (0x971d4 : word) = Some W_971d4.
Proof. vm_refl. Qed.
Lemma D_971d4 : decode_any W_971d4 = Some (Branch BC_EQ 10 0 1068, 4%Z).
Proof. vm_refl. Qed.

Definition W_971d8 : bv 32 := 0x00048593.
Lemma F_971d8 : fetch_word Ubsan.M.loaded_segments (0x971d8 : word) = Some W_971d8.
Proof. vm_refl. Qed.
Lemma D_971d8 : decode_any W_971d8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_971dc : bv 32 := 0xaf0d70ef.
Lemma F_971dc : fetch_word Ubsan.M.loaded_segments (0x971dc : word) = Some W_971dc.
Proof. vm_refl. Qed.
Lemma D_971dc : decode_any W_971dc = Some (Jal 1 1929968, 4%Z).
Proof. vm_refl. Qed.

Definition W_971e0 : bv 32 := 0x04013503.
Lemma F_971e0 : fetch_word Ubsan.M.loaded_segments (0x971e0 : word) = Some W_971e0.
Proof. vm_refl. Qed.
Lemma D_971e0 : decode_any W_971e0 = Some (Load SZ8 true 10 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_971e4 : bv 32 := 0x00048593.
Lemma F_971e4 : fetch_word Ubsan.M.loaded_segments (0x971e4 : word) = Some W_971e4.
Proof. vm_refl. Qed.
Lemma D_971e4 : decode_any W_971e4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_971e8 : bv 32 := 0xa54d70ef.
Lemma F_971e8 : fetch_word Ubsan.M.loaded_segments (0x971e8 : word) = Some W_971e8.
Proof. vm_refl. Qed.
Lemma D_971e8 : decode_any W_971e8 = Some (Jal 1 1929812, 4%Z).
Proof. vm_refl. Qed.

Definition W_971ec : bv 32 := 0x04013503.
Lemma F_971ec : fetch_word Ubsan.M.loaded_segments (0x971ec : word) = Some W_971ec.
Proof. vm_refl. Qed.
Lemma D_971ec : decode_any W_971ec = Some (Load SZ8 true 10 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_971f0 : bv 32 := 0x00048593.
Lemma F_971f0 : fetch_word Ubsan.M.loaded_segments (0x971f0 : word) = Some W_971f0.
Proof. vm_refl. Qed.
Lemma D_971f0 : decode_any W_971f0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_971f4 : bv 32 := 0xd84d70ef.
Lemma F_971f4 : fetch_word Ubsan.M.loaded_segments (0x971f4 : word) = Some W_971f4.
Proof. vm_refl. Qed.
Lemma D_971f4 : decode_any W_971f4 = Some (Jal 1 1930628, 4%Z).
Proof. vm_refl. Qed.

Definition W_971f8 : bv 32 := 0x04013503.
Lemma F_971f8 : fetch_word Ubsan.M.loaded_segments (0x971f8 : word) = Some W_971f8.
Proof. vm_refl. Qed.
Lemma D_971f8 : decode_any W_971f8 = Some (Load SZ8 true 10 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_971fc : bv 32 := 0x00048593.
Lemma F_971fc : fetch_word Ubsan.M.loaded_segments (0x971fc : word) = Some W_971fc.
Proof. vm_refl. Qed.
Lemma D_971fc : decode_any W_971fc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97200 : bv 32 := 0x960d70ef.
Lemma F_97200 : fetch_word Ubsan.M.loaded_segments (0x97200 : word) = Some W_97200.
Proof. vm_refl. Qed.
Lemma D_97200 : decode_any W_97200 = Some (Jal 1 1929568, 4%Z).
Proof. vm_refl. Qed.

Definition W_97204 : bv 32 := 0x00048513.
Lemma F_97204 : fetch_word Ubsan.M.loaded_segments (0x97204 : word) = Some W_97204.
Proof. vm_refl. Qed.
Lemma D_97204 : decode_any W_97204 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97208 : bv 32 := 0xfe5d70ef.
Lemma F_97208 : fetch_word Ubsan.M.loaded_segments (0x97208 : word) = Some W_97208.
Proof. vm_refl. Qed.
Lemma D_97208 : decode_any W_97208 = Some (Jal 1 1933284, 4%Z).
Proof. vm_refl. Qed.

Definition W_9720c : bv 32 := 0x00050413.
Lemma F_9720c : fetch_word Ubsan.M.loaded_segments (0x9720c : word) = Some W_9720c.
Proof. vm_refl. Qed.
Lemma D_9720c : decode_any W_9720c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97210 : bv 32 := 0x00048513.
Lemma F_97210 : fetch_word Ubsan.M.loaded_segments (0x97210 : word) = Some W_97210.
Proof. vm_refl. Qed.
Lemma D_97210 : decode_any W_97210 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97214 : bv 32 := 0xd39d60ef.
Lemma F_97214 : fetch_word Ubsan.M.loaded_segments (0x97214 : word) = Some W_97214.
Proof. vm_refl. Qed.
Lemma D_97214 : decode_any W_97214 = Some (Jal 1 1928504, 4%Z).
Proof. vm_refl. Qed.

Definition W_97218 : bv 32 := 0x04013583.
Lemma F_97218 : fetch_word Ubsan.M.loaded_segments (0x97218 : word) = Some W_97218.
Proof. vm_refl. Qed.
Lemma D_97218 : decode_any W_97218 = Some (Load SZ8 true 11 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9721c : bv 32 := 0x00050913.
Lemma F_9721c : fetch_word Ubsan.M.loaded_segments (0x9721c : word) = Some W_9721c.
Proof. vm_refl. Qed.
Lemma D_9721c : decode_any W_9721c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97220 : bv 32 := 0x00058513.
Lemma F_97220 : fetch_word Ubsan.M.loaded_segments (0x97220 : word) = Some W_97220.
Proof. vm_refl. Qed.
Lemma D_97220 : decode_any W_97220 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97224 : bv 32 := 0xfc9d70ef.
Lemma F_97224 : fetch_word Ubsan.M.loaded_segments (0x97224 : word) = Some W_97224.
Proof. vm_refl. Qed.
Lemma D_97224 : decode_any W_97224 = Some (Jal 1 1933256, 4%Z).
Proof. vm_refl. Qed.

Definition W_97228 : bv 32 := 0x04013583.
Lemma F_97228 : fetch_word Ubsan.M.loaded_segments (0x97228 : word) = Some W_97228.
Proof. vm_refl. Qed.
Lemma D_97228 : decode_any W_97228 = Some (Load SZ8 true 11 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9722c : bv 32 := 0x02a13c23.
Lemma F_9722c : fetch_word Ubsan.M.loaded_segments (0x9722c : word) = Some W_9722c.
Proof. vm_refl. Qed.
Lemma D_9722c : decode_any W_9722c = Some (Store SZ8 2 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_97230 : bv 32 := 0x00058513.
Lemma F_97230 : fetch_word Ubsan.M.loaded_segments (0x97230 : word) = Some W_97230.
Proof. vm_refl. Qed.
Lemma D_97230 : decode_any W_97230 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97234 : bv 32 := 0xd19d60ef.
Lemma F_97234 : fetch_word Ubsan.M.loaded_segments (0x97234 : word) = Some W_97234.
Proof. vm_refl. Qed.
Lemma D_97234 : decode_any W_97234 = Some (Jal 1 1928472, 4%Z).
Proof. vm_refl. Qed.

Definition W_97238 : bv 32 := 0x04c12583.
Lemma F_97238 : fetch_word Ubsan.M.loaded_segments (0x97238 : word) = Some W_97238.
Proof. vm_refl. Qed.
Lemma D_97238 : decode_any W_97238 = Some (Load SZ4 true 11 2 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_9723c : bv 32 := 0xfff58593.
Lemma F_9723c : fetch_word Ubsan.M.loaded_segments (0x9723c : word) = Some W_9723c.
Proof. vm_refl. Qed.
Lemma D_9723c : decode_any W_9723c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_97240 : bv 32 := 0x00100613.
Lemma F_97240 : fetch_word Ubsan.M.loaded_segments (0x97240 : word) = Some W_97240.
Proof. vm_refl. Qed.
Lemma D_97240 : decode_any W_97240 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_97244 : bv 32 := 0x3ec99263.
Lemma F_97244 : fetch_word Ubsan.M.loaded_segments (0x97244 : word) = Some W_97244.
Proof. vm_refl. Qed.
Lemma D_97244 : decode_any W_97244 = Some (Branch BC_NE 19 12 996, 4%Z).
Proof. vm_refl. Qed.

Definition W_97248 : bv 32 := 0x01f00613.
Lemma F_97248 : fetch_word Ubsan.M.loaded_segments (0x97248 : word) = Some W_97248.
Proof. vm_refl. Qed.
Lemma D_97248 : decode_any W_97248 = Some (OpImm ALU_ADD 12 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_9724c : bv 32 := 0x62b66ce3.
Lemma F_9724c : fetch_word Ubsan.M.loaded_segments (0x9724c : word) = Some W_9724c.
Proof. vm_refl. Qed.
Lemma D_9724c : decode_any W_9724c = Some (Branch BC_LTU 12 11 3640, 4%Z).
Proof. vm_refl. Qed.

Definition W_97250 : bv 32 := 0x00259593.
Lemma F_97250 : fetch_word Ubsan.M.loaded_segments (0x97250 : word) = Some W_97250.
Proof. vm_refl. Qed.
Lemma D_97250 : decode_any W_97250 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_97254 : bv 32 := 0xfff88617.
Lemma F_97254 : fetch_word Ubsan.M.loaded_segments (0x97254 : word) = Some W_97254.
Proof. vm_refl. Qed.
Lemma D_97254 : decode_any W_97254 = Some (Auipc 12 1048456, 4%Z).
Proof. vm_refl. Qed.

Definition W_97258 : bv 32 := 0x51460613.
Lemma F_97258 : fetch_word Ubsan.M.loaded_segments (0x97258 : word) = Some W_97258.
Proof. vm_refl. Qed.
Lemma D_97258 : decode_any W_97258 = Some (OpImm ALU_ADD 12 12 1300, 4%Z).
Proof. vm_refl. Qed.

Definition W_9725c : bv 32 := 0x00c585b3.
Lemma F_9725c : fetch_word Ubsan.M.loaded_segments (0x9725c : word) = Some W_9725c.
Proof. vm_refl. Qed.
Lemma D_9725c : decode_any W_9725c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_97260 : bv 32 := 0x0005a583.
Lemma F_97260 : fetch_word Ubsan.M.loaded_segments (0x97260 : word) = Some W_97260.
Proof. vm_refl. Qed.
Lemma D_97260 : decode_any W_97260 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97264 : bv 32 := 0x00c585b3.
Lemma F_97264 : fetch_word Ubsan.M.loaded_segments (0x97264 : word) = Some W_97264.
Proof. vm_refl. Qed.
Lemma D_97264 : decode_any W_97264 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_97268 : bv 32 := 0x00058067.
Lemma F_97268 : fetch_word Ubsan.M.loaded_segments (0x97268 : word) = Some W_97268.
Proof. vm_refl. Qed.
Lemma D_97268 : decode_any W_97268 = Some (Jalr 0 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97600 : bv 32 := 0x0008f517.
Lemma F_97600 : fetch_word Ubsan.M.loaded_segments (0x97600 : word) = Some W_97600.
Proof. vm_refl. Qed.
Lemma D_97600 : decode_any W_97600 = Some (Auipc 10 143, 4%Z).
Proof. vm_refl. Qed.

Definition W_97604 : bv 32 := 0x47053503.
Lemma F_97604 : fetch_word Ubsan.M.loaded_segments (0x97604 : word) = Some W_97604.
Proof. vm_refl. Qed.
Lemma D_97604 : decode_any W_97604 = Some (Load SZ8 true 10 10 1136, 4%Z).
Proof. vm_refl. Qed.

Definition W_97608 : bv 32 := 0x00052503.
Lemma F_97608 : fetch_word Ubsan.M.loaded_segments (0x97608 : word) = Some W_97608.
Proof. vm_refl. Qed.
Lemma D_97608 : decode_any W_97608 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9760c : bv 32 := 0x00500593.
Lemma F_9760c : fetch_word Ubsan.M.loaded_segments (0x9760c : word) = Some W_9760c.
Proof. vm_refl. Qed.
Lemma D_9760c : decode_any W_9760c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_97610 : bv 32 := 0x44a5c263.
Lemma F_97610 : fetch_word Ubsan.M.loaded_segments (0x97610 : word) = Some W_97610.
Proof. vm_refl. Qed.
Lemma D_97610 : decode_any W_97610 = Some (Branch BC_LT 11 10 1092, 4%Z).
Proof. vm_refl. Qed.

Definition W_97614 : bv 32 := 0xfff7b517.
Lemma F_97614 : fetch_word Ubsan.M.loaded_segments (0x97614 : word) = Some W_97614.
Proof. vm_refl. Qed.
Lemma D_97614 : decode_any W_97614 = Some (Auipc 10 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_97618 : bv 32 := 0xfff82597.
Lemma F_97618 : fetch_word Ubsan.M.loaded_segments (0x97618 : word) = Some W_97618.
Proof. vm_refl. Qed.
Lemma D_97618 : decode_any W_97618 = Some (Auipc 11 1048450, 4%Z).
Proof. vm_refl. Qed.

Definition W_9761c : bv 32 := 0x0c650513.
Lemma F_9761c : fetch_word Ubsan.M.loaded_segments (0x9761c : word) = Some W_9761c.
Proof. vm_refl. Qed.
Lemma D_9761c : decode_any W_9761c = Some (OpImm ALU_ADD 10 10 198, 4%Z).
Proof. vm_refl. Qed.

Definition W_97620 : bv 32 := 0xddb58593.
Lemma F_97620 : fetch_word Ubsan.M.loaded_segments (0x97620 : word) = Some W_97620.
Proof. vm_refl. Qed.
Lemma D_97620 : decode_any W_97620 = Some (OpImm ALU_ADD 11 11 3547, 4%Z).
Proof. vm_refl. Qed.

Definition W_97624 : bv 32 := 0x4240006f.
Lemma F_97624 : fetch_word Ubsan.M.loaded_segments (0x97624 : word) = Some W_97624.
Proof. vm_refl. Qed.
Lemma D_97624 : decode_any W_97624 = Some (Jal 0 1060, 4%Z).
Proof. vm_refl. Qed.

Definition W_97628 : bv 32 := 0x01f00613.
Lemma F_97628 : fetch_word Ubsan.M.loaded_segments (0x97628 : word) = Some W_97628.
Proof. vm_refl. Qed.
Lemma D_97628 : decode_any W_97628 = Some (OpImm ALU_ADD 12 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_9762c : bv 32 := 0x26b66ce3.
Lemma F_9762c : fetch_word Ubsan.M.loaded_segments (0x9762c : word) = Some W_9762c.
Proof. vm_refl. Qed.
Lemma D_9762c : decode_any W_9762c = Some (Branch BC_LTU 12 11 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_97630 : bv 32 := 0x00259593.
Lemma F_97630 : fetch_word Ubsan.M.loaded_segments (0x97630 : word) = Some W_97630.
Proof. vm_refl. Qed.
Lemma D_97630 : decode_any W_97630 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_97634 : bv 32 := 0xfff88617.
Lemma F_97634 : fetch_word Ubsan.M.loaded_segments (0x97634 : word) = Some W_97634.
Proof. vm_refl. Qed.
Lemma D_97634 : decode_any W_97634 = Some (Auipc 12 1048456, 4%Z).
Proof. vm_refl. Qed.

Definition W_97638 : bv 32 := 0x0b460613.
Lemma F_97638 : fetch_word Ubsan.M.loaded_segments (0x97638 : word) = Some W_97638.
Proof. vm_refl. Qed.
Lemma D_97638 : decode_any W_97638 = Some (OpImm ALU_ADD 12 12 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9763c : bv 32 := 0x00c585b3.
Lemma F_9763c : fetch_word Ubsan.M.loaded_segments (0x9763c : word) = Some W_9763c.
Proof. vm_refl. Qed.
Lemma D_9763c : decode_any W_9763c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_97640 : bv 32 := 0x0005a583.
Lemma F_97640 : fetch_word Ubsan.M.loaded_segments (0x97640 : word) = Some W_97640.
Proof. vm_refl. Qed.
Lemma D_97640 : decode_any W_97640 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97644 : bv 32 := 0x00c585b3.
Lemma F_97644 : fetch_word Ubsan.M.loaded_segments (0x97644 : word) = Some W_97644.
Proof. vm_refl. Qed.
Lemma D_97644 : decode_any W_97644 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_97648 : bv 32 := 0x00058067.
Lemma F_97648 : fetch_word Ubsan.M.loaded_segments (0x97648 : word) = Some W_97648.
Proof. vm_refl. Qed.
Lemma D_97648 : decode_any W_97648 = Some (Jalr 0 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97a48 : bv 32 := 0x00000613.
Lemma F_97a48 : fetch_word Ubsan.M.loaded_segments (0x97a48 : word) = Some W_97a48.
Proof. vm_refl. Qed.
Lemma D_97a48 : decode_any W_97a48 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_97a4c : bv 32 := 0xcf5cb0ef.
Lemma F_97a4c : fetch_word Ubsan.M.loaded_segments (0x97a4c : word) = Some W_97a4c.
Proof. vm_refl. Qed.
Lemma D_97a4c : decode_any W_97a4c = Some (Jal 1 1883380, 4%Z).
Proof. vm_refl. Qed.

Definition W_97a50 : bv 32 := 0x7e10006f.
Lemma F_97a50 : fetch_word Ubsan.M.loaded_segments (0x97a50 : word) = Some W_97a50.
Proof. vm_refl. Qed.
Lemma D_97a50 : decode_any W_97a50 = Some (Jal 0 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a2c : bv 32 := 0x04013503.
Lemma F_98a2c : fetch_word Ubsan.M.loaded_segments (0x98a2c : word) = Some W_98a2c.
Proof. vm_refl. Qed.
Lemma D_98a2c : decode_any W_98a2c = Some (Load SZ8 true 10 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a30 : bv 32 := 0x0b813083.
Lemma F_98a30 : fetch_word Ubsan.M.loaded_segments (0x98a30 : word) = Some W_98a30.
Proof. vm_refl. Qed.
Lemma D_98a30 : decode_any W_98a30 = Some (Load SZ8 true 1 2 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a34 : bv 32 := 0x0b013403.
Lemma F_98a34 : fetch_word Ubsan.M.loaded_segments (0x98a34 : word) = Some W_98a34.
Proof. vm_refl. Qed.
Lemma D_98a34 : decode_any W_98a34 = Some (Load SZ8 true 8 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a38 : bv 32 := 0x0a813483.
Lemma F_98a38 : fetch_word Ubsan.M.loaded_segments (0x98a38 : word) = Some W_98a38.
Proof. vm_refl. Qed.
Lemma D_98a38 : decode_any W_98a38 = Some (Load SZ8 true 9 2 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a3c : bv 32 := 0x0a013903.
Lemma F_98a3c : fetch_word Ubsan.M.loaded_segments (0x98a3c : word) = Some W_98a3c.
Proof. vm_refl. Qed.
Lemma D_98a3c : decode_any W_98a3c = Some (Load SZ8 true 18 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a40 : bv 32 := 0x09813983.
Lemma F_98a40 : fetch_word Ubsan.M.loaded_segments (0x98a40 : word) = Some W_98a40.
Proof. vm_refl. Qed.
Lemma D_98a40 : decode_any W_98a40 = Some (Load SZ8 true 19 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a44 : bv 32 := 0x09013a03.
Lemma F_98a44 : fetch_word Ubsan.M.loaded_segments (0x98a44 : word) = Some W_98a44.
Proof. vm_refl. Qed.
Lemma D_98a44 : decode_any W_98a44 = Some (Load SZ8 true 20 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a48 : bv 32 := 0x08813a83.
Lemma F_98a48 : fetch_word Ubsan.M.loaded_segments (0x98a48 : word) = Some W_98a48.
Proof. vm_refl. Qed.
Lemma D_98a48 : decode_any W_98a48 = Some (Load SZ8 true 21 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a4c : bv 32 := 0x08013b03.
Lemma F_98a4c : fetch_word Ubsan.M.loaded_segments (0x98a4c : word) = Some W_98a4c.
Proof. vm_refl. Qed.
Lemma D_98a4c : decode_any W_98a4c = Some (Load SZ8 true 22 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a50 : bv 32 := 0x07813b83.
Lemma F_98a50 : fetch_word Ubsan.M.loaded_segments (0x98a50 : word) = Some W_98a50.
Proof. vm_refl. Qed.
Lemma D_98a50 : decode_any W_98a50 = Some (Load SZ8 true 23 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a54 : bv 32 := 0x07013c03.
Lemma F_98a54 : fetch_word Ubsan.M.loaded_segments (0x98a54 : word) = Some W_98a54.
Proof. vm_refl. Qed.
Lemma D_98a54 : decode_any W_98a54 = Some (Load SZ8 true 24 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a58 : bv 32 := 0x06813c83.
Lemma F_98a58 : fetch_word Ubsan.M.loaded_segments (0x98a58 : word) = Some W_98a58.
Proof. vm_refl. Qed.
Lemma D_98a58 : decode_any W_98a58 = Some (Load SZ8 true 25 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a5c : bv 32 := 0x06013d03.
Lemma F_98a5c : fetch_word Ubsan.M.loaded_segments (0x98a5c : word) = Some W_98a5c.
Proof. vm_refl. Qed.
Lemma D_98a5c : decode_any W_98a5c = Some (Load SZ8 true 26 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a60 : bv 32 := 0x05813d83.
Lemma F_98a60 : fetch_word Ubsan.M.loaded_segments (0x98a60 : word) = Some W_98a60.
Proof. vm_refl. Qed.
Lemma D_98a60 : decode_any W_98a60 = Some (Load SZ8 true 27 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a64 : bv 32 := 0x0c010113.
Lemma F_98a64 : fetch_word Ubsan.M.loaded_segments (0x98a64 : word) = Some W_98a64.
Proof. vm_refl. Qed.
Lemma D_98a64 : decode_any W_98a64 = Some (OpImm ALU_ADD 2 2 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_98a68 : bv 32 := 0x00008067.
Lemma F_98a68 : fetch_word Ubsan.M.loaded_segments (0x98a68 : word) = Some W_98a68.
Proof. vm_refl. Qed.
Lemma D_98a68 : decode_any W_98a68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
