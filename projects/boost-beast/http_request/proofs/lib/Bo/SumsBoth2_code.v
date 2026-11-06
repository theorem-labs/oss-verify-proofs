(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8679c : bv 32 := 0x06060663.
Lemma D_8679c : decode_any W_8679c = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867a0 : bv 32 := 0x00000693.
Lemma D_867a0 : decode_any W_867a0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867a4 : bv 32 := 0x00d58733.
Lemma D_867a4 : decode_any W_867a4 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867a8 : bv 32 := 0x00074703.
Lemma D_867a8 : decode_any W_867a8 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867ac : bv 32 := 0x00070c63.
Lemma D_867ac : decode_any W_867ac = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867b0 : bv 32 := 0x00d507b3.
Lemma D_867b0 : decode_any W_867b0 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867b4 : bv 32 := 0x00168693.
Lemma D_867b4 : decode_any W_867b4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867b8 : bv 32 := 0x00e78023.
Lemma D_867b8 : decode_any W_867b8 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867bc : bv 32 := 0xfed614e3.
Lemma D_867bc : decode_any W_867bc = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867c0 : bv 32 := 0x00060693.
Lemma D_867c0 : decode_any W_867c0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867c4 : bv 32 := 0x00d505b3.
Lemma D_867c4 : decode_any W_867c4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867c8 : bv 32 := 0x40d6073b.
Lemma D_867c8 : decode_any W_867c8 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867cc : bv 32 := 0x00b76733.
Lemma D_867cc : decode_any W_867cc = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867d0 : bv 32 := 0x00f77713.
Lemma D_867d0 : decode_any W_867d0 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867d4 : bv 32 := 0x00070e63.
Lemma D_867d4 : decode_any W_867d4 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867d8 : bv 32 := 0x02d60863.
Lemma D_867d8 : decode_any W_867d8 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867dc : bv 32 := 0x00c50633.
Lemma D_867dc : decode_any W_867dc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867e0 : bv 32 := 0x00058023.
Lemma D_867e0 : decode_any W_867e0 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867e4 : bv 32 := 0x00158593.
Lemma D_867e4 : decode_any W_867e4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867e8 : bv 32 := 0xfec59ce3.
Lemma D_867e8 : decode_any W_867e8 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867ec : bv 32 := 0x01c0006f.
Lemma D_867ec : decode_any W_867ec = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867f0 : bv 32 := 0x00d60c63.
Lemma D_867f0 : decode_any W_867f0 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867f4 : bv 32 := 0x00c50633.
Lemma D_867f4 : decode_any W_867f4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867f8 : bv 32 := 0x0005b023.
Lemma D_867f8 : decode_any W_867f8 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_867fc : bv 32 := 0x0005b423.
Lemma D_867fc : decode_any W_867fc = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86800 : bv 32 := 0x01058593.
Lemma D_86800 : decode_any W_86800 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86804 : bv 32 := 0xfec5eae3.
Lemma D_86804 : decode_any W_86804 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_86808 : bv 32 := 0x00008067.
Lemma D_86808 : decode_any W_86808 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_722e4 : bv 32 := 0x00200613.
Lemma D_722e4 : decode_any W_722e4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_722e8 : bv 32 := 0x14c5ea63.
Lemma D_722e8 : decode_any W_722e8 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_722ec : bv 32 := 0x00100613.
Lemma D_722ec : decode_any W_722ec = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_722f0 : bv 32 := 0x00100693.
Lemma D_722f0 : decode_any W_722f0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_722f4 : bv 32 := 0x00c0006f.
Lemma D_722f4 : decode_any W_722f4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_722f8 : bv 32 := 0x00160613.
Lemma D_722f8 : decode_any W_722f8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_722fc : bv 32 := 0x12b60c63.
Lemma D_722fc : decode_any W_722fc = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72300 : bv 32 := 0x00461713.
Lemma D_72300 : decode_any W_72300 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72304 : bv 32 := 0x00e50733.
Lemma D_72304 : decode_any W_72304 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72308 : bv 32 := 0x00072703.
Lemma D_72308 : decode_any W_72308 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7230c : bv 32 := 0x00060893.
Lemma D_7230c : decode_any W_7230c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72310 : bv 32 := 0xfff88793.
Lemma D_72310 : decode_any W_72310 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72314 : bv 32 := 0x0017d813.
Lemma D_72314 : decode_any W_72314 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72318 : bv 32 := 0x00481293.
Lemma D_72318 : decode_any W_72318 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7231c : bv 32 := 0x005502b3.
Lemma D_7231c : decode_any W_7231c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72320 : bv 32 := 0x0002a303.
Lemma D_72320 : decode_any W_72320 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72324 : bv 32 := 0xfce37ae3.
Lemma D_72324 : decode_any W_72324 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72328 : bv 32 := 0x0002b303.
Lemma D_72328 : decode_any W_72328 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7232c : bv 32 := 0x00489893.
Lemma D_7232c : decode_any W_7232c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72330 : bv 32 := 0x011508b3.
Lemma D_72330 : decode_any W_72330 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72334 : bv 32 := 0x0048a383.
Lemma D_72334 : decode_any W_72334 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72338 : bv 32 := 0x0068b023.
Lemma D_72338 : decode_any W_72338 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7233c : bv 32 := 0x0082b303.
Lemma D_7233c : decode_any W_7233c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72340 : bv 32 := 0x0088be03.
Lemma D_72340 : decode_any W_72340 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72344 : bv 32 := 0x0068b423.
Lemma D_72344 : decode_any W_72344 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72348 : bv 32 := 0x00e2a023.
Lemma D_72348 : decode_any W_72348 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7234c : bv 32 := 0x0072a223.
Lemma D_7234c : decode_any W_7234c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72350 : bv 32 := 0x01c2b423.
Lemma D_72350 : decode_any W_72350 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72354 : bv 32 := 0x00080893.
Lemma D_72354 : decode_any W_72354 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72358 : bv 32 := 0xfaf6ece3.
Lemma D_72358 : decode_any W_72358 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7235c : bv 32 := 0xf9dff06f.
Lemma D_7235c : decode_any W_7235c = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72360 : bv 32 := 0x00000613.
Lemma D_72360 : decode_any W_72360 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72364 : bv 32 := 0x00459693.
Lemma D_72364 : decode_any W_72364 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72368 : bv 32 := 0x00d506b3.
Lemma D_72368 : decode_any W_72368 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7236c : bv 32 := 0x0006b703.
Lemma D_7236c : decode_any W_7236c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72370 : bv 32 := 0x0086b783.
Lemma D_72370 : decode_any W_72370 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72374 : bv 32 := 0x00053803.
Lemma D_72374 : decode_any W_72374 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72378 : bv 32 := 0x00853883.
Lemma D_72378 : decode_any W_72378 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7237c : bv 32 := 0x00e53023.
Lemma D_7237c : decode_any W_7237c = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72380 : bv 32 := 0x00f53423.
Lemma D_72380 : decode_any W_72380 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72384 : bv 32 := 0x0106b023.
Lemma D_72384 : decode_any W_72384 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72388 : bv 32 := 0x0116b423.
Lemma D_72388 : decode_any W_72388 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7238c : bv 32 := 0x00000693.
Lemma D_7238c : decode_any W_7238c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72390 : bv 32 := 0x00161793.
Lemma D_72390 : decode_any W_72390 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72394 : bv 32 := 0x00178813.
Lemma D_72394 : decode_any W_72394 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72398 : bv 32 := 0x00461713.
Lemma D_72398 : decode_any W_72398 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7239c : bv 32 := 0x00b86a63.
Lemma D_7239c : decode_any W_7239c = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723a0 : bv 32 := 0x00278793.
Lemma D_723a0 : decode_any W_723a0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723a4 : bv 32 := 0x02b7ea63.
Lemma D_723a4 : decode_any W_723a4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723a8 : bv 32 := 0x04c69c63.
Lemma D_723a8 : decode_any W_723a8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723ac : bv 32 := 0x0880006f.
Lemma D_723ac : decode_any W_723ac = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723b0 : bv 32 := 0x00e506b3.
Lemma D_723b0 : decode_any W_723b0 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723b4 : bv 32 := 0x00481893.
Lemma D_723b4 : decode_any W_723b4 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723b8 : bv 32 := 0x011508b3.
Lemma D_723b8 : decode_any W_723b8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723bc : bv 32 := 0x0006a683.
Lemma D_723bc : decode_any W_723bc = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723c0 : bv 32 := 0x0008a883.
Lemma D_723c0 : decode_any W_723c0 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723c4 : bv 32 := 0x0116e463.
Lemma D_723c4 : decode_any W_723c4 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723c8 : bv 32 := 0x00060813.
Lemma D_723c8 : decode_any W_723c8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723cc : bv 32 := 0x00080693.
Lemma D_723cc : decode_any W_723cc = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723d0 : bv 32 := 0x00278793.
Lemma D_723d0 : decode_any W_723d0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723d4 : bv 32 := 0xfcb7fae3.
Lemma D_723d4 : decode_any W_723d4 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723d8 : bv 32 := 0x00469813.
Lemma D_723d8 : decode_any W_723d8 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723dc : bv 32 := 0x00479893.
Lemma D_723dc : decode_any W_723dc = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723e0 : bv 32 := 0x01050833.
Lemma D_723e0 : decode_any W_723e0 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723e4 : bv 32 := 0x011508b3.
Lemma D_723e4 : decode_any W_723e4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723e8 : bv 32 := 0x00082803.
Lemma D_723e8 : decode_any W_723e8 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723ec : bv 32 := 0x0008a883.
Lemma D_723ec : decode_any W_723ec = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723f0 : bv 32 := 0x01186463.
Lemma D_723f0 : decode_any W_723f0 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723f4 : bv 32 := 0x00068793.
Lemma D_723f4 : decode_any W_723f4 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723f8 : bv 32 := 0x00078693.
Lemma D_723f8 : decode_any W_723f8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_723fc : bv 32 := 0x02c78c63.
Lemma D_723fc : decode_any W_723fc = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72400 : bv 32 := 0x00469613.
Lemma D_72400 : decode_any W_72400 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72404 : bv 32 := 0x00c50633.
Lemma D_72404 : decode_any W_72404 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72408 : bv 32 := 0x00063783.
Lemma D_72408 : decode_any W_72408 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7240c : bv 32 := 0x00e50733.
Lemma D_7240c : decode_any W_7240c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72410 : bv 32 := 0x00073803.
Lemma D_72410 : decode_any W_72410 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72414 : bv 32 := 0x00873883.
Lemma D_72414 : decode_any W_72414 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72418 : bv 32 := 0x00f73023.
Lemma D_72418 : decode_any W_72418 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7241c : bv 32 := 0x00863783.
Lemma D_7241c : decode_any W_7241c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72420 : bv 32 := 0x00f73423.
Lemma D_72420 : decode_any W_72420 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72424 : bv 32 := 0x01063023.
Lemma D_72424 : decode_any W_72424 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72428 : bv 32 := 0x01163423.
Lemma D_72428 : decode_any W_72428 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7242c : bv 32 := 0x00068613.
Lemma D_7242c : decode_any W_7242c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72430 : bv 32 := 0xf6b6e0e3.
Lemma D_72430 : decode_any W_72430 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72434 : bv 32 := 0xfff58593.
Lemma D_72434 : decode_any W_72434 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72438 : bv 32 := 0xf20594e3.
Lemma D_72438 : decode_any W_72438 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7243c : bv 32 := 0x00008067.
Lemma D_7243c : decode_any W_7243c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
