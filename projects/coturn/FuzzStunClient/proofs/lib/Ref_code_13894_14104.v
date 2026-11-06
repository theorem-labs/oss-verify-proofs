(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_13894 : bv 32 := 0xffffd197.
Lemma F_13894 : fetch_word Plain.M.loaded_segments (0x13894 : word) = Some W_13894.
Proof. vm_refl. Qed.
Lemma D_13894 : decode_any W_13894 = Some (Auipc 3 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13898 : bv 32 := 0xf6c18193.
Lemma F_13898 : fetch_word Plain.M.loaded_segments (0x13898 : word) = Some W_13898.
Proof. vm_refl. Qed.
Lemma D_13898 : decode_any W_13898 = Some (OpImm ALU_ADD 3 3 3948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1389c : bv 32 := 0x00010513.
Lemma F_1389c : fetch_word Plain.M.loaded_segments (0x1389c : word) = Some W_1389c.
Proof. vm_refl. Qed.
Lemma D_1389c : decode_any W_1389c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138a0 : bv 32 := 0xfffec597.
Lemma F_138a0 : fetch_word Plain.M.loaded_segments (0x138a0 : word) = Some W_138a0.
Proof. vm_refl. Qed.
Lemma D_138a0 : decode_any W_138a0 = Some (Auipc 11 1048556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138a4 : bv 32 := 0x76058593.
Lemma F_138a4 : fetch_word Plain.M.loaded_segments (0x138a4 : word) = Some W_138a4.
Proof. vm_refl. Qed.
Lemma D_138a4 : decode_any W_138a4 = Some (OpImm ALU_ADD 11 11 1888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138a8 : bv 32 := 0xff017113.
Lemma F_138a8 : fetch_word Plain.M.loaded_segments (0x138a8 : word) = Some W_138a8.
Proof. vm_refl. Qed.
Lemma D_138a8 : decode_any W_138a8 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138ac : bv 32 := 0x0040006f.
Lemma F_138ac : fetch_word Plain.M.loaded_segments (0x138ac : word) = Some W_138ac.
Proof. vm_refl. Qed.
Lemma D_138ac : decode_any W_138ac = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138b0 : bv 32 := 0x00052583.
Lemma F_138b0 : fetch_word Plain.M.loaded_segments (0x138b0 : word) = Some W_138b0.
Proof. vm_refl. Qed.
Lemma D_138b0 : decode_any W_138b0 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138b4 : bv 32 := 0x00012617.
Lemma F_138b4 : fetch_word Plain.M.loaded_segments (0x138b4 : word) = Some W_138b4.
Proof. vm_refl. Qed.
Lemma D_138b4 : decode_any W_138b4 = Some (Auipc 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138b8 : bv 32 := 0x00012697.
Lemma F_138b8 : fetch_word Plain.M.loaded_segments (0x138b8 : word) = Some W_138b8.
Proof. vm_refl. Qed.
Lemma D_138b8 : decode_any W_138b8 = Some (Auipc 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138bc : bv 32 := 0x00012717.
Lemma F_138bc : fetch_word Plain.M.loaded_segments (0x138bc : word) = Some W_138bc.
Proof. vm_refl. Qed.
Lemma D_138bc : decode_any W_138bc = Some (Auipc 14 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138c0 : bv 32 := 0x9fc63783.
Lemma F_138c0 : fetch_word Plain.M.loaded_segments (0x138c0 : word) = Some W_138c0.
Proof. vm_refl. Qed.
Lemma D_138c0 : decode_any W_138c0 = Some (Load SZ8 true 15 12 2556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138c4 : bv 32 := 0xa006b683.
Lemma F_138c4 : fetch_word Plain.M.loaded_segments (0x138c4 : word) = Some W_138c4.
Proof. vm_refl. Qed.
Lemma D_138c4 : decode_any W_138c4 = Some (Load SZ8 true 13 13 2560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138c8 : bv 32 := 0xa0473703.
Lemma F_138c8 : fetch_word Plain.M.loaded_segments (0x138c8 : word) = Some W_138c8.
Proof. vm_refl. Qed.
Lemma D_138c8 : decode_any W_138c8 = Some (Load SZ8 true 14 14 2564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138cc : bv 32 := 0x00850613.
Lemma F_138cc : fetch_word Plain.M.loaded_segments (0x138cc : word) = Some W_138cc.
Proof. vm_refl. Qed.
Lemma D_138cc : decode_any W_138cc = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138d0 : bv 32 := 0x00078513.
Lemma F_138d0 : fetch_word Plain.M.loaded_segments (0x138d0 : word) = Some W_138d0.
Proof. vm_refl. Qed.
Lemma D_138d0 : decode_any W_138d0 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138d4 : bv 32 := 0x00000793.
Lemma F_138d4 : fetch_word Plain.M.loaded_segments (0x138d4 : word) = Some W_138d4.
Proof. vm_refl. Qed.
Lemma D_138d4 : decode_any W_138d4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138d8 : bv 32 := 0x4190706f.
Lemma F_138d8 : fetch_word Plain.M.loaded_segments (0x138d8 : word) = Some W_138d8.
Proof. vm_refl. Qed.
Lemma D_138d8 : decode_any W_138d8 = Some (Jal 0 31768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138dc : bv 32 := 0xff010113.
Lemma F_138dc : fetch_word Plain.M.loaded_segments (0x138dc : word) = Some W_138dc.
Proof. vm_refl. Qed.
Lemma D_138dc : decode_any W_138dc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138e0 : bv 32 := 0x00113423.
Lemma F_138e0 : fetch_word Plain.M.loaded_segments (0x138e0 : word) = Some W_138e0.
Proof. vm_refl. Qed.
Lemma D_138e0 : decode_any W_138e0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138e4 : bv 32 := 0x00813023.
Lemma F_138e4 : fetch_word Plain.M.loaded_segments (0x138e4 : word) = Some W_138e4.
Proof. vm_refl. Qed.
Lemma D_138e4 : decode_any W_138e4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138e8 : bv 32 := 0x01010413.
Lemma F_138e8 : fetch_word Plain.M.loaded_segments (0x138e8 : word) = Some W_138e8.
Proof. vm_refl. Qed.
Lemma D_138e8 : decode_any W_138e8 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138ec : bv 32 := 0x00013517.
Lemma F_138ec : fetch_word Plain.M.loaded_segments (0x138ec : word) = Some W_138ec.
Proof. vm_refl. Qed.
Lemma D_138ec : decode_any W_138ec = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138f0 : bv 32 := 0xd5450513.
Lemma F_138f0 : fetch_word Plain.M.loaded_segments (0x138f0 : word) = Some W_138f0.
Proof. vm_refl. Qed.
Lemma D_138f0 : decode_any W_138f0 = Some (OpImm ALU_ADD 10 10 3412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138f4 : bv 32 := 0x00054503.
Lemma F_138f4 : fetch_word Plain.M.loaded_segments (0x138f4 : word) = Some W_138f4.
Proof. vm_refl. Qed.
Lemma D_138f4 : decode_any W_138f4 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138f8 : bv 32 := 0x00157513.
Lemma F_138f8 : fetch_word Plain.M.loaded_segments (0x138f8 : word) = Some W_138f8.
Proof. vm_refl. Qed.
Lemma D_138f8 : decode_any W_138f8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_138fc : bv 32 := 0x00050663.
Lemma F_138fc : fetch_word Plain.M.loaded_segments (0x138fc : word) = Some W_138fc.
Proof. vm_refl. Qed.
Lemma D_138fc : decode_any W_138fc = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13908 : bv 32 := 0x00013517.
Lemma F_13908 : fetch_word Plain.M.loaded_segments (0x13908 : word) = Some W_13908.
Proof. vm_refl. Qed.
Lemma D_13908 : decode_any W_13908 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1390c : bv 32 := 0xd3850593.
Lemma F_1390c : fetch_word Plain.M.loaded_segments (0x1390c : word) = Some W_1390c.
Proof. vm_refl. Qed.
Lemma D_1390c : decode_any W_1390c = Some (OpImm ALU_ADD 11 10 3384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13910 : bv 32 := 0x00100513.
Lemma F_13910 : fetch_word Plain.M.loaded_segments (0x13910 : word) = Some W_13910.
Proof. vm_refl. Qed.
Lemma D_13910 : decode_any W_13910 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13914 : bv 32 := 0x00a58023.
Lemma F_13914 : fetch_word Plain.M.loaded_segments (0x13914 : word) = Some W_13914.
Proof. vm_refl. Qed.
Lemma D_13914 : decode_any W_13914 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13918 : bv 32 := 0x00012517.
Lemma F_13918 : fetch_word Plain.M.loaded_segments (0x13918 : word) = Some W_13918.
Proof. vm_refl. Qed.
Lemma D_13918 : decode_any W_13918 = Some (Auipc 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1391c : bv 32 := 0x9b053503.
Lemma F_1391c : fetch_word Plain.M.loaded_segments (0x1391c : word) = Some W_1391c.
Proof. vm_refl. Qed.
Lemma D_1391c : decode_any W_1391c = Some (Load SZ8 true 10 10 2480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13920 : bv 32 := 0x02050063.
Lemma F_13920 : fetch_word Plain.M.loaded_segments (0x13920 : word) = Some W_13920.
Proof. vm_refl. Qed.
Lemma D_13920 : decode_any W_13920 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13940 : bv 32 := 0x00813083.
Lemma F_13940 : fetch_word Plain.M.loaded_segments (0x13940 : word) = Some W_13940.
Proof. vm_refl. Qed.
Lemma D_13940 : decode_any W_13940 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13944 : bv 32 := 0x00013403.
Lemma F_13944 : fetch_word Plain.M.loaded_segments (0x13944 : word) = Some W_13944.
Proof. vm_refl. Qed.
Lemma D_13944 : decode_any W_13944 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13948 : bv 32 := 0x01010113.
Lemma F_13948 : fetch_word Plain.M.loaded_segments (0x13948 : word) = Some W_13948.
Proof. vm_refl. Qed.
Lemma D_13948 : decode_any W_13948 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1394c : bv 32 := 0x00008067.
Lemma F_1394c : fetch_word Plain.M.loaded_segments (0x1394c : word) = Some W_1394c.
Proof. vm_refl. Qed.
Lemma D_1394c : decode_any W_1394c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13950 : bv 32 := 0xff010113.
Lemma F_13950 : fetch_word Plain.M.loaded_segments (0x13950 : word) = Some W_13950.
Proof. vm_refl. Qed.
Lemma D_13950 : decode_any W_13950 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13954 : bv 32 := 0x00113423.
Lemma F_13954 : fetch_word Plain.M.loaded_segments (0x13954 : word) = Some W_13954.
Proof. vm_refl. Qed.
Lemma D_13954 : decode_any W_13954 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13958 : bv 32 := 0x00813023.
Lemma F_13958 : fetch_word Plain.M.loaded_segments (0x13958 : word) = Some W_13958.
Proof. vm_refl. Qed.
Lemma D_13958 : decode_any W_13958 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1395c : bv 32 := 0x01010413.
Lemma F_1395c : fetch_word Plain.M.loaded_segments (0x1395c : word) = Some W_1395c.
Proof. vm_refl. Qed.
Lemma D_1395c : decode_any W_1395c = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13960 : bv 32 := 0x00013517.
Lemma F_13960 : fetch_word Plain.M.loaded_segments (0x13960 : word) = Some W_13960.
Proof. vm_refl. Qed.
Lemma D_13960 : decode_any W_13960 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13964 : bv 32 := 0xd2850513.
Lemma F_13964 : fetch_word Plain.M.loaded_segments (0x13964 : word) = Some W_13964.
Proof. vm_refl. Qed.
Lemma D_13964 : decode_any W_13964 = Some (OpImm ALU_ADD 10 10 3368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13968 : bv 32 := 0x00054503.
Lemma F_13968 : fetch_word Plain.M.loaded_segments (0x13968 : word) = Some W_13968.
Proof. vm_refl. Qed.
Lemma D_13968 : decode_any W_13968 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1396c : bv 32 := 0x00157513.
Lemma F_1396c : fetch_word Plain.M.loaded_segments (0x1396c : word) = Some W_1396c.
Proof. vm_refl. Qed.
Lemma D_1396c : decode_any W_1396c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13970 : bv 32 := 0x00050663.
Lemma F_13970 : fetch_word Plain.M.loaded_segments (0x13970 : word) = Some W_13970.
Proof. vm_refl. Qed.
Lemma D_13970 : decode_any W_13970 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1397c : bv 32 := 0x00013517.
Lemma F_1397c : fetch_word Plain.M.loaded_segments (0x1397c : word) = Some W_1397c.
Proof. vm_refl. Qed.
Lemma D_1397c : decode_any W_1397c = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13980 : bv 32 := 0xd0c50593.
Lemma F_13980 : fetch_word Plain.M.loaded_segments (0x13980 : word) = Some W_13980.
Proof. vm_refl. Qed.
Lemma D_13980 : decode_any W_13980 = Some (OpImm ALU_ADD 11 10 3340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13984 : bv 32 := 0x00100513.
Lemma F_13984 : fetch_word Plain.M.loaded_segments (0x13984 : word) = Some W_13984.
Proof. vm_refl. Qed.
Lemma D_13984 : decode_any W_13984 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13988 : bv 32 := 0x00a58023.
Lemma F_13988 : fetch_word Plain.M.loaded_segments (0x13988 : word) = Some W_13988.
Proof. vm_refl. Qed.
Lemma D_13988 : decode_any W_13988 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1398c : bv 32 := 0x00012517.
Lemma F_1398c : fetch_word Plain.M.loaded_segments (0x1398c : word) = Some W_1398c.
Proof. vm_refl. Qed.
Lemma D_1398c : decode_any W_1398c = Some (Auipc 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13990 : bv 32 := 0x94453503.
Lemma F_13990 : fetch_word Plain.M.loaded_segments (0x13990 : word) = Some W_13990.
Proof. vm_refl. Qed.
Lemma D_13990 : decode_any W_13990 = Some (Load SZ8 true 10 10 2372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13994 : bv 32 := 0x00050e63.
Lemma F_13994 : fetch_word Plain.M.loaded_segments (0x13994 : word) = Some W_13994.
Proof. vm_refl. Qed.
Lemma D_13994 : decode_any W_13994 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13998 : bv 32 := 0x0040006f.
Lemma F_13998 : fetch_word Plain.M.loaded_segments (0x13998 : word) = Some W_13998.
Proof. vm_refl. Qed.
Lemma D_13998 : decode_any W_13998 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1399c : bv 32 := 0x00013517.
Lemma F_1399c : fetch_word Plain.M.loaded_segments (0x1399c : word) = Some W_1399c.
Proof. vm_refl. Qed.
Lemma D_1399c : decode_any W_1399c = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a0 : bv 32 := 0x99c50513.
Lemma F_139a0 : fetch_word Plain.M.loaded_segments (0x139a0 : word) = Some W_139a0.
Proof. vm_refl. Qed.
Lemma D_139a0 : decode_any W_139a0 = Some (OpImm ALU_ADD 10 10 2460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a4 : bv 32 := 0x00053503.
Lemma F_139a4 : fetch_word Plain.M.loaded_segments (0x139a4 : word) = Some W_139a4.
Proof. vm_refl. Qed.
Lemma D_139a4 : decode_any W_139a4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a8 : bv 32 := 0x034080ef.
Lemma F_139a8 : fetch_word Plain.M.loaded_segments (0x139a8 : word) = Some W_139a8.
Proof. vm_refl. Qed.
Lemma D_139a8 : decode_any W_139a8 = Some (Jal 1 32820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139ac : bv 32 := 0x0040006f.
Lemma F_139ac : fetch_word Plain.M.loaded_segments (0x139ac : word) = Some W_139ac.
Proof. vm_refl. Qed.
Lemma D_139ac : decode_any W_139ac = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b0 : bv 32 := 0x00012517.
Lemma F_139b0 : fetch_word Plain.M.loaded_segments (0x139b0 : word) = Some W_139b0.
Proof. vm_refl. Qed.
Lemma D_139b0 : decode_any W_139b0 = Some (Auipc 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b4 : bv 32 := 0x92853503.
Lemma F_139b4 : fetch_word Plain.M.loaded_segments (0x139b4 : word) = Some W_139b4.
Proof. vm_refl. Qed.
Lemma D_139b4 : decode_any W_139b4 = Some (Load SZ8 true 10 10 2344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b8 : bv 32 := 0x00050c63.
Lemma F_139b8 : fetch_word Plain.M.loaded_segments (0x139b8 : word) = Some W_139b8.
Proof. vm_refl. Qed.
Lemma D_139b8 : decode_any W_139b8 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d0 : bv 32 := 0x00813083.
Lemma F_139d0 : fetch_word Plain.M.loaded_segments (0x139d0 : word) = Some W_139d0.
Proof. vm_refl. Qed.
Lemma D_139d0 : decode_any W_139d0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d4 : bv 32 := 0x00013403.
Lemma F_139d4 : fetch_word Plain.M.loaded_segments (0x139d4 : word) = Some W_139d4.
Proof. vm_refl. Qed.
Lemma D_139d4 : decode_any W_139d4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d8 : bv 32 := 0x01010113.
Lemma F_139d8 : fetch_word Plain.M.loaded_segments (0x139d8 : word) = Some W_139d8.
Proof. vm_refl. Qed.
Lemma D_139d8 : decode_any W_139d8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139dc : bv 32 := 0x00008067.
Lemma F_139dc : fetch_word Plain.M.loaded_segments (0x139dc : word) = Some W_139dc.
Proof. vm_refl. Qed.
Lemma D_139dc : decode_any W_139dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a34 : bv 32 := 0x24050a63.
Lemma F_13a34 : fetch_word Plain.M.loaded_segments (0x13a34 : word) = Some W_13a34.
Proof. vm_refl. Qed.
Lemma D_13a34 : decode_any W_13a34 = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a38 : bv 32 := 0x00050b93.
Lemma F_13a38 : fetch_word Plain.M.loaded_segments (0x13a38 : word) = Some W_13a38.
Proof. vm_refl. Qed.
Lemma D_13a38 : decode_any W_13a38 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a3c : bv 32 := 0x00000993.
Lemma F_13a3c : fetch_word Plain.M.loaded_segments (0x13a3c : word) = Some W_13a3c.
Proof. vm_refl. Qed.
Lemma D_13a3c : decode_any W_13a3c = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a40 : bv 32 := 0x00013517.
Lemma F_13a40 : fetch_word Plain.M.loaded_segments (0x13a40 : word) = Some W_13a40.
Proof. vm_refl. Qed.
Lemma D_13a40 : decode_any W_13a40 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a44 : bv 32 := 0xc4950b13.
Lemma F_13a44 : fetch_word Plain.M.loaded_segments (0x13a44 : word) = Some W_13a44.
Proof. vm_refl. Qed.
Lemma D_13a44 : decode_any W_13a44 = Some (OpImm ALU_ADD 22 10 3145, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a48 : bv 32 := 0x03501263.
Lemma F_13a48 : fetch_word Plain.M.loaded_segments (0x13a48 : word) = Some W_13a48.
Proof. vm_refl. Qed.
Lemma D_13a48 : decode_any W_13a48 = Some (Branch BC_NE 0 21 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a50 : bv 32 := 0x01348533.
Lemma F_13a50 : fetch_word Plain.M.loaded_segments (0x13a50 : word) = Some W_13a50.
Proof. vm_refl. Qed.
Lemma D_13a50 : decode_any W_13a50 = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a54 : bv 32 := 0x000b0593.
Lemma F_13a54 : fetch_word Plain.M.loaded_segments (0x13a54 : word) = Some W_13a54.
Proof. vm_refl. Qed.
Lemma D_13a54 : decode_any W_13a54 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a58 : bv 32 := 0x000b8613.
Lemma F_13a58 : fetch_word Plain.M.loaded_segments (0x13a58 : word) = Some W_13a58.
Proof. vm_refl. Qed.
Lemma D_13a58 : decode_any W_13a58 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a5c : bv 32 := 0x3e50f0ef.
Lemma F_13a5c : fetch_word Plain.M.loaded_segments (0x13a5c : word) = Some W_13a5c.
Proof. vm_refl. Qed.
Lemma D_13a5c : decode_any W_13a5c = Some (Jal 1 64484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a60 : bv 32 := 0x013b89b3.
Lemma F_13a60 : fetch_word Plain.M.loaded_segments (0x13a60 : word) = Some W_13a60.
Proof. vm_refl. Qed.
Lemma D_13a60 : decode_any W_13a60 = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a64 : bv 32 := 0x00048b93.
Lemma F_13a64 : fetch_word Plain.M.loaded_segments (0x13a64 : word) = Some W_13a64.
Proof. vm_refl. Qed.
Lemma D_13a64 : decode_any W_13a64 = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a68 : bv 32 := 0x01598663.
Lemma F_13a68 : fetch_word Plain.M.loaded_segments (0x13a68 : word) = Some W_13a68.
Proof. vm_refl. Qed.
Lemma D_13a68 : decode_any W_13a68 = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a6c : bv 32 := 0x000b8493.
Lemma F_13a6c : fetch_word Plain.M.loaded_segments (0x13a6c : word) = Some W_13a6c.
Proof. vm_refl. Qed.
Lemma D_13a6c : decode_any W_13a6c = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a70 : bv 32 := 0x03c0006f.
Lemma F_13a70 : fetch_word Plain.M.loaded_segments (0x13a70 : word) = Some W_13a70.
Proof. vm_refl. Qed.
Lemma D_13a70 : decode_any W_13a70 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13aac : bv 32 := 0x413a8633.
Lemma F_13aac : fetch_word Plain.M.loaded_segments (0x13aac : word) = Some W_13aac.
Proof. vm_refl. Qed.
Lemma D_13aac : decode_any W_13aac = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab0 : bv 32 := 0x00010537.
Lemma F_13ab0 : fetch_word Plain.M.loaded_segments (0x13ab0 : word) = Some W_13ab0.
Proof. vm_refl. Qed.
Lemma D_13ab0 : decode_any W_13ab0 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab4 : bv 32 := 0x00a66463.
Lemma F_13ab4 : fetch_word Plain.M.loaded_segments (0x13ab4 : word) = Some W_13ab4.
Proof. vm_refl. Qed.
Lemma D_13ab4 : decode_any W_13ab4 = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab8 : bv 32 := 0x00010637.
Lemma F_13ab8 : fetch_word Plain.M.loaded_segments (0x13ab8 : word) = Some W_13ab8.
Proof. vm_refl. Qed.
Lemma D_13ab8 : decode_any W_13ab8 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13abc : bv 32 := 0x000a0513.
Lemma F_13abc : fetch_word Plain.M.loaded_segments (0x13abc : word) = Some W_13abc.
Proof. vm_refl. Qed.
Lemma D_13abc : decode_any W_13abc = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac0 : bv 32 := 0x000b0593.
Lemma F_13ac0 : fetch_word Plain.M.loaded_segments (0x13ac0 : word) = Some W_13ac0.
Proof. vm_refl. Qed.
Lemma D_13ac0 : decode_any W_13ac0 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac4 : bv 32 := 0x784100ef.
Lemma F_13ac4 : fetch_word Plain.M.loaded_segments (0x13ac4 : word) = Some W_13ac4.
Proof. vm_refl. Qed.
Lemma D_13ac4 : decode_any W_13ac4 = Some (Jal 1 67460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ac8 : bv 32 := 0x14054263.
Lemma F_13ac8 : fetch_word Plain.M.loaded_segments (0x13ac8 : word) = Some W_13ac8.
Proof. vm_refl. Qed.
Lemma D_13ac8 : decode_any W_13ac8 = Some (Branch BC_LT 10 0 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13acc : bv 32 := 0x00050b93.
Lemma F_13acc : fetch_word Plain.M.loaded_segments (0x13acc : word) = Some W_13acc.
Proof. vm_refl. Qed.
Lemma D_13acc : decode_any W_13acc = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad0 : bv 32 := 0xf80510e3.
Lemma F_13ad0 : fetch_word Plain.M.loaded_segments (0x13ad0 : word) = Some W_13ad0.
Proof. vm_refl. Qed.
Lemma D_13ad0 : decode_any W_13ad0 = Some (Branch BC_NE 10 0 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad4 : bv 32 := 0x000a0513.
Lemma F_13ad4 : fetch_word Plain.M.loaded_segments (0x13ad4 : word) = Some W_13ad4.
Proof. vm_refl. Qed.
Lemma D_13ad4 : decode_any W_13ad4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ad8 : bv 32 := 0x710100ef.
Lemma F_13ad8 : fetch_word Plain.M.loaded_segments (0x13ad8 : word) = Some W_13ad8.
Proof. vm_refl. Qed.
Lemma D_13ad8 : decode_any W_13ad8 = Some (Jal 1 67344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b54 : bv 32 := 0x000ac663.
Lemma F_13b54 : fetch_word Plain.M.loaded_segments (0x13b54 : word) = Some W_13b54.
Proof. vm_refl. Qed.
Lemma D_13b54 : decode_any W_13b54 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b58 : bv 32 := 0x00050413.
Lemma F_13b58 : fetch_word Plain.M.loaded_segments (0x13b58 : word) = Some W_13b58.
Proof. vm_refl. Qed.
Lemma D_13b58 : decode_any W_13b58 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b5c : bv 32 := 0x0780006f.
Lemma F_13b5c : fetch_word Plain.M.loaded_segments (0x13b5c : word) = Some W_13b5c.
Proof. vm_refl. Qed.
Lemma D_13b5c : decode_any W_13b5c = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b60 : bv 32 := 0x148000ef.
Lemma F_13b60 : fetch_word Plain.M.loaded_segments (0x13b60 : word) = Some W_13b60.
Proof. vm_refl. Qed.
Lemma D_13b60 : decode_any W_13b60 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b64 : bv 32 := 0x0fb00593.
Lemma F_13b64 : fetch_word Plain.M.loaded_segments (0x13b64 : word) = Some W_13b64.
Proof. vm_refl. Qed.
Lemma D_13b64 : decode_any W_13b64 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b68 : bv 32 := 0x00050413.
Lemma F_13b68 : fetch_word Plain.M.loaded_segments (0x13b68 : word) = Some W_13b68.
Proof. vm_refl. Qed.
Lemma D_13b68 : decode_any W_13b68 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b6c : bv 32 := 0x06b56463.
Lemma F_13b6c : fetch_word Plain.M.loaded_segments (0x13b6c : word) = Some W_13b6c.
Proof. vm_refl. Qed.
Lemma D_13b6c : decode_any W_13b6c = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca8 : bv 32 := 0x00000513.
Lemma F_13ca8 : fetch_word Plain.M.loaded_segments (0x13ca8 : word) = Some W_13ca8.
Proof. vm_refl. Qed.
Lemma D_13ca8 : decode_any W_13ca8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cac : bv 32 := 0x00008067.
Lemma F_13cac : fetch_word Plain.M.loaded_segments (0x13cac : word) = Some W_13cac.
Proof. vm_refl. Qed.
Lemma D_13cac : decode_any W_13cac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
