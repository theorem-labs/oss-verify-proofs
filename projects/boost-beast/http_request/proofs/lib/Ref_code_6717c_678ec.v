(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6717c : bv 32 := 0xfc010113.
Lemma F_6717c : fetch_word Plain.M.loaded_segments (0x6717c : word) = Some W_6717c.
Proof. vm_refl. Qed.
Lemma D_6717c : decode_any W_6717c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67180 : bv 32 := 0x02113c23.
Lemma F_67180 : fetch_word Plain.M.loaded_segments (0x67180 : word) = Some W_67180.
Proof. vm_refl. Qed.
Lemma D_67180 : decode_any W_67180 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67184 : bv 32 := 0x02813823.
Lemma F_67184 : fetch_word Plain.M.loaded_segments (0x67184 : word) = Some W_67184.
Proof. vm_refl. Qed.
Lemma D_67184 : decode_any W_67184 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67188 : bv 32 := 0x02913423.
Lemma F_67188 : fetch_word Plain.M.loaded_segments (0x67188 : word) = Some W_67188.
Proof. vm_refl. Qed.
Lemma D_67188 : decode_any W_67188 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6718c : bv 32 := 0x03213023.
Lemma F_6718c : fetch_word Plain.M.loaded_segments (0x6718c : word) = Some W_6718c.
Proof. vm_refl. Qed.
Lemma D_6718c : decode_any W_6718c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67190 : bv 32 := 0x01313c23.
Lemma F_67190 : fetch_word Plain.M.loaded_segments (0x67190 : word) = Some W_67190.
Proof. vm_refl. Qed.
Lemma D_67190 : decode_any W_67190 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67194 : bv 32 := 0x01413823.
Lemma F_67194 : fetch_word Plain.M.loaded_segments (0x67194 : word) = Some W_67194.
Proof. vm_refl. Qed.
Lemma D_67194 : decode_any W_67194 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67198 : bv 32 := 0x01513423.
Lemma F_67198 : fetch_word Plain.M.loaded_segments (0x67198 : word) = Some W_67198.
Proof. vm_refl. Qed.
Lemma D_67198 : decode_any W_67198 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6719c : bv 32 := 0x0004b597.
Lemma F_6719c : fetch_word Plain.M.loaded_segments (0x6719c : word) = Some W_6719c.
Proof. vm_refl. Qed.
Lemma D_6719c : decode_any W_6719c = Some (Auipc 11 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671a0 : bv 32 := 0xf3800693.
Lemma F_671a0 : fetch_word Plain.M.loaded_segments (0x671a0 : word) = Some W_671a0.
Proof. vm_refl. Qed.
Lemma D_671a0 : decode_any W_671a0 = Some (OpImm ALU_ADD 13 0 3896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671a4 : bv 32 := 0x74458493.
Lemma F_671a4 : fetch_word Plain.M.loaded_segments (0x671a4 : word) = Some W_671a4.
Proof. vm_refl. Qed.
Lemma D_671a4 : decode_any W_671a4 = Some (OpImm ALU_ADD 9 11 1860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671a8 : bv 32 := 0x0104b903.
Lemma F_671a8 : fetch_word Plain.M.loaded_segments (0x671a8 : word) = Some W_671a8.
Proof. vm_refl. Qed.
Lemma D_671a8 : decode_any W_671a8 = Some (Load SZ8 true 18 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671ac : bv 32 := 0x0184b603.
Lemma F_671ac : fetch_word Plain.M.loaded_segments (0x671ac : word) = Some W_671ac.
Proof. vm_refl. Qed.
Lemma D_671ac : decode_any W_671ac = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671b0 : bv 32 := 0x0204b703.
Lemma F_671b0 : fetch_word Plain.M.loaded_segments (0x671b0 : word) = Some W_671b0.
Proof. vm_refl. Qed.
Lemma D_671b0 : decode_any W_671b0 = Some (Load SZ8 true 14 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671b4 : bv 32 := 0x40a686b3.
Lemma F_671b4 : fetch_word Plain.M.loaded_segments (0x671b4 : word) = Some W_671b4.
Proof. vm_refl. Qed.
Lemma D_671b4 : decode_any W_671b4 = Some (Op ALU_SUB 13 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671b8 : bv 32 := 0x0284b583.
Lemma F_671b8 : fetch_word Plain.M.loaded_segments (0x671b8 : word) = Some W_671b8.
Proof. vm_refl. Qed.
Lemma D_671b8 : decode_any W_671b8 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671bc : bv 32 := 0x00c509b3.
Lemma F_671bc : fetch_word Plain.M.loaded_segments (0x671bc : word) = Some W_671bc.
Proof. vm_refl. Qed.
Lemma D_671bc : decode_any W_671bc = Some (Op ALU_ADD 19 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671c0 : bv 32 := 0xfff70713.
Lemma F_671c0 : fetch_word Plain.M.loaded_segments (0x671c0 : word) = Some W_671c0.
Proof. vm_refl. Qed.
Lemma D_671c0 : decode_any W_671c0 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671c4 : bv 32 := 0x00d776b3.
Lemma F_671c4 : fetch_word Plain.M.loaded_segments (0x671c4 : word) = Some W_671c4.
Proof. vm_refl. Qed.
Lemma D_671c4 : decode_any W_671c4 = Some (Op ALU_AND 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671c8 : bv 32 := 0xfff5c713.
Lemma F_671c8 : fetch_word Plain.M.loaded_segments (0x671c8 : word) = Some W_671c8.
Proof. vm_refl. Qed.
Lemma D_671c8 : decode_any W_671c8 = Some (OpImm ALU_XOR 14 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671cc : bv 32 := 0x00371713.
Lemma F_671cc : fetch_word Plain.M.loaded_segments (0x671cc : word) = Some W_671cc.
Proof. vm_refl. Qed.
Lemma D_671cc : decode_any W_671cc = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671d0 : bv 32 := 0x00e989b3.
Lemma F_671d0 : fetch_word Plain.M.loaded_segments (0x671d0 : word) = Some W_671d0.
Proof. vm_refl. Qed.
Lemma D_671d0 : decode_any W_671d0 = Some (Op ALU_ADD 19 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671d4 : bv 32 := 0x00d50433.
Lemma F_671d4 : fetch_word Plain.M.loaded_segments (0x671d4 : word) = Some W_671d4.
Proof. vm_refl. Qed.
Lemma D_671d4 : decode_any W_671d4 = Some (Op ALU_ADD 8 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671d8 : bv 32 := 0x04090663.
Lemma F_671d8 : fetch_word Plain.M.loaded_segments (0x671d8 : word) = Some W_671d8.
Proof. vm_refl. Qed.
Lemma D_671d8 : decode_any W_671d8 = Some (Branch BC_EQ 18 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671dc : bv 32 := 0x0c840a13.
Lemma F_671dc : fetch_word Plain.M.loaded_segments (0x671dc : word) = Some W_671dc.
Proof. vm_refl. Qed.
Lemma D_671dc : decode_any W_671dc = Some (OpImm ALU_ADD 20 8 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671e0 : bv 32 := 0x00359593.
Lemma F_671e0 : fetch_word Plain.M.loaded_segments (0x671e0 : word) = Some W_671e0.
Proof. vm_refl. Qed.
Lemma D_671e0 : decode_any W_671e0 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671e4 : bv 32 := 0x00c50533.
Lemma F_671e4 : fetch_word Plain.M.loaded_segments (0x671e4 : word) = Some W_671e4.
Proof. vm_refl. Qed.
Lemma D_671e4 : decode_any W_671e4 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671e8 : bv 32 := 0x40b50ab3.
Lemma F_671e8 : fetch_word Plain.M.loaded_segments (0x671e8 : word) = Some W_671e8.
Proof. vm_refl. Qed.
Lemma D_671e8 : decode_any W_671e8 = Some (Op ALU_SUB 21 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671ec : bv 32 := 0x02893503.
Lemma F_671ec : fetch_word Plain.M.loaded_segments (0x671ec : word) = Some W_671ec.
Proof. vm_refl. Qed.
Lemma D_671ec : decode_any W_671ec = Some (Load SZ8 true 10 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671f0 : bv 32 := 0x00aa0533.
Lemma F_671f0 : fetch_word Plain.M.loaded_segments (0x671f0 : word) = Some W_671f0.
Proof. vm_refl. Qed.
Lemma D_671f0 : decode_any W_671f0 = Some (Op ALU_ADD 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671f4 : bv 32 := 0x7ff50513.
Lemma F_671f4 : fetch_word Plain.M.loaded_segments (0x671f4 : word) = Some W_671f4.
Proof. vm_refl. Qed.
Lemma D_671f4 : decode_any W_671f4 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671f8 : bv 32 := 0x00150513.
Lemma F_671f8 : fetch_word Plain.M.loaded_segments (0x671f8 : word) = Some W_671f8.
Proof. vm_refl. Qed.
Lemma D_671f8 : decode_any W_671f8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_671fc : bv 32 := 0x00aab023.
Lemma F_671fc : fetch_word Plain.M.loaded_segments (0x671fc : word) = Some W_671fc.
Proof. vm_refl. Qed.
Lemma D_671fc : decode_any W_671fc = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67200 : bv 32 := 0x02893503.
Lemma F_67200 : fetch_word Plain.M.loaded_segments (0x67200 : word) = Some W_67200.
Proof. vm_refl. Qed.
Lemma D_67200 : decode_any W_67200 = Some (Load SZ8 true 10 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67204 : bv 32 := 0x00893583.
Lemma F_67204 : fetch_word Plain.M.loaded_segments (0x67204 : word) = Some W_67204.
Proof. vm_refl. Qed.
Lemma D_67204 : decode_any W_67204 = Some (Load SZ8 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67208 : bv 32 := 0x01093603.
Lemma F_67208 : fetch_word Plain.M.loaded_segments (0x67208 : word) = Some W_67208.
Proof. vm_refl. Qed.
Lemma D_67208 : decode_any W_67208 = Some (Load SZ8 true 12 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6720c : bv 32 := 0x00aa0533.
Lemma F_6720c : fetch_word Plain.M.loaded_segments (0x6720c : word) = Some W_6720c.
Proof. vm_refl. Qed.
Lemma D_6720c : decode_any W_6720c = Some (Op ALU_ADD 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67210 : bv 32 := 0x0140e0ef.
Lemma F_67210 : fetch_word Plain.M.loaded_segments (0x67210 : word) = Some W_67210.
Proof. vm_refl. Qed.
Lemma D_67210 : decode_any W_67210 = Some (Jal 1 57364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67214 : bv 32 := 0x00093903.
Lemma F_67214 : fetch_word Plain.M.loaded_segments (0x67214 : word) = Some W_67214.
Proof. vm_refl. Qed.
Lemma D_67214 : decode_any W_67214 = Some (Load SZ8 true 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67218 : bv 32 := 0x008a8a93.
Lemma F_67218 : fetch_word Plain.M.loaded_segments (0x67218 : word) = Some W_67218.
Proof. vm_refl. Qed.
Lemma D_67218 : decode_any W_67218 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6721c : bv 32 := 0xfc0918e3.
Lemma F_6721c : fetch_word Plain.M.loaded_segments (0x6721c : word) = Some W_6721c.
Proof. vm_refl. Qed.
Lemma D_6721c : decode_any W_6721c = Some (Branch BC_NE 18 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67220 : bv 32 := 0x0284b583.
Lemma F_67220 : fetch_word Plain.M.loaded_segments (0x67220 : word) = Some W_67220.
Proof. vm_refl. Qed.
Lemma D_67220 : decode_any W_67220 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67224 : bv 32 := 0x00b9b023.
Lemma F_67224 : fetch_word Plain.M.loaded_segments (0x67224 : word) = Some W_67224.
Proof. vm_refl. Qed.
Lemma D_67224 : decode_any W_67224 = Some (Store SZ8 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67228 : bv 32 := 0x0d343023.
Lemma F_67228 : fetch_word Plain.M.loaded_segments (0x67228 : word) = Some W_67228.
Proof. vm_refl. Qed.
Lemma D_67228 : decode_any W_67228 = Some (Store SZ8 8 19 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6722c : bv 32 := 0x00040513.
Lemma F_6722c : fetch_word Plain.M.loaded_segments (0x6722c : word) = Some W_6722c.
Proof. vm_refl. Qed.
Lemma D_6722c : decode_any W_6722c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67230 : bv 32 := 0x03813083.
Lemma F_67230 : fetch_word Plain.M.loaded_segments (0x67230 : word) = Some W_67230.
Proof. vm_refl. Qed.
Lemma D_67230 : decode_any W_67230 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67234 : bv 32 := 0x03013403.
Lemma F_67234 : fetch_word Plain.M.loaded_segments (0x67234 : word) = Some W_67234.
Proof. vm_refl. Qed.
Lemma D_67234 : decode_any W_67234 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67238 : bv 32 := 0x02813483.
Lemma F_67238 : fetch_word Plain.M.loaded_segments (0x67238 : word) = Some W_67238.
Proof. vm_refl. Qed.
Lemma D_67238 : decode_any W_67238 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6723c : bv 32 := 0x02013903.
Lemma F_6723c : fetch_word Plain.M.loaded_segments (0x6723c : word) = Some W_6723c.
Proof. vm_refl. Qed.
Lemma D_6723c : decode_any W_6723c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67240 : bv 32 := 0x01813983.
Lemma F_67240 : fetch_word Plain.M.loaded_segments (0x67240 : word) = Some W_67240.
Proof. vm_refl. Qed.
Lemma D_67240 : decode_any W_67240 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67244 : bv 32 := 0x01013a03.
Lemma F_67244 : fetch_word Plain.M.loaded_segments (0x67244 : word) = Some W_67244.
Proof. vm_refl. Qed.
Lemma D_67244 : decode_any W_67244 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67248 : bv 32 := 0x00813a83.
Lemma F_67248 : fetch_word Plain.M.loaded_segments (0x67248 : word) = Some W_67248.
Proof. vm_refl. Qed.
Lemma D_67248 : decode_any W_67248 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6724c : bv 32 := 0x04010113.
Lemma F_6724c : fetch_word Plain.M.loaded_segments (0x6724c : word) = Some W_6724c.
Proof. vm_refl. Qed.
Lemma D_6724c : decode_any W_6724c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67250 : bv 32 := 0x00008067.
Lemma F_67250 : fetch_word Plain.M.loaded_segments (0x67250 : word) = Some W_67250.
Proof. vm_refl. Qed.
Lemma D_67250 : decode_any W_67250 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67504 : bv 32 := 0xff010113.
Lemma F_67504 : fetch_word Plain.M.loaded_segments (0x67504 : word) = Some W_67504.
Proof. vm_refl. Qed.
Lemma D_67504 : decode_any W_67504 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67508 : bv 32 := 0x00113423.
Lemma F_67508 : fetch_word Plain.M.loaded_segments (0x67508 : word) = Some W_67508.
Proof. vm_refl. Qed.
Lemma D_67508 : decode_any W_67508 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6750c : bv 32 := 0x00050e63.
Lemma F_6750c : fetch_word Plain.M.loaded_segments (0x6750c : word) = Some W_6750c.
Proof. vm_refl. Qed.
Lemma D_6750c : decode_any W_6750c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67510 : bv 32 := 0x00050593.
Lemma F_67510 : fetch_word Plain.M.loaded_segments (0x67510 : word) = Some W_67510.
Proof. vm_refl. Qed.
Lemma D_67510 : decode_any W_67510 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67514 : bv 32 := 0x00018517.
Lemma F_67514 : fetch_word Plain.M.loaded_segments (0x67514 : word) = Some W_67514.
Proof. vm_refl. Qed.
Lemma D_67514 : decode_any W_67514 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67518 : bv 32 := 0x2f453503.
Lemma F_67518 : fetch_word Plain.M.loaded_segments (0x67518 : word) = Some W_67518.
Proof. vm_refl. Qed.
Lemma D_67518 : decode_any W_67518 = Some (Load SZ8 true 10 10 756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6751c : bv 32 := 0x00800613.
Lemma F_6751c : fetch_word Plain.M.loaded_segments (0x6751c : word) = Some W_6751c.
Proof. vm_refl. Qed.
Lemma D_6751c : decode_any W_6751c = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67520 : bv 32 := 0x5050d0ef.
Lemma F_67520 : fetch_word Plain.M.loaded_segments (0x67520 : word) = Some W_67520.
Proof. vm_refl. Qed.
Lemma D_67520 : decode_any W_67520 = Some (Jal 1 56580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67524 : bv 32 := 0x01c0006f.
Lemma F_67524 : fetch_word Plain.M.loaded_segments (0x67524 : word) = Some W_67524.
Proof. vm_refl. Qed.
Lemma D_67524 : decode_any W_67524 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67528 : bv 32 := 0x00018517.
Lemma F_67528 : fetch_word Plain.M.loaded_segments (0x67528 : word) = Some W_67528.
Proof. vm_refl. Qed.
Lemma D_67528 : decode_any W_67528 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6752c : bv 32 := 0x2e053503.
Lemma F_6752c : fetch_word Plain.M.loaded_segments (0x6752c : word) = Some W_6752c.
Proof. vm_refl. Qed.
Lemma D_6752c : decode_any W_6752c = Some (Load SZ8 true 10 10 736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67530 : bv 32 := 0x41c655b7.
Lemma F_67530 : fetch_word Plain.M.loaded_segments (0x67530 : word) = Some W_67530.
Proof. vm_refl. Qed.
Lemma D_67530 : decode_any W_67530 = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67534 : bv 32 := 0xe6d5859b.
Lemma F_67534 : fetch_word Plain.M.loaded_segments (0x67534 : word) = Some W_67534.
Proof. vm_refl. Qed.
Lemma D_67534 : decode_any W_67534 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67538 : bv 32 := 0x02b505b3.
Lemma F_67538 : fetch_word Plain.M.loaded_segments (0x67538 : word) = Some W_67538.
Proof. vm_refl. Qed.
Lemma D_67538 : decode_any W_67538 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6753c : bv 32 := 0x00b53023.
Lemma F_6753c : fetch_word Plain.M.loaded_segments (0x6753c : word) = Some W_6753c.
Proof. vm_refl. Qed.
Lemma D_6753c : decode_any W_6753c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67540 : bv 32 := 0x00018517.
Lemma F_67540 : fetch_word Plain.M.loaded_segments (0x67540 : word) = Some W_67540.
Proof. vm_refl. Qed.
Lemma D_67540 : decode_any W_67540 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67544 : bv 32 := 0x2c853503.
Lemma F_67544 : fetch_word Plain.M.loaded_segments (0x67544 : word) = Some W_67544.
Proof. vm_refl. Qed.
Lemma D_67544 : decode_any W_67544 = Some (Load SZ8 true 10 10 712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67548 : bv 32 := 0x000500a3.
Lemma F_67548 : fetch_word Plain.M.loaded_segments (0x67548 : word) = Some W_67548.
Proof. vm_refl. Qed.
Lemma D_67548 : decode_any W_67548 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6754c : bv 32 := 0x00053503.
Lemma F_6754c : fetch_word Plain.M.loaded_segments (0x6754c : word) = Some W_6754c.
Proof. vm_refl. Qed.
Lemma D_6754c : decode_any W_6754c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67550 : bv 32 := 0x00020593.
Lemma F_67550 : fetch_word Plain.M.loaded_segments (0x67550 : word) = Some W_67550.
Proof. vm_refl. Qed.
Lemma D_67550 : decode_any W_67550 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67554 : bv 32 := 0xfea5b823.
Lemma F_67554 : fetch_word Plain.M.loaded_segments (0x67554 : word) = Some W_67554.
Proof. vm_refl. Qed.
Lemma D_67554 : decode_any W_67554 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67558 : bv 32 := 0x00813083.
Lemma F_67558 : fetch_word Plain.M.loaded_segments (0x67558 : word) = Some W_67558.
Proof. vm_refl. Qed.
Lemma D_67558 : decode_any W_67558 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6755c : bv 32 := 0x01010113.
Lemma F_6755c : fetch_word Plain.M.loaded_segments (0x6755c : word) = Some W_6755c.
Proof. vm_refl. Qed.
Lemma D_6755c : decode_any W_6755c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67560 : bv 32 := 0x00008067.
Lemma F_67560 : fetch_word Plain.M.loaded_segments (0x67560 : word) = Some W_67560.
Proof. vm_refl. Qed.
Lemma D_67560 : decode_any W_67560 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67564 : bv 32 := 0x00000023.
Lemma F_67564 : fetch_word Plain.M.loaded_segments (0x67564 : word) = Some W_67564.
Proof. vm_refl. Qed.
Lemma D_67564 : decode_any W_67564 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67568 : bv 32 := 0x00008067.
Lemma F_67568 : fetch_word Plain.M.loaded_segments (0x67568 : word) = Some W_67568.
Proof. vm_refl. Qed.
Lemma D_67568 : decode_any W_67568 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6756c : bv 32 := 0x00020513.
Lemma F_6756c : fetch_word Plain.M.loaded_segments (0x6756c : word) = Some W_6756c.
Proof. vm_refl. Qed.
Lemma D_6756c : decode_any W_6756c = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67570 : bv 32 := 0xf5c50513.
Lemma F_67570 : fetch_word Plain.M.loaded_segments (0x67570 : word) = Some W_67570.
Proof. vm_refl. Qed.
Lemma D_67570 : decode_any W_67570 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67574 : bv 32 := 0x00008067.
Lemma F_67574 : fetch_word Plain.M.loaded_segments (0x67574 : word) = Some W_67574.
Proof. vm_refl. Qed.
Lemma D_67574 : decode_any W_67574 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67578 : bv 32 := 0x00020593.
Lemma F_67578 : fetch_word Plain.M.loaded_segments (0x67578 : word) = Some W_67578.
Proof. vm_refl. Qed.
Lemma D_67578 : decode_any W_67578 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6757c : bv 32 := 0x08453613.
Lemma F_6757c : fetch_word Plain.M.loaded_segments (0x6757c : word) = Some W_6757c.
Proof. vm_refl. Qed.
Lemma D_6757c : decode_any W_6757c = Some (OpImm ALU_SLTU 12 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67580 : bv 32 := 0x40c00633.
Lemma F_67580 : fetch_word Plain.M.loaded_segments (0x67580 : word) = Some W_67580.
Proof. vm_refl. Qed.
Lemma D_67580 : decode_any W_67580 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67584 : bv 32 := 0x00a67533.
Lemma F_67584 : fetch_word Plain.M.loaded_segments (0x67584 : word) = Some W_67584.
Proof. vm_refl. Qed.
Lemma D_67584 : decode_any W_67584 = Some (Op ALU_AND 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67588 : bv 32 := 0xfffb1617.
Lemma F_67588 : fetch_word Plain.M.loaded_segments (0x67588 : word) = Some W_67588.
Proof. vm_refl. Qed.
Lemma D_67588 : decode_any W_67588 = Some (Auipc 12 1048497, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6758c : bv 32 := 0xfd05b583.
Lemma F_6758c : fetch_word Plain.M.loaded_segments (0x6758c : word) = Some W_6758c.
Proof. vm_refl. Qed.
Lemma D_6758c : decode_any W_6758c = Some (Load SZ8 true 11 11 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67590 : bv 32 := 0x00151513.
Lemma F_67590 : fetch_word Plain.M.loaded_segments (0x67590 : word) = Some W_67590.
Proof. vm_refl. Qed.
Lemma D_67590 : decode_any W_67590 = Some (ShiftImm ALU_SLL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67594 : bv 32 := 0x7b660613.
Lemma F_67594 : fetch_word Plain.M.loaded_segments (0x67594 : word) = Some W_67594.
Proof. vm_refl. Qed.
Lemma D_67594 : decode_any W_67594 = Some (OpImm ALU_ADD 12 12 1974, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67598 : bv 32 := 0x00a60533.
Lemma F_67598 : fetch_word Plain.M.loaded_segments (0x67598 : word) = Some W_67598.
Proof. vm_refl. Qed.
Lemma D_67598 : decode_any W_67598 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6759c : bv 32 := 0x00055503.
Lemma F_6759c : fetch_word Plain.M.loaded_segments (0x6759c : word) = Some W_6759c.
Proof. vm_refl. Qed.
Lemma D_6759c : decode_any W_6759c = Some (Load SZ2 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675a0 : bv 32 := 0x0285b583.
Lemma F_675a0 : fetch_word Plain.M.loaded_segments (0x675a0 : word) = Some W_675a0.
Proof. vm_refl. Qed.
Lemma D_675a0 : decode_any W_675a0 = Some (Load SZ8 true 11 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675a4 : bv 32 := 0xfffb1617.
Lemma F_675a4 : fetch_word Plain.M.loaded_segments (0x675a4 : word) = Some W_675a4.
Proof. vm_refl. Qed.
Lemma D_675a4 : decode_any W_675a4 = Some (Auipc 12 1048497, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675a8 : bv 32 := 0xff260613.
Lemma F_675a8 : fetch_word Plain.M.loaded_segments (0x675a8 : word) = Some W_675a8.
Proof. vm_refl. Qed.
Lemma D_675a8 : decode_any W_675a8 = Some (OpImm ALU_ADD 12 12 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675ac : bv 32 := 0x00a60533.
Lemma F_675ac : fetch_word Plain.M.loaded_segments (0x675ac : word) = Some W_675ac.
Proof. vm_refl. Qed.
Lemma D_675ac : decode_any W_675ac = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675b0 : bv 32 := 0x1250006f.
Lemma F_675b0 : fetch_word Plain.M.loaded_segments (0x675b0 : word) = Some W_675b0.
Proof. vm_refl. Qed.
Lemma D_675b0 : decode_any W_675b0 = Some (Jal 0 2340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675b4 : bv 32 := 0xfd010113.
Lemma F_675b4 : fetch_word Plain.M.loaded_segments (0x675b4 : word) = Some W_675b4.
Proof. vm_refl. Qed.
Lemma D_675b4 : decode_any W_675b4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675b8 : bv 32 := 0x02113423.
Lemma F_675b8 : fetch_word Plain.M.loaded_segments (0x675b8 : word) = Some W_675b8.
Proof. vm_refl. Qed.
Lemma D_675b8 : decode_any W_675b8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675bc : bv 32 := 0x00600513.
Lemma F_675bc : fetch_word Plain.M.loaded_segments (0x675bc : word) = Some W_675bc.
Proof. vm_refl. Qed.
Lemma D_675bc : decode_any W_675bc = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675c0 : bv 32 := 0x775020ef.
Lemma F_675c0 : fetch_word Plain.M.loaded_segments (0x675c0 : word) = Some W_675c0.
Proof. vm_refl. Qed.
Lemma D_675c0 : decode_any W_675c0 = Some (Jal 1 12148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675c4 : bv 32 := 0x00000513.
Lemma F_675c4 : fetch_word Plain.M.loaded_segments (0x675c4 : word) = Some W_675c4.
Proof. vm_refl. Qed.
Lemma D_675c4 : decode_any W_675c4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675c8 : bv 32 := 0x711020ef.
Lemma F_675c8 : fetch_word Plain.M.loaded_segments (0x675c8 : word) = Some W_675c8.
Proof. vm_refl. Qed.
Lemma D_675c8 : decode_any W_675c8 = Some (Jal 1 12048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675cc : bv 32 := 0x0004b517.
Lemma F_675cc : fetch_word Plain.M.loaded_segments (0x675cc : word) = Some W_675cc.
Proof. vm_refl. Qed.
Lemma D_675cc : decode_any W_675cc = Some (Auipc 10 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675d0 : bv 32 := 0x0cc50513.
Lemma F_675d0 : fetch_word Plain.M.loaded_segments (0x675d0 : word) = Some W_675d0.
Proof. vm_refl. Qed.
Lemma D_675d0 : decode_any W_675d0 = Some (OpImm ALU_ADD 10 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675d4 : bv 32 := 0x68c0e0ef.
Lemma F_675d4 : fetch_word Plain.M.loaded_segments (0x675d4 : word) = Some W_675d4.
Proof. vm_refl. Qed.
Lemma D_675d4 : decode_any W_675d4 = Some (Jal 1 59020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675d8 : bv 32 := 0x00000613.
Lemma F_675d8 : fetch_word Plain.M.loaded_segments (0x675d8 : word) = Some W_675d8.
Proof. vm_refl. Qed.
Lemma D_675d8 : decode_any W_675d8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675dc : bv 32 := 0x00013423.
Lemma F_675dc : fetch_word Plain.M.loaded_segments (0x675dc : word) = Some W_675dc.
Proof. vm_refl. Qed.
Lemma D_675dc : decode_any W_675dc = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675e0 : bv 32 := 0x00013823.
Lemma F_675e0 : fetch_word Plain.M.loaded_segments (0x675e0 : word) = Some W_675e0.
Proof. vm_refl. Qed.
Lemma D_675e0 : decode_any W_675e0 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675e4 : bv 32 := 0x00013c23.
Lemma F_675e4 : fetch_word Plain.M.loaded_segments (0x675e4 : word) = Some W_675e4.
Proof. vm_refl. Qed.
Lemma D_675e4 : decode_any W_675e4 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675e8 : bv 32 := 0x02013023.
Lemma F_675e8 : fetch_word Plain.M.loaded_segments (0x675e8 : word) = Some W_675e8.
Proof. vm_refl. Qed.
Lemma D_675e8 : decode_any W_675e8 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675ec : bv 32 := 0x08600893.
Lemma F_675ec : fetch_word Plain.M.loaded_segments (0x675ec : word) = Some W_675ec.
Proof. vm_refl. Qed.
Lemma D_675ec : decode_any W_675ec = Some (OpImm ALU_ADD 17 0 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675f0 : bv 32 := 0x00600513.
Lemma F_675f0 : fetch_word Plain.M.loaded_segments (0x675f0 : word) = Some W_675f0.
Proof. vm_refl. Qed.
Lemma D_675f0 : decode_any W_675f0 = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675f4 : bv 32 := 0x00810593.
Lemma F_675f4 : fetch_word Plain.M.loaded_segments (0x675f4 : word) = Some W_675f4.
Proof. vm_refl. Qed.
Lemma D_675f4 : decode_any W_675f4 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675f8 : bv 32 := 0x00800693.
Lemma F_675f8 : fetch_word Plain.M.loaded_segments (0x675f8 : word) = Some W_675f8.
Proof. vm_refl. Qed.
Lemma D_675f8 : decode_any W_675f8 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_675fc : bv 32 := 0x00000073.
Lemma F_675fc : fetch_word Plain.M.loaded_segments (0x675fc : word) = Some W_675fc.
Proof. vm_refl. Qed.
Lemma D_675fc : decode_any W_675fc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_675fc : is_ecall W_675fc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67600 : bv 32 := 0x00020513.
Lemma F_67600 : fetch_word Plain.M.loaded_segments (0x67600 : word) = Some W_67600.
Proof. vm_refl. Qed.
Lemma D_67600 : decode_any W_67600 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67604 : bv 32 := 0xf5852503.
Lemma F_67604 : fetch_word Plain.M.loaded_segments (0x67604 : word) = Some W_67604.
Proof. vm_refl. Qed.
Lemma D_67604 : decode_any W_67604 = Some (Load SZ4 true 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67608 : bv 32 := 0x02000613.
Lemma F_67608 : fetch_word Plain.M.loaded_segments (0x67608 : word) = Some W_67608.
Proof. vm_refl. Qed.
Lemma D_67608 : decode_any W_67608 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6760c : bv 32 := 0x08200893.
Lemma F_6760c : fetch_word Plain.M.loaded_segments (0x6760c : word) = Some W_6760c.
Proof. vm_refl. Qed.
Lemma D_6760c : decode_any W_6760c = Some (OpImm ALU_ADD 17 0 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67610 : bv 32 := 0x00600593.
Lemma F_67610 : fetch_word Plain.M.loaded_segments (0x67610 : word) = Some W_67610.
Proof. vm_refl. Qed.
Lemma D_67610 : decode_any W_67610 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67614 : bv 32 := 0x00000073.
Lemma F_67614 : fetch_word Plain.M.loaded_segments (0x67614 : word) = Some W_67614.
Proof. vm_refl. Qed.
Lemma D_67614 : decode_any W_67614 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_67614 : is_ecall W_67614 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67618 : bv 32 := 0x00c13023.
Lemma F_67618 : fetch_word Plain.M.loaded_segments (0x67618 : word) = Some W_67618.
Proof. vm_refl. Qed.
Lemma D_67618 : decode_any W_67618 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6761c : bv 32 := 0x08700893.
Lemma F_6761c : fetch_word Plain.M.loaded_segments (0x6761c : word) = Some W_6761c.
Proof. vm_refl. Qed.
Lemma D_6761c : decode_any W_6761c = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67620 : bv 32 := 0x00010593.
Lemma F_67620 : fetch_word Plain.M.loaded_segments (0x67620 : word) = Some W_67620.
Proof. vm_refl. Qed.
Lemma D_67620 : decode_any W_67620 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67624 : bv 32 := 0x00100513.
Lemma F_67624 : fetch_word Plain.M.loaded_segments (0x67624 : word) = Some W_67624.
Proof. vm_refl. Qed.
Lemma D_67624 : decode_any W_67624 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67628 : bv 32 := 0x00800693.
Lemma F_67628 : fetch_word Plain.M.loaded_segments (0x67628 : word) = Some W_67628.
Proof. vm_refl. Qed.
Lemma D_67628 : decode_any W_67628 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6762c : bv 32 := 0x00000613.
Lemma F_6762c : fetch_word Plain.M.loaded_segments (0x6762c : word) = Some W_6762c.
Proof. vm_refl. Qed.
Lemma D_6762c : decode_any W_6762c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67630 : bv 32 := 0x00000073.
Lemma F_67630 : fetch_word Plain.M.loaded_segments (0x67630 : word) = Some W_67630.
Proof. vm_refl. Qed.
Lemma D_67630 : decode_any W_67630 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_67630 : is_ecall W_67630 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67634 : bv 32 := 0x00000023.
Lemma F_67634 : fetch_word Plain.M.loaded_segments (0x67634 : word) = Some W_67634.
Proof. vm_refl. Qed.
Lemma D_67634 : decode_any W_67634 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67638 : bv 32 := 0x00900513.
Lemma F_67638 : fetch_word Plain.M.loaded_segments (0x67638 : word) = Some W_67638.
Proof. vm_refl. Qed.
Lemma D_67638 : decode_any W_67638 = Some (OpImm ALU_ADD 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6763c : bv 32 := 0x6f9020ef.
Lemma F_6763c : fetch_word Plain.M.loaded_segments (0x6763c : word) = Some W_6763c.
Proof. vm_refl. Qed.
Lemma D_6763c : decode_any W_6763c = Some (Jal 1 12024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67640 : bv 32 := 0x07f00513.
Lemma F_67640 : fetch_word Plain.M.loaded_segments (0x67640 : word) = Some W_67640.
Proof. vm_refl. Qed.
Lemma D_67640 : decode_any W_67640 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67644 : bv 32 := 0x004000ef.
Lemma F_67644 : fetch_word Plain.M.loaded_segments (0x67644 : word) = Some W_67644.
Proof. vm_refl. Qed.
Lemma D_67644 : decode_any W_67644 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67648 : bv 32 := 0x00050593.
Lemma F_67648 : fetch_word Plain.M.loaded_segments (0x67648 : word) = Some W_67648.
Proof. vm_refl. Qed.
Lemma D_67648 : decode_any W_67648 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6764c : bv 32 := 0x05e00893.
Lemma F_6764c : fetch_word Plain.M.loaded_segments (0x6764c : word) = Some W_6764c.
Proof. vm_refl. Qed.
Lemma D_6764c : decode_any W_6764c = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67650 : bv 32 := 0x00000073.
Lemma F_67650 : fetch_word Plain.M.loaded_segments (0x67650 : word) = Some W_67650.
Proof. vm_refl. Qed.
Lemma D_67650 : decode_any W_67650 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_67650 : is_ecall W_67650 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67654 : bv 32 := 0x05d00893.
Lemma F_67654 : fetch_word Plain.M.loaded_segments (0x67654 : word) = Some W_67654.
Proof. vm_refl. Qed.
Lemma D_67654 : decode_any W_67654 = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67658 : bv 32 := 0x00058513.
Lemma F_67658 : fetch_word Plain.M.loaded_segments (0x67658 : word) = Some W_67658.
Proof. vm_refl. Qed.
Lemma D_67658 : decode_any W_67658 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6765c : bv 32 := 0x00000073.
Lemma F_6765c : fetch_word Plain.M.loaded_segments (0x6765c : word) = Some W_6765c.
Proof. vm_refl. Qed.
Lemma D_6765c : decode_any W_6765c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6765c : is_ecall W_6765c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67660 : bv 32 := 0xff9ff06f.
Lemma F_67660 : fetch_word Plain.M.loaded_segments (0x67660 : word) = Some W_67660.
Proof. vm_refl. Qed.
Lemma D_67660 : decode_any W_67660 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67664 : bv 32 := 0xff010113.
Lemma F_67664 : fetch_word Plain.M.loaded_segments (0x67664 : word) = Some W_67664.
Proof. vm_refl. Qed.
Lemma D_67664 : decode_any W_67664 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67668 : bv 32 := 0x00113423.
Lemma F_67668 : fetch_word Plain.M.loaded_segments (0x67668 : word) = Some W_67668.
Proof. vm_refl. Qed.
Lemma D_67668 : decode_any W_67668 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6766c : bv 32 := 0x00068713.
Lemma F_6766c : fetch_word Plain.M.loaded_segments (0x6766c : word) = Some W_6766c.
Proof. vm_refl. Qed.
Lemma D_6766c : decode_any W_6766c = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67670 : bv 32 := 0x00060793.
Lemma F_67670 : fetch_word Plain.M.loaded_segments (0x67670 : word) = Some W_67670.
Proof. vm_refl. Qed.
Lemma D_67670 : decode_any W_67670 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67674 : bv 32 := 0x00058693.
Lemma F_67674 : fetch_word Plain.M.loaded_segments (0x67674 : word) = Some W_67674.
Proof. vm_refl. Qed.
Lemma D_67674 : decode_any W_67674 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67678 : bv 32 := 0x00050613.
Lemma F_67678 : fetch_word Plain.M.loaded_segments (0x67678 : word) = Some W_67678.
Proof. vm_refl. Qed.
Lemma D_67678 : decode_any W_67678 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6767c : bv 32 := 0x00019517.
Lemma F_6767c : fetch_word Plain.M.loaded_segments (0x6767c : word) = Some W_6767c.
Proof. vm_refl. Qed.
Lemma D_6767c : decode_any W_6767c = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67680 : bv 32 := 0xfffaa597.
Lemma F_67680 : fetch_word Plain.M.loaded_segments (0x67680 : word) = Some W_67680.
Proof. vm_refl. Qed.
Lemma D_67680 : decode_any W_67680 = Some (Auipc 11 1048490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67684 : bv 32 := 0x3a450513.
Lemma F_67684 : fetch_word Plain.M.loaded_segments (0x67684 : word) = Some W_67684.
Proof. vm_refl. Qed.
Lemma D_67684 : decode_any W_67684 = Some (OpImm ALU_ADD 10 10 932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67688 : bv 32 := 0x75d58593.
Lemma F_67688 : fetch_word Plain.M.loaded_segments (0x67688 : word) = Some W_67688.
Proof. vm_refl. Qed.
Lemma D_67688 : decode_any W_67688 = Some (OpImm ALU_ADD 11 11 1885, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6768c : bv 32 := 0x204030ef.
Lemma F_6768c : fetch_word Plain.M.loaded_segments (0x6768c : word) = Some W_6768c.
Proof. vm_refl. Qed.
Lemma D_6768c : decode_any W_6768c = Some (Jal 1 12804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67690 : bv 32 := 0xf25ff0ef.
Lemma F_67690 : fetch_word Plain.M.loaded_segments (0x67690 : word) = Some W_67690.
Proof. vm_refl. Qed.
Lemma D_67690 : decode_any W_67690 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67694 : bv 32 := 0xfd010113.
Lemma F_67694 : fetch_word Plain.M.loaded_segments (0x67694 : word) = Some W_67694.
Proof. vm_refl. Qed.
Lemma D_67694 : decode_any W_67694 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67698 : bv 32 := 0x02113423.
Lemma F_67698 : fetch_word Plain.M.loaded_segments (0x67698 : word) = Some W_67698.
Proof. vm_refl. Qed.
Lemma D_67698 : decode_any W_67698 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6769c : bv 32 := 0x02813023.
Lemma F_6769c : fetch_word Plain.M.loaded_segments (0x6769c : word) = Some W_6769c.
Proof. vm_refl. Qed.
Lemma D_6769c : decode_any W_6769c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676a0 : bv 32 := 0x00913c23.
Lemma F_676a0 : fetch_word Plain.M.loaded_segments (0x676a0 : word) = Some W_676a0.
Proof. vm_refl. Qed.
Lemma D_676a0 : decode_any W_676a0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676a4 : bv 32 := 0x01213823.
Lemma F_676a4 : fetch_word Plain.M.loaded_segments (0x676a4 : word) = Some W_676a4.
Proof. vm_refl. Qed.
Lemma D_676a4 : decode_any W_676a4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676a8 : bv 32 := 0x01313423.
Lemma F_676a8 : fetch_word Plain.M.loaded_segments (0x676a8 : word) = Some W_676a8.
Proof. vm_refl. Qed.
Lemma D_676a8 : decode_any W_676a8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676ac : bv 32 := 0x0004b517.
Lemma F_676ac : fetch_word Plain.M.loaded_segments (0x676ac : word) = Some W_676ac.
Proof. vm_refl. Qed.
Lemma D_676ac : decode_any W_676ac = Some (Auipc 10 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676b0 : bv 32 := 0xff450913.
Lemma F_676b0 : fetch_word Plain.M.loaded_segments (0x676b0 : word) = Some W_676b0.
Proof. vm_refl. Qed.
Lemma D_676b0 : decode_any W_676b0 = Some (OpImm ALU_ADD 18 10 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676b4 : bv 32 := 0x00490413.
Lemma F_676b4 : fetch_word Plain.M.loaded_segments (0x676b4 : word) = Some W_676b4.
Proof. vm_refl. Qed.
Lemma D_676b4 : decode_any W_676b4 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676b8 : bv 32 := 0x00040513.
Lemma F_676b8 : fetch_word Plain.M.loaded_segments (0x676b8 : word) = Some W_676b8.
Proof. vm_refl. Qed.
Lemma D_676b8 : decode_any W_676b8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676bc : bv 32 := 0x5a40e0ef.
Lemma F_676bc : fetch_word Plain.M.loaded_segments (0x676bc : word) = Some W_676bc.
Proof. vm_refl. Qed.
Lemma D_676bc : decode_any W_676bc = Some (Jal 1 58788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676c0 : bv 32 := 0x01093503.
Lemma F_676c0 : fetch_word Plain.M.loaded_segments (0x676c0 : word) = Some W_676c0.
Proof. vm_refl. Qed.
Lemma D_676c0 : decode_any W_676c0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676c4 : bv 32 := 0x06050863.
Lemma F_676c4 : fetch_word Plain.M.loaded_segments (0x676c4 : word) = Some W_676c4.
Proof. vm_refl. Qed.
Lemma D_676c4 : decode_any W_676c4 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676c8 : bv 32 := 0x00892583.
Lemma F_676c8 : fetch_word Plain.M.loaded_segments (0x676c8 : word) = Some W_676c8.
Proof. vm_refl. Qed.
Lemma D_676c8 : decode_any W_676c8 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676cc : bv 32 := 0x0180006f.
Lemma F_676cc : fetch_word Plain.M.loaded_segments (0x676cc : word) = Some W_676cc.
Proof. vm_refl. Qed.
Lemma D_676cc : decode_any W_676cc = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676d0 : bv 32 := 0x00053503.
Lemma F_676d0 : fetch_word Plain.M.loaded_segments (0x676d0 : word) = Some W_676d0.
Proof. vm_refl. Qed.
Lemma D_676d0 : decode_any W_676d0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676d4 : bv 32 := 0x02000593.
Lemma F_676d4 : fetch_word Plain.M.loaded_segments (0x676d4 : word) = Some W_676d4.
Proof. vm_refl. Qed.
Lemma D_676d4 : decode_any W_676d4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676d8 : bv 32 := 0x00b92423.
Lemma F_676d8 : fetch_word Plain.M.loaded_segments (0x676d8 : word) = Some W_676d8.
Proof. vm_refl. Qed.
Lemma D_676d8 : decode_any W_676d8 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676dc : bv 32 := 0x00a93823.
Lemma F_676dc : fetch_word Plain.M.loaded_segments (0x676dc : word) = Some W_676dc.
Proof. vm_refl. Qed.
Lemma D_676dc : decode_any W_676dc = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676e0 : bv 32 := 0x04050a63.
Lemma F_676e0 : fetch_word Plain.M.loaded_segments (0x676e0 : word) = Some W_676e0.
Proof. vm_refl. Qed.
Lemma D_676e0 : decode_any W_676e0 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676e4 : bv 32 := 0xfff5861b.
Lemma F_676e4 : fetch_word Plain.M.loaded_segments (0x676e4 : word) = Some W_676e4.
Proof. vm_refl. Qed.
Lemma D_676e4 : decode_any W_676e4 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676e8 : bv 32 := 0x00c92423.
Lemma F_676e8 : fetch_word Plain.M.loaded_segments (0x676e8 : word) = Some W_676e8.
Proof. vm_refl. Qed.
Lemma D_676e8 : decode_any W_676e8 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676ec : bv 32 := 0xfeb052e3.
Lemma F_676ec : fetch_word Plain.M.loaded_segments (0x676ec : word) = Some W_676ec.
Proof. vm_refl. Qed.
Lemma D_676ec : decode_any W_676ec = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676f0 : bv 32 := 0x01093503.
Lemma F_676f0 : fetch_word Plain.M.loaded_segments (0x676f0 : word) = Some W_676f0.
Proof. vm_refl. Qed.
Lemma D_676f0 : decode_any W_676f0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676f4 : bv 32 := 0x00361613.
Lemma F_676f4 : fetch_word Plain.M.loaded_segments (0x676f4 : word) = Some W_676f4.
Proof. vm_refl. Qed.
Lemma D_676f4 : decode_any W_676f4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676f8 : bv 32 := 0x00c50533.
Lemma F_676f8 : fetch_word Plain.M.loaded_segments (0x676f8 : word) = Some W_676f8.
Proof. vm_refl. Qed.
Lemma D_676f8 : decode_any W_676f8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676fc : bv 32 := 0x00853983.
Lemma F_676fc : fetch_word Plain.M.loaded_segments (0x676fc : word) = Some W_676fc.
Proof. vm_refl. Qed.
Lemma D_676fc : decode_any W_676fc = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67700 : bv 32 := 0x10853483.
Lemma F_67700 : fetch_word Plain.M.loaded_segments (0x67700 : word) = Some W_67700.
Proof. vm_refl. Qed.
Lemma D_67700 : decode_any W_67700 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67704 : bv 32 := 0x00040513.
Lemma F_67704 : fetch_word Plain.M.loaded_segments (0x67704 : word) = Some W_67704.
Proof. vm_refl. Qed.
Lemma D_67704 : decode_any W_67704 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67708 : bv 32 := 0x7e00e0ef.
Lemma F_67708 : fetch_word Plain.M.loaded_segments (0x67708 : word) = Some W_67708.
Proof. vm_refl. Qed.
Lemma D_67708 : decode_any W_67708 = Some (Jal 1 59360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6770c : bv 32 := 0x00048513.
Lemma F_6770c : fetch_word Plain.M.loaded_segments (0x6770c : word) = Some W_6770c.
Proof. vm_refl. Qed.
Lemma D_6770c : decode_any W_6770c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67710 : bv 32 := 0x000980e7.
Lemma F_67710 : fetch_word Plain.M.loaded_segments (0x67710 : word) = Some W_67710.
Proof. vm_refl. Qed.
Lemma D_67710 : decode_any W_67710 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67714 : bv 32 := 0x00040513.
Lemma F_67714 : fetch_word Plain.M.loaded_segments (0x67714 : word) = Some W_67714.
Proof. vm_refl. Qed.
Lemma D_67714 : decode_any W_67714 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67718 : bv 32 := 0x5480e0ef.
Lemma F_67718 : fetch_word Plain.M.loaded_segments (0x67718 : word) = Some W_67718.
Proof. vm_refl. Qed.
Lemma D_67718 : decode_any W_67718 = Some (Jal 1 58696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6771c : bv 32 := 0x00892503.
Lemma F_6771c : fetch_word Plain.M.loaded_segments (0x6771c : word) = Some W_6771c.
Proof. vm_refl. Qed.
Lemma D_6771c : decode_any W_6771c = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67720 : bv 32 := 0xfff5061b.
Lemma F_67720 : fetch_word Plain.M.loaded_segments (0x67720 : word) = Some W_67720.
Proof. vm_refl. Qed.
Lemma D_67720 : decode_any W_67720 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67724 : bv 32 := 0x00c92423.
Lemma F_67724 : fetch_word Plain.M.loaded_segments (0x67724 : word) = Some W_67724.
Proof. vm_refl. Qed.
Lemma D_67724 : decode_any W_67724 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67728 : bv 32 := 0xfca044e3.
Lemma F_67728 : fetch_word Plain.M.loaded_segments (0x67728 : word) = Some W_67728.
Proof. vm_refl. Qed.
Lemma D_67728 : decode_any W_67728 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6772c : bv 32 := 0x01093503.
Lemma F_6772c : fetch_word Plain.M.loaded_segments (0x6772c : word) = Some W_6772c.
Proof. vm_refl. Qed.
Lemma D_6772c : decode_any W_6772c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67730 : bv 32 := 0xfa1ff06f.
Lemma F_67730 : fetch_word Plain.M.loaded_segments (0x67730 : word) = Some W_67730.
Proof. vm_refl. Qed.
Lemma D_67730 : decode_any W_67730 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67734 : bv 32 := 0x00100513.
Lemma F_67734 : fetch_word Plain.M.loaded_segments (0x67734 : word) = Some W_67734.
Proof. vm_refl. Qed.
Lemma D_67734 : decode_any W_67734 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67738 : bv 32 := 0x00a90023.
Lemma F_67738 : fetch_word Plain.M.loaded_segments (0x67738 : word) = Some W_67738.
Proof. vm_refl. Qed.
Lemma D_67738 : decode_any W_67738 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6773c : bv 32 := 0x00040513.
Lemma F_6773c : fetch_word Plain.M.loaded_segments (0x6773c : word) = Some W_6773c.
Proof. vm_refl. Qed.
Lemma D_6773c : decode_any W_6773c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67740 : bv 32 := 0x02813083.
Lemma F_67740 : fetch_word Plain.M.loaded_segments (0x67740 : word) = Some W_67740.
Proof. vm_refl. Qed.
Lemma D_67740 : decode_any W_67740 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67744 : bv 32 := 0x02013403.
Lemma F_67744 : fetch_word Plain.M.loaded_segments (0x67744 : word) = Some W_67744.
Proof. vm_refl. Qed.
Lemma D_67744 : decode_any W_67744 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67748 : bv 32 := 0x01813483.
Lemma F_67748 : fetch_word Plain.M.loaded_segments (0x67748 : word) = Some W_67748.
Proof. vm_refl. Qed.
Lemma D_67748 : decode_any W_67748 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6774c : bv 32 := 0x01013903.
Lemma F_6774c : fetch_word Plain.M.loaded_segments (0x6774c : word) = Some W_6774c.
Proof. vm_refl. Qed.
Lemma D_6774c : decode_any W_6774c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67750 : bv 32 := 0x00813983.
Lemma F_67750 : fetch_word Plain.M.loaded_segments (0x67750 : word) = Some W_67750.
Proof. vm_refl. Qed.
Lemma D_67750 : decode_any W_67750 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67754 : bv 32 := 0x03010113.
Lemma F_67754 : fetch_word Plain.M.loaded_segments (0x67754 : word) = Some W_67754.
Proof. vm_refl. Qed.
Lemma D_67754 : decode_any W_67754 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67758 : bv 32 := 0x7900e06f.
Lemma F_67758 : fetch_word Plain.M.loaded_segments (0x67758 : word) = Some W_67758.
Proof. vm_refl. Qed.
Lemma D_67758 : decode_any W_67758 = Some (Jal 0 59280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6775c : bv 32 := 0x00008067.
Lemma F_6775c : fetch_word Plain.M.loaded_segments (0x6775c : word) = Some W_6775c.
Proof. vm_refl. Qed.
Lemma D_6775c : decode_any W_6775c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67760 : bv 32 := 0xfd010113.
Lemma F_67760 : fetch_word Plain.M.loaded_segments (0x67760 : word) = Some W_67760.
Proof. vm_refl. Qed.
Lemma D_67760 : decode_any W_67760 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67764 : bv 32 := 0x02113423.
Lemma F_67764 : fetch_word Plain.M.loaded_segments (0x67764 : word) = Some W_67764.
Proof. vm_refl. Qed.
Lemma D_67764 : decode_any W_67764 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67768 : bv 32 := 0x02813023.
Lemma F_67768 : fetch_word Plain.M.loaded_segments (0x67768 : word) = Some W_67768.
Proof. vm_refl. Qed.
Lemma D_67768 : decode_any W_67768 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6776c : bv 32 := 0x00913c23.
Lemma F_6776c : fetch_word Plain.M.loaded_segments (0x6776c : word) = Some W_6776c.
Proof. vm_refl. Qed.
Lemma D_6776c : decode_any W_6776c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67770 : bv 32 := 0x01213823.
Lemma F_67770 : fetch_word Plain.M.loaded_segments (0x67770 : word) = Some W_67770.
Proof. vm_refl. Qed.
Lemma D_67770 : decode_any W_67770 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67774 : bv 32 := 0x01313423.
Lemma F_67774 : fetch_word Plain.M.loaded_segments (0x67774 : word) = Some W_67774.
Proof. vm_refl. Qed.
Lemma D_67774 : decode_any W_67774 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67778 : bv 32 := 0x00050493.
Lemma F_67778 : fetch_word Plain.M.loaded_segments (0x67778 : word) = Some W_67778.
Proof. vm_refl. Qed.
Lemma D_67778 : decode_any W_67778 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6777c : bv 32 := 0x0004b517.
Lemma F_6777c : fetch_word Plain.M.loaded_segments (0x6777c : word) = Some W_6777c.
Proof. vm_refl. Qed.
Lemma D_6777c : decode_any W_6777c = Some (Auipc 10 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67780 : bv 32 := 0xf2450993.
Lemma F_67780 : fetch_word Plain.M.loaded_segments (0x67780 : word) = Some W_67780.
Proof. vm_refl. Qed.
Lemma D_67780 : decode_any W_67780 = Some (OpImm ALU_ADD 19 10 3876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67784 : bv 32 := 0x00498413.
Lemma F_67784 : fetch_word Plain.M.loaded_segments (0x67784 : word) = Some W_67784.
Proof. vm_refl. Qed.
Lemma D_67784 : decode_any W_67784 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67788 : bv 32 := 0x00040513.
Lemma F_67788 : fetch_word Plain.M.loaded_segments (0x67788 : word) = Some W_67788.
Proof. vm_refl. Qed.
Lemma D_67788 : decode_any W_67788 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6778c : bv 32 := 0x4d40e0ef.
Lemma F_6778c : fetch_word Plain.M.loaded_segments (0x6778c : word) = Some W_6778c.
Proof. vm_refl. Qed.
Lemma D_6778c : decode_any W_6778c = Some (Jal 1 58580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67790 : bv 32 := 0x0009c503.
Lemma F_67790 : fetch_word Plain.M.loaded_segments (0x67790 : word) = Some W_67790.
Proof. vm_refl. Qed.
Lemma D_67790 : decode_any W_67790 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67794 : bv 32 := 0xfff00913.
Lemma F_67794 : fetch_word Plain.M.loaded_segments (0x67794 : word) = Some W_67794.
Proof. vm_refl. Qed.
Lemma D_67794 : decode_any W_67794 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67798 : bv 32 := 0x06051263.
Lemma F_67798 : fetch_word Plain.M.loaded_segments (0x67798 : word) = Some W_67798.
Proof. vm_refl. Qed.
Lemma D_67798 : decode_any W_67798 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6779c : bv 32 := 0x0109b503.
Lemma F_6779c : fetch_word Plain.M.loaded_segments (0x6779c : word) = Some W_6779c.
Proof. vm_refl. Qed.
Lemma D_6779c : decode_any W_6779c = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677a0 : bv 32 := 0x00051663.
Lemma F_677a0 : fetch_word Plain.M.loaded_segments (0x677a0 : word) = Some W_677a0.
Proof. vm_refl. Qed.
Lemma D_677a0 : decode_any W_677a0 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677a4 : bv 32 := 0x01898513.
Lemma F_677a4 : fetch_word Plain.M.loaded_segments (0x677a4 : word) = Some W_677a4.
Proof. vm_refl. Qed.
Lemma D_677a4 : decode_any W_677a4 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677a8 : bv 32 := 0x00a9b823.
Lemma F_677a8 : fetch_word Plain.M.loaded_segments (0x677a8 : word) = Some W_677a8.
Proof. vm_refl. Qed.
Lemma D_677a8 : decode_any W_677a8 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677ac : bv 32 := 0x0089a583.
Lemma F_677ac : fetch_word Plain.M.loaded_segments (0x677ac : word) = Some W_677ac.
Proof. vm_refl. Qed.
Lemma D_677ac : decode_any W_677ac = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677b0 : bv 32 := 0x02000613.
Lemma F_677b0 : fetch_word Plain.M.loaded_segments (0x677b0 : word) = Some W_677b0.
Proof. vm_refl. Qed.
Lemma D_677b0 : decode_any W_677b0 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677b4 : bv 32 := 0x02c59263.
Lemma F_677b4 : fetch_word Plain.M.loaded_segments (0x677b4 : word) = Some W_677b4.
Proof. vm_refl. Qed.
Lemma D_677b4 : decode_any W_677b4 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677b8 : bv 32 := 0x20800513.
Lemma F_677b8 : fetch_word Plain.M.loaded_segments (0x677b8 : word) = Some W_677b8.
Proof. vm_refl. Qed.
Lemma D_677b8 : decode_any W_677b8 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677bc : bv 32 := 0x00100593.
Lemma F_677bc : fetch_word Plain.M.loaded_segments (0x677bc : word) = Some W_677bc.
Proof. vm_refl. Qed.
Lemma D_677bc : decode_any W_677bc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677c0 : bv 32 := 0x71c000ef.
Lemma F_677c0 : fetch_word Plain.M.loaded_segments (0x677c0 : word) = Some W_677c0.
Proof. vm_refl. Qed.
Lemma D_677c0 : decode_any W_677c0 = Some (Jal 1 1820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677c4 : bv 32 := 0x02050c63.
Lemma F_677c4 : fetch_word Plain.M.loaded_segments (0x677c4 : word) = Some W_677c4.
Proof. vm_refl. Qed.
Lemma D_677c4 : decode_any W_677c4 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677c8 : bv 32 := 0x00000593.
Lemma F_677c8 : fetch_word Plain.M.loaded_segments (0x677c8 : word) = Some W_677c8.
Proof. vm_refl. Qed.
Lemma D_677c8 : decode_any W_677c8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677cc : bv 32 := 0x0109b603.
Lemma F_677cc : fetch_word Plain.M.loaded_segments (0x677cc : word) = Some W_677cc.
Proof. vm_refl. Qed.
Lemma D_677cc : decode_any W_677cc = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677d0 : bv 32 := 0x00c53023.
Lemma F_677d0 : fetch_word Plain.M.loaded_segments (0x677d0 : word) = Some W_677d0.
Proof. vm_refl. Qed.
Lemma D_677d0 : decode_any W_677d0 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677d4 : bv 32 := 0x00a9b823.
Lemma F_677d4 : fetch_word Plain.M.loaded_segments (0x677d4 : word) = Some W_677d4.
Proof. vm_refl. Qed.
Lemma D_677d4 : decode_any W_677d4 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677d8 : bv 32 := 0x00000913.
Lemma F_677d8 : fetch_word Plain.M.loaded_segments (0x677d8 : word) = Some W_677d8.
Proof. vm_refl. Qed.
Lemma D_677d8 : decode_any W_677d8 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677dc : bv 32 := 0x00359613.
Lemma F_677dc : fetch_word Plain.M.loaded_segments (0x677dc : word) = Some W_677dc.
Proof. vm_refl. Qed.
Lemma D_677dc : decode_any W_677dc = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677e0 : bv 32 := 0x00c50533.
Lemma F_677e0 : fetch_word Plain.M.loaded_segments (0x677e0 : word) = Some W_677e0.
Proof. vm_refl. Qed.
Lemma D_677e0 : decode_any W_677e0 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677e4 : bv 32 := 0x00000617.
Lemma F_677e4 : fetch_word Plain.M.loaded_segments (0x677e4 : word) = Some W_677e4.
Proof. vm_refl. Qed.
Lemma D_677e4 : decode_any W_677e4 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677e8 : bv 32 := 0x00158593.
Lemma F_677e8 : fetch_word Plain.M.loaded_segments (0x677e8 : word) = Some W_677e8.
Proof. vm_refl. Qed.
Lemma D_677e8 : decode_any W_677e8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677ec : bv 32 := 0x04060613.
Lemma F_677ec : fetch_word Plain.M.loaded_segments (0x677ec : word) = Some W_677ec.
Proof. vm_refl. Qed.
Lemma D_677ec : decode_any W_677ec = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677f0 : bv 32 := 0x00c53423.
Lemma F_677f0 : fetch_word Plain.M.loaded_segments (0x677f0 : word) = Some W_677f0.
Proof. vm_refl. Qed.
Lemma D_677f0 : decode_any W_677f0 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677f4 : bv 32 := 0x10953423.
Lemma F_677f4 : fetch_word Plain.M.loaded_segments (0x677f4 : word) = Some W_677f4.
Proof. vm_refl. Qed.
Lemma D_677f4 : decode_any W_677f4 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677f8 : bv 32 := 0x00b9a423.
Lemma F_677f8 : fetch_word Plain.M.loaded_segments (0x677f8 : word) = Some W_677f8.
Proof. vm_refl. Qed.
Lemma D_677f8 : decode_any W_677f8 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677fc : bv 32 := 0x00040513.
Lemma F_677fc : fetch_word Plain.M.loaded_segments (0x677fc : word) = Some W_677fc.
Proof. vm_refl. Qed.
Lemma D_677fc : decode_any W_677fc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67800 : bv 32 := 0x6e80e0ef.
Lemma F_67800 : fetch_word Plain.M.loaded_segments (0x67800 : word) = Some W_67800.
Proof. vm_refl. Qed.
Lemma D_67800 : decode_any W_67800 = Some (Jal 1 59112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67804 : bv 32 := 0x00090513.
Lemma F_67804 : fetch_word Plain.M.loaded_segments (0x67804 : word) = Some W_67804.
Proof. vm_refl. Qed.
Lemma D_67804 : decode_any W_67804 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67808 : bv 32 := 0x02813083.
Lemma F_67808 : fetch_word Plain.M.loaded_segments (0x67808 : word) = Some W_67808.
Proof. vm_refl. Qed.
Lemma D_67808 : decode_any W_67808 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6780c : bv 32 := 0x02013403.
Lemma F_6780c : fetch_word Plain.M.loaded_segments (0x6780c : word) = Some W_6780c.
Proof. vm_refl. Qed.
Lemma D_6780c : decode_any W_6780c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67810 : bv 32 := 0x01813483.
Lemma F_67810 : fetch_word Plain.M.loaded_segments (0x67810 : word) = Some W_67810.
Proof. vm_refl. Qed.
Lemma D_67810 : decode_any W_67810 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67814 : bv 32 := 0x01013903.
Lemma F_67814 : fetch_word Plain.M.loaded_segments (0x67814 : word) = Some W_67814.
Proof. vm_refl. Qed.
Lemma D_67814 : decode_any W_67814 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67818 : bv 32 := 0x00813983.
Lemma F_67818 : fetch_word Plain.M.loaded_segments (0x67818 : word) = Some W_67818.
Proof. vm_refl. Qed.
Lemma D_67818 : decode_any W_67818 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6781c : bv 32 := 0x03010113.
Lemma F_6781c : fetch_word Plain.M.loaded_segments (0x6781c : word) = Some W_6781c.
Proof. vm_refl. Qed.
Lemma D_6781c : decode_any W_6781c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67820 : bv 32 := 0x00008067.
Lemma F_67820 : fetch_word Plain.M.loaded_segments (0x67820 : word) = Some W_67820.
Proof. vm_refl. Qed.
Lemma D_67820 : decode_any W_67820 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67824 : bv 32 := 0x00050067.
Lemma F_67824 : fetch_word Plain.M.loaded_segments (0x67824 : word) = Some W_67824.
Proof. vm_refl. Qed.
Lemma D_67824 : decode_any W_67824 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67828 : bv 32 := 0x00008067.
Lemma F_67828 : fetch_word Plain.M.loaded_segments (0x67828 : word) = Some W_67828.
Proof. vm_refl. Qed.
Lemma D_67828 : decode_any W_67828 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6782c : bv 32 := 0xfe010113.
Lemma F_6782c : fetch_word Plain.M.loaded_segments (0x6782c : word) = Some W_6782c.
Proof. vm_refl. Qed.
Lemma D_6782c : decode_any W_6782c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67830 : bv 32 := 0x00113c23.
Lemma F_67830 : fetch_word Plain.M.loaded_segments (0x67830 : word) = Some W_67830.
Proof. vm_refl. Qed.
Lemma D_67830 : decode_any W_67830 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67834 : bv 32 := 0x00813823.
Lemma F_67834 : fetch_word Plain.M.loaded_segments (0x67834 : word) = Some W_67834.
Proof. vm_refl. Qed.
Lemma D_67834 : decode_any W_67834 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67838 : bv 32 := 0x00913423.
Lemma F_67838 : fetch_word Plain.M.loaded_segments (0x67838 : word) = Some W_67838.
Proof. vm_refl. Qed.
Lemma D_67838 : decode_any W_67838 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6783c : bv 32 := 0x00018517.
Lemma F_6783c : fetch_word Plain.M.loaded_segments (0x6783c : word) = Some W_6783c.
Proof. vm_refl. Qed.
Lemma D_6783c : decode_any W_6783c = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67840 : bv 32 := 0x00018597.
Lemma F_67840 : fetch_word Plain.M.loaded_segments (0x67840 : word) = Some W_67840.
Proof. vm_refl. Qed.
Lemma D_67840 : decode_any W_67840 = Some (Auipc 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67844 : bv 32 := 0xffc53503.
Lemma F_67844 : fetch_word Plain.M.loaded_segments (0x67844 : word) = Some W_67844.
Proof. vm_refl. Qed.
Lemma D_67844 : decode_any W_67844 = Some (Load SZ8 true 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67848 : bv 32 := 0x0005b403.
Lemma F_67848 : fetch_word Plain.M.loaded_segments (0x67848 : word) = Some W_67848.
Proof. vm_refl. Qed.
Lemma D_67848 : decode_any W_67848 = Some (Load SZ8 true 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6784c : bv 32 := 0x00a47c63.
Lemma F_6784c : fetch_word Plain.M.loaded_segments (0x6784c : word) = Some W_6784c.
Proof. vm_refl. Qed.
Lemma D_6784c : decode_any W_6784c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67850 : bv 32 := 0xff853583.
Lemma F_67850 : fetch_word Plain.M.loaded_segments (0x67850 : word) = Some W_67850.
Proof. vm_refl. Qed.
Lemma D_67850 : decode_any W_67850 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67854 : bv 32 := 0xff850493.
Lemma F_67854 : fetch_word Plain.M.loaded_segments (0x67854 : word) = Some W_67854.
Proof. vm_refl. Qed.
Lemma D_67854 : decode_any W_67854 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67858 : bv 32 := 0x000580e7.
Lemma F_67858 : fetch_word Plain.M.loaded_segments (0x67858 : word) = Some W_67858.
Proof. vm_refl. Qed.
Lemma D_67858 : decode_any W_67858 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6785c : bv 32 := 0x00048513.
Lemma F_6785c : fetch_word Plain.M.loaded_segments (0x6785c : word) = Some W_6785c.
Proof. vm_refl. Qed.
Lemma D_6785c : decode_any W_6785c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67860 : bv 32 := 0xfe9468e3.
Lemma F_67860 : fetch_word Plain.M.loaded_segments (0x67860 : word) = Some W_67860.
Proof. vm_refl. Qed.
Lemma D_67860 : decode_any W_67860 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67864 : bv 32 := 0x01813083.
Lemma F_67864 : fetch_word Plain.M.loaded_segments (0x67864 : word) = Some W_67864.
Proof. vm_refl. Qed.
Lemma D_67864 : decode_any W_67864 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67868 : bv 32 := 0x01013403.
Lemma F_67868 : fetch_word Plain.M.loaded_segments (0x67868 : word) = Some W_67868.
Proof. vm_refl. Qed.
Lemma D_67868 : decode_any W_67868 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6786c : bv 32 := 0x00813483.
Lemma F_6786c : fetch_word Plain.M.loaded_segments (0x6786c : word) = Some W_6786c.
Proof. vm_refl. Qed.
Lemma D_6786c : decode_any W_6786c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67870 : bv 32 := 0x02010113.
Lemma F_67870 : fetch_word Plain.M.loaded_segments (0x67870 : word) = Some W_67870.
Proof. vm_refl. Qed.
Lemma D_67870 : decode_any W_67870 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67874 : bv 32 := 0xfb5ff06f.
Lemma F_67874 : fetch_word Plain.M.loaded_segments (0x67874 : word) = Some W_67874.
Proof. vm_refl. Qed.
Lemma D_67874 : decode_any W_67874 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67878 : bv 32 := 0xff010113.
Lemma F_67878 : fetch_word Plain.M.loaded_segments (0x67878 : word) = Some W_67878.
Proof. vm_refl. Qed.
Lemma D_67878 : decode_any W_67878 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6787c : bv 32 := 0x00113423.
Lemma F_6787c : fetch_word Plain.M.loaded_segments (0x6787c : word) = Some W_6787c.
Proof. vm_refl. Qed.
Lemma D_6787c : decode_any W_6787c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67880 : bv 32 := 0x00813023.
Lemma F_67880 : fetch_word Plain.M.loaded_segments (0x67880 : word) = Some W_67880.
Proof. vm_refl. Qed.
Lemma D_67880 : decode_any W_67880 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67884 : bv 32 := 0x00000593.
Lemma F_67884 : fetch_word Plain.M.loaded_segments (0x67884 : word) = Some W_67884.
Proof. vm_refl. Qed.
Lemma D_67884 : decode_any W_67884 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67888 : bv 32 := 0x00020613.
Lemma F_67888 : fetch_word Plain.M.loaded_segments (0x67888 : word) = Some W_67888.
Proof. vm_refl. Qed.
Lemma D_67888 : decode_any W_67888 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6788c : bv 32 := 0xf5862603.
Lemma F_6788c : fetch_word Plain.M.loaded_segments (0x6788c : word) = Some W_6788c.
Proof. vm_refl. Qed.
Lemma D_6788c : decode_any W_6788c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67890 : bv 32 := 0x0004b697.
Lemma F_67890 : fetch_word Plain.M.loaded_segments (0x67890 : word) = Some W_67890.
Proof. vm_refl. Qed.
Lemma D_67890 : decode_any W_67890 = Some (Auipc 13 75, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67894 : bv 32 := 0x03068693.
Lemma F_67894 : fetch_word Plain.M.loaded_segments (0x67894 : word) = Some W_67894.
Proof. vm_refl. Qed.
Lemma D_67894 : decode_any W_67894 = Some (OpImm ALU_ADD 13 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67898 : bv 32 := 0x1606a72f.
Lemma F_67898 : fetch_word Plain.M.loaded_segments (0x67898 : word) = Some W_67898.
Proof. vm_refl. Qed.
Lemma D_67898 : decode_any W_67898 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6789c : bv 32 := 0x00b71663.
Lemma F_6789c : fetch_word Plain.M.loaded_segments (0x6789c : word) = Some W_6789c.
Proof. vm_refl. Qed.
Lemma D_6789c : decode_any W_6789c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678a0 : bv 32 := 0x1ec6a7af.
Lemma F_678a0 : fetch_word Plain.M.loaded_segments (0x678a0 : word) = Some W_678a0.
Proof. vm_refl. Qed.
Lemma D_678a0 : decode_any W_678a0 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678a4 : bv 32 := 0xfe079ae3.
Lemma F_678a4 : fetch_word Plain.M.loaded_segments (0x678a4 : word) = Some W_678a4.
Proof. vm_refl. Qed.
Lemma D_678a4 : decode_any W_678a4 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678a8 : bv 32 := 0x0007059b.
Lemma F_678a8 : fetch_word Plain.M.loaded_segments (0x678a8 : word) = Some W_678a8.
Proof. vm_refl. Qed.
Lemma D_678a8 : decode_any W_678a8 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678ac : bv 32 := 0x02c58263.
Lemma F_678ac : fetch_word Plain.M.loaded_segments (0x678ac : word) = Some W_678ac.
Proof. vm_refl. Qed.
Lemma D_678ac : decode_any W_678ac = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678b0 : bv 32 := 0x02058263.
Lemma F_678b0 : fetch_word Plain.M.loaded_segments (0x678b0 : word) = Some W_678b0.
Proof. vm_refl. Qed.
Lemma D_678b0 : decode_any W_678b0 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678b4 : bv 32 := 0x04900893.
Lemma F_678b4 : fetch_word Plain.M.loaded_segments (0x678b4 : word) = Some W_678b4.
Proof. vm_refl. Qed.
Lemma D_678b4 : decode_any W_678b4 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678b8 : bv 32 := 0x00000593.
Lemma F_678b8 : fetch_word Plain.M.loaded_segments (0x678b8 : word) = Some W_678b8.
Proof. vm_refl. Qed.
Lemma D_678b8 : decode_any W_678b8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678bc : bv 32 := 0x00000613.
Lemma F_678bc : fetch_word Plain.M.loaded_segments (0x678bc : word) = Some W_678bc.
Proof. vm_refl. Qed.
Lemma D_678bc : decode_any W_678bc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678c0 : bv 32 := 0x00000693.
Lemma F_678c0 : fetch_word Plain.M.loaded_segments (0x678c0 : word) = Some W_678c0.
Proof. vm_refl. Qed.
Lemma D_678c0 : decode_any W_678c0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678c4 : bv 32 := 0x00000513.
Lemma F_678c4 : fetch_word Plain.M.loaded_segments (0x678c4 : word) = Some W_678c4.
Proof. vm_refl. Qed.
Lemma D_678c4 : decode_any W_678c4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678c8 : bv 32 := 0x00000073.
Lemma F_678c8 : fetch_word Plain.M.loaded_segments (0x678c8 : word) = Some W_678c8.
Proof. vm_refl. Qed.
Lemma D_678c8 : decode_any W_678c8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_678c8 : is_ecall W_678c8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_678cc : bv 32 := 0xff9ff06f.
Lemma F_678cc : fetch_word Plain.M.loaded_segments (0x678cc : word) = Some W_678cc.
Proof. vm_refl. Qed.
Lemma D_678cc : decode_any W_678cc = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678d0 : bv 32 := 0x00000023.
Lemma F_678d0 : fetch_word Plain.M.loaded_segments (0x678d0 : word) = Some W_678d0.
Proof. vm_refl. Qed.
Lemma D_678d0 : decode_any W_678d0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678d4 : bv 32 := 0x00050413.
Lemma F_678d4 : fetch_word Plain.M.loaded_segments (0x678d4 : word) = Some W_678d4.
Proof. vm_refl. Qed.
Lemma D_678d4 : decode_any W_678d4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678d8 : bv 32 := 0xdbdff0ef.
Lemma F_678d8 : fetch_word Plain.M.loaded_segments (0x678d8 : word) = Some W_678d8.
Proof. vm_refl. Qed.
Lemma D_678d8 : decode_any W_678d8 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678dc : bv 32 := 0xf51ff0ef.
Lemma F_678dc : fetch_word Plain.M.loaded_segments (0x678dc : word) = Some W_678dc.
Proof. vm_refl. Qed.
Lemma D_678dc : decode_any W_678dc = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678e0 : bv 32 := 0x288030ef.
Lemma F_678e0 : fetch_word Plain.M.loaded_segments (0x678e0 : word) = Some W_678e0.
Proof. vm_refl. Qed.
Lemma D_678e0 : decode_any W_678e0 = Some (Jal 1 12936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678e4 : bv 32 := 0x00040513.
Lemma F_678e4 : fetch_word Plain.M.loaded_segments (0x678e4 : word) = Some W_678e4.
Proof. vm_refl. Qed.
Lemma D_678e4 : decode_any W_678e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_678e8 : bv 32 := 0xd61ff0ef.
Lemma F_678e8 : fetch_word Plain.M.loaded_segments (0x678e8 : word) = Some W_678e8.
Proof. vm_refl. Qed.
Lemma D_678e8 : decode_any W_678e8 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.
