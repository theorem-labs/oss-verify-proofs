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
Definition Wx_83fd8 : bv 32 := 0x81010113.
Lemma Fx_83fd8 : fetch_word Asan.M.loaded_segments (0x84028 : word) = Some Wx_83fd8.
Proof. vm_refl. Qed.
Lemma Dx_83fd8 : decode_any Wx_83fd8 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83fdc : bv 32 := 0x7e113423.
Lemma Fx_83fdc : fetch_word Asan.M.loaded_segments (0x8402c : word) = Some Wx_83fdc.
Proof. vm_refl. Qed.
Lemma Dx_83fdc : decode_any Wx_83fdc = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83fe0 : bv 32 := 0x7e813023.
Lemma Fx_83fe0 : fetch_word Asan.M.loaded_segments (0x84030 : word) = Some Wx_83fe0.
Proof. vm_refl. Qed.
Lemma Dx_83fe0 : decode_any Wx_83fe0 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83fe4 : bv 32 := 0x7c913c23.
Lemma Fx_83fe4 : fetch_word Asan.M.loaded_segments (0x84034 : word) = Some Wx_83fe4.
Proof. vm_refl. Qed.
Lemma Dx_83fe4 : decode_any Wx_83fe4 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83fe8 : bv 32 := 0x7d213823.
Lemma Fx_83fe8 : fetch_word Asan.M.loaded_segments (0x84038 : word) = Some Wx_83fe8.
Proof. vm_refl. Qed.
Lemma Dx_83fe8 : decode_any Wx_83fe8 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83fec : bv 32 := 0x7d313423.
Lemma Fx_83fec : fetch_word Asan.M.loaded_segments (0x8403c : word) = Some Wx_83fec.
Proof. vm_refl. Qed.
Lemma Dx_83fec : decode_any Wx_83fec = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83ff0 : bv 32 := 0x7d413023.
Lemma Fx_83ff0 : fetch_word Asan.M.loaded_segments (0x84040 : word) = Some Wx_83ff0.
Proof. vm_refl. Qed.
Lemma Dx_83ff0 : decode_any Wx_83ff0 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83ff4 : bv 32 := 0x7b513c23.
Lemma Fx_83ff4 : fetch_word Asan.M.loaded_segments (0x84044 : word) = Some Wx_83ff4.
Proof. vm_refl. Qed.
Lemma Dx_83ff4 : decode_any Wx_83ff4 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83ff8 : bv 32 := 0x7f010413.
Lemma Fx_83ff8 : fetch_word Asan.M.loaded_segments (0x84048 : word) = Some Wx_83ff8.
Proof. vm_refl. Qed.
Lemma Dx_83ff8 : decode_any Wx_83ff8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_83ffc : bv 32 := 0xfa010113.
Lemma Fx_83ffc : fetch_word Asan.M.loaded_segments (0x8404c : word) = Some Wx_83ffc.
Proof. vm_refl. Qed.
Lemma Dx_83ffc : decode_any Wx_83ffc = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_84000 : bv 32 := 0x00058a13.
Lemma Fx_84000 : fetch_word Asan.M.loaded_segments (0x84050 : word) = Some Wx_84000.
Proof. vm_refl. Qed.
Lemma Dx_84000 : decode_any Wx_84000 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84004 : bv 32 := 0x000dd597.
Lemma Fx_84004 : fetch_word Asan.M.loaded_segments (0x84054 : word) = Some Wx_84004.
Proof. vm_refl. Qed.
Lemma Dx_84004 : decode_any Wx_84004 = Some (Auipc 11 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84008 : bv 32 := 0xbbc5b583.
Lemma Fx_84008 : fetch_word Asan.M.loaded_segments (0x84058 : word) = Some Wx_84008.
Proof. vm_refl. Qed.
Lemma Dx_84008 : decode_any Wx_84008 = Some (Load SZ8 true 11 11 3004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8400c : bv 32 := 0x0605c583.
Lemma Fx_8400c : fetch_word Asan.M.loaded_segments (0x8405c : word) = Some Wx_8400c.
Proof. vm_refl. Qed.
Lemma Dx_8400c : decode_any Wx_8400c = Some (Load SZ1 false 11 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84010 : bv 32 := 0x22058863.
Lemma Fx_84010 : fetch_word Asan.M.loaded_segments (0x84060 : word) = Some Wx_84010.
Proof. vm_refl. Qed.
Lemma Dx_84010 : decode_any Wx_84010 = Some (Branch BC_EQ 11 0 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84014 : bv 32 := 0x00068913.
Lemma Fx_84014 : fetch_word Asan.M.loaded_segments (0x84064 : word) = Some Wx_84014.
Proof. vm_refl. Qed.
Lemma Dx_84014 : decode_any Wx_84014 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84018 : bv 32 := 0x00060993.
Lemma Fx_84018 : fetch_word Asan.M.loaded_segments (0x84068 : word) = Some Wx_84018.
Proof. vm_refl. Qed.
Lemma Dx_84018 : decode_any Wx_84018 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8401c : bv 32 := 0x00050493.
Lemma Fx_8401c : fetch_word Asan.M.loaded_segments (0x8406c : word) = Some Wx_8401c.
Proof. vm_refl. Qed.
Lemma Dx_8401c : decode_any Wx_8401c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84020 : bv 32 := 0x000dd517.
Lemma Fx_84020 : fetch_word Asan.M.loaded_segments (0x84070 : word) = Some Wx_84020.
Proof. vm_refl. Qed.
Lemma Dx_84020 : decode_any Wx_84020 = Some (Auipc 10 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84024 : bv 32 := 0xbf853503.
Lemma Fx_84024 : fetch_word Asan.M.loaded_segments (0x84074 : word) = Some Wx_84024.
Proof. vm_refl. Qed.
Lemma Dx_84024 : decode_any Wx_84024 = Some (Load SZ8 true 10 10 3064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84028 : bv 32 := 0x00052503.
Lemma Fx_84028 : fetch_word Asan.M.loaded_segments (0x84078 : word) = Some Wx_84028.
Proof. vm_refl. Qed.
Lemma Dx_84028 : decode_any Wx_84028 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8402c : bv 32 := 0x00300593.
Lemma Fx_8402c : fetch_word Asan.M.loaded_segments (0x8407c : word) = Some Wx_8402c.
Proof. vm_refl. Qed.
Lemma Dx_8402c : decode_any Wx_8402c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84030 : bv 32 := 0x08b57063.
Lemma Fx_84030 : fetch_word Asan.M.loaded_segments (0x84080 : word) = Some Wx_84030.
Proof. vm_refl. Qed.
Lemma Dx_84030 : decode_any Wx_84030 = Some (Branch BC_GEU 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84034 : bv 32 := 0x0899fe63.
Lemma Fx_84034 : fetch_word Asan.M.loaded_segments (0x84084 : word) = Some Wx_84034.
Proof. vm_refl. Qed.
Lemma Dx_84034 : decode_any Wx_84034 = Some (Branch BC_GEU 19 9 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84038 : bv 32 := 0x80040513.
Lemma Fx_84038 : fetch_word Asan.M.loaded_segments (0x84088 : word) = Some Wx_84038.
Proof. vm_refl. Qed.
Lemma Dx_84038 : decode_any Wx_84038 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8403c : bv 32 := 0xfb050513.
Lemma Fx_8403c : fetch_word Asan.M.loaded_segments (0x8408c : word) = Some Wx_8403c.
Proof. vm_refl. Qed.
Lemma Dx_8403c : decode_any Wx_8403c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84040 : bv 32 := 0x80040593.
Lemma Fx_84040 : fetch_word Asan.M.loaded_segments (0x84090 : word) = Some Wx_84040.
Proof. vm_refl. Qed.
Lemma Dx_84040 : decode_any Wx_84040 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84044 : bv 32 := 0xfc058593.
Lemma Fx_84044 : fetch_word Asan.M.loaded_segments (0x84094 : word) = Some Wx_84044.
Proof. vm_refl. Qed.
Lemma Dx_84044 : decode_any Wx_84044 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84048 : bv 32 := 0x80040613.
Lemma Fx_84048 : fetch_word Asan.M.loaded_segments (0x84098 : word) = Some Wx_84048.
Proof. vm_refl. Qed.
Lemma Dx_84048 : decode_any Wx_84048 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8404c : bv 32 := 0xfb060613.
Lemma Fx_8404c : fetch_word Asan.M.loaded_segments (0x8409c : word) = Some Wx_8404c.
Proof. vm_refl. Qed.
Lemma Dx_8404c : decode_any Wx_8404c = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84050 : bv 32 := 0x7ff60a93.
Lemma Fx_84050 : fetch_word Asan.M.loaded_segments (0x840a0 : word) = Some Wx_84050.
Proof. vm_refl. Qed.
Lemma Dx_84050 : decode_any Wx_84050 = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84054 : bv 32 := 0x000ab4a3.
Lemma Fx_84054 : fetch_word Asan.M.loaded_segments (0x840a4 : word) = Some Wx_84054.
Proof. vm_refl. Qed.
Lemma Dx_84054 : decode_any Wx_84054 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84058 : bv 32 := 0x00b53023.
Lemma Fx_84058 : fetch_word Asan.M.loaded_segments (0x840a8 : word) = Some Wx_84058.
Proof. vm_refl. Qed.
Lemma Dx_84058 : decode_any Wx_84058 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8405c : bv 32 := 0x00053423.
Lemma Fx_8405c : fetch_word Asan.M.loaded_segments (0x840ac : word) = Some Wx_8405c.
Proof. vm_refl. Qed.
Lemma Dx_8405c : decode_any Wx_8405c = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84060 : bv 32 := 0x6451e0ef.
Lemma Fx_84060 : fetch_word Asan.M.loaded_segments (0x840b0 : word) = Some Wx_84060.
Proof. vm_refl. Qed.
Lemma Dx_84060 : decode_any Wx_84060 = Some (Jal 1 126532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84064 : bv 32 := 0x00050593.
Lemma Fx_84064 : fetch_word Asan.M.loaded_segments (0x840b4 : word) = Some Wx_84064.
Proof. vm_refl. Qed.
Lemma Dx_84064 : decode_any Wx_84064 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84068 : bv 32 := 0x000dd517.
Lemma Fx_84068 : fetch_word Asan.M.loaded_segments (0x840b8 : word) = Some Wx_84068.
Proof. vm_refl. Qed.
Lemma Dx_84068 : decode_any Wx_84068 = Some (Auipc 10 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8406c : bv 32 := 0xb5053503.
Lemma Fx_8406c : fetch_word Asan.M.loaded_segments (0x840bc : word) = Some Wx_8406c.
Proof. vm_refl. Qed.
Lemma Dx_8406c : decode_any Wx_8406c = Some (Load SZ8 true 10 10 2896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84070 : bv 32 := 0x02154703.
Lemma Fx_84070 : fetch_word Asan.M.loaded_segments (0x840c0 : word) = Some Wx_84070.
Proof. vm_refl. Qed.
Lemma Dx_84070 : decode_any Wx_84070 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84074 : bv 32 := 0x008ab4a3.
Lemma Fx_84074 : fetch_word Asan.M.loaded_segments (0x840c4 : word) = Some Wx_84074.
Proof. vm_refl. Qed.
Lemma Dx_84074 : decode_any Wx_84074 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84078 : bv 32 := 0x80040513.
Lemma Fx_84078 : fetch_word Asan.M.loaded_segments (0x840c8 : word) = Some Wx_84078.
Proof. vm_refl. Qed.
Lemma Dx_84078 : decode_any Wx_84078 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8407c : bv 32 := 0xfb050513.
Lemma Fx_8407c : fetch_word Asan.M.loaded_segments (0x840cc : word) = Some Wx_8407c.
Proof. vm_refl. Qed.
Lemma Dx_8407c : decode_any Wx_8407c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84080 : bv 32 := 0x0ff00793.
Lemma Fx_84080 : fetch_word Asan.M.loaded_segments (0x840d0 : word) = Some Wx_84080.
Proof. vm_refl. Qed.
Lemma Dx_84080 : decode_any Wx_84080 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84084 : bv 32 := 0x00040613.
Lemma Fx_84084 : fetch_word Asan.M.loaded_segments (0x840d4 : word) = Some Wx_84084.
Proof. vm_refl. Qed.
Lemma Dx_84084 : decode_any Wx_84084 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84088 : bv 32 := 0x00000693.
Lemma Fx_84088 : fetch_word Asan.M.loaded_segments (0x840d8 : word) = Some Wx_84088.
Proof. vm_refl. Qed.
Lemma Dx_84088 : decode_any Wx_84088 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8408c : bv 32 := 0x34c060ef.
Lemma Fx_8408c : fetch_word Asan.M.loaded_segments (0x840dc : word) = Some Wx_8408c.
Proof. vm_refl. Qed.
Lemma Dx_8408c : decode_any Wx_8408c = Some (Jal 1 25420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84090 : bv 32 := 0x80040713.
Lemma Fx_84090 : fetch_word Asan.M.loaded_segments (0x840e0 : word) = Some Wx_84090.
Proof. vm_refl. Qed.
Lemma Dx_84090 : decode_any Wx_84090 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84094 : bv 32 := 0xfb070713.
Lemma Fx_84094 : fetch_word Asan.M.loaded_segments (0x840e4 : word) = Some Wx_84094.
Proof. vm_refl. Qed.
Lemma Dx_84094 : decode_any Wx_84094 = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84098 : bv 32 := 0x00048513.
Lemma Fx_84098 : fetch_word Asan.M.loaded_segments (0x840e8 : word) = Some Wx_84098.
Proof. vm_refl. Qed.
Lemma Dx_84098 : decode_any Wx_84098 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8409c : bv 32 := 0x000a0593.
Lemma Fx_8409c : fetch_word Asan.M.loaded_segments (0x840ec : word) = Some Wx_8409c.
Proof. vm_refl. Qed.
Lemma Dx_8409c : decode_any Wx_8409c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840a0 : bv 32 := 0x00098613.
Lemma Fx_840a0 : fetch_word Asan.M.loaded_segments (0x840f0 : word) = Some Wx_840a0.
Proof. vm_refl. Qed.
Lemma Dx_840a0 : decode_any Wx_840a0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840a4 : bv 32 := 0x00090693.
Lemma Fx_840a4 : fetch_word Asan.M.loaded_segments (0x840f4 : word) = Some Wx_840a4.
Proof. vm_refl. Qed.
Lemma Dx_840a4 : decode_any Wx_840a4 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840a8 : bv 32 := 0x0e0030ef.
Lemma Fx_840a8 : fetch_word Asan.M.loaded_segments (0x840f8 : word) = Some Wx_840a8.
Proof. vm_refl. Qed.
Lemma Dx_840a8 : decode_any Wx_840a8 = Some (Jal 1 12512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840ac : bv 32 := 0x0300006f.
Lemma Fx_840ac : fetch_word Asan.M.loaded_segments (0x840fc : word) = Some Wx_840ac.
Proof. vm_refl. Qed.
Lemma Dx_840ac : decode_any Wx_840ac = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840b0 : bv 32 := 0xfff96517.
Lemma Fx_840b0 : fetch_word Asan.M.loaded_segments (0x84100 : word) = Some Wx_840b0.
Proof. vm_refl. Qed.
Lemma Dx_840b0 : decode_any Wx_840b0 = Some (Auipc 10 1048470, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840b4 : bv 32 := 0x8b050513.
Lemma Fx_840b4 : fetch_word Asan.M.loaded_segments (0x84104 : word) = Some Wx_840b4.
Proof. vm_refl. Qed.
Lemma Dx_840b4 : decode_any Wx_840b4 = Some (OpImm ALU_ADD 10 10 2224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840b8 : bv 32 := 0x00048593.
Lemma Fx_840b8 : fetch_word Asan.M.loaded_segments (0x84108 : word) = Some Wx_840b8.
Proof. vm_refl. Qed.
Lemma Dx_840b8 : decode_any Wx_840b8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840bc : bv 32 := 0x000a0613.
Lemma Fx_840bc : fetch_word Asan.M.loaded_segments (0x8410c : word) = Some Wx_840bc.
Proof. vm_refl. Qed.
Lemma Dx_840bc : decode_any Wx_840bc = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840c0 : bv 32 := 0x00098693.
Lemma Fx_840c0 : fetch_word Asan.M.loaded_segments (0x84110 : word) = Some Wx_840c0.
Proof. vm_refl. Qed.
Lemma Dx_840c0 : decode_any Wx_840c0 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840c4 : bv 32 := 0x00090713.
Lemma Fx_840c4 : fetch_word Asan.M.loaded_segments (0x84114 : word) = Some Wx_840c4.
Proof. vm_refl. Qed.
Lemma Dx_840c4 : decode_any Wx_840c4 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840c8 : bv 32 := 0x491120ef.
Lemma Fx_840c8 : fetch_word Asan.M.loaded_segments (0x84118 : word) = Some Wx_840c8.
Proof. vm_refl. Qed.
Lemma Dx_840c8 : decode_any Wx_840c8 = Some (Jal 1 76944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840cc : bv 32 := 0xf699e6e3.
Lemma Fx_840cc : fetch_word Asan.M.loaded_segments (0x8411c : word) = Some Wx_840cc.
Proof. vm_refl. Qed.
Lemma Dx_840cc : decode_any Wx_840cc = Some (Branch BC_LTU 19 9 8044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840d0 : bv 32 := 0xf72a64e3.
Lemma Fx_840d0 : fetch_word Asan.M.loaded_segments (0x84120 : word) = Some Wx_840d0.
Proof. vm_refl. Qed.
Lemma Dx_840d0 : decode_any Wx_840d0 = Some (Branch BC_LTU 20 18 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840d4 : bv 32 := 0xf73a62e3.
Lemma Fx_840d4 : fetch_word Asan.M.loaded_segments (0x84124 : word) = Some Wx_840d4.
Proof. vm_refl. Qed.
Lemma Dx_840d4 : decode_any Wx_840d4 = Some (Branch BC_LTU 20 19 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840d8 : bv 32 := 0xf69960e3.
Lemma Fx_840d8 : fetch_word Asan.M.loaded_segments (0x84128 : word) = Some Wx_840d8.
Proof. vm_refl. Qed.
Lemma Dx_840d8 : decode_any Wx_840d8 = Some (Branch BC_LTU 18 9 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840dc : bv 32 := 0x409a06b3.
Lemma Fx_840dc : fetch_word Asan.M.loaded_segments (0x8412c : word) = Some Wx_840dc.
Proof. vm_refl. Qed.
Lemma Dx_840dc : decode_any Wx_840dc = Some (Op ALU_SUB 13 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840e0 : bv 32 := 0x00100713.
Lemma Fx_840e0 : fetch_word Asan.M.loaded_segments (0x84130 : word) = Some Wx_840e0.
Proof. vm_refl. Qed.
Lemma Dx_840e0 : decode_any Wx_840e0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840e4 : bv 32 := 0x02871713.
Lemma Fx_840e4 : fetch_word Asan.M.loaded_segments (0x84134 : word) = Some Wx_840e4.
Proof. vm_refl. Qed.
Lemma Dx_840e4 : decode_any Wx_840e4 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840e8 : bv 32 := 0x00170513.
Lemma Fx_840e8 : fetch_word Asan.M.loaded_segments (0x84138 : word) = Some Wx_840e8.
Proof. vm_refl. Qed.
Lemma Dx_840e8 : decode_any Wx_840e8 = Some (OpImm ALU_ADD 10 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840ec : bv 32 := 0x04a6fa63.
Lemma Fx_840ec : fetch_word Asan.M.loaded_segments (0x8413c : word) = Some Wx_840ec.
Proof. vm_refl. Qed.
Lemma Dx_840ec : decode_any Wx_840ec = Some (Branch BC_GEU 13 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840f0 : bv 32 := 0x15298863.
Lemma Fx_840f0 : fetch_word Asan.M.loaded_segments (0x84140 : word) = Some Wx_840f0.
Proof. vm_refl. Qed.
Lemma Dx_840f0 : decode_any Wx_840f0 = Some (Branch BC_EQ 19 18 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840f4 : bv 32 := 0x007a7513.
Lemma Fx_840f4 : fetch_word Asan.M.loaded_segments (0x84144 : word) = Some Wx_840f4.
Proof. vm_refl. Qed.
Lemma Dx_840f4 : decode_any Wx_840f4 = Some (OpImm ALU_AND 10 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840f8 : bv 32 := 0x06051063.
Lemma Fx_840f8 : fetch_word Asan.M.loaded_segments (0x84148 : word) = Some Wx_840f8.
Proof. vm_refl. Qed.
Lemma Dx_840f8 : decode_any Wx_840f8 = Some (Branch BC_NE 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_840fc : bv 32 := 0x00098a13.
Lemma Fx_840fc : fetch_word Asan.M.loaded_segments (0x8414c : word) = Some Wx_840fc.
Proof. vm_refl. Qed.
Lemma Dx_840fc : decode_any Wx_840fc = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84100 : bv 32 := 0x00090a93.
Lemma Fx_84100 : fetch_word Asan.M.loaded_segments (0x84150 : word) = Some Wx_84100.
Proof. vm_refl. Qed.
Lemma Dx_84100 : decode_any Wx_84100 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84104 : bv 32 := 0x00048513.
Lemma Fx_84104 : fetch_word Asan.M.loaded_segments (0x84154 : word) = Some Wx_84104.
Proof. vm_refl. Qed.
Lemma Dx_84104 : decode_any Wx_84104 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84108 : bv 32 := 0x0074f993.
Lemma Fx_84108 : fetch_word Asan.M.loaded_segments (0x84158 : word) = Some Wx_84108.
Proof. vm_refl. Qed.
Lemma Dx_84108 : decode_any Wx_84108 = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8410c : bv 32 := 0x08099e63.
Lemma Fx_8410c : fetch_word Asan.M.loaded_segments (0x8415c : word) = Some Wx_8410c.
Proof. vm_refl. Qed.
Lemma Dx_8410c : decode_any Wx_8410c = Some (Branch BC_NE 19 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84110 : bv 32 := 0x000a0593.
Lemma Fx_84110 : fetch_word Asan.M.loaded_segments (0x84160 : word) = Some Wx_84110.
Proof. vm_refl. Qed.
Lemma Dx_84110 : decode_any Wx_84110 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84114 : bv 32 := 0x000a0513.
Lemma Fx_84114 : fetch_word Asan.M.loaded_segments (0x84164 : word) = Some Wx_84114.
Proof. vm_refl. Qed.
Lemma Dx_84114 : decode_any Wx_84114 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84118 : bv 32 := 0x0d5a6863.
Lemma Fx_84118 : fetch_word Asan.M.loaded_segments (0x84168 : word) = Some Wx_84118.
Proof. vm_refl. Qed.
Lemma Dx_84118 : decode_any Wx_84118 = Some (Branch BC_LTU 20 21 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8411c : bv 32 := 0xff8af513.
Lemma Fx_8411c : fetch_word Asan.M.loaded_segments (0x8416c : word) = Some Wx_8411c.
Proof. vm_refl. Qed.
Lemma Dx_8411c : decode_any Wx_8411c = Some (OpImm ALU_AND 10 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84120 : bv 32 := 0x0cbaf863.
Lemma Fx_84120 : fetch_word Asan.M.loaded_segments (0x84170 : word) = Some Wx_84120.
Proof. vm_refl. Qed.
Lemma Dx_84120 : decode_any Wx_84120 = Some (Branch BC_GEU 21 11 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84124 : bv 32 := 0xff8af493.
Lemma Fx_84124 : fetch_word Asan.M.loaded_segments (0x84174 : word) = Some Wx_84124.
Proof. vm_refl. Qed.
Lemma Dx_84124 : decode_any Wx_84124 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84128 : bv 32 := 0x007a8613.
Lemma Fx_84128 : fetch_word Asan.M.loaded_segments (0x84178 : word) = Some Wx_84128.
Proof. vm_refl. Qed.
Lemma Dx_84128 : decode_any Wx_84128 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8412c : bv 32 := 0xff867913.
Lemma Fx_8412c : fetch_word Asan.M.loaded_segments (0x8417c : word) = Some Wx_8412c.
Proof. vm_refl. Qed.
Lemma Dx_8412c : decode_any Wx_8412c = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84130 : bv 32 := 0x0c957a63.
Lemma Fx_84130 : fetch_word Asan.M.loaded_segments (0x84180 : word) = Some Wx_84130.
Proof. vm_refl. Qed.
Lemma Dx_84130 : decode_any Wx_84130 = Some (Branch BC_GEU 10 9 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84134 : bv 32 := 0x40a485b3.
Lemma Fx_84134 : fetch_word Asan.M.loaded_segments (0x84184 : word) = Some Wx_84134.
Proof. vm_refl. Qed.
Lemma Dx_84134 : decode_any Wx_84134 = Some (Op ALU_SUB 11 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84138 : bv 32 := 0x00000613.
Lemma Fx_84138 : fetch_word Asan.M.loaded_segments (0x84188 : word) = Some Wx_84138.
Proof. vm_refl. Qed.
Lemma Dx_84138 : decode_any Wx_84138 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8413c : bv 32 := 0x0e00006f.
Lemma Fx_8413c : fetch_word Asan.M.loaded_segments (0x8418c : word) = Some Wx_8413c.
Proof. vm_refl. Qed.
Lemma Dx_8413c : decode_any Wx_8413c = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84140 : bv 32 := 0xfff9e517.
Lemma Fx_84140 : fetch_word Asan.M.loaded_segments (0x84190 : word) = Some Wx_84140.
Proof. vm_refl. Qed.
Lemma Dx_84140 : decode_any Wx_84140 = Some (Auipc 10 1048478, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84144 : bv 32 := 0xfff9f597.
Lemma Fx_84144 : fetch_word Asan.M.loaded_segments (0x84194 : word) = Some Wx_84144.
Proof. vm_refl. Qed.
Lemma Dx_84144 : decode_any Wx_84144 = Some (Auipc 11 1048479, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84148 : bv 32 := 0x03450513.
Lemma Fx_84148 : fetch_word Asan.M.loaded_segments (0x84198 : word) = Some Wx_84148.
Proof. vm_refl. Qed.
Lemma Dx_84148 : decode_any Wx_84148 = Some (OpImm ALU_ADD 10 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8414c : bv 32 := 0x23458613.
Lemma Fx_8414c : fetch_word Asan.M.loaded_segments (0x8419c : word) = Some Wx_8414c.
Proof. vm_refl. Qed.
Lemma Dx_8414c : decode_any Wx_8414c = Some (OpImm ALU_ADD 12 11 564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84150 : bv 32 := 0x1b600593.
Lemma Fx_84150 : fetch_word Asan.M.loaded_segments (0x841a0 : word) = Some Wx_84150.
Proof. vm_refl. Qed.
Lemma Dx_84150 : decode_any Wx_84150 = Some (OpImm ALU_ADD 11 0 438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84154 : bv 32 := 0x58c170ef.
Lemma Fx_84154 : fetch_word Asan.M.loaded_segments (0x841a4 : word) = Some Wx_84154.
Proof. vm_refl. Qed.
Lemma Dx_84154 : decode_any Wx_84154 = Some (Jal 1 95628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84158 : bv 32 := 0xff8a7a93.
Lemma Fx_84158 : fetch_word Asan.M.loaded_segments (0x841a8 : word) = Some Wx_84158.
Proof. vm_refl. Qed.
Lemma Dx_84158 : decode_any Wx_84158 = Some (OpImm ALU_AND 21 20 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8415c : bv 32 := 0x00098593.
Lemma Fx_8415c : fetch_word Asan.M.loaded_segments (0x841ac : word) = Some Wx_8415c.
Proof. vm_refl. Qed.
Lemma Dx_8415c : decode_any Wx_8415c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84160 : bv 32 := 0x01396463.
Lemma Fx_84160 : fetch_word Asan.M.loaded_segments (0x841b0 : word) = Some Wx_84160.
Proof. vm_refl. Qed.
Lemma Dx_84160 : decode_any Wx_84160 = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84164 : bv 32 := 0x00090593.
Lemma Fx_84164 : fetch_word Asan.M.loaded_segments (0x841b4 : word) = Some Wx_84164.
Proof. vm_refl. Qed.
Lemma Dx_84164 : decode_any Wx_84164 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84168 : bv 32 := 0xf8bafae3.
Lemma Fx_84168 : fetch_word Asan.M.loaded_segments (0x841b8 : word) = Some Wx_84168.
Proof. vm_refl. Qed.
Lemma Dx_84168 : decode_any Wx_84168 = Some (Branch BC_GEU 21 11 8084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8416c : bv 32 := 0x000dd597.
Lemma Fx_8416c : fetch_word Asan.M.loaded_segments (0x841bc : word) = Some Wx_8416c.
Proof. vm_refl. Qed.
Lemma Dx_8416c : decode_any Wx_8416c = Some (Auipc 11 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84170 : bv 32 := 0xa5c5b583.
Lemma Fx_84170 : fetch_word Asan.M.loaded_segments (0x841c0 : word) = Some Wx_84170.
Proof. vm_refl. Qed.
Lemma Dx_84170 : decode_any Wx_84170 = Some (Load SZ8 true 11 11 2652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84174 : bv 32 := 0x0005b583.
Lemma Fx_84174 : fetch_word Asan.M.loaded_segments (0x841c4 : word) = Some Wx_84174.
Proof. vm_refl. Qed.
Lemma Dx_84174 : decode_any Wx_84174 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84178 : bv 32 := 0x003a5613.
Lemma Fx_84178 : fetch_word Asan.M.loaded_segments (0x841c8 : word) = Some Wx_84178.
Proof. vm_refl. Qed.
Lemma Dx_84178 : decode_any Wx_84178 = Some (ShiftImm ALU_SRL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8417c : bv 32 := 0x00c585b3.
Lemma Fx_8417c : fetch_word Asan.M.loaded_segments (0x841cc : word) = Some Wx_8417c.
Proof. vm_refl. Qed.
Lemma Dx_8417c : decode_any Wx_8417c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84180 : bv 32 := 0x00058583.
Lemma Fx_84180 : fetch_word Asan.M.loaded_segments (0x841d0 : word) = Some Wx_84180.
Proof. vm_refl. Qed.
Lemma Dx_84180 : decode_any Wx_84180 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84184 : bv 32 := 0x00058463.
Lemma Fx_84184 : fetch_word Asan.M.loaded_segments (0x841d4 : word) = Some Wx_84184.
Proof. vm_refl. Qed.
Lemma Dx_84184 : decode_any Wx_84184 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84188 : bv 32 := 0xf6b55ae3.
Lemma Fx_84188 : fetch_word Asan.M.loaded_segments (0x841d8 : word) = Some Wx_84188.
Proof. vm_refl. Qed.
Lemma Dx_84188 : decode_any Wx_84188 = Some (Branch BC_GE 10 11 8052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8418c : bv 32 := 0x000a8513.
Lemma Fx_8418c : fetch_word Asan.M.loaded_segments (0x841dc : word) = Some Wx_8418c.
Proof. vm_refl. Qed.
Lemma Dx_8418c : decode_any Wx_8418c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84190 : bv 32 := 0x0e9aea63.
Lemma Fx_84190 : fetch_word Asan.M.loaded_segments (0x841e0 : word) = Some Wx_84190.
Proof. vm_refl. Qed.
Lemma Dx_84190 : decode_any Wx_84190 = Some (Branch BC_LTU 21 9 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84194 : bv 32 := 0x00048513.
Lemma Fx_84194 : fetch_word Asan.M.loaded_segments (0x841e4 : word) = Some Wx_84194.
Proof. vm_refl. Qed.
Lemma Dx_84194 : decode_any Wx_84194 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84198 : bv 32 := 0x000a8a13.
Lemma Fx_84198 : fetch_word Asan.M.loaded_segments (0x841e8 : word) = Some Wx_84198.
Proof. vm_refl. Qed.
Lemma Dx_84198 : decode_any Wx_84198 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8419c : bv 32 := 0x0f3af863.
Lemma Fx_8419c : fetch_word Asan.M.loaded_segments (0x841ec : word) = Some Wx_8419c.
Proof. vm_refl. Qed.
Lemma Dx_8419c : decode_any Wx_8419c = Some (Branch BC_GEU 21 19 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841a0 : bv 32 := 0xf72ae4e3.
Lemma Fx_841a0 : fetch_word Asan.M.loaded_segments (0x841f0 : word) = Some Wx_841a0.
Proof. vm_refl. Qed.
Lemma Dx_841a0 : decode_any Wx_841a0 = Some (Branch BC_LTU 21 18 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841a4 : bv 32 := 0x0f00006f.
Lemma Fx_841a4 : fetch_word Asan.M.loaded_segments (0x841f4 : word) = Some Wx_841a4.
Proof. vm_refl. Qed.
Lemma Dx_841a4 : decode_any Wx_841a4 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841a8 : bv 32 := 0xf74504e3.
Lemma Fx_841a8 : fetch_word Asan.M.loaded_segments (0x841f8 : word) = Some Wx_841a8.
Proof. vm_refl. Qed.
Lemma Dx_841a8 : decode_any Wx_841a8 = Some (Branch BC_EQ 10 20 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841ac : bv 32 := 0xf75512e3.
Lemma Fx_841ac : fetch_word Asan.M.loaded_segments (0x841fc : word) = Some Wx_841ac.
Proof. vm_refl. Qed.
Lemma Dx_841ac : decode_any Wx_841ac = Some (Branch BC_NE 10 21 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841b0 : bv 32 := 0x00748593.
Lemma Fx_841b0 : fetch_word Asan.M.loaded_segments (0x84200 : word) = Some Wx_841b0.
Proof. vm_refl. Qed.
Lemma Dx_841b0 : decode_any Wx_841b0 = Some (OpImm ALU_ADD 11 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841b4 : bv 32 := 0xff85f913.
Lemma Fx_841b4 : fetch_word Asan.M.loaded_segments (0x84204 : word) = Some Wx_841b4.
Proof. vm_refl. Qed.
Lemma Dx_841b4 : decode_any Wx_841b4 = Some (OpImm ALU_AND 18 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841b8 : bv 32 := 0xf5257ce3.
Lemma Fx_841b8 : fetch_word Asan.M.loaded_segments (0x84208 : word) = Some Wx_841b8.
Proof. vm_refl. Qed.
Lemma Dx_841b8 : decode_any Wx_841b8 = Some (Branch BC_GEU 10 18 8024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841bc : bv 32 := 0xff84f513.
Lemma Fx_841bc : fetch_word Asan.M.loaded_segments (0x8420c : word) = Some Wx_841bc.
Proof. vm_refl. Qed.
Lemma Dx_841bc : decode_any Wx_841bc = Some (OpImm ALU_AND 10 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841c0 : bv 32 := 0xbd0ff0ef.
Lemma Fx_841c0 : fetch_word Asan.M.loaded_segments (0x84210 : word) = Some Wx_841c0.
Proof. vm_refl. Qed.
Lemma Dx_841c0 : decode_any Wx_841c0 = Some (Jal 1 2094032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841c4 : bv 32 := 0x01350023.
Lemma Fx_841c4 : fetch_word Asan.M.loaded_segments (0x84214 : word) = Some Wx_841c4.
Proof. vm_refl. Qed.
Lemma Dx_841c4 : decode_any Wx_841c4 = Some (Store SZ1 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841c8 : bv 32 := 0x00090593.
Lemma Fx_841c8 : fetch_word Asan.M.loaded_segments (0x84218 : word) = Some Wx_841c8.
Proof. vm_refl. Qed.
Lemma Dx_841c8 : decode_any Wx_841c8 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841cc : bv 32 := 0x012a6463.
Lemma Fx_841cc : fetch_word Asan.M.loaded_segments (0x8421c : word) = Some Wx_841cc.
Proof. vm_refl. Qed.
Lemma Dx_841cc : decode_any Wx_841cc = Some (Branch BC_LTU 20 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841d0 : bv 32 := 0x000a0593.
Lemma Fx_841d0 : fetch_word Asan.M.loaded_segments (0x84220 : word) = Some Wx_841d0.
Proof. vm_refl. Qed.
Lemma Dx_841d0 : decode_any Wx_841d0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841d4 : bv 32 := 0x012ae463.
Lemma Fx_841d4 : fetch_word Asan.M.loaded_segments (0x84224 : word) = Some Wx_841d4.
Proof. vm_refl. Qed.
Lemma Dx_841d4 : decode_any Wx_841d4 = Some (Branch BC_LTU 21 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841d8 : bv 32 := 0x000a8913.
Lemma Fx_841d8 : fetch_word Asan.M.loaded_segments (0x84228 : word) = Some Wx_841d8.
Proof. vm_refl. Qed.
Lemma Dx_841d8 : decode_any Wx_841d8 = Some (OpImm ALU_ADD 18 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841dc : bv 32 := 0x00090a93.
Lemma Fx_841dc : fetch_word Asan.M.loaded_segments (0x8422c : word) = Some Wx_841dc.
Proof. vm_refl. Qed.
Lemma Dx_841dc : decode_any Wx_841dc = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841e0 : bv 32 := 0x00058513.
Lemma Fx_841e0 : fetch_word Asan.M.loaded_segments (0x84230 : word) = Some Wx_841e0.
Proof. vm_refl. Qed.
Lemma Dx_841e0 : decode_any Wx_841e0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841e4 : bv 32 := 0xf325fce3.
Lemma Fx_841e4 : fetch_word Asan.M.loaded_segments (0x84234 : word) = Some Wx_841e4.
Proof. vm_refl. Qed.
Lemma Dx_841e4 : decode_any Wx_841e4 = Some (Branch BC_GEU 11 18 7992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841e8 : bv 32 := 0xff857513.
Lemma Fx_841e8 : fetch_word Asan.M.loaded_segments (0x84238 : word) = Some Wx_841e8.
Proof. vm_refl. Qed.
Lemma Dx_841e8 : decode_any Wx_841e8 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841ec : bv 32 := 0xf2baece3.
Lemma Fx_841ec : fetch_word Asan.M.loaded_segments (0x8423c : word) = Some Wx_841ec.
Proof. vm_refl. Qed.
Lemma Dx_841ec : decode_any Wx_841ec = Some (Branch BC_LTU 21 11 7992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841f0 : bv 32 := 0x000a8593.
Lemma Fx_841f0 : fetch_word Asan.M.loaded_segments (0x84240 : word) = Some Wx_841f0.
Proof. vm_refl. Qed.
Lemma Dx_841f0 : decode_any Wx_841f0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841f4 : bv 32 := 0xff8af493.
Lemma Fx_841f4 : fetch_word Asan.M.loaded_segments (0x84244 : word) = Some Wx_841f4.
Proof. vm_refl. Qed.
Lemma Dx_841f4 : decode_any Wx_841f4 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841f8 : bv 32 := 0x007a8613.
Lemma Fx_841f8 : fetch_word Asan.M.loaded_segments (0x84248 : word) = Some Wx_841f8.
Proof. vm_refl. Qed.
Lemma Dx_841f8 : decode_any Wx_841f8 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_841fc : bv 32 := 0xff867913.
Lemma Fx_841fc : fetch_word Asan.M.loaded_segments (0x8424c : word) = Some Wx_841fc.
Proof. vm_refl. Qed.
Lemma Dx_841fc : decode_any Wx_841fc = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84200 : bv 32 := 0xf2956ae3.
Lemma Fx_84200 : fetch_word Asan.M.loaded_segments (0x84250 : word) = Some Wx_84200.
Proof. vm_refl. Qed.
Lemma Dx_84200 : decode_any Wx_84200 = Some (Branch BC_LTU 10 9 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84204 : bv 32 := 0x00758513.
Lemma Fx_84204 : fetch_word Asan.M.loaded_segments (0x84254 : word) = Some Wx_84204.
Proof. vm_refl. Qed.
Lemma Dx_84204 : decode_any Wx_84204 = Some (OpImm ALU_ADD 10 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84208 : bv 32 := 0xff857513.
Lemma Fx_84208 : fetch_word Asan.M.loaded_segments (0x84258 : word) = Some Wx_84208.
Proof. vm_refl. Qed.
Lemma Dx_84208 : decode_any Wx_84208 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8420c : bv 32 := 0x00a97a63.
Lemma Fx_8420c : fetch_word Asan.M.loaded_segments (0x8425c : word) = Some Wx_8420c.
Proof. vm_refl. Qed.
Lemma Dx_8420c : decode_any Wx_8420c = Some (Branch BC_GEU 18 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84210 : bv 32 := 0x412505b3.
Lemma Fx_84210 : fetch_word Asan.M.loaded_segments (0x84260 : word) = Some Wx_84210.
Proof. vm_refl. Qed.
Lemma Dx_84210 : decode_any Wx_84210 = Some (Op ALU_SUB 11 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84214 : bv 32 := 0x0fc00613.
Lemma Fx_84214 : fetch_word Asan.M.loaded_segments (0x84264 : word) = Some Wx_84214.
Proof. vm_refl. Qed.
Lemma Dx_84214 : decode_any Wx_84214 = Some (OpImm ALU_ADD 12 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84218 : bv 32 := 0x00090513.
Lemma Fx_84218 : fetch_word Asan.M.loaded_segments (0x84268 : word) = Some Wx_84218.
Proof. vm_refl. Qed.
Lemma Dx_84218 : decode_any Wx_84218 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8421c : bv 32 := 0xe79fe0ef.
Lemma Fx_8421c : fetch_word Asan.M.loaded_segments (0x8426c : word) = Some Wx_8421c.
Proof. vm_refl. Qed.
Lemma Dx_8421c : decode_any Wx_8421c = Some (Jal 1 2092664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84220 : bv 32 := 0x02990063.
Lemma Fx_84220 : fetch_word Asan.M.loaded_segments (0x84270 : word) = Some Wx_84220.
Proof. vm_refl. Qed.
Lemma Dx_84220 : decode_any Wx_84220 = Some (Branch BC_EQ 18 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84224 : bv 32 := 0x409906b3.
Lemma Fx_84224 : fetch_word Asan.M.loaded_segments (0x84274 : word) = Some Wx_84224.
Proof. vm_refl. Qed.
Lemma Dx_84224 : decode_any Wx_84224 = Some (Op ALU_SUB 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84228 : bv 32 := 0x00800513.
Lemma Fx_84228 : fetch_word Asan.M.loaded_segments (0x84278 : word) = Some Wx_84228.
Proof. vm_refl. Qed.
Lemma Dx_84228 : decode_any Wx_84228 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8422c : bv 32 := 0x02a69e63.
Lemma Fx_8422c : fetch_word Asan.M.loaded_segments (0x8427c : word) = Some Wx_8422c.
Proof. vm_refl. Qed.
Lemma Dx_8422c : decode_any Wx_8422c = Some (Branch BC_NE 13 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84230 : bv 32 := 0x007af913.
Lemma Fx_84230 : fetch_word Asan.M.loaded_segments (0x84280 : word) = Some Wx_84230.
Proof. vm_refl. Qed.
Lemma Dx_84230 : decode_any Wx_84230 = Some (OpImm ALU_AND 18 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84234 : bv 32 := 0x00048513.
Lemma Fx_84234 : fetch_word Asan.M.loaded_segments (0x84284 : word) = Some Wx_84234.
Proof. vm_refl. Qed.
Lemma Dx_84234 : decode_any Wx_84234 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84238 : bv 32 := 0xb58ff0ef.
Lemma Fx_84238 : fetch_word Asan.M.loaded_segments (0x84288 : word) = Some Wx_84238.
Proof. vm_refl. Qed.
Lemma Dx_84238 : decode_any Wx_84238 = Some (Jal 1 2093912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8423c : bv 32 := 0x01250023.
Lemma Fx_8423c : fetch_word Asan.M.loaded_segments (0x8428c : word) = Some Wx_8423c.
Proof. vm_refl. Qed.
Lemma Dx_8423c : decode_any Wx_8423c = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84240 : bv 32 := 0x06010113.
Lemma Fx_84240 : fetch_word Asan.M.loaded_segments (0x84290 : word) = Some Wx_84240.
Proof. vm_refl. Qed.
Lemma Dx_84240 : decode_any Wx_84240 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84244 : bv 32 := 0x7e813083.
Lemma Fx_84244 : fetch_word Asan.M.loaded_segments (0x84294 : word) = Some Wx_84244.
Proof. vm_refl. Qed.
Lemma Dx_84244 : decode_any Wx_84244 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84248 : bv 32 := 0x7e013403.
Lemma Fx_84248 : fetch_word Asan.M.loaded_segments (0x84298 : word) = Some Wx_84248.
Proof. vm_refl. Qed.
Lemma Dx_84248 : decode_any Wx_84248 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8424c : bv 32 := 0x7d813483.
Lemma Fx_8424c : fetch_word Asan.M.loaded_segments (0x8429c : word) = Some Wx_8424c.
Proof. vm_refl. Qed.
Lemma Dx_8424c : decode_any Wx_8424c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84250 : bv 32 := 0x7d013903.
Lemma Fx_84250 : fetch_word Asan.M.loaded_segments (0x842a0 : word) = Some Wx_84250.
Proof. vm_refl. Qed.
Lemma Dx_84250 : decode_any Wx_84250 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84254 : bv 32 := 0x7c813983.
Lemma Fx_84254 : fetch_word Asan.M.loaded_segments (0x842a4 : word) = Some Wx_84254.
Proof. vm_refl. Qed.
Lemma Dx_84254 : decode_any Wx_84254 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84258 : bv 32 := 0x7c013a03.
Lemma Fx_84258 : fetch_word Asan.M.loaded_segments (0x842a8 : word) = Some Wx_84258.
Proof. vm_refl. Qed.
Lemma Dx_84258 : decode_any Wx_84258 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8425c : bv 32 := 0x7b813a83.
Lemma Fx_8425c : fetch_word Asan.M.loaded_segments (0x842ac : word) = Some Wx_8425c.
Proof. vm_refl. Qed.
Lemma Dx_8425c : decode_any Wx_8425c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84260 : bv 32 := 0x7f010113.
Lemma Fx_84260 : fetch_word Asan.M.loaded_segments (0x842b0 : word) = Some Wx_84260.
Proof. vm_refl. Qed.
Lemma Dx_84260 : decode_any Wx_84260 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84264 : bv 32 := 0x00008067.
Lemma Fx_84264 : fetch_word Asan.M.loaded_segments (0x842b4 : word) = Some Wx_84264.
Proof. vm_refl. Qed.
Lemma Dx_84264 : decode_any Wx_84264 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84268 : bv 32 := 0xfff9e517.
Lemma Fx_84268 : fetch_word Asan.M.loaded_segments (0x842b8 : word) = Some Wx_84268.
Proof. vm_refl. Qed.
Lemma Dx_84268 : decode_any Wx_84268 = Some (Auipc 10 1048478, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8426c : bv 32 := 0xfff95617.
Lemma Fx_8426c : fetch_word Asan.M.loaded_segments (0x842bc : word) = Some Wx_8426c.
Proof. vm_refl. Qed.
Lemma Dx_8426c : decode_any Wx_8426c = Some (Auipc 12 1048469, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84270 : bv 32 := 0x1dc00593.
Lemma Fx_84270 : fetch_word Asan.M.loaded_segments (0x842c0 : word) = Some Wx_84270.
Proof. vm_refl. Qed.
Lemma Dx_84270 : decode_any Wx_84270 = Some (OpImm ALU_ADD 11 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84274 : bv 32 := 0xf0c50513.
Lemma Fx_84274 : fetch_word Asan.M.loaded_segments (0x842c4 : word) = Some Wx_84274.
Proof. vm_refl. Qed.
Lemma Dx_84274 : decode_any Wx_84274 = Some (OpImm ALU_ADD 10 10 3852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84278 : bv 32 := 0xbfb60613.
Lemma Fx_84278 : fetch_word Asan.M.loaded_segments (0x842c8 : word) = Some Wx_84278.
Proof. vm_refl. Qed.
Lemma Dx_84278 : decode_any Wx_84278 = Some (OpImm ALU_ADD 12 12 3067, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8427c : bv 32 := 0x00800713.
Lemma Fx_8427c : fetch_word Asan.M.loaded_segments (0x842cc : word) = Some Wx_8427c.
Proof. vm_refl. Qed.
Lemma Dx_8427c : decode_any Wx_8427c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84280 : bv 32 := 0x460170ef.
Lemma Fx_84280 : fetch_word Asan.M.loaded_segments (0x842d0 : word) = Some Wx_84280.
Proof. vm_refl. Qed.
Lemma Dx_84280 : decode_any Wx_84280 = Some (Jal 1 95328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84284 : bv 32 := 0x000a8a13.
Lemma Fx_84284 : fetch_word Asan.M.loaded_segments (0x842d4 : word) = Some Wx_84284.
Proof. vm_refl. Qed.
Lemma Dx_84284 : decode_any Wx_84284 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84288 : bv 32 := 0xf13aece3.
Lemma Fx_84288 : fetch_word Asan.M.loaded_segments (0x842d8 : word) = Some Wx_84288.
Proof. vm_refl. Qed.
Lemma Dx_84288 : decode_any Wx_84288 = Some (Branch BC_LTU 21 19 7960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8428c : bv 32 := 0x00098a13.
Lemma Fx_8428c : fetch_word Asan.M.loaded_segments (0x842dc : word) = Some Wx_8428c.
Proof. vm_refl. Qed.
Lemma Dx_8428c : decode_any Wx_8428c = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84290 : bv 32 := 0xe72aece3.
Lemma Fx_84290 : fetch_word Asan.M.loaded_segments (0x842e0 : word) = Some Wx_84290.
Proof. vm_refl. Qed.
Lemma Dx_84290 : decode_any Wx_84290 = Some (Branch BC_LTU 21 18 7800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84294 : bv 32 := 0x00090a93.
Lemma Fx_84294 : fetch_word Asan.M.loaded_segments (0x842e4 : word) = Some Wx_84294.
Proof. vm_refl. Qed.
Lemma Dx_84294 : decode_any Wx_84294 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_84298 : bv 32 := 0xe71ff06f.
Lemma Fx_84298 : fetch_word Asan.M.loaded_segments (0x842e8 : word) = Some Wx_84298.
Proof. vm_refl. Qed.
Lemma Dx_84298 : decode_any Wx_84298 = Some (Jal 0 2096752, 4%Z).
Proof. vm_refl. Qed.

