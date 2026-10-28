(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushU10.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_156a0 : bv 32 := 0xff010113.
Lemma F_156a0 : fetch_word Ubsan.M.loaded_segments (0x1579c : word) = Some W_156a0.
Proof. vm_refl. Qed.
Lemma D_156a0 : decode_any W_156a0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a4 : bv 32 := 0x00113423.
Lemma F_156a4 : fetch_word Ubsan.M.loaded_segments (0x157a0 : word) = Some W_156a4.
Proof. vm_refl. Qed.
Lemma D_156a4 : decode_any W_156a4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156a8 : bv 32 := 0x00813023.
Lemma F_156a8 : fetch_word Ubsan.M.loaded_segments (0x157a4 : word) = Some W_156a8.
Proof. vm_refl. Qed.
Lemma D_156a8 : decode_any W_156a8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156ac : bv 32 := 0x00060413.
Lemma F_156ac : fetch_word Ubsan.M.loaded_segments (0x157a8 : word) = Some W_156ac.
Proof. vm_refl. Qed.
Lemma D_156ac : decode_any W_156ac = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b0 : bv 32 := 0x00050613.
Lemma F_156b0 : fetch_word Ubsan.M.loaded_segments (0x157ac : word) = Some W_156b0.
Proof. vm_refl. Qed.
Lemma D_156b0 : decode_any W_156b0 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b4 : bv 32 := 0xffffc517.
Lemma F_156b4 : fetch_word Ubsan.M.loaded_segments (0x157b0 : word) = Some W_156b4.
Proof. vm_refl. Qed.
Lemma D_156b4 : decode_any W_156b4 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156b8 : bv 32 := 0xe1f50513.
Lemma F_156b8 : fetch_word Ubsan.M.loaded_segments (0x157b4 : word) = Some W_156b8.
Proof. vm_refl. Qed.
Lemma D_156b8 : decode_any W_156b8 = Some (OpImm ALU_ADD 10 10 3615, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156bc : bv 32 := 0x018000ef.
Lemma F_156bc : fetch_word Ubsan.M.loaded_segments (0x157b8 : word) = Some W_156bc.
Proof. vm_refl. Qed.
Lemma D_156bc : decode_any W_156bc = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c0 : bv 32 := 0x00040513.
Lemma F_156c0 : fetch_word Ubsan.M.loaded_segments (0x157bc : word) = Some W_156c0.
Proof. vm_refl. Qed.
Lemma D_156c0 : decode_any W_156c0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c4 : bv 32 := 0x00813083.
Lemma F_156c4 : fetch_word Ubsan.M.loaded_segments (0x157c0 : word) = Some W_156c4.
Proof. vm_refl. Qed.
Lemma D_156c4 : decode_any W_156c4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156c8 : bv 32 := 0x00013403.
Lemma F_156c8 : fetch_word Ubsan.M.loaded_segments (0x157c4 : word) = Some W_156c8.
Proof. vm_refl. Qed.
Lemma D_156c8 : decode_any W_156c8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156cc : bv 32 := 0x01010113.
Lemma F_156cc : fetch_word Ubsan.M.loaded_segments (0x157c8 : word) = Some W_156cc.
Proof. vm_refl. Qed.
Lemma D_156cc : decode_any W_156cc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_156d0 : bv 32 := 0x00008067.
Lemma F_156d0 : fetch_word Ubsan.M.loaded_segments (0x157cc : word) = Some W_156d0.
Proof. vm_refl. Qed.
Lemma D_156d0 : decode_any W_156d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15770 : bv 32 := 0xff010113.
Lemma F_15770 : fetch_word Ubsan.M.loaded_segments (0x1586c : word) = Some W_15770.
Proof. vm_refl. Qed.
Lemma D_15770 : decode_any W_15770 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15774 : bv 32 := 0x00113423.
Lemma F_15774 : fetch_word Ubsan.M.loaded_segments (0x15870 : word) = Some W_15774.
Proof. vm_refl. Qed.
Lemma D_15774 : decode_any W_15774 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15778 : bv 32 := 0x00813023.
Lemma F_15778 : fetch_word Ubsan.M.loaded_segments (0x15874 : word) = Some W_15778.
Proof. vm_refl. Qed.
Lemma D_15778 : decode_any W_15778 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1577c : bv 32 := 0x00060413.
Lemma F_1577c : fetch_word Ubsan.M.loaded_segments (0x15878 : word) = Some W_1577c.
Proof. vm_refl. Qed.
Lemma D_1577c : decode_any W_1577c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15780 : bv 32 := 0x00050613.
Lemma F_15780 : fetch_word Ubsan.M.loaded_segments (0x1587c : word) = Some W_15780.
Proof. vm_refl. Qed.
Lemma D_15780 : decode_any W_15780 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15784 : bv 32 := 0xffffc517.
Lemma F_15784 : fetch_word Ubsan.M.loaded_segments (0x15880 : word) = Some W_15784.
Proof. vm_refl. Qed.
Lemma D_15784 : decode_any W_15784 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15788 : bv 32 := 0xd4f50513.
Lemma F_15788 : fetch_word Ubsan.M.loaded_segments (0x15884 : word) = Some W_15788.
Proof. vm_refl. Qed.
Lemma D_15788 : decode_any W_15788 = Some (OpImm ALU_ADD 10 10 3407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1578c : bv 32 := 0xf49ff0ef.
Lemma F_1578c : fetch_word Ubsan.M.loaded_segments (0x15888 : word) = Some W_1578c.
Proof. vm_refl. Qed.
Lemma D_1578c : decode_any W_1578c = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15790 : bv 32 := 0x00040513.
Lemma F_15790 : fetch_word Ubsan.M.loaded_segments (0x1588c : word) = Some W_15790.
Proof. vm_refl. Qed.
Lemma D_15790 : decode_any W_15790 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15794 : bv 32 := 0x00813083.
Lemma F_15794 : fetch_word Ubsan.M.loaded_segments (0x15890 : word) = Some W_15794.
Proof. vm_refl. Qed.
Lemma D_15794 : decode_any W_15794 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15798 : bv 32 := 0x00013403.
Lemma F_15798 : fetch_word Ubsan.M.loaded_segments (0x15894 : word) = Some W_15798.
Proof. vm_refl. Qed.
Lemma D_15798 : decode_any W_15798 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1579c : bv 32 := 0x01010113.
Lemma F_1579c : fetch_word Ubsan.M.loaded_segments (0x15898 : word) = Some W_1579c.
Proof. vm_refl. Qed.
Lemma D_1579c : decode_any W_1579c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157a0 : bv 32 := 0x00008067.
Lemma F_157a0 : fetch_word Ubsan.M.loaded_segments (0x1589c : word) = Some W_157a0.
Proof. vm_refl. Qed.
Lemma D_157a0 : decode_any W_157a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15910 : bv 32 := 0xfe010113.
Lemma F_15910 : fetch_word Ubsan.M.loaded_segments (0x15a0c : word) = Some W_15910.
Proof. vm_refl. Qed.
Lemma D_15910 : decode_any W_15910 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15914 : bv 32 := 0x00113c23.
Lemma F_15914 : fetch_word Ubsan.M.loaded_segments (0x15a10 : word) = Some W_15914.
Proof. vm_refl. Qed.
Lemma D_15914 : decode_any W_15914 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15918 : bv 32 := 0x00813823.
Lemma F_15918 : fetch_word Ubsan.M.loaded_segments (0x15a14 : word) = Some W_15918.
Proof. vm_refl. Qed.
Lemma D_15918 : decode_any W_15918 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1591c : bv 32 := 0x00913423.
Lemma F_1591c : fetch_word Ubsan.M.loaded_segments (0x15a18 : word) = Some W_1591c.
Proof. vm_refl. Qed.
Lemma D_1591c : decode_any W_1591c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15920 : bv 32 := 0x02050a63.
Lemma F_15920 : fetch_word Ubsan.M.loaded_segments (0x15a1c : word) = Some W_15920.
Proof. vm_refl. Qed.
Lemma D_15920 : decode_any W_15920 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15924 : bv 32 := 0x00050413.
Lemma F_15924 : fetch_word Ubsan.M.loaded_segments (0x15a20 : word) = Some W_15924.
Proof. vm_refl. Qed.
Lemma D_15924 : decode_any W_15924 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15928 : bv 32 := 0x00757513.
Lemma F_15928 : fetch_word Ubsan.M.loaded_segments (0x15a24 : word) = Some W_15928.
Proof. vm_refl. Qed.
Lemma D_15928 : decode_any W_15928 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1592c : bv 32 := 0x08051663.
Lemma F_1592c : fetch_word Ubsan.M.loaded_segments (0x15a28 : word) = Some W_1592c.
Proof. vm_refl. Qed.
Lemma D_1592c : decode_any W_1592c = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15930 : bv 32 := 0x00058493.
Lemma F_15930 : fetch_word Ubsan.M.loaded_segments (0x15a2c : word) = Some W_15930.
Proof. vm_refl. Qed.
Lemma D_15930 : decode_any W_15930 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15934 : bv 32 := 0x00043503.
Lemma F_15934 : fetch_word Ubsan.M.loaded_segments (0x15a30 : word) = Some W_15934.
Proof. vm_refl. Qed.
Lemma D_15934 : decode_any W_15934 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15938 : bv 32 := 0x00050463.
Lemma F_15938 : fetch_word Ubsan.M.loaded_segments (0x15a34 : word) = Some W_15938.
Proof. vm_refl. Qed.
Lemma D_15938 : decode_any W_15938 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15940 : bv 32 := 0x04048863.
Lemma F_15940 : fetch_word Ubsan.M.loaded_segments (0x15a3c : word) = Some W_15940.
Proof. vm_refl. Qed.
Lemma D_15940 : decode_any W_15940 = Some (Branch BC_EQ 9 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15990 : bv 32 := 0x00000593.
Lemma F_15990 : fetch_word Ubsan.M.loaded_segments (0x15a8c : word) = Some W_15990.
Proof. vm_refl. Qed.
Lemma D_15990 : decode_any W_15990 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15994 : bv 32 := 0x00000513.
Lemma F_15994 : fetch_word Ubsan.M.loaded_segments (0x15a90 : word) = Some W_15994.
Proof. vm_refl. Qed.
Lemma D_15994 : decode_any W_15994 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15998 : bv 32 := 0x00b43023.
Lemma F_15998 : fetch_word Ubsan.M.loaded_segments (0x15a94 : word) = Some W_15998.
Proof. vm_refl. Qed.
Lemma D_15998 : decode_any W_15998 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1599c : bv 32 := 0x0080006f.
Lemma F_1599c : fetch_word Ubsan.M.loaded_segments (0x15a98 : word) = Some W_1599c.
Proof. vm_refl. Qed.
Lemma D_1599c : decode_any W_1599c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a4 : bv 32 := 0x01813083.
Lemma F_159a4 : fetch_word Ubsan.M.loaded_segments (0x15aa0 : word) = Some W_159a4.
Proof. vm_refl. Qed.
Lemma D_159a4 : decode_any W_159a4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159a8 : bv 32 := 0x01013403.
Lemma F_159a8 : fetch_word Ubsan.M.loaded_segments (0x15aa4 : word) = Some W_159a8.
Proof. vm_refl. Qed.
Lemma D_159a8 : decode_any W_159a8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159ac : bv 32 := 0x00813483.
Lemma F_159ac : fetch_word Ubsan.M.loaded_segments (0x15aa8 : word) = Some W_159ac.
Proof. vm_refl. Qed.
Lemma D_159ac : decode_any W_159ac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b0 : bv 32 := 0x02010113.
Lemma F_159b0 : fetch_word Ubsan.M.loaded_segments (0x15aac : word) = Some W_159b0.
Proof. vm_refl. Qed.
Lemma D_159b0 : decode_any W_159b0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b4 : bv 32 := 0x00008067.
Lemma F_159b4 : fetch_word Ubsan.M.loaded_segments (0x15ab0 : word) = Some W_159b4.
Proof. vm_refl. Qed.
Lemma D_159b4 : decode_any W_159b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b04 : bv 32 := 0xff010113.
Lemma F_15b04 : fetch_word Ubsan.M.loaded_segments (0x15c00 : word) = Some W_15b04.
Proof. vm_refl. Qed.
Lemma D_15b04 : decode_any W_15b04 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b08 : bv 32 := 0x00113423.
Lemma F_15b08 : fetch_word Ubsan.M.loaded_segments (0x15c04 : word) = Some W_15b08.
Proof. vm_refl. Qed.
Lemma D_15b08 : decode_any W_15b08 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b0c : bv 32 := 0x00813023.
Lemma F_15b0c : fetch_word Ubsan.M.loaded_segments (0x15c08 : word) = Some W_15b0c.
Proof. vm_refl. Qed.
Lemma D_15b0c : decode_any W_15b0c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b10 : bv 32 := 0x098000ef.
Lemma F_15b10 : fetch_word Ubsan.M.loaded_segments (0x15c0c : word) = Some W_15b10.
Proof. vm_refl. Qed.
Lemma D_15b10 : decode_any W_15b10 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b14 : bv 32 := 0x04050263.
Lemma F_15b14 : fetch_word Ubsan.M.loaded_segments (0x15c10 : word) = Some W_15b14.
Proof. vm_refl. Qed.
Lemma D_15b14 : decode_any W_15b14 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b18 : bv 32 := 0x00757593.
Lemma F_15b18 : fetch_word Ubsan.M.loaded_segments (0x15c14 : word) = Some W_15b18.
Proof. vm_refl. Qed.
Lemma D_15b18 : decode_any W_15b18 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b1c : bv 32 := 0x08059463.
Lemma F_15b1c : fetch_word Ubsan.M.loaded_segments (0x15c18 : word) = Some W_15b1c.
Proof. vm_refl. Qed.
Lemma D_15b1c : decode_any W_15b1c = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b20 : bv 32 := 0x01056583.
Lemma F_15b20 : fetch_word Ubsan.M.loaded_segments (0x15c1c : word) = Some W_15b20.
Proof. vm_refl. Qed.
Lemma D_15b20 : decode_any W_15b20 = Some (Load SZ4 false 11 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b24 : bv 32 := 0x00456603.
Lemma F_15b24 : fetch_word Ubsan.M.loaded_segments (0x15c20 : word) = Some W_15b24.
Proof. vm_refl. Qed.
Lemma D_15b24 : decode_any W_15b24 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b28 : bv 32 := 0x00259593.
Lemma F_15b28 : fetch_word Ubsan.M.loaded_segments (0x15c24 : word) = Some W_15b28.
Proof. vm_refl. Qed.
Lemma D_15b28 : decode_any W_15b28 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b2c : bv 32 := 0x02c596b3.
Lemma F_15b2c : fetch_word Ubsan.M.loaded_segments (0x15c28 : word) = Some W_15b2c.
Proof. vm_refl. Qed.
Lemma D_15b2c : decode_any W_15b2c = Some (Mul M_MULH 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b30 : bv 32 := 0x02c58633.
Lemma F_15b30 : fetch_word Ubsan.M.loaded_segments (0x15c2c : word) = Some W_15b30.
Proof. vm_refl. Qed.
Lemma D_15b30 : decode_any W_15b30 = Some (Mul M_MUL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b34 : bv 32 := 0x43f65593.
Lemma F_15b34 : fetch_word Ubsan.M.loaded_segments (0x15c30 : word) = Some W_15b34.
Proof. vm_refl. Qed.
Lemma D_15b34 : decode_any W_15b34 = Some (ShiftImm ALU_SRA 11 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b38 : bv 32 := 0x06b69663.
Lemma F_15b38 : fetch_word Ubsan.M.loaded_segments (0x15c34 : word) = Some W_15b38.
Proof. vm_refl. Qed.
Lemma D_15b38 : decode_any W_15b38 = Some (Branch BC_NE 13 11 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b3c : bv 32 := 0x03853583.
Lemma F_15b3c : fetch_word Ubsan.M.loaded_segments (0x15c38 : word) = Some W_15b3c.
Proof. vm_refl. Qed.
Lemma D_15b3c : decode_any W_15b3c = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b40 : bv 32 := 0x00050413.
Lemma F_15b40 : fetch_word Ubsan.M.loaded_segments (0x15c3c : word) = Some W_15b40.
Proof. vm_refl. Qed.
Lemma D_15b40 : decode_any W_15b40 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b44 : bv 32 := 0x00058513.
Lemma F_15b44 : fetch_word Ubsan.M.loaded_segments (0x15c40 : word) = Some W_15b44.
Proof. vm_refl. Qed.
Lemma D_15b44 : decode_any W_15b44 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b48 : bv 32 := 0x00000593.
Lemma F_15b48 : fetch_word Ubsan.M.loaded_segments (0x15c44 : word) = Some W_15b48.
Proof. vm_refl. Qed.
Lemma D_15b48 : decode_any W_15b48 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b4c : bv 32 := 0x2f91c0ef.
Lemma F_15b4c : fetch_word Ubsan.M.loaded_segments (0x15c48 : word) = Some W_15b4c.
Proof. vm_refl. Qed.
Lemma D_15b4c : decode_any W_15b4c = Some (Jal 1 117496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b50 : bv 32 := 0x00040513.
Lemma F_15b50 : fetch_word Ubsan.M.loaded_segments (0x15c4c : word) = Some W_15b50.
Proof. vm_refl. Qed.
Lemma D_15b50 : decode_any W_15b50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b54 : bv 32 := 0x0400006f.
Lemma F_15b54 : fetch_word Ubsan.M.loaded_segments (0x15c50 : word) = Some W_15b54.
Proof. vm_refl. Qed.
Lemma D_15b54 : decode_any W_15b54 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b58 : bv 32 := 0x0001e517.
Lemma F_15b58 : fetch_word Ubsan.M.loaded_segments (0x15c54 : word) = Some W_15b58.
Proof. vm_refl. Qed.
Lemma D_15b58 : decode_any W_15b58 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b5c : bv 32 := 0x13c53503.
Lemma F_15b5c : fetch_word Ubsan.M.loaded_segments (0x15c58 : word) = Some W_15b5c.
Proof. vm_refl. Qed.
Lemma D_15b5c : decode_any W_15b5c = Some (Load SZ8 true 10 10 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b60 : bv 32 := 0x00052503.
Lemma F_15b60 : fetch_word Ubsan.M.loaded_segments (0x15c5c : word) = Some W_15b60.
Proof. vm_refl. Qed.
Lemma D_15b60 : decode_any W_15b60 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b64 : bv 32 := 0x00500593.
Lemma F_15b64 : fetch_word Ubsan.M.loaded_segments (0x15c60 : word) = Some W_15b64.
Proof. vm_refl. Qed.
Lemma D_15b64 : decode_any W_15b64 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b68 : bv 32 := 0x02a5c463.
Lemma F_15b68 : fetch_word Ubsan.M.loaded_segments (0x15c64 : word) = Some W_15b68.
Proof. vm_refl. Qed.
Lemma D_15b68 : decode_any W_15b68 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b6c : bv 32 := 0xffffb517.
Lemma F_15b6c : fetch_word Ubsan.M.loaded_segments (0x15c68 : word) = Some W_15b6c.
Proof. vm_refl. Qed.
Lemma D_15b6c : decode_any W_15b6c = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b70 : bv 32 := 0xffffb597.
Lemma F_15b70 : fetch_word Ubsan.M.loaded_segments (0x15c6c : word) = Some W_15b70.
Proof. vm_refl. Qed.
Lemma D_15b70 : decode_any W_15b70 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b74 : bv 32 := 0x8e250513.
Lemma F_15b74 : fetch_word Ubsan.M.loaded_segments (0x15c70 : word) = Some W_15b74.
Proof. vm_refl. Qed.
Lemma D_15b74 : decode_any W_15b74 = Some (OpImm ALU_ADD 10 10 2274, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b78 : bv 32 := 0xd5958593.
Lemma F_15b78 : fetch_word Ubsan.M.loaded_segments (0x15c74 : word) = Some W_15b78.
Proof. vm_refl. Qed.
Lemma D_15b78 : decode_any W_15b78 = Some (OpImm ALU_ADD 11 11 3417, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b7c : bv 32 := 0x00000613.
Lemma F_15b7c : fetch_word Ubsan.M.loaded_segments (0x15c78 : word) = Some W_15b7c.
Proof. vm_refl. Qed.
Lemma D_15b7c : decode_any W_15b7c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b80 : bv 32 := 0x00813083.
Lemma F_15b80 : fetch_word Ubsan.M.loaded_segments (0x15c7c : word) = Some W_15b80.
Proof. vm_refl. Qed.
Lemma D_15b80 : decode_any W_15b80 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b84 : bv 32 := 0x00013403.
Lemma F_15b84 : fetch_word Ubsan.M.loaded_segments (0x15c80 : word) = Some W_15b84.
Proof. vm_refl. Qed.
Lemma D_15b84 : decode_any W_15b84 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b88 : bv 32 := 0x01010113.
Lemma F_15b88 : fetch_word Ubsan.M.loaded_segments (0x15c84 : word) = Some W_15b88.
Proof. vm_refl. Qed.
Lemma D_15b88 : decode_any W_15b88 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b8c : bv 32 := 0xbe5ff06f.
Lemma F_15b8c : fetch_word Ubsan.M.loaded_segments (0x15c88 : word) = Some W_15b8c.
Proof. vm_refl. Qed.
Lemma D_15b8c : decode_any W_15b8c = Some (Jal 0 2096100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b94 : bv 32 := 0x00813083.
Lemma F_15b94 : fetch_word Ubsan.M.loaded_segments (0x15c90 : word) = Some W_15b94.
Proof. vm_refl. Qed.
Lemma D_15b94 : decode_any W_15b94 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b98 : bv 32 := 0x00013403.
Lemma F_15b98 : fetch_word Ubsan.M.loaded_segments (0x15c94 : word) = Some W_15b98.
Proof. vm_refl. Qed.
Lemma D_15b98 : decode_any W_15b98 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b9c : bv 32 := 0x01010113.
Lemma F_15b9c : fetch_word Ubsan.M.loaded_segments (0x15c98 : word) = Some W_15b9c.
Proof. vm_refl. Qed.
Lemma D_15b9c : decode_any W_15b9c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ba0 : bv 32 := 0x00008067.
Lemma F_15ba0 : fetch_word Ubsan.M.loaded_segments (0x15c9c : word) = Some W_15ba0.
Proof. vm_refl. Qed.
Lemma D_15ba0 : decode_any W_15ba0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ba8 : bv 32 := 0xfe010113.
Lemma F_15ba8 : fetch_word Ubsan.M.loaded_segments (0x15ca4 : word) = Some W_15ba8.
Proof. vm_refl. Qed.
Lemma D_15ba8 : decode_any W_15ba8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bac : bv 32 := 0x00113c23.
Lemma F_15bac : fetch_word Ubsan.M.loaded_segments (0x15ca8 : word) = Some W_15bac.
Proof. vm_refl. Qed.
Lemma D_15bac : decode_any W_15bac = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb0 : bv 32 := 0x00813823.
Lemma F_15bb0 : fetch_word Ubsan.M.loaded_segments (0x15cac : word) = Some W_15bb0.
Proof. vm_refl. Qed.
Lemma D_15bb0 : decode_any W_15bb0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb4 : bv 32 := 0x00913423.
Lemma F_15bb4 : fetch_word Ubsan.M.loaded_segments (0x15cb0 : word) = Some W_15bb4.
Proof. vm_refl. Qed.
Lemma D_15bb4 : decode_any W_15bb4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bb8 : bv 32 := 0x00058493.
Lemma F_15bb8 : fetch_word Ubsan.M.loaded_segments (0x15cb4 : word) = Some W_15bb8.
Proof. vm_refl. Qed.
Lemma D_15bb8 : decode_any W_15bb8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bbc : bv 32 := 0x134000ef.
Lemma F_15bbc : fetch_word Ubsan.M.loaded_segments (0x15cb8 : word) = Some W_15bbc.
Proof. vm_refl. Qed.
Lemma D_15bbc : decode_any W_15bbc = Some (Jal 1 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bc0 : bv 32 := 0x04050863.
Lemma F_15bc0 : fetch_word Ubsan.M.loaded_segments (0x15cbc : word) = Some W_15bc0.
Proof. vm_refl. Qed.
Lemma D_15bc0 : decode_any W_15bc0 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bc4 : bv 32 := 0x00050413.
Lemma F_15bc4 : fetch_word Ubsan.M.loaded_segments (0x15cc0 : word) = Some W_15bc4.
Proof. vm_refl. Qed.
Lemma D_15bc4 : decode_any W_15bc4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bc8 : bv 32 := 0x00757513.
Lemma F_15bc8 : fetch_word Ubsan.M.loaded_segments (0x15cc4 : word) = Some W_15bc8.
Proof. vm_refl. Qed.
Lemma D_15bc8 : decode_any W_15bc8 = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bcc : bv 32 := 0x12051063.
Lemma F_15bcc : fetch_word Ubsan.M.loaded_segments (0x15cc8 : word) = Some W_15bcc.
Proof. vm_refl. Qed.
Lemma D_15bcc : decode_any W_15bcc = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bd0 : bv 32 := 0x01042503.
Lemma F_15bd0 : fetch_word Ubsan.M.loaded_segments (0x15ccc : word) = Some W_15bd0.
Proof. vm_refl. Qed.
Lemma D_15bd0 : decode_any W_15bd0 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bd4 : bv 32 := 0x00251513.
Lemma F_15bd4 : fetch_word Ubsan.M.loaded_segments (0x15cd0 : word) = Some W_15bd4.
Proof. vm_refl. Qed.
Lemma D_15bd4 : decode_any W_15bd4 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bd8 : bv 32 := 0x029515b3.
Lemma F_15bd8 : fetch_word Ubsan.M.loaded_segments (0x15cd4 : word) = Some W_15bd8.
Proof. vm_refl. Qed.
Lemma D_15bd8 : decode_any W_15bd8 = Some (Mul M_MULH 11 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bdc : bv 32 := 0x02950533.
Lemma F_15bdc : fetch_word Ubsan.M.loaded_segments (0x15cd8 : word) = Some W_15bdc.
Proof. vm_refl. Qed.
Lemma D_15bdc : decode_any W_15bdc = Some (Mul M_MUL 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15be0 : bv 32 := 0x43f55613.
Lemma F_15be0 : fetch_word Ubsan.M.loaded_segments (0x15cdc : word) = Some W_15be0.
Proof. vm_refl. Qed.
Lemma D_15be0 : decode_any W_15be0 = Some (ShiftImm ALU_SRA 12 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15be4 : bv 32 := 0x10c59463.
Lemma F_15be4 : fetch_word Ubsan.M.loaded_segments (0x15ce0 : word) = Some W_15be4.
Proof. vm_refl. Qed.
Lemma D_15be4 : decode_any W_15be4 = Some (Branch BC_NE 11 12 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15be8 : bv 32 := 0x0001f597.
Lemma F_15be8 : fetch_word Ubsan.M.loaded_segments (0x15ce4 : word) = Some W_15be8.
Proof. vm_refl. Qed.
Lemma D_15be8 : decode_any W_15be8 = Some (Auipc 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bec : bv 32 := 0x12c58493.
Lemma F_15bec : fetch_word Ubsan.M.loaded_segments (0x15ce8 : word) = Some W_15bec.
Proof. vm_refl. Qed.
Lemma D_15bec : decode_any W_15bec = Some (OpImm ALU_ADD 9 11 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bf0 : bv 32 := 0x0004b583.
Lemma F_15bf0 : fetch_word Ubsan.M.loaded_segments (0x15cec : word) = Some W_15bf0.
Proof. vm_refl. Qed.
Lemma D_15bf0 : decode_any W_15bf0 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bf4 : bv 32 := 0x000580e7.
Lemma F_15bf4 : fetch_word Ubsan.M.loaded_segments (0x15cf0 : word) = Some W_15bf4.
Proof. vm_refl. Qed.
Lemma D_15bf4 : decode_any W_15bf4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bf8 : bv 32 := 0x04050a63.
Lemma F_15bf8 : fetch_word Ubsan.M.loaded_segments (0x15cf4 : word) = Some W_15bf8.
Proof. vm_refl. Qed.
Lemma D_15bf8 : decode_any W_15bf8 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15bfc : bv 32 := 0x02a43c23.
Lemma F_15bfc : fetch_word Ubsan.M.loaded_segments (0x15cf8 : word) = Some W_15bfc.
Proof. vm_refl. Qed.
Lemma D_15bfc : decode_any W_15bfc = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c00 : bv 32 := 0x00040513.
Lemma F_15c00 : fetch_word Ubsan.M.loaded_segments (0x15cfc : word) = Some W_15c00.
Proof. vm_refl. Qed.
Lemma D_15c00 : decode_any W_15c00 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c04 : bv 32 := 0x00000593.
Lemma F_15c04 : fetch_word Ubsan.M.loaded_segments (0x15d00 : word) = Some W_15c04.
Proof. vm_refl. Qed.
Lemma D_15c04 : decode_any W_15c04 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c08 : bv 32 := 0x070020ef.
Lemma F_15c08 : fetch_word Ubsan.M.loaded_segments (0x15d04 : word) = Some W_15c08.
Proof. vm_refl. Qed.
Lemma D_15c08 : decode_any W_15c08 = Some (Jal 1 8304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c0c : bv 32 := 0x0c80006f.
Lemma F_15c0c : fetch_word Ubsan.M.loaded_segments (0x15d08 : word) = Some W_15c0c.
Proof. vm_refl. Qed.
Lemma D_15c0c : decode_any W_15c0c = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c10 : bv 32 := 0x0001e517.
Lemma F_15c10 : fetch_word Ubsan.M.loaded_segments (0x15d0c : word) = Some W_15c10.
Proof. vm_refl. Qed.
Lemma D_15c10 : decode_any W_15c10 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c14 : bv 32 := 0x08453503.
Lemma F_15c14 : fetch_word Ubsan.M.loaded_segments (0x15d10 : word) = Some W_15c14.
Proof. vm_refl. Qed.
Lemma D_15c14 : decode_any W_15c14 = Some (Load SZ8 true 10 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c18 : bv 32 := 0x00052503.
Lemma F_15c18 : fetch_word Ubsan.M.loaded_segments (0x15d14 : word) = Some W_15c18.
Proof. vm_refl. Qed.
Lemma D_15c18 : decode_any W_15c18 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c1c : bv 32 := 0x00500593.
Lemma F_15c1c : fetch_word Ubsan.M.loaded_segments (0x15d18 : word) = Some W_15c1c.
Proof. vm_refl. Qed.
Lemma D_15c1c : decode_any W_15c1c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c20 : bv 32 := 0x0aa5c863.
Lemma F_15c20 : fetch_word Ubsan.M.loaded_segments (0x15d1c : word) = Some W_15c20.
Proof. vm_refl. Qed.
Lemma D_15c20 : decode_any W_15c20 = Some (Branch BC_LT 11 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c24 : bv 32 := 0xffffb517.
Lemma F_15c24 : fetch_word Ubsan.M.loaded_segments (0x15d20 : word) = Some W_15c24.
Proof. vm_refl. Qed.
Lemma D_15c24 : decode_any W_15c24 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c28 : bv 32 := 0xffffb597.
Lemma F_15c28 : fetch_word Ubsan.M.loaded_segments (0x15d24 : word) = Some W_15c28.
Proof. vm_refl. Qed.
Lemma D_15c28 : decode_any W_15c28 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c2c : bv 32 := 0x82a50513.
Lemma F_15c2c : fetch_word Ubsan.M.loaded_segments (0x15d28 : word) = Some W_15c2c.
Proof. vm_refl. Qed.
Lemma D_15c2c : decode_any W_15c2c = Some (OpImm ALU_ADD 10 10 2090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c30 : bv 32 := 0xa6658593.
Lemma F_15c30 : fetch_word Ubsan.M.loaded_segments (0x15d2c : word) = Some W_15c30.
Proof. vm_refl. Qed.
Lemma D_15c30 : decode_any W_15c30 = Some (OpImm ALU_ADD 11 11 2662, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c34 : bv 32 := 0x00000613.
Lemma F_15c34 : fetch_word Ubsan.M.loaded_segments (0x15d30 : word) = Some W_15c34.
Proof. vm_refl. Qed.
Lemma D_15c34 : decode_any W_15c34 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c38 : bv 32 := 0x01813083.
Lemma F_15c38 : fetch_word Ubsan.M.loaded_segments (0x15d34 : word) = Some W_15c38.
Proof. vm_refl. Qed.
Lemma D_15c38 : decode_any W_15c38 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c3c : bv 32 := 0x01013403.
Lemma F_15c3c : fetch_word Ubsan.M.loaded_segments (0x15d38 : word) = Some W_15c3c.
Proof. vm_refl. Qed.
Lemma D_15c3c : decode_any W_15c3c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c40 : bv 32 := 0x00813483.
Lemma F_15c40 : fetch_word Ubsan.M.loaded_segments (0x15d3c : word) = Some W_15c40.
Proof. vm_refl. Qed.
Lemma D_15c40 : decode_any W_15c40 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c44 : bv 32 := 0x02010113.
Lemma F_15c44 : fetch_word Ubsan.M.loaded_segments (0x15d40 : word) = Some W_15c44.
Proof. vm_refl. Qed.
Lemma D_15c44 : decode_any W_15c44 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c48 : bv 32 := 0xb29ff06f.
Lemma F_15c48 : fetch_word Ubsan.M.loaded_segments (0x15d44 : word) = Some W_15c48.
Proof. vm_refl. Qed.
Lemma D_15c48 : decode_any W_15c48 = Some (Jal 0 2095912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c4c : bv 32 := 0x01440513.
Lemma F_15c4c : fetch_word Ubsan.M.loaded_segments (0x15d48 : word) = Some W_15c4c.
Proof. vm_refl. Qed.
Lemma D_15c4c : decode_any W_15c4c = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c50 : bv 32 := 0xfff00593.
Lemma F_15c50 : fetch_word Ubsan.M.loaded_segments (0x15d4c : word) = Some W_15c50.
Proof. vm_refl. Qed.
Lemma D_15c50 : decode_any W_15c50 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c54 : bv 32 := 0x06b5252f.
Lemma F_15c54 : fetch_word Ubsan.M.loaded_segments (0x15d50 : word) = Some W_15c54.
Proof. vm_refl. Qed.
Lemma D_15c54 : decode_any W_15c54 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c58 : bv 32 := 0x00100593.
Lemma F_15c58 : fetch_word Ubsan.M.loaded_segments (0x15d54 : word) = Some W_15c58.
Proof. vm_refl. Qed.
Lemma D_15c58 : decode_any W_15c58 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c5c : bv 32 := 0x04b51063.
Lemma F_15c5c : fetch_word Ubsan.M.loaded_segments (0x15d58 : word) = Some W_15c5c.
Proof. vm_refl. Qed.
Lemma D_15c5c : decode_any W_15c5c = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c60 : bv 32 := 0x03843503.
Lemma F_15c60 : fetch_word Ubsan.M.loaded_segments (0x15d5c : word) = Some W_15c60.
Proof. vm_refl. Qed.
Lemma D_15c60 : decode_any W_15c60 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c64 : bv 32 := 0x00050663.
Lemma F_15c64 : fetch_word Ubsan.M.loaded_segments (0x15d60 : word) = Some W_15c64.
Proof. vm_refl. Qed.
Lemma D_15c64 : decode_any W_15c64 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c70 : bv 32 := 0x02843503.
Lemma F_15c70 : fetch_word Ubsan.M.loaded_segments (0x15d6c : word) = Some W_15c70.
Proof. vm_refl. Qed.
Lemma D_15c70 : decode_any W_15c70 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c74 : bv 32 := 0x00050463.
Lemma F_15c74 : fetch_word Ubsan.M.loaded_segments (0x15d70 : word) = Some W_15c74.
Proof. vm_refl. Qed.
Lemma D_15c74 : decode_any W_15c74 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c7c : bv 32 := 0x03043503.
Lemma F_15c7c : fetch_word Ubsan.M.loaded_segments (0x15d78 : word) = Some W_15c7c.
Proof. vm_refl. Qed.
Lemma D_15c7c : decode_any W_15c7c = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c80 : bv 32 := 0x00a13023.
Lemma F_15c80 : fetch_word Ubsan.M.loaded_segments (0x15d7c : word) = Some W_15c80.
Proof. vm_refl. Qed.
Lemma D_15c80 : decode_any W_15c80 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c84 : bv 32 := 0x00050863.
Lemma F_15c84 : fetch_word Ubsan.M.loaded_segments (0x15d80 : word) = Some W_15c84.
Proof. vm_refl. Qed.
Lemma D_15c84 : decode_any W_15c84 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c94 : bv 32 := 0x00040513.
Lemma F_15c94 : fetch_word Ubsan.M.loaded_segments (0x15d90 : word) = Some W_15c94.
Proof. vm_refl. Qed.
Lemma D_15c94 : decode_any W_15c94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c98 : bv 32 := 0x474150ef.
Lemma F_15c98 : fetch_word Ubsan.M.loaded_segments (0x15d94 : word) = Some W_15c98.
Proof. vm_refl. Qed.
Lemma D_15c98 : decode_any W_15c98 = Some (Jal 1 87156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15c9c : bv 32 := 0x0001e517.
Lemma F_15c9c : fetch_word Ubsan.M.loaded_segments (0x15d98 : word) = Some W_15c9c.
Proof. vm_refl. Qed.
Lemma D_15c9c : decode_any W_15c9c = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ca0 : bv 32 := 0xff853503.
Lemma F_15ca0 : fetch_word Ubsan.M.loaded_segments (0x15d9c : word) = Some W_15ca0.
Proof. vm_refl. Qed.
Lemma D_15ca0 : decode_any W_15ca0 = Some (Load SZ8 true 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ca4 : bv 32 := 0x00052503.
Lemma F_15ca4 : fetch_word Ubsan.M.loaded_segments (0x15da0 : word) = Some W_15ca4.
Proof. vm_refl. Qed.
Lemma D_15ca4 : decode_any W_15ca4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ca8 : bv 32 := 0x00500593.
Lemma F_15ca8 : fetch_word Ubsan.M.loaded_segments (0x15da4 : word) = Some W_15ca8.
Proof. vm_refl. Qed.
Lemma D_15ca8 : decode_any W_15ca8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cac : bv 32 := 0x02a5c263.
Lemma F_15cac : fetch_word Ubsan.M.loaded_segments (0x15da8 : word) = Some W_15cac.
Proof. vm_refl. Qed.
Lemma D_15cac : decode_any W_15cac = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cb0 : bv 32 := 0xffffb517.
Lemma F_15cb0 : fetch_word Ubsan.M.loaded_segments (0x15dac : word) = Some W_15cb0.
Proof. vm_refl. Qed.
Lemma D_15cb0 : decode_any W_15cb0 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cb4 : bv 32 := 0xffffb597.
Lemma F_15cb4 : fetch_word Ubsan.M.loaded_segments (0x15db0 : word) = Some W_15cb4.
Proof. vm_refl. Qed.
Lemma D_15cb4 : decode_any W_15cb4 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cb8 : bv 32 := 0x45f50513.
Lemma F_15cb8 : fetch_word Ubsan.M.loaded_segments (0x15db4 : word) = Some W_15cb8.
Proof. vm_refl. Qed.
Lemma D_15cb8 : decode_any W_15cb8 = Some (OpImm ALU_ADD 10 10 1119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cbc : bv 32 := 0x9da58593.
Lemma F_15cbc : fetch_word Ubsan.M.loaded_segments (0x15db8 : word) = Some W_15cbc.
Proof. vm_refl. Qed.
Lemma D_15cbc : decode_any W_15cbc = Some (OpImm ALU_ADD 11 11 2522, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cc0 : bv 32 := 0x00000613.
Lemma F_15cc0 : fetch_word Ubsan.M.loaded_segments (0x15dbc : word) = Some W_15cc0.
Proof. vm_refl. Qed.
Lemma D_15cc0 : decode_any W_15cc0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cc4 : bv 32 := 0xaadff0ef.
Lemma F_15cc4 : fetch_word Ubsan.M.loaded_segments (0x15dc0 : word) = Some W_15cc4.
Proof. vm_refl. Qed.
Lemma D_15cc4 : decode_any W_15cc4 = Some (Jal 1 2095788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cc8 : bv 32 := 0x00050413.
Lemma F_15cc8 : fetch_word Ubsan.M.loaded_segments (0x15dc4 : word) = Some W_15cc8.
Proof. vm_refl. Qed.
Lemma D_15cc8 : decode_any W_15cc8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ccc : bv 32 := 0x0080006f.
Lemma F_15ccc : fetch_word Ubsan.M.loaded_segments (0x15dc8 : word) = Some W_15ccc.
Proof. vm_refl. Qed.
Lemma D_15ccc : decode_any W_15ccc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cd4 : bv 32 := 0x00040513.
Lemma F_15cd4 : fetch_word Ubsan.M.loaded_segments (0x15dd0 : word) = Some W_15cd4.
Proof. vm_refl. Qed.
Lemma D_15cd4 : decode_any W_15cd4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cd8 : bv 32 := 0x01813083.
Lemma F_15cd8 : fetch_word Ubsan.M.loaded_segments (0x15dd4 : word) = Some W_15cd8.
Proof. vm_refl. Qed.
Lemma D_15cd8 : decode_any W_15cd8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15cdc : bv 32 := 0x01013403.
Lemma F_15cdc : fetch_word Ubsan.M.loaded_segments (0x15dd8 : word) = Some W_15cdc.
Proof. vm_refl. Qed.
Lemma D_15cdc : decode_any W_15cdc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce0 : bv 32 := 0x00813483.
Lemma F_15ce0 : fetch_word Ubsan.M.loaded_segments (0x15ddc : word) = Some W_15ce0.
Proof. vm_refl. Qed.
Lemma D_15ce0 : decode_any W_15ce0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce4 : bv 32 := 0x02010113.
Lemma F_15ce4 : fetch_word Ubsan.M.loaded_segments (0x15de0 : word) = Some W_15ce4.
Proof. vm_refl. Qed.
Lemma D_15ce4 : decode_any W_15ce4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ce8 : bv 32 := 0x00008067.
Lemma F_15ce8 : fetch_word Ubsan.M.loaded_segments (0x15de4 : word) = Some W_15ce8.
Proof. vm_refl. Qed.
Lemma D_15ce8 : decode_any W_15ce8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
