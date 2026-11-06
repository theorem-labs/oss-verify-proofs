(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.H Require GcFlushS16.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_13580 : bv 32 := 0xfe010113.
Lemma F_13580 : fetch_word Plain.M.loaded_segments (0x1367c : word) = Some W_13580.
Proof. vm_refl. Qed.
Lemma D_13580 : decode_any W_13580 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13584 : bv 32 := 0x00113c23.
Lemma F_13584 : fetch_word Plain.M.loaded_segments (0x13680 : word) = Some W_13584.
Proof. vm_refl. Qed.
Lemma D_13584 : decode_any W_13584 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13588 : bv 32 := 0x00813823.
Lemma F_13588 : fetch_word Plain.M.loaded_segments (0x13684 : word) = Some W_13588.
Proof. vm_refl. Qed.
Lemma D_13588 : decode_any W_13588 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1358c : bv 32 := 0x00913423.
Lemma F_1358c : fetch_word Plain.M.loaded_segments (0x13688 : word) = Some W_1358c.
Proof. vm_refl. Qed.
Lemma D_1358c : decode_any W_1358c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13590 : bv 32 := 0x00058413.
Lemma F_13590 : fetch_word Plain.M.loaded_segments (0x1368c : word) = Some W_13590.
Proof. vm_refl. Qed.
Lemma D_13590 : decode_any W_13590 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13594 : bv 32 := 0x00300593.
Lemma F_13594 : fetch_word Plain.M.loaded_segments (0x13690 : word) = Some W_13594.
Proof. vm_refl. Qed.
Lemma D_13594 : decode_any W_13594 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13598 : bv 32 := 0x02b46c63.
Lemma F_13598 : fetch_word Plain.M.loaded_segments (0x13694 : word) = Some W_13598.
Proof. vm_refl. Qed.
Lemma D_13598 : decode_any W_13598 = Some (Branch BC_LTU 8 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1359c : bv 32 := 0x00050493.
Lemma F_1359c : fetch_word Plain.M.loaded_segments (0x13698 : word) = Some W_1359c.
Proof. vm_refl. Qed.
Lemma D_1359c : decode_any W_1359c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135a0 : bv 32 := 0x00000517.
Lemma F_135a0 : fetch_word Plain.M.loaded_segments (0x1369c : word) = Some W_135a0.
Proof. vm_refl. Qed.
Lemma D_135a0 : decode_any W_135a0 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135a4 : bv 32 := 0x04850513.
Lemma F_135a4 : fetch_word Plain.M.loaded_segments (0x136a0 : word) = Some W_135a4.
Proof. vm_refl. Qed.
Lemma D_135a4 : decode_any W_135a4 = Some (OpImm ALU_ADD 10 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135a8 : bv 32 := 0x160000ef.
Lemma F_135a8 : fetch_word Plain.M.loaded_segments (0x136a4 : word) = Some W_135a8.
Proof. vm_refl. Qed.
Lemma D_135a8 : decode_any W_135a8 = Some (Jal 1 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135ac : bv 32 := 0x00048513.
Lemma F_135ac : fetch_word Plain.M.loaded_segments (0x136a8 : word) = Some W_135ac.
Proof. vm_refl. Qed.
Lemma D_135ac : decode_any W_135ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135b0 : bv 32 := 0x00040593.
Lemma F_135b0 : fetch_word Plain.M.loaded_segments (0x136ac : word) = Some W_135b0.
Proof. vm_refl. Qed.
Lemma D_135b0 : decode_any W_135b0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135b4 : bv 32 := 0x5dc010ef.
Lemma F_135b4 : fetch_word Plain.M.loaded_segments (0x136b0 : word) = Some W_135b4.
Proof. vm_refl. Qed.
Lemma D_135b4 : decode_any W_135b4 = Some (Jal 1 5596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135b8 : bv 32 := 0x00a13023.
Lemma F_135b8 : fetch_word Plain.M.loaded_segments (0x136b4 : word) = Some W_135b8.
Proof. vm_refl. Qed.
Lemma D_135b8 : decode_any W_135b8 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135bc : bv 32 := 0x00050a63.
Lemma F_135bc : fetch_word Plain.M.loaded_segments (0x136b8 : word) = Some W_135bc.
Proof. vm_refl. Qed.
Lemma D_135bc : decode_any W_135bc = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135c0 : bv 32 := 0x00000593.
Lemma F_135c0 : fetch_word Plain.M.loaded_segments (0x136bc : word) = Some W_135c0.
Proof. vm_refl. Qed.
Lemma D_135c0 : decode_any W_135c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135c4 : bv 32 := 0x560010ef.
Lemma F_135c4 : fetch_word Plain.M.loaded_segments (0x136c0 : word) = Some W_135c4.
Proof. vm_refl. Qed.
Lemma D_135c4 : decode_any W_135c4 = Some (Jal 1 5472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135c8 : bv 32 := 0x00010513.
Lemma F_135c8 : fetch_word Plain.M.loaded_segments (0x136c4 : word) = Some W_135c8.
Proof. vm_refl. Qed.
Lemma D_135c8 : decode_any W_135c8 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135cc : bv 32 := 0x658000ef.
Lemma F_135cc : fetch_word Plain.M.loaded_segments (0x136c8 : word) = Some W_135cc.
Proof. vm_refl. Qed.
Lemma D_135cc : decode_any W_135cc = Some (Jal 1 1624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135d0 : bv 32 := 0x00000513.
Lemma F_135d0 : fetch_word Plain.M.loaded_segments (0x136cc : word) = Some W_135d0.
Proof. vm_refl. Qed.
Lemma D_135d0 : decode_any W_135d0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135d4 : bv 32 := 0x01813083.
Lemma F_135d4 : fetch_word Plain.M.loaded_segments (0x136d0 : word) = Some W_135d4.
Proof. vm_refl. Qed.
Lemma D_135d4 : decode_any W_135d4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135d8 : bv 32 := 0x01013403.
Lemma F_135d8 : fetch_word Plain.M.loaded_segments (0x136d4 : word) = Some W_135d8.
Proof. vm_refl. Qed.
Lemma D_135d8 : decode_any W_135d8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135dc : bv 32 := 0x00813483.
Lemma F_135dc : fetch_word Plain.M.loaded_segments (0x136d8 : word) = Some W_135dc.
Proof. vm_refl. Qed.
Lemma D_135dc : decode_any W_135dc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135e0 : bv 32 := 0x02010113.
Lemma F_135e0 : fetch_word Plain.M.loaded_segments (0x136dc : word) = Some W_135e0.
Proof. vm_refl. Qed.
Lemma D_135e0 : decode_any W_135e0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135e4 : bv 32 := 0x00008067.
Lemma F_135e4 : fetch_word Plain.M.loaded_segments (0x136e0 : word) = Some W_135e4.
Proof. vm_refl. Qed.
Lemma D_135e4 : decode_any W_135e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135ec : bv 32 := 0xff010113.
Lemma F_135ec : fetch_word Plain.M.loaded_segments (0x136e8 : word) = Some W_135ec.
Proof. vm_refl. Qed.
Lemma D_135ec : decode_any W_135ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135f0 : bv 32 := 0x00113423.
Lemma F_135f0 : fetch_word Plain.M.loaded_segments (0x136ec : word) = Some W_135f0.
Proof. vm_refl. Qed.
Lemma D_135f0 : decode_any W_135f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135f4 : bv 32 := 0x00813023.
Lemma F_135f4 : fetch_word Plain.M.loaded_segments (0x136f0 : word) = Some W_135f4.
Proof. vm_refl. Qed.
Lemma D_135f4 : decode_any W_135f4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135f8 : bv 32 := 0x00060413.
Lemma F_135f8 : fetch_word Plain.M.loaded_segments (0x136f4 : word) = Some W_135f8.
Proof. vm_refl. Qed.
Lemma D_135f8 : decode_any W_135f8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_135fc : bv 32 := 0x00050613.
Lemma F_135fc : fetch_word Plain.M.loaded_segments (0x136f8 : word) = Some W_135fc.
Proof. vm_refl. Qed.
Lemma D_135fc : decode_any W_135fc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13600 : bv 32 := 0xffffd517.
Lemma F_13600 : fetch_word Plain.M.loaded_segments (0x136fc : word) = Some W_13600.
Proof. vm_refl. Qed.
Lemma D_13600 : decode_any W_13600 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13604 : bv 32 := 0x2de50513.
Lemma F_13604 : fetch_word Plain.M.loaded_segments (0x13700 : word) = Some W_13604.
Proof. vm_refl. Qed.
Lemma D_13604 : decode_any W_13604 = Some (OpImm ALU_ADD 10 10 734, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13608 : bv 32 := 0x018000ef.
Lemma F_13608 : fetch_word Plain.M.loaded_segments (0x13704 : word) = Some W_13608.
Proof. vm_refl. Qed.
Lemma D_13608 : decode_any W_13608 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1360c : bv 32 := 0x00040513.
Lemma F_1360c : fetch_word Plain.M.loaded_segments (0x13708 : word) = Some W_1360c.
Proof. vm_refl. Qed.
Lemma D_1360c : decode_any W_1360c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13610 : bv 32 := 0x00813083.
Lemma F_13610 : fetch_word Plain.M.loaded_segments (0x1370c : word) = Some W_13610.
Proof. vm_refl. Qed.
Lemma D_13610 : decode_any W_13610 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13614 : bv 32 := 0x00013403.
Lemma F_13614 : fetch_word Plain.M.loaded_segments (0x13710 : word) = Some W_13614.
Proof. vm_refl. Qed.
Lemma D_13614 : decode_any W_13614 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13618 : bv 32 := 0x01010113.
Lemma F_13618 : fetch_word Plain.M.loaded_segments (0x13714 : word) = Some W_13618.
Proof. vm_refl. Qed.
Lemma D_13618 : decode_any W_13618 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1361c : bv 32 := 0x00008067.
Lemma F_1361c : fetch_word Plain.M.loaded_segments (0x13718 : word) = Some W_1361c.
Proof. vm_refl. Qed.
Lemma D_1361c : decode_any W_1361c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136bc : bv 32 := 0xff010113.
Lemma F_136bc : fetch_word Plain.M.loaded_segments (0x137b8 : word) = Some W_136bc.
Proof. vm_refl. Qed.
Lemma D_136bc : decode_any W_136bc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136c0 : bv 32 := 0x00113423.
Lemma F_136c0 : fetch_word Plain.M.loaded_segments (0x137bc : word) = Some W_136c0.
Proof. vm_refl. Qed.
Lemma D_136c0 : decode_any W_136c0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136c4 : bv 32 := 0x00813023.
Lemma F_136c4 : fetch_word Plain.M.loaded_segments (0x137c0 : word) = Some W_136c4.
Proof. vm_refl. Qed.
Lemma D_136c4 : decode_any W_136c4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136c8 : bv 32 := 0x00060413.
Lemma F_136c8 : fetch_word Plain.M.loaded_segments (0x137c4 : word) = Some W_136c8.
Proof. vm_refl. Qed.
Lemma D_136c8 : decode_any W_136c8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136cc : bv 32 := 0x00050613.
Lemma F_136cc : fetch_word Plain.M.loaded_segments (0x137c8 : word) = Some W_136cc.
Proof. vm_refl. Qed.
Lemma D_136cc : decode_any W_136cc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136d0 : bv 32 := 0xffffd517.
Lemma F_136d0 : fetch_word Plain.M.loaded_segments (0x137cc : word) = Some W_136d0.
Proof. vm_refl. Qed.
Lemma D_136d0 : decode_any W_136d0 = Some (Auipc 10 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136d4 : bv 32 := 0x20e50513.
Lemma F_136d4 : fetch_word Plain.M.loaded_segments (0x137d0 : word) = Some W_136d4.
Proof. vm_refl. Qed.
Lemma D_136d4 : decode_any W_136d4 = Some (OpImm ALU_ADD 10 10 526, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136d8 : bv 32 := 0xf49ff0ef.
Lemma F_136d8 : fetch_word Plain.M.loaded_segments (0x137d4 : word) = Some W_136d8.
Proof. vm_refl. Qed.
Lemma D_136d8 : decode_any W_136d8 = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136dc : bv 32 := 0x00040513.
Lemma F_136dc : fetch_word Plain.M.loaded_segments (0x137d8 : word) = Some W_136dc.
Proof. vm_refl. Qed.
Lemma D_136dc : decode_any W_136dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136e0 : bv 32 := 0x00813083.
Lemma F_136e0 : fetch_word Plain.M.loaded_segments (0x137dc : word) = Some W_136e0.
Proof. vm_refl. Qed.
Lemma D_136e0 : decode_any W_136e0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136e4 : bv 32 := 0x00013403.
Lemma F_136e4 : fetch_word Plain.M.loaded_segments (0x137e0 : word) = Some W_136e4.
Proof. vm_refl. Qed.
Lemma D_136e4 : decode_any W_136e4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136e8 : bv 32 := 0x01010113.
Lemma F_136e8 : fetch_word Plain.M.loaded_segments (0x137e4 : word) = Some W_136e8.
Proof. vm_refl. Qed.
Lemma D_136e8 : decode_any W_136e8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_136ec : bv 32 := 0x00008067.
Lemma F_136ec : fetch_word Plain.M.loaded_segments (0x137e8 : word) = Some W_136ec.
Proof. vm_refl. Qed.
Lemma D_136ec : decode_any W_136ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13708 : bv 32 := 0x00051663.
Lemma F_13708 : fetch_word Plain.M.loaded_segments (0x13804 : word) = Some W_13708.
Proof. vm_refl. Qed.
Lemma D_13708 : decode_any W_13708 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13714 : bv 32 := 0x0000c597.
Lemma F_13714 : fetch_word Plain.M.loaded_segments (0x13810 : word) = Some W_13714.
Proof. vm_refl. Qed.
Lemma D_13714 : decode_any W_13714 = Some (Auipc 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13718 : bv 32 := 0xfea5b423.
Lemma F_13718 : fetch_word Plain.M.loaded_segments (0x13814 : word) = Some W_13718.
Proof. vm_refl. Qed.
Lemma D_13718 : decode_any W_13718 = Some (Store SZ8 11 10 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1371c : bv 32 := 0x00008067.
Lemma F_1371c : fetch_word Plain.M.loaded_segments (0x13818 : word) = Some W_1371c.
Proof. vm_refl. Qed.
Lemma D_1371c : decode_any W_1371c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f54 : bv 32 := 0x00050a63.
Lemma F_13f54 : fetch_word Plain.M.loaded_segments (0x14050 : word) = Some W_13f54.
Proof. vm_refl. Qed.
Lemma D_13f54 : decode_any W_13f54 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f58 : bv 32 := 0x00050613.
Lemma F_13f58 : fetch_word Plain.M.loaded_segments (0x14054 : word) = Some W_13f58.
Proof. vm_refl. Qed.
Lemma D_13f58 : decode_any W_13f58 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f5c : bv 32 := 0x00000513.
Lemma F_13f5c : fetch_word Plain.M.loaded_segments (0x14058 : word) = Some W_13f5c.
Proof. vm_refl. Qed.
Lemma D_13f5c : decode_any W_13f5c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f60 : bv 32 := 0x02b62223.
Lemma F_13f60 : fetch_word Plain.M.loaded_segments (0x1405c : word) = Some W_13f60.
Proof. vm_refl. Qed.
Lemma D_13f60 : decode_any W_13f60 = Some (Store SZ4 12 11 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13f64 : bv 32 := 0x00008067.
Lemma F_13f64 : fetch_word Plain.M.loaded_segments (0x14060 : word) = Some W_13f64.
Proof. vm_refl. Qed.
Lemma D_13f64 : decode_any W_13f64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
