(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a9614 : bv 32 := 0x00008067.
Lemma F_a9614 : fetch_word Ubsan.M.loaded_segments (0xacfa8 : word) = Some W_a9614.
Proof. vm_refl. Qed.
Lemma D_a9614 : decode_any W_a9614 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9618 : bv 32 := 0xe8010113.
Lemma F_a9618 : fetch_word Ubsan.M.loaded_segments (0xacfac : word) = Some W_a9618.
Proof. vm_refl. Qed.
Lemma D_a9618 : decode_any W_a9618 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a961c : bv 32 := 0x16113c23.
Lemma F_a961c : fetch_word Ubsan.M.loaded_segments (0xacfb0 : word) = Some W_a961c.
Proof. vm_refl. Qed.
Lemma D_a961c : decode_any W_a961c = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9620 : bv 32 := 0x16813823.
Lemma F_a9620 : fetch_word Ubsan.M.loaded_segments (0xacfb4 : word) = Some W_a9620.
Proof. vm_refl. Qed.
Lemma D_a9620 : decode_any W_a9620 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9624 : bv 32 := 0x16913423.
Lemma F_a9624 : fetch_word Ubsan.M.loaded_segments (0xacfb8 : word) = Some W_a9624.
Proof. vm_refl. Qed.
Lemma D_a9624 : decode_any W_a9624 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9628 : bv 32 := 0x17213023.
Lemma F_a9628 : fetch_word Ubsan.M.loaded_segments (0xacfbc : word) = Some W_a9628.
Proof. vm_refl. Qed.
Lemma D_a9628 : decode_any W_a9628 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a962c : bv 32 := 0x00058413.
Lemma F_a962c : fetch_word Ubsan.M.loaded_segments (0xacfc0 : word) = Some W_a962c.
Proof. vm_refl. Qed.
Lemma D_a962c : decode_any W_a962c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9630 : bv 32 := 0x00050493.
Lemma F_a9630 : fetch_word Ubsan.M.loaded_segments (0xacfc4 : word) = Some W_a9630.
Proof. vm_refl. Qed.
Lemma D_a9630 : decode_any W_a9630 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9634 : bv 32 := 0x03010513.
Lemma F_a9634 : fetch_word Ubsan.M.loaded_segments (0xacfc8 : word) = Some W_a9634.
Proof. vm_refl. Qed.
Lemma D_a9634 : decode_any W_a9634 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9638 : bv 32 := 0x13000613.
Lemma F_a9638 : fetch_word Ubsan.M.loaded_segments (0xacfcc : word) = Some W_a9638.
Proof. vm_refl. Qed.
Lemma D_a9638 : decode_any W_a9638 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a963c : bv 32 := 0x00000593.
Lemma F_a963c : fetch_word Ubsan.M.loaded_segments (0xacfd0 : word) = Some W_a963c.
Proof. vm_refl. Qed.
Lemma D_a963c : decode_any W_a963c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9640 : bv 32 := 0x5f4110ef.
Lemma F_a9640 : fetch_word Ubsan.M.loaded_segments (0xacfd4 : word) = Some W_a9640.
Proof. vm_refl. Qed.
Lemma D_a9640 : decode_any W_a9640 = Some (Jal 1 71156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9644 : bv 32 := 0x0001d517.
Lemma F_a9644 : fetch_word Ubsan.M.loaded_segments (0xacfd8 : word) = Some W_a9644.
Proof. vm_refl. Qed.
Lemma D_a9644 : decode_any W_a9644 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9648 : bv 32 := 0x22053503.
Lemma F_a9648 : fetch_word Ubsan.M.loaded_segments (0xacfdc : word) = Some W_a9648.
Proof. vm_refl. Qed.
Lemma D_a9648 : decode_any W_a9648 = Some (Load SZ8 true 10 10 544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a964c : bv 32 := 0x00953023.
Lemma F_a964c : fetch_word Ubsan.M.loaded_segments (0xacfe0 : word) = Some W_a964c.
Proof. vm_refl. Qed.
Lemma D_a964c : decode_any W_a964c = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9650 : bv 32 := 0x0004b503.
Lemma F_a9650 : fetch_word Ubsan.M.loaded_segments (0xacfe4 : word) = Some W_a9650.
Proof. vm_refl. Qed.
Lemma D_a9650 : decode_any W_a9650 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9654 : bv 32 := 0x00848493.
Lemma F_a9654 : fetch_word Ubsan.M.loaded_segments (0xacfe8 : word) = Some W_a9654.
Proof. vm_refl. Qed.
Lemma D_a9654 : decode_any W_a9654 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9658 : bv 32 := 0xfe051ce3.
Lemma F_a9658 : fetch_word Ubsan.M.loaded_segments (0xacfec : word) = Some W_a9658.
Proof. vm_refl. Qed.
Lemma D_a9658 : decode_any W_a9658 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a965c : bv 32 := 0x00050517.
Lemma F_a965c : fetch_word Ubsan.M.loaded_segments (0xacff0 : word) = Some W_a965c.
Proof. vm_refl. Qed.
Lemma D_a965c : decode_any W_a965c = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9660 : bv 32 := 0x2b050913.
Lemma F_a9660 : fetch_word Ubsan.M.loaded_segments (0xacff4 : word) = Some W_a9660.
Proof. vm_refl. Qed.
Lemma D_a9660 : decode_any W_a9660 = Some (OpImm ALU_ADD 18 10 688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9664 : bv 32 := 0x00993423.
Lemma F_a9664 : fetch_word Ubsan.M.loaded_segments (0xacff8 : word) = Some W_a9664.
Proof. vm_refl. Qed.
Lemma D_a9664 : decode_any W_a9664 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9668 : bv 32 := 0x0004b583.
Lemma F_a9668 : fetch_word Ubsan.M.loaded_segments (0xacffc : word) = Some W_a9668.
Proof. vm_refl. Qed.
Lemma D_a9668 : decode_any W_a9668 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a966c : bv 32 := 0x04058c63.
Lemma F_a966c : fetch_word Ubsan.M.loaded_segments (0xad000 : word) = Some W_a966c.
Proof. vm_refl. Qed.
Lemma D_a966c : decode_any W_a966c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9670 : bv 32 := 0x01048493.
Lemma F_a9670 : fetch_word Ubsan.M.loaded_segments (0xad004 : word) = Some W_a9670.
Proof. vm_refl. Qed.
Lemma D_a9670 : decode_any W_a9670 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9674 : bv 32 := 0x02500513.
Lemma F_a9674 : fetch_word Ubsan.M.loaded_segments (0xad008 : word) = Some W_a9674.
Proof. vm_refl. Qed.
Lemma D_a9674 : decode_any W_a9674 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9678 : bv 32 := 0x03010613.
Lemma F_a9678 : fetch_word Ubsan.M.loaded_segments (0xad00c : word) = Some W_a9678.
Proof. vm_refl. Qed.
Lemma D_a9678 : decode_any W_a9678 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a967c : bv 32 := 0x0100006f.
Lemma F_a967c : fetch_word Ubsan.M.loaded_segments (0xad010 : word) = Some W_a967c.
Proof. vm_refl. Qed.
Lemma D_a967c : decode_any W_a967c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9680 : bv 32 := 0x0004b583.
Lemma F_a9680 : fetch_word Ubsan.M.loaded_segments (0xad014 : word) = Some W_a9680.
Proof. vm_refl. Qed.
Lemma D_a9680 : decode_any W_a9680 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9684 : bv 32 := 0x01048493.
Lemma F_a9684 : fetch_word Ubsan.M.loaded_segments (0xad018 : word) = Some W_a9684.
Proof. vm_refl. Qed.
Lemma D_a9684 : decode_any W_a9684 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9688 : bv 32 := 0x00058e63.
Lemma F_a9688 : fetch_word Ubsan.M.loaded_segments (0xad01c : word) = Some W_a9688.
Proof. vm_refl. Qed.
Lemma D_a9688 : decode_any W_a9688 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a968c : bv 32 := 0xfeb56ae3.
Lemma F_a968c : fetch_word Ubsan.M.loaded_segments (0xad020 : word) = Some W_a968c.
Proof. vm_refl. Qed.
Lemma D_a968c : decode_any W_a968c = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9690 : bv 32 := 0xff84b683.
Lemma F_a9690 : fetch_word Ubsan.M.loaded_segments (0xad024 : word) = Some W_a9690.
Proof. vm_refl. Qed.
Lemma D_a9690 : decode_any W_a9690 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9694 : bv 32 := 0x00359593.
Lemma F_a9694 : fetch_word Ubsan.M.loaded_segments (0xad028 : word) = Some W_a9694.
Proof. vm_refl. Qed.
Lemma D_a9694 : decode_any W_a9694 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9698 : bv 32 := 0x00b605b3.
Lemma F_a9698 : fetch_word Ubsan.M.loaded_segments (0xad02c : word) = Some W_a9698.
Proof. vm_refl. Qed.
Lemma D_a9698 : decode_any W_a9698 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a969c : bv 32 := 0x00d5b023.
Lemma F_a969c : fetch_word Ubsan.M.loaded_segments (0xad030 : word) = Some W_a969c.
Proof. vm_refl. Qed.
Lemma D_a969c : decode_any W_a969c = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96a0 : bv 32 := 0xfe1ff06f.
Lemma F_a96a0 : fetch_word Ubsan.M.loaded_segments (0xad034 : word) = Some W_a96a0.
Proof. vm_refl. Qed.
Lemma D_a96a0 : decode_any W_a96a0 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96a4 : bv 32 := 0x0b013583.
Lemma F_a96a4 : fetch_word Ubsan.M.loaded_segments (0xad038 : word) = Some W_a96a4.
Proof. vm_refl. Qed.
Lemma D_a96a4 : decode_any W_a96a4 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96a8 : bv 32 := 0x13013503.
Lemma F_a96a8 : fetch_word Ubsan.M.loaded_segments (0xad03c : word) = Some W_a96a8.
Proof. vm_refl. Qed.
Lemma D_a96a8 : decode_any W_a96a8 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96ac : bv 32 := 0x00050617.
Lemma F_a96ac : fetch_word Ubsan.M.loaded_segments (0xad040 : word) = Some W_a96ac.
Proof. vm_refl. Qed.
Lemma D_a96ac : decode_any W_a96ac = Some (Auipc 12 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96b0 : bv 32 := 0x2cb63423.
Lemma F_a96b0 : fetch_word Ubsan.M.loaded_segments (0xad044 : word) = Some W_a96b0.
Proof. vm_refl. Qed.
Lemma D_a96b0 : decode_any W_a96b0 = Some (Store SZ8 12 11 712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96b4 : bv 32 := 0x00050c63.
Lemma F_a96b4 : fetch_word Ubsan.M.loaded_segments (0xad048 : word) = Some W_a96b4.
Proof. vm_refl. Qed.
Lemma D_a96b4 : decode_any W_a96b4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96cc : bv 32 := 0x06013503.
Lemma F_a96cc : fetch_word Ubsan.M.loaded_segments (0xad060 : word) = Some W_a96cc.
Proof. vm_refl. Qed.
Lemma D_a96cc : decode_any W_a96cc = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96d0 : bv 32 := 0x02a93823.
Lemma F_a96d0 : fetch_word Ubsan.M.loaded_segments (0xad064 : word) = Some W_a96d0.
Proof. vm_refl. Qed.
Lemma D_a96d0 : decode_any W_a96d0 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96d4 : bv 32 := 0x00041463.
Lemma F_a96d4 : fetch_word Ubsan.M.loaded_segments (0xad068 : word) = Some W_a96d4.
Proof. vm_refl. Qed.
Lemma D_a96d4 : decode_any W_a96d4 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96dc : bv 32 := 0x00041663.
Lemma F_a96dc : fetch_word Ubsan.M.loaded_segments (0xad070 : word) = Some W_a96dc.
Proof. vm_refl. Qed.
Lemma D_a96dc : decode_any W_a96dc = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96e8 : bv 32 := 0x0001d517.
Lemma F_a96e8 : fetch_word Ubsan.M.loaded_segments (0xad07c : word) = Some W_a96e8.
Proof. vm_refl. Qed.
Lemma D_a96e8 : decode_any W_a96e8 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96ec : bv 32 := 0x18453583.
Lemma F_a96ec : fetch_word Ubsan.M.loaded_segments (0xad080 : word) = Some W_a96ec.
Proof. vm_refl. Qed.
Lemma D_a96ec : decode_any W_a96ec = Some (Load SZ8 true 11 10 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96f0 : bv 32 := 0x0001d517.
Lemma F_a96f0 : fetch_word Ubsan.M.loaded_segments (0xad084 : word) = Some W_a96f0.
Proof. vm_refl. Qed.
Lemma D_a96f0 : decode_any W_a96f0 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96f4 : bv 32 := 0x18453503.
Lemma F_a96f4 : fetch_word Ubsan.M.loaded_segments (0xad088 : word) = Some W_a96f4.
Proof. vm_refl. Qed.
Lemma D_a96f4 : decode_any W_a96f4 = Some (Load SZ8 true 10 10 388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96f8 : bv 32 := 0x0085b023.
Lemma F_a96f8 : fetch_word Ubsan.M.loaded_segments (0xad08c : word) = Some W_a96f8.
Proof. vm_refl. Qed.
Lemma D_a96f8 : decode_any W_a96f8 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a96fc : bv 32 := 0x00140593.
Lemma F_a96fc : fetch_word Ubsan.M.loaded_segments (0xad090 : word) = Some W_a96fc.
Proof. vm_refl. Qed.
Lemma D_a96fc : decode_any W_a96fc = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9700 : bv 32 := 0x00853023.
Lemma F_a9700 : fetch_word Ubsan.M.loaded_segments (0xad094 : word) = Some W_a9700.
Proof. vm_refl. Qed.
Lemma D_a9700 : decode_any W_a9700 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9704 : bv 32 := 0x02f00613.
Lemma F_a9704 : fetch_word Ubsan.M.loaded_segments (0xad098 : word) = Some W_a9704.
Proof. vm_refl. Qed.
Lemma D_a9704 : decode_any W_a9704 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9708 : bv 32 := 0x00c0006f.
Lemma F_a9708 : fetch_word Ubsan.M.loaded_segments (0xad09c : word) = Some W_a9708.
Proof. vm_refl. Qed.
Lemma D_a9708 : decode_any W_a9708 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a970c : bv 32 := 0x00b53023.
Lemma F_a970c : fetch_word Ubsan.M.loaded_segments (0xad0a0 : word) = Some W_a970c.
Proof. vm_refl. Qed.
Lemma D_a970c : decode_any W_a970c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9710 : bv 32 := 0x00158593.
Lemma F_a9710 : fetch_word Ubsan.M.loaded_segments (0xad0a4 : word) = Some W_a9710.
Proof. vm_refl. Qed.
Lemma D_a9710 : decode_any W_a9710 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9714 : bv 32 := 0xfff5c683.
Lemma F_a9714 : fetch_word Ubsan.M.loaded_segments (0xad0a8 : word) = Some W_a9714.
Proof. vm_refl. Qed.
Lemma D_a9714 : decode_any W_a9714 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9718 : bv 32 := 0xfec68ae3.
Lemma F_a9718 : fetch_word Ubsan.M.loaded_segments (0xad0ac : word) = Some W_a9718.
Proof. vm_refl. Qed.
Lemma D_a9718 : decode_any W_a9718 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a971c : bv 32 := 0xfe069ae3.
Lemma F_a971c : fetch_word Ubsan.M.loaded_segments (0xad0b0 : word) = Some W_a971c.
Proof. vm_refl. Qed.
Lemma D_a971c : decode_any W_a971c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9720 : bv 32 := 0x03010513.
Lemma F_a9720 : fetch_word Ubsan.M.loaded_segments (0xad0b4 : word) = Some W_a9720.
Proof. vm_refl. Qed.
Lemma D_a9720 : decode_any W_a9720 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9724 : bv 32 := 0x214000ef.
Lemma F_a9724 : fetch_word Ubsan.M.loaded_segments (0xad0b8 : word) = Some W_a9724.
Proof. vm_refl. Qed.
Lemma D_a9724 : decode_any W_a9724 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9728 : bv 32 := 0x0f813503.
Lemma F_a9728 : fetch_word Ubsan.M.loaded_segments (0xad0bc : word) = Some W_a9728.
Proof. vm_refl. Qed.
Lemma D_a9728 : decode_any W_a9728 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a972c : bv 32 := 0x1ad000ef.
Lemma F_a972c : fetch_word Ubsan.M.loaded_segments (0xad0c0 : word) = Some W_a972c.
Proof. vm_refl. Qed.
Lemma D_a972c : decode_any W_a972c = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9730 : bv 32 := 0x08813503.
Lemma F_a9730 : fetch_word Ubsan.M.loaded_segments (0xad0c4 : word) = Some W_a9730.
Proof. vm_refl. Qed.
Lemma D_a9730 : decode_any W_a9730 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9734 : bv 32 := 0x09013583.
Lemma F_a9734 : fetch_word Ubsan.M.loaded_segments (0xad0c8 : word) = Some W_a9734.
Proof. vm_refl. Qed.
Lemma D_a9734 : decode_any W_a9734 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9738 : bv 32 := 0x00b51c63.
Lemma F_a9738 : fetch_word Ubsan.M.loaded_segments (0xad0cc : word) = Some W_a9738.
Proof. vm_refl. Qed.
Lemma D_a9738 : decode_any W_a9738 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a973c : bv 32 := 0x09813503.
Lemma F_a973c : fetch_word Ubsan.M.loaded_segments (0xad0d0 : word) = Some W_a973c.
Proof. vm_refl. Qed.
Lemma D_a973c : decode_any W_a973c = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9740 : bv 32 := 0x0a013583.
Lemma F_a9740 : fetch_word Ubsan.M.loaded_segments (0xad0d4 : word) = Some W_a9740.
Proof. vm_refl. Qed.
Lemma D_a9740 : decode_any W_a9740 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9744 : bv 32 := 0x00b51663.
Lemma F_a9744 : fetch_word Ubsan.M.loaded_segments (0xad0d8 : word) = Some W_a9744.
Proof. vm_refl. Qed.
Lemma D_a9744 : decode_any W_a9744 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9748 : bv 32 := 0x0e813503.
Lemma F_a9748 : fetch_word Ubsan.M.loaded_segments (0xad0dc : word) = Some W_a9748.
Proof. vm_refl. Qed.
Lemma D_a9748 : decode_any W_a9748 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a974c : bv 32 := 0x0e050063.
Lemma F_a974c : fetch_word Ubsan.M.loaded_segments (0xad0e0 : word) = Some W_a974c.
Proof. vm_refl. Qed.
Lemma D_a974c : decode_any W_a974c = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a982c : bv 32 := 0x17813083.
Lemma F_a982c : fetch_word Ubsan.M.loaded_segments (0xad1c0 : word) = Some W_a982c.
Proof. vm_refl. Qed.
Lemma D_a982c : decode_any W_a982c = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9830 : bv 32 := 0x17013403.
Lemma F_a9830 : fetch_word Ubsan.M.loaded_segments (0xad1c4 : word) = Some W_a9830.
Proof. vm_refl. Qed.
Lemma D_a9830 : decode_any W_a9830 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9834 : bv 32 := 0x16813483.
Lemma F_a9834 : fetch_word Ubsan.M.loaded_segments (0xad1c8 : word) = Some W_a9834.
Proof. vm_refl. Qed.
Lemma D_a9834 : decode_any W_a9834 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9838 : bv 32 := 0x16013903.
Lemma F_a9838 : fetch_word Ubsan.M.loaded_segments (0xad1cc : word) = Some W_a9838.
Proof. vm_refl. Qed.
Lemma D_a9838 : decode_any W_a9838 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a983c : bv 32 := 0x18010113.
Lemma F_a983c : fetch_word Ubsan.M.loaded_segments (0xad1d0 : word) = Some W_a983c.
Proof. vm_refl. Qed.
Lemma D_a983c : decode_any W_a983c = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9840 : bv 32 := 0x00008067.
Lemma F_a9840 : fetch_word Ubsan.M.loaded_segments (0xad1d4 : word) = Some W_a9840.
Proof. vm_refl. Qed.
Lemma D_a9840 : decode_any W_a9840 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9844 : bv 32 := 0xfe010113.
Lemma F_a9844 : fetch_word Ubsan.M.loaded_segments (0xad1d8 : word) = Some W_a9844.
Proof. vm_refl. Qed.
Lemma D_a9844 : decode_any W_a9844 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9848 : bv 32 := 0x00113c23.
Lemma F_a9848 : fetch_word Ubsan.M.loaded_segments (0xad1dc : word) = Some W_a9848.
Proof. vm_refl. Qed.
Lemma D_a9848 : decode_any W_a9848 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a984c : bv 32 := 0x00813823.
Lemma F_a984c : fetch_word Ubsan.M.loaded_segments (0xad1e0 : word) = Some W_a984c.
Proof. vm_refl. Qed.
Lemma D_a984c : decode_any W_a984c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9850 : bv 32 := 0x00913423.
Lemma F_a9850 : fetch_word Ubsan.M.loaded_segments (0xad1e4 : word) = Some W_a9850.
Proof. vm_refl. Qed.
Lemma D_a9850 : decode_any W_a9850 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9854 : bv 32 := 0xdc1ff0ef.
Lemma F_a9854 : fetch_word Ubsan.M.loaded_segments (0xad1e8 : word) = Some W_a9854.
Proof. vm_refl. Qed.
Lemma D_a9854 : decode_any W_a9854 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9858 : bv 32 := 0x0001d517.
Lemma F_a9858 : fetch_word Ubsan.M.loaded_segments (0xad1ec : word) = Some W_a9858.
Proof. vm_refl. Qed.
Lemma D_a9858 : decode_any W_a9858 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a985c : bv 32 := 0x0001d597.
Lemma F_a985c : fetch_word Ubsan.M.loaded_segments (0xad1f0 : word) = Some W_a985c.
Proof. vm_refl. Qed.
Lemma D_a985c : decode_any W_a985c = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9860 : bv 32 := 0x02453403.
Lemma F_a9860 : fetch_word Ubsan.M.loaded_segments (0xad1f4 : word) = Some W_a9860.
Proof. vm_refl. Qed.
Lemma D_a9860 : decode_any W_a9860 = Some (Load SZ8 true 8 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9864 : bv 32 := 0x0285b483.
Lemma F_a9864 : fetch_word Ubsan.M.loaded_segments (0xad1f8 : word) = Some W_a9864.
Proof. vm_refl. Qed.
Lemma D_a9864 : decode_any W_a9864 = Some (Load SZ8 true 9 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9868 : bv 32 := 0x0084fa63.
Lemma F_a9868 : fetch_word Ubsan.M.loaded_segments (0xad1fc : word) = Some W_a9868.
Proof. vm_refl. Qed.
Lemma D_a9868 : decode_any W_a9868 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a986c : bv 32 := 0x0004b503.
Lemma F_a986c : fetch_word Ubsan.M.loaded_segments (0xad200 : word) = Some W_a986c.
Proof. vm_refl. Qed.
Lemma D_a986c : decode_any W_a986c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9870 : bv 32 := 0x000500e7.
Lemma F_a9870 : fetch_word Ubsan.M.loaded_segments (0xad204 : word) = Some W_a9870.
Proof. vm_refl. Qed.
Lemma D_a9870 : decode_any W_a9870 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9874 : bv 32 := 0x00848493.
Lemma F_a9874 : fetch_word Ubsan.M.loaded_segments (0xad208 : word) = Some W_a9874.
Proof. vm_refl. Qed.
Lemma D_a9874 : decode_any W_a9874 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9878 : bv 32 := 0xfe84eae3.
Lemma F_a9878 : fetch_word Ubsan.M.loaded_segments (0xad20c : word) = Some W_a9878.
Proof. vm_refl. Qed.
Lemma D_a9878 : decode_any W_a9878 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a987c : bv 32 := 0x01813083.
Lemma F_a987c : fetch_word Ubsan.M.loaded_segments (0xad210 : word) = Some W_a987c.
Proof. vm_refl. Qed.
Lemma D_a987c : decode_any W_a987c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9880 : bv 32 := 0x01013403.
Lemma F_a9880 : fetch_word Ubsan.M.loaded_segments (0xad214 : word) = Some W_a9880.
Proof. vm_refl. Qed.
Lemma D_a9880 : decode_any W_a9880 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9884 : bv 32 := 0x00813483.
Lemma F_a9884 : fetch_word Ubsan.M.loaded_segments (0xad218 : word) = Some W_a9884.
Proof. vm_refl. Qed.
Lemma D_a9884 : decode_any W_a9884 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9888 : bv 32 := 0x02010113.
Lemma F_a9888 : fetch_word Ubsan.M.loaded_segments (0xad21c : word) = Some W_a9888.
Proof. vm_refl. Qed.
Lemma D_a9888 : decode_any W_a9888 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a988c : bv 32 := 0x00008067.
Lemma F_a988c : fetch_word Ubsan.M.loaded_segments (0xad220 : word) = Some W_a988c.
Proof. vm_refl. Qed.
Lemma D_a988c : decode_any W_a988c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9890 : bv 32 := 0xfe010113.
Lemma F_a9890 : fetch_word Ubsan.M.loaded_segments (0xad224 : word) = Some W_a9890.
Proof. vm_refl. Qed.
Lemma D_a9890 : decode_any W_a9890 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9894 : bv 32 := 0x00113c23.
Lemma F_a9894 : fetch_word Ubsan.M.loaded_segments (0xad228 : word) = Some W_a9894.
Proof. vm_refl. Qed.
Lemma D_a9894 : decode_any W_a9894 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9898 : bv 32 := 0x00813823.
Lemma F_a9898 : fetch_word Ubsan.M.loaded_segments (0xad22c : word) = Some W_a9898.
Proof. vm_refl. Qed.
Lemma D_a9898 : decode_any W_a9898 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a989c : bv 32 := 0x00913423.
Lemma F_a989c : fetch_word Ubsan.M.loaded_segments (0xad230 : word) = Some W_a989c.
Proof. vm_refl. Qed.
Lemma D_a989c : decode_any W_a989c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98a0 : bv 32 := 0x01213023.
Lemma F_a98a0 : fetch_word Ubsan.M.loaded_segments (0xad234 : word) = Some W_a98a0.
Proof. vm_refl. Qed.
Lemma D_a98a0 : decode_any W_a98a0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98a4 : bv 32 := 0x00060413.
Lemma F_a98a4 : fetch_word Ubsan.M.loaded_segments (0xad238 : word) = Some W_a98a4.
Proof. vm_refl. Qed.
Lemma D_a98a4 : decode_any W_a98a4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98a8 : bv 32 := 0x00058493.
Lemma F_a98a8 : fetch_word Ubsan.M.loaded_segments (0xad23c : word) = Some W_a98a8.
Proof. vm_refl. Qed.
Lemma D_a98a8 : decode_any W_a98a8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98ac : bv 32 := 0x00050913.
Lemma F_a98ac : fetch_word Ubsan.M.loaded_segments (0xad240 : word) = Some W_a98ac.
Proof. vm_refl. Qed.
Lemma D_a98ac : decode_any W_a98ac = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98b0 : bv 32 := 0x00063583.
Lemma F_a98b0 : fetch_word Ubsan.M.loaded_segments (0xad244 : word) = Some W_a98b0.
Proof. vm_refl. Qed.
Lemma D_a98b0 : decode_any W_a98b0 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98b4 : bv 32 := 0x00349513.
Lemma F_a98b4 : fetch_word Ubsan.M.loaded_segments (0xad248 : word) = Some W_a98b4.
Proof. vm_refl. Qed.
Lemma D_a98b4 : decode_any W_a98b4 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98b8 : bv 32 := 0x00a60533.
Lemma F_a98b8 : fetch_word Ubsan.M.loaded_segments (0xad24c : word) = Some W_a98b8.
Proof. vm_refl. Qed.
Lemma D_a98b8 : decode_any W_a98b8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98bc : bv 32 := 0x00850513.
Lemma F_a98bc : fetch_word Ubsan.M.loaded_segments (0xad250 : word) = Some W_a98bc.
Proof. vm_refl. Qed.
Lemma D_a98bc : decode_any W_a98bc = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98c0 : bv 32 := 0xd59ff0ef.
Lemma F_a98c0 : fetch_word Ubsan.M.loaded_segments (0xad254 : word) = Some W_a98c0.
Proof. vm_refl. Qed.
Lemma D_a98c0 : decode_any W_a98c0 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98c4 : bv 32 := 0x00000517.
Lemma F_a98c4 : fetch_word Ubsan.M.loaded_segments (0xad258 : word) = Some W_a98c4.
Proof. vm_refl. Qed.
Lemma D_a98c4 : decode_any W_a98c4 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98c8 : bv 32 := 0x02c50313.
Lemma F_a98c8 : fetch_word Ubsan.M.loaded_segments (0xad25c : word) = Some W_a98c8.
Proof. vm_refl. Qed.
Lemma D_a98c8 : decode_any W_a98c8 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98cc : bv 32 := 0x00090513.
Lemma F_a98cc : fetch_word Ubsan.M.loaded_segments (0xad260 : word) = Some W_a98cc.
Proof. vm_refl. Qed.
Lemma D_a98cc : decode_any W_a98cc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98d0 : bv 32 := 0x00048593.
Lemma F_a98d0 : fetch_word Ubsan.M.loaded_segments (0xad264 : word) = Some W_a98d0.
Proof. vm_refl. Qed.
Lemma D_a98d0 : decode_any W_a98d0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98d4 : bv 32 := 0x00040613.
Lemma F_a98d4 : fetch_word Ubsan.M.loaded_segments (0xad268 : word) = Some W_a98d4.
Proof. vm_refl. Qed.
Lemma D_a98d4 : decode_any W_a98d4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98d8 : bv 32 := 0x01813083.
Lemma F_a98d8 : fetch_word Ubsan.M.loaded_segments (0xad26c : word) = Some W_a98d8.
Proof. vm_refl. Qed.
Lemma D_a98d8 : decode_any W_a98d8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98dc : bv 32 := 0x01013403.
Lemma F_a98dc : fetch_word Ubsan.M.loaded_segments (0xad270 : word) = Some W_a98dc.
Proof. vm_refl. Qed.
Lemma D_a98dc : decode_any W_a98dc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98e0 : bv 32 := 0x00813483.
Lemma F_a98e0 : fetch_word Ubsan.M.loaded_segments (0xad274 : word) = Some W_a98e0.
Proof. vm_refl. Qed.
Lemma D_a98e0 : decode_any W_a98e0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98e4 : bv 32 := 0x00013903.
Lemma F_a98e4 : fetch_word Ubsan.M.loaded_segments (0xad278 : word) = Some W_a98e4.
Proof. vm_refl. Qed.
Lemma D_a98e4 : decode_any W_a98e4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98e8 : bv 32 := 0x02010113.
Lemma F_a98e8 : fetch_word Ubsan.M.loaded_segments (0xad27c : word) = Some W_a98e8.
Proof. vm_refl. Qed.
Lemma D_a98e8 : decode_any W_a98e8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98ec : bv 32 := 0x00030067.
Lemma F_a98ec : fetch_word Ubsan.M.loaded_segments (0xad280 : word) = Some W_a98ec.
Proof. vm_refl. Qed.
Lemma D_a98ec : decode_any W_a98ec = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98f0 : bv 32 := 0xfd010113.
Lemma F_a98f0 : fetch_word Ubsan.M.loaded_segments (0xad284 : word) = Some W_a98f0.
Proof. vm_refl. Qed.
Lemma D_a98f0 : decode_any W_a98f0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98f4 : bv 32 := 0x02113423.
Lemma F_a98f4 : fetch_word Ubsan.M.loaded_segments (0xad288 : word) = Some W_a98f4.
Proof. vm_refl. Qed.
Lemma D_a98f4 : decode_any W_a98f4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98f8 : bv 32 := 0x02813023.
Lemma F_a98f8 : fetch_word Ubsan.M.loaded_segments (0xad28c : word) = Some W_a98f8.
Proof. vm_refl. Qed.
Lemma D_a98f8 : decode_any W_a98f8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a98fc : bv 32 := 0x00913c23.
Lemma F_a98fc : fetch_word Ubsan.M.loaded_segments (0xad290 : word) = Some W_a98fc.
Proof. vm_refl. Qed.
Lemma D_a98fc : decode_any W_a98fc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9900 : bv 32 := 0x01213823.
Lemma F_a9900 : fetch_word Ubsan.M.loaded_segments (0xad294 : word) = Some W_a9900.
Proof. vm_refl. Qed.
Lemma D_a9900 : decode_any W_a9900 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9904 : bv 32 := 0x01313423.
Lemma F_a9904 : fetch_word Ubsan.M.loaded_segments (0xad298 : word) = Some W_a9904.
Proof. vm_refl. Qed.
Lemma D_a9904 : decode_any W_a9904 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9908 : bv 32 := 0x00060413.
Lemma F_a9908 : fetch_word Ubsan.M.loaded_segments (0xad29c : word) = Some W_a9908.
Proof. vm_refl. Qed.
Lemma D_a9908 : decode_any W_a9908 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a990c : bv 32 := 0x00058493.
Lemma F_a990c : fetch_word Ubsan.M.loaded_segments (0xad2a0 : word) = Some W_a990c.
Proof. vm_refl. Qed.
Lemma D_a990c : decode_any W_a990c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9910 : bv 32 := 0x00050913.
Lemma F_a9910 : fetch_word Ubsan.M.loaded_segments (0xad2a4 : word) = Some W_a9910.
Proof. vm_refl. Qed.
Lemma D_a9910 : decode_any W_a9910 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9914 : bv 32 := 0x00359513.
Lemma F_a9914 : fetch_word Ubsan.M.loaded_segments (0xad2a8 : word) = Some W_a9914.
Proof. vm_refl. Qed.
Lemma D_a9914 : decode_any W_a9914 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9918 : bv 32 := 0x00a60533.
Lemma F_a9918 : fetch_word Ubsan.M.loaded_segments (0xad2ac : word) = Some W_a9918.
Proof. vm_refl. Qed.
Lemma D_a9918 : decode_any W_a9918 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a991c : bv 32 := 0x00850993.
Lemma F_a991c : fetch_word Ubsan.M.loaded_segments (0xad2b0 : word) = Some W_a991c.
Proof. vm_refl. Qed.
Lemma D_a991c : decode_any W_a991c = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9920 : bv 32 := 0xf25ff0ef.
Lemma F_a9920 : fetch_word Ubsan.M.loaded_segments (0xad2b4 : word) = Some W_a9920.
Proof. vm_refl. Qed.
Lemma D_a9920 : decode_any W_a9920 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9924 : bv 32 := 0x00048513.
Lemma F_a9924 : fetch_word Ubsan.M.loaded_segments (0xad2b8 : word) = Some W_a9924.
Proof. vm_refl. Qed.
Lemma D_a9924 : decode_any W_a9924 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9928 : bv 32 := 0x00040593.
Lemma F_a9928 : fetch_word Ubsan.M.loaded_segments (0xad2bc : word) = Some W_a9928.
Proof. vm_refl. Qed.
Lemma D_a9928 : decode_any W_a9928 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a992c : bv 32 := 0x00098613.
Lemma F_a992c : fetch_word Ubsan.M.loaded_segments (0xad2c0 : word) = Some W_a992c.
Proof. vm_refl. Qed.
Lemma D_a992c : decode_any W_a992c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9930 : bv 32 := 0x000900e7.
Lemma F_a9930 : fetch_word Ubsan.M.loaded_segments (0xad2c4 : word) = Some W_a9930.
Proof. vm_refl. Qed.
Lemma D_a9930 : decode_any W_a9930 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_a9c94 : bv 32 := 0x00050593.
Lemma F_a9c94 : fetch_word Ubsan.M.loaded_segments (0xad61c : word) = Some W_a9c94.
Proof. vm_refl. Qed.
Lemma D_a9c94 : decode_any W_a9c94 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9c98 : bv 32 := 0x05e00893.
Lemma F_a9c98 : fetch_word Ubsan.M.loaded_segments (0xad620 : word) = Some W_a9c98.
Proof. vm_refl. Qed.
Lemma D_a9c98 : decode_any W_a9c98 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9c9c : bv 32 := 0x00000073.
Lemma F_a9c9c : fetch_word Ubsan.M.loaded_segments (0xad624 : word) = Some W_a9c9c.
Proof. vm_refl. Qed.
Lemma D_a9c9c : decode_any W_a9c9c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a9c9c : is_ecall W_a9c9c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_a9ce0 : bv 32 := 0xfd010113.
Lemma F_a9ce0 : fetch_word Ubsan.M.loaded_segments (0xad668 : word) = Some W_a9ce0.
Proof. vm_refl. Qed.
Lemma D_a9ce0 : decode_any W_a9ce0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9ce4 : bv 32 := 0x02113423.
Lemma F_a9ce4 : fetch_word Ubsan.M.loaded_segments (0xad66c : word) = Some W_a9ce4.
Proof. vm_refl. Qed.
Lemma D_a9ce4 : decode_any W_a9ce4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9ce8 : bv 32 := 0x02813023.
Lemma F_a9ce8 : fetch_word Ubsan.M.loaded_segments (0xad670 : word) = Some W_a9ce8.
Proof. vm_refl. Qed.
Lemma D_a9ce8 : decode_any W_a9ce8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9cec : bv 32 := 0x00913c23.
Lemma F_a9cec : fetch_word Ubsan.M.loaded_segments (0xad674 : word) = Some W_a9cec.
Proof. vm_refl. Qed.
Lemma D_a9cec : decode_any W_a9cec = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9cf0 : bv 32 := 0x01213823.
Lemma F_a9cf0 : fetch_word Ubsan.M.loaded_segments (0xad678 : word) = Some W_a9cf0.
Proof. vm_refl. Qed.
Lemma D_a9cf0 : decode_any W_a9cf0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9cf4 : bv 32 := 0x01313423.
Lemma F_a9cf4 : fetch_word Ubsan.M.loaded_segments (0xad67c : word) = Some W_a9cf4.
Proof. vm_refl. Qed.
Lemma D_a9cf4 : decode_any W_a9cf4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9cf8 : bv 32 := 0x00050517.
Lemma F_a9cf8 : fetch_word Ubsan.M.loaded_segments (0xad680 : word) = Some W_a9cf8.
Proof. vm_refl. Qed.
Lemma D_a9cf8 : decode_any W_a9cf8 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9cfc : bv 32 := 0x9d850913.
Lemma F_a9cfc : fetch_word Ubsan.M.loaded_segments (0xad684 : word) = Some W_a9cfc.
Proof. vm_refl. Qed.
Lemma D_a9cfc : decode_any W_a9cfc = Some (OpImm ALU_ADD 18 10 2520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d00 : bv 32 := 0x00490413.
Lemma F_a9d00 : fetch_word Ubsan.M.loaded_segments (0xad688 : word) = Some W_a9d00.
Proof. vm_refl. Qed.
Lemma D_a9d00 : decode_any W_a9d00 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d04 : bv 32 := 0x00040513.
Lemma F_a9d04 : fetch_word Ubsan.M.loaded_segments (0xad68c : word) = Some W_a9d04.
Proof. vm_refl. Qed.
Lemma D_a9d04 : decode_any W_a9d04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d08 : bv 32 := 0x648110ef.
Lemma F_a9d08 : fetch_word Ubsan.M.loaded_segments (0xad690 : word) = Some W_a9d08.
Proof. vm_refl. Qed.
Lemma D_a9d08 : decode_any W_a9d08 = Some (Jal 1 71240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d0c : bv 32 := 0x01093503.
Lemma F_a9d0c : fetch_word Ubsan.M.loaded_segments (0xad694 : word) = Some W_a9d0c.
Proof. vm_refl. Qed.
Lemma D_a9d0c : decode_any W_a9d0c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d10 : bv 32 := 0x06050863.
Lemma F_a9d10 : fetch_word Ubsan.M.loaded_segments (0xad698 : word) = Some W_a9d10.
Proof. vm_refl. Qed.
Lemma D_a9d10 : decode_any W_a9d10 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d14 : bv 32 := 0x00892583.
Lemma F_a9d14 : fetch_word Ubsan.M.loaded_segments (0xad69c : word) = Some W_a9d14.
Proof. vm_refl. Qed.
Lemma D_a9d14 : decode_any W_a9d14 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d18 : bv 32 := 0x0180006f.
Lemma F_a9d18 : fetch_word Ubsan.M.loaded_segments (0xad6a0 : word) = Some W_a9d18.
Proof. vm_refl. Qed.
Lemma D_a9d18 : decode_any W_a9d18 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d1c : bv 32 := 0x00053503.
Lemma F_a9d1c : fetch_word Ubsan.M.loaded_segments (0xad6a4 : word) = Some W_a9d1c.
Proof. vm_refl. Qed.
Lemma D_a9d1c : decode_any W_a9d1c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d20 : bv 32 := 0x02000593.
Lemma F_a9d20 : fetch_word Ubsan.M.loaded_segments (0xad6a8 : word) = Some W_a9d20.
Proof. vm_refl. Qed.
Lemma D_a9d20 : decode_any W_a9d20 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d24 : bv 32 := 0x00b92423.
Lemma F_a9d24 : fetch_word Ubsan.M.loaded_segments (0xad6ac : word) = Some W_a9d24.
Proof. vm_refl. Qed.
Lemma D_a9d24 : decode_any W_a9d24 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d28 : bv 32 := 0x00a93823.
Lemma F_a9d28 : fetch_word Ubsan.M.loaded_segments (0xad6b0 : word) = Some W_a9d28.
Proof. vm_refl. Qed.
Lemma D_a9d28 : decode_any W_a9d28 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d2c : bv 32 := 0x04050a63.
Lemma F_a9d2c : fetch_word Ubsan.M.loaded_segments (0xad6b4 : word) = Some W_a9d2c.
Proof. vm_refl. Qed.
Lemma D_a9d2c : decode_any W_a9d2c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d30 : bv 32 := 0xfff5861b.
Lemma F_a9d30 : fetch_word Ubsan.M.loaded_segments (0xad6b8 : word) = Some W_a9d30.
Proof. vm_refl. Qed.
Lemma D_a9d30 : decode_any W_a9d30 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d34 : bv 32 := 0x00c92423.
Lemma F_a9d34 : fetch_word Ubsan.M.loaded_segments (0xad6bc : word) = Some W_a9d34.
Proof. vm_refl. Qed.
Lemma D_a9d34 : decode_any W_a9d34 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d38 : bv 32 := 0xfeb052e3.
Lemma F_a9d38 : fetch_word Ubsan.M.loaded_segments (0xad6c0 : word) = Some W_a9d38.
Proof. vm_refl. Qed.
Lemma D_a9d38 : decode_any W_a9d38 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d3c : bv 32 := 0x01093503.
Lemma F_a9d3c : fetch_word Ubsan.M.loaded_segments (0xad6c4 : word) = Some W_a9d3c.
Proof. vm_refl. Qed.
Lemma D_a9d3c : decode_any W_a9d3c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d40 : bv 32 := 0x00361613.
Lemma F_a9d40 : fetch_word Ubsan.M.loaded_segments (0xad6c8 : word) = Some W_a9d40.
Proof. vm_refl. Qed.
Lemma D_a9d40 : decode_any W_a9d40 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d44 : bv 32 := 0x00c50533.
Lemma F_a9d44 : fetch_word Ubsan.M.loaded_segments (0xad6cc : word) = Some W_a9d44.
Proof. vm_refl. Qed.
Lemma D_a9d44 : decode_any W_a9d44 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d48 : bv 32 := 0x00853983.
Lemma F_a9d48 : fetch_word Ubsan.M.loaded_segments (0xad6d0 : word) = Some W_a9d48.
Proof. vm_refl. Qed.
Lemma D_a9d48 : decode_any W_a9d48 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d4c : bv 32 := 0x10853483.
Lemma F_a9d4c : fetch_word Ubsan.M.loaded_segments (0xad6d4 : word) = Some W_a9d4c.
Proof. vm_refl. Qed.
Lemma D_a9d4c : decode_any W_a9d4c = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d50 : bv 32 := 0x00040513.
Lemma F_a9d50 : fetch_word Ubsan.M.loaded_segments (0xad6d8 : word) = Some W_a9d50.
Proof. vm_refl. Qed.
Lemma D_a9d50 : decode_any W_a9d50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d54 : bv 32 := 0x085110ef.
Lemma F_a9d54 : fetch_word Ubsan.M.loaded_segments (0xad6dc : word) = Some W_a9d54.
Proof. vm_refl. Qed.
Lemma D_a9d54 : decode_any W_a9d54 = Some (Jal 1 71812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d58 : bv 32 := 0x00048513.
Lemma F_a9d58 : fetch_word Ubsan.M.loaded_segments (0xad6e0 : word) = Some W_a9d58.
Proof. vm_refl. Qed.
Lemma D_a9d58 : decode_any W_a9d58 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d5c : bv 32 := 0x000980e7.
Lemma F_a9d5c : fetch_word Ubsan.M.loaded_segments (0xad6e4 : word) = Some W_a9d5c.
Proof. vm_refl. Qed.
Lemma D_a9d5c : decode_any W_a9d5c = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d60 : bv 32 := 0x00040513.
Lemma F_a9d60 : fetch_word Ubsan.M.loaded_segments (0xad6e8 : word) = Some W_a9d60.
Proof. vm_refl. Qed.
Lemma D_a9d60 : decode_any W_a9d60 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d64 : bv 32 := 0x5ec110ef.
Lemma F_a9d64 : fetch_word Ubsan.M.loaded_segments (0xad6ec : word) = Some W_a9d64.
Proof. vm_refl. Qed.
Lemma D_a9d64 : decode_any W_a9d64 = Some (Jal 1 71148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d68 : bv 32 := 0x00892503.
Lemma F_a9d68 : fetch_word Ubsan.M.loaded_segments (0xad6f0 : word) = Some W_a9d68.
Proof. vm_refl. Qed.
Lemma D_a9d68 : decode_any W_a9d68 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d6c : bv 32 := 0xfff5061b.
Lemma F_a9d6c : fetch_word Ubsan.M.loaded_segments (0xad6f4 : word) = Some W_a9d6c.
Proof. vm_refl. Qed.
Lemma D_a9d6c : decode_any W_a9d6c = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d70 : bv 32 := 0x00c92423.
Lemma F_a9d70 : fetch_word Ubsan.M.loaded_segments (0xad6f8 : word) = Some W_a9d70.
Proof. vm_refl. Qed.
Lemma D_a9d70 : decode_any W_a9d70 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d74 : bv 32 := 0xfca044e3.
Lemma F_a9d74 : fetch_word Ubsan.M.loaded_segments (0xad6fc : word) = Some W_a9d74.
Proof. vm_refl. Qed.
Lemma D_a9d74 : decode_any W_a9d74 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d78 : bv 32 := 0x01093503.
Lemma F_a9d78 : fetch_word Ubsan.M.loaded_segments (0xad700 : word) = Some W_a9d78.
Proof. vm_refl. Qed.
Lemma D_a9d78 : decode_any W_a9d78 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d7c : bv 32 := 0xfa1ff06f.
Lemma F_a9d7c : fetch_word Ubsan.M.loaded_segments (0xad704 : word) = Some W_a9d7c.
Proof. vm_refl. Qed.
Lemma D_a9d7c : decode_any W_a9d7c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d80 : bv 32 := 0x00100513.
Lemma F_a9d80 : fetch_word Ubsan.M.loaded_segments (0xad708 : word) = Some W_a9d80.
Proof. vm_refl. Qed.
Lemma D_a9d80 : decode_any W_a9d80 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d84 : bv 32 := 0x00a90023.
Lemma F_a9d84 : fetch_word Ubsan.M.loaded_segments (0xad70c : word) = Some W_a9d84.
Proof. vm_refl. Qed.
Lemma D_a9d84 : decode_any W_a9d84 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d88 : bv 32 := 0x00040513.
Lemma F_a9d88 : fetch_word Ubsan.M.loaded_segments (0xad710 : word) = Some W_a9d88.
Proof. vm_refl. Qed.
Lemma D_a9d88 : decode_any W_a9d88 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d8c : bv 32 := 0x02813083.
Lemma F_a9d8c : fetch_word Ubsan.M.loaded_segments (0xad714 : word) = Some W_a9d8c.
Proof. vm_refl. Qed.
Lemma D_a9d8c : decode_any W_a9d8c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d90 : bv 32 := 0x02013403.
Lemma F_a9d90 : fetch_word Ubsan.M.loaded_segments (0xad718 : word) = Some W_a9d90.
Proof. vm_refl. Qed.
Lemma D_a9d90 : decode_any W_a9d90 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d94 : bv 32 := 0x01813483.
Lemma F_a9d94 : fetch_word Ubsan.M.loaded_segments (0xad71c : word) = Some W_a9d94.
Proof. vm_refl. Qed.
Lemma D_a9d94 : decode_any W_a9d94 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d98 : bv 32 := 0x01013903.
Lemma F_a9d98 : fetch_word Ubsan.M.loaded_segments (0xad720 : word) = Some W_a9d98.
Proof. vm_refl. Qed.
Lemma D_a9d98 : decode_any W_a9d98 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9d9c : bv 32 := 0x00813983.
Lemma F_a9d9c : fetch_word Ubsan.M.loaded_segments (0xad724 : word) = Some W_a9d9c.
Proof. vm_refl. Qed.
Lemma D_a9d9c : decode_any W_a9d9c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9da0 : bv 32 := 0x03010113.
Lemma F_a9da0 : fetch_word Ubsan.M.loaded_segments (0xad728 : word) = Some W_a9da0.
Proof. vm_refl. Qed.
Lemma D_a9da0 : decode_any W_a9da0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9da4 : bv 32 := 0x0351106f.
Lemma F_a9da4 : fetch_word Ubsan.M.loaded_segments (0xad72c : word) = Some W_a9da4.
Proof. vm_refl. Qed.
Lemma D_a9da4 : decode_any W_a9da4 = Some (Jal 0 71732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9da8 : bv 32 := 0x00008067.
Lemma F_a9da8 : fetch_word Ubsan.M.loaded_segments (0xad730 : word) = Some W_a9da8.
Proof. vm_refl. Qed.
Lemma D_a9da8 : decode_any W_a9da8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f38 : bv 32 := 0x00050067.
Lemma F_a9f38 : fetch_word Ubsan.M.loaded_segments (0xad8c0 : word) = Some W_a9f38.
Proof. vm_refl. Qed.
Lemma D_a9f38 : decode_any W_a9f38 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f3c : bv 32 := 0x00008067.
Lemma F_a9f3c : fetch_word Ubsan.M.loaded_segments (0xad8c4 : word) = Some W_a9f3c.
Proof. vm_refl. Qed.
Lemma D_a9f3c : decode_any W_a9f3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f40 : bv 32 := 0xfe010113.
Lemma F_a9f40 : fetch_word Ubsan.M.loaded_segments (0xad8c8 : word) = Some W_a9f40.
Proof. vm_refl. Qed.
Lemma D_a9f40 : decode_any W_a9f40 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f44 : bv 32 := 0x00113c23.
Lemma F_a9f44 : fetch_word Ubsan.M.loaded_segments (0xad8cc : word) = Some W_a9f44.
Proof. vm_refl. Qed.
Lemma D_a9f44 : decode_any W_a9f44 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f48 : bv 32 := 0x00813823.
Lemma F_a9f48 : fetch_word Ubsan.M.loaded_segments (0xad8d0 : word) = Some W_a9f48.
Proof. vm_refl. Qed.
Lemma D_a9f48 : decode_any W_a9f48 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f4c : bv 32 := 0x00913423.
Lemma F_a9f4c : fetch_word Ubsan.M.loaded_segments (0xad8d4 : word) = Some W_a9f4c.
Proof. vm_refl. Qed.
Lemma D_a9f4c : decode_any W_a9f4c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f50 : bv 32 := 0x0001d517.
Lemma F_a9f50 : fetch_word Ubsan.M.loaded_segments (0xad8d8 : word) = Some W_a9f50.
Proof. vm_refl. Qed.
Lemma D_a9f50 : decode_any W_a9f50 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f54 : bv 32 := 0x0001d597.
Lemma F_a9f54 : fetch_word Ubsan.M.loaded_segments (0xad8dc : word) = Some W_a9f54.
Proof. vm_refl. Qed.
Lemma D_a9f54 : decode_any W_a9f54 = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f58 : bv 32 := 0x95053503.
Lemma F_a9f58 : fetch_word Ubsan.M.loaded_segments (0xad8e0 : word) = Some W_a9f58.
Proof. vm_refl. Qed.
Lemma D_a9f58 : decode_any W_a9f58 = Some (Load SZ8 true 10 10 2384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f5c : bv 32 := 0x9545b403.
Lemma F_a9f5c : fetch_word Ubsan.M.loaded_segments (0xad8e4 : word) = Some W_a9f5c.
Proof. vm_refl. Qed.
Lemma D_a9f5c : decode_any W_a9f5c = Some (Load SZ8 true 8 11 2388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f60 : bv 32 := 0x00a47c63.
Lemma F_a9f60 : fetch_word Ubsan.M.loaded_segments (0xad8e8 : word) = Some W_a9f60.
Proof. vm_refl. Qed.
Lemma D_a9f60 : decode_any W_a9f60 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f64 : bv 32 := 0xff853583.
Lemma F_a9f64 : fetch_word Ubsan.M.loaded_segments (0xad8ec : word) = Some W_a9f64.
Proof. vm_refl. Qed.
Lemma D_a9f64 : decode_any W_a9f64 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f68 : bv 32 := 0xff850493.
Lemma F_a9f68 : fetch_word Ubsan.M.loaded_segments (0xad8f0 : word) = Some W_a9f68.
Proof. vm_refl. Qed.
Lemma D_a9f68 : decode_any W_a9f68 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f6c : bv 32 := 0x000580e7.
Lemma F_a9f6c : fetch_word Ubsan.M.loaded_segments (0xad8f4 : word) = Some W_a9f6c.
Proof. vm_refl. Qed.
Lemma D_a9f6c : decode_any W_a9f6c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f70 : bv 32 := 0x00048513.
Lemma F_a9f70 : fetch_word Ubsan.M.loaded_segments (0xad8f8 : word) = Some W_a9f70.
Proof. vm_refl. Qed.
Lemma D_a9f70 : decode_any W_a9f70 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f74 : bv 32 := 0xfe9468e3.
Lemma F_a9f74 : fetch_word Ubsan.M.loaded_segments (0xad8fc : word) = Some W_a9f74.
Proof. vm_refl. Qed.
Lemma D_a9f74 : decode_any W_a9f74 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f78 : bv 32 := 0x01813083.
Lemma F_a9f78 : fetch_word Ubsan.M.loaded_segments (0xad900 : word) = Some W_a9f78.
Proof. vm_refl. Qed.
Lemma D_a9f78 : decode_any W_a9f78 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f7c : bv 32 := 0x01013403.
Lemma F_a9f7c : fetch_word Ubsan.M.loaded_segments (0xad904 : word) = Some W_a9f7c.
Proof. vm_refl. Qed.
Lemma D_a9f7c : decode_any W_a9f7c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f80 : bv 32 := 0x00813483.
Lemma F_a9f80 : fetch_word Ubsan.M.loaded_segments (0xad908 : word) = Some W_a9f80.
Proof. vm_refl. Qed.
Lemma D_a9f80 : decode_any W_a9f80 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f84 : bv 32 := 0x02010113.
Lemma F_a9f84 : fetch_word Ubsan.M.loaded_segments (0xad90c : word) = Some W_a9f84.
Proof. vm_refl. Qed.
Lemma D_a9f84 : decode_any W_a9f84 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f88 : bv 32 := 0xfb5ff06f.
Lemma F_a9f88 : fetch_word Ubsan.M.loaded_segments (0xad910 : word) = Some W_a9f88.
Proof. vm_refl. Qed.
Lemma D_a9f88 : decode_any W_a9f88 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f8c : bv 32 := 0xff010113.
Lemma F_a9f8c : fetch_word Ubsan.M.loaded_segments (0xad914 : word) = Some W_a9f8c.
Proof. vm_refl. Qed.
Lemma D_a9f8c : decode_any W_a9f8c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f90 : bv 32 := 0x00113423.
Lemma F_a9f90 : fetch_word Ubsan.M.loaded_segments (0xad918 : word) = Some W_a9f90.
Proof. vm_refl. Qed.
Lemma D_a9f90 : decode_any W_a9f90 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f94 : bv 32 := 0x00813023.
Lemma F_a9f94 : fetch_word Ubsan.M.loaded_segments (0xad91c : word) = Some W_a9f94.
Proof. vm_refl. Qed.
Lemma D_a9f94 : decode_any W_a9f94 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f98 : bv 32 := 0x00000593.
Lemma F_a9f98 : fetch_word Ubsan.M.loaded_segments (0xad920 : word) = Some W_a9f98.
Proof. vm_refl. Qed.
Lemma D_a9f98 : decode_any W_a9f98 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f9c : bv 32 := 0x00020613.
Lemma F_a9f9c : fetch_word Ubsan.M.loaded_segments (0xad924 : word) = Some W_a9f9c.
Proof. vm_refl. Qed.
Lemma D_a9f9c : decode_any W_a9f9c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fa0 : bv 32 := 0xf5862603.
Lemma F_a9fa0 : fetch_word Ubsan.M.loaded_segments (0xad928 : word) = Some W_a9fa0.
Proof. vm_refl. Qed.
Lemma D_a9fa0 : decode_any W_a9fa0 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fa4 : bv 32 := 0x00050697.
Lemma F_a9fa4 : fetch_word Ubsan.M.loaded_segments (0xad92c : word) = Some W_a9fa4.
Proof. vm_refl. Qed.
Lemma D_a9fa4 : decode_any W_a9fa4 = Some (Auipc 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fa8 : bv 32 := 0x94c68693.
Lemma F_a9fa8 : fetch_word Ubsan.M.loaded_segments (0xad930 : word) = Some W_a9fa8.
Proof. vm_refl. Qed.
Lemma D_a9fa8 : decode_any W_a9fa8 = Some (OpImm ALU_ADD 13 13 2380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fac : bv 32 := 0x1606a72f.
Lemma F_a9fac : fetch_word Ubsan.M.loaded_segments (0xad934 : word) = Some W_a9fac.
Proof. vm_refl. Qed.
Lemma D_a9fac : decode_any W_a9fac = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fb0 : bv 32 := 0x00b71663.
Lemma F_a9fb0 : fetch_word Ubsan.M.loaded_segments (0xad938 : word) = Some W_a9fb0.
Proof. vm_refl. Qed.
Lemma D_a9fb0 : decode_any W_a9fb0 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fb4 : bv 32 := 0x1ec6a7af.
Lemma F_a9fb4 : fetch_word Ubsan.M.loaded_segments (0xad93c : word) = Some W_a9fb4.
Proof. vm_refl. Qed.
Lemma D_a9fb4 : decode_any W_a9fb4 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fb8 : bv 32 := 0xfe079ae3.
Lemma F_a9fb8 : fetch_word Ubsan.M.loaded_segments (0xad940 : word) = Some W_a9fb8.
Proof. vm_refl. Qed.
Lemma D_a9fb8 : decode_any W_a9fb8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fbc : bv 32 := 0x0007059b.
Lemma F_a9fbc : fetch_word Ubsan.M.loaded_segments (0xad944 : word) = Some W_a9fbc.
Proof. vm_refl. Qed.
Lemma D_a9fbc : decode_any W_a9fbc = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fc0 : bv 32 := 0x02c58263.
Lemma F_a9fc0 : fetch_word Ubsan.M.loaded_segments (0xad948 : word) = Some W_a9fc0.
Proof. vm_refl. Qed.
Lemma D_a9fc0 : decode_any W_a9fc0 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fc4 : bv 32 := 0x02058263.
Lemma F_a9fc4 : fetch_word Ubsan.M.loaded_segments (0xad94c : word) = Some W_a9fc4.
Proof. vm_refl. Qed.
Lemma D_a9fc4 : decode_any W_a9fc4 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fe8 : bv 32 := 0x00050413.
Lemma F_a9fe8 : fetch_word Ubsan.M.loaded_segments (0xad970 : word) = Some W_a9fe8.
Proof. vm_refl. Qed.
Lemma D_a9fe8 : decode_any W_a9fe8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fec : bv 32 := 0xcf5ff0ef.
Lemma F_a9fec : fetch_word Ubsan.M.loaded_segments (0xad974 : word) = Some W_a9fec.
Proof. vm_refl. Qed.
Lemma D_a9fec : decode_any W_a9fec = Some (Jal 1 2096372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9ff0 : bv 32 := 0xf51ff0ef.
Lemma F_a9ff0 : fetch_word Ubsan.M.loaded_segments (0xad978 : word) = Some W_a9ff0.
Proof. vm_refl. Qed.
Lemma D_a9ff0 : decode_any W_a9ff0 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9ff4 : bv 32 := 0x6dc050ef.
Lemma F_a9ff4 : fetch_word Ubsan.M.loaded_segments (0xad97c : word) = Some W_a9ff4.
Proof. vm_refl. Qed.
Lemma D_a9ff4 : decode_any W_a9ff4 = Some (Jal 1 22236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9ff8 : bv 32 := 0x00040513.
Lemma F_a9ff8 : fetch_word Ubsan.M.loaded_segments (0xad980 : word) = Some W_a9ff8.
Proof. vm_refl. Qed.
Lemma D_a9ff8 : decode_any W_a9ff8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9ffc : bv 32 := 0xc99ff0ef.
Lemma F_a9ffc : fetch_word Ubsan.M.loaded_segments (0xad984 : word) = Some W_a9ffc.
Proof. vm_refl. Qed.
Lemma D_a9ffc : decode_any W_a9ffc = Some (Jal 1 2096280, 4%Z).
Proof. vm_refl. Qed.

