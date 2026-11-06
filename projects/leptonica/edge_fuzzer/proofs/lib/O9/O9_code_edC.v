(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushS9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5ccf8 : bv 32 := 0xfd010113.
Lemma F_5ccf8 : fetch_word Plain.M.loaded_segments (0x5cd50 : word) = Some W_5ccf8.
Proof. vm_refl. Qed.
Lemma D_5ccf8 : decode_any W_5ccf8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ccfc : bv 32 := 0x02113423.
Lemma F_5ccfc : fetch_word Plain.M.loaded_segments (0x5cd54 : word) = Some W_5ccfc.
Proof. vm_refl. Qed.
Lemma D_5ccfc : decode_any W_5ccfc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd00 : bv 32 := 0x02813023.
Lemma F_5cd00 : fetch_word Plain.M.loaded_segments (0x5cd58 : word) = Some W_5cd00.
Proof. vm_refl. Qed.
Lemma D_5cd00 : decode_any W_5cd00 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd04 : bv 32 := 0x00913c23.
Lemma F_5cd04 : fetch_word Plain.M.loaded_segments (0x5cd5c : word) = Some W_5cd04.
Proof. vm_refl. Qed.
Lemma D_5cd04 : decode_any W_5cd04 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd08 : bv 32 := 0x00058413.
Lemma F_5cd08 : fetch_word Plain.M.loaded_segments (0x5cd60 : word) = Some W_5cd08.
Proof. vm_refl. Qed.
Lemma D_5cd08 : decode_any W_5cd08 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd0c : bv 32 := 0x00300593.
Lemma F_5cd0c : fetch_word Plain.M.loaded_segments (0x5cd64 : word) = Some W_5cd0c.
Proof. vm_refl. Qed.
Lemma D_5cd0c : decode_any W_5cd0c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd10 : bv 32 := 0x04b46863.
Lemma F_5cd10 : fetch_word Plain.M.loaded_segments (0x5cd68 : word) = Some W_5cd10.
Proof. vm_refl. Qed.
Lemma D_5cd10 : decode_any W_5cd10 = Some (Branch BC_LTU 8 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd14 : bv 32 := 0x00050493.
Lemma F_5cd14 : fetch_word Plain.M.loaded_segments (0x5cd6c : word) = Some W_5cd14.
Proof. vm_refl. Qed.
Lemma D_5cd14 : decode_any W_5cd14 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd18 : bv 32 := 0x00000517.
Lemma F_5cd18 : fetch_word Plain.M.loaded_segments (0x5cd70 : word) = Some W_5cd18.
Proof. vm_refl. Qed.
Lemma D_5cd18 : decode_any W_5cd18 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd1c : bv 32 := 0x06050513.
Lemma F_5cd1c : fetch_word Plain.M.loaded_segments (0x5cd74 : word) = Some W_5cd1c.
Proof. vm_refl. Qed.
Lemma D_5cd1c : decode_any W_5cd1c = Some (OpImm ALU_ADD 10 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd20 : bv 32 := 0x1f8000ef.
Lemma F_5cd20 : fetch_word Plain.M.loaded_segments (0x5cd78 : word) = Some W_5cd20.
Proof. vm_refl. Qed.
Lemma D_5cd20 : decode_any W_5cd20 = Some (Jal 1 504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd24 : bv 32 := 0x00048513.
Lemma F_5cd24 : fetch_word Plain.M.loaded_segments (0x5cd7c : word) = Some W_5cd24.
Proof. vm_refl. Qed.
Lemma D_5cd24 : decode_any W_5cd24 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd28 : bv 32 := 0x00040593.
Lemma F_5cd28 : fetch_word Plain.M.loaded_segments (0x5cd80 : word) = Some W_5cd28.
Proof. vm_refl. Qed.
Lemma D_5cd28 : decode_any W_5cd28 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd2c : bv 32 := 0x3b1150ef.
Lemma F_5cd2c : fetch_word Plain.M.loaded_segments (0x5cd84 : word) = Some W_5cd2c.
Proof. vm_refl. Qed.
Lemma D_5cd2c : decode_any W_5cd2c = Some (Jal 1 89008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd30 : bv 32 := 0x00a13823.
Lemma F_5cd30 : fetch_word Plain.M.loaded_segments (0x5cd88 : word) = Some W_5cd30.
Proof. vm_refl. Qed.
Lemma D_5cd30 : decode_any W_5cd30 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd34 : bv 32 := 0x02050663.
Lemma F_5cd34 : fetch_word Plain.M.loaded_segments (0x5cd8c : word) = Some W_5cd34.
Proof. vm_refl. Qed.
Lemma D_5cd34 : decode_any W_5cd34 = Some (Branch BC_EQ 10 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd38 : bv 32 := 0x00100593.
Lemma F_5cd38 : fetch_word Plain.M.loaded_segments (0x5cd90 : word) = Some W_5cd38.
Proof. vm_refl. Qed.
Lemma D_5cd38 : decode_any W_5cd38 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd3c : bv 32 := 0x00100613.
Lemma F_5cd3c : fetch_word Plain.M.loaded_segments (0x5cd94 : word) = Some W_5cd3c.
Proof. vm_refl. Qed.
Lemma D_5cd3c : decode_any W_5cd3c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd40 : bv 32 := 0x00100693.
Lemma F_5cd40 : fetch_word Plain.M.loaded_segments (0x5cd98 : word) = Some W_5cd40.
Proof. vm_refl. Qed.
Lemma D_5cd40 : decode_any W_5cd40 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd44 : bv 32 := 0x00c10713.
Lemma F_5cd44 : fetch_word Plain.M.loaded_segments (0x5cd9c : word) = Some W_5cd44.
Proof. vm_refl. Qed.
Lemma D_5cd44 : decode_any W_5cd44 = Some (OpImm ALU_ADD 14 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd48 : bv 32 := 0x00810793.
Lemma F_5cd48 : fetch_word Plain.M.loaded_segments (0x5cda0 : word) = Some W_5cd48.
Proof. vm_refl. Qed.
Lemma D_5cd48 : decode_any W_5cd48 = Some (OpImm ALU_ADD 15 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd4c : bv 32 := 0x00410813.
Lemma F_5cd4c : fetch_word Plain.M.loaded_segments (0x5cda4 : word) = Some W_5cd4c.
Proof. vm_refl. Qed.
Lemma D_5cd4c : decode_any W_5cd4c = Some (OpImm ALU_ADD 16 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd50 : bv 32 := 0x00000893.
Lemma F_5cd50 : fetch_word Plain.M.loaded_segments (0x5cda8 : word) = Some W_5cd50.
Proof. vm_refl. Qed.
Lemma D_5cd50 : decode_any W_5cd50 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd54 : bv 32 := 0x4e11a0ef.
Lemma F_5cd54 : fetch_word Plain.M.loaded_segments (0x5cdac : word) = Some W_5cd54.
Proof. vm_refl. Qed.
Lemma D_5cd54 : decode_any W_5cd54 = Some (Jal 1 109792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd58 : bv 32 := 0x01010513.
Lemma F_5cd58 : fetch_word Plain.M.loaded_segments (0x5cdb0 : word) = Some W_5cd58.
Proof. vm_refl. Qed.
Lemma D_5cd58 : decode_any W_5cd58 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd5c : bv 32 := 0x0a1050ef.
Lemma F_5cd5c : fetch_word Plain.M.loaded_segments (0x5cdb4 : word) = Some W_5cd5c.
Proof. vm_refl. Qed.
Lemma D_5cd5c : decode_any W_5cd5c = Some (Jal 1 22688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd60 : bv 32 := 0x00000513.
Lemma F_5cd60 : fetch_word Plain.M.loaded_segments (0x5cdb8 : word) = Some W_5cd60.
Proof. vm_refl. Qed.
Lemma D_5cd60 : decode_any W_5cd60 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd64 : bv 32 := 0x02813083.
Lemma F_5cd64 : fetch_word Plain.M.loaded_segments (0x5cdbc : word) = Some W_5cd64.
Proof. vm_refl. Qed.
Lemma D_5cd64 : decode_any W_5cd64 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd68 : bv 32 := 0x02013403.
Lemma F_5cd68 : fetch_word Plain.M.loaded_segments (0x5cdc0 : word) = Some W_5cd68.
Proof. vm_refl. Qed.
Lemma D_5cd68 : decode_any W_5cd68 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd6c : bv 32 := 0x01813483.
Lemma F_5cd6c : fetch_word Plain.M.loaded_segments (0x5cdc4 : word) = Some W_5cd6c.
Proof. vm_refl. Qed.
Lemma D_5cd6c : decode_any W_5cd6c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd70 : bv 32 := 0x03010113.
Lemma F_5cd70 : fetch_word Plain.M.loaded_segments (0x5cdc8 : word) = Some W_5cd70.
Proof. vm_refl. Qed.
Lemma D_5cd70 : decode_any W_5cd70 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cd74 : bv 32 := 0x00008067.
Lemma F_5cd74 : fetch_word Plain.M.loaded_segments (0x5cdcc : word) = Some W_5cd74.
Proof. vm_refl. Qed.
Lemma D_5cd74 : decode_any W_5cd74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf18 : bv 32 := 0x00051663.
Lemma F_5cf18 : fetch_word Plain.M.loaded_segments (0x5cf70 : word) = Some W_5cf18.
Proof. vm_refl. Qed.
Lemma D_5cf18 : decode_any W_5cf18 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf24 : bv 32 := 0x00092597.
Lemma F_5cf24 : fetch_word Plain.M.loaded_segments (0x5cf7c : word) = Some W_5cf24.
Proof. vm_refl. Qed.
Lemma D_5cf24 : decode_any W_5cf24 = Some (Auipc 11 146, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf28 : bv 32 := 0x7ca5be23.
Lemma F_5cf28 : fetch_word Plain.M.loaded_segments (0x5cf80 : word) = Some W_5cf28.
Proof. vm_refl. Qed.
Lemma D_5cf28 : decode_any W_5cf28 = Some (Store SZ8 11 10 2012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cf2c : bv 32 := 0x00008067.
Lemma F_5cf2c : fetch_word Plain.M.loaded_segments (0x5cf84 : word) = Some W_5cf2c.
Proof. vm_refl. Qed.
Lemma D_5cf2c : decode_any W_5cf2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e0 : bv 32 := 0xf8010113.
Lemma F_606e0 : fetch_word Plain.M.loaded_segments (0x60738 : word) = Some W_606e0.
Proof. vm_refl. Qed.
Lemma D_606e0 : decode_any W_606e0 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e4 : bv 32 := 0x06113c23.
Lemma F_606e4 : fetch_word Plain.M.loaded_segments (0x6073c : word) = Some W_606e4.
Proof. vm_refl. Qed.
Lemma D_606e4 : decode_any W_606e4 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e8 : bv 32 := 0x06813823.
Lemma F_606e8 : fetch_word Plain.M.loaded_segments (0x60740 : word) = Some W_606e8.
Proof. vm_refl. Qed.
Lemma D_606e8 : decode_any W_606e8 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606ec : bv 32 := 0x06913423.
Lemma F_606ec : fetch_word Plain.M.loaded_segments (0x60744 : word) = Some W_606ec.
Proof. vm_refl. Qed.
Lemma D_606ec : decode_any W_606ec = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f0 : bv 32 := 0x07213023.
Lemma F_606f0 : fetch_word Plain.M.loaded_segments (0x60748 : word) = Some W_606f0.
Proof. vm_refl. Qed.
Lemma D_606f0 : decode_any W_606f0 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f4 : bv 32 := 0x05313c23.
Lemma F_606f4 : fetch_word Plain.M.loaded_segments (0x6074c : word) = Some W_606f4.
Proof. vm_refl. Qed.
Lemma D_606f4 : decode_any W_606f4 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f8 : bv 32 := 0x05413823.
Lemma F_606f8 : fetch_word Plain.M.loaded_segments (0x60750 : word) = Some W_606f8.
Proof. vm_refl. Qed.
Lemma D_606f8 : decode_any W_606f8 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606fc : bv 32 := 0x05513423.
Lemma F_606fc : fetch_word Plain.M.loaded_segments (0x60754 : word) = Some W_606fc.
Proof. vm_refl. Qed.
Lemma D_606fc : decode_any W_606fc = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60700 : bv 32 := 0x05613023.
Lemma F_60700 : fetch_word Plain.M.loaded_segments (0x60758 : word) = Some W_60700.
Proof. vm_refl. Qed.
Lemma D_60700 : decode_any W_60700 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60704 : bv 32 := 0x03713c23.
Lemma F_60704 : fetch_word Plain.M.loaded_segments (0x6075c : word) = Some W_60704.
Proof. vm_refl. Qed.
Lemma D_60704 : decode_any W_60704 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60708 : bv 32 := 0x03813823.
Lemma F_60708 : fetch_word Plain.M.loaded_segments (0x60760 : word) = Some W_60708.
Proof. vm_refl. Qed.
Lemma D_60708 : decode_any W_60708 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6070c : bv 32 := 0x03913423.
Lemma F_6070c : fetch_word Plain.M.loaded_segments (0x60764 : word) = Some W_6070c.
Proof. vm_refl. Qed.
Lemma D_6070c : decode_any W_6070c = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60710 : bv 32 := 0x02813027.
Lemma F_60710 : fetch_word Plain.M.loaded_segments (0x60768 : word) = Some W_60710.
Proof. vm_refl. Qed.
Lemma D_60710 : decode_any W_60710 = Some (FStore FMT_D 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60714 : bv 32 := 0x00913c27.
Lemma F_60714 : fetch_word Plain.M.loaded_segments (0x6076c : word) = Some W_60714.
Proof. vm_refl. Qed.
Lemma D_60714 : decode_any W_60714 = Some (FStore FMT_D 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60718 : bv 32 := 0x01213827.
Lemma F_60718 : fetch_word Plain.M.loaded_segments (0x60770 : word) = Some W_60718.
Proof. vm_refl. Qed.
Lemma D_60718 : decode_any W_60718 = Some (FStore FMT_D 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6071c : bv 32 := 0x00058a13.
Lemma F_6071c : fetch_word Plain.M.loaded_segments (0x60774 : word) = Some W_6071c.
Proof. vm_refl. Qed.
Lemma D_6071c : decode_any W_6071c = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60720 : bv 32 := 0x20a50453.
Lemma F_60720 : fetch_word Plain.M.loaded_segments (0x60778 : word) = Some W_60720.
Proof. vm_refl. Qed.
Lemma D_60720 : decode_any W_60720 = Some (Fsgnj F_SGNJ FMT_S 8 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60724 : bv 32 := 0x00050413.
Lemma F_60724 : fetch_word Plain.M.loaded_segments (0x6077c : word) = Some W_60724.
Proof. vm_refl. Qed.
Lemma D_60724 : decode_any W_60724 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60728 : bv 32 := 0x00058463.
Lemma F_60728 : fetch_word Plain.M.loaded_segments (0x60780 : word) = Some W_60728.
Proof. vm_refl. Qed.
Lemma D_60728 : decode_any W_60728 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60730 : bv 32 := 0x02040863.
Lemma F_60730 : fetch_word Plain.M.loaded_segments (0x60788 : word) = Some W_60730.
Proof. vm_refl. Qed.
Lemma D_60730 : decode_any W_60730 = Some (Branch BC_EQ 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60734 : bv 32 := 0xf0000953.
Lemma F_60734 : fetch_word Plain.M.loaded_segments (0x6078c : word) = Some W_60734.
Proof. vm_refl. Qed.
Lemma D_60734 : decode_any W_60734 = Some (Fmv FMV_F_X FMT_S 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60738 : bv 32 := 0xa1241553.
Lemma F_60738 : fetch_word Plain.M.loaded_segments (0x60790 : word) = Some W_60738.
Proof. vm_refl. Qed.
Lemma D_60738 : decode_any W_60738 = Some (Fcmp F_LT FMT_S 10 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6073c : bv 32 := 0x08050a63.
Lemma F_6073c : fetch_word Plain.M.loaded_segments (0x60794 : word) = Some W_6073c.
Proof. vm_refl. Qed.
Lemma D_6073c : decode_any W_6073c = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607d0 : bv 32 := 0x00040513.
Lemma F_607d0 : fetch_word Plain.M.loaded_segments (0x60828 : word) = Some W_607d0.
Proof. vm_refl. Qed.
Lemma D_607d0 : decode_any W_607d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607d4 : bv 32 := 0x450000ef.
Lemma F_607d4 : fetch_word Plain.M.loaded_segments (0x6082c : word) = Some W_607d4.
Proof. vm_refl. Qed.
Lemma D_607d4 : decode_any W_607d4 = Some (Jal 1 1104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607d8 : bv 32 := 0x00050913.
Lemma F_607d8 : fetch_word Plain.M.loaded_segments (0x60830 : word) = Some W_607d8.
Proof. vm_refl. Qed.
Lemma D_607d8 : decode_any W_607d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607dc : bv 32 := 0x00000513.
Lemma F_607dc : fetch_word Plain.M.loaded_segments (0x60834 : word) = Some W_607dc.
Proof. vm_refl. Qed.
Lemma D_607dc : decode_any W_607dc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607e0 : bv 32 := 0x1b4000ef.
Lemma F_607e0 : fetch_word Plain.M.loaded_segments (0x60838 : word) = Some W_607e0.
Proof. vm_refl. Qed.
Lemma D_607e0 : decode_any W_607e0 = Some (Jal 1 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607e4 : bv 32 := 0x00050493.
Lemma F_607e4 : fetch_word Plain.M.loaded_segments (0x6083c : word) = Some W_607e4.
Proof. vm_refl. Qed.
Lemma D_607e4 : decode_any W_607e4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607e8 : bv 32 := 0x000a0c63.
Lemma F_607e8 : fetch_word Plain.M.loaded_segments (0x60840 : word) = Some W_607e8.
Proof. vm_refl. Qed.
Lemma D_607e8 : decode_any W_607e8 = Some (Branch BC_EQ 20 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60800 : bv 32 := 0x00000993.
Lemma F_60800 : fetch_word Plain.M.loaded_segments (0x60858 : word) = Some W_60800.
Proof. vm_refl. Qed.
Lemma D_60800 : decode_any W_60800 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60804 : bv 32 := 0x00c10613.
Lemma F_60804 : fetch_word Plain.M.loaded_segments (0x6085c : word) = Some W_60804.
Proof. vm_refl. Qed.
Lemma D_60804 : decode_any W_60804 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60808 : bv 32 := 0x00040513.
Lemma F_60808 : fetch_word Plain.M.loaded_segments (0x60860 : word) = Some W_60808.
Proof. vm_refl. Qed.
Lemma D_60808 : decode_any W_60808 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6080c : bv 32 := 0x00000593.
Lemma F_6080c : fetch_word Plain.M.loaded_segments (0x60864 : word) = Some W_6080c.
Proof. vm_refl. Qed.
Lemma D_6080c : decode_any W_6080c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60810 : bv 32 := 0x54c000ef.
Lemma F_60810 : fetch_word Plain.M.loaded_segments (0x60868 : word) = Some W_60810.
Proof. vm_refl. Qed.
Lemma D_60810 : decode_any W_60810 = Some (Jal 1 1356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60814 : bv 32 := 0x00200513.
Lemma F_60814 : fetch_word Plain.M.loaded_segments (0x6086c : word) = Some W_60814.
Proof. vm_refl. Qed.
Lemma D_60814 : decode_any W_60814 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60818 : bv 32 := 0x12a94c63.
Lemma F_60818 : fetch_word Plain.M.loaded_segments (0x60870 : word) = Some W_60818.
Proof. vm_refl. Qed.
Lemma D_60818 : decode_any W_60818 = Some (Branch BC_LT 18 10 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6081c : bv 32 := 0x00100a93.
Lemma F_6081c : fetch_word Plain.M.loaded_segments (0x60874 : word) = Some W_6081c.
Proof. vm_refl. Qed.
Lemma D_6081c : decode_any W_6081c = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60820 : bv 32 := 0x00810613.
Lemma F_60820 : fetch_word Plain.M.loaded_segments (0x60878 : word) = Some W_60820.
Proof. vm_refl. Qed.
Lemma D_60820 : decode_any W_60820 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60824 : bv 32 := 0x00040513.
Lemma F_60824 : fetch_word Plain.M.loaded_segments (0x6087c : word) = Some W_60824.
Proof. vm_refl. Qed.
Lemma D_60824 : decode_any W_60824 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60828 : bv 32 := 0x000a8593.
Lemma F_60828 : fetch_word Plain.M.loaded_segments (0x60880 : word) = Some W_60828.
Proof. vm_refl. Qed.
Lemma D_60828 : decode_any W_60828 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6082c : bv 32 := 0x530000ef.
Lemma F_6082c : fetch_word Plain.M.loaded_segments (0x60884 : word) = Some W_6082c.
Proof. vm_refl. Qed.
Lemma D_6082c : decode_any W_6082c = Some (Jal 1 1328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60830 : bv 32 := 0x00812487.
Lemma F_60830 : fetch_word Plain.M.loaded_segments (0x60888 : word) = Some W_60830.
Proof. vm_refl. Qed.
Lemma D_60830 : decode_any W_60830 = Some (FLoad FMT_S 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60834 : bv 32 := 0x00c12787.
Lemma F_60834 : fetch_word Plain.M.loaded_segments (0x6088c : word) = Some W_60834.
Proof. vm_refl. Qed.
Lemma D_60834 : decode_any W_60834 = Some (FLoad FMT_S 15 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60838 : bv 32 := 0x08f4f753.
Lemma F_60838 : fetch_word Plain.M.loaded_segments (0x60890 : word) = Some W_60838.
Proof. vm_refl. Qed.
Lemma D_60838 : decode_any W_60838 = Some (Fari F_SUB FMT_S 14 9 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6083c : bv 32 := 0xa1271553.
Lemma F_6083c : fetch_word Plain.M.loaded_segments (0x60894 : word) = Some W_6083c.
Proof. vm_refl. Qed.
Lemma D_6083c : decode_any W_6083c = Some (Fcmp F_LT FMT_S 10 14 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60840 : bv 32 := 0x00050463.
Lemma F_60840 : fetch_word Plain.M.loaded_segments (0x60898 : word) = Some W_60840.
Proof. vm_refl. Qed.
Lemma D_60840 : decode_any W_60840 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60844 : bv 32 := 0x20e71753.
Lemma F_60844 : fetch_word Plain.M.loaded_segments (0x6089c : word) = Some W_60844.
Proof. vm_refl. Qed.
Lemma D_60844 : decode_any W_60844 = Some (Fsgnj F_SGNJN FMT_S 14 14 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60848 : bv 32 := 0xa0e40553.
Lemma F_60848 : fetch_word Plain.M.loaded_segments (0x608a0 : word) = Some W_60848.
Proof. vm_refl. Qed.
Lemma D_60848 : decode_any W_60848 = Some (Fcmp F_LE FMT_S 10 8 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6084c : bv 32 := 0x00051863.
Lemma F_6084c : fetch_word Plain.M.loaded_segments (0x608a4 : word) = Some W_6084c.
Proof. vm_refl. Qed.
Lemma D_6084c : decode_any W_6084c = Some (Branch BC_NE 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60850 : bv 32 := 0x001a8a9b.
Lemma F_60850 : fetch_word Plain.M.loaded_segments (0x608a8 : word) = Some W_60850.
Proof. vm_refl. Qed.
Lemma D_60850 : decode_any W_60850 = Some (OpImm32 21 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60854 : bv 32 := 0xfd5916e3.
Lemma F_60854 : fetch_word Plain.M.loaded_segments (0x608ac : word) = Some W_60854.
Proof. vm_refl. Qed.
Lemma D_60854 : decode_any W_60854 = Some (Branch BC_NE 18 21 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60858 : bv 32 := 0x0f80006f.
Lemma F_60858 : fetch_word Plain.M.loaded_segments (0x608b0 : word) = Some W_60858.
Proof. vm_refl. Qed.
Lemma D_60858 : decode_any W_60858 = Some (Jal 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6085c : bv 32 := 0x001a8a1b.
Lemma F_6085c : fetch_word Plain.M.loaded_segments (0x608b4 : word) = Some W_6085c.
Proof. vm_refl. Qed.
Lemma D_6085c : decode_any W_6085c = Some (OpImm32 20 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60860 : bv 32 := 0x0f2a5863.
Lemma F_60860 : fetch_word Plain.M.loaded_segments (0x608b8 : word) = Some W_60860.
Proof. vm_refl. Qed.
Lemma D_60860 : decode_any W_60860 = Some (Branch BC_GE 20 18 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60864 : bv 32 := 0xa0979553.
Lemma F_60864 : fetch_word Plain.M.loaded_segments (0x608bc : word) = Some W_60864.
Proof. vm_refl. Qed.
Lemma D_60864 : decode_any W_60864 = Some (Fcmp F_LT FMT_S 10 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60868 : bv 32 := 0x00100b13.
Lemma F_60868 : fetch_word Plain.M.loaded_segments (0x608c0 : word) = Some W_60868.
Proof. vm_refl. Qed.
Lemma D_60868 : decode_any W_60868 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6086c : bv 32 := 0xfff5051b.
Lemma F_6086c : fetch_word Plain.M.loaded_segments (0x608c4 : word) = Some W_6086c.
Proof. vm_refl. Qed.
Lemma D_6086c : decode_any W_6086c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60870 : bv 32 := 0x00156c93.
Lemma F_60870 : fetch_word Plain.M.loaded_segments (0x608c8 : word) = Some W_60870.
Proof. vm_refl. Qed.
Lemma D_60870 : decode_any W_60870 = Some (OpImm ALU_OR 25 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60874 : bv 32 := 0xfff00b93.
Lemma F_60874 : fetch_word Plain.M.loaded_segments (0x608cc : word) = Some W_60874.
Proof. vm_refl. Qed.
Lemma D_60874 : decode_any W_60874 = Some (OpImm ALU_ADD 23 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60878 : bv 32 := 0x20948953.
Lemma F_60878 : fetch_word Plain.M.loaded_segments (0x608d0 : word) = Some W_60878.
Proof. vm_refl. Qed.
Lemma D_60878 : decode_any W_60878 = Some (Fsgnj F_SGNJ FMT_S 18 9 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6087c : bv 32 := 0x01c0006f.
Lemma F_6087c : fetch_word Plain.M.loaded_segments (0x608d4 : word) = Some W_6087c.
Proof. vm_refl. Qed.
Lemma D_6087c : decode_any W_6087c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60880 : bv 32 := 0x000a0a93.
Lemma F_60880 : fetch_word Plain.M.loaded_segments (0x608d8 : word) = Some W_60880.
Proof. vm_refl. Qed.
Lemma D_60880 : decode_any W_60880 = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60884 : bv 32 := 0x00100c13.
Lemma F_60884 : fetch_word Plain.M.loaded_segments (0x608dc : word) = Some W_60884.
Proof. vm_refl. Qed.
Lemma D_60884 : decode_any W_60884 = Some (OpImm ALU_ADD 24 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60888 : bv 32 := 0x20f78953.
Lemma F_60888 : fetch_word Plain.M.loaded_segments (0x608e0 : word) = Some W_60888.
Proof. vm_refl. Qed.
Lemma D_60888 : decode_any W_60888 = Some (Fsgnj F_SGNJ FMT_S 18 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6088c : bv 32 := 0x001a0a1b.
Lemma F_6088c : fetch_word Plain.M.loaded_segments (0x608e4 : word) = Some W_6088c.
Proof. vm_refl. Qed.
Lemma D_6088c : decode_any W_6088c = Some (OpImm32 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60890 : bv 32 := 0x000c0c93.
Lemma F_60890 : fetch_word Plain.M.loaded_segments (0x608e8 : word) = Some W_60890.
Proof. vm_refl. Qed.
Lemma D_60890 : decode_any W_60890 = Some (OpImm ALU_ADD 25 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60894 : bv 32 := 0x0b490e63.
Lemma F_60894 : fetch_word Plain.M.loaded_segments (0x608ec : word) = Some W_60894.
Proof. vm_refl. Qed.
Lemma D_60894 : decode_any W_60894 = Some (Branch BC_EQ 18 20 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60898 : bv 32 := 0x00810613.
Lemma F_60898 : fetch_word Plain.M.loaded_segments (0x608f0 : word) = Some W_60898.
Proof. vm_refl. Qed.
Lemma D_60898 : decode_any W_60898 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6089c : bv 32 := 0x00040513.
Lemma F_6089c : fetch_word Plain.M.loaded_segments (0x608f4 : word) = Some W_6089c.
Proof. vm_refl. Qed.
Lemma D_6089c : decode_any W_6089c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608a0 : bv 32 := 0x000a0593.
Lemma F_608a0 : fetch_word Plain.M.loaded_segments (0x608f8 : word) = Some W_608a0.
Proof. vm_refl. Qed.
Lemma D_608a0 : decode_any W_608a0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608a4 : bv 32 := 0x4b8000ef.
Lemma F_608a4 : fetch_word Plain.M.loaded_segments (0x608fc : word) = Some W_608a4.
Proof. vm_refl. Qed.
Lemma D_608a4 : decode_any W_608a4 = Some (Jal 1 1208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608a8 : bv 32 := 0x00812787.
Lemma F_608a8 : fetch_word Plain.M.loaded_segments (0x60900 : word) = Some W_608a8.
Proof. vm_refl. Qed.
Lemma D_608a8 : decode_any W_608a8 = Some (FLoad FMT_S 15 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608ac : bv 32 := 0x016c9663.
Lemma F_608ac : fetch_word Plain.M.loaded_segments (0x60904 : word) = Some W_608ac.
Proof. vm_refl. Qed.
Lemma D_608ac : decode_any W_608ac = Some (Branch BC_NE 25 22 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608b0 : bv 32 := 0xa0f91553.
Lemma F_608b0 : fetch_word Plain.M.loaded_segments (0x60908 : word) = Some W_608b0.
Proof. vm_refl. Qed.
Lemma D_608b0 : decode_any W_608b0 = Some (Fcmp F_LT FMT_S 10 18 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608b4 : bv 32 := 0xfc0516e3.
Lemma F_608b4 : fetch_word Plain.M.loaded_segments (0x6090c : word) = Some W_608b4.
Proof. vm_refl. Qed.
Lemma D_608b4 : decode_any W_608b4 = Some (Branch BC_NE 10 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608b8 : bv 32 := 0xfff00c13.
Lemma F_608b8 : fetch_word Plain.M.loaded_segments (0x60910 : word) = Some W_608b8.
Proof. vm_refl. Qed.
Lemma D_608b8 : decode_any W_608b8 = Some (OpImm ALU_ADD 24 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608bc : bv 32 := 0x018c9c63.
Lemma F_608bc : fetch_word Plain.M.loaded_segments (0x60914 : word) = Some W_608bc.
Proof. vm_refl. Qed.
Lemma D_608bc : decode_any W_608bc = Some (Branch BC_NE 25 24 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608c0 : bv 32 := 0xa0979553.
Lemma F_608c0 : fetch_word Plain.M.loaded_segments (0x60918 : word) = Some W_608c0.
Proof. vm_refl. Qed.
Lemma D_608c0 : decode_any W_608c0 = Some (Fcmp F_LT FMT_S 10 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608c4 : bv 32 := 0x00050863.
Lemma F_608c4 : fetch_word Plain.M.loaded_segments (0x6091c : word) = Some W_608c4.
Proof. vm_refl. Qed.
Lemma D_608c4 : decode_any W_608c4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608c8 : bv 32 := 0x000a0a93.
Lemma F_608c8 : fetch_word Plain.M.loaded_segments (0x60920 : word) = Some W_608c8.
Proof. vm_refl. Qed.
Lemma D_608c8 : decode_any W_608c8 = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608cc : bv 32 := 0x20f784d3.
Lemma F_608cc : fetch_word Plain.M.loaded_segments (0x60924 : word) = Some W_608cc.
Proof. vm_refl. Qed.
Lemma D_608cc : decode_any W_608cc = Some (Fsgnj F_SGNJ FMT_S 9 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608d0 : bv 32 := 0xfbdff06f.
Lemma F_608d0 : fetch_word Plain.M.loaded_segments (0x60928 : word) = Some W_608d0.
Proof. vm_refl. Qed.
Lemma D_608d0 : decode_any W_608d0 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608d4 : bv 32 := 0x036c9c63.
Lemma F_608d4 : fetch_word Plain.M.loaded_segments (0x6092c : word) = Some W_608d4.
Proof. vm_refl. Qed.
Lemma D_608d4 : decode_any W_608d4 = Some (Branch BC_NE 25 22 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608d8 : bv 32 := 0x08f977d3.
Lemma F_608d8 : fetch_word Plain.M.loaded_segments (0x60930 : word) = Some W_608d8.
Proof. vm_refl. Qed.
Lemma D_608d8 : decode_any W_608d8 = Some (Fari F_SUB FMT_S 15 18 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608dc : bv 32 := 0xa0f40553.
Lemma F_608dc : fetch_word Plain.M.loaded_segments (0x60934 : word) = Some W_608dc.
Proof. vm_refl. Qed.
Lemma D_608dc : decode_any W_608dc = Some (Fcmp F_LE FMT_S 10 8 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608e0 : bv 32 := 0x06050463.
Lemma F_608e0 : fetch_word Plain.M.loaded_segments (0x60938 : word) = Some W_608e0.
Proof. vm_refl. Qed.
Lemma D_608e0 : decode_any W_608e0 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608e4 : bv 32 := 0xd00af553.
Lemma F_608e4 : fetch_word Plain.M.loaded_segments (0x6093c : word) = Some W_608e4.
Proof. vm_refl. Qed.
Lemma D_608e4 : decode_any W_608e4 = Some (Fcvt FC_S FC_W 10 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608e8 : bv 32 := 0x00048513.
Lemma F_608e8 : fetch_word Plain.M.loaded_segments (0x60940 : word) = Some W_608e8.
Proof. vm_refl. Qed.
Lemma D_608e8 : decode_any W_608e8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608ec : bv 32 := 0x24c000ef.
Lemma F_608ec : fetch_word Plain.M.loaded_segments (0x60944 : word) = Some W_608ec.
Proof. vm_refl. Qed.
Lemma D_608ec : decode_any W_608ec = Some (Jal 1 588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_608f0 : bv 32 := 0x00098863.
Lemma F_608f0 : fetch_word Plain.M.loaded_segments (0x60948 : word) = Some W_608f0.
Proof. vm_refl. Qed.
Lemma D_608f0 : decode_any W_608f0 = Some (Branch BC_EQ 19 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60900 : bv 32 := 0x00812487.
Lemma F_60900 : fetch_word Plain.M.loaded_segments (0x60958 : word) = Some W_60900.
Proof. vm_refl. Qed.
Lemma D_60900 : decode_any W_60900 = Some (FLoad FMT_S 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60904 : bv 32 := 0x000a0a93.
Lemma F_60904 : fetch_word Plain.M.loaded_segments (0x6095c : word) = Some W_60904.
Proof. vm_refl. Qed.
Lemma D_60904 : decode_any W_60904 = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60908 : bv 32 := 0xf85ff06f.
Lemma F_60908 : fetch_word Plain.M.loaded_segments (0x60960 : word) = Some W_60908.
Proof. vm_refl. Qed.
Lemma D_60908 : decode_any W_60908 = Some (Jal 0 2097028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6090c : bv 32 := 0x017c8663.
Lemma F_6090c : fetch_word Plain.M.loaded_segments (0x60964 : word) = Some W_6090c.
Proof. vm_refl. Qed.
Lemma D_6090c : decode_any W_6090c = Some (Branch BC_EQ 25 23 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60918 : bv 32 := 0x0897f7d3.
Lemma F_60918 : fetch_word Plain.M.loaded_segments (0x60970 : word) = Some W_60918.
Proof. vm_refl. Qed.
Lemma D_60918 : decode_any W_60918 = Some (Fari F_SUB FMT_S 15 15 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6091c : bv 32 := 0xa0f40553.
Lemma F_6091c : fetch_word Plain.M.loaded_segments (0x60974 : word) = Some W_6091c.
Proof. vm_refl. Qed.
Lemma D_6091c : decode_any W_6091c = Some (Fcmp F_LE FMT_S 10 8 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60920 : bv 32 := 0xf60506e3.
Lemma F_60920 : fetch_word Plain.M.loaded_segments (0x60978 : word) = Some W_60920.
Proof. vm_refl. Qed.
Lemma D_60920 : decode_any W_60920 = Some (Branch BC_EQ 10 0 8044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60924 : bv 32 := 0xd00af553.
Lemma F_60924 : fetch_word Plain.M.loaded_segments (0x6097c : word) = Some W_60924.
Proof. vm_refl. Qed.
Lemma D_60924 : decode_any W_60924 = Some (Fcvt FC_S FC_W 10 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60928 : bv 32 := 0x00048513.
Lemma F_60928 : fetch_word Plain.M.loaded_segments (0x60980 : word) = Some W_60928.
Proof. vm_refl. Qed.
Lemma D_60928 : decode_any W_60928 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6092c : bv 32 := 0x20c000ef.
Lemma F_6092c : fetch_word Plain.M.loaded_segments (0x60984 : word) = Some W_6092c.
Proof. vm_refl. Qed.
Lemma D_6092c : decode_any W_6092c = Some (Jal 1 524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60930 : bv 32 := 0x00098863.
Lemma F_60930 : fetch_word Plain.M.loaded_segments (0x60988 : word) = Some W_60930.
Proof. vm_refl. Qed.
Lemma D_60930 : decode_any W_60930 = Some (Branch BC_EQ 19 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60940 : bv 32 := 0x00812907.
Lemma F_60940 : fetch_word Plain.M.loaded_segments (0x60998 : word) = Some W_60940.
Proof. vm_refl. Qed.
Lemma D_60940 : decode_any W_60940 = Some (FLoad FMT_S 18 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60944 : bv 32 := 0x000a0a93.
Lemma F_60944 : fetch_word Plain.M.loaded_segments (0x6099c : word) = Some W_60944.
Proof. vm_refl. Qed.
Lemma D_60944 : decode_any W_60944 = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60948 : bv 32 := 0x00100c13.
Lemma F_60948 : fetch_word Plain.M.loaded_segments (0x609a0 : word) = Some W_60948.
Proof. vm_refl. Qed.
Lemma D_60948 : decode_any W_60948 = Some (OpImm ALU_ADD 24 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6094c : bv 32 := 0xf41ff06f.
Lemma F_6094c : fetch_word Plain.M.loaded_segments (0x609a4 : word) = Some W_6094c.
Proof. vm_refl. Qed.
Lemma D_6094c : decode_any W_6094c = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60950 : bv 32 := 0x00048513.
Lemma F_60950 : fetch_word Plain.M.loaded_segments (0x609a8 : word) = Some W_60950.
Proof. vm_refl. Qed.
Lemma D_60950 : decode_any W_60950 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60954 : bv 32 := 0x07813083.
Lemma F_60954 : fetch_word Plain.M.loaded_segments (0x609ac : word) = Some W_60954.
Proof. vm_refl. Qed.
Lemma D_60954 : decode_any W_60954 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60958 : bv 32 := 0x07013403.
Lemma F_60958 : fetch_word Plain.M.loaded_segments (0x609b0 : word) = Some W_60958.
Proof. vm_refl. Qed.
Lemma D_60958 : decode_any W_60958 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6095c : bv 32 := 0x06813483.
Lemma F_6095c : fetch_word Plain.M.loaded_segments (0x609b4 : word) = Some W_6095c.
Proof. vm_refl. Qed.
Lemma D_6095c : decode_any W_6095c = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60960 : bv 32 := 0x06013903.
Lemma F_60960 : fetch_word Plain.M.loaded_segments (0x609b8 : word) = Some W_60960.
Proof. vm_refl. Qed.
Lemma D_60960 : decode_any W_60960 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60964 : bv 32 := 0x05813983.
Lemma F_60964 : fetch_word Plain.M.loaded_segments (0x609bc : word) = Some W_60964.
Proof. vm_refl. Qed.
Lemma D_60964 : decode_any W_60964 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60968 : bv 32 := 0x05013a03.
Lemma F_60968 : fetch_word Plain.M.loaded_segments (0x609c0 : word) = Some W_60968.
Proof. vm_refl. Qed.
Lemma D_60968 : decode_any W_60968 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6096c : bv 32 := 0x04813a83.
Lemma F_6096c : fetch_word Plain.M.loaded_segments (0x609c4 : word) = Some W_6096c.
Proof. vm_refl. Qed.
Lemma D_6096c : decode_any W_6096c = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60970 : bv 32 := 0x04013b03.
Lemma F_60970 : fetch_word Plain.M.loaded_segments (0x609c8 : word) = Some W_60970.
Proof. vm_refl. Qed.
Lemma D_60970 : decode_any W_60970 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60974 : bv 32 := 0x03813b83.
Lemma F_60974 : fetch_word Plain.M.loaded_segments (0x609cc : word) = Some W_60974.
Proof. vm_refl. Qed.
Lemma D_60974 : decode_any W_60974 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60978 : bv 32 := 0x03013c03.
Lemma F_60978 : fetch_word Plain.M.loaded_segments (0x609d0 : word) = Some W_60978.
Proof. vm_refl. Qed.
Lemma D_60978 : decode_any W_60978 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6097c : bv 32 := 0x02813c83.
Lemma F_6097c : fetch_word Plain.M.loaded_segments (0x609d4 : word) = Some W_6097c.
Proof. vm_refl. Qed.
Lemma D_6097c : decode_any W_6097c = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60980 : bv 32 := 0x02013407.
Lemma F_60980 : fetch_word Plain.M.loaded_segments (0x609d8 : word) = Some W_60980.
Proof. vm_refl. Qed.
Lemma D_60980 : decode_any W_60980 = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60984 : bv 32 := 0x01813487.
Lemma F_60984 : fetch_word Plain.M.loaded_segments (0x609dc : word) = Some W_60984.
Proof. vm_refl. Qed.
Lemma D_60984 : decode_any W_60984 = Some (FLoad FMT_D 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60988 : bv 32 := 0x01013907.
Lemma F_60988 : fetch_word Plain.M.loaded_segments (0x609e0 : word) = Some W_60988.
Proof. vm_refl. Qed.
Lemma D_60988 : decode_any W_60988 = Some (FLoad FMT_D 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6098c : bv 32 := 0x08010113.
Lemma F_6098c : fetch_word Plain.M.loaded_segments (0x609e4 : word) = Some W_6098c.
Proof. vm_refl. Qed.
Lemma D_6098c : decode_any W_6098c = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60990 : bv 32 := 0x00008067.
Lemma F_60990 : fetch_word Plain.M.loaded_segments (0x609e8 : word) = Some W_60990.
Proof. vm_refl. Qed.
Lemma D_60990 : decode_any W_60990 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c24 : bv 32 := 0x00050663.
Lemma F_60c24 : fetch_word Plain.M.loaded_segments (0x60c7c : word) = Some W_60c24.
Proof. vm_refl. Qed.
Lemma D_60c24 : decode_any W_60c24 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c28 : bv 32 := 0x00452503.
Lemma F_60c28 : fetch_word Plain.M.loaded_segments (0x60c80 : word) = Some W_60c28.
Proof. vm_refl. Qed.
Lemma D_60c28 : decode_any W_60c28 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60c2c : bv 32 := 0x00008067.
Lemma F_60c2c : fetch_word Plain.M.loaded_segments (0x60c84 : word) = Some W_60c2c.
Proof. vm_refl. Qed.
Lemma D_60c2c : decode_any W_60c2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d5c : bv 32 := 0x02060c63.
Lemma F_60d5c : fetch_word Plain.M.loaded_segments (0x60db4 : word) = Some W_60d5c.
Proof. vm_refl. Qed.
Lemma D_60d5c : decode_any W_60d5c = Some (Branch BC_EQ 12 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d60 : bv 32 := 0x00062023.
Lemma F_60d60 : fetch_word Plain.M.loaded_segments (0x60db8 : word) = Some W_60d60.
Proof. vm_refl. Qed.
Lemma D_60d60 : decode_any W_60d60 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d64 : bv 32 := 0x08050463.
Lemma F_60d64 : fetch_word Plain.M.loaded_segments (0x60dbc : word) = Some W_60d64.
Proof. vm_refl. Qed.
Lemma D_60d64 : decode_any W_60d64 = Some (Branch BC_EQ 10 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d68 : bv 32 := 0x0405cc63.
Lemma F_60d68 : fetch_word Plain.M.loaded_segments (0x60dc0 : word) = Some W_60d68.
Proof. vm_refl. Qed.
Lemma D_60d68 : decode_any W_60d68 = Some (Branch BC_LT 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d6c : bv 32 := 0x00452683.
Lemma F_60d6c : fetch_word Plain.M.loaded_segments (0x60dc4 : word) = Some W_60d6c.
Proof. vm_refl. Qed.
Lemma D_60d6c : decode_any W_60d6c = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d70 : bv 32 := 0x04d5d863.
Lemma F_60d70 : fetch_word Plain.M.loaded_segments (0x60dc8 : word) = Some W_60d70.
Proof. vm_refl. Qed.
Lemma D_60d70 : decode_any W_60d70 = Some (Branch BC_GE 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d74 : bv 32 := 0x00050693.
Lemma F_60d74 : fetch_word Plain.M.loaded_segments (0x60dcc : word) = Some W_60d74.
Proof. vm_refl. Qed.
Lemma D_60d74 : decode_any W_60d74 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d78 : bv 32 := 0x00000513.
Lemma F_60d78 : fetch_word Plain.M.loaded_segments (0x60dd0 : word) = Some W_60d78.
Proof. vm_refl. Qed.
Lemma D_60d78 : decode_any W_60d78 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d7c : bv 32 := 0x0186b683.
Lemma F_60d7c : fetch_word Plain.M.loaded_segments (0x60dd4 : word) = Some W_60d7c.
Proof. vm_refl. Qed.
Lemma D_60d7c : decode_any W_60d7c = Some (Load SZ8 true 13 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d80 : bv 32 := 0x00259593.
Lemma F_60d80 : fetch_word Plain.M.loaded_segments (0x60dd8 : word) = Some W_60d80.
Proof. vm_refl. Qed.
Lemma D_60d80 : decode_any W_60d80 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d84 : bv 32 := 0x00b685b3.
Lemma F_60d84 : fetch_word Plain.M.loaded_segments (0x60ddc : word) = Some W_60d84.
Proof. vm_refl. Qed.
Lemma D_60d84 : decode_any W_60d84 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d88 : bv 32 := 0x0005a787.
Lemma F_60d88 : fetch_word Plain.M.loaded_segments (0x60de0 : word) = Some W_60d88.
Proof. vm_refl. Qed.
Lemma D_60d88 : decode_any W_60d88 = Some (FLoad FMT_S 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d8c : bv 32 := 0x00f62027.
Lemma F_60d8c : fetch_word Plain.M.loaded_segments (0x60de4 : word) = Some W_60d8c.
Proof. vm_refl. Qed.
Lemma D_60d8c : decode_any W_60d8c = Some (FStore FMT_S 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60d90 : bv 32 := 0x00008067.
Lemma F_60d90 : fetch_word Plain.M.loaded_segments (0x60de8 : word) = Some W_60d90.
Proof. vm_refl. Qed.
Lemma D_60d90 : decode_any W_60d90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e20 : bv 32 := 0x06060463.
Lemma F_60e20 : fetch_word Plain.M.loaded_segments (0x60e78 : word) = Some W_60e20.
Proof. vm_refl. Qed.
Lemma D_60e20 : decode_any W_60e20 = Some (Branch BC_EQ 12 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e24 : bv 32 := 0x00062023.
Lemma F_60e24 : fetch_word Plain.M.loaded_segments (0x60e7c : word) = Some W_60e24.
Proof. vm_refl. Qed.
Lemma D_60e24 : decode_any W_60e24 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e28 : bv 32 := 0x0a050c63.
Lemma F_60e28 : fetch_word Plain.M.loaded_segments (0x60e80 : word) = Some W_60e28.
Proof. vm_refl. Qed.
Lemma D_60e28 : decode_any W_60e28 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e2c : bv 32 := 0x0805c463.
Lemma F_60e2c : fetch_word Plain.M.loaded_segments (0x60e84 : word) = Some W_60e2c.
Proof. vm_refl. Qed.
Lemma D_60e2c : decode_any W_60e2c = Some (Branch BC_LT 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e30 : bv 32 := 0x00452683.
Lemma F_60e30 : fetch_word Plain.M.loaded_segments (0x60e88 : word) = Some W_60e30.
Proof. vm_refl. Qed.
Lemma D_60e30 : decode_any W_60e30 = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e34 : bv 32 := 0x08d5d063.
Lemma F_60e34 : fetch_word Plain.M.loaded_segments (0x60e8c : word) = Some W_60e34.
Proof. vm_refl. Qed.
Lemma D_60e34 : decode_any W_60e34 = Some (Branch BC_GE 11 13 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e38 : bv 32 := 0x00050693.
Lemma F_60e38 : fetch_word Plain.M.loaded_segments (0x60e90 : word) = Some W_60e38.
Proof. vm_refl. Qed.
Lemma D_60e38 : decode_any W_60e38 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e3c : bv 32 := 0x00000513.
Lemma F_60e3c : fetch_word Plain.M.loaded_segments (0x60e94 : word) = Some W_60e3c.
Proof. vm_refl. Qed.
Lemma D_60e3c : decode_any W_60e3c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e40 : bv 32 := 0x0186b683.
Lemma F_60e40 : fetch_word Plain.M.loaded_segments (0x60e98 : word) = Some W_60e40.
Proof. vm_refl. Qed.
Lemma D_60e40 : decode_any W_60e40 = Some (Load SZ8 true 13 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e44 : bv 32 := 0x00259593.
Lemma F_60e44 : fetch_word Plain.M.loaded_segments (0x60e9c : word) = Some W_60e44.
Proof. vm_refl. Qed.
Lemma D_60e44 : decode_any W_60e44 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e48 : bv 32 := 0x00b685b3.
Lemma F_60e48 : fetch_word Plain.M.loaded_segments (0x60ea0 : word) = Some W_60e48.
Proof. vm_refl. Qed.
Lemma D_60e48 : decode_any W_60e48 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e4c : bv 32 := 0x0005a787.
Lemma F_60e4c : fetch_word Plain.M.loaded_segments (0x60ea4 : word) = Some W_60e4c.
Proof. vm_refl. Qed.
Lemma D_60e4c : decode_any W_60e4c = Some (FLoad FMT_S 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e50 : bv 32 := 0xf0000753.
Lemma F_60e50 : fetch_word Plain.M.loaded_segments (0x60ea8 : word) = Some W_60e50.
Proof. vm_refl. Qed.
Lemma D_60e50 : decode_any W_60e50 = Some (Fmv FMV_F_X FMT_S 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e54 : bv 32 := 0xfffbb597.
Lemma F_60e54 : fetch_word Plain.M.loaded_segments (0x60eac : word) = Some W_60e54.
Proof. vm_refl. Qed.
Lemma D_60e54 : decode_any W_60e54 = Some (Auipc 11 1048507, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e58 : bv 32 := 0x30c58593.
Lemma F_60e58 : fetch_word Plain.M.loaded_segments (0x60eb0 : word) = Some W_60e58.
Proof. vm_refl. Qed.
Lemma D_60e58 : decode_any W_60e58 = Some (OpImm ALU_ADD 11 11 780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e5c : bv 32 := 0xa0e796d3.
Lemma F_60e5c : fetch_word Plain.M.loaded_segments (0x60eb4 : word) = Some W_60e5c.
Proof. vm_refl. Qed.
Lemma D_60e5c : decode_any W_60e5c = Some (Fcmp F_LT FMT_S 13 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e60 : bv 32 := 0x00369693.
Lemma F_60e60 : fetch_word Plain.M.loaded_segments (0x60eb8 : word) = Some W_60e60.
Proof. vm_refl. Qed.
Lemma D_60e60 : decode_any W_60e60 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e64 : bv 32 := 0x00d585b3.
Lemma F_60e64 : fetch_word Plain.M.loaded_segments (0x60ebc : word) = Some W_60e64.
Proof. vm_refl. Qed.
Lemma D_60e64 : decode_any W_60e64 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e68 : bv 32 := 0x0005b707.
Lemma F_60e68 : fetch_word Plain.M.loaded_segments (0x60ec0 : word) = Some W_60e68.
Proof. vm_refl. Qed.
Lemma D_60e68 : decode_any W_60e68 = Some (FLoad FMT_D 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e6c : bv 32 := 0xfffbb597.
Lemma F_60e6c : fetch_word Plain.M.loaded_segments (0x60ec4 : word) = Some W_60e6c.
Proof. vm_refl. Qed.
Lemma D_60e6c : decode_any W_60e6c = Some (Auipc 11 1048507, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e70 : bv 32 := 0x5345b687.
Lemma F_60e70 : fetch_word Plain.M.loaded_segments (0x60ec8 : word) = Some W_60e70.
Proof. vm_refl. Qed.
Lemma D_60e70 : decode_any W_60e70 = Some (FLoad FMT_D 13 11 1332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e74 : bv 32 := 0x420787d3.
Lemma F_60e74 : fetch_word Plain.M.loaded_segments (0x60ecc : word) = Some W_60e74.
Proof. vm_refl. Qed.
Lemma D_60e74 : decode_any W_60e74 = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e78 : bv 32 := 0x7ad777c3.
Lemma F_60e78 : fetch_word Plain.M.loaded_segments (0x60ed0 : word) = Some W_60e78.
Proof. vm_refl. Qed.
Lemma D_60e78 : decode_any W_60e78 = Some (Fma F_MADD FMT_D 15 14 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e7c : bv 32 := 0xc20795d3.
Lemma F_60e7c : fetch_word Plain.M.loaded_segments (0x60ed4 : word) = Some W_60e7c.
Proof. vm_refl. Qed.
Lemma D_60e7c : decode_any W_60e7c = Some (Fcvt FC_W FC_D 11 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e80 : bv 32 := 0x00b62023.
Lemma F_60e80 : fetch_word Plain.M.loaded_segments (0x60ed8 : word) = Some W_60e80.
Proof. vm_refl. Qed.
Lemma D_60e80 : decode_any W_60e80 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60e84 : bv 32 := 0x00008067.
Lemma F_60e84 : fetch_word Plain.M.loaded_segments (0x60edc : word) = Some W_60e84.
Proof. vm_refl. Qed.
Lemma D_60e84 : decode_any W_60e84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63264 : bv 32 := 0x00050663.
Lemma F_63264 : fetch_word Plain.M.loaded_segments (0x632bc : word) = Some W_63264.
Proof. vm_refl. Qed.
Lemma D_63264 : decode_any W_63264 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63268 : bv 32 := 0x00852503.
Lemma F_63268 : fetch_word Plain.M.loaded_segments (0x632c0 : word) = Some W_63268.
Proof. vm_refl. Qed.
Lemma D_63268 : decode_any W_63268 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6326c : bv 32 := 0x00008067.
Lemma F_6326c : fetch_word Plain.M.loaded_segments (0x632c4 : word) = Some W_6326c.
Proof. vm_refl. Qed.
Lemma D_6326c : decode_any W_6326c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_728dc : bv 32 := 0x0fc0006f.
Lemma F_728dc : fetch_word Plain.M.loaded_segments (0x72934 : word) = Some W_728dc.
Proof. vm_refl. Qed.
Lemma D_728dc : decode_any W_728dc = Some (Jal 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a34 : bv 32 := 0xf9010113.
Lemma F_77a34 : fetch_word Plain.M.loaded_segments (0x77a8c : word) = Some W_77a34.
Proof. vm_refl. Qed.
Lemma D_77a34 : decode_any W_77a34 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a38 : bv 32 := 0x06113423.
Lemma F_77a38 : fetch_word Plain.M.loaded_segments (0x77a90 : word) = Some W_77a38.
Proof. vm_refl. Qed.
Lemma D_77a38 : decode_any W_77a38 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a3c : bv 32 := 0x06813023.
Lemma F_77a3c : fetch_word Plain.M.loaded_segments (0x77a94 : word) = Some W_77a3c.
Proof. vm_refl. Qed.
Lemma D_77a3c : decode_any W_77a3c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a40 : bv 32 := 0x04913c23.
Lemma F_77a40 : fetch_word Plain.M.loaded_segments (0x77a98 : word) = Some W_77a40.
Proof. vm_refl. Qed.
Lemma D_77a40 : decode_any W_77a40 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a44 : bv 32 := 0x05213823.
Lemma F_77a44 : fetch_word Plain.M.loaded_segments (0x77a9c : word) = Some W_77a44.
Proof. vm_refl. Qed.
Lemma D_77a44 : decode_any W_77a44 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a48 : bv 32 := 0x05313423.
Lemma F_77a48 : fetch_word Plain.M.loaded_segments (0x77aa0 : word) = Some W_77a48.
Proof. vm_refl. Qed.
Lemma D_77a48 : decode_any W_77a48 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a4c : bv 32 := 0x05413023.
Lemma F_77a4c : fetch_word Plain.M.loaded_segments (0x77aa4 : word) = Some W_77a4c.
Proof. vm_refl. Qed.
Lemma D_77a4c : decode_any W_77a4c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a50 : bv 32 := 0x03513c23.
Lemma F_77a50 : fetch_word Plain.M.loaded_segments (0x77aa8 : word) = Some W_77a50.
Proof. vm_refl. Qed.
Lemma D_77a50 : decode_any W_77a50 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a54 : bv 32 := 0x03613823.
Lemma F_77a54 : fetch_word Plain.M.loaded_segments (0x77aac : word) = Some W_77a54.
Proof. vm_refl. Qed.
Lemma D_77a54 : decode_any W_77a54 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a58 : bv 32 := 0x03713423.
Lemma F_77a58 : fetch_word Plain.M.loaded_segments (0x77ab0 : word) = Some W_77a58.
Proof. vm_refl. Qed.
Lemma D_77a58 : decode_any W_77a58 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a5c : bv 32 := 0x03813023.
Lemma F_77a5c : fetch_word Plain.M.loaded_segments (0x77ab4 : word) = Some W_77a5c.
Proof. vm_refl. Qed.
Lemma D_77a5c : decode_any W_77a5c = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a60 : bv 32 := 0x00088a93.
Lemma F_77a60 : fetch_word Plain.M.loaded_segments (0x77ab8 : word) = Some W_77a60.
Proof. vm_refl. Qed.
Lemma D_77a60 : decode_any W_77a60 = Some (OpImm ALU_ADD 21 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a64 : bv 32 := 0x00080413.
Lemma F_77a64 : fetch_word Plain.M.loaded_segments (0x77abc : word) = Some W_77a64.
Proof. vm_refl. Qed.
Lemma D_77a64 : decode_any W_77a64 = Some (OpImm ALU_ADD 8 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a68 : bv 32 := 0x00078913.
Lemma F_77a68 : fetch_word Plain.M.loaded_segments (0x77ac0 : word) = Some W_77a68.
Proof. vm_refl. Qed.
Lemma D_77a68 : decode_any W_77a68 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a6c : bv 32 := 0x00070993.
Lemma F_77a6c : fetch_word Plain.M.loaded_segments (0x77ac4 : word) = Some W_77a6c.
Proof. vm_refl. Qed.
Lemma D_77a6c : decode_any W_77a6c = Some (OpImm ALU_ADD 19 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a70 : bv 32 := 0x00068493.
Lemma F_77a70 : fetch_word Plain.M.loaded_segments (0x77ac8 : word) = Some W_77a70.
Proof. vm_refl. Qed.
Lemma D_77a70 : decode_any W_77a70 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a74 : bv 32 := 0x00060a13.
Lemma F_77a74 : fetch_word Plain.M.loaded_segments (0x77acc : word) = Some W_77a74.
Proof. vm_refl. Qed.
Lemma D_77a74 : decode_any W_77a74 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a78 : bv 32 := 0x00058b13.
Lemma F_77a78 : fetch_word Plain.M.loaded_segments (0x77ad0 : word) = Some W_77a78.
Proof. vm_refl. Qed.
Lemma D_77a78 : decode_any W_77a78 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a7c : bv 32 := 0x00050b93.
Lemma F_77a7c : fetch_word Plain.M.loaded_segments (0x77ad4 : word) = Some W_77a7c.
Proof. vm_refl. Qed.
Lemma D_77a7c : decode_any W_77a7c = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a80 : bv 32 := 0x00070463.
Lemma F_77a80 : fetch_word Plain.M.loaded_segments (0x77ad8 : word) = Some W_77a80.
Proof. vm_refl. Qed.
Lemma D_77a80 : decode_any W_77a80 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a84 : bv 32 := 0x0009a023.
Lemma F_77a84 : fetch_word Plain.M.loaded_segments (0x77adc : word) = Some W_77a84.
Proof. vm_refl. Qed.
Lemma D_77a84 : decode_any W_77a84 = Some (Store SZ4 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a88 : bv 32 := 0x00090463.
Lemma F_77a88 : fetch_word Plain.M.loaded_segments (0x77ae0 : word) = Some W_77a88.
Proof. vm_refl. Qed.
Lemma D_77a88 : decode_any W_77a88 = Some (Branch BC_EQ 18 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a8c : bv 32 := 0x00092023.
Lemma F_77a8c : fetch_word Plain.M.loaded_segments (0x77ae4 : word) = Some W_77a8c.
Proof. vm_refl. Qed.
Lemma D_77a8c : decode_any W_77a8c = Some (Store SZ4 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a90 : bv 32 := 0x0129e533.
Lemma F_77a90 : fetch_word Plain.M.loaded_segments (0x77ae8 : word) = Some W_77a90.
Proof. vm_refl. Qed.
Lemma D_77a90 : decode_any W_77a90 = Some (Op ALU_OR 10 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a94 : bv 32 := 0x06040c63.
Lemma F_77a94 : fetch_word Plain.M.loaded_segments (0x77aec : word) = Some W_77a94.
Proof. vm_refl. Qed.
Lemma D_77a94 : decode_any W_77a94 = Some (Branch BC_EQ 8 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a98 : bv 32 := 0x00042023.
Lemma F_77a98 : fetch_word Plain.M.loaded_segments (0x77af0 : word) = Some W_77a98.
Proof. vm_refl. Qed.
Lemma D_77a98 : decode_any W_77a98 = Some (Store SZ4 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77a9c : bv 32 := 0x00a03c33.
Lemma F_77a9c : fetch_word Plain.M.loaded_segments (0x77af4 : word) = Some W_77a9c.
Proof. vm_refl. Qed.
Lemma D_77a9c : decode_any W_77a9c = Some (Op ALU_SLTU 24 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77aa0 : bv 32 := 0x040b8263.
Lemma F_77aa0 : fetch_word Plain.M.loaded_segments (0x77af8 : word) = Some W_77aa0.
Proof. vm_refl. Qed.
Lemma D_77aa0 : decode_any W_77aa0 = Some (Branch BC_EQ 23 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77aa4 : bv 32 := 0x000b8513.
Lemma F_77aa4 : fetch_word Plain.M.loaded_segments (0x77afc : word) = Some W_77aa4.
Proof. vm_refl. Qed.
Lemma D_77aa4 : decode_any W_77aa4 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77aa8 : bv 32 := 0xfbceb0ef.
Lemma F_77aa8 : fetch_word Plain.M.loaded_segments (0x77b00 : word) = Some W_77aa8.
Proof. vm_refl. Qed.
Lemma D_77aa8 : decode_any W_77aa8 = Some (Jal 1 2013116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77aac : bv 32 := 0x00100593.
Lemma F_77aac : fetch_word Plain.M.loaded_segments (0x77b04 : word) = Some W_77aac.
Proof. vm_refl. Qed.
Lemma D_77aac : decode_any W_77aac = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ab0 : bv 32 := 0x02b51a63.
Lemma F_77ab0 : fetch_word Plain.M.loaded_segments (0x77b08 : word) = Some W_77ab0.
Proof. vm_refl. Qed.
Lemma D_77ab0 : decode_any W_77ab0 = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ab4 : bv 32 := 0x00400513.
Lemma F_77ab4 : fetch_word Plain.M.loaded_segments (0x77b0c : word) = Some W_77ab4.
Proof. vm_refl. Qed.
Lemma D_77ab4 : decode_any W_77ab4 = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ab8 : bv 32 := 0x08ab6463.
Lemma F_77ab8 : fetch_word Plain.M.loaded_segments (0x77b10 : word) = Some W_77ab8.
Proof. vm_refl. Qed.
Lemma D_77ab8 : decode_any W_77ab8 = Some (Branch BC_LTU 22 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ae4 : bv 32 := 0x00077517.
Lemma F_77ae4 : fetch_word Plain.M.loaded_segments (0x77b3c : word) = Some W_77ae4.
Proof. vm_refl. Qed.
Lemma D_77ae4 : decode_any W_77ae4 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ae8 : bv 32 := 0xa3453503.
Lemma F_77ae8 : fetch_word Plain.M.loaded_segments (0x77b40 : word) = Some W_77ae8.
Proof. vm_refl. Qed.
Lemma D_77ae8 : decode_any W_77ae8 = Some (Load SZ8 true 10 10 2612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77aec : bv 32 := 0x00052503.
Lemma F_77aec : fetch_word Plain.M.loaded_segments (0x77b44 : word) = Some W_77aec.
Proof. vm_refl. Qed.
Lemma D_77aec : decode_any W_77aec = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77af0 : bv 32 := 0x00500593.
Lemma F_77af0 : fetch_word Plain.M.loaded_segments (0x77b48 : word) = Some W_77af0.
Proof. vm_refl. Qed.
Lemma D_77af0 : decode_any W_77af0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77af4 : bv 32 := 0x20a5c863.
Lemma F_77af4 : fetch_word Plain.M.loaded_segments (0x77b4c : word) = Some W_77af4.
Proof. vm_refl. Qed.
Lemma D_77af4 : decode_any W_77af4 = Some (Branch BC_LT 11 10 528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77af8 : bv 32 := 0xfff9a517.
Lemma F_77af8 : fetch_word Plain.M.loaded_segments (0x77b50 : word) = Some W_77af8.
Proof. vm_refl. Qed.
Lemma D_77af8 : decode_any W_77af8 = Some (Auipc 10 1048474, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77afc : bv 32 := 0xfff9d597.
Lemma F_77afc : fetch_word Plain.M.loaded_segments (0x77b54 : word) = Some W_77afc.
Proof. vm_refl. Qed.
Lemma D_77afc : decode_any W_77afc = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b00 : bv 32 := 0xa8750513.
Lemma F_77b00 : fetch_word Plain.M.loaded_segments (0x77b58 : word) = Some W_77b00.
Proof. vm_refl. Qed.
Lemma D_77b00 : decode_any W_77b00 = Some (OpImm ALU_ADD 10 10 2695, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b04 : bv 32 := 0x77d58593.
Lemma F_77b04 : fetch_word Plain.M.loaded_segments (0x77b5c : word) = Some W_77b04.
Proof. vm_refl. Qed.
Lemma D_77b04 : decode_any W_77b04 = Some (OpImm ALU_ADD 11 11 1917, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b08 : bv 32 := 0x1c80006f.
Lemma F_77b08 : fetch_word Plain.M.loaded_segments (0x77b60 : word) = Some W_77b08.
Proof. vm_refl. Qed.
Lemma D_77b08 : decode_any W_77b08 = Some (Jal 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b40 : bv 32 := 0x11405e63.
Lemma F_77b40 : fetch_word Plain.M.loaded_segments (0x77b98 : word) = Some W_77b40.
Proof. vm_refl. Qed.
Lemma D_77b40 : decode_any W_77b40 = Some (Branch BC_GE 0 20 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b44 : bv 32 := 0x14905063.
Lemma F_77b44 : fetch_word Plain.M.loaded_segments (0x77b9c : word) = Some W_77b44.
Proof. vm_refl. Qed.
Lemma D_77b44 : decode_any W_77b44 = Some (Branch BC_GE 0 9 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b48 : bv 32 := 0x000b8513.
Lemma F_77b48 : fetch_word Plain.M.loaded_segments (0x77ba0 : word) = Some W_77b48.
Proof. vm_refl. Qed.
Lemma D_77b48 : decode_any W_77b48 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b4c : bv 32 := 0x000b0593.
Lemma F_77b4c : fetch_word Plain.M.loaded_segments (0x77ba4 : word) = Some W_77b4c.
Proof. vm_refl. Qed.
Lemma D_77b4c : decode_any W_77b4c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b50 : bv 32 := 0x000a8613.
Lemma F_77b50 : fetch_word Plain.M.loaded_segments (0x77ba8 : word) = Some W_77b50.
Proof. vm_refl. Qed.
Lemma D_77b50 : decode_any W_77b50 = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b54 : bv 32 := 0x1e4000ef.
Lemma F_77b54 : fetch_word Plain.M.loaded_segments (0x77bac : word) = Some W_77b54.
Proof. vm_refl. Qed.
Lemma D_77b54 : decode_any W_77b54 = Some (Jal 1 484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b58 : bv 32 := 0x00a13823.
Lemma F_77b58 : fetch_word Plain.M.loaded_segments (0x77bb0 : word) = Some W_77b58.
Proof. vm_refl. Qed.
Lemma D_77b58 : decode_any W_77b58 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b5c : bv 32 := 0x14050863.
Lemma F_77b5c : fetch_word Plain.M.loaded_segments (0x77bb4 : word) = Some W_77b5c.
Proof. vm_refl. Qed.
Lemma D_77b5c : decode_any W_77b5c = Some (Branch BC_EQ 10 0 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b60 : bv 32 := 0x00050b13.
Lemma F_77b60 : fetch_word Plain.M.loaded_segments (0x77bb8 : word) = Some W_77b60.
Proof. vm_refl. Qed.
Lemma D_77b60 : decode_any W_77b60 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b64 : bv 32 := 0x8c0e90ef.
Lemma F_77b64 : fetch_word Plain.M.loaded_segments (0x77bbc : word) = Some W_77b64.
Proof. vm_refl. Qed.
Lemma D_77b64 : decode_any W_77b64 = Some (Jal 1 2003136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b68 : bv 32 := 0x00100593.
Lemma F_77b68 : fetch_word Plain.M.loaded_segments (0x77bc0 : word) = Some W_77b68.
Proof. vm_refl. Qed.
Lemma D_77b68 : decode_any W_77b68 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b6c : bv 32 := 0x0ea5d063.
Lemma F_77b6c : fetch_word Plain.M.loaded_segments (0x77bc4 : word) = Some W_77b6c.
Proof. vm_refl. Qed.
Lemma D_77b6c : decode_any W_77b6c = Some (Branch BC_GE 11 10 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b70 : bv 32 := 0x00050a93.
Lemma F_77b70 : fetch_word Plain.M.loaded_segments (0x77bc8 : word) = Some W_77b70.
Proof. vm_refl. Qed.
Lemma D_77b70 : decode_any W_77b70 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b74 : bv 32 := 0x080c0e63.
Lemma F_77b74 : fetch_word Plain.M.loaded_segments (0x77bcc : word) = Some W_77b74.
Proof. vm_refl. Qed.
Lemma D_77b74 : decode_any W_77b74 = Some (Branch BC_EQ 24 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b78 : bv 32 := 0x01c10613.
Lemma F_77b78 : fetch_word Plain.M.loaded_segments (0x77bd0 : word) = Some W_77b78.
Proof. vm_refl. Qed.
Lemma D_77b78 : decode_any W_77b78 = Some (OpImm ALU_ADD 12 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b7c : bv 32 := 0x000b0513.
Lemma F_77b7c : fetch_word Plain.M.loaded_segments (0x77bd4 : word) = Some W_77b7c.
Proof. vm_refl. Qed.
Lemma D_77b7c : decode_any W_77b7c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b80 : bv 32 := 0x00000593.
Lemma F_77b80 : fetch_word Plain.M.loaded_segments (0x77bd8 : word) = Some W_77b80.
Proof. vm_refl. Qed.
Lemma D_77b80 : decode_any W_77b80 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b84 : bv 32 := 0xa9ce90ef.
Lemma F_77b84 : fetch_word Plain.M.loaded_segments (0x77bdc : word) = Some W_77b84.
Proof. vm_refl. Qed.
Lemma D_77b84 : decode_any W_77b84 = Some (Jal 1 2003612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b88 : bv 32 := 0x00000b93.
Lemma F_77b88 : fetch_word Plain.M.loaded_segments (0x77be0 : word) = Some W_77b88.
Proof. vm_refl. Qed.
Lemma D_77b88 : decode_any W_77b88 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b8c : bv 32 := 0x00000c13.
Lemma F_77b8c : fetch_word Plain.M.loaded_segments (0x77be4 : word) = Some W_77b8c.
Proof. vm_refl. Qed.
Lemma D_77b8c : decode_any W_77b8c = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b90 : bv 32 := 0x00100b13.
Lemma F_77b90 : fetch_word Plain.M.loaded_segments (0x77be8 : word) = Some W_77b90.
Proof. vm_refl. Qed.
Lemma D_77b90 : decode_any W_77b90 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b94 : bv 32 := 0x01013503.
Lemma F_77b94 : fetch_word Plain.M.loaded_segments (0x77bec : word) = Some W_77b94.
Proof. vm_refl. Qed.
Lemma D_77b94 : decode_any W_77b94 = Some (Load SZ8 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b98 : bv 32 := 0x01810613.
Lemma F_77b98 : fetch_word Plain.M.loaded_segments (0x77bf0 : word) = Some W_77b98.
Proof. vm_refl. Qed.
Lemma D_77b98 : decode_any W_77b98 = Some (OpImm ALU_ADD 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77b9c : bv 32 := 0x000b0593.
Lemma F_77b9c : fetch_word Plain.M.loaded_segments (0x77bf4 : word) = Some W_77b9c.
Proof. vm_refl. Qed.
Lemma D_77b9c : decode_any W_77b9c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ba0 : bv 32 := 0xa80e90ef.
Lemma F_77ba0 : fetch_word Plain.M.loaded_segments (0x77bf8 : word) = Some W_77ba0.
Proof. vm_refl. Qed.
Lemma D_77ba0 : decode_any W_77ba0 = Some (Jal 1 2003584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ba4 : bv 32 := 0x01812503.
Lemma F_77ba4 : fetch_word Plain.M.loaded_segments (0x77bfc : word) = Some W_77ba4.
Proof. vm_refl. Qed.
Lemma D_77ba4 : decode_any W_77ba4 = Some (Load SZ4 true 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ba8 : bv 32 := 0x01c12583.
Lemma F_77ba8 : fetch_word Plain.M.loaded_segments (0x77c00 : word) = Some W_77ba8.
Proof. vm_refl. Qed.
Lemma D_77ba8 : decode_any W_77ba8 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bac : bv 32 := 0x001b0b1b.
Lemma F_77bac : fetch_word Plain.M.loaded_segments (0x77c04 : word) = Some W_77bac.
Proof. vm_refl. Qed.
Lemma D_77bac : decode_any W_77bac = Some (OpImm32 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bb0 : bv 32 := 0x40b505b3.
Lemma F_77bb0 : fetch_word Plain.M.loaded_segments (0x77c08 : word) = Some W_77bb0.
Proof. vm_refl. Qed.
Lemma D_77bb0 : decode_any W_77bb0 = Some (Op ALU_SUB 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bb4 : bv 32 := 0x41f5d61b.
Lemma F_77bb4 : fetch_word Plain.M.loaded_segments (0x77c0c : word) = Some W_77bb4.
Proof. vm_refl. Qed.
Lemma D_77bb4 : decode_any W_77bb4 = Some (ShiftImm32 ALU_SRA 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bb8 : bv 32 := 0x00c5c5b3.
Lemma F_77bb8 : fetch_word Plain.M.loaded_segments (0x77c10 : word) = Some W_77bb8.
Proof. vm_refl. Qed.
Lemma D_77bb8 : decode_any W_77bb8 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bbc : bv 32 := 0x40c585bb.
Lemma F_77bbc : fetch_word Plain.M.loaded_segments (0x77c14 : word) = Some W_77bbc.
Proof. vm_refl. Qed.
Lemma D_77bbc : decode_any W_77bbc = Some (Op32 ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bc0 : bv 32 := 0x0145a633.
Lemma F_77bc0 : fetch_word Plain.M.loaded_segments (0x77c18 : word) = Some W_77bc0.
Proof. vm_refl. Qed.
Lemma D_77bc0 : decode_any W_77bc0 = Some (Op ALU_SLT 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bc4 : bv 32 := 0x00164693.
Lemma F_77bc4 : fetch_word Plain.M.loaded_segments (0x77c1c : word) = Some W_77bc4.
Proof. vm_refl. Qed.
Lemma D_77bc4 : decode_any W_77bc4 = Some (OpImm ALU_XOR 13 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bc8 : bv 32 := 0xfff60613.
Lemma F_77bc8 : fetch_word Plain.M.loaded_segments (0x77c20 : word) = Some W_77bc8.
Proof. vm_refl. Qed.
Lemma D_77bc8 : decode_any W_77bc8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bcc : bv 32 := 0x00dc0c33.
Lemma F_77bcc : fetch_word Plain.M.loaded_segments (0x77c24 : word) = Some W_77bcc.
Proof. vm_refl. Qed.
Lemma D_77bcc : decode_any W_77bcc = Some (Op ALU_ADD 24 24 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bd0 : bv 32 := 0x00b675b3.
Lemma F_77bd0 : fetch_word Plain.M.loaded_segments (0x77c28 : word) = Some W_77bd0.
Proof. vm_refl. Qed.
Lemma D_77bd0 : decode_any W_77bd0 = Some (Op ALU_AND 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bd4 : bv 32 := 0x01758bb3.
Lemma F_77bd4 : fetch_word Plain.M.loaded_segments (0x77c2c : word) = Some W_77bd4.
Proof. vm_refl. Qed.
Lemma D_77bd4 : decode_any W_77bd4 = Some (Op ALU_ADD 23 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bd8 : bv 32 := 0x00a12e23.
Lemma F_77bd8 : fetch_word Plain.M.loaded_segments (0x77c30 : word) = Some W_77bd8.
Proof. vm_refl. Qed.
Lemma D_77bd8 : decode_any W_77bd8 = Some (Store SZ4 2 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bdc : bv 32 := 0xfb6a9ce3.
Lemma F_77bdc : fetch_word Plain.M.loaded_segments (0x77c34 : word) = Some W_77bdc.
Proof. vm_refl. Qed.
Lemma D_77bdc : decode_any W_77bdc = Some (Branch BC_NE 21 22 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77be0 : bv 32 := 0x00098c63.
Lemma F_77be0 : fetch_word Plain.M.loaded_segments (0x77c38 : word) = Some W_77be0.
Proof. vm_refl. Qed.
Lemma D_77be0 : decode_any W_77be0 = Some (Branch BC_EQ 19 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77be4 : bv 32 := 0xd01c77d3.
Lemma F_77be4 : fetch_word Plain.M.loaded_segments (0x77c3c : word) = Some W_77be4.
Proof. vm_refl. Qed.
Lemma D_77be4 : decode_any W_77be4 = Some (Fcvt FC_S FC_WU 15 24 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77be8 : bv 32 := 0xfffa8513.
Lemma F_77be8 : fetch_word Plain.M.loaded_segments (0x77c40 : word) = Some W_77be8.
Proof. vm_refl. Qed.
Lemma D_77be8 : decode_any W_77be8 = Some (OpImm ALU_ADD 10 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bec : bv 32 := 0xd0157753.
Lemma F_77bec : fetch_word Plain.M.loaded_segments (0x77c44 : word) = Some W_77bec.
Proof. vm_refl. Qed.
Lemma D_77bec : decode_any W_77bec = Some (Fcvt FC_S FC_WU 14 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bf0 : bv 32 := 0x18e7f7d3.
Lemma F_77bf0 : fetch_word Plain.M.loaded_segments (0x77c48 : word) = Some W_77bf0.
Proof. vm_refl. Qed.
Lemma D_77bf0 : decode_any W_77bf0 = Some (Fari F_DIV FMT_S 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bf4 : bv 32 := 0x00f9a027.
Lemma F_77bf4 : fetch_word Plain.M.loaded_segments (0x77c4c : word) = Some W_77bf4.
Proof. vm_refl. Qed.
Lemma D_77bf4 : decode_any W_77bf4 = Some (FStore FMT_S 19 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bf8 : bv 32 := 0x00090c63.
Lemma F_77bf8 : fetch_word Plain.M.loaded_segments (0x77c50 : word) = Some W_77bf8.
Proof. vm_refl. Qed.
Lemma D_77bf8 : decode_any W_77bf8 = Some (Branch BC_EQ 18 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77bfc : bv 32 := 0xd01bf7d3.
Lemma F_77bfc : fetch_word Plain.M.loaded_segments (0x77c54 : word) = Some W_77bfc.
Proof. vm_refl. Qed.
Lemma D_77bfc : decode_any W_77bfc = Some (Fcvt FC_S FC_WU 15 23 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c00 : bv 32 := 0xfffa8513.
Lemma F_77c00 : fetch_word Plain.M.loaded_segments (0x77c58 : word) = Some W_77c00.
Proof. vm_refl. Qed.
Lemma D_77c00 : decode_any W_77c00 = Some (OpImm ALU_ADD 10 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c04 : bv 32 := 0xd0157753.
Lemma F_77c04 : fetch_word Plain.M.loaded_segments (0x77c5c : word) = Some W_77c04.
Proof. vm_refl. Qed.
Lemma D_77c04 : decode_any W_77c04 = Some (Fcvt FC_S FC_WU 14 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c08 : bv 32 := 0x18e7f7d3.
Lemma F_77c08 : fetch_word Plain.M.loaded_segments (0x77c60 : word) = Some W_77c08.
Proof. vm_refl. Qed.
Lemma D_77c08 : decode_any W_77c08 = Some (Fari F_DIV FMT_S 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c0c : bv 32 := 0x00f92027.
Lemma F_77c0c : fetch_word Plain.M.loaded_segments (0x77c64 : word) = Some W_77c0c.
Proof. vm_refl. Qed.
Lemma D_77c0c : decode_any W_77c0c = Some (FStore FMT_S 18 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c10 : bv 32 := 0x02040e63.
Lemma F_77c10 : fetch_word Plain.M.loaded_segments (0x77c68 : word) = Some W_77c10.
Proof. vm_refl. Qed.
Lemma D_77c10 : decode_any W_77c10 = Some (Branch BC_EQ 8 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c14 : bv 32 := 0x01013503.
Lemma F_77c14 : fetch_word Plain.M.loaded_segments (0x77c6c : word) = Some W_77c14.
Proof. vm_refl. Qed.
Lemma D_77c14 : decode_any W_77c14 = Some (Load SZ8 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c18 : bv 32 := 0xd014f553.
Lemma F_77c18 : fetch_word Plain.M.loaded_segments (0x77c70 : word) = Some W_77c18.
Proof. vm_refl. Qed.
Lemma D_77c18 : decode_any W_77c18 = Some (Fcvt FC_S FC_WU 10 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c1c : bv 32 := 0x00000593.
Lemma F_77c1c : fetch_word Plain.M.loaded_segments (0x77c74 : word) = Some W_77c1c.
Proof. vm_refl. Qed.
Lemma D_77c1c : decode_any W_77c1c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c20 : bv 32 := 0xac1e80ef.
Lemma F_77c20 : fetch_word Plain.M.loaded_segments (0x77c78 : word) = Some W_77c20.
Proof. vm_refl. Qed.
Lemma D_77c20 : decode_any W_77c20 = Some (Jal 1 2001600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c24 : bv 32 := 0x00a13423.
Lemma F_77c24 : fetch_word Plain.M.loaded_segments (0x77c7c : word) = Some W_77c24.
Proof. vm_refl. Qed.
Lemma D_77c24 : decode_any W_77c24 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c28 : bv 32 := 0xffde80ef.
Lemma F_77c28 : fetch_word Plain.M.loaded_segments (0x77c80 : word) = Some W_77c28.
Proof. vm_refl. Qed.
Lemma D_77c28 : decode_any W_77c28 = Some (Jal 1 2002940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c2c : bv 32 := 0xfff50513.
Lemma F_77c2c : fetch_word Plain.M.loaded_segments (0x77c84 : word) = Some W_77c2c.
Proof. vm_refl. Qed.
Lemma D_77c2c : decode_any W_77c2c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c30 : bv 32 := 0xfffa8a93.
Lemma F_77c30 : fetch_word Plain.M.loaded_segments (0x77c88 : word) = Some W_77c30.
Proof. vm_refl. Qed.
Lemma D_77c30 : decode_any W_77c30 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c34 : bv 32 := 0xd00577d3.
Lemma F_77c34 : fetch_word Plain.M.loaded_segments (0x77c8c : word) = Some W_77c34.
Proof. vm_refl. Qed.
Lemma D_77c34 : decode_any W_77c34 = Some (Fcvt FC_S FC_W 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c38 : bv 32 := 0xd01af753.
Lemma F_77c38 : fetch_word Plain.M.loaded_segments (0x77c90 : word) = Some W_77c38.
Proof. vm_refl. Qed.
Lemma D_77c38 : decode_any W_77c38 = Some (Fcvt FC_S FC_WU 14 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c3c : bv 32 := 0x18e7f7d3.
Lemma F_77c3c : fetch_word Plain.M.loaded_segments (0x77c94 : word) = Some W_77c3c.
Proof. vm_refl. Qed.
Lemma D_77c3c : decode_any W_77c3c = Some (Fari F_DIV FMT_S 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c40 : bv 32 := 0x00f42027.
Lemma F_77c40 : fetch_word Plain.M.loaded_segments (0x77c98 : word) = Some W_77c40.
Proof. vm_refl. Qed.
Lemma D_77c40 : decode_any W_77c40 = Some (FStore FMT_S 8 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c44 : bv 32 := 0x00810513.
Lemma F_77c44 : fetch_word Plain.M.loaded_segments (0x77c9c : word) = Some W_77c44.
Proof. vm_refl. Qed.
Lemma D_77c44 : decode_any W_77c44 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c48 : bv 32 := 0xe51e80ef.
Lemma F_77c48 : fetch_word Plain.M.loaded_segments (0x77ca0 : word) = Some W_77c48.
Proof. vm_refl. Qed.
Lemma D_77c48 : decode_any W_77c48 = Some (Jal 1 2002512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c4c : bv 32 := 0x01010513.
Lemma F_77c4c : fetch_word Plain.M.loaded_segments (0x77ca4 : word) = Some W_77c4c.
Proof. vm_refl. Qed.
Lemma D_77c4c : decode_any W_77c4c = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c50 : bv 32 := 0xe49e80ef.
Lemma F_77c50 : fetch_word Plain.M.loaded_segments (0x77ca8 : word) = Some W_77c50.
Proof. vm_refl. Qed.
Lemma D_77c50 : decode_any W_77c50 = Some (Jal 1 2002504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c54 : bv 32 := 0x00000513.
Lemma F_77c54 : fetch_word Plain.M.loaded_segments (0x77cac : word) = Some W_77c54.
Proof. vm_refl. Qed.
Lemma D_77c54 : decode_any W_77c54 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77c58 : bv 32 := 0x0b00006f.
Lemma F_77c58 : fetch_word Plain.M.loaded_segments (0x77cb0 : word) = Some W_77c58.
Proof. vm_refl. Qed.
Lemma D_77c58 : decode_any W_77c58 = Some (Jal 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cd0 : bv 32 := 0x00100613.
Lemma F_77cd0 : fetch_word Plain.M.loaded_segments (0x77d28 : word) = Some W_77cd0.
Proof. vm_refl. Qed.
Lemma D_77cd0 : decode_any W_77cd0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cd4 : bv 32 := 0x06813083.
Lemma F_77cd4 : fetch_word Plain.M.loaded_segments (0x77d2c : word) = Some W_77cd4.
Proof. vm_refl. Qed.
Lemma D_77cd4 : decode_any W_77cd4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cd8 : bv 32 := 0x06013403.
Lemma F_77cd8 : fetch_word Plain.M.loaded_segments (0x77d30 : word) = Some W_77cd8.
Proof. vm_refl. Qed.
Lemma D_77cd8 : decode_any W_77cd8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cdc : bv 32 := 0x05813483.
Lemma F_77cdc : fetch_word Plain.M.loaded_segments (0x77d34 : word) = Some W_77cdc.
Proof. vm_refl. Qed.
Lemma D_77cdc : decode_any W_77cdc = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ce0 : bv 32 := 0x05013903.
Lemma F_77ce0 : fetch_word Plain.M.loaded_segments (0x77d38 : word) = Some W_77ce0.
Proof. vm_refl. Qed.
Lemma D_77ce0 : decode_any W_77ce0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ce4 : bv 32 := 0x04813983.
Lemma F_77ce4 : fetch_word Plain.M.loaded_segments (0x77d3c : word) = Some W_77ce4.
Proof. vm_refl. Qed.
Lemma D_77ce4 : decode_any W_77ce4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77ce8 : bv 32 := 0x04013a03.
Lemma F_77ce8 : fetch_word Plain.M.loaded_segments (0x77d40 : word) = Some W_77ce8.
Proof. vm_refl. Qed.
Lemma D_77ce8 : decode_any W_77ce8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cec : bv 32 := 0x03813a83.
Lemma F_77cec : fetch_word Plain.M.loaded_segments (0x77d44 : word) = Some W_77cec.
Proof. vm_refl. Qed.
Lemma D_77cec : decode_any W_77cec = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cf0 : bv 32 := 0x03013b03.
Lemma F_77cf0 : fetch_word Plain.M.loaded_segments (0x77d48 : word) = Some W_77cf0.
Proof. vm_refl. Qed.
Lemma D_77cf0 : decode_any W_77cf0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cf4 : bv 32 := 0x02813b83.
Lemma F_77cf4 : fetch_word Plain.M.loaded_segments (0x77d4c : word) = Some W_77cf4.
Proof. vm_refl. Qed.
Lemma D_77cf4 : decode_any W_77cf4 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cf8 : bv 32 := 0x02013c03.
Lemma F_77cf8 : fetch_word Plain.M.loaded_segments (0x77d50 : word) = Some W_77cf8.
Proof. vm_refl. Qed.
Lemma D_77cf8 : decode_any W_77cf8 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77cfc : bv 32 := 0x07010113.
Lemma F_77cfc : fetch_word Plain.M.loaded_segments (0x77d54 : word) = Some W_77cfc.
Proof. vm_refl. Qed.
Lemma D_77cfc : decode_any W_77cfc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d00 : bv 32 := 0x87ce506f.
Lemma F_77d00 : fetch_word Plain.M.loaded_segments (0x77d58 : word) = Some W_77d00.
Proof. vm_refl. Qed.
Lemma D_77d00 : decode_any W_77d00 = Some (Jal 0 1986684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d08 : bv 32 := 0x06813083.
Lemma F_77d08 : fetch_word Plain.M.loaded_segments (0x77d60 : word) = Some W_77d08.
Proof. vm_refl. Qed.
Lemma D_77d08 : decode_any W_77d08 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d0c : bv 32 := 0x06013403.
Lemma F_77d0c : fetch_word Plain.M.loaded_segments (0x77d64 : word) = Some W_77d0c.
Proof. vm_refl. Qed.
Lemma D_77d0c : decode_any W_77d0c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d10 : bv 32 := 0x05813483.
Lemma F_77d10 : fetch_word Plain.M.loaded_segments (0x77d68 : word) = Some W_77d10.
Proof. vm_refl. Qed.
Lemma D_77d10 : decode_any W_77d10 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d14 : bv 32 := 0x05013903.
Lemma F_77d14 : fetch_word Plain.M.loaded_segments (0x77d6c : word) = Some W_77d14.
Proof. vm_refl. Qed.
Lemma D_77d14 : decode_any W_77d14 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d18 : bv 32 := 0x04813983.
Lemma F_77d18 : fetch_word Plain.M.loaded_segments (0x77d70 : word) = Some W_77d18.
Proof. vm_refl. Qed.
Lemma D_77d18 : decode_any W_77d18 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d1c : bv 32 := 0x04013a03.
Lemma F_77d1c : fetch_word Plain.M.loaded_segments (0x77d74 : word) = Some W_77d1c.
Proof. vm_refl. Qed.
Lemma D_77d1c : decode_any W_77d1c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d20 : bv 32 := 0x03813a83.
Lemma F_77d20 : fetch_word Plain.M.loaded_segments (0x77d78 : word) = Some W_77d20.
Proof. vm_refl. Qed.
Lemma D_77d20 : decode_any W_77d20 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d24 : bv 32 := 0x03013b03.
Lemma F_77d24 : fetch_word Plain.M.loaded_segments (0x77d7c : word) = Some W_77d24.
Proof. vm_refl. Qed.
Lemma D_77d24 : decode_any W_77d24 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d28 : bv 32 := 0x02813b83.
Lemma F_77d28 : fetch_word Plain.M.loaded_segments (0x77d80 : word) = Some W_77d28.
Proof. vm_refl. Qed.
Lemma D_77d28 : decode_any W_77d28 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d2c : bv 32 := 0x02013c03.
Lemma F_77d2c : fetch_word Plain.M.loaded_segments (0x77d84 : word) = Some W_77d2c.
Proof. vm_refl. Qed.
Lemma D_77d2c : decode_any W_77d2c = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d30 : bv 32 := 0x07010113.
Lemma F_77d30 : fetch_word Plain.M.loaded_segments (0x77d88 : word) = Some W_77d30.
Proof. vm_refl. Qed.
Lemma D_77d30 : decode_any W_77d30 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_77d34 : bv 32 := 0x00008067.
Lemma F_77d34 : fetch_word Plain.M.loaded_segments (0x77d8c : word) = Some W_77d34.
Proof. vm_refl. Qed.
Lemma D_77d34 : decode_any W_77d34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

