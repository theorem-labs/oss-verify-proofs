(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n QOTP QLPb QY73 Q72M QvSK Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.Riscv.Instr.
Import Qt8n QOTP.
Import QLPb QY73 Q72M.
Import QvSK.Mq0 Q5o6.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition MV_A : nat := 5.
Definition GV_A : nat := 423.
Definition CTX_A : list scell :=
[ SCi 8;
SCw 8 (EBlob false 25 8 8);
SCw 4 (ELit 1);
SCw 4 (ELit 1);
SCi 8;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4280));
SCw 8 (ELit 97);
SCw 8 (ELit 0);
SCi 8;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4096));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4096));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 8192));
SCi 16;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4120));
SCi 96;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4160));
SCi 24;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4200));
SCi 24;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4240));
SCi 208;
SCw 8 (ELit 10);
SCi 96;
SCw 8 (ELit 2);
SCi 24;
SCw 8 (ELit 2);
SCi 24;
SCw 8 (ELit 2);
SCi 256;
SCw 1 (ELit 1);
SCi 7;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 8192)) ].
Definition NL_A : list scell :=
[ SCi 1 ].
Definition PGSZ_A : list scell :=
[ SCw 8 (ELit 4096) ].
Definition GOTSSP_A : list scell :=
[ SCi 8 ].
Definition SSPG_A : list scell :=
[ SCw 8 (EVar 45) ].
Definition VML_A : list scell :=
[ SCi 4 ].
Definition META_A : list scell :=
[ SCw 8 (EBlob false 25 8 8);
SCz 8;
SCw 4 (ELit 101);
SCz 4;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4120));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4120));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 48));
SCw 4 (ELit 1022);
SCw 4 (ELit 0);
SCw 8 (ELit 169);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4160));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4160));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 32));
SCw 4 (ELit 2);
SCw 4 (ELit 0);
SCw 8 (ELit 993);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4200));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4200));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 16));
SCw 4 (ELit 2);
SCw 4 (ELit 0);
SCw 8 (ELit 1249);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4240));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4240));
SCw 8 (EMd Instr.M_MUL (ELit 4096) (EVar 423));
SCw 4 (ELit 2);
SCw 4 (ELit 0);
SCw 8 (ELit 5601);
SCz 3912 ].
Definition GRP_A : list scell :=
[ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4240));
SCw 1 (ELit 1);
SCz 4;
SCw 1 (ELit 192);
SCw 2 (ELit 0);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4200));
SCw 1 (ELit 1);
SCz 3;
SCw 1 (ELit 0);
SCw 1 (ELit 192);
SCw 2 (ELit 0);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4160));
SCw 1 (ELit 1);
SCz 3;
SCw 1 (ELit 0);
SCw 1 (ELit 192);
SCw 2 (ELit 0);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4120));
SCw 1 (ELit 9);
SCz 3;
SCw 1 (ELit 0);
SCw 1 (ELit 128);
SCw 2 (ELit 0);
SCw 8 (ELit 416428);
SCw 8 (ELit 416592);
SCw 8 (ELit 416688);
SCw 8 (ELit 0);
SCw 8 (ELit 0);
SCw 1 (ELit 0);
SCz 3;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 495;
SCw 1 (ELit 0);
SCz 1007;
SCw 1 (ELit 0);
SCz 2051 ].

Definition MV_B : nat := 423.
Definition GV_B : nat := 424.
Definition CTX_B : list scell :=
[ SCi 8;
SCw 8 (EBlob false 25 8 8);
SCw 4 (ELit 1);
SCw 4 (ELit 1);
SCi 8;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4280));
SCw 8 (ELit 97);
SCw 8 (ELit 0);
SCw 8 (ELit 1);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4096));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4096));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 8192));
SCi 16;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4120));
SCi 96;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4160));
SCi 24;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4200));
SCi 24;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4240));
SCi 208;
SCw 8 (ELit 10);
SCi 96;
SCw 8 (ELit 2);
SCi 24;
SCw 8 (ELit 2);
SCi 24;
SCw 8 (ELit 2);
SCi 256;
SCw 1 (ELit 1);
SCi 7;
SCw 8 (ELit 18446744073709551615) ].
Definition NL_B : list scell :=
[ SCi 1 ].
Definition PGSZ_B : list scell :=
[ SCw 8 (ELit 4096) ].
Definition GOTSSP_B : list scell :=
[ SCi 8 ].
Definition SSPG_B : list scell :=
[ SCw 8 (EVar 45) ].
Definition VML_B : list scell :=
[ SCi 4 ].
Definition META_B : list scell :=
[ SCw 8 (EBlob false 25 8 8);
SCz 8;
SCw 4 (ELit 101);
SCz 4;
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4120));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4120));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 424)) (ELit 48));
SCw 4 (ELit 1022);
SCw 4 (ELit 0);
SCw 8 (ELit 169);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4160));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4160));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 424)) (ELit 32));
SCw 4 (ELit 2);
SCw 4 (ELit 0);
SCw 8 (ELit 993);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4200));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4200));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 424)) (ELit 16));
SCw 4 (ELit 2);
SCw 4 (ELit 0);
SCw 8 (ELit 1249);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4240));
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4240));
SCw 8 (EMd Instr.M_MUL (ELit 4096) (EVar 424));
SCw 4 (ELit 2);
SCw 4 (ELit 0);
SCw 8 (ELit 5601);
SCz 3912 ].
Definition GRP_B : list scell :=
[ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4240));
SCw 1 (ELit 1);
SCz 4;
SCw 1 (ELit 192);
SCw 2 (ELit 0);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4200));
SCw 1 (ELit 1);
SCz 3;
SCw 1 (ELit 0);
SCw 1 (ELit 192);
SCw 2 (ELit 0);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4160));
SCw 1 (ELit 1);
SCz 3;
SCw 1 (ELit 0);
SCw 1 (ELit 192);
SCw 2 (ELit 0);
SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4120));
SCw 1 (ELit 9);
SCz 3;
SCw 1 (ELit 0);
SCw 1 (ELit 128);
SCw 2 (ELit 0);
SCw 8 (ELit 416428);
SCw 8 (ELit 416592);
SCw 8 (ELit 416688);
SCw 8 (ELit 0);
SCw 8 (ELit 0);
SCw 1 (ELit 0);
SCz 3;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 47;
SCw 1 (ELit 0);
SCz 495;
SCw 1 (ELit 0);
SCz 1007;
SCw 1 (ELit 0);
SCz 2051 ].

Lemma CTX_HS2sA_1_ok : cells_check JO6SEGS (kn_view HS2sA_1) (ELit 0) 6566368 CTX_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma CTX_HS2sA_2_ok : cells_check JO6SEGS (kn_view HS2sA_2) (ELit 0) 6566368 CTX_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma NL_HS2sA_1_ok : cells_check JO6SEGS (kn_view HS2sA_1) (ELit 0) 6566131 NL_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma NL_HS2sA_2_ok : cells_check JO6SEGS (kn_view HS2sA_2) (ELit 0) 6566131 NL_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PGSZ_HS2sA_1_ok : cells_check JO6SEGS (kn_view HS2sA_1) (ELit 0) 6566176 PGSZ_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PGSZ_HS2sA_2_ok : cells_check JO6SEGS (kn_view HS2sA_2) (ELit 0) 6566176 PGSZ_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GOTSSP_HS2sA_1_ok : cells_check JO6SEGS (kn_view HS2sA_1) (ELit 0) 945024 GOTSSP_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GOTSSP_HS2sA_2_ok : cells_check JO6SEGS (kn_view HS2sA_2) (ELit 0) 945024 GOTSSP_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SSPG_HS2sA_1_ok : cells_check JO6SEGS (kn_view HS2sA_1) (ELit 0) 6565536 SSPG_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SSPG_HS2sA_2_ok : cells_check JO6SEGS (kn_view HS2sA_2) (ELit 0) 6565536 SSPG_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma VML_HS2sA_1_ok : cells_check JO6SEGS (kn_view HS2sA_1) (ELit 0) 6571768 VML_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma VML_HS2sA_2_ok : cells_check JO6SEGS (kn_view HS2sA_2) (ELit 0) 6571768 VML_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma META_HS2sA_1_ok : cells_check JO6SEGS (kn_view HS2sA_1) (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4096 META_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma META_HS2sA_2_ok : cells_check JO6SEGS (kn_view HS2sA_2) (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4096 META_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GRP_HS2sA_1_ok : cells_check JO6SEGS (kn_view HS2sA_1) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0 GRP_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GRP_HS2sA_2_ok : cells_check JO6SEGS (kn_view HS2sA_2) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0 GRP_A = true.
Proof. vm_compute. reflexivity. Qed.
Lemma METAW_HS2sA_1_ok : wr_check (kn_view HS2sA_1) (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4096 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GRPW_HS2sA_1_ok : wr_check (kn_view HS2sA_1) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma METAW_HS2sA_2_ok : wr_check (kn_view HS2sA_2) (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4096 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GRPW_HS2sA_2_ok : wr_check (kn_view HS2sA_2) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma CTX_HS2sB_3_ok : cells_check JO6SEGS (kn_view HS2sB_3) (ELit 0) 6566368 CTX_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma CTX_HS2sB_4_ok : cells_check JO6SEGS (kn_view HS2sB_4) (ELit 0) 6566368 CTX_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma NL_HS2sB_3_ok : cells_check JO6SEGS (kn_view HS2sB_3) (ELit 0) 6566131 NL_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma NL_HS2sB_4_ok : cells_check JO6SEGS (kn_view HS2sB_4) (ELit 0) 6566131 NL_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PGSZ_HS2sB_3_ok : cells_check JO6SEGS (kn_view HS2sB_3) (ELit 0) 6566176 PGSZ_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PGSZ_HS2sB_4_ok : cells_check JO6SEGS (kn_view HS2sB_4) (ELit 0) 6566176 PGSZ_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GOTSSP_HS2sB_3_ok : cells_check JO6SEGS (kn_view HS2sB_3) (ELit 0) 945024 GOTSSP_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GOTSSP_HS2sB_4_ok : cells_check JO6SEGS (kn_view HS2sB_4) (ELit 0) 945024 GOTSSP_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SSPG_HS2sB_3_ok : cells_check JO6SEGS (kn_view HS2sB_3) (ELit 0) 6565536 SSPG_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma SSPG_HS2sB_4_ok : cells_check JO6SEGS (kn_view HS2sB_4) (ELit 0) 6565536 SSPG_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma VML_HS2sB_3_ok : cells_check JO6SEGS (kn_view HS2sB_3) (ELit 0) 6571768 VML_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma VML_HS2sB_4_ok : cells_check JO6SEGS (kn_view HS2sB_4) (ELit 0) 6571768 VML_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma META_HS2sB_3_ok : cells_check JO6SEGS (kn_view HS2sB_3) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4096 META_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma META_HS2sB_4_ok : cells_check JO6SEGS (kn_view HS2sB_4) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4096 META_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GRP_HS2sB_3_ok : cells_check JO6SEGS (kn_view HS2sB_3) (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 0 GRP_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GRP_HS2sB_4_ok : cells_check JO6SEGS (kn_view HS2sB_4) (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 0 GRP_B = true.
Proof. vm_compute. reflexivity. Qed.
Lemma METAW_HS2sB_3_ok : wr_check (kn_view HS2sB_3) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4096 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GRPW_HS2sB_3_ok : wr_check (kn_view HS2sB_3) (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 0 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma METAW_HS2sB_4_ok : wr_check (kn_view HS2sB_4) (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4096 4096 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma GRPW_HS2sB_4_ok : wr_check (kn_view HS2sB_4) (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 0 4096 = true.
Proof. vm_compute. reflexivity. Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi QQjP QJQc QNDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.Riscv.Instr.
Import Qt8n QOTP.
Import QXVi QQjP QJQc.
Import QvSK.Mq0 QNDM.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition DTID : list scell := [ SCw 4 (EVar 44) ].
Definition DLOC : list scell := [ SCw 8 (ELit 6576104) ].
Definition DATEXIT : list scell := [ SCi 1; SCi 3; SCi 4; SCw 4 (ELit 1); SCi 4; SCw 8 (ELit 6575496); SCi 8; SCw 8 (ELit 847136); SCi 8; SCi 240; SCw 8 (ELit 529456); SCi 8 ].
Definition drv_pieces_check (k : list kentry) : bool :=
cells_check JOB6SEGS k (ELit 0) 6444152 DTID && cells_check JOB6SEGS k (ELit 0) 6444272 DLOC && cells_check JOB6SEGS k (ELit 0) 6575472 DATEXIT.
Lemma DRVPIECES_HS2sA_1_ok : drv_pieces_check (kn_view HS2sA_1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma DRVPIECES_HS2sA_2_ok : drv_pieces_check (kn_view HS2sA_2) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma DRVPIECES_HS2sB_3_ok : drv_pieces_check (kn_view HS2sB_3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma DRVPIECES_HS2sB_4_ok : drv_pieces_check (kn_view HS2sB_4) = true.
Proof. vm_compute. reflexivity. Qed.
End Mq1.

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5o6.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ESP0 : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)).
Definition EARGC : expr := EVar 1.
Definition EARGV0 : expr := EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EMd Instr.M_MUL (ELit 16) (EVar 6))))) (ELit 184).
Definition EARGV1 : expr := EMd Instr.M_MUL (EAlu Instr.ALU_SLTU (ELit 1) (EVar 1)) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 1)) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 8) (EVar 2)) (EAlu Instr.ALU_ADD (EVar 3) (EMd Instr.M_MUL (ELit 16) (EVar 6)))))) (ELit 185)).
Definition DARGC : list scell := [ SCw 8 EARGC ].
Definition DARGV0 : list scell := [ SCw 8 EARGV0 ].
Definition DARGV1 : list scell := [ SCw 8 EARGV1 ].
Definition arg_pieces_check (k : list kentry) : bool :=
cells_check JO6SEGS k ESP0 0 DARGC && cells_check JO6SEGS k ESP0 8 DARGV0 && cells_check JO6SEGS k ESP0 16 DARGV1
&& wr_check k ESP0 (-8388608) 8388608.
Lemma ARGPIECES_HS2sA_1_ok : arg_pieces_check (kn_view HS2sA_1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ARGPIECES_HS2sA_2_ok : arg_pieces_check (kn_view HS2sA_2) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ARGPIECES_HS2sB_3_ok : arg_pieces_check (kn_view HS2sB_3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ARGPIECES_HS2sB_4_ok : arg_pieces_check (kn_view HS2sB_4) = true.
Proof. vm_compute. reflexivity. Qed.
