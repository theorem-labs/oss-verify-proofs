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

Definition PLOCK_A : list scell := [ SCi 4 ].
Definition PNL_A : list scell := [ SCi 1 ].
Definition PPGSZ_A : list scell := [ SCw 8 (ELit 4096) ].
Definition PGOTSSP_A : list scell := [ SCi 8 ].
Definition PSSPG_A : list scell := [ SCw 8 (EVar 45) ].
Definition PVML_A : list scell := [ SCi 4 ].
Definition PHEAD_A : list scell := [ SCw 8 (EBlob false 25 8 8); SCw 4 (ELit 1); SCw 4 (ELit 1); SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4280)); SCw 8 (ELit 97); SCw 8 (ELit 0); SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4096)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4096)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 8192)) ].
Definition PACT_A : list scell := [ SCi 8; SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4120)); SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4160)); SCi 8; SCi 8; SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4200)); SCi 8; SCi 8; SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4240)); SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8 ].
Definition PUSE_A : list scell := [ SCi 8; SCi 8; SCw 8 (ELit 10); SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCw 8 (ELit 2); SCi 8; SCi 8; SCi 8; SCw 8 (ELit 2); SCi 8; SCi 8; SCi 8; SCw 8 (ELit 2); SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8 ].
Definition PUNM_A : list scell := [ SCi 32 ].
Definition PBNC_A : list scell := [ SCi 32 ].
Definition PTAIL_A : list scell := [ SCw 1 (ELit 1); SCi 7; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 8192)) ].
Definition PMHDR_A : list scell := [ SCw 8 (EBlob false 25 8 8); SCz 8; SCw 4 (ELit 101); SCz 4 ].
Definition PM0_A : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4120)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4120)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 48)); SCw 4 (ELit 1022); SCw 4 (ELit 0); SCw 8 (ELit 169) ].
Definition PM1_A : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4160)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4160)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 32)); SCw 4 (ELit 2); SCw 4 (ELit 0); SCw 8 (ELit 993) ].
Definition PM2_A : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4200)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4200)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 16)); SCw 4 (ELit 2); SCw 4 (ELit 0); SCw 8 (ELit 1249) ].
Definition PM3_A : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4240)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4240)); SCw 8 (EMd Instr.M_MUL (ELit 4096) (EVar 423)); SCw 4 (ELit 2); SCw 4 (ELit 0); SCw 8 (ELit 5601) ].
Definition PMZERO_A : list scell := [ SCz 3912 ].
Definition PG0_A : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4240)); SCw 1 (ELit 1) ].
Definition PG1_A : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4200)); SCw 1 (ELit 1) ].
Definition PG2_A : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4160)); SCw 1 (ELit 1) ].
Definition PG3_A : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 5)) (ELit 4120)); SCw 1 (ELit 9) ].
Definition pieces_check_A (k : list kentry) : bool :=
cells_check JO6SEGS k (ELit 0) 6566368 PLOCK_A && cells_check JO6SEGS k (ELit 0) 6566131 PNL_A && cells_check JO6SEGS k (ELit 0) 6566176 PPGSZ_A && cells_check JO6SEGS k (ELit 0) 945024 PGOTSSP_A && cells_check JO6SEGS k (ELit 0) 6565536 PSSPG_A && cells_check JO6SEGS k (ELit 0) 6571768 PVML_A && cells_check JO6SEGS k (ELit 0) 6566376 PHEAD_A && cells_check JO6SEGS k (ELit 0) 6566456 PACT_A && cells_check JO6SEGS k (ELit 0) 6566840 PUSE_A && cells_check JO6SEGS k (ELit 0) 6567224 PUNM_A && cells_check JO6SEGS k (ELit 0) 6567256 PBNC_A && cells_check JO6SEGS k (ELit 0) 6567288 PTAIL_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4096 PMHDR_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4120 PM0_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4160 PM1_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4200 PM2_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4240 PM3_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4280 PMZERO_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0 PG0_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 16 PG1_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 32 PG2_A && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 48 PG3_A.

Definition PLOCK_B : list scell := [ SCi 4 ].
Definition PNL_B : list scell := [ SCi 1 ].
Definition PPGSZ_B : list scell := [ SCw 8 (ELit 4096) ].
Definition PGOTSSP_B : list scell := [ SCi 8 ].
Definition PSSPG_B : list scell := [ SCw 8 (EVar 45) ].
Definition PVML_B : list scell := [ SCi 4 ].
Definition PHEAD_B : list scell := [ SCw 8 (EBlob false 25 8 8); SCw 4 (ELit 1); SCw 4 (ELit 1); SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4280)); SCw 8 (ELit 97); SCw 8 (ELit 0); SCw 8 (ELit 1); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4096)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4096)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 8192)) ].
Definition PACT_B : list scell := [ SCi 8; SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4120)); SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4160)); SCi 8; SCi 8; SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4200)); SCi 8; SCi 8; SCi 8; SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4240)); SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8 ].
Definition PUSE_B : list scell := [ SCi 8; SCi 8; SCw 8 (ELit 10); SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCw 8 (ELit 2); SCi 8; SCi 8; SCi 8; SCw 8 (ELit 2); SCi 8; SCi 8; SCi 8; SCw 8 (ELit 2); SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8; SCi 8 ].
Definition PUNM_B : list scell := [ SCi 32 ].
Definition PBNC_B : list scell := [ SCi 32 ].
Definition PTAIL_B : list scell := [ SCw 1 (ELit 1); SCi 7; SCw 8 (ELit 18446744073709551615) ].
Definition PMHDR_B : list scell := [ SCw 8 (EBlob false 25 8 8); SCz 8; SCw 4 (ELit 101); SCz 4 ].
Definition PM0_B : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4120)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4120)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 424)) (ELit 48)); SCw 4 (ELit 1022); SCw 4 (ELit 0); SCw 8 (ELit 169) ].
Definition PM1_B : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4160)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4160)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 424)) (ELit 32)); SCw 4 (ELit 2); SCw 4 (ELit 0); SCw 8 (ELit 993) ].
Definition PM2_B : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4200)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4200)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 424)) (ELit 16)); SCw 4 (ELit 2); SCw 4 (ELit 0); SCw 8 (ELit 1249) ].
Definition PM3_B : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4240)); SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4240)); SCw 8 (EMd Instr.M_MUL (ELit 4096) (EVar 424)); SCw 4 (ELit 2); SCw 4 (ELit 0); SCw 8 (ELit 5601) ].
Definition PMZERO_B : list scell := [ SCz 3912 ].
Definition PG0_B : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4240)); SCw 1 (ELit 1) ].
Definition PG1_B : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4200)); SCw 1 (ELit 1) ].
Definition PG2_B : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4160)); SCw 1 (ELit 1) ].
Definition PG3_B : list scell := [ SCw 8 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4120)); SCw 1 (ELit 9) ].
Definition pieces_check_B (k : list kentry) : bool :=
cells_check JO6SEGS k (ELit 0) 6566368 PLOCK_B && cells_check JO6SEGS k (ELit 0) 6566131 PNL_B && cells_check JO6SEGS k (ELit 0) 6566176 PPGSZ_B && cells_check JO6SEGS k (ELit 0) 945024 PGOTSSP_B && cells_check JO6SEGS k (ELit 0) 6565536 PSSPG_B && cells_check JO6SEGS k (ELit 0) 6571768 PVML_B && cells_check JO6SEGS k (ELit 0) 6566376 PHEAD_B && cells_check JO6SEGS k (ELit 0) 6566456 PACT_B && cells_check JO6SEGS k (ELit 0) 6566840 PUSE_B && cells_check JO6SEGS k (ELit 0) 6567224 PUNM_B && cells_check JO6SEGS k (ELit 0) 6567256 PBNC_B && cells_check JO6SEGS k (ELit 0) 6567288 PTAIL_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4096 PMHDR_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4120 PM0_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4160 PM1_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4200 PM2_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4240 PM3_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4280 PMZERO_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 0 PG0_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 16 PG1_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 32 PG2_B && cells_check JO6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 48 PG3_B.

Lemma PIECES_HS2sA_1_ok : pieces_check_A (kn_view HS2sA_1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PIECES_HS2sA_2_ok : pieces_check_A (kn_view HS2sA_2) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PIECES_HS2sB_3_ok : pieces_check_B (kn_view HS2sB_3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PIECES_HS2sB_4_ok : pieces_check_B (kn_view HS2sB_4) = true.
Proof. vm_compute. reflexivity. Qed.
End Mq0.

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

Definition DTID : list scell := [ SCw 4 (EVar 44) ].
Definition DLOC : list scell := [ SCw 8 (ELit 6566184) ].
Definition DATEXIT : list scell := [ SCi 1; SCi 3; SCi 4; SCw 4 (ELit 1); SCi 4; SCw 8 (ELit 6565576); SCi 8; SCw 8 (ELit 837212); SCi 8; SCi 240; SCw 8 (ELit 528472); SCi 8 ].
Definition drv_pieces_check (k : list kentry) : bool :=
cells_check JO6SEGS k (ELit 0) 6434232 DTID && cells_check JO6SEGS k (ELit 0) 6434352 DLOC && cells_check JO6SEGS k (ELit 0) 6565552 DATEXIT.
Lemma DRVPIECES_HS2sA_1_ok : drv_pieces_check (kn_view HS2sA_1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma DRVPIECES_HS2sA_2_ok : drv_pieces_check (kn_view HS2sA_2) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma DRVPIECES_HS2sB_3_ok : drv_pieces_check (kn_view HS2sB_3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma DRVPIECES_HS2sB_4_ok : drv_pieces_check (kn_view HS2sB_4) = true.
Proof. vm_compute. reflexivity. Qed.
