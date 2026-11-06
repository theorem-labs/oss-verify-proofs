(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXVi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQjP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQjP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJQc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJQc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNDM.
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
cells_check JOB6SEGS k (ELit 0) 6576288 PLOCK_A && cells_check JOB6SEGS k (ELit 0) 6576051 PNL_A && cells_check JOB6SEGS k (ELit 0) 6576096 PPGSZ_A && cells_check JOB6SEGS k (ELit 0) 954256 PGOTSSP_A && cells_check JOB6SEGS k (ELit 0) 6575456 PSSPG_A && cells_check JOB6SEGS k (ELit 0) 6581688 PVML_A && cells_check JOB6SEGS k (ELit 0) 6576296 PHEAD_A && cells_check JOB6SEGS k (ELit 0) 6576376 PACT_A && cells_check JOB6SEGS k (ELit 0) 6576760 PUSE_A && cells_check JOB6SEGS k (ELit 0) 6577144 PUNM_A && cells_check JOB6SEGS k (ELit 0) 6577176 PBNC_A && cells_check JOB6SEGS k (ELit 0) 6577208 PTAIL_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4096 PMHDR_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4120 PM0_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4160 PM1_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4200 PM2_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4240 PM3_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 5)) 4280 PMZERO_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 0 PG0_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 16 PG1_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 32 PG2_A && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 48 PG3_A.

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
cells_check JOB6SEGS k (ELit 0) 6576288 PLOCK_B && cells_check JOB6SEGS k (ELit 0) 6576051 PNL_B && cells_check JOB6SEGS k (ELit 0) 6576096 PPGSZ_B && cells_check JOB6SEGS k (ELit 0) 954256 PGOTSSP_B && cells_check JOB6SEGS k (ELit 0) 6575456 PSSPG_B && cells_check JOB6SEGS k (ELit 0) 6581688 PVML_B && cells_check JOB6SEGS k (ELit 0) 6576296 PHEAD_B && cells_check JOB6SEGS k (ELit 0) 6576376 PACT_B && cells_check JOB6SEGS k (ELit 0) 6576760 PUSE_B && cells_check JOB6SEGS k (ELit 0) 6577144 PUNM_B && cells_check JOB6SEGS k (ELit 0) 6577176 PBNC_B && cells_check JOB6SEGS k (ELit 0) 6577208 PTAIL_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4096 PMHDR_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4120 PM0_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4160 PM1_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4200 PM2_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4240 PM3_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 423)) 4280 PMZERO_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 0 PG0_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 16 PG1_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 32 PG2_B && cells_check JOB6SEGS k (EMd Instr.M_MUL (ELit 4096) (EVar 424)) 48 PG3_B.

Lemma PIECES_HS2sA_1_ok : pieces_check_A (kn_view HS2sA_1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PIECES_HS2sA_2_ok : pieces_check_A (kn_view HS2sA_2) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PIECES_HS2sB_3_ok : pieces_check_B (kn_view HS2sB_3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PIECES_HS2sB_4_ok : pieces_check_B (kn_view HS2sB_4) = true.
Proof. vm_compute. reflexivity. Qed.
