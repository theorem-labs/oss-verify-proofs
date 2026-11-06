(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NUMU_D.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWU_vcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.

Module SLOWU_cert.
Import NUMU_D.PMUN_sum.
Import NUMU_D.PDCU_sum.
Import NUMU_D.NDCU_sum.
Import NUMU_D.SLOWU_defs.
(* [comment removed for export] *)

Lemma slowu_cert : SP.pcheck SG SNU.snu_gfp (SG.gvc_or (SG.gvc_list SLOWUG_GV) (NRC.nrc_ok SG)) SLOWU SLOWU_IT 4000 true ([[]; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; []; [ST.XH [(18%nat, EAlu ALU_ADD (EVar 20) (ELit 32768))] [] []; ST.xh0]; []; []; []]) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End SLOWU_cert.
