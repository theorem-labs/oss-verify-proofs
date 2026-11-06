(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fd_len (cs : acs) : expr := match a_fd cs with FdFile _ l _ => l | _ => ELit 0 end.
Definition fd_q (cs : acs) : nat := match fd_len cs with EAlu _ (EMd _ _ (EVar q)) _ => q | _ => 0%nat end.
Definition fd_r (cs : acs) : nat := match fd_len cs with EAlu _ _ (EVar r) => r | _ => 0%nat end.

