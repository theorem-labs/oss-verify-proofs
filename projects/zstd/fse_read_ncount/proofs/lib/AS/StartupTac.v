(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Export
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
MemSplit StartupAux ZStores.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with
| context [Z_to_bv 64 _] => fail
| _ => rewrite (u_Z2bv z) by lia
end
end.
Ltac zlit :=
repeat match goal with
| |- context [Z_to_bv 64 ?z] =>
lazymatch z with
| Z0 => fail | Zpos _ => fail | Zneg _ => fail
| _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
end
end.
Ltac region_side :=
unfold win_lo; rewrite ?stack_max_size_val, ?length_N_to_le_bytes, ?length_zeros, ?repeat_length;
cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.
Ltac peel := repeat (rewrite rdn_wbytes_out by region_side).
Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.
Ltac incl_list :=
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbn [In] in Hr;
repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
eapply regs_agree_mono; [| exact Hag]; incl_list.
Ltac ra_chain :=
first [ apply regs_agree_refl
| apply regs_agree_upd; [ in_list | ]; ra_chain
| match goal with
| Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
end ].
