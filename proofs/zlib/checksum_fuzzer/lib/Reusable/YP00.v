(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Section b.
Variable segs : list Segment.
Fixpoint interp_eff0 (t : eff) (m : word -> option byte)
: machine_result (core * (word -> option byte)) :=
match t with
| EDone c => MachineOk (c, m)
| EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault
| EIllegal _ | EEcall _ => MachineUnmodeled
| ELoad n a k =>
match ov_read_bytes segs m a (width_bytes n) with
| Some bs => interp_eff0 (k (bv_extract 0 n (le_bytes_to_word bs))) m
| None => MachineFault
end
| EStore n a v k =>
if store_ok segs m a (width_bytes n)
then interp_eff0 k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))
else MachineFault
end.
Lemma interp_eff_compat : forall t m,
interp_eff segs t m = interp_eff0 t m.
Proof.
unfold interp_eff.
induction t as [c| | | | | |n a k IH|n a v k IH]; intros m; cbn [interp_eff_accesses interp_eff0];
try reflexivity.
- destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|reflexivity].
rewrite <- IH. destruct (interp_eff_accesses segs _ m) as [[v acc]| |]; reflexivity.
- destruct (store_ok segs m a (width_bytes n)); [|reflexivity].
rewrite <- IH. destruct (interp_eff_accesses segs k _) as [[v' acc]| |]; reflexivity.
Qed.
Lemma decode_exec_compat : forall st w,
decode_exec segs st w =
(if is_ecall w then
MachineOk
{| ms_regs := ms_regs st; ms_fregs := ms_fregs st;
ms_pc_val := ms_pc_val st;
ms_svc_pending := Some (ms_reg st 17);
ms_resv := ms_resv st; ms_fcsr := ms_fcsr st;
ms_mem := ms_mem st;
ms_rom := ms_rom st |}
else
match decode_any w with
| None => if is_defined_illegal w then MachineFault else MachineUnmodeled
| Some (i, isz) =>
match interp_eff0 (exec (Z_to_bv 64 isz) i
{| c_regs := ms_regs st;
c_fregs := ms_fregs st;
c_pc := ms_pc_val st;
c_fcsr := ms_fcsr st;
c_resv := ms_resv st |})
(ms_mem st) with
| MachineFault => MachineFault
| MachineUnmodeled => MachineUnmodeled
| MachineOk (c, m') =>
MachineOk
{| ms_regs := c_regs c; ms_fregs := c_fregs c;
ms_pc_val := c_pc c;
ms_svc_pending := None;
ms_resv := c_resv c; ms_fcsr := c_fcsr c;
ms_mem := m';
ms_rom := ms_rom st |}
end
end).
Proof.
intros st w. unfold decode_exec, decode_exec_accesses.
destruct (is_ecall w); [reflexivity|].
destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); reflexivity].
rewrite <- interp_eff_compat. unfold interp_eff.
destruct (interp_eff_accesses segs _ _) as [[[c m'] acc]| |]; reflexivity.
Qed.
Lemma step_on_fetch_compat : forall ms w,
fetch_word segs (ms_pc_val ms) = Some w ->
RiscvSemantics.step segs ms = decode_exec segs ms w.
Proof.
intros ms w H. unfold RiscvSemantics.step, step_accesses, decode_exec, ms_pc.
rewrite H. reflexivity.
Qed.
End b.
