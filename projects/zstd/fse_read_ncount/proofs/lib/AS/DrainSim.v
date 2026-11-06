(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec WallSim StreamSim.
Import ListNotations.
Open Scope bv_scope.
Section Proc.
Context {A : Type}.
Variable f : A -> byte -> option A.
Fixpoint procs (a : A) (bs : list byte) : option A :=
match bs with
| [] => Some a
| b :: rest => match f a b with Some a' => procs a' rest | None => None end
end.
End Proc.
Section Traces.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
End Traces.
Section Drain.
Context {A : Type}.
Variable segs : list Segment.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : A -> machine_state -> Prop.
Definition lh_next (a : A) (ms : machine_state) : Prop :=
exists ms', msteps segs ms ms' /\ LH a ms'.
Definition WrFin (bs : list byte) (ms : machine_state) : Prop :=
(1 <= length bs)%nat /\
to_wall segs (Z_to_bv 64 1) ms bs (to_exit segs (Z_to_bv 64 0)).
Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_out bs ms' -> to_out bs ms.
Definition ReadPend (a : A) (ms : machine_state) : Prop :=
exists buf x8,
ms_svc_pending ms = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms 0 = Z_to_bv 64 0 /\
ms_gpr ms 1 = buf /\
ms_gpr ms 2 = cnt /\
(exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt
= Some w) /\
access_okb buf (bv_unsigned cnt) = true /\
to_out (out a) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
buf_modeled (out a) /\
(forall bs,
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
match procs f a bs with
| Some a' => lh_next a'
(advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))
| None => to_exit segs ec
(advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))
end).
Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_rd a ms' -> to_rd a ms.
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.
End Drain.
