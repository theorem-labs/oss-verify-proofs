(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK16 YK0o YK0j YK1i.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.









Definition M_loop (model : Model) : Prop :=
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
m_halted model = None /\
m_vm_lazy model = [].



Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
match n with
| O => true
| S n' =>
match find_segment segs (bv_unsigned a) 1 with
| Some seg =>
(seg_writable seg
&& match segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
| Some _ => true
| None => false
end
&& wseg_ok segs (a + 1) n')%bool
| None => false
end
end.











Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
(1 <= Z.of_nat (length bs))%Z ->
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
chunks cnt s (bs :: blocks) s''.



Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.
Definition iter_ev (bs : list byte) : list event :=
iter_ev_ch (Z_to_bv 64 0) bs.
Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
match s with
| IEof => [ExitEv (Z_to_bv 64 0) fs]
| ICons _ _ => []
end.
Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
(s : InputStream) (tr : list event) : Prop :=
exists blocks s',
chunks cnt s blocks s' /\
is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).
Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
(tr : list event) : Prop :=
stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.


Section d.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Definition lh_next (ms : machine_state) : Prop :=
exists ms', msteps segs ms ms' /\ LH ms'.
Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
(1 <= length bs)%nat /\
to_wall segs (Z_to_bv 64 1) ms bs lh_next.
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wr bs ms' -> to_wr bs ms.
Definition ReadPend (ms : machine_state) : Prop :=
exists buf x8,
ms_svc_pending ms = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms 0 = Z_to_bv 64 0 /\
ms_gpr ms 1 = buf /\
ms_gpr ms 2 = cnt /\
(exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\
access_okb buf (bv_unsigned cnt) = true /\
to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
(forall bs,
(1 <= Z.of_nat (length bs))%Z ->
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
to_wr bs (advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))).
Lemma msteps_to_wr : forall bs ms ms',
msteps segs ms ms' -> to_wr bs ms' -> to_wr bs ms.
Proof.
intros bs ms ms' H; induction H; [auto|].
intro Hwr. eapply twr_step; eauto.
Qed.

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_rd ms' -> to_rd ms.
Lemma msteps_to_rd : forall ms ms',
msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof.
intros ms ms' H; induction H; [auto|].
intro Hrd. eapply trd_step; eauto.
Qed.
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.





Definition sinv (c : config) : Prop :=
(M_loop (cfg_model c) /\
(to_rd (cfg_ms c)
\/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
\/ on_path segs (Z_to_bv 64 0) c.









End d.


