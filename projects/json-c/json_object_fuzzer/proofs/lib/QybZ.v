(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import Qg4E.Mq0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition alloc_ceiling : Z := 0x7fff7f800000.

Definition bottomup_floor : Z := 0x2aaaaaaab000.

Definition placement_ok (h : VmMaps) (aZ nZ : Z) : Prop :=
bottomup_floor <= aZ
\/ no_higher_fit (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h)).

Definition placement_ok_b (h : VmMaps) (aZ nZ : Z) : bool :=
(bottomup_floor <=? aZ)%Z
|| negb (higher_fit_b (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h))).

Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
if w_is0 addr then placement_ok_b h aZ nZ else true.

Definition placement_policy : Prop :=
forall (h : VmMaps) (a : word) (nZ : Z),
0 < nZ -> nZ mod page_size = 0 ->
bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
bv_unsigned a + nZ <= alloc_top h ->
region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
bv_unsigned a + nZ <= alloc_ceiling /\ placement_ok_b h (bv_unsigned a) nZ = true.

Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).

Lemma alloc_ceiling_le_alloc_top : forall h, init_sp_ok h -> alloc_ceiling <= alloc_top h.
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.

Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.

End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU8l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU8l. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qg4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qg4E.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition fd1chan (model : Model) : Prop :=
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).

Definition buf_modeled (b : list byte) : Prop :=
(Z.of_nat (length b) <= rw_bytes_max)%Z.

Definition bufs_modeled (bufs : list (list byte)) : Prop :=
Forall buf_modeled bufs.

Fixpoint wevents_ch (ch : word) (bufs : list (list byte)) : list event :=
match bufs with
| [] => []
| buf :: rest => map (WriteEv ch) buf ++ wevents_ch ch rest
end.

Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
(1 <= n)%nat -> (n <= length buf)%nat ->
wpick ch bufs tr ->
wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).

Section WithSegs.
Variable segs : list Segment.

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wexit ms' bufs code ->
to_wexit ms bufs code.

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
msteps ms' ms'' ->
msteps ms ms''.

Lemma msteps_trans : forall ms ms' ms'',
msteps ms ms' -> msteps ms' ms'' -> msteps ms ms''.
Proof.
intros ms ms' ms'' H; induction H; [auto|].
intro H2. eapply mst_step; eauto.
Qed.

Lemma msteps_to_wexit : forall ms ms' bufs code,
msteps ms ms' -> to_wexit ms' bufs code -> to_wexit ms bufs code.
Proof.
intros ms ms' bufs code H; induction H; [auto|].
intro Hw. eapply tw_step; eauto.
Qed.

Fixpoint wevents (bufs : list (list byte)) : list event :=
match bufs with
| [] => []
| buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
end.

Definition wexit_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
fun tr o =>
(exists full, wpick (Z_to_bv 64 1) bufs full /\ tr = full ++ [ExitEv code fs])
/\ exits_with code tr o.

End WithSegs.

Definition fdchan (fd ch : word) (model : Model) : Prop :=
fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wexit_ch ms' bufs code ->
to_wexit_ch ms bufs code.

Hypothesis Hfd32 : fd32 fd = fd.

End WithSegsCh.

