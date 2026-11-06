(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module StdioKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte) (only parsing).

(* [comment removed for export] *)
Definition F_STDIO_READ : Z := 0x99d8c.
Definition F_STDIO_WRITE : Z := 0x99eac.
Definition F_STDIO_SEEK : Z := 0x99ea4.
Definition F_STDIO_CLOSE : Z := 0x99d60.
Definition F_STDOUT_WRITE : Z := 0x9ada0.
Definition F_SYSRET : Z := 0x94b1c.
(* [comment removed for export] *)
Definition A_STDOUT : Z := 0xa9c90.
Definition A_STDOUT_BUF : Z := 0x6020d0.
Definition A_STDERR : Z := 0xa9ab0.
Definition A_STDERR_BUF : Z := 0x601cc0.
Definition A_STDIN : Z := 0xa9ba0.
Definition A_STDIN_BUF : Z := 0x601cc8.
Definition A_OFL_LOCK : Z := 0x601ca8.
Definition A_OFL_HEAD : Z := 0x601cb0.

(* [comment removed for export] *)
Definition ssp_cells (m : mem) (canary : word) : Prop :=
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.

Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte) (only parsing).

(* [comment removed for export] *)
Definition F_STDIO_READ : Z := 0x9a170.
Definition F_STDIO_WRITE : Z := 0x9a290.
Definition F_STDIO_SEEK : Z := 0x9a288.
Definition F_STDIO_CLOSE : Z := 0x9a144.
Definition F_STDOUT_WRITE : Z := 0x9b184.
Definition F_SYSRET : Z := 0x94f00.
(* [comment removed for export] *)
Definition A_STDOUT : Z := 0xaa070.
Definition A_STDOUT_BUF : Z := 0x6024d0.
Definition A_STDERR : Z := 0xa9e90.
Definition A_STDERR_BUF : Z := 0x6020c0.
Definition A_STDIN : Z := 0xa9f80.
Definition A_STDIN_BUF : Z := 0x6020c8.
Definition A_OFL_LOCK : Z := 0x6020a8.
Definition A_OFL_HEAD : Z := 0x6020b0.

(* [comment removed for export] *)
Definition ssp_cells (m : mem) (canary : word) : Prop :=
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_litstore :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | _ => idtac
  end.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.

Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. intros z. reflexivity. Qed.

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
End TwB.
End StdioKit.

(* [comment removed for export] *)
Module F_stdio_write.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_WRITE : Z := 0x99eac.
Definition STDIO_WRITE_DEPTH : Z := 112.
Definition SW_SHORT : Z := 0x99fcc.   (* [comment removed for export] *)
Definition SW_OK : Z := 0x99f40.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition wdec_Some__stmt : Prop := forall f rem rsp cnt,
  wdec f rem rsp = Some cnt ->
  rsp = eff0 (Z_to_bv 64 cnt) /\ 0 <= cnt <= rem /\ 0 <= cnt < 2^64 /\ (cnt = rem \/ 1 <= cnt < rem).
Section Sz1.
Variables f rem rsp cnt : ltac2:(SecDiet.SzSec.tyM 'wdec_Some__stmt "vvvv" @f).
#[using="Type"] Lemma wdec_Some__body : ltac2:(SecDiet.SzSec.bodyP 'wdec_Some__stmt "vvvv").
Proof.
  intros H.
 unfold wdec in H. destruct (f_chan f).
  - apply dec_writev_Some in H as (Hr & -> & Hc). split; [reflexivity|]. lia.
  - unfold dec_writevf_ok, dec_writevf in H.
    destruct (dec_plain (fun v => v =? rem) rsp) as [[e|v]|] eqn:E; try discriminate H.
    injection H as <-. apply dec_plain_Some in E as (-> & Hok & Hv).
    apply Z.eqb_eq in Hok. subst v. split; [reflexivity|]. lia.
Qed.
End Sz1.
Lemma wdec_Some : ltac:(let t := eval cbv delta [wdec_Some__stmt] in wdec_Some__stmt in exact t).
Proof. intros f rem rsp cnt. ltac2:(SecDiet.SzSec.closeP 'wdec_Some__body "vvvv"). Qed.

(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
Definition at_wnode__stmt : Prop := forall RNG f L (R F : bvmap 5 word) pc fc m (A : Z) (iovs : list (word * word)),
  rng RNG A (16 * Z.of_nat (length L)) ->
  Forall2 (fun (iov : word * word) (bs : list byte) => rng RNG (bv_unsigned (fst iov)) (Z.of_nat (length bs))) iovs (map to_bytes L) ->
  (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^32 /\ 1 <= Z.of_nat (length (concat (map to_bytes L))))) ->
  reg_get R 10 = Z_to_bv 64 (f_fd f) ->
  reg_get R 11 = Z_to_bv 64 A -> 0 <= A < 2^64 ->
  reg_get R 12 = Z_to_bv 64 (Z.of_nat (length L)) ->
  (1 <= length L <= 2)%nat ->
  A + 16 * Z.of_nat (length L) <= 2^47 ->   (* [comment removed for export] *)
  Z.of_nat (length (concat (map to_bytes L))) <= max_write ->
  bytes_at asegs m A (iovec_bytes iovs) ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47   (* [comment removed for export] *)
                         /\ bytes_at asegs m (bv_unsigned (fst iov)) bs) iovs (map to_bytes L) ->
  at_nodeA asegs (wnode f L) RNG (MSsvc R F pc (Z_to_bv 64 66) fc None m (seg_rom asegs)).
Section Sz2.
Variables RNG f L R F pc fc m A iovs : ltac2:(SecDiet.SzSec.tyM 'at_wnode__stmt "vvvvvvvvvv" @RNG).
#[using="Type"] Lemma at_wnode__body : ltac2:(SecDiet.SzSec.bodyP 'at_wnode__stmt "vvvvvvvvvv").
Proof.
  intros RA HR CH R10 R11 HA R12 HL HA47 HT HIOV HF.
  assert (HF4 : Forall2 (fun (iov : word * word) (bs : list byte) => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47
                 /\ bytes_at asegs m (bv_unsigned (fst iov)) bs /\ rng RNG (bv_unsigned (fst iov)) (Z.of_nat (length bs))) iovs (map to_bytes L)).
  { clear -HF HR. induction HF as [|iov bs iovs' bss (H1 & H2 & H3) HF IH]; [constructor|].
    inversion HR as [|? ? ? ? HR1 HR2]; subst. constructor; [exact (conj H1 (conj H2 (conj H3 HR1)))| exact (IH HR2)]. }
  unfold wnode. destruct (f_chan f).
  - cbn [at_nodeA]. unfold at_gatherA, areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS].
    rewrite R10, R11, R12, length_map. rewrite unsigned_lit by lia.
    repeat (split; [first [reflexivity | exact RA | assumption | lia]|]). exists iovs. split; assumption.
  - destruct CH as [FD TOT]. cbn [at_nodeA]. unfold at_gatherA, areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS].
    rewrite R10, R11, R12, length_map. rewrite unsigned_lit by lia.
    repeat (split; [first [reflexivity | exact RA | assumption | lia]|]). exists iovs. split; assumption.
Qed.
End Sz2.
#[using="Type"] Lemma at_wnode : ltac:(let t := eval cbv delta [at_wnode__stmt] in at_wnode__stmt in exact t).
Proof. intros RNG f L R F pc fc m A iovs. ltac2:(SecDiet.SzSec.closeP 'at_wnode__body "vvvvvvvvvv"). Qed.
End CANSEC0.

(* [comment removed for export] *)
Definition iov_bytes2__stmt : Prop := forall m A j8 (w0 w1 w2 w3 : word) rest,
  rw_cells asegs m A (CB 8 j8 :: C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: rest) ->
  bytes_at asegs m (A + 8) (iovec_bytes [(w0, w1); (w2, w3)]) /\ bytes_at asegs m (A + 24) (iovec_bytes [(w2, w3)]).
Section Sz3.
Variables m A j8 w0 w1 w2 w3 rest : ltac2:(SecDiet.SzSec.tyM 'iov_bytes2__stmt "vvvvvvvv" @m).
#[using="Type"] Lemma iov_bytes2__body : ltac2:(SecDiet.SzSec.bodyP 'iov_bytes2__stmt "vvvvvvvv").
Proof.
  intros FR.
  destruct FR as [[WF FB] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _].
  cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
  apply bytes_at_app in FB as [FB0 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB3 _].
  cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r. split.
  - apply bytes_at_app. rewrite length_app, !length_le8. split.
    + apply bytes_at_app. rewrite length_le8. split.
      * replace (A + 8) with (A + Z.of_nat 8) by lia. exact FB0.
      * replace (A + 8 + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB1.
    + apply bytes_at_app. rewrite length_le8. split.
      * replace (A + 8 + Z.of_nat (8 + 8)) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
      * replace (A + 8 + Z.of_nat (8 + 8) + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
  - apply bytes_at_app. rewrite length_le8. split.
    + replace (A + 24) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
    + replace (A + 24 + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
Qed.
End Sz3.
Lemma iov_bytes2 : ltac:(let t := eval cbv delta [iov_bytes2__stmt] in iov_bytes2__stmt in exact t).
Proof. intros m A j8 w0 w1 w2 w3 rest. ltac2:(SecDiet.SzSec.closeP 'iov_bytes2__body "vvvvvvvv"). Qed.

Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_skipn : forall m A bs n, bytes_at asegs m A bs -> (n <= length bs)%nat ->
  bytes_at asegs m (A + Z.of_nat n) (skipn n bs).
Proof.
  intros m A bs n H Hn. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H as [_ H].
  rewrite firstn_length_le in H by lia. exact H.
Qed.


Ltac wn_clr := repeat match goal with H : context [implAM] |- _ => clear H end.
Ltac wn_bufs RS RB :=
  wn_clr; cbn [map];
  repeat first [ apply Forall2_nil
               | apply Forall2_cons;
                 [ cbn [fst]; rewrite ?unsigned_lit by (unfold zlength in *; lia); rewrite ?length_to_bytes, ?length_skipn;
                   first [ eapply rng_sub'; [exact RS | unfold zlength in *; lia]
                         | eapply rng_sub'; [exact RB | unfold zlength in *; lia] ] |] ].

Section StdioWrite.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition fcells (flags : word) (rpos rend closefn : Z) (wend wpos wbase : Z)
      (readfn writefn seekfn B bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
    file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next fd mode lbf tail.

  Definition sw_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)].

  (* [comment removed for export] *)
  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn readfn writefn seekfn B bufsize prev next : Z) (mode : word) (lbf : Z) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => f' = set_w true [] f /\ st' = st /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (sw_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags rpos rend closefn (B + bufsize) B B readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail)
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition sw_ok_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z) (mode : word) (lbf : Z) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word) (j8 : list byte) (w0 w1 w2 w3 : word) (m' : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 SW_OK) fc None m' (seg_rom asegs)
      /\ munch (sw_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp + -112)
      /\ rw_cells asegs m' (bv_unsigned sp + -112)
           [CB 8 j8; C8 w0; C8 w1; C8 w2; C8 w3; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' Fp (fcells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail)
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition sw_tail__stmt : Prop := forall RNG (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st st' : St) (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z)
      (mode : word) (lbf : Z) (tail : list byte) (len lo : Z) (canary : word) (m : mem) ms u,
    rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng_aimg RNG ->
    sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m u st' ms ->
    (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (lo <= bv_unsigned sp - 112) ->
    (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
    (0 <= B) -> (0 <= bufsize) -> (B + bufsize < 2^64) -> (0 <= len < 2^64) ->
    evtF asegs RNG (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m (set_w true [] f) st') ms.
  Section Sz7.
  Variables RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st st' Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m ms u : ltac2:(SecDiet.SzSec.tyM 'sw_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma sw_tail__body : ltac2:(SecDiet.SzSec.bodyP 'sw_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros RSTK RFP RIMG POST Fp0 FPLO LO FSEP1 FSEP2 B0 BS0 BShi LEN.
    destruct POST as [-> POST]. destruct_exs POST.
    destruct POST as (-> & MU & WM & MI & ST & FR & FC & [GOT GUARD]).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold fcells, file_cells in FC. unfold got_ssp, ssp_guard, SW_OK in *.
    rename x23 into m1. unfold sw_W, STDIO_WRITE_DEPTH in MU.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size csize Nat.add] in FB.
    do 7 step.
    (* [comment removed for export] *)
    step. step. step. if_false.
    do 10 step.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold stdio_write_post, fcells, file_cells. split; [reflexivity|]. split; [reflexivity|].
    sys_finish. split; [exact GOT | exact GUARD].
  Qed.
  End Sz7.
  Lemma sw_tail : ltac:(let t := eval cbv delta [sw_tail__stmt] in sw_tail__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st st' Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m ms u. ltac2:(SecDiet.SzSec.closeP 'sw_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Section Loop.
    Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z)
              (mode : word) (lbf : Z) (tail : list byte) (s : list Z) (S lo : Z) (canary : word) (m : mem).
    #[local] Notation len := (zlength s) (only parsing).
    #[local] Notation wb := (f_wbuf f) (only parsing).
    #[local] Notation FCELLS := (fcells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail) (only parsing).
    #[local] Notation QOK := (sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend wpos wbase
                 readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m) (only parsing).

    Hypothesis CH : if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31).
    Hypothesis LO : lo <= bv_unsigned sp - 112.
    Hypothesis SP47 : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
    Hypothesis GLO : 0x603000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
    Hypothesis S0 : 0 <= S < 2^64.
    Hypothesis Shi : S + len <= 2^47.   (* [comment removed for export] *)
    Hypothesis LENW : zlength wb + len <= 2^26.
    Hypothesis SEPS : s = [] \/ ((S + len <= lo \/ bv_unsigned sp <= S) /\ (S + len <= Fp + 32 \/ Fp + 64 <= S)).
    Hypothesis SRC : bytes_at asegs m S (to_bytes s).      (* [comment removed for export] *)
    Hypothesis B0 : 0 <= B.
    Hypothesis BWB : B + zlength wb <= 2^47.   (* [comment removed for export] *)
    Hypothesis SEPB : (B + zlength wb <= lo \/ bv_unsigned sp <= B) /\ (B + zlength wb <= Fp + 32 \/ Fp + 64 <= B).
    Hypothesis BUFB : bytes_at asegs m B (to_bytes wb).    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFP : rng RNG Fp 232.
    Hypothesis RB : rng RNG B (zlength wb).
    Hypothesis RS : rng RNG S len.
    Hypothesis RIMG : rng_aimg RNG.

    Definition src_at__stmt : Prop := forall m1 k, munch (sw_W sp Fp) m m1 -> 0 <= k <= len ->
      bytes_at asegs m1 (S + k) (to_bytes (skipn (Z.to_nat k) s)).
    Section Sz8.
    Variables m1 k : ltac2:(SecDiet.SzSec.tyM 'src_at__stmt "vv" @m1).
    Lemma src_at__body : ltac2:(SecDiet.SzSec.bodyP 'src_at__stmt "vv").
    Proof using FPLO LENW LO S0 SEPB SEPS SRC Shi. pin_using (fun (FPLO LENW LO S0 SEPB SEPS SRC Shi : unit) => tt).
      intros MU Hk.
 rewrite to_bytes_skipn.
      replace (S + k) with (S + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skipn; [| rewrite length_to_bytes; unfold zlength in Hk; lia].
      clear RS. destruct SEPS as [-> | [SEP1 SEP2]].
      - apply bytes_at_nil. lia.
      - apply (bytes_at_transport _ _ _ m1 _ _ SRC MU). unfold sw_W, STDIO_WRITE_DEPTH. cbn [disjoint_from].
        rewrite length_to_bytes. unfold zlength in *. lia.
    Qed.
    End Sz8.
    Lemma src_at : ltac:(let t := eval cbv delta [src_at__stmt] in src_at__stmt in exact t).
    Proof using FPLO LENW LO S0 SEPB SEPS SRC Shi. intros m1 k. ltac2:(SecDiet.SzSec.closeP 'src_at__body "vv"). Qed.

    Definition buf_at__stmt : Prop := forall m1 k, munch (sw_W sp Fp) m m1 -> 0 <= k <= zlength wb ->
      bytes_at asegs m1 (B + k) (to_bytes (skipn (Z.to_nat k) wb)).
    Section Sz9.
    Variables m1 k : ltac2:(SecDiet.SzSec.tyM 'buf_at__stmt "vv" @m1).
    Lemma buf_at__body : ltac2:(SecDiet.SzSec.bodyP 'buf_at__stmt "vv").
    Proof using B0 BUFB BWB FPLO LENW LO SEPB SP47. pin_using (fun (B0 BUFB BWB FPLO LENW LO SEPB SP47 : unit) => tt).
      intros MU Hk.
 rewrite to_bytes_skipn.
      replace (B + k) with (B + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skipn; [| rewrite length_to_bytes; unfold zlength in Hk; lia].
      clear RB. destruct (f_wbuf f) as [|b0 wb'] eqn:EWB.
      - apply bytes_at_nil. lia.
      - destruct SEPB as [SEP1 SEP2].
        apply (bytes_at_transport _ _ _ m1 _ _ BUFB MU). unfold sw_W, STDIO_WRITE_DEPTH. cbn [disjoint_from].
        rewrite length_to_bytes. unfold zlength in *. cbn [length] in *. lia.
    Qed.
    End Sz9.
    Lemma buf_at : ltac:(let t := eval cbv delta [buf_at__stmt] in buf_at__stmt in exact t).
    Proof using B0 BUFB BWB FPLO LENW LO SEPB SP47. intros m1 k. ltac2:(SecDiet.SzSec.closeP 'buf_at__body "vv"). Qed.

    (* [comment removed for export] *)
    Lemma sw_loopB : forall fuel (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (j8 : list byte) (w0 w1 : word)
        (k cnt : Z) (m1 : mem),
      rw_cells asegs m1 (bv_unsigned sp + -112)
        [CB 8 j8; C8 w0; C8 w1; C8 (Z_to_bv 64 (S + k)); C8 (Z_to_bv 64 (len - k)); C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m1 Fp FCELLS ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -112) -> mem_inv asegs m1 ->
      munch (sw_W sp Fp) m m1 -> wmono asegs m m1 ->
      0 <= k -> 1 <= cnt -> k + cnt < len ->
      implAM RNG (writev_loop fuel f [skipn (Z.to_nat (k + cnt)) s] (len - k - cnt)) st QOK
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -88)) x20 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (len - k))
                 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_SHORT) fc None m1 (seg_rom asegs)).
    Proof using CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi RSTK RFP RB RS RIMG. pin_using (fun (CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi : unit) => tt).
      induction fuel as [|fuel IH]; intros until m1; intros FR FC SSP ST MI MU WM K0 C1 KC.
      { cbn [writev_loop]. apply implAM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, SW_SHORT in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold sw_W, STDIO_WRITE_DEPTH in MU.
      cbn [writev_loop]. (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      unfold zlength in *.
      assert (LS : Z.of_nat (length (to_bytes s)) = Z.of_nat (length s)) by (rewrite length_to_bytes; reflexivity).
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. clear IH. lia. }
      zs. zs.
      replace (Z.of_nat (length s) - k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      assert (FD : 0 <= f_fd f < 2^31) by (clear IH; destruct (f_chan f); lia).
      zs. zs.
      zs. zs. zs. rewrite Z.land_0_l. zs. rewrite Z.sub_0_r. zs. zs.
      zs. if_cases Hb; zify_cond Hb. 2:{ exfalso. clear IH. lia. }
      zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
      zs. zs. zs. zs. zs.
      step_ecall. split.
      { (* [comment removed for export] *)
        lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
        eapply at_wnode with (A := bv_unsigned sp + -88)
          (iovs := [(Z_to_bv 64 (S + k + cnt), Z_to_bv 64 (Z.of_nat (length s) - k - cnt))]).
        - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
        - (* [comment removed for export] *) wn_bufs RS RB.
        - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn. lia.
        - reflexivity.
        - reflexivity.
        - clear IH; lia.
        - reflexivity.
        - cbn; lia.
        - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
        - clear IH. cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn.
          replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
        - constructor; [|constructor]. split; [|split].
          + cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. clear IH; lia.
          + cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes, length_skipn. clear IH; lia.   (* [comment removed for export] *)
          + cbn [fst]. rewrite unsigned_lit by (clear IH; lia).
            replace (S + k + cnt) with (S + (k + cnt)) by lia. apply src_at; [exact MU | clear IH; unfold zlength; lia]. }
      (* [comment removed for export] *)
      intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implAM_from_evt. sys_nret.
      (* [comment removed for export] *)
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x99fc4)) with (Z_to_bv 64 0x99fc4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zs. zs.
      destruct Hcases as [-> | Hshort].
      - (* [comment removed for export] *)
        rewrite Z.eqb_refl. if_true.
        apply evtF_done. apply implAM_ret. apply evtF_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      - (* [comment removed for export] *)
        replace (cnt' =? Z.of_nat (length s) - k - cnt) with false by (symmetry; apply Z.eqb_neq; lia).
        if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
        cbn [advance_iovs].
        replace (zlength (skipn (Z.to_nat (k + cnt)) s) <? cnt') with false.
        2:{ symmetry. apply Z.ltb_ge. unfold zlength. rewrite length_skipn. clear IH. lia. }
        rewrite skipn_skipn.
        replace (Z.to_nat cnt' + Z.to_nat (k + cnt))%nat with (Z.to_nat ((k + cnt) + cnt')) by lia.
        replace (Z.of_nat (length s) - k - cnt - cnt') with (Z.of_nat (length s) - (k + cnt) - cnt') by lia.
        replace (Z.of_nat (length s) - k - cnt) with (Z.of_nat (length s) - (k + cnt)) in * by lia.
        replace (S + k + cnt) with (S + (k + cnt)) in * by lia.
        apply evtF_done. eapply IH; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | lia | lia | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma sw_loopA : forall fuel (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (j8 : list byte)
        (k cnt : Z) (m1 : mem),
      rw_cells asegs m1 (bv_unsigned sp + -112)
        [CB 8 j8; C8 (Z_to_bv 64 (B + k)); C8 (Z_to_bv 64 (zlength wb - k)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 len); C8 canary;
         C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m1 Fp FCELLS ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -112) -> mem_inv asegs m1 ->
      munch (sw_W sp Fp) m m1 -> wmono asegs m m1 ->
      0 <= k <= zlength wb -> 1 <= cnt -> k + cnt < zlength wb + len ->
      implAM RNG (writev_loop fuel f (advance_iovs [skipn (Z.to_nat k) wb; s] cnt) (zlength wb - k + len - cnt)) st QOK
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -104)) x20 (Z_to_bv 64 ssp_guard)
                 (Z_to_bv 64 (zlength wb - k + len)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_SHORT) fc None m1 (seg_rom asegs)).
    Proof using B0 BUFB BWB CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi RSTK RFP RB RS RIMG. pin_using (fun (B0 BUFB BWB CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi : unit) => tt).
      induction fuel as [|fuel IH]; intros until m1; intros FR FC SSP ST MI MU WM K0 C1 KC.
      { cbn [writev_loop]. destruct (zlength (skipn (Z.to_nat k) wb) <? cnt); apply implAM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, SW_SHORT in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold sw_W, STDIO_WRITE_DEPTH in MU.
      unfold zlength in *.
      assert (FD : 0 <= f_fd f < 2^31) by (clear IH; destruct (f_chan f); lia).
      cbn [writev_loop]. (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. clear IH. lia. }
      zs. zs.
      destruct (Z.le_gt_cases cnt (Z.of_nat (length (f_wbuf f)) - k)) as [LE | GT].
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (f_wbuf f)) - k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
        cbn [advance_iovs]. unfold zlength. rewrite length_skipn.
        replace (Z.of_nat (length (f_wbuf f) - Z.to_nat k) <? cnt) with false by (symmetry; apply Z.ltb_ge; clear IH; lia).
        zs. zs.
        zs. zs. zs. rewrite Z.land_0_l. zs. rewrite Z.sub_0_r. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 2:{ exfalso. clear IH. lia. }
        zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
        zs. zs. zs. zs. zs.
        step_ecall. split.
        { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
            lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
              pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [IOV _] end end.
          eapply at_wnode with (A := bv_unsigned sp + -104)
            (iovs := [(Z_to_bv 64 (B + k + cnt), Z_to_bv 64 (Z.of_nat (length (f_wbuf f)) - k - cnt));
                      (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
          - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
          - (* [comment removed for export] *) wn_bufs RS RB.
          - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
            cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn. lia.
          - reflexivity.
          - reflexivity.
          - clear IH; lia.
          - reflexivity.
          - cbn; lia.
          - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
          - clear IH. cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn.
            replace max_write with 67108864 by reflexivity. lia.
          - replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in IOV by lia. exact IOV.
          - constructor; [|constructor; [|constructor]].
            + split; [|split].
              * cbn [snd]. rewrite length_to_bytes, !length_skipn. f_equal. clear IH; lia.
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes, !length_skipn. clear IH; lia.   (* [comment removed for export] *)
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite skipn_skipn.
                replace (Z.to_nat cnt + Z.to_nat k)%nat with (Z.to_nat (k + cnt)) by lia.
                replace (B + k + cnt) with (B + (k + cnt)) by lia. apply buf_at; [exact MU | clear IH; unfold zlength; lia].
            + split; [|split].
              * cbn [snd]. rewrite length_to_bytes. reflexivity.
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes. clear IH; lia.   (* [comment removed for export] *)
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia).
                pose proof (src_at _ 0 MU) as SR. specialize (SR ltac:(clear IH; unfold zlength; lia)). cbn [Z.to_nat skipn] in SR.
                rewrite Z.add_0_r in SR. exact SR. }
       
        intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
        unfold eff0. apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x99fc4)) with (Z_to_bv 64 0x99fc4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. zs.
        destruct Hcases as [-> | Hshort].
        + rewrite Z.eqb_refl. if_true.
          apply evtF_done. apply implAM_ret. apply evtF_done.
          unfold sw_ok_post. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
        + replace (cnt' =? Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt) with false by (symmetry; apply Z.eqb_neq; lia).
          if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
          rewrite skipn_skipn.
          replace (Z.to_nat cnt + Z.to_nat k)%nat with (Z.to_nat (k + cnt)) by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt - cnt')
            with (Z.of_nat (length (f_wbuf f)) - (k + cnt) + Z.of_nat (length s) - cnt') by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt)
            with (Z.of_nat (length (f_wbuf f)) - (k + cnt) + Z.of_nat (length s)) in * by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k - cnt) with (Z.of_nat (length (f_wbuf f)) - (k + cnt)) in * by lia.
          replace (B + k + cnt) with (B + (k + cnt)) in * by lia.
          apply evtF_done. eapply IH; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | lia | lia | lia].
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (f_wbuf f)) - k <? cnt) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        cbn [advance_iovs]. unfold zlength. rewrite length_skipn.
        replace (Z.of_nat (length (f_wbuf f) - Z.to_nat k) <? cnt) with true by (symmetry; apply Z.ltb_lt; clear IH; lia).
        zs. zs.
        zs. zs. zs.
        replace (Z.land 18446744073709551615 (Z.of_nat (length (f_wbuf f)) - k)) with (Z.of_nat (length (f_wbuf f)) - k).
        2:{ rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. clear IH; lia. }
        zs. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. clear IH. lia. }
        zs. zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
        zs. zs. zs. zs. zs.
        set (kB := cnt - (Z.of_nat (length (f_wbuf f)) - k)) in *.
        step_ecall. split.
        { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
            lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
              pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
          eapply at_wnode with (A := bv_unsigned sp + -88)
            (iovs := [(Z_to_bv 64 (S + kB), Z_to_bv 64 (Z.of_nat (length s) - kB))]).
          - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
          - (* [comment removed for export] *) wn_bufs RS RB.
          - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
            cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn. subst kB. lia.
          - reflexivity.
          - reflexivity.
          - clear IH; lia.
          - cbn [length]. reflexivity.
          - cbn; lia.
          - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
          - clear IH. cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn.
            replace max_write with 67108864 by reflexivity. subst kB. lia.
          - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
          - constructor; [|constructor]. split; [|split].
            + cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. clear IH; subst kB; lia.
            + cbn [fst]. rewrite unsigned_lit by (clear IH; subst kB; lia). rewrite length_to_bytes, length_skipn. clear IH; subst kB; lia.   (* [comment removed for export] *)
            + cbn [fst]. rewrite unsigned_lit by (clear IH; subst kB; lia).
              replace (Z.to_nat (cnt - Z.of_nat (length (f_wbuf f) - Z.to_nat k))) with (Z.to_nat kB) by (subst kB; clear IH; lia).
              apply src_at; [exact MU | clear IH; subst kB; unfold zlength; lia]. }
        intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
        unfold eff0. apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x99fc4)) with (Z_to_bv 64 0x99fc4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. zs. 
        replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt) with (Z.of_nat (length s) - kB) in * by (subst kB; lia).
        
        replace (Z.to_nat (cnt - Z.of_nat (length (f_wbuf f) - Z.to_nat k))) with (Z.to_nat kB) by (subst kB; clear IH; lia).
        
        destruct Hcases as [-> | Hshort].
        + rewrite Z.eqb_refl. if_true. 
          apply evtF_done. apply implAM_ret. apply evtF_done.
          unfold sw_ok_post. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
        + replace (cnt' =? Z.of_nat (length s) - kB) with false by (symmetry; apply Z.eqb_neq; lia).
          if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
          cbn [advance_iovs]. 
          replace (zlength (skipn (Z.to_nat kB) s) <? cnt') with false.
          2:{ symmetry. apply Z.ltb_ge. unfold zlength. rewrite length_skipn. clear IH. subst kB. lia. }
          rewrite skipn_skipn.
          replace (Z.to_nat cnt' + Z.to_nat kB)%nat with (Z.to_nat (kB + cnt')) by (clear IH; subst kB; lia).
          replace (Z.of_nat (length s) - kB - cnt') with (Z.of_nat (length s) - kB - cnt') by lia.
          apply evtF_done.
          eapply sw_loopB; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | clear IH; subst kB; lia | clear IH; subst kB; lia | clear IH; subst kB; unfold zlength; lia].
    Qed.
  End Loop.
End StdioWrite.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Context {rc : runConstT}.
  Context {St : Type}.

  Lemma implM_at_eq : forall {A} RNG (c : M St A) s Q ms ms', implAM RNG c s Q ms' -> ms = ms' -> implAM RNG c s Q ms.
  Proof using Type. pin_using tt. intros A RNG c s Q ms ms' H ->. exact H. Qed.

  Ltac ms_eq := cbv delta [mkR]; repeat fastfirst (first [reflexivity | progress f_equal | unfold zlength in *; lia]).

  Definition stdio_write_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn wend readfn writefn seekfn B bufsize prev next : Z)
           (mode : word) (lbf : Z) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn wend (B + zlength (f_wbuf f)) B readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail) ->
      bytes_at asegs m B (to_bytes (f_wbuf f)) ->
      bytes_at asegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31 /\ 1 <= zlength (f_wbuf f) + zlength s)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STDIO_WRITE_DEPTH -> 0x603000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 <= B -> 0 <= bufsize -> B + bufsize < 2^64 -> B + zlength (f_wbuf f) <= 2^47 ->   (* [comment removed for export] *)
      0 <= S < 2^64 -> S + zlength s <= 2^47 (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      ((B + zlength (f_wbuf f) <= lo \/ bv_unsigned sp <= B) /\ (B + zlength (f_wbuf f) <= Fp + 32 \/ Fp + 64 <= B)) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (zlength (f_wbuf f)) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (stdio_write f s) st
        (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_WRITE) fc None m (seg_rom asegs)).
  Section Sz13.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn writefn seekfn B bufsize prev next mode lbf tail s S lo canary : ltac2:(SecDiet.SzSec.tyM 'stdio_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma stdio_write_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUFB SRC -> -> -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi BWB S0 Shi LENW SEPS SEPB RSTK RFP RB RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    assert (CH' : if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)).
    { destruct (f_chan f); [exact CH | exact (proj1 CH)]. }
    assert (FD : 0 <= f_fd f < 2^31) by (destruct (f_chan f); lia).
    unfold STDIO_WRITE, STDIO_WRITE_DEPTH in *.
    unfold stdio_write. cbv zeta.
    eapply implAM_bind with
      (Q1 := sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend (B + zlength (f_wbuf f)) B
               readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m).
    2:{ intros u st' ms' POST. apply implAM_ret.
        eapply sw_tail; [exact RSTK | exact RFP | exact RIMG | exact POST | lia | lia | lia | exact FSEP1 | exact FSEP2 | lia | lia | lia | ].
        unfold zlength in *. pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC. lia. }
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    unfold fcells, file_cells in FC.
    pose proof (munch_refl (sw_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold sw_W, STDIO_WRITE_DEPTH in MU.
    unfold zlength in *.
    assert (LS : length (to_bytes s) = length s) by apply length_to_bytes.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite LS in BSRC.
    change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
    change (bytes_at asegs m B (to_bytes (f_wbuf f))) with (boxed (bytes_at asegs m B (to_bytes (f_wbuf f)))) in BUFB.
    cbn [writev_loop].
    destruct (f_wbuf f) as [|b0 wb'] eqn:EWB.
    - (* [comment removed for export] *)
      change (Z.of_nat (@length Z [])) with 0 in *. rewrite !Z.add_0_l in *. rewrite !Z.add_0_r in *.
      (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      carve_frame 112%nat ST.
      (* [comment removed for export] *)
      lazymatch goal with
      | FRx : rw_cells asegs ?mm ?A [CB 112 ?j] |- _ =>
          apply (rw_cells_split_CB asegs mm A [] 112 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
          cbn [app mk_CB_cells] in FRx;
          repeat match type of FRx with
          | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
          end
      end.
      do 12 zs. do 13 zs.
      rewrite ?Z.add_0_r. rewrite ?Z.lxor_nilpotent. try change (Z.b2z (0 <? 0)) with 0.
      replace (B - B + Z.of_nat (length s)) with (Z.of_nat (length s)) by lia.
      zs. if_true. zs. zs. rewrite (sx32_small (f_fd f)) by lia. zs. zs. zs. zs.
      step_ecall. split.
      { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
        eapply at_wnode with (A := bv_unsigned sp + -88) (iovs := [(Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
        - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
        - (* [comment removed for export] *) wn_bufs RS RB.
        - generalize CH. destruct (f_chan f); intros CHx; [exact CHx|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, LS. lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - reflexivity.
        - cbn; lia.
        - cbn [length]. lia.   (* [comment removed for export] *)
        - cbn [map concat]. rewrite app_nil_r, LS. replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
        - constructor; [|constructor]. split; [|split].
          + cbn [snd]. rewrite LS. reflexivity.
          + cbn [fst]. rewrite unsigned_lit by lia. rewrite LS. lia.   (* [comment removed for export] *)
          + cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in SRC.
            destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
            apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LS. lia. }
      intros rsp cnt Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implAM_from_evt. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x99f3c)) with (Z_to_bv 64 0x99f3c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct Hcases as [-> | Hshort].
      + rewrite Z.eqb_refl. step. if_false.
        apply evtF_done. apply implAM_ret. apply evtF_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      + replace (cnt =? Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Hq; zify_cond Hq. 2:{ exfalso. lia. }
        cbn [advance_iovs]. unfold zlength.
        replace (Z.of_nat (length s) <? cnt) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evtF_done.
        replace (Z.to_nat cnt) with (Z.to_nat (0 + cnt)) by lia.
        replace (Z.of_nat (length s) - cnt) with (Z.of_nat (length s) - 0 - cnt) by lia.
        replace (C8 (Z_to_bv 64 S)) with (C8 (Z_to_bv 64 (S + 0))) in FR by (do 2 f_equal; lia).
        replace (C8 (Z_to_bv 64 (Z.of_nat (length s)))) with (C8 (Z_to_bv 64 (Z.of_nat (length s) - 0))) in FR by (do 2 f_equal; lia).
        eapply implM_at_eq; [eapply sw_loopB with (k := 0) | ].
        all: try exact FR.
        all: lazymatch goal with |- MS _ _ _ _ _ _ _ = _ => ms_eq | _ => idtac end.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH']) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SP47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [rewrite EWB; assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC]) | rewrite EWB; unfold zlength in *; cbn [length Z.of_nat]; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RSTK]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [rewrite EWB; assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WM]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; lia]) ].
    - (* [comment removed for export] *)
      rewrite <- EWB in *.
      assert (NB1 : 1 <= Z.of_nat (length (f_wbuf f))) by (rewrite EWB; cbn [length]; lia).
      set (nb := Z.of_nat (length (f_wbuf f))) in *.
      (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      carve_frame 112%nat ST.
      (* [comment removed for export] *)
      lazymatch goal with
      | FRx : rw_cells asegs ?mm ?A [CB 112 ?j] |- _ =>
          apply (rw_cells_split_CB asegs mm A [] 112 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
          cbn [app mk_CB_cells] in FRx;
          repeat match type of FRx with
          | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
          end
      end.
      do 12 zs. do 13 zs.
      replace (B + nb - B) with nb in * by lia.
      assert (XNZ : Z.lxor (B + nb) B <> 0) by (intros E; apply Z.lxor_eq in E; lia).
      assert (XNN : 0 <= Z.lxor (B + nb) B) by (apply Z.lxor_nonneg; lia).
      replace (0 <? Z.lxor (B + nb) B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. }
      zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia. zs. zs. zs. zs.
      step_ecall. split.
      { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [IOV _] end end.
        eapply at_wnode with (A := bv_unsigned sp + -104)
          (iovs := [(Z_to_bv 64 B, Z_to_bv 64 nb); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
        - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
        - (* [comment removed for export] *) wn_bufs RS RB.
        - generalize CH. destruct (f_chan f); intros CHx; [exact CHx|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, length_app, LS, length_to_bytes. lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - reflexivity.
        - cbn; lia.
        - cbn [length]. lia.   (* [comment removed for export] *)
        - cbn [map concat]. rewrite app_nil_r, length_app, LS, length_to_bytes. replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in IOV by lia. exact IOV.
        - constructor; [|constructor; [|constructor]].
          + split; [|split].
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. rewrite length_to_bytes. subst nb. lia.   (* [comment removed for export] *)
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in BUFB. destruct SEPB as [SEP1 SEP2].
              apply (bytes_at_transport _ _ _ _ _ _ BUFB MU). cbn [disjoint_from]. rewrite length_to_bytes. lia.
          + split; [|split].
            * cbn [snd]. rewrite LS. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. rewrite LS. lia.   (* [comment removed for export] *)
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in SRC.
              destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
              apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LS. lia. }
      intros rsp cnt Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implAM_from_evt. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x99f3c)) with (Z_to_bv 64 0x99f3c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct Hcases as [-> | Hshort].
      + rewrite Z.eqb_refl. step. if_false.
        apply evtF_done. apply implAM_ret. apply evtF_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      + replace (cnt =? nb + Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Hq; zify_cond Hq. 2:{ exfalso. lia. }
        apply evtF_done.
        replace (nb + Z.of_nat (length s) - cnt) with (nb - 0 + Z.of_nat (length s) - cnt) by lia.
        replace (C8 (Z_to_bv 64 B)) with (C8 (Z_to_bv 64 (B + 0))) in FR by (do 2 f_equal; lia).
        replace (C8 (Z_to_bv 64 nb)) with (C8 (Z_to_bv 64 (nb - 0))) in FR by (do 2 f_equal; lia).
          eapply implM_at_eq; [eapply sw_loopA with (k := 0) | ].
        all: try exact FR.
        all: lazymatch goal with |- MS _ _ _ _ _ _ _ = _ => ms_eq | _ => idtac end.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH']) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SP47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RSTK]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WM]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [subst nb; unfold zlength in *; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [subst nb; unfold zlength in *; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [subst nb; unfold zlength in *; lia]) ].
  Qed.
  End Sz13.
  Theorem stdio_write_spec : ltac:(let t := eval cbv delta [stdio_write_spec__stmt] in stdio_write_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn writefn seekfn B bufsize prev next mode lbf tail s S lo canary. ltac2:(SecDiet.SzSec.closeP 'stdio_write_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Entry.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_WRITE : Z := 0x9a290.
Definition STDIO_WRITE_DEPTH : Z := 112.
Definition SW_SHORT : Z := 0x9a3b0.   (* [comment removed for export] *)
Definition SW_OK : Z := 0x9a324.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition wdec_Some__stmt : Prop := forall f rem rsp cnt,
  wdec f rem rsp = Some cnt ->
  rsp = eff0 (Z_to_bv 64 cnt) /\ 0 <= cnt <= rem /\ 0 <= cnt < 2^64 /\ (cnt = rem \/ 1 <= cnt < rem).
Section Sz1.
Variables f rem rsp cnt : ltac2:(SecDiet.SzSec.tyM 'wdec_Some__stmt "vvvv" @f).
#[using="Type"] Lemma wdec_Some__body : ltac2:(SecDiet.SzSec.bodyP 'wdec_Some__stmt "vvvv").
Proof.
  intros H.
 unfold wdec in H. destruct (f_chan f).
  - apply dec_writev_Some in H as (Hr & -> & Hc). split; [reflexivity|]. lia.
  - unfold dec_writevf_ok, dec_writevf in H.
    destruct (dec_plain (fun v => v =? rem) rsp) as [[e|v]|] eqn:E; try discriminate H.
    injection H as <-. apply dec_plain_Some in E as (-> & Hok & Hv).
    apply Z.eqb_eq in Hok. subst v. split; [reflexivity|]. lia.
Qed.
End Sz1.
Lemma wdec_Some : ltac:(let t := eval cbv delta [wdec_Some__stmt] in wdec_Some__stmt in exact t).
Proof. intros f rem rsp cnt. ltac2:(SecDiet.SzSec.closeP 'wdec_Some__body "vvvv"). Qed.

(* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT}.
Definition at_wnode__stmt : Prop := forall RNG f L (R F : bvmap 5 word) pc fc m (A : Z) (iovs : list (word * word)),
  rng RNG A (16 * Z.of_nat (length L)) ->
  Forall2 (fun (iov : word * word) (bs : list byte) => rng RNG (bv_unsigned (fst iov)) (Z.of_nat (length bs))) iovs (map to_bytes L) ->
  (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^32 /\ 1 <= Z.of_nat (length (concat (map to_bytes L))))) ->
  reg_get R 10 = Z_to_bv 64 (f_fd f) ->
  reg_get R 11 = Z_to_bv 64 A -> 0 <= A < 2^64 ->
  reg_get R 12 = Z_to_bv 64 (Z.of_nat (length L)) ->
  (1 <= length L <= 2)%nat ->
  A + 16 * Z.of_nat (length L) <= 2^47 ->   (* [comment removed for export] *)
  Z.of_nat (length (concat (map to_bytes L))) <= max_write ->
  bytes_at asegs m A (iovec_bytes iovs) ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47   (* [comment removed for export] *)
                         /\ bytes_at asegs m (bv_unsigned (fst iov)) bs) iovs (map to_bytes L) ->
  at_nodeA asegs (wnode f L) RNG (MSsvc R F pc (Z_to_bv 64 66) fc None m (seg_rom asegs)).
Section Sz2.
Variables RNG f L R F pc fc m A iovs : ltac2:(SecDiet.SzSec.tyM 'at_wnode__stmt "vvvvvvvvvv" @RNG).
#[using="Type"] Lemma at_wnode__body : ltac2:(SecDiet.SzSec.bodyP 'at_wnode__stmt "vvvvvvvvvv").
Proof.
  intros RA HR CH R10 R11 HA R12 HL HA47 HT HIOV HF.
  assert (HF4 : Forall2 (fun (iov : word * word) (bs : list byte) => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47
                 /\ bytes_at asegs m (bv_unsigned (fst iov)) bs /\ rng RNG (bv_unsigned (fst iov)) (Z.of_nat (length bs))) iovs (map to_bytes L)).
  { clear -HF HR. induction HF as [|iov bs iovs' bss (H1 & H2 & H3) HF IH]; [constructor|].
    inversion HR as [|? ? ? ? HR1 HR2]; subst. constructor; [exact (conj H1 (conj H2 (conj H3 HR1)))| exact (IH HR2)]. }
  unfold wnode. destruct (f_chan f).
  - cbn [at_nodeA]. unfold at_gatherA, areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS].
    rewrite R10, R11, R12, length_map. rewrite unsigned_lit by lia.
    repeat (split; [first [reflexivity | exact RA | assumption | lia]|]). exists iovs. split; assumption.
  - destruct CH as [FD TOT]. cbn [at_nodeA]. unfold at_gatherA, areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS].
    rewrite R10, R11, R12, length_map. rewrite unsigned_lit by lia.
    repeat (split; [first [reflexivity | exact RA | assumption | lia]|]). exists iovs. split; assumption.
Qed.
End Sz2.
#[using="Type"] Lemma at_wnode : ltac:(let t := eval cbv delta [at_wnode__stmt] in at_wnode__stmt in exact t).
Proof. intros RNG f L R F pc fc m A iovs. ltac2:(SecDiet.SzSec.closeP 'at_wnode__body "vvvvvvvvvv"). Qed.
End CANSEC0.

(* [comment removed for export] *)
Definition iov_bytes2__stmt : Prop := forall m A j8 (w0 w1 w2 w3 : word) rest,
  rw_cells asegs m A (CB 8 j8 :: C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: rest) ->
  bytes_at asegs m (A + 8) (iovec_bytes [(w0, w1); (w2, w3)]) /\ bytes_at asegs m (A + 24) (iovec_bytes [(w2, w3)]).
Section Sz3.
Variables m A j8 w0 w1 w2 w3 rest : ltac2:(SecDiet.SzSec.tyM 'iov_bytes2__stmt "vvvvvvvv" @m).
#[using="Type"] Lemma iov_bytes2__body : ltac2:(SecDiet.SzSec.bodyP 'iov_bytes2__stmt "vvvvvvvv").
Proof.
  intros FR.
  destruct FR as [[WF FB] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _].
  cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
  apply bytes_at_app in FB as [FB0 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB3 _].
  cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r. split.
  - apply bytes_at_app. rewrite length_app, !length_le8. split.
    + apply bytes_at_app. rewrite length_le8. split.
      * replace (A + 8) with (A + Z.of_nat 8) by lia. exact FB0.
      * replace (A + 8 + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB1.
    + apply bytes_at_app. rewrite length_le8. split.
      * replace (A + 8 + Z.of_nat (8 + 8)) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
      * replace (A + 8 + Z.of_nat (8 + 8) + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
  - apply bytes_at_app. rewrite length_le8. split.
    + replace (A + 24) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
    + replace (A + 24 + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
Qed.
End Sz3.
Lemma iov_bytes2 : ltac:(let t := eval cbv delta [iov_bytes2__stmt] in iov_bytes2__stmt in exact t).
Proof. intros m A j8 w0 w1 w2 w3 rest. ltac2:(SecDiet.SzSec.closeP 'iov_bytes2__body "vvvvvvvv"). Qed.

Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_skipn : forall m A bs n, bytes_at asegs m A bs -> (n <= length bs)%nat ->
  bytes_at asegs m (A + Z.of_nat n) (skipn n bs).
Proof.
  intros m A bs n H Hn. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H as [_ H].
  rewrite firstn_length_le in H by lia. exact H.
Qed.


Ltac wn_clr := repeat match goal with H : context [implAM] |- _ => clear H end.
Ltac wn_bufs RS RB :=
  wn_clr; cbn [map];
  repeat first [ apply Forall2_nil
               | apply Forall2_cons;
                 [ cbn [fst]; rewrite ?unsigned_lit by (unfold zlength in *; lia); rewrite ?length_to_bytes, ?length_skipn;
                   first [ eapply rng_sub'; [exact RS | unfold zlength in *; lia]
                         | eapply rng_sub'; [exact RB | unfold zlength in *; lia] ] |] ].

Section StdioWrite.
  Context {rc : runConstT}.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition fcells (flags : word) (rpos rend closefn : Z) (wend wpos wbase : Z)
      (readfn writefn seekfn B bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
    file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next fd mode lbf tail.

  Definition sw_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)].

  (* [comment removed for export] *)
  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn readfn writefn seekfn B bufsize prev next : Z) (mode : word) (lbf : Z) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => f' = set_w true [] f /\ st' = st /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (sw_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags rpos rend closefn (B + bufsize) B B readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail)
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition sw_ok_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z) (mode : word) (lbf : Z) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word) (j8 : list byte) (w0 w1 w2 w3 : word) (m' : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 SW_OK) fc None m' (seg_rom asegs)
      /\ munch (sw_W sp Fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp + -112)
      /\ rw_cells asegs m' (bv_unsigned sp + -112)
           [CB 8 j8; C8 w0; C8 w1; C8 w2; C8 w3; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' Fp (fcells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail)
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition sw_tail__stmt : Prop := forall RNG (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st st' : St) (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z)
      (mode : word) (lbf : Z) (tail : list byte) (len lo : Z) (canary : word) (m : mem) ms u,
    rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng_aimg RNG ->
    sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m u st' ms ->
    (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (lo <= bv_unsigned sp - 112) ->
    (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
    (0 <= B) -> (0 <= bufsize) -> (B + bufsize < 2^64) -> (0 <= len < 2^64) ->
    evtF asegs RNG (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m (set_w true [] f) st') ms.
  Section Sz7.
  Variables RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st st' Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m ms u : ltac2:(SecDiet.SzSec.tyM 'sw_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma sw_tail__body : ltac2:(SecDiet.SzSec.bodyP 'sw_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros RSTK RFP RIMG POST Fp0 FPLO LO FSEP1 FSEP2 B0 BS0 BShi LEN.
    destruct POST as [-> POST]. destruct_exs POST.
    destruct POST as (-> & MU & WM & MI & ST & FR & FC & [GOT GUARD]).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold fcells, file_cells in FC. unfold got_ssp, ssp_guard, SW_OK in *.
    rename x23 into m1. unfold sw_W, STDIO_WRITE_DEPTH in MU.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size csize Nat.add] in FB.
    do 7 step.
    (* [comment removed for export] *)
    step. step. step. if_false.
    do 10 step.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold stdio_write_post, fcells, file_cells. split; [reflexivity|]. split; [reflexivity|].
    sys_finish. split; [exact GOT | exact GUARD].
  Qed.
  End Sz7.
  Lemma sw_tail : ltac:(let t := eval cbv delta [sw_tail__stmt] in sw_tail__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st st' Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m ms u. ltac2:(SecDiet.SzSec.closeP 'sw_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Section Loop.
    Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z)
              (mode : word) (lbf : Z) (tail : list byte) (s : list Z) (S lo : Z) (canary : word) (m : mem).
    #[local] Notation len := (zlength s) (only parsing).
    #[local] Notation wb := (f_wbuf f) (only parsing).
    #[local] Notation FCELLS := (fcells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail) (only parsing).
    #[local] Notation QOK := (sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend wpos wbase
                 readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m) (only parsing).

    Hypothesis CH : if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31).
    Hypothesis LO : lo <= bv_unsigned sp - 112.
    Hypothesis SP47 : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
    Hypothesis GLO : 0x604000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
    Hypothesis S0 : 0 <= S < 2^64.
    Hypothesis Shi : S + len <= 2^47.   (* [comment removed for export] *)
    Hypothesis LENW : zlength wb + len <= 2^26.
    Hypothesis SEPS : s = [] \/ ((S + len <= lo \/ bv_unsigned sp <= S) /\ (S + len <= Fp + 32 \/ Fp + 64 <= S)).
    Hypothesis SRC : bytes_at asegs m S (to_bytes s).      (* [comment removed for export] *)
    Hypothesis B0 : 0 <= B.
    Hypothesis BWB : B + zlength wb <= 2^47.   (* [comment removed for export] *)
    Hypothesis SEPB : (B + zlength wb <= lo \/ bv_unsigned sp <= B) /\ (B + zlength wb <= Fp + 32 \/ Fp + 64 <= B).
    Hypothesis BUFB : bytes_at asegs m B (to_bytes wb).    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFP : rng RNG Fp 232.
    Hypothesis RB : rng RNG B (zlength wb).
    Hypothesis RS : rng RNG S len.
    Hypothesis RIMG : rng_aimg RNG.

    Definition src_at__stmt : Prop := forall m1 k, munch (sw_W sp Fp) m m1 -> 0 <= k <= len ->
      bytes_at asegs m1 (S + k) (to_bytes (skipn (Z.to_nat k) s)).
    Section Sz8.
    Variables m1 k : ltac2:(SecDiet.SzSec.tyM 'src_at__stmt "vv" @m1).
    Lemma src_at__body : ltac2:(SecDiet.SzSec.bodyP 'src_at__stmt "vv").
    Proof using FPLO LENW LO S0 SEPB SEPS SRC Shi. pin_using (fun (FPLO LENW LO S0 SEPB SEPS SRC Shi : unit) => tt).
      intros MU Hk.
 rewrite to_bytes_skipn.
      replace (S + k) with (S + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skipn; [| rewrite length_to_bytes; unfold zlength in Hk; lia].
      clear RS. destruct SEPS as [-> | [SEP1 SEP2]].
      - apply bytes_at_nil. lia.
      - apply (bytes_at_transport _ _ _ m1 _ _ SRC MU). unfold sw_W, STDIO_WRITE_DEPTH. cbn [disjoint_from].
        rewrite length_to_bytes. unfold zlength in *. lia.
    Qed.
    End Sz8.
    Lemma src_at : ltac:(let t := eval cbv delta [src_at__stmt] in src_at__stmt in exact t).
    Proof using FPLO LENW LO S0 SEPB SEPS SRC Shi. intros m1 k. ltac2:(SecDiet.SzSec.closeP 'src_at__body "vv"). Qed.

    Definition buf_at__stmt : Prop := forall m1 k, munch (sw_W sp Fp) m m1 -> 0 <= k <= zlength wb ->
      bytes_at asegs m1 (B + k) (to_bytes (skipn (Z.to_nat k) wb)).
    Section Sz9.
    Variables m1 k : ltac2:(SecDiet.SzSec.tyM 'buf_at__stmt "vv" @m1).
    Lemma buf_at__body : ltac2:(SecDiet.SzSec.bodyP 'buf_at__stmt "vv").
    Proof using B0 BUFB BWB FPLO LENW LO SEPB SP47. pin_using (fun (B0 BUFB BWB FPLO LENW LO SEPB SP47 : unit) => tt).
      intros MU Hk.
 rewrite to_bytes_skipn.
      replace (B + k) with (B + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skipn; [| rewrite length_to_bytes; unfold zlength in Hk; lia].
      clear RB. destruct (f_wbuf f) as [|b0 wb'] eqn:EWB.
      - apply bytes_at_nil. lia.
      - destruct SEPB as [SEP1 SEP2].
        apply (bytes_at_transport _ _ _ m1 _ _ BUFB MU). unfold sw_W, STDIO_WRITE_DEPTH. cbn [disjoint_from].
        rewrite length_to_bytes. unfold zlength in *. cbn [length] in *. lia.
    Qed.
    End Sz9.
    Lemma buf_at : ltac:(let t := eval cbv delta [buf_at__stmt] in buf_at__stmt in exact t).
    Proof using B0 BUFB BWB FPLO LENW LO SEPB SP47. intros m1 k. ltac2:(SecDiet.SzSec.closeP 'buf_at__body "vv"). Qed.

    (* [comment removed for export] *)
    Lemma sw_loopB : forall fuel (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (j8 : list byte) (w0 w1 : word)
        (k cnt : Z) (m1 : mem),
      rw_cells asegs m1 (bv_unsigned sp + -112)
        [CB 8 j8; C8 w0; C8 w1; C8 (Z_to_bv 64 (S + k)); C8 (Z_to_bv 64 (len - k)); C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m1 Fp FCELLS ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -112) -> mem_inv asegs m1 ->
      munch (sw_W sp Fp) m m1 -> wmono asegs m m1 ->
      0 <= k -> 1 <= cnt -> k + cnt < len ->
      implAM RNG (writev_loop fuel f [skipn (Z.to_nat (k + cnt)) s] (len - k - cnt)) st QOK
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -88)) x20 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (len - k))
                 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_SHORT) fc None m1 (seg_rom asegs)).
    Proof using CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi RSTK RFP RB RS RIMG. pin_using (fun (CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi : unit) => tt).
      induction fuel as [|fuel IH]; intros until m1; intros FR FC SSP ST MI MU WM K0 C1 KC.
      { cbn [writev_loop]. apply implAM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, SW_SHORT in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold sw_W, STDIO_WRITE_DEPTH in MU.
      cbn [writev_loop]. (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      unfold zlength in *.
      assert (LS : Z.of_nat (length (to_bytes s)) = Z.of_nat (length s)) by (rewrite length_to_bytes; reflexivity).
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. clear IH. lia. }
      zs. zs.
      replace (Z.of_nat (length s) - k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      assert (FD : 0 <= f_fd f < 2^31) by (clear IH; destruct (f_chan f); lia).
      zs. zs.
      zs. zs. zs. rewrite Z.land_0_l. zs. rewrite Z.sub_0_r. zs. zs.
      zs. if_cases Hb; zify_cond Hb. 2:{ exfalso. clear IH. lia. }
      zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
      zs. zs. zs. zs. zs.
      step_ecall. split.
      { (* [comment removed for export] *)
        lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
        eapply at_wnode with (A := bv_unsigned sp + -88)
          (iovs := [(Z_to_bv 64 (S + k + cnt), Z_to_bv 64 (Z.of_nat (length s) - k - cnt))]).
        - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
        - (* [comment removed for export] *) wn_bufs RS RB.
        - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn. lia.
        - reflexivity.
        - reflexivity.
        - clear IH; lia.
        - reflexivity.
        - cbn; lia.
        - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
        - clear IH. cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn.
          replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
        - constructor; [|constructor]. split; [|split].
          + cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. clear IH; lia.
          + cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes, length_skipn. clear IH; lia.   (* [comment removed for export] *)
          + cbn [fst]. rewrite unsigned_lit by (clear IH; lia).
            replace (S + k + cnt) with (S + (k + cnt)) by lia. apply src_at; [exact MU | clear IH; unfold zlength; lia]. }
      (* [comment removed for export] *)
      intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implAM_from_evt. sys_nret.
      (* [comment removed for export] *)
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x9a3a8)) with (Z_to_bv 64 0x9a3a8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zs. zs.
      destruct Hcases as [-> | Hshort].
      - (* [comment removed for export] *)
        rewrite Z.eqb_refl. if_true.
        apply evtF_done. apply implAM_ret. apply evtF_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      - (* [comment removed for export] *)
        replace (cnt' =? Z.of_nat (length s) - k - cnt) with false by (symmetry; apply Z.eqb_neq; lia).
        if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
        cbn [advance_iovs].
        replace (zlength (skipn (Z.to_nat (k + cnt)) s) <? cnt') with false.
        2:{ symmetry. apply Z.ltb_ge. unfold zlength. rewrite length_skipn. clear IH. lia. }
        rewrite skipn_skipn.
        replace (Z.to_nat cnt' + Z.to_nat (k + cnt))%nat with (Z.to_nat ((k + cnt) + cnt')) by lia.
        replace (Z.of_nat (length s) - k - cnt - cnt') with (Z.of_nat (length s) - (k + cnt) - cnt') by lia.
        replace (Z.of_nat (length s) - k - cnt) with (Z.of_nat (length s) - (k + cnt)) in * by lia.
        replace (S + k + cnt) with (S + (k + cnt)) in * by lia.
        apply evtF_done. eapply IH; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | lia | lia | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma sw_loopA : forall fuel (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (j8 : list byte)
        (k cnt : Z) (m1 : mem),
      rw_cells asegs m1 (bv_unsigned sp + -112)
        [CB 8 j8; C8 (Z_to_bv 64 (B + k)); C8 (Z_to_bv 64 (zlength wb - k)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 len); C8 canary;
         C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs m1 Fp FCELLS ->
      ssp_cells m1 canary -> stk asegs m1 lo (bv_unsigned sp + -112) -> mem_inv asegs m1 ->
      munch (sw_W sp Fp) m m1 -> wmono asegs m m1 ->
      0 <= k <= zlength wb -> 1 <= cnt -> k + cnt < zlength wb + len ->
      implAM RNG (writev_loop fuel f (advance_iovs [skipn (Z.to_nat k) wb; s] cnt) (zlength wb - k + len - cnt)) st QOK
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -104)) x20 (Z_to_bv 64 ssp_guard)
                 (Z_to_bv 64 (zlength wb - k + len)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_SHORT) fc None m1 (seg_rom asegs)).
    Proof using B0 BUFB BWB CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi RSTK RFP RB RS RIMG. pin_using (fun (B0 BUFB BWB CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi : unit) => tt).
      induction fuel as [|fuel IH]; intros until m1; intros FR FC SSP ST MI MU WM K0 C1 KC.
      { cbn [writev_loop]. destruct (zlength (skipn (Z.to_nat k) wb) <? cnt); apply implAM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, SW_SHORT in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold sw_W, STDIO_WRITE_DEPTH in MU.
      unfold zlength in *.
      assert (FD : 0 <= f_fd f < 2^31) by (clear IH; destruct (f_chan f); lia).
      cbn [writev_loop]. (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. clear IH. lia. }
      zs. zs.
      destruct (Z.le_gt_cases cnt (Z.of_nat (length (f_wbuf f)) - k)) as [LE | GT].
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (f_wbuf f)) - k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
        cbn [advance_iovs]. unfold zlength. rewrite length_skipn.
        replace (Z.of_nat (length (f_wbuf f) - Z.to_nat k) <? cnt) with false by (symmetry; apply Z.ltb_ge; clear IH; lia).
        zs. zs.
        zs. zs. zs. rewrite Z.land_0_l. zs. rewrite Z.sub_0_r. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 2:{ exfalso. clear IH. lia. }
        zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
        zs. zs. zs. zs. zs.
        step_ecall. split.
        { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
            lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
              pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [IOV _] end end.
          eapply at_wnode with (A := bv_unsigned sp + -104)
            (iovs := [(Z_to_bv 64 (B + k + cnt), Z_to_bv 64 (Z.of_nat (length (f_wbuf f)) - k - cnt));
                      (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
          - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
          - (* [comment removed for export] *) wn_bufs RS RB.
          - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
            cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn. lia.
          - reflexivity.
          - reflexivity.
          - clear IH; lia.
          - reflexivity.
          - cbn; lia.
          - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
          - clear IH. cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn.
            replace max_write with 67108864 by reflexivity. lia.
          - replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in IOV by lia. exact IOV.
          - constructor; [|constructor; [|constructor]].
            + split; [|split].
              * cbn [snd]. rewrite length_to_bytes, !length_skipn. f_equal. clear IH; lia.
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes, !length_skipn. clear IH; lia.   (* [comment removed for export] *)
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite skipn_skipn.
                replace (Z.to_nat cnt + Z.to_nat k)%nat with (Z.to_nat (k + cnt)) by lia.
                replace (B + k + cnt) with (B + (k + cnt)) by lia. apply buf_at; [exact MU | clear IH; unfold zlength; lia].
            + split; [|split].
              * cbn [snd]. rewrite length_to_bytes. reflexivity.
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes. clear IH; lia.   (* [comment removed for export] *)
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia).
                pose proof (src_at _ 0 MU) as SR. specialize (SR ltac:(clear IH; unfold zlength; lia)). cbn [Z.to_nat skipn] in SR.
                rewrite Z.add_0_r in SR. exact SR. }
       
        intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
        unfold eff0. apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x9a3a8)) with (Z_to_bv 64 0x9a3a8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. zs.
        destruct Hcases as [-> | Hshort].
        + rewrite Z.eqb_refl. if_true.
          apply evtF_done. apply implAM_ret. apply evtF_done.
          unfold sw_ok_post. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
        + replace (cnt' =? Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt) with false by (symmetry; apply Z.eqb_neq; lia).
          if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
          rewrite skipn_skipn.
          replace (Z.to_nat cnt + Z.to_nat k)%nat with (Z.to_nat (k + cnt)) by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt - cnt')
            with (Z.of_nat (length (f_wbuf f)) - (k + cnt) + Z.of_nat (length s) - cnt') by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt)
            with (Z.of_nat (length (f_wbuf f)) - (k + cnt) + Z.of_nat (length s)) in * by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k - cnt) with (Z.of_nat (length (f_wbuf f)) - (k + cnt)) in * by lia.
          replace (B + k + cnt) with (B + (k + cnt)) in * by lia.
          apply evtF_done. eapply IH; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | lia | lia | lia].
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (f_wbuf f)) - k <? cnt) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        cbn [advance_iovs]. unfold zlength. rewrite length_skipn.
        replace (Z.of_nat (length (f_wbuf f) - Z.to_nat k) <? cnt) with true by (symmetry; apply Z.ltb_lt; clear IH; lia).
        zs. zs.
        zs. zs. zs.
        replace (Z.land 18446744073709551615 (Z.of_nat (length (f_wbuf f)) - k)) with (Z.of_nat (length (f_wbuf f)) - k).
        2:{ rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. clear IH; lia. }
        zs. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. clear IH. lia. }
        zs. zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
        zs. zs. zs. zs. zs.
        set (kB := cnt - (Z.of_nat (length (f_wbuf f)) - k)) in *.
        step_ecall. split.
        { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
            lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
              pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
          eapply at_wnode with (A := bv_unsigned sp + -88)
            (iovs := [(Z_to_bv 64 (S + kB), Z_to_bv 64 (Z.of_nat (length s) - kB))]).
          - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
          - (* [comment removed for export] *) wn_bufs RS RB.
          - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
            cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn. subst kB. lia.
          - reflexivity.
          - reflexivity.
          - clear IH; lia.
          - cbn [length]. reflexivity.
          - cbn; lia.
          - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
          - clear IH. cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn.
            replace max_write with 67108864 by reflexivity. subst kB. lia.
          - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
          - constructor; [|constructor]. split; [|split].
            + cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. clear IH; subst kB; lia.
            + cbn [fst]. rewrite unsigned_lit by (clear IH; subst kB; lia). rewrite length_to_bytes, length_skipn. clear IH; subst kB; lia.   (* [comment removed for export] *)
            + cbn [fst]. rewrite unsigned_lit by (clear IH; subst kB; lia).
              replace (Z.to_nat (cnt - Z.of_nat (length (f_wbuf f) - Z.to_nat k))) with (Z.to_nat kB) by (subst kB; clear IH; lia).
              apply src_at; [exact MU | clear IH; subst kB; unfold zlength; lia]. }
        intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
        unfold eff0. apply implAM_from_evt. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x9a3a8)) with (Z_to_bv 64 0x9a3a8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. zs. 
        replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt) with (Z.of_nat (length s) - kB) in * by (subst kB; lia).
        
        replace (Z.to_nat (cnt - Z.of_nat (length (f_wbuf f) - Z.to_nat k))) with (Z.to_nat kB) by (subst kB; clear IH; lia).
        
        destruct Hcases as [-> | Hshort].
        + rewrite Z.eqb_refl. if_true. 
          apply evtF_done. apply implAM_ret. apply evtF_done.
          unfold sw_ok_post. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
        + replace (cnt' =? Z.of_nat (length s) - kB) with false by (symmetry; apply Z.eqb_neq; lia).
          if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
          cbn [advance_iovs]. 
          replace (zlength (skipn (Z.to_nat kB) s) <? cnt') with false.
          2:{ symmetry. apply Z.ltb_ge. unfold zlength. rewrite length_skipn. clear IH. subst kB. lia. }
          rewrite skipn_skipn.
          replace (Z.to_nat cnt' + Z.to_nat kB)%nat with (Z.to_nat (kB + cnt')) by (clear IH; subst kB; lia).
          replace (Z.of_nat (length s) - kB - cnt') with (Z.of_nat (length s) - kB - cnt') by lia.
          apply evtF_done.
          eapply sw_loopB; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | clear IH; subst kB; lia | clear IH; subst kB; lia | clear IH; subst kB; unfold zlength; lia].
    Qed.
  End Loop.
End StdioWrite.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Context {rc : runConstT}.
  Context {St : Type}.

  Lemma implM_at_eq : forall {A} RNG (c : M St A) s Q ms ms', implAM RNG c s Q ms' -> ms = ms' -> implAM RNG c s Q ms.
  Proof using Type. pin_using tt. intros A RNG c s Q ms ms' H ->. exact H. Qed.

  Ltac ms_eq := cbv delta [mkR]; repeat fastfirst (first [reflexivity | progress f_equal | unfold zlength in *; lia]).

  Definition stdio_write_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn wend readfn writefn seekfn B bufsize prev next : Z)
           (mode : word) (lbf : Z) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn wend (B + zlength (f_wbuf f)) B readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail) ->
      bytes_at asegs m B (to_bytes (f_wbuf f)) ->
      bytes_at asegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31 /\ 1 <= zlength (f_wbuf f) + zlength s)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STDIO_WRITE_DEPTH -> 0x604000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 <= B -> 0 <= bufsize -> B + bufsize < 2^64 -> B + zlength (f_wbuf f) <= 2^47 ->   (* [comment removed for export] *)
      0 <= S < 2^64 -> S + zlength s <= 2^47 (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      ((B + zlength (f_wbuf f) <= lo \/ bv_unsigned sp <= B) /\ (B + zlength (f_wbuf f) <= Fp + 32 \/ Fp + 64 <= B)) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (zlength (f_wbuf f)) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (stdio_write f s) st
        (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_WRITE) fc None m (seg_rom asegs)).
  Section Sz13.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn writefn seekfn B bufsize prev next mode lbf tail s S lo canary : ltac2:(SecDiet.SzSec.tyM 'stdio_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma stdio_write_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUFB SRC -> -> -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi BWB S0 Shi LENW SEPS SEPB RSTK RFP RB RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    assert (CH' : if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)).
    { destruct (f_chan f); [exact CH | exact (proj1 CH)]. }
    assert (FD : 0 <= f_fd f < 2^31) by (destruct (f_chan f); lia).
    unfold STDIO_WRITE, STDIO_WRITE_DEPTH in *.
    unfold stdio_write. cbv zeta.
    eapply implAM_bind with
      (Q1 := sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend (B + zlength (f_wbuf f)) B
               readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m).
    2:{ intros u st' ms' POST. apply implAM_ret.
        eapply sw_tail; [exact RSTK | exact RFP | exact RIMG | exact POST | lia | lia | lia | exact FSEP1 | exact FSEP2 | lia | lia | lia | ].
        unfold zlength in *. pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC. lia. }
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    unfold fcells, file_cells in FC.
    pose proof (munch_refl (sw_W sp Fp) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold sw_W, STDIO_WRITE_DEPTH in MU.
    unfold zlength in *.
    assert (LS : length (to_bytes s) = length s) by apply length_to_bytes.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite LS in BSRC.
    change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
    change (bytes_at asegs m B (to_bytes (f_wbuf f))) with (boxed (bytes_at asegs m B (to_bytes (f_wbuf f)))) in BUFB.
    cbn [writev_loop].
    destruct (f_wbuf f) as [|b0 wb'] eqn:EWB.
    - (* [comment removed for export] *)
      change (Z.of_nat (@length Z [])) with 0 in *. rewrite !Z.add_0_l in *. rewrite !Z.add_0_r in *.
      (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      carve_frame 112%nat ST.
      (* [comment removed for export] *)
      lazymatch goal with
      | FRx : rw_cells asegs ?mm ?A [CB 112 ?j] |- _ =>
          apply (rw_cells_split_CB asegs mm A [] 112 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
          cbn [app mk_CB_cells] in FRx;
          repeat match type of FRx with
          | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
          end
      end.
      do 12 zs. do 13 zs.
      rewrite ?Z.add_0_r. rewrite ?Z.lxor_nilpotent. try change (Z.b2z (0 <? 0)) with 0.
      replace (B - B + Z.of_nat (length s)) with (Z.of_nat (length s)) by lia.
      zs. if_true. zs. zs. rewrite (sx32_small (f_fd f)) by lia. zs. zs. zs. zs.
      step_ecall. split.
      { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
        eapply at_wnode with (A := bv_unsigned sp + -88) (iovs := [(Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
        - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
        - (* [comment removed for export] *) wn_bufs RS RB.
        - generalize CH. destruct (f_chan f); intros CHx; [exact CHx|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, LS. lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - reflexivity.
        - cbn; lia.
        - cbn [length]. lia.   (* [comment removed for export] *)
        - cbn [map concat]. rewrite app_nil_r, LS. replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
        - constructor; [|constructor]. split; [|split].
          + cbn [snd]. rewrite LS. reflexivity.
          + cbn [fst]. rewrite unsigned_lit by lia. rewrite LS. lia.   (* [comment removed for export] *)
          + cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in SRC.
            destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
            apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LS. lia. }
      intros rsp cnt Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implAM_from_evt. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x9a320)) with (Z_to_bv 64 0x9a320 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct Hcases as [-> | Hshort].
      + rewrite Z.eqb_refl. step. if_false.
        apply evtF_done. apply implAM_ret. apply evtF_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      + replace (cnt =? Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Hq; zify_cond Hq. 2:{ exfalso. lia. }
        cbn [advance_iovs]. unfold zlength.
        replace (Z.of_nat (length s) <? cnt) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evtF_done.
        replace (Z.to_nat cnt) with (Z.to_nat (0 + cnt)) by lia.
        replace (Z.of_nat (length s) - cnt) with (Z.of_nat (length s) - 0 - cnt) by lia.
        replace (C8 (Z_to_bv 64 S)) with (C8 (Z_to_bv 64 (S + 0))) in FR by (do 2 f_equal; lia).
        replace (C8 (Z_to_bv 64 (Z.of_nat (length s)))) with (C8 (Z_to_bv 64 (Z.of_nat (length s) - 0))) in FR by (do 2 f_equal; lia).
        eapply implM_at_eq; [eapply sw_loopB with (k := 0) | ].
        all: try exact FR.
        all: lazymatch goal with |- MS _ _ _ _ _ _ _ = _ => ms_eq | _ => idtac end.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH']) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SP47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [rewrite EWB; assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC]) | rewrite EWB; unfold zlength in *; cbn [length Z.of_nat]; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RSTK]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [rewrite EWB; assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WM]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold zlength in *; lia]) ].
    - (* [comment removed for export] *)
      rewrite <- EWB in *.
      assert (NB1 : 1 <= Z.of_nat (length (f_wbuf f))) by (rewrite EWB; cbn [length]; lia).
      set (nb := Z.of_nat (length (f_wbuf f))) in *.
      (apply implAM_sysk; [first [exact I | unfold wnode; destruct (f_chan _); exact I]|]).
      carve_frame 112%nat ST.
      (* [comment removed for export] *)
      lazymatch goal with
      | FRx : rw_cells asegs ?mm ?A [CB 112 ?j] |- _ =>
          apply (rw_cells_split_CB asegs mm A [] 112 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
          cbn [app mk_CB_cells] in FRx;
          repeat match type of FRx with
          | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
          end
      end.
      do 12 zs. do 13 zs.
      replace (B + nb - B) with nb in * by lia.
      assert (XNZ : Z.lxor (B + nb) B <> 0) by (intros E; apply Z.lxor_eq in E; lia).
      assert (XNN : 0 <= Z.lxor (B + nb) B) by (apply Z.lxor_nonneg; lia).
      replace (0 <? Z.lxor (B + nb) B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. }
      zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia. zs. zs. zs. zs.
      step_ecall. split.
      { lazymatch goal with |- at_nodeA _ _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells asegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [IOV _] end end.
        eapply at_wnode with (A := bv_unsigned sp + -104)
          (iovs := [(Z_to_bv 64 B, Z_to_bv 64 nb); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
        - (* [comment removed for export] *) wn_clr; eapply rng_sub'; [exact RSTK | cbn [length]; lia].
        - (* [comment removed for export] *) wn_bufs RS RB.
        - generalize CH. destruct (f_chan f); intros CHx; [exact CHx|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, length_app, LS, length_to_bytes. lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - reflexivity.
        - cbn; lia.
        - cbn [length]. lia.   (* [comment removed for export] *)
        - cbn [map concat]. rewrite app_nil_r, length_app, LS, length_to_bytes. replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in IOV by lia. exact IOV.
        - constructor; [|constructor; [|constructor]].
          + split; [|split].
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. rewrite length_to_bytes. subst nb. lia.   (* [comment removed for export] *)
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in BUFB. destruct SEPB as [SEP1 SEP2].
              apply (bytes_at_transport _ _ _ _ _ _ BUFB MU). cbn [disjoint_from]. rewrite length_to_bytes. lia.
          + split; [|split].
            * cbn [snd]. rewrite LS. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. rewrite LS. lia.   (* [comment removed for export] *)
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in SRC.
              destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
              apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LS. lia. }
      intros rsp cnt Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implAM_from_evt. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x9a320)) with (Z_to_bv 64 0x9a320 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct Hcases as [-> | Hshort].
      + rewrite Z.eqb_refl. step. if_false.
        apply evtF_done. apply implAM_ret. apply evtF_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      + replace (cnt =? nb + Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Hq; zify_cond Hq. 2:{ exfalso. lia. }
        apply evtF_done.
        replace (nb + Z.of_nat (length s) - cnt) with (nb - 0 + Z.of_nat (length s) - cnt) by lia.
        replace (C8 (Z_to_bv 64 B)) with (C8 (Z_to_bv 64 (B + 0))) in FR by (do 2 f_equal; lia).
        replace (C8 (Z_to_bv 64 nb)) with (C8 (Z_to_bv 64 (nb - 0))) in FR by (do 2 f_equal; lia).
          eapply implM_at_eq; [eapply sw_loopA with (k := 0) | ].
        all: try exact FR.
        all: lazymatch goal with |- MS _ _ _ _ _ _ _ = _ => ms_eq | _ => idtac end.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH']) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SP47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RSTK]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [assumption]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WM]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [subst nb; unfold zlength in *; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [subst nb; unfold zlength in *; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [subst nb; unfold zlength in *; lia]) ].
  Qed.
  End Sz13.
  Theorem stdio_write_spec : ltac:(let t := eval cbv delta [stdio_write_spec__stmt] in stdio_write_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn writefn seekfn B bufsize prev next mode lbf tail s S lo canary. ltac2:(SecDiet.SzSec.closeP 'stdio_write_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Entry.
End TwB.
End F_stdio_write.

(* [comment removed for export] *)
Module F_towrite.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition towrite_entry : Z := 0x9ac80.

Definition towrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (closefn readfn writefn seekfn buf bufsize prev next fd : Z) (lbf : Z) (tail : list byte)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' Fp (file_cells flags 0 0 closefn (buf + bufsize) buf buf readfn writefn seekfn buf bufsize prev next fd mode' lbf tail).

Definition towrite_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (flags mode : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf : Z) (tail : list byte),
  rw_cells asegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  Z.land (bv_unsigned flags) 8 = 0 ->
  (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) 232 ->
  evtF asegs RNG (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) flags closefn readfn writefn seekfn buf bufsize prev next fd lbf tail m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ac80) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail : ltac2:(SecDiet.SzSec.tyM 'towrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma towrite_spec__body : ltac2:(SecDiet.SzSec.bodyP 'towrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros FC NOWR B0 BHI BS0 MI RFP.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold file_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evtF_done. unfold towrite_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.
End Sz1.
Lemma towrite_spec : ltac:(let t := eval cbv delta [towrite_spec__stmt] in towrite_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail. ltac2:(SecDiet.SzSec.closeP 'towrite_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition towrite_entry : Z := 0x9b064.

Definition towrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (closefn readfn writefn seekfn buf bufsize prev next fd : Z) (lbf : Z) (tail : list byte)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Fp, Fp + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' Fp (file_cells flags 0 0 closefn (buf + bufsize) buf buf readfn writefn seekfn buf bufsize prev next fd mode' lbf tail).

Definition towrite_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (flags mode : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf : Z) (tail : list byte),
  rw_cells asegs m (bv_unsigned a0) (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  Z.land (bv_unsigned flags) 8 = 0 ->
  (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
  mem_inv asegs m ->
  rng RNG (bv_unsigned a0) 232 ->
  evtF asegs RNG (towrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) flags closefn readfn writefn seekfn buf bufsize prev next fd lbf tail m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b064) fc None m (seg_rom asegs)).
Section Sz1.
Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail : ltac2:(SecDiet.SzSec.tyM 'towrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
#[using="Type"] Lemma towrite_spec__body : ltac2:(SecDiet.SzSec.bodyP 'towrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros FC NOWR B0 BHI BS0 MI RFP.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. rewrite file_cells_size in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold file_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evtF_done. unfold towrite_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.
End Sz1.
Lemma towrite_spec : ltac:(let t := eval cbv delta [towrite_spec__stmt] in towrite_spec__stmt in exact t).
Proof. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m flags mode rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd lbf tail. ltac2:(SecDiet.SzSec.closeP 'towrite_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_towrite.
