(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0o YK11 YK0i YK0j YK14 YK0v.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope bool_scope.
Section c.
Context {fx : FPState}.
Lemma find_segment_in : forall segs (a n : Z) seg,
find_segment segs a n = Some seg -> In seg segs.
Proof.
induction segs as [|s rest IH]; intros a n seg H; [discriminate|].
cbn in H. destruct (_ && _)%bool.
- injection H as <-. left; reflexivity.
- right; eauto.
Qed.
Lemma find_segment_range : forall segs (a n : Z) seg,
find_segment segs a n = Some seg ->
(Z.of_N (seg_base seg) <= a)%Z /\
(a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
induction segs as [|s rest IH]; intros a n seg H; [discriminate|].
cbn in H.
destruct (Z.leb (Z.of_N (seg_base s)) a) eqn:Hlo;
destruct (Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:Hhi;
cbn in H; eauto.
injection H as <-. split; [apply Z.leb_le, Hlo | apply Z.leb_le, Hhi].
Qed.
Definition no_ro_exec (segs : list Segment) : bool :=
forallb (fun s => negb (seg_executable s && negb (seg_writable s))) segs.


Definition mem_clear (m : word -> option byte) (lo hi : Z) : Prop :=
forall a : word, (lo <= bv_unsigned a < hi)%Z -> m a = None.


Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
induction n as [|n IH]; intro z; [reflexivity|].
cbn [Z_to_le_bytes length]. now rewrite IH.
Qed.
Lemma length_word_to_le_bytes : forall n (v : word),
length (word_to_le_bytes n v) = n.
Proof. intros. apply length_Z_to_le_bytes. Qed.


Definition wx_fetch (segs : list Segment) (m : word -> option byte)
(pc : word) (w : bv 32) : Prop :=
fetch_word segs pc = None /\ fetch_word_ov segs m pc = Some w.

End c.
Ltac wx_step_pipeline Hwx Hecall Hdecode :=
let Hn := fresh "Hn" in
let Hov := fresh "Hov" in
destruct Hwx as [Hn Hov];
unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
cbn [ms_pc ms_pc_val ms_mem mkst];
rewrite Hn;
cbv beta iota;
rewrite Hov;
cbv beta iota;
unfold RiscvSemantics.drop_access_report,
RiscvSemantics.decode_exec_accesses;
rewrite Hecall;
cbv beta iota;
rewrite Hdecode;
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses
RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
Sem.inval_resv Sem.w0 Sem.w1
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
rewrite ?bv_eqb0_is_x0.
Section d.
Context {fx : FPState}.



















End d.
