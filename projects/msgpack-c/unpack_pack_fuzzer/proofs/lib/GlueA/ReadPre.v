(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require InitLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggLib UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadC.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step ValP MemP CtrLib ReadC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module SH := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Module AE := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.

Definition STAGE : Z := 0x5fc110.
Definition RLO2 : Z := 0x5fc100.
Definition RHI2 : Z := 0x60c140.
Definition ZSH_LO : Z := 0x800b7820.
Definition ZSH_HI : Z := 0x800b9828.
Definition ERRNO : Z := 0x60cbdc.

Definition ZSC_LO : Z := 0x800b7822.
Definition ZSC_HI : Z := 0x800b9822.

Definition zsh_holds (m : word -> option byte) : Prop :=
  (forall a, ZSH_LO <= a < ZSH_HI -> wb asegs m a = true) /\ (forall a, ZSC_LO <= a < ZSC_HI -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).

Section PRE.

Lemma image_chunk : forall (m : word -> option byte) A (n : nat), 0 <= A -> Mem.abs_writable asegs A (Z.of_nat n) = true ->
  exists j, AS.rw_cells asegs m A [CB n j].
Proof.
  intros m A n HA W. destruct (MemP.abs_writable_sound asegs A (Z.of_nat n) HA ltac:(lia) W) as [RD WB].
  destruct (MemP.abs_readable_sound asegs A (Z.of_nat n) ltac:(lia) RD) as [B62 RS].
  apply (mapped_chunk asegs); [exact HA | lia |].
  intros i Hi. split; [exact (proj1 (WB i Hi) m)|].
  destruct (RS i Hi) as (b & rest & MR). exact (MemP.rb_rom asegs m (A + i) b rest MR).
Qed.

Lemma c4_of_CB : forall m A bs, AS.rw_cells asegs m A [CB 4 bs] -> exists w : word, AS.rw_cells asegs m A [C4 w].
Proof.
  intros m A bs H. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  exists (le_bytes_to_word bs).
  eapply (ALib.InitMem.rw_cells_recast asegs); [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_of_bytes by exact L. reflexivity.
Qed.

Lemma stage_chunk : forall (m : word -> option byte) (n : nat), Z.of_nat n <= 65536 -> exists j, AS.rw_cells asegs m STAGE [CB n j].
Proof.
  intros m n Hn.
  destruct (MemP.abs_writable_sound asegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [RD WB].
  destruct (MemP.abs_readable_sound asegs STAGE 65536 ltac:(lia) RD) as [_ RS].
  apply (mapped_chunk asegs); [unfold STAGE; lia | unfold STAGE; lia |].
  intros i Hi. split; [exact (proj1 (WB i ltac:(lia)) m)|].
  destruct (RS i ltac:(lia)) as (b & rest & MR). exact (MemP.rb_rom asegs m (STAGE + i) b rest MR).
Qed.

Lemma zsh_unpoisoned : forall m n, zsh_holds m -> 0 < n <= 65536 -> SH.unpoisoned m STAGE (STAGE + n).
Proof.
  intros m n Z Hn. unfold SH.unpoisoned. split; [unfold STAGE; lia|]. split; [unfold STAGE; lia|].
  intros G _ G1 G2. exists (Z_to_bv 8 0). split.
  - unfold ALib.Mem.wa. apply (proj2 Z (AE.ASHOFF + G) ltac:(unfold ZSC_LO, ZSC_HI, AE.ASHOFF, STAGE in *; lia)).
  - left. reflexivity.
Qed.
Lemma zsh_wr : forall m, zsh_holds m -> ALib.Mem.wr_at asegs m (AE.shad RLO2) (AE.shad RHI2 - AE.shad RLO2).
Proof.
  intros m Z. assert (E1 : AE.shad RLO2 = ZSH_LO) by (vm_compute; reflexivity). assert (E2 : AE.shad RHI2 = ZSH_HI) by (vm_compute; reflexivity).
  rewrite E1, E2. split; [unfold ZSH_LO; lia|]. split; [unfold ZSH_LO, ZSH_HI; lia|].
  intros i Hi. apply (GlueA.wb_wviewA asegs). apply (proj1 Z (ZSH_LO + i) ltac:(unfold ZSH_LO, ZSH_HI in *; lia)).
Qed.

Lemma errno_chunk : forall (m : word -> option byte), exists w : word, AS.rw_cells asegs m ERRNO [C4 w].
Proof.
  intros m. destruct (image_chunk m ERRNO 4 ltac:(unfold ERRNO; lia) ltac:(vm_compute; reflexivity)) as [j H].
  exact (c4_of_CB m ERRNO j H).
Qed.

Lemma want_ok_inv : forall v w, CtrS.want_ok v = Some w -> v = VL w /\ 0 < w2Z w <= 65536.
Proof.
  intros v w HW. unfold CtrS.want_ok in HW. destruct v; try discriminate HW.
  destruct (wltu wzero w0 && wleu w0 (wlit CtrS.STAGE_LEN)) eqn:Hc; [|discriminate HW]. injection HW as <-.
  apply andb_prop in Hc as [H1 H2]. rewrite wltu_w2Z in H1. rewrite ValP.wleu_w2Z in H2.
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. rewrite wlit_ok in H2. change (w2Z wzero) with 0 in H1.
  change (to_Z CtrS.STAGE_LEN) with 65536 in H2. split; [reflexivity | lia].
Qed.

Lemma aread_pre_inv : forall st off, aread_pre CFG_ASAN st = Some off ->
  CtrS.is_lit (Step.getr st X10) (wlit 3%uint63) = true /\ CtrS.is_lit (Step.getr st X11) (wlit 6275344%uint63) = true
  /\ CtrS.priv_has st 6275344%uint63 CtrS.STAGE_LEN = true
  /\ (exists a b, find_op ReadC.RSTV_ID (s_ops st) = Some [a; b]) /\ Nat.eqb (CtrS.count_ops ReadC.RSTV_ID (s_ops st)) 1%nat = true
  /\ CtrS.one_fd_op st = true /\ find_op 11%uint63 (s_ops st) = Some [] /\ find_op CtrS.FD3_ID (s_ops st) = Some [off].
Proof.
  intros st off H. unfold aread_pre in H. cbn [r_stage r_zsh CFG_ASAN] in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:B; [|discriminate H] end.
  repeat match type of B with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in B as [B X] end.
  split; [exact B|]. split; [exact Q3|]. split; [exact Q2|].
  destruct (find_op ReadC.RSTV_ID (s_ops st)) as [[|a [|b [|? ?]]]|] eqn:FR; try discriminate Q1.
  split; [exists a, b; reflexivity|]. split; [exact Q1|]. split; [exact Q0|].
  destruct (find_op 11%uint63 (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate Q.
  split; [reflexivity|].
  destruct (find_op CtrS.FD3_ID (s_ops st)) as [[|o [|? ?]]|] eqn:FD; try discriminate H. injection H as <-. reflexivity.
Qed.

Variable OPS : optable.

Hypothesis OPS_holds_zsh : forall m mo, op_holds OPS (r_zsh CFG_ASAN) [] m mo -> zsh_holds m.

Lemma aread_pre_facts : forall E st ms mo off,
  st_ok asegs OPS E st ms mo -> aread_pre CFG_ASAN st = Some off ->
  AP.getr (ms_regs ms) (reg_of_r5 X10) = Z_to_bv 64 3 /\ AP.getr (ms_regs ms) (reg_of_r5 X11) = Z_to_bv 64 STAGE /\ zsh_holds (ms_mem ms).
Proof.
  intros E st ms mo off HS H. destruct (aread_pre_inv st off H) as (A0 & A1 & _ & _ & _ & _ & FZ & _).
  unfold CtrS.is_lit in A0, A1. apply sv_eqb_eq in A0. apply sv_eqb_eq in A1.
  split; [rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), A0; reflexivity|].
  split; [rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), A1; reflexivity|].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  exact (OPS_holds_zsh _ _ HO).
Qed.
End PRE.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import ABase.TwinB ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs.
Import UnreggLib.TwinB UnreggPre.TwinB.
Import ReadC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step ValP MemP CtrLib ReadC.TwinB.ReadC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module SH := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Module AE := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.

Definition STAGE : Z := 0x5fe2d0.
Definition RLO2 : Z := 0x5fe2c0.
Definition RHI2 : Z := 0x60e300.
Definition ZSH_LO : Z := 0x800b7c58.
Definition ZSH_HI : Z := 0x800b9c60.
Definition ERRNO : Z := 0x60ed9c.

Definition ZSC_LO : Z := 0x800b7c5a.
Definition ZSC_HI : Z := 0x800b9c5a.

Definition zsh_holds (m : word -> option byte) : Prop :=
  (forall a, ZSH_LO <= a < ZSH_HI -> wb bsegs m a = true) /\ (forall a, ZSC_LO <= a < ZSC_HI -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).

Section PRE.

Lemma image_chunk : forall (m : word -> option byte) A (n : nat), 0 <= A -> Mem.abs_writable bsegs A (Z.of_nat n) = true ->
  exists j, AS.rw_cells bsegs m A [CB n j].
Proof.
  intros m A n HA W. destruct (MemP.abs_writable_sound bsegs A (Z.of_nat n) HA ltac:(lia) W) as [RD WB].
  destruct (MemP.abs_readable_sound bsegs A (Z.of_nat n) ltac:(lia) RD) as [B62 RS].
  apply (mapped_chunk bsegs); [exact HA | lia |].
  intros i Hi. split; [exact (proj1 (WB i Hi) m)|].
  destruct (RS i Hi) as (b & rest & MR). exact (MemP.rb_rom bsegs m (A + i) b rest MR).
Qed.

Lemma c4_of_CB : forall m A bs, AS.rw_cells bsegs m A [CB 4 bs] -> exists w : word, AS.rw_cells bsegs m A [C4 w].
Proof.
  intros m A bs H. pose proof H as H0. destruct H0 as [[[L _] _] _]. cbn in L.
  exists (le_bytes_to_word bs).
  eapply (ALib.InitMem.rw_cells_recast bsegs); [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. rewrite le4_of_bytes by exact L. reflexivity.
Qed.

Lemma stage_chunk : forall (m : word -> option byte) (n : nat), Z.of_nat n <= 65536 -> exists j, AS.rw_cells bsegs m STAGE [CB n j].
Proof.
  intros m n Hn.
  destruct (MemP.abs_writable_sound bsegs STAGE 65536 ltac:(unfold STAGE; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as [RD WB].
  destruct (MemP.abs_readable_sound bsegs STAGE 65536 ltac:(lia) RD) as [_ RS].
  apply (mapped_chunk bsegs); [unfold STAGE; lia | unfold STAGE; lia |].
  intros i Hi. split; [exact (proj1 (WB i ltac:(lia)) m)|].
  destruct (RS i ltac:(lia)) as (b & rest & MR). exact (MemP.rb_rom bsegs m (STAGE + i) b rest MR).
Qed.

Lemma zsh_unpoisoned : forall m n, zsh_holds m -> 0 < n <= 65536 -> SH.unpoisoned m STAGE (STAGE + n).
Proof.
  intros m n Z Hn. unfold SH.unpoisoned. split; [unfold STAGE; lia|]. split; [unfold STAGE; lia|].
  intros G _ G1 G2. exists (Z_to_bv 8 0). split.
  - unfold ALib.Mem.wa. apply (proj2 Z (AE.ASHOFF + G) ltac:(unfold ZSC_LO, ZSC_HI, AE.ASHOFF, STAGE in *; lia)).
  - left. reflexivity.
Qed.
Lemma zsh_wr : forall m, zsh_holds m -> ALib.Mem.wr_at bsegs m (AE.shad RLO2) (AE.shad RHI2 - AE.shad RLO2).
Proof.
  intros m Z. assert (E1 : AE.shad RLO2 = ZSH_LO) by (vm_compute; reflexivity). assert (E2 : AE.shad RHI2 = ZSH_HI) by (vm_compute; reflexivity).
  rewrite E1, E2. split; [unfold ZSH_LO; lia|]. split; [unfold ZSH_LO, ZSH_HI; lia|].
  intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs). apply (proj1 Z (ZSH_LO + i) ltac:(unfold ZSH_LO, ZSH_HI in *; lia)).
Qed.

Lemma errno_chunk : forall (m : word -> option byte), exists w : word, AS.rw_cells bsegs m ERRNO [C4 w].
Proof.
  intros m. destruct (image_chunk m ERRNO 4 ltac:(unfold ERRNO; lia) ltac:(vm_compute; reflexivity)) as [j H].
  exact (c4_of_CB m ERRNO j H).
Qed.

Lemma want_ok_inv : forall v w, CtrS.want_ok v = Some w -> v = VL w /\ 0 < w2Z w <= 65536.
Proof.
  intros v w HW. unfold CtrS.want_ok in HW. destruct v; try discriminate HW.
  destruct (wltu wzero w0 && wleu w0 (wlit CtrS.STAGE_LEN)) eqn:Hc; [|discriminate HW]. injection HW as <-.
  apply andb_prop in Hc as [H1 H2]. rewrite wltu_w2Z in H1. rewrite ValP.wleu_w2Z in H2.
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. rewrite wlit_ok in H2. change (w2Z wzero) with 0 in H1.
  change (to_Z CtrS.STAGE_LEN) with 65536 in H2. split; [reflexivity | lia].
Qed.

Lemma aread_pre_inv : forall st off, aread_pre CFG_ASAN st = Some off ->
  CtrS.is_lit (Step.getr st X10) (wlit 3%uint63) = true /\ CtrS.is_lit (Step.getr st X11) (wlit 6283984%uint63) = true
  /\ CtrS.priv_has st 6283984%uint63 CtrS.STAGE_LEN = true
  /\ (exists a b, find_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st) = Some [a; b]) /\ Nat.eqb (CtrS.count_ops ReadC.TwinB.ReadC.RSTV_ID (s_ops st)) 1%nat = true
  /\ CtrS.one_fd_op st = true /\ find_op 11%uint63 (s_ops st) = Some [] /\ find_op CtrS.FD3_ID (s_ops st) = Some [off].
Proof.
  intros st off H. unfold aread_pre in H. cbn [r_stage r_zsh CFG_ASAN] in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:B; [|discriminate H] end.
  repeat match type of B with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in B as [B X] end.
  split; [exact B|]. split; [exact Q3|]. split; [exact Q2|].
  destruct (find_op ReadC.TwinB.ReadC.RSTV_ID (s_ops st)) as [[|a [|b [|? ?]]]|] eqn:FR; try discriminate Q1.
  split; [exists a, b; reflexivity|]. split; [exact Q1|]. split; [exact Q0|].
  destruct (find_op 11%uint63 (s_ops st)) as [[|? ?]|] eqn:FZ; try discriminate Q.
  split; [reflexivity|].
  destruct (find_op CtrS.FD3_ID (s_ops st)) as [[|o [|? ?]]|] eqn:FD; try discriminate H. injection H as <-. reflexivity.
Qed.

Variable OPS : optable.

Hypothesis OPS_holds_zsh : forall m mo, op_holds OPS (r_zsh CFG_ASAN) [] m mo -> zsh_holds m.

Lemma aread_pre_facts : forall E st ms mo off,
  st_ok bsegs OPS E st ms mo -> aread_pre CFG_ASAN st = Some off ->
  AP.getr (ms_regs ms) (reg_of_r5 X10) = Z_to_bv 64 3 /\ AP.getr (ms_regs ms) (reg_of_r5 X11) = Z_to_bv 64 STAGE /\ zsh_holds (ms_mem ms).
Proof.
  intros E st ms mo off HS H. destruct (aread_pre_inv st off H) as (A0 & A1 & _ & _ & _ & _ & FZ & _).
  unfold CtrS.is_lit in A0, A1. apply sv_eqb_eq in A0. apply sv_eqb_eq in A1.
  split; [rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), A0; reflexivity|].
  split; [rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), A1; reflexivity|].
  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  exact (OPS_holds_zsh _ _ HO).
Qed.
End PRE.
End TwinB.
