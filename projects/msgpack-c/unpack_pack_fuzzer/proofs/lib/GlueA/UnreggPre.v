(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require InitLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggLib UnreggC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggAsan.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step ValP MemP CtrLib UnreggC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Module UA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.UnreggAsan.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition SH_LO : Z := 0x7fffc58c.  Definition SH_HI : Z := 0x7fffc670.
Definition ASH_LO : Z := 0x80012bd2. Definition ASH_HI : Z := 0x80012c80.

Definition shmap_holds (m : word -> option byte) : Prop :=
  forall a, (SH_LO <= a < SH_HI \/ ASH_LO <= a < ASH_HI) -> wb asegs m a = true.

Lemma no_seg_above : forall a, 0x62f000 <= a -> find_segment asegs a 1 = None.
Proof.
  intros a Ha. apply (InitLib.InitLib.find_segment_none asegs a 1 0x62f000); [vm_compute; reflexivity | exact Ha | lia].
Qed.

Lemma shmap_rb : forall m a, 0x62f000 <= a < 2 ^ 64 -> wb asegs m a = true -> rb asegs m a <> None.
Proof.
  intros m a Ha W. unfold wb, wview in W. unfold rb.
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  rewrite Z_to_bv_unsigned, bv_wrap_small in W by (unfold bv_modulus; lia). rewrite (no_seg_above a (proj1 Ha)) in W. discriminate W.
Qed.

Lemma shmap_chunk : forall m A n, shmap_holds m ->
  ((SH_LO <= A /\ A + Z.of_nat n <= SH_HI) \/ (ASH_LO <= A /\ A + Z.of_nat n <= ASH_HI)) ->
  exists j, AS.rw_cells asegs m A [CB n j].
Proof.
  intros m A n H R. unfold SH_LO, SH_HI, ASH_LO, ASH_HI in R. apply mapped_chunk; [lia | lia |].
  intros i Hi. assert (W : wb asegs m (A + i) = true) by (apply H; unfold SH_LO, SH_HI, ASH_LO, ASH_HI; lia).
  split; [exact W|]. apply shmap_rb; [lia | exact W].
Qed.

Section PRE.
Variable OPS : optable.

Hypothesis OPS_holds_shmap : forall m mo, op_holds OPS (u_shmap CFG_ASAN) [] m mo -> shmap_holds m.

Lemma find_op_In : forall id os args, find_op id os = Some args -> In (OpI id args) os.
Proof.
  induction os as [|o os IH]; intros args H; cbn [find_op] in H; [discriminate|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. apply Uint63.eqb_correct in Q. left. destruct o; cbn in *. subst. reflexivity.
  - right. exact (IH args H).
Qed.

Ltac img_goal IMG BASE :=
  apply (img_chunk_sound asegs); [vm_compute; reflexivity | lia |
    let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; simpl in Hi;
    match goal with |- rb _ _ (?A + i) = _ => replace (A + i) with (BASE + (A - BASE + i)) by lia end; apply IMG; lia].

Lemma unregg_pre_facts : forall E st ms mo,
  st_ok asegs OPS E st ms mo -> unregg_pre_b CFG_ASAN st = true -> artcells (ms_mem ms) ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> ms_mem ms (ALib.Mem.wa i) = None) ->
  UA.unregg_pre (ms_mem ms)
  /\ AP.getr (ms_regs ms) (reg_of_r5 X10) = Z_to_bv 64 0xd5e90 /\ AP.getr (ms_regs ms) (reg_of_r5 X11) = Z_to_bv 64 21.
Proof.
  intros E st ms mo HS H RT RELRO. unfold unregg_pre_b in H. cbn [u_gva u_n u_mtx u_rgl u_rglv u_got80 u_shmap CFG_ASAN] in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate H].
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.

  apply sv_eqb_eq in H. apply sv_eqb_eq in Q5.
  assert (BG : rg_bg r0 = BGImage) by (destruct (rg_bg r0); try discriminate Q4; reflexivity).
  apply negb_true_iff in Q2.
  set (m := ms_mem ms) in *.
  assert (IMG : forall i, 0 <= i < 1344 -> rb asegs m (0xd5e90 + i) = img_byte asegs (0xd5e90 + i)).
  { apply (image_bytes_p asegs OPS E st ms mo r0 0xd5e90 1344 HS Hr0 BG); [lia | lia | exact Q2 | exact Q3 | vm_compute; reflexivity]. }
  assert (IMG80 : forall i, 0 <= i < 8 -> rb asegs m (0xd1538 + i) = img_byte asegs (0xd1538 + i)).
  { intros i Hi. pose proof (RELRO (0xd1538 + i) ltac:(unfold ARELRO_LO, ARELRO_HI; lia)) as X. unfold ALib.Mem.wa in X.
    unfold rb, img_byte. fold m in X. rewrite X. reflexivity. }
  pose proof (lit_cell0_bytes asegs OPS E st ms mo r0 0xd7370 wzero HS Hr0 ltac:(lia) ltac:(reflexivity) Q1) as CM.
  pose proof (lit_cell0_bytes asegs OPS E st ms mo r0 0xd72d0 _ HS Hr0 ltac:(lia) ltac:(reflexivity) Q0) as CR.
  assert (SHM : shmap_holds m).
  { destruct (find_op 10%uint63 (s_ops st)) as [[|? ?]|] eqn:FO; try discriminate Q.
    pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ FO)) as HO. cbn [op_id op_args map] in HO.
    exact (OPS_holds_shmap _ _ HO). }
  split; [| split].
  - unfold artcells in RT. decompose [and] RT. clear RT.
    unfold UA.unregg_pre, UA.mdtor_rt, UA.gdesc.
    repeat match goal with |- _ /\ _ => split end;
      first [ assumption
            | img_goal IMG 0xd5e90
            | img_goal IMG80 0xd1538
            | apply (lit_chunk_sound asegs m 0xd7370 wzero); [vm_compute; reflexivity | lia | lia | vm_compute; reflexivity | exact CM]
            | apply (lit_chunk_sound asegs m 0xd72d0 (wlit 0x0101010000000001%uint63)); [vm_compute; reflexivity | lia | lia | vm_compute; reflexivity | exact CR]
            | apply (shmap_chunk m _ _ SHM); unfold SH_LO, SH_HI, ASH_LO, ASH_HI; lia ].
  - rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), H. reflexivity.
  - rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X11), Q5. reflexivity.
Qed.
End PRE.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import UnreggLib.TwinB UnreggC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step ValP MemP CtrLib UnreggC.TwinB.UnreggC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Module UA := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA.UnreggAsan.TwinB.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition SH_LO : Z := 0x7fffc5a0.  Definition SH_HI : Z := 0x7fffc6a0.
Definition ASH_LO : Z := 0x80012ff6. Definition ASH_HI : Z := 0x800130b8.

Definition shmap_holds (m : word -> option byte) : Prop :=
  forall a, (SH_LO <= a < SH_HI \/ ASH_LO <= a < ASH_HI) -> wb bsegs m a = true.

Lemma no_seg_above : forall a, 0x631000 <= a -> find_segment bsegs a 1 = None.
Proof.
  intros a Ha. apply (InitLib.InitLib.find_segment_none bsegs a 1 0x631000); [vm_compute; reflexivity | exact Ha | lia].
Qed.

Lemma shmap_rb : forall m a, 0x631000 <= a < 2 ^ 64 -> wb bsegs m a = true -> rb bsegs m a <> None.
Proof.
  intros m a Ha W. unfold wb, wview in W. unfold rb.
  destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  rewrite Z_to_bv_unsigned, bv_wrap_small in W by (unfold bv_modulus; lia). rewrite (no_seg_above a (proj1 Ha)) in W. discriminate W.
Qed.

Lemma shmap_chunk : forall m A n, shmap_holds m ->
  ((SH_LO <= A /\ A + Z.of_nat n <= SH_HI) \/ (ASH_LO <= A /\ A + Z.of_nat n <= ASH_HI)) ->
  exists j, AS.rw_cells bsegs m A [CB n j].
Proof.
  intros m A n H R. unfold SH_LO, SH_HI, ASH_LO, ASH_HI in R. apply mapped_chunk; [lia | lia |].
  intros i Hi. assert (W : wb bsegs m (A + i) = true) by (apply H; unfold SH_LO, SH_HI, ASH_LO, ASH_HI; lia).
  split; [exact W|]. apply shmap_rb; [lia | exact W].
Qed.

Section PRE.
Variable OPS : optable.

Hypothesis OPS_holds_shmap : forall m mo, op_holds OPS (u_shmap CFG_ASAN) [] m mo -> shmap_holds m.

Lemma find_op_In : forall id os args, find_op id os = Some args -> In (OpI id args) os.
Proof.
  induction os as [|o os IH]; intros args H; cbn [find_op] in H; [discriminate|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. apply Uint63.eqb_correct in Q. left. destruct o; cbn in *. subst. reflexivity.
  - right. exact (IH args H).
Qed.

Ltac img_goal IMG BASE :=
  apply (img_chunk_sound bsegs); [vm_compute; reflexivity | lia |
    let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; simpl in Hi;
    match goal with |- rb _ _ (?A + i) = _ => replace (A + i) with (BASE + (A - BASE + i)) by lia end; apply IMG; lia].

Lemma unregg_pre_facts : forall E st ms mo,
  st_ok bsegs OPS E st ms mo -> unregg_pre_b CFG_ASAN st = true -> artcells (ms_mem ms) ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> ms_mem ms (ALib.Mem.wa i) = None) ->
  UA.unregg_pre (ms_mem ms)
  /\ AP.getr (ms_regs ms) (reg_of_r5 X10) = Z_to_bv 64 0xd7fb0 /\ AP.getr (ms_regs ms) (reg_of_r5 X11) = Z_to_bv 64 24.
Proof.
  intros E st ms mo HS H RT RELRO. unfold unregg_pre_b in H. cbn [u_gva u_n u_mtx u_rgl u_rglv u_got80 u_shmap CFG_ASAN] in H.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate H].
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.

  apply sv_eqb_eq in H. apply sv_eqb_eq in Q5.
  assert (BG : rg_bg r0 = BGImage) by (destruct (rg_bg r0); try discriminate Q4; reflexivity).
  apply negb_true_iff in Q2.
  set (m := ms_mem ms) in *.
  assert (IMG : forall i, 0 <= i < 1536 -> rb bsegs m (0xd7fb0 + i) = img_byte bsegs (0xd7fb0 + i)).
  { apply (image_bytes_p bsegs OPS E st ms mo r0 0xd7fb0 1536 HS Hr0 BG); [lia | lia | exact Q2 | exact Q3 | vm_compute; reflexivity]. }
  assert (IMG80 : forall i, 0 <= i < 8 -> rb bsegs m (0xd3650 + i) = img_byte bsegs (0xd3650 + i)).
  { intros i Hi. pose proof (RELRO (0xd3650 + i) ltac:(unfold ARELRO_LO, ARELRO_HI; lia)) as X. unfold ALib.Mem.wa in X.
    unfold rb, img_byte. fold m in X. rewrite X. reflexivity. }
  pose proof (lit_cell0_bytes bsegs OPS E st ms mo r0 0xd9530 wzero HS Hr0 ltac:(lia) ltac:(reflexivity) Q1) as CM.
  pose proof (lit_cell0_bytes bsegs OPS E st ms mo r0 0xd9490 _ HS Hr0 ltac:(lia) ltac:(reflexivity) Q0) as CR.
  assert (SHM : shmap_holds m).
  { destruct (find_op 10%uint63 (s_ops st)) as [[|? ?]|] eqn:FO; try discriminate Q.
    pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (find_op_In _ _ _ FO)) as HO. cbn [op_id op_args map] in HO.
    exact (OPS_holds_shmap _ _ HO). }
  split; [| split].
  - unfold artcells in RT. decompose [and] RT. clear RT.
    unfold UA.unregg_pre, UA.mdtor_rt, UA.gdesc.
    repeat match goal with |- _ /\ _ => split end;
      first [ assumption
            | img_goal IMG 0xd7fb0
            | img_goal IMG80 0xd3650
            | apply (lit_chunk_sound bsegs m 0xd9530 wzero); [vm_compute; reflexivity | lia | lia | vm_compute; reflexivity | exact CM]
            | apply (lit_chunk_sound bsegs m 0xd9490 (wlit 0x0101010000000001%uint63)); [vm_compute; reflexivity | lia | lia | vm_compute; reflexivity | exact CR]
            | apply (shmap_chunk m _ _ SHM); unfold SH_LO, SH_HI, ASH_LO, ASH_HI; lia ].
  - rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), H. reflexivity.
  - rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X11), Q5. reflexivity.
Qed.
End PRE.
End TwinB.
