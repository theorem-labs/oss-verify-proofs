(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/TopHypsSrc.v: the contract table of the usage path discharged over BudgetWit.Rzb.rzb, and the usage path's rzb derivation for every input with argc <> 2 *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's caps, mmap base and far-end reader; the string-length contract's end alignment; PB12 bounds the string area, now SI.strarea of the ProcInput, by the launch's E2BIG cap; aw_init's start model with the launch's vDSO run state, by AWInit.aw_init stated for any vDSO run state; RunSrcB's run records, contract tables and family records taken at the launch's mmap base too, which the start environment reads). *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ItabSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require ClientX Ops.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Ceiling.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require AW AWInit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcNU Require T_SrcNU.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StackInit Nodes CertSound OblsLib Ops SysSpec CtrSys DrvShape DrvRoot DrvLib DrvTop RunCeil RunSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb PlanSoundB CertSoundB NodesB StdioWriteB DrvLibB HeapCtrW MemcpyCtrW StrCtrW RunSrcB.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Glue.Ops.Ops CtrS DrvShape DrvRoot DrvLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module RX := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.RunSrc.RunSrc.
Module RXB := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit.RunSrcB.RunSrcB.
Import PlanSB.

Module TopB.
Section RUN.

Variable inp : ProcInput.
Variables (sp brk0 mb : word) (rnd : EntryDraw) (lim : Z).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hhw : valid_hwcap (in_hwcap inp).
Hypothesis Hsz : in_va_size inp = Sv48.
(* the launch's caps, for the start state's window below sp (ALib/InitMem.v's stack_window_lo_valid) *)
Hypothesis Hvl : valid_launch inp.
(* the launch's far-end reader ([Run.valid_input]) *)
Hypothesis Hrdr : in_channel_reader inp = true.
Hypothesis Hen : valid_entry (mkImage SEGS PC PH) (mkEntry sp brk0 mb rnd) inp.
Hypothesis Hlim : 2 ^ 31 <= lim.

Definition CLG : Ceiling.ceiling := RunCeil.CLG sp rnd.
Lemma Hvsp : valid_sp sp.
Proof. pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as (H & _ & _ & _). exact H. Qed.
Lemma ceil_le : @Ceiling.alloc_ceiling CLG <= bv_unsigned sp - DrvTop.WOFF.
Proof. exact (RunCeil.ceil_le sp rnd Hvsp). Qed.
Definition XW : HeapOp.client_world := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.ClientX.CX.XTP SEGS.
Definition Cw : HeapOp.client_world := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops.UO.unp_cw SEGS XW.

Lemma cw_init : forall lo m, HeapOp.cw_holds Cw 0 [] [] [HeapOp.Win lo DrvTop.WLEN 0] m.
Proof.
  intros lo m. cbn [Cw HeapOp.cw_holds OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops.UO.unp_cw].
  unfold OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops.UO.cw_unp_holds. cbn. first [exact I | (constructor; [intros [A _]; exact (A eq_refl)| constructor])].
Qed.

Definition A : HeapOp.alloc_world SEGS RX.XCL := @AW.AWI CLG.
Lemma aw_fds : forall aw LB ws m mo fds, HeapOp.aw_holds SEGS RX.XCL A aw LB ws m mo -> HeapOp.aw_holds SEGS RX.XCL A aw LB ws m (with_fds fds mo).
Proof. intros aw LB ws m mo fds [H N]. split; [exact (@AW.aw_fds CLG aw LB m mo fds H)| exact N]. Qed.
Lemma aw_init : forall mem tid lo,
  (forall a, RX.AST_LO <= a < RX.AST_HI -> rb SEGS mem a = img_byte SEGS a) ->
  HeapOp.aw_holds SEGS RX.XCL A (Z_to_bv 64 0) [] [HeapOp.Win lo DrvTop.WLEN 0] mem (with_tid tid (RXB.model0 inp sp brk0 mb rnd lim)).
Proof.
  intros mem tid lo HI. pose proof (proj1 (valid_entry_sv48 _ _ _ Hsz) Hen) as (_ & Hbrk & Hmb & _).
  (* LPS 727298f3: the start model is init_model under with_vdso (the launch's vDSO draw); AWInit.aw_init is
     stated for any vDSO run state, and the run's own is read off the goal *)
  exact (@AWInit.aw_init CLG mem brk0 mb sp lim inp tid _ Hbrk (AWInit.ceil_clamp_ok sp Hvsp) Hmb Hlim HI
           [HeapOp.Win lo DrvTop.WLEN 0] ltac:(intros w [<-|[]]; cbn; unfold HeapOp.K_GHOST; lia)).
Qed.

Lemma aw_ceil_fds : forall mo fds, HeapOp.aw_ceiling SEGS RX.XCL A (with_fds fds mo) = HeapOp.aw_ceiling SEGS RX.XCL A mo.
Proof. intros mo fds. reflexivity. Qed.
Lemma aw_ceil0 : forall tid, HeapOp.aw_ceiling SEGS RX.XCL A (with_tid tid (RXB.model0 inp sp brk0 mb rnd lim)) <= bv_unsigned sp - DrvTop.WOFF.
Proof. intros tid. exact ceil_le. Qed.

Definition R : drun := RXB.R inp sp mb rnd Hva A Cw aw_fds aw_ceil_fds.
Let MP := RXB.MP inp.
Let PB := RXB.PB inp sp mb rnd.

Lemma OPS_holds1 : forall args m mo, op_holds (OPS R) CtrLib.HEAP_ID args m mo = HeapOp.heap_holds SEGS RX.XCL A Cw args m mo.
Proof. intros. reflexivity. Qed.
Lemma OPS_fp1 : forall args, op_fp (OPS R) CtrLib.HEAP_ID args = HeapOp.heap_fp RX.XCL args.
Proof. intros. reflexivity. Qed.

Lemma PBstr1 : forall E, PB (eb E) -> exists str, eb E 1%uint63 = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str /\
  bv_unsigned (den E (CtrA.SZ 9%uint63)) = Z.of_nat (length str) + 1.
Proof.
  intros E H. unfold PB, RXB.PB in H. exists (RXB.a0 inp). pose proof (RXB.a0_len inp Hva) as L.
  assert (E1 : eb E 1%uint63 = RXB.a0 inp ++ [Z_to_bv 8 0]) by (rewrite H; reflexivity).
  assert (E9 : eb E 9%uint63 = LE8 (Z.of_nat (length (RXB.a0 inp)) + 1)) by (rewrite H; reflexivity).
  split; [exact E1|]. split; [exact (RXB.a0_nz inp Hva)|].
  unfold CtrA.SZ. change wzero with (wp 0%uint63). exact (OL.den_param8_u E 9%uint63 _ E9 ltac:(lia)).
Qed.
Lemma PBstr3 : forall E, PB (eb E) -> exists str, eb E 3%uint63 = str ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str /\
  bv_unsigned (den E (CtrA.SZ 10%uint63)) = Z.of_nat (length str) + 1.
Proof.
  intros E H. unfold PB, RXB.PB in H. exists (RXB.p1 inp). pose proof (RXB.p1_len inp Hva) as L.
  assert (E3 : eb E 3%uint63 = RXB.p1 inp ++ [Z_to_bv 8 0]) by (rewrite H; reflexivity).
  assert (E10 : eb E 10%uint63 = LE8 (Z.of_nat (length (RXB.p1 inp)) + 1)) by (rewrite H; reflexivity).
  split; [exact E3|]. split; [exact (RXB.p1_nz inp Hva)|].
  unfold CtrA.SZ. change wzero with (wp 0%uint63). exact (OL.den_param8_u E 10%uint63 _ E10 ltac:(lia)).
Qed.
Lemma PB12 : forall E, PB (eb E) -> bv_unsigned (den E (CtrA.SZ 15%uint63)) = Z.of_nat (length (eb E 12%uint63)).
Proof.
  intros E H. unfold PB, RXB.PB in H.
  assert (E12 : eb E 12%uint63 = SI.strarea inp) by (rewrite H; reflexivity).
  assert (E15 : eb E 15%uint63 = LE8 (Z.of_nat (length (SI.strarea inp)))) by (rewrite H; reflexivity).
  (* LPS 727298f3: the string area's length (the launch's strings, the exec name, its NUL and the
     8-byte slot), under the launch's E2BIG cap ([valid_launch]) *)
  pose proof (SI.length_strarea inp) as L. pose proof (proj2 Hvl) as CAP. unfold launch_bytes, e2big_limit in CAP.
  rewrite E12.
  unfold CtrA.SZ. change wzero with (wp 0%uint63). apply (OL.den_param8_u E 15%uint63 _ E15). unfold SI.LSB in L. lia.
Qed.

Definition CS_roomdrop_b := @HeapCtrW.roomdrop_sound_b CLG Cw (OPS R) (RXB.OPS_plain_R inp sp mb rnd Hva A Cw aw_fds aw_ceil_fds) OPS_holds1 OPS_fp1 MP PB.
Ltac tabcase H :=
  apply imap_of_find_in in H; cbn [In] in H;
  repeat (destruct H as [H|H]; [symmetry in H; injection H as -> ->|]); try (exfalso; exact H).

Lemma ext_N_b :
  RXB.ext_ok_b inp sp mb rnd Hva A Cw aw_fds aw_ceil_fds T_SrcNU.CONTRACTS [].
Proof.
  intros cid ct Hf Hn. pose proof Hf as Hf0. unfold T_SrcNU.CONTRACTS in Hf. tabcase Hf.
  - apply (MemcpyCtrW.memcpy_rr_sound_b (OPS R) (RXB.OPS_plain_R inp sp mb rnd Hva A Cw aw_fds aw_ceil_fds) MP PB). reflexivity.
  - apply (StrCtrW.strnlen_sound_b (OPS R) (RXB.OPS_plain_R inp sp mb rnd Hva A Cw aw_fds aw_ceil_fds) MP PB PBstr1 PBstr3 PB12). reflexivity.
  - apply CS_roomdrop_b.
Qed.
Lemma FamN_b : RXB.FamHypsN_b inp sp mb rnd Hva A Cw aw_fds aw_ceil_fds.
Proof. exact (RXB.FHN inp sp mb rnd Hva A Cw aw_fds aw_ceil_fds ext_N_b). Qed.

Theorem rzb_usage_top : length (in_argv inp) <> 2%nat ->
  rzb SEGS (RXB.c0 inp sp brk0 mb rnd lim) (DrvShape.K inp).
Proof.
  intros HN.
  exact (RXB.rzb_usage_full inp sp brk0 mb rnd lim Hva Hve Hhw Hsz Hvl Hrdr Hen A Cw aw_fds aw_ceil_fds
           cw_init aw_ceil0 aw_init HN FamN_b).
Qed.

End RUN.
End TopB.
