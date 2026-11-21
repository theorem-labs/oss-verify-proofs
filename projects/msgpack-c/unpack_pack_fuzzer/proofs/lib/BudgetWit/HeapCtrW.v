(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Br/HeapCtr.v: the roomdrop contract's soundness restated over BudgetWit.Rzb.rzb *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Tac Image ZBridge SysStep SFModel ITree Nodes NodesM Decode DecodeM Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog MSafe KLink KStep KOwn KStepC A_MallocBlocks A_MallocHINV A_Malloc_iface A_MallocTree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_aligned16.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue RegsEqv TreeBridgeN KRel MPath Room HeapCore MF AW RMallocG RAllocG CtrFX HeapCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb PlanSoundB.
Set Keyed Unification.
Import ListNotations.
Import W64 Val FI St Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp CtrFX PlanSB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.

Module HeapCtrW.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma ERRNO_eq : to_Z ERRNO = RERRNO. Proof. reflexivity. Qed.
Lemma LIBC_eq : to_Z LIBC = RLIBC. Proof. reflexivity. Qed.
Lemma GOT_eq : to_Z GOT = RGOT_SSP. Proof. reflexivity. Qed.
Lemma GUARD_eq : to_Z GUARD = RSSP_GUARD. Proof. reflexivity. Qed.
Lemma TP_eq : to_Z TP = RATP. Proof. reflexivity. Qed.
Lemma NEED_LOCKS_eq : to_Z (PrimInt63.add LIBC 3%uint63) = RNEED_LOCKS. Proof. reflexivity. Qed.
Lemma PAGE_SIZE_eq : to_Z (PrimInt63.add LIBC 48%uint63) = RPAGE_SIZE. Proof. reflexivity. Qed.
Lemma AUXV_CELL_eq : to_Z (PrimInt63.add LIBC 8%uint63) = RAUXV_CELL. Proof. reflexivity. Qed.

Lemma wr_NEED_LOCKS : Mem.abs_writable rsegs RNEED_LOCKS 1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_PAGE_SIZE : Mem.abs_writable rsegs RPAGE_SIZE 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_AUXV_CELL : Mem.abs_writable rsegs RAUXV_CELL 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_GOT : Mem.abs_writable rsegs RGOT_SSP 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_GUARD : Mem.abs_writable rsegs RSSP_GUARD 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_ERRNO : Mem.abs_writable rsegs RERRNO 4 = true. Proof. vm_compute. reflexivity. Qed.

Lemma rom_of_seg_rom : St.rom_of rsegs = seg_rom rsegs.
Proof. reflexivity. Qed.

Lemma rb_mrd : forall m a, rb rsegs m a = mrd rsegs m (wa a).
Proof. reflexivity. Qed.

Lemma wb_wview : forall m a, wb rsegs m a = true <-> wview rsegs m (wa a) <> None.
Proof. intros m a. unfold wb, wa. destruct (wview rsegs m (Z_to_bv 64 a)); split; congruence. Qed.

Lemma bytes_at_of_ov_read : forall m a n bs,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa a) n = Some bs -> bytes_at rsegs m a bs.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs Ha Hn H.
  - cbn in H. injection H as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [ov_read_bytes] in H. fold (mrd rsegs m (wa a)) in H.
    change (match m (wa a) with Some b => Some b | None => match memory_read rsegs (wa a) 1 with Some (b :: _) => Some b | _ => None end end)
      with (mrd rsegs m (wa a)) in H.
    destruct (mrd rsegs m (wa a)) as [b|] eqn:Hb; [|discriminate].
    destruct (ov_read_bytes rsegs m (wa a + 1)%bv n) as [bs'|] eqn:Hr; [|discriminate]. injection H as <-.
    rewrite wa_succ in Hr. pose proof (IH (a + 1) bs' ltac:(lia) ltac:(lia) Hr) as (_ & L & B).
    split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply B. cbn in Hi. lia.
Qed.

Lemma ov_read_bytes_length : forall m a n bs, ov_read_bytes rsegs m a n = Some bs -> length bs = n.
Proof.
  intros m a n. revert a. induction n as [|n IH]; intros a bs H; cbn [ov_read_bytes] in H.
  - injection H as <-. reflexivity.
  - destruct (match m a with Some b => Some b | None => _ end); [|discriminate].
    destruct (ov_read_bytes rsegs m (a + 1)%bv n) eqn:R; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH. exact R.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
    pose proof (bytes_le_to_Z_nonneg bs) as NN.
    unfold bv_wrap. replace (bv_modulus 8) with 256 by reflexivity.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. pose proof (bytes_le_to_Z_nonneg bs) as NN.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. rewrite Z.add_0_r. exact IH.
Qed.

Lemma bytes_val_false_eq : forall n bs, length bs = n -> (1 <= n <= 8)%nat ->
  bv_unsigned (bytes_val false (Z.of_nat n) bs) = bytes_le_to_Z bs.
Proof.
  intros n bs Hl Hn. unfold bytes_val. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B.
  assert (P : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (ext_Z_small_id false (Z.of_nat n) (bytes_le_to_Z bs)).
  1:{ apply bv_wrap_small. rewrite bv_modulus_64, two64_eq. lia. }
  1:{ lia. }
  1:{ rewrite two64_eq. lia. }
  rewrite Z.sub_0_r. exact B.
Qed.

Lemma lit_load_bytes : forall E n bs (x : int),
  length bs = n -> (n <= 8)%nat ->
  den E (VL (wlit x)) = bytes_val false (Z.of_nat n) bs ->
  bs = Z_to_le_bytes n (to_Z x).
Proof.
  intros E n bs x Hl Hn H.
  destruct n as [|n']. { destruct bs; [reflexivity| discriminate]. }
  assert (E1 : to_Z x = bytes_le_to_Z bs).
  { apply (f_equal bv_unsigned) in H. rewrite unsigned_VL, wlit_ok in H. rewrite (bytes_val_false_eq (S n') bs Hl ltac:(lia)) in H. exact H. }
  rewrite E1, <- Hl. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Lemma load8_bytes : forall E bs v, length bs = 8%nat -> den E v = bytes_val false 8 bs -> bs = le8 (den E v).
Proof.
  intros E bs v Hl H. unfold le8, word_to_le_bytes. rewrite H, (bytes_val_false_eq 8 bs Hl ltac:(lia)), <- Hl.
  symmetry. apply Z_to_le_bytes_to_Z.
Qed.
Lemma load4_bytes : forall E bs v, length bs = 4%nat -> den E v = bytes_val false 4 bs -> bs = le4 (den E v).
Proof.
  intros E bs v Hl H. unfold le4. rewrite H, (bytes_val_false_eq 4 bs Hl ltac:(lia)), <- Hl.
  symmetry. apply Z_to_le_bytes_to_Z.
Qed.

Variable Cw : client_world.
Variable OPS : St.optable.

Hypothesis OPS_plain : St.plain_table OPS.

Hypothesis OPS_holds1 : forall args m mo, St.op_holds OPS HEAP_ID args m mo = heap_holds rsegs IMGX AWI Cw args m mo.
Hypothesis OPS_fp1 : forall args, St.op_fp OPS HEAP_ID args = heap_fp IMGX args.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Variable CANARY : sv.
Hypothesis PB_canary : forall E, PB (eb E) -> den E CANARY = Z_to_bv 64 ssp_canary.
Hypothesis PB_secret : forall E, PB (eb E) -> forall i, (i < 8)%nat ->
  nth_error (eb E 6%uint63) (8 + i) = nth_error (le8 (wz ctx_secret)) i.

Lemma st_ok_set_A : forall E st ms mo hargs a a' md nw rest,
  St.st_ok rsegs OPS E st ms mo ->
  find_op HEAP_ID (s_ops st) = Some hargs -> hargs = VL md :: a :: VL nw :: rest ->
  (forall s LBf mo', pclaim (bv_unsigned (den E a)) s LBf mo' -> pclaim (bv_unsigned (den E a')) s LBf mo') ->
  St.st_ok rsegs OPS E (set_ops st (set_op HEAP_ID (VL md :: a' :: VL nw :: rest) (s_ops st))) ms mo.
Proof.
  intros E st ms mo hargs a a' md nw rest HS Hf -> HR.
  pose proof (ops_hold_find OPS E (s_ops st) (ms_mem ms) mo HEAP_ID _ (St.so_ops _ _ _ _ _ _ HS) Hf) as HH.
  rewrite OPS_holds1 in HH. destruct HH as (md' & aw & ws & ca & LB & D & HA & WF & HC).
  destruct (decode_set_A E (VL md) a a' (VL nw) rest md' aw ws ca D) as [D' ->].
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf Hcov Hminv].
  split; cbn [set_ops s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - eapply ops_hold_set_op1; [exact Hf| exact Hops|]. rewrite OPS_holds1.
    exists md', (den E a'), ws, ca, LB. split; [exact D'|]. split; [| split; [exact WF| exact HC]].
    destruct HA as ((s & LBf & P & RC & K & MT & RM & RP) & NGW). apply aw_holdsW_intro; [| exact NGW]. exists s, LBf. repeat (split; [assumption|]). split; [| exact RP].
    apply HR. exact RM.
  - eapply ops_apart_set_op1; [exact Hf| exact Hapart|]. rewrite !OPS_fp1. unfold heap_fp. rewrite D, D'. reflexivity.
  -
    intros x _. apply St.plain_cover. exact OPS_plain.
Qed.

Theorem roomdrop_sound_b : forall pc, contract_sound_b rsegs OPS MP PB (CtrM.roomdrop_c pc).
Proof.
  intros pc st sts Hpc Happ K E ms mo HS HMP HPB HK. cbn [c_apply CtrM.roomdrop_c] in Happ. unfold CtrM.roomdrop_apply in Happ.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [|discriminate].
  destruct (heap_A hargs) as [[j| | | | | | | | | |]|] eqn:HA; try discriminate.
  destruct (heap_set_A hargs (VL wones)) as [hargs'|] eqn:HS'; [|discriminate]. injection Happ as <-.
  destruct (heap_set_A_shape hargs (VL wones) hargs' HS') as (md & A & nw & rest & -> & ->).
  apply (HK _ (or_introl eq_refl) E ms mo (env_ext_refl _ E) HMP).
  eapply st_ok_set_A; [exact HS| exact Hf| reflexivity|].
  intros s LBf mo' _. apply pclaim_none. rewrite unsigned_VL. change (w2Z wones) with (2^64 - 1). lia.
Qed.
End CEIL.
End HeapCtrW.
