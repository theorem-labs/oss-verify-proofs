(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_F_malloc_enframe A_MallocTree A_MallocFacts_A A_MallocKit_A A_MallocKit_AB A_MallocKit_A2 A_MallocKit_A3 A_MallocKit_B A_MallocKit_B3 A_MallocModel_B.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_Malloc_fp A_MallocNat A_MallocFacts_AS A_ASlot_W0 A_ASlot_W1 A_ASlot_I A_ASlot_W2 A_ASlot_W3 A_ASlot_W4 A_ASlot_W5 A_ASlot_W6 A_ASlot_W7 A_ASlot_W8 A_F_ntf_C.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 junk; C8 (wz ssp_canary); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
  rmrep st' m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk rsegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
  munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono rsegs m0 m ->
  evt rsegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom rsegs)
      /\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rmrep st' m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x49700) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR' MI FR ST LO LOLE MU WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  pose_ceil; unfold RSSP_GUARD, rta_frame in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.

  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

  st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

Lemma rfin_walk :
  forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
  bv_unsigned gw = G ->
  rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk rsegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' a3' : word) m' k,
      0 <= k < 32 /\ lowbit mask = 2 ^ k /\
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x49040) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros HG FR ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
  unfold meta_cells in CH. rewrite <- HG in CH.
  destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
  assert (P2 : 0 < 2 ^ k <= mask).
  { destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  pose_ceil; unfold rta_frame, RSSP_GUARD in *.

  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.

  step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).

  pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl rsegs m) as WMg.
  step.
  lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- _ =>
    apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
             (meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
    [| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
     | reflexivity | cbn; tauto ];
    rewrite HG in H;
    pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
  end.

  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.

  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. step. step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
  step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.

  step.
  rewrite ?LB in MR1.
  eapply evt_mono.
  { eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
      [exact MR1 | assumption | exact FR | exact ST | pose_ceil; lia | lia | exact MU | exact WM]. }
  cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
  do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_enframe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocTree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A3 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_B3 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocModel_B.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_fp OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocNat OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_AS OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W0 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W1 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_I OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W3 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W4 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W5 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W6 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W7 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_ASlot_W8 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_ntf_C.
Import RMallocRep.TwinB RMallocTree.TwinB RF_get_meta.TwinB RMallocKit_B.TwinB RMallocKit_B2.TwinB RMallocKit_B3.TwinB RF_mm_syscalls.TwinB RMallocKit_A.TwinB RMallocKit_A2.TwinB RMalloc_fp.TwinB RF_enframe.TwinB RF_malloc_entry.TwinB RF_malloc_small.TwinB RF_ntf_A.TwinB RF_ntf_C.TwinB RAllocSlot_iface.TwinB RASlot_I.TwinB RMallocKit_A3.TwinB.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 junk; C8 (wz ssp_canary); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
  rmrep st' m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk rsegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
  munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono rsegs m0 m ->
  evt rsegs (fun ms' => exists (a1' a2' : word) m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom rsegs)
      /\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rmrep st' m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4af04) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR' MI FR ST LO LOLE MU WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  pose_ceil; unfold RSSP_GUARD, rta_frame in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.

  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

  st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; pose_ceil; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

Lemma rfin_walk :
  forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
  bv_unsigned gw = G ->
  rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk rsegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a1' a2' a3' : word) m' k,
      0 <= k < 32 /\ lowbit mask = 2 ^ k /\
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4a844) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros HG FR ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
  unfold meta_cells in CH. rewrite <- HG in CH.
  destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
  assert (P2 : 0 < 2 ^ k <= mask).
  { destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  pose_ceil; unfold rta_frame, RSSP_GUARD in *.

  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.

  step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).

  pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl rsegs m) as WMg.
  step.
  lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- _ =>
    apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
             (meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
    [| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
     | reflexivity | cbn; tauto ];
    rewrite HG in H;
    pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
  end.

  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.

  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. step. step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
  step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.

  step.
  rewrite ?LB in MR1.
  eapply evt_mono.
  { eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
      [exact MR1 | assumption | exact FR | exact ST | pose_ceil; lia | lia | exact MU | exact WM]. }
  cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
  do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.

End CEIL.
End TwinB.
