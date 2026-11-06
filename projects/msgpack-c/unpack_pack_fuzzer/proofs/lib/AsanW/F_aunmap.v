(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 RT_stubs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition unmap_entry := 0x720b0.
End CANSEC1.
Abbreviation UNMAP_STACK := 48.

Section CANSEC2. Context {rc : runConstT}.
Lemma adec_munmap_Some : forall addr len rsp a, adec_munmap addr len rsp = Some a ->
  a = 0 /\ exists ci, rsp = eff0_ci ci (Z_to_bv 64 0)
                   \/ rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] ci.
Proof.
  intros addr len rsp a H. unfold adec_munmap in H.
  destruct (dec_munmap addr len rsp) as [[e|b]|] eqn:D; try discriminate. injection H as <-. split; [reflexivity|].
  destruct (dec_munmap_Some _ _ _ _ D) as [ci E]. exists ci. destruct b; [right| left]; exact E.
Qed.

Section STUB.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).
Lemma rt_munmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len : Z) (x12 x13 x14 x15 x17 : word),
  @implF node asegs (at_nodeA asegs) fst _ RNG (enode (NMunmap addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMunmap addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        (eff_ret rsp) (Z_to_bv 64 len) x12 x13 x14 x15 (Z_to_bv 64 215))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom asegs)))
    (MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 addr) (Z_to_bv 64 len) x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x7086c) fc None m (seg_rom asegs)).
Proof.
  intros fst RNG X dec addr len x12 x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.
End STUB.

Lemma munmap_keep : forall addr len rsp R R' lo n,
  fstepS (NMunmap addr len) rsp R R' -> rng R lo n ->
  (lo + n <= addr \/ addr + mmap_len len <= lo) -> 0 <= addr < 2^64 -> 0 <= len < 2^64 -> rng R' lo n.
Proof.
  intros addr len rsp R R' lo n HF HR HD HA HL. apply fstepS_fstepA in HF.
  eapply fstepA_munmap_rng; [exact HF | exact HR |].
  rewrite !unsigned_lit by lia. unfold mmap_len in HD. exact HD.
Qed.

Definition unmap_cells (m : amem) : Prop :=
     rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8)]
  /\ rw_cells asegs m 0x16b678 [C8 (Z_to_bv 64 0)].

Lemma unmap_or_die_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - UNMAP_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size ->
  AIMG_HI <= addr -> 0 < size -> size mod 4096 = 0 -> addr + size <= ATOP ->
  unmap_cells m ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap addr size) rsp RNG RNG' ->
      munch [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' ->
      mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> unmap_cells m' ->
      implS asegs RNG' (K 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMunmap addr size) (adec_munmap addr size)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 unmap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> APOS SPOS SAL ACE UC RA RIMG RSTK KONT.
  pose proof UC as [GOT LIM]. unfold AIMG_HI, unmap_entry in *. word_range sp SPR.
  pose proof (mmap_len_aligned size SAL) as ML.
  pose proof (munch_refl [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m) as MU.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => a = 0 /\ exists rsp m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fstepS (NMunmap addr size) rsp RNG RNG'
               /\ munch [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m'
               /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ unmap_cells m'
               /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' (-> & PO). destruct_exs PO. destruct PO as (HF & MU' & MI' & ST' & UC' & ->).
       eapply KONT; [exact HF | exact MU' | exact MI' | exact ST' | exact UC']. }

  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 APOS ACE. lia. }
  step.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SPOS ACE APOS. lia. }
  step. step. step.
  step.

  icallk rt_munmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_munmap_Some _ _ _ _ Hdec) as (-> & ci & SH).
  assert (HA : 0 <= addr < 2^64) by (clear -ACE APOS SPOS; lia). assert (HL : 0 <= size < 2^64) by (clear -ACE APOS SPOS; lia).
  assert (D1 : lo + (bv_unsigned sp - lo) <= addr \/ addr + mmap_len size <= lo) by (clear -ACE CEIL APOS SPOS ML; lia).
  assert (D2 : 0x10000 + 0x61f000 <= addr \/ addr + mmap_len size <= 0x10000) by (clear -ACE CEIL LO SPR APOS SPOS ML; lia).
  apply (munmap_keep _ _ _ _ _ _ _ HF) in RSTK; [| exact D1 | exact HA | exact HL].
  unfold rng_aimg in RIMG. apply (munmap_keep _ _ _ _ _ _ _ HF) in RIMG; [| exact D2 | exact HA | exact HL].
  fold (rng_aimg RNG') in RIMG. clear D1 D2.
  unfold rt_regs.
  replace (ret_pc (Z_to_bv 64 467168)) with (Z_to_bv 64 467168 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  destruct SH as [-> | ->];
    [   cbn [eff_ret]; rewrite eff_mem_eff0
    |   cbn [eff_ret]; rewrite eff_mem_unmaps; rewrite ML; sys_mem_unmaps ].
  all: step; step; step; step.
  all: step.
  all: step; step; step; if_lit.
  all: zstep; step.
  all: change (Z.b2z (18446744073709547520 <? 0)) with 0.
  all: step; if_lit.
  all: step; step.
  all: step; step; step; step; if_lit.
  all: step.
  all: step; step; step; step; step; step.
  all: lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -48) _ |- _ =>
         lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; split; [reflexivity|].
  all: eexists (_ : resp); do 16 eexists; split; [exact HF|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: split; [split; eassumption| reflexivity].
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB RT_stubs.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition unmap_entry := 0x72a40.
End CANSEC1.
Abbreviation UNMAP_STACK := 48.

Section CANSEC2. Context {rc : runConstT}.
Lemma adec_munmap_Some : forall addr len rsp a, adec_munmap addr len rsp = Some a ->
  a = 0 /\ exists ci, rsp = eff0_ci ci (Z_to_bv 64 0)
                   \/ rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] ci.
Proof.
  intros addr len rsp a H. unfold adec_munmap in H.
  destruct (dec_munmap addr len rsp) as [[e|b]|] eqn:D; try discriminate. injection H as <-. split; [reflexivity|].
  destruct (dec_munmap_Some _ _ _ _ D) as [ci E]. exists ci. destruct b; [right| left]; exact E.
Qed.

Section STUB.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).
Lemma rt_munmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len : Z) (x12 x13 x14 x15 x17 : word),
  @implF node bsegs (at_nodeA bsegs) fst _ RNG (enode (NMunmap addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMunmap addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                        (eff_ret rsp) (Z_to_bv 64 len) x12 x13 x14 x15 (Z_to_bv 64 215))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom bsegs)))
    (MS (rt_regs ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               (Z_to_bv 64 addr) (Z_to_bv 64 len) x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x711fc) fc None m (seg_rom bsegs)).
Proof.
  intros fst RNG X dec addr len x12 x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.
End STUB.

Lemma munmap_keep : forall addr len rsp R R' lo n,
  fstepS (NMunmap addr len) rsp R R' -> rng R lo n ->
  (lo + n <= addr \/ addr + mmap_len len <= lo) -> 0 <= addr < 2^64 -> 0 <= len < 2^64 -> rng R' lo n.
Proof.
  intros addr len rsp R R' lo n HF HR HD HA HL. apply fstepS_fstepA in HF.
  eapply fstepA_munmap_rng; [exact HF | exact HR |].
  rewrite !unsigned_lit by lia. unfold mmap_len in HD. exact HD.
Qed.

Definition unmap_cells (m : amem) : Prop :=
     rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8)]
  /\ rw_cells bsegs m 0x16d838 [C8 (Z_to_bv 64 0)].

Lemma unmap_or_die_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - UNMAP_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size ->
  AIMG_HI <= addr -> 0 < size -> size mod 4096 = 0 -> addr + size <= ATOP ->
  unmap_cells m ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap addr size) rsp RNG RNG' ->
      munch [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' ->
      mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp) -> unmap_cells m' ->
      implS bsegs RNG' (K 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMunmap addr size) (adec_munmap addr size)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 unmap_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> APOS SPOS SAL ACE UC RA RIMG RSTK KONT.
  pose proof UC as [GOT LIM]. unfold AIMG_HI, unmap_entry in *. word_range sp SPR.
  pose proof (mmap_len_aligned size SAL) as ML.
  pose proof (munch_refl [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m) as MU.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => a = 0 /\ exists rsp m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fstepS (NMunmap addr size) rsp RNG RNG'
               /\ munch [(bv_unsigned sp - UNMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m'
               /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp) /\ unmap_cells m'
               /\ ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' (-> & PO). destruct_exs PO. destruct PO as (HF & MU' & MI' & ST' & UC' & ->).
       eapply KONT; [exact HF | exact MU' | exact MI' | exact ST' | exact UC']. }

  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 APOS ACE. lia. }
  step.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SPOS ACE APOS. lia. }
  step. step. step.
  step.

  icallk rt_munmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_munmap_Some _ _ _ _ Hdec) as (-> & ci & SH).
  assert (HA : 0 <= addr < 2^64) by (clear -ACE APOS SPOS; lia). assert (HL : 0 <= size < 2^64) by (clear -ACE APOS SPOS; lia).
  assert (D1 : lo + (bv_unsigned sp - lo) <= addr \/ addr + mmap_len size <= lo) by (clear -ACE CEIL APOS SPOS ML; lia).
  assert (D2 : 0x10000 + 0x621000 <= addr \/ addr + mmap_len size <= 0x10000) by (clear -ACE CEIL LO SPR APOS SPOS ML; lia).
  apply (munmap_keep _ _ _ _ _ _ _ HF) in RSTK; [| exact D1 | exact HA | exact HL].
  unfold rng_aimg in RIMG. apply (munmap_keep _ _ _ _ _ _ _ HF) in RIMG; [| exact D2 | exact HA | exact HL].
  fold (rng_aimg RNG') in RIMG. clear D1 D2.
  unfold rt_regs.
  replace (ret_pc (Z_to_bv 64 469616)) with (Z_to_bv 64 469616 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  destruct SH as [-> | ->];
    [   cbn [eff_ret]; rewrite eff_mem_eff0
    |   cbn [eff_ret]; rewrite eff_mem_unmaps; rewrite ML; sys_mem_unmaps ].
  all: step; step; step; step.
  all: step.
  all: step; step; step; if_lit.
  all: zstep; step.
  all: change (Z.b2z (18446744073709547520 <? 0)) with 0.
  all: step; if_lit.
  all: step; step.
  all: step; step; step; step; if_lit.
  all: step.
  all: step; step; step; step; step; step.
  all: lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -48) _ |- _ =>
         lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; split; [reflexivity|].
  all: eexists (_ : resp); do 16 eexists; split; [exact HF|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: split; [split; eassumption| reflexivity].
Qed.
End CANSEC2.
End TwinB.
