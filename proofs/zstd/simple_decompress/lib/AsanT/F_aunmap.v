(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 RT_stubs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition unmap_entry := 0x67f50.
End CANSEC1.
Abbreviation UNMAP_STACK := 48.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma adec_munmap_Some : forall addr len rsp a, adec_munmap addr len rsp = Some a ->
  a = 0 /\ exists ci, rsp = eff0_ci ci (Z_to_bv 64 0)
                   \/ rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] ci.
Proof.
  intros addr len rsp a H. unfold adec_munmap in H.
  destruct (dec_munmap addr len rsp) as [[e|b]|] eqn:D; try discriminate. injection H as <-. split; [reflexivity|].
  destruct (dec_munmap_Some _ _ _ _ D) as [ci E]. exists ci. destruct b; [right| left]; exact E.
Qed.

(* [comment removed for export] *)
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
        F (Z_to_bv 64 0x6670c) fc None m (seg_rom bsegs)).
Proof.
  intros fst RNG X dec addr len x12 x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.
End STUB.

(* [comment removed for export] *)
Lemma munmap_keep : forall addr len rsp R R' lo n,
  fstepS (NMunmap addr len) rsp R R' -> rng R lo n ->
  (lo + n <= addr \/ addr + mmap_len len <= lo) -> 0 <= addr < 2^64 -> 0 <= len < 2^64 -> rng R' lo n.
Proof.
  intros addr len rsp R R' lo n HF HR HD HA HL. apply fstepS_fstepA in HF.
  eapply fstepA_munmap_rng; [exact HF | exact HR |].
  rewrite !unsigned_lit by lia. unfold mmap_len in HD. exact HD.
Qed.

(* [comment removed for export] *)
Definition unmap_cells (m : amem) : Prop :=
     rw_cells bsegs m 0xc72f8 [C8 (Z_to_bv 64 0x161828)]
  /\ rw_cells bsegs m 0x1618b8 [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 APOS ACE. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 SPOS ACE APOS. lia. }   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_munmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_munmap_Some _ _ _ _ Hdec) as (-> & ci & SH).
  assert (HA : 0 <= addr < 2^64) by (clear -ACE APOS SPOS; lia). assert (HL : 0 <= size < 2^64) by (clear -ACE APOS SPOS; lia).
  assert (D1 : lo + (bv_unsigned sp - lo) <= addr \/ addr + mmap_len size <= lo) by (clear -ACE CEIL APOS SPOS ML; lia).
  assert (D2 : 0x10000 + 0x615000 <= addr \/ addr + mmap_len size <= 0x10000) by (clear -ACE CEIL LO SPR APOS SPOS ML; lia).
  apply (munmap_keep _ _ _ _ _ _ _ HF) in RSTK; [| exact D1 | exact HA | exact HL].
  unfold rng_aimg in RIMG. apply (munmap_keep _ _ _ _ _ _ _ HF) in RIMG; [| exact D2 | exact HA | exact HL].
  fold (rng_aimg RNG') in RIMG. clear D1 D2.
  unfold rt_regs.
  replace (ret_pc (Z_to_bv 64 425856)) with (Z_to_bv 64 425856 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  destruct SH as [-> | ->];
    [ (* [comment removed for export] *) cbn [eff_ret]; rewrite eff_mem_eff0
    | (* [comment removed for export] *) cbn [eff_ret]; rewrite eff_mem_unmaps; rewrite ML; sys_mem_unmaps ].
  all: step; step; step; step.                                 (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; if_lit.                               (* [comment removed for export] *)
  all: zstep; step.                                            (* [comment removed for export] *)
  all: change (Z.b2z (18446744073709547520 <? 0)) with 0.
  all: step; if_lit.                                           (* [comment removed for export] *)
  all: step; step.                                             (* [comment removed for export] *)
  all: step; step; step; step; if_lit.                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; step; step; step.                     (* [comment removed for export] *)
  all: lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -48) _ |- _ =>
         lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; split; [reflexivity|].
  all: eexists (_ : resp); do 16 eexists; split; [exact HF|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: split; [split; eassumption| reflexivity].
Qed.
End CANSEC2.
