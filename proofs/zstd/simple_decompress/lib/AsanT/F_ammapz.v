(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 RT_stubs F_ammap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition mmapz_entry := 0x67fcc.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition mmapz_post (RNG : footprint) (sp : word) (a size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + size <= ATOP
  /\ munch [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' a size /\ rng RNG' (shad a) (shlen size)
  /\ rmap_cells m'.

Lemma mmapz_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> SAL SPOS SZ NAME RC RIMG RSTK FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM). word_range a1 A1R.
  unfold AIMG_HI, mmapz_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (FRESH a = false /\ 0 < a /\ a mod 4096 = 0 /\ a + size <= ATOP /\ fp_le RNG RNG')
                            \/ FRESH a = true /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               mmapz_post RNG sp a size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NF & P1 & P2 & P3 & P4)|[FR PO]]; [apply UNR; assumption|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT; [exact FR | exact PO]. }
  (* [comment removed for export] *)
  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS SZ; Z.div_mod_to_equations; lia).
  step. step. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME A1R. lia. }   (* [comment removed for export] *)
  step. step. step. lstep.                                     (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -48).
  step. setreg 13 (Z_to_bv 64 34) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepS_mmap_grant 0 size 34 _ RNG RNG' HF (eq_refl : Z.land 34 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS SZ; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
  pose proof HF as HF0. destruct HF0 as [[FPLE _] [_ BW]].
  destruct (FRESH a) eqn:HFR.
  2: { fstepS_transport HF. apply evtF_done. left. split; [reflexivity|]. split; [exact AM2|]. split; [exact AM1|]. split; [atop_facts; exact AM3| exact FPLE]. }
  destruct (FROK a HFR AM2 AM3) as [AIM AFR].
  fstepS_transport HF.
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 426068)) with (Z_to_bv 64 426068 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold mmapz_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AM1|]. split; [exact AM2|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rmapd_entry := 0x7079c.
(* [comment removed for export] *)
Notation RMAPD_STACK := 368 (only parsing).

Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv bsegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold rmapd_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  carve_frame 96%nat ST.
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
  step. step. step. step. step.                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  release_frame FR0 ST (bv_unsigned sp + -96).
  step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepS_mmap_grant addr size 50 _ RNG RNG' HF (eq_refl : Z.land 50 MAP_NORESERVE = 0)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS ASZ A0; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)). destruct GR as [GR1 GR2].
  pose proof HF as HF0. fstepS_transport HF.
  destruct (Z.eq_dec a addr) as [->|NE]. 2: { apply evtF_done. left. split; [exact NE|]. split; [exact AM2| atop_facts; exact AM3]. }
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 427204)) with (Z_to_bv 64 427204 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step.        (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -96) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  (* [comment removed for export] *)
  match goal with MUx : munch [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z _ _ |- _ =>
    apply (munch_weaken _ [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MUx;
    [| unfold sub_fp; cbn [outside]; intros x Hx; lia] end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmap_post. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End CANSEC2.
