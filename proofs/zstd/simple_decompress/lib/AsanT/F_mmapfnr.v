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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 RT_stubs F_ammap FsKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition AMMAPFNR : Z := 0x703c0.
Definition F_FIXNORES_RW_FLAGS : Z := 16434.       (* [comment removed for export] *)
End CANSEC1.
Notation FNR_STACK := 368 (only parsing).        (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition fnr_cells (m : amem) : Prop :=
     rw_cells bsegs m 0xc72e8 [C8 (Z_to_bv 64 0x15f7a0)]
  /\ rw_cells bsegs m 0x15f7a0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0xc72f8 [C8 (Z_to_bv 64 0x161828); C8 (Z_to_bv 64 0xcd4f8); C8 (Z_to_bv 64 0xcfcf8);
                               C8 (Z_to_bv 64 0xd09e8); C8 (Z_to_bv 64 0xd09f0); C8 (Z_to_bv 64 0xd09e0)]
  /\ rw_cells bsegs m 0x1618b8 [C8 (Z_to_bv 64 0)].

Lemma fnr_cells_frame : forall m m' W, fnr_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> fnr_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x625000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold fnr_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed.

Definition fnr_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ munch [(bv_unsigned sp - FNR_STACK, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size
  /\ fp_bw RNG'
  /\ fnr_cells m'.

Lemma fnr_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - FNR_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size <= 0x10007fff8000 ->
  fnr_cells m ->
  rw_cells bsegs m addr [CB (Z.to_nat size) junk] ->                 (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG addr size ->
  (* [comment removed for export] *)
  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fnr_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap addr size 3 F_FIXNORES_RW_FLAGS) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMMAPFNR) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 AHI RC DST RIMG RSTK RTGT UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & MLIM).
  unfold AMMAPFNR, F_FIXNORES_RW_FLAGS in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - FNR_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               fnr_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }
  (* [comment removed for export] *)
  iprefix.
  carve_frame 48%nat ST.
  do 6 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. if_lit.                                          (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS AHI A0; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite Z.land_comm, land_align4096 by lia; f_equal; clear -AAL A0 AHI SPOS; Z.div_mod_to_equations; lia).
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 48%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carve_frame 272%nat ST.
  do 8 step.                                                   (* [comment removed for export] *)
  step. step. step. if_lit.                                    (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  do 9 step.                                                   (* [comment removed for export] *)
  release_frame FR1 ST (bv_unsigned sp + -96).
  step. setreg 13 (Z_to_bv 64 16434) ltac:(vm_compute; reflexivity).   (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  icallk rt_mmap_stubP.
  intros a RNG' ms' (rsp & HF & Hdec & ->).
  destruct (adec_mmap_rw_Some _ _ _ Hdec) as (ci & -> & AM1 & AM2 & AM3).
  pose proof (page_round_up_mult size SAL ltac:(clear -SPOS; lia)) as PRU. unfold mmap_len in *. rewrite PRU in AM3. rewrite PRU.
  pose proof (fstepA_mmap_grant addr size 16434 _ RNG RNG' (fstepS_fstepA _ _ _ _ HF)) as GR. cbn [eff_ret] in GR.
  rewrite (unsigned_lit a) in GR by (clear -AM2 AM3 SPOS; lia). rewrite (unsigned_lit size) in GR by (clear -SPOS AHI A0; lia).
  rewrite PRU in GR. specialize (GR ltac:(unfold page_size; exact AM1)).
  pose proof HF as HF0. fstepS_transport HF.
  destruct (Z.eq_dec a addr) as [->|NE]. 2: { apply evtF_done. left. split; [exact NE|]. split; [exact AM2| atop_facts; exact AM3]. }
  unfold rt_regs. cbn [eff_ret]. rewrite eff_mem_zeros.
  replace (ret_pc (Z_to_bv 64 0x67f28)) with (Z_to_bv 64 0x67f28 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - FNR_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.
  (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step.                                                        (* [comment removed for export] *)
  step. step. step. step. step. step.                          (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -96) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -48) end.
  (* [comment removed for export] *)
  step. step. step. step. step.                                (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. if_lit.                                          (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. step. step. step. if_lit. step.                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step. step. step. step. step.                    (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -48) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold fnr_post. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR|]. split; [exact BW|].
  unfold fnr_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End CANSEC2.
