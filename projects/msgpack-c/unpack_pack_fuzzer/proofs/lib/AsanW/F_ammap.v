(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase AKit AKit2 RT_stubs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_ammap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rmap_entry := 0x7a7b0.
End CANSEC1.
Notation RMAP_STACK := 400 (only parsing).
Notation RMAPD_STACK := 368 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition rmap_cells (m : amem) : Prop :=
     rw_cells asegs m 0xd14f8 [C8 (Z_to_bv 64 0x169560)]
  /\ rw_cells asegs m 0x169560 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8); C8 (Z_to_bv 64 0xd72b8); C8 (Z_to_bv 64 0xd9ab8);
                               C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a0)]
  /\ rw_cells asegs m 0x16b6ec [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x16b678 [C8 (Z_to_bv 64 0)].

Lemma rmap_cells_frame : forall m m' W, rmap_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> rmap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x62f000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold rmap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed.

Definition rmap_post_g (STKN : Z) (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ addr + size <= ATOP
  /\ munch [(bv_unsigned sp - STKN, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size /\ rng RNG' (shad addr) (shlen size)
  /\ fp_bw RNG'
  /\ rmap_cells m'.

Definition rmap_post := rmap_post_g RMAP_STACK.
Definition rmapd_post := rmap_post_g RMAPD_STACK.

Lemma page_round_up_mult : forall s, s mod 4096 = 0 -> 0 <= s -> page_round_up_Z s = s.
Proof. intros s Hs H0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

Lemma land_align4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x - x mod 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_align2p18 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = x - x mod 262144.
Proof.
  intros x Hx.
  replace 18446744073709289472 with (Z.ldiff (Z.ones 64) (Z.ones 18)) by reflexivity.
  replace (x - x mod 262144) with (Z.shiftl (Z.shiftr x 18) 18).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^18) with 262144. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma adec_mmap_rw_Some : forall len rsp a, adec_mmap ATOP len 3 rsp = Some a ->
  exists ci, rsp = mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci
          /\ a mod 4096 = 0 /\ 0 < a /\ a + mmap_len len <= ATOP.
Proof.
  intros len rsp a H. unfold adec_mmap in H. cbn [Z.eqb] in H.
  destruct (dec_mmap ATOP len [] rsp) as [[e|a']|] eqn:D; try discriminate. injection H as <-.
  destruct (dec_mmap_Some _ _ _ _ _ D) as [ci [E OK]]. exists ci. split; [exact E|].
  pose proof (mmap_addr_ok_true _ _ _ _ OK) as [(M1 & M2 & M3) _]. unfold page_size in M1. auto.
Qed.

Lemma rmap_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->

  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> NAME AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold rmap_entry in *. word_range sp SPR. word_range a3 A3R.
  pose proof (munch_refl [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }

  iprefix.

  carve_frame 32%nat ST.
  step. step. step. step. step.
  step. step. step. step. step.
  step.
  step. step. step.
  carve_frame 96%nat ST.
  step. step. step. step. step. step. step.
  step. step. step.
  step. step. step.
  step. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
  step. if_lit.
  zstep.
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
  step. step. step. step. step.

  step.
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.
  step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME. lia. }
  step. step. step. lstep.
  zstep. step. if_lit.
  zstep.
  step. step. step. step. step. step. step. step. step.
  release_frame FR1 ST (bv_unsigned sp + -128).
  step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).
  step. step. step. step. step.
  step.

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
  replace (ret_pc (Z_to_bv 64 468516)) with (Z_to_bv 64 468516 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.

  step. step. step.
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.
  step. step.
  step. step. step. step. if_lit. step.
  step. step. step. step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -128) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -32) end.

  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 A0 ASZ SPOS. lia. }
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmap_post, rmap_post_g. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End CANSEC2.
End F_ammap.

Module F_ammapz.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs. Import F_ammap.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition mmapz_entry := 0x7212c.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition mmapz_post (RNG : footprint) (sp : word) (a size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + size <= ATOP
  /\ munch [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z m m' /\ wmono asegs m m'
  /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' a size /\ rng RNG' (shad a) (shlen size)
  /\ rmap_cells m'.

Lemma mmapz_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - MMAPZ_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 size -> size mod 4096 = 0 -> 0 < size -> size < 2^40 -> bv_unsigned a1 <> 0 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->

  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->

  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->

  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> mmapz_post RNG sp a size lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 size 3 34) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 mmapz_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> SAL SPOS SZ NAME RC RIMG RSTK FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM). word_range a1 A1R.
  unfold AIMG_HI, mmapz_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (FRESH a = false /\ 0 < a /\ a mod 4096 = 0 /\ a + size <= ATOP /\ fp_le RNG RNG')
                            \/ FRESH a = true /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               mmapz_post RNG sp a size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NF & P1 & P2 & P3 & P4)|[FR PO]]; [apply UNR; assumption|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT; [exact FR | exact PO]. }

  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.
  step.
  step. step. step.
  step.
  step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 9 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS SZ; Z.div_mod_to_equations; lia).
  step. step. step. step. step.

  step.
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.
  step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME A1R. lia. }
  step. step. step. lstep.
  zstep. step. if_lit.
  zstep.
  step. step. step. step. step. step. step. step. step.
  release_frame FR0 ST (bv_unsigned sp + -48).
  step. setreg 13 (Z_to_bv 64 34) ltac:(vm_compute; reflexivity).
  step. step. step. step. step.
  step.

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
  replace (ret_pc (Z_to_bv 64 467380)) with (Z_to_bv 64 467380 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.

  step. step. step.
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.
  step. step.
  step. step. step. step. if_lit. step.
  step. step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -48) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold mmapz_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AM1|]. split; [exact AM2|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.

Definition rmapd_entry := 0x7a8fc.
Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv asegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->

  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmapd_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmapd_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> -> AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold rmapd_entry in *. word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmapd_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom asegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }

  iprefix.
  step. step. step. step.
  step. step. step.
  carve_frame 96%nat ST.
  step. step. step. step. step. step. step.
  step. step. step.
  step. step. step.
  step. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
  step. if_lit.
  zstep.
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
  step. step. step. step. step.

  step.
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.
  step. step.
  step. if_lit.
  zstep.
  step. step. step. step. step. step. step. step. step.
  release_frame FR0 ST (bv_unsigned sp + -96).
  step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).
  step. step. step. step. step.
  step.

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
  replace (ret_pc (Z_to_bv 64 468516)) with (Z_to_bv 64 468516 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.

  step. step. step.
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.
  step. step.
  step. step. step. step. if_lit. step.
  step. step. step. step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -96) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmapd_post, rmap_post_g. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End CANSEC2.
End F_ammapz.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_ammap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rmap_entry := 0x7b140.
End CANSEC1.
Notation RMAP_STACK := 400 (only parsing).
Notation RMAPD_STACK := 368 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition rmap_cells (m : amem) : Prop :=
     rw_cells bsegs m 0xd3610 [C8 (Z_to_bv 64 0x16b720)]
  /\ rw_cells bsegs m 0x16b720 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8); C8 (Z_to_bv 64 0xd9478); C8 (Z_to_bv 64 0xdbc78);
                               C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc960)]
  /\ rw_cells bsegs m 0x16d8ac [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x16d838 [C8 (Z_to_bv 64 0)].

Lemma rmap_cells_frame : forall m m' W, rmap_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> rmap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x631000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold rmap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]).
Qed.

Definition rmap_post_g (STKN : Z) (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ addr + size <= ATOP
  /\ munch [(bv_unsigned sp - STKN, bv_unsigned sp); (addr, addr + size)]%Z m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' addr [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
  /\ rng RNG' addr size /\ rng RNG' (shad addr) (shlen size)
  /\ fp_bw RNG'
  /\ rmap_cells m'.

Definition rmap_post := rmap_post_g RMAP_STACK.
Definition rmapd_post := rmap_post_g RMAPD_STACK.

Lemma page_round_up_mult : forall s, s mod 4096 = 0 -> 0 <= s -> page_round_up_Z s = s.
Proof. intros s Hs H0. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. nia. Qed.

Lemma land_align4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx.
  replace 18446744073709547520 with (Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity.
  replace (x - x mod 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma land_align2p18 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = x - x mod 262144.
Proof.
  intros x Hx.
  replace 18446744073709289472 with (Z.ldiff (Z.ones 64) (Z.ones 18)) by reflexivity.
  replace (x - x mod 262144) with (Z.shiftl (Z.shiftr x 18) 18).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^18) with 262144. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma adec_mmap_rw_Some : forall len rsp a, adec_mmap ATOP len 3 rsp = Some a ->
  exists ci, rsp = mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci
          /\ a mod 4096 = 0 /\ 0 < a /\ a + mmap_len len <= ATOP.
Proof.
  intros len rsp a H. unfold adec_mmap in H. cbn [Z.eqb] in H.
  destruct (dec_mmap ATOP len [] rsp) as [[e|a']|] eqn:D; try discriminate. injection H as <-.
  destruct (dec_mmap_Some _ _ _ _ _ D) as [ci [E OK]]. exists ci. split; [exact E|].
  pose proof (mmap_addr_ok_true _ _ _ _ OK) as [(M1 & M2 & M3) _]. unfold page_size in M1. auto.
Qed.

Lemma rmap_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAP_STACK ->
  mem_inv bsegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> 0x10000 <= bv_unsigned a3 < 2^47 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->

  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmap_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (K addr) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap addr size 3 50) (adec_mmap ATOP size 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmap_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> NAME AAL SAL SPOS A0 ASZ RC RIMG RSTK UNR KONT. unfold AIMG_HI in A0.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold rmap_entry in *. word_range sp SPR. word_range a3 A3R.
  pose proof (munch_refl [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  eapply (implF_ebind _ _ _ _ _ _ _
            (fun a RNG' ms' => (a <> addr /\ 0 < a /\ a + size <= ATOP) \/ a = addr /\ exists m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
               rmap_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }

  iprefix.

  carve_frame 32%nat ST.
  step. step. step. step. step.
  step. step. step. step. step.
  step.
  step. step. step.
  carve_frame 96%nat ST.
  step. step. step. step. step. step. step.
  step. step. step.
  step. step. step.
  step. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
  step. if_lit.
  zstep.
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
  step. step. step. step. step.

  step.
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.
  step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME. lia. }
  step. step. step. lstep.
  zstep. step. if_lit.
  zstep.
  step. step. step. step. step. step. step. step. step.
  release_frame FR1 ST (bv_unsigned sp + -128).
  step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).
  step. step. step. step. step.
  step.

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
  replace (ret_pc (Z_to_bv 64 470964)) with (Z_to_bv 64 470964 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - RMAP_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.

  step. step. step.
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.
  step. step.
  step. step. step. step. if_lit. step.
  step. step. step. step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -128) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp + -32) end.

  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 A0 ASZ SPOS. lia. }
  step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmap_post, rmap_post_g. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End CANSEC2.
End F_ammap.

Module F_ammapz.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB. Import F_ammap.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition mmapz_entry := 0x72abc.
End CANSEC1.
Notation MMAPZ_STACK := 320 (only parsing).

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

  (forall a, FRESH a = true -> 0 < a -> a + size <= ATOP -> AIMG_HI <= a /\ (a + size <= bv_unsigned sp - 48 \/ bv_unsigned sp <= a)) ->

  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + size <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->

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

  iprefix.
  carve_frame 48%nat ST.
  step. step. step. step. step.
  step.
  step. step. step.
  step.
  step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 9 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS SZ; Z.div_mod_to_equations; lia).
  step. step. step. step. step.

  step.
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.
  step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 NAME A1R. lia. }
  step. step. step. lstep.
  zstep. step. if_lit.
  zstep.
  step. step. step. step. step. step. step. step. step.
  release_frame FR0 ST (bv_unsigned sp + -48).
  step. setreg 13 (Z_to_bv 64 34) ltac:(vm_compute; reflexivity).
  step. step. step. step. step.
  step.

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
  replace (ret_pc (Z_to_bv 64 469828)) with (Z_to_bv 64 469828 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - MMAPZ_STACK, bv_unsigned sp); (a, a + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.

  step. step. step.
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 a) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.
  step. step.
  step. step. step. step. if_lit. step.
  step. step. step. step. step. step. step.
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

Definition rmapd_entry := 0x7b28c.
Lemma rmapd_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMAPD_STACK ->
  mem_inv bsegs m ->
  a1 = Z_to_bv 64 addr -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 0 ->
  addr mod 4096 = 0 -> size mod 4096 = 0 -> 0 < size -> AIMG_HI <= addr -> addr + size < 2^63 ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->

  (forall a RNG' ms', a <> addr -> 0 < a -> a + size <= ATOP -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rmapd_post RNG sp addr size lo m RNG' m' ->
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
               rmapd_post RNG sp addr size lo m RNG' m' /\
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 addr) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bsegs))).
  2: { intros a RNG' ms' [(NE & P1 & P2)|[-> PO]]; [apply UNR; [exact NE | exact P1 | exact P2]|].
       destruct PO as (m' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & PO & ->).
       eapply KONT. exact PO. }

  iprefix.
  step. step. step. step.
  step. step. step.
  carve_frame 96%nat ST.
  step. step. step. step. step. step. step.
  step. step. step.
  step. step. step.
  step. step. if_lit.
  zstep. zstep. step. if_lit.
  zstep. zstep. zstep. zstep.
  setreg 8 (Z_to_bv 64 size) ltac:(rewrite land_align4096 by lia; f_equal; clear -SAL SPOS ASZ A0; Z.div_mod_to_equations; lia).
  step. if_lit.
  zstep.
  setreg 18 (Z_to_bv 64 addr) ltac:(rewrite land_align4096 by lia; f_equal; clear -AAL A0 ASZ SPOS; Z.div_mod_to_equations; lia).
  step. step. step. step. step.

  step.
  carve_frame 272%nat ST.
  step. step. step. step. step. step. step. step.
  step. step.
  step. if_lit.
  zstep.
  step. step. step. step. step. step. step. step. step.
  release_frame FR0 ST (bv_unsigned sp + -96).
  step. setreg 13 (Z_to_bv 64 50) ltac:(vm_compute; reflexivity).
  step. step. step. step. step.
  step.

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
  replace (ret_pc (Z_to_bv 64 470964)) with (Z_to_bv 64 470964 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  apply (munch_weaken _ [(bv_unsigned sp - RMAPD_STACK, bv_unsigned sp); (addr, addr + size)]%Z) in MU.
  2: { unfold sub_fp. cbn [outside]. clear. intros x Hx. tauto. }
  sys_mem_zeros.

  step. step. step.
  step. step. step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. step. step. step. step. step.
  step. step. step. if_cases K2; zify_cond K2. 2: { exfalso. clear -K2 AM3 SPOS A0. lia. }
  zstep. step.
  setreg 10 (Z_to_bv 64 0) ltac:(f_equal; destruct (Z.ltb_spec 18446744073709547520 addr) as [LT|GE]; [exfalso; clear -AM3 SPOS LT; lia| reflexivity]).
  step. if_lit.
  step. step.
  step. step. step. step. if_lit. step.
  step. step. step. step. step. step. step. step. step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -96) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  apply evtF_done. right. split; [reflexivity|].
  do 15 eexists. split. 2: reflexivity.
  unfold rmapd_post, rmap_post_g. destruct HF0 as [[FPLE _] [_ BW]].
  split; [exact FPLE|]. split; [exact AM3|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact ZNEW|]. split; [exact GR1|]. split; [exact GR2|]. split; [exact BW|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: apply ref_ro_addr_false; right; lia.
Qed.
End CANSEC2.
End F_ammapz.
End TwinB.
