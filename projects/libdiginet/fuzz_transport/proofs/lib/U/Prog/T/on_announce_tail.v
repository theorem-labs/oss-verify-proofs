(* Segments of the ubsan walk of on_announce (entry 0x17000, frame sp - 304; on_announce.v): the common epilogue
   at 0x17070. The frame below the saved registers is given as the pieces the walk carves: [sp - 304, sp - 296),
   [sp - 296, sp - 288) (the save slot of s1), [sp - 288, sp - 256) and [sp - 256, sp - 216) (the FOREIGN notice),
   [sp - 216, sp - 172) and [sp - 172, sp - 144) (the DESK notice), [sp - 144, sp - 104) (the announce a); the saved
   registers at [sp - 104, sp). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC
  diginet_session_wake_c on_announce_model on_announce_lib.
Import ListNotations.
Open Scope Z_scope.

(* the pieces of the frame below the saved registers, from sp - 304 up: sizes 8, 8, 32, 40, 44, 28, 40 *)
Definition oa_low (m : word -> option byte) (sp : word) (c0 cx cf1 cf2 cn1 cn2 ca : list cell) : Prop :=
  rw_cells rsegs m (bv_unsigned sp + -304) c0 /\ cells_size c0 = 8%nat /\
  rw_cells rsegs m (bv_unsigned sp + -296) cx /\ cells_size cx = 8%nat /\
  rw_cells rsegs m (bv_unsigned sp + -288) cf1 /\ cells_size cf1 = 32%nat /\
  rw_cells rsegs m (bv_unsigned sp + -256) cf2 /\ cells_size cf2 = 40%nat /\
  rw_cells rsegs m (bv_unsigned sp + -216) cn1 /\ cells_size cn1 = 44%nat /\
  rw_cells rsegs m (bv_unsigned sp + -172) cn2 /\ cells_size cn2 = 28%nat /\
  rw_cells rsegs m (bv_unsigned sp + -144) ca /\ cells_size ca = 40%nat.

(* 0x17070-0x170a8: ld ra, s0-s11 from the frame; addi sp, sp, 304; ret *)
Lemma oa_epi : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo : Z) (B' : list byte)
    (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (c0 cx cf1 cf2 cn1 cn2 ca : list cell),
  lo + 1056 <= bv_unsigned sp ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -304) ->
  oa_low m sp c0 cx cf1 cf2 cn1 cn2 ca ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m B' -> g_fail_next B' <= 1 ->
  evt rsegs (oa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17070) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B'
    x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m
    c0 cx cf1 cf2 cn1 cn2 ca LO MU WMO MI ST LOW FRs WM GF.
  destruct LOW as (F0 & S0 & Fx & Sx & Ff1 & Sf1 & Ff2 & Sf2 & Fn1 & Sn1 & Fn2 & Sn2 & Fa & Sa).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  do 15 step.
  (* the frame back to the stack, from sp - 304 up *)
  pose proof (stk_release rsegs m lo _ c0 ST F0 ltac:(lia)) as ST1. rewrite S0 in ST1.
  pose proof (stk_release rsegs m lo _ cx ST1 ltac:(replace (bv_unsigned sp + -304 + Z.of_nat 8) with (bv_unsigned sp + -296) by lia; exact Fx) ltac:(lia)) as ST2.
  rewrite Sx in ST2.
  pose proof (stk_release rsegs m lo _ cf1 ST2 ltac:(replace (bv_unsigned sp + -304 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -288) by lia; exact Ff1) ltac:(lia)) as ST3.
  rewrite Sf1 in ST3.
  pose proof (stk_release rsegs m lo _ cf2 ST3 ltac:(replace (bv_unsigned sp + -304 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 32) with (bv_unsigned sp + -256) by lia; exact Ff2) ltac:(lia)) as ST4.
  rewrite Sf2 in ST4.
  pose proof (stk_release rsegs m lo _ cn1 ST4 ltac:(replace (bv_unsigned sp + -304 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 32 + Z.of_nat 40) with (bv_unsigned sp + -216) by lia; exact Fn1) ltac:(lia)) as ST5.
  rewrite Sn1 in ST5.
  pose proof (stk_release rsegs m lo _ cn2 ST5 ltac:(replace (bv_unsigned sp + -304 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 32 + Z.of_nat 40 + Z.of_nat 44) with (bv_unsigned sp + -172) by lia; exact Fn2) ltac:(lia)) as ST6.
  rewrite Sn2 in ST6.
  pose proof (stk_release rsegs m lo _ ca ST6 ltac:(replace (bv_unsigned sp + -304 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 32 + Z.of_nat 40 + Z.of_nat 44 + Z.of_nat 28) with (bv_unsigned sp + -144) by lia; exact Fa) ltac:(lia)) as ST7.
  rewrite Sa in ST7.
  pose proof (stk_release rsegs m lo _ _ ST7 ltac:(replace (bv_unsigned sp + -304 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 32 + Z.of_nat 40 + Z.of_nat 44 + Z.of_nat 28 + Z.of_nat 40) with (bv_unsigned sp + -104) by lia; exact FRs) ltac:(lia)) as ST8.
  cbn [cells_size csize Nat.add] in ST8.
  replace (bv_unsigned sp + -304 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 32 + Z.of_nat 40 + Z.of_nat 44 + Z.of_nat 28 + Z.of_nat 40 + Z.of_nat 104) with (bv_unsigned sp) in ST8 by lia.
  apply evt_done. unfold oa_post. do 16 eexists. split; [reflexivity|].
  refine (conj MU (conj WMO (conj MI (conj ST8 (conj WM GF))))).
Qed.

(* the frame pieces and the saved registers, unpacked for the kit's transport tactics, and packed back *)
Ltac oa_low_unpack LOW :=
  destruct LOW as (F0 & S0 & Fx & Sx & Ff1 & Sf1 & Ff2 & Sf2 & Fn1 & Sn1 & Fn2 & Sn2 & Fa & Sa).
Ltac oa_low_pack :=
  unfold oa_low; repeat match goal with |- _ /\ _ => split end; first [eassumption | reflexivity].

(* 0x171e0-0x171f8: :204-205, if (s->state == IDLE && s->cfg.auto_wake) diginet_session_wake (s, now), then the
   epilogue; a0 holds s->state *)
Lemma oa_wake : diginet_session_wake_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (lo : Z) (B' : list byte) (TF : option tframe) (now : Z)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (m : word -> option byte) (Bc : list byte) (c0 cx cf1 cf2 cn1 cn2 ca : list cell),
  bv_unsigned sp mod 16 = 0 -> lo + 1056 <= bv_unsigned sp -> W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 1056 ->
  0 <= now < 2 ^ 64 -> tframe_at m0 sp 1056 TF -> relro_img m0 ->
  munch [(bv_unsigned sp - 1056, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m0 m ->
  wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -304) ->
  oa_low m sp c0 cx cf1 cf2 cn1 cn2 ca ->
  rw_cells rsegs m (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  wmem rsegs m Bc -> g_fail_next Bc <= 1 ->
  a0 = Z_to_bv 64 (S_state Bc) ->
  oa_wake_m timg_ubsan TF Bc now = Some (B', tt) ->
  evt rsegs (oa_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp t0 t1 t2
             (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 now) a0 a1 a2 a3 a4 a5 a6 a7
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 0x171e0) fc None m (seg_rom rsegs)).
Proof.
  intros WAKE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo B' TF now
    x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 m Bc
    c0 cx cf1 cf2 cn1 cn2 ca SP16 LO WOS Hnow TFA RR MU WMO MI ST LOW FRs WM GF -> HM.
  unfold diginet_session_wake_contract, diginet_session_wake_ENTRY, diginet_session_wake_FRAME in WAKE.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  wk_facts. assert (EOFF : OFF_g_s = 1648) by reflexivity.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -304)) = bv_unsigned sp + -304) by (apply unsigned_lit; lia).
  pose proof (s32_range Bc A_S_state) as RS. change (s32_at Bc A_S_state) with (S_state Bc) in RS.
  unfold oa_wake_m in HM.
  (* bnez a0: s->state *)
  step. rewrite oa_eqb0 by lia.
  change DIGINET_S_IDLE with 0 in HM.
  destruct (S_state Bc =? 0) eqn:E0; cbn [negb andb] in HM |- *.
  2:{ (* not IDLE: the epilogue *)
    injection HM as <-. eapply oa_epi; eassumption. }
  (* lw a0, 16(s0): s->cfg.auto_wake; beqz a0 *)
  step. step.
  pose proof (s32_range Bc A_S_cfg_auto_wake) as RA.
  change (s32_at Bc A_S_cfg_auto_wake) with (S_cfg_auto_wake Bc) in RA.
  change (s32_at Bc 1664) with (S_cfg_auto_wake Bc).
  rewrite oa_eqb0 by lia.
  destruct (S_cfg_auto_wake Bc =? 0) eqn:EA; cbn [negb] in HM |- *.
  { (* auto_wake = 0: the epilogue *)
    injection HM as <-. eapply oa_epi; eassumption. }
  destruct (diginet_session_wake_m timg_ubsan TF Bc now) as [[B5 r]|] eqn:HW; [|discriminate HM].
  injection HM as <-.
  (* mv a0, s0; mv a1, s1; jal diginet_session_wake *)
  do 3 step.
  oa_low_unpack LOW.
  eapply evt_cut.
  { eapply WAKE.
    - reflexivity.
    - reflexivity.
    - exact Hnow.
    - exact WM.
    - exact GF.
    - exact HW.
    - eapply tframe_at_move; [exact TFA | exact MU | rewrite Hsp; lia | rewrite Hsp; lia].
    - eapply relro_img_move; [exact RR | exact MU | exact WOS].
    - rewrite Hsp. Z.div_mod_to_equations. lia.
    - rewrite Hsp. exact ST.
    - rewrite Hsp. lia.
    - unfold w_off_stack. rewrite Hsp. lia.
    - exact MI. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & Eq & MUc & WMc & MI2 & ST2 & WM2 & GF2).
  subst ms'. rewrite Hsp in MUc, ST2. clear WM.
  lazymatch type of MUc with munch _ ?mm m2 => transport_after_call rsegs mm m2 MUc WMc end.
  clear MUc WMc MI.
  rewrite (ret_pc_even 0x171f8) by (first [lia | reflexivity]).
  (* j 0x17070 *)
  step.
  eapply oa_epi; try eassumption. oa_low_pack.
Qed.
