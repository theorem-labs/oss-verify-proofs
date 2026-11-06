From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import check_ack_settle_c check_state_settle_c
  check_inflight_settle_c check_keepalive_settle_c check_latest_queue_c check_latest_drain_c settle_c.
Import ListNotations.
Open Scope Z_scope.

Lemma settle_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

(* A call from settle's frame: the callee contract SPEC applied with its premises, in their order (world, model,
   sp alignment, stack, stack room, window above the world, mem_inv), each from the named caller fact; Hsp reads the
   callee's sp back. *)
Ltac settle_call SPEC WMh Hm STh MIh Hsp :=
  eapply SPEC;
    [ exact WMh | exact Hm | rewrite Hsp; Z.div_mod_to_equations; lia | rewrite Hsp; exact STh
    | rewrite Hsp; lia | unfold w_off_stack; rewrite Hsp; lia | exact MIh ].

Theorem settle_holds :
  check_ack_settle_contract -> check_state_settle_contract -> check_inflight_settle_contract ->
  check_keepalive_settle_contract -> check_latest_queue_contract -> check_latest_drain_contract ->
  settle_contract.
Proof.
  intros CAS CSS CIS CKS CLQ CLD.
  unfold check_ack_settle_contract, check_ack_settle_ENTRY, check_ack_settle_FRAME in CAS.
  unfold check_state_settle_contract, check_state_settle_ENTRY, check_state_settle_FRAME in CSS.
  unfold check_inflight_settle_contract, check_inflight_settle_ENTRY, check_inflight_settle_FRAME in CIS.
  unfold check_keepalive_settle_contract, check_keepalive_settle_ENTRY, check_keepalive_settle_FRAME in CKS.
  unfold check_latest_queue_contract, check_latest_queue_ENTRY, check_latest_queue_FRAME in CLQ.
  unfold check_latest_drain_contract, check_latest_drain_ENTRY, check_latest_drain_FRAME in CLD.
  unfold settle_contract, settle_ENTRY, settle_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo B B' ticked A0 TR WM HM SP16 ST LO WO MI.
  subst a0.
  unfold w_off_stack in WO.
  wk_facts.
  (* the model: the four checks return their world *)
  unfold settle_m in HM.
  destruct (check_ack_settle_m B) as [[B1 []]|] eqn:H1; rewrite ?H1 in HM; cbv beta iota in HM; [|discriminate HM].
  destruct (check_state_settle_m B1) as [[B2 []]|] eqn:H2; rewrite ?H2 in HM; cbv beta iota in HM; [|discriminate HM].
  destruct (check_inflight_settle_m B2) as [[B3 []]|] eqn:H3; rewrite ?H3 in HM; cbv beta iota in HM;
    [|discriminate HM].
  destruct (check_keepalive_settle_m B3) as [[B4 []]|] eqn:H4; rewrite ?H4 in HM; cbv beta iota in HM;
    [|discriminate HM].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  (* prologue: addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp); mv s0,a0 *)
  do 4 step.
  rename m into mI. rename MU into MU0. rename WMO into WM0.
  lazymatch goal with HF : rw_cells _ ?mm (bv_unsigned sp + -16) _ |- _ => rename mm into m1; rename HF into FR end.
  (* jal check_ack_settle *)
  step.
  eapply evt_cut.
  { settle_call CAS WM H1 ST MI Hsp. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 &
              Eq & MUc & WMc & MI2 & ST2 & EB & WM2).
  subst ms'. rewrite Hsp in MUc, ST2. subst B1. clear WM.
  transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI. try clear m1.
  rewrite (ret_pc_even 0x14f24) by (first [lia | reflexivity]).
  (* jal check_state_settle *)
  step.
  eapply evt_cut.
  { settle_call CSS WM2 H2 ST2 MI2 Hsp. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 &
              Eq & MUc & WMc & MI3 & ST3 & EB & WM3).
  subst ms'. rewrite Hsp in MUc, ST3. subst B2. clear WM2.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI2. try clear m2.
  rewrite (ret_pc_even 0x14f28) by (first [lia | reflexivity]).
  (* jal check_inflight_settle *)
  step.
  eapply evt_cut.
  { settle_call CIS WM3 H3 ST3 MI3 Hsp. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 &
              Eq & MUc & WMc & MI4 & ST4 & EB & WM4).
  subst ms'. rewrite Hsp in MUc, ST4. subst B3. clear WM3.
  transport_after_call rsegs m3 m4 MUc WMc. clear MUc WMc MI3. try clear m3.
  rewrite (ret_pc_even 0x14f2c) by (first [lia | reflexivity]).
  (* jal check_keepalive_settle *)
  step.
  eapply evt_cut.
  { settle_call CKS WM4 H4 ST4 MI4 Hsp. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 &
              Eq & MUc & WMc & MI5 & ST5 & EB & WM5).
  subst ms'. rewrite Hsp in MUc, ST5. subst B4. clear WM4.
  transport_after_call rsegs m4 m5 MUc WMc. clear MUc WMc MI4. try clear m4.
  rewrite (ret_pc_even 0x14f30) by (first [lia | reflexivity]).
  (* auipc a0; lw a0, g_raw *)
  step. step.
  change (s32_at B 64972) with (g_raw B).
  pose proof (s32_range B OFF_g_raw) as GR. change (s32_at B OFF_g_raw) with (g_raw B) in GR.
  (* beqz a0 *)
  step.
  rewrite settle_eqb0 by lia.
  (* the common epilogue: ld ra,8(sp); ld s0,0(sp); addi sp,sp,16 *)
  destruct (Z.eqb_spec (g_raw B) 0) as [G0|G0]; cbv iota.
  - (* g_raw = 0: jal check_latest_queue *)
    assert (T0 : truth (g_raw B) = false) by (unfold truth; rewrite G0; reflexivity).
    rewrite T0 in HM. cbv beta iota delta [negb] in HM.
    destruct (check_latest_queue_m B) as [[B5 []]|] eqn:H5; rewrite ?H5 in HM; cbv beta iota in HM;
      [|discriminate HM].
    step.
    eapply evt_cut.
    { settle_call CLQ WM5 H5 ST5 MI5 Hsp. }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 &
                Eq & MUc & WMc & MI6 & ST6 & EB & WM6).
    subst ms'. rewrite Hsp in MUc, ST6. subst B5. clear WM5.
    transport_after_call rsegs m5 m6 MUc WMc. clear MUc WMc MI5. try clear m5.
    rewrite (ret_pc_even 0x14f50) by (first [lia | reflexivity]).
    (* beqz s0 *)
    step.
    rewrite settle_eqb0 by lia.
    destruct (Z.eqb_spec ticked 0) as [K0|K0]; cbv iota.
    + (* ticked = 0: return *)
      assert (TK : truth ticked = false) by (unfold truth; rewrite K0; reflexivity).
      rewrite TK in HM. cbv beta iota in HM.
      do 2 step.
      release_frame FR ST6 (bv_unsigned sp).
      do 2 step.
      apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
      split; [exact MU0|]. split; [exact WM0|]. split; [exact MI6|]. split; [exact ST6|].
      split; [congruence | exact WM6].
    + (* ticked <> 0: ld ra; ld s0; addi sp; j check_latest_drain *)
      assert (TK : truth ticked = true) by (unfold truth; apply negb_true_iff, Z.eqb_neq; exact K0).
      rewrite TK in HM. cbv beta iota in HM.
      do 2 step.
      release_frame FR ST6 (bv_unsigned sp).
      do 2 step.
      eapply evt_cut.
      { eapply CLD; [ exact WM6 | exact HM | exact SP16 | exact ST6 | lia | unfold w_off_stack; lia | exact MI6 ]. }
      intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 &
                  Eq & MUc & WMc & MI7 & ST7 & EB & WM7).
      subst ms'. clear WM6.
      transport_after_call rsegs m6 m7 MUc WMc. clear MUc WMc MI6. try clear m6.
      apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
      split; [exact MU0|]. split; [exact WM0|]. split; [exact MI7|]. split; [exact ST7|].
      split; [exact EB | exact WM7].
  - (* g_raw <> 0: return *)
    assert (T1 : truth (g_raw B) = true) by (unfold truth; apply negb_true_iff, Z.eqb_neq; exact G0).
    rewrite T1 in HM. cbv beta iota delta [negb] in HM.
    do 2 step.
    release_frame FR ST5 (bv_unsigned sp).
    do 2 step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU0|]. split; [exact WM0|]. split; [exact MI5|]. split; [exact ST5|].
    split; [congruence | exact WM5].
Qed.
