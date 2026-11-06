(* LLVMFuzzerTestOneInput (ubsan) 0x137f8 .. 0x13854: diginet_session_config_default(&g_cfg), memcpy(g_cfg.host_mac,
   HOST, 6), the three flag fields (desk_mac_set, auto_wake, sum_mode; the machine stores them in that order, the
   model in the other), memcpy(g_cfg.desk_mac, DESK, 6). The world becomes the model's B6 (ent_W6). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  diginet_session_config_default_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_entry_m LLVMFuzzerTestOneInput_entry_d.
Import ListNotations.
Open Scope Z_scope.

Lemma ent_cfg : forall data regs0 m0 Sp lo B B1 o n flags F fc ms (Q : machine_state -> Prop),
  memcpy_contract -> diginet_session_config_default_contract ->
  ent_num Sp lo -> 0 <= flags < 256 ->
  diginet_session_config_default_m B = Some (B1, tt) ->
  ent_s7f8 data regs0 m0 Sp lo B o n flags F fc ms ->
  (forall ms', ent_s854 data regs0 m0 Sp lo B1 o n flags F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data regs0 m0 Sp lo B B1 o n flags F fc ms Q MCPY CDEF HNUM HFL HCD HS K.
  unfold diginet_session_config_default_contract, diginet_session_config_default_ENTRY,
    diginet_session_config_default_FRAME in CDEF.
  destruct HS as (ra & t0 & t1 & t2 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & s5 & s6 & s8 & s9 &
                  s10 & s11 & t3 & t4 & t5 & t6 & m & -> & HM).
  destruct HM as (j0 & j60 & ST & MI & WM & MU0 & WMO0 & FR).
  unfold ent_frame, llvm_saved in FR. cbn [app] in FR.
  destruct HNUM as (H16 & Hlo & HK & H63 & HWL). unfold LH_K, LH_FRAME in *.
  assert (USp : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_cfg.
  (* 0x137f8 auipc a0; 0x137fc addi s9 = &g_fail_next; 0x13800 addi s1 = &g_cfg; 0x13804 mv a0, s1 *)
  do 4 step.
  (* 0x13808 jal diginet_session_config_default *)
  step.
  eapply evt_cut.
  { eapply (CDEF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo B B1);
      [ reflexivity | exact WM | exact HCD | rewrite USp; exact H16 | rewrite USp; exact ST | rewrite USp; lia
      | unfold w_off_stack; rewrite USp; lia | exact MI ]. }
  wk_post_call rsegs m.
  lazymatch goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 Sp)) |- _ => rewrite USp in H end.
  lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI end.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ B1] |- _ => pose proof (wm_len _ _ _ _ H) as LB1 end.
  assert (U1 : bv_unsigned (Z_to_bv 64 0x43100) = 0x43100) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 0x10470) = 0x10470) by (apply unsigned_lit; lia).
  assert (U3 : bv_unsigned (Z_to_bv 64 6) = 6) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 0x43106) = 0x43106) by (apply unsigned_lit; lia).
  assert (U5 : bv_unsigned (Z_to_bv 64 0x10476) = 0x10476) by (apply unsigned_lit; lia).
  (* 0x1380c auipc; 0x13810 addi a1 = HOST (0x10470); li a2, 6; mv a0, s1; jal memcpy *)
  do 5 step.
  (* the memcpy into g_cfg.host_mac *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (HH : bytes_at rsegs m1 0x10470 HOST)
      by (apply ro_bytes_at; [exact MI | lia | vm_compute; discriminate |];
          apply ro_bytes_b_sound; vm_compute; reflexivity);
    lazymatch goal with H : rw_cells rsegs m1 W_BASE_UBSAN [CB _ ?W] |- _ =>
      pose proof (wm_piece rsegs W_BASE_UBSAN m1 W 65024 6 (W_BASE_UBSAN + 65024) H ltac:(reflexivity) ltac:(lia)
                    ltac:(lia) ltac:(lia)) as DST;
      eapply evt_cut;
      [ eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 HOST
                  (sub W 65024 (Z.to_nat 6)));
        [ exact HH | reflexivity | exact DST | left; rewrite !unsigned_lit by lia; lia | exact MI ] | ];
      let ms' := fresh "ms'" in let POST := fresh "POST" in
      intros ms' POST; unfold memcpy_post in POST;
      destruct POST as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & EQs & MUc & WOc & MI2 & DST2 & SRC2);
      subst ms';
      wk_world_after_call rsegs m1 m2;
      transport_after_call rsegs m1 m2 MUc WOc;
      clear MUc WOc MI; rename MI2 into MI; try clear m1
    end
  end.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  (* 0x13820 .. 0x13830: the flag bits; 0x13834 .. 0x1383c: the three stores *)
  do 8 zstep.
  rewrite (e_bit2 flags HFL), (e_bit1 flags HFL) in *.
  (* 0x13840 addi a0 = &g_cfg.desk_mac; auipc a1; addi a1 = DESK (0x10476); li a2, 6; jal memcpy *)
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (HDK : bytes_at rsegs m1 0x10476 DESK)
      by (apply ro_bytes_at; [exact MI | lia | vm_compute; discriminate |];
          apply ro_bytes_b_sound; vm_compute; reflexivity);
    lazymatch goal with H : rw_cells rsegs m1 W_BASE_UBSAN [CB _ ?W] |- _ =>
      pose proof (wm_piece rsegs W_BASE_UBSAN m1 W 65030 6 (W_BASE_UBSAN + 65030) H ltac:(reflexivity) ltac:(lia)
                    ltac:(lia) ltac:(lia)) as DST;
      eapply evt_cut;
      [ eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 DESK
                  (sub W 65030 (Z.to_nat 6)));
        [ exact HDK | reflexivity | exact DST | left; rewrite !unsigned_lit by lia; lia | exact MI ] | ];
      let ms' := fresh "ms'" in let POST := fresh "POST" in
      intros ms' POST; unfold memcpy_post in POST;
      destruct POST as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & EQs & MUc & WOc & MI2 & DST2 & SRC2);
      subst ms';
      wk_world_after_call rsegs m1 m2;
      transport_after_call rsegs m1 m2 MUc WOc;
      clear MUc WOc MI; rename MI2 into MI; try clear m1
    end
  end.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ _] |- _ =>
    rewrite (ent_W6_eq B1 flags) in H by exact LB1; rename H into WM end.
  apply K. unfold ent_s854.
  do 22 eexists. eexists. split; [reflexivity|].
  unfold ent_mem, ent_frame. do 2 eexists.
  split; [lazymatch goal with H : stk rsegs _ _ _ |- _ => exact H end|].
  split; [exact MI|]. split; [exact WM|]. split; [exact MU0|]. split; [exact WMO0|].
  exact FR.
Qed.
