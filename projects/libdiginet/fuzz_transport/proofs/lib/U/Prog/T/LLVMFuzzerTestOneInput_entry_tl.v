(* LLVMFuzzerTestOneInput (ubsan) 0x138d4 .. 0x13988: max_body (fuzz_transport.c:1148), the scalars and M
   (:1150-1158; memset(&M + 8, 0, 0x668), M.desk_known, memcpy(M.desk, DESK, 6)), and
   diginet_session_init(&g_s, &g_cfg, sp + 0x40, notice, 0) (:1165) on the model's B24 (ent_Wt). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TWorldMem TSess0 TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  diginet_session_init_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_entry_m LLVMFuzzerTestOneInput_entry_d.
Import ListNotations.
Open Scope Z_scope.

Lemma ent_tl1 : forall data D regs0 m0 Sp lo B1 o n flags F fc ms B25 rc (Q : machine_state -> Prop),
  memcpy_contract -> memset_contract -> diginet_session_init_contract ->
  ent_num Sp lo -> 0 <= flags < 256 -> 0 <= o -> 0 <= n -> o + n = Z.of_nat (length D) ->
  length B1 = Z.to_nat W_LEN ->
  diginet_session_init_m (ent_Wt flags (ent_v9 (cbyte D o n)) (ent_W14 (cbyte D o n) (ent_W6 flags B1)))
    0 (ti_io_send timg_ubsan) (ti_io_recv timg_ubsan) (ti_io_now timg_ubsan) (ti_notice timg_ubsan) 0 =
    Some (B25, rc) ->
  ent_s8d4 data D regs0 m0 Sp lo B1 o n flags F fc ms ->
  (forall ms', ent_s988 data regs0 m0 Sp lo o n rc B25 F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo B1 o n flags F fc ms B25 rc Q MCPY MSET INIT HNUM HFL Ho Hn Hon LB1 HI HS K.
  unfold diginet_session_init_contract, diginet_session_init_ENTRY, diginet_session_init_FRAME in INIT.
  destruct HS as (ra & t0 & t1 & t2 & s0 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s8 & s10 & s11 &
                  t3 & t4 & t5 & t6 & m & -> & HM).
  destruct HM as (j0 & j60 & ST & MI & WM & MU0 & WMO0 & FR).
  unfold ent_frame, llvm_saved in FR. cbn [app] in FR.
  destruct HNUM as (H16 & Hlo & HK & H63 & HWL). unfold LH_K, LH_FRAME in *.
  assert (USp : bv_unsigned (Z_to_bv 64 Sp) = Sp) by (apply unsigned_lit; lia).
  pose proof (wm_len _ _ _ _ WM) as LB.
  wk_facts. wk_eq_fact OFF_g_fail_next. wk_eq_fact OFF_g_cfg. wk_eq_fact OFF_M.
  assert (C12 : 0 <= cbyte D o n 12 < 256).
  { unfold cbyte. destruct (12 <? n); [unfold at8, bz; apply e_brange | lia]. }
  assert (C13 : 0 <= cbyte D o n 13 < 256).
  { unfold cbyte. destruct (13 <? n); [unfold at8, bz; apply e_brange | lia]. }
  (* 0x138d4 .. 0x13910: max_body = 24 + v9 % 1461 *)
  do 16 zstep.
  (* 0x13914 sw max_body; 0x13918 sb g_fail_next; 0x1391c sw g_raw; 0x13920 sw g_last_counter; 0x13924 sd g_now *)
  do 5 zstep.
  (* 0x13928 auipc; 0x1392c addi s8 = &M; 0x13930 addi a0 = &M + 8; li a2, 0x668; mv a1, zero; jal memset *)
  do 6 zstep.
  assert (U0 : bv_unsigned (Z_to_bv 64 209672) = 209672) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 1640) = 1640) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    lazymatch goal with H : rw_cells rsegs m1 W_BASE_UBSAN [CB _ ?W] |- _ =>
      pose proof (wm_piece rsegs W_BASE_UBSAN m1 W 8 1640 (W_BASE_UBSAN + 8) H ltac:(reflexivity) ltac:(lia)
                    ltac:(lia) ltac:(lia)) as DST;
      eapply evt_cut;
      [ eapply (MSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (sub W 8 (Z.to_nat 1640)));
        [ exact DST | exact MI ] | ];
      let ms' := fresh "ms'" in let POST := fresh "POST" in
      intros ms' POST; unfold memset_post in POST;
      destruct POST as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & EQs & MUc & WOc & MI2 & DST2);
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
    change (repeat (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) (Z.to_nat (bv_unsigned (Z_to_bv 64 1640))))
      with (repeat (b8 0) 1640) in H end.
  (* 0x13940 sw s3, 0(s8): M.desk_known *)
  zstep.
  (* 0x13944 addi a0 = &M + 4; auipc a1; addi a1 = DESK (0x10476); li a2, 6; jal memcpy *)
  do 5 zstep.
  assert (U3 : bv_unsigned (Z_to_bv 64 209668) = 209668) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 0x10476) = 0x10476) by (apply unsigned_lit; lia).
  assert (U5 : bv_unsigned (Z_to_bv 64 6) = 6) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (HDK : bytes_at rsegs m1 0x10476 DESK)
      by (apply ro_bytes_at; [exact MI | lia | vm_compute; discriminate |];
          apply ro_bytes_b_sound; vm_compute; reflexivity);
    lazymatch goal with H : rw_cells rsegs m1 W_BASE_UBSAN [CB _ ?W] |- _ =>
      pose proof (wm_piece rsegs W_BASE_UBSAN m1 W 4 6 (W_BASE_UBSAN + 4) H ltac:(reflexivity) ltac:(lia)
                    ltac:(lia) ltac:(lia)) as DST;
      eapply evt_cut;
      [ eapply (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 DESK
                  (sub W 4 (Z.to_nat 6)));
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
  (* 0x13958 sw g_nq; 0x1395c sw g_ncmd; 0x13960 sd g_rx *)
  do 3 zstep.
  (* the world is the model's B24 *)
  lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ _] |- _ =>
    erewrite (ent_Wt_eq _ flags (ent_v9 (cbyte D o n))) in H;
    [ rename H into WM
    | exact LB
    | exact (ent_W14_dms _ _ _ LB1)
    | rewrite (e_lor2 (cbyte D o n 12) (cbyte D o n 13) C12 C13); rewrite e_mb by lia;
      unfold ent_v9; rewrite e_lor16 by lia; unfold SPEC_CMD_MAX, SPEC_MAX_BODY;
      change (1484 - 24 + 1) with 1461; rewrite Z.mod_mod by lia; reflexivity
    | exact (e_raw flags HFL) ]
  end.
  (* 0x13964 .. 0x13980: s10 = &g_s, a3 = notice, a2 = sp + 0x40, a0 = s10, a1 = s1, a4 = 0; 0x13984 jal *)
  do 9 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m3 _) =>
    eapply evt_cut;
    [ eapply (INIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 lo (Sp + 64) 0 0x1482c
                0x14b20 0x14bbc 0x14bc8 0 rc _ B25);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | lia | lia | lia | lia | lia | lia
      | exact (ent_io_bytes _ _ _ _ _ FR)
      | unfold arg_blk, off_world, off_window; rewrite USp; lia
      | Z.div_mod_to_equations; lia
      | exact WM
      | exact HI
      | rewrite USp; exact H16
      | rewrite USp; exact ST
      | rewrite USp; lia
      | unfold w_off_stack; rewrite USp; lia
      | exact MI ]
    | wk_post_call rsegs m3 ]
  end.
  lazymatch goal with H : stk rsegs _ lo (bv_unsigned (Z_to_bv 64 Sp)) |- _ => rewrite USp in H end.
  apply K. unfold ent_s988.
  do 21 eexists. eexists. split; [reflexivity|].
  unfold ent_mem, ent_frame. do 2 eexists.
  split; [lazymatch goal with H : stk rsegs _ _ _ |- _ => exact H end|].
  split; [lazymatch goal with H : mem_inv rsegs _ |- _ => exact H end|].
  split; [lazymatch goal with H : rw_cells rsegs _ W_BASE_UBSAN [CB _ B25] |- _ => exact H end|].
  split; [exact MU0|]. split; [exact WMO0|].
  exact FR.
Qed.
