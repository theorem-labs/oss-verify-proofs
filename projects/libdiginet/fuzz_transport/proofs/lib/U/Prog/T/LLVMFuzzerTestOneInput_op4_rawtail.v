(* Case 4 of the ubsan LLVMFuzzerTestOneInput, the raw arm 0x144d0 .. the latch 0x14574: the UBSan pointer check of
   the take, c.len, memcpy(c.bytes, p, c.len) (:1080), diginet_session_submit (:1081), check_refusal_submit (:1082)
   and settle(0) (:1083). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract TSessC
  diginet_session_submit_c check_refusal_submit_c settle_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs LLVMFuzzerTestOneInput_op4_raw.
Import ListNotations.
Open Scope Z_scope.

Ltac hyp_mi := match goal with H : mem_inv rsegs _ |- _ => exact H end.

Lemma op4_cs_len : forall bytes len display key, length bytes = 24%nat ->
  length (cmd_struct bytes len display key) = 32%nat.
Proof.
  intros bytes len display key H. unfold cmd_struct.
  rewrite !app_length, length_put, H. cbn [length]. lia.
Qed.

Lemma op4_cs_app : forall bytes len display key,
  cmd_struct bytes len display key = bytes ++ ([b8 len; b8 display; b8 0; b8 0] ++ put 4 key).
Proof. intros. unfold cmd_struct. rewrite app_assoc. reflexivity. Qed.

(* the 32 bytes of the struct out of the frame's 40-byte cell *)
Lemma op4_cs_bytes : forall mm A cs jhi, length cs = 32%nat ->
  rw_cells rsegs mm A [CB 40 (cs ++ jhi)] -> bytes_at rsegs mm A cs.
Proof.
  intros mm A cs jhi L [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  exact (proj1 (proj1 (bytes_at_app rsegs mm A cs jhi) HB)).
Qed.

Theorem op4_raw_tail : forall data D regs0 m0 Sp lo ops c4 nn before B1 display key B2 B3 B4 rc F fc ms,
  memcpy_contract -> diginet_session_submit_contract -> check_refusal_submit_contract -> settle_contract ->
  op4_rt data D regs0 m0 Sp lo ops c4 nn before B1 display key F fc ms ->
  diginet_session_submit_m B1
    (cmd_struct (sub D (fi_off c4) (Z.to_nat nn) ++ repeat (b8 0) (Z.to_nat (24 - nn))) nn display key)
    = Some (B2, rc) ->
  check_refusal_submit_m B2
    (cmd_struct (sub D (fi_off c4) (Z.to_nat nn) ++ repeat (b8 0) (Z.to_nat (24 - nn))) nn display key)
    rc before = Some (B3, tt) ->
  settle_m B3 0 = Some (B4, tt) ->
  evt rsegs (llvm_latch data D regs0 m0 Sp lo ops (FuzzIn (fi_off c4 + nn) (fi_n c4 - nn)) B4 F fc) ms.
Proof.
  intros data D regs0 m0 Sp lo ops c4 nn before B1 display key B2 B3 B4 rc F fc ms
    MCP SUB CRS STL H HS1 HS2 HS3.
  destruct H as (ra & t0 & t1 & t2 & a1 & a3 & a4 & a5 & a6 & a7 & s5 & s6 & s7 & t3 & t4 & t5 & t6 & m &
                 j10 & jio & jhi & -> & HOPS & HC & HNN & HNC & RQ & HDSP & HKEY & LJ & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold llvm_cursor in HC. unfold LH_K, LH_FRAME in *.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  assert (LBz : length B1 = Z.to_nat W_LEN) by exact LB.
  wk_facts.
  pose proof (submit_rc B1 _ _ _ HS1) as HRC.
  set (cb0 := sub D (fi_off c4) (Z.to_nat nn) ++ repeat (b8 0) (Z.to_nat (24 - nn))) in *.
  assert (LSUB : length (sub D (fi_off c4) (Z.to_nat nn)) = Z.to_nat nn) by (apply length_sub; lia).
  assert (LCB0 : length cb0 = 24%nat) by (unfold cb0; rewrite app_length, LSUB, repeat_length; lia).
  assert (LCS : length (cmd_struct cb0 nn display key) = 32%nat) by (apply op4_cs_len; exact LCB0).
  assert (LJS : length (cmd_struct (repeat (b8 0) 24) nn display key ++ jhi) = 40%nat)
    by (rewrite app_length, (op4_cs_len (repeat (b8 0) 24) nn display key ltac:(apply repeat_length)), LJ; lia).
  assert (LJS2 : length (cmd_struct cb0 nn display key ++ jhi) = 40%nat)
    by (rewrite app_length, LCS, LJ; lia).
  assert (HFN2 : g_fail_next B2 <= 1)
    by (rewrite (submit_gfn B1 _ B2 rc LB LCS HS1);
        exact HFN).
  (* the frame *)
  destruct (llvm_frame_split regs0 m Sp j10 jio (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi) HRW)
    as (F1 & F2 & F3 & F4 & F5 & F6).
  clear HRW.
  unfold llvm_saved in F6.
  pose proof (munch_refl [(Sp, Sp + 240)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* ---- 0x144d0 not a1, s3; 0x144d4 bltu a1, a2 (the pointer overflow, not taken) ---- *)
  zstep.
  rewrite ?(unsigned_lit (data + fi_off c4)) by lia.
  rewrite ?(Z.mod_small (data + fi_off c4) 18446744073709551616) by lia.
  rewrite zb_lxor_ones by lia.
  zstep. brv false.
  (* ---- 0x144d8 mv s5, s0; 0x144dc add s0, s3, a2; 0x144e0 sub s6, a0, a2; 0x144e4 sb a2, 0x78(sp) ---- *)
  do 4 zstep.
  apply rw_cells_merge_all in F5. cbn [cells_size csize Nat.add] in F5.
  lazymatch type of F5 with
  | rw_cells _ _ _ [CB 40 ?X] =>
      let E := fresh "E" in
      assert (E : X = cmd_struct (repeat (b8 0) 24) nn display key ++ jhi)
        by (cbn [cells_bytes cbytes firstn skipn app repeat];
            rewrite ?op4_sb, ?app_nil_r; unfold cmd_struct; cbn [app repeat];
            rewrite <- ?app_assoc; reflexivity);
      rewrite E in F5; clear E
  end.
  (* split the struct for the memcpy *)
  pose proof (rw_cells_split_CB rsegs _ (Sp + 96) [] 40 _ [] [Z.to_nat nn; (40 - Z.to_nat nn)%nat] F5
                ltac:(cbn [sum_nat]; lia)) as FS.
  cbn [app mk_CB_cells] in FS.
  apply (proj1 (rw_cells_app _ _ [CB _ _] [CB _ _])) in FS. destruct FS as [FD FR].
  cbn [cells_size csize Nat.add] in FR.
  clear F5.
  (* the callee's footprint as lia reads it (transport_after_call sees bv_unsigned of the registers) *)
  assert (Hu0 : bv_unsigned (Z_to_bv 64 (Sp + 96)) = Sp + 96) by (apply unsigned_lit; lia).
  assert (Hu1 : bv_unsigned (Z_to_bv 64 (data + fi_off c4)) = data + fi_off c4) by (apply unsigned_lit; lia).
  assert (Hu2 : bv_unsigned (Z_to_bv 64 nn) = nn) by (apply unsigned_lit; lia).
  (* ---- 0x144e8 addi a0, sp, 0x60; 0x144ec mv a1, s3; 0x144f0 jal memcpy ---- *)
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut;
    [ eapply (MCP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc
                (sub D (fi_off c4) (Z.to_nat nn))
                (firstn (Z.to_nat nn) (cmd_struct (repeat (b8 0) 24) nn display key ++ jhi)));
      [ rewrite !unsigned_lit by lia; apply op4_sub_at; [exact HD | lia | lia]
      | rewrite !unsigned_lit by lia; exact LSUB
      | rewrite !unsigned_lit by lia; exact FD
      | rewrite !unsigned_lit by lia; left; lia
      | hyp_mi ]
    | wk_post_call rsegs mc ]
  end.
  try (rewrite (ret_pc_even 0x144f4) by (first [lia | reflexivity])).
  rewrite ?Hu0, ?Hu1, ?Hu2 in *.
  (* rejoin the struct: the copied bytes and the zero tail *)
  lazymatch goal with
  | HCP : rw_cells rsegs ?mm (Sp + 96) [CB (Z.to_nat nn) (sub D (fi_off c4) (Z.to_nat nn))] |- _ =>
      assert (FJ : rw_cells rsegs mm (Sp + 96)
                     ([CB (Z.to_nat nn) (sub D (fi_off c4) (Z.to_nat nn))] ++
                      [CB (40 - Z.to_nat nn)%nat
                         (firstn (40 - Z.to_nat nn)%nat
                            (skipn (Z.to_nat nn) (cmd_struct (repeat (b8 0) 24) nn display key ++ jhi)))]))
        by (apply (proj2 (rw_cells_app _ _ _ _)); split;
            [exact HCP | cbn [cells_size csize Nat.add]; exact FR])
  end.
  apply rw_cells_merge_all in FJ. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FJ.
  lazymatch type of FJ with rw_cells _ _ _ [CB ?n _] => replace n with 40%nat in FJ by lia end.
  lazymatch type of FJ with
  | rw_cells _ _ _ [CB 40 ?X] =>
      let E := fresh "E" in
      assert (E : X = cmd_struct cb0 nn display key ++ jhi)
        by (rewrite app_nil_r, (op4_cs_app (repeat (b8 0) 24)), (op4_cs_app cb0), <- !app_assoc,
              skipn_repeat_app by lia;
            rewrite firstn_all2
              by (rewrite !app_length, repeat_length, length_put, LJ; cbn [length]; lia);
            unfold cb0; rewrite <- !app_assoc;
            replace (Z.to_nat (24 - nn)) with (24 - Z.to_nat nn)%nat by lia;
            reflexivity);
      rewrite E in FJ; clear E
  end.
  (* the frame, whole again *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (llvm_frame_join regs0 mm Sp j10 jio _ F1 F2 F3 F4 FJ F6) as HRW1;
    pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo B1 m mm j10 jio
                  (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi) j10 jio _ HM0 MU WMO
                  ltac:(hyp_mi) HRW1 HJ1 HJ2 LJS2) as HM1
  end.
  clear F1 F2 F3 F4 F6 FR HM0 HRW1.
  try clear MU. try clear WMO. try clear HD. try clear HSTK. try clear HWM. try clear HMU. try clear HWMO.
  repeat match goal with H : mem_inv rsegs _ |- _ => clear H end.
  (* ---- 0x144f4-0x14500: diginet_session_submit(&g_s, &c) ---- *)
  do 4 zstep.
  pose proof (op4_cs_bytes _ _ _ _ LCS FJ) as HB1.
  pose proof HM1 as HM1c. unfold llvm_mem in HM1c.
  destruct HM1c as (_ & _ & _ & _ & _ & HSTK1 & _ & _ & _ & HMI1 & _ & HWM1 & HFN1 & _ & _ & _ & _ & _ & _).
  eapply evt_cut.
  { eapply (SUB _ (Z_to_bv 64 Sp) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
              (Sp + 96) rc (cmd_struct cb0 nn display key) B1 B2).
    - reflexivity.
    - reflexivity.
    - exact HB1.
    - exact LCS.
    - unfold arg_blk, off_world, off_window; rewrite unsigned_lit by lia;
      split; [lia|]; split; [lia|]; split; [right; lia | right; lia].
    - lia.
    - exact HWM1.
    - exact HS1.
    - rewrite unsigned_lit by lia; exact HSP.
    - rewrite unsigned_lit by lia; exact HSTK1.
    - rewrite unsigned_lit by lia; unfold diginet_session_submit_FRAME; lia.
    - unfold w_off_stack; rewrite unsigned_lit by lia; unfold diginet_session_submit_FRAME; lia.
    - exact HMI1. }
  intros ms' Hpost.
  destruct Hpost as (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & p9 & p10 & p11 & p12 & p13 & m2 &
                     -> & MU2 & WMO2 & MI2 & ST2 & WM2).
  rewrite unsigned_lit in MU2, ST2 by lia.
  assert (HM2 : llvm_mem data D regs0 m0 Sp lo B2 m2 j10 jio (cmd_struct cb0 nn display key ++ jhi)).
  { eapply (llvm_mem_after_call data D regs0 m0 Sp lo diginet_session_submit_FRAME B1 B2 _ m2);
      [ exact HM1 | unfold diginet_session_submit_FRAME, LH_K; lia | exact MU2 | exact WMO2
      | exact MI2 | exact ST2 | exact WM2 | exact HFN2 ]. }
  clear HM1 FJ HB1 HSTK1 HMI1 HWM1 HFN1 MU2 WMO2 MI2 ST2 WM2.
  rewrite (ret_pc_even 0x14504) by (first [lia | reflexivity]).
  (* ---- 0x14504 mv a1, a0; 0x14508 addi a0, sp, 0x60; 0x1450c mv a2, s5; 0x14510 jal check_refusal_submit ---- *)
  do 4 zstep.
  pose proof HM2 as HM2c. unfold llvm_mem in HM2c.
  destruct HM2c as (_ & _ & _ & _ & _ & HSTK2 & _ & _ & _ & HMI2 & _ & HWM2 & _ & _ & _ & _ & _ & _ & HRW2).
  destruct (llvm_frame_split regs0 m2 Sp j10 jio (cmd_struct cb0 nn display key ++ jhi) HRW2)
    as (G1 & G2 & G3 & G4 & G5 & G6).
  pose proof (op4_cs_bytes _ _ _ _ LCS G5) as HB2.
  eapply evt_cut.
  { eapply (CRS _ (Z_to_bv 64 Sp) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
              B2 B3 (Sp + 96) (cmd_struct cb0 nn display key) rc before).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact RQ.
    - lia.
    - lia.
    - exact HB2.
    - exact LCS.
    - unfold off_window; rewrite unsigned_lit by lia; unfold check_refusal_submit_FRAME; right; lia.
    - exact HWM2.
    - exact HS2.
    - rewrite unsigned_lit by lia; exact HSP.
    - rewrite unsigned_lit by lia; exact HSTK2.
    - rewrite unsigned_lit by lia; unfold check_refusal_submit_FRAME; lia.
    - unfold w_off_stack; rewrite unsigned_lit by lia; unfold check_refusal_submit_FRAME; lia.
    - exact HMI2. }
  intros ms' Hpost.
  destruct Hpost as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m3 &
                     -> & MU3 & WMO3 & MI3 & ST3 & EB3 & WM3).
  rewrite unsigned_lit in MU3, ST3 by lia.
  subst B3.
  assert (HM3 : llvm_mem data D regs0 m0 Sp lo B2 m3 j10 jio (cmd_struct cb0 nn display key ++ jhi)).
  { eapply (llvm_mem_after_call data D regs0 m0 Sp lo check_refusal_submit_FRAME B2 B2 m2 m3);
      [ exact HM2 | unfold check_refusal_submit_FRAME, LH_K; lia
      | apply lh_munch_add_world; exact MU3 | exact WMO3 | exact MI3 | exact ST3 | exact WM3 | exact HFN2 ]. }
  clear HM2 G1 G2 G3 G4 G5 G6 HB2 HSTK2 HMI2 HWM2 HRW2 MU3 WMO3 MI3 ST3 WM3.
  rewrite (ret_pc_even 0x14514) by (first [lia | reflexivity]).
  (* ---- 0x14514 mv s3, s0; 0x14518 j 0x1456c; 0x1456c mv a0, zero; 0x14570 jal settle ---- *)
  do 4 zstep.
  pose proof HM3 as HM3c. unfold llvm_mem in HM3c.
  destruct HM3c as (_ & _ & _ & _ & _ & HSTK3 & _ & _ & _ & HMI3 & _ & HWM3 & _ & _ & _ & _ & _ & _ & _).
  eapply evt_cut.
  { eapply (STL _ (Z_to_bv 64 Sp) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo
              B2 B4 0).
    - reflexivity.
    - lia.
    - exact HWM3.
    - exact HS3.
    - rewrite unsigned_lit by lia; exact HSP.
    - rewrite unsigned_lit by lia; exact HSTK3.
    - rewrite unsigned_lit by lia; unfold settle_FRAME; lia.
    - unfold w_off_stack; rewrite unsigned_lit by lia; unfold settle_FRAME; lia.
    - exact HMI3. }
  intros ms' Hpost.
  destruct Hpost as (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & m4 &
                     -> & MU4 & WMO4 & MI4 & ST4 & EB4 & WM4).
  rewrite unsigned_lit in MU4, ST4 by lia.
  subst B4.
  assert (HM4 : llvm_mem data D regs0 m0 Sp lo B2 m4 j10 jio (cmd_struct cb0 nn display key ++ jhi)).
  { eapply (llvm_mem_after_call data D regs0 m0 Sp lo settle_FRAME B2 B2 m3 m4);
      [ exact HM3 | unfold settle_FRAME, LH_K; lia
      | apply lh_munch_add_world; exact MU4 | exact WMO4 | exact MI4 | exact ST4 | exact WM4 | exact HFN2 ]. }
  (* ---- the latch 0x14574 ---- *)
  rewrite (ret_pc_even 0x14574) by (first [lia | reflexivity]).
  apply evt_done. unfold llvm_latch. cbn [fi_off fi_n].
  replace (data + (fi_off c4 + nn)) with (data + fi_off c4 + nn) by lia.
  do 19 eexists. exists m4, j10, jio, (cmd_struct cb0 nn display key ++ jhi).
  split; [reflexivity|].
  split; [exact HOPS|].
  split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
  exact HM4.
Qed.
