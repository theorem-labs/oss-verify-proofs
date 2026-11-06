(* Case 4 of the ubsan LLVMFuzzerTestOneInput, 0x13e94 .. the raw / tagged split: the key
   (c.key = SPEC_KEY(kb % 9 + 1, ab), stored at sp+0x7c), the display byte (c.display = fuzz_u8(in) & 1, stored at
   sp+0x79), the g_raw test (:1078) and, on the raw arm, the u16 w of :1079. The tagged arm ends at 0x141a4
   (llvm_op4_mid, after `sd s0, 0x18(sp)`), the raw arm at 0x14488 (op4_r). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid LLVMFuzzerTestOneInput_op4_lib
  LLVMFuzzerTestOneInput_op4_defs.
Import ListNotations.
Open Scope Z_scope.

(* the 40 bytes of the frame cell after the key store (offset 28) and the display store (offset 25) *)
Ltac op4_cmd_fix F5 display key jhi :=
  apply rw_cells_merge_all in F5;
  cbn [cells_size csize Nat.add] in F5;
  lazymatch type of F5 with
  | rw_cells _ _ _ [CB 40 ?X] =>
      let E := fresh "ECMD" in
      assert (E : X = cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi)
        by (cbn [cells_bytes cbytes firstn skipn app repeat];
            rewrite ?op4_sb, ?le4_put, ?app_nil_r; unfold cmd_struct; cbn [app repeat];
            rewrite <- ?app_assoc; reflexivity);
      rewrite E in F5; clear E
  end.

Lemma op4_key_lem : forall data D regs0 m0 Sp lo ops c2 kb ab before B1 F fc ms c3 db c3' lo8 c4 hi8
    (Q : machine_state -> Prop),
  op4_s2 data D regs0 m0 Sp lo ops c2 kb ab before B1 F fc ms ->
  fuzz_u8_m D c2 = (c3, db) -> fuzz_u8_m D c3 = (c3', lo8) -> fuzz_u8_m D c3' = (c4, hi8) ->
  (g_raw B1 = 0 -> forall ms',
     llvm_op4_mid data D regs0 m0 Sp lo ops before c3 B1 (Z.land db 1) (KEY (kb mod 9 + 1) ab) F fc ms' ->
     evt rsegs Q ms') ->
  (g_raw B1 <> 0 -> forall ms',
     op4_r data D regs0 m0 Sp lo ops c4 lo8 hi8 before B1 (Z.land db 1) (KEY (kb mod 9 + 1) ab) F fc ms' ->
     evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo ops c2 kb ab before B1 F fc ms c3 db c3' lo8 c4 hi8 Q H E1 E2 E3 HKT HKR.
  destruct H as (ra & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s5 & s6 & s7 & t3 & t4 & t5 & t6 & m & j10 & jio & jhi &
                 -> & HOPS & HC & HKB & HAB & RQ & LJ & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold llvm_cursor in HC. unfold LH_K, LH_FRAME in *.
  pose proof (bytes_at_bound rsegs m data D HD) as HDB.
  pose proof (s32_range B1 OFF_g_raw) as RRAW. change (s32_at B1 OFF_g_raw) with (g_raw B1) in RRAW.
  assert (HKEY : 0 <= KEY (kb mod 9 + 1) ab < 2 ^ 32).
  { unfold KEY. assert (0 <= kb mod 9 < 9) by (apply Z.mod_pos_bound; lia).
    apply lor_lt_pow2; [lia|]. change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound ab (2 ^ 16) ltac:(lia)). lia. }
  assert (HDSP : 0 <= Z.land db 1 <= 1).
  { assert (EL : Z.land db 1 = db mod 2) by (change 1 with (Z.ones 1); apply Z.land_ones; lia).
    rewrite EL. pose proof (Z.mod_pos_bound db 2 ltac:(lia)). lia. }
  destruct (llvm_frame_split regs0 m Sp j10 jio (repeat (b8 0) 32 ++ jhi) HRW) as (F1 & F2 & F3 & F4 & F5 & F6).
  clear HRW HSTK HRO HMU HWMO.
  unfold llvm_saved in F6.
  pose proof (munch_refl [(Sp, Sp + LH_FRAME)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  unfold LH_FRAME in MU.
  (* ---- 0x13e94-0x13eb4: the key; 0x13eb8 sw a1, 0x7c(sp) ---- *)
  do 9 zstep.
  rewrite (op4_key_val kb ab HKB HAB).
  do 2 zstep.
  (* the world across the key store (the store tactic drops it) *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wmem_frame_transport m mm Sp B1
                  ltac:(destruct HM0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & _); exact W)
                  MU WMO ltac:(lia)) as HWM1
  end.
  (* ---- 0x13ebc beqz a0 ---- *)
  destruct (Z.eqb_spec (fi_n c2) 0) as [N0|N0].
  - (* the cursor is empty: db = 0, display = 0 *)
    rewrite fu8_z in E1 by lia. injection E1 as <- <-.
    br.
    (* 0x13f10 lw a0, g_raw; 0x13f14 sb zero, 0x79(sp); 0x13f18 beqz a0 *)
    do 2 zstep.
    change (s32_at B1 64972) with (g_raw B1).
    zstep.
    destruct (Z.eqb_spec (g_raw B1) 0) as [R0|R0].
    + (* tagged: 0x14198 sd s0, 0x18(sp); 0x1419c mv s4, zero; 0x141a0 mv s7, s3 *)
      br. do 3 zstep.
      change (Z.land 0 1) with 0.
      op4_cmd_fix F5 0 (KEY (kb mod 9 + 1) ab) jhi.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply rw_cells_merge_all in F2; cbn [cells_size csize Nat.add cells_bytes cbytes] in F2;
        rewrite app_nil_r in F2;
        pose proof (llvm_frame_join regs0 mm Sp _ jio _ F1 F2 F3 F4 F5 F6) as HRW';
        pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo B1 m mm j10 jio (repeat (b8 0) 32 ++ jhi)
                      _ jio _ HM0 MU WMO HMI HRW' ltac:(rewrite app_length, firstn_length, length_le8; lia)
                      HJ2 ltac:(unfold cmd_struct; rewrite !app_length, repeat_length, length_put; cbn [length];
                                lia)) as HM'
      end.
      apply (HKT R0). unfold llvm_op4_mid.
      replace (fi_n c2) with 0 by lia.
      do 21 eexists. eexists. exists (firstn 8 j10), jio, jhi.
      split; [reflexivity|].
      split; [exact HOPS|]. split; [exact HC|]. split; [exact RQ|]. split; [lia|]. split; [exact HKEY|].
      split; [rewrite firstn_length; lia|]. split; [exact LJ|]. exact HM'.
    + (* raw: 0x13f1c mv a0, zero; 0x13f20 mv a1, zero; 0x13f24 mv a2, zero; 0x13f28 j 0x14488 *)
      br. do 4 zstep.
      rewrite fu8_z in E2 by lia. injection E2 as <- <-.
      rewrite fu8_z in E3 by lia. injection E3 as <- <-.
      change (Z.land 0 1) with 0.
      op4_cmd_fix F5 0 (KEY (kb mod 9 + 1) ab) jhi.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (llvm_frame_join regs0 mm Sp j10 jio _ F1 F2 F3 F4 F5 F6) as HRW';
        pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo B1 m mm j10 jio (repeat (b8 0) 32 ++ jhi)
                      j10 jio _ HM0 MU WMO HMI HRW' HJ1 HJ2
                      ltac:(unfold cmd_struct; rewrite !app_length, repeat_length, length_put; cbn [length];
                            lia)) as HM'
      end.
      apply (HKR R0). unfold op4_r.
      replace (fi_n c2) with 0 by lia.
      do 17 eexists. exists j10, jio, jhi.
      split; [reflexivity|].
      split; [exact HOPS|]. split; [exact HC|]. split; [lia|]. split; [lia|]. split; [exact RQ|].
      split; [lia|]. split; [exact HKEY|]. split; [exact LJ|]. exact HM'.
  - (* db is read: 0x13ec0 addi s7, s3, 1; 0x13ec4 bgeu (trap); 0x13ec8 lbu a1, 0(s3); 0x13ecc lw a2, g_raw;
       0x13ed0 andi a1, a1, 1; 0x13ed4 sb a1, 0x79(sp); 0x13ed8 addi s4, a0, -1; 0x13edc beqz a2 *)
    rewrite fu8_nz in E1 by lia. injection E1 as <- <-.
    pose proof (op4_read1 _ data D (fi_off c2) HD ltac:(lia) ltac:(lia)) as HR0.
    br. do 2 zstep. br. do 2 zstep.
    change (s32_at B1 64972) with (g_raw B1).
    do 4 zstep.
    cbn [fi_off fi_n] in E2 |- *.
    destruct (Z.eqb_spec (g_raw B1) 0) as [R0|R0].
    + (* tagged: 0x13fc0 sd s0, 0x18(sp); 0x13fc4 j 0x141a4 *)
      br. do 2 zstep.
      op4_cmd_fix F5 (Z.land (at8 D (Z.to_nat (fi_off c2))) 1) (KEY (kb mod 9 + 1) ab) jhi.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply rw_cells_merge_all in F2; cbn [cells_size csize Nat.add cells_bytes cbytes] in F2;
        rewrite app_nil_r in F2;
        pose proof (llvm_frame_join regs0 mm Sp _ jio _ F1 F2 F3 F4 F5 F6) as HRW';
        pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo B1 m mm j10 jio (repeat (b8 0) 32 ++ jhi)
                      _ jio _ HM0 MU WMO HMI HRW' ltac:(rewrite app_length, firstn_length, length_le8; lia)
                      HJ2 ltac:(unfold cmd_struct; rewrite !app_length, repeat_length, length_put; cbn [length];
                                lia)) as HM'
      end.
      apply (HKT R0). unfold llvm_op4_mid. cbn [fi_off fi_n].
      replace (data + (fi_off c2 + 1)) with (data + fi_off c2 + 1) by lia.
      replace (fi_n c2 - 1) with (fi_n c2 + -1) by lia.
      do 21 eexists. eexists. exists (firstn 8 j10), jio, jhi.
      split; [reflexivity|].
      split; [exact HOPS|]. split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
      split; [exact RQ|]. split; [exact HDSP|]. split; [exact HKEY|].
      split; [rewrite firstn_length; lia|]. split; [exact LJ|]. exact HM'.
    + (* raw: 0x13ee0 beqz s4 *)
      br. zstep.
      destruct (Z.eqb_spec (fi_n c2) 1) as [N1|N1].
      * (* one byte left: 0x14180 a0 = a1 = a2 = 0; s3 = s7; s4 = 7 *)
        rewrite fu8_z in E2 by (cbn [fi_n]; lia). injection E2 as <- <-.
        rewrite fu8_z in E3 by (cbn [fi_n]; lia). injection E3 as <- <-.
        br. do 6 zstep.
        op4_cmd_fix F5 (Z.land (at8 D (Z.to_nat (fi_off c2))) 1) (KEY (kb mod 9 + 1) ab) jhi.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (llvm_frame_join regs0 mm Sp j10 jio _ F1 F2 F3 F4 F5 F6) as HRW';
          pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo B1 m mm j10 jio (repeat (b8 0) 32 ++ jhi)
                        j10 jio _ HM0 MU WMO HMI HRW' HJ1 HJ2
                        ltac:(unfold cmd_struct; rewrite ?app_length, ?repeat_length, ?length_put;
                              cbn [length]; lia)) as HM'
        end.
        apply (HKR R0). unfold op4_r. cbn [fi_off fi_n].
        replace (data + (fi_off c2 + 1)) with (data + fi_off c2 + 1) by lia.
        replace (fi_n c2 - 1) with 0 by lia.
        do 17 eexists. exists j10, jio, jhi.
        split; [reflexivity|].
        split; [exact HOPS|]. split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
        split; [lia|]. split; [lia|]. split; [exact RQ|]. split; [exact HDSP|]. split; [exact HKEY|].
        split; [exact LJ|]. exact HM'.
      * (* lo8 is read: 0x13ee4 addi s7; bgeu; 0x13eec lbu a1, 1(s3); 0x13ef0 addi a3, s3, 2; li s4, 7;
           li a2, 2; 0x13efc bne a0, a2 *)
        rewrite fu8_nz in E2 by (cbn [fi_n]; lia). cbn [fi_off fi_n] in E2. injection E2 as <- <-.
        pose proof (op4_read1 _ data D (fi_off c2 + 1) HD ltac:(lia) ltac:(lia)) as HR1.
        br. do 2 zstep. br. do 5 zstep.
        cbn [fi_off fi_n] in E3 |- *.
        destruct (Z.eqb_spec (fi_n c2) 2) as [N2|N2].
        -- (* 0x13f00 a0 = 0; a2 = 0; s3 = a3 *)
           rewrite fu8_z in E3 by (cbn [fi_n]; lia). injection E3 as <- <-.
           br. do 4 zstep.
           op4_cmd_fix F5 (Z.land (at8 D (Z.to_nat (fi_off c2))) 1) (KEY (kb mod 9 + 1) ab) jhi.
           lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             pose proof (llvm_frame_join regs0 mm Sp j10 jio _ F1 F2 F3 F4 F5 F6) as HRW';
             pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo B1 m mm j10 jio (repeat (b8 0) 32 ++ jhi)
                           j10 jio _ HM0 MU WMO HMI HRW' HJ1 HJ2
                           ltac:(unfold cmd_struct; rewrite ?app_length, ?repeat_length, ?length_put;
                                 cbn [length]; lia)) as HM'
           end.
           apply (HKR R0). unfold op4_r. cbn [fi_off fi_n].
           replace (fi_n c2 - 1 - 1) with 0 by lia.
           replace (data + (fi_off c2 + 1 + 1)) with (data + fi_off c2 + 2) by lia.
           do 17 eexists. exists j10, jio, jhi.
           split; [reflexivity|].
           split; [exact HOPS|]. split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
           split; [apply at8_range|]. split; [lia|]. split; [exact RQ|]. split; [exact HDSP|].
           split; [exact HKEY|]. split; [exact LJ|]. exact HM'.
        -- (* hi8 is read: 0x14474 addi a3; bgeu; 0x1447c lbu a2, 2(s3); 0x14480 addi s3, s3, 3;
              0x14484 addi a0, a0, -3 *)
           rewrite fu8_nz in E3 by (cbn [fi_n]; lia). cbn [fi_off fi_n] in E3. injection E3 as <- <-.
           pose proof (op4_read1 _ data D (fi_off c2 + 2) HD ltac:(lia) ltac:(lia)) as HR2.
           br. do 2 zstep. br. do 3 zstep.
           op4_cmd_fix F5 (Z.land (at8 D (Z.to_nat (fi_off c2))) 1) (KEY (kb mod 9 + 1) ab) jhi.
           lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
             pose proof (llvm_frame_join regs0 mm Sp j10 jio _ F1 F2 F3 F4 F5 F6) as HRW';
             pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo B1 m mm j10 jio (repeat (b8 0) 32 ++ jhi)
                           j10 jio _ HM0 MU WMO HMI HRW' HJ1 HJ2
                           ltac:(unfold cmd_struct; rewrite ?app_length, ?repeat_length, ?length_put;
                                 cbn [length]; lia)) as HM'
           end.
           apply (HKR R0). unfold op4_r. cbn [fi_off fi_n].
           replace (data + (fi_off c2 + 1 + 1 + 1)) with (data + fi_off c2 + 3) by lia.
           replace (fi_n c2 - 1 - 1 - 1) with (fi_n c2 + -3) by lia.
           replace (Z.to_nat (fi_off c2 + 1 + 1)) with (Z.to_nat (fi_off c2 + 2)) by (f_equal; lia).
           do 17 eexists. exists j10, jio, jhi.
           split; [reflexivity|].
           split; [exact HOPS|]. split; [unfold llvm_cursor; cbn [fi_off fi_n]; lia|].
           split; [apply at8_range|]. split; [apply at8_range|]. split; [exact RQ|]. split; [exact HDSP|].
           split; [exact HKEY|]. split; [exact LJ|]. exact HM'.
Qed.
