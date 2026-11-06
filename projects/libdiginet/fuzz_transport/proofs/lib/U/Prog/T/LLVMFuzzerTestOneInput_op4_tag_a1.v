(* The tagged path of case 4 of the ubsan LLVMFuzzerTestOneInput, 0x141a4 .. 0x14220 (fuzz/fuzz_transport.c:1086-1088):
   serial = g_ncmd and its index trap (0x141ac), &g_cmd[serial] and its overflow check (0x141c4),
   memset(&g_cmd[serial], 0, 40) (the model's t4_B2), and len = fuzz_u8(&in) % 22 + 3 (a mulhu by the reciprocal of 22;
   the empty cursor takes the byte 0 at 0x14214). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid
  LLVMFuzzerTestOneInput_op4_lib LLVMFuzzerTestOneInput_op4_tag_lib LLVMFuzzerTestOneInput_op4_tag_m
  LLVMFuzzerTestOneInput_op4_tag_s.
Import ListNotations.
Open Scope Z_scope.

Lemma t4_A : memset_contract ->
  forall data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms (Q : machine_state -> Prop),
  llvm_op4_mid data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms ->
  g_ncmd B1 < CMDS_MAX ->
  (forall ms', t4_SA data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros MSET data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms Q H HSER HK.
  unfold memset_contract, MEMSET in MSET.
  destruct H as (ra & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s5 & s6 &
                 t3 & t4 & t5 & t6 & m & jlo & jio & jhi & -> & HOPS & HCUR & HBEF & HDSP & HKEY & LJLO & LJHI & HM).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  clear HD HSTK HRO HMU HWMO HRW.
  pose proof (wm_len _ _ _ _ HWM) as LB.
  pose proof (t4_ncmd_rng B1) as HNR.
  assert (HSN : 0 <= g_ncmd B1 < 1024) by (unfold CMDS_MAX in HSER; lia).
  pose proof HCUR as (HO3 & HN3 & HD3).
  change (Z_to_bv 64 LH_OP4_MID) with (Z_to_bv 64 0x141a4).
  (* ---- 0x141a4 lw s0, 0x10(s9): serial = g_ncmd ---- *)
  zstep.
  replace (s32_at B1 64984) with (g_ncmd B1)
    by (symmetry; apply t4_s32_small; change (u_at B1 64984 4) with (g_ncmd B1); lia).
  (* ---- 0x141a8 li a0, 0x401; 0x141ac bgeu s0, a0 (the index trap) ---- *)
  zstep. zstep. t4_br.
  (* ---- 0x141b0 li a0, 40; mul a0, s0, a0; auipc a1; addi s5, a1, -0xf0; add s2, s5, a0 ---- *)
  do 5 zstep.
  (* ---- 0x141c4 bltu s2, a0 (the overflow of &g_cmd[serial]) ---- *)
  zstep. t4_br.
  (* ---- 0x141c8 li a2, 40; mv a0, s2; mv a1, zero; jal memset ---- *)
  do 4 zstep.
  eapply evt_cut.
  { eapply MSET with (junk := sub B1 (A_Cmd_st (g_ncmd B1)) (Z.to_nat 40)); [| exact HMI].
    rewrite !unsigned_lit by lia.
    apply (wm_piece rsegs W_BASE_UBSAN m B1 (A_Cmd_st (g_ncmd B1)) 40);
      [ exact HWM | unfold A_Cmd_st, OFF_g_cmd, W_BASE_UBSAN; lia | unfold A_Cmd_st, OFF_g_cmd; lia | lia
      | unfold A_Cmd_st, OFF_g_cmd, W_LEN; lia ]. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m1 &
                     -> & MU1 & WMO1 & MI1 & CZ1).
  rewrite !unsigned_lit in MU1, CZ1 by lia.
  assert (HM1 : llvm_mem data D regs0 m0 Sp lo (t4_B2 B1) m1 (jlo ++ le8 (Z_to_bv 64 (bv_swrap 32 before))) jio
                  (cmd_struct (repeat (b8 0) 24) 0 display key ++ jhi)).
  { unfold t4_B2.
    eapply t4_after_fill; [exact HM0 | exact MU1 | exact WMO1 | exact MI1 | exact CZ1 | | | | | ];
      [ unfold A_Cmd_st, OFF_g_cmd, W_BASE_UBSAN; lia | unfold A_Cmd_st, OFF_g_cmd; lia | lia
      | unfold A_Cmd_st, OFF_g_cmd, W_LEN; lia | ].
    rewrite (t4_gf_upd B1 (repeat (b8 0) (Z.to_nat Cmd_ESZ)) (A_Cmd_st (g_ncmd B1)) LB);
      [ exact HFN | unfold A_Cmd_st, OFF_g_cmd; lia
      | rewrite repeat_length; unfold A_Cmd_st, OFF_g_cmd, Cmd_ESZ, W_LEN; lia
      | left; rewrite repeat_length; unfold A_Cmd_st, OFF_g_cmd, Cmd_ESZ, OFF_g_fail_next; lia ]. }
  clear MU1 WMO1 CZ1 HM0 HWM HMI HFN.
  t4_ret.
  pose proof HM1 as HM1c. unfold llvm_mem in HM1c.
  destruct HM1c as (_ & _ & _ & HD1 & _).
  (* ---- 0x141d8 beqz s4: the empty cursor takes the byte 0 ---- *)
  zstep.
  destruct (Z.eqb_spec (fi_n c3) 0) as [N0|N0].
  - (* 0x14214 mv a4, zero; 0x14218 li a0, 3; 0x1421c addi s10, sp, 0x61 *)
    t4_br. do 3 zstep.
    destruct (t4_c4_z D c3 N0) as [E4 EL].
    apply HK. unfold t4_SA. rewrite E4, EL.
    do 28 eexists. exists m1, jlo, jio, jhi.
    split; [reflexivity|].
    do 10 (split; [t4_weq|]).
    split; [exact (conj HOPS (conj HCUR (conj HBEF (conj HDSP (conj HKEY HSER)))))|].
    split; [exact LJLO|]. split; [exact LJHI|]. exact HM1.
  - (* 0x141dc addi a1, s7, 1; 0x141e0 addi s10, sp, 0x61; 0x141e4 bgeu s1, a1 (the pointer check) *)
    t4_br.
    pose proof (op4_read1 m1 data D (fi_off c3) HD1 ltac:(lia) ltac:(lia)) as HR0.
    pose proof (t4_byte_rng (nth (Z.to_nat (fi_off c3)) D (b8 0))) as HBR.
    zstep. zstep. zstep. t4_br.
    (* 0x141e8 lbu a0, 0(s7); 0x141ec auipc a2; 0x141f0 ld a2, 0x214(a2) (the reciprocal of 22);
       0x141f4 addi a4, s4, -1; 0x141f8 mulhu a2, a0, a2; 0x141fc li a3, 22; 0x14200 mul a2, a2, a3;
       0x14204 sub a0, a0, a2; 0x14208 addi a0, a0, 3; 0x1420c mv s7, a1; 0x14210 j 0x14220 *)
    do 11 zstep.
    destruct (t4_c4_nz D c3 N0) as [E4 EL].
    apply HK. unfold t4_SA. rewrite E4, EL. cbn [fi_off fi_n].
    do 28 eexists. exists m1, jlo, jio, jhi.
    split; [reflexivity|].
    do 8 (split; [t4_weq|]).
    split; [t4_len_eq (bv_unsigned (nth (Z.to_nat (fi_off c3)) D (b8 0)))|].
    split; [t4_weq|].
    split; [exact (conj HOPS (conj HCUR (conj HBEF (conj HDSP (conj HKEY HSER)))))|].
    split; [exact LJLO|]. split; [exact LJHI|]. exact HM1.
Qed.
