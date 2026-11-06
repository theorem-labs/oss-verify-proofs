(* The tagged path of case 4 of the ubsan LLVMFuzzerTestOneInput, 0x14220 .. 0x1427c (fuzz/fuzz_transport.c:1089-1093):
     0x14220  TAG, serial & 0x7f, serial >> 7 at sp+0x60 .. sp+0x62 and len at sp+0x78 (four sb), s6 = len - 3
              (by sp+0x08 = 2^32 - 3), then n = min(len - 3, in.n) (fuzz_take)                         t4_B1
     0x1425c  the cursor's n at sp+0x10, the take's UBSan checks, memcpy(sp+0x63, in.p, n)              t4_B2
   The struct diginet_cmd at sp+0x60 is then the model's cmd_struct over t4_cb. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells
  Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps
  TWorldLemmas TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_op4_mid
  LLVMFuzzerTestOneInput_op4_lib LLVMFuzzerTestOneInput_op4_tag_lib LLVMFuzzerTestOneInput_op4_tag_m
  LLVMFuzzerTestOneInput_op4_tag_s.
Import ListNotations.
Open Scope Z_scope.

(* 0x14228-0x14230: (len + 2^32 - 3) & (2^32 - 1) *)
Lemma t4_m3 : forall x, 3 <= x <= 24 -> Z.land (x + 4294967293) 4294967295 = x - 3.
Proof.
  intros x H. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia.
  replace (x + 4294967293) with (x - 3 + 1 * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma t4_n_lt : forall D c3, llvm_cursor D c3 -> t4_len D c3 - 3 < fi_n (t4_c4 D c3) -> t4_n D c3 = t4_len D c3 - 3.
Proof.
  intros D c3 HC H. pose proof (t4_tk_facts D c3 HC) as (_ & E & _).
  rewrite E. apply Z.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma t4_n_ge : forall D c3, llvm_cursor D c3 -> fi_n (t4_c4 D c3) <= t4_len D c3 - 3 -> t4_n D c3 = fi_n (t4_c4 D c3).
Proof.
  intros D c3 HC H. pose proof (t4_tk_facts D c3 HC) as (_ & E & _).
  rewrite E. apply Z.ltb_ge in H. rewrite H. reflexivity.
Qed.

Lemma t4_skip8 : forall (jlo v : list byte), length jlo = 8%nat -> skipn 8 (jlo ++ v) = v.
Proof. intros jlo v H. rewrite <- H. apply skipn_app_exact. Qed.

Lemma t4_first8 : forall w : word, firstn 8 (le8 w) = le8 w.
Proof. intros w. apply firstn_all2. rewrite length_le8. lia. Qed.

(* the memcpy of the n input bytes into the struct at offset 3 *)
Lemma t4_fill3 : forall (pfx p R : list byte) (n : nat), length pfx = 3%nat -> length p = n -> (n <= 21)%nat ->
  upd (pfx ++ repeat (b8 0) 21 ++ R) 3 p = pfx ++ p ++ repeat (b8 0) (21 - n) ++ R.
Proof.
  intros pfx p R n Lp Lq Hn. unfold upd. change (Z.to_nat 3) with 3%nat.
  rewrite firstn_app, Lp. replace (3 - 3)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  rewrite firstn_all2 by lia.
  rewrite skipn_app, Lp. rewrite (skipn_all2 pfx) by lia. cbn [app].
  replace (3 + length p - 3)%nat with n by lia.
  rewrite skipn_repeat_app by lia. reflexivity.
Qed.

Lemma t4_B1 : forall data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms (Q : machine_state -> Prop),
  t4_SA data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms ->
  (forall ms', t4_SB1 data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms Q H HK.
  destruct H as (ra & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 &
                 s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jlo & jio & jhi & -> &
                 E0 & E2 & E5 & E7 & E8 & E9 & E10 & E11 & Ea0 & Ea4 & HOK & LJLO & LJHI & HM).
  subst s0 s2 s5 s7 s8 s9 s10 s11 a0 a4.
  pose proof HOK as (HOPS & HCUR & HBEF & HDSP & HKEY & HSER).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  clear HD HSTK HRO HWM HFN HMU HWMO.
  pose proof (t4_len_rng D c3) as HLEN.
  pose proof (t4_cur4 D c3 HCUR) as (HO4 & HN4 & HD4).
  pose proof (t4_ncmd_rng B1) as HNR.
  assert (HSN : 0 <= g_ncmd B1 < 1024) by (unfold CMDS_MAX in HSER; lia).
  destruct (llvm_frame_split regs0 m Sp _ _ _ HRW) as (F1 & F2 & F3 & F4 & F5 & F6).
  clear HRW. unfold llvm_saved in F6.
  pose proof (munch_refl [(Sp, Sp + 240)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* ---- 0x14220 andi a1, s0, 0x7f; 0x14224 ld a3, 8(sp); 0x14228 add a2, a0, a3; 0x1422c addi a3, a3, 2;
     0x14230 and s6, a2, a3; 0x14234 srli a2, s0, 7; 0x14238 li a3, 0xa0;
     0x1423c sb a3, 0x60(sp); 0x14240 sb a1, 0x61(sp); 0x14244 sb a2, 0x62(sp); 0x14248 sb a0, 0x78(sp) ---- *)
  do 11 zstep.
  (* the struct after the four byte stores *)
  apply rw_cells_merge_all in F5. cbn [cells_size csize Nat.add] in F5.
  lazymatch type of F5 with
  | rw_cells _ _ _ [CB 40 ?X] =>
      let E := fresh "EJ" in
      assert (E : X = t4_j60s B1 D c3 display key jhi)
        by (unfold t4_j60s, t4_pfx, cmd_struct; cbn [cells_bytes cbytes firstn skipn app repeat];
            rewrite ?op4_sb, ?app_nil_r; rewrite (t4_shiftr7 (g_ncmd B1)) by lia; reflexivity);
      rewrite E in F5; clear E
  end.
  rewrite (t4_m3 (t4_len D c3)) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (llvm_frame_join regs0 mm Sp _ jio _ F1 F2 F3 F4 F5 F6) as HRW';
    pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo (t4_B2 B1) m mm _ jio _ _ jio
                  (t4_j60s B1 D c3 display key jhi) HM0 MU WMO HMI HRW' HJ1 HJ2
                  (t4_j60s_len B1 D c3 display key jhi LJHI)) as HM'
  end.
  clear F1 F2 F3 F4 F5 F6 HRW' MU WMO HMI HM0.
  (* ---- 0x1424c li s1, 0xf0; 0x14250 li s4, 0x13; 0x14254 bltu s6, a4: n = min(len - 3, in.n) ---- *)
  do 3 zstep.
  destruct (Z.lt_ge_cases (t4_len D c3 - 3) (fi_n (t4_c4 D c3))) as [LT|GE].
  - t4_br.
    apply HK. unfold t4_SB1. rewrite (t4_n_lt D c3 HCUR LT).
    do 28 eexists. eexists. exists jlo, jio, jhi.
    split; [reflexivity|].
    do 12 (split; [t4_weq|]).
    split; [exact HOK|]. split; [exact LJLO|]. split; [exact LJHI|]. exact HM'.
  - t4_br. zstep.
    apply HK. unfold t4_SB1. rewrite (t4_n_ge D c3 HCUR GE).
    do 28 eexists. eexists. exists jlo, jio, jhi.
    split; [reflexivity|].
    do 12 (split; [t4_weq|]).
    split; [exact HOK|]. split; [exact LJLO|]. split; [exact LJHI|]. exact HM'.
Qed.

Lemma t4_B2 : memcpy_contract ->
  forall data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms (Q : machine_state -> Prop),
  t4_SB1 data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms ->
  (forall ms', t4_SB data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms' -> evt rsegs Q ms') ->
  evt rsegs Q ms.
Proof.
  intros MCPY data D regs0 m0 Sp lo ops before c3 B1 display key F fc ms Q H HK.
  unfold memcpy_contract in MCPY.
  destruct H as (ra & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 &
                 s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jlo & jio & jhi & -> &
                 E0 & E1 & E2 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & Ea4 & HOK & LJLO & LJHI & HM).
  subst s0 s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 a4.
  pose proof HOK as (HOPS & HCUR & HBEF & HDSP & HKEY & HSER).
  pose proof HM as HM0. unfold llvm_mem in HM.
  destruct HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                  HJ1 & HJ2 & HJ3 & HRW).
  unfold LH_K, LH_FRAME in *.
  clear HD HSTK HRO HWM HFN HMU HWMO.
  pose proof (t4_len_rng D c3) as HLEN.
  pose proof (t4_tk_facts D c3 HCUR) as (EOFF & ENV & HNR & HNC & EO5 & EN5).
  pose proof (t4_cur4 D c3 HCUR) as (HO4 & HN4 & HD4).
  pose proof (t4_cbD D c3 HCUR) as (HCB1 & HCB2 & HCB3).
  destruct (llvm_frame_split regs0 m Sp _ _ _ HRW) as (F1 & F2 & F3 & F4 & F5 & F6).
  clear HRW. unfold llvm_saved in F6.
  pose proof (munch_refl [(Sp, Sp + 240)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMO.
  (* ---- 0x1425c sd a4, 0x10(sp) ---- *)
  zstep.
  apply rw_cells_merge_all in F2. cbn [cells_size csize Nat.add] in F2.
  lazymatch type of F2 with
  | rw_cells _ _ _ [CB 16 ?X] =>
      let E := fresh "EJ" in
      assert (E : X = t4_j10 D c3 before)
        by (unfold t4_j10; cbn [cells_bytes cbytes];
            rewrite ?app_nil_r, ?(t4_skip8 jlo _ LJLO), ?t4_first8; reflexivity);
      rewrite E in F2; clear E
  end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (llvm_frame_join regs0 mm Sp _ jio _ F1 F2 F3 F4 F5 F6) as HRW';
    pose proof (llvm_mem_store_frame data D regs0 m0 Sp lo (t4_B2 B1) m mm _ jio _ (t4_j10 D c3 before) jio
                  _ HM0 MU WMO HMI HRW' (t4_j10_len D c3 before) HJ2 HJ3) as HM1
  end.
  clear F1 F2 F3 F4 F5 F6 HRW' MU WMO HMI HM0.
  pose proof HM1 as HM1c. unfold llvm_mem in HM1c.
  destruct HM1c as (_ & _ & _ & HD1 & _ & _ & _ & _ & _ & HMI1 & _).
  (* ---- 0x14260 add s3, s6, s7; 0x14264 bltu s3, s7; 0x14268 beqz s3 (the take's UBSan checks) ---- *)
  zstep. zstep. t4_br. zstep. t4_br.
  (* ---- 0x1426c addi a0, sp, 0x63; 0x14270 mv a1, s7; 0x14274 mv a2, s6; 0x14278 jal memcpy ---- *)
  do 4 zstep.
  eapply evt_cut.
  { eapply MCPY with (src := sub D (fi_off (t4_c4 D c3)) (Z.to_nat (t4_n D c3))).
    - rewrite !unsigned_lit by lia.
      apply (t4_sub_bytes _ data D (fi_off (t4_c4 D c3)) (Z.to_nat (t4_n D c3)));
        [exact HD1 | lia | rewrite <- EOFF; lia | lia].
    - rewrite !unsigned_lit by lia. rewrite length_sub by lia. f_equal; lia.
    - rewrite !unsigned_lit by lia.
      apply (t4_mem_cell60 data D regs0 m0 Sp lo (t4_B2 B1) _ (t4_j10 D c3 before) jio
               (t4_j60s B1 D c3 display key jhi) 3); [exact HM1 | lia | lia | lia | lia].
    - rewrite !unsigned_lit by lia. left; lia.
    - exact HMI1. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 &
                     -> & MU2 & WMO2 & MI2 & DST2 & SRC2).
  clear SRC2.
  rewrite !unsigned_lit in MU2, DST2 by lia.
  pose proof (t4_mem_fill60 data D regs0 m0 Sp lo (t4_B2 B1) _ m2 (t4_j10 D c3 before) jio
                (t4_j60s B1 D c3 display key jhi) 3 _ (sub D (fi_off (t4_c4 D c3)) (Z.to_nat (t4_n D c3))) _
                HM1 MU2 WMO2 MI2 DST2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HM2.
  assert (EJ : upd (t4_j60s B1 D c3 display key jhi) 3 (sub D (fi_off (t4_c4 D c3)) (Z.to_nat (t4_n D c3)))
               = t4_cs B1 D c3 display key ++ jhi).
  { unfold t4_j60s, t4_cs, t4_cb, cmd_struct. rewrite <- EOFF. rewrite <- !app_assoc.
    rewrite (t4_fill3 (t4_pfx B1) _ _ (Z.to_nat (t4_n D c3))); [| reflexivity | apply length_sub; lia | lia].
    replace (Z.to_nat (21 - t4_n D c3)) with (21 - Z.to_nat (t4_n D c3))%nat by lia.
    unfold t4_pfx. reflexivity. }
  rewrite EJ in HM2. clear EJ HM1.
  t4_ret.
  apply HK. unfold t4_SB. rewrite EO5.
  do 28 eexists. exists m2, jio, jhi.
  split; [reflexivity|].
  do 11 (split; [t4_weq|]).
  split; [exact HOK|]. split; [exact LJHI|]. exact HM2.
Qed.
