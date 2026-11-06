(* check_state_desk_seg_head: the head of check_state_desk in image B (fuzz_transport.asan-ubsan, 0x854d8 ..
   0x855e8, after the prologue of lib/B/Prog/check_state_desk_seg_kit.v csd_pro_F): GOT.desk <= OW.desk, the UBSan
   alignment test of p, the checks of the loads of n->mac_offset, n->personality and n->announce, and, when
   n->personality is not NULL, the UBSan alignment and NULL tests of the two records it and OW.desk_p name and their
   device and strips bytes. Image B's twin of lib/A/Prog/check_state_desk_seg_head.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_desk_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Section Pieces.
Variables (RNG : ExecF.footprint)
  (sp gp tp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Local Notation ST pc x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 mm :=
  (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
           s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

(* ---- the head: 0x854d8 .. 0x855e8 ---- *)

Lemma csd_head_F : forall (m : word -> option byte) (p : Z) (NB Bw : list byte) (fr : TI.tframe) (vn nn : nat)
    (ra s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 : word) (Q : machine_state -> Prop),
  csd_mem m p NB Bw fr vn nn -> csd_rng RNG (bv_unsigned sp) p NB fr vn nn -> csd_bnd p NB Bw fr ->
  (TW.s32_at Bw TW.A_OW_desk <? TW.s32_at Bw TW.A_GOT_desk) = false ->
  TW.s32_at NB 40 = TW.s32_at Bw TW.A_OW_desk_off ->
  (TW.u_at NB 32 8 =? 0) = (TW.u_at Bw TW.A_OW_desk_p 8 =? 0) ->
  (TW.u_at NB 32 8 = 0 \/ (TW.u_at NB 32 8 = CSD_PERS0 /\ TW.u_at Bw TW.A_OW_desk_p 8 = CSD_C24) \/
   (TW.u_at NB 32 8 = CSD_PERS1 /\ TW.u_at Bw TW.A_OW_desk_p 8 = CSD_PC)) ->
  (forall x10 x11 x12 x14 x15 x16 x17 : word,
     ExecF.evtF rsegs RNG Q (ST 0x855e8 ra (Z_to_bv 64 (TW.u_at NB 24 8)) s1 x10 x11 x12 (Z_to_bv 64 TB_OW)
                               x14 x15 x16 x17 s2 s3 (Z_to_bv 64 ASAN_K) m)) ->
  ExecF.evtF rsegs RNG Q (ST 0x854d8 ra s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 m).
Proof.
  intros m p NB Bw fr vn nn ra s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 Q MEM RNGH BND C1 C2 C3 CP CONT.
  csd_prep MEM RNGH BND.
  assert (RG : ov_read_bytes rsegs m (wa (TB_GOT + 208)) 4 = Some (TW.sub Bw TW.A_GOT_desk 4))
    by (apply csd_rdall; [exact M3 | apply csd_len_sub; unfold TW.A_GOT_desk, TW.OFF_GOT, TW.W_LEN in *; lia]).
  assert (RO : ov_read_bytes rsegs m (wa (TB_OW + 208)) 4 = Some (TW.sub Bw TW.A_OW_desk 4))
    by (apply csd_rdall; [exact M4 | apply csd_len_sub; unfold TW.A_OW_desk, TW.OFF_OW, TW.W_LEN in *; lia]).
  assert (ROO : ov_read_bytes rsegs m (wa (TB_OW + 232)) 4 = Some (TW.sub Bw TW.A_OW_desk_off 4))
    by (apply csd_rdall; [exact M5 | apply csd_len_sub; unfold TW.A_OW_desk_off, TW.OFF_OW, TW.W_LEN in *; lia]).
  assert (ROP : ov_read_bytes rsegs m (wa (TB_OW + 240)) 8 = Some (TW.sub Bw TW.A_OW_desk_p 8))
    by (apply csd_rdall; [exact M6 | apply csd_len_sub; unfold TW.A_OW_desk_p, TW.OFF_OW, TW.W_LEN in *; lia]).
  pose proof (csd_rdall m _ _ 8 M1 (length_le8 _)) as RDG.
  pose proof (csd_rdall m _ _ 8 M2 (length_le8 _)) as RDC.
  pose proof (TWL.u_at_range NB 32 8) as RPN. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RPN.
  pose proof (TWL.u_at_range Bw TW.A_OW_desk_p 8) as RPD. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RPD.
  pose proof (TWL.u_at_range NB 24 8) as RAN. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in RAN.
  assert (RS3 : ExecF.rng RNG ((p + 24) / 8 + ASAN_K) 1)
    by (apply RA; do 5 right; left; exists 3; split; [lia | f_equal; f_equal; lia]).
  assert (RS4 : ExecF.rng RNG ((p + 32) / 8 + ASAN_K) 1)
    by (apply RA; do 5 right; left; exists 4; split; [lia | f_equal; f_equal; lia]).
  assert (RS5 : ExecF.rng RNG ((p + 40) / 8 + ASAN_K) 1)
    by (apply RA; do 5 right; left; exists 5; split; [lia | f_equal; f_equal; lia]).
  assert (MS3 : mrd rsegs m (wa ((p + 24) / 8 + ASAN_K)) = Some (Z_to_bv 8 0))
    by (rewrite <- (M9 3 ltac:(lia)); do 3 f_equal; lia).
  assert (MS4 : mrd rsegs m (wa ((p + 32) / 8 + ASAN_K)) = Some (Z_to_bv 8 0))
    by (rewrite <- (M9 4 ltac:(lia)); do 3 f_equal; lia).
  assert (MS5 : mrd rsegs m (wa ((p + 40) / 8 + ASAN_K)) = Some (Z_to_bv 8 0))
    by (rewrite <- (M9 5 ltac:(lia)); do 3 f_equal; lia).
  unfold ASAN_K in RS3, RS4, RS5, MS3, MS4, MS5.
  pose proof (Z.div_pos (p + 24) 8 ltac:(lia) ltac:(lia)) as DP3.
  pose proof (Z.div_le_upper_bound (p + 40) 8 (2 ^ 63) ltac:(lia) ltac:(lia)) as DP5.
  (* ---- 0x855e8 is reached from 0x855cc: the check of the 8-byte load at p + 24, s0 = n->announce ---- *)
  assert (TAIL : forall x11 x12 x14 x15 x16 x17 : word,
    ExecF.evtF rsegs RNG Q (ST 0x855cc ra s0 s1 (Z_to_bv 64 p) x11 x12 (Z_to_bv 64 TB_OW)
                              x14 x15 x16 x17 s2 s3 (Z_to_bv 64 ASAN_K) m)).
  { intros x11 x12 x14 x15 x16 x17.
    unfold TB_OW, ASAN_K.
    step. try rewrite (unsigned_lit p) by lia.
    step. gen_shr (Z_to_bv 64 (p + 24)) g G. rewrite (unsigned_lit (p + 24)) in G by lia.
    step. gen_addi g h H.
    pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS3 ltac:(lia)) as RH.
    pose proof (rdw0 m h _ _ MS3 ltac:(lia)) as R. step. clear R.
    step. brF false.
    pose proof (csd_rdn m p NB 24 8 (p + 24) M8 ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as R.
    step. clear R. rewrite ld_world.
    step. br_false ltac:(rewrite PW.csd_eqb_lit by lia; apply Z.eqb_neq; lia).
    apply CONT. }
  unfold TB_GOT, TB_OW, GOT_CELL_K, CELL_K, ASAN_K in *.
  (* 0x854d8 auipc a1; 0x854dc auipc a2; 0x854e0 lw a1 (GOT.desk); 0x854e4 addi a3 (OW); 0x854e8 lw a2 (OW.desk) *)
  step. step. step. step. step.
  rewrite !lw_world.
  (* 0x854ec blt a2,a1: OW.desk < GOT.desk goes to the trap *)
  step. br_false ltac:(rewrite (PW.csd_lts_s32 _ _ (TWL.s32_range _ _) (TWL.s32_range _ _)); exact C1).
  (* 0x854f0 andi a1,a0,7; 0x854f4 bnez a1: p mod 8 = 0 (the UBSan alignment test) *)
  step.
  step. br_false ltac:(rewrite (unsigned_lit p) by lia; rewrite land7, BP8, bv_eqb_refl; reflexivity).
  (* 0x854f8 auipc a1; 0x854fc ld a1 (GOT_CELL_K); 0x85500 ld s4 (CELL_K): s4 = 0x7fff8000 *)
  step. step. step.
  (* 0x85504 addi a1,a0,40 and the check of the 4-byte load at p + 40 *)
  step. try rewrite (unsigned_lit p) by lia.
  step. gen_shr (Z_to_bv 64 (p + 40)) g G. rewrite (unsigned_lit (p + 40)) in G by lia.
  step. gen_addi g h H.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS5 ltac:(lia)) as RH.
  pose proof (rdw0 m h _ _ MS5 ltac:(lia)) as R. step. clear R.
  step. brF false.
  (* 0x85518 lw a1 (n->mac_offset); 0x8551c lw a2 (OW.desk_off); 0x85520 bne a1,a2 *)
  pose proof (csd_rdn m p NB 40 4 (p + 40) M8 ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as R.
  step. clear R. rewrite lw_world.
  step. rewrite lw_world.
  step. br_false ltac:(rewrite C2, bv_eqb_refl; reflexivity).
  (* 0x85524 addi a1,a0,32 and the check of the 8-byte load at p + 32 *)
  step. try rewrite (unsigned_lit p) by lia.
  step. clear g h G H RH. gen_shr (Z_to_bv 64 (p + 32)) g G. rewrite (unsigned_lit (p + 32)) in G by lia.
  step. gen_addi g h H.
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS4 ltac:(lia)) as RH.
  pose proof (rdw0 m h _ _ MS4 ltac:(lia)) as R. step. clear R.
  step. brF false.
  (* 0x85538 ld a5 (n->personality); 0x8553c ld a4 (OW.desk_p) *)
  pose proof (csd_rdn m p NB 32 8 (p + 32) M8 ltac:(lia) ltac:(rewrite ML; lia) eq_refl) as R.
  step. clear R. rewrite ld_world.
  step. rewrite ld_world.
  (* 0x85540 sltiu a1,a5,1; 0x85544 sltu a2,zero,a4; 0x85548 beq a1,a2: exactly one of them NULL goes to the trap *)
  step. rewrite PW.csd_seqz by lia.
  step. rewrite PW.csd_snez by lia.
  step. br_false ltac:(rewrite PW.csd_eqb_b2z, C3; destruct (TW.u_at Bw TW.A_OW_desk_p 8 =? 0); reflexivity).
  (* 0x8554c beq a5,zero *)
  step. rewrite PW.csd_eqb_lit by lia.
  destruct (Z.eqb_spec (TW.u_at NB 32 8) 0) as [PN0|PN0]; cbv iota.
  { apply TAIL. }
  (* n->personality names personalities[0] and OW.desk_p SPEC_C24, or personalities[1] and SPEC_PC: the checks of
     the 1-byte loads of the element's device and strips bytes and the desk's, each granule's shadow byte 0, and
     the two compares of equal bytes, after the UBSan tests pn & 7 = 0 (0x85550), pd <> 0 (0x85558) and pd & 7 = 0
     (0x8555c), on the records' closed addresses *)
  destruct CP as [E|[[E1 E2]|[E1 E2]]]; [contradiction|..].
  - rewrite E1, E2. unfold CSD_PERS0, CSD_C24. cbn [TI.ti_personalities TI.ti_spec_c24 timg_B].
    pose proof (rd1 _ _ _ (M14 CSD_P0 ltac:(cbn; tauto))) as RSP. change (CSD_P0 / 8 + 2147450880) with 2147534690 in RSP.
    pose proof (rd1 _ _ _ (M14 CSD_D0 ltac:(cbn; tauto))) as RSD. change (CSD_D0 / 8 + 2147450880) with 2147534657 in RSD.
    pose proof (csd_rd1 m _ _ 0 670480 M10 ltac:(cbn; lia) eq_refl) as RB0.
    pose proof (csd_rd1 m _ _ 1 670481 M10 ltac:(cbn; lia) eq_refl) as RB1.
    pose proof (csd_rd1 m _ _ 0 670216 M12 ltac:(cbn; lia) eq_refl) as RD0.
    pose proof (csd_rd1 m _ _ 1 670217 M12 ltac:(cbn; lia) eq_refl) as RD1.
    cbn [nth] in RB0, RB1, RD0, RD1.
    pose proof (RA 2147534690 ltac:(do 6 right; left; exists CSD_P0; split; [cbn; tauto | right; reflexivity])) as GSP.
    pose proof (RA 2147534657 ltac:(do 6 right; left; exists CSD_D0; split; [cbn; tauto | right; reflexivity])) as GSD.
    pose proof (RA 670480 ltac:(do 6 right; left; exists CSD_P0; split; [cbn; tauto | left; unfold CSD_P0, CSD_PERS0; cbn; lia])) as GB0.
    pose proof (RA 670481 ltac:(do 6 right; left; exists CSD_P0; split; [cbn; tauto | left; unfold CSD_P0, CSD_PERS0; cbn; lia])) as GB1.
    pose proof (RA 670216 ltac:(do 6 right; left; exists CSD_D0; split; [cbn; tauto | left; unfold CSD_D0, CSD_C24; cbn; lia])) as GD0.
    pose proof (RA 670217 ltac:(do 6 right; left; exists CSD_D0; split; [cbn; tauto | left; unfold CSD_D0, CSD_C24; cbn; lia])) as GD1.
    step. step. brF false. step. brF false. step. step. brF false.
    step. step. step. step. step. brF false.
    step. step. step. step. step. step. brF false. step. step. brF false.
    step. step. step. step. step. brF false.
    step. step. step. step. step. step. brF false. step. step. brF false.
    apply TAIL.
  - rewrite E1, E2. unfold CSD_PERS1, CSD_PERS0, CSD_PC. cbn [TI.ti_personalities TI.ti_spec_pc timg_B].
    pose proof (rd1 _ _ _ (M14 CSD_P1 ltac:(cbn; tauto))) as RSP. change (CSD_P1 / 8 + 2147450880) with 2147534693 in RSP.
    pose proof (rd1 _ _ _ (M14 CSD_D1 ltac:(cbn; tauto))) as RSD. change (CSD_D1 / 8 + 2147450880) with 2147534661 in RSD.
    pose proof (csd_rd1 m _ _ 0 670504 M11 ltac:(cbn; lia) eq_refl) as RB0.
    pose proof (csd_rd1 m _ _ 1 670505 M11 ltac:(cbn; lia) eq_refl) as RB1.
    pose proof (csd_rd1 m _ _ 0 670248 M13 ltac:(cbn; lia) eq_refl) as RD0.
    pose proof (csd_rd1 m _ _ 1 670249 M13 ltac:(cbn; lia) eq_refl) as RD1.
    cbn [nth] in RB0, RB1, RD0, RD1.
    pose proof (RA 2147534693 ltac:(do 6 right; left; exists CSD_P1; split; [cbn; tauto | right; reflexivity])) as GSP.
    pose proof (RA 2147534661 ltac:(do 6 right; left; exists CSD_D1; split; [cbn; tauto | right; reflexivity])) as GSD.
    pose proof (RA 670504 ltac:(do 6 right; left; exists CSD_P1; split; [cbn; tauto | left; unfold CSD_P1, CSD_PERS1, CSD_PERS0; cbn; lia])) as GB0.
    pose proof (RA 670505 ltac:(do 6 right; left; exists CSD_P1; split; [cbn; tauto | left; unfold CSD_P1, CSD_PERS1, CSD_PERS0; cbn; lia])) as GB1.
    pose proof (RA 670248 ltac:(do 6 right; left; exists CSD_D1; split; [cbn; tauto | left; unfold CSD_D1, CSD_PC; cbn; lia])) as GD0.
    pose proof (RA 670249 ltac:(do 6 right; left; exists CSD_D1; split; [cbn; tauto | left; unfold CSD_D1, CSD_PC; cbn; lia])) as GD1.
    step. step. brF false. step. brF false. step. step. brF false.
    step. step. step. step. step. brF false.
    step. step. step. step. step. step. brF false. step. step. brF false.
    step. step. step. step. step. brF false.
    step. step. step. step. step. step. brF false. step. step. brF false.
    apply TAIL.
Qed.

End Pieces.
