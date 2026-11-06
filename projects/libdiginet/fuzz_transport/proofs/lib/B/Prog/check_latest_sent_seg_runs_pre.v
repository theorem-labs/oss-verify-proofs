(* check_latest_sent_seg_runs_pre: the two runs of one loop round of the ASan image-B walk of check_latest_sent that
   lead to its two calls: cls_run_pre (the loop head 0x84974 to the tagged_of entry 0x846a0; the `jal` at 0x84998)
   and cls_run_mid (tagged_of's return 0x8499c to the bcmp entry 0x42d34; the `jal` at 0x849f0). Neither stores.
   Shapes in check_latest_sent_seg_runs.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  AsanKA AsanKAProof TWorldB check_state_wake_c check_latest_sent_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  check_latest_sent_seg_model check_latest_sent_seg_runs.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The two runs join the two paths of each instrumented check at the instruction after its `bnez`, as image A's
   cls_run_pre does: clsr_pre_join r pc J states the goal at pc for every value of register r (the one register the
   check's handler writes), clsr_pre_close r J closes a path that reached pc. clsr_pre_ul turns every
   bv_unsigned (Z_to_bv 64 e) of the walk into e. *)
Local Ltac clsr_pre_join r pc J :=
  lazymatch goal with |- ExecF.evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    assert (J : forall y : word, ExecF.evtF segs RNG Q (MS (tset p y R) F (Z_to_bv 64 pc) fc rv m ro))
  end.
Local Ltac clsr_pre_close r J := let w := reg_val r in exact (J w).
Local Ltac clsr_pre_ul :=
  rewrite ?cls_shr3, ?cls_wrap64_7, ?land7;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      rewrite (unsigned_lit e)
        by (first [lia | split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia])
  end;
  rewrite ?cls_shr3, ?land7.

(* `seqz` of a nonzero address *)
Lemma clsr_pre_seqz : forall x, 0 < x < 2 ^ 64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 0.
Proof.
  intros x Hx. unfold v_sltiu. rewrite (unsigned_lit x) by lia. rewrite cls_wrap64_1.
  rewrite (proj2 (Z.ltb_ge x 1) ltac:(lia)). reflexivity.
Qed.

(* the UBSan alignment test `andi a0,a0,3` of t = g_cmd + 40 s *)
Lemma clsr_pre_land3 : forall s, Z.land (6180992 + 40 * s) 3 = 0.
Proof.
  intros s. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  replace (6180992 + 40 * s) with ((1545248 + 10 * s) * 4) by lia. apply Z.mod_mul. lia.
Qed.

(* ---- the loop head to the tagged_of entry, 0x84974 .. 0x84998 ---- *)
Lemma cls_run_pre : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (spv dp bp len pos : Z) (j0 : list byte)
    (ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110 : word)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 gp tp : word),
  cls_bounds spv dp bp len -> cls_rng RNG spv dp ->
  0 <= pos < len ->
  rw_cells rsegs m spv (cls_fr j0 dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
  length j0 = 8%nat ->
  ExecF.evtF rsegs RNG Q
    (MS (cls_regs_tag x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x20 x24 x28 x29 x30 x31 gp tp spv dp bp len pos)
        F (Z_to_bv 64 542368) fc None m (seg_rom rsegs)) ->
  ExecF.evtF rsegs RNG Q
    (MS (cls_regs_head x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 gp tp
           spv dp bp len pos)
        F (Z_to_bv 64 543092) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc spv dp bp len pos j0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x28 x29 x30 x31 gp tp
    HB HR Hpos FR Hj0 K.
  unfold cls_bounds in HB. unfold cls_rng in HR.
  destruct HB as (Hsp0 & Hsp1 & Hdp0 & Hdp1 & Hbp0 & Hlen0 & Hbp1 & Hdp4).
  destruct HR as (Rfr & Rk1 & Rk2 & Rdp & Rdps & Rks & Rcmd & Rcsh & Rq & Rqsh & Rnq).
  clear Rk1 Rk2 Rdp Rdps Rks Rcmd Rcsh Rq Rqsh Rnq.
  unfold cls_fr in FR. unfold cls_regs_head. unfold cls_regs_tag in K.
  (* 0x84974 add s5,s2,s9: s5 = bp + pos, below 2^64 *)
  step. clsr_pre_ul.
  (* 0x84978 bltu s5,s2: the UBSan pointer-overflow trap, not taken *)
  step. rewrite cls_ltu_lit by lia. rewrite (proj2 (Z.ltb_ge (bp + pos) bp) ltac:(lia)). cbv iota.
  (* 0x8497c seqz a0,s5: a0 = 0, as 0 < bp + pos *)
  step. rewrite (clsr_pre_seqz (bp + pos)) by lia.
  (* 0x84980 ld a1,40(sp): frame slot 5 = (bp <> 0) = 1 *)
  step.
  (* 0x84984 xor a0,a1,a0: a0 = 1; 0x84988 beqz a0: the UBSan trap, not taken *)
  step.
  step. rewrite cls_eqb_lit by lia. change (1 =? 0) with false. cbv iota.
  (* 0x8498c sub s6,s1,s9: s6 = len - pos *)
  step. clsr_pre_ul.
  (* 0x84990 mv a0,s5; 0x84994 mv a1,s6 *)
  step. clsr_pre_ul.
  step. clsr_pre_ul.
  (* 0x84998 jal tagged_of (0x846a0), ra = 0x8499c *)
  step.
  exact K.
Qed.

(* ---- tagged_of's return to the bcmp entry, 0x8499c .. 0x849f0 ---- *)
Lemma cls_run_mid : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (spv dp bp len pos s : Z) (Bc body : list byte) (v : word) (j0 : list byte)
    (ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110 : word)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x24 x28 x29 x30 x31 gp tp : word),
  cls_bounds spv dp bp len -> cls_rng RNG spv dp ->
  Z.of_nat (length Bc) = TW.W_LEN ->
  0 <= pos < len ->
  0 <= s < TC.CMDS_MAX ->
  TW.Cmd_st Bc s = TC.PENDING ->
  TW.Cmd_len Bc s <= len - pos ->
  rw_cells rsegs m spv (cls_fr j0 dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
  length j0 = 8%nat ->
  cls_mem m Bc body dp bp len v ->
  ExecF.evtF rsegs RNG Q
    (MS (cls_regs_call x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp
           spv dp bp len pos s (TW.Cmd_len Bc s))
        F (Z_to_bv 64 273716) fc None m (seg_rom rsegs)) ->
  ExecF.evtF rsegs RNG Q
    (MS (cls_regs_tret x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x24 x28 x29 x30 x31 gp tp
           spv dp bp len pos (6180992 + 40 * s))
        F (Z_to_bv 64 543132) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc spv dp bp len pos s Bc body v j0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x24 x28 x29 x30 x31 gp tp
    HB HR HLc Hpos Hs HST HTL FR Hj0 HM K.
  unfold cls_bounds in HB. unfold cls_rng in HR. unfold cls_mem in HM.
  destruct HB as (Hsp0 & Hsp1 & Hdp0 & Hdp1 & Hbp0 & Hlen0 & Hbp1 & Hdp4).
  destruct HR as (Rfr & Rk1 & Rk2 & Rdp & Rdps & Rks & Rcmd & Rcsh & Rq & Rqsh & Rnq).
  destruct HM as (HW & HDP & HBY & ADC & ADQ & ADD & ADB & HWOK).
  clear Rk1 Rk2 Rdp Rdps Rks Rq Rqsh Rnq HDP HBY ADQ ADD ADB HWOK HLc.
  unfold cls_fr in FR. unfold cls_regs_tret. unfold cls_regs_call in K.
  unfold TC.CMDS_MAX in Hs.
  pose proof (cls_cmd_len_range Bc s) as Rtl.
  pose proof (cls_cmd_st_range Bc s) as Rst.
  (* 0x8499c beqz a0: the abort path, not taken (t <> 0) *)
  step. rewrite cls_eqb0 by lia. rewrite (proj2 (Z.eqb_neq (6180992 + 40 * s) 0) ltac:(lia)). cbv iota.
  (* 0x849a0 mv s3,a0 *)
  step. clsr_pre_ul.
  (* 0x849a4 andi a0,a0,3; 0x849a8 bnez a0: the UBSan alignment trap, not taken (t is 4-aligned) *)
  step. clsr_pre_ul. rewrite clsr_pre_land3.
  step. rewrite cls_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  (* 0x849ac - 0x849b8: s8 = the shadow address of t; the check of the 4-byte load at t; its handler 0x84b00
     writes a1 *)
  destruct (cls_sh_load m 6180992 40960 (40 * s) 4 ADC ltac:(lia) ltac:(lia) ltac:(lia)) as (k3 & MK3 & SK3).
  unfold ASAN_K in MK3. pose proof (rd1 m _ _ MK3) as RD.
  pose proof (cls_shc RNG (40 * s) Rcsh ltac:(lia)) as RK. unfold ASAN_K in RK.
  step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
  clear RD RK MK3.
  clsr_pre_join 11 0x849bc J1.
  2: { step. rewrite sxb_eq0. destruct SK3 as [C|[C Cu]].
       - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. clsr_pre_close 11 J1.
       - rewrite (proj2 (Z.eqb_neq (bv_signed k3) 0) ltac:(lia)). cbn [negb]. cbv iota.
         (* 0x84b00 andi a1,s3,7; 0x84b04 addi a1,a1,3; 0x84b08 bge a1,a0 (the report), not taken;
            0x84b0c j 0x849bc *)
         step. clsr_pre_ul. step. clsr_pre_ul. step.
         rewrite (cls_lts_lit ((6180992 + 40 * s) mod 8 + 3) k3) by lia.
         rewrite (proj2 (Z.ltb_lt ((6180992 + 40 * s) mod 8 + 3) (bv_signed k3)) ltac:(lia)).
         cbn [negb]. cbv iota.
         step. clsr_pre_close 11 J1. }
  intros y11. cbv beta iota delta [tset]. clear SK3.
  (* 0x849bc - 0x849c4: t->st = PENDING, the abort path not taken *)
  pose proof (cls_rd m Bc TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s) 4 HW TMAP_B_g_cmd ltac:(lia)
    ltac:(unfold TW.SZ_g_cmd; lia)) as RD.
  unfold TB_g_cmd in RD.
  replace (TW.OFF_g_cmd + 40 * s) with (TW.A_Cmd_st s) in RD by (unfold TW.A_Cmd_st; lia).
  step. clear RD. rewrite lw_world. change (TW.s32_at Bc (TW.A_Cmd_st s)) with (TW.Cmd_st Bc s).
  rewrite HST. unfold TC.PENDING.
  step. step. rewrite cls_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  (* 0x849c8 - 0x849d8: a0 = t + 36; the check of the 1-byte load at it; its handler 0x84b10 writes a2 *)
  step. clsr_pre_ul.
  destruct (cls_sh_load m 6180992 40960 (40 * s + 36) 1 ADC ltac:(lia) ltac:(lia) ltac:(lia))
    as (k4 & MK4 & SK4).
  replace (6180992 + (40 * s + 36)) with (6180992 + 40 * s + 36) in MK4, SK4 by lia.
  unfold ASAN_K in MK4. pose proof (rd1 m _ _ MK4) as RD.
  pose proof (cls_shc RNG (40 * s + 36) Rcsh ltac:(lia)) as RK. unfold ASAN_K in RK.
  replace (6180992 + (40 * s + 36)) with (6180992 + 40 * s + 36) in RK by lia.
  step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
  clear RD RK MK4.
  clsr_pre_join 12 0x849dc J2.
  2: { step. rewrite sxb_eq0. destruct SK4 as [C|[C Cu]].
       - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. clsr_pre_close 12 J2.
       - rewrite (proj2 (Z.eqb_neq (bv_signed k4) 0) ltac:(lia)). cbn [negb]. cbv iota.
         (* 0x84b10 andi a2,a0,7; 0x84b14 bge a2,a1 (the report), not taken; 0x84b18 j 0x849dc *)
         step. clsr_pre_ul. step.
         rewrite (cls_lts_lit ((6180992 + 40 * s + 36) mod 8) k4) by lia.
         rewrite (proj2 (Z.ltb_lt ((6180992 + 40 * s + 36) mod 8) (bv_signed k4)) ltac:(lia)).
         cbn [negb]. cbv iota.
         step. clsr_pre_close 12 J2. }
  intros y12. cbv beta iota delta [tset]. clear SK4.
  (* 0x849dc: s4 = t->len *)
  pose proof (cls_rd m Bc TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s + 36) 1 HW TMAP_B_g_cmd ltac:(lia)
    ltac:(unfold TW.SZ_g_cmd; lia)) as RD.
  unfold TB_g_cmd in RD.
  replace (0x5e5080 + (40 * s + 36)) with (6180992 + 40 * s + 36) in RD by lia.
  replace (TW.OFF_g_cmd + (40 * s + 36)) with (TW.A_Cmd_len s) in RD by (unfold TW.A_Cmd_len; lia).
  step. clear RD. rewrite lbu_world. change (TW.u_at Bc (TW.A_Cmd_len s) 1) with (TW.Cmd_len Bc s).
  (* 0x849e0 bltu s6,s4: the abort path len - pos < t->len, not taken *)
  step. rewrite cls_ltu_lit by lia. rewrite (proj2 (Z.ltb_ge _ _) HTL). cbn [negb]. cbv iota.
  (* 0x849e4 - 0x849ec: a1 = t + 12, a0 = bp + pos, a2 = t->len; 0x849f0 jal bcmp (0x42d34), ra = 0x849f4 *)
  step. clsr_pre_ul. step. clsr_pre_ul. step. clsr_pre_ul.
  step.
  exact K.
Qed.
