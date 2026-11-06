From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes Image.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require Import memset_c memcpy_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import TImgP WMem TContract io_send_c
  io_send_keep io_send_sf io_send_data
  check_sent_frame_c check_ack_frame_c check_latest_control_c check_inflight_retry_c check_state_wake_c
  check_inflight_new_c check_latest_frame_c check_keepalive_due_c check_latest_sent_c check_latest_display_c.
Import ListNotations.
Open Scope Z_scope.

Theorem io_send_holds :
  memset_contract -> memcpy_contract ->
  check_sent_frame_contract -> check_ack_frame_contract -> check_latest_control_contract ->
  check_inflight_retry_contract -> check_state_wake_contract -> check_inflight_new_contract ->
  check_latest_frame_contract -> check_keepalive_due_contract -> check_latest_sent_contract ->
  check_latest_display_contract -> io_send_contract.
Proof.
  intros MEMSET MEMCPY CSF CAF CLC CIR CSW CIN CLF CKD CLS CLD.
  unfold check_sent_frame_contract, check_sent_frame_ENTRY, check_sent_frame_FRAME in CSF.
  unfold check_ack_frame_contract, check_ack_frame_ENTRY, check_ack_frame_FRAME in CAF.
  unfold check_latest_control_contract, check_latest_control_ENTRY, check_latest_control_FRAME in CLC.
  unfold check_inflight_retry_contract, check_inflight_retry_ENTRY, check_inflight_retry_FRAME in CIR.
  unfold check_state_wake_contract, check_state_wake_ENTRY, check_state_wake_FRAME in CSW.
  unfold check_inflight_new_contract, check_inflight_new_ENTRY, check_inflight_new_FRAME in CIN.
  unfold check_latest_frame_contract, check_latest_frame_ENTRY, check_latest_frame_FRAME in CLF.
  unfold check_keepalive_due_contract, check_keepalive_due_ENTRY, check_keepalive_due_FRAME in CKD.
  unfold check_latest_sent_contract, check_latest_sent_ENTRY, check_latest_sent_FRAME in CLS.
  unfold check_latest_display_contract, check_latest_display_ENTRY, check_latest_display_FRAME in CLD.
  unfold io_send_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo B B' p r frame Ea1 Ea2 Hp HFR HFA HOW HFN Hsp ST HLO HWS MI WM HM.
  subst a1 a2.
  unfold io_send_ENTRY, io_send_FRAME in *.
  unfold w_off_stack in HWS. unfold off_window in HOW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bytes_at_bound rsegs m p frame HFR) as Bfr.
  destruct ST as (Hlo0 & Hhi0 & STb). assert (ST : stk rsegs m lo (bv_unsigned sp)) by (split; [lia|split; [lia|exact STb]]).
  clear Hhi0 STb.
  assert (HWS' : 0x32790 + 65616 <= bv_unsigned sp - 304) by (unfold W_BASE_PLAIN, W_LEN in HWS; lia).
  unfold io_send_frame_at, off_world, W_BASE_PLAIN, W_LEN, OFF_g_s, SZ_g_s in HFA.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -192)) = bv_unsigned sp + -192)
    by (rewrite unsigned_lit by lia; reflexivity).
  assert (EA0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176)
    by (rewrite unsigned_lit by lia; reflexivity).
  assert (EA2 : bv_unsigned (Z_to_bv 64 80) = 80) by (rewrite unsigned_lit by lia; reflexivity).
  (* the model: the parse succeeds, so every abort branch of the parse is impossible *)
  assert (HCSF : check_sent_frame_m (set_g_fail_next B 0) frame <> None).
  { intros E. unfold io_send_m in HM. cbv zeta beta in HM. rewrite E in HM. discriminate. }
  assert (HOK : sf_code (rf frame) = SPEC_OK).
  { destruct (Z.eqb_spec (sf_code (rf frame)) SPEC_OK) as [E|NE]; [exact E|].
    exfalso. apply HCSF. unfold check_sent_frame_m.
    replace (sf_code (rf frame) =? SPEC_OK) with false by (symmetry; apply Z.eqb_neq; exact NE).
    reflexivity. }
  assert (HBB : holds_body (zs frame) frame) by apply holds_body_map.
  destruct (spec_read_frame_fr (zs frame) frame HBB) as (HC & HFLD).
  change (spec_read_frame (zs frame) (Z.of_nat (length frame))) with (rf frame) in HC, HFLD.
  assert (HFC : fr_code frame = 0) by (rewrite <- HC; exact HOK).
  destruct (fr_code_ok frame HFC) as (HL30 & HET & HNB1 & HNB2).
  specialize (HFLD HFC). cbv zeta in HFLD.
  destruct HFLD as (Fdst & Fsrc & Fet & Fnb & Fsum & Fsend & Fack & Fretry & Fcmd & Fncmds & Fbody & Fblen & Fpad & Fbsum).
  (* the model: check_sent_frame, then the switch on f.cmd, then the return value *)
  unfold io_send_m in HM. cbv zeta beta in HM.
  destruct (check_sent_frame_m (set_g_fail_next B 0) frame) as [[B1 []]|] eqn:HCS; [|discriminate HM].
  lazymatch type of HM with
  | match ?E with _ => _ end = _ => destruct E as [[B2 []]|] eqn:HSW; [|discriminate HM]
  end.
  injection HM as HB2 HRV. subst B2.
  (* check_sent_frame's length clause (:417) gives len = max (60, 30 + body_len): the frame is at least 60
     bytes, so no pointer the parse builds into it wraps *)
  assert (HLEN60 : 60 <= Z.of_nat (length frame)).
  { unfold check_sent_frame_m in HCS. cbv zeta beta in HCS.
    lazymatch type of HCS with
    | (if ?c then _ else _) = _ => destruct c eqn:E1; [discriminate HCS|]
    end.
    lazymatch type of HCS with
    | (if ?c then _ else _) = _ => destruct c eqn:E2; [discriminate HCS|]
    end.
    apply orb_false_iff in E2 as [E2a _]. apply orb_false_iff in E2a as [E2b _].
    apply negb_false_iff, Z.eqb_eq in E2b.
    rewrite E2b.
    destruct (SPEC_BODY_AT + sf_body_len (rf frame) <? SPEC_MIN_FRAME) eqn:EN;
      [ cbv [SPEC_MIN_FRAME]; lia
      | apply Z.ltb_ge in EN; cbv [SPEC_MIN_FRAME SPEC_BODY_AT] in EN |- *; lia ]. }
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  wk_facts.
  carve_frame 192%nat ST.
  destruct (rwc_split m (bv_unsigned sp + -192) (bv_unsigned sp + -180) junk 192 12 180 FR
              ltac:(reflexivity) ltac:(lia)) as (j0 & jr1 & FR0 & FRr1).
  destruct (rwc_split m (bv_unsigned sp + -180) (bv_unsigned sp + -176) jr1 180 4 176 FRr1
              ltac:(reflexivity) ltac:(lia)) as (jD & jr2 & FRD & FRr2).
  destruct (rwc_split m (bv_unsigned sp + -176) (bv_unsigned sp + -96) jr2 176 80 96 FRr2
              ltac:(reflexivity) ltac:(lia)) as (jF & jS & FRF & FRS).
  clear FR FRr1 FRr2.
  (* ---- 14824-14864: the epilogue, from every path that returns; the 4 bytes at sp + 12 (sp' = sp - 192) are
     check_latest_sent's display out cell on the DATA path, so their contents are any jd ---- *)
  assert (EPI : forall (mm : word -> option byte) (cs : list cell) (jd : list byte)
                  (vra vt0 vt1 vt2 vs0 vs1 va0 va1 va2 va3 va4 va5 va6 va7
                   vs2 vs3 vs4 vs6 vs7 vs8 vs9 vs10 vt3 vt4 vt5 vt6 : word),
    munch [(bv_unsigned sp - 304, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mm ->
    wmono rsegs m mm -> mem_inv rsegs mm -> stk rsegs mm lo (bv_unsigned sp + -192) ->
    wmem rsegs mm B' ->
    rw_cells rsegs mm (bv_unsigned sp + -192) [CB 12 j0] ->
    rw_cells rsegs mm (bv_unsigned sp + -180) [CB 4 jd] ->
    rw_cells rsegs mm (bv_unsigned sp + -176) cs -> cells_size cs = 80%nat ->
    rw_cells rsegs mm (bv_unsigned sp + -96)
      [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt rsegs QQ
      (MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp vt0 vt1 vt2 vs0 vs1 va0 va1 va2 va3 va4 va5 va6 va7
                vs2 vs3 vs4 (Z_to_bv 64 (g_fail_next B)) vs6 vs7 vs8 vs9 vs10 s11 vt3 vt4 vt5 vt6)
          F (Z_to_bv 64 84012) fc None mm (seg_rom rsegs))).
  { intros mm cs jd vra vt0 vt1 vt2 vs0 vs1 va0 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4 vs6 vs7 vs8 vs9 vs10
      vt3 vt4 vt5 vt6 MUm WMm MIm STm WMEm FR0m FRDm FRFm FRFsz FRSm.
    assert (FB : g_fail_next B = 0 \/ g_fail_next B = 1).
    { pose proof (u_at_range B OFF_g_fail_next 1) as HU. change (8 * Z.of_nat 1) with 8 in HU.
      change (u_at B OFF_g_fail_next 1) with (g_fail_next B) in HU. lia. }
    destruct FB as [FB0|FB0].
    all: rewrite FB0 in HRV |- *.
    all: unfold EIO in HRV.
    all: cbn in HRV.
    all: do 3 step.
    all: do 12 step.
    all: assert (ST1 : stk rsegs mm lo (bv_unsigned sp + -180))
        by (replace (bv_unsigned sp + -180) with (bv_unsigned sp + -192 + Z.of_nat (cells_size [CB 12 j0]))
              by (cbn [cells_size csize]; lia);
            exact (stk_release rsegs mm lo (bv_unsigned sp + -192) [CB 12 j0] STm FR0m ltac:(lia))).
    all: assert (ST2 : stk rsegs mm lo (bv_unsigned sp + -176))
        by (replace (bv_unsigned sp + -176) with (bv_unsigned sp + -180 + Z.of_nat (cells_size [CB 4 jd]))
              by (cbn [cells_size csize]; lia);
            exact (stk_release rsegs mm lo (bv_unsigned sp + -180) [CB 4 jd] ST1 FRDm ltac:(lia))).
    all: assert (ST3 : stk rsegs mm lo (bv_unsigned sp + -96))
        by (replace (bv_unsigned sp + -96) with (bv_unsigned sp + -176 + Z.of_nat (cells_size cs))
              by (rewrite FRFsz; lia);
            exact (stk_release rsegs mm lo (bv_unsigned sp + -176) cs ST2 FRFm ltac:(lia))).
    all: assert (ST4 : stk rsegs mm lo (bv_unsigned sp))
        by (replace (bv_unsigned sp)
              with (bv_unsigned sp + -96 +
                    Z.of_nat (cells_size [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1;
                                          C8 s0; C8 ra]))
              by (cbn [cells_size csize]; lia);
            exact (stk_release rsegs mm lo (bv_unsigned sp + -96) _ ST3 FRSm ltac:(lia))).
    all: do 2 step.
    all: try rewrite (zbv_cong 18446744073709551611 (- (5)) ltac:(reflexivity)).
    all: apply evt_done; unfold QQ; rewrite <- HRV; do 15 eexists.
    all: split; [reflexivity|].
    all: split; [exact MUm|]; split; [exact WMm|]; split; [exact MIm|]; split; [exact ST4|]; exact WMEm. }
  (* ---- 147e0-14820: the frame in flight, from the E2 path and from the DATA path ---- *)
  assert (FLY : forall (mm : word -> option byte) (cs : list cell) (jd Bx : list byte) (flen : Z)
                  (vra vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4 vs9 vs10 vt3 vt4 vt5 vt6 : word),
    munch [(bv_unsigned sp - 304, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m mm ->
    wmono rsegs m mm -> mem_inv rsegs mm -> stk rsegs mm lo (bv_unsigned sp + -192) ->
    wmem rsegs mm Bx ->
    bytes_at rsegs mm p frame ->
    flen = (if Z.of_nat (length frame) <? 1514 then Z.of_nat (length frame) else 1514) ->
    B' = set_M_fly_frame
           (set_M_fly_len
              (set_M_fly_sent
                 (set_M_fly_retries
                    (set_M_fly_counter (set_M_fly_cmd (set_M_fly_on Bx 1) (sf_cmd (rf frame)))
                       (sf_send (rf frame))) 0) (g_now Bx)) flen)
           (firstn (Z.to_nat flen) frame) ->
    rw_cells rsegs mm (bv_unsigned sp + -192) [CB 12 j0] ->
    rw_cells rsegs mm (bv_unsigned sp + -180) [CB 4 jd] ->
    rw_cells rsegs mm (bv_unsigned sp + -176) cs -> cells_size cs = 80%nat ->
    rw_cells rsegs mm (bv_unsigned sp + -96)
      [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt rsegs QQ
      (MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp vt0 vt1 vt2
                (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p)
                va0 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4
                (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 271704)
                (Z_to_bv 64 (sf_send (rf frame))) (Z_to_bv 64 (sf_cmd (rf frame)))
                vs9 vs10 s11 vt3 vt4 vt5 vt6)
          F (Z_to_bv 64 83944) fc None mm (seg_rom rsegs))).
  { intros mm cs jd Bx flen vra vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vs2 vs3 vs4 vs9 vs10 vt3 vt4 vt5 vt6
      MUm WMm MIm STm WMEm HFRm HFLEN HBF FR0m FRDm FRFm FRFsz FRSm.
    assert (RFL : 0 <= flen <= 1514)
      by (rewrite HFLEN; destruct (Z.ltb_spec (Z.of_nat (length frame)) 1514); lia).
    assert (RFL2 : flen <= Z.of_nat (length frame))
      by (rewrite HFLEN; destruct (Z.ltb_spec (Z.of_nat (length frame)) 1514); lia).
    (* 147e0-147ec: a0 = &M, a1 = 1, a2 = g_now *)
    do 4 step.
    change (u_at Bx 65000 8) with (g_now Bx).
    (* 147f0-14804: M.fly.on, .cmd, .counter, .retries, .sent *)
    do 6 step.
    (* 14808: bltu s0,1514 ; 1480c: li s0,1514 *)
    step.
    if_cases EL; cbv iota;
      [ replace (Z_to_bv 64 (Z.of_nat (length frame))) with (Z_to_bv 64 flen)
          by (f_equal; rewrite HFLEN; zify_cond EL; rewrite ?unsigned_lit_wrap in EL;
              replace (Z.of_nat (length frame) <? 1514) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity)
      | step;
        replace (Z_to_bv 64 1514) with (Z_to_bv 64 flen)
          by (f_equal; rewrite HFLEN; zify_cond EL; rewrite ?unsigned_lit_wrap in EL;
              replace (Z.of_nat (length frame) <? 1514) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity) ].
    all: do 5 step.
    all: assert (EFL : bv_unsigned (Z_to_bv 64 flen) = flen) by (apply unsigned_lit; lia).
    all: assert (EDST : bv_unsigned (Z_to_bv 64 206856) = 206856) by (apply unsigned_lit; lia).
    all: assert (EPP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
    all: lazymatch goal with
         | H : rw_cells rsegs ?mz W_BASE_PLAIN [CB (Z.to_nat W_LEN) ?BB] |- _ =>
             assert (DST : rw_cells rsegs mz 206856 [CB (Z.to_nat flen) (sub BB 120 (Z.to_nat flen))])
               by (apply (wm_piece rsegs W_BASE_PLAIN mz BB 120);
                   [ exact H | reflexivity | lia | lia | unfold W_LEN; lia ])
         end.
    all: eapply evt_cut;
         [ eapply MEMCPY with (src := sub frame 0 (Z.to_nat flen));
             [ rewrite ?EPP; apply (bytes_at_sub' _ p frame 0 (Z.to_nat flen) p);
               [ exact HFRm | lia | lia | lia ]
             | rewrite EFL; apply length_sub; lia
             | rewrite EDST, EFL; exact DST
             | rewrite EPP, EDST, EFL; unfold W_BASE_PLAIN, W_LEN in *; lia
             | eassumption ]
         | ].
    all: intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mz2 &
                     Eqz & MUz & WMz & MIz & DSTz & SRCz).
    all: subst ms'.
    all: rewrite EDST, EFL in MUz, DSTz.
    all: lazymatch goal with
         | H : rw_cells rsegs ?mz W_BASE_PLAIN [CB (Z.to_nat W_LEN) ?BB] |- _ =>
             assert (WMF : wmem rsegs mz2 (upd BB 120 (sub frame 0 (Z.to_nat flen))))
               by (apply (wm_fill rsegs W_BASE_PLAIN mz mz2 BB 206856 120 flen
                            (sub frame 0 (Z.to_nat flen)) H MUz WMz DSTz);
                   [ reflexivity | lia | lia | unfold W_LEN; lia ]);
             clear H
         end.
    all: lazymatch type of MUz with
         | munch _ ?mz _ =>
             assert (STz : stk rsegs mz2 lo (bv_unsigned sp + -192))
               by (apply (stk_after_copy mz mz2 lo (bv_unsigned sp + -192) 206856 flen
                            (sub frame 0 (Z.to_nat flen))); [ exact STm | exact MUz | exact WMz | exact DSTz
                                                            | lia | lia | lia ]);
             transport_after_call rsegs mz mz2 MUz WMz
         end.
    all: rewrite (ret_pc_even 84012) by (first [lia | reflexivity]).
    all: eapply EPI;
         [ exact MUm | exact WMm | exact MIz | exact STz
         | rewrite HBF; exact WMF
         | exact FR0m | exact FRDm | exact FRFm | exact FRFsz | exact FRSm ]. }
  (* 144e4-14524: the prologue, s0 = len, s1 = frame, s6 = &g_fail_next *)
  do 17 step.
  (* 14528: lbu s5,0(s6) -- g_fail_next *)
  step.
  change (u_at B 64968 1) with (g_fail_next B).
  (* 1452c: sb zero,0(s6) -- g_fail_next = 0 *)
  step.
  lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WM1 end.
  change (upd B 64968 (put 1 0)) with (set_g_fail_next B 0) in WM1.
  (* 14530-1453c: memset (&f, 0, 80) *)
  do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  eapply evt_cut.
  { eapply MEMSET with (junk := jF).
    - rewrite EA0, EA2. exact FRF.
    - exact MI. }
  post_call rsegs mA.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mB end.
  rewrite EA0, EA2 in POST.
  change (Z.to_nat 80) with 80%nat in POST.
  change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (b8 0) in POST.
  (* 14540: li a0,30 ; 14544: bgeu s0,a0 -> 14550 (the parse is OK, so len >= 30) *)
  do 2 step.
  rewrite ltu_lit by lia.
  replace (Z.of_nat (length frame) <? 30) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [negb].
  pose proof (at8_range frame 12). pose proof (at8_range frame 13).
  pose proof (at8_range frame 14). pose proof (at8_range frame 15).
  assert (RNB : 0 <= fr_numbytes frame < 65536)
    by (unfold fr_numbytes, be16; lia).
  (* 14550: lbu a0,12(s1) ; 14554: lbu a1,13(s1) : the EtherType *)
  lbuf HFR 12 12%nat.
  lbuf HFR 13 13%nat.
  (* 14558: slli a0,a0,8 ; 1455c: or a0,a0,a1 ; 14560-14564: a1 = 0x885f *)
  do 4 step.
  rewrite (unsigned_lit (at8 frame 12)) by lia.
  rewrite (unsigned_lit (Z.shiftl (at8 frame 12) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (unsigned_lit (at8 frame 13)) by lia.
  replace (Z.lor (Z.shiftl (at8 frame 12) 8) (at8 frame 13)) with 34911
    by (rewrite <- HET; unfold fr_ethertype, be16; rewrite Z.lor_comm, lor_shiftl8_add by lia; lia).
  (* 14568: sh a0,40(sp) -- f.ethertype *)
  step.
  (* 1456c: bne a0,a1 -> 146b0 ; not taken *)
  step.
  rewrite eqb_lit by lia.
  replace (34911 =? 34911) with true by reflexivity.
  cbn [negb].
  (* 14570: lbu a0,14(s1) ; 14574: lbu a1,15(s1) : numbytes *)
  lbuf HFR 14 14%nat.
  lbuf HFR 15 15%nat.
  (* 14578: li a3,16 ; 1457c: slli ; 14580: or *)
  do 3 step.
  rewrite (unsigned_lit (at8 frame 14)) by lia.
  rewrite (unsigned_lit (Z.shiftl (at8 frame 14) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (unsigned_lit (at8 frame 15)) by lia.
  replace (Z.lor (Z.shiftl (at8 frame 14) 8) (at8 frame 15)) with (fr_numbytes frame)
    by (unfold fr_numbytes, be16; rewrite Z.lor_comm, lor_shiftl8_add by lia; lia).
  (* 14584: sh a0,42(sp) -- f.numbytes ; 14588: li a2,-4 ; 1458c: bltu a0,16 (not taken) *)
  do 3 step.
  rewrite ltu_lit by lia.
  replace (fr_numbytes frame <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [negb].
  (* 14590: addi a1,s0,-14 ; 14594: bltu a1,a0 (not taken) *)
  step.
  rewrite ?(unsigned_lit (Z.of_nat (length frame))) by lia.
  step.
  rewrite ltu_lit by lia.
  replace (Z.of_nat (length frame) + -14 <? fr_numbytes frame) with false
    by (symmetry; apply Z.ltb_ge; lia).
  cbn [negb].
  (* ---- 14598-1461c: the OK path reads the header fields ---- *)
  pose proof (at8_range frame 16). pose proof (at8_range frame 17).
  pose proof (at8_range frame 18). pose proof (at8_range frame 19).
  pose proof (at8_range frame 20). pose proof (at8_range frame 21).
  pose proof (at8_range frame 22). pose proof (at8_range frame 23).
  pose proof (at8_range frame 24). pose proof (at8_range frame 25).
  pose proof (at8_range frame 26). pose proof (at8_range frame 27).
  pose proof (at8_range frame 28). pose proof (at8_range frame 29).
  (* 14598: addi a2,s1,6 -- f.src *)
  step. rewrite ?(unsigned_lit p) by lia.
  (* 1459c-145b8: lbu of the header bytes 16..23 *)
  lbuf HFR 16 16%nat. lbuf HFR 17 17%nat. lbuf HFR 18 18%nat. lbuf HFR 19 19%nat.
  lbuf HFR 20 20%nat. lbuf HFR 21 21%nat. lbuf HFR 22 22%nat. lbuf HFR 23 23%nat.
  (* 145bc-145d0: the six shifts *)
  do 6 step. cleanz.
  (* 145d4: or a3,a3,a4 -- f.sum *)
  step. cleanz.
  replace (Z.lor (Z.shiftl (at8 frame 16) 8) (at8 frame 17)) with (fr_sum frame)
    by (unfold fr_sum, be16; rewrite lor_sh by lia; lia).
  (* 145d8: or a4,a6,a5 -- the high half of f.send *)
  step. cleanz.
  replace (Z.lor (Z.shiftl (at8 frame 19) 16) (Z.shiftl (at8 frame 18) 24))
    with (at8 frame 18 * 2 ^ 24 + at8 frame 19 * 2 ^ 16)
    by (rewrite Z.lor_comm; rewrite lor_sh by (rewrite ?Z.shiftl_mul_pow2 by lia; lia);
        rewrite ?Z.shiftl_mul_pow2 by lia; lia).
  (* 145dc: or a5,a7,t0 -- the low half of f.send *)
  step. cleanz.
  replace (Z.lor (Z.shiftl (at8 frame 20) 8) (at8 frame 21))
    with (at8 frame 20 * 2 ^ 8 + at8 frame 21) by (rewrite lor_sh by lia; lia).
  (* 145e0-145e8: lbu of bytes 24, 25, 26 *)
  lbuf HFR 24 24%nat. lbuf HFR 25 25%nat. lbuf HFR 26 26%nat.
  (* 145ec: or t1,t2,t1 -- the high half of f.ack *)
  step. cleanz.
  replace (Z.lor (Z.shiftl (at8 frame 23) 16) (Z.shiftl (at8 frame 22) 24))
    with (at8 frame 22 * 2 ^ 24 + at8 frame 23 * 2 ^ 16)
    by (rewrite Z.lor_comm; rewrite lor_sh by (rewrite ?Z.shiftl_mul_pow2 by lia; lia);
        rewrite ?Z.shiftl_mul_pow2 by lia; lia).
  (* 145f0: lbu t2,27(s1) *)
  lbuf HFR 27 27%nat.
  (* 145f4-145f8: slli a6,a6,8 ; slli t0,t0,8 *)
  do 2 step. cleanz.
  (* 145fc: or a6,a6,a7 -- the low half of f.ack *)
  step. cleanz.
  replace (Z.lor (Z.shiftl (at8 frame 24) 8) (at8 frame 25))
    with (at8 frame 24 * 2 ^ 8 + at8 frame 25) by (rewrite lor_sh by lia; lia).
  (* 14600: or s8,t0,t2 -- f.retry *)
  step. cleanz.
  replace (Z.lor (Z.shiftl (at8 frame 26) 8) (at8 frame 27)) with (fr_retry frame)
    by (unfold fr_retry, be16; rewrite lor_sh by lia; lia).
  (* 14604: lbu s10,28(s1) -- f.cmd ; 14608: lbu s4,29(s1) -- f.ncmds *)
  lbuf HFR 28 28%nat. lbuf HFR 29 29%nat.
  (* 1460c: or s7,a4,a5 -- f.send *)
  step. cleanz.
  replace (Z.lor (at8 frame 18 * 2 ^ 24 + at8 frame 19 * 2 ^ 16)
                 (at8 frame 20 * 2 ^ 8 + at8 frame 21)) with (fr_send frame)
    by (unfold fr_send, be32;
        replace (at8 frame 18 * 2 ^ 24 + at8 frame 19 * 2 ^ 16)
          with ((at8 frame 18 * 2 ^ 8 + at8 frame 19) * 2 ^ 16) by lia;
        rewrite lk_lor_mul_pow2 by lia; lia).
  (* 14610: addi s2,s1,30 -- f.body *)
  step. rewrite ?(unsigned_lit p) by lia.
  (* 14614: or a4,t1,a6 -- f.ack *)
  step. cleanz.
  replace (Z.lor (at8 frame 22 * 2 ^ 24 + at8 frame 23 * 2 ^ 16)
                 (at8 frame 24 * 2 ^ 8 + at8 frame 25)) with (fr_ack frame)
    by (unfold fr_ack, be32;
        replace (at8 frame 22 * 2 ^ 24 + at8 frame 23 * 2 ^ 16)
          with ((at8 frame 22 * 2 ^ 8 + at8 frame 23) * 2 ^ 16) by lia;
        rewrite lk_lor_mul_pow2 by lia; lia).
  (* 14618: addi s3,a0,-16 -- f.body_len *)
  step. rewrite ?(unsigned_lit (fr_numbytes frame)) by lia.
  replace (fr_numbytes frame + -16) with (fr_body_len frame) by (unfold fr_body_len; lia).
  (* 1461c: sub a1,a1,a0 -- f.pad_len *)
  step. rewrite ?(unsigned_lit (Z.of_nat (length frame) + -14)) by lia.
  rewrite ?(unsigned_lit (fr_numbytes frame)) by lia.
  replace (Z.of_nat (length frame) + -14 - fr_numbytes frame) with (fr_pad_len frame)
    by (unfold fr_pad_len, fr_body_len; lia).
  (* 14620-14634: the six wide stores into f *)
  do 6 step.
  (* 14638: sb s10,56(sp) -- f.cmd ; 1463c: sb s4,57(sp) -- f.ncmds *)
  step. step.
  (* 14640-14648: f.body, f.body_len, f.pad_len ; 1464c: li a1,0 *)
  do 4 step.
  (* 14650: beqz s3,14670 (body_len = 0 skips the body sum) *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
  assert (Rbl : 0 <= fr_body_len frame < 65536) by (unfold fr_body_len; lia).
  assert (BL30 : 30 + fr_body_len frame <= Z.of_nat (length frame)) by (unfold fr_body_len; lia).
  assert (SUMB : forall n : nat, 0 <= sum_bytes (sub frame 30 n) <= 255 * Z.of_nat n).
  { intros n. pose proof (sum_bytes_bound (sub frame 30 n)).
    pose proof (length_sub_le frame 30 n). lia. }
  (* the state at 14670, where the two paths meet: a0, a2, a3 and the untouched temporaries are free *)
  enough (CONT : forall (va0 va2 va3 vt3 vt4 vt5 vt6 : word),
    evt rsegs QQ
      (MS (mkR (Z_to_bv 64 83272) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp
               (Z_to_bv 64 (Z.shiftl (at8 frame 26) 8))
               (Z_to_bv 64 (at8 frame 22 * 2 ^ 24 + at8 frame 23 * 2 ^ 16))
               (Z_to_bv 64 (at8 frame 27))
               (Z_to_bv 64 (Z.of_nat (length frame)))
               (Z_to_bv 64 p)
               va0
               (Z_to_bv 64 (sum_bytes (sub frame 30 (Z.to_nat (fr_body_len frame)))))
               va2 va3
               (Z_to_bv 64 (fr_ack frame))
               (Z_to_bv 64 (at8 frame 20 * 2 ^ 8 + at8 frame 21))
               (Z_to_bv 64 (at8 frame 24 * 2 ^ 8 + at8 frame 25))
               (Z_to_bv 64 (at8 frame 25))
               (Z_to_bv 64 (p + 30))
               (Z_to_bv 64 (fr_body_len frame))
               (Z_to_bv 64 (fr_ncmds frame))
               (Z_to_bv 64 (g_fail_next B))
               (Z_to_bv 64 271704)
               (Z_to_bv 64 (fr_send frame))
               (Z_to_bv 64 (fr_retry frame))
               s9 (Z_to_bv 64 (fr_cmd frame)) s11 vt3 vt4 vt5 vt6)
          F (Z_to_bv 64 83576) fc None mS (seg_rom rsegs))).
  { step.
    if_cases EBL; cbv iota.
    - (* body_len = 0: the sum stays 0 *)
      zify_cond EBL. rewrite ?unsigned_lit_wrap in EBL.
      assert (BL0 : fr_body_len frame = 0) by lia.
      replace (Z_to_bv 64 0)
        with (Z_to_bv 64 (sum_bytes (sub frame 30 (Z.to_nat (fr_body_len frame)))))
        by (rewrite BL0; reflexivity).
      eapply CONT.
    - (* body_len > 0: the sum loop of 14660-1466c *)
      zify_cond EBL. rewrite ?unsigned_lit_wrap in EBL.
      assert (BLP : 0 < fr_body_len frame) by lia.
      (* 14654: add a0,a0,s1 ; 14658: addi a0,a0,14 ; 1465c: mv a2,s2 *)
      do 3 step.
      rewrite ?(unsigned_lit (fr_numbytes frame)) by lia.
      rewrite ?(unsigned_lit p) by lia.
      rewrite ?(unsigned_lit (fr_numbytes frame + p)) by lia.
      replace (fr_numbytes frame + p + 14) with (p + (30 + fr_body_len frame))
        by (unfold fr_body_len; lia).
      assert (LOOP : forall (k : nat) (j : Z) (va3 vt3 vt4 vt5 vt6 : word),
        Z.of_nat k = fr_body_len frame - j -> 0 <= j < fr_body_len frame ->
        evt rsegs QQ
          (MS (mkR (Z_to_bv 64 83272) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp
                   (Z_to_bv 64 (Z.shiftl (at8 frame 26) 8))
                   (Z_to_bv 64 (at8 frame 22 * 2 ^ 24 + at8 frame 23 * 2 ^ 16))
                   (Z_to_bv 64 (at8 frame 27))
                   (Z_to_bv 64 (Z.of_nat (length frame)))
                   (Z_to_bv 64 p)
                   (Z_to_bv 64 (p + (30 + fr_body_len frame)))
                   (Z_to_bv 64 (sum_bytes (sub frame 30 (Z.to_nat j))))
                   (Z_to_bv 64 (p + (30 + j))) va3
                   (Z_to_bv 64 (fr_ack frame))
                   (Z_to_bv 64 (at8 frame 20 * 2 ^ 8 + at8 frame 21))
                   (Z_to_bv 64 (at8 frame 24 * 2 ^ 8 + at8 frame 25))
                   (Z_to_bv 64 (at8 frame 25))
                   (Z_to_bv 64 (p + 30))
                   (Z_to_bv 64 (fr_body_len frame))
                   (Z_to_bv 64 (fr_ncmds frame))
                   (Z_to_bv 64 (g_fail_next B))
                   (Z_to_bv 64 271704)
                   (Z_to_bv 64 (fr_send frame))
                   (Z_to_bv 64 (fr_retry frame))
                   s9 (Z_to_bv 64 (fr_cmd frame)) s11 vt3 vt4 vt5 vt6)
              F (Z_to_bv 64 83560) fc None mS (seg_rom rsegs))).
      { induction k as [|k IH]; intros j va3 vt3 vt4 vt5 vt6 Hk Hj; [lia|].
        pose proof (SUMB (Z.to_nat j)) as SB1.
        pose proof (at8_range frame (30 + Z.to_nat j)) as RB1.
        (* 14660: lbu a3,0(a2) *)
        pose proof (rd_sub mS p frame (30 + j) 1 HFR ltac:(lia) ltac:(lia)) as RD.
        step. rewrite lbu_val by (apply length_sub; lia).
        rewrite (ble_sub1 frame (30 + j) (30 + Z.to_nat j)%nat ltac:(lia) ltac:(lia)). clear RD.
        (* 14664: addi a2,a2,1 ; 14668: add a1,a1,a3 *)
        do 2 step.
        rewrite ?(unsigned_lit (sum_bytes (sub frame 30 (Z.to_nat j)))) by lia.
        rewrite ?(unsigned_lit (at8 frame (30 + Z.to_nat j))) by lia.
        replace (sum_bytes (sub frame 30 (Z.to_nat j)) + at8 frame (30 + Z.to_nat j))
          with (sum_bytes (sub frame 30 (Z.to_nat (j + 1))))
          by (replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia;
              rewrite (sum_bytes_sub_succ frame 30 (Z.to_nat j)) by lia; reflexivity).
        replace (p + (30 + j) + 1) with (p + (30 + (j + 1))) by lia.
        (* 1466c: bne a2,a0 -> 14660 *)
        step.
        if_cases EJ; cbv iota.
        + assert (HJ : j + 1 < fr_body_len frame).
          { zify_cond EJ. rewrite ?unsigned_lit_wrap in EJ. lia. }
          apply (IH (j + 1)); lia.
        + assert (HJ : j + 1 = fr_body_len frame).
          { zify_cond EJ. rewrite ?unsigned_lit_wrap in EJ. lia. }
          rewrite HJ. eapply CONT. }
      apply (LOOP (Z.to_nat (fr_body_len frame)) 0); lia. }
  intros va0 va2 va3 vt3 vt4 vt5 vt6.
  (* 14670: sh a1,88(sp) -- f.body_sum ; the struct f is then the parse of the frame *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mT end.
  assert (SFC : sf_code (rf frame) = 0) by exact HOK.
  assert (HSFB : bytes_at rsegs mT (bv_unsigned sp + -176) (sf_bytes p (rf frame))).
  { lazymatch goal with H : rw_cells rsegs mT (bv_unsigned sp + -176) ?cs |- _ =>
      eapply bytes_at_ext; [ exact (rwc_bytes mT (bv_unsigned sp + -176) cs H) | ] end.
    unfold sf_bytes, sf_ptr.
    rewrite SFC, Fdst, Fsrc, Fet, Fnb, Fsum, Fretry, Fsend, Fack, Fcmd, Fncmds, Fbody, Fblen, Fpad, Fbsum.
    rewrite HET.
    unfold fr_body_sum, sum16. rewrite put2_mod.
    cbn [cells_bytes cbytes].
    rewrite ?le8_put, ?le4_put, ?le2_put, ?Z.add_0_r.
    cleanz.
    reflexivity. }
  assert (SFANY : forall mm : word -> option byte,
            bytes_at rsegs mm (bv_unsigned sp + -176) (sf_bytes p (rf frame)) ->
            sframe_at mm (bv_unsigned sp + -176) p (rf frame)).
  { intros mm HB. apply sf_bytes_sframe; try exact HB;
      [ lia | Z.div_mod_to_equations; lia
      | rewrite SFC; lia
      | unfold sf_ptr; rewrite SFC, Fdst; unfold SPEC_OK; cbn [Z.eqb]; lia
      | unfold sf_ptr; rewrite SFC, Fsrc; unfold SPEC_OK; cbn [Z.eqb]; lia
      | rewrite Fet, HET; lia
      | rewrite Fnb; lia
      | rewrite Fsum; unfold fr_sum, be16; lia
      | rewrite Fretry; unfold fr_retry, be16; lia
      | rewrite Fsend; unfold fr_send, be32; lia
      | rewrite Fack; unfold fr_ack, be32; lia
      | rewrite Fcmd; unfold fr_cmd; lia
      | rewrite Fncmds; unfold fr_ncmds; lia
      | unfold sf_ptr; rewrite SFC, Fbody; unfold SPEC_OK; cbn [Z.eqb]; lia
      | rewrite Fblen; lia
      | rewrite Fpad; unfold fr_pad_len, fr_body_len; lia
      | rewrite Fbsum; unfold fr_body_sum, sum16; apply Z.mod_pos_bound; lia ]. }
  pose proof (SFANY mT HSFB) as HSF.
  (* 14674: addi a2,sp,16 ; 14678: mv a0,s1 ; 1467c: mv a1,s0 ; 14680: jal check_sent_frame *)
  do 4 step.
  lazymatch goal with H : wmem rsegs mT _ |- _ => rename H into WMT end.
  eapply evt_cut.
  { eapply CSF;
      [ reflexivity | reflexivity | reflexivity | lia | exact HFR
      | unfold off_window; rewrite ESP; lia
      | exact HSF
      | unfold off_window; rewrite ESP; lia
      | exact WMT | exact HCS
      | rewrite ESP; Z.div_mod_to_equations; lia
      | rewrite ESP; exact ST
      | rewrite ESP; lia
      | unfold w_off_stack; rewrite ESP; lia
      | lazymatch goal with H : mem_inv rsegs mT |- _ => exact H end ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mU &
              Eq & MUc & WMc & MIU & STU & EB1 & WMU).
  subst ms'. rewrite ESP in MUc, STU. subst B1. clear WMT.
  transport_after_call rsegs mT mU MUc WMc. clear MUc WMc. try clear mT.
  rewrite (ret_pc_even 83596) by (first [lia | reflexivity]).
  (* ---- 14684-14694 and 14868-14884: the switch on f.cmd ---- *)
  pose proof (at8_range frame 28) as RC28.
  assert (RFC : 0 <= fr_cmd frame < 256) by (unfold fr_cmd; lia).
  rewrite Fcmd in HSW.
  do 2 step.
  if_cases EC1; cbv iota.
  1: assert (HC1 : 225 < fr_cmd frame) by (zc EC1; lia).
  1: do 2 step.
  1: if_cases EC2; cbv iota.
  2: assert (HC2 : fr_cmd frame <> 226) by (zc EC2; lia).
  2: do 2 step.
  2: if_cases EC3; cbv iota.
  (* goals: 1 = E2 (14890), 2 = the default (return), 3 = E3 (14878), 4 = f.cmd <= 225 *)
  2: { (* f.cmd is none of the four: the default of :895-896 *)
       assert (HC3 : fr_cmd frame <> 227) by (zc EC3; lia).
       replace (fr_cmd frame =? SPEC_CMD_ACK) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_ACK]; lia).
       replace (fr_cmd frame =? SPEC_CMD_E2) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_E2]; lia).
       replace (fr_cmd frame =? SPEC_CMD_DATA) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_DATA]; lia).
       replace (fr_cmd frame =? SPEC_CMD_E3) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_E3]; lia).
       cbn [orb] in HSW.
       assert (HBE : B' = set_g_fail_next B 0) by (injection HSW as HSW; congruence).
       subst B'.
       eapply EPI;
         [ exact MU | exact WMo | exact MIU | exact STU | exact WMU
         | exact FR0 | exact FRD | exact POST | cbn [cells_size csize]; reflexivity | exact FRS ]. }
  2: { (* f.cmd = 227 (SPEC_CMD_E3): GOT.e3++ at 14878, then check_latest_control *)
       assert (HC3 : fr_cmd frame = 227) by (zc EC3; lia).
       replace (fr_cmd frame =? SPEC_CMD_ACK) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_ACK]; lia).
       replace (fr_cmd frame =? SPEC_CMD_E2) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_E2]; lia).
       replace (fr_cmd frame =? SPEC_CMD_DATA) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_DATA]; lia).
       replace (fr_cmd frame =? SPEC_CMD_E3) with true in HSW
         by (symmetry; apply Z.eqb_eq; cbv [SPEC_CMD_E3]; lia).
       cbn [orb] in HSW.
       destruct (int_inc (GOT_e3 (set_g_fail_next B 0))) as [e3|] eqn:HE3; [|discriminate HSW].
       assert (He3 : e3 = GOT_e3 (set_g_fail_next B 0) + 1)
         by (unfold int_inc in HE3; destruct (GOT_e3 (set_g_fail_next B 0) =? INT_MAX);
             [discriminate HE3 | injection HE3; auto]).
       (* 14878: lw a0,316(s6) ; 1487c: addi a0,a0,1 ; 14880: sw a0,316(s6) *)
       step.
       change (s32_at (set_g_fail_next B 0) 65284) with (GOT_e3 (set_g_fail_next B 0)).
       do 2 step.
       lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WM2 end.
       rewrite ?put4_wrap1 in WM2. rewrite <- He3 in WM2.
       change (upd (set_g_fail_next B 0) 65284 (put 4 e3))
         with (set_GOT_e3 (set_g_fail_next B 0) e3) in WM2.
       (* 14884: addi a0,sp,16 ; 14888: jal check_latest_control *)
       do 2 step.
       eapply evt_cut.
       { eapply CLC;
           [ reflexivity | apply SFANY; exact HSFB
           | unfold off_window; rewrite ESP; lia
           | exact WM2 | exact HSW
           | rewrite ESP; Z.div_mod_to_equations; lia
           | rewrite ESP; exact STU
           | rewrite ESP; lia
           | unfold w_off_stack; rewrite ESP; lia
           | exact MIU ]. }
       intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mW &
                   EqW & MUw & WMw & MIW & STW & EBW & WMW).
       subst ms'. rewrite ESP in MUw, STW. clear WM2.
       lazymatch type of MUw with
       | munch _ ?mv _ => transport_after_call rsegs mv mW MUw WMw
       end.
       clear MUw WMw.
       rewrite (ret_pc_even 84116) by (first [lia | reflexivity]).
       (* 1488c: j 14824 *)
       step.
       rewrite <- EBW in WMW.
       eapply EPI;
         [ exact MU | exact WMo | exact MIW | exact STW | exact WMW
         | exact FR0 | exact FRD | exact POST | cbn [cells_size csize]; reflexivity | exact FRS ]. }
  (* goals: 1 = E2 (14890), 2 = f.cmd <= 225 *)
  2: assert (HC1 : fr_cmd frame <= 225) by (zc EC1; lia).
  2: step.
  2: if_cases EC4; cbv iota.
  (* goals: 1 = E2, 2 = f.cmd = 0 (DATA, 14890), 3 = f.cmd <> 0 *)
  3: assert (HC4 : fr_cmd frame <> 0) by (zc EC4; lia).
  3: do 2 step.
  3: if_cases EC5; cbv iota.
  (* goals: 1 = E2, 2 = DATA, 3 = f.cmd <> 160 (the default), 4 = f.cmd = 160 (ACK) *)
  3: { (* f.cmd is none of the four: the default of :895-896 *)
       assert (HC5 : fr_cmd frame <> 160) by (zc EC5; lia).
       replace (fr_cmd frame =? SPEC_CMD_ACK) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_ACK]; lia).
       replace (fr_cmd frame =? SPEC_CMD_E2) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_E2]; lia).
       replace (fr_cmd frame =? SPEC_CMD_DATA) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_DATA]; lia).
       replace (fr_cmd frame =? SPEC_CMD_E3) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_E3]; lia).
       cbn [orb] in HSW.
       assert (HBE : B' = set_g_fail_next B 0) by (injection HSW as HSW; congruence).
       subst B'.
       eapply EPI;
         [ exact MU | exact WMo | exact MIU | exact STU | exact WMU
         | exact FR0 | exact FRD | exact POST | cbn [cells_size csize]; reflexivity | exact FRS ]. }
  3: { (* f.cmd = 160 (SPEC_CMD_ACK): GOT.acks++ at 14698, check_ack_frame, check_latest_control *)
       assert (HC5 : fr_cmd frame = 160) by (zc EC5; lia).
       replace (fr_cmd frame =? SPEC_CMD_ACK) with true in HSW
         by (symmetry; apply Z.eqb_eq; cbv [SPEC_CMD_ACK]; lia).
       cbn [orb] in HSW.
       destruct (int_inc (GOT_acks (set_g_fail_next B 0))) as [ak|] eqn:HAK; [|discriminate HSW].
       assert (Hak : ak = GOT_acks (set_g_fail_next B 0) + 1)
         by (unfold int_inc in HAK; destruct (GOT_acks (set_g_fail_next B 0) =? INT_MAX);
             [discriminate HAK | injection HAK; auto]).
       destruct (check_ack_frame_m (set_GOT_acks (set_g_fail_next B 0) ak) frame) as [[B3 []]|] eqn:HCA;
         [|discriminate HSW].
       (* 14698: lw a0,320(s6) ; 1469c: addi a0,a0,1 ; 146a0: sw a0,320(s6) *)
       step.
       change (s32_at (set_g_fail_next B 0) 65288) with (GOT_acks (set_g_fail_next B 0)).
       do 2 step.
       lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WM2 end.
       rewrite ?put4_wrap1 in WM2. rewrite <- Hak in WM2.
       change (upd (set_g_fail_next B 0) 65288 (put 4 ak))
         with (set_GOT_acks (set_g_fail_next B 0) ak) in WM2.
       (* 146a4: addi a0,sp,16 ; 146a8: jal check_ack_frame *)
       do 2 step.
       eapply evt_cut.
       { eapply CAF;
           [ reflexivity | apply SFANY; exact HSFB
           | unfold off_window; rewrite ESP; lia
           | exact WM2 | exact HCA
           | rewrite ESP; Z.div_mod_to_equations; lia
           | rewrite ESP; exact STU
           | rewrite ESP; lia
           | unfold w_off_stack; rewrite ESP; lia
           | exact MIU ]. }
       intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mW &
                   EqW & MUw & WMw & MIW & STW & EBW & WMW).
       subst ms'. rewrite ESP in MUw, STW. clear WM2. subst B3.
       lazymatch type of MUw with
       | munch _ ?mv _ => transport_after_call rsegs mv mW MUw WMw
       end.
       clear MUw WMw.
       rewrite (ret_pc_even 83636) by (first [lia | reflexivity]).
       (* 146ac: j 14884 ; 14884: addi a0,sp,16 ; 14888: jal check_latest_control *)
       do 3 step.
       eapply evt_cut.
       { eapply CLC;
           [ reflexivity | apply SFANY; exact HSFB
           | unfold off_window; rewrite ESP; lia
           | exact WMW | exact HSW
           | rewrite ESP; Z.div_mod_to_equations; lia
           | rewrite ESP; exact STW
           | rewrite ESP; lia
           | unfold w_off_stack; rewrite ESP; lia
           | exact MIW ]. }
       intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mX &
                   EqX & MUx & WMx & MIX & STX & EBX & WMX).
       subst ms'. rewrite ESP in MUx, STX. clear WMW.
       lazymatch type of MUx with
       | munch _ ?mv => idtac
       | munch _ ?mv _ => transport_after_call rsegs mv mX MUx WMx
       end.
       clear MUx WMx.
       rewrite (ret_pc_even 84116) by (first [lia | reflexivity]).
       step.
       rewrite <- EBX in WMX.
       eapply EPI;
         [ exact MU | exact WMo | exact MIX | exact STX | exact WMX
         | exact FR0 | exact FRD | exact POST | cbn [cells_size csize]; reflexivity | exact FRS ]. }
  (* goals: 1 = E2 (14890), 2 = DATA (14890) *)
  1: { (* f.cmd = 226 (SPEC_CMD_E2) *)
       assert (HC2 : fr_cmd frame = 226) by (zc EC2; lia).
       replace (fr_cmd frame =? SPEC_CMD_ACK) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_ACK]; lia).
       replace (fr_cmd frame =? SPEC_CMD_E2) with true in HSW
         by (symmetry; apply Z.eqb_eq; cbv [SPEC_CMD_E2]; lia).
       cbn [orb] in HSW.
       rewrite Fretry in HSW.
       assert (RRT : 0 <= fr_retry frame < 65536)
         by (unfold fr_retry, be16; pose proof (at8_range frame 26); pose proof (at8_range frame 27); lia).
       (* 14890: beqz s8,148c4 *)
       step.
       if_cases ER; cbv iota.
       - (* f.retry = 0: no retransmission, 148c4 *)
         assert (HR0 : fr_retry frame = 0) by (zc ER; lia).
         replace (truth (fr_retry frame)) with false in HSW
           by (unfold truth; rewrite HR0; reflexivity).
         cbv iota in HSW.
         replace (fr_cmd frame =? SPEC_CMD_E2) with true in HSW
           by (symmetry; apply Z.eqb_eq; cbv [SPEC_CMD_E2]; lia).
         cbv iota in HSW.
         destruct (check_state_wake_m (set_g_fail_next B 0)) as [[B3 []]|] eqn:HCW; [|discriminate HSW].
         (* 148c4: li s8,226 ; 148c8: bne s10,s8 (not taken) *)
         do 2 step.
         if_cases EE; cbv iota.
         + exfalso. zc EE. lia.
         + (* 148cc: jal check_state_wake *)
           step.
           eapply evt_cut.
           { eapply CSW;
               [ exact WMU | exact HCW
               | rewrite ESP; Z.div_mod_to_equations; lia
               | rewrite ESP; exact STU | rewrite ESP; lia
               | unfold w_off_stack; rewrite ESP; lia | exact MIU ]. }
           intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mW &
                       EqW & MUw & WMw & MIW & STW & EBW & WMW).
           subst ms'. rewrite ESP in MUw, STW. subst B3. clear WMU.
           lazymatch type of MUw with
           | munch _ ?mv _ => transport_after_call rsegs mv mW MUw WMw
           end.
           clear MUw WMw.
           rewrite (ret_pc_even 84184) by (first [lia | reflexivity]).
           destruct (check_latest_control_m (set_g_fail_next B 0) frame) as [[B4 []]|] eqn:HCL;
             [|discriminate HSW].
           (* 148d0: addi a0,sp,16 ; 148d4: jal check_latest_control *)
           do 2 step.
           eapply evt_cut.
           { eapply CLC;
               [ reflexivity | apply SFANY; exact HSFB
               | unfold off_window; rewrite ESP; lia
               | exact WMW | exact HCL
               | rewrite ESP; Z.div_mod_to_equations; lia
               | rewrite ESP; exact STW | rewrite ESP; lia
               | unfold w_off_stack; rewrite ESP; lia | exact MIW ]. }
           intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mX &
                       EqX & MUx & WMx & MIX & STX & EBX & WMX).
           subst ms'. rewrite ESP in MUx, STX. subst B4. clear WMW.
           lazymatch type of MUx with
           | munch _ ?mv _ => transport_after_call rsegs mv mX MUx WMx
           end.
           clear MUx WMx.
           rewrite (ret_pc_even 84192) by (first [lia | reflexivity]).
           destruct (int_inc (GOT_e2 (set_g_fail_next B 0))) as [e2|] eqn:HE2; [|discriminate HSW].
           assert (He2 : e2 = GOT_e2 (set_g_fail_next B 0) + 1)
             by (unfold int_inc in HE2; destruct (GOT_e2 (set_g_fail_next B 0) =? INT_MAX);
                 [discriminate HE2 | injection HE2; auto]).
           (* 148d8: lw a0,312(s6) ; 148dc: addi a0,a0,1 ; 148e0: sw a0,312(s6) *)
           step.
           change (s32_at (set_g_fail_next B 0) 65280) with (GOT_e2 (set_g_fail_next B 0)).
           do 2 step.
           lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WM2 end.
           rewrite ?put4_wrap1 in WM2. rewrite <- He2 in WM2.
           change (upd (set_g_fail_next B 0) 65280 (put 4 e2))
             with (set_GOT_e2 (set_g_fail_next B 0) e2) in WM2.
           (* 148e4: andi a0,s5,1 ; 148e8: sw s7,8(s6) *)
           do 2 step.
           lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WM3 end.
           rewrite ?Fsend in WM3.
           change (upd (set_GOT_e2 (set_g_fail_next B 0) e2) 64976 (put 4 (fr_send frame)))
             with (set_g_last_counter (set_GOT_e2 (set_g_fail_next B 0) e2) (fr_send frame)) in WM3.
           rewrite <- Fsend in WM3.
           (* 148ec: beqz a0,147e0 *)
           step.
           assert (FB : g_fail_next B = 0 \/ g_fail_next B = 1).
           { pose proof (u_at_range B OFF_g_fail_next 1) as HU. change (8 * Z.of_nat 1) with 8 in HU.
             change (u_at B OFF_g_fail_next 1) with (g_fail_next B) in HU. lia. }
           if_cases EF; cbv iota.
           * (* the send did not fail: the frame goes in flight, 147e0 *)
             assert (HF0 : g_fail_next B = 0).
             { zc EF. destruct FB as [Hf0|Hf1]; [exact Hf0|]. rewrite Hf1 in EF. cbv in EF. lia. }
             replace (truth (g_fail_next B)) with false in HSW
               by (unfold truth; rewrite HF0; reflexivity).
             cbv iota in HSW.
             rewrite <- Fsend.
             replace (Z_to_bv 64 226) with (Z_to_bv 64 (sf_cmd (rf frame))) by (rewrite Fcmd, HC2; reflexivity).
             eapply FLY;
               [ exact MU | exact WMo | exact MIX | exact STX | exact WM3 | exact HFR
               | reflexivity
               | injection HSW as HSW; rewrite <- HSW, Fcmd; reflexivity
               | exact FR0 | exact FRD | exact POST | cbn [cells_size csize]; reflexivity | exact FRS ].
           * (* the send failed: no frame in flight, 14824 *)
             assert (HF1 : g_fail_next B = 1).
             { zc EF. destruct FB as [Hf0|Hf1]; [|exact Hf1]. rewrite Hf0 in EF. cbv in EF. lia. }
             replace (truth (g_fail_next B)) with true in HSW
               by (unfold truth; rewrite HF1; reflexivity).
             cbv iota in HSW.
             step.
             assert (HBE : B' = set_g_last_counter (set_GOT_e2 (set_g_fail_next B 0) e2) (sf_send (rf frame)))
               by (injection HSW as HSW; congruence).
             eapply EPI;
               [ exact MU | exact WMo | exact MIX | exact STX | rewrite HBE; exact WM3
               | exact FR0 | exact FRD | exact POST | cbn [cells_size csize]; reflexivity | exact FRS ].
       - (* f.retry <> 0: the retransmission check of :841 *)
         assert (HRN : fr_retry frame <> 0) by (zc ER; lia).
         replace (truth (fr_retry frame)) with true in HSW
           by (unfold truth; symmetry; apply negb_true_iff, Z.eqb_neq; exact HRN).
         cbv iota in HSW.
         destruct (check_inflight_retry_m (set_g_fail_next B 0) frame) as [[B3 []]|] eqn:HCI;
           [|discriminate HSW].
         (* 14894-148a0: a2 = &f, a0 = frame, a1 = len ; jal check_inflight_retry *)
         do 4 step.
         eapply evt_cut.
         { eapply CIR;
             [ reflexivity | reflexivity | reflexivity | lia | lia
             | exact HFR | unfold off_window; rewrite ESP; lia
             | apply SFANY; exact HSFB | unfold off_window; rewrite ESP; lia
             | exact WMU | exact HCI
             | rewrite ESP; Z.div_mod_to_equations; lia
             | rewrite ESP; exact STU | rewrite ESP; lia
             | unfold w_off_stack; rewrite ESP; lia | exact MIU ]. }
         intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mW &
                     EqW & MUw & WMw & MIW & STW & EBW & WMW).
         subst ms'. rewrite ESP in MUw, STW. subst B3. clear WMU.
         lazymatch type of MUw with
         | munch _ ?mv _ => transport_after_call rsegs mv mW MUw WMw
         end.
         clear MUw WMw.
         rewrite (ret_pc_even 84140) by (first [lia | reflexivity]).
         (* 148a4-148b0: a0 = &M ; a1 = M.fly.retries ; a2 = g_now *)
         do 3 step.
         change (s32_at (set_g_fail_next B 0) 108)
           with (bv_swrap 32 (M_fly_retries (set_g_fail_next B 0))).
         step.
         change (u_at (set_g_fail_next B 0) 65000 8) with (g_now (set_g_fail_next B 0)).
         (* 148b4: addi a1,a1,1 ; 148b8: sw a1,108(a0) ; 148bc: sd a2,112(a0) *)
         do 3 step.
         lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WM2 end.
         rewrite ?(put4_s32_inc (M_fly_retries (set_g_fail_next B 0))),
                 ?(put4_swrap_inc (M_fly_retries (set_g_fail_next B 0))) in WM2.
         (* 148c0: j 14824 *)
         step.
         assert (HBE : B' = set_M_fly_sent
                              (set_M_fly_retries (set_g_fail_next B 0)
                                 (u32 (M_fly_retries (set_g_fail_next B 0) + 1)))
                              (g_now (set_g_fail_next B 0)))
           by (injection HSW as HSW; congruence).
         eapply EPI;
           [ exact MU | exact WMo | exact MIW | exact STW | rewrite HBE; exact WM2
           | exact FR0 | exact FRD | exact POST | cbn [cells_size csize]; reflexivity | exact FRS ]. }
  (* f.cmd = 0 (SPEC_CMD_DATA): 14890, the retry test first *)
       assert (HC0 : fr_cmd frame = 0) by (zc EC4; lia).
       replace (fr_cmd frame =? SPEC_CMD_ACK) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_ACK]; lia).
       replace (fr_cmd frame =? SPEC_CMD_E2) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_E2]; lia).
       replace (fr_cmd frame =? SPEC_CMD_DATA) with true in HSW
         by (symmetry; apply Z.eqb_eq; cbv [SPEC_CMD_DATA]; lia).
       cbn [orb] in HSW.
       rewrite Fretry in HSW.
       assert (RRT : 0 <= fr_retry frame < 65536)
         by (unfold fr_retry, be16; pose proof (at8_range frame 26); pose proof (at8_range frame 27); lia).
       (* 14890: beqz s8,148c4 *)
       step.
       if_cases ER; cbv iota.
       2: { (* f.retry <> 0: the retransmission check of :841 *)
         assert (HRN : fr_retry frame <> 0) by (zc ER; lia).
         replace (truth (fr_retry frame)) with true in HSW
           by (unfold truth; symmetry; apply negb_true_iff, Z.eqb_neq; exact HRN).
         cbv iota in HSW.
         destruct (check_inflight_retry_m (set_g_fail_next B 0) frame) as [[B3 []]|] eqn:HCI;
           [|discriminate HSW].
         (* 14894-148a0: a2 = &f, a0 = frame, a1 = len ; jal check_inflight_retry *)
         do 4 step.
         eapply evt_cut.
         { eapply CIR;
             [ reflexivity | reflexivity | reflexivity | lia | lia
             | exact HFR | unfold off_window; rewrite ESP; lia
             | apply SFANY; exact HSFB | unfold off_window; rewrite ESP; lia
             | exact WMU | exact HCI
             | rewrite ESP; Z.div_mod_to_equations; lia
             | rewrite ESP; exact STU | rewrite ESP; lia
             | unfold w_off_stack; rewrite ESP; lia | exact MIU ]. }
         intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mW &
                     EqW & MUw & WMw & MIW & STW & EBW & WMW).
         subst ms'. rewrite ESP in MUw, STW. subst B3. clear WMU.
         lazymatch type of MUw with
         | munch _ ?mv _ => transport_after_call rsegs mv mW MUw WMw
         end.
         clear MUw WMw.
         rewrite (ret_pc_even 84140) by (first [lia | reflexivity]).
         (* 148a4-148b0: a0 = &M ; a1 = M.fly.retries ; a2 = g_now *)
         do 3 step.
         change (s32_at (set_g_fail_next B 0) 108)
           with (bv_swrap 32 (M_fly_retries (set_g_fail_next B 0))).
         step.
         change (u_at (set_g_fail_next B 0) 65000 8) with (g_now (set_g_fail_next B 0)).
         (* 148b4: addi a1,a1,1 ; 148b8: sw a1,108(a0) ; 148bc: sd a2,112(a0) *)
         do 3 step.
         lazymatch goal with H : rw_cells rsegs _ W_BASE_PLAIN _ |- _ => rename H into WM2 end.
         rewrite ?(put4_s32_inc (M_fly_retries (set_g_fail_next B 0))),
                 ?(put4_swrap_inc (M_fly_retries (set_g_fail_next B 0))) in WM2.
         (* 148c0: j 14824 *)
         step.
         assert (HBE : B' = set_M_fly_sent
                              (set_M_fly_retries (set_g_fail_next B 0)
                                 (u32 (M_fly_retries (set_g_fail_next B 0) + 1)))
                              (g_now (set_g_fail_next B 0)))
           by (injection HSW as HSW; congruence).
         eapply EPI;
           [ exact MU | exact WMo | exact MIW | exact STW | rewrite HBE; exact WM2
           | exact FR0 | exact FRD | exact POST | cbn [cells_size csize]; reflexivity | exact FRS ]. }
       (* f.retry = 0: 148c4 li s8,226 ; 148c8 bne s10,s8 -> 148f4 (taken: f.cmd is 0) *)
       assert (HR0 : fr_retry frame = 0) by (zc ER; lia).
       replace (truth (fr_retry frame)) with false in HSW
         by (unfold truth; rewrite HR0; reflexivity).
       cbv iota in HSW.
       replace (fr_cmd frame =? SPEC_CMD_E2) with false in HSW
         by (symmetry; apply Z.eqb_neq; cbv [SPEC_CMD_E2]; lia).
       cbv iota in HSW.
       do 2 step.
       if_cases EE; cbv iota.
       2: { exfalso. zc EE. lia. }
  (* 148f4-14920: the keepalive flag s9 of :854 *)
  rewrite Fbody, Fblen, Fncmds in HSW.
  set (kaV := (fr_body_len frame =? 1) && (at8 (skipn (Z.to_nat 30) frame) 0 =? 0) && (fr_ncmds frame =? 1))
    in HSW.
  assert (RNC : 0 <= fr_ncmds frame < 256)
    by (unfold fr_ncmds; pose proof (at8_range frame 29); lia).
  pose proof (at8_range frame 30) as RB30.
  enough (DENT : forall (vs9 vt0 vt1 vt2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6 : word),
    vs9 = Z_to_bv 64 (b2z kaV) ->
    evt rsegs QQ
      (MS (mkR (Z_to_bv 64 83596) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp vt0 vt1 vt2
                (Z_to_bv 64 (Z.of_nat (length frame))) (Z_to_bv 64 p)
                va0 va1 va2 va3 va4 va5 va6 va7
                (Z_to_bv 64 (p + 30)) (Z_to_bv 64 (fr_body_len frame)) (Z_to_bv 64 (fr_ncmds frame))
                (Z_to_bv 64 (g_fail_next B)) (Z_to_bv 64 271704) (Z_to_bv 64 (fr_send frame))
                (Z_to_bv 64 (fr_cmd frame)) vs9 (Z_to_bv 64 (fr_cmd frame)) s11
                vt3 vt4 vt5 vt6)
          F (Z_to_bv 64 83688) fc None mU (seg_rom rsegs))).
  do 2 step.
  if_cases EB1; cbv iota.
  (* f.body_len <> 1: not a keepalive *)
  assert (HB1 : fr_body_len frame <> 1) by (zc EB1; lia).
  assert (KF : kaV = false)
    by (unfold kaV; replace (fr_body_len frame =? 1) with false
          by (symmetry; apply (proj2 (Z.eqb_neq _ _)); exact HB1); reflexivity).
  do 3 step.
  eapply DENT. rewrite KF. reflexivity.
  (* f.body_len = 1: the body byte and f.ncmds decide *)
  assert (HB1 : fr_body_len frame = 1) by (zc EB1; lia).
  pose proof (rd_sub mU p frame 30 1 HFR ltac:(lia) ltac:(lia)) as RD.
  step. rewrite lbu_val by (apply length_sub; lia).
  rewrite (ble_sub1 frame 30 30 eq_refl ltac:(lia)). clear RD.
  (* 14900: zext.b a1,s4 ; 14904: xori a1,a1,1 ; 14908: or a0,a0,a1 ; 1490c: seqz s9,a0 ; 14910: li s3,1 ;
     14914: j 1491c ; 1491c: mv s8,s10 ; 14920: j 146e0 *)
  do 6 step.
  do 2 step.
  replace (Z_to_bv 64 1) with (Z_to_bv 64 (fr_body_len frame)) by (rewrite HB1; reflexivity).
  eapply DENT.
  rewrite io_ka_seqz by lia.
  unfold kaV. rewrite HB1. change (Z.to_nat 30) with 30%nat. rewrite at8_skipn0. reflexivity.
  (* ---- 146e0-147e0: the rest of the DATA arm (io_send_data.v) ---- *)
  refine (io_send_data CIN CLF CKD CLS CLD QQ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mU lo B B' p
            frame j0 jD _ kaV Hp HFR HFA HOW Hsp Hlo0 HLO HWS' Fsend Fcmd RNC Rbl BL30 HSW
            MU WMo MIU STU WMU FR0 FRD POST _ HSFB SFANY FRS FLY).
  cbn [cells_size csize]. reflexivity.
Qed.

Print Assumptions io_send_holds.
