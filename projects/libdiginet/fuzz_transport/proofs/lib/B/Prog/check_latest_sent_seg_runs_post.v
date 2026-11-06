(* check_latest_sent_seg_runs_post: the run of the ASan image-B walk of check_latest_sent from bcmp's return 0x849f4
   (a0 = 0) through the SENT store at t, the q_remove loop (the serial recovered from t through the constant-pool
   word in the frame slot sp + 24), the g_nq store and the display store, to the next loop head 0x84974 or the
   epilogue 0x84b4c. Shapes in check_latest_sent_seg_runs.v. *)
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

(* The step tactics' hypothesis transport, extended with the facts this walk carries: cls_body, cls_wok,
   addressable and mem_grows. Tac.v states footprint_after_store as a plain Ltac, so it can be redefined; the
   redefinition is Local, so a file that Requires this one keeps the library's own transport. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU;
              [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | MG : mem_grows ?mq m |- _ => apply (clsr_grow_write mq m (wa a) bs) in MG
  | HK : cls_wok ?d m |- _ => apply (cls_wok_write d m (wa a) bs) in HK
  | HB : cls_body m ?p ?bsy |- _ =>
      first [ apply (clsr_body_write m p bsy a bs) in HB; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | fail 100 "store meets the body:" a ]
  | HA : addressable m ?p ?n |- _ =>
      first [ apply (cls_addr_store m p n a bs) in HA; [ | lia | simpl_sizes; slia | cls_app_tac ]
            | fail 100 "store not in application memory:" a ]
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* ---- the helpers of cls_run_post ---- *)

(* a munch of [d, d + 4) keeps the world when [d, d + 4) misses every range of G_HARNESS_B: the store at dp *)
Lemma clsr_post_tw_dp : forall (m m' : word -> option byte) (d : Z) (Bw : list byte),
  tw_at TMAP_B (csw_view m) Bw -> munch [(d, d + 4)] m m' ->
  (forall b n, In (b, n) TransportGB.G_HARNESS_B -> d + 4 <= b \/ b + n <= d) ->
  tw_at TMAP_B (csw_view m') Bw.
Proof.
  intros m m' d Bw HW MU Hd.
  apply (clsr_tw_munch m m' [(d, d + 4)] Bw HW MU).
  intros b n i Hin Hi. cbn [outside]. split; [destruct (Hd b n Hin); lia | exact I].
Qed.

(* `srai a0,a0,3` of t - g_cmd = 40 s *)
Lemma clsr_post_srai : forall s, 0 <= s < 1024 -> Z.shiftr (bv_signed (Z_to_bv 64 (40 * s))) 3 = 5 * s.
Proof.
  intros s Hs. rewrite signed_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (40 * s) with (5 * s * 2 ^ 3) by lia. apply Z.div_mul. lia.
Qed.

(* `mulw a4,a0,a1` of 5 s and the pool word 0xcccccccccccccccd: the low 32 bits of the product are s, since
   5 * 0xcccccccccccccccd = 2^66 + 1, and s < 2^31 keeps the sign extension *)
Lemma clsr_post_mulw_z : forall s, 0 <= s < 1024 -> bv_swrap 32 (5 * s * CLS_KVAL) = s.
Proof.
  intros s Hs. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32).
  replace (5 * s * CLS_KVAL + 2 ^ 31) with (s + 2 ^ 31 + s * 2 ^ 34 * 2 ^ 32) by (unfold CLS_KVAL; lia).
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma clsr_post_mulw : forall s, 0 <= s < 1024 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (5 * s)) * bv_unsigned (Z_to_bv 64 CLS_KVAL))) = Z_to_bv 64 s.
Proof.
  intros s Hs. rewrite (unsigned_lit (5 * s)) by lia. rewrite (unsigned_lit CLS_KVAL) by (unfold CLS_KVAL; lia).
  rewrite clsr_post_mulw_z by lia. reflexivity.
Qed.

(* `slli a1,a2,2` of k *)
Lemma clsr_post_shl2 : forall k, 0 <= k < 2 ^ 32 -> Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 2 = 4 * k.
Proof. intros k Hk. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

(* before store_done: write the store's address in H the way store_done names it (wa of the goal's address) *)
Local Ltac clsr_post_fix_addr H :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a _) _) =>
      let E := addr_expr a in
      lazymatch type of H with
      | context [write_to_mem mm (wa ?E0) ?bs0] =>
          replace (write_to_mem mm (wa E0) bs0) with (write_to_mem mm (wa E) bs0) in H
            by (f_equal; unfold wa; f_equal; lia)
      end
  end.

(* ---- bcmp's return to the next loop head or the epilogue, 0x849f4 .. 0x84afc ---- *)
Lemma cls_run_post : forall (RNG : ExecF.footprint) (Q : machine_state -> Prop)
    (m : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
    (spv dp bp len pos s dispc : Z) (Bc B2 body : list byte) (j0 : list byte)
    (ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110 : word)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp : word),
  cls_bounds spv dp bp len -> cls_app spv 160 -> cls_app dp 4 ->
  cls_off spv dp bp len -> cls_rng RNG spv dp ->
  Z.of_nat (length body) = len ->
  Z.of_nat (length Bc) = TW.W_LEN ->
  0 <= pos -> 3 <= len - pos ->
  0 <= s < TC.CMDS_MAX ->
  TW.Cmd_len Bc s <= len - pos ->
  TC.q_remove_m (TW.set_Cmd_st Bc s TC.SENT) s = Some (B2, tt) ->
  rw_cells rsegs m spv (cls_fr j0 dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
  length j0 = 8%nat ->
  cls_mem m Bc body dp bp len (Z_to_bv 64 dispc) ->
  (* the exit, at 0x84b4c *)
  (forall (m' : word -> option byte) (j : list byte)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
           y28 y29 y30 y31 : word),
     length j = 56%nat ->
     rw_cells rsegs m' spv (cls_fr_e j ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
     cls_mem m' B2 body dp bp len (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display B2 s))) ->
     munch (cls_W spv dp) m m' -> wmono rsegs m m' -> mem_grows m m' ->
     len <= pos + TW.Cmd_len Bc s ->
     ExecF.evtF rsegs RNG Q
       (MS (mkR y1 (Z_to_bv 64 spv) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
           F (Z_to_bv 64 543564) fc None m' (seg_rom rsegs))) ->
  (* the next round, at the loop head 0x84974 *)
  (forall (m' : word -> option byte) (j0' : list byte)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y24 y28 y29 y30 y31 : word),
     length j0' = 8%nat ->
     rw_cells rsegs m' spv (cls_fr j0' dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
     cls_mem m' B2 body dp bp len (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display B2 s))) ->
     munch (cls_W spv dp) m m' -> wmono rsegs m m' -> mem_grows m m' ->
     pos + TW.Cmd_len Bc s < len ->
     ExecF.evtF rsegs RNG Q
       (MS (cls_regs_head y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y24 y28 y29 y30 y31 gp tp
              spv dp bp len (pos + TW.Cmd_len Bc s))
           F (Z_to_bv 64 543092) fc None m' (seg_rom rsegs))) ->
  ExecF.evtF rsegs RNG Q
    (MS (cls_regs_post x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp
           spv dp bp len pos s (TW.Cmd_len Bc s))
        F (Z_to_bv 64 543220) fc None m (seg_rom rsegs)).
Proof.
  intros RNG Q m F fc spv dp bp len pos s dispc Bc B2 body j0
    ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp
    HBD HAS HAD HOFF HRNG HLB HLBc Hpos H3 Hs HTL HQR FR HJ0 HM EXIT HEAD.
  assert (HL : 0 < len) by lia.
  destruct HBD as (Hsp0 & Hsp1 & Hdp0 & Hdp1 & Hbp0 & Hlen0 & Hbp1 & Hdp4).
  destruct HRNG as (RFR & RC1 & RC2 & RDP & RDS & RKS & RC & RSC & RQ & RSQ & RNQ).
  destruct HM as (HW & DPc & HB & AC & AQ & AD & AB & HK).
  pose proof HOFF as (_ & _ & _ & _ & _ & _ & _ & HOG & HOB & _ & _ & _).
  unfold TC.CMDS_MAX in Hs.
  pose proof (cls_cmd_len_range Bc s) as RTL.
  pose proof (Z.mod_pos_bound dp 8 ltac:(lia)) as Rdp8.
  (* the model: q_remove's loop gives B1q and the count kf, and B2 = set_g_nq B1q kf; the loop bounds g_nq *)
  destruct (cls_qrm _ _ _ HQR) as (B1q & kf & HQL & HB2). clear HQR.
  rewrite (cls_g_nq_set_st Bc s TC.SENT HLBc ltac:(unfold TC.CMDS_MAX; lia)) in HQL.
  pose proof (cls_q_nqle _ _ _ _ _ _ _ _ HQL ltac:(unfold TC.CMDS_MAX; lia)) as HNQ1.
  pose proof (cls_g_nq_range Bc) as HNQ0.
  assert (HNQ : 0 <= TW.g_nq Bc <= 1024) by (unfold TC.CMDS_MAX in HNQ1; lia).
  clear HNQ1 HNQ0.
  pose proof (cls_len_set_st Bc s TC.SENT HLBc ltac:(unfold TC.CMDS_MAX; lia)) as HL1.
  destruct (cls_q_loop_gen (fun _ => True) (fun _ _ _ _ _ _ => I) _ _ _ _ _ _ _ _ HQL HL1
              ltac:(lia) ltac:(lia) I) as (HLq & _ & Kf1 & Kf2 & _).
  assert (HKF : 0 <= kf <= TW.g_nq Bc) by lia.
  clear Kf1 Kf2.
  subst B2.
  unfold cls_regs_head in HEAD. unfold cls_regs_post.
  pose proof (munch_refl (cls_W spv dp) m) as MU. unfold cls_W in MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (mem_grows_refl m) as MG.
  unfold cls_fr in FR.
  (* ---- 0x84ac0 .. 0x84afc: g_nq := k, the display, the next round or the exit ---- *)
  assert (TAIL : forall (m3 : word -> option byte) (Bqf : list byte) (kfin : Z)
            (y5 y6 y10 y11 y13 y14 y15 y16 y17 : word),
    Bqf = B1q -> kfin = kf ->
    rw_cells rsegs m3 spv (cls_fr j0 dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
    tw_at TMAP_B (csw_view m3) Bqf -> rw_cells rsegs m3 dp [C4 (Z_to_bv 64 dispc)] -> cls_body m3 bp body ->
    addressable m3 6180992 40960 -> addressable m3 6232192 4096 -> addressable m3 dp 4 ->
    addressable m3 bp len -> cls_wok dp m3 ->
    munch (cls_W spv dp) m m3 -> wmono rsegs m m3 -> mem_grows m m3 ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 spv) gp tp y5 y6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
               y10 y11 (Z_to_bv 64 kfin) y13 y14 y15 y16 y17
               (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
               (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
               (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
               x28 x29 x30 x31)
          F (Z_to_bv 64 543424) fc None m3 (seg_rom rsegs))).
  { intros m3 Bqf kfin y5 y6 y10 y11 y13 y14 y15 y16 y17 EBq EKf FR3 HW3 DP3 HB3 AC3 AQ3 AD3 AB3 HK3
      MU3 WMo3 MG3.
    subst Bqf kfin.
    clear FR HW DPc HB AC AQ AD AB HK MU WMo MG.
    unfold cls_fr in FR3. unfold cls_W in MU3.
    (* 0x84ac0: sw a2,-868(s11): g_nq := kf, no instrumented check *)
    assert (HS : store_ok rsegs m3 (wa 6157792) 4 = true).
    { apply (cls_wok_store_ok dp m3 6157792 4 HK3); [lia | change (Z.of_nat 4) with 4; lia |].
      intros i Hi. change (Z.of_nat 4) with 4 in Hi. unfold cls_wrange. lia. }
    pose proof HOFF as (O1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & O11 & _). specialize (O11 HL).
    unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI in O1.
    pose proof (HOG _ _ (TMAP_B_in_G _ _ _ TMAP_B_g_nq)) as Gn. unfold TB_g_nq, TW.SZ_g_nq in Gn.
    step.
    pose proof (cls_tw_wr4 m3 B1q TW.OFF_g_nq TB_g_nq TW.SZ_g_nq 0 kf HW3 TMAP_B_g_nq ltac:(lia)
      ltac:(unfold TW.SZ_g_nq; lia)) as HW4.
    unfold TB_g_nq in HW4. rewrite !Z.add_0_r in HW4.
    change (TW.upd B1q TW.OFF_g_nq (TW.put 4 kf)) with (TW.set_g_nq B1q kf) in HW4.
    clsr_post_fix_addr HW4.
    clear HW3.
    store_done.
    clear O1 O11 Gn.
    lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
    (* the state at 0x84ae8: the display is in a0, the check of dp is done *)
    assert (DPST : forall z11 z12 : word,
      ExecF.evtF rsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 spv) gp tp y5 y6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 (Z_to_bv 64 (TW.Cmd_display (TW.set_g_nq B1q kf) s)) z11 z12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                 (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
                 (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 543464) fc None m4 (seg_rom rsegs))).
    { intros z11 z12.
      (* 0x84ae8: lw a1,0(s0) *)
      step.
      (* 0x84aec: or a0,a1,a0 *)
      step.
      (* 0x84af0: add s9,s9,s4 *)
      step.
      (* 0x84af4: sw a0,0(s0); the world is kept through a munch of [dp, dp + 4) *)
      pose proof HOFF as (_ & _ & _ & _ & _ & O6 & _ & _ & _ & _ & _ & O12). specialize (O12 HL).
      pose proof (munch_refl [(dp, dp + 4)] m4) as MUd.
      step.
      lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
      pose proof (clsr_post_tw_dp m4 m5 dp _ HW4 MUd HOG) as HW5.
      clear HW4 MUd O6 O12.
      lazymatch goal with H : rw_cells rsegs m5 dp [C4 ?v] |- _ =>
        pose proof (clsr_c4_swap m5 dp v
                      (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display (TW.set_g_nq B1q kf) s)))
                      (cls_disp_le4 _ _) H) as DP5; clear H end.
      (* 0x84af8: bltu s9,s1 *)
      step. rewrite cls_ltu_lit by lia.
      destruct (Z.ltb_spec (pos + TW.Cmd_len Bc s) len) as [Lt|Ge]; cbv iota.
      - apply (HEAD m5 j0);
          [ exact HJ0 | exact FR3
          | exact (conj HW5 (conj DP5 (conj HB3 (conj AC3 (conj AQ3 (conj AD3 (conj AB3 HK3)))))))
          | exact MU3 | exact WMo3 | exact MG3 | exact Lt ].
      - (* 0x84afc: j 0x84b4c *)
        step.
        destruct (clsr_fr_e m5 spv dp j0 ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110 HJ0 FR3)
          as (je & HJe & FRe).
        apply (EXIT m5 je);
          [ exact HJe | exact FRe
          | exact (conj HW5 (conj DP5 (conj HB3 (conj AC3 (conj AQ3 (conj AD3 (conj AB3 HK3)))))))
          | exact MU3 | exact WMo3 | exact MG3 | exact Ge ]. }
    (* the state at 0x84ad8: the check of t + 8 is done *)
    assert (BODYD : forall z11 z12 : word,
      ExecF.evtF rsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 spv) gp tp y5 y6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 (Z_to_bv 64 (6180992 + 40 * s + 8)) z11 z12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                 (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
                 (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 543448) fc None m4 (seg_rom rsegs))).
    { intros z11 z12.
      (* 0x84ad8: ld a1,48(sp): the shadow address of dp *)
      step.
      (* 0x84adc: lb a1,0(a1): the shadow byte of dp *)
      destruct (cls_sh_load m4 dp 4 0 4 AD3 ltac:(lia) ltac:(lia) ltac:(lia)) as (kd & MKd & SKd).
      rewrite Z.add_0_r in MKd, SKd. change (4 - 1) with 3 in SKd. unfold ASAN_K in MKd.
      pose proof (rd1 m4 _ _ MKd) as RDd. clear MKd.
      step.
      (* 0x84ae0: lw a0,0(a0): t->display *)
      pose proof (cls_rd m4 (TW.set_g_nq B1q kf) TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s + 8) 4 HW4
        TMAP_B_g_cmd ltac:(lia) ltac:(unfold TW.SZ_g_cmd; lia)) as RDc.
      unfold TB_g_cmd in RDc.
      replace (6180992 + (40 * s + 8)) with (6180992 + 40 * s + 8) in RDc by lia.
      replace (TW.OFF_g_cmd + (40 * s + 8)) with (TW.A_Cmd_display s) in RDc
        by (unfold TW.A_Cmd_display; lia).
      step. rewrite lw_world. clear RDc.
      change (TW.s32_at (TW.set_g_nq B1q kf) (TW.A_Cmd_display s))
        with (TW.Cmd_display (TW.set_g_nq B1q kf) s).
      (* 0x84ae4: bnez a1 *)
      step. rewrite sxb_eq0.
      destruct SKd as [C|[C Cu]].
      - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply DPST.
      - rewrite (proj2 (Z.eqb_neq (bv_signed kd) 0) ltac:(lia)). cbn [negb]. cbv iota.
        (* 0x84b3c-0x84b40: ld a2,8(sp); blt a2,a1 goes back to the load *)
        step. step.
        rewrite (cls_lts_lit (dp mod 8 + 3) kd ltac:(lia)).
        rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
        apply DPST. }
    (* 0x84ac4-0x84ad4: a0 = t + 8; the check of the 4-byte load at it *)
    destruct (cls_sh_load m4 6180992 40960 (40 * s + 8) 4 AC3 ltac:(lia) ltac:(lia) ltac:(lia))
      as (k8 & MK8 & SK8).
    replace (6180992 + (40 * s + 8)) with (6180992 + 40 * s + 8) in MK8, SK8 by lia.
    change (4 - 1) with 3 in SK8.
    pose proof (cls_shc RNG (40 * s + 8) RSC ltac:(lia)) as RK8.
    replace (6180992 + (40 * s + 8)) with (6180992 + 40 * s + 8) in RK8 by lia.
    unfold ASAN_K in MK8, RK8.
    pose proof (rd1 m4 _ _ MK8) as RD8. clear MK8.
    step.
    step. rewrite (unsigned_lit (6180992 + 40 * s + 8)) by lia. rewrite cls_shr3.
    step. step.
    step. rewrite sxb_eq0.
    destruct SK8 as [C|[C Cu]].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply BODYD.
    - rewrite (proj2 (Z.eqb_neq (bv_signed k8) 0) ltac:(lia)). cbn [negb]. cbv iota.
      (* 0x84b2c-0x84b38: the handler goes back to the load *)
      step. step.
      step. rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit (6180992 + 40 * s + 8)) by lia.
      rewrite (cls_lts_lit ((6180992 + 40 * s + 8) mod 8 + 3) k8 ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
      step. apply BODYD. }
  (* ---- 0x84a34 .. 0x84a98: the q_remove loop, i the index, k the count kept ---- *)
  assert (LOOP : forall fuel i k (Bq : list byte) (m3 : word -> option byte) (y5 y6 y11 y17 : word)
            (A0 A6 N3 N5 : Z),
    TC.q_remove_loop fuel Bq s (TW.g_nq Bc) i k = Some (B1q, kf) ->
    0 <= k <= i -> i < TW.g_nq Bc ->
    A0 = 6232192 + 4 * i -> A6 = 6232192 + 4 * i -> N3 = TW.g_nq Bc - i -> N5 = 1024 - i ->
    rw_cells rsegs m3 spv (cls_fr j0 dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
    tw_at TMAP_B (csw_view m3) Bq -> rw_cells rsegs m3 dp [C4 (Z_to_bv 64 dispc)] -> cls_body m3 bp body ->
    addressable m3 6180992 40960 -> addressable m3 6232192 4096 -> addressable m3 dp 4 ->
    addressable m3 bp len -> cls_wok dp m3 ->
    munch (cls_W spv dp) m m3 -> wmono rsegs m m3 -> mem_grows m m3 ->
    ExecF.evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 spv) gp tp y5 y6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
               (Z_to_bv 64 A0) y11 (Z_to_bv 64 k) (Z_to_bv 64 N3) (Z_to_bv 64 s) (Z_to_bv 64 N5)
               (Z_to_bv 64 A6) y17
               (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
               (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
               (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
               x28 x29 x30 x31)
          F (Z_to_bv 64 543284) fc None m3 (seg_rom rsegs))).
  { clear FR HW DPc HB AC AQ AD AB HK MU WMo MG.
    induction fuel as [|fuel IH];
      intros i k Bq m3 y5 y6 y11 y17 A0 A6 N3 N5 HQi Hki Hinq EA0 EA6 EN3 EN5
        FR3 HW3 DP3 HB3 AC3 AQ3 AD3 AB3 HK3 MU3 WMo3 MG3; [discriminate HQi|].
    destruct (cls_q_step (S fuel) Bq s (TW.g_nq Bc) i k B1q kf HQi Hinq) as (f2 & Ef2 & HiM & HQ2).
    assert (Ef : f2 = fuel) by lia. subst f2. clear Ef2. unfold TC.CMDS_MAX in HiM.
    (* the state at 0x84a84: a3 -= 1, a0 and a6 += 4, a5 -= 1, then the loop test *)
    assert (NEXT : forall k' (Bq' : list byte) (m4 : word -> option byte) (z5 z6 z11 z17 : word),
      TC.q_remove_loop fuel Bq' s (TW.g_nq Bc) (i + 1) k' = Some (B1q, kf) -> 0 <= k' <= i + 1 ->
      rw_cells rsegs m4 spv (cls_fr j0 dp ra0 s00 s10 s20 s30 s40 s50 s60 s70 s80 s90 s100 s110) ->
      tw_at TMAP_B (csw_view m4) Bq' -> rw_cells rsegs m4 dp [C4 (Z_to_bv 64 dispc)] -> cls_body m4 bp body ->
      addressable m4 6180992 40960 -> addressable m4 6232192 4096 -> addressable m4 dp 4 ->
      addressable m4 bp len -> cls_wok dp m4 ->
      munch (cls_W spv dp) m m4 -> wmono rsegs m m4 -> mem_grows m m4 ->
      ExecF.evtF rsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 spv) gp tp z5 z6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 (Z_to_bv 64 A0) z11 (Z_to_bv 64 k') (Z_to_bv 64 N3) (Z_to_bv 64 s) (Z_to_bv 64 N5)
                 (Z_to_bv 64 A6) z17
                 (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                 (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
                 (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 543364) fc None m4 (seg_rom rsegs))).
    { intros k' Bq' m4 z5 z6 z11 z17 HQ' Hk' FR4 HW4 DP4 HB4 AC4 AQ4 AD4 AB4 HK4 MU4 WMo4 MG4.
      (* 0x84a84-0x84a90 *)
      step. step. step. step.
      (* 0x84a94: bnez a3 *)
      step. rewrite cls_eqb0 by lia.
      destruct (Z.eqb_spec (N3 + -1) 0) as [E0|E0]; cbn [negb]; cbv iota.
      - (* 0x84a98: j 0x84ac0 *)
        step.
        destruct (cls_q_exit _ _ _ _ _ _ _ _ HQ' ltac:(lia)) as [EB EK].
        apply (TAIL m4 Bq' k');
          [ exact (eq_sym EB) | exact (eq_sym EK) | exact FR4 | exact HW4 | exact DP4 | exact HB4
          | exact AC4 | exact AQ4 | exact AD4 | exact AB4 | exact HK4 | exact MU4 | exact WMo4 | exact MG4 ].
      - apply (IH (i + 1) k' Bq' m4);
          [ exact HQ' | lia | lia | lia | lia | lia | lia | exact FR4 | exact HW4 | exact DP4 | exact HB4
          | exact AC4 | exact AQ4 | exact AD4 | exact AB4 | exact HK4 | exact MU4 | exact WMo4 | exact MG4 ]. }
    unfold cls_fr in FR3. unfold cls_W in MU3.
    (* the state at 0x84a48: the check of g_q[i] is done *)
    assert (BODYQ : forall z11 z17 : word,
      ExecF.evtF rsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 spv) gp tp y5 y6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                 (Z_to_bv 64 A0) z11 (Z_to_bv 64 k) (Z_to_bv 64 N3) (Z_to_bv 64 s) (Z_to_bv 64 N5)
                 (Z_to_bv 64 A6) z17
                 (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                 (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
                 (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
                 x28 x29 x30 x31)
            F (Z_to_bv 64 543304) fc None m3 (seg_rom rsegs))).
    { intros z11 z17.
      (* 0x84a48: lw a7,0(a6) = g_q[i] *)
      pose proof (cls_rd m3 Bq TW.OFF_g_q TB_g_q TW.SZ_g_q (4 * i) 4 HW3 TMAP_B_g_q ltac:(lia)
        ltac:(unfold TW.SZ_g_q; lia)) as RDq.
      unfold TB_g_q in RDq. replace (6232192 + 4 * i) with A6 in RDq by lia.
      step. rewrite lw_world. clear RDq.
      pose proof (TWLK.s32_range Bq (TW.OFF_g_q + 4 * i)) as RS1.
      (* 0x84a4c: beq a7,a4 *)
      step. rewrite cls_eqb_lit by lia.
      rewrite (cls_s32_eqb Bq (TW.OFF_g_q + 4 * i) s) by lia.
      change (TW.u_at Bq (TW.OFF_g_q + 4 * i) 4) with (TW.Q_at Bq i).
      destruct (Z.eqb_spec (TW.Q_at Bq i) s) as [EQS|EQS]; cbv iota.
      - (* g_q[i] = s: skip, 0x84a84 *)
        try rewrite (proj2 (Z.eqb_eq _ _) EQS) in HQ2. cbv beta iota in HQ2.
        apply (NEXT k Bq m3);
          [ exact HQ2 | lia | exact FR3 | exact HW3 | exact DP3 | exact HB3
          | exact AC3 | exact AQ3 | exact AD3 | exact AB3 | exact HK3 | exact MU3 | exact WMo3 | exact MG3 ].
      - (* copy: 0x84a50 *)
        try rewrite (proj2 (Z.eqb_neq _ _) EQS) in HQ2. cbv beta iota in HQ2.
        (* the state at 0x84a7c: the check of g_q[k] is done *)
        assert (BODYC : forall z5 z6 : word,
          ExecF.evtF rsegs RNG Q
            (MS (mkR x1 (Z_to_bv 64 spv) gp tp z5 z6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
                     (Z_to_bv 64 A0) (Z_to_bv 64 (6232192 + 4 * k)) (Z_to_bv 64 k) (Z_to_bv 64 N3)
                     (Z_to_bv 64 s) (Z_to_bv 64 N5) (Z_to_bv 64 A6)
                     (Z_to_bv 64 (TW.s32_at Bq (TW.OFF_g_q + 4 * i)))
                     (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
                     (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880)
                     (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
                     (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
                     x28 x29 x30 x31)
                F (Z_to_bv 64 543356) fc None m3 (seg_rom rsegs))).
        { intros z5 z6.
          (* 0x84a7c: addiw a2,a2,1 *)
          step. rewrite cls_addiw by lia.
          (* 0x84a80: sw a7,0(a1): g_q[k] := g_q[i] *)
          assert (HS : store_ok rsegs m3 (wa (6232192 + 4 * k)) 4 = true).
          { apply (cls_wok_store_ok dp m3 (6232192 + 4 * k) 4 HK3); [lia | change (Z.of_nat 4) with 4; lia |].
            intros i' Hi'. change (Z.of_nat 4) with 4 in Hi'. unfold cls_wrange. lia. }
          pose proof HOFF as (O1 & _ & _ & _ & _ & _ & _ & _ & _ & O10 & _ & _). specialize (O10 HL).
          unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI in O1.
          pose proof (HOG _ _ (TMAP_B_in_G _ _ _ TMAP_B_g_q)) as Gq. unfold TB_g_q, TW.SZ_g_q in Gq.
          step.
          pose proof (cls_tw_wr4 m3 Bq TW.OFF_g_q TB_g_q TW.SZ_g_q (4 * k) (TW.s32_at Bq (TW.OFF_g_q + 4 * i))
            HW3 TMAP_B_g_q ltac:(lia) ltac:(unfold TW.SZ_g_q; lia)) as HW4.
          unfold TB_g_q in HW4.
          replace (TW.upd Bq (TW.OFF_g_q + 4 * k) (TW.put 4 (TW.s32_at Bq (TW.OFF_g_q + 4 * i))))
            with (TW.set_Q_at Bq k (TW.Q_at Bq i)) in HW4
            by (unfold TW.set_Q_at, TW.Q_at; rewrite cls_put_s32; reflexivity).
          clsr_post_fix_addr HW4.
          clear HW3.
          store_done.
          clear O1 O10 Gq.
          lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
          apply (NEXT (k + 1) (TW.set_Q_at Bq k (TW.Q_at Bq i)) m4);
            [ exact HQ2 | lia | exact FR3 | exact HW4 | exact DP3 | exact HB3
            | exact AC3 | exact AQ3 | exact AD3 | exact AB3 | exact HK3 | exact MU3 | exact WMo3 | exact MG3 ]. }
        (* 0x84a50: bltu s10,a2 (the trap 1023 < k) *)
        step. rewrite cls_ltu_lit by lia.
        rewrite (proj2 (Z.ltb_ge 1023 k) ltac:(lia)). cbv iota.
        (* 0x84a54: slli a1,a2,2 *)
        step. rewrite clsr_post_shl2 by lia.
        (* 0x84a58-0x84a5c: t0 = g_q; 0x84a60: not t1,t0 *)
        step. step. step.
        (* 0x84a64: bltu t1,a1 (the trap ~g_q < 4 k) *)
        step. rewrite cls_ltu_lit by lia.
        rewrite (proj2 (Z.ltb_ge 18446744073703319423 (4 * k)) ltac:(lia)). cbv iota.
        (* 0x84a68: add a1,t0,a1 *)
        step. rewrite ?(unsigned_lit (4 * k)) by lia.
        (* 0x84a6c-0x84a78: the check of the 4-byte store at g_q + 4 k *)
        destruct (cls_sh_load m3 6232192 4096 (4 * k) 4 AQ3 ltac:(lia) ltac:(lia) ltac:(lia)) as (kk & MKk & SKk).
        change (4 - 1) with 3 in SKk.
        pose proof (cls_shq RNG (4 * k) RSQ ltac:(lia)) as RKk.
        unfold ASAN_K in MKk, RKk.
        pose proof (rd1 m3 _ _ MKk) as RDk. clear MKk.
        step. rewrite (unsigned_lit (6232192 + 4 * k)) by lia. rewrite cls_shr3.
        step. step.
        step. rewrite sxb_eq0.
        destruct SKk as [C|[C Cu]].
        + rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply BODYC.
        + rewrite (proj2 (Z.eqb_neq (bv_signed kk) 0) ltac:(lia)). cbn [negb]. cbv iota.
          (* 0x84aac-0x84ab8: the handler goes back to the store *)
          step. step.
          step. rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit (6232192 + 4 * k)) by lia.
          rewrite (cls_lts_lit ((6232192 + 4 * k) mod 8 + 3) kk ltac:(lia)).
          rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
          step. apply BODYC. }
    (* 0x84a34: beqz a5 (the trap i = 1024) *)
    step. rewrite cls_eqb0 by lia.
    rewrite (proj2 (Z.eqb_neq N5 0) ltac:(lia)). cbv iota.
    (* 0x84a38-0x84a44: the check of the 4-byte load at g_q + 4 i *)
    destruct (cls_sh_load m3 6232192 4096 (4 * i) 4 AQ3 ltac:(lia) ltac:(lia) ltac:(lia)) as (kq & MKq & SKq).
    replace (6232192 + 4 * i) with A0 in MKq, SKq by lia.
    change (4 - 1) with 3 in SKq.
    pose proof (cls_shq RNG (4 * i) RSQ ltac:(lia)) as RKq.
    replace (6232192 + 4 * i) with A0 in RKq by lia.
    unfold ASAN_K in MKq, RKq.
    pose proof (rd1 m3 _ _ MKq) as RDkq. clear MKq.
    step. rewrite (unsigned_lit A0) by lia. rewrite cls_shr3.
    step. step.
    step. rewrite sxb_eq0.
    destruct SKq as [C|[C Cu]].
    - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply BODYQ.
    - rewrite (proj2 (Z.eqb_neq (bv_signed kq) 0) ltac:(lia)). cbn [negb]. cbv iota.
      (* 0x84a9c-0x84aa8: the handler goes back to the load *)
      step. step.
      step. rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit A0) by lia.
      rewrite (cls_lts_lit (A0 mod 8 + 3) kq ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
      step. apply BODYQ. }
  (* ---- 0x84a00 .. 0x84a30: t->st := SENT, then the g_nq load, q_remove's set-up or the g_nq store ---- *)
  assert (STT : forall y10 y11 : word,
    ExecF.evtF rsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 spv) gp tp x5 x6 x7 (Z_to_bv 64 dp) (Z_to_bv 64 len)
               y10 y11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 bp) (Z_to_bv 64 (6180992 + 40 * s)) (Z_to_bv 64 (TW.Cmd_len Bc s))
               (Z_to_bv 64 (bp + pos)) (Z_to_bv 64 (len - pos)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 ((6180992 + 40 * s) / 8 + 2147450880))
               (Z_to_bv 64 pos) (Z_to_bv 64 1023) (Z_to_bv 64 6158660)
               x28 x29 x30 x31)
          F (Z_to_bv 64 543232) fc None m (seg_rom rsegs))).
  { intros y10 y11.
    (* 0x84a00: li a0,2 *)
    step.
    (* 0x84a04: sw a0,0(s3): t->st := SENT *)
    assert (HS : store_ok rsegs m (wa (6180992 + 40 * s)) 4 = true).
    { apply (cls_wok_store_ok dp m (6180992 + 40 * s) 4 HK); [lia | change (Z.of_nat 4) with 4; lia |].
      intros i Hi. change (Z.of_nat 4) with 4 in Hi. unfold cls_wrange. lia. }
    pose proof HOFF as (O1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold TransportGB.G_HARNESS_B_LO, TransportGB.G_HARNESS_B_HI in O1.
    pose proof (HOG _ _ (TMAP_B_in_G _ _ _ TMAP_B_g_cmd)) as Gc. unfold TB_g_cmd, TW.SZ_g_cmd in Gc.
    pose proof (HOB HL s ltac:(lia)) as Bs.
    step.
    pose proof (cls_tw_wr4 m Bc TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * s) 2 HW TMAP_B_g_cmd ltac:(lia)
      ltac:(unfold TW.SZ_g_cmd; lia)) as HW1.
    unfold TB_g_cmd in HW1.
    replace (TW.upd Bc (TW.OFF_g_cmd + 40 * s) (TW.put 4 2)) with (TW.set_Cmd_st Bc s TC.SENT) in HW1
      by (unfold TW.set_Cmd_st, TW.A_Cmd_st, TC.SENT; rewrite Z.add_0_r; reflexivity).
    clsr_post_fix_addr HW1.
    clear HW.
    store_done.
    clear O1 Gc Bs.
    lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    (* 0x84a08: lwu a3,-868(s11): g_nq, unsigned, no instrumented check *)
    pose proof (cls_rd m1 (TW.set_Cmd_st Bc s TC.SENT) TW.OFF_g_nq TB_g_nq TW.SZ_g_nq 0 4 HW1 TMAP_B_g_nq
      ltac:(lia) ltac:(unfold TW.SZ_g_nq; lia)) as RDn.
    unfold TB_g_nq in RDn. rewrite !Z.add_0_r in RDn.
    step. rewrite lwu_world. clear RDn.
    change (TW.u_at (TW.set_Cmd_st Bc s TC.SENT) TW.OFF_g_nq 4) with (TW.g_nq (TW.set_Cmd_st Bc s TC.SENT)).
    rewrite (cls_g_nq_set_st Bc s TC.SENT HLBc ltac:(unfold TC.CMDS_MAX; lia)).
    (* 0x84a0c: beqz a3 *)
    step. rewrite cls_eqb0 by lia.
    destruct (Z.eqb_spec (TW.g_nq Bc) 0) as [N0|N0]; cbv iota.
    - (* g_nq = 0: 0x84abc li a2,0, then the g_nq store *)
      step.
      destruct (cls_q_exit _ _ _ _ _ _ _ _ HQL ltac:(lia)) as [EB EK].
      apply (TAIL m1 (TW.set_Cmd_st Bc s TC.SENT) 0);
        [ exact (eq_sym EB) | exact (eq_sym EK) | exact FR | exact HW1 | exact DPc | exact HB
        | exact AC | exact AQ | exact AD | exact AB | exact HK | exact MU | exact WMo | exact MG ].
    - (* 0x84a10: li a2,0; 0x84a14: ld a0,32(sp) = g_cmd; 0x84a18: sub a0,s3,a0 = 40 s *)
      step. step. step.
      rewrite (unsigned_lit (6180992 + 40 * s)) by lia.
      replace (6180992 + 40 * s - 6180992) with (40 * s) by lia.
      (* 0x84a1c: srai a0,a0,3 = 5 s *)
      step. rewrite clsr_post_srai by lia.
      (* 0x84a20: ld a1,24(sp) = the pool word; 0x84a24: mulw a4,a0,a1 = s *)
      step. step.
      rewrite clsr_post_mulw by lia.
      (* 0x84a28: li a5,1024; 0x84a2c: ld a0,16(sp) = g_q; 0x84a30: mv a6,a0 *)
      step. step. step.
      apply (LOOP (S (Z.to_nat TC.CMDS_MAX)) 0 0 (TW.set_Cmd_st Bc s TC.SENT) m1);
        [ exact HQL | lia | lia | lia | lia | lia | lia | exact FR | exact HW1 | exact DPc | exact HB
        | exact AC | exact AQ | exact AD | exact AB | exact HK | exact MU | exact WMo | exact MG ]. }
  (* ---- 0x849f4: bnez a0, and a0 = 0 ---- *)
  step.
  try (replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by reflexivity).
  cbn [negb]. cbv iota.
  (* 0x849f8-0x849fc: the check of the 4-byte store at t, its shadow byte re-read through s8 *)
  destruct (cls_sh_load m 6180992 40960 (40 * s) 4 AC ltac:(lia) ltac:(lia) ltac:(lia)) as (kt & MKt & SKt).
  change (4 - 1) with 3 in SKt. unfold ASAN_K in MKt.
  pose proof (cls_shc RNG (40 * s) RSC ltac:(lia)) as RKt. unfold ASAN_K in RKt.
  pose proof (rd1 m _ _ MKt) as RDt. clear MKt.
  step.
  step. rewrite sxb_eq0.
  destruct SKt as [C|[C Cu]].
  - rewrite (proj2 (Z.eqb_eq _ _) C). cbn [negb]. cbv iota. apply STT.
  - rewrite (proj2 (Z.eqb_neq (bv_signed kt) 0) ltac:(lia)). cbn [negb]. cbv iota.
    (* 0x84b1c-0x84b28: the handler goes back to the store *)
    step. step.
    step. rewrite ?cls_wrap64_7. rewrite land7, (unsigned_lit (6180992 + 40 * s)) by lia.
    rewrite (cls_lts_lit ((6180992 + 40 * s) mod 8 + 3) kt ltac:(lia)).
    rewrite (proj2 (Z.ltb_lt _ _) C). cbn [negb]. cbv iota.
    step. apply STT.
Qed.
