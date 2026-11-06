From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegCLib SweepRowCheck SweepGroups.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import reac_headamp_default_c reac_ctrl_identity_poll_block_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma header_ranges : forall pl, 0 <= h_in (header pl) < 256 /\ 0 <= h_rows (header pl) < 256.
Proof.
  intros pl. unfold header.
  destruct (rd16 pl 0) as [u p1]. destruct (rd8 pl p1) as [i p2] eqn:E2. destruct (rd8 pl p2) as [r p3] eqn:E3.
  pose proof (rd8_val pl p1) as V2. pose proof (rd8_val pl p2) as V3. rewrite E2 in V2. rewrite E3 in V3.
  cbn in V2, V3 |- *. lia.
Qed.

Ltac fin_sweep MUF WMF SA SB SC Hrow STF S50F S194F HRL :=
  apply evt_done; split;
  [ split; [ eapply munch_weaken; [|exact MUF]; unfold sub_fp, sw1_size, hd; cbn [x_pl outside x_S];
             intros xx Hx; repeat split; try exact I; lia
           | exact WMF ] | ];
  apply frz_out in SA, SB, SC, Hrow;
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ SA MUF WMF ltac:(cbn [disjoint_from]; repeat split; lia)) as SAf;
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ SB MUF WMF ltac:(cbn [disjoint_from]; repeat split; lia)) as SBf;
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ SC MUF WMF ltac:(cbn [disjoint_from]; repeat split; lia)) as SCf;
  pose proof (bytes_at_transport rsegs _ _ _ _ _ Hrow MUF ltac:(cbn [disjoint_from]; rewrite HRL; repeat split; lia)) as ROWf;
  pose proof (stk_merge rsegs _ _ _ _ STF SAf ltac:(lia)) as K1;
  pose proof (stk_merge rsegs _ _ _ _ K1 S50F ltac:(lia)) as K2;
  pose proof (stk_merge rsegs _ _ _ _ K2 SBf ltac:(lia)) as K3;
  pose proof (stk_merge rsegs _ _ _ _ K3 S194F ltac:(lia)) as K4;
  pose proof (stk_merge rsegs _ _ _ _ K4 SCf ltac:(lia)) as K5;
  clear SA SB SC Hrow SAf SBf SCf K1 K2 K3 K4;
  thaw MUF WMF;
  unfold At_freeSW1, at_after_admit, body, common, cur, slots, cslot, table, arrays, blk, SPL, x_n, sw1_size, hd, ok;
  cbn [x_S x_ra x_gp x_tp x_sv x_p x_pl x_F x_fc ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS];
  splits; try fin1.

Theorem seg_sweep_holds : reac_grant_build_sweep_need -> check_groupa_need -> reac_headamp_default_contract ->
  reac_ctrl_identity_poll_block_contract -> bcmp_contract -> seg_sweep.
Proof.
  intros BS GAN DFL POLL BCMP. unfold reac_grant_build_sweep_need in BS.
  unfold seg_sweep. intros x t s ms H.
  apply evt_canon; [apply eqv_and; [apply eqv_kept | apply eqv_At_freeSW1] |].
  destruct x as [Sx ra gp tp sv p pl F fc].
  unfold At_mallocSW1_ret, sw1_size, at_after_admit, body, common, cur, slots, cslot, table, arrays, SPL, x_n, hd in H.
  cbn [x_S x_ra x_gp x_tp x_sv x_p x_pl x_F x_fc] in H.
  destruct H as ((((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                   Hsp & HSV & HS16 & HSVl & HS63) & Hn & Hs0 & (Hs1 & Hs9) & HSL & HCS & (HTb & HT16 & HTl & HT) &
                   (HWl & HSTl & HWS & HSTA) & HH & HI) & Hok & Ha0 & H18 & H19 & H20 & HAB & Hsb & Hst & (junk & HSW)).
  rewrite canon_MS by exact Hsvc. unfold mkR_of.
  rewrite Hpc, HF, Hfc, Hrv, Hro.
  assert (E2 : Sem.reg_get (ms_regs ms) 2 = w64 (Sx - LLVM_FRAME)) by exact Hsp.
  assert (E3 : Sem.reg_get (ms_regs ms) 3 = gp) by exact Hgp.
  assert (E4 : Sem.reg_get (ms_regs ms) 4 = tp) by exact Htp.
  assert (E8 : Sem.reg_get (ms_regs ms) 8 = w64 t) by exact Hs0.
  assert (E9 : Sem.reg_get (ms_regs ms) 9 = w64 (p + Z.of_nat (pos_end pl))) by exact Hs1.
  assert (E25 : Sem.reg_get (ms_regs ms) 25 = w64 (Z.of_nat (length pl) - Z.of_nat (pos_end pl))) by exact Hs9.
  assert (E10 : Sem.reg_get (ms_regs ms) 10 = w64 s) by exact Ha0.
  assert (E18 : Sem.reg_get (ms_regs ms) 18 = w64 (h_rows (header pl))) by exact H18.
  assert (E19 : Sem.reg_get (ms_regs ms) 19 = w64 (h_in (header pl))) by exact H19.
  assert (E20 : Sem.reg_get (ms_regs ms) 20 = w64 (h_base (header pl))) by exact H20.
  rewrite E2, E3, E4, E8, E9, E25, E10, E18, E19, E20.
  clear E2 E3 E4 E8 E9 E25 E10 E18 E19 E20 Hsp Hgp Htp Hs0 Hs1 Hs9 Ha0 H18 H19 H20.
  repeat match goal with |- context [Sem.reg_get (ms_regs ms) ?k] =>
    let v := fresh "r" in generalize (Sem.reg_get (ms_regs ms) k) as v; intro v end.
  change (YK11.seg_rom rsegs) with (PropExec.seg_rom rsegs).
  unfold kept. cbn [x_S].
  revert HPL HST HMI HSV HSL HCS HT HWS HSTA HAB HSW Hrow.
  generalize (ms_mem ms) as m0. intros m0 HPL HST HMI HSV HSL HCS HT HWS HSTA HAB HSW Hrow.
  clear Hpc HF Hfc Hrv Hsvc Hro.
  assert (HRL : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  unfold w64 in *. rewrite ?LLVM_STACK_val, ?LLVM_FRAME_val in *.
  unfold blk, x_n in HTb, Hsb; cbn [x_S x_p x_pl] in HTb, Hsb; rewrite ?LLVM_STACK_val in HTb, Hsb.
  unfold ok in Hok. pose proof (fits_range _ _ Hok) as Hfit. pose proof (header_ranges pl) as Hhr.
  set (base := h_base (header pl)) in *. set (w := h_in (header pl)) in *. set (rows := h_rows (header pl)) in *.
  pose proof HST as (HSx0 & _ & _).
  destruct (stk_split rsegs m0 (Sx - 8784) (Sx - 592) Sx HST ltac:(lia)) as [ST HS1]. clear HST.
  destruct (stk_split rsegs m0 (Sx - 592) (Sx - 592 + 50) Sx HS1 ltac:(lia)) as [SA HS2]. clear HS1.
  destruct (stk_split rsegs m0 (Sx - 592 + 50) (Sx - 592 + 84) Sx HS2 ltac:(lia)) as [S50 HS3]. clear HS2.
  destruct (stk_split rsegs m0 (Sx - 592 + 84) (Sx - 592 + 194) Sx HS3 ltac:(lia)) as [SB HS4]. clear HS3.
  destruct (stk_split rsegs m0 (Sx - 592 + 194) (Sx - 592 + 198) Sx HS4 ltac:(lia)) as [S194 SC]. clear HS4.
  pose proof (rw_cells_CB_bytes _ _ _ _ HT) as [TB _].
  pose proof (rw_cells_CB_bytes _ _ _ _ HWS) as [WB _].
  pose proof (rw_cells_CB_bytes _ _ _ _ HSTA) as [STB _].
  pose proof (rw_cells_CB_bytes _ _ _ _ HAB) as [AB _].
  pose proof HCS as HC32.
  pose proof Hrow as ROW0.
  apply frz_in in HPL, HSV, HSL, HCS, HT, HWS, HSTA, HAB, HSW, SA, SB, SC, Hrow, HC32.
  unfold PC_MALLOC_SW1_RET. zstep. ifc. zstep. zstep. zstep. zstep. zstep.
  assert (EB : bs_res s (Sx - 592 + 198) rows base w = if rows <? 8 + 3 * w then -1 else 8 + 3 * w).
  { destruct (Z.ltb_spec rows (8 + 3 * w)).
    - apply bs_res_bad. right; right; right. lia.
    - apply bs_res_ok; [lia | lia | exact Hok | lia]. }
  eapply evt_cut.
  { eapply BS with (s := s) (mx := rows) (al := Sx - 592 + 198) (t := t) (lo := Sx - 8784) (base := base) (w := w)
      (T := T_end pl) (junk := firstn (Z.to_nat (34 * (8 + 3 * w))) junk).
    all: try side.
    - intros _. split; [lia|]. split; [lia|]. split; [exact AB | unl; lia].
    - intros Hres. rewrite EB in Hres. destruct (Z.ltb_spec rows (8 + 3 * w)); [lia|].
      split; [apply (rw_cells_prefix _ _ (Z.to_nat (Z.max rows 1 * 34))); [exact (frz_out _ HSW) | lia] |].
      unl. rewrite Z.max_l in Hsb, Hst by lia. lia. }
  intros ms1 (u0 & u1 & u2 & rr & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m1 & -> & Hr & MU1 & WM1 & MI1 & ST1 & ROW1 & SW1).
  retpc. rewrite EB in Hr. subst rr. rewrite (unsigned_lit (Sx - 592)) in MU1, ST1 by lia.
  destruct (Z.ltb_spec rows (8 + 3 * w)) as [Hlt | Hge].
  - rewrite bs_win_bad in MU1 by exact EB.
    pose proof (bytes_at_transport rsegs _ m0 m1 _ _ AB MU1 ltac:(cbn [disjoint_from length]; repeat split; lia)) as AB1.
    pose proof (bytes_byte_read m1 _ _ 1 AB1 ltac:(cbn; lia)) as R199. cbn [nth Z.of_nat] in R199.
    assert (Hw256 : 0 <= w < 256) by lia.
    zstep. cbv beta. rewrite (bv8_small w Hw256).
    zstep. rewrite ?Z.shiftl_mul_pow2 by lia. zstep. zstep. zstep.
    rewrite (proj2 (Z.ltb_lt rows (w * 2 + w + 8))) by lia. cbn [Z.b2z].
    zstep. zstep.
    replace (Z.lor 18446744073709551615 (w * 2 + w + 8)) with 18446744073709551615
      by (rewrite <- (unsigned_lit (w * 2 + w + 8)) by lia; rewrite lor_ones_w; reflexivity).
    zstep. ifc. zstep. ifc. zstep.
    assert (MUF : munch [(Sx - 8784, Sx - 592); (Sx - 592 + 50, Sx - 592 + 84); (Sx - 592 + 194, Sx - 592 + 198);
                         (s, s + Z.max rows 1 * 34)] m0 m1).
    { eapply munch_weaken; [|exact MU1]. unfold sub_fp. intros xx Hx. cbn [outside] in *. repeat split; try exact I; lia. }
    rename WM1 into WMF, MI1 into MIF, ST1 into STF.
    pose proof (stk_transport_disjoint rsegs _ _ _ _ _ S50 MU1 WMF ltac:(cbn [disjoint_from]; repeat split; lia)) as S50F.
    pose proof (stk_transport_disjoint rsegs _ _ _ _ _ S194 MU1 WMF ltac:(cbn [disjoint_from]; repeat split; lia)) as S194F.
    clear MU1 S50 S194 ST TB WB STB AB AB1 R199 ROW0 ROW1 SW1 HC32.
    fin_sweep MUF WMF SA SB SC Hrow STF S50F S194F HRL.
  - rewrite bs_win_ok in MU1 by (first [exact EB | lia]).
    rewrite Z.max_l in Hsb, Hst, HSW by lia.
    pose proof (proj1 (rw_cells_CB_bytes _ _ _ _ (SW1 EB))) as SWB.
    assert (MV1 : minv Sx s t base w rows (T_end pl) (ws_end pl) (st_end pl) m0 m1).
    { unfold minv. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      - eapply munch_weaken; [|exact MU1]. unfold sub_fp, Wf. intros xx Hx. cbn [outside] in *. repeat split; try exact I; lia.
      - exact WM1.
      - exact MI1.
      - exact ST1.
      - eapply stk_transport_disjoint; [exact S50 | exact MU1 | exact WM1 | cbn [disjoint_from]; repeat split; lia].
      - eapply stk_transport_disjoint; [exact S194 | exact MU1 | exact WM1 | cbn [disjoint_from]; repeat split; lia].
      - eapply bytes_at_transport; [exact TB | exact MU1 | cbn [disjoint_from]; rewrite HTl; repeat split; lia].
      - eapply bytes_at_transport; [exact WB | exact MU1 | cbn [disjoint_from]; rewrite HWl; repeat split; lia].
      - eapply bytes_at_transport; [exact STB | exact MU1 | cbn [disjoint_from]; rewrite HSTl; repeat split; lia].
      - eapply bytes_at_transport; [exact AB | exact MU1 | cbn [disjoint_from length]; repeat split; lia].
      - exact SWB. }
    eapply evt_cut.
    { eapply sweep_rest with (S := Sx) (s := s) (t := t) (base := base) (w := w) (rows := rows) (T := T_end pl)
        (ws := ws_end pl) (st := st_end pl) (m0 := m0) (m := m1) (v32 := Z_to_bv 64 (p + Z.of_nat (pos_end pl))).
      all: first [ reflexivity | assumption | exact MV1 | exact (frz_out _ HC32) | lia ]. }
    intros ms2 (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q18 & q19 & q20 & q21 & q22 & mf & -> & MVf).
    destruct MVf as (MUw & WMF & MIF & STF & S50F & S194F & _).
    assert (MUF : munch [(Sx - 8784, Sx - 592); (Sx - 592 + 50, Sx - 592 + 84); (Sx - 592 + 194, Sx - 592 + 198);
                         (s, s + Z.max rows 1 * 34)] m0 mf).
    { eapply munch_weaken; [|exact MUw]. unfold sub_fp, Wf. intros xx Hx. cbn [outside] in *.
      rewrite Z.max_l in Hx by lia. repeat split; try exact I; lia. }
    clear MUw MU1 WM1 MI1 ST1 S50 S194 ST TB WB STB AB ROW0 ROW1 SW1 SWB MV1 HC32.
    fin_sweep MUF WMF SA SB SC Hrow STF S50F S194F HRL.
Qed.
