From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegCLib reac_grant_alloc_fits_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Theorem seg_rawsweep_holds : reac_grant_build_sweep_need -> reac_grant_alloc_fits_contract -> seg_rawsweep.
Proof.
  intros BS AF. unfold reac_grant_build_sweep_need in BS. unfold reac_grant_alloc_fits_contract in AF.
  unfold seg_rawsweep. intros x t s ms H.
  apply evt_canon; [apply eqv_and; [apply eqv_kept | apply eqv_At_freeSW2] |].
  destruct x as [Sx ra gp tp sv p pl F fc].
  unfold At_mallocSW2_ret, body, common, cur5, table, arrays, SPL, x_n, hd in H.
  cbn [x_S x_ra x_gp x_tp x_sv x_p x_pl x_F x_fc] in H.
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) & Hsp & HSV & HS16 & HSVl & HS63) & Hn & Hs0 & (Hs21 & Hs9) & Ha0 & HRAW & (HTb & HT16 & HTl & HT) & (HWl & HSTl & HWS & HSTA) & HH & HI & Hsb & Hst & (junk & HSW)).
  rewrite canon_MS by exact Hsvc. unfold mkR_of.
  rewrite Hpc, HF, Hfc, Hrv, Hro.
  assert (E2 : Sem.reg_get (ms_regs ms) 2 = w64 (Sx - LLVM_FRAME)) by exact Hsp.
  assert (E3 : Sem.reg_get (ms_regs ms) 3 = gp) by exact Hgp.
  assert (E4 : Sem.reg_get (ms_regs ms) 4 = tp) by exact Htp.
  assert (E8 : Sem.reg_get (ms_regs ms) 8 = w64 t) by exact Hs0.
  assert (E21 : Sem.reg_get (ms_regs ms) 21 = w64 (p + Z.of_nat (pos_raw pl))) by exact Hs21.
  assert (E25 : Sem.reg_get (ms_regs ms) 25 = w64 (Z.of_nat (length pl) - Z.of_nat (pos_raw pl))) by exact Hs9.
  assert (E10 : Sem.reg_get (ms_regs ms) 10 = w64 s) by exact Ha0.
  rewrite E2, E3, E4, E8, E21, E25, E10. clear E2 E3 E4 E8 E21 E25 E10 Hsp Hgp Htp Hs0 Hs21 Hs9 Ha0.
  repeat match goal with |- context [Sem.reg_get (ms_regs ms) ?k] =>
    let v := fresh "r" in generalize (Sem.reg_get (ms_regs ms) k) as v; intro v end.
  change (YK11.seg_rom rsegs) with (PropExec.seg_rom rsegs).
  unfold kept. cbn [x_S].
  revert HPL HST HMI HSV HT HWS HSTA HRAW HSW Hrow.
  generalize (ms_mem ms) as m0. intros m0 HPL HST HMI HSV HT HWS HSTA HRAW HSW Hrow.
  assert (HRL : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  clear Hpc HF Hfc Hrv Hsvc Hro.
  unfold w64 in *. rewrite ?LLVM_STACK_val, ?LLVM_FRAME_val in *.
  unfold blk, x_n in HTb, Hsb; cbn [x_S x_p x_pl] in HTb, Hsb; rewrite ?LLVM_STACK_val in HTb, Hsb.
  destruct (raw_rd pl) as [[rb rw] pr] eqn:ERAW.
  cbv beta iota zeta in HRAW. apply rw_cells_two_inv in HRAW.
  assert (Hrb : 0 <= rb < 256 /\ 0 <= rw < 256).
  { unfold raw_rd in ERAW. destruct (rd8 pl (pos_end pl)) as [b1 p1] eqn:E1. destruct (rd8 pl p1) as [b2 p2] eqn:E2.
    inversion ERAW; subst. pose proof (rd8_val pl (pos_end pl)) as V1. pose proof (rd8_val pl p1) as V2.
    rewrite E1 in V1. rewrite E2 in V2. cbn in V1, V2. lia. }
  pose proof HST as (HSx0 & _ & _).
  destruct (stk_split rsegs m0 (Sx - 8800) (Sx - 608) Sx HST ltac:(lia)) as [HSTlo HSThi]. clear HST.
  pose proof (munch_refl [(Sx - 8800, Sx - 608); (s, s + 4352)] m0) as MUf.
  pose proof (munch_refl [(Sx - 8800, Sx); (s, s + 4352)] m0) as MUc.
  pose proof (wmono_refl rsegs m0) as WM.
  apply frz_in in HPL, HSV, HT, HWS, HSTA.
  assert (EPR : pos_raw pl = pr) by (unfold pos_raw; rewrite ERAW; reflexivity). rewrite EPR in *.
  pose proof (rw_cells_CB_bytes _ _ _ _ (frz_out _ HT)) as [TB _].
  unfold PC_MALLOC_SW2_RET.
  gz 0x15380.
  assert (EB1 : bs_res s (Sx - 608 + 66) 128 rb rw = if fits rb rw then 8 + 3 * rw else -1).
  { destruct (fits rb rw) eqn:Ef.
    - pose proof (fits_range _ _ Ef). apply bs_res_ok; [lia | lia | exact Ef | lia].
    - apply bs_res_bad. right; right; left; exact Ef. }
  eapply evt_cut.
  { eapply BS with (s := s) (mx := 128) (al := Sx - 608 + 66) (t := t) (lo := Sx - 8800) (base := rb) (w := rw)
      (T := T_end pl) (junk := firstn (Z.to_nat (34 * (8 + 3 * rw))) junk).
    all: try side.
    - intros _. split; [lia|]. split; [lia|]. split; [exact (proj1 (rw_cells_CB_bytes _ _ _ _ (rw_cells_two _ _ _ _ HRAW))) | unl; lia].
    - intros Hres. assert (Ef : fits rb rw = true) by (destruct (fits rb rw); [reflexivity | rewrite EB1 in Hres; lia]).
      pose proof (fits_range _ _ Ef). split; [apply (rw_cells_prefix _ _ 4352); [exact HSW | lia] | unl; lia]. }
  intros ms1 (t0' & t1' & t2' & rr & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & Hr & MU1 & WM1 & MI1 & ST1 & RW1 & SW1).
  retpc. rewrite EB1 in Hr. clear SW1. rewrite (unsigned_lit (Sx - 608)) in MU1, ST1 by lia.
  assert (EW1 : bs_win s (Sx - 608 + 66) 128 rb rw = if fits rb rw then [(s, s + 34 * (8 + 3 * rw))] else []).
  { destruct (fits rb rw) eqn:Ef; [apply bs_win_ok; [rewrite EB1; reflexivity | lia] | apply bs_win_bad; rewrite EB1; reflexivity]. }
  rewrite EW1 in MU1. subst rr.
  destruct (fits rb rw) eqn:Ef; cbv beta iota in MU1; [pose proof (fits_range _ _ Ef) as Hfr|];
    xcall m0 m1 MU1 WM1.
  all: gz 0x152f4.
  all: eapply evt_cut; [ eapply AF with (base := rb) (width := rw); [ apply zxb_lit8; lia | apply zxb_lit8; lia | unfold int32; lia | unfold int32; lia | intros; lia ] | ].
  all: intros ms2 (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & ->).
  all: retpc; rewrite Ef; cbn [Z.b2z].
  all: gz 0x15380.
  all: eapply evt_cut; [ eapply BS with (s := 0) (mx := 1) (al := Sx - 608 + 66) (t := t) (lo := Sx - 8800) (base := rb) (w := rw)
      (T := T_end pl) (junk := []); try side;
      [ intros _; split; [lia|]; split; [lia|]; split; [exact (proj1 (rw_cells_CB_bytes _ _ _ _ (rw_cells_two _ _ _ _ HRAW))) | unl; lia]
      | intros Hres; rewrite bs_res_bad in Hres by (left; reflexivity); lia ] | ].
  all: intros ms3 (u0 & u1 & u2 & rr & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & m3 & -> & Hr & MU3 & WM3 & MI3 & ST3 & RW3 & SW3).
  all: retpc; rewrite bs_res_bad in Hr by (left; reflexivity); subst rr; clear SW3.
  all: rewrite (unsigned_lit (Sx - 608)) in MU3, ST3 by lia; rewrite bs_win_bad in MU3 by (apply bs_res_bad; left; reflexivity).
  all: lazymatch type of MU3 with munch _ ?mo _ => xcall mo m3 MU3 WM3 end.
  all: gz 0x15380.
  all: eapply evt_cut; [ eapply BS with (s := s) (mx := 128) (al := 0) (t := t) (lo := Sx - 8800) (base := 0) (w := 0)
      (T := T_end pl) (junk := []); try side;
      intros Hres; first [ lia | rewrite bs_res_bad in Hres by (right; left; reflexivity); lia ] | ].
  all: intros ms4 (v0 & v1 & v2 & rr & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & m4 & -> & Hr & MU4 & WM4 & MI4 & ST4 & RW4 & SW4).
  all: retpc; rewrite bs_res_bad in Hr by (right; left; reflexivity); subst rr; clear SW4.
  all: rewrite (unsigned_lit (Sx - 608)) in MU4, ST4 by lia; rewrite bs_win_bad in MU4 by (apply bs_res_bad; right; left; reflexivity).
  all: lazymatch type of MU4 with munch _ ?mo _ => xcall mo m4 MU4 WM4 end.
  all: gz 0x139f4.
  all: apply evt_done; split; [split; assumption|].
  all: thaw MUf WM.
  all: pose proof (stk_merge rsegs m4 _ _ _ ST4 HSThi ltac:(lia)) as HSTf.
  all: unfold At_freeSW2, body, common, cur5, table, arrays, blk, SPL, x_n, hd;
    cbn [x_S x_ra x_gp x_tp x_sv x_p x_pl x_F x_fc ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem MS].
  all: rewrite ?EPR.
  all: splits.
  all: try fin1.
Qed.
