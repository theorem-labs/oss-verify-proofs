From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Bytes ZBridge Step Arr Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegSetModel GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import reac_headamp_tx_set_c reac_headamp_tx_effective_c reac_headamp_default_c SetRead.
Import ListNotations.
Open Scope Z_scope.

Lemma eff_set_T : forall T t c q v, length T = 460%nat -> t <> 0 -> 0 <= c < 48 -> legal q v ->
  eff (set_T T c q v) t c q = v.
Proof.
  intros T t c q v HL Ht Hc Hl. destruct (legal_bound q v Hl) as [Hq Hv].
  rewrite eff_cell by lia. rewrite !tb_set_T by lia. ncond. reflexivity.
Qed.

Lemma upd_upd_bytes : forall (l : list byte) i b, (i < length l)%nat -> upd l i b = upd_bytes l i [b].
Proof.
  intros l i b H. rewrite upd_firstn_skipn by exact H. unfold upd_bytes. cbn [length app].
  replace (i + 1)%nat with (S i) by lia. reflexivity.
Qed.

Theorem seg_set_turn_holds : reac_headamp_tx_set_contract -> reac_headamp_tx_effective_contract ->
  reac_headamp_default_contract -> seg_set_turn.
Proof.
  intros SET EFF DFL. unfold seg_set_turn. intros x t i ms H.
  apply evt_canon; [eqv_inv_tac|].
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                  Hsp & HSV & HS16 & Hsv12 & HS63) &
                 Hn & Hi & Hs0 & (Hs27 & Hs25) & Hs18 & Hs9 & Hs26 & HSL & (HN40 & HN48) & HTA).
  revert HTA. destruct (tables_at (x_pl x) i) as [[T ws] st] eqn:ETi.
  intros ((HTb & HT16 & HTl & HT) & (Hwl & Hstl & HWS & HSTA) & HHr & HI1).
  unfold slots in HSL. unfold wnot, w64 in HN40, HN48.
  pose proof HTb as HTb'. unfold blk in HTb'.
  assert (ELS : LLVM_STACK = 8800) by reflexivity.
  rewrite ELS in HTb', Hpd, Hrs.
  assert (ELR : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  assert (HSlo : 8800 <= x_S x) by (destruct HST as (H0 & _); rewrite ELS in H0; lia).
  assert (ESPL : SPL x = x_S x - 608) by reflexivity.
  assert (Exn : x_n x = Z.of_nat (length (x_pl x))) by reflexivity.
  assert (ESZ : cells_size (map C8 (rev (x_sv x) ++ [x_ra x])) = 104%nat) by (apply saved_size; exact Hsv12).
  assert (HT4 : t mod 4 = 0) by (Z.div_mod_to_equations; lia).
  set (pos := snd (cells_upto (x_pl x) i)) in *.
  pose proof (cells_upto_le (x_pl x) i) as Hpos. fold pos in Hpos.
  rewrite canon_rg by exact Hsvc.
  rewrite Hpc, HF, Hfc, Hrv, Hro, Hs0, Hs27, Hs25, Hs18, Hs9, Hs26, Hsp.
  set (m00 := ms_mem ms) in *.
  destruct (CB_bytes _ _ _ _ HPL) as (HPB & _ & _).
  destruct (CB_bytes _ _ _ _ HT) as (HTB & HTW & _).
  assert (MU : munch [(x_S x - 8800, x_S x); (t, t + 460)] m00 m00) by apply munch_refl.
  assert (WM : wmono rsegs m00 m00) by apply wmono_refl.
  unfold w64, PC_SET.
  eapply evt_cut.
  { eapply (read_block SET EFF DFL) with (t := t) (p := x_p x) (pl := x_pl x) (pos := pos) (T := T); qprem. }
  intros ms1 Hpost. revert Hpost.
  pose proof (cell_rd_ok (x_pl x) pos) as Hok.
  pose proof (cell_rd_le (x_pl x) pos Hpos) as Hpos'.
  destruct (cell_rd (x_pl x) pos) as [[[c q] v] pos'] eqn:ECR.
  destruct Hok as (Hc & Hq & Hv). cbn [snd] in Hpos'.
  assert (ETS : tables_at (x_pl x) (S i) = set_step (T, ws, st) (c, q, v))
    by (rewrite tables_at_S, ETi; change (snd (cells_upto (x_pl x) i)) with pos; rewrite ECR; reflexivity).
  assert (EPS : snd (cells_upto (x_pl x) (S i)) = pos')
    by (rewrite pos_S; change (snd (cells_upto (x_pl x) i)) with pos; rewrite ECR; reflexivity).
  assert (Hns : 0 <= nset (x_pl x) < 256) by (unfold nset; apply rd8_range).
  intros (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & s31 & s41 & s51 & s61 & s71 &
          s81 & s91 & s111 & t31 & t41 & t51 & t61 & m1 & -> & -> & -> & -> & -> & -> & -> & Hs3 & HM).
  revert Hs3 HM. destruct ((c <? 48) && legalb q v) eqn:EL; intros Hs3 HM.
  - specialize (Hs3 eq_refl). subst s31.
    destruct HM as (HTB' & MUc & WMc).
    pose proof EL as ELp. apply andb_true_iff in ELp. destruct ELp as [ELc ELq].
    apply Z.ltb_lt in ELc. apply legalb_legal in ELq; [|lia|lia].
    destruct (legal_bound q v ELq) as [Hq3 _].
    assert (HMI1 : mem_inv rsegs m1) by (eapply mem_inv_munch; eauto).
    transport_after_call rsegs m00 m1 MUc WMc. clear MUc WMc.
    change (if true then 0 else -1) with 0.
    zstep. brx.
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply EFF with (T := set_T T c q v);
        [reflexivity | reflexivity | reflexivity | lia | lia |
         right; split; [apply len_set_T; lia | split; [exact HTB' | exact HT4]]]. }
    intros ms2 (t02 & t12 & t22 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 & ->).
    fix_ret. rewrite eff_set_T by (first [lia | assumption]).
    zstep. brx.
    zstep. brx.
    zstep. zstep.
    rewrite ?Z.shiftl_mul_pow2 by lia. try (change (2 ^ 1) with 2).
    zstep. zstep. brx.
    zstep. brx.
    zstep. zstep. zstep. rewrite ?zb_lxor_ones by (Z.div_mod_to_equations; lia). zstep. brx.
    zstep.
    assert (HT1 : rw_cells rsegs m1 t [CB 460 (set_T T c q v)])
      by (apply rw_cells_CB; [apply len_set_T; lia | exact HTB' | exact HTW]).
    clear HTB'.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ HWS) as U1.
    assert (HS1 : store_ok rsegs m1 (wa (SPL x + 360 + (3 * c + q))) 1 = true)
      by (apply (u8arr_store_ok _ _ _ _ (3 * c + q) _ U1); [rewrite Hwl; lia | reflexivity]).
    zstep.
    change (Z_to_bv 64 (SPL x + 360 + (3 * c + q))) with (wa (SPL x + 360 + (3 * c + q))).
    rewrite (le1_small 1) by lia.
    pose proof (u8arr_write _ _ _ _ (3 * c + q) (Z_to_bv 8 1) U1 ltac:(rewrite Hwl; lia)) as U1'.
    clear HWS.
    transport_chunks rsegs m1 (SPL x + 360 + (3 * c + q)) [Z_to_bv 8 1].
    footprint_after_store rsegs m1 (SPL x + 360 + (3 * c + q)) [Z_to_bv 8 1].
    apply (mem_inv_store rsegs m1 (wa (SPL x + 360 + (3 * c + q))) [Z_to_bv 8 1]) in HMI1; [|exact HS1].
    set (m2 := write_to_mem m1 (wa (SPL x + 360 + (3 * c + q))) [Z_to_bv 8 1]) in *.
    clear HS1.
    zstep. zstep. brx.
    zstep. zstep. zstep. rewrite ?zb_lxor_ones by (Z.div_mod_to_equations; lia). zstep. brx.
    zstep.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ HSTA) as U2.
    assert (HS2 : store_ok rsegs m2 (wa (SPL x + 216 + (3 * c + q))) 1 = true)
      by (apply (u8arr_store_ok _ _ _ _ (3 * c + q) _ U2); [rewrite Hstl; lia | reflexivity]).
    zstep.
    change (Z_to_bv 64 (SPL x + 216 + (3 * c + q))) with (wa (SPL x + 216 + (3 * c + q))).
    rewrite (le1_small v) by lia.
    pose proof (u8arr_write _ _ _ _ (3 * c + q) (Z_to_bv 8 v) U2 ltac:(rewrite Hstl; lia)) as U2'.
    clear HSTA U2.
    transport_chunks rsegs m2 (SPL x + 216 + (3 * c + q)) [Z_to_bv 8 v].
    footprint_after_store rsegs m2 (SPL x + 216 + (3 * c + q)) [Z_to_bv 8 v].
    apply (mem_inv_store rsegs m2 (wa (SPL x + 216 + (3 * c + q))) [Z_to_bv 8 v]) in HMI1; [|exact HS2].
    set (m3 := write_to_mem m2 (wa (SPL x + 216 + (3 * c + q))) [Z_to_bv 8 v]) in *.
    clear HS2.
    apply rw_cells_of_u8arr in U1'. apply rw_cells_of_u8arr in U2'.
    rewrite upd_length, Hwl, upd_upd_bytes in U1' by lia.
    rewrite upd_length, Hstl, upd_upd_bytes in U2' by lia.
    change (upd_bytes ws (Z.to_nat (3 * c + q)) [Z_to_bv 8 1]) with (ws_put ws c q 1) in U1'.
    change (upd_bytes st (Z.to_nat (3 * c + q)) [Z_to_bv 8 v]) with (ws_put st c q v) in U2'.
    assert (HTl' : length (set_T T c q v) = 460%nat) by (apply len_set_T; lia).
    assert (Hwl' : length (ws_put ws c q 1) = 144%nat) by (apply len_ws_put; lia).
    assert (Hstl' : length (ws_put st c q v) = 144%nat) by (apply len_ws_put; lia).
    pose proof (Hrel_set T ws st c q v HTl Hwl Hstl ltac:(lia) ltac:(lia) ltac:(lia) HHr) as HHr'.
    pose proof (I1_set_T T c q v HTl ltac:(lia) ELq HI1) as HI1'.
    zstep. zstep.
    rewrite ?swrap32_mod64. rewrite swrap32_id by lia.
    if_cases HCX; zify_cond HCX.
    + apply evt_done. split; [split; [exact MU | exact WM]|].
      right. split; [lia|].
      assert (Eni : Z.to_nat (nset (x_pl x)) = S i) by lia.
      unfold At_unset0, T_end, ws_end, st_end, tables_end, pos_end. rewrite Eni, ETS, EPS, set_step_cell, EL.
      cbv beta iota. cbn [fst snd].
      fin_at.
    + zstep.
      apply evt_done. split; [split; [exact MU | exact WM]|].
      left. split; [lia|].
      unfold At_set. rewrite ETS, EPS, set_step_cell, EL. cbv beta iota.
      fin_at.
  - subst m1.
    change (if false then 0 else -1) with (-1).
    zstep. brx.
    zstep. zstep.
    rewrite ?swrap32_mod64. rewrite swrap32_id by lia.
    if_cases HCX; zify_cond HCX.
    + apply evt_done. split; [split; [exact MU | exact WM]|].
      right. split; [lia|].
      assert (Eni : Z.to_nat (nset (x_pl x)) = S i) by lia.
      unfold At_unset0, T_end, ws_end, st_end, tables_end, pos_end. rewrite Eni, ETS, EPS, set_step_cell, EL.
      cbv beta iota. cbn [fst snd].
      fin_at.
    + zstep.
      apply evt_done. split; [split; [exact MU | exact WM]|].
      left. split; [lia|].
      unfold At_set. rewrite ETS, EPS, set_step_cell, EL. cbv beta iota.
      fin_at.
Qed.
