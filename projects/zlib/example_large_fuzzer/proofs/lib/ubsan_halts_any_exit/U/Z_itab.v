From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit Z_itab_head Z_itab_next
     Z_itab_sub Z_itab_offs Z_itab_sort Z_itab_init Z_itab_kraft Z_itab_max Z_itab_nosym.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_itab_pure Z_itab_lx.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 ItableModel3 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].
Record ITCM (X : itx) (low ofsc : list cell) (cnt wk tb : arr) (m : mem) : Prop := mkITCM {
  cm_low : rw_cells usegs m (bv_unsigned (tx_sp X) + -208) low;
  cm_ofs : rw_cells usegs m (bv_unsigned (tx_sp X) + -166) ofsc;
  cm_cnt : u8arr usegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16));
  cm_sav : rw_cells usegs m (bv_unsigned (tx_sp X) + -104) (it_saved X);
  cm_stk : stk usegs m (tx_lo X) (bv_unsigned (tx_sp X) + -208);
  cm_work : u8arr usegs m (il_As (tx_L X) + 808) (u16s (av16 wk 288));
  cm_codes : u32arr usegs m (il_As (tx_L X) + 1384) (av32 tb 1444);
  cm_lens : u8arr usegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320));
  cm_mi : mem_inv usegs m;
  cm_mu : munch (tx_W1 X) (tx_m0 X) m;
  cm_wm : wmono usegs (tx_m0 X) m }.
Definition low_shape (low : list cell) : Prop := exists j0 ja jb jc jd j2, low = [CB 8 j0; CB 8 ja; CB 8 jb; CB 8 jc; CB 8 jd; CB 2 j2].
Definition ofs_shape (ofsc : list cell) : Prop :=
  exists o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15, ofsc = ofs_junk o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15.
Section Phases.
Variables (X : itx) (low ofsc : list cell) (cnt : arr) (m : mem).
Hypothesis CM : ITCM X low ofsc cnt (is_work (tx_s X)) (is_codes (tx_s X)) m.
Hypothesis LSH : low_shape low.
Hypothesis OSH : ofs_shape ofsc.
Hypothesis XO : itx_ok X.
Hypothesis IST0 : IST (tx_m0 X) (tx_L X) (tx_s X).
Hypothesis Ecnt : cnt = itm_count (tx_lens X) (tx_lofs X) (tx_codes X).
Hypothesis SAFE : it_safe (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)) = true.
Hypothesis ATY0 : ATY (tx_s X).
Hypothesis L15 : forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15.
Hypothesis Rtab : 0 <= tx_table X <= 1444.
Hypothesis Rb : 0 <= tx_bits X <= 15.
Hypothesis HCX : it_codes_ok (tx_ty X) (tx_codes X).
Lemma cnt_ty16 : ty16 cnt.
Proof. intros i. rewrite Ecnt, itm_count_eq. apply itm_count_k_range. Qed.
Lemma cnt_len : arr_len cnt = 16.
Proof. rewrite Ecnt, itm_count_eq. apply itm_count_k_len. Qed.
Lemma itab_KN : nosym_K X cnt m.
Proof.
  unfold nosym_K. intros until x31; intros EM0.
  destruct CM as [LOW OFSC CNT SAV ST Gw Gc Gl MI MU WM]. destruct LSH as (j0 & ja & jb & jc & jd & j2 & EL). destruct OSH as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & o12 & o13 & o14 & o15 & EO).
  subst low ofsc. pose proof (xo_arrs X XO) as (LL & LW & LT & _). destruct ATY0 as (TYL & TYW & TYT).
  pose proof (it_safe_max0 _ _ _ _ _ _ _ _ SAFE) as SM. cbv zeta in SM. rewrite <- Ecnt in SM. specialize (SM EM0).
  eapply itab_nosym; [exact LOW| reflexivity| exact OFSC| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact MI| exact MU| exact WM
    | exact XO| exact IST0| exact LW| exact LT| exact TYT| lia| lia|].
  unfold tx_call. apply inflate_table_eq_max0. rewrite <- Ecnt. exact EM0.
Qed.
Lemma itab_KR : kraft_K X cnt m.
Proof.
  unfold kraft_K. intros until x31; intros EM EMIN ER Rmax Rmin Rroot.
  destruct CM as [LOW OFSC CNT SAV ST Gw Gc Gl MI MU WM]. destruct LSH as (j0 & ja & jb & jc & jd & j2 & EL). destruct OSH as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & o12 & o13 & o14 & o15 & EO).
  subst low ofsc. pose proof (xo_arrs X XO) as (LL & LW & LT & _). destruct ATY0 as (TYL & TYW & TYT).
  assert (NZ : itm_max (itm_count (tx_lens X) (tx_lofs X) (tx_codes X)) <> 0) by (rewrite <- Ecnt; lia).
  eapply itab_kraft; [exact LOW| reflexivity| exact OFSC| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact Gl| exact MI| exact MU| exact WM
    | exact XO| exact IST0| apply cnt_ty16| apply cnt_len| exact LW| exact LT| |].
  -
    intros R. unfold tx_call. apply inflate_table_eq_reject; [exact NZ|]. rewrite <- Ecnt, EM. exact R.
  - intros NR x7' x16' x27' x29'.
    pose proof (it_safe_sort _ _ _ _ _ _ _ _ SAFE NZ) as SS. cbv zeta in SS. rewrite <- Ecnt, EM, EMIN, ER, LW, LT in SS.
    unfold tx_lens in SS at 2. rewrite LL in SS. specialize (SS NR). destruct SS as [SOK LP].
    eapply evt_cut; [eapply itab_offs; [exact LOW| reflexivity| exact OFSC| exact CNT| exact SAV| exact ST| exact Gw| exact Gc| exact Gl| exact MI| exact MU| exact WM
      | exact XO| apply cnt_ty16| apply cnt_len| exact LW| exact LT]|].
    intros ms' (y1 & y8 & y9 & y16 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & m' & -> & SM).
    eapply evt_cut; [eapply itab_sort; [exact SM| reflexivity| exact XO| intros i; rewrite itm_offs_eq; apply itm_offs_k_range| rewrite itm_offs_eq; apply itm_offs_k_len
      | exact TYW| exact LW| exact TYL| exact L15| rewrite <- it_sort_ok_eq; exact SOK]|].
    intros ms'' (z1 & z7 & z8 & z9 & z12 & z16 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31 & m'' & -> & SM').
    pose proof (itm_sort_k_len (tx_lens X) (tx_lofs X) (tx_codes X) (itm_offs cnt) (is_work (tx_s X))) as [_ LW1]. rewrite LW in LW1.
    rewrite itm_work_eq in LP.
    eapply itab_type; [apply ITSM_ITM; exact SM'| exact XO| exact IST0| exact Rroot| exact Rmax| exact Rmin| lia| apply cnt_ty16| apply cnt_len| exact TYT| exact LT
      | intros i; apply itm_sort_k_work_range; exact TYW| exact LW1| |].
    + intros NE. unfold tx_call. rewrite (inflate_table_eq_nospace (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)) NZ);
        rewrite <- ?Ecnt, ?EM, ?EMIN, ?ER; [rewrite itm_work_eq; reflexivity| exact NR| exact NE].
    + intros NE. destruct (LP NE) as (_ & _ & OK). split; [exact OK|]. split.
      { assert (HC19 : tx_ty X = CODES -> tx_codes X <= 19) by (intros E; pose proof HCX as H; rewrite E in H; exact H).
        assert (HL286 : tx_ty X = LENS -> tx_codes X <= 286) by (intros E; pose proof HCX as H; rewrite E in H; exact H).
        destruct (ity_code_cases (tx_ty X)) as [[_ TY]|[[_ TY]|[_ TY]]].
        3: { apply it_lx_dists. unfold itm_ctx. cbn [x_ty]. exact TY. }
        all: assert (H288 : 0 <= tx_codes X <= 288)
               by (pose proof (xo_codes X XO); first [pose proof (HC19 TY) | pose proof (HL286 TY)]; lia).
        all: assert (LX := it_lx_intro (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X)
                         (is_work (tx_s X)) cnt max min root H288 HC19 HL286
                         ltac:(intros i Hi; unfold tx_lens; pose proof (TYL i); split; [lia|];
                               replace i with (tx_lofs X + (i - tx_lofs X)) by lia; apply L15; pose proof (xo_codes X XO); lia)
                         ltac:(lia) Ecnt EM ltac:(lia) NR EMIN ER).
        all: rewrite itm_work_eq in LX; exact LX. }
      unfold tx_call. rewrite (inflate_table_eq_loop (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)) NZ);
        rewrite <- ?Ecnt, ?EM, ?EMIN, ?ER; [rewrite itm_work_eq; reflexivity| exact NR| exact NE].
Qed.
End Phases.
Definition cnt_post (X : itx) (low ofsc : list cell) (wk tb : arr) (x1 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
    : machine_state -> Prop :=
  fun ms' => exists x5 x6 x7 x8 x16 x17 x28 x29 x30 x31 m',
    ms' = MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
                 (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_CNTX) (tx_fc X) None m' (seg_rom usegs)
    /\ ITCM X low ofsc (itm_count_k (tx_lens X) (tx_lofs X) (tx_codes X)) wk tb m'.
Lemma itab_count_loop : forall n X low ofsc cnt wk tb m (k : Z) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x31 : word),
  ITCM X low ofsc cnt wk tb m -> cnt = itm_count_k (tx_lens X) (tx_lofs X) k ->
  Z.of_nat (cells_size low) = 42 -> Z.of_nat (cells_size ofsc) = 30 ->
  itx_ok X -> ty16 (tx_lens X) -> (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  0 <= k < tx_codes X -> tx_codes X - k <= Z.of_nat n -> arr_len wk = 288 -> arr_len tb = 1444 ->
  evt usegs (cnt_post X low ofsc wk tb x1 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) (wz 0) (wz (18446744073709551615 - tx_lensA X))
             (wz (18446744073709551615 - (bv_unsigned (tx_sp X) + -136))) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808))
             (wz (2 * k)) (wz (bv_unsigned (tx_sp X) + -136))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (2 * tx_codes X)) (wz 16) (wz (tx_lensA X + 2 * k)) x31) (tx_F X) (wz PC_IT_CNT) (tx_fc X) None m (seg_rom usegs)).
Proof.
  induction n as [|n IH]; intros until x31; intros CM Ec SZ SZO XO TYL L15 Rk Rn LW LT; [lia|].
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  destruct CM as [LOW OFSC CNT SAV ST Gw Gc Gl MI MU WM]. unfold tx_W1 in MU. pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c. pose proof (av16_zlength wk 288 ltac:(lia)) as L16w.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  assert (RLA : 0 < tx_lensA X /\ tx_lensA X + 2 * tx_codes X < 2 ^ 62 /\ tx_lensA X mod 2 = 0) by (unfold tx_lensA; lia).
  assert (LC : arr_len cnt = 16) by (rewrite Ec; apply itm_count_k_len).
  assert (TYC : ty16 cnt) by (intros i; rewrite Ec; apply itm_count_k_range).
  pose proof (L15 k ltac:(lia)) as Rl. pose proof (TYL (tx_lofs X + k)) as Rl0. set (len := arr_get (tx_lens X) (tx_lofs X + k)) in *.
  pose proof (TYC len) as Rc. set (c := arr_get cnt len) in *.
  unfold PC_IT_CNT. ustep PC_IT_TRAP. zs. br_false.
  pose proof (u16arr_read usegs _ (il_As (tx_L X) + 168) (av16 (tx_lens X) 320) (tx_lofs X + k) _ (wa (tx_lensA X + 2 * k)) Gl
                (av16_nth (tx_lens X) 320 (tx_lofs X + k) ltac:(lia)) ltac:(lia) ltac:(unfold tx_lensA; f_equal; lia)) as RD.
  zs. rewrite zx16_small by lia. clear RD. fold len.
  ustep PC_IT_TRAP. zs. rewrite (shl1 len). ustep PC_IT_TRAP. zs.
  pose proof (u16arr_read usegs _ (bv_unsigned (tx_sp X) + -136) (av16 cnt 16) len (wz c) (wa (bv_unsigned (tx_sp X) + -136 + 2 * len)) CNT (av16_nth cnt 16 len ltac:(lia)) ltac:(lia) eq_refl) as RD.
  zs. clear RD. zs. zs.
  st16 CNT cnt 16 (bv_unsigned (tx_sp X) + -136) len (wrap16 (c + 1)) ltac:(rewrite le2_swrap16_add by lia; reflexivity).
  assert (Ec' : arr_set cnt len (wrap16 (c + 1)) = itm_count_k (tx_lens X) (tx_lofs X) (k + 1)).
  { rewrite itm_count_k_step by lia. cbv zeta. rewrite <- Ec. reflexivity. }
  zs. zs. br_cases K.
  -
    replace (2 * k + 2) with (2 * (k + 1)) by lia. replace (tx_lensA X + 2 * k + 2) with (tx_lensA X + 2 * (k + 1)) by lia.
    eapply (IH X low ofsc _ wk tb _ (k + 1)); [| exact Ec'| exact SZ| exact SZO| exact XO'| exact TYL| exact L15| lia| lia| exact LW| exact LT].
    split; assumption.
  -
    apply evt_done. unfold cnt_post, PC_IT_CNTX. do 11 eexists. split; [reflexivity|].
    replace (tx_codes X) with (k + 1) by lia. rewrite <- Ec'. split; assumption.
Qed.
Lemma low_split : forall m A junk, rw_cells usegs m A [CB 42 junk] -> exists low, rw_cells usegs m A low /\ low_shape low.
Proof.
  intros m A junk H. pose proof (rw_cells_split_CB usegs m A [] 42 junk [] [8; 8; 8; 8; 8; 2]%nat H eq_refl) as H'.
  cbn [app mk_CB_cells] in H'. eexists. split; [exact H'|]. do 6 eexists. reflexivity.
Qed.
Lemma ofs_split : forall m A junk, rw_cells usegs m A [CB 30 junk] -> exists ofsc, rw_cells usegs m A ofsc /\ ofs_shape ofsc.
Proof.
  intros m A junk H. pose proof (rw_cells_split_CB usegs m A [] 30 junk [] [2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]%nat H eq_refl) as H'.
  cbn [app mk_CB_cells] in H'. eexists. split; [exact H'|]. do 15 eexists. reflexivity.
Qed.
Lemma low_shape_size : forall low, low_shape low -> Z.of_nat (cells_size low) = 42.
Proof. intros low (j0 & ja & jb & jc & jd & j2 & ->). reflexivity. Qed.
Lemma ofs_shape_size : forall ofsc, ofs_shape ofsc -> Z.of_nat (cells_size ofsc) = 30.
Proof. intros ofsc (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & o9 & o10 & o11 & o12 & o13 & o14 & o15 & ->). reflexivity. Qed.
Lemma cnt_zero_view : forall m A lens lofs,
  rw_cells usegs m A [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> u8arr usegs m A (u16s (av16 (itm_count_k lens lofs 0) 16)).
Proof.
  intros m A lens lofs H. rewrite itm_count_k_0 by lia. apply (u8arr_of_rw_cells usegs m A 32).
  apply (rw_cells_recast m A _ _ H); [cbn; split; [reflexivity| exact I]|].
  unfold av16. change (zseq 16) with [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]. cbn [map].
  rewrite !it_zero_count_spec. reflexivity.
Qed.
Lemma ITCM_isA : forall X low ofsc cnt wk tb m, itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> ITCM X low ofsc cnt wk tb m -> isA m (tx_L X) (tx_s X).
Proof.
  intros X low ofsc cnt wk tb m XO ST CM. apply (isA_munch (tx_m0 X) m _ _ (tx_W1 X)); [exact (ist_A _ _ _ ST)| exact (cm_mu _ _ _ _ _ _ _ CM)| exact (cm_wm _ _ _ _ _ _ _ CM)|].
  pose proof (xo_As X XO) as HA. unfold tx_W1. cbn [disjoint_from]. split; [lia| split; [lia| exact I]].
Qed.
Lemma itab_function : forall X (x5 x6 x7 x16 x17 x28 x29 x30 x31 : word),
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> mem_inv usegs (tx_m0 X) ->
  stk usegs (tx_m0 X) (tx_lo X) (bv_unsigned (tx_sp X)) ->
  0 <= tx_table X <= 1444 -> 0 <= tx_bits X <= 15 ->
  it_safe (tx_ty X) (tx_lens X) (tx_lofs X) (tx_codes X) (is_codes (tx_s X)) (tx_table X) (tx_bits X) (is_work (tx_s X)) = true ->
  ATY (tx_s X) -> (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  it_codes_ok (tx_ty X) (tx_codes X) ->
  evt usegs (itab_post X)
    (MS (mkR (tx_ra X) (tx_sp X) (tx_gp X) (tx_tp X) x5 x6 x7 (tx_s0 X) (tx_s1 X) (wz (ity_code (tx_ty X))) (wz (tx_lensA X)) (wz (tx_codes X))
             (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17 (tx_s2 X) (tx_s3 X) (tx_s4 X) (tx_s5 X)
             (tx_s6 X) (tx_s7 X) (tx_s8 X) (tx_s9 X) (tx_s10 X) (tx_s11 X) x28 x29 x30 x31)
        (tx_F X) (wz Z_INFLATE_TABLE) (tx_fc X) None (tx_m0 X) (seg_rom usegs)).
Proof.
  intros until x31; intros XO IST0 MI ST Rtab Rb SAFE ATY0 L15 HCX. pose proof XO as XO'.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  assert (LO0 : 0 <= tx_lo X) by exact (proj1 ST).
  pose proof (munch_refl (tx_W1 X) (tx_m0 X)) as MU. unfold tx_W1 in MU. pose proof (wmono_refl usegs (tx_m0 X)) as WM.
  pose proof IST0 as [GA GT Gl Gw Gc Gwin _ _]. unfold ilens, u16arr in Gl. unfold iwork, u16arr in Gw. unfold icodes in Gc.
  change (is_lens (tx_s X)) with (tx_lens X) in Gl.
  pose proof ARRS as (LL & LW & LT & _). pose proof ATY0 as (TYL & TYW & TYT). change (is_lens (tx_s X)) with (tx_lens X) in TYL.
  pose proof (av16_zlength (tx_lens X) 320 ltac:(unfold tx_lens; lia)) as L16l. pose proof (av16_zlength (is_work (tx_s X)) 288 ltac:(lia)) as L16w.
  pose proof (av32_zlength (is_codes (tx_s X)) 1444 ltac:(lia)) as L32.
  assert (RLA : 0 < tx_lensA X /\ tx_lensA X + 2 * tx_codes X < 2 ^ 62 /\ tx_lensA X mod 2 = 0) by (unfold tx_lensA; lia).
  set (m := tx_m0 X) in *.
  carve_frame 104%nat ST. rename FR into SAV.
  carve_frame 32%nat ST. rename FR into CNT.
  carve_frame 30%nat ST. destruct (ofs_split _ _ _ FR) as (ofsc & OFSC & OSH). clear FR. pose proof (ofs_shape_size ofsc OSH) as SZO.
  carve_frame 42%nat ST. destruct (low_split _ _ _ FR) as (low & LOW & LSH). clear FR. pose proof (low_shape_size low LSH) as SZ.
  unfold Z_INFLATE_TABLE. do 18 zs. pose proof (it_saved_bound X _ SAV) as BSP.
  apply (cnt_zero_view _ _ (tx_lens X) (tx_lofs X)) in CNT.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (CM : ITCM X low ofsc (itm_count_k (tx_lens X) (tx_lofs X) 0) (is_work (tx_s X)) (is_codes (tx_s X)) m1) by (split; assumption) end.
  zs. br_cases K.
  -
    assert (Ecnt : itm_count_k (tx_lens X) (tx_lofs X) 0 = itm_count (tx_lens X) (tx_lofs X) (tx_codes X)) by (rewrite itm_count_eq, K; reflexivity).
    eapply (itab_cntx X _ _ CNT XO' ltac:(intros i; apply itm_count_k_range) Rb);
      [ eapply itab_KR; eassumption| eapply itab_KN; eassumption| eapply ITCM_isA; eassumption].
  -
    ustep PC_IT_TRAP. zs. zs. zs. al2 (tx_lensA X). zs. rewrite (zb_lxor_ones (tx_lensA X)) by lia. zs. zs. rewrite zb_lxor_ones by lia. zs.
    first [rewrite zext32_x2 by lia | rewrite shl_32, mul32_shr31 by lia]. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (itab_count_loop (Z.to_nat (tx_codes X)) X low ofsc (itm_count_k (tx_lens X) (tx_lofs X) 0) (is_work (tx_s X)) (is_codes (tx_s X)) m1 0) as CL end.
    replace (2 * 0) with 0 in CL by lia. rewrite (Z.add_0_r (tx_lensA X)) in CL.
    eapply evt_cut; [eapply CL; [exact CM| reflexivity| exact SZ| exact SZO| exact XO'| exact TYL| exact L15| lia| lia| exact LW| exact LT]|]. clear CL.
    intros ms' (y5 & y6 & y7 & y8 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & CM').
    eapply (itab_cntx X _ m' (cm_cnt _ _ _ _ _ _ _ CM') XO' ltac:(intros i; apply itm_count_k_range) Rb);
      [ eapply itab_KR; try eassumption; symmetry; apply itm_count_eq| eapply itab_KN; try eassumption; symmetry; apply itm_count_eq| eapply ITCM_isA; eassumption].
Qed.
Theorem inflate_table_proof : inflate_table_stmt.
Proof.
  unfold inflate_table_stmt.
  intros L s ty dsel lens_ofs codes lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST MI STK Rlo HAS HWIN Rlofs Rcodes Rsum Rnext Rbits SAFE ATY0 L15 H286 -> -> -> -> -> ->.
  pose proof (ist_lay _ _ _ ST) as [BA _]. unfold blk_ok in BA. unfold Z_ITABLE_STACK in Rlo.
  apply (itab_function (mkITX L s ty dsel lens_ofs codes lo m sp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)); cbn [tx_lo tx_sp tx_L tx_s tx_m0 tx_table tx_bits tx_ty tx_lens tx_lofs tx_codes tx_dsel].
  - constructor; cbn [tx_lo tx_sp tx_L tx_s tx_lofs tx_codes]; [unfold Z_ITABLE_STACK; lia| lia| exact HWIN| lia| exact (ist_arrs _ _ _ ST)| exact (ist_lay _ _ _ ST)| lia].
  - exact ST.
  - exact MI.
  - exact STK.
  - exact Rnext.
  - exact Rbits.
  - exact SAFE.
  - exact ATY0.
  - exact L15.
  - exact H286.
Qed.
