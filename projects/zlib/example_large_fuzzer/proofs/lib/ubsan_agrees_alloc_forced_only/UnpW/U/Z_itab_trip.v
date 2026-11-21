From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit Z_itab_fill Z_itab_head Z_itab_next Z_itab_sub.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_itab_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].
Lemma it_huff_next_range : forall huff len, 0 <= huff < 65536 -> 1 <= len <= 15 -> 0 <= it_huff_next huff len < 65536.
Proof.
  intros huff len Hh Hl. unfold it_huff_next. rewrite it_incr_back_rec, shl32_pow2' by lia.
  pose proof (incr_rec_range huff 32 (2 ^ (len - 1)) ltac:(apply Z.pow_nonneg; lia)) as Hr.
  assert (2 ^ (len - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *.
  destruct (Z.eqb_spec (incr_rec huff 32 (2 ^ (len - 1))) 0); cbn [negb]; [lia|].
  pose proof (land_le_r huff (incr_rec huff 32 (2 ^ (len - 1)) - 1) ltac:(lia)). lia.
Qed.
Lemma fill_iter_ty : forall here hs next incr j tbl, 0 <= here < 2 ^ 32 -> ty32 tbl -> ty32 (fill_iter here hs next incr j tbl).
Proof.
  intros here hs next incr j. induction j as [|j IH]; intros tbl Hh Ht; cbn [fill_iter]; [exact Ht|].
  apply IH; [exact Hh| apply ty32_set; [exact Ht| exact Hh]].
Qed.
Lemma itab_incr0 : forall X root max cnt wk tb ms (len : Z) x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_INCR0 (mkLS x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31) cnt wk tb ms ->
  x26 = wz len -> itx_ok X -> 1 <= len <= 15 ->
  evt usegs (ITL X root max PC_IT_INCR (mkLS x1 x6 (wz (len - 1)) x9 x16 (wz (2 ^ (len - 1))) x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31) cnt wk tb) ms.
Proof.
  intros until x31; intros HL E26 XO Rlen.
  itl_open HL; subst x26; destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  unfold PC_IT_INCR0 at 1. zs. zs. ustep PC_IT_TRAP. zs. zs. rewrite sllw_1 by lia. apply evt_done. unfold PC_IT_INCR. itl_close.
Qed.
Definition TREGS (X : itx) (st : ItSt) (q : lscr) : Prop :=
  l6 q = wz (t_len st - t_drop st) /\ l7 q = wz (il_As (tx_L X) + 808 + 2 * t_sym st) /\ l9 q = wz (il_As (tx_L X) + 1384 + 4 * t_next st) /\
  l16 q = wz (lowx (t_low st)) /\ l21 q = wz (t_drop st) /\ l22 q = wz (t_sym st) /\ l25 q = wz (t_curr st) /\ l26 q = wz (t_len st) /\
  l29 q = wz (t_used st) /\ l30 q = wz (t_huff st).
Definition DREGS (X : itx) (st : ItSt) (q : lscr) : Prop :=
  l9 q = wz (il_As (tx_L X) + 1384 + 4 * t_next st) /\ l30 q = wz (t_huff st) /\ l6 q = wz ((t_len st - t_drop st) * 256) /\ l29 q = wz (t_used st).
Definition LINV (X : itx) (root : Z) (st : ItSt) : Prop :=
  (if t_drop st =? 0 then root else t_drop st) = root /\ 0 <= t_drop st <= 15 /\ (t_low st = 4294967295 \/ 0 <= t_low st < 65536) /\
  0 <= tx_table X <= t_next st /\
  ty16 (t_count st) /\ arr_len (t_count st) = 16 /\ ty32 (t_tbl st) /\ arr_len (t_tbl st) = 1444 /\ ty16 (t_work st) /\ arr_len (t_work st) = 288.
Definition trip_post (X : itx) (root max : Z) (r : ItStep) : machine_state -> Prop :=
  fun ms' => match r with
  | ItCont st' => exists q', ITL X root max PC_IT_TRIP q' (t_count st') (t_work st') (t_tbl st') ms' /\ TREGS X st' q' /\ LINV X root st'
  | ItBreak st' => exists q', ITL X root max PC_IT_DONE q' (t_count st') (t_work st') (t_tbl st') ms' /\ DREGS X st' q' /\ LINV X root st'
                   /\ 0 <= t_huff st' < 65536 /\ 0 <= t_len st' - t_drop st' <= 15 /\ 0 <= t_used st' < 65536 /\ 0 <= t_next st' < 1444
  | ItFail st' => exists q', ITL X root max PC_IT_EPI q' (t_count st') (t_work st') (t_tbl st') ms' /\ l16 q' = wz 1 /\ LINV X root st'
  end.
Lemma it_step_brk : forall x st s1, it_st1 x st = s1 -> it_brk x st = true -> it_step x st = ItBreak s1.
Proof. intros x st s1 E B. rewrite it_step_eq, B, E. reflexivity. Qed.
Lemma it_step_nosub : forall x st s1, it_st1 x st = s1 -> it_brk x st = false ->
  (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = false -> it_step x st = ItCont s1.
Proof. intros x st s1 E B C. rewrite it_step_eq, B, E. unfold it_sub. rewrite C. reflexivity. Qed.
Lemma it_step_sub : forall x st s1, it_st1 x st = s1 -> it_brk x st = false ->
  (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = true ->
  let drop := if t_drop s1 =? 0 then x_root x else t_drop s1 in
  let next := t_next s1 + t_min s1 in
  let curr := it_subtable_curr (t_count s1) (t_len s1) drop (x_max x) in
  let used := wrap32 (t_used s1 + Z.shiftl 1 curr) in
  it_step x st
  = if it_not_enough (x_ty x) used
    then ItFail (mkItSt (t_huff s1) (t_sym s1) (t_len s1) next curr drop (t_low s1) used (t_min s1) (t_count s1) (t_tbl s1) (t_work s1))
    else ItCont (mkItSt (t_huff s1) (t_sym s1) (t_len s1) next curr drop (Z.land (t_huff s1) (x_mask x)) used (t_min s1) (t_count s1)
                  (arr_set (t_tbl s1) (x_table x + Z.land (t_huff s1) (x_mask x)) (code_pack curr (x_root x) (next - x_table x))) (t_work s1)).
Proof. intros x st s1 E B C. rewrite it_step_eq, B, E. unfold it_sub. rewrite C. reflexivity. Qed.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- ty16 _ => fail | |- ty32 _ => fail end).
Lemma itab_trip : forall X root max st q ms,
  ITL X root max PC_IT_TRIP q (t_count st) (t_work st) (t_tbl st) ms -> TREGS X st q -> LINV X root st ->
  itx_ok X -> IST (tx_m0 X) (tx_L X) (tx_s X) -> 1 <= root <= 15 -> 1 <= max <= 15 ->
  it_trip_ok (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) 288 320 1444 st = true ->
  (forall st', it_step (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) st = ItCont st' ->
     it_trip_ok (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) 288 320 1444 st' = true) ->
  (tx_ty X = LENS -> arr_get (t_work st) (t_sym st) < 286) -> (tx_ty X = CODES -> arr_get (t_work st) (t_sym st) < 19) ->
  evt usegs (trip_post X root max (it_step (itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) st)) ms.
Proof.
  intros X root max st q ms HL HR HI XO IST0 Rroot Rmax TOK TOK2 LX0 LC0.
  set (x := itm_ctx _ _ _ _ _ _) in *.
  pose proof (trip_ok_basic x _ _ _ st TOK) as (Bsym & Blen & Bdrop & Bcurr & Bhuff & Bnext & Bused & Bmin).
  pose proof (trip_ok_work x _ _ _ st TOK) as Bw. cbv zeta in Bw. destruct Bw as [Bw Bw3].
  pose proof (trip_ok_fill x _ _ _ st TOK) as Bfill. rewrite !Z.shiftl_1_l in Bfill.
  pose proof (trip_ok_next x _ _ _ st TOK) as Bnx. cbv zeta in Bnx.
  pose proof (trip_ok_sub x _ _ _ st TOK) as Bsub.
  destruct HR as (E6 & E7 & E9 & E16 & E21 & E22 & E25 & E26 & E29 & E30).
  destruct HI as (Hdp & Rdrop & Rlow & Rtab & TYC & LC & TYT & LT & TYW & LW).
  destruct st as [huff sym len next curr drop low used min count tbl work].
  destruct q as [x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31].
  cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work l1 l6 l7 l9 l16 l18 l19 l20 l21 l22 l23 l25 l26 l27 l28 l29 l30 l31] in *.
  subst x. cbn [x_ty x_lens x_lens_ofs x_table x_root x_max x_mask itm_ctx] in *.
  pose proof (pow2_le15 (len - drop) ltac:(lia)) as Pld. pose proof (pow2_le15 curr ltac:(lia)) as Pcu.
  assert (Hhs : 0 <= huff ≫ drop <= huff) by (apply shiftr_le'; lia).
  assert (Hic0 : 2 ^ (len - drop) <= 2 ^ curr) by (apply Z.pow_le_mono_r; lia).
  eapply evt_cut.
  { eapply itab_head; [exact HL| exact E6| exact E7| exact E9| exact E30| exact E21| exact E25| exact XO| lia| lia| lia| lia| lia| lia| exact TYW| | exact LX0| exact LC0].
    cbv zeta. intros Hm. apply Bw3; [apply Z.ltb_ge; lia| apply Z.leb_le; lia]. }
  cbv beta. intros ms1 HL1. clear HL.
  set (incr := 2 ^ (len - drop)) in *.
  set (j := Z.to_nat (2 ^ (curr - (len - drop)))).
  assert (Hj : Z.of_nat j * incr = 2 ^ curr).
  { subst j incr. rewrite Z2Nat.id by (apply Z.pow_nonneg; lia). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hj1 : (1 <= j)%nat).
  { subst j. pose proof (Z.pow_le_mono_r 2 0 (curr - (len - drop)) ltac:(lia) ltac:(lia)) as P. change (2 ^ 0) with 1 in P. lia. }
  set (here := code_pack (it_here_op (tx_ty X) work (arr_get work sym)) (len - drop) (it_here_val (tx_ty X) work (arr_get work sym))).
  pose proof (it_here_op_range (tx_ty X) work (arr_get work sym)) as Rop.
  pose proof (it_here_val_range (tx_ty X) work (arr_get work sym) TYW Bw ltac:(intros Hm; apply Bw3; [apply Z.ltb_ge; lia| apply Z.leb_le; lia])) as Rval.
  eapply evt_cut.
  { eapply (itab_fill j X root max _ _ _ _ _ (len - drop) _ (huff ≫ drop) next incr); [exact HL1| reflexivity| reflexivity| reflexivity| f_equal; lia| rewrite <- Hj; reflexivity| reflexivity| exact E9
     | exact XO| exact Hj1| subst incr; reflexivity| lia| lia| lia| lia| lia| exact LT| exact TYT| exact Rop| exact Rval| lia|].
    rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
  cbv beta. intros ms2 (x1' & x27' & x31' & HL2). clear HL1. fold here in HL2.
  eapply evt_cut. { eapply itab_incr0; [exact HL2| exact E26| exact XO| lia]. }
  cbv beta. intros ms3 HL3. clear HL2.
  pose proof (pow2_le15 (len - 1) ltac:(lia)) as Pl1.
  eapply evt_cut.
  { eapply (itab_incr_loop 32); [exact HL3| exact E30| reflexivity| exact XO| lia| lia|].
    apply (Z.le_lt_trans _ (2 ^ 15)); [lia|]. apply Z.pow_lt_mono_r; cbn; lia. }
  cbv beta. intros ms4 HL4. clear HL3.
  rewrite <- (shl32_pow2' (len - 1)), <- it_incr_back_rec in HL4 by lia.
  pose proof (it_huff_next_range huff len Bhuff Blen) as Rh'.
  eapply evt_cut.
  { eapply itab_nextsym; [exact HL4| exact E26| exact E30| reflexivity| exact E22| reflexivity| exact XO| exact IST0| reflexivity| lia| lia| lia| lia| exact TYW| exact TYC| exact LC|].
    cbv zeta. intros Hc Hm. exact (Bnx Hc Hm). }
  cbv beta. intros ms5 (x6' & x7' & x18' & x19' & x28' & HL5). clear HL4. cbv zeta in HL5.
  set (c := wrap16 (arr_get count len - 1)) in *.
  set (huff' := it_huff_next huff len) in *.
  set (tbl' := fill_iter here (huff ≫ drop) next incr j tbl) in *.
  set (len' := if (c =? 0) && negb (len =? max) then arr_get (tx_lens X) (tx_lofs X + arr_get work (sym + 1)) else len) in *.
  set (x := itm_ctx (tx_ty X) (tx_lens X) (tx_lofs X) (tx_table X) root max) in *.
  set (st0 := {| t_huff := huff; t_sym := sym; t_len := len; t_next := next; t_curr := curr; t_drop := drop; t_low := low; t_used := used;
                 t_min := min; t_count := count; t_tbl := tbl; t_work := work |}) in *.
  set (s1 := {| t_huff := huff'; t_sym := sym + 1; t_len := len'; t_next := next; t_curr := curr; t_drop := drop; t_low := low; t_used := used;
                t_min := 2 ^ curr; t_count := arr_set count len c; t_tbl := tbl'; t_work := work |}).
  assert (Ebrk : it_brk x st0 = (c =? 0) && (len =? max)) by reflexivity.
  assert (Est1 : it_st1 x st0 = s1).
  { subst s1 st0 x. unfold it_st1. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work x_ty x_lens x_lens_ofs x_table x_root x_max x_mask itm_ctx].
    rewrite !shl32_pow2' by lia. fold incr. rewrite <- Hj. rewrite (it_fill_spec _ incr huff drop next j tbl Hj1 ltac:(lia) ltac:(lia)).
    rewrite Hj. rewrite code_pack_wrap8_bits. rewrite (wrap32_id (sym + 1)) by lia. reflexivity. }
  assert (Hlen' : 1 <= len' <= 15).
  { subst len'. destruct (Z.eqb_spec c 0) as [Ec|Ec]; cbn [andb]; [|lia]. destruct (Z.eqb_spec len max) as [Em|Em]; cbn [negb]; [lia|].
    destruct (Bnx Ec Em) as (_ & _ & _ & W4). exact W4. }
  assert (TYC' : ty16 (arr_set count len c)) by (apply ty16_set; [exact TYC| apply wrap16_ty]).
  assert (TYT' : ty32 tbl') by (apply fill_iter_ty; [apply code_pack_ty| exact TYT]).
  assert (LT' : arr_len tbl' = 1444) by (subst tbl'; rewrite fill_iter_len; exact LT).
  assert (Hic : incr <= 2 ^ curr) by (subst incr; apply Z.pow_le_mono_r; lia).
  pose proof (pow2_root_bounds root Rroot) as Pr.
  assert (Emask : x_mask x = 2 ^ root - 1) by (subst x; cbn [x_mask itm_ctx]; rewrite itm_used_pow2 by lia; reflexivity).
  destruct (Sumbool.sumbool_of_bool ((c =? 0) && (len =? max))) as [EB|EB]; rewrite EB in Ebrk.
  -
    rewrite (it_step_brk x st0 s1 Est1 Ebrk).
    apply andb_prop in EB as [E1 E2]. rewrite E1, E2 in HL5. cbn [andb negb] in HL5.
    assert (El : len' = len) by (subst len'; rewrite E1, E2; reflexivity).
    apply evt_done. subst s1. cbn [trip_post t_count t_work t_tbl t_huff t_len t_drop t_used t_next]. eexists. split; [exact HL5|]. split; [|split].
    + unfold DREGS. cbn [t_next t_huff t_len t_drop t_used l9 l30 l6 l29]. rewrite <- El in *. splits; first [assumption | reflexivity | exact E6].
    + unfold LINV. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite arr_len_set. splits; try assumption; lia.
    + rewrite El. splits; lia.
  - rewrite EB in HL5.
    eapply evt_mono.
    { eapply itab_sub; [exact HL5| reflexivity| reflexivity| exact E9| reflexivity| exact E21| exact E16| exact E29| reflexivity| reflexivity| exact E25| exact XO| exact IST0
        | lia| lia| exact Hlen'| lia| exact Rh'| lia| lia| exact Hdp| lia| exact Rlow| lia| lia| exact TYC'| rewrite arr_len_set; exact LC| exact LT'| exact TYT'|].
      intros Hrl NEL ENT.
      assert (COND : (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = true).
      { rewrite Emask. subst x s1. cbn [x_root itm_ctx t_len t_huff t_low]. apply andb_true_intro. split; [apply Z.ltb_lt; exact Hrl| apply Bool.negb_true_iff, Z.eqb_neq; exact NEL]. }
      pose proof (it_step_sub x st0 s1 Est1 Ebrk COND) as ES. cbv zeta in ES. rewrite Emask in ES.
      subst s1. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work] in ES. rewrite Hdp in ES.
      replace (x_max x) with max in ES by (subst x; reflexivity). replace (x_ty x) with (tx_ty X) in ES by (subst x; reflexivity).
      rewrite Z.shiftl_1_l, wrap32_id, ENT in ES.
      2:{ pose proof (curr_rec_bound (arr_set count len c) root max 16 (len' - root) (2 ^ (len' - root)) ltac:(lia) ltac:(lia) ltac:(lia)) as CB.
          rewrite <- it_subtable_curr_eq in CB by lia. pose proof (pow2_le15 (it_subtable_curr (arr_set count len c) len' root max) ltac:(lia)). lia. }
      destruct (Bsub _ ES ltac:(cbn [t_low]; left; exact NEL)) as (B1 & _ & _). cbn [t_low] in B1. replace (x_table x) with (tx_table X) in B1 by (subst x; reflexivity). exact B1. }
    cbv beta. intros ms6 P6. fold tbl' in P6. unfold sub_post in P6. cbv zeta in P6.
    destruct (Sumbool.sumbool_of_bool ((root <? len') && negb (Z.land huff' (2 ^ root - 1) =? low))) as [ES|ES]; rewrite ES in P6.
    +
      assert (COND : (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = true) by (rewrite Emask; subst x s1; exact ES).
      pose proof (it_step_sub x st0 s1 Est1 Ebrk COND) as EST. cbv zeta in EST. rewrite Emask in EST.
      subst s1. cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work] in EST. rewrite Hdp in EST.
      replace (x_max x) with max in EST by (subst x; reflexivity). replace (x_ty x) with (tx_ty X) in EST by (subst x; reflexivity).
      replace (x_table x) with (tx_table X) in EST by (subst x; reflexivity).
      set (curr' := it_subtable_curr (arr_set count len c) len' root max) in *.
      assert (Rc' : 1 <= curr' <= 15).
      { pose proof (curr_rec_bound (arr_set count len c) root max 16 (len' - root) (2 ^ (len' - root)) ltac:(lia) ltac:(lia) ltac:(lia)) as CB.
        rewrite <- it_subtable_curr_eq in CB by lia. apply andb_prop in ES as [ES1 _]. apply Z.ltb_lt in ES1. lia. }
      pose proof (pow2_le15 curr' ltac:(lia)) as Pc'.
      rewrite Z.shiftl_1_l, wrap32_id in EST by lia. rewrite EST. unfold used_post in P6. cbv zeta in P6.
      destruct (it_not_enough (tx_ty X) (used + 2 ^ curr')).
      *
        destruct P6 as (q' & HL6 & E16'). cbn [trip_post t_count t_work t_tbl]. exists q'. split; [exact HL6|]. split; [exact E16'|].
        unfold LINV. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite arr_len_set.
        splits; try assumption; try lia. destruct (root =? 0); reflexivity.
      * destruct P6 as (y1 & y18 & y19 & y20 & y23 & y27 & y28 & y31 & HL6). cbn [trip_post t_count t_work t_tbl]. eexists. split; [exact HL6|]. split.
        -- unfold TREGS. cbn [t_len t_curr t_next t_huff t_drop t_low t_used t_sym l6 l7 l9 l16 l21 l22 l25 l26 l29 l30]. splits; try reflexivity.
           unfold lowx. pose proof (land_le_r huff' (2 ^ root - 1) ltac:(lia)). replace (Z.land huff' (2 ^ root - 1) =? 4294967295) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
        -- unfold LINV. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite !arr_len_set.
           pose proof (land_le_r huff' (2 ^ root - 1) ltac:(lia)).
           splits; try assumption; try lia. { destruct (root =? 0); reflexivity. } apply ty32_set; [exact TYT'| apply code_pack_ty].
    +
      assert (COND : (x_root x <? t_len s1) && negb (Z.land (t_huff s1) (x_mask x) =? t_low s1) = false) by (rewrite Emask; subst x s1; exact ES).
      rewrite (it_step_nosub x st0 s1 Est1 Ebrk COND). subst s1.
      destruct P6 as (y1 & y18 & y19 & y20 & y23 & y27 & y28 & y31 & HL6). cbn [trip_post t_count t_work t_tbl]. eexists. split; [exact HL6|]. split.
      * unfold TREGS. cbn [t_len t_curr t_next t_huff t_drop t_low t_used t_sym l6 l7 l9 l16 l21 l22 l25 l26 l29 l30]. splits; reflexivity.
      * unfold LINV. cbn [t_drop t_low t_next t_count t_tbl t_work]. rewrite !arr_len_set. splits; try assumption; lia.
Qed.
