(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateParams DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel RefDeflateRel RefDeflSafeL1 RefDeflSafeG RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeFB RefDeflSafeL0 RefDeflSafeL2 RefDeflSafeL3 RefDeflSafeL4 RefDeflSafeL5 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRel DeflateTaintRelG DeflateTaintLzG DeflateTaintBlkG DeflateTaintCallG DeflateTaintStored DeflateTaintCoreG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateParamsDD DeflateParamsZ1 DeflateParamsZ4 DeflateParamsDD1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma rel_reC W C C' B bnd bnd' ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> (forall p, C' p -> C p) -> chain C' bnd' s1 -> REL W C' B bnd' ms pm s1 s2.
Proof.
  intros R HC CH. destruct R; constructor; try assumption.
  eapply aeq_mono; [eassumption | exact HC].
Qed.

Lemma chain_CHAIN C bnd s BH BP WS :
  chain C bnd s -> CHAINW s BH BP WS -> ds_hash_size s = 32768 -> ds_w_mask s = 32767 ->
  chain (fun p => C p /\ WS p) (Z.max BH BP) s.
Proof.
  intros [H1 H2] [K1 K2] Hs Hm. rewrite Hs, Hm in *. split.
  - intros h Hh. destruct (H1 h Hh) as [Rg Alt]. split; [exact Rg|].
    destruct (K1 h Hh) as [E0 | [Bd Ws]]; [left; exact E0 | right].
    destruct Alt as [E0 | [_ Cc]]; [exfalso; clear - E0 Bd; lia|].
    split; [clear - Bd; lia | exact (conj Cc Ws)].
  - intros p [Cp Wp]. destruct (H2 p Cp) as [Rp [Rg Alt]]. split; [exact Rp|]. split; [exact Rg|].
    destruct (K2 p Wp) as [_ [E0 | [Bd Ws]]]; [left; exact E0 | right].
    destruct Alt as [E0 | [_ Cc]]; [exfalso; clear - E0 Bd; lia|].
    split; [clear - Bd; lia | exact (conj Cc Ws)].
Qed.

Lemma clear_hash_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 -> REL W C B bnd ms pm (clear_hash s1) (clear_hash s2).
Proof.
  intros R I1 I2. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC.
  pose proof (ig_hl s1 I1) as L1. pose proof (ig_hl s2 I2) as L2. pose proof (ig_hsize s1 I1) as Hs1.
  assert (Hs2 : ds_hash_size s2 = 32768) by (rewrite <- (clean_eq_fieldT ds_hash_size _ _ EC ltac:(reflexivity)); exact Hs1).
  pose proof (r_head _ _ _ _ _ _ _ _ R) as AH. pose proof (r_chain _ _ _ _ _ _ _ _ R) as [CH1 CH2].
  rewrite !RefDeflSafeI3.clear_hash_eq, Hs1, Hs2.
  set (a1 := arr_fill (arr_set (ds_head s1) (32768 - 1) NIL) 0 (32768 - 1) 0).
  set (a2 := arr_fill (arr_set (ds_head s2) (32768 - 1) NIL) 0 (32768 - 1) 0).
  assert (A12 : aeq (fun _ => True) a1 a2).
  { subst a1 a2. eapply aeq_mono; [apply aeq_fill; apply aeq_set_keep; exact AH | intros i _; left; exact I]. }
  assert (Z1 : forall h, 0 <= h < 32768 -> arr_get a1 h = 0).
  { intros h Hh. subst a1. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, L1.
    destruct (Z.eq_dec h (32768 - 1)) as [->|Hne].
    - replace ((0 <=? 32768 - 1) && (32768 - 1 <? 0 + Z.max 0 (32768 - 1)) && ((0 <=? 32768 - 1) && (32768 - 1 <? 32768))) with false by reflexivity.
      rewrite arr_get_set. unfold arr_inb. rewrite L1. reflexivity.
    - replace ((0 <=? h) && (h <? 0 + Z.max 0 (32768 - 1)) && ((0 <=? h) && (h <? 32768))) with true
        by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity. }
  clearbody a1 a2.
  apply (rel_set_head W C C B bnd bnd ms pm s1 s2 a1 a2 R A12 (r_prev _ _ _ _ _ _ _ _ R)).
  dsr. split; [| exact CH2]. intros h Hh. rewrite (Z1 h Hh). unfold cv. split; [lia | left; reflexivity].
Qed.

Lemma INVG_clear_hash s : INVG s -> INVG (clear_hash s).
Proof.
  intros I. pose proof (ig_hl s I) as L. rewrite RefDeflSafeI3.clear_hash_eq.
  destruct I; constructor; dsr; try assumption. rewrite arr_len_fill, arr_len_set. exact L.
Qed.

Definition tq (s : deflate_state) :=
  (ds_high_water s, ds_strstart s, ds_lookahead s, ds_pending_out s, ds_pending s, ds_lit_bufsize s, ds_sym_next s, ds_strm s).
Lemma tq_slide_hash s : tq (slide_hash s) = tq s. Proof. reflexivity. Qed.
Lemma tq_clear_hash s : tq (clear_hash s) = tq s. Proof. reflexivity. Qed.
Lemma tq_set_matches s v : tq (set_matches s v) = tq s. Proof. reflexivity. Qed.
Lemma tq_set_level s v : tq (set_level s v) = tq s. Proof. reflexivity. Qed.

Lemma tq_fields a b : tq b = tq a ->
  ds_high_water b = ds_high_water a /\ ds_strstart b = ds_strstart a /\ ds_lookahead b = ds_lookahead a
  /\ ds_pending_out b = ds_pending_out a /\ ds_pending b = ds_pending a /\ ds_lit_bufsize b = ds_lit_bufsize a
  /\ ds_sym_next b = ds_sym_next a /\ ds_strm b = ds_strm a.
Proof.
  intros E. unfold tq in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat split; assumption.
Qed.

Lemma DQ_of_tq W C B bnd ms pm a1 b1 b2 :
  tq b1 = tq a1 ->
  (forall i, i < WHI a1 -> W i) ->
  (forall i, ds_pending_out a1 <= i < ds_pending_out a1 + ds_pending a1 -> B i) ->
  SYMB B a1 ->
  REL W C B bnd ms pm b1 b2 -> (ds_level b1 <> 0 -> bnd <= ds_strstart b1) -> HWI b1 ->
  DQ b1 b2.
Proof.
  intros E HW HP HS R Hb HH. pose proof (tq_fields _ _ E) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  exists W, C, B, bnd, ms, pm. split; [exact R|]. split; [unfold WHI; rewrite E1, E2, E3; exact HW|].
  split; [exact Hb|]. split; [rewrite E4, E5; exact HP|]. split; [unfold SYMB; rewrite E6, E7; exact HS | exact HH].
Qed.


Lemma relevel_rel : forall u1 u2 level,
  DQ u1 u2 -> INVG u1 -> INVG u2 -> dwf u1 -> ZLS u1 ->
  (ds_level u1 = 0 -> level <> 0 -> ds_lookahead u1 = 0) ->
  let p1 := set_level (pre_st u1) level in let p2 := set_level (pre_st u2) level in
  DQ p1 p2 /\ INVG p1 /\ INVG p2 /\ tq p1 = tq u1 /\ tq p2 = tq u2.
Proof.
  intros u1 u2 level (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH) I1 I2 D1 Z1 Hlk p1 p2.
  pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC.
  assert (El : ds_level u2 = ds_level u1) by (symmetry; exact (clean_eq_fieldT ds_level _ _ EC ltac:(reflexivity))).
  assert (Em : ds_matches u2 = ds_matches u1) by (symmetry; exact (clean_eq_fieldT ds_matches _ _ EC ltac:(reflexivity))).
  assert (PRE : exists bndp, REL W C B bndp ms pm (pre_st u1) (pre_st u2) /\ INVG (pre_st u1) /\ INVG (pre_st u2)
                 /\ tq (pre_st u1) = tq u1 /\ tq (pre_st u2) = tq u2 /\ (ds_level u1 <> 0 -> pre_st u1 = u1 /\ bndp = bnd)).
  { unfold pre_st. rewrite El, Em.
    destruct (Z.eqb_spec (ds_level u1) 0) as [O0 | O0]; cbn [andb].
    - destruct (negb (ds_matches u1 =? 0)).
      + destruct (ds_matches u1 =? 1).
        * exists (bnd - 32768). split; [apply rel_set_matches; apply slide_hash_rel; assumption|].
          split; [apply INVG_set_matches, INVG_slide_hash; exact I1|]. split; [apply INVG_set_matches, INVG_slide_hash; exact I2|].
          rewrite !tq_set_matches, !tq_slide_hash. split; [reflexivity|]. split; [reflexivity|]. intros X; exfalso; exact (X O0).
        * exists bnd. split; [apply rel_set_matches; apply clear_hash_rel; assumption|].
          split; [apply INVG_set_matches, INVG_clear_hash; exact I1|]. split; [apply INVG_set_matches, INVG_clear_hash; exact I2|].
          rewrite !tq_set_matches, !tq_clear_hash. split; [reflexivity|]. split; [reflexivity|]. intros X; exfalso; exact (X O0).
      + exists bnd. split; [exact R|]. split; [exact I1|]. split; [exact I2|]. split; [reflexivity|]. split; [reflexivity|]. intros _; split; reflexivity.
    - exists bnd. split; [exact R|]. split; [exact I1|]. split; [exact I2|]. split; [reflexivity|]. split; [reflexivity|]. intros _; split; reflexivity. }
  destruct PRE as (bndp & Rp & Ip1 & Ip2 & Tp1 & Tp2 & Keep).
  pose proof (tq_fields _ _ Tp1) as (F1 & F2 & F3 & _).
  assert (Tq1 : tq p1 = tq u1) by (subst p1; rewrite tq_set_level; exact Tp1).
  assert (Tq2 : tq p2 = tq u2) by (subst p2; rewrite tq_set_level; exact Tp2).
  split; [| split; [subst p1; apply INVG_set_level; exact Ip1 | split; [subst p2; apply INVG_set_level; exact Ip2 | exact (conj Tq1 Tq2)]]].
  destruct (Z.eq_dec level 0) as [L0 | L0].
  {
    apply (DQ_of_tq W C B bndp ms pm u1); [exact Tq1 | exact HW | exact HP | exact HS | subst p1 p2; apply rel_set_level; exact Rp | |].
    - subst p1. dsr. intros X. exfalso. exact (X L0).
    - subst p1. unfold HWI. dsr. rewrite L0. apply HWI4_lvl0. }
  destruct (Z.eq_dec (ds_level u1) 0) as [O0 | O0].
  -
    pose proof (pre_st_chain u1 D1 Z1 O0) as [[WS CW] _].
    pose proof (chain_CHAIN C bndp (pre_st u1) _ _ WS (r_chain _ _ _ _ _ _ _ _ Rp) CW (ig_hsize _ Ip1) (ig_wmask _ Ip1)) as CH'.
    pose proof (rel_reC W C (fun p => C p /\ WS p) B bndp _ ms pm _ _ Rp ltac:(intros p [Cp _]; exact Cp) CH') as R'.
    apply (DQ_of_tq W (fun p => C p /\ WS p) B (Z.max (ds_strstart u1 - 1) (ds_strstart u1 - 1)) ms pm u1);
      [exact Tq1 | exact HW | exact HP | exact HS | subst p1 p2; apply rel_set_level; exact R' | |].
    + subst p1. dsr. rewrite F2. intros _. clear - F2. lia.
    + subst p1. unfold HWI. dsr. rewrite F3, F2, F1, (Hlk O0 L0). apply HWI4_look0.
  -
    destruct (Keep O0) as [Ep1 Eb]. subst bndp.
    apply (DQ_of_tq W C B bnd ms pm u1); [exact Tq1 | exact HW | exact HP | exact HS | subst p1 p2; apply rel_set_level; exact Rp | |].
    + subst p1. dsr. rewrite F2. intros _. exact (Hb O0).
    + subst p1. unfold HWI in *. dsr. rewrite F3, F2, F1. unfold HWI4 in *. clear - HH O0 L0. lia.
Qed.


Lemma DQ_set_max_lazy_match a b v : DQ a b -> DQ (set_max_lazy_match a v) (set_max_lazy_match b v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_max_lazy_match; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DQ_set_good_match a b v : DQ a b -> DQ (set_good_match a v) (set_good_match b v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_good_match; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DQ_set_nice_match a b v : DQ a b -> DQ (set_nice_match a v) (set_nice_match b v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_nice_match; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DQ_set_max_chain_length a b v : DQ a b -> DQ (set_max_chain_length a v) (set_max_chain_length b v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_max_chain_length; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DQ_set_strategy a b v : DQ a b -> DQ (set_strategy a v) (set_strategy b v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_strategy; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.

Definition dparams_switch (u : deflate_state) (level strategy : Z) : deflate_state :=
  set_strategy (if negb (Z.eqb (ds_level u) level) then dparams_set_level u level else u) strategy.

Lemma switch_rel : forall u1 u2 level strategy,
  DQ u1 u2 -> INVG u1 -> INVG u2 -> dwf u1 -> ZLS u1 ->
  (ds_level u1 = 0 -> level <> 0 -> ds_lookahead u1 = 0) -> (strategy <> 2 /\ strategy <> 3) ->
  let t1 := dparams_switch u1 level strategy in let t2 := dparams_switch u2 level strategy in
  DQ t1 t2 /\ INVG t1 /\ INVG t2 /\ ds_strm t1 = ds_strm u1 /\ ds_strm t2 = ds_strm u2.
Proof.
  intros u1 u2 level strategy HQ I1 I2 D1 Z1 Hlk Hst t1 t2. subst t1 t2. unfold dparams_switch.
  pose proof (DQ_clean _ _ HQ) as EC.
  assert (El : ds_level u2 = ds_level u1) by (symmetry; exact (clean_eq_fieldT ds_level _ _ EC ltac:(reflexivity))).
  rewrite El. destruct (negb (ds_level u1 =? level)).
  - rewrite !dparams_set_level_eq. destruct (configuration_table level) as [[[good lazy] nice] chain].
    pose proof (relevel_rel u1 u2 level HQ I1 I2 D1 Z1 Hlk) as (HQp & Ip1 & Ip2 & Tp1 & Tp2). cbv zeta in HQp, Ip1, Ip2, Tp1, Tp2.
    pose proof (tq_fields _ _ Tp1) as (_ & _ & _ & _ & _ & _ & _ & Es1). pose proof (tq_fields _ _ Tp2) as (_ & _ & _ & _ & _ & _ & _ & Es2).
    set (p1 := set_level (pre_st u1) level) in *. set (p2 := set_level (pre_st u2) level) in *. clearbody p1 p2.
    split; [apply DQ_set_strategy, DQ_set_max_chain_length, DQ_set_nice_match, DQ_set_good_match, DQ_set_max_lazy_match; exact HQp|].
    split; [apply INVG_set_strategy; [exact Hst|]; apply INVG_set_max_chain_length, INVG_set_nice_match, INVG_set_good_match, INVG_set_max_lazy_match; exact Ip1|].
    split; [apply INVG_set_strategy; [exact Hst|]; apply INVG_set_max_chain_length, INVG_set_nice_match, INVG_set_good_match, INVG_set_max_lazy_match; exact Ip2|].
    dsr. exact (conj Es1 Es2).
  - split; [apply DQ_set_strategy; exact HQ|]. split; [apply INVG_set_strategy; [exact Hst | exact I1]|].
    split; [apply INVG_set_strategy; [exact Hst | exact I2]|]. dsr. split; reflexivity.
Qed.


Lemma zl_modes_clean a b : clean a = clean b -> zl_modes a -> zl_modes b.
Proof.
  intros EC [Hm Hs]. unfold zl_modes. rewrite (dmode_clean _ _ EC).
  rewrite <- (clean_eq_fieldT ds_strategy _ _ EC ltac:(reflexivity)). exact (conj Hm Hs).
Qed.

Lemma SWF_clean a b level : clean a = clean b -> SWF a level -> SWF b level.
Proof.
  intros EC H. unfold SWF in *.
  rewrite <- (clean_eq_fieldT ds_level _ _ EC ltac:(reflexivity)), <- (clean_eq_fieldT ds_strm _ _ EC ltac:(reflexivity)),
    <- (clean_eq_fieldT ds_strstart _ _ EC ltac:(reflexivity)), <- (clean_eq_fieldT ds_block_start _ _ EC ltac:(reflexivity)),
    <- (clean_eq_fieldT ds_lookahead _ _ EC ltac:(reflexivity)), <- (clean_eq_fieldT ds_last_flush _ _ EC ltac:(reflexivity)).
  exact H.
Qed.

Lemma look0_of_SWF u level : DD u -> ZLS u -> zl_modes u -> SWF u level -> 0 <= level <= 9 ->
  ds_level u = 0 -> level <> 0 -> ds_lookahead u = 0.
Proof.
  intros HDD HZ Hm HSW Hl O0 L0.
  assert (NE : cfunc_id (ds_level u) <> cfunc_id level).
  { rewrite O0, cfunc_id_0. pose proof (cfunc_id_cases level Hl) as ([A1 A2] & _ & _). intros E. symmetry in E. exact (L0 (A1 E)). }
  exact (proj1 (SWP_of u level HDD HZ Hm HSW NE)).
Qed.

Definition DCALLZ (s1 s2 : deflate_state) : Prop := DCALL s1 s2 /\ ZLS s1 /\ ZLS s2 /\ zl_modes s1.

Local Notation Hst := stored_bf_spec.
Local Notation Hhf := (huff_bf_spec FB_CALL_ok).
Local Notation Hrl := (rle_bf_spec FB_CALL_ok).
Local Notation Hfa := (fast_bf_spec FB_CALL_ok).
Local Notation Hsl := (slow_bf_spec FB_CALL_ok).

Theorem dparams_rel : forall s1 s2 zc level strategy,
  DCALLZ s1 s2 -> dcall_wf zc -> params_legal level strategy -> (strategy = 0 \/ strategy = 1) ->
  (cfunc_id level = 0 \/ cfunc_id level = 2) ->
  snd (deflateParams_m s1 zc level strategy) = snd (deflateParams_m s2 zc level strategy)
  /\ DCALLZ (fst (deflateParams_m s1 zc level strategy)) (fst (deflateParams_m s2 zc level strategy)).
Proof.
  intros s1 s2 zc level strategy ((HQ & I1 & I2 & DD1 & DD2) & HZ1 & HZ2 & Hm1) Hzc Hleg Hst01 Hcl.
  pose proof Hleg as [Hl Hs9].
  assert (HstG : strategy <> 2 /\ strategy <> 3) by (clear - Hst01; lia).
  pose proof (DQ_clean _ _ HQ) as EC. pose proof (zl_modes_clean _ _ EC Hm1) as Hm2.
  unfold deflateParams_m.
  set (c0 := cstrm_of_call zc).
  pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
  assert (Ain : 0 <= cs_avail_in c0) by (subst c0; rewrite cstrm_of_call_avail_in; unfold zlength; clear; lia).
  assert (Aout : 0 <= cs_avail_out c0) by (subst c0; rewrite cstrm_of_call_avail_out; destruct Hzc as (_ & Hao & _); clear - Hao; lia).
  pose proof (DQ_set_strm s1 s2 c0 HQ) as HQ0.
  pose proof (INVG_set_strm s1 c0 Ain Aout I1) as I10. pose proof (INVG_set_strm s2 c0 Ain Aout I2) as I20.
  pose proof (DD_set_strm s1 c0 DD1) as DD10. pose proof (DD_set_strm s2 c0 DD2) as DD20.
  assert (HZ10 : ZLS (set_strm s1 c0)) by (apply ZLS_load; exact HZ1). assert (HZ20 : ZLS (set_strm s2 c0)) by (apply ZLS_load; exact HZ2).
  assert (Hm10 : zl_modes (set_strm s1 c0)) by exact Hm1. assert (Hm20 : zl_modes (set_strm s2 c0)) by exact Hm2.
  pose proof (deflate_core_QQ s1 zc Z_BLOCK DD1 Hzc ltac:(right; right; reflexivity) HZ1 Hm1) as U1. cbv zeta in U1. fold c0 in U1.
  pose proof (deflate_core_QQ s2 zc Z_BLOCK DD2 Hzc ltac:(right; right; reflexivity) HZ2 Hm2) as U2. cbv zeta in U2. fold c0 in U2.
  assert (G1 : DC c0 (set_strm s1 c0)) by (split; [exact DD10 | subst c0; apply SV_entry; exact Hzc]).
  assert (G2 : DC c0 (set_strm s2 c0)) by (split; [exact DD20 | subst c0; apply SV_entry; exact Hzc]).
  pose proof (core_rel c0 (set_strm s1 c0) (set_strm s2 c0) HC0 eq_refl eq_refl (proj1 (proj1 G1)) (proj1 (proj1 G2)) Z_BLOCK
                (conj G1 eq_refl) (conj G2 eq_refl) HQ0 I10 I20 ltac:(right; right; reflexivity)) as (Ee & HQc & Ic1 & Ic2).
  set (u1 := set_strm s1 c0) in *. set (u2 := set_strm s2 c0) in *. clearbody u1 u2.
  pose proof (DQ_clean _ _ HQ0) as EC0.
  rewrite (deflateParams_core_eq u1 level strategy (df_status _ (proj1 DD10)) Hl Hs9).
  rewrite (deflateParams_core_eq u2 level strategy (df_status _ (proj1 DD20)) Hl Hs9). cbv zeta.
  assert (Efl : dparams_flushes u2 level strategy = dparams_flushes u1 level strategy).
  { unfold dparams_flushes. rewrite <- (clean_eq_fieldT ds_strategy _ _ EC0 ltac:(reflexivity)), <- (clean_eq_fieldT ds_level _ _ EC0 ltac:(reflexivity)),
      <- (clean_eq_fieldT ds_last_flush _ _ EC0 ltac:(reflexivity)). reflexivity. }
  rewrite Efl.
  assert (TAIL : forall v1 v2, DQ v1 v2 -> INVG v1 -> INVG v2 -> DD v1 -> DD v2 -> ZLS v1 -> ZLS v2 -> zl_modes v1 -> SWF v1 level ->
            snd (dparams_switch v1 level strategy, zret_of_cs (ds_strm (dparams_switch v1 level strategy)) Z_OK)
              = snd (dparams_switch v2 level strategy, zret_of_cs (ds_strm (dparams_switch v2 level strategy)) Z_OK)
            /\ DCALLZ (fst (dparams_switch v1 level strategy, zret_of_cs (ds_strm (dparams_switch v1 level strategy)) Z_OK))
                      (fst (dparams_switch v2 level strategy, zret_of_cs (ds_strm (dparams_switch v2 level strategy)) Z_OK))).
  { intros v1 v2 Q J1 J2 E1 E2 Y1 Y2 M1 SW1. cbn [fst snd].
    pose proof (DQ_clean _ _ Q) as ECv. pose proof (zl_modes_clean _ _ ECv M1) as M2. pose proof (SWF_clean _ _ level ECv SW1) as SW2.
    pose proof (switch_rel v1 v2 level strategy Q J1 J2 (proj1 E1) Y1 (look0_of_SWF v1 level E1 Y1 M1 SW1 Hl) HstG) as (Qt & Jt1 & Jt2 & St1 & St2).
    cbv zeta in Qt, Jt1, Jt2, St1, St2.
    pose proof (set_level_DD v1 level strategy E1 Y1 Hl Hst01 (conj M1 Hcl) SW1) as (Et1 & Yt1 & Mt1). cbv zeta in Et1, Yt1, Mt1.
    pose proof (set_level_DD v2 level strategy E2 Y2 Hl Hst01 (conj M2 Hcl) SW2) as (Et2 & Yt2 & _). cbv zeta in Et2, Yt2.
    fold (dparams_switch v1 level strategy) in Et1, Yt1, Mt1. fold (dparams_switch v2 level strategy) in Et2, Yt2.
    split; [rewrite St1, St2, <- (clean_eq_fieldT ds_strm _ _ ECv ltac:(reflexivity)); reflexivity|].
    split; [| split; [exact Yt1 | split; [exact Yt2 | exact Mt1]]].
    split; [exact Qt|]. split; [exact Jt1|]. split; [exact Jt2|]. split; [exact Et1 | exact Et2]. }
  destruct (dparams_flushes u1 level strategy) eqn:Hfl.
  -
    assert (EX1 : exists x, x = deflate_core u1 Z_BLOCK) by (eexists; reflexivity). destruct EX1 as [[t1 e1] X1].
    assert (EX2 : exists x, x = deflate_core u2 Z_BLOCK) by (eexists; reflexivity). destruct EX2 as [[t2 e2] X2].
    rewrite <- X1, <- X2 in *. cbn [fst snd] in Ee, HQc, Ic1, Ic2, U1, U2. subst e2.
    destruct U1 as (Dt1 & Yt1 & Mt1). destruct U2 as (Dt2 & Yt2 & Mt2).
    pose proof (DQ_clean _ _ HQc) as ECt.
    destruct (e1 =? Z_STREAM_ERROR).
    { cbn [fst snd]. split; [rewrite <- (clean_eq_fieldT ds_strm _ _ ECt ltac:(reflexivity)); reflexivity|].
      split; [| split; [exact Yt1 | split; [exact Yt2 | exact Mt1]]]. split; [exact HQc|]. split; [exact Ic1|]. split; [exact Ic2|]. split; assumption. }
    rewrite <- (clean_eq_fieldT ds_strm _ _ ECt ltac:(reflexivity)), <- (clean_eq_fieldT ds_strstart _ _ ECt ltac:(reflexivity)),
      <- (clean_eq_fieldT ds_block_start _ _ ECt ltac:(reflexivity)), <- (clean_eq_fieldT ds_lookahead _ _ ECt ltac:(reflexivity)).
    destruct (negb (cs_avail_in (ds_strm t1) =? 0) || negb (ds_strstart t1 - ds_block_start t1 + ds_lookahead t1 =? 0)) eqn:Et.
    { cbn [fst snd]. split; [rewrite <- (clean_eq_fieldT ds_strm _ _ ECt ltac:(reflexivity)); reflexivity|].
      split; [| split; [exact Yt1 | split; [exact Yt2 | exact Mt1]]]. split; [exact HQc|]. split; [exact Ic1|]. split; [exact Ic2|]. split; assumption. }
    apply Bool.orb_false_iff in Et. destruct Et as [Ea Eb]. apply Bool.negb_false_iff in Ea. apply Bool.negb_false_iff in Eb.
    apply Z.eqb_eq in Ea. apply Z.eqb_eq in Eb.
    apply (TAIL t1 t2 HQc Ic1 Ic2 Dt1 Dt2 Yt1 Yt2 Mt1). intros _. left. exact (conj Ea Eb).
  -
    apply (TAIL u1 u2 HQ0 I10 I20 DD10 DD20 HZ10 HZ20 Hm10).
    intros NE. right. unfold dparams_flushes in Hfl.
    apply Bool.andb_false_iff in Hfl. destruct Hfl as [Hfl|Hfl].
    + exfalso. apply Bool.orb_false_iff in Hfl. destruct Hfl as [_ Hfl]. apply Bool.negb_false_iff in Hfl. apply Z.eqb_eq in Hfl. exact (NE Hfl).
    + apply Bool.negb_false_iff in Hfl. apply Z.eqb_eq in Hfl. exact Hfl.
Qed.
