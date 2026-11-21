(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs Zg_inffast_exit Zg_inffast_copy Zg_inffast_win.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Zg_inffast_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem RefInffast4 RefInffast17 RefInflateOkb RefInflateA_DIST1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition ff_dres2 (x : ffx) (op : Z) (f : ffs) : fstep :=
  let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
  let f := fdrop f op in
  let op := wrap32 (f_out f - x_beg x) in
  if op <? f_dist f then ff_winres x f
  else
    let f := fset_from f (FOut (f_out f - f_dist f)) in
    let f := copy_do3 x f in
    FCont (copy_tail x f).

Definition ff_distres (x : ffx) (here : Z) (f : ffs) : fstep :=
  let f := fset_dist f (code_val here) in
  let op := Z.land (code_op here) 15 in
  let f := if f_bits f <? op then
             let f := fpull x f in
             if f_bits f <? op then fpull x f else f
           else f in
  ff_dres2 x op f.

Definition ff_dok2 (x : ffx) (ON WN op : Z) (f : ffs) : bool :=
  (op <=? f_bits f) &&
  let f := fset_dist f (wrap32 (f_dist f + Z.land (wrap32 (f_hold f)) (zmask op))) in
  let f := fdrop f op in
  (1 <=? f_dist f) && (3 <=? f_len f) && (f_out f + f_len f <=? ON) &&
  let op := wrap32 (f_out f - x_beg x) in
  if op <? f_dist f then
    let op := wrap32 (f_dist f - op) in
    if (x_whave x <? op) && negb (x_sane x =? 0) then true
    else window_ok x ON WN (fset_op f op)
  else true.
Definition ff_distok (x : ffx) (IN ON WN here : Z) (f : ffs) : bool :=
  let f := fset_dist f (code_val here) in
  let op := Z.land (code_op here) 15 in
  (if f_bits f <? op then (f_in f + 1 <=? IN) && (if f_bits f + 8 <? op then f_in f + 2 <=? IN else true) else true) &&
  let f := if f_bits f <? op then
             let f := fpull x f in
             if f_bits f <? op then fpull x f else f
           else f in
  ff_dok2 x ON WN op f.

Lemma dodist_S : forall k x s here f,
  dodist (S k) x s here f =
    let f := fdrop f (code_bits here) in
    if negb (Z.land (code_op here) 16 =? 0) then ff_distres x here f
    else if Z.land (code_op here) 64 =? 0 then dodist k x s (code_at s (is_distcode s) (code_val here + Z.land (f_hold f) (zmask (code_op here)))) f
    else FBreak f BAD (Some MSG_ff_invalid_distance_code).
Proof. intros. cbv delta [ff_distres ff_dres2 ff_winres ff_place]. cbv zeta. cbn delta [dodist] fix iota beta zeta. reflexivity. Qed.

Lemma dodist_ok_S : forall k x s IN ON WN here f,
  dodist_ok x s IN ON WN (S k) here f =
    (code_bits here <=? f_bits f) &&
    let f := fdrop f (code_bits here) in
    if negb (Z.land (code_op here) 16 =? 0) then ff_distok x IN ON WN here f
    else if Z.land (code_op here) 64 =? 0 then
      (code_op here <? 16) &&
      let i := code_val here + Z.land (f_hold f) (zmask (code_op here)) in
      (i <? ctab_len (is_distcode s)) && dodist_ok x s IN ON WN k (code_at s (is_distcode s) i) f
    else true.
Proof. intros. cbv delta [ff_distok ff_dok2]. cbv zeta. cbn delta [dodist_ok] fix iota beta zeta. reflexivity. Qed.

Lemma cnot_small : forall a, 0 <= a < 2^64 -> cnot a = 18446744073709551615 - a.
Proof.
  intros a Ha. unfold cnot. change 18446744073709551615 with (Z.ones 64) at 1. rewrite Z.land_ones, Z.mod_small by lia.
  apply zb_lxor_ones. exact Ha.
Qed.
Lemma cnot_land : forall a, 0 <= a < 2^64 -> Z.land (cnot a) 18446744073709551615 = 18446744073709551615 - a.
Proof. intros a Ha. rewrite cnot_small by exact Ha. apply land_ones64. lia. Qed.
Ltac gCN := zstep; let K := fresh "KC" in if_cases K; br_norm K;
  [exfalso; rewrite ?cnot_land, ?cnot_small, ?zb_lxor_ones in K by lia; rewrite ?land_ones64 in K by lia; lia | clear K].
Lemma cp_addr_even : forall L p, il_As L mod 16 = 0 -> cp_addr L p mod 2 = 0.
Proof.
  intros L p HA. destruct p as [ofs| |]; cbn [cp_addr]; unfold Z_LENFIX, Z_DISTFIX; Z.div_mod_to_equations; lia.
Qed.
Ltac alcp L p XAl := rewrite land1_mod2 by (pose proof (cp_addr_even L p XAl); Z.div_mod_to_equations; lia).

Section DIST.
Variables (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave).
Local Notation L := (ix_L X).
Local Notation xx := (ffx_of s c r).
Local Ltac bfact H := first [apply Z.leb_le in H | apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.leb_gt in H].

Lemma finv_drop : forall f g op, FINV X s c f -> 0 <= op <= f_bits f ->
  f_in g = f_in f -> f_out g = f_out f -> f_ob g = f_ob f -> f_bits g = wrap32 (f_bits f - op) -> f_hold g = Z.shiftr (f_hold f) op ->
  FINV X s c g.
Proof.
  intros f g op (Fb & Fh & Fin & Fout & Fob & Fbytes) Hop E1 E2 E3 E4 E5. unfold FINV. rewrite E1, E2, E3, E4, E5.
  rewrite wrap32_id by lia. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (shiftr_lt_pow2 (f_hold f) (f_bits f) op ltac:(lia) ltac:(lia)) as HS.
  pose proof (Z.pow_pos_nonneg 2 op ltac:(lia) ltac:(lia)).
  repeat (split; [first [lia | apply Z.div_pos; lia] |]). exact Fbytes.
Qed.

Lemma finv_pull : forall f, FINV X s c f -> ff_typed X s c r -> f_bits f <= 48 -> f_in f + 1 <= arr_len (ic_input c) ->
  FINV X s c (fpull xx f)
  /\ fpull xx f = mkF (f_in f + 1) (f_out f) (f_hold f + arr_get (ic_input c) (f_in f) * 2 ^ f_bits f) (f_bits f + 8)
                      (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Proof.
  intros f (Fb & Fh & Fin & Fout & Fob & Fbytes) HT Hb Hin.
  destruct HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & _).
  destruct (fpull_eq xx f ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn [x_input ffx_of]; apply Bin)) as [E B]. cbn [x_input ffx_of] in E, B.
  split; [| exact E]. rewrite E. unfold FINV. cbn [f_in f_out f_hold f_bits f_ob].
  pose proof (Bin (f_in f)). pose proof (Z.pow_pos_nonneg 2 (f_bits f) ltac:(lia) ltac:(lia)).
  repeat (split; [first [lia | nia] |]). exact Fbytes.
Qed.

Lemma ff_in_read : forall j me m a, ix_ok X -> ff_typed X s c r -> FFMs X s c r sv me -> munch (ffW X) me m ->
  0 <= j < arr_len (ic_input c) -> a = wa (il_NI (ix_L X) + j) ->
  ov_read_bytes usegs m a 1 = Some [Z_to_bv 8 (arr_get (ic_input c) j)] /\ 0 <= arr_get (ic_input c) j < 256.
Proof.
  intros j me m a XO HT HS MU Hj ->.
  destruct HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & _).
  destruct HS as (FR & GA & GT & ZS & Gc & Gwin & IN & ARRS & LAY). ix_open XO. unfold iin in IN. unfold ffW in MU.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  assert (Hj' : 0 <= j < arr_len (ix_input X)) by (rewrite <- Pin; exact Hj).
  eapply u8ro_transport in IN; [| exact MU| cbn [disjoint_from]; rewrite av8_length; slia].
  split; [| apply Bin]. rewrite Pin.
  apply (u8ro_read usegs m (il_NI (ix_L X)) (av8 (ix_input X) (arr_len (ix_input X))) j); [exact IN| apply av8_nth; exact Hj'| lia| reflexivity].
Qed.

Lemma finv_pull2 : forall f, FINV X s c f -> ff_typed X s c r -> f_bits f < 15 -> f_in f + 2 <= arr_len (ic_input c) ->
  FINV X s c (fpull xx (fpull xx f))
  /\ fpull xx (fpull xx f) = mkF (f_in f + 2) (f_out f)
        (f_hold f + arr_get (ic_input c) (f_in f) * 2 ^ f_bits f + arr_get (ic_input c) (f_in f + 1) * 2 ^ (f_bits f + 8)) (f_bits f + 16)
        (f_len f) (f_dist f) (f_op f) (f_from f) (f_ob f).
Proof.
  intros f FI HT Hb Hin.
  destruct (finv_pull f FI HT ltac:(lia) ltac:(lia)) as [FI1 E1].
  destruct (finv_pull (fpull xx f) FI1 HT ltac:(rewrite E1; cbn; lia) ltac:(rewrite E1; cbn; lia)) as [FI2 E2].
  rewrite E1 in E2. cbn [f_in f_out f_hold f_bits f_len f_dist f_op f_from f_ob] in E2.
  replace (f_in f + 1 + 1) with (f_in f + 2) in E2 by lia. replace (f_bits f + 8 + 8) with (f_bits f + 16) in E2 by lia.
  split; [exact FI2 | rewrite E1; exact E2].
Qed.

Definition ff_dlres (f : ffs) : fstep :=
  let f := fpull2_if xx f in
  let here := code_at s (is_distcode s) (Z.land (f_hold f) (x_dmask xx)) in
  dodist 4 xx s here f.
Definition ff_dlok (f : ffs) : bool :=
  pull2_ok (arr_len (ic_input c)) f &&
  let f := fpull2_if xx f in
  let i := Z.land (f_hold f) (x_dmask xx) in
  (i <? ctab_len (is_distcode s)) && dodist_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) 4 (code_at s (is_distcode s) i) f.


Lemma ff_dtail : forall f2 e (x1 x5 x6 x7 x9 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f2 ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f2) (f_out f2) m ->
  0 <= f_dist f2 < 65536 -> 0 <= e <= 15 -> e <= f_bits f2 ->
  ff_dok2 xx (arr_len (ic_outbuf c)) (arr_len (is_window s)) e f2 = true ->
  evt usegs (TPOST X s c r sv me (ff_dres2 xx e f2))
    (FFL X s c r f2 0x22a04 x1 x5 x6 x7 x9 (wz e) (wz (f_dist f2)) (wz (f_len f2)) x29 m).
Proof.
  intros f2 e x1 x5 x6 x7 x9 x29 me m XO HRS HT FI HS MU0 WM0 HC Rval Re He DOK. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  pose proof (ones_range15 e Re) as ROe.
  unfold ff_dok2 in DOK. cbn [f_bits f_dist f_hold f_out f_len f_op fset_dist fdrop fset_op fset_hold fset_bits] in DOK.
  change (x_whave xx) with (is_whave s) in DOK. change (x_sane xx) with (is_sane s) in DOK.
  apply andb_prop in DOK. destruct DOK as [D1 DOK]. apply andb_prop in DOK. destruct DOK as [DOK DW].
  apply andb_prop in DOK. destruct DOK as [DOK D4]. apply andb_prop in DOK. destruct DOK as [D2 D3]. bfact D1. bfact D2. bfact D3. bfact D4.
  unfold ff_dres2. cbn [f_bits f_dist f_hold f_out f_len f_op f_in f_ob f_from fset_dist fdrop fset_op fset_hold fset_bits fset_from].
  rewrite land_wrap32_zmask in D2, DW |- * by lia.
  pose proof (Z.mod_pos_bound (f_hold f2) (2 ^ e) ltac:(apply Z.pow_pos_nonneg; lia)) as Rmod.
  assert (Rpe : 2 ^ e <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2 ^ 15) with 32768 in Rpe.
  rewrite (wrap32_id (f_dist f2 + f_hold f2 mod 2 ^ e)) in D2, DW |- * by lia.
  set (dist := f_dist f2 + f_hold f2 mod 2 ^ e) in *.
  destruct HC as [OUT MI].
  pose proof FR as FRm. unfold ff_frame_cells, ff_sp in FRm. unfold ffW in MU0.
  eapply rw_cells_transport in FRm; [| exact MU0| exact WM0| cbn [disjoint_from]; cells_cbv; slia].
  unfold FFL, ff_sp. fnorm.
  zs. do 2 zs. rewrite clang_mask32 by lia. zs. rewrite (Z.land_ones (f_hold f2) e) by lia.
  zs. rewrite (land63_small e) by lia.
  do 3 zs.
  replace (f_hold f2 mod 2 ^ e + f_dist f2) with dist by lia.
  rewrite (wrap32_id (f_out f2 - x_beg xx)) in DW |- * by lia.
  assert (FI3 : FINV X s c (fdrop (fset_dist f2 dist) e)) by (eapply (finv_drop f2 _ e FI); [lia| reflexivity ..]).
  zstep. br_cases K.
  -
    replace (f_out f2 - x_beg xx <? dist) with false by (symmetry; apply Z.ltb_ge; lia).
    eapply evt_eq; [| eapply (ff_do3_tp X s c r sv (fset_from (fdrop (fset_dist f2 dist) e) (FOut (f_out f2 - dist))) _ _ _ _ _ _ _ me m); fnorm;
      first [ assumption | reflexivity | split; [exact OUT| exact MI] | lia ] ].
    unfold PC_FF_OUT. eapply FFL_intro2; fnorm; ffreg.
  -
    replace (f_out f2 - x_beg xx <? dist) with true in DW |- * by (symmetry; apply Z.ltb_lt; lia).
    eapply evt_eq; [| eapply (ff_win X s c r sv (fdrop (fset_dist f2 dist) e) _ _ _ _ _ _ me m); fnorm;
      first [ assumption | split; [exact OUT| exact MI] | rewrite wrap32_id by lia; lia | lia
            | rewrite (wrap32_id (f_out f2 - x_beg xx)) by lia; exact DW ] ].
    unfold PC_FF_WIN. eapply FFL_intro2; fnorm; ffreg.
Qed.

Lemma ff_dist : forall p i f (x1 x6 x7 x9 x23 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  p = is_distcode s -> 0 <= i < ctab_size p ->
  ff_distok xx (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) (code_at s (is_distcode s) i) f = true ->
  evt usegs (TPOST X s c r sv me (ff_distres xx (code_at s (is_distcode s) i) f))
    (FFL X s c r f PC_FF_DIST x1 (wz (code_op (code_at s (is_distcode s) i))) x6 x7 x9 (wz (cp_addr L (is_distcode s) + 4 * i)) x23 (wz (f_len f)) x29 m).
Proof.
  intros p i f x1 x6 x7 x9 x23 x29 me m XO HRS HT FI HS MU0 WM0 HC Ep Hi DOK. subst p. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  pose proof (code_op_range (code_at s (is_distcode s) i)) as ROP. pose proof (code_val_range (code_at s (is_distcode s) i)) as Rval.
  assert (Re : 0 <= Z.land (code_op (code_at s (is_distcode s) i)) 15 <= 15).
  { pose proof (land_ones_range (code_op (code_at s (is_distcode s) i)) 4 ltac:(lia)) as HH. change (2^4 - 1) with 15 in HH. change (2^4) with 16 in HH. lia. }
  unfold ff_distres. unfold ff_distok in DOK. cbv zeta in DOK. cbn [f_bits f_in fset_dist] in DOK.
  set (e := Z.land (code_op (code_at s (is_distcode s) i)) 15) in *.
  apply andb_prop in DOK. destruct DOK as [DP DOK].
  pose proof Gc as Gc'. unfold ffW in MU0.
  apply (icodes_munch me m L s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
  pose proof CPD as CPO. destruct HC as [OUT MI].
  unfold FFL, ff_sp, PC_FF_DIST.
  pose proof (code_rd_val m L s (is_distcode s) i (wa (cp_addr L (is_distcode s) + 4 * i + 2)) MI Gc' CPO Hi eq_refl) as RD.
  zs. rewrite (zx16_small (code_val (code_at s (is_distcode s) i))) by exact Rval. clear RD.
  zs. change (Z.land (code_op (code_at s (is_distcode s) i)) 15) with e.
  zstep. br_cases K0.
  -
    replace (f_bits f <? e) with false in DOK |- * by (symmetry; apply Z.ltb_ge; lia). cbv iota in DOK. cbv iota.
    eapply evt_eq; [| eapply (ff_dtail (fset_dist f (code_val (code_at s (is_distcode s) i))) e _ _ _ _ _ _ me m); fnorm;
      first [assumption | split; [exact OUT| exact MI] | lia] ].
    eapply FFL_intro2; fnorm; ffreg.
  - replace (f_bits f <? e) with true in DP, DOK |- * by (symmetry; apply Z.ltb_lt; lia). cbv iota in DOK. cbv iota.
    apply andb_prop in DP. destruct DP as [DP1 DP2]. bfact DP1.
    destruct (finv_pull (fset_dist f (code_val (code_at s (is_distcode s) i))) ltac:(exact FI) HT ltac:(fnorm; lia) ltac:(fnorm; lia)) as [FI2 EP].
    fnorm in EP. rewrite EP in FI2. rewrite EP in DOK. rewrite ?EP in DP2. rewrite EP.
    fnorm in DP2. fnorm in DOK. fnorm.
    zstep. gF.
    destruct (ff_in_read (f_in f) me m (wa (il_NI L + f_in f)) XO HT HS MU0 ltac:(lia) eq_refl) as [RD RV].
    zs. cbv beta. rewrite (bv8_small _ RV). clear RD.
    set (b0 := arr_get (ic_input c) (f_in f)) in *.
    zs. rewrite (land63_small (f_bits f)) by lia. rewrite (Z.shiftl_mul_pow2 b0 (f_bits f)) by lia.
    do 2 zs. zstep. br_cases K1.
    +
      replace (f_bits f + 8 <? e) with false in DOK by (symmetry; apply Z.ltb_ge; lia).
      replace (f_bits f + 8 <? e) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota in DOK. cbv iota.
      do 2 zs.
      eapply evt_eq; [| eapply (ff_dtail _ e _ _ _ _ _ _ me m); fnorm; first [eassumption | split; [exact OUT| exact MI] | lia] ].
      eapply FFL_intro2; fnorm; ffreg.
    +
      replace (f_bits f + 8 <? e) with true in DP2 by (symmetry; apply Z.ltb_lt; lia). bfact DP2.
      replace (f_bits f + 8 <? e) with true in DOK by (symmetry; apply Z.ltb_lt; lia).
      replace (f_bits f + 8 <? e) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota in DOK. cbv iota.
      match goal with |- context [fpull xx ?F] =>
        destruct (finv_pull F FI2 HT ltac:(fnorm; lia) ltac:(fnorm; lia)) as [FI3 EP2] end.
      fnorm in EP2. rewrite EP2 in FI3. rewrite EP2 in DOK. rewrite EP2. fnorm in DOK. fnorm.
      match goal with |- context [ff_dres2 xx e ?F] => set (f2 := F) in * end.
      zstep. br_false.
      destruct (ff_in_read (f_in f + 1) me m (wa (il_NI L + f_in f + 1)) XO HT HS MU0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as [RD RV1].
      zs. cbv beta. rewrite (bv8_small _ RV1). clear RD.
      set (b1 := arr_get (ic_input c) (f_in f + 1)) in *.
      zs. zs. rewrite (land63_small (f_bits f + 8)) by lia. rewrite (Z.shiftl_mul_pow2 b1 (f_bits f + 8)) by lia.
      do 3 zs.
      eapply evt_eq; [| eapply (ff_dtail f2 e _ _ _ _ _ _ me m); subst f2; fnorm; first [eassumption | split; [exact OUT| exact MI] | lia] ].
      eapply FFL_intro2; subst f2; fnorm; ffreg.
Qed.

Lemma ff_dodist : forall k p i f (x1 x5 x6 x7 x9 x23 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  p = is_distcode s -> 0 <= i < ctab_size p ->
  dodist_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) k (code_at s (is_distcode s) i) f = true ->
  evt usegs (TPOST X s c r sv me (dodist k xx s (code_at s (is_distcode s) i) f))
    (FFL X s c r f PC_FF_DODIST x1 x5 x6 x7 x9 (wz (cp_addr L (is_distcode s) + 4 * i)) x23 (wz (f_len f)) x29 m).
Proof.
  intros k; induction k as [|k IH];
    intros p i f x1 x5 x6 x7 x9 x23 x29 me m XO HRS HT FI HS MU0 WM0 HC Ep Hi DOK; subst p; [cbn [dodist_ok] in DOK; discriminate DOK|].
  tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  pose proof (code_op_range (code_at s (is_distcode s) i)) as ROP. pose proof (code_val_range (code_at s (is_distcode s) i)) as RVAL.
  pose proof (code_bits_range (code_at s (is_distcode s) i)) as RB.
  rewrite dodist_ok_S in DOK. cbv zeta in DOK. apply andb_prop in DOK. destruct DOK as [DB DOK]. bfact DB.
  rewrite dodist_S. cbv zeta.
  pose proof Gc as Gc'. unfold ffW in MU0.
  apply (icodes_munch me m L s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
  pose proof CPD as CPO. pose proof HC as [OUT MI].
  pose proof (cp_addr_rng L (is_distcode s) i CPO Hi ltac:(lia)) as CPR.
  unfold FFL, ff_sp, PC_FF_DODIST.
  pose proof (code_rd_bits m L s (is_distcode s) i (wa (cp_addr L (is_distcode s) + 4 * i + 1)) MI Gc' CPO Hi eq_refl) as RD.
  zs. cbv beta. rewrite (bv8_small (code_bits (code_at s (is_distcode s) i))) by exact RB. clear RD.
  gF.
  pose proof (code_rd_op m L s (is_distcode s) i (wa (cp_addr L (is_distcode s) + 4 * i)) MI Gc' CPO Hi eq_refl) as RD.
  zs. cbv beta. rewrite (bv8_small (code_op (code_at s (is_distcode s) i))) by exact ROP. clear RD.
  zs. rewrite (land63_small (code_bits (code_at s (is_distcode s) i))) by lia.
  do 2 zs.
  assert (FI2 : FINV X s c (fdrop f (code_bits (code_at s (is_distcode s) i)))) by (eapply (finv_drop f _ (code_bits (code_at s (is_distcode s) i)) FI); [lia| reflexivity ..]).
  zstep. br_cases K16.
  -
    replace (Z.land (code_op (code_at s (is_distcode s) i)) 16 =? 0) with false in DOK |- * by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in DOK |- *.
    eapply evt_eq; [| eapply (ff_dist (is_distcode s) i (fdrop f (code_bits (code_at s (is_distcode s) i))) _ _ _ _ _ _ me m); fnorm;
      first [ eassumption | reflexivity | split; [exact OUT| exact MI] | lia | exact DOK ] ].
    unfold PC_FF_DIST. eapply FFL_intro2; fnorm; ffreg.
  - replace (Z.land (code_op (code_at s (is_distcode s) i)) 16 =? 0) with true in DOK |- * by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in DOK |- *.
    zs. zstep. br_cases K64.
    +
      replace (Z.land (code_op (code_at s (is_distcode s) i)) 64 =? 0) with false in DOK |- * by (symmetry; apply Z.eqb_neq; lia).
      pose proof (ffm_after_copy X s c r sv (fdrop f (code_bits (code_at s (is_distcode s) i))) me m XO Whas HS MU0 WM0 ltac:(fnorm; exact HC)) as HM.
      eapply evt_mono; [ eapply evt_eq; [| eapply (ff_brk2 X s c r sv (fdrop f (code_bits (code_at s (is_distcode s) i))) _ _ _ _ _ _ _ _ _ m);
                                            first [exact XO | exact HRS | exact HT | exact FI2 | exact HM] ];
                         unfold PC_FF_BRK2; eapply FFL_intro2; fnorm; ffreg
                       | intros ms' PO; eapply tpost_of_brk; [exact PO| exact FI2| exact MU0| exact WM0] ].
    +
      replace (Z.land (code_op (code_at s (is_distcode s) i)) 64 =? 0) with true in DOK |- * by (symmetry; apply Z.eqb_eq; lia).
      apply andb_prop in DOK. destruct DOK as [D16 DOK]. apply andb_prop in DOK. destruct DOK as [DI DOK]. bfact D16. bfact DI.
      set (op := code_op (code_at s (is_distcode s) i)) in *.
      pose proof (ones_range15 op ltac:(lia)) as ROo.
      rewrite (land_zmask (Z.shiftr (f_hold f) (code_bits (code_at s (is_distcode s) i))) op) in DI, DOK |- * by lia.
      cbn [f_hold fdrop fset_bits fset_hold] in DI, DOK.
      set (h1 := Z.shiftr (f_hold f) (code_bits (code_at s (is_distcode s) i))) in *.
      assert (Rh1 : 0 <= h1 < 2^64).
      { subst h1. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (code_bits (code_at s (is_distcode s) i)) ltac:(lia) ltac:(lia)).
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
      pose proof (Z.mod_pos_bound h1 (2 ^ op) ltac:(apply Z.pow_pos_nonneg; lia)) as Rmod.
      set (i2 := code_val (code_at s (is_distcode s) i) + h1 mod 2 ^ op) in *.
      rewrite ctab_size_len in Hi.
      pose proof (cp_addr_rng L (is_distcode s) i2 CPO ltac:(rewrite ctab_size_len; lia) ltac:(lia)) as CPR2.
      pose proof (code_rd_val m L s (is_distcode s) i (wa (cp_addr L (is_distcode s) + 4 * i + 2)) MI Gc' CPO ltac:(rewrite ctab_size_len; lia) eq_refl) as RD.
      zs. rewrite (zx16_small (code_val (code_at s (is_distcode s) i))) by exact RVAL. clear RD.
      zs. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      gCN. gF.
      zs. do 2 zs. rewrite clang_mask32 by lia. zs. rewrite (Z.land_ones h1 op) by lia.
      zs. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
      zs. gCN.
      zs. zs. alcp (ix_L X) (is_distcode s) XAl.
      zstep. br_true.
      eapply evt_eq; [| eapply (IH (is_distcode s) i2 (fdrop f (code_bits (code_at s (is_distcode s) i))) _ _ _ _ _ _ _ me m); fnorm;
        first [ eassumption | reflexivity | split; [exact OUT| exact MI] | rewrite ctab_size_len; lia | exact DOK ] ].
      eapply FFL_intro2; fnorm; ffreg.
Qed.

Lemma ff_dlook2 : forall f2 (x1 x5 x6 x7 x9 x13 x23 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f2 ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f2) (f_out f2) m ->
  (Z.land (f_hold f2) (x_dmask xx) <? ctab_len (is_distcode s)) &&
    dodist_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) 4
      (code_at s (is_distcode s) (Z.land (f_hold f2) (x_dmask xx))) f2 = true ->
  evt usegs (TPOST X s c r sv me (dodist 4 xx s (code_at s (is_distcode s) (Z.land (f_hold f2) (x_dmask xx))) f2))
    (FFL X s c r f2 PC_FF_DLOOK x1 x5 x6 x7 x9 x13 x23 (wz (f_len f2)) x29 m).
Proof.
  intros f2 x1 x5 x6 x7 x9 x13 x23 x29 me m XO HRS HT FI HS MU0 WM0 HC D2. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  apply andb_prop in D2. destruct D2 as [DI D2]. bfact DI.
  assert (EDM : x_dmask xx = zmask (is_distbits s)) by reflexivity. rewrite EDM in DI, D2 |- *.
  set (i := Z.land (f_hold f2) (zmask (is_distbits s))) in *.
  assert (Ri : 0 <= i) by (subst i; apply Z.land_nonneg; left; lia).
  pose proof CPD as CPO.
  pose proof (cp_addr_rng L (is_distcode s) i CPO ltac:(rewrite ctab_size_len; lia) ltac:(lia)) as CPR.
  pose proof FR as FRm. unfold ff_frame_cells, ff_sp in FRm. unfold ffW in MU0.
  eapply rw_cells_transport in FRm; [| exact MU0| exact WM0| cbn [disjoint_from]; cells_cbv; slia].
  unfold FFL, ff_sp, PC_FF_DLOOK. cbn [ffx_of x_dmask] in FRm.
  do 3 zs. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. fold i.
  zs. gF. do 3 zs. gX. zs. alcp (ix_L X) (is_distcode s) XAl. gF. gF.
  eapply evt_eq; [| eapply (ff_dodist 4 (is_distcode s) i f2 _ _ _ _ _ _ _ me m);
    first [ eassumption | reflexivity | rewrite ctab_size_len; lia | exact D2 ] ].
  unfold PC_FF_DODIST. eapply FFL_intro2; fnorm; ffreg.
Qed.

Lemma ff_dpull : forall f (x1 x5 x6 x7 x9 x13 x23 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  f_bits f < 15 -> ff_dlok f = true ->
  evt usegs (TPOST X s c r sv me (ff_dlres f))
    (FFL X s c r f 0x228f8 x1 x5 x6 x7 x9 x13 x23 (wz (f_len f)) x29 m).
Proof.
  intros f x1 x5 x6 x7 x9 x13 x23 x29 me m XO HRS HT FI HS MU0 WM0 HC Hb DOK. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  unfold ff_dlres. unfold ff_dlok, pull2_ok in DOK. cbv zeta in DOK. unfold fpull2_if in DOK |- *.
  replace (f_bits f <? 15) with true in DOK |- * by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in DOK. destruct DOK as [DP DOK]. bfact DP.
  destruct (finv_pull2 f FI HT ltac:(lia) ltac:(lia)) as [FI2 EP]. rewrite EP in FI2, DOK |- *.
  match goal with |- context [dodist 4 xx s _ ?F] => set (f2 := F) in * end.
  unfold FFL, ff_sp.
  zstep. gF. zstep. br_false.
  destruct (ff_in_read (f_in f) me m (wa (il_NI L + f_in f)) XO HT HS MU0 ltac:(lia) eq_refl) as [RD RV0].
  zs. cbv beta. rewrite (bv8_small _ RV0). clear RD.
  destruct (ff_in_read (f_in f + 1) me m (wa (il_NI L + f_in f + 1)) XO HT HS MU0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as [RD RV1].
  zs. cbv beta. rewrite (bv8_small _ RV1). clear RD.
  set (b0 := arr_get (ic_input c) (f_in f)) in *. set (b1 := arr_get (ic_input c) (f_in f + 1)) in *.
  do 2 zs.
  zs. rewrite (land63_small (f_bits f)) by lia. rewrite (Z.shiftl_mul_pow2 b0 (f_bits f)) by lia.
  zs. rewrite (land63_small (f_bits f + 8)) by lia. rewrite (Z.shiftl_mul_pow2 b1 (f_bits f + 8)) by lia.
  do 3 zs. rewrite lor16_small by lia.
  eapply evt_eq; [| eapply (ff_dlook2 f2 _ _ _ _ _ _ _ _ me m); subst f2; fnorm; first [eassumption | exact DOK] ].
  unfold PC_FF_DLOOK. eapply FFL_intro2; subst f2; fnorm; ffreg.
Qed.

Lemma ff_dlook : forall f (x1 x5 x6 x7 x9 x13 x23 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  ff_dlok f = true ->
  evt usegs (TPOST X s c r sv me (ff_dlres f))
    (FFL X s c r f 0x228f0 x1 x5 x6 x7 x9 x13 x23 (wz (f_len f)) x29 m).
Proof.
  intros f x1 x5 x6 x7 x9 x13 x23 x29 me m XO HRS HT FI HS MU0 WM0 HC DOK. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  unfold FFL, ff_sp. zs. zstep. br_cases K15.
  -
    unfold ff_dlres. unfold ff_dlok, pull2_ok in DOK. cbv zeta in DOK. unfold fpull2_if in DOK |- *.
    replace (f_bits f <? 15) with false in DOK |- * by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in DOK.
    eapply evt_eq; [| eapply (ff_dlook2 f _ _ _ _ _ _ _ _ me m); first [eassumption | exact DOK] ].
    unfold PC_FF_DLOOK. eapply FFL_intro2; fnorm; ffreg.
  - eapply evt_eq; [| eapply (ff_dpull f _ _ _ _ _ _ _ _ me m); first [eassumption | lia] ].
    eapply FFL_intro2; fnorm; ffreg.
Qed.
End DIST.
