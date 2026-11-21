(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs Zg_inffast_exit Zg_inffast_copy Zg_inffast_model Zg_inffast_win Zg_inffast_dist.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem RefInffast3 RefInffast17 RefInffast18 RefInflateOkb RefInflateA_DIST1 RefInflateArmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma le4_code_val_lo : forall v, firstn 1 (skipn 2 (le4 (wz v))) = [Z_to_bv 8 (wrap8 (code_val v))].
Proof.
  intros v. unfold le4, code_val, wrap8. cbn [Z_to_le_bytes firstn skipn]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change 255 with (Z.ones 8). change 65535 with (Z.ones 16).
  rewrite !Z.land_ones by lia. rewrite ?Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536.
  Z.div_mod_to_equations. lia.
Qed.

Section LEN.
Variables (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave).
Local Notation xx := (ffx_of s c r).
Local Ltac bfact H := first [apply Z.leb_le in H | apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.leb_gt in H].

Definition ff_lenres (here : Z) (f : ffs) : fstep :=
  let f := fset_len f (code_val here) in
  let op := Z.land (code_op here) 15 in
  let f := if negb (op =? 0) then
             let f := if f_bits f <? op then fpull xx f else f in
             let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
             fdrop f op
           else f in
  ff_dlres s c r f.
Definition ff_lenok (here : Z) (f : ffs) : bool :=
  let f := fset_len f (code_val here) in
  let op := Z.land (code_op here) 15 in
  (if negb (op =? 0) then if f_bits f <? op then (f_in f + 1 <=? arr_len (ic_input c)) && (op <=? f_bits f + 8) else true else true) &&
  let f := if negb (op =? 0) then
             let f := if f_bits f <? op then fpull xx f else f in
             let f := fset_len f (wrap32 (f_len f + Z.land (wrap32 (f_hold f)) (zmask op))) in
             fdrop f op
           else f in
  ff_dlok s c r f.
Definition ff_l2res (k : nat) (here : Z) (f : ffs) : fstep :=
  if negb (Z.land (code_op here) 16 =? 0) then ff_lenres here f
  else if Z.land (code_op here) 64 =? 0 then dolen k xx s (code_at s (is_lencode s) (code_val here + Z.land (f_hold f) (zmask (code_op here)))) f
  else if negb (Z.land (code_op here) 32 =? 0) then FBreak f TYPE None
  else FBreak f BAD (Some MSG_ff_invalid_literal_length_code).
Definition ff_l2ok (k : nat) (here : Z) (f : ffs) : bool :=
  if negb (Z.land (code_op here) 16 =? 0) then ff_lenok here f
  else if Z.land (code_op here) 64 =? 0 then
    (code_op here <? 16) &&
    let i := code_val here + Z.land (f_hold f) (zmask (code_op here)) in
    (i <? ctab_len (is_lencode s)) && dolen_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) k (code_at s (is_lencode s) i) f
  else true.

Lemma dolen_S : forall k here f,
  dolen (S k) xx s here f =
    let f := fdrop f (code_bits here) in
    if code_op here =? 0 then FCont (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) (wrap8 (code_val here)))) (f_out f + 1))
    else ff_l2res k here f.
Proof. intros. cbv delta [ff_l2res ff_lenres ff_dlres]. cbv zeta. cbn delta [dolen] fix iota beta zeta. reflexivity. Qed.
Lemma dolen_ok_S : forall k here f,
  dolen_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) (S k) here f =
    (code_bits here <=? f_bits f) &&
    let f := fdrop f (code_bits here) in
    if code_op here =? 0 then f_out f <? arr_len (ic_outbuf c) else ff_l2ok k here f.
Proof. intros. cbv delta [ff_l2ok ff_lenok ff_dlok]. cbv zeta. cbn delta [dolen_ok] fix iota beta zeta. reflexivity. Qed.

Lemma ff_lit : forall p i f (x1 x21 x25 x26 x27 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c sv me -> munch (ffW X) me m -> wmono psegs me m -> CPM X c (f_ob f) (f_out f) m ->
  p = is_lencode s -> 0 <= i < ctab_size p -> f_out f < arr_len (ic_outbuf c) ->
  evt psegs (TPOST X s c r sv me (FCont (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) (wrap8 (code_val (code_at s p i))))) (f_out f + 1))))
    (FFL X s c r f PC_FF_LIT x1 (wz (cp_addr (ix_L X) p + 4 * i)) x21 x25 x26 x27 m).
Proof.
  intros p i f x1 x21 x25 x26 x27 me m XO HRS HT FI HS MU0 WM0 HC Ep Hi Ron. subst p. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  destruct HC as [OUT MI].
  pose proof Gc as Gc'. unfold ffW in MU0.
  apply (icodes_munch me m (ix_L X) s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (f_ob f)) (f_out f) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  set (v := wrap8 (code_val (code_at s (is_lencode s) i))). pose proof (wrap8_range (code_val (code_at s (is_lencode s) i))) as RV. fold v in RV. change (2^8) with 256 in RV.
  unfold FFL, ff_sp, PC_FF_LIT.
  pose proof (code_rd m (ix_L X) s (is_lencode s) i 2 1 (wa (cp_addr (ix_L X) (is_lencode s) + 4 * i + Z.of_nat 2)) MI Gc' CPL Hi ltac:(lia) eq_refl) as RD.
  rewrite le4_code_val_lo in RD. fold v in RD. change (Z.of_nat 2) with 2 in RD.
  zs. cbv beta. rewrite (bv8_small v) by lia. clear RD.
  zs.
  cp_store OUT LOB (f_ob f) (f_out f) v RV.
  pose proof (obt_step (f_ob f) (f_out f) v Fbytes ltac:(lia) RV) as OBT1.
  zs.
  apply evt_done. cbn [TPOST]. do 7 eexists.
  split; [eapply FFL_intro2; fnorm; ffreg|].
  split; [eapply munch_weaken; [|exact MU0]; unfold sub_fp, ffW, ffWb; cbn [outside]; intros; lia|].
  split; [exact WM0|]. split; [assumption|].
  destruct (FFMs_transport X s c sv me _ XO Whas HS MU0 WM0) as (FR' & GA' & GT' & ZS' & Gc'' & Gwin' & IN' & ARRS' & LAY').
  split.
  - unfold FFM, FFMg. fnorm.
    split; [exact FR'|]. split; [exact GA'|]. split; [exact GT'|]. split; [exact ZS'|]. split; [exact Gc''|]. split; [exact Gwin'|].
    split; [exact IN'|]. split; [exact OUT|]. split; [assumption|]. split; [exact ARRS'| exact LAY'].
  - unfold FINV. fnorm. rewrite arr_len_set. repeat (split; [lia|]). exact OBT1.
Qed.

Lemma ff_len : forall p i f (x1 x21 x26 x27 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c sv me -> munch (ffW X) me m -> wmono psegs me m -> CPM X c (f_ob f) (f_out f) m ->
  p = is_lencode s -> 0 <= i < ctab_size p -> ff_lenok (code_at s p i) f = true ->
  evt psegs (TPOST X s c r sv me (ff_lenres (code_at s p i) f))
    (FFL X s c r f PC_FF_LEN x1 (wz (cp_addr (ix_L X) p + 4 * i)) x21 (wz (code_op (code_at s p i))) x26 x27 m).
Proof.
  intros p i f x1 x21 x26 x27 me m XO HRS HT FI HS MU0 WM0 HC Ep Hi LOK. subst p. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  destruct HC as [OUT MI].
  pose proof Gc as Gc'. unfold ffW in MU0.
  apply (icodes_munch me m (ix_L X) s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
  pose proof (code_op_range (code_at s (is_lencode s) i)) as ROP. pose proof (code_val_range (code_at s (is_lencode s) i)) as RVAL.
  assert (Re : 0 <= Z.land (code_op (code_at s (is_lencode s) i)) 15 <= 15).
  { pose proof (land_ones_range (code_op (code_at s (is_lencode s) i)) 4 ltac:(lia)) as HH. change (2^4 - 1) with 15 in HH. change (2^4) with 16 in HH. lia. }
  set (e := Z.land (code_op (code_at s (is_lencode s) i)) 15) in *. pose proof (ones_range15 e Re) as ROe.
  set (val := code_val (code_at s (is_lencode s) i)) in *.
  unfold ff_lenres. unfold ff_lenok in LOK. cbv zeta in LOK. fold e in LOK |- *. fold val in LOK |- *.
  cbn [f_bits f_in f_len f_hold fset_len] in LOK.
  apply andb_prop in LOK. destruct LOK as [LP LOK].
  unfold FFL, ff_sp, PC_FF_LEN.
  pose proof (code_rd_val m (ix_L X) s (is_lencode s) i (wa (cp_addr (ix_L X) (is_lencode s) + 4 * i + 2)) MI Gc' CPL Hi eq_refl) as RD.
  zs. rewrite (zx16_small (code_val (code_at s (is_lencode s) i))) by exact RVAL. clear RD. fold val.
  zs. change (Z.land (code_op (code_at s (is_lencode s) i)) 15) with e.
  zs. br_cases K0.
  -
    replace (e =? 0) with true in LOK |- * by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in LOK |- *.
    eapply evt_eq; [| eapply (ff_dlook X s c r sv (fset_len f val) _ _ _ _ _ me m); fnorm; first [ eassumption | split; [exact OUT| exact MI] | lia ] ].
    unfold PC_FF_DLOOK. eapply FFL_intro2; fnorm; ffreg.
  - replace (e =? 0) with false in LP, LOK |- * by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in LP, LOK |- *.
    pose proof (Z.mod_pos_bound (f_hold f) (2 ^ e) ltac:(apply Z.pow_pos_nonneg; lia)) as Rmod0.
    assert (Rpe : 2 ^ e <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2 ^ 15) with 32768 in Rpe.
    zs. br_cases K1.
    +
      replace (f_bits f <? e) with false in LOK |- * by (symmetry; apply Z.ltb_ge; lia).
      fnorm. rewrite (land_wrap32_zmask (f_hold f) e) by lia. rewrite (wrap32_id (val + f_hold f mod 2 ^ e)) by lia.
      fnorm in LOK. rewrite (land_wrap32_zmask (f_hold f) e) in LOK by lia. rewrite (wrap32_id (val + f_hold f mod 2 ^ e)) in LOK by lia.
      match goal with |- context [ff_dlres s c r ?F] => set (f2 := F) in * end.
      assert (FI2 : FINV X s c f2) by (eapply (finv_drop X s c f _ e FI); [lia| subst f2; reflexivity ..]).
      do 3 zs. rewrite clang_mask32 by lia. rewrite (Z.land_ones (f_hold f) e) by lia.
      zs. rewrite (land63_small e) by lia. do 2 zs.
      eapply evt_eq; [| eapply (ff_dlook X s c r sv f2 _ _ _ _ _ me m); subst f2; fnorm; first [ eassumption | split; [exact OUT| exact MI] | rewrite ?wrap32_id by lia; lia ] ].
      unfold PC_FF_DLOOK. eapply FFL_intro2; subst f2; fnorm; ffreg.
    +
      replace (f_bits f <? e) with true in LP, LOK |- * by (symmetry; apply Z.ltb_lt; lia).
      apply andb_prop in LP. destruct LP as [LP1 LP2]. bfact LP1. bfact LP2.
      destruct (finv_pull X s c r (fset_len f val) ltac:(exact FI) HT ltac:(fnorm; lia) ltac:(fnorm; lia)) as [FIp EP]. fnorm in EP.
      rewrite EP in LOK |- *. fnorm in LOK. fnorm.
      set (b0 := arr_get (ic_input c) (f_in f)) in *.
      pose proof (proj1 (proj2 (proj1 (finv_pull X s c r (fset_len f val) ltac:(exact FI) HT ltac:(fnorm; lia) ltac:(fnorm; lia))))) as Rh1.
      rewrite EP in Rh1. fnorm in Rh1. fold b0 in Rh1.
      assert (RH64' : 0 <= b0 * 2 ^ f_bits f + f_hold f < 2 ^ 64).
      { rewrite Z.add_comm. split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Rh1)|]. apply Z.pow_le_mono_r; lia. }
      pose proof (Z.mod_pos_bound (f_hold f + b0 * 2 ^ f_bits f) (2 ^ e) ltac:(apply Z.pow_pos_nonneg; lia)) as Rmod1.
      rewrite (land_wrap32_zmask (f_hold f + b0 * 2 ^ f_bits f) e) in LOK |- * by lia.
      rewrite (wrap32_id (val + (f_hold f + b0 * 2 ^ f_bits f) mod 2 ^ e)) in LOK |- * by lia.
      match goal with |- context [ff_dlres s c r ?F] => set (f2 := F) in * end.
      assert (FI2 : FINV X s c f2).
      { eapply (finv_drop X s c _ _ e); [rewrite EP in FIp; exact FIp| fnorm; lia| subst f2; fnorm; reflexivity ..]. }
      destruct (ff_in_read X s c r sv (f_in f) me m (wa (il_NI (ix_L X) + f_in f)) XO HT HS MU0 ltac:(lia) eq_refl) as [RD RV].
      zs. cbv beta. rewrite (bv8_small _ RV). clear RD. fold b0.
      do 2 zs. rewrite (land63_small (f_bits f)) by lia. rewrite (Z.shiftl_mul_pow2 b0 (f_bits f)) by lia.
      do 2 zs.
      do 3 zs. rewrite clang_mask32 by lia. rewrite (Z.land_ones (b0 * 2 ^ f_bits f + f_hold f) e) by lia.
      zs. rewrite (land63_small e) by lia. do 2 zs.
      replace (b0 * 2 ^ f_bits f + f_hold f) with (f_hold f + b0 * 2 ^ f_bits f) by lia.
      eapply evt_eq; [| eapply (ff_dlook X s c r sv f2 _ _ _ _ _ me m); subst f2; fnorm; first [ eassumption | split; [exact OUT| exact MI] | rewrite ?wrap32_id by lia; lia ] ].
      unfold PC_FF_DLOOK. eapply FFL_intro2; subst f2; fnorm; ffreg.
Qed.

Lemma land255_op : forall v, Z.land (code_op v) 255 = code_op v.
Proof. intros v. pose proof (code_op_range v). change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Local Ltac d2_len LOK i f me m :=
  replace (Z.land (code_op (code_at s (is_lencode s) i)) 16 =? 0) with false in LOK |- * by (symmetry; apply Z.eqb_neq; lia); cbn [negb] in LOK |- *;
  eapply evt_eq; [| eapply (ff_len (is_lencode s) i f _ _ _ _ me m); first [ eassumption | reflexivity | lia ] ];
  unfold PC_FF_LEN; eapply FFL_intro2; fnorm; ffreg.
Local Ltac d2_brk LOK i f me m XO HRS HT FI HS MU0 WM0 HC Whas :=
  let HM := fresh "HM" in let PO := fresh "PO" in let ms' := fresh "ms'" in let E32 := fresh "E32" in
  replace (Z.land (code_op (code_at s (is_lencode s) i)) 64 =? 0) with false in LOK |- * by (symmetry; apply Z.eqb_neq; lia);
  pose proof (ffm_after_copy X s c sv f me m XO Whas HS MU0 WM0 HC) as HM;
  eapply evt_mono; [ eapply evt_eq; [| eapply (ff_brk1 X s c r sv f (code_at s (is_lencode s) i) _ _ _ _ _ m); first [exact XO | exact HRS | exact HT | exact FI | exact HM] ];
                     unfold PC_FF_BRK1; eapply FFL_intro2; fnorm; ffreg
                   | intros ms' PO; destruct (Z.eq_dec (Z.land (code_op (code_at s (is_lencode s) i)) 32) 0) as [E32|E32];
                     [ replace (Z.land (code_op (code_at s (is_lencode s) i)) 32 =? 0) with true in PO |- * by (symmetry; apply Z.eqb_eq; lia)
                     | replace (Z.land (code_op (code_at s (is_lencode s) i)) 32 =? 0) with false in PO |- * by (symmetry; apply Z.eqb_neq; lia) ];
                     (cbn [negb] in PO |- *; eapply tpost_of_brk; [exact PO| exact FI| exact MU0| exact WM0]) ].

Lemma ff_dolen2 : forall k p i f (x1 x21 x26 x27 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c sv me -> munch (ffW X) me m -> wmono psegs me m -> CPM X c (f_ob f) (f_out f) m ->
  p = is_lencode s -> 0 <= i < ctab_size p -> code_op (code_at s p i) <> 0 -> ff_l2ok k (code_at s p i) f = true ->
  evt psegs (TPOST X s c r sv me (ff_l2res k (code_at s p i) f))
    (FFL X s c r f PC_FF_DOLEN x1 (wz (cp_addr (ix_L X) p + 4 * i)) x21 (wz (code_op (code_at s p i))) x26 x27 m).
Proof.
  intros k; induction k as [|k IH];
    intros p i f x1 x21 x26 x27 me m XO HRS HT FI HS MU0 WM0 HC Ep Hi Hop LOK; subst p; tp_open XO HRS HT FI HS; ffx_pose HRS HT; ix_open XO;
    pose proof (code_op_range (code_at s (is_lencode s) i)) as ROP; pose proof (code_val_range (code_at s (is_lencode s) i)) as RVAL;
    unfold ff_l2res; unfold ff_l2ok in LOK; unfold FFL, ff_sp, PC_FF_DOLEN;
    (do 3 zs); rewrite ?land255_op; br_cases K16.
  1: d2_len LOK i f me m.
  2: d2_len LOK i f me m.
  all: replace (Z.land (code_op (code_at s (is_lencode s) i)) 16 =? 0) with true in LOK |- * by (symmetry; apply Z.eqb_eq; lia); cbn [negb] in LOK |- *;
      (do 2 zs); br_cases K64.
  1: d2_brk LOK i f me m XO HRS HT FI HS MU0 WM0 HC Whas.
  2: d2_brk LOK i f me m XO HRS HT FI HS MU0 WM0 HC Whas.
  all: replace (Z.land (code_op (code_at s (is_lencode s) i)) 64 =? 0) with true in LOK |- * by (symmetry; apply Z.eqb_eq; lia).
  -
    exfalso. apply andb_prop in LOK. destruct LOK as [_ LOK]. apply andb_prop in LOK. destruct LOK as [_ LOK]. cbn [dolen_ok] in LOK. discriminate LOK.
  -
    apply andb_prop in LOK. destruct LOK as [D16 LOK]. apply andb_prop in LOK. destruct LOK as [DI LOK]. bfact D16. bfact DI.
    set (op := code_op (code_at s (is_lencode s) i)) in *.
    pose proof (ones_range15 op ltac:(lia)) as ROo.
    rewrite (land_zmask (f_hold f) op) in DI, LOK |- * by lia.
    pose proof (Z.mod_pos_bound (f_hold f) (2 ^ op) ltac:(apply Z.pow_pos_nonneg; lia)) as Rmod.
    set (i2 := code_val (code_at s (is_lencode s) i) + f_hold f mod 2 ^ op) in *.
    rewrite dolen_ok_S in LOK. cbv zeta in LOK. apply andb_prop in LOK. destruct LOK as [DB LOK]. bfact DB.
    pose proof (code_bits_range (code_at s (is_lencode s) i2)) as RB2. pose proof (code_op_range (code_at s (is_lencode s) i2)) as ROP2.
    pose proof Gc as Gc'. unfold ffW in MU0.
    apply (icodes_munch me m (ix_L X) s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
    destruct HC as [OUT MI].
    pose proof (code_rd_val m (ix_L X) s (is_lencode s) i (wa (cp_addr (ix_L X) (is_lencode s) + 4 * i + 2)) MI Gc' CPL ltac:(rewrite ctab_size_len in *; lia) eq_refl) as RD.
    zs. rewrite (zx16_small (code_val (code_at s (is_lencode s) i))) by exact RVAL. clear RD.
    do 2 zs. rewrite clang_mask32 by lia. zs. rewrite (Z.land_ones (f_hold f) op) by lia.
    do 4 zs. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    pose proof (code_rd_bits m (ix_L X) s (is_lencode s) i2 (wa (cp_addr (ix_L X) (is_lencode s) + 4 * i2 + 1)) MI Gc' CPL ltac:(rewrite ctab_size_len; lia) eq_refl) as RD.
    zs. cbv beta. rewrite (bv8_small (code_bits (code_at s (is_lencode s) i2))) by exact RB2. clear RD.
    pose proof (code_rd_op m (ix_L X) s (is_lencode s) i2 (wa (cp_addr (ix_L X) (is_lencode s) + 4 * i2)) MI Gc' CPL ltac:(rewrite ctab_size_len; lia) eq_refl) as RD.
    zs. cbv beta. rewrite (bv8_small (code_op (code_at s (is_lencode s) i2))) by exact ROP2. clear RD.
    zs. rewrite (land63_small (code_bits (code_at s (is_lencode s) i2))) by lia.
    zs.
    rewrite dolen_S. cbv zeta.
    assert (FI2 : FINV X s c (fdrop f (code_bits (code_at s (is_lencode s) i2)))) by (eapply (finv_drop X s c f _ (code_bits (code_at s (is_lencode s) i2)) FI); [lia| reflexivity ..]).
    zs. br_cases Kop.
    +
      replace (code_op (code_at s (is_lencode s) i2) =? 0) with false in LOK |- * by (symmetry; apply Z.eqb_neq; lia).
      eapply evt_eq; [| eapply (IH (is_lencode s) i2 (fdrop f (code_bits (code_at s (is_lencode s) i2))) _ _ _ _ me m); fnorm;
        first [ eassumption | reflexivity | split; [exact OUT| exact MI] | rewrite ctab_size_len; lia | lia | exact LOK ] ].
      eapply FFL_intro2; fnorm; ffreg.
    +
      replace (code_op (code_at s (is_lencode s) i2) =? 0) with true in LOK |- * by (symmetry; apply Z.eqb_eq; lia). bfact LOK.
      eapply evt_eq; [| eapply (ff_lit (is_lencode s) i2 (fdrop f (code_bits (code_at s (is_lencode s) i2))) _ _ _ _ _ me m); fnorm;
        first [ eassumption | reflexivity | split; [exact OUT| exact MI] | rewrite ctab_size_len; lia | lia ] ].
      unfold PC_FF_LIT. eapply FFL_intro2; fnorm; ffreg.
Qed.

Lemma ff_head : forall f (x1 x7 x21 x25 x26 x27 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c sv me -> munch (ffW X) me m -> wmono psegs me m -> CPM X c (f_ob f) (f_out f) m ->
  trip_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) f = true ->
  evt psegs (TPOST X s c r sv me (fast_trip xx s f))
    (FFL X s c r f PC_FF_LOOP x1 x7 x21 x25 x26 x27 m).
Proof.
  intros f x1 x7 x21 x25 x26 x27 me m XO HRS HT FI HS MU0 WM0 HC TOK. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  unfold fast_trip. unfold trip_ok, pull2_ok in TOK. cbv zeta in TOK. unfold fpull2_if in TOK |- *.
  destruct HC as [OUT MI].
  pose proof Gc as Gc'. unfold ffW in MU0.
  apply (icodes_munch me m (ix_L X) s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
  assert (ELM : x_lmask xx = zmask (is_lenbits s)) by reflexivity.
  unfold FFL, ff_sp, PC_FF_LOOP.
  assert (TAIL : forall f2 (y7 y25 y26 : word), FINV X s c f2 -> f_out f2 = f_out f -> f_ob f2 = f_ob f ->
    (Z.land (f_hold f2) (x_lmask xx) <? ctab_len (is_lencode s)) &&
      dolen_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) 4
        (code_at s (is_lencode s) (Z.land (f_hold f2) (x_lmask xx))) f2 = true ->
    evt psegs (TPOST X s c r sv me (dolen 4 xx s (code_at s (is_lencode s) (Z.land (f_hold f2) (x_lmask xx))) f2))
      (FFL X s c r f2 0x1fa48 x1 y7 x21 y25 y26 x27 m)).
  { intros f2 y7 y25 y26 FI2 Eo Eob D2.
    pose proof FI2 as (Gb & Gh & Gin & Gout & Gob & Gbytes).
    assert (GH64 : 0 <= f_hold f2 < 2^64) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 Gh)|]; apply Z.pow_le_mono_r; lia).
    apply andb_prop in D2. destruct D2 as [DI D2]. bfact DI.
    unfold FFL. fnorm. rewrite ELM in DI, D2 |- *.
    set (i := Z.land (f_hold f2) (zmask (is_lenbits s))) in *.
    assert (Ri : 0 <= i) by (subst i; apply Z.land_nonneg; left; lia).
    rewrite dolen_ok_S in D2. cbv zeta in D2. apply andb_prop in D2. destruct D2 as [DB D2]. bfact DB.
    pose proof (code_bits_range (code_at s (is_lencode s) i)) as RB. pose proof (code_op_range (code_at s (is_lencode s) i)) as ROP.
    do 3 zs. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. fold i.
    pose proof (code_rd_bits m (ix_L X) s (is_lencode s) i (wa (cp_addr (ix_L X) (is_lencode s) + 4 * i + 1)) MI Gc' CPL ltac:(rewrite ctab_size_len; lia) eq_refl) as RD.
    zs. cbv beta. rewrite (bv8_small (code_bits (code_at s (is_lencode s) i))) by exact RB. clear RD.
    pose proof (code_rd_op m (ix_L X) s (is_lencode s) i (wa (cp_addr (ix_L X) (is_lencode s) + 4 * i)) MI Gc' CPL ltac:(rewrite ctab_size_len; lia) eq_refl) as RD.
    zs. cbv beta. rewrite (bv8_small (code_op (code_at s (is_lencode s) i))) by exact ROP. clear RD.
    zs. rewrite (land63_small (code_bits (code_at s (is_lencode s) i))) by lia.
    zs.
    rewrite dolen_S. cbv zeta.
    assert (FI3 : FINV X s c (fdrop f2 (code_bits (code_at s (is_lencode s) i)))) by (eapply (finv_drop X s c f2 _ (code_bits (code_at s (is_lencode s) i)) FI2); [lia| reflexivity ..]).
    zs. br_cases Kop.
    -
      replace (code_op (code_at s (is_lencode s) i) =? 0) with true in D2 |- * by (symmetry; apply Z.eqb_eq; lia). bfact D2. fnorm in D2. rewrite ?Eo in D2.
      eapply evt_eq; [| eapply (ff_lit (is_lencode s) i (fdrop f2 (code_bits (code_at s (is_lencode s) i))) _ _ _ _ _ me m); fnorm; rewrite ?Eo, ?Eob;
        first [ eassumption | reflexivity | split; [exact OUT| exact MI] | rewrite ctab_size_len; lia | lia ] ].
      unfold PC_FF_LIT. eapply FFL_intro2; fnorm; rewrite ?Eo; ffreg.
    - replace (code_op (code_at s (is_lencode s) i) =? 0) with false in D2 |- * by (symmetry; apply Z.eqb_neq; lia).
      eapply evt_eq; [| eapply (ff_dolen2 3 (is_lencode s) i (fdrop f2 (code_bits (code_at s (is_lencode s) i))) _ _ _ _ me m); fnorm; rewrite ?Eo, ?Eob;
        first [ eassumption | reflexivity | split; [exact OUT| exact MI] | rewrite ctab_size_len; lia | lia | exact D2 ] ].
      unfold PC_FF_DOLEN. eapply FFL_intro2; fnorm; rewrite ?Eo; ffreg. }
  zs. br_cases K15.
  -
    replace (f_bits f <? 15) with false in TOK |- * by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in TOK.
    apply (TAIL f); [exact FI | reflexivity | reflexivity | exact TOK].
  - replace (f_bits f <? 15) with true in TOK |- * by (symmetry; apply Z.ltb_lt; lia).
    apply andb_prop in TOK. destruct TOK as [DP TOK]. bfact DP.
    destruct (finv_pull2 X s c r f FI HT ltac:(lia) ltac:(lia)) as [FI2 EP]. rewrite EP in FI2, TOK |- *.
    match goal with |- context [dolen 4 xx s _ ?F] => set (f2 := F) in * end.
    destruct (ff_in_read X s c r sv (f_in f + 1) me m (wa (il_NI (ix_L X) + f_in f + 1)) XO HT HS MU0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as [RD RV1].
    zs. cbv beta. rewrite (bv8_small _ RV1). clear RD.
    destruct (ff_in_read X s c r sv (f_in f) me m (wa (il_NI (ix_L X) + f_in f)) XO HT HS MU0 ltac:(lia) eq_refl) as [RD RV0].
    zs. cbv beta. rewrite (bv8_small _ RV0). clear RD.
    set (b0 := arr_get (ic_input c) (f_in f)) in *. set (b1 := arr_get (ic_input c) (f_in f + 1)) in *.
    do 2 zs. rewrite (land63_small (f_bits f + 8)) by lia. rewrite (Z.shiftl_mul_pow2 b1 (f_bits f + 8)) by lia.
    do 2 zs. rewrite (land63_small (f_bits f)) by lia. rewrite (Z.shiftl_mul_pow2 b0 (f_bits f)) by lia.
    do 3 zs. rewrite lor16_small by lia.
    eapply evt_eq; [| eapply (TAIL f2); subst f2; fnorm; first [exact FI2 | reflexivity | exact TOK] ].
    eapply FFL_intro2; subst f2; fnorm; ffreg.
Qed.
End LEN.
