(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs Zg_inffast_exit Zg_inffast_copy Zg_inffast_win Zg_inffast_dist.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Zg_inffast_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem RefInffast4. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInffast17 RefInflateOkb RefInflateA_DIST1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma le4_code_val_lo : forall v, firstn 1 (skipn 2 (le4 (wz v))) = [Z_to_bv 8 (wrap8 (code_val v))].
Proof.
  intros v. unfold le4, code_val, wrap8. cbn [Z_to_le_bytes firstn skipn]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change 255 with (Z.ones 8). change 65535 with (Z.ones 16).
  rewrite !Z.land_ones by lia. rewrite ?Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac gNZ := zstep; let K := fresh "KC" in if_cases K; br_norm K;
  [exfalso; rewrite ?ff_nz_pos in K by lia; rewrite ?xor_guard1 in K by lia; lia | clear K].

Section LEN.
Variables (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave).
Local Notation L := (ix_L X).
Local Notation xx := (ffx_of s c r).
Local Ltac bfact H := first [apply Z.leb_le in H | apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.leb_gt in H].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ff_lit : forall p i f (x1 x6 x7 x9 x13 x23 x27 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  p = is_lencode s -> 0 <= i < ctab_size p -> f_out f < arr_len (ic_outbuf c) ->
  evt usegs (TPOST X s c r sv me (FCont (fset_out (fset_ob f (arr_set (f_ob f) (f_out f) (wrap8 (code_val (code_at s p i))))) (f_out f + 1))))
    (FFL X s c r f PC_FF_LIT x1 (wz (cp_addr L p + 4 * i)) x6 x7 x9 x13 x23 x27 x29 m).
Proof.
  intros p i f x1 x6 x7 x9 x13 x23 x27 x29 me m XO HRS HT FI HS MU0 WM0 HC Ep Hi Ron. subst p. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  destruct HC as [OUT MI].
  pose proof Gc as Gc'. unfold ffW in MU0.
  apply (icodes_munch me m L s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (f_ob f)) (f_out f) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  set (v := wrap8 (code_val (code_at s (is_lencode s) i))). pose proof (wrap8_range (code_val (code_at s (is_lencode s) i))) as RV. fold v in RV. change (2^8) with 256 in RV.
  unfold FFL, ff_sp, PC_FF_LIT.
  zstep. gF.
  pose proof (code_rd m L s (is_lencode s) i 2 1 (wa (cp_addr L (is_lencode s) + 4 * i + Z.of_nat 2)) MI Gc' CPL Hi ltac:(lia) eq_refl) as RD.
  rewrite le4_code_val_lo in RD. fold v in RD. change (Z.of_nat 2) with 2 in RD.
  zs. cbv beta. rewrite (bv8_small v) by lia. clear RD.
  cp_store OUT LOB (f_ob f) (f_out f) v RV.
  pose proof (obt_step (f_ob f) (f_out f) v Fbytes ltac:(lia) RV) as OBT1.
  zs.
  apply evt_done. cbn [TPOST]. do 10 eexists.
  split; [eapply FFL_intro2; fnorm; ffreg|].
  split; [eapply munch_weaken; [|exact MU0]; unfold sub_fp, ffW, ffWb; cbn [outside]; intros; lia|].
  split; [exact WM0|]. split; [assumption|].
  destruct (FFMs_transport X s c r sv me _ XO Whas HS MU0 WM0) as (FR' & GA' & GT' & ZS' & Gc'' & Gwin' & IN' & ARRS' & LAY').
  split.
  - unfold FFM, FFMg. fnorm.
    split; [exact FR'|]. split; [exact GA'|]. split; [exact GT'|]. split; [exact ZS'|]. split; [exact Gc''|]. split; [exact Gwin'|].
    split; [exact IN'|]. split; [exact OUT|]. split; [assumption|]. split; [exact ARRS'| exact LAY'].
  - unfold FINV. fnorm. rewrite arr_len_set. repeat (split; [lia|]). exact OBT1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ff_len : forall p i f (x1 x6 x7 x9 x23 x27 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  p = is_lencode s -> 0 <= i < ctab_size p -> ff_lenok (code_at s p i) f = true ->
  evt usegs (TPOST X s c r sv me (ff_lenres (code_at s p i) f))
    (FFL X s c r f PC_FF_LEN x1 (wz (cp_addr L p + 4 * i)) x6 x7 x9 (wz (code_op (code_at s p i))) x23 x27 x29 m).
Proof.
  intros p i f x1 x6 x7 x9 x23 x27 x29 me m XO HRS HT FI HS MU0 WM0 HC Ep Hi LOK. subst p. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  pose proof HC as [OUT MI].
  pose proof Gc as Gc'. unfold ffW in MU0.
  apply (icodes_munch me m L s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
  pose proof (code_op_range (code_at s (is_lencode s) i)) as ROP. pose proof (code_val_range (code_at s (is_lencode s) i)) as RVAL.
  assert (Re : 0 <= Z.land (code_op (code_at s (is_lencode s) i)) 15 <= 15).
  { pose proof (land_ones_range (code_op (code_at s (is_lencode s) i)) 4 ltac:(lia)) as HH. change (2^4 - 1) with 15 in HH. change (2^4) with 16 in HH. lia. }
  set (e := Z.land (code_op (code_at s (is_lencode s) i)) 15) in *. pose proof (ones_range15 e Re) as ROe.
  set (val := code_val (code_at s (is_lencode s) i)) in *.
  unfold ff_lenres. unfold ff_lenok in LOK. cbv zeta in LOK. fold e in LOK |- *. fold val in LOK |- *.
  cbn [f_bits f_in f_len f_hold fset_len] in LOK.
  apply andb_prop in LOK. destruct LOK as [LP LOK].
  unfold FFL, ff_sp, PC_FF_LEN.
  pose proof (code_rd_val m L s (is_lencode s) i (wa (cp_addr L (is_lencode s) + 4 * i + 2)) MI Gc' CPL Hi eq_refl) as RD.
  zs. rewrite (zx16_small (code_val (code_at s (is_lencode s) i))) by exact RVAL. clear RD. fold val.
  zs. change (Z.land (code_op (code_at s (is_lencode s) i)) 15) with e.
  zstep. br_cases K0.
  - (* [comment removed for export] *)
    replace (e =? 0) with true in LOK |- * by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in LOK |- *.
    eapply evt_eq; [| eapply (ff_dlook X s c r sv (fset_len f val) _ _ _ _ _ _ _ _ me m);
      first [ exact XO | exact HRS | exact HT | exact FI | exact HS | exact MU0 | exact WM0 | exact HC | exact LOK ] ].
    eapply FFL_intro2; fnorm; ffreg.
  - replace (e =? 0) with false in LP, LOK |- * by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in LP, LOK |- *.
    pose proof (Z.mod_pos_bound (f_hold f) (2 ^ e) ltac:(apply Z.pow_pos_nonneg; lia)) as Rmod0.
    assert (Rpe : 2 ^ e <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). change (2 ^ 15) with 32768 in Rpe.
    (* [comment removed for export] *)
    assert (TAIL : forall g (y5 y6 : word), FINV X s c g -> f_out g = f_out f -> f_ob g = f_ob f -> f_len g = val -> e <= f_bits g ->
      ff_dlok s c r (fdrop (fset_len g (wrap32 (f_len g + Z.land (wrap32 (f_hold g)) (zmask e)))) e) = true ->
      evt usegs (TPOST X s c r sv me (ff_dlres s c r (fdrop (fset_len g (wrap32 (f_len g + Z.land (wrap32 (f_hold g)) (zmask e)))) e)))
        (FFL X s c r g 0x228d8 x1 y5 y6 x7 x9 (wz e) x23 (wz val) x29 m)).
    { intros g y5 y6 FIg Eo Eob Elen Heg DOK.
      pose proof FIg as (Gb & Gh & Gin & Gout & Gob & Gbytes).
      assert (GH64 : 0 <= f_hold g < 2^64) by (split; [lia|]; eapply Z.lt_le_trans; [exact (proj2 Gh)|]; apply Z.pow_le_mono_r; lia).
      pose proof (Z.mod_pos_bound (f_hold g) (2 ^ e) ltac:(apply Z.pow_pos_nonneg; lia)) as Rmod.
      rewrite (land_wrap32_zmask (f_hold g) e) in DOK |- * by lia. rewrite Elen in DOK |- *. rewrite (wrap32_id (val + f_hold g mod 2 ^ e)) in DOK |- * by lia.
      match goal with |- context [ff_dlres s c r ?F] => set (f2 := F) in * end.
      assert (FI2 : FINV X s c f2) by (eapply (finv_drop X s c g _ e FIg); [lia| subst f2; reflexivity ..]).
      unfold FFL, ff_sp. fnorm.
      zs. do 2 zs. rewrite clang_mask32 by lia. zs. rewrite (Z.land_ones (f_hold g) e) by lia.
      zs. rewrite (land63_small e) by lia. do 2 zs.
      zstep. br_cases K14.
      + (* [comment removed for export] *)
        eapply evt_eq; [| eapply (ff_dpull X s c r sv f2 _ _ _ _ _ _ _ _ me m);
          first [ exact XO | exact HRS | exact HT | exact FI2 | exact HS | exact MU0 | exact WM0 | exact DOK
                | subst f2; fnorm; rewrite ?Eo, ?Eob; first [ exact HC | rewrite ?wrap32_id by lia; lia ] ] ].
        eapply FFL_intro2; subst f2; fnorm; ffreg.
      + (* [comment removed for export] *)
        zs.
        unfold ff_dlok, pull2_ok, fpull2_if in DOK. cbv zeta in DOK. unfold ff_dlres, fpull2_if.
        replace (f_bits f2 <? 15) with false in DOK |- * by (symmetry; apply Z.ltb_ge; subst f2; fnorm; rewrite ?wrap32_id by lia; lia). cbn [andb] in DOK.
        eapply evt_eq; [| eapply (ff_dlook2 X s c r sv f2 _ _ _ _ _ _ _ _ me m);
          first [ exact XO | exact HRS | exact HT | exact FI2 | exact HS | exact MU0 | exact WM0 | exact DOK
                | subst f2; fnorm; rewrite ?Eo, ?Eob; exact HC ] ].
        unfold PC_FF_DLOOK. eapply FFL_intro2; subst f2; fnorm; ffreg. }
    zstep. br_cases K1.
    + (* [comment removed for export] *)
      replace (f_bits f <? e) with false in LOK |- * by (symmetry; apply Z.ltb_ge; lia).
      eapply (TAIL (fset_len f val)); first [exact FI | exact LOK | reflexivity | fnorm; lia].
    + (* [comment removed for export] *)
      replace (f_bits f <? e) with true in LP, LOK |- * by (symmetry; apply Z.ltb_lt; lia).
      apply andb_prop in LP. destruct LP as [LP1 LP2]. bfact LP1. bfact LP2.
      destruct (finv_pull X s c r (fset_len f val) ltac:(exact FI) HT ltac:(fnorm; lia) ltac:(fnorm; lia)) as [FIp EP]. fnorm in EP.
      rewrite EP in LOK, FIp |- *.
      set (b0 := arr_get (ic_input c) (f_in f)) in *.
      zstep. gF.
      destruct (ff_in_read X s c r sv (f_in f) me m (wa (il_NI L + f_in f)) XO HT HS MU0 ltac:(lia) eq_refl) as [RD RV].
      zs. cbv beta. rewrite (bv8_small _ RV). clear RD. fold b0.
      zs. zs. rewrite (land63_small (f_bits f)) by lia. rewrite (Z.shiftl_mul_pow2 b0 (f_bits f)) by lia.
      do 2 zs.
      eapply evt_eq; [| eapply (TAIL (mkF (f_in f + 1) (f_out f) (f_hold f + b0 * 2 ^ f_bits f) (f_bits f + 8) val (f_dist f) (f_op f) (f_from f) (f_ob f)));
        first [exact FIp | exact LOK | reflexivity | fnorm; lia] ].
      eapply FFL_intro2; fnorm; ffreg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ff_dolen : forall k p i f (x1 x6 x7 x9 x13 x23 x27 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  p = is_lencode s -> 0 <= i < ctab_size p ->
  dolen_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) k (code_at s p i) f = true ->
  evt usegs (TPOST X s c r sv me (dolen k xx s (code_at s p i) f))
    (FFL X s c r f PC_FF_DOLEN x1 (wz (cp_addr L p + 4 * i)) x6 x7 x9 x13 x23 x27 x29 m).
Proof.
  intros k; induction k as [|k IH];
    intros p i f x1 x6 x7 x9 x13 x23 x27 x29 me m XO HRS HT FI HS MU0 WM0 HC Ep Hi LOK; subst p; [cbn [dolen_ok] in LOK; discriminate LOK|].
  tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  pose proof (code_op_range (code_at s (is_lencode s) i)) as ROP. pose proof (code_val_range (code_at s (is_lencode s) i)) as RVAL.
  pose proof (code_bits_range (code_at s (is_lencode s) i)) as RB.
  rewrite dolen_ok_S in LOK. cbv zeta in LOK. apply andb_prop in LOK. destruct LOK as [DB LOK]. bfact DB.
  rewrite dolen_S. cbv zeta.
  (* [comment removed for export] *)
  pose proof Gc as Gc'. unfold ffW in MU0.
  apply (icodes_munch me m L s (ffW X)) in Gc'; [| exact MU0 | exact WM0 | unfold ffW; cbn [disjoint_from]; slia ].
  pose proof HC as [OUT MI].
  pose proof (cp_addr_rng L (is_lencode s) i CPL Hi ltac:(lia)) as CPR.
  unfold FFL, ff_sp, PC_FF_DOLEN.
  (* [comment removed for export] *)
  pose proof (code_rd_bits m L s (is_lencode s) i (wa (cp_addr L (is_lencode s) + 4 * i + 1)) MI Gc' CPL Hi eq_refl) as RD.
  zs. cbv beta. rewrite (bv8_small (code_bits (code_at s (is_lencode s) i))) by exact RB. clear RD.
  gF.
  pose proof (code_rd_op m L s (is_lencode s) i (wa (cp_addr L (is_lencode s) + 4 * i)) MI Gc' CPL Hi eq_refl) as RD.
  zs. cbv beta. rewrite (bv8_small (code_op (code_at s (is_lencode s) i))) by exact ROP. clear RD.
  zs. rewrite (land63_small (code_bits (code_at s (is_lencode s) i))) by lia.
  zs.
  assert (FI2 : FINV X s c (fdrop f (code_bits (code_at s (is_lencode s) i)))) by (eapply (finv_drop X s c f _ (code_bits (code_at s (is_lencode s) i)) FI); [lia| reflexivity ..]).
  zstep. br_cases Kop.
  - (* [comment removed for export] *)
    replace (code_op (code_at s (is_lencode s) i) =? 0) with true in LOK |- * by (symmetry; apply Z.eqb_eq; lia). bfact LOK.
    eapply evt_eq; [| eapply (ff_lit (is_lencode s) i (fdrop f (code_bits (code_at s (is_lencode s) i))) _ _ _ _ _ _ _ _ me m);
      first [ exact XO | exact HRS | exact HT | exact FI2 | exact HS | exact MU0 | exact WM0 | reflexivity | split; [exact OUT| exact MI] | lia ] ].
    unfold PC_FF_LIT. eapply FFL_intro2; fnorm; ffreg.
  - replace (code_op (code_at s (is_lencode s) i) =? 0) with false in LOK |- * by (symmetry; apply Z.eqb_neq; lia).
    unfold ff_l2res. unfold ff_l2ok in LOK.
    zs. zstep. br_cases K16.
    + (* [comment removed for export] *)
      replace (Z.land (code_op (code_at s (is_lencode s) i)) 16 =? 0) with false in LOK |- * by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in LOK |- *.
      eapply evt_eq; [| eapply (ff_len (is_lencode s) i (fdrop f (code_bits (code_at s (is_lencode s) i))) _ _ _ _ _ _ _ me m);
        first [ exact XO | exact HRS | exact HT | exact FI2 | exact HS | exact MU0 | exact WM0 | exact LOK | reflexivity | split; [exact OUT| exact MI] | lia ] ].
      unfold PC_FF_LEN. eapply FFL_intro2; fnorm; ffreg.
    + replace (Z.land (code_op (code_at s (is_lencode s) i)) 16 =? 0) with true in LOK |- * by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in LOK |- *.
      zs. zstep. br_cases K64.
      * (* [comment removed for export] *)
        replace (Z.land (code_op (code_at s (is_lencode s) i)) 64 =? 0) with false in LOK |- * by (symmetry; apply Z.eqb_neq; lia).
        pose proof (ffm_after_copy X s c r sv (fdrop f (code_bits (code_at s (is_lencode s) i))) me m XO Whas HS MU0 WM0 ltac:(fnorm; exact HC)) as HM.
        eapply evt_mono; [ eapply evt_eq; [| eapply (ff_brk1 X s c r sv (fdrop f (code_bits (code_at s (is_lencode s) i))) (code_at s (is_lencode s) i) _ _ _ _ _ _ _ _ m);
                                              first [exact XO | exact HRS | exact HT | exact FI2 | exact HM] ];
                           unfold PC_FF_BRK1; eapply FFL_intro2; fnorm; ffreg
                         | intros ms' PO; destruct (Z.eq_dec (Z.land (code_op (code_at s (is_lencode s) i)) 32) 0) as [E32|E32];
                           [ replace (Z.land (code_op (code_at s (is_lencode s) i)) 32 =? 0) with true in PO |- * by (symmetry; apply Z.eqb_eq; lia)
                           | replace (Z.land (code_op (code_at s (is_lencode s) i)) 32 =? 0) with false in PO |- * by (symmetry; apply Z.eqb_neq; lia) ];
                           (cbn [negb] in PO |- *; eapply tpost_of_brk; [exact PO| exact FI2| exact MU0| exact WM0]) ].
      * (* [comment removed for export] *)
        replace (Z.land (code_op (code_at s (is_lencode s) i)) 64 =? 0) with true in LOK |- * by (symmetry; apply Z.eqb_eq; lia).
        apply andb_prop in LOK. destruct LOK as [D16 LOK]. apply andb_prop in LOK. destruct LOK as [DI LOK]. bfact D16. bfact DI.
        set (op := code_op (code_at s (is_lencode s) i)) in *.
        pose proof (ones_range15 op ltac:(lia)) as ROo.
        rewrite (land_zmask (Z.shiftr (f_hold f) (code_bits (code_at s (is_lencode s) i))) op) in DI, LOK |- * by lia.
        cbn [f_hold fdrop fset_bits fset_hold] in DI, LOK.
        set (h1 := Z.shiftr (f_hold f) (code_bits (code_at s (is_lencode s) i))) in *.
        assert (Rh1 : 0 <= h1 < 2^64).
        { subst h1. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (code_bits (code_at s (is_lencode s) i)) ltac:(lia) ltac:(lia)).
          split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
        pose proof (Z.mod_pos_bound h1 (2 ^ op) ltac:(apply Z.pow_pos_nonneg; lia)) as Rmod.
        set (i2 := code_val (code_at s (is_lencode s) i) + h1 mod 2 ^ op) in *.
        rewrite ctab_size_len in Hi.
        pose proof (cp_addr_rng L (is_lencode s) i2 CPL ltac:(rewrite ctab_size_len; lia) ltac:(lia)) as CPR2.
        (* [comment removed for export] *)
        pose proof (code_rd_val m L s (is_lencode s) i (wa (cp_addr L (is_lencode s) + 4 * i + 2)) MI Gc' CPL ltac:(rewrite ctab_size_len; lia) eq_refl) as RD.
        zs. rewrite (zx16_small (code_val (code_at s (is_lencode s) i))) by exact RVAL. clear RD.
        zs. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
        gCN. gF.
        (* [comment removed for export] *)
        zs. do 2 zs. rewrite clang_mask32 by lia. zs. rewrite (Z.land_ones h1 op) by lia.
        zs. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
        zs. gCN.
        zs. zs. alcp (ix_L X) (is_lencode s) XAl.
        zstep. br_true.
        eapply evt_eq; [| eapply (IH (is_lencode s) i2 (fdrop f (code_bits (code_at s (is_lencode s) i))) _ _ _ _ _ _ _ _ me m);
          first [ exact XO | exact HRS | exact HT | exact FI2 | exact HS | exact MU0 | exact WM0 | exact LOK | reflexivity | split; [exact OUT| exact MI]
                | rewrite ctab_size_len; lia ] ].
        eapply FFL_intro2; fnorm; ffreg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ff_look : forall f2 (x1 x5 x6 x7 x9 x13 x23 x27 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f2 ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f2) (f_out f2) m ->
  (Z.land (f_hold f2) (x_lmask xx) <? ctab_len (is_lencode s)) &&
    dolen_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) 4
      (code_at s (is_lencode s) (Z.land (f_hold f2) (x_lmask xx))) f2 = true ->
  evt usegs (TPOST X s c r sv me (dolen 4 xx s (code_at s (is_lencode s) (Z.land (f_hold f2) (x_lmask xx))) f2))
    (FFL X s c r f2 PC_FF_LOOK x1 x5 x6 x7 x9 x13 x23 x27 x29 m).
Proof.
  intros f2 x1 x5 x6 x7 x9 x13 x23 x27 x29 me m XO HRS HT FI HS MU0 WM0 HC D2. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  apply andb_prop in D2. destruct D2 as [DI D2]. bfact DI.
  assert (ELM : x_lmask xx = zmask (is_lenbits s)) by reflexivity. rewrite ELM in DI, D2 |- *.
  set (i := Z.land (f_hold f2) (zmask (is_lenbits s))) in *.
  assert (Ri : 0 <= i) by (subst i; apply Z.land_nonneg; left; lia).
  pose proof (cp_addr_rng L (is_lencode s) i CPL ltac:(rewrite ctab_size_len; lia) ltac:(lia)) as CPR.
  unfold FFL, ff_sp, PC_FF_LOOK. cbn [ffx_of x_lmask].
  do 2 zs. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. fold i.
  zs. gF. do 2 zs. gNZ. zs. alcp (ix_L X) (is_lencode s) XAl. gF. gF.
  eapply evt_eq; [| eapply (ff_dolen 4 (is_lencode s) i f2 _ _ _ _ _ _ _ _ me m);
    first [ exact XO | exact HRS | exact HT | exact FI | exact HS | exact MU0 | exact WM0 | exact HC | exact D2 | reflexivity | rewrite ctab_size_len; lia ] ].
  unfold PC_FF_DOLEN. eapply FFL_intro2; fnorm; ffreg.
Qed.

(* [comment removed for export] *)
Lemma ff_lpull : forall f (x1 x5 x6 x7 x9 x13 x23 x27 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  f_bits f < 15 -> trip_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) f = true ->
  evt usegs (TPOST X s c r sv me (fast_trip xx s f))
    (FFL X s c r f 0x227cc x1 x5 x6 x7 x9 x13 x23 x27 x29 m).
Proof.
  intros f x1 x5 x6 x7 x9 x13 x23 x27 x29 me m XO HRS HT FI HS MU0 WM0 HC Hb TOK. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  unfold fast_trip. unfold trip_ok, pull2_ok in TOK. cbv zeta in TOK. unfold fpull2_if in TOK |- *.
  replace (f_bits f <? 15) with true in TOK |- * by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in TOK. destruct TOK as [DP TOK]. bfact DP.
  destruct (finv_pull2 X s c r f FI HT ltac:(lia) ltac:(lia)) as [FI2 EP]. rewrite EP in FI2, TOK |- *.
  match goal with |- context [dolen 4 xx s _ ?F] => set (f2 := F) in * end.
  unfold FFL, ff_sp.
  (* [comment removed for export] *)
  zstep. gF. zstep. br_false.
  destruct (ff_in_read X s c r sv (f_in f) me m (wa (il_NI L + f_in f)) XO HT HS MU0 ltac:(lia) eq_refl) as [RD RV0].
  zs. cbv beta. rewrite (bv8_small _ RV0). clear RD.
  destruct (ff_in_read X s c r sv (f_in f + 1) me m (wa (il_NI L + f_in f + 1)) XO HT HS MU0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as [RD RV1].
  zs. cbv beta. rewrite (bv8_small _ RV1). clear RD.
  set (b0 := arr_get (ic_input c) (f_in f)) in *. set (b1 := arr_get (ic_input c) (f_in f + 1)) in *.
  do 2 zs.
  zs. rewrite (land63_small (f_bits f)) by lia. rewrite (Z.shiftl_mul_pow2 b0 (f_bits f)) by lia.
  zs. rewrite (land63_small (f_bits f + 8)) by lia. rewrite (Z.shiftl_mul_pow2 b1 (f_bits f + 8)) by lia.
  do 3 zs. rewrite lor16_small by lia.
  eapply evt_eq; [| eapply (ff_look f2 _ _ _ _ _ _ _ _ _ me m);
    first [ exact XO | exact HRS | exact HT | exact FI2 | exact HS | exact MU0 | exact WM0 | exact TOK | subst f2; fnorm; exact HC ] ].
  unfold PC_FF_LOOK. eapply FFL_intro2; subst f2; fnorm; ffreg.
Qed.

(* [comment removed for export] *)
Lemma ff_head : forall f (x1 x5 x6 x7 x13 x23 x27 x29 : word) me m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f ->
  FFMs X s c r sv me -> munch (ffW X) me m -> wmono usegs me m -> CPM X c (f_ob f) (f_out f) m ->
  trip_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) f = true ->
  evt usegs (TPOST X s c r sv me (fast_trip xx s f))
    (FFL X s c r f PC_FF_LOOP x1 x5 x6 x7 (wz 14) x13 x23 x27 x29 m).
Proof.
  intros f x1 x5 x6 x7 x13 x23 x27 x29 me m XO HRS HT FI HS MU0 WM0 HC TOK. tp_open XO HRS HT FI HS. ffx_pose HRS HT. ix_open XO.
  unfold FFL, ff_sp, PC_FF_LOOP. zstep. br_cases K15.
  - (* [comment removed for export] *)
    unfold fast_trip. unfold trip_ok, pull2_ok, fpull2_if in TOK. cbv zeta in TOK. unfold fpull2_if.
    replace (f_bits f <? 15) with false in TOK |- * by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in TOK.
    eapply evt_eq; [| eapply (ff_look f _ _ _ _ _ _ _ _ _ me m);
      first [ exact XO | exact HRS | exact HT | exact FI | exact HS | exact MU0 | exact WM0 | exact HC | exact TOK ] ].
    unfold PC_FF_LOOK. eapply FFL_intro2; fnorm; ffreg.
  - eapply evt_eq; [| eapply (ff_lpull f _ _ _ _ _ _ _ _ _ me m);
      first [ exact XO | exact HRS | exact HT | exact FI | exact HS | exact MU0 | exact WM0 | exact HC | exact TOK | lia ] ].
    eapply FFL_intro2; fnorm; ffreg.
Qed.
End LEN.
