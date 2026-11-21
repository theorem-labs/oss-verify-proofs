(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_pure Z_infl_a_match Zg_infl_t_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_MATCH1 RefInflateA_MATCH RefInflateSafeOK RefInflateSafeOK2 RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition from_ok (win ob : arr) (put0 n : Z) (from : fromptr) : Prop :=
  match from with
  | FWin i => 0 <= i /\ i + n <= arr_len win /\ (forall t, 0 <= t < arr_len win -> 0 <= arr_get win t < 256)
  | FOut i => 0 <= i < put0
  end.

Lemma mc_src_typed : forall win ob put0 n from k,
  from_ok win ob put0 n from -> (forall t, 0 <= t < put0 -> 0 <= arr_get ob t < 256) -> 0 <= k < n ->
  0 <= mc_src win ob put0 from k < 256.
Proof.
  intros win ob put0 n [i|i] k FOK TOB Hk; cbn [from_ok mc_src] in *.
  - apply FOK. lia.
  - apply TOB. pose proof (Z.mod_pos_bound k (put0 - i) ltac:(lia)). lia.
Qed.

Lemma mc_obn_typed : forall win ob put0 n from j t,
  from_ok win ob put0 n from -> (forall t, 0 <= t < put0 -> 0 <= arr_get ob t < 256) -> 0 <= put0 -> Z.of_nat j <= n ->
  put0 + n <= arr_len ob -> 0 <= t < put0 + Z.of_nat j -> 0 <= arr_get (mc_obn win ob put0 from j) t < 256.
Proof.
  intros win ob put0 n from j t FOK TOB Hp Hj Hn Ht.
  rewrite mc_obn_get by lia.
  destruct (Z.leb_spec put0 t); destruct (Z.ltb_spec t (put0 + Z.of_nat j)); cbn [andb]; try (apply TOB; lia).
  apply (mc_src_typed win ob put0 n from); [exact FOK| exact TOB| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_MT_L : Z := 0x214b4.       (* [comment removed for export] *)
Definition PC_MT_X : Z := 0x214e4.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mt_base (X : ictx) (from : fromptr) : Z :=
  match from with FWin i => il_Aw (ix_L X) + i | FOut i => il_NO (ix_L X) + i end.

(* [comment removed for export] *)
Definition mtw (s1 : inflate_state) (c : icall) (r : iregs) (from : fromptr) (j : nat) : iw :=
  mkW s1 (icset_outbuf c (mc_obn (is_window s1) (ic_outbuf c) (ir_put r) from j)) (irset_put r (ir_put r + Z.of_nat j)).

(* [comment removed for export] *)
Definition MTH (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h10 q = wz (-2) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r) /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r).

(* [comment removed for export] *)
Definition MTL (X : ictx) (r : iregs) (from : fromptr) (n : Z) (j : nat) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r + Z.of_nat j) /\ h11 q = wz (mt_base X from + Z.of_nat j) /\ h12 q = wz (n - Z.of_nat j)
  /\ h13 q = wz (mt_base X from + Z.of_nat j) /\ h14 q = wz (il_NO (ix_L X) + ir_put r + Z.of_nat j) /\ MTH X r q.

(* [comment removed for export] *)
Definition MTX (X : ictx) (r : iregs) (n : Z) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r + n) /\ h15 q = wz (il_NO (ix_L X) + ir_put r + n) /\ MTH X r q.
Local Ltac mt_close j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [exact GA| exact GT| exact Gl| exact Gw| exact Gc
                        | first [exact Gwin | unfold iwin; inorm; lazymatch goal with |- match ?wb with _ => _ end => destruct wb; [exact Gwin| exact I] end]
                        | unfold iarrs in *; inorm; rewrite ?arr_len_set, ?mc_obn_len; exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

(* [comment removed for export] *)
Lemma mt_loop : forall k X s1 c r from n j q ms,
  ILOOPh X (mtw s1 c r from j) PC_MT_L q ms -> MTL X r from n j q ->
  ix_ok X -> (is_window_blk s1 <> None -> ix_hasw X = true) ->
  0 <= ir_put r -> ir_put r + n <= arr_len (ic_outbuf c) -> arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> n < 2^31 ->
  from_ok (is_window s1) (ic_outbuf c) (ir_put r) n from ->
  match from with FWin _ => is_window_blk s1 <> None /\ arr_len (is_window s1) = 32768 | FOut _ => True end ->
  (forall t, 0 <= t < ir_put r -> 0 <= arr_get (ic_outbuf c) t < 256) ->
  Z.of_nat j + Z.of_nat k = n -> (0 < k)%nat ->
  evt usegs (fun ms' => exists q', ILOOPh X (mtw s1 c r from (Z.to_nat n)) PC_MT_X q' ms' /\ MTX X r n q') ms.
Proof.
  induction k as [|k IH]; intros X s1 c r from n j [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms
    HL HQ XO Pwin Rp Rpn Pout Rn31 FOK FW TOB Hjk Hk; [lia|].
  unfold mtw in HL. iarm_openh HL. unfold MTL, MTH in HQ. hred_in HQ. destruct HQ as (E9 & E11 & E12 & E13 & E14 & E10 & E18 & E22 & E24 & E25). subst x9 x11 x12 x13 x14 x10 x18 x22 x24 x25. hred.
  ired_in OUT. ired_in FRM.
  ix_open XO. unfold PC_MT_L.
  set (put0 := ir_put r) in *. set (ob := ic_outbuf c) in *. set (win := is_window s1) in *.
  set (obj := mc_obn win ob put0 from j) in *.
  pose proof (mc_obn_len win ob put0 from j) as LOBJ. fold obj in LOBJ.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c obj) (put0 + Z.of_nat j) ltac:(cbn [ic_outbuf icset_outbuf]; lia)) as LOB.
  apply (f_equal Z.of_nat) in LOB.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (mc_src_typed win ob put0 n from (Z.of_nat j) FOK TOB ltac:(lia)) as RV.
  set (v := mc_src win ob put0 from (Z.of_nat j)) in *.
  open_IST ST.
  pose proof (munch_refl [(il_NO (ix_L X), il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X)))] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  (* [comment removed for export] *)
  destruct from as [i|i]; cbn [mt_base from_ok] in FOK, FW |- *;
  [> (* [comment removed for export] *)
     let GW := fresh "GW" in
     destruct FW as [NWB LW];
     assert (GW : u8arr usegs m (il_Aw (ix_L X)) (av8 win 32768))
       by (clear - Gwin NWB; unfold iwin in Gwin; destruct (is_window_blk s1); [exact Gwin| exfalso; exact (NWB eq_refl)]);
     pose proof (xo_win _ XO (Pwin NWB)) as XWin; pose proof (xo_ow _ XO (Pwin NWB)) as XOW; pose proof (xo_sw _ XO (Pwin NWB)) as XSW;
     pose proof (av8_zlength win 32768 ltac:(lia)) as LWIN;
     do 2 zs; gF; zs; gF;
     replace (il_Aw (ix_L X) + i + Z.of_nat j) with (il_Aw (ix_L X) + (i + Z.of_nat j)) by lia;
     ld8 GW win 32768 (il_Aw (ix_L X)) (i + Z.of_nat j) ltac:(apply (proj2 (proj2 FOK)); lia);
     change (arr_get win (i + Z.of_nat j)) with v;
     replace (il_Aw (ix_L X) + (i + Z.of_nat j)) with (il_Aw (ix_L X) + i + Z.of_nat j) by lia
   | (* [comment removed for export] *)
     let MR := fresh "MR" in let RD := fresh "RD" in
     do 2 zs; gF; zs; gF;
     pose proof (mc_read win ob put0 (FOut i) j ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as MR; rewrite from_add_Out in MR; fold obj in MR; fold v in MR;
     replace (il_NO (ix_L X) + i + Z.of_nat j) with (il_NO (ix_L X) + (i + Z.of_nat j)) by lia;
     pose proof (u8arr_read usegs _ _ _ (i + Z.of_nat j) _ (wa (il_NO (ix_L X) + (i + Z.of_nat j))) OUT
                   (iout_bytes_nth (ix_rest0 X) (icset_outbuf c obj) (put0 + Z.of_nat j) (i + Z.of_nat j) ltac:(lia)) ltac:(lia) eq_refl) as RD;
     cbn [ic_outbuf icset_outbuf] in RD; rewrite MR in RD;
     zs; cbv beta; rewrite (bv8_small v) by exact RV; clear RD;
     replace (il_NO (ix_L X) + (i + Z.of_nat j)) with (il_NO (ix_L X) + i + Z.of_nat j) by lia ].
  all: do 3 zs.
  (* [comment removed for export] *)
  all: pose proof (u8arr_store_ok usegs _ _ _ (put0 + Z.of_nat j) (wa (il_NO (ix_L X) + (put0 + Z.of_nat j))) OUT ltac:(lia) eq_refl) as SOK;
       replace (il_NO (ix_L X) + (put0 + Z.of_nat j)) with (il_NO (ix_L X) + put0 + Z.of_nat j) in SOK by lia;
       zs; rewrite le1_wz_byte by exact RV;
       pose proof (u8arr_write usegs _ _ _ (put0 + Z.of_nat j) (Z_to_bv 8 v) OUT ltac:(lia)) as OUT2; clear OUT;
       replace (il_NO (ix_L X) + (put0 + Z.of_nat j)) with (il_NO (ix_L X) + put0 + Z.of_nat j) in OUT2 by lia;
       store_done;
       rewrite iout_bytes_store in OUT2 by (cbn [ic_outbuf icset_outbuf]; lia); cbn [ic_outbuf icset_outbuf] in OUT2;
       replace (put0 + Z.of_nat j + 1) with (put0 + Z.of_nat (S j)) in OUT2 by lia;
       pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (arr_set obj (put0 + Z.of_nat j) v)) (put0 + Z.of_nat (S j)) ltac:(cbn [ic_outbuf icset_outbuf]; lia)) as LOB2;
       apply (f_equal Z.of_nat) in LOB2;
       zs; zstep; br_cases K.
  all: itr_groups MUf WMf.
  1,3: (* [comment removed for export] *)
    eapply (IH X s1 c r _ n (S j));
      [ unfold mtw; cbn [mc_obn]; subst put0 ob win obj v; eapply ILOOPh_intro; ired; [ireg .. |]
      | unfold MTL, MTH; hred; cbn [mt_base]; subst put0 ob win obj v; repeat split; ireg
      | exact XO | exact Pwin | exact Rp | exact Rpn | exact Pout | exact Rn31 | exact FOK
      | cbn; first [exact I | split; assumption] | exact TOB | lia | lia ];
    mt_close j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT2 MU WM.
  all: (* [comment removed for export] *)
    assert (EJ : Z.to_nat n = S j) by lia;
    apply evt_done; eexists; unfold mtw; rewrite EJ; cbn [mc_obn]; subst put0 ob win obj v;
    (split; [eapply ILOOPh_intro; ired; [ireg .. |]| unfold MTX, MTH; hred; repeat split; ireg]);
    mt_close j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT2 MU WM.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mt_res (s : inflate_state) (c : icall) (r : iregs) (from : fromptr) (n : Z) : ares unit :=
  let s1 := iset_length s (is_length s - n) in
  let c1 := mt_c s c r from n in
  let r1 := irset_put (irset_left r (ir_left r - n)) (ir_put r + n) in
  if is_length s - n =? 0 then ARun tt (mkW (iset_mode s1 LEN) c1 r1) else ARun tt (mkW s1 c1 r1).

(* [comment removed for export] *)
Definition MTT (X : ictx) (s : inflate_state) (r : iregs) (from : fromptr) (n : Z) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h11 q = wz (mt_base X from) /\ h12 q = wz n /\ h13 q = wz (bv_swrap 32 (is_length s))
  /\ h14 q = wz (ir_left r) /\ MTH X r q.

Local Ltac mt_closeA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma mt_tail : forall X s c r from n q ms,
  ILOOPh X (mkW s c r) PC_MATCH_T q ms -> MTT X s r from n q ->
  ix_ok X -> (is_window_blk s <> None -> ix_hasw X = true) ->
  0 <= ir_put r -> 0 < n -> n <= ir_left r -> n <= is_length s -> is_length s < 2^32 ->
  ir_put r + ir_left r = arr_len (ic_outbuf c) -> arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X)) -> arr_len (ic_outbuf c) < 2^31 ->
  0 <= arr_len (ix_input X) ->
  from_ok (is_window s) (ic_outbuf c) (ir_put r) n from ->
  match from with FWin _ => is_window_blk s <> None /\ arr_len (is_window s) = 32768 | FOut _ => True end ->
  (forall t, 0 <= t < ir_put r -> 0 <= arr_get (ic_outbuf c) t < 256) -> 0 <= is_mode s < 2^31 ->
  evt usegs (IPOST X (mt_res s c r from n)) ms.
Proof.
  intros X s c r from n [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ
         XO Pwin Rp Hn0 Hnl HnL RLEN Rpl Pout Pout1 LIN0 FOK FW TOB RMODE.
  iarm_openh HL. unfold MTT, MTH in HQ. hred_in HQ. destruct HQ as (E9 & E11 & E12 & E13 & E14 & E10 & E18 & E22 & E24 & E25).
  subst x9 x11 x12 x13 x14 x10 x18 x22 x24 x25. hred.
  ix_open XO. unfold PC_MATCH_T.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  open_IST ST. open_isA GA.
  pose proof (munch_refl (ix_Wf X) m) as MUf; unfold ix_Wf in MUf; pose proof (wmono_refl usegs m) as WMf.
  (* [comment removed for export] *)
  zs. rewrite (bv_swrap32_id (ir_left r - n)) by lia. zs.
  (* [comment removed for export] *)
  zs. rewrite bv_swrap32_sub_land. set (l1 := bv_swrap 32 (is_length s - n)). pose proof (bv_swrap32_range (is_length s - n)) as Rl1. fold l1 in Rl1.
  zs. do 2 zs.
  itr_groups MUf WMf.
  set (s1 := iset_length s (is_length s - n)). set (r' := irset_left r (ir_left r - n)).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (mt_loop (Z.to_nat n) X s1 c r' from n 0);
      [ unfold mtw; cbn [mc_obn Z.of_nat]; eapply ILOOPh_intro; ired; [ireg .. |]
      | unfold MTL, MTH; hred; subst r'; cbn [Z.of_nat ir_put ir_bits ir_hold ir_have ir_next irset_left]; repeat split; ireg
      | exact XO | exact Pwin | subst r'; cbn; exact Rp | subst r'; cbn; lia | exact Pout | lia | exact FOK | exact FW | exact TOB | lia | lia ].
    subst s1 r'. apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA; subst l1; apply le4_swrap32| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin
                          | exact ARRS| exact LAY]
    | exact IN | unfold iout; inorm; rewrite Z.add_0_r, (iout_bytes_ext _ _ c) by reflexivity; exact OUT | eassumption | exact MU | exact WM ]. }
  clear FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM MUf WMf LOB MI j0 jf.
  intros ms1 ([y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31] & HL1 & HQ1).
  unfold MTX, MTH in HQ1. hred_in HQ1. destruct HQ1 as (F9 & F15 & F10 & F18 & F22 & F24 & F25). subst y9 y15 y10 y18 y22 y24 y25.
  unfold mtw in HL1. rewrite Z2Nat.id in HL1 by lia. iarm_openh HL1. subst r'. cbn [ir_put ir_bits ir_hold ir_have ir_next irset_left irset_put ir_in ir_out ir_ret ir_left] in *.
  change (icset_outbuf c (mc_obn (is_window s1) (ic_outbuf c) (ir_put r) from (Z.to_nat n))) with (mt_c s c r from n) in OUT |- *.
  pose proof (iout_bytes_length (ix_rest0 X) (mt_c s c r from n) (ir_put r + n) ltac:(lia)) as LOB.
  apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. subst s1. ired_in GA.
  lazymatch type of Gwin with iwin _ _ ?sx => assert (PwinL : is_window_blk sx <> None -> ix_hasw X = true) by exact Pwin end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => ifine mm end.
  unfold PC_MT_X. unfold mt_res. cbv zeta.
  zs. rewrite (sx32_wz_u (is_length s - n)). fold l1. do 3 zs. zstep. br_cases K.
  - apply (proj1 (land64_zero_iff l1 ltac:(lia))) in K. unfold l1 in K. apply (proj1 (bv_swrap32_zero_iff (is_length s - n) ltac:(lia))) in K.
    replace (is_length s - n =? 0) with true by (symmetry; apply Z.eqb_eq; exact K).
    do 4 zs. itr_groups MUf WMf.
    apply evt_done. cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    mt_closeA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - assert (K' : is_length s - n <> 0).
    { intros E. apply K. apply (proj2 (land64_zero_iff l1 ltac:(lia))). unfold l1. apply (proj2 (bv_swrap32_zero_iff (is_length s - n) ltac:(lia))). exact E. }
    replace (is_length s - n =? 0) with false by (symmetry; apply Z.eqb_neq; exact K').
    zs. itr_groups MUf WMf.
    apply evt_done. cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
    mt_closeA j0 jf FRM STK ZS GA GT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PATG_mt : forall X s c r s' from n,
  PATG X (mkW s c r) -> is_mode s = MATCH -> ir_out r = arr_len (ic_outbuf c) ->
  is_wrap s' = is_wrap s -> is_wbits s' = is_wbits s -> is_head s' = is_head s -> is_flags s' = is_flags s ->
  is_window_blk s' = is_window_blk s -> is_window s' = is_window s -> is_last s' = is_last s -> is_havedict s' = is_havedict s ->
  is_back s' = is_back s -> (is_mode s' = MATCH \/ is_mode s' = LEN) ->
  0 <= ir_put r -> 0 < n <= ir_left r -> ir_put r + ir_left r = arr_len (ic_outbuf c) ->
  from_ok (is_window s) (ic_outbuf c) (ir_put r) n from ->
  PATG X (mkW s' (mt_c s c r from n) (irset_put (irset_left r (ir_left r - n)) (ir_put r + n))).
Proof.
  intros X s c r s' from n HP HM HOUT Ew Ewb Ehd Efl Ewk Ewn Ela Ehv Ebk Hmd Hp Hn Hpl FOK.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & [PL PHD] & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  unfold PATG, OBYT, ISR, mt_c. ired. rewrite Ew, Ewb, Ehd, Efl, Ewk, Ewn, Ela, Ehv, mc_obn_len.
  split; [exact Pw|]. split; [exact Pwb|]. split; [exact Phd|]. split; [left; exact Pf0|].
  split; [unfold LEN, MATCH, FLAGS, HCRC in *; lia|].
  split; [exact Pwin|]. split; [exact Pin|]. split; [exact Pin1|]. split; [exact Pout|]. split; [exact Pout1|].
  split; [split; assumption|].
  split.
  { split; [intros i Hi; apply (mc_obn_typed (is_window s) (ic_outbuf c) (ir_put r) n from); try assumption; rewrite ?Z2Nat.id by lia; lia|].
    split; [exact POW|]. split; [lia|].
    split; [| exact PHW].
    unfold NOPUTb. destruct Hmd as [E|E]; rewrite E; reflexivity. }
  unfold bk_ok in *. rewrite Ebk. rewrite HM in PBK. unfold bkmax in *.
  destruct Hmd as [E|E]; rewrite E; cbn; cbn in PBK; lia.
Qed.

(* [comment removed for export] *)
Lemma mt_after : forall X s c r from n q ms,
  ILOOPh X (mkW s c r) PC_MATCH_T q ms -> MTT X s r from n q ->
  ix_ok X -> PATG X (mkW s c r) -> is_mode s = MATCH -> ir_out r = arr_len (ic_outbuf c) ->
  0 <= ir_put r -> 0 < n <= ir_left r -> n <= is_length s -> is_length s < 2^32 -> ir_put r + ir_left r = arr_len (ic_outbuf c) ->
  from_ok (is_window s) (ic_outbuf c) (ir_put r) n from ->
  match from with FWin _ => is_window_blk s <> None /\ arr_len (is_window s) = 32768 | FOut _ => True end ->
  evt usegs (fun ms' => IPOST X (mt_res s c r from n) ms' /\ PATG X (wof (mt_res s c r from n))) ms.
Proof.
  intros X s c r from n q ms HL HQ XO HP HM HOUT Rp Hn HnL RLEN Rpl FOK FW.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  assert (RMODE : 0 <= is_mode s < 2^31) by (rewrite HM; unfold MATCH; lia).
  pose proof (xo_ni _ XO) as (_ & LIN0 & _).
  eapply evt_mono.
  { exact (mt_tail X s c r from n q ms HL HQ XO Pwin Rp ltac:(lia) ltac:(lia) HnL RLEN Rpl Pout ltac:(rewrite Pout; exact Pout1) LIN0 FOK FW POB RMODE). }
  cbv beta. intros ms' H'. split; [exact H'|].
  unfold mt_res. destruct (is_length s - n =? 0); cbn [wof];
    (eapply PATG_mt; [exact HP| exact HM| exact HOUT| reflexivity ..| | exact Rp| exact Hn| exact Rpl| exact FOK]); [right; reflexivity| left; exact HM].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lminw (s : inflate_state) (x : Z) : Z := if is_length s <? x then is_length s else x.

(* [comment removed for export] *)
Lemma sx32u_lt_small' : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^31 -> (Z.land (bv_swrap 32 x) 18446744073709551615 < y <-> x < y).
Proof. intros x y Hx Hy. rewrite land_swrap32 by exact Hx. destruct (Z.ltb_spec x 2147483648); lia. Qed.

Local Ltac fin_cut HMEM :=
  apply evt_done; eexists; split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|];
  unfold MTT, MTH; hred; cbn [mt_base mt_clamp]; repeat split; ireg.

Lemma mt_win_fin : forall X s c r cwx idx q ms,
  ILOOPh X (mkW s c r) PC_MATCH_J q ms -> h11 q = wz (il_Aw (ix_L X) + idx) -> h12 q = wz cwx -> h13 q = wz (il_Aw (ix_L X)) ->
  h9 q = wz (il_NO (ix_L X) + ir_put r) -> MTH X r q ->
  ix_ok X -> is_window_blk s <> None -> ix_hasw X = true ->
  0 < cwx <= 32768 -> 0 <= idx <= 32768 -> 0 <= is_length s < 2^32 -> 0 < ir_left r < 2^31 ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) -> 0 <= arr_len (ix_input X) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW s c r) PC_MATCH_T q' ms' /\ MTT X s r (FWin idx) (mt_clamp r (lminw s cwx)) q') ms.
Proof.
  intros X s c r cwx idx [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms
         HL E11 E12 E13 E9 HQ XO NWB HASW Rcw Ridx Clen Rl RPUT LIN0.
  destruct HL as (m & -> & HMEM). unfold MTH in HQ. hred_in HQ. destruct HQ as (E10 & E18 & E22 & E24 & E25).
  cbn [h9 h11 h12 h13] in E9, E11, E12, E13. subst x9 x11 x12 x13 x10 x18 x22 x24 x25. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & _). unfold iframe_cells in FRM. cbn [w_s w_c w_r] in ST, FRM.
  ix_open XO. unfold PC_MATCH_J.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  open_IST ST. open_isA GA.
  pose proof (xo_win _ XO HASW) as XWin.
  pose proof (sx32_wz_u (is_length s)) as ESL. pose proof (bv_swrap32_range (is_length s)) as RSL. set (sl := bv_swrap 32 (is_length s)) in *.
  (* [comment removed for export] *)
  do 3 zs. gX.
  (* [comment removed for export] *)
  zs. rewrite ESL. fold sl. zstep. br_cases K5.
  - (* [comment removed for export] *)
    apply (proj1 (sx32u_lt_small (is_length s) cwx ltac:(lia) ltac:(lia))) in K5.
    replace (lminw s cwx) with cwx by (unfold lminw; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    zs. zstep. br_cases K6.
    + replace (mt_clamp r cwx) with cwx by (unfold mt_clamp; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity). fin_cut HMEM.
    + zs. replace (mt_clamp r cwx) with (ir_left r) by (unfold mt_clamp; destruct (Z.ltb_spec (ir_left r) cwx); lia). fin_cut HMEM.
  - (* [comment removed for export] *)
    assert (K5' : is_length s <= cwx).
    { destruct (Z.le_gt_cases (is_length s) cwx) as [H|H]; [exact H|]. exfalso.
      apply (proj2 (sx32u_lt_small (is_length s) cwx ltac:(lia) ltac:(lia))) in H. fold sl in H. lia. }
    assert (Esl : sl = is_length s) by (subst sl; apply bv_swrap32_id; lia).
    replace (lminw s cwx) with (is_length s) by (unfold lminw; destruct (Z.ltb_spec (is_length s) cwx); lia).
    zs. rewrite Esl at 1. zs. zstep. br_cases K6.
    + replace (mt_clamp r (is_length s)) with (is_length s) by (unfold mt_clamp; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity). fin_cut HMEM.
    + zs. replace (mt_clamp r (is_length s)) with (ir_left r) by (unfold mt_clamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia). fin_cut HMEM.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac close_memT j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].

Lemma match_core_ok : match_core_stmt.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM. cbn [w_s] in HM.
  destruct HL as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x19 & x20 & x21 & x23 & x28 & x29 & x30 & x31 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HW as (HCORE & HREGS & HMF & HWF & HWB). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & (POB & POW & POL & PNP & PHW) & PBK). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & _ & Hlen1 & Hoff).
  rewrite HM in HWF. unfold WF in HWF. cbn in HWF.
  destruct (match_win_facts s HCORE Pwb) as (Hws & Hwh & Hwn & _).
  assert (HWIN : 1 <= is_whave s -> is_wsize s = 32768 /\ is_window_blk s <> None /\ arr_len (is_window s) = 32768).
  { intros H1. destruct HCORE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & _).
    assert (NE : is_wsize s <> 0) by (intros E; destruct (C6 E); lia).
    pose proof (C3 NE) as EWS. rewrite Pwb in EWS. change (shl32 1 15) with 32768 in EWS.
    split; [exact EWS|]. split; [intros EN; exact (NE (C1 EN))|].
    destruct (C2 ltac:(intros EN; exact (NE (C1 EN)))) as [LW _]. rewrite Pwb in LW. exact LW. }
  assert (Csane : is_sane s = 1) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
  assert (Clen : 0 <= is_length s < 2^32) by (destruct HCORE as (_&_&_&_&_&_&_&_&_&_&_&_&_&H); exact H).
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (RMODE : 0 <= is_mode s < 2^31) by (rewrite HM; unfold MATCH; lia).
  assert (HAV : ir_left r < 2^31 /\ ir_put r < 2^31) by (rewrite Pout in Rpl; lia).
  assert (EOL : ir_out r - ir_left r = ir_put r) by lia.
  pose proof (xo_ni _ XO) as (_ & LIN0 & _).
  apply (id : _ -> hide _) in HWIN.
  clear RH HCORE HWB Pfl.
  pose proof HMEM as ((j0 & jf & FRM) & STK & [ZS ST] & IN & OUT & MI & MU & WM).
  unfold iframe_cells in FRM; unfold iin in IN; unfold iout in OUT; unfold ix_W in MU; cbn [w_s w_c w_r] in *.
  ix_open XO. unfold PC_MATCH.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_izs ZS. ifineS m.
  rewrite (arm_MATCH_eq s c r Csane).
  zs. zstep. br_cases K.
  { (* [comment removed for export] *)
    assert (Kl : ir_left r = 0) by lia.
    replace (ir_left r =? 0) with true by (symmetry; apply Z.eqb_eq; exact Kl).
    do 3 zs.
    itr_groups MUf WMf.
    apply evt_done. split; [|exact HP].
    cbn [IPOST]. eapply ILEAVE_intro; ired; [ireg .. |].
    apply IMEML_intro; inorm;
    [ exists (wz (ir_ret r)), j0, jf; unfold iframe_cells; rewrite Kl; exact FRM | exact STK
    | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
    | constructor; [exact GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | exact OUT | eassumption | exact MU | exact WM ]. }
  replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold mt_plan. rewrite EOL. rewrite (wrap32_id (ir_put r)) by lia.
  pose proof (sx32_wz_u (is_length s)) as ESL. pose proof (bv_swrap32_range (is_length s)) as RSL. set (sl := bv_swrap 32 (is_length s)) in *.
  do 4 zs. rewrite EOL, Z.add_0_r. zstep. br_cases K2.
  - (* [comment removed for export] *)
    apply (proj1 (sx32u_le_small (is_offset s) (ir_put r) ltac:(lia) ltac:(lia))) in K2.
    replace (ir_put r <? is_offset s) with false by (symmetry; apply Z.ltb_ge; lia). cbv beta iota zeta.
    set (n := mt_clamp r (is_length s)) in *.
    assert (RN : 0 < n <= ir_left r /\ n <= is_length s) by (subst n; unfold mt_clamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
    rewrite (match_copy_eq (is_window s) (ic_outbuf c) (ir_put r) (FOut (ir_put r - is_offset s)) n) by (cbn; lia). cbv beta iota zeta.
    rewrite !wrap32_id by lia.
    eapply (evt_mono usegs (fun ms' => IPOST X (mt_res s c r (FOut (ir_put r - is_offset s)) n) ms' /\ PATG X (wof (mt_res s c r (FOut (ir_put r - is_offset s)) n))));
      [| intros ms' H'; exact H'].
    eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW s c r) PC_MATCH_T q ms1 /\ MTT X s r (FOut (ir_put r - is_offset s)) n q)).
    2:{ intros ms1 (q & HJ & HQ).
        exact (mt_after X s c r _ n q ms1 HJ HQ XO HP HM HWF Rp (proj1 RN) (proj2 RN) (proj2 Clen) Rpl ltac:(cbn; lia) I). }
    (* [comment removed for export] *)
    gF. do 4 zs. gXsub.
    (* [comment removed for export] *)
    zs. rewrite ESL. fold sl. do 4 zs. zstep. br_cases K5.
    + apply (proj1 (sx32u_lt_small' (is_length s) (ir_left r) ltac:(lia) ltac:(lia))) in K5.
      assert (En : n = is_length s) by (subst n; unfold mt_clamp; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
      assert (Esl : sl = is_length s) by (subst sl; apply bv_swrap32_id; lia).
      rewrite En. rewrite Esl at 1. fin_cut HMEM.
    + assert (K5' : ir_left r <= is_length s).
      { destruct (Z.le_gt_cases (ir_left r) (is_length s)) as [H|H]; [exact H|]. exfalso.
        apply (proj2 (sx32u_lt_small' (is_length s) (ir_left r) ltac:(lia) ltac:(lia))) in H. fold sl in H. lia. }
      assert (En : n = ir_left r) by (subst n; unfold mt_clamp; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
      zs. rewrite En. fin_cut HMEM.
  - (* [comment removed for export] *)
    assert (K2' : ir_put r < is_offset s).
    { destruct (Z.le_gt_cases (is_offset s) (ir_put r)) as [H|H]; [| exact H]. exfalso.
      apply (proj2 (sx32u_le_small (is_offset s) (ir_put r) ltac:(lia) ltac:(lia))) in H. lia. }
    replace (ir_put r <? is_offset s) with true by (symmetry; apply Z.ltb_lt; lia).
    set (cw := is_offset s - ir_put r) in *.
    rewrite (wrap32_id cw) by lia.
    do 2 zs. fold cw. zstep. br_cases K3.
    2:{ (* [comment removed for export] *)
        assert (Kf : is_whave s < cw).
        { destruct (Z.le_gt_cases cw (is_whave s)) as [H|H]; [| exact H]. exfalso.
          apply (proj2 (sx32u_le_small cw (is_whave s) ltac:(lia) ltac:(lia))) in H. lia. }
        replace (is_whave s <? cw) with true by (symmetry; apply Z.ltb_lt; exact Kf). cbv beta iota.
        open_isT GT. do 2 zs. rewrite Csane. zs. br_false.
        do 5 zs.
        itr_groups MUf WMf.
        apply evt_done. split.
        - cbn [IPOST]. eexists _, _. eapply ILOOP_intro; ired; [ireg .. |].
          close_memT j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        - cbn [wof]. eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep]. }
    (* [comment removed for export] *)
    assert (Kok : cw <= is_whave s) by (apply (proj1 (sx32u_le_small cw (is_whave s) ltac:(lia) ltac:(lia))); exact K3).
    replace (is_whave s <? cw) with false by (symmetry; apply Z.ltb_ge; exact Kok).
    unfold hide in HWIN. destruct (HWIN ltac:(lia)) as (EWS & NWB & LW).
    assert (HASW : ix_hasw X = true) by (apply Pwin; exact NWB).
    assert (FWo : match FWin 0 with FWin _ => is_window_blk s <> None /\ arr_len (is_window s) = 32768 | FOut _ => True end) by (split; assumption).
    assert (EWA : win_addr (ix_L X) (is_window_blk s) = il_Aw (ix_L X)) by (destruct (is_window_blk s); [reflexivity| contradiction]).
    rewrite EWA in GA. pose proof (xo_win _ XO HASW) as XWin.
    rewrite (bv_swrap32_id cw) by lia.
    zs. zstep. br_cases K4.
    + (* [comment removed for export] *)
      replace (is_wnext s <? cw) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
      change (if is_length s <? cw then is_length s else cw) with (lminw s cw).
      set (n := mt_clamp r (lminw s cw)) in *.
      assert (RN : 0 < n <= ir_left r /\ n <= is_length s /\ n <= cw)
        by (subst n; unfold mt_clamp, lminw; destruct (Z.ltb_spec (is_length s) cw); [destruct (Z.ltb_spec (ir_left r) (is_length s))| destruct (Z.ltb_spec (ir_left r) cw)]; lia).
      rewrite (match_copy_eq (is_window s) (ic_outbuf c) (ir_put r) (FWin (is_wnext s - cw)) n) by (cbn; lia). cbv beta iota zeta.
      rewrite !wrap32_id by lia.
      eapply (evt_mono usegs (fun ms' => IPOST X (mt_res s c r (FWin (is_wnext s - cw)) n) ms' /\ PATG X (wof (mt_res s c r (FWin (is_wnext s - cw)) n))));
        [| intros ms' H'; exact H'].
      (* [comment removed for export] *)
      do 5 zs. rewrite land_u32_small by lia. gF.
      eapply evt_cut.
      { eapply (mt_win_fin X s c r cw (is_wnext s - cw)); [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | hred; ireg .. | unfold MTH; hred; repeat split; ireg
          | exact XO | exact NWB | exact HASW | lia | lia | exact Clen | lia | lia | exact LIN0]. }
      intros ms1 (q & HJ & HQ).
      exact (mt_after X s c r _ n q ms1 HJ HQ XO HP HM HWF Rp (proj1 RN) (proj1 (proj2 RN)) (proj2 Clen) Rpl
               ltac:(cbn; split; [lia| split; [rewrite LW; lia| exact POW]]) FWo).
    + (* [comment removed for export] *)
      replace (is_wnext s <? cw) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      rewrite (wrap32_id (cw - is_wnext s)) by lia.
      change (if is_length s <? cw - is_wnext s then is_length s else cw - is_wnext s) with (lminw s (cw - is_wnext s)).
      set (n := mt_clamp r (lminw s (cw - is_wnext s))) in *.
      assert (RN : 0 < n <= ir_left r /\ n <= is_length s /\ n <= cw - is_wnext s)
        by (subst n; unfold mt_clamp, lminw; destruct (Z.ltb_spec (is_length s) (cw - is_wnext s)); [destruct (Z.ltb_spec (ir_left r) (is_length s))| destruct (Z.ltb_spec (ir_left r) (cw - is_wnext s))]; lia).
      rewrite (match_copy_eq (is_window s) (ic_outbuf c) (ir_put r) (FWin (is_wsize s - (cw - is_wnext s))) n) by (cbn; lia). cbv beta iota zeta.
      rewrite !wrap32_id by lia.
      eapply (evt_mono usegs (fun ms' => IPOST X (mt_res s c r (FWin (is_wsize s - (cw - is_wnext s))) n) ms'
                                       /\ PATG X (wof (mt_res s c r (FWin (is_wsize s - (cw - is_wnext s))) n))));
        [| intros ms' H'; exact H'].
      (* [comment removed for export] *)
      do 7 zs. rewrite land_u32_small by lia. gT.
      eapply evt_cut.
      { eapply (mt_win_fin X s c r (cw - is_wnext s) (is_wsize s - (cw - is_wnext s)));
          [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | hred; ireg .. | unfold MTH; hred; repeat split; ireg
          | exact XO | exact NWB | exact HASW | lia | lia | exact Clen | lia | lia | exact LIN0]. }
      intros ms1 (q & HJ & HQ).
      exact (mt_after X s c r _ n q ms1 HJ HQ XO HP HM HWF Rp (proj1 RN) (proj1 (proj2 RN)) (proj2 Clen) Rpl
               ltac:(cbn; split; [lia| split; [rewrite LW; lia| exact POW]]) FWo).
Qed.

