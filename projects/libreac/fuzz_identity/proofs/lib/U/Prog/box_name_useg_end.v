From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model box_name_lemmas.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c memcpy_c strlen_c box_name_ucall box_name_ubase.
Import ListNotations.
Open Scope Z_scope.

Section BoxName.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo f i o : Z) (display display_len : word)
          (sd : list Z).
Hypothesis SBCH : sb_ch_contract.
Hypothesis DEC : sb_dec_contract.
Hypothesis MC : memcpy_contract.
Hypothesis SL : strlen_contract.

Notation S := (bv_unsigned sp).
Notation SVC := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation ACC := (bn_accept f sd i o (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                   (bv_unsigned display) (bv_unsigned display_len)).
Notation NM := (bn_NM f sd i o).
Notation LN := (firstn 23 NM).
Notation NOV := (if 23 <? Z.of_nat (length NM) then 1 else 0).
Hypothesis HIM : bn_image m (S - BN_K) S.

Definition QQ : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S /\
    (if ACC
     then a0' = Z_to_bv 64 0 /\
          munch [(S - BN_K, S);
                 (bv_unsigned a4, bv_unsigned a4 + Z.of_nat (length NM) + 1);
                 (bv_unsigned a6, bv_unsigned a6 + Z.of_nat (length (bn_TK NM)) + 1);
                 (bv_unsigned display, bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1)] m m' /\
          bytes_at rsegs m' (bv_unsigned a4) (bn_bytes (NM ++ [0])) /\
          bytes_at rsegs m' (bv_unsigned a6) (bn_bytes (bn_TK NM ++ [0])) /\
          bytes_at rsegs m' (bv_unsigned display) (bn_bytes (bn_DP NM i o ++ [0]))
     else a0' = Z_to_bv 64 (-1) /\ munch [(S - BN_K, S)] m m').

Definition bn_res (m2 : word -> option byte) (r : Z) : Prop :=
  if ACC
  then r = 0 /\
       munch [(S - BN_K, S);
              (bv_unsigned a4, bv_unsigned a4 + Z.of_nat (length NM) + 1);
              (bv_unsigned a6, bv_unsigned a6 + Z.of_nat (length (bn_TK NM)) + 1);
              (bv_unsigned display, bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1)] m m2 /\
       bytes_at rsegs m2 (bv_unsigned a4) (bn_bytes (NM ++ [0])) /\
       bytes_at rsegs m2 (bv_unsigned a6) (bn_bytes (bn_TK NM ++ [0])) /\
       bytes_at rsegs m2 (bv_unsigned display) (bn_bytes (bn_DP NM i o ++ [0]))
  else r = -1 /\ munch [(S - BN_K, S)] m m2.

Lemma seg_epi : forall (m2 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  lo + BN_K <= S ->
  stk rsegs m2 lo (S + -104) -> rw_cells rsegs m2 (S + -104) SVC -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  bn_res m2 r ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14738) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    HLO ST2 SV2 WM2 MI2 RES.
  unfold BN_K in HLO.
  do 13 step.
  release_frame SV2 ST2 (bv_unsigned sp).
  do 2 step.
  apply evt_done. unfold QQ, bn_res in *.
  destruct ACC.
  - destruct RES as (-> & RES). do 15 eexists. exists m2. split; [reflexivity|].
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [reflexivity|exact RES].
  - destruct RES as (-> & RES). do 15 eexists. exists m2. split; [reflexivity|].
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [reflexivity|exact RES].
Qed.

Lemma seg_final : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (j0 jw jgw : list byte) (pd pt pn pw : word),
  lo + BN_K <= S ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  stk rsegs m2 lo (S + -352) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -352) [CB 8 j0; C8 display] ->
  rw_cells rsegs m2 (S + -336)
    [C8 (Z_to_bv 64 (S + -304)); C8 (Z_to_bv 64 48); C8 (Z_to_bv 64 (Z.of_nat (length (bn_DP LN i o))));
     C4 (Z_to_bv 64 0); C4 pd] ->
  bbuf m2 (S + -304) 48 (bn_DP LN i o) ->
  rw_cells rsegs m2 (S + -256)
    [C8 (Z_to_bv 64 (S + -224)); C8 (Z_to_bv 64 24); C8 (Z_to_bv 64 (Z.of_nat (length (bn_tk false LN))));
     C4 (Z_to_bv 64 0); C4 pt] ->
  bbuf m2 (S + -224) 24 (bn_tk false LN ++ [0]) ->
  rw_cells rsegs m2 (S + -200)
    [C8 (Z_to_bv 64 (S + -168)); C8 (Z_to_bv 64 24); C8 (Z_to_bv 64 (Z.of_nat (length LN)));
     C4 (Z_to_bv 64 NOV); C4 pn] ->
  bbuf m2 (S + -168) 24 (LN ++ [0]) ->
  rw_cells rsegs m2 (S + -144) [CB 24 jw; C4 (Z_to_bv 64 0); C4 pw] ->
  rw_cells rsegs m2 (S + -112) [CB 8 jgw] ->
  evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 x11 x12 x13 x14 x15 x16 x17
                        a4 a7 a5 x21 x22 x23 display_len x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x146ac) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 j0 jw jgw
    pd pt pn pw HLO AOK BUFS ST2 MU2 WM2 MI2 SV2 DS2 RD2 DP2 RT2 TK2 RN2 NM2 RW2 GW2.
  unfold BN_K in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  destruct DP2 as (rdp & Ldp & UDP). destruct TK2 as (rtk & Ltk & UTK). destruct NM2 as (rnm & Lnm & UNM).
  assert (Hlo0 : 0 <= lo) by (destruct ST2 as (Q & _); exact Q).
  destruct (args_ok_split _ _ _ _ _ _ _ _ AOK) as (_ & _ & _ & _ & _ & _ & OKI & OKO & _).
  pose proof (bn_DP_len LN i o OKI OKO) as LDP.
  assert (LLN : (length LN <= 23)%nat) by (rewrite length_firstn; lia).
  pose proof (bn_tk_len LN false) as LTK.
  step. step. step. bfalse.
  step. step. step. bfalse.
  step.
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  step.
  pose proof (u8arr_store_ok rsegs m2 (S + -304) _ (Z.of_nat (length (bn_DP LN i o))) _ UDP
                ltac:(rewrite length_app, bn_bytes_length; lia) eq_refl) as HST.
  step.
  bst UDP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  pose proof (bbuf_upd _ _ 48 _ _ _ HW Ldp ltac:(lia)) as DP3. clear HW.
  assert (ST3 : stk rsegs m3 lo (S + -104)).
  { pose proof (stk_of_rw_cells rsegs _ _ _ DS2) as K1. cbn [cells_size csize] in K1.
    pose proof (stk_of_rw_cells rsegs _ _ _ RD2) as K2. cbn [cells_size csize] in K2.
    pose proof (bbuf_stk _ _ _ _ DP3) as K3.
    pose proof (stk_of_rw_cells rsegs _ _ _ RT2) as K4. cbn [cells_size csize] in K4.
    pose proof (u8arr_stk _ _ _ UTK) as K5. rewrite length_app, bn_bytes_length, Ltk in K5.
    pose proof (stk_of_rw_cells rsegs _ _ _ RN2) as K6. cbn [cells_size csize] in K6.
    pose proof (u8arr_stk _ _ _ UNM) as K7. rewrite length_app, bn_bytes_length, Lnm in K7.
    pose proof (stk_of_rw_cells rsegs _ _ _ RW2) as K8. cbn [cells_size csize] in K8.
    pose proof (stk_of_rw_cells rsegs _ _ _ GW2) as K9. cbn [cells_size csize] in K9.
    pose proof (stk_glue _ _ _ _ _ ST2 K1 ltac:(lia) ltac:(lia)) as G.
    pose proof (stk_glue _ _ _ _ _ G K2 ltac:(lia) ltac:(lia)) as G2.
    pose proof (stk_glue _ _ _ _ _ G2 K3 ltac:(lia) ltac:(lia)) as G3.
    pose proof (stk_glue _ _ _ _ _ G3 K4 ltac:(lia) ltac:(lia)) as G4.
    pose proof (stk_glue _ _ _ _ _ G4 K5 ltac:(lia) ltac:(lia)) as G5.
    pose proof (stk_glue _ _ _ _ _ G5 K6 ltac:(lia) ltac:(lia)) as G6.
    pose proof (stk_glue _ _ _ _ _ G6 K7 ltac:(lia) ltac:(lia)) as G7.
    pose proof (stk_glue _ _ _ _ _ G7 K8 ltac:(lia) ltac:(lia)) as G8.
    pose proof (stk_glue _ _ _ _ _ G8 K9 ltac:(lia) ltac:(lia)) as G9.
    eapply stk_ext; [exact G9|lia]. }
  pose proof (acc_eq f sd i o _ _ _ _ _ _ AOK) as ACCE. unfold bn_TK in ACCE.
  assert (REF : forall (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
                        y29 y30 y31 : word),
    ACC = false ->
    evt rsegs QQ (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (-1)) y11 y12 y13 y14 y15
                          y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x14738) fc None m3 (seg_rom rsegs))).
  { intros y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 AF.
    eapply seg_epi; [unfold BN_K; lia | exact ST3 | exact SV2 | exact WM2 | exact MI2 |].
    unfold bn_res. rewrite AF. unfold BN_K. split; [reflexivity|exact MU2]. }
  step. step. bfalse.
  destruct (Z.ltb_spec 23 (Z.of_nat (length NM))) as [OV|OV].
  - replace (23 <? Z.of_nat (length NM)) with true in RN2 by (symmetry; apply Z.ltb_lt; lia).
    step. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). step. btrue.
    apply REF. rewrite ACCE. replace (Z.of_nat (length NM) <=? 23) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  - replace (23 <? Z.of_nat (length NM)) with false in RN2 by (symmetry; apply Z.ltb_ge; lia).
    assert (EL : LN = NM) by (apply firstn_all2; lia).
    rewrite EL in *.
    step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). step. bfalse.
    step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). step. bfalse.
    step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). step. bfalse.
    assert (RL : forall b : bool, b = false ->
      (Z.of_nat (length NM) <=? 23) && b = false) by (intros b ->; apply andb_false_r).
    step.
    destruct (Z.ltb_spec (Z.of_nat (length (bn_DP NM i o))) (bv_unsigned display_len)) as [CD|CD].
    2: { btrue. apply REF. rewrite ACCE.
         replace (Z.of_nat (length (bn_DP NM i o)) <? bv_unsigned display_len) with false
           by (symmetry; apply Z.ltb_ge; lia). apply andb_false_r. }
    bfalse.
    step. step.
    destruct (Z.ltb_spec (Z.of_nat (length NM)) (bv_unsigned a5)) as [CN|CN].
    2: { btrue. apply REF. rewrite ACCE.
         replace (Z.of_nat (length NM) <? bv_unsigned a5) with false by (symmetry; apply Z.ltb_ge; lia).
         rewrite andb_false_r. reflexivity. }
    bfalse.
    step. step.
    destruct (Z.ltb_spec (Z.of_nat (length (bn_tk false NM))) (bv_unsigned a7)) as [CT|CT].
    2: { btrue. apply REF. rewrite ACCE.
         replace (Z.of_nat (length (bn_tk false NM)) <? bv_unsigned a7) with false by (symmetry; apply Z.ltb_ge; lia).
         rewrite andb_false_r, andb_false_l. reflexivity. }
    bfalse.
    assert (AT : ACC = true).
    { rewrite ACCE. replace (Z.of_nat (length NM) <=? 23) with true by (symmetry; apply Z.leb_le; lia).
      replace (Z.of_nat (length NM) <? bv_unsigned a5) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z.of_nat (length (bn_tk false NM)) <? bv_unsigned a7) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z.of_nat (length (bn_DP NM i o)) <? bv_unsigned display_len) with true by (symmetry; apply Z.ltb_lt; lia).
      reflexivity. }
    clear REF ACCE.
    destruct BUFS as ((jn & RN) & (jt & RT) & (jd & RD) & DN & DT & DD). cbn [disjoint_from] in DN, DT, DD.
    pose proof (rw_cells_bound rsegs _ _ _ RN) as BN. pose proof (rw_cells_bound rsegs _ _ _ RT) as BT.
    pose proof (rw_cells_bound rsegs _ _ _ RD) as BD. cbn [cells_size csize] in BN, BT, BD.
    pose proof (bv_unsigned_in_range 64 a5) as R5. pose proof (bv_unsigned_in_range 64 a7) as R7.
    pose proof (bv_unsigned_in_range 64 display_len) as R8. unfold bv_modulus in R5, R7, R8.
    assert (M1 : Z.of_nat (length NM) + 1 <= Z.min (bv_unsigned a5) 24) by lia.
    assert (M2 : Z.of_nat (length (bn_tk false NM)) + 1 <= Z.min (bv_unsigned a7) 24) by lia.
    assert (M3 : Z.of_nat (length (bn_DP NM i o)) + 1 <= Z.min (bv_unsigned display_len) 48) by lia.
    destruct DN as (DN1 & DN2 & DN3 & _). destruct DT as (DT1 & DT2 & _). destruct DD as (DD1 & _).
    assert (FN : bv_unsigned a4 + Z.of_nat (length NM) + 1 <= S - 416 \/ S <= bv_unsigned a4)
      by (clear - DN1 M1; lia).
    assert (FT : bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1 <= S - 416 \/ S <= bv_unsigned a6)
      by (clear - DT1 M2; lia).
    assert (FD : bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1 <= S - 416 \/ S <= bv_unsigned display)
      by (clear - DD1 M3; lia).
    assert (FNT : bv_unsigned a4 + Z.of_nat (length NM) + 1 <= bv_unsigned a6 \/
                  bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1 <= bv_unsigned a4)
      by (clear - DN2 M1 M2; lia).
    assert (FND : bv_unsigned a4 + Z.of_nat (length NM) + 1 <= bv_unsigned display \/
                  bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1 <= bv_unsigned a4)
      by (clear - DN3 M1 M3; lia).
    assert (FTD : bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1 <= bv_unsigned display \/
                  bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1 <= bv_unsigned a6)
      by (clear - DT2 M2 M3; lia).
    assert (BN' : 0 <= bv_unsigned a4 /\ bv_unsigned a4 + Z.of_nat (length NM) + 1 <= 2^64) by (clear - BN M1; lia).
    assert (BT' : 0 <= bv_unsigned a6 /\ bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1 <= 2^64)
      by (clear - BT M2; lia).
    assert (BD' : 0 <= bv_unsigned display /\ bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1 <= 2^64)
      by (clear - BD M3; lia).
    apply (rw_CB_prefix _ _ _ _ (Z.to_nat (Z.of_nat (length NM) + 1))) in RN; [|clear - M1; lia].
    apply (rw_CB_prefix _ _ _ _ (Z.to_nat (Z.of_nat (length (bn_tk false NM)) + 1))) in RT; [|clear - M2; lia].
    apply (rw_CB_prefix _ _ _ _ (Z.to_nat (Z.of_nat (length (bn_DP NM i o)) + 1))) in RD; [|clear - M3; lia].
    clear DN1 DN2 DN3 DT1 DT2 DD1 BN BT BD M1 M2 M3 R5 R7 R8.
    apply (rw_cells_transport rsegs [(S - 416, S)] m m3 _ _) in RN;
      [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; clear - FN; split; [lia|exact I]].
    apply (rw_cells_transport rsegs [(S - 416, S)] m m3 _ _) in RT;
      [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; clear - FT; split; [lia|exact I]].
    apply (rw_cells_transport rsegs [(S - 416, S)] m m3 _ _) in RD;
      [| exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize]; clear - FD; split; [lia|exact I]].
    destruct DP3 as (rdp3 & Ldp3 & UDP).
    pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UNM)) as [SRCN _].
    pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UTK)) as [SRCT _].
    pose proof (proj1 (bytes_at_app rsegs _ _ _ _) (proj1 UDP)) as [SRCD _].
    step. step. step. step.
    eapply evt_cut.
    { eapply MC with (src := bn_bytes (NM ++ [0])).
      - rewrite ?unsigned_lit by lia. exact SRCN.
      - rewrite ?unsigned_lit by lia. rewrite bn_bytes_length, length_app. cbn [length]. lia.
      - rewrite ?unsigned_lit by lia. exact RN.
      - rewrite ?unsigned_lit by lia. lia.
      - exact MI2. }
    intros ms' PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4 & E & MUc &
                    WMc & MIc & DST & _).
    subst ms'. rewrite ?unsigned_lit in MUc, DST by lia.
    rewrite (ret_pc_even 0x14714) by (cbn; lia).
    destruct DST as [[_ DSTN] _]. cbn [cells_bytes cbytes] in DSTN. rewrite app_nil_r in DSTN.
    pose proof (stk_cpy _ _ _ _ _ _ (bn_bytes (NM ++ [0])) ST3 MUc
                  ltac:(rewrite bn_bytes_length, length_app; cbn [length]; lia) WMc DSTN)
      as ST4.
    replace (bv_unsigned a4 + (Z.of_nat (length NM) + 1)) with (bv_unsigned a4 + Z.of_nat (length NM) + 1) in MUc by lia.
    pose proof (munch_snoc _ _ _ _ _ _ MU2 MUc) as MU4. cbn [app] in MU4.
    pose proof (wmono_trans rsegs _ _ _ WM2 WMc) as WM4.
    clear RN SRCN ST3 MU2 WM2 MI2.
    xport m3 m4 MUc WMc.
    clear MUc WMc.
    step. step. step. step.
    eapply evt_cut.
    { eapply MC with (src := bn_bytes (bn_tk false NM ++ [0])).
      - rewrite ?unsigned_lit by lia. exact SRCT.
      - rewrite ?unsigned_lit by lia. rewrite bn_bytes_length, length_app. cbn [length]. lia.
      - rewrite ?unsigned_lit by lia. exact RT.
      - rewrite ?unsigned_lit by lia. lia.
      - exact MIc. }
    intros ms' PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m5 & E & MUc &
                    WMc & MIc2 & DST & _).
    subst ms'. rewrite ?unsigned_lit in MUc, DST by lia.
    rewrite (ret_pc_even 0x14724) by (cbn; lia).
    destruct DST as [[_ DSTT] _]. cbn [cells_bytes cbytes] in DSTT. rewrite app_nil_r in DSTT.
    pose proof (stk_cpy _ _ _ _ _ _ (bn_bytes (bn_tk false NM ++ [0])) ST4 MUc
                  ltac:(rewrite bn_bytes_length, length_app; cbn [length]; lia) WMc DSTT)
      as ST5.
    replace (bv_unsigned a6 + (Z.of_nat (length (bn_tk false NM)) + 1))
      with (bv_unsigned a6 + Z.of_nat (length (bn_tk false NM)) + 1) in MUc by lia.
    pose proof (munch_snoc _ _ _ _ _ _ MU4 MUc) as MU5. cbn [app] in MU5.
    pose proof (wmono_trans rsegs _ _ _ WM4 WMc) as WM5.
    clear RT SRCT ST4 MU4 WM4 MIc.
    xport m4 m5 MUc WMc.
    clear MUc WMc.
    step. step. step. step.
    eapply evt_cut.
    { eapply MC with (src := bn_bytes (bn_DP NM i o ++ [0])).
      - rewrite ?unsigned_lit by lia. exact SRCD.
      - rewrite ?unsigned_lit by lia. rewrite bn_bytes_length, length_app. cbn [length]. lia.
      - rewrite ?unsigned_lit by lia. exact RD.
      - rewrite ?unsigned_lit by lia. lia.
      - exact MIc2. }
    intros ms' PO.
    destruct PO as (w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6 & E & MUc &
                    WMc & MIc3 & DST & _).
    subst ms'. rewrite ?unsigned_lit in MUc, DST by lia.
    rewrite (ret_pc_even 0x14734) by (cbn; lia).
    destruct DST as [[_ DSTD] _]. cbn [cells_bytes cbytes] in DSTD. rewrite app_nil_r in DSTD.
    pose proof (stk_cpy _ _ _ _ _ _ (bn_bytes (bn_DP NM i o ++ [0])) ST5 MUc
                  ltac:(rewrite bn_bytes_length, length_app; cbn [length]; lia) WMc DSTD)
      as ST6.
    replace (bv_unsigned display + (Z.of_nat (length (bn_DP NM i o)) + 1))
      with (bv_unsigned display + Z.of_nat (length (bn_DP NM i o)) + 1) in MUc by lia.
    pose proof (munch_snoc _ _ _ _ _ _ MU5 MUc) as MU6. cbn [app] in MU6.
    pose proof (wmono_trans rsegs _ _ _ WM5 WMc) as WM6.
    clear RD SRCD ST5 MU5 WM5 MIc2.
    xport m5 m6 MUc WMc.
    clear MUc WMc.
    step.
    eapply seg_epi; [unfold BN_K; lia | exact ST6 | exact SV2 | exact WM6 | exact MIc3 |].
    unfold bn_res. rewrite AT. unfold BN_K, bn_TK. split; [reflexivity|].
    split; [exact MU6|]. split; [exact DSTN|]. split; [exact DSTT|exact DSTD].
Qed.

End BoxName.
