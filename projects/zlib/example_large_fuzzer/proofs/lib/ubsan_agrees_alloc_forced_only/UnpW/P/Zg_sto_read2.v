(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_kit Z_tr_kit Z_adler32 Zg_adler32_iface Zg_defl_iface Zg_sto_model Zg_sto_ole Zg_sto_kit Zg_sto_rdo Zg_sto_used Zg_sto_fill.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk SendModel FillWinModel ZChkAdl AdlerModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored1 RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8 RefDeflStored9 RefDeflSafeS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_STO_FINAL : Z := 0x18670.
Definition Z_STO_HW2 : Z := 0x1866c.

Ltac join_x18 v pcj :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode ?Lt None (TNode ?A ?o2 (TNode (TNode (TNode TEmpty (Some _) TEmpty) ?o10 ?B) ?o6 ?C))) ?F _ ?fc None ?m ?rom) =>
      eapply (evt_cut psegs (fun ms' => ms' = MS (TNode Lt None (TNode A o2 (TNode (TNode (TNode TEmpty (Some v) TEmpty) o10 B) o6 C))) F (wz pcj) fc None m rom))
  end.

Section READ2.
Variables (L : dlay) (flush ai0 : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : sto_ctx L inp rest0 lo r me.
Hypothesis HADL : adler32_stmt.

Definition KFIN (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y12 y13 y14 y15 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
    STOINV L flush ai0 1 rest0 lo r me X m' ->
    evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 y10 (wz (ds_strstart X)) y12 y13 y14 y15 (wz flush) y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31)
                    F (wz Z_STO_FINAL) fc None m' (seg_rom psegs)).

Lemma sto_hw2 : forall (Q : machine_state -> Prop) (Y : deflate_state)
    (y1 y5 y6 y7 y9 y10 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31 : word) (m' : mem),
  STOINV L flush ai0 1 rest0 lo r me Y m' -> 0 <= ds_strstart Y < 2^32 -> 0 <= ds_high_water Y < 2^64 ->
  KFIN Q (hw_st Y) ->
  evt psegs Q (MS (stoR L r y1 y5 y6 y7 y9 y10 (wz (ds_strstart Y)) y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y27 y28 y29 y30 y31)
                  F (wz Z_STO_FIN2) fc None m' (seg_rom psegs)).
Proof using CTX inp.
  intros until m'. intros INV RSTR RHW K.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_FIN2, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. below_open BEL. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  open_DST ST. open_D GD. unfold sto_W, slow_W in MU.
  pose proof (munch_refl [(dl_As L + 5881, dl_As L + 5968)] m') as MUf. pose proof (wmono_refl psegs m') as WMf.
  zstep. zstep. zstep. rewrite (Z.mod_small (ds_strstart Y)) by lia. zs. zstep. br_cases K1.
  -
    replace (wz (ds_strstart Y)) with (wz (ds_strstart (hw_st Y))) by (destruct (hw_st_facts Y) as (E & _); rewrite E; reflexivity).
    unfold KFIN in K. eapply K.
    unfold hw_st. replace (ds_high_water Y <? ds_strstart Y) with false by (symmetry; apply Z.ltb_ge; exact K1).
    split; [split; [exact ZS|]|].
    { constructor; [exact GA| exact GB| exact GC| eexists _, _, _, _, _; exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| exact LENS| exact LAY]. }
    split; [exact DOUT|]. split; [exact RM|]. split; [eexists; unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
  - zs. name_mem mB.
    replace (wz (ds_strstart Y)) with (wz (ds_strstart (hw_st Y))) by (destruct (hw_st_facts Y) as (E & _); rewrite E; reflexivity).
    unfold KFIN in K. eapply K.
    unfold hw_st. replace (ds_high_water Y <? ds_strstart Y) with true by (symmetry; apply Z.ltb_lt; exact K1).
    tr_groups MUf WMf.
    split; [split; [first [exact ZS| eapply dzs_munch; [exact ZS| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|]|].
    { constructor; [exact GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS| exact LAY]. }
    split; [first [exact DOUT| eapply (dout_munch _ m' mB); [exact DOUT| exact RM| exact MUf| exact WMf| cbn [disjoint_from]; slia]]|].
    split; [exact RM|]. split; [eexists; unfold sto_frame; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Variables (Q : machine_state -> Prop) (X3 : deflate_state) (have : Z).
Let n := fmin have (cs_avail_in (ds_strm X3)).
Hypothesis HV3 : so_inv X3.
Hypothesis TIE : din_tie inp X3.
Hypothesis WS : ds_w_size X3 = 32768.
Hypothesis WRAP : ds_wrap X3 <> 2.
Hypothesis RAI : cs_avail_in (ds_strm X3) < 2^31.
Hypothesis RHV : 0 <= have /\ ds_strstart X3 + have <= 65536.
Hypothesis K : KFIN Q (hw_st (st_fillw X3 n)).

Lemma sto_read2 : KRD2 L flush ai0 rest0 lo r F fc me Q X3 have.
Proof using K RHV RAI WRAP WS TIE HV3 n HADL CTX inp.
  unfold KRD2. intros until m'. intros INV.
  pose proof INV as (DR & DOUT & RM & (j0 & FR) & STK & MU & WM & MI). unfold sto_frame in FR. unfold Z_STO_RD2, stoR, stoR7.
  pose proof (tc_lo _ _ _ _ _ _ CTX) as LOsp. unfold Z_STORED_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY.
  pose proof (tc_bel _ _ _ _ _ _ CTX) as BEL. pose proof BEL as BEL'. below_open BEL'. pose proof (tc_io _ _ _ _ _ _ CTX) as IO. pose proof IO as IO'. io_open IO'.
  pose proof (vi_str _ HV3) as Vstr. pose proof (vi_bs _ HV3) as Vbs. pose proof (vi_ins _ HV3) as Vins. pose proof (vi_hw _ HV3) as Vhw.
  pose proof (vi_ni _ HV3) as Vni. pose proof (vi_inlen _ HV3) as Vinl. pose proof (vi_ai _ HV3) as Vai. pose proof (vi_wrap _ HV3) as Vwr.
  pose proof (vi_ad _ HV3) as Vad. pose proof (vi_ti _ HV3) as Vti.
  destruct TIE as [TIE1 TIE2]. rewrite TIE1, arr_len_of_list in Vinl. rewrite WS in Vstr, Vins.
  open_DST ST. open_A GA. open_D GD. open_zs ZS. unfold sto_W, slow_W in MU. unfold KFIN in K.
  zstep. zs.

  zstep. join_x18 (wz n) 0x185a4.
  { br_cases K1.
    - replace (wz n) with (wz have) by (f_equal; subst n; unfold fmin; destruct (Z.ltb_spec (cs_avail_in (ds_strm X3)) have); lia). apply evt_done. reflexivity.
    - zstep. replace (wz n) with (wz (cs_avail_in (ds_strm X3))) by (f_equal; subst n; unfold fmin; destruct (Z.ltb_spec (cs_avail_in (ds_strm X3)) have); lia).
      apply evt_done. reflexivity. }
  intros ms' ->.
  assert (RN : 0 <= n <= have /\ n <= cs_avail_in (ds_strm X3)) by (subst n; apply fmin_range; lia).
  zstep. br_cases K2.
  {
    assert (En : n = 0) by lia. rewrite En, st_fillw_0 in K.
    eapply (sto_hw2 Q X3); [exact INV| lia| lia| exact K]. }

  assert (RNp : 0 < n <= cs_avail_in (ds_strm X3)) by lia.
  pose proof (st_fillw_facts X3 n RNp) as [EFS EFH].
  pose proof (sto_din _ _ _ _ _ _ CTX m' MU) as DIN.
  unfold dout in DOUT. open_win Gwin.
  remember (arr_slice (arr_of_list inp) (cs_next_in (ds_strm X3)) n) as l eqn:El.
  assert (Ll : length (zb8 l) = Z.to_nat n) by (rewrite zb8_length, El; apply arr_slice_length').
  assert (Bl : Forall (fun b => 0 <= b < 256) l).
  { rewrite El, <- TIE1. apply Forall_forall. apply (slice_input_bytes X3); [exact HV3| lia| rewrite TIE1, arr_len_of_list; lia]. }
  pose proof (din_bytes m' L inp (cs_next_in (ds_strm X3)) n DIN ltac:(lia) ltac:(lia) ltac:(lia)) as SRC. rewrite <- El in SRC.
  destruct (u8arr_split3 _ (dl_Aw L) _ (Z.to_nat (ds_strstart X3)) (Z.to_nat n) Gwin ltac:(rewrite av8_length; lia)) as (O1 & O2 & O3). clear Gwin.
  rewrite !Z2Nat.id in O2 by lia. rewrite !Z2Nat.id in O3 by lia.
  assert (LO1 : length (firstn (Z.to_nat (ds_strstart X3)) (av8 (ds_window X3) 65536)) = Z.to_nat (ds_strstart X3)) by (rewrite length_firstn, av8_length; lia).
  assert (LO3 : length (skipn (Z.to_nat (ds_strstart X3) + Z.to_nat n) (av8 (ds_window X3) 65536)) = (Z.to_nat 65536 - (Z.to_nat (ds_strstart X3) + Z.to_nat n))%nat)
    by (rewrite length_skipn, av8_length; lia).
  pose proof (outv_length rest0 (ds_strm X3) (unbox _ RM)) as OL.
  pose proof (munch_refl [(lo, bv_unsigned (r_sp r) + -160); (dl_Aw L, dl_Aw L + 65536); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] m') as MUf.
  pose proof (wmono_refl psegs m') as WMf.
  zstep. zstep. zs. zs. zstep. zstep. rewrite (Z.mod_small (ds_strstart X3)) by lia. zstep. zstep. zstep. rewrite (Z.mod_small n) by lia. zstep. zstep.
  zstep. call (memcpy_Z (dl_Aw L + ds_strstart X3) (dl_NI L + cs_next_in (ds_strm X3)) n).
  1:{ exact SRC. } 1:{ exact Ll. } 1:{ exact O2. } 1:{ zsep. } 1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  pose proof (u8arr_join3z _ (dl_Aw L) _ _ _ (ds_strstart X3) n ltac:(lia) ltac:(lia) LO1 O1 PC O3) as WIN.
  pose proof (proj1 (u8arr_of_rw_cells psegs _ _ _ _ PC)) as BY.
  unfold zb8 in WIN. rewrite El in WIN. rewrite (av8_blit' (ds_window X3) (arr_of_list inp) 65536 (ds_strstart X3) (cs_next_in (ds_strm X3)) n) in WIN by (pose proof (ln_win _ LENS); lia).
  rewrite arr_blit_upd, <- El in WIN.
  pose proof (arr_len_blit (ds_window X3) (ds_strstart X3) (arr_of_list inp) (cs_next_in (ds_strm X3)) n) as LNW.
  rewrite arr_blit_upd, <- El, (ln_win _ LENS) in LNW.
  pose proof (av8_zlength (arr_upd (ds_window X3) (ds_strstart X3) l) 65536 ltac:(lia)) as LWF.
  clear O1 O3 PC POST SRC LO1 LO3.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -160)) = bv_unsigned (r_sp r) + -160) by (apply unsigned_lit; lia).
  pose proof (ins_add_eq (ds_insert X3) n (ds_w_size X3) ltac:(lia) ltac:(lia) ltac:(lia)) as [EIA RIA].

  assert (KJ : forall (mA : mem) (adl : Z) (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
    adl = (if ds_wrap X3 =? 1 then adler32_upd (cs_adler (ds_strm X3)) l else cs_adler (ds_strm X3)) ->
    rw_cells psegs mA (dl_S L)
      [C8 (wz (dl_NI L + cs_next_in (ds_strm X3))); C4 (wz (cs_avail_in (ds_strm X3) - n)); CB 4 zp1; C8 (wz (cs_total_in (ds_strm X3)));
       C8 (wz (dl_NO L + Z.of_nat (length (cs_out_rev (ds_strm X3))))); C4 (wz (cs_avail_out (ds_strm X3))); CB 4 zp2; C8 (wz (cs_total_out (ds_strm X3)));
       C8 (wz (msg_ptr (cs_msg (ds_strm X3)))); C8 (wz (dl_As L)); C8 (wz Z_ZCALLOC); C8 (wz Z_ZCFREE); C8 (wz 0);
       C4 (wz (cs_data_type (ds_strm X3))); CB 4 zp3; C8 (wz adl); C8 zresv] ->
    rw_cells psegs mA (dl_As L) (dsA_cells L X3 hA1 hA2 hA3 hA4 hA5) ->
    rw_cells psegs mA (dl_As L + 5881) (dsD_cells L X3 hD0 hD1 hD2 hD3 hD4) ->
    u8arr psegs mA (dl_Aw L) (av8 (arr_upd (ds_window X3) (ds_strstart X3) l) 65536) ->
    u8arr psegs mA (dl_NO L) (outv rest0 (ds_strm X3)) ->
    rw_cells psegs mA (bv_unsigned (r_sp r) + -160) (sto_frame j0 flush ai0 1 r) -> stk psegs mA lo (bv_unsigned (r_sp r) + -160) ->
    munch [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Aw L, dl_Aw L + 65536);
           (dl_Ap L, dl_Ap L + 2 * 32768); (dl_Ah L, dl_Ah L + 2 * 32768); (dl_Ab L, dl_Ab L + 65536); (dl_NO L, dl_NO L + Z.of_nat (length rest0))] me mA ->
    wmono psegs me mA ->
    munch [(lo, bv_unsigned (r_sp r) + -160); (dl_Aw L, dl_Aw L + 65536); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] m' mA ->
    wmono psegs m' mA -> mem_inv psegs mA ->
    evt psegs Q
      (MS (stoR L r v1 v5 v6 v7 (wz (dl_S L)) v10 v11 v12 v13 v14 v15 v16 v17
               (wz n) (wz n) (wz (dl_Aw L + ds_strstart X3)) y21 y22 y27 v28 v29 v30 v31)
          F (wz 0x18618) fc None mA (seg_rom psegs))).
  { clear ZS GA GD WIN BY FR STK MU WM MUf WMf DOUT. try clear MI0.
    intros mA adl v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 EADL ZS GA GD WIN DOUT FR STK MU WM MUf WMf MI.
    unfold sto_frame in FR. unfold dsA_cells in GA. unfold dsD_cells in GD. unfold stoR, stoR7.
    do 12 zs.
    remember (if n <? ds_w_size X3 - ds_insert X3 then n else ds_w_size X3 - ds_insert X3) as mn eqn:Emn.
    zstep. join_x18 (wz mn) 0x18650.
    { br_cases K3.
      - replace (wz mn) with (wz n) by (f_equal; rewrite Emn; destruct (Z.ltb_spec n (ds_w_size X3 - ds_insert X3)); lia). apply evt_done. reflexivity.
      - zstep. replace (wz mn) with (wz (ds_w_size X3 - ds_insert X3)) by (f_equal; rewrite Emn; destruct (Z.ltb_spec n (ds_w_size X3 - ds_insert X3)); lia).
        apply evt_done. reflexivity. }
    intros ms' ->.
    zs. zs. name_mem mB. tr_groups MUf WMf.
    replace (wz (ds_strstart X3 + n)) with (wz (ds_strstart (st_fillw X3 n))) by (rewrite EFS; reflexivity).
    eapply (sto_hw2 Q (st_fillw X3 n)); [| rewrite EFS; lia | rewrite EFH; lia | exact K].
    rewrite (st_fillw_eq X3 X3 n eq_refl RNp). unfold st_rbw, rbw_mid. cbv zeta. rewrite TIE1, <- El.
    replace (ds_wrap X3 =? 2) with false by (symmetry; apply Z.eqb_neq; exact WRAP).
    destruct (ds_wrap X3 =? 1); subst adl.
    all: split; [split|];
    [ eexists _, _, _, _; unfold zs_call_cells, zs_priv_cells; cbn [app]; dsred; close_cells ZS
    | constructor; [eexists _, _, _, _, _; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| eexists _, _, _, _, _; unfold dsD_cells; dsred; close_cells GD
                   | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
                   | unfold dwin; dsred; exact WIN| exact Gprev| exact Ghead| exact Gpend| | exact LAY];
      destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
      constructor; dsred; [exact l1| exact l2| exact l3| exact l4| exact l5| exact l6| exact l7| exact l8| exact l9| exact LNW| exact l11| exact l12| exact l13]
    | split; [unfold dout; dsred; exact DOUT|];
      split; [constructor; dsred; exact (unbox _ RM)|];
      split; [eexists; exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| assumption] ]. }

  zstep. zs. zstep. zstep. br_cases K3; [exfalso; lia|].
  zstep. zstep. br_cases K4.
  -
    apply (KJ _ (cs_adler (ds_strm X3))); [replace (ds_wrap X3 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K4); reflexivity
      | exact ZS| exact GA| exact GD| exact WIN| exact DOUT| exact FR| exact STK| exact MU| exact WM| exact MUf| exact WMf| assumption].
  -
    zstep. zstep. zstep.
    assert (E12 : wz n = wz (Z.of_nat (length (zb8 l)))) by (rewrite zb8_length, <- (zb8_length l), Ll; f_equal; lia).
    set_x12 (wz (Z.of_nat (length (zb8 l)))) E12. clear E12.
    zstep. call (adler32_call HADL (cs_adler (ds_strm X3)) (dl_Aw L + ds_strstart X3) lo (zb8 l)).
    1:{ apply Vad. lia. } 1:{ lia. } 1:{ rewrite Ll. lia. } 1:{ rewrite Ll. lia. } 1:{ exact BY. } 1:{ assumption. }
    1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ rewrite Ll. lia. }
    rewrite ESP in *.
    replace (adler32_z_spec (cs_adler (ds_strm X3)) (dl_Aw L + ds_strstart X3) (zb8 l)) with (adler32_upd (cs_adler (ds_strm X3)) l)
      by (symmetry; apply adler32_upd_spec; [pose proof (Vad ltac:(lia)); lia | lia | exact Bl]).
    zstep. zs. name_mem mE.
    apply (KJ mE (adler32_upd (cs_adler (ds_strm X3)) l)); [rewrite K4; reflexivity
      | exact ZS| exact GA| exact GD| exact WIN| exact DOUT| exact FR| assumption| exact MU| exact WM| exact MUf| exact WMf| assumption].
Qed.
End READ2.
