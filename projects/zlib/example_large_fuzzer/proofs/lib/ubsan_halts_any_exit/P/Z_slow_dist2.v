(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_tr_rod Z_slow_dist1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6 LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section DIST2.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma d_code_idx : forall dd, d_code dd = arr_get dist_code_a (if dd <? 256 then dd else 256 + Z.shiftr dd 7).
Proof. intros dd. unfold d_code. destruct (dd <? 256); reflexivity. Qed.

Lemma slow_tdist2 : forall (Q : machine_state -> Prop) (S : deflate_state) (dd w12 : Z)
    (y1 y5 y6 y7 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me S m ->
  Z.land (w12 mod 18446744073709551616) 65535 = dd -> 0 <= dd < 32768 ->
  0 <= ds_strstart S <= 65536 -> 1 <= ds_lookahead S <= 65536 -> 3 <= ds_prev_length S <= 258 -> ds_prev_length S - 1 <= ds_lookahead S ->
  3 <= ds_strstart S + ds_lookahead S <= 65536 -> 0 <= ds_sym_next S < 2^18 -> 0 <= ds_sym_end S < 2^18 ->
  (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc S) i < 65536) ->
  Z_slow_dist1.KINS L flush rest0 lo r F fc me Q (dist2_st (sdist2 S (d_code dd))) (ds_strstart S + ds_lookahead S - 3) (wz (ds_sym_next S)) (wz (ds_sym_end S)) ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart S)) (wz (ds_lookahead S)) (wz w12) (wz dd) y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31)
                  F (wz 0x19ad0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) EDD Rdd Rss Rla Rpl PLLA RSL Rsn Rse Rdfc HK.
  apply box in EDD.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_D GD. open_ct Gdt.
  pose proof (ln_dtf _ LENS) as Ldtf.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 2504, dl_As L + 2748)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  zs. zstep.
  eapply (evt_cut psegs (fun ms' => ms' = _)).
  { if_cases KDD; zify_cond KDD; rewrite ?unsigned_lit in KDD by lia.
    -
      zs. zs. rewrite (unbox _ EDD).
      replace (wz dd) with (wz (if dd <? 256 then dd else 256 + Z.shiftr dd 7)) at 1 by (replace (dd <? 256) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      apply evt_done. reflexivity.
    - zs. zs. zs. zs.
      replace (Z.land ((dd ≫ 7 + 256) mod 18446744073709551616) 65535) with (if dd <? 256 then dd else 256 + Z.shiftr dd 7).
      2:{ replace (dd <? 256) with false by (symmetry; apply Z.ltb_ge; lia).
          change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
          rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. change (2^64) with 18446744073709551616. change (2^16) with 65536.
          Z.div_mod_to_equations. lia. }
      apply evt_done. reflexivity. }
  intros ms' ->.
  assert (Rdci : 0 <= (if dd <? 256 then dd else 256 + Z.shiftr dd 7) < 512).
  { destruct (Z.ltb_spec dd 256); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^7) with 128. Z.div_mod_to_equations. lia. }
  pose proof (d_code_idx dd) as EDC.
  remember (if dd <? 256 then dd else 256 + Z.shiftr dd 7) as dci eqn:Edci. clear Edci.
  assert (RLA0 : relro_clean mA) by (apply (slow_relro L inp rest0 lo r me CTX); unfold slow_W; exact MU).
  (* 1.4: _dist_code is file-static, addressed pc-relative (auipc + add): no GOT read *)
  zs. clear RLA0.
  do 4 zs.
  pose proof (rod_dist_code _ MI) as TDC. unfold Z_DIST_CODE in TDC.
  ld8ro TDC dist_code_a 512 72464 dci dc Edc ltac:(pose proof (dist_code_range dci Rdci); lia).
  clear TDC. pose proof (dist_code_range dci Rdci) as Rdc30. rewrite <- Edc in Rdc30. rewrite <- EDC in Edc.
  do 5 zs.
  replace (wz (dl_As L + 2504 + dc ≪ 2)) with (wz (dl_As L + 2504 + 4 * dc)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (u16arr_read psegs _ (dl_As L + 2504) (avct (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61) (2 * dc)
                (wz (arr_get (ds_dyn_dtree_fc S) dc)) (wa (dl_As L + 2504 + 4 * dc)) Gdt
                (avct_nth_fc _ _ 61 dc ltac:(lia)) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zs. clear RD.
  zs. zs. zs. zs.
  ct_store_fc Gdt (ds_dyn_dtree_fc S) (ds_dyn_dtree_dl S) 61 (dl_As L + 2504) dc (wrap16 (arr_get (ds_dyn_dtree_fc S) dc + 1))
    ltac:(first [apply le2_swrap16_inc | apply le2_sx16_inc]; apply Rdfc; lia).
  do 6 zs. name_mem mB.
  tr_groups MUf WMf.
  subst dc. unfold Z_slow_dist1.KINS in HK. unfold slowR in HK.
  replace (wz (ds_strstart S + ds_lookahead S + -3)) with (wz (ds_strstart S + ds_lookahead S - 3)) by (f_equal; lia).
  replace (wz (ds_strstart S + 1)) with (wz (ds_strstart (dist2_st (sdist2 S (d_code dd))) + 1)) by reflexivity.
  replace (wz (ds_prev_length S + -3)) with (wz (ds_prev_length (dist2_st (sdist2 S (d_code dd))) - 1)) by (unfold dist2_st, sdist2; dsred; f_equal; lia).
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold dist2_st, sdist2. constructor;
      [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| do 5 eexists; exact GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_ins : forall (n : nat) (Q : machine_state -> Prop) (X : deflate_state) (mi : Z) (v11 v12 : word),
  ILI X -> ds_prev_length X = Z.of_nat n -> (1 <= n)%nat -> Z.of_nat n <= 258 -> ds_strstart X + Z.of_nat n + 1 <= 65536 -> 0 <= mi -> mi + 2 < 65536 ->
  (forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
     SINV L flush rest0 lo r me (deflate_slow_insert n X mi) m' ->
     evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart (deflate_slow_insert n X mi) + 1)) v11 v12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31)
                     F (wz 0x19c6c) fc None m' (seg_rom psegs))) ->
  Z_slow_dist1.KINS L flush rest0 lo r F fc me Q X mi v11 v12.
Proof.
  induction n as [|n IH]; intros Q X mi v11 v12 HI PLn N1 N258 SSn MI0 MI2 KEXIT; [lia|].
  unfold Z_slow_dist1.KINS. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct (ILI_step X mi HI) as (HI' & ESS' & EPL').
  destruct HI as (Rss & Rih & Rhm & Rwm & Rhs & Rwb & Rhb).
  pose proof CTX as CTX0. destruct CTX0 as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.

  assert (FIN : forall (a1 a5 a6 a7 a15 a16 a17 a18 a19 a25 a28 a29 a30 a31 : word) (mm : mem),
    SINV L flush rest0 lo r me (insl_st X mi) mm ->
    evt psegs Q (MS (slowR L r a1 a5 a6 a7 (wz flush) (wz (ds_strstart X + 1 + 1)) v11 v12 (wz mi) (wz (ds_prev_length X - 1 + -1)) a15 a16 a17 a18 a19 a25 a28 a29 a30 a31)
                    F (wz 0x19b50) fc None mm (seg_rom psegs))).
  { intros until mm. intros SI'. unfold slowR. zstep.
    if_cases KX; zify_cond KX.
    -
      assert (N0 : n = 0%nat) by (rewrite PLn in KX; Z.div_mod_to_equations; lia).
      subst n. rewrite (slow_insert_last X mi PLn) in KEXIT. unfold slowR in KEXIT.
      replace (wz (ds_strstart X + 2)) with (wz (ds_strstart (insl_st X mi) + 1)) by (rewrite ESS'; f_equal; lia).
      eapply KEXIT. exact SI'.
    -
      assert (N1' : (1 <= n)%nat) by (rewrite PLn in KX; Z.div_mod_to_equations; lia).
      destruct n as [|n']; [lia|].
      rewrite (slow_insert_more n' X mi PLn) in KEXIT.
      replace (wz (ds_strstart X + 2)) with (wz (ds_strstart (insl_st X mi) + 1)) by (rewrite ESS'; f_equal; lia).
      replace (wz (ds_prev_length X - 1 + -1)) with (wz (ds_prev_length (insl_st X mi) - 1)) by (rewrite EPL'; f_equal; lia).
      eapply (IH Q (insl_st X mi) mi v11 v12 HI'); [rewrite EPL', PLn; lia| lia| lia| rewrite ESS'; lia| exact MI0| exact MI2| exact KEXIT| exact SI']. }
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUs.
  zs. zstep.
  if_cases KI; zify_cond KI; rewrite ?unsigned_lit in KI by lia.
  -
    do 3 zs. name_mem mB. clear MUf.
    tr_groups MUs WMf.
    eapply FIN.
    unfold insl_st. replace (ds_strstart X + 1 <=? mi) with false by (symmetry; apply Z.leb_gt; lia).
    split; [split|].
    + exact ZS.
    + constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    + split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUs WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
  -
    name_mem mS.
    assert (GwinS : dwin mS L X) by (apply (dwin_munch mA mS L X _ Gwin MUs WMf); cbn [disjoint_from]; slia).
    assert (GprevS : dprev mS L X) by (apply (dprev_munch mA mS L X _ Gprev MUs WMf); cbn [disjoint_from]; slia).
    assert (GheadS : dhead mS L X) by (apply (dhead_munch mA mS L X _ Ghead MUs WMf); cbn [disjoint_from]; slia).
    clear Gwin Gprev Ghead MUs. rename GwinS into Gwin. rename GprevS into Gprev. rename GheadS into Ghead.
    pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mS) as MUg. pose proof (wmono_refl psegs mS) as WMg.
    open_u16 Gprev. open_u16 Ghead.
    pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
    do 8 zs. rewrite ?Z.mod_small by lia.
    zs.
    ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 3) ltac:(apply Rwb; lia).
    zs. zs. zs. zs. zs. zs.
    rewrite (hash_mach X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3))) by lia.
    pose proof (update_hash_range X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3)) ltac:(lia)) as Rhv.
    remember (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 3))) as h eqn:Eh.
    zs. zs. rewrite (shl32_shr31 h) by lia. zs.
    pose proof (u16arr_read psegs _ (dl_Ah L) (av16 (ds_head X) 32768) h (wz (arr_get (ds_head X) h)) (wa (dl_Ah L + 2 * h)) Ghead
                  (av16_nth (ds_head X) 32768 h ltac:(lia)) ltac:(lia) eq_refl) as RD.
    zs. clear RD.
    pose proof (Rhb h ltac:(lia)) as Rhh.
    zs. zs.
    rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite (Z.mul_comm _ 2).
    pose proof (LmatchModel.land_upper_both (ds_strstart X + 1) (ds_w_mask X) ltac:(lia) ltac:(lia)) as Rpi.
    remember (Z.land (ds_strstart X + 1) (ds_w_mask X)) as pi eqn:Epi.
    zs.
    st16 Gprev (ds_prev X) 32768 (dl_Ap L) pi (arr_get (ds_head X) h) ltac:(apply le2_sx16_wz; exact Rhh).
    st16 Ghead (ds_head X) 32768 (dl_Ah L) h (wrap16 (ds_strstart X + 1)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
    do 4 zs. name_mem mB.
    tr_groups MUf WMf. tr_groups MUg WMg.
    eapply FIN.
    unfold insl_st. replace (ds_strstart X + 1 <=? mi) with true by (symmetry; apply Z.leb_le; lia).
    subst h pi. replace (ds_strstart X + 3) with (ds_strstart X + 1 + 2) in * by lia.
    split; [split|].
    + exact ZS.
    + unfold RefDeflSlow2.ins_str. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
    + split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Definition KA (Q : machine_state -> Prop) (X : deflate_state) : Prop :=
  forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me X m' ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart X)) y11 y12 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x19c80) fc None m' (seg_rom psegs)).

Lemma slow_dexit : forall (Q : machine_state -> Prop) (Xf : deflate_state) (sn se : Z)
    (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m : mem),
  SINV L flush rest0 lo r me Xf m -> 0 <= sn < 2^32 -> 0 <= se < 2^32 ->
  (sn <> se -> SK L flush rest0 lo r F fc me Q Z_SLOW_HEAD (exit_st Xf)) ->
  (sn = se -> KA Q (exit_st Xf)) ->
  evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz (ds_strstart Xf + 1)) (wz sn) (wz se) y13 y14 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x19c6c) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) Rsn Rse KH0 KA0.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 4 zs. name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : SINV L flush rest0 lo r me (exit_st Xf) mB).
  { split; [split|].
    - exact ZS.
    - unfold exit_st. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - eapply (KH0 KB). exact SI'.
  - unfold KA in KA0. replace (wz (ds_strstart Xf + 1)) with (wz (ds_strstart (exit_st Xf))) by reflexivity.
    eapply (KA0 KB). exact SI'.
Qed.

End DIST2.
