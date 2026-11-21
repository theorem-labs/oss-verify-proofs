(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit Zg_slow_frame Zg_fast_model Zg_fast_kit Zg_fast_dist2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast2 RefDeflFast3 RefDeflFast6 LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma hash_machr : forall s ih c hsh hm, ds_hash_shift s = hsh -> ds_hash_mask s = hm -> 0 <= hsh < 32 -> 0 <= hm < 2^31 ->
  Z.land (Z.lxor (bv_swrap 32 (Z.shiftl ih hsh) mod 18446744073709551616) (c mod 18446744073709551616)) hm
  = update_hash s ih c.
Proof.
  intros s ih c hsh hm <- <- H1 H2. rewrite <- (hash_mach s ih c H1 H2).
  rewrite (Z.mod_small (ds_hash_shift s) 32) by lia. reflexivity.
Qed.

Section FINS.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Definition KINSF (Q : machine_state -> Prop) (Y : deflate_state) (hsh : Z) (v10 v11 : word) : Prop :=
  forall (y1 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me Y m' ->
    evt psegs Q (MS (fastR L r y1 (wz (dl_Ah L)) (wz (ds_match_length Y - 1)) (wz (ds_ins_h Y)) v10 v11 (wz (ds_strstart Y + 1))
                           (wz 32767) (wz hsh) (wz 32767) (wz (dl_Aw L)) (wz (dl_Ap L)) y18 y19 y28 y29 y30 y31)
                    F (wz 0x191dc) fc None m' (seg_rom psegs)).

Definition KIEX (Q : machine_state -> Prop) (Yf : deflate_state) (v10 v11 : word) : Prop :=
  forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31 : word) (m' : mem),
    FINV L flush rest0 lo r me Yf m' ->
    evt psegs Q (MS (fastR L r y1 y5 y6 y7 v10 v11 (wz (ds_strstart Yf + 1)) y13 y14 y15 y16 y17 y18 y19 y28 y29 y30 y31)
                    F (wz 0x19238) fc None m' (seg_rom psegs)).

Lemma fast_insl : forall (n : nat) (Q : machine_state -> Prop) (Y : deflate_state) (hsh : Z) (v10 v11 : word),
  ILIF Y -> ds_hash_shift Y = hsh -> ds_match_length Y = Z.of_nat n -> (1 <= n)%nat -> Z.of_nat n <= 258 -> ds_strstart Y + Z.of_nat n + 2 < 65536 ->
  KIEX Q (deflate_fast_insert n Y) v10 v11 ->
  KINSF Q Y hsh v10 v11.
Proof.
  induction n as [|n IH]; intros Q Y hsh v10 v11 HI EHS MLn N1 N258 SSn KEXIT; [lia|].
  unfold KINSF. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct (ILIF_step Y HI) as (HI' & ESS' & EML').
  destruct HI as (Rss & Rih & Rhm & Rwm & Rhs & Rwb & Rhb).
  pose proof CTX as CTX0. destruct CTX0 as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.

  assert (FIN : forall (a1 a18 a19 a28 a29 a30 a31 : word) (mm : mem),
    FINV L flush rest0 lo r me (insl_st Y) mm ->
    evt psegs Q (MS (fastR L r a1 (wz (dl_Ah L)) (wz (ds_match_length Y - 1 + -1)) (wz (ds_ins_h (insl_st Y))) v10 v11 (wz (ds_strstart Y + 1 + 1))
                           (wz 32767) (wz hsh) (wz 32767) (wz (dl_Aw L)) (wz (dl_Ap L)) a18 a19 a28 a29 a30 a31)
                    F (wz 0x19234) fc None mm (seg_rom psegs))).
  { intros until mm. intros SI'. unfold fastR. zstep.
    if_cases KX; zify_cond KX.
    -
      assert (N1' : (1 <= n)%nat) by (rewrite MLn in KX; Z.div_mod_to_equations; lia).
      destruct n as [|n']; [lia|].
      rewrite (fast_insert_more n' Y MLn) in KEXIT.
      replace (wz (ds_strstart Y + 2)) with (wz (ds_strstart (insl_st Y) + 1)) by (rewrite ESS'; f_equal; lia).
      replace (wz (ds_match_length Y - 1 + -1)) with (wz (ds_match_length (insl_st Y) - 1)) by (rewrite EML'; f_equal; lia).
      unfold KINSF, fastR in IH.
      eapply (IH Q (insl_st Y) hsh v10 v11 HI'); [rewrite <- EHS; reflexivity| rewrite EML', MLn; lia| lia| lia| rewrite ESS'; lia| exact KEXIT| exact SI'].
    -
      assert (N0 : n = 0%nat) by (rewrite MLn in KX; Z.div_mod_to_equations; lia).
      subst n. rewrite (fast_insert_last Y MLn) in KEXIT. unfold KIEX, fastR in KEXIT.
      replace (wz (ds_strstart Y + 2)) with (wz (ds_strstart (insl_st Y) + 1)) by (rewrite ESS'; f_equal; lia).
      eapply KEXIT. exact SI'. }
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR. unfold fast_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUs.
  zs.
  name_mem mS.
  assert (GwinS : dwin mS L Y) by (apply (dwin_munch mA mS L Y _ Gwin MUs WMf); cbn [disjoint_from]; slia).
  assert (GprevS : dprev mS L Y) by (apply (dprev_munch mA mS L Y _ Gprev MUs WMf); cbn [disjoint_from]; slia).
  assert (GheadS : dhead mS L Y) by (apply (dhead_munch mA mS L Y _ Ghead MUs WMf); cbn [disjoint_from]; slia).
  clear Gwin Gprev Ghead MUs. rename GwinS into Gwin. rename GprevS into Gprev. rename GheadS into Ghead.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mS) as MUg. pose proof (wmono_refl psegs mS) as WMg.
  open_u16 Gprev. open_u16 Ghead.
  pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
  do 4 zs. rewrite ?Z.mod_small by lia.
  zs.
  ld8 Gwin (ds_window Y) 65536 (dl_Aw L) (ds_strstart Y + 3) ltac:(apply Rwb; lia).
  zs. zs. zs. zs. zs.
  rewrite (hash_machr Y (ds_ins_h Y) (arr_get (ds_window Y) (ds_strstart Y + 3)) hsh 32767 EHS Rhm) by lia.
  pose proof (update_hash_range Y (ds_ins_h Y) (arr_get (ds_window Y) (ds_strstart Y + 3)) ltac:(lia)) as Rhv.
  remember (update_hash Y (ds_ins_h Y) (arr_get (ds_window Y) (ds_strstart Y + 3))) as h eqn:Eh.
  zs. zs. rewrite (shl32_shr31 h) by lia. zs.
  pose proof (u16arr_read psegs _ (dl_Ah L) (av16 (ds_head Y) 32768) h (wz (arr_get (ds_head Y) h)) (wa (dl_Ah L + 2 * h)) Ghead
                (av16_nth (ds_head Y) 32768 h ltac:(lia)) ltac:(lia) eq_refl) as RD.
  zs. clear RD.
  pose proof (Rhb h ltac:(lia)) as Rhh.
  zs. zs. zs.
  rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite (Z.mul_comm _ 2).
  pose proof (LmatchModel.land_upper_both (ds_strstart Y + 1) 32767 ltac:(lia) ltac:(lia)) as Rpi.
  remember (Z.land (ds_strstart Y + 1) 32767) as pi eqn:Epi.
  st16 Gprev (ds_prev Y) 32768 (dl_Ap L) pi (arr_get (ds_head Y) h) ltac:(apply le2_sx16_wz; exact Rhh).
  st16 Ghead (ds_head Y) 32768 (dl_Ah L) h (wrap16 (ds_strstart Y + 1)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
  zs. name_mem mB.
  tr_groups MUf WMf. tr_groups MUg WMg.
  assert (EIH : ds_ins_h (insl_st Y) = h) by (rewrite Eh; unfold insl_st, ins_str; dsred; f_equal; f_equal; lia).
  unfold fastR in FIN. rewrite EIH in FIN.
  eapply FIN.
  unfold insl_st.
  subst h pi. replace (ds_strstart Y + 3) with (ds_strstart Y + 1 + 2) in * by lia. rewrite <- Rwm in *.
  split; [split|].
  - exact ZS.
  - unfold ins_str. constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma fast_ins0 : forall (Q : machine_state -> Prop) (T : deflate_state) (sn se : Z),
  ILIF T -> 0 <= ds_match_length T <= 258 -> ds_strstart T <= 65536 ->
  KINSF Q (set_match_length T (ds_match_length T - 1)) (ds_hash_shift T) (wz sn) (wz se) ->
  KDEC L flush rest0 lo r F fc me Q 0x191ac T sn se.
Proof.
  intros Q T sn se HI Rml Rss65 HK. unfold KDEC. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct HI as (Rss & Rih & Rhm & Rwm & Rhs & Rwb & Rhb).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR. unfold fast_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 9 zs. zs. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  unfold KINSF, fastR in HK.
  replace (ds_match_length (set_match_length T (ds_match_length T - 1))) with (ds_match_length T - 1) in HK by reflexivity.
  replace (ds_ins_h (set_match_length T (ds_match_length T - 1))) with (ds_ins_h T) in HK by reflexivity.
  replace (ds_strstart (set_match_length T (ds_match_length T - 1))) with (ds_strstart T) in HK by reflexivity.
  rewrite Rhm, Rwm.
  replace (wz (ds_match_length T + -2)) with (wz (ds_match_length T - 1 - 1)) by (f_equal; lia).
  eapply HK.
  split; [split|].
  - exact ZS.
  - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
      | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma fast_iexit : forall (Q : machine_state -> Prop) (Yf : deflate_state) (sn se : Z),
  0 <= ds_strstart Yf <= 65536 -> 0 <= sn < 2^32 -> 0 <= se < 2^32 ->
  (sn <> se -> FK L flush rest0 lo r F fc me Q Z_FAST_HEAD (set_strstart Yf (ds_strstart Yf + 1))) ->
  (sn = se -> FKA L flush rest0 lo r F fc me Q (set_strstart Yf (ds_strstart Yf + 1))) ->
  KIEX Q Yf (wz sn) (wz se).
Proof.
  intros Q Yf sn se Rss Rsn Rse KH0 KA0. unfold KIEX. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR. unfold fast_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  zs. name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : FINV L flush rest0 lo r me (set_strstart Yf (ds_strstart Yf + 1)) mB).
  { split; [split|].
    - exact ZS.
    - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - unfold FK, fastR, Z_FAST_HEAD in KH0. eapply (KH0 KB). exact SI'.
  - zs. specialize (KA0 ltac:(lia)). unfold FKA, fastR, Z_FAST_FBA in KA0.
    replace (ds_strstart (set_strstart Yf (ds_strstart Yf + 1))) with (ds_strstart Yf + 1) in KA0 by reflexivity.
    eapply KA0. exact SI'.
Qed.

Lemma fast_noins : forall (Q : machine_state -> Prop) (T : deflate_state) (sn se : Z),
  ILIF T -> 0 <= ds_match_length T <= 258 -> ds_strstart T + ds_match_length T + 2 <= 65536 -> 0 <= sn < 2^32 -> 0 <= se < 2^32 ->
  (sn <> se -> FK L flush rest0 lo r F fc me Q Z_FAST_HEAD (noins_st T)) ->
  (sn = se -> FKA L flush rest0 lo r F fc me Q (noins_st T)) ->
  KDEC L flush rest0 lo r F fc me Q 0x19244 T sn se.
Proof.
  intros Q T sn se HI Rml SS2 Rsn Rse KH0 KA0. unfold KDEC. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct HI as (Rss & Rih & Rhm & Rwm & Rhs & Rwb & Rhb).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_win Gwin.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR. unfold fast_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 5 zs. zs. zs. do 3 zs. rewrite ?Z.mod_small by lia.
  ld8 Gwin (ds_window T) 65536 (dl_Aw L) (ds_strstart T + ds_match_length T) ltac:(apply Rwb; lia).
  pose proof (Rwb (ds_strstart T + ds_match_length T) ltac:(lia)) as Rc0.
  remember (arr_get (ds_window T) (ds_strstart T + ds_match_length T)) as c0 eqn:Ec0.
  do 4 zs. rewrite ?Z.mod_small by lia. zs.
  ld8 Gwin (ds_window T) 65536 (dl_Aw L) (ds_strstart T + ds_match_length T + 1) ltac:(apply Rwb; lia).
  zs. zs. zs.
  rewrite (hash_mach T c0 (arr_get (ds_window T) (ds_strstart T + ds_match_length T + 1))) by lia.
  zs. name_mem mB.
  tr_groups MUf WMf.
  assert (ENO : noins_st T = set_ins_h (set_ins_h (set_match_length (set_strstart T (ds_strstart T + ds_match_length T)) 0) c0)
                                        (update_hash T c0 (arr_get (ds_window T) (ds_strstart T + ds_match_length T + 1))))
    by (rewrite Ec0; reflexivity).
  assert (SI' : FINV L flush rest0 lo r me (noins_st T) mB).
  { rewrite ENO. split; [split|].
    - exact ZS.
    - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA | exact GB| exact GC| exact GD
        | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | unfold dwin; exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - unfold FK, fastR, Z_FAST_HEAD in KH0. eapply (KH0 KB). exact SI'.
  - zs. specialize (KA0 ltac:(lia)). unfold FKA, fastR, Z_FAST_FBA in KA0.
    replace (ds_strstart (noins_st T)) with (ds_strstart T + ds_match_length T) in KA0 by reflexivity.
    eapply KA0. exact SI'.
Qed.

Lemma fast_insbr : forall (Q : machine_state -> Prop) (T : deflate_state) (sn se : Z),
  ILIF T -> 3 <= ds_match_length T <= 258 -> ds_strstart T + ds_match_length T + 2 <= 65536 -> 0 <= sn < 2^32 -> 0 <= se < 2^32 ->
  (sn <> se -> FK L flush rest0 lo r F fc me Q Z_FAST_HEAD (st_ins T)) ->
  (sn = se -> FKA L flush rest0 lo r F fc me Q (st_ins T)) ->
  KDEC L flush rest0 lo r F fc me Q 0x191ac T sn se.
Proof.
  intros Q T sn se TI Rml SS2 Rsn Rse KH0 KA0.
  pose proof TI as (Rss & Rih & Rhm & Rwm & Rhs & Rwb & Rhb).
  apply (fast_ins0 Q T); [exact TI| lia| lia|].
  set (Y0 := set_match_length T (ds_match_length T - 1)).
  assert (YI : ILIF Y0).
  { unfold ILIF, Y0. dsred. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Rwb| exact Rhb]. }
  assert (YML : ds_match_length Y0 = Z.of_nat (Z.to_nat (ds_match_length T - 1))) by (unfold Y0; dsred; rewrite Z2Nat.id; lia).
  assert (N1 : (1 <= Z.to_nat (ds_match_length T - 1))%nat) by lia.
  apply (fast_insl (Z.to_nat (ds_match_length T - 1)) Q Y0 (ds_hash_shift T) _ _ YI eq_refl YML N1);
    [rewrite Z2Nat.id by lia; lia| rewrite Z2Nat.id by lia; unfold Y0; dsred; lia|].
  destruct (fast_insert_strstart _ Y0 YML N1) as [EYS _]. rewrite Z2Nat.id in EYS by lia.
  rewrite st_ins_eq in KH0, KA0. cbv zeta in KH0, KA0. fold Y0 in KH0, KA0.
  apply (fast_iexit Q); [rewrite EYS; unfold Y0; dsred; lia| lia| lia| |].
  - intros NE. apply KH0. exact NE.
  - intros EQ. apply KA0. exact EQ.
Qed.
End FINS.
