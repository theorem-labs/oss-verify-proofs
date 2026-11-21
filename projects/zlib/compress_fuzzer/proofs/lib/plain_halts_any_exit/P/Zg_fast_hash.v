(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_lmatch Zg_fast_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast2 RefDeflFast3 RefDeflFast6 LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section FHASH.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Lemma fast_hash : forall (Q : machine_state -> Prop) (X : deflate_state),
  trip_inv X -> 3 <= ds_lookahead X -> ds_w_size X = 32768 -> ds_hash_size X = 32768 ->
  (lm_cond (ins_str X (ds_strstart X)) (hash_hh X) = false -> FK L flush rest0 lo r F fc me Q Z_FAST_MTEST (ins_str X (ds_strstart X))) ->
  (lm_cond (ins_str X (ds_strstart X)) (hash_hh X) = true -> FKL L flush rest0 lo r F fc me Q (ins_str X (ds_strstart X)) (hash_hh X)) ->
  FK L flush rest0 lo r F fc me Q Z_FAST_HASH X.
Proof.
  intros Q X SV LA3 WS HS KM KL. unfold FK. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *. rewrite HS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_u16 Gprev. open_u16 Ghead.
  pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR, Z_FAST_HASH. unfold fast_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 9 zs. rewrite ?Z.mod_small by lia.
  zs.
  ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 2) ltac:(apply Rwb; lia).
  zs. zs. zs. zs. zs. zs.
  rewrite (hash_mach X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2))) by lia.
  pose proof (update_hash_range X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2)) ltac:(lia)) as Rhv.
  remember (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2))) as h eqn:Eh.
  zs. zs. rewrite (shl32_shr31 h) by lia. zs.
  ld16 Ghead (ds_head X) 32768 (dl_Ah L) h ltac:(apply Rhb; lia).
  pose proof (Rhb h ltac:(lia)) as Rhh.
  zs. zs. zs.
  rewrite (Z.land_comm (ds_w_mask X) (ds_strstart X)), Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite (Z.mul_comm _ 2).
  pose proof (LmatchModel.land_upper_both (ds_strstart X) (ds_w_mask X) ltac:(lia) ltac:(lia)) as Rpi.
  remember (Z.land (ds_strstart X) (ds_w_mask X)) as pi eqn:Epi.
  st16 Gprev (ds_prev X) 32768 (dl_Ap L) pi (arr_get (ds_head X) h) ltac:(reflexivity).
  st16 Ghead (ds_head X) 32768 (dl_Ah L) h (wrap16 (ds_strstart X)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
  name_mem mB.
  tr_groups MUf WMf.
  assert (SI' : FINV L flush rest0 lo r me (ins_str X (ds_strstart X)) mB).
  { subst h pi. split; [split|].
    - exact ZS.
    - unfold ins_str. constructor;
        [do 5 eexists; unfold dsA_cells; dsred; close_cells GA
        | exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
        | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
    - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
      split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  assert (EHH : hash_hh X = arr_get (ds_head X) h) by (rewrite Eh; reflexivity).
  rewrite lm_cond_eq in KM, KL. replace (ds_strstart (ins_str X (ds_strstart X))) with (ds_strstart X) in KM, KL by reflexivity.
  replace (ds_w_size (ins_str X (ds_strstart X))) with (ds_w_size X) in KM, KL by reflexivity.
  rewrite WS, EHH in KM, KL. unfold FK, FKL, fastR, Z_FAST_MTEST, Z_FAST_LMCALL in KM, KL.
  clear Gprev Ghead MUf WMf.
  zstep. if_cases KH0; zify_cond KH0; rewrite ?unsigned_lit in KH0 by lia.
  -
    eapply KM; [| exact SI'].
    replace (arr_get (ds_head X) h =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - zs. zs. zs. zstep. if_cases KD0; zify_cond KD0; rewrite ?WS in KD0.
    +
      eapply KL; [| exact SI'].
      replace (arr_get (ds_head X) h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (wrap32 (ds_strstart X - arr_get (ds_head X) h) <=? 32768 - 262) with true; [reflexivity|].
      symmetry. apply Z.leb_le. rewrite wrap32_mod. change (2^32) with 4294967296.
      Z.div_mod_to_equations. lia.
    +
      eapply KM; [| exact SI'].
      replace (wrap32 (ds_strstart X - arr_get (ds_head X) h) <=? 32768 - 262) with false; [rewrite andb_false_r; reflexivity|].
      symmetry. apply Z.leb_gt. rewrite wrap32_mod. change (2^32) with 4294967296.
      Z.div_mod_to_equations. lia.
Qed.

Lemma fast_mtest : forall (Q : machine_state -> Prop) (X : deflate_state),
  0 <= ds_match_length X <= 258 ->
  (3 <= ds_match_length X -> FKD L flush rest0 lo r F fc me Q X) ->
  (ds_match_length X < 3 -> FK L flush rest0 lo r F fc me Q Z_FAST_LIT X) ->
  FK L flush rest0 lo r F fc me Q Z_FAST_MTEST X.
Proof.
  intros Q X Rml KD KLIT. unfold FK. intros until m'. intros SI.
  pose proof SI as (DR & _). destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
  unfold fastR, Z_FAST_MTEST. unfold FK, FKD, fastR, Z_FAST_LIT, Z_FAST_DIST in KD, KLIT.
  zs. zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
  - eapply (KLIT ltac:(lia)). exact SI.
  - eapply (KD ltac:(lia)). exact SI.
Qed.

Lemma fast_lm : forall (Q : machine_state -> Prop) (s : deflate_state) (hh : Z),
  ds_w_size s = 32768 -> lm_ok s hh ->
  (3 <= snd (longest_match s hh) -> FKD L flush rest0 lo r F fc me Q (set_match_length (fst (longest_match s hh)) (snd (longest_match s hh)))) ->
  (snd (longest_match s hh) < 3 -> FK L flush rest0 lo r F fc me Q Z_FAST_LIT (set_match_length (fst (longest_match s hh)) (snd (longest_match s hh)))) ->
  FKL L flush rest0 lo r F fc me Q s hh.
Proof.
  intros Q s hh WS LM KD KLIT. unfold FKL. intros until m'. intros SI.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold fastR, Z_FAST_LMCALL. unfold FK, FKD, fastR, Z_FAST_LIT, Z_FAST_DIST in KD, KLIT.
  pose proof SI as (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct DR as [ZS ST0].
  unfold fast_frame in FR. unfold slow_W in MU.
  assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
  name_mem mA.
  pose proof (munch_refl [(lo, bv_unsigned (r_sp r) + -128); (dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  zs. zs.
  call (longest_match_spec L s hh lo).
  1:{ exact ST0. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ unfold dlay_below. rewrite ESP. lia. }
  1:{ exact LM. } 1:{ exact WS. } 1:{ reflexivity. } 1:{ reflexivity. }
  name_mem mB. rewrite ESP in PC.
  assert (Rrl : 0 <= snd (longest_match s hh) <= 258) by (unfold lm_ok in LM; decompose [and] LM; lia).
  destruct (longest_match_ms s hh) as (ms & Ems).
  rewrite Ems in POST, KD, KLIT.
  remember (snd (longest_match s hh)) as rl eqn:Erl. clear Erl Ems.
  destruct POST as [GA' GB' GC' GD' Glt' Gdt' Gbt' Gblc' Gheap' Gdep' Gwin' Gprev' Ghead' Gpend' LENS' LAY'].
  clear ST0.
  tr_groups MUf WMf.
  assert (DOUTB : dout mB L rest0 (ds_strm s)) by (apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia).
  clear MUf WMf DOUT.
  open_A GA'. dsred in GA'.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] mB) as MUf. pose proof (wmono_refl psegs mB) as WMf.
  zs. name_mem mC.
  tr_groups MUf WMf.
  assert (DOUTC : dout mC L rest0 (ds_strm s)) by (apply (dout_munch _ mB mC L rest0 _ DOUTB ROOM MUf WMf); cbn [disjoint_from]; slia).
  clear MUf WMf DOUTB.
  remember (set_match_length (set_match_start s ms) rl) as s1 eqn:Es1.
  assert (SI1 : FINV L flush rest0 lo r me s1 mC).
  { rewrite Es1. split; [split|].
    - exact ZS.
    - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA'
        | exact GB'| exact GC'| exact GD'| exact Glt'| exact Gdt'| exact Gbt'| exact Gblc'| exact Gheap'| exact Gdep'
        | exact Gwin'| exact Gprev'| exact Ghead'| exact Gpend'| close_lens LENS' | exact LAY'].
    - split; [exact DOUTC|]. split; [exact ROOM|]. split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
  assert (EML : ds_match_length s1 = rl) by (rewrite Es1; reflexivity).
  rewrite EML in KD.
  zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
  - eapply (KD ltac:(lia)). exact SI1.
  - eapply (KLIT ltac:(lia)). exact SI1.
Qed.
End FHASH.
