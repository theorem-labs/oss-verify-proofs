(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_lmatch Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel LmatchModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section HASH.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (fj : list byte) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFL : 0 <= flush <= 5.

Definition KLM (Q : machine_state -> Prop) (s : deflate_state) (hh : Z) : Prop :=
  forall (y1 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r fj me s m' ->
    evt usegs Q (MS (slowR L flush r y1 y5 y6 y7 (wz 2) (wz hh) (wz (ds_prev_length s)) y13 y14 y15 y16 y17 y28 y29 y30 y31) F (wz 0x1a244) fc None m' (seg_rom usegs)).

Lemma slow_hash : forall (Q : machine_state -> Prop) (X : deflate_state),
  strip_inv X -> 3 <= ds_lookahead X -> ds_w_size X = 32768 -> ds_hash_size X = 32768 ->
  KLM Q (hash_st X) (hash_hh X) ->
  KH L flush rest0 lo r fj F fc me Q X.
Proof.
  intros Q X SV LA3 WS HS HK. unfold KH, SK. intros until m'. intros (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *. rewrite HS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_u16 Gprev. open_u16 Ghead.
  pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (lo_h _ LAY) as BKh. unfold blk_ok in BKh. pose proof (lo_p _ LAY) as BKp. unfold blk_ok in BKp.
  unfold slowR, Z_SLOW_HASH. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
  zs. gF. zs. zs. zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX. gF.
  zs.
  ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 2) ltac:(apply Rwb; lia).
  zs. zs. zs. zs. zs.
  rewrite (hash_mach X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2))) by lia.
  pose proof (update_hash_range X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2)) ltac:(lia)) as Rhv.
  remember (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2))) as h eqn:Eh.
  zstep. zstep. rewrite (shl32_shr31 h) by lia. zstep. zs.
  gF. zstep. zstep. zstep. gX. gF. zstep.
  assert (ALh : (dl_Ah L + 2 * h) mod 2 = 0) by (clear - BKh Rhv; Z.div_mod_to_equations; lia).
  first [rewrite (land1_mod2 _ ALh) | replace (2 * h + dl_Ah L) with (dl_Ah L + 2 * h) by lia; rewrite (land1_mod2 _ ALh)]. gF.
  zs. zs. zstep. zstep. zstep.
  rewrite (Z.land_comm (ds_w_mask X) (ds_strstart X)), ?Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite ?(Z.mul_comm _ 2).
  pose proof (LmatchModel.land_upper_both (ds_strstart X) (ds_w_mask X) ltac:(lia) ltac:(lia)) as Rpi.
  remember (Z.land (ds_strstart X) (ds_w_mask X)) as pi eqn:Epi.
  gF. zstep. zstep. zstep. gX. gF. zstep.
  assert (ALp : (dl_Ap L + 2 * pi) mod 2 = 0) by (clear - BKp Rpi; Z.div_mod_to_equations; lia).
  first [rewrite (land1_mod2 _ ALp) | replace (2 * pi + dl_Ap L) with (dl_Ap L + 2 * pi) by lia; rewrite (land1_mod2 _ ALp) | replace (dl_Ap L + pi * 2) with (dl_Ap L + 2 * pi) by lia; rewrite (land1_mod2 _ ALp)]. gF.
  ld16 Ghead (ds_head X) 32768 (dl_Ah L) h ltac:(apply Rhb; lia).
  st16 Gprev (ds_prev X) 32768 (dl_Ap L) pi (arr_get (ds_head X) h) ltac:(reflexivity).
  gF.
  st16 Ghead (ds_head X) 32768 (dl_Ah L) h (wrap16 (ds_strstart X)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
  zstep.
  zs. zs. rewrite (sx32_wz (ds_match_length X)) by lia. zstep. zs. zs. zs. name_mem mB.
  tr_groups MUf WMf.
  subst h pi. unfold KLM in HK. unfold slowR in HK.
  replace (wz (ds_match_length X)) with (wz (ds_prev_length (hash_st X))) by reflexivity.
  change (arr_get (ds_head X) (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2)))) with (hash_hh X).
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold hash_st, ins_str. constructor;
      [do 5 eexists; unfold dsA_cells; dsred; eapply rw_cells_sim; [exact GA| cells_sim_tac; apply le4_sx32_wz; lia]
      | exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_lm : forall (Q : machine_state -> Prop) (s : deflate_state) (hh : Z),
  0 <= ds_prev_length s <= 258 -> 0 <= ds_max_lazy_match s < 2^31 -> ds_w_size s = 32768 -> 0 <= ds_strstart s <= 65536 ->
  ds_match_length s = 2 -> 0 <= hh < 65536 -> 0 <= ds_strategy s <= 4 ->
  (sl_lm_cond s hh = true -> lm_ok s hh) -> strip_inv (st_lm s hh) ->
  KD L flush rest0 lo r fj F fc me Q (st_lm s hh) ->
  KLM Q s hh.
Proof.
  intros Q s hh Rpl Rlazy WS Rss ML2 Rhh Rstrat LMOK SVF HK. unfold KLM. intros until m'. intros SI.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16. unfold Z_NO_FLUSH, Z_FINISH in HFL.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold KD in HK. unfold slowR in *. unfold Z_SLOW_DECIDE in HK.
  pose proof SI as (DR & DOUT & ROOM & FR & STK & MU & WM & MI).
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1]. open_A GA.
  unfold slow_frame in FR. unfold slow_W in MU.
  assert (RWS : 0 <= ds_w_size s < 2^31) by lia.
  zstep. if_cases KH0; zify_cond KH0; rewrite ?unsigned_lit in KH0 by lia.
  -
    assert (EST : st_lm s hh = s) by (apply st_lm_false; unfold sl_lm_cond; replace (hh =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
    rewrite EST in HK. rewrite ML2 in HK. eapply HK. exact SI.
  - zs. zstep. if_cases KLZ; zify_cond KLZ; rewrite ?unsigned_lit in KLZ by lia.
    +
      assert (EST : st_lm s hh = s).
      { apply st_lm_false. unfold sl_lm_cond. replace (ds_prev_length s <? ds_max_lazy_match s) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity. }
      rewrite EST in HK. rewrite ML2 in HK. eapply HK. exact SI.
    + zs. zs. zs. zs. zstep.
      if_cases KD0; zify_cond KD0; rewrite ?WS in KD0.
      *
        assert (EST : st_lm s hh = s).
        { apply st_lm_false. unfold sl_lm_cond. rewrite WS.
          replace (wrap32 (ds_strstart s - hh) <=? 32768 - 262) with false; [rewrite andb_false_r; reflexivity|].
          symmetry. apply Z.leb_gt. rewrite wrap32_mod. change (2^32) with 4294967296.
          Z.div_mod_to_equations. lia. }
        rewrite EST in HK. rewrite ML2 in HK. eapply HK. exact SI.
      * assert (CND : sl_lm_cond s hh = true).
        { unfold sl_lm_cond. rewrite WS.
          replace (hh =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          replace (ds_prev_length s <? ds_max_lazy_match s) with true by (symmetry; apply Z.ltb_lt; lia).
          replace (wrap32 (ds_strstart s - hh) <=? 32768 - 262) with true; [reflexivity|].
          symmetry. apply Z.leb_le. rewrite wrap32_mod. change (2^32) with 4294967296.
          Z.div_mod_to_equations. lia. }
        pose proof (LMOK CND) as LM.
        assert (ESP : bv_unsigned (wz (bv_unsigned (r_sp r) + -128)) = bv_unsigned (r_sp r) + -128) by (apply unsigned_lit; lia).
        pose proof SI as (DR0 & _). destruct DR0 as [_ ST0].
        name_mem mA.
        pose proof (munch_refl [(lo, bv_unsigned (r_sp r) + -128); (dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl usegs mA) as WMf.
        clear GA.
        zstep. zstep.
        call (longest_match_spec L s hh lo).
        1:{ exact ST0. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ unfold dlay_below. rewrite ESP. lia. }
        1:{ exact LM. } 1:{ exact WS. } 1:{ reflexivity. } 1:{ reflexivity. }
        name_mem mB.
        lazymatch goal with H : stk usegs mB lo _ |- _ => rewrite ?ESP in H; rename H into STK1 end.
        lazymatch goal with H : DST mB L _ |- _ => rename H into POST end.
        lazymatch goal with H : mem_inv usegs mB |- _ => rename H into MI1 end.
        assert (Rrl : 0 <= snd (longest_match s hh) <= 258) by (unfold lm_ok in LM; decompose [and] LM; lia).
        destruct (longest_match_ms s hh) as (ms & Ems).
        pose proof (st_lm_true s hh CND) as EST. cbv zeta in EST. rewrite Ems in EST, POST.
        remember (snd (longest_match s hh)) as rl eqn:Erl. clear Erl Ems.
        rewrite sl_filter_eq in EST.
        assert (Rms : 0 <= ms < 2^32) by (pose proof (si_ms _ SVF) as R0; rewrite EST in R0; destruct (_ && _) in R0; exact R0).
        destruct POST as [GA' GB' GC' GD' Glt' Gdt' Gbt' Gblc' Gheap' Gdep' Gwin' Gprev' Ghead' Gpend' LENS' LAY'].
        clear GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend ST0 LENS LAY1.
        tr_groups MUf WMf.
        assert (DOUTB : dout mB L rest0 (ds_strm s)) by (apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia).
        clear MUf WMf DOUT.
        open_A GA'. dsred in GA'.
        pose proof (munch_refl [(dl_As L, dl_As L + 212)] mB) as MUf. pose proof (wmono_refl usegs mB) as WMf.
        zs. name_mem mC.
        tr_groups MUf WMf.
        assert (DOUTC : dout mC L rest0 (ds_strm s)) by (apply (dout_munch _ mB mC L rest0 _ DOUTB ROOM MUf WMf); cbn [disjoint_from]; slia).
        clear MUf WMf DOUTB.
        remember (set_match_length (set_match_start s ms) rl) as s1 eqn:Es1.
        assert (SI1 : SINV L flush rest0 lo r fj me s1 mC).
        { rewrite Es1. split; [split|].
          - exact ZS.
          - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA'
              | exact GB'| exact GC'| exact GD'| exact Glt'| exact Gdt'| exact Gbt'| exact Gblc'| exact Gheap'| exact Gdep'
              | exact Gwin'| exact Gprev'| exact Ghead'| exact Gpend'| close_lens LENS' | exact LAY'].
          - split; [exact DOUTC|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| exact MI1]. }
        assert (C550 : (rl <=? 5) && ((ds_strategy s =? 1) || (rl =? 3) && (4096 <? wrap32 (ds_strstart s - ms))) = true ->
          forall (a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31 : word),
          evt usegs Q (MS (slowR L flush r a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a28 a29 a30 a31) F (wz 0x1a284) fc None mC (seg_rom usegs))).
        { intros CT. intros. unfold slowR. rewrite CT in EST.
          pose proof (munch_refl [(dl_As L, dl_As L + 212)] mC) as MUf. pose proof (wmono_refl usegs mC) as WMf.
          zstep. zs. name_mem mD. zstep.
          tr_groups MUf WMf.
          assert (DOUTD : dout mD L rest0 (ds_strm s)) by (apply (dout_munch _ mC mD L rest0 _ DOUTC ROOM MUf WMf); cbn [disjoint_from]; slia).
          rewrite EST in HK. replace (wz 2) with (wz (ds_match_length (set_match_length s1 2))) at 1 by reflexivity.
          eapply HK.
          rewrite Es1. split; [split|].
          - exact ZS.
          - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA'
              | exact GB'| exact GC'| exact GD'| exact Glt'| exact Gdt'| exact Gbt'| exact Gblc'| exact Gheap'| exact Gdep'
              | exact Gwin'| exact Gprev'| exact Ghead'| exact Gpend'| close_lens LENS' | exact LAY'].
          - split; [exact DOUTD|]. split; [exact ROOM|]. split; [exact FR|]. split; [exact STK1|]. split; [exact MU|]. split; [exact WM| eassumption]. }
        pose proof (si_strat _ SVF) as Rst0.
        zstep. zstep. if_cases KF1; zify_cond KF1; rewrite ?unsigned_lit in KF1 by lia.
        --
           replace (rl <=? 5) with false in EST by (symmetry; apply Z.leb_gt; lia). cbn [andb] in EST.
           rewrite EST in HK. rewrite Es1 in HK. replace (wz rl) with (wz (ds_match_length (set_match_length (set_match_start s ms) rl))) by reflexivity.
           eapply HK. rewrite <- Es1. exact SI1.
        -- zs. zstep. zstep. if_cases KF2; zify_cond KF2; rewrite ?unsigned_lit in KF2 by lia.
           ++
              zstep. if_cases KF3; zify_cond KF3; rewrite ?unsigned_lit in KF3 by lia.
              **
                 replace (ds_strategy s =? 1) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                 replace (rl =? 3) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                 cbn [andb orb] in EST. rewrite andb_false_r in EST.
                 rewrite EST in HK. rewrite Es1 in HK. replace (wz rl) with (wz (ds_match_length (set_match_length (set_match_start s ms) rl))) by reflexivity.
                 eapply HK. rewrite <- Es1. exact SI1.
              **
                 zs. zs. zs. zs. zstep.
                 if_cases KF4; zify_cond KF4.
                 ---
                     eapply C550. replace (rl <=? 5) with true by (symmetry; apply Z.leb_le; lia).
                     replace (rl =? 3) with true by (symmetry; apply Z.eqb_eq; lia).
                     replace (4096 <? wrap32 (ds_strstart s - ms)) with true; [rewrite orb_true_r; reflexivity|].
                     symmetry. apply Z.ltb_lt. pose proof (toofar_mach (ds_strstart s) ms Rms) as TF. lia.
                 --- zstep.
                     replace (rl <=? 5) with true in EST by (symmetry; apply Z.leb_le; lia).
                     replace (ds_strategy s =? 1) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                     replace (4096 <? wrap32 (ds_strstart s - ms)) with false in EST.
                     2:{ symmetry. apply Z.ltb_ge. pose proof (toofar_mach (ds_strstart s) ms Rms) as TF. lia. }
                     rewrite andb_false_r in EST. cbn [andb orb] in EST.
                     assert (E3 : rl = 3) by lia. subst rl.
                     rewrite EST in HK. rewrite Es1 in HK. replace (wz 3) with (wz (ds_match_length (set_match_length (set_match_start s ms) 3))) at 1 by reflexivity.
                     eapply HK. rewrite <- Es1. exact SI1.
           ++
              eapply C550. replace (rl <=? 5) with true by (symmetry; apply Z.leb_le; lia).
              replace (ds_strategy s =? 1) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
Qed.
End HASH.
