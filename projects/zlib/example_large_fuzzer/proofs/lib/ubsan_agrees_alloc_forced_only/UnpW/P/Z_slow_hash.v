(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_kit Z_lmatch.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow6. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeW LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section HASH.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.

Definition KLM (Q : machine_state -> Prop) (s : deflate_state) (hh : Z) : Prop :=
  forall (y1 y5 y6 y7 y13 y15 y16 y17 y18 y19 y25 y28 y29 y30 y31 : word) (m' : mem),
    SINV L flush rest0 lo r me s m' ->
    evt psegs Q (MS (slowR L r y1 y5 y6 y7 (wz flush) (wz 2) (wz hh) (wz (ds_prev_length s)) y13 (wz (ds_strstart s)) y15 y16 y17 y18 y19 y25 y28 y29 y30 y31) F (wz 0x199c8) fc None m' (seg_rom psegs)).

Lemma slow_hash : forall (Q : machine_state -> Prop) (X : deflate_state),
  strip_inv X -> 3 <= ds_lookahead X -> ds_w_size X = 32768 -> ds_hash_size X = 32768 ->
  KLM Q (hash_st X) (hash_hh X) ->
  KH L flush rest0 lo r F fc me Q X.
Proof.
  intros Q X SV LA3 WS HS HK. unfold KH. intros until m'. intros (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI) E13.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  destruct SV as [Rstr Rsl Rlook Rih Rhm Rwm Rhs Rml Rms Rpl Rpm Rma Rstrat Rlazy Rsn Rse Rwb Rhb Rpb Rlfc Rdfc].
  rewrite WS in *. rewrite HS in *.
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1].
  open_A GA. open_u16 Gprev. open_u16 Ghead.
  pose proof (ln_prev _ LENS) as Lprev. pose proof (ln_head _ LENS) as Lhead.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold slowR, Z_SLOW_HASH. unfold slow_frame in FR. unfold slow_W in MU.
  name_mem mA.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
  do 9 zs. rewrite ?Z.mod_small by lia.
  zs.
  ld8 Gwin (ds_window X) 65536 (dl_Aw L) (ds_strstart X + 2) ltac:(apply Rwb; lia).
  zs. zs. zs. zs. zs.
  rewrite (hash_mach X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2))) by lia.
  pose proof (update_hash_range X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2)) ltac:(lia)) as Rhv.
  remember (update_hash X (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 2))) as h eqn:Eh.
  zs. zs. rewrite (shl32_shr31 h) by lia. zs.
  ld16 Ghead (ds_head X) 32768 (dl_Ah L) h ltac:(apply Rhb; lia).
  zs. zs. zs.
  rewrite (Z.land_comm (ds_w_mask X) (ds_strstart X)), Z.shiftl_mul_pow2 by lia. change (2^1) with 2. rewrite (Z.mul_comm _ 2).
  pose proof (LmatchModel.land_upper_both (ds_strstart X) (ds_w_mask X) ltac:(lia) ltac:(lia)) as Rpi.
  remember (Z.land (ds_strstart X) (ds_w_mask X)) as pi eqn:Epi.
  st16 Gprev (ds_prev X) 32768 (dl_Ap L) pi (arr_get (ds_head X) h) ltac:(reflexivity).
  zs.
  st16 Ghead (ds_head X) 32768 (dl_Ah L) h (wrap16 (ds_strstart X)) ltac:(apply le2_wz_mod; rewrite unsigned_lit by lia; rewrite wrap16_mod, Z.mod_mod by lia; reflexivity).
  do 4 zs. name_mem mB.
  tr_groups MUf WMf.
  subst h pi. unfold KLM in HK.
  eapply HK.
  split; [split|].
  - exact ZS.
  - unfold hash_st, ins_str. constructor;
      [do 5 eexists; unfold dsA_cells; dsred; eapply rw_cells_sim; [exact GA| cells_sim_tac; exact E13]
      | exact GB| exact GC| exact GD| exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
      | exact Gwin| exact Gprev| exact Ghead| exact Gpend| close_lens_set LENS | exact LAY1].
  - split; [apply (dout_munch _ mA mB L rest0 _ DOUT ROOM MUf WMf); cbn [disjoint_from]; slia|]. split; [exact ROOM|].
    split; [exists j0; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| eassumption].
Qed.

Lemma slow_lm : forall (Q : machine_state -> Prop) (s : deflate_state) (hh : Z),
  0 <= ds_prev_length s <= 258 -> 0 <= ds_max_lazy_match s < 2^31 -> ds_w_size s = 32768 -> 0 <= ds_strstart s <= 65536 ->
  ds_match_length s = 2 -> 0 <= hh < 65536 -> 0 <= ds_strategy s <= 4 ->
  (sl_lm_cond s hh = true -> lm_ok s hh) -> strip_inv (st_lm s hh) ->
  KD L flush rest0 lo r F fc me Q (st_lm s hh) ->
  KLM Q s hh.
Proof.
  intros Q s hh Rpl Rlazy WS Rss ML2 Rhh Rstrat LMOK SVF HK. unfold KLM. intros until m'. intros SI.
  destruct CTX as [LOsp SP16 LAY BEL IO RELRO DIN]. unfold Z_SLOW_STACK in LOsp. clear SP16.
  lay_open LAY. below_open BEL. pose proof IO as I0. io_open I0.
  unfold KD in HK. unfold slowR in *. unfold Z_SLOW_DECIDE in HK.

  assert (C578 : forall (a1 a5 a6 a7 a11 a12 a13 a14 a15 a16 a17 a18 a19 a25 a28 a29 a30 a31 : word) (mm : mem),
    SINV L flush rest0 lo r me (st_lm s hh) mm ->
    evt psegs Q (MS (mkR a1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) a5 a6 a7 (wz (dl_As L)) (wz flush) (wz (ds_match_length (st_lm s hh))) a11 a12 a13 a14 a15 a16 a17 a18 a19
      (wz 65535) (wz (dl_As L + 5888)) (wz (dl_As L + 212)) (wz (-1)) (wz 262) a25 (wz 3) (wz (dl_As L + 2504)) a28 a29 a30 a31) F (wz 0x19a30) fc None mm (seg_rom psegs))).
  { intros until mm. intros SIF. pose proof SIF as (DR & _). destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
    pose proof (si_pl _ SVF) as Rplf.
    zs. eapply HK. exact SIF. }
  pose proof SI as (DR & DOUT & ROOM & (j0 & FR) & STK & MU & WM & MI).
  destruct DR as [ZS ST]. destruct ST as [GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend LENS LAY1]. open_A GA.
  unfold slow_frame in FR. unfold slow_W in MU.
  zstep. if_cases KH0; zify_cond KH0; rewrite ?unsigned_lit in KH0 by lia.
  -
    assert (EST : st_lm s hh = s) by (apply st_lm_false; unfold sl_lm_cond; replace (hh =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
    rewrite EST in HK. rewrite ML2 in HK. eapply HK. exact SI.
  - zs. zs. zstep. if_cases KLZ; zify_cond KLZ; rewrite ?unsigned_lit in KLZ by lia.
    +
      assert (EST : st_lm s hh = s).
      { apply st_lm_false. unfold sl_lm_cond. replace (ds_prev_length s <? ds_max_lazy_match s) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity. }
      rewrite EST in C578. rewrite ML2 in C578. eapply C578. exact SI.
    + zs. zs. zs. zstep.
      if_cases KD0; zify_cond KD0; rewrite ?WS in KD0.
      *
        assert (EST : st_lm s hh = s).
        { apply st_lm_false. unfold sl_lm_cond. rewrite WS.
          replace (wrap32 (ds_strstart s - hh) <=? 32768 - 262) with false; [rewrite andb_false_r; reflexivity|].
          symmetry. apply Z.leb_gt. rewrite wrap32_mod. change (2^32) with 4294967296.
          Z.div_mod_to_equations. lia. }
        rewrite EST in C578. rewrite ML2 in C578. eapply C578. exact SI.
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
        pose proof (munch_refl [(lo, bv_unsigned (r_sp r) + -128); (dl_As L, dl_As L + 212)] mA) as MUf. pose proof (wmono_refl psegs mA) as WMf.
        clear GA.
        zs. zs.
        call (longest_match_spec L s hh lo).
        1:{ exact ST0. } 1:{ exact MI. } 1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. lia. } 1:{ unfold dlay_below. rewrite ESP. lia. }
        1:{ exact LM. } 1:{ exact WS. } 1:{ reflexivity. } 1:{ reflexivity. }
        name_mem mB. rewrite ESP in PC.
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
        pose proof (munch_refl [(dl_As L, dl_As L + 212)] mB) as MUf. pose proof (wmono_refl psegs mB) as WMf.
        zs. name_mem mC.
        tr_groups MUf WMf.
        assert (DOUTC : dout mC L rest0 (ds_strm s)) by (apply (dout_munch _ mB mC L rest0 _ DOUTB ROOM MUf WMf); cbn [disjoint_from]; slia).
        clear MUf WMf DOUTB.
        remember (set_match_length (set_match_start s ms) rl) as s1 eqn:Es1.
        assert (SI1 : SINV L flush rest0 lo r me s1 mC).
        { rewrite Es1. split; [split|].
          - exact ZS.
          - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA'
              | exact GB'| exact GC'| exact GD'| exact Glt'| exact Gdt'| exact Gbt'| exact Gblc'| exact Gheap'| exact Gdep'
              | exact Gwin'| exact Gprev'| exact Ghead'| exact Gpend'| close_lens LENS' | exact LAY'].
          - split; [exact DOUTC|]. split; [exact ROOM|]. split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
        assert (C550 : (rl <=? 5) && ((ds_strategy s =? 1) || (rl =? 3) && (4096 <? wrap32 (ds_strstart s - ms))) = true ->
          forall (a1 a5 a6 a7 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a25 a28 a29 a30 a31 : word),
          evt psegs Q (MS (mkR a1 (wz (bv_unsigned (r_sp r) + -128)) (r_gp r) (r_tp r) a5 a6 a7 (wz (dl_As L)) (wz flush) a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
            (wz 65535) (wz (dl_As L + 5888)) (wz (dl_As L + 212)) (wz (-1)) (wz 262) a25 (wz 3) (wz (dl_As L + 2504)) a28 a29 a30 a31) F (wz 0x19a08) fc None mC (seg_rom psegs))).
        { intros CT. intros. rewrite CT in EST.
          pose proof (munch_refl [(dl_As L, dl_As L + 212)] mC) as MUf. pose proof (wmono_refl psegs mC) as WMf.
          zs. zs. name_mem mD. zs.
          tr_groups MUf WMf.
          assert (DOUTD : dout mD L rest0 (ds_strm s)) by (apply (dout_munch _ mC mD L rest0 _ DOUTC ROOM MUf WMf); cbn [disjoint_from]; slia).
          rewrite EST in C578. eapply C578.
          rewrite Es1. split; [split|].
          - exact ZS.
          - constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA'
              | exact GB'| exact GC'| exact GD'| exact Glt'| exact Gdt'| exact Gbt'| exact Gblc'| exact Gheap'| exact Gdep'
              | exact Gwin'| exact Gprev'| exact Ghead'| exact Gpend'| close_lens LENS' | exact LAY'].
          - split; [exact DOUTD|]. split; [exact ROOM|]. split; [exists j0; exact FR|]. split; [exact PC|]. split; [exact MU|]. split; [exact WM| eassumption]. }
        pose proof (si_strat _ SVF) as Rst0.
        zs. zstep. if_cases KF1; zify_cond KF1; rewrite ?unsigned_lit in KF1 by lia.
        --
           replace (rl <=? 5) with false in EST by (symmetry; apply Z.leb_gt; lia). cbn [andb] in EST.
           rewrite EST in C578. rewrite Es1 in C578. eapply C578. rewrite <- Es1. exact SI1.
        -- zs. zs. zstep. if_cases KF2; zify_cond KF2; rewrite ?unsigned_lit in KF2 by lia.
           ++
              zstep. if_cases KF3; zify_cond KF3; rewrite ?unsigned_lit in KF3 by lia.
              **
                 replace (ds_strategy s =? 1) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                 replace (rl =? 3) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                 cbn [andb orb] in EST. rewrite andb_false_r in EST.
                 rewrite EST in C578. rewrite Es1 in C578. eapply C578. rewrite <- Es1. exact SI1.
              **
                 zs. zs. zs. zs. zstep.
                 if_cases KF4; zify_cond KF4.
                 ---
                     eapply C550. replace (rl <=? 5) with true by (symmetry; apply Z.leb_le; lia).
                     replace (rl =? 3) with true by (symmetry; apply Z.eqb_eq; lia).
                     replace (4096 <? wrap32 (ds_strstart s - ms)) with true; [rewrite orb_true_r; reflexivity|].
                     symmetry. apply Z.ltb_lt. pose proof (toofar_mach (ds_strstart s) ms Rms) as TF. lia.
                 --- zs.
                     replace (rl <=? 5) with true in EST by (symmetry; apply Z.leb_le; lia).
                     replace (ds_strategy s =? 1) with false in EST by (symmetry; apply Z.eqb_neq; lia).
                     replace (4096 <? wrap32 (ds_strstart s - ms)) with false in EST.
                     2:{ symmetry. apply Z.ltb_ge. pose proof (toofar_mach (ds_strstart s) ms Rms) as TF. lia. }
                     rewrite andb_false_r in EST. cbn [andb orb] in EST.
                     assert (E3 : rl = 3) by lia. subst rl.
                     rewrite EST in C578. rewrite Es1 in C578.
                     eapply C578. rewrite <- Es1. exact SI1.
           ++
              eapply C550. replace (rl <=? 5) with true by (symmetry; apply Z.leb_le; lia).
              replace (ds_strategy s =? 1) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
Qed.
End HASH.
