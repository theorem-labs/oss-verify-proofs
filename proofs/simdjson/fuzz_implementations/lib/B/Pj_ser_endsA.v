(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_dispA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length sa_buf sa_size sa_cap]; lia]
  | |- _ => reflexivity
  end.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma land_topmask : forall w, 0 <= w < 2^64 -> Z.land w 18374686479671623680 = ttype w * 72057594037927936.
Proof.
  intros w Hw. unfold ttype. change (2 ^ 56) with 72057594037927936.
  replace 18374686479671623680 with (Z.shiftl (Z.ones 8) 56) by reflexivity.
  replace (w / 72057594037927936 * 72057594037927936) with (Z.shiftl (Z.shiftr w 56) 56)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec. rewrite !Z.shiftl_spec by lia.
  destruct (Z_lt_le_dec n 56) as [L|L].
  - rewrite !(Z.testbit_neg_r _ (n - 56)) by lia. apply Bool.andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (n - 56 + 56) with n by lia.
    destruct (Z_lt_le_dec n 64) as [M|M].
    + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r.
      destruct (Z.eq_dec w 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Hw)|]. apply Z.pow_le_mono_r; lia.
Qed.

Section Ends.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Variables (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (fu : nat).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis KX : exit_KA RT PMc E I K.
Hypothesis KH : head_stmtA RT PMc E I K D fu.
Notation aevt := (aevt RT PMc).
Notation RESTA := (rest_ok (pa_T E) (pa_S E) (pa_sn E)).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.

Lemma ends_loopA : forall (ks : list bool) (d0 : nat) (i2 c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  ks <> [] -> si_j I - i2 <= Z.of_nat fu -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  RESTA d0 ks i2 c2 (si_j I) (si_c' I) -> 1 <= i2 -> 0 <= c2 ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i2 - 1) + 6 * c2 + 2 ->
  CREDA RT E I Σ (2 * (si_j I - i2) + 1) st ->
  aevt Σ K (LSTA E I PJ_ENDS_A i2 (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) xt5
               xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX KX KH.
  induction ks as [|k ks IH]; intros d0 i2 c2 isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
    NE HF0 HD HL15 KR HR HI2 HC2 HSM FRM ACC CR; [congruence|]. clear NE.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (c_c' E D I CX) as (CC1 & CC2).
  pose proof (ok_wfS E OK) as WF. pose proof WF as (_ & SN & _).
  pose proof (sctx_out E D I OK CX) as OUTB. pose proof (pa_n_32 E OK) as N32.
  pose proof (rest_ok_lt _ _ _ _ _ _ _ _ _ _ HR) as LTJ.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (_ & LEC & _).
  pose proof (rest_ok_word _ _ _ SN _ _ _ _ _ _ _ HR ltac:(clear - HI2; lia) ltac:(clear - J2 N32; lia)) as WR.
  set (w := pa_T E i2) in *.
  assert (TYR : 0 <= ttype w < 256) by (unfold ttype; clear - WR; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  cbn [length] in *. rewrite Nat2Z.inj_succ in *.
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX.

  assert (JOIN : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (yt5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    (ttype w = t_arr_end \/ ttype w = t_obj_end) ->
    SERMA RT E I (wkC E) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size + 1 -> 0 <= size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - i2) + 1) st5 ->
    aevt Σ5 K (LSTA E I 0xba884 i2 (Z.succ (Z.of_nat (length ks))) (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz (pa_SB E + 80)) yt5
                  yra yt0 yt1 yt2 (wz (sa_buf st5 + size)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 x5 F5 yt5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HEND HSM5 ESZ SZ0' ROOM CR5.
    pose proof (rest_ok_end _ _ _ SN _ _ _ _ _ _ _ HR ltac:(clear - HI2; lia) ltac:(clear - J2 N32; lia) HEND) as HR'.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_cap sa_buf] in ESZ, ROOM |- *. subst size5.
    apply (aevt_evt RT AF PMc MST). ser_open HSM5 OK.
    pose proof (buf_factsA RT AF E D I Σ5 _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf5 + size) ltac:(clear - ROOM SZ0'; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. pj_store_done. zstep. zstep. step.
    ser_close HSM6 OK CX.
    if_cases K9; zify_cond K9; pjnorm_in K9.
    -
      apply evt_done.
      eapply aevt_eq; [| eapply (IH (S d0) (i2 + 1) c2 isobj Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))];
        [pj_st_eq| destruct ks; [cbn in K9; clear - K9; lia| discriminate]| clear - HF0; lia| clear - HD; lia| clear - HL15; lia
        | eapply kinds_rel_pop; exact KR| exact HR'| clear - HI2; lia| exact HC2| eexists; exact HSM6| exact FRM| cbn [sa_size]; clear - ACC; lia
        | eapply CREDA_le; [exact CR5| clear; lia]].
    -
      step. apply evt_done.
      assert (ks = []) by (destruct ks; [reflexivity| cbn [length] in K9; clear - K9; lia]). subst ks.
      destruct (rest_ok_nil_inv _ _ _ _ _ _ _ _ HR') as [EJ EC].
      eapply (KX isobj Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5)); [eexists; exact HSM6| exact FRM| cbn [sa_size]; clear - ACC EJ EC LTJ LEC; lia
        | eapply CREDA_le; [exact CR5| clear - LTJ; lia]]. }

  assert (TAIL : forall (pc : Z) (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word)
                        (yt5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    (pc = 0xba7c0 /\ ttype w = t_arr_end) \/ (pc = 0xba82c /\ ttype w = t_obj_end) ->
    SERMA RT E I (wkC E) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size -> 0 <= size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - i2) + 1) st5 ->
    aevt Σ5 K (LSTA E I pc i2 (Z.succ (Z.of_nat (length ks))) (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz (pa_SB E + 80)) yt5
                  yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F5 fc m5)).
  { intros pc Σ5 st5 m5 x5 F5 yt5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HPC HSM5 ESZ SZ0' ROOM CR5.
    assert (HEND : ttype w = t_arr_end \/ ttype w = t_obj_end) by (destruct HPC as [[_ H]|[_ H]]; [left| right]; exact H).
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_cap sa_buf] in ESZ, ROOM |- *. subst size5.
    apply (aevt_evt RT AF PMc MST). ser_open HSM5 OK.
    pose proof (shz_sb_mu RT AF E D I OK CX Σ5 _ _ _ HREF MU WM) as SHZ.
    pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.
    destruct HPC as [[-> _]|[-> _]].

    all: step; zstep; zstep; shz_norm; zstep; if_false; zstep; shz_norm; zstep; if_false; clear RD64 RD72.

    all: step; step; zstep; zstep; unbox FSB; unbox SHSB; step; box_disj.

    all: step; if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc SZ0' R0 BL LO; lia| clear Kc].
    all: zstep; zstep; zstep;
         replace (0 <? buf5) with true by (symmetry; apply Z.ltb_lt; clear - R0; lia);
         replace (buf5 + size <? 1) with false by (symmetry; apply Z.ltb_ge; clear - R0 SZ0'; lia);
         cbn [Z.b2z Z.lxor]; zstep; if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc; lia| clear Kc].
    all: zstep; if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc R0; lia| clear Kc].

    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (acc_buf_mu RT AF E D I OK CX Σ5 _ _ mm HREF MU WM) as ACCB end;
         cbn [sa_buf sa_cap] in ACCB;
         destruct (acc_read1 _ _ _ (buf5 + size) ACCB ltac:(clear - ROOM SZ0'; lia)) as (b & RDB & SOK); clear ACCB.
    all: zstep; pjnorm; zstep; zstep; clear RDB.
    all: ser_close HSM6 OK CX.
    all: destruct (pj_sh_ok_cases b (buf5 + size) SOK) as [-> | (kq & -> & K17 & KM)];
      [ rewrite sxb_z8; zstep; if_false
      | rewrite (pj_sxb_small7 kq) by (clear - K17; lia); zstep;
        (if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia]);

        zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ0'; lia); zstep;
        (if_cases Kc; zify_cond Kc;
          [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia]) ].

    1,2: zstep; step.
    3,4: zstep.
    all: apply evt_done.
    all: eapply aevt_eq; [| eapply (JOIN Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; slia. }

  assert (CLOSE : forall (m5 : mem) (x5 : xjA) (yra ya0 ya1 ya2 ya3 ya4 : word),
    (ttype w = t_arr_end \/ ttype w = t_obj_end) ->
    SERMA RT E I (wkC E) x5 ser_shpatA isobj Σ (mkSbA buf size cap hp kk) m5 ->
    evt bsegs (fun ms' => aevt Σ K ms')
        (LSTA E I 0xba754 i2 (Z.succ (Z.of_nat (length ks))) xs3 (wz (pa_SB E + 80)) xt5
              yra xt0 xt1 xt2 ya0 ya1 ya2 ya3 ya4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m5)).
  { intros m5 x5 yra ya0 ya1 ya2 ya3 ya4 HEND HSM5.

    zstep. zstep. zstep.
    eapply evt_cut; [eapply (ser_trefA RT AF E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) m5 i2 F fc);
      [exact OK| exact CX| exact HSM5| clear - HI2 LTJ J2; lia]|].
    cbv beta. intros ms1 (m6 & za4 & -> & HSM6). clear HSM5. rewrite (ret_pc_even 0xba760) by lia.
    ser_open HSM6 OK.
    pose proof (tape_read_mu RT AF E D I OK CX _ _ _ _ i2 HREF MU WM ltac:(clear - HI2 LTJ J2; lia)) as RDT. fold w in RDT.
    pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_TAPE E + 8 * i2) ltac:(clear - HI2 LTJ J2; lia)) as RDW.
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ _ HREF MU WM) as SHZ.
    pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

    zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. clear RDW.

    step. zstep. zstep. shz_norm. zstep. if_false. clear RD80.

    step. zstep. zstep. shz_norm. zstep. if_false. clear RD72.

    step. rewrite ?unsigned_lit by (clear - WR; lia). clear RDT. step. step. step.
    zstep. unfold TOPMASK. change ((255 * 2 ^ 56) mod 18446744073709551616) with 18374686479671623680. rewrite (land_topmask w) by (clear - WR; lia).
    zstep. step.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GROWN : forall pc : Z, (pc = 0xba7b4 /\ ttype w = t_arr_end) \/ (pc = 0xba820 /\ ttype w = t_obj_end) -> cap < size + 1 ->
      evt bsegs (fun ms' => aevt Σ K ms')
          (LSTA E I pc i2 (Z.succ (Z.of_nat (length ks))) (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz (pa_SB E + 80)) xt5
                (wz 0xba760) xt0 xt1 xt2 (wz (size + 1)) (wz cap) (wz END93) (wz (ttype w * 72057594037927936)) za4 xa5 xa6 xa7 xt3 xt4 xt6 F fc mm)) end.
    { intros pc HPC KC.
      pose proof HPC as [[-> HE]|[-> HE]].
      all: zstep; pjnorm; zstep; zstep.
      all: ser_close HSM7 OK CX; apply evt_done.
      1: eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - i2) + 1) 0xba7c0)];
           [pj_st_eq| exact OK| exact CX| exact HSM7| | exact CR| clear - LTJ; lia| clear; lia| reflexivity|].
      3: eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - i2) + 1) 0xba82c)];
           [pj_st_eq| exact OK| exact CX| exact HSM7| | exact CR| clear - LTJ; lia| clear; lia| reflexivity|].
      1,3: eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM7|]; cbn [sa_cap sa_size] in *; clear - KC ACC OUTB LTJ LEC HI2 HC2; lia.
      all: intros Σ' NEW m' F' yt0 yt1 yt2 ya0' ya1' ya2' ya3' ya4' ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM8 CR8.
      all: eapply aevt_eq; [| eapply (TAIL _ Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))];
           [pj_st_eq| first [left; split; [reflexivity| exact HE] | right; split; [reflexivity| exact HE]] | try eassumption..];
           unfold sb_grownA; slia. }

    step. if_cases K1; zify_cond K1; unfold END93 in K1; pjnorm_in K1.
    -
      assert (HE : ttype w = t_obj_end) by (destruct HEND as [HE|HE]; [exfalso; unfold t_arr_end in HE; clear - K1 HE; lia| exact HE]).
      step. if_cases K2; zify_cond K2; pjnorm_in K2.
      + ser_close HSM7 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (TAIL _ Σ (mkSbA buf size cap hp kk))]; [pj_st_eq| right; split; [reflexivity| exact HE]| try eassumption..]; slia.
      + eapply GROWN; [right; split; [reflexivity| exact HE]| clear - K2; lia].
    -
      assert (HE : ttype w = t_arr_end) by (unfold t_arr_end; clear - K1; lia).
      step. if_cases K2; zify_cond K2; pjnorm_in K2.
      + ser_close HSM7 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (TAIL _ Σ (mkSbA buf size cap hp kk))]; [pj_st_eq| left; split; [reflexivity| exact HE]| try eassumption..]; slia.
      + eapply GROWN; [left; split; [reflexivity| exact HE]| clear - K2; lia]. }

  apply (aevt_evt RT AF PMc MST). unfold PJ_ENDS_A.
  destruct HSM as (xv & HSM).

  zstep. zstep. zstep.
  eapply evt_cut; [eapply (ser_trefA RT AF E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) m i2 F fc);
    [exact OK| exact CX| exact HSM| clear - HI2 LTJ J2; lia]|].
  cbv beta. intros ms1 (m1 & ya4 & -> & HSM1). clear HSM. rewrite (ret_pc_even 0xba700) by lia.
  ser_open HSM1 OK.
  pose proof (tape_read_mu RT AF E D I OK CX _ _ _ _ i2 HREF MU WM ltac:(clear - HI2 LTJ J2; lia)) as RDT. fold w in RDT.
  pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_TAPE E + 8 * i2) ltac:(clear - HI2 LTJ J2; lia)) as RDW.

  zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. clear RDW.

  step. rewrite ?unsigned_lit by (clear - WR; lia). clear RDT. step.
  zstep. unfold TOPMASK. change ((255 * 2 ^ 56) mod 18446744073709551616) with 18374686479671623680. rewrite (land_topmask w) by (clear - WR; lia).
  step. step. if_cases K1; zify_cond K1; unfold END93 in K1; pjnorm_in K1.
  -
    assert (HE : ttype w = t_arr_end) by (unfold t_arr_end; clear - K1; lia).
    ser_close HSM2 OK CX.
    eapply evt_eq; [| eapply (CLOSE m1); [left; exact HE| exact HSM2]]. pj_st_eq.
  -
    ser_close HSM2 OK CX.
    zstep. zstep. zstep.
    eapply evt_cut; [eapply (ser_trefA RT AF E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) m1 i2 F fc);
      [exact OK| exact CX| exact HSM2| clear - HI2 LTJ J2; lia]|].
    cbv beta. intros ms2 (m2 & ya4' & -> & HSM3). clear HSM2. rewrite (ret_pc_even 0xba730) by lia.
    ser_open HSM3 OK.
    pose proof (tape_read_mu RT AF E D I OK CX _ _ _ _ i2 HREF MU WM ltac:(clear - HI2 LTJ J2; lia)) as RDT. fold w in RDT.
    pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_TAPE E + 8 * i2) ltac:(clear - HI2 LTJ J2; lia)) as RDW.

    zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. clear RDW.

    step. rewrite ?unsigned_lit by (clear - WR; lia). clear RDT. step.
    zstep. unfold TOPMASK. change ((255 * 2 ^ 56) mod 18446744073709551616) with 18374686479671623680. rewrite (land_topmask w) by (clear - WR; lia).
    step. step. if_cases K3; zify_cond K3; unfold END125 in K3; pjnorm_in K3.
    +
      assert (NA : SjTape.ty (pa_T E) i2 <> t_arr_end) by (unfold SjTape.ty, t_arr_end; fold w; clear - K1; lia).
      assert (NO : SjTape.ty (pa_T E) i2 <> t_obj_end) by (unfold SjTape.ty, t_obj_end; fold w; clear - K3; lia).
      destruct (rest_ok_item (pa_T E) (pa_S E) (pa_sn E) SN d0 k ks i2 c2 (si_j I) (si_c' I) HR NA NO) as (i3 & c3 & HIT & HR3).
      zstep. step.
      ser_close HSM4 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (KH d0 (k :: ks) i2 i3 c2 c3 true isobj Σ (mkSbA buf size cap hp kk))];
        [pj_st_eq| clear - HF0; lia| cbn [length]; clear - HD; lia| cbn [length]; clear - HL15; lia| exact KR| exact HIT| exact HR3| discriminate
        | exact HI2| exact HC2| exact HSM4| exact FRM| cbn [sa_size]; clear - ACC; lia| eapply CREDA_le; [exact CR| clear; lia]].
    +
      assert (HE : ttype w = t_obj_end) by (unfold t_obj_end; clear - K3; lia).
      ser_close HSM4 OK CX.
      eapply evt_eq; [| eapply (CLOSE m2); [right; exact HE| exact HSM4]]. pj_st_eq.
Qed.

Theorem aval_proofA : aval_stmtA RT PMc E I K D fu.
Proof using AF RC FDO MST GROW OK CX KX KH.
  unfold aval_stmtA.
  intros d0 ks i2 c2 isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL15 KR HR HI2 HC2 HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2).
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). unfold PJ_AV_A.
  destruct ks as [|k ks].
  -
    cbn [length] in *. step. if_cases K9; zify_cond K9; [clear K9| exfalso; pjnorm_in K9; cbn in K9; clear - K9; lia]. apply evt_done.
    destruct (rest_ok_nil_inv _ _ _ _ _ _ _ _ HR) as [EJ EC].
    eapply (KX isobj Σ (mkSbA buf size cap hp kk)); [exact HSM| exact FRM| cbn [sa_size]; clear - ACC EJ EC; lia| eapply CREDA_le; [exact CR| clear - EJ; lia]].
  -
    pose proof (rest_ok_lt _ _ _ _ _ _ _ _ _ _ HR) as LTJ.
    cbn [length] in *. step. if_cases K9; zify_cond K9; [exfalso; pjnorm_in K9; cbn in K9; clear - K9; lia| clear K9].
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (ends_loopA (k :: ks) d0 i2 c2 isobj Σ (mkSbA buf size cap hp kk))];
      [pj_st_eq| discriminate| exact HF0| exact HD| exact HL15| exact KR| exact HR| clear - HI2; lia| exact HC2| exact HSM| exact FRM| exact ACC| exact CR].
Qed.

End Ends.
