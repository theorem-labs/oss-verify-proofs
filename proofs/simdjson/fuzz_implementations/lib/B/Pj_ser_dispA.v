(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_trefA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA.
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

Section Disp.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis MST : mat_stable PMc.
Variables (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (fu : nat).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis AV : aval_stmtA RT PMc E I K D fu.
Hypothesis OPA : open_stmtA RT PMc E I K D fu false.
Hypothesis OPO : open_stmtA RT PMc E I K D fu true.
Hypothesis PSTR : str_stmtA RT PMc.
Hypothesis PI64 : i64_stmtA RT PMc.
Hypothesis PU64 : u64_stmtA RT PMc.
Hypothesis PDBL : dbl_stmtA RT PMc.
Hypothesis PTRUE : true_stmtA RT PMc.
Hypothesis PFALSE : false_stmtA RT PMc.
Hypothesis PNULL : null_stmtA RT PMc.
Notation aevt := (aevt RT PMc).
Notation RESTA := (rest_ok (pa_T E) (pa_S E) (pa_sn E)).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.

Lemma av_K_ofA : forall (d0 : nat) (ks : list bool) (i2 c2 : Z) (isobj : list byte) (X bound : Z),
  si_j I - i2 <= Z.of_nat fu -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  RESTA d0 ks i2 c2 (si_j I) (si_c' I) -> 2 <= i2 -> 0 <= c2 -> bound <= 41 * (i2 - 1) + 6 * c2 + 2 -> 2 * (si_j I - i2) + 1 <= X ->
  av_KA RT PMc E I K isobj (i2 - 1) (Z.of_nat (length ks)) X bound.
Proof using AV.
  intros d0 ks i2 c2 isobj X bound HF0 HD HL KR HR HI HC HB HX. unfold av_KA.
  intros Σ' st' m' F' fc' xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HSM FRM ACC CR.
  eapply (AV d0 ks i2 c2 isobj Σ' st'); try eassumption; [lia|]. eapply CREDA_le; [exact CR| exact HX].
Qed.

Lemma pa_n_32 : pa_n E + 2 < 2^32.
Proof using OK.
  pose proof (ok_sizes E OK) as [HT _]. pose proof (ok_len E OK) as HL.
  unfold SJ_TAPE, roundup64, sj_cap, SJ_PADMAX in *. Z.div_mod_to_equations. lia.
Qed.

Theorem disp_proofA : disp_stmtA RT PMc E I K D (S fu).
Proof using AF MST OK CX AV OPA OPO PSTR PI64 PU64 PDBL PTRUE PFALSE PNULL.
  unfold disp_stmtA.
  intros d0 ks i i2 c c2 isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HEL HR HI HC HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (c_c' E D I CX) as (CC1 & CC2).
  pose proof (ok_wfS E OK) as WF. pose proof WF as (_ & SN & _).
  pose proof (sctx_out E D I OK CX) as OUTB. pose proof pa_n_32 as N32.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT.
  pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
  pose proof (ser_view_of _ _ _ SN _ _ _ _ _ HEL ltac:(clear - HI; lia) ltac:(clear - LT LEJ J2 N32; lia)) as V.
  assert (WR : 0 <= pa_T E i < 2^64).
  { destruct V as [Hw _ _|Hw _ _|l Hw _ _ _ _|d' e n _ Hw _ _ _ _|d' e n _ Hw _ _ _ _];
      try (destruct Hw as [Hw|[Hw|Hw]]); (eapply ttype_range; [exact Hw|]);
      unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj; clear; lia. }
  set (w := pa_T E i) in *. unfold SjTape.ty in V. fold w in V.
  assert (TYR : 0 <= ttype w < 256) by (unfold ttype; clear - WR; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). unfold PJ_DISP_A.
  destruct HSM as (xv & x224 & HSM).

  zstep. zstep. zstep.
  eapply evt_cut; [eapply (ser_trefA RT AF E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) m i F fc); [exact OK| exact CX| exact HSM| clear - HI LT LEJ J2; lia]|].
  cbv beta. intros ms1 (m1 & ya4 & -> & HSM1). clear HSM. rewrite (ret_pc_even 0xb8f20) by lia.
  ser_open HSM1 OK.
  pose proof (tape_read_mu RT AF E D I OK CX _ _ _ _ i HREF MU WM ltac:(clear - HI LT LEJ J2; lia)) as RDT. fold w in RDT.
  pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_TAPE E + 8 * i) ltac:(clear - HI LT LEJ J2; lia)) as RDW.

  zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_true.

  step. zstep. rewrite ?unsigned_lit by (clear - WR; lia). rewrite shr56_ttype.
  assert (EW : tword (ttype w) (tval w) = w).
  { unfold tword, ttype, tval. pose proof (Z.div_mod w (2^56) ltac:(clear; lia)). clear - H WR. lia. }
  set (t := ttype w) in *.
  remember (41 * (i - 1) + 6 * c + 3) as A eqn:EA.

  assert (VT : boxP ((t = t_true /\ i2 = i + 1 /\ c2 = c) \/ (t = t_false /\ i2 = i + 1 /\ c2 = c) \/ (t = t_null /\ i2 = i + 1 /\ c2 = c)
            \/ (t = t_i64 /\ i2 = i + 2 /\ c2 = c) \/ (t = t_u64 /\ i2 = i + 2 /\ c2 = c) \/ (t = t_dbl /\ i2 = i + 2 /\ c2 = c)
            \/ (t = t_str /\ i2 = i + 1 /\ exists l, tval w = c /\ str_at (pa_S E) (pa_sn E) c l /\ c2 = c + l + 5)
            \/ (t = t_arr /\ exists d' e n, d0 = S d' /\ i2 = e + 1 /\ tnext w = e + 1 /\ ttype (pa_T E e) = t_arr_end
                             /\ tilesS (elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d') (i + 1) e n c c2)
            \/ (t = t_obj /\ exists d' e n, d0 = S d' /\ i2 = e + 1 /\ tnext w = e + 1 /\ ttype (pa_T E e) = t_obj_end
                             /\ tilesS (fieldS (pa_T E) (pa_S E) (pa_sn E) (elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d')) (i + 1) e n c c2))).
  { unfold boxP. destruct V as [Hw Ej Ec|Hw Ej Ec|l Hw Hv Ej Hs Ec|d' e n Ed Hw Ej Hn He Ht|d' e n Ed Hw Ej Hn He Ht].
    - destruct Hw as [Hw|[Hw|Hw]]; [left| right; left| right; right; left]; (split; [exact Hw| split; [exact Ej| exact Ec]]).
    - destruct Hw as [Hw|[Hw|Hw]]; [do 3 right; left| do 4 right; left| do 5 right; left]; (split; [exact Hw| split; [exact Ej| exact Ec]]).
    - do 6 right. left. split; [exact Hw|]. split; [exact Ej|]. exists l. split; [exact Hv|]. split; [exact Hs| exact Ec].
    - do 7 right. left. split; [exact Hw|]. exists d', e, n. split; [exact Ed|]. split; [exact Ej|]. split; [exact Hn|]. split; [exact He| exact Ht].
    - do 8 right. split; [exact Hw|]. exists d', e, n. split; [exact Ed|]. split; [exact Ej|]. split; [exact Hn|]. split; [exact He| exact Ht]. }
  clear V. unfold t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_str, t_arr, t_obj in VT.
  assert (ES : bv_signed (Z_to_bv 64 t) = t) by (apply pj_signed_small; clear - TYR; lia).

  assert (KAV : forall N X', A + N <= 41 * (i2 - 1) + 6 * c2 + 2 -> 2 * (si_j I - i2) + 1 <= X' ->
                av_KA RT PMc E I K isobj (i2 - 1) (Z.of_nat (length ks)) X' (A + N)).
  { intros N X' HB HX. eapply (av_K_ofA d0 ks i2 c2 isobj X' (A + N)); try eassumption; clear - HF0 LT HI CUR HC; lia. }
  Local Ltac clear_disj_but VT := repeat match goal with H : _ \/ _ |- _ => tryif constr_eq H VT then fail else clear H end.
  Local Ltac vt_get VT := unfold boxP in VT; clear_disj_but VT; destruct VT as [V|[V|[V|[V|[V|[V|[V|[V|V]]]]]]]]; destruct V as (V1 & V2); try lia.

  zstep. zstep. pjnorm. lstep.

  zstep. step. if_cases K0; zify_cond K0; rewrite ?ES in K0; pjnorm_in K0.
  -
    zstep. step. if_cases K1; zify_cond K1; rewrite ?ES in K1; pjnorm_in K1.
    +
      zstep. step. if_cases K2; zify_cond K2; pjnorm_in K2.
      *
        assert (EI : t = 100 /\ i2 = i + 2 /\ c2 = c) by vt_get VT. destruct EI as (Et & Ei2 & Ec2).
        pose proof (KAV 27 (2 * (si_j I - i) - 1 - 1) ltac:(clear - Ei2 Ec2 EA; lia) ltac:(clear - Ei2; lia)) as KA.
        replace (i2 - 1) with (i + 1) in KA by (clear - Ei2; lia).
        ser_close HSMC OK CX. apply evt_done. subst t.
        eapply aevt_eq; [| eapply (PDBL E D I K isobj Σ (mkSbA buf size cap hp kk) _ F fc i (Z.of_nat (length ks)) A (2 * (si_j I - i) - 1))];
          [pj_st_eq| exact OK| exact CX| eexists; exact HSMC| exact FRM| exact HI| clear - Ei2 LEJ J2; lia| unfold SjTape.ty; fold w; unfold t_dbl; exact Et
          | clear - HL; lia| cbn [sa_size]; clear - ACC EA; lia| clear - OUTB EA Ei2 Ec2 LEJ LEC CUR HI HC LT; lia| exact CR| clear - LT LEJ Ei2; lia| exact KA].
      *
        step. zstep. step. if_cases K3; zify_cond K3; pjnorm_in K3; [exfalso; vt_get VT|].
        assert (EI : i2 = i + 1 /\ c2 = c) by vt_get VT. destruct EI as (Ei2 & Ec2).
        pose proof (KAV 5 (2 * (si_j I - i) - 1) ltac:(clear - Ei2 Ec2 EA; lia) ltac:(clear - Ei2; lia)) as KA.
        replace (i2 - 1) with i in KA by (clear - Ei2; lia).
        ser_close HSMC OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (PFALSE E D I K isobj Σ (mkSbA buf size cap hp kk) _ F fc i (Z.of_nat (length ks)) A (2 * (si_j I - i) - 1))];
          [pj_st_eq| exact OK| exact CX| eexists; exact HSMC| exact FRM| clear - HL; lia| cbn [sa_size]; clear - ACC EA; lia
          | clear - OUTB EA Ei2 Ec2 LEJ LEC CUR HI HC LT; lia| exact CR| clear - LT LEJ Ei2; lia| exact KA].
    +
      zstep. step. if_cases K2; zify_cond K2; pjnorm_in K2.
      *
        assert (VS : t = 34 /\ i2 = i + 1 /\ exists l, tval w = c /\ str_at (pa_S E) (pa_sn E) c l /\ c2 = c + l + 5) by (vt_get VT; split; [lia| exact V2]).
        destruct VS as (Et & Ej & l & Hv & Hs & Ec). pose proof Hs as (_ & L0 & _).
        pose proof (KAV (2 + 6 * l) (2 * (si_j I - i) - 1) ltac:(clear - Ej Ec EA L0; lia) ltac:(clear - Ej; lia)) as KA.
        replace (i2 - 1) with i in KA by (clear - Ej; lia).
        assert (EWS : w = tword t_str c) by (rewrite <- EW; fold t; rewrite Hv, Et; reflexivity).
        ser_close HSMC OK CX. apply evt_done. subst t.
        eapply aevt_eq; [| eapply (PSTR E D I K isobj Σ (mkSbA buf size cap hp kk) _ F fc i c l (Z.of_nat (length ks)) A (2 * (si_j I - i) - 1))];
          [pj_st_eq| exact OK| exact CX| eexists; exact HSMC| exact FRM| clear - HI LT LEJ J2; lia| unfold w in EWS; exact EWS| exact Hs| clear - HL; lia
          | cbn [sa_size]; clear - ACC EA; lia| clear - OUTB EA Ej Ec LEJ LEC CUR HI HC LT L0; lia| exact CR| clear - LT LEJ Ej; lia| exact KA].
      *
        step. zstep. step. if_cases K3; zify_cond K3; pjnorm_in K3; [exfalso; vt_get VT|].
        zstep. step. if_cases K4; zify_cond K4; pjnorm_in K4; [| exfalso; vt_get VT].
        assert (VA : exists d' e n, d0 = S d' /\ i2 = e + 1 /\ tnext w = e + 1 /\ ttype (pa_T E e) = t_arr_end
                       /\ tilesS (elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d') (i + 1) e n c c2)
          by (vt_get VT; exact V2).
        destruct VA as (d' & e & n & Ed & Ej & Hn & He & Ht). subst d0 i2.
        ser_close HSMC OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (OPA d' ks i e n c c2 isobj Σ (mkSbA buf size cap hp kk) _ F fc)];
          [pj_st_eq| clear - HF0; lia| exact HD| exact HL| exact KR| unfold SjTape.ty; fold w; fold t; unfold t_arr; clear - K4; cbn; lia| exact Hn| exact He
          | unfold itemS; exact Ht| exact HR| exact HI| exact HC| eexists; exact HSMC| exact FRM| cbn [sa_size]; clear - ACC EA; lia| exact CR].
  -
    zstep. step. zstep. step. if_cases K1; zify_cond K1; pjnorm_in K1.
    +
      zstep. step. if_cases K2; zify_cond K2; pjnorm_in K2; [exfalso; vt_get VT|].
      assert (VO : exists d' e n, d0 = S d' /\ i2 = e + 1 /\ tnext w = e + 1 /\ ttype (pa_T E e) = t_obj_end
                     /\ tilesS (fieldS (pa_T E) (pa_S E) (pa_sn E) (elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d')) (i + 1) e n c c2)
        by (vt_get VT; exact V2).
      destruct VO as (d' & e & n & Ed & Ej & Hn & He & Ht). subst d0 i2.
      ser_close HSMC OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (OPO d' ks i e n c c2 isobj Σ (mkSbA buf size cap hp kk) _ F fc)];
        [pj_st_eq| clear - HF0; lia| exact HD| exact HL| exact KR| unfold SjTape.ty; fold w; fold t; unfold t_obj; clear - K2; cbn; lia| exact Hn| exact He
        | unfold itemS; exact Ht| exact HR| exact HI| exact HC| eexists; exact HSMC| exact FRM| cbn [sa_size]; clear - ACC EA; lia| exact CR].
    +
      assert (TJ : boxP ((t = 108 /\ i2 = i + 2 /\ c2 = c) \/ (t = 110 /\ i2 = i + 1 /\ c2 = c) \/ (t = 116 /\ i2 = i + 1 /\ c2 = c) \/ (t = 117 /\ i2 = i + 2 /\ c2 = c)))
        by (unfold boxP; vt_get VT).
      unfold boxP in TJ. destruct TJ as [(Et & Ei2 & Ec2)|[(Et & Ei2 & Ec2)|[(Et & Ei2 & Ec2)|(Et & Ei2 & Ec2)]]]; rewrite Et.
      *
        zstep. zstep. zstep. zstep. step. zstep. zstep.
        pose proof (KAV 20 (2 * (si_j I - i) - 1 - 1) ltac:(clear - Ei2 Ec2 EA; lia) ltac:(clear - Ei2; lia)) as KA.
        replace (i2 - 1) with (i + 1) in KA by (clear - Ei2; lia).
        ser_close HSMC OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (PI64 E D I K isobj Σ (mkSbA buf size cap hp kk) _ F fc i (Z.of_nat (length ks)) A (2 * (si_j I - i) - 1))];
          [pj_st_eq| exact OK| exact CX| eexists; exact HSMC| exact FRM| exact HI| clear - Ei2 LEJ J2; lia| unfold SjTape.ty; fold w; unfold t_i64; exact Et
          | clear - HL; lia| cbn [sa_size]; clear - ACC EA; lia| clear - OUTB EA Ei2 Ec2 LEJ LEC CUR HI HC LT; lia| exact CR| clear - LT LEJ Ei2; lia| exact KA].
      *
        zstep. zstep. zstep. zstep. step. zstep. zstep.
        pose proof (KAV 4 (2 * (si_j I - i) - 1) ltac:(clear - Ei2 Ec2 EA; lia) ltac:(clear - Ei2; lia)) as KA.
        replace (i2 - 1) with i in KA by (clear - Ei2; lia).
        ser_close HSMC OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (PNULL E D I K isobj Σ (mkSbA buf size cap hp kk) _ F fc i (Z.of_nat (length ks)) A (2 * (si_j I - i) - 1))];
          [pj_st_eq| exact OK| exact CX| eexists; exact HSMC| exact FRM| clear - HL; lia| cbn [sa_size]; clear - ACC EA; lia
          | clear - OUTB EA Ei2 Ec2 LEJ LEC CUR HI HC LT; lia| exact CR| clear - LT LEJ Ei2; lia| exact KA].
      *
        zstep. zstep. zstep. zstep. step. zstep. zstep.
        pose proof (KAV 4 (2 * (si_j I - i) - 1) ltac:(clear - Ei2 Ec2 EA; lia) ltac:(clear - Ei2; lia)) as KA.
        replace (i2 - 1) with i in KA by (clear - Ei2; lia).
        ser_close HSMC OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (PTRUE E D I K isobj Σ (mkSbA buf size cap hp kk) _ F fc i (Z.of_nat (length ks)) A (2 * (si_j I - i) - 1))];
          [pj_st_eq| exact OK| exact CX| eexists; exact HSMC| exact FRM| clear - HL; lia| cbn [sa_size]; clear - ACC EA; lia
          | clear - OUTB EA Ei2 Ec2 LEJ LEC CUR HI HC LT; lia| exact CR| clear - LT LEJ Ei2; lia| exact KA].
      *
        zstep. zstep. zstep. zstep. step. zstep. zstep.
        pose proof (KAV 20 (2 * (si_j I - i) - 1 - 1) ltac:(clear - Ei2 Ec2 EA; lia) ltac:(clear - Ei2; lia)) as KA.
        replace (i2 - 1) with (i + 1) in KA by (clear - Ei2; lia).
        ser_close HSMC OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (PU64 E D I K isobj Σ (mkSbA buf size cap hp kk) _ F fc i (Z.of_nat (length ks)) A (2 * (si_j I - i) - 1))];
          [pj_st_eq| exact OK| exact CX| eexists; exact HSMC| exact FRM| exact HI| clear - Ei2 LEJ J2; lia| unfold SjTape.ty; fold w; unfold t_u64; exact Et
          | clear - HL; lia| cbn [sa_size]; clear - ACC EA; lia| clear - OUTB EA Ei2 Ec2 LEJ LEC CUR HI HC LT; lia| exact CR| clear - LT LEJ Ei2; lia| exact KA].
Qed.

End Disp.
