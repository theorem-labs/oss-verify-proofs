(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_dispA.
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
    (xs8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  ks <> [] -> si_j I - i2 <= Z.of_nat fu -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  RESTA d0 ks i2 c2 (si_j I) (si_c' I) -> 1 <= i2 -> 0 <= c2 ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i2 - 1) + 6 * c2 + 2 ->
  CREDA RT E I Σ (2 * (si_j I - i2) + 1) st ->
  aevt Σ K (LSTA E I 0xb9784 i2 (Z.of_nat (length ks)) (wz (SHDOCA E)) (wz (8 * i2)) xs8 (wz (pa_SB E + 80)) (wz (pa_SB E)) (wz (T5A E))
               xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX KX KH.
  induction ks as [|k ks IH]; intros d0 i2 c2 isobj Σ st m F fc xs8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
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

  assert (JOIN : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    (ttype w = t_arr_end \/ ttype w = t_obj_end) ->
    SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E)) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size + 1 -> 0 <= size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - i2) + 1) st5 ->
    aevt Σ5 K (LSTA E I 0xb9878 i2 (Z.succ (Z.of_nat (length ks))) (wz (SHDOCA E)) (wz (8 * i2)) (wz (ttype w)) (wz (pa_SB E + 80)) (wz (pa_SB E)) (wz (T5A E))
                  yra yt0 yt1 yt2 (wz (sa_buf st5 + size)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 x5 F5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HEND HSM5 ESZ SZ0' ROOM CR5.
    pose proof (rest_ok_end _ _ _ SN _ _ _ _ _ _ _ HR ltac:(clear - HI2; lia) ltac:(clear - J2 N32; lia) HEND) as HR'.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_cap sa_buf] in ESZ, ROOM |- *. subst size5.
    apply (aevt_evt RT AF PMc MST). ser_open HSM5 OK.
    pose proof (buf_factsA RT AF E D I Σ5 _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
    pose proof (APB (buf5 + size) ltac:(clear - ROOM SZ0'; lia)) as (A1 & A2 & A3 & A4). clear APB.

    step. pj_store_done. zstep. zstep. zstep. step.
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

  assert (TAIL : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    (ttype w = t_arr_end \/ ttype w = t_obj_end) ->
    SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E)) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size -> 0 <= size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - i2) + 1) st5 ->
    aevt Σ5 K (LSTA E I 0xb9834 i2 (Z.succ (Z.of_nat (length ks))) (wz (SHDOCA E)) (wz (8 * i2)) (wz (ttype w)) (wz (pa_SB E + 80)) (wz (pa_SB E)) (wz (T5A E))
                  yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 x5 F5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HEND HSM5 ESZ SZ0' ROOM CR5.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_cap sa_buf] in ESZ, ROOM |- *. subst size5.
    apply (aevt_evt RT AF PMc MST). ser_open HSM5 OK.
    pose proof (shz_sb_mu RT AF E D I OK CX Σ5 _ _ _ HREF MU WM) as SHZ.
    pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.

    step. zstep. zstep. shz_norm. zstep. if_false. zstep. zstep. shz_norm. zstep. if_false.

    step. step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (acc_buf_mu RT AF E D I OK CX Σ5 _ _ mm HREF MU WM) as ACCB end.
    cbn [sa_buf sa_cap] in ACCB.
    destruct (acc_read1 _ _ _ (buf5 + size) ACCB ltac:(clear - ROOM SZ0'; lia)) as (b & RDB & SOK).

    zstep. pjnorm. zstep. zstep.
    ser_close HSM6 OK CX.
    destruct (pj_sh_ok_cases b (buf5 + size) SOK) as [-> | (kq & -> & K17 & KM)].
    - rewrite sxb_z8. zstep. if_false. apply evt_done.
      eapply aevt_eq; [| eapply (JOIN Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; slia.
    - rewrite (pj_sxb_small7 kq) by (clear - K17; lia). zstep.
      if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].

      zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ0'; lia). zstep.
      if_cases Kc; zify_cond Kc;
        [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
      apply evt_done.
      eapply aevt_eq; [| eapply (JOIN Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; slia. }

  apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (doc_cells_mu RT AF E D I OK CX _ _ _ _ HREF MU WM) as DOCC.
  pose proof (tape_read_mu RT AF E D I OK CX _ _ _ _ i2 HREF MU WM ltac:(clear - HI2 LTJ J2; lia)) as RDT. fold w in RDT.
  pose proof (shz_doc_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_DOC E) ltac:(clear; lia)) as RDD.
  pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_TAPE E + 8 * i2) ltac:(clear - HI2 LTJ J2; lia)) as RDW.
  pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ _ HREF MU WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.

  zstep. shz_norm. zstep. if_false.

  step. zstep. zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false.

  step. zstep. rewrite ?unsigned_lit by (clear - WR; lia). rewrite shr56_ttype. fold w.
  assert (ES : bv_signed (Z_to_bv 64 (ttype w)) = ttype w) by (apply pj_signed_small; clear - TYR; lia).

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (GROWN : forall ya2 : word, (ttype w = t_arr_end \/ ttype w = t_obj_end) -> cap < size + 1 ->
    evt asegs (fun ms' => aevt Σ K ms')
        (LSTA E I 0xb981c i2 (Z.succ (Z.of_nat (length ks))) (wz (SHDOCA E)) (wz (8 * i2)) (wz (ttype w)) (wz (pa_SB E + 80)) (wz (pa_SB E)) (wz (T5A E))
              xra xt0 xt1 xt2 (wz (size + 1)) (wz cap) ya2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc mm)) end.
  { intros ya2 HEND KC.

    zstep. pjnorm. zstep. zstep.
    ser_close HSM3 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - i2) + 1) 0xb9828)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - LTJ; lia| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - KC ACC OUTB LTJ LEC HI2 HC2. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 za2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK.

    step. step.
    ser_close HSM5 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA; slia. }

  step. step. if_cases K1; zify_cond K1; pjnorm_in K1.
  -
    assert (HEND : ttype w = t_arr_end \/ ttype w = t_obj_end) by (right; unfold t_obj_end; clear - K1; lia).
    step. zstep. zstep. shz_norm. zstep. if_false. zstep. zstep. shz_norm. zstep. if_false.

    step. step. zstep. step. if_cases K2; zify_cond K2; pjnorm_in K2.
    +   step.
      ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (TAIL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    + eapply GROWN; [exact HEND| clear - K2; lia].
  -
    step. step. if_cases K3; zify_cond K3; pjnorm_in K3.
    +
      assert (NA : SjTape.ty (pa_T E) i2 <> t_arr_end) by (unfold SjTape.ty, t_arr_end; fold w; clear - K3; lia).
      assert (NO : SjTape.ty (pa_T E) i2 <> t_obj_end) by (unfold SjTape.ty, t_obj_end; fold w; clear - K1; lia).
      destruct (rest_ok_item (pa_T E) (pa_S E) (pa_sn E) SN d0 k ks i2 c2 (si_j I) (si_c' I) HR NA NO) as (i3 & c3 & HIT & HR3).
      step. step. if_cases K9; zify_cond K9; [exfalso; pjnorm_in K9; cbn in K9; clear - K9; lia| clear K9]. step.
      ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (KH d0 (k :: ks) i2 i3 c2 c3 true isobj Σ (mkSbA buf size cap hp kk))];
        [pj_st_eq| clear - HF0; lia| cbn [length]; clear - HD; lia| cbn [length]; clear - HL15; lia| exact KR| exact HIT| exact HR3| discriminate
        | exact HI2| exact HC2| exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| eapply CREDA_le; [exact CR| clear; lia]].
    +
      assert (HEND : ttype w = t_arr_end \/ ttype w = t_obj_end) by (left; unfold t_arr_end; clear - K3; lia).
      step. zstep. zstep. shz_norm. zstep. if_false. zstep. zstep. shz_norm. zstep. if_false.
      step. step. zstep. step. if_cases K2; zify_cond K2; pjnorm_in K2.
      * eapply GROWN; [exact HEND| clear - K2; lia].
      *   step. step.
        ser_close HSM2 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (TAIL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Theorem aval_proofA : aval_stmtA RT PMc E I K D fu.
Proof using AF RC FDO MST GROW OK CX KX KH.
  unfold aval_stmtA.
  intros d0 ks i2 c2 isobj Σ st m F fc xs5 xs8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL15 KR HR HI2 HC2 HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2).
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST).
  destruct ks as [|k ks].
  -
    cbn [length] in *. step. if_cases K9; zify_cond K9; [clear K9| exfalso; pjnorm_in K9; cbn in K9; clear - K9; lia]. apply evt_done.
    destruct (rest_ok_nil_inv _ _ _ _ _ _ _ _ HR) as [EJ EC].
    eapply (KX isobj Σ (mkSbA buf size cap hp kk)); [exact HSM| exact FRM| cbn [sa_size]; clear - ACC EJ EC; lia| eapply CREDA_le; [exact CR| clear - EJ; lia]].
  -
    pose proof (rest_ok_lt _ _ _ _ _ _ _ _ _ _ HR) as LTJ.
    cbn [length] in *. step. if_cases K9; zify_cond K9; [exfalso; pjnorm_in K9; cbn in K9; clear - K9; lia| clear K9].
    zstep. pjnorm. zstep. zstep. apply evt_done.
    eapply aevt_eq; [| eapply (ends_loopA (k :: ks) d0 i2 c2 isobj Σ (mkSbA buf size cap hp kk))];
      [pj_st_eq| discriminate| exact HF0| exact HD| exact HL15| exact KR| exact HR| clear - HI2; lia| exact HC2| exact HSM| exact FRM| exact ACC| exact CR].
Qed.

End Ends.
