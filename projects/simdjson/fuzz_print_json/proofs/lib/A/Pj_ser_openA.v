(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_dispA Pj_ser_endsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [length sa_buf sa_size sa_cap Z.b2z]; lia]
  | |- _ => reflexivity
  end.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma tnext_back3 : forall w e, tnext w = e + 1 -> 0 <= e -> 0 <= w ->
  Z.land ((w + 4294967295) mod 18446744073709551616) (4294967295 mod 18446744073709551616) = e.
Proof.
  intros w e H He Hw. rewrite (Z.mod_small 4294967295) by lia.
  replace ((w + 4294967295) mod 18446744073709551616) with ((w + 4294967295) + (- ((w + 4294967295) / 18446744073709551616) * 4294967296) * 4294967296)
    by (Z.div_mod_to_equations; lia).
  change 4294967295 with (Z.ones 32) at 3. rewrite Z.land_ones by lia. change (2 ^ 32) with 4294967296. rewrite Z.mod_add by lia.
  pose proof (tnext_back2 w e H He) as T. change 4294967295 with (Z.ones 32) in T at 2. rewrite Z.land_ones in T by lia. exact T.
Qed.

Section Open.
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
Hypothesis AV : aval_stmtA RT PMc E I K D fu.
Hypothesis REC : rec_okA RT PMc D.
Notation aevt := (aevt RT PMc).
Notation RESTA := (rest_ok (pa_T E) (pa_S E) (pa_sn E)).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k Z.b2z]; lia.

Lemma open_pushA : forall (k : bool) (d1 : nat) (ks : list bool) (i i3 c c3 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs8 xs9 xs10 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 1) <= Z.of_nat fu -> (d1 + S (length ks) = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
  itemS (pa_T E) (pa_S E) (pa_sn E) k d1 (i + 1) i3 c c3 -> RESTA d1 (k :: ks) i3 c3 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * i + 6 * c + 2 ->
  CREDA RT E I Σ (2 * (si_j I - (i + 1)) - 1) st ->
  aevt Σ K (LSTA E I 0xb4afc (i + 1) (Z.of_nat (length ks)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) xs8 xs9 xs10 (wz (T5A E))
               xra xt0 xt1 xt2 xa0 xa1 (wz (Z.b2z k)) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF MST OK CX KH.
  intros k d1 ks i i3 c c3 isobj Σ st m F fc xs8 xs9 xs10 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HIT HR HI HC HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (isobj_sh_read _ I (Z.of_nat (length ks) + 1) ((si_f I + 432 + (Z.of_nat (length ks) + 1)) / 8 + 2147450880) SHF Ef ltac:(clear - HL; lia) eq_refl) as RDS.
  pose proof (u8arr_store_ok asegs _ (si_f I + 432) isobj (Z.of_nat (length ks) + 1) (wa (si_f I + 432 + (Z.of_nat (length ks) + 1))) IS ltac:(rewrite ISL; clear - HL; lia) eq_refl) as SOK1.
  pose proof (kinds_rel_push ks isobj k KR ltac:(rewrite ISL; clear - HL; lia)) as KR'.

  step. zstep. zstep. pjnorm. zstep. zstep. shz_norm. step. step. zstep. if_false.

  step. unbox FSB; unbox SHf. step.
  destruct k; unfold kbyte in KR'; cbn [Z.b2z];
    [change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1] | change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]];
    (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ [?b]) _) =>
       pose proof (u8arr_write asegs mm (si_f I + 432) isobj (Z.of_nat (length ks) + 1) b IS ltac:(rewrite ISL; clear - HL; lia)) as IS';
       replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (length ks + 1)%nat in IS' by (clear; lia);
       store_done; box_disj;
       rewrite <- (upd_length isobj (length ks + 1) b) in ISL; try clear IS; rename IS' into IS end);

    zstep; step; (if_cases K9; zify_cond K9; [exfalso; pjnorm_in K9; cbn in K9; clear - K9; lia| clear K9]); step;
    ser_close HSM2 OK CX; apply evt_done.
  - eapply aevt_eq; [| eapply (KH d1 (true :: ks) (i + 1) i3 c c3 false _ Σ (mkSbA buf size cap hp kk))];
      [pj_st_eq| exact HF0| cbn [length]; clear - HD; lia| cbn [length]; clear - HL; lia| exact KR'| exact HIT| exact HR| reflexivity
      | clear - HI; lia| exact HC| exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
  - eapply aevt_eq; [| eapply (KH d1 (false :: ks) (i + 1) i3 c c3 false _ Σ (mkSbA buf size cap hp kk))];
      [pj_st_eq| exact HF0| cbn [length]; clear - HD; lia| cbn [length]; clear - HL; lia| exact KR'| exact HIT| exact HR| reflexivity
      | clear - HI; lia| exact HC| exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
Qed.

Lemma avs_storeA : forall (d0 : nat) (ks : list bool) (i2 c2 bval : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs5 xs8 xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - i2 <= Z.of_nat fu -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  RESTA d0 ks i2 c2 (si_j I) (si_c' I) -> 2 <= i2 -> 0 <= c2 ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= 41 * (i2 - 1) + 6 * c2 + 2 ->
  CREDA RT E I Σ (2 * (si_j I - i2) + 1) st -> 0 <= bval < 256 ->
  aevt Σ K (LSTA E I PJ_AVS_A (i2 - 1) (Z.of_nat (length ks)) (wz (SHDOCA E)) xs5 xs8 (wz (pa_SB E + 80)) (wz (pa_SB E)) (wz (T5A E))
               xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) (wz bval) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF MST OK CX AV.
  intros d0 ks i2 c2 bval isobj Σ st m F fc xs5 xs8 xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HR HI2 HC2 HSM FRM SZ1 ACC CR BV.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. pj_store_done.
  ser_close HSM2 OK CX. apply evt_done.
  eapply (AV d0 ks i2 c2 isobj Σ (mkSbA buf size cap hp kk)); try eassumption. eexists; exact HSM2.
Qed.

Lemma open_emptyA : forall (k : bool) (d1 : nat) (ks : list bool) (i c : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 2) <= Z.of_nat fu -> (d1 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  RESTA d1 ks (i + 2) c (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st + 1 <= 41 * (i + 1) + 6 * c + 2 ->
  CREDA RT E I Σ (2 * (si_j I - (i + 2)) + 1) st ->
  aevt Σ K (MS (mkR xra (wz (si_b I)) (si_gp I) (wz TPV_A) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (wz (Z.of_nat (length ks))) (wz (pa_SB E + 72)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) (wz (i + 1)) (wz 2147450880)
                    (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz ((pa_SB E + 80) / 8 + 2147450880)) (wz ((pa_SB E + 64) / 8 + 2147450880)) (wz (pa_DOC E))
                    xt3 xt4 (wz (T5A E)) xt6)
               F (wz (if k then 0xb3e3c else 0xb4654)) fc None m (seg_rom asegs)).
Proof using AF RC FDO MST GROW OK CX AV.
  intros k d1 ks i c isobj Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HR HI HC HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (sctx_out E D I OK CX) as OUTB.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX.

  assert (JOIN : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E)) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size + 1 -> 0 <= size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - (i + 2)) + 1) st5 ->
    aevt Σ5 K (LSTA E I (if k then 0xb3ec0 else 0xb46d4) (i + 1) (Z.of_nat (length ks)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) (wz ((pa_SB E + 72) / 8 + 2147450880))
                     (wz (pa_SB E + 80)) (wz (pa_SB E)) (wz (T5A E))
                  yra yt0 yt1 yt2 (wz (sa_buf st5 + size)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 x5 F5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HSM5 ESZ SZ0' ROOM CR5.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_cap sa_buf] in ESZ, ROOM |- *. subst size5.
    apply (aevt_evt RT AF PMc MST).

    destruct k; step; step; apply evt_done.
    - eapply aevt_eq; [| eapply (avs_storeA d1 ks (i + 2) c 125 isobj Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; try (eexists; exact HSM5); slia.
    - eapply aevt_eq; [| eapply (avs_storeA d1 ks (i + 2) c 93 isobj Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; try (eexists; exact HSM5); slia. }

  assert (TAIL : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E)) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size -> 0 <= size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - (i + 2)) + 1) st5 ->
    aevt Σ5 K (MS (mkR yra (wz (si_b I)) (si_gp I) (wz TPV_A) yt0 yt1 yt2 (wz (si_q I)) (wz (si_b I)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                      (wz (Z.of_nat (length ks))) (wz (pa_SB E + 72)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) (wz (i + 1)) (wz 2147450880)
                      (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz (pa_SB E + 80)) (wz ((pa_SB E + 64) / 8 + 2147450880)) (wz (pa_DOC E))
                      yt3 yt4 (wz (T5A E)) yt6)
                 F5 (wz (if k then 0xb3e78 else 0xb4690)) fc None m5 (seg_rom asegs))).
  { intros Σ5 st5 m5 x5 F5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HSM5 ESZ SZ0' ROOM CR5.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_cap sa_buf] in ESZ, ROOM |- *. subst size5.
    apply (aevt_evt RT AF PMc MST). ser_open HSM5 OK.
    pose proof (shz_sb_mu RT AF E D I OK CX Σ5 _ _ _ HREF MU WM) as SHZ.
    pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.

    destruct k;
      (zstep; shz_norm; zstep; if_true; zstep; shz_norm; step; zstep; if_true;
       step; step; step; zstep; zstep; unbox FSB; unbox SHSB; step; box_disj;
       lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (acc_buf_mu RT AF E D I OK CX Σ5 _ _ mm HREF MU WM) as ACCB end;
       cbn [sa_buf sa_cap] in ACCB;
       destruct (acc_read1 _ _ _ (buf5 + size) ACCB ltac:(clear - ROOM SZ0'; lia)) as (b & RDB & SOK);
       zstep; pjnorm; zstep; zstep;
       ser_close HSM6 OK CX;
       destruct (pj_sh_ok_cases b (buf5 + size) SOK) as [-> | (kq & -> & K17 & KM)]; [rewrite sxb_z8| rewrite (pj_sxb_small7 kq) by (clear - K17; lia)]).
    -
      zstep. if_true. apply evt_done.
      eapply aevt_eq; [| eapply (JOIN Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc]. step.
      zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ0'; lia). zstep.
      if_cases Kc; zify_cond Kc;
        [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc].
      step. apply evt_done.
      eapply aevt_eq; [| eapply (JOIN Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. if_false. apply evt_done.
      eapply aevt_eq; [| eapply (JOIN Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; slia.
    -
      zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
      zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ0'; lia). zstep.
      if_cases Kc; zify_cond Kc;
        [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
      apply evt_done.
      eapply aevt_eq; [| eapply (JOIN Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; slia. }

  apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.

  destruct k;
    (zstep; shz_norm; zstep; if_true; zstep; shz_norm; step; zstep; if_true;
     step; step; zstep; step; if_cases K2; zify_cond K2; pjnorm_in K2;
     [ ser_close HSM2 OK CX; apply evt_done;
       eapply aevt_eq; [| eapply (TAIL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
     |
       zstep; pjnorm; step; zstep; ser_close HSM3 OK CX; apply evt_done ]).
  - eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - (i + 2)) + 1) 0xb3e74)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - HF0 LEJ; lia| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - K2 ACC OUTB LEJ LEC HI HC. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK.

    step. ser_close HSM5 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA; slia.
  - eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - (i + 2)) + 1) 0xb468c)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - HF0 LEJ; lia| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - K2 ACC OUTB LEJ LEC HI HC. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK.

    step. ser_close HSM5 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA; slia.
Qed.

Lemma open_byteA : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 1) <= Z.of_nat fu -> (S d' + length ks = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
  ty (pa_T E) e = end_ty k -> tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d') (i + 1) e n c c2 ->
  RESTA (S d') ks (e + 1) c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= 41 * (i - 1) + 6 * c + 4 ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (MS (mkR xra (wz (si_b I)) (si_gp I) (wz TPV_A) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I)) (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (wz (Z.of_nat (length ks))) (wz (pa_SB E + 72)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) (wz i) (wz 2147450880)
                    (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz ((pa_SB E + 80) / 8 + 2147450880)) (wz ((pa_SB E + 64) / 8 + 2147450880)) (wz (pa_DOC E))
                    xt3 xt4 (wz (T5A E)) xt6)
               F (wz (if k then 0xb3df8 else 0xb4610)) fc None m (seg_rom asegs)).
Proof using AF RC FDO MST GROW OK CX KH AV.
  intros k d' ks i e n c c2 isobj Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR He Ht HR HI HC HSM FRM SZ1 ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (ok_wfS E OK) as WF. pose proof WF as (_ & SN & _). pose proof (pa_n_32 E OK) as N32.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  pose proof (tilesS_le _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
  pose proof (rest_ok_open (pa_T E) (pa_S E) (pa_sn E) d' ks k i e n c c2 (si_j I) (si_c' I) Ht He HR) as HR'.
  pose proof (rest_ok_word (pa_T E) (pa_S E) (pa_sn E) SN d' k ks (i + 1) c (si_j I) (si_c' I) HR' ltac:(clear - HI; lia) ltac:(clear - J2 N32; lia)) as WR.
  set (t := ttype (pa_T E (i + 1))) in *.
  assert (TYR : 0 <= t < 256) by (unfold t, ttype; clear - WR; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  destruct k; (step; step; pj_store_done;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (doc_cells_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as DOCC;
      pose proof (shz_doc_mu RT AF E D I OK CX _ _ _ mm HREF MU WM (pa_DOC E) ltac:(clear; lia)) as RDD;
      pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ mm HREF MU WM (pa_TAPE E + 8 * (i + 1)) ltac:(clear - HI LIE LEJ J2; lia)) as RDW;
      pose proof (tape_read7_mu RT AF E D I OK CX _ _ _ mm (i + 1) HREF MU WM ltac:(clear - HI LIE LEJ J2; lia) WR) as RD7; fold t in RD7 end;

    zstep; shz_norm; zstep; if_true; step; zstep; zstep; pjnorm; zstep; zstep; pjnorm; zstep; zstep; shz_norm; zstep; if_true;
    zstep; pjnorm; step; ser_close HSM2 OK CX; step; if_cases K1; zify_cond K1; pjnorm_in K1).
  -
    assert (NA : SjTape.ty (pa_T E) (i + 1) <> t_arr_end /\ SjTape.ty (pa_T E) (i + 1) <> t_obj_end).
    { destruct (Z.eq_dec (i + 1) e) as [EE|NE].
      - exfalso. rewrite <- EE in He. unfold SjTape.ty in He. fold t in He. unfold end_ty, t_obj_end, t_arr_end in He. clear - He K1. lia.
      - destruct (tilesS_next _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) true d') _ _ _ _ _ Ht NE) as (i3 & c3 & HIT & LE3 & _).
        eapply (itemS_not_end (pa_T E) (pa_S E) (pa_sn E) SN true d' (i + 1) i3 c c3 HIT); clear - HI LE3 LEJ J2 N32; lia. }
    destruct (rest_ok_item (pa_T E) (pa_S E) (pa_sn E) SN d' true ks (i + 1) c (si_j I) (si_c' I) HR' (proj1 NA) (proj2 NA)) as (i3 & c3 & HIT & HR3).
    step. apply evt_done.
    eapply aevt_eq; [| eapply (open_pushA true d' ks i i3 c c3 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      [clear - HD; lia| eexists; exact HSM2| slia| eapply CREDA_le; [exact CR| clear; lia]].
  -
    assert (HEND : SjTape.ty (pa_T E) (i + 1) = t_arr_end \/ SjTape.ty (pa_T E) (i + 1) = t_obj_end) by (right; unfold SjTape.ty; fold t; unfold t_obj_end; clear - K1; lia).
    pose proof (rest_ok_end (pa_T E) (pa_S E) (pa_sn E) SN d' true ks (i + 1) c (si_j I) (si_c' I) HR' ltac:(clear - HI; lia) ltac:(clear - J2 N32; lia) HEND) as HR2.
    replace (i + 1 + 1) with (i + 2) in HR2 by (clear; lia).
    apply evt_done.
    eapply aevt_eq; [| eapply (open_emptyA true (S d') ks i c isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      [clear - HF0; lia| clear - HL; lia| eexists; exact HSM2| slia| eapply CREDA_le; [exact CR| clear; lia]].
  -
    assert (NA : SjTape.ty (pa_T E) (i + 1) <> t_arr_end /\ SjTape.ty (pa_T E) (i + 1) <> t_obj_end).
    { destruct (Z.eq_dec (i + 1) e) as [EE|NE].
      - exfalso. rewrite <- EE in He. unfold SjTape.ty in He. fold t in He. unfold end_ty, t_obj_end, t_arr_end in He. clear - He K1. lia.
      - destruct (tilesS_next _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) false d') _ _ _ _ _ Ht NE) as (i3 & c3 & HIT & LE3 & _).
        eapply (itemS_not_end (pa_T E) (pa_S E) (pa_sn E) SN false d' (i + 1) i3 c c3 HIT); clear - HI LE3 LEJ J2 N32; lia. }
    destruct (rest_ok_item (pa_T E) (pa_S E) (pa_sn E) SN d' false ks (i + 1) c (si_j I) (si_c' I) HR' (proj1 NA) (proj2 NA)) as (i3 & c3 & HIT & HR3).
    step. step. apply evt_done.
    eapply aevt_eq; [| eapply (open_pushA false d' ks i i3 c c3 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      [clear - HD; lia| eexists; exact HSM2| slia| eapply CREDA_le; [exact CR| clear; lia]].
  -
    assert (HEND : SjTape.ty (pa_T E) (i + 1) = t_arr_end \/ SjTape.ty (pa_T E) (i + 1) = t_obj_end) by (left; unfold SjTape.ty; fold t; unfold t_arr_end; clear - K1; lia).
    pose proof (rest_ok_end (pa_T E) (pa_S E) (pa_sn E) SN d' false ks (i + 1) c (si_j I) (si_c' I) HR' ltac:(clear - HI; lia) ltac:(clear - J2 N32; lia) HEND) as HR2.
    replace (i + 1 + 1) with (i + 2) in HR2 by (clear; lia).
    apply evt_done.
    eapply aevt_eq; [| eapply (open_emptyA false (S d') ks i c isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      [clear - HF0; lia| clear - HL; lia| eexists; exact HSM2| slia| eapply CREDA_le; [exact CR| clear; lia]].
Qed.

Lemma open_midA : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs10 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 1) <= Z.of_nat fu -> (S d' + length ks = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
  ty (pa_T E) e = end_ty k -> tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d') (i + 1) e n c c2 ->
  RESTA (S d') ks (e + 1) c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i - 1) + 6 * c + 3 -> sa_size st + 1 <= sa_cap st ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (MS (mkR xra (wz (si_b I)) (si_gp I) (wz TPV_A) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (wz (Z.of_nat (length ks))) (wz (pa_SB E + 72)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) (wz i) (wz 2147450880)
                    (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz ((pa_SB E + 80) / 8 + 2147450880)) xs10 (wz (pa_DOC E))
                    xt3 xt4 (wz (T5A E)) xt6)
               F (wz (if k then 0xb3dac else 0xb45c8)) fc None m (seg_rom asegs)).
Proof using AF RC FDO MST GROW OK CX KH AV.
  intros k d' ks i e n c c2 isobj Σ st m F fc xs10 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR He Ht HR HI HC HSM FRM ACC ROOM CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHZ.
  pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.

  destruct k;
    (step; zstep; zstep; shz_norm; zstep; if_true; zstep; shz_norm; zstep; if_true;
     step; step; step; zstep; zstep; unbox FSB; unbox SHSB; step; box_disj;
     lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB end;
     cbn [sa_buf sa_cap] in ACCB;
     destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK);
     zstep; pjnorm; zstep; zstep;
     ser_close HSM2 OK CX;
     destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (kq & -> & K17 & KM)]; [rewrite sxb_z8| rewrite (pj_sxb_small7 kq) by (clear - K17; lia)]).
  -
    zstep. if_true. apply evt_done.
    eapply aevt_eq; [| eapply (open_byteA true d' ks i e n c c2 isobj Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; try (eexists; exact HSM2); slia.
  -
    zstep. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc]. step.
    zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia). zstep.
    if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc].
    step. apply evt_done.
    eapply aevt_eq; [| eapply (open_byteA true d' ks i e n c c2 isobj Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; try (eexists; exact HSM2); slia.
  -
    zstep. if_false. apply evt_done.
    eapply aevt_eq; [| eapply (open_byteA false d' ks i e n c c2 isobj Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; try (eexists; exact HSM2); slia.
  -
    zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc K17; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia). zstep.
    if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia].
    apply evt_done.
    eapply aevt_eq; [| eapply (open_byteA false d' ks i e n c c2 isobj Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; try (eexists; exact HSM2); slia.
Qed.

Lemma open_recA : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 1) <= Z.of_nat fu -> (S d' + length ks = D)%nat -> length ks = 15%nat -> kinds_rel ks isobj ->
  ty (pa_T E) i = (if k then t_obj else t_arr) -> tnext (pa_T E i) = e + 1 -> ty (pa_T E) e = end_ty k ->
  tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d') (i + 1) e n c c2 ->
  RESTA (S d') ks (e + 1) c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i - 1) + 6 * c + 3 ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (MS (mkR xra (wz (si_b I)) (si_gp I) (wz TPV_A) xt0 xt1 xt2 (wz (si_q I)) (wz (si_b I)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                    (wz (Z.of_nat (length ks))) (wz (pa_SB E + 72)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) (wz i) (wz 2147450880)
                    (wz PJ_NE_TAB_A) (wz (8 * i)) (wz (pa_SB E)) (wz (pa_DOC E))
                    xt3 xt4 (wz (T5A E)) xt6)
               F (wz (if k then 0xb52d0 else 0xb52bc)) fc None m (seg_rom asegs)).
Proof using AF RC FDO MST GROW OK CX KX KH REC.
  intros k d' ks i e n c c2 isobj Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HTY HNX He Ht HR HI HC HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (c_c' E D I CX) as (CC1 & CC2).
  pose proof (ok_wfS E OK) as WF. pose proof WF as (_ & SN & _). pose proof (pa_n_32 E OK) as N32.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  pose proof (tilesS_le _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
  assert (WR : 0 <= pa_T E i < 2^64).
  { eapply ttype_range; [exact HTY|]. destruct k; unfold t_obj, t_arr; clear; lia. }
  assert (CONT : cont_cpsA RT PMc k d') by (apply REC; clear - HD HL; lia).
  assert (NE : ks <> []) by (intros ->; cbn in HL; clear - HL; lia).
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX.

  assert (KRET : forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
      (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
    frm0 fc' -> SERMC RT E I isobj Σ' st' m' -> sb_accA st' (e + 1) c2 -> CREDA RT E I Σ' (2 * (si_j I - i) - 1 - 2 * (e - i)) st' ->
    aevt Σ' K (MS (mkR yra (wz (si_b I)) (si_gp I) (wz TPV_A) yt0 yt1 yt2 (wz (si_q I)) (wz (si_b I)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                       (wz (Z.of_nat (length ks))) (wz (pa_SB E + 72)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) (wz i) (wz 2147450880)
                       (wz PJ_NE_TAB_A) (wz (8 * i)) (wz (pa_SB E)) (wz (pa_DOC E))
                       yt3 yt4 yt5 yt6)
                  F' (wz 0xb52e0) fc' None m' (seg_rom asegs))).
  { intros Σ' st' m' F' fc' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FRM' HSM' ACC' CR'.
    unfold sb_accA in ACC'. destruct st' as [buf' size' cap' hp' kk']. cbn [sa_size] in ACC'.
    apply (aevt_evt RT AF PMc MST). ser_open HSM' OK.
    pose proof (doc_cells_mu RT AF E D I OK CX _ _ _ _ HREF MU WM) as DOCC.
    pose proof (tape_read_mu RT AF E D I OK CX _ _ _ _ i HREF MU WM ltac:(clear - HI LIE LEJ J2; lia)) as RDT.
    pose proof (shz_doc_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_DOC E) ltac:(clear; lia)) as RDD.
    pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_TAPE E + 8 * i) ltac:(clear - HI LIE LEJ J2; lia)) as RDW.

    zstep. shz_norm. zstep. if_false. step. zstep. zstep. pjnorm. zstep. zstep. shz_norm. step. zstep. if_false.

    step. step. zstep. zstep. unfold MASK32. rewrite (tnext_back3 (pa_T E i) e HNX ltac:(clear - LIE HI; lia) ltac:(clear - WR; lia)). step. step.

    zstep. pjnorm. zstep. zstep.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ends_loopA RT AF RC PMc FDO MST GROW E D I K fu OK CX KX KH ks (S d') (e + 1) c2 isobj Σ' (mkSbA buf' size' cap' hp' kk'))];
      [pj_st_eq| exact NE| clear - HF0 LIE; lia| exact HD| clear - HL; lia| exact KR| exact HR| clear - HI LIE; lia| clear - HC LCC; lia| eexists; exact HSM2| exact FRM'
      | cbn [sa_size]; exact ACC'| eapply CREDA_le; [exact CR'| clear; lia]]. }
  destruct HSM as [x HSM].
  apply (aevt_evt RT AF PMc MST).

  destruct k; (step; step; step; step; apply evt_done).
  - eapply aevt_eq; [| eapply (ser_call_contA RT AF PMc FDO MST true d' E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K i e n c c2 (2 * (si_j I - i) - 1) 0xb52e0)];
      [pj_st_eq| exact CONT| clear - HD HL; lia| exact OK| exact CX| exact HSM| exact FRM| exact HTY| exact HNX| exact He| exact Ht| exact HI| clear - LEJ J2; lia| exact HC
      | clear - LCC LEC CC2; lia| exact ACC| exact CR| clear - LEJ; lia| clear; lia| reflexivity|].
    intros Σ' st' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FRM' HSM' ACC' CR'.
    eapply (KRET Σ' st'); [exact FRM'| eexists; exact HSM'| exact ACC'| exact CR'].
  - eapply aevt_eq; [| eapply (ser_call_contA RT AF PMc FDO MST false d' E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K i e n c c2 (2 * (si_j I - i) - 1) 0xb52cc)];
      [pj_st_eq| exact CONT| clear - HD HL; lia| exact OK| exact CX| exact HSM| exact FRM| exact HTY| exact HNX| exact He| exact Ht| exact HI| clear - LEJ J2; lia| exact HC
      | clear - LCC LEC CC2; lia| exact ACC| exact CR| clear - LEJ; lia| clear; lia| reflexivity|].
    intros Σ' st' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FRM' HSM' ACC' CR'.

    apply (aevt_evt RT AF PMc MST). step. apply evt_done.
    eapply (KRET Σ' st'); [exact FRM'| eexists; exact HSM'| exact ACC'| exact CR'].
Qed.

Theorem open_proofA : forall k, open_stmtA RT PMc E I K D fu k.
Proof using AF RC FDO MST GROW OK CX KX KH AV REC.
  intros k. unfold open_stmtA.
  intros d' ks i e n c c2 isobj Σ st m F fc xs5 xs10 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HTY HNX He Ht HR HI HC HSM FRM ACC CR HS10.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (c_c' E D I CX) as (CC1 & CC2). pose proof (sctx_out E D I OK CX) as OUTB.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  pose proof (tilesS_le _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
  pose proof HSM as HSM0. destruct HSM as [x HSM].
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_cap] in *.
  ser_envA OK CX.

  assert (TAIL : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (ys10 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    (length ks + 1 <= 15)%nat ->
    SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E)) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - i) - 1) st5 ->
    aevt Σ5 K (MS (mkR yra (wz (si_b I)) (si_gp I) (wz TPV_A) yt0 yt1 yt2 (wz (si_q I)) (wz (si_b I)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                      (wz (Z.of_nat (length ks))) (wz (pa_SB E + 72)) (wz (SHDOCA E)) (wz (Z.of_nat (length ks) + 1)) (wz i) (wz 2147450880)
                      (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz ((pa_SB E + 80) / 8 + 2147450880)) ys10 (wz (pa_DOC E))
                      yt3 yt4 (wz (T5A E)) yt6)
                 F5 (wz (if k then 0xb3dac else 0xb45c8)) fc None m5 (seg_rom asegs))).
  { intros Σ5 st5 m5 x5 F5 ys10 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HL1 HSM5 ESZ ROOM5 CR5.
    eapply (open_midA k d' ks i e n c c2 isobj Σ5 st5 m5 F5 fc); try eassumption; [eexists; exact HSM5| clear - ESZ ACC; lia| clear - ESZ ROOM5; lia]. }
  apply (aevt_evt RT AF PMc MST).
  destruct k.
  -
    rewrite (HS10 eq_refl). zstep. step. step.
    if_cases K0; zify_cond K0; pjnorm_in K0.
    +
      ser_open HSM OK.
      pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHZ.
      pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.
      step. zstep. zstep. shz_norm. zstep. if_true. zstep. zstep. shz_norm. zstep. if_true.

      step. step. step. zstep. step.
      if_cases K2; zify_cond K2; pjnorm_in K2.
      * ser_close HSM3 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (TAIL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
      *
        zstep. pjnorm. zstep. zstep.
        ser_close HSM3 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - i) - 1) 0xb3da8)];
          [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - LIE LEJ; lia| clear; lia| reflexivity|].
        { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - K2 ACC OUTB LIE LEJ LEC LCC HI HC. lia. }
        intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
        apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK.

        step. ser_close HSM5 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA; slia.
    +
      step. apply evt_done.
      eapply aevt_eq; [| eapply (open_recA true d' ks i e n c c2 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; first [clear - K0 HL; lia| slia].
  -
    ser_open HSM OK.
    zstep. step. step. step.
    if_cases K0; zify_cond K0; pjnorm_in K0.
    +
      ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (open_recA false d' ks i e n c c2 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; try (eexists; exact HSM2); first [clear - K0 HL; lia| slia].
    +
      pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHZ.
      pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.
      step. zstep. zstep. shz_norm. zstep. if_true. zstep. zstep. shz_norm. zstep. if_true.

      step. step. step. zstep. step.
      if_cases K2; zify_cond K2; pjnorm_in K2.
      * ser_close HSM3 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (TAIL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
      *
        zstep. pjnorm. zstep. zstep.
        ser_close HSM3 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - i) - 1) 0xb45c4)];
          [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - LIE LEJ; lia| clear; lia| reflexivity|].
        { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - K2 ACC OUTB LIE LEJ LEC LCC HI HC. lia. }
        intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
        apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK.

        step. ser_close HSM5 OK CX. apply evt_done.
        eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA; slia.
Qed.

End Open.
