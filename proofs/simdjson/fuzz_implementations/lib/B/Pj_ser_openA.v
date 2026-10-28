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
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA
     Pj_ser_dispA Pj_ser_endsA.
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

Lemma tnext_pred_mod : forall w e, tnext w = e + 1 -> 0 <= e -> 0 <= w < 2^64 ->
  ((w + -1) mod 18446744073709551616) mod 4294967296 = e.
Proof.
  intros w e H He Hw. unfold tnext in H. change (2 ^ 32) with 4294967296 in H. change (2 ^ 64) with 18446744073709551616 in Hw.
  rewrite (Z.mod_small (w + -1)) by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

Notation MSTA E I pc i dp xs3 xs4 xs5 xs7 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 (pa_SB E + 72)) xs3 xs4 xs5 (Z_to_bv 64 i) xs7 (Z_to_bv 64 (pa_SB E)) (Z_to_bv 64 2147450880)
        (Z_to_bv 64 dp) (Z_to_bv 64 (pa_DOC E))
        xt3 xt4 xt5 xt6 F fc m).
Notation SH64 E := ((pa_SB E + 64) / 8 + 2147450880).
Notation SH72 E := ((pa_SB E + 72) / 8 + 2147450880).
Notation SH80 E := ((pa_SB E + 80) / 8 + 2147450880).

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
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 1) <= Z.of_nat fu -> (d1 + S (length ks) = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
  itemS (pa_T E) (pa_S E) (pa_sn E) k d1 (i + 1) i3 c c3 -> RESTA d1 (k :: ks) i3 c3 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * i + 6 * c + 2 ->
  CREDA RT E I Σ (2 * (si_j I - (i + 1)) - 1) st ->
  aevt Σ K (MSTA E I (if k then 0xba0fc else 0xba0b8) (i + 1) (Z.of_nat (length ks)) xs3 (wz (SH72 E)) (wz (SH80 E)) (wz (SH64 E)) xt5
               xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF MST OK CX KH.
  intros k d1 ks i i3 c c3 isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HIT HR HI HC HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (isobj_sh_read _ I (Z.of_nat (length ks) + 1) ((si_f I + 304 + (Z.of_nat (length ks) + 1)) / 8 + 2147450880) SHF Ef ltac:(clear - HL; lia) eq_refl) as RDS.
  pose proof (u8arr_store_ok bsegs _ (si_f I + 304) isobj (Z.of_nat (length ks) + 1) (wa (si_f I + 304 + (Z.of_nat (length ks) + 1))) IS ltac:(rewrite ISL; clear - HL; lia) eq_refl) as SOK1.
  pose proof (kinds_rel_push ks isobj k KR ltac:(rewrite ISL; clear - HL; lia)) as KR'.

  destruct k; (step; step; step; unfold lnotw; step;
    (if_cases Kc; zify_cond Kc; [exfalso; unfold Z.lnot in Kc; clear - Kc HL F0 FLO LQ QT; Z.div_mod_to_equations; lia| clear Kc]);
    zstep; pjnorm;

    step; zstep; zstep; pjnorm; zstep; zstep; shz_norm; zstep; if_false).
  -
    zstep. zstep. unbox FSB; unbox SHf. step. change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ [?b]) _) =>
       pose proof (u8arr_write bsegs mm (si_f I + 304) isobj (Z.of_nat (length ks) + 1) b IS ltac:(rewrite ISL; clear - HL; lia)) as IS';
       replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (length ks + 1)%nat in IS' by (clear; lia);
       store_done; box_disj;
       rewrite <- (upd_length isobj (length ks + 1) b) in ISL; try clear IS; rename IS' into IS end.
    unfold kbyte in KR'.

    step. step. step.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (KH d1 (true :: ks) (i + 1) i3 c c3 false _ Σ (mkSbA buf size cap hp kk))];
      [pj_st_eq| exact HF0| cbn [length]; clear - HD; lia| cbn [length]; clear - HL; lia| exact KR'| exact HIT| exact HR| reflexivity
      | clear - HI; lia| exact HC| exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
  -
    zstep. unbox FSB; unbox SHf. step. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ [?b]) _) =>
       pose proof (u8arr_write bsegs mm (si_f I + 304) isobj (Z.of_nat (length ks) + 1) b IS ltac:(rewrite ISL; clear - HL; lia)) as IS';
       replace (Z.to_nat (Z.of_nat (length ks) + 1)) with (length ks + 1)%nat in IS' by (clear; lia);
       store_done; box_disj;
       rewrite <- (upd_length isobj (length ks + 1) b) in ISL; try clear IS; rename IS' into IS end.
    unfold kbyte in KR'.
    step.

    step. step. step.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (KH d1 (false :: ks) (i + 1) i3 c c3 false _ Σ (mkSbA buf size cap hp kk))];
      [pj_st_eq| exact HF0| cbn [length]; clear - HD; lia| cbn [length]; clear - HL; lia| exact KR'| exact HIT| exact HR| reflexivity
      | clear - HI; lia| exact HC| exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
Qed.

Lemma avs_storeA : forall (d0 : nat) (ks : list bool) (i2 c2 bval : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - i2 <= Z.of_nat fu -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  RESTA d0 ks i2 c2 (si_j I) (si_c' I) -> 2 <= i2 -> 0 <= c2 ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= 41 * (i2 - 1) + 6 * c2 + 2 ->
  CREDA RT E I Σ (2 * (si_j I - i2) + 1) st -> 0 <= bval < 256 ->
  aevt Σ K (LSTA E I PJ_AVS_A (i2 - 1) (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) xt5
               xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) (wz bval) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF MST OK CX AV.
  intros d0 ks i2 c2 bval isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HR HI2 HC2 HSM FRM SZ1 ACC CR BV.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. unfold PJ_AVS_A.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. pj_store_done.
  ser_close HSM2 OK CX. apply evt_done.
  eapply (AV d0 ks i2 c2 isobj Σ (mkSbA buf size cap hp kk)); try eassumption. eexists; exact HSM2.
Qed.

Lemma open_emptyA : forall (k : bool) (d1 : nat) (ks : list bool) (i c : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 2) <= Z.of_nat fu -> (d1 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  RESTA d1 ks (i + 2) c (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st + 1 <= 41 * (i + 1) + 6 * c + 2 ->
  CREDA RT E I Σ (2 * (si_j I - (i + 2)) + 1) st ->
  aevt Σ K (MSTA E I (if k then 0xb9470 else 0xb91b8) (i + 1) (Z.of_nat (length ks)) xs3 (wz (SH72 E)) (wz (SH80 E)) (wz (SH64 E)) xt5
               xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX AV.
  intros k d1 ks i c isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HR HI HC HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (sctx_out E D I OK CX) as OUTB.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX.

  assert (JOIN : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (yt5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    SERMA RT E I (wkC E) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size + 1 -> 0 <= size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - (i + 2)) + 1) st5 ->
    aevt Σ5 K (LSTA E I (if k then 0xb9518 else 0xb9260) (i + 1) (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) yt5
                  yra yt0 yt1 yt2 (wz (sa_buf st5 + size)) ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 x5 F5 yt5 yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HSM5 ESZ SZ0' ROOM CR5.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_cap sa_buf] in ESZ, ROOM |- *. subst size5.
    apply (aevt_evt RT AF PMc MST).

    destruct k; zstep; step; apply evt_done.
    - eapply aevt_eq; [| eapply (avs_storeA d1 ks (i + 2) c 125 isobj Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; try (eexists; exact HSM5); slia.
    - eapply aevt_eq; [| eapply (avs_storeA d1 ks (i + 2) c 93 isobj Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; try (eexists; exact HSM5); slia. }

  assert (TAIL : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (yt5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    SERMA RT E I (wkC E) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size -> 0 <= size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - (i + 2)) + 1) st5 ->
    aevt Σ5 K (MSTA E I (if k then 0xb94ac else 0xb91f4) (i + 1) (Z.of_nat (length ks)) xs3 (wz (SH72 E)) (wz (SHFA I)) (wz (SH64 E)) yt5
                  yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 x5 F5 yt5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HSM5 ESZ SZ0' ROOM CR5.
    destruct st5 as [buf5 size5 cap5 hp5 kk5]. cbn [sa_size sa_cap sa_buf] in ESZ, ROOM |- *. subst size5.
    apply (aevt_evt RT AF PMc MST). ser_open HSM5 OK.
    pose proof (shz_sb_mu RT AF E D I OK CX Σ5 _ _ _ HREF MU WM) as SHZ.
    pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

    destruct k.
    all: zstep; shz_norm; zstep; if_true; zstep; shz_norm; step; zstep; if_true; clear RD64 RD72.
    all: step; step; step; zstep; zstep; unbox FSB; unbox SHSB; step; box_disj.

    all: step; if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc SZ0' R0 BL LO; lia].
    all: zstep; zstep; zstep;
         replace (0 <? buf5) with true by (symmetry; apply Z.ltb_lt; clear - R0; lia);
         replace (buf5 + size <? 1) with false by (symmetry; apply Z.ltb_ge; clear - R0 SZ0'; lia);
         cbn [Z.b2z Z.lxor]; zstep; if_true.
    all: zstep; if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc R0; lia].

    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (acc_buf_mu RT AF E D I OK CX Σ5 _ _ mm HREF MU WM) as ACCB end;
         cbn [sa_buf sa_cap] in ACCB;
         destruct (acc_read1 _ _ _ (buf5 + size) ACCB ltac:(clear - ROOM SZ0'; lia)) as (b & RDB & SOK); clear ACCB.
    all: zstep; pjnorm; zstep; zstep; clear RDB.
    all: ser_close HSM6 OK CX.
    all: destruct (pj_sh_ok_cases b (buf5 + size) SOK) as [-> | (kq & -> & K17 & KM)];
       [ rewrite sxb_z8; zstep; if_true
       | rewrite (pj_sxb_small7 kq) by (clear - K17; lia); zstep;
         (if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc]); step;
         zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ0'; lia); zstep;
         (if_cases Kc; zify_cond Kc;
           [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc]); step ].
    all: apply evt_done.
    all: eapply aevt_eq; [| eapply (JOIN Σ5 (mkSbA buf5 (size + 1) cap5 hp5 kk5))]; try eassumption; try pj_st_eq; slia. }

  apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHZ.
  pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  destruct k.
  all: zstep; shz_norm; zstep; if_true; zstep; shz_norm; zstep; if_true; clear RD80 RD72.
  all: step; step; step; zstep; step; step; if_cases K2; zify_cond K2; pjnorm_in K2;
     [ ser_close HSM2 OK CX; apply evt_done;
       eapply aevt_eq; [| eapply (TAIL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia
     |
       zstep; pjnorm; zstep; zstep; ser_close HSM3 OK CX; apply evt_done ].
  - eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - (i + 2)) + 1) 0xb94ac)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - HF0 LEJ; lia| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - K2 ACC OUTB LEJ LEC HI HC. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA; slia.
  - eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - (i + 2)) + 1) 0xb91f4)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - HF0 LEJ; lia| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - K2 ACC OUTB LEJ LEC HI HC. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA; slia.
Qed.

Lemma open_byteA : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 1) <= Z.of_nat fu -> (S d' + length ks = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
  ty (pa_T E) e = end_ty k -> tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d') (i + 1) e n c c2 ->
  RESTA (S d') ks (e + 1) c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> 1 <= sa_size st -> sa_size st <= 41 * (i - 1) + 6 * c + 4 ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (MSTA E I (if k then 0xb9430 else 0xb9178) i (Z.of_nat (length ks)) xs3 (wz (SH72 E)) (wz (SH80 E)) (wz (SH64 E)) xt5
               xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX KH AV.
  intros k d' ks i e n c c2 isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR He Ht HR HI HC HSM FRM SZ1 ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (ok_wfS E OK) as WF. pose proof WF as (_ & SN & _). pose proof (pa_n_32 E OK) as N32.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  pose proof (tilesS_le _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
  pose proof (rest_ok_open (pa_T E) (pa_S E) (pa_sn E) d' ks k i e n c c2 (si_j I) (si_c' I) Ht He HR) as HR'.
  pose proof (rest_ok_word (pa_T E) (pa_S E) (pa_sn E) SN d' k ks (i + 1) c (si_j I) (si_c' I) HR' ltac:(clear - HI; lia) ltac:(clear - J2 N32; lia)) as WR.
  set (w := pa_T E (i + 1)) in *.
  assert (TYR : 0 <= ttype w < 256) by (unfold ttype; clear - WR; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST).
  destruct HSM as [xv HSM]. ser_open HSM OK.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  destruct k; (zstep; step; pj_store_done; ser_close HSM2 OK CX; zstep; zstep; zstep; zstep;
    (eapply evt_cut; [eapply (ser_trefA RT AF E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ (i + 1) F fc);
      [exact OK| exact CX| exact HSM2| clear - HI LIE LEJ J2; lia]|]);
    cbv beta; intros ms1 (m1 & ya4 & -> & HSM3); clear HSM2; ser_open HSM3 OK;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (tape_read_mu RT AF E D I OK CX _ _ _ mm (i + 1) HREF MU WM ltac:(clear - HI LIE LEJ J2; lia)) as RDT; fold w in RDT;
      pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ mm HREF MU WM (pa_TAPE E + 8 * (i + 1)) ltac:(clear - HI LIE LEJ J2; lia)) as RDW end).
  1: rewrite (ret_pc_even 0xb9448) by lia.
  2: rewrite (ret_pc_even 0xb9190) by lia.

  all: zstep; pjnorm; zstep; zstep; shz_norm; zstep; if_true; clear RDW;
       step; rewrite ?unsigned_lit by (clear - WR; lia); clear RDT; step;
       zstep; unfold TOPMASK; change ((255 * 2 ^ 56) mod 18446744073709551616) with 18374686479671623680; rewrite (land_topmask w) by (clear - WR; lia);
       step; ser_close HSM4 OK CX; step; if_cases K1; zify_cond K1; unfold END125, END93 in K1; pjnorm_in K1.
  -
    assert (NA : SjTape.ty (pa_T E) (i + 1) <> t_arr_end /\ SjTape.ty (pa_T E) (i + 1) <> t_obj_end).
    { destruct (Z.eq_dec (i + 1) e) as [EE|NE].
      - exfalso. rewrite <- EE in He. unfold SjTape.ty in He. fold w in He. unfold end_ty, t_obj_end, t_arr_end in He. clear - He K1. lia.
      - destruct (tilesS_next _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) true d') _ _ _ _ _ Ht NE) as (i3 & c3 & HIT & LE3 & _).
        eapply (itemS_not_end (pa_T E) (pa_S E) (pa_sn E) SN true d' (i + 1) i3 c c3 HIT); clear - HI LE3 LEJ J2 N32; lia. }
    destruct (rest_ok_item (pa_T E) (pa_S E) (pa_sn E) SN d' true ks (i + 1) c (si_j I) (si_c' I) HR' (proj1 NA) (proj2 NA)) as (i3 & c3 & HIT & HR3).
    apply evt_done.
    eapply aevt_eq; [| eapply (open_pushA true d' ks i i3 c c3 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      [clear - HD; lia| eexists; exact HSM4| slia| eapply CREDA_le; [exact CR| clear; lia]].
  -
    assert (HEND : SjTape.ty (pa_T E) (i + 1) = t_arr_end \/ SjTape.ty (pa_T E) (i + 1) = t_obj_end) by (right; unfold SjTape.ty; fold w; unfold t_obj_end; clear - K1; lia).
    pose proof (rest_ok_end (pa_T E) (pa_S E) (pa_sn E) SN d' true ks (i + 1) c (si_j I) (si_c' I) HR' ltac:(clear - HI; lia) ltac:(clear - J2 N32; lia) HEND) as HR2.
    replace (i + 1 + 1) with (i + 2) in HR2 by (clear; lia).
    apply evt_done.
    eapply aevt_eq; [| eapply (open_emptyA true (S d') ks i c isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      [clear - HF0; lia| clear - HL; lia| eexists; exact HSM4| slia| eapply CREDA_le; [exact CR| clear; lia]].
  -
    assert (NA : SjTape.ty (pa_T E) (i + 1) <> t_arr_end /\ SjTape.ty (pa_T E) (i + 1) <> t_obj_end).
    { destruct (Z.eq_dec (i + 1) e) as [EE|NE].
      - exfalso. rewrite <- EE in He. unfold SjTape.ty in He. fold w in He. unfold end_ty, t_obj_end, t_arr_end in He. clear - He K1. lia.
      - destruct (tilesS_next _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) false d') _ _ _ _ _ Ht NE) as (i3 & c3 & HIT & LE3 & _).
        eapply (itemS_not_end (pa_T E) (pa_S E) (pa_sn E) SN false d' (i + 1) i3 c c3 HIT); clear - HI LE3 LEJ J2 N32; lia. }
    destruct (rest_ok_item (pa_T E) (pa_S E) (pa_sn E) SN d' false ks (i + 1) c (si_j I) (si_c' I) HR' (proj1 NA) (proj2 NA)) as (i3 & c3 & HIT & HR3).
    apply evt_done.
    eapply aevt_eq; [| eapply (open_pushA false d' ks i i3 c c3 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      [clear - HD; lia| eexists; exact HSM4| slia| eapply CREDA_le; [exact CR| clear; lia]].
  -
    assert (HEND : SjTape.ty (pa_T E) (i + 1) = t_arr_end \/ SjTape.ty (pa_T E) (i + 1) = t_obj_end) by (left; unfold SjTape.ty; fold w; unfold t_arr_end; clear - K1; lia).
    pose proof (rest_ok_end (pa_T E) (pa_S E) (pa_sn E) SN d' false ks (i + 1) c (si_j I) (si_c' I) HR' ltac:(clear - HI; lia) ltac:(clear - J2 N32; lia) HEND) as HR2.
    replace (i + 1 + 1) with (i + 2) in HR2 by (clear; lia).
    apply evt_done.
    eapply aevt_eq; [| eapply (open_emptyA false (S d') ks i c isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      [clear - HF0; lia| clear - HL; lia| eexists; exact HSM4| slia| eapply CREDA_le; [exact CR| clear; lia]].
Qed.

Lemma open_midA : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 1) <= Z.of_nat fu -> (S d' + length ks = D)%nat -> (length ks + 1 <= 15)%nat -> kinds_rel ks isobj ->
  ty (pa_T E) e = end_ty k -> tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d') (i + 1) e n c c2 ->
  RESTA (S d') ks (e + 1) c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i - 1) + 6 * c + 3 -> sa_size st + 1 <= sa_cap st ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (MSTA E I (if k then 0xb93c0 else 0xb9108) i (Z.of_nat (length ks)) xs3 (wz (SH72 E)) (wz (SH80 E)) (wz (pa_SB E + 80)) xt5
               xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX KH AV.
  intros k d' ks i e n c c2 isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR He Ht HR HI HC HSM FRM ACC ROOM CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHZ.
  pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72. clear SHZ.

  destruct k;
    (step; zstep; zstep; shz_norm; zstep; if_true; zstep; shz_norm; zstep; if_true; clear RD64 RD72;
     step; step; step; zstep; zstep; unbox FSB; unbox SHSB; step; box_disj;
     step; (if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc SZ R0 BL LO; lia]);
     zstep; zstep; zstep;
     replace (0 <? buf) with true by (symmetry; apply Z.ltb_lt; clear - R0; lia);
     replace (buf + size <? 1) with false by (symmetry; apply Z.ltb_ge; clear - R0 SZ; lia);
     cbn [Z.b2z Z.lxor]; zstep; if_true;
     zstep; (if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc R0; lia]);
     lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB end;
     cbn [sa_buf sa_cap] in ACCB;
     destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK); clear ACCB;
     zstep; pjnorm; zstep; zstep; clear RDB;
     ser_close HSM2 OK CX;
     destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (kq & -> & K17 & KM)];
     [
       rewrite sxb_z8; zstep; if_true
     |
       rewrite (pj_sxb_small7 kq) by (clear - K17; lia); zstep;
       (if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc]); step;
       zstep; pjnorm; rewrite pj_land7 by (clear - R0 SZ; lia); zstep;
       (if_cases Kc; zify_cond Kc;
         [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc]); step ];
     apply evt_done).
  1,2: eapply aevt_eq; [| eapply (open_byteA true d' ks i e n c c2 isobj Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; try (eexists; exact HSM2); slia.
  all: eapply aevt_eq; [| eapply (open_byteA false d' ks i e n c c2 isobj Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; try (eexists; exact HSM2); slia.
Qed.

Lemma open_recA : forall (k : bool) (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32)
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - (i + 1) <= Z.of_nat fu -> (S d' + length ks = D)%nat -> length ks = 15%nat -> kinds_rel ks isobj ->
  ty (pa_T E) i = (if k then t_obj else t_arr) -> tnext (pa_T E i) = e + 1 -> ty (pa_T E) e = end_ty k ->
  tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d') (i + 1) e n c c2 ->
  RESTA (S d') ks (e + 1) c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i - 1) + 6 * c + 3 ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (LSTA E I (if k then 0xba8cc else 0xba8b8) i (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) xt5
               xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW OK CX KX KH REC.
  intros k d' ks i e n c c2 isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
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
    aevt Σ' K (LSTA E I 0xba8dc i (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) yt5
                   yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F' fc' m')).
  { intros Σ' st' m' F' fc' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FRM' HSM' ACC' CR'.
    unfold sb_accA in ACC'. destruct st' as [buf' size' cap' hp' kk']. cbn [sa_size] in ACC'.
    apply (aevt_evt RT AF PMc MST). destruct HSM' as [x' HSM'].

    zstep. zstep. zstep.
    eapply evt_cut; [eapply (ser_trefA RT AF E D I _ _ _ isobj Σ' (mkSbA buf' size' cap' hp' kk') m' i F' fc');
      [exact OK| exact CX| exact HSM'| clear - HI LIE LEJ J2; lia]|].
    cbv beta. intros ms1 (m1 & za4 & -> & HSM1). clear HSM'. rewrite (ret_pc_even 0xba8e8) by lia.
    ser_open HSM1 OK.
    pose proof (tape_read_mu RT AF E D I OK CX _ _ _ _ i HREF MU WM ltac:(clear - HI LIE LEJ J2; lia)) as RDT.
    pose proof (shz_tape_mu RT AF E D I OK CX _ _ _ _ HREF MU WM (pa_TAPE E + 8 * i) ltac:(clear - HI LIE LEJ J2; lia)) as RDW.

    zstep. pjnorm. zstep. zstep. shz_norm. zstep. if_false. clear RDW.

    step. rewrite ?unsigned_lit by (clear - WR; lia). clear RDT. zstep. zstep. zstep.
    rewrite (tnext_pred_mod (pa_T E i) e HNX ltac:(clear - LIE HI; lia) WR).
    step. zstep.
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (ends_loopA RT AF RC PMc FDO MST GROW E D I K fu OK CX KX KH ks (S d') (e + 1) c2 isobj Σ' (mkSbA buf' size' cap' hp' kk'))];
      [pj_st_eq| exact NE| clear - HF0 LIE; lia| exact HD| clear - HL; lia| exact KR| exact HR| clear - HI LIE; lia| clear - HC LCC; lia| eexists; exact HSM2| exact FRM'
      | cbn [sa_size]; exact ACC'| eapply CREDA_le; [exact CR'| clear; lia]]. }
  destruct HSM as [x HSM].
  apply (aevt_evt RT AF PMc MST).

  destruct k; (zstep; zstep; zstep; step; apply evt_done).
  - eapply aevt_eq; [| eapply (ser_call_contA RT AF PMc FDO MST true d' E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K i e n c c2 (2 * (si_j I - i) - 1) 0xba8dc)];
      [pj_st_eq| exact CONT| clear - HD HL; lia| exact OK| exact CX| exact HSM| exact FRM| exact HTY| exact HNX| exact He| exact Ht| exact HI| clear - LEJ J2; lia| exact HC
      | clear - LCC LEC CC2; lia| exact ACC| exact CR| clear - LEJ; lia| clear; lia| reflexivity|].
    intros Σ' st' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FRM' HSM' ACC' CR'.
    eapply aevt_eq; [| eapply (KRET Σ' st'); [exact FRM'| eexists; exact HSM'| exact ACC'| exact CR']]. pj_st_eq.
  - eapply aevt_eq; [| eapply (ser_call_contA RT AF PMc FDO MST false d' E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K i e n c c2 (2 * (si_j I - i) - 1) 0xba8c8)];
      [pj_st_eq| exact CONT| clear - HD HL; lia| exact OK| exact CX| exact HSM| exact FRM| exact HTY| exact HNX| exact He| exact Ht| exact HI| clear - LEJ J2; lia| exact HC
      | clear - LCC LEC CC2; lia| exact ACC| exact CR| clear - LEJ; lia| clear; lia| reflexivity|].
    intros Σ' st' m' F' fc' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 FRM' HSM' ACC' CR'.

    apply (aevt_evt RT AF PMc MST). step. apply evt_done.
    eapply aevt_eq; [| eapply (KRET Σ' st'); [exact FRM'| eexists; exact HSM'| exact ACC'| exact CR']]. pj_st_eq.
Qed.

Theorem open_proofA : forall k, open_stmtA RT PMc E I K D fu k.
Proof using AF RC FDO MST GROW OK CX KX KH AV REC.
  intros k. unfold open_stmtA.
  intros d' ks i e n c c2 isobj Σ st m F fc xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HTY HNX He Ht HR HI HC HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (c_c' E D I CX) as (CC1 & CC2). pose proof (sctx_out E D I OK CX) as OUTB.
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  pose proof (tilesS_le _ (itemS_lt (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LIE & _).
  pose proof (tilesS_cur _ (pa_sn E) (itemS_cur (pa_T E) (pa_S E) (pa_sn E) k d') _ _ _ _ _ Ht) as (LCC & _).
  pose proof HSM as HSM0. destruct HSM as [x HSM].
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_cap] in *.
  ser_envA OK CX. unfold PJ_OBJ_A, PJ_ARR_A.

  assert (TAIL : forall (Σ5 : rts RT) (st5 : sbA) (m5 : mem) (x5 : xjA) (F5 : bvmap 5 word) (yt5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 : word),
    (length ks + 1 <= 15)%nat ->
    SERMA RT E I (wkC E) x5 ser_shpatA isobj Σ5 st5 m5 ->
    sa_size st5 = size -> size + 1 <= sa_cap st5 -> CREDA RT E I Σ5 (2 * (si_j I - i) - 1) st5 ->
    aevt Σ5 K (MSTA E I (if k then 0xb93c0 else 0xb9108) i (Z.of_nat (length ks)) xs3 (wz (SH72 E)) (wz (SH80 E)) (wz (pa_SB E + 80)) yt5
                  yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 F5 fc m5)).
  { intros Σ5 st5 m5 x5 F5 yt5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HL1 HSM5 ESZ ROOM5 CR5.
    eapply (open_midA k d' ks i e n c c2 isobj Σ5 st5 m5 F5 fc); try eassumption; [eexists; exact HSM5| clear - ESZ ACC; lia| clear - ESZ ROOM5; lia]. }
  apply (aevt_evt RT AF PMc MST).

  destruct k; zstep; step; if_cases K0; zify_cond K0; pjnorm_in K0;
    [ |   step; apply evt_done;
        eapply aevt_eq; [| eapply (open_recA true d' ks i e n c c2 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; first [cbn in K0; clear - K0 HL; lia| slia]
      | | step; apply evt_done;
        eapply aevt_eq; [| eapply (open_recA false d' ks i e n c c2 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; first [cbn in K0; clear - K0 HL; lia| slia] ].

  all: ser_open HSM OK;
       pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHZ;
       pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80; pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72; clear SHZ;
       step; zstep; zstep; shz_norm; zstep; if_true; step; zstep; zstep; shz_norm; zstep; if_true; clear RD80 RD72;
       step; step; zstep; step; if_cases K2; zify_cond K2; pjnorm_in K2;
       [ ser_close HSM3 OK CX; apply evt_done;
         eapply aevt_eq; [| eapply (TAIL Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; first [cbn in K0; clear - K0 HL; lia| slia]
       | zstep; pjnorm; zstep; zstep; ser_close HSM3 OK CX; apply evt_done ].
  - eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - i) - 1) 0xb93c0)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - LIE LEJ; lia| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - K2 ACC OUTB LIE LEJ LEC LCC HI HC. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA;
      first [cbn in K0; clear - K0 HL; lia| slia].
  - eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - i) - 1) 0xb9108)];
      [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - LIE LEJ; lia| clear; lia| reflexivity|].
    { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - K2 ACC OUTB LIE LEJ LEC LCC HI HC. lia. }
    intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
    eapply aevt_eq; [| eapply (TAIL Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq; unfold sb_grownA;
      first [cbn in K0; clear - K0 HL; lia| slia].
Qed.

End Open.
