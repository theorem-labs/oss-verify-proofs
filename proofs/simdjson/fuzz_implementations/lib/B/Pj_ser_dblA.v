(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame ZBridge SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_trefA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA
     Pj_ser_ncallsA.
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
Ltac gok := let G := fresh "G" in zstep; if_cases G; zify_cond G; [try clear G| gref G].

Definition shpD1Z : list Z :=
  [241; 241; 241; 241; 0; 0; 0; 0; 0; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242;
   248; 248; 248; 242; 242; 242; 242; 242; 248; 242; 242; 242; 248; 242; 242; 242; 0; 0; 243; 243; 243; 243].
Definition shpD1 : list byte := map (Z_to_bv 8) shpD1Z.
Lemma shpD1_eq : upd (upd (upd (upd (upd ser_shpatA 4 z8) 5 z8) 6 z8) 7 z8) 8 z8 = shpD1.
Proof. reflexivity. Qed.
Lemma shpD0_eq : upd (upd (upd (upd (upd shpD1 4 (Z_to_bv 8 248)) 5 (Z_to_bv 8 248)) 6 (Z_to_bv 8 248)) 7 (Z_to_bv 8 248)) 8 (Z_to_bv 8 248) = ser_shpatA.
Proof. reflexivity. Qed.
Lemma shpD1_nb : forall j, (j < 5)%nat -> nth_error shpD1 (4 + j)%nat = Some z8.
Proof. intros [|[|[|[|[|j]]]]] H; [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| lia]. Qed.
Section Dbl.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis TOCHARS : tochars_cpsA RT PMc.
Notation aevt := (aevt RT PMc).

Section Pieces.
Variable E : pjenvA.
Variable D : nat.
Variable I : serI.
Variable K : config -> Prop.
Variable isobj : list byte.
Variables (i dp A X : Z).
Hypothesis OK : pjenvA_ok E.
Hypothesis CX : sctxA E D I.
Hypothesis Hi : 1 <= i.
Hypothesis Hi2 : i + 1 < pa_n E.
Hypothesis Hdp : 0 <= dp <= 15.
Hypothesis BUD : A + 27 <= PJ_OUTMAX (pa_len E).
Hypothesis X1 : 1 <= X.
Hypothesis HK : av_KA RT PMc E I K isobj (i + 1) dp (X - 1) (A + 27).

Notation DST pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 (pa_SB E + 72)) xs3 xs4 (Z_to_bv 64 (SHFA I)) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 (pa_SB E + 80)) xs8 (Z_to_bv 64 2147450880) (Z_to_bv 64 dp) (Z_to_bv 64 (pa_DOC E))
        xt3 xt4 xt5 xt6 F fc m).
Notation SERMD shp x Σ st m := (SERMA RT E I (wkC E) x shp isobj Σ st m).
Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono bsegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.
Local Ltac shp_norm SHF l :=
  rewrite ?zb8_m8 in SHF;
  lazymatch type of SHF with u8arr _ _ _ ?cur => lazymatch cur with l => idtac | _ => replace cur with l in SHF by reflexivity end end;
  try match goal with L : length _ = 44%nat |- _ => clear L end;
  let SHL := fresh "SHL" in assert (SHL : length l = 44%nat) by reflexivity.

Local Ltac shst SHF k :=
  lazymatch type of SHF with u8arr _ ?m ?A ?l =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok bsegs m A l k (wa (A + k)) SHF ltac:(change (Z.of_nat (length l)) with 44; lia) eq_refl) as SOK;
    step;
    let SHF1 := fresh "SHF" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le1 ?v)) _) =>
      pose proof (u8arr_write_le1 m A l k v a SHF ltac:(change (Z.of_nat (length l)) with 44; lia) ltac:(unfold wa; f_equal; lia)) as SHF1 end;
    store_done; try clear SHF; rename SHF1 into SHF
  end.
Local Ltac cbnx := cbn [Pj_ser_defsA.xj0 Pj_ser_defsA.xj8 Pj_ser_defsA.xj16 Pj_ser_defsA.xj24 Pj_ser_defsA.xj80 Pj_ser_defsA.xj208 Pj_ser_defsA.xj216 Pj_ser_defsA.xj288 Pj_ser_defsA.xj296] in *.

Lemma dbl_finA : forall (n : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
  SERMD shpD1 x Σ st m -> frm0 fc -> 0 <= n -> sa_size st + n <= sa_cap st -> sa_size st + n <= A + 27 -> CREDA RT E I Σ (X - 1) st ->
  aevt Σ K (DST 0xba024 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (shad (pa_SB E + 72))) (wz (sa_size st + n)) xs8 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW TOCHARS OK CX Hi Hi2 Hdp BUD X1 HK.
  intros n x Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 HSM FRM L0 ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. cbnx. sb_shz.

  astep. astep. unbox FSB; unbox SHSB. step. box_disj.

  zstep. unbox SHSB; unbox SHf; unbox SHDC. shst SHF 4. shst SHF 5. shst SHF 6. shst SHF 7. shst SHF 8. box_disj. shp_norm SHF ser_shpatA.

  step. step. step.
  ser_close HSM2 OK CX. apply evt_done.
  eapply (HK Σ (mkSbA buf (size + n) cap hp kk) _ F fc); [eexists; exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
Qed.

Lemma dbl_tailA : forall (n : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  1 <= n <= 27 ->
  SERMD shpD1 x Σ st m -> frm0 fc -> sa_size st + n <= sa_cap st -> sa_size st + n <= A + 27 -> CREDA RT E I Σ (X - 1) st ->
  aevt Σ K (DST 0xb9fd4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (shad (pa_SB E + 72))) (wz (sa_size st + n)) (wz (si_f I + 32 + n))
               xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW TOCHARS OK CX Hi Hi2 Hdp BUD X1 HK.
  intros n x Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HN HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. ser_open HSM OK. cbnx. sb_shz.

  step. astep. astep. astep. astep. astep.

  step. step. step. zstep. try (replace (size + buf) with (buf + size) by (clear; lia)).
  gtrap. zstep. zstep. zstep. unz. change (Z.lxor 1 0) with 1. gtrap.

  step. zstep. zstep.
  pose proof (f3_rngA RT E D I _ _ _ isobj Σ _ m (si_f I + 32) n OK CX HSM0 ltac:(clear; lia) ltac:(clear - HN; lia) ltac:(clear - HN; lia))
    as (RC3 & F3a & F3b & (src & SRC & SRCL)).
  pose proof (f3_acc_run m (si_f I) shpD1 4 5 SHF shpD1_nb Ef ltac:(clear - F0; lia)) as AC40.
  ser_close HSM2 OK CX. apply evt_done.
  eapply aevt_eq; [| eapply (ser_copyA RT AF RC PMc FDO MST E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) m K (si_f I + 32) n 0xba024 src)];
    [pj_st_eq; clear - HN; lia| exact OK| exact CX| exact HSM2| exact SRC| exact SRCL| clear - HN; lia| cbn [sa_size sa_cap]; exact ROOM
    | intros _; split; [eapply acc_sub; [exact AC40| clear; lia| clear - HN; lia]| exact RC3]| clear - F0; lia| exact F3b
    | clear; lia| reflexivity|].
  intros m' F' yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
  eapply aevt_eq; [| eapply (dbl_finA n _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; clear - HN ROOM ACC; cbn [sa_size sa_cap]; lia.
Qed.

Lemma dbl_midA : forall (e : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6 : word),
  si_f I + 32 < e <= si_f I + 59 ->
  SERMD shpD1 x Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ (X - 1) st ->
  aevt Σ K (DST 0xb9f78 xra xt0 xt1 xt2 (wz e) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW TOCHARS OK CX Hi Hi2 Hdp BUD X1 HK.
  intros e x Σ st m F fc xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs8 xt3 xt4 xt5 xt6 HE HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. cbnx.

  step. astep. sb_shz. astep. astep. zstep. step. astep. astep. astep.

  step. step. step. zstep. zstep. step.
  set (n := e - (si_f I + 32)) in *.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  - ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (dbl_tailA n _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try (pj_st_eq; subst n; clear - HE; lia);
      subst n; clear - HE Kc ACC; cbn [sa_size sa_cap]; lia.
  -
    zstep. pjnorm. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + n) ->
      evt bsegs (fun ms' => aevt Σ K ms')
        (DST 0xb9fcc xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa6 xa7
             (wz (shad (pa_SB E + 72))) (wz (size + n)) (wz e) xt3 xt4 xt5 xt6 F0 fc0 mm)) end.
    { intros z ya0 EZ.
      step. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z (X - 1) 0xb9fd4)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - X1; lia| clear; lia| reflexivity|].
      { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. subst n. clear - ACC BUD HE. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
      eapply aevt_eq; [| eapply (dbl_tailA n _ Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try (pj_st_eq; subst n; clear - HE; lia);
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; subst n; clear - Kc ACC SZ HE; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    + eapply evt_eq; [| eapply (GROWN (size + n))]; [pj_st_eq; subst n; clear - HE; lia| clear - K2 Kc; lia].
    + zstep. eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq; subst n; clear - HE; lia| clear - K2 Kc; lia].
Qed.

Theorem dbl_mainA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xs3 xs7 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  ty (pa_T E) i = t_dbl ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (LSTA E I PJ_DBL_A i dp xs3 xs7 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW TOCHARS OK CX Hi Hi2 Hdp BUD X1 HK.
  intros Σ st m F fc xs3 xs7 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HTY HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *. unfold PJ_DBL_A.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). destruct HSM as [x HSM]. pose proof HSM as HSM0. ser_open HSM OK. cbnx.

  zstep. zstep. zstep. zstep.
  ser_close HSM1 OK CX.
  eapply evt_cut; [eapply (ser_trefA RT AF E D I _ _ _ isobj Σ _ m (i + 1)); [exact OK| exact CX| exact HSM1| clear - Hi Hi2; lia]|].
  cbv beta. intros ms1 (m1 & ya4 & -> & HSM2). clear HSM1 HSM0. rewrite (ret_pc_even 0xb9f40) by (clear; lia).
  ser_open HSM2 OK. cbnx.

  pose proof (shz_tape_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHTP.
  assert (G : pa_TAPE E <= pa_TAPE E + 8 * (i + 1) < pa_TAPE E + 8 * pa_n E) by (clear - Hi Hi2; lia).
  pose proof (shz_rd _ _ _ SHTP _ G) as RD. clear G SHTP.
  astep. astep. astep. step. astep. clear RD.

  pose proof (tape_read_mu RT AF E D I OK CX Σ _ _ _ (i + 1) HREF MU WM ltac:(clear - Hi Hi2; lia)) as RDT.
  step. clear RDT.

  unbox SHSB; unbox SHf; unbox SHDC. shst SHF 4. shst SHF 5. shst SHF 6. shst SHF 7. shst SHF 8. box_disj. shp_norm SHF shpD1.

  step. zstep.
  ser_close HSM3 OK CX. apply evt_done.
  eapply aevt_eq; [| eapply (ser_tocharsA RT AF RC PMc FDO MST TOCHARS E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K X 0xb9f78)];
    [pj_st_eq| exact OK| exact CX| exact HSM3| exact shpD1_nb| exact FRM| exact CR| exact X1| clear; lia| reflexivity|].
  intros Σ' e m' F' fc' yt0 yt1 yt2 ya1 ya2 ya3 ya4' ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4 FRM4 HE.
  eapply (dbl_midA e _ Σ' (mkSbA buf size cap hp kk)); [exact HE| exact HSM4| exact FRM4| cbn [sa_size]; exact ACC| exact CR4].
Qed.

End Pieces.

Theorem dbl_okA : dbl_stmtA RT PMc.
Proof using AF RC FDO MST GROW TOCHARS.
  unfold dbl_stmtA.
  intros E D I K isobj Σ st m F fc i dp A X xs3 xs7 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 OK CX HSM FRM Hi Hi2 HTY Hdp ACC BUD CR X1 HK.
  eapply (dbl_mainA E D I K isobj i dp A X OK CX Hi Hi2 Hdp BUD X1 HK); eassumption.
Qed.
End Dbl.
