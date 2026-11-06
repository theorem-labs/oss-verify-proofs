(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame ZBridge SFModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim SjModel PjModel.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer SjPjItoa SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_skitA Pj_ser_intkA.
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

Section I64.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis F3COPY : f3copy_stmtA RT PMc.
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
Hypothesis BUD : A + 20 <= PJ_OUTMAX (pa_len E).
Hypothesis X0 : 0 <= X.
Hypothesis HK : av_KA RT PMc E I K isobj (i + 1) dp X (A + 20).

Notation IST pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xs11 xt3 xt4 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 dp) (Z_to_bv 64 (pa_SB E + 72)) (Z_to_bv 64 (SHDOCA E)) xs5 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 2147450880) xs8 xs9 (Z_to_bv 64 (pa_SB E)) xs11
        xt3 xt4 (Z_to_bv 64 (T5A E)) xt6 F fc m).
Notation SERMI shp x Σ st m := (SERMA RT E I (wz PJ_ESC_TAB_A) (wz (T5A E)) (wz (S64A E)) (wz (S80A E)) x shp isobj Σ st m).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.
Local Ltac sb_shz :=
  lazymatch goal with
  | HREF : SREFA _ _ _ _ _ ?mr, MU : munch _ ?mr ?mm, WM : wmono asegs ?mr ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHZ := fresh "SHZ" in let R64 := fresh "RD64" in let R72 := fresh "RD72" in let R80 := fresh "RD80" in
    pose proof (shz_sb_mu RT AF E D I OK CX _ _ _ mm HREF MU WM) as SHZ;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 64) ltac:(clear; lia)) as R64;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 72) ltac:(clear; lia)) as R72;
    pose proof (shz_rd mm _ _ SHZ (pa_SB E + 80) ltac:(clear; lia)) as R80; clear SHZ
  end.
Local Ltac shp_norm SHF l :=
  rewrite ?zb8_m8 in SHF;
  lazymatch type of SHF with u8arr _ _ _ ?cur => lazymatch cur with l => idtac | _ => replace cur with l in SHF by reflexivity end end;
  try match goal with L : length _ = 60%nat |- _ => clear L end;
  let SHL := fresh "SHL" in assert (SHL : length l = 60%nat) by reflexivity.
Local Ltac shst SHF k :=
  lazymatch type of SHF with u8arr _ ?m ?A ?l =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok asegs m A l k (wa (A + k)) SHF ltac:(change (Z.of_nat (length l)) with 60; lia) eq_refl) as SOK;
    step;
    let SHF1 := fresh "SHF" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le1 ?v)) _) =>
      pose proof (u8arr_write_le1 m A l k v a SHF ltac:(change (Z.of_nat (length l)) with 60; lia) ltac:(unfold wa; f_equal; lia)) as SHF1 end;
    store_done; try clear SHF; rename SHF1 into SHF
  end.
Local Ltac cbnx := cbn [Pj_ser_defsA.xj0 Pj_ser_defsA.xj56 Pj_ser_defsA.xj64 Pj_ser_defsA.xj96 Pj_ser_defsA.xj192 Pj_ser_defsA.xj200 Pj_ser_defsA.xj208 Pj_ser_defsA.xj256 Pj_ser_defsA.xj264] in *.

Lemma i64_finA : forall (len : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs11 xt3 xt4 xt6 : word),
  SERMI shpI2 x Σ st m -> frm0 fc -> 0 <= len -> sa_size st + len <= sa_cap st -> sa_size st + len <= A + 20 -> CREDA RT E I Σ X st ->
  aevt Σ K (IST 0xb4c38 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (shad (pa_SB E + 72))) (wz (sa_size st + len)) xs9 xs11 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW F3COPY OK CX Hi Hi2 Hdp BUD X0 HK.
  intros len x Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs11 xt3 xt4 xt6 HSM FRM L0 ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. cbnx. sb_shz.

  astep. astep. unbox FSB; unbox SHSB. step. box_disj.

  step. zstep. unbox SHSB; unbox SHf; unbox SHDC. shst SHF 38. shst SHF 39. shst SHF 40. box_disj. shp_norm SHF ser_shpatA.

  step. step. step.
  ser_close HSM2 OK CX. apply evt_done.
  eapply (HK Σ (mkSbA buf (size + len) cap hp kk) _ F fc); [eexists; exact HSM2| exact FRM| cbn [sa_size]; clear - ACC; lia| exact CR].
Qed.

Lemma i64_tailA : forall (len : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 : word),
  1 <= len <= 20 ->
  SERMI shpI2 x Σ st m -> frm0 fc -> sa_size st + len <= sa_cap st -> sa_size st + len <= A + 20 -> CREDA RT E I Σ X st ->
  aevt Σ K (IST 0xb4bf0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (shad (pa_SB E + 72))) (wz (sa_size st + len)) (wz len) (wz (si_f I + 304 + len))
               xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW F3COPY OK CX Hi Hi2 Hdp BUD X0 HK.
  intros len x Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xt3 xt4 xt6 HLEN HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). pose proof HSM as HSM0. ser_open HSM OK. cbnx. sb_shz.

  step. zstep. if_cases Kz; zify_cond Kz; pjnorm_in Kz; [exfalso; clear - Kz HLEN F0 FLO LQ QT; lia|].

  step. astep. astep. astep. astep. astep.

  step. step. step. zstep. step. zstep. zstep.
  pose proof (f3_rngA RT E D I _ _ _ _ _ _ isobj Σ _ m (si_f I + 304) len OK CX HSM0 ltac:(clear; lia) ltac:(clear - HLEN; lia) ltac:(clear - HLEN; lia))
    as (RC3 & F3a & F3b & (src & SRC & SRCL)).
  pose proof (f3_acc3 m (si_f I) shpI2 38 SHF eq_refl eq_refl eq_refl Ef ltac:(clear - F0; lia)) as AC24.
  ser_close HSM2 OK CX. apply evt_done.
  eapply aevt_eq; [| eapply (ser_copyA RT AF RC PMc FDO MST e_asan_memmove E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) m K (si_f I + 304) len 0xb4c34 src)];
    [pj_st_eq| right; reflexivity| exact OK| exact CX| exact HSM2| exact SRC| exact SRCL| clear - HLEN; lia| cbn [sa_size sa_cap]; exact ROOM
    | eapply acc_sub; [exact AC24| clear; lia| clear - HLEN; lia]| exact RC3| exact F3a| exact F3b
    | intros EQ; exfalso; clear - EQ; unfold e_asan_memmove, e_asan_memcpy in EQ; lia
    | clear; lia| reflexivity|].
  intros m' F' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
  apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK. cbnx.

  step.
  ser_close HSM5 OK CX. apply evt_done.
  eapply aevt_eq; [| eapply (i64_finA len _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; clear - HLEN ROOM ACC; cbn [sa_size sa_cap]; lia.
Qed.

Lemma i64_midA : forall (sg ndig : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xt3 xt4 xt5 xt6 : word),
  0 <= sg <= 1 -> 1 <= ndig -> ndig + sg <= 20 ->
  SERMI shpI1 x Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (SSTA I 0xb4b78 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 dp) (Z_to_bv 64 (pa_SB E + 72)) (Z_to_bv 64 (SHDOCA E)) xs5 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 2147450880)
              xs8 (wz ndig) (Z_to_bv 64 (pa_SB E)) (wz (si_f I + 304 + sg)) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST GROW F3COPY OK CX Hi Hi2 Hdp BUD X0 HK.
  intros sg ndig x Σ st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xt3 xt4 xt5 xt6 HSG HN1 HN2 HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. cbnx.

  step. zstep. unbox SHSB; unbox SHf; unbox SHDC. shst SHF 12. shst SHF 13. shst SHF 14. box_disj. shp_norm SHF shpI2.

  step. astep. sb_shz. astep. astep. step. astep. astep. astep.

  step. step. step. zstep. step. zstep. zstep. step.
  if_cases Kc; zify_cond Kc; pjnorm_in Kc.
  - ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (i64_tailA (ndig + sg) _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; clear - HSG HN1 HN2 Kc ACC; cbn [sa_size sa_cap]; lia.
  -
    zstep. pjnorm. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
    assert (GROWN : forall (z : Z) (ya0 : word), z = Z.max (2 * cap) (size + (ndig + sg)) ->
      evt asegs (fun ms' => aevt Σ K ms')
        (SSTA I 0xb4be4 xra xt0 xt1 xt2 ya0 (wz z) xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 dp) (Z_to_bv 64 (pa_SB E + 72)) (Z_to_bv 64 (SHDOCA E)) (wz (shad (pa_SB E + 72))) (Z_to_bv 64 (i + 1)) (Z_to_bv 64 2147450880)
              (wz (size + (ndig + sg))) (wz (ndig + sg)) (Z_to_bv 64 (pa_SB E)) (wz (si_f I + 304 + (ndig + sg))) xt3 xt4 (Z_to_bv 64 (T5A E)) xt6 F0 fc0 mm)) end.
    { intros z ya0 EZ.
      zstep. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K z X 0xb4bec)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| exact X0| clear; lia| reflexivity|].
      { rewrite EZ. eapply (ser_req_okA RT E D I); [exact OK| exact CX| exact HSM3| cbn [sa_cap]; clear - Kc; lia|].
        cbn [sa_size]. clear - ACC BUD HSG HN1 HN2. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 za0 za1 za2 za3 za4 za5 za6 za7 yt3 yt4 yt5 yt6 HSM4 CR4.
      apply (aevt_evt RT AF PMc MST). ser_open HSM4 OK. cbnx.
      step.
      ser_close HSM5 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (i64_tailA (ndig + sg) _ Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW z))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; rewrite ?EZ; clear - Kc ACC SZ HSG HN1 HN2; lia. }
    if_cases K2; zify_cond K2; pjnorm_in K2.
    + eapply evt_eq; [| eapply (GROWN (size + (ndig + sg)))]; [pj_st_eq; clear - HSG HN1; lia| clear - K2 Kc; lia].
    + zstep. eapply evt_eq; [| eapply (GROWN (2 * cap))]; [pj_st_eq; clear - HSG HN1; lia| clear - K2 Kc; lia].
Qed.

Lemma i64_lastA : forall (sg idx d : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt1 xt2 xa0 xa2 xa4 xa5 xa6 xs5 xs8 xt3 xt4 xt6 : word),
  0 <= sg <= 1 -> sg <= idx <= 19 -> 0 <= d <= 9 ->
  SERMI shpI1 x Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (IST 0xb4b4c xra (wz 99) xt1 xt2 xa0 (wz (si_f I + 96 + idx)) xa2 (wz d) xa4 xa5 xa6 (wz 10) xs5 xs8 (wz (8 * i)) (wz (si_f I + 304 + sg))
               xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW F3COPY OK CX Hi Hi2 Hdp BUD X0 HK.
  intros sg idx d x Σ st m F fc xra xt1 xt2 xa0 xa2 xa4 xa5 xa6 xs5 xs8 xt3 xt4 xt6 HSG HIDX HD HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. cbnx.
  destruct (shpI1_gran idx ltac:(clear - HIDX HSG; lia)) as (b & NB & BZ & B4).
  pose proof (itoa_shadow_read m (si_f I) shpI1 12 96 idx b SHF NB Ef ltac:(clear - F0; lia) ltac:(clear - HIDX HSG; lia) eq_refl) as RD.

  zstep. pjnorm. zstep. shfold. zstep. clear RD.
  lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
  assert (JOIN : forall ya0 ya2 : word,
    evt asegs (fun ms' => aevt Σ K ms')
      (IST 0xb4b5c xra (wz 99) xt1 xt2 ya0 (wz (si_f I + 96 + idx)) ya2 (wz d) xa4 xa5 xa6 (wz 10) xs5 xs8 (wz (8 * i)) (wz (si_f I + 304 + sg)) xt3 xt4 xt6 F0 fc0 mm)) end.
  { intros ya0 ya2.

    zstep. unbox FSB; unbox SHf. step. pj_store_done. box_disj. step. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
      pose proof (f3_acc20 m2 (si_f I) shpI1 12 SHF eq_refl eq_refl eq_refl Ef ltac:(clear - F0; lia)) as ACS;
      pose proof (f3_acc3 m2 (si_f I) shpI1 38 SHF eq_refl eq_refl eq_refl Ef ltac:(clear - F0; lia)) as ACD end.
    ser_close HSM2 OK CX.
    pose proof (f3_rngA RT E D I _ _ _ _ _ _ isobj Σ _ _ (si_f I + 96 + idx) (20 - idx) OK CX HSM2 ltac:(clear - HIDX HSG; lia) ltac:(clear - HIDX; lia) ltac:(clear - HIDX; lia))
      as (_ & _ & _ & (src & SRC & SRCL)).
    apply evt_done.
    eapply aevt_eq; [| eapply (F3COPY E D I _ _ _ _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (si_f I + 304 + sg) (si_f I + 96 + idx) (20 - idx) 0xb4b78 src)];
      [pj_st_eq| exact OK| exact CX| exact HSM2| exact SRC| exact SRCL| clear - HIDX; lia
      | clear - HIDX HSG; lia| clear - HIDX; lia| clear - HSG; lia| clear - HIDX HSG; lia
      | eapply acc_sub; [exact ACS| clear - HIDX HSG; lia| clear - HIDX; lia]
      | eapply acc_sub; [exact ACD| clear - HSG; lia| clear - HIDX HSG; lia]
      | right; clear - HIDX HSG; lia| clear; lia| reflexivity|].
    intros m' F' yt0 yt1 yt2 ya1 ya2' ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CPY.
    eapply aevt_eq; [| eapply (i64_midA sg (20 - idx) _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
      clear - HIDX HSG; lia. }
  destruct (Z_lt_le_dec idx 16) as [LO16|HI16].
  - rewrite (BZ ltac:(clear - LO16; lia)). replace (sxb z8) with (Z_to_bv 64 0) by reflexivity. zstep. try if_false. apply JOIN.
  - rewrite (B4 HI16). rewrite (pj_sxb_small7 4) by (clear; lia). zstep.
    if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - F0 HIDX HSG; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - F0 HIDX HSG Ef; Z.div_mod_to_equations; lia); clear - Kc HI16 HIDX Ef; Z.div_mod_to_equations; lia].
    apply JOIN.
Qed.

Lemma i64_loopA : forall (fu : nat) (sg idx w : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt1 xt2 xa1 xa5 xa6 xs5 xs8 xt3 xt4 xt6 : word),
  idx <= Z.of_nat fu -> 0 <= sg <= 1 -> 0 <= idx <= 19 -> 10 <= w < 10 ^ (idx + 1 - sg) -> w < 18446744073709551616 ->
  SERMI shpI1 x Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (IST 0xb4520 xra (wz 99) xt1 xt2 (wz (si_f I + 96 + idx)) xa1 (wz PJ_ITOA_BASE_A) (wz w) (wz (si_f I + 96 + idx)) xa5 xa6 (wz 10)
               xs5 xs8 (wz (8 * i)) (wz (si_f I + 304 + sg)) xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW F3COPY OK CX Hi Hi2 Hdp BUD X0 HK.
  induction fu as [|fu IH]; intros sg idx w x Σ st m F fc xra xt1 xt2 xa1 xa5 xa6 xs5 xs8 xt3 xt4 xt6 HFU HSG HIDX HW W64 HSM FRM ACC CR.
  { exfalso. pose proof (pow10_ge2 w (idx + 1 - sg) HW). lia. }
  pose proof (pow10_ge2 w (idx + 1 - sg) HW) as J2.
  pose proof (pow10_step w (idx + 1 - sg) ltac:(lia) ltac:(lia)) as HQ. replace (idx + 1 - sg - 1) with (idx - 1 + 1 - sg) in HQ by lia.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. cbnx. unfold PJ_ITOA_BASE_A in *.
  destruct (shpI1_gran idx HIDX) as (b & NB & BZ & B4).
  pose proof (itoa_shadow_read m (si_f I) shpI1 12 96 idx b SHF NB Ef ltac:(clear - F0; lia) ltac:(clear - HIDX; lia) eq_refl) as RD.

  zstep. pjnorm. zstep. shfold. zstep. clear RD. zstep.
  lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 _ ?mm _) =>
  assert (JOIN : forall ya1 ya3 : word,
    evt asegs (fun ms' => aevt Σ K ms')
      (IST 0xb4534 xra (wz 99) xt1 xt2 (wz (si_f I + 96 + idx)) ya1 (wz 64812) ya3 (wz (si_f I + 96 + idx)) (wz w) xa6 (wz 10)
            xs5 xs8 (wz (8 * i)) (wz (si_f I + 304 + sg)) xt3 xt4 xt6 F0 fc0 mm)) end.
  { intros ya1 ya3.

    step. zstep. zstep. zstep.
    rewrite SFModel.land_W64. change (2 ^ 64) with 18446744073709551616.
    change 14757395258967641293 with DIV10_MAGIC. rewrite (div10_machine w) by (clear - HW W64; lia).

    zstep. zstep. zstep. unbox FSB; unbox SHf. step. pj_store_done. box_disj. zstep. zstep. zstep.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    - ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (IH sg (idx - 1) (w / 10) _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
        [clear - HFU; lia| clear - HIDX J2 HSG; lia| | clear - HQ W64; lia].
      split; [apply (div10_ge10 w); clear - Kc HW; lia| exact (proj2 HQ)].
    - zstep. ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (i64_lastA sg (idx - 1) (w / 10) _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
        [clear - HIDX J2 HSG; lia|].
      split; [clear - HQ; lia|]. pose proof (div10_ge10 w ltac:(clear - HW; lia)) as DG. clear - Kc DG HQ. lia. }
  destruct (Z_lt_le_dec idx 16) as [LO16|HI16].
  - rewrite (BZ ltac:(clear - LO16; lia)). replace (sxb z8) with (Z_to_bv 64 0) by reflexivity. zstep. try if_false. apply JOIN.
  - rewrite (B4 HI16). rewrite (pj_sxb_small7 4) by (clear; lia). zstep.
    if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - F0 HIDX; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - F0 HIDX Ef; Z.div_mod_to_equations; lia); clear - Kc HI16 HIDX Ef; Z.div_mod_to_equations; lia].
    apply JOIN.
Qed.

Lemma i64_loop0A : forall (sg w : Z) (x : xjA) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xra xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs5 xs8 xt3 xt4 xt6 : word),
  0 <= sg <= 1 -> 10 <= w < 10 ^ (20 - sg) -> w < 18446744073709551616 ->
  SERMI shpI1 x Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (IST 0xb4518 xra (wz 99) xt1 xt2 xa0 xa1 (wz PJ_ITOA_BASE_A) (wz w) xa4 xa5 xa6 (wz 10) xs5 xs8 (wz (8 * i)) (wz (si_f I + 304 + sg)) xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW F3COPY OK CX Hi Hi2 Hdp BUD X0 HK.
  intros sg w x Σ st m F fc xra xt1 xt2 xa0 xa1 xa4 xa5 xa6 xs5 xs8 xt3 xt4 xt6 HSG HW W64 HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. cbnx.
  step. zstep.
  ser_close HSM2 OK CX. apply evt_done.
  eapply aevt_eq; [| eapply (i64_loopA 19%nat sg 19 w _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
    try (clear; lia). all: replace (19 + 1 - sg) with (20 - sg) by lia; exact HW.
Qed.

Theorem i64_mainA : forall (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
    (xs5 xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  ty (pa_T E) i = t_i64 ->
  SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= A -> CREDA RT E I Σ X st ->
  aevt Σ K (LSTA E I PJ_I64_A i dp (wz (SHDOCA E)) xs5 (wz PJ_NE_TAB_A) (wz (8 * i)) (wz (pa_SB E)) (wz (T5A E))
               xra xt0 xt1 xt2 (wz 108) (wz (pa_TAPE E)) (wz PJ_ITOA_BASE_A) (wz 108) xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF RC FDO MST GROW F3COPY OK CX Hi Hi2 Hdp BUD X0 HK.
  intros Σ st m F fc xs5 xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt6 HTY HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *. unfold PJ_I64_A.
  ser_envA OK CX. str_envA_sb OK. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. cbnx.

  pose proof (shz_tape_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHTP.
  assert (G : pa_TAPE E <= pa_TAPE E + 8 * (i + 1) < pa_TAPE E + 8 * pa_n E) by (clear - Hi Hi2; lia).
  pose proof (shz_rd _ _ _ SHTP _ G) as RD. clear G SHTP.
  zstep. zstep. pjnorm. zstep. astep. astep. astep. astep. clear RD.

  pose proof (tape_read_mu RT AF E D I OK CX Σ _ _ _ (i + 1) HREF MU WM ltac:(clear - Hi Hi2; lia)) as RDT.
  step. clear RDT.
  set (wd := Z_to_bv 64 (pa_T E (i + 1))). pose proof (bv_unsigned_in_range 64 wd) as WR. unfold bv_modulus in WR. cbn in WR.
  rewrite <- (Z_to_bv_bv_unsigned wd). set (w := bv_unsigned wd) in *. clearbody w. clear wd.

  step. unbox SHSB; unbox SHf; unbox SHDC. shst SHF 12. shst SHF 13. zstep. shst SHF 14. shst SHF 38. shst SHF 39. shst SHF 40. box_disj. shp_norm SHF shpI1.

  zstep. zstep. zstep.
  pose proof (u64_lt_pow10_20 w WR) as P20.
  if_cases Kn; zify_cond Kn; pjnorm_in Kn.
  -
    rewrite ?pj_signed_small in Kn by (clear - WR; lia) || idtac.
    step. zstep. unbox FSB; unbox SHf. step. pj_store_done. box_disj. zstep.
    replace (Z_to_bv 64 (0 - w)) with (Z_to_bv 64 (18446744073709551616 - w))
      by (apply Z_to_bv_eqm; change (2 ^ 64) with 18446744073709551616; clear - WR; Z.div_mod_to_equations; lia).
    step. zstep.
    assert (NW : 0 < 18446744073709551616 - w <= 9223372036854775808).
    { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Kn. cbn in Kn. clear - Kn WR. Z.div_mod_to_equations. lia. }
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    + ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (i64_loop0A 1 (18446744073709551616 - w) _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
        [clear; lia| change (10 ^ (20 - 1)) with 10000000000000000000; clear - Kc NW; lia| clear - NW; lia].
    +
      step. ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (i64_lastA 1 19 (18446744073709551616 - w) _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
        [clear; lia| clear; lia| clear - Kc NW; lia].
  -
    step. zstep.
    assert (PW : w < 9223372036854775808).
    { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Kn. cbn in Kn. clear - Kn WR. Z.div_mod_to_equations. lia. }
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    +
      step. ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (i64_lastA 0 19 w _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
        [clear; lia| clear; lia| clear - Kc WR; lia].
    + ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (i64_loop0A 0 w _ Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq;
        [clear; lia| change (10 ^ (20 - 0)) with 100000000000000000000; clear - Kc P20; lia| clear - WR; lia].
Qed.

End Pieces.

Theorem i64_okA : i64_stmtA' RT PMc.
Proof using AF RC FDO MST GROW F3COPY.
  unfold i64_stmtA'.
  intros E D I K isobj Σ st m F fc i dp A X xs5 xra xt0 xt1 xt2 xa4 xa5 xa6 xa7 xt3 xt4 xt6 OK CX HSM FRM Hi Hi2 HTY Hdp ACC BUD CR X0 HK.
  eapply (i64_mainA E D I K isobj i dp A X OK CX Hi Hi2 Hdp BUD X0 HK); eassumption.
Qed.
End I64.
