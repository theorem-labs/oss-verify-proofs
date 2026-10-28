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
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA.
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

Section Head.
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
Hypothesis DISP : disp_stmtA RT PMc E I K D (S fu).
Hypothesis PKEY : key_stmtA RT PMc.
Notation aevt := (aevt RT PMc).
Notation RESTA := (rest_ok (pa_T E) (pa_S E) (pa_sn E)).
Local Ltac slia := repeat match goal with H : _ \/ _ |- _ => clear H end; cbn [sa_size sa_cap sa_buf sa_heap sa_k]; lia.

Lemma head_itemA : forall (d0 : nat) (ks : list bool) (i i2 c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32) (j168 j176 j184 j224 : word) (x : xjA)
    (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - i <= Z.of_nat (S fu) -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  item_okA E ks d0 i i2 c c2 -> RESTA d0 ks i2 c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMA RT E I (mkWK j168 j176 j184 j224 (wz (S64A E)) (wz (T5A E)) (wz (S80A E))) x ser_shpatA isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i - 1) + 6 * c + 3 ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (LSTA E I PJ_ITEM_A i (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) xt5
               xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF MST OK CX DISP PKEY.
  intros d0 ks i i2 c c2 isobj Σ st m F fc j168 j176 j184 j224 x xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HIT HR HI HC HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (c_c' E D I CX) as (CC1 & CC2).
  pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  assert (KB : exists k : bool, nth_error isobj (Z.to_nat (Z.of_nat (length ks))) = Some (kbyte k)
               /\ (k = false -> elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d0 i i2 c c2)
               /\ (k = true -> fieldS (pa_T E) (pa_S E) (pa_sn E) (elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d0) i i2 c c2)).
  { rewrite Nat2Z.id. destruct ks as [|k ks'].
    - exists false. split; [exact (proj1 KR)|]. split; [intros _; exact HIT| discriminate].
    - exists k. cbn [length]. replace (S (length ks')) with (length ks' + 1)%nat by lia.
      split; [eapply kinds_rel_top; exact KR|]. cbn [item_okA] in HIT. unfold itemS in HIT.
      destruct k; (split; [intros Hk; first [discriminate Hk | exact HIT]| intros Hk; first [discriminate Hk | exact HIT]]). }
  destruct KB as (k & KN & KF & KT).
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK. unfold PJ_ITEM_A.
  pose proof (u8arr_read bsegs _ _ isobj (Z.of_nat (length ks)) (kbyte k) _ IS KN ltac:(lia) eq_refl) as RDK.

  zstep. zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; cbn in Kc; clear - Kc HL; lia].
  step. zstep. pjnorm. zstep.

  destruct k; unfold kbyte in *; cbn [Z.b2z] in *.
  -
    zstep. zstep. if_true. zstep. pjnorm.
    do 4 zstep. zstep. zstep. lstep. zstep. lstep. zstep. lstep.
    zstep. if_cases KC; zify_cond KC; [exfalso; pjnorm_in KC; lia| clear KC].
    ser_close HSMC OK CX.
    destruct (KT eq_refl) as (c1 & (l & HTW & HS & EC1) & HEL).
    pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT. pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & _).
    pose proof HS as (_ & L0 & _).
    apply evt_done. remember (41 * (i - 1) + 6 * c + 3) as A eqn:EA.
    eapply aevt_eq; [| eapply (PKEY E D I K isobj Σ (mkSbA buf size cap hp kk) _ F fc i c l (Z.of_nat (length ks)) A (2 * (si_j I - i) - 1))];
      [pj_st_eq| exact OK| exact CX| do 2 eexists; exact HSMC| exact FRM| clear - HI LT LEJ J2; lia| exact HTW| exact HS| clear - HL; lia| cbn [sa_size]; clear - ACC EA; lia
      | subst A; pose proof (sctx_out E D I OK CX) as OUTB; pose proof HS as (_ & L0x & _); clear - OUTB LT CUR LEC LEJ EC1 L0x HI HC; lia| exact CR| clear - HF0 LT LEJ; lia|].
    unfold disp_KA. intros Σ' st' m' F' fc' ys3 yt5 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt6 HSM' FRM' ACC' CR'.
    eapply (DISP d0 ks (i + 1) i2 c1 c2 isobj Σ' st'); try eassumption; try lia.
    eapply CREDA_le; [exact CR'| lia].
  -
    zstep. zstep. if_true. zstep. pjnorm.
    do 4 zstep. zstep. zstep. lstep. zstep. lstep. zstep. lstep.
    zstep. if_cases KC; zify_cond KC; [clear KC| exfalso; pjnorm_in KC; lia].

    step. zstep. zstep. if_cases KD; zify_cond KD; [clear KD| exfalso; clear - KD DOCR; lia].
    zstep. if_true.
    ser_close HSMC OK CX.
    apply evt_done.
    eapply aevt_eq; [| eapply (DISP d0 ks i i2 c c2 isobj Σ (mkSbA buf size cap hp kk))];
      [pj_st_eq| exact HF0| exact HD| exact HL| exact KR| exact (KF eq_refl)| exact HR| lia| lia| do 2 eexists; exact HSMC| exact FRM| cbn [sa_size]; lia| exact CR].
Qed.

Lemma head_commaA : forall (d0 : nat) (ks : list bool) (i i2 c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32) (j168 j176 j184 j224 : word) (x : xjA)
    (xt5 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - i <= Z.of_nat (S fu) -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  item_okA E ks d0 i i2 c c2 -> RESTA d0 ks i2 c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMA RT E I (mkWK j168 j176 j184 j224 (wz (S64A E)) (wz (T5A E)) (wz (S80A E))) x ser_shpatA isobj Σ st m -> frm0 fc ->
  1 <= sa_size st -> sa_size st <= 41 * (i - 1) + 6 * c + 3 ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (LSTA E I 0xb81d4 i (Z.of_nat (length ks)) (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz (pa_SB E + 80)) xt5
               xra xt0 xt1 xt2 (wz (sa_buf st + (sa_size st - 1))) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF MST OK CX DISP PKEY.
  intros d0 ks i i2 c c2 isobj Σ st m F fc j168 j176 j184 j224 x xt5 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HIT HR HI HC HSM FRM SZ1 ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (buf_factsA RT AF E D I Σ _ _ (si_b I) OK CX HREF) as (_ & _ & _ & _ & APB). cbn [sa_buf sa_cap] in APB.
  pose proof (APB (buf + (size - 1)) ltac:(clear - SZ1 SZ; lia)) as (A1 & A2 & A3 & A4). clear APB.

  step. step. pj_store_done.
  ser_close HSM2 OK CX. apply evt_done.
  eapply (head_itemA d0 ks i i2 c c2 isobj Σ (mkSbA buf size cap hp kk)); try eassumption.
Qed.

Lemma head_tailA : forall (d0 : nat) (ks : list bool) (i i2 c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
    (F : bvmap 5 word) (fc : bv 32) (j168 j176 j184 j224 : word) (x : xjA)
    (xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
  si_j I - i <= Z.of_nat (S fu) -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
  item_okA E ks d0 i i2 c c2 -> RESTA d0 ks i2 c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
  SERMA RT E I (mkWK j168 j176 j184 j224 (wz (S64A E)) (wz (T5A E)) (wz (S80A E))) x ser_shpatA isobj Σ st m -> frm0 fc ->
  sa_size st + 1 <= sa_cap st -> sa_size st <= 41 * (i - 1) + 6 * c + 2 ->
  CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
  aevt Σ K (LSTA E I 0xb8168 i (Z.of_nat (length ks)) (wz ((pa_SB E + 72) / 8 + 2147450880)) (wz (pa_SB E + 80)) xt5
               xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Proof using AF MST OK CX DISP PKEY.
  intros d0 ks i i2 c c2 isobj Σ st m F fc j168 j176 j184 j224 x xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HIT HR HI HC HSM FRM ROOM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size sa_buf sa_cap] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). ser_open HSM OK.
  pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ _ HREF MU WM) as SHZ.
  pose proof (SHZ (pa_SB E + 64) ltac:(clear; lia)) as RD64. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.

  step. zstep. zstep. shz_norm. zstep. if_true.

  zstep. shz_norm. zstep. if_true.

  step. step. zstep. zstep. unbox FSB; unbox SHSB. step. box_disj.

  step. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc SZ R0; lia].
  zstep. zstep. zstep.
  replace (0 <? buf) with true by (symmetry; apply Z.ltb_lt; clear - R0; lia). replace (buf + size <? 1) with false by (symmetry; apply Z.ltb_ge; clear - R0 SZ; lia).
  cbn [Z.b2z Z.lxor]. zstep. if_true.
  zstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc R0; lia].

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (acc_buf_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as ACCB end.
  cbn [sa_buf sa_cap] in ACCB.
  destruct (acc_read1 _ _ _ (buf + size) ACCB ltac:(clear - ROOM SZ; lia)) as (b & RDB & SOK).
  zstep. pjnorm. zstep. zstep.
  ser_close HSM2 OK CX.
  destruct (pj_sh_ok_cases b (buf + size) SOK) as [-> | (k & -> & K17 & KM)].
  -
    rewrite sxb_z8. zstep. if_true. apply evt_done.
    eapply aevt_eq; [| eapply (head_commaA d0 ks i i2 c c2 isobj Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
  -
    rewrite (pj_sxb_small7 k) by (clear - K17; lia). zstep.
    if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc K17; lia| clear Kc].
    zstep. zstep. pjnorm. rewrite pj_land7 by (clear - R0 SZ; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [exfalso; rewrite !pj_signed_small in Kc by (clear - K17; Z.div_mod_to_equations; lia); clear - Kc K17 KM; lia| clear Kc].
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (head_commaA d0 ks i i2 c c2 isobj Σ (mkSbA buf (size + 1) cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

Lemma item_okA_lt : forall ks d0 i i2 c c2, item_okA E ks d0 i i2 c c2 -> i < i2.
Proof. intros [|k ks] d0 i i2 c c2 H; cbn [item_okA] in H; [eapply elemS_lt; exact H| eapply itemS_lt; exact H]. Qed.

Theorem head_proofA : head_stmtA RT PMc E I K D (S fu).
Proof using AF RC FDO MST GROW OK CX DISP PKEY.
  unfold head_stmtA.
  intros d0 ks i i2 c c2 after isobj Σ st m F fc w x xs3 xt5 xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6
         HF0 HD HL KR HIT HR HAF HI HC HSM FRM ACC CR.
  pose proof (c_j E D I CX) as (J1 & J2). pose proof (rest_ok_le _ _ _ _ _ _ _ _ _ HR) as (LEJ & LEC & _).
  pose proof (item_okA_lt _ _ _ _ _ _ HIT) as LT.
  pose proof (sctx_out E D I OK CX) as OUTB.
  assert (CUR : c <= c2).
  { destruct ks as [|k ks']; cbn [item_okA] in HIT.
    - exact (proj1 (elemS_cur _ _ _ _ _ _ _ _ _ HIT)).
    - exact (proj1 (itemS_cur _ _ _ _ _ _ _ _ _ HIT)). }
  destruct st as [buf size cap hp kk]. cbn [sa_size] in *.
  ser_envA OK CX. apply (aevt_evt RT AF PMc MST). unfold PJ_HEAD_A.
  destruct after; cbn [Z.b2z] in *.
  -
    ser_open HSM OK.

    zstep. pjnorm. zstep. pjnorm. step. zstep. pjnorm. step. zstep. pjnorm. step.
    step. if_cases Kc; zify_cond Kc; [exfalso; cbn in Kc; clear - Kc; lia| clear Kc].

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (shz_sb_mu RT AF E D I OK CX Σ _ _ mm HREF MU WM) as SHZ end.
    pose proof (SHZ (pa_SB E + 80) ltac:(clear; lia)) as RD80. pose proof (SHZ (pa_SB E + 72) ltac:(clear; lia)) as RD72.
    step. zstep. zstep. shz_norm. zstep. if_true. step. zstep. zstep. shz_norm. zstep. if_true.

    step. step. zstep. step.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    +
      ser_close HSM2 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (head_tailA d0 ks i i2 c c2 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
    +
      zstep. pjnorm. zstep. zstep.
      ser_close HSM3 OK CX. apply evt_done.
      eapply aevt_eq; [| eapply (ser_growA RT AF PMc GROW E D I _ _ _ isobj Σ (mkSbA buf size cap hp kk) _ K (2 * cap) (2 * (si_j I - i) - 1) 0xb8168)];
        [pj_st_eq| exact OK| exact CX| exact HSM3| | exact CR| clear - LT LEJ; lia| clear; lia| reflexivity|].
      { eapply (ser_req_ok2A RT E D I); [exact OK| exact CX| exact HSM3|]. cbn [sa_cap sa_size] in *. clear - Kc ACC OUTB LT LEJ CUR LEC HI HC. lia. }
      intros Σ' NEW m' F' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HSM4 CR4.
      eapply aevt_eq; [| eapply (head_tailA d0 ks i i2 c c2 isobj Σ' (sb_grownA (mkSbA buf size cap hp kk) NEW (2 * cap)))]; try eassumption; try pj_st_eq;
        unfold sb_grownA; slia.
  -
    ser_open HSM OK.
    zstep. pjnorm. zstep. pjnorm. step. zstep. pjnorm. step. zstep. pjnorm. step.
    step. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; cbn in Kc; clear - Kc; lia].
    ser_close HSM2 OK CX. apply evt_done.
    eapply aevt_eq; [| eapply (head_itemA d0 ks i i2 c c2 isobj Σ (mkSbA buf size cap hp kk))]; try eassumption; try pj_st_eq; slia.
Qed.

End Head.
