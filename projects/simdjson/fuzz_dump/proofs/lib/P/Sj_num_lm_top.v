(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_num_kit Sj_num_lm_defs Sj_num_lm_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section LMTOP.
  Hypothesis HMEMCPY : memcpy_stmt.
  Hypothesis HMEMSET : memset_stmt.
  Variable E : lmenv.
  Hypothesis OK : lm_ok E.
  Notation SP := (l_SP E).
  Notation X := (l_X E).
  Notation Y := (l_Y E).
  Notation ny := (l_ny E).
  Ltac lm_env :=
    destruct OK as [ROOM XHI YLEN YLO]; unfold LM_STACK in *;
    pose proof (bv_unsigned_in_range 64 (l_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR.
  Ltac lm_begin INV :=
    lm_open INV;
    lazymatch goal with HXA : u64arr _ _ (l_X E) ?ws, HXL : length ?ws = 62%nat |- _ =>
      let XB := fresh "XB" in pose proof (u64arr_bound _ _ _ _ HXA) as XB; rewrite HXL in XB end.

  Section LOOP.

  Variable zlen : Z.
  Hypothesis ZLEN : (0 <= zlen <= 62)%Z.
  Variable xs5 : word.
  Hypothesis S5Z : bv_unsigned xs5 = 0%Z <-> zlen = 0%Z.
  Notation W16 := (Z_to_bv 64 (8 * zlen)).

  Notation LMI idx pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (LM E pc xra xt0 xt1 xt2 (Z_to_bv 64 X) (Z_to_bv 64 Y) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 ny) xs3 (Z_to_bv 64 zlen) xs5 (Z_to_bv 64 (1 - idx)) (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Definition bot_k (idx : Z) : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xlen mm,
      LMINV E mm xlen W16 ->
      evt psegs (lm_post E) (LMI idx 0x4fb64 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 xlen) xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Lemma lm_260 : forall (idx k xlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    bot_k idx -> LMINV E mm xlen W16 -> (1 <= idx)%Z -> (0 <= k)%Z -> (idx + k <= xlen)%Z ->
    (bv_unsigned xs10 = 0%Z <-> k = 0%Z) ->
    evt psegs (lm_post E) (LMI idx 0x4fc64 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 xlen) (Z_to_bv 64 k) xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK ZLEN S5Z.
    intros until mm. intros HBOT INV Hidx Hk Hstart S10.
    lm_env. pose proof INV as INV0. lm_begin INV.
    zstep.
    if_cases K0; zify_cond K0.
    { eapply HBOT. exact INV0. }
    zstep. zstep. nnorm. zstep. zstep. zstep. zstep.
    eapply evt_eq; [| eapply (lm_add E OK (lm_post E) (Z.to_nat k) 0 k idx); [exact INV0 | lia | lia | lia | lia |]]; [num_st_eq|].
    lm_forget. clear INV0. intros xt0' xa0' xa1' xa3' xa4' xa5' xa6' xa7' mm1 INV.
    pose proof INV as INV0. lm_begin INV.
    zstep.
    if_cases K1; zify_cond K1.
    { eapply HBOT. exact INV0. }
    zstep. zstep. zstep.
    if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep. nnorm. zstep. zstep. zstep.
    eapply evt_eq; [| eapply (lm_carry E OK (lm_post E) (Z.to_nat (xlen - (idx + k))) (idx + k)%Z); [exact INV0 | lia | lia | |]]; [num_st_eq | |].
    -
      lm_forget. clear INV0. intros ya0 ya1 ya2 ya3 mm2 INV.
      pose proof INV as INV0. lm_begin INV.
      zstep. zstep.
      if_cases K3; zify_cond K3.
      { eapply lm_false; [exact OK | exact INV0]. }
      zstep. nnorm. zstep. zstep. zstep.
      u64_store_lit XA xlen (Z_to_bv 64 1).
      zstep. zstep.
      eapply evt_eq; [| eapply (HBOT) with (xlen := (xlen + 1)%Z); lm_close]. num_st_eq.
    - intros ya0 ya1 ya2 ya3 mm2 INV. eapply HBOT. exact INV.
  Qed.

  Lemma lm_230 : forall (idx k xlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    bot_k idx -> LMINV E mm xlen W16 -> (1 <= idx < ny)%Z -> (0 <= k <= 62)%Z ->
    (bv_unsigned xs10 = 0%Z <-> k = 0%Z) ->
    evt psegs (lm_post E) (LMI idx 0x4fc34 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 xlen) (Z_to_bv 64 k) xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using HMEMSET OK ZLEN S5Z.
    intros until mm. intros HBOT INV Hidx Hk S10.
    lm_env. pose proof INV as INV0. lm_begin INV.
    pose proof (bytes_at_bound _ _ _ _ YB) as YBD. rewrite YLEN in YBD.
    assert (K258 : forall xlen' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 mm', LMINV E mm' xlen' W16 -> (idx + k <= 62)%Z ->
              evt psegs (lm_post E) (LMI idx 0x4fc5c yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 xlen') (Z_to_bv 64 k) xs10
                                         (Z_to_bv 64 (idx + k)) yt3 yt4 yt5 yt6 mm')).
    { intros until mm'. intros INV' Hn. clear INV0. lm_forget. lm_begin INV'.
      zstep. zstep.
      num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV E m1 (idx + k) W16) by lm_close).
      eapply lm_260; [exact HBOT | exact INV1 | lia | lia | lia | exact S10]. }
    zstep. zstep. zstep.
    if_cases K0; zify_cond K0.
    { eapply lm_false; [exact OK | exact INV0]. }
    zstep.
    if_cases K1; zify_cond K1.
    { eapply K258; [exact INV0 | lia]. }

    zstep. nnorm. zstep. zstep. zstep. nnorm. zstep. zstep.
    destruct (u64arr_range_split psegs mm X ws (Z.to_nat xlen) (Z.to_nat (idx + k)) XA ltac:(lia) ltac:(lia))
      as (w1 & mid & w3 & L1 & LM & L3 & U1 & MID & U3).
    clear XA.
    replace (X + 8 * Z.of_nat (Z.to_nat xlen))%Z with (X + 8 * xlen)%Z in MID by lia.
    replace (8 * (Z.to_nat (idx + k) - Z.to_nat xlen))%nat with (Z.to_nat (8 * (idx + k - xlen))) in MID by lia.
    pose proof HMEMSET as HM. unfold memset_stmt, memsetZ_stmt_g in HM.
    eapply evt_cut.
    { eapply evt_eq; [| eapply HM with (D := (X + 8 * xlen)%Z) (C := 0%Z) (N := (8 * (idx + k - xlen))%Z) (junk := mid);
                        [exact MID | exact MI | lia | lia | lia | lia]].
      num_st_eq. }
    cbv beta. intros ms' P. unfold memsetZ_post_g in P.
    destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & MUc & WMc & MIc & DSTc).
    transport_after_call psegs mm m3 MUc WMc.
    clear MUc WMc MI HM.
    replace (ret_pc (Z_to_bv 64 326748)) with (Z_to_bv 64 326748) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace (X + 8 * xlen)%Z with (X + 8 * Z.of_nat (length w1))%Z in DSTc by lia.
    replace (Z.to_nat (8 * (idx + k - xlen))) with (8 * (Z.to_nat (idx + k) - Z.to_nat xlen))%nat in DSTc by lia.
    replace (X + 8 * Z.of_nat (Z.to_nat (idx + k)))%Z with (X + 8 * Z.of_nat (length w1) + 8 * Z.of_nat (Z.to_nat (idx + k) - Z.to_nat xlen))%Z in U3 by lia.
    destruct (u64arr_range_join psegs m3 X w1 _ _ w3 U1 DSTc U3) as (ws' & LW' & XA).
    assert (XL' : length ws' = 62%nat) by lia.
    clear U1 U3 DSTc.
    eapply evt_eq; [| eapply (K258 xlen); [lm_close | lia]]. num_st_eq.
  Qed.

  Lemma lm_228 : forall (idx k xlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    bot_k idx -> LMINV E mm xlen W16 -> (1 <= idx < ny)%Z -> (0 <= k <= 62)%Z -> (idx <= xlen)%Z ->
    (bv_unsigned xs10 = 0%Z <-> k = 0%Z) ->
    evt psegs (lm_post E) (LMI idx 0x4fc2c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 xlen) (Z_to_bv 64 k) xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using HMEMSET OK ZLEN S5Z.
    intros until mm. intros HBOT INV Hidx Hk Hx S10.
    lm_env. pose proof INV as INV0. lm_begin INV.
    zstep. zstep.
    if_cases K0; zify_cond K0.
    - eapply lm_260; [exact HBOT | exact INV0 | lia | lia | lia | exact S10].
    - eapply lm_230; [exact HBOT | exact INV0 | lia | lia | exact S10].
  Qed.

  Lemma lm_body : forall (idx xlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
    bot_k idx -> LMINV E mm xlen W16 -> (1 <= idx < ny)%Z ->
    evt psegs (lm_post E) (LMI idx 0x4fb74 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 xlen) xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using HMEMCPY HMEMSET OK ZLEN S5Z.
    intros until mm. intros HBOT INV Hidx.
    lm_env. pose proof INV as INV0. lm_begin INV.
    pose proof (bytes_at_bound _ _ _ _ YB) as YBD. rewrite YLEN in YBD.
    destruct (bytes_u64_read psegs mm Y (l_ybs E) (8 * idx) YB ltac:(lia) ltac:(lia)) as [yi RDY].
    zstep. nnorm. zstep. zstep. zstep.
    if_cases K0.
    { eapply HBOT. exact INV0. }
    clear K0 RDY.
    zstep.
    num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV E m1 xlen W16) by lm_close).
    zstep.

    assert (K1FC : forall (k : Z) yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys9 ys10 yt3 yt4 yt5 yt6 mm', LMINV E mm' xlen W16 -> (0 <= k <= 62)%Z ->
              evt psegs (lm_post E) (LMI idx 0x4fc00 yra yt0 yt1 yt2 (Z_to_bv 64 k) ya1 ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 xlen) ys9 ys10 xs11 yt3 yt4 yt5 yt6 mm')).
    { intros until mm'. intros INV' Hk.
      zstep. zstep. nnorm. zstep.
      assert (S10 : bv_unsigned (Z_to_bv 64 (Z.shiftl k 48)) = 0%Z <-> k = 0%Z).
      { rewrite unsigned_lit_wrap. change (2 ^ 64)%Z with 18446744073709551616%Z. apply shl48_zero. lia. }
      if_cases K1; zify_cond K1.
      - eapply lm_228; [exact HBOT | exact INV' | lia | lia | lia | exact S10].
      - zstep. eapply lm_230; [exact HBOT | exact INV' | lia | lia | exact S10]. }
    if_cases K2; zify_cond K2.
    -
      assert (Z0 : zlen = 0%Z) by (apply S5Z; exact K2).
      zstep. zstep. zstep. nnorm. zstep.
      if_cases K3; zify_cond K3; [exfalso; lia|].
      zstep. zstep. zstep.
      assert (S10 : bv_unsigned (Z_to_bv 64 0) = 0%Z <-> 0%Z = 0%Z) by (split; reflexivity).
      if_cases K4; zify_cond K4.
      + eapply evt_eq; [| eapply (lm_230 idx 0 xlen); [exact HBOT | exact INV1 | lia | lia | exact S10]]. num_st_eq.
      + eapply evt_eq; [| eapply (lm_228 idx 0 xlen); [exact HBOT | exact INV1 | lia | lia | lia | exact S10]]. num_st_eq.
    -
      assert (Z0 : zlen <> 0%Z) by (intros EZ; apply K2; apply S5Z; exact EZ).
      zstep. zstep. zstep. zstep.
      pose proof (u64arr_bound _ _ _ _ ZIA) as ZIB. rewrite ZIL in ZIB.
      pose proof (u64arr_bound _ _ _ _ ZA) as ZB. rewrite ZL in ZB.
      pose proof (u64arr_prefix_bytes psegs m (SP + -608) zs (Z.to_nat zlen) ZA ltac:(lia)) as SRC.
      destruct (u64arr_range_split psegs m (SP + -1112) zis 0 (Z.to_nat zlen) ZIA ltac:(lia) ltac:(lia))
        as (w1 & mid & w3 & L1 & LMID & L3 & U1 & MID & U3).
      clear ZIA.
      replace (SP + -1112 + 8 * Z.of_nat 0)%Z with (SP + -1112)%Z in MID by lia.
      replace (8 * (Z.to_nat zlen - 0))%nat with (Z.to_nat (8 * zlen)) in MID by lia.
      pose proof HMEMCPY as HM. unfold memcpy_stmt, memcpyZ_stmt_g in HM.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HM with (Dst := (SP + -1112)%Z) (Src := (SP + -608)%Z) (N := (8 * zlen)%Z)
                            (src := u64s (firstn (Z.to_nat zlen) zs)) (junk := mid);
                          [exact SRC | rewrite u64s_length, length_firstn; lia | exact MID | lia | lia | lia | lia | exact MI]].
        num_st_eq. }
      cbv beta. intros ms' P. unfold memcpyZ_post_g in P.
      destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & MUc & WMc & MIc & DSTc & SRCc).
      clear SRC SRCc.
      transport_after_call psegs m m3 MUc WMc.
      clear MUc WMc MI HM.
      replace (ret_pc (Z_to_bv 64 326556)) with (Z_to_bv 64 326556) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      replace (SP + -1112)%Z with (SP + -1112 + 8 * Z.of_nat (length w1))%Z in DSTc by lia.
      replace (Z.to_nat (8 * zlen)) with (8 * Z.to_nat zlen)%nat in DSTc by lia.
      replace (SP + -1112 + 8 * Z.of_nat (Z.to_nat zlen))%Z with (SP + -1112 + 8 * Z.of_nat (length w1) + 8 * Z.of_nat (Z.to_nat zlen))%Z in U3 by lia.
      destruct (u64arr_range_join psegs m3 (SP + -1112) w1 _ _ w3 U1 DSTc U3) as (zis' & LZ' & ZIA).
      assert (ZIL' : length zis' = 62%nat) by lia.
      clear U1 U3 DSTc ZIL INV1 INV0.
      zstep. nnorm. zstep. zstep. zstep. nnorm. zstep.
      if_cases K3; zify_cond K3; [exfalso; lia|].
      zstep. zstep. nnorm. zstep. zstep.
      num_cur_mem ltac:(fun m1 => assert (INV2 : LMINV E m1 xlen W16) by lm_close).
      eapply evt_eq; [| eapply (lm_mul2 E OK (lm_post E) (Z.to_nat zlen) 0 zlen); [exact INV2 | lia | lia | lia |]]; [num_st_eq|].
      lm_forget. clear INV2. intros xa3' xa4' xa6' xa7' mm4 INV.
      pose proof INV as INV0. lm_begin INV.
      pose proof (u64arr_bound _ _ _ _ ZIA) as ZIB'. rewrite ZIL in ZIB'.
      zstep.
      if_cases K5; zify_cond K5.
      { eapply evt_eq; [| eapply (K1FC zlen); [exact INV0 | lia]]. num_st_eq. }
      zstep. zstep.
      if_cases K6; zify_cond K6.
      { eapply lm_false; [exact OK | exact INV0]. }
      zstep. zstep.
      u64_store ZIA zlen.
      zstep.
      eapply evt_eq; [| eapply (K1FC (zlen + 1)%Z); [lm_close | lia]]. num_st_eq.
  Qed.

  Definition lm_head_stmt (f : nat) : Prop :=
    forall (idx xlen : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm,
      LMINV E mm xlen W16 -> (1 <= idx < ny)%Z -> (ny - idx <= Z.of_nat f)%Z ->
      evt psegs (lm_post E) (LMI idx 0x4fb74 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 xlen) xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Lemma lm_bot : forall f idx, lm_head_stmt f -> (1 <= idx < ny)%Z -> (ny - idx <= Z.of_nat (S f))%Z -> bot_k idx.
  Proof using OK ZLEN S5Z.
    intros f idx HH Hidx Hf. unfold bot_k. intros until mm. intros INV.
    lm_env. pose proof INV as INV0. lm_begin INV.
    pose proof (bytes_at_bound _ _ _ _ YB) as YBD. rewrite YLEN in YBD.
    zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - eapply lm_norm; [exact OK | exact INV0].
    - eapply evt_eq; [| eapply (HH (idx + 1)%Z xlen); [exact INV0 | lia | lia]]. num_st_eq.
  Qed.

  Theorem lm_head : forall f, lm_head_stmt f.
  Proof using HMEMCPY HMEMSET OK ZLEN S5Z.
    intros f. induction f as [|f IH]; unfold lm_head_stmt; intros until mm; intros INV Hidx Hf; [exfalso; lia|].
    eapply lm_body; [eapply (lm_bot f); [exact IH | lia | lia] | exact INV | lia].
  Qed.
  End LOOP.

  Theorem lm_body_spec : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws len,
    mem_inv psegs (l_m0 E) -> stk psegs (l_m0 E) (l_lo E) SP -> bigint_at psegs (l_m0 E) X ws len -> bytes_at psegs (l_m0 E) Y (l_ybs E) ->
    evt psegs (lm_post E)
      (MS (mkR (l_ra E) (l_sp E) (l_gp E) (l_tp E) t0 t1 t2 (l_s0 E) (l_s1 E) (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 ny) a3 a4 a5 a6 a7
               (l_s2 E) (l_s3 E) (l_s4 E) (l_s5 E) (l_s6 E) (l_s7 E) (l_s8 E) (l_s9 E) (l_s10 E) (l_s11 E) t3 t4 t5 t6)
          (l_F E) (Z_to_bv 64 LM_ENTRY) (l_fc E) None (l_m0 E) (seg_rom psegs)).
  Proof using HMEMCPY HMEMSET OK.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws len MI ST (XA & XL & XN & LEN) YB.
    unfold LM_ENTRY. lm_env.
    assert (LO0 : (0 <= l_lo E)%Z) by (destruct ST as [? _]; assumption).
    pose proof (u64arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    pose proof (bytes_at_bound _ _ _ _ YB) as YBD. rewrite YLEN in YBD.
    pose proof (munch_refl (lm_W E) (l_m0 E)) as MU. pose proof (wmono_refl psegs (l_m0 E)) as WM. unfold lm_W, LM_STACK in MU.
    set (m := l_m0 E) in MI, ST, XA, XN, YB, MU at 2, WM at 2 |- * at 2. clearbody m.
    step.
    carve_frame 1136%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 1136 junk [] [16;8;496;8;496;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step.
    change [CB 16 j; CB 8 j0; CB 496 j1; CB 8 j2; CB 496 j3; CB 8 j4; C8 (l_s11 E); C8 (l_s10 E); C8 (l_s9 E); C8 (l_s8 E); C8 (l_s7 E);
            C8 (l_s6 E); C8 (l_s5 E); C8 (l_s4 E); C8 (l_s3 E); C8 (l_s2 E); C8 (l_s1 E); C8 (l_s0 E); C8 (l_ra E)]
      with ([CB 16 j; CB 8 j0] ++ [CB (8 * 62) j1] ++ [CB 8 j2] ++ [CB (8 * 62) j3] ++ [CB 8 j4] ++ lm_saved E) in FR.
    apply num_rw_cells_app in FR. destruct FR as [FRlo FR]. apply num_rw_cells_app in FR. destruct FR as [FRzi FR].
    apply num_rw_cells_app in FR. destruct FR as [ZIN FR]. apply num_rw_cells_app in FR. destruct FR as [FRz FR].
    apply num_rw_cells_app in FR. destruct FR as [ZN SAVED].
    cbn [cells_size csize Nat.add Nat.mul] in FRzi, ZIN, FRz, ZN, SAVED.
    replace (SP + -1136 + Z.of_nat 24)%Z with (SP + -1112)%Z in * by lia.
    replace (SP + -1112 + Z.of_nat 496)%Z with (SP + -616)%Z in * by lia.
    replace (SP + -616 + Z.of_nat 8)%Z with (SP + -608)%Z in * by lia.
    replace (SP + -608 + Z.of_nat 496)%Z with (SP + -112)%Z in * by lia.
    replace (SP + -112 + Z.of_nat 8)%Z with (SP + -104)%Z in * by lia.
    destruct (u64arr_of_rw_cells psegs _ _ 62 _ FRzi) as (zis & ZIL & ZIA). clear FRzi.
    destruct (u64arr_of_rw_cells psegs _ _ 62 _ FRz) as (zs & ZL & ZA). clear FRz.
    apply (num_cb8_c8 psegs _ _ [CB 16 j] []) in FRlo. cbn [app] in FRlo.
    set (w16 := le_bytes_to_word j0) in FRlo. clearbody w16. clear j0.
    zstep. zstep. zstep. zstep. zstep. nnorm. zstep. zstep.
    zstep.
    if_cases K0; zify_cond K0; [exfalso; lia|].

    assert (K0E8 : forall xlen' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 mm',
              LMINV E mm' xlen' w16 -> (1 <= ny)%Z ->
              evt psegs (lm_post E) (LM E 0x4faec yra yt0 yt1 yt2 (Z_to_bv 64 X) (Z_to_bv 64 Y) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                                        (Z_to_bv 64 ny) ys3 (Z_to_bv 64 (0 + len)) ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 mm')).
    { intros until mm'. intros INV' Hny.
      replace (0 + len)%Z with len by lia.
      pose proof INV' as INV0. lm_forget. lm_begin INV'.
      zstep. zstep.
      if_cases K1; zify_cond K1.
      2:{ eapply lm_norm; [exact OK | exact INV0]. }
      zstep. zstep. nnorm. zstep. zstep.
      if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. zstep.
      assert (S5Z : bv_unsigned (Z_to_bv 64 (Z.shiftl len 48)) = 0%Z <-> len = 0%Z).
      { rewrite unsigned_lit_wrap. change (2 ^ 64)%Z with 18446744073709551616%Z. apply shl48_zero. lia. }
      assert (K144 : forall za1, evt psegs (lm_post E)
                (LM E 0x4fb48 yra yt0 yt1 yt2 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 (Z.shiftl len 51)) za1 ya2 ya3 ya4 ya5 ya6 ya7
                    (Z_to_bv 64 ny) ys3 (Z_to_bv 64 len) (Z_to_bv 64 (Z.shiftl len 48)) ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 mm')).
      { intros za1.
        zstep. zstep. nnorm. zstep. zstep. nnorm. zstep. zstep. zstep.
        num_cur_mem ltac:(fun m1 => assert (INV2 : LMINV E m1 xlen' (Z_to_bv 64 (8 * len))) by lm_close).
        eapply evt_eq; [| eapply (lm_head len LEN _ S5Z (Z.to_nat ny) 1%Z xlen'); [exact INV2 | lia | lia]]. num_st_eq. }
      zstep.
      if_cases K3; zify_cond K3.
      - eapply evt_eq; [| apply K144]. num_st_eq.
      - zstep. assert (NY2 : ny = 2%Z) by lia. eapply evt_eq; [| apply K144]. num_st_eq. }

    assert (K088 : forall yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 mm',
              LMINV E mm' len w16 ->
              evt psegs (lm_post E) (LM E 0x4fa8c yra yt0 yt1 yt2 (Z_to_bv 64 X) (Z_to_bv 64 Y) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                                        (Z_to_bv 64 ny) (Z_to_bv 64 len) (Z_to_bv 64 0) ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 mm')).
    { intros until mm'. intros INV'.
      lm_forget. lm_begin INV'.
      zstep. zstep. zstep.
      num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV E m1 len w16) by lm_close).
      if_cases K1; zify_cond K1.
      { eapply lm_norm; [exact OK | exact INV1]. }
      zstep.
      if_cases K2; zify_cond K2.
      { eapply K0E8; [exact INV1 | lia]. }
      destruct (bytes_u64_read psegs _ Y (l_ybs E) 0 YB ltac:(lia) ltac:(lia)) as [y0 RDY].
      rewrite Z.add_0_r in RDY.
      zstep. zstep. zstep. nnorm. zstep. zstep.
      eapply evt_eq; [| eapply (lm_mul1 E OK (lm_post E) (Z.to_nat len) 0 len); [exact INV1 | lia | lia |]]; [num_st_eq|].
      lm_forget. clear INV1. intros xa1' xa3' xa4' xa5' mm2 INV.
      pose proof INV as INV0. lm_begin INV.
      zstep.
      if_cases K3; zify_cond K3.
      { eapply K0E8; [exact INV0 | lia]. }
      zstep. zstep.
      if_cases K4; zify_cond K4.
      { eapply lm_false; [exact OK | exact INV0]. }
      u64_store XA len.
      zstep. zstep.
      eapply (K0E8 (len + 1)%Z); [lm_close | lia]. }
    zstep.
    if_cases K1; zify_cond K1.
    - zstep.
      num_cur_mem ltac:(fun m1 => assert (INV1 : LMINV E m1 len w16) by lm_close).
      eapply K088. exact INV1.
    - zstep. nnorm. zstep. zstep. zstep.
      pose proof (u64arr_bound _ _ _ _ ZA) as ZB. rewrite ZL in ZB.
      pose proof (u64arr_prefix_bytes psegs m X ws (Z.to_nat len) XA ltac:(lia)) as SRC.
      destruct (u64arr_range_split psegs m (SP + -608) zs 0 (Z.to_nat len) ZA ltac:(lia) ltac:(lia))
        as (w1 & mid & w3 & L1 & LMID & L3 & U1 & MID & U3).
      clear ZA.
      replace (SP + -608 + 8 * Z.of_nat 0)%Z with (SP + -608)%Z in MID by lia.
      replace (8 * (Z.to_nat len - 0))%nat with (Z.to_nat (8 * len)) in MID by lia.
      pose proof HMEMCPY as HM. unfold memcpy_stmt, memcpyZ_stmt_g in HM.
      eapply evt_cut.
      { eapply evt_eq; [| eapply HM with (Dst := (SP + -608)%Z) (Src := X) (N := (8 * len)%Z)
                            (src := u64s (firstn (Z.to_nat len) ws)) (junk := mid);
                          [exact SRC | rewrite u64s_length, length_firstn; lia | exact MID | lia | lia | lia | lia | exact MI]].
        num_st_eq. }
      cbv beta. intros ms' P. unfold memcpyZ_post_g in P.
      destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & MUc & WMc & MIc & DSTc & SRCc).
      clear SRC SRCc.
      transport_after_call psegs m m3 MUc WMc.
      clear MUc WMc MI HM.
      replace (ret_pc (Z_to_bv 64 326272)) with (Z_to_bv 64 326272) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      replace (SP + -608)%Z with (SP + -608 + 8 * Z.of_nat (length w1))%Z in DSTc by lia.
      replace (Z.to_nat (8 * len)) with (8 * Z.to_nat len)%nat in DSTc by lia.
      replace (SP + -608 + 8 * Z.of_nat (Z.to_nat len))%Z with (SP + -608 + 8 * Z.of_nat (length w1) + 8 * Z.of_nat (Z.to_nat len))%Z in U3 by lia.
      destruct (u64arr_range_join psegs m3 (SP + -608) w1 _ _ w3 U1 DSTc U3) as (zs' & LZ' & ZA).
      assert (ZL' : length zs' = 62%nat) by lia.
      clear U1 U3 DSTc ZL.
      zstep. nnorm. zstep.
      eapply K088. lm_close.
  Qed.
End LMTOP.

Theorem lm_spec : memcpy_stmt -> memset_stmt -> lm_stmt_g psegs LM_ENTRY.
Proof.
  intros HCPY HSET. unfold lm_stmt_g. intros until ybs. intros MI ST ROOM BIG XHI YB YLEN YLO.
  set (E := mkLmEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X Y ny lo ybs m).
  assert (OK : lm_ok E) by (constructor; cbn; assumption).
  exact (lm_body_spec HCPY HSET E OK t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ws len MI ST BIG YB).
Qed.
