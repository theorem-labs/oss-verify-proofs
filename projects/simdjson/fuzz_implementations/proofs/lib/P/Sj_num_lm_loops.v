(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_num_kit Sj_num_lm_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section LMLOOPS.
  Variable E : lmenv.
  Hypothesis OK : lm_ok E.
  Notation SP := (l_SP E).
  Notation X := (l_X E).

  Ltac lm_begin INV :=
    lm_open INV; destruct OK as [ROOM XHI YLEN YLO]; unfold LM_STACK in *;
    pose proof (bv_unsigned_in_range 64 (l_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    lazymatch goal with HXA : u64arr _ _ (l_X E) ?ws, HXL : length ?ws = 62%nat |- _ =>
      let XB := fresh "XB" in pose proof (u64arr_bound _ _ _ _ HXA) as XB; rewrite HXL in XB end.

  Lemma lm_mul1 : forall (Q : machine_state -> Prop) (f : nat) (i n : Z)
      xra xt0 xt1 xt2 xs1 xa1 xa2 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm w16,
    LMINV E mm n w16 -> (0 <= i < n)%Z -> (n - i <= Z.of_nat f)%Z ->
    (forall xa1' xa3' xa4' xa5' mm', LMINV E mm' n w16 ->
       evt psegs Q (LM E 0x56944 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 (X + 8 * n)) xa1' xa2 xa3' xa4' xa5' xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (LM E 0x56920 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 (X + 8 * n)) xa1 xa2 (Z_to_bv 64 (X + 8 * i)) xa4 xa5 xa6 xa7
                    xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until w16; intros INV Hi Hf HK; [exfalso; lia|].
    lm_begin INV.
    u64_read XA i w.
    zstep. zstep. zstep. zstep. zstep.
    u64_store XA i.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply (IH (i + 1)%Z n); [lm_close | lia | lia | exact HK]]. num_st_eq.
    - apply HK. lm_close.
  Qed.

  Lemma lm_mul2 : forall (Q : machine_state -> Prop) (f : nat) (i k : Z)
      xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm xlen w16,
    LMINV E mm xlen w16 -> (0 <= i < k)%Z -> (k <= 62)%Z -> (k - i <= Z.of_nat f)%Z ->
    (forall xa3' xa4' xa6' xa7' mm', LMINV E mm' xlen w16 ->
       evt psegs Q (LM E 0x56a54 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3' xa4' (Z_to_bv 64 (SP + -1112 + 8 * k)) xa6' xa7'
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (LM E 0x56a30 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 (Z_to_bv 64 (SP + -1112 + 8 * i)) (Z_to_bv 64 (SP + -1112 + 8 * k)) xa6 xa7
                    xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until w16; intros INV Hi Hk Hf HK; [exfalso; lia|].
    lm_begin INV.
    pose proof (u64arr_bound _ _ _ _ ZIA) as ZIB. rewrite ZIL in ZIB.
    u64_read ZIA i w.
    zstep. zstep. zstep. zstep. zstep.
    u64_store ZIA i.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply (IH (i + 1)%Z k); [lm_close | lia | lia | lia | exact HK]]. num_st_eq.
    - apply HK. lm_close.
  Qed.

  Lemma lm_add : forall (Q : machine_state -> Prop) (f : nat) (j k base : Z)
      xra xt0 xt1 xt2 xs1 xa0 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm xlen w16,
    LMINV E mm xlen w16 -> (0 <= j < k)%Z -> (0 <= base)%Z -> (base + k <= 62)%Z -> (k - j <= Z.of_nat f)%Z ->
    (forall xt0' xa0' xa1' xa3' xa4' xa5' xa6' xa7' mm', LMINV E mm' xlen w16 ->
       evt psegs Q (LM E 0x56b34 xra xt0' xt1 xt2 (Z_to_bv 64 X) xs1 xa0' xa1' (Z_to_bv 64 (SP + -1112 + 8 * k)) xa3' xa4' xa5' xa6' xa7'
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (LM E 0x56b10 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0 (Z_to_bv 64 (SP + -1112 + 8 * j)) (Z_to_bv 64 (SP + -1112 + 8 * k))
                    (Z_to_bv 64 (X + 8 * (base + j))) xa4 xa5 xa6 xa7
                    xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until w16; intros INV Hj Hb Hbk Hf HK; [exfalso; lia|].
    lm_begin INV.
    pose proof (u64arr_bound _ _ _ _ ZIA) as ZIB. rewrite ZIL in ZIB.
    assert (KREST : forall xt0' xa0' xa4' xa5' xa6' xa7',
              evt psegs Q (LM E 0x56af0 xra xt0' xt1 xt2 (Z_to_bv 64 X) xs1 xa0' (Z_to_bv 64 (SP + -1112 + 8 * j)) (Z_to_bv 64 (SP + -1112 + 8 * k))
                              (Z_to_bv 64 (X + 8 * (base + j))) xa4' xa5' xa6' xa7'
                              xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm)).
    { intros xt0' xa0' xa4' xa5' xa6' xa7'.
      zstep. zstep.
      u64_store XA (base + j)%Z.
      zstep. zstep. zstep. zstep. zstep.
      if_cases K; zify_cond K.
      - apply HK. lm_close.
      - eapply evt_eq; [| eapply (IH (j + 1)%Z k base); [lm_close | lia | lia | lia | lia | exact HK]]. num_st_eq. }
    u64_read XA (base + j)%Z wx.
    u64_read ZIA j wz.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    if_cases KC.
    - apply KREST.
    - zstep. zstep. apply KREST.
  Qed.

  Lemma lm_carry : forall (Q : machine_state -> Prop) (f : nat) (p : Z)
      xra xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm xlen w16,
    LMINV E mm xlen w16 -> (0 <= p <= xlen)%Z -> (xlen - p <= Z.of_nat f)%Z ->
    (forall xa0' xa1' xa2' xa3' mm', LMINV E mm' xlen w16 ->
       evt psegs Q (LM E 0x56b7c xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0' xa1' xa2' xa3' xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm')) ->
    (forall xa0' xa1' xa2' xa3' mm', LMINV E mm' xlen w16 ->
       evt psegs Q (LM E 0x569d4 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 xa0' xa1' xa2' xa3' xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm')) ->
    evt psegs Q (LM E 0x56b58 xra xt0 xt1 xt2 (Z_to_bv 64 X) xs1 (Z_to_bv 64 (xlen - p + 1)) (Z_to_bv 64 (X + 8 * p)) xa2 xa3 xa4 xa5 xa6 xa7
                    xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros until w16; intros INV Hp Hf HPUSH HBOT.
    -
      pose proof INV as INV0. lm_begin INV.
      zstep. zstep.
      if_cases K; zify_cond K; [|exfalso; lia].
      apply HPUSH. exact INV0.
    - pose proof INV as INV0. lm_begin INV.
      zstep. zstep.
      if_cases K; zify_cond K.
      { apply HPUSH. exact INV0. }
      u64_read XA p w.
      zstep. zstep. zstep.
      u64_store XA p.
      zstep. zstep.
      if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply (IH (p + 1)%Z); [lm_close | lia | lia | exact HPUSH | exact HBOT]]. num_st_eq.
      + zstep. apply HBOT. lm_close.
  Qed.
End LMLOOPS.
