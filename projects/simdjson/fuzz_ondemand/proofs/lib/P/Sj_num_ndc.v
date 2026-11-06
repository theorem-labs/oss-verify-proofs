(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Definition NDC_ENTRY : Z := 0x3c688.
Definition NDC_GTOP : Z := 0xab000.
Definition ndc_p5_stmt : Prop := p5_stmt_g psegs 0x3ca54 NDC_GTOP.
Definition ndc_memmove_stmt : Prop := memmove_stmt_g psegs 0x72044.
Definition ndc_memset_stmt : Prop := memsetZ_stmt_g psegs 0x721c0.

Section NDC.
  Hypothesis HP5 : ndc_p5_stmt.
  Hypothesis HMOVE : ndc_memmove_stmt.
  Hypothesis HSET : ndc_memset_stmt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X lo : Z) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation T := (SP + -568)%Z.
  Hypothesis ROOM : (lo + NDC_STACK <= SP)%Z.
  Hypothesis GTOP : (NDC_GTOP <= lo)%Z.
  Hypothesis XHI : (SP <= X)%Z.

  Notation W := [(SP - NDC_STACK, SP); (X, X + 498)]%Z.
  Notation POST := (ndc_post_g psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo m0).
  Notation ND pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 (SP + -576)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6
             s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  Definition NDINV (mm : mem) (xlen tlen : Z) : Prop :=
    (exists j, rw_cells psegs mm (SP + -576) [CB 8 j]) /\
    (exists tbs, u8arr psegs mm T tbs /\ length tbs = 496%nat) /\
    rw_cells psegs mm (SP + -72) [C2 (Z_to_bv 64 tlen)] /\ (0 <= tlen <= 62)%Z /\
    (exists j, rw_cells psegs mm (SP + -70) [CB 6 j]) /\
    rw_cells psegs mm (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists xbs, u8arr psegs mm X xbs /\ length xbs = 496%nat) /\
    rw_cells psegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] /\ (0 <= xlen <= 62)%Z /\
    mem_inv psegs mm /\ munch W m0 mm /\ wmono psegs m0 mm /\ stk psegs mm lo (SP + -576).

  Ltac nd_open H :=
    let j := fresh "j" in let tbs := fresh "tbs" in let j2 := fresh "j" in let xbs := fresh "xbs" in
    destruct H as ((j & FR0) & (tbs & TA & ?TL) & TN & ?TLEN & (j2 & TP) & SAVED & (xbs & XA & ?XL) & XN & ?XLEN & MI & MU & WM & ST);
    unfold NDC_STACK, P5_STACK, LM_STACK in MU.
  Ltac nd_close :=
    lazymatch goal with
    | |- NDINV _ _ _ =>
        split; [eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|]; split; [eassumption|]; split; [lia|];
        split; [eexists; eassumption|]; split; [eassumption|]; split; [eexists; split; [eassumption| lia]|];
        split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
    end.
  Ltac nd_env :=
    pose proof ROOM as ROOM'; pose proof GTOP as GTOP'; unfold NDC_STACK, P5_STACK, LM_STACK, NDC_GTOP in ROOM', GTOP';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR.

  Lemma nd_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen ->
    evt psegs POST (ND 0x3ca2c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros until tlen. intros INV. nd_open INV. nd_env.
    do 8 zstep. zstep. zstep.
    apply rw_cells_of_u8arr in TA. rewrite TL in TA.
    release_frame FR0 ST (SP + -568)%Z.
    release_frame TA ST (SP + -72)%Z.
    release_frame TN ST (SP + -70)%Z.
    release_frame TP ST (SP + -64)%Z.
    release_frame SAVED ST (bv_unsigned sp).
    destruct (u64arr_of_u8arr psegs mm X xbs XA XL) as (ws & WL & WA).
    apply evt_done. unfold ndc_post_g. do 15 eexists. exists mm, ws, xlen.
    split; [cbv delta [mkR]; reflexivity|].
    unfold NDC_STACK, P5_STACK, LM_STACK, bigint_at.
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [split; [exact WA| split; [exact WL| split; [exact XN| lia]]] | exact ST].
  Qed.

  Lemma nd_tail : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen ->
    evt psegs POST (ND 0x3c980 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros until tlen. intros INV.
    assert (IsData xs0) by exact I. assert (IsData xs1) by exact I. assert (IsData xs4) by exact I.
    assert (IsData xa0) by exact I. assert (IsData xa1) by exact I.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3ca2c%Z => first [ eapply nd_exit; exact INV | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_cl : forall (f : nat) (j : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen -> (-1 <= j <= 61)%Z -> (j + 1 <= Z.of_nat f)%Z ->
    evt psegs POST (ND 0x3c958 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 (Z_to_bv 64 (T + 8 * j)) (Z_to_bv 64 (j + 2)) xa4 xa5 xa6 xa7
                       (Z_to_bv 64 (X + 8 * j)) xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros f. induction f as [|f IH]; intros until tlen; intros INV Hj Hf.
    - pose proof INV as INV0. nd_open INV. nd_env. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3c980%Z => first [ eapply nd_tail; exact INV0 | fail 100 "cut" pc ]
        end).
    - pose proof INV as INV0. nd_open INV. nd_env. nstep.
      walk ltac:(fun pc => lazymatch pc with
        | 0x3c980%Z => first [ eapply nd_tail; exact INV0 | fail 100 "cut" pc ]
        | 0x3c958%Z => first [ eapply evt_eq; [| eapply (IH (j - 1)%Z)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma nd_cmp : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen ->
    evt psegs POST (ND 0x3c918 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using ROOM XHI GTOP.
    intros until tlen. intros INV.
    pose proof INV as INV0. nd_open INV. nd_env.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c980%Z => first [ eapply nd_tail; exact INV0 | fail 100 "cut" pc ]
      | 0x3c958%Z => first [ eapply evt_eq; [| eapply (nd_cl 63 (xlen - 1)%Z)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_ad28 : forall xra xt0 xt1 xt2 xs0 xs1 (xa0 : word) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen ->
    evt psegs POST (ND 0x3c8c8 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE HSET ROOM XHI GTOP.
    intros until tlen. intros INV.
    pose proof INV as INV0. nd_open INV. nd_env.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c918%Z => first [ eapply nd_cmp; exact INV0 | fail 100 "cut" pc ]
      | 0x72044%Z => idtac
      end).
    set (d := Z.shiftr (bv_unsigned xa0) 6) in *.
    assert (Hd : (0 <= d < 288230376151711744)%Z).
    { unfold d. apply shr6_range. pose proof (bv_unsigned_in_range 64 xa0) as R. unfold bv_modulus in R. cbn in R. lia. }
    rewrite (Z.mod_small (d + xlen)) in * by lia.
    pose proof (u8arr_bound _ _ _ _ XA) as XB. rewrite XL in XB.
    num_call_memmove HMOVE XA (X + 8 * d)%Z X (8 * xlen)%Z.
    walk ltac:(fun pc => lazymatch pc with | 0x721c0%Z => idtac end).
    num_call_memset HSET XA 0%Z (8 * d)%Z 0%Z.
    clear INV0.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c918%Z => first [ eapply nd_cmp; nd_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_shlx : forall (f : nat) (i : Z) xra xt0 xt1 xt2 xs0 xs1 (xa0 : word) xa2 xa4 xa5 xa7 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen -> (0 <= i < xlen)%Z -> (xlen - i <= Z.of_nat f)%Z ->
    evt psegs POST (ND 0x3c88c xra xt0 xt1 xt2 xs0 xs1 xa0 (Z_to_bv 64 xlen) xa2 (Z_to_bv 64 (X + 8 * xlen)) xa4 xa5 (Z_to_bv 64 (X + 8 * i)) xa7
                       (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE HSET ROOM XHI GTOP.
    intros f. induction f as [|f IH]; intros until tlen; intros INV Hi Hf; [exfalso; lia|].
    nd_open INV. nd_env. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c88c%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | nd_close | lia | lia] | fail 100 "cut" pc ]
      | 0x3c8c8%Z => first [ eapply nd_ad28; nd_close | fail 100 "cut" pc ]
      | 0x3c918%Z => first [ eapply nd_cmp; nd_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_ac64 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 (xs5 : word) xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen ->
    evt psegs POST (ND 0x3c804 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE HSET ROOM XHI GTOP.
    intros until tlen. intros INV.
    pose proof INV as INV0. nd_open INV. nd_env.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c918%Z => first [ eapply nd_cmp; exact INV0 | fail 100 "cut" pc ]
      | 0x72044%Z => idtac
      end).
    set (d := Z.shiftr (bv_unsigned xs5) 6) in *.
    assert (Hd : (0 <= d < 288230376151711744)%Z).
    { unfold d. apply shr6_range. pose proof (bv_unsigned_in_range 64 xs5) as R. unfold bv_modulus in R. cbn in R. lia. }
    rewrite (Z.mod_small (d + tlen)) in * by lia.
    pose proof (u8arr_bound _ _ _ _ TA) as TB. rewrite TL in TB.
    num_call_memmove HMOVE TA (bv_unsigned sp + -568 + 8 * d)%Z (bv_unsigned sp + -568)%Z (8 * tlen)%Z.
    walk ltac:(fun pc => lazymatch pc with | 0x721c0%Z => idtac end).
    num_call_memset HSET TA 0%Z (8 * d)%Z 0%Z.
    clear INV0.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c918%Z => first [ eapply nd_cmp; nd_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_shlt : forall (f : nat) (i : Z) xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa7 xs3 xs4 (xs5 : word) xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen -> (0 <= i < tlen)%Z -> (tlen - i <= Z.of_nat f)%Z ->
    evt psegs POST (ND 0x3c7c0 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 tlen) (Z_to_bv 64 (8 * tlen)) xa2 xa3 xa4 (Z_to_bv 64 (T + 8 * i)) (Z_to_bv 64 (T + 8 * tlen)) xa7
                       (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE HSET ROOM XHI GTOP.
    intros f. induction f as [|f IH]; intros until tlen; intros INV Hi Hf; [exfalso; lia|].
    nd_open INV. nd_env. nstep.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c7c0%Z => first [ eapply evt_eq; [| eapply (IH (i + 1)%Z)]; [num_st_eq | nd_close | lia | lia] | fail 100 "cut" pc ]
      | 0x3c804%Z => first [ eapply nd_ac64; nd_close | fail 100 "cut" pc ]
      | 0x3c918%Z => first [ eapply nd_cmp; nd_close | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_abf4 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 (xs5 : word) xs6 xt3 xt4 xt5 xt6 mm xlen tlen,
    NDINV mm xlen tlen ->
    evt psegs POST (ND 0x3c794 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 X) xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using HMOVE HSET ROOM XHI GTOP.
    intros until tlen. intros INV.
    pose proof INV as INV0. nd_open INV. nd_env.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c918%Z => first [ eapply nd_cmp; exact INV0 | fail 100 "cut" pc ]
      | 0x3c804%Z => first [ eapply nd_ac64; exact INV0 | fail 100 "cut" pc ]
      | 0x3c8c8%Z => first [ eapply nd_ad28; exact INV0 | fail 100 "cut" pc ]
      | 0x3c7c0%Z => first [ eapply evt_eq; [| eapply (nd_shlt 62 0%Z)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      | 0x3c88c%Z => first [ eapply evt_eq; [| eapply (nd_shlx 62 0%Z)]; [num_st_eq | exact INV0 | lia | lia] | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma nd_abbc : forall (e : Z) xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm xbs xlen j j0 j1,
    rw_cells psegs mm (SP + -576) [CB 8 j; CB 8 j0; CB 496 j1; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    u8arr psegs mm X xbs -> length xbs = 496%nat -> rw_cells psegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] -> (0 <= xlen <= 62)%Z ->
    mem_inv psegs mm -> munch W m0 mm -> wmono psegs m0 mm -> stk psegs mm lo (SP + -576) ->
    (-2147483648 <= e < 2147483648)%Z ->
    evt psegs POST (ND 0x3c75c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 X) (Z_to_bv 64 e) xs4 xs5 xs6 xt3 xt4 xt5 xt6 mm).
  Proof using HP5 HMOVE HSET ROOM XHI GTOP.
    intros until j1. intros FR XA XL XN XLEN MI MU WM ST He.
    nd_env. unfold NDC_STACK, P5_STACK, LM_STACK in MU.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    walk ltac:(fun pc => lazymatch pc with | 0x721c0%Z => idtac end).

    change [CB 8 j; CB 8 j0; CB 496 j1; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      with ([CB 8 j; CB 8 j0] ++ [CB 496 j1] ++ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    apply num_rw_cells_app in FR. destruct FR as [FRa FR]. apply num_rw_cells_app in FR. destruct FR as [FRb SAVED].
    cbn [cells_size csize Nat.add] in FRb, SAVED.
    replace (SP + -576 + Z.of_nat 16)%Z with (SP + -560)%Z in * by lia.
    replace (SP + -560 + Z.of_nat 496)%Z with (SP + -64)%Z in * by lia.
    pose proof (u8arr_of_rw_cells psegs _ _ _ _ FRb) as ZA.
    assert (ZL : length j1 = 496%nat) by (destruct FRb as [[Hwf _] _]; cbn in Hwf; tauto).
    clear FRb.
    num_call_memset HSET ZA 0%Z 496%Z 0%Z.

    destruct (u8arr_range_split psegs _ _ _ 488 490 ZA ltac:(lia) ltac:(lia)) as (b1 & lenb & b3 & LB1 & LBM & LB3 & U1 & TN & U3).
    clear ZA.
    replace (SP + -560 + Z.of_nat 488)%Z with (SP + -72)%Z in TN by lia. change (490 - 488)%nat with 2%nat in TN.
    replace (SP + -560 + Z.of_nat 490)%Z with (SP + -70)%Z in U3 by lia.
    zstep. zstep. zstep.

    lazymatch type of FRa with rw_cells _ _ _ [CB 8 j; ?c] => change [CB 8 j; c] with ([CB 8 j] ++ [c]) in FRa end.
    apply num_rw_cells_app in FRa. destruct FRa as [FR0 L0]. cbn [cells_size csize Nat.add] in L0.
    replace (SP + -576 + Z.of_nat 8)%Z with (SP + -568)%Z in L0 by lia.
    destruct (rw_cells_forget psegs _ _ _ L0) as [l0 L0']. cbn [cells_size csize Nat.add] in L0'. clear L0.
    assert (LL0 : length l0 = 8%nat) by (destruct L0' as [[Hwf _] _]; cbn in Hwf; tauto).
    apply u8arr_of_rw_cells in L0'.
    replace (SP + -560)%Z with (SP + -568 + Z.of_nat (length l0))%Z in U1 by lia.
    pose proof (u8arr_app psegs _ _ _ _ L0' U1) as TA.
    assert (TL : length (l0 ++ b1) = 496%nat) by (rewrite length_app; lia).
    clear L0' U1.
    apply rw_cells_of_u8arr in U3. replace (length b3) with 6%nat in U3 by lia.
    num_cur_mem ltac:(fun m1 => assert (INV : NDINV m1 xlen 1) by nd_close).
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c794%Z => first [ eapply nd_abf4; exact INV | fail 100 "cut" pc ]
      | 0x3ca54%Z => idtac
      end).

    clear INV.
    set (e5 := bv_swrap 32 (0 - e mod 18446744073709551616)) in *.
    assert (He5 : (-2147483648 <= e5 < 2147483648)%Z) by (unfold e5; rewrite bv_swrap32; apply swrap32_range).
    destruct (u64arr_of_u8arr psegs _ _ _ TA TL) as (tws & TWL & TWA).
    replace (SP + -72)%Z with (SP + -568 + 496)%Z in TN by lia.
    pose proof HP5 as HP. unfold ndc_p5_stmt, p5_stmt_g in HP.
    eapply evt_cut.
    { eapply HP with (X := (SP + -568)%Z) (e := e5) (lo := lo) (ws := tws) (len := 1%Z);
        rewrite ?unsigned_lit by lia; unfold P5_STACK, LM_STACK, NDC_GTOP in *;
        [ eassumption | exact ST | lia | lia | split; [exact TWA| split; [exact TWL| split; [exact TN| lia]]] | lia | exact He5 ]. }
    cbv beta. intros ms' P. unfold p5_post_g in P.
    destruct P as (q5 & q6 & q7 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & ws3 & len3
                   & -> & MUc & WMc & MIc & BIG3 & STc).
    rewrite !unsigned_lit in MUc, STc by lia. unfold P5_STACK, LM_STACK in MUc.
    clear TA TN TWA.
    lazymatch type of MUc with munch _ ?mo ?mn => transport_after_call psegs mo mn MUc WMc end.
    clear MUc WMc HP. repeat match goal with MIo : mem_inv psegs ?mo |- _ => lazymatch mo with m3 => fail | _ => clear MIo end end.
    destruct BIG3 as (WA3 & WL3 & TN & TLEN3).
    num_ret_pc.
    destruct (u8arr_of_u64arr psegs m3 _ ws3 WA3 WL3) as (tbs3 & TL3 & TA). clear WA3 WL3.
    replace (SP + -568 + 496)%Z with (SP + -72)%Z in TN by lia.
    assert (INV : NDINV m3 xlen len3) by nd_close.
    eapply nd_abf4. exact INV.
  Qed.

  Lemma nd_body : forall t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 (e : Z) ws len,
    mem_inv psegs m0 -> stk psegs m0 lo SP -> bigint_at psegs m0 X ws len ->
    (-2147483648 <= e < 2147483648)%Z ->
    evt psegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 (Z_to_bv 64 e) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 NDC_ENTRY) fc None m0 (seg_rom psegs)).
  Proof using HP5 HMOVE HSET ROOM XHI GTOP.
    intros t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 e ws len MI ST (WA & WL & XN & XLEN) He.
    unfold NDC_ENTRY. nd_env.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    destruct (u8arr_of_u64arr psegs _ X ws WA WL) as (xbs & XL & XA). clear WA WL ws.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl psegs m0) as WM. unfold NDC_STACK, P5_STACK, LM_STACK in MU.
    set (m := m0) in MI, ST, XA, XN, MU at 2, WM at 2 |- * at 2. clearbody m.
    assert (DA1 : IsData a1) by exact I. assert (DA2 : IsData a2) by exact I.
    step.
    carve_frame 576%nat ST.
    apply (rw_cells_split_CB psegs m _ [] 576 junk [] [8;8;496;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 8 step.
    walk ltac:(fun pc => lazymatch pc with
      | 0x3c75c%Z => first [ eapply (nd_abbc e); eassumption | fail 100 "cut" pc ]
      end).
  Qed.
End NDC.

Theorem ndc_spec : ndc_p5_stmt -> ndc_memmove_stmt -> ndc_memset_stmt -> ndc_stmt_g psegs NDC_ENTRY NDC_GTOP.
Proof.
  intros H5 HMV HST. unfold ndc_stmt_g. intros until len. intros MI ST ROOM GTOP BIG XHI He.
  eapply nd_body; eassumption.
Qed.
