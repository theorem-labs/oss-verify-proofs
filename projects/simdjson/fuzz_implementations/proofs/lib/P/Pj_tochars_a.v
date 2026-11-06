(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes FP StoreFast SysStep.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Str_tac Sj_num_kit Pj_num_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition TCINV (ra s0 s1 s2 s3 : word) (q lo NB : Z) (m0 m : word -> option byte) : Prop :=
  rw_cells psegs m (q + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  (exists tmp, u8arr psegs m (q + -80) tmp /\ length tmp = 40%nat) /\
  (exists nb, u8arr psegs m NB nb /\ length nb = 40%nat) /\
  mem_inv psegs m /\ munch [(q + -80, q); (NB, NB + 40)]%Z m0 m /\ wmono psegs m0 m /\ stk psegs m lo (q + -80).

Ltac tc_open H :=
  let tmp := fresh "tmp" in let nb := fresh "nb" in
  destruct H as (FRS & (tmp & TA & TL) & (nb & NA & NL) & MI & MU & WM & ST).
Ltac tc_close :=
  lazymatch goal with
  | |- TCINV _ _ _ _ _ _ _ _ _ _ =>
      split; [eassumption|]; split; [eexists; split; [eassumption| rewrite ?upd_bytes_length by (cbn [length]; lia); assumption]|];
      split; [eexists; split; [eassumption| rewrite ?upd_bytes_length by (cbn [length]; lia); assumption]|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Lemma bytes_at_read1 : forall segs (m : word -> option byte) A bs k,
  bytes_at segs m A bs -> (0 <= k < Z.of_nat (length bs))%Z ->
  exists b, ov_read_bytes segs m (wa (A + k)) 1 = Some [b].
Proof.
  intros segs m A bs k H Hk.
  destruct (nth_error bs (Z.to_nat k)) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  exists b. rewrite (bytes_at_read segs m A bs k 1 H) by lia.
  f_equal. apply nth_error_split in E. destruct E as (l1 & l2 & -> & L).
  rewrite <- L. rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity.
Qed.

Ltac arr_forget UA L :=
  lazymatch type of UA with
  | u8arr _ _ _ (upd_bytes ?bs ?k ?xs) =>
      let L' := fresh "L" in
      assert (L' : length (upd_bytes bs k xs) = length bs)
        by (apply upd_bytes_length; rewrite ?length_le1, ?length_le2, ?length_le4, ?length_le8; cbn [length]; lia);
      rewrite L in L'; clear L; rename L' into L;
      let nb := fresh "bs" in set (nb := upd_bytes bs k xs) in *; clearbody nb
  end.

Ltac arr_store UA L k n := u8_store UA k n; arr_forget UA L.

Section TC.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q lo NB : Z) (m0 : word -> option byte).
  Hypothesis ROOM : (lo <= q - TC_STACK)%Z.
  Hypothesis GTOP : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QNB : (q <= NB)%Z.
  Hypothesis NBHI : (NB + 40 < 2^63)%Z.

  Notation POST := (tochars_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo NB m0).
  Notation INV := (TCINV ra s0 s1 s2 s3 q lo NB m0).
  Notation TCS pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m :=
    (MS (mkR xra (Z_to_bv 64 (q + -80)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).

  Lemma tc_exit : forall e xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (NB < e <= NB + 27)%Z ->
    evt psegs POST (TCS 0x42424 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 e) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HE. tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    do 5 zstep. zstep. zstep.
    pose proof (rw_cells_of_u8arr psegs _ _ _ TA) as TMP. rewrite TL in TMP.
    pose proof (proj2 (num_rw_cells_app psegs m (q + -80) [CB 40 tmp] [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) as J.
    cbn [cells_size csize Nat.add] in J. change (Z.of_nat 40) with 40%Z in J.
    replace (q + -80 + 40)%Z with (q + -40)%Z in J by lia.
    specialize (J (conj TMP FRS)). cbn [app] in J.
    release_frame J ST q.
    pose proof (rw_cells_of_u8arr psegs _ _ _ NA) as NBC. rewrite NL in NBC.
    replace (q + -80)%Z with (q - 80)%Z in MU by lia.
    apply evt_done. unfold tochars_post, TC_STACK.
    do 16 eexists. exists m, e, nb.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FRM|]. split; [exact HE| exact NBC].
  Qed.

  Lemma tc_zero : forall sg xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (0 <= sg <= 1)%Z ->
    evt psegs POST (TCS 0x420a4 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HS. tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    zstep. zstep. zstep.
    arr_store NA NL sg 1%nat.
    arr_store NA NL (sg + 1)%Z 1%nat.
    arr_store NA NL (sg + 2)%Z 1%nat.
    zstep.
    eapply evt_eq; [| eapply (tc_exit (NB + sg + 3)); [tc_close | exact FRM | lia]].
    num_st_eq.
  Qed.

  Definition tc_copy_stmt : Prop :=
    forall n e sg xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (1 <= n <= 20)%Z -> (SF_EMIN <= e <= SF_EMAX)%Z -> (0 <= sg <= 1)%Z ->
    evt psegs POST (TCS 0x4219c xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (e mod 4294967296)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        (Z_to_bv 64 (q + -56 - n)) (Z_to_bv 64 (q + -56)) xt3 xt4 xt5 xt6 F fc m).

  Section Digits.
  Hypothesis KCOPY : tc_copy_stmt.
  Variables (e sg : Z) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis FRM : frm0 fc.
  Hypothesis HE : (SF_EMIN <= e <= SF_EMAX)%Z.
  Hypothesis HSG : (0 <= sg <= 1)%Z.

  Notation DS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 m :=
    (TCS pc xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (e mod 4294967296)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (q + -56)) xt3 xt4 xt5 xt6 F fc m).

  Lemma tc_tail2 : forall (j w : Z) xra xt0 xt1 xt2 xa0 xa2 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 m,
    INV m -> (10 <= w < 100)%Z -> (1 <= j <= 10)%Z ->
    evt psegs POST (DS 0x42164 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 0x18369) xa2 (Z_to_bv 64 w) (Z_to_bv 64 (q + -76 + 2 * j)) xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP QNB NBHI KCOPY FRM HE HSG.
    intros j w xra xt0 xt1 xt2 xa0 xa2 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 m I HW HJ.
    tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    zstep. zstep.
    rewrite shl1. rewrite (swrap32_id (2 * w)) by lia.
    destruct (image_readable_b psegs m 200 0x18369 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TBL & TB).
    destruct (bytes_at_read1 psegs m 0x18369 tb (2 * w) TB ltac:(lia)) as [b0 RD0].
    destruct (bytes_at_read1 psegs m 0x18369 tb (2 * w + 1) TB ltac:(lia)) as [b1 RD1].
    zstep. zstep.
    clear RD0 RD1 TB TBL tb.
    zstep.
    arr_store TA TL (2 * j + 2)%Z 1%nat.
    zstep.
    arr_store TA TL (2 * j + 3)%Z 1%nat.
    eapply evt_eq; [| eapply (KCOPY (22 - 2 * j)%Z e sg); [tc_close | exact FRM | lia | exact HE | exact HSG]].
    num_st_eq.
  Qed.

  Lemma tc_tail1 : forall (j w : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 m,
    INV m -> (0 <= w < 10)%Z -> (1 <= j <= 10)%Z ->
    evt psegs POST (DS 0x42190 xra xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 w) (Z_to_bv 64 (q + -76 + 2 * j)) xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP QNB NBHI KCOPY FRM HE HSG.
    intros j w xra xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xs2 xt3 xt4 xt5 xt6 m I HW HJ.
    tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    zstep. zstep.
    arr_store TA TL (2 * j + 3)%Z 1%nat.
    eapply evt_eq; [| eapply (KCOPY (21 - 2 * j)%Z e sg); [tc_close | exact FRM | lia | exact HE | exact HSG]].
    num_st_eq.
  Qed.

  Lemma tc_loop : forall (f : nat) (j w : Z) xra xt0 xt1 xt2 xa3 xa4 xs2 xt3 xt4 xt5 xt6 m,
    INV m -> (100 <= w < 100 ^ j)%Z -> (w < 18446744073709551616)%Z -> (j <= 10)%Z -> (j <= Z.of_nat f)%Z ->
    evt psegs POST (DS 0x4211c xra xt0 xt1 xt2 (Z_to_bv 64 w) (Z_to_bv 64 0x18369) (Z_to_bv 64 100) xa3 xa4 (Z_to_bv 64 DIV100_MAGIC)
                       (Z_to_bv 64 624) (Z_to_bv 64 (q + -76 + 2 * j)) xs2 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP QNB NBHI KCOPY FRM HE HSG.
    induction f as [|f IH]; intros j w xra xt0 xt1 xt2 xa3 xa4 xs2 xt3 xt4 xt5 xt6 m I HW W64 HJ HF.
    { exfalso. pose proof (pow100_ge2 w j HW). lia. }
    pose proof (pow100_ge2 w j HW) as J2.
    pose proof (pow100_step w j ltac:(lia) ltac:(lia)) as HQ.
    tc_open I.
    unfold TC_STACK, GLOBALS_TOP, DIV100_MAGIC in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    zstep. zstep. zstep.
    change 2951479051793528259%Z with DIV100_MAGIC. rewrite (div100_machine w) by lia.
    zstep. zstep. zstep. zstep.
    replace (w - w / 100 * 100)%Z with (w mod 100)%Z by (Z.div_mod_to_equations; lia).
    assert (R100 : (0 <= w mod 100 < 100)%Z) by (apply Z.mod_pos_bound; lia).
    set (r := (w mod 100)%Z) in *.
    rewrite (swrap32_id r) by lia. rewrite (Z.mod_small r) by lia. rewrite shl1. rewrite (swrap32_id (2 * r)) by lia.
    destruct (image_readable_b psegs m 200 0x18369 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TBL & TB).
    destruct (bytes_at_read1 psegs m 0x18369 tb (2 * r) TB ltac:(lia)) as [b0 RD0].
    destruct (bytes_at_read1 psegs m 0x18369 tb (2 * r + 1) TB ltac:(lia)) as [b1 RD1].
    zstep. zstep.
    clear RD0 RD1 TB TBL tb.
    zstep. zstep.
    arr_store TA TL (2 * j + 2)%Z 1%nat.
    arr_store TA TL (2 * j + 3)%Z 1%nat.
    zstep. zstep.
    zstep. if_cases K; zify_cond K.
    -
      assert (W4 : (10000 <= w)%Z).
      { rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 4)%Z with 16%Z in K. Z.div_mod_to_equations. lia. }
      eapply evt_eq; [| eapply (IH (j - 1)%Z (w / 100)%Z); [tc_close | | | lia | lia]].
      + num_st_eq.
      + split; [Z.div_mod_to_equations; lia| lia].
      + Z.div_mod_to_equations; lia.
    - assert (W4 : (w < 10000)%Z).
      { rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 4)%Z with 16%Z in K. Z.div_mod_to_equations. lia. }
      assert (Q100 : (0 <= w / 100 < 100)%Z) by (Z.div_mod_to_equations; lia).
      zstep.
      zstep. if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply (tc_tail1 (j - 1)%Z (w / 100)%Z); [tc_close | lia | lia]].
        num_st_eq.
      + eapply evt_eq; [| eapply (tc_tail2 (j - 1)%Z (w / 100)%Z); [tc_close | lia | lia]].
        num_st_eq.
  Qed.

  Lemma tc_digits : forall (wd : word) xra xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 m,
    INV m ->
    evt psegs POST (TCS 0x420f4 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) xs1 wd (Z_to_bv 64 (e mod 4294967296)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI KCOPY FRM HE HSG.
    intros wd xra xt0 xt1 xt2 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 m I.
    pose proof (bv_unsigned_in_range 64 wd) as WR. unfold bv_modulus in WR. cbn in WR.
    rewrite <- (Z_to_bv_bv_unsigned wd). set (w := bv_unsigned wd) in *. clearbody w.
    pose proof I as I0. tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    do 5 zstep.
    zstep. if_cases K; zify_cond K.
    -
      do 3 zstep.
      zstep. if_cases K2; zify_cond K2.
      + eapply evt_eq; [| eapply (tc_tail2 10%Z w); [exact I0 | lia | lia]].
        num_st_eq.
      + eapply evt_eq; [| eapply (tc_tail1 10%Z w); [exact I0 | lia | lia]].
        num_st_eq.
    - do 4 zstep.
      eapply evt_eq; [| eapply (tc_loop 10%nat 10%Z w); [exact I0 | | lia | lia | lia]].
      + num_st_eq.
      + change (100 ^ 10)%Z with 100000000000000000000%Z. lia.
  Qed.
  End Digits.
End TC.
