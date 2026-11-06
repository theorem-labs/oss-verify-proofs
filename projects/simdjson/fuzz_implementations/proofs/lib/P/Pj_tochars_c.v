(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes FP StoreFast SysStep SFModel.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Str_tac Sj_num_kit Pj_num_defs Pj_tochars_a Pj_tochars_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac arr_load UA k :=
  lazymatch type of UA with
  | u8arr ?segs ?m ?A ?bs =>
      let b := fresh "b" in let RD := fresh "RD" in
      destruct (u8arr_read1 segs m A bs k UA ltac:(lia)) as [b RD];
      zstep; clear RD
  end.

Ltac arr_call SPEC UA L :=
  call SPEC; [ exact UA | first [eassumption | rewrite ?L; lia] .. | ];
  try clear UA;
  lazymatch goal with
  | Lx : length ?bs' = length ?bs, Ux : u8arr _ _ _ ?bs' |- _ =>
      rewrite L in Lx; clear L; rename Lx into L; rename Ux into UA; try clear bs
  end.

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
  Notation EXIT := (tc_exit ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q lo NB m0 ROOM GTOP QNB NBHI).

  Lemma tc_lay1 : forall n pt sg xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (1 <= n)%Z -> (n <= pt <= 15)%Z -> (0 <= sg <= 1)%Z ->
    evt psegs POST (TCS 0x421cc xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 pt) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 n) xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HN HP HS. tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    do 4 zstep. zstep.
    replace (Z_to_bv 64 (NB + sg + n)) with (Z_to_bv 64 (NB + (sg + n))) by (f_equal; lia).
    arr_call arr_memset NA NL.
    zstep. zstep.
    arr_store NA NL (sg + pt)%Z 1%nat.
    arr_store NA NL (sg + pt + 1)%Z 1%nat.
    zstep. zstep.
    eapply evt_eq; [| eapply (EXIT (NB + sg + pt + 2)%Z); [tc_close | exact FRM | lia]].
    num_st_eq.
  Qed.

  Lemma tc_lay2 : forall n pt sg xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (1 <= n <= 20)%Z -> (1 <= pt <= 15)%Z -> (0 <= sg <= 1)%Z ->
    evt psegs POST (TCS 0x42318 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 pt) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 n) xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HN HP HS. tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    do 4 zstep. zstep.
    replace (Z_to_bv 64 (NB + sg + pt + 1)) with (Z_to_bv 64 (NB + (sg + pt) + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (NB + sg + pt)) with (Z_to_bv 64 (NB + (sg + pt))) by (f_equal; lia).
    arr_call arr_memmove1 NA NL.
    zstep. zstep.
    arr_store NA NL (sg + pt)%Z 1%nat.
    zstep. zstep.
    eapply evt_eq; [| eapply (EXIT (NB + sg + n + 1)%Z); [tc_close | exact FRM | lia]].
    num_st_eq.
  Qed.

  Lemma tc_exp : forall c (pt : word) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (0 <= c <= 21)%Z ->
    evt psegs POST (TCS 0x42364 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + c)) pt xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HC.
    assert (KF : forall d ya1 ya2 ya3 m', INV m' -> (5 <= d <= 6)%Z ->
              evt psegs POST (TCS 0x42418 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + c)) pt (Z_to_bv 64 (NB + c + d)) ya1 ya2 ya3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m')).
    { intros d ya1 ya2 ya3 m' I' HD. tc_open I'.
      unfold TC_STACK, GLOBALS_TOP in *.
      pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
      zstep.
      arr_store NA NL (c + 3)%Z 1%nat.
      arr_store NA NL (c + 4)%Z 1%nat.
      eapply evt_eq; [| eapply (EXIT (NB + c + d)%Z); [tc_close | exact FRM | lia]].
      num_st_eq. }
    assert (K2 : forall ya0 ya1 ya2 ya3 m', INV m' ->
              evt psegs POST (TCS 0x423f4 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + c)) pt ya0 ya1 ya2 ya3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m')).
    { intros ya0 ya1 ya2 ya3 m' I'.
      do 9 zstep.
      eapply evt_eq; [| eapply (KF 5%Z); [exact I' | lia]].
      num_st_eq. }
    assert (K3 : forall ya0 ya1 ya2 ya3 m', INV m' ->
              evt psegs POST (TCS 0x42390 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + c)) pt ya0 ya1 ya2 ya3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 F fc m')).
    { intros ya0 ya1 ya2 ya3 m' I'. pose proof I' as I0. tc_open I'.
      unfold TC_STACK, GLOBALS_TOP in *.
      pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
      do 19 zstep.
      arr_store NA NL (c + 5)%Z 1%nat.
      zstep.
      eapply evt_eq; [| eapply (KF 6%Z); [tc_close | lia]].
      num_st_eq. }
    tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    zstep. zstep.
    arr_store NA NL (c + 1)%Z 1%nat.
    zstep. zstep. zstep.
    zstep. if_cases K.
    -
      zstep. zstep.
      arr_store NA NL (c + 2)%Z 1%nat.
      zstep. if_cases KK.
      + eapply evt_eq; [| eapply K3; tc_close]. num_st_eq.
      + eapply evt_eq; [| eapply K2; tc_close]. num_st_eq.
    - zstep. zstep.
      arr_store NA NL (c + 2)%Z 1%nat.
      zstep. if_cases KK.
      + eapply evt_eq; [| eapply K2; tc_close]. num_st_eq.
      + eapply evt_eq; [| eapply K3; tc_close]. num_st_eq.
  Qed.

  Lemma tc_lay4 : forall n (pt : word) sg xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (1 <= n <= 20)%Z -> (0 <= sg <= 1)%Z ->
    evt psegs POST (TCS 0x42340 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) pt xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 n) xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HN HS. pose proof I as I0. tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    zstep.
    zstep. if_cases K; zify_cond K.
    -
      eapply evt_eq; [| eapply (tc_exp sg); [exact I0 | exact FRM | lia]].
      num_st_eq.
    - do 3 zstep. zstep.
      replace (Z_to_bv 64 (NB + sg + 2)) with (Z_to_bv 64 (NB + (sg + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (NB + sg + 1)) with (Z_to_bv 64 (NB + (sg + 1))) by (f_equal; lia).
      arr_call arr_memmove1 NA NL.
      zstep.
      arr_store NA NL (sg + 1)%Z 1%nat.
      zstep.
      eapply evt_eq; [| eapply (tc_exp (sg + n)%Z); [tc_close | exact FRM | lia]].
      num_st_eq.
  Qed.

  Lemma tc_lay3 : forall n pt sg xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    INV m -> frm0 fc -> (1 <= n <= 20)%Z -> (-3 <= pt <= 0)%Z -> (0 <= sg <= 1)%Z ->
    evt psegs POST (TCS 0x42210 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 pt) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 n) xs3 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HN HP HS. tc_open I.
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    arr_load NA (sg + 8)%Z. arr_load NA (sg + 9)%Z. arr_load NA (sg + 10)%Z. arr_load NA (sg + 11)%Z.
    arr_load NA (sg + 0)%Z. arr_load NA (sg + 1)%Z. arr_load NA (sg + 2)%Z. arr_load NA (sg + 3)%Z.
    arr_load NA (sg + 4)%Z. arr_load NA (sg + 5)%Z. arr_load NA (sg + 6)%Z. arr_load NA (sg + 7)%Z.
    zstep. zstep.
    arr_store NA NL (sg + 4)%Z 1%nat. arr_store NA NL (sg + 5)%Z 1%nat. arr_store NA NL (sg + 0)%Z 1%nat.
    arr_store NA NL (sg + 1)%Z 1%nat. arr_store NA NL (sg + 2)%Z 1%nat. arr_store NA NL (sg + 3)%Z 1%nat.
    do 4 zstep.
    arr_load NA (sg + 12)%Z. arr_load NA (sg + 13)%Z.
    zstep.
    arr_load NA (sg + 14)%Z. arr_load NA (sg + 15)%Z.
    do 21 zstep.
    arr_load NA (sg + 16)%Z.
    zstep.
    replace (bv_swrap 32 (0 - Z.land pt 18446744073709551615)) with (- pt)%Z
      by (assert (pt = -3 \/ pt = -2 \/ pt = -1 \/ pt = 0)%Z as [->|[->|[->| ->]]] by lia; reflexivity).
    do 3 zstep.
    arr_store TA TL 0%Z 8%nat.
    arr_store TA TL 8%Z 8%nat.
    arr_store TA TL 16%Z 1%nat.
    do 3 zstep. zstep.
    lazymatch type of TA with
    | u8arr _ ?mm _ ?tb =>
        pose proof (bytes_at_sub psegs mm (q + -80) tb 0 17 (proj1 TA) ltac:(rewrite TL; lia)) as SRC;
        assert (LS : length (firstn 17 (skipn 0 tb)) = 17%nat) by (rewrite length_firstn, length_skipn; lia);
        set (src17 := firstn 17 (skipn 0 tb)) in *; clearbody src17
    end.
    replace (q + -80 + Z.of_nat 0)%Z with (q + -80)%Z in SRC by lia.
    replace (Z_to_bv 64 (NB + sg + 2 + - pt)) with (Z_to_bv 64 (NB + (sg + 2 - pt))) by (f_equal; lia).
    arr_call arr_memcpy NA NL.
    clear SRC.
    do 3 zstep. zstep.
    eapply evt_eq; [| eapply (EXIT (NB + sg + n - pt + 2)%Z); [tc_close | exact FRM | lia]].
    num_st_eq.
  Qed.

  Theorem tc_copy_proof : tc_copy_stmt ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q lo NB m0.
  Proof using ROOM GTOP QNB NBHI.
    unfold tc_copy_stmt. intros until m. intros I FRM HN HE HS. tc_open I.
    unfold TC_STACK, GLOBALS_TOP, SF_EMIN, SF_EMAX in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    do 3 zstep. zstep.
    pose proof (bytes_at_sub psegs m (q + -80) tmp (Z.to_nat (24 - n)) 16 (proj1 TA) ltac:(rewrite TL; lia)) as SRC.
    assert (LS : length (firstn 16 (skipn (Z.to_nat (24 - n)) tmp)) = 16%nat) by (rewrite length_firstn, length_skipn; lia).
    set (src16 := firstn 16 (skipn (Z.to_nat (24 - n)) tmp)) in *. clearbody src16.
    replace (q + -80 + Z.of_nat (Z.to_nat (24 - n)))%Z with (q + -56 - n)%Z in SRC by lia.
    arr_call arr_memcpy NA NL.
    clear SRC.
    arr_load TA (40 - n)%Z.
    zstep. zstep.
    replace (bv_swrap 32 (q + -56 - (q + -56 - n))) with n
      by (replace (q + -56 - (q + -56 - n))%Z with n by lia; symmetry; apply swrap32_id; lia).
    replace (bv_swrap 32 (e mod 4294967296 + 0)) with e by (rewrite swrap32_Z; Z.div_mod_to_equations; lia).
    arr_store NA NL (sg + 16)%Z 1%nat.
    zstep.
    replace (bv_swrap 32 (n + e mod 4294967296)) with (n + e)%Z by (rewrite swrap32_Z; symmetry; apply sw32_add_mod32; lia).
    assert (K904 : forall ya0 ya1 m', INV m' ->
              evt psegs POST (TCS 0x421f8 (Z_to_bv 64 0x421ac) x x0 x1 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (n + e)) ya0 ya1 x3 x4 x5 x6 x7 x8
                                  (Z_to_bv 64 n) (Z_to_bv 64 (q + -56)) x9 x10 x11 x12 F fc m')).
    { intros ya0 ya1 m' I'.
      zstep. zstep.
      rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
      rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
      rewrite (sw32_mod64_add (n + e) (-16)) by lia.
      zstep. if_cases K; zify_cond K; rewrite land_W64 in K; change (2 ^ 64)%Z with 18446744073709551616%Z in K.
      {
        assert (P1 : (1 <= n + e <= 15)%Z) by (Z.div_mod_to_equations; lia). clear K.
        eapply evt_eq; [| eapply (tc_lay2 n (n + e)%Z sg); [exact I' | exact FRM | lia | lia | lia]].
        num_st_eq. }
      assert (P1 : (n + e <= 0 \/ 16 <= n + e)%Z) by (Z.div_mod_to_equations; lia). clear K.
      zstep. zstep.
      rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
      rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
      rewrite (sw32_mod64_add (n + e) 3) by lia.
      zstep. if_cases K; zify_cond K; rewrite land_W64 in K; change (2 ^ 64)%Z with 18446744073709551616%Z in K.
      { eapply evt_eq; [| eapply (tc_lay4 n (Z_to_bv 64 (n + e)) sg); [exact I' | exact FRM | lia | lia]].
        num_st_eq. }
      assert (P3 : (-3 <= n + e <= 0)%Z) by (Z.div_mod_to_equations; lia). clear K.
      eapply evt_eq; [| eapply (tc_lay3 n (n + e)%Z sg); [exact I' | exact FRM | lia | lia | lia]].
      num_st_eq. }
    zstep. if_cases K1; zify_cond K1; rewrite land_W64 in K1; change (2 ^ 64)%Z with 18446744073709551616%Z in K1.
    { eapply evt_eq; [| eapply K904; tc_close]. num_st_eq. }

    assert (E0 : (0 <= e)%Z) by (Z.div_mod_to_equations; lia). clear K1.
    zstep.
    zstep. if_cases K2; zify_cond K2; rewrite signed_of_Z in K2 by lia.
    { eapply evt_eq; [| eapply K904; tc_close]. num_st_eq. }
    eapply evt_eq; [| eapply (tc_lay1 n (n + e)%Z sg); [tc_close | exact FRM | lia | lia | lia]].
    num_st_eq.
  Qed.
End TC.
