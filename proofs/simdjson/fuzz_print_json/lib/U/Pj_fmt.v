(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP StoreFast SysStep SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_num_defs Pj_tochars_defs Pj_tochars_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

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

Ltac gref G := exfalso; rewrite ?unsigned_lit in G by lia; rewrite ?signed_of_Z in G by lia; lia.
Ltac gtrap := let G := fresh "G" in zstep; if_cases G; zify_cond G; [gref G|]; try clear G.
Ltac gfall := let G := fresh "G" in zstep; if_cases G; zify_cond G; [|gref G]; try clear G.

Lemma b2z_pos : forall x, (0 < x)%Z -> Z.b2z (0 <? x) = 1%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, (0 < x)%Z -> Z.b2z (x <? 1) = 0%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Lemma slti0_nonneg : forall x, (0 <= x < 9223372036854775808)%Z -> Z.b2z (Z.lxor x 9223372036854775808 <? 9223372036854775808) = 0%Z.
Proof.
  intros x H. change 9223372036854775808%Z with (2^63)%Z. rewrite ZBridge.zb_lxor_pow2_small by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma b2z_ltu_false : forall a b, (b <= a)%Z -> Z.b2z (a <? b) = 0%Z.
Proof. intros a b H. rewrite (proj2 (Z.ltb_ge a b) H). reflexivity. Qed.

Ltac uov := rewrite ?slti0_nonneg by lia; rewrite ?b2z_ltu_false by lia; change (Z.lxor (Z.lxor 0 0) 1) with 1%Z.

Ltac unot := rewrite ?ZBridge.zb_lxor_ones by lia.

Ltac scond H := unfold bv_lts in H; rewrite ?signed_of_Z in H by lia; zify_bool H.

Section FM.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (p lo NB sg : Z) (m0 : word -> option byte).
  Hypothesis ROOM : (lo <= p - FMT_STACK)%Z.
  Hypothesis GTOP : (GLOBALS_TOP <= lo)%Z.
  Hypothesis PNB : (p <= NB)%Z.
  Hypothesis NBHI : (NB + 40 < 2^63)%Z.
  Hypothesis HSG : (0 <= sg <= 1)%Z.

  Notation POST := (fmt_post ra p gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo NB sg m0).
  Notation FMS pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 m :=
    (MS (mkR xra (Z_to_bv 64 (p + -80)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Definition FMINV (m : word -> option byte) : Prop :=
    rw_cells usegs m (p + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    (exists tmp, u8arr usegs m (p + -80) tmp /\ length tmp = 32%nat) /\
    (exists nb, u8arr usegs m NB nb /\ length nb = 40%nat) /\
    mem_inv usegs m /\ munch [(p + -80, p); (NB, NB + 40)]%Z m0 m /\ wmono usegs m0 m /\ stk usegs m lo (p + -80).

  Ltac fm_open H :=
    let tmp := fresh "tmp" in let nb := fresh "nb" in
    destruct H as (FRS & (tmp & TA & TL) & (nb & NA & NL) & MI & MU & WM & ST);
    unfold FMT_STACK, GLOBALS_TOP in *;
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
  Ltac fm_close :=
    lazymatch goal with
    | |- FMINV _ =>
        split; [eassumption|]; split; [eexists; split; eassumption|]; split; [eexists; split; eassumption|];
        split; [assumption|]; split; [assumption|]; split; assumption
    end.

  Lemma fm_exit : forall e xra xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 m,
    FMINV m -> (NB + sg < e <= NB + sg + 26)%Z ->
    evt usegs POST (FMS 0x40a48 xra xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 e) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HE. fm_open I.
    do 6 zstep. zstep. zstep.
    lazymatch type of TA with u8arr _ ?mm _ ?tb =>
      pose proof (rw_cells_of_u8arr usegs _ _ _ TA) as TMP; rewrite TL in TMP;
      pose proof (proj2 (num_rw_cells_app usegs mm (p + -80)%Z [CB 32 tb] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) as J;
      cbn [cells_size csize Nat.add] in J; change (Z.of_nat 32) with 32%Z in J;
      replace (p + -80 + 32)%Z with (p + -48)%Z in J by lia;
      specialize (J (conj TMP FRS)); cbn [app] in J
    end.
    release_frame J ST p.
    replace (p + -80)%Z with (p - 80)%Z in MU by lia.
    apply evt_done. unfold fmt_post.
    do 14 eexists. eexists. exists e. eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact HE|].
    split; [exact NA| exact NL].
  Qed.

  Lemma fm_exit2 : forall d xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 m,
    FMINV m -> (0 < d <= 26)%Z ->
    evt usegs POST (FMS 0x40a44 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) xs1 (Z_to_bv 64 d) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HD.
    zstep.
    eapply evt_eq; [| eapply (fm_exit (NB + sg + d)%Z); [exact I | lia]].
    num_st_eq.
  Qed.

  Lemma fm_lay1 : forall n pt xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 m,
    FMINV m -> (1 <= n)%Z -> (n <= pt <= 15)%Z ->
    evt usegs POST (FMS 0x40830 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 pt) xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HN HP. fm_open I.

    zstep. zstep. zstep.
    unz.
    zstep. if_false.

    zstep. zstep. zstep. zstep.
    uov.
    zstep. if_false.

    zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 (NB + sg + n)) with (Z_to_bv 64 (NB + (sg + n))) by (f_equal; lia).
    arr_call arr_memset NA NL.

    zstep. zstep. unz.
    zstep. if_false.

    zstep. zstep. zstep. zstep. uov.
    zstep. if_false.
    gtrap.

    zstep. zstep.
    rewrite (swrap32_id (pt + 1)) by lia.
    arr_store NA NL (sg + pt)%Z 1%nat.
    gtrap.

    zstep.
    gtrap.
    zstep. zstep. zstep. zstep. uov.
    zstep. if_false.

    zstep. zstep. unot.
    arr_store NA NL (sg + pt + 1)%Z 1%nat.
    gtrap.
    zstep.
    gtrap.
    zstep. zstep.
    eapply evt_eq; [| eapply (fm_exit (NB + sg + pt + 2)%Z); [fm_close | lia]].
    num_st_eq.
  Qed.

  Lemma fm_lay2 : forall n pt xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 m,
    FMINV m -> (1 <= n <= 20)%Z -> (1 <= pt <= 15)%Z ->
    evt usegs POST (FMS 0x408dc xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 pt) xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HN HP. fm_open I.

    gtrap.
    zstep.
    gtrap.
    gtrap.
    zstep. unot.
    gtrap.

    zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 (NB + sg + pt + 1)) with (Z_to_bv 64 (NB + (sg + pt) + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (NB + sg + pt)) with (Z_to_bv 64 (NB + (sg + pt))) by (f_equal; lia).
    arr_call arr_memmove1 NA NL.

    zstep. zstep.
    arr_store NA NL (sg + pt)%Z 1%nat.
    gfall.
    eapply evt_eq; [| eapply (fm_exit2 (n + 1)%Z); [fm_close | lia]].
    num_st_eq.
  Qed.

  Lemma fm_lay3 : forall n pt xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 m,
    FMINV m -> (1 <= n <= 20)%Z -> (-3 <= pt <= 0)%Z ->
    evt usegs POST (FMS 0x40920 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 pt) xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HN HP. fm_open I.
    arr_load NA (sg + 8)%Z. arr_load NA (sg + 9)%Z. arr_load NA (sg + 10)%Z. arr_load NA (sg + 11)%Z.
    arr_load NA (sg + 12)%Z. arr_load NA (sg + 13)%Z. arr_load NA (sg + 14)%Z. arr_load NA (sg + 15)%Z.
    do 5 zstep.
    arr_load NA (sg + 0)%Z. arr_load NA (sg + 1)%Z. arr_load NA (sg + 2)%Z. arr_load NA (sg + 3)%Z.
    do 9 zstep.
    arr_load NA (sg + 4)%Z. arr_load NA (sg + 5)%Z.
    zstep.
    arr_load NA (sg + 6)%Z. arr_load NA (sg + 7)%Z.
    do 9 zstep.
    arr_load NA (sg + 16)%Z.
    do 6 zstep.

    arr_store TA TL 8%Z 8%nat.
    arr_store TA TL 16%Z 8%nat.
    arr_store TA TL 24%Z 1%nat.
    arr_store NA NL (sg + 0)%Z 1%nat.
    gtrap.

    zstep. zstep.
    arr_store NA NL (sg + 1)%Z 1%nat.
    gtrap.

    zstep.
    replace (bv_swrap 32 (0 - Z.land pt 18446744073709551615)) with (- pt)%Z
      by (assert (pt = -3 \/ pt = -2 \/ pt = -1 \/ pt = 0)%Z as [->|[->|[->| ->]]] by lia; reflexivity).
    zstep. zstep. zstep. unot.
    arr_store NA NL (sg + 2)%Z 1%nat. arr_store NA NL (sg + 3)%Z 1%nat.
    arr_store NA NL (sg + 4)%Z 1%nat. arr_store NA NL (sg + 5)%Z 1%nat.
    gtrap.

    zstep. zstep. zstep. zstep.
    lazymatch type of TA with
    | u8arr _ ?mm _ ?tb =>
        pose proof (bytes_at_sub usegs mm (p + -80) tb 8 17 (proj1 TA) ltac:(rewrite TL; lia)) as SRC;
        assert (LS : length (firstn 17 (skipn 8 tb)) = 17%nat) by (rewrite length_firstn, length_skipn; lia);
        set (src17 := firstn 17 (skipn 8 tb)) in *; clearbody src17
    end.
    replace (p + -80 + Z.of_nat 8)%Z with (p + -72)%Z in SRC by lia.
    replace (Z_to_bv 64 (NB + sg + 2 + - pt)) with (Z_to_bv 64 (NB + (sg + 2 - pt))) by (f_equal; lia).
    arr_call arr_memcpy NA NL.
    clear SRC.

    zstep. zstep. zstep. unot.
    gtrap.
    eapply evt_eq; [| eapply (fm_exit2 (n - pt + 2)%Z); [fm_close | lia]].
    num_st_eq.
  Qed.

  Lemma fm_exp : forall d pt xra xt0 xt1 xt2 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 m,
    FMINV m -> (1 <= d <= 21)%Z -> (-400 <= pt <= 400)%Z ->
    evt usegs POST (FMS 0x40ab0 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) xs1 (Z_to_bv 64 d) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 pt) xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HD HP.

    assert (K2 : forall ya1 ya3 ya4 ya5 m', FMINV m' ->
              evt usegs POST (FMS 0x40b24 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + d)) xs1 (Z_to_bv 64 (NB + sg + d + 3)) ya1 (Z_to_bv 64 (NB + sg + d + 2)) ya3 ya4 ya5 xa6 xa7
                                  xs2 (Z_to_bv 64 pt) xs4 xt3 xt4 xt5 xt6 m')).
    { intros ya1 ya3 ya4 ya5 m' I'. fm_open I'.

      zstep.
      gtrap.
      do 5 zstep.
      arr_store NA NL (sg + d + 2)%Z 1%nat.
      gtrap.

      do 5 zstep.
      arr_store NA NL (sg + d + 3)%Z 1%nat.
      zstep.
      eapply evt_eq; [| eapply (fm_exit (NB + sg + d + 4)%Z); [fm_close | lia]].
      num_st_eq. }

    assert (K3 : forall ya1 ya3 ya4 ya5 m', FMINV m' ->
              evt usegs POST (FMS 0x40b64 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + d)) xs1 (Z_to_bv 64 (NB + sg + d + 3)) ya1 (Z_to_bv 64 (NB + sg + d + 2)) ya3 ya4 ya5 xa6 xa7
                                  xs2 (Z_to_bv 64 pt) xs4 xt3 xt4 xt5 xt6 m')).
    { intros ya1 ya3 ya4 ya5 m' I'. fm_open I'.

      zstep.
      gtrap.
      do 7 zstep.
      arr_store NA NL (sg + d + 2)%Z 1%nat.
      gtrap.

      do 10 zstep.
      arr_store NA NL (sg + d + 3)%Z 1%nat.
      gtrap.

      do 6 zstep.
      arr_store NA NL (sg + d + 4)%Z 1%nat.
      zstep.
      eapply evt_eq; [| eapply (fm_exit (NB + sg + d + 5)%Z); [fm_close | lia]].
      num_st_eq. }

    assert (KJ : forall ya0 ya1 ya2 ya3 m', FMINV m' ->
              evt usegs POST (FMS 0x40b0c xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg + d)) xs1 ya0 ya1 ya2 ya3 xa4 xa5 xa6 xa7
                                  xs2 (Z_to_bv 64 pt) xs4 xt3 xt4 xt5 xt6 m')).
    { intros ya0 ya1 ya2 ya3 m' I'. pose proof I' as I0. fm_open I'.

      zstep.
      arr_store NA NL (sg + d + 1)%Z 1%nat.
      zstep. zstep. zstep.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply K3; fm_close]. num_st_eq.
      - eapply evt_eq; [| eapply K2; fm_close]. num_st_eq. }
    clear K2 K3.
    fm_open I.

    zstep. zstep.
    gtrap.
    zstep. zstep.
    rewrite land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
    rewrite (sw32_mod64_add pt (-1)) by lia.
    arr_store NA NL (sg + d)%Z 1%nat.
    gtrap.

    zstep. if_cases K.
    -
      zstep. zstep.
      assert (PN : (pt + -1 < 0)%Z).
      { unfold bv_lts in K. rewrite signed_of_Z in K by lia. change (bv_signed (Z_to_bv 64 0)) with 0%Z in K. apply Z.ltb_lt in K. exact K. }
      clear K.
      replace (Z.land (pt + -1) 18446744073709551615) with (pt + -1 + 18446744073709551616)%Z
        by (rewrite land_W64; change (2 ^ 64)%Z with 18446744073709551616%Z; Z.div_mod_to_equations; lia).
      replace (bv_swrap 32 (0 - (pt + -1 + 18446744073709551616))) with (1 - pt)%Z by (rewrite swrap32_Z; Z.div_mod_to_equations; lia).
      replace (Z_to_bv 64 (0 + - (pt + -1 + 18446744073709551616))) with (Z_to_bv 64 (1 - pt)) by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
      zstep. if_false.

      zstep. zstep. zstep. zstep.
      gtrap.
      eapply evt_eq; [| eapply KJ; fm_close]. num_st_eq.
    -
      clear K.
      zstep. zstep. zstep. zstep. zstep.
      gfall.
      eapply evt_eq; [| eapply KJ; fm_close]. num_st_eq.
  Qed.

  Lemma fm_lay4 : forall n pt xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 m,
    FMINV m -> (1 <= n <= 20)%Z -> (-400 <= pt <= 400)%Z ->
    evt usegs POST (FMS 0x40a68 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 pt) xs4 xt3 xt4 xt5 xt6 m).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until m. intros I HN HP. pose proof I as I0. fm_open I.

    zstep.
    zstep. if_cases K; zify_cond K.
    -
      zstep. zstep.
      gtrap.
      zstep. zstep. zstep.
      replace (Z_to_bv 64 (NB + sg + 2)) with (Z_to_bv 64 (NB + (sg + 1) + 1)) by (f_equal; lia).
      replace (Z_to_bv 64 (NB + sg + 1)) with (Z_to_bv 64 (NB + (sg + 1))) by (f_equal; lia).
      arr_call arr_memmove1 NA NL.

      zstep.
      arr_store NA NL (sg + 1)%Z 1%nat.
      gtrap.
      zstep. zstep. unot.
      gtrap.
      eapply evt_eq; [| eapply (fm_exp (n + 1)%Z pt); [fm_close | lia | lia]].
      num_st_eq.
    -
      zstep. zstep.
      gfall.
      eapply evt_eq; [| eapply (fm_exp 1%Z pt); [exact I0 | lia | lia]].
      num_st_eq.
  Qed.

  Lemma fmt_body : forall n e t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 (nb : list byte),
    stk usegs m0 lo p -> mem_inv usegs m0 -> (1 <= n <= 20)%Z -> (SF_EMIN <= e <= SF_EMAX)%Z ->
    u8arr usegs m0 NB nb -> length nb = 40%nat ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) (Z_to_bv 64 e) (Z_to_bv 64 (-4)) (Z_to_bv 64 15) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x407f8) fc None m0 (seg_rom usegs)).
  Proof using ROOM GTOP PNB NBHI HSG.
    intros until nb. intros ST MI HN HE NA NL.
    pose proof fm_lay1 as KL1. pose proof fm_lay2 as KL2. pose proof fm_lay3 as KL3. pose proof fm_lay4 as KL4.
    pose proof ROOM as ROOM'. pose proof GTOP as GTOP'. unfold FMT_STACK, GLOBALS_TOP in ROOM', GTOP'. unfold SF_EMIN, SF_EMAX in HE.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    pose proof (munch_refl [(p + -80, p); (NB, NB + 40)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    zstep. carve_frame 80%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [32;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    do 6 zstep.
    apply (proj1 (num_rw_cells_app usegs _ _ [CB 32 (firstn 32 junk)] _)) in FR. destruct FR as [TMP FRS].
    cbn [cells_size csize Nat.add] in FRS. change (Z.of_nat 32) with 32%Z in FRS.
    replace (p + -80 + 32)%Z with (p + -48)%Z in FRS by lia.
    pose proof (u8arr_of_rw_cells usegs _ _ _ _ TMP) as TA.
    assert (TL : length (firstn 32 junk) = 32%nat) by (destruct TMP as [[Hwf _] _]; cbn in Hwf; tauto).
    clear TMP. set (tmp := firstn 32 junk) in *. clearbody tmp.

    zstep. zstep.
    replace (bv_swrap 32 (n + Z.land e 18446744073709551615)) with (n + e)%Z
      by (rewrite land_W64; change (2 ^ 64)%Z with 18446744073709551616%Z; rewrite swrap32_Z; Z.div_mod_to_equations; lia).
    zstep. if_false.
    assert (I0 : FMINV m1) by fm_close.
    clear FRS TA TL NA NL.

    zstep. zstep.
    assert (K87c : forall ya0 ya1 ya2,
              evt usegs POST (FMS 0x408d4 ra t0 t1 t2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) ya0 ya1 ya2 (Z_to_bv 64 (-4)) (Z_to_bv 64 15) a5 a6 a7
                                  s2 (Z_to_bv 64 (n + e)) s4 t3 t4 t5 t6 m1)).
    { intros ya0 ya1 ya2.
      assert (K8c0 : evt usegs POST (FMS 0x40918 ra t0 t1 t2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 n) ya0 ya1 ya2 (Z_to_bv 64 (-4)) (Z_to_bv 64 15) a5 a6 a7
                                  s2 (Z_to_bv 64 (n + e)) s4 t3 t4 t5 t6 m1)).
      {
        zstep. if_cases K; scond K.
        { eapply evt_eq; [| eapply (KL4 n (n + e)%Z); [exact I0 | lia | lia]]. num_st_eq. }
        zstep. if_cases K'; scond K'.
        { eapply evt_eq; [| eapply (KL4 n (n + e)%Z); [exact I0 | lia | lia]]. num_st_eq. }
        eapply evt_eq; [| eapply (KL3 n (n + e)%Z); [exact I0 | lia | ]]. num_st_eq.
        lia. }

      zstep. if_cases K; scond K.
      { exact K8c0. }
      zstep. if_cases K'; scond K'.
      { exact K8c0. }
      eapply evt_eq; [| eapply (KL2 n (n + e)%Z); [exact I0 | lia | ]]. num_st_eq.
      lia. }
    zstep. if_cases K1; scond K1.
    { eapply evt_eq; [| eapply K87c]. num_st_eq. }
    zstep. if_cases K2; scond K2.
    { eapply evt_eq; [| eapply K87c]. num_st_eq. }
    eapply evt_eq; [| eapply (KL1 n (n + e)%Z); [exact I0 | lia | ]]. num_st_eq.
    lia.
  Qed.
End FM.

Theorem fmt_proof : fmt_stmt.
Proof.
  unfold fmt_stmt. intros until nb. intros ST ROOM GTOP MI PNB NBHI HSG HN HE NA NL. unfold FMT_ENTRY.
  eapply fmt_body; eassumption.
Qed.
