(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig SjPjBeta.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_num_defs Pj_sf_a Pj_sf_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Section SF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv usegs m.

  Notation POST := (sf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m).
  Notation SFS pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 :=
    (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Lemma land64_land32 : forall x, Z.land (Z.land x 18446744073709551615) 4294967295 = ((x mod 18446744073709551616) mod 4294967296)%Z.
  Proof.
    intros x. change 18446744073709551615%Z with (Z.ones 64). change 4294967295%Z with (Z.ones 32).
    rewrite !Z.land_ones by lia. reflexivity.
  Qed.
  Lemma sf_finl : forall x xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    POST (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 (Z_to_bv 64 (Z.land (Z.land x 18446744073709551615) 4294967295)) xa2 xa3 xa4 xa5 xa6 xa7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (ret_pc ra) fc None m (seg_rom usegs)).
  Proof. intros. rewrite land64_land32. apply sf_fin. assumption. Qed.

  Lemma sf_exit_inc : forall x xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= x <= SF_EMAX)%Z ->
    evt usegs POST (SFS 0x5b6b8 xt0 xt1 xt2 xa0 (Z_to_bv 64 x) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI. intros. do 5 zstep. apply evt_done. apply sf_finl. assumption. Qed.

  Lemma sf_tz2 : forall k xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (SF_EMIN <= k <= SF_EMAX - 16)%Z ->
    evt usegs POST (SFS 0x5b5d0 xt0 xt1 xt2 xa0 (Z_to_bv 64 k) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK.
    unfold SF_EMIN, SF_EMAX in *.
    assert (K4 : forall x ya0 ya3 ya4 ya5 ya6 ya7, (-324 <= x <= 307)%Z ->
              evt usegs POST (SFS 0x5b6a8 xt0 xt1 xt2 ya0 (Z_to_bv 64 x) xa2 ya3 ya4 ya5 ya6 ya7 xt3 xt4 xt5 xt6)).
    { intros x ya0 ya3 ya4 ya5 ya6 ya7 HX.
      do 4 zstep. apply evt_done. apply sf_finl. unfold SF_EMIN, SF_EMAX. lia. }
    assert (K3 : forall x4 x5 ya0 ya3 ya6 ya7, (0 <= x4 <= 2)%Z -> (0 <= x5 <= 12)%Z ->
              evt usegs POST (SFS 0x5b670 xt0 xt1 xt2 ya0 (Z_to_bv 64 k) xa2 ya3 (Z_to_bv 64 x4) (Z_to_bv 64 x5) ya6 ya7 xt3 xt4 xt5 xt6)).
    { intros x4 x5 ya0 ya3 ya6 ya7 H4 H5.
      do 12 zstep.
      lazymatch goal with |- context [Z.b2z ?b] => pose proof (b2z_range b) as RB; set (bb := Z.b2z b) in * end.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply (K4 (k + x5 + x4 + bb)%Z)]; [num_st_eq | lia].
      - zstep.
        eapply evt_eq; [| eapply (K4 (k + x5 + x4 + bb)%Z)]; [num_st_eq | lia]. }
    assert (K2 : forall ya0 ya4 ya6 ya7 (b1 b2 : bool),
              evt usegs POST (SFS 0x5b634 xt0 xt1 xt2 ya0 (Z_to_bv 64 k) xa2 (Z_to_bv 64 (Z.b2z b1)) ya4 (Z_to_bv 64 (Z.b2z b2)) ya6 ya7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya4 ya6 ya7 b1 b2.
      pose proof (b2z_range b1) as R1. pose proof (b2z_range b2) as R2.
      do 13 zstep. nnorm.
      match goal with |- context [Z.lor ?x ?y] =>
        lazymatch x with context [Z.b2z b1] =>
          replace (Z.lor x y) with (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z by (destruct b1, b2; reflexivity) end end.
      lazymatch goal with |- context [Z.b2z (?u <? ?v)] => pose proof (b2z_range (u <? v)) as RB; set (b3 := Z.b2z (u <? v)) in * end.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply (K3 (2 * b3)%Z (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z)]; [num_st_eq | lia | lia].
      - zstep.
        eapply evt_eq; [| eapply (K3 (2 * b3)%Z (8 * Z.b2z b1 + 4 * Z.b2z b2)%Z)]; [num_st_eq | lia | lia]. }
    assert (K1 : forall ya0 ya3 ya4 ya5 ya6,
              evt usegs POST (SFS 0x5b604 xt0 xt1 xt2 ya0 (Z_to_bv 64 k) xa2 ya3 ya4 ya5 ya6 xa7 xt3 xt4 xt5 xt6)).
    { intros ya0 ya3 ya4 ya5 ya6.
      do 10 zstep.
      zstep. if_cases K.
      - eapply evt_eq; [| eapply K2]; num_st_eq.
      - zstep.
        eapply evt_eq; [| eapply K2]; num_st_eq. }
    do 11 zstep.
    zstep. if_cases K.
    - eapply evt_eq; [| eapply K1]; num_st_eq.
    - zstep.
      eapply evt_eq; [| eapply K1]; num_st_eq.
  Qed.

  Lemma sf_short2 : forall k b2 xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-324 <= k <= 292)%Z -> (0 <= b2 <= 3)%Z ->
    evt usegs POST (SFS 0x5b568 xt0 xt1 xt2 (Z_to_bv 64 b2) (Z_to_bv 64 k) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros k b2 xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HK HB.
    do 11 zstep.
    zstep. if_cases K1.
    { apply sf_tz2. unfold SF_EMIN, SF_EMAX; lia. }
    assert (KA : forall ya0 ya2 ya5,
              evt usegs POST (SFS 0x5b5a4 xt0 xt1 xt2 ya0 (Z_to_bv 64 k) ya2 xa3 xa4 ya5 xa6 xa7 xt3 xt4 xt5 xt6) ->
              True) by (intros; exact I). clear KA.
    assert (b2 = 0 \/ b2 = 1 \/ b2 = 2 \/ b2 = 3)%Z as [->|[->|[->| ->]]] by lia;
      (zstep; zstep; zstep; if_false;
       do 4 zstep;
       zstep; if_cases K2; [apply sf_exit_inc; unfold SF_EMIN, SF_EMAX; lia|];
       zstep;
       zstep; if_cases K3; [apply sf_exit_inc; unfold SF_EMIN, SF_EMAX; lia|];
       apply sf_exit_dec; [exact MI| unfold SF_EMIN, SF_EMAX; lia]).
  Qed.

  Lemma sf_short : forall e2 xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
    (-1074 <= e2 <= 972)%Z ->
    evt usegs POST (SFS 0x5b4e4 xt0 xt1 xt2 xa0 xa1 xa2 (Z_to_bv 64 e2) xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6).
  Proof using MI.
    intros e2 xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HE.
    pose proof (sf_k2_range e2 HE) as HK.
    pose proof (sf_beta2_range e2 HE) as HB.
    pose proof (sf_prod2_small e2 HE) as [_ P2].
    do 4 zstep.
    rewrite SFModel.land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    rewrite swrap32_Z. change ((?x + 2147483648) mod 4294967296 - 2147483648)%Z with (sw32 x).
    rewrite (sw32_mulc e2 631305) by lia.
    replace (Z_to_bv 64 (e2 mod 18446744073709551616 * 631305)) with (Z_to_bv 64 (e2 * 631305))
      by (apply Z_to_bv_eqm; change (2 ^ 64)%Z with 18446744073709551616%Z; symmetry; apply mod64_mulc).
    zstep. if_false.

    do 5 zstep.
    rewrite SFModel.land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    replace (bv_swrap 32 (Z.shiftr (bv_swrap 32 ((e2 * 631305 + -261663) mod 18446744073709551616)) 21)) with (sf_k2 e2)
      by (rewrite !swrap32_Z; symmetry; apply sf_k2_machine; [exact HE | rewrite Z.mod_mod by lia; f_equal; lia]).
    set (k := sf_k2 e2) in *.

    zstep. zstep. rewrite SFModel.land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z. nnorm.
    zstep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    zstep. zstep. zstep. zstep. nnorm.
    zstep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].

    do 6 zstep.
    rewrite !SFModel.land_W64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    replace (bv_swrap 32 (Z.shiftr (bv_swrap 32 ((k mod 18446744073709551616 * 18446744073707809969) mod 18446744073709551616)) 19) + e2)%Z
      with (sf_beta2 e2) by (rewrite !swrap32_Z; symmetry; exact (sf_beta2_machine e2 HE)).
    set (b2 := sf_beta2 e2) in *.

    zstep. zstep.
    rewrite (swrap32_id (11 - b2)) by lia.
    zstep. if_cases G4; zify_cond G4; [exfalso; rewrite ?unsigned_lit in G4 by lia; lia|].

    zstep. zstep. zstep.
    destruct (image_readable_b usegs m (Z.to_nat 9904) 0x176c0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (tb & TL & TB).
    destruct (bytes_u64_read usegs m 0x176c0 tb (16 * (292 - k)) TB ltac:(lia) ltac:(rewrite TL; lia)) as [w0 RD0].
    zstep.
    clear RD0 TB TL tb.
    zstep. zstep.
    apply sf_short2; [exact HK | exact HB].
  Qed.

  Lemma sf_body : forall E t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    (0 <= E <= 2047)%Z ->
    evt usegs POST (SFS 0x5b228 t0 t1 t2 a0 (Z_to_bv 64 E) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof using MI.
    intros E t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HE.
    zstep.
    zstep. if_cases K0; zify_cond K0.
    {
      zstep. apply sf_main; [exact MI| lia]. }

    zstep.
    rewrite (swrap32_id (E + -1075)) by lia.
    zstep. if_cases G; zify_cond G.
    { exfalso. rewrite ?SFModel.signed_of_Z in G by lia. lia. }
    zstep. if_cases K1.
    { apply sf_short. lia. }
    do 4 zstep.
    apply sf_main; [exact MI| lia].
  Qed.
End SF.

Theorem sf_proof : sf_stmt.
Proof.
  unfold sf_stmt. intros. unfold SF_ENTRY. apply sf_body; assumption.
Qed.
