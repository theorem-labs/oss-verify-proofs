(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Od_arm_dbl_swar Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_arm_dbl_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Lemma b4w_eq : forall b0 b1 b2 x, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z -> (0 <= b2 < 256)%Z -> (0 <= x)%Z ->
  Z.lor (Z.lor (Z.shiftl x 24 mod 18446744073709551616) (Z.shiftl b2 16 mod 18446744073709551616))
        (Z.lor (Z.shiftl b1 8 mod 18446744073709551616) b0)
  = (b0 + 256 * (b1 + 256 * (b2 + 256 * ((x mod 1099511627776) mod 256 + 256 * ((x mod 1099511627776) / 256)))))%Z.
Proof.
  intros b0 b1 b2 x H0 H1 H2 Hx.
  set (h := (x mod 1099511627776)%Z). assert (Hh : (0 <= h < 1099511627776)%Z) by (apply Z.mod_pos_bound; lia).
  replace (h mod 256 + 256 * (h / 256))%Z with h by (pose proof (Z.div_mod h 256 ltac:(lia)); lia).
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 24)%Z with 16777216%Z. change (2 ^ 16)%Z with 65536%Z. change (2 ^ 8)%Z with 256%Z.
  replace ((x * 16777216) mod 18446744073709551616)%Z with (h * 16777216)%Z
    by (unfold h; change 18446744073709551616%Z with (1099511627776 * 16777216)%Z; rewrite Z.mul_mod_distr_r by lia; reflexivity).
  rewrite (Z.mod_small (b2 * 65536)) by lia. rewrite (Z.mod_small (b1 * 256)) by lia.
  rewrite (lor_disj (b1 * 256) b0 8) by (try apply Z.mod_mul; change (2 ^ 8)%Z with 256%Z; lia).
  rewrite (lor_disj (h * 16777216) (b2 * 65536) 24)
    by (try (change (2 ^ 24)%Z with 16777216%Z; apply Z.mod_mul); change (2 ^ 24)%Z with 16777216%Z; lia).
  rewrite (lor_disj (h * 16777216 + b2 * 65536) (b1 * 256 + b0) 16).
  - lia.
  - lia.
  - lia.
  - change (2 ^ 16)%Z with 65536%Z. replace (h * 16777216 + b2 * 65536)%Z with ((h * 256 + b2) * 65536)%Z by lia. apply Z.mod_mul. lia.
  - change (2 ^ 16)%Z with 65536%Z. lia.
Qed.

Section ArmDblFh4B.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_fh_p4 : forall (Q : machine_state -> Prop) st (neg q0 q k : Z) v4 (w2 w6 : word)
      xra xa3 xs3 xs4 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 -> dbl_R_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= q)%Z -> (1 <= k)%Z -> (q + k <= o_len E)%Z ->
    evt bsegs Q (DBLST E 0x99794 xra (Z_to_bv 64 DBL_KT0) (Z_to_bv 64 k) w2 (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 (o_BUF E + q)) (Z_to_bv 64 (o_BUF E + q + k)) xa3
                       v4 (Z_to_bv 64 neg) w6 (Z_to_bv 64 DBL_KA7) xs3 xs4 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HR PS SG Hq Hk Hqk.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + k)) as R0. pose proof (od_B_range E BOK (q + k + 1)) as R1.
    pose proof (od_B_range E BOK (q + k + 2)) as R2. pose proof (od_B_range E BOK (q + k + 3)) as R3.
    set (b0 := B bs (q + k)) in *. set (b1 := B bs (q + k + 1)) in *. set (b2 := B bs (q + k + 2)) in *. set (b3 := B bs (q + k + 3)) in *.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    ostep. ostep. ostep. ostep. ostep. ostep. ostep. if_true.

    ostep. ostep. ostep. ostep. ostep. if_true.

    pose proof (tokB_read m1 E (q + k + 1) BUFRO ltac:(lia)) as RB. dstep0. odnorm. clear RB.
    pose proof (tokB_read m1 E (q + k) BUFRO ltac:(lia)) as RB. dstep0. odnorm. clear RB.
    pose proof (tokB_read m1 E (q + k + 2) BUFRO ltac:(lia)) as RB. dstep0. odnorm. clear RB.
    pose proof (tokB_read m1 E (q + k + 3) BUFRO ltac:(lia)) as RB. dstep0. odnorm. clear RB.

    do 6 dstep0.
    fold b0 b1 b2 b3.
    set (x3 := ((if (b3 <? 128)%Z then b3 else (b3 - 256)%Z) mod 18446744073709551616)%Z) in *.
    assert (X3 : (0 <= x3)%Z) by (unfold x3; apply Z.mod_pos_bound; lia).
    clearbody x3.
    pose proof (b4w_eq b0 b1 b2 x3 R0 R1 R2 X3) as EW.
    match goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) (Z.lor ?c ?d))] => set (w := Z.lor (Z.lor a b) (Z.lor c d)) in * end.
    clearbody w.

    do 8 dstep0.
    if_cases K; zify_cond K.
    -
      clear K.
      eapply evt_eq; [| eapply (HR neg q0 q k v4 w2 w6); [exact PS | exact SG | exact Hq | lia | lia | exact FRM | exact INV2]].
      od_st_eq.
    -
      assert (G : (48 <= b0 /\ 48 <= b1 /\ 48 <= b2 /\ 48 <= (x3 mod 1099511627776) mod 256)%Z).
      { rewrite !bv_swrap32, ?swrap32_mod64 in K. unfold swrap32 in K. rewrite EW in K.
        eapply swar4_ge48; [exact R0 | exact R1 | exact R2 | apply Z.mod_pos_bound; lia | exact K]. }
      assert (QL : (q + k + 2 < blen bs)%Z) by (apply B_nonzero_lt_len; fold b2; lia).
      clear K G EW.
      repeat match goal with |- context [Z_to_bv 64 ?t] =>
        lazymatch t with context [w] => idtac end;
        let z := fresh "dw" in generalize (Z_to_bv 64 t); intro z; ddata z end.
      ddata w6.

      do 13 dstep.
      eapply evt_eq; [| eapply (HR neg q0 q (k + 4)%Z v4 w2); [exact PS | exact SG | exact Hq | lia | lia | exact FRM | exact INV2]].
      od_st_eq.
  Qed.
End ArmDblFh4B.
