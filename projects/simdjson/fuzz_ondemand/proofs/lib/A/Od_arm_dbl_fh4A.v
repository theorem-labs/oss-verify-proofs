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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_cpsA Od_arm_dbl_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Lemma a4w_eq : forall b0 b1 b2 x, (0 <= b0 < 256)%Z -> (0 <= b1 < 256)%Z -> (0 <= b2 < 256)%Z -> (0 <= x)%Z ->
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

Section ArmDblFh4A.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation off st := (tokI (o_bs E) (o_idxs E) (o_pos st)).

  Notation HINV st neg c00 c08 v176 m1 :=
    (DBLINVa E st [c00; c08; C8 (Z_to_bv 64 DBL_K16); C8 (Z_to_bv 64 DBL_K24)]
                  [C8 (Z_to_bv 64 (off st)); C8 (Z_to_bv 64 (o_BUF E)); C8 (Z_to_bv 64 neg)] [C8 v176] m1).

  Notation HST st pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
             (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
             (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 200))
             (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

  Lemma dbl_fh_p4 : forall (Q : machine_state -> Prop) st (neg q0 q k : Z) j0 j8 v176
      xt0 xt1 xt2 xa0 xa1 xa3 xa5 xa7 xt4 xt5 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> HINV st neg (CB 8 j0) (CB 8 j8) v176 m1 -> dbl_R_k E Q st ->
    dbl_pos E st neg q0 -> (q0 <= q)%Z -> (1 <= k)%Z -> (q + k <= o_len E)%Z ->
    evt asegs Q (HST st 0x991f0 (Z_to_bv 64 (o_act E)) xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q + k)) xa3 (Z_to_bv 64 (o_BUF E + q)) xa5 (Z_to_bv 64 10) xa7
                     (Z_to_bv 64 2) (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 k) xt4 xt5 (Z_to_bv 64 1) xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HR PS Hq Hk Hqk.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokB_read m1 E (q + k) BUFRO ltac:(lia)) as RB0. pose proof (tokB_read m1 E (q + k + 1) BUFRO ltac:(lia)) as RB1.
    pose proof (tokB_read m1 E (q + k + 2) BUFRO ltac:(lia)) as RB2. pose proof (tokB_read m1 E (q + k + 3) BUFRO ltac:(lia)) as RB3.
    pose proof (od_B_range E BOK (q + k)) as R0. pose proof (od_B_range E BOK (q + k + 1)) as R1.
    pose proof (od_B_range E BOK (q + k + 2)) as R2. pose proof (od_B_range E BOK (q + k + 3)) as R3.
    set (b0 := B bs (q + k)) in *. set (b1 := B bs (q + k + 1)) in *. set (b2 := B bs (q + k + 2)) in *. set (b3 := B bs (q + k + 3)) in *.
    dwalkk ltac:(fun pc => lazymatch pc with 0x99220%Z => idtac end).
    dstep0. dstep0. dstep0. odnorm. dstep0.
    clear RB0 RB1 RB2 RB3.
    do 6 dstep0.
    set (x3 := bv_unsigned (sxb (Z_to_bv 8 b3))) in *.
    assert (X3 : (0 <= x3)%Z) by (unfold x3; pose proof (bv_unsigned_in_range 64 (sxb (Z_to_bv 8 b3))) as RX; lia).
    clearbody x3.
    pose proof (a4w_eq b0 b1 b2 x3 R0 R1 R2 X3) as EW.
    match goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) (Z.lor ?c ?d))] => set (w := Z.lor (Z.lor a b) (Z.lor c d)) in * end.
    clearbody w.
    do 8 dstep0.
    if_cases K; zify_cond K.
    -
      clear K. forget_2 FR104.
      eapply evt_eq; [| eapply (HR neg q0 q k); [exact PS | exact Hq | lia | lia | exact FRM | unfold DBL_K16, DBL_K24; dbl_close_inv]].
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
      ddata xa5.
      do 12 dstep.
      forget_2 FR104.
      eapply evt_eq; [| eapply (HR neg q0 q (k + 4)%Z); [exact PS | exact Hq | lia | lia | exact FRM | unfold DBL_K16, DBL_K24; dbl_close_inv]].
      od_st_eq.
  Qed.
End ArmDblFh4A.
