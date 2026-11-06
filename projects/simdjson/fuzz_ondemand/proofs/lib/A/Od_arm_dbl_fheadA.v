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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_cpsA Od_arm_dbl_defsA Od_arm_dbl_fh4A Od_arm_dblA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Lemma shad_next8 : forall X, ((X + 8) / 8 = X / 8 + 1)%Z.
Proof. intros X. replace (X + 8)%Z with (X + 1 * 8)%Z by lia. apply Z.div_add. lia. Qed.

Section ArmDblFheadA.
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

  Local Ltac bload m1 BUFRO k :=
    let RB := fresh "RB" in
    pose proof (tokB_read m1 E k BUFRO ltac:(lia)) as RB; dstep0; odnorm; clear RB.

  Local Ltac ds := dstep0; num_abstract_data.

  Lemma dbl_fh_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 q o : Z) v176
      xt0 xt1 xt2 xa0 xa5 xa6 xa7 xs11 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    HINV st neg (C8 (Z_to_bv 64 (o_BUF E + q0))) (C8 (Z_to_bv 64 2)) v176 m1 -> dbl_R_k E Q st ->
    dbl_pos E st neg q0 -> (q0 <= q)%Z -> (0 <= o)%Z -> (q + o + 9 <= o_len E)%Z -> (blen bs - (q + o) <= Z.of_nat f)%Z ->
    evt asegs Q (HST st 0x97dc4 (Z_to_bv 64 (o_BUF E + q + 9)) xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q + 16)) (Z_to_bv 64 o)
                     (Z_to_bv 64 1085102592571150095) (Z_to_bv 64 (o_BUF E + q)) xa5 xa6 xa7
                     (Z_to_bv 64 ((o_BUF E + q + 9 + o) / 8 + 2147450880)) xs11
                     (Z_to_bv 64 17361641481138401520) (Z_to_bv 64 434041037028460038) (Z_to_bv 64 3689348814741910323) xt6 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HR PS Hq Ho Hqo Hf.
    { exfalso. pose proof (od_n_range E (oka_s1 E OK)) as NR. pose proof (oka_len E OK). pose proof PS as [NGR Hq0].
      pose proof HH as (HP & _). pose proof (od_tokI_range E (oka_s1 E OK) (o_pos st) ltac:(lia)) as TR. unfold o_len in *. lia. }
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + 9 + o)) as R0. pose proof (od_B_range E BOK (q + 9 + o + 1)) as R1.
    pose proof (od_B_range E BOK (q + 9 + o + 2)) as R2. pose proof (od_B_range E BOK (q + 9 + o + 3)) as R3.
    pose proof (od_B_range E BOK (q + 9 + o + 4)) as R4. pose proof (od_B_range E BOK (q + 9 + o + 5)) as R5.
    pose proof (od_B_range E BOK (q + 9 + o + 6)) as R6. pose proof (od_B_range E BOK (q + 9 + o + 7)) as R7.
    set (c0 := B bs (q + 9 + o)) in *. set (c1 := B bs (q + 9 + o + 1)) in *. set (c2 := B bs (q + 9 + o + 2)) in *. set (c3 := B bs (q + 9 + o + 3)) in *.
    set (c4 := B bs (q + 9 + o + 4)) in *. set (c5 := B bs (q + 9 + o + 5)) in *. set (c6 := B bs (q + 9 + o + 6)) in *. set (c7 := B bs (q + 9 + o + 7)) in *.
    ddata xa7. ddata xa5.

    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    dstep0. dstep0. dstep0. if_false.
    do 6 dstep0. if_false.

    ds. ds.
    bload m1 BUFRO (q + 9 + o)%Z. bload m1 BUFRO (q + 9 + o + 1)%Z. bload m1 BUFRO (q + 9 + o + 2)%Z. bload m1 BUFRO (q + 9 + o + 3)%Z.

    do 9 ds.

    bload m1 BUFRO (q + 9 + o + 4)%Z. bload m1 BUFRO (q + 9 + o + 5)%Z. ds. bload m1 BUFRO (q + 9 + o + 6)%Z. bload m1 BUFRO (q + 9 + o + 7)%Z.

    do 29 ds.
    if_cases K; zify_cond K.
    -
      fold (le4z c4 c5 c6 c7) in K. fold (le4z c0 c1 c2 c3) in K. fold (le8z c0 c1 c2 c3 c4 c5 c6 c7) in K.
      pose proof (swar8n_machine c0 c1 c2 c3 c4 c5 c6 c7 _ R0 R1 R2 R3 R4 R5 R6 R7 K) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (QL : (q + 9 + o + 7 < blen bs)%Z) by (apply B_nonzero_lt_len; fold c7; lia).
      clear K.
      eapply evt_eq; [| eapply (IH Q st neg q0 q (o + 8)%Z v176); [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact PS| exact Hq| lia| lia| lia]].
      assert (ES : ((o_BUF E + q + 9 + (o + 8)) / 8 = (o_BUF E + q + 9 + o) / 8 + 1)%Z)
        by (replace (o_BUF E + q + 9 + (o + 8))%Z with (o_BUF E + q + 9 + o + 8)%Z by lia; apply shad_next8).
      od_st_eq.
    -
      clear K. do 8 dstep0.
      forget_2 FR0.
      eapply evt_eq; [| eapply (dbl_fh_p4 E OK Q st neg q0 q (o + 9)%Z); [exact HLAST| exact HH| exact FRM| unfold DBL_K16, DBL_K24; dbl_close_inv| exact HR| exact PS| exact Hq| lia| lia]].
      od_st_eq.
  Qed.

  Theorem dbl_fhead : dbl_fhead_stmt E.
  Proof using OK.
    unfold dbl_fhead_stmt. intros Q st HLAST HH HK HR. unfold dbl_F_k.
    intros neg q0 q j0 j8 j104 j112 v176 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa7 xF xfc m1 PS Hq HDOT FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    assert (QL : (q < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
    pose proof (od_B_range E BOK (q + 1)) as R1. pose proof (od_B_range E BOK (q + 2)) as R2.
    pose proof (od_B_range E BOK (q + 3)) as R3. pose proof (od_B_range E BOK (q + 4)) as R4.
    pose proof (od_B_range E BOK (q + 5)) as R5. pose proof (od_B_range E BOK (q + 6)) as R6.
    pose proof (od_B_range E BOK (q + 7)) as R7. pose proof (od_B_range E BOK (q + 8)) as R8.
    set (b1 := B bs (q + 1)) in *. set (b2 := B bs (q + 2)) in *. set (b3 := B bs (q + 3)) in *. set (b4 := B bs (q + 4)) in *.
    set (b5 := B bs (q + 5)) in *. set (b6 := B bs (q + 6)) in *. set (b7 := B bs (q + 7)) in *. set (b8 := B bs (q + 8)) in *.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    dstep0. do 4 dstep0. if_true.
    dstep0. dstep0.
    do 5 dstep0. if_true.
    od_cur_mem ltac:(fun mm => assert (INVH : HINV st neg (CB 8 j0) (CB 8 j8) v176 mm) by (unfold DBL_K16, DBL_K24; dbl_close_inv)).

    od_cur_mem ltac:(fun mm => bload mm BUFRO (q + 1)%Z). od_cur_mem ltac:(fun mm => bload mm BUFRO (q + 2)%Z).
    od_cur_mem ltac:(fun mm => bload mm BUFRO (q + 3)%Z). od_cur_mem ltac:(fun mm => bload mm BUFRO (q + 4)%Z).
    do 5 dstep0.
    od_cur_mem ltac:(fun mm => bload mm BUFRO (q + 5)%Z). od_cur_mem ltac:(fun mm => bload mm BUFRO (q + 6)%Z).
    dstep0.
    od_cur_mem ltac:(fun mm => bload mm BUFRO (q + 7)%Z). od_cur_mem ltac:(fun mm => bload mm BUFRO (q + 8)%Z).

    do 20 dstep0.
    if_cases K; zify_cond K.
    -
      fold (le4z b5 b6 b7 b8) in K. fold (le4z b1 b2 b3 b4) in K. fold (le8z b1 b2 b3 b4 b5 b6 b7 b8) in K.
      pose proof (swar8n_machine b1 b2 b3 b4 b5 b6 b7 b8 _ R1 R2 R3 R4 R5 R6 R7 R8 K) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (QL8 : (q + 8 < blen bs)%Z) by (apply B_nonzero_lt_len; fold b8; lia).
      clear K.

      do 7 dstep0.
      assert (ES : ((o_BUF E + q + 9 + 0) / 8 = (o_BUF E + q + 9) / 8)%Z) by (f_equal; lia).
      eapply evt_eq; [| eapply (dbl_fh_loop (Z.to_nat (blen bs)) Q st neg q0 q 0%Z v176);
                        [exact HLAST| exact HH| exact FRM| unfold DBL_K16, DBL_K24; dbl_close_inv| exact HR| exact PS| lia| lia| lia| lia]].
      od_st_eq.
    -
      clear K. do 4 dstep0.
      eapply evt_eq; [| eapply (dbl_fh_p4 E OK Q st neg q0 q 1%Z); [exact HLAST| exact HH| exact FRM| exact INVH| exact HR| exact PS| lia| lia| lia]].
      od_st_eq.
  Qed.
End ArmDblFheadA.
