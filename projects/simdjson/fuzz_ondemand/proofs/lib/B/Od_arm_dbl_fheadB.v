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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_arm_dbl_defsB Od_arm_dbl_fh4B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Lemma shad_next8 : forall X, ((X + 8) / 8 = X / 8 + 1)%Z.
Proof. intros X. replace (X + 8)%Z with (X + 1 * 8)%Z by lia. apply Z.div_add. lia. Qed.

Section ArmDblFheadB.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Notation HST pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
             (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880)) xs3 xs4 xs5 xs6
             (Z_to_bv 64 2147450880) xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom bsegs)).

  Local Ltac bload m1 BUFRO k :=
    let RB := fresh "RB" in
    pose proof (tokB_read m1 E k BUFRO ltac:(lia)) as RB; dstep0; odnorm; clear RB.

  Local Ltac ds := dstep0; num_abstract_data.

  Lemma dbl_fh_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 q o : Z) v4 (w2 : word)
      xra xa2 xa6 xs5 xs6 xs8 xs9 xs10 xs11 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 -> dbl_R_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= q)%Z -> (0 <= o)%Z -> (q + o + 9 <= o_len E)%Z -> (blen bs - (q + o) <= Z.of_nat f)%Z ->
    evt bsegs Q (HST 0x982c0 xra (Z_to_bv 64 DBL_KT0) (Z_to_bv 64 17361641481138401520) w2 (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 (o_BUF E + q)) xa2
                     (Z_to_bv 64 1085102592571150095) v4 (Z_to_bv 64 neg) xa6 (Z_to_bv 64 DBL_KA7)
                     (Z_to_bv 64 ((o_BUF E + q + 9 + o) / 8 + 2147450880)) (Z_to_bv 64 (o_BUF E + q + 16)) xs5 xs6 xs8 xs9 xs10 xs11
                     (Z_to_bv 64 434041037028460038) (Z_to_bv 64 3689348814741910323) (Z_to_bv 64 o) (Z_to_bv 64 (o_BUF E + q + 9)) xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HR PS SG Hq Ho Hqo Hf.
    { exfalso. pose proof (od_n_range E (oka_s1 E OK)) as NR. pose proof (oka_len E OK). pose proof PS as [NGR Hq0].
      pose proof HH as (HP & _). pose proof (od_tokI_range E (oka_s1 E OK) (o_pos st) ltac:(lia)) as TR. unfold o_len in *. lia. }
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + 9 + o)) as R0. pose proof (od_B_range E BOK (q + 9 + o + 1)) as R1.
    pose proof (od_B_range E BOK (q + 9 + o + 2)) as R2. pose proof (od_B_range E BOK (q + 9 + o + 3)) as R3.
    pose proof (od_B_range E BOK (q + 9 + o + 4)) as R4. pose proof (od_B_range E BOK (q + 9 + o + 5)) as R5.
    pose proof (od_B_range E BOK (q + 9 + o + 6)) as R6. pose proof (od_B_range E BOK (q + 9 + o + 7)) as R7.
    ddata xs5. ddata xa6.

    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    dstep0. dstep0. dstep0. if_false.
    do 5 dstep0. if_false.

    ds. ds.
    bload m1 BUFRO (q + 9 + o)%Z. bload m1 BUFRO (q + 9 + o + 1)%Z. bload m1 BUFRO (q + 9 + o + 2)%Z. bload m1 BUFRO (q + 9 + o + 3)%Z.

    do 9 ds.

    bload m1 BUFRO (q + 9 + o + 4)%Z. bload m1 BUFRO (q + 9 + o + 5)%Z. ds. bload m1 BUFRO (q + 9 + o + 6)%Z. bload m1 BUFRO (q + 9 + o + 7)%Z.

    do 29 ds.
    if_cases K; zify_cond K.
    -
      set (c0 := B bs (q + 9 + o)) in *. set (c1 := B bs (q + 9 + o + 1)) in *. set (c2 := B bs (q + 9 + o + 2)) in *. set (c3 := B bs (q + 9 + o + 3)) in *.
      set (c4 := B bs (q + 9 + o + 4)) in *. set (c5 := B bs (q + 9 + o + 5)) in *. set (c6 := B bs (q + 9 + o + 6)) in *. set (c7 := B bs (q + 9 + o + 7)) in *.
      fold (le4z c4 c5 c6 c7) in K. fold (le4z c0 c1 c2 c3) in K. fold (le8z c0 c1 c2 c3 c4 c5 c6 c7) in K.
      pose proof (swar8n_machine c0 c1 c2 c3 c4 c5 c6 c7 _ R0 R1 R2 R3 R4 R5 R6 R7 K) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (QL : (q + 9 + o + 7 < blen bs)%Z) by (apply B_nonzero_lt_len; fold c7; lia).
      clear K.
      eapply evt_eq; [| eapply (IH Q st neg q0 q (o + 8)%Z v4 w2); [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact PS| exact SG| exact Hq| lia| lia| lia]].
      assert (ES : ((o_BUF E + q + 9 + (o + 8)) / 8 = (o_BUF E + q + 9 + o) / 8 + 1)%Z)
        by (replace (o_BUF E + q + 9 + (o + 8))%Z with (o_BUF E + q + 9 + o + 8)%Z by lia; apply shad_next8).
      od_st_eq.
    -
      clear K. do 4 dstep0.
      eapply evt_eq; [| eapply (dbl_fh_p4 E OK Q st neg q0 q (o + 9)%Z v4 w2); [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact PS| exact SG| exact Hq| lia| lia]].
      od_st_eq.
  Qed.

  Theorem dbl_fhead : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_R_k E Q st -> dbl_F_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HR. unfold dbl_F_k.
    intros neg q0 q v4 w2 w6 xra xt1 xa2 xa3 xs3 xs4 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 PS SG Hq HDOT FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    assert (QL : (q < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
    pose proof (od_B_range E BOK (q + 1)) as R1. pose proof (od_B_range E BOK (q + 2)) as R2.
    pose proof (od_B_range E BOK (q + 3)) as R3. pose proof (od_B_range E BOK (q + 4)) as R4.
    pose proof (od_B_range E BOK (q + 5)) as R5. pose proof (od_B_range E BOK (q + 6)) as R6.
    pose proof (od_B_range E BOK (q + 7)) as R7. pose proof (od_B_range E BOK (q + 8)) as R8.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    ostep. ostep. dgok. ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. ostep. ostep. ostep. if_true.

    bload m1 BUFRO (q + 1)%Z. bload m1 BUFRO (q + 2)%Z. bload m1 BUFRO (q + 3)%Z. bload m1 BUFRO (q + 4)%Z.
    do 5 dstep0.
    bload m1 BUFRO (q + 5)%Z. bload m1 BUFRO (q + 6)%Z.
    dstep0.
    bload m1 BUFRO (q + 7)%Z. bload m1 BUFRO (q + 8)%Z.

    do 20 dstep0.
    if_cases K; zify_cond K.
    -
      set (b1 := B bs (q + 1)) in *. set (b2 := B bs (q + 2)) in *. set (b3 := B bs (q + 3)) in *. set (b4 := B bs (q + 4)) in *.
      set (b5 := B bs (q + 5)) in *. set (b6 := B bs (q + 6)) in *. set (b7 := B bs (q + 7)) in *. set (b8 := B bs (q + 8)) in *.
      fold (le4z b5 b6 b7 b8) in K. fold (le4z b1 b2 b3 b4) in K. fold (le8z b1 b2 b3 b4 b5 b6 b7 b8) in K.
      pose proof (swar8n_machine b1 b2 b3 b4 b5 b6 b7 b8 _ R1 R2 R3 R4 R5 R6 R7 R8 K) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (QL8 : (q + 8 < blen bs)%Z) by (apply B_nonzero_lt_len; fold b8; lia).
      clear K.

      do 5 dstep0.
      assert (ES : ((o_BUF E + q + 9 + 0) / 8 = (o_BUF E + q + 9) / 8)%Z) by (f_equal; lia).
      eapply evt_eq; [| eapply (dbl_fh_loop (Z.to_nat (blen bs)) Q st neg q0 q 0%Z v4 w2);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact PS| exact SG| lia| lia| lia| lia]].
      od_st_eq.
    -
      clear K. do 3 dstep0.
      eapply evt_eq; [| eapply (dbl_fh_p4 E OK Q st neg q0 q 1%Z v4 w2); [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact PS| exact SG| lia| lia| lia]].
      od_st_eq.
  Qed.
End ArmDblFheadB.
