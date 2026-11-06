(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit Sj_num_walk Sj_num_sp_defs Sj_num_sp_dc Sj_num_sp_cf1 Sj_num_sp_pdefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section SPACC.
  Hypothesis HSET : sp_memset_stmt.
  Hypothesis HPM : sp_pm_stmt.
  Hypothesis HPDC : sp_pdc_stmt.
  Hypothesis HNDC : sp_ndc_stmt.
  Variable E : spenv.
  Hypothesis OK : sp_ok E.
  Notation A := (q_A E).
  Notation LAST := (q_LAST E).
  Notation OUT := (q_OUT E).

  Lemma sp_398w : forall (IP IL FPT FL : Z) (xa7 xa3 xs1 : word) xra xt0 xs0 xa0 xa1 xa4 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL ->
    (bv_unsigned xa3 <> 0 -> 1 <= bv_unsigned xa7 <= 18446744073709551614)%Z ->
    evt psegs (sp_post E) (SPS E 0x51244 xra xt0 (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 xa1 (Z_to_bv 64 OUT) xa3 xa4 (Z_to_bv 64 IL) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF HTM.
    rewrite <- (num_wz_signed xs1).
    pose proof (bv_signed_in_range 64 xs1 ltac:(lia)) as R. unfold bv_half_modulus, bv_modulus in R.
    change (2 ^ Z.of_N 64 / 2)%Z with 9223372036854775808%Z in R.
    eapply (sp_398 HSET HPM HPDC HNDC E OK (bv_signed xs1) IP IL FPT FL); [exact INV | exact FRM | apply sp_pfacts_spans; assumption | lia | exact HTM].
  Qed.

  Lemma sp_L7 : forall (f : nat) (IP IL FPT FL z k w : Z) xra xs0 xs1 xa0 xa3 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> sp_nz E IP IL FPT FL z ->
    (FPT <> 0)%Z -> (0 <= k < FL)%Z -> (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ FPT + k <= z)%Z -> (FL - k <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (SPS E 0x511b0 xra (Z_to_bv 64 10) (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 (Z_to_bv 64 (FPT + k)) (Z_to_bv 64 OUT) xa3
                               (Z_to_bv 64 999999999999999999) (Z_to_bv 64 IL) xa6 (Z_to_bv 64 w)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) (Z_to_bv 64 (FL - 1 - k)) xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF NZ HF Hk Hw Hz Hf; [exfalso; lia|].
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & [[PA PB] | [(PA & PB & PC & PD) G2]]); [exfalso; lia|].
    pose proof (G2 (FPT + k)%Z ltac:(lia)) as Gk. pose proof (sp_tb_range E (FPT + k)) as Rk.
    destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    unfold sp_tb in Gk, Rk.
    assert (NZk : (z = FPT + k -> 49 <= bv_unsigned (nth (Z.to_nat (FPT + k - A)) (q_txt E) (Z_to_bv 8 0)))%Z) by (intros ->; exact NZ1').
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x51244%Z => first [ eapply evt_eq; [| eapply (sp_398w IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF | ];
                             intros _; rewrite ?unsigned_lit by lia; destruct (Z.eq_dec z (FPT + k)); lia
                           | fail 100 "cut" pc ]
      | 0x511b0%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL z (k + 1)%Z
                                                          (w * 10 + bv_unsigned (nth (Z.to_nat (FPT + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)%Z)];
                             [num_st_eq | exact INV | assumption | exact PF | split; assumption | lia | lia | lia
                             | destruct (Z.eq_dec z (FPT + k)); lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_2ec : forall (IP IL FPT FL z w : Z) xra xt0 xs0 xs1 xa0 xa1 xa3 xa4 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> sp_nz E IP IL FPT FL z ->
    (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ IP + IL <= z)%Z ->
    evt psegs (sp_post E) (SPS E 0x51198 xra xt0 (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 xa1 (Z_to_bv 64 OUT) xa3
                               xa4 (Z_to_bv 64 IL) xa6 (Z_to_bv 64 w)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF NZ Hw Hz.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR). destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    assert (FLR : (0 <= FL /\ (FL <> 0 -> FPT = IP + IL + 1 /\ FPT + FL <= LAST))%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x51244%Z => first [ eapply evt_eq; [| eapply (sp_398w IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF | ];
                             intros _; rewrite ?unsigned_lit by lia; lia
                           | fail 100 "cut" pc ]
      | 0x511b0%Z => first [ eapply evt_eq; [| eapply (sp_L7 (Z.to_nat FL) IP IL FPT FL z 0%Z w)];
                             [num_st_eq | exact INV | assumption | exact PF | split; assumption | lia | lia | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_L6 : forall (f : nat) (IP IL FPT FL z k w : Z) xra xs0 xs1 xa0 xa3 xa6 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> sp_nz E IP IL FPT FL z ->
    (0 <= k < IL)%Z -> (0 <= w <= 999999999999999999)%Z -> (1 <= w \/ IP + k <= z)%Z -> (IL - k <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (SPS E 0x51178 xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 (Z_to_bv 64 (IP + k)) (Z_to_bv 64 OUT) xa3
                               (Z_to_bv 64 999999999999999999) (Z_to_bv 64 IL) xa6 (Z_to_bv 64 w)
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) (Z_to_bv 64 10) xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF NZ Hk Hw Hz Hf; [exfalso; lia|].
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR).
    pose proof (G1 (IP + k)%Z ltac:(lia)) as Gk. pose proof (sp_tb_range E (IP + k)) as Rk.
    destruct NZ as [NZ1 NZ2]. pose proof NZ1 as NZ1'.
    unfold sp_tb in Gk, Rk.
    assert (NZk : (z = IP + k -> 49 <= bv_unsigned (nth (Z.to_nat (IP + k - A)) (q_txt E) (Z_to_bv 8 0)))%Z) by (intros ->; exact NZ1').
    kstep.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x51244%Z => first [ eapply evt_eq; [| eapply (sp_398w IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF | ];
                             intros _; rewrite ?unsigned_lit by lia; lia
                           | fail 100 "cut" pc ]
      | 0x51198%Z => first [ eapply evt_eq; [| eapply (sp_2ec IP IL FPT FL z
                                                          (w * 10 + bv_unsigned (nth (Z.to_nat (IP + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)%Z)];
                             [num_st_eq | exact INV | assumption | exact PF | split; assumption | lia
                             | destruct (Z.eq_dec z (IP + k)); lia]
                           | fail 100 "cut" pc ]
      | 0x51178%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL z (k + 1)%Z
                                                          (w * 10 + bv_unsigned (nth (Z.to_nat (IP + k - A)) (q_txt E) (Z_to_bv 8 0)) - 48)%Z)];
                             [num_st_eq | exact INV | assumption | exact PF | split; assumption | lia | lia
                             | destruct (Z.eq_dec z (IP + k)); lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_2b4 : forall (IP IL FPT FL z : Z) xra xs0 xs1 xa0 xa1 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL -> sp_nz E IP IL FPT FL z ->
    evt psegs (sp_post E) (SPS E 0x51160 xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 xa1 (Z_to_bv 64 OUT) xa3
                               xa4 (Z_to_bv 64 IL) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF NZ.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR). pose proof NZ as [NZ1 NZ2].
    assert (FLR : (FPT <> 0 -> FPT = IP + IL + 1)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x51198%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x51178%Z => first [ eapply evt_eq; [| eapply (sp_L6 (Z.to_nat IL) IP IL FPT FL z 0%Z 0%Z)];
                             [num_st_eq | exact INV | assumption | exact PF | exact NZ | lia | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma sp_330 : forall (IP IL FPT FL : Z) xra xt0 xs0 xs1 xa0 xa1 xa3 xa4 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt4 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL ->
    evt psegs (sp_post E) (SPS E 0x511dc xra xt0 (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 xa1 (Z_to_bv 64 OUT) xa3
                               xa4 (Z_to_bv 64 IL) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) xt4 xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF.
    kstep. kstep.
    eapply evt_eq; [| eapply (sp_398w IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF | ].
    intros C. exfalso. apply C. reflexivity.
  Qed.

  Notation cs IL FL d := (Z.min d IL + Z.max 0 (Z.min (d - IL - 1) FL))%Z.
  Lemma sp_L5 : forall (f : nat) (IP IL FPT FL c cnt : Z) xra xs0 xs1 xa0 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL ->
    (IP <= c < LAST)%Z -> (IL + FL - (c - IP) <= cnt <= IL + FL - cs IL FL (c - IP))%Z -> (LAST - c <= Z.of_nat f)%Z ->
    evt psegs (sp_post E) (SPS E 0x5114c xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) xa3
                               (Z_to_bv 64 46) (Z_to_bv 64 IL) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) (Z_to_bv 64 cnt) (Z_to_bv 64 48) (Z_to_bv 64 c) xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros f. induction f as [|f IH]; intros until mm; intros INV FRM PF Hc Hcnt Hf; [exfalso; lia|].
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR).
    pose proof (sp_tb_range E c) as Rc.
    assert (FR0 : (FPT = 0 -> FL = 0)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (FR1 : (FPT <> 0 -> FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= LAST)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (S1 : (IP <= c < IP + IL -> 48 <= sp_tb E c)%Z) by (intros X; apply G1; lia).
    assert (S2 : (FPT <> 0 -> FPT <= c < FPT + FL -> 48 <= sp_tb E c)%Z).
    { intros X Y. destruct PFR as [[? ?] | [_ G2]]; [lia | apply G2; lia]. }
    assert (D1 : (FPT <> 0 -> c = IP + IL -> sp_tb E c = 46)%Z).
    { intros X ->. destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; [lia | assumption]. }
    unfold sp_tb in Rc, S1, S2, D1.
    kstep. kstep.
    if_cases KB; zify_cond KB; [rewrite KB | kstep; if_cases KB0; zify_cond KB0; [rewrite KB0 | ]].
    -
      kwalk ltac:(fun pc => lazymatch pc with
        | 0x511dc%Z => first [ eapply evt_eq; [| eapply (sp_330 IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF] | fail 100 "cut" pc ]
        | 0x51160%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x5114c%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL (c + 1)%Z (cnt - 1)%Z)];
                               [num_st_eq | exact INV | assumption | exact PF | lia | lia | lia]
                             | fail 100 "cut" pc ]
        end).
    -
      kwalk ltac:(fun pc => lazymatch pc with
        | 0x511dc%Z => first [ eapply evt_eq; [| eapply (sp_330 IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF] | fail 100 "cut" pc ]
        | 0x51160%Z => first [ exfalso; lia | fail 100 "cut" pc ]
        | 0x5114c%Z => first [ eapply evt_eq; [| eapply (IH IP IL FPT FL (c + 1)%Z cnt)];
                               [num_st_eq | exact INV | assumption | exact PF | lia | lia | lia]
                             | fail 100 "cut" pc ]
        end).
    -
      kwalk ltac:(fun pc => lazymatch pc with
        | 0x511dc%Z => first [ eapply evt_eq; [| eapply (sp_330 IP IL FPT FL)]; [num_st_eq | exact INV | assumption | exact PF] | fail 100 "cut" pc ]
        | 0x51160%Z => first [ assert (SPAN : (IP <= c < IP + IL \/ (FPT <> 0 /\ FPT <= c < FPT + FL))%Z) by lia;
                               eapply evt_eq; [| eapply (sp_2b4 IP IL FPT FL c)]; [num_st_eq | exact INV | assumption | exact PF |];
                               split; [unfold sp_tb; lia | exact SPAN]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma sp_278 : forall (IP IL FPT FL : Z) xra xs0 xs1 xa0 xa3 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt5 xt6 xF xfc mm,
    SPINV E mm -> frm0 xfc -> sp_pfacts E IP IL FPT FL ->
    evt psegs (sp_post E) (SPS E 0x51124 xra (Z_to_bv 64 (IP + IL)) (Z_to_bv 64 IP) (Z_to_bv 64 FPT) xs0 xs1 xa0 (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) xa3
                               (Z_to_bv 64 SPATH_A4) (Z_to_bv 64 IL) xa6 xa7
                               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 FL) (Z_to_bv 64 (IL + FL)) xt5 xt6 xF xfc mm).
  Proof using HSET HPM HPDC HNDC OK.
    intros until mm. intros INV FRM PF.
    pose proof INV as INV0. sp_open INV0. sp_env OK.
    pose proof PF as ((P1 & P2 & P3) & G1 & PFR).
    assert (FR0 : (FPT = 0 -> FL = 0)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    assert (FR1 : (FPT <> 0 -> FPT = IP + IL + 1 /\ 1 <= FL /\ FPT + FL <= LAST)%Z) by (destruct PFR as [[? ?] | [(? & ? & ? & ?) _]]; lia).
    unfold SPATH_A4.
    kwalk ltac:(fun pc => lazymatch pc with
      | 0x51160%Z => first [ exfalso; lia | fail 100 "cut" pc ]
      | 0x5114c%Z => first [ eapply evt_eq; [| eapply (sp_L5 (Z.to_nat LAST) IP IL FPT FL IP (IL + FL)%Z)];
                             [num_st_eq | exact INV | assumption | exact PF | lia | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.
End SPACC.