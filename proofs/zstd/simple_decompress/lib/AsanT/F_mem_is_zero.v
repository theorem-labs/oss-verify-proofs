(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition mem_is_zero_entry := 0x66430%Z.

(* [comment removed for export] *)
End CANSEC1.
Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_lits :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a <? b)%Z) in change (Z.b2z (a <? b)%Z) with v
  | |- context [Z.b2z (?a =? ?b)%Z] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (a =? b)%Z) in change (Z.b2z (a =? b)%Z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  end.
Ltac pr := match goal with |- evtF _ _ _ (MS ?r _ ?pc _ _ ?mm _) => idtac pc; idtac r end.

Section CANSEC2. Context {rc : runConstT}.
Definition mem_is_zero_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Section Proofs.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z).
  Notation B := (bv_unsigned a0).
  Notation n := (bv_unsigned a1).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 16)%Z.
  Hypothesis SB : shadow_bytes m B (B + n) (fun _ => 0%Z).
  Hypothesis BLO : (0x625000 <= B)%Z.
  Hypothesis SEP : (B + n <= bv_unsigned sp - 16 \/ bv_unsigned sp <= B)%Z.
  Hypothesis SZ : (n <= 2^40)%Z.
  Hypothesis BHI : (B + n + 8 <= 2^64)%Z.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RB : rng RNG B n.

  Notation POST := (mem_is_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  Lemma B_bound : (0 <= B /\ B + n <= 2^64 /\ 0 <= n)%Z.
  Proof. destruct SB as (A & C & _). pose proof (bv_unsigned_in_range 64 a1). lia. Qed.

  (* [comment removed for export] *)
  Section Loops.
    Variables (m1 : word -> option byte) (junk8 : list byte).
    Hypothesis FR : rw_cells bsegs m1 (bv_unsigned sp + -16) [CB 8 junk8; C8 ra].
    Hypothesis ST1 : stk bsegs m1 lo (bv_unsigned sp + -16).
    Hypothesis MU1 : munch [(bv_unsigned sp + -16, bv_unsigned sp)]%Z m m1.
    Hypothesis WM1 : wmono bsegs m m1.
    Hypothesis MI1 : mem_inv bsegs m1.
    Hypothesis SB1 : shadow_bytes m1 B (B + n) (fun _ => 0%Z).
    Variables (AB AE : Z).
    Hypothesis RAB : (B <= AB <= B + 7 /\ AB mod 8 = 0)%Z.
    Hypothesis RAE : (B + n - 7 <= AE <= B + n /\ AE mod 8 = 0)%Z.
    Hypothesis BB : (0 <= B /\ B + n <= 2^64 /\ 0 <= n)%Z.
    Hypothesis LO0 : (0 <= lo)%Z.

    (* [comment removed for export] *)
    Notation AT pc x10 x11 x12 x13 x14 x15 x16 :=
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom bsegs)).

    Lemma L_ret : forall x10 x12 x13 x14 x15 x16,
      evtF bsegs RNG POST (AT 0x664bc x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16).
    Proof.
      intros.
      zstep. fold_lits. zstep. zstep. zstep. fold_lits.
      release_frame FR ST1 (bv_unsigned sp). finish.
    Qed.

    (* [comment removed for export] *)
    Lemma L_epi : forall (k : nat) (c : Z) x10 x13 x15 x16,
      Z.to_nat (B + n - c) = k -> (B <= c < B + n)%Z ->
      evtF bsegs RNG POST (AT 0x664a8 x10 (Z_to_bv 64 0) (Z_to_bv 64 c) x13 (Z_to_bv 64 (B + n - c)) x15 x16).
    Proof.
      induction k as [|k IH]; intros c x10 x13 x15 x16 Hk Hc; [exfalso; lia|].
      pose proof (ov_read1_of_shadow_bytes bsegs m1 B (B + n) (fun _ => 0%Z) c SB1 ltac:(lia)) as RD; cbn beta in RD.
      zstep. cbv beta. zsimp. zstep. zstep. fold_lits.
      zstep. zstep.
      if_cases K; zify_cond K.
      - replace (B + n - c + -1)%Z with (B + n - (c + 1))%Z by lia. apply IH; lia.
      - apply L_ret.
    Qed.

    (* [comment removed for export] *)
    Lemma L_tail : forall x13 x15 x16,
      evtF bsegs RNG POST (AT 0x6649c a0 (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 (B + n)) x15 x16).
    Proof.
      intros.
      zstep. if_cases K1; zify_cond K1. { apply L_ret. }
      zstep. if_cases K2; zify_cond K2. { apply L_ret. }
      zstep.
      apply (L_epi (Z.to_nat (B + n - AE)) AE); lia.
    Qed.

    (* [comment removed for export] *)
    Lemma L_word : forall (k : nat) (c : Z) x13 x16,
      Z.to_nat (AE - c) = k -> (AB <= c < AE)%Z -> (c mod 8 = 0)%Z ->
      evtF bsegs RNG POST (AT 0x6648c a0 (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 (B + n)) (Z_to_bv 64 c) x16).
    Proof.
      intros k. induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf). intros c x13 x16 Hk Hc Hal.
      assert (C8 : (c + 8 <= AE)%Z) by (Z.div_mod_to_equations; lia).
      pose proof (ov_read8_zero bsegs m1 B (B + n) (fun _ => 0%Z) c SB1 ltac:(lia) ltac:(lia) ltac:(intros; reflexivity)) as RD.
      zstep. zstep. zstep. fold_lits. zstep.
      if_cases K; zify_cond K.
      - apply (IH (Z.to_nat (AE - (c + 8)))); try lia; Z.div_mod_to_equations; lia.
      - replace (Z_to_bv 64 (c + 8)) with (Z_to_bv 64 AE) by (f_equal; lia). apply L_tail.
    Qed.

    (* [comment removed for export] *)
    Lemma L_mid : forall x13 x16,
      evtF bsegs RNG POST (AT 0x66488 a0 (Z_to_bv 64 0) (Z_to_bv 64 AE) x13 (Z_to_bv 64 (B + n)) (Z_to_bv 64 AB) x16).
    Proof.
      intros. zstep. if_cases K; zify_cond K. { apply L_tail. }
      apply (L_word (Z.to_nat (AE - AB)) AB); lia.
    Qed.

    (* [comment removed for export] *)
    Lemma L_pro : forall (k : nat) (c : Z) x16,
      Z.to_nat (AB - c) = k -> (B <= c < AB)%Z -> (c < B + n)%Z ->
      evtF bsegs RNG POST (AT 0x66470 a0 (Z_to_bv 64 0) (Z_to_bv 64 AE) (Z_to_bv 64 (c + 1)) (Z_to_bv 64 (B + n)) (Z_to_bv 64 AB) x16).
    Proof.
      induction k as [|k IH]; intros c x16 Hk Hc HcE; [exfalso; lia|].
      pose proof (ov_read1_of_shadow_bytes bsegs m1 B (B + n) (fun _ => 0%Z) c SB1 ltac:(lia)) as RD; cbn beta in RD.
      zstep. zstep. cbv beta. zsimp. zstep. fold_lits. zstep.
      if_cases K1; zify_cond K1. { apply L_mid. }
      zstep. zstep.
      if_cases K2; zify_cond K2.
      - replace (c + 2)%Z with ((c + 1) + 1)%Z by lia. apply IH; lia.
      - apply L_mid.
    Qed.
  End Loops.

  Lemma mem_is_zero_body :
    evtF bsegs RNG POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x66430) fc None m (seg_rom bsegs)).
  Proof.
    pose proof B_bound as BB.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    carve_frame 16%nat ST.
    zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with MU1 : munch _ m m1 |- _ =>
        pose proof (shadow_bytes_munch _ m m1 B (B + n) (fun _ => 0%Z) SB MU1 ltac:(cbn; lia)) as SB1 end end.
    do 5 zstep.
    if_cases K; zify_cond K. { exfalso. lia. }
    do 5 zstep.
    change 18446744073709551608%Z with (2^64 - 2^3)%Z. rewrite !land_align_down by lia.
    remember (B + 7 - (B + 7) mod 2 ^ 3)%Z as AB eqn:HAB.
    remember (B + n - (B + n) mod 2 ^ 3)%Z as AE eqn:HAE.
    assert (RAB : (B <= AB <= B + 7 /\ AB mod 8 = 0)%Z) by (subst AB; Z.div_mod_to_equations; lia).
    assert (RAE : (B + n - 7 <= AE <= B + n /\ AE mod 8 = 0)%Z) by (subst AE; Z.div_mod_to_equations; lia).
    clear HAB HAE.
    zstep. if_cases K1; zify_cond K1.
    { eapply L_mid; eassumption. }
    zstep. if_cases K2; zify_cond K2.
    { eapply L_mid; eassumption. }
    zstep. zstep.
    eapply (L_pro m0) with (c := B); try eassumption; [reflexivity | lia | lia].
  Qed.
End Proofs.

Lemma mem_is_zero_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) ->
  (lo <= bv_unsigned sp - 16)%Z ->
  shadow_bytes m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a1) (fun _ => 0%Z) ->
  (0x625000 <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 <= 2^40)%Z ->
  (bv_unsigned a0 + bv_unsigned a1 + 8 <= 2^64)%Z ->
  rng RNG lo (bv_unsigned sp - lo) ->
  rng RNG (bv_unsigned a0) (bv_unsigned a1) ->
  evtF bsegs RNG (mem_is_zero_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x66430) fc None m (seg_rom bsegs)).
Proof. intros until lo. intros MI ST LO SB BLO SEP SZ BHI RSTK RB. eapply mem_is_zero_body; eassumption. Qed.
End CANSEC2.
