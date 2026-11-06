(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare L5Defs L5Kn L5KnA L5Core L5CoreKit L5DefsA L5StepAR PmModelFacts
     PnDecFacts PnADec128Defs PnADec128P3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADRN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma to_bv_of_unsigned (b : bv 64) z : bv_unsigned b = z -> b = Z_to_bv 64 z.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Definition RRL : list nat := [2; 3; 4; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 26; 27]%nat.
Definition RRa (R0 : bvmap 5 word) (S F first sigma E1 : Z) (R : bvmap 5 word) (k : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 128) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 5) = Z_to_bv 64 14757395259826634752 /\ getr R (reg 6) = Z_to_bv 64 10
  /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 128) /\ getr R (reg 10) = Z_to_bv 64 (3 - k)
  /\ getr R (reg 11) = Z_to_bv 64 E1 /\ getr R (reg 12) = Z_to_bv 64 16383 /\ getr R (reg 13) = Z_to_bv 64 (S - 104)
  /\ getr R (reg 14) = Z_to_bv 64 (F + 64 + 36 * k) /\ getr R (reg 15) = Z_to_bv 64 (-36) /\ getr R (reg 16) = Z_to_bv 64 19342813113834067
  /\ getr R (reg 17) = Z_to_bv 64 1000000000 /\ getr R (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R (reg 19) = Z_to_bv 64 F
  /\ getr R (reg 20) = Z_to_bv 64 (first + 42) /\ getr R (reg 21) = Z_to_bv 64 (first + sigma) /\ getr R (reg 22) = Z_to_bv 64 first
  /\ getr R (reg 23) = Z_to_bv 64 (F + 32) /\ getr R (reg 26) = Z_to_bv 64 F /\ getr R (reg 27) = Z_to_bv 64 2147450880.
Lemma RRa_keep R0 S F first sigma E1 R R' k : RRa R0 S F first sigma E1 R k -> (forall j, In j RRL -> getr R' (reg j) = getr R (reg j)) -> RRa R0 S F first sigma E1 R' k.
Proof.
  intros H KS. unfold RRa in *. rewrite !KS by (unfold RRL; cbn [In]; tauto). exact H.
Qed.

Section Call.
Variables (R0 : bvmap 5 word) (S F first sigma E1 : Z).
Hypothesis FS : 140735332487296 <= S <= 140737488355328.
Hypothesis F32 : S mod 32 = 0.
Hypothesis FF1 : 4096 <= F <= 140737488354816.
Hypothesis Ffirst : 4096 <= first <= 140737488355280.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis FE1 : 0 <= E1 < 2 ^ 64.
Abbreviation RR := (RRa R0 S F first sigma E1).
Definition VV (k : Z) (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 38%nat => first + sigma | 40%nat => k | 50%nat => F | 59%nat => E1 | _ => 0 end.

Local Ltac rsc := first [ assumption | (hnf; assumption) | lia ].

(* [comment removed for export] *)
Definition limb_step (j : Z) (pc1 : Z) : Prop :=
  forall fx R M k rr p, RR R k -> getr R (reg 7) = Z_to_bv 64 k -> getr R (reg 28) = Z_to_bv 64 (S - 120 + 4 * j) -> getr R (reg 30) = Z_to_bv 64 (F + 28 + 36 * k) ->
    getr R (reg 31) = Z_to_bv 64 rr -> 0 <= k <= 3 -> 0 <= rr < 1000000000 -> 0 <= p < 2 ^ 32 ->
    L5.writable RSEGS M (S - 128) 128 -> L5.u32_at RSEGS M (S - 120 + 4 * j) p ->
    exists fx' R' M', msteps RSEGS (st fx R 0xb2a64 M) (st fx' R' pc1 M') /\ mem_grows M M'
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 + 4 * j <= a < S - 120 + 4 * j + 4) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      /\ RR R' k /\ getr R' (reg 7) = Z_to_bv 64 k /\ getr R' (reg 28) = Z_to_bv 64 (S - 120 + 4 * (j + 1)) /\ getr R' (reg 30) = Z_to_bv 64 (F + 28 + 36 * k)
      /\ getr R' (reg 31) = Z_to_bv 64 (PNDF.lrem rr p) /\ L5.u32_at RSEGS M' (S - 120 + 4 * j) (PNDF.lquot rr p).

Local Ltac limb_tac CONC KSL :=
  intros fx R M k rr p RRk G7 G28 G30 G31 Hk Hrr Hp WR C0;
  pose proof RRk as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27);
  let P := fresh "P" in
  pose proof (CONC fx R M (fun i => match i with 44%nat => rr | 45%nat => p | _ => VV k i end)) as P; cbn beta iota delta [VV] in P;
  repeat match type of G28 with context [?a + 4 * ?b] => let v := eval vm_compute in (4 * b) in change (4 * b) with v in * end;
  L5SAR.feed P ltac:(first [ assumption | (hnf; assumption) | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end
                           | match goal with |- L5.u32_at _ _ ?a _ => match goal with H : L5.u32_at _ _ ?b _ |- _ => replace a with b by lia; exact H end end | lia ]);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A28 & B29 & B31 & D0);
  change (bv_unsigned (getr R1 (reg 31)) = PNDF.lrem rr p) in B31; apply to_bv_of_unsigned in B31;
  match type of D0 with L5.u32_at _ _ ?a _ => change (L5.u32_at RSEGS M1 a (PNDF.lquot rr p)) in D0 end;
  exists fx1, R1, M1; split; [exact MS1|]; split; [exact MG1|];
  split; [intros a Ha Hn; apply (FZ1 a Ha); intros Y; apply Hn; lia|];
  split; [apply (RRa_keep R0 S F first sigma E1 R R1 k RRk); intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b RRL KSL); vm_compute; reflexivity|];
  split; [rewrite (KS1 7%nat) by inl; exact G7|];
  split; [rewrite A28; f_equal; lia|];
  split; [rewrite (KS1 30%nat) by inl; exact G30|];
  split; [exact B31|];
  match type of D0 with L5.u32_at _ _ ?a _ => match goal with |- L5.u32_at _ _ ?b _ => replace b with a by lia; exact D0 end end.

Lemma limb0 : limb_step 0 0xb2a64. Proof. unfold limb_step. limb_tac PNADP3.adkL0_conc PNADP3.KS_adkL0. Qed.
Lemma limb1 : limb_step 1 0xb2a64. Proof. unfold limb_step. limb_tac PNADP3.adkL1_conc PNADP3.KS_adkL1. Qed.
Lemma limb2 : limb_step 2 0xb2a64. Proof. unfold limb_step. limb_tac PNADP3.adkL2_conc PNADP3.KS_adkL2. Qed.
Lemma limb3 : limb_step 3 0xb2a90. Proof. unfold limb_step. limb_tac PNADP3.adkL3_conc PNADP3.KS_adkL3. Qed.

(* [comment removed for export] *)
Lemma part_keep (Ma Mb : mem) lo a v : (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < lo + 4) -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) ->
  (a + 4 <= lo \/ lo + 4 <= a) -> S - 120 <= a <= S - 108 -> L5.u32_at RSEGS Ma a v -> L5.u32_at RSEGS Mb a v.
Proof.
  intros FZ Ha Hb U. apply (PMF.u32_at_agree RSEGS Ma Mb); [| lia| lia| exact U]. intros x Hx. apply FZ; lia.
Qed.

(* [comment removed for export] *)
Lemma limbs fx R M k P0 P1 P2 P3 :
  RR R k -> getr R (reg 7) = Z_to_bv 64 k -> getr R (reg 28) = Z_to_bv 64 (S - 120) -> getr R (reg 30) = Z_to_bv 64 (F + 28 + 36 * k) -> getr R (reg 31) = Z_to_bv 64 0 ->
  0 <= k <= 3 -> 0 <= P0 < 1000000000 -> 0 <= P1 < 2 ^ 32 -> 0 <= P2 < 2 ^ 32 -> 0 <= P3 < 2 ^ 32 -> L5.writable RSEGS M (S - 128) 128 ->
  L5.u32_at RSEGS M (S - 120) P0 -> L5.u32_at RSEGS M (S - 116) P1 -> L5.u32_at RSEGS M (S - 112) P2 -> L5.u32_at RSEGS M (S - 108) P3 ->
  let r0 := PNDF.lrem 0 P0 in let r1 := PNDF.lrem r0 P1 in let r2 := PNDF.lrem r1 P2 in let r3 := PNDF.lrem r2 P3 in
  exists fx' R' M', msteps RSEGS (st fx R 0xb2a64 M) (st fx' R' 0xb2a90 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 <= a < S - 104) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ RR R' k /\ getr R' (reg 7) = Z_to_bv 64 k /\ getr R' (reg 28) = Z_to_bv 64 (S - 104) /\ getr R' (reg 30) = Z_to_bv 64 (F + 28 + 36 * k) /\ getr R' (reg 31) = Z_to_bv 64 r3
    /\ L5.writable RSEGS M' (S - 128) 128
    /\ L5.u32_at RSEGS M' (S - 120) (PNDF.lquot 0 P0) /\ L5.u32_at RSEGS M' (S - 116) (PNDF.lquot r0 P1)
    /\ L5.u32_at RSEGS M' (S - 112) (PNDF.lquot r1 P2) /\ L5.u32_at RSEGS M' (S - 108) (PNDF.lquot r2 P3).
Proof.
  intros RRk G7 G28 G30 G31 Hk HP0 HP1 HP2 HP3 WR C0 C1 C2 C3. cbn zeta.
  pose proof (PNDF.ldiv4 P0 P1 P2 P3 HP0 HP1 HP2 HP3) as LD. cbn zeta in LD.
  destruct LD as (EW & Hr3 & Hq0 & Hq1 & Hq2 & Hq3 & Hr0 & Hr1 & Hr2).
  set (r0 := PNDF.lrem 0 P0) in *. set (r1 := PNDF.lrem r0 P1) in *. set (r2 := PNDF.lrem r1 P2) in *. set (r3 := PNDF.lrem r2 P3) in *.
  set (q0 := PNDF.lquot 0 P0) in *. set (q1 := PNDF.lquot r0 P1) in *. set (q2 := PNDF.lquot r1 P2) in *. set (q3 := PNDF.lquot r2 P3) in *.
  assert (Eq0 : q0 = PNDF.lquot 0 P0) by reflexivity. assert (Eq1 : q1 = PNDF.lquot r0 P1) by reflexivity.
  assert (Eq2 : q2 = PNDF.lquot r1 P2) by reflexivity. assert (Eq3 : q3 = PNDF.lquot r2 P3) by reflexivity.
  assert (Er0 : r0 = PNDF.lrem 0 P0) by reflexivity. assert (Er1 : r1 = PNDF.lrem r0 P1) by reflexivity.
  assert (Er2 : r2 = PNDF.lrem r1 P2) by reflexivity. assert (Er3 : r3 = PNDF.lrem r2 P3) by reflexivity.
  clearbody r0 r1 r2 r3 q0 q1 q2 q3.
  destruct (limb0 fx R M k 0 P0 RRk G7 ltac:(rewrite G28; f_equal; lia) G30 G31 Hk ltac:(lia) ltac:(lia) WR ltac:(replace (S - 120 + 4 * 0) with (S - 120) by lia; exact C0))
    as (fx1 & R1 & M1 & MS1 & MG1 & FZ1 & RR1 & A7 & A28 & A30 & A31 & D0). rewrite <- Er0 in A31. rewrite <- Eq0 in D0. replace (S - 120 + 4 * 0) with (S - 120) in * by lia.
  pose proof (L5.writable_grows RSEGS M M1 _ _ MG1 WR) as WR1.
  pose proof (part_keep M M1 (S - 120) (S - 116) P1 FZ1 ltac:(lia) ltac:(lia) C1) as C11.
  pose proof (part_keep M M1 (S - 120) (S - 112) P2 FZ1 ltac:(lia) ltac:(lia) C2) as C21.
  pose proof (part_keep M M1 (S - 120) (S - 108) P3 FZ1 ltac:(lia) ltac:(lia) C3) as C31.
  destruct (limb1 fx1 R1 M1 k r0 P1 RR1 A7 A28 A30 A31 Hk ltac:(lia) ltac:(lia) WR1 ltac:(replace (S - 120 + 4 * 1) with (S - 116) by lia; exact C11))
    as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & RR2 & B7 & B28 & B30 & B31 & D1). rewrite <- Er1 in B31. rewrite <- Eq1 in D1. replace (S - 120 + 4 * 1) with (S - 116) in * by lia.
  pose proof (L5.writable_grows RSEGS M1 M2 _ _ MG2 WR1) as WR2.
  pose proof (part_keep M1 M2 (S - 116) (S - 120) q0 FZ2 ltac:(lia) ltac:(lia) D0) as D02.
  pose proof (part_keep M1 M2 (S - 116) (S - 112) P2 FZ2 ltac:(lia) ltac:(lia) C21) as C22.
  pose proof (part_keep M1 M2 (S - 116) (S - 108) P3 FZ2 ltac:(lia) ltac:(lia) C31) as C32.
  destruct (limb2 fx2 R2 M2 k r1 P2 RR2 B7 B28 B30 B31 Hk ltac:(lia) ltac:(lia) WR2 ltac:(replace (S - 120 + 4 * 2) with (S - 112) by lia; exact C22))
    as (fx3 & R3 & M3 & MS3 & MG3 & FZ3 & RR3 & E7 & E28 & E30 & E31 & D2). rewrite <- Er2 in E31. rewrite <- Eq2 in D2. replace (S - 120 + 4 * 2) with (S - 112) in * by lia.
  pose proof (L5.writable_grows RSEGS M2 M3 _ _ MG3 WR2) as WR3.
  pose proof (part_keep M2 M3 (S - 112) (S - 120) q0 FZ3 ltac:(lia) ltac:(lia) D02) as D03.
  pose proof (part_keep M2 M3 (S - 112) (S - 116) q1 FZ3 ltac:(lia) ltac:(lia) D1) as D13.
  pose proof (part_keep M2 M3 (S - 112) (S - 108) P3 FZ3 ltac:(lia) ltac:(lia) C32) as C33.
  destruct (limb3 fx3 R3 M3 k r2 P3 RR3 E7 E28 E30 E31 Hk ltac:(lia) ltac:(lia) WR3 ltac:(replace (S - 120 + 4 * 3) with (S - 108) by lia; exact C33))
    as (fx4 & R4 & M4 & MS4 & MG4 & FZ4 & RR4 & H7 & H28 & H30 & H31 & D3). rewrite <- Er3 in H31. rewrite <- Eq3 in D3. replace (S - 120 + 4 * 3) with (S - 108) in * by lia.
  pose proof (L5.writable_grows RSEGS M3 M4 _ _ MG4 WR3) as WR4.
  pose proof (part_keep M3 M4 (S - 108) (S - 120) q0 FZ4 ltac:(lia) ltac:(lia) D03) as D04.
  pose proof (part_keep M3 M4 (S - 108) (S - 116) q1 FZ4 ltac:(lia) ltac:(lia) D13) as D14.
  pose proof (part_keep M3 M4 (S - 108) (S - 112) q2 FZ4 ltac:(lia) ltac:(lia) D2) as D24.
  exists fx4, R4, M4.
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]|].
  split; [intros a Ha; apply MG4; apply MG3; apply MG2; apply MG1; exact Ha|].
  split. { intros a Ha Hn. rewrite (FZ4 a Ha) by lia. rewrite (FZ3 a Ha) by lia. rewrite (FZ2 a Ha) by lia. apply (FZ1 a Ha). lia. }
  split; [exact RR4|]. split; [exact H7|]. split; [rewrite H28; f_equal; clear; lia|]. split; [exact H30|]. split; [exact H31|]. split; [exact WR4|].
  split; [exact D04|]. split; [exact D14|]. split; [exact D24| exact D3].
Qed.

End Call.
End PNADRN.
