(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare HeapIface AxSymExec3 BigLinkBase L5Defs L5Kn L5KnA L5Core L5CoreKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModelFacts
     PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128Defs_b PnADec128P3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADRN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma to_bv_of_unsigned (b : bv 64) z : bv_unsigned b = z -> b = Z_to_bv 64 z.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Definition RRL : list nat := [2; 3; 4; 8; 9; 10; 18; 19; 20; 22; 23; 25; 26; 27]%nat.
Definition RRa (R0 : bvmap 5 word) (S F : Z) (R : bvmap 5 word) (k : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 256) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 256) /\ getr R (reg 10) = Z_to_bv 64 k
  /\ getr R (reg 18) = Z_to_bv 64 (F + 32) /\ getr R (reg 19) = Z_to_bv 64 (3 - k) /\ getr R (reg 20) = Z_to_bv 64 1000000000
  /\ getr R (reg 22) = Z_to_bv 64 (S - 104) /\ getr R (reg 23) = Z_to_bv 64 14757395259826634752 /\ getr R (reg 25) = Z_to_bv 64 19342813113834067
  /\ getr R (reg 26) = Z_to_bv 64 (F + 64 + 36 * k) /\ getr R (reg 27) = Z_to_bv 64 10.
Definition RRo (R0 : bvmap 5 word) (S F : Z) (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 256) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 256) /\ getr R (reg 18) = Z_to_bv 64 (F + 32).
Definition RRB : list nat := [2; 3; 4; 8; 9; 19; 20; 22; 23; 25; 26; 27]%nat.
Definition RRb (R0 : bvmap 5 word) (S F : Z) (R : bvmap 5 word) (k : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 256) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 256)
  /\ getr R (reg 19) = Z_to_bv 64 (3 - k) /\ getr R (reg 20) = Z_to_bv 64 1000000000
  /\ getr R (reg 22) = Z_to_bv 64 (S - 104) /\ getr R (reg 23) = Z_to_bv 64 14757395259826634752 /\ getr R (reg 25) = Z_to_bv 64 19342813113834067
  /\ getr R (reg 26) = Z_to_bv 64 (F + 64 + 36 * k) /\ getr R (reg 27) = Z_to_bv 64 10.
Lemma RRa_keep R0 S F R R' k : RRa R0 S F R k -> (forall j, In j RRL -> getr R' (reg j) = getr R (reg j)) -> RRa R0 S F R' k.
Proof.
  intros H KS. unfold RRa in *. rewrite !KS by (unfold RRL; cbn [In]; tauto). exact H.
Qed.
Lemma RRb_keep R0 S F R R' k : RRb R0 S F R k -> (forall j, In j RRB -> getr R' (reg j) = getr R (reg j)) -> RRb R0 S F R' k.
Proof.
  intros H KS. unfold RRb in *. rewrite !KS by (unfold RRB; cbn [In]; tauto). exact H.
Qed.
Lemma RRb_of_RRa R0 S F R k : RRa R0 S F R k -> RRb R0 S F R k.
Proof.
  intros (G2 & G3 & G4 & G8 & G9 & G10 & G18 & G19 & G20 & G22 & G23 & G25 & G26 & G27). unfold RRb. repeat split; assumption.
Qed.
Lemma RRb_preserved R0 S F R R' k : RRb R0 S F R k -> regs_preserved R R' -> RRb R0 S F R' k.
Proof.
  intros H RP. apply (RRb_keep R0 S F R R' k H). intros j Hj. apply (L5SAR.cs_of_preserved R R' j RP). revert j Hj.
  apply (L5K.incl_b RRB). vm_compute. reflexivity.
Qed.

Section Call.
Variables (R0 : bvmap 5 word) (S F : Z).
Hypothesis FS : 140735332487296 <= S <= 140737488355328.
Hypothesis F32 : S mod 32 = 0.
Hypothesis FF1 : 4096 <= F <= 140737488354816.
Hypothesis FF32 : F mod 32 = 0.
Hypothesis FFSH : 2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784.
Hypothesis FFS : S - 256 + 256 <= F \/ F + 512 <= S - 256.
Hypothesis FFI : 65536 + 6840320 <= F \/ F + 512 <= 65536.
Abbreviation RB := (RRb R0 S F).
Definition VV (k : Z) (i : nat) : Z :=
  match i with 2%nat => S | 40%nat => k | 50%nat => F | _ => 0 end.

Lemma ubv z : 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. clear - Hz. cbn. lia. Qed.
Local Ltac fsc := first [ assumption | (hnf; assumption)
  | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end
  | match goal with |- L5.u32_at _ _ ?a _ => match goal with H : L5.u32_at _ _ ?b _ |- _ => replace a with b by lia; exact H end end | lia ].
Local Ltac zword H :=
  lazymatch type of H with getr ?R1 ?r = AX2.edenot ?E ?e =>
    let t := eval vm_compute in (BL.zcomp e) in
    lazymatch t with Some ?z =>
      let H' := fresh "Z" in
      assert (H' : bv_unsigned (getr R1 r) = BL.zden (BL.uv E) z) by (rewrite H; apply BL.zcomp_sound; vm_compute; reflexivity);
      cbn [BL.zden] in H'; unfold BL.uv in H'; cbn [AX2.ev] in H'; clear H; rename H' into H end end.

(* [comment removed for export] *)
Definition limb_step (j : Z) (pc1 : Z) : Prop :=
  forall fx R M k rr p, RB R k -> getr R (reg 10) = Z_to_bv 64 (S - 120 + 4 * j) -> getr R (reg 18) = Z_to_bv 64 (F + 28 + 36 * k) ->
    getr R (reg 21) = Z_to_bv 64 rr -> getr R (reg 24) = Z_to_bv 64 k -> 0 <= k <= 3 -> 0 <= rr < 1000000000 -> 0 <= p < 2 ^ 32 ->
    L5.writable RSEGS M (S - 256) 256 -> L5.u32_at RSEGS M (S - 120 + 4 * j) p ->
    exists fx' R' M', msteps RSEGS (st fx R 0xb41c8 M) (st fx' R' pc1 M') /\ mem_grows M M'
      /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 + 4 * j <= a < S - 120 + 4 * j + 4) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
      /\ RB R' k /\ getr R' (reg 10) = Z_to_bv 64 (S - 120 + 4 * (j + 1)) /\ getr R' (reg 18) = Z_to_bv 64 (F + 28 + 36 * k)
      /\ getr R' (reg 21) = Z_to_bv 64 (PNDF.lrem rr p) /\ getr R' (reg 24) = Z_to_bv 64 k
      /\ L5.u32_at RSEGS M' (S - 120 + 4 * j) (PNDF.lquot rr p).

Local Ltac limb_tac CONC KSL :=
  intros fx R M k rr p RRk G10 G18 G21 G24 Hk Hrr Hp WR C0;
  pose proof RRk as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 & G27);
  let P := fresh "P" in
  pose proof (CONC fx R M (fun i => match i with 44%nat => rr | 45%nat => p | _ => VV k i end)) as P; cbn beta iota delta [VV] in P;
  repeat match type of G10 with context [?a + 4 * ?b] => let v := eval vm_compute in (4 * b) in change (4 * b) with v in * end;
  L5SAR.feed P ltac:(fsc);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A10 & A11 & A12 & A21 & A28 & A29 & A31 & D0);
  zword A21; rewrite (ubv rr), (ubv p) in A21 by lia; unfold BL.MM in A21;
  match type of D0 with L5.u32_at _ _ ?a _ => change (L5.u32_at RSEGS M1 a (PNDF.lquot rr p)) in D0 end;
  exists fx1, R1, M1; split; [exact MS1|]; split; [exact MG1|];
  split; [intros a Ha Hn; apply (FZ1 a Ha); intros Y; apply Hn; lia|];
  split; [apply (RRb_keep R0 S F R R1 k RRk); intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b RRB KSL); vm_compute; reflexivity|];
  split; [rewrite A10; f_equal; lia|];
  split; [rewrite (KS1 18%nat) by inl; exact G18|];
  split; [apply to_bv_of_unsigned; rewrite A21; unfold PNDF.lrem, PNDF.lquot, PNDF.ltemp; reflexivity|];
  split; [rewrite (KS1 24%nat) by inl; exact G24|];
  match type of D0 with L5.u32_at _ _ ?a _ => match goal with |- L5.u32_at _ _ ?b _ => replace b with a by lia; exact D0 end end.

Lemma limb0 : limb_step 0 0xb41c8. Proof. unfold limb_step. limb_tac PNADP3.adkL0_conc PNADP3.KS_adkL0. Qed.
Lemma limb1 : limb_step 1 0xb41c8. Proof. unfold limb_step. limb_tac PNADP3.adkL1_conc PNADP3.KS_adkL1. Qed.
Lemma limb2 : limb_step 2 0xb41c8. Proof. unfold limb_step. limb_tac PNADP3.adkL2_conc PNADP3.KS_adkL2. Qed.
Lemma limb3 : limb_step 3 0xb41f4. Proof. unfold limb_step. limb_tac PNADP3.adkL3_conc PNADP3.KS_adkL3. Qed.

(* [comment removed for export] *)
Lemma part_keep (Ma Mb : mem) lo a v : (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < lo + 4) -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) ->
  (a + 4 <= lo \/ lo + 4 <= a) -> S - 120 <= a <= S - 108 -> L5.u32_at RSEGS Ma a v -> L5.u32_at RSEGS Mb a v.
Proof.
  intros FZ Ha Hb U. apply (PMF.u32_at_agree RSEGS Ma Mb); [| lia| lia| exact U]. intros x Hx. apply FZ; lia.
Qed.

(* [comment removed for export] *)
Lemma limbs_call fx R M k P0 P1 P2 P3 :
  RB R k -> getr R (reg 10) = Z_to_bv 64 (S - 120) -> getr R (reg 18) = Z_to_bv 64 (F + 28 + 36 * k) ->
  getr R (reg 21) = Z_to_bv 64 0 -> getr R (reg 24) = Z_to_bv 64 k ->
  0 <= k <= 3 -> 0 <= P0 < 2 ^ 32 -> 0 <= P1 < 2 ^ 32 -> 0 <= P2 < 2 ^ 32 -> 0 <= P3 < 2 ^ 32 -> L5.writable RSEGS M (S - 256) 256 ->
  L5.u32_at RSEGS M (S - 120) P0 -> L5.u32_at RSEGS M (S - 116) P1 -> L5.u32_at RSEGS M (S - 112) P2 -> L5.u32_at RSEGS M (S - 108) P3 ->
  let r0 := PNDF.lrem 0 P0 in let r1 := PNDF.lrem r0 P1 in let r2 := PNDF.lrem r1 P2 in let r3 := PNDF.lrem r2 P3 in
  exists fx' R' M', msteps RSEGS (st fx R 0xb41c8 M) (st fx' R' 0x77c94 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 <= a < S - 104) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ RB R' k /\ getr R' (reg 18) = Z_to_bv 64 (F + 28 + 36 * k) /\ getr R' (reg 21) = Z_to_bv 64 r3 /\ getr R' (reg 24) = Z_to_bv 64 k
    /\ getr R' (reg 1) = Z_to_bv 64 0xb4204 /\ getr R' (reg 10) = Z_to_bv 64 (S - 136) /\ getr R' (reg 11) = Z_to_bv 64 (S - 120)
    /\ getr R' (reg 12) = Z_to_bv 64 16
    /\ L5.u32_at RSEGS M' (S - 120) (PNDF.lquot 0 P0) /\ L5.u32_at RSEGS M' (S - 116) (PNDF.lquot r0 P1)
    /\ L5.u32_at RSEGS M' (S - 112) (PNDF.lquot r1 P2) /\ L5.u32_at RSEGS M' (S - 108) (PNDF.lquot r2 P3).
Proof.
  intros RRk G10 G18 G21 G24 Hk HP0 HP1 HP2 HP3 WR C0 C1 C2 C3. cbn zeta.
  assert (Hr0 : 0 <= PNDF.lrem 0 P0 < 1000000000) by (rewrite PNDF.lrem_val by lia; apply Z.mod_pos_bound; lia).
  set (r0 := PNDF.lrem 0 P0) in *.
  assert (Hr1 : 0 <= PNDF.lrem r0 P1 < 1000000000) by (rewrite PNDF.lrem_val by lia; apply Z.mod_pos_bound; lia).
  set (r1 := PNDF.lrem r0 P1) in *.
  assert (Hr2 : 0 <= PNDF.lrem r1 P2 < 1000000000) by (rewrite PNDF.lrem_val by lia; apply Z.mod_pos_bound; lia).
  set (r2 := PNDF.lrem r1 P2) in *.
  assert (Hr3 : 0 <= PNDF.lrem r2 P3 < 1000000000) by (rewrite PNDF.lrem_val by lia; apply Z.mod_pos_bound; lia).
  set (r3 := PNDF.lrem r2 P3) in *.
  set (q0 := PNDF.lquot 0 P0). set (q1 := PNDF.lquot r0 P1). set (q2 := PNDF.lquot r1 P2). set (q3 := PNDF.lquot r2 P3).
  destruct (limb0 fx R M k 0 P0 RRk ltac:(rewrite G10; f_equal; lia) G18 G21 G24 Hk ltac:(lia) HP0 WR ltac:(replace (S - 120 + 4 * 0) with (S - 120) by lia; exact C0))
    as (fx1 & R1 & M1 & MS1 & MG1 & FZ1 & RR1 & A10 & A18 & A21 & A24 & D0). replace (S - 120 + 4 * 0) with (S - 120) in * by lia.
  pose proof (L5.writable_grows RSEGS M M1 _ _ MG1 WR) as WR1.
  pose proof (part_keep M M1 (S - 120) (S - 116) P1 FZ1 ltac:(lia) ltac:(lia) C1) as C11.
  pose proof (part_keep M M1 (S - 120) (S - 112) P2 FZ1 ltac:(lia) ltac:(lia) C2) as C21.
  pose proof (part_keep M M1 (S - 120) (S - 108) P3 FZ1 ltac:(lia) ltac:(lia) C3) as C31.
  destruct (limb1 fx1 R1 M1 k r0 P1 RR1 A10 A18 A21 A24 Hk Hr0 HP1 WR1 ltac:(replace (S - 120 + 4 * 1) with (S - 116) by lia; exact C11))
    as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & RR2 & B10 & B18 & B21 & B24 & D1). replace (S - 120 + 4 * 1) with (S - 116) in * by lia.
  pose proof (L5.writable_grows RSEGS M1 M2 _ _ MG2 WR1) as WR2.
  pose proof (part_keep M1 M2 (S - 116) (S - 120) q0 FZ2 ltac:(lia) ltac:(lia) D0) as D02.
  pose proof (part_keep M1 M2 (S - 116) (S - 112) P2 FZ2 ltac:(lia) ltac:(lia) C21) as C22.
  pose proof (part_keep M1 M2 (S - 116) (S - 108) P3 FZ2 ltac:(lia) ltac:(lia) C31) as C32.
  destruct (limb2 fx2 R2 M2 k r1 P2 RR2 B10 B18 B21 B24 Hk Hr1 HP2 WR2 ltac:(replace (S - 120 + 4 * 2) with (S - 112) by lia; exact C22))
    as (fx3 & R3 & M3 & MS3 & MG3 & FZ3 & RR3 & E10 & E18 & E21 & E24 & D2). replace (S - 120 + 4 * 2) with (S - 112) in * by lia.
  pose proof (L5.writable_grows RSEGS M2 M3 _ _ MG3 WR2) as WR3.
  pose proof (part_keep M2 M3 (S - 112) (S - 120) q0 FZ3 ltac:(lia) ltac:(lia) D02) as D03.
  pose proof (part_keep M2 M3 (S - 112) (S - 116) q1 FZ3 ltac:(lia) ltac:(lia) D1) as D13.
  pose proof (part_keep M2 M3 (S - 112) (S - 108) P3 FZ3 ltac:(lia) ltac:(lia) C32) as C33.
  destruct (limb3 fx3 R3 M3 k r2 P3 RR3 E10 E18 E21 E24 Hk Hr2 HP3 WR3 ltac:(replace (S - 120 + 4 * 3) with (S - 108) by lia; exact C33))
    as (fx4 & R4 & M4 & MS4 & MG4 & FZ4 & RR4 & H10 & H18 & H21 & H24 & D3). replace (S - 120 + 4 * 3) with (S - 108) in * by lia.
  pose proof (L5.writable_grows RSEGS M3 M4 _ _ MG4 WR3) as WR4.
  pose proof (part_keep M3 M4 (S - 108) (S - 120) q0 FZ4 ltac:(lia) ltac:(lia) D03) as D04.
  pose proof (part_keep M3 M4 (S - 108) (S - 116) q1 FZ4 ltac:(lia) ltac:(lia) D13) as D14.
  pose proof (part_keep M3 M4 (S - 108) (S - 112) q2 FZ4 ltac:(lia) ltac:(lia) D2) as D24.
  clear G10 G18 G21 G24 A10 A18 A21 A24 B10 B18 B21 B24 E10 E18 E21 E24.
  pose proof RR4 as (G2 & G3 & G4 & G8 & G9 & G19 & G20 & G22 & G23 & G25 & G26 & G27).
  pose proof (PNADP3.adkRM_conc fx4 R4 M4 (fun i => match i with 48%nat => r3 | _ => VV k i end)) as P; cbn beta iota delta [VV] in P.
  L5SAR.feed P ltac:(fsc).
  destruct P as (fx5 & R5 & M5 & MG5 & _ & FZ5 & MS5 & KS5 & B1 & B10 & B11 & B12).
  assert (EM : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FZ5). subst M5.
  exists fx5, R5, M4.
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| eapply msteps_trans; [exact MS4| exact MS5]]]]|].
  split; [intros a Ha; apply MG4; apply MG3; apply MG2; apply MG1; exact Ha|].
  split. { intros a Ha Hn. rewrite (FZ4 a Ha) by lia. rewrite (FZ3 a Ha) by lia. rewrite (FZ2 a Ha) by lia. apply (FZ1 a Ha). lia. }
  split; [apply (RRb_keep R0 S F R4 R5 k RR4); intros j Hj; apply KS5; revert j Hj; apply (L5K.incl_b RRB); vm_compute; reflexivity|].
  split; [rewrite (KS5 18%nat) by inl; exact H18|]. split; [rewrite (KS5 21%nat) by inl; exact H21|]. split; [rewrite (KS5 24%nat) by inl; exact H24|].
  split; [exact B1|]. split; [exact B10|]. split; [exact B11|]. split; [exact B12|].
  split; [exact D04|]. split; [exact D14|]. split; [exact D24| exact D3].
Qed.

End Call.
End PNADRN.
