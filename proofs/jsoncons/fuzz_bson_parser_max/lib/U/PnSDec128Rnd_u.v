(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk L5Defs L5Core L5CoreKit
     AxSymExec3. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PnDecFacts PnMemW. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSDec128Defs_u PnSDec128RP_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDRN.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma to_bv_of_unsigned (b : bv 64) z : bv_unsigned b = z -> b = Z_to_bv 64 z.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section Call.
Variables (R0 : bvmap 5 word) (S first sigma e V r : Z).
Let u8 := bv_unsigned (getr R0 (reg 8)).
Let u9 := bv_unsigned (getr R0 (reg 9)).
Let u18 := bv_unsigned (getr R0 (reg 18)).
Let u19 := bv_unsigned (getr R0 (reg 19)).
Let u20 := bv_unsigned (getr R0 (reg 20)).
Let u21 := bv_unsigned (getr R0 (reg 21)).
Let u22 := bv_unsigned (getr R0 (reg 22)).
Let u23 := bv_unsigned (getr R0 (reg 23)).
Hypothesis Fr : 0 <= r < 2 ^ 47.
Hypothesis FS : 140735332483312 <= S <= 140737488355328.
Hypothesis F16 : S mod 16 = 0.
Hypothesis Ffirst : 4096 <= first <= 140737488355286.
Hypothesis Fdj : S - 18432 + 18432 <= first \/ first + 42 <= S - 18432.
Hypothesis Fe : 0 <= e <= 16383.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis FV : 0 <= V < 2 ^ 114.

(* [comment removed for export] *)
Abbreviation saves := (PNSDD.saves R0 S r).
Abbreviation MI := (PNSDD.MI R0 S first r).
Abbreviation cell := (PNSDD.cell S).
Abbreviation digs := (PNSDD.digs S V).
Abbreviation zers := (PNSDD.zers S).
Abbreviation MI_xfer := (PNSDD.MI_xfer R0 S first r FS).
Abbreviation cell_xfer := (PNSDD.cell_xfer S FS).
(* [comment removed for export] *)
Definition RR (R : bvmap 5 word) (k : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 256) /\ getr R (reg 5) = Z_to_bv 64 18446744073709551607 /\ getr R (reg 6) = Z_to_bv 64 18446744073709551603 /\
  getr R (reg 7) = Z_to_bv 64 19342813113834067 /\ getr R (reg 8) = Z_to_bv 64 (first + 42) /\ getr R (reg 9) = Z_to_bv 64 (first + sigma) /\
  getr R (reg 12) = Z_to_bv 64 (3 - k) /\ getr R (reg 13) = Z_to_bv 64 (S - 240) /\ getr R (reg 14) = Z_to_bv 64 (S - 184 + 36 * k) /\
  getr R (reg 15) = Z_to_bv 64 18446744073709551580 /\ getr R (reg 16) = Z_to_bv 64 (S - 216) /\ getr R (reg 17) = Z_to_bv 64 (S - 256) /\
  getr R (reg 18) = Z_to_bv 64 first /\ getr R (reg 28) = Z_to_bv 64 1000000000 /\ getr R (reg 29) = Z_to_bv 64 14757395259826634752 /\
  getr R (reg 30) = Z_to_bv 64 10 /\
  getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4) /\
  getr R (reg 24) = getr R0 (reg 24) /\ getr R (reg 25) = getr R0 (reg 25) /\ getr R (reg 26) = getr R0 (reg 26) /\ getr R (reg 27) = getr R0 (reg 27).
(* [comment removed for export] *)
Definition VV (k : Z) (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 38%nat => sigma | 40%nat => k | 50%nat => e
  | 60%nat => r | 61%nat => u8 | 62%nat => u9 | 63%nat => u18 | 64%nat => u19 | 65%nat => u20 | 66%nat => u21 | 67%nat => u22 | 68%nat => u23 | _ => 0 end.

Lemma ufacts : 0 <= u8 < 2 ^ 64 /\ 0 <= u9 < 2 ^ 64 /\ 0 <= u18 < 2 ^ 64 /\ 0 <= u19 < 2 ^ 64 /\ 0 <= u20 < 2 ^ 64 /\ 0 <= u21 < 2 ^ 64
  /\ 0 <= u22 < 2 ^ 64 /\ 0 <= u23 < 2 ^ 64.
Proof.
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 8))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 9))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 18))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 19))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 20))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 21))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 22))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 23))).
  unfold bv_modulus in *. subst u8 u9 u18 u19 u20 u21 u22 u23. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma limbs fx R M k P0 P1 P2 P3 :
  RR R k -> getr R (reg 31) = Z_to_bv 64 k -> getr R (reg 21) = Z_to_bv 64 (S - 256) -> getr R (reg 20) = Z_to_bv 64 0 ->
  0 <= k <= 3 -> 0 <= P0 < 1000000000 -> 0 <= P1 < 2 ^ 32 -> 0 <= P2 < 2 ^ 32 -> 0 <= P3 < 2 ^ 32 -> MI M ->
  L5.u32_at RSEGS M (S - 256) P0 -> L5.u32_at RSEGS M (S - 252) P1 -> L5.u32_at RSEGS M (S - 248) P2 -> L5.u32_at RSEGS M (S - 244) P3 ->
  let r0 := PNDF.lrem 0 P0 in let r1 := PNDF.lrem r0 P1 in let r2 := PNDF.lrem r1 P2 in let r3 := PNDF.lrem r2 P3 in
  exists fx' R' M', msteps RSEGS (st fx R 0x38c1c M) (st fx' R' 0x38c48 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 256 <= a < S - 240) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ RR R' k /\ getr R' (reg 31) = Z_to_bv 64 k /\ getr R' (reg 20) = Z_to_bv 64 r3 /\ getr R' (reg 19) = getr R (reg 19)
    /\ getr R' (reg 10) = getr R (reg 10) /\ getr R' (reg 11) = getr R (reg 11) /\ MI M'
    /\ L5.u32_at RSEGS M' (S - 256) (PNDF.lquot 0 P0) /\ L5.u32_at RSEGS M' (S - 252) (PNDF.lquot r0 P1)
    /\ L5.u32_at RSEGS M' (S - 248) (PNDF.lquot r1 P2) /\ L5.u32_at RSEGS M' (S - 244) (PNDF.lquot r2 P3).
Proof using Fr FS F16 Ffirst Fdj Fe Fsig.
  intros RRk G31 G21 G20 Hk HP0 HP1 HP2 HP3 MIM C0 C1 C2 C3. cbn zeta.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof (PNDF.ldiv4 P0 P1 P2 P3 HP0 HP1 HP2 HP3) as LD. cbn zeta in LD.
  destruct LD as (EW & Hr3 & Hq0 & Hq1 & Hq2 & Hq3 & Hr0 & Hr1 & Hr2).
  set (r0 := PNDF.lrem 0 P0) in *. set (r1 := PNDF.lrem r0 P1) in *. set (r2 := PNDF.lrem r1 P2) in *. set (r3 := PNDF.lrem r2 P3) in *.
  set (q0 := PNDF.lquot 0 P0) in *. set (q1 := PNDF.lquot r0 P1) in *. set (q2 := PNDF.lquot r1 P2) in *. set (q3 := PNDF.lquot r2 P3) in *.
  (* [comment removed for export] *)
  assert (Eq0 : q0 = PNDF.lquot 0 P0) by reflexivity. assert (Eq1 : q1 = PNDF.lquot r0 P1) by reflexivity.
  assert (Eq2 : q2 = PNDF.lquot r1 P2) by reflexivity. assert (Eq3 : q3 = PNDF.lquot r2 P3) by reflexivity.
  assert (Er0 : r0 = PNDF.lrem 0 P0) by reflexivity. assert (Er1 : r1 = PNDF.lrem r0 P1) by reflexivity.
  assert (Er2 : r2 = PNDF.lrem r1 P2) by reflexivity. assert (Er3 : r3 = PNDF.lrem r2 P3) by reflexivity.
  clearbody r0 r1 r2 r3 q0 q1 q2 q3.
  destruct RRk as (G2 & G5 & G6 & G7 & G8 & G9 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G28 & G29 & G30 & G3 & G4 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (XF : forall Ma Mb lo (a v : Z), (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < lo + 4) -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) ->
            (a + 4 <= lo \/ lo + 4 <= a) -> S - 256 <= a <= S - 244 -> L5.u32_at RSEGS Ma a v -> L5.u32_at RSEGS Mb a v).
  { intros Ma Mb lo a v FZ Ha Hb C. apply (PNMW.u32_at_agree RSEGS Ma Mb); [| clear -Hb FS; lia| clear -Hb FS; lia| exact C].
    intros x Hx. apply FZ; clear -Hx Ha Hb FS; lia. }
  assert (XM : forall Ma Mb lo, MI Ma -> mem_grows Ma Mb -> S - 256 <= lo <= S - 244 ->
            (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < lo + 4) -> Mb (Z_to_bv 64 i) = Ma (Z_to_bv 64 i)) -> MI Mb).
  { intros Ma Mb lo HM MG Hlo FZ. apply (MI_xfer Ma Mb HM MG). intros a Ha Hn. apply FZ; [exact Ha| clear -Hn Hlo; lia]. }
  (* [comment removed for export] *)
  (let T := type of (PNSDRP.dkL0_conc fx R M (fun i => match i with 44%nat => 0 | 45%nat => P0 | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkL0_conc fx R M (fun i => match i with 44%nat => 0 | 45%nat => P0 | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FZ1 & MS1 & KS1 & B20 & A21 & _ & D0)); PMK.pvz_clrT.
  change (bv_unsigned (getr R1 (reg 20)) = PNDF.lrem 0 P0) in B20. rewrite <- Er0 in B20. apply to_bv_of_unsigned in B20.
  change (L5.u32_at RSEGS M1 (S - 256) (PNDF.lquot 0 P0)) in D0. rewrite <- Eq0 in D0.
  pose proof (XM M M1 (S - 256) MIM MG1 ltac:(clear; lia) FZ1) as MI1. pose proof MI1 as (WRf1 & WR11 & IC1 & (T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18 & T19)).
  pose proof (XF M M1 (S - 256) (S - 252) P1 FZ1 ltac:(clear; lia) ltac:(clear; lia) C1) as C11.
  pose proof (XF M M1 (S - 256) (S - 248) P2 FZ1 ltac:(clear; lia) ltac:(clear; lia) C2) as C21.
  pose proof (XF M M1 (S - 256) (S - 244) P3 FZ1 ltac:(clear; lia) ltac:(clear; lia) C3) as C31.
  (let T := type of (PNSDRP.dkL1_conc fx1 R1 M1 (fun i => match i with 44%nat => r0 | 45%nat => P1 | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkL1_conc fx1 R1 M1 (fun i => match i with 44%nat => r0 | 45%nat => P1 | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG2 & _ & FZ2 & MS2 & KS2 & B20' & A21' & _ & D1)); PMK.pvz_clrT.
  change (bv_unsigned (getr R2 (reg 20)) = PNDF.lrem r0 P1) in B20'. rewrite <- Er1 in B20'. apply to_bv_of_unsigned in B20'.
  change (L5.u32_at RSEGS M2 (S - 252) (PNDF.lquot r0 P1)) in D1. rewrite <- Eq1 in D1.
  pose proof (XM M1 M2 (S - 252) MI1 MG2 ltac:(clear; lia) FZ2) as MI2. pose proof MI2 as (WRf2 & WR12 & IC2 & (T21 & T22 & T23 & T24 & T25 & T26 & T27 & T28 & T29)).
  pose proof (XF M1 M2 (S - 252) (S - 256) q0 FZ2 ltac:(clear; lia) ltac:(clear; lia) D0) as D02.
  pose proof (XF M1 M2 (S - 252) (S - 248) P2 FZ2 ltac:(clear; lia) ltac:(clear; lia) C21) as C22.
  pose proof (XF M1 M2 (S - 252) (S - 244) P3 FZ2 ltac:(clear; lia) ltac:(clear; lia) C31) as C32.
  (let T := type of (PNSDRP.dkL2_conc fx2 R2 M2 (fun i => match i with 44%nat => r1 | 45%nat => P2 | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkL2_conc fx2 R2 M2 (fun i => match i with 44%nat => r1 | 45%nat => P2 | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG3 & _ & FZ3 & MS3 & KS3 & B20'' & A21'' & _ & D2)); PMK.pvz_clrT.
  change (bv_unsigned (getr R3 (reg 20)) = PNDF.lrem r1 P2) in B20''. rewrite <- Er2 in B20''. apply to_bv_of_unsigned in B20''.
  change (L5.u32_at RSEGS M3 (S - 248) (PNDF.lquot r1 P2)) in D2. rewrite <- Eq2 in D2.
  pose proof (XM M2 M3 (S - 248) MI2 MG3 ltac:(clear; lia) FZ3) as MI3. pose proof MI3 as (WRf3 & WR13 & IC3 & (T31 & T32 & T33 & T34 & T35 & T36 & T37 & T38 & T39)).
  pose proof (XF M2 M3 (S - 248) (S - 256) q0 FZ3 ltac:(clear; lia) ltac:(clear; lia) D02) as D03.
  pose proof (XF M2 M3 (S - 248) (S - 252) q1 FZ3 ltac:(clear; lia) ltac:(clear; lia) D1) as D13.
  pose proof (XF M2 M3 (S - 248) (S - 244) P3 FZ3 ltac:(clear; lia) ltac:(clear; lia) C32) as C33.
  (let T := type of (PNSDRP.dkL3_conc fx3 R3 M3 (fun i => match i with 44%nat => r2 | 45%nat => P3 | _ => VV k i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDRP.dkL3_conc fx3 R3 M3 (fun i => match i with 44%nat => r2 | 45%nat => P3 | _ => VV k i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG4 & _ & FZ4 & MS4 & KS4 & B20x & _ & _ & D3)); PMK.pvz_clrT.
  change (bv_unsigned (getr R4 (reg 20)) = PNDF.lrem r2 P3) in B20x. rewrite <- Er3 in B20x. apply to_bv_of_unsigned in B20x.
  change (L5.u32_at RSEGS M4 (S - 244) (PNDF.lquot r2 P3)) in D3. rewrite <- Eq3 in D3.
  pose proof (XM M3 M4 (S - 244) MI3 MG4 ltac:(clear; lia) FZ4) as MI4.
  pose proof (XF M3 M4 (S - 244) (S - 256) q0 FZ4 ltac:(clear; lia) ltac:(clear; lia) D03) as D04.
  pose proof (XF M3 M4 (S - 244) (S - 252) q1 FZ4 ltac:(clear; lia) ltac:(clear; lia) D13) as D14.
  pose proof (XF M3 M4 (S - 244) (S - 248) q2 FZ4 ltac:(clear; lia) ltac:(clear; lia) D2) as D24.
  exists fx4, R4, M4.
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]|].
  split; [intros a Ha; apply MG4; apply MG3; apply MG2; apply MG1; exact Ha|].
  split. { intros a Ha Hn. rewrite (FZ4 a Ha) by (clear -Hn; lia). rewrite (FZ3 a Ha) by (clear -Hn; lia). rewrite (FZ2 a Ha) by (clear -Hn; lia). apply (FZ1 a Ha). clear -Hn; lia. }
  split. { unfold RR. repeat apply conj; PMK.sc. }
  split; [PMK.sc|]. split; [exact B20x|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [exact MI4|].
  split; [exact D04|]. split; [exact D14|]. split; [exact D24| exact D3].
Qed.

End Call.
End PNSDRN.
