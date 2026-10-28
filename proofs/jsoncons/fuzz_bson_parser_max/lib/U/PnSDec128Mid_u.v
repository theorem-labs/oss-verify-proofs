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
     AxSymExec3. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PnDecFacts PnMemW PnDecBv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSDec128Defs_u PnSDec128RP_u PnSDec128AP_u PnSDec128Rnd_u PnSDec128Rnd2_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDMID.
Import PNSDRN PNSDRN2.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Definition outP (R0 : bvmap 5 word) (S first sigma r : Z) (fx : FPState) (R : bvmap 5 word) (pc : Z) (M : word -> option byte) : Prop :=
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 256 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ PNSDD.MI R0 S first r M'
    /\ (exists e' z sd d, msteps RSEGS (st fx R pc M) (st fx' R' 0x38cec M') /\ PNSDD.stP R0 S first sigma e' z sd d R'
          /\ 0 <= e' <= 16383 /\ 0 <= z /\ 1 <= sd /\ z + sd <= 36 /\ 0 <= d <= 9 /\ PNSDD.sdigs S M' z sd).

Section Call.


Variables (R0 : bvmap 5 word) (S first sigma e V r : Z).
Hypothesis Fr : 0 <= r < 2 ^ 47.
Hypothesis FS : 140735332483312 <= S <= 140737488355328.
Hypothesis F16 : S mod 16 = 0.
Hypothesis Ffirst : 4096 <= first <= 140737488355286.
Hypothesis Fdj : S - 18432 + 18432 <= first \/ first + 42 <= S - 18432.
Hypothesis Fe : 0 <= e <= 16383.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis FV : 0 <= V < 2 ^ 114.

Abbreviation saves := (PNSDD.saves R0 S r).
Abbreviation MI := (PNSDD.MI R0 S first r).
Abbreviation cell := (PNSDD.cell S).
Abbreviation digs := (PNSDD.digs S V).
Abbreviation zers := (PNSDD.zers S).
Abbreviation RR := (PNSDRN.RR R0 S first sigma).
Abbreviation ufacts := (PNSDRN.ufacts R0 S).
Abbreviation MI_xfer := (PNSDD.MI_xfer R0 S first r FS).
Abbreviation cell_xfer := (PNSDD.cell_xfer S FS).
Abbreviation VV := (PNSDRN2.VV R0 S first sigma e r).
Abbreviation HD := (PNSDRN2.HD R0 S first sigma V r).
Abbreviation round_step := (PNSDRN2.round_step R0 S first sigma e V r Fr FS F16 Ffirst Fdj Fe Fsig FV).
Abbreviation entry := (PNSDRN2.entry R0 S first sigma V r FS).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rounds fx R M : HD R M 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 256 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M' /\ msteps RSEGS (st fx R 0x38bc4 M) (st fx' R' 0x38c94 M') /\ PNSDD.RB R0 S first sigma R' /\ RR R' (-1)
    /\ getr R' (reg 10) = getr R (reg 10) /\ getr R' (reg 11) = getr R (reg 11) /\ digs M' 0.
Proof.
  intros HD3.
  destruct (round_step fx R M 3 ltac:(clear; lia) HD3) as (fx1 & R1 & M1 & MG1 & FZ1 & MI1 & B10 & B11 & [(K & _) | (_ & MS1 & HD2)]); [exfalso; clear -K; lia|].
  destruct (round_step fx1 R1 M1 (3 - 1) ltac:(clear; lia) HD2) as (fx2 & R2 & M2 & MG2 & FZ2 & MI2 & C10 & C11 & [(K & _) | (_ & MS2 & HD1)]); [exfalso; clear -K; lia|].
  destruct (round_step fx2 R2 M2 (3 - 1 - 1) ltac:(clear; lia) HD1) as (fx3 & R3 & M3 & MG3 & FZ3 & MI3 & D10 & D11 & [(K & _) | (_ & MS3 & HD0)]); [exfalso; clear -K; lia|].
  destruct (round_step fx3 R3 M3 (3 - 1 - 1 - 1) ltac:(clear; lia) HD0) as (fx4 & R4 & M4 & MG4 & FZ4 & MI4 & E10 & E11 & [(_ & MS4 & RB4 & RR4 & _ & _ & DG4) | (K & _)]); [| exfalso; clear -K; lia].
  exists fx4, R4, M4. split; [intros a Ha; apply MG4; apply MG3; apply MG2; apply MG1; exact Ha|].
  split. { intros a Ha Hn. rewrite (FZ4 a Ha Hn), (FZ3 a Ha Hn), (FZ2 a Ha Hn). exact (FZ1 a Ha Hn). }
  split; [exact MI4|].
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]|].
  split; [exact RB4|]. split; [exact RR4|].
  split; [rewrite E10, D10, C10; exact B10|]. split; [rewrite E11, D11, C11; exact B11| exact DG4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma V_lt35 : V < 10 ^ 35.
Proof. clear -FV. assert (2 ^ 114 < 10 ^ 35) by (vm_compute; reflexivity). lia. Qed.
Lemma dg0 : PNDF.dg V 0 = 0.
Proof. unfold PNDF.dg. replace (35 - 0) with 35 by (clear; lia). rewrite Z.div_small; [reflexivity|]. pose proof V_lt35. clear -H FV; lia. Qed.

Lemma scan_loop (FVp : 0 < V) (n : nat) : forall fx R M i,
  35 - i = Z.of_nat n -> 0 <= i <= 34 -> V < 10 ^ (35 - i) ->
  PNSDD.stW R0 S first sigma e R -> getr R (reg 12) = Z_to_bv 64 (36 - i) -> getr R (reg 15) = Z_to_bv 64 18446744073709551611 ->
  getr R (reg 16) = Z_to_bv 64 (S - 216 + 4 * i) -> digs M 0 -> MI M ->
  exists fx' R' z, msteps RSEGS (st fx R 0x38cd0 M) (st fx' R' 0x38cec M) /\ PNSDD.stP R0 S first sigma e z (36 - z) (PNDF.dg V z) R' /\ i < z <= 35.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi HV SW G12 G15 G16 DG MIM.
  { exfalso. clear -Hn Hi. lia. }
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof SW as ((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & (w & G10 & Hw & Ew) & G11).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof (PNDF.dg_range V (i + 1)) as Hd.
  assert (C : L5.u32_at RSEGS M (S - 216 + 4 * i + 4) (PNDF.dg V (i + 1))).
  { pose proof (DG (i + 1) ltac:(clear -Hi; lia)) as C. unfold PNSDD.cell in C. replace (S - 216 + 4 * i + 4) with (S - 216 + 4 * (i + 1)) by (clear; lia). exact C. }
  (let T := type of (PNSDAP.dkSC_conc fx R M (fun j => match j with 52%nat => i | 53%nat => PNDF.dg V (i + 1) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkSC_conc fx R M (fun j => match j with 52%nat => i | 53%nat => PNDF.dg V (i + 1) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A12 & A13 & A14 & A16 & Hz) | (MS1 & KS1 & A12 & A13 & A14 & A16 & Hnz) ]).
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
    rewrite Z.sub_0_r, Z.mod_small in Hz by (clear -Hd; lia).
    assert (D0 : PNDF.dg V (i + 1) = 0) by (clear -Hz Hd; lia).
    pose proof (PNDF.dg_zero_step V (i + 1) ltac:(clear -FV; lia) ltac:(clear -Hi; lia) ltac:(replace (35 - (i + 1) + 1) with (35 - i) by (clear; lia); exact HV) D0) as HV'.
    assert (Hi' : i + 1 <= 34).
    { destruct (Z_lt_le_dec 34 (i + 1)) as [LT|LE]; [| exact LE]. exfalso.
      replace (35 - (i + 1)) with 0 in HV' by (clear -LT Hi; lia). clear -HV' FVp. cbn in HV'. lia. }
    destruct (IH fx1 R1 M (i + 1) ltac:(clear -Hn; lia) ltac:(clear -Hi Hi'; lia) HV') as (fx2 & R2 & z & MS2 & SP & Hz2).
    + unfold PNSDD.stW, PNSDD.RB. split; [repeat apply conj; PMK.sc|]. split; [exists w; split; [PMK.sc| split; [exact Hw| exact Ew]]| PMK.sc].
    + PMK.sc. + PMK.sc. + PMK.sc. + exact DG. + exact MIM.
    + exists fx2, R2, z. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP| clear -Hz2 Hi; lia].
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
    exists fx1, R1, (i + 1). split; [exact MS1|].
    split; [| clear -Hi; lia]. unfold PNSDD.stP. split.
    { unfold PNSDD.stW, PNSDD.RB. split; [repeat apply conj; PMK.sc|]. split; [exists w; split; [PMK.sc| split; [exact Hw| exact Ew]]| PMK.sc]. }
    repeat apply conj; PMK.sc.
Qed.

(* [comment removed for export] *)
Lemma scan (FVp : 0 < V) fx R M :
  PNSDD.stW R0 S first sigma e R -> RR R (-1) -> digs M 0 -> MI M ->
  exists fx' R' z, msteps RSEGS (st fx R 0x38c94 M) (st fx' R' 0x38cec M) /\ PNSDD.stP R0 S first sigma e z (36 - z) (PNDF.dg V z) R' /\ 1 <= z <= 35.
Proof.
  intros SW RRm DG MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof SW as ((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & (w & G10 & Hw & Ew) & G11).
  destruct RRm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G15 & G16 & _).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (C0 : L5.u32_at RSEGS M (S - 216) 0).
  { pose proof (DG 0 ltac:(clear; lia)) as C. unfold PNSDD.cell in C. rewrite dg0 in C. replace (S - 216 + 4 * 0) with (S - 216) in C by (clear; lia). exact C. }
  (let T := type of (PNSDAP.dkZ1_conc fx R M (fun j => match j with 51%nat => 0 | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkZ1_conc fx R M (fun j => match j with 51%nat => 0 | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A12 & A14 & A15 & Hz) | (MS1 & KS1 & A12 & A13 & A14 & Hnz) ]).
  2:{ exfalso. clear -Hnz. change ((0 - 0) mod 2 ^ 64) with 0 in Hnz. lia. }
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  pose proof V_lt35 as HV.
  destruct (scan_loop FVp 35%nat fx1 R1 M 0 eq_refl ltac:(clear; lia) ltac:(replace (35 - 0) with 35 by (clear; lia); exact HV)) as (fx2 & R2 & z & MS2 & SP & Hz2).
  - unfold PNSDD.stW, PNSDD.RB. split; [repeat apply conj; PMK.sc|]. split; [exists w; split; [PMK.sc| split; [exact Hw| exact Ew]]| PMK.sc].
  - PMK.sc. - PMK.sc. - PMK.sc. - exact DG. - exact MIM.
  - exists fx2, R2, z. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP| clear -Hz2; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma to_bv_eqm a b : a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact E. Qed.
Lemma land_le_r a m : 0 <= a -> 0 <= m -> Z.land a m <= m.
Proof. intros Ha Hm. rewrite Z.land_comm. apply PNSDAP.land_le_l; assumption. Qed.

Lemma land_rng w : 0 <= w -> 0 <= Z.land w 16383 <= 16383.
Proof. intros Hw. split; [apply Z.land_nonneg; right; lia| apply land_le_r; lia]. Qed.
Lemma w_rng hi q : 0 <= hi < 2 ^ 64 -> 32768 <= q -> 0 <= hi / 2 ^ 32 / q < 2 ^ 17.
Proof. intros H Hq. rewrite Z.div_div by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. Qed.

Lemma tail332 (FVp : 0 < V) fx R M w c3 c2 c1 c0 :
  PNSDD.stNH R0 S first sigma R -> getr R (reg 10) = Z_to_bv 64 w -> 0 <= w < 2 ^ 17 -> Z.land w 16383 = e ->
  L5.u32_at RSEGS M (S - 232) c3 -> L5.u32_at RSEGS M (S - 228) c2 -> L5.u32_at RSEGS M (S - 224) c1 -> L5.u32_at RSEGS M (S - 220) c0 ->
  V = c3 mod 2 ^ 32 * 2 ^ 96 + c2 mod 2 ^ 32 * 2 ^ 64 + c1 mod 2 ^ 32 * 2 ^ 32 + c0 mod 2 ^ 32 -> MI M -> zers M 4 ->
  outP R0 S first sigma r fx R 0x38bc4 M.
Proof using Fr FS F16 Ffirst Fdj Fe Fsig FV.
  intros SN G10 Hw Ew C3 C2 C1 C0 HV MIM ZR.
  pose proof (entry R M c3 c2 c1 c0 SN C3 C2 C1 C0 MIM ZR HV) as HD3.
  destruct (rounds fx R M HD3) as (fx1 & R1 & M1 & MG1 & FZ1 & MI1 & MS1 & RB1 & RR1 & B10 & B11 & DG1).
  assert (SW : PNSDD.stW R0 S first sigma e R1).
  { split; [exact RB1|]. split; [exists w; split; [rewrite B10; exact G10| split; [exact Hw| exact Ew]]|].
    rewrite B11. destruct SN as (_ & _ & _ & _ & G11 & _). exact G11. }
  destruct (scan FVp fx1 R1 M1 SW RR1 DG1 MI1) as (fx2 & R2 & z & MS2 & SP & Hz).
  unfold outP. exists fx2, R2, M1. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MI1|].
  exists e, z, (36 - z), (PNDF.dg V z). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP|].
  split; [clear -Fe; lia|]. split; [clear -Hz; lia|]. split; [clear -Hz; lia|]. split; [clear -Hz; lia|]. split; [apply PNDF.dg_range|].
  intros i Hi. exists (PNDF.dg V i). split; [apply DG1; clear -Hi Hz; lia| apply PNDF.dg_range].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zero568 fx R M w :
  PNSDD.RB R0 S first sigma R -> getr R (reg 10) = Z_to_bv 64 w -> 0 <= w < 2 ^ 17 -> getr R (reg 11) = Z_to_bv 64 16383 -> MI M ->
  outP R0 S first sigma r fx R 0x38cb0 M.
Proof using Fr FS F16 Ffirst Fdj Fsig.
  intros (G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) G10 Hw G11 MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDAP.dkZ0_conc fx R M (PNSDRN2.VV R0 S first sigma 0 r 0)) in let T := eval cbn beta iota delta [PNSDRN2.VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkZ0_conc fx R M (PNSDRN2.VV R0 S first sigma 0 r 0)) T ltac:(cbn beta iota delta [PNSDRN2.VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FZ1 & MS1 & KS1 & A12 & A13 & A14 & C0)); PMK.pvz_clrT.
  unfold outP. exists fx1, R1, M1. split; [exact MG1|].
  split. { intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
  split. { apply (MI_xfer M M1 MIM MG1). intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
  exists (Z.land w 16383), 0, 1, 0. split; [exact MS1|].
  split.
  { unfold PNSDD.stP, PNSDD.stW, PNSDD.RB.
    split; [split; [repeat apply conj; PMK.sc| split; [exists w; split; [PMK.sc| split; [exact Hw| reflexivity]]| PMK.sc]]|].
    repeat apply conj; PMK.sc. }
  split; [apply land_rng; clear -Hw; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
  intros i Hi. exists 0. replace i with 0 by (clear -Hi; lia). split; [| clear; lia].
  unfold PNSDD.cell. replace (S - 216 + 4 * 0) with (S - 216) by (clear; lia). exact C0.
Qed.

End Call.

Lemma outP_pre (R0 : bvmap 5 word) (S first sigma r : Z) fx R (pc : Z) M fx1 R1 (pc1 : Z) M1 :
  msteps RSEGS (st fx R pc M) (st fx1 R1 pc1 M1) -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 256 <= a < S - 72) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  outP R0 S first sigma r fx1 R1 pc1 M1 -> outP R0 S first sigma r fx R pc M.
Proof.
  intros MS MG FZ (fx2 & R2 & M2 & MG2 & FZ2 & MI2 & e' & z & sd & d & MS2 & SP).
  unfold outP. exists fx2, R2, M2. split; [intros a Ha; apply MG2; apply MG; exact Ha|].
  split; [intros a Ha Hn; rewrite (FZ2 a Ha Hn); exact (FZ a Ha Hn)|]. split; [exact MI2|].
  exists e', z, sd, d. split; [eapply msteps_trans; [exact MS| exact MS2]| exact SP].
Qed.

Lemma cN_rng hi : 0 <= hi < 2 ^ 64 -> 2 ^ 17 <= PNSDD.cN232 hi < 2 ^ 18.
Proof.
  intros Fh. pose proof (PNSDD.msb_range hi ltac:(lia)) as Hm. unfold PNSDD.msb in Hm. unfold PNSDD.cN232.
  match type of Hm with 0 <= ?X <= 1 => set (m := X) in * end.
  assert (HL : 0 <= Z.land (hi / 2 ^ 32) 16383 <= 16383) by (apply land_rng; apply Z.div_pos; lia).
  rewrite (Z.mod_small (_ * m)) by lia. rewrite (Z.mod_small (_ * m + _)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma t332 (R0 : bvmap 5 word) (S first sigma r hi lo c3 w : Z)
  (Fr : 0 <= r < 2 ^ 47) (FS : 140735332483312 <= S <= 140737488355328) (F16 : S mod 16 = 0)
  (Ffirst : 4096 <= first <= 140737488355286) (Fdj : S - 18432 + 18432 <= first \/ first + 42 <= S - 18432)
  (Fsig : 0 <= sigma <= 1) (Fhi : 0 <= hi < 2 ^ 64) (Flo : 0 <= lo < 2 ^ 64) (F3 : 0 <= c3 < 2 ^ 18) (Fw : 0 <= w < 2 ^ 17) fx R M :
  PNSDD.stNH R0 S first sigma R -> getr R (reg 10) = Z_to_bv 64 w ->
  L5.u32_at RSEGS M (S - 232) c3 -> L5.u32_at RSEGS M (S - 228) hi -> L5.u32_at RSEGS M (S - 224) (lo / 2 ^ 32) -> L5.u32_at RSEGS M (S - 220) lo ->
  (c3 <> 0 \/ hi mod 2 ^ 32 <> 0 \/ lo / 2 ^ 32 <> 0 \/ lo mod 2 ^ 32 <> 0) ->
  PNSDD.MI R0 S first r M -> PNSDD.zers S M 4 -> outP R0 S first sigma r fx R 0x38bc4 M.
Proof.
  intros SN G10 C3 C2 C1 C0 NZ MIM ZR.
  assert (QL : 0 <= lo / 2 ^ 32 < 2 ^ 32).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 32 * 2 ^ 32) with (2 ^ 64); lia. }
  pose proof (Z.mod_pos_bound hi (2 ^ 32) ltac:(lia)) as B2. pose proof (Z.mod_pos_bound lo (2 ^ 32) ltac:(lia)) as B0.
  assert (E3 : c3 mod 2 ^ 32 = c3) by (apply Z.mod_small; lia).
  assert (E1 : (lo / 2 ^ 32) mod 2 ^ 32 = lo / 2 ^ 32) by (apply Z.mod_small; lia).
  assert (FV' : 0 <= c3 mod 2 ^ 32 * 2 ^ 96 + hi mod 2 ^ 32 * 2 ^ 64 + (lo / 2 ^ 32) mod 2 ^ 32 * 2 ^ 32 + lo mod 2 ^ 32 < 2 ^ 114)
    by (rewrite E3, E1; lia).
  assert (FVp' : 0 < c3 mod 2 ^ 32 * 2 ^ 96 + hi mod 2 ^ 32 * 2 ^ 64 + (lo / 2 ^ 32) mod 2 ^ 32 * 2 ^ 32 + lo mod 2 ^ 32)
    by (rewrite E3, E1; destruct NZ as [N|[N|[N|N]]]; lia).
  exact (tail332 R0 S first sigma (Z.land w 16383)
           (c3 mod 2 ^ 32 * 2 ^ 96 + hi mod 2 ^ 32 * 2 ^ 64 + (lo / 2 ^ 32) mod 2 ^ 32 * 2 ^ 32 + lo mod 2 ^ 32) r
           Fr FS F16 Ffirst Fdj (land_rng _ (proj1 Fw)) Fsig FV' FVp' fx R M w c3 hi (lo / 2 ^ 32) lo
           SN G10 Fw eq_refl C3 C2 C1 C0 eq_refl MIM ZR).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem middle (R0 : bvmap 5 word) (S first sigma r vp hi lo : Z)
  (Fr : 0 <= r < 2 ^ 47) (FS : 140735332483312 <= S <= 140737488355328) (F16 : S mod 16 = 0)
  (Ffirst : 4096 <= first <= 140737488355286) (Fdj : S - 18432 + 18432 <= first \/ first + 42 <= S - 18432)
  (Fsig : 0 <= sigma <= 1) (Fvp : 4096 <= vp <= 140737488355312) (Fvp8 : vp mod 8 = 0)
  (Fvpdj : S - 240 + 240 <= vp \/ vp + 16 <= S - 240) (Fvpf : first + 42 <= vp \/ vp + 16 <= first)
  (Fhi : 0 <= hi < 2 ^ 64) (Flo : 0 <= lo < 2 ^ 64) fx R M :
  PNSDD.stJ R0 S first sigma vp R -> PNSDD.MI R0 S first r M -> PNSDD.zers S M 4 -> PNSDD.vp_at M vp lo hi ->
  (exists fx' R' M', mem_grows M M' /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 232 <= a < S - 216) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
     /\ PNSDD.MI R0 S first r M' /\ msteps RSEGS (st fx R 0x38afc M) (st fx' R' 0x39080 M') /\ PNSDD.stX R0 S first sigma vp hi lo R'
     /\ Z.land (hi / 2 ^ 32) 1610612736 = 1610612736)
  \/ outP R0 S first sigma r fx R 0x38afc M.
Proof.
  intros ((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & G19) MIM ZR (VP0 & VP8).
  pose proof (PNSDRN.ufacts R0 S) as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  destruct (PNDBV.hi_fields hi Fhi) as (a & b & c & d & E & Ha & Hb & Hc & Hd).
  pose proof (w_rng hi 131072 Fhi ltac:(clear; lia)) as Hw.
  assert (P3 : 0 <= PNDBV.parts0 hi < 2 ^ 18).
  { unfold PNDBV.parts0. rewrite (PNDBV.f_parts0 hi a b c d E Ha Hb Hc Hd). clear -Hb Hc; lia. }
  (let T := type of (PNSDAP.dkB_conc fx R M (fun j => match j with 35%nat => vp | 36%nat => lo | 37%nat => hi | _ => PNSDRN2.VV R0 S first sigma 0 r 3 j end)) in let T := eval cbn beta iota delta [PNSDRN2.VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkB_conc fx R M (fun j => match j with 35%nat => vp | 36%nat => lo | 37%nat => hi | _ => PNSDRN2.VV R0 S first sigma 0 r 3 j end)) T ltac:(cbn beta iota delta [PNSDRN2.VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & PS).
  assert (FZ1' : forall a0, 0 <= a0 < 2 ^ 64 -> ~ (S - 256 <= a0 < S - 72) -> M1 (Z_to_bv 64 a0) = M (Z_to_bv 64 a0)).
  { intros a0 Ha0 Hn. apply (FZ1 a0 Ha0). clear -Hn; lia. }
  pose proof (PNSDD.MI_xfer R0 S first r FS M M1 MIM MG1 FZ1') as MI1.
  assert (ZR1 : PNSDD.zers S M1 4).
  { intros i Hi. apply (PNSDD.cell_xfer S FS M M1 _ i 0 FZ1); [intros a0 Ha0; clear -Ha0 Hi; lia| clear -Hi; lia| exact (ZR i Hi)]. }
  destruct PS as [ X0 | [ X1 | [ X2 | [ X3 | [ X4 | [ X5 | X6 ]]]]]].
  - destruct X0 as (MS1 & KS1 & A10 & A11 & A12 & A13 & A15 & Hsp).
    left. exists fx1, R1, M1. split; [exact MG1|]. split; [intros a0 Ha0 Hn; apply (FZ1 a0 Ha0); clear -Hn; lia|].
    split; [exact MI1|]. split; [exact MS1|].
    split. { unfold PNSDD.stX, PNSDD.RB. change (2 ^ 32) with 4294967296. repeat apply conj; PMK.sc. }
    pose proof (land_le_r (hi / 4294967296) 1610612736 ltac:(apply Z.div_pos; clear -Fhi; lia) ltac:(clear; lia)) as LE.
    assert (NN' : 0 <= Z.land (hi / 4294967296) 1610612736) by (apply Z.land_nonneg; right; clear; lia).
    change (2 ^ 32) with 4294967296.
    destruct (Z.eq_dec (Z.land (hi / 4294967296) 1610612736) 1610612736) as [EQ|NE]; [exact EQ| exfalso].
    replace ((Z.land (hi / 4294967296) 1610612736 - 1610612736) mod 2 ^ 64) with (Z.land (hi / 4294967296) 1610612736 - 1610612736 + 2 ^ 64) in Hsp.
    { clear -Hsp LE NE NN'; lia. }
    apply (Z.mod_unique_pos _ _ (-1)); clear -LE NE NN'; lia.
  - destruct X1 as (MS1 & KS1 & _ & A10 & A11 & _).
    right. apply (outP_pre R0 S first sigma r fx R 0x38afc M fx1 R1 0x38cb0 M1 MS1 MG1 FZ1').
    apply (zero568 R0 S first sigma r Fr FS F16 Ffirst Fdj Fsig fx1 R1 M1 (hi / 2 ^ 32 / 131072)); [| exact A10| exact Hw| exact A11| exact MI1].
    unfold PNSDD.RB. repeat apply conj; PMK.sc.
  - cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in X2.
    destruct X2 as (MS1 & KS1 & A5 & A6 & A7 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A19 & A28 & A29 & A30 & Hlo & _ & _ & C220 & C224 & C228 & C232 & _).
    rewrite PNDBV.bv_sub_0, PNDBV.ltu1, PNDBV.sextw_zero, (PNDBV.u_lit lo Flo), PNDBV.bvu_if in Hlo.
    assert (NZ : lo mod 2 ^ 32 <> 0).
    { intros L0. rewrite L0 in Hlo. change (0 <= 1 <= 0) in Hlo. clear -Hlo; lia. }
    right. apply (outP_pre R0 S first sigma r fx R 0x38afc M fx1 R1 0x38bc4 M1 MS1 MG1 FZ1').
    apply (t332 R0 S first sigma r hi lo (PNDBV.parts0 hi) (hi / 2 ^ 32 / 131072) Fr FS F16 Ffirst Fdj Fsig Fhi Flo P3 Hw fx1 R1 M1);
      [| exact A10| exact C232| exact C228| exact C224| exact C220| right; right; right; exact NZ| exact MI1| exact ZR1].
    unfold PNSDD.stNH, PNSDD.RB. repeat apply conj; PMK.sc.
  - destruct X3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & _).
    exfalso. rewrite (PNDBV.f_msb hi a b c d E Ha Hb Hc Hd) in Hx. clear -Hx Hb; lia.
  - cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in X4.
    destruct X4 as (MS1 & KS1 & A5 & A6 & A7 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A19 & A28 & A29 & A30 & _ & Hq & _ & C220 & C224 & C228 & C232 & _).
    assert (NZ : lo / 2 ^ 32 <> 0).
    { intros L0. change (2 ^ 32) with 4294967296 in L0. rewrite L0, Z.sub_0_r, Z.mod_0_l in Hq by (clear; lia). clear -Hq; lia. }
    right. apply (outP_pre R0 S first sigma r fx R 0x38afc M fx1 R1 0x38bc4 M1 MS1 MG1 FZ1').
    apply (t332 R0 S first sigma r hi lo (PNDBV.parts0 hi) (hi / 2 ^ 32 / 131072) Fr FS F16 Ffirst Fdj Fsig Fhi Flo P3 Hw fx1 R1 M1);
      [| exact A10| exact C232| exact C228| exact C224| exact C220| right; right; left; exact NZ| exact MI1| exact ZR1].
    unfold PNSDD.stNH, PNSDD.RB. repeat apply conj; PMK.sc.
  - destruct X5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & _).
    exfalso. rewrite (PNDBV.f_msb hi a b c d E Ha Hb Hc Hd) in Hx. clear -Hx Hb; lia.
  - cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in X6.
    destruct X6 as (MS1 & KS1 & A5 & A6 & A7 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A19 & A28 & A29 & A30 & _ & Hor & C220 & C224 & C228 & C232 & _).
    rewrite PNDBV.bv_sub_0, PNDBV.ltu1, PNDBV.sextw_zero, bv_or_unsigned, (PNDBV.parts0_bv hi lo Fhi Flo), (PNDBV.u_lit hi Fhi), PNDBV.bvu_if in Hor.
    assert (NZ : PNDBV.parts0 hi <> 0 \/ hi mod 2 ^ 32 <> 0).
    { destruct (Z.eq_dec (PNDBV.parts0 hi) 0) as [Z3|Z3]; [right| left; exact Z3]. intros Z2.
      rewrite (PNDBV.mod32_lor (PNDBV.parts0 hi) hi), Z3, Z2 in Hor by (clear -P3 Fhi; lia). change (0 <= 1 <= 0) in Hor. clear -Hor; lia. }
    right. apply (outP_pre R0 S first sigma r fx R 0x38afc M fx1 R1 0x38bc4 M1 MS1 MG1 FZ1').
    apply (t332 R0 S first sigma r hi lo (PNDBV.parts0 hi) (hi / 2 ^ 32 / 131072) Fr FS F16 Ffirst Fdj Fsig Fhi Flo P3 Hw fx1 R1 M1);
      [| exact A10| exact C232| exact C228| exact C224| exact C220| destruct NZ as [N|N]; [left| right; left]; exact N| exact MI1| exact ZR1].
    unfold PNSDD.stNH, PNSDD.RB. repeat apply conj; PMK.sc.
Qed.

Theorem from_nz (R0 : bvmap 5 word) (S first sigma r vp hi lo : Z)
  (Fr : 0 <= r < 2 ^ 47) (FS : 140735332483312 <= S <= 140737488355328) (F16 : S mod 16 = 0)
  (Ffirst : 4096 <= first <= 140737488355286) (Fdj : S - 18432 + 18432 <= first \/ first + 42 <= S - 18432)
  (Fsig : 0 <= sigma <= 1) (Fhi : 0 <= hi < 2 ^ 64) (Flo : 0 <= lo < 2 ^ 64) fx R M :
  PNSDD.stNZ R0 S first sigma vp hi lo R -> PNSDD.MI R0 S first r M ->
  outP R0 S first sigma r fx R 0x38cb0 M.
Proof.
  intros (RBR & _ & G10 & G11 & _) MIM.
  exact (zero568 R0 S first sigma r Fr FS F16 Ffirst Fdj Fsig fx R M (hi / 2 ^ 32 / 32768) RBR G10 (w_rng hi 32768 Fhi ltac:(clear; lia)) G11 MIM).
Qed.

Theorem from_nh (R0 : bvmap 5 word) (S first sigma r hi lo : Z)
  (Fr : 0 <= r < 2 ^ 47) (FS : 140735332483312 <= S <= 140737488355328) (F16 : S mod 16 = 0)
  (Ffirst : 4096 <= first <= 140737488355286) (Fdj : S - 18432 + 18432 <= first \/ first + 42 <= S - 18432)
  (Fsig : 0 <= sigma <= 1) (Fhi : 0 <= hi < 2 ^ 64) (Flo : 0 <= lo < 2 ^ 64) fx R M :
  PNSDD.stNH R0 S first sigma R -> getr R (reg 10) = Z_to_bv 64 (hi / 2 ^ 32 / 32768) ->
  PNSDD.cN S hi lo M -> PNSDD.MI R0 S first r M -> PNSDD.zers S M 4 ->
  outP R0 S first sigma r fx R 0x38bc4 M.
Proof.
  intros SN G10 (C220 & C224 & C228 & C232) MIM ZR.
  pose proof (cN_rng hi Fhi) as H3.
  exact (t332 R0 S first sigma r hi lo (PNSDD.cN232 hi) (hi / 2 ^ 32 / 32768) Fr FS F16 Ffirst Fdj Fsig Fhi Flo ltac:(clear -H3; lia)
           (w_rng hi 32768 Fhi ltac:(clear; lia)) fx R M
           SN G10 C232 C228 C224 C220 ltac:(left; clear -H3; lia) MIM ZR).
Qed.

End PNSDMID.
