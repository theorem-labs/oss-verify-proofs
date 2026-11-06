(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare AxSymExec3 L5Defs L5Kn L5KnA L5Core L5CoreKit L5DefsA L5StepAR PmModelFacts
     PnDecFacts PnDecBv PnMemW PnSDec128Rnd2 PnADec128Defs PnADec128Bv PnADec128P2 PnADec128P6 PnADec128Rnd PnADec128Rnd2 PnADec128Rnd3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADMID.
Import PNADRN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma to_bv_eqm a b : a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact E. Qed.

Section Call.
Variables (R0 : bvmap 5 word) (S F first sigma E1 : Z).
Hypothesis FS : 140735332487296 <= S <= 140737488355328.
Hypothesis F32 : S mod 32 = 0.
Hypothesis FF1 : 4096 <= F <= 140737488354816.
Hypothesis FF32 : F mod 32 = 0.
Hypothesis FFSH : 2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784.
Hypothesis FFS : S - 128 + 128 <= F \/ F + 512 <= S - 128.
Hypothesis FFI : 65536 + 6832128 <= F \/ F + 512 <= 65536.
Hypothesis Ffirst : 4096 <= first <= 140737488355280.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis FE1 : 0 <= E1 < 2 ^ 64.
Variable V : Z.
Hypothesis FV : 0 <= V < 2 ^ 113.
Abbreviation RR := (RRa R0 S F first sigma E1).
Abbreviation cell := (PNADD.cell F).
Abbreviation digs := (PNADD.digs F V).
Abbreviation zers := (PNADD.zers F).
Abbreviation HD := (PNADRN3.HD R0 S F first sigma E1 V).
Abbreviation Wrnd := (PNADRN3.Wrnd S F).
Abbreviation bvu_small := PNSDRN2.bvu_small.
Definition VV (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 38%nat => first + sigma | 50%nat => F | 59%nat => E1 | _ => 0 end.
Local Ltac fsc := first [ assumption | (hnf; assumption) | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end | lia ].
Local Ltac lem T L := pose proof L as T; L5SAR.feed T ltac:(assumption).
Local Ltac keep1 KSa := first [ assumption | (rewrite KSa by inl; assumption) ].
Local Ltac keep2 KSa KSb := first [ assumption | (rewrite KSa by inl; first [ assumption | (rewrite KSb by inl; assumption) ]) ].

Lemma RBO_of_RR R k : RR R k -> PNADD.RBO R0 S F first sigma R.
Proof.
  intros (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27).
  unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rounds fx R M : HD R M 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wrnd a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ L5.writable RSEGS M' (S - 128) 128 /\ L5.writable RSEGS M' F 512
    /\ msteps RSEGS (st fx R 0xb2a14 M) (st fx' R' 0xb2af8 M') /\ RR R' (-1) /\ digs M' 0.
Proof.
  intros HD3. lem RS (PNADRN3.round_step R0 S F first sigma E1). specialize (RS V FV).
  destruct (RS fx R M 3 ltac:(clear; lia) HD3) as (fx1 & R1 & M1 & MG1 & FZ1 & _ & _ & [(K & _) | (_ & MS1 & HD2)]); [exfalso; clear -K; lia|].
  destruct (RS fx1 R1 M1 (3 - 1) ltac:(clear; lia) HD2) as (fx2 & R2 & M2 & MG2 & FZ2 & _ & _ & [(K & _) | (_ & MS2 & HD1)]); [exfalso; clear -K; lia|].
  destruct (RS fx2 R2 M2 (3 - 1 - 1) ltac:(clear; lia) HD1) as (fx3 & R3 & M3 & MG3 & FZ3 & _ & _ & [(K & _) | (_ & MS3 & HD0)]); [exfalso; clear -K; lia|].
  destruct (RS fx3 R3 M3 (3 - 1 - 1 - 1) ltac:(clear; lia) HD0) as (fx4 & R4 & M4 & MG4 & FZ4 & WR4 & WF4 & [(_ & MS4 & RB4 & DG4) | (K & _)]); [| exfalso; clear -K; lia].
  exists fx4, R4, M4. split; [intros a Ha; apply MG4; apply MG3; apply MG2; apply MG1; exact Ha|].
  split. { intros a Ha Hn. rewrite (FZ4 a Ha Hn), (FZ3 a Ha Hn), (FZ2 a Ha Hn). exact (FZ1 a Ha Hn). }
  split; [exact WR4|]. split; [exact WF4|].
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]|].
  split; [exact RB4| exact DG4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma V_lt35 : V < 10 ^ 35.
Proof. clear -FV. assert (2 ^ 113 < 10 ^ 35) by (vm_compute; reflexivity). lia. Qed.
Lemma dg0 : PNDF.dg V 0 = 0.
Proof. unfold PNDF.dg. replace (35 - 0) with 35 by (clear; lia). rewrite Z.div_small; [reflexivity|]. pose proof V_lt35. clear -H FV; lia. Qed.
(* [comment removed for export] *)
Lemma sh_cell i : 0 <= i <= 35 -> exists j, (F + 32 + 4 * i) / 8 = F / 8 + j /\ 4 <= j <= 21.
Proof.
  intros Hi. exists ((32 + 4 * i) / 8).
  assert (F8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(clear; lia)) as E. rewrite FF32, Z.add_0_r in E. rewrite E. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia). apply Z.mod_mul. clear; lia. }
  pose proof (Z.div_mod F 8 ltac:(clear; lia)) as E8. rewrite F8, Z.add_0_r in E8.
  split.
  - replace (F + 32 + 4 * i) with (F / 8 * 8 + (32 + 4 * i)) by (clear -E8; lia). apply Z.div_add_l. clear; lia.
  - split; [apply Z.div_le_lower_bound; clear -Hi; lia| apply Z.lt_succ_r; apply Z.div_lt_upper_bound; clear -Hi; lia].
Qed.

Abbreviation e14 := (Z.land E1 16383).
Lemma e14_range : 0 <= e14 <= 16383.
Proof. rewrite PNDBV.land_ones14. pose proof (Z.mod_pos_bound E1 (2 ^ 14) ltac:(clear; lia)) as B. clear -B; lia. Qed.

Lemma scan_loop (FVp : 0 < V) (n : nat) : forall fx R M i,
  35 - i = Z.of_nat n -> 0 <= i <= 34 -> V < 10 ^ (35 - i) ->
  PNADD.RBO R0 S F first sigma R -> getr R (reg 11) = Z_to_bv 64 E1 -> getr R (reg 12) = Z_to_bv 64 16383 ->
  getr R (reg 10) = Z_to_bv 64 (F + 36 + 4 * i) -> getr R (reg 23) = Z_to_bv 64 (F + 32 + 4 * i) -> getr R (reg 25) = Z_to_bv 64 (36 - i) ->
  digs M 0 -> L5.writable RSEGS M (S - 128) 128 -> L5KA.zeros_at M (PNADD.SH F + 4) 18 ->
  exists fx' R' z, msteps RSEGS (st fx R 0xb2d34 M) (st fx' R' 0xb2b04 M) /\ PNADD.stP R0 S F first sigma e14 z (36 - z) R' /\ i < z <= 35.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi HV RBR G11 G12 G10 G23 G25 DG WR ZSH.
  { exfalso. clear -Hn Hi. lia. }
  pose proof RBR as ((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G26 & G27) & G20 & G22 & G21).
  unfold PNADD.SH, PNADD.SBv in G18, G27, ZSH.
  pose proof (PNDF.dg_range V (i + 1)) as Hd.
  assert (C : L5.u32_at RSEGS M (F + 36 + 4 * i) (PNDF.dg V (i + 1))).
  { pose proof (DG (i + 1) ltac:(clear -Hi; lia)) as C. unfold PNADD.cell in C. replace (F + 36 + 4 * i) with (F + 32 + 4 * (i + 1)) by (clear; lia). exact C. }
  assert (ZS : L5KA.zeros_at M ((F + 36 + 4 * i) / 8 + 2147450880) 1).
  { destruct (sh_cell (i + 1) ltac:(clear -Hi; lia)) as (j & Ej & Hj). replace (F + 36 + 4 * i) with (F + 32 + 4 * (i + 1)) by (clear; lia). rewrite Ej.
    apply (L5KA.zeros_at_sub M _ _ _ _ ZSH); clear -Hj; lia. }
  assert (AL : (F + 36 + 4 * i) mod 4 = 0).
  { pose proof (Z.div_mod F 32 ltac:(clear; lia)) as E. rewrite FF32, Z.add_0_r in E. rewrite E. replace (32 * (F / 32) + 36 + 4 * i) with ((8 * (F / 32) + 9 + i) * 4) by (clear; lia). apply Z.mod_mul. clear; lia. }
  (let T := type of (PNADP2.adkSC_conc fx R M (fun j => match j with 52%nat => F + 36 + 4 * i | 53%nat => PNDF.dg V (i + 1) | 54%nat => 36 - i | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkSC_conc fx R M (fun j => match j with 52%nat => F + 36 + 4 * i | 53%nat => PNDF.dg V (i + 1) | 54%nat => 36 - i | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [ (MS1 & KS1 & A10 & A13 & A23 & A25 & Hz) | (MS1 & KS1 & A10 & A13 & A23 & A25 & Hnz) ]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1.
  - rewrite Z.sub_0_r, Z.mod_small in Hz by (clear -Hd; lia).
    assert (D0 : PNDF.dg V (i + 1) = 0) by (clear -Hz Hd; lia).
    pose proof (PNDF.dg_zero_step V (i + 1) ltac:(clear -FV; lia) ltac:(clear -Hi; lia) ltac:(replace (35 - (i + 1) + 1) with (35 - i) by (clear; lia); exact HV) D0) as HV'.
    assert (Hi' : i + 1 <= 34).
    { destruct (Z_lt_le_dec 34 (i + 1)) as [LT|LE]; [| exact LE]. exfalso.
      replace (35 - (i + 1)) with 0 in HV' by (clear -LT Hi; lia). clear -HV' FVp. cbn in HV'. lia. }
    destruct (IH fx1 R1 M (i + 1) ltac:(clear -Hn; lia) ltac:(clear -Hi Hi'; lia) HV') as (fx2 & R2 & z & MS2 & SP & Hz2).
    + unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS1.
    + keep1 KS1.
    + keep1 KS1.
    + rewrite A10. f_equal. clear; lia.
    + rewrite A23. f_equal. clear; lia.
    + rewrite A25. f_equal. clear; lia.
    + exact DG.
    + exact WR.
    + unfold PNADD.SH, PNADD.SBv. exact ZSH.
    + exists fx2, R2, z. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP| clear -Hz2 Hi; lia].
  - exists fx1, R1, (i + 1). split; [exact MS1|].
    split; [| clear -Hi; lia]. unfold PNADD.stP.
    split. { unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS1. }
    split; [rewrite A23; f_equal; clear; lia|]. split; [rewrite A25; f_equal; clear; lia|].
    split; [rewrite (KS1 11%nat) by inl; rewrite G11, (bvu_small E1 FE1); reflexivity|]. keep1 KS1.
Qed.

(* [comment removed for export] *)
Lemma scan (FVp : 0 < V) fx R M :
  RR R (-1) -> digs M 0 -> L5.writable RSEGS M (S - 128) 128 -> L5KA.zeros_at M (PNADD.SH F + 4) 18 ->
  exists fx' R' z, msteps RSEGS (st fx R 0xb2af8 M) (st fx' R' 0xb2b04 M) /\ PNADD.stP R0 S F first sigma e14 z (36 - z) R' /\ 1 <= z <= 35.
Proof.
  intros RRk DG WR ZSH.
  pose proof (RBO_of_RR R _ RRk) as RBR.
  pose proof RRk as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27).
  assert (C0 : L5.u32_at RSEGS M (F + 32) 0).
  { pose proof (DG 0 ltac:(clear; lia)) as C. unfold PNADD.cell in C. rewrite dg0 in C. replace (F + 32 + 4 * 0) with (F + 32) in C by (clear; lia). exact C. }
  (let T := type of (PNADP2.adkZ1_conc fx R M (fun j => match j with 55%nat => 0 | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkZ1_conc fx R M (fun j => match j with 55%nat => 0 | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [ (MS1 & KS1 & A10 & A25 & Hnz) | (MS1 & KS1 & A10 & A25 & Hz) ]).
  { exfalso. clear -Hnz. rewrite Z.sub_0_r, Z.mod_small in Hnz by lia. lia. }
  assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1.
  pose proof V_lt35 as HV.
  destruct (scan_loop FVp 35%nat fx1 R1 M 0 eq_refl ltac:(clear; lia) ltac:(replace (35 - 0) with 35 by (clear; lia); exact HV)) as (fx2 & R2 & z & MS2 & SP & Hz2).
  - destruct RBR as ((I2 & I3 & I4 & I8 & I9 & I18 & I19 & I26 & I27) & I20 & I22 & I21).
    unfold PNADD.RBO, PNADD.RBA. repeat split; keep1 KS1.
  - keep1 KS1.
  - keep1 KS1.
  - rewrite A10. f_equal. clear; lia.
  - rewrite (KS1 23%nat) by inl. rewrite G23. f_equal. clear; lia.
  - rewrite A25. f_equal.
  - exact DG.
  - exact WR.
  - exact ZSH.
  - exists fx2, R2, z. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP| clear -Hz2; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iszero fx R M e :
  PNADD.stZ R0 S F first sigma e R -> getr R (reg 11) = Z_to_bv 64 E1 -> L5.writable RSEGS M (S - 128) 128 -> L5.writable RSEGS M F 512 ->
  exists fx' R' M', msteps RSEGS (st fx R 0xb2aec M) (st fx' R' 0xb2b04 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 36) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ PNADD.stP R0 S F first sigma e 0 1 R' /\ cell M' 0 0.
Proof.
  intros (((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G26 & G27) & G20 & G22 & G21) & G23 & A11 & G12) G11 WR WF.
  unfold PNADD.SH, PNADD.SBv in G18, G27.
  (let T := type of (PNADP2.adkZ0_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkZ0_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A25 & C0).
  exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
  split. { intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
  split. { unfold PNADD.stP. split. { unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS1. }
           split; [rewrite (KS1 23%nat) by inl; rewrite G23; f_equal; clear; lia|]. split; [exact A25|].
           split; [rewrite (KS1 11%nat) by inl; exact A11|]. keep1 KS1. }
  unfold PNADD.cell. replace (F + 32 + 4 * 0) with (F + 32) by (clear; lia). exact C0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Decode.
Variables (vp hi lo : Z).
Hypothesis Fvp : 6897664 <= vp <= 140737488355312.
Hypothesis Fvp8 : vp mod 8 = 0.
Hypothesis FvpSH : 2147446784 + 17592186048512 <= vp \/ vp + 16 <= 2147446784.
Hypothesis FvpS : S - 128 + 128 <= vp \/ vp + 16 <= S - 128.
Hypothesis Fhi : 0 <= hi < 2 ^ 64.
Hypothesis Flo : 0 <= lo < 2 ^ 64.
Hypothesis HV : V = (hi mod 2 ^ 49) * 2 ^ 64 + lo.
Hypothesis HE1 : E1 = hi / 4294967296 / 131072.

Lemma decode fx R M :
  PNADD.stJ R0 S F first sigma vp R -> L5.writable RSEGS M (S - 128) 128 -> L5.writable RSEGS M F 512 -> L5.img_clear M 65536 1269760 ->
  digs M 4 -> zers M 4 -> PNADD.vp_at M vp lo hi ->
  exists fx' R',
    (msteps RSEGS (st fx R 0xb2964 M) (st fx' R' 0xb3100 M) /\ PNADD.stX R0 S F first sigma hi lo R')
    \/ (msteps RSEGS (st fx R 0xb2964 M) (st fx' R' 0xb2aec M) /\ PNADD.stZ R0 S F first sigma e14 R' /\ getr R' (reg 11) = Z_to_bv 64 E1)
    \/ (msteps RSEGS (st fx R 0xb2964 M) (st fx' R' 0xb2a14 M) /\ HD R' M 3 /\ 0 < V).
Proof.
  intros (((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G26 & G27) & G20 & G22 & G21) & G23 & G24 & G10 & G11) WR WF IC DG ZR (VP0 & VP8 & VPZ).
  unfold PNADD.SH, PNADD.SBv in G18, G27, G11, VPZ.
  destruct (PNDBV.hi_fields hi Fhi) as (a & b & c & d & E & Ha & Hb & Hc & Hd).
  pose proof (PNADBV.msb_range hi lo Fhi Flo) as Hm. pose proof (PNADBV.hi32_range hi lo Fhi Flo) as Hh.
  (let T := type of (PNADP2.adkD1_conc fx R M (fun j => match j with 34%nat => vp | 35%nat => lo | 36%nat => hi | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP2.adkD1_conc fx R M (fun j => match j with 34%nat => vp | 35%nat => lo | 36%nat => hi | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [ (MS1 & KS1 & A10 & A11 & A12 & A13 & A14 & A28 & CND) | (MS1 & KS1 & A10 & A11 & A12 & A13 & A28 & CND) ]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1.
  2:{ (* [comment removed for export] *)
    exists fx1, R1. left. split; [exact MS1|].
    unfold PNADD.stX. split. { unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS1. }
    split; [keep1 KS1|]. split; [exact A28|]. split; [exact A10|]. apply to_bv_of_unsigned. rewrite A13. reflexivity. }
  (* [comment removed for export] *)
  assert (B13 : getr R1 (reg 13) = Z_to_bv 64 (PNADBV.hi32 hi)) by (apply to_bv_of_unsigned; rewrite A13; reflexivity).
  assert (B14 : getr R1 (reg 14) = Z_to_bv 64 (PNADBV.msb hi)) by (apply to_bv_of_unsigned; rewrite A14; reflexivity).
  assert (RBO1 : PNADD.RBO R0 S F first sigma R1) by (unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv; repeat split; keep1 KS1).
  assert (B23 : getr R1 (reg 23) = Z_to_bv 64 (F + 32)) by keep1 KS1.
  assert (B24 : getr R1 (reg 24) = Z_to_bv 64 vp) by keep1 KS1.
  clear G2 G3 G4 G8 G9 G18 G19 G26 G27 G20 G22 G21 G23 G24 G10 G11 KS1 A11 A12 A13 A14 CND.
  pose proof RBO1 as ((G2 & G3 & G4 & G8 & G9 & G18 & G19 & G26 & G27) & G20 & G22 & G21).
  unfold PNADD.SH, PNADD.SBv in G18, G27.
  (let T := type of (PNADP6.adkD2_conc fx1 R1 M (fun j => match j with 34%nat => vp | 35%nat => lo | 36%nat => hi | 37%nat => PNADBV.msb hi | 39%nat => PNADBV.hi32 hi | _ => VV j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP6.adkD2_conc fx1 R1 M (fun j => match j with 34%nat => vp | 35%nat => lo | 36%nat => hi | 37%nat => PNADBV.msb hi | 39%nat => PNADBV.hi32 hi | _ => VV j end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  assert (EE1 : PNADBV.hi32 hi / 131072 = E1) by (rewrite HE1; reflexivity).
  rewrite EE1 in P.
  destruct P as (fx2 & R2 & M2 & _ & _ & FZ2 & [ (MS2 & KS2 & A5 & A6 & C10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A29 & A30 & A31 & CA)
     |[ (MS2 & KS2 & A5 & A6 & C10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A29 & A30 & A31 & CB & _)
     | (MS2 & KS2 & _ & A11 & A12 & _) ]]);
    (assert (EM : M2 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ2)); subst M2.
  3:{ (* [comment removed for export] *)
    exists fx2, R2. right. left. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [| exact A11].
    unfold PNADD.stZ. split. { unfold PNADD.RBO, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat split; keep1 KS2. }
    split; [keep1 KS2|]. split; [rewrite A11, (bvu_small E1 FE1); reflexivity| exact A12]. }
  (* [comment removed for export] *)
  1: assert (Vnz : V <> 0) by (pose proof (PNADBV.w_nonzero _ PNADBV.XA CA) as NZ; rewrite (PNADBV.XA_val hi lo Fhi Flo) in NZ by reflexivity; rewrite HV; exact (PNADBV.A_nz hi lo Fhi Flo NZ)).
  2: assert (Vnz : V <> 0) by (pose proof (PNADBV.w_nonzero _ PNADBV.XB CB) as NZ; rewrite (PNADBV.XB_val hi lo Fhi Flo) in NZ by reflexivity; rewrite HV; exact (PNADBV.B_nz hi lo Fhi Flo NZ)).
  all: exists fx2, R2; right; right; (split; [eapply msteps_trans; [exact MS1| exact MS2]|]); (split; [| clear -Vnz FV; lia]);
    unfold PNADRN3.HD;
    (split; [unfold RRa; repeat split; first [ keep1 KS2 | (rewrite A14; f_equal; clear; lia) | (rewrite A15; apply to_bv_eqm; reflexivity) ]|]);
    (split; [exact A31|]); rewrite PNSDRN2.Wk3;
    (split; [rewrite A30; unfold PNADBV.msb, PNADBV.hi32; rewrite (PNDBV.f_parts0 hi a b c d E Ha Hb Hc Hd); unfold PNSDRN2.p0; rewrite HV, (PNDBV.f_p0 hi a b c d E Ha Hb Hc Hd lo Flo); apply Z.mod_small; clear -Hb Hc; lia|]);
    (split; [rewrite (KS2 28%nat) by inl; rewrite A28, (PNDBV.u_lit hi Fhi); unfold PNSDRN2.p1; rewrite HV, (PNDBV.f_mod49 hi a b c d E Ha Hb Hc Hd);
             rewrite (PNDBV.f_mod32 hi a b c d E Ha Hb Hc Hd);
             replace ((2 ^ 46 * b + 2 ^ 32 * c + d) * 2 ^ 64 + lo) with (lo + (2 ^ 46 * b + 2 ^ 32 * c + d) * 2 ^ 64) by (clear; lia);
             rewrite Z.div_add by (clear; lia); rewrite (Z.div_small lo) by exact Flo; rewrite Z.add_0_l;
             apply (Z.mod_unique_pos _ _ (2 ^ 14 * b + c)); clear -Hb Hc Hd; lia|]);
    (split; [apply to_bv_of_unsigned; rewrite A29, (PNDBV.rot_lo lo Flo); unfold PNSDRN2.p2, PNSDRN2.p3; rewrite HV;
             pose proof (Z.div_mod lo (2 ^ 32) ltac:(clear; lia)) as EL; pose proof (Z.mod_pos_bound lo (2 ^ 32) ltac:(clear; lia)) as BL;
             assert (QL : 0 <= lo / 2 ^ 32 < 2 ^ 32) by (split; [apply Z.div_pos; clear -Flo; lia| apply Z.div_lt_upper_bound; [clear; lia| change (2 ^ 32 * 2 ^ 32) with (2 ^ 64); clear -Flo; lia]]);
             replace ((hi mod 2 ^ 49 * 2 ^ 64 + lo) / 2 ^ 32) with ((hi mod 2 ^ 49) * 2 ^ 32 + lo / 2 ^ 32) by (apply (Z.div_unique_pos _ _ _ (lo mod 2 ^ 32)); clear -EL BL; lia);
             replace ((hi mod 2 ^ 49 * 2 ^ 32 + lo / 2 ^ 32) mod 2 ^ 32) with ((lo / 2 ^ 32) mod 2 ^ 32)
               by (replace (hi mod 2 ^ 49 * 2 ^ 32 + lo / 2 ^ 32) with (lo / 2 ^ 32 + hi mod 2 ^ 49 * 2 ^ 32) by (clear; lia); rewrite Z.mod_add; [reflexivity| clear; lia]);
             replace ((hi mod 2 ^ 49 * 2 ^ 64 + lo) mod 2 ^ 32) with (lo mod 2 ^ 32); [reflexivity|];
             replace (hi mod 2 ^ 49 * 2 ^ 64 + lo) with (lo + (hi mod 2 ^ 49 * 2 ^ 32) * 2 ^ 32) by (clear; lia); rewrite Z.mod_add; [reflexivity| clear; lia]|]);
    (split; [exact WR|]); (split; [exact WF|]); (split; [exact DG| exact ZR]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem middle fx R M :
  PNADD.stJ R0 S F first sigma vp R -> L5.writable RSEGS M (S - 128) 128 -> L5.writable RSEGS M F 512 -> L5.img_clear M 65536 1269760 ->
  L5KA.zeros_at M (PNADD.SH F + 4) 18 -> zers M 4 -> PNADD.vp_at M vp lo hi ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R 0xb2964 M) (st fx' R' pc' M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wrnd a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ ((pc' = 0xb3100 /\ PNADD.stX R0 S F first sigma hi lo R' /\ (forall a, M' a = M a))
        \/ (pc' = 0xb2b04 /\ exists z sd, PNADD.stP R0 S F first sigma e14 z sd R' /\ 0 <= z /\ 1 <= sd /\ z + sd <= 36 /\ PNADD.sdigs F M' z sd)).
Proof.
  intros SJ WR WF IC ZSH ZR VP.
  assert (DG : digs M 4) by (intros i Hi; exfalso; clear -Hi; lia).
  destruct (decode fx R M SJ WR WF IC DG ZR VP) as (fx1 & R1 & [(MS1 & SX) | [(MS1 & SZ & A11) | (MS1 & HD3 & Vp)]]).
  - exists fx1, R1, M, 0xb3100. split; [exact MS1|]. split; [intros a Ha; exact Ha|]. split; [intros; reflexivity|].
    left. split; [reflexivity|]. split; [exact SX| intros; reflexivity].
  - destruct (iszero fx1 R1 M e14 SZ A11 WR WF) as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & SP & C0).
    exists fx2, R2, M2, 0xb2b04. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG2|].
    split; [intros a Ha Hn; apply (FZ2 a Ha); unfold PNADRN3.Wrnd in Hn; clear -Hn; lia|].
    right. split; [reflexivity|]. exists 0, 1. split; [exact SP|].
    split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
    intros i Hi. exists 0. replace i with 0 by (clear -Hi; lia). split; [exact C0| clear; lia].
  - destruct (rounds fx1 R1 M HD3) as (fx2 & R2 & M2 & MG2 & FZ2 & WR2 & WF2 & MS2 & RB2 & DG2).
    assert (ZSH2 : L5KA.zeros_at M2 (PNADD.SH F + 4) 18).
    { apply (L5KA.zeros_at_agree1 M M2 _ _); [| exact ZSH]. intros i Hi. apply FZ2.
      - unfold PNADD.SH, PNADD.SBv in Hi. pose proof (Z.div_pos F 8 ltac:(clear -FF1; lia) ltac:(clear; lia)) as Q0.
        assert (Q1 : F / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; clear -FF1; lia). clear -Hi Q0 Q1. lia.
      - unfold PNADRN3.Wrnd, PNADD.SH, PNADD.SBv in *. intros [X|X].
        + pose proof (Z.div_pos F 8 ltac:(clear -FF1; lia) ltac:(clear; lia)) as Q0.
          assert (Q1 : F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear -FF1; lia). clear -Hi X Q0 Q1 FS. lia.
        + pose proof (Z.div_mod F 8 ltac:(clear; lia)) as E8. pose proof (Z.mod_pos_bound F 8 ltac:(clear; lia)) as B8.
          clear -Hi X E8 B8 FFSH. lia. }
    destruct (scan Vp fx2 R2 M2 RB2 DG2 WR2 ZSH2) as (fx3 & R3 & z & MS3 & SP & Hz).
    exists fx3, R3, M2, 0xb2b04. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|]. split; [exact MG2|]. split; [exact FZ2|].
    right. split; [reflexivity|]. exists z, (36 - z). split; [exact SP|].
    split; [clear -Hz; lia|]. split; [clear -Hz; lia|]. split; [clear -Hz; lia|].
    intros i Hi. exists (PNDF.dg V i). split; [apply DG2; clear -Hi Hz; lia| apply PNDF.dg_range].
Qed.
End Decode.

End Call.
End PNADMID.
