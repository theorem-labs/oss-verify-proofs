(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk L5Defs L5Core L5CoreKit
     AxSymExec3 Bs0PlanKit PmStep PmKeep PnDecFacts PnMemW PnDecBv PnSDec128Defs PnSDec128RP PnSDec128AP PnSDec128Rnd PnSDec128Rnd2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDMID.
Import PNSDRN PNSDRN2.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Call.


Variables (R0 : bvmap 5 word) (S first sigma e V r : Z).
Hypothesis Fr : 0 <= r < 2 ^ 47.
Hypothesis FS : 140735332483312 <= S <= 140737488355328.
Hypothesis F16 : S mod 16 = 0.
Hypothesis Ffirst : 4096 <= first <= 140737488355286.
Hypothesis Fdj : S - 18432 + 18432 <= first \/ first + 42 <= S - 18432.
Hypothesis Fe : 0 <= e <= 16383.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis FV : 0 <= V < 2 ^ 113.

Abbreviation saves := (PNSDD.saves R0 S r).
Abbreviation MI := (PNSDD.MI R0 S first r).
Abbreviation cell := (PNSDD.cell S).
Abbreviation digs := (PNSDD.digs S V).
Abbreviation zers := (PNSDD.zers S).
Abbreviation RR := (PNSDRN.RR R0 S first sigma e).
Abbreviation ufacts := (PNSDRN.ufacts R0 S).
Abbreviation MI_xfer := (PNSDD.MI_xfer R0 S first r FS).
Abbreviation cell_xfer := (PNSDD.cell_xfer S FS).
Abbreviation VV := (PNSDRN2.VV R0 S first sigma e r).
Abbreviation HD := (PNSDRN2.HD R0 S first sigma e V r).
Abbreviation Wk := (PNSDRN2.Wk V).
Abbreviation bvu_small := PNSDRN2.bvu_small.
Abbreviation round_step := (PNSDRN2.round_step R0 S first sigma e V r Fr FS F16 Ffirst Fdj Fe Fsig FV).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rounds fx R M : HD R M 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 240 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M' /\ msteps RSEGS (st fx R 0x37b84 M) (st fx' R' 0x37c40 M') /\ PNSDD.RB R0 S first sigma R'
    /\ getr R' (reg 10) = Z_to_bv 64 e /\ getr R' (reg 11) = Z_to_bv 64 (e - 6176) /\ getr R' (reg 12) = Z_to_bv 64 (PNDF.dg V 0) /\ digs M' 0.
Proof.
  intros HD3.
  destruct (round_step fx R M 3 ltac:(clear; lia) HD3) as (fx1 & R1 & M1 & MG1 & FZ1 & MI1 & [(K & _) | (_ & MS1 & HD2)]); [exfalso; clear -K; lia|].
  destruct (round_step fx1 R1 M1 (3 - 1) ltac:(clear; lia) HD2) as (fx2 & R2 & M2 & MG2 & FZ2 & MI2 & [(K & _) | (_ & MS2 & HD1)]); [exfalso; clear -K; lia|].
  destruct (round_step fx2 R2 M2 (3 - 1 - 1) ltac:(clear; lia) HD1) as (fx3 & R3 & M3 & MG3 & FZ3 & MI3 & [(K & _) | (_ & MS3 & HD0)]); [exfalso; clear -K; lia|].
  destruct (round_step fx3 R3 M3 (3 - 1 - 1 - 1) ltac:(clear; lia) HD0) as (fx4 & R4 & M4 & MG4 & FZ4 & MI4 & [(_ & MS4 & RB4 & A10 & A11 & A12 & DG4) | (K & _)]); [| exfalso; clear -K; lia].
  exists fx4, R4, M4. split; [intros a Ha; apply MG4; apply MG3; apply MG2; apply MG1; exact Ha|].
  split. { intros a Ha Hn. rewrite (FZ4 a Ha Hn), (FZ3 a Ha Hn), (FZ2 a Ha Hn). exact (FZ1 a Ha Hn). }
  split; [exact MI4|].
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]|].
  split; [exact RB4|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12| exact DG4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma V_lt35 : V < 10 ^ 35.
Proof. clear -FV. assert (2 ^ 113 < 10 ^ 35) by (vm_compute; reflexivity). lia. Qed.
Lemma dg0 : PNDF.dg V 0 = 0.
Proof. unfold PNDF.dg. replace (35 - 0) with 35 by (clear; lia). rewrite Z.div_small; [reflexivity|]. pose proof V_lt35. clear -H FV; lia. Qed.

Lemma scan_loop (FVp : 0 < V) (n : nat) : forall fx R M i,
  35 - i = Z.of_nat n -> 0 <= i <= 34 -> V < 10 ^ (35 - i) ->
  PNSDD.RB R0 S first sigma R -> getr R (reg 10) = Z_to_bv 64 e -> getr R (reg 11) = Z_to_bv 64 (e - 6176) ->
  getr R (reg 13) = Z_to_bv 64 (S - 216 + 4 * i) -> getr R (reg 21) = Z_to_bv 64 (36 - i) -> digs M 0 -> MI M ->
  exists fx' R' z, msteps RSEGS (st fx R 0x37c6c M) (st fx' R' 0x37c80 M) /\ PNSDD.stP R0 S first sigma e z (36 - z) (PNDF.dg V z) R' /\ i < z <= 35.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi HV RBR G10 G11 G13 G21 DG MIM.
  { exfalso. clear -Hn Hi. lia. }
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  destruct RBR as (G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof (PNDF.dg_range V (i + 1)) as Hd.
  assert (C : L5.u32_at RSEGS M (S - 216 + 4 * i + 4) (PNDF.dg V (i + 1))).
  { pose proof (DG (i + 1) ltac:(clear -Hi; lia)) as C. unfold PNSDD.cell in C. replace (S - 216 + 4 * i + 4) with (S - 216 + 4 * (i + 1)) by (clear; lia). exact C. }
  (let T := type of (PNSDAP.dkSC_conc fx R M (fun j => match j with 52%nat => i | 53%nat => PNDF.dg V (i + 1) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkSC_conc fx R M (fun j => match j with 52%nat => i | 53%nat => PNDF.dg V (i + 1) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A12 & A13 & A20 & A21 & Hz) | (MS1 & KS1 & A12 & A13 & A20 & A21 & Hnz) ]).
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
    rewrite Z.sub_0_r, Z.mod_small in Hz by (clear -Hd; lia).
    assert (D0 : PNDF.dg V (i + 1) = 0) by (clear -Hz Hd; lia).
    pose proof (PNDF.dg_zero_step V (i + 1) ltac:(clear -FV; lia) ltac:(clear -Hi; lia) ltac:(replace (35 - (i + 1) + 1) with (35 - i) by (clear; lia); exact HV) D0) as HV'.
    assert (Hi' : i + 1 <= 34).
    { destruct (Z_lt_le_dec 34 (i + 1)) as [LT|LE]; [| exact LE]. exfalso.
      replace (35 - (i + 1)) with 0 in HV' by (clear -LT Hi; lia). clear -HV' FVp. cbn in HV'. lia. }
    destruct (IH fx1 R1 M (i + 1) ltac:(clear -Hn; lia) ltac:(clear -Hi Hi'; lia) HV') as (fx2 & R2 & z & MS2 & SP & Hz2).
    + unfold PNSDD.RB. repeat apply conj; PMK.sc.
    + PMK.sc. + PMK.sc. + PMK.sc. + PMK.sc. + exact DG. + exact MIM.
    + exists fx2, R2, z. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP| clear -Hz2 Hi; lia].
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
    exists fx1, R1, (i + 1). split; [exact MS1|].
    split; [| clear -Hi; lia]. unfold PNSDD.stP, PNSDD.RB.
    replace (getr R1 (reg 10)) with (getr R (reg 10)) by (symmetry; PMK.sc). rewrite G10, (bvu_small e) by (clear -Fe; lia).
    repeat apply conj; PMK.sc.
Qed.

(* [comment removed for export] *)
Lemma scan (FVp : 0 < V) fx R M :
  PNSDD.RB R0 S first sigma R -> getr R (reg 10) = Z_to_bv 64 e -> getr R (reg 11) = Z_to_bv 64 (e - 6176) -> getr R (reg 12) = Z_to_bv 64 (PNDF.dg V 0) ->
  digs M 0 -> MI M ->
  exists fx' R' z, msteps RSEGS (st fx R 0x37c40 M) (st fx' R' 0x37c80 M) /\ PNSDD.stP R0 S first sigma e z (36 - z) (PNDF.dg V z) R' /\ 1 <= z <= 35.
Proof.
  intros RBR G10 G11 G12 DG MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  destruct RBR as (G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  rewrite dg0 in G12.
  (let T := type of (PNSDAP.dkZ1_conc fx R M (fun j => match j with 51%nat => 0 | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkZ1_conc fx R M (fun j => match j with 51%nat => 0 | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A20 & A21 & Hnz) | (MS1 & KS1 & A13 & A21 & Hz) ]).
  { exfalso. clear -Hnz. rewrite Z.sub_0_r, Z.mod_small in Hnz by lia. lia. }
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  pose proof V_lt35 as HV.
  destruct (scan_loop FVp 35%nat fx1 R1 M 0 eq_refl ltac:(clear; lia) ltac:(replace (35 - 0) with 35 by (clear; lia); exact HV)) as (fx2 & R2 & z & MS2 & SP & Hz2).
  - unfold PNSDD.RB. repeat apply conj; PMK.sc.
  - PMK.sc. - PMK.sc. - PMK.sc. - PMK.sc. - exact DG. - exact MIM.
  - exists fx2, R2, z. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP| clear -Hz2; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma to_bv_eqm a b : a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact E. Qed.
Lemma land_le_r a m : 0 <= a -> 0 <= m -> Z.land a m <= m.
Proof. intros Ha Hm. rewrite Z.land_comm. apply PNSDAP.land_le_l; assumption. Qed.

Section Decode.
Variables (vp hi lo : Z).
Hypothesis Fvp : 4096 <= vp <= 140737488355312.
Hypothesis Fvp8 : vp mod 8 = 0.
Hypothesis Fvpdj : S - 240 + 240 <= vp \/ vp + 16 <= S - 240.
Hypothesis Fvpf : first + 42 <= vp \/ vp + 16 <= first.
Hypothesis Fhi : 0 <= hi < 2 ^ 64.
Hypothesis Flo : 0 <= lo < 2 ^ 64.
Hypothesis HV : V = (hi mod 2 ^ 49) * 2 ^ 64 + lo.
Hypothesis He : e = Z.land (hi / 4294967296 / 131072) 16383.

Lemma decode fx R M :
  PNSDD.stJ R0 S first sigma vp hi R -> MI M -> zers M 4 -> PNSDD.vp_at M vp lo hi ->
  exists fx' R',
    (msteps RSEGS (st fx R 0x37ae0 M) (st fx' R' 0x37ef8 M) /\ PNSDD.stX R0 S first sigma vp hi lo R' /\ Z.land (hi / 2 ^ 32) 1610612736 = 1610612736)
    \/ (msteps RSEGS (st fx R 0x37ae0 M) (st fx' R' 0x37c50 M) /\ PNSDD.stZ R0 S first sigma e R' /\ V = 0)
    \/ (msteps RSEGS (st fx R 0x37ae0 M) (st fx' R' 0x37b84 M) /\ HD R' M 3 /\ 0 < V).
Proof.
  intros ((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & G19 & G12) MIM ZR (VP0 & VP8).
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  destruct (PNDBV.hi_fields hi Fhi) as (a & b & c & d & E & Ha & Hb & Hc & Hd).
  pose proof (PNDBV.f_e hi) as Fe'. rewrite <- He in Fe'.
  assert (A11x : Z_to_bv 64 ((Z.land (hi / 4294967296 / 131072) 16383 + 18446744073709545440) mod 2 ^ 64) = Z_to_bv 64 (e - 6176)).
  { rewrite <- He. apply to_bv_eqm. rewrite Z.mod_mod by (clear; lia). replace (e + 18446744073709545440) with (e - 6176 + 1 * 2 ^ 64) by (clear; lia).
    rewrite Z.mod_add; [reflexivity| clear; lia]. }
  (let T := type of (PNSDAP.dkB_conc fx R M (fun j => match j with 35%nat => vp | 36%nat => lo | 37%nat => hi | _ => VV 3 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkB_conc fx R M (fun j => match j with 35%nat => vp | 36%nat => lo | 37%nat => hi | _ => VV 3 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ X0 | [ X1 | [ X2 | X3 ]]]);
    assert (EM : M1 = M) by (apply functional_extensionality; exact FW1); subst M1.
  - (* [comment removed for export] *)
    destruct X0 as (MS1 & KS1 & A5 & A6 & A7 & A10 & A11 & A13 & A14 & A15 & A16 & A17 & A19' & A28 & A30 & A31 & Hnz & Hmsb & Hsp).
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in A13, Hnz.
    rewrite PNDBV.bv_sub_0 in Hnz. rewrite <- A13 in Hnz.
    change (getr R1 (reg 13) = (if bv_ltu (sext 64 (low32 (PNDBV.Xbv hi lo) + low32 (Z_to_bv 64 0))) (Z_to_bv 64 1) then Z_to_bv 64 1 else Z_to_bv 64 0)) in A13.
    rewrite PNDBV.ltu1, PNDBV.sextw_zero, (PNDBV.zero_test hi lo Fhi Flo), <- HV in A13.
    rewrite A13, PNDBV.ltu1, PNDBV.bvu_if in Hnz.
    destruct (Z.eqb_spec V 0) as [V0 | Vnz]. { exfalso. clear -Hnz. rewrite (PNDBV.u_lit 1) in Hnz by (clear; lia). cbn in Hnz. lia. }
    exists fx1, R1. right. right. split; [exact MS1|]. split; [| clear -Vnz FV; lia].
    assert (A10' : getr R1 (reg 10) = Z_to_bv 64 e) by (apply PNSDRN.to_bv_of_unsigned; rewrite A10; symmetry; exact He).
    assert (A11' : getr R1 (reg 11) = Z_to_bv 64 (e - 6176)) by (rewrite <- A11x; apply PNSDRN.to_bv_of_unsigned; exact A11).
    assert (A16' : getr R1 (reg 16) = Z_to_bv 64 (-36)) by (rewrite A16; apply to_bv_eqm; reflexivity).
    unfold PNSDRN2.HD. split.
    { unfold PNSDRN.RR. repeat apply conj; try PMK.sc. }
    split; [exact A19'|].
    rewrite PNSDRN2.Wk3.
    split. { rewrite A30. rewrite (PNDBV.f_parts0 hi a b c d E Ha Hb Hc Hd). unfold PNSDRN2.p0. rewrite HV, (PNDBV.f_p0 hi a b c d E Ha Hb Hc Hd lo Flo). apply Z.mod_small. clear -Hb Hc; lia. }
    split. { rewrite (KS1 12%nat) by PMK.inl. rewrite G12, (PNDBV.u_lit hi Fhi). unfold PNSDRN2.p1. rewrite HV, (PNDBV.f_mod49 hi a b c d E Ha Hb Hc Hd).
             rewrite (PNDBV.f_mod32 hi a b c d E Ha Hb Hc Hd).
             replace ((2 ^ 46 * b + 2 ^ 32 * c + d) * 2 ^ 64 + lo) with (lo + (2 ^ 46 * b + 2 ^ 32 * c + d) * 2 ^ 64) by (clear; lia).
             rewrite Z.div_add by (clear; lia). rewrite (Z.div_small lo) by exact Flo. rewrite Z.add_0_l.
             apply (Z.mod_unique_pos _ _ (2 ^ 14 * b + c)); clear -Hb Hc Hd; lia. }
    split. { apply PNSDRN.to_bv_of_unsigned. rewrite A31, (PNDBV.rot_lo lo Flo). unfold PNSDRN2.p2, PNSDRN2.p3. rewrite HV.
             pose proof (Z.div_mod lo (2 ^ 32) ltac:(clear; lia)) as EL. pose proof (Z.mod_pos_bound lo (2 ^ 32) ltac:(clear; lia)) as BL.
             assert (QL : 0 <= lo / 2 ^ 32 < 2 ^ 32).
             { split; [apply Z.div_pos; clear -Flo; lia|]. apply Z.div_lt_upper_bound; [clear; lia|]. change (2 ^ 32 * 2 ^ 32) with (2 ^ 64); clear -Flo; lia. }
             replace ((hi mod 2 ^ 49 * 2 ^ 64 + lo) / 2 ^ 32) with ((hi mod 2 ^ 49) * 2 ^ 32 + lo / 2 ^ 32).
             2:{ apply (Z.div_unique_pos _ _ _ (lo mod 2 ^ 32)); clear -EL BL; lia. }
             replace ((hi mod 2 ^ 49 * 2 ^ 32 + lo / 2 ^ 32) mod 2 ^ 32) with ((lo / 2 ^ 32) mod 2 ^ 32).
             2:{ replace (hi mod 2 ^ 49 * 2 ^ 32 + lo / 2 ^ 32) with (lo / 2 ^ 32 + hi mod 2 ^ 49 * 2 ^ 32) by (clear; lia). rewrite Z.mod_add; [reflexivity| clear; lia]. }
             replace ((hi mod 2 ^ 49 * 2 ^ 64 + lo) mod 2 ^ 32) with (lo mod 2 ^ 32); [reflexivity|].
             replace (hi mod 2 ^ 49 * 2 ^ 64 + lo) with (lo + (hi mod 2 ^ 49 * 2 ^ 32) * 2 ^ 32) by (clear; lia). rewrite Z.mod_add; [reflexivity| clear; lia]. }
    split; [exact MIM|]. split; [intros i Hi; exfalso; clear -Hi; lia| exact ZR].
  - (* [comment removed for export] *)
    destruct X1 as (MS1 & KS1 & A5 & A10 & A11 & A13 & A14 & A16 & A17 & A30 & Hz & Hmsb & Hsp).
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in A13, Hz.
    rewrite PNDBV.bv_sub_0 in Hz. rewrite <- A13 in Hz.
    change (getr R1 (reg 13) = (if bv_ltu (sext 64 (low32 (PNDBV.Xbv hi lo) + low32 (Z_to_bv 64 0))) (Z_to_bv 64 1) then Z_to_bv 64 1 else Z_to_bv 64 0)) in A13.
    rewrite PNDBV.ltu1, PNDBV.sextw_zero, (PNDBV.zero_test hi lo Fhi Flo), <- HV in A13.
    rewrite A13, PNDBV.ltu1, PNDBV.bvu_if in Hz.
    destruct (Z.eqb_spec V 0) as [V0 | Vnz]; [| exfalso; clear -Hz; rewrite (PNDBV.u_lit 0) in Hz by (clear; lia); cbn in Hz; lia].
    exists fx1, R1. right. left. split; [exact MS1|]. split; [| exact V0].
    assert (A11' : getr R1 (reg 11) = Z_to_bv 64 (e - 6176)) by (rewrite <- A11x; apply PNSDRN.to_bv_of_unsigned; exact A11).
    unfold PNSDD.stZ, PNSDD.RB. rewrite He. repeat apply conj; try PMK.sc. rewrite <- He. exact A11'.
  - (* [comment removed for export] *)
    exfalso. destruct X2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hmsb & _). rewrite (PNDBV.f_msb hi a b c d E Ha Hb Hc Hd) in Hmsb. clear -Hmsb Hb; lia.
  - (* [comment removed for export] *)
    destruct X3 as (MS1 & KS1 & A10 & A11 & A13 & A14 & Hsp).
    exists fx1, R1. left. split; [exact MS1|].
    split. { unfold PNSDD.stX, PNSDD.RB. change (2 ^ 32) with 4294967296. repeat apply conj; PMK.sc. }
    pose proof (land_le_r (hi / 4294967296) 1610612736 ltac:(apply Z.div_pos; clear -Fhi; lia) ltac:(clear; lia)) as LE.
    assert (NN' : 0 <= Z.land (hi / 4294967296) 1610612736) by (apply Z.land_nonneg; right; clear; lia).
    change (2 ^ 32) with 4294967296.
    destruct (Z.eq_dec (Z.land (hi / 4294967296) 1610612736) 1610612736) as [EQ|NE]; [exact EQ| exfalso].
    replace ((Z.land (hi / 4294967296) 1610612736 - 1610612736) mod 2 ^ 64) with (Z.land (hi / 4294967296) 1610612736 - 1610612736 + 2 ^ 64) in Hsp.
    { clear -Hsp LE NE NN'; lia. }
    apply (Z.mod_unique_pos _ _ (-1)); clear -LE NE NN'; lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iszero fx R M :
  PNSDD.stZ R0 S first sigma e R -> MI M ->
  exists fx' R' M', msteps RSEGS (st fx R 0x37c50 M) (st fx' R' 0x37c80 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 216 <= a < S - 212) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ PNSDD.stP R0 S first sigma e 0 1 0 R' /\ MI M' /\ cell M' 0 0.
Proof.
  intros ((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & A10 & G11) MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (G10 : getr R (reg 10) = Z_to_bv 64 e) by (apply PNSDRN.to_bv_of_unsigned; exact A10).
  (let T := type of (PNSDAP.dkZ0_conc fx R M (VV 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDAP.dkZ0_conc fx R M (VV 0)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FZ1 & MS1 & KS1 & A12 & A20 & A21 & C0)); PMK.pvz_clrT.
  exists fx1, R1, M1. split; [exact MS1|]. split; [exact MG1|].
  split. { intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
  split. { unfold PNSDD.stP, PNSDD.RB. replace (getr R1 (reg 10)) with (getr R (reg 10)) by (symmetry; PMK.sc). rewrite A10.
           replace (S - 216 + 4 * 0) with (S - 216) by (clear; lia). repeat apply conj; PMK.sc. }
  split. { apply (MI_xfer M M1 MIM MG1). intros a Ha Hn. apply (FZ1 a Ha). clear -Hn; lia. }
  unfold PNSDD.cell. replace (S - 216 + 4 * 0) with (S - 216) by (clear; lia). exact C0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem middle fx R M :
  PNSDD.stJ R0 S first sigma vp hi R -> MI M -> zers M 4 -> PNSDD.vp_at M vp lo hi ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 240 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) /\ MI M'
    /\ ((msteps RSEGS (st fx R 0x37ae0 M) (st fx' R' 0x37ef8 M') /\ PNSDD.stX R0 S first sigma vp hi lo R' /\ Z.land (hi / 2 ^ 32) 1610612736 = 1610612736
           /\ (forall a, M' a = M a))
        \/ (exists z sd d, msteps RSEGS (st fx R 0x37ae0 M) (st fx' R' 0x37c80 M') /\ PNSDD.stP R0 S first sigma e z sd d R'
           /\ 0 <= z /\ 1 <= sd /\ z + sd <= 36 /\ 0 <= d <= 9 /\ PNSDD.sdigs S M' z sd)).
Proof.
  intros SJ MIM ZR VP.
  destruct (decode fx R M SJ MIM ZR VP) as (fx1 & R1 & [(MS1 & SX & HS) | [(MS1 & SZ & V0) | (MS1 & HD3 & Vp)]]).
  - exists fx1, R1, M. split; [intros a Ha; exact Ha|]. split; [intros; reflexivity|]. split; [exact MIM|].
    left. split; [exact MS1|]. split; [exact SX|]. split; [exact HS| intros; reflexivity].
  - destruct (iszero fx1 R1 M SZ MIM) as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & SP & MI2 & C0).
    exists fx2, R2, M2. split; [exact MG2|]. split; [intros a Ha Hn; apply (FZ2 a Ha); clear -Hn; lia|]. split; [exact MI2|].
    right. exists 0, 1, 0. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact SP|].
    split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
    intros i Hi. exists 0. replace i with 0 by (clear -Hi; lia). split; [exact C0| clear; lia].
  - destruct (rounds fx1 R1 M HD3) as (fx2 & R2 & M2 & MG2 & FZ2 & MI2 & MS2 & RB2 & A10 & A11 & A12 & DG2).
    destruct (scan Vp fx2 R2 M2 RB2 A10 A11 A12 DG2 MI2) as (fx3 & R3 & z & MS3 & SP & Hz).
    exists fx3, R3, M2. split; [exact MG2|]. split; [exact FZ2|]. split; [exact MI2|].
    right. exists z, (36 - z), (PNDF.dg V z). split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|]. split; [exact SP|].
    split; [clear -Hz; lia|]. split; [clear -Hz; lia|]. split; [clear -Hz; lia|]. split; [apply PNDF.dg_range|].
    intros i Hi. exists (PNDF.dg V i). split; [apply DG2; clear -Hi Hz; lia| apply PNDF.dg_range].
Qed.
End Decode.

End Call.
End PNSDMID.
