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
     AxSymExec3 Bs0PlanKit PmStep PmKeep PnDecFacts PnMemW PnDecBv PnSDec128Defs PnSDec128OP PnSDec128Rnd PnSDec128Rnd2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDOUT.
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
Abbreviation ufacts := (PNSDRN.ufacts R0 S).
Abbreviation MI_xfer := (PNSDD.MI_xfer R0 S first r FS).
Abbreviation cell_xfer := (PNSDD.cell_xfer S FS).
Abbreviation VV := (PNSDRN2.VV R0 S first sigma e r).
Abbreviation bvu_small := PNSDRN2.bvu_small.

Section Out.
(* [comment removed for export] *)
Hypothesis Fimg : first + 42 <= 65536 \/ 958464 <= first.
(* [comment removed for export] *)
Variables (z sd d : Z).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma to_bv_add a b : (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma slt_lit a b : - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_unsigned (if bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) then Z_to_bv 64 1 else Z_to_bv 64 0) = (if a <? b then 1 else 0).
Proof.
  intros Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  assert (HM : bv_half_modulus 64 = 2 ^ 63) by (vm_compute; reflexivity).
  rewrite !bv_swrap_small by (rewrite HM; clear -Ha Hb; lia). destruct (a <? b); reflexivity.
Qed.

Lemma to_bv_eqm a b : a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact E. Qed.

(* [comment removed for export] *)
Lemma MI_out M M' : MI M -> mem_grows M M' -> PNSDD.agree_but (PNSDD.in_out first) M M' -> MI M'.
Proof.
  intros (W1 & W2 & IC & SV) MG FZ. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W1)|]. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W2)|].
  split. { apply (PMKP.clear_agree M M' 65536 749064); [|exact IC]. intros i Hi. apply FZ; [clear -Hi; lia|]. unfold PNSDD.in_out. clear -Hi Fimg; lia. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ; [clear -Hi FS; lia| unfold PNSDD.in_out; clear -Hi FS Fdj; lia]| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.

(* [comment removed for export] *)
Definition RL (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 240) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 8) = Z_to_bv 64 (first + 42) /\ getr R (reg 18) = Z_to_bv 64 (first + sigma)
  /\ getr R (reg 24) = getr R0 (reg 24) /\ getr R (reg 25) = getr R0 (reg 25) /\ getr R (reg 26) = getr R0 (reg 26) /\ getr R (reg 27) = getr R0 (reg 27).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gloop (n : nat) : forall fx R M i,
  sd - i = Z.of_nat n -> 0 <= i < sd -> sigma + i <= 35 -> z + sd <= 36 -> 0 <= z ->
  RL R -> getr R (reg 10) = Z_to_bv 64 i -> getr R (reg 11) = Z_to_bv 64 (sigma + 1) -> getr R (reg 12) = Z_to_bv 64 sd ->
  getr R (reg 13) = Z_to_bv 64 36 -> getr R (reg 20) = Z_to_bv 64 (S - 216 + 4 * (z + i)) -> MI M -> L5.defined M (S - 216) 144 ->
  exists fx' R' M' cnt, msteps RSEGS (st fx R 0x37cd0 M) (st fx' R' 0x37fe0 M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ PNSDD.stE R0 S (first + sigma + cnt) R' /\ i < cnt <= sd /\ sigma + cnt <= 36 /\ MI M'.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi Hsi Hz Hz0 RBR G10 G11 G12 G13 G20 MIM DF; [exfalso; clear -Hn Hi; lia|].
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  destruct RBR as (G2 & G3 & G4 & G8 & G18 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof (bv_unsigned_in_range _ (getr R (reg 9))) as R9. unfold bv_modulus in R9. cbn in R9.
  assert (G9' : getr R (reg 9) = Z_to_bv 64 (bv_unsigned (getr R (reg 9)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  (let T := type of (PNSDOP.dkG2_conc fx R M (fun j => match j with 57%nat => i | 55%nat => sd | 58%nat => z + i | 59%nat => bv_unsigned (getr R (reg 9)) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkG2_conc fx R M (fun j => match j with 57%nat => i | 55%nat => sd | 58%nat => z + i | 59%nat => bv_unsigned (getr R (reg 9)) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A9 & A10 & A14 & A15 & A20 & Hlt & Hmore) | [ (MS1 & KS1 & A9 & A11 & A15 & Hdone) | (MS1 & KS1 & A9 & A10 & A11 & A14 & A15 & A20 & Hge & Hmore) ]]).
  - (* [comment removed for export] *)
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hlt. rewrite !to_bv_add, slt_lit in Hlt by (clear -Hsi Hi Fsig; lia).
    destruct (Z.ltb_spec (sigma + i + 1) 36) as [Hl|Hl]; [| exfalso; clear -Hlt; lia].
    rewrite Z.mod_small in Hmore by (clear -Hi Hz Hz0; lia).
    pose proof (MI_out M M1 MIM MG1 ltac:(intros a Ha Hn'; apply (FZ1 a Ha); unfold PNSDD.in_out in Hn'; clear -Hn' Hi Hsi Fsig; lia)) as MI1.
    destruct (IH fx1 R1 M1 (i + 1) ltac:(clear -Hn; lia) ltac:(clear -Hi Hmore; lia) ltac:(clear -Hl; lia) Hz Hz0) as (fx2 & R2 & M2 & cnt & MS2 & MG2 & AG2 & SE2 & Hcnt & Hsc & MI2).
    + unfold RL. repeat apply conj; PMK.sc.
    + exact A10. + PMK.sc. + PMK.sc. + PMK.sc. + rewrite A20. f_equal. clear; lia. + exact MI1. + exact (L5.defined_grows M M1 _ _ MG1 DF).
    + exists fx2, R2, M2, cnt. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
      split. { intros a Ha Hn'. rewrite (AG2 a Ha Hn'). apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
      split; [exact SE2|]. split; [clear -Hcnt Hi; lia|]. split; [exact Hsc| exact MI2].
  - (* [comment removed for export] *)
    rewrite Z.mod_small in Hdone by (clear -Hi Hz Hz0; lia).
    exists fx1, R1, M1, (i + 1). split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
    split. { unfold PNSDD.stE. repeat apply conj; PMK.sc. }
    split; [clear -Hi Hdone; lia|]. split; [clear -Hsi; lia|].
    apply (MI_out M M1 MIM MG1). intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia.
  - (* [comment removed for export] *)
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hge. rewrite !to_bv_add, slt_lit in Hge by (clear -Hsi Hi Fsig; lia).
    destruct (Z.ltb_spec (sigma + i + 1) 36) as [Hl|Hl]; [exfalso; clear -Hge; lia|].
    exists fx1, R1, M1, (i + 1). split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
    split. { unfold PNSDD.stE. repeat apply conj; PMK.sc. }
    rewrite Z.mod_small in Hmore by (clear -Hi Hz Hz0; lia).
    split; [clear -Hi Hmore; lia|]. split; [clear -Hsi; lia|].
    apply (MI_out M M1 MIM MG1). intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia.
Qed.

Lemma regular fx R M :
  PNSDD.stQ R0 S first sigma e z sd R -> MI M -> L5.defined M (S - 216) 144 -> 0 <= z -> 1 <= sd -> z + sd <= 36 ->
  exists fx' R' M' cnt, msteps RSEGS (st fx R 0x37ca8 M) (st fx' R' 0x37fe0 M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ PNSDD.stE R0 S (first + sigma + cnt) R' /\ 1 <= cnt <= sd /\ sigma + cnt <= 36 /\ MI M'.
Proof.
  intros ((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & A10 & G11 & G20 & G21) MIM DF Hz0 Hsd Hz.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (G10 : getr R (reg 10) = Z_to_bv 64 e) by (apply PNSDRN.to_bv_of_unsigned; exact A10).
  (let T := type of (PNSDOP.dkG1_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkG1_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A10' & A11 & A12 & A13 & A21).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  destruct (gloop (Z.to_nat sd) fx1 R1 M 0 ltac:(clear -Hsd; lia) ltac:(clear -Hsd; lia) ltac:(clear -Fsig; lia) Hz Hz0)
    as (fx2 & R2 & M2 & cnt & MS2 & MG2 & AG2 & SE2 & Hcnt & Hsc & MI2).
  - unfold RL. repeat apply conj; PMK.sc.
  - exact A10'. - exact A11. - exact A12. - exact A13. - replace (z + 0) with z by (clear; lia). PMK.sc. - exact MIM. - exact DF.
  - exists fx2, R2, M2, cnt. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG2|]. split; [exact AG2|]. split; [exact SE2|].
    split; [clear -Hcnt; lia|]. split; [exact Hsc| exact MI2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma epilogue fx R M ptr :
  PNSDD.stE R0 S ptr R -> MI M -> 0 <= ptr < 2 ^ 64 ->
  exists fx' R', msteps RSEGS (st fx R 0x37fe0 M) (st fx' R' 0x3800c M)
    /\ getr R' (reg 1) = Z_to_bv 64 r /\ getr R' (reg 2) = Z_to_bv 64 S /\ getr R' (reg 10) = Z_to_bv 64 ptr
    /\ (forall k, In k PNSDD.CS -> getr R' (reg k) = getr R0 (reg k)).
Proof.
  intros (G2 & G3 & G4 & G9 & G24 & G25 & G26 & G27) MIM Hptr.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof (bv_unsigned_in_range _ (getr R (reg 8))) as R8. unfold bv_modulus in R8. cbn in R8.
  assert (G8 : getr R (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 8)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  (let T := type of (PNSDOP.dkE_conc fx R M (fun j => match j with 59%nat => ptr | 58%nat => bv_unsigned (getr R (reg 8)) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkE_conc fx R M (fun j => match j with 59%nat => ptr | 58%nat => bv_unsigned (getr R (reg 8)) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A18 & A19 & A20 & A21 & A22 & A23).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  exists fx1, R1. split; [exact MS1|]. split; [exact A1|]. split; [exact A2|]. split; [exact A10|].
  intros k Hk. unfold PNSDD.CS in Hk.
  destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
    first [ rewrite A8 | rewrite A9 | rewrite A18 | rewrite A19 | rewrite A20 | rewrite A21 | rewrite A22 | rewrite A23 | PMK.sc ]; apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iloop (sciw : Z) (n : nat) : forall fx R M i,
  (sd - 1) - i = Z.of_nat n -> 0 <= i < sd - 1 -> sigma + 2 + i <= 35 -> z + sd <= 36 -> 0 <= z -> 0 <= sciw < 2 ^ 64 ->
  RL R -> getr R (reg 10) = Z_to_bv 64 i -> getr R (reg 11) = Z_to_bv 64 (sd - 1) -> getr R (reg 12) = Z_to_bv 64 (sigma + 3) ->
  getr R (reg 13) = Z_to_bv 64 36 -> getr R (reg 20) = Z_to_bv 64 (S - 216 + 4 * (z + 1 + i)) -> getr R (reg 21) = Z_to_bv 64 (first + sigma + 2) ->
  getr R (reg 19) = Z_to_bv 64 sciw -> getr R (reg 9) = Z_to_bv 64 first -> MI M -> L5.defined M (S - 216) 144 ->
  exists fx' R' M' p, msteps RSEGS (st fx R 0x37d44 M) (st fx' R' 0x37dac M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ RL R' /\ getr R' (reg 21) = Z_to_bv 64 (first + p) /\ getr R' (reg 19) = Z_to_bv 64 sciw
    /\ getr R' (reg 9) = Z_to_bv 64 first /\ sigma + 3 <= p <= 37 /\ MI M'.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi Hsi Hz Hz0 Hsw RLR G10 G11 G12 G13 G20 G21 G19 G9 MIM DF; [exfalso; clear -Hn Hi; lia|].
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  destruct RLR as (G2 & G3 & G4 & G8 & G18 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDOP.dkI2_conc fx R M (fun j => match j with 57%nat => i | 59%nat => sd - 1 | 58%nat => z + 1 + i | 52%nat => sciw | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI2_conc fx R M (fun j => match j with 57%nat => i | 59%nat => sd - 1 | 58%nat => z + 1 + i | 52%nat => sciw | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A10 & A14 & A15 & A20 & Hlt & Hmore) | [ (MS1 & KS1 & A14 & A15 & A21 & Hdone) | (MS1 & KS1 & A10 & A14 & A15 & A20 & A21 & Hge & Hmore) ]]).
  - cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hlt. rewrite !to_bv_add, slt_lit in Hlt by (clear -Hsi Hi Fsig; lia).
    destruct (Z.ltb_spec (sigma + i + 3) 36) as [Hl|Hl]; [| exfalso; clear -Hlt; lia].
    rewrite Z.mod_small in Hmore by (clear -Hi Hz Hz0; lia).
    pose proof (MI_out M M1 MIM MG1 ltac:(intros a Ha Hn'; apply (FZ1 a Ha); unfold PNSDD.in_out in Hn'; clear -Hn' Hi Hsi Fsig; lia)) as MI1.
    destruct (IH fx1 R1 M1 (i + 1) ltac:(clear -Hn; lia) ltac:(clear -Hi Hmore; lia) ltac:(clear -Hl; lia) Hz Hz0 Hsw) as (fx2 & R2 & M2 & p & MS2 & MG2 & AG2 & RL2 & B21 & B19 & B9 & Hp & MI2).
    + unfold RL. repeat apply conj; PMK.sc.
    + exact A10. + PMK.sc. + PMK.sc. + PMK.sc. + rewrite A20. f_equal. clear; lia. + PMK.sc. + PMK.sc. + PMK.sc. + exact MI1. + exact (L5.defined_grows M M1 _ _ MG1 DF).
    + exists fx2, R2, M2, p. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
      split. { intros a Ha Hn'. rewrite (AG2 a Ha Hn'). apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
      split; [exact RL2|]. split; [exact B21|]. split; [exact B19|]. split; [exact B9|]. split; [exact Hp| exact MI2].
  - rewrite Z.mod_small in Hdone by (clear -Hi Hz Hz0; lia).
    exists fx1, R1, M1, (sigma + i + 3). split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
    split. { unfold RL. repeat apply conj; PMK.sc. }
    split; [rewrite A21; f_equal; clear; lia|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [clear -Hsi Hi; lia|].
    apply (MI_out M M1 MIM MG1). intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia.
  - cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hge. rewrite !to_bv_add, slt_lit in Hge by (clear -Hsi Hi Fsig; lia).
    destruct (Z.ltb_spec (sigma + i + 3) 36) as [Hl|Hl]; [exfalso; clear -Hge; lia|].
    exists fx1, R1, M1, (sigma + i + 3). split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
    split. { unfold RL. repeat apply conj; PMK.sc. }
    split; [rewrite A21; f_equal; clear; lia|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [clear -Hsi Hi; lia|].
    apply (MI_out M M1 MIM MG1). intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia.
Qed.

Lemma sci_front (sciw : Z) fx R M :
  PNSDD.stP R0 S first sigma e z sd d R -> getr R (reg 13) = Z_to_bv 64 (sd - 1) -> getr R (reg 19) = Z_to_bv 64 sciw -> 0 <= sciw < 2 ^ 64 ->
  MI M -> L5.defined M (S - 216) 144 -> 0 <= z -> 1 <= sd -> z + sd <= 36 -> 0 <= d <= 9 ->
  exists fx' R' M' p, msteps RSEGS (st fx R 0x37d04 M) (st fx' R' 0x37dac M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ RL R' /\ getr R' (reg 21) = Z_to_bv 64 (first + p) /\ getr R' (reg 19) = Z_to_bv 64 sciw
    /\ getr R' (reg 9) = Z_to_bv 64 first /\ sigma + 1 <= p <= 37 /\ MI M'.
Proof.
  intros ((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & A10 & G11 & G20 & G21 & G12) G13 G19 Hsw MIM DF Hz0 Hsd Hz Hd.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (G10 : getr R (reg 10) = Z_to_bv 64 e) by (apply PNSDRN.to_bv_of_unsigned; exact A10).
  (let T := type of (PNSDOP.dkI1_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | 56%nat => d | 59%nat => sd - 1 | 52%nat => sciw | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI1_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | 56%nat => d | 59%nat => sd - 1 | 52%nat => sciw | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A10' & A21 & Hone & C0) | (MS1 & KS1 & A10' & A11 & A12 & A13 & A20 & A21 & C1 & Hmany & C0) ]).
  - rewrite Z.sub_0_r, Z.mod_small in Hone by (clear -Hsd Hz Hz0; lia).
    exists fx1, R1, M1, (sigma + 1). split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Fsig; lia. }
    split. { unfold RL. repeat apply conj; PMK.sc. }
    split; [rewrite A21; f_equal; clear; lia|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [clear -Fsig; lia|].
    apply (MI_out M M1 MIM MG1). intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Fsig; lia.
  - rewrite Z.sub_0_r, Z.mod_small in Hmany by (clear -Hsd Hz Hz0; lia).
    pose proof (MI_out M M1 MIM MG1 ltac:(intros a Ha Hn'; apply (FZ1 a Ha); unfold PNSDD.in_out in Hn'; clear -Hn' Fsig; lia)) as MI1.
    destruct (iloop sciw (Z.to_nat (sd - 1)) fx1 R1 M1 0 ltac:(clear -Hmany; lia) ltac:(clear -Hmany; lia) ltac:(clear -Fsig; lia) Hz Hz0 Hsw)
      as (fx2 & R2 & M2 & p & MS2 & MG2 & AG2 & RL2 & B21 & B19 & B9 & Hp & MI2).
    + unfold RL. repeat apply conj; PMK.sc.
    + exact A10'. + exact A11. + exact A12. + exact A13. + rewrite A20. f_equal. clear; lia. + PMK.sc. + PMK.sc. + PMK.sc. + exact MI1.
    + exact (L5.defined_grows M M1 _ _ MG1 DF).
    + exists fx2, R2, M2, p. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
      split. { intros a Ha Hn'. rewrite (AG2 a Ha Hn'). apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Fsig; lia. }
      split; [exact RL2|]. split; [exact B21|]. split; [exact B19|]. split; [exact B9|]. split; [clear -Hp Fsig; lia| exact MI2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fork fx R M :
  PNSDD.stP R0 S first sigma e z sd d R -> MI M -> 0 <= z -> 1 <= sd -> z + sd <= 36 -> 0 <= d <= 9 ->
  exists fx' R',
    (msteps RSEGS (st fx R 0x37c80 M) (st fx' R' 0x37d04 M) /\ PNSDD.stP R0 S first sigma e z sd d R' /\ getr R' (reg 13) = Z_to_bv 64 (sd - 1)
       /\ getr R' (reg 19) = Z_to_bv 64 (e + sd - 6177) /\ (e + sd - 6177 < -6 \/ 6177 <= e))
    \/ (msteps RSEGS (st fx R 0x37c80 M) (st fx' R' 0x37d74 M) /\ PNSDD.stQ R0 S first sigma e z sd R' /\ e <= 6175 /\ -6 <= e + sd - 6177)
    \/ (msteps RSEGS (st fx R 0x37c80 M) (st fx' R' 0x37ca8 M) /\ PNSDD.stQ R0 S first sigma e z sd R' /\ e = 6176).
Proof.
  intros ((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & A10 & G11 & G20 & G21 & G12) MIM Hz0 Hsd Hz Hd.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (G10 : getr R (reg 10) = Z_to_bv 64 e) by (apply PNSDRN.to_bv_of_unsigned; exact A10).
  (let T := type of (PNSDOP.dkO0_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | 56%nat => d | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkO0_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | 56%nat => d | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A13 & A14 & A19 & Hlt) | [ (MS1 & KS1 & A13 & A14 & A19 & Hbig & Hge) | [ (MS1 & KS1 & A12 & A13 & A14 & A19 & Hsm & He1 & Hge) | (MS1 & KS1 & A12 & A13 & A14 & A19 & Hsm & He1 & Hge) ]]]);
    (assert (EM : M1 = M) by (apply functional_extensionality; exact FW1)); subst M1; exists fx1, R1.
  - left. cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hlt.
    rewrite !to_bv_add, (to_bv_eqm 18446744073709551610 (-6)), slt_lit in Hlt by (first [reflexivity | clear -Fe Hsd Hz Hz0; lia]).
    destruct (Z.ltb_spec (e + sd + -6177) (-6)) as [Hl|Hl]; [| exfalso; clear -Hlt; lia].
    split; [exact MS1|]. split. { unfold PNSDD.stP, PNSDD.RB. rewrite (KS1 10%nat) by PMK.inl. repeat apply conj; PMK.sc. }
    split; [exact A13|]. split; [rewrite A19; f_equal; clear; lia|]. left. clear -Hl; lia.
  - left. split; [exact MS1|]. split. { unfold PNSDD.stP, PNSDD.RB. rewrite (KS1 10%nat) by PMK.inl. repeat apply conj; PMK.sc. }
    split; [exact A13|]. split; [rewrite A19; f_equal; clear; lia|]. right. exact Hbig.
  - right. left. cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hge.
    rewrite !to_bv_add, (to_bv_eqm 18446744073709551610 (-6)), slt_lit in Hge by (first [reflexivity | clear -Fe Hsd Hz Hz0; lia]).
    destruct (Z.ltb_spec (e + sd + -6177) (-6)) as [Hl|Hl]; [exfalso; clear -Hge; lia|].
    split; [exact MS1|]. split. { unfold PNSDD.stQ, PNSDD.RB. rewrite (KS1 10%nat) by PMK.inl. repeat apply conj; PMK.sc. }
    split; [| clear -Hl; lia]. clear -Hsm He1 Fe. assert (e / 32 < 193 -> e <= 6175) by (intros; lia). lia.
  - right. right. split; [exact MS1|]. split. { unfold PNSDD.stQ, PNSDD.RB. rewrite (KS1 10%nat) by PMK.inl. repeat apply conj; PMK.sc. }
    clear -Hsm He1 Fe. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RL_ (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 240) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 8) = Z_to_bv 64 (first + 42)
  /\ getr R (reg 24) = getr R0 (reg 24) /\ getr R (reg 25) = getr R0 (reg 25) /\ getr R (reg 26) = getr R0 (reg 26) /\ getr R (reg 27) = getr R0 (reg 27).
Lemma to_bv_mod a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. clear; lia. Qed.
(* [comment removed for export] *)
Lemma MI_xfer_gen M M' : MI M -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PNSDD.in_out first a -> ~ (S - 240 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> MI M'.
Proof.
  intros (W1 & W2 & IC & SV) MG FZ. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W1)|]. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W2)|].
  split. { apply (PMKP.clear_agree M M' 65536 749064); [|exact IC]. intros i Hi. apply FZ; [clear -Hi; lia| unfold PNSDD.in_out; clear -Hi Fimg; lia| clear -Hi FS; lia]. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ; [clear -Hi FS; lia| unfold PNSDD.in_out; clear -Hi FS Fdj; lia| clear -Hi FS; lia]| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sci_e (sci p : Z) fx R M :
  RL R -> getr R (reg 21) = Z_to_bv 64 (first + p) -> getr R (reg 19) = Z_to_bv 64 sci -> getr R (reg 9) = Z_to_bv 64 first ->
  - 2 ^ 62 <= sci < 2 ^ 62 -> sigma + 1 <= p <= 37 -> MI M ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (first + p <= a < first + p + 1) -> ~ (S - 240 <= a < S - 216) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M' /\ RL R' /\ getr R' (reg 19) = Z_to_bv 64 sci /\ getr R' (reg 9) = Z_to_bv 64 first /\ getr R' (reg 21) = Z_to_bv 64 (first + p)
    /\ L5.u64_at RSEGS M' (S - 240) 0 /\ L5.u64_at RSEGS M' (S - 232) 0 /\ L5.u64_at RSEGS M' (S - 224) 0
    /\ ((sci < 0 /\ msteps RSEGS (st fx R 0x37dac M) (st fx' R' 0x37dd0 M'))
        \/ (0 <= sci /\ msteps RSEGS (st fx R 0x37dac M) (st fx' R' 0x57350 M') /\ getr R' (reg 1) = Z_to_bv 64 0x37dd0
            /\ getr R' (reg 10) = Z_to_bv 64 (S - 240) /\ getr R' (reg 11) = Z_to_bv 64 43)).
Proof.
  intros (G2 & G3 & G4 & G8 & G18 & G24 & G25 & G26 & G27) G21 G19 G9 Hsci Hp MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof (Z.mod_pos_bound sci (2 ^ 64) ltac:(clear; lia)) as Hsw.
  assert (G19' : getr R (reg 19) = Z_to_bv 64 (sci mod 2 ^ 64)) by (rewrite to_bv_mod; exact G19).
  assert (G64 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 10))) as R64. unfold bv_modulus in R64. cbn in R64.
  assert (G65 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 11))) as R65. unfold bv_modulus in R65. cbn in R65.
  (let T := type of (PNSDOP.dkI3_conc fx R M (fun j => match j with 59%nat => p | 52%nat => sci mod 2 ^ 64 | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI3_conc fx R M (fun j => match j with 59%nat => p | 52%nat => sci mod 2 ^ 64 | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A10 & Hlt & C224 & C232 & C240 & CE) | (MS1 & KS1 & A1 & A10 & A11 & Hge & C224 & C232 & C240 & CE) ]);
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hlt || cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hge.
  - rewrite to_bv_mod, slt_lit in Hlt by (clear -Hsci; lia). destruct (Z.ltb_spec sci 0) as [Hl|Hl]; [| exfalso; clear -Hlt; lia].
    exists fx1, R1, M1. split; [exact MG1|]. split; [intros a Ha N1 N2; apply (FZ1 a Ha); [clear -N1; lia| clear -N2; lia]|].
    split. { apply (MI_xfer_gen M M1 MIM MG1). intros a Ha N1 N2. apply (FZ1 a Ha); [clear -N1 Hp Fsig; unfold PNSDD.in_out in N1; lia| clear -N2; lia]. }
    split. { unfold RL. repeat apply conj; PMK.sc. } split; [rewrite <- to_bv_mod; PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|].
    split; [exact C240|]. split; [exact C232|]. split; [exact C224|]. left. split; [exact Hl| exact MS1].
  - rewrite to_bv_mod, slt_lit in Hge by (clear -Hsci; lia). destruct (Z.ltb_spec sci 0) as [Hl|Hl]; [exfalso; clear -Hge; lia|].
    exists fx1, R1, M1. split; [exact MG1|]. split; [intros a Ha N1 N2; apply (FZ1 a Ha); [clear -N1; lia| clear -N2; lia]|].
    split. { apply (MI_xfer_gen M M1 MIM MG1). intros a Ha N1 N2. apply (FZ1 a Ha); [clear -N1 Hp Fsig; unfold PNSDD.in_out in N1; lia| clear -N2; lia]. }
    split. { unfold RL. repeat apply conj; PMK.sc. } split; [rewrite <- to_bv_mod; PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|].
    split; [exact C240|]. split; [exact C232|]. split; [exact C224|]. right. split; [exact Hl|]. split; [exact MS1|]. split; [exact A1|]. split; [exact A10| exact A11].
Qed.

(* [comment removed for export] *)
Lemma sci_fi (sci p : Z) fx R M :
  RL R -> getr R (reg 21) = Z_to_bv 64 (first + p) -> getr R (reg 19) = Z_to_bv 64 sci -> getr R (reg 9) = Z_to_bv 64 first -> sigma + 1 <= p <= 37 -> MI M ->
  exists fx' R', msteps RSEGS (st fx R 0x37dd0 M) (st fx' R' 0x38654 M)
    /\ RL R' /\ getr R' (reg 19) = Z_to_bv 64 sci /\ getr R' (reg 9) = Z_to_bv 64 first /\ getr R' (reg 21) = Z_to_bv 64 (first + p)
    /\ getr R' (reg 1) = Z_to_bv 64 0x37ddc /\ getr R' (reg 10) = Z_to_bv 64 sci /\ getr R' (reg 11) = Z_to_bv 64 (S - 240).
Proof.
  intros (G2 & G3 & G4 & G8 & G18 & G24 & G25 & G26 & G27) G21 G19 G9 Hp MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof (Z.mod_pos_bound sci (2 ^ 64) ltac:(clear; lia)) as Hsw.
  assert (G19' : getr R (reg 19) = Z_to_bv 64 (sci mod 2 ^ 64)) by (rewrite to_bv_mod; exact G19).
  assert (G64 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 10))) as R64. unfold bv_modulus in R64. cbn in R64.
  assert (G65 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 11))) as R65. unfold bv_modulus in R65. cbn in R65.
  (let T := type of (PNSDOP.dkI4_conc fx R M (fun j => match j with 59%nat => p | 52%nat => sci mod 2 ^ 64 | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI4_conc fx R M (fun j => match j with 59%nat => p | 52%nat => sci mod 2 ^ 64 | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & _ & MS1 & KS1 & A1 & A10 & A11).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  exists fx1, R1. split; [exact MS1|]. split. { unfold RL. repeat apply conj; PMK.sc. }
  split; [rewrite <- to_bv_mod; PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [exact A1|]. split; [rewrite <- to_bv_mod; exact A10| exact A11].
Qed.

(* [comment removed for export] *)
Lemma sci_cp (p n : Z) fx R M :
  RL R -> getr R (reg 21) = Z_to_bv 64 (first + p) -> getr R (reg 9) = Z_to_bv 64 first -> sigma + 1 <= p <= 37 -> 0 <= n <= 12 ->
  L5.u8_at RSEGS M (S - 240) (2 * n) -> MI M ->
  exists fx' R',
    (p + 1 + n < 42 /\ msteps RSEGS (st fx R 0x37ddc M) (st fx' R' 0xa9e98 M) /\ RL_ R' /\ getr R' (reg 1) = Z_to_bv 64 0x37e18
       /\ getr R' (reg 9) = Z_to_bv 64 (first + p + 1) /\ getr R' (reg 10) = Z_to_bv 64 (first + p + 1) /\ getr R' (reg 11) = Z_to_bv 64 (S - 239)
       /\ getr R' (reg 12) = Z_to_bv 64 n /\ getr R' (reg 18) = Z_to_bv 64 (first + p + 1 + n) /\ getr R' (reg 19) = Z_to_bv 64 0 /\ getr R' (reg 20) = Z_to_bv 64 n)
    \/ (42 <= p + 1 + n /\ msteps RSEGS (st fx R 0x37ddc M) (st fx' R' 0x37fe0 M) /\ PNSDD.stE R0 S (first + p + 1) R').
Proof.
  intros (G2 & G3 & G4 & G8 & G18 & G24 & G25 & G26 & G27) G21 G9 Hp Hn C0 MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (G19 : getr R (reg 19) = Z_to_bv 64 (bv_unsigned (getr R (reg 19)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 19))) as R19. unfold bv_modulus in R19. cbn in R19.
  assert (G64 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 10))) as R64. unfold bv_modulus in R64. cbn in R64.
  assert (G65 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 11))) as R65. unfold bv_modulus in R65. cbn in R65.
  (let T := type of (PNSDOP.dkI5_conc fx R M (fun j => match j with 59%nat => p | 72%nat => 2 * n | 52%nat => bv_unsigned (getr R (reg 19)) | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI5_conc fx R M (fun j => match j with 59%nat => p | 72%nat => 2 * n | 52%nat => bv_unsigned (getr R (reg 19)) | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  assert (EV : Z.land (2 * n) 1 = 0). { replace 1 with (Z.ones 1) by reflexivity. rewrite Z.land_ones by (clear; lia). change (2 ^ 1) with 2. rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (HF : 2 * n / 2 = n) by (rewrite Z.mul_comm; apply Z_div_mult; clear; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & _ & [ (MS1 & KS1 & A1 & A9 & A10 & A11 & A12 & A18 & A19 & A20 & Hroom & _) | [ (MS1 & KS1 & A9 & _ & _ & A12 & A18 & A19 & A20 & Hnoroom & _) | (MS1 & KS1 & _ & _ & _ & _ & _ & Hodd) ]]);
    (assert (EM : M1 = M) by (apply functional_extensionality; exact FW1)); subst M1; rewrite ?HF in *.
  - rewrite (Z.mod_small (p + n)), (Z.mod_small (first + (p + n))), (Z.mod_small (first + (p + n) + 1)), (Z.mod_small (first + 42)) in Hroom by (clear -Ffirst Hp Hn Fsig; lia).
    exists fx1, R1. left. split; [clear -Hroom; lia|]. split; [exact MS1|].
    split. { unfold RL_. repeat apply conj; PMK.sc. }
    split; [exact A1|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [exact A12|]. split; [PMK.sc|].
    split; [apply PNSDRN.to_bv_of_unsigned; rewrite A19; exact EV| exact A20].
  - rewrite (Z.mod_small (p + n)), (Z.mod_small (first + (p + n))), (Z.mod_small (first + (p + n) + 1)), (Z.mod_small (first + 42)) in Hnoroom by (clear -Ffirst Hp Hn Fsig; lia).
    exists fx1, R1. right. split; [clear -Hnoroom; lia|]. split; [exact MS1|]. unfold PNSDD.stE. repeat apply conj; PMK.sc.
  - exfalso. rewrite EV in Hodd. clear -Hodd. cbn in Hodd. lia.
Qed.

(* [comment removed for export] *)
Lemma sci_tail (p n : Z) fx R M :
  RL_ R -> getr R (reg 9) = Z_to_bv 64 (first + p + 1) -> getr R (reg 18) = Z_to_bv 64 (first + p + 1 + n) -> getr R (reg 19) = Z_to_bv 64 0 ->
  getr R (reg 20) = Z_to_bv 64 n -> sigma + 1 <= p <= 37 -> 0 <= n <= 12 -> MI M ->
  exists fx' R', msteps RSEGS (st fx R 0x37e18 M) (st fx' R' 0x37fe0 M) /\ PNSDD.stE R0 S (first + p + 1 + n) R'.
Proof.
  intros (G2 & G3 & G4 & G8 & G24 & G25 & G26 & G27) G9 G18 G19 G20 Hp Hn MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (G64 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 10))) as R64. unfold bv_modulus in R64. cbn in R64.
  assert (G65 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 11))) as R65. unfold bv_modulus in R65. cbn in R65.
  (let T := type of (PNSDOP.dkI6_conc fx R M (fun j => match j with 59%nat => p | 73%nat => 0 | 74%nat => n | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI6_conc fx R M (fun j => match j with 59%nat => p | 73%nat => 0 | 74%nat => n | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & _ & MS1 & KS1 & A9 & _).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  exists fx1, R1. split; [exact MS1|]. unfold PNSDD.stE. repeat apply conj; PMK.sc.
Qed.

End Out.
End Call.
End PNSDOUT.
