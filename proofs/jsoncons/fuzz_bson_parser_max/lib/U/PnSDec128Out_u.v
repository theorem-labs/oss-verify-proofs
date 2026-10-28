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
     AxSymExec3. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PnDecFacts PnMemW PnDecBv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSDec128Defs_u PnSDec128OP_u PnSDec128Rnd_u PnSDec128Rnd2_u.
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
Hypothesis Fimg : first + 42 <= 65536 \/ 962560 <= first.
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
  split. { apply (PMKP.clear_agree M M' 65536 754672); [|exact IC]. intros i Hi. apply FZ; [clear -Hi; lia|]. unfold PNSDD.in_out. clear -Hi Fimg; lia. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ; [clear -Hi FS; lia| unfold PNSDD.in_out; clear -Hi FS Fdj; lia]| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.

(* [comment removed for export] *)
Definition RL (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 256) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 8) = Z_to_bv 64 (first + 42) /\ getr R (reg 9) = Z_to_bv 64 (first + sigma)
  /\ getr R (reg 24) = getr R0 (reg 24) /\ getr R (reg 25) = getr R0 (reg 25) /\ getr R (reg 26) = getr R0 (reg 26) /\ getr R (reg 27) = getr R0 (reg 27).

(* [comment removed for export] *)
Lemma x16_low (s zz : Z) : 4096 <= s < 2 ^ 62 -> 0 <= zz <= 35 ->
  36 <= ((((((18446744073709551615 * s) mod 2 ^ 64) + ((18446744073709551612 * zz) mod 2 ^ 64)) mod 2 ^ 64) + 215) mod 2 ^ 64) / 4.
Proof.
  intros Hs Hz. change (2 ^ 64) with 18446744073709551616. change (2 ^ 62) with 4611686018427387904 in Hs.
  replace (18446744073709551615 * s) with ((18446744073709551616 - s) + (s - 1) * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (18446744073709551616 - s)) by lia.
  destruct (Z.eq_dec zz 0) as [->|Hz0].
  - rewrite Z.mul_0_r, Z.mod_0_l, Z.add_0_r by lia. rewrite (Z.mod_small (18446744073709551616 - s)) by lia.
    rewrite (Z.mod_small (18446744073709551616 - s + 215)) by lia. apply Z.div_le_lower_bound; lia.
  - replace (18446744073709551612 * zz) with ((18446744073709551616 - 4 * zz) + (zz - 1) * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (18446744073709551616 - 4 * zz)) by lia.
    replace (18446744073709551616 - s + (18446744073709551616 - 4 * zz)) with ((18446744073709551616 - s - 4 * zz) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite (Z.mod_small (18446744073709551616 - s - 4 * zz)) by lia.
    rewrite (Z.mod_small (18446744073709551616 - s - 4 * zz + 215)) by lia. apply Z.div_le_lower_bound; lia.
Qed.

(* [comment removed for export] *)
Lemma gloop (v : Z) (n : nat) : forall fx R M i,
  sd - i = Z.of_nat n -> 0 <= i < sd -> sigma + i <= 35 -> z + sd <= 36 -> 0 <= z ->
  RL R -> getr R (reg 18) = Z_to_bv 64 first -> getr R (reg 10) = Z_to_bv 64 i -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 (sigma + 1) ->
  getr R (reg 13) = Z_to_bv 64 (S - 216 + 4 * (z + i)) -> getr R (reg 14) = Z_to_bv 64 2 -> getr R (reg 15) = Z_to_bv 64 sd ->
  getr R (reg 16) = Z_to_bv 64 v -> 36 <= v < 2 ^ 64 -> getr R (reg 17) = Z_to_bv 64 36 -> MI M -> L5.defined M (S - 216) 144 ->
  exists fx' R' M' cnt, msteps RSEGS (st fx R 0x38d5c M) (st fx' R' 0x38f6c M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ PNSDD.stE R0 S (first + sigma + cnt) R' /\ i < cnt <= sd /\ sigma + cnt <= 36 /\ MI M'.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi Hsi Hz Hz0 RBR G18 G10 G11 G12 G13 G14 G15 G16 Hv G17 MIM DF; [exfalso; clear -Hn Hi; lia|].
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  destruct RBR as (G2 & G3 & G4 & G8 & G9 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDOP.dkG2_conc fx R M (fun j => match j with 57%nat => i | 55%nat => sd | 58%nat => z + i | 59%nat => v | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkG2_conc fx R M (fun j => match j with 57%nat => i | 55%nat => sd | 58%nat => z + i | 59%nat => v | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A5 & A10 & A13 & A19 & Hlt & Hmore) | [ (MS1 & KS1 & A5 & A19 & Hdone) | (MS1 & KS1 & A5 & A10 & A13 & A19 & Hge & Hmore) ]]).
  - (* [comment removed for export] *)
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hlt. rewrite !to_bv_add, slt_lit in Hlt by (clear -Hsi Hi Fsig; lia).
    destruct (Z.ltb_spec (sigma + i + 1) 36) as [Hl|Hl]; [| exfalso; clear -Hlt; lia].
    rewrite Z.mod_small in Hmore by (clear -Hi Hz Hz0; lia).
    pose proof (MI_out M M1 MIM MG1 ltac:(intros a Ha Hn'; apply (FZ1 a Ha); unfold PNSDD.in_out in Hn'; clear -Hn' Hi Hsi Fsig; lia)) as MI1.
    destruct (IH fx1 R1 M1 (i + 1) ltac:(clear -Hn; lia) ltac:(clear -Hi Hmore; lia) ltac:(clear -Hl; lia) Hz Hz0) as (fx2 & R2 & M2 & cnt & MS2 & MG2 & AG2 & SE2 & Hcnt & Hsc & MI2).
    + unfold RL. repeat apply conj; PMK.sc.
    + PMK.sc. + exact A10. + PMK.sc. + PMK.sc. + rewrite A13. f_equal. clear; lia. + PMK.sc. + PMK.sc. + PMK.sc. + exact Hv. + PMK.sc. + exact MI1. + exact (L5.defined_grows M M1 _ _ MG1 DF).
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
  PNSDD.stQ R0 S first sigma e z sd R -> getr R (reg 18) = Z_to_bv 64 first -> MI M -> L5.defined M (S - 216) 144 -> 0 <= z -> 1 <= sd -> z + sd <= 36 ->
  exists fx' R' M' cnt, msteps RSEGS (st fx R 0x38d24 M) (st fx' R' 0x38f6c M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ PNSDD.stE R0 S (first + sigma + cnt) R' /\ 1 <= cnt <= sd /\ sigma + cnt <= 36 /\ MI M'.
Proof.
  intros ((G2 & G3 & G4 & G8 & G9 & G24 & G25 & G26 & G27) & G15 & G13 & G12) G18 MIM DF Hz0 Hsd Hz.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDOP.dkG1_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkG1_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A10' & A11 & A12 & A14 & A15 & A16 & A17).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  assert (Hv : 36 <= bv_unsigned (getr R1 (reg 16)) < 2 ^ 64).
  { split; [rewrite A16; apply x16_low; clear -FS Hz0 Hz Hsd; lia|]. pose proof (bv_unsigned_in_range _ (getr R1 (reg 16))) as B. unfold bv_modulus in B. cbn in B. exact (proj2 B). }
  destruct (gloop (bv_unsigned (getr R1 (reg 16))) (Z.to_nat sd) fx1 R1 M 0 ltac:(clear -Hsd; lia) ltac:(clear -Hsd; lia) ltac:(clear -Fsig; lia) Hz Hz0)
    as (fx2 & R2 & M2 & cnt & MS2 & MG2 & AG2 & SE2 & Hcnt & Hsc & MI2).
  - unfold RL. repeat apply conj; PMK.sc.
  - PMK.sc. - exact A10'. - exact A11. - exact A12. - replace (z + 0) with z by (clear; lia). PMK.sc. - exact A14. - exact A15. - symmetry; apply Z_to_bv_bv_unsigned. - exact Hv. - exact A17. - exact MIM. - exact DF.
  - exists fx2, R2, M2, cnt. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG2|]. split; [exact AG2|]. split; [exact SE2|].
    split; [clear -Hcnt; lia|]. split; [exact Hsc| exact MI2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma epilogue fx R M ptr :
  PNSDD.stE R0 S ptr R -> MI M -> 0 <= ptr < 2 ^ 64 ->
  exists fx' R', msteps RSEGS (st fx R 0x38f6c M) (st fx' R' 0x38f98 M)
    /\ getr R' (reg 1) = Z_to_bv 64 r /\ getr R' (reg 2) = Z_to_bv 64 S /\ getr R' (reg 10) = Z_to_bv 64 ptr
    /\ (forall k, In k PNSDD.CS -> getr R' (reg k) = getr R0 (reg k)).
Proof.
  intros (G2 & G3 & G4 & G19 & G24 & G25 & G26 & G27) MIM Hptr.
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
  RL R -> getr R (reg 18) = Z_to_bv 64 first -> getr R (reg 5) = Z_to_bv 64 36 -> getr R (reg 10) = Z_to_bv 64 (first + sigma + 2) -> getr R (reg 11) = Z_to_bv 64 0 ->
  getr R (reg 12) = Z_to_bv 64 i -> getr R (reg 13) = Z_to_bv 64 (S - 216 + 4 * (z + 1 + i)) -> getr R (reg 14) = Z_to_bv 64 18446744073709551611 -> getr R (reg 15) = Z_to_bv 64 18446744073709551615 ->
  getr R (reg 16) = Z_to_bv 64 (sd - 1) -> getr R (reg 17) = Z_to_bv 64 (sigma + 3) -> getr R (reg 19) = Z_to_bv 64 sciw -> MI M -> L5.defined M (S - 216) 144 ->
  exists fx' R' M' p, msteps RSEGS (st fx R 0x38e08 M) (st fx' R' 0x38eac M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ RL R' /\ getr R' (reg 20) = Z_to_bv 64 (first + p) /\ getr R' (reg 19) = Z_to_bv 64 sciw
    /\ getr R' (reg 18) = Z_to_bv 64 first /\ sigma + 3 <= p <= 37 /\ MI M'.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi Hsi Hz Hz0 Hsw RLR G18 G5 G10 G11 G12 G13 G14 G15 G16 G17 G19 MIM DF; [exfalso; clear -Hn Hi; lia|].
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  destruct RLR as (G2 & G3 & G4 & G8 & G9 & G24 & G25 & G26 & G27).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDOP.dkI2_conc fx R M (fun j => match j with 57%nat => i | 59%nat => sd - 1 | 58%nat => z + 1 + i | 52%nat => sciw | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI2_conc fx R M (fun j => match j with 57%nat => i | 59%nat => sd - 1 | 58%nat => z + 1 + i | 52%nat => sciw | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A6 & A12 & A13 & A20 & Hlt & Hmore) | [ (MS1 & KS1 & A6 & A20 & Hdone) | (MS1 & KS1 & A6 & A12 & A13 & A20 & Hge & Hmore) ]]).
  - cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hlt. rewrite !to_bv_add, slt_lit in Hlt by (clear -Hsi Hi Fsig; lia).
    destruct (Z.ltb_spec (sigma + i + 3) 36) as [Hl|Hl]; [| exfalso; clear -Hlt; lia].
    rewrite Z.mod_small in Hmore by (clear -Hi Hz Hz0; lia).
    pose proof (MI_out M M1 MIM MG1 ltac:(intros a Ha Hn'; apply (FZ1 a Ha); unfold PNSDD.in_out in Hn'; clear -Hn' Hi Hsi Fsig; lia)) as MI1.
    destruct (IH fx1 R1 M1 (i + 1) ltac:(clear -Hn; lia) ltac:(clear -Hi Hmore; lia) ltac:(clear -Hl; lia) Hz Hz0 Hsw) as (fx2 & R2 & M2 & p & MS2 & MG2 & AG2 & RL2 & B21 & B19 & B9 & Hp & MI2).
    + unfold RL. repeat apply conj; PMK.sc.
    + PMK.sc. + PMK.sc. + PMK.sc. + PMK.sc. + exact A12. + rewrite A13. f_equal. clear; lia. + PMK.sc. + PMK.sc. + PMK.sc. + PMK.sc. + PMK.sc. + exact MI1. + exact (L5.defined_grows M M1 _ _ MG1 DF).
    + exists fx2, R2, M2, p. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
      split. { intros a Ha Hn'. rewrite (AG2 a Ha Hn'). apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
      split; [exact RL2|]. split; [exact B21|]. split; [exact B19|]. split; [exact B9|]. split; [exact Hp| exact MI2].
  - rewrite Z.mod_small in Hdone by (clear -Hi Hz Hz0; lia).
    exists fx1, R1, M1, (sigma + i + 3). split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
    split. { unfold RL. repeat apply conj; PMK.sc. }
    split; [rewrite A20; f_equal; clear; lia|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [clear -Hsi Hi; lia|].
    apply (MI_out M M1 MIM MG1). intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia.
  - cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hge. rewrite !to_bv_add, slt_lit in Hge by (clear -Hsi Hi Fsig; lia).
    destruct (Z.ltb_spec (sigma + i + 3) 36) as [Hl|Hl]; [exfalso; clear -Hge; lia|].
    exists fx1, R1, M1, (sigma + i + 3). split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia. }
    split. { unfold RL. repeat apply conj; PMK.sc. }
    split; [rewrite A20; f_equal; clear; lia|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [clear -Hsi Hi; lia|].
    apply (MI_out M M1 MIM MG1). intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Hi Hsi Fsig; lia.
Qed.

Lemma sci_front (sciw : Z) fx R M :
  PNSDD.RB R0 S first sigma R -> getr R (reg 10) = Z_to_bv 64 e -> getr R (reg 11) = Z_to_bv 64 (sd - 1) -> getr R (reg 12) = Z_to_bv 64 sd ->
  getr R (reg 13) = Z_to_bv 64 (S - 216 + 4 * z) -> getr R (reg 14) = Z_to_bv 64 (d + 48) -> getr R (reg 15) = Z_to_bv 64 (e - 6176) ->
  getr R (reg 19) = Z_to_bv 64 sciw -> 0 <= sciw < 2 ^ 64 ->
  MI M -> L5.defined M (S - 216) 144 -> 0 <= z -> 1 <= sd -> z + sd <= 36 -> 0 <= d <= 9 ->
  exists fx' R' M' p, msteps RSEGS (st fx R 0x38da4 M) (st fx' R' 0x38eac M') /\ mem_grows M M'
    /\ PNSDD.agree_but (PNSDD.in_out first) M M' /\ RL R' /\ getr R' (reg 20) = Z_to_bv 64 (first + p) /\ getr R' (reg 19) = Z_to_bv 64 sciw
    /\ getr R' (reg 18) = Z_to_bv 64 first /\ sigma + 1 <= p <= 37 /\ MI M'.
Proof.
  intros (G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) G10 G11 G12 G13 G14 G15 G19 Hsw MIM DF Hz0 Hsd Hz Hd.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDOP.dkI1_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | 56%nat => d | 59%nat => sd - 1 | 52%nat => sciw | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI1_conc fx R M (fun j => match j with 54%nat => z | 55%nat => sd | 56%nat => d | 59%nat => sd - 1 | 52%nat => sciw | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A10' & A20 & Hone & C0) | (MS1 & KS1 & A5 & A10' & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A20 & C1 & Hmany & C0) ]).
  - rewrite Z.sub_0_r, Z.mod_small in Hone by (clear -Hsd Hz Hz0; lia).
    exists fx1, R1, M1, (sigma + 1). split; [exact MS1|]. split; [exact MG1|].
    split. { intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Fsig; lia. }
    split. { unfold RL. repeat apply conj; PMK.sc. }
    split; [rewrite A20; f_equal; clear; lia|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [clear -Fsig; lia|].
    apply (MI_out M M1 MIM MG1). intros a Ha Hn'. apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Fsig; lia.
  - rewrite Z.sub_0_r, Z.mod_small in Hmany by (clear -Hsd Hz Hz0; lia).
    pose proof (MI_out M M1 MIM MG1 ltac:(intros a Ha Hn'; apply (FZ1 a Ha); unfold PNSDD.in_out in Hn'; clear -Hn' Fsig; lia)) as MI1.
    destruct (iloop sciw (Z.to_nat (sd - 1)) fx1 R1 M1 0 ltac:(clear -Hmany; lia) ltac:(clear -Hmany; lia) ltac:(clear -Fsig; lia) Hz Hz0 Hsw)
      as (fx2 & R2 & M2 & p & MS2 & MG2 & AG2 & RL2 & B21 & B19 & B9 & Hp & MI2).
    + unfold RL. repeat apply conj; PMK.sc.
    + PMK.sc. + exact A5. + exact A10'. + exact A11. + exact A12. + rewrite A13. f_equal. clear; lia. + exact A14. + exact A15. + exact A16. + exact A17. + PMK.sc. + exact MI1.
    + exact (L5.defined_grows M M1 _ _ MG1 DF).
    + exists fx2, R2, M2, p. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
      split. { intros a Ha Hn'. rewrite (AG2 a Ha Hn'). apply (FZ1 a Ha). unfold PNSDD.in_out in Hn'. clear -Hn' Fsig; lia. }
      split; [exact RL2|]. split; [exact B21|]. split; [exact B19|]. split; [exact B9|]. split; [clear -Hp Fsig; lia| exact MI2].
Qed.

Lemma and_lit (w : Z) : 0 <= w < 2 ^ 64 -> alu64 Instr.ALU_AND (Z_to_bv 64 w) (Z_to_bv 64 16383) = Z_to_bv 64 (Z.land w 16383).
Proof.
  intros Hw. apply bv_eq. rewrite AxSymExec3Sound.AX2S.u_and64, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small w) by lia. change (16383 mod 2 ^ 64) with 16383.
  assert (LB : 0 <= Z.land w 16383 < 2 ^ 64).
  { change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound w (2 ^ 14) ltac:(lia)). lia. }
  rewrite (Z.mod_small (Z.land w 16383)) by lia. reflexivity.
Qed.
Lemma eqm_shift (a b c : Z) : c = b + 2 ^ 64 -> (a + c) mod 2 ^ 64 = (a + b) mod 2 ^ 64.
Proof. intros ->. change (2 ^ 64) with 18446744073709551616. replace (a + (b + 18446744073709551616)) with ((a + b) + 1 * 18446744073709551616) by lia. apply Z.mod_add. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fork fx R M :
  PNSDD.stP R0 S first sigma e z sd d R -> MI M -> 0 <= z -> 1 <= sd -> z + sd <= 36 -> 0 <= d <= 9 ->
  exists fx' R',
    (msteps RSEGS (st fx R 0x38cec M) (st fx' R' 0x38da4 M) /\ PNSDD.RB R0 S first sigma R' /\ getr R' (reg 10) = Z_to_bv 64 e
       /\ getr R' (reg 11) = Z_to_bv 64 (sd - 1) /\ getr R' (reg 12) = Z_to_bv 64 sd /\ getr R' (reg 13) = Z_to_bv 64 (S - 216 + 4 * z)
       /\ getr R' (reg 14) = Z_to_bv 64 (d + 48) /\ getr R' (reg 15) = Z_to_bv 64 (e - 6176)
       /\ getr R' (reg 19) = Z_to_bv 64 (e + sd - 6177) /\ (e + sd - 6177 < -6 \/ 6177 <= e))
    \/ (msteps RSEGS (st fx R 0x38cec M) (st fx' R' 0x38e44 M) /\ PNSDD.stQ R0 S first sigma e z sd R' /\ e <= 6175 /\ -6 <= e + sd - 6177)
    \/ (msteps RSEGS (st fx R 0x38cec M) (st fx' R' 0x38d24 M) /\ PNSDD.stQ R0 S first sigma e z sd R' /\ getr R' (reg 18) = Z_to_bv 64 first /\ e = 6176).
Proof.
  intros (((G2 & G3 & G4 & G9 & G8 & G18 & G24 & G25 & G26 & G27) & (w & G10 & Hw & Hwe) & G11) & G13 & G12 & G14) MIM Hz0 Hsd Hz Hd.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  (let T := type of (PNSDOP.dkO0_conc fx R M (fun j => match j with 50%nat => w | 54%nat => z | 55%nat => sd | 56%nat => d | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkO0_conc fx R M (fun j => match j with 50%nat => w | 54%nat => z | 55%nat => sd | 56%nat => d | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A10 & A11 & A15 & A16 & A19 & Hlt) | [ (MS1 & KS1 & A10 & A11 & A15 & A16 & A19 & Hbig & Hge) | [ (MS1 & KS1 & A10 & A11 & A15 & A16 & A19 & Hsm & He1 & Hge) | (MS1 & KS1 & A10 & A11 & A15 & A16 & A19 & Hsm & He1 & Hge) ]]]);
    (assert (EM : M1 = M) by (apply functional_extensionality; exact FW1)); subst M1; exists fx1, R1; rewrite Hwe in *;
    (assert (X15 : getr R1 (reg 15) = Z_to_bv 64 (e - 6176))
       by (rewrite (PNSDRN.to_bv_of_unsigned _ _ A15); apply to_bv_eqm; rewrite Z.mod_mod by lia; replace (e - 6176) with (e + (-6176)) by lia; apply eqm_shift; reflexivity));
    (assert (X19 : getr R1 (reg 19) = Z_to_bv 64 (e + sd - 6177))
       by (rewrite (PNSDRN.to_bv_of_unsigned _ _ A19); apply to_bv_eqm; rewrite Z.mod_mod, Z.add_mod_idemp_l by lia;
           replace (e + sd - 6177) with ((sd + e) + (-6177)) by lia; apply eqm_shift; reflexivity)).
  - left. split; [exact MS1|]. split. { unfold PNSDD.RB. repeat apply conj; PMK.sc. }
    split; [exact (PNSDRN.to_bv_of_unsigned _ _ A10)|]. split; [exact A11|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [exact X15|]. split; [exact X19|].
    cbn [AX2.edenot AX2.ev] in Hlt. rewrite (and_lit w ltac:(clear -Hw; lia)), Hwe in Hlt. cbn [alu64 alu32 alu mul_div] in Hlt.
    rewrite !to_bv_add, (to_bv_eqm 18446744073709551610 (-6)), slt_lit in Hlt by (first [reflexivity | clear -Fe Hsd Hz Hz0; lia]).
    destruct (Z.ltb_spec (sd + e + -6177) (-6)) as [Hl|Hl]; [| exfalso; clear -Hlt; lia]. left. clear -Hl; lia.
  - left. split; [exact MS1|]. split. { unfold PNSDD.RB. repeat apply conj; PMK.sc. }
    split; [exact (PNSDRN.to_bv_of_unsigned _ _ A10)|]. split; [exact A11|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [exact X15|]. split; [exact X19|].
    right. exact Hbig.
  - right. left.
    cbn [AX2.edenot AX2.ev] in Hge. rewrite (and_lit w ltac:(clear -Hw; lia)), Hwe in Hge. cbn [alu64 alu32 alu mul_div] in Hge.
    rewrite !to_bv_add, (to_bv_eqm 18446744073709551610 (-6)), slt_lit in Hge by (first [reflexivity | clear -Fe Hsd Hz Hz0; lia]).
    destruct (Z.ltb_spec (sd + e + -6177) (-6)) as [Hl|Hl]; [exfalso; clear -Hge; lia|].
    split; [exact MS1|]. split. { unfold PNSDD.stQ. split; [repeat apply conj; PMK.sc|]. split; [exact X15|]. split; PMK.sc. }
    split; [| clear -Hl; lia]. clear -Hsm He1 Fe. assert (e / 32 < 193 -> e <= 6175) by (intros; lia). lia.
  - right. right. split; [exact MS1|]. split. { unfold PNSDD.stQ. split; [repeat apply conj; PMK.sc|]. split; [exact X15|]. split; PMK.sc. }
    split; [PMK.sc|]. clear -Hsm He1 Fe. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RL_ (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 256) /\ getr R (reg 3) = getr R0 (reg 3) /\ getr R (reg 4) = getr R0 (reg 4)
  /\ getr R (reg 8) = Z_to_bv 64 (first + 42)
  /\ getr R (reg 24) = getr R0 (reg 24) /\ getr R (reg 25) = getr R0 (reg 25) /\ getr R (reg 26) = getr R0 (reg 26) /\ getr R (reg 27) = getr R0 (reg 27).
Lemma to_bv_mod a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. clear; lia. Qed.
(* [comment removed for export] *)
Lemma MI_xfer_gen M M' : MI M -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PNSDD.in_out first a -> ~ (S - 256 <= a < S - 72) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> MI M'.
Proof.
  intros (W1 & W2 & IC & SV) MG FZ. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W1)|]. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W2)|].
  split. { apply (PMKP.clear_agree M M' 65536 754672); [|exact IC]. intros i Hi. apply FZ; [clear -Hi; lia| unfold PNSDD.in_out; clear -Hi Fimg; lia| clear -Hi FS; lia]. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ; [clear -Hi FS; lia| unfold PNSDD.in_out; clear -Hi FS Fdj; lia| clear -Hi FS; lia]| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sci_e (sci p : Z) fx R M :
  RL R -> getr R (reg 20) = Z_to_bv 64 (first + p) -> getr R (reg 19) = Z_to_bv 64 sci -> getr R (reg 18) = Z_to_bv 64 first ->
  - 2 ^ 62 <= sci < 2 ^ 62 -> sigma + 1 <= p <= 37 -> MI M ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (first + p <= a < first + p + 1) -> ~ (S - 256 <= a < S - 232) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ MI M' /\ RL R' /\ getr R' (reg 19) = Z_to_bv 64 sci /\ getr R' (reg 18) = Z_to_bv 64 first /\ getr R' (reg 20) = Z_to_bv 64 (first + p)
    /\ L5.u64_at RSEGS M' (S - 256) 0 /\ L5.u64_at RSEGS M' (S - 248) 0 /\ L5.u64_at RSEGS M' (S - 240) 0
    /\ ((sci < 0 /\ msteps RSEGS (st fx R 0x38eac M) (st fx' R' 0x38ed8 M'))
        \/ (0 <= sci /\ msteps RSEGS (st fx R 0x38eac M) (st fx' R' 0x58938 M') /\ getr R' (reg 1) = Z_to_bv 64 0x38ed8
            /\ getr R' (reg 10) = Z_to_bv 64 (S - 256) /\ getr R' (reg 11) = Z_to_bv 64 43)).
Proof.
  intros (G2 & G3 & G4 & G8 & G9 & G24 & G25 & G26 & G27) G20 G19 G18 Hsci Hp MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof (Z.mod_pos_bound sci (2 ^ 64) ltac:(clear; lia)) as Hsw.
  assert (G19' : getr R (reg 19) = Z_to_bv 64 (sci mod 2 ^ 64)) by (rewrite to_bv_mod; exact G19).
  assert (G64 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 10))) as R64. unfold bv_modulus in R64. cbn in R64.
  assert (G65 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 11))) as R65. unfold bv_modulus in R65. cbn in R65.
  (let T := type of (PNSDOP.dkI3_conc fx R M (fun j => match j with 59%nat => p | 52%nat => sci mod 2 ^ 64 | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI3_conc fx R M (fun j => match j with 59%nat => p | 52%nat => sci mod 2 ^ 64 | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A10 & Hlt & C240 & C248 & C256 & CE) | (MS1 & KS1 & A1 & A10 & A11 & Hge & C240 & C248 & C256 & CE) ]);
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hlt || cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in Hge.
  - rewrite to_bv_mod, slt_lit in Hlt by (clear -Hsci; lia). destruct (Z.ltb_spec sci 0) as [Hl|Hl]; [| exfalso; clear -Hlt; lia].
    exists fx1, R1, M1. split; [exact MG1|]. split; [intros a Ha N1 N2; apply (FZ1 a Ha); [clear -N1; lia| clear -N2; lia]|].
    split. { apply (MI_xfer_gen M M1 MIM MG1). intros a Ha N1 N2. apply (FZ1 a Ha); [clear -N1 Hp Fsig; unfold PNSDD.in_out in N1; lia| clear -N2; lia]. }
    split. { unfold RL. repeat apply conj; PMK.sc. } split; [rewrite <- to_bv_mod; PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|].
    split; [exact C256|]. split; [exact C248|]. split; [exact C240|]. left. split; [exact Hl| exact MS1].
  - rewrite to_bv_mod, slt_lit in Hge by (clear -Hsci; lia). destruct (Z.ltb_spec sci 0) as [Hl|Hl]; [exfalso; clear -Hge; lia|].
    exists fx1, R1, M1. split; [exact MG1|]. split; [intros a Ha N1 N2; apply (FZ1 a Ha); [clear -N1; lia| clear -N2; lia]|].
    split. { apply (MI_xfer_gen M M1 MIM MG1). intros a Ha N1 N2. apply (FZ1 a Ha); [clear -N1 Hp Fsig; unfold PNSDD.in_out in N1; lia| clear -N2; lia]. }
    split. { unfold RL. repeat apply conj; PMK.sc. } split; [rewrite <- to_bv_mod; PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|].
    split; [exact C256|]. split; [exact C248|]. split; [exact C240|]. right. split; [exact Hl|]. split; [exact MS1|]. split; [exact A1|]. split; [exact A10| exact A11].
Qed.

(* [comment removed for export] *)
Lemma sci_fi (sci p : Z) fx R M :
  RL R -> getr R (reg 20) = Z_to_bv 64 (first + p) -> getr R (reg 19) = Z_to_bv 64 sci -> getr R (reg 18) = Z_to_bv 64 first -> sigma + 1 <= p <= 37 -> MI M ->
  exists fx' R', msteps RSEGS (st fx R 0x38ed8 M) (st fx' R' 0x39a24 M)
    /\ RL R' /\ getr R' (reg 19) = Z_to_bv 64 sci /\ getr R' (reg 18) = Z_to_bv 64 first /\ getr R' (reg 20) = Z_to_bv 64 (first + p)
    /\ getr R' (reg 1) = Z_to_bv 64 0x38ee4 /\ getr R' (reg 10) = Z_to_bv 64 sci /\ getr R' (reg 11) = Z_to_bv 64 (S - 256).
Proof.
  intros (G2 & G3 & G4 & G8 & G9 & G24 & G25 & G26 & G27) G20 G19 G18 Hp MIM.
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
  RL R -> getr R (reg 20) = Z_to_bv 64 (first + p) -> getr R (reg 18) = Z_to_bv 64 first -> sigma + 1 <= p <= 37 -> 0 <= n <= 12 ->
  L5.u8_at RSEGS M (S - 256) (2 * n) -> MI M ->
  exists fx' R',
    (p + 1 + n < 42 /\ msteps RSEGS (st fx R 0x38ee4 M) (st fx' R' 0xab480 M) /\ RL_ R' /\ getr R' (reg 1) = Z_to_bv 64 0x38f28
       /\ getr R' (reg 9) = Z_to_bv 64 n /\ getr R' (reg 10) = Z_to_bv 64 (first + p + 1) /\ getr R' (reg 11) = Z_to_bv 64 (S - 255)
       /\ getr R' (reg 12) = Z_to_bv 64 n /\ getr R' (reg 18) = Z_to_bv 64 0 /\ getr R' (reg 19) = Z_to_bv 64 (first + p + 1) /\ getr R' (reg 20) = Z_to_bv 64 (first + p + 1 + n)
       /\ getr R' (reg 21) = Z_to_bv 64 (- first - p - 2))
    \/ (42 <= p + 1 + n /\ msteps RSEGS (st fx R 0x38ee4 M) (st fx' R' 0x38f6c M) /\ PNSDD.stE R0 S (first + p + 1) R').
Proof.
  intros (G2 & G3 & G4 & G8 & G9 & G24 & G25 & G26 & G27) G20 G18 Hp Hn C0 MIM.
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
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & _ & [ (MS1 & KS1 & A1 & A9 & A10 & A11 & A12 & A18 & A19 & A20 & A21 & Hroom & _) | [ (MS1 & KS1 & A9 & _ & _ & A18 & A19 & A20 & A21 & Hnoroom & _) | (MS1 & KS1 & _ & _ & _ & _ & Hodd) ]]);
    (assert (EM : M1 = M) by (apply functional_extensionality; exact FW1)); subst M1; rewrite ?HF in *.
  - rewrite (Z.mod_small (p + n)), (Z.mod_small (first + (p + n))), (Z.mod_small (first + (p + n) + 1)), (Z.mod_small (first + 42)) in Hroom by (clear -Ffirst Hp Hn Fsig; lia).
    exists fx1, R1. left. split; [clear -Hroom; lia|]. split; [exact MS1|].
    split. { unfold RL_. repeat apply conj; PMK.sc. }
    split; [exact A1|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [PMK.sc|]. split; [exact A12|]. split; [apply PNSDRN.to_bv_of_unsigned; rewrite A18; exact EV|].
    split; [PMK.sc|]. split; [PMK.sc| PMK.sc].
  - rewrite (Z.mod_small (p + n)), (Z.mod_small (first + (p + n))), (Z.mod_small (first + (p + n) + 1)), (Z.mod_small (first + 42)) in Hnoroom by (clear -Ffirst Hp Hn Fsig; lia).
    exists fx1, R1. right. split; [clear -Hnoroom; lia|]. split; [exact MS1|]. unfold PNSDD.stE. repeat apply conj; PMK.sc.
  - exfalso. rewrite EV in Hodd. clear -Hodd. cbn in Hodd. lia.
Qed.

(* [comment removed for export] *)
Lemma sci_tail (p n : Z) fx R M :
  RL_ R -> getr R (reg 9) = Z_to_bv 64 n -> getr R (reg 18) = Z_to_bv 64 0 -> getr R (reg 19) = Z_to_bv 64 (first + p + 1) ->
  getr R (reg 20) = Z_to_bv 64 (first + p + 1 + n) -> getr R (reg 21) = Z_to_bv 64 (- first - p - 2) -> sigma + 1 <= p <= 37 -> 0 <= n <= 12 -> MI M ->
  exists fx' R', msteps RSEGS (st fx R 0x38f28 M) (st fx' R' 0x38f6c M) /\ PNSDD.stE R0 S (first + p + 1 + n) R'.
Proof.
  intros (G2 & G3 & G4 & G8 & G24 & G25 & G26 & G27) G9 G18 G19 G20 G21 Hp Hn MIM.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (G64 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 10))) as R64. unfold bv_modulus in R64. cbn in R64.
  assert (G65 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bv_unsigned_in_range _ (getr R (reg 11))) as R65. unfold bv_modulus in R65. cbn in R65.
  (let T := type of (PNSDOP.dkI6_conc fx R M (fun j => match j with 59%nat => p | 73%nat => 0 | 74%nat => n | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDOP.dkI6_conc fx R M (fun j => match j with 59%nat => p | 73%nat => 0 | 74%nat => n | 70%nat => bv_unsigned (getr R (reg 10)) | 71%nat => bv_unsigned (getr R (reg 11)) | _ => VV 0 j end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & _ & MS1 & KS1 & _ & _ & A19).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  exists fx1, R1. split; [exact MS1|]. unfold PNSDD.stE. repeat apply conj; PMK.sc.
Qed.

End Out.
End Call.
End PNSDOUT.
