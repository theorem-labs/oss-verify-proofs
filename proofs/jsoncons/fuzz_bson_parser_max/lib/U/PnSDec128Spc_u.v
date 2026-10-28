(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk L5Defs L5Core L5CoreKit
     AxSymExec3. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmModel PmModelFacts PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnStatics. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSrcSMemmove_u PnSDec128Defs_u PnSDec128SP_u
     Bs0_code_37f10_37f14_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDSPC.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Abbreviation AN := PnLayoutS_u.NADDR_S.

(* [comment removed for export] *)
Lemma comb_31 h : 0 <= h -> ((((8589934592 * h) mod 2 ^ 64) / 576460752303423488 - 31) mod 2 ^ 64) < 1 ->
  ((8589934592 * h) mod 2 ^ 64) / 576460752303423488 = 31.
Proof.
  intros Hh H. set (c := ((8589934592 * h) mod 2 ^ 64) / 576460752303423488) in *.
  assert (Hc : 0 <= c < 32).
  { subst c. pose proof (Z.mod_pos_bound (8589934592 * h) (2 ^ 64) ltac:(clear; lia)) as B.
    split; [apply Z.div_pos; clear -B; lia| apply Z.div_lt_upper_bound; clear -B; lia]. }
  destruct (Z.eq_dec c 31) as [E|NE]; [exact E| exfalso].
  replace (c - 31) with ((c - 31 + 2 ^ 64) + (-1) * 2 ^ 64) in H by (clear; lia). rewrite Z.mod_add, Z.mod_small in H by (clear -Hc NE; lia).
  clear -H Hc NE. lia.
Qed.
Lemma to_bv_of_unsigned (b : bv 64) z : bv_unsigned b = z -> b = Z_to_bv 64 z.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* [comment removed for export] *)
Lemma e_nc_range h : 0 <= h -> 0 <= Z.land (h / 32768) 16383 <= 16383.
Proof.
  intros Hh. change 16383 with (Z.ones 14). rewrite Z.land_ones by (clear; lia).
  pose proof (Z.mod_pos_bound (h / 32768) (2 ^ 14) ltac:(clear; lia)). change (Z.ones 14) with (2 ^ 14 - 1). clear -H. lia.
Qed.
Lemma msb_nc h : 0 <= h -> 7 < (((131072 * h) mod 2 ^ 64) / 9223372036854775808 + 8) mod 2 ^ 64.
Proof.
  intros Hh. pose proof (Z.mod_pos_bound (131072 * h) (2 ^ 64) ltac:(clear; lia)) as B.
  assert (Hb : 0 <= ((131072 * h) mod 2 ^ 64) / 9223372036854775808 <= 1).
  { split; [apply Z.div_pos; clear -B; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; clear -B; lia. }
  rewrite Z.mod_small by (clear -Hb; lia). clear -Hb. lia.
Qed.

Section Spc.
Variables (R0 : bvmap 5 word) (S first sigma vp hi lo r : Z).
Let u8 := bv_unsigned (getr R0 (reg 8)).
Let u9 := bv_unsigned (getr R0 (reg 9)).
Let u18 := bv_unsigned (getr R0 (reg 18)).
Let u19 := bv_unsigned (getr R0 (reg 19)).
Let u20 := bv_unsigned (getr R0 (reg 20)).
Let u21 := bv_unsigned (getr R0 (reg 21)).
Let u22 := bv_unsigned (getr R0 (reg 22)).
Let u23 := bv_unsigned (getr R0 (reg 23)).
Hypothesis FS : 140735332483408 <= S <= 140737488355328.
Hypothesis F16 : S mod 16 = 0.
Hypothesis Ffirst : 4096 <= first <= 140737488355286.
Hypothesis Fimg : first + 42 <= 65536 \/ 962560 <= first.      (* [comment removed for export] *)
Hypothesis Fdj : S - 336 + 336 <= first \/ first + 42 <= S - 336.
Hypothesis Fsig : 0 <= sigma <= 1.
Hypothesis Fhi : 0 <= hi < 2 ^ 64.
Hypothesis Flo : 0 <= lo < 2 ^ 64.
Hypothesis Fvp : 4096 <= vp <= 140737488355312.
Hypothesis Fr : 0 <= r < 2 ^ 47.
Hypothesis RAok : L5.ra_ok r.

Abbreviation MI := (PNSDD.MI R0 S first r).
(* [comment removed for export] *)
Definition VV (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 35%nat => vp | 36%nat => lo | 37%nat => hi | 38%nat => sigma | 39%nat => hi / 2 ^ 32
  | 60%nat => r | 61%nat => u8 | 62%nat => u9 | 63%nat => u18 | 64%nat => u19 | 65%nat => u20 | 66%nat => u21 | 67%nat => u22 | 68%nat => u23 | _ => 0 end.

Lemma ufacts : 0 <= u8 < 2 ^ 64 /\ 0 <= u9 < 2 ^ 64 /\ 0 <= u18 < 2 ^ 64 /\ 0 <= u19 < 2 ^ 64 /\ 0 <= u20 < 2 ^ 64 /\ 0 <= u21 < 2 ^ 64
  /\ 0 <= u22 < 2 ^ 64 /\ 0 <= u23 < 2 ^ 64 /\ 0 <= hi / 2 ^ 32 <= 4294967295.
Proof.
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 8))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 9))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 18))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 19))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 20))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 21))).
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 22))). pose proof (bv_unsigned_in_range _ (getr R0 (reg 23))).
  assert (hi / 2 ^ 32 < 2 ^ 32) by (apply Z.div_lt_upper_bound; clear -Fhi; lia).
  assert (0 <= hi / 2 ^ 32) by (apply Z.div_pos; clear -Fhi; lia).
  unfold bv_modulus in *. subst u8 u9 u18 u19 u20 u21 u22 u23. repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma MI_out M M' (P : Z -> Prop) : MI M -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, P a -> first <= a < first + 42) -> MI M'.
Proof.
  intros (W1 & W2 & IC & SV) MG FZ PF. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W1)|]. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W2)|].
  assert (FZ' : forall a, 0 <= a < 2 ^ 64 -> ~ (first <= a < first + 42) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FZ; [exact Ha|]. intros X. apply N. apply PF. exact X. }
  split. { apply (PMKP.clear_agree M M' 65536 754672); [|exact IC]. intros i Hi. apply FZ'; clear -Hi FS Ffirst Fimg; lia. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ'; clear -Hi FS Fdj; lia| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.
(* [comment removed for export] *)
Lemma bdec_out M M' (P : Z -> Prop) : PNST.bdec_ok RSEGS AN M true -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, P a -> first <= a < first + 42) -> PNST.bdec_ok RSEGS AN M' true.
Proof.
  intros (G1 & G2 & (BI & DI) & (BN & DN)) MG FZ PF. unfold PNST.bdec_ok, PNST.sso_lit in *. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.mul Z.add] in *.
  assert (AGR : forall a n, 0xc8588 <= a -> a + n <= 0xc85c8 -> L5C.agree_on M M' a n).
  { intros a n Ha Hn i Hi. apply FZ; [clear -Hi Ha Hn; lia|]. intros X. apply PF in X. clear -X Hi Ha Hn Ffirst Fimg. lia. }
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact G1]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact G2]|].
  split; [split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact BI]| exact (L5.defined_grows M M' _ _ MG DI)]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact BN]| exact (L5.defined_grows M M' _ _ MG DN)].
Qed.
Lemma MI_fr M M' : MI M -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 232 <= a < S - 216) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> MI M'.
Proof.
  intros (W1 & W2 & IC & SV) MG FZ. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W1)|]. split; [exact (L5.writable_grows RSEGS M M' _ _ MG W2)|].
  split. { apply (PMKP.clear_agree M M' 65536 754672); [|exact IC]. intros i Hi. apply FZ; clear -Hi FS; lia. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ; clear -Hi FS; lia| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.
Lemma bdec_fr M M' : PNST.bdec_ok RSEGS AN M true -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 232 <= a < S - 216) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PNST.bdec_ok RSEGS AN M' true.
Proof.
  intros (G1 & G2 & (BI & DI) & (BN & DN)) MG FZ. unfold PNST.bdec_ok, PNST.sso_lit in *. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.mul Z.add] in *.
  assert (AGR : forall a n, 0xc8588 <= a -> a + n <= 0xc85c8 -> L5C.agree_on M M' a n).
  { intros a n Ha Hn i Hi. apply FZ; clear -Hi Ha Hn FS; lia. }
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact G1]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact G2]|].
  split; [split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact BI]| exact (L5.defined_grows M M' _ _ MG DI)]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact BN]| exact (L5.defined_grows M M' _ _ MG DN)].
Qed.

(* [comment removed for export] *)
Lemma ret_step fx R M : getr R (reg 1) = Z_to_bv 64 r -> msteps RSEGS (st fx R 0x38f98 M) (st fx R r M).
Proof. intros H1. destruct RAok as (_ & E). apply (PMK.ret_to RSEGS fx R M 0x38f98 W_37fb4 r F_37fb4 eq_refl D_37fb4 H1 Fr E). Qed.

Lemma dkN_exitZ R M (R2 : bvmap 5 word) M2 :
  PNSDD.stX R0 S first sigma vp hi lo R -> MI M -> PNST.bdec_ok RSEGS AN M true -> mem_grows M M2 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 232 <= i < S - 232 + 16) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall k, In k [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 27]%nat -> getr R2 (reg k) = getr R (reg k)) ->
  getr R2 (reg 10) = Z_to_bv 64 (hi / 2 ^ 32 / 32768) -> getr R2 (reg 11) = Z_to_bv 64 16383 ->
  bv_unsigned (getr R2 (reg 14)) = (PNSDD.msb hi + 8) mod 2 ^ 64 -> getr R2 (reg 15) = Z_to_bv 64 (lo / 2 ^ 32) ->
  getr R2 (reg 17) = Z_to_bv 64 (S - 232) ->
  L5.u32_at RSEGS M2 (S - 220) lo -> L5.u32_at RSEGS M2 (S - 224) (lo / 2 ^ 32) -> L5.u32_at RSEGS M2 (S - 228) hi ->
  L5.u32_at RSEGS M2 (S - 232) (PNSDD.cN232 hi) ->
  PNSDD.stNZ R0 S first sigma vp hi lo R2 /\ PNSDD.cN S hi lo M2 /\ MI M2 /\ PNST.bdec_ok RSEGS AN M2 true
  /\ PNSDD.agree_but (fun a => S - 232 <= a < S - 216) M M2.
Proof.
  intros ((X2 & X3 & X4 & X9 & X8 & X18 & X24 & X25 & X26 & X27) & X19 & _) MIM DEC MG FZ KS Y10 Y11 Y14 Y15 Y17 C1 C2 C3 C4.
  assert (FZ' : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 232 <= a < S - 216) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FZ; [exact Ha|]. intros X. apply N. clear -X. lia. }
  pose proof (PNSDD.msb_range hi ltac:(clear -Fhi; lia)) as MB.
  split; [| split; [| split; [| split]]].
  - unfold PNSDD.stNZ, PNSDD.RB.
    repeat apply conj; first [ exact Y10 | exact Y11 | exact Y15 | exact Y17
                             | rewrite KS by (cbn; tauto); first [exact X2 | exact X3 | exact X4 | exact X9 | exact X8 | exact X18 | exact X24 | exact X25 | exact X26 | exact X27 | exact X19]
                             | idtac ].
    rewrite (to_bv_of_unsigned _ _ Y14). f_equal. apply Z.mod_small. clear -MB. lia.
  - split; [exact C1| split; [exact C2| split; [exact C3| exact C4]]].
  - exact (MI_fr M M2 MIM MG FZ').
  - exact (bdec_fr M M2 DEC MG FZ').
  - exact FZ'.
Qed.

Lemma dkN_exitH R M (R2 : bvmap 5 word) M2 :
  PNSDD.stX R0 S first sigma vp hi lo R -> MI M -> PNST.bdec_ok RSEGS AN M true -> mem_grows M M2 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 232 <= i < S - 232 + 16) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (forall k, In k [2; 3; 4; 8; 9; 18; 24; 25; 26; 27]%nat -> getr R2 (reg k) = getr R (reg k)) ->
  getr R2 (reg 5) = Z_to_bv 64 18446744073709551607 -> getr R2 (reg 6) = Z_to_bv 64 18446744073709551603 ->
  getr R2 (reg 7) = Z_to_bv 64 19342813113834067 -> getr R2 (reg 10) = Z_to_bv 64 (hi / 2 ^ 32 / 32768) ->
  getr R2 (reg 11) = Z_to_bv 64 16383 -> getr R2 (reg 12) = Z_to_bv 64 0 -> getr R2 (reg 13) = Z_to_bv 64 (S - 240) ->
  getr R2 (reg 14) = Z_to_bv 64 (S - 76) -> getr R2 (reg 15) = Z_to_bv 64 18446744073709551580 ->
  getr R2 (reg 16) = Z_to_bv 64 (S - 216) -> getr R2 (reg 17) = Z_to_bv 64 (S - 256) -> getr R2 (reg 19) = Z_to_bv 64 3 ->
  getr R2 (reg 28) = Z_to_bv 64 1000000000 -> getr R2 (reg 29) = Z_to_bv 64 14757395259826634752 -> getr R2 (reg 30) = Z_to_bv 64 10 ->
  L5.u32_at RSEGS M2 (S - 220) lo -> L5.u32_at RSEGS M2 (S - 224) (lo / 2 ^ 32) -> L5.u32_at RSEGS M2 (S - 228) hi ->
  L5.u32_at RSEGS M2 (S - 232) (PNSDD.cN232 hi) ->
  PNSDD.stNH R0 S first sigma R2 /\ getr R2 (reg 10) = Z_to_bv 64 (hi / 2 ^ 32 / 32768) /\ PNSDD.cN S hi lo M2 /\ MI M2 /\ PNST.bdec_ok RSEGS AN M2 true
  /\ PNSDD.agree_but (fun a => S - 232 <= a < S - 216) M M2.
Proof.
  intros ((X2 & X3 & X4 & X9 & X8 & X18 & X24 & X25 & X26 & X27) & _) MIM DEC MG FZ KS Y5 Y6 Y7 Y10 Y11 Y12 Y13 Y14 Y15 Y16 Y17 Y19 Y28 Y29 Y30 C1 C2 C3 C4.
  assert (FZ' : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 232 <= a < S - 216) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FZ; [exact Ha|]. intros X. apply N. clear -X. lia. }
  split; [| split; [| split; [| split; [| split]]]].
  - unfold PNSDD.stNH, PNSDD.RB.
    repeat apply conj; first [ assumption
                             | rewrite KS by (cbn; tauto); first [exact X2 | exact X3 | exact X4 | exact X9 | exact X8 | exact X18 | exact X24 | exact X25 | exact X26 | exact X27] ].
  - exact Y10.
  - split; [exact C1| split; [exact C2| split; [exact C3| exact C4]]].
  - exact (MI_fr M M2 MIM MG FZ').
  - exact (bdec_fr M M2 DEC MG FZ').
  - exact FZ'.
Qed.

Theorem special fx R M :
  PNSDD.stX R0 S first sigma vp hi lo R -> MI M -> Z.land (hi / 2 ^ 32) 1610612736 = 1610612736 -> PNST.bdec_ok RSEGS AN M true ->
  exists fx' R' M', mem_grows M M' /\
    (   (msteps RSEGS (st fx R 0x39080 M) (st fx' R' r M') /\ (exists ptr, PNSDD.stR R0 S ptr R' /\ first <= ptr <= first + 42)
         /\ MI M' /\ PNST.bdec_ok RSEGS AN M' true /\ PNSDD.agree_but (fun a => PNSDD.in_frame S a \/ PNSDD.in_out first a) M M')
     \/ (msteps RSEGS (st fx R 0x39080 M) (st fx' R' 0x38cb0 M') /\ PNSDD.stNZ R0 S first sigma vp hi lo R' /\ PNSDD.cN S hi lo M'
         /\ MI M' /\ PNST.bdec_ok RSEGS AN M' true /\ PNSDD.agree_but (fun a => S - 232 <= a < S - 216) M M')
     \/ (msteps RSEGS (st fx R 0x39080 M) (st fx' R' 0x38bc4 M') /\ PNSDD.stNH R0 S first sigma R' /\ getr R' (reg 10) = Z_to_bv 64 (hi / 2 ^ 32 / 32768) /\ PNSDD.cN S hi lo M'
         /\ MI M' /\ PNST.bdec_ok RSEGS AN M' true /\ PNSDD.agree_but (fun a => S - 232 <= a < S - 216) M M')).
Proof.
  intros SX MIM LAND DEC. pose proof SX as ((X2 & X3 & X4 & X9 & X8 & X18 & X24 & X25 & X26 & X27) & X19 & X13 & X12 & X15).
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F39).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof DEC as (G1 & G2 & (BI & DI') & (BN & DN')). unfold PNST.sso_lit in BI, DI', BN, DN'.
  cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.mul Z.add] in G1, G2, DI', BI, DN', BN.
  (let T := type of (PNSDSP.dkS_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDSP.dkS_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A1 & A9 & A10 & A11 & A12 & C31) | [ (MS1 & KS1 & Y10 & Y11 & C30 & N31) | (MS1 & KS1 & Y10 & Y11 & N30 & N31) ] ]);
    assert (EM : M1 = M) by (apply functional_extensionality; exact FW1); subst M1.
  - (* [comment removed for export] *)
    destruct (PMCP.copy_run RSEGS 0xab480 PMCPS.memcpy_copy1 fx1 R1 M first 820649 3 0x3915c A10 A11 A12 A1 ltac:(split; [clear; lia| reflexivity])
                ltac:(clear; lia) ltac:(clear -Ffirst; lia) ltac:(clear -Ffirst; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Ffirst Fimg; lia)
                ltac:(apply (L5.writable_sub RSEGS M first 42 first 3 WR1); clear; lia) DN')
      as (R2 & M2 & MS2 & MG2 & FZ2 & DEF2 & KS2 & B10).
    assert (MI2 : MI M2) by (apply (MI_out M M2 (fun a => first <= a < first + 3) MIM MG2 FZ2); intros a Ha; clear -Ha; lia).
    assert (DEC2 : PNST.bdec_ok RSEGS AN M2 true) by (apply (bdec_out M M2 (fun a => first <= a < first + 3) DEC MG2 FZ2); intros a Ha; clear -Ha; lia).
    pose proof MI2 as (WRf2 & WR12 & IC2 & SV2). pose proof SV2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    pose proof DEC2 as (G1' & G2' & (BI2 & DI2) & (BN2 & DN2)). unfold PNST.sso_lit in BI2, DI2, BN2, DN2. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.mul Z.add] in G1', G2', DI2, BI2, DN2, BN2.
    (let T := type of (PNSDSP.dkSNT_conc fx1 R2 M2 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDSP.dkSNT_conc fx1 R2 M2 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS2 _) by PMK.inl; first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc]
                           ])).
    destruct P as (fx3 & R3 & M3 & MG3 & FW3 & FZ3 & MS3 & KS3 & B1 & B2 & B8 & B9 & B10' & B11 & B18 & B19 & B20 & B21 & B22 & B23 & NUL).
    exists fx3, R3, M3. split; [exact (mem_grows_trans _ _ _ MG2 MG3)|]. left.
    split.
    { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3|]. apply ret_step. exact B1. }
    split.
    { exists (first + 3). split; [| clear; lia]. unfold PNSDD.stR. split; [exact B2|]. split; [exact B10'|].
      intros k Hk. unfold PNSDD.CS in Hk.
      destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        first [ rewrite B8; apply Z_to_bv_bv_unsigned | rewrite B9; apply Z_to_bv_bv_unsigned | rewrite B18; apply Z_to_bv_bv_unsigned
              | rewrite B19; apply Z_to_bv_bv_unsigned | rewrite B20; apply Z_to_bv_bv_unsigned | rewrite B21; apply Z_to_bv_bv_unsigned
              | rewrite B22; apply Z_to_bv_bv_unsigned | rewrite B23; apply Z_to_bv_bv_unsigned
              | rewrite (KS3 _) by PMK.inl; rewrite (KS2 _) by PMK.inl; rewrite (KS1 _) by PMK.inl; first [exact X3 | exact X4 | exact X24 | exact X25 | exact X26 | exact X27] ]. }
    split; [apply (MI_out M2 M3 (fun a => first + 3 <= a < first + 3 + 1) MI2 MG3 FZ3); intros a Ha; clear -Ha; lia|].
    split; [apply (bdec_out M2 M3 (fun a => first + 3 <= a < first + 3 + 1) DEC2 MG3 FZ3); intros a Ha; clear -Ha; lia|].
    intros a Ha N. rewrite (FZ3 a Ha) by (intros X; apply N; right; unfold PNSDD.in_out; clear -X; lia).
    apply (FZ2 a Ha). intros X. apply N. right. unfold PNSDD.in_out. clear -X. lia.
  - (* [comment removed for export] *)
    pose proof (comb_31 (hi / 2 ^ 32) ltac:(clear -F39; lia)) as C31lem.
    assert (SPLIT : forall (EN : sigma = 0 \/ sigma = 1), exists fx' R' M', mem_grows M M' /\
      (msteps RSEGS (st fx1 R1 0x39098 M) (st fx' R' r M') /\ (exists ptr, PNSDD.stR R0 S ptr R' /\ first <= ptr <= first + 42)
       /\ MI M' /\ PNST.bdec_ok RSEGS AN M' true /\ PNSDD.agree_but (fun a => PNSDD.in_frame S a \/ PNSDD.in_out first a) M M')).
    2:{ destruct (SPLIT ltac:(clear -Fsig; lia)) as (fx' & R' & M' & MG & MS & REST). exists fx', R', M'. split; [exact MG|]. left.
        split; [eapply msteps_trans; [exact MS1| exact MS]| exact REST]. }
    intros [EN|EN].
    + pose proof (PNSDSP.dkSI0_conc fx1 R1 M VV) as P. cbn beta iota delta [VV] in P. rewrite EN, Z.add_0_r in X9. rewrite ?Z.add_0_r in P.
      PMK.feed P ltac:(first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc ]).
      destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & MS2 & KS2 & A1 & A8 & A10 & A11 & A12 & A18);
        assert (EM : M2 = M) by (apply functional_extensionality; exact FW2); subst M2.
      destruct (PMCP.copy_run RSEGS 0xab480 PMCPS.memcpy_copy1 fx2 R2 M first 820617 8 0x39128 A10 A11 A12 A1 ltac:(split; [clear; lia| reflexivity])
                  ltac:(clear; lia) ltac:(clear -Ffirst; lia) ltac:(clear -Ffirst; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Ffirst Fimg; lia)
                  ltac:(apply (L5.writable_sub RSEGS M first 42 first 8 WR1); clear; lia) DI')
        as (R3 & M3 & MS3 & MG3 & FZ3 & DEF3 & KS3 & B10).
      assert (MI3 : MI M3) by (apply (MI_out M M3 (fun a => first <= a < first + 8) MIM MG3 FZ3); intros a Ha; clear -Ha; lia).
      assert (DEC3 : PNST.bdec_ok RSEGS AN M3 true) by (apply (bdec_out M M3 (fun a => first <= a < first + 8) DEC MG3 FZ3); intros a Ha; clear -Ha; lia).
      pose proof MI3 as (WRf3 & WR13 & IC3 & SV3). pose proof SV3 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
      pose proof DEC3 as (G1' & G2' & (BI3 & DI3) & (BN3 & DN3)). unfold PNST.sso_lit in BI3, DI3, BN3, DN3. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.mul Z.add] in G1', G2', DI3, BI3, DN3, BN3.
      (let T := type of (PNSDSP.dkSIT0_conc fx2 R3 M3 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDSP.dkSIT0_conc fx2 R3 M3 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS3 _) by PMK.inl; first [PMK.sc | rewrite (KS2 _) by PMK.inl; first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc]]
])).
      destruct P as (fx4 & R4 & M4 & MG4 & FW4 & FZ4 & MS4 & KS4 & B1 & B2 & B8 & B9 & B10' & B11 & B18 & B19 & B20 & B21 & B22 & B23 & NUL).
      exists fx4, R4, M4. split; [exact (mem_grows_trans _ _ _ MG3 MG4)|].
      split.
      { eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MS4|]. apply ret_step. exact B1. }
      split.
      { exists (first + 8). split; [| clear -Fsig; lia]. unfold PNSDD.stR. split; [exact B2|]. split; [rewrite B10'; f_equal; clear; lia|].
        intros k Hk. unfold PNSDD.CS in Hk.
        destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
          first [ rewrite B8; apply Z_to_bv_bv_unsigned | rewrite B9; apply Z_to_bv_bv_unsigned | rewrite B18; apply Z_to_bv_bv_unsigned
                | rewrite B19; apply Z_to_bv_bv_unsigned | rewrite B20; apply Z_to_bv_bv_unsigned | rewrite B21; apply Z_to_bv_bv_unsigned
                | rewrite B22; apply Z_to_bv_bv_unsigned | rewrite B23; apply Z_to_bv_bv_unsigned
                | rewrite (KS4 _) by PMK.inl; rewrite (KS3 _) by PMK.inl; rewrite (KS2 _) by PMK.inl; rewrite (KS1 _) by PMK.inl; first [exact X3 | exact X4 | exact X24 | exact X25 | exact X26 | exact X27] ]. }
      split; [apply (MI_out M3 M4 (fun a => first + 8 <= a < first + 8 + 1) MI3 MG4); [intros a Ha N; apply FZ4; [exact Ha| clear -N; intros X; apply N; lia]| intros a Ha; clear -Ha; lia]|].
      split; [apply (bdec_out M3 M4 (fun a => first + 8 <= a < first + 8 + 1) DEC3 MG4); [intros a Ha N; apply FZ4; [exact Ha| clear -N; intros X; apply N; lia]| intros a Ha; clear -Ha; lia]|].
      intros a Ha N. rewrite (FZ4 a Ha) by (intros X; apply N; right; unfold PNSDD.in_out; clear -X Fsig; lia).
      apply (FZ3 a Ha). intros X. apply N. right. unfold PNSDD.in_out. clear -X Fsig. lia.
    + idtac. rewrite EN in X9.
      (let T := type of (PNSDSP.dkSI1_conc fx1 R1 M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDSP.dkSI1_conc fx1 R1 M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc ])).
      destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & MS2 & KS2 & A1 & A8 & A10 & A11 & A12 & A18);
        assert (EM : M2 = M) by (apply functional_extensionality; exact FW2); subst M2.
      destruct (PMCP.copy_run RSEGS 0xab480 PMCPS.memcpy_copy1 fx2 R2 M (first + 1) 820617 8 0x39128 A10 A11 A12 A1 ltac:(split; [clear; lia| reflexivity])
                  ltac:(clear; lia) ltac:(clear -Ffirst; lia) ltac:(clear -Ffirst; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Ffirst Fimg; lia)
                  ltac:(apply (L5.writable_sub RSEGS M first 42 (first + 1) 8 WR1); clear; lia) DI')
        as (R3 & M3 & MS3 & MG3 & FZ3 & DEF3 & KS3 & B10).
      assert (MI3 : MI M3) by (apply (MI_out M M3 (fun a => first + 1 <= a < first + 1 + 8) MIM MG3 FZ3); intros a Ha; clear -Ha; lia).
      assert (DEC3 : PNST.bdec_ok RSEGS AN M3 true) by (apply (bdec_out M M3 (fun a => first + 1 <= a < first + 1 + 8) DEC MG3 FZ3); intros a Ha; clear -Ha; lia).
      pose proof MI3 as (WRf3 & WR13 & IC3 & SV3). pose proof SV3 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
      pose proof DEC3 as (G1' & G2' & (BI3 & DI3) & (BN3 & DN3)). unfold PNST.sso_lit in BI3, DI3, BN3, DN3. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS_u.NADDR_S Z.mul Z.add] in G1', G2', DI3, BI3, DN3, BN3.
      (let T := type of (PNSDSP.dkSIT1_conc fx2 R3 M3 VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDSP.dkSIT1_conc fx2 R3 M3 VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS3 _) by PMK.inl; first [PMK.sc | rewrite (KS2 _) by PMK.inl; first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc]]
])).
      destruct P as (fx4 & R4 & M4 & MG4 & FW4 & FZ4 & MS4 & KS4 & B1 & B2 & B8 & B9 & B10' & B11 & B18 & B19 & B20 & B21 & B22 & B23 & NUL).
      exists fx4, R4, M4. split; [exact (mem_grows_trans _ _ _ MG3 MG4)|].
      split.
      { eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MS4|]. apply ret_step. exact B1. }
      split.
      { exists (first + 1 + 8). split; [| clear -Fsig; lia]. unfold PNSDD.stR. split; [exact B2|]. split; [rewrite B10'; f_equal; clear; lia|].
        intros k Hk. unfold PNSDD.CS in Hk.
        destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
          first [ rewrite B8; apply Z_to_bv_bv_unsigned | rewrite B9; apply Z_to_bv_bv_unsigned | rewrite B18; apply Z_to_bv_bv_unsigned
                | rewrite B19; apply Z_to_bv_bv_unsigned | rewrite B20; apply Z_to_bv_bv_unsigned | rewrite B21; apply Z_to_bv_bv_unsigned
                | rewrite B22; apply Z_to_bv_bv_unsigned | rewrite B23; apply Z_to_bv_bv_unsigned
                | rewrite (KS4 _) by PMK.inl; rewrite (KS3 _) by PMK.inl; rewrite (KS2 _) by PMK.inl; rewrite (KS1 _) by PMK.inl; first [exact X3 | exact X4 | exact X24 | exact X25 | exact X26 | exact X27] ]. }
      split; [apply (MI_out M3 M4 (fun a => first + 1 + 8 <= a < first + 1 + 8 + 1) MI3 MG4); [intros a Ha N; apply FZ4; [exact Ha| clear -N; intros X; apply N; lia]| intros a Ha; clear -Ha; lia]|].
      split; [apply (bdec_out M3 M4 (fun a => first + 1 + 8 <= a < first + 1 + 8 + 1) DEC3 MG4); [intros a Ha N; apply FZ4; [exact Ha| clear -N; intros X; apply N; lia]| intros a Ha; clear -Ha; lia]|].
      intros a Ha N. rewrite (FZ4 a Ha) by (intros X; apply N; right; unfold PNSDD.in_out; clear -X Fsig; lia).
      apply (FZ3 a Ha). intros X. apply N. right. unfold PNSDD.in_out. clear -X Fsig. lia.
  - (* [comment removed for export] *)
    (let T := type of (PNSDSP.dkN_conc fx1 R1 M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDSP.dkN_conc fx1 R1 M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc ])).
    destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & [ (MS2 & KS2 & Z5 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & J1 & J2 & J3 & C1 & C2 & C3 & C4)
      | [ (MS2 & KS2 & Z5 & Z6 & Z7 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z19 & Z28 & Z29 & Z30 & J1 & J2 & J3 & C1 & C2 & C3 & C4)
      | [ (MS2 & KS2 & Z5 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & J1 & J2 & J3 & C1 & C2 & C3 & C4)
      | [ (MS2 & KS2 & Z5 & Z6 & Z7 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z19 & Z28 & Z29 & Z30 & J1 & J2 & J3 & C1 & C2 & C3 & C4)
      | [ (MS2 & KS2 & Z5 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & J1 & J2 & C1 & C2 & C3 & C4)
      | (MS2 & KS2 & Z5 & Z6 & Z7 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z19 & Z28 & Z29 & Z30 & J1 & J2 & C1 & C2 & C3 & C4) ] ] ] ] ]).
    all: try (exfalso; pose proof (msb_nc hi ltac:(clear -Fhi; lia)) as NC; clear -NC J1; lia).
    all: exists fx2, R2, M2; split; [exact MG2|]; right;
      lazymatch type of MS2 with msteps _ _ (@mkst _ _ (Z_to_bv 64 ?pc) _ _) =>
        first [ constr_eq pc 0x38cb0; left; (split; [eapply msteps_trans; [exact MS1| exact MS2]|]);
                apply (dkN_exitZ R M R2 M2 SX MIM DEC MG2 FZ2);
                [ intros k Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [rewrite (KS2 _) by PMK.inl; rewrite (KS1 _) by PMK.inl; reflexivity|]); destruct Hk
                | exact Z10 | exact Z11 | exact Z14 | exact Z15 | exact Z17 | exact C1 | exact C2 | exact C3 | exact C4 ]
              | constr_eq pc 0x38bc4; right; (split; [eapply msteps_trans; [exact MS1| exact MS2]|]);
                apply (dkN_exitH R M R2 M2 SX MIM DEC MG2 FZ2);
                [ intros k Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [rewrite (KS2 _) by PMK.inl; rewrite (KS1 _) by PMK.inl; reflexivity|]); destruct Hk
                | exact Z5 | exact Z6 | exact Z7 | exact Z10 | exact Z11 | exact Z12 | exact Z13 | exact Z14 | exact Z15 | exact Z16 | exact Z17
                | exact Z19 | exact Z28 | exact Z29 | exact Z30 | exact C1 | exact C2 | exact C3 | exact C4 ] ] end.
Qed.
End Spc.
End PNSDSPC.
