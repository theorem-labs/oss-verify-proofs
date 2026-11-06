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
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk L5Defs L5Core L5CoreKit
     AxSymExec3 Bs0PlanKit PmStep PmKeep PmModel PmModelFacts PnLayout PnLayoutS PnStatics PnSrcSMemmove PnSDec128Defs PnSDec128SP
     Bs0_code_37f10_37f14.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSDSPC.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Abbreviation AN := PnLayoutS.NADDR_S.

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
Hypothesis Fimg : first + 42 <= 65536 \/ 958464 <= first.      (* [comment removed for export] *)
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
  split. { apply (PMKP.clear_agree M M' 65536 749064); [|exact IC]. intros i Hi. apply FZ'; clear -Hi FS Ffirst Fimg; lia. }
  destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  repeat split; (eapply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply FZ'; clear -Hi FS Fdj; lia| clear -FS; lia| clear -FS; lia| eassumption]).
Qed.
(* [comment removed for export] *)
Lemma bdec_out M M' (P : Z -> Prop) : PNST.bdec_ok RSEGS AN M true -> mem_grows M M' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, P a -> first <= a < first + 42) -> PNST.bdec_ok RSEGS AN M' true.
Proof.
  intros (G1 & G2 & (BI & DI) & (BN & DN)) MG FZ PF. unfold PNST.bdec_ok, PNST.sso_lit in *. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS.NADDR_S Z.mul Z.add] in *.
  assert (AGR : forall a n, 0xc6fa8 <= a -> a + n <= 0xc6fe8 -> L5C.agree_on M M' a n).
  { intros a n Ha Hn i Hi. apply FZ; [clear -Hi Ha Hn; lia|]. intros X. apply PF in X. clear -X Hi Ha Hn Ffirst Fimg. lia. }
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact G1]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact G2]|].
  split; [split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact BI]| exact (L5.defined_grows M M' _ _ MG DI)]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; clear; lia| clear; lia| clear; lia| exact BN]| exact (L5.defined_grows M M' _ _ MG DN)].
Qed.

(* [comment removed for export] *)
Lemma ret_step fx R M : getr R (reg 1) = Z_to_bv 64 r -> msteps RSEGS (st fx R 0x3800c M) (st fx R r M).
Proof. intros H1. destruct RAok as (_ & E). apply (PMK.ret_to RSEGS fx R M 0x3800c W_37fb4 r F_37fb4 eq_refl D_37fb4 H1 Fr E). Qed.

Theorem special fx R M :
  PNSDD.stX R0 S first sigma vp hi lo R -> MI M -> Z.land (hi / 2 ^ 32) 1610612736 = 1610612736 -> PNST.bdec_ok RSEGS AN M true ->
  exists fx' R' M', mem_grows M M' /\
    (   (msteps RSEGS (st fx R 0x37ef8 M) (st fx' R' r M') /\ (exists ptr, PNSDD.stR R0 S ptr R' /\ first <= ptr <= first + 42)
         /\ MI M' /\ PNST.bdec_ok RSEGS AN M' true /\ PNSDD.agree_but (fun a => PNSDD.in_frame S a \/ PNSDD.in_out first a) M M')
     \/ (msteps RSEGS (st fx R 0x37ef8 M) (st fx' R' 0x37c50 M') /\ (exists e, PNSDD.stZ R0 S first sigma e R' /\ 0 <= e <= 16383)
         /\ (forall a, M' a = M a))).
Proof.
  intros ((X2 & X3 & X4 & X9 & X8 & X18 & X24 & X25 & X26 & X27) & X19 & X12 & X14 & X13) MIM LAND DEC.
  pose proof ufacts as (F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F39).
  pose proof MIM as (WRf & WR1 & IC & SV). pose proof SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof DEC as (G1 & G2 & (BI & DI') & (BN & DN')). unfold PNST.sso_lit in BI, DI', BN, DN'.
  cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS.NADDR_S Z.mul Z.add] in G1, G2, DI', BI, DN', BN.
  (let T := type of (PNSDSP.dkS_conc fx R M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDSP.dkS_conc fx R M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A1 & A8 & A10 & A11 & A12 & A18 & C31) | [ (MS1 & KS1 & Y10 & Y11 & C30 & N31) | (MS1 & KS1 & Y10 & Y11 & N30 & N31) ] ]);
    assert (EM : M1 = M) by (apply functional_extensionality; exact FW1); subst M1.
  - (* [comment removed for export] *)
    destruct (PMCP.copy_run RSEGS 0xa9e98 PMCPS.memcpy_copy1 fx1 R1 M first 815049 3 0x37fb8 A10 A11 A12 A1 ltac:(split; [clear; lia| reflexivity])
                ltac:(clear; lia) ltac:(clear -Ffirst; lia) ltac:(clear -Ffirst; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Ffirst Fimg; lia)
                ltac:(apply (L5.writable_sub RSEGS M first 42 first 3 WR1); clear; lia) DN')
      as (R2 & M2 & MS2 & MG2 & FZ2 & DEF2 & KS2 & B10).
    assert (MI2 : MI M2) by (apply (MI_out M M2 (fun a => first <= a < first + 3) MIM MG2 FZ2); intros a Ha; clear -Ha; lia).
    assert (DEC2 : PNST.bdec_ok RSEGS AN M2 true) by (apply (bdec_out M M2 (fun a => first <= a < first + 3) DEC MG2 FZ2); intros a Ha; clear -Ha; lia).
    pose proof MI2 as (WRf2 & WR12 & IC2 & SV2). pose proof SV2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
    pose proof DEC2 as (G1' & G2' & (BI2 & DI2) & (BN2 & DN2)). unfold PNST.sso_lit in BI2, DI2, BN2, DN2. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS.NADDR_S Z.mul Z.add] in G1', G2', DI2, BI2, DN2, BN2.
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
      (msteps RSEGS (st fx1 R1 0x37f10 M) (st fx' R' r M') /\ (exists ptr, PNSDD.stR R0 S ptr R' /\ first <= ptr <= first + 42)
       /\ MI M' /\ PNST.bdec_ok RSEGS AN M' true /\ PNSDD.agree_but (fun a => PNSDD.in_frame S a \/ PNSDD.in_out first a) M M')).
    2:{ destruct (SPLIT ltac:(clear -Fsig; lia)) as (fx' & R' & M' & MG & MS & REST). exists fx', R', M'. split; [exact MG|]. left.
        split; [eapply msteps_trans; [exact MS1| exact MS]| exact REST]. }
    intros [EN|EN].
    + pose proof (PNSDSP.dkSI0_conc fx1 R1 M VV) as P. cbn beta iota delta [VV] in P. rewrite EN, Z.add_0_r in X18. rewrite ?Z.add_0_r in P.
      PMK.feed P ltac:(first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc ]).
      destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & MS2 & KS2 & A1 & A9 & A10 & A11 & A12);
        assert (EM : M2 = M) by (apply functional_extensionality; exact FW2); subst M2.
      destruct (PMCP.copy_run RSEGS 0xa9e98 PMCPS.memcpy_copy1 fx2 R2 M first 815017 8 0x37f98 A10 A11 A12 A1 ltac:(split; [clear; lia| reflexivity])
                  ltac:(clear; lia) ltac:(clear -Ffirst; lia) ltac:(clear -Ffirst; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Ffirst Fimg; lia)
                  ltac:(apply (L5.writable_sub RSEGS M first 42 first 8 WR1); clear; lia) DI')
        as (R3 & M3 & MS3 & MG3 & FZ3 & DEF3 & KS3 & B10).
      assert (MI3 : MI M3) by (apply (MI_out M M3 (fun a => first <= a < first + 8) MIM MG3 FZ3); intros a Ha; clear -Ha; lia).
      assert (DEC3 : PNST.bdec_ok RSEGS AN M3 true) by (apply (bdec_out M M3 (fun a => first <= a < first + 8) DEC MG3 FZ3); intros a Ha; clear -Ha; lia).
      pose proof MI3 as (WRf3 & WR13 & IC3 & SV3). pose proof SV3 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
      pose proof DEC3 as (G1' & G2' & (BI3 & DI3) & (BN3 & DN3)). unfold PNST.sso_lit in BI3, DI3, BN3, DN3. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS.NADDR_S Z.mul Z.add] in G1', G2', DI3, BI3, DN3, BN3.
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
    + idtac. rewrite EN in X18.
      (let T := type of (PNSDSP.dkSI1_conc fx1 R1 M VV) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSDSP.dkSI1_conc fx1 R1 M VV) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (KS1 _) by PMK.inl; PMK.sc ])).
      destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & MS2 & KS2 & A1 & A9 & A10 & A11 & A12);
        assert (EM : M2 = M) by (apply functional_extensionality; exact FW2); subst M2.
      destruct (PMCP.copy_run RSEGS 0xa9e98 PMCPS.memcpy_copy1 fx2 R2 M (first + 1) 815017 8 0x37f98 A10 A11 A12 A1 ltac:(split; [clear; lia| reflexivity])
                  ltac:(clear; lia) ltac:(clear -Ffirst; lia) ltac:(clear -Ffirst; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear -Ffirst Fimg; lia)
                  ltac:(apply (L5.writable_sub RSEGS M first 42 (first + 1) 8 WR1); clear; lia) DI')
        as (R3 & M3 & MS3 & MG3 & FZ3 & DEF3 & KS3 & B10).
      assert (MI3 : MI M3) by (apply (MI_out M M3 (fun a => first + 1 <= a < first + 1 + 8) MIM MG3 FZ3); intros a Ha; clear -Ha; lia).
      assert (DEC3 : PNST.bdec_ok RSEGS AN M3 true) by (apply (bdec_out M M3 (fun a => first + 1 <= a < first + 1 + 8) DEC MG3 FZ3); intros a Ha; clear -Ha; lia).
      pose proof MI3 as (WRf3 & WR13 & IC3 & SV3). pose proof SV3 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
      pose proof DEC3 as (G1' & G2' & (BI3 & DI3) & (BN3 & DN3)). unfold PNST.sso_lit in BI3, DI3, BN3, DN3. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN PnLayoutS.NADDR_S Z.mul Z.add] in G1', G2', DI3, BI3, DN3, BN3.
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
    destruct P as (fx2 & R2 & M2 & MG2 & FW2 & FZ2 & [ (MS2 & KS2 & B10 & B11 & B15 & B16 & B17 & _) | (MS2 & KS2 & _ & _ & _ & _ & _ & BAD) ]);
      assert (EM : M2 = M) by (apply functional_extensionality; exact FW2); subst M2.
    2:{ exfalso. pose proof (msb_nc hi ltac:(clear -Fhi; lia)). clear -H BAD. lia. }
    exists fx2, R2, M. split; [apply mem_grows_refl|]. right.
    split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [| intros a; reflexivity].
    exists (Z.land (hi / 2 ^ 32 / 32768) 16383). split; [| apply e_nc_range; clear -F39; lia].
    unfold PNSDD.stZ, PNSDD.RB. split.
    { repeat apply conj; rewrite ?(KS2 _) by PMK.inl; rewrite ?(KS1 _) by PMK.inl; first [exact X2 | exact X3 | exact X4 | exact X9 | exact X8 | exact X18 | exact X24 | exact X25 | exact X26 | exact X27]. }
    split; [exact B10|].
    rewrite (to_bv_of_unsigned _ _ B11). apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_mod by (clear; lia). set (e := Z.land (hi / 2 ^ 32 / 32768) 16383).
    replace (e + 18446744073709545440) with ((e - 6176) + 1 * 2 ^ 64) by (clear; lia). rewrite Z.mod_add by (clear; lia). reflexivity.
Qed.
End Spc.
End PNSDSPC.
