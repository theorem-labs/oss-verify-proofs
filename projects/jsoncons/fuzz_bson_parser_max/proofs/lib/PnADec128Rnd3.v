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
     PnDecFacts PnMemW PnSDec128Rnd2 PnADec128Defs PnADec128Bv PnADec128P3 PnADec128P6 PnADec128Rnd PnADec128Rnd2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNADRN3.
Import PNADRN.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
Abbreviation rdig := PNSDRN2.rdig.
Abbreviation RRT := PNADRN2.RRT.
Abbreviation RRL_sub := PNADRN2.RRL_sub.

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
Abbreviation RR := (RRa R0 S F first sigma E1).
Abbreviation cell := (PNADD.cell F).
Definition VV (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => first | 38%nat => first + sigma | 50%nat => F | 59%nat => E1 | _ => 0 end.
Local Ltac fsc := first [ assumption | (hnf; assumption) | match goal with |- getr _ _ = Z_to_bv 64 ?z => match goal with H : getr _ _ = Z_to_bv 64 ?y |- _ => replace z with y by lia; exact H end end | lia ].
(* [comment removed for export] *)
Local Ltac lem T L := pose proof L as T; L5SAR.feed T ltac:(assumption).
Lemma RR_next R R' k a10 a14 : RR R k -> (forall j, In j RRT -> getr R' (reg j) = getr R (reg j)) ->
  getr R' (reg 10) = Z_to_bv 64 a10 -> a10 = 3 - (k - 1) -> getr R' (reg 14) = Z_to_bv 64 a14 -> a14 = F + 64 + 36 * (k - 1) -> RR R' (k - 1).
Proof. lem T (PNADRN2.RR_next R0 S F first sigma E1). exact (T R R' k a10 a14). Qed.

(* [comment removed for export] *)
Lemma tail0 fx R M k D0 D1 :
  RR R k -> getr R (reg 7) = Z_to_bv 64 k -> getr R (reg 28) = Z_to_bv 64 D0 ->
  0 <= k <= 3 -> 0 <= D0 < 2 ^ 64 -> 0 <= D1 < 2 ^ 64 -> L5.writable RSEGS M (S - 128) 128 -> L5.u64_at RSEGS M (S - 112) D1 ->
  exists fx' R' (pc' : Z), msteps RSEGS (st fx R 0xb2ae0 M) (st fx' R' pc' M)
    /\ RR R' (k - 1) /\ getr R' (reg 28) = Z_to_bv 64 (D0 / 4294967296) /\ getr R' (reg 30) = Z_to_bv 64 0 /\ getr R' (reg 29) = Z_to_bv 64 D1
    /\ getr R' (reg 31) = Z_to_bv 64 (k - 1)
    /\ ((pc' = 0xb2af8 /\ k = 0) \/ (pc' = 0xb2a14 /\ 1 <= k)).
Proof.
  intros RRk G7 G28 Hk HD0 HD1 WR C1.
  pose proof RRk as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27).
  (let T := type of (PNADP3.adkRT0_conc fx R M (fun i => match i with 40%nat => k | 47%nat => D0 | 49%nat => D1 | _ => VV i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP3.adkRT0_conc fx R M (fun i => match i with 40%nat => k | 47%nat => D0 | 49%nat => D1 | _ => VV i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & _ & _ & FZ1 & [(MS1 & KS1 & A10 & A14 & A28 & A29 & A30 & A31 & CND)|(MS1 & KS1 & A10 & A14 & A28 & A29 & A30 & A31 & CND)]);
    (assert (EM : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FZ1)); subst M1;
    rewrite Z.sub_0_r, Z.mod_small in CND by (clear - Hk; lia).
  - exists fx1, R1, 0xb2af8. split; [exact MS1|].
    split; [eapply (RR_next R R1 k); [exact RRk| intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b RRT); vm_compute; reflexivity| exact A10| clear; lia| exact A14| clear; lia]|].
    split; [exact A28|]. split; [exact A30|]. split; [exact A29|]. split; [exact A31|]. left. split; [reflexivity| clear - CND Hk; lia].
  - exists fx1, R1, 0xb2a14. split; [exact MS1|].
    split; [eapply (RR_next R R1 k); [exact RRk| intros j Hj; apply KS1; revert j Hj; apply (L5K.incl_b RRT); vm_compute; reflexivity| exact A10| clear; lia| exact A14| clear; lia]|].
    split; [exact A28|]. split; [exact A30|]. split; [exact A29|]. split; [exact A31|]. right. split; [reflexivity| exact CND].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable V : Z.
Hypothesis FV : 0 <= V < 2 ^ 113.
Abbreviation p0 := PNSDRN2.p0.
Abbreviation p1 := PNSDRN2.p1.
Abbreviation p2 := PNSDRN2.p2.
Abbreviation p3 := PNSDRN2.p3.
Abbreviation Wk := (PNSDRN2.Wk V).
Abbreviation digs := (PNADD.digs F V).
Abbreviation zers := (PNADD.zers F).
Abbreviation bvu_small := PNSDRN2.bvu_small.

(* [comment removed for export] *)
Lemma cell_xfer (Ma Mb : mem) (P : Z -> Prop) i v :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (forall a, F + 32 + 4 * i <= a < F + 32 + 4 * i + 4 -> ~ P a) -> 0 <= i < 36 -> cell Ma i v -> cell Mb i v.
Proof.
  intros FZ HP Hi C. unfold PNADD.cell in *. apply (PMF.u32_at_agree RSEGS Ma Mb); [| clear - FF1 Hi; lia| clear - FF1 Hi; lia| exact C].
  intros x Hx. apply FZ; [clear - FF1 Hi Hx; lia| apply HP; exact Hx].
Qed.

(* [comment removed for export] *)
Lemma headfork fx R M k W :
  RR R k -> getr R (reg 31) = Z_to_bv 64 k -> 0 <= k <= 3 -> 0 <= W < 2 ^ 113 ->
  bv_unsigned (getr R (reg 30)) mod 2 ^ 32 = p0 W -> bv_unsigned (getr R (reg 28)) mod 2 ^ 32 = p1 W ->
  getr R (reg 29) = Z_to_bv 64 (p2 W + 4294967296 * p3 W) -> L5.writable RSEGS M (S - 128) 128 ->
  exists fx' R' M' (pc' : Z), msteps RSEGS (st fx R 0xb2a14 M) (st fx' R' pc' M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 <= a < S - 104) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ RR R' k /\ getr R' (reg 7) = Z_to_bv 64 k
    /\ ((pc' = 0xb2ae0 /\ W = 0 /\ getr R' (reg 28) = Z_to_bv 64 0 /\ L5.u64_at RSEGS M' (S - 112) 0)
        \/ (pc' = 0xb2a64 /\ getr R' (reg 28) = Z_to_bv 64 (S - 120) /\ getr R' (reg 30) = Z_to_bv 64 (F + 28 + 36 * k) /\ getr R' (reg 31) = Z_to_bv 64 0
            /\ L5.u32_at RSEGS M' (S - 120) (p0 W) /\ L5.u32_at RSEGS M' (S - 116) (p1 W) /\ L5.u32_at RSEGS M' (S - 112) (p2 W)
            /\ L5.u32_at RSEGS M' (S - 108) (p3 W))).
Proof.
  intros RRk G31 Hk HW H30 H28 G29 WR.
  pose proof (PNSDRN2.parts_val W HW) as (EW & B0 & B1 & B2 & B3).
  set (q0 := p0 W) in *. set (q1 := p1 W) in *. set (q2 := p2 W) in *. set (q3 := p3 W) in *. clearbody q0 q1 q2 q3.
  set (u30 := bv_unsigned (getr R (reg 30))) in *. set (u28 := bv_unsigned (getr R (reg 28))) in *.
  pose proof (bv_unsigned_in_range _ (getr R (reg 30))) as R30. pose proof (bv_unsigned_in_range _ (getr R (reg 28))) as R28.
  unfold bv_modulus in R30, R28. fold u30 in R30. fold u28 in R28.
  assert (G30 : getr R (reg 30) = Z_to_bv 64 u30) by (apply to_bv_of_unsigned; reflexivity).
  assert (G28 : getr R (reg 28) = Z_to_bv 64 u28) by (apply to_bv_of_unsigned; reflexivity).
  clearbody u30 u28.
  set (D1 := q2 + 4294967296 * q3) in *. set (D0 := q0 + 4294967296 * q1).
  assert (HD1 : 0 <= D1 < 2 ^ 64) by (subst D1; clear -B2 B3; lia). assert (HD0 : 0 <= D0 < 2 ^ 64) by (subst D0; clear -B0 B1; lia).
  pose proof RRk as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27).
  (let T := type of (PNADP6.adkRH_conc fx R M (fun i => match i with 40%nat => k | 41%nat => u30 | 42%nat => D1 | 43%nat => u28 | _ => VV i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP6.adkRH_conc fx R M (fun i => match i with 40%nat => k | 41%nat => u30 | 42%nat => D1 | 43%nat => u28 | _ => VV i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A7 & A28 & A30 & A31 & C112 & C120).
  rewrite (PNDF.dword0_val u28 u30) in A28, C120 by (clear -R30 R28; lia).
  rewrite H30, H28 in A28, C120. fold D0 in A28, C120.
  set (t6 := bv_unsigned (getr R1 (reg 31))).
  assert (Ht6 : t6 = 0 <-> q0 = 0).
  { subst t6. rewrite A31. rewrite PNADBV.sxw_zero. cbn [AX2.edenot AX2.ev]. rewrite (bvu_small u30) by (clear -R30; lia). rewrite H30. reflexivity. }
  pose proof (bv_unsigned_in_range _ (getr R1 (reg 31))) as Rt6. unfold bv_modulus in Rt6. fold t6 in Rt6.
  assert (G31' : getr R1 (reg 31) = Z_to_bv 64 t6) by (apply to_bv_of_unsigned; reflexivity).
  clearbody t6. clear A31.
  pose proof (L5.writable_grows RSEGS M M1 _ _ MG1 WR) as WR1.
  assert (X0 : L5.u32_at RSEGS M1 (S - 120) (D0 mod 2 ^ 32)) by (apply (PNMW.u32_of_u64_lo RSEGS M1 (S - 120) D0); [clear -FS; lia| clear -FS; lia| exact HD0| exact C120]).
  assert (X1 : L5.u32_at RSEGS M1 (S - 120 + 4) (D0 / 2 ^ 32)) by (apply (PNMW.u32_of_u64_hi RSEGS M1 (S - 120) D0); [clear -FS; lia| clear -FS; lia| exact HD0| exact C120]).
  assert (X2 : L5.u32_at RSEGS M1 (S - 112) (D1 mod 2 ^ 32)) by (apply (PNMW.u32_of_u64_lo RSEGS M1 (S - 112) D1); [clear -FS; lia| clear -FS; lia| exact HD1| exact C112]).
  assert (X3 : L5.u32_at RSEGS M1 (S - 112 + 4) (D1 / 2 ^ 32)) by (apply (PNMW.u32_of_u64_hi RSEGS M1 (S - 112) D1); [clear -FS; lia| clear -FS; lia| exact HD1| exact C112]).
  replace (D0 mod 2 ^ 32) with q0 in X0.
  2:{ subst D0. replace (q0 + 4294967296 * q1) with (q0 + q1 * 2 ^ 32) by (clear; lia). rewrite Z.mod_add by (clear; lia). symmetry. apply Z.mod_small. clear -B0; lia. }
  replace (D0 / 2 ^ 32) with q1 in X1.
  2:{ subst D0. replace (q0 + 4294967296 * q1) with (q0 + q1 * 2 ^ 32) by (clear; lia). rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -B0; lia). clear; lia. }
  replace (D1 mod 2 ^ 32) with q2 in X2.
  2:{ subst D1. replace (q2 + 4294967296 * q3) with (q2 + q3 * 2 ^ 32) by (clear; lia). rewrite Z.mod_add by (clear; lia). symmetry. apply Z.mod_small. clear -B2; lia. }
  replace (D1 / 2 ^ 32) with q3 in X3.
  2:{ subst D1. replace (q2 + 4294967296 * q3) with (q2 + q3 * 2 ^ 32) by (clear; lia). rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -B2; lia). clear; lia. }
  replace (S - 120 + 4) with (S - 116) in X1 by (clear; lia). replace (S - 112 + 4) with (S - 108) in X3 by (clear; lia).
  assert (RR1 : RR R1 k) by (apply (RRa_keep R0 S F first sigma E1 R R1 k RRk); intros j Hj; apply KS1; revert j Hj; apply RRL_sub; vm_compute; reflexivity).
  assert (FZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 <= a < S - 104) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a Ha Hn; apply (FZ1 a Ha); clear -Hn; lia).
  clear G2 G3 G4 G5 G6 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G26 G27 G28 G29 G30 G31 KS1 FZ1.
  pose proof RR1 as (G2 & G3 & G4 & G5 & G6 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G26 & G27).
  (let T := type of (PNADP6.adkRF_conc fx1 R1 M1 (fun i => match i with 40%nat => k | 44%nat => t6 | 56%nat => q1 | 57%nat => q2 | 58%nat => q3 | _ => VV i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNADP6.adkRF_conc fx1 R1 M1 (fun i => match i with 40%nat => k | 44%nat => t6 | 56%nat => q1 | 57%nat => q2 | 58%nat => q3 | _ => VV i end)) T ltac:(cbn beta iota delta [VV]) ltac:(fsc)).
  destruct P as (fx2 & R2 & M2 & _ & _ & FZ2 & [(MS2 & KS2 & _ & F58 & F57 & F56 & CND)
     |[(MS2 & KS2 & A28' & A30' & A31' & _)|[(MS2 & KS2 & A28' & _ & A30' & A31' & _)|[(MS2 & KS2 & A28' & _ & A30' & A31' & _)|(MS2 & KS2 & A28' & _ & A30' & A31' & _)]]]]);
    (assert (EM : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FZ2)); subst M2.
  - rewrite Z.sub_0_r, Z.mod_small in CND by (clear - Rt6; lia).
    assert (Z0 : q0 = 0) by (apply Ht6; clear - CND Rt6; lia).
    pose proof (PNADBV.lw_zero _ 56%nat q1 F56 eq_refl ltac:(clear -B1; lia)) as Z1.
    pose proof (PNADBV.lw_zero _ 57%nat q2 F57 eq_refl ltac:(clear -B2; lia)) as Z2.
    pose proof (PNADBV.lw_zero _ 58%nat q3 F58 eq_refl ltac:(clear -B3; lia)) as Z3.
    exists fx2, R2, M1, 0xb2ae0. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FZ1'|].
    split; [apply (RRa_keep R0 S F first sigma E1 R1 R2 k RR1); intros j Hj; apply KS2; revert j Hj; apply RRL_sub; vm_compute; reflexivity|].
    split; [rewrite (KS2 7%nat) by inl; exact A7|]. left. split; [reflexivity|]. split; [clear - EW Z0 Z1 Z2 Z3; lia|].
    split. { rewrite (KS2 28%nat) by inl. apply to_bv_of_unsigned. rewrite A28. subst D0. clear - Z0 Z1. lia. }
    replace 0 with D1 by (subst D1; clear - Z2 Z3; lia). exact C112.
  - exists fx2, R2, M1, 0xb2a64. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FZ1'|].
    split; [apply (RRa_keep R0 S F first sigma E1 R1 R2 k RR1); intros j Hj; apply KS2; revert j Hj; apply RRL_sub; vm_compute; reflexivity|].
    split; [rewrite (KS2 7%nat) by inl; exact A7|]. right. split; [reflexivity|]. split; [exact A28'|]. split; [rewrite A30'; f_equal; clear; lia|]. split; [exact A31'|].
    split; [exact X0|]. split; [exact X1|]. split; [exact X2| exact X3].
  - exists fx2, R2, M1, 0xb2a64. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FZ1'|].
    split; [apply (RRa_keep R0 S F first sigma E1 R1 R2 k RR1); intros j Hj; apply KS2; revert j Hj; apply RRL_sub; vm_compute; reflexivity|].
    split; [rewrite (KS2 7%nat) by inl; exact A7|]. right. split; [reflexivity|]. split; [exact A28'|]. split; [rewrite A30'; f_equal; clear; lia|]. split; [exact A31'|].
    split; [exact X0|]. split; [exact X1|]. split; [exact X2| exact X3].
  - exists fx2, R2, M1, 0xb2a64. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FZ1'|].
    split; [apply (RRa_keep R0 S F first sigma E1 R1 R2 k RR1); intros j Hj; apply KS2; revert j Hj; apply RRL_sub; vm_compute; reflexivity|].
    split; [rewrite (KS2 7%nat) by inl; exact A7|]. right. split; [reflexivity|]. split; [exact A28'|]. split; [rewrite A30'; f_equal; clear; lia|]. split; [exact A31'|].
    split; [exact X0|]. split; [exact X1|]. split; [exact X2| exact X3].
  - exists fx2, R2, M1, 0xb2a64. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FZ1'|].
    split; [apply (RRa_keep R0 S F first sigma E1 R1 R2 k RR1); intros j Hj; apply KS2; revert j Hj; apply RRL_sub; vm_compute; reflexivity|].
    split; [rewrite (KS2 7%nat) by inl; exact A7|]. right. split; [reflexivity|]. split; [exact A28'|]. split; [rewrite A30'; f_equal; clear; lia|]. split; [exact A31'|].
    split; [exact X0|]. split; [exact X1|]. split; [exact X2| exact X3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma divide fx R M k W :
  RR R k -> getr R (reg 7) = Z_to_bv 64 k -> getr R (reg 28) = Z_to_bv 64 (S - 120) -> getr R (reg 30) = Z_to_bv 64 (F + 28 + 36 * k) ->
  getr R (reg 31) = Z_to_bv 64 0 -> 0 <= k <= 3 -> 0 <= W < 2 ^ 113 -> L5.writable RSEGS M (S - 128) 128 ->
  L5.u32_at RSEGS M (S - 120) (p0 W) -> L5.u32_at RSEGS M (S - 116) (p1 W) -> L5.u32_at RSEGS M (S - 112) (p2 W) -> L5.u32_at RSEGS M (S - 108) (p3 W) ->
  exists fx' R' M' Q rr, msteps RSEGS (st fx R 0xb2a64 M) (st fx' R' 0xb2a90 M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 <= a < S - 104) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ RR R' k /\ getr R' (reg 7) = Z_to_bv 64 k /\ getr R' (reg 28) = Z_to_bv 64 (S - 104) /\ getr R' (reg 30) = Z_to_bv 64 (F + 28 + 36 * k)
    /\ getr R' (reg 31) = Z_to_bv 64 rr /\ L5.writable RSEGS M' (S - 128) 128
    /\ 0 <= rr < 1000000000 /\ Q = W / 1000000000 /\ rr = W mod 1000000000 /\ 0 <= Q < 2 ^ 113
    /\ 0 <= p0 Q + 4294967296 * p1 Q < 2 ^ 64 /\ 0 <= p2 Q + 4294967296 * p3 Q < 2 ^ 64
    /\ (p0 Q + 4294967296 * p1 Q) mod 2 ^ 32 = p0 Q /\ (p0 Q + 4294967296 * p1 Q) / 4294967296 = p1 Q
    /\ L5.u64_at RSEGS M' (S - 120) (p0 Q + 4294967296 * p1 Q) /\ L5.u64_at RSEGS M' (S - 112) (p2 Q + 4294967296 * p3 Q).
Proof.
  intros RRk G7 G28 G30 G31 Hk HW WR C0 C1 C2 C3.
  pose proof (PNSDRN2.parts_val W HW) as (EW & B0 & B1 & B2 & B3).
  lem LIMBS (PNADRN.limbs R0 S F first sigma E1).
  destruct (LIMBS fx R M k (p0 W) (p1 W) (p2 W) (p3 W) RRk G7 G28 G30 G31 Hk ltac:(clear -B0; lia) B1 B2 B3 WR C0 C1 C2 C3)
    as (fx2 & R2 & M2 & MS2 & MG2 & FZ2 & RR2 & B7 & B28 & B30 & B31 & WR2 & D0 & D1 & D2 & D3).
  clear LIMBS.
  pose proof (PNDF.ldiv4 (p0 W) (p1 W) (p2 W) (p3 W) ltac:(clear -B0; lia) B1 B2 B3) as LD. cbn zeta in LD.
  destruct LD as (EQ & Hr3 & Hq0 & Hq1 & Hq2 & Hq3 & _).
  eexists fx2, R2, M2, _, _. split; [exact MS2|]. split; [exact MG2|]. split; [exact FZ2|]. split; [exact RR2|]. split; [exact B7|]. split; [exact B28|].
  split; [exact B30|]. split; [exact B31|]. split; [exact WR2|]. split; [exact Hr3|].
  match type of EQ with _ = 1000000000 * ?Qt + ?rt =>
    pose proof (PNSDRN2.limb_uniq Qt _ _ _ _ eq_refl Hq0 Hq1 Hq2 Hq3) as (U0 & U1 & U2 & U3);
    assert (HQ : Qt = W / 1000000000) by (apply (Z.div_unique_pos W 1000000000 Qt rt); [exact Hr3| clear -EW EQ; lia]);
    assert (HR : rt = W mod 1000000000) by (apply (Z.mod_unique_pos W 1000000000 Qt rt); [exact Hr3| clear -EW EQ; lia])
  end.
  split; [exact HQ|]. split; [exact HR|].
  split. { rewrite HQ. split; [apply Z.div_pos; clear -HW; lia|]. apply Z.div_lt_upper_bound; [clear; lia|]. clear -HW; lia. }
  rewrite U0, U1, U2, U3.
  split; [clear -Hq0 Hq1; lia|]. split; [clear -Hq2 Hq3; lia|].
  split. { match goal with |- (?a + 4294967296 * ?b) mod _ = _ => replace (a + 4294967296 * b) with (a + b * 2 ^ 32) by (clear; lia) end.
           rewrite Z.mod_add by (clear; lia). apply Z.mod_small. exact Hq0. }
  split. { match goal with |- (?a + 4294967296 * ?b) / _ = _ => replace (a + 4294967296 * b) with (a + b * 4294967296) by (clear; lia) end.
           rewrite Z.div_add by (clear; lia). rewrite Z.div_small by exact Hq0. clear; lia. }
  split.
  - match goal with |- L5.u64_at _ _ _ (?a + 4294967296 * ?b) => apply (PNMW.u64_of_u32x2 RSEGS M2 (S - 120) a b) end;
      [clear -FS; lia| clear -FS; lia| exact Hq0| exact Hq1| exact D0| replace (S - 120 + 4) with (S - 116) by (clear; lia); exact D1].
  - match goal with |- L5.u64_at _ _ _ (?a + 4294967296 * ?b) => apply (PNMW.u64_of_u32x2 RSEGS M2 (S - 112) a b) end;
      [clear -FS; lia| clear -FS; lia| exact Hq2| exact Hq3| exact D2| replace (S - 112 + 4) with (S - 108) by (clear; lia); exact D3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HD (R : bvmap 5 word) (M : mem) (k : Z) : Prop :=
  RR R k /\ getr R (reg 31) = Z_to_bv 64 k
  /\ bv_unsigned (getr R (reg 30)) mod 2 ^ 32 = p0 (Wk k) /\ bv_unsigned (getr R (reg 28)) mod 2 ^ 32 = p1 (Wk k)
  /\ getr R (reg 29) = Z_to_bv 64 (p2 (Wk k) + 4294967296 * p3 (Wk k))
  /\ L5.writable RSEGS M (S - 128) 128 /\ L5.writable RSEGS M F 512 /\ digs M (k + 1) /\ zers M (k + 1).

(* [comment removed for export] *)
Lemma finish fx R M k Q :
  RR R k -> getr R (reg 7) = Z_to_bv 64 k -> 0 <= k <= 3 -> L5.writable RSEGS M (S - 128) 128 -> L5.writable RSEGS M F 512 -> digs M k -> zers M k ->
  getr R (reg 28) = Z_to_bv 64 (p0 Q + 4294967296 * p1 Q) -> getr R (reg 29) = Z_to_bv 64 (p2 Q + 4294967296 * p3 Q) ->
  0 <= Q < 2 ^ 113 -> Q = Wk k / 1000000000 ->
  exists fx' R',
    (k = 0 /\ msteps RSEGS (st fx R 0xb2ac4 M) (st fx' R' 0xb2af8 M) /\ RR R' (-1))
    \/ (1 <= k /\ msteps RSEGS (st fx R 0xb2ac4 M) (st fx' R' 0xb2a14 M) /\ HD R' M (k - 1)).
Proof.
  intros RRk G7 Hk WR WF DG ZR G28 G29 HQr HQ.
  pose proof (PNSDRN2.parts_val Q HQr) as (EQ & B0 & B1 & B2 & B3).
  set (q0 := p0 Q) in *. set (q1 := p1 Q) in *. set (q2 := p2 Q) in *. set (q3 := p3 Q) in *.
  assert (HD0 : 0 <= q0 + 4294967296 * q1 < 2 ^ 64) by (clear -B0 B1; lia).
  lem TL (PNADRN2.tail R0 S F first sigma E1).
  destruct (TL fx R M k (q0 + 4294967296 * q1) (q2 + 4294967296 * q3) RRk G7 G28 G29 Hk HD0 WR)
    as (fx1 & R1 & pc' & MS1 & RR1 & A28 & A30 & A29 & A31 & [(-> & K0) | (-> & K1)]); clear TL.
  - exists fx1, R1. left. split; [exact K0|]. split; [exact MS1|]. subst k. exact RR1.
  - exists fx1, R1. right. split; [exact K1|]. split; [exact MS1|].
    unfold HD. rewrite (PNSDRN2.Wk_step V k) by (clear -K1 Hk; lia). rewrite <- HQ. fold q0 q1 q2 q3.
    split; [exact RR1|]. split; [exact A31|].
    split. { rewrite A30, (bvu_small _ HD0). replace (q0 + 4294967296 * q1) with (q0 + q1 * 2 ^ 32) by (clear; lia). rewrite Z.mod_add by (clear; lia). apply Z.mod_small. clear -B0; lia. }
    split. { rewrite A28. replace ((q0 + 4294967296 * q1) / 4294967296) with q1.
             2:{ replace (q0 + 4294967296 * q1) with (q0 + q1 * 4294967296) by (clear; lia). rewrite Z.div_add by (clear; lia). rewrite Z.div_small by (clear -B0; lia). clear; lia. }
             rewrite (bvu_small q1) by (clear -B1; lia). apply Z.mod_small. exact B1. }
    split; [exact A29|]. split; [exact WR|]. split; [exact WF|].
    replace (k - 1 + 1) with k by (clear; lia). split; [exact DG| exact ZR].
Qed.

(* [comment removed for export] *)
Lemma finish0 fx R M k :
  RR R k -> getr R (reg 7) = Z_to_bv 64 k -> getr R (reg 28) = Z_to_bv 64 0 -> 0 <= k <= 3 ->
  L5.writable RSEGS M (S - 128) 128 -> L5.writable RSEGS M F 512 -> digs M k -> zers M k -> L5.u64_at RSEGS M (S - 112) 0 -> Wk k = 0 ->
  exists fx' R',
    (k = 0 /\ msteps RSEGS (st fx R 0xb2ae0 M) (st fx' R' 0xb2af8 M) /\ RR R' (-1))
    \/ (1 <= k /\ msteps RSEGS (st fx R 0xb2ae0 M) (st fx' R' 0xb2a14 M) /\ HD R' M (k - 1)).
Proof.
  intros RRk G7 G28 Hk WR WF DG ZR C1 W0.
  destruct (tail0 fx R M k 0 0 RRk G7 G28 Hk ltac:(clear; lia) ltac:(clear; lia) WR C1)
    as (fx1 & R1 & pc' & MS1 & RR1 & A28 & A30 & A29 & A31 & [(-> & K0) | (-> & K1)]).
  - exists fx1, R1. left. split; [exact K0|]. split; [exact MS1|]. subst k. exact RR1.
  - exists fx1, R1. right. split; [exact K1|]. split; [exact MS1|].
    unfold HD. rewrite (PNSDRN2.Wk_step V k) by (clear -K1 Hk; lia). rewrite W0.
    split; [exact RR1|]. split; [exact A31|].
    split; [rewrite A30; reflexivity|]. split; [rewrite A28; reflexivity|]. split; [rewrite A29; reflexivity|]. split; [exact WR|]. split; [exact WF|].
    replace (k - 1 + 1) with k by (clear; lia). split; [exact DG| exact ZR].
Qed.

(* [comment removed for export] *)
Definition Wrnd (a : Z) : Prop := S - 120 <= a < S - 104 \/ F + 32 <= a < F + 176.
Lemma cell_parts (Ma Mb : mem) i v : (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 120 <= a < S - 104) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  0 <= i < 36 -> cell Ma i v -> cell Mb i v.
Proof. intros FZ Hi C. apply (cell_xfer Ma Mb _ i v FZ); [| exact Hi| exact C]. intros a Ha. clear - Ha Hi FFS FS FF1. lia. Qed.
Lemma cell_group (Ma Mb : mem) k i v : (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + 36 * k <= a < F + 32 + 36 * k + 36) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  0 <= i < 36 -> (i < 9 * k \/ 9 * (k + 1) <= i) -> cell Ma i v -> cell Mb i v.
Proof. intros FZ Hi Ho C. apply (cell_xfer Ma Mb _ i v FZ); [| exact Hi| exact C]. intros a Ha. clear - Ha Hi Ho. lia. Qed.

Lemma round_step fx R M k : 0 <= k <= 3 -> HD R M k ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wrnd a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ L5.writable RSEGS M' (S - 128) 128 /\ L5.writable RSEGS M' F 512
    /\ ((k = 0 /\ msteps RSEGS (st fx R 0xb2a14 M) (st fx' R' 0xb2af8 M') /\ RR R' (-1) /\ digs M' 0)
        \/ (1 <= k /\ msteps RSEGS (st fx R 0xb2a14 M) (st fx' R' 0xb2a14 M') /\ HD R' M' (k - 1))).
Proof.
  intros Hk (RRk & G31 & H30 & H28 & G29 & WR & WF & DG & ZR).
  pose proof (PNSDRN2.Wk_range V FV k Hk) as HWk.
  assert (HW : 0 <= Wk k < 2 ^ 113) by (clear -HWk FV; lia).
  destruct (headfork fx R M k (Wk k) RRk G31 Hk HW H30 H28 G29 WR)
    as (fx1 & R1 & M1 & pc1 & MS1 & MG1 & FZ1 & RR1 & A7 & [(-> & W0 & A28 & C1) | (-> & A28 & A30 & A31 & C0 & C1 & C2 & C3)]).
  - (* [comment removed for export] *)
    pose proof (L5.writable_grows RSEGS M M1 _ _ MG1 WR) as WR1. pose proof (L5.writable_grows RSEGS M M1 _ _ MG1 WF) as WF1.
    assert (ZR1 : zers M1 (k + 1)) by (intros i Hi; apply (cell_parts M M1 i 0 FZ1); [clear -Hi Hk; lia| exact (ZR i Hi)]).
    assert (DG1 : digs M1 k).
    { intros i Hi. destruct (Z_lt_le_dec i (9 * (k + 1))) as [LT | GE].
      - replace i with (9 * k + (i - 9 * k)) by (clear; lia). rewrite (PNDF.dg_W_zero V k (i - 9 * k)); [| clear -FV; lia| exact Hk| clear -Hi LT; lia| exact W0].
        replace (9 * k + (i - 9 * k)) with i by (clear; lia). apply ZR1. clear -Hi LT Hk; lia.
      - apply (cell_parts M M1 i _ FZ1); [clear -Hi Hk; lia| ]. apply DG. clear -Hi GE; lia. }
    assert (ZR1' : zers M1 k) by (intros i Hi; apply ZR1; clear -Hi Hk; lia).
    destruct (finish0 fx1 R1 M1 k RR1 A7 A28 Hk WR1 WF1 DG1 ZR1' C1 W0) as (fx2 & R2 & [(K0 & MS2 & RB2) | (K1 & MS2 & HD2)]).
    + exists fx2, R2, M1. split; [exact MG1|]. split; [intros a Ha Hn; apply (FZ1 a Ha); unfold Wrnd in Hn; clear -Hn; lia|]. split; [exact WR1|]. split; [exact WF1|].
      left. split; [exact K0|]. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. subst k. split; [exact RB2| exact DG1].
    + exists fx2, R2, M1. split; [exact MG1|]. split; [intros a Ha Hn; apply (FZ1 a Ha); unfold Wrnd in Hn; clear -Hn; lia|]. split; [exact WR1|]. split; [exact WF1|].
      right. split; [exact K1|]. split; [eapply msteps_trans; [exact MS1| exact MS2]| exact HD2].
  - (* [comment removed for export] *)
    pose proof (L5.writable_grows RSEGS M M1 _ _ MG1 WR) as WR1. pose proof (L5.writable_grows RSEGS M M1 _ _ MG1 WF) as WF1.
    destruct (divide fx1 R1 M1 k (Wk k) RR1 A7 A28 A30 A31 Hk HW WR1 C0 C1 C2 C3)
      as (fx2 & R2 & M2 & Q & rr & MS2 & MG2 & FZ2 & RR2 & B7 & B28 & B30 & B31 & WR2 & Hrr & HQ & HR & HQr & HE0 & HE1 & M0 & Dv1 & X0 & X1).
    pose proof (L5.writable_grows RSEGS M1 M2 _ _ MG2 WF1) as WF2.
    assert (ZR2 : zers M2 (k + 1)).
    { intros i Hi. apply (cell_parts M1 M2 i 0 FZ2); [clear -Hi Hk; lia|]. apply (cell_parts M M1 i 0 FZ1); [clear -Hi Hk; lia| exact (ZR i Hi)]. }
    assert (DG2 : digs M2 (k + 1)).
    { intros i Hi. apply (cell_parts M1 M2 i _ FZ2); [clear -Hi Hk; lia|]. apply (cell_parts M M1 i _ FZ1); [clear -Hi Hk; lia| exact (DG i Hi)]. }
    lem RELOAD (PNADRN2.reload R0 S F first sigma E1).
    destruct (RELOAD fx2 R2 M2 k rr (p0 Q + 4294967296 * p1 Q) (p2 Q + 4294967296 * p3 Q) RR2 B7 B28 B30 B31 Hk Hrr HE0 HE1 WR2 X0 X1)
      as (fx3 & R3 & pc3 & MS3 & RR3 & C7 & C28 & C29 & C30 & C31 & [(-> & Rz) | (-> & Rnz & C24)]); clear RELOAD.
    + (* [comment removed for export] *)
      assert (DG3 : digs M2 k).
      { intros i Hi. destruct (Z_lt_le_dec i (9 * (k + 1))) as [LT | GE]; [| apply DG2; clear -Hi GE; lia].
        replace i with (9 * k + (i - 9 * k)) by (clear; lia).
        rewrite (PNDF.dg_round_zero V k (i - 9 * k)); [| clear -FV; lia| exact Hk| clear -Hi LT; lia| unfold PNSDRN2.Wk in HR; rewrite <- HR; exact Rz].
        replace (9 * k + (i - 9 * k)) with i by (clear; lia). apply ZR2. clear -Hi LT Hk; lia. }
      assert (ZR3 : zers M2 k) by (intros i Hi; apply ZR2; clear -Hi Hk; lia).
      destruct (finish fx3 R3 M2 k Q RR3 C7 Hk WR2 WF2 DG3 ZR3 C28 C29 HQr HQ) as (fx4 & R4 & [(K0 & MS4 & RB4) | (K1 & MS4 & HD4)]).
      * exists fx4, R4, M2. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
        split; [intros a Ha Hn; unfold Wrnd in Hn; rewrite (FZ2 a Ha) by (clear -Hn; lia); apply (FZ1 a Ha); clear -Hn; lia|]. split; [exact WR2|]. split; [exact WF2|].
        left. split; [exact K0|]. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]|].
        subst k. split; [exact RB4| exact DG3].
      * exists fx4, R4, M2. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
        split; [intros a Ha Hn; unfold Wrnd in Hn; rewrite (FZ2 a Ha) by (clear -Hn; lia); apply (FZ1 a Ha); clear -Hn; lia|]. split; [exact WR2|]. split; [exact WF2|].
        right. split; [exact K1|]. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| exact MS4]]]| exact HD4].
    + (* [comment removed for export] *)
      assert (Hrr' : 1 <= rr < 1000000000) by (clear -Rnz Hrr; lia).
      lem DIGITS (PNADRN2.digits R0 S F first sigma E1).
      destruct (DIGITS k Hk fx3 R3 M2 rr (p0 Q + 4294967296 * p1 Q) (p2 Q + 4294967296 * p3 Q) RR3 C7 C24 C30 C31 C28 C29 HE0 HE1 Hrr' WR2 WF2)
        as (fx4 & R4 & M4 & MS4 & MG4 & FZ4 & RR4 & D7 & D28 & D29 & CELLS); clear DIGITS.
      pose proof (L5.writable_grows RSEGS M2 M4 _ _ MG4 WR2) as WR4. pose proof (L5.writable_grows RSEGS M2 M4 _ _ MG4 WF2) as WF4.
      assert (DG4 : digs M4 k).
      { intros i Hi. destruct (Z_lt_le_dec i (9 * (k + 1))) as [LT | GE].
        - replace i with (9 * k + (i - 9 * k)) by (clear; lia).
          rewrite <- (PNDF.dg_round V k (i - 9 * k)); [| clear -FV; lia| exact Hk| clear -Hi LT; lia].
          unfold PNSDRN2.Wk in HR. rewrite <- HR. apply (CELLS (i - 9 * k)). clear -Hi LT Hk; lia.
        - apply (cell_group M2 M4 k i _ FZ4); [clear -Hi Hk; lia| clear -GE; lia|]. apply DG2. clear -Hi GE; lia. }
      assert (ZR4 : zers M4 k).
      { intros i Hi. apply (cell_group M2 M4 k i 0 FZ4); [clear -Hi Hk; lia| clear -Hi; lia|]. apply ZR2. clear -Hi Hk; lia. }
      destruct (finish fx4 R4 M4 k Q RR4 D7 Hk WR4 WF4 DG4 ZR4 D28 D29 HQr HQ) as (fx5 & R5 & [(K0 & MS5 & RB5) | (K1 & MS5 & HD5)]).
      * exists fx5, R5, M4. split; [intros a Ha; apply MG4; apply MG2; apply MG1; exact Ha|].
        split; [intros a Ha Hn; unfold Wrnd in Hn; rewrite (FZ4 a Ha) by (clear -Hn Hk; lia); rewrite (FZ2 a Ha) by (clear -Hn; lia); apply (FZ1 a Ha); clear -Hn; lia|].
        split; [exact WR4|]. split; [exact WF4|].
        left. split; [exact K0|].
        split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| eapply msteps_trans; [exact MS4| exact MS5]]]]|].
        subst k. split; [exact RB5| exact DG4].
      * exists fx5, R5, M4. split; [intros a Ha; apply MG4; apply MG2; apply MG1; exact Ha|].
        split; [intros a Ha Hn; unfold Wrnd in Hn; rewrite (FZ4 a Ha) by (clear -Hn Hk; lia); rewrite (FZ2 a Ha) by (clear -Hn; lia); apply (FZ1 a Ha); clear -Hn; lia|].
        split; [exact WR4|]. split; [exact WF4|].
        right. split; [exact K1|].
        split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| eapply msteps_trans; [exact MS3| eapply msteps_trans; [exact MS4| exact MS5]]]]| exact HD5].
Qed.

End Call.
End PNADRN3.
