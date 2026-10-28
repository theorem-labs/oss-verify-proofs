(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PnLayout PnModel. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDigitFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAFromIntP_b PnAFromIntP2_b PnAFromIntP3_b PnAFromIntK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAFID.
Import L5A. Import L5CA. Import L5SAR. Import PNAFIK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (y & Hy & E). apply Nat.eqb_eq in E. subst y. exact Hy.
Qed.
Lemma to_bv_neg a : Z_to_bv 64 (- a) = Z_to_bv 64 (2 ^ 64 - a).
Proof.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (2 ^ 64 - a) with (- a + 1 * 2 ^ 64) by Lia.lia. rewrite Z.mod_add by Lia.lia. reflexivity.
Qed.
Lemma to_bv_mod a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. Lia.lia. Qed.

(* [comment removed for export] *)
Definition rbase (S o F : Z) (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 128) /\ getr R (reg 8) = Z_to_bv 64 S /\ getr R (reg 9) = Z_to_bv 64 (S - 128)
  /\ getr R (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr R (reg 19) = Z_to_bv 64 F /\ getr R (reg 20) = Z_to_bv 64 o
  /\ getr R (reg 23) = Z_to_bv 64 F /\ getr R (reg 24) = Z_to_bv 64 2147450880 /\ getr R (reg 25) = Z_to_bv 64 (F + 32).
Definition RB : list nat := [2; 8; 9; 18; 19; 20; 23; 24; 25]%nat.
Lemma rbase_keep S o F R R' : (forall i, In i RB -> getr R' (reg i) = getr R (reg i)) -> rbase S o F R -> rbase S o F R'.
Proof.
  intros KS (B2 & B8 & B9 & B18 & B19 & B20 & B23 & B24 & B25). unfold rbase.
  rewrite (KS 2%nat), (KS 8%nat), (KS 9%nat), (KS 18%nat), (KS 19%nat), (KS 20%nat), (KS 23%nat), (KS 24%nat), (KS 25%nat) by inl.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition pmem (S F fl : Z) (M : mem) : Prop :=
  L5.writable RSEGS M (S - 128) 128 /\ L5.defined M F 512 /\ L5.writable RSEGS M F 512 /\ L5.writable RSEGS M (F / 8 + 2147450880) 64
  /\ L5.u64_at RSEGS M (F + 504) fl /\ L5.writable RSEGS M fl 1.
Lemma pmem_keep S o F fl (M M' : mem) : geom S o F fl -> mem_grows M M' ->
  (forall a, F + 504 <= a < F + 512 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> pmem S F fl M -> pmem S F fl M'.
Proof.
  intros GEO MG AG (P1 & P2 & P3 & P4 & P5 & P6).
  destruct GEO as (GS1 & GS32 & GO1 & GO2 & GO8 & GOB & GF1 & GF2 & GF32 & GFB & GOF & GL1 & GL2 & GLB & GFL & GOL).
  unfold pmem.
  split; [exact (L5.writable_grows RSEGS M M' _ _ MG P1)|]. split; [exact (L5.defined_grows M M' _ _ MG P2)|].
  split; [exact (L5.writable_grows RSEGS M M' _ _ MG P3)|]. split; [exact (L5.writable_grows RSEGS M M' _ _ MG P4)|].
  split; [| exact (L5.writable_grows RSEGS M M' _ _ MG P6)].
  apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; clear - Hi; lia| clear - GF1; lia| clear - GF2 GS1; lia| exact P5].
Qed.

Section Call.
Variables (S o F fl v : Z).
Hypothesis GEO : geom S o F fl.
Hypothesis Hv : - 2 ^ 31 <= v < 2 ^ 31.

(* [comment removed for export] *)
Definition VV (k x j : Z) (i : nat) : Z :=
  match i with 2%nat => S | 33%nat => o | 34%nat => v mod 2 ^ 64 | 35%nat => k | 36%nat => x | 40%nat => j | 50%nat => F | 51%nat => fl | _ => 0 end.

(* [comment removed for export] *)
Lemma gfacts :
  (0 <= S < 2 ^ 64 /\ 0 <= o < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= v mod 2 ^ 64 < 2 ^ 64)
  /\ 140735332487296 <= S <= 140737488355328 /\ PNAFIP.aligned S 32 /\ 6905856 <= F <= 140737488354816 /\ PNAFIP.aligned F 32
  /\ (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) /\ 4096 <= fl <= 140737488355327
  /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) /\ (F + 512 <= fl \/ fl + 1 <= F)
  /\ (S - 128 + 128 <= F \/ F + 512 <= S - 128) /\ (S - 128 + 128 <= fl \/ fl + 1 <= S - 128)
  /\ (65536 + 6840320 <= F \/ F + 512 <= 65536) /\ (65536 + 6840320 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= 65536)
  /\ (65536 + 6840320 <= fl \/ fl + 1 <= 65536) /\ 0 <= v mod 2 ^ 64 <= 18446744073709551615.
Proof.
  pose proof (geom_rng _ _ _ _ GEO) as (Eo8 & EF8 & Qo0 & QF0 & Qo1 & QF1 & QoF).
  destruct GEO as (GS1 & GS32 & GO1 & GO2 & GO8 & GOB & GF1 & GF2 & GF32 & GFB & GOF & GL1 & GL2 & GLB & GFL & GOL).
  pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(clear; Lia.lia)) as U34.
  split; [clear - GS1 GO1 GO2 GF1 GF2 GL1 GL2 U34; Lia.lia|].
  split; [exact GS1|]. split; [exact GS32|]. split; [clear - GS1 GF1 GF2; Lia.lia|]. split; [exact GF32|]. split; [exact GFB|].
  split; [clear - GS1 GL1 GL2; Lia.lia|]. split; [exact GLB|]. split; [exact GFL|].
  split; [right; clear - GF2; Lia.lia|]. split; [right; clear - GL2; Lia.lia|]. split; [left; clear - GF1; Lia.lia|].
  split; [left; clear - QF0; Lia.lia|]. split; [left; clear - GL1; Lia.lia|]. clear - U34. Lia.lia.
Qed.

Ltac gpose :=
  pose proof gfacts as ((?QS & ?Qo & ?QF & ?Qfl & ?Qv) & ?GS1 & ?GS32 & ?GF1 & ?GF32 & ?GFB & ?GL1 & ?GLB & ?GFL & ?GSF & ?GSL & ?GIF & ?GISF & ?GIL & ?GV).
Ltac pm_open PM := pose proof PM as (?MWS & ?MFD & ?MFW & ?MFSW & ?MFLC & ?MFLW).
Ltac rb_open RB := pose proof RB as (?B2 & ?B8 & ?B9 & ?B18 & ?B19 & ?B20 & ?B23 & ?B24 & ?B25).

(* [comment removed for export] *)
Definition KD : list nat := [3; 4; 22; 27]%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pos_loop (m : nat) : forall (fx : FPState) R M x k,
  rbase S o F R -> getr R (reg 10) = Z_to_bv 64 10 -> getr R (reg 11) = Z_to_bv 64 14757395259826634752 -> getr R (reg 12) = Z_to_bv 64 254 ->
  getr R (reg 14) = Z_to_bv 64 x -> getr R (reg 21) = Z_to_bv 64 k -> pmem S F fl M ->
  0 <= x < 10 ^ Z.of_nat m -> x < 2 ^ 31 -> 0 <= k -> k + Z.of_nat m <= 10 -> (1 <= m)%nat ->
  exists (fx' : FPState) R' M' d, msteps RSEGS (st fx R 0xb63e0 M) (st fx' R' 0xb646c M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 32 + 16) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ k + 1 <= d <= k + Z.of_nat m /\ getr R' (reg 21) = Z_to_bv 64 d
    /\ rbase S o F R' /\ (forall i, In i KD -> getr R' (reg i) = getr R (reg i)).
Proof.
  induction m as [|m IH]; intros fx R M x k RB G10 G11 G12 G14 G21 PM Hx Hx31 Hk Hkm Hm; [exfalso; clear - Hm; Lia.lia|].
  gpose. pm_open PM. rb_open RB.
  assert (Hx64 : 0 <= x < 2 ^ 64) by (clear - Hx Hx31; Lia.lia). assert (Hk64 : 0 <= k < 2 ^ 64) by (clear - Hk Hkm; Lia.lia).
  assert (Hx32 : 0 <= x <= 2147483647) by (clear - Hx Hx31; Lia.lia). assert (Hk10 : 0 <= k <= 10) by (clear - Hk Hkm; Lia.lia).
  (let T := type of (PNAFIP.afnPL_conc fx R M (VV k x 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNAFIP.afnPL_conc fx R M (VV k x 0)) T ltac:(cbn beta iota delta [VV]) ltac:(L5SAR.sc)).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & B13 & B14' & B15 & B16 & _ & B21 & _).
  rewrite (PNDG.quot_pos x) in B14' by (clear - Hx Hx31; Lia.lia).
  assert (A14 : getr R1 (reg 14) = Z_to_bv 64 (x / 10)).
  { rewrite <- B14'. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (RB1 : rbase S o F R1) by (apply (rbase_keep S o F R R1); [intros i Hi; apply KS1; revert i Hi; apply sub_in; vm_compute; reflexivity| exact RB]).
  assert (PM1 : pmem S F fl M1) by (apply (pmem_keep S o F fl M M1 GEO MG1); [intros a Ha; apply FRZ1; clear - Ha GF1; Lia.lia| exact PM]).
  rb_open RB1. pm_open PM1.
  assert (C10 : getr R1 (reg 10) = Z_to_bv 64 10) by (rewrite (KS1 10%nat) by inl; exact G10).
  assert (C12 : getr R1 (reg 12) = Z_to_bv 64 254) by (rewrite (KS1 12%nat) by inl; exact G12).
  (let T := type of (PNAFIP.afnPM_conc fx1 R1 M1 (VV k x 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNAFIP.afnPM_conc fx1 R1 M1 (VV k x 0)) T ltac:(cbn beta iota delta [VV]) ltac:(L5SAR.sc)).
  destruct P as (fx2 & R2 & M2 & MG2 & FR2 & _ & EX).
  assert (EM : M2 = M1) by (apply functional_extensionality; exact FR2). subst M2.
  destruct EX as [(MS2 & KS2 & GE10)|(MS2 & KS2 & LT10)].
  - (* [comment removed for export] *)
    assert (Hx' : 0 <= x / 10 < 10 ^ Z.of_nat m).
    { split; [apply Z.div_pos; clear - Hx; Lia.lia|]. apply Z.div_lt_upper_bound; [clear; Lia.lia|].
      replace (10 * 10 ^ Z.of_nat m) with (10 ^ Z.of_nat (Datatypes.S m)); [clear - Hx; Lia.lia|].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by (clear; Lia.lia). reflexivity. }
    assert (Hm1 : (1 <= m)%nat).
    { destruct m; [|clear; Lia.lia]. exfalso. cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Hx. clear - Hx GE10. Lia.lia. }
    assert (RB2 : rbase S o F R2) by (apply (rbase_keep S o F R1 R2); [intros i Hi; apply KS2; revert i Hi; apply sub_in; vm_compute; reflexivity| exact RB1]).
    destruct (IH fx2 R2 M1 (x / 10) (k + 1) RB2) as (fx3 & R3 & M3 & d & MS3 & MG3 & FRZ3 & Hd & D21 & RB3 & KS3).
    { rewrite (KS2 10%nat) by inl. exact C10. }
    { rewrite (KS2 11%nat) by inl. rewrite (KS1 11%nat) by inl. exact G11. }
    { rewrite (KS2 12%nat) by inl. exact C12. }
    { rewrite (KS2 14%nat) by inl. exact A14. }
    { rewrite (KS2 21%nat) by inl. exact B21. }
    { exact PM1. }
    { exact Hx'. }
    { apply Z.div_lt_upper_bound; clear - Hx Hx31; Lia.lia. }
    { clear - Hk; Lia.lia. }
    { rewrite Nat2Z.inj_succ in Hkm. clear - Hkm. Lia.lia. }
    { exact Hm1. }
    exists fx3, R3, M3, d. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|].
    split; [intros a Ha; apply MG3; apply MG1; exact Ha|].
    split; [intros a Ha Na; rewrite (FRZ3 a Ha Na); apply (FRZ1 a Ha Na)|].
    split; [rewrite Nat2Z.inj_succ; clear - Hd; Lia.lia|]. split; [exact D21|]. split; [exact RB3|].
    intros i Hi. rewrite (KS3 i Hi). rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
  - (* [comment removed for export] *)
    exists fx2, R2, M1, (k + 1). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FRZ1|].
    split; [rewrite Nat2Z.inj_succ; clear; Lia.lia|]. split; [rewrite (KS2 21%nat) by inl; exact B21|].
    split; [apply (rbase_keep S o F R1 R2); [intros i Hi; apply KS2; revert i Hi; apply sub_in; vm_compute; reflexivity| exact RB1]|].
    intros i Hi. rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma neg_loop (m : nat) : forall (fx : FPState) R M a k,
  rbase S o F R -> getr R (reg 10) = Z_to_bv 64 10 -> getr R (reg 11) = Z_to_bv 64 (-20) -> getr R (reg 12) = Z_to_bv 64 1717986919 ->
  getr R (reg 13) = Z_to_bv 64 254 -> getr R (reg 15) = Z_to_bv 64 (2 ^ 64 - a) -> getr R (reg 21) = Z_to_bv 64 k -> pmem S F fl M ->
  1 <= a < 10 ^ Z.of_nat m -> a <= 2 ^ 31 -> 0 <= k -> k + Z.of_nat m <= 10 -> (1 <= m)%nat ->
  exists (fx' : FPState) R' M' d, msteps RSEGS (st fx R 0xb6430 M) (st fx' R' 0xb646c M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 32 + 16) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ k + 1 <= d <= k + Z.of_nat m /\ getr R' (reg 21) = Z_to_bv 64 d
    /\ rbase S o F R' /\ (forall i, In i KD -> getr R' (reg i) = getr R (reg i)).
Proof.
  induction m as [|m IH]; intros fx R M a k RB G10 G11 G12 G13 G15 G21 PM Ha Ha31 Hk Hkm Hm; [exfalso; clear - Hm; Lia.lia|].
  gpose. pm_open PM. rb_open RB.
  assert (Hx64 : 0 <= 2 ^ 64 - a < 2 ^ 64) by (clear - Ha Ha31; Lia.lia). assert (Hk64 : 0 <= k < 2 ^ 64) by (clear - Hk Hkm; Lia.lia).
  assert (Hx32 : 18446744071562067968 <= 2 ^ 64 - a <= 18446744073709551615) by (clear - Ha Ha31; Lia.lia). assert (Hk10 : 0 <= k <= 10) by (clear - Hk Hkm; Lia.lia).
  (let T := type of (PNAFIP2.afnNL_conc fx R M (VV k (2 ^ 64 - a) 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNAFIP2.afnNL_conc fx R M (VV k (2 ^ 64 - a) 0)) T ltac:(cbn beta iota delta [VV]) ltac:(L5SAR.sc)).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & _ & B14 & B15 & B16 & B17 & B21).
  cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in B15, B16.
  rewrite (PNDG.quot_neg (Z_to_bv 64 (2 ^ 64 - a)) a ltac:(clear - Ha Ha31; Lia.lia) eq_refl) in B15.
  set (t0 := bv_unsigned (getr R1 (reg 16))).
  pose proof (PNDG.t0_neg (Z_to_bv 64 (2 ^ 64 - a)) a ltac:(clear - Ha Ha31; Lia.lia) eq_refl) as T0. rewrite <- B16 in T0. fold t0 in T0.
  assert (Ht0 : 0 <= t0 < 2 ^ 64) by (subst t0; apply bv_unsigned_in_range).
  assert (A16 : getr R1 (reg 16) = Z_to_bv 64 t0) by (subst t0; symmetry; apply Z_to_bv_bv_unsigned).
  assert (A15 : getr R1 (reg 15) = Z_to_bv 64 ((- (a / 10)) mod 2 ^ 64)) by (rewrite B15, to_bv_mod; reflexivity).
  pose proof (Z.mod_pos_bound (- (a / 10)) (2 ^ 64) ltac:(clear; Lia.lia)) as U41.
  assert (RB1 : rbase S o F R1) by (apply (rbase_keep S o F R R1); [intros i Hi; apply KS1; revert i Hi; apply sub_in; vm_compute; reflexivity| exact RB]).
  assert (PM1 : pmem S F fl M1) by (apply (pmem_keep S o F fl M M1 GEO MG1); [intros i Hi; apply FRZ1; clear - Hi GF1; Lia.lia| exact PM]).
  assert (Hq : 0 <= a / 10 /\ a / 10 < 214748365).
  { split; [apply Z.div_pos| apply Z.div_lt_upper_bound]; clear - Ha Ha31; Lia.lia. }
  (* [comment removed for export] *)
  idtac.
  clear B2 B8 B9 B18 B19 B20 B23 B24 B25 MWS MFD MFW MFSW MFLC MFLW.
  rb_open RB1. pm_open PM1.
  assert (C10 : getr R1 (reg 10) = Z_to_bv 64 10) by (rewrite (KS1 10%nat) by inl; exact G10).
  assert (C11 : getr R1 (reg 11) = Z_to_bv 64 (-20)) by (rewrite (KS1 11%nat) by inl; exact G11).
  assert (C12 : getr R1 (reg 12) = Z_to_bv 64 1717986919) by (rewrite (KS1 12%nat) by inl; exact G12).
  assert (C13 : getr R1 (reg 13) = Z_to_bv 64 254) by (rewrite (KS1 13%nat) by inl; exact G13).
  (let T := type of (PNAFIP.afnNM_conc fx1 R1 M1 (fun i => match i with 39%nat => t0 | 41%nat => (- (a / 10)) mod 2 ^ 64 | _ => VV k 0 0 i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNAFIP.afnNM_conc fx1 R1 M1 (fun i => match i with 39%nat => t0 | 41%nat => (- (a / 10)) mod 2 ^ 64 | _ => VV k 0 0 i end)) T ltac:(cbn beta iota delta [VV]) ltac:(L5SAR.sc)).
  destruct P as (fx2 & R2 & M2 & MG2 & FR2 & _ & EX).
  assert (EM : M2 = M1) by (apply functional_extensionality; exact FR2). subst M2.
  destruct EX as [(MS2 & KS2 & LE)|(MS2 & KS2 & GT)].
  - (* [comment removed for export] *)
    assert (Ha10 : 10 <= a) by (destruct (Z_lt_le_dec a 10) as [l|l]; [exfalso; clear - T0 LE l; apply proj1 in T0; specialize (T0 ltac:(Lia.lia)); Lia.lia| exact l]).
    assert (Ha' : 1 <= a / 10 < 10 ^ Z.of_nat m).
    { split; [apply Z.div_le_lower_bound; clear - Ha10; Lia.lia|]. apply Z.div_lt_upper_bound; [clear; Lia.lia|].
      replace (10 * 10 ^ Z.of_nat m) with (10 ^ Z.of_nat (Datatypes.S m)); [clear - Ha; Lia.lia|].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by (clear; Lia.lia). reflexivity. }
    assert (Hm1 : (1 <= m)%nat).
    { destruct m; [|clear; Lia.lia]. exfalso. cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Ha. clear - Ha Ha10. Lia.lia. }
    assert (RB2 : rbase S o F R2) by (apply (rbase_keep S o F R1 R2); [intros i Hi; apply KS2; revert i Hi; apply sub_in; vm_compute; reflexivity| exact RB1]).
    destruct (IH fx2 R2 M1 (a / 10) (k + 1) RB2) as (fx3 & R3 & M3 & d & MS3 & MG3 & FRZ3 & Hd & D21 & RB3 & KS3).
    { rewrite (KS2 10%nat) by inl. exact C10. }
    { rewrite (KS2 11%nat) by inl. exact C11. }
    { rewrite (KS2 12%nat) by inl. exact C12. }
    { rewrite (KS2 13%nat) by inl. exact C13. }
    { rewrite (KS2 15%nat) by inl. rewrite B15. apply to_bv_neg. }
    { rewrite (KS2 21%nat) by inl. exact B21. }
    { exact PM1. }
    { exact Ha'. }
    { clear - Hq. Lia.lia. }
    { clear - Hk; Lia.lia. }
    { rewrite Nat2Z.inj_succ in Hkm. clear - Hkm. Lia.lia. }
    { exact Hm1. }
    exists fx3, R3, M3, d. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|].
    split; [intros b Hb; apply MG3; apply MG1; exact Hb|].
    split; [intros b Hb Nb; rewrite (FRZ3 b Hb Nb); apply (FRZ1 b Hb Nb)|].
    split; [rewrite Nat2Z.inj_succ; clear - Hd; Lia.lia|]. split; [exact D21|]. split; [exact RB3|].
    intros i Hi. rewrite (KS3 i Hi). rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
  - (* [comment removed for export] *)
    exists fx2, R2, M1, (k + 1). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FRZ1|].
    split; [rewrite Nat2Z.inj_succ; clear; Lia.lia|]. split; [rewrite (KS2 21%nat) by inl; exact B21|].
    split; [apply (rbase_keep S o F R1 R2); [intros i Hi; apply KS2; revert i Hi; apply sub_in; vm_compute; reflexivity| exact RB1]|].
    intros i Hi. rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Ltac cget H := lazymatch type of H with
  | ?A /\ ?B => lazymatch goal with |- A => exact (proj1 H) | _ => cget (proj2 H) end
  | _ => exact H end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma done_fork (fx : FPState) R M d :
  rbase S o F R -> getr R (reg 21) = Z_to_bv 64 d -> getr R (reg 22) = Z_to_bv 64 v -> 1 <= d <= 10 -> pmem S F fl M ->
  exists (fx' : FPState) R', rbase S o F R' /\ (forall i, In i [3; 4; 27]%nat -> getr R' (reg i) = getr R (reg i)) /\ getr R' (reg 21) = Z_to_bv 64 d
    /\ ( (0 <= v /\ msteps RSEGS (st fx R 0xb646c M) (st fx' R' 0xb64a0 M)
          /\ getr R' (reg 22) = Z_to_bv 64 (F + 32 + (d - 1)) /\ getr R' (reg 26) = Z_to_bv 64 (F + 32 + (d - 1)))
      \/ (v < 0 /\ msteps RSEGS (st fx R 0xb646c M) (st fx' R' 0xd5bc4 M) /\ getr R' (reg 1) = Z_to_bv 64 0xb6488 /\ getr R' (reg 10) = Z_to_bv 64 o
          /\ getr R' (reg 26) = Z_to_bv 64 (F + 32 + d)) ).
Proof.
  intros RB G21 G22 Hd PM. gpose. pm_open PM. rb_open RB.
  assert (A22 : getr R (reg 22) = Z_to_bv 64 (v mod 2 ^ 64)) by (rewrite to_bv_mod; exact G22).
  assert (Hd64 : 0 <= d < 2 ^ 64) by (clear - Hd; Lia.lia).
  (let T := type of (PNAFIP3.afnD_conc fx R M (VV d 0 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNAFIP3.afnD_conc fx R M (VV d 0 0)) T ltac:(cbn beta iota delta [VV]) ltac:(L5SAR.sc)).
  destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & EX).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
  pose proof (PNDG.slt0 v ltac:(clear - Hv; Lia.lia)) as SLT.
  exists fx1, R1.
  destruct EX as [(MS1 & KS1 & _ & C22 & C26 & SGN)|(MS1 & KS1 & C1 & C10 & _ & C27 & SGN)];
    cbn [AX2.edenot AX2.ev] in SGN; rewrite to_bv_mod, SLT in SGN.
  - assert (Hv0 : 0 <= v) by (destruct (Z.ltb_spec v 0); [exfalso; clear - SGN; Lia.lia| assumption]).
    split; [apply (rbase_keep S o F R R1); [intros i Hi; apply KS1; revert i Hi; apply sub_in; vm_compute; reflexivity| exact RB]|].
    split; [intros i Hi; apply KS1; revert i Hi; apply sub_in; vm_compute; reflexivity|].
    split; [rewrite (KS1 21%nat) by inl; exact G21|].
    left. split; [exact Hv0|]. split; [exact MS1|].
    split; [rewrite C22; f_equal; clear; Lia.lia| rewrite C26; f_equal; clear; Lia.lia].
  - assert (Hvn : v < 0) by (destruct (Z.ltb_spec v 0); [assumption| exfalso; clear - SGN; Lia.lia]).
    split; [apply (rbase_keep S o F R R1); [intros i Hi; apply KS1; revert i Hi; apply sub_in; vm_compute; reflexivity| exact RB]|].
    split; [intros i Hi; apply KS1; revert i Hi; apply sub_in; vm_compute; reflexivity|].
    split; [rewrite (KS1 21%nat) by inl; exact G21|].
    right. split; [exact Hvn|]. split; [exact MS1|]. split; [exact C1|]. split; [exact C10|].
    rewrite C27; f_equal; clear; Lia.lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wd (a : Z) : Prop :=
  (S - 104 <= a < S - 104 + 8) \/ (F <= a < F + 24) \/ (F + 32 <= a < F + 32 + 16) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 64).

Lemma digits (fx : FPState) R M :
  getr R (reg 2) = Z_to_bv 64 (S - 128) -> getr R (reg 8) = Z_to_bv 64 S -> getr R (reg 9) = Z_to_bv 64 (S - 128) -> getr R (reg 10) = Z_to_bv 64 F ->
  getr R (reg 20) = Z_to_bv 64 o -> getr R (reg 22) = Z_to_bv 64 v -> getr R (reg 24) = Z_to_bv 64 2147450880 -> pmem S F fl M ->
  exists (fx' : FPState) R' M' d, mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wd a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ 1 <= d <= 10 /\ rbase S o F R' /\ (forall i, In i [3; 4; 27]%nat -> getr R' (reg i) = getr R (reg i))
    /\ L5KA.zeros_at M' (F / 8 + 2147450880 + 4) 2 /\ pmem S F fl M'
    /\ ( (0 <= v /\ msteps RSEGS (st fx R 0xb6270 M) (st fx' R' 0xb64a0 M') /\ getr R' (reg 21) = Z_to_bv 64 d
          /\ getr R' (reg 22) = Z_to_bv 64 (F + 32 + (d - 1)) /\ getr R' (reg 26) = Z_to_bv 64 (F + 32 + (d - 1)))
      \/ (v < 0 /\ msteps RSEGS (st fx R 0xb6270 M) (st fx' R' 0xd5bc4 M') /\ getr R' (reg 1) = Z_to_bv 64 0xb6488 /\ getr R' (reg 10) = Z_to_bv 64 o
          /\ getr R' (reg 21) = Z_to_bv 64 d /\ getr R' (reg 26) = Z_to_bv 64 (F + 32 + d)) ).
Proof.
  intros G2 G8 G9 G10 G20 G22 G24 PM. gpose. pm_open PM.
  pose proof (geom_rng _ _ _ _ GEO) as (Eo8 & EF8 & Qo0 & QF0 & Qo1 & QF1 & QoF).
  assert (A22 : getr R (reg 22) = Z_to_bv 64 (v mod 2 ^ 64)) by (rewrite to_bv_mod; exact G22).
  (let T := type of (PNAFIP3.afnB_conc fx R M (VV 0 0 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNAFIP3.afnB_conc fx R M (VV 0 0 0)) T ltac:(cbn beta iota delta [VV]) ltac:(L5SAR.sc)).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & EX).
  pose proof (PNDG.slt0 v ltac:(clear - Hv; Lia.lia)) as SLT.
  assert (AG1 : forall a, 0 <= a < 2 ^ 64 -> ~ Wd a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRZ1; [exact Ha| intros Y; apply N; left; exact Y| intros Y; apply N; right; left; clear - Y; Lia.lia
                              | intros Y; apply N; right; right; right; clear - Y; Lia.lia]. }
  assert (PM1 : pmem S F fl M1) by (apply (pmem_keep S o F fl M M1 GEO MG1); [intros a Ha; apply AG1; [clear - Ha GF1; Lia.lia| unfold Wd; clear - Ha GF1 GS1 QF0 QF1 GFB GSF; Lia.lia]| exact PM]).
  assert (ZOF : L5.u8_at RSEGS M1 (F / 8 + 2147450884) 0 -> L5.u8_at RSEGS M1 (F / 8 + 2147450885) 0 -> L5KA.zeros_at M1 (F / 8 + 2147450880 + 4) 2).
  { intros U4 U5 i Hi. assert (Ei : i = 0 \/ i = 1) by (clear - Hi; Lia.lia). destruct Ei as [-> | ->].
    - replace (F / 8 + 2147450880 + 4 + 0) with (F / 8 + 2147450884) by (clear; Lia.lia).
      apply (L5ADHR.byte_of_u8 M1 _ 0 U4); [right; clear - QF0; Lia.lia| clear - QF0 QF1; Lia.lia].
    - replace (F / 8 + 2147450880 + 4 + 1) with (F / 8 + 2147450885) by (clear; Lia.lia).
      apply (L5ADHR.byte_of_u8 M1 _ 0 U5); [right; clear - QF0; Lia.lia| clear - QF0 QF1; Lia.lia]. }
  assert (TLc : forall (KSa : list nat),
             (forall x, In x KSa -> getr R1 (reg x) = getr R (reg x)) -> (forall i, In i [2; 3; 4; 8; 9; 20; 22; 24; 27]%nat -> In i KSa) ->
             getr R1 (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) -> getr R1 (reg 19) = Z_to_bv 64 F -> getr R1 (reg 23) = Z_to_bv 64 F -> getr R1 (reg 25) = Z_to_bv 64 (F + 32) ->
             L5.u8_at RSEGS M1 (F / 8 + 2147450884) 0 -> L5.u8_at RSEGS M1 (F / 8 + 2147450885) 0 ->
             rbase S o F R1 /\ getr R1 (reg 22) = Z_to_bv 64 v /\ L5KA.zeros_at M1 (F / 8 + 2147450880 + 4) 2 /\ (forall i, In i [3; 4; 27]%nat -> getr R1 (reg i) = getr R (reg i))).
  { intros KSa KS1 INC C18 C19 C23 C25 U4 U5.
    split; [unfold rbase; rewrite (KS1 2%nat), (KS1 8%nat), (KS1 9%nat), (KS1 20%nat), (KS1 24%nat) by (apply INC; inl); repeat split; assumption|].
    split; [rewrite (KS1 22%nat) by (apply INC; inl); exact G22|]. split; [exact (ZOF U4 U5)|].
    intros i Hi. apply KS1. apply INC. revert i Hi. apply sub_in. vm_compute. reflexivity. }
  assert (FIN : forall (M2 : mem), mem_grows M1 M2 ->
             (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 32 + 16) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
             L5KA.zeros_at M1 (F / 8 + 2147450880 + 4) 2 ->
             mem_grows M M2 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ Wd a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
             /\ L5KA.zeros_at M2 (F / 8 + 2147450880 + 4) 2 /\ pmem S F fl M2).
  { intros M2 MG2 FRZ2 ZS1.
    split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
    split; [intros a Ha Na; rewrite FRZ2; [apply AG1; assumption| exact Ha| intros Y; apply Na; right; right; left; exact Y]|].
    split; [intros i Hi; rewrite FRZ2; [exact (ZS1 i Hi)| clear - Hi QF0 QF1; Lia.lia| clear - Hi QF0 QF1 GFB; Lia.lia]|].
    apply (pmem_keep S o F fl M1 M2 GEO MG2); [intros a Ha; apply FRZ2; clear - Ha GF1; Lia.lia| exact PM1]. }
  destruct EX as [(MS1 & KS1 & TL)|(MS1 & KS1 & TL)].
  - (* [comment removed for export] *)
    assert (SGN : 0 <= bv_unsigned (AX2.edenot (AX2.Env (fun j : nat => match j with 2%nat => Z_to_bv 64 S | 33%nat => Z_to_bv 64 o | 34%nat => Z_to_bv 64 (v mod 2 ^ 64) | 50%nat => Z_to_bv 64 F | 51%nat => Z_to_bv 64 fl | _ => getr R (reg j) end) (fun _ => [])) (AX2.EAlu Instr.ALU_SLT (AX2.EVar 34) (AX2.ELit 0))) <= 0) by cget TL.
    cbn [AX2.edenot AX2.ev] in SGN. rewrite to_bv_mod, SLT in SGN.
    assert (Hv0 : 0 <= v) by (destruct (Z.ltb_spec v 0); [exfalso; clear - SGN; Lia.lia| assumption]).
    assert (C10 : getr R1 (reg 10) = Z_to_bv 64 10) by cget TL. assert (C11 : getr R1 (reg 11) = Z_to_bv 64 14757395259826634752) by cget TL.
    assert (C12 : getr R1 (reg 12) = Z_to_bv 64 254) by cget TL. assert (C14 : getr R1 (reg 14) = Z_to_bv 64 (v mod 2 ^ 64)) by cget TL.
    assert (C18 : getr R1 (reg 18) = Z_to_bv 64 (F / 8 + 2147450880)) by cget TL. assert (C19 : getr R1 (reg 19) = Z_to_bv 64 F) by cget TL.
    assert (C21 : getr R1 (reg 21) = Z_to_bv 64 0) by cget TL. assert (C23 : getr R1 (reg 23) = Z_to_bv 64 F) by cget TL.
    assert (C25 : getr R1 (reg 25) = Z_to_bv 64 (F + 32)) by cget TL.
    assert (U4 : L5.u8_at RSEGS M1 (F / 8 + 2147450884) 0) by cget TL. assert (U5 : L5.u8_at RSEGS M1 (F / 8 + 2147450885) 0) by cget TL.
    clear TL.
    destruct (TLc _ KS1 ltac:(apply sub_in; vm_compute; reflexivity) C18 C19 C23 C25 U4 U5) as (RB1 & B22 & ZS1 & K34).
    rewrite to_bv_mod in C14.
    destruct (pos_loop 10 fx1 R1 M1 v 0 RB1 C10 C11 C12 C14 C21 PM1) as (fx2 & R2 & M2 & d & MS2 & MG2 & FRZ2 & Hd & D21 & RB2 & KS2);
      [change (10 ^ Z.of_nat 10) with (10 ^ 10); clear - Hv0 Hv; Lia.lia| clear - Hv; Lia.lia| clear; Lia.lia| clear; cbn; Lia.lia| clear; Lia.lia|].
    destruct (FIN M2 MG2 FRZ2 ZS1) as (MGa & AGa & ZS2 & PM2).
    destruct (done_fork fx2 R2 M2 d RB2 D21 ltac:(rewrite (KS2 22%nat) by inl; exact B22) ltac:(clear - Hd; cbn in Hd; Lia.lia) PM2) as (fx3 & R3 & RB3 & K3 & E21 & EX).
    exists fx3, R3, M2, d. split; [exact MGa|]. split; [exact AGa|]. split; [clear - Hd; cbn in Hd; Lia.lia|]. split; [exact RB3|].
    split; [intros i Hi; rewrite (K3 i Hi); rewrite (KS2 i) by (revert i Hi; apply sub_in; vm_compute; reflexivity); exact (K34 i Hi)|].
    split; [exact ZS2|]. split; [exact PM2|].
    destruct EX as [(Hv' & MS3 & E22 & E26)|(Hv' & _)]; [| exfalso; clear - Hv' Hv0; Lia.lia].
    left. split; [exact Hv0|]. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|].
    split; [exact E21|]. split; [exact E22| exact E26].
  - (* [comment removed for export] *)
    assert (SGN : 1 <= bv_unsigned (AX2.edenot (AX2.Env (fun j : nat => match j with 2%nat => Z_to_bv 64 S | 33%nat => Z_to_bv 64 o | 34%nat => Z_to_bv 64 (v mod 2 ^ 64) | 50%nat => Z_to_bv 64 F | 51%nat => Z_to_bv 64 fl | _ => getr R (reg j) end) (fun _ => [])) (AX2.EAlu Instr.ALU_SLT (AX2.EVar 34) (AX2.ELit 0))) <= 1) by cget TL.
    cbn [AX2.edenot AX2.ev] in SGN. rewrite to_bv_mod, SLT in SGN.
    assert (Hvn : v < 0) by (destruct (Z.ltb_spec v 0); [assumption| exfalso; clear - SGN; Lia.lia]).
    assert (C10 : getr R1 (reg 10) = Z_to_bv 64 10) by cget TL. assert (C11 : getr R1 (reg 11) = Z_to_bv 64 18446744073709551596) by cget TL.
    assert (C12 : getr R1 (reg 12) = Z_to_bv 64 1717986919) by cget TL. assert (C13 : getr R1 (reg 13) = Z_to_bv 64 254) by cget TL.
    assert (C15 : getr R1 (reg 15) = Z_to_bv 64 (v mod 2 ^ 64)) by cget TL.
    assert (C18 : getr R1 (reg 18) = Z_to_bv 64 (F / 8 + 2147450880)) by cget TL. assert (C19 : getr R1 (reg 19) = Z_to_bv 64 F) by cget TL.
    assert (C21 : getr R1 (reg 21) = Z_to_bv 64 0) by cget TL. assert (C23 : getr R1 (reg 23) = Z_to_bv 64 F) by cget TL.
    assert (C25 : getr R1 (reg 25) = Z_to_bv 64 (F + 32)) by cget TL.
    assert (U4 : L5.u8_at RSEGS M1 (F / 8 + 2147450884) 0) by cget TL. assert (U5 : L5.u8_at RSEGS M1 (F / 8 + 2147450885) 0) by cget TL.
    clear TL.
    destruct (TLc _ KS1 ltac:(apply sub_in; vm_compute; reflexivity) C18 C19 C23 C25 U4 U5) as (RB1 & B22 & ZS1 & K34).
    assert (E34 : v mod 2 ^ 64 = 2 ^ 64 - (- v)).
    { replace v with ((2 ^ 64 - - v) + (-1) * 2 ^ 64) at 1 by (clear; Lia.lia). rewrite Z.mod_add by (clear; Lia.lia). apply Z.mod_small. clear - Hvn Hv. Lia.lia. }
    rewrite E34 in C15.
    assert (C11' : getr R1 (reg 11) = Z_to_bv 64 (-20)) by (rewrite C11; change 18446744073709551596 with ((-20) mod 2 ^ 64); apply to_bv_mod).
    destruct (neg_loop 10 fx1 R1 M1 (- v) 0 RB1 C10 C11' C12 C13 C15 C21 PM1) as (fx2 & R2 & M2 & d & MS2 & MG2 & FRZ2 & Hd & D21 & RB2 & KS2);
      [change (10 ^ Z.of_nat 10) with (10 ^ 10); clear - Hvn Hv; Lia.lia| clear - Hv; Lia.lia| clear; Lia.lia| clear; cbn; Lia.lia| clear; Lia.lia|].
    destruct (FIN M2 MG2 FRZ2 ZS1) as (MGa & AGa & ZS2 & PM2).
    destruct (done_fork fx2 R2 M2 d RB2 D21 ltac:(rewrite (KS2 22%nat) by inl; exact B22) ltac:(clear - Hd; cbn in Hd; Lia.lia) PM2) as (fx3 & R3 & RB3 & K3 & E21 & EX).
    exists fx3, R3, M2, d. split; [exact MGa|]. split; [exact AGa|]. split; [clear - Hd; cbn in Hd; Lia.lia|]. split; [exact RB3|].
    split; [intros i Hi; rewrite (K3 i Hi); rewrite (KS2 i) by (revert i Hi; apply sub_in; vm_compute; reflexivity); exact (K34 i Hi)|].
    split; [exact ZS2|]. split; [exact PM2|].
    destruct EX as [(Hv' & _)|(Hv' & MS3 & E1 & E10 & E27)]; [exfalso; clear - Hv' Hvn; Lia.lia|].
    right. split; [exact Hvn|]. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|].
    split; [exact E1|]. split; [exact E10|]. split; [exact E21| exact E27].
Qed.

End Call.
End PNAFID.
