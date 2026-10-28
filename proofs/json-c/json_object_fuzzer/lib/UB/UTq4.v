(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UvXs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UvXs.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition isdig (c : Z) : bool := (48 <=? c) && (c <=? 57).

Section PeNumStrict.
Variables (md : Model) (T : TSet) (F : bvmap 5 word) (fc : bv 32).
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
Variables (m : word -> option byte) (buf : Z) (txt : list byte).
Let L : list byte := txt ++ [b0].
Let len : Z := Z.of_nat (length txt).
Hypothesis MI : mem_inv rsegs m.
Hypothesis TXT : bytes_at rsegs m buf (txt ++ [b0]).
Hypothesis NUM : Forall (fun b => numb b = true) txt.
Hypothesis B0 : 0 <= buf.
Hypothesis BH : buf + Z.of_nat (length txt) + 1 < 2^63.

Definition st (pc : Z) (a1 a2 a3 a4 a5 : word) : machine_state :=
MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).
Hypothesis KOK : forall a1 a2 a3 a4 a5, evt rsegs (RZ rsegs md T) (st 0x22c7c a1 a2 a3 a4 a5).
Hypothesis KREJ : forall a1 a2 a3 a4 a5, evt rsegs (RZ rsegs md T) (st 0x23e18 a1 a2 a3 a4 a5).

#[using="TXT NUM"] Lemma Lat : forall i, 0 <= i <= len ->
exists b : byte, nth_error L (Z.to_nat i) = Some b /\
ov_read_bytes rsegs m (Z_to_bv 64 (buf + i)) 1 = Some [b] /\
(i < len -> numb b = true) /\ (i = len -> bv_unsigned b = 0) /\ (bv_unsigned b <> 0 -> i < len).
Proof.
intros i Hi. subst L len.
destruct (Z_lt_dec i (Z.of_nat (length txt))) as [LT | GE].
- destruct (nth_error txt (Z.to_nat i)) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
assert (HL : nth_error (txt ++ [b0]) (Z.to_nat i) = Some b) by (rewrite nth_error_app1 by (apply nth_error_Some_length in Hb; exact Hb); exact Hb).
exists b. split; [exact HL|]. split; [exact (string_byte _ _ _ _ _ TXT HL ltac:(lia))|].
split; [intros _; exact (proj1 (Forall_forall _ _) NUM b (nth_error_In _ _ Hb))|].
split; [intros E; exfalso; lia | intros _; exact LT].
- assert (Ei : i = Z.of_nat (length txt)) by lia.
assert (HL : nth_error (txt ++ [b0]) (Z.to_nat i) = Some b0).
{ rewrite nth_error_app2 by lia. replace (Z.to_nat i - length txt)%nat with 0%nat by lia. reflexivity. }
exists b0. split; [exact HL|]. split; [exact (string_byte _ _ _ _ _ TXT HL ltac:(lia))|].
split; [intros LT; exfalso; lia|]. split; [intros _; reflexivity | intros NZ; exfalso; apply NZ; reflexivity].
Qed.

#[using="TXT NUM B0 BH"] Lemma loop1 : forall (k : nat) (j : Z) (a2 a3 a4 a5 : word),
len - j <= Z.of_nat k -> 1 <= j <= len ->
(forall (j' : Z) (b : byte) (a1' a4' a5' : word),
j <= j' <= len -> nth_error L (Z.to_nat j') = Some b -> isdig (bv_unsigned b) = false ->
evt rsegs (RZ rsegs md T) (st 0x22b94 a1' (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (buf + j')) a4' a5')) ->
evt rsegs (RZ rsegs md T) (st 0x22b30 (Z_to_bv 64 (buf + j - 1)) a2 a3 a4 a5).
Proof.
induction k as [|k IH]; intros j a2 a3 a4 a5 Hk Hj K.
-
assert (Ej : j = len) by lia.
destruct (Lat j ltac:(lia)) as (b & HL & RD & _ & Z0 & _). specialize (Z0 Ej).
pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR.
unfold st. replace (buf + j) with (buf + j - 1 + 1) in RD by lia.
step. step. if_truex.
step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
step. step. step. step. step.
rewrite <- (zbv_shift64 (bv_unsigned b + -48)). if_falsex. step.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; rewrite Z0; reflexivity].
- destruct (Lat j ltac:(lia)) as (b & HL & RD & NB & Z0 & NZ).
pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR.
unfold st. replace (buf + j) with (buf + j - 1 + 1) in RD by lia.
step. step. if_truex.
step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
step. step. step. step. step.
destruct (Z_lt_dec (bv_unsigned b) 48) as [LT48 | GE48].
+ rewrite <- (zbv_shift64 (bv_unsigned b + -48)). if_falsex. step.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; apply andb_false_iff; left; apply Z.leb_gt; lia].
+ destruct (Z_lt_dec 57 (bv_unsigned b)) as [GT57 | LE57].
* if_falsex. step.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; apply andb_false_iff; right; apply Z.leb_gt; lia].
*
assert (LTj : j < len) by (apply NZ; lia).
if_truex.
replace (buf + j - 1 + 1) with (buf + (j + 1) - 1) by lia.
apply (IH (j + 1)); [lia | lia |]. intros j' b' a1' a4' a5' Hj' HL' ND'. apply (K j' b'); [lia | exact HL' | exact ND'].
Qed.

#[using="TXT NUM B0 BH"] Lemma loop2 : forall (k : nat) (j : Z) (a2 a3 a4 a5 : word),
len - j <= Z.of_nat k -> 1 <= j <= len ->
(forall (j' : Z) (b : byte) (a4' a5' : word),
j <= j' <= len -> nth_error L (Z.to_nat j') = Some b -> isdig (bv_unsigned b) = false ->
evt rsegs (RZ rsegs md T) (st 0x22bf4 (Z_to_bv 64 (buf + j')) (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (buf + j')) a4' a5')) ->
evt rsegs (RZ rsegs md T) (st 0x22bd0 (Z_to_bv 64 (buf + j - 1)) a2 a3 a4 a5).
Proof.
induction k as [|k IH]; intros j a2 a3 a4 a5 Hk Hj K.
- assert (Ej : j = len) by lia.
destruct (Lat j ltac:(lia)) as (b & HL & RD & _ & Z0 & _). specialize (Z0 Ej).
pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR.
unfold st. replace (buf + j) with (buf + j - 1 + 1) in RD by lia.
step. step. if_truex.
step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
step. step. step. step. step.
rewrite <- (zbv_shift64 (bv_unsigned b + -48)). if_falsex.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; rewrite Z0; reflexivity].
- destruct (Lat j ltac:(lia)) as (b & HL & RD & NB & Z0 & NZ).
pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR.
unfold st. replace (buf + j) with (buf + j - 1 + 1) in RD by lia.
step. step. if_truex.
step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
step. step. step. step. step.
destruct (Z_lt_dec (bv_unsigned b) 48) as [LT48 | GE48].
+ rewrite <- (zbv_shift64 (bv_unsigned b + -48)). if_falsex.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; apply andb_false_iff; left; apply Z.leb_gt; lia].
+ destruct (Z_lt_dec 57 (bv_unsigned b)) as [GT57 | LE57].
* if_falsex.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; apply andb_false_iff; right; apply Z.leb_gt; lia].
* assert (LTj : j < len) by (apply NZ; lia).
if_truex.
replace (buf + j - 1 + 1) with (buf + (j + 1) - 1) by lia.
apply (IH (j + 1)); [lia | lia |]. intros j' b' a4' a5' Hj' HL' ND'. apply (K j' b'); [lia | exact HL' | exact ND'].
Qed.

#[using="TXT NUM B0 BH"] Lemma loop3 : forall (k : nat) (j : Z) (a2 a3 a4 a5 : word),
len - j <= Z.of_nat k -> 1 <= j <= len ->
(forall (j' : Z) (b : byte) (a3' a4' : word),
j <= j' <= len -> nth_error L (Z.to_nat j') = Some b -> isdig (bv_unsigned b) = false ->
evt rsegs (RZ rsegs md T) (st 0x22c74 (Z_to_bv 64 (buf + j')) (Z_to_bv 64 (bv_unsigned b)) a3' a4' a5)) ->
evt rsegs (RZ rsegs md T) (st 0x22c54 (Z_to_bv 64 (buf + j - 1)) a2 a3 a4 a5).
Proof.
induction k as [|k IH]; intros j a2 a3 a4 a5 Hk Hj K.
- assert (Ej : j = len) by lia.
destruct (Lat j ltac:(lia)) as (b & HL & RD & _ & Z0 & _). specialize (Z0 Ej).
pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR.
unfold st. replace (buf + j) with (buf + j - 1 + 1) in RD by lia.
step. step. if_truex.
step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
step. step. step. step.
rewrite <- (zbv_shift64 (bv_unsigned b + -48)). if_falsex.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; rewrite Z0; reflexivity].
- destruct (Lat j ltac:(lia)) as (b & HL & RD & NB & Z0 & NZ).
pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR.
unfold st. replace (buf + j) with (buf + j - 1 + 1) in RD by lia.
step. step. if_truex.
step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
step. step. step. step.
destruct (Z_lt_dec (bv_unsigned b) 48) as [LT48 | GE48].
+ rewrite <- (zbv_shift64 (bv_unsigned b + -48)). if_falsex.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; apply andb_false_iff; left; apply Z.leb_gt; lia].
+ destruct (Z_lt_dec 57 (bv_unsigned b)) as [GT57 | LE57].
* if_falsex.
replace (buf + j - 1 + 1) with (buf + j) by lia. apply (K j b); [lia | exact HL | unfold isdig; apply andb_false_iff; right; apply Z.leb_gt; lia].
* assert (LTj : j < len) by (apply NZ; lia).
if_truex.
replace (buf + j - 1 + 1) with (buf + (j + 1) - 1) by lia.
apply (IH (j + 1)); [lia | lia |]. intros j' b' a3' a4' Hj' HL' ND'. apply (K j' b'); [lia | exact HL' | exact ND'].
Qed.

#[using="txt len KOK KREJ"] Lemma j4 : forall (b : byte) (a1 a3 a4 a5 : word),
evt rsegs (RZ rsegs md T) (st 0x22c74 a1 (Z_to_bv 64 (bv_unsigned b)) a3 a4 a5).
Proof.
intros b a1 a3 a4 a5. pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR. unfold st.
destruct (Z.eq_dec (bv_unsigned b) 0) as [Z0 | NZ].
- rewrite Z0. step. if_true. apply KOK.
- step. if_falsex. step. apply KREJ.
Qed.

#[using="TXT NUM B0 BH KOK KREJ"] Lemma j3 : forall (p : Z) (b : byte) (a2 a3 a4 a5 : word),
0 <= p <= len -> nth_error L (Z.to_nat p) = Some b ->
evt rsegs (RZ rsegs md T) (st 0x22c34 (Z_to_bv 64 (buf + p)) a2 a3 a4 a5).
Proof.
intros p b a2 a3 a4 a5 Hp HL. pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR. unfold st.
destruct (Lat p Hp) as (bb & HLb & RD & NB & Z0 & NZ). rewrite HL in HLb. injection HLb as <-.
step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)). step. step. step.
destruct (Z_lt_dec (bv_unsigned b) 48) as [LT48 | GE48].
{ rewrite <- (zbv_shift64 (bv_unsigned b + -48)). if_falsex. step. apply KREJ. }
destruct (Z_lt_dec 57 (bv_unsigned b)) as [GT57 | LE57].
{ if_falsex. step. apply KREJ. }
if_truex.
assert (LTp : p < len) by (apply NZ; lia).
step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)). step. step. if_falsex.
replace (buf + p) with (buf + (p + 1) - 1) by lia.
apply (loop3 (Z.to_nat (len - p) + 1) (p + 1)); [lia | lia |]. intros j' b' a3' a4' Hj' HL' ND'. apply j4.
Qed.

#[using="TXT NUM B0 BH KOK KREJ"] Lemma j2 : forall (j : Z) (b : byte) (a1 a4 a5 : word),
0 <= j <= len -> nth_error L (Z.to_nat j) = Some b -> isdig (bv_unsigned b) = false ->
evt rsegs (RZ rsegs md T) (st 0x22bf4 a1 (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (buf + j)) a4 a5).
Proof.
intros j b a1 a4 a5 Hj HL ND. pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR. unfold st.
destruct (Lat j Hj) as (bb & HLb & RD & NB & Z0 & NZ). rewrite HL in HLb. injection HLb as <-.
pose proof (lor_lt_pow2 (bv_unsigned b) 32 8 ltac:(lia) ltac:(lia)) as LR. change (2^8) with 256 in LR.
pose proof (Z.lor_nonneg (bv_unsigned b) 32) as LR0.
step. rewrite (unsigned_lit (bv_unsigned b)) by lia. step.
destruct (Z.eq_dec (Z.lor (bv_unsigned b) 32) 101) as [E | NE].
-
assert (LTj : j < len) by (apply NZ; intros Z0'; rewrite Z0' in E; discriminate E).
rewrite E. step. if_false.
destruct (Lat (j + 1) ltac:(lia)) as (b2 & HL2 & RD2 & NB2 & Z02 & NZ2).
pose proof (bv_unsigned_in_range 8 b2) as BR2; unfold bv_modulus in BR2; cbn in BR2.
replace (buf + (j + 1)) with (buf + j + 1) in RD2 by lia.
step. step. if_truex.
step. step. change (zxb b2) with (Z_to_bv 64 (bv_unsigned b2)). step. step.
destruct (Z.eq_dec (bv_unsigned b2) 45) as [E45 | N45].
+  rewrite E45. if_true.
assert (LT2 : j + 1 < len) by (apply NZ2; lia).
destruct (Lat (j + 2) ltac:(lia)) as (b3 & HL3 & _).
step. step. if_truex. step.
replace (buf + j + 2) with (buf + (j + 2)) by lia. apply (j3 (j + 2) b3); [lia | exact HL3].
+ if_falsex. step. step.
destruct (Z.eq_dec (bv_unsigned b2) 43) as [E43 | N43].
*  rewrite E43. if_false.
assert (LT2 : j + 1 < len) by (apply NZ2; lia).
destruct (Lat (j + 2) ltac:(lia)) as (b3 & HL3 & _).
step. step. if_truex. step.
replace (buf + j + 2) with (buf + (j + 2)) by lia. apply (j3 (j + 2) b3); [lia | exact HL3].
* if_truex.
replace (buf + j + 1) with (buf + (j + 1)) by lia. apply (j3 (j + 1) b2); [lia | exact HL2].
-
step. if_truex. apply j4.
Qed.

#[using="TXT NUM B0 BH KOK KREJ"] Lemma j1 : forall (j : Z) (b : byte) (a1 a4 a5 : word),
0 <= j <= len -> nth_error L (Z.to_nat j) = Some b -> isdig (bv_unsigned b) = false ->
evt rsegs (RZ rsegs md T) (st 0x22b94 a1 (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (buf + j)) a4 a5).
Proof.
intros j b a1 a4 a5 Hj HL ND. pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn in BR. unfold st.
destruct (Lat j Hj) as (bb & HLb & RD & NB & Z0 & NZ). rewrite HL in HLb. injection HLb as <-.
step.
destruct (Z.eq_dec (bv_unsigned b) 46) as [E46 | N46].
-
assert (LTj : j < len) by (apply NZ; lia).
rewrite E46. step. if_false.
destruct (Lat (j + 1) ltac:(lia)) as (b2 & HL2 & RD2 & NB2 & Z02 & NZ2).
pose proof (bv_unsigned_in_range 8 b2) as BR2; unfold bv_modulus in BR2; cbn in BR2.
replace (buf + (j + 1)) with (buf + j + 1) in RD2 by lia.
step. step. if_truex.
step. step. change (zxb b2) with (Z_to_bv 64 (bv_unsigned b2)). step. step. step.
destruct (Z_lt_dec (bv_unsigned b2) 48) as [LT48 | GE48].
{ rewrite <- (zbv_shift64 (bv_unsigned b2 + -48)). if_falsex. step. apply KREJ. }
destruct (Z_lt_dec 57 (bv_unsigned b2)) as [GT57 | LE57].
{ if_falsex. step. apply KREJ. }
if_truex.
assert (LT2 : j + 1 < len) by (apply NZ2; lia).
step. change (zxb b2) with (Z_to_bv 64 (bv_unsigned b2)). step. step. step. if_falsex.
replace (buf + j + 1) with (buf + (j + 2) - 1) by lia.
apply (loop2 (Z.to_nat (len - j) + 1) (j + 2)); [lia | lia |]. intros j' b' a4' a5' Hj' HL' ND'. apply (j2 j' b'); [lia | exact HL' | exact ND'].
- step. if_truex. apply (j2 j b); [lia | exact HL | exact ND].
Qed.

#[using="len TXT NUM B0 BH KOK KREJ"] Lemma walk : forall (c0 : byte) (a3 a4 a5 : word),
nth_error L 0%nat = Some c0 ->
evt rsegs (RZ rsegs md T) (st 0x22ac4 (Z_to_bv 64 buf) (Z_to_bv 64 (bv_unsigned c0)) a3 a4 a5).
Proof.
intros c0 a3 a4 a5 Hc0. pose proof (bv_unsigned_in_range 8 c0) as CR; unfold bv_modulus in CR; cbn in CR. unfold st.
assert (LEN0 : 0 <= len) by (subst len; lia).
destruct (Lat 0 ltac:(lia)) as (cc & HLc & _ & _ & _ & NZ0). change (Z.to_nat 0) with 0%nat in HLc. rewrite Hc0 in HLc. injection HLc as <-.

assert (INT : forall (n0 : Z) (a2x : word), 0 <= n0 <= len ->
evt rsegs (RZ rsegs md T) (st 0x22adc (Z_to_bv 64 (buf + n0)) a2x (Z_to_bv 64 45) a4 a5)).
{ intros n0 a2x Hn0. unfold st.
destruct (Lat n0 Hn0) as (b1 & HL1 & RD1 & NB1 & Z01 & NZ1).
pose proof (bv_unsigned_in_range 8 b1) as BR1; unfold bv_modulus in BR1; cbn in BR1.
step. change (zxb b1) with (Z_to_bv 64 (bv_unsigned b1)). step. step.
destruct (Z.eq_dec (bv_unsigned b1) 48) as [E48 | N48].
-
assert (LT1 : n0 < len) by (apply NZ1; lia).
rewrite E48. if_false.
destruct (Lat (n0 + 1) ltac:(lia)) as (b2 & HL2 & RD2 & _).
pose proof (bv_unsigned_in_range 8 b2) as BR2; unfold bv_modulus in BR2; cbn in BR2.
replace (buf + (n0 + 1)) with (buf + n0 + 1) in RD2 by lia.
step. step. if_truex.
step. change (zxb b2) with (Z_to_bv 64 (bv_unsigned b2)). step. step. step.
destruct (Z_lt_dec (bv_unsigned b2) 48) as [LT48 | GE48].
{ rewrite <- (zbv_shift64 (bv_unsigned b2 + -48)). if_truex. step. step.
replace (buf + n0 + 1) with (buf + (n0 + 1)) by lia.
apply (j1 (n0 + 1) b2); [lia | exact HL2 | unfold isdig; apply andb_false_iff; left; apply Z.leb_gt; lia]. }
destruct (Z_lt_dec 57 (bv_unsigned b2)) as [GT57 | LE57].
{ if_truex. step. step.
replace (buf + n0 + 1) with (buf + (n0 + 1)) by lia.
apply (j1 (n0 + 1) b2); [lia | exact HL2 | unfold isdig; apply andb_false_iff; right; apply Z.leb_gt; lia]. }
if_falsex. step. apply KREJ.
- if_truex. step. step. step.
destruct (Z_lt_dec (bv_unsigned b1) 49) as [LT49 | GE49].
{ rewrite <- (zbv_shift64 (bv_unsigned b1 + -49)). if_falsex. step. apply KREJ. }
destruct (Z_lt_dec 57 (bv_unsigned b1)) as [GT57 | LE57].
{ if_falsex. step. apply KREJ. }
if_truex.
assert (LT1 : n0 < len) by (apply NZ1; lia).
step. change (zxb b1) with (Z_to_bv 64 (bv_unsigned b1)). step. step. step. if_falsex.
replace (buf + n0) with (buf + (n0 + 1) - 1) by lia.
apply (loop1 (Z.to_nat (len - n0) + 1) (n0 + 1)); [lia | lia |]. intros j' b' a1' a4' a5' Hj' HL' ND'. apply (j1 j' b'); [lia | exact HL' | exact ND']. }

step. step.
destruct (Z.eq_dec (bv_unsigned c0) 45) as [E45 | N45].
- assert (LT0 : 0 < len) by (apply NZ0; lia).
rewrite E45. if_false. step. step. if_truex. step.
apply (INT 1 (Z_to_bv 64 (-1))); lia.
- if_truex.
pose proof (INT 0 (Z_to_bv 64 (bv_unsigned c0)) ltac:(lia)) as I0. rewrite Z.add_0_r in I0. exact I0.
Qed.
End PeNumStrict.

Lemma num_strict :
forall (m : word -> option byte) (buf : Z) (txt : list byte) (c0 : byte) (md : Model) (T : TSet) (F : bvmap 5 word) (fc : bv 32)
(x1 sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
mem_inv rsegs m -> bytes_at rsegs m buf (txt ++ [b0]) -> Forall (fun b => numb b = true) txt ->
nth_error (txt ++ [b0]) 0 = Some c0 -> 0 <= buf -> buf + Z.of_nat (length txt) + 1 < 2^63 ->
(forall a1' a2' a3' a4' a5',
evt rsegs (RZ rsegs md T) (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x22c7c) fc None m (seg_rom rsegs))) ->
(forall a1' a2' a3' a4' a5',
evt rsegs (RZ rsegs md T) (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x23e18) fc None m (seg_rom rsegs))) ->
evt rsegs (RZ rsegs md T) (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 buf) (Z_to_bv 64 (bv_unsigned c0)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x22ac4) fc None m (seg_rom rsegs)).
Proof.
intros until t6. intros MI TXT NUM Hc0 B0 BH KOK KREJ.
pose proof (@walk md T F fc x1 sp gp tp t0 t1 t2 s0 s1 a0 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m buf txt) as W.
unfold st in W. eapply W; clear W; first [exact TXT | exact NUM | exact MI | exact B0 | exact BH | exact KOK | exact KREJ | exact Hc0].
Qed.
