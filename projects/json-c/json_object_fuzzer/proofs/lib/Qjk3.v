(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qazd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qazd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtMn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition hglob0_rng_P (a : Z) : Prop :=
0x63d78 <= a < 0x63d80 \/ 0x63d98 <= a < 0x63da0 \/ 0x64ee0 <= a < 0x64ee3 \/ 0x64ef0 <= a < 0x64efc \/ 0x65198 <= a < 0x651a0.

Definition hglob0_P (m : word -> option byte) : Prop :=
jc_glob_P m /\ bytes_at rsegs m UTF8REP_ADDR utf8rep
/\ bytes_at rsegs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))).

#[using="Type"] Lemma bytes_at_pointwise : forall segs (m m' : word -> option byte) A bs,
bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> m' (wa a) = m (wa a)) -> bytes_at segs m' A bs.
Proof.
intros segs m m' A bs (H0 & H1 & HB) E. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd. rewrite (E (A + Z.of_nat i)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma rw_cells_pointwise : forall segs (m m' : word -> option byte) A cs,
rw_cells segs m A cs ->
(forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
rw_cells segs m' A cs.
Proof.
intros segs m m' A cs [[WF HB] (W0 & W1 & HW)] E. split; [split; [exact WF|]|].
- eapply bytes_at_pointwise; [exact HB|]. intros a Ha. rewrite cells_bytes_length in Ha by exact WF. apply (proj1 (E a ltac:(lia))).
- split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (E (A + i) ltac:(lia))). apply HW. exact Hi.
Qed.

#[using="Type"] Lemma hglob0_P_pointwise : forall m m' : word -> option byte,
hglob0_P m ->
(forall a, hglob0_rng_P a -> m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None)) ->
hglob0_P m'.
Proof.
intros m m' (([seed G1] & G2 & (vf & G3 & VF)) & U8 & GF) E. unfold hglob0_rng_P in E.
split; [split; [| split]| split].
- exists seed. eapply rw_cells_pointwise; [exact G1|]. intros a Ha. cbn in Ha. apply E. lia.
- eapply rw_cells_pointwise; [exact G2|]. intros a Ha. cbn in Ha. apply E. lia.
- exists vf. split; [| exact VF]. eapply rw_cells_pointwise; [exact G3|]. intros a Ha. cbn in Ha. apply E. lia.
- eapply bytes_at_pointwise; [exact U8|]. intros a Ha. unfold UTF8REP_ADDR in Ha. cbn in Ha. apply (proj1 (E a ltac:(lia))).
- eapply bytes_at_pointwise; [exact GF|]. intros a Ha. unfold GOT_free_userdata in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (proj1 (E a ltac:(lia))).
Qed.

#[using="Type"] Lemma hglob0_P_init : forall m : word -> option byte,
(forall a, hglob0_rng_P a -> m (Z_to_bv 64 a) = None) -> hglob0_P m.
Proof.
intros m NONE. unfold hglob0_rng_P in NONE. split; [| split].
- apply jc_glob_P_init. intros a Ha. apply NONE. lia.
- assert (RW : rw_cells rsegs m UTF8REP_ADDR [CB 3 utf8rep]).
{ eapply (rw_cells_img_gen rsegs m UTF8REP_ADDR utf8rep);
[intros i Hi; apply NONE; unfold UTF8REP_ADDR in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold UTF8REP_ADDR; lia
| unfold UTF8REP_ADDR; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
- assert (RW : rw_cells rsegs m GOT_free_userdata [C8 (Z_to_bv 64 (fn_free_userdata S4F))]).
{ eapply (rw_cells_img_gen rsegs m GOT_free_userdata (cells_bytes [C8 (Z_to_bv 64 (fn_free_userdata S4F))]));
[intros i Hi; apply NONE; unfold GOT_free_userdata in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold GOT_free_userdata; lia
| unfold GOT_free_userdata; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
Qed.

Definition UTF8REP_ADDR_U : Z := 0x66a28.
Definition GOT_free_userdata_U : Z := 0x658c0.

Definition hglob0_rng_U (a : Z) : Prop :=
0x658c0 <= a < 0x658c8 \/ 0x658e0 <= a < 0x658e8 \/ 0x66a28 <= a < 0x66a2b \/ 0x66a38 <= a < 0x66a44 \/ 0x66f20 <= a < 0x66f28.

Definition hglob0_U (m : word -> option byte) : Prop :=
jc_glob_U m /\ bytes_at usegs m UTF8REP_ADDR_U utf8rep
/\ bytes_at usegs m GOT_free_userdata_U (le8 (Z_to_bv 64 (fn_free_userdata U4F))).

#[using="Type"] Lemma hglob0_U_pointwise : forall m m' : word -> option byte,
hglob0_U m ->
(forall a, hglob0_rng_U a -> m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
hglob0_U m'.
Proof.
intros m m' (([seed G1] & G2 & (vf & G3 & VF)) & U8 & GF) E. unfold hglob0_rng_U in E.
split; [split; [| split]| split].
- exists seed. eapply rw_cells_pointwise; [exact G1|]. intros a Ha. cbn in Ha. apply E. lia.
- eapply rw_cells_pointwise; [exact G2|]. intros a Ha. cbn in Ha. apply E. lia.
- exists vf. split; [| exact VF]. eapply rw_cells_pointwise; [exact G3|]. intros a Ha. cbn in Ha. apply E. lia.
- eapply bytes_at_pointwise; [exact U8|]. intros a Ha. unfold UTF8REP_ADDR_U in Ha. cbn in Ha. apply (proj1 (E a ltac:(lia))).
- eapply bytes_at_pointwise; [exact GF|]. intros a Ha. unfold GOT_free_userdata_U in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (proj1 (E a ltac:(lia))).
Qed.

#[using="Type"] Lemma hglob0_U_init : forall m : word -> option byte,
(forall a, hglob0_rng_U a -> m (Z_to_bv 64 a) = None) -> hglob0_U m.
Proof.
intros m NONE. unfold hglob0_rng_U in NONE. split; [| split].
- apply jc_glob_U_init. intros a Ha. apply NONE. lia.
- assert (RW : rw_cells usegs m UTF8REP_ADDR_U [CB 3 utf8rep]).
{ eapply (rw_cells_img_gen usegs m UTF8REP_ADDR_U utf8rep);
[intros i Hi; apply NONE; unfold UTF8REP_ADDR_U in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold UTF8REP_ADDR_U; lia
| unfold UTF8REP_ADDR_U; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
- assert (RW : rw_cells usegs m GOT_free_userdata_U [C8 (Z_to_bv 64 (fn_free_userdata U4F))]).
{ eapply (rw_cells_img_gen usegs m GOT_free_userdata_U (cells_bytes [C8 (Z_to_bv 64 (fn_free_userdata U4F))]));
[intros i Hi; apply NONE; unfold GOT_free_userdata_U in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold GOT_free_userdata_U; lia
| unfold GOT_free_userdata_U; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
Qed.

Definition JO_SDTBL_P : Z := 0x60918.   Definition JO_SDTBL_VAL_P : Z := 0x239ec.
Definition JO_LCONV_P : Z := 0x63c50.   Definition JO_LCONV_VAL_P : Z := 0x10eaf.
Definition JO_GOTUDS_P : Z := 0x63d80.  Definition JO_GOTUDS_VAL_P : Z := 0x24ec0.
Definition JO_GOTSCF_P : Z := 0x63d88.  Definition JO_GOTSCF_VAL_P : Z := 0x25548.

Definition jox_P (m : word -> option byte) : Prop :=
bytes_at rsegs m JO_SDTBL_P (le8 (Z_to_bv 64 JO_SDTBL_VAL_P)) /\ bytes_at rsegs m JO_LCONV_P (le8 (Z_to_bv 64 JO_LCONV_VAL_P))
/\ bytes_at rsegs m JO_GOTUDS_P (le8 (Z_to_bv 64 JO_GOTUDS_VAL_P)) /\ bytes_at rsegs m JO_GOTSCF_P (le8 (Z_to_bv 64 JO_GOTSCF_VAL_P)).
Definition jox_rng_P (a : Z) : Prop := 0x60918 <= a < 0x60920 \/ 0x63c50 <= a < 0x63c58 \/ 0x63d80 <= a < 0x63d90.

Definition hglob_rng_P (a : Z) : Prop :=
0x63d78 <= a < 0x63d80 \/ 0x63d98 <= a < 0x63da0 \/ 0x64ee0 <= a < 0x64ee3 \/ 0x64ef0 <= a < 0x64efc \/ 0x65198 <= a < 0x651a0
\/ 0x60918 <= a < 0x60920 \/ 0x63c50 <= a < 0x63c58 \/ 0x63d80 <= a < 0x63d90.
Definition hglob_P (m : word -> option byte) : Prop := hglob0_P m /\ jox_P m.

#[using="Type"] Lemma jox_P_pointwise : forall m m' : word -> option byte,
jox_P m -> (forall a, jox_rng_P a -> m' (wa a) = m (wa a)) -> jox_P m'.
Proof.
intros m m' (J1 & J2 & J3 & J4) E. unfold jox_rng_P in E.
split; [| split; [| split]].
- eapply bytes_at_pointwise; [exact J1|]. intros a Ha. unfold JO_SDTBL_P in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (E a ltac:(lia)).
- eapply bytes_at_pointwise; [exact J2|]. intros a Ha. unfold JO_LCONV_P in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (E a ltac:(lia)).
- eapply bytes_at_pointwise; [exact J3|]. intros a Ha. unfold JO_GOTUDS_P in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (E a ltac:(lia)).
- eapply bytes_at_pointwise; [exact J4|]. intros a Ha. unfold JO_GOTSCF_P in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (E a ltac:(lia)).
Qed.

#[using="Type"] Lemma hglob_P_pointwise : forall m m' : word -> option byte,
hglob_P m ->
(forall a, hglob_rng_P a -> m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None)) ->
hglob_P m'.
Proof.
intros m m' [G J] E. split.
- eapply hglob0_P_pointwise; [exact G|]. intros a Ha. apply E. unfold hglob_rng_P; unfold hglob0_rng_P in Ha; lia.
- eapply jox_P_pointwise; [exact J|]. intros a Ha. unfold jox_rng_P in Ha. apply (proj1 (E a ltac:(unfold hglob_rng_P; lia))).
Qed.

#[using="Type"] Lemma hglob_P_pres : forall LB SP m m', heap_pres S4L LB SP m m' -> hglob_P m -> hglob_P m'.
Proof.
intros LB SP m m' HPR G. eapply hglob_P_pointwise; [exact G|]. intros a Ha. unfold hglob_rng_P in Ha.
apply (HPR a); [lia|]. right; left. cbn. unfold s4_client_static. lia.
Qed.

#[using="Type"] Lemma hglob_P_munch : forall m m' W,
hglob_P m -> munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => (0x63d90 <= fst iv \/ snd iv <= 0x63d78) /\ (0x63e60 <= fst iv \/ snd iv <= 0x63d98) /\ (0x64ee3 <= fst iv \/ snd iv <= 0x64ee0)
/\ (0x64efc <= fst iv \/ snd iv <= 0x64ef0) /\ (0x651a0 <= fst iv \/ snd iv <= 0x65198)
/\ (0x60920 <= fst iv \/ snd iv <= 0x60918) /\ (0x63c58 <= fst iv \/ snd iv <= 0x63c50)) W ->
hglob_P m'.
Proof.
intros m m' W G MU WM DJ. eapply hglob_P_pointwise; [exact G|]. intros a Ha. split.
- apply MU. rewrite wa_unsigned by (unfold hglob_rng_P in Ha; lia).
clear MU WM G. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in DJ as [D1 DJ]. cbn [fst snd] in D1.
split; [unfold hglob_rng_P in Ha; lia | apply IH; exact DJ].
- intros Hw. apply WM. exact Hw.
Qed.

#[using="Type"] Lemma hglob_P_outside : forall m m' W,
hglob_P m -> munch W m m' -> wmono rsegs m m' -> Forall (fun iv => snd iv <= 0x60000 \/ 0x97000 <= fst iv) W -> hglob_P m'.
Proof.
intros m m' W G MU WM HW. eapply hglob_P_munch; [exact G | exact MU | exact WM |].
eapply Forall_impl; [| exact HW]. intros [lo hi] H. cbn [fst snd] in *. lia.
Qed.

#[using="Type"] Lemma hglob_P_init : forall m : word -> option byte,
(forall a, hglob_rng_P a -> m (Z_to_bv 64 a) = None) -> hglob_P m.
Proof.
intros m NONE. unfold hglob_rng_P in NONE. split.
- apply hglob0_P_init. intros a Ha. apply NONE. unfold hglob0_rng_P in Ha. lia.
- split; [| split; [| split]].
+ assert (RW : rw_cells rsegs m JO_SDTBL_P [C8 (Z_to_bv 64 JO_SDTBL_VAL_P)]).
{ eapply (rw_cells_img_gen rsegs m JO_SDTBL_P (cells_bytes [C8 (Z_to_bv 64 JO_SDTBL_VAL_P)]));
[intros i Hi; apply NONE; unfold JO_SDTBL_P in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold JO_SDTBL_P; lia
| unfold JO_SDTBL_P; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
+ assert (RW : rw_cells rsegs m JO_LCONV_P [C8 (Z_to_bv 64 JO_LCONV_VAL_P)]).
{ eapply (rw_cells_img_gen rsegs m JO_LCONV_P (cells_bytes [C8 (Z_to_bv 64 JO_LCONV_VAL_P)]));
[intros i Hi; apply NONE; unfold JO_LCONV_P in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold JO_LCONV_P; lia
| unfold JO_LCONV_P; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
+ assert (RW : rw_cells rsegs m JO_GOTUDS_P [C8 (Z_to_bv 64 JO_GOTUDS_VAL_P)]).
{ eapply (rw_cells_img_gen rsegs m JO_GOTUDS_P (cells_bytes [C8 (Z_to_bv 64 JO_GOTUDS_VAL_P)]));
[intros i Hi; apply NONE; unfold JO_GOTUDS_P in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold JO_GOTUDS_P; lia
| unfold JO_GOTUDS_P; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
+ assert (RW : rw_cells rsegs m JO_GOTSCF_P [C8 (Z_to_bv 64 JO_GOTSCF_VAL_P)]).
{ eapply (rw_cells_img_gen rsegs m JO_GOTSCF_P (cells_bytes [C8 (Z_to_bv 64 JO_GOTSCF_VAL_P)]));
[intros i Hi; apply NONE; unfold JO_GOTSCF_P in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold JO_GOTSCF_P; lia
| unfold JO_GOTSCF_P; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
Qed.

Definition JO_SDTBL_U : Z := 0x626a0.   Definition JO_SDTBL_VAL_U : Z := 0x24a40.
Definition JO_LCONV_U : Z := 0x65798.   Definition JO_LCONV_VAL_U : Z := 0x10eaf.
Definition JO_GOTUDS_U : Z := 0x658c8.  Definition JO_GOTUDS_VAL_U : Z := 0x261bc.
Definition JO_GOTSCF_U : Z := 0x658d0.  Definition JO_GOTSCF_VAL_U : Z := 0x26968.

Definition jox_U (m : word -> option byte) : Prop :=
bytes_at usegs m JO_SDTBL_U (le8 (Z_to_bv 64 JO_SDTBL_VAL_U)) /\ bytes_at usegs m JO_LCONV_U (le8 (Z_to_bv 64 JO_LCONV_VAL_U))
/\ bytes_at usegs m JO_GOTUDS_U (le8 (Z_to_bv 64 JO_GOTUDS_VAL_U)) /\ bytes_at usegs m JO_GOTSCF_U (le8 (Z_to_bv 64 JO_GOTSCF_VAL_U)).
Definition jox_rng_U (a : Z) : Prop := 0x626a0 <= a < 0x626a8 \/ 0x65798 <= a < 0x657a0 \/ 0x658c8 <= a < 0x658d8.

Definition hglob_rng_U (a : Z) : Prop :=
0x658c0 <= a < 0x658c8 \/ 0x658e0 <= a < 0x658e8 \/ 0x66a28 <= a < 0x66a2b \/ 0x66a38 <= a < 0x66a44 \/ 0x66f20 <= a < 0x66f28
\/ 0x626a0 <= a < 0x626a8 \/ 0x65798 <= a < 0x657a0 \/ 0x658c8 <= a < 0x658d8.
Definition hglob_U (m : word -> option byte) : Prop := hglob0_U m /\ jox_U m.

#[using="Type"] Lemma jox_U_pointwise : forall m m' : word -> option byte,
jox_U m -> (forall a, jox_rng_U a -> m' (wa a) = m (wa a)) -> jox_U m'.
Proof.
intros m m' (J1 & J2 & J3 & J4) E. unfold jox_rng_U in E.
split; [| split; [| split]].
- eapply bytes_at_pointwise; [exact J1|]. intros a Ha. unfold JO_SDTBL_U in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (E a ltac:(lia)).
- eapply bytes_at_pointwise; [exact J2|]. intros a Ha. unfold JO_LCONV_U in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (E a ltac:(lia)).
- eapply bytes_at_pointwise; [exact J3|]. intros a Ha. unfold JO_GOTUDS_U in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (E a ltac:(lia)).
- eapply bytes_at_pointwise; [exact J4|]. intros a Ha. unfold JO_GOTSCF_U in Ha. rewrite length_le8 in Ha. cbn in Ha. apply (E a ltac:(lia)).
Qed.

#[using="Type"] Lemma hglob_U_pointwise : forall m m' : word -> option byte,
hglob_U m ->
(forall a, hglob_rng_U a -> m' (wa a) = m (wa a) /\ (wview usegs m (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
hglob_U m'.
Proof.
intros m m' [G J] E. split.
- eapply hglob0_U_pointwise; [exact G|]. intros a Ha. apply E. unfold hglob_rng_U; unfold hglob0_rng_U in Ha; lia.
- eapply jox_U_pointwise; [exact J|]. intros a Ha. unfold jox_rng_U in Ha. apply (proj1 (E a ltac:(unfold hglob_rng_U; lia))).
Qed.

#[using="Type"] Lemma hglob_U_pres : forall LB SP m m', heap_pres U4L LB SP m m' -> hglob_U m -> hglob_U m'.
Proof.
intros LB SP m m' HPR G. eapply hglob_U_pointwise; [exact G|]. intros a Ha. unfold hglob_rng_U in Ha.
apply (HPR a); [lia|]. right; left. cbn. unfold u4_client_static. lia.
Qed.

#[using="Type"] Lemma hglob_U_munch : forall m m' W,
hglob_U m -> munch W m m' -> wmono usegs m m' ->
Forall (fun iv => (0x658d8 <= fst iv \/ snd iv <= 0x658c0) /\ (0x659a8 <= fst iv \/ snd iv <= 0x658e0) /\ (0x66a2b <= fst iv \/ snd iv <= 0x66a28)
/\ (0x66a44 <= fst iv \/ snd iv <= 0x66a38) /\ (0x66f30 <= fst iv \/ snd iv <= 0x66f20)
/\ (0x626a8 <= fst iv \/ snd iv <= 0x626a0) /\ (0x657a0 <= fst iv \/ snd iv <= 0x65798)) W ->
hglob_U m'.
Proof.
intros m m' W G MU WM DJ. eapply hglob_U_pointwise; [exact G|]. intros a Ha. split.
- apply MU. rewrite wa_unsigned by (unfold hglob_rng_U in Ha; lia).
clear MU WM G. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in DJ as [D1 DJ]. cbn [fst snd] in D1.
split; [unfold hglob_rng_U in Ha; lia | apply IH; exact DJ].
- intros Hw. apply WM. exact Hw.
Qed.

#[using="Type"] Lemma hglob_U_outside : forall m m' W,
hglob_U m -> munch W m m' -> wmono usegs m m' -> Forall (fun iv => snd iv <= 0x62000 \/ 0x98288 <= fst iv) W -> hglob_U m'.
Proof.
intros m m' W G MU WM HW. eapply hglob_U_munch; [exact G | exact MU | exact WM |].
eapply Forall_impl; [| exact HW]. intros [lo hi] H. cbn [fst snd] in *. lia.
Qed.

#[using="Type"] Lemma hglob_U_init : forall m : word -> option byte,
(forall a, hglob_rng_U a -> m (Z_to_bv 64 a) = None) -> hglob_U m.
Proof.
intros m NONE. unfold hglob_rng_U in NONE. split.
- apply hglob0_U_init. intros a Ha. apply NONE. unfold hglob0_rng_U in Ha. lia.
- split; [| split; [| split]].
+ assert (RW : rw_cells usegs m JO_SDTBL_U [C8 (Z_to_bv 64 JO_SDTBL_VAL_U)]).
{ eapply (rw_cells_img_gen usegs m JO_SDTBL_U (cells_bytes [C8 (Z_to_bv 64 JO_SDTBL_VAL_U)]));
[intros i Hi; apply NONE; unfold JO_SDTBL_U in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold JO_SDTBL_U; lia
| unfold JO_SDTBL_U; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
+ assert (RW : rw_cells usegs m JO_LCONV_U [C8 (Z_to_bv 64 JO_LCONV_VAL_U)]).
{ eapply (rw_cells_img_gen usegs m JO_LCONV_U (cells_bytes [C8 (Z_to_bv 64 JO_LCONV_VAL_U)]));
[intros i Hi; apply NONE; unfold JO_LCONV_U in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold JO_LCONV_U; lia
| unfold JO_LCONV_U; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
+ assert (RW : rw_cells usegs m JO_GOTUDS_U [C8 (Z_to_bv 64 JO_GOTUDS_VAL_U)]).
{ eapply (rw_cells_img_gen usegs m JO_GOTUDS_U (cells_bytes [C8 (Z_to_bv 64 JO_GOTUDS_VAL_U)]));
[intros i Hi; apply NONE; unfold JO_GOTUDS_U in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold JO_GOTUDS_U; lia
| unfold JO_GOTUDS_U; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
+ assert (RW : rw_cells usegs m JO_GOTSCF_U [C8 (Z_to_bv 64 JO_GOTSCF_VAL_U)]).
{ eapply (rw_cells_img_gen usegs m JO_GOTSCF_U (cells_bytes [C8 (Z_to_bv 64 JO_GOTSCF_VAL_U)]));
[intros i Hi; apply NONE; unfold JO_GOTSCF_U in Hi; cbn in Hi; lia | vm_compute; reflexivity | unfold JO_GOTSCF_U; lia
| unfold JO_GOTSCF_U; cbn; lia | cbn; repeat split; lia | reflexivity | reflexivity]. }
destruct RW as [[_ HB] _]. exact HB.
Qed.

End RC__1.
