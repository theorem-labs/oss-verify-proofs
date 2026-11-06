(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs Q0Do Qc6I QJFf Q6sh QKTr QJBH QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk QpY2 Q9Ho QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 Q0Do Qc6I QJFf.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QpY2.Mq5 QNQk.Mq1.
Import Q9Ho.Mq0.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation b8 := (Z_to_bv 8).

Definition gzone (p n : Z) : Prop :=
(0x236a0 <= p /\ p + n <= 0x236a9) \/ (0x23700 <= p /\ p + n <= 0x23704) \/ (0x23720 <= p /\ p + n <= 0x23724).

Definition GSHW1 : list byte := [b8 3; b8 249; b8 249; b8 249; b8 0; b8 1; b8 249; b8 249].
Definition GSHW2 : list byte := [b8 4; b8 249; b8 249; b8 249; b8 4; b8 249; b8 249; b8 249].
Definition gsh (m : mem) : Prop := bytes_at asegs m 0x7fffc6d0 GSHW1 /\ bytes_at asegs m 0x7fffc6e0 GSHW2.

Lemma bytes_at_hjunk : forall m A (bs : list byte), bytes_at asegs m A bs -> 0x645000 <= A -> hjunk m A (A + Z.of_nat (length bs)).
Proof.
intros m A bs (B0 & B1 & B2) HA. split; [lia|]. split; [lia|].
intros a Ha. specialize (B2 (Z.to_nat (a - A)) ltac:(lia)). rewrite Z2Nat.id in B2 by lia.
replace (A + (a - A)) with a in B2 by lia. rewrite a_mrd_overlay in B2 by (rewrite wa_unsigned by lia; lia).
destruct (nth_error bs (Z.to_nat (a - A))) as [b|] eqn:E; [exists b; exact B2|].
apply nth_error_None in E. lia.
Qed.

Lemma bytes_at_1 : forall m A (bs : list byte) i b, bytes_at asegs m A bs -> nth_error bs i = Some b -> bytes_at asegs m (A + Z.of_nat i) [b].
Proof.
intros m A bs i b (B0 & B1 & B2) E. pose proof (proj1 (nth_error_Some bs i) ltac:(rewrite E; discriminate)) as L.
split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. assert (j = 0%nat) by lia. subst j. cbn.
rewrite Z.add_0_r. rewrite B2 by exact L. exact E.
Qed.

Lemma gsh_munch : forall m m' W, gsh m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= 0x7fffc6d0 \/ 0x7fffc6e8 <= fst iv) W -> gsh m'.
Proof.
intros m m' W [G1 G2] MU WM HW.
assert (D : forall a n, 0x7fffc6d0 <= a -> a + n <= 0x7fffc6e8 -> disjoint_from W a n).
{ intros a n H1 H2. clear - HW H1 H2. induction HW as [|[lo hi] W' H HW IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
split; (eapply bytes_at_transport; [eassumption| exact MU| apply D; cbn; lia]).
Qed.

Definition ash {BAND : Band} (m : mem) : Prop := Q9Ho.Mq0.ash m /\ gsh m.

Definition szone {BAND : Band} (p n : Z) : Prop :=
(0x10000 <= p /\ p + n <= 0x23080) \/ (band_lo + 64 <= p /\ p + n + 8 <= 2^47) \/ ((0x6435c0 <= p /\ p + n <= 0x643a00) \/ gzone p n).

Lemma ash_munch {BAND : Band} : forall m m' W, ash m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= 0x7fffa000 \/ (0x7fffc6e8 <= fst iv /\ snd iv <= 0x800c06b8) \/ (0x800c0740 <= fst iv /\ snd iv <= SH band_lo) \/ 0x10007fff8000 <= fst iv) W ->
ash m'.
Proof.
intros m m' W [A G] MU WM HW. split.
- eapply Q9Ho.Mq0.ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply gsh_munch; [exact G| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. unfold SH, A_SHADOW_OFS in H. lia.
Qed.

Local Ltac gbyte G i := let X := fresh "X" in pose proof (bytes_at_1 _ _ _ i _ G eq_refl) as X; cbn in X; exact X.

Lemma rng_ok_of_gsh : forall m p n, gsh m -> gzone p n -> 0 <= n -> rng_ok m p n.
Proof.
intros m p n [G1 G2] GZ N0. unfold rng_ok.
assert (W1 : exists w : word, rw_cells asegs m 0x7fffc6d0 [C8 w]) by (apply hjunk_C8; apply (bytes_at_hjunk _ _ _ G1); lia).
assert (W2 : exists w : word, rw_cells asegs m 0x7fffc6e0 [C8 w]) by (apply hjunk_C8; apply (bytes_at_hjunk _ _ _ G2); lia).
pose proof (bytes_at_1 _ _ _ 4%nat _ G1 eq_refl) as S14. pose proof (bytes_at_1 _ _ _ 5%nat _ G1 eq_refl) as S15.
pose proof (bytes_at_1 _ _ _ 0%nat _ G2 eq_refl) as S20. pose proof (bytes_at_1 _ _ _ 4%nat _ G2 eq_refl) as S24.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in S14, S15, S20, S24. rewrite ?Z.add_0_r in S20.
unfold gzone in GZ.
split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
- intros K k Hk Hkn. rewrite SH_eq.
destruct GZ as [(A1 & A2)|[(A1 & A2)|(A1 & A2)]].
+
assert (C : (p / 8 * 8 = 0x236a0 /\ (k = 0 \/ k = 1)) \/ (p / 8 * 8 = 0x236a8 /\ k = 0)) by (Z.div_mod_to_equations; lia).
destruct C as [(E & [-> | ->]) | (E & ->)]; rewrite E.
* exists 0. split; [exact S14| left; reflexivity].
* exists 1. split; [exact S15| right; lia].
* exists 1. split; [exact S15| right; lia].
+ assert (C : p / 8 * 8 = 0x23700 /\ k = 0) by (Z.div_mod_to_equations; lia). destruct C as (E & ->). rewrite E.
exists 4. split; [exact S20| right; lia].
+ assert (C : p / 8 * 8 = 0x23720 /\ k = 0) by (Z.div_mod_to_equations; lia). destruct C as (E & ->). rewrite E.
exists 4. split; [exact S24| right; lia].
- intros K. rewrite !SH_eq.
destruct GZ as [(A1 & A2)|[(A1 & A2)|(A1 & A2)]].
+ replace (8 * ((p / 8 + 2147450880) / 8)) with 0x7fffc6d0 by (Z.div_mod_to_equations; lia).
replace (8 * (((p + n - 1) / 8 + 2147450880) / 8)) with 0x7fffc6d0 by (Z.div_mod_to_equations; lia). split; exact W1.
+ replace (8 * ((p / 8 + 2147450880) / 8)) with 0x7fffc6e0 by (Z.div_mod_to_equations; lia).
replace (8 * (((p + n - 1) / 8 + 2147450880) / 8)) with 0x7fffc6e0 by (Z.div_mod_to_equations; lia). split; exact W2.
+ replace (8 * ((p / 8 + 2147450880) / 8)) with 0x7fffc6e0 by (Z.div_mod_to_equations; lia).
replace (8 * (((p + n - 1) / 8 + 2147450880) / 8)) with 0x7fffc6e0 by (Z.div_mod_to_equations; lia). split; exact W2.
Qed.

Lemma rng_ok_of_ash {BAND : Band} : forall m p n, ash m -> szone p n -> 0 <= n -> rng_ok m p n.
Proof.
intros m p n [A G] SZ N0. unfold szone in SZ.
destruct SZ as [Z1|[Z2|[Z3|GZ]]].
- apply (Q9Ho.Mq0.rng_ok_of_ash _ _ _ A); [left; exact Z1| exact N0].
- apply (Q9Ho.Mq0.rng_ok_of_ash _ _ _ A); [right; left; exact Z2| exact N0].
- apply (Q9Ho.Mq0.rng_ok_of_ash _ _ _ A); [right; right; exact Z3| exact N0].
- apply rng_ok_of_gsh; assumption.
Qed.

Definition ISH {BAND : Band} (m : mem) : Prop := ash m /\ rt_consts_at asegs m /\ shadow_base asegs m.

Lemma ISH_of_AR {BAND : Band} : forall m, Q9Ho.Mq0.ISH m -> gsh m -> ISH m.
Proof. intros m (A & R & S) G. split; [split; assumption | split; assumption]. Qed.
Lemma ISH_to_AR {BAND : Band} : forall m, ISH m -> Q9Ho.Mq0.ISH m.
Proof. intros m ((A & G) & R & S). split; [exact A | split; assumption]. Qed.

Lemma ISH_munch {BAND : Band} : forall m m' W, ISH m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> ISH m'.
Proof.
intros m m' W (A & R & S) MU WM HW.
assert (HW1 : Forall rt_wzone W).
{ eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold rt_wzone. cbn in *. lia. }
split; [| split].
- eapply ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply rt_consts_at_munch; [exact R| exact MU| exact WM| exact HW1].
- eapply shadow_base_munch; [exact S| exact MU| exact HW1].
Qed.

Lemma ISH_munch_app {BAND : Band} : forall m m' W, ISH m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (0x645000 <= fst iv /\ snd iv <= 0x7fff8000) \/ 0x10007fff8000 <= fst iv) W -> ISH m'.
Proof.
intros m m' W (A & R & S) MU WM HW.
assert (HW1 : Forall rt_wzone W).
{ eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold rt_wzone. cbn in *. lia. }
split; [| split].
- eapply ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply rt_consts_at_munch; [exact R| exact MU| exact WM| exact HW1].
- eapply shadow_base_munch; [exact S| exact MU| exact HW1].
Qed.

Lemma szone_sub {BAND : Band} : forall p n p' n', szone p n -> p <= p' -> p' + n' <= p + n -> 0 <= n' -> szone p' n'.
Proof. intros p n p' n' SZ H1 H2 H3. unfold szone, gzone in *. lia. Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbcP_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbcP_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QN4c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QN4c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation b8 := (Z_to_bv 8).

Definition gzone (p n : Z) : Prop :=
(0x23700 <= p /\ p + n <= 0x23709) \/ (0x23760 <= p /\ p + n <= 0x23764) \/ (0x23780 <= p /\ p + n <= 0x23784).

Definition GSHW1 : list byte := [b8 0; b8 1; b8 249; b8 249; b8 5; b8 249; b8 249; b8 249].
Definition GSHW2 : list byte := [b8 6; b8 249; b8 249; b8 249; b8 4; b8 249; b8 249; b8 249].
Definition GSHW3 : list byte := [b8 4; b8 249; b8 249; b8 249; b8 0; b8 1; b8 249; b8 249].
Definition gsh (m : mem) : Prop := bytes_at asegs m 0x7fffc6e0 GSHW1 /\ bytes_at asegs m 0x7fffc6e8 GSHW2 /\ bytes_at asegs m 0x7fffc6f0 GSHW3.

Lemma bytes_at_hjunk : forall m A (bs : list byte), bytes_at asegs m A bs -> 0x647000 <= A -> hjunk m A (A + Z.of_nat (length bs)).
Proof.
intros m A bs (B0 & B1 & B2) HA. split; [lia|]. split; [lia|].
intros a Ha. specialize (B2 (Z.to_nat (a - A)) ltac:(lia)). rewrite Z2Nat.id in B2 by lia.
replace (A + (a - A)) with a in B2 by lia. rewrite a_mrd_overlay in B2 by (rewrite wa_unsigned by lia; lia).
destruct (nth_error bs (Z.to_nat (a - A))) as [b|] eqn:E; [exists b; exact B2|].
apply nth_error_None in E. lia.
Qed.

Lemma bytes_at_1 : forall m A (bs : list byte) i b, bytes_at asegs m A bs -> nth_error bs i = Some b -> bytes_at asegs m (A + Z.of_nat i) [b].
Proof.
intros m A bs i b (B0 & B1 & B2) E. pose proof (proj1 (nth_error_Some bs i) ltac:(rewrite E; discriminate)) as L.
split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj. assert (j = 0%nat) by lia. subst j. cbn.
rewrite Z.add_0_r. rewrite B2 by exact L. exact E.
Qed.

Lemma gsh_munch : forall m m' W, gsh m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= 0x7fffc6e0 \/ 0x7fffc6f8 <= fst iv) W -> gsh m'.
Proof.
intros m m' W (G1 & G2 & G3) MU WM HW.
assert (D : forall a n, 0x7fffc6e0 <= a -> a + n <= 0x7fffc6f8 -> disjoint_from W a n).
{ intros a n H1 H2. clear - HW H1 H2. induction HW as [|[lo hi] W' H HW IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
split; [| split]; (eapply bytes_at_transport; [eassumption| exact MU| apply D; cbn; lia]).
Qed.

Definition ash {BAND : Band} (m : mem) : Prop := Q9Ho.ash m /\ gsh m.

Definition szone {BAND : Band} (p n : Z) : Prop :=
(0x10000 <= p /\ p + n <= 0x230c0) \/ (band_lo + 64 <= p /\ p + n + 8 <= 2^47) \/ ((0x645c80 <= p /\ p + n <= 0x6460c0) \/ gzone p n).

Lemma ash_munch {BAND : Band} : forall m m' W, ash m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= 0x7fffa000 \/ (0x7fffc6f8 <= fst iv /\ snd iv <= 0x800c0b90) \/ (0x800c0c18 <= fst iv /\ snd iv <= SH band_lo) \/ 0x10007fff8000 <= fst iv) W ->
ash m'.
Proof.
intros m m' W [A G] MU WM HW. split.
- eapply Q9Ho.ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply gsh_munch; [exact G| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. unfold SH, A_SHADOW_OFS in H. lia.
Qed.

Local Ltac gbyte G i := let X := fresh "X" in pose proof (bytes_at_1 _ _ _ i _ G eq_refl) as X; cbn in X; exact X.

Lemma rng_ok_of_gsh : forall m p n, gsh m -> gzone p n -> 0 <= n -> rng_ok m p n.
Proof.
intros m p n (G1 & G2 & G3) GZ N0. unfold rng_ok.
assert (W1 : exists w : word, rw_cells asegs m 0x7fffc6e0 [C8 w]) by (apply hjunk_C8; apply (bytes_at_hjunk _ _ _ G1); lia).
assert (W2 : exists w : word, rw_cells asegs m 0x7fffc6e8 [C8 w]) by (apply hjunk_C8; apply (bytes_at_hjunk _ _ _ G2); lia).
assert (W3 : exists w : word, rw_cells asegs m 0x7fffc6f0 [C8 w]) by (apply hjunk_C8; apply (bytes_at_hjunk _ _ _ G3); lia).
pose proof (bytes_at_1 _ _ _ 0%nat _ G1 eq_refl) as S10. pose proof (bytes_at_1 _ _ _ 1%nat _ G1 eq_refl) as S11.
pose proof (bytes_at_1 _ _ _ 4%nat _ G2 eq_refl) as S24. pose proof (bytes_at_1 _ _ _ 0%nat _ G3 eq_refl) as S30.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in S10, S11, S24, S30. rewrite ?Z.add_0_r in S10, S30.
unfold gzone in GZ.
split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
- intros K k Hk Hkn. rewrite SH_eq.
destruct GZ as [(A1 & A2)|[(A1 & A2)|(A1 & A2)]].
+
assert (C : (p / 8 * 8 = 0x23700 /\ (k = 0 \/ k = 1)) \/ (p / 8 * 8 = 0x23708 /\ k = 0)) by (Z.div_mod_to_equations; lia).
destruct C as [(E & [-> | ->]) | (E & ->)]; rewrite E.
* exists 0. split; [exact S10| left; reflexivity].
* exists 1. split; [exact S11| right; lia].
* exists 1. split; [exact S11| right; lia].
+ assert (C : p / 8 * 8 = 0x23760 /\ k = 0) by (Z.div_mod_to_equations; lia). destruct C as (E & ->). rewrite E.
exists 4. split; [exact S24| right; lia].
+ assert (C : p / 8 * 8 = 0x23780 /\ k = 0) by (Z.div_mod_to_equations; lia). destruct C as (E & ->). rewrite E.
exists 4. split; [exact S30| right; lia].
- intros K. rewrite !SH_eq.
destruct GZ as [(A1 & A2)|[(A1 & A2)|(A1 & A2)]].
+ replace (8 * ((p / 8 + 2147450880) / 8)) with 0x7fffc6e0 by (Z.div_mod_to_equations; lia).
replace (8 * (((p + n - 1) / 8 + 2147450880) / 8)) with 0x7fffc6e0 by (Z.div_mod_to_equations; lia). split; exact W1.
+ replace (8 * ((p / 8 + 2147450880) / 8)) with 0x7fffc6e8 by (Z.div_mod_to_equations; lia).
replace (8 * (((p + n - 1) / 8 + 2147450880) / 8)) with 0x7fffc6e8 by (Z.div_mod_to_equations; lia). split; exact W2.
+ replace (8 * ((p / 8 + 2147450880) / 8)) with 0x7fffc6f0 by (Z.div_mod_to_equations; lia).
replace (8 * (((p + n - 1) / 8 + 2147450880) / 8)) with 0x7fffc6f0 by (Z.div_mod_to_equations; lia). split; exact W3.
Qed.

Lemma rng_ok_of_ash {BAND : Band} : forall m p n, ash m -> szone p n -> 0 <= n -> rng_ok m p n.
Proof.
intros m p n [A G] SZ N0. unfold szone in SZ.
destruct SZ as [Z1|[Z2|[Z3|GZ]]].
- apply (Q9Ho.rng_ok_of_ash _ _ _ A); [left; exact Z1| exact N0].
- apply (Q9Ho.rng_ok_of_ash _ _ _ A); [right; left; exact Z2| exact N0].
- apply (Q9Ho.rng_ok_of_ash _ _ _ A); [right; right; exact Z3| exact N0].
- apply rng_ok_of_gsh; assumption.
Qed.

Definition ISH {BAND : Band} (m : mem) : Prop := ash m /\ rt_consts_at asegs m /\ shadow_base asegs m.

Lemma ISH_of_AR {BAND : Band} : forall m, Q9Ho.ISH m -> gsh m -> ISH m.
Proof. intros m (A & R & S) G. split; [split; assumption | split; assumption]. Qed.
Lemma ISH_to_AR {BAND : Band} : forall m, ISH m -> Q9Ho.ISH m.
Proof. intros m ((A & G) & R & S). split; [exact A | split; assumption]. Qed.

Lemma ISH_munch {BAND : Band} : forall m m' W, ISH m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => band_lo <= fst iv) W -> ISH m'.
Proof.
intros m m' W (A & R & S) MU WM HW.
assert (HW1 : Forall rt_wzone W).
{ eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold rt_wzone. cbn in *. lia. }
split; [| split].
- eapply ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply rt_consts_at_munch; [exact R| exact MU| exact WM| exact HW1].
- eapply shadow_base_munch; [exact S| exact MU| exact HW1].
Qed.

Lemma ISH_munch_app {BAND : Band} : forall m m' W, ISH m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (0x647000 <= fst iv /\ snd iv <= 0x7fff8000) \/ 0x10007fff8000 <= fst iv) W -> ISH m'.
Proof.
intros m m' W (A & R & S) MU WM HW.
assert (HW1 : Forall rt_wzone W).
{ eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. unfold rt_wzone. cbn in *. lia. }
split; [| split].
- eapply ash_munch; [exact A| exact MU| exact WM|]. eapply Forall_impl; [| exact HW]. cbv beta. intros [lo hi] H. cbn in *. lia.
- eapply rt_consts_at_munch; [exact R| exact MU| exact WM| exact HW1].
- eapply shadow_base_munch; [exact S| exact MU| exact HW1].
Qed.

Lemma szone_sub {BAND : Band} : forall p n p' n', szone p n -> p <= p' -> p' + n' <= p + n -> 0 <= n' -> szone p' n'.
Proof. intros p n p' n' SZ H1 H2 H3. unfold szone, gzone in *. lia. Qed.
