(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition SS_BASE : Z := 0x1c19c8.
Definition SS_BLK0 : Z := 0x1c19d8.
Definition DP_TAB : Z := 0x1d19d8.

Definition DP_MAP1 : Z := 0x5d19e8.
Definition DP_END : Z := 0x6119f0.

Definition MM : Z := 0xc6a4a7935bd1e995.
Definition MM8 : Z := 0x35253c9ade8f4ca8.
Definition MSEED : Z := 0x9747b28c9747b28c.

Definition bkt (h : Z) : Z := Z.land h 1048575.

Definition hinitw (szw : word) : word :=
wz (Z.lxor (bv_unsigned (wz (bv_unsigned (wz (Z.land (bv_unsigned szw) 4294967295)) * MM8))) MSEED).
Definition hstepw (h w : word) : word :=
let k1 := wz (bv_unsigned w * MM) in
let k2 := wz (Z.lxor (bv_unsigned (wz (bv_unsigned k1 ≫ 47))) (bv_unsigned k1)) in
let k3 := wz (bv_unsigned k2 * MM) in
wz (bv_unsigned (wz (Z.lxor (bv_unsigned k3) (bv_unsigned h))) * MM).
Definition hfinw (h : word) : word :=
let a1 := wz (bv_unsigned (wz (Z.lxor 0 (bv_unsigned h))) * MM) in
let a2 := wz (bv_unsigned a1 ≫ 47) in
let a1' := wz (Z.lxor (bv_unsigned a2) (bv_unsigned a1)) in
let a0 := wz (bv_unsigned a1' * MM) in
let a1'' := wz (bv_unsigned a0 ≫ 47) in
wz (Z.lxor (bv_unsigned a1'') (bv_unsigned a0)).
Definition dhash (ks : list Z) : Z :=
bv_unsigned (hfinw (fold_left hstepw (map wz ks) (hinitw (wz (Z.of_nat (length ks)))))).

Fixpoint lastb (nh : Z -> Z) (b : Z) (k : nat) : Z :=
match k with
| O => 0
| S k' => if Z.eqb (bkt (nh (Z.of_nat k))) b then Z.of_nat k else lastb nh b k'
end.

Lemma lastb_range : forall nh b k, 0 <= lastb nh b k <= Z.of_nat k.
Proof. intros nh b k. induction k as [|k IH]; cbn [lastb]; [lia|]. destruct (Z.eqb _ _); lia. Qed.

Lemma lastb_bkt : forall nh b k, lastb nh b k <> 0 -> bkt (nh (lastb nh b k)) = b.
Proof.
intros nh b k. induction k as [|k IH]; cbn [lastb]; [lia|].
destruct (Z.eqb_spec (bkt (nh (Z.of_nat (S k)))) b); [intros _; assumption| exact IH].
Qed.

Lemma lastb_max : forall nh b k j, lastb nh b k < j <= Z.of_nat k -> bkt (nh j) <> b.
Proof.
intros nh b k. induction k as [|k IH]; cbn [lastb]; intros j Hj; [lia|].
destruct (Z.eqb_spec (bkt (nh (Z.of_nat (S k)))) b); [lia|].
destruct (Z.eq_dec j (Z.of_nat (S k))) as [->|NE]; [exact n|]. apply IH. lia.
Qed.

Lemma lastb_ext : forall nh nh' b k, (forall j, 1 <= j <= Z.of_nat k -> nh' j = nh j) -> lastb nh' b k = lastb nh b k.
Proof.
intros nh nh' b k. induction k as [|k IH]; intros E; cbn [lastb]; [reflexivity|].
rewrite E by lia. rewrite IH by (intros; apply E; lia). reflexivity.
Qed.

Definition zseq (n : Z) : list Z := map Z.of_nat (seq 1 (Z.to_nat n)).

Definition RDepot {BAND : Band} (RE : aentry) (X : rlay) (m : mem) : Prop :=
exists (n tf st h0 junk40 : Z) (nh ns : Z -> Z),

1 <= n /\ 0 <= st <= tf /\ 0 <= tf <= 32 * n
/\ (forall i, 1 <= i <= n -> n <= DEPOT_CAP /\ 0 <= nh i < 2^64)
/\ List.NoDup (map nh (zseq n))

/\ rl_dn X mod 16 = 0 /\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ rl_ssb X mod 8 = 0 /\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ appr_lia (rl_T X) 0x1000 /\ rl_T X + 0x1000 <= band_lo

/\ rw_cells asegs m SS_BASE [C8 (wz tf); C8 (wz junk40); C8 (wz (rl_ssb X)); C4 (wz st)]
/\ (forall b, 0 <= b < 2^20 -> rw_cells asegs m (DP_TAB + 4 * b) [C4 (wz (lastb nh b (Z.to_nat n)))])
/\ rw_cells asegs m DP_N [C4 (wz n)]
/\ rw_cells asegs m DP_MAP1 [C8 (wz (rl_dn X))]
/\ (forall i, 1 <= i <= n ->
rw_cells asegs m (rl_dn X + 16 * i) [C8 (wz (nh i)); C4 (wz (lastb nh (bkt (nh i)) (Z.to_nat (i - 1)))); C4 (wz (ns i))])
/\ hjunk m (rl_dn X + 16 * (n + 1)) (rl_dn X + 0x100000)
/\ hjunk m (rl_ssb X) (rl_ssb X + 0x800000)
/\ rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)].

Lemma zseq_In : forall n i, In i (zseq n) <-> 1 <= i <= n.
Proof.
intros n i. unfold zseq. rewrite in_map_iff. split.
- intros (k & <- & Hk). apply in_seq in Hk. lia.
- intros Hi. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.

Lemma depot_capacity : forall n (h0 : Z) (nh : Z -> Z),
0 <= n -> (forall i, 1 <= i <= n -> n <= DEPOT_CAP) -> List.NoDup (map nh (zseq n)) -> n <= 32000.
Proof.
intros n h0 nh Hn HU ND. unfold DEPOT_CAP in HU. destruct (Z.eq_dec n 0) as [->|NZ]; [lia| exact (HU 1 ltac:(lia))].
Qed.

Lemma depot_n_fun : forall m n n', depot_n asegs m n -> depot_n asegs m n' -> n < 2^32 -> n' < 2^32 -> n = n'.
Proof.
intros m n n' [[[_ B1] _] P1] [[[_ B2] _] P2] U1 U2. cbn [cells_bytes cbytes app] in B1, B2. rewrite app_nil_r in B1, B2.
assert (E : le4 (wz n) = le4 (wz n')).
{ destruct B1 as (_ & _ & H1). destruct B2 as (_ & _ & H2). apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i 4) as [L|G].
- rewrite <- (H1 i), <- (H2 i) by (rewrite length_le4; exact L). reflexivity.
- rewrite !(proj2 (nth_error_None _ _)) by (rewrite length_le4; exact G). reflexivity. }
rewrite !le4_lit in E. apply (f_equal bytes_le_to_Z) in E. rewrite !bytes_le_to_Z_to_le_bytes in E by lia.
change (2 ^ (8 * Z.of_nat 4)) with (2^32) in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.

Definition depot_step (m m' : mem) : Prop := forall n, depot_n asegs m n -> n < 2^32 -> exists n', depot_n asegs m' n' /\ n <= n' <= n + 1.
Lemma depot_step_intro : forall m m' dn, depot_n asegs m dn -> dn < 2^32 -> (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) -> depot_step m m'.
Proof. intros m m' dn H U E n Hn Un. rewrite <- (depot_n_fun m dn n H Hn U Un). exact E. Qed.

Lemma depot_keep_step : forall m1 m2 m3, depot_keep asegs m1 m2 -> depot_step m2 m3 -> depot_step m1 m3.
Proof. intros m1 m2 m3 K S n H U. exact (S n (K n H) U). Qed.

Section Laws.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Lemma RDepot_frame : forall m m', RDepot RE X m -> wmono asegs m m' -> agree_on asegs (fp_RDepot RE X) m m' -> RDepot RE X m'.
Proof.
intros m m' (n & tf & st & h0 & j40 & nh & ns & P1 & P2 & P3 & HU & ND & D1 & D2 & D3 & S1 & S2 & S3 & T1 & T2
& CSS & CTAB & CN & CMAP & CND & JD & JS & TU) WM AG.
assert (AGc : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> fp_RDepot RE X a) -> rw_cells asegs m' A cs)
by (intros A cs H P; eapply rw_cells_agree; [exact AG| exact H| exact P]).
pose proof (depot_capacity n h0 nh ltac:(lia) (fun i Hi => proj1 (HU i Hi)) ND) as CAP.
exists n, tf, st, h0, j40, nh, ns. repeat (split; [assumption|]).
unfold fp_RDepot, in_iv, SS_BASE, DP_TAB, DP_N, DP_MAP1 in *. cbn [fst snd] in *.
split. { apply AGc; [exact CSS|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { intros b Hb. apply AGc; [exact (CTAB b Hb)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { apply AGc; [exact CN|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { apply AGc; [exact CMAP|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { intros i Hi. apply AGc; [exact (CND i Hi)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { eapply hjunk_wmono; eassumption. }
split. { eapply hjunk_wmono; eassumption. }
apply AGc; [exact TU|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia.
Qed.

Lemma RDepot_unw : forall m, RDepot RE X m -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)].
Proof. intros m H. destruct H as (n & tf & st & h0 & j40 & nh & ns & H). do 20 (destruct H as [_ H]). exact H. Qed.

Lemma RDepot_frame_unw : forall m m', rlay_ok RE X -> RDepot RE X m -> wmono asegs m m' ->
agree_on asegs (fun a => fp_RDepot RE X a /\ a <> rl_T X + 3168) m m' ->
rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] -> RDepot RE X m'.
Proof.
intros m m' RL (n & tf & st & h0 & j40 & nh & ns & P1 & P2 & P3 & HU & ND & D1 & D2 & D3 & S1 & S2 & S3 & T1 & T2
& CSS & CTAB & CN & CMAP & CND & JD & JS & TU) WM AG TU'.
pose proof (rlay_pd RE X RL) as PD. pd_pair PD 0 1 DTD. clear PD.
pose proof (depot_capacity n h0 nh ltac:(lia) (fun i Hi => proj1 (HU i Hi)) ND) as CAP.
assert (AGc : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> fp_RDepot RE X a /\ a <> rl_T X + 3168) -> rw_cells asegs m' A cs)
by (intros A cs H P; eapply rw_cells_agree; [exact AG| exact H| exact P]).
pose proof T1 as T1'. rewrite ?KHI_eq in T1'.
exists n, tf, st, h0, j40, nh, ns. repeat (split; [assumption|]).
unfold fp_RDepot, in_iv, SS_BASE, DP_TAB, DP_N, DP_MAP1 in *. cbn [fst snd] in *.
rewrite ?KHI_eq in D2, S2. idtac.
split. { apply AGc; [exact CSS|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { intros b Hb. apply AGc; [exact (CTAB b Hb)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { apply AGc; [exact CN|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { apply AGc; [exact CMAP|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia. }
split. { intros i Hi. apply AGc; [exact (CND i Hi)|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
lia. }
split. { eapply hjunk_wmono; eassumption. }
split. { eapply hjunk_wmono; eassumption. }
exact TU'.
Qed.

End Laws.
