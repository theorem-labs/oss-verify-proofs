(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QRjH Qpox QsV0 QO3A Q7m0 QSpR QuJV QCPB QH7x QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qpox QsV0 QRjH QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QBxa.Mq2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma low32_zero_sext : low32 (Z_to_bv 64 0) = sext 32 (0 : bv 12).
Proof. apply bv_eq. reflexivity. Qed.

#[using="Type"] Lemma edenot_addw0_r : forall E a,
(bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
edenot E (EAluw ALU_ADD a (ELit 0)) = edenot E a.
Proof.
intros E a Ha. cbn [edenot]. rewrite low32_zero_sext, w_addiw.
change (bv_signed (0 : bv 12)) with 0%Z. apply v_addiw_id. exact Ha.
Qed.

#[using="Type"] Lemma alu32_add_comm : forall x y : bv 32, alu32 ALU_ADD x y = alu32 ALU_ADD y x.
Proof.
intros x y. change (x + y = y + x). apply bv_eq.
rewrite !bv_add_unsigned. f_equal. lia.
Qed.

#[using="Type"] Lemma edenot_addw0_l : forall E a,
(bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
edenot E (EAluw ALU_ADD (ELit 0) a) = edenot E a.
Proof.
intros E a Ha. cbn [edenot]. rewrite alu32_add_comm.
pose proof (edenot_addw0_r E a Ha) as H. cbn [edenot] in H. exact H.
Qed.

#[using="Type"] Lemma edenot_exts4 : forall E a,
(bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
edenot E (EExt true 0 4 a) = edenot E a.
Proof.
intros E a Ha. cbn [edenot]. apply ext_val_sx_id; [lia|].
change (2 ^ (8 * Z.of_nat 4 - 1))%Z with (2 ^ 31)%Z. exact Ha.
Qed.

#[using="Type"] Lemma edenot_extu4 : forall E a,
(bv_unsigned (edenot E a) < 2 ^ 32)%Z ->
edenot E (EExt false 0 4 a) = edenot E a.
Proof.
intros E a Ha. cbn [edenot]. apply ext_val_zx_id.
change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. exact Ha.
Qed.
End FPGEN1.

Ltac intisms E e Hsmall :=
repeat first [ rewrite (edenot_addw0_r E e Hsmall)
| rewrite (edenot_addw0_l E e Hsmall)
| rewrite (edenot_exts4 E e Hsmall) ].
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.

Definition win_out_b (spi : nat) (lo hi ihi : Z) (b : expr) (k n : Z) : bool :=
match b with
| EVar i => Nat.eqb i spi && (Z.leb (k + n) lo || Z.leb hi k)
&& Z.leb (- 2 ^ 40) k && Z.leb (k + n) (2 ^ 40) && Z.leb 0 n
| ELit z => Z.eqb z 0 && Z.leb 0 k && Z.leb 0 n && Z.leb (k + n) ihi
| _ => false
end.

Definition win_ok (E : env) (spi : nat) (lo hi ihi : Z) : Prop :=
(2 ^ 41 <= bv_unsigned (ev E spi))%Z /\ (bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64)%Z
/\ (lo <= hi)%Z /\ (- 2 ^ 40 <= lo)%Z /\ (hi <= 2 ^ 40)%Z
/\ (0 <= ihi)%Z /\ (ihi <= bv_unsigned (ev E spi) + lo)%Z.

#[using="Type"] Lemma win_out_sound : forall E spi lo hi ihi b k n,
win_out_b spi lo hi ihi b k n = true -> win_ok E spi lo hi ihi ->
(0 <= bv_unsigned (edenot E b) + k)%Z
/\ (bv_unsigned (edenot E b) + k < 2 ^ 64 /\ bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z
/\ (0 <= n)%Z
/\ forall x : word,
(bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n)%Z ->
~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z.
Proof.
intros E spi lo hi ihi b k n Hb (W1 & W2 & W3 & W4 & W5 & W6 & W7).
destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate.
- repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
apply Z.eqb_eq in Hb. subst z.
repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
repeat split; try lia.
- repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
apply Nat.eqb_eq in Hb. subst i.
repeat match goal with
| H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
| H : (_ || _)%bool = true |- _ => apply orb_prop in H
end.
cbn [edenot]. repeat split; try lia.
Qed.

Definition entry_out_b (spi : nat) (lo hi ihi : Z) (e : sentry) : bool :=
match e with
| SE (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
end.

Definition log_out_b (spi : nat) (lo hi ihi : Z) (log : list sentry) : bool :=
forallb (entry_out_b spi lo hi ihi) log.

#[using="Type"] Lemma mem_denot_out : forall E M log spi lo hi ihi (x : word),
log_out_b spi lo hi ihi log = true -> win_ok E spi lo hi ihi ->
(bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
mem_denot E M log x = M x.
Proof.
intros E M log spi lo hi ihi x Hb Hw Hx.
induction log as [|[[b k] w v] rest IH]; [reflexivity|].
cbn [log_out_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
cbn [entry_out_b] in He.
destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) He Hw) as (A & B & C & D).
cbn [mem_denot]. rewrite wbytes_outside.
- apply IH. exact Hrest.
- rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
- rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
pose proof (u64_range x).
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k)) as [L|G]; [left; lia|].
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k + Z.of_nat w)) as [L2|G2]; [|right; lia].
exfalso. apply (D x); lia.
Qed.

#[using="Type"] Lemma rdn_mem_denot_out : forall segs E M log spi lo hi ihi (a : word) n,
log_out_b spi lo hi ihi log = true -> win_ok E spi lo hi ihi ->
(bv_unsigned (ev E spi) + lo <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= bv_unsigned (ev E spi) + hi)%Z ->
rdn segs (mem_denot E M log) a n = rdn segs M a n.
Proof.
intros segs E M log spi lo hi ihi a n Hb Hw H1 H2.
destruct Hw as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
apply rdn_agree. intros j Hj. pose proof (u64_range a).
apply (mem_denot_out E M log spi lo hi ihi); [exact Hb | repeat split; assumption |].
rewrite u_small by lia. lia.
Qed.

Definition kentry_out_b (spi : nat) (lo hi ihi : Z) (K : kentry) : bool :=
match K with
| KWord (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
| KZero (SA b k) (ELit n) => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
| KBlob (SA b k) (ELit n) _ => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
| KImg l h => Z.leb h ihi
| KAlign _ _ => true
| KRange _ _ _ => true
| KDisj _ _ _ _ => true
| KWr _ _ => true
| _ => false
end.

Definition kn_cut (spi : nat) (lo hi ihi : Z) (kn : list kentry) : list kentry :=
List.filter (kentry_out_b spi lo hi ihi) kn.

#[using="Type"] Lemma elenZ_lit_small : forall E n, (0 <= n < 2 ^ 64)%Z -> elenZ E (ELit n) = n.
Proof. intros E n Hn. unfold elenZ. cbn [edenot]. apply u_small. lia. Qed.

#[using="Type"] Lemma kentry_cut_sound : forall segs E M M' spi lo hi ihi K,
win_ok E spi lo hi ihi ->
(forall x : word,
~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z -> M' x = M x) ->
mem_grows M M' ->
kentry_ok segs E M K -> kentry_out_b spi lo hi ihi K = true -> kentry_ok segs E M' K.
Proof.
intros segs E M M' spi lo hi ihi K Hw Hag Hg HK Hb.
pose proof Hw as Hw'. destruct Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|a n|a1 n1 a2 n2]; cbn [kentry_out_b] in Hb;
cbn [kentry_ok] in HK |- *; try exact HK.
-
destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) Hb Hw) as (A & B & C & D).
rewrite <- Hr. apply rdn_agree. intros j Hj. apply Hag.
pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
rewrite Hu. apply D. rewrite u_small by lia. lia.
-
destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
destruct HK as (Hfl & Hz).
assert (Hn0 : (0 <= n)%Z).
{ destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
split; [exact Hfl|]. intros i Hi.
destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
apply D. rewrite u_small by lia. lia.
-
destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
destruct HK as (Hfl & Hlen & Hz).
assert (Hn0 : (0 <= n)%Z).
{ destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
rewrite elenZ_lit_small in Hfl, Hlen, Hz |- * by lia.
split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
apply D. rewrite u_small by lia. lia.
-
apply Z.leb_le in Hb. destruct HK as (H0 & H64 & Hnone).
split; [exact H0|]. split; [exact H64|]. intros i Hi.
rewrite Hag; [apply Hnone; exact Hi|]. rewrite u_small by lia. lia.
-
destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
eapply store_ok_mono; [exact Hg|]. apply Hst; assumption.
Qed.

#[using="Type"] Theorem know_cut_sound : forall segs E M M' spi lo hi ihi kn,
win_ok E spi lo hi ihi ->
(forall x : word,
~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z -> M' x = M x) ->
mem_grows M M' ->
know_ok segs E M kn -> know_ok segs E M' (kn_cut spi lo hi ihi kn).
Proof.
intros segs E M M' spi lo hi ihi kn Hw Hag Hg HK. unfold know_ok in *.
induction kn as [|K rest IH]; [constructor|].
apply Forall_cons_iff in HK as [HK1 HK2].
change (kn_cut spi lo hi ihi (K :: rest))
with (if kentry_out_b spi lo hi ihi K then K :: kn_cut spi lo hi ihi rest else kn_cut spi lo hi ihi rest).
destruct (kentry_out_b spi lo hi ihi K) eqn:Hb.
- constructor; [|apply IH; exact HK2]. eapply kentry_cut_sound; eauto.
- apply IH. exact HK2.
Qed.

#[using="Type"] Lemma wbytes_agree_out : forall M (a : word) bs E spi lo hi,
(bv_unsigned (ev E spi) + lo <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned (ev E spi) + hi)%Z ->
(bv_unsigned (ev E spi) + hi <= 2 ^ 64)%Z ->
forall x : word,
~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
wbytes M a bs x = M x.
Proof.
intros M a bs E spi lo hi H1 H2 H3 x Hx. pose proof (u64_range x).
apply wbytes_outside; [lia|].
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a)) as [L|G]; [left; exact L | right].
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [L2|G2]; [|exact G2].
exfalso. apply Hx. lia.
Qed.

#[using="Type"] Lemma krange_of_know : forall segs E M kn i e lo hi,
know_ok segs E M kn -> nth_error kn i = Some (KRange e lo hi) ->
(lo <= bv_unsigned (edenot E e) <= hi)%Z.
Proof.
intros segs E M kn i e lo hi HK Hn.
pose proof (know_nth segs E M kn i _ HK Hn) as H. cbn [kentry_ok] in H. lia.
Qed.
End FPGEN2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (b : expr) (k n : Z) : bool :=
if expr_eqb b ub then (Z.leb (k + n) uk || Z.leb (uk + un) k)%bool
else ranges_apart allkn ub uk un b k n.

#[using="Type"] Lemma apart_b_sound : forall segs E M allkn ub uk un b k n,
know_ok segs E M allkn -> apart_b allkn ub uk un b k n = true ->
((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z).
Proof.
intros segs E M allkn ub uk un b k n HK H. unfold apart_b in H.
destruct (expr_eqb b ub) eqn:Heq.
- apply expr_eqb_eq in Heq. subst b. unfold estart. cbn [a_base a_off].
apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
- eapply ranges_apart_sound; [exact HK | exact H].
Qed.

Definition kn_frame1 (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : list kentry :=
match K with
| KWord (SA b k) w _ => if apart_b allkn ub uk un b k (Z.of_nat w) then [K] else []
| KZero (SA b k) (ELit l) =>
if (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool then
if apart_b allkn ub uk un b k l then [K]
else if expr_eqb b ub then
(if Z.ltb k uk then [KZero (SA b k) (ELit (Z.min l (uk - k)))] else [])
++ (if Z.ltb (uk + un) (k + l) then [KZero (SA b (Z.max k (uk + un))) (ELit (k + l - Z.max k (uk + un)))] else [])
else []
else []
| KZero _ _ => []
| KBlob (SA b k) (ELit l) _ => if (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b allkn ub uk un b k l)%bool then [K] else []
| KBlob _ _ _ => []
| KImg lo hi => if (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b allkn ub uk un (ELit 0) lo (hi - lo))%bool then [K] else []
| KAlign _ _ => [K]
| KRange _ _ _ => [K]
| KDisj _ _ _ _ => [K]
| KWr _ _ => [K]
end.

Definition kn_frame (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
flat_map (kn_frame1 kn ub uk un) kn.

#[using="Type"] Lemma edenot_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma know_ok_frame : forall segs E M M' kn ub uk un,
know_ok segs E M kn -> flat E (SA ub uk) un ->
(forall x : word,
(bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z -> M' x = M x) ->
mem_grows M M' ->
know_ok segs E M' (kn_frame kn ub uk un).
Proof.
intros segs E M M' kn ub uk un HK Hfl OUT GR.
pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
unfold know_ok, kn_frame. apply Forall_forall. intros K' HinF.
apply in_flat_map in HinF as (K & Hin & Hb).
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
assert (APART : forall b k n, apart_b kn ub uk un b k n = true ->
((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
{ intros b k n H. eapply apart_b_sound; [exact HK | exact H]. }
destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
cbn [kn_frame1] in Hb.
-
destruct (apart_b kn ub uk un b k (Z.of_nat w)) eqn:Hap; [|destruct Hb].
destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
rewrite <- Hr. apply rdn_agree. intros j Hj.
pose proof (flat_u E _ _ Hf) as Hub. destruct Hf as (G1 & G2 & G3 & G4).
apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hap); lia.
-
destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
destruct (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool eqn:Hl; [|destruct Hb].
apply andb_prop in Hl as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
cbn [kentry_ok] in HKK. destruct HKK as (Hf & Hz).
assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
rewrite El in *. pose proof Hf as Hf0. destruct Hf as (G1 & G2 & G3 & G4).
destruct (apart_b kn ub uk un b k l) eqn:Hap.
+ destruct Hb as [<-|[]]. cbn [kentry_ok]. rewrite El. split; [exact Hf0|].
intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
rewrite u_small by lia. destruct (APART b k l Hap); lia.
+ destruct (expr_eqb b ub) eqn:Heq; [|destruct Hb].
apply expr_eqb_eq in Heq. subst b.
unfold estart in G1, G2, G4, OUT, Hz |- *. cbn [a_base a_off] in G1, G2, G4, OUT, Hz |- *.
apply in_app_or in Hb. destruct Hb as [Hb|Hb].
* destruct (Z.ltb k uk) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
rewrite u_small by lia. split; [split; [exact G1 | split; [exact G2 | split; lia]]|].
intros i Hi. rewrite OUT; [apply Hz; lia|]. rewrite u_small by lia. lia.
* destruct (Z.ltb (uk + un) (k + l)) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
rewrite u_small by lia. split; [split; [lia | split; [lia | split; lia]]|].
intros i Hi. rewrite OUT; [|rewrite u_small by lia; lia].
replace (bv_unsigned (edenot E ub) + Z.max k (uk + un) + i)%Z
with (bv_unsigned (edenot E ub) + k + (Z.max k (uk + un) - k + i))%Z by lia.
apply Hz. lia.
-
destruct len as [l| | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
destruct (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b kn ub uk un b k l)%bool eqn:Hl; [|destruct Hb].
destruct Hb as [<-|[]].
apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hlen & Hz). split; [exact Hf|]. split; [exact Hlen|].
assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
rewrite u_small by lia. destruct (APART b k l Hap); lia.
-
destruct (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b kn ub uk un (ELit 0) lo (hi - lo))%bool eqn:Hl; [|destruct Hb].
destruct Hb as [<-|[]].
apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl Hhi]. apply andb_prop in Hl as [Hlo Hlh].
apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.leb_le in Hhi.
cbn [kentry_ok] in HKK |- *. destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite OUT; [apply Hnone; exact Hi|].
pose proof (APART (ELit 0) lo (hi - lo)%Z Hap) as AP. unfold estart in AP |- *. cbn [a_base a_off] in AP |- *.
rewrite edenot_lit0 in AP. rewrite u_small by lia. lia.
-  destruct Hb as [<-|[]]. exact HKK.
-  destruct Hb as [<-|[]]. exact HKK.
-
destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
destruct HKK as (Hf & Hst). split; [exact Hf|].
intros d m Hd Hm. eapply store_ok_mono; [exact GR | apply Hst; assumption].
-  destruct Hb as [<-|[]]. exact HKK.
Qed.

#[using="Type"] Lemma zfill_inside : forall (a n : word) M (x : word),
(bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n)%Z ->
zfill a n M x = Some (Z_to_bv 8 0).
Proof.
intros a n M x H. unfold zfill, zmem.
rewrite (proj2 (Z.leb_le _ _) (proj1 H)). rewrite (proj2 (Z.ltb_lt _ _) (proj2 H)). reflexivity.
Qed.

#[using="Type"] Lemma zfill_outside : forall (a n : word) M (x : word),
(bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x)%Z ->
zfill a n M x = M x.
Proof. intros a n M x H. apply zfill_out. exact H. Qed.

#[using="Type"] Lemma know_ok_zfill : forall segs E M kn ub uk un,
know_ok segs E M kn -> flat E (SA ub uk) un -> (0 < un)%Z -> (un < 2 ^ 64)%Z ->
know_ok segs E (zfill (adenot E (SA ub uk)) (Z_to_bv 64 un) M)
(KZero (SA ub uk) (ELit un) :: kn_frame kn ub uk un).
Proof.
intros segs E M kn ub uk un HK Hfl Hpos Hun.
pose proof (flat_u E _ _ Hfl) as Hu. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in F1, F2, F3, F4. cbn [a_base a_off] in F1, F2, F3, F4.
apply know_ok_cons.
- eapply (kzero_intro segs E _ ub (edenot E ub) uk (ELit un) un); [reflexivity | | exact F1 | exact Hpos | exact F4 |].
+ cbn [edenot]. apply u_small. clear -Hpos Hun. lia.
+ intros i Hi. apply zfill_inside. rewrite Hu, !u_small by lia. unfold estart. cbn [a_base a_off]. lia.
- eapply know_ok_frame; [exact HK | exact Hfl | |].
+ intros x Hx. apply zfill_outside. rewrite Hu, u_small by lia. exact Hx.
+ intros x Hx. unfold zfill, zmem. destruct (_ && _)%bool; [discriminate | exact Hx].
Qed.

#[using="Type"] Lemma know_ok_wblob : forall segs E M kn ub uk (k : nat) (bs : list byte),
know_ok segs E M kn -> flat E (SA ub uk) (Z.of_nat (length bs)) ->
eb E k = bs -> (0 < length bs)%nat -> (Z.of_nat (length bs) < 2 ^ 64)%Z ->
know_ok segs E (wbytes M (adenot E (SA ub uk)) bs)
(KBlob (SA ub uk) (ELit (Z.of_nat (length bs))) k :: kn_frame kn ub uk (Z.of_nat (length bs))).
Proof.
intros segs E M kn ub uk k bs HK Hfl Hb Hpos Hsmall.
pose proof (flat_u E _ _ Hfl) as Hu. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in F1, F2, F3, F4. cbn [a_base a_off] in F1, F2, F3, F4.
apply know_ok_cons.
- eapply (kblob_intro segs E _ ub (edenot E ub) uk _ k bs); [reflexivity | exact Hb | | exact F1 | exact F2 | exact F4 |].
+ cbn [edenot]. apply u_small. clear -Hsmall. lia.
+ intros i Hi.
rewrite QBxa.Mq2.wbytes_inside by (rewrite Hu; unfold estart; cbn [a_base a_off]; rewrite ?u_small by lia; lia).
f_equal. f_equal. rewrite Hu, u_small by lia. unfold estart. cbn [a_base a_off]. lia.
- eapply know_ok_frame; [exact HK | exact Hfl | |].
+ intros x Hx. apply QBxa.Mq2.wbytes_outside; rewrite Hu; [unfold estart; cbn [a_base a_off]; lia | exact Hx].
+ apply wbytes_grows.
Qed.

#[using="Type"] Lemma wbytes_nil_id : forall M (a : word), wbytes M a [] = M.
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma rdn_1_of_mem : forall segs M (a : word) (b : byte),
M a = Some b -> rdn segs M a 1 = Some [b].
Proof. intros segs M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma kword1_of_mem : forall segs E M (e : expr) (a : word) off (z : Z),
edenot E e = a -> (0 <= z < 256)%Z ->
(0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + 1 <= 2 ^ 64)%Z ->
M (Z_to_bv 64 (bv_unsigned a + off)) = Some (Z_to_bv 8 z) ->
kentry_ok segs E M (KWord (SA e off) 1 (ELit z)).
Proof.
intros segs E M e a off z He Hz H1 H2 Hm.
eapply (kword_intro segs E M e a off 1 (ELit z) (Z_to_bv 64 z)); try assumption; try reflexivity; try lia.
rewrite (rdn_1_of_mem segs M _ _ Hm). cbn. rewrite u_small by lia. reflexivity.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
