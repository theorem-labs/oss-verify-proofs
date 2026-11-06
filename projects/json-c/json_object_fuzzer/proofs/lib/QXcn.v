(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4g. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition TQ (X : rlay) : Z := rl_T X + 80.
Definition GQ : Z := A_INSTANCE + 888.
Definition QMUT : Z := A_INSTANCE + 880.
Definition IA : Z := 0x0f33c0.
Definition IA_MAP1 : Z := 0x0f33c8.
Definition IA_FLAG : Z := 0x181c48.

Lemma kq_consts : kBatchClass = 24 /\ kBatchBytes = 8192 /\ kBatchCount = 1021
/\ kQMaxSize = 268435456 /\ kQMinSize = 241591905 /\ kQMaxCache = 1048576.
Proof. repeat split; reflexivity. Qed.

Lemma class_size_24 : class_size 24 = 8192.
Proof. reflexivity. Qed.

Definition zbytes (m : mem) (A n : Z) : Prop :=
wr_at asegs m A n /\ forall i, 0 <= i < n -> bytes_at asegs m (A + i) [b8 0].

Definition ia_inv (m : mem) : Prop :=
exists b0 : Z,
rw_cells asegs m IA_FLAG [C1 (b8 b0); C1 (b8 0); C1 (b8 0); C1 (b8 0)] /\ (b0 = 0 \/ b0 = 1)
/\ zbytes m IA_MAP1 0x40000
/\ (b0 = 1 \/ (zbytes m IA 8 /\ zbytes m 0x0133400 0xd80 /\ zbytes m 0x0134180 0x40248 /\ zbytes m 0x1743c8 40)).

Definition qhdr_cells (b1 n' : Z) (id : word) : list cell :=
[C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz n'); C8 id].

Section QChunk.
Context {BAND : Band}.
Variables (m : mem) (lo hi A n : Z).
Let n' := used_size n.
Let rz := A - lo.
Let up := A + round_up n' 8.

Definition qchunk_mem : Prop :=
(16 < rz -> rw_cells asegs m lo [C8 (wz kMagic); C8 (wz (A - 16))] /\ hjunk m (lo + 16) (A - 16))
/\ (exists b1 id, (b1 = 0x11 \/ b1 = 0x91) /\ rw_cells asegs m (A - 16) (qhdr_cells b1 n' id))
/\ hjunk m A hi
/\ (exists sj, rw_cells asegs m (SH lo) [CB (Z.to_nat (rz / 8)) (fas (rz / 8)); CB (Z.to_nat (ngran n')) sj;
CB (Z.to_nat ((hi - up) / 8)) (fas ((hi - up) / 8))])
/\ lo mod 16 = 0 /\ A mod 16 = 0 /\ rz mod 16 = 0 /\ 16 <= rz /\ hi mod 8 = 0 /\ up <= hi /\ 0 <= n
/\ (lowhigh lo (hi - lo) /\ off_hull lo (hi - lo)) /\ hi <= band_lo.
End QChunk.

Definition qptr_rep {BAND : Band} (a : AState) (LB : list ablock) (G : ghost) (RE : aentry) (m : mem) (QA : aptr -> Z) (p : aptr) : Prop :=
match p with
| APrim _ n => exists i, tag_at G (class_of n) i = Some (TQuar p) /\ from_primary n = true
/\ QA p = slot_beg RE (class_of n) i + rz_size n
/\ qchunk_mem m (slot_beg RE (class_of n) i) (slot_beg RE (class_of n) i + class_size (class_of n)) (QA p) n
| ASec mb n => In (mkSec mb (sec_map_size n) n) (as_reg a) /\ ~ sec_live LB (mkSec mb (sec_map_size n) n)
/\ from_primary n = false /\ QA p = mb + kSecUserOff
/\ qchunk_mem m (mb + kPage) (mb + sec_map_size n) (QA p) n
end.

Definition qptrs (q : qcache) : list aptr := concat (map b_chunks (q_list q)).

Definition bwf (b : batch) : Prop :=
b_count b = Z.of_nat (length (b_chunks b)) /\ 1 <= b_count b <= kBatchCount
/\ b_size b = kBatchBytes + fold_right Z.add 0 (map aptr_used (b_chunks b))
/\ Forall (fun p => 0 <= aptr_req p <= 2^26) (b_chunks b).
Definition qwf (q : qcache) : Prop :=
Forall bwf (q_list q) /\ q_bytes q = fold_right Z.add 0 (map b_size (q_list q)).

Definition batch_mem (RE : aentry) (m : mem) (QA : aptr -> Z) (b : batch) (j nx : Z) : Prop :=
let B := slot_beg RE 24 j in
rw_cells asegs m B [C8 (wz nx); C8 (wz (b_size b)); C8 (wz (b_count b))]
/\ u64arr asegs m (B + 24) (map (fun p => wz (QA p - 16)) (b_chunks b))
/\ hjunk m (B + 24 + 8 * b_count b) (B + 8192)
/\ rw_cells asegs m (SH B) [CB 1024%nat (fas 1024)].

Definition q_first (RE : aentry) (J : list Z) : Z := match J with [] => 0 | j :: _ => slot_beg RE 24 j end.
Definition q_last (RE : aentry) (J : list Z) : Z := match J with [] => 0 | _ => slot_beg RE 24 (last J 0) end.

Fixpoint batches_mem_nx (RE : aentry) (m : mem) (QA : aptr -> Z) (bs : list batch) (J : list Z) (fin : Z) : Prop :=
match bs, J with
| [], [] => True
| b :: bs', j :: J' =>
batch_mem RE m QA b j (match J' with [] => fin | j' :: _ => slot_beg RE 24 j' end)
/\ batches_mem_nx RE m QA bs' J' fin
| _, _ => False
end.
Definition batches_mem (RE : aentry) (m : mem) (QA : aptr -> Z) (bs : list batch) (J : list Z) : Prop :=
batches_mem_nx RE m QA bs J 0.

Definition qrep (RE : aentry) (G : ghost) (m : mem) (QA : aptr -> Z) (C : Z) (q : qcache) (J : list Z) : Prop :=
rw_cells asegs m C [C8 (wz (Z.of_nat (length (q_list q)))); C8 (wz (q_first RE J)); C8 (wz (q_last RE J)); C8 (wz (q_bytes q))]
/\ batches_mem RE m QA (q_list q) J
/\ Forall (fun j => tag_at G 24 j = Some TQOwn) J
/\ qwf q.

Lemma batches_mem_nx_length : forall RE m QA bs J fin, batches_mem_nx RE m QA bs J fin -> length bs = length J.
Proof.
intros RE m QA bs. induction bs as [|b bs IH]; intros [|j J] fin H; cbn in H |- *; try tauto.
f_equal. eapply IH. apply H.
Qed.

Definition hd_slot (RE : aentry) (J : list Z) (fin : Z) : Z := match J with [] => fin | j :: _ => slot_beg RE 24 j end.

Lemma batches_mem_nx_app : forall RE m QA bs1 J1 bs2 J2 fin,
batches_mem_nx RE m QA bs1 J1 (hd_slot RE J2 fin) -> batches_mem_nx RE m QA bs2 J2 fin ->
batches_mem_nx RE m QA (bs1 ++ bs2) (J1 ++ J2) fin.
Proof.
intros RE m QA bs1. induction bs1 as [|b bs1 IH]; intros [|j J1] bs2 J2 fin H1 H2; cbn in H1 |- *; try tauto.
destruct H1 as [HB H1]. split; [| apply IH; assumption].
destruct J1 as [|j' J1']; cbn in *; [| exact HB].
destruct bs1; [| destruct H1]. cbn. destruct J2; cbn in HB |- *; exact HB.
Qed.

Lemma batches_mem_nx_app_inv : forall RE m QA bs1 J1 bs2 J2 fin,
length bs1 = length J1 -> batches_mem_nx RE m QA (bs1 ++ bs2) (J1 ++ J2) fin ->
batches_mem_nx RE m QA bs1 J1 (hd_slot RE J2 fin) /\ batches_mem_nx RE m QA bs2 J2 fin.
Proof.
intros RE m QA bs1. induction bs1 as [|b bs1 IH]; intros [|j J1] bs2 J2 fin L H; cbn in L, H |- *; try discriminate; [auto|].
destruct H as [HB H]. destruct (IH J1 bs2 J2 fin ltac:(lia) H) as [H1 H2]. split; [| exact H2]. split; [| exact H1].
destruct J1 as [|j' J1']; cbn in *.
- destruct bs1; [| discriminate]. cbn in HB. destruct J2; exact HB.
- exact HB.
Qed.

Lemma batches_mem_nx_snoc : forall RE m QA bs J b j fin,
batches_mem_nx RE m QA bs J (slot_beg RE 24 j) -> batch_mem RE m QA b j fin ->
batches_mem_nx RE m QA (bs ++ [b]) (J ++ [j]) fin.
Proof. intros. apply batches_mem_nx_app; [exact H| cbn; auto]. Qed.

Lemma batches_mem_nx_snoc_inv : forall RE m QA bs J b j fin,
length bs = length J -> batches_mem_nx RE m QA (bs ++ [b]) (J ++ [j]) fin ->
batches_mem_nx RE m QA bs J (slot_beg RE 24 j) /\ batch_mem RE m QA b j fin.
Proof.
intros RE m QA bs J b j fin L H. destruct (batches_mem_nx_app_inv RE m QA bs J [b] [j] fin L H) as [H1 [H2 _]]. auto.
Qed.

Lemma q_last_snoc : forall RE J j, q_last RE (J ++ [j]) = slot_beg RE 24 j.
Proof. intros RE J j. unfold q_last. destruct (J ++ [j]) eqn:E; [destruct J; discriminate|]. rewrite <- E, last_last. reflexivity. Qed.

Lemma q_first_snoc : forall RE J j, q_first RE (J ++ [j]) = match J with [] => slot_beg RE 24 j | _ => q_first RE J end.
Proof. intros RE [|j0 J] j; reflexivity. Qed.

Lemma bwf_size_lb : forall b, bwf b -> kBatchBytes + 1 <= b_size b.
Proof.
intros b (B1 & B2 & B3 & B4). rewrite B3.
assert (GEN : forall l, Forall (fun p => 0 <= aptr_req p <= 2^26) l -> Z.of_nat (length l) <= fold_right Z.add 0 (map aptr_used l)).
{ induction l as [|p l IH]; intros HF; cbn; [lia|]. inversion HF; subst. specialize (IH ltac:(assumption)). unfold aptr_used, used_size in *. lia. }
specialize (GEN _ B4). pose proof kq_consts as (_ & _ & KC & _). lia.
Qed.

Lemma qwf_length_bound : forall q, qwf q -> (kBatchBytes + 1) * Z.of_nat (length (q_list q)) <= q_bytes q.
Proof.
intros [l qb] [HF HB]. cbn in *. rewrite HB. clear HB. induction l as [|b l IH]; cbn; [lia|].
inversion HF; subst. specialize (IH ltac:(assumption)). pose proof (bwf_size_lb b ltac:(assumption)). lia.
Qed.

Definition qall (pend : list (aptr * Z)) (a : AState) : list aptr :=
map fst pend ++ qptrs (as_tq a) ++ qptrs (as_gq a).

Definition RQuarM {BAND : Band} (rb bt bg : Z) (pend : list (aptr * Z))
(a : AState) (LB : list ablock) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
exists (JT JG : list Z) (QA : aptr -> Z),
qrep RE G m QA (TQ X) (as_tq a) JT
/\ qrep RE G m QA GQ (as_gq a) JG
/\ rw_cells asegs m QMUT [C1 (b8 0); C1 (b8 rb); C1 (b8 0); C1 (b8 0)]
/\ ia_inv m

/\ List.NoDup (JT ++ JG)
/\ (forall j, tag_at G 24 j = Some TQOwn -> In j (JT ++ JG))
/\ (forall c j, tag_at G c j = Some TQOwn -> c = 24)
/\ List.NoDup (qall pend a)
/\ (forall p, In p (qall pend a) -> qptr_rep a LB G RE m QA p)
/\ (forall c i p, tag_at G c i = Some (TQuar p) -> In p (qall pend a) /\ aptr_cls p = c)
/\ Forall (fun pa => QA (fst pa) = snd pa) pend

/\ 0 <= q_bytes (as_tq a) <= bt /\ 0 <= q_bytes (as_gq a) <= bg.

Definition QB : Z := 2^40.
Definition RQuar {BAND : Band} (a : AState) (LB : list ablock) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
RQuarM 0 QB QB [] a LB G RE X m.

Lemma used_size_pos : forall n, 0 <= n -> 1 <= used_size n /\ n <= used_size n.
Proof. intros n Hn. unfold used_size. lia. Qed.

Lemma qchunk_geom {BAND : Band} : forall m lo hi A n, qchunk_mem m lo hi A n ->
lo + 16 <= A /\ A + round_up (used_size n) 8 <= hi /\ (lowhigh lo (hi - lo) /\ off_hull lo (hi - lo)) /\ hi <= band_lo
/\ (A - lo) mod 16 = 0 /\ lo mod 16 = 0 /\ hi mod 8 = 0 /\ 0 <= n
/\ exists q g r, A - lo = 8 * q /\ 2 <= q /\ round_up (used_size n) 8 = 8 * g /\ ngran (used_size n) = g /\ 1 <= g
/\ hi - (A + round_up (used_size n) 8) = 8 * r /\ 0 <= r /\ hi - lo = 8 * (q + g + r).
Proof.
intros m lo hi A n (_ & _ & _ & _ & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
pose proof (used_size_pos n M7) as [U1 U2].
pose proof (ngran_eq (used_size n) ltac:(lia)) as (N1 & N2 & N3).
pose proof (round_up_ge (used_size n) 8 ltac:(lia)) as (R1 & R2 & R3).
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
exists ((A - lo) / 8), (ngran (used_size n)), ((hi - (A + round_up (used_size n) 8)) / 8).
Z.div_mod_to_equations. nia.
Qed.

Section Laws.
Context {BAND : Band}.
Variables (a : AState) (LB : list ablock) (G : ghost) (RE : aentry) (X : rlay).

Local Notation agree := (agree_on asegs).

Lemma zbytes_agree : forall (P : Z -> Prop) m m' A n,
agree P m m' -> zbytes m A n -> (forall x, A <= x < A + n -> P x) -> zbytes m' A n.
Proof.
intros P m m' A n AG [W Z0] HP. split; [eapply wr_at_agree; eauto|].
intros i Hi. eapply bytes_at_agree; [exact AG| apply Z0; exact Hi|]. cbn [length Z.of_nat]. intros x Hx. apply HP. lia.
Qed.

Lemma qchunk_mem_agree : forall (P : Z -> Prop) m m' lo hi A n,
agree P m m' -> qchunk_mem m lo hi A n ->
(forall x, lo <= x < hi -> P x) -> (forall x, SH lo <= x < SH lo + (hi - lo) / 8 -> P x) ->
qchunk_mem m' lo hi A n.
Proof.
intros P m m' lo hi A n AG QM HP HS.
pose proof (qchunk_geom m lo hi A n QM) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & q & g & r & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
destruct QM as (LEFT & (b1 & id & Hb1 & HDR) & JUNK & (sj & SHD) & PURE).
split; [| split; [| split; [| split; [| exact PURE]]]].
- intros Hrz. destruct (LEFT Hrz) as [L1 L2]. split.
+ eapply rw_cells_agree; [exact AG| exact L1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HP. lia.
+ eapply hjunk_agree; [exact AG| exact L2|]. intros x Hx. apply HP. lia.
- exists b1, id. split; [exact Hb1|]. eapply rw_cells_agree; [exact AG| exact HDR|]. intros x Hx. cbn [qhdr_cells cells_size csize Nat.add] in Hx. apply HP. lia.
- eapply hjunk_agree; [exact AG| exact JUNK|]. intros x Hx. apply HP. lia.
- exists sj. eapply rw_cells_agree; [exact AG| exact SHD|]. intros x Hx. apply HS.
cbn [cells_size csize] in Hx. unfold fas in Hx. rewrite !Nat.add_0_r, !Nat2Z.inj_add, !Z2Nat.id in Hx by lia.
rewrite Q1, Q4, Q6, Q8 in *. rewrite !(Z.mul_comm 8), !Z.div_mul in Hx |- * by lia. lia.
Qed.

Lemma batch_mem_agree : forall (P : Z -> Prop) m m' QA b j nx,
agree P m m' -> batch_mem RE m QA b j nx ->
(forall x, in_iv (slot_beg RE 24 j, class_size 24) x -> P x) ->
(forall x, in_sh (slot_beg RE 24 j, class_size 24) x -> P x) ->
bwf b -> batch_mem RE m' QA b j nx.
Proof.
intros P m m' QA b j nx AG (H1 & H2 & H3 & H4) HP HS (B1 & B2 & _). unfold batch_mem. rewrite class_size_24 in HP, HS.
pose proof kq_consts as (_ & _ & KC & _). rewrite KC in B2.
split; [| split; [| split]].
- eapply rw_cells_agree; [exact AG| exact H1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HP. split; cbn [fst snd]; lia.
- eapply u64arr_agree; [exact AG| exact H2|]. intros x Hx. rewrite length_map in Hx. apply HP. split; cbn [fst snd]; lia.
- eapply hjunk_agree; [exact AG| exact H3|]. intros x Hx. apply HP. split; cbn [fst snd]; lia.
- eapply rw_cells_agree; [exact AG| exact H4|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HS. split; cbn [fst snd]; [lia|].
change (8192 / 8) with 1024. lia.
Qed.

Lemma batches_mem_nx_agree : forall (P : Z -> Prop) m m' QA bs J fin,
agree P m m' -> batches_mem_nx RE m QA bs J fin ->
Forall (fun j => forall x, in_iv (slot_beg RE 24 j, class_size 24) x -> P x) J ->
Forall (fun j => forall x, in_sh (slot_beg RE 24 j, class_size 24) x -> P x) J ->
Forall bwf bs -> batches_mem_nx RE m' QA bs J fin.
Proof.
intros P m m' QA bs. induction bs as [|b bs IH]; intros J fin AG H FP FS FB; destruct J as [|j J]; cbn in H |- *; try exact H.
destruct H as [HB H]. inversion FP; inversion FS; inversion FB; subst.
split; [eapply batch_mem_agree; eauto| eapply IH; eauto].
Qed.

Lemma batches_mem_agree : forall (P : Z -> Prop) m m' QA bs J,
agree P m m' -> batches_mem RE m QA bs J ->
Forall (fun j => forall x, in_iv (slot_beg RE 24 j, class_size 24) x -> P x) J ->
Forall (fun j => forall x, in_sh (slot_beg RE 24 j, class_size 24) x -> P x) J ->
Forall bwf bs -> batches_mem RE m' QA bs J.
Proof. unfold batches_mem. intros; eapply batches_mem_nx_agree; eauto. Qed.

Lemma ia_inv_agree : forall (P : Z -> Prop) m m',
agree P m m' -> ia_inv m -> (forall x, IA <= x < 0x1743f8 \/ IA_FLAG <= x < IA_FLAG + 4 -> P x) -> ia_inv m'.
Proof.
intros P m m' AG (b0 & F1 & F2 & F3 & F4) HP. exists b0. unfold IA, IA_FLAG, IA_MAP1 in *.
split; [eapply rw_cells_agree; [exact AG| exact F1|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply HP; right; lia|].
split; [exact F2|].
split; [eapply zbytes_agree; [exact AG| exact F3|]; intros x Hx; apply HP; left; lia|].
destruct F4 as [F4|(Z1 & Z2 & Z3 & Z4)]; [left; exact F4| right].
split; [| split; [| split]]; (eapply zbytes_agree; [exact AG| eassumption|]); intros x Hx; apply HP; left; lia.
Qed.

Lemma qrep_agree : forall (P : Z -> Prop) m m' QA C q J,
agree P m m' -> qrep RE G m QA C q J ->
(forall x, C <= x < C + 32 -> P x) ->
(forall j x, In j J -> in_iv (slot_beg RE 24 j, class_size 24) x -> P x) ->
(forall j x, In j J -> in_sh (slot_beg RE 24 j, class_size 24) x -> P x) ->
qrep RE G m' QA C q J.
Proof.
intros P m m' QA C q J AG (R1 & R2 & R3 & R4) HC HJ HJS. split; [| split; [| split; [exact R3| exact R4]]].
- eapply rw_cells_agree; [exact AG| exact R1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply HC. lia.
- eapply batches_mem_agree; [exact AG| exact R2| | | apply R4].
+ apply List.Forall_forall. intros j Hj x Hx. eapply HJ; eauto.
+ apply List.Forall_forall. intros j Hj x Hx. eapply HJS; eauto.
Qed.

Lemma RQuarM_agree : forall rb bt bg pend m m',
RQuarM rb bt bg pend a LB G RE X m -> agree (fp_RQuar a LB G RE X) m m' -> RQuarM rb bt bg pend a LB G RE X m'.
Proof.
intros rb bt bg pend m m' (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND) AG.
exists JT, JG, QA.

assert (SLOT : forall c j t x, tag_at G c j = Some t -> tag_quar t = true -> in_iv (slot_beg RE c j, class_size c) x -> fp_RQuar a LB G RE X x).
{ intros c j t x Ht Hq Hx. do 5 right; left. exists c, j, t. auto. }
assert (SLOTS : forall c j t x, tag_at G c j = Some t -> tag_quar t = true -> in_sh (slot_beg RE c j, class_size c) x -> fp_RQuar a LB G RE X x).
{ intros c j t x Ht Hq Hx. do 6 right; left. exists c, j, t. auto. }
assert (QREP : forall C q J, (forall x, C <= x < C + 32 -> fp_RQuar a LB G RE X x) -> qrep RE G m QA C q J -> qrep RE G m' QA C q J).
{ intros C q J HC R. pose proof R as (_ & _ & R3 & _). eapply qrep_agree; [exact AG| exact R| exact HC| |].
- intros j x Hj Hx. eapply SLOT; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)| reflexivity| exact Hx].
- intros j x Hj Hx. eapply SLOTS; [exact (proj1 (List.Forall_forall _ _) R3 j Hj)| reflexivity| exact Hx]. }
split; [apply QREP; [| exact HT]; intros x Hx; left; unfold TQ in Hx; split; cbn [fst snd]; lia|].
split; [apply QREP; [| exact HG]; intros x Hx; right; right; left; unfold GQ in Hx; split; cbn [fst snd]; lia|].
split; [eapply rw_cells_agree; [exact AG| exact HM|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; right; left; unfold QMUT in Hx; split; cbn [fst snd]; lia|].
split.
{ eapply ia_inv_agree; [exact AG| exact HI|]. intros x [Hx|Hx]; [do 3 right; left| do 4 right; left]; unfold IA, IA_FLAG in *; split; cbn [fst snd]; lia. }
split; [exact ND|]. split; [exact TQO|]. split; [exact C24|]. split; [exact NDP|]. split; [| split; [exact TQP| split; [exact PQA| exact BND]]].
intros p Hp. pose proof (REP p Hp) as R. destruct p as [id n|mb n]; cbn [qptr_rep] in R |- *.
- destruct R as (i & Ht & Hpr & HQA & QM). exists i. split; [exact Ht|]. split; [exact Hpr|]. split; [exact HQA|].
eapply qchunk_mem_agree; [exact AG| exact QM| |].
+ intros x Hx. eapply SLOT; [exact Ht| reflexivity|]. split; cbn [fst snd]; lia.
+ intros x Hx. eapply SLOTS; [exact Ht| reflexivity|]. split; cbn [fst snd]; [lia|].
replace (slot_beg RE (class_of n) i + class_size (class_of n) - slot_beg RE (class_of n) i) with (class_size (class_of n)) in Hx by lia. lia.
- destruct R as (Hin & Hnl & Hpr & HQA & QM). split; [exact Hin|]. split; [exact Hnl|]. split; [exact Hpr|]. split; [exact HQA|].
eapply qchunk_mem_agree; [exact AG| exact QM| |].
+ intros x Hx. do 7 right; left. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. auto.
+ intros x Hx. do 8 right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req]. split; [exact Hin|]. split; [exact Hnl|].
split; cbn [fst snd]; [lia|]. replace (mb + sec_map_size n - (mb + kPage)) with (sec_map_size n - kPage) in Hx by lia. lia.
Qed.

Lemma sec_live_perm : forall LB1 LB2 e, Permutation LB1 LB2 -> sec_live LB1 e -> sec_live LB2 e.
Proof. intros LB1 LB2 e P [A HA]. exists A. eapply Permutation_in; eauto. Qed.

Lemma RQuarM_ext : forall rb bt bg pend a' LB' G' m, RQuarM rb bt bg pend a LB G RE X m ->
as_tq a' = as_tq a -> as_gq a' = as_gq a -> as_reg a' = as_reg a ->
(forall e, In e (as_reg a) -> (sec_live LB e <-> sec_live LB' e)) -> same_tags tag_quar G G' ->
RQuarM rb bt bg pend a' LB' G' RE X m.
Proof.
intros rb bt bg pend a' LB' G' m (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND) Etq Egq Ereg HL ST.
assert (TQ1 : forall c j, tag_at G c j = Some TQOwn <-> tag_at G' c j = Some TQOwn) by (intros; apply ST; reflexivity).
assert (TQ2 : forall c j p, tag_at G c j = Some (TQuar p) <-> tag_at G' c j = Some (TQuar p)) by (intros; apply ST; reflexivity).
assert (QREP : forall C q J, qrep RE G m QA C q J -> qrep RE G' m QA C q J).
{ intros C q J (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [| exact R4].
apply List.Forall_forall. intros j Hj. apply TQ1. exact (proj1 (List.Forall_forall _ _) R3 j Hj). }
assert (EQA : qall pend a' = qall pend a) by (unfold qall; rewrite Etq, Egq; reflexivity).
exists JT, JG, QA. rewrite Etq, Egq, EQA.
split; [apply QREP; exact HT|]. split; [apply QREP; exact HG|]. split; [exact HM|]. split; [exact HI|]. split; [exact ND|].
split; [intros j Hj; apply TQO; apply TQ1; exact Hj|].
split; [intros c j Hj; apply (C24 c j); apply TQ1; exact Hj|].
split; [exact NDP|]. split.
- intros p Hp. pose proof (REP p Hp) as R. destruct p as [id n|mb n]; cbn [qptr_rep] in R |- *.
+ destruct R as (i & Ht & R). exists i. split; [apply TQ2; exact Ht| exact R].
+ destruct R as (Hin & Hnl & R). rewrite Ereg. split; [exact Hin|]. split; [| exact R]. intros HL'. apply Hnl. apply (HL _ Hin). exact HL'.
- split; [| split; [exact PQA| exact BND]]. intros c i p Ht. apply (TQP c i p). apply TQ2. exact Ht.
Qed.

Lemma RQuarM_perm : forall rb bt bg pend LB' m, RQuarM rb bt bg pend a LB G RE X m -> Permutation LB LB' -> RQuarM rb bt bg pend a LB' G RE X m.
Proof.
intros rb bt bg pend LB' m H P. eapply RQuarM_ext; [exact H| reflexivity| reflexivity| reflexivity| | intros c i t _; tauto].
intros e _. split; apply sec_live_perm; [exact P| apply Permutation_sym; exact P].
Qed.

Lemma RQuar_frame : forall m m', RQuar a LB G RE X m -> wmono asegs m m' -> agree (fp_RQuar a LB G RE X) m m' -> RQuar a LB G RE X m'.
Proof. intros m m' H _ AG. eapply RQuarM_agree; [exact H| exact AG]. Qed.

Lemma RQuar_perm : forall LB' m, RQuar a LB G RE X m -> Permutation LB LB' -> RQuar a LB' G RE X m.
Proof. intros LB' m H P. eapply RQuarM_perm; [exact H| exact P]. Qed.

Lemma RQuar_ext : forall a' LB' G' m, RQuar a LB G RE X m ->
as_tq a' = as_tq a -> as_gq a' = as_gq a -> as_reg a' = as_reg a ->
(forall e, In e (as_reg a) -> (sec_live LB e <-> sec_live LB' e)) -> same_tags tag_quar G G' ->
RQuar a' LB' G' RE X m.
Proof. intros a' LB' G' m H E1 E2 E3 HL ST. eapply RQuarM_ext; [exact H| exact E1| exact E2| exact E3| exact HL| exact ST]. Qed.

Lemma RQuarM_alloc_sec : forall rb bt bg pend a' m mb msz n A,
RQuarM rb bt bg pend a LB G RE X m ->
as_tq a' = as_tq a -> as_gq a' = as_gq a -> as_reg a' = as_reg a ++ [mkSec mb msz n] ->
~ In mb (map se_beg (as_reg a)) ->
RQuarM rb bt bg pend a' ((ASec mb n, A, n) :: LB) G RE X m.
Proof.
intros rb bt bg pend a' m mb msz n A (JT & JG & QA & HT & HG & HM & HI & ND & TQO & C24 & NDP & REP & TQP & PQA & BND) Etq Egq Ereg Hmb.
assert (EQA : qall pend a' = qall pend a) by (unfold qall; rewrite Etq, Egq; reflexivity).
exists JT, JG, QA. rewrite Etq, Egq, EQA.
repeat (split; [assumption|]). split; [| split; [exact TQP| split; [exact PQA| exact BND]]].
intros p Hp. pose proof (REP p Hp) as R. destruct p as [id k|mb' k]; cbn [qptr_rep] in R |- *; [exact R|].
destruct R as (Hin & Hnl & R). rewrite Ereg. split; [apply in_or_app; left; exact Hin|]. split; [| exact R].
intros (A' & HL). cbn [se_beg se_req] in HL. destruct HL as [E|HL].
- injection E; intros; subst. apply Hmb. apply in_map_iff. eexists. split; [| exact Hin]. reflexivity.
- apply Hnl. exists A'. exact HL.
Qed.

Lemma RQuar_alloc_sec : forall a' m mb msz n A,
RQuar a LB G RE X m ->
as_tq a' = as_tq a -> as_gq a' = as_gq a -> as_reg a' = as_reg a ++ [mkSec mb msz n] ->
~ In mb (map se_beg (as_reg a)) ->
RQuar a' ((ASec mb n, A, n) :: LB) G RE X m.
Proof. intros a' m mb msz n A H E1 E2 E3 Hmb. eapply RQuarM_alloc_sec; eauto. Qed.
End Laws.