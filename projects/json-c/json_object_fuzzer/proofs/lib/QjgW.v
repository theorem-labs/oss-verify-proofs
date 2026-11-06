(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).
Local Notation agree := (agree_on asegs).

Definition SEC : Z := A_INSTANCE + 64.
Definition SEC_NRES : Z := A_INSTANCE + 112.
Definition SEC_NCH : Z := A_INSTANCE + 120.
Definition SEC_JUNK : Z := A_INSTANCE + 128.
Definition SEC_MUT : Z := A_INSTANCE + 680.
Definition SEC_GST : Z := A_INSTANCE + 688.
Definition SEC_END : Z := A_INSTANCE + 728.

Definition sec_size (n : Z) : Z := needed n + rz_size n.

Definition wjunk (m : mem) (A : Z) (k : nat) : Prop := exists ws : list word, length ws = k /\ u64arr asegs m A ws.

Section Def.
Variables (a : AState) (RE : aentry) (X : rlay) (m : mem).
Let reg := as_reg a.
Let nch := Z.of_nat (length reg).
Let nres := as_nres a.
Let parr := ptrarr_lo RE.

Definition sec_hdr_mem (i : nat) (e : secent) : Prop :=
rw_cells asegs m (se_beg e) [C8 (wz (se_beg e)); C8 (wz (se_size e)); C8 (wz (sec_size (se_req e))); C8 (wz (Z.of_nat i))]
/\ hjunk m (se_beg e + 32) (se_beg e + kPage)
/\ rw_cells asegs m (SH (se_beg e)) [CB 512%nat (fas 512)].

Definition RSec_mem : Prop :=

rw_cells asegs m SEC_NRES [C8 (wz nres); C8 (wz nch)]
/\ wjunk m SEC_JUNK 69
/\ rw_cells asegs m SEC_MUT [C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C4 (wz 0)]
/\ wjunk m SEC_GST 5

/\ u64arr asegs m parr (map (fun e => wz (se_beg e)) reg)
/\ hjunk m (parr + 8 * nch) (parr + 8 * nres)

/\ (forall i e, nth_error reg i = Some e -> sec_hdr_mem i e)

/\ nch <= nres /\ nres <= kMaxNumChunks /\ nres mod kPtrArrBlock = 0.
End Def.

Definition RSec (a : AState) (LB : list ablock) (RE : aentry) (X : rlay) (m : mem) : Prop := RSec_mem a RE m.

Lemma wjunk_agree : forall P m m' A k, agree P m m' -> wjunk m A k -> (forall x, A <= x < A + 8 * Z.of_nat k -> P x) -> wjunk m' A k.
Proof.
intros P m m' A k AG (ws & L & U) HP. exists ws. split; [exact L|]. eapply u64arr_agree; [exact AG| exact U|]. rewrite L. exact HP.
Qed.

Section Laws.
Variables (a : AState) (LB : list ablock) (RE : aentry) (X : rlay).

Lemma RSec_frame : forall m m', RSec a LB RE X m -> wmono asegs m m' -> agree (fp_RSec a RE X) m m' -> RSec a LB RE X m'.
Proof.
intros m m' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) WM AG. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & _).
unfold RSec, RSec_mem.
assert (INST : forall x, A_INSTANCE + 104 <= x < A_INSTANCE + 728 -> fp_RSec a RE X x) by (intros x Hx; left; split; cbn [fst snd]; lia).
assert (PARR : forall x, ptrarr_lo RE <= x < ptrarr_lo RE + 0x800000 -> fp_RSec a RE X x) by (intros x Hx; right; left; split; cbn [fst snd]; lia).
pose proof H8 as (P1 & P2 & P3). unfold kMaxNumChunks in P2. pose proof (Nat2Z.is_nonneg (length (as_reg a))) as P0.
split; [eapply rw_cells_agree; [exact AG| exact H1|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INST; unfold SEC_NRES in Hx; lia|].
split; [eapply wjunk_agree; [exact AG| exact H2|]; intros x Hx; apply INST; unfold SEC_JUNK in Hx; lia|].
split; [eapply rw_cells_agree; [exact AG| exact H3|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply INST; unfold SEC_MUT in Hx; lia|].
split; [eapply wjunk_agree; [exact AG| exact H4|]; intros x Hx; apply INST; unfold SEC_GST in Hx; lia|].
split; [eapply u64arr_agree; [exact AG| exact H5|]; intros x Hx; rewrite length_map in Hx; apply PARR; lia|].
split; [eapply hjunk_agree; [exact AG| exact H6|]; intros x Hx; apply PARR; lia|].
split; [| exact H8].
intros i e Hi. destruct (H7 i e Hi) as (A1 & A2 & A3). pose proof (nth_error_In _ _ Hi) as Hin.
split; [| split].
- eapply rw_cells_agree; [exact AG| exact A1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right; left. exists e. split; [exact Hin| lia].
- eapply hjunk_agree; [exact AG| exact A2|]. intros x Hx. right; right; left. exists e. split; [exact Hin| lia].
- eapply rw_cells_agree; [exact AG| exact A3|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. right; right; right. exists e. split; [exact Hin|].
unfold in_sh. cbn [fst snd]. rewrite KP. change (4096 / 8) with 512. lia.
Qed.

Lemma RSec_ext : forall a' LB' m, RSec a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> RSec a' LB' RE X m.
Proof. intros a' LB' m H E1 E2. unfold RSec, RSec_mem in *. rewrite E1, E2. exact H. Qed.

Lemma RSec_perm : forall LB' m, RSec a LB RE X m -> Permutation LB LB' -> RSec a LB' RE X m.
Proof. intros LB' m H _. exact H. Qed.
End Laws.
