(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import ListNotations.
Open Scope Z_scope.

Definition csfx (src bs : list byte) (q : nat) : Prop :=
length bs = length src /\ forall i, (q <= i < length src)%nat -> nth_error bs i = nth_error src i.

Lemma csfx_init : forall src bs, length bs = length src -> csfx src bs (length src).
Proof. intros src bs H. split; [exact H|]. intros i Hi. lia. Qed.

Lemma csfx_all : forall src bs, csfx src bs 0 -> bs = src.
Proof.
intros src bs [Hl H]. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length src)).
- apply H. lia.
- rewrite (proj2 (nth_error_None bs i)) by lia. rewrite (proj2 (nth_error_None src i)) by lia. reflexivity.
Qed.

Lemma csfx_upd : forall src bs q k xs,
csfx src bs q -> (k <= q)%nat -> (q <= length src)%nat ->
xs = firstn k (skipn (q - k) src) ->
csfx src (upd_bytes bs (q - k) xs) (q - k).
Proof.
intros src bs q k xs [Hl H] Hk Hq Hxs.
assert (Lxs : length xs = k). { subst xs. rewrite length_firstn, length_skipn. lia. }
split.
- rewrite upd_bytes_length by lia. exact Hl.
- intros i Hi. rewrite upd_bytes_nth by lia. rewrite Lxs.
destruct (Nat.leb_spec0 (q - k) i); destruct (Nat.ltb_spec0 i (q - k + k)); cbn [andb]; try lia.
+ subst xs. rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn. f_equal. lia.
+ apply H. lia.
Qed.

Lemma copied_upd' : forall src bs P k xs,
copied src bs P -> (P + k <= length src)%nat -> xs = firstn k (skipn P src) ->
copied src (upd_bytes bs P xs) (P + k).
Proof.
intros src bs P k xs HC Hk Hxs.
assert (Lxs : length xs = k). { subst xs. rewrite length_firstn, length_skipn. lia. }
rewrite <- Lxs. apply copied_upd; [exact HC | rewrite Lxs; symmetry; exact Hxs | lia].
Qed.

Lemma le8_ld : forall w : list byte, length w = 8%nat -> le8 (bv_extract 0 64 (le_bytes_to_word w)) = w.
Proof.
intros w Hw. rewrite <- store_bytes_8'. rewrite load8_le_val by exact Hw.
rewrite <- bytes_le_to_Z_le_val. rewrite <- Hw. apply Z_to_le_bytes_to_Z.
Qed.

Section WithSegs.
Variable segs : list MemImageType.Segment.
Variables (S D n : Z) (src : list byte) (m0 : word -> option byte).
Hypothesis LEN : length src = Z.to_nat n.
Hypothesis NB : 0 <= n.

Definition fwd_inv (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
bytes_at segs m1 (S + P) (skipn (Z.to_nat P) src) /\
mem_inv segs m1 /\ munch [(D, D + n)] m0 m1 /\ wmono segs m0 m1.

Definition bwd_inv (m1 : word -> option byte) (bs : list byte) (Q : Z) : Prop :=
u8arr segs m1 D bs /\ csfx src bs (Z.to_nat Q) /\
bytes_at segs m1 S (firstn (Z.to_nat Q) src) /\
mem_inv segs m1 /\ munch [(D, D + n)] m0 m1 /\ wmono segs m0 m1.

#[using="LEN"] Lemma fwd_read : forall m1 bs P (k : nat) a,
fwd_inv m1 bs P -> 0 <= P -> P + Z.of_nat k <= n -> a = wa (S + P) ->
ov_read_bytes segs m1 a k = Some (firstn k (skipn (Z.to_nat P) src)).
Proof.
intros m1 bs P k a (_ & _ & SRC & _) HP Hk ->.
pose proof (bytes_at_read segs m1 (S + P) (skipn (Z.to_nat P) src) 0 k SRC ltac:(lia)) as R.
rewrite length_skipn, LEN in R. specialize (R ltac:(lia)).
rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. exact R.
Qed.

#[using="LEN"] Lemma fwd_store : forall m1 bs P (k : nat) xs a,
fwd_inv m1 bs P -> D <= S -> 0 <= P -> P + Z.of_nat k <= n -> 0 <= D -> D + n <= 2^64 ->
xs = firstn k (skipn (Z.to_nat P) src) -> a = wa (D + P) ->
store_ok segs m1 a k = true /\
fwd_inv (write_to_mem m1 a xs) (upd_bytes bs (Z.to_nat P) xs) (P + Z.of_nat k).
Proof.
intros m1 bs P k xs a (DST & CP & SRC & MI & MU & WM) DS HP Hk D0 Dn Hxs ->.
pose proof (proj1 CP) as Lbs.
assert (Lxs : length xs = k). { subst xs. rewrite length_firstn, length_skipn, LEN. lia. }
split. { eapply (u8arr_store_ok_n segs m1 D bs P k); [exact DST | lia | rewrite Lbs, LEN; lia | reflexivity]. }
split. { apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN, Lxs. lia. }
split. { replace (Z.to_nat (P + Z.of_nat k)) with (Z.to_nat P + k)%nat by lia. apply copied_upd'; [exact CP | rewrite LEN; lia | exact Hxs]. }
split.
{
assert (SRC' : bytes_at segs m1 (S + (P + Z.of_nat k)) (skipn (Z.to_nat (P + Z.of_nat k)) src)).
{ rewrite <- (firstn_skipn k (skipn (Z.to_nat P) src)) in SRC. apply bytes_at_app in SRC. destruct SRC as [_ SRC].
rewrite length_firstn, length_skipn, LEN, skipn_skipn in SRC.
replace (S + P + Z.of_nat (Nat.min k (Z.to_nat n - Z.to_nat P))) with (S + (P + Z.of_nat k)) in SRC by lia.
replace (k + Z.to_nat P)%nat with (Z.to_nat (P + Z.of_nat k)) in SRC by lia. exact SRC. }
apply bytes_at_write_other; [exact SRC' | lia | rewrite Lxs; lia |]. rewrite Lxs, length_skipn, LEN. lia. }
split. { apply mem_inv_store; [exact MI|]. rewrite Lxs. eapply (u8arr_store_ok_n segs m1 D bs P k); [exact DST | lia | rewrite Lbs, LEN; lia | reflexivity]. }
split. { apply munch_write; [exact MU | lia | rewrite Lxs; lia |]. cbn [inside]. left. rewrite Lxs. lia. }
apply wmono_write. exact WM.
Qed.

#[using="LEN"] Lemma bwd_read : forall m1 bs Q (k : nat) a,
bwd_inv m1 bs Q -> Z.of_nat k <= Q -> Q <= n -> a = wa (S + (Q - Z.of_nat k)) ->
ov_read_bytes segs m1 a k = Some (firstn k (skipn (Z.to_nat (Q - Z.of_nat k)) src)).
Proof.
intros m1 bs Q k a (_ & _ & SRC & _) Hk HQ ->.
pose proof (bytes_at_read segs m1 S (firstn (Z.to_nat Q) src) (Q - Z.of_nat k) k SRC ltac:(lia)) as R.
rewrite length_firstn, LEN in R. specialize (R ltac:(lia)). rewrite R. f_equal.
rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

#[using="LEN"] Lemma bwd_store : forall m1 bs Q (k : nat) xs a,
bwd_inv m1 bs Q -> S <= D -> Z.of_nat k <= Q -> Q <= n -> 0 <= D -> D + n <= 2^64 -> 0 <= S ->
xs = firstn k (skipn (Z.to_nat (Q - Z.of_nat k)) src) -> a = wa (D + (Q - Z.of_nat k)) ->
store_ok segs m1 a k = true /\
bwd_inv (write_to_mem m1 a xs) (upd_bytes bs (Z.to_nat (Q - Z.of_nat k)) xs) (Q - Z.of_nat k).
Proof.
intros m1 bs Q k xs a (DST & CS & SRC & MI & MU & WM) SD Hk HQ D0 Dn S0 Hxs ->.
pose proof (proj1 CS) as Lbs.
assert (Lxs : length xs = k). { subst xs. rewrite length_firstn, length_skipn, LEN. lia. }
split. { eapply (u8arr_store_ok_n segs m1 D bs (Q - Z.of_nat k) k); [exact DST | lia | rewrite Lbs, LEN; lia | reflexivity]. }
split. { apply (u8arr_write_bytes segs m1 D bs (Q - Z.of_nat k) xs DST); [lia|]. rewrite Lbs, LEN, Lxs. lia. }
split. { replace (Z.to_nat (Q - Z.of_nat k)) with (Z.to_nat Q - k)%nat by lia. apply csfx_upd; [exact CS | lia | rewrite LEN; lia |].
rewrite Hxs. f_equal. f_equal. lia. }
split.
{ assert (SRC' : bytes_at segs m1 S (firstn (Z.to_nat (Q - Z.of_nat k)) src)).
{ rewrite <- (firstn_skipn (Z.to_nat (Q - Z.of_nat k)) (firstn (Z.to_nat Q) src)) in SRC.
apply bytes_at_app in SRC. destruct SRC as [SRC _]. rewrite firstn_firstn in SRC.
replace (Nat.min (Z.to_nat (Q - Z.of_nat k)) (Z.to_nat Q)) with (Z.to_nat (Q - Z.of_nat k)) in SRC by lia. exact SRC. }
apply bytes_at_write_other; [exact SRC' | lia | rewrite Lxs; lia |]. rewrite Lxs, length_firstn, LEN. lia. }
split. { apply mem_inv_store; [exact MI|]. rewrite Lxs. eapply (u8arr_store_ok_n segs m1 D bs (Q - Z.of_nat k) k); [exact DST | lia | rewrite Lbs, LEN; lia | reflexivity]. }
split. { apply munch_write; [exact MU | lia | rewrite Lxs; lia |]. cbn [inside]. left. rewrite Lxs. lia. }
apply wmono_write. exact WM.
Qed.

#[using="LEN"] Lemma fwd_init : forall m1 junk,
rw_cells segs m1 D [CB (Z.to_nat n) junk] -> bytes_at segs m1 S src -> mem_inv segs m1 ->
munch [(D, D + n)] m0 m1 -> wmono segs m0 m1 -> fwd_inv m1 junk 0.
Proof.
intros m1 junk DST SRC MI MU WM. pose proof (rw_cells_CB_length _ _ _ _ _ DST) as L.
split; [apply u8arr_of_rw_cells in DST; exact DST|]. split; [apply copied_0; rewrite L, LEN; reflexivity|].
split; [rewrite Z.add_0_r; cbn; exact SRC|]. split; [exact MI|]. split; [exact MU|exact WM].
Qed.

#[using="LEN"] Lemma bwd_init : forall m1 junk,
rw_cells segs m1 D [CB (Z.to_nat n) junk] -> bytes_at segs m1 S src -> mem_inv segs m1 ->
munch [(D, D + n)] m0 m1 -> wmono segs m0 m1 -> bwd_inv m1 junk n.
Proof.
intros m1 junk DST SRC MI MU WM. pose proof (rw_cells_CB_length _ _ _ _ _ DST) as L.
split; [apply u8arr_of_rw_cells in DST; exact DST|]. split; [rewrite <- LEN; apply csfx_init; rewrite L, LEN; reflexivity|].
split; [rewrite <- LEN, firstn_all; exact SRC|]. split; [exact MI|]. split; [exact MU|exact WM].
Qed.

#[using="LEN"] Lemma fwd_done : forall m1 bs P, fwd_inv m1 bs P -> n <= P ->
rw_cells segs m1 D [CB (Z.to_nat n) src] /\ mem_inv segs m1 /\ munch [(D, D + n)] m0 m1 /\ wmono segs m0 m1.
Proof.
intros m1 bs P (DST & CP & _ & MI & MU & WM) HP.
pose proof (copied_all _ _ _ CP ltac:(rewrite LEN; lia)) as ->.
apply rw_cells_of_u8arr in DST. rewrite LEN in DST. split; [exact DST|]. split; [exact MI|]. split; [exact MU|exact WM].
Qed.

#[using="LEN"] Lemma bwd_done : forall m1 bs Q, bwd_inv m1 bs Q -> Q <= 0 ->
rw_cells segs m1 D [CB (Z.to_nat n) src] /\ mem_inv segs m1 /\ munch [(D, D + n)] m0 m1 /\ wmono segs m0 m1.
Proof.
intros m1 bs Q (DST & CS & _ & MI & MU & WM) HQ.
replace (Z.to_nat Q) with 0%nat in CS by lia. pose proof (csfx_all _ _ CS) as ->.
apply rw_cells_of_u8arr in DST. rewrite LEN in DST. split; [exact DST|]. split; [exact MI|]. split; [exact MU|exact WM].
Qed.
End WithSegs.
