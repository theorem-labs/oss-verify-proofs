(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.
Import ListNotations.
Open Scope Z_scope.

Definition wlist := list (Z * list byte).

Fixpoint apply_writes (m : word -> option byte) (ws : wlist) : word -> option byte :=
match ws with
| [] => m
| (a, bs) :: ws' => apply_writes (write_to_mem m (wa a) bs) ws'
end.

Definition wtag := option (nat * cell).

Fixpoint wmatch (A sz : Z) (ws : wlist) (ts : list wtag) : Prop :=
match ws, ts with
| [], [] => True
| (a, bs) :: ws', Some (k, c) :: ts' => a = A + Z.of_nat k /\ bs = cbytes c /\ wmatch A sz ws' ts'
| (a, bs) :: ws', None :: ts' =>
0 <= a /\ a + Z.of_nat (length bs) <= 2^64 /\ (A + sz <= a \/ a + Z.of_nat (length bs) <= A) /\ wmatch A sz ws' ts'
| _, _ => False
end.

Definition cell_wfb (c : cell) : bool := match c with CB _ _ => false | _ => true end.

Fixpoint cells_apply (cs : list cell) (ts : list wtag) : option (list cell) :=
match ts with
| [] => Some cs
| None :: ts' => cells_apply cs ts'
| Some (k, c) :: ts' =>
let n := csize c in
if cb_split_ok cs k n then
let cs1 := cb_split cs k n in
match cell_at cs1 k with
| Some c0 => if (Nat.eqb (csize c0) n && cell_wfb c)%bool then cells_apply (cell_upd cs1 k c) ts' else None
| None => None
end
else None
end.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma cells_size_upd : forall cs k c c', cell_at cs k = Some c -> csize c' = csize c ->
cells_size (cell_upd cs k c') = cells_size cs.
Proof.
intros cs k c c' Hk Hsz. destruct (cell_at_split cs k c c' Hk) as (pre & post & -> & _ & ->).
rewrite !cells_size_app. cbn. lia.
Qed.

#[using="Type"] Lemma cell_wfb_wf : forall c, cell_wfb c = true -> cell_wf c.
Proof. intros [] H; cbn in *; first [exact I | discriminate]. Qed.

#[using="Type"] Theorem rw_cells_apply : forall ws ts m A cs cs',
rw_cells segs m A cs -> wmatch A (Z.of_nat (cells_size cs)) ws ts -> cells_apply cs ts = Some cs' ->
rw_cells segs (apply_writes m ws) A cs'.
Proof.
induction ws as [|[a bs] ws IH]; intros ts m A cs cs' HR HM HC.
- destruct ts; [|destruct HM]. cbn in HC. injection HC as <-. exact HR.
- destruct ts as [|[[k c]|] ts]; [destruct HM| |].
+ cbn [wmatch] in HM. destruct HM as (-> & -> & HM).
cbn [cells_apply] in HC.
destruct (cb_split_ok cs k (csize c)) eqn:Hok; [|discriminate].
destruct (cell_at (cb_split cs k (csize c)) k) as [c0|] eqn:Hat; [|discriminate].
destruct (Nat.eqb (csize c0) (csize c) && cell_wfb c)%bool eqn:Hb; [|discriminate].
apply andb_true_iff in Hb as [Hsz Hwf]. apply Nat.eqb_eq in Hsz. apply cell_wfb_wf in Hwf.
pose proof (rw_cells_cb_split segs m A cs _ k (csize c) HR Hok eq_refl) as HR1.
pose proof (rw_cells_write segs m A _ k c0 c HR1 Hat (eq_sym Hsz) Hwf) as HR2.
cbn [apply_writes]. eapply IH; [exact HR2 | | exact HC].
rewrite (cells_size_upd _ _ _ _ Hat (eq_sym Hsz)).
rewrite cells_size_cb_split; [exact HM | exact (cells_at_wf _ _ _ _ (proj1 HR)) | exact Hok].
+ cbn [wmatch] in HM. destruct HM as (H0 & H1 & HD & HM). cbn [cells_apply] in HC. cbn [apply_writes].
eapply IH; [| exact HM | exact HC].
apply rw_cells_frame; [exact HR | lia | lia | lia].
Qed.

Fixpoint nones (ws : wlist) : list wtag := match ws with [] => [] | _ :: ws' => None :: nones ws' end.

Definition wdisj (A sz : Z) (ws : wlist) : Prop :=
Forall (fun w => 0 <= fst w /\ fst w + Z.of_nat (length (snd w)) <= 2^64 /\
(A + sz <= fst w \/ fst w + Z.of_nat (length (snd w)) <= A)) ws.

#[using="Type"] Lemma bytes_at_apply : forall ws m A bs,
bytes_at segs m A bs -> wdisj A (Z.of_nat (length bs)) ws -> bytes_at segs (apply_writes m ws) A bs.
Proof.
induction ws as [|[a b] ws IH]; intros m A bs HB HD; [exact HB|].
apply Forall_cons_iff in HD as [(H0 & H1 & H2) HD]. cbn in H0, H1, H2. cbn [apply_writes].
apply IH; [|exact HD]. apply bytes_at_write_other; [exact HB | lia | lia | lia].
Qed.

#[using="Type"] Lemma rw_cells_apply_frame : forall ws m A cs,
rw_cells segs m A cs -> wdisj A (Z.of_nat (cells_size cs)) ws -> rw_cells segs (apply_writes m ws) A cs.
Proof.
induction ws as [|[a b] ws IH]; intros m A cs HB HD; [exact HB|].
apply Forall_cons_iff in HD as [(H0 & H1 & H2) HD]. cbn in H0, H1, H2. cbn [apply_writes].
apply IH; [|exact HD]. apply rw_cells_frame; [exact HB | lia | lia | lia].
Qed.

#[using="Type"] Lemma ro_cells_apply_frame : forall ws m A cs,
ro_cells segs m A cs -> wdisj A (Z.of_nat (cells_size cs)) ws -> ro_cells segs (apply_writes m ws) A cs.
Proof.
induction ws as [|[a b] ws IH]; intros m A cs HB HD; [exact HB|].
apply Forall_cons_iff in HD as [(H0 & H1 & H2) HD]. cbn in H0, H1, H2. cbn [apply_writes].
apply IH; [|exact HD]. apply ro_cells_frame; [exact HB | lia | lia | lia].
Qed.

Definition writes_in (ws : wlist) (l h : Z) : Prop :=
Forall (fun w => l <= fst w /\ fst w + Z.of_nat (length (snd w)) <= h) ws.

#[using="Type"] Lemma wdisj_of_hull : forall ws l h A sz,
writes_in ws l h -> 0 <= l -> h <= 2^64 -> (A + sz <= l \/ h <= A) -> wdisj A sz ws.
Proof.
intros ws l h A sz HW Hl Hh HD. unfold wdisj, writes_in in *.
eapply Forall_impl; [|exact HW]. intros [a b] [H1 H2]; cbn in *. lia.
Qed.

Fixpoint tags_hull (ts : list wtag) : option (nat * nat) :=
match ts with
| [] => None
| None :: _ => None
| Some (k, c) :: ts' =>
match ts' with
| [] => Some (k, k + csize c)%nat
| _ => match tags_hull ts' with
| Some (lo, hi) => Some (Nat.min k lo, Nat.max (k + csize c) hi)%nat
| None => None
end
end
end.

#[using="Type"] Lemma wmatch_hull : forall ws ts A sz lo hi,
wmatch A sz ws ts -> tags_hull ts = Some (lo, hi) ->
Forall (fun t => match t with Some (_, c) => cell_wfb c = true | None => False end) ts ->
writes_in ws (A + Z.of_nat lo) (A + Z.of_nat hi).
Proof.
induction ws as [|[a b] ws IH]; intros ts A sz lo hi HM HT HF.
- destruct ts; [discriminate HT | destruct HM].
- destruct ts as [|[[k c]|] ts]; [destruct HM | | cbn in HT; discriminate HT].
cbn [wmatch] in HM. destruct HM as (-> & -> & HM).
apply Forall_cons_iff in HF as [Hc HF].
assert (HL : length (cbytes c) = csize c) by (apply cbytes_length, cell_wfb_wf, Hc).
cbn [tags_hull] in HT.
destruct ts as [|t ts'].
+ injection HT as <- <-. destruct ws as [|[a2 b2] ws2]; [|destruct HM]. constructor; [cbn; rewrite HL; lia | constructor].
+ destruct (tags_hull (t :: ts')) as [[lo' hi']|] eqn:HT'; [|discriminate HT].
injection HT as <- <-.
pose proof (IH _ _ _ _ _ HM HT' HF) as HW.
constructor.
* cbn. rewrite HL. lia.
* unfold writes_in in HW. eapply Forall_impl; [|exact HW]. intros [a' b'] [H1 H2]; cbn in *. lia.
Qed.

#[using="Type"] Lemma wmono_apply : forall ws m0 m, wmono segs m0 m -> wmono segs m0 (apply_writes m ws).
Proof. induction ws as [|[a b] ws IH]; intros m0 m H; [exact H|]. cbn. apply IH. apply wmono_write. exact H. Qed.

#[using="Type"] Lemma wr_at_apply : forall ws m A n, wr_at segs m A n -> wr_at segs (apply_writes m ws) A n.
Proof. induction ws as [|[a b] ws IH]; intros m A n H; [exact H|]. cbn. apply IH. apply wr_at_write. exact H. Qed.

#[using="Type"] Lemma stk_apply : forall ws m lo hi l h,
stk segs m lo hi -> writes_in ws l h -> 0 <= l -> h <= 2^64 -> stk segs (apply_writes m ws) lo hi.
Proof.
induction ws as [|[a b] ws IH]; intros m lo hi l h HS HW Hl Hh; [exact HS|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2. cbn [apply_writes].
eapply IH; [| exact HW | exact Hl | exact Hh]. apply stk_write; [exact HS | lia | lia].
Qed.

#[using="Type"] Lemma inside_sub : forall W l n a k, inside W l n -> l <= a -> a + k <= l + n -> 0 <= k -> inside W a k.
Proof.
induction W as [|[lo hi] W IH]; intros l n a k H H1 H2 H3; cbn in *; [exact H|].
destruct H as [H|H]; [left; lia | right; eapply IH; eauto].
Qed.

#[using="Type"] Lemma munch_apply : forall ws W m0 m l h,
munch W m0 m -> writes_in ws l h -> 0 <= l -> h <= 2^64 -> inside W l (h - l) ->
munch W m0 (apply_writes m ws).
Proof.
induction ws as [|[a b] ws IH]; intros W m0 m l h HM HW Hl Hh HI; [exact HM|].
apply Forall_cons_iff in HW as [[H1 H2] HW]. cbn in H1, H2. cbn [apply_writes].
eapply IH; [| exact HW | exact Hl | exact Hh | exact HI].
apply munch_write; [exact HM | lia | lia |]. eapply inside_sub; [exact HI | lia | lia | lia].
Qed.

#[using="Type"] Lemma mem_inv_apply : forall ws m A n l h,
mem_inv segs m -> wr_at segs m A n -> writes_in ws l h -> A <= l -> h <= A + n ->
mem_inv segs (apply_writes m ws).
Proof.
induction ws as [|[a b] ws IH]; intros m A n l h HM HW HI HAl HAh; [exact HM|].
apply Forall_cons_iff in HI as [[H1 H2] HI]. cbn in H1, H2. cbn [apply_writes].
eapply IH; [| apply wr_at_write; exact HW | exact HI | exact HAl | exact HAh].
apply mem_inv_store; [exact HM|].
replace (wa a) with (wa (A + (a - A))) by (f_equal; lia).
eapply wr_at_store_ok; [exact HW | lia | lia].
Qed.

#[using="Type"] Lemma rw_cells_wr_at : forall m A cs, rw_cells segs m A cs -> wr_at segs m A (Z.of_nat (cells_size cs)).
Proof. intros m A cs [_ H]. exact H. Qed.

#[using="Type"] Lemma off_eq : forall x dA k d, (dA + k =? d) = true -> x + d = x + dA + k.
Proof. intros x dA k d H. apply Z.eqb_eq in H. lia. Qed.
#[using="Type"] Lemma off_eq0 : forall x k d, (k =? d) = true -> x + d = x + k.
Proof. intros x k d H. apply Z.eqb_eq in H. lia. Qed.
#[using="Type"] Lemma off_eqA : forall x dA k, (dA + k =? 0) = true -> x = x + dA + k.
Proof. intros x dA k H. apply Z.eqb_eq in H. lia. Qed.
#[using="Type"] Lemma off_eq00 : forall x k, (k =? 0) = true -> x = x + k.
Proof. intros x k H. apply Z.eqb_eq in H. lia. Qed.

End WithSegs.
