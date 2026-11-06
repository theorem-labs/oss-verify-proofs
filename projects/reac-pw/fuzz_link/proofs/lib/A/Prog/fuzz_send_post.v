(* fuzz_send on image A: the byte algebra of its Post (lib/A/Prog/fuzz_send_c.v fuzz_send_apost), over byte
   lists only. The walk (lib/A/Prog/fuzz_send.v) reads the g_nl bytes bs' off the end memory and knows, for each
   path, which offsets of g_nl the run may have written (P) and the values of the written fields; the lemmas here
   turn that into the Post's link_spec facts. The ring lemmas are the plain walk's (lib/Prog/fuzz_send.v
   nk_sent_same, nk_sent_snoc), re-proved here over the "agrees outside P" relation.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkNlk.
Import ListNotations.
Open Scope Z_scope.

(* the misuse flag fuzz_send leaves (netlink.h:92-93), as the Post states it *)
Definition snd_mis (fd : Z) (bs : list byte) : Z :=
  if (fd =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1.

Lemma snd_mis_range : forall fd bs, nlk_wf bs -> 0 <= snd_mis fd bs <= 1.
Proof.
  intros fd bs (_ & _ & _ & _ & _ & _ & _ & W8 & _). unfold snd_mis.
  destruct ((fd =? NL_FD) && negb (nk_open bs =? 0)); lia.
Qed.

(* bs' holds bs's byte at every offset of g_nl outside P *)
Definition agree_out (bs bs' : list byte) (P : Z -> Prop) : Prop :=
  forall i, 0 <= i < NK_SIZE -> ~ P i -> nth_error bs' (Z.to_nat i) = nth_error bs (Z.to_nat i).

Lemma rdn_out : forall bs bs' (P : Z -> Prop) off n,
  Z.of_nat (length bs) = NK_SIZE -> Z.of_nat (length bs') = NK_SIZE -> agree_out bs bs' P ->
  0 <= off -> 0 <= n -> off + n <= NK_SIZE -> (forall i, off <= i < off + n -> ~ P i) ->
  rdn bs' off n = rdn bs off n.
Proof.
  intros bs bs' P off n Hl Hl' HA Hoff Hn Hhi HP.
  apply rdn_agree; [lia | lia | lia | lia |].
  intros k Hk. replace (Z.to_nat off + k)%nat with (Z.to_nat (off + Z.of_nat k)) by lia.
  apply HA; [lia | apply HP; lia].
Qed.

Lemma slice_out : forall bs bs' (P : Z -> Prop) off n,
  Z.of_nat (length bs) = NK_SIZE -> Z.of_nat (length bs') = NK_SIZE -> agree_out bs bs' P ->
  0 <= off -> 0 <= n -> off + n <= NK_SIZE -> (forall i, off <= i < off + n -> ~ P i) ->
  slice bs' off n = slice bs off n.
Proof.
  intros bs bs' P off n Hl Hl' HA Hoff Hn Hhi HP.
  apply lw_list_ext; [rewrite !lw_slice_length by lia; reflexivity|].
  intros k Hk. rewrite lw_slice_length in Hk by lia.
  rewrite !lw_slice_nth by lia.
  replace (Z.to_nat off + k)%nat with (Z.to_nat (off + Z.of_nat k)) by lia.
  apply HA; [lia | apply HP; lia].
Qed.

(* the n bytes of bs' at off are l, when the walk knows each of them *)
Lemma slice_of_nth : forall (bs' l : list byte) off,
  0 <= off -> off + Z.of_nat (length l) <= Z.of_nat (length bs') ->
  (forall k, (k < length l)%nat -> nth_error bs' (Z.to_nat off + k) = nth_error l k) ->
  slice bs' off (Z.of_nat (length l)) = l.
Proof.
  intros bs' l off Hoff Hlen H.
  apply lw_list_ext; [rewrite lw_slice_length by lia; lia|].
  intros k Hk. rewrite lw_slice_length in Hk by lia. rewrite lw_slice_nth by lia. apply H. lia.
Qed.

Lemma nk_sent_len : forall bs, 0 <= nk_n_sent bs -> Z.of_nat (length (nk_sent bs)) = nk_n_sent bs.
Proof. intros bs H. unfold nk_sent. rewrite length_map, length_seq. lia. Qed.

Lemma nk_sent_same : forall bs bs', nk_n_sent bs' = nk_n_sent bs ->
  (forall i, 0 <= i < nk_n_sent bs -> nk_sent_one bs' i = nk_sent_one bs i) -> nk_sent bs' = nk_sent bs.
Proof.
  intros bs bs' E H. unfold nk_sent. rewrite E. apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
Qed.

Lemma nk_sent_snoc : forall bs bs' r, 0 <= nk_n_sent bs -> nk_n_sent bs' = nk_n_sent bs + 1 ->
  (forall i, 0 <= i < nk_n_sent bs -> nk_sent_one bs' i = nk_sent_one bs i) ->
  nk_sent_one bs' (nk_n_sent bs) = r -> nk_sent bs' = nk_sent bs ++ [r].
Proof.
  intros bs bs' r H0 E H Hr. unfold nk_sent. rewrite E.
  replace (Z.to_nat (nk_n_sent bs + 1)) with (S (Z.to_nat (nk_n_sent bs))) by lia.
  rewrite seq_S, map_app. cbn [map]. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
  - rewrite Nat.add_0_l, Z2Nat.id by lia. rewrite Hr. reflexivity.
Qed.

(* the three fields every path may write, and the misuse word *)
Definition P_base (i : Z) : Prop :=
  (NK_SEND_ERRNO <= i < NK_SEND_ERRNO + 4) \/ (NK_MISUSE <= i < NK_MISUSE + 4) \/ (NK_N_SENT <= i < NK_N_SENT + 4).

(* the offsets the recording path may write: P_base, sent[n] (len bytes) and sent_len[n] *)
Definition P_copy (n len : Z) (i : Z) : Prop :=
  P_base i \/ (NK_SENT + NL_SENT_LEN * n <= i < NK_SENT + NL_SENT_LEN * n + len)
  \/ (NK_SENT_LEN + 8 * n <= i < NK_SENT_LEN + 8 * n + 8).

Ltac nk_unf := unfold nk_n_chunks, nk_next, nk_n_sent, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
  nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, fld_u64 in *.
Ltac nk_nums := repeat lazymatch goal with |- forall _, _ => intro | |- ~ _ => intro end;
  try unfold P_copy in *; try unfold P_base in *; unfold NK_N_CHUNKS, NK_NEXT, NK_N_SENT, NK_N_IF, NK_OPEN, NK_OPENED,
  NK_CLOSED, NK_MISUSE, NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_CHUNK_LEN, NK_SENT_LEN, NK_SENT, NK_SIZE,
  NL_CHUNKS, NL_SENT_MAX, NL_CHUNK_MAX, NL_SENT_LEN in *.

(* The part of the Post every path shares: the fields fuzz_send never writes, and misuse. *)
Definition snd_common (fd : Z) (bs bs' : list byte) : Prop :=
  nk_socket_errno bs' = nk_socket_errno bs /\ nk_end_errno bs' = nk_end_errno bs
  /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
  /\ nk_closed bs' = nk_closed bs
  /\ nk_misuse bs' = (if (fd =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1).

Lemma snd_common_of : forall fd bs bs' (P : Z -> Prop),
  Z.of_nat (length bs) = NK_SIZE -> Z.of_nat (length bs') = NK_SIZE -> agree_out bs bs' P ->
  (forall i, P i -> P_base i \/ NK_SENT <= i < NK_N_SENT) ->
  rdn bs' NK_MISUSE 4 = snd_mis fd bs ->
  snd_common fd bs bs'.
Proof.
  intros fd bs bs' P Hl Hl' HA HP HM.
  assert (OUT : forall off, 0 <= off -> off + 4 <= NK_SEND_ERRNO \/ (NK_OPEN <= off /\ off + 4 <= NK_MISUSE) ->
            rdn bs' off 4 = rdn bs off 4).
  { intros off H0 Hd. apply (rdn_out bs bs' P); [exact Hl | exact Hl' | exact HA | lia | lia | nk_nums; lia |].
    intros i Hi HPi. destruct (HP i HPi) as [Hb | Hb]; clear - Hb Hi Hd; try unfold P_base in Hb; nk_nums; lia. }
  unfold snd_common. nk_unf.
  split; [apply OUT; nk_nums; lia|]. split; [apply OUT; nk_nums; lia|].
  split; [apply OUT; nk_nums; lia|]. split; [apply OUT; nk_nums; lia|].
  split; [apply OUT; nk_nums; lia|].
  exact HM.
Qed.

(* The error path: send_errno := 0 and misuse; the ring is as it was. *)
Lemma post_err_b : forall fd bs bs',
  Z.of_nat (length bs) = NK_SIZE -> Z.of_nat (length bs') = NK_SIZE -> nlk_wf bs ->
  agree_out bs bs' P_base ->
  rdn bs' NK_MISUSE 4 = snd_mis fd bs -> rdn bs' NK_SEND_ERRNO 4 = 0 -> rdn bs' NK_N_SENT 4 = nk_n_sent bs ->
  nlk_wf bs' /\ snd_common fd bs bs' /\ nk_send_errno bs' = 0 /\ nk_n_sent bs' = nk_n_sent bs
  /\ nk_sent bs' = nk_sent bs.
Proof.
  intros fd bs bs' Hl Hl' WF HA HM HS HN.
  pose proof (snd_mis_range fd bs WF) as Mb.
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  assert (OUT : forall off n, 0 <= off -> 0 <= n -> off + n <= NK_SIZE ->
            (forall i, off <= i < off + n -> ~ P_base i) -> rdn bs' off n = rdn bs off n)
    by (intros off n H0 H1 H2 H3; exact (rdn_out bs bs' P_base off n Hl Hl' HA H0 H1 H2 H3)).
  assert (OUTs : forall off n, 0 <= off -> 0 <= n -> off + n <= NK_SIZE ->
            (forall i, off <= i < off + n -> ~ P_base i) -> slice bs' off n = slice bs off n)
    by (intros off n H0 H1 H2 H3; exact (slice_out bs bs' P_base off n Hl Hl' HA H0 H1 H2 H3)).
  pose proof (snd_common_of fd bs bs' P_base Hl Hl' HA ltac:(intros i Hi; left; exact Hi) HM) as COM.
  assert (NS : nk_n_sent bs' = nk_n_sent bs) by (unfold nk_n_sent, fld_u32; exact HN).
  assert (SENT : nk_sent bs' = nk_sent bs).
  { apply nk_sent_same; [exact NS|].
    intros i Hi. pose proof (W13 i Hi) as L13. unfold nk_sent_one.
    unfold fld_u64 in *. rewrite (OUT (NK_SENT_LEN + 8 * i) 8) by (nk_unf; nk_nums; lia).
    apply OUTs; nk_unf; nk_nums; intros; lia. }
  refine (conj _ (conj COM (conj _ (conj NS SENT)))); [|unfold nk_send_errno, fld_u32; exact HS].
  destruct COM as (C1 & C2 & C3 & C4 & C5 & C6).
  apply (nlk_wf_same_queues bs bs' WF).
  - nk_unf. apply OUT; nk_nums; intros; lia.
  - exact NS.
  - nk_unf. apply OUT; nk_nums; intros; lia.
  - intros i Hi. nk_unf. apply OUT; nk_nums; intros; lia.
  - intros i Hi. nk_unf. apply OUT; nk_nums; intros; lia.
  - nk_unf. rewrite (OUT NK_NEXT 4) by (nk_nums; intros; lia). lia.
  - rewrite C3. exact W5.
  - rewrite C4. exact W6.
  - rewrite C5. exact W7.
  - rewrite C6. fold (snd_mis fd bs). lia.
  - rewrite C2. exact W9.
  - rewrite C1. exact W10.
  - unfold nk_send_errno, fld_u32. rewrite HS. lia.
Qed.

(* The full ring (n_sent = 16, so owe records nothing): only misuse changes. *)
Lemma post_full_b : forall fd bs bs' req,
  Z.of_nat (length bs) = NK_SIZE -> Z.of_nat (length bs') = NK_SIZE -> nlk_wf bs ->
  nk_send_errno bs = 0 -> 15 < nk_n_sent bs ->
  agree_out bs bs' P_base ->
  rdn bs' NK_MISUSE 4 = snd_mis fd bs -> rdn bs' NK_SEND_ERRNO 4 = nk_send_errno bs ->
  rdn bs' NK_N_SENT 4 = nk_n_sent bs ->
  nlk_wf bs' /\ snd_common fd bs bs' /\ nk_send_errno bs' = 0 /\ nk_sent bs' = owe (nk_sent bs) req
  /\ nk_n_sent bs' = Z.of_nat (length (owe (nk_sent bs) req)).
Proof.
  intros fd bs bs' req Hl Hl' WF SE N15 HA HM HS HN.
  destruct (post_err_b fd bs bs' Hl Hl' WF HA HM ltac:(rewrite HS; exact SE) HN) as (WF' & COM & SE' & NS & SENT).
  pose proof WF as (_ & _ & W3 & _).
  assert (LS : Z.of_nat (length (nk_sent bs)) = 16) by (rewrite nk_sent_len; unfold NL_SENT_MAX in W3; lia).
  assert (OW : owe (nk_sent bs) req = nk_sent bs)
    by (unfold owe, NL_SENT_MAX; destruct (Z.ltb_spec (Z.of_nat (length (nk_sent bs))) 16); [lia | reflexivity]).
  rewrite OW, SENT, NS, LS. unfold NL_SENT_MAX in W3.
  refine (conj WF' (conj COM (conj SE' (conj eq_refl _)))). lia.
Qed.

Lemma post_copy_b : forall fd bs bs' req,
  Z.of_nat (length bs) = NK_SIZE -> Z.of_nat (length bs') = NK_SIZE -> nlk_wf bs ->
  nk_send_errno bs = 0 -> nk_n_sent bs <= 15 -> Z.of_nat (length req) <= NL_SENT_LEN ->
  agree_out bs bs' (P_copy (nk_n_sent bs) (Z.of_nat (length req))) ->
  rdn bs' NK_MISUSE 4 = snd_mis fd bs -> rdn bs' NK_SEND_ERRNO 4 = nk_send_errno bs ->
  rdn bs' NK_N_SENT 4 = nk_n_sent bs + 1 ->
  rdn bs' (NK_SENT_LEN + 8 * nk_n_sent bs) 8 = Z.of_nat (length req) ->
  (forall k, (k < length req)%nat ->
     nth_error bs' (Z.to_nat (NK_SENT + NL_SENT_LEN * nk_n_sent bs) + k) = nth_error req k) ->
  nlk_wf bs' /\ snd_common fd bs bs' /\ nk_send_errno bs' = 0 /\ nk_sent bs' = owe (nk_sent bs) req
  /\ nk_n_sent bs' = Z.of_nat (length (owe (nk_sent bs) req)).
Proof.
  intros fd bs bs' req Hl Hl' WF SE N15 LR HA HM HS HN HSL HR.
  pose proof (snd_mis_range fd bs WF) as Mb.
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  remember (nk_n_sent bs) as n eqn:En.
  remember (Z.of_nat (length req)) as len eqn:Elen.
  assert (Hn0 : 0 <= n) by (subst n; nk_unf; lia).
  assert (Hlen0 : 0 <= len) by lia.
  assert (OUT : forall off k, 0 <= off -> 0 <= k -> off + k <= NK_SIZE ->
            (forall i, off <= i < off + k -> ~ P_copy n len i) -> rdn bs' off k = rdn bs off k)
    by (intros off k H0 H1 H2 H3; exact (rdn_out bs bs' (P_copy n len) off k Hl Hl' HA H0 H1 H2 H3)).
  assert (OUTs : forall off k, 0 <= off -> 0 <= k -> off + k <= NK_SIZE ->
            (forall i, off <= i < off + k -> ~ P_copy n len i) -> slice bs' off k = slice bs off k)
    by (intros off k H0 H1 H2 H3; exact (slice_out bs bs' (P_copy n len) off k Hl Hl' HA H0 H1 H2 H3)).
  pose proof (snd_common_of fd bs bs' (P_copy n len) Hl Hl' HA
    ltac:(intros i Hi; unfold P_copy, NL_SENT_LEN in Hi; nk_nums; lia) HM) as COM.
  assert (NS : nk_n_sent bs' = n + 1) by (unfold nk_n_sent, fld_u32; exact HN).
  assert (SR : nk_sent_one bs' n = req).
  { unfold nk_sent_one, fld_u64. rewrite HSL, Elen. apply slice_of_nth; [nk_nums; lia | rewrite <- Elen; nk_nums; lia |].
    intros k Hk. exact (HR k Hk). }
  assert (SENT : nk_sent bs' = nk_sent bs ++ [req]).
  { apply nk_sent_snoc; [rewrite <- En; exact Hn0 | rewrite NS, <- En; reflexivity | |
      rewrite <- En; exact SR].
    intros i Hi. rewrite <- En in Hi. pose proof (W13 i ltac:(lia)) as L13.
    unfold nk_sent_one. unfold fld_u64 in *.
    rewrite (OUT (NK_SENT_LEN + 8 * i) 8) by (unfold P_copy; nk_nums; intros; lia).
    apply OUTs; unfold P_copy; nk_nums; intros; lia. }
  assert (LS : Z.of_nat (length (nk_sent bs)) = n) by (rewrite nk_sent_len; lia).
  assert (OW : owe (nk_sent bs) req = nk_sent bs ++ [req])
    by (unfold owe, NL_SENT_MAX; destruct (Z.ltb_spec (Z.of_nat (length (nk_sent bs))) 16); [reflexivity | lia]).
  destruct COM as (C1 & C2 & C3 & C4 & C5 & C6).
  refine (conj _ (conj (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 C6))))) (conj _ (conj _ _)))).
  - unfold nlk_wf.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ _)))))))))))).
    + nk_unf. rewrite (OUT NK_N_CHUNKS 4) by (unfold P_copy; nk_nums; intros; lia). lia.
    + nk_unf. rewrite !(OUT _ 4) by (unfold P_copy; nk_nums; intros; lia). lia.
    + rewrite NS. unfold NL_SENT_MAX. lia.
    + nk_unf. rewrite (OUT NK_N_IF 4) by (unfold P_copy; nk_nums; intros; lia). lia.
    + rewrite C3. exact W5.
    + rewrite C4. exact W6.
    + rewrite C5. exact W7.
    + rewrite C6. fold (snd_mis fd bs). lia.
    + rewrite C2. exact W9.
    + rewrite C1. exact W10.
    + unfold nk_send_errno, fld_u32. rewrite HS. lia.
    + intros i Hi. unfold nk_n_chunks, fld_u32 in Hi. rewrite (OUT NK_N_CHUNKS 4) in Hi by (unfold P_copy; nk_nums; intros; lia).
      unfold fld_u64. rewrite (OUT (NK_CHUNK_LEN + 8 * i) 8) by (unfold P_copy; nk_unf; nk_nums; intros; lia).
      apply W12. exact Hi.
    + intros i Hi. rewrite NS in Hi. destruct (Z.eq_dec i n) as [->|Ni].
      * unfold fld_u64. rewrite HSL. unfold NL_SENT_LEN in *. lia.
      * unfold fld_u64. rewrite (OUT (NK_SENT_LEN + 8 * i) 8) by (unfold P_copy; nk_nums; intros; lia).
        apply W13. lia.
  - unfold nk_send_errno, fld_u32. rewrite HS. exact SE.
  - rewrite OW. exact SENT.
  - rewrite NS, OW, length_app. cbn [length]. lia.
Qed.
