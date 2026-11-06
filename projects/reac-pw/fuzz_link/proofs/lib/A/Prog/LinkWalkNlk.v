(* reac-pw/fuzz_link, image A: the fake kernel g_nl after a walk. The Post of every walk of a function that writes
   some fields of g_nl (fuzz_socket, fuzz_send, fuzz_recv, fuzz_close, kernel) names a byte list bs' with
   `anlk_at m' LA_G_NL bs'`; the walk knows the end memory m' only as "the bytes outside the written fields are as at
   the call" and "the written fields hold these values" (val_mem facts read back out of the symbolic run's regions).

   - anlk_after: bs' := abytes_of m' g NK_SIZE is a g_nl byte list of the end memory, its reads outside the written
     window [lo, hi) are the reads of the call's list bs, and a read of a field the run left as a val_mem fact is
     that value.
   - anlk_at_unique: the byte list at g_nl is unique (the Posts quantify over the Pre's list).
   - nlk_wf_same_queues: lib/Prog/kn_nlk.v's lemma of the same name (the plain walks'), re-proved here because that
     file is plain-image only: well-formedness when the chunk queue, the request ring and the interface count are
     untouched.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YI04 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem LinkWalk.
Import ListNotations.
Open Scope Z_scope.

Section n.
Variable segs : list Segment.

Lemma anlk_at_unique : forall m g b1 b2, anlk_at segs m g b1 -> anlk_at segs m g b2 -> b1 = b2.
Proof.
  intros m g b1 b2 [[(_ & _ & H1) _] L1] [[(_ & _ & H2) _] L2].
  apply lw_list_ext; [lia|].
  intros k Hk. rewrite <- (H1 k Hk). apply H2. lia.
Qed.

(* the list read off the end memory *)
Lemma anlk_after : forall m m' g bs lo hi,
  anlk_at segs m g bs ->
  (forall i, 0 <= i < NK_SIZE -> ~ (lo <= i < hi) -> mbyte segs m' (g + i) = mbyte segs m (g + i)) ->
  (forall i, 0 <= i < NK_SIZE -> lo <= i < hi -> exists b, mbyte segs m' (g + i) = Some b) ->
  (forall i, 0 <= i < NK_SIZE -> writable_at segs m' (g + i)) ->
  anlk_at segs m' g (abytes_of segs m' g (Z.to_nat NK_SIZE)) /\
  (forall off n, 0 <= off -> 0 <= n -> off + n <= NK_SIZE -> off + n <= lo \/ hi <= off ->
     rdn (abytes_of segs m' g (Z.to_nat NK_SIZE)) off n = rdn bs off n) /\
  (forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= NK_SIZE -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
     val_mem segs m' (g + off) n v -> rdn (abytes_of segs m' g (Z.to_nat NK_SIZE)) off (Z.of_nat n) = v).
Proof.
  intros m m' g bs lo hi [[(Hg0 & Hgl & Hb) Hw] HL] Hout Hin Hwr.
  assert (NKv : NK_SIZE = 271992) by reflexivity.
  assert (HL' : length (abytes_of segs m' g (Z.to_nat NK_SIZE)) = Z.to_nat NK_SIZE) by apply abytes_of_length.
  (* every byte of g_nl is defined at the end *)
  assert (Hdef : forall i, 0 <= i < NK_SIZE -> exists b, mbyte segs m' (g + i) = Some b).
  { intros i Hi. destruct (Z_lt_le_dec i lo) as [Hl|Hl]; [|destruct (Z_lt_le_dec i hi) as [Hh|Hh]].
    1, 3: rewrite (Hout i Hi ltac:(lia));
      replace i with (Z.of_nat (Z.to_nat i)) by lia;
      rewrite (Hb (Z.to_nat i) ltac:(lia));
      destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|];
      apply nth_error_None in E; lia.
    exact (Hin i Hi ltac:(lia)). }
  (* a byte outside [lo, hi) is the call's *)
  assert (Hsame : forall i, 0 <= i < NK_SIZE -> ~ (lo <= i < hi) ->
            nth_error (abytes_of segs m' g (Z.to_nat NK_SIZE)) (Z.to_nat i) = nth_error bs (Z.to_nat i)).
  { intros i Hi Hn. destruct (Hdef i Hi) as (b & Eb).
    rewrite (abytes_of_nth segs m' g (Z.to_nat NK_SIZE) (Z.to_nat i) b ltac:(lia)
               ltac:(rewrite Z2Nat.id by lia; exact Eb)).
    rewrite <- (Hb (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id by lia.
    rewrite <- (Hout i Hi Hn). symmetry. exact Eb. }
  split; [|split].
  - split; [|rewrite HL'; lia]. split.
    + apply abytes_of_abytes; [lia | lia |]. intros i Hi. apply Hdef. lia.
    + intros i Hi. apply Hwr. rewrite HL' in Hi. lia.
  - intros off n Hoff Hn Hon Hd.
    apply rdn_agree; [lia | lia | lia | rewrite HL'; lia |].
    intros k Hk. replace (Z.to_nat off + k)%nat with (Z.to_nat (off + Z.of_nat k)) by lia.
    apply Hsame; lia.
  - intros off n v Hoff Hon Hv HV.
    apply rdn_of_vals; [lia | rewrite HL'; lia | exact Hv |].
    intros k Hk. apply (abytes_of_val segs m' g (Z.to_nat NK_SIZE) off n v k); [lia | lia | exact Hk | exact HV].
Qed.

Lemma nlk_wf_same_queues : forall bs bs',
  nlk_wf bs ->
  nk_n_chunks bs' = nk_n_chunks bs -> nk_n_sent bs' = nk_n_sent bs -> nk_n_if bs' = nk_n_if bs ->
  (forall i, 0 <= i < nk_n_chunks bs -> fld_u64 bs' (NK_CHUNK_LEN + 8 * i) = fld_u64 bs (NK_CHUNK_LEN + 8 * i)) ->
  (forall i, 0 <= i < nk_n_sent bs -> fld_u64 bs' (NK_SENT_LEN + 8 * i) = fld_u64 bs (NK_SENT_LEN + 8 * i)) ->
  0 <= nk_next bs' <= nk_n_chunks bs ->
  0 <= nk_open bs' <= 1 -> 0 <= nk_opened bs' < 2 ^ 31 -> 0 <= nk_closed bs' < 2 ^ 31 -> 0 <= nk_misuse bs' <= 1 ->
  0 <= nk_end_errno bs' < 2 ^ 31 -> 0 <= nk_socket_errno bs' < 2 ^ 31 -> 0 <= nk_send_errno bs' < 2 ^ 31 ->
  nlk_wf bs'.
Proof.
  intros bs bs' (W1 & W2 & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & W12 & W13) E1 E2 E3 C1 C2 N O1 O2 O3 O4 O5 O6 O7.
  unfold nlk_wf. rewrite E1, E2, E3.
  refine (conj W1 (conj N (conj W3 (conj W4 (conj O1 (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 (conj O7
    (conj _ _)))))))))))).
  - intros i Hi. rewrite C1 by exact Hi. apply W12. exact Hi.
  - intros i Hi. rewrite C2 by exact Hi. apply W13. exact Hi.
Qed.

(* the call's list at a field, as the entry state needs it *)
Lemma anlk_field : forall m g bs off (n : nat),
  anlk_at segs m g bs -> 0 <= off -> off + Z.of_nat n <= NK_SIZE ->
  val_mem segs m (g + off) n (rdn bs off (Z.of_nat n)).
Proof.
  intros m g bs off n [[Hab _] HL] Hoff Hn. apply val_mem_of_abytes; [exact Hab | exact Hoff | lia].
Qed.
End n.
