(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/varnish/esi_parse_fuzzer/lib/Lib/Step.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Lib/Step.v; 706 of its 733 lines of code are new or changed and 666 lines of the source are left out. *)
(* fuzz_recv (netlink.h:107-137), PLAIN build: the walk of its contract (lib/Prog/fuzz_recv_c.v) on the plain
   image, 0x13610-0x13777 (90 instructions, an 80-byte frame), with its calls of memcpy (memcpy_holds), memset
   (memset_holds, twice) and the three instructions of ___errno_location (0x16e04: `mv a0, tp;
   addi a0, a0, -0xa4; ret`), walked inline. Each instruction is fetched from the image and decoded by computation
   (lib/Lib/Step.v `step`).
   The nine fields n_chunks .. misuse (g_nl + 0x40200 .. 0x40224) are cut out of `nlk_at` as cells, the walk reads
   and writes them there, and they are joined back at the end (lib/Prog/kn_nlk.v). The two reads at an index the
   walk loads from g_nl (chunk_len[next] and the bytes of chunk[next]) are served from the bytes before the cells:
   the address of each stays an expression in `next`; the load gets an `ov_read_bytes` fact at that expression and
   memcpy gets the chunk's `bytes_at`, both from `bytes_at_read` / `bytes_at_sub` (no case split on `next`).
   The walk is cut at the points where paths join: 0x13668 (after the misuse store), 0x13694 (n chosen),
   0x136c4 (o chosen), the loop head 0x136f0 (an induction over the bytes left) and the epilogue 0x13748.
   The Post's last conjunct (AMEND-lib L8: the whole buffer is still `rw_cells` on both arms): on the success arm
   the chunk, the zeros and the bytes after them join back into one CB (buf_rw); on the failure arm the buffer
   survives the errno store by rcv_cb_write (the Pre does not keep errno apart from the buffer). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf kn_nlk memcpy_c memcpy
  memset_c memset fuzz_recv_c.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Words and memory
   ========================================================================== *)

Lemma signed_lit : forall v, 0 <= v < 2 ^ 63 -> bv_signed (Z_to_bv 64 v) = v.
Proof.
  intros v H. unfold bv_signed. rewrite unsigned_lit by lia. unfold bv_swrap.
  change (bv_half_modulus 64) with (2 ^ 63).
  change (bv_wrap 64 (v + 2 ^ 63)) with ((v + 2 ^ 63) mod 2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

(* `addi a0, s1, 3; srliw s4, a0, 2; slli s4, s4, 2` on n <= 4096: o = NL_ALIGN(n) *)
Lemma o_word : forall c, 0 <= c <= 4096 ->
  Z_to_bv 64 (Z.shiftl (bv_swrap 32 (Z.shiftr (bv_wrap 32 (c + 3)) 2) mod 18446744073709551616) 2) =
  Z_to_bv 64 (4 * ((c + 3) / 4)).
Proof.
  intros c H. f_equal.
  change (bv_wrap 32 (c + 3)) with ((c + 3) mod 2 ^ 32). rewrite (Z.mod_small (c + 3) (2 ^ 32)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (D : 0 <= (c + 3) / 4 <= 1025) by (Z.div_mod_to_equations; lia).
  unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_wrap 32 ((c + 3) / 4 + 2 ^ 31)) with (((c + 3) / 4 + 2 ^ 31) mod 2 ^ 32).
  rewrite (Z.mod_small ((c + 3) / 4 + 2 ^ 31) (2 ^ 32)) by lia.
  replace ((c + 3) / 4 + 2 ^ 31 - 2 ^ 31) with ((c + 3) / 4) by lia.
  rewrite (Z.mod_small ((c + 3) / 4) 18446744073709551616) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. lia.
Qed.

Lemma sx32_lit : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. exact sx32_wz. Qed.

Lemma wr_at_split : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m a (n1 + n2) <-> wr_at rsegs m a n1 /\ wr_at rsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). split; (split; [lia|]); (split; [lia|]).
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_split by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)). rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_cb_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma rw_cells_cb_len : forall m A n bs, rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.

Lemma rw_cells_nil : forall m A, 0 <= A <= 2 ^ 64 -> rw_cells rsegs m A [CB 0 []].
Proof.
  intros m A H. split; [split|].
  - cbn. split; [reflexivity|exact I].
  - cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact H.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Lemma rw_cells_cb_split : forall m A (n1 n2 : nat) bs, rw_cells rsegs m A [CB (n1 + n2) bs] ->
  rw_cells rsegs m A [CB n1 (firstn n1 bs)] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs H. pose proof (rw_cells_cb_len _ _ _ _ H) as L.
  apply (rw_cells_split_CB rsegs m A [] (n1 + n2) bs [] [n1; n2]) in H; [|cbn; lia].
  cbn [app mk_CB_cells] in H.
  rewrite (firstn_all2 (n := n2)) in H by (rewrite length_skipn; lia).
  change [CB n1 (firstn n1 bs); CB n2 (skipn n1 bs)] with ([CB n1 (firstn n1 bs)] ++ [CB n2 (skipn n1 bs)]) in H.
  apply rw_cells_app in H. cbn [cells_size csize] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma rw_cells_cb_join : forall m A (n1 n2 : nat) b1 b2,
  rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells rsegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2.
  assert (H : rw_cells rsegs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply rw_cells_app. cbn [cells_size csize]. rewrite Nat.add_0_r. split; assumption. }
  apply (rw_cells_merge rsegs m A [] ([CB n1 b1] ++ [CB n2 b2]) []) in H.
  cbn [app cells_size csize cells_bytes cbytes] in H. rewrite Nat.add_0_r, app_nil_r in H. exact H.
Qed.

Lemma rw_cells_squash : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. apply (rw_cells_merge rsegs m A [] cs []). cbn [app]. rewrite app_nil_r. exact H.
Qed.

Lemma bytes_at_sub : forall m a l k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hl. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

(* the buffer after the walk: the chunk, the zeros to the 4-byte boundary, the rest *)
Lemma buf3 : forall m A k1 k2 L b1 b2 b3, 0 <= k1 <= k2 -> k2 <= L ->
  rw_cells rsegs m A [CB (Z.to_nat k1) b1] -> rw_cells rsegs m (A + k1) [CB (Z.to_nat (k2 - k1)) b2] ->
  rw_cells rsegs m (A + k2) [CB (Z.to_nat (L - k2)) b3] ->
  bytes_at rsegs m A (b1 ++ b2 ++ b3) /\ Z.of_nat (length (b2 ++ b3)) = L - k1.
Proof.
  intros m A k1 k2 L b1 b2 b3 Hk HL H1 H2 H3.
  pose proof (rw_cells_cb_len _ _ _ _ H1) as L1. pose proof (rw_cells_cb_len _ _ _ _ H2) as L2.
  pose proof (rw_cells_cb_len _ _ _ _ H3) as L3.
  apply rw_cells_cb_bytes in H1, H2, H3.
  split; [|rewrite length_app; lia].
  apply bytes_at_app. split; [exact H1|]. apply bytes_at_app. split.
  - eapply bytes_at_at; [exact H2|]. lia.
  - eapply bytes_at_at; [exact H3|]. rewrite L1, L2. lia.
Qed.

Lemma buf_post : forall m A k1 k2 L b1 b2 b3, 0 <= k1 <= k2 -> k2 <= L ->
  rw_cells rsegs m A [CB (Z.to_nat k1) b1] -> rw_cells rsegs m (A + k1) [CB (Z.to_nat (k2 - k1)) b2] ->
  rw_cells rsegs m (A + k2) [CB (Z.to_nat (L - k2)) b3] ->
  exists rest, bytes_at rsegs m A (b1 ++ rest) /\ Z.of_nat (length rest) = L - k1.
Proof.
  intros m A k1 k2 L b1 b2 b3 Hk HL H1 H2 H3.
  destruct (buf3 m A k1 k2 L b1 b2 b3 Hk HL H1 H2 H3) as [B LL]. exists (b2 ++ b3). split; assumption.
Qed.

(* L8 (the buffer stays `rw_cells` on every path). Success: the three pieces the walk leaves join back into one CB
   of len bytes. Failure: the errno store may land inside the buffer (the Pre does not keep errno apart from it), so
   the buffer is rebuilt from its write permission (kept by `wr_at_write`) and the bytes every address of it has. *)
Lemma buf_rw : forall m A k1 k2 L b1 b2 b3, 0 <= k1 <= k2 -> k2 <= L ->
  rw_cells rsegs m A [CB (Z.to_nat k1) b1] -> rw_cells rsegs m (A + k1) [CB (Z.to_nat (k2 - k1)) b2] ->
  rw_cells rsegs m (A + k2) [CB (Z.to_nat (L - k2)) b3] ->
  exists junk, rw_cells rsegs m A [CB (Z.to_nat L) junk].
Proof.
  intros m A k1 k2 L b1 b2 b3 Hk HL H1 H2 H3.
  assert (H2' : rw_cells rsegs m (A + Z.of_nat (Z.to_nat k1)) [CB (Z.to_nat (k2 - k1)) b2])
    by (rewrite Z2Nat.id by lia; exact H2).
  pose proof (rw_cells_cb_join m A _ _ _ _ H1 H2') as H12.
  assert (H3' : rw_cells rsegs m (A + Z.of_nat (Z.to_nat k1 + Z.to_nat (k2 - k1))) [CB (Z.to_nat (L - k2)) b3])
    by (replace (A + Z.of_nat (Z.to_nat k1 + Z.to_nat (k2 - k1))) with (A + k2) by lia; exact H3).
  pose proof (rw_cells_cb_join m A _ _ _ _ H12 H3') as H.
  replace (Z.to_nat k1 + Z.to_nat (k2 - k1) + Z.to_nat (L - k2))%nat with (Z.to_nat L) in H by lia.
  eexists. exact H.
Qed.

Lemma rcv_nth_seq : forall s n i, (i < n)%nat -> nth_error (seq s n) i = Some (s + i)%nat.
Proof.
  intros s n. revert s. induction n as [|n IH]; intros s i Hi; [lia|].
  destruct i as [|i]; cbn [seq nth_error]; [f_equal; lia|].
  rewrite IH by lia. f_equal; lia.
Qed.

Lemma rcv_cb_of : forall m A n, wr_at rsegs m A (Z.of_nat n) ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (A + Z.of_nat i)) = Some b) ->
  exists j, rw_cells rsegs m A [CB n j].
Proof.
  intros m A n W RD.
  set (f := fun i : nat => match mrd rsegs m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  exists (map f (seq 0 n)). pose proof W as (W0 & W1 & _).
  assert (L : length (map f (seq 0 n)) = n) by (rewrite length_map, length_seq; reflexivity).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite L; lia|].
    intros i Hi. rewrite L in Hi.
    erewrite map_nth_error; [|apply rcv_nth_seq; exact Hi].
    cbn [Nat.add]. unfold f. destruct (RD i Hi) as [b Hb]. rewrite Hb. reflexivity.
  - cbn [cells_size csize]. rewrite ?Nat.add_0_r. exact W.
Qed.

Lemma rcv_cb_write : forall m A n j a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  rw_cells rsegs m A [CB n j] -> exists j', rw_cells rsegs (write_to_mem m (wa a) bs) A [CB n j'].
Proof.
  intros m A n j a bs Ha Hal H.
  pose proof (rw_cells_cb_len _ _ _ _ H) as L.
  pose proof (rw_cells_cb_bytes _ _ _ _ H) as B.
  destruct H as [_ W]. cbn [cells_size csize] in W. rewrite ?Nat.add_0_r in W.
  apply rcv_cb_of; [apply wr_at_write; exact W |].
  intros i Hi. rewrite (nth_error_write rsegs m a bs A j i B Ha Hal) by lia.
  destruct (Z.leb_spec0 a (A + Z.of_nat i)); destruct (Z.ltb_spec0 (A + Z.of_nat i) (a + Z.of_nat (length bs)));
    cbn [andb].
  all: first [ destruct (nth_error bs (Z.to_nat (A + Z.of_nat i - a))) as [b|] eqn:E;
               [exists b; reflexivity | apply nth_error_None in E; lia]
             | destruct (nth_error j i) as [b|] eqn:E; [exists b; reflexivity | apply nth_error_None in E; lia] ].
Qed.

(* A callee wrote [A, B) and left cells there: a stack window keeps its readable bytes. The buffer of recv may lie
   anywhere the contract allows, also below the frame, so `stk` cannot be moved by disjointness alone. *)
Lemma stk_cover : forall m m' lo hi A B cs, stk rsegs m lo hi -> munch [(A, B)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' A cs -> B <= A + Z.of_nat (cells_size cs) -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi A B cs (H1 & H2 & H) MU WM [[Hwf Hb] _] HB.
  pose proof (cells_bytes_length cs Hwf) as Lc.
  destruct Hb as (HA0 & HA1 & Hb'). rewrite Lc in HA1, Hb'.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hr)]. split; [apply WM; exact Hw|].
  destruct (Z_lt_le_dec a A) as [LA|LA]; [|destruct (Z_lt_le_dec a B) as [LB|LB]].
  - exists b. unfold mrd in *. rewrite MU; [exact Hr|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia|exact I].
  - specialize (Hb' (Z.to_nat (a - A)) ltac:(lia)).
    replace (A + Z.of_nat (Z.to_nat (a - A))) with a in Hb' by lia.
    rewrite Hb'. destruct (nth_error (cells_bytes cs) (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite Lc in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hr|]. cbn [outside]. rewrite wa_unsigned by lia.
    split; [lia|exact I].
Qed.

(* post_call (lib/Lib/Tac.v) with two changes: the callee's addresses are read through `unsigned_lit`, and a stack
   window is carried over the callee's footprint by the cells the callee left there (stk_cover). *)
Ltac rcv_post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc [MIc PO]]]];
  subst ms';
  try destruct_ands PO;
  repeat match goal with H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ => rewrite (unsigned_lit z) in H by lia end;
  lazymatch type of MUc with
  | munch [(?A, ?B)] m ?m' =>
      try (lazymatch goal with
           | ST : stk segs m ?lo ?hi, RW : rw_cells segs m' A ?cs |- _ =>
               let ST' := fresh "ST" in
               pose proof (stk_cover m m' lo hi A B cs ST MUc WMc RW ltac:(cbn [cells_size csize]; lia)) as ST';
               clear ST
           end);
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* A byte store of a whole register (`sb s4, 0(s2)`) leaves `le1 v`, and one of the zero register leaves
   `Z_to_le_bytes 1 _`: both are one byte, a C1 cell. *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Step.cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

(* the 36 bytes one turn of the loop writes, cut out of the bytes left, and put back *)
Lemma split36 : forall m P L j, 36 <= L -> rw_cells rsegs m P [CB (Z.to_nat L) j] ->
  exists j0 j1 j2, rw_cells rsegs m P [CB 6 j0] /\ rw_cells rsegs m (P + 6) [CB 30 j1] /\
                   rw_cells rsegs m (P + 36) [CB (Z.to_nat (L - 36)) j2].
Proof.
  intros m P L j HL H.
  replace (Z.to_nat L) with (6 + (30 + Z.to_nat (L - 36)))%nat in H by lia.
  apply rw_cells_cb_split in H. destruct H as [H0 H].
  apply rw_cells_cb_split in H. destruct H as [H1 H2].
  do 3 eexists. split; [exact H0|]. split; [exact H1|].
  replace (P + 36) with (P + Z.of_nat 6 + Z.of_nat 30) by lia. exact H2.
Qed.

Lemma join36 : forall m P L cs0 cs1 j2, 36 <= L ->
  cells_size cs0 = 6%nat -> cells_size cs1 = 30%nat ->
  rw_cells rsegs m P cs0 -> rw_cells rsegs m (P + 6) cs1 -> rw_cells rsegs m (P + 36) [CB (Z.to_nat (L - 36)) j2] ->
  exists j, rw_cells rsegs m P [CB (Z.to_nat L) j].
Proof.
  intros m P L cs0 cs1 j2 HL S0 S1 H0 H1 H2.
  apply rw_cells_squash in H0, H1. rewrite S0 in H0. rewrite S1 in H1.
  pose proof (rw_cells_cb_join m P 6 30 _ _ H0 H1) as H01.
  assert (H2' : rw_cells rsegs m (P + Z.of_nat (6 + 30)) [CB (Z.to_nat (L - 36)) j2])
    by (replace (P + Z.of_nat (6 + 30)) with (P + 36) by lia; exact H2).
  pose proof (rw_cells_cb_join m P (6 + 30) (Z.to_nat (L - 36)) _ _ H01 H2') as H.
  replace (6 + 30 + Z.to_nat (L - 36))%nat with (Z.to_nat L) in H by lia.
  eexists. exact H.
Qed.

(* ==========================================================================
   2. The loop (0x136f0-0x13734): one NLMSG_ERROR record of 36 bytes per turn while o + 36 <= len
   ========================================================================== *)

Lemma rcv_loop : forall (len B : Z) (n : nat) (P o Q : Z) (m : word -> option byte) (j : list byte)
    (s0w s1w x1 x2 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27
     x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  bv_unsigned s0w = len -> P = B + o -> Q = o + 36 -> 0 <= o -> o + 36 <= len -> len - o <= Z.of_nat n ->
  0 <= B -> B + len <= 2 ^ 64 -> len + 72 <= 2 ^ 64 ->
  rw_cells rsegs m P [CB (Z.to_nat (len - o)) j] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms => exists y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y28 y29 y30 y31 m',
       ms = MS (mkR y1 x2 x3 x4 y5 y6 y7 s0w s1w y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23
                    x24 x25 x26 x27 y28 y29 y30 y31) F (Z_to_bv 64 0x13748) fc None m' (seg_rom rsegs)
       /\ munch [(P, B + len)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ exists j', rw_cells rsegs m' P [CB (Z.to_nat (len - o)) j'])
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 s0w s1w x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 P) (Z_to_bv 64 Q)
             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x136f0) fc None m (seg_rom rsegs)).
Proof.
  intros len B n. induction n as [|n IH];
    intros P o Q m j s0w s1w x1 x2 x3 x4 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31 F fc Hs0 EP EQ Ho Ho36 Hn HB HBL HL72 RW MI.
  { cbn in Hn. lia. }
  destruct (split36 m P (len - o) j ltac:(lia) RW) as (j0 & j1 & j2 & R0 & R1 & R2). clear RW.
  pose proof (munch_refl [(P, B + len)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word s0w) as Rs0. unfold inr64 in Rs0.
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply memset_holds with (junk := j1);
      [ rewrite ?unsigned_lit by lia; exact R1 | exact MI ]
    | rcv_post_call rsegs mm ] end.
  match goal with H : rw_cells _ _ (P + 6) _ |- _ => change (Z.to_nat 30) with 30%nat in H end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  lazymatch goal with
  | H0 : rw_cells _ ?mm P ?c0, H1 : rw_cells _ ?mm (P + 6) ?c1 |- _ => rename H0 into C0; rename H1 into C1
  end.
  if_cases K.
  - zify_cond K.
    replace (len - o - 36) with (len - (o + 36)) in R2 by lia.
    eapply evt_mono.
    + eapply (IH (P + 36) (o + 36)); [eassumption | lia | lia | lia | lia | lia | lia | lia | lia | exact R2 | eassumption].
    + intros ms' (y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23
                 & y28 & y29 & y30 & y31 & m' & -> & MU' & WM' & MI' & j' & RW').
      do 23 eexists. split; [reflexivity|].
      split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']];
              unfold sub_fp; cbn [outside]; intros; lia|].
      split; [eapply wmono_trans; eassumption|]. split; [exact MI'|].
      apply (rw_cells_transport rsegs [(P + 36, B + len)] _ m') in C0;
        [|exact MU'|exact WM'|cbn [disjoint_from cells_size csize]; lia].
      apply (rw_cells_transport rsegs [(P + 36, B + len)] _ m') in C1;
        [|exact MU'|exact WM'|cbn [disjoint_from cells_size csize]; lia].
      replace (len - (o + 36)) with (len - o - 36) in RW' by lia.
      eapply join36; [lia | | | exact C0 | exact C1 | exact RW']; reflexivity.
  - zify_cond K.
    zstep.
    apply evt_done. do 23 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    replace (len - o - 36) with (len - (o + 36)) in R2 by lia.
    eapply join36; [lia | | | exact C0 | exact C1 | ]; [reflexivity | reflexivity |].
    replace (len - o - 36) with (len - (o + 36)) by lia. exact R2.
Qed.

(* ==========================================================================
   3. The walk, cut at the join points
   ========================================================================== *)

Definition rcv_wr : bvmap 5 word -> (word -> option byte) -> list ivl :=
  ltac:(let t := eval cbv delta [fuzz_recv_contract] in fuzz_recv_contract in
        lazymatch t with leaf _ _ _ ?W _ => exact W end).
Definition rcv_post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(let t := eval cbv delta [fuzz_recv_contract] in fuzz_recv_contract in
        lazymatch t with leaf _ _ _ _ ?P => exact P end).

Section Recv.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo : Z) (bs pre post : list byte).

Hypothesis NK0 : nlk_at m0 bs.
Hypothesis WF0 : nlk_wf bs.
Hypothesis Epre : pre = firstn (Z.to_nat NK_N_CHUNKS) bs.
Hypothesis Epost : post = skipn (Z.to_nat NK_N_CHUNKS + 4 * 9) bs.
Hypothesis HFA : bv_unsigned sp + -80 + 80 <= 203648 \/ 475640 <= bv_unsigned sp + -80.
Hypothesis HEF : bv_unsigned tp + -164 + 4 <= bv_unsigned sp + -80 \/ bv_unsigned sp <= bv_unsigned tp + -164.
Hypothesis HEG : bv_unsigned tp + -164 + 4 <= 203648 \/ 475640 <= bv_unsigned tp + -164.
Hypothesis HER : 0 <= bv_unsigned tp + -164 /\ bv_unsigned tp + -164 + 4 <= 2 ^ 64.
Hypothesis HLEN : 4096 <= bv_unsigned a2.
Hypothesis HBG : bv_unsigned a1 + bv_unsigned a2 <= 203648 \/ 475640 <= bv_unsigned a1.
Hypothesis HBF : bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp + -80 \/ bv_unsigned sp <= bv_unsigned a1.
Hypothesis HBR : 0 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 <= 2 ^ 64.
Hypothesis HLO : 0 <= lo /\ lo + 80 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp < 2 ^ 63.

Local Abbreviation R0 := (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Local Abbreviation SP80 := (Z_to_bv 64 (bv_unsigned sp + -80)).
Local Abbreviation W0 := [(bv_unsigned sp + -80, bv_unsigned sp); (466308, 466340);
                      (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4);
                      (bv_unsigned a1, bv_unsigned a1 + bv_unsigned a2)].
Local Abbreviation FRC j := [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Abbreviation MSU := (if (bv_unsigned a0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1).
Local Abbreviation CELLS x1 mu :=
  [C4 (Z_to_bv 64 (nk_n_chunks bs)); C4 x1; C4 (Z_to_bv 64 (nk_end_errno bs));
   C4 (Z_to_bv 64 (nk_socket_errno bs)); C4 (Z_to_bv 64 (nk_send_errno bs)); C4 (Z_to_bv 64 (nk_open bs));
   C4 (Z_to_bv 64 (nk_opened bs)); C4 (Z_to_bv 64 (nk_closed bs)); C4 mu].
Local Abbreviation CLEN := (fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs)).
Local Abbreviation OO := (4 * ((fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs) + 3) / 4)).

Definition QQ : machine_state -> Prop := fun ms' =>
  exists (regs' : bvmap 5 word) (m' : word -> option byte),
    ms' = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    regs_preserved R0 regs' /\
    munch ((bv_unsigned sp - 80, bv_unsigned sp) :: rcv_wr R0 m0) m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    rcv_post R0 m0 regs' m'.

Lemma LPre : Z.of_nat (length pre) = 262656.
Proof using NK0 Epre. clear - NK0 Epre. pose proof NK0 as [_ HL]. subst pre. rewrite length_firstn. nk_nums. lia. Qed.
Lemma LPo : Z.of_nat (length post) = 9300.
Proof using NK0 Epost. clear - NK0 Epost. pose proof NK0 as [_ HL]. subst post. rewrite length_skipn. nk_nums. lia. Qed.

Ltac rcv_ranges :=
  pose proof (zr_word sp) as Rsp; unfold inr64 in Rsp;
  pose proof (zr_word tp) as Rtp; unfold inr64 in Rtp;
  pose proof (zr_word a1) as Ra1; unfold inr64 in Ra1;
  pose proof (zr_word a2) as Ra2; unfold inr64 in Ra2;
  pose proof LPre as LPre'; pose proof LPo as LPo';
  pose proof WF0 as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13);
  unfold NL_CHUNKS, NL_CHUNK_MAX, NL_SENT_MAX, NL_SENT_LEN in W1, W3, W12, W13.

(* side conditions with no variable in them, decided by computation (lia would case-split the context) *)
Ltac zclosed := vm_compute; first [reflexivity | congruence].
Ltac rdn_cells_f :=
  repeat first [ rewrite rdn_le4_head by reflexivity | rewrite rdn_le4_cons by zclosed ].

(* the Post, from the nine cells the walk leaves *)
Lemma recv_post : forall m' (x0 x1 x2 x3 x4 x5 x6 x7 x8 : word) (regs' : bvmap 5 word),
  bytes_at rsegs m' 203648 pre ->
  rw_cells rsegs m' 466304 [C4 x0; C4 x1; C4 x2; C4 x3; C4 x4; C4 x5; C4 x6; C4 x7; C4 x8] ->
  bytes_at rsegs m' 466340 post ->
  wr_at rsegs m' 203648 271992 ->
  bv_unsigned x0 mod 2 ^ 32 = nk_n_chunks bs -> bv_unsigned x2 mod 2 ^ 32 = nk_end_errno bs ->
  bv_unsigned x3 mod 2 ^ 32 = nk_socket_errno bs -> bv_unsigned x4 mod 2 ^ 32 = nk_send_errno bs ->
  bv_unsigned x5 mod 2 ^ 32 = nk_open bs -> bv_unsigned x6 mod 2 ^ 32 = nk_opened bs ->
  bv_unsigned x7 mod 2 ^ 32 = nk_closed bs -> bv_unsigned x8 mod 2 ^ 32 = MSU ->
  (nk_n_chunks bs <= nk_next bs ->
     getr regs' 10 = wz (-1) /\ bv_unsigned x1 mod 2 ^ 32 = nk_next bs /\
     u32_at m' (bv_unsigned tp + -164) (nk_end_errno bs)) ->
  (nk_next bs < nk_n_chunks bs ->
     getr regs' 10 = wz (Z.of_nat (length (nk_chunk bs (nk_next bs)))) /\
     bv_unsigned x1 mod 2 ^ 32 = nk_next bs + 1 /\
     exists rest, bytes_at rsegs m' (bv_unsigned a1) (nk_chunk bs (nk_next bs) ++ rest)
       /\ Z.of_nat (length rest) = bv_unsigned a2 - Z.of_nat (length (nk_chunk bs (nk_next bs)))) ->
  (exists junk, rw_cells rsegs m' (bv_unsigned a1) [CB (Z.to_nat (bv_unsigned a2)) junk]) ->
  rcv_post R0 m0 regs' m'.
Proof.
  intros m' x0 x1 x2 x3 x4 x5 x6 x7 x8 regs' B1 C B3 W V0 V2 V3 V4 V5 V6 V7 V8 VE VO RB.
  clear HFA HEF HEG HBG HBF HBR HER HLO HSP.
  unfold rcv_post. cbv beta. rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_errno. unfold ERRNO_TP_OFF.
  intros bs0 NKb. rewrite (nlk_at_unique m0 bs0 bs NKb NK0). clear bs0 NKb.
  pose proof NK0 as [_ HL]. subst pre post.
  destruct (nlk_join_rd m' bs NK_N_CHUNKS [C4 x0; C4 x1; C4 x2; C4 x3; C4 x4; C4 x5; C4 x6; C4 x7; C4 x8] HL
              ltac:(kn_side) ltac:(kn_side) ltac:(kn_side) B1 C B3 W) as (bs' & NK' & HL' & OUT & IN).
  exists bs'. split; [exact NK'|].
  cbn [cells_size csize cells_bytes cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OUT, IN.
  assert (O : forall a n, 0 <= a -> 0 <= n -> a + n <= 262656 -> rdn bs' a n = rdn bs a n /\ slice bs' a n = slice bs a n)
    by (intros a n Ha Hn H; apply (OUT a n Ha Hn); nk_nums; lia).
  assert (O2 : forall a n, 0 <= n -> 262692 <= a -> rdn bs' a n = rdn bs a n)
    by (intros a n Hn H; apply (OUT a n ltac:(lia) Hn); nk_nums; lia).
  pose proof WF0 as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  unfold NL_CHUNKS, NL_CHUNK_MAX, NL_SENT_MAX, NL_SENT_LEN in W1, W3, W12, W13.
  assert (ENC : nk_n_chunks bs' = nk_n_chunks bs)
    by (unfold nk_n_chunks at 1, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; exact V0).
  assert (ENX : nk_next bs' = bv_unsigned x1 mod 2 ^ 32)
    by (unfold nk_next, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; reflexivity).
  assert (EEE : nk_end_errno bs' = nk_end_errno bs)
    by (unfold nk_end_errno at 1, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; exact V2).
  assert (ESE : nk_socket_errno bs' = nk_socket_errno bs)
    by (unfold nk_socket_errno at 1, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; exact V3).
  assert (ESD : nk_send_errno bs' = nk_send_errno bs)
    by (unfold nk_send_errno at 1, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; exact V4).
  assert (EOP : nk_open bs' = nk_open bs)
    by (unfold nk_open at 1, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; exact V5).
  assert (EOD : nk_opened bs' = nk_opened bs)
    by (unfold nk_opened at 1, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; exact V6).
  assert (ECL : nk_closed bs' = nk_closed bs)
    by (unfold nk_closed at 1, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; exact V7).
  assert (EMI : nk_misuse bs' = MSU)
    by (unfold nk_misuse at 1, fld_u32; rewrite IN by zclosed; nk_nums; rdn_cells_f; exact V8).
  assert (ENS : nk_n_sent bs' = nk_n_sent bs) by (unfold nk_n_sent, fld_u32; nk_nums; apply O2; zclosed).
  assert (ENI : nk_n_if bs' = nk_n_if bs) by (unfold nk_n_if, fld_u32; nk_nums; apply O2; zclosed).
  assert (ECH : nk_chunks bs' = nk_chunks bs).
  { clear V0 V2 V3 V4 V5 V6 V7 V8 VE VO ENX EEE ESE ESD EOP EOD ECL EMI ENS ENI.
    unfold nk_chunks. rewrite ENC. apply map_ext_in. intros i Hi. apply in_seq in Hi.
    assert (Li : 0 <= fld_u64 bs (NK_CHUNK_LEN + 8 * Z.of_nat i) <= 4096) by (apply W12; lia).
    unfold nk_chunk. unfold fld_u64 in Li |- *. unfold NK_CHUNK, NK_CHUNK_LEN, NL_CHUNK_MAX in Li |- *.
    rewrite (proj1 (O (262144 + 8 * Z.of_nat i) 8 ltac:(lia) ltac:(lia) ltac:(lia))).
    eapply proj2. apply O; lia. }
  assert (Q1 : 0 <= bv_unsigned x1 mod 2 ^ 32 <= nk_n_chunks bs).
  { destruct (Z_le_gt_dec (nk_n_chunks bs) (nk_next bs)) as [Hc|Hc].
    - destruct (VE Hc) as (_ & -> & _). lia.
    - destruct (VO ltac:(lia)) as (_ & -> & _). lia. }
  split.
  - apply (nlk_wf_same_queues bs bs' WF0 ENC ENS ENI).
    + intros i Hi. unfold fld_u64, NK_CHUNK_LEN.
      rewrite (proj1 (O (262144 + 8 * i) 8 ltac:(lia) ltac:(lia) ltac:(lia))). reflexivity.
    + intros i Hi. unfold fld_u64, NK_SENT_LEN. apply O2; lia.
    + rewrite ENX. exact Q1.
    + rewrite EOP. exact W5.
    + rewrite EOD. exact W6.
    + rewrite ECL. exact W7.
    + rewrite EMI. destruct ((bv_unsigned a0 =? NL_FD) && negb (nk_open bs =? 0)); lia.
    + rewrite EEE. exact W9.
    + rewrite ESE. exact W10.
    + rewrite ESD. exact W11.
  - split; [exact ENC|]. split; [exact EEE|]. split; [exact ESE|]. split; [exact ESD|]. split; [exact ECH|].
    split; [exact EOP|]. split; [exact EOD|]. split; [exact ECL|]. split; [exact ENS|]. split; [exact EMI|].
    split; [intros Hc; destruct (VE Hc) as (R10 & X1 & EU); rewrite ENX; exact (conj R10 (conj X1 EU)) |].
    split; [intros Hc; destruct (VO Hc) as (R10 & X1 & RS); rewrite ENX; exact (conj R10 (conj X1 RS)) |].
    exact RB.
Qed.

Lemma rcv_exit : forall m (v : word) (j : list byte)
    x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
  rw_cells rsegs m (bv_unsigned sp + -80) (FRC j) ->
  stk rsegs m lo (bv_unsigned sp + -80) -> munch W0 m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  (forall regs', getr regs' 10 = v -> rcv_post R0 m0 regs' m) ->
  evt rsegs QQ (MS (mkR x1 SP80 gp tp x5 x6 x7 x8 v x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                        s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x13748) fc None m (seg_rom rsegs)).
Proof.
  intros m v j x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31
    FR ST MU WM MI HP.
  rcv_ranges.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold QQ. eexists _, _. split; [reflexivity|].
  split; [solve_rp|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  apply HP. reflexivity.
Qed.

Lemma chunk_length : nk_next bs < nk_n_chunks bs -> length (nk_chunk bs (nk_next bs)) = Z.to_nat CLEN.
Proof using NK0 WF0.
  clear - NK0 WF0. intros H. pose proof NK0 as [_ HL].
  pose proof WF0 as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  unfold NL_CHUNKS, NL_CHUNK_MAX in W1, W12.
  assert (CL : 0 <= CLEN <= 4096) by (apply W12; lia).
  unfold nk_chunk. apply slice_length; unfold NK_CHUNK, NL_CHUNK_MAX, NK_SIZE in *; lia.
Qed.

(* the end of a path through the buffer: the epilogue and the Post, from the chunk, the zeros after it and the bytes
   after those (B1, B2, B3 at a1, a1 + n, a1 + o); the same three pieces give the whole buffer back (L8) *)
Ltac vfld := rewrite unsigned_lit by lia; apply Z.mod_small; lia.
Ltac o_exit LC nx clen :=
  eapply rcv_exit; [eassumption | eassumption | eassumption | eassumption | eassumption |];
  let regs' := fresh "regs'" in let Hr := fresh "Hr" in intros regs' Hr;
  eapply recv_post;
  [ eassumption | eassumption | eassumption | eassumption
  | vfld | vfld | vfld | vfld | vfld | vfld | vfld
  | eassumption | intros; exfalso; lia |
  | eapply buf_rw; [ | | eassumption | eassumption | eassumption ]; lia ];
  intros _;
  change (nk_next bs) with nx; change (fld_u64 bs (NK_CHUNK_LEN + 8 * nx)) with clen;
  (split; [rewrite Hr; unfold wz; f_equal; rewrite LC; lia |]);
  (split; [vfld |]);
  rewrite LC, Z2Nat.id by lia;
  eapply buf_post; [ | | eassumption | eassumption | eassumption ]; lia.

Lemma rcv_o : forall m (w mu : word) (j j2 : list byte) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  nk_next bs < nk_n_chunks bs ->
  w = Z_to_bv 64 OO ->
  bv_unsigned mu mod 2 ^ 32 = MSU ->
  rw_cells rsegs m (bv_unsigned sp + -80) (FRC j) ->
  stk rsegs m lo (bv_unsigned sp + -80) -> munch W0 m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m 203648 pre ->
  rw_cells rsegs m 466304 (CELLS (Z_to_bv 64 (nk_next bs + 1)) mu) ->
  bytes_at rsegs m 466340 post ->
  wr_at rsegs m 203648 271992 ->
  wr_at rsegs m (bv_unsigned tp + -164) 4 ->
  rw_cells rsegs m (bv_unsigned a1) [CB (Z.to_nat CLEN) (nk_chunk bs (nk_next bs))] ->
  rw_cells rsegs m (bv_unsigned a1 + CLEN) [CB (Z.to_nat (bv_unsigned a2 - CLEN)) j2] ->
  evt rsegs QQ (MS (mkR x1 SP80 gp tp x5 x6 x7 a2 (Z_to_bv 64 CLEN) x10 x11 x12 x13 x14 x15 x16 x17
                        a1 s3 w s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x136c4) fc None m (seg_rom rsegs)).
Proof.
  intros m w mu j j2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HN -> HMU FR ST MU WM MI PRE CE
    PST WRA WE B1 B2.
  rcv_ranges.
  pose proof (chunk_length HN) as LC.
  set (nx := nk_next bs) in *. set (clen := fld_u64 bs (NK_CHUNK_LEN + 8 * nx)) in *.
  assert (CL : 0 <= clen <= 4096) by (apply W12; lia).
  set (o := 4 * ((clen + 3) / 4)) in *.
  assert (Oo : clen <= o <= clen + 3 /\ o <= 4096) by (subst o; clear - CL; Z.div_mod_to_equations; lia).
  replace (Z.to_nat (bv_unsigned a2 - clen)) with (Z.to_nat (o - clen) + Z.to_nat (bv_unsigned a2 - o))%nat in B2
    by lia.
  apply rw_cells_cb_split in B2. destruct B2 as [B2 B3].
  replace (bv_unsigned a1 + clen + Z.of_nat (Z.to_nat (o - clen))) with (bv_unsigned a1 + o) in B3 by lia.
  zstep. zstep. zstep. zstep.
  destruct (Z_lt_le_dec (bv_unsigned a1 + clen) (2 ^ 64)) as [NW|WR].
  - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply memset_holds with (junk := firstn (Z.to_nat (o - clen)) j2);
        [ rewrite !unsigned_lit by lia; exact B2 | exact MI ]
      | rcv_post_call rsegs mm ] end.
    zstep. zstep. if_cases K; zify_cond K.
    + o_exit LC nx clen.
    + zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply (rcv_loop (bv_unsigned a2) (bv_unsigned a1) (Z.to_nat (bv_unsigned a2)) (bv_unsigned a1 + o) o
                    (o + 36) mm);
          [ reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | lia | lia | exact B3 | eassumption ]
        | ] end.
      intros ms' (y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21
                  & y22 & y23 & y28 & y29 & y30 & y31 & m' & -> & MUl & WMl & MIl & jl & RWl).
      lazymatch goal with ST : stk _ ?mm lo _ |- _ =>
        let ST' := fresh "ST" in
        pose proof (stk_cover mm m' lo _ _ _ _ ST MUl WMl RWl ltac:(cbn [cells_size csize]; lia)) as ST';
        clear ST;
        transport_after_call rsegs mm m' MUl WMl
      end.
      clear MUl WMl.
      o_exit LC nx clen.
  - (* the chunk ends at the top of the address space: n = len = 4096, and the memset writes nothing *)
    assert (Eo : o = clen) by lia.
    assert (E64 : bv_unsigned a1 + clen = 2 ^ 64) by lia.
    replace (Z_to_bv 64 (bv_unsigned a1 + clen)) with (Z_to_bv 64 0) by (apply Z_to_bv_eqm; rewrite E64; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply memset_holds with (junk := []);
        [ rewrite !unsigned_lit by lia; replace (Z.to_nat (o - clen)) with 0%nat by lia; apply rw_cells_nil; lia
        | exact MI ]
      | rcv_post_call rsegs mm ] end.
    zstep. zstep. if_cases K; zify_cond K.
    + o_exit LC nx clen.
    + exfalso. lia.
Qed.

Lemma rcv_n : forall m (v mu : word) (j jb : list byte) x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  nk_next bs < nk_n_chunks bs ->
  v = Z_to_bv 64 CLEN ->
  bv_unsigned mu mod 2 ^ 32 = MSU ->
  rw_cells rsegs m (bv_unsigned sp + -80) (FRC j) ->
  stk rsegs m lo (bv_unsigned sp + -80) -> munch W0 m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m 203648 pre ->
  rw_cells rsegs m 466304 (CELLS (Z_to_bv 64 (nk_next bs)) mu) ->
  bytes_at rsegs m 466340 post ->
  wr_at rsegs m 203648 271992 ->
  wr_at rsegs m (bv_unsigned tp + -164) 4 ->
  rw_cells rsegs m (bv_unsigned a1) [CB (Z.to_nat (bv_unsigned a2)) jb] ->
  evt rsegs QQ (MS (mkR ra SP80 gp tp x5 x6 x7 a2 v (Z_to_bv 64 465792) (Z_to_bv 64 203648) (Z_to_bv 64 (nk_next bs))
                        x13 x14 x15 x16 x17 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x13694) fc None m (seg_rom rsegs)).
Proof.
  intros m v mu j jb x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 HN -> HMU FR ST MU WM MI PRE CE PST WRA WE BUF.
  rcv_ranges.
  pose proof (chunk_length HN) as LC.
  assert (CL : 0 <= CLEN <= 4096) by (apply W12; lia).
  assert (SRC : bytes_at rsegs m (203648 + 4096 * nk_next bs) (nk_chunk bs (nk_next bs))).
  { pose proof (bytes_at_sub m 203648 pre (Z.to_nat (4096 * nk_next bs)) (Z.to_nat CLEN) PRE ltac:(lia)) as S.
    rewrite Z2Nat.id in S by lia.
    replace (nk_chunk bs (nk_next bs)) with (slice pre (4096 * nk_next bs) CLEN); [exact S|].
    rewrite Epre, slice_firstn by (unfold NK_N_CHUNKS; lia). unfold nk_chunk, NK_CHUNK, NL_CHUNK_MAX. f_equal; lia. }
  replace (Z.to_nat (bv_unsigned a2)) with (Z.to_nat CLEN + Z.to_nat (bv_unsigned a2 - CLEN))%nat in BUF by lia.
  apply rw_cells_cb_split in BUF. destruct BUF as [B1 B2]. rewrite Z2Nat.id in B2 by lia.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply memcpy_holds with (src := nk_chunk bs (nk_next bs)) (junk := firstn (Z.to_nat CLEN) jb);
      [ rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 12) with 4096; rewrite unsigned_lit by lia;
        eapply bytes_at_at; [exact SRC | lia]
      | rewrite unsigned_lit by lia; exact LC
      | rewrite unsigned_lit by lia; exact B1
      | rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 12) with 4096; rewrite !unsigned_lit by lia; lia
      | exact MI ]
    | rcv_post_call rsegs mm ] end.
  zstep. zstep. zstep.
  rewrite (o_word _ CL).
  assert (OO1 : CLEN <= OO <= 4096) by (clear - CL; Z.div_mod_to_equations; lia).
  zstep. if_cases K; zify_cond K.
  - eapply rcv_o; [lia | reflexivity | exact HMU | eassumption .. ].
  - zstep. eapply (rcv_o _ a2); [lia | | exact HMU | eassumption .. ].
    apply bv_eq. rewrite unsigned_lit by lia. lia.
Qed.

Lemma rcv_head : forall m (mu : word) (j jb : list byte) x5 x6 x7 x10 x14 x15 x16 x17 x28 x29 x30 x31,
  bv_unsigned mu mod 2 ^ 32 = MSU ->
  rw_cells rsegs m (bv_unsigned sp + -80) (FRC j) ->
  stk rsegs m lo (bv_unsigned sp + -80) -> munch W0 m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  bytes_at rsegs m 203648 pre ->
  rw_cells rsegs m 466304 (CELLS (Z_to_bv 64 (nk_next bs)) mu) ->
  bytes_at rsegs m 466340 post ->
  wr_at rsegs m 203648 271992 ->
  wr_at rsegs m (bv_unsigned tp + -164) 4 ->
  rw_cells rsegs m (bv_unsigned a1) [CB (Z.to_nat (bv_unsigned a2)) jb] ->
  evt rsegs QQ (MS (mkR ra SP80 gp tp x5 x6 x7 a2 s1 x10 (Z_to_bv 64 203648) (Z_to_bv 64 465792) (Z_to_bv 64 7)
                        x14 x15 x16 x17 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x13668) fc None m (seg_rom rsegs)).
Proof.
  intros m mu j jb x5 x6 x7 x10 x14 x15 x16 x17 x28 x29 x30 x31 HMU FR ST MU WM MI PRE CE PST WRA WE BUF.
  rcv_ranges.
  zstep. zstep. zstep. rewrite sx32_lit by lia. zstep. rewrite sx32_lit by lia.
  zstep. if_cases K; zify_cond K; rewrite ?signed_lit in K by lia.
  - (* next >= n_chunks: errno := end_errno, answer -1 *)
    zstep. rewrite sx32_lit by lia.
    zstep. zstep. zstep. zstep.
    match goal with WE : wr_at _ ?mm (bv_unsigned tp + -164) 4 |- _ =>
      pose proof (wr_at_store_ok rsegs mm (bv_unsigned tp + -164) 4 0 4 WE ltac:(lia) ltac:(lia)) as HSe end.
    rewrite Z.add_0_r in HSe.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      assert (ERB : bytes_at rsegs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; rewrite ?length_le4; lia);
      (* L8: the store may fall inside the buffer; the buffer keeps its permission and some bytes *)
      assert (BUF' : exists jb', rw_cells rsegs (write_to_mem mm (wa E) bs) (bv_unsigned a1)
                                   [CB (Z.to_nat (bv_unsigned a2)) jb'])
        by (eapply rcv_cb_write; [lia | rewrite ?length_le4; lia | eassumption])
    end.
    destruct BUF' as [jb' BUF']. clear BUF.
    store_done.
    zstep.
    eapply rcv_exit; [eassumption | eassumption | eassumption | eassumption | eassumption |].
    intros regs' Hr.
    eapply recv_post; [eassumption | eassumption | eassumption | eassumption | .. ];
      [ rewrite unsigned_lit by lia; apply Z.mod_small; lia .. | exact HMU | | intros; exfalso; lia
      | exists jb'; exact BUF' ].
    intros _. split; [rewrite Hr; unfold wz; first [reflexivity | apply bv_eq; reflexivity] |].
    split; [rewrite unsigned_lit by lia; apply Z.mod_small; lia |].
    exact ERB.
  - (* next < n_chunks *)
    zstep. zstep. zstep.
    assert (HR : ov_read_bytes rsegs m (wa (465792 + Z.shiftl (nk_next bs) 3)) 8 = Some (le8 (Z_to_bv 64 CLEN))).
    { replace (465792 + Z.shiftl (nk_next bs) 3) with (203648 + (262144 + 8 * nk_next bs))
        by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; lia).
      rewrite (bytes_at_read rsegs m 203648 pre (262144 + 8 * nk_next bs) 8 PRE) by lia.
      f_equal.
      change (firstn 8 (skipn (Z.to_nat (262144 + 8 * nk_next bs)) pre)) with (slice pre (262144 + 8 * nk_next bs) 8).
      pose proof NK0 as [_ HL].
      rewrite Epre, slice_firstn by (unfold NK_N_CHUNKS; lia). apply rdn_le8_slice; unfold NK_SIZE in HL; lia. }
    zstep.
    assert (CL : 0 <= CLEN <= 4096) by (apply W12; lia).
    zstep. if_cases K4; zify_cond K4.
    + eapply rcv_n; [lia | reflexivity | exact HMU | eassumption .. ].
    + zstep. eapply (rcv_n _ a2); [lia | | exact HMU | eassumption .. ].
      apply bv_eq. rewrite unsigned_lit by lia. lia.
Qed.

Lemma rcv_entry : forall jb,
  wr_at rsegs m0 (bv_unsigned tp + -164) 4 ->
  rw_cells rsegs m0 (bv_unsigned a1) [CB (Z.to_nat (bv_unsigned a2)) jb] ->
  mem_inv rsegs m0 -> stk rsegs m0 lo (bv_unsigned sp) ->
  evt rsegs QQ (MS R0 F (Z_to_bv 64 0x13610) fc None m0 (seg_rom rsegs)).
Proof.
  intros jb WE BUF MI ST.
  rcv_ranges.
  assert (SP0 : 0 <= NK_N_CHUNKS) by (unfold NK_N_CHUNKS; lia).
  assert (SP1 : NK_N_CHUNKS + 4 * Z.of_nat 9 <= NK_SIZE) by (unfold NK_N_CHUNKS, NK_SIZE; lia).
  destruct (nlk_split_u32 m0 bs NK_N_CHUNKS 9 NK0 SP0 SP1) as (PRE & CE & PST & WRA). clear SP0 SP1.
  change (u32_cells bs NK_N_CHUNKS 9) with (CELLS (Z_to_bv 64 (nk_next bs)) (Z_to_bv 64 (nk_misuse bs))) in CE.
  change (A_G_NL + NK_N_CHUNKS) with 466304 in CE.
  change (A_G_NL + NK_N_CHUNKS + 4 * Z.of_nat 9) with 466340 in PST.
  change A_G_NL with 203648 in PRE, WRA. change NK_SIZE with 271992 in WRA.
  rewrite <- Epre in PRE. rewrite <- Epost in PST.
  carve_frame 80%nat ST.
  pose proof (munch_refl W0 m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K.
  - (* fd <> NL_FD: misuse *)
    zify_cond K.
    zstep. zstep.
    eapply rcv_head; [ | eassumption .. ].
    rewrite unsigned_lit by lia. unfold NL_FD. rewrite (proj2 (Z.eqb_neq _ _) K). reflexivity.
  - zify_cond K.
    zstep. rewrite sx32_lit by lia. zstep. if_cases K2.
    + (* open <> 0: no misuse *)
      zify_cond K2.
      eapply rcv_head; [ | eassumption .. ].
      rewrite unsigned_lit by lia. unfold NL_FD. rewrite K, Z.eqb_refl, (proj2 (Z.eqb_neq _ _) K2).
      cbn [andb negb]. apply Z.mod_small. lia.
    + (* open = 0: misuse *)
      zify_cond K2.
      zstep. zstep.
      eapply rcv_head; [ | eassumption .. ].
      rewrite unsigned_lit by lia. unfold NL_FD. rewrite K2, Z.eqb_refl. cbn [andb negb].
      destruct (bv_unsigned a0 =? 7); reflexivity.
Qed.

End Recv.

Theorem fuzz_recv_holds : fuzz_recv_contract.
Proof.
  unfold fuzz_recv_contract. apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in H |- *.
    unfold frame_apart_gnl, apart_frame, apart_gnl, errno_at, spZ, arg in *. rewrite <- ?E. exact H.
  - intros r1 r2 m E. cbv beta. unfold errno_at, arg. rewrite <- ?E. reflexivity.
  - intros r1 r2 m q1 q2 m' E E' H. cbv beta in H |- *. unfold errno_at, arg in *. rewrite <- ?E, <- ?E'. exact H.
  - unfold leaf_walk, FUZZ_RECV.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros (bs & junk & NK & FA & WF & WE & EF & EG & LEN & BUF & BG & BF) MI ST LO SP.
    unfold frame_apart_gnl, apart_frame, apart_gnl, A_G_NL, NK_SIZE, NL_CHUNK_MAX in FA, EF, EG, BG, BF, LEN.
    change (spZ (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
      with (bv_unsigned sp) in FA, EF, BF.
    change (errno_at (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
      with (bv_unsigned tp + -164) in WE, EF, EG.
    change (arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 1)
      with (bv_unsigned a1) in BUF, BG, BF.
    change (arg (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 2)
      with (bv_unsigned a2) in LEN, BUF, BG, BF.
    pose proof (rw_cells_bound _ _ _ _ BUF) as BUFB. cbn [cells_size csize] in BUFB.
    pose proof WE as [WE0 [WE1 _]].
    pose proof ST as [STlo _].
    pose proof (zr_word a2) as Ra2. unfold inr64 in Ra2.
    eapply (rcv_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo bs (firstn (Z.to_nat NK_N_CHUNKS) bs) (skipn (Z.to_nat NK_N_CHUNKS + 4 * 9) bs)).
    all: first [ eassumption | reflexivity | lia ].
Qed.
