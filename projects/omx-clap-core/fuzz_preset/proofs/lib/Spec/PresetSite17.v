(* omx-clap-core/fuzz_preset, Spec: P8 part D3 -- the 768-byte class 17 at every consumer site of the harness model,
   per-site accounting (h-hpreset-7's port of asan_halts / agrees, piece P8; c-frame-alloc).

   WHAT IT SAYS.
   - n17t t counts the nodes of a tree that can own a class-17 block (requests 449 .. 640, is17_eq): a container with
     1 .. 8 items (its 464-byte kids array), an object with 33 .. 64 members (its 528-byte keys array), a string value
     or member name of decoded length >= 72, a number of text length >= 432. A string block is its raw span + 1 + 16 in
     the text it was read from, and a decoded byte takes at most 6 bytes of that span (decode_q6), so a class-17 string
     block has decoded length >= 72.
   - blocks17_read / blocks17_ttrace: the blocks a tree holds after its parse (of the input, or of the writer's text)
     have at most n17t t class-17 members. n17t_copy_set: the rewrite's pj_set adds at most 2.
   - rb_pos: position i of hruns lies in the read-back parse of round trip 2 (the tree t read back from its pretty
     text) or of round trip 3 (copy_set ms read back), in call os1's successor, at offset k of that parse. Only a call
     where no check_no_overread reading ran out (PresetRun.ranout) makes the round trips.
   - live17_two: at every consumer allocation of hruns that is not an rb_pos, the live class-17 count is at most
     2 M17 + 6, M17 bounding the class-17 requests of one parse of x and of the trace of x's tree.
   - rt_site17: at an rb_pos, the free history is pre ++ F ++ X with F the frees of the writer chain of the text read
     back (no class-17 request: every capacity is 4096 * 2 ^ j) and X the frees after it (rendered ()'s chain at round
     trip 2, then the read-back parse's frees so far); X has at most nc9 t' + nk65 t' + 1 class-17 members, and the
     live class-17 count PLUS X's is at most n17t t + n17t t + n17t t' + nc9 t' + nk65 t' + 4 (t the doc tree, t' the
     tree read back: t at round trip 2, copy_set ms at round trip 3).
   - wsum_n17: D1's node weights (PjWeight.wsum) pay for n17t + nk65, nc9 and the longest piece (PresetPiece.lmax):
     wa (n17t u + nk65 u) + wc nc9 u + [w_lmin <= lmax u] w_len lmax u <= wsum W u when wa is at most each of
     w_c18, w_k64, w_str, w_num and wc at most w_c9.

   WHY THE JOINT FORM. In the middle of a parse, an open container's kids array (464 bytes, class 17) is live before
   the container has its 9th item; when it ends with 9 or more items n17t does not count it (nc9 does). So the live
   count alone is not bounded by three n17t terms plus a constant: sanity_open below has six nested 9-item arrays,
   n17t = 0, and 5 live class-17 blocks at a round trip 2 read-back allocation. Every class-17 request of the read-back
   parse so far is either still live or freed into X (cnt_live_frees), which gives the joint bound; the quarantine
   flush lemma (PresetRoom.quar17_flush) takes X's class-17 count with X's bytes.

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss PresetRun PresetFlush PjWeight PresetPiece.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PjCharge.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ class 17 *)

(* PresetRoom's class 17 (the 768-byte chunks) *)
Definition is17 (q : Z) : bool := PresetRoom.in_cls 17 q.

(* case on the class-17 test the goal makes *)
Ltac d17 E := match goal with |- context [is17 ?q] => destruct (is17 q) eqn:E end.

(* PjGrammar's zb and sinj (section-local there) *)
Ltac zbx := repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ || _)%bool = false |- _ => apply orb_false_iff in H; destruct H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
  | H : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
  end.

Ltac sinjx H := apply some_inj in H; apply pair_inj in H; let H1 := fresh in let H2 := fresh in destruct H as [H1 H2].

Fixpoint chk17 (n : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f => Bool.eqb (is17 n) (in17 n) && chk17 (n + 1) f
  end.

Lemma chk17_ok : forall f n m, chk17 n f = true -> n <= m < n + Z.of_nat f -> is17 m = in17 m.
Proof.
  induction f as [|f IH]; intros n m H Hm; [lia|].
  cbn [chk17] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec m n) as [->|Hne].
  - apply Bool.eqb_prop in H1. exact H1.
  - apply (IH (n + 1) m H2). lia.
Qed.

Lemma chk17_run : chk17 1 (Z.to_nat 65536) = true.
Proof. vm_compute. reflexivity. Qed.

(* class 17 is exactly the requests 449 .. 640 (PresetFlush.in17) *)
Theorem is17_eq : forall q, is17 q = in17 q.
Proof.
  intros q. destruct (Z_lt_le_dec q 1) as [Hq|Hq].
  - assert (E : PresetRoom.needed0 q = 24).
    { unfold PresetRoom.needed0, PresetRoom.rounded_size, PresetRoom.rz_size, PresetRoom.rz_log, PresetRoom.rup.
      rewrite Z.max_r by lia. rewrite (proj2 (Z.leb_le q 48)) by lia. reflexivity. }
    unfold is17, PresetRoom.in_cls, PresetRoom.cls, PresetRoom.is_primary. rewrite E.
    unfold in17. rewrite (proj2 (Z.leb_gt 449 q)) by lia. vm_compute. reflexivity.
  - destruct (Z_le_gt_dec q 65536) as [Hh|Hh].
    + apply (chk17_ok (Z.to_nat 65536) 1 q chk17_run). rewrite Z2Nat.id by lia. lia.
    + assert (A : is17 q = false).
      { unfold is17, PresetRoom.in_cls, PresetRoom.cls.
        destruct (PresetRoom.is_primary q) eqn:Ep; [|reflexivity].
        pose proof (PresetRoom.cls_small q ltac:(lia) Ep). unfold PresetRoom.K_MAX_SIZE in *. lia. }
      rewrite A. unfold in17. rewrite (proj2 (Z.leb_gt q 640)) by lia. rewrite andb_false_r. reflexivity.
Qed.

Lemma is17_range : forall q, is17 q = true -> 449 <= q <= 640.
Proof.
  intros q H. rewrite is17_eq in H. unfold in17 in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1, H2. lia.
Qed.

Lemma not17_big : forall q, 641 <= q -> is17 q = false.
Proof. intros q H. rewrite is17_eq. unfold in17. rewrite (proj2 (Z.leb_gt q 640)) by lia. apply andb_false_r. Qed.

Lemma not17_small : forall q, q < 449 -> is17 q = false.
Proof. intros q H. rewrite is17_eq. unfold in17. rewrite (proj2 (Z.leb_gt 449 q)) by lia. reflexivity. Qed.

Lemma cnt17_in17 : forall l, cnt is17 l = cnt in17 l.
Proof. intros l. unfold cnt. rewrite (filter_ext is17 in17 is17_eq). reflexivity. Qed.

Lemma cnt_nil : forall f, cnt f [] = 0%nat.
Proof. reflexivity. Qed.

Lemma cnt_def : forall f l, length (filter f l) = cnt f l.
Proof. reflexivity. Qed.

Lemma cnt_cons0 : forall a l, is17 a = false -> cnt is17 (a :: l) = cnt is17 l.
Proof. intros a l H. rewrite cnt_cons_eqR, H. reflexivity. Qed.

Lemma cnt_none17 : forall l, Forall (fun q => is17 q = false) l -> cnt is17 l = 0%nat.
Proof. intros l H. induction H as [|q l Hq _ IH]; [reflexivity|]. rewrite cnt_cons0 by exact Hq. exact IH. Qed.

(* ================================================================ n17t: the nodes that can own a class-17 block *)

Definition c17 (n : nat) : nat := if (Nat.leb 1 n && Nat.leb n 8)%bool then 1%nat else 0%nat.
Definition k17 (n : nat) : nat := if (Nat.leb 33 n && Nat.leb n 64)%bool then 1%nat else 0%nat.
Definition s17 (s : list Z) : nat := if Nat.leb 72 (length s) then 1%nat else 0%nat.

(* containers with 1 .. 8 items (464-byte kids array), objects with 33 .. 64 members (528-byte keys array), strings
   and member names of decoded length >= 72, numbers of text length >= 432 *)
Fixpoint n17t (t : jv) : nat :=
  match t with
  | JNum txt _ => if Nat.leb 432 (length txt) then 1%nat else 0%nat
  | JStr s => s17 s
  | JArr items => (c17 (length items) + list_sum (map n17t items))%nat
  | JObj ms => (c17 (length ms) + k17 (length ms) + list_sum (map (fun '(k, u) => (s17 k + n17t u)%nat) ms))%nat
  | _ => 0%nat
  end.

(* ---------------------------------------------------------------- a container's arrays *)

Lemma ncap_inv : forall n, (n = 0%nat /\ ncap n = 0%nat) \/
  (exists j, Z.of_nat (ncap n) = 8 * 2 ^ Z.of_nat j /\ (1 <= n <= ncap n)%nat /\ (ncap n = 8 \/ ncap n < 2 * n)%nat).
Proof.
  induction n as [|n IH]; [left; split; reflexivity|].
  right. cbn [ncap]. unfold gcap.
  destruct IH as [[-> E] | (j & Ej & Hn & Hc)].
  - rewrite E. cbn. exists 0%nat. split; [reflexivity|]. lia.
  - destruct (Nat.ltb_spec n (ncap n)) as [Hl|Hl].
    + exists j. split; [exact Ej|]. lia.
    + destruct (Nat.eqb_spec (ncap n) 0) as [E0|E0]; [lia|].
      exists (S j). split.
      * rewrite Nat2Z.inj_mul, Ej, (Nat2Z.inj_succ j), Z.pow_succ_r by lia. lia.
      * lia.
Qed.

Lemma arrz17 : forall n,
  (cnt is17 (arrz false (ncap n)) <= c17 n)%nat /\ (cnt is17 (arrz true (ncap n)) <= c17 n + k17 n)%nat.
Proof.
  intros n. destruct (ncap_inv n) as [[-> E] | (j & Ej & Hn & Hc)].
  - rewrite E. cbn [arrz]. rewrite cnt_nil. lia.
  - set (c := ncap n) in *. clearbody c.
    assert (Ha : forall o, arrz o c = (Z.of_nat (56 * c) + HEAD) :: (if o then [Z.of_nat (8 * c) + HEAD] else [])).
    { intros o. destruct c as [|c']; [lia|reflexivity]. }
    assert (K1 : ((if is17 (Z.of_nat (56 * c) + HEAD) then 1 else 0) <= c17 n)%nat).
    { d17 E1; [|lia]. rewrite is17_eq in E1.
      pose proof (kids17 c j Ej E1) as Hc8. unfold c17.
      destruct (Nat.leb_spec 1 n); destruct (Nat.leb_spec n 8); cbn; lia. }
    assert (K2 : ((if is17 (Z.of_nat (8 * c) + HEAD) then 1 else 0) <= k17 n)%nat).
    { d17 E2; [|lia]. rewrite is17_eq in E2.
      pose proof (keys17 c j Ej E2) as Hc64. unfold k17.
      destruct (Nat.leb_spec 33 n); destruct (Nat.leb_spec n 64); cbn; lia. }
    split.
    + rewrite (Ha false), cnt_cons_eqR, cnt_nil. lia.
    + rewrite (Ha true), !cnt_cons_eqR, cnt_nil. lia.
Qed.

(* the per-item count of a container's items: an object's member name and each value *)
Definition msum (o : bool) (L : list (list Z * jv)) : nat :=
  list_sum (map (fun m => ((if o then s17 (fst m) else 0) + n17t (snd m))%nat) L).

Lemma msum_nil : forall o, msum o [] = 0%nat.
Proof. reflexivity. Qed.

Lemma msum_cons : forall o k u L, msum o ((k, u) :: L) = ((if o then s17 k else 0) + n17t u + msum o L)%nat.
Proof. intros o k u L. unfold msum. rewrite map_cons, lsum_cons. reflexivity. Qed.

Lemma msum_obj : forall L, msum true L = list_sum (map (fun '(k, u) => (s17 k + n17t u)%nat) L).
Proof. induction L as [|[k u] r IH]; [reflexivity|]. rewrite msum_cons, map_cons, lsum_cons, IH. reflexivity. Qed.

Lemma msum_arr : forall L, msum false L = list_sum (map n17t (map snd L)).
Proof. induction L as [|[k u] r IH]; [reflexivity|]. rewrite msum_cons, !map_cons, lsum_cons, IH. reflexivity. Qed.

Lemma mk17 : forall o L, (cnt is17 (arrz o (ncap (length L))) + msum o L <= n17t (mk o L))%nat.
Proof.
  intros o L. destruct (arrz17 (length L)) as [H1 H2]. destruct o; unfold mk; cbn [n17t].
  - rewrite msum_obj. lia.
  - rewrite msum_arr, length_map. lia.
Qed.

(* ---------------------------------------------------------------- a string block's span *)

Lemma utf8_ne : forall cp, (1 <= length (utf8 cp))%nat.
Proof.
  intros cp. unfold utf8. destruct (cp <? 128); [cbn; lia|]. destruct (cp <? 2048); [cbn; lia|].
  destruct (cp <? 65536); cbn; lia.
Qed.

Lemma utf8_big : forall cp, 65536 <= cp -> length (utf8 cp) = 4%nat.
Proof.
  intros cp H. unfold utf8.
  rewrite (proj2 (Z.ltb_ge cp 128)), (proj2 (Z.ltb_ge cp 2048)), (proj2 (Z.ltb_ge cp 65536)) by lia. reflexivity.
Qed.

(* a decoded string of length k comes from at most 6 k bytes before its closing quote *)
Lemma decode_q6 : forall x s r, decode x = Some (s, r) -> exists q, scan x = Some q /\ (q <= 6 * length s)%nat.
Proof.
  intro x. remember (length x) as n eqn:Hn. revert x Hn.
  induction n as [n IH] using lt_wf_ind. intros x Hn s r H.
  destruct x as [|b r0]; [discriminate|]. cbn [decode] in H.
  destruct (b =? 34) eqn:E34.
  - sinjx H. subst s r. exists 0%nat. cbn [scan]. rewrite E34. split; [reflexivity|]. cbn [length]. lia.
  - destruct (b <? 32) eqn:E32; [discriminate|].
    destruct (negb (b =? 92)) eqn:E92.
    + destruct (decode r0) as [[s1 r1]|] eqn:Hd; [|discriminate]. sinjx H. subst s r.
      simpl in Hn. destruct (IH (length r0) ltac:(lia) r0 eq_refl s1 r1 Hd) as (q1 & Hs & Hl).
      zbx. exists (S q1). rewrite scan_ndq by lia. rewrite Hs.
      split; [reflexivity|]. cbn [app length]. lia.
    + zbx. subst b.
      destruct r0 as [|e r2]; [discriminate|].
      destruct (e =? 117) eqn:Eu.
      * zbx. subst e.
        destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; try discriminate.
        destruct (hex4 (h0 :: h1 :: h2 :: h3 :: r3)) as [cp|] eqn:Hx; [|discriminate].
        destruct (hex4_some _ _ Hx) as (a0 & a1 & a2 & a3 & r' & Heq & N0 & N0' & N1 & N1' & N2 & N2' & N3 & N3' & Hcp).
        inversion Heq; subst a0 a1 a2 a3 r'. clear Heq.
        destruct (cp =? 0) eqn:Ec0; [discriminate|]. zbx.
        destruct ((55296 <=? cp) && (cp <? 56320)) eqn:Ehi.
        -- zbx. destruct r3 as [|b1 [|b2 [|m0 [|m1 [|m2 [|m3 r4]]]]]]; try discriminate.
           destruct (low (b1 :: b2 :: m0 :: m1 :: m2 :: m3 :: r4)) as [lo|] eqn:Hl; [|discriminate].
           destruct (low_some _ _ Hl) as (n0 & n1 & n2 & n3 & r'' & Heq & M0 & M0' & M1 & M1' & M2 & M2' & M3 & M3' & Hlo).
           inversion Heq; subst b1 b2 n0 n1 n2 n3 r''. clear Heq.
           destruct (decode r4) as [[s4 r5]|] eqn:Hd; [|discriminate]. sinjx H. subst s r.
           simpl in Hn.
           destruct (IH (length r4) ltac:(lia) r4 eq_refl s4 r5 Hd) as (q4 & Hs & Hlen).
           exists (12 + q4)%nat.
           rewrite scan_bs. rewrite !scan_ndq by assumption. rewrite scan_bs. rewrite !scan_ndq by assumption.
           rewrite Hs. split; [reflexivity|].
           assert (Hp : 65536 <= pair_cp cp lo) by (unfold pair_cp; lia).
           rewrite length_app, (utf8_big _ Hp). lia.
        -- destruct ((56320 <=? cp) && (cp <? 57344)) eqn:Elo; [discriminate|].
           destruct (decode r3) as [[s3 r5]|] eqn:Hd; [|discriminate]. sinjx H. subst s r.
           simpl in Hn.
           destruct (IH (length r3) ltac:(lia) r3 eq_refl s3 r5 Hd) as (q3 & Hs & Hlen).
           exists (6 + q3)%nat.
           rewrite scan_bs. rewrite !scan_ndq by assumption.
           rewrite Hs. split; [reflexivity|].
           pose proof (utf8_ne cp). rewrite length_app. lia.
      * destruct (escape e) as [c|] eqn:He; [|discriminate].
        destruct (decode r2) as [[s2 r5]|] eqn:Hd; [|discriminate]. sinjx H. subst s r.
        simpl in Hn.
        destruct (IH (length r2) ltac:(lia) r2 eq_refl s2 r5 Hd) as (q2 & Hs & Hlen).
        exists (S (S q2)). rewrite scan_bs, Hs.
        split; [reflexivity|]. cbn [app length]. lia.
Qed.

Lemma str17 : forall q s, (q <= 6 * length s)%nat -> is17 (Z.of_nat (S q) + HEAD) = true -> s17 s = 1%nat.
Proof.
  intros q s Hq H. apply is17_range in H. unfold HEAD in H. unfold s17.
  destruct (Nat.leb_spec 72 (length s)); lia.
Qed.

(* ---------------------------------------------------------------- the blocks of a parse *)

(* the event list es, from any state s, leaves the requests B on top of s *)
Definition BLK (es : list hev) (B : list Z) : Prop :=
  forall s, okf s es /\ Permutation (hlive_from s es) (B ++ s).

Lemma BLK_nil : BLK [] [].
Proof. intros s. split; [exact I | apply Permutation_refl]. Qed.

Lemma BLK_alloc : forall q, BLK (rd_hevs [EAlloc q]) [Z.of_nat q + HEAD].
Proof. intros q s. split; [split; exact I | apply Permutation_refl]. Qed.

Lemma BLK_app : forall a b A B, BLK a A -> BLK b B -> BLK (a ++ b) (B ++ A).
Proof.
  intros a b A B HA HB s. destruct (HA s) as [A1 A2]. destruct (HB (A ++ s)) as [B1 B2]. split.
  - apply okf_app. split; [exact A1|]. exact (okf_perm b (A ++ s) _ (Permutation_sym A2) B1).
  - rewrite hlive_from_app. apply (Permutation_trans (hlive_from_perm b _ _ A2)). rewrite <- app_assoc. exact B2.
Qed.

(* a value: its blocks, at most n17t v of class 17 *)
Definition VB (v : jv) (tr : list ev) : Prop := exists B, BLK (rd_hevs tr) B /\ (cnt is17 B <= n17t v)%nat.

(* a container's item loop from n items in arrays of capacity cap: the items L it adds, their blocks B *)
Definition LB (o : bool) (n cap : nat) (acc : list (list Z * jv)) (v : jv) (tr : list ev) : Prop :=
  exists L B, v = mk o (rev acc ++ L) /\
    (forall s, okf (arrz o cap ++ s) (rd_hevs tr) /\
       Permutation (hlive_from (arrz o cap ++ s) (rd_hevs tr)) (arrz o (capf n cap (length L)) ++ B ++ s)) /\
    (cnt is17 B <= msum o L)%nat.

Lemma name_blk : forall o y ok nm y1 tn ok2, jr_name o y ok = (Some (nm, y1), tn, ok2) ->
  exists K, BLK (rd_hevs tn) K /\ (cnt is17 K <= (if o then s17 nm else 0))%nat.
Proof.
  intros o y ok nm y1 tn ok2 H. destruct o.
  - unfold jr_name in H. destruct (skip y) as [|b z]; [unfold jrefuse in H; discriminate|].
    destruct (b =? 34); [|unfold jrefuse in H; discriminate].
    apply jbind_some in H as ([nm0 r] & t1 & ok1 & t2 & Hs & H & ->). cbv beta iota in H.
    destruct (skip r) as [|c r1]; [cbv [jbind jfree jrefuse] in H; discriminate|].
    destruct (c =? 58); [|cbv [jbind jfree jrefuse] in H; discriminate].
    unfold jret in H. injection H; intros; subst.
    pose proof (jr_string_spec z ok) as Hp. rewrite Hs in Hp. destruct Hp as (q & Hsc & Hd & -> & _).
    destruct (decode_q6 z nm r Hd) as (q' & Hsc' & Hq). rewrite Hsc in Hsc'. injection Hsc' as <-.
    exists [Z.of_nat (S q) + HEAD]. split.
    + rewrite app_nil_r. apply BLK_alloc.
    + rewrite cnt_cons_eqR, cnt_nil. d17 E; [|lia].
      rewrite (str17 q nm Hq E). lia.
  - unfold jr_name, jret in H. injection H; intros; subst. exists []. split; [apply BLK_nil | apply Nat.le_0_l].
Qed.

Section Read.

Variable sm : list Z -> Z * Z.

Lemma num_tr : forall x ok u r tr ok', jr_number sm x ok = (Some (u, r), tr, ok') ->
  exists txt bits, u = JNum txt bits /\ tr = [EAlloc (S (length txt))].
Proof.
  intros x ok u r tr ok' H. unfold jr_number in H. cbv zeta in H.
  destruct (skipn _ x) as [|c z]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct (negb (digit c)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  destruct ((c =? 48) && match z with c1 :: _ => digit c1 | [] => false end)%bool; cbv beta iota in H;
    [unfold jrefuse in H; discriminate|].
  destruct (span numch z) as [a r0]. cbv beta iota in H.
  apply jbind_some in H as ([] & t1 & ok1 & t2 & E1 & E2 & ->).
  unfold jalloc, take in E1.
  destruct ok as [|b ok]; [|destruct b]; cbv beta iota in E1; [injection E1; intros; subst..|discriminate].
  all: cbv beta in E2.
  all: match type of E2 with context [whole sm ?T] => destruct (whole sm T) end;
       [unfold jret in E2; injection E2; intros; subst | unfold jrefuse in E2; discriminate].
  all: do 2 eexists; split; reflexivity.
Qed.

Lemma cont_blk : forall f d o b y ok v r tr ok',
  (forall d o n cap acc y ok v r tr ok', jrl sm f d o n cap acc y ok = (Some (v, r), tr, ok') -> LB o n cap acc v tr) ->
  jr_cont (jrl sm f) d o (b :: y) ok = (Some (v, r), tr, ok') -> VB v tr.
Proof.
  intros f d o b y ok v r tr ok' IHl H. unfold jr_cont in H.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota in H; [unfold jrefuse in H; discriminate|].
  cbn [tl] in H. cbv zeta in H.
  assert (Hloop : forall y', jrl sm f (S d) o 0 0 [] y' ok = (Some (v, r), tr, ok') -> VB v tr).
  { intros y' Hl. destruct (IHl _ _ _ _ _ _ _ _ _ _ _ Hl) as (L & B & -> & HB & Hc).
    exists (arrz o (ncap (length L)) ++ B). split.
    - intros s. destruct (HB s) as [B1 B2]. cbn [arrz app] in B1, B2. rewrite <- ncap_eq in B2.
      split; [exact B1|]. rewrite <- app_assoc. exact B2.
    - rewrite cnt_app. pose proof (mk17 o L). cbn [rev app]. lia. }
  destruct (skip y) as [|c r0]; [exact (Hloop _ H)|].
  destruct (c =? closer o); [|exact (Hloop _ H)].
  unfold jret in H. injection H; intros; subst. exists []. split; [apply BLK_nil | apply Nat.le_0_l].
Qed.

Lemma read_fuel : forall f,
  (forall d x ok v r tr ok', jrv sm f d x ok = (Some (v, r), tr, ok') -> VB v tr) /\
  (forall d o n cap acc y ok v r tr ok', jrl sm f d o n cap acc y ok = (Some (v, r), tr, ok') -> LB o n cap acc v tr).
Proof.
  induction f as [|f [IHv IHl]].
  - split; intros; cbn [jrv jrl] in *; unfold jrefuse in *; discriminate.
  - split.
    + intros d x ok v r tr ok' H. cbn [jrv] in H.
      destruct (skip x) as [|b y]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (b =? 123); cbv beta iota in H; [exact (cont_blk f d true b y ok v r tr ok' IHl H)|].
      destruct (b =? 91); cbv beta iota in H; [exact (cont_blk f d false b y ok v r tr ok' IHl H)|].
      destruct (b =? 34); cbv beta iota in H.
      { apply jbind_some in H as ([s r1] & t1 & ok1 & t2 & Hj & H & ->). cbv beta iota in H.
        unfold jret in H. injection H; intros; subst.
        pose proof (jr_string_spec y ok) as Hs. rewrite Hj in Hs. destruct Hs as (q & Hsc & Hd & -> & _).
        destruct (decode_q6 _ _ _ Hd) as (q' & Hsc' & Hq). rewrite Hsc in Hsc'. injection Hsc' as <-.
        exists [Z.of_nat (S q) + HEAD]. split; [rewrite app_nil_r; apply BLK_alloc|].
        rewrite cnt_cons_eqR, cnt_nil. cbn [n17t]. d17 E; [|lia].
        rewrite (str17 q _ Hq E). lia. }
      destruct (b =? 116); cbv beta iota in H.
      { destruct (PjCharge.lit_grows _ _ _ _ _ _ _ _ H) as [-> ->]. exists []. split; [apply BLK_nil | apply Nat.le_0_l]. }
      destruct (b =? 102); cbv beta iota in H.
      { destruct (PjCharge.lit_grows _ _ _ _ _ _ _ _ H) as [-> ->]. exists []. split; [apply BLK_nil | apply Nat.le_0_l]. }
      destruct (b =? 110); cbv beta iota in H.
      { destruct (PjCharge.lit_grows _ _ _ _ _ _ _ _ H) as [-> ->]. exists []. split; [apply BLK_nil | apply Nat.le_0_l]. }
      destruct (num_tr _ _ _ _ _ _ H) as (txt & bits & -> & ->).
      exists [Z.of_nat (S (length txt)) + HEAD]. split; [apply BLK_alloc|].
      rewrite cnt_cons_eqR, cnt_nil. cbn [n17t]. d17 E; [|lia].
      apply is17_range in E. unfold HEAD in E. destruct (Nat.leb_spec 432 (length txt)); lia.
    + intros d o n cap acc y ok v r tr ok' H. cbn [jrl] in H.
      apply jbind_some in H as (cap1 & tg & ok1 & t2 & Eg & H & ->). cbv beta in H.
      destruct (PjCharge.grow_some o n cap ok cap1 tg ok1 Eg) as [-> ->].
      apply jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & ->). cbv beta iota in H.
      apply jbind_some in H as ([v0 r0] & tv & ok3 & t4 & Ev & H & ->). cbv beta iota in H.
      destruct (name_blk o y ok1 nm y1 tn ok2 En) as (K & HK & cK).
      destruct (IHv d y1 ok2 v0 r0 tv ok3 Ev) as (Bv & HBv & cBv).
      (* the arrays after the grow, then the name and the value on top *)
      assert (Hpre : forall s, okf (arrz o cap ++ s) (rd_hevs (grow_ev o n cap ++ tn ++ tv)) /\
        Permutation (hlive_from (arrz o cap ++ s) (rd_hevs (grow_ev o n cap ++ tn ++ tv)))
                    (arrz o (gcap n cap) ++ Bv ++ K ++ s)).
      { intros s. destruct (grow_ev_ok o n cap s) as [G1 G2].
        destruct (BLK_app _ _ _ _ HK HBv (hlive_from (arrz o cap ++ s) (rd_hevs (grow_ev o n cap)))) as [N1 N2].
        rewrite !rd_hevs_app. split.
        - apply okf_app. split; [exact G1|]. exact N1.
        - rewrite hlive_from_app. apply (Permutation_trans N2).
          apply (Permutation_trans (Permutation_app_head (Bv ++ K) G2)).
          rewrite (app_assoc Bv K s). apply Permutation_app_swap_app. }
      destruct (skip r0) as [|c r1]; cbv beta iota in H; [unfold jrefuse in H; discriminate|].
      destruct (c =? 44); cbv beta iota in H.
      * destruct (IHl d o (S n) (gcap n cap) ((nm, v0) :: acc) r1 ok3 v r t4 ok' H) as (L & B & Ev' & HB & Hc).
        exists ((nm, v0) :: L), (B ++ Bv ++ K). split; [|split].
        -- rewrite Ev'. cbn [rev]. rewrite <- app_assoc. reflexivity.
        -- intros s. destruct (Hpre s) as [P1 P2]. destruct (HB (Bv ++ K ++ s)) as [B1 B2].
           assert (E : rd_hevs (grow_ev o n cap ++ tn ++ tv ++ t4) =
                       rd_hevs (grow_ev o n cap ++ tn ++ tv) ++ rd_hevs t4)
             by (rewrite !rd_hevs_app, <- !app_assoc; reflexivity).
           rewrite E. split.
           ++ apply okf_app. split; [exact P1|]. exact (okf_perm _ _ _ (Permutation_sym P2) B1).
           ++ rewrite hlive_from_app. apply (Permutation_trans (hlive_from_perm _ _ _ P2)).
              cbn [length capf]. rewrite <- !app_assoc. exact B2.
        -- rewrite msum_cons, !cnt_app. lia.
      * destruct (c =? closer o); cbv beta iota in H; [|unfold jrefuse in H; discriminate].
        unfold jret in H. injection H; intros; subst.
        exists [(nm, v0)], (Bv ++ K). split; [|split].
        -- cbn [rev]. reflexivity.
        -- intros s. destruct (Hpre s) as [P1 P2]. rewrite app_nil_r. split; [exact P1|].
           cbn [length capf]. rewrite <- app_assoc. exact P2.
        -- rewrite msum_cons, msum_nil, cnt_app. lia.
Qed.

End Read.

(* THE BLOCKS OF A READ TREE: whatever text t was read from, its blocks have at most n17t t of class 17. *)
Theorem blocks17_read : forall sm x t, json_read sm x = Some t ->
  (cnt is17 (rd_blocks (rtr sm [] x)) <= n17t t)%nat.
Proof.
  intros sm x t H. unfold json_read in H. unfold rtr. rewrite jr_run_eq in H |- *. cbn [fst snd] in H |- *.
  destruct (jr_value sm 0 x []) as [[[[t' r]|] tr] ok'] eqn:E; cbn [fst snd post] in H |- *; [|discriminate].
  destruct (skip r); [injection H as <-|discriminate].
  unfold jr_value in E. destruct (proj1 (read_fuel sm _) 0%nat x [] t' r tr ok' E) as (B & HB & Hc).
  destruct (HB []) as [_ HP]. unfold rd_blocks, hlive. rewrite (cnt_perm _ _ _ HP), app_nil_r. exact Hc.
Qed.

(* and the blocks of a written-and-read-back tree (PjRoundTrip.ttrace) *)
Theorem blocks17_ttrace : forall sm t, pj_wf sm t -> (cnt is17 (rd_blocks (ttrace t)) <= n17t t)%nat.
Proof.
  intros sm t Hw. pose proof (blocks17_read sm (wdoc t false) t (G9 sm t Hw false)) as H.
  unfold rtr in H. rewrite (G9_trace sm t Hw false) in H. exact H.
Qed.

Lemma set17_sum : forall ms,
  (list_sum (map (fun '(k, u) => (s17 k + n17t u)%nat) (pj_set_model ms MOD_KEY (JStr MOD_VAL))) <=
   list_sum (map (fun '(k, u) => (s17 k + n17t u)%nat) ms))%nat.
Proof.
  induction ms as [|[k v] r IH]; cbn [pj_set_model].
  - cbn. lia.
  - destruct (list_eq_dec Z.eq_dec k MOD_KEY) as [E|E]; rewrite !map_cons, !lsum_cons.
    + assert (N : n17t (JStr MOD_VAL) = 0%nat) by reflexivity. rewrite N. lia.
    + lia.
Qed.

(* the rewrite's pj_set ("modifiedAt": "2026-10-25T00:00:00Z"): its key and value are short, at most one more member *)
Theorem n17t_copy_set : forall ms, (n17t (copy_set ms) <= n17t (JObj ms) + 2)%nat.
Proof.
  intros ms. unfold copy_set. cbn [n17t]. pose proof (set17_sum ms) as H.
  set (n := length (pj_set_model ms MOD_KEY (JStr MOD_VAL))).
  assert (A : (c17 n <= 1)%nat) by (unfold c17; destruct (Nat.leb 1 n && Nat.leb n 8)%bool; lia).
  assert (B : (k17 n <= 1)%nat) by (unfold k17; destruct (Nat.leb 33 n && Nat.leb n 64)%bool; lia).
  lia.
Qed.

(* ================================================================ counting along an event list *)

Lemma step_cnt : forall f s e, hits s e -> (cnt f (hstep s e) + cnt f (hfree1 e) = cnt f s + prod_evR f e)%nat.
Proof.
  intros f s [n | m n | n | L] Hh; cbn [hstep hfree1 prod_evR hits] in *.
  - rewrite cnt_cons_eqR, cnt_nil. destruct (f n); lia.
  - rewrite !cnt_cons_eqR, cnt_nil. rewrite (cnt_perm f s _ (rm1_in m s Hh)), cnt_cons_eqR.
    destruct (f n), (f m); lia.
  - rewrite cnt_cons_eqR, cnt_nil. rewrite (cnt_perm f s _ (rm1_in n s Hh)), cnt_cons_eqR. destruct (f n); lia.
  - destruct Hh as [d Hd]. destruct (bulk_ok L s d Hd) as [_ HB]. cbn [hstep] in HB.
    rewrite (cnt_perm f _ _ HB), (cnt_perm f _ _ Hd), cnt_app. lia.
Qed.

(* every request of es is still live or freed by es *)
Theorem cnt_live_frees : forall f es s, okf s es ->
  (cnt f (hlive_from s es) + cnt f (hfrees es) = cnt f s + nprodR f es)%nat.
Proof.
  intros f es. induction es as [|e r IH]; intros s Hk.
  { change (hlive_from s []) with s. change (hfrees []) with (@nil Z). cbn [nprodR]. rewrite cnt_nil. lia. }
  destruct Hk as [Hh Hr]. rewrite hlive_from_cons.
  change (hfrees (e :: r)) with (hfree1 e ++ hfrees r). rewrite cnt_app. cbn [nprodR].
  pose proof (IH (hstep s e) Hr). pose proof (step_cnt f s e Hh). lia.
Qed.

Lemma okf_firstn : forall s es k, okf s es -> okf s (firstn k es).
Proof. intros s es k H. rewrite <- (firstn_skipn k es) in H. apply okf_app in H. exact (proj1 H). Qed.

Lemma nprodR_firstn : forall f es k, (nprodR f (firstn k es) <= nprodR f es)%nat.
Proof. intros f es k. rewrite <- (firstn_skipn k es) at 2. rewrite nprodR_app. lia. Qed.

Lemma cnt_hfrees_firstn : forall f es k, (cnt f (hfrees (firstn k es)) <= cnt f (hfrees es))%nat.
Proof. intros f es k. rewrite <- (firstn_skipn k es) at 2. rewrite hfrees_app, cnt_app. lia. Qed.

(* a read-back parse requests at most n17t + nc9 + nk65 class-17 blocks: the ones it keeps, and the 464-byte kids
   and 528-byte keys arrays it grows away (PresetFlush.c17_tt) *)
Lemma tt_prod17 : forall sm t, pj_wf sm t -> (nprodR is17 (rd_hevs (ttrace t)) <= n17t t + nc9 t + nk65 t)%nat.
Proof.
  intros sm t Hw. pose proof (cnt_live_frees is17 (rd_hevs (ttrace t)) [] (ttrace_okf t [])) as E.
  pose proof (blocks17_ttrace sm t Hw) as B. unfold rd_blocks, hlive in B.
  pose proof (c17_tt t) as C. rewrite <- cnt17_in17 in C. rewrite cnt_nil in E. lia.
Qed.

Lemma cnt_removelast : forall f l, (cnt f (removelast l) <= cnt f l)%nat.
Proof.
  intros f l. induction l as [|a l IH]; [cbn; lia|].
  destruct l as [|b l]; [apply Nat.le_0_l|].
  change (removelast (a :: b :: l)) with (a :: removelast (b :: l)).
  rewrite (cnt_cons_eqR f a (removelast (b :: l))), (cnt_cons_eqR f a (b :: l)). lia.
Qed.

(* ---------------------------------------------------------------- the writer's and rendered ()'s buffers *)

Lemma last_Forall : forall (P : Z -> Prop) l d, Forall P l -> P d -> P (last l d).
Proof.
  intros P l d Hl Hd. induction Hl as [|a l Ha Hl IH]; [exact Hd|].
  destruct l as [|b l]; [exact Ha | exact IH].
Qed.

Lemma Forall_removelast : forall (P : Z -> Prop) l, Forall P l -> Forall P (removelast l).
Proof.
  intros P l H. induction H as [|a l Ha Hl IH]; [constructor|].
  destruct l as [|b l]; [constructor | cbn [removelast]; constructor; assumption].
Qed.

Lemma wcaps_ge : forall t p, Forall (fun c => 4096 <= c) (wcaps t p).
Proof.
  intros t p. eapply Forall_impl; [|exact (wcaps_pow t p)]. intros c (j & Hj & ->).
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

(* the writer chain frees no class-17 request: each capacity is 4096 * 2 ^ j, its request cap + 16 *)
Theorem wchain_not17 : forall t p, Forall (fun q => is17 q = false) (hfrees (w_evs t p)).
Proof.
  intros t p. rewrite hfrees_w_evs. apply Forall_map.
  eapply Forall_impl; [|exact (Forall_removelast _ _ (wcaps_ge t p))]. intros c Hc. cbv beta in *.
  apply not17_big. unfold HEAD. lia.
Qed.

Lemma wlast_not17 : forall t p, is17 (last (wcaps t p) 0 + HEAD) = false.
Proof.
  intros t p. assert (H : (fun c => c = 0 \/ 4096 <= c) (last (wcaps t p) 0)).
  { apply last_Forall; [|left; reflexivity]. eapply Forall_impl; [|exact (wcaps_ge t p)]. intros c Hc. right. exact Hc. }
  cbv beta in H. destruct H as [-> | H]; [apply not17_small | apply not17_big]; unfold HEAD; lia.
Qed.

(* rendered ()'s capacities more than double, so at most one is in 449 .. 640 *)
Fixpoint dchain (c : Z) (l : list Z) : Prop :=
  match l with [] => True | z :: r => 2 * c < z /\ dchain z r end.

Lemma tx_dchain : forall ls n cap, 0 <= cap -> dchain cap (tx_caps n cap ls).
Proof.
  induction ls as [|k ls IH]; intros n cap Hc; cbn [tx_caps]; [exact I|].
  destruct (cap <? n + k + 1) eqn:E.
  - apply Z.ltb_lt in E. cbn [dchain]. split; [lia|]. apply IH. lia.
  - apply IH. exact Hc.
Qed.

Lemma dchain_gt : forall l c, 0 <= c -> dchain c l -> Forall (fun z => 2 * c < z) l.
Proof.
  induction l as [|z l IH]; intros c Hc H; [constructor|]. destruct H as [H1 H2].
  constructor; [exact H1|]. eapply Forall_impl; [|apply (IH z); [lia | exact H2]]. intros w Hw. cbv beta in *. lia.
Qed.

Lemma dchain_cnt : forall l c, 0 <= c -> dchain c l -> (cnt is17 l <= 1)%nat.
Proof.
  induction l as [|z l IH]; intros c Hc H; [cbn; lia|]. destruct H as [H1 H2].
  rewrite cnt_cons_eqR. destruct (is17 z) eqn:E.
  - apply is17_range in E.
    assert (C0 : cnt is17 l = 0%nat).
    { apply cnt_none17. eapply Forall_impl; [|exact (dchain_gt l z ltac:(lia) H2)].
      intros w Hw. cbv beta in Hw. apply not17_big. lia. }
    lia.
  - pose proof (IH z ltac:(lia) H2). lia.
Qed.

Lemma rcaps17 : forall t p, (cnt is17 (rcaps t p) <= 1)%nat.
Proof. intros t p. unfold rcaps. apply (dchain_cnt _ 0); [lia|]. apply tx_dchain. lia. Qed.

(* ================================================================ the call's segments *)

Definition hd3 (x : list Z) : list hev :=
  [HMal (Z.of_nat (length x) + FUZZ_PAD); HMal (Z.of_nat (length x) + FUZZ_PAD); HMal (Z.of_nat (length x) + FUZZ_PAD)].
Definition hdp (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) : list hev :=
  parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2) ++ parse_evs sm x (okof o0).
Definition hdf (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) : list hev :=
  p1_tfree sm x o1 ++ p1_tfree sm x o2 ++ p1_tfree sm x o0 ++
  [HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD)].

(* check_no_overread: the three copies, the three readings (not consumers), their frees *)
Definition call_head (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) : list hev :=
  hd3 x ++ hdp sm x o1 o2 o0 ++ hdf sm x o1 o2 o0.

(* expected ()'s scratch *)
Definition scr (x : list Z) : list hev := [HMal (Z.of_nat (length x) + 1); HFr (Z.of_nat (length x) + 1)].

(* check_round_trip after round trip 2's free of `back`: the rewrite, or pj_free (&copy) *)
Definition rt_end (sm : list Z -> Z * Z) (t : jv) : list hev :=
  match t with
  | JObj ms => rw_evs sm ms ++ [HBulk (fo (copy_set ms))]
  | _ => [HBulk (fo t)]
  end.

(* the events of a call before round trip 2's read-back parse (of wdoc t true) *)
Definition rb2_pre (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) (t : jv) : list hev :=
  call_head sm x o1 o2 o0 ++ parse_evs sm x [] ++ scr x ++ rt_text sm t false ++ w_evs t true ++ r_evs t true.

(* the events of a call before round trip 3's read-back parse (of wdoc (copy_set ms) true) *)
Definition rb3_pre (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) (ms : list (list Z * jv)) : list hev :=
  call_head sm x o1 o2 o0 ++ parse_evs sm x [] ++ scr x ++ rt_text sm (JObj ms) false ++ rt_text sm (JObj ms) true ++
  [HBulk (fo (JObj ms))] ++ set_evs ms ++ w_evs (copy_set ms) true.

(* offset j of call_evs x o1 o2 o0 is event k of round trip 2's or round trip 3's read-back parse. The round trips are
   made only when no check_no_overread reading ran out (PresetRun.ranout). *)
Definition rb_call (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) (j : nat) : Prop :=
  Z.of_nat (length x) <= MAXB /\
  (ranout sm x o1 = false /\ ranout sm x o2 = false /\ ranout sm x o0 = false) /\
  exists t, fst (jr_run sm x []) = Some t /\
  ((exists k, (k < length (rd_hevs (ttrace t)))%nat /\ j = (length (rb2_pre sm x o1 o2 o0 t) + k)%nat) \/
   (exists ms k, t = JObj ms /\ (k < length (rd_hevs (ttrace (copy_set ms))))%nat /\
                 j = (length (rb3_pre sm x o1 o2 o0 ms) + k)%nat)).

(* THE READ-BACK POSITIONS: position i of the calls lies in the call after os1, at a read-back offset of it *)
Definition rb_pos (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
  : Prop :=
  exists os1 o1 o2 o0 os2 j, os = os1 ++ (o1, o2, o0) :: os2 /\ i = (length (hruns sm x os1) + j)%nat /\
    rb_call sm x o1 o2 o0 j.

(* when no reading ran out: check_no_overread's events, then the rest *)
Lemma call_evs_head : forall sm x o1 o2 o0, Z.of_nat (length x) <= MAXB ->
  ranout sm x o1 = false /\ ranout sm x o2 = false /\ ranout sm x o0 = false ->
  call_evs sm x o1 o2 o0 = call_head sm x o1 o2 o0 ++ call_rest sm x.
Proof.
  intros sm x o1 o2 o0 Hx (R1 & R2 & R0). rewrite call_evs_blocks, (proj2 (Z.ltb_ge MAXB _) Hx), R1, R2, R0.
  cbv iota. unfold call_head, hd3, hdp, hdf. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma call_cons_head : forall sm x o1 o2 o0, Z.of_nat (length x) <= MAXB ->
  ranout sm x o1 = false /\ ranout sm x o2 = false /\ ranout sm x o0 = false ->
  call_cons sm x o1 o2 o0 =
  flags true (hd3 x) ++ flags false (hdp sm x o1 o2 o0) ++ flags true (hdf sm x o1 o2 o0 ++ call_rest sm x).
Proof.
  intros sm x o1 o2 o0 Hx (R1 & R2 & R0). unfold call_cons. cbv zeta.
  rewrite (proj2 (Z.ltb_ge MAXB _) Hx), R1, R2, R0. cbv iota.
  unfold hd3, hdp, hdf, flags. rewrite !map_app, <- !app_assoc. reflexivity.
Qed.

Lemma call_rest_eq : forall sm x, call_rest sm x = parse_evs sm x [] ++ scr x ++ call_tail sm x.
Proof. reflexivity. Qed.

Lemma tail_shape : forall sm x t, fst (jr_run sm x []) = Some t ->
  call_tail sm x = rt_text sm t false ++ (w_evs t true ++ r_evs t true) ++ parse_evs sm (wdoc t true) [] ++
    (r_free t true ++ w_free t true ++ [HBulk (fo t)]) ++ rt_end sm t ++
    starved_parse sm x (calls (rtr sm [] x)) ++ starved_writes x t ++ [HBulk (pj_frees sm [] x)].
Proof.
  intros sm x t H. unfold call_tail. rewrite H. cbv beta iota.
  unfold round_trip, rt_end, rt_text. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma call_shape2 : forall sm x o1 o2 o0 t, Z.of_nat (length x) <= MAXB ->
  ranout sm x o1 = false /\ ranout sm x o2 = false /\ ranout sm x o0 = false -> fst (jr_run sm x []) = Some t ->
  exists rest, call_evs sm x o1 o2 o0 = rb2_pre sm x o1 o2 o0 t ++ rd_hevs (ttrace t) ++ rest.
Proof.
  intros sm x o1 o2 o0 t Hx Hno Ej. assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); exact Ej).
  exists ((r_free t true ++ w_free t true ++ [HBulk (fo t)]) ++ rt_end sm t ++
          starved_parse sm x (calls (rtr sm [] x)) ++ starved_writes x t ++ [HBulk (pj_frees sm [] x)]).
  rewrite (call_evs_head sm x o1 o2 o0 Hx Hno), call_rest_eq, (tail_shape sm x t Ej), <- (parse_wf sm t true Hw).
  unfold rb2_pre. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma call_shape3 : forall sm x o1 o2 o0 ms, Z.of_nat (length x) <= MAXB ->
  ranout sm x o1 = false /\ ranout sm x o2 = false /\ ranout sm x o0 = false -> fst (jr_run sm x []) = Some (JObj ms) ->
  exists rest, call_evs sm x o1 o2 o0 = rb3_pre sm x o1 o2 o0 ms ++ rd_hevs (ttrace (copy_set ms)) ++ rest.
Proof.
  intros sm x o1 o2 o0 ms Hx Hno Ej. assert (Hw : pj_wf sm (JObj ms)) by (apply (wf_read sm x); exact Ej).
  pose proof (wf_copy sm ms Hw) as Hc.
  exists (w_free (copy_set ms) true ++ [HBulk (fo (copy_set ms))] ++
          [HBulk (fo (copy_set ms))] ++
          starved_parse sm x (calls (rtr sm [] x)) ++ starved_writes x (JObj ms) ++ [HBulk (pj_frees sm [] x)]).
  rewrite (call_evs_head sm x o1 o2 o0 Hx Hno), call_rest_eq, (tail_shape sm x _ Ej),
    <- (parse_wf sm (copy_set ms) true Hc).
  cbn [rt_end]. unfold rw_evs, rb3_pre, rt_text. rewrite <- !app_assoc. reflexivity.
Qed.

(* ---------------------------------------------------------------- the live requests before a read-back *)

Lemma head_nil : forall sm x o1 o2 o0, hlive_from [] (call_head sm x o1 o2 o0) = [].
Proof.
  intros sm x o1 o2 o0. unfold call_head, hd3, hdp, hdf.
  set (CP := Z.of_nat (length x) + FUZZ_PAD).
  destruct (p1_ok sm x o1 o2 o0 [CP; CP; CP]) as [_ Q2].
  destruct (tfrees_ok sm x o1 o2 o0 CP) as [_ T2].
  rewrite hlive_from_app. change (hlive_from [] [HMal CP; HMal CP; HMal CP]) with [CP; CP; CP].
  rewrite hlive_from_app, Q2. exact T2.
Qed.

Lemma head_rest : forall sm x o1 o2 o0 t L, fst (jr_run sm x []) = Some t ->
  hlive_from [] (call_head sm x o1 o2 o0 ++ parse_evs sm x [] ++ scr x ++ L) = hlive_from (rd_blocks (rtr sm [] x)) L.
Proof.
  intros sm x o1 o2 o0 t L Ej. rewrite !hlive_from_app, head_nil.
  rewrite (proj2 (parse_ok sm x [] [])), app_nil_r.
  assert (E : pacc sm x [] = rd_blocks (rtr sm [] x)) by (unfold pacc; rewrite Ej; reflexivity).
  rewrite E. unfold scr. rewrite !hlive_from_cons. cbn [hstep]. rewrite rm1_cons_eq. reflexivity.
Qed.

Lemma rt2_after : forall sm t S1, pj_wf sm t ->
  Permutation (hlive_from S1 (rt_text sm t true ++ [HBulk (fo t)])) S1.
Proof.
  intros sm t S1 Hw. rewrite hlive_from_app, hlive_from_cons, hlive_from_nil.
  destruct (rt_text_ok sm t true S1 Hw) as [_ H].
  refine (proj2 (bulk_ok _ _ S1 _)). apply (Permutation_trans H). apply Permutation_app_tail.
  apply Permutation_sym. apply fo_tblk.
Qed.

Lemma rt12_after : forall sm t A, pj_wf sm t ->
  Permutation (hlive_from A (rt_text sm t false ++ rt_text sm t true ++ [HBulk (fo t)]))
              (tblk t ++ A).
Proof.
  intros sm t A Hw. rewrite hlive_from_app.
  destruct (rt_text_ok sm t false A Hw) as [_ H1].
  exact (Permutation_trans (rt2_after sm t _ Hw) H1).
Qed.

Lemma rt_end_cases : forall sm t, (exists ms, t = JObj ms) \/ rt_end sm t = [HBulk (fo t)].
Proof. intros sm t. destruct t; try (right; reflexivity). left. eexists. reflexivity. Qed.

Lemma rt_end_after : forall sm t A, pj_wf sm t -> Permutation (hlive_from (tblk t ++ A) (rt_end sm t)) A.
Proof.
  intros sm t A Hw. destruct (rt_end_cases sm t) as [(ms & ->) | E].
  - cbn [rt_end].
    destruct (rw_ok sm ms (tblk (JObj ms)) Hw (Permutation_refl _)) as [R1 R2].
    rewrite hlive_from_app, (hlive_from_okf (rw_evs sm ms) (tblk (JObj ms)) A R1).
    rewrite hlive_from_cons, hlive_from_nil.
    assert (HP : Permutation (hlive_from (tblk (JObj ms)) (rw_evs sm ms) ++ A) (fo (copy_set ms) ++ A)).
    { apply Permutation_app_tail. apply (Permutation_trans R2). apply (Permutation_trans (set_tblk ms)).
      apply Permutation_sym. apply fo_tblk. }
    exact (proj2 (bulk_ok _ _ A HP)).
  - rewrite E, hlive_from_cons, hlive_from_nil.
    refine (proj2 (bulk_ok _ _ A _)). apply Permutation_app_tail. apply Permutation_sym. apply fo_tblk.
Qed.

(* at round trip 2's read-back: rendered ()'s buffer, the writer's, the copy (`back` of round trip 1), the doc *)
Lemma pre2_live : forall sm x o1 o2 o0 t, fst (jr_run sm x []) = Some t ->
  Permutation (hlive_from [] (rb2_pre sm x o1 o2 o0 t))
    ((last (rcaps t true) 0 + 0) :: (last (wcaps t true) 0 + HEAD) :: tblk t ++ rd_blocks (rtr sm [] x)).
Proof.
  intros sm x o1 o2 o0 t Ej. assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); exact Ej).
  unfold rb2_pre. rewrite (head_rest sm x o1 o2 o0 t _ Ej), !hlive_from_app.
  destruct (rt_text_ok sm t false (rd_blocks (rtr sm [] x)) Hw) as [_ H1].
  rewrite (proj2 (w_evs_ok t true _)), (proj2 (r_evs_ok t true _)).
  apply perm_skip, perm_skip. exact H1.
Qed.

(* at round trip 3's read-back: the writer's buffer, the copy after pj_string / pj_set, the doc *)
Lemma pre3_cnt : forall sm x o1 o2 o0 ms, fst (jr_run sm x []) = Some (JObj ms) ->
  (cnt is17 (hlive_from [] (rb3_pre sm x o1 o2 o0 ms)) <=
   cnt is17 (tblk (JObj ms)) + cnt is17 (rd_blocks (rtr sm [] x)) + 4)%nat.
Proof.
  intros sm x o1 o2 o0 ms Ej. assert (Hw : pj_wf sm (JObj ms)) by (apply (wf_read sm x); exact Ej).
  unfold rb3_pre. rewrite (head_rest sm x o1 o2 o0 _ _ Ej), !hlive_from_app.
  rewrite (proj2 (w_evs_ok (copy_set ms) true _)), (cnt_cons0 _ _ (wlast_not17 (copy_set ms) true)).
  assert (HS2 : Permutation (hlive_from (hlive_from (hlive_from (rd_blocks (rtr sm [] x)) (rt_text sm (JObj ms) false))
                                         (rt_text sm (JObj ms) true)) [HBulk (fo (JObj ms))])
                            (tblk (JObj ms) ++ rd_blocks (rtr sm [] x))).
  { rewrite <- !hlive_from_app. exact (rt12_after sm (JObj ms) _ Hw). }
  pose proof (cnt_live_leR is17 (hlive_from (hlive_from (hlive_from (rd_blocks (rtr sm [] x))
                (rt_text sm (JObj ms) false)) (rt_text sm (JObj ms) true)) [HBulk (fo (JObj ms))])
                (set_evs ms)) as C.
  pose proof (set_evs_nprodR is17 ms).
  rewrite (cnt_perm _ _ _ HS2), cnt_app in C. lia.
Qed.

(* ================================================================ outside the read-backs: at most two trees *)

Definition is_alloc (e : hev) : bool := match e with HMal _ | HRe _ _ => true | _ => false end.

(* event i of es is an allocation (malloc or realloc) *)
Definition alloc_at (es : list hev) (i : nat) : Prop :=
  match nth_error es i with Some e => is_alloc e = true | None => False end.

(* from the state s, at every allocation j of es with Q j, the live class-17 count is at most B *)
Definition BO (s : list Z) (es : list hev) (Q : nat -> Prop) (B : nat) : Prop :=
  forall j, (j < length es)%nat -> Q j -> alloc_at es j -> (cnt is17 (hlive_from s (firstn j es)) <= B)%nat.

Lemma BO_app : forall s a b Q B, BO s a Q B -> BO (hlive_from s a) b (fun j => Q (length a + j)%nat) B ->
  BO s (a ++ b) Q B.
Proof.
  intros s a b Q B Ha Hb j Hj HQ Hal. rewrite length_app in Hj.
  destruct (Nat.lt_ge_cases j (length a)) as [Hl|Hl].
  - rewrite firstn_app. replace (j - length a)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
    apply Ha; [exact Hl | exact HQ |]. unfold alloc_at in *. rewrite nth_error_app1 in Hal by exact Hl. exact Hal.
  - rewrite firstn_app, firstn_all2 by lia. rewrite hlive_from_app.
    specialize (Hb (j - length a)%nat ltac:(lia)). cbv beta in Hb.
    replace (length a + (j - length a))%nat with j in Hb by lia.
    apply Hb; [exact HQ|]. unfold alloc_at in *. rewrite nth_error_app2 in Hal by exact Hl. exact Hal.
Qed.

Lemma BO_perm : forall s s' es Q B, Permutation s s' -> BO s' es Q B -> BO s es Q B.
Proof.
  intros s s' es Q B Hp H j Hj HQ Ha. rewrite (cnt_perm _ _ _ (hlive_from_perm _ _ _ Hp)). exact (H j Hj HQ Ha).
Qed.

Lemma BO_appS : forall s a b Q B S', Permutation (hlive_from s a) S' -> BO s a Q B ->
  BO S' b (fun j => Q (length a + j)%nat) B -> BO s (a ++ b) Q B.
Proof. intros s a b Q B S' Hp Ha Hb. apply BO_app; [exact Ha|]. exact (BO_perm _ _ _ _ _ Hp Hb). Qed.

Lemma BO_pk0 : forall s es Q B, (pkR is17 [] es + cnt is17 s <= B)%nat -> BO s es Q B.
Proof.
  intros s es Q B H j _ _ _. pose proof (pkR_prefix is17 es s j). pose proof (pkR_base0 is17 es s). lia.
Qed.

Lemma BO_none : forall s es Q B, (forall j, (j < length es)%nat -> ~ Q j) -> BO s es Q B.
Proof. intros s es Q B H j Hj HQ. exfalso. exact (H j Hj HQ). Qed.

Lemma BO_free : forall s es Q B, Forall (fun e => is_alloc e = false) es -> BO s es Q B.
Proof.
  intros s es Q B H j Hj _ Ha. exfalso. unfold alloc_at in Ha.
  destruct (nth_error es j) as [e|] eqn:E; [|exact Ha].
  rewrite Forall_forall in H. rewrite (H e (nth_error_In es j E)) in Ha. discriminate.
Qed.

Lemma BO_impl : forall s es Q Q' B, (forall j, (j < length es)%nat -> Q j -> Q' j) -> BO s es Q' B -> BO s es Q B.
Proof. intros s es Q Q' B HQ H j Hj Hq Ha. exact (H j Hj (HQ j Hj Hq) Ha). Qed.

Lemma nth_flags_app : forall b (es : list hev) L j d, nth (length es + j) (flags b es ++ L) d = nth j L d.
Proof.
  intros b es L j d. assert (E : length (flags b es) = length es) by (unfold flags; apply length_map).
  rewrite app_nth2 by lia. rewrite E. f_equal. lia.
Qed.

Lemma nth_flags_in : forall b (es : list hev) L j d, (j < length es)%nat -> nth j (flags b es ++ L) d = b.
Proof.
  intros b es L j d Hj. assert (E : length (flags b es) = length es) by (unfold flags; apply length_map).
  rewrite app_nth1 by lia. unfold flags. clear E. revert j Hj.
  induction es as [|e es IH]; intros j Hj; [cbn in Hj; lia|].
  destruct j as [|j]; [reflexivity|]. cbn [map nth]. apply IH. cbn [length] in Hj. lia.
Qed.

Lemma p1_free : forall sm x o, Forall (fun e => is_alloc e = false) (p1_tfree sm x o).
Proof. intros sm x o. unfold p1_tfree. destruct (fst (jr_run sm x (okof o))); repeat constructor. Qed.

Lemma hcons_cons : forall sm x o1 o2 o0 os,
  hcons sm x ((o1, o2, o0) :: os) = call_cons sm x o1 o2 o0 ++ hcons sm x os.
Proof. reflexivity. Qed.

(* a call that a reading cut (it ran out): the copies, the readings made (not consumers), then frees only *)
Lemma call_cut : forall sm x o1 o2 o0, Z.of_nat (length x) <= MAXB ->
  ranout sm x o1 = true \/ ranout sm x o2 = true \/ ranout sm x o0 = true ->
  exists G F, call_evs sm x o1 o2 o0 = hd3 x ++ G ++ F /\
    call_cons sm x o1 o2 o0 = flags true (hd3 x) ++ flags false G ++ flags true F /\
    Forall (fun e => is_alloc e = false) F.
Proof.
  intros sm x o1 o2 o0 Hx Hr. unfold call_evs, call_cons. cbv zeta.
  rewrite (proj2 (Z.ltb_ge MAXB _) Hx). cbv iota.
  destruct (ranout sm x o1) eqn:E1; cbv iota.
  { exists (parse_evs sm x (okof o1)),
      [HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD)].
    split; [reflexivity|]. split; [reflexivity|]. repeat constructor. }
  destruct (ranout sm x o2) eqn:E2; cbv iota.
  { exists (parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2)),
      (p1_tfree sm x o1 ++
       [HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD)]).
    split; [unfold hd3; rewrite <- !app_assoc; reflexivity|].
    split; [unfold hd3, flags; rewrite !map_app, <- !app_assoc; reflexivity|].
    apply Forall_app. split; [apply p1_free | repeat constructor]. }
  destruct Hr as [H | [H | H]]; [congruence | congruence|]. rewrite H. cbv iota.
  exists (hdp sm x o1 o2 o0), (hdf sm x o1 o2 o0).
  split; [unfold hd3, hdp, hdf; rewrite app_nil_r, <- !app_assoc; reflexivity|].
  split; [unfold hd3, hdp, hdf, flags; rewrite app_nil_r, !map_app, <- !app_assoc; reflexivity|].
  unfold hdf. apply Forall_app. split; [apply p1_free|]. apply Forall_app. split; [apply p1_free|].
  apply Forall_app. split; [apply p1_free | repeat constructor].
Qed.

Section Sites.

Variable sm : list Z -> Z * Z.
Variable x : list Z.
Variable M17 : nat.
Hypothesis HMx : forall ok, (nprodR is17 (rd_hevs (rtr sm ok x)) <= M17)%nat.
Hypothesis HMt : forall t, fst (jr_run sm x []) = Some t -> (nprodR is17 (rd_hevs (ttrace t)) <= M17)%nat.

(* after check_no_overread when no reading ran out: the main parse, the scratch, the round trips (but their
   read-backs 2 and 3), the starved parse and writes *)
Lemma rest_BO : forall o1 o2 o0, Z.of_nat (length x) <= MAXB ->
  ranout sm x o1 = false /\ ranout sm x o2 = false /\ ranout sm x o0 = false ->
  BO [] (call_rest sm x) (fun j => ~ rb_call sm x o1 o2 o0 (length (call_head sm x o1 o2 o0) + j)%nat) (2 * M17 + 6).
Proof.
  intros o1 o2 o0 Hx Hno. rewrite call_rest_eq.
  assert (HLr : forall ok, (cnt is17 (pacc sm x ok) <= M17)%nat) by (intros ok; exact (cnt_pacc sm is17 x ok M17 HMx)).
  apply BO_app.
  { apply BO_pk0. pose proof (pkR_le is17 (parse_evs sm x []) []) as P. rewrite nprodR_parse in P.
    pose proof (HMx []). rewrite cnt_nil in *. lia. }
  rewrite (proj2 (parse_ok sm x [] [])), app_nil_r.
  apply BO_app.
  { apply BO_pk0. pose proof (pkR_le is17 (scr x) []) as P.
    assert (N : (nprodR is17 (scr x) <= 2)%nat) by exact (nprodR_len is17 (scr x)).
    pose proof (HLr []). rewrite cnt_nil in P. lia. }
  assert (Hsc : hlive_from (pacc sm x []) (scr x) = pacc sm x []).
  { unfold scr. rewrite !hlive_from_cons. cbn [hstep]. rewrite rm1_cons_eq. reflexivity. }
  rewrite Hsc.
  destruct (fst (jr_run sm x [])) as [t|] eqn:Ej.
  2: { unfold call_tail, pacc. rewrite Ej. cbv beta iota. apply BO_pk0.
       pose proof (pkR_starved sm is17 x [] M17 HMx) as P. rewrite cnt_nil in *. lia. }
  assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); exact Ej).
  assert (EL : pacc sm x [] = rd_blocks (rtr sm [] x)) by (unfold pacc; rewrite Ej; reflexivity).
  assert (HcL : (cnt is17 (rd_blocks (rtr sm [] x)) <= M17)%nat) by (rewrite <- EL; apply HLr).
  assert (HMt0 : (nprodR is17 (rd_hevs (ttrace t)) <= M17)%nat) by (apply HMt; first [exact Ej | reflexivity]).
  assert (HcT : (cnt is17 (tblk t) <= M17)%nat) by (pose proof (cnt_tblkR is17 t); lia).
  rewrite EL, (tail_shape sm x t Ej).
  set (Lr := rd_blocks (rtr sm [] x)) in *.
  (* round trip 1 (its read-back included): the doc, the writer, rendered (), the read-back *)
  apply (BO_appS _ _ _ _ _ (tblk t ++ Lr)); [exact (proj2 (rt_text_ok sm t false Lr Hw)) | |].
  { apply BO_pk0. pose proof (pkR_rt_text is17 sm t false [] Hw). rewrite cnt_nil in *. lia. }
  (* round trip 2's writer and rendered (): the doc and the copy *)
  apply BO_app.
  { apply BO_pk0. rewrite cnt_app.
    assert (P : (pkR is17 [] (w_evs t true ++ r_evs t true) <= 2)%nat).
    { rewrite pkR_app, (proj2 (w_evs_ok t true [])).
      pose proof (pkR_w_evs is17 t true []) as P1. pose proof (pkR_r_evs is17 t true [last (wcaps t true) 0 + HEAD]) as P2.
      rewrite cnt_nil in P1. rewrite (cnt_cons0 _ _ (wlast_not17 t true)), cnt_nil in P2. lia. }
    lia. }
  (* round trip 2's read-back: excluded *)
  apply BO_app.
  { apply BO_none. intros j Hj HQ. cbv beta in HQ. apply HQ. unfold rb_call. split; [exact Hx|]. split; [exact Hno|].
    exists t. split; [exact Ej|]. left. exists j. split; [rewrite <- (parse_wf sm t true Hw); exact Hj|].
    unfold rb2_pre. rewrite !length_app. lia. }
  (* free (want), fuzz_free (text), pj_free (&back): the copy and the doc are left *)
  apply (BO_appS _ _ _ _ _ (tblk t ++ Lr)).
  { rewrite <- !hlive_from_app. pose proof (rt2_after sm t (tblk t ++ Lr) Hw) as H2.
    match goal with |- Permutation (hlive_from _ ?L) _ =>
      replace L with (rt_text sm t true ++ [HBulk (fo t)])
        by (unfold rt_text; rewrite <- !app_assoc; reflexivity) end.
    exact H2. }
  { apply BO_free. unfold r_free, w_free. cbn [app]. repeat constructor. }
  (* the rewrite, or pj_free (&copy): the doc is left *)
  apply (BO_appS _ _ _ _ _ Lr); [exact (rt_end_after sm t Lr Hw) | |].
  { destruct (rt_end_cases sm t) as [(ms & ->) | E].
    - cbn [rt_end]. unfold rw_evs. rewrite <- !app_assoc.
      apply BO_app.
      { apply BO_pk0. pose proof (pkR_le is17 (set_evs ms) []) as P. pose proof (set_evs_nprodR is17 ms).
        rewrite cnt_nil in P. rewrite cnt_app. lia. }
      apply BO_app.
      { apply BO_pk0. pose proof (pkR_w_evs is17 (copy_set ms) true []) as P.
        pose proof (cnt_live_leR is17 (tblk (JObj ms) ++ Lr) (set_evs ms)) as C. pose proof (set_evs_nprodR is17 ms).
        rewrite cnt_nil in P. rewrite cnt_app in C. lia. }
      (* round trip 3's read-back: excluded *)
      apply BO_app.
      { apply BO_none. intros j Hj HQ. cbv beta in HQ. apply HQ. unfold rb_call. split; [exact Hx|]. split; [exact Hno|].
        exists (JObj ms). split; [exact Ej|]. right. exists ms, j. split; [reflexivity|].
        split; [rewrite <- (parse_wf sm (copy_set ms) true (wf_copy sm ms Hw)); exact Hj|].
        unfold rb3_pre, rt_text. rewrite !length_app. cbn [length]. lia. }
      apply BO_free. unfold w_free. cbn [app]. repeat constructor.
    - rewrite E. apply BO_free. repeat constructor. }
  (* check_reject_clean_starved's parse and writes; pj_free (&doc) *)
  apply (BO_appS _ _ _ _ _ Lr); [rewrite (proj2 (starved_ok sm x Lr)); apply Permutation_refl | |].
  { apply BO_pk0. pose proof (pkR_starved sm is17 x [] M17 HMx) as P. rewrite cnt_nil in P. lia. }
  apply BO_app.
  { apply BO_pk0. pose proof (pkR_starved_writes is17 x t []) as P. rewrite cnt_nil in P. lia. }
  apply BO_free. repeat constructor.
Qed.

Lemma call_BO : forall o1 o2 o0,
  BO [] (call_evs sm x o1 o2 o0)
     (fun j => nth j (call_cons sm x o1 o2 o0) false = true /\ ~ rb_call sm x o1 o2 o0 j) (2 * M17 + 6).
Proof.
  intros o1 o2 o0. destruct (Z_le_gt_dec (Z.of_nat (length x)) MAXB) as [Hx|Hx].
  2: { intros j Hj. exfalso. unfold call_evs in Hj. cbv zeta in Hj.
       rewrite (proj2 (Z.ltb_lt MAXB (Z.of_nat (length x))) ltac:(lia)) in Hj.
       cbn [length] in Hj. lia. }
  assert (Hcase : (ranout sm x o1 = true \/ ranout sm x o2 = true \/ ranout sm x o0 = true) \/
                  (ranout sm x o1 = false /\ ranout sm x o2 = false /\ ranout sm x o0 = false)).
  { destruct (ranout sm x o1); [left; left; reflexivity|].
    destruct (ranout sm x o2); [left; right; left; reflexivity|].
    destruct (ranout sm x o0); [left; right; right; reflexivity|].
    right. split; [reflexivity|]. split; reflexivity. }
  destruct Hcase as [Hcut | Hno].
  { (* a reading ran out: the three copies, the readings made (not consumers), frees *)
    destruct (call_cut sm x o1 o2 o0 Hx Hcut) as (G & F & Ee & Ec & HF).
    rewrite Ee.
    apply BO_app.
    { apply BO_pk0. pose proof (pkR_le is17 (hd3 x) []) as P.
      assert (N : (nprodR is17 (hd3 x) <= 3)%nat) by exact (nprodR_len is17 (hd3 x)).
      rewrite !cnt_nil in *. lia. }
    apply BO_app.
    { apply BO_none. intros j Hj HQ. cbv beta in HQ. destruct HQ as [Hc _].
      rewrite Ec, nth_flags_app, nth_flags_in in Hc by exact Hj. discriminate. }
    apply BO_free. exact HF. }
  pose proof (call_cons_head sm x o1 o2 o0 Hx Hno) as Ec.
  rewrite (call_evs_head sm x o1 o2 o0 Hx Hno). unfold call_head. rewrite <- !app_assoc.
  (* the three copies *)
  apply BO_app.
  { apply BO_pk0. pose proof (pkR_le is17 (hd3 x) []) as P.
    assert (N : (nprodR is17 (hd3 x) <= 3)%nat) by exact (nprodR_len is17 (hd3 x)).
    rewrite !cnt_nil in *. lia. }
  (* the three readings: not consumers *)
  apply BO_app.
  { apply BO_none. intros j Hj HQ. cbv beta in HQ. destruct HQ as [Hc _].
    rewrite Ec, nth_flags_app, nth_flags_in in Hc by exact Hj. discriminate. }
  (* their frees *)
  apply BO_app.
  { apply BO_free. unfold hdf. apply Forall_app. split; [apply p1_free|]. apply Forall_app. split; [apply p1_free|].
    apply Forall_app. split; [apply p1_free|]. repeat constructor. }
  assert (S0 : hlive_from (hlive_from (hlive_from [] (hd3 x)) (hdp sm x o1 o2 o0)) (hdf sm x o1 o2 o0) = []).
  { rewrite <- !hlive_from_app. exact (head_nil sm x o1 o2 o0). }
  rewrite S0.
  apply (BO_impl _ _ _ (fun j => ~ rb_call sm x o1 o2 o0 (length (call_head sm x o1 o2 o0) + j)%nat)).
  { intros j _ HQ. cbv beta in HQ. destruct HQ as [_ HQ].
    assert (E : (length (call_head sm x o1 o2 o0) + j =
                 length (hd3 x) + (length (hdp sm x o1 o2 o0) + (length (hdf sm x o1 o2 o0) + j)))%nat)
      by (unfold call_head; rewrite !length_app; lia).
    rewrite E. exact HQ. }
  exact (rest_BO o1 o2 o0 Hx Hno).
Qed.

Lemma hruns_BO : forall os,
  BO [] (hruns sm x os) (fun i => nth i (hcons sm x os) false = true /\ ~ rb_pos sm x os i) (2 * M17 + 6).
Proof.
  induction os as [|[[o1 o2] o0] os IH].
  - intros j Hj. cbn in Hj. lia.
  - rewrite hruns_cons. apply BO_app.
    + apply (BO_impl _ _ _ (fun j => nth j (call_cons sm x o1 o2 o0) false = true /\ ~ rb_call sm x o1 o2 o0 j));
        [|apply call_BO].
      intros j Hj [Hc Hr]. split.
      * rewrite hcons_cons, app_nth1 in Hc by (rewrite call_cons_len; exact Hj). exact Hc.
      * intros Hb. apply Hr. exists [], o1, o2, o0, os, j. split; [reflexivity|]. split; [reflexivity | exact Hb].
    + change (hlive_from [] (call_evs sm x o1 o2 o0)) with (hlive (call_evs sm x o1 o2 o0)).
      rewrite (proj2 (call_ok sm x o1 o2 o0)).
      apply (BO_impl _ _ _ (fun i => nth i (hcons sm x os) false = true /\ ~ rb_pos sm x os i)); [|exact IH].
      intros j Hj HQ. cbv beta in HQ. destruct HQ as [Hc Hr]. split.
      * rewrite hcons_cons, app_nth2 in Hc by (rewrite call_cons_len; lia). rewrite call_cons_len in Hc.
        replace (length (call_evs sm x o1 o2 o0) + j - length (call_evs sm x o1 o2 o0))%nat with j in Hc by lia.
        exact Hc.
      * intros (os1 & p1 & p2 & p0 & os2 & k & Eos & Ei & Hk). apply Hr.
        exists ((o1, o2, o0) :: os1), p1, p2, p0, os2, k. split; [rewrite Eos; reflexivity|]. split; [|exact Hk].
        rewrite hruns_cons, length_app. lia.
Qed.

End Sites.

(* OUTSIDE THE READ-BACKS, AT MOST TWO TREES: at every consumer allocation of the k calls that is not in round trip
   2's or round trip 3's read-back parse, the live class-17 count is at most 2 M17 + 6, M17 bounding the class-17
   requests of one reading of x (any grants) and of the trace of x's tree. *)
Theorem live17_two : forall sm x os M17 i,
  (forall ok, (nprodR is17 (rd_hevs (rtr sm ok x)) <= M17)%nat) ->
  (forall t, fst (jr_run sm x []) = Some t -> (nprodR is17 (rd_hevs (ttrace t)) <= M17)%nat) ->
  nth i (hcons sm x os) false = true -> alloc_at (hruns sm x os) i -> ~ rb_pos sm x os i ->
  (cnt is17 (hlive (firstn i (hruns sm x os))) <= 2 * M17 + 6)%nat.
Proof.
  intros sm x os M17 i HMx HMt Hc Ha Hr.
  assert (Hi : (i < length (hruns sm x os))%nat).
  { unfold alloc_at in Ha. destruct (nth_error (hruns sm x os) i) eqn:E; [|contradiction].
    apply nth_error_Some. rewrite E. discriminate. }
  exact (hruns_BO sm x M17 HMx HMt os i Hi (conj Hc Hr) Ha).
Qed.

(* ================================================================ at the read-backs *)

Lemma hruns_app : forall sm x a b, hruns sm x (a ++ b) = hruns sm x a ++ hruns sm x b.
Proof. intros sm x a b. unfold hruns. rewrite map_app, concat_app. reflexivity. Qed.

Lemma hruns_nil_live : forall sm x os, hlive_from [] (hruns sm x os) = [].
Proof.
  intros sm x os. induction os as [|[[o1 o2] o0] os IH]; [reflexivity|].
  rewrite hruns_cons, hlive_from_app. change (hlive_from [] (call_evs sm x o1 o2 o0)) with (hlive (call_evs sm x o1 o2 o0)).
  rewrite (proj2 (call_ok sm x o1 o2 o0)). exact IH.
Qed.

Lemma firstn_app_len : forall (A B : list hev) k, firstn (length A + k) (A ++ B) = A ++ firstn k B.
Proof. intros A B k. rewrite firstn_app, firstn_all2 by lia. f_equal. f_equal. lia. Qed.

Lemma firstn_le_app : forall (A B : list hev) k, (k <= length A)%nat -> firstn k (A ++ B) = firstn k A.
Proof.
  intros A B k H. rewrite firstn_app. replace (k - length A)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  reflexivity.
Qed.

Lemma pos_split : forall sm x os1 o1 o2 o0 os2 P T rest k, call_evs sm x o1 o2 o0 = P ++ T ++ rest ->
  (k <= length T)%nat ->
  firstn (length (hruns sm x os1) + (length P + k)) (hruns sm x (os1 ++ (o1, o2, o0) :: os2)) =
  hruns sm x os1 ++ P ++ firstn k T.
Proof.
  intros sm x os1 o1 o2 o0 os2 P T rest k Ec Hk.
  rewrite hruns_app, hruns_cons, Ec, firstn_app_len, <- !app_assoc, firstn_app_len, firstn_le_app by exact Hk.
  reflexivity.
Qed.

(* AT THE READ-BACKS: the doc tree t and the tree t' read back (t at round trip 2, copy_set ms at round trip 3, t =
   JObj ms), k events into its parse. The free history is pre ++ F ++ X: F the writer chain of the text read back (no
   class-17 request), X rendered ()'s chain (round trip 2) and the read-back parse's frees so far. X has at most
   nc9 t' + nk65 t' + 1 class-17 members, and the live class-17 count plus X's is at most
   2 n17t t + n17t t' + nc9 t' + nk65 t' + 4. *)
Theorem rt_site17 : forall sm x os i, rb_pos sm x os i ->
  exists t t' k pre F X,
    json_read sm x = Some t /\ pj_wf sm t' /\ (k < length (rd_hevs (ttrace t')))%nat /\
    ((t' = t /\ X = hfrees (r_evs t true) ++ hfrees (firstn k (rd_hevs (ttrace t)))) \/
     (exists ms, t = JObj ms /\ t' = copy_set ms /\ X = hfrees (firstn k (rd_hevs (ttrace t'))))) /\
    hfrees (firstn i (hruns sm x os)) = pre ++ F ++ X /\
    F = hfrees (w_evs t' true) /\
    Forall (fun q => is17 q = false) F /\
    (length (filter is17 X) <= nc9 t' + nk65 t' + 1)%nat /\
    (cnt is17 (hlive (firstn i (hruns sm x os))) + length (filter is17 X) <=
       n17t t + n17t t + n17t t' + nc9 t' + nk65 t' + 4)%nat.
Proof.
  intros sm x os i (os1 & o1 & o2 & o0 & os2 & j & Eos & Ei & Hx & Hno & t & Ej & Hrb).
  assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); exact Ej).
  assert (Hr : json_read sm x = Some t) by exact Ej.
  assert (HcL : (cnt is17 (rd_blocks (rtr sm [] x)) <= n17t t)%nat) by exact (blocks17_read sm x t Hr).
  assert (HcT : (cnt is17 (tblk t) <= n17t t)%nat).
  { rewrite <- (cnt_perm _ _ _ (ttrace_blocks t)). exact (blocks17_ttrace sm t Hw). }
  subst os i.
  destruct Hrb as [(k & Hk & ->) | (ms & k & -> & Hk & ->)].
  - (* round trip 2 *)
    destruct (call_shape2 sm x o1 o2 o0 t Hx Hno Ej) as [rest Ec].
    rewrite (pos_split sm x os1 o1 o2 o0 os2 _ _ rest k Ec ltac:(lia)).
    pose proof (cnt_live_frees is17 (firstn k (rd_hevs (ttrace t))) (hlive_from [] (rb2_pre sm x o1 o2 o0 t))
                  (okf_firstn _ _ k (ttrace_okf t _))) as E.
    pose proof (pre2_live sm x o1 o2 o0 t Ej) as HS0.
    pose proof (nprodR_firstn is17 (rd_hevs (ttrace t)) k) as N1.
    pose proof (tt_prod17 sm t Hw) as N2.
    pose proof (cnt_hfrees_firstn is17 (rd_hevs (ttrace t)) k) as N3.
    pose proof (c17_tt t) as N4. rewrite <- cnt17_in17 in N4.
    pose proof (cnt_removelast is17 (rcaps t true)) as N5. pose proof (rcaps17 t true) as N6.
    rewrite (cnt_perm _ _ _ HS0), cnt_cons_eqR, (cnt_cons0 _ _ (wlast_not17 t true)), cnt_app in E.
    assert (HR : ((if is17 ((last (rcaps t true) 0 + 0)%Z) then 1 else 0) <= 1)%nat) by (d17 E0; lia).
    exists t, t, k,
      (hfrees (hruns sm x os1) ++ hfrees (call_head sm x o1 o2 o0 ++ parse_evs sm x [] ++ scr x ++ rt_text sm t false)),
      (hfrees (w_evs t true)), (hfrees (r_evs t true) ++ hfrees (firstn k (rd_hevs (ttrace t)))).
    split; [exact Hr|]. split; [exact Hw|]. split; [exact Hk|]. split; [left; split; reflexivity|].
    split.
    { rewrite !hfrees_app. unfold rb2_pre. rewrite !hfrees_app, <- !app_assoc. reflexivity. }
    split; [reflexivity|]. split; [apply wchain_not17|].
    rewrite cnt_def, cnt_app, hfrees_r_evs.
    split; [lia|].
    unfold hlive. rewrite !hlive_from_app, hruns_nil_live. lia.
  - (* round trip 3 *)
    assert (Hc : pj_wf sm (copy_set ms)) by exact (wf_copy sm ms Hw).
    destruct (call_shape3 sm x o1 o2 o0 ms Hx Hno Ej) as [rest Ec].
    rewrite (pos_split sm x os1 o1 o2 o0 os2 _ _ rest k Ec ltac:(lia)).
    pose proof (cnt_live_frees is17 (firstn k (rd_hevs (ttrace (copy_set ms)))) (hlive_from [] (rb3_pre sm x o1 o2 o0 ms))
                  (okf_firstn _ _ k (ttrace_okf (copy_set ms) _))) as E.
    pose proof (pre3_cnt sm x o1 o2 o0 ms Ej) as HS0.
    pose proof (nprodR_firstn is17 (rd_hevs (ttrace (copy_set ms))) k) as N1.
    pose proof (tt_prod17 sm (copy_set ms) Hc) as N2.
    pose proof (cnt_hfrees_firstn is17 (rd_hevs (ttrace (copy_set ms))) k) as N3.
    pose proof (c17_tt (copy_set ms)) as N4. rewrite <- cnt17_in17 in N4.
    exists (JObj ms), (copy_set ms), k,
      (hfrees (hruns sm x os1) ++ hfrees (call_head sm x o1 o2 o0 ++ parse_evs sm x [] ++ scr x ++
         rt_text sm (JObj ms) false ++ rt_text sm (JObj ms) true ++ [HBulk (fo (JObj ms))] ++
         set_evs ms)),
      (hfrees (w_evs (copy_set ms) true)), (hfrees (firstn k (rd_hevs (ttrace (copy_set ms))))).
    split; [exact Hr|]. split; [exact Hc|]. split; [exact Hk|].
    split; [right; exists ms; split; [reflexivity|]; split; reflexivity|].
    split.
    { rewrite !hfrees_app. unfold rb3_pre. rewrite !hfrees_app, <- !app_assoc. reflexivity. }
    split; [reflexivity|]. split; [apply wchain_not17|].
    rewrite cnt_def.
    split; [lia|].
    unfold hlive. rewrite !hlive_from_app, hruns_nil_live. lia.
Qed.

(* ================================================================ sanity, by computation

   Why the live count needs X's class-17 frees (or nc9) beside the three n17t terms: six nested arrays of 9 items each
   (the first item the next array, 8 empty arrays after it). n17t = 0 (no container with 1 .. 8 items), nc9 = 6. At
   round trip 2's read-back, entering the sixth kids array's malloc (464 bytes, class 17, a consumer allocation), the
   five outer kids arrays of the read-back are live: 5 > n17t t + n17t t' + n17t t' + 4. *)
Fixpoint nest_x (d : nat) : list Z :=
  match d with O => [91; 93] | S d0 => [91] ++ nest_x d0 ++ concat (repeat [44; 91; 93] 8) ++ [93] end.

Fixpoint nest_t (d : nat) : jv :=
  match d with O => JArr [] | S d0 => JArr (nest_t d0 :: repeat (JArr []) 8) end.

Definition nest_pos (sm : list Z -> Z * Z) : nat := (length (rb2_pre sm (nest_x 6) None None None (nest_t 6)) + 5)%nat.

Example sanity_open : forall sm,
  json_read sm (nest_x 6) = Some (nest_t 6) /\ n17t (nest_t 6) = 0%nat /\ nc9 (nest_t 6) = 6%nat /\
  rb_pos sm (nest_x 6) [(None, None, None)] (nest_pos sm) /\
  nth_error (hruns sm (nest_x 6) [(None, None, None)]) (nest_pos sm) = Some (HMal 464) /\
  nth (nest_pos sm) (hcons sm (nest_x 6) [(None, None, None)]) false = true /\
  cnt is17 (hlive (firstn (nest_pos sm) (hruns sm (nest_x 6) [(None, None, None)]))) = 5%nat.
Proof.
  intros sm. assert (Hr : json_read sm (nest_x 6) = Some (nest_t 6)) by (vm_compute; reflexivity).
  split; [exact Hr|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split.
  { exists [], None, None, None, [], (length (rb2_pre sm (nest_x 6) None None None (nest_t 6)) + 5)%nat.
    split; [reflexivity|]. split; [reflexivity|]. unfold rb_call.
    split; [apply Z.leb_le; vm_compute; reflexivity|].
    split; [split; [reflexivity|]; split; reflexivity|].
    exists (nest_t 6). split; [exact Hr|]. left. exists 5%nat.
    split; [apply Nat.ltb_lt; vm_compute; reflexivity | reflexivity]. }
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
Qed.

(* ================================================================ D1's weights pay for n17t, nk65, nc9 and lmax

   Node by node: a container with 1 .. 8 items pays w_c18 >= wa for its c17; one with >= 9 items pays w_c9 >= wc for
   its nc9 term; an object with >= 33 members pays w_k64 >= wa once (kwt), for its k17 (33 .. 64) or its nk65 term
   (>= 65), never both; a string or member name of length >= 72 pays w_str >= wa for its s17, a number of text length
   >= 432 pays w_num >= wa; and every piece of length >= w_lmin pays w_len per byte, so the longest one is paid
   (lwt (max a b) <= lwt a + lwt b, PresetPiece.pc_lwt_max). *)

Definition wnh (W : nweights) (wa wc : Z) : Prop :=
  0 <= wa /\ 0 <= wc /\ wa <= w_c18 W /\ wa <= w_k64 W /\ wa <= w_str W /\ wa <= w_num W /\ wc <= w_c9 W /\
  0 <= w_len W.

Definition gw (wa wc : Z) (u : jv) : Z := wa * Z.of_nat (n17t u + nk65 u) + wc * Z.of_nat (nc9 u).

(* a container's own weight pays its c17 or its nc9 term *)
Lemma wn_cnode : forall W wa wc n, wnh W wa wc ->
  wa * Z.of_nat (c17 n) + wc * Z.of_nat (if Nat.leb 9 n then 1 else 0) <= cwt W n.
Proof.
  intros W wa wc n (Ha & Hc & H18 & Hk & Hs & Hn & H9 & Hl). unfold c17, cwt.
  destruct (Nat.eqb_spec n 0) as [->|N0]; [cbn; lia|].
  destruct (Nat.leb_spec n 8); destruct (Nat.leb_spec 1 n); destruct (Nat.leb_spec 9 n); try lia;
    cbn [andb]; lia.
Qed.

(* an object's kwt pays its k17 or its nk65 term *)
Lemma wn_knode : forall W wa wc n, wnh W wa wc ->
  wa * Z.of_nat (k17 n) + wa * Z.of_nat (if Nat.leb 65 n then 1 else 0) <= kwt W n.
Proof.
  intros W wa wc n (Ha & Hc & H18 & Hk & Hs & Hn & H9 & Hl). unfold k17, kwt.
  destruct (Nat.leb_spec 33 n); destruct (Nat.leb_spec n 64); destruct (Nat.leb_spec 65 n); try lia;
    cbn [andb]; lia.
Qed.

(* a string or member name pays its s17 and its piece *)
Lemma wn_name : forall W wa wc (k : list Z), wnh W wa wc -> wa * Z.of_nat (s17 k) + lwt W (length k) <= swt W (length k).
Proof.
  intros W wa wc k (Ha & Hc & H18 & Hk & Hs & Hn & H9 & Hl). unfold s17, swt, lwt.
  destruct (Nat.leb 72 (length k)); destruct (Nat.leb (w_lmin W) (length k)); cbv beta iota; lia.
Qed.

Lemma wn_arr : forall W wa wc items, wnh W wa wc ->
  Forall (fun u => gw wa wc u + lwt W (lmax u) <= wsum W u) items ->
  wa * Z.of_nat (list_sum (map n17t items) + list_sum (map nk65 items)) + wc * Z.of_nat (list_sum (map nc9 items)) +
  lwt W (list_max (map lmax items)) <= fold_right Z.add 0 (map (wsum W) items).
Proof.
  intros W wa wc items Hw H. pose proof Hw as (Ha & Hc & H18 & Hk & Hs & Hn & H9 & Hl).
  induction H as [|u l Hu _ IH].
  - pose proof (pc_lwt0 W) as L0. cbn. lia.
  - rewrite pc_lmax_cons, pc_fr_cons, !map_cons, !lsum_cons.
    pose proof (pc_lwt_max W (lmax u) (list_max (map lmax l)) Hl) as M. unfold gw in Hu.
    rewrite !Nat2Z.inj_add in *. nia.
Qed.

Lemma wn_obj : forall W wa wc ms, wnh W wa wc ->
  Forall (fun m => gw wa wc (snd m) + lwt W (lmax (snd m)) <= wsum W (snd m)) ms ->
  wa * Z.of_nat (list_sum (map (fun '(k, u) => (s17 k + n17t u)%nat) ms) + list_sum (map (fun '(_, u) => nk65 u) ms)) +
  wc * Z.of_nat (list_sum (map (fun '(_, u) => nc9 u) ms)) +
  lwt W (list_max (map (fun '(k, u) => Nat.max (length k) (lmax u)) ms)) <=
  fold_right Z.add 0 (map (fun m => swt W (length (fst m)) + wsum W (snd m)) ms).
Proof.
  intros W wa wc ms Hw H. pose proof Hw as (Ha & Hc & H18 & Hk & Hs & Hn & H9 & Hl).
  induction H as [|[k u] l Hu _ IH].
  - pose proof (pc_lwt0 W) as L0. cbn. lia.
  - rewrite pc_lmax_cons, pc_fr_cons, !map_cons, !lsum_cons. cbv beta iota. cbn [fst snd] in Hu |- *.
    match goal with |- context [lwt W (Nat.max (Nat.max (length k) (lmax u)) ?R)] =>
      pose proof (pc_lwt_max W (Nat.max (length k) (lmax u)) R Hl) as M1 end.
    pose proof (pc_lwt_max W (length k) (lmax u) Hl) as M2.
    pose proof (wn_name W wa wc k Hw) as Nm. unfold gw in Hu.
    rewrite !Nat2Z.inj_add in *. nia.
Qed.

Lemma wn_all : forall W wa wc u, wnh W wa wc -> gw wa wc u + lwt W (lmax u) <= wsum W u.
Proof.
  intros W wa wc u Hw. pose proof Hw as (Ha & Hc & H18 & Hk & Hs & Hn & H9 & Hl).
  induction u as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  1-3: unfold gw; cbn [n17t nk65 nc9 wsum lmax]; rewrite pc_lwt0; lia.
  - unfold gw. cbn [n17t nk65 nc9 wsum lmax]. unfold nwt, lwt.
    destruct (Nat.leb 432 (length txt)); destruct (Nat.leb (w_lmin W) (length txt)); cbv beta iota; lia.
  - unfold gw. cbn [n17t nk65 nc9 wsum lmax]. pose proof (wn_name W wa wc s Hw). lia.
  - unfold gw. cbn [n17t nk65 nc9 wsum lmax].
    pose proof (wn_arr W wa wc items Hw IH) as L. pose proof (wn_cnode W wa wc (length items) Hw) as C.
    rewrite !Nat2Z.inj_add in *. nia.
  - unfold gw. cbn [n17t nk65 nc9 wsum lmax].
    pose proof (wn_obj W wa wc ms Hw IH) as L. pose proof (wn_cnode W wa wc (length ms) Hw) as C.
    pose proof (wn_knode W wa wc (length ms) Hw) as K.
    rewrite !Nat2Z.inj_add in *. nia.
Qed.

(* D1'S WEIGHTS PAY FOR THE CLASS-17 NODES: with wa at most each of w_c18, w_k64, w_str, w_num and wc at most w_c9,
   a tree's weight is at least wa (n17t + nk65) + wc nc9, plus w_len per byte of its longest piece when that piece
   reaches w_lmin. *)
Theorem wsum_n17 : forall (W : nweights) (wa wc : Z), 0 <= wa -> 0 <= wc -> wa <= w_c18 W -> wa <= w_k64 W -> wa <= w_str W -> wa <= w_num W -> wc <= w_c9 W -> 0 <= w_len W ->
  forall u, wa * Z.of_nat (n17t u + nk65 u) + wc * Z.of_nat (nc9 u) + (if Nat.leb (w_lmin W) (lmax u) then w_len W * Z.of_nat (lmax u) else 0) <= wsum W u.
Proof.
  intros W wa wc Ha Hc H18 Hk Hs Hn H9 Hl u.
  pose proof (wn_all W wa wc u (conj Ha (conj Hc (conj H18 (conj Hk (conj Hs (conj Hn (conj H9 Hl)))))))) as H.
  unfold gw, lwt in H. exact H.
Qed.
