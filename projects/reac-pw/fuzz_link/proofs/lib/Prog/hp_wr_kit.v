(* reac-pw/fuzz_link, PLAIN build: the kit the two `struct nl_w` writer walks share,
   lib/Prog/nl_error.v (contract lib/Prog/nl_error_c.v) and lib/Prog/attr_text.v
   (contract lib/Prog/attr_text_c.v).

   Both functions only append to the reply the harness is building, and neither contract says
   WHICH bytes they append: it is enough that the 4096 payload bytes stay readable and writable,
   that w->n stays in [0, 4096] and never falls, and that w->full stays a flag.

   So the walks do NOT carry the payload as a byte list. They carry it as `stk rsegs m w
   (w + NW_SIZE)`: every byte of the structure holds a value and is writable. That is what both
   functions need of w->b (a `sb` into it needs `store_ok`, a memcpy into it needs `rw_cells`),
   it is what `nlw_at` asks for at the `ret`, and `stk` is the one shape the walk tactics carry
   through a store with no disjointness side condition (lib/Lib/Frame.v `stk_write`), which a
   store at a register-held offset into w->b cannot give. `stk_of_nlw` makes it at the entry and
   `nlw_from` turns it back into `nlw_at` at the `ret`, reading the two field values out of the
   two cells the walk does track (`wst` below).

   Nothing here is specific to one of the two functions: both get the same stores (a byte at a
   time into w->b, `sd` of the new length, `sw` of the full flag), the same memcpy into w->b and
   the same memset of the NL_ALIGN padding. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Lists
   ========================================================================== *)

Lemma skipn_nil_any : forall {X} (n : nat), skipn n (@nil X) = [].
Proof. intros X [|n]; reflexivity. Qed.

Lemma skipn_skipn_add : forall {X} (b a : nat) (l : list X), skipn a (skipn b l) = skipn (a + b) l.
Proof.
  intros X b. induction b as [|b IH]; intros a l.
  - rewrite Nat.add_0_r. reflexivity.
  - destruct l as [|x l]; cbn [skipn].
    + rewrite !skipn_nil_any. reflexivity.
    + rewrite IH. replace (a + S b)%nat with (S (a + b))%nat by lia. reflexivity.
Qed.

Lemma nth_error_skipn_add : forall {X} (n : nat) (l : list X) i,
  nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros X n. induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|x l]; cbn [skipn]; [rewrite nth_error_nil; destruct (n + i)%nat; reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma nth_error_firstn_lt : forall {X} (l : list X) n i,
  (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X l. induction l as [|x l IH]; intros n i Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn].
    destruct i as [|i]; [reflexivity|]. cbn [nth_error]. apply IH. lia.
Qed.

Lemma list_ext_nth : forall {X} (l1 l2 : list X), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros X l1. induction l1 as [|x l1 IH]; intros l2 H.
  - destruct l2 as [|y l2]; [reflexivity|]. specialize (H 0%nat). discriminate.
  - destruct l2 as [|y l2]; [specialize (H 0%nat); discriminate|].
    pose proof (H 0%nat) as H0. cbn in H0. injection H0 as H0. subst y.
    rewrite (IH l2 (fun i => H (S i))). reflexivity.
Qed.

(* the little-endian value of the eight bytes an `sd` leaves *)
Lemma bytes_le_to_Z_le8 : forall v : word, bytes_le_to_Z (le8 v) = bv_unsigned v.
Proof.
  intros v. unfold le8, word_to_le_bytes.
  rewrite bytes_le_to_Z_to_le_bytes by apply bv_unsigned_in_range.
  change (8 * Z.of_nat 8)%Z with 64%Z.
  pose proof (bv_unsigned_in_range 64 v) as Hr. unfold bv_modulus in Hr.
  apply Z.mod_small. lia.
Qed.

(* The two field readers, as the walks see them. `nw_n` and `nw_full` are `rdn` of a `slice`,
   and `rdn` is also a name of the semantics (lib/Lib/Mem.v), so these two steps go by
   conversion and never by `unfold rdn`, which would reach the other constant. *)
Lemma nw_n_val : forall bs, nw_n bs = bytes_le_to_Z (firstn (Z.to_nat 8) (skipn (Z.to_nat 4096) bs)).
Proof. reflexivity. Qed.
Lemma nw_full_val : forall bs, nw_full bs = bytes_le_to_Z (firstn (Z.to_nat 4) (skipn (Z.to_nat 4104) bs)).
Proof. reflexivity. Qed.

(* a window of a byte list that another `bytes_at` pins down: both read the same memory *)
Lemma slice_of_bytes_at : forall m A bs (i : Z) xs,
  bytes_at rsegs m A bs -> bytes_at rsegs m (A + i) xs -> 0 <= i ->
  (Z.to_nat i + length xs <= length bs)%nat ->
  firstn (length xs) (skipn (Z.to_nat i) bs) = xs.
Proof.
  intros m A bs i xs HB HX Hi Hk.
  pose proof HB as (_ & _ & NB). pose proof HX as (_ & _ & NX).
  apply list_ext_nth. intros j.
  destruct (Nat.lt_ge_cases j (length xs)) as [Hj|Hj].
  - rewrite nth_error_firstn_lt by lia. rewrite nth_error_skipn_add.
    rewrite <- (NB (Z.to_nat i + j)%nat) by lia. rewrite <- (NX j) by lia.
    replace (A + i + Z.of_nat j) with (A + Z.of_nat (Z.to_nat i + j)%nat) by lia. reflexivity.
  - rewrite (proj2 (nth_error_None _ j)) by (rewrite firstn_length, skipn_length; lia).
    rewrite (proj2 (nth_error_None xs j)) by lia. reflexivity.
Qed.

(* ==========================================================================
   2. `stk` windows: what a store, a callee and `nlw_at` need of them
   ========================================================================== *)

Lemma stk_sub : forall m lo hi a b, stk rsegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk rsegs m a b.
Proof.
  intros m lo hi a b H Ha Hab Hb.
  destruct (stk_split rsegs m lo a hi H ltac:(lia)) as [_ H1].
  destruct (stk_split rsegs m a b hi H1 ltac:(lia)) as [H2 _]. exact H2.
Qed.

Lemma wr_at_of_stk : forall m lo hi a k,
  stk rsegs m lo hi -> lo <= a -> 0 <= k -> a + k <= hi -> wr_at rsegs m a k.
Proof.
  intros m lo hi a k (H1 & H2 & H) Ha Hk Hak.
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma cells_of_stk : forall m lo hi a (k : nat),
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat k <= hi ->
  exists junk, length junk = k /\ rw_cells rsegs m a [CB k junk].
Proof.
  intros m lo hi a k ST Ha Hk.
  pose proof (stk_sub m lo hi a (a + Z.of_nat k) ST Ha ltac:(lia) ltac:(lia)) as ST2.
  destruct (stk_bytes rsegs m a (a + Z.of_nat k) ST2 ltac:(lia)) as (bs & Hlen & Hb).
  replace (Z.to_nat (a + Z.of_nat k - a)) with k in Hlen by lia.
  exists bs. split; [exact Hlen|]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hlen | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    eapply wr_at_of_stk; [exact ST | lia | lia | lia].
Qed.

Lemma stk_of_nlw : forall m w bs, nlw_at m w bs -> stk rsegs m w (w + NW_SIZE).
Proof.
  intros m w bs [HU HL].
  pose proof (stk_of_rw_cells rsegs m w _ (rw_cells_of_u8arr rsegs m w bs HU)) as ST.
  cbn [cells_size csize] in ST. rewrite Nat.add_0_r in ST.
  replace (w + NW_SIZE) with (w + Z.of_nat (length bs)) by lia. exact ST.
Qed.

(* the value an `ld` of a byte-list cell leaves in its register *)
Lemma ld_cb : forall bs : list byte, length bs = 8%nat ->
  bv_extract 0 64 (le_bytes_to_word bs) = Z_to_bv 64 (bytes_le_to_Z bs).
Proof.
  intros bs H. apply bv_eq. rewrite load8_le_val by exact H.
  rewrite Z_to_bv_unsigned, bytes_le_to_Z_le_val. symmetry. apply bv_wrap_small.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr.
  rewrite length_map, H in Hr. change (256 ^ Z.of_nat 8) with (2^64) in Hr.
  change (bv_modulus 64) with (2^64). lia.
Qed.

(* a store leaves a C8 or C4 cell where the walk carries a CB cell: same bytes, same size *)
Lemma rw_cells_same_bytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] W E S. split; [split; [exact W|]|].
  - rewrite E. exact Hb.
  - rewrite S. exact Hw.
Qed.

(* w->n after an `sd`, and w->full after a `sw`: the cell the store leaves, back in the
   byte-list shape the walk carries, with its new value *)
Lemma cells_sd : forall m A v tf pad,
  rw_cells rsegs m A [C8 v; CB 4 tf; CB 4 pad] -> length tf = 4%nat -> length pad = 4%nat ->
  rw_cells rsegs m A [CB 8 (le8 v); CB 4 tf; CB 4 pad] /\ bytes_le_to_Z (le8 v) = bv_unsigned v.
Proof.
  intros m A v tf pad H L1 L2. split; [|apply bytes_le_to_Z_le8].
  eapply rw_cells_same_bytes; [exact H | cbn [cells_wf cell_wf] | reflexivity | reflexivity].
  split; [apply length_le8|]. split; [exact L1|]. split; [exact L2 | exact I].
Qed.

Lemma cells_sw : forall m A tn v pad,
  rw_cells rsegs m A [CB 8 tn; C4 v; CB 4 pad] -> length tn = 8%nat -> length pad = 4%nat ->
  rw_cells rsegs m A [CB 8 tn; CB 4 (le4 v); CB 4 pad] /\
  bytes_le_to_Z (le4 v) = bv_unsigned v mod 2 ^ 32.
Proof.
  intros m A tn v pad H L1 L2. split; [|apply bytes_le_to_Z_le4].
  eapply rw_cells_same_bytes; [exact H | cbn [cells_wf cell_wf] | reflexivity | reflexivity].
  split; [exact L1|]. split; [apply length_le4|]. split; [exact L2 | exact I].
Qed.

(* the two field cells after any mix of `sd`/`sw` stores, back in the byte-list shape *)
Lemma cells_nw : forall m A c0 c1 pad,
  rw_cells rsegs m A [c0; c1; CB 4 pad] ->
  csize c0 = 8%nat -> csize c1 = 4%nat -> cell_wf c0 -> cell_wf c1 -> length pad = 4%nat ->
  rw_cells rsegs m A [CB 8 (cbytes c0); CB 4 (cbytes c1); CB 4 pad].
Proof.
  intros m A c0 c1 pad H S0 S1 W0 W1 Lp.
  eapply rw_cells_same_bytes; [exact H | cbn [cells_wf cell_wf] | reflexivity |].
  - rewrite (cbytes_length c0 W0), (cbytes_length c1 W1).
    split; [exact S0|]. split; [exact S1|]. split; [exact Lp | exact I].
  - cbn [cells_size csize]. lia.
Qed.

(* a `sb`, `sh`, `sw` or `sd` into w->b at an offset the registers hold *)
Lemma nw_store_ok : forall m w n (k : nat),
  stk rsegs m w (w + NW_SIZE) -> 0 <= n -> n + Z.of_nat k <= NW_SIZE ->
  store_ok rsegs m (wa (w + n)) k = true.
Proof.
  intros m w n k SW Hn Hk.
  eapply wr_at_store_ok with (a := w) (n := NW_SIZE); [|lia|lia].
  eapply wr_at_of_stk; [exact SW | lia | unfold NW_SIZE; lia | lia].
Qed.

Lemma wr_at_sub : forall m A n i k,
  wr_at rsegs m A n -> 0 <= i -> 0 <= k -> i + k <= n -> wr_at rsegs m (A + i) k.
Proof.
  intros m A n i k (A1 & B1 & C1) Hi Hk Hik.
  split; [lia|]. split; [lia|]. intros j Hj.
  replace (A + i + j) with (A + (i + j)) by lia. apply C1. lia.
Qed.

Lemma cells3 : forall m A tn tf pad,
  bytes_at rsegs m A (tn ++ (tf ++ pad)) -> wr_at rsegs m A 16 ->
  length tn = 8%nat -> length tf = 4%nat -> length pad = 4%nat ->
  rw_cells rsegs m A [CB 8 tn; CB 4 tf; CB 4 pad].
Proof.
  intros m A tn tf pad HB HW L1 L2 L3. split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. exact HW.
Qed.

(* the entry: w->n and w->full as the two cells the walk reads and writes *)
Lemma nlw_cells : forall m w bs, nlw_at m w bs ->
  exists tn tf pad, rw_cells rsegs m (w + 4096) [CB 8 tn; CB 4 tf; CB 4 pad] /\
    bytes_le_to_Z tn = nw_n bs /\ bytes_le_to_Z tf = nw_full bs.
Proof.
  intros m w bs [[Hb Hw] HL]. unfold NW_SIZE in HL.
  assert (Ern : skipn (Z.to_nat 8) (skipn (Z.to_nat 4096) bs) = skipn (Z.to_nat 4104) bs)
    by (rewrite skipn_skipn_add; f_equal; lia).
  assert (Epd : skipn (Z.to_nat 4) (skipn (Z.to_nat 4104) bs) = skipn (Z.to_nat 4108) bs)
    by (rewrite skipn_skipn_add; f_equal; lia).
  assert (E2 : skipn (Z.to_nat 4096) bs =
               firstn (Z.to_nat 8) (skipn (Z.to_nat 4096) bs) ++
               (firstn (Z.to_nat 4) (skipn (Z.to_nat 4104) bs) ++ skipn (Z.to_nat 4108) bs))
    by (rewrite <- Epd, firstn_skipn, <- Ern, firstn_skipn; reflexivity).
  assert (Hb2 : bytes_at rsegs m w (firstn (Z.to_nat 4096) bs ++ skipn (Z.to_nat 4096) bs))
    by (rewrite firstn_skipn; exact Hb).
  apply (proj1 (bytes_at_app rsegs m w _ _)) in Hb2. destruct Hb2 as [_ Htail].
  rewrite firstn_length in Htail.
  replace (Z.of_nat (Nat.min (Z.to_nat 4096) (length bs))) with 4096 in Htail by lia.
  rewrite E2 in Htail.
  exists (firstn (Z.to_nat 8) (skipn (Z.to_nat 4096) bs)),
         (firstn (Z.to_nat 4) (skipn (Z.to_nat 4104) bs)), (skipn (Z.to_nat 4108) bs).
  split; [|split; [symmetry; apply nw_n_val | symmetry; apply nw_full_val]].
  apply cells3.
  - exact Htail.
  - eapply wr_at_sub with (n := Z.of_nat (length bs)); [exact Hw | lia | lia | lia].
  - rewrite firstn_length, skipn_length. lia.
  - rewrite firstn_length, skipn_length. lia.
  - rewrite skipn_length. lia.
Qed.

(* `stk` across a callee: a byte of the window is either untouched or one the callee left *)
Lemma stk_transport_mrd : forall W m m' lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ (exists b, mrd rsegs m' (wa x) = Some b)) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Hc a Ha) as [Ho | (b' & Hb')]; [|exists b'; exact Hb'].
  exists b. unfold mrd in *. rewrite (MU (wa a)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
Qed.

Lemma cells_mrd : forall m A cs i,
  rw_cells rsegs m A cs -> (i < cells_size cs)%nat ->
  exists b, mrd rsegs m (wa (A + Z.of_nat i)) = Some b.
Proof.
  intros m A cs i [[Hwf Hb] _] Hi. pose proof Hb as (_ & _ & Hnth).
  rewrite cells_bytes_length in Hnth by exact Hwf.
  rewrite (Hnth i Hi).
  destruct (nth_error (cells_bytes cs) i) as [b|] eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. rewrite cells_bytes_length in E by exact Hwf. lia.
Qed.

(* the window a callee wrote, as the `stk` side condition wants it *)
Lemma stk_cover_cells : forall m' A cs x,
  rw_cells rsegs m' A cs -> A <= x < A + Z.of_nat (cells_size cs) ->
  exists b, mrd rsegs m' (wa x) = Some b.
Proof.
  intros m' A cs x HC Hx.
  replace x with (A + Z.of_nat (Z.to_nat (x - A))) by lia.
  eapply cells_mrd; [exact HC | lia].
Qed.

(* ==========================================================================
   3. The writer's state through a walk
   ========================================================================== *)

Definition wst (m0 m : word -> option byte) (w lo sp0 K n f : Z) (fr : list cell) : Prop :=
  stk rsegs m w (w + NW_SIZE) /\
  (exists tn tf pad, rw_cells rsegs m (w + NW_N) [CB 8 tn; CB 4 tf; CB 4 pad] /\
     bytes_le_to_Z tn = n /\ bytes_le_to_Z tf = f) /\
  munch [(sp0 - K, sp0); (w, w + NW_SIZE)] m0 m /\ wmono rsegs m0 m /\
  mem_inv rsegs m /\ stk rsegs m lo (sp0 - K) /\ rw_cells rsegs m (sp0 - K) fr.

Lemma nlw_bound : forall m w bs, nlw_at m w bs -> 0 <= w /\ w + NW_SIZE <= 2^64.
Proof.
  intros m w bs [[Hb _] Hl]. pose proof (bytes_at_bound rsegs m w bs Hb) as [P1 P2].
  unfold NW_SIZE in *. lia.
Qed.

Lemma nlw_at_unique : forall m w bs1 bs2, nlw_at m w bs1 -> nlw_at m w bs2 -> bs1 = bs2.
Proof.
  intros m w bs1 bs2 [[B1 _] L1] [[B2 _] L2].
  pose proof B1 as (_ & _ & N1). pose proof B2 as (_ & _ & N2).
  apply list_ext_nth. intros i.
  destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
  - rewrite <- (N1 i) by lia. rewrite <- (N2 i) by lia. reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i)) by lia.
    rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.

(* the `ret`: the structure is a reply writer again, with the two field values the walk tracked *)
Lemma nlw_from : forall m w n f tn tf pad,
  stk rsegs m w (w + NW_SIZE) ->
  rw_cells rsegs m (w + NW_N) [CB 8 tn; CB 4 tf; CB 4 pad] ->
  bytes_le_to_Z tn = n -> bytes_le_to_Z tf = f ->
  exists bs, nlw_at m w bs /\ nw_n bs = n /\ nw_full bs = f.
Proof.
  intros m w n f tn tf pad SW HC Hn Hf.
  pose proof HC as [[Hwf HCb] _]. cbn [cells_wf cell_wf] in Hwf.
  destruct Hwf as (Ltn & Ltf & Lpad & _).
  cbn [cells_bytes cbytes] in HCb. rewrite app_nil_r in HCb.
  destruct (stk_bytes rsegs m w (w + NW_SIZE) SW ltac:(unfold NW_SIZE; lia)) as (bs & Hlen & Hb).
  replace (Z.to_nat (w + NW_SIZE - w)) with (Z.to_nat NW_SIZE) in Hlen by lia.
  assert (HL : Z.of_nat (length bs) = NW_SIZE) by (rewrite Hlen; unfold NW_SIZE; reflexivity).
  (* the length word and the flag word, as windows of bs *)
  apply (proj1 (bytes_at_app rsegs m (w + NW_N) tn (tf ++ pad))) in HCb.
  destruct HCb as [Btn Brest].
  apply (proj1 (bytes_at_app rsegs m (w + NW_N + Z.of_nat (length tn)) tf pad)) in Brest.
  destruct Brest as [Btf _].
  assert (En : firstn (Z.to_nat 8) (skipn (Z.to_nat 4096) bs) = tn).
  { replace (Z.to_nat 8) with (length tn) by lia.
    eapply (slice_of_bytes_at m w bs 4096 tn Hb);
      [ replace (w + 4096) with (w + NW_N) by (unfold NW_N; lia); exact Btn | lia
      | unfold NW_SIZE in HL; lia ]. }
  assert (Ef : firstn (Z.to_nat 4) (skipn (Z.to_nat 4104) bs) = tf).
  { replace (Z.to_nat 4) with (length tf) by lia.
    eapply (slice_of_bytes_at m w bs 4104 tf Hb);
      [ replace (w + 4104) with (w + NW_N + Z.of_nat (length tn)) by (unfold NW_N; lia); exact Btf
      | lia | unfold NW_SIZE in HL; lia ]. }
  exists bs. split; [split|].
  - split; [exact Hb|]. rewrite HL.
    eapply wr_at_of_stk; [exact SW | lia | unfold NW_SIZE; lia | lia].
  - exact HL.
  - split; [rewrite nw_n_val, En; exact Hn | rewrite nw_full_val, Ef; exact Hf].
Qed.

(* what the Post of both contracts asks for *)
Lemma wst_post : forall m0 m w lo sp0 K n f fr bs,
  wst m0 m w lo sp0 K n f fr -> 0 <= n <= NL_CHUNK_MAX -> 0 <= f <= 1 ->
  nlw_at m0 w bs -> nw_n bs <= n ->
  exists bs', nlw_at m w bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs'.
Proof.
  intros m0 m w lo sp0 K n f fr bs (SW & (tn & tf & pad & HC & Hn & Hf) & _) Hnr Hfr HB Hle.
  destruct (nlw_from m w n f tn tf pad SW HC Hn Hf) as (bs' & HW & En & Ef).
  exists bs'. split; [exact HW|]. split; [split; rewrite ?En, ?Ef; lia | lia].
Qed.
