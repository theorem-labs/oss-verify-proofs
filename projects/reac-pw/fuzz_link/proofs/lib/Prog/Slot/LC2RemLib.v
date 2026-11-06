(* Arm c2 (op_mark), piece REMEMBER (LC2Rem.v): the facts the walk 0x140d4 -> 0x13da4 uses.
   1. words and branch conditions; 2. lists, slices and upd_bytes; 3. md lies outside the image;
   4. what a write in the stack window or in md keeps (c2m_W); 5. the model block after the store of
   n + 1 at MD_N_MARK and the write of the name in slot n; 6. the slots strcmp reads. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
Local Open Scope Z_scope.

Ltac c2m_lia :=
  unfold MD_N_MARK, MD_MARK, MARK_LEN, MD_SIZE, MD_N_REQ, MD_REQ, MD_REQ_LEN, NL_SENT_LEN, NL_SENT_MAX,
         MD_NEXT, MD_SOCKET_ERRNO, MD_SEND_ERRNO, MARKS_MAX, SLOT_FRAME, SLOT_STACK_Z in *; lia.

(* ==========================================================================
   1. Words and branch conditions
   ========================================================================== *)

Lemma c2m_signed : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit by lia.
  destruct (Z.ltb_spec z (2^63)) as [H|H]; [reflexivity | lia].
Qed.

(* lw: the sign extension of a 32-bit field that holds 0 <= v < 2^31 *)
Lemma c2m_lw_val : forall B, 0 <= bytes_le_to_Z B < 2^31 ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word B)) = Z_to_bv 64 (bytes_le_to_Z B).
Proof.
  intros B HB. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

Lemma c2m_shl4 : forall n, 0 <= n < 2^59 -> Z.shiftl (bv_unsigned (Z_to_bv 64 n)) 4 = 16 * n.
Proof.
  intros n Hn. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. lia.
Qed.

(* decide the branch at the head of the goal to b, from the arithmetic facts in context *)
Ltac c2m_cond :=
  unfold bv_eqb, bv_lts, bv_ltu; rewrite ?unsigned_lit by lia; rewrite ?c2m_signed by lia; solve_cond_rec.
Ltac c2m_br b :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with b; [cbv iota | symmetry; c2m_cond] end.

(* ==========================================================================
   2. Lists, slices, upd_bytes
   ========================================================================== *)

Lemma c2m_nth_firstn : forall {A} (l : list A) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros A l. induction l as [|x l IH]; intros n i H.
  - destruct n, i; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma c2m_nth_skipn : forall {A} (l : list A) k i, nth_error (skipn k l) i = nth_error l (k + i).
Proof.
  intros A l. induction l as [|x l IH]; intros k i.
  - destruct k, i; reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn. apply IH.
Qed.

Lemma c2m_ext : forall {A} (l1 l2 : list A), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros [|b l2] H.
  - reflexivity.
  - specialize (H O). cbn in H. discriminate H.
  - specialize (H O). cbn in H. discriminate H.
  - pose proof (H O) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

Lemma c2m_firstn_S : forall {A} (l : list A) p d, (p < length l)%nat -> firstn (S p) l = firstn p l ++ [nth p l d].
Proof.
  intros A l. induction l as [|x l IH]; intros p d H; cbn [length] in H; [lia|].
  destruct p as [|p]; [reflexivity|]. cbn [firstn nth]. rewrite (IH p d) by lia. reflexivity.
Qed.

Lemma c2m_bytes_sub : forall m c cs k len, bytes_at rsegs m c cs -> (k + len <= length cs)%nat ->
  bytes_at rsegs m (c + Z.of_nat k) (firstn len (skipn k cs)).
Proof.
  intros m c cs k len (H0 & H1 & H) Hk.
  assert (L : length (firstn len (skipn k cs)) = len) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite L; lia|].
  intros i Hi. rewrite L in Hi. rewrite c2m_nth_firstn by exact Hi. rewrite c2m_nth_skipn.
  replace (c + Z.of_nat k + Z.of_nat i) with (c + Z.of_nat (k + i)) by lia. apply H. lia.
Qed.

Lemma c2m_rw_sub : forall m c cs k len, u8arr rsegs m c cs -> (k + len <= length cs)%nat ->
  rw_cells rsegs m (c + Z.of_nat k) [CB len (firstn len (skipn k cs))].
Proof.
  intros m c cs k len [HB HW] Hk.
  assert (L : length (firstn len (skipn k cs)) = len) by (rewrite length_firstn, length_skipn; lia).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact (c2m_bytes_sub m c cs k len HB Hk).
  - cbn [cells_size csize]. destruct HW as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
    replace (c + Z.of_nat k + i) with (c + (Z.of_nat k + i)) by lia. apply W. lia.
Qed.

Lemma c2m_bytes_det : forall m a bs1 bs2, bytes_at rsegs m a bs1 -> bytes_at rsegs m a bs2 ->
  length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) HL. apply c2m_ext. intros i.
  destruct (Nat.ltb_spec i (length bs1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.

Lemma c2m_nth_upd : forall (cs T : list byte) k i, (k + length T <= length cs)%nat ->
  nth_error (upd_bytes cs k T) i =
    if (Nat.leb k i && Nat.ltb i (k + length T))%bool then nth_error T (i - k) else nth_error cs i.
Proof.
  intros cs T k i H. destruct (Nat.ltb_spec i (length cs)) as [Hi|Hi].
  - apply upd_bytes_nth; assumption.
  - rewrite (proj2 (nth_error_None (upd_bytes cs k T) i)) by (rewrite upd_bytes_length; lia).
    destruct (Nat.leb_spec k i); destruct (Nat.ltb_spec i (k + length T)); cbn [andb]; try (exfalso; lia).
    all: symmetry; apply nth_error_None; lia.
Qed.

Lemma c2m_nth_slice : forall (c : list byte) off n i,
  nth_error (slice c off n) i = if Nat.ltb i (Z.to_nat n) then nth_error c (Z.to_nat off + i) else None.
Proof.
  intros c off n i. unfold slice. destruct (Nat.ltb_spec i (Z.to_nat n)) as [H|H].
  - rewrite c2m_nth_firstn by exact H. apply c2m_nth_skipn.
  - apply nth_error_None. rewrite length_firstn. lia.
Qed.

Lemma c2m_slice_out : forall (cs T : list byte) X off len,
  0 <= X -> 0 <= off -> 0 <= len -> (Z.to_nat X + length T <= length cs)%nat ->
  off + len <= X \/ X + Z.of_nat (length T) <= off ->
  slice (upd_bytes cs (Z.to_nat X) T) off len = slice cs off len.
Proof.
  intros cs T X off len HX Ho Hl HL Hd. apply c2m_ext. intros i. rewrite !c2m_nth_slice.
  destruct (Nat.ltb_spec i (Z.to_nat len)) as [Hi|Hi]; [|reflexivity].
  rewrite c2m_nth_upd by exact HL.
  destruct (Nat.leb_spec (Z.to_nat X) (Z.to_nat off + i));
    destruct (Nat.ltb_spec (Z.to_nat off + i) (Z.to_nat X + length T)); cbn [andb]; try reflexivity.
  exfalso. lia.
Qed.

Lemma c2m_slice_in : forall (cs T : list byte) X len, 0 <= X -> Z.of_nat (length T) = len ->
  (Z.to_nat X + length T <= length cs)%nat -> slice (upd_bytes cs (Z.to_nat X) T) X len = T.
Proof.
  intros cs T X len HX HT HL. apply c2m_ext. intros i. rewrite c2m_nth_slice.
  replace (Z.to_nat len) with (length T) by lia.
  destruct (Nat.ltb_spec i (length T)) as [Hi|Hi].
  - rewrite c2m_nth_upd by exact HL.
    destruct (Nat.leb_spec (Z.to_nat X) (Z.to_nat X + i));
      destruct (Nat.ltb_spec (Z.to_nat X + i) (Z.to_nat X + length T)); cbn [andb]; try (exfalso; lia).
    f_equal. lia.
  - symmetry. apply nth_error_None. lia.
Qed.

Lemma c2m_slice_pre : forall (cs T : list byte) X len j, 0 <= X -> (Z.to_nat X + length T <= length cs)%nat ->
  (j < length T)%nat -> (j < Z.to_nat len)%nat ->
  nth_error (slice (upd_bytes cs (Z.to_nat X) T) X len) j = nth_error T j.
Proof.
  intros cs T X len j HX HL Hj Hjl. rewrite c2m_nth_slice.
  destruct (Nat.ltb_spec j (Z.to_nat len)); [|exfalso; lia].
  rewrite c2m_nth_upd by exact HL.
  destruct (Nat.leb_spec (Z.to_nat X) (Z.to_nat X + j));
    destruct (Nat.ltb_spec (Z.to_nat X + j) (Z.to_nat X + length T)); cbn [andb]; try (exfalso; lia).
  f_equal. lia.
Qed.

Lemma c2m_firstn_slice : forall (l : list byte) off len k, (k <= Z.to_nat len)%nat ->
  firstn k (skipn (Z.to_nat off) l) = firstn k (slice l off len).
Proof. intros l off len k H. unfold slice. rewrite firstn_firstn. f_equal. lia. Qed.

(* C strings inside a byte list *)
Lemma c2m_zb0 : forall b : byte, bz b = 0 -> b = zb 0.
Proof. intros b H. apply bv_eq. unfold bz in H. rewrite H. reflexivity. Qed.

Lemma c2m_nul_nth : forall (l : list byte) d, (nul_at l < length l)%nat -> bz (nth (nul_at l) l d) = 0.
Proof.
  induction l as [|x l IH]; intros d H; cbn [length] in H; [cbn [nul_at] in H; lia|].
  revert H. cbn [nul_at]. destruct (bz x =? 0) eqn:E; intros H; cbn [nth].
  - apply Z.eqb_eq. exact E.
  - apply IH. lia.
Qed.

Lemma c2m_nul_at_eq : forall (l : list byte) p,
  (forall j, (j < p)%nat -> exists b, nth_error l j = Some b /\ bz b <> 0) ->
  (exists b, nth_error l p = Some b /\ bz b = 0) -> nul_at l = p.
Proof.
  induction l as [|x l IH]; intros p H1 (b & Hb & Hb0).
  - destruct p; cbn in Hb; discriminate Hb.
  - destruct p as [|p].
    + cbn [nth_error] in Hb. injection Hb as ->. cbn [nul_at]. rewrite (proj2 (Z.eqb_eq _ _) Hb0). reflexivity.
    + destruct (H1 O ltac:(lia)) as (b0 & Hx & Hx0). cbn [nth_error] in Hx. injection Hx as ->.
      cbn [nul_at]. rewrite (proj2 (Z.eqb_neq _ _) Hx0). f_equal. apply IH.
      * intros j Hj. exact (H1 (S j) ltac:(lia)).
      * exists b. split; [exact Hb | exact Hb0].
Qed.

Lemma c2m_cstr_eq : forall (l t : list byte), (forall j, (j < length t)%nat -> nth_error l j = nth_error t j) ->
  (forall b, In b t -> bz b <> 0) -> (exists b, nth_error l (length t) = Some b /\ bz b = 0) ->
  nul_at l = length t /\ cstr l = t.
Proof.
  intros l t H1 H2 H3.
  assert (Hn : nul_at l = length t).
  { apply c2m_nul_at_eq; [|exact H3].
    intros j Hj. rewrite H1 by exact Hj. destruct (nth_error t j) as [b|] eqn:E.
    - exists b. split; [reflexivity|]. apply H2. exact (nth_error_In t j E).
    - exfalso. apply nth_error_None in E. lia. }
  split; [exact Hn|]. unfold cstr. rewrite Hn. apply c2m_ext. intros j.
  destruct (Nat.ltb_spec j (length t)) as [Hj|Hj].
  - rewrite c2m_nth_firstn by exact Hj. apply H1. exact Hj.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite length_firstn; lia). symmetry. apply nth_error_None. lia.
Qed.

(* the C string of a 16-byte slot with a NUL inside it, and its NUL, are bytes of the block *)
Lemma c2m_cstr_prefix : forall m c cs off len, bytes_at rsegs m c cs -> 0 <= off ->
  (Z.to_nat off + Z.to_nat len <= length cs)%nat -> (nul_at (slice cs off len) < Z.to_nat len)%nat ->
  bytes_at rsegs m (c + off) (cstr (slice cs off len) ++ [zb 0]) /\ ~ In (zb 0) (cstr (slice cs off len)).
Proof.
  intros m c cs off len HB Ho Hl Hn.
  remember (slice cs off len) as sl eqn:Esl.
  assert (Lsl : length sl = Z.to_nat len) by (subst sl; unfold slice; rewrite length_firstn, length_skipn; lia).
  assert (E1 : firstn (S (nul_at sl)) (skipn (Z.to_nat off) cs) = cstr sl ++ [zb 0]).
  { rewrite (c2m_firstn_slice cs off len) by lia. rewrite <- Esl.
    rewrite (c2m_firstn_S sl (nul_at sl) (zb 0)) by lia. unfold cstr. f_equal. f_equal.
    apply c2m_zb0. apply c2m_nul_nth. lia. }
  pose proof (c2m_bytes_sub m c cs (Z.to_nat off) (S (nul_at sl)) HB ltac:(lia)) as HB1.
  rewrite E1, Z2Nat.id in HB1 by exact Ho.
  split; [exact HB1|].
  intro Hin. exact (firstn_nul_free sl (nul_at sl) (zb 0) (le_n _) Hin eq_refl).
Qed.

(* ==========================================================================
   3. The model block lies outside the image: below 0x10000 or at or above 0x960e0
   ========================================================================== *)

Definition c2m_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint c2m_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => c2m_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma c2m_cov_in : forall L cur x, cur <= x < c2m_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [c2m_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Lemma c2m_cov_img : 0x960e0 <= c2m_cov (c2m_ivs (segments_reserved rsegs)) 0x10000.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma c2m_md_img : forall E, lenv_ok E -> e_md E + MD_SIZE <= 0x10000 \/ 0x960e0 <= e_md E.
Proof.
  intros E HE. destruct HE as (_ & _ & _ & (_ & _ & HF) & _).
  assert (C : forall x, 0x10000 <= x < 0x960e0 -> exists s, In s (segments_reserved rsegs) /\
                bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. pose proof c2m_cov_img as Hc.
    destruct (c2m_cov_in (c2m_ivs (segments_reserved rsegs)) 0x10000 x ltac:(lia)) as (a & b & Hin & Hab).
    unfold c2m_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). injection Es as Ea Eb.
    exists s. split; [exact Hs | lia]. }
  destruct (Z.lt_ge_cases (e_md E) 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (e_md E + MD_SIZE) 0x10000) as [H2|H2]; [left; exact H2|].
    exfalso. destruct (C 0x10000 ltac:(lia)) as (s & Hs & Hx).
    apply (HF (0x10000 - e_md E) ltac:(lia) s Hs). replace (e_md E + (0x10000 - e_md E)) with 0x10000 by lia.
    exact Hx.
  - destruct (Z.lt_ge_cases (e_md E) 0x960e0) as [H2|H2]; [|right; exact H2].
    exfalso. destruct (C (e_md E) ltac:(lia)) as (s & Hs & Hx).
    apply (HF 0 ltac:(unfold MD_SIZE; lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

(* ==========================================================================
   4. What a write inside the stack window [S - 65536, S - 480) or inside md keeps
   ========================================================================== *)

Definition c2m_W (E : lenv) : list ivl :=
  [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME); (e_md E, e_md E + MD_SIZE)].

Lemma c2m_munch_write : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  munch [(a, a + Z.of_nat (length bs))] m (write_to_mem m (wa a) bs).
Proof. intros m a bs Ha Hl. apply munch_write; [apply munch_refl | lia | lia | cbn [inside]; left; lia]. Qed.

Lemma c2m_sub_md : forall E lo hi, e_md E <= lo -> hi <= e_md E + MD_SIZE -> sub_fp [(lo, hi)] (c2m_W E).
Proof. intros E lo hi H1 H2 x Hx. unfold c2m_W in Hx. cbn [outside] in *. split; [lia | exact I]. Qed.

Lemma c2m_sub_pf : forall E lo hi D D2, lo = e_S E - SLOT_STACK_Z -> hi = e_S E - SLOT_FRAME ->
  e_md E <= D -> D2 <= e_md E + MD_SIZE -> sub_fp [(lo, hi); (D, D2)] (c2m_W E).
Proof.
  intros E lo hi D D2 -> -> H1 H2 x Hx. unfold c2m_W in Hx. cbn [outside] in *.
  split; [lia|]. split; [lia | exact I].
Qed.

Lemma c2m_task_write : forall m a bs, MemNorm.task_mem rsegs m -> 0 <= a ->
  a + Z.of_nat (length bs) <= TASK_SIZE -> MemNorm.task_mem rsegs (write_to_mem m (wa a) bs).
Proof.
  intros m a bs HT Ha Hl x b Hx. destruct (write_to_mem_some bs m (wa a) x b Hx) as [H|(i & Hi & ->)].
  - exact (HT x b H).
  - right. unfold TASK_SIZE in *. rewrite (wa_unsigned a) by lia. rewrite wa_unsigned by lia. lia.
Qed.

Lemma c2m_segfp : forall E m m', munch (c2m_W E) m m' -> wmono rsegs m m' -> seg_fp (e_S E) (c2_hp E) m m'.
Proof.
  intros E m m' MU WM. exists (c2m_W E). split; [exact MU|]. split; [exact WM|].
  intros x Hx Hn. unfold c2m_W in Hn. cbn [outside] in Hn. unfold own_w, c2_hp.
  destruct (Z_le_gt_dec (e_md E) x) as [A1|A1]; destruct (Z_lt_ge_dec x (e_md E + MD_SIZE)) as [A2|A2].
  1: { right; right; right; right; right. exists (e_md E), MD_SIZE. split; [left; reflexivity | lia]. }
  all: destruct (Z_le_gt_dec (e_S E - SLOT_STACK_Z) x) as [B1|B1];
       destruct (Z_lt_ge_dec x (e_S E - SLOT_FRAME)) as [B2|B2];
       first [ left; unfold SLOT_FRAME in *; lia
             | exfalso; apply Hn; split; [lia | split; [lia | exact I]] ].
Qed.

Section C2mKeep.
Variables (E : lenv) (m m' : word -> option byte).
Hypothesis HE : lenv_ok E.
Hypothesis MU : munch (c2m_W E) m m'.
Hypothesis WM : wmono rsegs m m'.

Lemma c2m_disj_img : forall A len, 0x10000 <= A -> A + len <= 0x960e0 -> disjoint_from (c2m_W E) A len.
Proof.
  intros A len H1 H2. pose proof (c2m_md_img E HE) as Hm. pose proof HE as (HS1 & _).
  unfold c2m_W, SLOT_STACK_Z, SLOT_FRAME in *. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma c2m_disj_hi : forall A len, e_S E - SLOT_FRAME <= A -> disjoint_from (c2m_W E) A len.
Proof.
  intros A len H. pose proof HE as (HS1 & HS2 & HS3 & (Hm0 & Hm1 & _) & _).
  unfold c2m_W. cbn [disjoint_from]. split; [lia|]. split; [unfold SLOT_STACK_Z, SLOT_FRAME in *; lia | exact I].
Qed.

Lemma c2m_bytes_img : forall A bs, bytes_at rsegs m A bs -> 0x10000 <= A ->
  A + Z.of_nat (length bs) <= 0x960e0 -> bytes_at rsegs m' A bs.
Proof. intros A bs H H1 H2. exact (bytes_at_transport rsegs _ m m' A bs H MU (c2m_disj_img A _ H1 H2)). Qed.

Lemma c2m_cstr_img : forall a s, cstr_at m a s -> 0x10000 <= a -> a + Z.of_nat (length s) + 1 <= 0x960e0 ->
  cstr_at m' a s.
Proof.
  intros a s [H H0] H1 H2. split; [|exact H0].
  apply c2m_bytes_img; [exact H | exact H1 | rewrite length_app; cbn [length]; lia].
Qed.

Lemma c2m_u64_img : forall a v, u64_at m a v -> 0x10000 <= a -> a + 8 <= 0x960e0 -> u64_at m' a v.
Proof. unfold u64_at. intros a v H H1 H2. apply c2m_bytes_img; [exact H | exact H1 | rewrite length_le8; lia]. Qed.

Lemma c2m_gnames : gnames_at m -> gnames_at m'.
Proof.
  intros H k Hk. destruct (H k Hk) as (rest & HB & HL). exists rest. split; [|exact HL].
  apply c2m_bytes_img; [exact HB | unfold A_G_NAMES; lia | rewrite HL; unfold A_G_NAMES; lia].
Qed.

Lemma c2m_odd_loc : forall i, (i < 6)%nat ->
  0x10000 <= nth i odd_ptrs 0 /\ nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x960e0.
Proof.
  intros i Hi. do 6 (destruct i as [|i]; [vm_compute; split; intro Hc; discriminate Hc|]). lia.
Qed.

Lemma c2m_odd : odd_at m -> odd_at m'.
Proof.
  intros H i Hi. destruct (H i Hi) as [H1 H2]. destruct (c2m_odd_loc i Hi) as [L1 L2]. split.
  - apply c2m_u64_img; [exact H1 | unfold A_ODD; lia | unfold A_ODD; lia].
  - apply c2m_cstr_img; [exact H2 | exact L1 | exact L2].
Qed.

Lemma c2m_policy : policy_ro m -> policy_ro m'.
Proof.
  intros (H1 & H2 & H3 & H4).
  split; [|split; [|split]]; (apply c2m_cstr_img; [assumption | |]).
  all: unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY, S_PREFIX, S_SERVED, S_VLAN; rewrite ?length_map; cbn [length]; lia.
Qed.

Lemma c2m_la : la_ok m -> la_ok m'.
Proof.
  intros (la & sl & HR & HB & HL). exists la, sl. split; [|split; [|exact HL]].
  - apply (rw_cells_transport rsegs _ m m' _ _ HR MU WM). apply c2m_disj_img; [unfold A_LONG_ALIAS; lia|].
    change (Z.of_nat (cells_size _)) with 301. unfold A_LONG_ALIAS. lia.
  - apply c2m_bytes_img; [exact HB | unfold A_LONG_ALIAS, LONG_ALIAS_SIZE; lia |].
    rewrite HL. unfold A_LONG_ALIAS, LONG_ALIAS_SIZE. lia.
Qed.

Lemma c2m_texts : texts_at m -> texts_at m'.
Proof. intros H i Hi. apply c2m_u64_img; [exact (H i Hi) | unfold A_TEXTS; lia | unfold A_TEXTS; lia]. Qed.

Lemma c2m_ifptrs : ifptrs_at m -> ifptrs_at m'.
Proof.
  intros H i Hi. apply c2m_u64_img; [exact (H i Hi) | unfold A_G_NL, NK_IF_NAME; lia | unfold A_G_NL, NK_IF_NAME; lia].
Qed.

Lemma c2m_guard : guard_m m -> guard_m m'.
Proof.
  intros [H1 (c & H2)]. split; [|exists c].
  - apply c2m_bytes_img; [exact H1 | unfold A_GOT_GUARD_S; lia | rewrite length_le8; unfold A_GOT_GUARD_S; lia].
  - apply c2m_bytes_img; [exact H2 | unfold A_GUARD_S; lia | rewrite length_le8; unfold A_GUARD_S; lia].
Qed.

Lemma c2m_saved : bytes_at rsegs m (e_S E - 104) (e_saved E) -> bytes_at rsegs m' (e_S E - 104) (e_saved E).
Proof. intros H. apply (bytes_at_transport rsegs _ m m' _ _ H MU). apply c2m_disj_hi. unfold SLOT_FRAME. lia. Qed.

Lemma c2m_frame : forall P N j0 j1 j2, c2_frame E P N j0 j1 j2 m -> c2_frame E P N j0 j1 j2 m'.
Proof.
  intros P N j0 j1 j2 H. unfold c2_frame in *. apply (rw_cells_transport rsegs _ m m' _ _ H MU WM).
  apply c2m_disj_hi. lia.
Qed.

Lemma c2m_cursor : forall P N, cursor_ok m (e_p0 E) (e_pl E) P N -> cursor_ok m' (e_p0 E) (e_pl E) P N.
Proof.
  intros P N [HB HK]. split; [|exact HK]. apply (bytes_at_transport rsegs _ m m' _ _ HB MU).
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hp0 & Hp1 & _) & Hpm & _).
  unfold c2m_W. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma c2m_marks : forall gbs, c2_marks E gbs m -> c2_marks E gbs m'.
Proof.
  intros gbs ((HU & HL) & HW). split; [split; [|exact HL] | exact HW].
  apply (u8arr_transport rsegs _ m m' _ _ HU MU WM).
  pose proof HE as (_ & _ & _ & _ & (Hk0 & Hk1 & _) & _ & _ & Hdj & _).
  unfold c2m_W. cbn [disjoint_from]. rewrite HL. split; [lia|]. split; [lia | exact I].
Qed.

Lemma c2m_name : forall s, c2_name_ok m s -> c2_name_ok m' s.
Proof.
  intros s [HA HN]. split.
  - revert HA. destruct (sel_name s) as [t|] eqn:Es; intros HA; cbn [str_arg] in *; [|exact HA].
    destruct HA as [Hp HC]. split; [exact Hp|].
    destruct (HN t eq_refl) as (Hl & Hloc & _).
    apply c2m_cstr_img; [exact HC | |];
      destruct Hloc as [(L1 & L2) | (k & Hk & Ek & Hl4)]; unfold A_RO_LO, A_RO_END, A_G_NAMES in *; lia.
  - intros t Ht. destruct (HN t Ht) as (Hl & Hloc & (sl & HB & HL)).
    split; [exact Hl|]. split; [exact Hloc|]. exists sl. split; [|exact HL].
    pose proof (Z.mod_pos_bound (- (sel_ptr s + Z.of_nat (length t) + 1)) 8 ltac:(lia)) as Hm.
    apply c2m_bytes_img; [exact HB | |];
      destruct Hloc as [(L1 & L2) | (k & Hk & Ek & Hl4)]; unfold A_RO_LO, A_RO_END, A_G_NAMES in *; lia.
Qed.

Lemma c2m_tab_facts : forall i nm ix, nth_error link_tab i = Some (nm, ix) -> (i < 64)%nat /\ (length nm <= 11)%nat.
Proof.
  intros i nm ix H. split.
  - apply nth_error_lt in H. replace (length link_tab) with 64%nat in H by (vm_compute; reflexivity). exact H.
  - apply nth_error_In in H.
    assert (C : forallb (fun e : list byte * Z => Nat.leb (length (fst e)) 11) link_tab = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in C. specialize (C _ H). cbn [fst] in C. apply Nat.leb_le. exact C.
Qed.

Lemma c2m_ptr_loc : forall i, (i < 64)%nat -> 0x10000 <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + 12 <= 0x960e0.
Proof.
  intros i Hi.
  assert (C : forallb (fun p => (0x10000 <=? p) && (p + 12 <=? 0x960e0)) link_ptrs = true)
    by (vm_compute; reflexivity).
  assert (Hl : length link_ptrs = 64%nat) by (vm_compute; reflexivity).
  assert (Hin : In (nth i link_ptrs 0) link_ptrs) by (apply nth_In; lia).
  rewrite forallb_forall in C. specialize (C _ Hin).
  apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

Lemma c2m_u64_det : forall a p q, u64_at m a p -> u64_at m a q -> 0 <= p < 2^64 -> 0 <= q < 2^64 -> p = q.
Proof.
  intros a p q Hp Hq Rp Rq. unfold u64_at in *.
  pose proof (c2m_bytes_det m a _ _ Hp Hq ltac:(rewrite !length_le8; reflexivity)) as Eb.
  apply (f_equal le_bytes_to_word) in Eb. rewrite !le_bytes_to_word_le8 in Eb.
  unfold wz in Eb. apply (f_equal bv_unsigned) in Eb. rewrite !unsigned_lit in Eb by lia. exact Eb.
Qed.

Lemma c2m_iftab : forall kbs, ifptrs_at m -> iftab_at m kbs link_tab -> iftab_at m' kbs link_tab.
Proof.
  intros kbs HP (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i nm ix Hn. destruct (H3 i nm ix Hn) as (Hix & p & Hu & Hp0 & Hc & Hx).
  destruct (c2m_tab_facts i nm ix Hn) as [Hi Hl].
  pose proof (HP i Hi) as Hq. destruct (c2m_ptr_loc i Hi) as [Q1 Q2].
  assert (Rp : 0 <= p < 2^64).
  { pose proof Hc as ((Hc0 & Hc1 & _) & _). rewrite length_app in Hc1. cbn [length] in Hc1. lia. }
  assert (Ep : p = nth i link_ptrs 0) by (apply (c2m_u64_det _ p _ Hu Hq Rp); lia).
  split; [exact Hix|]. exists p. split; [|split; [exact Hp0|split]].
  - apply c2m_u64_img; [exact Hu | unfold A_G_NL, NK_IF_NAME; lia | unfold A_G_NL, NK_IF_NAME; lia].
  - apply c2m_cstr_img; [exact Hc | lia | lia].
  - unfold u32_at in *. apply c2m_bytes_img; [exact Hx | unfold A_G_NL, NK_IF_INDEX; lia |].
    rewrite length_le4. unfold A_G_NL, NK_IF_INDEX. lia.
Qed.

Lemma c2m_kern : forall i kbs, ifptrs_at m -> c2_kern i kbs m -> c2_kern i kbs m'.
Proof.
  intros i kbs HP ((HU & HL) & HW & HT & HR).
  split; [split; [|exact HL] | split; [exact HW | split; [exact (c2m_iftab kbs HP HT) | exact HR]]].
  apply (u8arr_transport rsegs _ m m' _ _ HU MU WM).
  apply c2m_disj_img; [unfold A_G_NL; lia | rewrite HL; unfold A_G_NL, NK_SIZE; lia].
Qed.

Lemma c2m_fix : mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) -> c2_fix E m -> c2_fix E m'.
Proof.
  intros MI TM ST (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _ & _ & _).
  split; [exact (c2m_saved H1)|]. split; [exact (c2m_gnames H2)|]. split; [exact (c2m_odd H3)|].
  split; [exact (c2m_policy H4)|]. split; [exact (c2m_la H5)|]. split; [exact (c2m_texts H6)|].
  split; [exact (c2m_ifptrs H7)|]. split; [exact (wr_at_transport rsegs m m' _ _ H8 WM)|].
  split; [exact (c2m_guard H9)|]. split; [exact MI|]. split; [exact TM | exact ST].
Qed.

End C2mKeep.

(* ==========================================================================
   5. The model block after `sw n + 1, MD_N_MARK` and snprintf of the name t into slot n
   ========================================================================== *)

Definition c2m_D (n : Z) : Z := MD_MARK + MARK_LEN * n.
Definition c2m_mbs1 (mbs : list byte) (n : Z) : list byte :=
  upd_bytes mbs (Z.to_nat MD_N_MARK) (le4 (Z_to_bv 64 (n + 1))).
Definition c2m_mbs2 (mbs : list byte) (n : Z) (t : list byte) : list byte :=
  upd_bytes (c2m_mbs1 mbs n) (Z.to_nat (c2m_D n)) (t ++ [zb 0]).

Lemma c2m_len1 : forall mbs n, Z.of_nat (length mbs) = MD_SIZE -> length (c2m_mbs1 mbs n) = length mbs.
Proof. intros mbs n HL. unfold c2m_mbs1. apply upd_bytes_length. rewrite length_le4. c2m_lia. Qed.

Lemma c2m_lenT : forall t : list byte, length (t ++ [zb 0]) = S (length t).
Proof. intros t. rewrite length_app. cbn [length]. lia. Qed.

Lemma c2m_len2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  length (c2m_mbs2 mbs n t) = length mbs.
Proof.
  intros mbs n t HL Hn Ht. unfold c2m_mbs2. rewrite upd_bytes_length; [apply c2m_len1; exact HL|].
  rewrite c2m_len1 by exact HL. rewrite c2m_lenT. unfold c2m_D. c2m_lia.
Qed.

Lemma c2m_slice2 : forall mbs n t off len, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  0 <= off -> 0 <= len -> off + len <= MD_N_MARK ->
  (off + len <= c2m_D n \/ c2m_D n + Z.of_nat (length t) + 1 <= off) ->
  slice (c2m_mbs2 mbs n t) off len = slice mbs off len.
Proof.
  intros mbs n t off len HL Hn Ht Ho Hl H1 H2. unfold c2m_mbs2.
  pose proof (c2m_len1 mbs n HL) as L1. pose proof (c2m_lenT t) as LT.
  rewrite c2m_slice_out by (rewrite ?L1, ?LT; unfold c2m_D in *; c2m_lia).
  unfold c2m_mbs1. apply c2m_slice_out; [c2m_lia | exact Ho | exact Hl | rewrite length_le4; c2m_lia | left; exact H1].
Qed.

Lemma c2m_fld32 : forall mbs n t off, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  0 <= off -> off + 4 <= MD_MARK -> fld_u32 (c2m_mbs2 mbs n t) off = fld_u32 mbs off.
Proof.
  intros mbs n t off HL Hn Ht Ho H. unfold fld_u32, link_spec.rdn.
  rewrite c2m_slice2 by (first [assumption | unfold c2m_D; c2m_lia]). reflexivity.
Qed.

Lemma c2m_nmark2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  md_n_mark (c2m_mbs2 mbs n t) = n + 1.
Proof.
  intros mbs n t HL Hn Ht. unfold md_n_mark, fld_u32, link_spec.rdn, c2m_mbs2.
  pose proof (c2m_len1 mbs n HL) as L1. pose proof (c2m_lenT t) as LT.
  rewrite (c2m_slice_out (c2m_mbs1 mbs n) (t ++ [zb 0]) (c2m_D n) MD_N_MARK 4)
    by (rewrite ?L1, ?LT; unfold c2m_D in *; c2m_lia).
  unfold c2m_mbs1.
  rewrite (c2m_slice_in mbs (le4 (Z_to_bv 64 (n + 1))) MD_N_MARK 4)
    by (first [rewrite length_le4; reflexivity | rewrite length_le4; c2m_lia | c2m_lia]).
  rewrite bytes_le_to_Z_le4, unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma c2m_reqs2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  model_wf mbs -> md_reqs (c2m_mbs2 mbs n t) = md_reqs mbs.
Proof.
  intros mbs n t HL Hn Ht (Hr & _ & _ & _ & Hrl & _).
  assert (En : md_n_req (c2m_mbs2 mbs n t) = md_n_req mbs)
    by (unfold md_n_req; apply c2m_fld32; first [assumption | c2m_lia]).
  unfold md_reqs. rewrite En. apply map_ext_in. intros i Hi. apply in_seq in Hi. cbv beta.
  assert (Hi' : 0 <= Z.of_nat i < md_n_req mbs) by lia.
  pose proof (Hrl (Z.of_nat i) Hi') as Hli.
  unfold md_req_one.
  assert (El : fld_u64 (c2m_mbs2 mbs n t) (MD_REQ_LEN + 8 * Z.of_nat i) = fld_u64 mbs (MD_REQ_LEN + 8 * Z.of_nat i)).
  { unfold fld_u64, link_spec.rdn. rewrite c2m_slice2 by (first [assumption | unfold c2m_D; c2m_lia]). reflexivity. }
  rewrite El. apply c2m_slice2; first [assumption | unfold c2m_D; c2m_lia].
Qed.

Lemma c2m_slotk2 : forall mbs n t j, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  0 <= j < n -> slice (c2m_mbs2 mbs n t) (MD_MARK + MARK_LEN * j) MARK_LEN = slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN.
Proof. intros mbs n t j HL Hn Ht Hj. apply c2m_slice2; first [assumption | unfold c2m_D; c2m_lia]. Qed.

Lemma c2m_slotn2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> 0 <= n < 32 -> (length t <= 11)%nat ->
  ~ In (zb 0) t ->
  nul_at (slice (c2m_mbs2 mbs n t) (c2m_D n) MARK_LEN) = length t /\
  cstr (slice (c2m_mbs2 mbs n t) (c2m_D n) MARK_LEN) = t.
Proof.
  intros mbs n t HL Hn Ht H0.
  pose proof (c2m_len1 mbs n HL) as L1. pose proof (c2m_lenT t) as LT.
  apply c2m_cstr_eq.
  - intros j Hj. unfold c2m_mbs2.
    rewrite c2m_slice_pre; [ | unfold c2m_D; c2m_lia | rewrite L1, LT; unfold c2m_D; c2m_lia
                             | rewrite LT; lia | unfold MARK_LEN; lia].
    rewrite nth_error_app1 by exact Hj. reflexivity.
  - intros b Hb Hb0. apply H0. replace (zb 0) with b; [exact Hb|]. apply c2m_zb0. exact Hb0.
  - exists (zb 0). split; [|reflexivity]. unfold c2m_mbs2.
    rewrite c2m_slice_pre; [ | unfold c2m_D; c2m_lia | rewrite L1, LT; unfold c2m_D; c2m_lia
                             | rewrite LT; lia | unfold MARK_LEN; lia].
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma c2m_marks2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> n = md_n_mark mbs -> 0 <= n < 32 ->
  (length t <= 11)%nat -> ~ In (zb 0) t -> md_marks (c2m_mbs2 mbs n t) = md_marks mbs ++ [t].
Proof.
  intros mbs n t HL En Hn Ht H0. unfold md_marks.
  rewrite (c2m_nmark2 mbs n t HL Hn Ht). rewrite <- En.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. rewrite seq_S, map_app. cbn [map]. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. cbv beta. f_equal.
    apply c2m_slotk2; try assumption. lia.
  - f_equal.
    lazymatch goal with |- cstr (slice _ ?o _) = _ =>
      replace o with (c2m_D n) by (unfold c2m_D, MD_MARK, MARK_LEN; lia) end.
    exact (proj2 (c2m_slotn2 mbs n t HL Hn Ht H0)).
Qed.

Lemma c2m_wf2 : forall mbs n t, Z.of_nat (length mbs) = MD_SIZE -> n = md_n_mark mbs -> 0 <= n < 32 ->
  (length t <= 11)%nat -> ~ In (zb 0) t -> model_wf mbs -> model_wf (c2m_mbs2 mbs n t).
Proof.
  intros mbs n t HL En Hn Ht H0 (Hr & Hx & Hs1 & Hs2 & Hrl & (Hm & Hst)).
  assert (F : forall off, 0 <= off -> off + 4 <= MD_MARK -> fld_u32 (c2m_mbs2 mbs n t) off = fld_u32 mbs off)
    by (intros off Ho Hof; apply c2m_fld32; assumption).
  assert (Er : md_n_req (c2m_mbs2 mbs n t) = md_n_req mbs) by (unfold md_n_req; apply F; c2m_lia).
  split; [rewrite Er; exact Hr|].
  split; [unfold md_next; rewrite F by c2m_lia; exact Hx|].
  split; [unfold md_socket_errno; rewrite F by c2m_lia; exact Hs1|].
  split; [unfold md_send_errno; rewrite F by c2m_lia; exact Hs2|].
  split.
  - intros i Hi. rewrite Er in Hi.
    unfold fld_u64, link_spec.rdn. rewrite c2m_slice2 by (first [assumption | unfold c2m_D; c2m_lia]).
    exact (Hrl i Hi).
  - unfold model_marks_wf. rewrite (c2m_nmark2 mbs n t HL Hn Ht). split; [unfold MARKS_MAX; lia|].
    intros i Hi. destruct (Z.eq_dec i n) as [->|Hne].
    + fold (c2m_D n). rewrite (proj1 (c2m_slotn2 mbs n t HL Hn Ht H0)). unfold MARK_LEN. lia.
    + rewrite c2m_slotk2 by (first [assumption | lia]). apply Hst. lia.
Qed.

(* the block after both writes: bytes of the old block, the new count, the name and its NUL *)
Lemma c2m_bytes_upd : forall W mm mm' c cs k T,
  bytes_at rsegs mm c cs -> munch W mm mm' -> bytes_at rsegs mm' (c + Z.of_nat k) T ->
  (k + length T <= length cs)%nat ->
  (forall i, (i < length cs)%nat -> (i < k \/ k + length T <= i)%nat -> outside W (c + Z.of_nat i)) ->
  bytes_at rsegs mm' c (upd_bytes cs k T).
Proof.
  intros W mm mm' c cs k T (H0 & H1 & H) MU (G0 & G1 & G) HL HO.
  split; [exact H0|]. rewrite upd_bytes_length by exact HL. split; [exact H1|].
  intros i Hi. rewrite upd_bytes_nth by assumption.
  destruct (Nat.leb_spec k i); destruct (Nat.ltb_spec i (k + length T)); cbn [andb].
  1: { replace (c + Z.of_nat i) with (c + Z.of_nat k + Z.of_nat (i - k)) by lia. apply G. lia. }
  all: rewrite <- (H i Hi); unfold mrd; rewrite (MU (wa (c + Z.of_nat i))); [reflexivity|];
       rewrite wa_unsigned by lia; apply HO; lia.
Qed.

Lemma c2m_pf_t : forall t : list byte, (length t <= 15)%nat ->
  pf_bytes (firstn (Z.to_nat (16 - 1)) (map bz t ++ []) ++ [0]) = t ++ [zb 0].
Proof.
  intros t Ht. rewrite app_nil_r. rewrite firstn_all2 by (rewrite length_map; lia).
  unfold pf_bytes. rewrite map_app, map_map. f_equal.
  transitivity (map (fun b : byte => b) t); [|apply map_id].
  apply map_ext. intros b. unfold bz. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  apply bv_unsigned_in_range.
Qed.

(* ==========================================================================
   6. The marks strcmp reads, and remember
   ========================================================================== *)

Definition c2m_slot (mbs : list byte) (j : Z) : list byte := cstr (slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN).

Lemma c2m_slot_at : forall m md mbs j, model_at m md mbs -> model_wf mbs -> 0 <= j < md_n_mark mbs ->
  bytes_at rsegs m (md + MD_MARK + MARK_LEN * j) (c2m_slot mbs j ++ [zb 0]) /\ ~ In (zb 0) (c2m_slot mbs j).
Proof.
  intros m md mbs j [HB HL] (_ & _ & _ & _ & _ & (Hm & Hst)) Hj.
  replace (md + MD_MARK + MARK_LEN * j) with (md + (MD_MARK + MARK_LEN * j)) by lia.
  unfold c2m_slot. apply c2m_cstr_prefix; [exact (proj1 HB) | c2m_lia | c2m_lia | apply Hst; exact Hj].
Qed.

Lemma c2m_marks_map : forall mbs, md_marks mbs = map (fun i => c2m_slot mbs (Z.of_nat i)) (seq 0 (Z.to_nat (md_n_mark mbs))).
Proof. reflexivity. Qed.

Lemma c2m_rem_in : forall mbs t, 0 <= md_n_mark mbs -> (exists j, 0 <= j < md_n_mark mbs /\ c2m_slot mbs j = t) ->
  remember (md_marks mbs) t = md_marks mbs.
Proof.
  intros mbs t H0 (j & Hj & Ej). unfold remember.
  replace (existsb (fun x => bl_eqb x t) (md_marks mbs)) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists (c2m_slot mbs j). split.
  - rewrite c2m_marks_map. apply in_map_iff. exists (Z.to_nat j). rewrite Z2Nat.id by lia. split; [reflexivity|].
    apply in_seq. lia.
  - apply bl_eqb_iff. exact Ej.
Qed.

Lemma c2m_rem_full : forall mbs t, md_n_mark mbs = 32 -> remember (md_marks mbs) t = md_marks mbs.
Proof.
  intros mbs t H. unfold remember. destruct (existsb (fun x => bl_eqb x t) (md_marks mbs)); [reflexivity|].
  rewrite c2m_marks_map, length_map, length_seq, H. reflexivity.
Qed.

Lemma c2m_rem_new : forall mbs t, 0 <= md_n_mark mbs < 32 -> (length t <= 15)%nat ->
  (forall j, 0 <= j < md_n_mark mbs -> c2m_slot mbs j <> t) ->
  remember (md_marks mbs) t = md_marks mbs ++ [t].
Proof.
  intros mbs t Hn Ht NF. unfold remember.
  replace (existsb (fun x => bl_eqb x t) (md_marks mbs)) with false.
  - rewrite c2m_marks_map, length_map, length_seq.
    replace (Z.of_nat (Z.to_nat (md_n_mark mbs)) <? MARKS_MAX) with true by (symmetry; apply Z.ltb_lt; unfold MARKS_MAX; lia).
    rewrite firstn_all2 by exact Ht. reflexivity.
  - symmetry. apply Bool.not_true_iff_false. intro H. apply existsb_exists in H. destruct H as (x & Hin & Hx).
    rewrite c2m_marks_map in Hin. apply in_map_iff in Hin. destruct Hin as (i & <- & Hi). apply in_seq in Hi.
    apply bl_eqb_iff in Hx. apply (NF (Z.of_nat i)); [lia | exact Hx].
Qed.
