(* op_refused (arm 5 of the slot's loop), plain image: carrying the cut facts of LC45Defs.v across a
   memory change that only touches a set of addresses Pw (munch W with every address of W in Pw), and
   the pure facts about the kernel and model blocks after model_begin (LC45RLib.v c45r_kbs, c45r_mbs). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs LC45RLib.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Footprints
   ========================================================================== *)

Lemma c45r_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z.le_gt_cases lo x) as [H1|H1]; [destruct (Z.lt_ge_cases x hi) as [H2|H2]|].
  - right. intros [H3 _]. apply H3. lia.
  - left. split; [lia|exact H].
  - left. split; [lia|exact H].
Qed.

Lemma c45r_outside_app : forall A B x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof. induction A as [|[lo hi] A IH]; intros B x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.

Lemma c45r_munch_app_l : forall A B m m', munch A m m' -> munch (A ++ B) m m'.
Proof.
  intros A B m m' H. apply (munch_weaken A); [|exact H].
  intros x Hx. apply c45r_outside_app in Hx. exact (proj1 Hx).
Qed.

Lemma c45r_munch_app_r : forall A B m m', munch B m m' -> munch (A ++ B) m m'.
Proof.
  intros A B m m' H. apply (munch_weaken B); [|exact H].
  intros x Hx. apply c45r_outside_app in Hx. exact (proj2 Hx).
Qed.

Lemma c45r_hw1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. cbn [outside] in H.
  destruct (Z.le_gt_cases lo x); destruct (Z.lt_ge_cases x hi); try lia;
    exfalso; apply H; (split; [lia | exact I]).
Qed.

Lemma c45r_tr_task : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x, ~ outside W x -> x < TASK_SIZE) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU H a b E. destruct (c45r_outside_dec W (bv_unsigned a)) as [O|O].
  - rewrite (MU a O) in E. exact (T a b E).
  - right. exact (H _ O).
Qed.

Lemma c45r_task_size : TASK_SIZE = 2 ^ 47.
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   2. Where the static strings lie
   ========================================================================== *)

Lemma c45r_bytes_at_unique : forall m a l1 l2, bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None l1 i) Hi), (proj2 (nth_error_None l2 i) ltac:(lia)). reflexivity.
Qed.

Lemma c45r_u64_same : forall m a p q, u64_at m a p -> u64_at m a q ->
  0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> p = q.
Proof.
  intros m a p q Hp Hq Rp Rq. unfold u64_at in *.
  pose proof (c45r_bytes_at_unique m a _ _ Hp Hq ltac:(rewrite !length_le8; reflexivity)) as E.
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal bv_unsigned) in E. unfold wz in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

Lemma c45r_odd_loc : forall j, (j < 6)%nat ->
  0x10000 <= nth j odd_ptrs 0 /\ nth j odd_ptrs 0 + Z.of_nat (length (nth j odd_strs [])) + 1 <= A_G_NL.
Proof.
  intros j Hj.
  assert (H : forallb (fun j => (0x10000 <=? nth j odd_ptrs 0) &&
                                (nth j odd_ptrs 0 + Z.of_nat (length (nth j odd_strs [])) + 1 <=? A_G_NL))
                      (seq 0 6) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H j ltac:(apply in_seq; lia)).
  apply andb_prop in H as [H1 H2]. split; apply Z.leb_le; assumption.
Qed.

Lemma c45r_link_tab_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma c45r_link_loc : forall j nm ix, nth_error link_tab j = Some (nm, ix) ->
  (j < 64)%nat /\ 0x10000 <= nth j link_ptrs 0 /\ nth j link_ptrs 0 + Z.of_nat (length nm) + 1 <= 0x960e0 /\
  (nth j link_ptrs 0 + Z.of_nat (length nm) + 1 <= A_G_NL \/ A_G_NL + NK_IF_NAME <= nth j link_ptrs 0).
Proof.
  intros j nm ix Hj.
  assert (Hlt : (j < 64)%nat) by (rewrite <- c45r_link_tab_len; apply nth_error_Some; congruence).
  assert (H : forallb (fun j => match nth_error link_tab j with
                                | Some (nm, _) => (0x10000 <=? nth j link_ptrs 0) &&
                                                  (nth j link_ptrs 0 + Z.of_nat (length nm) + 1 <=? 0x960e0) &&
                                                  ((nth j link_ptrs 0 + Z.of_nat (length nm) + 1 <=? A_G_NL) ||
                                                   (A_G_NL + NK_IF_NAME <=? nth j link_ptrs 0))
                                | None => true end) (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H j ltac:(apply in_seq; lia)). rewrite Hj in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact Hlt|]. split; [apply Z.leb_le; exact H1|]. split; [apply Z.leb_le; exact H2|].
  apply orb_prop in H3 as [H3|H3]; [left|right]; apply Z.leb_le; exact H3.
Qed.

(* ==========================================================================
   3. Carrying facts across a change confined to Pw
   ========================================================================== *)

(* the static regions the cuts keep: the image below 0x960e0, outside g_nl's fields before if_name *)
Definition c45r_stat (Pw : Z -> Prop) : Prop :=
  forall x, 0x10000 <= x < 0x960e0 -> (x < A_G_NL \/ A_G_NL + NK_IF_NAME <= x) -> ~ Pw x.

Section Carry.
Variable Pw : Z -> Prop.
Variables (W : list ivl) (m m' : word -> option byte).
Hypothesis HW : forall x, ~ outside W x -> Pw x.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono rsegs m m'.

Lemma c45r_tr_mrd : forall x, 0 <= x < 2 ^ 64 -> ~ Pw x -> mrd rsegs m' (wa x) = mrd rsegs m (wa x).
Proof.
  intros x Hx Hp. unfold mrd. rewrite MU; [reflexivity|].
  rewrite wa_unsigned by lia.
  destruct (c45r_outside_dec W x) as [O|O]; [exact O | exfalso; exact (Hp (HW x O))].
Qed.

Lemma c45r_tr_bytes : forall A bs, bytes_at rsegs m A bs ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> ~ Pw x) -> bytes_at rsegs m' A bs.
Proof.
  intros A bs (H0 & H1 & H) Hp. split; [lia|]. split; [lia|]. intros j Hj.
  rewrite c45r_tr_mrd by (lia || (apply Hp; lia)). apply H, Hj.
Qed.

Lemma c45r_tr_wr : forall A n, wr_at rsegs m A n -> wr_at rsegs m' A n.
Proof. intros A n H. exact (wr_at_transport rsegs m m' A n H WM). Qed.

Lemma c45r_tr_rw : forall A cs, rw_cells rsegs m A cs ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> ~ Pw x) -> rw_cells rsegs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] Hp. split; [split; [exact Hwf|] | exact (c45r_tr_wr _ _ Hw)].
  apply c45r_tr_bytes; [exact Hb|]. rewrite cells_bytes_length by exact Hwf. exact Hp.
Qed.

Lemma c45r_tr_u8 : forall A bs, u8arr rsegs m A bs ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> ~ Pw x) -> u8arr rsegs m' A bs.
Proof. intros A bs [Hb Hw] Hp. split; [exact (c45r_tr_bytes _ _ Hb Hp) | exact (c45r_tr_wr _ _ Hw)]. Qed.

Lemma c45r_tr_cstr : forall A s, cstr_at m A s ->
  (forall x, A <= x < A + Z.of_nat (length s) + 1 -> ~ Pw x) -> cstr_at m' A s.
Proof.
  intros A s [Hb Hn] Hp. split; [|exact Hn]. apply c45r_tr_bytes; [exact Hb|].
  rewrite length_app. cbn [length]. intros x Hx. apply Hp. lia.
Qed.

Lemma c45r_tr_u64 : forall A v, u64_at m A v -> (forall x, A <= x < A + 8 -> ~ Pw x) -> u64_at m' A v.
Proof. intros A v H Hp. unfold u64_at in *. apply c45r_tr_bytes; [exact H|]. rewrite length_le8. exact Hp. Qed.

Lemma c45r_tr_u32 : forall A v, u32_at m A v -> (forall x, A <= x < A + 4 -> ~ Pw x) -> u32_at m' A v.
Proof. intros A v H Hp. unfold u32_at in *. apply c45r_tr_bytes; [exact H|]. rewrite length_le4. exact Hp. Qed.

Lemma c45r_tr_stk : forall lo hi, stk rsegs m lo hi -> (forall x, lo <= x < hi -> ~ Pw x) -> stk rsegs m' lo hi.
Proof.
  intros lo hi ST Hp. apply (stk_transport rsegs W m m' lo hi ST MU WM). intros x Hx. left.
  destruct (c45r_outside_dec W x) as [O|O]; [exact O|]. exfalso. exact (Hp x Hx (HW x O)).
Qed.

Section Stat.
Hypothesis HST : c45r_stat Pw.

Lemma c45r_tr_gnames : gnames_at m -> gnames_at m'.
Proof.
  intros G k Hk. destruct (G k Hk) as (rest & B & L). exists rest. split; [|exact L].
  apply c45r_tr_bytes; [exact B|]. rewrite L. intros x Hx.
  apply HST; unfold A_G_NAMES, A_G_NL, NK_IF_NAME in *; lia.
Qed.

Lemma c45r_tr_odd : odd_at m -> odd_at m'.
Proof.
  intros O j Hj. destruct (O j Hj) as (U & C). destruct (c45r_odd_loc j Hj) as (L1 & L2). split.
  - apply c45r_tr_u64; [exact U|]. intros x Hx. apply HST; unfold A_ODD, A_G_NL in *; lia.
  - apply c45r_tr_cstr; [exact C|]. intros x Hx. apply HST; unfold A_G_NL in *; lia.
Qed.

Lemma c45r_tr_policy : policy_ro m -> policy_ro m'.
Proof.
  intros (P1 & P2 & P3 & P4). split; [|split; [|split]].
  - apply c45r_tr_cstr; [exact P1|]. intros x Hx. unfold S_PREFIX in Hx. rewrite length_map in Hx.
    cbn [length] in Hx. apply HST; unfold A_PREFIX, A_G_NL in *; lia.
  - apply c45r_tr_cstr; [exact P2|]. intros x Hx. unfold S_SERVED in Hx. rewrite length_map in Hx.
    cbn [length] in Hx. apply HST; unfold A_SERVED, A_G_NL in *; lia.
  - apply c45r_tr_cstr; [exact P3|]. intros x Hx. unfold S_VLAN in Hx. rewrite length_map in Hx.
    cbn [length] in Hx. apply HST; unfold A_VLAN, A_G_NL in *; lia.
  - apply c45r_tr_cstr; [exact P4|]. intros x Hx. cbn [length] in Hx.
    apply HST; unfold A_EMPTY, A_G_NL in *; lia.
Qed.

Lemma c45r_tr_la : la_ok m -> la_ok m'.
Proof.
  intros (la & sl & R & B & L). exists la, sl. split; [|split; [|exact L]].
  - apply c45r_tr_rw; [exact R|]. intros x Hx. cbn [cells_size csize] in Hx.
    change (Z.to_nat 300) with 300%nat in Hx.
    apply HST; unfold A_LONG_ALIAS, A_G_NL, NK_IF_NAME in *; lia.
  - apply c45r_tr_bytes; [exact B|]. rewrite L. intros x Hx.
    apply HST; unfold A_LONG_ALIAS, LONG_ALIAS_SIZE, A_G_NL, NK_IF_NAME in *; lia.
Qed.

Lemma c45r_tr_texts : texts_at m -> texts_at m'.
Proof.
  intros T j Hj. apply c45r_tr_u64; [exact (T j Hj)|]. intros x Hx.
  apply HST; unfold A_TEXTS, A_G_NL, NK_IF_NAME in *; lia.
Qed.

Lemma c45r_tr_ifptrs : ifptrs_at m -> ifptrs_at m'.
Proof.
  intros T j Hj. apply c45r_tr_u64; [exact (T j Hj)|]. intros x Hx.
  apply HST; unfold A_G_NL, NK_IF_NAME in *; lia.
Qed.

Lemma c45r_tr_guard : guard_m m -> guard_m m'.
Proof.
  intros (G1 & c & G2). split; [|exists c].
  - apply c45r_tr_bytes; [exact G1|]. rewrite length_le8. intros x Hx.
    apply HST; unfold A_GOT_GUARD_S, A_G_NL, NK_IF_NAME in *; lia.
  - apply c45r_tr_bytes; [exact G2|]. rewrite length_le8. intros x Hx.
    apply HST; unfold A_GUARD_S, A_G_NL, NK_IF_NAME in *; lia.
Qed.

Lemma c45r_tr_keep : forall E, c45_keep E m ->
  (forall x, e_p0 E <= x < e_p0 E + Z.of_nat (length (e_pl E)) -> ~ Pw x) -> c45_keep E m'.
Proof.
  intros E (G & O & PR & LA & TX & IP & WR & GU & PL) Hpl.
  exact (conj (c45r_tr_gnames G) (conj (c45r_tr_odd O) (conj (c45r_tr_policy PR) (conj (c45r_tr_la LA)
    (conj (c45r_tr_texts TX) (conj (c45r_tr_ifptrs IP) (conj (c45r_tr_wr _ _ WR) (conj (c45r_tr_guard GU)
    (c45r_tr_bytes _ _ PL Hpl))))))))).
Qed.

Lemma c45r_tr_iftab : forall kbs, iftab_at m kbs link_tab -> ifptrs_at m -> iftab_at m' kbs link_tab.
Proof.
  intros kbs (N & L & T) IP. split; [exact N|]. split; [exact L|].
  intros j nm ix Hj. destruct (T j nm ix Hj) as (Hix & p & U & Hp0 & C & U4). split; [exact Hix|].
  destruct (c45r_link_loc j nm ix Hj) as (Hlt & L1 & L2 & L3).
  assert (Ep : p = nth j link_ptrs 0).
  { apply (c45r_u64_same m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat j)); [exact U | exact (IP j Hlt) | | ].
    - destruct C as [Cb _]. pose proof (bytes_at_bound rsegs m p _ Cb) as B.
      rewrite length_app in B. cbn [length] in B. lia.
    - lia. }
  exists p. split; [|split; [exact Hp0|split]].
  - apply c45r_tr_u64; [exact U|]. intros x Hx. apply HST; unfold A_G_NL, NK_IF_NAME in *; lia.
  - apply c45r_tr_cstr; [exact C|]. subst p. intros x Hx. apply HST; lia.
  - apply c45r_tr_u32; [exact U4|]. intros x Hx.
    apply HST; unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX in *; lia.
Qed.
End Stat.
End Carry.

(* ==========================================================================
   4. The placement lenv_ok gives, without its pf_img_free premises
   ========================================================================== *)

Definition c45r_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint c45r_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => c45r_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma c45r_cov_in : forall L cur x, cur <= x < c45r_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [c45r_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Lemma c45r_rsegs_pages : c45r_cov (c45r_ivs (segments_reserved rsegs)) 0x10000 = 618496.
Proof. vm_compute. reflexivity. Qed.

Lemma c45r_img_free : forall D n, 0 <= D -> 0 < n -> pf_img_free D n -> D + n <= 0x10000 \/ 618496 <= D.
Proof.
  intros D n HD Hn F.
  assert (C : forall x, 0x10000 <= x < 618496 -> exists s, In s (segments_reserved rsegs)
                /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. rewrite <- c45r_rsegs_pages in Hx. destruct (c45r_cov_in _ _ _ Hx) as (a & b & Hin & Hab).
    unfold c45r_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). injection Es as Ea Eb.
    exists s. split; [exact Hs | lia]. }
  destruct (Z.lt_ge_cases D 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (D + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (C 0x10000 ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F (0x10000 - D) ltac:(lia) s Hs). replace (D + (0x10000 - D)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases D 618496) as [H2|H2]; [|right; exact H2].
    destruct (C D ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

Lemma c45r_lenv : forall E, lenv_ok E ->
  0x960e0 + 65536 <= e_S E <= 2 ^ 47 /\
  4096 <= e_md E /\ e_md E + 8856 <= e_S E - 65536 /\ (e_md E + 8856 <= 0x10000 \/ 618496 <= e_md E) /\
  4096 <= e_mk E /\ e_mk E + 516 <= e_S E - 65536 /\ (e_mk E + 516 <= 0x10000 \/ 618496 <= e_mk E) /\
  1 <= Z.of_nat (length (e_pl E)) < 2 ^ 26 /\ 4096 <= e_p0 E /\
  e_p0 E + Z.of_nat (length (e_pl E)) <= e_S E - 65536 /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= 0x10000 \/ 618496 <= e_p0 E) /\
  (e_md E + 8856 <= e_mk E \/ e_mk E + 516 <= e_md E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_md E \/ e_md E + 8856 <= e_p0 E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_mk E \/ e_mk E + 516 <= e_p0 E).
Proof.
  intros E (S1 & S2 & S3 & (M1 & M2 & M3) & (K1 & K2 & K3) & _ & _ & MK & PL & (P1 & P2 & P3) & PM & PK & _).
  unfold SLOT_STACK_Z, MD_SIZE, MK_SIZE in *.
  pose proof (c45r_img_free (e_md E) 8856 ltac:(lia) ltac:(lia) M3) as IM.
  pose proof (c45r_img_free (e_mk E) 516 ltac:(lia) ltac:(lia) K3) as IK.
  pose proof (c45r_img_free (e_p0 E) (Z.of_nat (length (e_pl E))) ltac:(lia) ltac:(lia) P3) as IP.
  repeat split; assumption || lia.
Qed.

(* ==========================================================================
   5. Byte lists after stores (fields of the kernel and the model)
   ========================================================================== *)

Lemma c45r_nth_firstn : forall {A} (l : list A) n i,
  nth_error (firstn n l) i = if (i <? n)%nat then nth_error l i else None.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i]; cbn; try reflexivity;
    try (rewrite IH; reflexivity);
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma c45r_nth_skipn : forall {A} (l : list A) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros A l. induction l as [|x l IH]; intros n i; destruct n as [|n]; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

Lemma c45r_slice_nth : forall (c : list byte) off len i, 0 <= off -> 0 <= len ->
  nth_error (slice c off len) i =
    if (i <? Z.to_nat len)%nat then nth_error c (Z.to_nat off + i) else None.
Proof. intros c off len i H0 H1. unfold slice. rewrite c45r_nth_firstn, c45r_nth_skipn. reflexivity. Qed.

Lemma c45r_upd_nth : forall (cs bs : list byte) k i, (k + length bs <= length cs)%nat ->
  nth_error (upd_bytes cs k bs) i =
    if (Nat.leb k i && Nat.ltb i (k + length bs))%bool then nth_error bs (i - k) else nth_error cs i.
Proof.
  intros cs bs k i H. destruct (Nat.lt_ge_cases i (length cs)) as [Hi|Hi].
  - apply upd_bytes_nth; assumption.
  - rewrite (proj2 (nth_error_None _ i)) by (rewrite upd_bytes_length by assumption; lia).
    rewrite (proj2 (nth_error_None cs i)) by lia.
    destruct (Nat.leb_spec k i), (Nat.ltb_spec i (k + length bs)); cbn; try reflexivity; lia.
Qed.

Lemma c45r_slice_upd_other : forall (cs bs : list byte) k off len, 0 <= off -> 0 <= len ->
  (k + length bs <= length cs)%nat ->
  (off + len <= Z.of_nat k \/ Z.of_nat (k + length bs) <= off) ->
  slice (upd_bytes cs k bs) off len = slice cs off len.
Proof.
  intros cs bs k off len H0 H1 H2 H3. apply nth_error_ext. intros i.
  rewrite !c45r_slice_nth by lia. destruct (Nat.ltb_spec i (Z.to_nat len)); [|reflexivity].
  rewrite c45r_upd_nth by exact H2.
  destruct (Nat.leb_spec k (Z.to_nat off + i)), (Nat.ltb_spec (Z.to_nat off + i) (k + length bs));
    cbn; try reflexivity; lia.
Qed.

Lemma c45r_rdn_upd_other : forall (cs bs : list byte) k off n, 0 <= off -> 0 <= n ->
  (k + length bs <= length cs)%nat ->
  (off + n <= Z.of_nat k \/ Z.of_nat (k + length bs) <= off) ->
  link_spec.rdn (upd_bytes cs k bs) off n = link_spec.rdn cs off n.
Proof. intros. unfold link_spec.rdn. rewrite c45r_slice_upd_other by assumption. reflexivity. Qed.

Lemma c45r_slice_upd_same : forall (cs xs : list byte) k, (k + length xs <= length cs)%nat ->
  slice (upd_bytes cs k xs) (Z.of_nat k) (Z.of_nat (length xs)) = xs.
Proof.
  intros cs xs k H. apply nth_error_ext. intros i.
  rewrite c45r_slice_nth by lia. rewrite !Nat2Z.id.
  destruct (Nat.ltb_spec i (length xs)) as [Hi|Hi].
  - rewrite c45r_upd_nth by exact H.
    destruct (Nat.leb_spec k (k + i)), (Nat.ltb_spec (k + i) (k + length xs)); try lia.
    cbn [andb]. f_equal. lia.
  - symmetry. apply nth_error_None. exact Hi.
Qed.

Lemma c45r_rdn_upd_same4 : forall (cs : list byte) (k : Z) v, 0 <= k ->
  (Z.to_nat k + 4 <= length cs)%nat -> 0 <= v < 2 ^ 32 ->
  link_spec.rdn (upd_bytes cs (Z.to_nat k) (le4 (Z_to_bv 64 v))) k 4 = v.
Proof.
  intros cs k v Hk0 Hk Hv. unfold link_spec.rdn.
  replace (slice (upd_bytes cs (Z.to_nat k) (le4 (Z_to_bv 64 v))) k 4)
    with (slice (upd_bytes cs (Z.to_nat k) (le4 (Z_to_bv 64 v))) (Z.of_nat (Z.to_nat k))
                (Z.of_nat (length (le4 (Z_to_bv 64 v)))))
    by (rewrite Z2Nat.id, length_le4 by lia; reflexivity).
  rewrite c45r_slice_upd_same by (rewrite length_le4; lia).
  rewrite bytes_le_to_Z_le4. rewrite unsigned_lit by lia. apply Z.mod_small. lia.
Qed.

(* the kernel after `sw zero, 0x2a8(a1)` *)
Section Kbs.
Variable kbs : list byte.
Hypothesis KL : Z.of_nat (length kbs) = NK_SIZE.

Lemma c45r_kbs_len : Z.of_nat (length (c45r_kbs kbs)) = NK_SIZE.
Proof.
  unfold c45r_kbs. rewrite upd_bytes_length; [exact KL|]. rewrite length_le4.
  unfold NK_N_SENT, NK_SIZE in *. lia.
Qed.

Lemma c45r_kbs_rdn : forall off n, 0 <= off -> 0 <= n ->
  (off + n <= NK_N_SENT \/ NK_N_SENT + 4 <= off) -> link_spec.rdn (c45r_kbs kbs) off n = link_spec.rdn kbs off n.
Proof.
  intros off n H0 H1 H2. unfold c45r_kbs. apply c45r_rdn_upd_other; [lia | lia | |];
    rewrite ?length_le4; unfold NK_N_SENT, NK_SIZE in *; lia.
Qed.

Lemma c45r_kbs_n_sent : nk_n_sent (c45r_kbs kbs) = 0.
Proof.
  unfold nk_n_sent, fld_u32, c45r_kbs. apply c45r_rdn_upd_same4; [unfold NK_N_SENT; lia| |lia].
  unfold NK_N_SENT, NK_SIZE in *. lia.
Qed.

Lemma c45r_kbs_wf : nlk_wf kbs -> nlk_wf (c45r_kbs kbs).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  assert (E : forall off, 0 <= off -> (off + 4 <= NK_N_SENT \/ NK_N_SENT + 4 <= off) ->
              fld_u32 (c45r_kbs kbs) off = fld_u32 kbs off)
    by (intros off Ha Hb; unfold fld_u32; apply c45r_kbs_rdn; lia).
  pose proof c45r_kbs_n_sent as NS.
  unfold nlk_wf. unfold nk_n_chunks, nk_next, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
    nk_end_errno, nk_socket_errno, nk_send_errno in *.
  rewrite NS.
  rewrite !E by (unfold NK_N_CHUNKS, NK_NEXT, NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_END_ERRNO,
                   NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_N_IF, NK_N_SENT; lia).
  split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|].
  split; [exact H11|]. split.
  - intros j Hj. unfold fld_u64.
    rewrite c45r_kbs_rdn by (unfold NK_CHUNK_LEN, NK_N_SENT, NL_CHUNKS, NK_N_CHUNKS in *; lia).
    apply H12. exact Hj.
  - intros j Hj. lia.
Qed.

Lemma c45r_kbs_iftab : forall m tab, iftab_at m kbs tab -> iftab_at m (c45r_kbs kbs) tab.
Proof.
  intros m tab (N & L & T). split; [|split; [exact L | exact T]].
  unfold nk_n_if, fld_u32 in *. rewrite c45r_kbs_rdn by (unfold NK_N_IF, NK_N_SENT; lia). exact N.
Qed.

Lemma c45r_kbs_fld : forall off, 0 <= off -> (off + 4 <= NK_N_SENT \/ NK_N_SENT + 4 <= off) ->
  fld_u32 (c45r_kbs kbs) off = fld_u32 kbs off.
Proof. intros off H0 H1. unfold fld_u32. apply c45r_kbs_rdn; lia. Qed.
End Kbs.

(* the model after model_begin's four stores *)
Section Mbs.
Variables (mbs : list byte) (se sd : Z).
Hypothesis ML : Z.of_nat (length mbs) = MD_SIZE.

Let b1 := upd_bytes mbs (Z.to_nat 0) (le4 (Z_to_bv 64 se)).
Let b2 := upd_bytes b1 (Z.to_nat 4) (le4 (Z_to_bv 64 sd)).
Let b3 := upd_bytes b2 (Z.to_nat 8) (le4 (Z_to_bv 64 0)).

Lemma c45r_mbs_lens : length b1 = length mbs /\ length b2 = length mbs /\ length b3 = length mbs /\
  length (c45r_mbs mbs se sd) = length mbs.
Proof.
  assert (L1 : length b1 = length mbs)
    by (unfold b1; apply upd_bytes_length; rewrite length_le4; unfold MD_SIZE in ML; lia).
  assert (L2 : length b2 = length mbs)
    by (unfold b2; rewrite upd_bytes_length; [exact L1 | rewrite L1, length_le4; unfold MD_SIZE in ML; lia]).
  assert (L3 : length b3 = length mbs)
    by (unfold b3; rewrite upd_bytes_length; [exact L2 | rewrite L2, length_le4; unfold MD_SIZE in ML; lia]).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  unfold c45r_mbs. fold b1 b2 b3. rewrite upd_bytes_length; [exact L3|].
  rewrite L3, length_le4. unfold MD_SIZE, MD_N_REQ in *. lia.
Qed.

Lemma c45r_mbs_len : Z.of_nat (length (c45r_mbs mbs se sd)) = MD_SIZE.
Proof. destruct c45r_mbs_lens as (_ & _ & _ & L). rewrite L. exact ML. Qed.

Lemma c45r_mbs_slice : forall off n, 12 <= off -> 0 <= n -> (off + n <= MD_N_REQ \/ MD_N_REQ + 4 <= off) ->
  slice (c45r_mbs mbs se sd) off n = slice mbs off n.
Proof.
  intros off n H0 H1 H2. destruct c45r_mbs_lens as (L1 & L2 & L3 & _).
  unfold c45r_mbs. fold b1 b2 b3.
  rewrite c45r_slice_upd_other; [| lia | lia | rewrite L3, length_le4; unfold MD_SIZE, MD_N_REQ in *; lia
                                 | rewrite length_le4; unfold MD_N_REQ in *; lia].
  unfold b3. rewrite c45r_slice_upd_other; [| lia | lia | fold b2; rewrite L2, length_le4; unfold MD_SIZE in *; lia
                                            | rewrite length_le4; cbn; lia].
  unfold b2. rewrite c45r_slice_upd_other; [| lia | lia | fold b1; rewrite L1, length_le4; unfold MD_SIZE in *; lia
                                            | rewrite length_le4; cbn; lia].
  unfold b1. rewrite c45r_slice_upd_other; [reflexivity | lia | lia | rewrite length_le4; unfold MD_SIZE in *; lia
                                           | rewrite length_le4; cbn; lia].
Qed.

Lemma c45r_mbs_n_req : md_n_req (c45r_mbs mbs se sd) = 0.
Proof.
  destruct c45r_mbs_lens as (L1 & L2 & L3 & _).
  unfold md_n_req, fld_u32, c45r_mbs. fold b1 b2 b3.
  apply c45r_rdn_upd_same4; [unfold MD_N_REQ; lia | rewrite L3; unfold MD_SIZE, MD_N_REQ in *; lia | lia].
Qed.

Lemma c45r_mbs_next : md_next (c45r_mbs mbs se sd) = 0.
Proof.
  destruct c45r_mbs_lens as (L1 & L2 & L3 & _).
  unfold md_next, fld_u32, c45r_mbs. fold b1 b2 b3.
  rewrite c45r_rdn_upd_other; [| unfold MD_NEXT; lia | lia | rewrite L3, length_le4; unfold MD_SIZE, MD_N_REQ in *; lia
                              | rewrite length_le4; unfold MD_NEXT, MD_N_REQ; lia].
  unfold b3. apply c45r_rdn_upd_same4; [unfold MD_NEXT; lia | fold b2; rewrite L2; unfold MD_NEXT, MD_SIZE in *; lia | lia].
Qed.

Lemma c45r_mbs_send : 0 <= sd < 2 ^ 32 -> md_send_errno (c45r_mbs mbs se sd) = sd.
Proof.
  intros Hsd. destruct c45r_mbs_lens as (L1 & L2 & L3 & _).
  unfold md_send_errno, fld_u32, c45r_mbs. fold b1 b2 b3.
  rewrite c45r_rdn_upd_other; [| unfold MD_SEND_ERRNO; lia | lia
                              | rewrite L3, length_le4; unfold MD_SIZE, MD_N_REQ in *; lia
                              | rewrite length_le4; unfold MD_SEND_ERRNO, MD_N_REQ; lia].
  unfold b3. rewrite c45r_rdn_upd_other; [| unfold MD_SEND_ERRNO; lia | lia
                                         | fold b2; rewrite L2, length_le4; unfold MD_SIZE in *; lia
                                         | rewrite length_le4; unfold MD_SEND_ERRNO; cbn; lia].
  unfold b2. apply c45r_rdn_upd_same4;
    [unfold MD_SEND_ERRNO; lia | fold b1; rewrite L1; unfold MD_SEND_ERRNO, MD_SIZE in *; lia | exact Hsd].
Qed.

Lemma c45r_mbs_sock : 0 <= se < 2 ^ 32 -> md_socket_errno (c45r_mbs mbs se sd) = se.
Proof.
  intros Hse. destruct c45r_mbs_lens as (L1 & L2 & L3 & _).
  unfold md_socket_errno, fld_u32, c45r_mbs. fold b1 b2 b3.
  rewrite c45r_rdn_upd_other; [| unfold MD_SOCKET_ERRNO; lia | lia
                              | rewrite L3, length_le4; unfold MD_SIZE, MD_N_REQ in *; lia
                              | rewrite length_le4; unfold MD_SOCKET_ERRNO, MD_N_REQ; lia].
  unfold b3. rewrite c45r_rdn_upd_other; [| unfold MD_SOCKET_ERRNO; lia | lia
                                         | fold b2; rewrite L2, length_le4; unfold MD_SIZE in *; lia
                                         | rewrite length_le4; unfold MD_SOCKET_ERRNO; cbn; lia].
  unfold b2. rewrite c45r_rdn_upd_other; [| unfold MD_SOCKET_ERRNO; lia | lia
                                         | fold b1; rewrite L1, length_le4; unfold MD_SIZE in *; lia
                                         | rewrite length_le4; unfold MD_SOCKET_ERRNO; cbn; lia].
  unfold b1. apply c45r_rdn_upd_same4;
    [unfold MD_SOCKET_ERRNO; lia | unfold MD_SOCKET_ERRNO, MD_SIZE in *; lia | exact Hse].
Qed.

Lemma c45r_mbs_n_mark : md_n_mark (c45r_mbs mbs se sd) = md_n_mark mbs.
Proof.
  unfold md_n_mark, fld_u32, link_spec.rdn. rewrite c45r_mbs_slice; [reflexivity | unfold MD_N_MARK; lia | lia |].
  unfold MD_N_MARK, MD_N_REQ; lia.
Qed.

Lemma c45r_mbs_mark_slice : forall j, 0 <= j < MARKS_MAX ->
  slice (c45r_mbs mbs se sd) (MD_MARK + MARK_LEN * j) MARK_LEN = slice mbs (MD_MARK + MARK_LEN * j) MARK_LEN.
Proof.
  intros j Hj. apply c45r_mbs_slice; unfold MD_MARK, MARK_LEN, MD_N_REQ, MARKS_MAX in *; lia.
Qed.

Lemma c45r_mbs_marks : model_marks_wf mbs -> md_marks (c45r_mbs mbs se sd) = md_marks mbs.
Proof.
  intros (Hn & _). unfold md_marks. rewrite c45r_mbs_n_mark. apply map_ext_in. intros a Ha.
  apply in_seq in Ha. rewrite c45r_mbs_mark_slice; [reflexivity|]. lia.
Qed.

Lemma c45r_mbs_wf : model_wf mbs -> 0 <= se < 2 ^ 31 -> 0 <= sd < 2 ^ 31 -> model_wf (c45r_mbs mbs se sd).
Proof.
  intros (_ & _ & _ & _ & _ & (Hn & T)) Hse Hsd. unfold model_wf.
  rewrite c45r_mbs_n_req, c45r_mbs_next, c45r_mbs_sock, c45r_mbs_send by lia.
  split; [unfold NL_SENT_MAX; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros j Hj; lia|].
  unfold model_marks_wf. rewrite c45r_mbs_n_mark. split; [exact Hn|].
  intros j Hj. rewrite c45r_mbs_mark_slice by lia. exact (T j Hj).
Qed.

Lemma c45r_mbs_are : forall gbs, model_wf mbs -> marks_are gbs mbs -> marks_are gbs (c45r_mbs mbs se sd).
Proof.
  intros gbs (_ & _ & _ & _ & _ & MW) (E1 & E2). split.
  - rewrite c45r_mbs_n_mark. exact E1.
  - rewrite c45r_mbs_marks by exact MW. exact E2.
Qed.
End Mbs.
