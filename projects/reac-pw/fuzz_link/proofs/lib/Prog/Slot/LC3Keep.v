(* The op_unmark arm (c3), plain image: the memory views lh_mem keeps (g_names, odd, the policy strings,
   long_alias, texts, the if_name pointers, the interface table, the guard, the payload), each carried
   across a write set W that keeps clear of it (munch). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC3Lib.
Local Open Scope Z_scope.

Lemma c3_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' ->
  disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n a' n' H H1 H2 H3; [exact I|].
  destruct H as [H4 H5]. split; [lia | exact (IH a n a' n' H5 H1 H2 H3)].
Qed.

Lemma c3_cstr_tr : forall W m m' a s, cstr_at m a s -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length s) + 1) -> cstr_at m' a s.
Proof.
  intros W m m' a s [HB HN] MU D. split; [|exact HN].
  eapply (bytes_at_transport rsegs); [exact HB | exact MU |]. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add.
  exact D.
Qed.

Lemma c3_u64_tr : forall W m m' a v, u64_at m a v -> munch W m m' -> disjoint_from W a 8 -> u64_at m' a v.
Proof.
  intros W m m' a v H MU D. unfold u64_at in *.
  eapply (bytes_at_transport rsegs); [exact H | exact MU |]. rewrite length_le8. exact D.
Qed.

Lemma c3_u32_tr : forall W m m' a v, u32_at m a v -> munch W m m' -> disjoint_from W a 4 -> u32_at m' a v.
Proof.
  intros W m m' a v H MU D. unfold u32_at in *.
  eapply (bytes_at_transport rsegs); [exact H | exact MU |]. rewrite length_le4. exact D.
Qed.

Lemma c3_gnames_tr : forall W m m', gnames_at m -> munch W m m' -> disjoint_from W A_G_NAMES G_NAMES_SIZE ->
  gnames_at m'.
Proof.
  intros W m m' H MU D k Hk. destruct (H k Hk) as (rest & HB & HL). exists rest. split; [|exact HL].
  eapply (bytes_at_transport rsegs); [exact HB | exact MU |]. rewrite HL.
  eapply c3_dj_sub; [exact D | | |]; unfold G_NAMES_SIZE; lia.
Qed.

Lemma c3_odd_home : forall i, (i < 6)%nat ->
  0x10000 <= nth i odd_ptrs 0 /\ nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x12000.
Proof.
  intros i Hi. do 6 (destruct i as [|i]; [cbn; lia|]). lia.
Qed.

Lemma c3_odd_tr : forall W m m', odd_at m -> munch W m m' -> disjoint_from W A_ODD 48 ->
  disjoint_from W 0x10000 0x2000 -> odd_at m'.
Proof.
  intros W m m' H MU D1 D2 i Hi. destruct (H i Hi) as [Hu Hc]. pose proof (c3_odd_home i Hi) as Hh.
  split.
  - eapply c3_u64_tr; [exact Hu | exact MU |]. eapply c3_dj_sub; [exact D1 | | |]; unfold A_ODD; lia.
  - eapply c3_cstr_tr; [exact Hc | exact MU |]. eapply c3_dj_sub; [exact D2 | | |]; lia.
Qed.

Lemma c3_policy_tr : forall W m m', policy_ro m -> munch W m m' -> disjoint_from W 0x10000 0x2000 -> policy_ro m'.
Proof.
  intros W m m' (H1 & H2 & H3 & H4) MU D.
  split; [|split; [|split]]; (eapply c3_cstr_tr; [eassumption | exact MU |]); eapply c3_dj_sub; try exact D;
    unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY; cbn [length S_PREFIX S_SERVED S_VLAN map]; lia.
Qed.

Lemma c3_la_tr : forall W m m', la_ok m -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W A_LONG_ALIAS (LONG_ALIAS_SIZE + 3) -> la_ok m'.
Proof.
  intros W m m' (la & sl & HC & HB & HL) MU WM D. exists la, sl. split; [|split; [|exact HL]].
  - eapply (rw_cells_transport rsegs); [exact HC | exact MU | exact WM |].
    cbn [cells_size csize]. eapply c3_dj_sub; [exact D | | |]; unfold LONG_ALIAS_SIZE; lia.
  - eapply (bytes_at_transport rsegs); [exact HB | exact MU |]. rewrite HL.
    eapply c3_dj_sub; [exact D | | |]; unfold LONG_ALIAS_SIZE; lia.
Qed.

Lemma c3_texts_tr : forall W m m', texts_at m -> munch W m m' -> disjoint_from W A_TEXTS 88 -> texts_at m'.
Proof.
  intros W m m' H MU D i Hi. eapply c3_u64_tr; [exact (H i Hi) | exact MU |].
  eapply c3_dj_sub; [exact D | | |]; lia.
Qed.

Lemma c3_ifptrs_tr : forall W m m', ifptrs_at m -> munch W m m' -> disjoint_from W (A_G_NL + NK_IF_NAME) 512 ->
  ifptrs_at m'.
Proof.
  intros W m m' H MU D i Hi. eapply c3_u64_tr; [exact (H i Hi) | exact MU |].
  eapply c3_dj_sub; [exact D | | |]; lia.
Qed.

Lemma c3_guard_tr : forall W m m', guard_m m -> munch W m m' -> disjoint_from W A_GOT_GUARD_S 8 ->
  disjoint_from W A_GUARD_S 8 -> guard_m m'.
Proof.
  intros W m m' (H1 & c & H2) MU D1 D2. split.
  - eapply (bytes_at_transport rsegs); [exact H1 | exact MU |]. rewrite length_le8. exact D1.
  - exists c. eapply (bytes_at_transport rsegs); [exact H2 | exact MU |]. rewrite length_le8. exact D2.
Qed.

Lemma c3_cursor_tr : forall W m m' p0 pl P N, cursor_ok m p0 pl P N -> munch W m m' ->
  disjoint_from W p0 (Z.of_nat (length pl)) -> cursor_ok m' p0 pl P N.
Proof.
  intros W m m' p0 pl P N (HB & HK) MU D. split; [|exact HK].
  eapply (bytes_at_transport rsegs); [exact HB | exact MU | exact D].
Qed.

(* where the interface table's names live: g_names for the 60 kept k, .rodata for odd[1..4] *)
Lemma c3_link_tab_home : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  (i < 64)%nat /\
  ((A_G_NAMES <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <= A_G_NAMES + G_NAMES_SIZE) \/
   (0x10000 <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <= 0x12000)).
Proof.
  intros i nm ix H.
  assert (C : forallb (fun i => match nth_error link_tab i with
      | Some (nm, _) => let q := nth i link_ptrs 0 in
          ((A_G_NAMES <=? q) && (q + Z.of_nat (length nm) + 1 <=? A_G_NAMES + G_NAMES_SIZE)) ||
          ((65536 <=? q) && (q + Z.of_nat (length nm) + 1 <=? 73728))
      | None => false end) (seq 0 64) = true) by (vm_compute; reflexivity).
  assert (L : length link_tab = 64%nat) by (vm_compute; reflexivity).
  assert (Hi : (i < 64)%nat).
  { rewrite <- L. apply nth_error_Some. rewrite H. discriminate. }
  split; [exact Hi|].
  rewrite forallb_forall in C. specialize (C i (proj2 (in_seq 64 0 i) (conj (Nat.le_0_l i) Hi))).
  rewrite H in C. cbv zeta in C.
  apply orb_prop in C as [C|C]; apply andb_prop in C as [C1 C2]; apply Z.leb_le in C1; apply Z.leb_le in C2;
    [left|right]; split; assumption.
Qed.

(* the pointer an iftab_at entry names is the one interfaces() stored (ifptrs_at) *)
Lemma c3_iftab_ptr : forall m kbs tab i nm ix p q, iftab_at m kbs tab -> nth_error tab i = Some (nm, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) q ->
  0 <= q < 2 ^ 64 -> cstr_at m p nm -> p = q.
Proof.
  intros m kbs tab i nm ix p q _ _ Hp Hq Bq Hc. unfold u64_at in Hp, Hq.
  pose proof (c3_bytes_at_same _ _ _ _ Hp Hq ltac:(rewrite !length_le8; reflexivity)) as E.
  apply c3_le8_inj in E. destruct Hc as [Hcb _]. pose proof (bytes_at_bound rsegs _ _ _ Hcb) as Bp.
  rewrite length_app in Bp. cbn [length] in Bp.
  unfold wz in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

Lemma c3_link_ptr_range : forall i, (i < 64)%nat -> 0x10000 <= nth i link_ptrs 0 < A_G_NAMES + G_NAMES_SIZE.
Proof.
  intros i Hi.
  assert (C : forallb (fun i => (65536 <=? nth i link_ptrs 0) && (nth i link_ptrs 0 <? A_G_NAMES + G_NAMES_SIZE))
                (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C i (proj2 (in_seq 64 0 i) (conj (Nat.le_0_l i) Hi))).
  apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia.
Qed.

Lemma c3_iftab_tr : forall W m m' kbs kbs',
  iftab_at m kbs link_tab -> ifptrs_at m -> munch W m m' -> nk_n_if kbs' = nk_n_if kbs ->
  disjoint_from W (A_G_NL + NK_IF_NAME) 512 -> disjoint_from W (A_G_NL + NK_IF_INDEX) 256 ->
  disjoint_from W A_G_NAMES G_NAMES_SIZE -> disjoint_from W 0x10000 0x2000 ->
  iftab_at m' kbs' link_tab.
Proof.
  intros W m m' kbs kbs' HT HP MU En D1 D2 D3 D4.
  pose proof HT as (H1 & H2 & H3).
  split; [rewrite En; exact H1|]. split; [exact H2|].
  intros i nm ix Hn. destruct (H3 i nm ix Hn) as (Hix & p & Hu & Hp0 & Hc & Hx).
  destruct (c3_link_tab_home i nm ix Hn) as (Hi & Hhome).
  pose proof (c3_link_ptr_range i Hi) as Rq.
  assert (Ep : p = nth i link_ptrs 0)
    by (exact (c3_iftab_ptr m kbs link_tab i nm ix p _ HT Hn Hu (HP i Hi) ltac:(unfold A_G_NAMES, G_NAMES_SIZE in Rq; lia) Hc)).
  subst p.
  split; [exact Hix|]. exists (nth i link_ptrs 0).
  split; [eapply c3_u64_tr; [exact Hu | exact MU |]; eapply c3_dj_sub; [exact D1 | | |]; lia|].
  split; [exact Hp0|].
  split; [eapply c3_cstr_tr; [exact Hc | exact MU |]; destruct Hhome as [Hh|Hh];
          [eapply c3_dj_sub; [exact D3 | | |]; lia | eapply c3_dj_sub; [exact D4 | | |]; lia]|].
  eapply c3_u32_tr; [exact Hx | exact MU |]. eapply c3_dj_sub; [exact D2 | | |]; lia.
Qed.
