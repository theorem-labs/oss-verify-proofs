(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 326 of its 382 lines of code are new or changed and 197 lines of the source are left out. *)
(* Arms 4 and 5 of the slot's loop, piece `com` (link/sl/briefs/C45-PIECES.md): the lemmas the dispatch
   and the tail use, and that the arms' other segments can use too.
   - c45_seg_fp_refl / c45_seg_fp_trans: LDefs' seg_fp is a preorder.
   - transport of the cuts' memory views (c45_keep, c45_kmg, task_mem) across a step whose footprint W
     lies at or above S - 65536 (the slot's stack window): every region those views name is in the image
     (below 0x960e0) or in a heap block below S - 65536 (lenv_ok, blk_out).
   - the frame: lh_cells as LC45Defs' four pieces (c45_ptrs, the cursor, the two buffers), and the whole
     376 bytes as one CB (ex_ms). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC45Defs.
Local Open Scope Z_scope.

(* ==========================================================================
   1. seg_fp
   ========================================================================== *)

Lemma c45c_outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma c45c_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi).
  - right. intros [H1 _]. lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

Lemma c45_seg_fp_refl : forall S hp m, seg_fp S hp m m.
Proof.
  intros S hp m. exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
  intros x _ H. exfalso. apply H. exact I.
Qed.

Lemma c45_seg_fp_trans : forall S hp m1 m2 m3, seg_fp S hp m1 m2 -> seg_fp S hp m2 m3 -> seg_fp S hp m1 m3.
Proof.
  intros S hp m1 m2 m3 (W1 & M1 & V1 & O1) (W2 & M2 & V2 & O2).
  exists (W1 ++ W2). split; [|split].
  - intros x Hx. apply c45c_outside_app in Hx. destruct Hx as [H1 H2]. rewrite (M2 x H2). exact (M1 x H1).
  - eapply wmono_trans; eassumption.
  - intros x Hr Hx. destruct (c45c_outside_dec W1 x) as [H1|H1].
    + apply O2; [exact Hr|]. intros H2. apply Hx. apply c45c_outside_app. split; assumption.
    + apply O1; assumption.
Qed.

(* a step whose footprint lies in the stack window *)
Lemma c45c_seg_fp_stack : forall S hp W m m', munch W m m' -> wmono rsegs m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> S - SLOT_STACK_Z <= x < S) -> seg_fp S hp m m'.
Proof. intros S hp W m m' MU WM HW. exists W. split; [exact MU|]. split; [exact WM|]. intros x Hx Ho. left. auto. Qed.

Lemma c45c_not_outside1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x H. cbn in H. destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); try lia;
    exfalso; apply H; split; try lia; exact I.
Qed.

Lemma c45c_disj1 : forall lo hi L, L <= lo -> disjoint_from [(lo, hi)] 0 L.
Proof. intros lo hi L H. cbn. split; [lia | exact I]. Qed.

(* ==========================================================================
   2. Transport across a footprint W at or above L
   ========================================================================== *)

Lemma c45c_disj_below : forall W L a n, disjoint_from W 0 L -> 0 <= a -> 0 <= n -> a + n <= L ->
  disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros L a n H Ha Hn Hl; [exact I|].
  destruct H as [H1 H2]. split; [lia | eapply IH; eauto].
Qed.

Lemma c45c_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma c45c_list_ext : forall (l1 l2 : list byte), length l1 = length l2 ->
  (forall i, (i < length l1)%nat -> nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] HL H; cbn in HL; try discriminate; [reflexivity|].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as ->. f_equal.
  apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

(* two byte lists of one length at one address are the same *)
Lemma c45c_bytes_at_det : forall m a l1 l2, bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) HL. apply c45c_list_ext; [exact HL|].
  intros i Hi. rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
Qed.

Lemma c45c_u64_same : forall m a p q, u64_at m a p -> u64_at m a q -> wz p = wz q.
Proof.
  intros m a p q Hp Hq. unfold u64_at in *.
  pose proof (c45c_bytes_at_det m a _ _ Hp Hq ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 (wz p)), <- (le_bytes_to_word_le8 (wz q)), E. reflexivity.
Qed.

Section Tr.
Variables (W : list ivl) (L : Z) (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono rsegs m m'.
Hypothesis DL : disjoint_from W 0 L.

Lemma c45c_tr_bytes : forall a bs, bytes_at rsegs m a bs -> a + Z.of_nat (length bs) <= L ->
  bytes_at rsegs m' a bs.
Proof.
  intros a bs H Hl. pose proof (bytes_at_bound _ _ _ _ H) as B.
  eapply bytes_at_transport; [exact H | exact MU | apply (c45c_disj_below W L _ _ DL); lia].
Qed.

Lemma c45c_tr_cstr : forall a s, cstr_at m a s -> a + Z.of_nat (length s) + 1 <= L -> cstr_at m' a s.
Proof.
  intros a s [H1 H2] Hl. split; [|exact H2]. apply c45c_tr_bytes; [exact H1|].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma c45c_tr_u64 : forall a v, u64_at m a v -> a + 8 <= L -> u64_at m' a v.
Proof. intros a v H Hl. unfold u64_at in *. apply c45c_tr_bytes; [exact H|]. rewrite length_le8. lia. Qed.

Lemma c45c_tr_u32 : forall a v, u32_at m a v -> a + 4 <= L -> u32_at m' a v.
Proof. intros a v H Hl. unfold u32_at in *. apply c45c_tr_bytes; [exact H|]. rewrite length_le4. lia. Qed.

Lemma c45c_tr_u8arr : forall a bs, u8arr rsegs m a bs -> a + Z.of_nat (length bs) <= L -> u8arr rsegs m' a bs.
Proof.
  intros a bs H Hl. pose proof (u8arr_bound _ _ _ _ H) as B.
  eapply u8arr_transport; [exact H | exact MU | exact WM | apply (c45c_disj_below W L _ _ DL); lia].
Qed.

Lemma c45c_tr_rw : forall a cs, rw_cells rsegs m a cs -> a + Z.of_nat (cells_size cs) <= L ->
  rw_cells rsegs m' a cs.
Proof.
  intros a cs H Hl. pose proof (rw_cells_bound _ _ _ _ H) as B.
  eapply rw_cells_transport; [exact H | exact MU | exact WM | apply (c45c_disj_below W L _ _ DL); lia].
Qed.

Lemma c45c_tr_wr : forall a n, wr_at rsegs m a n -> wr_at rsegs m' a n.
Proof. intros a n H. eapply wr_at_transport; [exact H | exact WM]. Qed.

(* the views over the image *)
Hypothesis HL : 0x960e0 <= L.

Lemma c45c_tr_gnames : gnames_at m -> gnames_at m'.
Proof.
  intros H k Hk. destruct (H k Hk) as (rest & B & Len). exists rest. split; [|exact Len].
  apply c45c_tr_bytes; [exact B|]. rewrite Len. unfold A_G_NAMES. lia.
Qed.

Lemma c45c_odd_bound : forall i, (i < 6)%nat ->
  0 <= nth i odd_ptrs 0 /\ nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= 0x960e0.
Proof.
  intros i Hi. do 6 (destruct i as [|i]; [split; apply Z.leb_le; vm_compute; reflexivity|]). lia.
Qed.

Lemma c45c_tr_odd : odd_at m -> odd_at m'.
Proof.
  intros H i Hi. destruct (H i Hi) as [U C]. pose proof (c45c_odd_bound i Hi) as B. split.
  - apply c45c_tr_u64; [exact U|]. unfold A_ODD. lia.
  - apply c45c_tr_cstr; [exact C | lia].
Qed.

Lemma c45c_tr_policy : policy_ro m -> policy_ro m'.
Proof.
  intros (C1 & C2 & C3 & C4).
  assert (L1 : length S_PREFIX = 8%nat) by reflexivity.
  assert (L2 : length S_SERVED = 14%nat) by reflexivity.
  assert (L3 : length S_VLAN = 4%nat) by reflexivity.
  split; [|split; [|split]]; (apply c45c_tr_cstr; [eassumption|]).
  - rewrite L1. unfold A_PREFIX. lia.
  - rewrite L2. unfold A_SERVED. lia.
  - rewrite L3. unfold A_VLAN. lia.
  - cbn [length]. unfold A_EMPTY. lia.
Qed.

Lemma c45c_tr_la : la_ok m -> la_ok m'.
Proof.
  intros (la & sl & R & B & Ls). exists la, sl. split; [|split; [|exact Ls]].
  - apply c45c_tr_rw; [exact R|]. change (cells_size [CB (Z.to_nat 300) la; C1 (zb 0)]) with 301%nat.
    unfold A_LONG_ALIAS. lia.
  - apply c45c_tr_bytes; [exact B|]. rewrite Ls. unfold A_LONG_ALIAS, LONG_ALIAS_SIZE. lia.
Qed.

Lemma c45c_tr_texts : texts_at m -> texts_at m'.
Proof. intros H i Hi. apply c45c_tr_u64; [exact (H i Hi)|]. unfold A_TEXTS. lia. Qed.

Lemma c45c_tr_ifptrs : ifptrs_at m -> ifptrs_at m'.
Proof. intros H i Hi. apply c45c_tr_u64; [exact (H i Hi)|]. unfold A_G_NL, NK_IF_NAME. lia. Qed.

Lemma c45c_tr_guard : guard_m m -> guard_m m'.
Proof.
  intros (G1 & c & G2). split; [|exists c].
  - apply c45c_tr_bytes; [exact G1|]. rewrite length_le8. unfold A_GOT_GUARD_S. lia.
  - apply c45c_tr_bytes; [exact G2|]. rewrite length_le8. unfold A_GUARD_S. lia.
Qed.

Lemma c45c_tr_nlk : forall kbs, nlk_at m kbs -> nlk_at m' kbs.
Proof.
  intros kbs (U & Ln). split; [|exact Ln]. apply c45c_tr_u8arr; [exact U|]. rewrite Ln.
  unfold A_G_NL, NK_SIZE. lia.
Qed.

(* the interface table: each name pointer is the one ifptrs_at fixes, a string of the image *)
Definition c45c_ltab_ok : bool :=
  forallb (fun i => match nth_error link_tab i with
                    | Some (nm, _) => (0 <=? nth i link_ptrs 0) &&
                                      (nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <=? 0x960e0)
                    | None => true
                    end) (seq 0 64).

Lemma c45c_ltab_ok_true : c45c_ltab_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma c45c_link_tab_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma c45c_ltab_bound : forall i nm ix, nth_error link_tab i = Some (nm, ix) ->
  (i < 64)%nat /\ 0 <= nth i link_ptrs 0 /\ nth i link_ptrs 0 + Z.of_nat (length nm) + 1 <= 0x960e0.
Proof.
  intros i nm ix Hn.
  assert (Hi : (i < length link_tab)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  rewrite c45c_link_tab_len in Hi.
  pose proof c45c_ltab_ok_true as T. unfold c45c_ltab_ok in T. rewrite forallb_forall in T.
  specialize (T i ltac:(apply in_seq; lia)). cbv beta in T. rewrite Hn in T.
  apply andb_true_iff in T as [T1 T2]. apply Z.leb_le in T1. apply Z.leb_le in T2. lia.
Qed.

Lemma c45c_tr_iftab : forall kbs, ifptrs_at m -> iftab_at m kbs link_tab -> iftab_at m' kbs link_tab.
Proof.
  intros kbs HP (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i nm ix Hn. destruct (H3 i nm ix Hn) as (Hix & p & U & Pz & C & U32). split; [exact Hix|].
  destruct (c45c_ltab_bound i nm ix Hn) as (Hi & Q0 & QB).
  pose proof (HP i Hi) as UQ.
  assert (Pr : 0 <= p < 2 ^ 64).
  { destruct C as [CB _]. pose proof (bytes_at_bound _ _ _ _ CB) as BB. rewrite length_app in BB.
    cbn [length] in BB. lia. }
  assert (Ep : p = nth i link_ptrs 0).
  { pose proof (c45c_u64_same _ _ _ _ U UQ) as E. apply (f_equal bv_unsigned) in E. unfold wz in E.
    rewrite !unsigned_lit in E by lia. exact E. }
  exists p. split; [|split; [exact Pz|split]].
  - apply c45c_tr_u64; [exact U|]. unfold A_G_NL, NK_IF_NAME. lia.
  - apply c45c_tr_cstr; [exact C|]. lia.
  - apply c45c_tr_u32; [exact U32|]. unfold A_G_NL, NK_IF_INDEX. lia.
Qed.

End Tr.

Lemma c45c_tr_keep : forall E W m m', lenv_ok E -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W 0 (e_S E - SLOT_STACK_Z) -> c45_keep E m -> c45_keep E m'.
Proof.
  intros E W m m' HE MU WM DL (G & O & PR & LA & TX & IP & ER & GD & PL).
  destruct HE as (HS1 & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HP & _) & _).
  assert (HL : 0x960e0 <= e_S E - SLOT_STACK_Z) by lia.
  split; [exact (c45c_tr_gnames W _ m m' MU DL HL G)|].
  split; [exact (c45c_tr_odd W _ m m' MU DL HL O)|].
  split; [exact (c45c_tr_policy W _ m m' MU DL HL PR)|].
  split; [exact (c45c_tr_la W _ m m' MU WM DL HL LA)|].
  split; [exact (c45c_tr_texts W _ m m' MU DL HL TX)|].
  split; [exact (c45c_tr_ifptrs W _ m m' MU DL HL IP)|].
  split; [exact (c45c_tr_wr m m' WM _ _ ER)|].
  split; [exact (c45c_tr_guard W _ m m' MU DL HL GD)|].
  exact (c45c_tr_bytes W _ m m' MU DL _ _ PL HP).
Qed.

Lemma c45c_tr_kmg : forall E i kbs mbs gbs W m m', lenv_ok E -> munch W m m' -> wmono rsegs m m' ->
  disjoint_from W 0 (e_S E - SLOT_STACK_Z) -> c45_keep E m -> c45_kmg E i kbs mbs gbs m ->
  c45_kmg E i kbs mbs gbs m'.
Proof.
  intros E i kbs mbs gbs W m m' HE MU WM DL KP (NK & NW & IT & O1 & O2 & O3 & O4 & MD & MW & MK & KW & KA).
  destruct KP as (_ & _ & _ & _ & _ & IP & _).
  destruct HE as (HS1 & _ & _ & (_ & HMD & _) & (_ & HMK & _) & _).
  assert (HL : 0x960e0 <= e_S E - SLOT_STACK_Z) by lia.
  split; [exact (c45c_tr_nlk W _ m m' MU WM DL HL kbs NK)|]. split; [exact NW|].
  split; [exact (c45c_tr_iftab W _ m m' MU DL HL kbs IP IT)|].
  do 4 (split; [assumption|]).
  split; [destruct MD as [MU8 ML]; split; [|exact ML]; apply (c45c_tr_u8arr W _ m m' MU WM DL);
          [exact MU8 | rewrite ML; exact HMD]|].
  split; [exact MW|].
  split; [destruct MK as [MU8 ML]; split; [|exact ML]; apply (c45c_tr_u8arr W _ m m' MU WM DL);
          [exact MU8 | rewrite ML; exact HMK]|].
  split; [exact KW | exact KA].
Qed.

Lemma c45c_tr_task : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> x < 2 ^ 47) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU HW a b Ha. destruct (c45c_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - rewrite (MU a Ho) in Ha. exact (T a b Ha).
  - right. assert (TS : 2 ^ 47 <= TASK_SIZE) by (apply Z.leb_le; vm_compute; reflexivity).
    pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R.
    pose proof (HW (bv_unsigned a) ltac:(cbn in R; lia) Ho). lia.
Qed.

(* ==========================================================================
   3. The frame
   ========================================================================== *)

Lemma c45c_wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m a (n1 + n2) <-> wr_at rsegs m a n1 /\ wr_at rsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma c45c_rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite c45c_wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma c45c_lh_cells_eq : forall E P N j0 j1 j2,
  lh_cells (e_md E) (e_mk E) P N j0 j1 j2 =
  c45_ptrs E j0 ++ [C8 (wz P); C8 (wz N)] ++ [CB 40 j1] ++ [CB 256 j2].
Proof. reflexivity. Qed.

Lemma c45c_frame_split : forall E m P N j0 j1 j2,
  rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P N j0 j1 j2) ->
  rw_cells rsegs m (c45_sp E) (c45_ptrs E j0) /\
  rw_cells rsegs m (c45_sp E + FO_P) [C8 (wz P); C8 (wz N)] /\
  rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] /\
  rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2].
Proof.
  intros E m P N j0 j1 j2 H. rewrite c45c_lh_cells_eq in H. unfold c45_sp.
  apply c45c_rw_cells_app in H. destruct H as [H1 H]. apply c45c_rw_cells_app in H. destruct H as [H2 H].
  apply c45c_rw_cells_app in H. destruct H as [H3 H4].
  change (cells_size (c45_ptrs E j0)) with 64%nat in H2, H3, H4.
  change (cells_size [C8 (wz P); C8 (wz N)]) with 16%nat in H3, H4.
  change (cells_size [CB 40 j1]) with 40%nat in H4.
  split; [exact H1|]. split; [exact H2|]. split.
  - replace (e_S E - SLOT_FRAME + FO_B40) with (e_S E - SLOT_FRAME + Z.of_nat 64 + Z.of_nat 16)
      by (unfold FO_B40; lia). exact H3.
  - replace (e_S E - SLOT_FRAME + FO_B256) with (e_S E - SLOT_FRAME + Z.of_nat 64 + Z.of_nat 16 + Z.of_nat 40)
      by (unfold FO_B256; lia). exact H4.
Qed.

Lemma c45c_frame_merge : forall E m P N j0 j1 j2,
  rw_cells rsegs m (c45_sp E) (c45_ptrs E j0) ->
  rw_cells rsegs m (c45_sp E + FO_P) [C8 (wz P); C8 (wz N)] ->
  rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] ->
  rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] ->
  rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P N j0 j1 j2).
Proof.
  intros E m P N j0 j1 j2 H1 H2 H3 H4. rewrite c45c_lh_cells_eq. unfold c45_sp in *.
  apply c45c_rw_cells_app. split; [exact H1|].
  change (cells_size (c45_ptrs E j0)) with 64%nat.
  apply c45c_rw_cells_app. split; [exact H2|].
  change (cells_size [C8 (wz P); C8 (wz N)]) with 16%nat.
  apply c45c_rw_cells_app. split.
  - replace (e_S E - SLOT_FRAME + Z.of_nat 64 + Z.of_nat 16) with (e_S E - SLOT_FRAME + FO_B40)
      by (unfold FO_B40; lia). exact H3.
  - change (cells_size [CB 40 j1]) with 40%nat.
    replace (e_S E - SLOT_FRAME + Z.of_nat 64 + Z.of_nat 16 + Z.of_nat 40) with (e_S E - SLOT_FRAME + FO_B256)
      by (unfold FO_B256; lia). exact H4.
Qed.

(* the 376 bytes below the saved registers as one block (ex_ms) *)
Lemma c45c_frame376 : forall E m cs, rw_cells rsegs m (e_S E - SLOT_FRAME) cs -> cells_size cs = 376%nat ->
  exists j, rw_cells rsegs m (e_S E - SLOT_FRAME) [CB 376 j].
Proof.
  intros E m cs H Hs. exists (cells_bytes cs).
  pose proof (rw_cells_merge rsegs m (e_S E - SLOT_FRAME) [] cs [] ) as M.
  rewrite app_nil_r in M. cbn [app] in M. rewrite Hs in M. exact (M H).
Qed.

(* ==========================================================================
   4. From the end of an arm to the next loop head's memory
   ========================================================================== *)

Lemma c45c_lh_mem_of : forall E i P N kbs mbs gbs j0 j1 j2 m,
  c45_frame E j0 P N m -> c45_cur E P N ->
  rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] ->
  rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] ->
  c45_kmg E i kbs mbs gbs m -> c45_keep E m ->
  lh_mem E i P N kbs mbs gbs m.
Proof.
  intros E i P N kbs mbs gbs j0 j1 j2 m (F1 & F2 & SV) CUR B40 B256
    (NK & NW & IT & O1 & O2 & O3 & O4 & MD & MW & MK & KW & KA)
    (G & O & PR & LA & TX & IP & ER & GD & PL).
  split; [exists j0, j1, j2, N; exact (c45c_frame_merge E m P N j0 j1 j2 F1 F2 B40 B256)|].
  split; [exact SV|]. split; [exact NK|]. split; [exact NW|]. split; [exact IT|].
  split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|].
  split; [exact G|]. split; [exact O|]. split; [exact PR|]. split; [exact LA|].
  split; [exact TX|]. split; [exact IP|]. split; [exact MD|]. split; [exact MW|].
  split; [exact MK|]. split; [exact KW|]. split; [exact KA|].
  split; [split; [exact PL | exact CUR]|]. split; [exact ER | exact GD].
Qed.

Lemma c45c_frame376_of : forall E j0 P N j1 j2 m,
  c45_frame E j0 P N m ->
  rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] ->
  rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] ->
  exists j, rw_cells rsegs m (e_S E - SLOT_FRAME) [CB 376 j].
Proof.
  intros E j0 P N j1 j2 m (F1 & F2 & _) B40 B256.
  apply (c45c_frame376 E m (lh_cells (e_md E) (e_mk E) P N j0 j1 j2)); [|reflexivity].
  exact (c45c_frame_merge E m P N j0 j1 j2 F1 F2 B40 B256).
Qed.

Lemma c45c_cell8_bytes : forall m A v w, rw_cells rsegs m A [C8 v; C8 w] -> bytes_at rsegs m A (le8 v).
Proof. intros m A v w [[_ B] _]. cbn [cells_bytes cbytes] in B. apply bytes_at_app in B. exact (proj1 B). Qed.

(* the exit's state (ex_ms) from the memory of an arm's end *)
Lemma c45c_ex_of : forall E gp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m j0 P N j1 j2,
  frm0 fc -> c45_frame E j0 P N m ->
  rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] ->
  rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] ->
  c45_keep E m -> c45_mach E m ->
  ex_ms E gp (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) s1 a0 a1 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 (wz (e_mk E)) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz L_EXIT) fc None m (seg_rom rsegs)).
Proof.
  intros E gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j0 P N j1 j2
    FC FRM B40 B256 KEEP (MI & TM & ST).
  destruct (c45c_frame376_of E j0 P N j1 j2 m FRM B40 B256) as (j & FJ).
  destruct FRM as (_ & _ & SV). destruct KEEP as (_ & _ & _ & LA & _ & _ & ER & GD & _).
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s1, s2, s3, s4, s5, s6, s8, s9, s10, s11, t3, t4, t5, t6.
  exists F, fc, m, j. split; [reflexivity|].
  split; [exact FC|]. split; [exact FJ|]. split; [exact SV|]. split; [exact ER|]. split; [exact GD|].
  split; [exact LA|].
  split; [exact MI|]. split; [exact TM | exact ST].
Qed.

(* the next loop head's state (lh_ms at i + 1) from the memory of an arm's end *)
Lemma c45c_lh_of : forall E i gp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word)
    F fc m j0 P N j1 j2 kbs mbs gbs,
  frm0 fc -> 0 <= i + 1 <= 47 -> 1 <= N -> c45_frame E j0 P N m -> c45_cur E P N ->
  rw_cells rsegs m (c45_sp E + FO_B40) [CB 40 j1] ->
  rw_cells rsegs m (c45_sp E + FO_B256) [CB 256 j2] ->
  c45_kmg E (i + 1) kbs mbs gbs m -> c45_keep E m -> c45_mach E m ->
  lh_ms E (i + 1) gp
    (MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40) a0 a1 a2 a3 a4 a5 a6 a7
             (wz N) s3 s4 (wz 46) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4) (wz (e_md E + MD_N_REQ)) (wz (i + 1))
             t3 t4 t5 t6)
        F (wz L_LH) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 F fc m j0 P N j1 j2 kbs mbs gbs
    FC HI HN FRM CUR B40 B256 KMG KEEP (MI & TM & ST).
  pose proof (c45c_lh_mem_of E (i + 1) P N kbs mbs gbs j0 j1 j2 m FRM CUR B40 B256 KMG KEEP) as LM.
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s3, s4, t3, t4, t5, t6, F, fc, m, P, N, kbs, mbs, gbs.
  split; [reflexivity|]. split; [exact FC|]. split; [exact HI|]. split; [exact HN|]. split; [exact LM|].
  split; [exact MI|]. split; [exact TM | exact ST].
Qed.

Print Assumptions c45_seg_fp_refl.
Print Assumptions c45_seg_fp_trans.
Print Assumptions c45c_tr_keep.
Print Assumptions c45c_tr_kmg.
Print Assumptions c45c_lh_of.
Print Assumptions c45c_ex_of.
