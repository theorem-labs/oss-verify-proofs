(* reac-pw/fuzz_link, PLAIN build: the frame facts the walk of mark_quietly (lib/Prog/mark_quietly.v)
   carries across its stores, its callees and the memory normalisation the leaf contracts need.

   Every fact the walk keeps is read through `mbyte` (the bytes it holds) and `writable_at` (the bytes
   it may still write). `kb S m m'` says two memories hold the same byte at every address of S;
   `kw S m m'` says every address of S writable in m is writable in m'. Each view the contracts use
   (lib/Prog/link_mem.v, memfile_c.v, reac_served_mark_c.v) is kept by `kb` over the bytes it reads
   and `kw` over the bytes it asks to be writable. The walk gets `kb` / `kw` from a callee's `munch`
   and `wmono`, from the frame's `call_post_k`, and from MemNorm's `normalize_cj` (the memory the
   `leaf_fp` contract of reac_served_mark runs on: no byte above TASK_SIZE outside the image). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem memfile_c reac_served_mark_c mk_str.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The two relations
   ========================================================================== *)

Definition kb (S : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, S a -> mbyte rsegs m' a = mbyte rsegs m a.
Definition kw (S : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, S a -> writable_at rsegs m a -> writable_at rsegs m' a.
Definition rng (a n x : Z) : Prop := a <= x < a + n.

(* helpers: mbyte and writable_at as mrd and wview at `wa`, and both read one address of m *)
Lemma mq_mbyte_mrd : forall m x, mbyte rsegs m x = mrd rsegs m (wa x).
Proof. reflexivity. Qed.
Lemma mq_mrd_ext : forall m m' x, m' x = m x -> mrd rsegs m' x = mrd rsegs m x.
Proof. intros m m' x H. unfold mrd. rewrite H. reflexivity. Qed.
Lemma mq_wview_ext : forall m m' x, m' x = m x -> wview rsegs m' x = wview rsegs m x.
Proof. intros m m' x H. unfold wview. rewrite H. reflexivity. Qed.
Lemma mq_ua : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. exact (wa_unsigned a Ha). Qed.
Lemma mq_task_size : TASK_SIZE = 140737488355328.
Proof. reflexivity. Qed.

Lemma kb_mono : forall (S S' : Z -> Prop) m m', (forall x, S' x -> S x) -> kb S m m' -> kb S' m m'.
Proof. intros S S' m m' HS H a Ha. apply H. apply HS. exact Ha. Qed.
Lemma kw_mono : forall (S S' : Z -> Prop) m m', (forall x, S' x -> S x) -> kw S m m' -> kw S' m m'.
Proof. intros S S' m m' HS H a Ha. apply H. apply HS. exact Ha. Qed.
Lemma kb_refl : forall S m, kb S m m.
Proof. intros S m a _. reflexivity. Qed.
Lemma kw_refl : forall S m, kw S m m.
Proof. intros S m a _ H. exact H. Qed.
Lemma kb_sym : forall S m m', kb S m m' -> kb S m' m.
Proof. intros S m m' H a Ha. symmetry. exact (H a Ha). Qed.
Lemma kb_trans : forall S m1 m2 m3, kb S m1 m2 -> kb S m2 m3 -> kb S m1 m3.
Proof. intros S m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma kw_trans : forall S m1 m2 m3, kw S m1 m2 -> kw S m2 m3 -> kw S m1 m3.
Proof. intros S m1 m2 m3 H1 H2 a Ha W. exact (H2 a Ha (H1 a Ha W)). Qed.
Lemma kb_or : forall (S1 S2 : Z -> Prop) m m', kb S1 m m' -> kb S2 m m' -> kb (fun x => S1 x \/ S2 x) m m'.
Proof. intros S1 S2 m m' H1 H2 a [Ha|Ha]; [exact (H1 a Ha) | exact (H2 a Ha)]. Qed.
Lemma kw_or : forall (S1 S2 : Z -> Prop) m m', kw S1 m m' -> kw S2 m m' -> kw (fun x => S1 x \/ S2 x) m m'.
Proof. intros S1 S2 m m' H1 H2 a [Ha|Ha]; [exact (H1 a Ha) | exact (H2 a Ha)]. Qed.

(* from a callee's footprint *)
Lemma kb_munch : forall W (S : Z -> Prop) m m', munch W m m' ->
  (forall x, S x -> 0 <= x < 2 ^ 64 /\ outside W x) -> kb S m m'.
Proof.
  intros W S m m' H HS a Ha. destruct (HS a Ha) as [Hr Ho]. rewrite !mq_mbyte_mrd.
  apply mq_mrd_ext. apply H. rewrite wa_unsigned by exact Hr. exact Ho.
Qed.
Lemma kw_munch : forall W (S : Z -> Prop) m m', munch W m m' ->
  (forall x, S x -> 0 <= x < 2 ^ 64 /\ outside W x) -> kw S m m'.
Proof.
  intros W S m m' H HS a Ha Wa. destruct (HS a Ha) as [Hr Ho]. unfold writable_at in *.
  rewrite (mq_wview_ext m m' (Z_to_bv 64 a)); [exact Wa|].
  apply H. rewrite mq_ua by exact Hr. exact Ho.
Qed.
Lemma kw_wmono : forall S m m', wmono rsegs m m' -> kw S m m'.
Proof. intros S m m' H a _ Wa. unfold writable_at in *. exact (H _ Wa). Qed.

(* read-only bytes: two memories that agree with the image agree there *)
Lemma kb_ro : forall m m', ro_agree rsegs m -> ro_agree rsegs m' ->
  kb (fun x => 0 <= x < 2 ^ 64 /\ ro_addr rsegs (wa x) = true) m m'.
Proof.
  intros m m' H H' a [_ Ha]. rewrite !mq_mbyte_mrd. rewrite (H' (wa a) Ha), (H (wa a) Ha). reflexivity.
Qed.
Lemma ro_agree_of_mem_inv : forall m, mem_inv rsegs m -> ro_agree rsegs m.
Proof.
  intros m H a Ha. unfold mrd. destruct (m a) as [b|] eqn:E; [|reflexivity].
  exfalso. rewrite (H a b E) in Ha. discriminate Ha.
Qed.

(* the normalised memory of MemNorm (`normalize_cj`) and back (`mem_rel_cj`) *)
Lemma kb_ncj : forall m, ro_agree rsegs m -> kb (fun x => 0 <= x < TASK_SIZE) m (normalize_cj rsegs m).
Proof.
  intros m Hro a Ha. pose proof mq_task_size as HT. rewrite !mq_mbyte_mrd.
  apply mrd_normalize_cj; [exact Hro|]. right. right. rewrite wa_unsigned by lia. lia.
Qed.
Lemma kw_ncj : forall m,
  kw (fun x => 0 <= x < TASK_SIZE /\ ro_addr rsegs (wa x) = false) m (normalize_cj rsegs m).
Proof.
  intros m a [Ha Hro] Wa. pose proof mq_task_size as HT. unfold writable_at in *.
  assert (E : cj_drop rsegs (Z_to_bv 64 a) = false).
  { apply cj_drop_false_intro; [exact Hro|]. right. rewrite mq_ua by lia. lia. }
  rewrite (mq_wview_ext m (normalize_cj rsegs m) (Z_to_bv 64 a)); [exact Wa|].
  unfold normalize_cj. rewrite E. reflexivity.
Qed.
Lemma kb_rcj : forall m m0, mem_rel_cj rsegs m m0 -> ro_agree rsegs m ->
  kb (fun x => 0 <= x < TASK_SIZE) m0 m.
Proof.
  intros m m0 HR Hro a Ha. pose proof mq_task_size as HT. rewrite !mq_mbyte_mrd.
  rewrite (mq_mrd_ext (normalize_cj rsegs m) m0 (wa a) (proj1 HR (wa a))).
  symmetry. apply mrd_normalize_cj; [exact Hro|]. right. right. rewrite wa_unsigned by lia. lia.
Qed.
Lemma kw_rcj : forall S m m0, mem_rel_cj rsegs m m0 -> kw S m0 m.
Proof. intros S m m0 HR a _ Wa. exact (writable_at_rel_cj rsegs m m0 a HR Wa). Qed.

(* the segments of the plain image, by computation *)
Lemma mq_find_segment : forall (l : list Segment) x n seg, find_segment l x n = Some seg ->
  In seg l /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  intros l x n seg H. split; [exact (YK1j.find_segment_in _ _ _ _ H)|].
  exact (YK1j.find_segment_range _ _ _ _ H).
Qed.

Lemma mq_rsegs_ro : forallb (fun s => seg_writable s ||
  ((0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x20000))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mq_rsegs_rw : forallb (fun s => negb (seg_writable s) ||
  ((Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x10000) || (0x20000 <=? Z.of_N (seg_base s)))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mq_rsegs_img : forallb (fun s =>
  (0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x97000)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Definition mq_holds (lo hi : Z) (s : Segment) : bool :=
  (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)).
Lemma mq_rsegs_cover : existsb (mq_holds 0x10000 0x12000) rsegs = true /\
  existsb (mq_holds 0x12000 0x20000) rsegs = true.
Proof. split; vm_compute; reflexivity. Qed.

Lemma mq_seg_range : forall x seg, find_segment rsegs x 1 = Some seg -> 0x10000 <= x < 0x97000.
Proof.
  intros x seg E. apply mq_find_segment in E as (Hin & H1 & H2).
  pose proof mq_rsegs_img as C. rewrite forallb_forall in C. specialize (C seg Hin). cbv beta in C.
  apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

(* a writable byte outside the image's range is a byte of m *)
Lemma mq_present_out : forall m a, 0 <= a < 2 ^ 64 -> (a < 0x10000 \/ 0x97000 <= a) ->
  wview rsegs m (wa a) <> None -> exists b, m (wa a) = Some b.
Proof.
  intros m a Ha Hout Wa. destruct (m (wa a)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply Wa. unfold wview. rewrite E.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [seg|] eqn:F; [|reflexivity].
  exfalso. rewrite wa_unsigned in F by exact Ha. apply mq_seg_range in F. lia.
Qed.

(* the read-only range of the plain image: its two non-writable PT_LOADs, [0x10000, 0x20000) *)
Lemma ro_addr_range : forall x, 0 <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = true -> 0x10000 <= x < 0x20000.
Proof.
  intros x Hx H. unfold ro_addr in H. rewrite wa_unsigned in H by exact Hx. revert H.
  destruct (find_segment rsegs x 1) as [seg|] eqn:E; intros H; [|discriminate H].
  apply mq_find_segment in E as (Hin & H1 & H2).
  pose proof mq_rsegs_ro as C. rewrite forallb_forall in C. specialize (C seg Hin). cbv beta in C.
  apply negb_true_iff in H. rewrite H in C. cbn [orb] in C. apply andb_prop in C as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.
Lemma ro_addr_of_range : forall x, 0x10000 <= x < 0x20000 -> ro_addr rsegs (wa x) = true.
Proof.
  intros x Hx. unfold ro_addr. rewrite wa_unsigned by lia.
  destruct (find_segment rsegs x 1) as [seg|] eqn:E.
  - apply mq_find_segment in E as (Hin & H1 & H2).
    pose proof mq_rsegs_rw as C. rewrite forallb_forall in C. specialize (C seg Hin). cbv beta in C.
    destruct (seg_writable seg) eqn:Wr; [|reflexivity]. exfalso.
    try rewrite Wr in C. cbn [negb orb] in C.
    apply orb_true_iff in C as [C|C]; apply Z.leb_le in C; lia.
  - exfalso. destruct mq_rsegs_cover as [C1 C2].
    destruct (Z_lt_ge_dec x 0x12000) as [Hl|Hl].
    + apply existsb_exists in C1 as (s & Hin & Hs). unfold mq_holds in Hs.
      apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.leb_le in Hs2.
      exact (find_segment_some rsegs s x 1 Hin ltac:(lia) ltac:(lia) E).
    + apply existsb_exists in C2 as (s & Hin & Hs). unfold mq_holds in Hs.
      apply andb_prop in Hs as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.leb_le in Hs2.
      exact (find_segment_some rsegs s x 1 Hin ltac:(lia) ltac:(lia) E).
Qed.

(* where a kept string lies (link_mem `kept_str`) *)
Lemma kept_str_range : forall a n, kept_str a n -> 0 <= a < 2 ^ 64 -> 0 < n ->
  (A_G_NAMES <= a /\ a + n <= A_G_NAMES + G_NAMES_SIZE) \/ (0x10000 <= a /\ a + n <= 0x20000).
Proof.
  intros a n [H|H] Ha Hn; [left; exact H|right].
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  apply ro_addr_range in H0; [|exact Ha].
  destruct (Z_lt_ge_dec (a + n - 1) (2 ^ 64)) as [Hl|Hl].
  - pose proof (H (n - 1) ltac:(lia)) as H1. apply ro_addr_range in H1; [lia | lia].
  - exfalso. pose proof (H (2 ^ 64 - a) ltac:(lia)) as H1.
    replace (a + (2 ^ 64 - a)) with (2 ^ 64) in H1 by lia.
    assert (E : wa (2 ^ 64) = wa 0) by (apply bv_eq; unfold wa; rewrite !Z_to_bv_unsigned; reflexivity).
    rewrite E in H1. apply ro_addr_range in H1; lia.
Qed.

(* ==========================================================================
   2. Each view, kept
   ========================================================================== *)

Lemma bytes_at_kb : forall m m' a bs, bytes_at rsegs m a bs -> kb (rng a (Z.of_nat (length bs))) m m' ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) K. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- mq_mbyte_mrd. rewrite (K (a + Z.of_nat i)) by (unfold rng; lia).
  rewrite mq_mbyte_mrd. exact (H3 i Hi).
Qed.
Lemma wr_at_kw : forall m m' a n, wr_at rsegs m a n -> kw (rng a n) m m' -> wr_at rsegs m' a n.
Proof.
  intros m m' a n (H1 & H2 & H3) K. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  change (writable_at rsegs m' (a + i)). apply (K (a + i)); [unfold rng; lia|]. exact (H3 i Hi).
Qed.
Lemma u64_at_kb : forall m m' a v, u64_at m a v -> kb (rng a 8) m m' -> u64_at m' a v.
Proof.
  intros m m' a v H K. unfold u64_at in *. apply (bytes_at_kb m m' a _ H).
  rewrite length_le8. exact K.
Qed.
Lemma u32_at_kb : forall m m' a v, u32_at m a v -> kb (rng a 4) m m' -> u32_at m' a v.
Proof.
  intros m m' a v H K. unfold u32_at in *. apply (bytes_at_kb m m' a _ H).
  rewrite length_le4. exact K.
Qed.
Lemma cstr_at_kb : forall m m' a s, cstr_at m a s -> kb (rng a (Z.of_nat (length s) + 1)) m m' -> cstr_at m' a s.
Proof.
  intros m m' a s [H N] K. split; [|exact N]. apply (bytes_at_kb m m' a _ H).
  eapply kb_mono; [|exact K]. intros x Hx. unfold rng in *. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.
Lemma str_arg_kb : forall m m' a o, str_arg m a o ->
  (forall s, o = Some s -> kb (rng a (Z.of_nat (length s) + 1)) m m') -> str_arg m' a o.
Proof.
  intros m m' a [s|] H K; cbn [str_arg] in H |- *; [|exact H].
  destruct H as [Ha Hc]. split; [exact Ha|]. exact (cstr_at_kb m m' a s Hc (K s eq_refl)).
Qed.
Lemma rw_cells_kbw : forall m m' a cs, rw_cells rsegs m a cs ->
  kb (rng a (Z.of_nat (cells_size cs))) m m' -> kw (rng a (Z.of_nat (cells_size cs))) m m' ->
  rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs [[Hwf Hb] Hw] K W. split; [split; [exact Hwf|]|].
  - apply (bytes_at_kb m m' a _ Hb). rewrite cells_bytes_length by exact Hwf. exact K.
  - exact (wr_at_kw m m' a _ Hw W).
Qed.
Lemma stk_kbw : forall m m' lo hi, stk rsegs m lo hi ->
  kb (fun x => lo <= x < hi) m m' -> kw (fun x => lo <= x < hi) m m' -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) K W. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. split.
  - change (writable_at rsegs m' a). apply (W a Ha). exact Hw.
  - exists b. rewrite <- mq_mbyte_mrd. rewrite (K a Ha). rewrite mq_mbyte_mrd. exact Hb.
Qed.
Lemma val_mem_kb : forall m m' a n v, YI04.val_mem rsegs m a n v -> kb (rng a (Z.of_nat n)) m m' ->
  YI04.val_mem rsegs m' a n v.
Proof.
  intros m m' a n v H K k Hk. rewrite (K (a + Z.of_nat k)) by (unfold rng; lia). exact (H k Hk).
Qed.
Lemma nlk_at_kbw : forall m m' bs, nlk_at m bs -> kb (rng A_G_NL NK_SIZE) m m' -> kw (rng A_G_NL NK_SIZE) m m' ->
  nlk_at m' bs.
Proof.
  intros m m' bs [[Hb Hw] Hl] K W. split; [split|exact Hl].
  - apply (bytes_at_kb m m' _ _ Hb). rewrite Hl. exact K.
  - apply (wr_at_kw m m' _ _ Hw). rewrite Hl. exact W.
Qed.
Lemma iftab_at_kb : forall m m' bs tab, iftab_at m bs tab -> kb (rng A_G_NL NK_SIZE) m m' ->
  (forall i nm ix p, nth_error tab i = Some (nm, ix) -> u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     0 <= p -> p + Z.of_nat (length nm) + 1 <= 2 ^ 64 ->
     kb (rng p (Z.of_nat (length nm) + 1)) m m') ->
  iftab_at m' bs tab.
Proof.
  intros m m' bs tab (Hn & Hl & H) K KS. split; [exact Hn|]. split; [exact Hl|].
  intros i nm ix Hi. destruct (H i nm ix Hi) as (Hix & p & Hp & Hp0 & Hc & Hu).
  assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [exact Hix|]. exists p. split; [|split; [exact Hp0|split]].
  - apply (u64_at_kb m m' _ _ Hp). eapply kb_mono; [|exact K]. intros x Hx.
    unfold rng, A_G_NL, NK_IF_NAME, NK_SIZE in *. lia.
  - destruct Hc as [Hcb Hcn]. pose proof (bytes_at_bound rsegs m p _ Hcb) as Bd.
    rewrite length_app in Bd. cbn [length] in Bd.
    exact (cstr_at_kb m m' p nm (conj Hcb Hcn) (KS i nm ix p Hi Hp ltac:(lia) ltac:(lia))).
  - apply (u32_at_kb m m' _ _ Hu). eapply kb_mono; [|exact K]. intros x Hx.
    unfold rng, A_G_NL, NK_IF_INDEX, NK_SIZE in *. lia.
Qed.
Lemma marks_at_kbw : forall m m' p gbs, marks_at m p gbs -> kb (rng p MK_SIZE) m m' -> kw (rng p MK_SIZE) m m' ->
  marks_at m' p gbs.
Proof.
  intros m m' p gbs [[Hb Hw] Hl] K W. split; [split|exact Hl].
  - apply (bytes_at_kb m m' _ _ Hb). rewrite Hl. exact K.
  - apply (wr_at_kw m m' _ _ Hw). rewrite Hl. exact W.
Qed.

(* one FILE field, kept by kb over the FILE header *)
Ltac mq_fld K :=
  unfold mf_fld in *; eapply val_mem_kb; [eassumption|]; eapply kb_mono; [|exact K];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; unfold rng, MemFile.MF_ZEROED, MemFile.MF_COOKIE in *; lia.

Lemma memfile_k_kbw : forall m m' f k, memfile_k m f k -> kb (rng f MemFile.MF_ZEROED) m m' ->
  kw (fun x => rng f MemFile.MF_BLOCK x \/ rng A_G_SAID SAID_SIZE x) m m' -> memfile_k m' f k.
Proof.
  intros m m' f k (Hm & Hw & Hb & Hs & Hp) K W.
  split; [|split; [|split; [|split]]].
  - eapply MemFile.memfile_at_frame; [|exact Hm]. intros x Hx. exact (K x Hx).
  - unfold mf_win in *.
    destruct Hw as [(Hk & H1 & H2 & H3) | (Hk & H1 & H2 & H3)]; [left|right];
      (split; [exact Hk|]); (split; [|split]); mq_fld K.
  - apply (wr_at_kw m m' _ _ Hb). eapply kw_mono; [|exact W]. intros x Hx. left. exact Hx.
  - apply (wr_at_kw m m' _ _ Hs). eapply kw_mono; [|exact W]. intros x Hx. right. exact Hx.
  - exact Hp.
Qed.
Lemma mf_dyn_kb : forall m m' f fl om wend wpos wbase pos len, mf_dyn m f fl om wend wpos wbase pos len ->
  kb (rng f MemFile.MF_ZEROED) m m' -> mf_dyn m' f fl om wend wpos wbase pos len.
Proof.
  intros m m' f fl om wend wpos wbase pos len H K. unfold mf_dyn in *.
  destruct H as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
  do 7 (split; [assumption|]).
  repeat (split; [mq_fld K|]). mq_fld K.
Qed.
Lemma mf_pend_bytes_kb : forall m m' f pb, mf_pend_bytes m f pb ->
  kb (rng (f + MemFile.MF_BUF) (Z.of_nat (length pb))) m m' -> mf_pend_bytes m' f pb.
Proof. intros m m' f pb H K. exact (bytes_at_kb m m' _ pb H K). Qed.
Lemma guard_words_kb : forall m m', guard_words m -> kb (fun x => rng GOT_GUARD 8 x \/ rng GUARD 8 x) m m' ->
  guard_words m'.
Proof.
  intros m m' [H1 (g & H2)] K. split.
  - apply (bytes_at_kb m m' _ _ H1). eapply kb_mono; [|exact K]. intros x Hx. left.
    rewrite length_le8 in Hx. exact Hx.
  - exists g. apply (bytes_at_kb m m' _ _ H2). eapply kb_mono; [|exact K]. intros x Hx. right.
    rewrite length_le8 in Hx. exact Hx.
Qed.
Lemma mark_errno_ok_kw : forall m m' regs K sink, mark_errno_ok m regs K sink -> kw (rng (errno_at regs) 4) m m' ->
  mark_errno_ok m' regs K sink.
Proof.
  intros m m' regs K sink (H & R) W. split; [exact (wr_at_kw m m' _ _ H W) | exact R].
Qed.
Lemma mark_name_ok_kb : forall m m' regs K sink nm, mark_name_ok m regs K sink nm ->
  (forall s, nm = Some s -> kb (rng (arg regs 1) (name_span (arg regs 1) s)) m m') ->
  mark_name_ok m' regs K sink nm.
Proof.
  intros m m' regs K sink nm H KS s Hs.
  destruct (H s Hs) as (H1 & H2 & H3 & H4 & H5 & (slack & Hsl & Hlen) & H7).
  pose proof (KS s Hs) as Ks.
  do 5 (split; [assumption|]).
  split; [|exact H7]. exists slack. split; [|exact Hlen].
  apply (bytes_at_kb m m' _ _ Hsl). eapply kb_mono; [|exact Ks]. intros x Hx. unfold rng, name_span in *.
  pose proof (Z.mod_pos_bound (- (arg regs 1 + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
Qed.
Lemma mark_block_ok_kbw : forall m m' regs K sink, mark_block_ok m regs K sink ->
  (arg regs 0 <> 0 -> kb (rng (arg regs 0) MK_SIZE) m m' /\ kw (rng (arg regs 0) MK_SIZE) m m') ->
  mark_block_ok m' regs K sink.
Proof.
  intros m m' regs K sink H KW H0. destruct (H H0) as (H1 & H2 & H3 & H4 & H5 & gbs & Hg & Hwf).
  destruct (KW H0) as [Kb Kw].
  do 5 (split; [assumption|]). exists gbs. split; [|exact Hwf]. exact (marks_at_kbw m m' _ gbs Hg Kb Kw).
Qed.
Lemma mark_table_ok_kb : forall m m' regs K sink tab, mark_table_ok m regs K sink tab ->
  (Z.of_nat (length tab) <= 80)%Z -> kb (rng A_G_NL NK_SIZE) m m' -> mark_table_ok m' regs K sink tab.
Proof.
  intros m m' regs K sink tab H Hl Kb i n2 ix p Hi Hp.
  assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  apply (H i n2 ix p Hi).
  apply (u64_at_kb m' m _ _ Hp). apply kb_sym. eapply kb_mono; [|exact Kb]. intros x Hx.
  unfold rng, A_G_NL, NK_IF_NAME, NK_SIZE in *. lia.
Qed.
Lemma policy_ro_of_mem_inv : forall m, mem_inv rsegs m -> policy_ro m.
Proof.
  intros m MI. split; [|split; [|split]].
  - split; [exact (prefix_at m MI) | exact S_PREFIX_no_nul].
  - split; [exact (served_at m MI) | exact S_SERVED_no_nul].
  - split; [exact (vlan_at m MI) | exact S_VLAN_no_nul].
  - split; [exact (empty_at m MI) | intros []].
Qed.

(* fmemopen's precondition (lib/Prog/StdioModel.v) *)
Lemma stdio_ok_kb : forall m m', StdioModel.stdio_ok m ->
  kb (fun x => x = StdioModel.A_LIBC + 1 \/ x = StdioModel.A_LIBC + 3 \/ rng StdioModel.A_OFL_LOCK 4 x) m m' ->
  StdioModel.stdio_ok m'.
Proof.
  intros m m' (H1 & H2 & H3) K. split; [|split].
  - apply (bytes_at_kb m m' _ _ H1). eapply kb_mono; [|exact K]. intros x Hx.
    unfold rng in Hx. cbn [length] in Hx. left. lia.
  - apply (bytes_at_kb m m' _ _ H2). eapply kb_mono; [|exact K]. intros x Hx.
    unfold rng in Hx. cbn [length] in Hx. right. left. lia.
  - apply (bytes_at_kb m m' _ _ H3). eapply kb_mono; [|exact K]. intros x Hx.
    rewrite length_le4 in Hx. right. right. exact Hx.
Qed.
Lemma ofl_empty_kbw : forall m m', StdioModel.ofl_empty m ->
  kb (rng StdioModel.A_OFL_HEAD 8) m m' -> kw (rng StdioModel.A_OFL_HEAD 8) m m' -> StdioModel.ofl_empty m'.
Proof.
  intros m m' H K W. unfold StdioModel.ofl_empty in *. exact (rw_cells_kbw m m' _ _ H K W).
Qed.
Lemma guard_ok_kb : forall m m', StdioModel.guard_ok m -> kb (fun x => rng A_GOT_GUARD 8 x \/ rng A_GUARD 8 x) m m' ->
  StdioModel.guard_ok m'.
Proof.
  intros m m' [H1 (g & H2)] K. split.
  - apply (bytes_at_kb m m' _ _ H1). eapply kb_mono; [|exact K]. intros x Hx. left.
    rewrite length_le8 in Hx. exact Hx.
  - exists g. apply (bytes_at_kb m m' _ _ H2). eapply kb_mono; [|exact K]. intros x Hx. right.
    rewrite length_le8 in Hx. exact Hx.
Qed.

(* rewind's precondition from the FILE alone: the seven words and the pending bytes *)
Lemma mf_dyn_of_memfile_k : forall m f k, memfile_k m f k ->
  exists fl om wend wpos wbase pos len, mf_dyn m f fl om wend wpos wbase pos len.
Proof.
  intros m f k (MA & WIN & _).
  destruct MA as (F0 & F1 & F2 & _ & FL & OM & _ & (pos & len & PL & LS & CP & CL)).
  assert (Hf : f + MemFile.MF_BLOCK < 2 ^ 64) by (unfold MemFile.MF_BLOCK in *; lia).
  change (MemFile.mf_size MemFile.link_mf) with 4096 in LS.
  destruct FL as [FL|FL]; [exists MemFile.F_NORD | exists (MemFile.F_NORD + MemFile.F_ERR)];
  (destruct OM as [OM|OM]; [exists 0 | exists YI14.U32M1]);
  (destruct WIN as [(Hk & A & B & C) | (Hk & A & B & C)];
   [exists 0, 0, 0 | exists (f + MemFile.MF_BUF + MemFile.MF_BUFSIZ), (f + MemFile.MF_BUF + k), (f + MemFile.MF_BUF)]);
  exists pos, len; unfold mf_dyn;
  (split; [unfold MemFile.F_NORD, MemFile.F_ERR; lia|]);
  (split; [unfold YI14.U32M1; lia|]);
  (split; [unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia|]);
  (split; [unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia|]);
  (split; [unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_BLOCK in *; lia|]);
  (split; [lia|]); (split; [unfold SAID_SIZE; lia|]);
  repeat (split; [assumption|]); assumption.
Qed.
Lemma mf_pend_of_memfile_k : forall m f k, memfile_k m f k ->
  exists pb, mf_pend_bytes m f pb /\ Z.of_nat (length pb) = k.
Proof.
  intros m f k Hk. pose proof (memfile_k_range m f k Hk) as Hr.
  destruct Hk as (Hm & _ & (Hb0 & Hb1 & Hb) & _ & Hp).
  destruct Hm as (Hf0 & Hf1 & _).
  unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK, MemFile.MF_BUFSIZ in *.
  assert (S : stk rsegs m (f + MemFile.MF_BUF) (f + MemFile.MF_BUF + k)).
  { unfold MemFile.MF_BUF. split; [lia|]. split; [lia|]. intros x Hx.
    pose proof (Hb (x - f) ltac:(lia)) as Wx. replace (f + (x - f)) with x in Wx by lia.
    split; [exact Wx|].
    destruct (mq_present_out m x ltac:(lia) ltac:(lia) Wx) as (b & Eb).
    exists b. unfold mrd. rewrite Eb. reflexivity. }
  destruct (stk_bytes rsegs m _ _ S ltac:(lia)) as (bs & Hlen & Hbs).
  exists bs. split; [exact Hbs|]. rewrite Hlen. rewrite Z2Nat.id by lia. lia.
Qed.

(* ==========================================================================
   3. Back from the normalised memory, and image facts
   ========================================================================== *)
Definition mle (m m' : word -> option byte) : Prop :=
  (forall a b, mbyte rsegs m a = Some b -> mbyte rsegs m' a = Some b) /\
  (forall a, writable_at rsegs m a -> writable_at rsegs m' a).
Lemma mle_rcj : forall m m0, mem_rel_cj rsegs m m0 -> mle m0 m.
Proof.
  intros m m0 HR. split.
  - intros a b H. exact (mbyte_rel_cj rsegs m m0 a b HR H).
  - intros a H. exact (writable_at_rel_cj rsegs m m0 a HR H).
Qed.
Lemma bytes_at_mle : forall m m' a bs, bytes_at rsegs m a bs -> mle m m' -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) [Hb _]. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  rewrite <- mq_mbyte_mrd. apply Hb. rewrite mq_mbyte_mrd, (H3 i Hi). exact E.
Qed.
Lemma wr_at_mle : forall m m' a n, wr_at rsegs m a n -> mle m m' -> wr_at rsegs m' a n.
Proof.
  intros m m' a n (H1 & H2 & H3) [_ Hw]. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  change (writable_at rsegs m' (a + i)). apply Hw. exact (H3 i Hi).
Qed.
Lemma u64_at_mle : forall m m' a v, u64_at m a v -> mle m m' -> u64_at m' a v.
Proof. intros m m' a v H L. exact (bytes_at_mle m m' a _ H L). Qed.
Lemma cstr_at_mle : forall m m' a s, cstr_at m a s -> mle m m' -> cstr_at m' a s.
Proof. intros m m' a s [H N] L. split; [exact (bytes_at_mle m m' a _ H L) | exact N]. Qed.
Lemma nlk_at_mle : forall m m' bs, nlk_at m bs -> mle m m' -> nlk_at m' bs.
Proof.
  intros m m' bs [[Hb Hw] Hl] L. split; [split|exact Hl].
  - exact (bytes_at_mle m m' _ _ Hb L).
  - exact (wr_at_mle m m' _ _ Hw L).
Qed.
Lemma iftab_at_mle : forall m m' bs tab, iftab_at m bs tab -> mle m m' -> iftab_at m' bs tab.
Proof.
  intros m m' bs tab (Hn & Hl & H) L. split; [exact Hn|]. split; [exact Hl|].
  intros i nm ix Hi. destruct (H i nm ix Hi) as (Hix & p & Hp & Hp0 & Hc & Hu).
  split; [exact Hix|]. exists p. split; [exact (u64_at_mle m m' _ _ Hp L)|].
  split; [exact Hp0|]. split.
  - exact (cstr_at_mle m m' _ _ Hc L).
  - exact (bytes_at_mle m m' _ _ Hu L).
Qed.
Lemma marks_at_mle : forall m m' p gbs, marks_at m p gbs -> mle m m' -> marks_at m' p gbs.
Proof.
  intros m m' p gbs [[Hb Hw] Hl] L. split; [split|exact Hl].
  - exact (bytes_at_mle m m' _ _ Hb L).
  - exact (wr_at_mle m m' _ _ Hw L).
Qed.

Lemma mq_val_mem_mle : forall m m' a n v, YI04.val_mem rsegs m a n v -> mle m m' -> YI04.val_mem rsegs m' a n v.
Proof. intros m m' a n v H [Hb _] k Hk. apply Hb. exact (H k Hk). Qed.

(* memfile_at reads its block only through val_mem *)
Lemma mq_memfile_at_vm : forall (B : malloc_syms) MS (m m' : word -> option byte) f,
  (forall a n v, YI04.val_mem (ms_segs B) m a n v -> YI04.val_mem (ms_segs B) m' a n v) ->
  MemFile.memfile_at B MS m f -> MemFile.memfile_at B MS m' f.
Proof.
  intros B MS m m' f HV (Hf0 & Hf1 & Hf2 & Hst & Hfl & Hom & Hwn & Hc).
  split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|].
  split; [|split; [|split; [|split]]].
  - unfold MemFile.memfile_static in *. clear Hfl Hom Hwn Hc.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat match goal with |- _ /\ _ => split end; apply HV; assumption.
  - unfold MemFile.memfile_flags in *. destruct Hfl as [H|H]; [left|right]; apply HV; exact H.
  - unfold MemFile.memfile_omode in *. destruct Hom as [H|H]; [left|right]; apply HV; exact H.
  - unfold MemFile.memfile_window in *.
    destruct Hwn as (H8 & H16 & [(H1 & H2 & H3) | (k & Hk & H1 & H2 & H3)]).
    + split; [apply HV; exact H8|]. split; [apply HV; exact H16|].
      left. split; [|split]; apply HV; assumption.
    + split; [apply HV; exact H8|]. split; [apply HV; exact H16|].
      right. exists k. split; [exact Hk|]. split; [|split]; apply HV; assumption.
  - unfold MemFile.memfile_cookie in *. destruct Hc as (pos & len & Hp & Hl & H1 & H2).
    exists pos, len. split; [exact Hp|]. split; [exact Hl|]. split; apply HV; assumption.
Qed.

Lemma memfile_k_mle : forall m m' f k, memfile_k m f k -> mle m m' -> memfile_k m' f k.
Proof.
  intros m m' f k (Hm & Hw & Hb & Hs & Hp) L.
  split; [|split; [|split; [|split]]].
  - apply (mq_memfile_at_vm _ _ m m' f); [|exact Hm].
    intros a n v H. exact (mq_val_mem_mle m m' a n v H L).
  - unfold mf_win, mf_fld in *.
    destruct Hw as [(Hk & H1 & H2 & H3) | (Hk & H1 & H2 & H3)]; [left|right];
      (split; [exact Hk|]); (split; [|split]); (eapply mq_val_mem_mle; [eassumption | exact L]).
  - exact (wr_at_mle m m' f _ Hb L).
  - exact (wr_at_mle m m' _ _ Hs L).
  - exact Hp.
Qed.

Lemma mq_outside_or : forall W x, outside W x \/ exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as [H|(lo' & hi' & Hin & H)].
    + left. split; [lia | exact H].
    + right. exists lo', hi'. split; [right; exact Hin | exact H].
  - destruct (IH x) as [H|(lo' & hi' & Hin & H)].
    + left. split; [lia | exact H].
    + right. exists lo', hi'. split; [right; exact Hin | exact H].
Qed.

Lemma task_mem_munch : forall W m m', task_mem rsegs m -> munch W m m' ->
  (forall lo hi, In (lo, hi) W -> hi <= TASK_SIZE) -> task_mem rsegs m'.
Proof.
  intros W m m' HT HM HW a b E.
  destruct (mq_outside_or W (bv_unsigned a)) as [Ho|(lo & hi & Hin & Hx)].
  - rewrite (HM a Ho) in E. exact (HT a b E).
  - right. pose proof (HW lo hi Hin). lia.
Qed.

(* the image's own writable bytes, by computation *)
Definition mq_wv0 (x : Z) : bool :=
  match wview rsegs (fun _ => None) (wa x) with Some _ => true | None => false end.
Lemma mq_wr_at_img : forall m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  forallb (fun i => mq_wv0 (a + Z.of_nat i)) (seq 0 n) = true -> wr_at rsegs m a (Z.of_nat n).
Proof.
  intros m a n Ha Hn H. split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
  rewrite forallb_forall in H. specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). cbv beta in H.
  rewrite Z2Nat.id in H by lia. unfold mq_wv0 in H.
  destruct (m (wa (a + i))) as [b|] eqn:E.
  - unfold wview. rewrite E. discriminate.
  - rewrite (mq_wview_ext (fun _ => None) m (wa (a + i)) E).
    destruct (wview rsegs (fun _ => None) (wa (a + i))); [discriminate | discriminate H].
Qed.

Lemma wr_at_g_say : forall m, wr_at rsegs m A_G_SAY 8.
Proof.
  intros m. apply (mq_wr_at_img m A_G_SAY 8%nat); [unfold A_G_SAY; lia | unfold A_G_SAY; lia |].
  vm_compute. reflexivity.
Qed.
Lemma wr_at_g_sink : forall m, wr_at rsegs m A_G_SINK 8.
Proof.
  intros m. apply (mq_wr_at_img m A_G_SINK 8%nat); [unfold A_G_SINK; lia | unfold A_G_SINK; lia |].
  vm_compute. reflexivity.
Qed.
Lemma wr_at_errno_img : forall m, wr_at rsegs m 0x75564 4.
Proof.
  intros m. apply (mq_wr_at_img m 0x75564 4%nat); [lia | lia |].
  vm_compute. reflexivity.
Qed.
Lemma present_of_writable_out : forall m a, 0 <= a < 2 ^ 64 -> (a < 0x10000 \/ 0x97000 <= a) ->
  writable_at rsegs m a -> exists b, m (Z_to_bv 64 a) = Some b.
Proof. intros m a Ha Hout Wa. exact (mq_present_out m a Ha Hout Wa). Qed.

(* the reserved segments of the plain image, by computation *)
Lemma mq_rsv_in : forallb (fun s : word * word =>
  (0x10000 <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x97000))
  (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.
Definition mq_rsv_holds (lo hi : Z) (s : word * word) : bool :=
  (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)).
Lemma mq_rsv_cover : existsb (mq_rsv_holds 0x10000 0x12000) (segments_reserved rsegs) = true /\
  existsb (mq_rsv_holds 0x12000 0x20000) (segments_reserved rsegs) = true /\
  existsb (mq_rsv_holds 0x20000 0x21000) (segments_reserved rsegs) = true /\
  existsb (mq_rsv_holds 0x21000 0x97000) (segments_reserved rsegs) = true.
Proof. split; [|split; [|split]]; vm_compute; reflexivity. Qed.
Lemma mq_rsv_from : forall lo hi a, existsb (mq_rsv_holds lo hi) (segments_reserved rsegs) = true ->
  lo <= a < hi -> exists s, In s (segments_reserved rsegs) /\
    bv_unsigned (fst s) <= a < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  intros lo hi a H Ha. apply existsb_exists in H as (s & Hin & Hs). unfold mq_rsv_holds in Hs.
  apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.
Lemma mq_rsegs_len : length rsegs = 4%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma in_img_rsegs : forall B a, ms_segs B = rsegs -> (in_img B a <-> 0x10000 <= a < 0x97000).
Proof.
  intros B a E. unfold in_img. rewrite E. split.
  - intros [_ (s & Hin & Hs)]. pose proof mq_rsv_in as C. rewrite forallb_forall in C.
    specialize (C s Hin). cbv beta in C.
    apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
  - intros Ha. split.
    + intros Hn. pose proof mq_rsegs_len as L. rewrite Hn in L. discriminate L.
    + destruct mq_rsv_cover as (C1 & C2 & C3 & C4).
      destruct (Z_lt_ge_dec a 0x12000); [exact (mq_rsv_from _ _ a C1 ltac:(lia))|].
      destruct (Z_lt_ge_dec a 0x20000); [exact (mq_rsv_from _ _ a C2 ltac:(lia))|].
      destruct (Z_lt_ge_dec a 0x21000); [exact (mq_rsv_from _ _ a C3 ltac:(lia))|].
      exact (mq_rsv_from _ _ a C4 ltac:(lia)).
Qed.
