(* The slot LLVMFuzzerTestOneInput, plain image, op_write arm, segment B1: text_of's return (0x13fb8, cut
   c1_13fb8) through kernel, the inlined model_begin and model_write to model_write's return (0x13ff8, c1_13ff8).
   This file: the facts the three pieces of B1 share.
   - the numbers of the placement (lenv_ok) and of the image's reserved segments;
   - the addresses a piece may write (c1b1_al) and the transport of every other loop-memory fact across a
     write whose footprint lies there (c1b1_wok);
   - lh_mem cut into the part no piece of B1 writes (c1b1_static) and the parts kernel, model_begin and
     model_write change;
   - 32-bit fields of the model block and of g_nl as cells, and the blocks rebuilt after the stores;
   - the interface table, the selector's name, the texts strings (the image's .rodata bytes);
   - the two callee contracts taken apart (Pre / Wr / Post), and the two inner cut predicates of B1.
   Every address is read from the plain image (the unstripped twin of the pin ebe34b259b9f;
   link/ct/dis/plain/LLVMFuzzerTestOneInput.s 477-493). *)
From Stdlib Require Import Classical.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem printf_facts_c kernel_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Numbers
   ========================================================================== *)

Definition c1b1_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint c1b1_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => c1b1_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma c1b1_cov_in : forall L cur x, cur <= x < c1b1_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [c1b1_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

(* the image's reserved segments cover [0x10000, 0x97000) *)
Lemma c1b1_img_free : forall D n, 0 <= D -> 0 < n -> pf_img_free D n -> D + n <= 65536 \/ 618496 <= D.
Proof.
  intros D n HD Hn F.
  assert (EP : c1b1_cov (c1b1_ivs (segments_reserved rsegs)) 65536 = 618496) by (vm_compute; reflexivity).
  assert (C : forall x, 65536 <= x < 618496 -> exists s, In s (segments_reserved rsegs)
                /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. rewrite <- EP in Hx. destruct (c1b1_cov_in _ _ _ Hx) as (a & b & Hin & Hab).
    unfold c1b1_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). injection Es as Ea Eb.
    exists s. split; [exact Hs | lia]. }
  destruct (Z.lt_ge_cases D 65536) as [H1|H1].
  - destruct (Z.le_gt_cases (D + n) 65536) as [H2|H2]; [left; exact H2|].
    destruct (C 65536 ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F (65536 - D) ltac:(lia) s Hs). replace (D + (65536 - D)) with 65536 by lia. exact Hx.
  - destruct (Z.lt_ge_cases D 618496) as [H2|H2]; [|right; exact H2].
    destruct (C D ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

Lemma c1b1_lenv : forall E, lenv_ok E ->
  680160 <= e_S E /\ e_S E <= 2 ^ 47 /\
  4096 <= e_md E /\ e_md E + 8856 <= e_S E - 65536 /\ (e_md E + 8856 <= 65536 \/ 618496 <= e_md E) /\
  4096 <= e_mk E /\ e_mk E + 516 <= e_S E - 65536 /\ (e_mk E + 516 <= 65536 \/ 618496 <= e_mk E) /\
  (e_md E + 8856 <= e_mk E \/ e_mk E + 516 <= e_md E) /\
  1 <= Z.of_nat (length (e_pl E)) < 2 ^ 26 /\ 4096 <= e_p0 E /\
  e_p0 E + Z.of_nat (length (e_pl E)) <= e_S E - 65536 /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= 65536 \/ 618496 <= e_p0 E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_md E \/ e_md E + 8856 <= e_p0 E) /\
  (e_p0 E + Z.of_nat (length (e_pl E)) <= e_mk E \/ e_mk E + 516 <= e_p0 E) /\
  length (e_saved E) = 104%nat.
Proof.
  intros E (S1 & S2 & _ & (M1 & M2 & M3) & (K1 & K2 & K3) & _ & _ & D1 & L1 & (P1 & P2 & P3) & D2 & D3 & SV).
  unfold SLOT_STACK_Z, MD_SIZE, MK_SIZE in *.
  pose proof (c1b1_img_free (e_md E) 8856 ltac:(lia) ltac:(lia) M3) as I1.
  pose proof (c1b1_img_free (e_mk E) 516 ltac:(lia) ltac:(lia) K3) as I2.
  pose proof (c1b1_img_free (e_p0 E) (Z.of_nat (length (e_pl E))) ltac:(lia) ltac:(lia) P3) as I3.
  clear M3 K3 P3.
  split; [lia|].
  refine (conj S2 (conj M1 (conj M2 (conj I1 (conj K1 (conj K2 (conj I2 (conj D1
    (conj L1 (conj P1 (conj P2 (conj I3 (conj D2 (conj D3 SV)))))))))))))).
Qed.

(* a fact the walk tactics must not touch *)
Definition c1b1_keep (P : Prop) : Prop := P.

(* ==========================================================================
   2. Where a piece of B1 writes, and what survives it
   ========================================================================== *)

(* the stack window below the slot's frame, the cursor cells, g_nl below its interface table, the 301
   bytes of long_alias, the model block *)
Definition c1b1_al (E : lenv) (x : Z) : Prop :=
  (e_S E - 65536 <= x < e_S E - 480) \/ (e_S E - 416 <= x < e_S E - 400) \/
  (203648 <= x < 474672) \/ (476152 <= x < 476453) \/ (e_md E <= x < e_md E + 8856).

Definition c1b1_wok (E : lenv) (W : list ivl) : Prop :=
  forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> c1b1_al E x.

Definition c1b1_clr (W : list ivl) (a n : Z) : Prop := forall x, a <= x < a + n -> outside W x.

Lemma c1b1_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H].
  - destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
    + right. intros [H3 _]. apply H3. lia.
    + left. split; [lia | exact H].
    + left. split; [lia | exact H].
  - right. intros [_ H3]. exact (H H3).
Qed.

Lemma c1b1_clr_wok : forall E W a n, c1b1_wok E W -> 0 <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> ~ c1b1_al E x) -> c1b1_clr W a n.
Proof.
  intros E W a n HW H0 H1 HN x Hx. destruct (c1b1_outside_dec W x) as [O|O]; [exact O|].
  exfalso. apply (HN x Hx). apply HW; [lia | exact O].
Qed.

(* the addresses no piece of B1 writes: the image's constants, g_nl's interface table and g_names, the
   globals after long_alias up to the image's end, the slot's frame outside the cursor *)
Lemma c1b1_na : forall E x, lenv_ok E ->
  (65536 <= x < 203648 \/ 474672 <= x < 476152 \/ 476453 <= x < 614624 \/
   e_S E - 480 <= x < e_S E - 416 \/ e_S E - 400 <= x < e_S E) -> ~ c1b1_al E x.
Proof.
  intros E x HE Hx. destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & _).
  unfold c1b1_al. lia.
Qed.

Lemma c1b1_na_mk : forall E x, lenv_ok E -> e_mk E <= x < e_mk E + 516 -> ~ c1b1_al E x.
Proof.
  intros E x HE Hx. destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & K1 & K2 & K3 & D1 & _).
  unfold c1b1_al. lia.
Qed.

Lemma c1b1_na_pl : forall E x, lenv_ok E -> e_p0 E <= x < e_p0 E + Z.of_nat (length (e_pl E)) -> ~ c1b1_al E x.
Proof.
  intros E x HE Hx.
  destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & M3 & K1 & K2 & K3 & D1 & L1 & P1 & P2 & P3 & D2 & _).
  clear K1 K2 K3 D1. unfold c1b1_al. lia.
Qed.

Lemma c1b1_clr_na : forall E W a n, lenv_ok E -> c1b1_wok E W -> 0 <= a -> a + n <= 2 ^ 64 ->
  (forall x, a <= x < a + n -> 65536 <= x < 203648 \/ 474672 <= x < 476152 \/ 476453 <= x < 614624 \/
     e_S E - 480 <= x < e_S E - 416 \/ e_S E - 400 <= x < e_S E) -> c1b1_clr W a n.
Proof.
  intros E W a n HE HW H0 H1 H2. apply (c1b1_clr_wok E W a n HW H0 H1).
  intros x Hx. apply c1b1_na; [exact HE | apply H2; exact Hx].
Qed.

(* transports *)
Lemma c1b1_bytes_tr : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  c1b1_clr W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) MU C. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd. rewrite (MU (wa (a + Z.of_nat i))); [reflexivity|].
  rewrite wa_unsigned by lia. apply C. lia.
Qed.

Lemma c1b1_rw_tr : forall W m m' a cs, rw_cells rsegs m a cs -> munch W m m' -> wmono rsegs m m' ->
  c1b1_clr W a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' a cs.
Proof.
  intros W m m' a cs [[Hwf HB] HW] MU WM C. split; [split; [exact Hwf|]|].
  - eapply c1b1_bytes_tr; [exact HB | exact MU |]. rewrite cells_bytes_length by exact Hwf. exact C.
  - eapply wr_at_transport; eassumption.
Qed.

Lemma c1b1_u8_tr : forall W m m' a bs, u8arr rsegs m a bs -> munch W m m' -> wmono rsegs m m' ->
  c1b1_clr W a (Z.of_nat (length bs)) -> u8arr rsegs m' a bs.
Proof.
  intros W m m' a bs [HB HW] MU WM C.
  split; [eapply c1b1_bytes_tr; eassumption | eapply wr_at_transport; eassumption].
Qed.

Lemma c1b1_cstr_tr : forall W m m' a s, cstr_at m a s -> munch W m m' ->
  c1b1_clr W a (Z.of_nat (length s) + 1) -> cstr_at m' a s.
Proof.
  intros W m m' a s [HB HN] MU C. split; [|exact HN]. eapply c1b1_bytes_tr; [exact HB | exact MU |].
  replace (Z.of_nat (length (s ++ [zb 0]))) with (Z.of_nat (length s) + 1)
    by (rewrite length_app; cbn [length]; lia). exact C.
Qed.

Lemma c1b1_u64_tr : forall W m m' a v, u64_at m a v -> munch W m m' -> c1b1_clr W a 8 -> u64_at m' a v.
Proof.
  intros W m m' a v H MU C. unfold u64_at in *. eapply c1b1_bytes_tr; [exact H | exact MU |].
  rewrite length_le8. exact C.
Qed.

Lemma c1b1_u32_tr : forall W m m' a v, u32_at m a v -> munch W m m' -> c1b1_clr W a 4 -> u32_at m' a v.
Proof.
  intros W m m' a v H MU C. unfold u32_at in *. eapply c1b1_bytes_tr; [exact H | exact MU |].
  rewrite length_le4. exact C.
Qed.

(* the segment footprint and task_mem across a write inside c1b1_al *)
Lemma c1b1_segfp : forall E W m0 m m', seg_fp (e_S E) (c1_hp E) m0 m -> munch W m m' -> wmono rsegs m m' ->
  c1b1_wok E W -> seg_fp (e_S E) (c1_hp E) m0 m'.
Proof.
  intros E W m0 m m' H MU WM HW. eapply seg_fp_call; [exact H | exact MU | exact WM |].
  intros x Hx HO. specialize (HW x Hx HO). unfold c1b1_al in HW. unfold own_w, c1_hp.
  unfold SLOT_STACK_Z, A_G_NL, NK_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE.
  destruct HW as [H1|[H1|[H1|[H1|H1]]]].
  - left; lia.
  - left; lia.
  - right; left; lia.
  - right; right; right; left; lia.
  - right; right; right; right; right. exists (e_md E), MD_SIZE. split; [left; reflexivity | unfold MD_SIZE; lia].
Qed.

Lemma c1b1_task : forall E W m m', lenv_ok E -> MemNorm.task_mem rsegs m -> munch W m m' -> c1b1_wok E W ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros E W m m' HE HT MU HW a b Ha. pose proof (bv_unsigned_in_range 64 a) as Ra.
  change (bv_modulus 64) with (2 ^ 64) in Ra.
  destruct (c1b1_outside_dec W (bv_unsigned a)) as [HO|HO].
  - rewrite (MU a HO) in Ha. exact (HT a b Ha).
  - right. specialize (HW _ Ra HO). destruct (c1b1_lenv E HE) as (S1 & S2 & M1 & M2 & _).
    unfold c1b1_al in HW.
    assert (T : TASK_SIZE = 140737488355328) by reflexivity. rewrite T. lia.
Qed.

(* the alias text_of gave: its bytes are apart from every address a piece of B1 writes *)
Lemma c1b1_alok_tr : forall E m m' W s t sl, al_ok E m s t sl -> munch W m m' -> c1b1_wok E W ->
  al_ok E m' s t sl.
Proof.
  intros E m m' W s t sl (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) MU HW.
  refine (conj A1 (conj _ (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 A10))))))))).
  eapply c1b1_bytes_tr; [exact A2 | exact MU |].
  pose proof (bytes_at_bound rsegs _ _ _ A2) as B.
  apply (c1b1_clr_wok E W); [exact HW | lia | lia |].
  intros x Hx. unfold c1b1_al. unfold apart, apart_gnl in *. rewrite length_app in *. cbn [length] in *.
  unfold SLOT_STACK_Z, A_G_NL, NK_SIZE, A_LONG_ALIAS, MD_SIZE, A_ERRNO, A_TP, ERRNO_TP_OFF in *. lia.
Qed.

(* ==========================================================================
   3. The loop memory, cut
   ========================================================================== *)

Lemma c1b1_wr_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m A (n1 + n2) <-> wr_at rsegs m A n1 /\ wr_at rsegs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. split.
  - intros (Ha & Hn & H). split; (split; [lia|]; split; [lia|]); intros i Hi.
    + apply H. lia.
    + replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros [(Ha & Hn & H) (Hb & Hm & H')]. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_dec i n1); [apply H; lia|].
    replace (A + i) with (A + n1 + (i - n1)) by lia. apply H'. lia.
Qed.

Lemma c1b1_rw_app : forall m A B cs1 cs2, B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A (cs1 ++ cs2) <-> rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 ->. unfold rw_cells, cells_at.
  rewrite cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  pose proof (cells_wf_app cs1 cs2) as WA.
  split.
  - intros [[W12 HB] HW]. apply WA in W12. destruct W12 as [W1 W2].
    apply (proj1 (bytes_at_app rsegs _ _ _ _)) in HB. destruct HB as [B1 B2].
    rewrite cells_bytes_length in B2 by exact W1.
    apply (proj1 (c1b1_wr_app m A _ _ (Nat2Z.is_nonneg (cells_size cs1)) (Nat2Z.is_nonneg (cells_size cs2)))) in HW.
    destruct HW as [H1 H2].
    exact (conj (conj (conj W1 B1) H1) (conj (conj W2 B2) H2)).
  - intros [[[W1 B1] H1] [[W2 B2] H2]].
    split; [split; [apply WA; split; assumption|]|].
    + apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [exact B1|].
      rewrite cells_bytes_length by exact W1. exact B2.
    + apply (proj2 (c1b1_wr_app m A _ _ (Nat2Z.is_nonneg (cells_size cs1)) (Nat2Z.is_nonneg (cells_size cs2)))).
      split; assumption.
Qed.

(* the frame's first eight cells (sp .. sp + 0x40): the three scratch words and the five pointers *)
Definition c1b1_lo (E : lenv) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E)); C8 (wz A_G_NAMES);
   C8 (wz A_JT); C8 (wz GNL42)].

(* the part of the loop memory no piece of B1 writes *)
Definition c1b1_static (E : lenv) (gbs : list byte) (m : word -> option byte) : Prop :=
  (exists j0, rw_cells rsegs m (e_S E - SLOT_FRAME) (c1b1_lo E j0)) /\
  (exists j1 j2, rw_cells rsegs m (e_S E - SLOT_FRAME + FO_B40) [CB 40 j1; CB 256 j2]) /\
  bytes_at rsegs m (e_S E - 104) (e_saved E) /\
  gnames_at m /\ odd_at m /\ policy_ro m /\ texts_at m /\ ifptrs_at m /\
  marks_at m (e_mk E) gbs /\ bytes_at rsegs m (e_p0 E) (e_pl E) /\
  (exists sl, bytes_at rsegs m (A_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat) /\
  wr_at rsegs m A_ERRNO 4 /\ guard_m m.

Lemma c1b1_lh_split : forall E i P N kbs mbs gbs m, lh_mem E i P N kbs mbs gbs m ->
  c1b1_static E gbs m /\
  (exists nc, rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz nc)]) /\
  nlk_at m kbs /\ nlk_wf kbs /\ iftab_at m kbs link_tab /\
  nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs <= 64 * i /\
  (exists la, rw_cells rsegs m A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)]) /\
  model_at m (e_md E) mbs /\ model_wf mbs /\ marks_wf gbs /\ marks_are gbs mbs /\
  (exists k, 0 <= k <= Z.of_nat (length (e_pl E)) /\ P = e_p0 E + k /\ N = Z.of_nat (length (e_pl E)) - k).
Proof.
  intros E i P N kbs mbs gbs m
    ((j0 & j1 & j2 & nc & FR) & SV & NK & NW & IT & O1 & O2 & O3 & O4 & GN & OD & PR & (la & sl & LA1 & LA2 & LA3) &
     TX & IP & MD & MW & MK & KW & MA & (PLB & CK) & ER & GD).
  change (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2)
    with (c1b1_lo E j0 ++ [C8 (wz P); C8 (wz nc)] ++ [CB 40 j1; CB 256 j2]) in FR.
  assert (EQ1 : e_S E - SLOT_FRAME + FO_P = e_S E - SLOT_FRAME + Z.of_nat (cells_size (c1b1_lo E j0)))
    by (change (Z.of_nat (cells_size (c1b1_lo E j0))) with 64; unfold FO_P; lia).
  destruct (proj1 (c1b1_rw_app m _ _ _ _ EQ1) FR) as [FL FR2].
  assert (EQ2 : e_S E - SLOT_FRAME + FO_B40 = e_S E - SLOT_FRAME + FO_P + Z.of_nat (cells_size [C8 (wz P); C8 (wz nc)]))
    by (change (Z.of_nat (cells_size [C8 (wz P); C8 (wz nc)])) with 16; unfold FO_P, FO_B40; lia).
  destruct (proj1 (c1b1_rw_app m _ _ _ _ EQ2) FR2) as [FC FH].
  refine (conj _ (conj (ex_intro _ nc FC) (conj NK (conj NW (conj IT (conj O1 (conj O2 (conj O3 (conj O4
    (conj (ex_intro _ la LA1) (conj MD (conj MW (conj KW (conj MA CK)))))))))))))).
  refine (conj (ex_intro _ j0 FL) (conj (ex_intro _ j1 (ex_intro _ j2 FH)) (conj SV (conj GN (conj OD (conj PR
    (conj TX (conj IP (conj MK (conj PLB (conj (ex_intro _ sl (conj LA2 LA3)) (conj ER GD)))))))))))).
Qed.

Lemma c1b1_lh_join : forall E i P N kbs mbs gbs m,
  c1b1_static E gbs m ->
  (exists nc, rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz nc)]) ->
  nlk_at m kbs -> nlk_wf kbs -> iftab_at m kbs link_tab ->
  nk_open kbs = 0 -> nk_misuse kbs = 0 -> nk_opened kbs = nk_closed kbs -> nk_opened kbs <= 64 * i ->
  (exists la, rw_cells rsegs m A_LONG_ALIAS [CB (Z.to_nat 300) la; C1 (zb 0)]) ->
  model_at m (e_md E) mbs -> model_wf mbs -> marks_wf gbs -> marks_are gbs mbs ->
  (exists k, 0 <= k <= Z.of_nat (length (e_pl E)) /\ P = e_p0 E + k /\ N = Z.of_nat (length (e_pl E)) - k) ->
  lh_mem E i P N kbs mbs gbs m.
Proof.
  intros E i P N kbs mbs gbs m
    ((j0 & FL) & (j1 & j2 & FH) & SV & GN & OD & PR & TX & IP & MK & PLB & (sl & LA2 & LA3) & ER & GD)
    (nc & FC) NK NW IT O1 O2 O3 O4 (la & LA1) MD MW KW MA CK.
  assert (FR : rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2)).
  { change (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2)
      with (c1b1_lo E j0 ++ [C8 (wz P); C8 (wz nc)] ++ [CB 40 j1; CB 256 j2]).
    assert (EQ1 : e_S E - SLOT_FRAME + FO_P = e_S E - SLOT_FRAME + Z.of_nat (cells_size (c1b1_lo E j0)))
      by (change (Z.of_nat (cells_size (c1b1_lo E j0))) with 64; unfold FO_P; lia).
    assert (EQ2 : e_S E - SLOT_FRAME + FO_B40 = e_S E - SLOT_FRAME + FO_P + Z.of_nat (cells_size [C8 (wz P); C8 (wz nc)]))
      by (change (Z.of_nat (cells_size [C8 (wz P); C8 (wz nc)])) with 16; unfold FO_P, FO_B40; lia).
    apply (proj2 (c1b1_rw_app m _ _ _ _ EQ1)). split; [exact FL|].
    apply (proj2 (c1b1_rw_app m _ _ _ _ EQ2)). split; [exact FC | exact FH]. }
  refine (conj (ex_intro _ j0 (ex_intro _ j1 (ex_intro _ j2 (ex_intro _ nc FR)))) (conj SV (conj NK (conj NW
    (conj IT (conj O1 (conj O2 (conj O3 (conj O4 (conj GN (conj OD (conj PR
    (conj (ex_intro _ la (ex_intro _ sl (conj LA1 (conj LA2 LA3)))) (conj TX (conj IP (conj MD (conj MW
    (conj MK (conj KW (conj MA (conj (conj PLB CK) (conj ER GD)))))))))))))))))))))).
Qed.

(* the bounds of the image's tables *)
Lemma c1b1_odd_bnd : forall k, (k < 6)%nat ->
  65536 <= nth k odd_ptrs 0 /\ nth k odd_ptrs 0 + Z.of_nat (length (nth k odd_strs [])) + 1 <= 73396.
Proof.
  intros k Hk.
  assert (B : forallb (fun k => (65536 <=? nth k odd_ptrs 0) &&
                (nth k odd_ptrs 0 + Z.of_nat (length (nth k odd_strs [])) + 1 <=? 73396)) (seq 0 6) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B k (proj2 (in_seq 6 0 k) (conj (Nat.le_0_l k) Hk))).
  apply andb_prop in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

Lemma c1b1_link_len : length link_tab = 64%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma c1b1_link_bnd : forall k, (k < 64)%nat ->
  65536 <= nth k link_ptrs 0 /\
  nth k link_ptrs 0 + Z.of_nat (length (fst (nth k link_tab ([], 0)))) + 1 <= 476152 /\
  (nth k link_ptrs 0 + Z.of_nat (length (fst (nth k link_tab ([], 0)))) + 1 <= 73396 \/
   475640 <= nth k link_ptrs 0).
Proof.
  intros k Hk.
  assert (B : forallb (fun k => (65536 <=? nth k link_ptrs 0) &&
                (nth k link_ptrs 0 + Z.of_nat (length (fst (nth k link_tab ([], 0)))) + 1 <=? 476152) &&
                ((nth k link_ptrs 0 + Z.of_nat (length (fst (nth k link_tab ([], 0)))) + 1 <=? 73396) ||
                 (475640 <=? nth k link_ptrs 0))) (seq 0 64) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B k (proj2 (in_seq 64 0 k) (conj (Nat.le_0_l k) Hk))).
  apply andb_prop in B. destruct B as [B12 B3]. apply andb_prop in B12. destruct B12 as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply orb_prop in B3.
  destruct B3 as [B3|B3]; apply Z.leb_le in B3; lia.
Qed.

Lemma c1b1_static_tr : forall E gbs m m' W, lenv_ok E -> c1b1_static E gbs m -> munch W m m' -> wmono rsegs m m' ->
  c1b1_wok E W -> c1b1_static E gbs m'.
Proof.
  intros E gbs m m' W HE (FL & FH & SV & GN & OD & PR & TX & IP & MK & PL & LS & ER & GD) MU WM HW.
  destruct (c1b1_lenv E HE) as (S1 & S2 & _ & _ & _ & _ & _ & _ & _ & L1 & P1 & P2 & _ & _ & _ & SL).
  pose proof (fun a n => c1b1_clr_na E W a n HE HW) as NA.
  unfold c1b1_static. unfold SLOT_FRAME, FO_B40 in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))).
  - destruct FL as [j0 FL]. exists j0. eapply c1b1_rw_tr; [exact FL | exact MU | exact WM |].
    change (Z.of_nat (cells_size (c1b1_lo E j0))) with 64. apply NA; [lia | lia | intros x Hx; lia].
  - destruct FH as (j1 & j2 & FH). exists j1, j2. eapply c1b1_rw_tr; [exact FH | exact MU | exact WM |].
    change (Z.of_nat (cells_size [CB 40 j1; CB 256 j2])) with 296. apply NA; [lia | lia | intros x Hx; lia].
  - eapply c1b1_bytes_tr; [exact SV | exact MU |]. rewrite SL. change (Z.of_nat 104) with 104.
    apply NA; [lia | lia | intros x Hx; lia].
  - intros k Hk. destruct (GN k Hk) as (rest & B & L). exists rest. split; [|exact L].
    eapply c1b1_bytes_tr; [exact B | exact MU |]. rewrite L. change (Z.of_nat 8) with 8.
    unfold A_G_NAMES. apply NA; [lia | lia | intros x Hx; lia].
  - intros k Hk. destruct (OD k Hk) as [U C]. pose proof (c1b1_odd_bnd k Hk) as B. split.
    + eapply c1b1_u64_tr; [exact U | exact MU |]. unfold A_ODD. apply NA; [lia | lia | intros x Hx; lia].
    + eapply c1b1_cstr_tr; [exact C | exact MU |]. apply NA; [lia | lia | intros x Hx; lia].
  - destruct PR as (C1 & C2 & C3 & C4). unfold policy_ro. unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY in *.
    refine (conj _ (conj _ (conj _ _))); (eapply c1b1_cstr_tr; [eassumption | exact MU |]).
    + change (Z.of_nat (length S_PREFIX)) with 8. apply NA; [lia | lia | intros x Hx; lia].
    + change (Z.of_nat (length S_SERVED)) with 14. apply NA; [lia | lia | intros x Hx; lia].
    + change (Z.of_nat (length S_VLAN)) with 4. apply NA; [lia | lia | intros x Hx; lia].
    + change (Z.of_nat (length (@nil byte))) with 0. apply NA; [lia | lia | intros x Hx; lia].
  - intros k Hk. eapply c1b1_u64_tr; [exact (TX k Hk) | exact MU |]. unfold A_TEXTS.
    apply NA; [lia | lia | intros x Hx; lia].
  - intros k Hk. eapply c1b1_u64_tr; [exact (IP k Hk) | exact MU |]. unfold A_G_NL, NK_IF_NAME.
    apply NA; [lia | lia | intros x Hx; lia].
  - destruct MK as [MK ML]. split; [|exact ML]. eapply c1b1_u8_tr; [exact MK | exact MU | exact WM |].
    rewrite ML. unfold MK_SIZE. pose proof (c1b1_lenv E HE) as F.
    apply (c1b1_clr_wok E W); [exact HW | lia | lia |]. intros x Hx. apply c1b1_na_mk; [exact HE | exact Hx].
  - eapply c1b1_bytes_tr; [exact PL | exact MU |].
    apply (c1b1_clr_wok E W); [exact HW | lia | lia |]. intros x Hx. apply c1b1_na_pl; [exact HE | exact Hx].
  - destruct LS as (sl & B & L). exists sl. split; [|exact L]. eapply c1b1_bytes_tr; [exact B | exact MU |].
    rewrite L. change (Z.of_nat 3) with 3. unfold A_LONG_ALIAS, LONG_ALIAS_SIZE.
    apply NA; [lia | lia | intros x Hx; lia].
  - eapply wr_at_transport; [exact ER | exact WM].
  - destruct GD as (G1 & c & G2). split.
    + eapply c1b1_bytes_tr; [exact G1 | exact MU |]. rewrite length_le8. change (Z.of_nat 8) with 8.
      unfold A_GOT_GUARD_S. apply NA; [lia | lia | intros x Hx; lia].
    + exists c. eapply c1b1_bytes_tr; [exact G2 | exact MU |]. rewrite length_le8. change (Z.of_nat 8) with 8.
      unfold A_GUARD_S. apply NA; [lia | lia | intros x Hx; lia].
Qed.

(* the own cell sp + 0x78 *)
Lemma c1b1_own_tr : forall E m m' W own, lenv_ok E ->
  bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) -> munch W m m' -> c1b1_wok E W ->
  bytes_at rsegs m' (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)).
Proof.
  intros E m m' W own HE H MU HW. destruct (c1b1_lenv E HE) as (S1 & S2 & _).
  eapply c1b1_bytes_tr; [exact H | exact MU |]. rewrite length_le8. change (Z.of_nat 8) with 8.
  unfold SLOT_FRAME, FO_B256. apply (c1b1_clr_na E W); [exact HE | exact HW | lia | lia | intros x Hx; lia].
Qed.

(* ==========================================================================
   4. Fields, slices, blocks
   ========================================================================== *)

Lemma c1b1_Z_to_le_bytes_of_bytes : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  pose proof (bytes_le_to_Z_nonneg l) as Nl.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned.
    change (bv_wrap 8 (bv_unsigned b + 256 * bytes_le_to_Z l))
      with ((bv_unsigned b + 256 * bytes_le_to_Z l) mod 2 ^ 8).
    change (2 ^ 8) with 256. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z l) / 256) with (bytes_le_to_Z l); [exact IH|].
    rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma c1b1_firstn_plus : forall {A} k1 k2 (l : list A), firstn (k1 + k2) l = firstn k1 l ++ firstn k2 (skipn k1 l).
Proof.
  intros A k1. induction k1 as [|k1 IH]; intros k2 l; [reflexivity|].
  destruct l as [|x l]; [destruct k2; reflexivity|].
  cbn. f_equal. apply IH.
Qed.

Lemma c1b1_list_eq_nth : forall {A} (l1 l2 : list A), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. inversion H0; subst. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

Lemma c1b1_slice_length : forall bs a n, 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length bs) ->
  length (slice bs a n) = Z.to_nat n.
Proof. intros bs a n H0 H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma c1b1_slice_split : forall bs a n1 n2, 0 <= a -> 0 <= n1 -> 0 <= n2 ->
  slice bs a (n1 + n2) = slice bs a n1 ++ slice bs (a + n1) n2.
Proof.
  intros bs a n1 n2 Ha H1 H2. unfold slice. rewrite Z2Nat.inj_add by lia. rewrite c1b1_firstn_plus.
  f_equal. rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma c1b1_slice_app_l : forall l r a n, 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length l) ->
  slice (l ++ r) a n = slice l a n.
Proof.
  intros l r a n Ha Hn H. unfold slice.
  rewrite skipn_app. replace (Z.to_nat a - length l)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app, length_skipn. replace (Z.to_nat n - (length l - Z.to_nat a))%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

Lemma c1b1_slice_app_r : forall l r a n, Z.of_nat (length l) <= a ->
  slice (l ++ r) a n = slice r (a - Z.of_nat (length l)) n.
Proof.
  intros l r a n H. unfold slice.
  rewrite skipn_app, skipn_all2 by lia. cbn [app]. f_equal. f_equal. lia.
Qed.

Lemma c1b1_slice_firstn : forall bs k a n, 0 <= a -> 0 <= n -> a + n <= Z.of_nat k ->
  slice (firstn k bs) a n = slice bs a n.
Proof.
  intros bs k a n Ha Hn H. unfold slice. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma c1b1_slice_skipn : forall bs k a n, Z.of_nat k <= a ->
  slice (skipn k bs) (a - Z.of_nat k) n = slice bs a n.
Proof. intros bs k a n H. unfold slice. rewrite skipn_skipn. f_equal. f_equal. lia. Qed.

Lemma c1b1_slice_upd_out : forall bs k l a n, 0 <= a -> 0 <= n ->
  (k + length l <= length bs)%nat ->
  a + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length l) <= a ->
  slice (upd_bytes bs k l) a n = slice bs a n.
Proof.
  intros bs k l a n Ha Hn Hk [H|H]; unfold upd_bytes.
  - rewrite c1b1_slice_app_l by (rewrite ?length_firstn; lia). apply c1b1_slice_firstn; lia.
  - rewrite app_assoc. rewrite c1b1_slice_app_r by (rewrite ?length_app, ?length_firstn; lia).
    rewrite length_app, length_firstn.
    replace (Z.of_nat (Nat.min k (length bs) + length l)) with (Z.of_nat (k + length l)) by lia.
    apply c1b1_slice_skipn. lia.
Qed.

Lemma c1b1_slice_upd_in : forall bs k l a n, 0 <= n ->
  (k + length l <= length bs)%nat -> Z.of_nat k <= a -> a + n <= Z.of_nat k + Z.of_nat (length l) ->
  slice (upd_bytes bs k l) a n = slice l (a - Z.of_nat k) n.
Proof.
  intros bs k l a n Hn Hk H1 H2. unfold upd_bytes.
  rewrite c1b1_slice_app_r by (rewrite ?length_firstn; lia).
  rewrite length_firstn. replace (Z.of_nat (Nat.min k (length bs))) with (Z.of_nat k) by lia.
  apply c1b1_slice_app_l; lia.
Qed.

Lemma c1b1_rdn_upd_out : forall bs k l a n, 0 <= a -> 0 <= n ->
  (k + length l <= length bs)%nat ->
  a + n <= Z.of_nat k \/ Z.of_nat k + Z.of_nat (length l) <= a ->
  link_spec.rdn (upd_bytes bs k l) a n = link_spec.rdn bs a n.
Proof. intros. unfold link_spec.rdn. f_equal. apply c1b1_slice_upd_out; assumption. Qed.

Lemma c1b1_rdn_upd_in : forall bs k l a n, 0 <= n ->
  (k + length l <= length bs)%nat -> Z.of_nat k <= a -> a + n <= Z.of_nat k + Z.of_nat (length l) ->
  link_spec.rdn (upd_bytes bs k l) a n = link_spec.rdn l (a - Z.of_nat k) n.
Proof. intros. unfold link_spec.rdn. f_equal. apply c1b1_slice_upd_in; assumption. Qed.

Lemma c1b1_rdn_le4_slice : forall bs a, 0 <= a -> a + 4 <= Z.of_nat (length bs) ->
  slice bs a 4 = le4 (wz (link_spec.rdn bs a 4)).
Proof.
  intros bs a H0 H1. unfold le4, wz, link_spec.rdn.
  pose proof (c1b1_slice_length bs a 4 H0 ltac:(lia) H1) as L. change (Z.to_nat 4) with 4%nat in L.
  pose proof (bytes_le_to_Z_nonneg (slice bs a 4)) as N.
  pose proof (bytes_le_to_Z_bound (slice bs a 4)) as B. rewrite L in B.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in B.
  rewrite unsigned_lit by lia.
  transitivity (Z_to_le_bytes (length (slice bs a 4)) (bytes_le_to_Z (slice bs a 4))).
  - symmetry. apply c1b1_Z_to_le_bytes_of_bytes.
  - rewrite L. reflexivity.
Qed.

Lemma c1b1_rdn_le4_head : forall w r a, a = 0 -> link_spec.rdn (le4 w ++ r) a 4 = bv_unsigned w mod 2 ^ 32.
Proof.
  intros w r a ->. unfold link_spec.rdn. rewrite c1b1_slice_app_l by (rewrite ?length_le4; lia).
  unfold slice. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 4) with 4%nat. cbn [skipn].
  rewrite <- (length_le4 w) at 1. rewrite firstn_all. apply bytes_le_to_Z_le4.
Qed.

Lemma c1b1_rdn_le4_cons : forall w r a n, 4 <= a -> link_spec.rdn (le4 w ++ r) a n = link_spec.rdn r (a - 4) n.
Proof.
  intros. unfold link_spec.rdn. rewrite c1b1_slice_app_r by (rewrite ?length_le4; lia). rewrite length_le4. reflexivity.
Qed.

Lemma c1b1_rdn_le4_0 : forall w, link_spec.rdn (le4 w) 0 4 = bv_unsigned w mod 2 ^ 32.
Proof. intros w. rewrite <- (app_nil_r (le4 w)). apply c1b1_rdn_le4_head. reflexivity. Qed.

Lemma c1b1_sx32_wz : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v H. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_wrap 32 (v + 2 ^ 31)) with ((v + 2 ^ 31) mod 2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma c1b1_wr_sub : forall m a n k j, wr_at rsegs m a n -> 0 <= k -> 0 <= j -> k + j <= n ->
  wr_at rsegs m (a + k) j.
Proof.
  intros m a n k j (H0 & H1 & H) Hk Hj Hkj. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

(* the cells of a run of bytes inside a block *)
Lemma c1b1_u8_cells : forall m A bs off cs a, u8arr rsegs m A bs -> 0 <= off -> cells_wf cs ->
  off + Z.of_nat (cells_size cs) <= Z.of_nat (length bs) ->
  cells_bytes cs = slice bs off (Z.of_nat (cells_size cs)) -> a = A + off -> rw_cells rsegs m a cs.
Proof.
  intros m A bs off cs a [HB HW] H0 Hwf Hsz HC ->.
  split; [split; [exact Hwf|]|].
  - rewrite HC. unfold slice. rewrite Nat2Z.id.
    pose proof (CB3_bytes (Z.to_nat off) (cells_size cs) bs ltac:(lia)) as E3. rewrite <- E3 in HB.
    apply bytes_at_app in HB. destruct HB as [_ HB]. apply bytes_at_app in HB. destruct HB as [HB _].
    rewrite length_firstn in HB.
    replace (A + Z.of_nat (Nat.min (Z.to_nat off) (length bs))) with (A + off) in HB by lia. exact HB.
  - apply c1b1_wr_sub with (n := Z.of_nat (length bs)); [exact HW | lia | lia | lia].
Qed.

Fixpoint c1b1_u32c (bs : list byte) (off : Z) (n : nat) : list cell :=
  match n with
  | O => []
  | S n' => C4 (wz (fld_u32 bs off)) :: c1b1_u32c bs (off + 4) n'
  end.

Lemma c1b1_u32c_wf : forall n bs off, cells_wf (c1b1_u32c bs off n).
Proof. induction n as [|n IH]; intros; cbn; [exact I | split; [exact I | apply IH]]. Qed.

Lemma c1b1_u32c_size : forall n bs off, cells_size (c1b1_u32c bs off n) = (4 * n)%nat.
Proof. induction n as [|n IH]; intros; cbn [c1b1_u32c cells_size csize]; [reflexivity|]. rewrite IH. lia. Qed.

Lemma c1b1_u32c_bytes : forall n bs off, 0 <= off -> off + 4 * Z.of_nat n <= Z.of_nat (length bs) ->
  cells_bytes (c1b1_u32c bs off n) = slice bs off (4 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intros bs off H0 H1.
  - cbn [c1b1_u32c cells_bytes]. unfold slice. change (4 * Z.of_nat 0) with 0. reflexivity.
  - cbn [c1b1_u32c cells_bytes cbytes]. rewrite IH by lia.
    replace (4 * Z.of_nat (S n)) with (4 + 4 * Z.of_nat n) by lia.
    rewrite c1b1_slice_split by lia. f_equal. symmetry. apply c1b1_rdn_le4_slice; lia.
Qed.

Lemma c1b1_u8_u32c : forall m A bs off n a, u8arr rsegs m A bs -> 0 <= off ->
  off + 4 * Z.of_nat n <= Z.of_nat (length bs) -> a = A + off -> rw_cells rsegs m a (c1b1_u32c bs off n).
Proof.
  intros m A bs off n a H H0 H1 Ha. eapply c1b1_u8_cells; [exact H | exact H0 | apply c1b1_u32c_wf | | | exact Ha].
  - rewrite c1b1_u32c_size. lia.
  - rewrite c1b1_u32c_bytes by lia. rewrite c1b1_u32c_size. f_equal. lia.
Qed.

(* a block after stores at one or two runs inside it, and every other byte untouched *)
Lemma c1b1_u8_patch2 : forall W m m' A bs o1 x1 o2 x2 a1 a2,
  u8arr rsegs m A bs -> munch W m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' a1 x1 -> bytes_at rsegs m' a2 x2 -> a1 = A + o1 -> a2 = A + o2 ->
  0 <= o1 -> o1 + Z.of_nat (length x1) <= o2 -> o2 + Z.of_nat (length x2) <= Z.of_nat (length bs) ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> ~ (A + o1 <= x < A + o1 + Z.of_nat (length x1)) ->
     ~ (A + o2 <= x < A + o2 + Z.of_nat (length x2)) -> outside W x) ->
  u8arr rsegs m' A (upd_bytes (upd_bytes bs (Z.to_nat o1) x1) (Z.to_nat o2) x2).
Proof.
  intros W m m' A bs o1 x1 o2 x2 a1 a2 [(HA & HL & HB) HW] MU WM (_ & _ & B1) (_ & _ & B2) -> -> H1 H2 H3 HO.
  assert (L1 : length (upd_bytes bs (Z.to_nat o1) x1) = length bs) by (apply upd_bytes_length; lia).
  assert (L2 : length (upd_bytes (upd_bytes bs (Z.to_nat o1) x1) (Z.to_nat o2) x2) = length bs)
    by (rewrite upd_bytes_length; [exact L1 | rewrite L1; lia]).
  split; [|rewrite L2; eapply wr_at_transport; eassumption].
  split; [exact HA|]. split; [rewrite L2; exact HL|].
  intros i Hi. rewrite L2 in Hi.
  rewrite upd_bytes_nth by (rewrite ?L1; lia).
  match goal with |- context [if ?c then _ else _] => destruct c eqn:C2 end.
  - apply andb_prop in C2. destruct C2 as [C2a C2b]. apply Nat.leb_le in C2a. apply Nat.ltb_lt in C2b.
    rewrite <- (B2 (i - Z.to_nat o2)%nat) by lia. f_equal. f_equal. lia.
  - rewrite upd_bytes_nth by lia.
    match goal with |- context [if ?c then _ else _] => destruct c eqn:C1 end.
    + apply andb_prop in C1. destruct C1 as [C1a C1b]. apply Nat.leb_le in C1a. apply Nat.ltb_lt in C1b.
      rewrite <- (B1 (i - Z.to_nat o1)%nat) by lia. f_equal. f_equal. lia.
    + rewrite <- (HB i Hi). unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [reflexivity|].
      rewrite wa_unsigned by lia.
      apply andb_false_iff in C1. apply andb_false_iff in C2.
      apply HO; [lia | ..].
      * destruct C1 as [C1|C1]; [apply Nat.leb_gt in C1 | apply Nat.ltb_ge in C1]; lia.
      * destruct C2 as [C2|C2]; [apply Nat.leb_gt in C2 | apply Nat.ltb_ge in C2]; lia.
Qed.

Lemma c1b1_u8_patch1 : forall W m m' A bs o x a,
  u8arr rsegs m A bs -> munch W m m' -> wmono rsegs m m' -> bytes_at rsegs m' a x -> a = A + o ->
  0 <= o -> o + Z.of_nat (length x) <= Z.of_nat (length bs) ->
  (forall y, A <= y < A + Z.of_nat (length bs) -> ~ (A + o <= y < A + o + Z.of_nat (length x)) -> outside W y) ->
  u8arr rsegs m' A (upd_bytes bs (Z.to_nat o) x).
Proof.
  intros W m m' A bs o x a [(HA & HL & HB) HW] MU WM (_ & _ & B1) -> H1 H2 HO.
  assert (L1 : length (upd_bytes bs (Z.to_nat o) x) = length bs) by (apply upd_bytes_length; lia).
  split; [|rewrite L1; eapply wr_at_transport; eassumption].
  split; [exact HA|]. split; [rewrite L1; exact HL|].
  intros i Hi. rewrite L1 in Hi.
  rewrite upd_bytes_nth by lia.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:C1 end.
  - apply andb_prop in C1. destruct C1 as [C1a C1b]. apply Nat.leb_le in C1a. apply Nat.ltb_lt in C1b.
    rewrite <- (B1 (i - Z.to_nat o)%nat) by lia. f_equal. f_equal. lia.
  - rewrite <- (HB i Hi). unfold mrd. rewrite (MU (wa (A + Z.of_nat i))); [reflexivity|].
    rewrite wa_unsigned by lia.
    apply andb_false_iff in C1. apply HO; [lia |].
    destruct C1 as [C1|C1]; [apply Nat.leb_gt in C1 | apply Nat.ltb_ge in C1]; lia.
Qed.

(* ==========================================================================
   5. Pointers, strings, the interface table
   ========================================================================== *)

Lemma c1b1_bytes_unique : forall m a l1 l2,
  bytes_at rsegs m a l1 -> bytes_at rsegs m a l2 -> length l1 = length l2 -> l1 = l2.
Proof.
  intros m a l1 l2 (_ & _ & H1) (_ & _ & H2) L. apply c1b1_list_eq_nth. intros i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hi|Hi].
  - rewrite <- H1, <- H2 by lia. reflexivity.
  - rewrite (proj2 (nth_error_None l1 i)), (proj2 (nth_error_None l2 i)) by lia. reflexivity.
Qed.

Lemma c1b1_u64_eq : forall m a p q, u64_at m a p -> u64_at m a q -> wz p = wz q.
Proof.
  intros m a p q Hp Hq. unfold u64_at in *.
  pose proof (c1b1_bytes_unique m a _ _ Hp Hq ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 (wz p)), <- (le_bytes_to_word_le8 (wz q)), E. reflexivity.
Qed.

Lemma c1b1_wz_eq : forall p q, wz p = wz q -> 0 <= q < 2 ^ 64 -> exists k, p = q + 2 ^ 64 * k.
Proof.
  intros p q E Hq. apply (f_equal bv_unsigned) in E. unfold wz in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E. change (2 ^ Z.of_N 64) with (2 ^ 64) in E.
  rewrite (Z.mod_small q) in E by lia.
  exists (p / 2 ^ 64). pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as D. lia.
Qed.

Lemma c1b1_cstr_unique : forall s1 s2 m a, cstr_at m a s1 -> cstr_at m a s2 -> s1 = s2.
Proof.
  induction s1 as [|b1 s1 IH]; intros [|b2 s2] m a (B1 & N1) (B2 & N2).
  - reflexivity.
  - exfalso. destruct B1 as (_ & _ & H1). destruct B2 as (_ & _ & H2).
    specialize (H1 0%nat ltac:(cbn; lia)). specialize (H2 0%nat ltac:(cbn [length app]; lia)).
    rewrite H1 in H2. cbn [nth_error app] in H2. injection H2 as E0. apply N2. left. symmetry. exact E0.
  - exfalso. destruct B1 as (_ & _ & H1). destruct B2 as (_ & _ & H2).
    specialize (H1 0%nat ltac:(cbn [length app]; lia)). specialize (H2 0%nat ltac:(cbn; lia)).
    rewrite H1 in H2. cbn [nth_error app] in H2. injection H2 as E0. apply N1. left. exact E0.
  - assert (Eb : b1 = b2).
    { destruct B1 as (_ & _ & H1). destruct B2 as (_ & _ & H2).
      specialize (H1 0%nat ltac:(cbn [length app]; lia)). specialize (H2 0%nat ltac:(cbn [length app]; lia)).
      rewrite H1 in H2. cbn [nth_error app] in H2. injection H2 as E0. exact E0. }
    subst b2. f_equal. apply (IH s2 m (a + 1)).
    + split; [|intros Hin; apply N1; right; exact Hin].
      destruct B1 as (Ha & Hl & H1). cbn [length app] in Hl.
      split; [lia|]. split; [cbn [length app] in *; lia|].
      intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply (H1 (S i)).
      cbn [length app] in *. lia.
    + split; [|intros Hin; apply N2; right; exact Hin].
      destruct B2 as (Ha & Hl & H2). cbn [length app] in Hl.
      split; [lia|]. split; [cbn [length app] in *; lia|].
      intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. apply (H2 (S i)).
      cbn [length app] in *. lia.
Qed.

Lemma c1b1_nth_error_nth : forall {A} (l : list A) i d, (i < length l)%nat -> nth_error l i = Some (nth i l d).
Proof.
  intros A l. induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.

(* a name the interface table points at, read through any table iftab_at accepts over the same g_nl:
   it is link_tab's name at the same index, at link_ptrs' address *)
Lemma c1b1_ifname : forall m kbs tab i nm ix p,
  iftab_at m kbs link_tab -> ifptrs_at m -> iftab_at m kbs tab -> nth_error tab i = Some (nm, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  (i < 64)%nat /\ wz p = wz (nth i link_ptrs 0) /\ nm = fst (nth i link_tab ([], 0)) /\
  cstr_at m (nth i link_ptrs 0) nm.
Proof.
  intros m kbs tab i nm ix p (L1 & _ & T1) IP (L2 & _ & T2) Hn U.
  assert (Hi : (i < 64)%nat).
  { pose proof (nth_error_lt tab i (nm, ix) Hn) as Hl. rewrite c1b1_link_len in L1. lia. }
  pose proof (IP i Hi) as UL.
  destruct (T2 i nm ix Hn) as (_ & p2 & U2 & _ & C2 & _).
  pose proof (c1b1_nth_error_nth link_tab i ([], 0) ltac:(rewrite c1b1_link_len; exact Hi)) as Hl.
  destruct (nth i link_tab ([], 0)) as [nm1 ix1] eqn:EN. cbn [fst].
  try rewrite EN in Hl.
  destruct (T1 i nm1 ix1 Hl) as (_ & p1 & U1 & _ & C1 & _).
  pose proof (c1b1_link_bnd i Hi) as B. rewrite EN in B. cbn [fst] in B.
  assert (E2 : p2 = nth i link_ptrs 0).
  { destruct (c1b1_wz_eq p2 (nth i link_ptrs 0) (c1b1_u64_eq _ _ _ _ U2 UL) ltac:(lia)) as [k Hk].
    destruct C2 as [C2 _]. pose proof (bytes_at_bound rsegs _ _ _ C2) as BB. lia. }
  assert (E1 : p1 = nth i link_ptrs 0).
  { destruct (c1b1_wz_eq p1 (nth i link_ptrs 0) (c1b1_u64_eq _ _ _ _ U1 UL) ltac:(lia)) as [k Hk].
    destruct C1 as [C1' _]. pose proof (bytes_at_bound rsegs _ _ _ C1') as BB. lia. }
  subst p1 p2.
  refine (conj Hi (conj (c1b1_u64_eq _ _ _ _ U UL) (conj _ C2))).
  exact (c1b1_cstr_unique _ _ _ _ C2 C1).
Qed.

(* iftab_at over link_tab across a write that misses g_nl's table, the image's .rodata and g_names *)
Lemma c1b1_iftab_tr : forall W m m' kbs kbs',
  iftab_at m kbs link_tab -> ifptrs_at m -> munch W m m' ->
  c1b1_clr W 474672 968 -> c1b1_clr W 65536 8000 -> c1b1_clr W 475640 512 ->
  nk_n_if kbs' = nk_n_if kbs -> iftab_at m' kbs' link_tab.
Proof.
  intros W m m' kbs kbs' IT IP MU C1 C2 C3 EN.
  pose proof IT as (L & L80 & T). split; [rewrite EN; exact L|]. split; [exact L80|].
  intros i nm ix Hn. destruct (T i nm ix Hn) as (Hix & p & U & P0 & C & U32).
  split; [exact Hix|]. exists p.
  destruct (c1b1_ifname m kbs link_tab i nm ix p IT IP IT Hn U) as (Hi & Ep & Enm & _).
  pose proof (c1b1_link_bnd i Hi) as B. rewrite <- Enm in B.
  assert (Pe : p = nth i link_ptrs 0).
  { destruct (c1b1_wz_eq p (nth i link_ptrs 0) Ep ltac:(lia)) as [k Hk].
    destruct C as [C' _]. pose proof (bytes_at_bound rsegs _ _ _ C') as BB. lia. }
  refine (conj _ (conj P0 (conj _ _))).
  - eapply c1b1_u64_tr; [exact U | exact MU |]. intros x Hx. apply C1. unfold A_G_NL, NK_IF_NAME in Hx. lia.
  - eapply c1b1_cstr_tr; [exact C | exact MU |]. intros x Hx. subst p.
    destruct B as (B1 & B2 & [B3|B3]); [apply C2 | apply C3]; lia.
  - eapply c1b1_u32_tr; [exact U32 | exact MU |]. intros x Hx. apply C1. unfold A_G_NL, NK_IF_INDEX in Hx. lia.
Qed.

(* the texts strings: the image's .rodata bytes up to the NUL, and the bytes strlen reads after it *)
Fixpoint c1b1_rstr (fuel : nat) (a : Z) : list byte :=
  match fuel with
  | O => []
  | S f => match seg_rom rsegs (wa a) with
           | Some b => if bz b =? 0 then [] else b :: c1b1_rstr f (a + 1)
           | None => []
           end
  end.

Definition c1b1_rslack (p : Z) (s : list byte) : list byte :=
  match image_bytes rsegs (p + Z.of_nat (length s) + 1) (Z.to_nat ((- (p + Z.of_nat (length s) + 1)) mod 8)) with
  | Some l => l
  | None => []
  end.

Definition c1b1_rok (p : Z) : bool :=
  let s := c1b1_rstr 64 p in
  let sl := c1b1_rslack p s in
  ro_bytes_b rsegs p (s ++ zb 0 :: sl) && negb (existsb (fun b => bz b =? 0) s) &&
  (Z.of_nat (length s) <? 4096) && (65536 <=? p) &&
  (p + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <=? 73396) &&
  ((- (p + Z.of_nat (length s) + 1)) mod 8 <=? Z.of_nat (length sl)).

Lemma c1b1_rok_sound : forall m p, mem_inv rsegs m -> c1b1_rok p = true ->
  exists s slack, bytes_at rsegs m p (s ++ zb 0 :: slack) /\ ~ In (zb 0) s /\
    (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
    Z.of_nat (length s) < 4096 /\ 65536 <= p /\
    p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= 73396.
Proof.
  intros m p MI H. unfold c1b1_rok in H.
  set (s := c1b1_rstr 64 p) in H. set (sl := c1b1_rslack p s) in H.
  apply andb_prop in H. destruct H as [H H6]. apply andb_prop in H. destruct H as [H H5].
  apply andb_prop in H. destruct H as [H H4]. apply andb_prop in H. destruct H as [H H3].
  apply andb_prop in H. destruct H as [H1 H2].
  apply Z.leb_le in H6. apply Z.leb_le in H5. apply Z.leb_le in H4. apply Z.ltb_lt in H3.
  exists s, sl. split; [|split; [|split; [exact H6 | split; [exact H3 | split; [exact H4 | exact H5]]]]].
  - apply ro_bytes_at; [exact MI | lia | rewrite length_app; cbn [length]; lia |].
    apply ro_bytes_b_sound. exact H1.
  - intros Hin. apply negb_true_iff in H2.
    assert (X : existsb (fun b => bz b =? 0) s = true)
      by (apply existsb_exists; exists (zb 0); split; [exact Hin | reflexivity]).
    rewrite X in H2. discriminate.
Qed.

Lemma c1b1_texts : forall m, mem_inv rsegs m -> texts_at m -> forall i, 0 <= i < TEXTS_N ->
  exists p s slack, u64_at m (A_TEXTS + 8 * i) p /\ bytes_at rsegs m p (s ++ zb 0 :: slack) /\ ~ In (zb 0) s /\
    (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
    Z.of_nat (length s) < NL_CHUNK_MAX /\ 65536 <= p /\
    p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= 73396.
Proof.
  intros m MI TX i Hi. unfold TEXTS_N in Hi.
  assert (B : forallb c1b1_rok texts_ptrs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B.
  assert (Hn : (Z.to_nat i < 11)%nat) by lia.
  assert (HI : In (nth (Z.to_nat i) texts_ptrs 0) texts_ptrs)
    by (apply nth_In; change (length texts_ptrs) with 11%nat; lia).
  pose proof (B _ HI) as R.
  destruct (c1b1_rok_sound m _ MI R) as (s & sl & H1 & H2 & H3 & H4 & H5 & H6).
  exists (nth (Z.to_nat i) texts_ptrs 0), s, sl.
  refine (conj _ (conj H1 (conj H2 (conj H3 (conj _ (conj H5 H6)))))).
  - pose proof (TX (Z.to_nat i) Hn) as U. rewrite Z2Nat.id in U by lia. exact U.
  - unfold NL_CHUNK_MAX. exact H4.
Qed.

(* the selector's name (name_of, inlined): NULL for 255, else a g_names slot or an odd string *)
Lemma c1b1_gname_nonul : forall k, 0 <= k < 100 -> ~ In (zb 0) (gname k).
Proof.
  intros k Hk Hin. unfold gname, gname_z, dec2 in Hin. apply in_map_iff in Hin. destruct Hin as (z & Ez & Hz).
  assert (Hz' : 48 <= z < 111).
  { revert Hz. destruct (k <? 10) eqn:E; intros Hz.
    - apply Z.ltb_lt in E. cbn [In] in Hz. destruct Hz as [<-|[<-|[<-|[]]]]; lia.
    - apply Z.ltb_ge in E. cbn [In] in Hz.
      destruct Hz as [<-|[<-|[<-|[<-|[]]]]]; try lia; Z.div_mod_to_equations; lia. }
  apply (f_equal bv_unsigned) in Ez. unfold zb in Ez. rewrite !Z_to_bv_unsigned in Ez.
  unfold bv_wrap, bv_modulus in Ez. change (2 ^ Z.of_N 8) with 256 in Ez.
  rewrite (Z.mod_small z 256) in Ez by lia. change (0 mod 256) with 0 in Ez. lia.
Qed.

Lemma c1b1_gname_len : forall k, 0 <= k < 100 -> (length (gname k) <= 4)%nat.
Proof.
  intros k Hk. unfold gname, gname_z, dec2. rewrite length_map.
  destruct (k <? 10); cbn; lia.
Qed.

Lemma c1b1_sel : forall m nb, 0 <= nb < 256 -> gnames_at m -> odd_at m ->
  str_arg m (sel_ptr nb) (sel_name nb) /\ 0 <= sel_ptr nb < 2 ^ 64 /\
  (forall s, sel_name nb = Some s -> 65536 <= sel_ptr nb /\ sel_ptr nb + Z.of_nat (length s) + 1 <= 476152).
Proof.
  intros m nb Hnb GN OD. unfold sel_ptr, sel_name.
  destruct (nb =? 255) eqn:E255.
  - split; [reflexivity|]. split; [lia|]. intros s Hs. discriminate.
  - destruct (nb <? 64) eqn:E64.
    + apply Z.ltb_lt in E64. destruct (GN nb ltac:(lia)) as (rest & B & L).
      pose proof (c1b1_gname_len nb ltac:(lia)) as GL.
      assert (C : cstr_at m (A_G_NAMES + 8 * nb) (gname nb)).
      { split; [|apply c1b1_gname_nonul; lia].
        assert (B' : bytes_at rsegs m (A_G_NAMES + 8 * nb) ((gname nb ++ [zb 0]) ++ rest))
          by (rewrite <- app_assoc; exact B).
        apply bytes_at_app in B'. exact (proj1 B'). }
      split; [split; [unfold A_G_NAMES; lia | exact C]|]. split; [unfold A_G_NAMES; lia|].
      intros s Hs. assert (Es : s = gname nb) by congruence. rewrite Es. unfold A_G_NAMES. lia.
    + apply Z.ltb_ge in E64.
      assert (Hk : (Z.to_nat (nb mod 6) < 6)%nat) by (pose proof (Z.mod_pos_bound nb 6); lia).
      destruct (OD _ Hk) as [_ C]. pose proof (c1b1_odd_bnd _ Hk) as B.
      split; [split; [lia | exact C]|]. split; [lia|].
      intros s Hs. assert (Es : s = nth (Z.to_nat (nb mod 6)) odd_strs []) by congruence.
      rewrite Es. destruct B as [B1 B2]. split; [exact B1 | lia].
Qed.

(* ==========================================================================
   6. Registers of an mkR map
   ========================================================================== *)

Lemma c1b1_spZ : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word,
  spZ (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
           x25 x26 x27 x28 x29 x30 x31) = bv_unsigned x2.
Proof. reflexivity. Qed.

Lemma c1b1_arg0 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word,
  arg (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
           x25 x26 x27 x28 x29 x30 x31) 0 = bv_unsigned x10.
Proof. reflexivity. Qed.

Lemma c1b1_arg1 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word,
  arg (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
           x25 x26 x27 x28 x29 x30 x31) 1 = bv_unsigned x11.
Proof. reflexivity. Qed.

Lemma c1b1_arg2 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word,
  arg (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
           x25 x26 x27 x28 x29 x30 x31) 2 = bv_unsigned x12.
Proof. reflexivity. Qed.

Lemma c1b1_getr10 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word,
  getr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
            x25 x26 x27 x28 x29 x30 x31) 10 = x10.
Proof. reflexivity. Qed.

(* ==========================================================================
   7. The two callee contracts, taken apart
   ========================================================================== *)

Definition c1b1_kP : bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(let t := eval cbv delta [kernel_contract] in kernel_contract in
        lazymatch t with leaf _ _ ?P _ _ => exact P end).
Definition c1b1_kW : bvmap 5 word -> (word -> option byte) -> list ivl :=
  ltac:(let t := eval cbv delta [kernel_contract] in kernel_contract in
        lazymatch t with leaf _ _ _ ?W _ => exact W end).
Definition c1b1_kQ : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(let t := eval cbv delta [kernel_contract] in kernel_contract in
        lazymatch t with leaf _ _ _ _ ?Q => exact Q end).
Lemma c1b1_kok : kernel_contract -> leaf KERNEL 4416 c1b1_kP c1b1_kW c1b1_kQ.
Proof. exact (fun H => H). Qed.

Definition c1b1_mP : bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(let t := eval cbv delta [model_write_contract] in model_write_contract in
        lazymatch t with leaf _ _ ?P _ _ => exact P end).
Definition c1b1_mW : bvmap 5 word -> (word -> option byte) -> list ivl :=
  ltac:(let t := eval cbv delta [model_write_contract] in model_write_contract in
        lazymatch t with leaf _ _ _ ?W _ => exact W end).
Definition c1b1_mQ : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop :=
  ltac:(let t := eval cbv delta [model_write_contract] in model_write_contract in
        lazymatch t with leaf _ _ _ _ ?Q => exact Q end).
Lemma c1b1_mok : model_write_contract -> leaf MODEL_WRITE 704 c1b1_mP c1b1_mW c1b1_mQ.
Proof. exact (fun H => H). Qed.

(* ==========================================================================
   8. The two cuts inside B1
   ========================================================================== *)

(* kernel's return 0x13fc4: s5 = the alias s, the cursor moved on, the fake kernel kbs with nk_next = 0;
   m0 is B1's start memory (the segment footprint) *)
Definition c1b1_13fc4 (E : lenv) (i : Z) (gp : word) (own : Z) (m0 : word -> option byte)
    (ms : machine_state) : Prop :=
  exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte) (nb s : Z) (t sl : list byte),
    ms = MS (mkR ra (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (wz (sel_ptr nb)) s3 s4 (wz s) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz 0x13fc4) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= nb < 256 /\ 0 <= N /\
    lh_mem E i P N kbs mbs gbs m /\ nk_next kbs = 0 /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
    bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\
    (own = 0 \/ own = s) /\
    al_ok E m s t sl /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) /\
    seg_fp (e_S E) (c1_hp E) m0 m.

(* the entry of model_write (0x15c50, ra 0x13ff8) after model_begin: a0 = md, a1 = name, a2 = alias,
   s4 = g_nl.opened; g_nl.n_sent = 0, the model's requests empty and its kstate the fake kernel's *)
Definition c1b1_15c50 (E : lenv) (i : Z) (gp : word) (own : Z) (m0 : word -> option byte)
    (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (P N : Z) (kbs mbs gbs : list byte) (nb s : Z) (t sl : list byte),
    ms = MS (mkR (wz C1_MW_RA) (wz (e_S E - SLOT_FRAME)) gp (wz A_TP) t0 t1 t2 (wz (e_md E)) (wz GNL40)
                 (wz (e_md E)) (wz (sel_ptr nb)) (wz s) a3 a4 a5 a6 a7
                 (wz (sel_ptr nb)) s3 (wz (nk_opened kbs)) (wz s) (wz A_JT) (wz (e_mk E)) (wz 0xab) (wz 4)
                 (wz (e_md E + MD_N_REQ)) (wz i) t3 t4 t5 t6)
            F (wz MODEL_WRITE) fc None m (seg_rom rsegs) /\
    frm0 fc /\ 0 <= i <= 47 /\ 0 <= nb < 256 /\ 0 <= N /\
    lh_mem E i P N kbs mbs gbs m /\ nk_n_sent kbs = 0 /\ md_reqs mbs = [] /\ md_kstate mbs kbs = nk_kstate kbs /\
    rw_cells rsegs m (e_S E - SLOT_FRAME + FO_P) [C8 (wz P); C8 (wz N)] /\
    bytes_at rsegs m (e_S E - SLOT_FRAME + FO_B256) (le8 (wz own)) /\
    (own = 0 \/ own = s) /\
    al_ok E m s t sl /\
    mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
    stk rsegs m (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) /\
    seg_fp (e_S E) (c1_hp E) m0 m.
