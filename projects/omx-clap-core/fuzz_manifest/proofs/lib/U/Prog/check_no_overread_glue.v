From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import MState Mem Frame Cells Step Exec Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem Ledger ManifestB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import names_c check_no_overread_c check_no_overread_steps.
Import ListNotations.
Local Open Scope Z_scope.

Lemma getr_eqv : forall R R', xregs_eqv R R' -> forall r, getr R r = getr R' r.
Proof.
  intros R R' H r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  apply H. unfold is_x0. apply Z.eqb_neq. intros H0.
  assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in E. discriminate.
Qed.

Lemma eqv_shape : forall (f : FPState) R pc m ro ms',
  ms_eqv (MS R (@fp_regs f) pc (@fp_csr f) None m ro) ms' ->
  ms' = @mkst f (ms_regs ms') pc m ro /\ xregs_eqv R (ms_regs ms').
Proof.
  intros f R pc m ro [R' F' pc' svc' rv' fc' m' ro'] (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  cbn in *. subst. split; [reflexivity | exact HR].
Qed.

Lemma canon_mkst : forall (f : FPState) regs pc m ro,
  RegisterBridge.canonical_register_state (@mkst f regs pc m ro) = MS (mkR_of regs) (@fp_regs f) pc (@fp_csr f) None m ro.
Proof. reflexivity. Qed.

Lemma find_segment_above : forall segs top a n,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true ->
  top <= a -> 0 < n -> find_segment segs a n = None.
Proof.
  induction segs as [|s segs IH]; intros top a n H Ha Hn; cbn; [reflexivity|].
  cbn in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1.
  destruct ((Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E2. lia.
  - exact (IH top a n H2 Ha Hn).
Qed.

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x51000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ro_false_high : forall a, 0x51000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
  rewrite (find_segment_above rsegs 0x51000 a 1 rsegs_top) by lia. reflexivity.
Qed.

Lemma stk_of_writable : forall m lo hi, 0x51000 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  specialize (H a Ha). unfold writable_at in H. split; [exact H|].
  unfold mrd. destruct (m (wa a)) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply H.
  unfold wview. change (Z_to_bv 64 a) with (wa a). rewrite E.
  rewrite (wa_unsigned a) by lia.
  rewrite (find_segment_above rsegs 0x51000 a 1 rsegs_top) by lia. reflexivity.
Qed.

Lemma writable_munch : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros segs W m m' a H Ha Ho. unfold writable_at, wview. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  change (Z_to_bv 64 a) with (wa a). rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma present_munch : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  present m a -> present m' a.
Proof.
  intros W m m' a H Ha Ho [b Hb]. exists b. rewrite (H (Z_to_bv 64 a)); [exact Hb|].
  change (Z_to_bv 64 a) with (wa a). rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma outside_one : forall lo hi x, x < lo \/ hi <= x -> outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn. split; [lia | exact I]. Qed.

Lemma in_blocks : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ a = ptr_addr L p.
Proof.
  intros L A a k H. unfold blocks in H. apply in_map_iff in H as ([p k'] & E & Hin). cbn in E.
  inversion E; subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma rw_cells_keep : forall m m' A cs, rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Ha' & Hn & Hw)] H.
  rewrite cells_bytes_length in Hl, Hb by assumption.
  split; [split; [exact Hwf|]|].
  - split; [lia|]. split; [rewrite cells_bytes_length by assumption; lia|]. intros i Hi.
    rewrite cells_bytes_length in Hi by assumption.
    rewrite <- (Hb i Hi). exact (proj1 (H (A + Z.of_nat i) ltac:(lia))).
  - split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (proj2 (H (A + i) ltac:(lia))) (Hw i Hi)).
Qed.

Lemma rw_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf | apply (proj2 (bytes_at_rel rsegs m m0 _ _ HR)); exact Hb]|].
  exact (wr_at_rel rsegs m m0 _ _ HR Hw).
Qed.

Lemma rw_cells_norm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof.
  intros m A cs HA [[Hwf Hb] Hw] Hro. split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m _ _ HA Hb)]|].
  exact (wr_at_norm rsegs m (normalize rsegs m) _ _ (mem_rel_normalize rsegs m HA) Hw Hro).
Qed.

Lemma stk_norm : forall m lo hi, ro_agree rsegs m -> 0x51000 <= lo -> stk rsegs m lo hi -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi HA Hlo (H1 & H2 & H). apply stk_of_writable; [exact Hlo | exact H2 |].
  intros a Ha. destruct (H a Ha) as [Hw _]. unfold writable_at.
  change (Z_to_bv 64 a) with (wa a).
  rewrite (wview_rel_rw rsegs m (normalize rsegs m) (wa a) (mem_rel_normalize rsegs m HA)) by (apply ro_false_high; lia).
  exact Hw.
Qed.

Lemma rel_shape : forall R F pc fc m0 ro s, ms_rel rsegs s (MS R F pc fc None m0 ro) ->
  s = MS R F pc fc None (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros R F pc fc m0 ro [R' F' pc' svc' rv' fc' m' ro'] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma norm_back : forall m m0 mr W, ro_agree rsegs m -> mem_rel rsegs mr m0 -> ro_same rsegs m mr ->
  munch W (normalize rsegs m) m0 -> wmono rsegs (normalize rsegs m) m0 ->
  munch W m mr /\ wmono rsegs m mr /\ ro_agree rsegs mr.
Proof.
  intros m m0 mr W HA HR HS MU WM. pose proof (mem_rel_normalize rsegs m HA) as HN.
  split; [exact (munch_rel rsegs W m (normalize rsegs m) mr m0 HN HR HS MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mr m0 HN HR HS WM)|].
  exact (ro_agree_same rsegs m mr HA HS).
Qed.

Lemma bytes_ro_agree : forall m m' a bs, ro_agree rsegs m -> ro_agree rsegs m' ->
  (forall i, (i < length bs)%nat -> ro_addr rsegs (wa (a + Z.of_nat i)) = true) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs H H' Hro (Ha & Hl & Hb). split; [lia|]. split; [lia|]. intros i Hi.
  rewrite <- (Hb i Hi). rewrite (H' _ (Hro i Hi)), (H _ (Hro i Hi)). reflexivity.
Qed.

Lemma img_strings_agree : forall m m', ro_agree rsegs m -> ro_agree rsegs m' -> img_strings m -> img_strings m'.
Proof.
  intros m m' H H' (P1 & P2 & P3).
  split; [|split]; (eapply bytes_ro_agree; [exact H | exact H' | | eassumption]); intros i Hi;
    cbn in Hi; do 8 (destruct i as [|i]; [vm_compute; reflexivity|]); lia.
Qed.

Definition saved_regs (R : bvmap 5 word) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
  getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
  getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11.

Lemma saved_preserved : forall R R' sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  saved_regs R sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 -> regs_preserved R R' ->
  saved_regs R' sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
Proof.
  intros R R' sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    (H2 & H3 & H4 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27) HP.
  unfold regs_preserved, callee_saved in HP.
  repeat split.
  - rewrite <- H2. apply (HP 2). lia.
  - rewrite <- H3. apply (HP 3). lia.
  - rewrite <- H4. apply (HP 4). lia.
  - rewrite <- H8. apply (HP 8). lia.
  - rewrite <- H9. apply (HP 9). lia.
  - rewrite <- H18. apply (HP 18). lia.
  - rewrite <- H19. apply (HP 19). lia.
  - rewrite <- H20. apply (HP 20). lia.
  - rewrite <- H21. apply (HP 21). lia.
  - rewrite <- H22. apply (HP 22). lia.
  - rewrite <- H23. apply (HP 23). lia.
  - rewrite <- H24. apply (HP 24). lia.
  - rewrite <- H25. apply (HP 25). lia.
  - rewrite <- H26. apply (HP 26). lia.
  - rewrite <- H27. apply (HP 27). lia.
Qed.

Lemma saved_of_eqv : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x27 x28 x29 x30 x31 R',
  xregs_eqv (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                 x24 x25 x26 x27 x28 x29 x30 x31) R' ->
  saved_regs R' x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 /\
  getr R' 1 = x1 /\ getr R' 10 = x10 /\ getr R' 11 = x11.
Proof.
  intros. unfold saved_regs. repeat split; rewrite <- (getr_eqv _ _ H); reflexivity.
Qed.

Lemma canon_saved : forall (f : FPState) R pc m ro sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  saved_regs R sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  canonical_register_state (@mkst f R pc m ro) =
  MS (mkR (reg_get R 1) sp gp tp (reg_get R 5) (reg_get R 6) (reg_get R 7) s0 s1 (reg_get R 10)
          (reg_get R 11) (reg_get R 12) (reg_get R 13) (reg_get R 14) (reg_get R 15) (reg_get R 16)
          (reg_get R 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (reg_get R 28) (reg_get R 29) (reg_get R 30)
          (reg_get R 31))
     (@fp_regs f) pc (@fp_csr f) None m ro.
Proof.
  intros f R pc m ro sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    (H2 & H3 & H4 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  rewrite canon_mkst. unfold mkR_of.
  change (reg_get R 2) with (getr R 2). change (reg_get R 3) with (getr R 3).
  change (reg_get R 4) with (getr R 4). change (reg_get R 8) with (getr R 8).
  change (reg_get R 9) with (getr R 9). change (reg_get R 18) with (getr R 18).
  change (reg_get R 19) with (getr R 19). change (reg_get R 20) with (getr R 20).
  change (reg_get R 21) with (getr R 21). change (reg_get R 22) with (getr R 22).
  change (reg_get R 23) with (getr R 23). change (reg_get R 24) with (getr R 24).
  change (reg_get R 25) with (getr R 25). change (reg_get R 26) with (getr R 26).
  change (reg_get R 27) with (getr R 27).
  rewrite H2, H3, H4, H8, H9, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27. reflexivity.
Qed.

Lemma mrd_mbyte : forall m x, mrd rsegs m (wa x) = mbyte rsegs m x.
Proof. reflexivity. Qed.

Lemma bytes_at_mbyte : forall m m' a bs,
  bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) K. split; [lia|]. split; [lia|].
  intros i Hi. rewrite mrd_mbyte, K by lia. rewrite <- mrd_mbyte. apply H. exact Hi.
Qed.

Lemma find_segment_some : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn in H; [discriminate|].
  destruct ((Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
  - inversion H; subst. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | lia].
  - destruct (IH a n seg H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma rsegs_resv : forallb (fun s =>
    (0 <=? page_round_down_Z (Z.of_N (seg_base s))) &&
    (page_round_down_Z (Z.of_N (seg_base s)) <=? Z.of_N (seg_base s)) &&
    (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? page_round_up_Z (Z.of_N (seg_base s) + Z.of_N (seg_size s))) &&
    (page_round_up_Z (Z.of_N (seg_base s) + Z.of_N (seg_size s)) <=? 2 ^ 40)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_nonempty : rsegs <> [].
Proof. vm_compute. discriminate. Qed.

Section G.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.

Lemma find_segment_img : forall a seg, find_segment rsegs a 1 = Some seg -> in_img B a.
Proof.
  intros a seg H. destruct (find_segment_some rsegs a 1 seg H) as (Hin & H1 & H2).
  pose proof rsegs_resv as R. rewrite forallb_forall in R. specialize (R seg Hin).
  repeat rewrite andb_true_iff in R. destruct R as (((R1 & R2) & R3) & R4).
  apply Z.leb_le in R1, R2, R3, R4.
  split; [rewrite HS; exact rsegs_nonempty|].
  exists (segment_reservation seg). rewrite HS. split; [apply in_map; exact Hin|].
  unfold segment_reservation. cbn [fst snd].
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite !Z.mod_small by lia. lia.
Qed.

Lemma ro_false_not_img : forall a, ~ in_img B a -> 0 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Hn Ha. unfold ro_addr. rewrite wa_unsigned by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|reflexivity].
  exfalso. exact (Hn (find_segment_img a seg F)).
Qed.

Lemma blocks_low : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  4096 <= a + i < alloc_ceiling.
Proof.
  intros L A mem md a k i HM Hin Hi. destruct (in_blocks L A a k Hin) as (p & Hp & ->).
  pose proof (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp). lia.
Qed.

Lemma in_img_low : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof.
  intros a [_ (s & Hs & Ha)]. rewrite HS in Hs. pose proof alloc_ceiling_val as Hac.
  assert (Hall : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 40) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall s Hs). apply Z.leb_le in Hall.
  pose proof (bv_unsigned_in_range 64 (fst s)) as R1. pose proof (bv_unsigned_in_range 64 (snd s)) as R2.
  unfold bv_modulus in R1, R2. lia.
Qed.

Lemma word_mem_munch : forall segs W m m' a v, munch W m m' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> outside W x) -> word_mem segs m a v -> word_mem segs m' a v.
Proof.
  intros segs W m m' a v H Ha Hb Ho Hw k Hk. rewrite (mbyte_munch segs W m m'); [apply Hw; exact Hk | exact H | lia |].
  apply Ho. lia.
Qed.

Lemma alloc_words_munch : forall m m' W live peak cnt fail, alloc_words B m live peak cnt fail -> munch W m m' ->
  (forall x, 0 <= x < 0x51000 -> outside W x) -> alloc_words B m' live peak cnt fail.
Proof.
  intros m m' W live peak cnt fail (W1 & W2 & W3 & W4) HW Ho.
  unfold alloc_words, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  split; [|split; [|split]];
    (eapply word_mem_munch; [exact HW | lia | lia | intros x Hx; apply Ho; lia | eassumption]).
Qed.

Lemma present_of_mrd : forall m x b, ~ in_img B x -> 0 <= x < 2 ^ 64 ->
  mrd rsegs m (wa x) = Some b -> present m x.
Proof.
  intros m x b Hn Hx H. unfold mrd in H. unfold present.
  destruct (m (wa x)) as [y|] eqn:E; [exists y; exact E|].
  exfalso. apply Hn. unfold PropExec.seg_rom, memory_read in H.
  rewrite (wa_unsigned x Hx) in H.
  destruct (find_segment rsegs x (Z.of_N 1)) as [seg|] eqn:F; [|discriminate].
  exact (find_segment_img x seg F).
Qed.

Lemma present_of_bytes : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  ~ in_img B (a + i) -> present m (a + i).
Proof.
  intros m a bs i (Ha & Hl & H) Hi Hn.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E.
  - exact (present_of_mrd m (a + i) b Hn ltac:(lia) H).
  - apply nth_error_None in E. lia.
Qed.

Lemma rw_cells_of_present : forall m a n, 0 <= a -> a + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> present m (a + i)) ->
  exists junk, rw_cells rsegs m a [CB (Z.to_nat n) junk].
Proof.
  intros m a n Ha Hn Hn0 H.
  assert (ST : stk rsegs m a (a + n)).
  { split; [lia|]. split; [lia|]. intros x Hx.
    destruct (H (x - a) ltac:(lia)) as [b Hb]. replace (a + (x - a)) with x in Hb by lia.
    split.
    - unfold wview. change (Z_to_bv 64 x) with (wa x) in Hb. rewrite Hb. discriminate.
    - exists b. unfold mrd. change (Z_to_bv 64 x) with (wa x) in Hb. rewrite Hb. reflexivity. }
  destruct (stk_carve rsegs m a (a + n) (Z.to_nat n) ST ltac:(lia)) as [_ (junk & J)].
  exists junk. replace (a + n - Z.of_nat (Z.to_nat n)) with a in J by lia. exact J.
Qed.

Lemma not_owned_any : forall L A m md a, MR L A m md ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ static_owned B a ->
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L A a.
Proof.
  intros L A m md a HM Hr Hs Hc [Ho|Ho]; [|exact (Hs Ho)].
  pose proof (mr_owned_low _ _ (aa_laws API) L A m md a HM (or_introl Ho)) as Hlow.
  destruct Hr as [Hr|Hr]; [lia|].
  exact (Hc (ax_img AX L A m md a HM Hr Ho)).
Qed.

Lemma block_not_img : forall L A m md a k i, MR L A m md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (a + i).
Proof.
  intros L A m md a k i HM Hin Hi. destruct (in_blocks L A a k Hin) as (p & Hp & ->).
  exact (ax_blocks_img AX L A m md p k i HM Hp Hi).
Qed.

Lemma pairwise_dup : forall {X} (R : X -> X -> Prop) l1 x l2, pairwise R (l1 ++ x :: l2) -> In x (l1 ++ l2) -> R x x.
Proof.
  intros X R l1. induction l1 as [|y l1 IH]; intros x l2 HP Hin; cbn in *.
  - destruct HP as [H _]. apply H. exact Hin.
  - destruct HP as [Hy HP]. destruct Hin as [<-|Hin].
    + apply Hy. apply in_app_iff. right. left. reflexivity.
    + exact (IH x l2 HP Hin).
Qed.

Lemma pairwise_in2' : forall {X} (R : X -> X -> Prop) l x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
  destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - left. apply Hz. exact Hy.
  - right. apply Hz. exact Hx.
  - apply IH; assumption.
Qed.

Lemma blocks_sep : forall L A m md x y, MR L A m md -> In x (blocks L A) -> In y (blocks L A) -> x <> y ->
  fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros L A m md x y HM Hx Hy Hne.
  destruct (pairwise_in2' _ _ x y (mr_blocks_disjoint _ _ (aa_laws API) L A m md HM) Hx Hy Hne) as [H|H];
    unfold ranges_disjoint in H; lia.
Qed.

Lemma fresh_notin : forall L A m md b1 b2 r n, MR L A m md -> blocks L A = b1 ++ (r, n) :: b2 -> 0 < n ->
  ~ In (r, n) (b1 ++ b2).
Proof.
  intros L A m md b1 b2 r n HM E Hn Hin.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A m md HM) as P. rewrite E in P.
  pose proof (pairwise_dup _ b1 (r, n) b2 P Hin) as D. unfold ranges_disjoint in D. cbn in D. lia.
Qed.

End G.

Definition zz_eqb (x y : Z * Z) : bool := (fst x =? fst y) && (snd x =? snd y).
Fixpoint rmb (x : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => []
  | y :: l' => if zz_eqb y x then rmb x l' else y :: rmb x l'
  end.

Lemma zz_eqb_true : forall x y, zz_eqb x y = true <-> x = y.
Proof.
  intros [a b] [c d]. unfold zz_eqb. cbn. rewrite andb_true_iff, !Z.eqb_eq. split.
  - intros [-> ->]. reflexivity.
  - intros E. inversion E. split; reflexivity.
Qed.

Lemma rmb_notin : forall x l, ~ In x l -> rmb x l = l.
Proof.
  intros x l. induction l as [|y l IH]; intros H; [reflexivity|]. cbn [rmb].
  destruct (zz_eqb y x) eqn:E.
  - apply zz_eqb_true in E. subst. exfalso. apply H. left. reflexivity.
  - f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma rmb_app : forall x l1 l2, rmb x (l1 ++ l2) = rmb x l1 ++ rmb x l2.
Proof.
  intros x l1 l2. induction l1 as [|y l1 IH]; [reflexivity|]. cbn [rmb app].
  destruct (zz_eqb y x); [exact IH | cbn [app]; f_equal; exact IH].
Qed.

Lemma rmb_ins : forall x b1 b2, ~ In x (b1 ++ b2) -> rmb x (b1 ++ x :: b2) = b1 ++ b2.
Proof.
  intros x b1 b2 H. rewrite rmb_app. cbn [rmb].
  replace (zz_eqb x x) with true by (symmetry; apply zz_eqb_true; reflexivity). cbv beta iota.
  rewrite <- rmb_app. apply rmb_notin. exact H.
Qed.

Lemma rmb_comm : forall x y l, rmb x (rmb y l) = rmb y (rmb x l).
Proof.
  intros x y l. induction l as [|z l IH]; [reflexivity|]. cbn [rmb].
  destruct (zz_eqb z y) eqn:E1; destruct (zz_eqb z x) eqn:E2; cbn [rmb]; rewrite ?E1, ?E2;
    first [exact IH | f_equal; exact IH].
Qed.

Lemma rmb_in : forall x y l, In y l -> y <> x -> In y (rmb x l).
Proof.
  intros x y l. induction l as [|z l IH]; intros H Hne; [destruct H|]. cbn [rmb].
  destruct (zz_eqb z x) eqn:E.
  - apply zz_eqb_true in E. subst z. destruct H as [<-|H]; [exfalso; exact (Hne eq_refl) | exact (IH H Hne)].
  - destruct H as [<-|H]; [left; reflexivity | right; exact (IH H Hne)].
Qed.

Lemma rmb_sub : forall x y l, In y (rmb x l) -> In y l.
Proof.
  intros x y l. induction l as [|z l IH]; intros H; [destruct H|]. cbn [rmb] in H.
  destruct (zz_eqb z x); [right; exact (IH H) | destruct H as [<-|H]; [left; reflexivity | right; exact (IH H)]].
Qed.

Lemma rmb4 : forall x1 x2 x3 x4 l0 l1 l2 l3 l4,
  rmb x4 l4 = l3 -> rmb x3 l3 = l2 -> rmb x2 l2 = l1 -> rmb x1 l1 = l0 ->
  rmb x4 (rmb x3 (rmb x2 (rmb x1 l4))) = l0.
Proof.
  intros x1 x2 x3 x4 l0 l1 l2 l3 l4 E4 E3 E2 E1.
  rewrite (rmb_comm x2 x1), (rmb_comm x3 x1), (rmb_comm x3 x2), (rmb_comm x4 x1), (rmb_comm x4 x2), (rmb_comm x4 x3).
  rewrite E4, E3, E2, E1. reflexivity.
Qed.

Lemma with_vmmaps_twice' : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma with_vmmaps_self' : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Section J.
Context {fx : YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.

Definition jinv (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\
  (exists vm, md = with_vmmaps vm md0) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ static_owned B a ->
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ scratch_k B CNO_K regs0 a -> ~ stat_writes a ->
     mbyte rsegs mem a = mbyte rsegs mem0 a /\ (writable_at rsegs mem0 a <-> writable_at rsegs mem a)) /\
  (forall a, scratch_k B CNO_K regs0 a -> writable_at rsegs mem a) /\
  (forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k -> mbyte rsegs mem (a + i) = mbyte rsegs mem0 (a + i)) /\
  (forall x, In x (blocks L0 A0) -> In x (blocks L A)) /\
  ro_agree rsegs mem.

Lemma jinv_init : forall L A regs mem md, call_pre_k B MR CNO_K L A regs mem md -> ro_agree rsegs mem ->
  jinv L A regs mem md L A mem md.
Proof.
  intros L A regs mem md (HM & HWF & HBD & _ & _ & _ & _ & HWS & _ & HER & _) HMI.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|].
  split; [exists (m_vmmaps md); apply with_vmmaps_self'|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros a [Ha|Ha]; rewrite <- HS; [apply HWS | apply HER]; exact Ha|].
  split; [intros; reflexivity|]. split; [intros x Hx; exact Hx|]. exact HMI.
Qed.

Lemma jinv_kindA : forall L0 A0 regs0 mem0 md0 L A mem md mem' W,
  jinv L0 A0 regs0 mem0 md0 L A mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  alloc_ceiling + CNO_K <= spZ regs0 ->
  (forall x, 0 <= x < 2 ^ 64 -> outside W x \/ (spZ regs0 - CNO_K <= x < spZ regs0) \/
     (exists r n, In (r, n) (blocks L A) /\ ~ In (r, n) (blocks L0 A0) /\ r <= x < r + n /\ present mem' x)) ->
  jinv L0 A0 regs0 mem0 md0 L A mem' md.
Proof.
  intros L0 A0 regs0 mem0 md0 L A mem md mem' W (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI) MU WM MI' HK CLS.
  pose proof alloc_ceiling_val as Hac.
  assert (OWN : forall a, owned B L A a -> 0 <= a < alloc_ceiling /\ outside W a).
  { intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md a HM Ho) as Hl. split; [exact Hl|].
    destruct (CLS a ltac:(lia)) as [Hout | [Hst | (r & n & Hin & _ & Hr & _)]]; [exact Hout | lia |].
    exfalso. destruct (in_blocks L A r n Hin) as (p & Hp & ->).
    destruct (mr_blocks _ _ (aa_laws API) L A mem md p n (a - ptr_addr L p) HM Hp ltac:(lia)) as (_ & _ & _ & Hno).
    replace (ptr_addr L p + (a - ptr_addr L p)) with a in Hno by lia. exact (Hno Ho). }
  split.
  { destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & Hm).
    eapply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
    - intros a Ho. destruct (OWN a Ho) as [Hl0 Hout]. apply (mbyte_munch _ W); [exact MU | lia | exact Hout].
    - intros a Ho Hp. destruct (OWN a Ho) as [Hl0 Hout]. apply (present_munch W mem); [exact MU | lia | exact Hout | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L A mem md p n i HM Hin Hi) as (Hp & H1 & H2 & _).
      destruct (CLS (ptr_addr L p + i) ltac:(lia)) as [Hout | [Hst | (r & k & _ & _ & _ & Hpr)]].
      + apply (present_munch W mem); [exact MU | lia | exact Hout | exact Hp].
      + lia.
      + exact Hpr.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HMD|].
  split.
  { intros a Hr Hs Hc Hsc Hst. destruct (HFR a Hr Hs Hc Hsc Hst) as [E1 E2].
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B HS a Hr); lia]).
    destruct (CLS a Ha) as [Hout | [Hstk | (r & n & Hin & _ & Hrn & _)]].
    - split.
      + rewrite (mbyte_munch _ W mem mem' a MU Ha Hout). exact E1.
      + rewrite E2. apply (writable_munch _ W mem mem' a MU Ha Hout).
    - exfalso. apply Hsc. left. exact Hstk.
    - exfalso. pose proof (blocks_low B API L A mem md r n (a - r) HM Hin ltac:(lia)) as Hlow.
      pose proof (block_not_img B API AX L A mem md r n (a - r) HM Hin ltac:(lia)) as Hni.
      replace (r + (a - r)) with a in Hlow, Hni by lia. destruct Hr as [Hr|Hr]; [lia | exact (Hni Hr)]. }
  split; [intros a Hs; apply WM; apply HSC; exact Hs|].
  split.
  { intros a k i Hin Hi. rewrite <- (HB0 a k i Hin Hi).
    pose proof (HP0 _ Hin) as Hin'.
    pose proof (blocks_low B API L A mem md a k i HM Hin' Hi) as Hlow.
    destruct (CLS (a + i) ltac:(lia)) as [Hout | [Hstk | (r & n & Hrin & Hrn0 & Hrn & _)]].
    - apply (mbyte_munch _ W); [exact MU | lia | exact Hout].
    - lia.
    - exfalso. assert (Hne : (a, k) <> (r, n)) by (intros E; rewrite E in Hin; exact (Hrn0 Hin)).
      destruct (blocks_sep B API L A mem md (a, k) (r, n) HM Hin' Hrin Hne) as [D|D]; cbn in D; lia. }
  split; [exact HP0 | exact MI'].
Qed.

Lemma jinv_step : forall L0 A0 regs0 mem0 md0 L A mem md L' A' mem' md' (Kc spc : Z) (E : Z -> Prop),
  jinv L0 A0 regs0 mem0 md0 L A mem md ->
  MR L' A' mem' md' -> WF A' -> bounded A' -> (exists vm', md' = with_vmmaps vm' md) ->
  spZ regs0 - CNO_K <= spc - Kc -> spc <= spZ regs0 -> alloc_ceiling + CNO_K <= spZ regs0 ->
  (forall a, E a -> (a < alloc_ceiling /\ ~ in_img B a) \/ stat_writes a) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
     ~ (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4) -> ~ E a ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)) ->
  (forall a, (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4) -> writable_at rsegs mem' a) ->
  (forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k -> mbyte rsegs mem' (a + i) = mbyte rsegs mem (a + i)) ->
  (forall x, In x (blocks L0 A0) -> In x (blocks L' A')) ->
  ro_agree rsegs mem' ->
  jinv L0 A0 regs0 mem0 md0 L' A' mem' md'.
Proof.
  intros L0 A0 regs0 mem0 md0 L A mem md L' A' mem' md' Kc spc E
    (HM & HWF & HBD & (vm & HMD) & HFR & HSC & HB0 & HP0 & HMI) HM' HWF' HBD' (vm' & HMD') Hk1 Hk2 HK HE
    FR SC B0 P0 MI'.
  pose proof alloc_ceiling_val as Hac.
  assert (HSW : forall a, stat_writes a -> a < alloc_ceiling) by (unfold stat_writes, G_LIVE, G_COUNT, G_FAIL; lia).
  split; [exact HM'|]. split; [exact HWF'|]. split; [exact HBD'|].
  split; [exists vm'; rewrite HMD', HMD; apply with_vmmaps_twice'|].
  split.
  { intros a Hr Hs Hc Hsc Hst. destruct (HFR a Hr Hs Hc Hsc Hst) as [E1 E2].
    assert (Hn1 : ~ owned B L A a) by (exact (not_owned_any B API AX L A mem md a HM Hr Hs Hc)).
    assert (Hn2 : ~ owned B L' A' a) by (exact (not_owned_any B API AX L' A' mem' md' a HM' Hr Hs Hc)).
    assert (Hn3 : ~ (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4)).
    { intros [H|H]; apply Hsc; unfold scratch_k, spZ in *; [left; lia | right; exact H]. }
    assert (Hn4 : ~ E a).
    { intros He. destruct (HE a He) as [(H1 & H2)|H]; [destruct Hr as [Hr|Hr]; [lia | exact (H2 Hr)] | exact (Hst H)]. }
    destruct (FR a Hr Hn1 Hn2 Hn3 Hn4) as [F1 F2].
    split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros a Hs.
    assert (D : (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4) \/
                ~ (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4)).
    { destruct (Z.le_gt_cases (spc - Kc) a); destruct (Z.lt_ge_cases a spc);
        destruct (Z.le_gt_cases (errno_addr B) a); destruct (Z.lt_ge_cases a (errno_addr B + 4));
        first [left; lia | right; lia]. }
    destruct D as [D|D]; [exact (SC a D)|].
    destruct Hs as [Hs|Hs]; [|exfalso; apply D; right; exact Hs].
    unfold spZ in Hs, HK.
    pose proof (zr_word (getr regs0 2)) as R. unfold inr64 in R.
    assert (Hr : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
    assert (Hn1 : ~ owned B L A a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho); lia).
    assert (Hn2 : ~ owned B L' A' a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho); lia).
    assert (Hn4 : ~ E a) by (intros He; destruct (HE a He) as [(H1 & _)|H]; [lia | pose proof (HSW a H); lia]).
    destruct (FR a Hr Hn1 Hn2 D Hn4) as [_ F2]. apply F2. apply HSC. left. unfold spZ. exact Hs. }
  split.
  { intros a k i Hin Hi. rewrite (B0 a k i Hin Hi). exact (HB0 a k i Hin Hi). }
  split; [exact P0 | exact MI'].
Qed.

Lemma guard_kept_of_MR : forall L A mem md L' A' mem' md', MR L A mem md -> MR L' A' mem' md' ->
  guard_kept B mem mem'.
Proof.
  intros L A mem md L' A' mem' md' HM HM' i Hi.
  destruct (ax_statics AX L A mem md HM) as (G0 & _).
  destruct (ax_statics AX L' A' mem' md' HM') as (G1 & _).
  pose proof (G0 (Z.to_nat i) ltac:(lia)) as E0. pose proof (G1 (Z.to_nat i) ltac:(lia)) as E1.
  rewrite Z2Nat.id in E0, E1 by lia. rewrite E0, E1. reflexivity.
Qed.

Lemma jinv_bpost : forall L0 A0 regs0 mem0 md0 L A mem md regs',
  ctx_owned B MR -> MR L0 A0 mem0 md0 ->
  jinv L0 A0 regs0 mem0 md0 L A mem md ->
  regs_preserved regs0 regs' -> blocks L A = blocks L0 A0 ->
  bpost B MR CNO_K stat_writes L0 A0 regs0 mem0 md0 L A regs' mem md.
Proof.
  intros L0 A0 regs0 mem0 md0 L A mem md regs' CTX HM0 (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI) RP BL.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact RP|]. split; [exact HMD|].
  split; [exact BL|].
  split; [rewrite HS; exact HB0|].
  split.
  { intros a Hr Hn0 _ Hsc Hst. rewrite HS.
    apply HFR; [exact Hr | intros Hs; apply Hn0; right; exact Hs | intros Hc; exact (Hn0 (CTX _ _ _ _ a HM0 Hc)) |
      exact Hsc | exact Hst]. }
  split; [rewrite HS; exact HSC|].
  split; [rewrite HS; exact HMI | exact (guard_kept_of_MR L0 A0 mem0 md0 L A mem md HM0 HM)].
Qed.

End J.
