From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Lemma land_m2_mod2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (-2) with (Z.lnot 1). rewrite <- Z.ldiff_land.
  replace 1 with (Z.ones 1) by reflexivity. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_mul. lia.
Qed.

Lemma ret_pc_ok : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H.
  assert (E : bv_unsigned k mod 2 = 0).
  { unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in H. apply (f_equal bv_unsigned) in H.
    rewrite Z_to_bv_unsigned in H. rewrite <- H. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (land_m2_mod2 (bv_unsigned k + 0)) as M.
    set (y := Z.land (bv_unsigned k + 0) (-2)) in *. Z.div_mod_to_equations. lia. }
  pose proof (zr_word k) as R. unfold inr64 in R.
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [exact R | exact E].
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

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x55000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stk_of_writable : forall m lo hi, 0x55000 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  specialize (H a Ha). unfold writable_at in H. split; [exact H|].
  unfold mrd. destruct (m (wa a)) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply H.
  unfold wview. change (Z_to_bv 64 a) with (wa a). rewrite E.
  rewrite (wa_unsigned a) by lia.
  rewrite (find_segment_above rsegs 0x55000 a 1 rsegs_top) by lia. reflexivity.
Qed.

Lemma mbyte_munch : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  mbyte segs m' a = mbyte segs m a.
Proof.
  intros segs W m m' a H Ha Ho. unfold mbyte. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  change (Z_to_bv 64 a) with (wa a). rewrite wa_unsigned by lia. exact Ho.
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

Lemma word_mem_munch : forall segs W m m' a v, munch W m m' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> outside W x) -> word_mem segs m a v -> word_mem segs m' a v.
Proof.
  intros segs W m m' a v H Ha Hb Ho Hw k Hk. rewrite (mbyte_munch segs W m m'); [apply Hw; exact Hk | exact H | lia |].
  apply Ho. lia.
Qed.

Lemma outside_one : forall lo hi x, x < lo \/ hi <= x -> outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn. split; [lia | exact I]. Qed.


Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma alloc_words_munch : forall m m' W live peak cnt fail, alloc_words B m live peak cnt fail -> munch W m m' ->
  (forall x, 0 <= x < 0x50000 -> outside W x) -> alloc_words B m' live peak cnt fail.
Proof.
  intros m m' W live peak cnt fail (W1 & W2 & W3 & W4) HW Ho.
  unfold alloc_words, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  split; [|split; [|split]];
    (eapply word_mem_munch; [exact HW | lia | lia | intros x Hx; apply Ho; lia | eassumption]).
Qed.

Lemma in_blocks : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ a = ptr_addr L p.
Proof.
  intros L A a k H. unfold blocks in H. apply in_map_iff in H as ([p k'] & E & Hin). cbn in E.
  inversion E; subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma block_low : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  4096 <= a + i < alloc_ceiling.
Proof.
  intros L A mem md a k i HM Hin Hi. destruct (in_blocks L A a k Hin) as (p & Hp & ->).
  pose proof (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp). lia.
Qed.

Lemma MR_high : forall L A mem mem' md W, MR L A mem md -> munch W mem mem' ->
  (forall x, 0 <= x < alloc_ceiling -> outside W x) -> MR L A mem' md.
Proof.
  intros L A mem mem' md W HM HW Ho. pose proof alloc_ceiling_val as Hac.
  destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & Hm).
  eapply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
  - intros a Hown. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md a HM Hown).
    apply (mbyte_munch _ W); [exact HW | lia | apply Ho; lia].
  - intros a Hown Hp. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md a HM Hown).
    apply (present_munch W mem); [exact HW | lia | apply Ho; lia | exact Hp].
  - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L A mem md p n i HM Hin Hi) as (Hp & H1 & H2 & _).
    apply (present_munch W mem); [exact HW | lia | apply Ho; lia | exact Hp].
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hm.
Qed.

Lemma ledger_munch : forall L A mem md m' W Lam peak cnt fail, MR L A mem md ->
  ledger B L A mem Lam peak cnt fail -> munch W mem m' ->
  (forall x, 0 <= x < alloc_ceiling -> outside W x) -> ledger B L A m' Lam peak cnt fail.
Proof.
  intros L A mem md m' W Lam peak cnt fail HM (AW & R1 & R2 & R3 & ND & FA) HW Ho.
  pose proof alloc_ceiling_val as Hac.
  split; [apply (alloc_words_munch mem m' W _ _ _ _ AW HW); intros x Hx; apply Ho; lia|].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact ND|].
  eapply Forall_impl; [|exact FA]. intros [a k] (Hk & Hin & Hw & Hni). cbn [fst snd] in *.
  split; [exact Hk|]. split; [exact Hin|]. split; [|exact Hni].
  pose proof (block_low L A mem md (a - 16) (k + 16) 0 HM Hin ltac:(lia)) as B0.
  pose proof (block_low L A mem md (a - 16) (k + 16) 7 HM Hin ltac:(lia)) as B7.
  apply (word_mem_munch _ W mem m'); [exact HW | lia | lia | | exact Hw].
  intros x Hx. apply Ho. lia.
Qed.

Lemma in_img_low : ms_segs B = rsegs -> forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof.
  intros HS a [_ (s & Hs & Ha)]. rewrite HS in Hs. pose proof alloc_ceiling_val as Hac.
  assert (Hall : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 40) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall s Hs). apply Z.leb_le in Hall.
  pose proof (bv_unsigned_in_range 64 (fst s)) as R1. pose proof (bv_unsigned_in_range 64 (snd s)) as R2.
  unfold bv_modulus in R1, R2. lia.
Qed.

End KB.

Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH W2 x H2) as [H3 H4]. split; [split; assumption | exact H4].
Qed.

Lemma munch_cat : forall W1 W2 m m1 m2, munch W1 m m1 -> munch W2 m1 m2 -> munch (W1 ++ W2) m m2.
Proof.
  intros W1 W2 m m1 m2 H1 H2 x Hx. destruct (outside_app W1 W2 _ Hx) as [Ha Hb].
  rewrite (H2 x Hb). apply H1. exact Ha.
Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; destruct (Z.le_gt_cases lo x) as [Q1|Q1]; destruct (Z.lt_ge_cases x hi) as [Q2|Q2];
    first [ left; split; [lia | exact H] | right; intros [Ha Hb]; first [lia | contradiction] ].
Qed.

Lemma mem_inv_munch : forall W m m', mem_inv rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> ro_addr rsegs x = false) -> mem_inv rsegs m'.
Proof.
  intros W m m' H HW Hro a b Ha.
  destruct (outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - rewrite (HW a Ho) in Ha. exact (H a b Ha).
  - exact (Hro a Ho).
Qed.

