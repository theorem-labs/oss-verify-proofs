From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require YN01 YI04 YL01 YK1j.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestMem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestB.
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

Lemma cstr_munch : forall m m' W a bs sl, cstr_at m a bs sl -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length bs + 1 + length sl)) -> cstr_at m' a bs sl.
Proof.
  intros m m' W a bs sl [Hb [Hn Ha]] HW Hd. split; [|split; assumption].
  eapply bytes_at_transport; [exact Hb | exact HW |].
  rewrite length_app. cbn [length]. replace (length bs + S (length sl))%nat with (length bs + 1 + length sl)%nat by lia.
  exact Hd.
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

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x51000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

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

Lemma bytes_ro : forall m m' a bs, ro_agree rsegs m -> ro_agree rsegs m' ->
  (forall i, (i < length bs)%nat -> ro_addr rsegs (wa (a + Z.of_nat i)) = true) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs H H' Hro (Ha & Hl & Hb). split; [lia|]. split; [lia|]. intros i Hi.
  rewrite <- (Hb i Hi). specialize (Hro i Hi). rewrite (H' _ Hro), (H _ Hro). reflexivity.
Qed.

Lemma img_strings_keep : forall m m', ro_agree rsegs m -> ro_agree rsegs m' -> img_strings m -> img_strings m'.
Proof.
  intros m m' H H' (P1 & P2 & P3).
  split; [|split]; (eapply bytes_ro; [exact H | exact H' | | eassumption]); intros i Hi;
    cbn in Hi; do 8 (destruct i as [|i]; [vm_compute; reflexivity|]); lia.
Qed.

Lemma ro_low : forall x : word, ro_addr rsegs x = true -> 65536 <= bv_unsigned x < 122880.
Proof.
  intros x H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:Hf; [|discriminate H].
  pose proof (YK1j.find_segment_in _ _ _ _ Hf) as Hin.
  pose proof (YK1j.find_segment_range _ _ _ _ Hf) as [H1 H2].
  assert (Hall : forallb (fun s => seg_writable s || ((65536 <=? Z.of_N (seg_base s)) &&
                   (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 122880))) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall s Hin).
  apply negb_true_iff in H. rewrite H in Hall. cbn [orb] in Hall.
  apply andb_true_iff in Hall as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. lia.
Qed.

Lemma ro_agree_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall x, 65536 <= x < 122880 -> outside W x) -> ro_agree rsegs m'.
Proof.
  intros W m m' H HW Ho a Ha. rewrite <- (H a Ha). unfold mrd. rewrite (HW a (Ho _ (ro_low a Ha))). reflexivity.
Qed.

Lemma ro_false_high : forall a : Z, 122880 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity].
  pose proof (ro_low _ E) as R. rewrite wa_unsigned in R by lia. lia.
Qed.

Lemma stk_normalize : forall m lo hi, stk rsegs m lo hi -> 122880 <= lo ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hlo. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (ro_false_high a ltac:(lia)) as E. destruct (H a Ha) as [Hw Hr].
  unfold wview, mrd, normalize in *. rewrite E. split; [exact Hw | exact Hr].
Qed.

Lemma cstr_normalize : forall m a bs sl, ro_agree rsegs m -> cstr_at m a bs sl -> cstr_at (normalize rsegs m) a bs sl.
Proof.
  intros m a bs sl H (Hb & Hn & Hs). split; [|split; assumption]. apply bytes_at_normalize; assumption.
Qed.

Lemma rel_shape : forall s R F pc fc rv m0 ro, ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [R' F' pc' svc' rv' fc' m' ro'] R F pc fc rv m0 ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  cbn in *. subst. split; [reflexivity | exact HR].
Qed.

Lemma stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw Hr]. split.
  - exact (writable_at_rel rsegs m m0 a HR Hw).
  - rewrite (mrd_rel rsegs m m0 _ HR). exact Hr.
Qed.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma alloc_words_munch : forall m m' W live peak cnt fail, alloc_words B m live peak cnt fail -> munch W m m' ->
  (forall x, 0 <= x < 0x51000 -> outside W x) -> alloc_words B m' live peak cnt fail.
Proof.
  intros m m' W live peak cnt fail (W1 & W2 & W3 & W4) HW Ho.
  unfold alloc_words, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  split; [|split; [|split]];
    (eapply word_mem_munch; [exact HW | lia | lia | intros x Hx; apply Ho; lia | eassumption]).
Qed.

Lemma guard_cells_munch : forall m m' W, guard_syms B -> guard_cells B m -> munch W m m' ->
  (forall x, 0x1e368 <= x < 0x1e368 + 8 \/ 0x4f978 <= x < 0x4f978 + 8 -> outside W x) -> guard_cells B m'.
Proof.
  intros m m' W [G1 G2] (C1 & g & C2) HW Ho. unfold guard_cells. rewrite G1, G2 in *.
  split; [|exists g];
    (eapply word_mem_munch; [exact HW | lia | lia | intros x Hx; apply Ho; first [left; lia | right; lia] | eassumption]).
Qed.

Lemma in_blocks : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ a = ptr_addr L p.
Proof.
  intros L A a k H. unfold blocks in H. apply in_map_iff in H as ([p k'] & E & Hin). cbn in E.
  inversion E; subst. exists p. split; [exact Hin | reflexivity].
Qed.

Lemma blocks_low : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
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
  eapply Forall_impl; [|exact FA]. intros [a k] (Hk & Hin & Hw & Himg). cbn [fst snd] in *.
  split; [exact Hk|]. split; [exact Hin|]. split; [|exact Himg].
  pose proof (blocks_low L A mem md (a - 16) (k + 16) 0 HM Hin ltac:(lia)) as B0.
  pose proof (blocks_low L A mem md (a - 16) (k + 16) 7 HM Hin ltac:(lia)) as B7.
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

Lemma bpost_sandwich : forall K K1 E L A regs mem md mem1 regs1 L' A' regs2 mem2 md' mem3 regs3 lo3 hi3,
  MR L A mem md ->
  (forall a, spZ regs - K <= a < spZ regs -> writable_at (ms_segs B) mem a) ->
  alloc_ceiling + K <= spZ regs -> spZ regs < 2 ^ 63 -> 0 <= K1 -> 32 + K1 <= K ->
  spZ regs1 = spZ regs - 32 ->
  (forall a, E a -> a < alloc_ceiling) ->
  (forall a, in_img B a -> 0 <= a < alloc_ceiling) ->
  munch [(spZ regs - 32, spZ regs)] mem mem1 -> wmono (ms_segs B) mem mem1 ->
  bpost B MR K1 E L A regs1 mem1 md L' A' regs2 mem2 md' ->
  munch [(lo3, hi3)] mem2 mem3 -> wmono (ms_segs B) mem2 mem3 -> spZ regs - K <= lo3 -> hi3 <= spZ regs ->
  guard_syms B -> ro_agree (ms_segs B) mem3 ->
  regs_preserved regs regs3 ->
  bpost B MR K E L A regs mem md L' A' regs3 mem3 md'.
Proof.
  intros K K1 E L A regs mem md mem1 regs1 L' A' regs2 mem2 md' mem3 regs3 lo3 hi3
    HM HWs Hac H63 HK0 HK Hsp1 HE HI MU1 WM1 BP MU3 WM3 Hlo3 Hhi3 GS RA3 RP.
  pose proof alloc_ceiling_val as Hacv.
  destruct BP as (HM2 & HWF & HBD & _ & Hmd & Hbl & Hbb & Hfr & Hsc & _ & GK).
  assert (HM1 : MR L A mem1 md).
  { apply (MR_high L A mem mem1 md _ HM MU1). intros x Hx. apply outside_one. lia. }
  assert (O1 : forall x, 0 <= x < spZ regs - 32 -> outside [(spZ regs - 32, spZ regs)] x)
    by (intros x Hx; apply outside_one; lia).
  assert (O3 : forall x, 0 <= x < lo3 \/ hi3 <= x -> outside [(lo3, hi3)] x)
    by (intros x Hx; apply outside_one; lia).
  assert (NO : forall L0 A0 m0 md0 a, MR L0 A0 m0 md0 -> alloc_ceiling <= a -> ~ owned B L0 A0 a).
  { intros L0 A0 m0 md0 a H0 Ha Ho. pose proof (mr_owned_low _ _ (aa_laws API) L0 A0 m0 md0 a H0 Ho). lia. }
  split; [apply (MR_high L' A' mem2 mem3 md' _ HM2 MU3); intros x Hx; apply O3; lia|].
  split; [exact HWF|]. split; [exact HBD|]. split; [exact RP|]. split; [exact Hmd|]. split; [exact Hbl|].
  split.
  { intros a k i Hin Hi.
    pose proof (blocks_low L A mem md a k i HM Hin Hi) as Hlow.
    rewrite (mbyte_munch _ [(lo3, hi3)] mem2 mem3) by first [exact MU3 | lia | apply O3; lia].
    rewrite (Hbb a k i Hin Hi).
    apply (mbyte_munch _ [(spZ regs - 32, spZ regs)] mem mem1); [exact MU1 | lia | apply O1; lia]. }
  split.
  { intros a Hr HnA HnA' Hsc0 HnE.
    assert (Hn1 : ~ scratch_k B K1 regs1 a).
    { intros [Hs|Hs]; apply Hsc0; [left; unfold spZ in *; lia | right; exact Hs]. }
    assert (Hout : ~ (spZ regs - K <= a < spZ regs)) by (intros Hs; apply Hsc0; left; exact Hs).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (HI a Hr); lia]).
    destruct (Hfr a Hr HnA HnA' Hn1 HnE) as [Hm2 Hw2].
    split.
    - rewrite (mbyte_munch _ [(lo3, hi3)] mem2 mem3) by first [exact MU3 | lia | apply O3; lia].
      rewrite Hm2. apply (mbyte_munch _ [(spZ regs - 32, spZ regs)] mem mem1); [exact MU1 | lia | apply outside_one; lia].
    - rewrite (writable_munch _ [(spZ regs - 32, spZ regs)] mem mem1 a MU1) by first [lia | apply outside_one; lia].
      rewrite Hw2. apply (writable_munch _ [(lo3, hi3)] mem2 mem3 a MU3); [lia | apply O3; lia]. }
  assert (GK3 : guard_kept B mem mem3).
  { destruct GS as [G1 _]. intros i Hi. specialize (GK i Hi). rewrite G1 in GK |- *.
    rewrite (mbyte_munch _ [(lo3, hi3)] mem2 mem3) by first [exact MU3 | lia | apply O3; lia].
    rewrite GK.
    apply (mbyte_munch _ [(spZ regs - 32, spZ regs)] mem mem1); [exact MU1 | lia | apply O1; lia]. }
  split; [|exact (conj RA3 GK3)].
  intros a Hs. apply WM3.
  assert (D : scratch_k B K1 regs1 a \/ ~ scratch_k B K1 regs1 a).
  { unfold scratch_k. destruct (Z.le_gt_cases (spZ regs1 - K1) a); destruct (Z.lt_ge_cases a (spZ regs1));
      destruct (Z.le_gt_cases (errno_addr B) a); destruct (Z.lt_ge_cases a (errno_addr B + 4));
      first [left; lia | right; lia]. }
  destruct D as [Hs1|Hs1]; [exact (Hsc a Hs1)|].
  destruct Hs as [Hs|Hs]; [|exfalso; apply Hs1; right; exact Hs].
  assert (Hw1 : writable_at (ms_segs B) mem1 a) by (apply WM1; apply HWs; exact Hs).
  assert (Hr : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
  assert (Hn1 : ~ owned B L A a) by (apply (NO _ _ _ _ a HM1); lia).
  assert (Hn2 : ~ owned B L' A' a) by (apply (NO _ _ _ _ a HM2); lia).
  assert (Hn3 : ~ E a) by (intros He; pose proof (HE a He); lia).
  destruct (Hfr a Hr Hn1 Hn2 Hs1 Hn3) as [_ Hw2].
  apply Hw2. exact Hw1.
Qed.

End KB.
Lemma word_mem_bytes : forall segs m a v, 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  word_mem segs m a v -> bytes_at segs m a (le8 (Z_to_bv 64 v)).
Proof.
  intros segs m a v Hv Ha Hb H. split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi.
  change (mrd segs m (wa (a + Z.of_nat i))) with (mbyte segs m (a + Z.of_nat i)).
  rewrite (H i Hi). unfold le8, word_to_le_bytes.
  rewrite YN01.nth_error_Z_to_le_bytes by exact Hi.
  rewrite (inr64_unsigned_lit v) by (unfold inr64; lia).
  f_equal. apply YI04.le_byte_small; [change (8 * Z.of_nat 8) with 64; lia | exact Hi].
Qed.

Lemma bytes_word_mem : forall segs m a v, 0 <= v < 2 ^ 64 ->
  bytes_at segs m a (le8 (Z_to_bv 64 v)) -> word_mem segs m a v.
Proof.
  intros segs m a v Hv (Ha & Hl & Hb) k Hk.
  pose proof (Hb k ltac:(rewrite length_le8; lia)) as E.
  change (mrd segs m (wa (a + Z.of_nat k))) with (mbyte segs m (a + Z.of_nat k)) in E.
  rewrite E. unfold le8, word_to_le_bytes.
  rewrite YN01.nth_error_Z_to_le_bytes by exact Hk.
  rewrite (inr64_unsigned_lit v) by (unfold inr64; lia).
  f_equal. symmetry. apply YI04.le_byte_small; [change (8 * Z.of_nat 8) with 64; lia | exact Hk].
Qed.

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

Section KS.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SF : statics_free B MR.
Hypothesis SFA : statics_facts B.
Hypothesis AX : YL01.AllocExtra B MR.

Lemma static_not_block : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ alloc_statics (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi Hs. destruct (in_blocks L A a k Hin) as (p & Hp & ->).
  exact (YL01.ax_blocks_img AX L A mem md p k i HM Hp Hi (proj1 (SFA _ Hs))).
Qed.

Lemma bpost_sandwich_s : forall K K1 E L A regs mem md mem1 regs1 L' A' regs2 mem2 md' mem3 regs3 W1 W3,
  MR L A mem md ->
  (forall a, spZ regs - K <= a < spZ regs -> writable_at (ms_segs B) mem a) ->
  alloc_ceiling + K <= spZ regs -> spZ regs < 2 ^ 63 ->
  (forall a, scratch_k B K1 regs1 a -> scratch_k B K regs a) ->
  (forall a, E a -> a < alloc_ceiling) ->
  (forall a, alloc_statics a -> E a) ->
  (forall a, in_img B a -> 0 <= a < alloc_ceiling) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - K <= x < spZ regs) -> ~ alloc_statics x -> outside W1 x) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - K <= x < spZ regs) -> ~ alloc_statics x -> outside W3 x) ->
  munch W1 mem mem1 -> wmono (ms_segs B) mem mem1 ->
  bpost B MR K1 E L A regs1 mem1 md L' A' regs2 mem2 md' ->
  munch W3 mem2 mem3 -> wmono (ms_segs B) mem2 mem3 ->
  guard_syms B -> ro_agree (ms_segs B) mem3 ->
  regs_preserved regs regs3 ->
  bpost B MR K E L A regs mem md L' A' regs3 mem3 md'.
Proof.
  intros K K1 E L A regs mem md mem1 regs1 L' A' regs2 mem2 md' mem3 regs3 W1 W3
    HM HWs Hac H63 HSC HE HSE HI HW1 HW3 MU1 WM1 BP MU3 WM3 GS RA3 RP.
  pose proof alloc_ceiling_val as Hacv.
  destruct BP as (HM2 & HWF & HBD & _ & Hmd & Hbl & Hbb & Hfr & Hsc & _ & GK).
  assert (OW : forall L0 A0 m0 md0 W a, MR L0 A0 m0 md0 -> owned B L0 A0 a ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - K <= x < spZ regs) -> ~ alloc_statics x -> outside W x) ->
     outside W a).
  { intros L0 A0 m0 md0 W a H0 Ho HW. pose proof (mr_owned_low _ _ (aa_laws API) L0 A0 m0 md0 a H0 Ho).
    apply HW; [lia | lia | intros Hs; exact (SF L0 A0 m0 md0 a H0 Hs Ho)]. }
  assert (MRW : forall L0 A0 m0 m0' md0 W, MR L0 A0 m0 md0 -> munch W m0 m0' ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - K <= x < spZ regs) -> ~ alloc_statics x -> outside W x) ->
     MR L0 A0 m0' md0).
  { intros L0 A0 m0 m0' md0 W H0 HW Ho.
    destruct (mr_model _ _ (aa_laws API) L0 A0 m0 md0 H0) as (Hh & Hl & Hm).
    eapply (mr_frame _ _ (aa_laws API) L0 A0 m0 m0' md0 md0 H0).
    - intros a Hown. pose proof (mr_owned_low _ _ (aa_laws API) L0 A0 m0 md0 a H0 Hown).
      apply (mbyte_munch _ W); [exact HW | lia | exact (OW _ _ _ _ W a H0 Hown Ho)].
    - intros a Hown Hp. pose proof (mr_owned_low _ _ (aa_laws API) L0 A0 m0 md0 a H0 Hown).
      apply (present_munch W m0); [exact HW | lia | exact (OW _ _ _ _ W a H0 Hown Ho) | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L0 A0 m0 md0 p n i H0 Hin Hi) as (Hp & H1 & H2 & _).
      apply (present_munch W m0); [exact HW | lia | | exact Hp].
      apply Ho; [lia | lia |]. intros Hs.
      exact (YL01.ax_blocks_img AX L0 A0 m0 md0 p n i H0 Hin Hi (proj1 (SFA _ Hs))).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  assert (HM1 : MR L A mem1 md) by exact (MRW _ _ _ _ _ W1 HM MU1 HW1).
  assert (NO : forall L0 A0 m0 md0 a, MR L0 A0 m0 md0 -> alloc_ceiling <= a -> ~ owned B L0 A0 a).
  { intros L0 A0 m0 md0 a H0 Ha Ho. pose proof (mr_owned_low _ _ (aa_laws API) L0 A0 m0 md0 a H0 Ho). lia. }
  split; [exact (MRW _ _ _ _ _ W3 HM2 MU3 HW3)|].
  split; [exact HWF|]. split; [exact HBD|]. split; [exact RP|]. split; [exact Hmd|]. split; [exact Hbl|].
  split.
  { intros a k i Hin Hi.
    pose proof (blocks_low B API L A mem md a k i HM Hin Hi) as Hlow.
    pose proof (static_not_block L A mem md a k i HM Hin Hi) as NS.
    assert (O3 : outside W3 (a + i)) by (apply HW3; [lia | lia | exact NS]).
    assert (O1 : outside W1 (a + i)) by (apply HW1; [lia | lia | exact NS]).
    rewrite (mbyte_munch _ W3 mem2 mem3 (a + i) MU3 ltac:(lia) O3).
    rewrite (Hbb a k i Hin Hi).
    exact (mbyte_munch _ W1 mem mem1 (a + i) MU1 ltac:(lia) O1). }
  split.
  { intros a Hr HnA HnA' Hsc0 HnE.
    assert (Hn1 : ~ scratch_k B K1 regs1 a) by (intros Hs; apply Hsc0; apply HSC; exact Hs).
    assert (Hout : ~ (spZ regs - K <= a < spZ regs)) by (intros Hs; apply Hsc0; left; exact Hs).
    assert (NS : ~ alloc_statics a) by (intros Hs; apply HnE; apply HSE; exact Hs).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (HI a Hr); lia]).
    assert (O3 : outside W3 a) by (apply HW3; assumption).
    assert (O1 : outside W1 a) by (apply HW1; assumption).
    destruct (Hfr a Hr HnA HnA' Hn1 HnE) as [Hm2 Hw2].
    split.
    - rewrite (mbyte_munch _ W3 mem2 mem3 _ MU3 Ha64 O3). rewrite Hm2.
      exact (mbyte_munch _ W1 mem mem1 _ MU1 Ha64 O1).
    - rewrite (writable_munch _ W1 mem mem1 a MU1 Ha64 O1). rewrite Hw2.
      exact (writable_munch _ W3 mem2 mem3 a MU3 Ha64 O3). }
  assert (GK3 : guard_kept B mem mem3).
  { destruct GS as [G1 _]. intros i Hi. specialize (GK i Hi). rewrite G1 in GK |- *.
    assert (NS : ~ alloc_statics (123752 + i)) by (unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia).
    rewrite (mbyte_munch _ W3 mem2 mem3 (123752 + i) MU3 ltac:(lia) ltac:(apply HW3; [lia | lia | exact NS])).
    rewrite GK.
    exact (mbyte_munch _ W1 mem mem1 (123752 + i) MU1 ltac:(lia) ltac:(apply HW1; [lia | lia | exact NS])). }
  split; [|exact (conj RA3 GK3)].
  intros a Hs. apply WM3.
  assert (D : scratch_k B K1 regs1 a \/ ~ scratch_k B K1 regs1 a).
  { unfold scratch_k. destruct (Z.le_gt_cases (spZ regs1 - K1) a); destruct (Z.lt_ge_cases a (spZ regs1));
      destruct (Z.le_gt_cases (errno_addr B) a); destruct (Z.lt_ge_cases a (errno_addr B + 4));
      first [left; lia | right; lia]. }
  destruct D as [Hs1|Hs1]; [exact (Hsc a Hs1)|].
  destruct Hs as [Hs|Hs]; [|exfalso; apply Hs1; right; exact Hs].
  assert (Hw1 : writable_at (ms_segs B) mem1 a) by (apply WM1; apply HWs; exact Hs).
  assert (Hr : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
  assert (Hn1 : ~ owned B L A a) by (apply (NO _ _ _ _ a HM1); lia).
  assert (Hn2 : ~ owned B L' A' a) by (apply (NO _ _ _ _ a HM2); lia).
  assert (Hn3 : ~ E a) by (intros He; pose proof (HE a He); lia).
  destruct (Hfr a Hr Hn1 Hn2 Hs1 Hn3) as [_ Hw2].
  apply Hw2. exact Hw1.
Qed.

End KS.

Lemma cstr_trim : forall m s tb ts, cstr_at m s tb ts ->
  exists sl, cstr_at m s tb sl /\ Z.of_nat (length sl) = (- (s + Z.of_nat (length tb) + 1)) mod 8.
Proof.
  intros m s tb ts (Hb & Hn & Ha).
  set (k := (- (s + Z.of_nat (length tb) + 1)) mod 8) in *.
  assert (Hk : 0 <= k < 8) by (apply Z.mod_pos_bound; lia).
  exists (firstn (Z.to_nat k) ts).
  assert (Hl : length (firstn (Z.to_nat k) ts) = Z.to_nat k) by (rewrite length_firstn; lia).
  split; [|rewrite Hl; lia].
  split; [|split; [exact Hn | rewrite Hl; lia]].
  rewrite <- (firstn_skipn (Z.to_nat k) ts) in Hb.
  replace (tb ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) ts ++ skipn (Z.to_nat k) ts)
    with ((tb ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) ts) ++ skipn (Z.to_nat k) ts) in Hb
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.
