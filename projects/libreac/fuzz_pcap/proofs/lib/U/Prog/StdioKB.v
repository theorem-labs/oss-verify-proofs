From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import MState Mem Frame Cells Step Regs6ss ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel.
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

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? (symaddr ImgPages.Ubsan.top)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stk_of_writable : forall m lo hi, (symaddr ImgPages.Ubsan.top) <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a) -> stk rsegs m lo hi.
Proof.
  intros m lo hi Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  specialize (H a Ha). unfold writable_at in H. split; [exact H|].
  unfold mrd. destruct (m (wa a)) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply H.
  unfold wview. change (Z_to_bv 64 a) with (wa a). rewrite E.
  rewrite (wa_unsigned a) by lia.
  rewrite (find_segment_above rsegs (symaddr ImgPages.Ubsan.top) a 1 rsegs_top) by lia. reflexivity.
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

Lemma outside_one : forall lo hi x, x < lo \/ hi <= x -> outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn. split; [lia | exact I]. Qed.

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

Lemma bytes_keep : forall m m' A bs, bytes_at rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> mbyte rsegs m' a = mbyte rsegs m a) ->
  bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (Ha & Hl & Hb) H. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite <- (Hb i Hi). exact (H (A + Z.of_nat i) ltac:(lia)).
Qed.

Lemma classic_outside : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_ge_dec x lo) as [H1|H1]; [left; split; [lia|exact H]|].
  destruct (Z_le_gt_dec hi x) as [H2|H2]; [left; split; [lia|exact H]|].
  right. intros [H3 _]. lia.
Qed.

Lemma task_mem_munch : forall W m m', task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview rsegs m x <> None) -> task_mem rsegs m'.
Proof.
  intros W m m' HT HW HI x b Hx.
  destruct (classic_outside W (bv_unsigned x)) as [Ho | Hn].
  - rewrite (HW x Ho) in Hx. exact (HT x b Hx).
  - specialize (HI x Hn). unfold wview in HI.
    destruct (m x) as [b0|] eqn:E; [exact (HT x b0 E)|].
    left. destruct (find_segment rsegs (bv_unsigned x) 1) as [s|]; [discriminate|]. exfalso. exact (HI eq_refl).
Qed.

Lemma rw_cells_bytes_eq : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' E.
  assert (S : cells_size cs' = cells_size cs).
  { rewrite <- (cells_bytes_length cs' Hwf'), <- (cells_bytes_length cs Hwf), E. reflexivity. }
  split; [split; [exact Hwf' | rewrite E; exact Hb] | rewrite S; exact Hw].
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
  assert (SZ : cells_size (cs1 ++ cs2) = (cells_size cs1 + cells_size cs2)%nat).
  { induction cs1 as [|c cs1 IH]; cbn; [reflexivity|]. rewrite IH. lia. }
  rewrite SZ. split.
  - intros [[[W1 W2] [B1 B2]] (H0 & H1 & H2)].
    rewrite (cells_bytes_length cs1 W1) in B2.
    split; split; try (split; assumption).
    + split; [lia|]. split; [lia|]. intros i Hi. apply H2. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply H2. lia.
  - intros [[[W1 B1] (H0 & H1 & H2)] [[W2 B2] (G0 & G1 & G2)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2 |- *.
    split; [split; [split; assumption | split; assumption]|].
    rewrite (cells_bytes_length cs1 W1) in *.
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hl|Hl]; [apply H2; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
    apply G2. lia.
Qed.

Definition mf_pre (h : Z) (fl pad0 rpos rend : word) : list cell :=
  [ C4 fl; C4 pad0; C8 rpos; C8 rend; C8 (wz A_MCLOSE);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz A_MREAD); C8 (wz A_MWRITE); C8 (wz A_MSEEK); C8 (wz (h + 280)); C8 (wz 1024) ].

Definition mf_post (h b n : Z) (md pad1 pos pad2 : word) (ung buf : list byte) : list cell :=
  [ C4 (wz 4294967295); C4 (wz 0); C8 (wz 0); C4 md; C4 (wz 4294967295); C4 (wz 4294967295); C4 pad1;
    C8 (wz (h + 232));
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 pos; C8 (wz n); C8 (wz n); C8 (wz b); C4 (wz 114); C4 pad2;
    CB 8 ung; CB 1024 buf ].

Lemma mfile_split : forall m h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf,
  rw_cells rsegs m h (mfile_cells h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf) <->
  rw_cells rsegs m h (mf_pre h fl pad0 rpos rend) /\ rw_cells rsegs m (h + 104) [C8 prev; C8 next] /\
  rw_cells rsegs m (h + 120) (mf_post h b n md pad1 pos pad2 ung buf).
Proof.
  intros. change (mfile_cells h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf)
    with (mf_pre h fl pad0 rpos rend ++ [C8 prev; C8 next] ++ mf_post h b n md pad1 pos pad2 ung buf).
  rewrite !rw_cells_app. cbn [cells_size csize mf_pre Nat.add].
  replace (h + Z.of_nat 104 + Z.of_nat 16) with (h + 120) by lia.
  replace (h + Z.of_nat 104) with (h + 104) by lia. tauto.
Qed.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

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

Lemma in_img_low : ms_segs B = rsegs -> forall a, in_img B a -> 0 <= a < (symaddr ImgPages.Ubsan.top).
Proof.
  intros HS a [_ (s & Hs & Ha)]. rewrite HS in Hs.
  assert (Hall : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? (symaddr ImgPages.Ubsan.top)) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall s Hs). apply Z.leb_le in Hall.
  pose proof (bv_unsigned_in_range 64 (fst s)) as R1. pose proof (bv_unsigned_in_range 64 (snd s)) as R2.
  unfold bv_modulus in R1, R2. lia.
Qed.

End KB.
