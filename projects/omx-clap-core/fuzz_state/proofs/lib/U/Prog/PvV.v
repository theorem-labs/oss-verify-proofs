From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require YI06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import PvDefs PvModel PvGlue PvMain0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.

Lemma stk_back : forall m m0 lo hi, U.MemNorm.mem_rel rsegs m m0 -> Frame.stk rsegs m0 lo hi -> Frame.stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (U.MemNorm.wview_rel_rw rsegs m m0 _ HR (U.MemNorm.ro_false_of_wview rsegs m m0 _ HR Hw)). exact Hw.
  - exists b. rewrite (U.MemNorm.mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma pj_in_ok_norm : forall m q text len p d tb, U.MemNorm.ro_agree rsegs m ->
  (forall i, 0 <= i < 24 -> Mem.ro_addr rsegs (Z_to_bv 64 (q + i)) = false) ->
  pj_in_ok rsegs m q text len p d tb -> pj_in_ok rsegs (U.MemNorm.normalize rsegs m) q text len p d tb.
Proof.
  intros m q text len p d tb HRO Hq (H1 & H2 & H3 & H4 & H5).
  pose proof (U.MemNorm.mem_rel_normalize rsegs m HRO) as HR.
  split; [exact (U.MemNorm.bytes_at_normalize rsegs m _ _ HRO H1)|].
  split; [exact (U.MemNorm.bytes_at_normalize rsegs m _ _ HRO H2)|].
  split; [exact (U.MemNorm.bytes_at_normalize rsegs m _ _ HRO H3)|].
  split; [apply (U.MemNorm.wr_at_norm rsegs m _ q 24 HR H4); intros i Hi; exact (Hq i Hi)|].
  destruct H5 as (H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [exact (U.MemNorm.bytes_at_normalize rsegs m _ _ HRO H10)|]. split; [exact H11 | exact H12].
Qed.

Lemma pj_in_ok_back : forall m m0 q text len p d tb, U.MemNorm.mem_rel rsegs m m0 ->
  pj_in_ok rsegs m0 q text len p d tb -> pj_in_ok rsegs m q text len p d tb.
Proof.
  intros m m0 q text len p d tb HR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  split; [exact (proj2 (U.MemNorm.bytes_at_rel rsegs m m0 _ _ HR) H1)|].
  split; [exact (proj2 (U.MemNorm.bytes_at_rel rsegs m m0 _ _ HR) H2)|].
  split; [exact (proj2 (U.MemNorm.bytes_at_rel rsegs m m0 _ _ HR) H3)|].
  split; [exact (U.MemNorm.wr_at_rel rsegs m m0 _ _ HR H4)|].
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [exact (proj2 (U.MemNorm.bytes_at_rel rsegs m m0 _ _ HR) H10)|]. split; [exact H11 | exact H12].
Qed.

Lemma zeros_sub : forall m a (N : nat) off len, Mem.bytes_at rsegs m a (repeat (Z_to_bv 8 0) N) ->
  0 <= off -> off + Z.of_nat len <= Z.of_nat N -> Mem.bytes_at rsegs m (a + off) (repeat (Z_to_bv 8 0) len).
Proof.
  intros m a N off len (H1 & H2 & H) Ho Hl. rewrite repeat_length in H2.
  split; [lia|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi.
  replace (a + off + Z.of_nat i) with (a + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite H by (rewrite repeat_length; lia).
  rewrite !pj_nth_repeat by lia. reflexivity.
Qed.

Section V.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

Lemma vb_disj : forall L A mem md a1 n1 a2 n2, MR L A mem md ->
  In (a1, n1) (blocks L A) -> In (a2, n2) (blocks L A) -> (a1, n1) <> (a2, n2) -> 0 < n1 -> 0 < n2 ->
  a1 + n1 <= a2 \/ a2 + n2 <= a1.
Proof.
  intros L A mem md a1 n1 a2 n2 HM H1 H2 Hne Hn1 Hn2.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A mem md HM) as HP.
  destruct (U.Reusable.YI06.pairwise_in2 _ _ _ _ HP H1 H2 Hne) as [Hd|Hd]; unfold ranges_disjoint in Hd; cbn in Hd; lia.
Qed.

Lemma vb_lblock : forall L A mem Lam peak cnt fail a k, ledger B L A mem Lam peak cnt fail -> In (a, k) Lam ->
  0 <= k /\ In (a - 16, k + 16) (blocks L A).
Proof.
  intros L A mem Lam peak cnt fail a k (_ & _ & _ & _ & _ & HF) Hin. rewrite Forall_forall in HF.
  destruct (HF _ Hin) as (H1 & H2 & _). split; [exact H1 | exact H2].
Qed.

Lemma v_heads : forall L A mem md Lam peak cnt fail S v, MR L A mem md -> ledger B L A mem Lam peak cnt fail ->
  alloc_ceiling <= S -> pj_place (lin Lam) (fun a k => In (a, k) (blocks L A)) S (2 ^ 64) v ->
  forall a k x, In (a, k) Lam -> a - 16 <= x < a -> ~ (v <= x < v + 56).
Proof.
  intros L A mem md Lam peak cnt fail S v HM HL HS Hpl a k x Hin Hx Hv.
  destruct (vb_lblock _ _ _ _ _ _ _ _ _ HL Hin) as (Hk & Hraw).
  pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL Hin) as (Ra & Rb & _).
  destruct Hpl as [(H1 & _)|[(ra & rk & Hb & Hn & H1 & H2)|(a' & k' & Hl & H1 & H2)]].
  - lia.
  - assert (Hne : (ra, rk) <> (a - 16, k + 16)).
    { intro Eq. injection Eq as E1 E2. apply Hn. unfold lin. replace (ra + 16) with a by lia.
      replace (rk - 16) with k by lia. exact Hin. }
    destruct (vb_disj _ _ _ _ _ _ _ _ HM Hb Hraw Hne ltac:(lia) ltac:(lia)); lia.
  - destruct (vb_lblock _ _ _ _ _ _ _ _ _ HL Hl) as (Hk' & Hraw').
    destruct (Z.eq_dec a' a) as [->|Ha]; [lia|].
    assert (Hne : (a' - 16, k' + 16) <> (a - 16, k + 16)) by (intro Eq; injection Eq as E1 _; lia).
    destruct (vb_disj _ _ _ _ _ _ _ _ HM Hraw' Hraw Hne ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma pv_A : forall K S L A mem md Lam peak cnt fail mem' W (E : Z -> Prop) v,
  ms_segs B = rsegs -> MR L A mem md -> WF A -> bounded A -> ledger B L A mem Lam peak cnt fail -> rd_cells B mem ->
  alloc_ceiling <= S - K -> S <= 2 ^ 64 ->
  (forall k, 0 <= k < 8 -> in_img B (ms_got_guard B + k) /\ in_img B (ms_guard B + k)) ->
  (forall a, (S - K <= a < S \/ errno_addr B <= a < errno_addr B + 4) -> writable_at segs mem a) ->
  Frame.munch W mem mem' -> Frame.wmono segs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (alloc_ceiling <= x /\ (S - K <= x < S \/ E x)) \/ (v <= x < v + 56 /\ E x)) ->
  (forall i, 0 <= i < 56 -> ~ owned B L A (v + i) /\ ~ alloc_statics (v + i) /\ ~ in_img B (v + i)) ->
  (forall a k x, In (a, k) Lam -> a - 16 <= x < a -> ~ (v <= x < v + 56)) ->
  (forall i, 0 <= i < 56 -> ~ Frame.outside W (v + i) -> present mem' (v + i)) ->
  pv_mid B API K S L A mem md E L A mem' md /\ ledger B L A mem' Lam peak cnt fail /\ rd_cells B mem'.
Proof.
  intros K S L A mem md Lam peak cnt fail mem' W E v SEG HM HWF HB HL RC Hc HS HG HWr MU WM HW HV HH HP.
  pose proof ceil_big as Cb.
  assert (Himg : forall x, in_img B x -> x < 0x55000) by (intros x Hx; apply (img_iff B SEG) in Hx; lia).
  assert (Hout : forall x, 0 <= x < 2 ^ 64 -> x < alloc_ceiling -> ~ (v <= x < v + 56) -> Frame.outside W x).
  { intros x Hx H1 H2. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
    destruct (HW x Hx Ho) as [(H3 & _)|(H3 & _)]; lia. }
  assert (Hvi : forall x, v <= x < v + 56 -> ~ in_img B x).
  { intros x Hx. destruct (HV (x - v) ltac:(lia)) as (_ & _ & H). replace (v + (x - v)) with x in H by lia. exact H. }
  split.
  - apply (mid_A B API (pv_img_low B SEG) K S L A mem md mem' W E HM HWF HB HWr MU WM).
    + intros x Hx Ho. destruct (HW x Hx Ho) as [(H1 & [H2|H2])|(H1 & H2)]; [left; left; exact H2 | right; exact H2 | right; exact H2].
    + intros x Hx Ho Hown. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Hown).
      destruct (HW x Hx Ho) as [(H1 & _)|(H1 & _)]; [lia|].
      destruct (HV (x - v) ltac:(lia)) as (Hno & _). apply Hno. replace (v + (x - v)) with x by lia. exact Hown.
    + intros p n i Hin Hi Ho. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as (_ & H1 & H2 & _).
      destruct (HW (ptr_addr L p + i) ltac:(lia) Ho) as [(H3 & _)|(H3 & H4)]; [lia|].
      split; [exact H4|]. pose proof (HP (ptr_addr L p + i - v) ltac:(lia)) as Q.
      replace (v + (ptr_addr L p + i - v)) with (ptr_addr L p + i) in Q by lia. exact (Q Ho).
  - split.
    + apply (ledger_A B API L A mem md mem' W Lam peak cnt fail HM HL MU).
      intros x Hx Ho. destruct (HW x Hx Ho) as [(H1 & _)|(H1 & _)].
      * split; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia|].
        intros a k Hin Hr. pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL Hin).
        pose proof (vb_lblock _ _ _ _ _ _ _ _ _ HL Hin). lia.
      * destruct (HV (x - v) ltac:(lia)) as (_ & Hst & _). replace (v + (x - v)) with x in Hst by lia.
        split; [exact Hst|]. intros a k Hin Hr. exact (HH a k x Hin ltac:(lia) H1).
    + destruct (HG 0 ltac:(lia)) as (G1 & G2). destruct (HG 7 ltac:(lia)) as (G3 & G4).
      apply (img_iff B SEG) in G1, G2, G3, G4.
      apply (rd_cells_A B mem mem' W RC MU); [lia | lia | lia | lia | |].
      * intros x Hro. pose proof (ro_low B SEG x Hro) as Hx. pose proof (bv_unsigned_in_range 64 x) as R.
        unfold bv_modulus in R. cbn in R. apply Hout; [lia | lia |].
        intros Hv. apply (Hvi (bv_unsigned x) Hv). apply (img_iff B SEG). lia.
      * intros k Hk. destruct (HG k Hk) as (G5 & G6).
        pose proof (proj1 (img_iff B SEG _) G5) as I5. pose proof (proj1 (img_iff B SEG _) G6) as I6.
        split; (apply Hout; [lia | lia | intros Hv; eapply Hvi; [exact Hv | assumption]]).
Qed.

End V.
