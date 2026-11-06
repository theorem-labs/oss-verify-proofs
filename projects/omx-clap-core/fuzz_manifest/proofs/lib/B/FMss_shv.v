(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_shv.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* The local shadow premise of the strstr lane's P-model walks.  The copied wrapper statements
   (lib/A/Prog/*_wrap_c.v) ask for `shadow_rw m` (AsanRT.v:29): every byte of the whole low and
   high shadow readable.  At a donor call site the memory is `mrestrict (w_H W) mem` and the
   donor keeps the shadow lazy (YG0n.v:300-302, :323; YK04.v:519-523), so that premise never
   holds there.  The walks need only the two aligned shadow words of each checked range
   (asan_memcpy.v:135-184, the only reader of shadow_rw); `shvis m p n` says those bytes are
   readable for [p, p + n) and every sub-range, which is what the donor's shadow_hull_vis
   (YG0d.v:310) gives. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import Img0 AsanRT AsanRTFacts BzBridge.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.asan_memcpy.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_qck.
Import ListNotations.
Open Scope Z_scope.

Module AMC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.asan_memcpy.
Module BzQ := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.I_qck.

(* the shadow bytes from the aligned word of [p]'s shadow to the aligned word of [p + n - 1]'s *)
Definition shvis (m : word -> option byte) (p n : Z) : Prop :=
  0 < n -> forall s, BzQ.al8 (BzS.shad p) <= s < BzQ.al8 (BzS.shad (p + n - 1)) + 8 ->
    exists b, mrd rsegs m (wa s) = Some b.

Lemma al8_shad_mono : forall x y, x <= y -> BzQ.al8 (BzS.shad x) <= BzQ.al8 (BzS.shad y).
Proof.
  intros x y H. unfold BzQ.al8, BzS.shad.
  assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia).
  assert ((x / 8 + BzS.SHB) / 8 <= (y / 8 + BzS.SHB) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma shvis_sub : forall m p n k n', shvis m p n -> 0 <= k -> 0 <= n' -> k + n' <= n -> shvis m (p + k) n'.
Proof.
  intros m p n k n' H Hk Hn' Hkn Hpos s Hs. apply H; [lia|].
  pose proof (al8_shad_mono p (p + k) ltac:(lia)).
  pose proof (al8_shad_mono (p + k + n' - 1) (p + n - 1) ltac:(lia)). lia.
Qed.

Lemma shvis_prefix : forall m p n n', shvis m p n -> n' <= n -> shvis m p n'.
Proof.
  intros m p n n' H Hn Hpos s Hs. apply H; [lia|].
  pose proof (al8_shad_mono (p + n' - 1) (p + n - 1) ltac:(lia)). lia.
Qed.

(* the shadow of an application interval lies in the shadow band *)
Lemma shvis_in_shadow : forall p n s, app_ivl p (p + n) -> 0 < n ->
  BzQ.al8 (BzS.shad p) <= s < BzQ.al8 (BzS.shad (p + n - 1)) + 8 -> in_shadow s.
Proof.
  intros p n s AI Hn Hs.
  pose proof (AI p ltac:(lia)) as A0. pose proof (AI (p + n - 1) ltac:(lia)) as A1.
  unfold BzQ.al8, BzS.shad, BzS.SHB in Hs.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A0, A1.
  destruct A0 as [A0|A0]; destruct A1 as [A1|A1].
  - left. Z.div_mod_to_equations. lia.
  - exfalso. pose proof (AI 0x7fff8000 ltac:(lia)) as X. unfold app_mem, LOWMEM_END, HIGHMEM_BEG in X. lia.
  - exfalso. lia.
  - right. Z.div_mod_to_equations. lia.
Qed.

(* which a stack-window munch keeps *)
Lemma shvis_kept : forall m m' p n, shvis m p n -> meta_kept m m' -> app_ivl p (p + n) -> shvis m' p n.
Proof.
  intros m m' p n H MK AI Hn s Hs. destruct (H Hn s Hs) as [b Hb]. exists b.
  rewrite (MK s); [exact Hb|]. exact (shvis_in_shadow p n s AI Hn Hs).
Qed.

(* and the normalized memory the moved walks run on keeps (strstr_wrap.v:83 shadow_rw_norm, locally) *)
Lemma shvis_norm : forall m p n, mem_inv rsegs m -> shvis m p n -> app_ivl p (p + n) ->
  shvis (normalize_cj rsegs m) p n.
Proof.
  intros m p n HMI H AI Hn s Hs. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  destruct (H Hn s Hs) as [b Hb]. exists b.
  pose proof (shvis_in_shadow p n s AI Hn Hs) as HS.
  assert (At : 0 <= s < 2^47).
  { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in HS. lia. }
  assert (Ea : bv_unsigned (wa s) = s) by (apply wa_unsigned; lia).
  rewrite mrd_normalize_cj; [exact Hb | exact RO |]. right. right. rewrite Ea. unfold TASK_SIZE; lia.
Qed.

(* asan_memcpy.v:135 shadow_word, from the eight bytes of the one word instead of the whole shadow *)
Lemma shadow_word_L : forall m x, mem_inv rsegs m -> app_mem x ->
  (forall j, 0 <= j < 8 -> exists b, mrd rsegs m (wa (BzQ.al8 (BzS.shad x) + j)) = Some b) ->
  exists w, BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) (BzQ.al8 (BzS.shad x)) [BzCl.C8 w].
Proof.
  intros m x HMI Hx HW. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  assert (HA : forall j, 0 <= j < 8 -> in_shadow (BzQ.al8 (BzS.shad x) + j)).
  { intros j Hj. unfold BzQ.al8, BzS.shad, BzS.SHB, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx.
    Z.div_mod_to_equations. destruct Hx as [Hx|Hx]; [left|right]; lia. }
  pose proof (in_shadow_range _ (HA 0 ltac:(lia))) as R0.
  pose proof (HA 7 ltac:(lia)) as R7.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in R7.
  destruct (AMC.bytes_exist m 8 (BzQ.al8 (BzS.shad x)) ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)) as (bs & L & B).
  { intros j Hj. change (Z.of_nat 8) with 8 in Hj. exact (HW j Hj). }
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). split; [cbn; tauto|].
  assert (E : BzCl.cells_bytes [BzCl.C8 (Z_to_bv 64 (bytes_le_to_Z bs))] = bs).
  { cbn [BzCl.cells_bytes BzCl.cbytes]. rewrite app_nil_r. exact (AMC.le8_of_len8 bs L). }
  rewrite E.
  assert (HL : BzQ.al8 (BzS.shad x) + Z.of_nat (length bs) <= TASK_SIZE)
    by (rewrite L; change (Z.of_nat 8) with 8; unfold TASK_SIZE; lia).
  exact (bytes_normalize_low m _ bs RO HL B).
Qed.

(* asan_memcpy.v:172 chk_ok_of_ours with shvis for shadow_rw *)
Lemma chk_ok_of_loc : forall m p n, mem_inv rsegs m -> shvis m p n -> addressable m p n -> end_in_app p n ->
  (n = 0 \/ app_mem (p + 7)) -> n <= 2^40 -> BzQ.chk_ok (normalize_cj rsegs m) p n.
Proof.
  intros m p n HMI HSV AD EA A7 HN. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  split; [exact (acc_normalize m p n RO AD)|]. split.
  - intros Hn. pose proof AD as (P0 & N0 & PE & H).
    destruct (H 0 ltac:(lia)) as (A0 & _). destruct (H (n - 1) ltac:(lia)) as (A1 & _).
    rewrite Z.add_0_r in A0. replace (p + (n - 1)) with (p + n - 1) in A1 by lia.
    pose proof (al8_shad_mono p (p + n - 1) ltac:(lia)) as LE.
    destruct (shadow_word_L m p HMI A0) as [w1 W1].
    { intros j Hj. apply (HSV ltac:(lia)). lia. }
    destruct (shadow_word_L m (p + n - 1) HMI A1) as [w2 W2].
    { intros j Hj. apply (HSV ltac:(lia)). lia. }
    exists w1, w2. split; assumption.
  - exact (AMC.rng_of_ours m p n AD EA A7 HN).
Qed.

(* wrap_kit.v:185 wrap_post without shadow_rw: the run keeps the shadow band (meta_kept) instead *)
Lemma wrap_post_L : forall W m m' m0' lo hi,
  mem_inv rsegs m -> asan_cells m ->
  mem_rel_cj rsegs m' m0' -> cj_same rsegs m m' ->
  munch W (normalize_cj rsegs m) m0' -> wmono rsegs (normalize_cj rsegs m) m0' -> stk rsegs m0' lo hi ->
  all_app W -> disjoint_from W RT_LO (RT_HI - RT_LO) ->
  munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo hi /\ asan_cells m' /\ meta_kept m m'.
Proof.
  intros W m m' m0' lo hi HMI HC E8 SAME MU WM ST AW DJ.
  pose proof (mem_rel_cj_normalize rsegs m (ro_agree_of_mem_inv m HMI)) as REL0.
  assert (MU' : munch W m m') by (eapply munch_rel_cj; [exact REL0 | exact E8 | exact SAME | exact MU]).
  assert (WM' : wmono rsegs m m') by (eapply wmono_rel_cj; [exact REL0 | exact E8 | exact SAME | exact WM]).
  split; [exact MU'|]. split; [exact WM'|]. split; [exact (mem_inv_of_normalized m m' HMI SAME)|].
  split; [exact (stk_of_normalized _ _ lo hi E8 ST)|].
  split; [exact (asan_cells_kept W m m' HC MU' DJ)|].
  exact (munch_meta W m m' MU' AW).
Qed.
