(* lib/A/Prog/TwAsan.v (a Theorem Labs lane's port, unchanged from a working branch affce6489c8) with the local-shadow change
   (FMss_shv.v): TW_ASAN's `shadow_rw m` becomes `shv2 m a0 a1 hb nb` (the shadow words of the haystack's and the
   needle's checked bytes) and tw_asan_kept keeps it through shvis_kept.  Same names as the original; import this
   module instead of TwAsan. *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import Img0 AsanRT FMss_shv.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require AsanRTFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require Import TwFrame2.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require memchr_c memcmp_c memchr_wrap_c memcmp_wrap_c.
Import ListNotations.
Open Scope Z_scope.

Definition shv2 (m : word -> option byte) (a0 a1 : word) (hb nb : list byte) : Prop :=
  shvis m (bv_unsigned a0) (Z.of_nat (length hb) + 1) /\ shvis m (bv_unsigned a1) (Z.of_nat (length nb) + 1).

Definition TW_ASAN (sp a0 a1 : word) (m : word -> option byte) (hb nb : list byte) (lo : Z) : Prop :=
  Z.of_nat (length hb) + 1 <= 2^40 /\ Z.of_nat (length nb) + 1 <= 2^40 /\
  addressable m (bv_unsigned a0) (Z.of_nat (length hb) + 1) /\
  addressable m (bv_unsigned a1) (Z.of_nat (length nb) + 1) /\
  end_in_app (bv_unsigned a0) (Z.of_nat (length hb) + 1) /\ end_in_app (bv_unsigned a1) (Z.of_nat (length nb) + 1) /\
  (forall i, 0 <= i < Z.of_nat (length hb) + 1 -> app_mem (bv_unsigned a0 + i + 7)) /\
  (forall i, 0 <= i < Z.of_nat (length nb) + 1 -> app_mem (bv_unsigned a1 + i + 7)) /\
  HIGHMEM_BEG <= lo /\ bv_unsigned sp <= APPMEM_END /\ asan_cells m /\ shv2 m a0 a1 hb nb /\
  bytes_at rsegs m memchr_wrap_c.REAL_MEMCHR (le8 (wa memchr_c.MEMCHR)) /\
  bytes_at rsegs m memcmp_wrap_c.REAL_MEMCMP (le8 (wa memcmp_c.MEMCMP)) /\
  bytes_at rsegs m memcmp_wrap_c.GOT_CF (le8 (wa memcmp_wrap_c.CF)) /\
  bytes_at rsegs m (memcmp_wrap_c.CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (memcmp_wrap_c.CF + 255) [Z_to_bv 8 1].

Lemma tw_asan_kept : forall sp a0 a1 m m' hb nb lo lo' hi',
  TW_ASAN sp a0 a1 m hb nb lo -> munch [(lo', hi')] m m' -> wmono rsegs m m' ->
  lo <= lo' -> hi' <= bv_unsigned sp -> TW_ASAN sp a0 a1 m' hb nb lo.
Proof.
  intros sp a0 a1 m m' hb nb lo lo' hi'
    (LH & LN & ADH & ADN & EH & EN & PH & PN & HL & SPA & AC & SR & RMC & RMP & GCF & CF4 & CF5) MU WM L1 L2.
  assert (AW : AsanRTFacts.all_app [(lo', hi')]).
  { cbn [AsanRTFacts.all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. lia. }
  pose proof (AsanRTFacts.munch_meta _ _ _ MU AW) as MK.
  assert (D : forall a k, a + k <= HIGHMEM_BEG -> disjoint_from [(lo', hi')] a k).
  { intros a k Ha. cbn [disjoint_from]. split; [lia | exact I]. }
  unfold TW_ASAN.
  split; [exact LH|]. split; [exact LN|].
  split; [exact (AsanRTFacts.addressable_kept _ _ _ _ ADH MK)|].
  split; [exact (AsanRTFacts.addressable_kept _ _ _ _ ADN MK)|].
  split; [exact EH|]. split; [exact EN|]. split; [exact PH|]. split; [exact PN|].
  split; [exact HL|]. split; [exact SPA|].
  split. { apply (AsanRTFacts.asan_cells_kept _ _ _ AC MU). apply D. unfold RT_LO, RT_HI, HIGHMEM_BEG. lia. }
  split. { destruct SR as [SR1 SR2]. split; [exact (shvis_kept _ _ _ _ SR1 MK (AsanRTFacts.addressable_app _ _ _ ADH))
                                            | exact (shvis_kept _ _ _ _ SR2 MK (AsanRTFacts.addressable_app _ _ _ ADN))]. }
  split. { apply (bytes_at_transport rsegs _ _ _ _ _ RMC MU). apply D. rewrite length_le8.
           unfold memchr_wrap_c.REAL_MEMCHR, HIGHMEM_BEG. lia. }
  split. { apply (bytes_at_transport rsegs _ _ _ _ _ RMP MU). apply D. rewrite length_le8.
           unfold memcmp_wrap_c.REAL_MEMCMP, HIGHMEM_BEG. lia. }
  split. { apply (bytes_at_transport rsegs _ _ _ _ _ GCF MU). apply D. rewrite length_le8.
           unfold memcmp_wrap_c.GOT_CF, HIGHMEM_BEG. lia. }
  split. { apply (bytes_at_transport rsegs _ _ _ _ _ CF4 MU). apply D. cbn [length].
           unfold memcmp_wrap_c.CF, HIGHMEM_BEG. lia. }
  apply (bytes_at_transport rsegs _ _ _ _ _ CF5 MU). apply D. cbn [length].
  unfold memcmp_wrap_c.CF, HIGHMEM_BEG. lia.
Qed.

Lemma tw_end_sub : forall m p n k n', addressable m p n -> end_in_app p n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  end_in_app (p + k) n'.
Proof.
  intros m p n k n' AD EA Hk Hn' Hkn. unfold end_in_app in *.
  destruct (Z.eq_dec (k + n') n) as [E|NE].
  - destruct EA as [E0|EA]; [left; lia|]. right. replace (p + k + n') with (p + n) by lia. exact EA.
  - right. destruct AD as (_ & _ & _ & AB). destruct (AB (k + n') ltac:(lia)) as [AP _].
    replace (p + k + n') with (p + (k + n')) by lia. exact AP.
Qed.

Lemma tw_memchr_n_le : forall A (hb hs : list byte) j n, ~ In (Z_to_bv 8 0) hb -> (j <= length hb)%nat -> 0 <= n ->
  A + Z.of_nat (length hb) <> 0 ->
  0 <= memchr_wrap_c.memchr_n (A + Z.of_nat j) 0 n (skipn j hb ++ Z_to_bv 8 0 :: hs) <= Z.of_nat (length hb - j) + 1.
Proof.
  intros A hb hs j n NZ Hj Hn HA. unfold memchr_wrap_c.memchr_n.
  destruct (Z_lt_le_dec (Z.of_nat (length hb - j)) n) as [HIT|MISS].
  - rewrite (tw_memchr_res_hit A hb hs j n NZ Hj HIT).
    rewrite (proj2 (Z.eqb_neq _ _) HA). cbv iota. lia.
  - rewrite (tw_memchr_res_miss A hb hs j n NZ Hj MISS). rewrite Z.eqb_refl. cbv iota. lia.
Qed.
