(* asan_set_shadow_contract_F (asan_set_shadow_cF.v) by route 1 (ROUTE1.md (a working note, not in this delivery)), as asan_memsetF.v proves
   asan_memset_contract_F: the EXISTING walk -- here the plain contract asan_set_shadow_contract entry v, which
   asan_set_shadow.v proves from memset_contract for the 00 / f5 / f8 instances -- runs UNCHANGED on the restricted
   memory normalize_P m, where P keeps the image [IMG_LO, IMG_HI) and the written range [A, A + N).
   MemNormP.evtF_normalize_P turns that run into a footprint run on m with footprint RNG_P; the rng premises weaken
   RNG_P to RNG (MemNormP.evtF_RNG_P_weaken_top). The post comes back to m by the _rel_P transfer lemmas.
   The frame premise `rng RNG (sp - ASAN_SET_SHADOW_K) ASAN_SET_SHADOW_K` is not used: ASAN_SET_SHADOW_K = 0 and the
   run touches no stack byte, so P does not keep any.
   The generic theorem asan_set_shadow_F_of_plain needs only the plain contract at the same entry and fill byte, so
   the 00, f5 and f8 instances close by the same one line.
   Helpers taken from asan_memsetF.v, not restated here: in_rngb / in_rngb_true (the kept byte set), in_seg_img
   (every loaded segment lies in the image), rw_cells_P (Bz cells into the restricted memory). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge BzCallBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memset_c asan_set_shadow_c asan_set_shadow.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset asan_memsetF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_set_shadow_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* The kept byte set P of the run: the image and the written range. *)
Definition PSS (A N : Z) (a : word) : bool :=
  in_rngb IMG_LO (IMG_HI - IMG_LO) (bv_unsigned a) || in_rngb A N (bv_unsigned a).

Lemma PSS_img : forall A N x, IMG_LO <= x < IMG_HI -> PSS A N (wa x) = true.
Proof.
  intros A N x Hx. unfold PSS. rewrite wa_unsigned by (unfold IMG_LO, IMG_HI in Hx; lia).
  apply orb_true_iff; left. apply in_rngb_true. lia.
Qed.

Lemma PSS_dst : forall A N x, 0 <= x < 2^64 -> A <= x < A + N -> PSS A N (wa x) = true.
Proof.
  intros A N x Hx H. unfold PSS. rewrite wa_unsigned by exact Hx.
  apply orb_true_iff; right. apply in_rngb_true. lia.
Qed.

Lemma PSS_inv : forall A N x, 0 <= x < 2^64 -> PSS A N (wa x) = true ->
  IMG_LO <= x < IMG_HI \/ A <= x < A + N.
Proof.
  intros A N x Hx H. unfold PSS in H. rewrite wa_unsigned in H by exact Hx.
  apply orb_true_iff in H as [H|H]; apply in_rngb_true in H; [left | right]; lia.
Qed.

(* Into the restricted memory. *)
Lemma bytes_at_img_P : forall (P : word -> bool) m a bs,
  (forall x, IMG_LO <= x < IMG_HI -> P (wa x) = true) -> ro_agree rsegs m ->
  IMG_LO <= a -> a + Z.of_nat (length bs) <= IMG_HI ->
  bytes_at rsegs m a bs -> bytes_at rsegs (MemNormP.normalize_P rsegs P m) a bs.
Proof.
  intros P m a bs PI RO H1 H2 H.
  apply (MemNormP.bytes_at_P_of_cj rsegs P m a bs).
  - intros i Hi. left. apply PI. lia.
  - apply bytes_normalize_low; [exact RO | unfold TASK_SIZE, IMG_HI in *; lia | exact H].
Qed.

Lemma asan_cells_P : forall (P : word -> bool) m,
  (forall x, IMG_LO <= x < IMG_HI -> P (wa x) = true) -> mem_inv rsegs m ->
  asan_cells m -> asan_cells (MemNormP.normalize_P rsegs P m).
Proof.
  intros P m PI HMI AC. pose proof (ro_agree_of_mem_inv m HMI) as RO. unfold asan_cells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply bytes_at_img_P; [exact PI | exact RO | | | eassumption]);
    rewrite ?length_le8, ?length_le4; cbn [length];
    unfold IMG_LO, IMG_HI, CELL_K, UAR, INITED, REPLACE, CANPOISON, HIEND, MIDBEG, MIDEND, REAL_MEMCPY, REAL_MEMSET,
      GOT_CELL_K, GOT_UAR, GOT_REPLACE, GOT_HIEND, GOT_MIDBEG, GOT_MIDEND, GOT_REAL_MEMSET; lia.
Qed.

(* The written range: k = 0 touches no byte, so only the bounds of rw_cells are left and they do not depend on the
   memory; k > 0 lies in the shadow, below TASK_SIZE, which is what rw_cb_normalize asks. *)
Lemma rw_cb_P_shadow : forall (P : word -> bool) m a k bs, mem_inv rsegs m ->
  (forall i, 0 <= i < Z.of_nat k -> in_shadow (a + i)) ->
  (forall i, 0 <= i < Z.of_nat k -> P (wa (a + i)) = true) ->
  rw_cells rsegs m a [CB k bs] -> rw_cells rsegs (MemNormP.normalize_P rsegs P m) a [CB k bs].
Proof.
  intros P m a k bs HMI HS HP H.
  destruct (Nat.eq_dec k 0) as [Ek|Ek].
  - subst k. destruct H as [[Hwf (B0 & B1 & _)] (W0 & W1 & _)].
    refine (conj (conj Hwf (conj B0 (conj B1 _))) (conj W0 (conj W1 _))).
    + intros i Hi. exfalso. cbn [cell_wf cells_wf] in Hwf. destruct Hwf as [Hl _].
      cbn [cells_bytes cbytes] in Hi. rewrite app_nil_r, Hl in Hi. lia.
    + intros i Hi. exfalso. cbn [cells_size csize] in Hi. lia.
  - apply rw_cb_of_bz. apply (rw_cells_P P m).
    + intros i Hi. apply HP. cbn [BzCl.cells_size BzCl.csize] in Hi. lia.
    + apply rw_cb_normalize; [exact HMI | exact H |].
      pose proof (in_shadow_task _ (HS (Z.of_nat k - 1) ltac:(lia))). lia.
Qed.

Theorem asan_set_shadow_F_of_plain : forall entry v,
  asan_set_shadow_contract entry v -> asan_set_shadow_contract_F entry v.
Proof.
  intros entry v PL. unfold asan_set_shadow_contract in PL. cbv zeta in PL.
  unfold asan_set_shadow_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk.
  cbv zeta. intros HSH HRW HC HMI RB RI _ RD.
  pose (P := PSS (bv_unsigned a0) (bv_unsigned a1)).
  assert (PI : forall x, IMG_LO <= x < IMG_HI -> P (wa x) = true).
  { intros x Hx. exact (PSS_img (bv_unsigned a0) (bv_unsigned a1) x Hx). }
  assert (PD : forall x, bv_unsigned a0 <= x < bv_unsigned a0 + bv_unsigned a1 -> P (wa x) = true).
  { pose proof RD as (D0 & D1 & _). intros x Hx.
    exact (PSS_dst (bv_unsigned a0) (bv_unsigned a1) x ltac:(lia) Hx). }
  assert (P0 : P (wa (2^64 - 1)) = false).
  { destruct (P (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
    destruct (PSS_inv (bv_unsigned a0) (bv_unsigned a1) (2^64 - 1) ltac:(lia) E) as [X|X].
    - unfold IMG_LO, IMG_HI in X. lia.
    - pose proof (HSH (2^64 - 1 - bv_unsigned a0) ltac:(lia)) as Hs.
      replace (bv_unsigned a0 + (2^64 - 1 - bv_unsigned a0)) with (2^64 - 1) in Hs by lia.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs. lia. }
  assert (S0 : MemNormP.in_seg rsegs (wa (2^64 - 1)) = false).
  { destruct (MemNormP.in_seg rsegs (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
    pose proof (in_seg_img (2^64 - 1) ltac:(lia) E) as X. unfold IMG_LO, IMG_HI in X. lia. }
  assert (HB : forall x, 0 <= x < 2^64 -> P (wa x) = true \/ MemNormP.in_seg rsegs (wa x) = true -> RNG x 1%nat).
  { intros x Hx [Hp|Hs].
    - destruct (PSS_inv (bv_unsigned a0) (bv_unsigned a1) x Hx Hp) as [X|X].
      + destruct RI as (_ & _ & R). apply R; lia.
      + destruct RD as (_ & _ & R). apply R; lia.
    - destruct RI as (_ & _ & R). pose proof (in_seg_img x Hx Hs). apply R; lia. }
  apply (MemNormP.evtF_RNG_P_weaken_top rsegs P RNG RB P0 S0 HB).
  clear HB P0 S0.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (MemNormP.mem_rel_P_normalize rsegs P m RO) as REL0.
  apply (ExecF.evtF_mono rsegs (MemNormP.RNG_P rsegs P) (fun st => exists st0,
            asan_set_shadow_post v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1
              (MemNormP.normalize_P rsegs P m) st0
            /\ MemNormP.ms_rel_P rsegs P st st0 /\ MemNormP.same_P rsegs P m (ms_mem st))).
  - apply (MemNormP.evtF_normalize_P rsegs P _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply (PL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNormP.normalize_P rsegs P m) junk).
    + exact HSH.
    + pose proof (bv_unsigned_in_range 64 a1) as RN. unfold bv_modulus in RN.
      change (2 ^ Z.of_N 64) with (2 ^ 64) in RN.
      apply rw_cb_P_shadow; [exact HMI | | | exact HRW]; intros i Hi; rewrite Z2Nat.id in Hi by lia.
      * apply HSH. lia.
      * apply PD. lia.
    + exact (asan_cells_P P m PI HMI HC).
    + intros x b Hx. unfold MemNormP.normalize_P in Hx.
      destruct (MemNormP.keepP rsegs P x); [exact (HMI x b Hx) | discriminate Hx].
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & RW).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    unfold asan_set_shadow_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [|split; [|split]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + eapply (MemNormP.munch_rel_P rsegs P); [exact REL0 | exact E8 | exact SAME | exact MU].
    + eapply (MemNormP.wmono_rel_P rsegs P); [exact REL0 | exact E8 | exact SAME | exact WM].
    + intros x b Hx. destruct (MemNormP.keepP rsegs P x) eqn:K.
      * exact (proj1 (cj_drop_false rsegs x (MemNormP.keepP_cj rsegs P x K))).
      * rewrite (SAME x K) in Hx. exact (HMI x b Hx).
    + destruct RW as [[Hwf Hb] Hw].
      split; [split; [exact Hwf | exact (MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 Hb)]
             | exact (MemNormP.wr_at_rel_P rsegs P _ _ _ _ E8 Hw)].
Qed.

Theorem asan_set_shadow_00_holds_F : memset_contract -> asan_set_shadow_00_contract_F.
Proof.
  intros MSC. exact (asan_set_shadow_F_of_plain ASAN_SET_SHADOW_00 0x00 (asan_set_shadow_00_holds MSC)).
Qed.

Theorem asan_set_shadow_f5_holds_F : memset_contract -> asan_set_shadow_f5_contract_F.
Proof.
  intros MSC. exact (asan_set_shadow_F_of_plain ASAN_SET_SHADOW_F5 0xf5 (asan_set_shadow_f5_holds MSC)).
Qed.

Theorem asan_set_shadow_f8_holds_F : memset_contract -> asan_set_shadow_f8_contract_F.
Proof.
  intros MSC. exact (asan_set_shadow_F_of_plain ASAN_SET_SHADOW_F8 0xf8 (asan_set_shadow_f8_holds MSC)).
Qed.
