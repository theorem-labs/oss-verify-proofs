From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c reac_identity_init_c.
Import ListNotations.
Open Scope Z_scope.

Ltac rii_fixret :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* The 16-byte frame [sp - 16, sp) is application memory apart from the runtime's cells. *)
Lemma rii_frame_app : forall lo sp, HIGHMEM_BEG <= lo -> lo + 2224 <= sp -> sp <= APPMEM_END ->
  all_app [(sp + -16, sp)].
Proof.
  intros lo sp H1 H2 H3. cbn [all_app]. split; [|exact I].
  intros a Ha. unfold app_mem. right. lia.
Qed.

Lemma rii_frame_rt : forall lo sp, HIGHMEM_BEG <= lo -> lo + 2224 <= sp ->
  disjoint_from [(sp + -16, sp)] RT_LO (RT_HI - RT_LO).
Proof.
  intros lo sp H1 H2. cbn [disjoint_from]. split; [|exact I].
  unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
Qed.

Lemma rii_sub_frame : forall sp id, sub_fp [(sp + -16, sp)] [(sp - 2224, sp); (id, id + 38)].
Proof. intros sp id x (H1 & _). cbn [outside]. split; [lia | exact I]. Qed.

Lemma rii_sub_frame0 : forall sp, sub_fp [(sp + -16, sp)] [(sp - 16, sp)].
Proof. intros sp x (H1 & _). cbn [outside]. split; [lia | exact I]. Qed.

Lemma rii_sub_call : forall sp id,
  sub_fp [(id, id + 38); (sp + -16 - 2208, sp + -16)] [(sp - 2224, sp); (id, id + 38)].
Proof. intros sp id x (H1 & H2 & _). cbn [outside]. split; [lia|]. split; [lia | exact I]. Qed.

Theorem reac_identity_init_holds : asan_memset_contract -> reac_identity_init_contract.
Proof.
  intros AMS. unfold asan_memset_contract, ASAN_MEMSET_K in AMS. cbv zeta in AMS.
  unfold reac_identity_init_contract, REAC_IDENTITY_INIT, REAC_IDENTITY_INIT_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo id idb
    -> Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WVS : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; apply (rc_wv_stk rsegs m lo (bv_unsigned sp)); [exact ST | lia]).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rii_frame_app lo (bv_unsigned sp) HHM HLO HAE) as AA.
  pose proof (rii_frame_rt lo (bv_unsigned sp) HHM HLO) as DRT.
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (munch_meta _ m m1 MU AA) as MK.
  pose proof (asan_cells_kept _ m m1 HC MU DRT) as HC1.
  pose proof (shadow_rw_kept m m1 HSW MK WM) as HSW1.
  assert (MI1 : mem_inv rsegs m1) by (first [exact MI | exact (rc_mem_inv_frame rsegs m m1 _ _ MI MU WVS)]).
  step.
  if_cases E; cbv iota; zify_cond E.
  - (* id = 0: the frame only *)
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold reac_identity_init_post, reac_identity_init_W, REAC_IDENTITY_INIT_K,
      REAC_IDENTITY_INIT_FRAME.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m1.
    split; [reflexivity|].
    split; [exact (munch_weaken _ _ m m1 (rii_sub_frame (bv_unsigned sp) id) MU)|].
    split; [exact WM|]. split; [exact MI1|]. split; [exact ST|]. split; [exact HC1|]. split; [exact HSW1|].
    split; [intros _; exact (munch_weaken _ _ m m1 (rii_sub_frame0 (bv_unsigned sp)) MU)|].
    intros H. exfalso. exact (H E).
  - (* id <> 0: __asan_memset(id, 0, 38) *)
    destruct (HS1 E) as [_ RW]. destruct (HAD E) as [ADR EIA].
    pose proof (HRT E) as HRT'. pose proof (HSP E) as HSP'.
    pose proof (rw_cells_transport rsegs _ m m1 id _ RW MU WM
                  ltac:(cbn [disjoint_from cells_size csize]; split; [lia | exact I])) as RW1.
    pose proof (addressable_kept m m1 id 38 ADR MK) as ADR1.
    pose proof ADR1 as (_ & _ & _ & HA7).
    pose proof (proj1 (HA7 7 ltac:(lia))) as A7.
    assert (EU1 : bv_unsigned (Z_to_bv 64 id) = id) by (apply unsigned_lit; lia).
    assert (EU2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16)
      by (apply unsigned_lit; lia).
    step. step. step.
    eapply evt_cut.
    { eapply AMS with (junk := idb) (lo := lo).
      all: rewrite ?EU1, ?EU2; try change (bv_unsigned (Z_to_bv 64 38)) with 38.
      - exact RW1.
      - lia.
      - exact ADR1.
      - exact EIA.
      - right. exact A7.
      - exact HRT'.
      - lia.
      - exact ST.
      - lia.
      - exact HHM.
      - lia.
      - exact HC1.
      - exact HSW1.
      - exact MI1. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                -> & MU2 & WM2 & MI2 & ST2 & RW2 & HC2 & HSW2).
    unfold ASAN_MEMSET_K in MU2.
    rewrite !unsigned_lit in MU2 by lia.
    rewrite unsigned_lit in ST2 by lia.
    rewrite !unsigned_lit in RW2 by lia.
    change (Z.to_nat 38) with 38%nat in RW2.
    change (0 mod 256) with 0 in RW2.
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2
                  ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | split; [lia | exact I]])) as FR2.
    rii_fixret.
    step. step. step.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold reac_identity_init_post, reac_identity_init_W, REAC_IDENTITY_INIT_K.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
    split; [reflexivity|].
    split.
    { apply (munch_trans _ m m1 m2).
      - exact (munch_weaken _ _ m m1 (rii_sub_frame (bv_unsigned sp) id) MU).
      - exact (munch_weaken _ _ m1 m2 (rii_sub_call (bv_unsigned sp) id) MU2). }
    split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact HC2|]. split; [exact HSW2|].
    split; [intros H; exfalso; exact (E H)|]. intros _. exact RW2.
Qed.
