(* The footprint twin of reac_identity_init.v (image B; RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF
   under a footprint RNG (reac_identity_init_contract_F), by the script of reac_identity_init.v over StepF's step. The
   function's own accesses are the store and the load of ra in its 16-byte frame, closed from the window premise. Its
   one callee, __asan_memset, is taken as a hypothesis in the same place as the old theorem takes asan_memset_contract,
   here in its footprint form: a Theorem Labs lane's shared statement asan_memset_contract_F (lib/B/Prog/asan_memset_cF.v),
   which a Theorem Labs lane proves (asan_memset_holds_F in asan_memsetF.v). reac_identity_init.v and its theorem are
   unchanged. *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import
  asan_memset_c asan_memset_cF reac_identity_init_c reac_identity_init.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memset_c_on asan_memset_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ShadowRwOnT.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The 8-aligned shadow word span of a window [p, p + n) (sh_word_rng of rng_asan.v, the premise of
   reac_identity_init_contract_F) covers that of any sub-range [p', p' + n'), n' > 0: the frame of __asan_memset
   below sp - 16. *)
Lemma rii_wincov : forall RNG p n p' n',
  sh_word_rng RNG p n -> 0 < n' -> p <= p' -> p' + n' <= p + n -> sh_word_rng RNG p' n'.
Proof.
  intros RNG p n p' n' [E|H] Hn' H1 H2; [lia|]. right.
  unfold sh_al8_lo, sh_al8_hi, shadow_addr in *.
  eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p p' 8 ltac:(lia) H1).
    pose proof (Z.div_le_mono (p / 8 + ASAN_K) (p' / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono (p' + n' - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono ((p' + n' - 1) / 8 + ASAN_K) ((p + n - 1) / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)).
    lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
Theorem reac_identity_init_F_holds : asan_memset_contract_F -> reac_identity_init_contract_F.
Proof.
  intros AMS.
  (* the shared statement, with its shadow word spans (sh_word_rng of rng_asan.v) written out *)
  unfold asan_memset_contract_F, ASAN_MEMSET_K, sh_word_rng, sh_al8_lo, sh_al8_hi in AMS. cbv zeta in AMS.
  unfold reac_identity_init_contract_F, REAC_IDENTITY_INIT, REAC_IDENTITY_INIT_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo id idb
    -> Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP RBY RIMG RWIN RWSA RWSH RRT RID.
  (* the byte-exact shadow span of the window is not used: the span the frame of __asan_memset needs comes from
     the 8-aligned span RWSA *)
  clear RWSH.
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
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (munch_meta _ m m1 MU AA) as MK.
  pose proof (asan_cells_kept _ m m1 HC MU DRT) as HC1.
  pose proof (shadow_rw_kept m m1 HSW MK WM) as HSW1.
  assert (MI1 : mem_inv rsegs m1) by (first [exact MI | exact (rc_mem_inv_frame rsegs m m1 _ _ MI MU WVS)]).
  step.
  if_cases E; cbv iota; zify_cond E.
  - (* id = 0: the frame only *)
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold reac_identity_init_post, reac_identity_init_W, REAC_IDENTITY_INIT_K,
      REAC_IDENTITY_INIT_FRAME.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m1.
    split; [reflexivity|].
    split; [exact (munch_weaken _ _ m m1 (rii_sub_frame (bv_unsigned sp) id) MU)|].
    split; [exact WM|]. split; [exact MI1|]. split; [exact ST|]. split; [exact HC1|]. split; [exact HSW1|].
    split; [intros _; exact (munch_weaken _ _ m m1 (rii_sub_frame0 (bv_unsigned sp)) MU)|].
    intros H. exfalso. exact (H E).
  - (* id <> 0: __asan_memset(id, 0, 38) *)
    destruct (HS1 E) as [_ RW]. destruct (HAD E) as [ADR EIA].
    destruct (RID E) as [RD RDS].
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
    eapply evtF_cut.
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
      - exact MI1.
      - exact RBY.
      - exact RIMG.
      - (* the callee's window [sp - 16 - 2208, sp - 16) inside this function's window *)
        eapply rng_sub; [exact RWIN | lia | lia].
      - exact RD.
      - right. unfold shadow_addr. replace (id + 38 - 1) with (id + 37) by lia. exact RDS.
      - (* the 8-aligned shadow word span of the callee's window, inside that of this function's window *)
        exact (rii_wincov RNG (bv_unsigned sp - 2224) 2224 (bv_unsigned sp + -16 - 2208) 2208 RWSA
                 ltac:(lia) ltac:(lia) ltac:(lia)). }
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
    apply evtF_done. unfold reac_identity_init_post, reac_identity_init_W, REAC_IDENTITY_INIT_K.
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

(* RECIPE step 1: the old theorem's statement, back from the footprint form at ExecF.RNG_all, from the same callee
   contract (in footprint form) as the old theorem. *)
Theorem reac_identity_init_holds_of_F : asan_memset_contract_F -> reac_identity_init_contract.
Proof. intros AMS. exact (reac_identity_init_contract_of_F (reac_identity_init_F_holds AMS)). Qed.


(* ------------------------------------------------------------------------------------------------------------ *)
(* Route (C), the CALLEE case (a Theorem Labs lane 09:58Z): the theorem above keeps its statement and its own proof; this one is NEW
   and takes the callee's NARROWED contract. The script is the same run; the three differences are
     - the shadow premise is the region one, shadow_rw_on (reac_identity_init_shadow_R id) m;
     - the callee's shadow premise is that region cut down to the memset's own
       (asan_memset_shadow_R = sh_word_on id 38) by ShadowRwOn.shadow_rw_on_mono, under the id <> 0 branch;
     - the post carries ANY region across the run (the wave's form): m -> m1 by
       ShadowRwOnT.shadow_rw_on_kept, and m1 -> m2 by the memset _on post's own transport. *)
Theorem reac_identity_init_F_holds_on :
  asan_memset_contract_F_on -> reac_identity_init_contract_F_on.
Proof.
  intros AMS.
  unfold asan_memset_contract_F_on, ASAN_MEMSET_K, sh_word_rng, sh_al8_lo, sh_al8_hi in AMS. cbv zeta in AMS.
  unfold reac_identity_init_contract_F_on, REAC_IDENTITY_INIT, REAC_IDENTITY_INIT_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo id idb
    -> Hid HS1 MI ST HLO HHM HAE HC HSW HAD HRT HSP RBY RIMG RWIN RWSA RWSH RRT RID.
  clear RWSH.
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
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (munch_meta _ m m1 MU AA) as MK.
  pose proof (asan_cells_kept _ m m1 HC MU DRT) as HC1.
  (* the frame stores keep EVERY shadow region, so the post's transport and the callee's premise both come from here *)
  assert (TR1 : forall P : Z -> Prop, ShadowRwOn.shadow_rw_on P m -> ShadowRwOn.shadow_rw_on P m1)
    by (intros P HP; exact (ShadowRwOnT.shadow_rw_on_kept P m m1 HP MK WM)).
  pose proof (TR1 _ HSW) as HSW1.
  assert (MI1 : mem_inv rsegs m1) by (first [exact MI | exact (rc_mem_inv_frame rsegs m m1 _ _ MI MU WVS)]).
  step.
  if_cases E; cbv iota; zify_cond E.
  - (* id = 0: the frame only *)
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. unfold reac_identity_init_post_on, reac_identity_init_W, REAC_IDENTITY_INIT_K,
      REAC_IDENTITY_INIT_FRAME.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m1.
    split; [reflexivity|].
    split; [exact (munch_weaken _ _ m m1 (rii_sub_frame (bv_unsigned sp) id) MU)|].
    split; [exact WM|]. split; [exact MI1|]. split; [exact ST|]. split; [exact HC1|]. split; [exact TR1|].
    split; [intros _; exact (munch_weaken _ _ m m1 (rii_sub_frame0 (bv_unsigned sp)) MU)|].
    intros H. exfalso. exact (H E).
  - (* id <> 0: __asan_memset(id, 0, 38) *)
    destruct (HS1 E) as [_ RW]. destruct (HAD E) as [ADR EIA].
    destruct (RID E) as [RD RDS].
    pose proof (HRT E) as HRT'. pose proof (HSP E) as HSP'.
    pose proof (rw_cells_transport rsegs _ m m1 id _ RW MU WM
                  ltac:(cbn [disjoint_from cells_size csize]; split; [lia | exact I])) as RW1.
    pose proof (addressable_kept m m1 id 38 ADR MK) as ADR1.
    pose proof ADR1 as (_ & _ & _ & HA7).
    pose proof (proj1 (HA7 7 ltac:(lia))) as A7.
    assert (EU1 : bv_unsigned (Z_to_bv 64 id) = id) by (apply unsigned_lit; lia).
    assert (EU2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16)
      by (apply unsigned_lit; lia).
    (* the callee's own region, from this run's region under the id <> 0 branch *)
    assert (HSWc : ShadowRwOn.shadow_rw_on (asan_memset_shadow_R (Z_to_bv 64 id) (Z_to_bv 64 38)) m1).
    { apply (ShadowRwOn.shadow_rw_on_mono (reac_identity_init_shadow_R id)); [|exact HSW1].
      intros x Hx. unfold asan_memset_shadow_R in Hx. rewrite EU1 in Hx.
      change (bv_unsigned (Z_to_bv 64 38)) with 38 in Hx.
      unfold reac_identity_init_shadow_R. split; [exact E | exact Hx]. }
    step. step. step.
    eapply evtF_cut.
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
      - exact HSWc.
      - exact MI1.
      - exact RBY.
      - exact RIMG.
      - eapply rng_sub; [exact RWIN | lia | lia].
      - exact RD.
      - right. unfold shadow_addr. replace (id + 38 - 1) with (id + 37) by lia. exact RDS.
      - exact (rii_wincov RNG (bv_unsigned sp - 2224) 2224 (bv_unsigned sp + -16 - 2208) 2208 RWSA
                 ltac:(lia) ltac:(lia) ltac:(lia)). }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                -> & MU2 & WM2 & MI2 & ST2 & RW2 & HC2 & TR2).
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
    apply evtF_done. unfold reac_identity_init_post_on, reac_identity_init_W, REAC_IDENTITY_INIT_K.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
    split; [reflexivity|].
    split.
    { apply (munch_trans _ m m1 m2).
      - exact (munch_weaken _ _ m m1 (rii_sub_frame (bv_unsigned sp) id) MU).
      - exact (munch_weaken _ _ m1 m2 (rii_sub_call (bv_unsigned sp) id) MU2). }
    split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact HC2|].
    split; [intros P HP; exact (TR2 P (TR1 P HP))|].
    split; [intros H; exfalso; exact (E H)|]. intros _. exact RW2.
Qed.
