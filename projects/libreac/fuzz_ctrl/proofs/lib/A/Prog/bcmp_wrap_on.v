(* lib/A/Prog/bcmp_wrap_on.v -- route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane wave L1, writer a Theorem Labs lane): the PROOFS of the `_on`
   forms (statements in lib/A/Prog/bcmp_wrap_c_on.v) of bcmp_wrap_c.v's contracts. This file edits no line of bcmp_wrap_c.v, whose code changes since this file was written are IMG_HI from A.AsanRT.RT_GT in place of A.Contract.GT and the removal of `Require Contract` (bcmp_wrap.v and bcmp_wrap_F.v are not in this delivery).
   rule 24: no function proved here that is not already proved: bcmp_wrap's run is bcmp_wrap_F.v's, re-run with the
   narrowed premise (proofs/libreac/fuzz_ctrl/lib/A/Prog/bcmp_wrap_F.v:336-509, same script).

   PRE: `shadow_rw m` -> `shadow_rw_on (bcmp_wrap_shadow_R L R N) m`. The run READS shadow only in the two ASan range
   checks (bcmp_wrap_on.v:135-139), one per string, each inside a Theorem Labs lane's sh_word_on region of that string (none when
   N = 0). sh_word_on p n is the CONTIGUOUS span of aligned shadow words covering [p, p + n), not just the first and last
   word: the range check reads the first and last byte's words, and for n >= 65 the run takes the
   __asan_region_is_poisoned arm, whose mem_is_zero reads the whole span (a Theorem Labs lane audit, ROUTE C batch 2). Its other shadow_rw use carried the fact to the post
   (wrap_post_P, bcmp_wrap_F.v (not in this delivery)).
   POST: `shadow_rw m'` -> `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (wave form, a Theorem Labs lane 09:38Z), by
   ShadowRwOnT.shadow_rw_on_kept from the run's meta_kept + wmono.
   CLOSURE (two Theorem Labs lanes 15:30Z): one normalization twin only, lib.A.MemNorm. The P-normalization comes from
   lib/A/MemNormP.v and bcmp_wrap_F.v's (not in this delivery) helper lemmas from lib/A/Prog/bcmp_wrap_Fk.v (both image-A copies), never from
   the root lib/MemNormP.v / lib/MemNorm.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes ExecF.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c wrap_kit bcmp_wrap_Fk sh_word_on sh_word_on_bz asan_memcpy_on bcmp_wrap_c_on.
Import ListNotations.
Open Scope Z_scope.

Lemma wrap_post_P_on : forall (Pb : word -> bool) W m m' m0' lo hi,
  mem_inv rsegs m -> asan_cells m ->
  mem_rel_P rsegs Pb m' m0' -> same_P rsegs Pb m m' ->
  munch W (normalize_P rsegs Pb m) m0' -> wmono rsegs (normalize_P rsegs Pb m) m0' -> stk rsegs m0' lo hi ->
  all_app W -> disjoint_from W RT_LO (RT_HI - RT_LO) ->
  munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo hi /\ asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m').
Proof.
  intros Pb W m m' m0' lo hi HMI HC E8 SAME MU WM ST AW DJ.
  pose proof (mem_rel_P_normalize rsegs Pb m (ro_agree_of_mem_inv m HMI)) as REL0.
  assert (MU' : munch W m m') by (eapply munch_rel_P; [exact REL0 | exact E8 | exact SAME | exact MU]).
  assert (WM' : wmono rsegs m m') by (eapply wmono_rel_P; [exact REL0 | exact E8 | exact SAME | exact WM]).
  split; [exact MU'|]. split; [exact WM'|].
  split; [exact (mem_inv_of_normalized m m' HMI (cj_same_of_same_P Pb m m' SAME))|].
  split; [exact (stk_rel_P Pb m' m0' lo hi E8 ST)|].
  split; [exact (asan_cells_kept W m m' HC MU' DJ)|].
  exact (fun P H => A.ShadowRwOnT.shadow_rw_on_kept P m m' H (munch_meta W m m' MU' AW) WM').
Qed.

Lemma bcmp_wrap_F_core_on : forall (Pb : word -> bool) (RNG : footprint)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  (forall x, IMG_LO <= x < IMG_HI -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
  (forall x, bv_unsigned sp - BCMP_WRAP_K <= x < bv_unsigned sp ->
     Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
  (forall x, bv_unsigned a0 <= x < bv_unsigned a0 + bv_unsigned a2 ->
     Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
  (forall x, bv_unsigned a1 <= x < bv_unsigned a1 + bv_unsigned a2 ->
     Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
  (bv_unsigned a2 <> 0 -> forall x, sh_lo (bv_unsigned a0) <= x < sh_hi (bv_unsigned a0) (bv_unsigned a2) ->
     Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
  (bv_unsigned a2 <> 0 -> forall x, sh_lo (bv_unsigned a1) <= x < sh_hi (bv_unsigned a1) (bv_unsigned a2) ->
     Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
  (forall x, 0 <= x < 2^64 -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true -> x < 2^47 /\ RNG x 1%nat) ->
  rng_bytes RNG ->
  bytes_at rsegs m (bv_unsigned a0) ls ->
  bytes_at rsegs m (bv_unsigned a1) rs ->
  memcmp_model ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
  mem_inv rsegs m ->
  (bv_unsigned a2 <= 2^40)%Z ->
  addressable m (bv_unsigned a0) (bv_unsigned a2) -> addressable m (bv_unsigned a1) (bv_unsigned a2) ->
  end_in_app (bv_unsigned a0) (bv_unsigned a2) -> end_in_app (bv_unsigned a1) (bv_unsigned a2) ->
  (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7))%Z -> (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a1 + 7))%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw_on (bcmp_wrap_shadow_R (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)) m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  evtF rsegs RNG (bcmp_wrap_post_on ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (seg_rom rsegs)).
Proof.
  intros Pb RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ls rs v lo HPimg HPstk HPL HPR HPsL HPsR HB RB.
  intros BUFL BUFR HM HMI HN ADL ADR EAL EAR A7L A7R SEPL SEPR HST HK HLO HSP HC HSR HRB HRM HGCF HF4 HF5.
  unfold BCMP_WRAP_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof ADL as (L0 & N0 & LE & _). pose proof ADR as (R0 & _ & RE & _).
  unfold APPMEM_END in LE, RE, HSP. unfold HIGHMEM_BEG in HLO.
  assert (HM' : BzSF.memcmp_model (firstn (Z.to_nat (bv_unsigned a2)) ls) (firstn (Z.to_nat (bv_unsigned a2)) rs)
                  (Z.to_nat (bv_unsigned a2)) = Some v) by (rewrite memcmp_model_firstn; exact HM).
  assert (LL : (length (firstn (Z.to_nat (bv_unsigned a2)) ls) <= Z.to_nat (bv_unsigned a2))%nat)
    by (rewrite length_firstn; lia).
  assert (LR : (length (firstn (Z.to_nat (bv_unsigned a2)) rs) <= Z.to_nat (bv_unsigned a2))%nat)
    by (rewrite length_firstn; lia).
  assert (BL : bytes_at rsegs m (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)).
  { apply (bytes_at_prefix m _ _ (skipn (Z.to_nat (bv_unsigned a2)) ls)). rewrite firstn_skipn. exact BUFL. }
  assert (BR : bytes_at rsegs m (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs)).
  { apply (bytes_at_prefix m _ _ (skipn (Z.to_nat (bv_unsigned a2)) rs)). rewrite firstn_skipn. exact BUFR. }
  apply (evtF_P_lt Pb RNG RB HB).
  apply (evtF_mono rsegs (RNG_P rsegs Pb)
           (fun st => exists st0,
              BzH.frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v
                [(bv_unsigned sp - 4560, bv_unsigned sp)] (bv_unsigned sp - 4560) (normalize_P rsegs Pb m) st0
              /\ ms_rel_P rsegs Pb st st0 /\ same_P rsegs Pb m (ms_mem st))).
  - apply (evtF_normalize_P rsegs Pb _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply BzT.tramp_bcmp.
    apply (BzC.ibcmp_spec BzP.rip_proof mcmp_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6 F fc (normalize_P rsegs Pb m) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)
             (firstn (Z.to_nat (bv_unsigned a2)) ls) (firstn (Z.to_nat (bv_unsigned a2)) rs) v
             (bv_unsigned sp - 4560) (bv_unsigned sp - 4560)).
    + unfold BzC.bcmp_cell.
      apply (ro_cells_P_img Pb m _ _ HPimg);
        [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia |].
      apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HRB].
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + unfold BzW.cmp_pre.
      split; [exact LL|]. split; [exact LR|]. split; [exact HM'|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. split; [lia|].
      split.
      { apply (bytes_at_P_of_cj rsegs Pb m (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)).
        - intros i Hi. rewrite length_firstn in Hi. apply HPL. lia.
        - apply (bytes_normalize_low m _ _ RO); [rewrite length_firstn; unfold TASK_SIZE; lia | exact BL]. }
      split.
      { apply (bytes_at_P_of_cj rsegs Pb m (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs)).
        - intros i Hi. rewrite length_firstn in Hi. apply HPR. lia.
        - apply (bytes_normalize_low m _ _ RO); [rewrite length_firstn; unfold TASK_SIZE; lia | exact BR]. }
      split; [lia|]. split; [lia|].
      split.
      { apply (chk_ok_P_of_cj Pb m (bv_unsigned a0) (bv_unsigned a2)); [lia | lia | exact HPsL |].
        exact (chk_ok_of_ours_on _ m _ _ HMI (shadow_rw_on_mono _ (sh_word_on _ _) m (fun a H => or_introl H) HSR) (sh_word_on_cover _ _) ADL EAL A7L HN). }
      split.
      { apply (chk_ok_P_of_cj Pb m (bv_unsigned a1) (bv_unsigned a2)); [lia | lia | exact HPsR |].
        exact (chk_ok_of_ours_on _ m _ _ HMI (shadow_rw_on_mono _ (sh_word_on _ _) m (fun a H => or_intror H) HSR) (sh_word_on_cover _ _) ADR EAR A7R HN). }
      split.
      { apply (m2s_cells_P_of_cj Pb m HPimg). exact (BCB.m2s_cells_normalize m HMI HC). }
      apply (icells_mcmp_P_of_cj Pb m HPimg). exact (icells_mcmp_norm m HMI HC HGCF HRM HF4 HF5).
    + lia.
    + apply (stk_P_of_cj rsegs Pb m (bv_unsigned sp - 4560) (bv_unsigned sp) HPstk).
      apply (stk_normalize m (bv_unsigned sp - 4560) (bv_unsigned sp) HMI); [|unfold TASK_SIZE; lia].
      exact (stk_sub m lo (bv_unsigned sp - 4560) (bv_unsigned sp) HST ltac:(lia) ltac:(lia)).
    + lia.
    + unfold BzR.kHighShadowEnd. lia.
    + lia.
    + exact (bz_mem_inv_normalize_P Pb m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (stack_W_ok (bv_unsigned sp - 4560) (bv_unsigned sp) ltac:(unfold HIGHMEM_BEG; lia) ltac:(lia)
                ltac:(unfold APPMEM_END; lia)) as [AW DJ].
    destruct (wrap_post_P_on Pb [(bv_unsigned sp - 4560, bv_unsigned sp)] m (ms_mem st) m0'
                (bv_unsigned sp - 4560) (bv_unsigned sp) HMI HC E8 SAME MU WM ST AW DJ)
      as (MU' & WM' & MI' & ST' & HC' & HSR').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [exact MU'|split; [exact WM'|split; [exact MI'|split; [|split; [exact HC'|split; [exact HSR'|split]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + exact (stk_join m (ms_mem st) lo (bv_unsigned sp - 4560) (bv_unsigned sp) HST ST' MU' ltac:(lia)).
    + apply (bytes_at_transport rsegs [(bv_unsigned sp - 4560, bv_unsigned sp)] m (ms_mem st)); [exact BL | exact MU' |].
      rewrite length_firstn. cbn [disjoint_from]. split; [lia | exact I].
    + apply (bytes_at_transport rsegs [(bv_unsigned sp - 4560, bv_unsigned sp)] m (ms_mem st)); [exact BR | exact MU' |].
      rewrite length_firstn. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Theorem bcmp_wrap_holds_F_on : bcmp_wrap_contract_F_on.
Proof.
  unfold bcmp_wrap_contract_F_on.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v lo.
  cbv zeta. intros BUFL BUFR HM HMI HN ADL ADR EAL EAR A7L A7R SEPL SEPR HST HK HLO HSP HC HSR HRB HRM HGCF HF4 HF5
    RB RIMG RSTK RL RSL RR RSR.
  unfold BCMP_WRAP_K in *.
  pose proof ADL as (L0 & N0 & LE & _). pose proof ADR as (R0 & _ & RE & _).
  unfold APPMEM_END in LE, RE, HSP. unfold HIGHMEM_BEG in HLO.
  apply (bcmp_wrap_F_core_on
           (bcmp_P (bv_unsigned sp - 4560) (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)) RNG);
    try assumption.
  - intros x Hx. left. apply P_img. exact Hx.
  - intros x Hx. unfold BCMP_WRAP_K in Hx. left. apply P_stk; lia.
  - intros x Hx. left. apply P_buf1; lia.
  - intros x Hx. left. apply P_buf2; lia.
  - intros Hne x Hx. left. apply P_sh1; lia.
  - intros Hne x Hx. left. apply P_sh2; lia.
  - intros x Hx [HPx|HSx].
    + split.
      * rewrite <- (wa_unsigned x ltac:(lia)).
        refine (P_lt _ _ _ _ _ _ _ _ _ _ _ _ _ HPx); lia.
      * unfold bcmp_P in HPx. apply existsb_exists in HPx as (r & Hin & Hr). cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst r.
        -- cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. rewrite wa_unsigned in Hr by lia.
           unfold IMG_LO, IMG_HI in Hr.
           exact (rng_byte RNG IMG_LO (IMG_HI - IMG_LO) x RIMG ltac:(unfold IMG_LO, IMG_HI; lia)
                    ltac:(unfold IMG_LO, IMG_HI; lia)).
        -- cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. rewrite wa_unsigned in Hr by lia.
           exact (rng_byte RNG (bv_unsigned sp - 4560) 4560 x RSTK ltac:(lia) ltac:(lia)).
        -- cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. rewrite wa_unsigned in Hr by lia.
           exact (rng_byte RNG (bv_unsigned a0) (bv_unsigned a2) x RL ltac:(lia) ltac:(lia)).
        -- cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. rewrite wa_unsigned in Hr by lia.
           exact (rng_byte RNG (bv_unsigned a1) (bv_unsigned a2) x RR ltac:(lia) ltac:(lia)).
        -- unfold shad_ivl in Hr. destruct (Z.eqb_spec (bv_unsigned a2) 0) as [EN|EN]; cbn [fst snd] in Hr;
             apply in_ivl_b_range in Hr; rewrite wa_unsigned in Hr by lia; [lia|].
           destruct RSL as [EZ|RSL]; [lia|]. unfold sh_lo, sh_hi in Hr.
           exact (rng_byte RNG (8 * (shadow_addr (bv_unsigned a0) / 8))
                    (8 * (shadow_addr (bv_unsigned a0 + bv_unsigned a2 - 1) / 8) + 8
                       - 8 * (shadow_addr (bv_unsigned a0) / 8)) x RSL ltac:(lia) ltac:(lia)).
        -- unfold shad_ivl in Hr. destruct (Z.eqb_spec (bv_unsigned a2) 0) as [EN|EN]; cbn [fst snd] in Hr;
             apply in_ivl_b_range in Hr; rewrite wa_unsigned in Hr by lia; [lia|].
           destruct RSR as [EZ|RSR]; [lia|]. unfold sh_lo, sh_hi in Hr.
           exact (rng_byte RNG (8 * (shadow_addr (bv_unsigned a1) / 8))
                    (8 * (shadow_addr (bv_unsigned a1 + bv_unsigned a2 - 1) / 8) + 8
                       - 8 * (shadow_addr (bv_unsigned a1) / 8)) x RSR ltac:(lia) ltac:(lia)).
    + pose proof (in_seg_img _ HSx) as Hi. rewrite wa_unsigned in Hi by lia.
      unfold IMG_LO, IMG_HI in Hi. split; [lia|].
      exact (rng_byte RNG IMG_LO (IMG_HI - IMG_LO) x RIMG ltac:(unfold IMG_LO, IMG_HI; lia)
               ltac:(unfold IMG_LO, IMG_HI; lia)).
Qed.

Lemma bcmp_wrap_contract_on_of_F_on : bcmp_wrap_contract_F_on -> bcmp_wrap_contract_on.
Proof.
  unfold bcmp_wrap_contract_F_on, bcmp_wrap_contract_on. cbv zeta. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v lo.
  intros BL BR HM HMI HN ADL ADR EL ER AL AR SL SR HST HK HLO HSP HC HSR HRB HRM HGCF HCF1 HCF2.
  pose proof ADL as (L0 & N0 & LE & _). pose proof ADR as (R0 & _ & RE & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. unfold HIGHMEM_BEG, APPMEM_END in *.
  apply (evtF_evt rsegs RNG_all). apply HF; try assumption; try right;
    first [ intros ? ? ? ? ?; exact I | apply rng_all ];
    unfold shadow_addr, ASAN_K, IMG_LO, IMG_HI; Z.div_mod_to_equations; lia.
Qed.

Theorem bcmp_wrap_holds_on : bcmp_wrap_contract_on.
Proof. exact (bcmp_wrap_contract_on_of_F_on bcmp_wrap_holds_F_on). Qed.

Print Assumptions bcmp_wrap_holds_F_on.
Print Assumptions bcmp_wrap_holds_on.
