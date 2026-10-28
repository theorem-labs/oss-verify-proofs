(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W3 ASlot_W5 ASlot_W6 ASlot_W9 F_ntf_C.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RASlot_W2 RASlot_W4 RASlot_W3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ RCTX <= a < RCTX + 928
  \/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof. intros; left; assumption. Qed.
Lemma rta_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rta_fp st lo sp a. Proof. intros; right; left; assumption. Qed.
Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros; do 2 right; left. exists q; auto. Qed.
Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros; do 3 right. exists b, gh; auto. Qed.

Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).

Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
  rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Hypothesis HK1 : forall stX g3 msk k m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv bgusegs m' -> stk bgusegs m' lo spv ->
  rpres_except (rta_fp st lo spv) m m' ->
  rimplT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom bgusegs)).

Lemma rfin_block : forall stX g3 msk mZ (t0 t1 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 ->
  rmrep stX mZ -> mem_inv bgusegs mZ -> rw_cells bgusegs mZ (spv + -144) (FRM junk) -> stk bgusegs mZ lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mZ ->
  rimplT o (ta_fin stX g3 msk K) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) (wz (sxv msk)) a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x2b1ec8) fc None mZ (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros TR HA GM HM MR0 MRZ MIZ FRZ STZ PEZ.
  destruct (gmf_geom st stX sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds st m g3) as GB0.
  pose proof (rmeta_slot_bounds stX mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
  destruct (lowbit_facts msk ltac:(lia)) as (k & Hk & LB).
  unfold ta_fin. riprefixT. unfold RR, rt1_regs.
  eapply evt_mono.
  { eapply (rfin_walk stX mZ g3 msk lo MRZ MSZ ltac:(lia) CLO); [| exact FRZ| exact STZ| unfold spv; lia| exact MIZ].
    rewrite unsigned_lit by lia. symmetry; exact ECONC. }
  cbv beta. intros ms' (a1' & a2' & a3' & m' & k' & Hk' & LB' & -> & MU & WM & MI' & ST' & MR').
  assert (k' = k) by (rewrite LB in LB'; apply Z.pow_inj_r in LB'; lia). subst k'.
  eapply (HK1 stX g3 msk k m'); try eassumption; try lia.
  eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
  cbn [ivs_covered]. split; [|split; [|exact I]].
  - intros x Hx. apply rta_fp_stack. unfold spv in *; lia.
  - intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
Qed.

Lemma ravz_block : forall (pc : Z) stZ g3 mZ (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  (pc = 0x2b1e44 \/ pc = 0x2b1e50) ->
  ta_rel sc st stZ -> active stZ sc = Some g3 -> gmf st sc g3 ->
  rmrep stZ mZ -> mem_inv bgusegs mZ -> rw_cells bgusegs mZ (spv + -144) (FRM junk) -> stk bgusegs mZ lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mZ ->
  rimplT o (ta_avz K bail stZ g3) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 pc) fc None mZ (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros PC TR HA GM MRZ MIZ FRZ STZ PEZ.
  destruct (gmf_geom st stZ sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stZ mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
  destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
  pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & _ & _).
  assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
  unfold ta_avz, activate_group.
  destruct (m_avail (get_meta_rec stZ g3) =? 0) eqn:AV0; [|unfold guard; apply rimplT_undef].
  apply Z.eqb_eq in AV0. unfold guard at 1. cbv beta.
  rewrite EM, Hmem. cbn [default].
  replace (group_active_idx stZ b) with (g_active_idx gh1).
  2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  set (act := mask_upto (g_active_idx gh1)). set (f := m_freed (get_meta_rec stZ g3)).
  destruct (Z.land f act =? 0) eqn:MZ; unfold guard; cbn [negb]; [apply rimplT_undef|].
  apply Z.eqb_neq in MZ.
  rewrite get_meta_rec_upd_same. cbn [m_sizeclass m_set_avail m_set_freed].
  assert (EMb : m_mem (get_meta_rec stZ g3) = Some b) by (rewrite EM; exact Hmem).
  assert (HG : bv_unsigned (Z_to_bv 64 (conc st g3)) = conc stZ g3) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).

  unfold RR.
  eapply (rimplT_evt o _ _ _ (fun ms' => exists a1x : word, ms' = MS (rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st g3)) a1x a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b1e50) fc None mZ (seg_rom bgusegs))).
  { destruct PC as [-> | ->].
    - eapply evt_mono. { eapply (ravz_pre_walk stZ mZ g3 sc MRZ MSZ AV0); [exact HG| exact MIZ]. } cbv beta. intros ms' ->. eexists. reflexivity.
    - apply evt_done. eexists. reflexivity. }
  intros ms0 [a1x ->].
  riprefixT. eapply evt_mono.
  { eapply (ravz_walk stZ mZ g3 b gh1 sc MRZ MSZ AV0 EMb Hgh1 AI1R RFZ MWZ MZ); [| exact SC| exact HG| exact MIZ].
    intros i. pose proof (taf_bnc _ _ TAF i) as B0. pose proof (tr_bounces _ _ _ TR i ltac:(lia)). lia. }
  cbv beta. intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
  set (st4 := upd_meta g3 (fun r : meta => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) stZ) in *.
  set (st5 := decay_bounces (m_sizeclass (get_meta_rec stZ g3)) st4) in *.
  assert (TR4 : ta_rel sc st st4).
  { eapply ta_rel_trans; [exact TR|]. unfold st4. rewrite upd_meta_put. apply ta_rel_put_meta.
    - repeat split; reflexivity.
    - cbn [m_avail m_freed m_set_avail m_set_freed]. intros i Hi Hb. fold f.
      apply orb_prop in Hb. rewrite AV0, Z.bits_0. cbn [orb].
      destruct Hb as [Hb|Hb]; [rewrite Z.land_spec in Hb| rewrite Z.ldiff_spec in Hb]; apply andb_prop in Hb; destruct Hb as [Hb _]; exact Hb.
    - cbn [m_avail m_freed m_set_avail m_set_freed]. fold f. intros _ Hf.
      pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
      pose proof (ldiff_le f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
      pose proof (Z.ldiff_nonneg f act). lia. }
  assert (TR5 : ta_rel sc st st5).
  { eapply ta_rel_trans; [exact TR4|]. unfold st5. apply ta_rel_decay.
    pose proof (taf_bnc _ _ TAF (m_sizeclass (get_meta_rec stZ g3) - 7)). pose proof (tr_bounces _ _ _ TR4 (m_sizeclass (get_meta_rec stZ g3) - 7) ltac:(lia)). lia. }
  assert (FR5 : rw_cells bgusegs m5 (spv + -144) (FRM junk)).
  { eapply rw_cells_transport; [exact FRZ| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
    intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia. }
  assert (ST5 : stk bgusegs m5 lo (spv + -144)).
  { eapply stk_transport_disjoint; [exact STZ| exact MU| exact WM|]. apply disjoint_high; [|lia].
    intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia. }
  eapply (rfin_block st5 g3 (Z.land f act) m5 t0 t1 a2' a3' a4' a5' a6' a7' junk);
    [exact TR5| | exact GM| | | exact MR5| exact MI5| exact FR5| exact ST5|].
  - unfold st5. rewrite active_decay. unfold st4. rewrite active_upd_meta. exact HA.
  - unfold st5. rewrite rec_decay. unfold st4. rewrite get_meta_rec_upd_same. reflexivity.
  - pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)). lia.
  - eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    + intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
    + intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.

Lemma ract_block : forall stY g2 msk mY (t0 t1 a1' a2 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stY -> active stY sc = Some g2 -> gmf st sc g2 ->
  msk = m_freed (get_meta_rec stY g2) ->
  (forall mn, m_next (get_meta_rec stY g2) = Some mn -> gmf st sc mn) ->
  m_next (get_meta_rec stY g2) <> None ->
  rmrep stY mY -> mem_inv bgusegs mY -> rw_cells bgusegs mY (spv + -144) (FRM junk) -> stk bgusegs mY lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mY ->
  rimplT o (ta_act sc K bail stY g2 msk) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g2)) a1' a2 (wz (sxv msk)) (Z_to_bv 64 2) a5 a6 a7) F (Z_to_bv 64 0x2b1e1c) fc None mY (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros TR HA GM HM GN NN MRY MIY FRY STY PEY.
  destruct (gmf_geom st stY sc g2 TR GM) as (MSY & RAY & RFY & MWY & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stY mY g2 MRY MSY) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
  destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
  pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & SCR0 & _).
  assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
  assert (EMb : m_mem (get_meta_rec stY g2) = Some b) by (rewrite EM; exact Hmem).
  assert (MSKR : 0 <= msk < 2^32) by (rewrite HM; exact RFY).
  assert (HG : bv_unsigned (Z_to_bv 64 (conc st g2)) = conc stY g2) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).
  unfold ta_act. rewrite EMb. cbn [default].
  replace (group_active_idx stY b) with (g_active_idx gh1).
  2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  unfold RR.
  destruct (Z.land msk (mask_upto (g_active_idx gh1)) =? 0) eqn:ZR.
  -
    apply Z.eqb_eq in ZR.
    destruct (m_next (get_meta_rec stY g2)) as [mn|] eqn:GNY; [|exfalso; apply NN; reflexivity].
    cbn [optr_eqb]. destruct (aptr_eqb mn g2) eqn:EQ; cbn [negb].
    +
      apply aptr_eqb_eq in EQ. subst mn.
      destruct (Z.eq_dec (m_sizeclass (get_meta_rec st g2)) 0) as [SCZ|SCNZ].
      *
        assert (AIE : g_active_idx gh1 = m_last_idx (get_meta_rec st g2)).
        { destruct AI1 as [E|[_ P]]; [rewrite E; apply SC0; exact SCZ| exfalso; exact (P g2 GMg SCZ)]. }
        assert (MZ : msk = 0).
        { apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
          destruct (Z.testbit msk i) eqn:Ti; [|reflexivity]. exfalso.
          assert (IL : i <= m_last_idx (get_meta_rec st g2)).
          { pose proof (tr_bits _ _ _ TR g2 i Hi) as TB. rewrite <- HM, Ti in TB. rewrite orb_true_r in TB. specialize (TB eq_refl).
            apply orb_prop in TB. destruct TB as [TB|TB]; [exact (gmf_abits _ _ _ GM i Hi TB)| exact (gmf_fbits _ _ _ GM i Hi TB)]. }
          assert (TB2 : Z.testbit (Z.land msk (mask_upto (g_active_idx gh1))) i = true).
          { rewrite Z.land_spec, Ti. unfold mask_upto. replace (2 ^ (g_active_idx gh1 + 1) - 1) with (Z.ones (g_active_idx gh1 + 1)) by (rewrite Z.ones_equiv; lia).
            rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. apply Z.ltb_lt. lia. }
          rewrite ZR, Z.bits_0 in TB2. discriminate. }

        cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai.
        destruct (m_avail (get_meta_rec stY g2) =? 0); unfold guard; [|apply rimplT_undef].
        cbv beta. rewrite <- HM, MZ, Z.land_0_l. cbn [Z.eqb negb]. apply rimplT_undef.
      *
        destruct (m_avail (get_meta_rec stY g2) =? 0) eqn:AV0.
        2:{ cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai, AV0. unfold guard. apply rimplT_undef. }
        apply Z.eqb_eq in AV0.
        assert (SCY : 1 <= m_sizeclass (get_meta_rec stY g2) < 48) by (rewrite ESC; pose proof (gmf_sc48 _ _ _ GM); lia).
        rewrite <- ECONC. riprefixT. eapply evt_mono.
        { eapply (ract_span_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R); [exact ZR| exact GNY| exact MWY| exact SCY| | rewrite GM1; exact GMg| exact AV0| exact MIY].
          intros o' Ho'. rewrite (tr_get_shadow _ _ _ _ TR). apply UNK. exact Ho'. }
        cbv beta. intros ms' (t0' & t1' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
        cbv zeta iota beta.
        match goal with |- rimplT _ (ta_avz _ _ ?st3 _) _ _ _ => set (stG := st3) in * end.
        assert (TRG : ta_rel sc st stG).
        { eapply ta_rel_trans; [exact TR|]. apply ta_rel_set_gai.
          - apply land31_range.
          - intros h g' Hh Hg'. rewrite Hgh1 in Hh. inversion Hh; subst h. rewrite GM1 in Hg'. rewrite GMg in Hg'. inversion Hg'; subst g'. lia. }
        rewrite (tr_conc _ _ _ g2 TR).
        eapply (ravz_block 0x2b1e50 stG g2 m5); [right; reflexivity| exact TRG| | exact GM| exact MR5| exact MI5| | |].
        -- unfold stG. rewrite active_set_gai. exact HA.
        -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
           pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
        -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
           pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
           intros lo' hi' [E|[]]; inversion E; subst; unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
        -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
           cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply (rta_fp_grp st lo spv x b gh Hgh). rewrite <- (tr_conc _ _ _ b TR). lia.
    +
      assert (NE : mn <> g2) by (intros ->; rewrite (proj2 (aptr_eqb_eq g2 g2) eq_refl) in EQ; discriminate).
      pose proof (GN mn eq_refl) as GMn.
      destruct (gmf_geom st stY sc mn TR GMn) as (MSn & _ & _ & _ & _ & _ & _ & _ & ECONCn).
      rewrite <- ECONC. riprefixT. eapply evt_mono.
      { eapply (ract_next_walk stY mY g2 b gh1 sc msk MRY MSY SC EMb Hgh1 AI1R); [exact ZR| exact GNY| exact NE| exact MSn| exact MIY]. }
      cbv beta. intros ms' (a1'' & a2' & a3' & a4' & m5 & -> & MU & WM & MI5 & MR5).
      assert (TRN : ta_rel sc st (set_active sc (Some mn) stY)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
      rewrite ECONCn.
      eapply (ravz_block 0x2b1e44 (set_active sc (Some mn) stY) mn m5); [left; reflexivity| exact TRN| | exact GMn| exact MR5| exact MI5| | |].
      -- rewrite active_set_active, Z.eqb_refl. reflexivity.
      -- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
         intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
      -- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
         intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
      -- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
         cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
  -
    apply Z.eqb_neq in ZR.
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (ract_skip_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R MSKR); [exact ZR| exact MIY]. }
    cbv beta. intros ms' (a1'' & a2' & a3' & a4' & ->). rewrite ECONC.
    eapply (ravz_block 0x2b1e44 stY g2 mY); [left; reflexivity| ..]; eassumption.
Qed.

Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

Lemma rm_block : forall stX g1 mX (P : aptr -> Prop) (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
  ta_rel sc st stX -> active stX sc = Some g1 -> rnclosed stX P -> P g1 ->
  rmrep stX mX -> mem_inv bgusegs mX -> rw_cells bgusegs mX (spv + -144) (FRM junk) -> stk bgusegs mX lo (spv + -144) ->
  rpres_except (rta_fp st lo spv) m mX ->
  rimplT o (ta_m sc K bail stX g1) s Q
    (MS (RR t0 t1 (Z_to_bv 64 (conc st g1)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0x2b1df0) fc None mX (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros TR HA NC P1 MRX MIX FRX STX PEX.
  destruct (NC g1 P1) as (GM & mn & GN1 & Pmn).
  destruct (gmf_geom st stX sc g1 TR GM) as (MSX & RAX & RFX & MWX & EM & ELI & ESC & EFB & ECONC).
  pose proof (rmeta_slot_bounds stX mX g1 MRX MSX) as (Gpos & GC & GI & _ & _).
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
  pose proof (gmf_mw _ _ _ GM) as (LI0 & FB0 & SCR0 & _).
  unfold ta_m, RR.
  set (f := m_freed (get_meta_rec stX g1)).
  destruct ((f =? mask_upto (m_last_idx (get_meta_rec stX g1))) && negb (m_freeable (get_meta_rec stX g1) =? 0)) eqn:FSK.
  -
    pose proof FSK as FSK'. apply andb_prop in FSK'. destruct FSK' as [FE FB]. apply Z.eqb_eq in FE. apply Bool.negb_true_iff in FB. apply Z.eqb_neq in FB.
    rewrite GN1.
    destruct (NC mn Pmn) as (GMn & mn2 & GN2 & Pmn2).
    destruct (gmf_geom st stX sc mn TR GMn) as (MSn & RAn & RFn & MWn & EMn & _ & _ & _ & ECONCn).
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_skip_walk stX mX g1 sc MRX MSX SC RFX MWX); [exact FSK| exact GN1| exact MSn| exact RFn| exact MIX]. }
    cbv beta. intros ms' (a1'' & a2' & m5 & -> & MU & WM & MI5 & MR5).
    assert (TRN : ta_rel sc st (set_active sc (Some mn) stX)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
    rewrite ECONCn.
    eapply (ract_block (set_active sc (Some mn) stX) mn (m_freed (get_meta_rec stX mn)) m5); try eassumption.
    + rewrite active_set_active, Z.eqb_refl. reflexivity.
    + reflexivity.
    + intros q Hq. rewrite rec_set_active in Hq. rewrite GN2 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn2)).
    + rewrite rec_set_active, GN2. discriminate.
    + eapply rw_cells_transport; [exact FRX| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
    + eapply stk_transport_disjoint; [exact STX| exact MU| exact WM|]. apply disjoint_high; [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
    + eapply rpres_except_trans; [exact PEX|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
  -
    rewrite <- ECONC. riprefixT. eapply evt_mono.
    { eapply (rm_act_walk stX mX g1 sc MRX MSX RFX MWX); [exact FSK| exact MIX]. }
    cbv beta. intros ms' (a1'' & a2' & ->). rewrite ECONC.
    eapply (ract_block stX g1 f mX); try eassumption.
    + reflexivity.
    + intros q Hq. rewrite GN1 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn)).
    + rewrite GN1. discriminate.
Qed.

Lemma rta_phase : forall (t0 t1 a0 a2 a3 a4 a5 a6 a7 : word),
  a0 = Z_to_bv 64 sc ->
  rmrep st m -> mem_inv bgusegs m -> stk bgusegs m lo spv ->
  (forall st1 m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
     ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
     rmrep st1 m' -> mem_inv bgusegs m' -> rw_cells bgusegs m' (spv + -144) (FRM junk) -> stk bgusegs m' lo (spv + -144) ->
     rpres_except (rta_fp st lo spv) m m' ->
     rimplT o (K st1 0) s Q (MS (RR t0' t1' a0' a1' a2' a3' a4' a5' a6' a7') F (Z_to_bv 64 0x2b1f08) fc None m' (seg_rom bgusegs))) ->
  rimplT o (try_avail sc st K bail) s Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until a7. intros A0 MR MI ST HK0.
  assert (AMS : forall g, active st sc = Some g -> meta_slot st g) by (intros g Hg; exact (gmf_slot _ _ _ (proj1 (taf_head _ _ TAF g Hg)))).
  riprefixT. eapply evt_mono.
  { eapply (ras_entry_walk st m sc lo MR SC CLO AMS); [exact A0| exact ST| exact LO| exact MI]. }
  cbv beta. intros ms' (a1x & m1 & junk & -> & FR1 & ST1 & MU1 & WM1 & MI1 & MR1).
  assert (PE1 : rpres_except (rta_fp st lo spv) m m1).
  { eapply rpres_except_of_munch_cov; [exact MU1| exact WM1|]. cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_stack. unfold spv; lia. }
  clear MU1 WM1.
  rewrite (try_avail_eq sc K bail st).
  destruct (active st sc) as [g|] eqn:HA.
  2:{
      eapply (HK0 st m1); [| apply ta_rel_refl| exact HA| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
      unfold ta_fail, try_avail. rewrite HA. reflexivity. }
  destruct (taf_head _ _ TAF g HA) as [GM GSC].
  pose proof (gmf_slot _ _ _ GM) as MSg. pose proof (gmf_avail _ _ _ GM) as RAg. pose proof (gmf_freed _ _ _ GM) as RFg.
  pose proof (rmeta_slot_bounds st m1 g MR1 MSg) as (Gpos & GC & GI & _ & _).
  unfold pw. cbn [oconc]. unfold wz.
  destruct (m_avail (get_meta_rec st g) =? 0) eqn:AV; cbn [negb].
  2:{
      apply Z.eqb_neq in AV.
      riprefixT. eapply evt_mono.
      { eapply (rt1_fin_walk st m1 g sc MR1 MSg RAg); [exact AV| exact MI1]. }
      cbv beta. intros ms' ->.
      eapply (rfin_block st g (m_avail (get_meta_rec st g)) m1); [apply ta_rel_refl| exact HA| exact GM| reflexivity| lia| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1]. }
  apply Z.eqb_eq in AV.
  destruct (gmf_links _ _ _ GM) as (nx & pv & GN & GP).
  destruct (taf_next _ _ TAF g nx GM GN) as (GMn & SCn & PRn).
  destruct (taf_prev _ _ TAF g pv GM GP) as (GMp & NXp).
  destruct (m_freed (get_meta_rec st g) =? 0) eqn:FZ.
  -
    apply Z.eqb_eq in FZ.
    riprefixT. eapply evt_mono.
    { eapply (rt1_deq_walk st m1 g sc MR1 MSg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. intros ms' ->.
    destruct (decide (nx = g)) as [->|NEn].
    +
      rewrite (dequeue_self_eq sc g st GN).
      replace (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (@None aptr)
        by (change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc); rewrite active_set_active, Z.eqb_refl; reflexivity).
      cbn [Z.eqb].
      riprefixT. eapply evt_mono.
      { eapply (rdeq_self_walk st m1 g sc MR1 MSg SC); [exact GN| exact MI1]. }
      cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2).
      eapply (HK0 _ m2).
      * unfold ta_fail. rewrite (try_avail_eq sc kS bS st), HA, AV, FZ. cbn [Z.eqb negb].
        rewrite (dequeue_self_eq sc g st GN).
        change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
        rewrite active_set_active, Z.eqb_refl. reflexivity.
      * eapply ta_rel_trans; [apply ta_rel_set_active|]. unfold clr.
        replace (get_meta_rec st g) with (get_meta_rec (set_active sc None st) g) by reflexivity. apply ta_rel_put_links.
      * change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
        rewrite active_set_active, Z.eqb_refl. reflexivity.
      * exact MR2.
      * exact MI2.
      * eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
        intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|exact I]]; intros x Hx; [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]].
    +
      assert (NEp : pv <> g).
      { intros ->. rewrite NXp in GN. inversion GN. subst nx. apply NEn. reflexivity. }
      rewrite (dequeue_other_eq sc g nx pv st GN GP NEn NEp HA). cbv zeta.
      match goal with |- context [active ?stq sc] => set (st1 := stq) in * end.
      assert (HA1 : active st1 sc = Some nx).
      { unfold st1. unfold active, put_meta, set_metas, set_active, upd_ctx. cbn [s_ctx ctx c_active set_active_map]. apply lookup_insert_eq. }
      rewrite HA1.
      pose proof (gmf_slot _ _ _ GMn) as MSn. pose proof (gmf_slot _ _ _ GMp) as MSp.
      riprefixT. eapply evt_mono.
      { eapply (rdeq_other_walk st m1 g sc MR1 MSg SC HA); [exact GN| exact GP| exact NEn| exact NEp| exact MSn| exact MSp| exact MI1]. }
      cbv beta. intros ms' (a1'' & m2 & -> & MU & WM & MI2 & MR2). fold st1 in MR2.
      assert (TR1 : ta_rel sc st st1).
      { unfold st1.
        lazymatch goal with |- ta_rel _ _ (put_meta _ _ ?sC) =>
          lazymatch sC with set_active _ _ ?sB =>
            lazymatch sB with put_meta _ _ ?sA =>
              apply (ta_rel_trans sc st sC); [apply (ta_rel_trans sc st sB); [apply (ta_rel_trans sc st sA); [apply ta_rel_put_next| apply ta_rel_put_prev] | apply ta_rel_set_active] |];
              unfold clr; replace (get_meta_rec st g) with (get_meta_rec sC g); [apply ta_rel_put_links|]
            end end end.
        rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
        rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }

      assert (REC1 : forall q, q <> g -> get_meta_rec st1 q =
                 if aptr_eqb q nx then m_set_prev (Some pv) (if aptr_eqb nx pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st nx)
                 else if aptr_eqb q pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st q).
      { intros q Hq. unfold st1. rewrite (get_meta_rec_put_other _ g) by exact Hq. rewrite rec_set_active.
        rewrite get_meta_rec_put. destruct (aptr_eqb q nx) eqn:E1.
        - apply aptr_eqb_eq in E1. subst q. f_equal. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv) eqn:E2; [apply aptr_eqb_eq in E2; subst; reflexivity| reflexivity].
        - rewrite get_meta_rec_put. reflexivity. }
      eapply (rm_block st1 nx m2 (fun q => gmf st sc q /\ q <> g)); [exact TR1| exact HA1| | split; [exact GMn| exact NEn] | exact MR2| exact MI2| | |].
      * intros q [GMq NEq]. split; [exact GMq|]. rewrite (REC1 q NEq).
        destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP). destruct (taf_next _ _ TAF q qn GMq QN) as (GMqn & _ & PRqn).
        destruct (aptr_eqb q nx) eqn:E1.
        -- apply aptr_eqb_eq in E1. subst q. cbn [m_next m_set_prev].
           destruct (aptr_eqb nx pv) eqn:E2.
           ++ exists nx. cbn. split; [reflexivity|]. split; [exact GMn| exact NEn].
           ++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->.
              rewrite PRqn in GP. inversion GP. subst pv. rewrite (proj2 (aptr_eqb_eq nx nx) eq_refl) in E2. discriminate.
        -- destruct (aptr_eqb q pv) eqn:E2.
           ++ apply aptr_eqb_eq in E2. subst q. cbn. exists nx. split; [reflexivity|]. split; [exact GMn| exact NEn].
           ++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->. rewrite PRqn in GP. inversion GP. subst pv.
              rewrite (proj2 (aptr_eqb_eq q q) eq_refl) in E2. discriminate.
      * eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
        pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
      * eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
        pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
        intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
      * eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
        cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]]; intros x Hx;
          [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]| eapply rta_fp_meta; [exact MSp| lia]| eapply rta_fp_meta; [exact MSn| lia]].
  -
    apply Z.eqb_neq in FZ. rewrite GN.
    riprefixT. eapply evt_mono.
    { eapply (rt1_next_walk st m1 g sc MR1 MSg SC RFg); [exact AV| exact FZ| exact MI1]. }
    cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2). rewrite GN in MR2 |- *. unfold pw. cbn [oconc]. unfold wz.
    eapply (rm_block (set_active sc (Some nx) st) nx m2 (gmf st sc)); [| | | exact GMn| exact MR2| exact MI2| | |].
    + apply ta_rel_set_active.
    + rewrite active_set_active, Z.eqb_refl. reflexivity.
    + intros q GMq. split; [exact GMq|]. rewrite rec_set_active. destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP).
      exists qn. split; [exact QN|]. exact (proj1 (taf_next _ _ TAF q qn GMq QN)).
    + eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
    + eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
      intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia.
    + eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.
End PHASE.
End WithCeiling0.
