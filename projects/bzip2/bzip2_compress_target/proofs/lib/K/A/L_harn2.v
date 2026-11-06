(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs L_hkit2 L_harnw1 L_harnw2 L_harnw5 L_harnw6 L_harnw7 L_harn1.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw1.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw5.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw6.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harnw7.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn1.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section Exits.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis FRE : free_contract RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis MAL0 : malloc0_contract RT.

Variables (Σ0 : rts RT) (PMc : Model -> Prop) (cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) (usp lo : Z) (m0 : mem) (d : Z) (bs : list byte)
          (p0 n0 spa Fr : Z).
Local Notation n := (Z.of_nat (length bs)).
Local Notation live0 := (rt_live RT Σ0).
Local Notation OKT := (hz_ok RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr).
Local Notation HMc := (HM RT Σ0 cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 spa Fr).
Local Notation HSc := (HS RT Σ0 Fr).
Local Notation HQc := (HQ RT LIB Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0).
Hypothesis OK : OKT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LIVE_MAX, B2B_STACK in *; lia.

Ltac to_cps W c Hc Σ MST :=
  lazymatch type of W with evt bsegs _ ?X =>
    let W' := fresh "W'" in
    assert (W' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W);
    clear W; apply (cps_realizes bsegs _ _ _ c (asta_evt' RT AF Σ _ _ _ MST W') Hc); clear W' end.

(* [comment removed for export] *)
Definition hz_st (pc : word) (a0 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (npc : word) (m : mem) : machine_state :=
  MS (mkR pc (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 t3 t4 t5 t6) F npc fc None m (seg_rom bsegs).


Local Notation r33 f := (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(* [comment removed for export] *)
Lemma hz_free_step : forall (Σ : rts RT) (m : mem) new q k r (s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ new -> In (q, k) new -> 0 < k -> In r [0x8150c; 0x81514] ->
  cps bsegs (ASTA RT Σ PMc (eq (hz_st (Z_to_bv 64 r) (Z_to_bv 64 q) s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (Z_to_bv 64 e_free) m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
           ms = hz_st (Z_to_bv 64 r) v s3 s4 s5 s6 s7 s8 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' (ret_pc (Z_to_bv 64 r)) m'
           /\ HMc Σ' m' /\ rt_pres (rt_live RT Σ') [(Fr, 0%nat)] spa m m') c
       /\ rt_live RT Σ' = live_remove q (rt_live RT Σ) /\ rt_frames RT Σ' = [(Fr, 0%nat)] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ0
       /\ rt_credit RT Σ' = rt_credit RT Σ).
Proof using OK AF FRE.
  intros Σ m new q k r s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S Hin K0 Hr T c Hc Hk. unfold hz_st in Hc.
  pose proof H as (ART0 & MI0 & _). pose proof S as (LV & FRS & SP0).
  refine (cps_realizes bsegs _ _ T c _ Hc _).
  { eapply (r33 (FRE Σ PMc) m q k lo); try reflexivity.
    - exact (hz_FDO OK).
    - exact (hz_MST OK).
    - rewrite LV. apply in_or_app. left. exact Hin.
    - exact (hz_TP OK).
    - exact ART0.
    - exact MI0.
    - exact (hm_call_ok OK Σ m new H S).
    - apply (hm_unwind OK Σ m r H). destruct Hr as [<-|[<-|[]]]; cbn; tauto. }
  intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PR1) & Hc1'). clear Hc1.
  destruct RS1 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & ->).
  rewrite (hz_EU OK) in ST1, PR1. rewrite FRS in PR1, FRS1.
  apply Hk. exists Σ1. split; [| split; [exact LV1| split; [exact FRS1| split; [rewrite SP1; exact SP0| exact CR1]]]].
  eapply ASTA_conseq; [exact Hc1'|]. intros ms <-. exists m1, v, w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F1, fc1.
  split; [reflexivity|]. split; [| exact PR1].
  apply (hm_step OK Σ Σ1 m m1 H ART1 MI1 ST1). apply (core_of_pres OK _ m m1 PR1).
  intros e He. rewrite LV1. apply live_remove_keep; [rewrite LV; apply in_or_app; right; exact He|].
  exact (hs_fresh AF OK Σ m new q k ART0 S Hin K0 e He).
Qed.

(* [comment removed for export] *)
Lemma hz_malloc_step : forall (Σ : rts RT) (m : mem) new sz r (s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ new -> In r [0x81434; 0x814c8] -> 0 <= sz <= 0x8000000 -> (length new < 8)%nat -> mcost sz <= rt_credit RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (hz_st (Z_to_bv 64 r) (Z_to_bv 64 sz) s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (Z_to_bv 64 e_malloc) m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
           ms = hz_st (Z_to_bv 64 r) (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' (ret_pc (Z_to_bv 64 r)) m'
           /\ HMc Σ' m' /\ rt_pres (rt_live RT Σ) [(Fr, 0%nat)] spa m m' /\ wr_at bsegs m' p (Z.max sz 1)) c
       /\ HSc Σ' ((p, Z.max sz 1) :: new) /\ rt_credit RT Σ' = rt_credit RT Σ - mcost sz /\ 0 < p /\ p + Z.max sz 1 < USTACK_TOP).
Proof using OK AF MAL MAL0.
  intros Σ m new sz r s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S Hr SZ NEW CR T c Hc Hk. unfold hz_st in Hc.
  pose proof H as (ART0 & MI0 & _). pose proof S as (LV & FRS & SP0).
  assert (LVB : Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX).
  { rewrite LV, length_app. pose proof (hz_LVB OK). unfold FUZZ_LIVE, LIVE_MAX in *. lia. }
  assert (UW : unwind_ch m (Z_to_bv 64 r) (Z_to_bv 64 usp) (Z_to_bv 64 spa)).
  { apply (hm_unwind OK Σ m r H). destruct Hr as [<-|[<-|[]]]; cbn; tauto. }
  assert (POST : forall cf1, malloc_post RT Σ PMc (Z_to_bv 64 r) (Z_to_bv 64 spa) gp tp (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8
                                (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 (Z.max sz 1) lo m cf1 -> mcost (Z.max sz 1) = mcost sz -> realizes bsegs cf1 T).
  { intros cf1 (Σ1 & p & Hc1 & LV1 & FRS1 & SP1 & CR1 & P0 & _ & PT) MC.
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & _ & ST1) & PR1 & WR1 & _) & Hc1'). clear Hc1.
    destruct RS1 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & ->).
    rewrite (hz_EU OK) in ST1, PR1. rewrite FRS in PR1, FRS1.
    apply Hk. exists Σ1, p. split; [| split; [split; [rewrite LV1, LV; reflexivity| split; [exact FRS1| rewrite SP1; exact SP0]]| split; [rewrite CR1, MC; reflexivity| split; [exact P0| exact PT]]]].
    eapply ASTA_conseq; [exact Hc1'|]. intros ms <-. exists m1, w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F1, fc1.
    split; [reflexivity|]. split; [| split; [exact PR1| exact WR1]].
    apply (hm_step OK Σ Σ1 m m1 H ART1 MI1 ST1). apply (core_of_pres OK _ m m1 PR1).
    intros e He. rewrite LV. apply in_or_app. right. exact He. }
  destruct (Z.eq_dec sz 0) as [->|NZ].
  - refine (cps_realizes bsegs _ _ T c _ Hc (fun cf1 Hcf1 => POST cf1 Hcf1 eq_refl)).
    eapply (r33 (MAL0 Σ PMc) m lo); try reflexivity.
    + exact (hz_FDO OK).
    + exact (hz_MST OK).
    + exact (hz_TP OK).
    + exact LVB.
    + exact ART0.
    + exact MI0.
    + exact (hm_call_ok OK Σ m new H S).
    + exact UW.
  - replace (Z.max sz 1) with sz in * by lia.
    refine (cps_realizes bsegs _ _ T c _ Hc (fun cf1 Hcf1 => POST cf1 Hcf1 eq_refl)).
    eapply (r33 (MAL Σ PMc) m sz lo); try reflexivity.
    + exact (hz_FDO OK).
    + exact (hz_MST OK).
    + lia.
    + exact (hz_TP OK).
    + exact LVB.
    + exact CR.
    + exact ART0.
    + exact MI0.
    + exact (hm_call_ok OK Σ m new H S).
    + exact UW.
Qed.

(* [comment removed for export] *)
Lemma hz_epi_cps : forall (Σ : rts RT) (m : mem) (a0 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [] -> rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (hz_st (Z_to_bv 64 0x81514) a0 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (ret_pc (Z_to_bv 64 0x81514)) m))) HQc.
Proof using OK AF LIB_loc.
  intros Σ m a0 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S CRX T c Hc Hk. unfold hz_st in Hc.
  pose proof H as (ART0 & MI0 & ST0 & PR0 & (z0 & j8 & FR0) & GAP0 & (h0 & HDR0) & SH0). pose proof S as (LV & FRS & SP0).
  pose proof (hz_geo OK) as G. pose proof (hz_MST OK) as MST.
  pose proof (hz_F64 OK) as F64. pose proof (hz_FSEG OK) as FSEG. unfold SEGTOP_A in FSEG.
  pose proof (hz_FPL OK) as FPL. pose proof (hz_FLO OK) as FLO.
  (* [comment removed for export] *)
  pose proof (hz_wJ1 usp spa Fr h0 a0 s3 s4 s5 s6 s7 s8 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 c11 t3 t4 t5 t6 F fc m ltac:(lia) F64 FPL ltac:(lia) HDR0 SH0 MI0) as W.
  to_cps W c Hc Σ MST. intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & a0' & -> & MU1 & WM1 & MI1 & SH1) & Hc1'). clear Hc1.
  assert (ART1 : ART RT Σ m1).
  { apply (hs_art_munch AF OK Σ [] _ m m1 ART0 S MU1 WM1). intros x H1 H2 H3. cbn [outside]. lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ m1 Fr 0 [] ART1 FRS) as (Σ2 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (Fr + 64 - 8) with (Fr + 56) in FW by lia. rewrite SP0 in FLW.
  pose proof (hz_wJ2 usp spa Fr fl a0' s3 s4 s5 s6 s7 s8 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 c11 t3 t4 t5 t6 F fc m1 ltac:(lia) ltac:(lia) FL0
                ltac:(destruct OK; ul) FW FLC MI1) as W.
  to_cps W cf1 Hc1' Σ MST. intros cf2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & (m2 & -> & MU2 & WM2 & MI2 & FLC2) & Hc2'). clear Hc2.
  destruct (REL m2 MU2 WM2 FLC2) as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2).
  (* [comment removed for export] *)
  assert (AG : agree_on (fun x => spa <= x < usp \/ ACL RT Σ0 usp x) m m2).
  { apply (agree_trans _ m m1 m2).
    - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. pose proof (shad_F_lo OK) as SL.
      destruct Hx as [Hx|Hx]; [lia|]. destruct (hz_FAP OK x Hx) as (A1 & A2).
      rewrite (shad_F64 OK) in A2. lia.
    - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [outside]. split; [| exact I]. intros Hfl. assert (E : x = fl) by lia. subst x.
      destruct Hx as [Hx|Hx]; [destruct OK; ul|]. apply NAC. rewrite LV, FRS. cbn [app].
      destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; [destruct OK; ul| right; left; exact Hx| right; right; left; exact Hx|
        destruct Hx as (f & k & [] & _)| destruct Hx as (f & k & [] & _)]. }
  assert (ST2 : stk bsegs m2 lo (usp + -128)).
  { assert (ST2' : stk bsegs m2 lo spa) by exact (stk_wmono' _ _ _ _ ST0 (wmono_trans _ _ _ _ WM1 WM2)).
    destruct GAP0 as [E|(E & jg & GP)]; [rewrite <- E; exact ST2'|]. rewrite E in ST2'.
    apply (stk_merge bsegs _ _ (usp + -144) _ ST2'); [| lia].
    apply (rw_cells_stk' m2 _ [CB 16 jg]); [cbn; lia|]. apply (rw_cells_agree_nw bsegs m m2 _ _ GP). apply (agree_sub _ _ _ _ AG).
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (FR2 : rw_cells bsegs m2 (usp + -128) (hz_frame (C8 z0) j8 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)).
  { apply (rw_cells_agree_nw bsegs m m2 _ _ FR0). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size hz_frame csize Nat.add] in Hx. left. lia. }
  pose proof (hz_wI2 usp lo z0 j8 (Z_to_bv 64 0x81514) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 spa) (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 t3 t4 t5 t6 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m2
                ST2 ltac:(lia) ltac:(lia) FR2 MI2) as W.
  to_cps W cf2 Hc2' Σ MST. intros cf3 Hc3. apply Hk.
  exists Σ2. split; [| split; [rewrite LV2, LV; reflexivity| split; [exact FRS2| split; [rewrite SP2; exact SP0| rewrite CR2; exact CRX]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ Σ2 _ _ cf3 Hc3 AL2 AM2)|]. intros ms (RS & ST3). exists m2. split; [exact RS|].
  split; [split; [exact ART2| split; [exact MI2| exact ST3]]|].
  assert (PR2 : agree_on (ACL RT Σ0 usp) m0 m2).
  { apply (agree_trans _ m0 m m2 PR0). apply (agree_sub _ _ _ _ AG). intros x Hx. right. exact Hx. }
  split; [intros a Ha _; exact (PR2 a Ha)|].
  apply (LIB_loc m0 m2 (hz_LIB0 OK)). intros a Ha. apply PR2. right; left. exact (proj1 (LIB_img _ Ha)).
Qed.


(* [comment removed for export] *)
Lemma hz_tail_cps : forall (Σ : rts RT) (m : mem) q k (s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [(q, k)] -> 0 < k -> rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (hz_st (Z_to_bv 64 0x81514) (Z_to_bv 64 q) s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (Z_to_bv 64 e_free) m))) HQc.
Proof using OK AF LIB_loc FRE.
  intros Σ m q k s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S K0 CRX T c Hc Hk.
  refine (cps_realizes bsegs _ _ T c (hz_free_step Σ m [(q, k)] q k 0x81514 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S
                                        (or_introl eq_refl) K0 ltac:(cbn; tauto)) Hc _).
  intros cf1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & v & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & -> & H1 & _) & Hc1').
  clear Hc1.
  assert (S1 : HSc Σ1 []).
  { split; [| split; [exact FRS1| exact SP1]]. rewrite LV1. pose proof S as (LV & _). rewrite LV. cbn [app]. apply live_remove_head.
    exact (hs_fresh AF OK Σ m [(q, k)] q k (proj1 H) S (or_introl eq_refl) K0). }
  exact (hz_epi_cps Σ1 m1 v s3 s4 s5 s6 s7 s8 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F1 fc1 H1 S1 ltac:(rewrite CR1; exact CRX) T cf1 Hc1' Hk).
Qed.

(* [comment removed for export] *)
Lemma hz_free2_cps : forall (Σ : rts RT) (m : mem) zb zc ob oc (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [(ob, oc); (zb, zc)] -> 0 < oc -> 0 < zc -> rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (hz_call 0x8150c e_free usp spa Fr d n zb (Z_to_bv 64 zb) a1 a2 gp tp t0 t1 t2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) c11 t3 t4 t5 t6 F fc m))) HQc.
Proof using OK AF LIB_loc FRE.
  intros Σ m zb zc ob oc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S OC ZC CRX T c Hc Hk.
  pose proof H as (ART0 & _). pose proof S as (LV & FRS & SP0).
  refine (cps_realizes bsegs _ _ T c (hz_free_step Σ m [(ob, oc); (zb, zc)] zb zc 0x8150c (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb)
                                        (Z_to_bv 64 ob) (Z_to_bv 64 (Fr + 48)) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S
                                        (or_intror (or_introl eq_refl)) ZC ltac:(cbn; tauto)) Hc _).
  intros cf1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & v & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & -> & H1 & _) & Hc1').
  clear Hc1.
  assert (NE : ob <> zb).
  { pose proof (af_live_disj RT AF Σ m zb zc ob oc [(ob, oc)] live0 ART0 LV ltac:(left; reflexivity)) as D. lia. }
  assert (S1 : HSc Σ1 [(ob, oc)]).
  { split; [| split; [exact FRS1| exact SP1]]. rewrite LV1, LV. cbn [app].
    rewrite (live_remove_cons_keep zb (ob, oc)) by (cbn [fst]; exact NE). f_equal. apply live_remove_head.
    exact (hs_fresh AF OK Σ m _ zb zc ART0 S (or_intror (or_introl eq_refl)) ZC). }
  pose proof (hz_wH usp spa Fr d n zb v (Z_to_bv 64 ob) gp tp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 c11 w3 w4 w5 w6 F1 fc1 m1) as W.
  to_cps W cf1 Hc1' Σ1 (hz_MST OK). intros cf2 Hc2.
  destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & <- & Hc2'). clear Hc2.
  exact (hz_tail_cps Σ1 m1 ob oc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 H1 S1 OC ltac:(rewrite CR1; exact CRX) T cf2 Hc2' Hk).
Qed.

End Exits.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs L_hkit2
  L_harnw1 L_harnw2 L_harnw5 L_harnw6 L_harnw7 L_harn1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Section Exits.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis FRE : free_contract RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis MAL0 : malloc0_contract RT.

Variables (Σ0 : rts RT) (PMc : Model -> Prop) (cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word) (usp lo : Z) (m0 : mem) (d : Z) (bs : list byte)
          (p0 n0 spa Fr : Z).
Local Notation n := (Z.of_nat (length bs)).
Local Notation live0 := (rt_live RT Σ0).
Local Notation OKT := (hz_ok RT LIB Σ0 PMc cra tp c0 usp lo m0 d bs p0 n0 spa Fr).
Local Notation HMc := (HM RT Σ0 cra c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 usp lo m0 spa Fr).
Local Notation HSc := (HS RT Σ0 Fr).
Local Notation HQc := (HQ RT LIB Σ0 PMc cra gp tp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 usp lo m0).
Hypothesis OK : OKT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, LIVE_MAX, B2B_STACK in *; lia.

Ltac to_cps W c Hc Σ MST :=
  lazymatch type of W with evt asegs _ ?X =>
    let W' := fresh "W'" in
    assert (W' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W);
    clear W; apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ _ _ _ MST W') Hc); clear W' end.

(* [comment removed for export] *)
Definition hz_st (pc : word) (a0 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (npc : word) (m : mem) : machine_state :=
  MS (mkR pc (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 t3 t4 t5 t6) F npc fc None m (seg_rom asegs).


Local Notation r33 f := (f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(* [comment removed for export] *)
Lemma hz_free_step : forall (Σ : rts RT) (m : mem) new q k r (s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ new -> In (q, k) new -> 0 < k -> In r [0x81ac0; 0x81ac8] ->
  cps asegs (ASTA RT Σ PMc (eq (hz_st (Z_to_bv 64 r) (Z_to_bv 64 q) s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (Z_to_bv 64 e_free) m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
           ms = hz_st (Z_to_bv 64 r) v s3 s4 s5 s6 s7 s8 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' (ret_pc (Z_to_bv 64 r)) m'
           /\ HMc Σ' m' /\ rt_pres (rt_live RT Σ') [(Fr, 0%nat)] spa m m') c
       /\ rt_live RT Σ' = live_remove q (rt_live RT Σ) /\ rt_frames RT Σ' = [(Fr, 0%nat)] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ0
       /\ rt_credit RT Σ' = rt_credit RT Σ).
Proof using OK AF FRE.
  intros Σ m new q k r s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S Hin K0 Hr T c Hc Hk. unfold hz_st in Hc.
  pose proof H as (ART0 & MI0 & _). pose proof S as (LV & FRS & SP0).
  refine (cps_realizes asegs _ _ T c _ Hc _).
  { eapply (r33 (FRE Σ PMc) m q k lo); try reflexivity.
    - exact (hz_FDO OK).
    - exact (hz_MST OK).
    - rewrite LV. apply in_or_app. left. exact Hin.
    - exact (hz_TP OK).
    - exact ART0.
    - exact MI0.
    - exact (hm_call_ok OK Σ m new H S).
    - apply (hm_unwind OK Σ m r H). destruct Hr as [<-|[<-|[]]]; cbn; tauto. }
  intros cf1 (Σ1 & v & Hc1 & LV1 & FRS1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & ST1) & PR1) & Hc1'). clear Hc1.
  destruct RS1 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & ->).
  rewrite (hz_EU OK) in ST1, PR1. rewrite FRS in PR1, FRS1.
  apply Hk. exists Σ1. split; [| split; [exact LV1| split; [exact FRS1| split; [rewrite SP1; exact SP0| exact CR1]]]].
  eapply ASTA_conseq; [exact Hc1'|]. intros ms <-. exists m1, v, w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F1, fc1.
  split; [reflexivity|]. split; [| exact PR1].
  apply (hm_step OK Σ Σ1 m m1 H ART1 MI1 ST1). apply (core_of_pres OK _ m m1 PR1).
  intros e He. rewrite LV1. apply live_remove_keep; [rewrite LV; apply in_or_app; right; exact He|].
  exact (hs_fresh AF OK Σ m new q k ART0 S Hin K0 e He).
Qed.

(* [comment removed for export] *)
Lemma hz_malloc_step : forall (Σ : rts RT) (m : mem) new sz r (s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ new -> In r [0x819e8; 0x81a7c] -> 0 <= sz <= 0x8000000 -> (length new < 8)%nat -> mcost sz <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (hz_st (Z_to_bv 64 r) (Z_to_bv 64 sz) s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (Z_to_bv 64 e_malloc) m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
           ms = hz_st (Z_to_bv 64 r) (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' (ret_pc (Z_to_bv 64 r)) m'
           /\ HMc Σ' m' /\ rt_pres (rt_live RT Σ) [(Fr, 0%nat)] spa m m' /\ wr_at asegs m' p (Z.max sz 1)) c
       /\ HSc Σ' ((p, Z.max sz 1) :: new) /\ rt_credit RT Σ' = rt_credit RT Σ - mcost sz /\ 0 < p /\ p + Z.max sz 1 < USTACK_TOP).
Proof using OK AF MAL MAL0.
  intros Σ m new sz r s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S Hr SZ NEW CR T c Hc Hk. unfold hz_st in Hc.
  pose proof H as (ART0 & MI0 & _). pose proof S as (LV & FRS & SP0).
  assert (LVB : Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX).
  { rewrite LV, length_app. pose proof (hz_LVB OK). unfold FUZZ_LIVE, LIVE_MAX in *. lia. }
  assert (UW : unwind_ch m (Z_to_bv 64 r) (Z_to_bv 64 usp) (Z_to_bv 64 spa)).
  { apply (hm_unwind OK Σ m r H). destruct Hr as [<-|[<-|[]]]; cbn; tauto. }
  assert (POST : forall cf1, malloc_post RT Σ PMc (Z_to_bv 64 r) (Z_to_bv 64 spa) gp tp (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8
                                (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 (Z.max sz 1) lo m cf1 -> mcost (Z.max sz 1) = mcost sz -> realizes asegs cf1 T).
  { intros cf1 (Σ1 & p & Hc1 & LV1 & FRS1 & SP1 & CR1 & P0 & _ & PT) MC.
    destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & RS1 & (ART1 & MI1 & _ & ST1) & PR1 & WR1 & _) & Hc1'). clear Hc1.
    destruct RS1 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & ->).
    rewrite (hz_EU OK) in ST1, PR1. rewrite FRS in PR1, FRS1.
    apply Hk. exists Σ1, p. split; [| split; [split; [rewrite LV1, LV; reflexivity| split; [exact FRS1| rewrite SP1; exact SP0]]| split; [rewrite CR1, MC; reflexivity| split; [exact P0| exact PT]]]].
    eapply ASTA_conseq; [exact Hc1'|]. intros ms <-. exists m1, w0, w1, w2, e1, e2, e3, e4, e5, e6, e7, w3, w4, w5, w6, F1, fc1.
    split; [reflexivity|]. split; [| split; [exact PR1| exact WR1]].
    apply (hm_step OK Σ Σ1 m m1 H ART1 MI1 ST1). apply (core_of_pres OK _ m m1 PR1).
    intros e He. rewrite LV. apply in_or_app. right. exact He. }
  destruct (Z.eq_dec sz 0) as [->|NZ].
  - refine (cps_realizes asegs _ _ T c _ Hc (fun cf1 Hcf1 => POST cf1 Hcf1 eq_refl)).
    eapply (r33 (MAL0 Σ PMc) m lo); try reflexivity.
    + exact (hz_FDO OK).
    + exact (hz_MST OK).
    + exact (hz_TP OK).
    + exact LVB.
    + exact ART0.
    + exact MI0.
    + exact (hm_call_ok OK Σ m new H S).
    + exact UW.
  - replace (Z.max sz 1) with sz in * by lia.
    refine (cps_realizes asegs _ _ T c _ Hc (fun cf1 Hcf1 => POST cf1 Hcf1 eq_refl)).
    eapply (r33 (MAL Σ PMc) m sz lo); try reflexivity.
    + exact (hz_FDO OK).
    + exact (hz_MST OK).
    + lia.
    + exact (hz_TP OK).
    + exact LVB.
    + exact CR.
    + exact ART0.
    + exact MI0.
    + exact (hm_call_ok OK Σ m new H S).
    + exact UW.
Qed.

(* [comment removed for export] *)
Lemma hz_epi_cps : forall (Σ : rts RT) (m : mem) (a0 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [] -> rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (hz_st (Z_to_bv 64 0x81ac8) a0 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (ret_pc (Z_to_bv 64 0x81ac8)) m))) HQc.
Proof using OK AF LIB_loc.
  intros Σ m a0 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S CRX T c Hc Hk. unfold hz_st in Hc.
  pose proof H as (ART0 & MI0 & ST0 & PR0 & (z0 & j8 & FR0) & GAP0 & (h0 & HDR0) & SH0). pose proof S as (LV & FRS & SP0).
  pose proof (hz_geo OK) as G. pose proof (hz_MST OK) as MST.
  pose proof (hz_F64 OK) as F64. pose proof (hz_FSEG OK) as FSEG. unfold SEGTOP_A in FSEG.
  pose proof (hz_FPL OK) as FPL. pose proof (hz_FLO OK) as FLO.
  (* [comment removed for export] *)
  pose proof (hz_wJ1 usp spa Fr h0 a0 s3 s4 s5 s6 s7 s8 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 c11 t3 t4 t5 t6 F fc m ltac:(lia) F64 FPL ltac:(lia) HDR0 SH0 MI0) as W.
  to_cps W c Hc Σ MST. intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & a0' & -> & MU1 & WM1 & MI1 & SH1) & Hc1'). clear Hc1.
  assert (ART1 : ART RT Σ m1).
  { apply (hs_art_munch AF OK Σ [] _ m m1 ART0 S MU1 WM1). intros x H1 H2 H3. cbn [outside]. lia. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ m1 Fr 0 [] ART1 FRS) as (Σ2 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (Fr + 64 - 8) with (Fr + 56) in FW by lia. rewrite SP0 in FLW.
  pose proof (hz_wJ2 usp spa Fr fl a0' s3 s4 s5 s6 s7 s8 gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 c11 t3 t4 t5 t6 F fc m1 ltac:(lia) ltac:(lia) FL0
                ltac:(destruct OK; ul) FW FLC MI1) as W.
  to_cps W cf1 Hc1' Σ MST. intros cf2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & (m2 & -> & MU2 & WM2 & MI2 & FLC2) & Hc2'). clear Hc2.
  destruct (REL m2 MU2 WM2 FLC2) as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2).
  (* [comment removed for export] *)
  assert (AG : agree_on (fun x => spa <= x < usp \/ ACL RT Σ0 usp x) m m2).
  { apply (agree_trans _ m m1 m2).
    - apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. pose proof (shad_F_lo OK) as SL.
      destruct Hx as [Hx|Hx]; [lia|]. destruct (hz_FAP OK x Hx) as (A1 & A2).
      rewrite (shad_F64 OK) in A2. lia.
    - apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [outside]. split; [| exact I]. intros Hfl. assert (E : x = fl) by lia. subst x.
      destruct Hx as [Hx|Hx]; [destruct OK; ul|]. apply NAC. rewrite LV, FRS. cbn [app].
      destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; [destruct OK; ul| right; left; exact Hx| right; right; left; exact Hx|
        destruct Hx as (f & k & [] & _)| destruct Hx as (f & k & [] & _)]. }
  assert (ST2 : stk asegs m2 lo (usp + -128)).
  { assert (ST2' : stk asegs m2 lo spa) by exact (stk_wmono' _ _ _ _ ST0 (wmono_trans _ _ _ _ WM1 WM2)).
    destruct GAP0 as [E|(E & jg & GP)]; [rewrite <- E; exact ST2'|]. rewrite E in ST2'.
    apply (stk_merge asegs _ _ (usp + -144) _ ST2'); [| lia].
    apply (rw_cells_stk' m2 _ [CB 16 jg]); [cbn; lia|]. apply (rw_cells_agree_nw asegs m m2 _ _ GP). apply (agree_sub _ _ _ _ AG).
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia. }
  assert (FR2 : rw_cells asegs m2 (usp + -128) (hz_frame (C8 z0) j8 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)).
  { apply (rw_cells_agree_nw asegs m m2 _ _ FR0). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size hz_frame csize Nat.add] in Hx. left. lia. }
  pose proof (hz_wI2 usp lo z0 j8 (Z_to_bv 64 0x81ac8) (Z_to_bv 64 spa) gp tp t0 t1 t2 (Z_to_bv 64 spa) (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 Fr) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (shad Fr)) (Z_to_bv 64 Fr) c11 t3 t4 t5 t6 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra F fc m2
                ST2 ltac:(lia) ltac:(lia) FR2 MI2) as W.
  to_cps W cf2 Hc2' Σ MST. intros cf3 Hc3. apply Hk.
  exists Σ2. split; [| split; [rewrite LV2, LV; reflexivity| split; [exact FRS2| split; [rewrite SP2; exact SP0| rewrite CR2; exact CRX]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ Σ2 _ _ cf3 Hc3 AL2 AM2)|]. intros ms (RS & ST3). exists m2. split; [exact RS|].
  split; [split; [exact ART2| split; [exact MI2| exact ST3]]|].
  assert (PR2 : agree_on (ACL RT Σ0 usp) m0 m2).
  { apply (agree_trans _ m0 m m2 PR0). apply (agree_sub _ _ _ _ AG). intros x Hx. right. exact Hx. }
  split; [intros a Ha _; exact (PR2 a Ha)|].
  apply (LIB_loc m0 m2 (hz_LIB0 OK)). intros a Ha. apply PR2. right; left. exact (proj1 (LIB_img _ Ha)).
Qed.


(* [comment removed for export] *)
Lemma hz_tail_cps : forall (Σ : rts RT) (m : mem) q k (s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [(q, k)] -> 0 < k -> rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (hz_st (Z_to_bv 64 0x81ac8) (Z_to_bv 64 q) s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc (Z_to_bv 64 e_free) m))) HQc.
Proof using OK AF LIB_loc FRE.
  intros Σ m q k s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S K0 CRX T c Hc Hk.
  refine (cps_realizes asegs _ _ T c (hz_free_step Σ m [(q, k)] q k 0x81ac8 s3 s4 s5 s6 s7 s8 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S
                                        (or_introl eq_refl) K0 ltac:(cbn; tauto)) Hc _).
  intros cf1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & v & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & -> & H1 & _) & Hc1').
  clear Hc1.
  assert (S1 : HSc Σ1 []).
  { split; [| split; [exact FRS1| exact SP1]]. rewrite LV1. pose proof S as (LV & _). rewrite LV. cbn [app]. apply live_remove_head.
    exact (hs_fresh AF OK Σ m [(q, k)] q k (proj1 H) S (or_introl eq_refl) K0). }
  exact (hz_epi_cps Σ1 m1 v s3 s4 s5 s6 s7 s8 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F1 fc1 H1 S1 ltac:(rewrite CR1; exact CRX) T cf1 Hc1' Hk).
Qed.

(* [comment removed for export] *)
Lemma hz_free2_cps : forall (Σ : rts RT) (m : mem) zb zc ob oc (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
  HMc Σ m -> HSc Σ [(ob, oc); (zb, zc)] -> 0 < oc -> 0 < zc -> rt_credit RT Σ0 - FUZZ_COST <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (hz_call 0x81ac0 e_free usp spa Fr d n zb (Z_to_bv 64 zb) a1 a2 gp tp t0 t1 t2 a3 a4 a5 a6 a7 (Z_to_bv 64 ob) c11 t3 t4 t5 t6 F fc m))) HQc.
Proof using OK AF LIB_loc FRE.
  intros Σ m zb zc ob oc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S OC ZC CRX T c Hc Hk.
  pose proof H as (ART0 & _). pose proof S as (LV & FRS & SP0).
  refine (cps_realizes asegs _ _ T c (hz_free_step Σ m [(ob, oc); (zb, zc)] zb zc 0x81ac0 (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 zb)
                                        (Z_to_bv 64 ob) (Z_to_bv 64 (Fr + 48)) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc H S
                                        (or_intror (or_introl eq_refl)) ZC ltac:(cbn; tauto)) Hc _).
  intros cf1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1).
  destruct (ASTA_unpack RT Σ1 _ _ cf1 Hc1) as (ms1 & (m1 & v & w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F1 & fc1 & -> & H1 & _) & Hc1').
  clear Hc1.
  assert (NE : ob <> zb).
  { pose proof (af_live_disj RT AF Σ m zb zc ob oc [(ob, oc)] live0 ART0 LV ltac:(left; reflexivity)) as D. lia. }
  assert (S1 : HSc Σ1 [(ob, oc)]).
  { split; [| split; [exact FRS1| exact SP1]]. rewrite LV1, LV. cbn [app].
    rewrite (live_remove_cons_keep zb (ob, oc)) by (cbn [fst]; exact NE). f_equal. apply live_remove_head.
    exact (hs_fresh AF OK Σ m _ zb zc ART0 S (or_intror (or_introl eq_refl)) ZC). }
  pose proof (hz_wH usp spa Fr d n zb v (Z_to_bv 64 ob) gp tp w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 c11 w3 w4 w5 w6 F1 fc1 m1) as W.
  to_cps W cf1 Hc1' Σ1 (hz_MST OK). intros cf2 Hc2.
  destruct (ASTA_unpack RT Σ1 _ _ cf2 Hc2) as (ms2 & <- & Hc2'). clear Hc2.
  exact (hz_tail_cps Σ1 m1 ob oc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 H1 S1 OC ltac:(rewrite CR1; exact CRX) T cf2 Hc2' Hk).
Qed.

End Exits.
