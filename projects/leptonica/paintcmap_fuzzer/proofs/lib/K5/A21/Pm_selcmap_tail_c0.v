(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.A21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_gaps_iface Pm_iface Pm_kit Pm_walkkit Pm_objkit Pm_selkit Pm_selloop_defs Pm_selcmap_defs.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section SELC_TAIL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis BGG : boxGetGeometry_cps RT.
Hypothesis SELROWS : sel_rows_stmt.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (pix b : Z) (v : pixv) (cv : cmapv) (fr : Z).


Theorem selc_cut_ok_0 :
  selc_ctx RT Σ PMc usp lo m pix b v ->
  selc_cut_stmt_0 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr.
Proof using AF GP BGG SELROWS.
  intros (FDO & MST & ART0 & LOW & LOR & STa & SPT & SPA & SPB & LVP & CNZ & DNZ & D4 & BNE).
  unfold selc_cut_stmt_0.
  intros Sc mc cvx idx j0 j1 j2 f0 f1 js r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r21 r22 r23 r24 r27 r28 r29 r30 r31 F' fc'
    ARTc MIc WMc STc FR FRMx FRMI FRMR FSH LH SSP AGF FRS LVE ESP0 ECR POBJ EARR EDEP ENAL BOBJ IDXR.
  set (PFW := selc_PFW RT Σ usp v cv) in *.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  assert (USP : 0 <= usp < 2^64) by (clear - STa LOR SPT; lia).
  assert (PFS : forall a, PFW a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  unfold entry_st, selc_fshadow in *.
  (* [comment removed for export] *)
  pose proof (af_frames_range RT AF Sc mc fr 2%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _).
  pose proof (af_frames_align RT AF Sc mc fr 2%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG).
  pose proof (af_frames_hi RT AF Sc mc fr 2%nat ARTc ltac:(rewrite FRS; left; reflexivity)) as FRSH.
  change (fs_size 2) with 256 in FRHI, FRSH. rewrite ESP0 in FRHI. unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG.
  assert (NFA : forall a, PFW a -> (a < fr \/ fr + 256 <= a) /\ (a < fr / 8 + 2147450880 \/ fr / 8 + 32 + 2147450880 <= a)).
  { intros a [Ha _]. pose proof (new_frame_apart RT AF Sc mc fr 2%nat (rt_frames RT Σ) (rt_live RT Σ) usp a ARTc FRS
      ltac:(intros e He; rewrite LVE; exact He) ltac:(rewrite ESP0; lia) ltac:(rewrite ESP0; unfold STACK_WIN; lia) Ha) as NF.
    change (fs_size 2) with 256 in NF. unfold shad, SHB in NF. clear - NF FR64. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & HOK & DD & CC).
  destruct DD as [DZ|((IND & D0 & D16 & _) & DNP)]; [contradiction|].
  destruct CC as [CZ|(COBJ & CNP & ANP & CND & AND)]; [contradiction|].
  pose proof COBJ as (_ & (CIN & CM0 & _) & (AIN & _) & _ & _).
  pose proof BOBJ as (BXC & (INB & BX0 & BX16 & _)).
  pose proof HOK as (_ & WR & HR & EWPL & RSZ).
  unfold rsize in IND. unfold pix_cells in PXC.
  chunk_facts RT AF GP pix 64. chunk_facts RT AF GP (p_cmap v) 24. chunk_facts RT AF GP b 20.
  chunk_facts RT AF GP (p_data v) (4 * (p_wpl v * p_h v)).
  fframe_chunk RT AF fr 2%nat 256 pix 64. fframe_chunk RT AF fr 2%nat 256 b 20.
  fframe_chunk RT AF fr 2%nat 256 (p_data v) (4 * (p_wpl v * p_h v)).
  pose proof (live_apart RT AF Σ m (p_data v) (4 * (p_wpl v * p_h v)) pix 64 ART0 IND PIN DNP) as DPD.
  pose proof (live_apart RT AF Σ m (p_data v) (4 * (p_wpl v * p_h v)) (p_cmap v) 24 ART0 IND CIN ltac:(congruence)) as DPC.
  unfold box_cells in BXC.
  (* [comment removed for export] *)
  pose proof FSH as TW. split_at TW 4%nat TW2. split_at TW2 1%nat TW3. clear TW TW3.
  assert (ACCW : acc asegs mc (fr + 32) 4)
    by (destruct TW2 as [[_ B] _]; apply (acc_ushadow asegs mc (fr + 32) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
        replace (shad (fr + 32)) with (fr / 8 + 2147450884) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); exact B).
  clear TW2.
  pose proof FSH as TH. split_at TH 6%nat TH2. split_at TH2 1%nat TH3. clear TH TH3.
  assert (ACCH : acc asegs mc (fr + 48) 4)
    by (destruct TH2 as [[_ B] _]; apply (acc_ushadow asegs mc (fr + 48) 4); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
        replace (shad (fr + 48)) with (fr / 8 + 2147450886) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); exact B).
  clear TH2.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
               [e_boxGetGeometry; 0x935f4; 0x93978].

  (* [comment removed for export] *)
  split_last_CB FRMx [12%nat; 4%nat; 12%nat; 4%nat; 12%nat; 4%nat; 12%nat; 4%nat; 12%nat].
  split_at FRMx 8%nat LX1. split_at LX1 1%nat RR1. split_at RR1 1%nat LY1. split_at LY1 1%nat RR2.
  split_at RR2 1%nat LBW. split_at LBW 1%nat RR3. split_at RR3 1%nat LBH. split_at LBH 1%nat RR4.
  lazymatch type of LX1 with rw_cells _ ?mm ?a [CB 4 ?bs] => destruct (cb4_c4' mm a bs LX1) as (x1v & CX1); clear LX1 end.
  lazymatch type of LY1 with rw_cells _ ?mm ?a [CB 4 ?bs] => destruct (cb4_c4' mm a bs LY1) as (y1v & CY1); clear LY1 end.
  lazymatch type of LBW with rw_cells _ ?mm ?a [CB 4 ?bs] => destruct (cb4_c4' mm a bs LBW) as (bwv & CBW); clear LBW end.
  lazymatch type of LBH with rw_cells _ ?mm ?a [CB 4 ?bs] => destruct (cb4_c4' mm a bs LBH) as (bhv & CBH); clear LBH end.
  pose proof FSH as S8. split_at S8 8%nat SH8. split_at SH8 1%nat S9. clear S8 S9.
  pose proof FSH as S10. split_at S10 10%nat SH10. split_at SH10 1%nat S11. clear S10 S11.
  pose proof FSH as S12. split_at S12 12%nat SH12. split_at SH12 1%nat S13. clear S12 S13.
  pose proof FSH as S14. split_at S14 14%nat SH14. split_at SH14 1%nat S15. clear S14 S15.
  (* [comment removed for export] *)
  lazymatch goal with MUx : munch _ mc ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (KL1 : keeps_live (rt_live RT Sc) mc m1)
      by (apply (keeps_live_walk2 RT AF Sc mc m1 fr usp (usp + -256) ARTc ltac:(rewrite FRS; left; reflexivity)
                   ltac:(rewrite ESP0; unfold STACK_WIN; lia) MUx)) end.
  rewrite LVE in KL1.
  lazymatch type of KL1 with keeps_live _ _ ?m1 => pose proof (pix_obj_keep _ mc m1 pix v cvx KL1 POBJ) as POBJ1 end.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).

  pose proof BGG as BG. unfold boxGetGeometry_cps in BG.
  eapply cps_seq.
  { eapply BG with (lo := lo) (b := b) (x := 278) (y := 35) (w := 122) (h := 50) (px := fr + 64) (py := fr + 80) (pw := fr + 96) (ph := fr + 112)
                   (x0 := x1v) (y0 := y1v) (w0 := bwv) (h0 := bhv); rt_side idtac.
    all: lazymatch goal with
         | |- box_obj _ _ _ _ _ _ _ => rewrite ?LVE; split; [exact BXC| exact (proj2 BOBJ)]
         | |- optrF _ _ _ ?p _ =>
             unfold optrF, own_frame, parked in *; split;
             [ exists fr, 2%nat; split; [rewrite FRS; left; reflexivity|];
               change (fs_size 2) with 256;
               split; [lia|]; split; [lia|]; split; [clear - FR64; Z.div_mod_to_equations; lia|];
               split; [lia|]; split; [lia|];
               first [ replace (shad (fr + 64)) with (fr / 8 + 2147450888) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SH8 as [[_ B] _]; exact B
                     | replace (shad (fr + 80)) with (fr / 8 + 2147450890) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SH10 as [[_ B] _]; exact B
                     | replace (shad (fr + 96)) with (fr / 8 + 2147450892) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SH12 as [[_ B] _]; exact B
                     | replace (shad (fr + 112)) with (fr / 8 + 2147450894) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SH14 as [[_ B] _]; exact B ]
             | unfold SEGTOP_A; repeat split; first [lia | clear - FR64; Z.div_mod_to_equations; lia] ]
         | |- rw_cells _ _ _ [C4 _] => first [exact CX1 | exact CY1 | exact CBW | exact CBH]
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ <= _ < _ => clear; lia
         | |- _ <= _ => clear; lia
         | |- ?g => idtac "LEFT-BG:" g
         end. }

  clear SH8 SH10 SH12 SH14.
  after_call RT AF.
  lazymatch goal with AGx : agree_on _ ?ma ?mb, A : ART RT ?S0 ?ma |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
    assert (KL2 : keeps_live (rt_live RT Σ) ma mb)
      by (intros bb kk Hin a Ha;
          assert (HinS : In (bb, kk) (rt_live RT S0)) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin);
          pose proof (live_outside_walk2 RT AF S0 ma fr usp (usp + -256) bb kk _ A ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                        ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia) HinS Ha) as OUT;
          cbn [outside] in OUT; destruct OUT as (_ & OF & _);
          apply AGx; split; [right; right; left; exists bb, kk; split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact Hin| exact Ha]|];
          cbn [outside]; repeat split; try exact I; clear - OF; lia);
    pose proof (pix_obj_keep _ ma mb pix v cvx KL2 POBJ1) as POBJ2 end.
  fold_ag ltac:(fun Hx => pose proof (NFA _ Hx) as [N1 _]; unfold PFW, selc_PFW in Hx; destruct Hx as [Hx1 _];
                  split; [apply (aclient_mono _ _ usp _ _ _ _ Hx1); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]
                         | cbn [outside]; repeat split; try exact I; clear - N1; lia]).

  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32); (p_data v, p_data v + 4 * (p_wpl v * p_h v))]
               [e_boxGetGeometry; 0x935f4; 0x93978].
  (* [comment removed for export] *)
  assert (LHC : forall q n, In (q, n) [(pix, 64); (p_cmap v, 24)] ->
                  In (q, n) (rt_live RT Σ) /\ (q + n <= p_data v \/ p_data v + 4 * (p_wpl v * p_h v) <= q)).
  { intros q n [E|[E|[]]]; injection E as <- <-; (split; [assumption|]); [clear - DPD; unfold parked in *; lia| clear - DPC; unfold parked in *; lia]. }

  (* [comment removed for export] *)
  rewrite !(sx32_small 35), !(sx32_small 50), !(sx32_small 278), !(sx32_small 122) by (clear; lia).
  rewrite !(unsigned_lit 35), !(unsigned_lit 50), !(unsigned_lit 278), !(unsigned_lit 122) by (clear; lia).
  repeat match goal with |- context [bv_swrap 32 ?z] => let z' := eval vm_compute in (bv_swrap 32 z) in change (bv_swrap 32 z) with z' end.
  pose proof HOK as (_ & WR & HR & _ & RSZ).
  assert (IDXR : 0 <= idx <= 256) by (clear - IDXR0 IDXR1; lia).
  assert (WPLR : 0 <= p_wpl v < 2^31) by (clear - RSZ HR; nia).
  rewrite !(sx32_small (p_wpl v)) by exact WPLR.
  (* [comment removed for export] *)
  lazymatch goal with WMx : wmono asegs mc ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_transport asegs mc mm (p_data v) (4 * (p_wpl v * p_h v))
                  (proj1 (af_acc_live RT AF Sc mc _ _ ARTc ltac:(rewrite LVE; exact IND))) WMx) as WRD end.
  apply wr_at_rw_CB in WRD; [| clear - RSZ; lia]. destruct WRD as (dbs & DBC).
  pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC.
  (* [comment removed for export] *)
  pose proof FRMx as LW. split_at LW 4%nat LW2. split_at LW2 1%nat LW3. split_at LW3 1%nat LH2. split_at LH2 1%nat LH3. clear LW LW3 LH3.
  rewrite (sx32_small (p_w v)) in LW2 by (clear - WR; lia). rewrite (sx32_small (p_h v)) in LH2 by (clear - HR; lia).
  pose proof FR as SPL. split_at SPL 3%nat SPL2. split_at SPL2 5%nat SPL3. clear SPL SPL3.
  eapply evt_cut.
  { lazymatch goal with
    | CKHd : parked (p_data v + 4 * (p_wpl v * p_h v) <= 2147446784 \/ _),
      CKSd : parked (p_data v + 4 * (p_wpl v * p_h v) <= 65536 \/ _),
      CKRd : p_data v + 4 * (p_wpl v * p_h v) <= rt_sp0 RT Σ - 8388608,
      FCDd : parked (fr + 256 <= p_data v \/ _),
      ACCd : acc asegs ?mm (p_data v) _,
      CX1' : rw_cells asegs ?mm (fr + 64) [C4 (Z_to_bv 64 278)],
      CIX : rw_cells asegs ?mm (fr + 128) [C4 (Z_to_bv 64 idx)],
      MIx : mem_inv asegs ?mm |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
        epose proof (SELROWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) fr (p_data v) (p_w v) (p_h v) (p_d v) (p_wpl v) idx _ dbs
                       ltac:(cbn [In]; clear - D4; lia) WR HR EWPL RSZ IDXR
                       D0 D16 ltac:(clear - CKRd SP0R1; lia) CKHd CKSd DBC ltac:(rewrite DBL; clear - RSZ; lia) ACCd
                       FR0 FR64 ltac:(clear - FRHI SP0R1; lia) FCDd
                       ltac:(clear - LOR STa; lia) ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(clear - SPT; lia)
                       ltac:(clear - CKRd LOW LOR; lia) LW2 LH2 CX1' CIX) as ZR;
        unfold SEGTOP_A, SEL_HEAD in ZR; replace (usp + -192 + 24) with (usp + -168) in ZR by (clear; lia);
        specialize (ZR SPL2 MIx)
    end.
    exact ZR. }

  intros ms' PO. unfold sel_exit in PO.
  destruct PO as (ra' & t1' & t2' & a0' & a1' & a2' & a7' & s5' & s10' & s11' & t4' & m' & -> & MU' & WM' & MI').
  unfold SEL_EXIT.
  lazymatch goal with H : parked (p_data v + 4 * (p_wpl v * p_h v) <= 65536 \/ _) |- _ => pose proof H as CKSd end.
  lazymatch goal with H : p_data v + 4 * (p_wpl v * p_h v) <= rt_sp0 RT Σ - 8388608 |- _ => pose proof H as CKRd end.
  lazymatch goal with H : parked (fr + 256 <= p_data v \/ _) |- _ => pose proof H as FCDd end.
  lazymatch goal with H : parked (p_data v + 4 * (p_wpl v * p_h v) <= fr / 8 + 2147450880 \/ _) |- _ => pose proof H as FCSd end.
  lazymatch type of MU' with munch _ ?mm m' =>
    lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 mm |- _ =>
      loop_art RT AF S m' lo MU'
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
                split; [intros zz Hzz; right; right; left; exists (p_data v), (4 * (p_wpl v * p_h v)); split; [solve [in_live_tac]| lia]| exact I]]]])
    end end.
  clear DBC DBL LW2 LH2 SPL2. clear BXC.
  lazymatch type of MU' with munch _ ?mm m' =>
    loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKRd CKSd FCDd FCSd DPD LOW LOR SPT SPB STa USP0 USP1 FR0; unfold parked in *; lia) end.

  clear MU' WM'.
  awalk [e_boxGetGeometry; 0x935f4; 0x93978].

  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (KL5 : keeps_live [(pix, 64); (p_cmap v, 24)] m0 m1)
      by (apply (keeps_live_walk2r RT AF S m0 m1 fr usp (usp + -256) (p_data v) (4 * (p_wpl v * p_h v)) _ A
                   ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                   ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia));
          [ intros q n Hq; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (LHC q n Hq) | exact MUx ]);
    pose proof (pix_obj_keep_hc _ m0 m1 pix v cvx KL5 POBJ2) as POBJ5 end.
  frame_release RT AF GP MST Σ fr 2%nat 256 PFW AGF PFS usp lo 0x93980
    ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac|
            split; [intros zz Hzz; right; right; left; exists (p_data v), (4 * (p_wpl v * p_h v)); split; [solve [in_live_tac]| lia]| exact I]]]])
    ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold PFW, selc_PFW in Hx; destruct Hx as [_ Hx2];
                    unfold pm_fp, rsize in Hx2; cbn [outside] in Hx2; destruct Hx2 as [Hx2 _]; unfold shad, SHB in *;
                    repeat split; try exact I; first [exact Hx2 | lia | Z.div_mod_to_equations; lia]).

  lazymatch goal with KR : forall b kk, In (b, kk) (rt_live RT ?S) -> forall a : word, _ -> ?mb a = ?ma a |- _ =>
    assert (KL6 : keeps_live [(pix, 64); (p_cmap v, 24)] ma mb)
      by (intros bb kk Hin a Ha; apply (KR bb kk); [| exact Ha];
          repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (proj1 (LHC bb kk Hin)));
    pose proof (pix_obj_keep_hc _ ma mb pix v cvx KL6 POBJ5) as POBJ6 end.
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 192, usp)] (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -192) |- _ => release_frame FR ST' usp end).
  cps_stop.

  apply cps_finish; intros c Hc; unfold selc_post; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end.
  eexists. exists cvx. split; [| alg_tac].
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; do 16 eexists; reflexivity|].
  split; [split; [split; [assumption| split; [assumption| split; [assumption| assumption]]]| split; assumption]|].
  split; [| split; [| repeat split; assumption]].
  - intros a Ha Ho. apply AGF. split; [| exact Ho].
    lazymatch type of Ha with aclient ?lv _ _ _ => replace lv with (rt_live RT Σ) in Ha by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
    exact Ha.
  - lazymatch goal with |- pix_obj ?lv ?mf _ _ _ =>
      replace lv with (rt_live RT Σ) by (repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity) end.
    exact POBJ6.
Qed.

End SELC_TAIL.
