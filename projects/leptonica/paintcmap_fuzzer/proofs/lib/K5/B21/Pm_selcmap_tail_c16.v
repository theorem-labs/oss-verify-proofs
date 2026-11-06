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
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_gaps_iface Pm_iface Pm_kit Pm_walkkit Pm_objkit Pm_selkit Pm_selloop_defs Pm_selcmap_defs LeptB_guard.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac frame_release RT AF GP MST Σ0 fr k SZ PF AGF PFS usp lo pcafter ivt pft ::=
  cps_stop;
  art_now RT AF ivt;
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx pft end;
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    let FRSc := fresh "FRSc" in
    assert (FRSc : rt_frames RT S = (fr, k) :: rt_frames RT Σ0)
      by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
    let S2 := fresh "S2" in let fl := fresh "fl" in let FLC := fresh "FLC" in let FLN := fresh "FLN" in let FL0 := fresh "FL0" in
    let FLHI := fresh "FLHI" in let FLP := fresh "FLP" in let REL := fresh "REL" in
    destruct (af_frame_release RT AF S mm fr k _ A FRSc) as (S2 & fl & FLC & FLN & FL0 & FLHI & FLP & REL);
    change (fs_size k) with SZ in FLP;
    let off := eval vm_compute in (SZ - 8)%Z in replace (fr + SZ - 8)%Z with (fr + off)%Z in FLP by lia;
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in FLHI end; unfold STACK_WIN in FLHI;
    (* [comment removed for export] *)
    repeat match goal with
    | IN : In (?b, ?kk) _ |- _ =>
        lazymatch goal with
        | _ : fl < b \/ b + kk <= fl |- _ => fail
        | _ => let FA := fresh "FLA" in
               assert (FA : fl < b \/ b + kk <= fl)
                 by (apply (flag_apart _ _ fl b (b + kk) FLN); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                     right; right; left; exists b, kk; split; [solve [in_live_tac] | lia])
        end
    end;
    (* [comment removed for export] *)
    let FLG := fresh "FLG" in
    assert (FLG : forall b kk, In (b, kk) (rt_live RT S) -> fl < b \/ b + kk <= fl)
      by (let b := fresh "b" in let kk := fresh "kk" in let Hb := fresh "Hb" in intros b kk Hb;
          apply (flag_apart _ _ fl b (b + kk) FLN); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          right; right; left; exists b, kk; split; [exact Hb | lia]);
    let LHs := fresh "LHs" in let SSPs := fresh "SSPs" in
    lazymatch goal with LHx : LIBH mm |- _ => pose proof LHx as LHs; hide LHs end;
    lazymatch goal with SSPx : io_ssp mm |- _ => pose proof SSPx as SSPs; hide SSPs end;
    walk_to AF MST [(fl, fl + 1)] [pcafter];
    cps_stop;
    lazymatch goal with MUx : munch [(fl, fl + 1)] mm ?m', WMx : wmono asegs mm ?m', FLC' : rw_cells asegs ?m' fl _ |- _ =>
      let ART2 := fresh "ART2" in let FRS2 := fresh "FRS2" in let LV2 := fresh "LV2" in let SP2 := fresh "SP2" in
      let CR2 := fresh "CR2" in let AL2 := fresh "AL2" in let AM2 := fresh "AM2" in let AGS := fresh "AGS" in
      destruct (REL m' MUx WMx FLC') as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2);
      assert (AGS : agree_on client_static mm m')
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply MUx; cbn [outside]; split; [| exact I];
            let Hin := fresh "Hin" in intros Hin; apply FLN; replace fl with (bv_unsigned a) by lia; right; left; exact Ha);
      unfold hid in LHs, SSPs;
      let LH2 := fresh "LH" in let SSP2 := fresh "SSP" in
      assert (LH2 : LIBH m') by (exact (LIBH_agree RT GP client_static mm m' LHs AGS (fun a Ha => Ha)));
      assert (SSP2 : io_ssp m') by (exact (io_ssp_agree RT GP client_static S2 mm m' SSPs ART2 AGS (fun a Ha => Ha)));
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [| exact I]; let Hin := fresh "Hin" in intros Hin;
        lazymatch type of Hx with PF ?z =>
          apply (flag_not_client _ _ (rt_live RT Σ0) (rt_frames RT Σ0) fl lo usp FLN ltac:(lia) ltac:(lia));
          [ first [ solve [live_sub_tac] | solve [live_add_tac]
                  | solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                           repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; auto] ]
          | solve [frames_sub_tac] | replace fl with z by lia; first [exact Hx | exact (proj1 Hx)] ] end);   (* [comment removed for export] *)
      (* [comment removed for export] *)
      let KEEPR := fresh "KEEPR" in
      assert (KEEPR : forall b kk, In (b, kk) (rt_live RT S) -> forall a : word, b <= bv_unsigned a < b + kk -> m' a = mm a)
        by (let b := fresh "b" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
            intros b kk Hb a Ha; apply MUx; cbn [outside]; split; [| exact I]; pose proof (FLG b kk Hb); lia);
      apply (cps_ASTA_switch RT _ S2 _ _ _ AL2 AM2);
      clear REL LHs SSPs FLC FLN AGS FLG
    end
  end.

Section SELC_TAIL.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis BGG : boxGetGeometry_cps RT.
Hypothesis SELROWS : sel_rows_stmt.
Variables (Σ : rts RT) (PMc : Model -> Prop) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem)
          (pix b : Z) (v : pixv) (cv : cmapv) (fr : Z).

Theorem selc_cut_ok_16 :
  selc_ctx RT Σ PMc usp lo m pix b v ->
  selc_cut_stmt_16 RT Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m pix b v cv fr.
Proof using AF GP BGG SELROWS.
  intros (FDO & MST & ART0 & LOW & LOR & STa & SPT & SPA & SPB & LVP & CNZ & DNZ & D4 & BNE).
  unfold selc_cut_stmt_16.
  intros Sc mc cvx idx j0 j1 j2 j3 f0 f1 js r1 r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r21 r22 r23 r24 r27 r28 r29 r30 r31 F' fc'
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
  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)]
               [e_boxGetGeometry; 0x93f04; 0x94340].

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

  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 256, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32); (p_data v, p_data v + 4 * (p_wpl v * p_h v))]
               [e_boxGetGeometry; 0x93f04; 0x94340].
  (* [comment removed for export] *)
  assert (LHC : forall q n, In (q, n) [(pix, 64); (p_cmap v, 24)] ->
                  In (q, n) (rt_live RT Σ) /\ (q + n <= p_data v \/ p_data v + 4 * (p_wpl v * p_h v) <= q)).
  { intros q n [E|[E|[]]]; injection E as <- <-; (split; [assumption|]); [clear - DPD; unfold parked in *; lia| clear - DPC; unfold parked in *; lia]. }

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  rewrite !(sx32_small 35), !(sx32_small 50), !(sx32_small 278), !(sx32_small 122) by (clear; lia).
  rewrite ?(unsigned_lit 35), ?(unsigned_lit 50), !(unsigned_lit 278), !(unsigned_lit 122) by (clear; lia).
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
  rewrite ?(sx32_small (p_w v)) in LW2 by (clear - WR; lia). rewrite ?(sx32_small (p_h v)) in LH2 by (clear - HR; lia).
  pose proof FR as SPL. split_at SPL 1%nat SPL2. split_at SPL2 6%nat SPL3. clear SPL SPL3.
  (* [comment removed for export] *)
  rewrite (proj2 (Z.ltb_lt 0 (p_data v)) D0). change (Z.b2z true) with 1.
  (* [comment removed for export] *)
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
        epose proof (SELROWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -208) fr (p_data v) (p_w v) (p_h v) (p_d v) (p_wpl v) idx _ _ dbs
                       ltac:(cbn [In]; clear - D4; lia) WR HR EWPL RSZ IDXR
                       D0 D16 ltac:(clear - CKRd SP0R1; lia) CKHd CKSd DBC ltac:(rewrite DBL; clear - RSZ; lia) ACCd
                       FR0 FR64 ltac:(clear - FRHI SP0R1; lia) FCDd
                       ltac:(clear - LOR STa; lia) ltac:(clear - SPA; Z.div_mod_to_equations; lia) ltac:(clear - SPT; lia)
                       ltac:(clear - CKRd LOW LOR; lia) LW2 LH2 CX1' CIX) as ZR;
        unfold SEGTOP_A, SEL_HEAD in ZR; replace (usp + -208 + 16) with (usp + (-192)) in ZR by (clear; lia);
        specialize (ZR SPL2 MIx)
    end.
    exact ZR. }

  (* [comment removed for export] *)
  intros ms' PO. unfold sel_exit in PO.
  destruct PO as (ra' & t0' & t1' & a0' & a1' & a2' & a6' & s9' & s10' & s11' & t6' & m' & -> & MU' & WM' & MI').
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
  (* [comment removed for export] *)
  awalk [e_boxGetGeometry; 0x93f04; 0x94340].

  (* [comment removed for export] *)
  lazymatch goal with A : ART RT ?S ?m0, MUx : munch _ ?m0 ?m1 |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (KL5 : keeps_live [(pix, 64); (p_cmap v, 24)] m0 m1)
      by (apply (keeps_live_walk2r RT AF S m0 m1 fr usp (usp + -256) (p_data v) (4 * (p_wpl v * p_h v)) _ A
                   ltac:(repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; left; reflexivity)
                   ltac:(repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; unfold STACK_WIN; lia));
          [ intros q n Hq; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact (LHC q n Hq) | exact MUx ]);
    pose proof (pix_obj_keep_hc _ m0 m1 pix v cvx KL5 POBJ2) as POBJ5 end.
  (* [comment removed for export] *)
  frame_release RT AF GP MST Σ fr 2%nat 256 PFW AGF PFS usp lo 0x94348
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
  (* [comment removed for export] *)
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 208, usp)] (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -208) |- _ => release_frame FR ST' usp end).
  cps_stop.

  (* [comment removed for export] *)
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
